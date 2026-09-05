"""Kernel IR — per-procedure semantic trees, and the passes that
shape them for the Lean printer.

This is the *second* IR of DESIGN §2.3: deep (typed expression/statement trees)
exactly where the relational IR (`groundline/ir.py`) is deliberately shallow, and
consumed only by the Lean printer (`groundline/lean_printer.py`). Nothing here may
leak into the relational IR, and nothing here is flang-specific — a frontend
(`frontend/flang_kernel.py` today) populates it.

Trusted-base rule (VISION D6): everything in this module is deterministic and
small enough to audit. A construct outside the supported subset raises
:class:`UnsupportedConstruct` — refusal, never a guess.

Passes:

- :func:`pointize` — strip a single loop-nest wrapper and turn every array
  reference indexed *exactly* by the loop indices into a scalar. This is the
  semantic move that pairs a Fortran loop nest with an AMReX per-point kernel.
  Two nest forms are admitted, with two different licenses:

  * ``do concurrent`` — the *source* asserts iteration independence; that
    assertion is the license for the pointwise model. Any other subscript
    pattern (offsets, masks, partial indexing) is refused.
  * a plain, PERFECTLY nested ``do`` nest (each level's body is exactly one
    inner ``do`` until the innermost) — the source asserts nothing, so the
    license is a *proof*: the schema lemma ``foldSeq f enum = pointwise f``
    (``lean/groundline/Groundline/SeqSchema.lean``) shows the honest sequential-fold
    semantics of such a nest equals the pointwise map, for any duplicate-free
    enumeration of the index box. The gate here is what guarantees the
    lemma's setting applies — it does not itself justify the reordering:
    every array reference must be indexed exactly by the loop indices, and
    every write must land in the iteration's own array cell (an assignment
    to a scalar parameter is an accumulator/reduction shape and refuses;
    reductions and cross-iteration recurrences are not point-local and stay
    out of the subset). The one cross-iteration channel this gate does not
    itself refuse — a local scalar read before its first write, which in a
    plain DO would carry the previous iteration's value — cannot produce a
    wrong model either: :func:`functionalize` binds locals per iteration via
    ``Let``, so such a read prints as an unbound name and the generated Lean
    fails to elaborate (refusal by the checker, loud).

  Derived-type component reads (rule B) are admitted in exactly two shapes,
  both becoming synthesized scalar ``in`` parameters of the pointized kernel:
  a loop-invariant scalar component (``gv%h_to_z``; loop-invariant because
  the base must be an ``intent(in)`` derived-type dummy argument, which
  Fortran forbids modifying, and component writes refuse), and a component
  array indexed exactly by the loop indices (``tv%spv_avg(i,j,k)``). The
  synthesized parameter takes the component's own name (``gv%h_to_z`` →
  ``h_to_z``) and is modeled as a real scalar — the one-time by-eye audit of
  each generated def against its source covers the component's actual type.
  Naming is deterministic and collision-checked: if the component name
  collides with an existing parameter, local, loop index, or another
  synthesized name from a different component, the extraction refuses rather
  than renames. Synthesized parameters append after the real parameters in
  first-use order (the order the scalarization walk first meets them). A
  component read in any other shape refuses.
- :func:`functionalize` — turn the imperative body (assignments + structured
  ifs) into a single functional expression tree: local assignments become
  ``Let`` bindings, assignments to inout arguments update a symbolic state, and
  each control-flow path ends by materializing the state tuple. Statements
  *after* an ``If`` (a control-flow join) are supported in exactly one shape:
  the ``If`` has a single branch (no elseif chain) and every branch body is
  assignments to state (output) variables only — no locals (a ``Let`` may not
  escape a branch), no nested ``If``s. Each variable a branch assigned merges
  as ``state'[v] = Cond(cond, state_then[v], state_else[v])``; the remaining
  statements then run against the *merged* state, so a later read of a
  variable the ``If`` may have updated observes the conditional value —
  sequential semantics, as in the source. Any other join shape is refused.

  A *function* kernel (Fortran ``function … result(r)``; a non-void C++ point
  function) carries its result as a parameter of intent ``result``: the
  single output. Unlike an ``inout``/``out`` argument, whose caller-supplied
  value the body may read, **the caller supplies no value for the result
  variable** — it starts undefined. The model therefore starts it unbound
  rather than at ``Var(r)``, so a read before its first assignment refuses, a control-flow path that never assigns
  it refuses (the source would return an undefined value there), and a
  joined ``If`` assigning it on one side only refuses for the same reason. A
  result alongside ``inout``/``out`` arguments (two output conventions in one
  procedure) refuses. The frontends supply the parameter: flang from the
  ``result(name)`` suffix, clang by naming the return value after the
  function (Fortran's own default for a result variable).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Union


class UnsupportedConstruct(Exception):
    """A source construct outside the supported kernel subset (refuse, don't guess)."""


# --------------------------------------------------------------------------- #
# Expressions
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class RealLit:
    text: str          # source spelling, e.g. "3.0"


@dataclass(frozen=True)
class IntLit:
    text: str          # source spelling, e.g. "2"


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class ArrayRef:
    name: str
    subscripts: tuple["Expr", ...]


@dataclass(frozen=True)
class ComponentRef:
    """Derived-type component read ``base%comp`` (single level only);
    ``subscripts`` is ``()`` for a scalar component, or the section subscripts
    for a component array reference. Consumed only by :func:`pointize`, which
    synthesizes a scalar ``in`` parameter for the supported shapes (see the
    module docstring) — a ``ComponentRef`` never survives into the printed
    model."""
    base: str
    comp: str
    subscripts: tuple["Expr", ...]


@dataclass(frozen=True)
class Paren:
    """Source parentheses — semantically transparent, kept so the printed model
    mirrors the source's own grouping (the fidelity principle)."""
    inner: "Expr"


@dataclass(frozen=True)
class Neg:
    """Unary minus. Fortran only admits it on a whole term (R1008), so the
    frontend produces it wrapping either a leaf or an entire term/paren."""
    inner: "Expr"


@dataclass(frozen=True)
class BinOp:
    op: str            # 'add' | 'sub' | 'mul' | 'div' | 'pow'
    lhs: "Expr"
    rhs: "Expr"


@dataclass(frozen=True)
class Cmp:
    op: str            # 'lt' | 'le' | 'gt' | 'ge' | 'eq' | 'ne'
    lhs: "Expr"
    rhs: "Expr"


@dataclass(frozen=True)
class Call:
    """Intrinsic reference (``abs``, later ``min``/``max``)."""
    name: str
    args: tuple["Expr", ...]


@dataclass(frozen=True)
class Cond:
    """Conditional *expression* — the functional layer's inline
    ``if cond then a else b``. No frontend ever produces one: only
    :func:`functionalize` creates it, when merging a control-flow join
    (see the module docstring)."""
    cond: "Expr"
    then: "Expr"
    orelse: "Expr"


Expr = Union[RealLit, IntLit, Var, ArrayRef, ComponentRef, Paren, Neg, BinOp,
             Cmp, Call, Cond]


# --------------------------------------------------------------------------- #
# Statements
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class Assign:
    target: Union[Var, ArrayRef]
    value: Expr


@dataclass(frozen=True)
class If:
    """Structured IF: ``branches`` are (condition, body) in source order
    (if/elseif...), ``orelse`` the else body ([] if absent)."""
    branches: tuple[tuple[Expr, tuple["Stmt", ...]], ...]
    orelse: tuple["Stmt", ...]


@dataclass(frozen=True)
class DoConcurrent:
    """``do concurrent`` nest: controls are (index_name, lower, upper) in
    source order; the body is a statement sequence."""
    controls: tuple[tuple[str, Expr, Expr], ...]
    body: tuple["Stmt", ...]


@dataclass(frozen=True)
class Do:
    """One level of a plain ``do`` loop (no stride): control is
    (index_name, lower, upper). A perfectly nested plain nest arrives as
    ``Do(k, (Do(j, (Do(i, body),)),))`` — :func:`pointize` unwraps it."""
    control: tuple[str, Expr, Expr]
    body: tuple["Stmt", ...]


Stmt = Union[Assign, If, DoConcurrent, Do]


# --------------------------------------------------------------------------- #
# Kernel
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class Param:
    name: str
    type: str          # 'real' | 'integer' | 'derived:<name>'
    intent: Optional[str]   # 'in' | 'inout' | 'out' | 'result' | None (local)
    rank: int          # 0 = scalar


@dataclass(frozen=True)
class Kernel:
    name: str
    params: tuple[Param, ...]   # dummy arguments, in source order
    locals: tuple[Param, ...]   # local declarations (intent None)
    body: tuple[Stmt, ...]


# --------------------------------------------------------------------------- #
# Pass 1: pointization
# --------------------------------------------------------------------------- #

def is_loop_nest(kernel: Kernel) -> bool:
    """True iff the kernel body is exactly one top-level loop nest
    (``do concurrent`` or plain ``do``) — the shape :func:`pointize` reduces.
    The kernel bank uses this to tell loop kernels (which need an explicit
    ``pointize = true`` license in the manifest) from kernels that are
    already per-point."""
    return len(kernel.body) == 1 and isinstance(kernel.body[0], (DoConcurrent, Do))


def pointize(kernel: Kernel) -> Kernel:
    """Strip a single top-level loop-nest wrapper; scalarize arrays.

    Every ``ArrayRef`` whose subscripts are exactly the loop indices (as plain
    ``Var``s) becomes ``Var(name)``; the supported ``ComponentRef`` shapes
    become synthesized scalar ``in`` parameters (rule B — see the module
    docstring for the naming/collision/ordering rules). The loop indices, the
    bound variables, and any parameter no longer referenced by the pointized
    body (grid structs, index ranges) are dropped.

    The nest may be a ``do concurrent`` (license: the source's independence
    assertion) or a plain, perfectly nested ``do`` (license: the schema lemma
    — see the module docstring). The plain-DO path additionally refuses any
    write that does not land in the iteration's own array cell: an assignment
    to a scalar parameter is a reduction/accumulator, which is not point-local.
    """
    if len(kernel.body) != 1 or not isinstance(kernel.body[0], (DoConcurrent, Do)):
        raise UnsupportedConstruct(
            f"{kernel.name}: pointize expects the body to be exactly one "
            f"do-concurrent or plain-do nest")
    loop = kernel.body[0]
    if isinstance(loop, DoConcurrent):
        plain = False
        indices = tuple(name for (name, _, _) in loop.controls)
        loop_body = loop.body
    else:
        # Rule A: unwrap a PERFECTLY nested plain-do nest — each level's body
        # must be exactly one inner do until the innermost. (A do remaining
        # anywhere in the innermost body is an imperfect nest and refuses in
        # scalarize_stmt below.)
        plain = True
        names = [loop.control[0]]
        loop_body = loop.body
        while len(loop_body) == 1 and isinstance(loop_body[0], Do):
            names.append(loop_body[0].control[0])
            loop_body = loop_body[0].body
        if len(set(names)) != len(names):
            raise UnsupportedConstruct(
                f"{kernel.name}: duplicate loop index in a plain-do nest {names}")
        indices = tuple(names)

    param_by_name = {p.name: p for p in kernel.params}
    local_names = {p.name for p in kernel.locals}
    # Rule B: synthesized scalar params for component reads, keyed by
    # (base, comp); insertion order = first-use order (the walk below is the
    # deterministic statement/left-to-right expression order).
    synth: dict[tuple[str, str], str] = {}

    def synth_param(e: ComponentRef) -> Var:
        key = (e.base, e.comp)
        if key not in synth:
            name = e.comp
            if (name in param_by_name or name in local_names
                    or name in indices or name in synth.values()):
                raise UnsupportedConstruct(
                    f"{kernel.name}: synthesized parameter '{name}' for the "
                    f"component read {e.base}%{e.comp} collides with an "
                    f"existing name")
            synth[key] = name
        return Var(synth[key])

    def scalarize_expr(e: Expr) -> Expr:
        if isinstance(e, ComponentRef):
            base = param_by_name.get(e.base)
            if (base is None or not base.type.startswith("derived:")
                    or base.intent != "in"):
                raise UnsupportedConstruct(
                    f"{kernel.name}: component read {e.base}%{e.comp} — the "
                    f"base must be an intent(in) derived-type dummy argument")
            if e.subscripts == ():
                return synth_param(e)      # loop-invariant scalar component
            subs = tuple(s.name if isinstance(s, Var) else None
                         for s in e.subscripts)
            if set(subs) == set(indices) and None not in subs:
                return synth_param(e)      # component array at the own index
            raise UnsupportedConstruct(
                f"{kernel.name}: component read {e.base}%{e.comp}{subs} is "
                f"neither a loop-invariant scalar nor a component array "
                f"indexed exactly by the loop indices {indices}")
        if isinstance(e, (RealLit, IntLit, Var)):
            return e
        if isinstance(e, ArrayRef):
            subs = tuple(s.name if isinstance(s, Var) else None for s in e.subscripts)
            if set(subs) == set(indices) and None not in subs:
                return Var(e.name)
            raise UnsupportedConstruct(
                f"{kernel.name}: array reference {e.name}{subs} is not indexed "
                f"exactly by the loop indices {indices}")
        if isinstance(e, Paren):
            return Paren(scalarize_expr(e.inner))
        if isinstance(e, Neg):
            return Neg(scalarize_expr(e.inner))
        if isinstance(e, BinOp):
            return BinOp(e.op, scalarize_expr(e.lhs), scalarize_expr(e.rhs))
        if isinstance(e, Cmp):
            return Cmp(e.op, scalarize_expr(e.lhs), scalarize_expr(e.rhs))
        if isinstance(e, Call):
            return Call(e.name, tuple(scalarize_expr(a) for a in e.args))
        raise UnsupportedConstruct(f"{kernel.name}: cannot scalarize {type(e).__name__}")

    def scalarize_stmt(s: Stmt) -> Stmt:
        if isinstance(s, Assign):
            if isinstance(s.target, ComponentRef):
                raise UnsupportedConstruct(
                    f"{kernel.name}: assignment to derived-type component "
                    f"{s.target.base}%{s.target.comp} is unsupported")
            if plain and isinstance(s.target, Var) and s.target.name in param_by_name:
                raise UnsupportedConstruct(
                    f"{kernel.name}: assignment to scalar parameter "
                    f"'{s.target.name}' inside a plain-do nest is a "
                    f"reduction/accumulator shape — every write must land in "
                    f"the iteration's own array cell")
            tgt = scalarize_expr(s.target)
            if not isinstance(tgt, Var):
                raise UnsupportedConstruct(f"{kernel.name}: unsupported assignment target")
            return Assign(tgt, scalarize_expr(s.value))
        if isinstance(s, If):
            return If(
                tuple((scalarize_expr(c), tuple(scalarize_stmt(b) for b in body))
                      for (c, body) in s.branches),
                tuple(scalarize_stmt(b) for b in s.orelse))
        if isinstance(s, (Do, DoConcurrent)):
            raise UnsupportedConstruct(
                f"{kernel.name}: a do-construct inside the loop body — the "
                f"nest is not perfectly nested")
        raise UnsupportedConstruct(
            f"{kernel.name}: {type(s).__name__} inside the loop body is unsupported")

    body = tuple(scalarize_stmt(s) for s in loop_body)

    used: set[str] = set()

    def collect(e: Expr) -> None:
        if isinstance(e, Var):
            used.add(e.name)
        elif isinstance(e, (Paren, Neg)):
            collect(e.inner)
        elif isinstance(e, BinOp):
            collect(e.lhs); collect(e.rhs)
        elif isinstance(e, Cmp):
            collect(e.lhs); collect(e.rhs)
        elif isinstance(e, Call):
            for a in e.args:
                collect(a)

    def collect_stmt(s: Stmt) -> None:
        if isinstance(s, Assign):
            used.add(s.target.name); collect(s.value)
        elif isinstance(s, If):
            for (c, b) in s.branches:
                collect(c)
                for x in b:
                    collect_stmt(x)
            for x in s.orelse:
                collect_stmt(x)

    for s in body:
        collect_stmt(s)

    params = tuple(Param(p.name, p.type, p.intent, 0)
                   for p in kernel.params if p.name in used and p.name not in indices)
    # Rule B: synthesized params append after the real params, in first-use
    # order. Modeled as real scalars (see the module docstring).
    params += tuple(Param(n, "real", "in", 0) for n in synth.values())
    locals_ = tuple(Param(p.name, p.type, None, 0)
                    for p in kernel.locals if p.name in used and p.name not in indices)
    return Kernel(kernel.name, params, locals_, body)


# --------------------------------------------------------------------------- #
# Pass 2: functionalization
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class Let:
    """Functional form: ``let name := value; body``."""
    name: str
    value: Expr
    body: "FunExpr"


@dataclass(frozen=True)
class IfExpr:
    cond: Expr
    then: "FunExpr"
    orelse: "FunExpr"


@dataclass(frozen=True)
class Tuple_:
    elems: tuple[Expr, ...]


FunExpr = Union[Let, IfExpr, Tuple_]


def functionalize(kernel: Kernel) -> tuple[tuple[Param, ...], tuple[str, ...], FunExpr]:
    """Translate the (pointized) imperative body into one functional expression.

    Returns ``(input_params, output_names, expr)`` where the outputs are the
    ``inout``/``out`` parameters in declaration order — or the single
    ``result`` parameter of a function kernel; ``expr`` evaluates to their
    tuple. Locals become ``Let`` bindings; an ``inout``/``out`` output's
    current value is tracked symbolically, starting at its own input ``Var``;
    a ``result`` starts unbound (see the module docstring).
    """
    outputs = tuple(p.name for p in kernel.params
                    if p.intent in ("inout", "out", "result"))
    if not outputs:
        raise UnsupportedConstruct(f"{kernel.name}: no inout/out parameters — nothing to return")
    results = {p.name for p in kernel.params if p.intent == "result"}
    if results and len(outputs) > 1:
        raise UnsupportedConstruct(
            f"{kernel.name}: a function result alongside other outputs "
            f"{sorted(set(outputs) - results)} — two output conventions in "
            f"one kernel")
    local_names = {p.name for p in kernel.locals}

    def materialize(state: dict[str, Expr]) -> Tuple_:
        missing = [o for o in outputs if o not in state]
        if missing:
            raise UnsupportedConstruct(
                f"{kernel.name}: function result '{missing[0]}' is not "
                f"assigned on every control-flow path")
        return Tuple_(tuple(state[o] for o in outputs))

    def go(stmts: tuple[Stmt, ...], state: dict[str, Expr]) -> FunExpr:
        if not stmts:
            return materialize(state)
        head, rest = stmts[0], stmts[1:]
        if isinstance(head, Assign):
            name = head.target.name
            value = subst(head.value, state)
            if name in local_names:
                return Let(name, value, go(rest, state))
            if name in outputs:
                return go(rest, {**state, name: value})
            raise UnsupportedConstruct(
                f"{kernel.name}: assignment to '{name}', neither local nor output")
        if isinstance(head, If):
            if rest:
                # Control-flow join: the remaining statements run against the
                # MERGED state, so a later read of a variable this IF may have
                # updated observes the conditional value (sequential semantics).
                return go(rest, merge_if(head, state))
            def branch(i: int) -> FunExpr:
                if i < len(head.branches):
                    cond, body = head.branches[i]
                    return IfExpr(subst(cond, state), go(body, dict(state)), branch(i + 1))
                return go(head.orelse, dict(state))
            return branch(0)
        raise UnsupportedConstruct(f"{kernel.name}: {type(head).__name__} is unsupported here")

    def merge_if(head: If, state: dict[str, Expr]) -> dict[str, Expr]:
        """Merge an ``If`` that statements follow into a per-variable ``Cond``.

        Supported ONLY when the ``If`` has a single branch (no elseif chain)
        and every branch body consists solely of assignments to state (output)
        variables — no locals (a ``Let`` may not escape), no nested ``If``s.
        Per variable a branch assigned: ``state'[v] = Cond(cond, state_then[v],
        state_else[v])``; unassigned variables pass through unchanged.
        """
        if len(head.branches) != 1:
            raise UnsupportedConstruct(
                f"{kernel.name}: statements after an IF with an elseif chain "
                f"(control-flow join) are unsupported")
        cond, then_body = head.branches[0]

        def branch_state(body: tuple[Stmt, ...]) -> tuple[dict[str, Expr], set[str]]:
            st, assigned = dict(state), set()
            for s in body:
                if not isinstance(s, Assign):
                    raise UnsupportedConstruct(
                        f"{kernel.name}: statements after an IF (control-flow join) "
                        f"require its branches to hold only assignments to output "
                        f"variables; found {type(s).__name__}")
                if s.target.name not in outputs:
                    raise UnsupportedConstruct(
                        f"{kernel.name}: assignment to non-output '{s.target.name}' "
                        f"inside a joined IF branch (a Let may not escape the branch)")
                st[s.target.name] = subst(s.value, st)
                assigned.add(s.target.name)
            return st, assigned

        st_then, asg_then = branch_state(then_body)
        st_else, asg_else = branch_state(head.orelse)
        cond_now = subst(cond, state)
        merged = dict(state)
        for v in asg_then | asg_else:
            if v not in st_then or v not in st_else:
                # Only a `result` can be missing from a side: inout/out
                # outputs are in `state` from the start.
                raise UnsupportedConstruct(
                    f"{kernel.name}: function result '{v}' is assigned in only "
                    f"one branch of a joined IF — undefined on the other path")
            merged[v] = Cond(cond_now, st_then[v], st_else[v])
        return merged

    def subst(e: Expr, state: dict[str, Expr]) -> Expr:
        """Replace reads of *output* variables with their current symbolic value.
        (Locals are bound by ``Let`` and read by name, so they pass through.)

        Unconditional on purpose: when the current value is the identity
        ``Var(name)`` the substitution is a no-op, and when it is any other
        expression — including a plain ``Var`` alias like ``b = a`` — the read
        must see it, or a later statement would silently read the *input*
        value. Sequential threading is the whole contract here.

        The caller supplies no value for a function result (unlike an
        inout/out argument), so reading it before its first assignment reads
        an undefined value in the source — refused here."""
        if isinstance(e, Var) and e.name in state:
            return state[e.name]
        if isinstance(e, Var) and e.name in results:
            raise UnsupportedConstruct(
                f"{kernel.name}: function result '{e.name}' is read before it "
                f"is assigned")
        if isinstance(e, Paren):
            return Paren(subst(e.inner, state))
        if isinstance(e, Neg):
            return Neg(subst(e.inner, state))
        if isinstance(e, BinOp):
            return BinOp(e.op, subst(e.lhs, state), subst(e.rhs, state))
        if isinstance(e, Cmp):
            return Cmp(e.op, subst(e.lhs, state), subst(e.rhs, state))
        if isinstance(e, Call):
            return Call(e.name, tuple(subst(a, state) for a in e.args))
        return e

    # inout/out outputs start at the value the caller passed in; a result
    # starts unbound — the caller passes nothing in for it.
    state0: dict[str, Expr] = {o: Var(o) for o in outputs if o not in results}
    return kernel.params, outputs, go(kernel.body, state0)
