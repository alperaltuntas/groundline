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
    ``Let`` and refuses a read of a local that is not yet in scope.

  Derived-type component reads (rule B) are admitted in exactly two shapes,
  both becoming synthesized scalar ``in`` parameters of the pointized kernel:
  a loop-invariant scalar component (``gv%h_to_z``; loop-invariant because
  the base must be an ``intent(in)`` derived-type dummy argument, which
  Fortran forbids modifying, and component writes refuse), and a component
  array indexed by loop indices — all of them (``tv%spv_avg(i,j,k)``) or a
  subset (``g%iareat(i,j)`` in a k,j,i nest; the value is then the same for
  every index the subscripts omit, and it is read-only for the same reason
  the scalar is). The synthesized parameter takes the component's own name
  (``gv%h_to_z`` → ``h_to_z``) and is modeled as a real scalar — the one-time
  by-eye audit of each generated def against its source covers the
  component's actual type. A component read in any other shape (offsets,
  non-index subscripts) refuses.

  Read-only neighbor stencils (rule C): an array reference whose subscripts
  are the loop indices, some carrying a literal offset (``uh(i-1,j,k)``), is
  admitted when the array is never written anywhere in the nest — the value
  read is then loop-entry data, so the iteration still depends only on
  loop-entry data — and when the nest is ``do concurrent`` (the license
  granted 2026-09-05 is that narrow; the plain-DO case stays refused until
  its schema-lemma variant is proved, though the existing lemma's
  environment-in-the-closure form appears to cover it). Each distinct offset
  pattern becomes a synthesized scalar ``in`` parameter named after the array
  and the offsets, index by index (``uh(i-1,j,k)`` → ``uh_im1``,
  ``a(i+1,j-1,k)`` → ``a_ip1_jm1``); the offset is absorbed into *which
  input*, never into integer arithmetic inside the model. Writes must still
  land in the iteration's own cell; an offset read of an array the nest
  writes is a cross-iteration recurrence and refuses in either loop form.

  Nest-invariant locals (rule D): a scalar local read in the nest but never
  assigned in it (``h_min``, set before the loop) is an input of the point
  function and becomes a synthesized ``in`` parameter under its own name and
  declared type; a local the nest assigns stays a per-iteration local.

  All synthesized names are collision-checked against the existing
  parameters, locals, loop indices and each other: the extraction refuses
  rather than renames (a silent rename would defeat the by-eye audit).
  Synthesized parameters append after the real parameters in first-use order
  (the order the scalarization walk first meets them).
- :func:`functionalize` — turn the imperative body (assignments + structured
  ifs) into a single functional expression tree: local assignments become
  ``Let`` bindings, assignments to inout arguments update a symbolic state, and
  each control-flow path ends by materializing the state tuple. Statements
  *after* an ``If`` (a control-flow join) are merged **sequentially**: every
  branch body (then, each elseif, else) is run against a copy of the incoming
  state — assignments update it, locals assigned inside the branch are
  tracked in that copy (so later reads within the branch see them), and a
  nested ``If`` inside the branch merges recursively against it — and each
  variable some branch assigned becomes a conditional chain over the branch
  conditions, ``Cond(c1, s1[v], Cond(c2, s2[v], … s_else[v]))``. Merged
  *outputs* update the state; merged *locals* are bound by ``Let`` right
  after the join (in first-assignment order), so the statements that follow
  run against the merged values — sequential semantics, as in the source. A
  local assigned on only some paths takes its prior ``Let`` binding on the
  others when it has one; when it has none it is undefined there, so it is
  dropped if nothing after the join reads it and **refused** if something
  does (a conservative read scan — never a wrong model). A local read before
  any assignment refuses outright.

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
    type: str          # 'real' | 'integer' | 'logical' | 'derived:<name>'
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
    (rule B), read-only neighbor stencils (rule C) and nest-invariant locals
    (rule D) become synthesized scalar ``in`` parameters — see the module
    docstring for the shapes and the naming/collision/ordering rules. The
    loop indices, the bound variables, and any parameter no longer referenced
    by the pointized body (grid structs, index ranges) are dropped.

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
    local_by_name = {p.name: p for p in kernel.locals}
    local_names = set(local_by_name)
    # Every name the nest assigns (scalar or array cell) — the write set the
    # stencil and invariant-local rules are gated on.
    written: set[str] = set()

    def collect_writes(s: Stmt) -> None:
        if isinstance(s, Assign):
            written.add(s.target.name if isinstance(s.target, (Var, ArrayRef))
                        else s.target.base)
        elif isinstance(s, If):
            for (_, body) in s.branches:
                for x in body:
                    collect_writes(x)
            for x in s.orelse:
                collect_writes(x)
        elif isinstance(s, (Do, DoConcurrent)):
            for x in s.body:
                collect_writes(x)

    for s in loop_body:
        collect_writes(s)

    # Synthesized scalar `in` params — rule B (component reads, keyed by
    # (base, comp)), rule C (stencil reads, keyed by array + offset pattern),
    # rule D (nest-invariant locals, keyed by name); insertion order =
    # first-use order (the walk below is the deterministic statement /
    # left-to-right expression order).
    synth: dict[tuple, Param] = {}

    def synth_param(key: tuple, name: str, type_: str, what: str) -> Var:
        if key not in synth:
            taken = (name in param_by_name or name in indices
                     or (name in local_names and key[0] != "local")
                     or any(p.name == name for p in synth.values()))
            if taken:
                raise UnsupportedConstruct(
                    f"{kernel.name}: synthesized parameter '{name}' for {what} "
                    f"collides with an existing name")
            synth[key] = Param(name, type_, "in", 0)
        return Var(synth[key].name)

    def fmt_subs(parsed) -> str:
        """Render parsed subscripts as the source spells them: ``(i, k+1)``."""
        return "(" + ", ".join(
            "?" if p is None else
            (p[0] if p[1] == 0 else f"{p[0]}{'+' if p[1] > 0 else '-'}{abs(p[1])}")
            for p in parsed) + ")"

    def parse_subscripts(e: ArrayRef | ComponentRef):
        """Each subscript as (index, offset): a plain loop index is offset 0,
        ``index ± literal`` carries the literal; anything else is None."""
        out = []
        for sub in e.subscripts:
            if isinstance(sub, Var) and sub.name in indices:
                out.append((sub.name, 0))
            elif (isinstance(sub, BinOp) and sub.op in ("add", "sub")
                    and isinstance(sub.lhs, Var) and sub.lhs.name in indices
                    and isinstance(sub.rhs, IntLit)):
                off = int(sub.rhs.text) * (1 if sub.op == "add" else -1)
                out.append((sub.lhs.name, off))
            else:
                out.append(None)
        return out

    def scalarize_expr(e: Expr) -> Expr:
        if isinstance(e, ComponentRef):
            base = param_by_name.get(e.base)
            if (base is None or not base.type.startswith("derived:")
                    or base.intent != "in"):
                raise UnsupportedConstruct(
                    f"{kernel.name}: component read {e.base}%{e.comp} — the "
                    f"base must be an intent(in) derived-type dummy argument")
            what = f"the component read {e.base}%{e.comp}"
            if e.subscripts == ():
                return synth_param(("comp", e.base, e.comp), e.comp, "real", what)
            subs = tuple(s.name if isinstance(s, Var) else None
                         for s in e.subscripts)
            # Rule B, array form: indexed by loop indices — all of them, or a
            # subset (then constant along the omitted ones); no offsets.
            if (None not in subs and set(subs) <= set(indices)
                    and len(set(subs)) == len(subs)):
                return synth_param(("comp", e.base, e.comp), e.comp, "real", what)
            raise UnsupportedConstruct(
                f"{kernel.name}: component read {e.base}%{e.comp}{subs} is "
                f"neither a loop-invariant scalar nor a component array "
                f"indexed by (a subset of) the loop indices {indices}")
        if isinstance(e, (RealLit, IntLit)):
            return e
        if isinstance(e, Var):
            # Rule D: a scalar local the nest reads but never assigns is
            # loop-entry data — an input of the point function.
            if (e.name in local_names and e.name not in written
                    and e.name not in indices):
                loc = local_by_name[e.name]
                return synth_param(("local", e.name), e.name, loc.type,
                                   f"the nest-invariant local {e.name}")
            return e
        if isinstance(e, ArrayRef):
            parsed = parse_subscripts(e)
            names = [p[0] for p in parsed if p is not None]
            if (None in parsed or set(names) != set(indices)
                    or len(names) != len(indices)):
                subs = tuple(s.name if isinstance(s, Var) else None
                             for s in e.subscripts)
                raise UnsupportedConstruct(
                    f"{kernel.name}: array reference {e.name}{subs} is not "
                    f"indexed by the loop indices {indices} (plain, or with a "
                    f"literal offset)")
            if all(off == 0 for (_, off) in parsed):
                return Var(e.name)          # the iteration's own cell
            # Rule C: a read-only neighbor stencil.
            if plain:
                raise UnsupportedConstruct(
                    f"{kernel.name}: neighbor read {e.name}{fmt_subs(parsed)} in "
                    f"a plain-do nest — read-only stencils are admitted in do "
                    f"concurrent nests only (the plain-DO schema-lemma variant "
                    f"is not yet proved)")
            if e.name in written:
                raise UnsupportedConstruct(
                    f"{kernel.name}: neighbor read {e.name}{fmt_subs(parsed)} of "
                    f"an array the nest writes — a cross-iteration recurrence")
            suffix = "".join(f"_{idx}{'p' if off > 0 else 'm'}{abs(off)}"
                             for (idx, off) in parsed if off != 0)
            return synth_param(("stencil", e.name, tuple(parsed)),
                               e.name + suffix, "real",
                               f"the neighbor read {e.name}{fmt_subs(parsed)}")
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
            if isinstance(s.target, ArrayRef):
                # Writes land in the iteration's own cell only — never in a
                # neighbor's (that would be a recurrence in either loop form).
                parsed = parse_subscripts(s.target)
                if any(p is not None and p[1] != 0 for p in parsed):
                    raise UnsupportedConstruct(
                        f"{kernel.name}: write to a neighbor cell "
                        f"{s.target.name}{fmt_subs(parsed)} — every write must "
                        f"land in the iteration's own cell")
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
    # Synthesized params (rules B, C, D) append after the real params, in
    # first-use order.
    params += tuple(synth.values())
    promoted = {key[1] for key in synth if key[0] == "local"}
    locals_ = tuple(Param(p.name, p.type, None, 0)
                    for p in kernel.locals
                    if p.name in used and p.name not in indices
                    and p.name not in promoted)
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


def _names_in_expr(e: Expr, out: set[str]) -> None:
    """Every variable name read in ``e`` (array/component bases included)."""
    if isinstance(e, Var):
        out.add(e.name)
    elif isinstance(e, ArrayRef):
        out.add(e.name)
        for sub in e.subscripts:
            _names_in_expr(sub, out)
    elif isinstance(e, ComponentRef):
        out.add(e.base)
        for sub in e.subscripts:
            _names_in_expr(sub, out)
    elif isinstance(e, (Paren, Neg)):
        _names_in_expr(e.inner, out)
    elif isinstance(e, (BinOp, Cmp)):
        _names_in_expr(e.lhs, out)
        _names_in_expr(e.rhs, out)
    elif isinstance(e, Call):
        for a in e.args:
            _names_in_expr(a, out)
    elif isinstance(e, Cond):
        _names_in_expr(e.cond, out)
        _names_in_expr(e.then, out)
        _names_in_expr(e.orelse, out)


def _names_in_stmt(s: Stmt, out: set[str]) -> None:
    """Every variable name occurring in ``s`` — reads and write targets."""
    if isinstance(s, Assign):
        _names_in_expr(s.target, out)
        _names_in_expr(s.value, out)
    elif isinstance(s, If):
        for (c, body) in s.branches:
            _names_in_expr(c, out)
            for x in body:
                _names_in_stmt(x, out)
        for x in s.orelse:
            _names_in_stmt(x, out)
    elif isinstance(s, DoConcurrent):
        for (idx, lo, hi) in s.controls:
            out.add(idx)
            _names_in_expr(lo, out)
            _names_in_expr(hi, out)
        for x in s.body:
            _names_in_stmt(x, out)
    elif isinstance(s, Do):
        idx, lo, hi = s.control
        out.add(idx)
        _names_in_expr(lo, out)
        _names_in_expr(hi, out)
        for x in s.body:
            _names_in_stmt(x, out)


def _reads_before_redef(name: str, stmts: tuple[Stmt, ...]) -> bool:
    """Could the statements read ``name`` before unconditionally reassigning
    it? Conservative: any occurrence inside an ``If`` (conditions or branches)
    counts as a read, since a redefinition there is only conditional. Used to
    decide whether a local left undefined on some path of a join is dead."""
    for s in stmts:
        if isinstance(s, Assign):
            reads: set[str] = set()
            _names_in_expr(s.value, reads)
            if name in reads:
                return True
            if isinstance(s.target, Var) and s.target.name == name:
                return False          # unconditionally redefined before any read
            continue
        names: set[str] = set()
        _names_in_stmt(s, names)
        if name in names:
            return True
    return False


def functionalize(kernel: Kernel) -> tuple[tuple[Param, ...], tuple[str, ...], FunExpr]:
    """Translate the (pointized) imperative body into one functional expression.

    Returns ``(input_params, output_names, expr)`` where the outputs are the
    ``inout``/``out`` parameters in declaration order — or the single
    ``result`` parameter of a function kernel; ``expr`` evaluates to their
    tuple. Locals become ``Let`` bindings; an ``inout``/``out`` output's
    current value is tracked symbolically, starting at its own input ``Var``;
    a ``result`` starts unbound (see the module docstring, which also states
    the control-flow-join semantics implemented by ``merge_if`` below).
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

    def go(stmts: tuple[Stmt, ...], state: dict[str, Expr],
           bound: frozenset[str]) -> FunExpr:
        """``state``: the outputs' current symbolic values (a result only once
        assigned); ``bound``: the locals currently in scope via ``Let``."""
        if not stmts:
            return materialize(state)
        head, rest = stmts[0], stmts[1:]
        if isinstance(head, Assign):
            name = head.target.name
            value = subst(head.value, state, bound)
            if name in local_names:
                return Let(name, value, go(rest, state, bound | {name}))
            if name in outputs:
                return go(rest, {**state, name: value}, bound)
            raise UnsupportedConstruct(
                f"{kernel.name}: assignment to '{name}', neither local nor output")
        if isinstance(head, If):
            if rest:
                # Control-flow join: the remaining statements run against the
                # MERGED state, with the merged locals bound first, so a later
                # read of anything this IF may have updated observes the
                # conditional value (sequential semantics).
                merged, merged_locals, _ = merge_if(head, state, bound, rest)

                def bind(items: list[tuple[str, Expr]],
                         bound_now: frozenset[str]) -> FunExpr:
                    if not items:
                        return go(rest, merged, bound_now)
                    (v, e), tail = items[0], items[1:]
                    return Let(v, e, bind(tail, bound_now | {v}))
                return bind(list(merged_locals.items()), bound)

            def branch(i: int) -> FunExpr:
                if i < len(head.branches):
                    cond, body = head.branches[i]
                    return IfExpr(subst(cond, state, bound),
                                  go(body, dict(state), bound), branch(i + 1))
                return go(head.orelse, dict(state), bound)
            return branch(0)
        raise UnsupportedConstruct(f"{kernel.name}: {type(head).__name__} is unsupported here")

    def merge_if(head: If, state: dict[str, Expr], bound: frozenset[str],
                 continuation: tuple[Stmt, ...]
                 ) -> tuple[dict[str, Expr], dict[str, Expr], list[str]]:
        """Merge an ``If`` that statements follow (``continuation`` = everything
        that executes after it, used only for the dead-local scan).

        Returns ``(state', merged_locals, changed)``: the outputs' merged
        state, the locals to bind after the join (first-assignment order),
        and the names of every variable the merge touched.
        """
        conds = [subst(c, state, bound) for (c, _) in head.branches]
        bodies = [b for (_, b) in head.branches] + [head.orelse]
        states: list[dict[str, Expr]] = []
        order: list[str] = []
        for body in bodies:
            st, assigned = branch_state(body, state, bound, continuation)
            states.append(st)
            for v in assigned:
                if v not in order:
                    order.append(v)
        merged = dict(state)
        merged_locals: dict[str, Expr] = {}
        changed: list[str] = []
        for v in order:
            values: Optional[list[Expr]] = []
            for st in states:
                if v in st:
                    values.append(st[v])
                elif v in local_names and v in bound:
                    values.append(Var(v))     # this path keeps the prior binding
                elif v in local_names:
                    values = None             # undefined on this path
                    break
                else:
                    # Only a `result` can be missing from a side: inout/out
                    # outputs are in `state` from the start.
                    raise UnsupportedConstruct(
                        f"{kernel.name}: function result '{v}' is assigned in "
                        f"only some branches of a joined IF — undefined on the "
                        f"other paths")
            if values is None:
                if _reads_before_redef(v, continuation):
                    raise UnsupportedConstruct(
                        f"{kernel.name}: local '{v}' is assigned on only some "
                        f"paths of a joined IF, was not assigned before it, "
                        f"and is read after the join — undefined on the other "
                        f"paths")
                continue                      # dead after the join: dropped
            expr = values[-1]
            for c, val in reversed(list(zip(conds, values[:-1]))):
                expr = Cond(c, val, expr)
            if v in local_names:
                merged_locals[v] = expr
            else:
                merged[v] = expr
            changed.append(v)
        return merged, merged_locals, changed

    def branch_state(body: tuple[Stmt, ...], state: dict[str, Expr],
                     bound: frozenset[str], continuation: tuple[Stmt, ...]
                     ) -> tuple[dict[str, Expr], list[str]]:
        """Run one branch body sequentially against a copy of the incoming
        state. Locals assigned here are tracked in the copy (later reads within
        the branch substitute them), so the merge can pair per-path values.
        Returns the branch's outgoing state and the names it assigned, in order."""
        st, assigned = dict(state), []
        for idx, s in enumerate(body):
            if isinstance(s, Assign):
                name = s.target.name
                if name not in outputs and name not in local_names:
                    raise UnsupportedConstruct(
                        f"{kernel.name}: assignment to '{name}', neither local "
                        f"nor output")
                st[name] = subst(s.value, st, bound)
                if name not in assigned:
                    assigned.append(name)
            elif isinstance(s, If):
                # A nested IF (a join inside the branch, or its tail): merge it
                # against the branch state; everything after it — the rest of
                # this branch, then the outer continuation — is what may read
                # the values it leaves.
                inner_cont = tuple(body[idx + 1:]) + continuation
                st, inner_locals, changed = merge_if(s, st, bound, inner_cont)
                st.update(inner_locals)
                for v in changed:
                    if v not in assigned:
                        assigned.append(v)
            else:
                raise UnsupportedConstruct(
                    f"{kernel.name}: {type(s).__name__} inside a joined IF "
                    f"branch is unsupported")
        return st, assigned

    def subst(e: Expr, state: dict[str, Expr], bound: frozenset[str]) -> Expr:
        """Replace reads of tracked variables with their current symbolic value.

        Unconditional on purpose: when the current value is the identity
        ``Var(name)`` the substitution is a no-op, and when it is any other
        expression — including a plain ``Var`` alias like ``b = a`` — the read
        must see it, or a later statement would silently read the *input*
        value. Sequential threading is the whole contract here.

        A local read by name must be in scope (``bound``) or tracked in
        ``state`` (inside a joined branch); otherwise it is read before any
        assignment — an undefined value in the source — and refuses. The
        caller supplies no value for a function result (unlike an inout/out
        argument), so reading it before its first assignment refuses the same
        way."""
        if isinstance(e, Var):
            if e.name in state:
                return state[e.name]
            if e.name in results:
                raise UnsupportedConstruct(
                    f"{kernel.name}: function result '{e.name}' is read before it "
                    f"is assigned")
            if e.name in local_names and e.name not in bound:
                raise UnsupportedConstruct(
                    f"{kernel.name}: local '{e.name}' is read before it is "
                    f"assigned")
            return e
        if isinstance(e, Paren):
            return Paren(subst(e.inner, state, bound))
        if isinstance(e, Neg):
            return Neg(subst(e.inner, state, bound))
        if isinstance(e, BinOp):
            return BinOp(e.op, subst(e.lhs, state, bound), subst(e.rhs, state, bound))
        if isinstance(e, Cmp):
            return Cmp(e.op, subst(e.lhs, state, bound), subst(e.rhs, state, bound))
        if isinstance(e, Call):
            return Call(e.name, tuple(subst(a, state, bound) for a in e.args))
        if isinstance(e, Cond):
            return Cond(subst(e.cond, state, bound), subst(e.then, state, bound),
                        subst(e.orelse, state, bound))
        return e

    # inout/out outputs start at the value the caller passed in; a result
    # starts unbound — the caller passes nothing in for it.
    state0: dict[str, Expr] = {o: Var(o) for o in outputs if o not in results}
    return kernel.params, outputs, go(kernel.body, state0, frozenset())
