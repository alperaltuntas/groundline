"""The column pass: from a Fortran subroutine (or a C++ ``ParallelFor``
lambda) whose loops run over horizontal cells and a vertical index, to a
per-column kernel over folds and maps along the vertical index.

Design: ``docs/COLUMN_KERNELS.md``. In short — the manifest names the
**column indices** (``columns = ["j", "i"]``); every loop nest is split into
its column indices and its remaining index ``k``; the column indices are
pointized with the point tier's rules (A: own-cell writes, B: component reads,
C: read-only stencils, D: nest-invariant locals), and what remains is either a
per-column scalar statement, a **map** over ``k`` (writes only own-``k``
cells: ``let a := fun k => …``) or a **fold** over ``k`` (writes per-column
state: ``ks.foldl (fun s k => …) s``). Calls to *banked* primitives resolve
against the callee's extracted kernel into :class:`~groundline.kir.CallBind`.

Trusted-base rule (VISION D6): deterministic, small enough to audit; anything
outside the subset raises :class:`~groundline.kir.UnsupportedConstruct` —
refusal, never a guess. The semantics decisions the pass implements were
licensed by the user on 2026-09-05 (DEVLOG, docs/COLUMN_KERNELS.md §6): the
fold model, calls to banked primitives, per-column Bool inputs, explicit
column indices, and masks (a ``do concurrent`` mask is ``if mask then body
else skip``: on a fold, the step keeps its state; on per-column statements,
an ``if`` without else; on a map it refuses — skipped cells stay unwritten).

Array classification (by subscript shape, never by declared rank):

- subscripts = the column indices (plainly)       → a per-column scalar ``Var``
- subscripts = the column indices + ``k``        → a per-k array read ``App(name, k)``
- a literal offset on a column index             → rule C: a synthesized stencil
  input (per-column or per-k), admitted when the array is never written in the
  nest and the nest is ``do concurrent``
- a literal offset on ``k``                      → refuses (a k-recurrence)
- all subscripts ``:`` on a column-shaped array  → the whole-array assignment
  ``a(:,:) = e`` is the per-column scalar assignment ``a = e``
- a *local* array indexed plainly by a strict subset of the column indices
  (``duL(I)`` under ``do j``: a row scratch)      → a per-column scalar ``Var``.
  Sound because the cells the columns share along the omitted index are a
  local nobody outside observes, the omitted index is bound by a plain
  (sequential) loop, and a read of the scratch before the column body writes
  it — the only way a value could cross from one column to another — refuses
  in ``functionalize``
- anything else                                  → refuses

Writes: to a per-column cell or scalar local outside any k-loop → a scalar
statement; inside a plain ``do k`` → fold state; to an own-``k`` cell inside a
k-loop → a map target; to a component array of an ``intent(inout)``
derived-type dummy at the column cell (``BT_cont%FA_u_W0(I,j) = …``) → a
synthesized per-column *output* named after the component (rule B for
outputs). A k-loop writing both per-column state and per-k cells is a
**scan** and refuses (Tier C).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from groundline.kir import (
    App, ArrayRef, Assign, BinOp, Call, CallBind, CallStmt, Cmp, ComponentRef,
    Cond, Do, DoConcurrent, Expr, FoldStmt, If, IntLit, Kernel, MapStmt, Neg,
    Param, Paren, RealLit, Slice, Stmt, UnsupportedConstruct, Var,
)


@dataclass(frozen=True)
class Callee:
    """What the column pass needs to know about a banked primitive: the name
    of its generated def, its full dummy list in source order (the caller's
    actuals are matched to it positionally), and its kept parameters — the
    dummies its own extraction did not drop — with their types and intents."""
    def_name: str
    dummies: tuple[str, ...]
    params: tuple[Param, ...]


def columnize(kernel: Kernel, columns: tuple[str, ...],
              callees: dict[str, Callee], *, columns_bound: bool = False) -> Kernel:
    """Reduce ``kernel`` to a per-column kernel over the vertical index.

    ``columns`` names the column indices as they appear in the loops (already
    lowercased on the Fortran side). ``callees`` maps a callable name (as it
    appears in ``CallStmt``) to its :class:`Callee`. ``columns_bound`` says
    the body is already per-column — a C++ ``ParallelFor`` lambda, whose
    column indices are its parameters — so its loops run over ``k`` alone;
    a Fortran subroutine binds the columns by its own loops.
    """
    cols = tuple(columns)
    if len(set(cols)) != len(cols) or not cols:
        raise UnsupportedConstruct(f"{kernel.name}: column indices must be distinct and nonempty")
    param_by_name = {p.name: p for p in kernel.params}
    local_by_name = {p.name: p for p in kernel.locals}
    local_names = set(local_by_name)

    # ---- the whole body's write set (rules C and D are gated on it) --------
    written: set[str] = set()

    def collect_writes(s: Stmt) -> None:
        if isinstance(s, Assign):
            t = s.target
            written.add(t.name if isinstance(t, (Var, ArrayRef)) else t.base)
        elif isinstance(s, CallStmt):
            callee = callees.get(s.callee)
            if callee is not None:
                for dummy, actual in zip(callee.dummies, s.args):
                    p = next((q for q in callee.params if q.name == dummy), None)
                    if p is not None and p.intent in ("out", "inout"):
                        if isinstance(actual, (Var, ArrayRef)):
                            written.add(actual.name)
        elif isinstance(s, If):
            for (_, body) in s.branches:
                for x in body:
                    collect_writes(x)
            for x in s.orelse:
                collect_writes(x)
        elif isinstance(s, (Do, DoConcurrent)):
            for x in s.body:
                collect_writes(x)

    for s in kernel.body:
        collect_writes(s)

    # ---- synthesized inputs (rules B, C, D), first-use order ---------------
    synth: dict[tuple, Param] = {}
    # per-k-ness of every array name seen, to keep each name's shape consistent
    shape: dict[str, str] = {}       # name -> 'column' | 'k'

    def note_shape(name: str, kind: str) -> None:
        if shape.setdefault(name, kind) != kind:
            raise UnsupportedConstruct(
                f"{kernel.name}: '{name}' is read both as a per-column and as a "
                f"per-k array")

    def synth_param(key: tuple, name: str, type_: str, what: str,
                    intent: str = "in") -> Param:
        if key not in synth:
            taken = (name in param_by_name or name in cols
                     or (name in local_names and key[0] != "local")
                     or any(p.name == name for p in synth.values()))
            if taken:
                raise UnsupportedConstruct(
                    f"{kernel.name}: synthesized parameter '{name}' for {what} "
                    f"collides with an existing name")
            synth[key] = Param(name, type_, intent, 0)
        return synth[key]

    # ---- subscripts ----------------------------------------------------------
    def parse_subs(e, indices: tuple[str, ...]):
        """(index, offset) per subscript, or None for anything else."""
        out = []
        for sub in e.subscripts:
            if isinstance(sub, Var) and sub.name in indices:
                out.append((sub.name, 0))
            elif (isinstance(sub, BinOp) and sub.op in ("add", "sub")
                    and isinstance(sub.lhs, Var) and sub.lhs.name in indices
                    and isinstance(sub.rhs, IntLit)):
                out.append((sub.lhs.name, int(sub.rhs.text) * (1 if sub.op == "add" else -1)))
            else:
                out.append(None)
        return out

    def fmt(parsed) -> str:
        return "(" + ", ".join(
            "?" if p is None else (p[0] if p[1] == 0 else f"{p[0]}{'+' if p[1] > 0 else '-'}{abs(p[1])}")
            for p in parsed) + ")"

    def suffix(parsed) -> str:
        return "".join(f"_{i}{'p' if o > 0 else 'm'}{abs(o)}" for (i, o) in parsed if o != 0)

    # ---- expression scalarization within a nest context -------------------
    class Ctx:
        """The current nest: its k index (None outside k-loops), which column
        indices were bound by an independence-asserting construct (`do
        concurrent`, or the `ParallelFor` a lambda runs under) — the license
        for a stencil along that index — and the array names the nest
        writes."""
        def __init__(self, k: Optional[str], col_conc: dict[str, bool], nest_writes: set[str]):
            self.k, self.col_conc, self.nest_writes = k, col_conc, nest_writes

    def classify(e, ctx: Ctx, what: str):
        """An ArrayRef/ComponentRef's subscripts → ('column' | 'k', parsed).
        Column indices may carry literal offsets (rule C, checked by the
        caller); k may not."""
        indices = cols + ((ctx.k,) if ctx.k else ())
        parsed = parse_subs(e, indices)
        if None in parsed:
            raise UnsupportedConstruct(
                f"{kernel.name}: {what}{fmt(parsed)} is not indexed by the column "
                f"indices {cols}" + (f" and the k index '{ctx.k}'" if ctx.k else ""))
        names = [p[0] for p in parsed]
        if len(set(names)) != len(names):
            raise UnsupportedConstruct(f"{kernel.name}: {what}{fmt(parsed)} repeats an index")
        if any(o != 0 for (i, o) in parsed if i == ctx.k):
            raise UnsupportedConstruct(
                f"{kernel.name}: {what}{fmt(parsed)} reads at an offset in the k "
                f"index — a k-recurrence")
        if set(names) == set(cols):
            return "column", parsed
        if ctx.k and set(names) == set(cols) | {ctx.k}:
            return "k", parsed
        if (isinstance(e, ArrayRef) and e.name in local_names and names
                and set(names) < set(cols) and all(o == 0 for (_, o) in parsed)):
            # A row scratch (module docstring): per column, provided the
            # omitted column indices run sequentially — under a do concurrent
            # the columns sharing a cell would race.
            racing = [c for c in cols if c not in names and ctx.col_conc.get(c, False)]
            if racing:
                raise UnsupportedConstruct(
                    f"{kernel.name}: local array {what}{fmt(parsed)} is shared by "
                    f"the columns along {racing}, bound by do concurrent (or "
                    f"ParallelFor) — a race the source could not mean")
            return "column", parsed
        raise UnsupportedConstruct(
            f"{kernel.name}: {what}{fmt(parsed)} is indexed by neither the column "
            f"indices {cols} nor the columns plus the k index")

    def stencil_ok(name: str, parsed, ctx: Ctx, what: str) -> None:
        if all(o == 0 for (_, o) in parsed):
            return
        for (idx, off) in parsed:
            if off != 0 and not ctx.col_conc.get(idx, False):
                raise UnsupportedConstruct(
                    f"{kernel.name}: neighbor read {what}{fmt(parsed)} along "
                    f"'{idx}', an index bound by a plain-do loop — read-only "
                    f"stencils are admitted along do concurrent (or ParallelFor) "
                    f"indices only (the plain-DO schema-lemma variant is not yet "
                    f"proved)")
        if name in ctx.nest_writes:
            raise UnsupportedConstruct(
                f"{kernel.name}: neighbor read {what}{fmt(parsed)} of an array "
                f"the nest writes — a cross-iteration recurrence")

    def scal(e: Expr, ctx: Ctx, want: str = "real") -> Expr:
        if isinstance(e, (RealLit, IntLit)):
            return e
        if isinstance(e, Var):
            if e.name in cols or e.name == ctx.k:
                raise UnsupportedConstruct(
                    f"{kernel.name}: loop index '{e.name}' used as a value")
            if e.name in local_names and e.name not in written:
                loc = local_by_name[e.name]          # rule D: nest-invariant local
                return Var(synth_param(("local", e.name), e.name, loc.type,
                                       f"the invariant local {e.name}").name)
            return e
        if isinstance(e, ArrayRef):
            kind, parsed = classify(e, ctx, e.name)
            stencil_ok(e.name, parsed, ctx, e.name)
            if all(o == 0 for (_, o) in parsed):
                note_shape(e.name, kind)
                return Var(e.name) if kind == "column" else App(e.name, ctx.k)
            name = e.name + suffix(parsed)
            p = synth_param(("stencil", e.name, tuple(parsed)), name,
                            "real" if kind == "column" else "real[k]",
                            f"the neighbor read {e.name}{fmt(parsed)}")
            return Var(p.name) if kind == "column" else App(p.name, ctx.k)
        if isinstance(e, ComponentRef):
            base = param_by_name.get(e.base)
            if (base is None or not base.type.startswith("derived:")
                    or base.intent != "in"):
                raise UnsupportedConstruct(
                    f"{kernel.name}: component read {e.base}%{e.comp} — the base "
                    f"must be an intent(in) derived-type dummy argument")
            what = f"the component read {e.base}%{e.comp}"
            if e.subscripts == ():
                return Var(synth_param(("comp", e.base, e.comp), e.comp, want, what).name)
            indices = cols + ((ctx.k,) if ctx.k else ())
            parsed = parse_subs(e, indices)
            if None in parsed or len({p[0] for p in parsed}) != len(parsed):
                raise UnsupportedConstruct(
                    f"{kernel.name}: {what}{fmt(parsed)} is not indexed by loop indices")
            names = {p[0] for p in parsed}
            if any(o != 0 for (i, o) in parsed if i == ctx.k):
                raise UnsupportedConstruct(
                    f"{kernel.name}: {what}{fmt(parsed)} reads at an offset in k")
            for (idx, off) in parsed:
                if off != 0 and not ctx.col_conc.get(idx, False):
                    raise UnsupportedConstruct(
                        f"{kernel.name}: neighbor read {what}{fmt(parsed)} along "
                        f"'{idx}', an index bound by a plain-do loop — read-only "
                        f"stencils are admitted along do concurrent (or ParallelFor) "
                        f"indices only")
            per_k = ctx.k in names
            if not (names <= set(cols) | ({ctx.k} if ctx.k else set())):
                raise UnsupportedConstruct(
                    f"{kernel.name}: {what}{fmt(parsed)} is indexed outside the loop indices")
            name = e.comp + suffix(parsed)
            p = synth_param(("comp", e.base, e.comp, tuple(parsed)), name,
                            ("real[k]" if per_k else want), what)
            return App(p.name, ctx.k) if per_k else Var(p.name)
        if isinstance(e, Paren):
            return Paren(scal(e.inner, ctx))
        if isinstance(e, Neg):
            return Neg(scal(e.inner, ctx))
        if isinstance(e, BinOp):
            return BinOp(e.op, scal(e.lhs, ctx), scal(e.rhs, ctx))
        if isinstance(e, Cmp):
            return Cmp(e.op, scal(e.lhs, ctx), scal(e.rhs, ctx))
        if isinstance(e, Call):
            return Call(e.name, tuple(scal(a, ctx) for a in e.args))
        if isinstance(e, Slice):
            raise UnsupportedConstruct(
                f"{kernel.name}: an array section ':' outside a whole-array assignment")
        raise UnsupportedConstruct(f"{kernel.name}: cannot scalarize {type(e).__name__}")

    # ---- targets ------------------------------------------------------------
    def target_of(t, ctx: Ctx) -> tuple[str, str]:
        """(name, 'column' | 'k' | 'scalar') for an assignment/call-output place."""
        if isinstance(t, Var):
            if t.name in cols or t.name == ctx.k:
                raise UnsupportedConstruct(f"{kernel.name}: assignment to loop index '{t.name}'")
            return t.name, "scalar"
        if isinstance(t, ArrayRef):
            if t.subscripts and all(isinstance(s, Slice) for s in t.subscripts):
                if len(t.subscripts) != len(cols):
                    raise UnsupportedConstruct(
                        f"{kernel.name}: whole-array assignment to '{t.name}' of rank "
                        f"{len(t.subscripts)} — only column-shaped arrays (rank "
                        f"{len(cols)}) may be assigned whole")
                if ctx.k is not None:
                    raise UnsupportedConstruct(
                        f"{kernel.name}: whole-array assignment inside a k-loop")
                note_shape(t.name, "column")
                return t.name, "column"
            kind, parsed = classify(t, ctx, t.name)
            if any(o != 0 for (_, o) in parsed):
                raise UnsupportedConstruct(
                    f"{kernel.name}: write to a neighbor cell {t.name}{fmt(parsed)} — "
                    f"every write must land in the iteration's own cell")
            note_shape(t.name, kind)
            return t.name, kind
        if isinstance(t, ComponentRef):
            # Rule B for outputs: a component array of an intent(inout)
            # derived-type dummy, written at the column cell, is a per-column
            # output named after the component. (Reads of such a component
            # refuse in `scal` — the base is not intent(in) — so an output
            # component is write-only, and its incoming value is never read.)
            base = param_by_name.get(t.base)
            what = f"the component write {t.base}%{t.comp}"
            if (base is None or not base.type.startswith("derived:")
                    or base.intent != "inout"):
                raise UnsupportedConstruct(
                    f"{kernel.name}: {what} — the base must be an intent(inout) "
                    f"derived-type dummy argument")
            if ctx.k is not None:
                raise UnsupportedConstruct(
                    f"{kernel.name}: {what} inside a k-loop is not supported")
            parsed = parse_subs(t, cols)
            names = [p[0] for p in parsed if p is not None]
            if (None in parsed or set(names) != set(cols) or len(names) != len(cols)
                    or any(o != 0 for (_, o) in parsed)):
                raise UnsupportedConstruct(
                    f"{kernel.name}: {what}{fmt(parsed)} must be indexed exactly by "
                    f"the column indices {cols}")
            p = synth_param(("compout", t.base, t.comp), t.comp, "real", what, intent="out")
            return p.name, "column"
        raise UnsupportedConstruct(f"{kernel.name}: unsupported assignment target")

    # ---- calls ---------------------------------------------------------------
    def resolve_call(s: CallStmt, ctx: Ctx) -> tuple[CallBind, list[tuple[str, str]]]:
        callee = callees.get(s.callee)
        if callee is None:
            raise UnsupportedConstruct(
                f"{kernel.name}: call to '{s.callee}', which is not a banked "
                f"primitive of this manifest (nor declared ignorable)")
        if len(s.args) != len(callee.dummies):
            raise UnsupportedConstruct(
                f"{kernel.name}: call to '{s.callee}' with {len(s.args)} actuals "
                f"for {len(callee.dummies)} dummies")
        kept = {p.name: p for p in callee.params}
        args: list[Expr] = []
        outs: list[str] = []
        out_kinds: list[tuple[str, str]] = []
        for dummy, actual in zip(callee.dummies, s.args):
            p = kept.get(dummy)
            if p is None:
                continue                         # a dummy the callee dropped (grid structs)
            if p.intent == "in":
                args.append(scal(actual, ctx, want=p.type))
            elif p.intent in ("out", "inout"):
                name, kind = target_of(actual, ctx)
                args.append(scal(actual, ctx) if p.intent == "inout" else RealLit("0"))
                outs.append(name)
                out_kinds.append((name, kind))
            else:
                raise UnsupportedConstruct(
                    f"{kernel.name}: callee '{s.callee}' parameter '{dummy}' has no intent")
        return CallBind(callee.def_name, tuple(args), tuple(outs)), out_kinds

    # ---- statements ----------------------------------------------------------
    def nest_indices(loop) -> tuple[list[str], tuple[Stmt, ...], dict[str, bool],
                                    Optional[Expr]]:
        """Indices (source order), innermost body, per-index concurrency
        (True under `do concurrent`) and the mask of a nest. Plain levels must
        be perfectly nested (rule A); a plain chain may end in a `do
        concurrent` (`do k ; do concurrent (I, mask)`), whose indices and
        mask are the nest's innermost."""
        names: list[str] = []
        conc: dict[str, bool] = {}
        body: tuple[Stmt, ...] = (loop,)
        while len(body) == 1 and isinstance(body[0], (Do, DoConcurrent)):
            inner = body[0]
            if isinstance(inner, DoConcurrent):
                for (n, _, _) in inner.controls:
                    names.append(n)
                    conc[n] = True
                return names, inner.body, conc, inner.mask
            names.append(inner.control[0])
            conc[inner.control[0]] = False
            body = inner.body
        return names, body, conc, None

    def nest_write_names(body: tuple[Stmt, ...]) -> set[str]:
        acc: set[str] = set()
        saved = set(written)
        written.clear()
        for x in body:
            collect_writes(x)
        acc = set(written)
        written.clear()
        written.update(saved)
        return acc

    def carried_locals(body: tuple[Stmt, ...]) -> set[str]:
        """Scalar locals a k-loop body reads before it writes them — values
        carried from the previous iteration (or from before the loop)."""
        from groundline.kir import _names_in_expr
        written_here: set[str] = set()
        carried: set[str] = set()

        def scan(stmts):
            for s in stmts:
                if isinstance(s, Assign):
                    reads: set[str] = set()
                    _names_in_expr(s.value, reads)
                    if isinstance(s.target, ArrayRef):
                        for sub in s.target.subscripts:
                            _names_in_expr(sub, reads)
                    carried.update(r for r in reads if r in local_names and r not in written_here)
                    if isinstance(s.target, Var):
                        written_here.add(s.target.name)
                elif isinstance(s, CallStmt):
                    callee = callees.get(s.callee)
                    outs = set()
                    if callee is not None:
                        kept = {q.name: q for q in callee.params}
                        for dummy, actual in zip(callee.dummies, s.args):
                            q = kept.get(dummy)
                            if q is not None and q.intent in ("out", "inout") and isinstance(actual, Var):
                                outs.add(actual.name)
                                if q.intent == "inout" and actual.name in local_names and actual.name not in written_here:
                                    carried.add(actual.name)
                            elif q is not None and q.intent == "in":
                                reads: set[str] = set()
                                _names_in_expr(actual, reads)
                                carried.update(r for r in reads if r in local_names and r not in written_here)
                    written_here.update(outs)
                elif isinstance(s, If):
                    reads: set[str] = set()
                    for (c, b) in s.branches:
                        _names_in_expr(c, reads)
                    carried.update(r for r in reads if r in local_names and r not in written_here)
                    for (_, b) in s.branches:
                        scan(b)
                    scan(s.orelse)
        scan(body)
        return carried

    def translate_nest(loop, bound: frozenset[str],
                       bound_conc: dict[str, bool]) -> Optional[Stmt]:
        """``bound``: the column indices already bound by enclosing loops (or
        by the lambda's parameters), ``bound_conc`` whether each was bound by
        an independence-asserting construct. This nest must bind the remaining
        ones (plus at most one k index); when it binds only some, its body may
        hold nothing but further nests."""
        names, body, conc, mask = nest_indices(loop)
        if len(set(names)) != len(names):
            raise UnsupportedConstruct(f"{kernel.name}: duplicate loop index in a nest {names}")
        col_part = [n for n in names if n in cols]
        rest = [n for n in names if n not in cols]
        if any(n in bound for n in col_part):
            raise UnsupportedConstruct(
                f"{kernel.name}: nest over {names} re-binds a column index already "
                f"bound by an enclosing loop")
        now_bound = bound | set(col_part)
        now_conc = {**bound_conc, **{n: conc[n] for n in col_part}}
        if now_bound != set(cols):
            if rest:
                raise UnsupportedConstruct(
                    f"{kernel.name}: nest over {names} runs over the k index before "
                    f"every column index {cols} is bound")
            if mask is not None:
                raise UnsupportedConstruct(
                    f"{kernel.name}: a mask on a nest that binds only some of the "
                    f"column indices {cols} is not supported")
            inner: list[Stmt] = []
            for s in body:
                if isinstance(s, (Do, DoConcurrent)):
                    out = translate_nest(s, now_bound, now_conc)
                    if out is not None:
                        inner.extend(out if isinstance(out, list) else [out])
                else:
                    raise UnsupportedConstruct(
                        f"{kernel.name}: {type(s).__name__} at a partial column "
                        f"level (columns {sorted(set(cols) - now_bound)} not yet "
                        f"bound) — only nests may appear there")
            return inner
        if len(rest) > 1:
            raise UnsupportedConstruct(
                f"{kernel.name}: nest over {names} has more than one non-column index")
        k = rest[0] if rest else None
        ctx = Ctx(k, now_conc, nest_write_names(body))
        stmts: list[Stmt] = []
        writes_k: list[str] = []
        writes_col: list[str] = []
        for s in body:
            out = translate_stmt(s, ctx, writes_k, writes_col)
            if isinstance(out, list):
                stmts.extend(out)
            elif out is not None:
                stmts.append(out)
        if not stmts:
            return None
        # The mask (licensed 2026-09-05): iterations where it is false do
        # nothing, so the body runs under `if mask` — a fold step keeps its
        # state, per-column statements become a guarded block, and a map
        # refuses (its skipped cells would stay unwritten).
        cond = scal(mask, ctx) if mask is not None else None
        if k is None:
            for w in writes_col:
                col_assigned.add(w)
            if cond is not None:
                return If(((cond, tuple(stmts)),), ())
            return stmts if len(stmts) > 1 else stmts[0]        # per-column statements
        # A scalar local written in the k-loop is fold state only when it was
        # bound before the loop or is read before written inside it (carried
        # across iterations); otherwise it is a per-iteration temporary.
        carried = carried_locals(body)
        writes_col = [w for w in writes_col
                      if shape.get(w) == "column" or w in col_assigned or w in carried]
        if writes_k and writes_col:
            raise UnsupportedConstruct(
                f"{kernel.name}: the k-loop over '{k}' writes both per-k cells "
                f"{writes_k} and per-column state {writes_col} — a scan, outside "
                f"the fold model")
        if writes_col:
            if conc[k]:
                raise UnsupportedConstruct(
                    f"{kernel.name}: a do concurrent over '{k}' writes per-column "
                    f"state {writes_col} — a race the source could not mean")
            col_assigned.update(writes_col)
            if cond is not None:
                stmts = [If(((cond, tuple(stmts)),), ())]
            return FoldStmt(k, tuple(writes_col), tuple(stmts))
        if not writes_k:
            raise UnsupportedConstruct(f"{kernel.name}: the k-loop over '{k}' writes nothing")
        if cond is not None:
            raise UnsupportedConstruct(
                f"{kernel.name}: a masked map over '{k}' — the cells of skipped "
                f"iterations would stay unwritten, which a `fun k => …` cannot say")
        return MapStmt(k, tuple(stmts))

    def translate_stmt(s: Stmt, ctx: Ctx, writes_k: list[str],
                       writes_col: list[str]) -> Optional[Stmt]:
        if isinstance(s, Assign):
            name, kind = target_of(s.target, ctx)
            if ctx.k is not None:
                lst = writes_k if kind == "k" else writes_col
                if name not in lst:
                    lst.append(name)
            elif kind == "k":
                raise UnsupportedConstruct(
                    f"{kernel.name}: per-k write to '{name}' outside a k-loop")
            else:
                col_assigned.add(name)
            return Assign(Var(name), scal(s.value, ctx))
        if isinstance(s, CallStmt):
            bind, kinds = resolve_call(s, ctx)
            for name, kind in kinds:
                if ctx.k is not None:
                    lst = writes_k if kind == "k" else writes_col
                    if name not in lst:
                        lst.append(name)
                elif kind == "k":
                    raise UnsupportedConstruct(
                        f"{kernel.name}: per-k call output '{name}' outside a k-loop")
                else:
                    col_assigned.add(name)
            return bind
        if isinstance(s, If):
            # Inside a k-loop: a conditional step of the fold (or map). At
            # the column level: a per-column conditional whose branches may
            # hold per-column statements and whole k-nests (the C++'s
            # `if (active) { for k … }`); functionalize joins the branches.
            def block(body):
                out: list[Stmt] = []
                for x in body:
                    t = translate_stmt(x, ctx, writes_k, writes_col)
                    if isinstance(t, list):
                        out.extend(t)
                    elif t is not None:
                        out.append(t)
                return tuple(out)
            branches = tuple((scal(c, ctx), block(body)) for (c, body) in s.branches)
            return If(branches, block(s.orelse))
        if isinstance(s, (Do, DoConcurrent)):
            if ctx.k is not None:
                raise UnsupportedConstruct(
                    f"{kernel.name}: a loop nested inside the k-loop over '{ctx.k}'")
            return translate_nest(s, frozenset(cols), dict(ctx.col_conc))
        raise UnsupportedConstruct(f"{kernel.name}: {type(s).__name__} is unsupported at the column level")

    # Names assigned so far at the column level (per-column arrays whole or
    # scalar locals) — the values a later fold may carry as state.
    col_assigned: set[str] = set()
    # Outside every loop: for a lambda the columns are bound by ParallelFor
    # (asserted independent); for a subroutine nothing is bound yet.
    conc0 = {c: True for c in cols} if columns_bound else {}
    top = Ctx(None, conc0, set())
    bound0 = frozenset(cols) if columns_bound else frozenset()
    body: list[Stmt] = []
    for s in kernel.body:
        if isinstance(s, (Do, DoConcurrent)):
            out = translate_nest(s, bound0, conc0)
        else:
            out = translate_stmt(s, top, [], [])
        if out is None:
            continue
        if isinstance(out, list):
            body.extend(out)
        else:
            body.append(out)

    # ---- parameters and locals of the column kernel ---------------------------
    from groundline.kir import _names_in_stmt      # the post-pass name collector
    used: set[str] = set()
    for s in body:
        _names_in_stmt(s, used)

    def col_type(p: Param) -> str:
        """A real array is a per-k array or a per-column scalar by how the
        body indexed it (its declared rank is not consulted — AMReX arrays are
        all rank 4, and Fortran shapes may sit on the entity or the
        attribute)."""
        if p.type != "real":
            return p.type
        return "real[k]" if shape.get(p.name) == "k" else "real"

    params = tuple(Param(p.name, col_type(p), p.intent, 0)
                   for p in kernel.params if p.name in used and p.name not in cols)
    params += tuple(synth.values())
    promoted = {key[1] for key in synth if key[0] == "local"}
    locals_ = tuple(Param(p.name, col_type(p), None, 0)
                    for p in kernel.locals
                    if p.name in used and p.name not in cols and p.name not in promoted)
    return Kernel(kernel.name, params, locals_, tuple(body), column=True)
