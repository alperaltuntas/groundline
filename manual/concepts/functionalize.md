# Functionalize: state threading and the control-flow join

Lean models are pure functions, but kernels are written imperatively — they
assign, they branch, they overwrite. `kir.functionalize` bridges the gap: it
turns a (pointized, rank-0) imperative body into **one functional expression**
that evaluates to the tuple of output values.

## The basic translation

- **Outputs** are the `intent(inout)`/`intent(out)` parameters, in declaration
  order. Each output's *current value* is tracked symbolically, starting at
  its own input variable.
- **Local assignments** become `let` bindings: `w = s * a(i)` prints as
  `let w := s * a`.
- **Assignments to outputs** update the symbolic state — later reads of that
  output see the updated expression, not the original input. This sequential
  threading is the whole contract: after `b = a`, a later read of `b` *must*
  see `a`. (A subtle bug hid exactly here once — the substitution skipped
  plain-variable aliases — and machine-checking flushed it out; the
  [CW84 case study](../case-studies/ppm-limit-cw84.md) tells that story.)
- **Structured `if`/`elseif`/`else`** at the *end* of a path becomes a
  functional if-expression, each branch ending by materializing the output
  tuple.
- **A function result** (Fortran `result(name)`; a C++ return value) is the
  single output and, unlike an `inout`/`out` argument, **the caller supplies
  no value for it**: it starts undefined, and the model starts it unbound. So
  reading it before its first assignment,
  leaving it unassigned on some path, or assigning it on only one side of a
  join all refuse — each would model an undefined value. A result alongside
  other outputs refuses too (one output convention per kernel).

For a straight-line kernel this yields exactly the shape a Lean-literate
reader would write by hand — compare `GeneratedFtn.lean`'s `ppm_limit_pos`
with its Fortran source in the
[first case study](../case-studies/ppm-limit-pos.md).

## The control-flow join

The hard case is a statement *after* an `if` — a control-flow join. The code
below the join must observe whichever values the branches left behind:

```fortran
if (FunFac > RLdiff2) h_L = 3.0*h_i - 2.0*h_R
if (FunFac < -RLdiff2) h_R = 3.0*h_i - 2.0*h_L   ! reads h_L, possibly just updated
```

Functionalize merges a join **sequentially**, exactly as the source executes
it:

- every branch body — then, each elseif, else (an absent else is an empty
  branch) — is run against a *copy* of the incoming state. Assignments
  update the copy; a local assigned inside the branch is tracked in the copy
  too, so later reads within the branch see it; a nested `if` inside the
  branch is merged recursively against the copy;
- each variable some branch assigned becomes one conditional chain over the
  branch conditions, `if c₁ then s₁[v] else if c₂ then s₂[v] else s_else[v]`
  — an inline conditional expression (`Cond`, the one kernel-IR node no
  frontend ever produces);
- merged **outputs** update the state; merged **locals** are bound by `let`
  right after the join, in first-assignment order. The statements that follow
  then run against the merged values.

Locals need one more rule, because a branch may define a local the others do
not. If the local already had a `let` binding before the `if`, the other
paths keep that binding (`let w := if u > 0 then u else w`, Lean's shadowing
saying exactly what the source does). If it had none, the local is undefined
on those paths: when nothing after the join reads it, it is simply dropped
(flux_elem's `CFL`, `curv_3`, `dh` are of this kind — inlined where the
branch read them, dead afterwards); when something does read it, functionalize
**refuses** — a conservative read scan, so it may refuse spuriously, never
mismodel. A local read before any assignment at all refuses outright.

Two locals may read *each other's* prior values across the branches —
`if (FA_avg > max(FA_0, FAmt_L)) then FA_avg = … elseif (FA_avg < min(FA_0,
FAmt_L)) then FA_0 = FA_avg endif`. No order of `let`s can express that
(whichever is bound first is read by the other as its *new* value), so such
locals are bound together by one destructuring `let`, its branches tuples:

```lean
let (FA_avg, FA_0) := if FA_avg > max (FA_0) (FAmt_L) then (max (FA_0) (FAmt_L), FA_0)
                      else if FA_avg < min (FA_0) (FAmt_L) then (FA_avg, FA_avg) else (FA_avg, FA_0)
```

Every right-hand side is evaluated before any name changes — exactly the
source's semantics. The C++ `else if` is flattened into the branch list at
extraction, so both frontends yield the same join.

Until 2026-09-05 the join was supported in exactly one shape — a
single-branch `if` assigning only to outputs, the CW84 kernel's pair of
guarded assignments — and everything else refused. The generalization was a
semantics decision taken explicitly when `flux_elem` demanded it (its
if/elseif/else assigns four locals and one output, and the derivative
computed after the join reads one of the locals); the old shape is a special
case of the new rule and the CW84 def came out byte-identical. A trailing
`if` — nothing after it — keeps the structured if-expression path, so kernels
without joins are unaffected.

## No pending value is ever captured

An output's value is a symbolic expression over the names in scope, printed
where the path materializes it. That is only right if none of those names is
re-bound in between: `BT_cont%FA_u_W0(I,j) = FA_0 ; … ; FA_0 = FAmt_0` must
not make the output read the second `FA_0`. So before any `let` shadows a
name, every pending value of the path's outputs (or of a fold's states) that
mentions it is let-bound under its own name first — `let FA_u_W0 := FA_0` —
recursively, and the tracked value becomes that reference. A join's `let`s
obey the same rule: one is emitted only when no other pending value mentions
its name (the values all speak of the bindings *before* the `if`), in
first-assignment order among the eligible; the mutually-dependent remainder
is the destructuring case above.

This discipline was added on 2026-09-05, when `set_zonal_BT_cont` re-assigned
a local an output had just read. Regenerating every banked def under it
changed nothing — no existing theorem had rested on a captured value — but
the first extraction of that kernel had printed one, on both sides alike, and
the theorem would have held. The hazard is pinned on hand-built kernels in
`tests/test_functionalize_capture.py`.

## Column statements

For [column kernels](column-kernels.md) three more statement forms reach
functionalize, all frontend-neutral:

- a **call to a banked primitive** binds each output as a projection of the
  applied def, `let uh_val := (flux_elem_point …).1`, in the callee's output
  order — a local receiver by `let`, a state receiver by state update;
- a **map** binds each per-layer array its body writes as `let a := fun k =>
  …`, later statements reading `a k`; within the body, later statements see
  the values earlier ones assigned;
- a **fold** binds its state variables to `ks.foldl (fun s k => step) init`,
  where the step is the body functionalized with the state variables as its
  outputs (locals inside are per-iteration `let`s, control flow merges as
  anywhere else) and `init` is the states' current values. One state binds
  by `let s := …`; several by a destructuring `let (a, b) := ks.foldl (fun
  (a, b) k => …) (a, b)`. The binding shadows the earlier names, so what
  follows reads the fold's result.

## Why this design is easy to trust

Everything functionalize does is *syntactic* state bookkeeping — substitution
and merging of expression trees — with no arithmetic knowledge whatsoever. It
cannot "simplify" anything, so the printed model preserves the source's
computation structure; whether two differently-shaped models are equal is
always [the prover's job, not the printer's](printer-fidelity.md). And the
representation it chooses for joins (inline `Cond`s inside the result tuple)
versus the natural hand-written one (sequential `let`s) is a *propositional*,
not definitional, difference — the equivalence proofs absorb it with a
two-line case split, as both CW84 fidelity theorems show.
