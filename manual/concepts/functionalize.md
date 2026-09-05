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

Functionalize supports the join in **exactly one shape**, deliberately
restricted:

- the `if` has a single branch (no elseif chain — the merge formula below is
  binary);
- every branch body consists solely of assignments to *output* variables — no
  locals (a `let` may not escape a branch), no nested `if`s.

The merge is per variable: each variable `v` some branch assigned gets

```text
state'[v] = Cond(cond, state_then[v], state_else[v])
```

— an inline conditional expression (`if cond then … else …` in the printed
Lean) — and variables no branch assigned pass through unchanged. The remaining
statements then run against the *merged* state, so a later read of a variable
the `if` may have updated observes the conditional value: sequential
semantics, exactly as in the source. `Cond` is the one kernel-IR node no
frontend ever produces — only this merge creates it.

Any other join shape refuses. The restriction is not a temporary limitation
waiting to be quietly relaxed — it is the one shape the merge semantics was
designed for, tested on (the golden fixture pins the merged-state threading
visibly), and audited against. A trailing `if` — nothing after it — keeps the
structured if-expression path, so kernels without joins are unaffected.

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
