# Limits & roadmap

The rest of this manual documents what runs today; this page is the
inventory of what does not — and what each missing piece would take.
Everything below is **roadmap**: none of it is implemented, and none of it
should be cited as a capability.

## The frontier: scans, k-recurrences, and unordered reductions

The point tier rests on **point-locality**: each output cell from that cell's
inputs alone. The [column tier](concepts/column-kernels.md) (2026-09-05)
moved the frontier once: an accumulation over the vertical index whose two
implementations walk `k` **in the same order** is a fold on both sides, and
equivalence is fold congruence — no reordering is argued, so the
commutativity question below never arises. What the pipeline still refuses:

- **k-recurrences** — `find_dz_for_eta`'s hydrostatic pressure accumulation,
  `p(i,j,K+1) = p(i,j,K) + GV%g_Earth*GV%H_to_RZ*h(i,j,k)`: iteration `k+1`
  reads what iteration `k` wrote. The boundary is marked with a committed
  refusal fixture
  ([case study](case-studies/edge-thickness-upwind.md#the-boundary-marked-with-a-refusal-fixture)).
  In the column model this is a per-k write that depends on the fold state —
  a **scan** — and `zonal_flux_adjust`'s Newton iteration is the same shape.
- **unordered reductions** — a scalar accumulator whose two implementations
  sum in *different* orders; over ℝ the order is provably irrelevant, but the
  lemma has to be stated and proved once. No banked kernel needs it yet.

What a future step would need:

- a **model shape** that keeps the sequential structure instead of erasing
  it — for a k-recurrence, a fold over the k-enumeration *is* the honest
  model on both sides, and the equivalence theorem becomes an **induction**
  over that enumeration rather than an instantiation of a ∀-schema;
- a matching **extraction rule** — pointize over the parallel indices (i, j)
  only, leaving the recurrence dimension as an explicit fold; a new gate must
  check which subscripts carry offsets and in which dimension;
- for reductions, additionally a decision about **operation order**: over ℝ
  the fold order is provably irrelevant (associativity/commutativity), which
  is exactly the reals-first division of labor — but the schema lemma for
  "any duplicate-free enumeration gives the same sum" still has to be proved
  once;
- the sequential-vs-unordered question these shapes pose is real mathematics,
  and it was deliberately **reserved** rather than hand-waved when plain DO
  was admitted.

## Neighbor reads: read-only stencils — landed in `do concurrent`, open in plain DO

A stencil like `b(i) = a(i-1) + a(i+1)` on an array **never written in the
loop** is admitted since 2026-09-05 in `do concurrent` nests
([rule C](concepts/pointize.md#read-only-stencils-rule-c)): each offset
pattern becomes a synthesized input (`a(i-1)` → `a_im1`), writes still land
in the iteration's own cell, and the source's independence assertion is the
license. What remains open:

- **plain DO** — refused until the schema-lemma variant for read-only
  environments is proved. The existing lemma threads read-only arrays through
  the point function's closure rather than the mutable state, so it appears
  to cover the case already; admitting it is a semantics decision for when a
  kernel needs it;
- **the C++ side** — the ports so far do the stencil at the call site and
  pass scalars into the point function, so nothing was needed. A port that
  reads `a(i-1,j,k)` off an `Array4` *inside* a point function would need the
  clang frontend's mirror admission (part of the C++ loop-extraction item
  below).

Distinct from a k-recurrence, where the offset read is of the array being
*written* — that one genuinely sequentializes and lives in the section above;
it refuses in either loop form.

## Integer values in kernel bodies

Integers as **addresses** (loop indices, bounds, subscripts) are fully
supported — pointize consumes and drops them. Integer **values** in the
modeled arithmetic refuse instead
([the printer's gate](reference/refusals.md)): Fortran evaluates `2/3` in
truncating integer arithmetic (it is 0), an ℝ model would say ⅔, and a
plausible-but-wrong model is the one failure mode the pipeline must never
have. The C++ frontend refuses the same shapes at its cast allowlist
(`IntegralToFloating`).

Faithful integer semantics is possible — Lean's `Int.div` truncates toward
zero, matching both languages — but it is a real modeling project, not one
gate: mixed ℤ/ℝ defs with coercions (breaking the uniform `rfl`/`ring` proof
story), the exact *placement* of int→real conversion points (the with-sema
tree marks them; each placement changes the value), the `MOD`/`MODULO`/`%`
family (truncating vs flooring), and C++ signed overflow, which is undefined
behavior and has no faithful total function at all. It enters by the
[subset-extension workflow](howto/extend-subset.md) when a real kernel
demands it — fixture first, refusal edges pinned — not before.

## Masks and per-cell guards

Many kernels in the case-study code base guard their arithmetic per cell
(`if (G%mask2dT(i,j) > 0.) …`) or branch on wet/dry state. In **column
kernels** masks are in since 2026-09-05 (B2): a `do concurrent` mask, or a
per-column `if` on a logical array, is a per-column `Bool` input and the body
runs under it ([Column kernels](concepts/column-kernels.md)); the C++'s
`do_I(i,j,0) != 0` is the same Bool. What remains open is the **point
tier**: a masked point kernel is still point-local, so the iteration schemas
should extend — but the skipped iterations leave their cells unwritten, which
the pointwise model (a total function per cell) cannot say without reading
the cell's old value, and a masked `do concurrent` **refuses** there
(pinned). Scalar logical *arguments* as guards (`if (vol_CFL)`) are in for
every tier as `Bool` inputs.

## More C++ surface

The clang frontend admits exactly what the existing kernels need. Real
future kernels will bring at least: `pow` calls (today only `abs` passes the
callee gate), ternary conditional expressions (`?:` — the natural C++
spelling of what functionalize's `Cond` already models), and `amrex::min`/
`amrex::max` (the printer is already able to spell `min`/`max`). Each enters
by the [subset-extension workflow](howto/extend-subset.md) when a kernel
demands it — fixture first, refusal edges pinned.

One larger item in the same category: **C++ loop extraction**. Today the
clang frontend accepts only per-point functions, so a Fortran loop can only
be compared against a C++ point function (under the explicit
`pointize = true` license). Extracting a C++ `for` nest and pointizing it
the same way would allow loop-vs-loop comparisons — a natural next step,
not started.

## Floating point: a readiness ledger

Equivalence is over ℝ by design (next section), and this page does not
propose changing that. But if a floating-point model is ever wanted, the
question worth answering *now* is whether the places where ℝ enters would be
hard to find later. They would not, because the design concentrates them —
and this ledger names them, to be maintained as kernels are banked rather than
reconstructed afterwards.

**What is already float-ready.** The generated defs mirror the source's own
operation order — parentheses kept, nothing reassociated or simplified,
inlined locals textual copies of deterministic expressions. That is exactly
the structure a floating-point model needs; a float carrier would reuse the
same generated defs behind a different binder type.

**Where ℝ enters:**

- *The printer's tables* (`lean_printer.py`): the carrier type (`_LEAN_TYPE`),
  the operator spellings (`_BIN`, `_CMP`), the literal normalization
  (`_real_lit` — spelling only: `1e-6` and `1.0e-6` become one numeral, the
  value is untouched), the intrinsic spellings (`abs`, `min`, `max`).
  Swapping the carrier touches these and nothing in the frontends or passes.
  A float model would additionally *want* what the C++ frontend now does for
  every literal: print the source spelling, never clang's re-printed
  long-double value.
- *Every non-`rfl` proof step.* A `rfl` point lemma says the two sides are the
  same expression, hence the same float computation modulo the compiler.
  Every other tactic marks an algebraic identity the ℝ proof leaned on — a
  float question to re-examine. The inventory today (grep the proof files):
    - `PpmLimitPos.lean`: `c*c + 3*(d*d) = c^2 + 3*d^2` by `ring` — the
      `**2` versus `x*x` spelling. IEEE-exact provided the compiler lowers a
      constant integer power 2 to a multiply (flang does).
    - `PpmLimitCw84.lean`, `FidelityCpp.lean`: `split_ifs <;> rfl` —
      control-flow *representation* only (merged `Cond`s versus sequential
      `let`s); no arithmetic identity, float-exact.
    - `FluxElem.lean`: `neg_mul` — `(-u) * dt = -(u * dt)`. IEEE-exact:
      negation is exact and rounding is sign-symmetric.
    - `ThicknessToDz.lean`: `foldSeq_eq_pointwiseMap` — an iteration-order
      lemma, arithmetic-agnostic (each cell is computed once from loop-entry
      data), float-exact.
    - `BtMassFlux.lean`: `simp only` with the two defs and
      `fluxElem_point_equiv` — unfolding, zeta-reduction and rewriting the
      callee under the fold's binder; no arithmetic identity at all. The
      folds coincide term for term because both sides sum the layers in the
      same order, so this is float-exact as well (a `+` in the same order
      rounds the same way).
    - `SetZonalBtCont.lean`: `neg_mul` again, and `neg_div` — `(-(x)) / v =
      -((x) / v)`, the same precedence difference under a division;
      IEEE-exact for the same reason. `apply_ite` (the output permutation
      pushed through the tail's `if`) and the `cases` on the mask are
      representation only.
- *Lean's ℝ conventions.* `x / 0 = 0` in Lean; IEEE gives ±∞ or NaN. Every
  `/` in a generated def is a site a float model must speak about. Today:
  `ppm_limit_pos`'s `scale` (guarded — `curv > 0` makes the denominator
  positive) and `ratio_max`'s `a / b` (reachable with `b = 0` when `a = 0`,
  where the source yields NaN and the ℝ model yields 0 — the theorem still
  holds because both sides compute the same expression, but a float
  *specification* of `ratio_max` would have to say so).
- *Comparisons and guards.* Over ℝ every comparison is total; in float, NaN
  makes them all false. The `Cmp` table is the one place that changes; the
  `min`/`max` intrinsics carry their own NaN and tie conventions, which
  differ between Fortran and `amrex::max`.

**What the parse trees do not pin, and a float model would have to:**

- *Real kinds* are read and dropped when a parameter becomes `real`
  (`flang_kernel._parse_type_decl`; `clang_kernel._extract_param`, where
  `Real` and `double` both map to `real`). One line on each side to keep
  them.
- *Compiler flags* are outside both trees entirely: FMA contraction,
  reassociation, fast-math. A float model would state the assumed
  compilation mode explicitly.

None of the extensions on this page hides a float assumption: stencils,
subset indexing, the generalized join and Bool guards are about *which values
flow where*, and that structure is the same in either arithmetic.

## Scope boundaries that are permanent, not roadmap

Worth restating, so the roadmap above isn't misread as "everything,
eventually":

- equivalence stays **over ℝ** — floating-point identity is the regression
  and ensemble machinery's job, by design
  ([what the theorems mean](index.md#what-the-theorems-mean-and-deliberately-do-not));
- the theorems cover **kernels**, not the surrounding driver code, MPI
  choreography, or I/O;
- the translator will keep **refusing** rather than approximating; the
  subset grows construct by construct with fixtures, or not at all.

## The other half of the vision

The kernel track certifies each port; the **relational track** is meant to decide
*which* kernels are provable in isolation and to gate the porting frontier in
CI — the two compose into one gate: every ported kernel carries a checked
theorem *and* no forbidden structural edge appears. The relational track's
query/CI layer is not built yet; see [The relational track](relational.md)
for what exists today.
