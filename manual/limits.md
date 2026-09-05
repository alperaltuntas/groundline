# Limits & roadmap

The rest of this manual documents what runs today; this page is the
inventory of what does not — and what each missing piece would take.
Everything below is **roadmap**: none of it is implemented, and none of it
should be cited as a capability.

## The frontier: reductions and k-recurrences

The current method rests on **point-locality**: every banked kernel computes
each output cell from that cell's inputs alone, so both iteration licenses —
`do concurrent`'s assertion and the plain-DO
[schema lemma](concepts/pointize.md) — reduce a loop to a pointwise map. The
kernels just past that boundary are the ones the pipeline refuses today:

- **k-recurrences** — `find_dz_for_eta`'s hydrostatic pressure accumulation,
  `p(i,j,K+1) = p(i,j,K) + GV%g_Earth*GV%H_to_RZ*h(i,j,k)`: iteration `k+1`
  reads what iteration `k` wrote. The boundary is marked with a committed
  refusal fixture
  ([case study](case-studies/edge-thickness-upwind.md#the-boundary-marked-with-a-refusal-fixture)).
- **reductions** — scalar accumulators (`s = s + a(i)`), refused by the
  plain-DO write gate as not point-local.

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

## Neighbor reads: read-only stencils

A stencil like `b(i) = a(i-1) + a(i+1)` refuses today at the array-index gate
(every reference must sit exactly at the loop indices). But when the offset
reads are of arrays **never written in the loop**, this is a much cheaper
extension than the recurrences above — the iterations still don't interact:

- **extraction** — admit subscripts of the form *loop index ± integer
  literal* on read-only arrays; each distinct offset pattern becomes a
  synthesized scalar input (`a(i-1)` → `a_m1`), the same move rule B already
  makes for component arrays. Writes must still land in the iteration's own
  cell. The offset is absorbed into *which input* — it never becomes integer
  arithmetic inside the ℝ model;
- **licenses** — `do concurrent`'s assertion carries over unchanged; the
  plain-DO schema lemma needs a variant that threads the read-only arrays as
  a fixed environment instead of mutable cell state — a strictly easier
  frame argument than the one already proved;
- **the C++ side** — the ports read `a(i-1,j,k)` off an `Array4` inside a
  point function, so the clang frontend needs the mirror admission, mapping
  the same literal-offset reads to the same synthesized inputs.

Distinct from a k-recurrence, where the offset read is of the array being
*written* — that one genuinely sequentializes and lives in the section above.

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
(`if (G%mask2dT(i,j) > 0.) …`) or branch on wet/dry state. A masked point kernel is still point-local,
so the iteration schemas should extend — but the mask array enters the model
as a per-cell input with its own rule-B-like story (a component array of the
grid type, read at exactly the loop indices), and the generated defs grow a
guard shape the printer and the by-eye audit must handle. Scalar logical
*arguments* as guards (`if (vol_CFL)`) are in since 2026-09-05, as `Bool`
inputs; per-cell mask *arrays* are the open part — refused today by the
array-index gate (the mask subscripts `(i,j)` don't match a 3-D nest's
indices).

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
