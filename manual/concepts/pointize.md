# Pointize: from loop nest to point function

`kir.pointize` performs the pipeline's central semantic move: it strips a
kernel's single loop-nest wrapper and turns every array reference indexed
*exactly* by the loop indices into a scalar. `b(i) = b(i) + w` becomes
`b = b + w`; the loop indices, bound variables, and any parameter the
pointized body no longer references (grid structs, index ranges) are
dropped. What remains is a pure per-point function — the same shape as a
C++/AMReX device kernel, which is what makes the two sides comparable at
all.

It never runs silently. A loop and a point function are different things,
so a loop-nest kernel refuses at extraction unless its manifest entry
carries `pointize = true` — the user's explicit license for the reduction.
(A Fortran kernel that is already per-point needs no license and skips this
pass entirely.)

The interesting question is not the mechanics but the **license**: a loop nest
and a pointwise map are only the same thing if the iterations do not interact.
Who says they don't? Pointize admits two nest forms, with two *different*
answers.

## `do concurrent` — licensed by the source's assertion

Fortran's `do concurrent` *asserts* iteration independence — the programmer
declares that the iterations may execute in any order. groundline takes the
source at its word: that assertion is the license for the pointwise model,
exactly as it is the license for the compiler to parallelize. The extraction
gate still checks what it can (every array reference indexed exactly by the
loop indices — offsets, masks, and partial indexing refuse), but the semantic
authority is the source.

## Plain `do` — licensed by a proved schema lemma

A plain `do` nest asserts nothing. Its honest semantics is a **sequential
fold**: iterate the body over the index box in order, each iteration seeing
the state the previous one left. Modeling it as a pointwise map would be an
assertion the source never made — so groundline doesn't assert it; it **proves**
it, once and for all, as a schema lemma in `lean/groundline/Groundline/SeqSchema.lean`:

```lean
theorem foldSeq_eq_pointwiseMap (f : ι → σ → σ) (enum : List ι)
    (hnd : enum.Nodup) (hall : ∀ i, i ∈ enum) (s₀ : ι → σ) :
    foldSeq f s₀ enum = pointwiseMap f s₀
```

For any point function `f` and any duplicate-free, complete enumeration of the
index box, the sequential fold of per-point updates equals the pointwise map.
The proof is an induction over the enumeration with a frame argument
(`foldSeq_frame`: cells not in the enumeration are never written; under
no-duplicates, each iteration finds its own cell pristine, writes land in
disjoint cells, and the fold telescopes to the map).

The division of labor between Python and Lean here is worth stating precisely,
because it is easy to get backwards:

- **The extraction gate does not justify the reordering.** The Python-side
  checks — perfect nesting (each loop level's body is exactly one inner loop
  until the innermost), every array reference at exactly the loop indices,
  and, on the plain-DO path only, every *write* landing in the iteration's own
  array cell — are what guarantee the lemma's *setting applies*. An assignment
  to a scalar parameter (`s = s + a(i)` — an accumulator/reduction) refuses;
  so do imperfect nests, strides, and duplicate indices.
- **The lemma is the semantic justification.** Once pointize has produced
  `f`, point-locality is baked into `f`'s *type* — `f : ι → σ → σ` sees only
  its own cell's state and cannot reference a neighbor — so the lemma's
  hypothesis is structural rather than re-checked per kernel.

## A symmetry worth noticing

For `do concurrent`, the license is an **assertion** (the source's own).
For plain `do`, it is a **proof**. Plain DO ends up on equal — arguably
*better* — footing than the construct designed for parallelism; see the
[thickness_to_dz case study](../case-studies/thickness-to-dz.md) for how that
played out on real kernels.

Reductions and cross-iteration recurrences fit neither license: they are not
point-local, and their sequential-vs-unordered question is real mathematics
reserved for a future step ([Limits & roadmap](../limits.md)). They refuse.

## Component reads (rule B)

Real kernels read configuration through derived types (`GV%H_to_Z`). Pointize
admits exactly two shapes, both becoming **synthesized scalar `in`
parameters** of the point function:

- a **loop-invariant scalar component** — `GV%H_to_Z` → parameter `h_to_z`.
  Loop-invariance is guaranteed, not assumed: the base must be an
  `intent(in)` derived-type dummy argument, which Fortran forbids modifying,
  and component *writes* refuse;
- a **component array indexed by loop indices** — all of them
  (`tv%SpV_avg(i,j,k)` → parameter `spv_avg`, fed per cell) or, since
  2026-09-05, a *subset* of them (`G%IareaT(i,j)` in a `k, j, i` nest →
  `iareat`): along the omitted indices the value is the same for every
  iteration, and it is read-only for the same reason the scalar is.

Naming is deterministic — the component's own name — and collision-checked:
if it collides with a parameter, local, loop index, or another synthesized
name, extraction **refuses rather than renames** (a silent rename would break
the by-eye audit of generated Lean against source). Synthesized parameters are
modeled as real scalars; the one-time audit of each generated def against its
source covers the component's actual type. Everything else — offset
subscripts, non-`intent(in)` bases, chained `a%b%c` — refuses.

## Read-only stencils (rule C)

A stencil reads a neighbor: `uh(I-1,j,k)` next to `uh(I,j,k)`. Whether that
breaks point-locality depends on one thing — whether the nest ever *writes*
`uh`. If it does, iteration `I` reads what iteration `I-1` wrote: a
recurrence, refused in either loop form (the write set of the nest is
computed first). If it does not, the value read is loop-entry data, exactly
like the cell's own inputs, and the iteration still depends only on loop-entry
data. Pointize then admits the read and synthesizes an input per offset
pattern, named after the array and the offsets index by index:
`uh(I-1,j,k)` → `uh_im1`, `a(i+1,j-1,k)` → `a_ip1_jm1`. The offset is
absorbed into *which input* — it never becomes integer arithmetic inside the
ℝ model. Only `index ± literal` subscripts are admitted; writes must still
land in the iteration's own cell.

The license, granted 2026-09-05, is deliberately narrow: stencils are
admitted in **`do concurrent` nests only**. The source's independence
assertion covers them there. A plain DO with a stencil refuses until the
schema-lemma variant for it is proved — though the existing lemma's form,
which threads read-only arrays through the point function's closure rather
than through the mutable state, appears to cover the read-only case already.
That is a decision for when a kernel needs it.

## Nest-invariant locals (rule D)

A scalar local the nest reads but never assigns — `h_min`, set before the
loop from an optional argument — is loop-entry data too: an input of the
point function, synthesized under its own name and declared type. A local
the nest *does* assign stays a per-iteration `let`, as before. How the caller
set the value is outside the kernel, like any scalar argument.

## One gap, closed by the checker

The plain-DO write gate does not itself refuse one cross-iteration channel: a
local scalar *read before its first write* would, in a sequential loop, carry
the previous iteration's value. This cannot produce a wrong model —
[functionalize](functionalize.md) binds locals per iteration, and since
2026-09-05 it tracks which locals are in scope and **refuses** such a read
itself (`read before it is assigned`). Before that, the read printed as an
unbound name and the generated Lean failed to elaborate — the same loud
outcome, delivered by the checker instead of Python. Either way: never a
wrong model.
