# Bank a new kernel pair

"Banking" a pair means: both sides extracted and generated into the committed
Lean modules, an equivalence theorem proved between the two generated defs,
and the axioms audit extended. This guide assumes the kernel is **inside the
supported subset**; if extraction refuses, see
[Extend the construct subset](extend-subset.md) first — and read the refusal
message, it names the construct.

## 0. Check the shape

The Fortran side must be either a per-point subroutine (scalar arguments,
no loop) or a single mask-free loop nest (`do concurrent`, or a perfectly
nested plain `do`) of assignments and structured ifs over `+ - * / **`,
comparisons, and `abs`, with every array reference indexed exactly by the
loop indices. The C++ side must be a per-point function in the supported
shape: `void`, reference outputs, const-value inputs, real scalars
throughout (`Real` or `double`). When in doubt, just try
`groundline kernel show` — refusal is loud and names the problem.

## 1. Add the manifest entry

Add a `[[kernel]]` table to your manifest (see
[the schema](../reference/manifest.md)); for the production instance that is
`examples/turbo-stack.kernels.toml`:

```toml
[[kernel]]
name = "my_kernel"
fortran  = { dump = "MOM6/MOM_something.o_ptree", subroutine = "my_kernel" }
cpp      = { source = "mom_something_kernel.hpp", function = "my_kernel_point" }
pointize = true   # only if the Fortran side is a loop nest
```

A whole-subroutine kernel must be named after its subroutine (the manifest
loader enforces this); a loop *inside* a subroutine is addressed by nest
ordinal instead — see [Address a loop inside a subroutine](inline-loops.md).
If the Fortran side is a loop nest, `pointize = true` is required — it is
the explicit license to reduce the loop to its per-point body
([why](../concepts/pointize.md)); without it, extraction refuses and the
message points here.

Check the addressing resolves:

```console
$ groundline kernel list
$ groundline kernel show my_kernel
```

`show` prints both generated defs without touching any files — this is the
moment for the **one-time by-eye audit**: hold each def against its source
and check the expression shapes mirror it (the
[fidelity contract](../concepts/printer-fidelity.md) is what makes this
feasible).

## 2. Generate and diff

```console
$ groundline kernel generate
$ git diff lean/groundline/Groundline/GeneratedFtn.lean lean/groundline/Groundline/GeneratedCpp.lean
```

The diff must be **purely additive** — your new defs appended, existing defs
byte-identical. If an existing def changed, stop: something in your change
touched shared machinery, and that needs understanding before proving
anything.

## 3. Write the equivalence theorem

Create `lean/groundline/Groundline/MyKernel.lean` following the mature pattern (no
hand-written models — relate the two *generated* defs directly; use
`Groundline/ThicknessToDz.lean` and `Groundline/EdgeThicknessUpwind.lean` as templates):

- **Point lemma** — the two generated defs agree, modulo parameter order.
  When the bodies come out identical this is literally `:= rfl`; when shapes
  differ, `unfold`/`simp only` plus `ring`-provable bridge identities, or
  `split_ifs <;> rfl` for control-flow representation deltas, have covered
  every banked kernel so far. If the proof needs anything beyond `rfl` and
  a control-flow split, add the identity it uses to the
  [float-readiness ledger](../limits.md#floating-point-a-readiness-ledger) —
  each such step is a place a floating-point model would have to re-examine.
- **Kernel-level theorem** — lift to whole arrays with the license matching
  the loop form: a `do concurrent` kernel reuses the `pointwise` schema (the
  source's independence assertion is the license); a plain-DO kernel models
  the Fortran side honestly as `foldSeq` and instantiates
  `foldSeq_eq_pointwiseMap` (a proof is the license). See
  [Pointize](../concepts/pointize.md).

Add the file to `lean/groundline/Groundline.lean`'s imports if you created a new module.

## 4. Extend the axioms audit

Append `#print axioms` lines to `lean/groundline/Groundline/AxiomsAudit.lean` for
*every* new declaration — the generated defs, the point lemma, the kernel
theorem:

```lean
#print axioms Groundline.GeneratedFtn.my_kernel
#print axioms Groundline.GeneratedCpp.my_kernel_point
#print axioms Groundline.myKernel_point_equiv
#print axioms Groundline.myKernel_kernel_equiv
```

Every line must report exactly `[propext, Classical.choice, Quot.sound]` (or
a strict subset); see [the audit convention](../concepts/trusted-base.md).

## 5. Run the gate

```console
$ groundline kernel verify
ok [fortran]: GeneratedFtn.lean matches a fresh regeneration
ok [cpp]: GeneratedCpp.lean matches a fresh regeneration
running `lake build` in .../lean/groundline ...
ok [lean]: lake build succeeded
```

(Lean stage: activate a real Lean toolchain first — a bare elan shim fails the
gate loudly.) Also run the pytest suite; the golden tests import the
manifest, so they pick up the new kernel automatically.

## 6. Commit

Commit the manifest row, the regenerated `Generated*.lean`, the new proof
file, and the audit lines together — that is one reviewable unit: "this pair
is now banked, here is the proof, here is its audit."
