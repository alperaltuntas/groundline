# Kernels that live inside branches: edge_thickness_upwind

*Kernel pair: Fortran `zonal_edge_thickness`, loop nest 1
(`MOM6/src/core/MOM_continuity_PPM.F90`) ⇄ C++
`MOM::edge_thickness_upwind_point`
(`TIM/mom/cpp/mom_continuity_ppm_kernel.hpp`).*

The upwind edge-thickness kernel is, mathematically, the least interesting
thing in the bank — its body copies one value to two outputs:

```fortran
if (CS%upwind_1st) then
  do concurrent (k=1:nz, j=jsh:jeh, i=ish-1:ieh+1)
    h_W(i,j,k) = h_in(i,j,k) ; h_E(i,j,k) = h_in(i,j,k)
  enddo
```

It is in this manual because of *where it lives*: not a standalone subroutine
but a loop under a configuration branch inside `zonal_edge_thickness`. Most
real kernels look like this, and banking one forced the question the tidy
early kernels dodged: **how do you durably, deterministically name a loop that
has no name?**

## Addressing by ordinal

The flang dump carries no line numbers, so the address is the loop's
**source-order ordinal** among the subroutine's outermost do-constructs —
here, nest 1 (the routine's only nest). The counting walk descends into `if`
branches (that's where these kernels live) but never into a do-construct, so
inner loops of a nest are not separately addressable; out-of-range ordinals
refuse with the actual count. The manifest row supplies the generated def's
name and records the pairing:

```toml
[[kernel]]
name = "edge_thickness_upwind"
fortran = { dump = "MOM6/MOM_continuity_PPM.o_ptree",
            subroutine = "zonal_edge_thickness", nest = 1 }
cpp = { source = "mom_continuity_ppm_kernel.hpp",
        function = "edge_thickness_upwind_point" }
pointize = true
```

One more accommodation real routines need: the enclosing subroutine's
declarations are inherited *tolerantly*. `zonal_edge_thickness` declares
plenty the loop never touches — and declarations outside the kernel subset
(`character` buffers, `optional`/`pointer` attributes, `logical` locals)
poison only their own names; extraction refuses iff the addressed nest
actually references one. Details in
[the how-to](../howto/inline-loops.md).

The generated def is honest about how little the body does:

```lean
/-- Generated from loop nest 1 of `zonal_edge_thickness` in
`MOM6/MOM_continuity_PPM.o_ptree` (flang with-sema dump).
Outputs `(h_w, h_e)` — the `intent(out)` arguments, modeled functionally over ℝ. -/
def edge_thickness_upwind (h_in h_w h_e : ℝ) : ℝ × ℝ :=
  (h_in, h_in)
```

and the point lemma is `rfl` — both generated sides are `(h_in, h_in)`. The
value of the theorem is not the algebra; it is the *checked pairing*: this
specific branch of this specific routine is what the C++ port implements,
with nothing dropped on the way. (`meridional_edge_thickness` holds the
textually identical `h_S`/`h_N` loop; the function proved is the same. The
loop is `do concurrent`, so its license is the source's assertion — contrast
[the plain-DO kernels](thickness-to-dz.md). And this kernel's `intent(out)`
outputs caught a small printer dishonesty: the generated doc line used to
hardcode "the `intent(inout)` arguments"; it now derives from the actual
intents, byte-identical for everything previously banked.)

## The boundary, marked with a refusal fixture

The same subroutine family contains the method's current *frontier*, and
banking this batch marked it deliberately. `find_dz_for_eta` accumulates
hydrostatic pressure downward:

```fortran
p(i,j,K+1) = p(i,j,K) + GV%g_Earth*GV%H_to_RZ*h(i,j,k)
```

Iteration `k+1` reads what iteration `k` wrote — a genuine k-recurrence, not
point-local, and **no license exists**: neither a `do concurrent` assertion
nor the [schema lemma](../concepts/pointize.md) applies. Rather than leave
that boundary implicit, it is pinned as a refusal fixture
(`tests/f90/test_kernel_recurrence`), distilled to the shape above — with the
capital-`K` spelling kept deliberately: the dump lowercases names, `K` and
`k` are the same index, so the test proves the refusal fires on the `+1`
*offset*, not on a spurious case mismatch. (Since read-only stencils were
admitted, the gate that fires is the *write* to the neighbor cell `K+1` —
reads at an offset are fine when the array is never written in the nest;
here it is.) The real refusal, from the real pipeline:

```console
$ groundline kernel show accumulate --kernels /tmp/demo/kernels.toml
--8<-- "refusal_recurrence.txt"
```

That message is the method being upfront about its own limits: the pipeline states
precisely what it will not model, and [Limits & roadmap](../limits.md) states
what a future step needs (induction over the enumeration, not a ∀-schema)
before kernels like `find_dz_for_eta` can be banked.

## The theorems and their audits

From the current build log:

```text
'Groundline.GeneratedFtn.edge_thickness_upwind' depends on axioms: [propext, Classical.choice, Quot.sound]
'Groundline.GeneratedCpp.edge_thickness_upwind_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'Groundline.edgeThicknessUpwind_point_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Groundline.edgeThicknessUpwind_kernel_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Proof file: `lean/groundline/Groundline/EdgeThicknessUpwind.lean`. With this kernel and
[the two thickness conversions](thickness-to-dz.md), the bank covered five of
five — the entire TIM point-kernel population at the time of writing.
