# Address a loop inside a subroutine

Not every kernel is a tidy standalone subroutine. In real code, kernels often
live *inline* — a loop nest under an `if` inside a larger routine, sometimes
one variant per configuration branch. groundline addresses these by **source
order ordinal**.

## The addressing rule

```toml
[[kernel]]
name = "edge_thickness_upwind"       # the generated def's name — YOU supply it
fortran = { dump = "MOM6/MOM_continuity_PPM.o_ptree",
            subroutine = "zonal_edge_thickness",
            nest = 1 }
cpp = { source = "mom_continuity_ppm_kernel.hpp",
        function = "edge_thickness_upwind_point" }
pointize = true                      # an addressed nest is a loop — the license
```

`nest = N` selects the **N-th outermost do-construct of the subroutine, in
source order** (1-based). The dump carries no line numbers, so the ordinal is
the deterministic address. The counting walk:

- counts both `do concurrent` and plain-`do` nests;
- **descends into `if` branches** — a loop under `if (CS%upwind_1st)` is
  counted where it appears;
- **never descends into a do-construct** — inner loops of a nest are part of
  it, not separately addressable.

An out-of-range ordinal refuses with the actual count, and requesting
whole-subroutine extraction on a routine that is more than one nest also
refuses — both are pinned by fixtures (`tests/f90/test_kernel_inline_nests`).

Because an inline loop has no name of its own, the entry's `name` becomes the
generated def's name, and the manifest row *is* the durable record of the
pairing. Choose the name to match the C++ point function it pairs with.

## Declarations are inherited tolerantly

The enclosing subroutine's specification part supplies the declarations, and
big production routines declare far more than any one loop uses — `character`
message buffers, `pointer` dummies, `logical` locals, all outside the kernel
subset (an `optional` dummy the nest reads is fine: presence is the caller's
precondition, and the guard that tests it sits outside the nest). A
declaration outside the subset **poisons only its own names**: extraction
refuses if and only if the addressed nest actually *references* a poisoned
name (the refusal names both the variable and why its declaration was
rejected). The loop you want is not held hostage by the routine around it.

## Worked example

In the production case study, `thickness_to_dz_3d` carries four sibling nests — a
do-concurrent and a plain-DO variant of each of its two physics branches,
under a `do_offload` guard. In source order: nest 1 = do-concurrent
non-Boussinesq, 2 = plain-DO non-Boussinesq, 3 = do-concurrent Boussinesq,
4 = plain-DO Boussinesq. The banked entries pick nests 2 and 4 (the plain-DO
defaults):

```toml
[[kernel]]
name = "thickness_to_dz_3d_boussinesq"
fortran = { dump = "MOM6/MOM_interface_heights.o_ptree",
            subroutine = "thickness_to_dz_3d", nest = 4 }
cpp = { source = "mom_interface_heights_kernel.hpp",
        function = "thickness_to_dz_3d_boussinesq_point" }
pointize = true
```

`groundline kernel list` displays the ordinal, and the generated def's doc
comment records it (`Generated from loop nest 4 of thickness_to_dz_3d …`), so
the address stays auditable end to end.

!!! note "Ordinals can move"

    The ordinal is stable against everything except *source edits that add,
    remove, or reorder loop nests in that subroutine*. If an upstream change
    touches the routine, `groundline kernel verify` catches it: the
    regenerated def either differs (byte-diff fails) or the extraction
    refuses. Re-derive the ordinal by reading the source, update the row, and
    re-audit the def — the same one-time audit as banking.

The full story of the first inline-addressed kernel — and the refusal fixture
that marks where this technique stops — is in the
[edge_thickness_upwind case study](../case-studies/edge-thickness-upwind.md).
