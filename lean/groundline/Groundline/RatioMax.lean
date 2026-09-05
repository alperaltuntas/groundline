import Groundline.GeneratedFtn
import Groundline.GeneratedCpp

set_option linter.style.header false

/-!
# The sixth kernel: ratio_max — a function-result kernel

Kernel pair (TIM PR 36, the continuity mass-flux port):
  Fortran:  `pure function ratio_max(a, b, maxrat) result(ratio)`
            MOM6/src/core/MOM_continuity_PPM.F90
  C++:      `MOM::ratio_max_point`   TIM/mom/cpp/mom_continuity_ppm_kernel.hpp

The first banked pair whose kernel is a *function* on both sides: the Fortran
result variable and the C++ return value are each the kernel's single output,
so the generated defs take only the inputs `(a b maxrat : ℝ)` — no
`intent(inout)` slot doubling as an input, and no loop of its own. The callers
(the CFL-limit passes of `zonal_mass_flux` / `meridional_mass_flux`) apply it
once per (I, j) column inside column kernels that are outside the point subset
for now; what the subset can certify is the primitive they share.

Per the mature pattern there is no hand-written model: the point lemma relates
the two generated defs directly, and it is `rfl` — the two sources spell the
same expressions (`abs(a) > abs(maxrat*b)` against `amrex::Math::abs(a) >
amrex::Math::abs(maxrat * b)`, then `maxrat` or `a / b`).
-/

namespace Groundline

noncomputable section

/-- **Point lemma:** the C++ port and the Fortran function compute the same
value over ℝ — the two generated bodies are definitionally equal. -/
theorem ratioMax_point_equiv (a b maxrat : ℝ) :
    GeneratedCpp.ratio_max_point a b maxrat = GeneratedFtn.ratio_max a b maxrat := rfl

/-- **Kernel level:** evaluated pointwise over any index set — as the
mass-flux callers do, one evaluation per column — the two sides agree as
arrays. This lift is all the point subset says about those callers today. -/
theorem ratioMax_kernel_equiv {ι : Type*} (a b maxrat : ι → ℝ) :
    (fun i => GeneratedCpp.ratio_max_point (a i) (b i) (maxrat i))
      = fun i => GeneratedFtn.ratio_max (a i) (b i) (maxrat i) :=
  funext fun i => ratioMax_point_equiv (a i) (b i) (maxrat i)

end

end Groundline
