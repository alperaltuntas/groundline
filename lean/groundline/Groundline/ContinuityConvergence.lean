import Groundline.GeneratedFtn
import Groundline.GeneratedCpp

set_option linter.style.header false

/-!
# The convergence update: four Fortran nests, one C++ primitive

Kernel pairs (TIM PR 36, the continuity mass-flux port):
  Fortran:  `continuity_zonal_convergence`, loop nests 1 and 2, and
            `continuity_merdional_convergence` (the source's spelling), loop
            nests 1 and 2 — MOM6/src/core/MOM_continuity_PPM.F90. Each nest is
            `do concurrent (k, j, i)` around
            `h(i,j,k) = max(h_prev - dt*G%IareaT(i,j)*(flux(i,j,k) - flux(i-1,j,k)), h_min)`
            with `h_prev` = `hin(i,j,k)` (nest 1) or `h(i,j,k)` itself (nest 2,
            the in-place branch the source marks "untested"), and the flux read
            at the west (`uh(I-1,j,k)`) or south (`vh(i,J-1,k)`) neighbor.
  C++:      `MOM::continuity_convergence_point`
            TIM/mom/cpp/mom_continuity_ppm_kernel.hpp — one primitive; its four
            call sites in `mom_continuity_ppm.cpp` do the stencil and pass
            scalars, e.g.
            `h(i,j,k) = continuity_convergence_point(hin(i,j,k), uh(i,j,k),
                                                    uh(i-1,j,k), dt, IareaT(i,j,0), h_min)`.

Three extraction rules meet here for the first time (DEVLOG 2026-09-05): the
neighbor read `uh(I-1,j,k)` of an array the nest never writes becomes the
synthesized input `uh_im1` (rule C, read-only stencils, `do concurrent`
only); `G%IareaT(i,j)`, indexed by two of the three loop indices, becomes the
per-cell input `iareat` (rule B, subset form); and `h_min`, set before the
loop and only read inside it, becomes the input `h_min` (rule D). On the C++
side the return value is the output and `amrex::max` is the callee.

The four point lemmas are `rfl`: modulo argument order the generated bodies
are the same expression. The argument correspondence in each theorem is read
off the C++ call site quoted above — `uh (west i)` in the `flux_in` slot is
the one link that is by eye — and a wrong pairing would fail to prove, since
`uh - uh_im1` is not `uh_im1 - uh`. The kernel-level theorems make the
stencil explicit as a neighbor map on the index type (`west`, `south`), so
"the C++ launch equals the Fortran nest" is stated for any grid shape.
-/

namespace Groundline

noncomputable section

/-! ## Point lemmas — one C++ primitive against each Fortran nest -/

/-- Zonal, `present(hin)` branch. -/
theorem convergenceZonal_point_equiv (h uh dt hin iareat uh_im1 h_min : ℝ) :
    GeneratedCpp.continuity_convergence_point hin uh uh_im1 dt iareat h_min
      = GeneratedFtn.continuity_convergence_zonal h uh dt hin iareat uh_im1 h_min := rfl

/-- Zonal, in-place branch (`h` is both the previous thickness and the output). -/
theorem convergenceZonalInplace_point_equiv (h uh dt iareat uh_im1 h_min : ℝ) :
    GeneratedCpp.continuity_convergence_point h uh uh_im1 dt iareat h_min
      = GeneratedFtn.continuity_convergence_zonal_inplace h uh dt iareat uh_im1 h_min := rfl

/-- Meridional, `present(hin)` branch. -/
theorem convergenceMeridional_point_equiv (h vh dt hin iareat vh_jm1 h_min : ℝ) :
    GeneratedCpp.continuity_convergence_point hin vh vh_jm1 dt iareat h_min
      = GeneratedFtn.continuity_convergence_meridional h vh dt hin iareat vh_jm1 h_min := rfl

/-- Meridional, in-place branch. -/
theorem convergenceMeridionalInplace_point_equiv (h vh dt iareat vh_jm1 h_min : ℝ) :
    GeneratedCpp.continuity_convergence_point h vh vh_jm1 dt iareat h_min
      = GeneratedFtn.continuity_convergence_meridional_inplace h vh dt iareat vh_jm1 h_min := rfl

/-! ## Kernel level — the stencil as a neighbor map

`do concurrent` asserts the iterations are independent (the license), and the
flux array is never written in the nest, so each cell's update reads
loop-entry data at its own index and at its neighbor's. `west` / `south` are
the neighbor maps on the abstract index type; the C++ call site's
`uh(i-1,j,k)` is `uh (west i)`. -/

theorem convergenceZonal_kernel_equiv {ι : Type*} (west : ι → ι)
    (h uh hin iareat : ι → ℝ) (dt h_min : ℝ) :
    (fun i => GeneratedCpp.continuity_convergence_point (hin i) (uh i) (uh (west i))
        dt (iareat i) h_min)
      = fun i => GeneratedFtn.continuity_convergence_zonal (h i) (uh i) dt (hin i)
        (iareat i) (uh (west i)) h_min :=
  funext fun i => convergenceZonal_point_equiv (h i) (uh i) dt (hin i) (iareat i)
    (uh (west i)) h_min

theorem convergenceZonalInplace_kernel_equiv {ι : Type*} (west : ι → ι)
    (h uh iareat : ι → ℝ) (dt h_min : ℝ) :
    (fun i => GeneratedCpp.continuity_convergence_point (h i) (uh i) (uh (west i))
        dt (iareat i) h_min)
      = fun i => GeneratedFtn.continuity_convergence_zonal_inplace (h i) (uh i) dt
        (iareat i) (uh (west i)) h_min :=
  funext fun i => convergenceZonalInplace_point_equiv (h i) (uh i) dt (iareat i)
    (uh (west i)) h_min

theorem convergenceMeridional_kernel_equiv {ι : Type*} (south : ι → ι)
    (h vh hin iareat : ι → ℝ) (dt h_min : ℝ) :
    (fun i => GeneratedCpp.continuity_convergence_point (hin i) (vh i) (vh (south i))
        dt (iareat i) h_min)
      = fun i => GeneratedFtn.continuity_convergence_meridional (h i) (vh i) dt (hin i)
        (iareat i) (vh (south i)) h_min :=
  funext fun i => convergenceMeridional_point_equiv (h i) (vh i) dt (hin i) (iareat i)
    (vh (south i)) h_min

theorem convergenceMeridionalInplace_kernel_equiv {ι : Type*} (south : ι → ι)
    (h vh iareat : ι → ℝ) (dt h_min : ℝ) :
    (fun i => GeneratedCpp.continuity_convergence_point (h i) (vh i) (vh (south i))
        dt (iareat i) h_min)
      = fun i => GeneratedFtn.continuity_convergence_meridional_inplace (h i) (vh i) dt
        (iareat i) (vh (south i)) h_min :=
  funext fun i => convergenceMeridionalInplace_point_equiv (h i) (vh i) dt (iareat i)
    (vh (south i)) h_min

end

end Groundline
