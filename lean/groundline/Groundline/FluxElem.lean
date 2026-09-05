import Groundline.GeneratedFtn
import Groundline.GeneratedCpp

set_option linter.style.header false

/-!
# The seventh kernel: flux_elem — the PPM face flux

Kernel pair (TIM PR 36, the continuity mass-flux port):
  Fortran:  `elemental subroutine flux_elem(u, h, h_p1, h_L, h_L_p1, h_R, h_R_p1,
              uh, duhdu, visc_rem, G_dy_Cu, G_IareaT, G_IareaT_p1, G_IdxT,
              G_IdxT_p1, dt, G, GV, US, vol_CFL, por_face_area)`
            MOM6/src/core/MOM_continuity_PPM.F90
  C++:      `MOM::flux_elem_point`   TIM/mom/cpp/mom_continuity_ppm_kernel.hpp

This is where the physics of the mass-flux family lives: the PPM-reconstructed
transport `uh` through one face and its velocity derivative `duhdu`, for one
candidate face velocity. Every column kernel of the port (`*_mass_flux`,
`*_BT_mass_flux`, `set_*_BT_cont`, `*_flux_adjust`) calls it once per layer.

Three things make it the first of its shape in the bank: a **logical
argument** (`vol_CFL`, a `Bool` binder in both generated defs) used as a bare
guard; the **generalized control-flow join** — the if/elseif/else assigns the
locals `CFL`, `curv_3`, `dh`, `h_marg` and the output `uh`, and
`duhdu = tmp * h_marg * visc_rem` follows — which functionalize renders as one
merged `let h_marg := …` (the locals `CFL`/`curv_3`/`dh` are inlined, being
dead after the join); and, on the C++ side, **locals declared without an
initializer** (`Real CFL, curv_3, h_marg, dh;`) assigned inside the branches.
The unreferenced grid structs `G`, `GV`, `US` are dropped from the Fortran
def, which is why the two binder lists line up positionally.

There is no hand-written model: the point lemma relates the two generated
defs directly. It is not `rfl`. The one delta is the documented C++/Fortran
parse asymmetry for unary minus, in the `u < 0` branch: Fortran's `-u * dt`
is `-(u * dt)` (R1008), C++'s is `(-u) * dt`. `neg_mul` normalizes both to
the same term; everything else is syntactically identical.
-/

namespace Groundline

noncomputable section

/-- **Point lemma:** the C++ port and the Fortran elemental subroutine compute
the same `(uh, duhdu)` over ℝ, for every candidate velocity, every
reconstruction, and both settings of `vol_CFL`. -/
theorem fluxElem_point_equiv
    (u h h_p1 h_L h_L_p1 h_R h_R_p1 uh duhdu visc_rem G_dy_Cu G_IareaT G_IareaT_p1
      G_IdxT G_IdxT_p1 dt : ℝ) (vol_CFL : Bool) (por_face_area : ℝ) :
    GeneratedCpp.flux_elem_point u h h_p1 h_L h_L_p1 h_R h_R_p1 uh duhdu visc_rem
        G_dy_Cu G_IareaT G_IareaT_p1 G_IdxT G_IdxT_p1 dt vol_CFL por_face_area
      = GeneratedFtn.flux_elem u h h_p1 h_L h_L_p1 h_R h_R_p1 uh duhdu visc_rem
        G_dy_Cu G_IareaT G_IareaT_p1 G_IdxT G_IdxT_p1 dt vol_CFL por_face_area := by
  simp only [GeneratedCpp.flux_elem_point, GeneratedFtn.flux_elem, neg_mul]

/-- **Kernel level:** applied cell by cell — as every mass-flux column kernel
does, once per layer, with the loop-invariant `dt` and `vol_CFL` — the two
sides agree as arrays of `(uh, duhdu)` pairs. -/
theorem fluxElem_kernel_equiv {ι : Type*}
    (u h h_p1 h_L h_L_p1 h_R h_R_p1 uh duhdu visc_rem G_dy_Cu G_IareaT G_IareaT_p1
      G_IdxT G_IdxT_p1 : ι → ℝ) (dt : ℝ) (vol_CFL : Bool) (por_face_area : ι → ℝ) :
    (fun i => GeneratedCpp.flux_elem_point (u i) (h i) (h_p1 i) (h_L i) (h_L_p1 i)
        (h_R i) (h_R_p1 i) (uh i) (duhdu i) (visc_rem i) (G_dy_Cu i) (G_IareaT i)
        (G_IareaT_p1 i) (G_IdxT i) (G_IdxT_p1 i) dt vol_CFL (por_face_area i))
      = fun i => GeneratedFtn.flux_elem (u i) (h i) (h_p1 i) (h_L i) (h_L_p1 i)
        (h_R i) (h_R_p1 i) (uh i) (duhdu i) (visc_rem i) (G_dy_Cu i) (G_IareaT i)
        (G_IareaT_p1 i) (G_IdxT i) (G_IdxT_p1 i) dt vol_CFL (por_face_area i) :=
  funext fun i => fluxElem_point_equiv (u i) (h i) (h_p1 i) (h_L i) (h_L_p1 i)
    (h_R i) (h_R_p1 i) (uh i) (duhdu i) (visc_rem i) (G_dy_Cu i) (G_IareaT i)
    (G_IareaT_p1 i) (G_IdxT i) (G_IdxT_p1 i) dt vol_CFL (por_face_area i)

end

end Groundline
