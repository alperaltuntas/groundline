import Groundline.SeqSchema
import Groundline.FluxElem

set_option linter.style.header false

/-!
# The first column kernels: the barotropic mass fluxes

Kernel pairs (TIM PR 36; the first Tier-B kernels, docs/COLUMN_KERNELS.md):
  Fortran:  `zonal_BT_mass_flux`, `meridional_BT_mass_flux`
            MOM6/src/core/MOM_continuity_PPM.F90 — whole subroutines, as
            column kernels over `(j, I)` / `(j, i)`
  C++:      the `ParallelFor` lambda of `MOM::zonal_BT_mass_flux` /
            `MOM::meridional_BT_mass_flux`, TIM/mom/cpp/mom_continuity_ppm.cpp

Per column, both sides compute the depth-integrated transport
`uhbt = Σ_k uh_k`, where `uh_k` is the first output of `flux_elem` for layer
`k`. The Fortran does it in two passes — a `do concurrent (k, j, I)` map
filling the 3-D temporary `uh(I,j,k)`, then a plain `do k ; do j ; do I` fold
accumulating it — the C++ in one `for k` loop that calls `flux_elem_point` and
accumulates `uh_val` as it goes. The generated defs make the two shapes the
same term: the map is `let uh := fun k => (flux_elem …).1`, the fold
`ks.foldl (fun uhbt k => uhbt + uh k) 0`, and unfolding the `let` *is* the
C++'s fused loop. Loop fusion is definitional; nothing is reordered — both
sides walk the same enumeration `ks` in the same order.

Both defs are **specialized** under the manifest hypotheses
`local_specified_bc = false`, `obc_in_row = false` — the open-boundary paths,
which the C++ port itself aborts on (a non-null OBC pointer) — and, on the
Fortran side, with the timer calls dropped; the generated doc comments say so.

The column lemmas are `simp only` with the two defs and the banked
`fluxElem_point_equiv`: unfold, zeta-reduce the lets, rewrite the callee, and
the folds coincide syntactically. This is composition through a banked
theorem — the first generated def that references another.

The kernel-level statements lift over columns with the licenses each nest
carries: the C++ `ParallelFor(bx2d)` is a pointwise map over columns (the
assertion); the Fortran's accumulation nest is a plain DO over `(j, I)`, so its
honest model is `foldSeq` over the column enumeration, with the schema lemma
turning it into the pointwise map. The neighbor columns the stencils read
(`h_in(I+1,j,k)`, `G%IareaT(I+1,j)`) appear as an explicit neighbor map
`east` / `north` on the column index type, exactly as in the convergence
theorems.
-/

namespace Groundline

noncomputable section

/-! ## Column lemmas -/

/-- **Zonal, per column:** the C++ lambda body equals the Fortran subroutine
body for one column, for any enumeration of the layers. -/
theorem zonalBtMassFlux_column_equiv {κ : Type*} (ks : List κ)
    (u h_in h_W h_E por_face_areaU h_in_ip1 h_W_ip1 h_E_ip1 : κ → ℝ)
    (uhbt dt dy_Cu IareaT IdxT IareaT_ip1 IdxT_ip1 : ℝ) (vol_CFL : Bool) :
    GeneratedCpp.zonal_BT_mass_flux ks u h_in h_W h_E uhbt dt dy_Cu IareaT IdxT
        por_face_areaU h_in_ip1 h_W_ip1 h_E_ip1 IareaT_ip1 IdxT_ip1 vol_CFL
      = GeneratedFtn.zonal_bt_mass_flux ks u h_in h_W h_E uhbt dt por_face_areaU
        h_in_ip1 h_W_ip1 h_E_ip1 dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 vol_CFL := by
  simp only [GeneratedCpp.zonal_BT_mass_flux, GeneratedFtn.zonal_bt_mass_flux,
             fluxElem_point_equiv]

/-- **Meridional, per column.** -/
theorem meridionalBtMassFlux_column_equiv {κ : Type*} (ks : List κ)
    (v h_in h_S h_N por_face_areaV h_in_jp1 h_S_jp1 h_N_jp1 : κ → ℝ)
    (vhbt dt dx_Cv IareaT IdyT IareaT_jp1 IdyT_jp1 : ℝ) (vol_CFL : Bool) :
    GeneratedCpp.meridional_BT_mass_flux ks v h_in h_S h_N vhbt dt dx_Cv IareaT IdyT
        por_face_areaV h_in_jp1 h_S_jp1 h_N_jp1 IareaT_jp1 IdyT_jp1 vol_CFL
      = GeneratedFtn.meridional_bt_mass_flux ks v h_in h_S h_N vhbt dt por_face_areaV
        h_in_jp1 h_S_jp1 h_N_jp1 dx_Cv IareaT IareaT_jp1 IdyT IdyT_jp1 vol_CFL := by
  simp only [GeneratedCpp.meridional_BT_mass_flux, GeneratedFtn.meridional_bt_mass_flux,
             fluxElem_point_equiv]

/-! ## Kernel level: the Fortran subroutine over the whole box vs the AMReX launch

`ι` is the column index type, `κ` the layer index type; `east c` is the column
whose west face is column `c`'s east face (the `I+1` neighbor). Per-layer
fields are `ι → κ → ℝ`, per-column fields `ι → ℝ`. -/

/-- The Fortran subroutine over the whole box: its accumulation nest is a
plain DO over the columns, so the honest model is a sequential fold of the
per-column body over the column enumeration (the map nest that precedes it
is folded into the body definitionally — `uh` is a function). -/
def zonalBtMassFluxLoopF {ι κ : Type*} [DecidableEq ι] (east : ι → ι) (ks : List κ)
    (u h_in h_W h_E por_face_areaU : ι → κ → ℝ) (dt : ℝ)
    (dy_Cu IareaT IdxT : ι → ℝ) (vol_CFL : Bool) (uhbt₀ : ι → ℝ) (cols : List ι) : ι → ℝ :=
  foldSeq (fun c s => GeneratedFtn.zonal_bt_mass_flux ks (u c) (h_in c) (h_W c) (h_E c) s dt
      (por_face_areaU c) (h_in (east c)) (h_W (east c)) (h_E (east c))
      (dy_Cu c) (IareaT c) (IareaT (east c)) (IdxT c) (IdxT (east c)) vol_CFL)
    uhbt₀ cols

/-- The AMReX `ParallelFor(bx2d)` launch of the C++ lambda over the columns. -/
def zonalBtMassFluxLaunchC {ι κ : Type*} (east : ι → ι) (ks : List κ)
    (u h_in h_W h_E por_face_areaU : ι → κ → ℝ) (dt : ℝ)
    (dy_Cu IareaT IdxT : ι → ℝ) (vol_CFL : Bool) (uhbt₀ : ι → ℝ) : ι → ℝ :=
  fun c => GeneratedCpp.zonal_BT_mass_flux ks (u c) (h_in c) (h_W c) (h_E c) (uhbt₀ c) dt
      (dy_Cu c) (IareaT c) (IdxT c) (por_face_areaU c)
      (h_in (east c)) (h_W (east c)) (h_E (east c)) (IareaT (east c)) (IdxT (east c)) vol_CFL

/-- **Kernel equivalence, zonal:** for every duplicate-free, complete
enumeration of the columns, the Fortran subroutine and the AMReX launch
produce the same `uhbt` array. -/
theorem zonalBtMassFlux_kernel_equiv {ι κ : Type*} [DecidableEq ι] (east : ι → ι) (ks : List κ)
    (u h_in h_W h_E por_face_areaU : ι → κ → ℝ) (dt : ℝ)
    (dy_Cu IareaT IdxT : ι → ℝ) (vol_CFL : Bool) (uhbt₀ : ι → ℝ) (cols : List ι)
    (hnd : cols.Nodup) (hall : ∀ c, c ∈ cols) :
    zonalBtMassFluxLoopF east ks u h_in h_W h_E por_face_areaU dt dy_Cu IareaT IdxT
        vol_CFL uhbt₀ cols
      = zonalBtMassFluxLaunchC east ks u h_in h_W h_E por_face_areaU dt dy_Cu IareaT IdxT
        vol_CFL uhbt₀ := by
  unfold zonalBtMassFluxLoopF zonalBtMassFluxLaunchC
  rw [foldSeq_eq_pointwiseMap _ cols hnd hall uhbt₀]
  funext c
  exact (zonalBtMassFlux_column_equiv ks (u c) (h_in c) (h_W c) (h_E c) (por_face_areaU c)
    (h_in (east c)) (h_W (east c)) (h_E (east c)) (uhbt₀ c) dt (dy_Cu c) (IareaT c) (IdxT c)
    (IareaT (east c)) (IdxT (east c)) vol_CFL).symm

/-- The meridional twin, with `north` the `J+1` neighbor. -/
def meridionalBtMassFluxLoopF {ι κ : Type*} [DecidableEq ι] (north : ι → ι) (ks : List κ)
    (v h_in h_S h_N por_face_areaV : ι → κ → ℝ) (dt : ℝ)
    (dx_Cv IareaT IdyT : ι → ℝ) (vol_CFL : Bool) (vhbt₀ : ι → ℝ) (cols : List ι) : ι → ℝ :=
  foldSeq (fun c s => GeneratedFtn.meridional_bt_mass_flux ks (v c) (h_in c) (h_S c) (h_N c) s dt
      (por_face_areaV c) (h_in (north c)) (h_S (north c)) (h_N (north c))
      (dx_Cv c) (IareaT c) (IareaT (north c)) (IdyT c) (IdyT (north c)) vol_CFL)
    vhbt₀ cols

def meridionalBtMassFluxLaunchC {ι κ : Type*} (north : ι → ι) (ks : List κ)
    (v h_in h_S h_N por_face_areaV : ι → κ → ℝ) (dt : ℝ)
    (dx_Cv IareaT IdyT : ι → ℝ) (vol_CFL : Bool) (vhbt₀ : ι → ℝ) : ι → ℝ :=
  fun c => GeneratedCpp.meridional_BT_mass_flux ks (v c) (h_in c) (h_S c) (h_N c) (vhbt₀ c) dt
      (dx_Cv c) (IareaT c) (IdyT c) (por_face_areaV c)
      (h_in (north c)) (h_S (north c)) (h_N (north c)) (IareaT (north c)) (IdyT (north c)) vol_CFL

/-- **Kernel equivalence, meridional.** -/
theorem meridionalBtMassFlux_kernel_equiv {ι κ : Type*} [DecidableEq ι] (north : ι → ι)
    (ks : List κ)
    (v h_in h_S h_N por_face_areaV : ι → κ → ℝ) (dt : ℝ)
    (dx_Cv IareaT IdyT : ι → ℝ) (vol_CFL : Bool) (vhbt₀ : ι → ℝ) (cols : List ι)
    (hnd : cols.Nodup) (hall : ∀ c, c ∈ cols) :
    meridionalBtMassFluxLoopF north ks v h_in h_S h_N por_face_areaV dt dx_Cv IareaT IdyT
        vol_CFL vhbt₀ cols
      = meridionalBtMassFluxLaunchC north ks v h_in h_S h_N por_face_areaV dt dx_Cv IareaT
        IdyT vol_CFL vhbt₀ := by
  unfold meridionalBtMassFluxLoopF meridionalBtMassFluxLaunchC
  rw [foldSeq_eq_pointwiseMap _ cols hnd hall vhbt₀]
  funext c
  exact (meridionalBtMassFlux_column_equiv ks (v c) (h_in c) (h_S c) (h_N c) (por_face_areaV c)
    (h_in (north c)) (h_S (north c)) (h_N (north c)) (vhbt₀ c) dt (dx_Cv c) (IareaT c) (IdyT c)
    (IareaT (north c)) (IdyT (north c)) vol_CFL).symm

end

end Groundline
