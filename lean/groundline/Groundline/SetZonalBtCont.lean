import Groundline.SeqSchema
import Groundline.FluxElem

set_option linter.style.header false

/-!
# `set_zonal_BT_cont`: the barotropic-consistency face areas

Kernel pair (TIM PR 36; Tier B, stage B2 of docs/COLUMN_KERNELS.md):
  Fortran:  `set_zonal_BT_cont`, MOM6/src/core/MOM_continuity_PPM.F90 — the
            whole subroutine, as a column kernel over `(j, I)`
  C++:      the `ParallelFor(bx2d)` lambda of `MOM::set_zonal_BT_cont`,
            TIM/mom/cpp/mom_continuity_ppm.cpp

Per column, both sides pick two test velocity corrections `duL`, `duR` (a
fold over the layers, each step conditional), sum the marginal face areas and
transports of the three test velocities (a fold with five state variables,
three `flux_elem` calls per layer), and then fit the effective face areas
`FA_u_W0 / FA_u_WW / uBT_WW` and their easterly twins per column.

The constructs new to this stage, and how the two sides spell them:

* **The mask.** The Fortran runs its two k-loops as `do k ; do concurrent
  (I=…, do_I(I,j))` — every layer step is masked — and its tail under `if
  (do_I(I,j))`; the C++ tests `active = (do_I(i,j,0) != 0)` once and puts
  both loops and the tail under `if (active)`. The generated Fortran def has
  `if do_i then step else (duR, duL)` inside each fold, the C++ def the folds
  inside `if active`. The proof is a case split on the Bool: when it is
  true the masked steps *are* the steps; when it is false both sides are the
  six zeros. Arithmetic-free.
* **Row scratch.** The Fortran's `duL(I)`, `FAmt_L(I)`, … are 1-D locals
  indexed by `I` alone under the plain `do j`; the C++ has plain lambda
  locals. Both are per-column scalars in the generated defs.
* **Several fold states.** `let (duR, duL) := ks.foldl (fun (duR, duL) k => …)`
  on both sides — pattern-matching lambdas over the state tuple.
* **The join that reads both prior values.** `if (FA_avg > max(FA_0,
  FAmt_L)) then FA_avg = … elseif (FA_avg < min(FA_0, FAmt_L)) then FA_0 =
  FA_avg endif` re-assigns two locals from each other's *prior* values, so
  it is bound as one destructuring `let (FA_avg, FA_0) := if … then (…, …)
  else …` — on both sides, the C++ `else if` flattened to the same branch
  list.
* **Component outputs.** The Fortran writes `BT_cont%FA_u_W0(I,j)` on an
  `intent(inout)` derived-type dummy; the C++ writes six separate `Array4`s.
  The Fortran def's outputs come in first-write order `(W0, WW, uWW, E0, EE,
  uEE)`, the C++ def's in parameter order `(W0, E0, WW, EE, uWW, uEE)`;
  `btContCppOrder` is that permutation, and the theorem states the C++
  result equals the permuted Fortran result.

Two rewrites carry genuine language semantics, both float-exact (the
readiness ledger in the manual): `neg_mul` for `-du_CFL*visc_rem`, which C++
parses as `(-du_CFL) * visc_rem` and Fortran as `-(du_CFL * visc_rem)`, and
`neg_div` for `-(u + …) / visc_rem_lim`, parsed `(-(…)) / v` versus
`-((…) / v)` in the same way. Everything else is unfolding, zeta-reduction,
the banked `fluxElem_point_equiv`, the case split on the mask, and one
bookkeeping step: the Fortran tail is an `if` of two six-tuples, and the
permutation has to be pushed through that `if` (`apply_ite`) before the two
sides are the same `if` of tuples.

Both defs are specialized to nothing this time — the subroutine has no OBC
path — and the Fortran def carries no timer calls to drop.
-/

namespace Groundline

noncomputable section

/-- The permutation from the Fortran def's output order `(FA_u_W0, FA_u_WW,
uBT_WW, FA_u_E0, FA_u_EE, uBT_EE)` — the components in first-write order —
to the C++ def's `(FA_u_W0, FA_u_E0, FA_u_WW, FA_u_EE, uBT_WW, uBT_EE)`, its
`Array4` parameters in declaration order. -/
def btContCppOrder : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  fun (w0, ww, uww, e0, ee, uee) => (w0, e0, ww, ee, uww, uee)

/-- The permutation on an explicit tuple, by unfolding. -/
theorem btContCppOrder_mk (w0 ww uww e0 ee uee : ℝ) :
    btContCppOrder (w0, ww, uww, e0, ee, uee) = (w0, e0, ww, ee, uww, uee) := rfl

/-! ## Column lemma -/

/-- **Per column:** the C++ lambda body equals the Fortran subroutine body for
one column, up to the output permutation, for any enumeration of the layers. -/
theorem setZonalBtCont_column_equiv {κ : Type*} (ks : List κ)
    (u h_in h_W h_E visc_rem por_face_areaU h_in_ip1 h_W_ip1 h_E_ip1 : κ → ℝ)
    (FA_u_W0 FA_u_E0 FA_u_WW FA_u_EE uBT_WW uBT_EE du0 dt dxCu dy_Cu IareaT IdxT
      visc_rem_max IareaT_ip1 IdxT_ip1 : ℝ) (do_I vol_CFL : Bool) :
    GeneratedCpp.set_zonal_BT_cont ks u h_in h_W h_E FA_u_W0 FA_u_E0 FA_u_WW FA_u_EE uBT_WW
        uBT_EE du0 dt dxCu dy_Cu IareaT IdxT visc_rem visc_rem_max do_I por_face_areaU
        h_in_ip1 h_W_ip1 h_E_ip1 IareaT_ip1 IdxT_ip1 vol_CFL
      = btContCppOrder (GeneratedFtn.set_zonal_bt_cont ks u h_in h_W h_E du0 dt visc_rem
        visc_rem_max do_I por_face_areaU dxCu h_in_ip1 h_W_ip1 h_E_ip1 dy_Cu IareaT IareaT_ip1
        IdxT IdxT_ip1 vol_CFL FA_u_W0 FA_u_WW uBT_WW FA_u_E0 FA_u_EE uBT_EE) := by
  -- The Fortran tail is `if … then (six values) else (six values)`; the
  -- permutation is pushed through that `if` (`apply_ite`) and then reduced on
  -- the explicit tuples, so both sides are an `if` of tuples.
  cases do_I <;> simp only [GeneratedCpp.set_zonal_BT_cont, GeneratedFtn.set_zonal_bt_cont,
    apply_ite btContCppOrder, btContCppOrder_mk, fluxElem_point_equiv, neg_mul, neg_div,
    Bool.false_eq_true, ↓reduceIte]

/-! ## Kernel level: the Fortran subroutine over the whole box vs the AMReX launch

`ι` is the column index type, `κ` the layer index type; `east c` is the `I+1`
neighbor column. Per-layer fields are `ι → κ → ℝ`, per-column fields `ι → ℝ`,
the mask `ι → Bool`; the per-column state is the six outputs in the Fortran
def's order. -/

/-- The Fortran subroutine over the whole box: the row loop `do j` is a plain
DO and the `do concurrent (I)` nests under it write each their own column, so
the honest model is a sequential fold of the per-column body over the column
enumeration. -/
def setZonalBtContLoopF {ι κ : Type*} [DecidableEq ι] (east : ι → ι) (ks : List κ)
    (u h_in h_W h_E visc_rem por_face_areaU : ι → κ → ℝ) (dt : ℝ)
    (du0 dxCu dy_Cu IareaT IdxT visc_rem_max : ι → ℝ) (do_I : ι → Bool) (vol_CFL : Bool)
    (s₀ : ι → ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) (cols : List ι) : ι → ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  foldSeq (fun c s => GeneratedFtn.set_zonal_bt_cont ks (u c) (h_in c) (h_W c) (h_E c) (du0 c)
      dt (visc_rem c) (visc_rem_max c) (do_I c) (por_face_areaU c) (dxCu c)
      (h_in (east c)) (h_W (east c)) (h_E (east c)) (dy_Cu c) (IareaT c) (IareaT (east c))
      (IdxT c) (IdxT (east c)) vol_CFL
      s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)
    s₀ cols

/-- The AMReX `ParallelFor(bx2d)` launch of the C++ lambda over the columns;
its result is in the C++ output order. -/
def setZonalBtContLaunchC {ι κ : Type*} (east : ι → ι) (ks : List κ)
    (u h_in h_W h_E visc_rem por_face_areaU : ι → κ → ℝ) (dt : ℝ)
    (du0 dxCu dy_Cu IareaT IdxT visc_rem_max : ι → ℝ) (do_I : ι → Bool) (vol_CFL : Bool)
    (s₀ : ι → ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) : ι → ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  fun c => GeneratedCpp.set_zonal_BT_cont ks (u c) (h_in c) (h_W c) (h_E c)
      (s₀ c).1 (s₀ c).2.2.2.1 (s₀ c).2.1 (s₀ c).2.2.2.2.1 (s₀ c).2.2.1 (s₀ c).2.2.2.2.2
      (du0 c) dt (dxCu c) (dy_Cu c) (IareaT c) (IdxT c) (visc_rem c) (visc_rem_max c) (do_I c)
      (por_face_areaU c) (h_in (east c)) (h_W (east c)) (h_E (east c)) (IareaT (east c))
      (IdxT (east c)) vol_CFL

/-- **Kernel equivalence:** for every duplicate-free, complete enumeration of
the columns, the AMReX launch produces, column by column, the Fortran
subroutine's six output arrays (in the C++ order). -/
theorem setZonalBtCont_kernel_equiv {ι κ : Type*} [DecidableEq ι] (east : ι → ι) (ks : List κ)
    (u h_in h_W h_E visc_rem por_face_areaU : ι → κ → ℝ) (dt : ℝ)
    (du0 dxCu dy_Cu IareaT IdxT visc_rem_max : ι → ℝ) (do_I : ι → Bool) (vol_CFL : Bool)
    (s₀ : ι → ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) (cols : List ι)
    (hnd : cols.Nodup) (hall : ∀ c, c ∈ cols) :
    setZonalBtContLaunchC east ks u h_in h_W h_E visc_rem por_face_areaU dt du0 dxCu dy_Cu
        IareaT IdxT visc_rem_max do_I vol_CFL s₀
      = fun c => btContCppOrder (setZonalBtContLoopF east ks u h_in h_W h_E visc_rem
        por_face_areaU dt du0 dxCu dy_Cu IareaT IdxT visc_rem_max do_I vol_CFL s₀ cols c) := by
  unfold setZonalBtContLoopF setZonalBtContLaunchC
  rw [foldSeq_eq_pointwiseMap _ cols hnd hall s₀]
  funext c
  exact setZonalBtCont_column_equiv ks (u c) (h_in c) (h_W c) (h_E c) (visc_rem c)
    (por_face_areaU c) (h_in (east c)) (h_W (east c)) (h_E (east c))
    (s₀ c).1 (s₀ c).2.2.2.1 (s₀ c).2.1 (s₀ c).2.2.2.2.1 (s₀ c).2.2.1 (s₀ c).2.2.2.2.2
    (du0 c) dt (dxCu c) (dy_Cu c) (IareaT c) (IdxT c) (visc_rem_max c) (IareaT (east c))
    (IdxT (east c)) (do_I c) vol_CFL

end

end Groundline
