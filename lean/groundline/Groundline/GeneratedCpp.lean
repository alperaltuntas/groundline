import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
-- Generated expressions stay on one line, however wide.
set_option linter.style.longLine false
-- Outputs are also inputs; a kernel may never read an output's incoming value.
set_option linter.unusedVariables false

/-!
# GENERATED FILE — do not edit

Emitted by `groundline.lean_printer` from clang JSON ASTs
(`groundline.frontend.clang_kernel`).
Regenerate with `groundline kernel generate` (manifest: `turbo-stack.kernels.toml`).
Fidelity against the hand-written reference models is machine-checked in
`Groundline/FidelityCpp.lean`.

Extraction provenance (pinned):
  clang version 21.0.0git (https://github.com/llvm/llvm-project.git bb982e733cfcda7e4cfb0583544f68af65211ed1)
  -std=c++20 -fsyntax-only -Xclang -ast-dump=json -Xclang -ast-dump-filter
  -I/glade/work/altuntas/turbo-stack/bin/gnu/MOM6_using_TIM/amrex/install/include
  -I/glade/work/altuntas/turbo-stack/submodules/infra/TIM/mom/cpp
  -I/glade/work/altuntas/llvm-hpc/include
-/

namespace Groundline.GeneratedCpp

noncomputable section

/-- Generated from `ppm_limit_pos_point` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm_kernel.hpp` (clang JSON AST).
Outputs `(h_L, h_R)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def ppm_limit_pos_point (h_L h_R h_in h_min : ℝ) : ℝ × ℝ :=
  let curv := 3 * ((h_L + h_R) - 2 * h_in)
  if curv > 0 then
    let dh := h_R - h_L
    if |dh| < curv then
      if h_in ≤ h_min then
        (h_in, h_in)
      else if 12 * curv * (h_in - h_min) < ((curv * curv) + (3 * (dh * dh))) then
        let scale := 12 * curv * (h_in - h_min) / ((curv * curv) + (3 * (dh * dh)))
        (h_in + scale * (h_L - h_in), h_in + scale * (h_R - h_in))
      else (h_L, h_R)
    else (h_L, h_R)
  else (h_L, h_R)

/-- Generated from `ppm_limit_cw84_point` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm_kernel.hpp` (clang JSON AST).
Outputs `(h_L, h_R)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def ppm_limit_cw84_point (h_L h_R h_in : ℝ) : ℝ × ℝ :=
  let h_i := h_in
  if (h_R - h_i) * (h_i - h_L) ≤ 0 then
    (h_i, h_i)
  else
    let RLdiff := h_R - h_L
    let RLmean := 0.5 * (h_R + h_L)
    let FunFac := 6 * RLdiff * (h_i - RLmean)
    let RLdiff2 := RLdiff * RLdiff
    if FunFac < -RLdiff2 then
      (if FunFac > RLdiff2 then 3 * h_i - 2 * h_R else h_L, 3 * h_i - 2 * (if FunFac > RLdiff2 then 3 * h_i - 2 * h_R else h_L))
    else (if FunFac > RLdiff2 then 3 * h_i - 2 * h_R else h_L, h_R)

/-- Generated from `edge_thickness_upwind_point` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm_kernel.hpp` (clang JSON AST).
Outputs `(h_L, h_R)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def edge_thickness_upwind_point (h_L h_R h_in : ℝ) : ℝ × ℝ :=
  (h_in, h_in)

/-- Generated from `thickness_to_dz_3d_boussinesq_point` in `submodules/infra/TIM/mom/cpp/mom_interface_heights_kernel.hpp` (clang JSON AST).
Outputs `(dz)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def thickness_to_dz_3d_boussinesq_point (dz h h_to_z : ℝ) : ℝ :=
  h_to_z * h

/-- Generated from `thickness_to_dz_3d_nonboussinesq_point` in `submodules/infra/TIM/mom/cpp/mom_interface_heights_kernel.hpp` (clang JSON AST).
Outputs `(dz)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def thickness_to_dz_3d_nonboussinesq_point (dz h spv h_to_rz : ℝ) : ℝ :=
  h_to_rz * h * spv

/-- Generated from `ratio_max_point` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm_kernel.hpp` (clang JSON AST).
Result `ratio_max_point` — the function result, modeled functionally over ℝ. -/
def ratio_max_point (a b maxrat : ℝ) : ℝ :=
  if |a| > |maxrat * b| then
    maxrat
  else a / b

/-- Generated from `flux_elem_point` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm_kernel.hpp` (clang JSON AST).
Outputs `(uh, duhdu)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def flux_elem_point (u h h_p1 h_L h_L_p1 h_R h_R_p1 uh duhdu visc_rem G_dy_Cu G_IareaT G_IareaT_p1 G_IdxT G_IdxT_p1 dt : ℝ) (vol_CFL : Bool) (por_face_area : ℝ) : ℝ × ℝ :=
  let tmp := G_dy_Cu * por_face_area
  let h_marg := if u > 0 then h_R + (if vol_CFL then (u * dt) * (G_dy_Cu * G_IareaT) else u * dt * G_IdxT) * (h_L - h_R + 3 * ((h_L + h_R) - 2 * h) * ((if vol_CFL then (u * dt) * (G_dy_Cu * G_IareaT) else u * dt * G_IdxT) - 1)) else if u < 0 then h_L_p1 + (if vol_CFL then ((-u) * dt) * (G_dy_Cu * G_IareaT_p1) else (-u) * dt * G_IdxT_p1) * (h_R_p1 - h_L_p1 + 3 * ((h_L_p1 + h_R_p1) - 2 * h_p1) * ((if vol_CFL then ((-u) * dt) * (G_dy_Cu * G_IareaT_p1) else (-u) * dt * G_IdxT_p1) - 1)) else 0.5 * (h_L_p1 + h_R)
  (if u > 0 then tmp * u * (h_R + (if vol_CFL then (u * dt) * (G_dy_Cu * G_IareaT) else u * dt * G_IdxT) * (0.5 * (h_L - h_R) + ((h_L + h_R) - 2 * h) * ((if vol_CFL then (u * dt) * (G_dy_Cu * G_IareaT) else u * dt * G_IdxT) - 1.5))) else if u < 0 then tmp * u * (h_L_p1 + (if vol_CFL then ((-u) * dt) * (G_dy_Cu * G_IareaT_p1) else (-u) * dt * G_IdxT_p1) * (0.5 * (h_R_p1 - h_L_p1) + ((h_L_p1 + h_R_p1) - 2 * h_p1) * ((if vol_CFL then ((-u) * dt) * (G_dy_Cu * G_IareaT_p1) else (-u) * dt * G_IdxT_p1) - 1.5))) else 0, tmp * h_marg * visc_rem)

/-- Generated from `continuity_convergence_point` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm_kernel.hpp` (clang JSON AST).
Result `continuity_convergence_point` — the function result, modeled functionally over ℝ. -/
def continuity_convergence_point (h_prev flux_out flux_in dt IareaT h_min : ℝ) : ℝ :=
  max (h_prev - dt * IareaT * (flux_out - flux_in)) (h_min)

/-- Generated from ParallelFor lambda 1 of `zonal_BT_mass_flux` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm.cpp` (clang JSON AST), as a column kernel over (i, j); specialized under the hypothesis `local_specified_bc = false`, `obc_in_row = false` (guarded blocks pruned).
Outputs `(uhbt)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def zonal_BT_mass_flux {κ : Type*} (ks : List κ) (u h_in h_W h_E : κ → ℝ) (uhbt dt dy_Cu IareaT IdxT : ℝ) (por_face_areaU h_in_ip1 h_W_ip1 h_E_ip1 : κ → ℝ) (IareaT_ip1 IdxT_ip1 : ℝ) (vol_CFL : Bool) : ℝ :=
  let uhbt_val := 0
  let uhbt_val := ks.foldl (fun uhbt_val k =>
      let uh_val := (flux_elem_point (u k) (h_in k) (h_in_ip1 k) (h_W k) (h_W_ip1 k) (h_E k) (h_E_ip1 k) 0 0 1 dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 dt vol_CFL (por_face_areaU k)).1
      let duhdu_val := (flux_elem_point (u k) (h_in k) (h_in_ip1 k) (h_W k) (h_W_ip1 k) (h_E k) (h_E_ip1 k) 0 0 1 dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 dt vol_CFL (por_face_areaU k)).2
      uhbt_val + uh_val) uhbt_val
  uhbt_val

/-- Generated from ParallelFor lambda 1 of `meridional_BT_mass_flux` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm.cpp` (clang JSON AST), as a column kernel over (i, j); specialized under the hypothesis `local_specified_bc = false`, `obc_in_row = false` (guarded blocks pruned).
Outputs `(vhbt)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def meridional_BT_mass_flux {κ : Type*} (ks : List κ) (v h_in h_S h_N : κ → ℝ) (vhbt dt dx_Cv IareaT IdyT : ℝ) (por_face_areaV h_in_jp1 h_S_jp1 h_N_jp1 : κ → ℝ) (IareaT_jp1 IdyT_jp1 : ℝ) (vol_CFL : Bool) : ℝ :=
  let vhbt_val := 0
  let vhbt_val := ks.foldl (fun vhbt_val k =>
      let vh_val := (flux_elem_point (v k) (h_in k) (h_in_jp1 k) (h_S k) (h_S_jp1 k) (h_N k) (h_N_jp1 k) 0 0 1 dx_Cv IareaT IareaT_jp1 IdyT IdyT_jp1 dt vol_CFL (por_face_areaV k)).1
      let dvhdv_val := (flux_elem_point (v k) (h_in k) (h_in_jp1 k) (h_S k) (h_S_jp1 k) (h_N k) (h_N_jp1 k) 0 0 1 dx_Cv IareaT IareaT_jp1 IdyT IdyT_jp1 dt vol_CFL (por_face_areaV k)).2
      vhbt_val + vh_val) vhbt_val
  vhbt_val

/-- Generated from ParallelFor lambda 1 of `set_zonal_BT_cont` in `submodules/infra/TIM/mom/cpp/mom_continuity_ppm.cpp` (clang JSON AST), as a column kernel over (i, j).
Outputs `(FA_u_W0, FA_u_E0, FA_u_WW, FA_u_EE, uBT_WW, uBT_EE)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def set_zonal_BT_cont {κ : Type*} (ks : List κ) (u h_in h_W h_E : κ → ℝ) (FA_u_W0 FA_u_E0 FA_u_WW FA_u_EE uBT_WW uBT_EE du0 dt dxCu dy_Cu IareaT IdxT : ℝ) (visc_rem : κ → ℝ) (visc_rem_max : ℝ) (do_I : Bool) (por_face_areaU h_in_ip1 h_W_ip1 h_E_ip1 : κ → ℝ) (IareaT_ip1 IdxT_ip1 : ℝ) (vol_CFL : Bool) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  let Idt := 1 / dt
  let min_visc_rem := 0.1
  let CFL_min := 1e-6
  let active := (do_I)
  let du_CFL := (CFL_min * Idt) * dxCu
  let duR := min (0) (du0 - du_CFL)
  let duL := max (0) (du0 + du_CFL)
  let FAmt_L := 0
  let FAmt_R := 0
  let FAmt_0 := 0
  let uhtot_L := 0
  let uhtot_R := 0
  if active then
    let (duR, duL) := ks.foldl (fun (duR, duL) k =>
        let visc_rem_lim := max (visc_rem k) (min_visc_rem * visc_rem_max)
        if visc_rem_lim > 0 then
          if u k + duL * visc_rem_lim < du_CFL * visc_rem k then
            (if u k + duR * visc_rem_lim > (-du_CFL) * visc_rem k then (-(u k + du_CFL * visc_rem k)) / visc_rem_lim else duR, (-(u k - du_CFL * visc_rem k)) / visc_rem_lim)
          else (if u k + duR * visc_rem_lim > (-du_CFL) * visc_rem k then (-(u k + du_CFL * visc_rem k)) / visc_rem_lim else duR, duL)
        else (duR, duL)) (duR, duL)
    let (FAmt_0, FAmt_L, FAmt_R, uhtot_L, uhtot_R) := ks.foldl (fun (FAmt_0, FAmt_L, FAmt_R, uhtot_L, uhtot_R) k =>
        let u_L := u k + duL * visc_rem k
        let u_R := u k + duR * visc_rem k
        let u_0 := u k + du0 * visc_rem k
        let uh_0 := (flux_elem_point u_0 (h_in k) (h_in_ip1 k) (h_W k) (h_W_ip1 k) (h_E k) (h_E_ip1 k) 0 0 (visc_rem k) dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 dt vol_CFL (por_face_areaU k)).1
        let duhdu_0 := (flux_elem_point u_0 (h_in k) (h_in_ip1 k) (h_W k) (h_W_ip1 k) (h_E k) (h_E_ip1 k) 0 0 (visc_rem k) dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 dt vol_CFL (por_face_areaU k)).2
        let uh_L := (flux_elem_point u_L (h_in k) (h_in_ip1 k) (h_W k) (h_W_ip1 k) (h_E k) (h_E_ip1 k) 0 0 (visc_rem k) dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 dt vol_CFL (por_face_areaU k)).1
        let duhdu_L := (flux_elem_point u_L (h_in k) (h_in_ip1 k) (h_W k) (h_W_ip1 k) (h_E k) (h_E_ip1 k) 0 0 (visc_rem k) dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 dt vol_CFL (por_face_areaU k)).2
        let uh_R := (flux_elem_point u_R (h_in k) (h_in_ip1 k) (h_W k) (h_W_ip1 k) (h_E k) (h_E_ip1 k) 0 0 (visc_rem k) dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 dt vol_CFL (por_face_areaU k)).1
        let duhdu_R := (flux_elem_point u_R (h_in k) (h_in_ip1 k) (h_W k) (h_W_ip1 k) (h_E k) (h_E_ip1 k) 0 0 (visc_rem k) dy_Cu IareaT IareaT_ip1 IdxT IdxT_ip1 dt vol_CFL (por_face_areaU k)).2
        (FAmt_0 + duhdu_0, FAmt_L + duhdu_L, FAmt_R + duhdu_R, uhtot_L + uh_L, uhtot_R + uh_R)) (FAmt_0, FAmt_L, FAmt_R, uhtot_L, uhtot_R)
    let FA_0 := FAmt_0
    let FA_avg := FAmt_0
    let FA_avg := if (duL - du0) ≠ 0 then uhtot_L / (duL - du0) else FA_avg
    let (FA_avg, FA_0) := if FA_avg > max (FA_0) (FAmt_L) then (max (FA_0) (FAmt_L), FA_0) else if FA_avg < min (FA_0) (FAmt_L) then (FA_avg, FA_avg) else (FA_avg, FA_0)
    let FA_u_W0 := FA_0
    let uBT_WW := if |FA_0 - FAmt_L| ≤ 1e-12 * FA_0 then 0 else (1.5 * (duL - du0)) * ((FAmt_L - FA_avg) / (FAmt_L - FA_0))
    let FA_0 := FAmt_0
    let FA_avg := FAmt_0
    let FA_avg := if (duR - du0) ≠ 0 then uhtot_R / (duR - du0) else FA_avg
    let (FA_avg, FA_0) := if FA_avg > max (FA_0) (FAmt_R) then (max (FA_0) (FAmt_R), FA_0) else if FA_avg < min (FA_0) (FAmt_R) then (FA_avg, FA_avg) else (FA_avg, FA_0)
    if |FAmt_R - FA_0| ≤ 1e-12 * FA_0 then
      (FA_u_W0, FA_0, FAmt_L, FAmt_R, uBT_WW, 0)
    else (FA_u_W0, FA_0, FAmt_L, FAmt_R, uBT_WW, (1.5 * (duR - du0)) * ((FAmt_R - FA_avg) / (FAmt_R - FA_0)))
  else (0, 0, 0, 0, 0, 0)

end

end Groundline.GeneratedCpp
