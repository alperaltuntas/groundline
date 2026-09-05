import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
-- Generated expressions stay on one line, however wide.
set_option linter.style.longLine false
-- Outputs are also inputs; a kernel may never read an output's incoming value.
set_option linter.unusedVariables false

/-!
# GENERATED FILE — do not edit

Emitted by `groundline.lean_printer` from flang with-sema
parse-tree dumps (`groundline.frontend.flang_kernel`).
Regenerate with `groundline kernel generate` (manifest: `turbo-stack.kernels.toml`).
Fidelity against the hand-written reference models is machine-checked in
`Groundline/FidelityFtn.lean`.
-/

namespace Groundline.GeneratedFtn

noncomputable section

/-- Generated from `ppm_limit_pos` in `MOM6/MOM_continuity_PPM.o_ptree` (flang with-sema dump).
Outputs `(h_l, h_r)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def ppm_limit_pos (h_in h_l h_r h_min : ℝ) : ℝ × ℝ :=
  let curv := 3 * ((h_l + h_r) - 2 * h_in)
  if curv > 0 then
    let dh := h_r - h_l
    if |dh| < curv then
      if h_in ≤ h_min then
        (h_in, h_in)
      else if 12 * curv * (h_in - h_min) < (curv ^ 2 + 3 * dh ^ 2) then
        let scale := 12 * curv * (h_in - h_min) / (curv ^ 2 + 3 * dh ^ 2)
        (h_in + scale * (h_l - h_in), h_in + scale * (h_r - h_in))
      else (h_l, h_r)
    else (h_l, h_r)
  else (h_l, h_r)

/-- Generated from `ppm_limit_cw84` in `MOM6/MOM_continuity_PPM.o_ptree` (flang with-sema dump).
Outputs `(h_l, h_r)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def ppm_limit_cw84 (h_in h_l h_r : ℝ) : ℝ × ℝ :=
  let h_i := h_in
  if (h_r - h_i) * (h_i - h_l) ≤ 0 then
    (h_i, h_i)
  else
    let rldiff := h_r - h_l
    let rlmean := 0.5 * (h_r + h_l)
    let funfac := 6 * rldiff * (h_i - rlmean)
    let rldiff2 := rldiff * rldiff
    if funfac < -rldiff2 then
      (if funfac > rldiff2 then 3 * h_i - 2 * h_r else h_l, 3 * h_i - 2 * (if funfac > rldiff2 then 3 * h_i - 2 * h_r else h_l))
    else (if funfac > rldiff2 then 3 * h_i - 2 * h_r else h_l, h_r)

/-- Generated from loop nest 1 of `zonal_edge_thickness` in `MOM6/MOM_continuity_PPM.o_ptree` (flang with-sema dump).
Outputs `(h_w, h_e)` — the `intent(out)` arguments, modeled functionally over ℝ. -/
def edge_thickness_upwind (h_in h_w h_e : ℝ) : ℝ × ℝ :=
  (h_in, h_in)

/-- Generated from loop nest 4 of `thickness_to_dz_3d` in `MOM6/MOM_interface_heights.o_ptree` (flang with-sema dump).
Outputs `(dz)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def thickness_to_dz_3d_boussinesq (h dz h_to_z : ℝ) : ℝ :=
  h_to_z * h

/-- Generated from loop nest 2 of `thickness_to_dz_3d` in `MOM6/MOM_interface_heights.o_ptree` (flang with-sema dump).
Outputs `(dz)` — the `intent(inout)` arguments, modeled functionally over ℝ. -/
def thickness_to_dz_3d_nonboussinesq (h dz h_to_rz spv_avg : ℝ) : ℝ :=
  h_to_rz * h * spv_avg

/-- Generated from `ratio_max` in `MOM6/MOM_continuity_PPM.o_ptree` (flang with-sema dump).
Result `ratio` — the function result, modeled functionally over ℝ. -/
def ratio_max (a b maxrat : ℝ) : ℝ :=
  if |a| > |maxrat * b| then
    maxrat
  else a / b

/-- Generated from `flux_elem` in `MOM6/MOM_continuity_PPM.o_ptree` (flang with-sema dump).
Outputs `(uh, duhdu)` — the `intent(out)` arguments, modeled functionally over ℝ. -/
def flux_elem (u h h_p1 h_l h_l_p1 h_r h_r_p1 uh duhdu visc_rem g_dy_cu g_iareat g_iareat_p1 g_idxt g_idxt_p1 dt : ℝ) (vol_cfl : Bool) (por_face_area : ℝ) : ℝ × ℝ :=
  let tmp := g_dy_cu * por_face_area
  let h_marg := if u > 0 then h_r + (if vol_cfl then (u * dt) * (g_dy_cu * g_iareat) else u * dt * g_idxt) * (h_l - h_r + 3 * ((h_l + h_r) - 2 * h) * ((if vol_cfl then (u * dt) * (g_dy_cu * g_iareat) else u * dt * g_idxt) - 1)) else if u < 0 then h_l_p1 + (if vol_cfl then (-(u * dt)) * (g_dy_cu * g_iareat_p1) else -(u * dt * g_idxt_p1)) * (h_r_p1 - h_l_p1 + 3 * ((h_l_p1 + h_r_p1) - 2 * h_p1) * ((if vol_cfl then (-(u * dt)) * (g_dy_cu * g_iareat_p1) else -(u * dt * g_idxt_p1)) - 1)) else 0.5 * (h_l_p1 + h_r)
  (if u > 0 then tmp * u * (h_r + (if vol_cfl then (u * dt) * (g_dy_cu * g_iareat) else u * dt * g_idxt) * (0.5 * (h_l - h_r) + ((h_l + h_r) - 2 * h) * ((if vol_cfl then (u * dt) * (g_dy_cu * g_iareat) else u * dt * g_idxt) - 1.5))) else if u < 0 then tmp * u * (h_l_p1 + (if vol_cfl then (-(u * dt)) * (g_dy_cu * g_iareat_p1) else -(u * dt * g_idxt_p1)) * (0.5 * (h_r_p1 - h_l_p1) + ((h_l_p1 + h_r_p1) - 2 * h_p1) * ((if vol_cfl then (-(u * dt)) * (g_dy_cu * g_iareat_p1) else -(u * dt * g_idxt_p1)) - 1.5))) else 0, tmp * h_marg * visc_rem)

end

end Groundline.GeneratedFtn
