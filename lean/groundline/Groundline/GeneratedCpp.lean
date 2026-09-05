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

end

end Groundline.GeneratedCpp
