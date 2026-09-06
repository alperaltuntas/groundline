import Groundline.PpmLimitPos
import Groundline.PpmLimitCw84
import Groundline.FidelityFtn
import Groundline.FidelityCpp
import Groundline.SeqSchema
import Groundline.EdgeThicknessUpwind
import Groundline.ThicknessToDz
import Groundline.RatioMax
import Groundline.FluxElem
import Groundline.ContinuityConvergence
import Groundline.BtMassFlux
import Groundline.SetZonalBtCont
import Groundline.QuickstartEquiv

set_option linter.style.header false

/-!
# Axioms audit (trusted-base check, VISION D6)

`#print axioms` on each theorem must list nothing beyond Lean/Mathlib's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — in particular
no `sorryAx`. The output is checked by eye in the build log.
-/

#print axioms Groundline.ppmLimitPos_point_equiv
#print axioms Groundline.ppmLimitPos_kernel_equiv

#print axioms Groundline.GeneratedFtn.ppm_limit_pos
#print axioms generated_ppm_limit_pos_fidelity
#print axioms generated_matches_cpp

#print axioms Groundline.GeneratedFtn.ppm_limit_cw84
#print axioms Groundline.ppmLimitCw84_point_equiv
#print axioms Groundline.ppmLimitCw84_kernel_equiv

#print axioms Groundline.GeneratedCpp.ppm_limit_pos_point
#print axioms Groundline.GeneratedCpp.ppm_limit_cw84_point
#print axioms generated_cpp_ppm_limit_pos_fidelity
#print axioms generated_cpp_ppm_limit_cw84_fidelity
#print axioms generated_cpp_matches_generated_fortran_pos
#print axioms generated_cpp_matches_generated_fortran_cw84

-- The plain-DO schema (Groundline/SeqSchema.lean). The polymorphic defs and the
-- structural-induction proofs use no classical reasoning, so these may report
-- a strict SUBSET of the three standard axioms — anything beyond them (in
-- particular sorryAx) is still a trusted-base violation.
#print axioms Groundline.foldSeq
#print axioms Groundline.pointwiseMap
#print axioms Groundline.foldSeq_frame
#print axioms Groundline.foldSeq_apply_of_mem
#print axioms Groundline.foldSeq_eq_pointwiseMap

#print axioms Groundline.GeneratedFtn.edge_thickness_upwind
#print axioms Groundline.GeneratedCpp.edge_thickness_upwind_point
#print axioms Groundline.edgeThicknessUpwind_point_equiv
#print axioms Groundline.edgeThicknessUpwind_kernel_equiv

#print axioms Groundline.GeneratedFtn.thickness_to_dz_3d_boussinesq
#print axioms Groundline.GeneratedCpp.thickness_to_dz_3d_boussinesq_point
#print axioms Groundline.thicknessToDzBouss_point_equiv
#print axioms Groundline.thicknessToDzBouss_kernel_equiv

#print axioms Groundline.GeneratedFtn.thickness_to_dz_3d_nonboussinesq
#print axioms Groundline.GeneratedCpp.thickness_to_dz_3d_nonboussinesq_point
#print axioms Groundline.thicknessToDzNonBouss_point_equiv
#print axioms Groundline.thicknessToDzNonBouss_kernel_equiv

#print axioms Groundline.GeneratedFtn.ratio_max
#print axioms Groundline.GeneratedCpp.ratio_max_point
#print axioms Groundline.ratioMax_point_equiv
#print axioms Groundline.ratioMax_kernel_equiv

#print axioms Groundline.GeneratedFtn.flux_elem
#print axioms Groundline.GeneratedCpp.flux_elem_point
#print axioms Groundline.fluxElem_point_equiv
#print axioms Groundline.fluxElem_kernel_equiv

#print axioms Groundline.GeneratedCpp.continuity_convergence_point
#print axioms Groundline.GeneratedFtn.continuity_convergence_zonal
#print axioms Groundline.GeneratedFtn.continuity_convergence_zonal_inplace
#print axioms Groundline.GeneratedFtn.continuity_convergence_meridional
#print axioms Groundline.GeneratedFtn.continuity_convergence_meridional_inplace
#print axioms Groundline.convergenceZonal_point_equiv
#print axioms Groundline.convergenceZonalInplace_point_equiv
#print axioms Groundline.convergenceMeridional_point_equiv
#print axioms Groundline.convergenceMeridionalInplace_point_equiv
#print axioms Groundline.convergenceZonal_kernel_equiv
#print axioms Groundline.convergenceZonalInplace_kernel_equiv
#print axioms Groundline.convergenceMeridional_kernel_equiv
#print axioms Groundline.convergenceMeridionalInplace_kernel_equiv

-- The first column kernels (docs/COLUMN_KERNELS.md): generated defs that call
-- the banked flux_elem defs, and theorems composed through fluxElem_point_equiv.
#print axioms Groundline.GeneratedFtn.zonal_bt_mass_flux
#print axioms Groundline.GeneratedCpp.zonal_BT_mass_flux
#print axioms Groundline.zonalBtMassFlux_column_equiv
#print axioms Groundline.zonalBtMassFlux_kernel_equiv
#print axioms Groundline.GeneratedFtn.meridional_bt_mass_flux
#print axioms Groundline.GeneratedCpp.meridional_BT_mass_flux
#print axioms Groundline.meridionalBtMassFlux_column_equiv
#print axioms Groundline.meridionalBtMassFlux_kernel_equiv

-- Tier B, stage B2 (docs/COLUMN_KERNELS.md §5): masks, several fold states,
-- component outputs; the theorem carries the output permutation.
#print axioms Groundline.GeneratedFtn.set_zonal_bt_cont
#print axioms Groundline.GeneratedCpp.set_zonal_BT_cont
#print axioms Groundline.btContCppOrder
#print axioms Groundline.btContCppOrder_mk
#print axioms Groundline.setZonalBtCont_column_equiv
#print axioms Groundline.setZonalBtCont_kernel_equiv

-- The quickstart pair (examples/quickstart/kernels.toml)
#print axioms Quickstart.GeneratedFtn.scale_clip_acc
#print axioms Quickstart.GeneratedCpp.scale_clip_acc_point
#print axioms Quickstart.scale_clip_acc_equiv
