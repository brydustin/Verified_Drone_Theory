theory Scratch_Geodesic
  imports "Applied_Math_D34_Analytic.D34_Geodesic_Branch"
begin

text \<open>Guard-only: the geodesic (c-space normal-coordinate) branch content lives in
  \<open>Appendix/AnalyticBridge/D34_Geodesic_Branch.thy\<close>.  This file re-checks the
  Tier 5b two-bump \<open>Lambda_rad_ij\<close> witness and genericity names are present in
  the heap.\<close>

thm two_bump_nth two_bump_row_sum_i two_bump_row_sum_j
thm Phi_par_uslot_radial
thm Lambda_rad_two_bump_witness Lambda_rad_zeros_nowhere_dense
thm gradU2_perp_slot_zeros_nowhere_dense real_analytic_on_Lambda_rad_ij
thm Jac3_H12rad_zeros_meager Jac3_H12rad_nonzero_in_open
thm gain_dip_nonzero_of_Dcvec_det_nonzero
thm Jac3_H12rad_zeros_meager_of_det Jac3_H12rad_nonzero_in_open_of_det
thm Jac3_H12rad_identity Jac3_H12rad_nonzero_criterion

end
