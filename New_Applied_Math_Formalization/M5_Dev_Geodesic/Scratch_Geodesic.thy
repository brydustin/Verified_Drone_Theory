theory Scratch_Geodesic
  imports "Applied_Math_D34_Analytic.D34_Geodesic_Branch"
begin

text \<open>Guard-only: the geodesic (c-space normal-coordinate) branch content lives in
  \<open>Appendix/AnalyticBridge/D34_Geodesic_Branch.thy\<close>.  This file re-checks the
  Tier 6 cubic-stratum names are present in the heap.\<close>

thm Phi_par_zero_of_gradU_zero radial_level1_of_gradU_zero
thm H_par_zero_of_HessU_zero radial_level2_of_HessU_zero
thm Lambda_cub_ij_def Jac3_H0cub_def Jac3_H0cub_identity Jac3_H0cub_nonzero_criterion
thm real_analytic_on_Lambda_cub_ij
thm Lambda_cub_two_bump_witness Lambda_cub_zeros_nowhere_dense
thm Jac3_H0cub_zeros_meager Jac3_H0cub_nonzero_in_open
thm Jac3_H0cub_nonzero_in_open_robust4_witness

end
