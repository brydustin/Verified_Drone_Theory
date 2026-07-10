theory Scratch_Geodesic
  imports "Applied_Math_D34_Analytic.D34_Geodesic_Branch"
begin

text \<open>Guard-only: the geodesic (c-space normal-coordinate) branch content lives in
  \<open>Appendix/AnalyticBridge/D34_Geodesic_Branch.thy\<close>.  This file just re-checks the
  key names are present in the heap.\<close>

thm Wc_def Wc_eq_cmod_sq U_dip_Wc
thm has_derivative_pair_phase_sum_x pair_phase_sum_perp_slot_zero
thm Wc_curve_d1 Wc_curve_d2 Wc_curve_d3
thm T3rad_def T3rad_slot_perp_zero
thm Wc_slot_perp_zero T1rad_slot_perp_zero T2rad_slot_perp_zero

end
