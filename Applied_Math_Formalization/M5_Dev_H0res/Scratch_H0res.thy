theory Scratch_H0res
  imports "Applied_Math_D34_Analytic.D34_H0res_Branch"
begin

text \<open>CONSOLIDATED. See D34_H0res_Branch.thy for the full account: the elementary
  transversality fact for app:H0res's B1=B2=B3=0 branch, connected to the actual
  D34 (cvec_dip-based) configuration type. Checks below guard the interface.\<close>

thm beta_h0_def beta_h0_deriv_nonzero_at_zero has_derivative_beta_h0
thm ucoord_h0_def has_derivative_ucoord_h0_x ucoord_h0_slot_self ucoord_h0_uslot_deriv
thm B_dip_def has_derivative_B_dip_x
thm B_dip_uslot_transversal

end
