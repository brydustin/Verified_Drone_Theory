theory Scratch_Wiring
  imports "Applied_Math_D3_Wiring.D3_Chart_Wiring"
begin

text \<open>Guard-only: the wiring-layer content lives in
  \<open>Appendix/Wiring/D3_Chart_Wiring.thy\<close>.  This file re-checks the key names.\<close>

thm H0core_fibre_Phi_par_zero H0core_fibre_gradU2_zero detHess_zero_cases
thm tangential_projection_bounded_linear tangential_projection_not_surj
thm scalar_cut_id_within_derivative
thm chart_core_data_of_scalar_cuts

end
