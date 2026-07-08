theory Scratch_g11
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-08).  The G11 quotient-rule derivative and the Delta_ij
  determinant identity (\<open>prop:vpair11\<close>) --- verified here and spliced verbatim into
  \<open>D34_Analytic_Bridge.thy\<close>:
  \<^enum> \<open>Phi2_perp_slot_value\<close>: the perp-slot value of \<open>gradU\<close>'s component 2
    (\<open>\<Phi>\<^sub>2\<close>), in clean closed form, via \<open>bounded_linear.has_derivative\<close> composed
    with @{thm has_derivative_gradU_dip_x_explicit} + \<open>frechet_derivative_at\<close> +
    \<open>fun_cong\<close>, matched against @{thm gradU_dip_xderiv_perp_slot} via \<open>arg_cong\<close>
    (extracting the \<open>j=2\<close> component of that vector identity);
  \<^enum> \<open>G11\<close> (\<open>= H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2/H\<^sub>1\<^sub>1\<close>) and \<^bold>\<open>has_derivative_G11_x\<close>: the quotient-rule
    \<open>x\<close>-derivative (fixed \<open>\<omega>\<close>, assuming \<open>H\<^sub>1\<^sub>1 \<noteq> 0\<close>), built from
    @{thm has_derivative_HessU_dip_entry_x} at \<open>(2,2)/(1,2)/(1,1)\<close> via
    \<open>has_derivative_mult\<close>/\<open>has_derivative_divide'\<close>/\<open>has_derivative_diff\<close> ---
    expressed via \<open>frechet_derivative\<close> notation for the three Hessian entries
    (NOT hand-flattened, avoiding the transcription risk of a fabricated closed
    form: an earlier draft mistakenly copied \<open>\<Phi>\<^sub>2\<close>'s formula for \<open>H\<^sub>2\<^sub>2\<close>, caught
    before running anything --- they are unrelated quantities);
  \<^enum> \<^bold>\<open>G11_perp_slot_value\<close>: the value at a perpendicular slot, via
    \<open>frechet_derivative_at\<close> + \<open>fun_cong\<close> (mechanical, no algebra);
  \<^enum> \<open>Delta_ij\<close> (the \<open>prop:vpair11\<close> rank-3 Jacobian determinant, invariantly: the
    perpendicular slot direction for triple element \<open>i\<close> is \<open>slot i (perp2 c)\<close>) and
    \<^bold>\<open>Delta_ij_identity\<close>: the \<open>\<Phi>\<^sub>2\<close>-factors collapse to their closed form
    (\<open>Phi2_perp_slot_value\<close>); the \<open>G11\<close>-factors stay packaged (\<open>G11_perp_slot_value\<close>
    is available separately, on demand, rather than force-expanded here).
  Checks below guard the interface.\<close>

thm Phi2_perp_slot_value
thm G11_def has_derivative_G11_x
thm G11_perp_slot_value
thm Delta_ij_def Delta_ij_identity

end
