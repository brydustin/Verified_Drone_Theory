theory Scratch_analytic_ift
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  Layer 3 of the D34 analytic bridge --- the analytic
  IFT chart engine --- was drafted and verified here with \<open>eval_at\<close> (green on the first
  full pass), then spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>:
  \<^enum> \<open>real_analytic_at_1d_deriv\<close> / \<open>real_analytic_on_deriv_1d\<close>: the derivative of a
    1-D real-analytic function is real-analytic (holomorphic extension +
    \<open>holomorphic_deriv\<close>; the extension's derivative is real on the real axis by
    \<open>has_derivative_unique\<close> against the constant-zero imaginary part);
  \<^enum> \<open>real_analytic_on_cnj\<close> / \<open>real_analytic_on_cmod_sq\<close> closure;
  \<^enum> \<open>real_analytic_on_deriv_gdip\<close>, \<open>DERIV_gdip\<close>, \<open>frechet_gdip_eq\<close> (the gain jet);
  \<^enum> \<open>real_analytic_on_A_cart_dip\<close>, \<open>real_analytic_on_Dcvec_dip_applied\<close>,
    \<open>real_analytic_on_dA_cart_dip\<close>, and \<^bold>\<open>real_analytic_on_gradU_dip\<close> --- the dipole
    gradient field is real-analytic JOINTLY in \<open>(x,\<omega>)\<close>, via @{thm gradU_explicit}
    at the concrete jets @{thm has_derivative_cvec_dip} + @{thm gain_dip_has_derivative};
  \<^enum> \<open>bij_matrix_vector_mult\<close> (\<open>det \<noteq> 0 \<Longrightarrow> bij\<close>), and
  \<^enum> \<^bold>\<open>dip_critical_graph_dichotomy\<close>: at \<open>gradU = 0 \<and> det HessU \<noteq> 0\<close>, a connected open
    chart \<open>B \<ni> x0\<close> carries a real-analytic critical graph \<open>g\<close> with \<open>gradU x (g x) = 0\<close>
    on \<open>B\<close>, and \<open>{x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}\<close> is either ALL of \<open>B\<close>
    (what the transversality witness must exclude) or has closure with empty interior.
  The checks below guard the interface.\<close>

thm real_analytic_at_1d_deriv real_analytic_on_deriv_1d
thm real_analytic_on_cnj real_analytic_on_cmod_sq
thm real_analytic_on_deriv_gdip DERIV_gdip frechet_gdip_eq
thm real_analytic_on_A_cart_dip real_analytic_on_dA_cart_dip
thm real_analytic_on_gradU_dip
thm bij_matrix_vector_mult
thm dip_critical_graph_dichotomy

end
