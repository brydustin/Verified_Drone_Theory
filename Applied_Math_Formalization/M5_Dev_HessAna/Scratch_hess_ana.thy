theory Scratch_hess_ana
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-07).  The \<open>wit_core\<close> substrate --- Hessian entry fields
  real-analytic --- verified here and spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>:
  \<^enum> helpers \<open>real_analytic_on_field_nth\<close>, \<open>inner_expand_vec\<close>, \<open>inner_mv_expand\<close>;
  \<^enum> \<open>Afun\<close>/\<open>Mcfun\<close>/\<open>M2cfun\<close> jointly analytic in \<open>(c,x)\<close>; \<open>Hcmat\<close> entries and the
    c-pattern gradient components (\<open>Hcmat_entry_eq\<close>, via @{thm gradU_c_field});
  \<^enum> the gain's second derivative: \<open>real_analytic_on_deriv2_gdip\<close>, \<open>DERIV_deriv_gdip\<close>,
    \<open>frechet_gdip2_eq\<close>; the second chart jet \<open>real_analytic_on_D2cvec_dip_applied\<close>;
  \<^enum> \<^bold>\<open>real_analytic_on_HessU_dip_entry\<close> (each \<open>(k,l)\<close> entry of \<open>HessU\<close> jointly
    analytic in \<open>(x,\<omega>)\<close>, assembled through @{thm HessU_dip_entry_moments}),
    \<^bold>\<open>real_analytic_on_detHessU_dip\<close> (via \<open>det_2\<close>), and the chart-composed
    \<open>real_analytic_on_detHessU_chart\<close> --- the field the \<open>det HessU \<noteq> 0\<close> continuity
    shrink and the branch certificates consume.
  Checks below guard the interface.\<close>

thm real_analytic_on_field_nth inner_expand_vec inner_mv_expand
thm real_analytic_on_Afun_cx real_analytic_on_Mcfun_cx real_analytic_on_M2cfun_cx
thm Hcmat_entry_eq real_analytic_on_Hcmat_entry_cx real_analytic_on_gradUc_comp_cx
thm real_analytic_on_deriv2_gdip DERIV_deriv_gdip frechet_gdip2_eq
thm real_analytic_on_D2cvec_dip_applied
thm real_analytic_on_HessU_dip_entry real_analytic_on_detHessU_dip
thm real_analytic_on_detHessU_chart

end
