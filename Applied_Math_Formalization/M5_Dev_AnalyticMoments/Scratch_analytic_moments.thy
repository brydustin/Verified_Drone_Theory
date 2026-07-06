theory Scratch_analytic_moments
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  Layer 2 of the D34 analytic bridge --- the generic
  closure kit (\<open>real_analytic_on_inner/uminus/Re/Im/Complex/cmult/of_real/cis/
  scaleR_complex/det\<close> + \<open>matrix_gram_entry\<close>), the joint \<open>(c,x)\<close>-analyticity of
  \<open>phase\<close>/\<open>d_phase\<close>, the six moments, the six \<open>D*_paper_x\<close> Jacobian components, the
  \<open>transC\<close>-transported entry fields, and the Gram determinant \<open>mstarg\<close> (defined here,
  verbatim the Robust3 definition, to be the canonical copy once Robust3 imports the
  bridge) --- was drafted and verified here with \<open>eval_at\<close>, then spliced verbatim into
  \<open>D34_Analytic_Bridge.thy\<close>.  GOTCHAS recorded: in this merged heap \<open>$\<close> is parse-ambiguous
  (HMA's \<open>$h\<close>/\<open>$v\<close>) --- statements must spell \<open>vec_nth\<close>; \<open>finite_UNIV\<close> resolves to the
  Cardinality Phantom constant --- use the type-class fact \<open>finite\<close>; the unqualified
  \<open>DM_paper_x\<close> is \<open>Nonemptiness_Paper.DM_paper_x\<close> (components \<open>D*_paper_x\<close>), which
  shadows \<open>Moment_Map.DM_paper_x\<close> (components \<open>d_*_moment_x\<close>) --- \<open>mstarg\<close> is built
  from the former.  The checks below guard the interface.\<close>

thm real_analytic_on_inner real_analytic_on_cmult real_analytic_on_cis
thm real_analytic_on_det matrix_gram_entry
thm real_analytic_on_phase real_analytic_on_d_phase
thm real_analytic_on_A_moment real_analytic_on_M12_moment
thm real_analytic_on_DA_paper_x real_analytic_on_DM22_paper_x
thm real_analytic_on_transC_DM_entry linear_DM_paper_x
thm mstarg_def real_analytic_on_mstarg real_analytic_on_mstarg_x real_analytic_on_mstarg_cvec

end
