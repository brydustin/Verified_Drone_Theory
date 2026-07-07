theory Scratch_branch_scaffold
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-07).  The branch case scaffold --- verified here and
  spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>: \<open>real_analytic_on_HessU_entry_chart\<close>,
  \<open>HessU_entry_chart_shrink\<close> (the generic sub-chart shrink on a nonvanishing Hessian
  entry), and \<^bold>\<open>dip_wit_core_scaffold\<close>: \<open>wit_core\<close>'s conclusion follows from the THREE
  branch hypotheses \<open>brH11\<close>/\<open>brH22\<close>/\<open>brH12\<close> (full chart package + one Hessian entry
  nonvanishing along the chart), by the pointwise entry dichotomy from
  \<open>det H \<noteq> 0\<close> (\<open>det_2\<close>: all of \<open>H\<^sub>1\<^sub>1, H\<^sub>2\<^sub>2, H\<^sub>1\<^sub>2\<close> zero kills the determinant) and
  the shrink.  The three branch hypotheses are the exact standing hypotheses of the
  paper's Case-B branch families.  Checks below guard the interface.\<close>

thm real_analytic_on_HessU_entry_chart
thm HessU_entry_chart_shrink
thm dip_wit_core_scaffold

end
