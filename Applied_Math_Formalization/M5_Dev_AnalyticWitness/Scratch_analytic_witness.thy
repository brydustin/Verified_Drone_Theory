theory Scratch_analytic_witness
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  The layer-4b INTERFACE --- the transversality witness
  isolated as one hypothesis --- was drafted and verified here, then spliced verbatim
  into \<open>D34_Analytic_Bridge.thy\<close>: \<open>dip_critical_chart_nowhere_dense\<close> upgrades the chart
  engine's dichotomy to an UNCONDITIONAL thin conclusion, under the single premise
  \<open>wit\<close> (a witness point on every connected real-analytic critical chart through the
  bad basepoint with nonvanishing steered wavevector).  \<open>wit\<close> is the layer-4b
  obligation, playing exactly the role \<open>nd\<close> plays in the two Robust3 sorries; its
  mathematical content is the paper's Case-B appendix (branch decomposition over a
  good triple in c-adapted coordinates, tex app:caseB, cor:caseBmeager).
  The check below guards the interface.\<close>

thm dip_critical_chart_nowhere_dense

end
