theory Scratch_analytic_unique
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  Layer 4a of the D34 analytic bridge --- local
  uniqueness of the critical graph --- was drafted and verified here with \<open>eval_at\<close>,
  then spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>:
  \<^enum> \<open>real_analytic_implicit_function_unique\<close>: the analytic implicit function theorem
    additionally exposing the local-inverse neighbourhood \<open>N\<close> of \<open>(x0, y0)\<close> on which
    the solution graph is the ONLY zero locus (injectivity of the homeomorphism
    \<open>\<Phi>(x,y) = (x, F(x,y))\<close> via \<open>homeomorphism_apply1\<close>).  Mirrored verbatim from the
    @{thm real_analytic_implicit_function} assembly; upstream candidate for
    \<open>Real_Analytic_IFT\<close>.  GOTCHA: in the merged D34 heap the token \<open>inv\<close> is claimed by
    algebra structure syntax (\<open>m_inv\<close>) --- "Illegal reference to implicit structure";
    spell \<open>inv_into UNIV\<close> (definitionally identical, all \<open>inv\<close> lemmas still apply).
  \<^enum> \<open>dip_critical_graph_dichotomy_unique\<close>: the complete chart engine --- connected
    chart \<open>B\<close>, uniqueness neighbourhood \<open>N\<close>, real-analytic critical graph \<open>g\<close> with
    \<open>gradU x (g x) = 0\<close> and \<open>(x, g x) \<in> N\<close> on \<open>B\<close>, every critical \<open>(x,\<omega>) \<in> N\<close> over
    \<open>B\<close> lies ON the graph, and the mstarg-along-graph dichotomy (all-of-\<open>B\<close> or
    closure-with-empty-interior).
  The checks below guard the interface.\<close>

thm real_analytic_implicit_function_unique
thm dip_critical_graph_dichotomy_unique

end
