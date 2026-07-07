theory Scratch_cadapt
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  Layer 4b step 1 (transport entry point) --- the
  concrete c-adapted matrix \<open>cadapt c\<close> (columns \<open>c/|c|\<^sup>2\<close> and \<open>c\<^sup>\<perp>\<close>) with
  \<open>transpose (cadapt c) *v c = c0_paper\<close> and \<open>det (cadapt c) = 1\<close> --- verified here
  and spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>.  This is the witness matrix
  the \<open>applyT\<close> moment-transport laws quantify over.  Still open in step 1: migrate
  the \<open>M12_moment_applyT\<close>/\<open>M_paper_applyT\<close> laws (Robust3:5/99) into bridge scope.
  Checks below guard the interface.\<close>

thm cadapt_def cadapt_transport cadapt_det cadapt_invertible

end
