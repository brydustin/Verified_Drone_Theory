theory Scratch_applyT_mig
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  Layer 4b step 1 (transport migration) --- the
  \<open>applyT\<close> bricks from the top of \<open>Nonemptiness_Robust3\<close> (\<open>M12_moment_applyT\<close>,
  \<open>M_paper_applyT\<close>, \<open>applyT_linear\<close>, \<open>applyT_surj\<close>) --- migrated into the bridge,
  with all statement/proof-level \<open>$\<close> rewritten to \<open>vec_nth\<close> (the verbatim \<open>$\<close> forms
  PARSE-HANG in the merged D34 heap: >10 min vs seconds --- the known super-linear
  \<open>$\<close>-overload cost, now measured) and the \<open>consider\<close>-\<open>metis\<close> replaced by
  \<open>exhaust_6[of i] by blast\<close>.  When Robust3 is rewired to import the bridge
  (layer 5), its local copies (L5--155, L322--341) are to be DELETED.
  With \<open>cadapt\<close> this completes the c-adapted transport entry point.
  Checks below guard the interface.\<close>

thm M12_moment_applyT M_paper_applyT
thm applyT_linear applyT_surj

end
