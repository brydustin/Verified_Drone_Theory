theory Scratch_analytic_elem
  imports "Applied_Math_Analytic_Complex.Real_Analytic_Complex"
begin

text \<open>CONSOLIDATED (2026-07-06).  The elementary real-analytic function layer drafted
  here --- \<open>has_holo_extension_at_sin/cos/rsinc\<close>, \<open>real_analytic_on_sin/cos/rsinc\<close>
  (via the complexification bridge @{thm real_analytic_at_1d_iff_holo_extension} with
  the classical holomorphic witnesses, and \<open>removable_singularity\<close> for the entire
  \<open>sinc\<close> kernel), plus the composed forms \<open>real_analytic_on_sin_comp\<close> /
  \<open>_cos_comp\<close> / \<open>_rsinc_comp\<close> --- was verified with \<open>eval_at\<close> and spliced verbatim
  into \<open>Real_Analytic_Complex.thy\<close>.  It now resolves from the
  \<open>Applied_Math_Analytic_Complex\<close> heap; the checks below guard the interface.\<close>

thm real_analytic_on_sin real_analytic_on_cos real_analytic_on_rsinc
thm real_analytic_on_sin_comp real_analytic_on_cos_comp real_analytic_on_rsinc_comp
thm rsinc_def complex_sinc_holomorphic

end
