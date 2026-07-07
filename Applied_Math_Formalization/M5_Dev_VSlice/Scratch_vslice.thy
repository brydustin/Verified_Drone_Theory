theory Scratch_vslice
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-07).  The H11-certificate ground layer --- the single-slot
  moment derivative calculus --- verified here and spliced verbatim into
  \<open>D34_Analytic_Bridge.thy\<close>: \<open>slot\<close>/\<open>perp2\<close> (+ \<open>_orth\<close>, \<open>_nz\<close>), the master law
  \<open>d_phase_slot\<close>, the six collapsed slot laws \<open>d_*_moment_x_slot\<close> (single surviving
  term per derivative), the six perpendicular corollaries \<open>d_*_moment_x_perp\<close>
  (\<open>c \<bullet> v = 0\<close>: the phase derivative dies, only the weight term survives --- the
  source of the paper's \<open>\<partial>\<^sub>v\<^sub>j\<close> formulas in \<open>prop:vpair11\<close>/\<open>prop:vblock\<close>), and the
  glue \<open>D*_paper_eq_d_moment\<close> identifying the two derivative-entry families.
  GOTCHA: a standalone assumption \<open>c \<bullet> v = 0\<close> is parse-ambiguous in the merged heap
  (JNF \<open>scalar_prod\<close>) --- pin with \<open>fixes c v :: "real^2"\<close>.
  Checks below guard the interface.\<close>

thm slot_nth perp2_orth perp2_nz
thm d_phase_slot
thm d_A_moment_x_slot d_M1_moment_x_slot d_M2_moment_x_slot
thm d_M11_moment_x_slot d_M12_moment_x_slot d_M22_moment_x_slot
thm d_A_moment_x_perp d_M1_moment_x_perp d_M2_moment_x_perp
thm d_M11_moment_x_perp d_M12_moment_x_perp d_M22_moment_x_perp
thm DA_paper_eq_d_moment DM1_paper_eq_d_moment DM2_paper_eq_d_moment
thm DM11_paper_eq_d_moment DM12_paper_eq_d_moment DM22_paper_eq_d_moment

end
