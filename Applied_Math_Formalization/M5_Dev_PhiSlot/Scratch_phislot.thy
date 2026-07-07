theory Scratch_phislot
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-07).  The first corrected-path derivative brick ---
  verified here and spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>: \<open>dEjm_zero1\<close>
  (the \<open>dEjm\<close> form on tangents with vanishing first slot),
  \<open>DM_paper_x_perp_slot_1/2/3\<close> (the moment tangent of a perpendicular slot),
  \<open>dEjm_perp_slot_value\<close>, and \<^bold>\<open>gradU_dip_xderiv_perp_slot\<close>: the \<open>x\<close>-derivative of
  the gradient field at FIXED \<open>\<omega>\<close> in a perpendicular slot direction, in invariant
  form \<open>\<partial>\<^bsub>slot m v\<^esub>\<Phi>\<^sub>j = 2g(\<gamma>\<^sub>j \<bullet> v) Im(cnj A \<cdot> \<phi>\<^sub>m)\<close> --- the paper's
  \<open>\<partial>\<^sub>v\<^sub>j\<Phi>\<^sub>2 = -2ag s\<^sub>j\<close> before gauge/frame specialisation, matching
  @{thm has_derivative_gradU_dip_x_explicit}'s derivative map exactly.
  Check below guards the interface.\<close>

thm dEjm_zero1 DM_paper_x_perp_slot_1 DM_paper_x_perp_slot_2 DM_paper_x_perp_slot_3
thm dEjm_perp_slot_value gradU_dip_xderiv_perp_slot

end
