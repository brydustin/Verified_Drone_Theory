theory Scratch_g22
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-08).  The symmetric \<open>H22\<close> branch
  (\<open>prop:vpair22\<close>/\<open>cor:vpair22\<close>) --- verified here and spliced verbatim into
  \<open>D34_Analytic_Bridge.thy\<close>.  This mirrors \<open>prop:vpair11\<close>/\<open>cor:vpair11\<close> almost
  exactly: SAME \<open>\<Phi>2\<close> factor, SAME block-triangular argument with \<open>\<Phi>_par\<close>
  (independent of every v-slot, proven ONCE and reused verbatim, since it does
  NOT depend on the H11/H22 choice) --- only \<open>G11\<close> is replaced by
  \<open>G22 := H11 - H12\<^sup>2/H22\<close>.  All five theorems checked cleanly on the FIRST
  attempt by direct reuse of the H11-branch proof pattern (\<open>has_derivative_G22_x\<close>
  mirrors \<open>has_derivative_G11_x\<close>; \<open>Jac3_22\<close>/\<open>Jac3_22_identity\<close>/
  \<open>Jac3_22_nonzero_criterion\<close> mirror \<open>Jac3\<close>/\<open>Jac3_identity\<close>/
  \<open>Jac3_nonzero_criterion\<close>, with G11 replaced by G22 and H11\<noteq>0 replaced by
  H22\<noteq>0 throughout).
  \<^enum> \<open>G22\<close> + \<^bold>\<open>has_derivative_G22_x\<close> (quotient-rule \<open>x\<close>-derivative, \<open>H22\<noteq>0\<close>) +
    \<^bold>\<open>G22_perp_slot_value\<close>;
  \<^enum> \<open>Delta_ij_22\<close> (\<open>:= det \<partial>(\<Phi>2,G22)/\<partial>(v_i,v_j)\<close>) + \<^bold>\<open>Delta_ij_22_identity\<close>;
  \<^enum> \<open>Jac3_22\<close> + \<^bold>\<open>Jac3_22_identity\<close> (\<open>= D\<Phi>_par(U) * Delta_ij_22(i,j)\<close>) +
    \<^bold>\<open>Jac3_22_nonzero_criterion\<close> --- \<open>cor:vpair22\<close>'s rank-3 criterion, fully
    invariant.
  NOTE: this is the BARE rank-3 criterion (\<open>cor:vpair22\<close>), not yet the deeper
  \<open>cor:vpair22-full\<close> (which needs a real-analytic lifting argument with
  auxiliary variables, codimension counting in an EXTENDED space --- a
  genuinely different, larger piece of work, not yet attempted).
  Checks below guard the interface.\<close>

thm G22_def has_derivative_G22_x
thm G22_perp_slot_value
thm Delta_ij_22_def Delta_ij_22_identity
thm Jac3_22_def Jac3_22_identity
thm Jac3_22_nonzero_criterion

end
