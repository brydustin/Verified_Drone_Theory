theory Scratch_H12zero
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-08).  The H12=0,H22\<noteq>0 branch (prop:H12zero/cor:H12zero)
  --- verified here and spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>, WITH ONE
  EXPLICIT, NAMED, UNVERIFIED HYPOTHESIS carried rather than silently assumed.

  BACKGROUND: prop:H12zero's determinant needs \<open>H\<^sub>1\<^sub>1\<close> independent of every v-slot,
  mirroring \<open>\<Phi>\<^sub>1\<close>'s v-independence claim from \<open>cor:vpair11\<close> --- which does NOT hold
  automatically in our angular omega coordinates (that's exactly what \<open>Phi_par\<close>/\<open>e_par\<close>
  fixed, at the FIRST-derivative level).  Tried the SAME fix at the SECOND-derivative
  (Hessian) level: \<open>H_par\<close>, contracting BOTH Hessian indices with \<open>e_par\<close> instead of
  \<open>axis 1 1\<close>.  Tracing @{thm HessU_dip_entry_perp_slot_value} through this contraction,
  most terms collapse the same clean way \<open>Phi_par\<close>'s did --- but a residual term from
  \<open>D2cvec_dip(e_par)(e_par)\<close> does NOT obviously vanish.  A differential-geometry
  argument (cvec_dip is a fixed linear projection, with a nonzero constant beam-steering
  shift, of a point on the unit sphere; the classical Gauss equation for the sphere's
  ambient Hessian splits into a tangential part plus a part along the position vector,
  and the constant shift breaks the clean "parallel to c" conclusion) suggests this
  residual is genuinely nonzero in general --- but this is NOT a formally checked proof
  either way, just a considered reason for doubt.  See the diary entry "cor:H12zero
  investigation: a genuine obstacle, not a quick brick" for the full reasoning.

  RATHER THAN silently assume the residual vanishes (or block on resolving it), this
  file carries it as an EXPLICIT, NAMED hypothesis
  (\<open>h_par_vslot_zero\<close>) on the two final theorems, so what IS proven is honest:
  \<^enum> \<open>H_par\<close> + \<^bold>\<open>has_derivative_H_par_x\<close> + \<^bold>\<open>H_par_slot_value\<close>: fully proven,
    unconditionally, for ANY slot direction (mechanical composition of
    @{thm has_derivative_HessU_dip_entry_x} at all four \<open>(k,l)\<close> pairs weighted by
    \<open>e_par\<close> --- GOTCHA: naive repeated \<open>rule has_derivative_add has_derivative_mult
    has_derivative_const ...\<close> does NOT chain correctly for a 4-term sum; needed
    explicit nested \<open>has_derivative_add[OF has_derivative_add[OF ...] ...]\<close> plus
    \<open>has_derivative_eq_rhs\<close> wrapping each product term, mirroring the \<open>h12sq\<close> pattern
    from the G11 session);
  \<^enum> \<^bold>\<open>Phi_par_uslot_value\<close> / \<^bold>\<open>Phi2_uslot_value\<close>: fully proven, unconditionally ---
    these did NOT need any new "general slot" derivation at all: the existing
    @{thm has_derivative_gradU_inner_x} / @{thm has_derivative_gradU_dip_x_explicit}
    were ALREADY stated for an arbitrary direction \<open>h\<close> (not perp-restricted), so the
    u-slot (parallel, \<open>slot j (cvec_dip \<omega>0 \<omega>s \<omega>)\<close>) values fall out of the SAME
    machinery used for the v-slot ones, just kept PACKAGED (raw \<open>dEjm\<close> form) rather
    than simplified;
  \<^enum> \<open>Lambda_ij\<close> (\<open>:= det \<partial>(Phi_par,H_par)/\<partial>(u_i,u_j)\<close>), \<open>Jac3_H12zero\<close> (the 3x3
    block-triangular determinant via the existing \<open>det3\<close>), and
    \<^bold>\<open>Jac3_H12zero_identity\<close>: fully proven, GIVEN \<open>h_par_vslot_zero\<close> --- the
    block-triangular collapse itself reuses \<open>Phi_par_perp_slot_zero\<close> (the (1,3) zero
    entry) exactly as in the H11/H22 sessions, no new derivation needed there;
  \<^enum> \<^bold>\<open>Jac3_H12zero_nonzero_criterion\<close>: the rank-3 conclusion, GIVEN
    \<open>h_par_vslot_zero\<close> plus the paper's own two hypotheses (\<open>s_k\<noteq>0\<close>,
    \<open>Lambda_ij\<noteq>0\<close>).

  STATUS: this is cor:H12zero conditional on \<open>h_par_vslot_zero\<close>.  NEXT: either (a)
  attempt the \<open>D2cvec_dip(e_par)(e_par) \<bullet> perp2(c)\<close> computation directly to settle
  whether it is actually zero, or (b) leave the hypothesis in place (matching this
  project's existing pattern of carrying genuine nondegeneracy conditions like
  \<open>det(Dcvec_dip)\<noteq>0\<close>) and move to layer-5 assembly once the OTHER Case-B branches are
  further along.  Checks below guard the interface.\<close>

thm H_par_def has_derivative_H_par_x
thm H_par_slot_value
thm Phi_par_uslot_value Phi2_uslot_value
thm Lambda_ij_def Jac3_H12zero_def
thm Jac3_H12zero_identity
thm Jac3_H12zero_nonzero_criterion

end
