theory Scratch_hess_entry
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-08).  The Hessian-entry \<open>x\<close>-derivative assembly ---
  verified here and spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>:
  \<^enum> named block-derivative abbreviations \<open>dV_x\<close>/\<open>dgradcV_x\<close>/\<open>dHcmat_x\<close> repackaging
    the three proven block derivatives, plus their perp-slot values;
  \<^enum> \<open>has_derivative_gradcV_inner_x\<close>/\<open>has_derivative_Hcmat_bilinear_x\<close>: a FIXED
    vector (resp. pair of vectors) paired against the \<open>gradcV\<close>/\<open>Hcmat\<close> block --
    the linear-combination machinery @{thm HessU_dip_entry_moments} needs;
  \<^enum> \<^bold>\<open>has_derivative_HessU_dip_entry_x\<close>: the \<open>x\<close>-derivative (at FIXED \<open>\<omega>\<close>) of a
    single Hessian entry \<open>HessU(\<cdot>,\<omega>)$k$l\<close>, assembled from the three block
    derivatives through @{thm HessU_dip_entry_moments}'s linear combination
    (everything else in that identity --- \<open>Dcvec_dip\<close>, \<open>D2cvec_dip\<close>, \<open>gain_dip\<close>,
    the \<open>gdip\<close> jets --- is constant in \<open>x\<close>, since it depends only on \<open>\<omega>\<close>);
  \<^enum> \<^bold>\<open>HessU_dip_entry_perp_slot_value\<close>: that derivative's VALUE at a
    perpendicular slot direction (via \<open>frechet_derivative_at\<close> + \<open>fun_cong\<close>) ---
    the input the Case-B branch certificates (\<open>prop:vpair11\<close> et al.)
    differentiate directly.
  GOTCHAS: \<open>define\<close> introduces a genuine local constant, so a fact proven with
  \<open>define c where "c = ..."\<close>-abbreviated names does NOT syntactically match a
  goal stated in the unabbreviated (long) form even though they are
  propositionally equal --- unfolding the \<open>_def\<close> on the GOAL and on the FACT
  diverge.  Wrote everything in full long form instead (verbose but safe).
  Bare \<open>HessU (...) $ k $ l\<close> in a \<open>frechet_derivative (\<lambda>y. ...)\<close> argument can hit
  the \<open>fps_nth\<close>/\<open>vec_nth\<close> \<open>$\<close>-ambiguity even where the SAME pattern parsed fine as
  a \<open>has_derivative\<close> LHS --- spell \<open>vec_nth\<close> explicitly to be safe.  A \<open>fixes m ::
  'n\<close> used with \<open>slot\<close> needs the explicit \<open>'n::finite\<close> sort.  Checks below guard
  the interface.\<close>

thm dV_x_def dgradcV_x_def dHcmat_x_def
thm dV_x_perp dgradcV_x_perp dHcmat_x_perp
thm has_derivative_gradcV_inner_x has_derivative_Hcmat_bilinear_x
thm has_derivative_HessU_dip_entry_x
thm HessU_dip_entry_perp_slot_value

end
