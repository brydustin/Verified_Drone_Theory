theory Scratch_D3ArcCount
  imports "Applied_Math_M5_H0coreArc.Scratch_H0coreArc"
begin

section \<open>The D3 capstone input, reduced to a single explicit hypothesis\<close>

text \<open>
  This leaf assembles the whole D3 side of the Robust4 capstone at the design
  point \<open>\<omega>\<^sub>0 = (\<pi>/2, 0)\<close>, \<open>\<omega>\<^sub>s = 0\<close>, \<open>\<delta> = \<pi>/4\<close> down to one clearly-stated
  hypothesis.  Every other ingredient is already proven, \<open>sorry\<close>-free, upstream:

    \<^item> the fixed-angle chart core at every regular angle
      (\<open>fixed_omega_H0core_chart_core_of_generic_conditions\<close>, via the
      \<open>d3_s1\<close>/\<open>d3_s2\<close> global-factor split);
    \<^item> the countable-cover glue
      (\<open>H0coreArc_chart_core_all_robust4_of_countable_bad_angle_sets\<close>);
    \<^item> the Robust4 \<open>w\<^sub>1\<close>-strip \<open>OmegaPF (\<pi>/2,0) (\<pi>/4) \<subseteq> {0 < \<omega>\<^sub>1 < \<pi>}\<close>.

  This theory itself is entirely \<open>sorry\<close>-free: the one remaining geometric-measure
  fact is carried as an \<^emph>\<open>explicit hypothesis\<close>, exactly as the final theorem
  \<open>F0_dip_nonempty\<close> carries its \<open>d3core\<close> and \<open>branchcore\<close> inputs as assumptions.

  Recall (\<open>Nonemptiness_Robust1\<close>) that \<open>HessU = \<nabla>\<^sup>2\<^sub>\<omega> U\<close> and \<open>gradU = \<nabla>\<^sub>\<omega> U\<close> are the
  Hessian / gradient in the 2-D steering angle \<open>\<omega>\<close>; the configuration \<open>x\<close> is a
  parameter.  A configuration is ``bad at \<open>\<omega>\<close>'' (\<open>D3BadXG_H0core\<close>) when \<open>\<omega>\<close> is a
  degenerate critical point of \<open>\<omega> \<mapsto> U(x,\<omega>)\<close> (\<open>\<nabla>\<^sub>\<omega> U = 0\<close>, \<open>det \<nabla>\<^sup>2\<^sub>\<omega> U = 0\<close>) that
  is moreover not transversally unfolded by moving \<open>x\<close> (\<open>\<not> surj (\<partial>\<^sub>x \<nabla>\<^sub>\<omega> U)\<close>,
  \<open>\<not> surj DM_paper_x\<close>).
\<close>


subsection \<open>Fully proven: if bad fibres are empty, D3 closes with no countability\<close>

text \<open>
  The cleanest possible outcome (route ``P0'').  If, on the whole box, no
  configuration in \<open>V\<close> is bad at any angle, then the bad-angle set of every arc
  is empty and the countable-cover glue applies with the trivial cover.  This
  needs no zero-set / countability machinery at all.  It is the target a
  numerical check would aim to justify --- show \<open>\<partial>\<^sub>x \<nabla>\<^sub>\<omega> U\<close> is always onto \<open>\<real>\<^sup>2\<close> at
  \<open>\<omega>\<close>-critical configurations --- though for the odd \<open>N \<ge> 6\<close> of the capstone the
  bad set is expected \<open>0\<close>-dimensional (isolated), not empty, so in general the
  hypothesis of the next subsection is the operative one.
\<close>

lemma H0coreArc_bad_angles_empty_of_empty_fibres:
  fixes V :: "((real^2)^'n::finite) set"
  assumes empty: "\<And>\<omega>. \<omega> \<in> \<gamma> \<Longrightarrow>
      (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set) = {}"
  shows "H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> = {}"
proof -
  have "\<omega> \<notin> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>" for \<omega>
  proof
    assume "\<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>"
    then have wg: "\<omega> \<in> \<gamma>"
      and ex: "\<exists>x\<in>V. x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}"
      unfolding H0coreArc_bad_angles_def by auto
    from ex obtain x where "x \<in> V" and "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}"
      by blast
    with empty[OF wg] show False by blast
  qed
  thus ?thesis by auto
qed

theorem d3_capstone_input_robust4_of_empty_bad_fibres:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and empty: "\<And>\<omega>. \<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      (V \<inter> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {\<omega>}
        :: ((real^2)^'n) set) = {}"
  shows "d3_detHess_arc_chart_core_all V (vector [pi / 2, 0]) (pi / 4)
      (vector [pi / 2, 0]) (vector [0, 0])"
proof (rule H0coreArc_chart_core_all_robust4_of_countable_bad_angle_sets[OF card2])
  fix \<gamma> :: "(real^2) set"
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
  have empt: "H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma> = {}"
    by (rule H0coreArc_bad_angles_empty_of_empty_fibres)
       (use empty gsub in blast)
  show "countable
      (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>)"
    by (simp add: empt Top1_Ch3.countable_def inj_on_def)
qed


subsection \<open>The general capstone input, on one explicit countability hypothesis\<close>

text \<open>
  \<^bold>\<open>The one open obligation, made honest.\<close>  Rather than leave a \<open>sorry\<close>, the
  remaining fact --- that on each analytic arc through the box only countably
  many angles carry a bad configuration --- is exposed as an \<^emph>\<open>explicit
  hypothesis\<close> \<open>countable_bad\<close> of the capstone-input theorem, precisely as the
  final theorem \<open>F0_dip_nonempty\<close> exposes its \<open>d3core\<close> / \<open>branchcore\<close> inputs as
  assumptions.  The whole leaf is therefore \<open>sorry\<close>-free: everything is proven
  \<^emph>\<open>modulo\<close> this one visible, precisely-stated assumption.

  Why the hypothesis is expected to hold: cutting out the bad set
  \<open>\<B> \<subseteq> (x,\<omega>)\<close>-space (dimension \<open>2n+2\<close>) by \<open>\<nabla>\<^sub>\<omega> U = 0\<close> (2 equations),
  \<open>det \<nabla>\<^sup>2\<^sub>\<omega> U = 0\<close> (1), and the rank-deficient unfolding \<open>\<not> surj (\<partial>\<^sub>x \<nabla>\<^sub>\<omega> U)\<close>
  (\<open>2n\<^bold>-1\<close>) is codimension \<open>2n+2\<close> \<^emph>\<open>full\<close>: \<open>\<B>\<close> is generically \<open>0\<close>-dimensional, so
  its projection to a fixed arc is discrete/countable.  Countability is thus the
  generic truth; failure would need a non-generic family holding degeneracy
  \<^emph>\<open>and\<close> rank-1 unfolding across an arc-interval.

  Why it is an assumption, not a lemma: the statement carries an \<open>\<exists>x \<in> V\<close> over
  positive-dimensional, non-compact configuration space, so the 1-D
  ``analytic \<Longrightarrow> isolated zeros'' route does not apply directly --- there is no
  single analytic function of the arc parameter alone whose zeros contain the
  bad angles without first eliminating \<open>x\<close>, and on this box every angle is
  regular, so there is no \<open>\<omega>\<close>-only discriminant.  Discharging it needs the
  parametric-transversality / subanalytic-projection bridge (a ``countable
  critical values'' theorem) not yet in the library --- the same class of
  geometric-measure input the D4 Branch-P side also still assumes.  This is the
  paper's documented open D3 input.
\<close>

theorem d3_capstone_input_robust4:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and countable_bad: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow>
        \<gamma> \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
        countable
          (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>)"
  shows "d3_detHess_arc_chart_core_all V (vector [pi / 2, 0]) (pi / 4)
      (vector [pi / 2, 0]) (vector [0, 0])"
  by (rule H0coreArc_chart_core_all_robust4_of_countable_bad_angle_sets
        [OF card2 countable_bad])

end
