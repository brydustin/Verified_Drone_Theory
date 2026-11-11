theory Scratch_ArcWiring
imports
  Applied_Math_M5_Wiring.Scratch_Wiring
  Applied_Math_M5_ArcBridge.Scratch_ArcBridge
begin

text \<open>Sketch.md \<section>5 step 4: wire the unconditional fixed-angle chart-core
  result @{thm fixed_omega_H0core_chart_core_robust4_all_angles} (proved in
  \<open>Scratch_Wiring.thy\<close>, zero side conditions beyond the angle range) into the
  \<open>left\<close>/\<open>right\<close> obligations of the arc-bridge capstone
  @{thm d3_chart_core_all_of_analytic_arc_pointwise_arc_schur_patches}
  (\<open>Scratch_ArcBridge.thy\<close>), at the concrete Robust4 design values
  \<open>\<omega>0 = (\<pi>/2,0)\<close>, \<open>\<omega>s = (0,0)\<close>, \<open>ctr = (\<pi>/2,0)\<close>, \<open>\<delta> = \<pi>/4\<close>.  This needs a
  session that sees both \<open>Applied_Math_M5_Wiring\<close> and
  \<open>Applied_Math_M5_ArcBridge\<close> at once -- previously deferred as a
  heap-merge risk while both were being edited live; both are stable now,
  so this is a fresh leaf session, not a rebuild of either.\<close>

lemma OmegaPF_robust4_theta_lo:
  fixes \<omega> :: "real^2"
  assumes "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
  shows "0 < vec_nth \<omega> 1"
proof -
  have bnd: "pi / 2 - pi / 4 \<le> vec_nth \<omega> 1"
    using OmegaPF_component_bounds[OF assms] by (simp add: vector_2)
  show ?thesis
    using bnd pi_gt_zero by linarith
qed

lemma OmegaPF_robust4_theta_hi:
  fixes \<omega> :: "real^2"
  assumes "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
  shows "vec_nth \<omega> 1 < pi"
proof -
  have bnd: "vec_nth \<omega> 1 \<le> pi / 2 + pi / 4"
    using OmegaPF_component_bounds[OF assms] by (simp add: vector_2)
  show ?thesis
    using bnd pi_gt_zero by linarith
qed

theorem d3_left_free_robust4:
  fixes V :: "((real^2)^'n::finite) set" and \<phi> :: "real \<Rightarrow> real^2"
  assumes ab: "a \<le> (b :: real)"
    and gsub: "\<phi> ` {a..b} \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) {\<phi> a}"
proof -
  have mem: "\<phi> a \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    using gsub ab by auto
  show ?thesis
    by (rule fixed_omega_H0core_chart_core_robust4_all_angles
        [OF OmegaPF_robust4_theta_lo[OF mem] OmegaPF_robust4_theta_hi[OF mem] card2])
qed

theorem d3_right_free_robust4:
  fixes V :: "((real^2)^'n::finite) set" and \<phi> :: "real \<Rightarrow> real^2"
  assumes ab: "a \<le> (b :: real)"
    and gsub: "\<phi> ` {a..b} \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) {\<phi> b}"
proof -
  have mem: "\<phi> b \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    using gsub ab by auto
  show ?thesis
    by (rule fixed_omega_H0core_chart_core_robust4_all_angles
        [OF OmegaPF_robust4_theta_lo[OF mem] OmegaPF_robust4_theta_hi[OF mem] card2])
qed

text \<open>Assembled form: the arc-bridge capstone at the Robust4 design values,
  with \<open>left\<close>/\<open>right\<close> now unconditionally discharged -- only \<open>trans\<close>/\<open>schur\<close>
  remain as genuine hypotheses.  This is the honest state-of-the-art D3
  obligation after Sketch.md \<section>5 step 4.\<close>

theorem d3_detHess_arc_chart_core_all_robust4_left_right_free:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and trans: "\<And>\<phi> D\<phi> a b q.
      a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {\<phi> (snd q)}} \<Longrightarrow>
      vec_nth (HessU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) gain_dip
        (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    and schur: "\<And>\<phi> D\<phi> a b q.
      a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {\<phi> (snd q)}} \<Longrightarrow>
      \<exists>r. arc_schur_L (vector [pi / 2, 0]) (vector [0, 0]) \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
  shows "d3_detHess_arc_chart_core_all V (vector [pi / 2, 0]) (pi / 4)
      (vector [pi / 2, 0]) (vector [0, 0])"
proof (rule d3_chart_core_all_of_analytic_arc_pointwise_arc_schur_patches)
  show "\<And>\<phi> a b. a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) {\<phi> a}"
    using d3_left_free_robust4[OF _ _ card2] by blast
  show "\<And>\<phi> a b. a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) {\<phi> b}"
    using d3_right_free_robust4[OF _ _ card2] by blast
  show "\<And>\<phi> D\<phi> a b q.
      a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {\<phi> (snd q)}} \<Longrightarrow>
      vec_nth (HessU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) gain_dip
        (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    by (rule trans)
  show "\<And>\<phi> D\<phi> a b q.
      a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {\<phi> (snd q)}} \<Longrightarrow>
      \<exists>r. arc_schur_L (vector [pi / 2, 0]) (vector [0, 0]) \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
    by (rule schur)
qed

end
