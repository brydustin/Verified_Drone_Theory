theory Scratch_ArcSplit
  imports "Applied_Math_D3_Wiring.D3_Chart_Wiring"
begin

section \<open>Splitting an arc's H0core fibre into interior + two endpoint fibres\<close>

text \<open>\<^bold>\<open>Scratch staging only.\<close>  \<open>D3BadXG_H0core\<close> distributes over a union of the
  parametrizing set exactly like \<open>D3BadXG\<close>/\<open>BadXGW\<close> already do (their \<open>_UN\<close>
  lemmas are pure set algebra).  For an arc \<open>\<gamma> = \<phi> ` {a..b}\<close> this lets us peel
  off the two ENDPOINTS \<open>\<phi> a\<close>, \<open>\<phi> b\<close> (each a single fixed-\<omega> fibre, already
  fully handled by the existing \<open>fixed_omega_H0core_chart_core_*\<close> machinery)
  and reduce the arc-bridge problem to the OPEN interior parametrization
  \<open>\<phi> ` {a<..<b}\<close>, where \<open>\<phi>\<close> behaves as a genuine two-sided \<open>C\<^sup>1\<close> function at
  every point (no boundary derivative subtleties).\<close>

lemma D3BadXG_H0core_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "D3BadXG_H0core \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)
          = (\<Union>i\<in>I. (D3BadXG_H0core \<omega>0 \<omega>s (arc i) :: ((real^2)^'n::finite) set))"
  unfolding D3BadXG_H0core_def by blast

lemma D3BadXG_H0core_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "D3BadXG_H0core \<omega>0 \<omega>s \<Gamma> \<subseteq> (D3BadXG_H0core \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n::finite) set)"
  using assms unfolding D3BadXG_H0core_def by blast

lemma D3BadXG_H0core_point:
  fixes \<omega> :: "real^2"
  shows "D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}
          = {x :: (real^2)^'n::finite.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  unfolding D3BadXG_H0core_def by blast

text \<open>The arc-interval split: \<open>\<phi> ` {a..b} = {\<phi> a} \<union> \<phi> ` {a<..<b} \<union> {\<phi> b}\<close>
  (as sets, when \<open>a \<le> b\<close>), so the H0core fibre over the whole closed arc is the
  union of the two endpoint fibres and the OPEN-interior fibre.\<close>

lemma closed_interval_eq_endpoints_union_open:
  fixes a b :: real
  assumes ab: "a \<le> b"
  shows "{a..b} = {a} \<union> {a<..<b} \<union> {b}"
  using ab by fastforce

lemma D3BadXG_H0core_arc_split:
  fixes \<phi> :: "real \<Rightarrow> real^2" and a b :: real
  assumes ab: "a \<le> b"
  shows "D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a..b})
       = (D3BadXG_H0core \<omega>0 \<omega>s {\<phi> a} :: ((real^2)^'n::finite) set)
         \<union> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b})
         \<union> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> b}"
proof -
  have "\<phi> ` {a..b} = \<phi> ` ({a} \<union> {a<..<b} \<union> {b})"
    using closed_interval_eq_endpoints_union_open[OF ab] by simp
  also have "\<dots> = \<phi> ` {a} \<union> \<phi> ` {a<..<b} \<union> \<phi> ` {b}"
    by (simp add: image_Un)
  finally have eq: "\<phi> ` {a..b} = {\<phi> a} \<union> \<phi> ` {a<..<b} \<union> {\<phi> b}"
    by simp
  show ?thesis
    unfolding eq D3BadXG_H0core_def by blast
qed

end
