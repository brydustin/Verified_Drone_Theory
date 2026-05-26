theory Parametric_Transversality_Euclidean_Base
  imports
    "HOL-Analysis.Analysis"
begin

text \<open>
  Reusable Euclidean infrastructure for the paper's "parametric transversality"
  steps:

  * Regular value hypothesis for a joint map \<open>G : V\<times>\<Omega> \<to> \<real>^k\<close>.
  * Regular value theorem (implicit-function-theorem based): the preimage
    \<open>{(x,\<omega>). G(x,\<omega>) = 0}\<close> admits a countable smooth chart cover.
  * Sard on the projection from that regular level set to the parameter space.

  Isabelle/HOL (as shipped) provides Sard in the form of @{thm baby_Sard}. What is
  missing is a convenient packaged regular-value / submanifold development. We
  therefore record the pipeline here as a single theorem with one central
  \<open>sorry\<close>, and we will later refine it by proving the intermediate lemmas.
\<close>

subsection \<open>Regular Value Predicate\<close>

definition regular_value_on ::
  "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
where
  "regular_value_on f S y \<longleftrightarrow>
     (\<forall>x\<in>S. f x = y \<longrightarrow> (\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f'))"

lemma regular_value_onI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = y \<Longrightarrow> (\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f')"
  shows "regular_value_on f S y"
  using assms unfolding regular_value_on_def by blast


subsection \<open>Complex as \<open>real^2\<close> (for Sard)\<close>

definition cplx_r2 :: "complex \<Rightarrow> real^2"
where
  "cplx_r2 z = (vector [Re z, Im z] :: real^2)"

lemma vector2_add:
  "(vector [a + b, c + d] :: real^2) = vector [a, c] + vector [b, d]"
  by (simp add: vec_eq_iff forall_2 algebra_simps)

lemma vector2_scaleR:
  "(vector [r * a, r * c] :: real^2) = r *\<^sub>R vector [a, c]"
  by (simp add: vec_eq_iff forall_2)

lemma cplx_r2_eq_iff [simp]: "cplx_r2 z = cplx_r2 w \<longleftrightarrow> z = w"
proof
  assume h: "cplx_r2 z = cplx_r2 w"
  have "Re z = Re w"
  proof -
    have "(cplx_r2 z) $ 1 = (cplx_r2 w) $ 1"
      using h by simp
    then show ?thesis
      by (simp add: cplx_r2_def)
  qed
  moreover have "Im z = Im w"
  proof -
    have "(cplx_r2 z) $ 2 = (cplx_r2 w) $ 2"
      using h by simp
    then show ?thesis
      by (simp add: cplx_r2_def)
  qed
  ultimately show "z = w"
    by (simp add: complex_eq_iff)
next
  assume "z = w"
  then show "cplx_r2 z = cplx_r2 w" by simp
qed

lemma cplx_r2_0_iff [simp]: "cplx_r2 z = 0 \<longleftrightarrow> z = 0"
proof
  assume "cplx_r2 z = 0"
  then have hz: "vector [Re z, Im z] = (0::real^2)"
    by (simp add: cplx_r2_def)
  have "Re z = 0"
  proof -
    have "(vector [Re z, Im z] :: real^2) $ 1 = (0::real^2) $ 1"
      by (rule arg_cong[OF hz])
    then show ?thesis by simp
  qed
  moreover have "Im z = 0"
  proof -
    have "(vector [Re z, Im z] :: real^2) $ 2 = (0::real^2) $ 2"
      by (rule arg_cong[OF hz])
    then show ?thesis by simp
  qed
  ultimately show "z = 0"
    by (simp add: complex_eq_iff)
next
  assume "z = 0"
  then show "cplx_r2 z = 0"
    by (simp add: cplx_r2_def vec_eq_iff forall_2)
qed

lemma bounded_linear_cplx_r2: "bounded_linear cplx_r2"
proof (rule bounded_linear_intro[where K=2])
  fix x y
  show "cplx_r2 (x + y) = cplx_r2 x + cplx_r2 y"
    unfolding cplx_r2_def by (simp add: vector2_add)
  fix r x
  show "cplx_r2 (r *\<^sub>R x) = r *\<^sub>R cplx_r2 x"
    unfolding cplx_r2_def by (simp add: vector2_scaleR)
  fix x
  show "norm (cplx_r2 x) \<le> cmod x * 2"
  proof -
    have "norm (cplx_r2 x) \<le> (\<Sum>i\<in>UNIV. \<bar>(cplx_r2 x) $ i\<bar>)"
      by (rule norm_le_l1_cart)
    also have "\<dots> = norm (Re x) + norm (Im x)"
      unfolding cplx_r2_def by (simp add: sum_2)
    also have "\<dots> \<le> norm x + norm x"
      by (intro add_mono, simp_all add: abs_Re_le_cmod abs_Im_le_cmod)
    finally show ?thesis
      by linarith
  qed
qed

lemma has_derivative_cplx_r2 [derivative_intros]:
  fixes z :: complex
  shows "(cplx_r2 has_derivative cplx_r2) (at z)"
  by (simp only: bounded_linear_cplx_r2 bounded_linear_imp_has_derivative)

lemma surj_cplx_r2: "surj cplx_r2"
proof -
  have "\<And>v::real^2. cplx_r2 (Complex (v$1) (v$2)) = v"
    unfolding cplx_r2_def by (simp add: vec_eq_iff forall_2)
  then show ?thesis
    by (intro surjI[where f = "\<lambda>v::real^2. Complex (v$1) (v$2)"]) auto
qed


subsection \<open>Parametric Sard/Transversality (Euclidean Pipeline)\<close>

theorem parametric_transversality_negligible_stub:
  fixes V :: "(real^'m::finite) set"
    and \<Omega> :: "(real^'n::finite) set"
    and G :: "((real^'m) \<times> (real^'n)) \<Rightarrow> (real^'k::finite)"
  assumes "open V" "V \<noteq> {}"
    and "open \<Omega>"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "negligible {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
                 (\<not> (\<exists>D. ((\<lambda>u. G (x,u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D))}"
  sorry

theorem parametric_transversality_meager_euclidean_stub:
  fixes V :: "(real^'m::finite) set"
    and \<Omega> :: "(real^'n::finite) set"
    and G :: "((real^'m) \<times> (real^'n)) \<Rightarrow> (real^'k::finite)"
  assumes "open V" "V \<noteq> {}"
    and "open \<Omega>"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "meager {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
                 (\<not> (\<exists>D. ((\<lambda>u. G (x,u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D))}"
  sorry

end
