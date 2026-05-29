theory Sard_Negligible
  imports "HOL-Analysis.Analysis"
begin

text \<open>Foundational pieces for the (real^2)^'n \<cong> real^('n bit0) transport.\<close>

lemma card_n2_bit0:
  "card (UNIV :: ('n::finite \<times> 2) set) = card (UNIV :: ('n bit0) set)"
  by simp

lemma exists_index_bij:
  "\<exists>\<beta> :: 'n::finite bit0 \<Rightarrow> ('n \<times> 2). bij \<beta>"
proof -
  have "card (UNIV :: ('n bit0) set) = card (UNIV :: ('n \<times> 2) set)"
    by (simp add: card_n2_bit0)
  then show ?thesis
    by (metis finite_same_card_bij finite_class.finite_UNIV)
qed

lemma negligible_singular_image_2n:
  fixes f :: "(real^2)^'n \<Rightarrow> (real^2)^'n"
    and f' :: "(real^2)^'n \<Rightarrow> ((real^2)^'n \<Rightarrow> (real^2)^'n)"
  assumes der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and ns:  "\<And>x. x \<in> S \<Longrightarrow> \<not> surj (f' x)"
  shows "negligible (f ` S)"
proof -
  obtain \<beta> :: "'n bit0 \<Rightarrow> ('n \<times> 2)" where b: "bij \<beta>"
    using exists_index_bij by blast
  define \<gamma> where "\<gamma> = inv \<beta>"
  have bg: "bij \<gamma>" unfolding \<gamma>_def by (simp add: b bij_imp_bij_inv)
  have g\<beta>: "\<gamma> (\<beta> k) = k" for k unfolding \<gamma>_def
    by (metis b bij_inv_eq_iff) 
  have \<beta>g: "\<beta> (\<gamma> p) = p" for p unfolding \<gamma>_def by (meson b bij_inv_eq_iff)

  define \<Phi> :: "(real^2)^'n \<Rightarrow> real^('n bit0)"
    where "\<Phi> v = (\<chi> k. (v $ fst (\<beta> k)) $ snd (\<beta> k))" for v
  define \<Psi> :: "real^('n bit0) \<Rightarrow> (real^2)^'n"
    where "\<Psi> w = (\<chi> i. \<chi> j. w $ \<gamma> (i,j))" for w

  have lin\<Phi>: "linear \<Phi>"
    by (rule linearI) (auto simp: \<Phi>_def vec_eq_iff)
  have lin\<Psi>: "linear \<Psi>"
    by (rule linearI) (auto simp: \<Psi>_def vec_eq_iff)

  have \<Psi>\<Phi>: "\<Psi> (\<Phi> v) = v" for v
    by (simp add: \<Phi>_def \<Psi>_def vec_eq_iff \<beta>g)
  have \<Phi>\<Psi>: "\<Phi> (\<Psi> w) = w" for w
    by (simp add: \<Phi>_def \<Psi>_def vec_eq_iff g\<beta>)

    define h :: "real^('n bit0) \<Rightarrow> real^('n bit0)"
    where "h = (\<lambda>y. \<Phi> (f (\<Psi> y)))"

  have der_h:
    "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow>
      (h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
  proof -
    fix y assume yS: "y \<in> \<Phi> ` S"
    have \<Psi>yS: "\<Psi> y \<in> S"
      using yS \<Psi>\<Phi> by auto

    have d\<Psi>: "(\<Psi> has_derivative \<Psi>) (at y within \<Phi> ` S)"
      using lin\<Psi> by (simp add: linear_imp_has_derivative)

    have df:
      "(f has_derivative f' (\<Psi> y)) (at (\<Psi> y) within \<Psi> ` (\<Phi> ` S))"
      by (metis (mono_tags, lifting) \<Psi>\<Phi> \<Psi>yS der has_derivative_subset image_iff image_subsetI)

    have d_f\<Psi>:
      "((\<lambda>y. f (\<Psi> y)) has_derivative (\<lambda>z. f' (\<Psi> y) (\<Psi> z)))
        (at y within \<Phi> ` S)"
      by (simp add: df has_derivative_in_compose lin\<Psi> linear_imp_has_derivative)
 

    have d\<Phi>:
      "(\<Phi> has_derivative \<Phi>)
        (at (f (\<Psi> y)) within (\<lambda>y. f (\<Psi> y)) ` (\<Phi> ` S))"
      using lin\<Phi> by (simp add: linear_imp_has_derivative)

    show "(h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
      unfolding h_def
      using has_derivative_in_compose[OF d_f\<Psi> d\<Phi>] by simp
  qed

  have ns_h:
    "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow> \<not> surj (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"
  proof
    fix y assume yS: "y \<in> \<Phi> ` S"
    assume sur: "surj (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"

    have \<Psi>yS: "\<Psi> y \<in> S"
      using yS \<Psi>\<Phi> by auto

    have "surj (f' (\<Psi> y))"
      unfolding surj_def
    proof clarify
      fix u :: "(real^2)^'n"
      from sur obtain z where z:
        "\<Phi> (f' (\<Psi> y) (\<Psi> z)) = \<Phi> u"
        by (metis (mono_tags, lifting) surj_def)

      show "\<exists>x. u = f' (\<Psi> y) x"
      proof (intro exI[where x = "\<Psi> z"])
        have "\<Psi> (\<Phi> (f' (\<Psi> y) (\<Psi> z))) = \<Psi> (\<Phi> u)"
          using z by simp
        then show "u = f' (\<Psi> y) (\<Psi> z)"
          by (simp add: \<Psi>\<Phi>)
      qed
    qed

    then show False
      using ns[OF \<Psi>yS] by contradiction
  qed

  have neg_h: "negligible (h ` (\<Phi> ` S))"
  proof (rule baby_Sard[where f = h and S = "\<Phi> ` S"
            and f' = "\<lambda>y z. \<Phi> (f' (\<Psi> y) (\<Psi> z))"])
    show "CARD('n bit0) \<le> CARD('n bit0)" by simp
    show "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow>
        (h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
      using der_h by blast
  next
    fix y assume yS: "y \<in> \<Phi> ` S"
    have \<Psi>yS: "\<Psi> y \<in> S" using yS \<Psi>\<Phi> by auto
    have linf': "linear (f' (\<Psi> y))" using der[OF \<Psi>yS] has_derivative_linear by blast
    have ling: "linear (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"
      using linear_compose[OF linear_compose[OF lin\<Psi> linf'] lin\<Phi>]
      by (simp add: o_def)
    have "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) \<noteq> CARD('n bit0)"
      by (metis full_rank_surjective ling matrix_vector_mul(2) ns_h yS)
    moreover have "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) \<le> CARD('n bit0)"
      by (metis min.idem rank_bound)
    ultimately show "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) < CARD('n bit0)"
      by simp
  qed

  have image_eq: "f ` S = \<Psi> ` (h ` (\<Phi> ` S))"
    unfolding h_def
    using \<Psi>\<Phi>
    by (smt (verit, best) image_cong image_image) 

  show ?thesis
    unfolding image_eq
  proof (rule negligible_locally_Lipschitz_image[OF _ neg_h])
    show "DIM(real^('n bit0)) \<le> DIM((real^2)^'n)" by simp
  next
    fix x :: "real^('n bit0)" assume "x \<in> h ` (\<Phi> ` S)"
    obtain K where K: "\<And>z. norm (\<Psi> z) \<le> K * norm z"
      using lin\<Psi> linear_conv_bounded_linear bounded_linear.bounded linear_bounded by blast
    show "\<exists>T B. open T \<and> x \<in> T \<and>
            (\<forall>y\<in>(h ` (\<Phi> ` S)) \<inter> T. norm (\<Psi> y - \<Psi> x) \<le> B * norm (y - x))"
      by (rule exI[of _ UNIV], rule exI[of _ K], auto simp: linear_diff[OF lin\<Psi>, symmetric] K)
  qed
qed

end
