section \<open>A set whose line slices are countable is negligible\<close>

theory Residual_Measure
  imports "HOL-Analysis.Analysis"
begin

text \<open>Fubini for a Borel set in a product with the real line: countable slices give measure zero.\<close>

lemma emeasure_lborel_countable_slices:
  fixes A :: "('a::euclidean_space \<times> real) set"
  assumes A: "A \<in> sets borel"
    and cnt: "\<And>p. countable {r. (p, r) \<in> A}"
  shows "emeasure lborel A = 0"
proof -
  have A': "A \<in> sets ((lborel :: 'a measure) \<Otimes>\<^sub>M (lborel :: real measure))"
    unfolding lborel_prod using A by simp
  have "emeasure lborel A = emeasure ((lborel :: 'a measure) \<Otimes>\<^sub>M (lborel :: real measure)) A"
    by (simp add: lborel_prod)
  also have "\<dots> = (\<integral>\<^sup>+p. emeasure lborel (Pair p -` A) \<partial>lborel)"
    by (rule lborel.emeasure_pair_measure_alt[OF A'])
  also have "\<dots> = (\<integral>\<^sup>+p. 0 \<partial>(lborel :: 'a measure))"
  proof (rule nn_integral_cong)
    fix p :: 'a
    have "Pair p -` A = {r. (p, r) \<in> A}"
      by auto
    then show "emeasure lborel (Pair p -` A) = 0"
      using cnt[of p] by (simp add: emeasure_lborel_countable)
  qed
  also have "\<dots> = 0"
    by simp
  finally show ?thesis .
qed

text \<open>The general form.  The shear \<open>(p, r) \<mapsto> (p + r d, r)\<close> turns slices of \<open>S\<close> along \<open>d\<close>
  into slices along the second factor.\<close>

theorem negligible_of_countable_line_slices:
  fixes S :: "'a::euclidean_space set" and d :: 'a
  assumes S: "S \<in> sets borel"
    and cnt: "\<And>p. countable {r::real. p + r *\<^sub>R d \<in> S}"
  shows "negligible S"
proof -
  define shear :: "'a \<times> real \<Rightarrow> 'a \<times> real" where "shear z = (fst z + snd z *\<^sub>R d, snd z)" for z
  define T :: "('a \<times> real) set" where "T = {z. fst z + snd z *\<^sub>R d \<in> S \<and> snd z \<in> {0..1}}"
  have lin: "linear shear"
    by (rule linearI) (simp_all add: shear_def algebra_simps)
  have T_borel: "T \<in> sets borel"
  proof -
    have "(\<lambda>z::'a \<times> real. fst z + snd z *\<^sub>R d) \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    then have 1: "(\<lambda>z::'a \<times> real. fst z + snd z *\<^sub>R d) -` S \<in> sets borel"
      using S by (rule measurable_sets_borel)
    have "(snd :: 'a \<times> real \<Rightarrow> real) \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    then have 2: "(snd :: 'a \<times> real \<Rightarrow> real) -` {0..1} \<in> sets borel"
      by (rule measurable_sets_borel) simp
    have "T = (\<lambda>z. fst z + snd z *\<^sub>R d) -` S \<inter> snd -` {0..1}"
      by (auto simp: T_def)
    then show ?thesis
      using 1 2 by simp
  qed
  have "emeasure lborel T = 0"
  proof (rule emeasure_lborel_countable_slices[OF T_borel])
    fix p :: 'a
    have "{r. (p, r) \<in> T} \<subseteq> {r. p + r *\<^sub>R d \<in> S}"
      by (auto simp: T_def)
    then show "countable {r. (p, r) \<in> T}"
      using cnt[of p] countable_subset by blast
  qed
  then have "T \<in> null_sets lborel"
    using T_borel by (simp add: null_sets_def)
  then have negT: "negligible T"
    by (simp add: negligible_iff_null_sets null_sets_completionI)
  have image: "shear ` T = S \<times> {0..1}"
  proof (intro equalityI subsetI)
    fix w assume "w \<in> shear ` T"
    then show "w \<in> S \<times> {0..1}"
      by (auto simp: shear_def T_def)
  next
    fix w :: "'a \<times> real" assume w: "w \<in> S \<times> {0..1}"
    define z where "z = (fst w - snd w *\<^sub>R d, snd w)"
    have "z \<in> T" and "shear z = w"
      using w by (auto simp: z_def T_def shear_def)
    then show "w \<in> shear ` T"
      by (metis imageI)
  qed
  have neg: "negligible (S \<times> {0..1::real})"
    using negligible_linear_image[OF lin negT] by (simp add: image)
  have borel: "S \<times> {0..1::real} \<in> sets borel"
    by (rule borel_Times[OF S]) simp
  have "emeasure lborel (S \<times> {0..1::real}) = 0"
  proof -
    have "S \<times> {0..1::real} \<in> null_sets lebesgue"
      using neg by (simp add: negligible_iff_null_sets)
    then have "emeasure lebesgue (S \<times> {0..1::real}) = 0"
      by (simp add: null_sets_def)
    then show ?thesis
      using borel by simp
  qed
  moreover have "emeasure lborel (S \<times> {0..1::real}) = emeasure lborel S * emeasure lborel {0..1::real}"
  proof -
    have "emeasure lborel (S \<times> {0..1::real})
        = emeasure ((lborel :: 'a measure) \<Otimes>\<^sub>M (lborel :: real measure)) (S \<times> {0..1})"
      by (simp add: lborel_prod)
    also have "\<dots> = emeasure lborel S * emeasure lborel {0..1::real}"
      by (rule lborel.emeasure_pair_measure_Times) (use S in simp_all)
    finally show ?thesis .
  qed
  ultimately have "emeasure lborel S = 0"
    by simp
  then have "S \<in> null_sets lborel"
    using S by (simp add: null_sets_def)
  then show ?thesis
    by (simp add: negligible_iff_null_sets null_sets_completionI)
qed

text \<open>The form used for the residual: the set is cut out by an open and a closed condition.\<close>

corollary negligible_of_countable_line_slices_open_closed:
  fixes U C :: "'a::euclidean_space set" and d :: 'a
  assumes "open U" and "closed C"
    and "\<And>p. countable {r::real. p + r *\<^sub>R d \<in> U \<inter> C}"
  shows "negligible (U \<inter> C)"
proof (rule negligible_of_countable_line_slices)
  show "U \<inter> C \<in> sets borel"
    using assms(1,2) by simp
qed (rule assms(3))

text \<open>A negligible Borel set times a whole space is negligible.\<close>

lemma negligible_Times_UNIV:
  fixes A :: "'a::euclidean_space set"
  assumes A: "A \<in> sets borel" and neg: "negligible A"
  shows "negligible (A \<times> (UNIV :: 'b::euclidean_space set))"
proof -
  have "A \<in> null_sets lebesgue"
    using neg by (simp add: negligible_iff_null_sets)
  then have "emeasure lebesgue A = 0"
    by (simp add: null_sets_def)
  then have A0: "emeasure lborel A = 0"
    using A by simp
  have borel: "A \<times> (UNIV :: 'b set) \<in> sets borel"
    by (rule borel_Times[OF A]) simp
  have "emeasure lborel (A \<times> (UNIV :: 'b set))
      = emeasure ((lborel :: 'a measure) \<Otimes>\<^sub>M (lborel :: 'b measure)) (A \<times> UNIV)"
    by (simp add: lborel_prod)
  also have "\<dots> = emeasure lborel A * emeasure lborel (UNIV :: 'b set)"
    by (rule lborel.emeasure_pair_measure_Times) (use A in simp_all)
  also have "\<dots> = 0"
    by (simp add: A0)
  finally have "A \<times> (UNIV :: 'b set) \<in> null_sets lborel"
    using borel by (simp add: null_sets_def)
  then show ?thesis
    by (simp add: negligible_iff_null_sets null_sets_completionI)
qed

end
