section \<open>The phase equation has a negligible zero set\<close>

theory Residual_Null_Set
  imports Residual_Measure "HOL-Complex_Analysis.Complex_Analysis"
begin

subsection \<open>The phase functions\<close>

text \<open>For a phase vector \<open>t\<close> (in \<open>Sketch.md\<close> \<section>8, \<open>t\<^sub>a = c \<bullet> x\<^sub>a\<close>) the four sums below are the real
  and imaginary parts of the moments \<open>\<Sum>\<^sub>a e\<^bsup>-i t\<^sub>a\<^esup>\<close> and \<open>\<Sum>\<^sub>a t\<^sub>a e\<^bsup>-i t\<^sub>a\<^esup>\<close>.  The sketch writes
  \<open>s\<^sub>m\<close>, \<open>q\<^sub>m\<close>, \<open>W\<close>, \<open>P\<close>, \<open>f\<^sub>m\<close> as double sums over phase differences; here they are
  \<open>res_s m\<close>, \<open>res_q m\<close>, \<open>res_W\<close>, \<open>res_P\<close>, \<open>res_f m\<close>, written with the single sums (the two
  forms agree by the addition formulas).\<close>

definition phase_cos_sum :: "real^'n \<Rightarrow> real" where
  "phase_cos_sum t = (\<Sum>a\<in>UNIV. cos (t $ a))"

definition phase_sin_sum :: "real^'n \<Rightarrow> real" where
  "phase_sin_sum t = (\<Sum>a\<in>UNIV. sin (t $ a))"

definition phase_lin_cos_sum :: "real^'n \<Rightarrow> real" where
  "phase_lin_cos_sum t = (\<Sum>a\<in>UNIV. t $ a * cos (t $ a))"

definition phase_lin_sin_sum :: "real^'n \<Rightarrow> real" where
  "phase_lin_sin_sum t = (\<Sum>a\<in>UNIV. t $ a * sin (t $ a))"

definition res_s :: "'n \<Rightarrow> real^'n \<Rightarrow> real" where
  "res_s m t = sin (t $ m) * phase_cos_sum t - cos (t $ m) * phase_sin_sum t"

definition res_q :: "'n \<Rightarrow> real^'n \<Rightarrow> real" where
  "res_q m t = t $ m * (cos (t $ m) * phase_cos_sum t + sin (t $ m) * phase_sin_sum t)
     - (cos (t $ m) * phase_lin_cos_sum t + sin (t $ m) * phase_lin_sin_sum t)"

definition res_W :: "real^'n \<Rightarrow> real" where
  "res_W t = (phase_cos_sum t)\<^sup>2 + (phase_sin_sum t)\<^sup>2"

definition res_P :: "real^'n \<Rightarrow> real" where
  "res_P t = 2 * (phase_lin_sin_sum t * phase_cos_sum t - phase_lin_cos_sum t * phase_sin_sum t)"

definition res_f :: "'n \<Rightarrow> real^'n \<Rightarrow> real" where
  "res_f m t = res_s m t * (res_P t + res_W t) + res_q m t * res_W t"


subsection \<open>One phase varies\<close>

text \<open>Along a line in direction \<open>axis m 1\<close> only the \<open>m\<close>-th term of each sum changes.  With the
  other terms collected in \<open>c\<close>, \<open>s\<close>, \<open>tc\<close>, \<open>ts\<close>, the functions become functions of one variable,
  stated for real and complex arguments at once.\<close>

definition slice_s :: "'a::{real_normed_field,banach} \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "slice_s c s x = sin x * (c + cos x) - cos x * (s + sin x)"

definition slice_q :: "'a::{real_normed_field,banach} \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "slice_q c s tc ts x = x * (cos x * (c + cos x) + sin x * (s + sin x))
     - (cos x * (tc + x * cos x) + sin x * (ts + x * sin x))"

definition slice_W :: "'a::{real_normed_field,banach} \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "slice_W c s x = (c + cos x)\<^sup>2 + (s + sin x)\<^sup>2"

definition slice_P :: "'a::{real_normed_field,banach} \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "slice_P c s tc ts x = 2 * ((ts + x * sin x) * (c + cos x) - (tc + x * cos x) * (s + sin x))"

definition slice_f :: "'a::{real_normed_field,banach} \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "slice_f c s tc ts x = slice_s c s x * (slice_P c s tc ts x + slice_W c s x)
     + slice_q c s tc ts x * slice_W c s x"

lemma sum_coordinate_shift:
  fixes p :: "real^'n" and g :: "real \<Rightarrow> real"
  shows "(\<Sum>a\<in>UNIV. g ((p + r *\<^sub>R axis m 1) $ a)) = (\<Sum>a\<in>UNIV - {m}. g (p $ a)) + g (p $ m + r)"
proof -
  have "(\<Sum>a\<in>UNIV. g ((p + r *\<^sub>R axis m 1) $ a))
      = g ((p + r *\<^sub>R axis m 1) $ m) + (\<Sum>a\<in>UNIV - {m}. g ((p + r *\<^sub>R axis m 1) $ a))"
    by (rule sum.remove) simp_all
  also have "(\<Sum>a\<in>UNIV - {m}. g ((p + r *\<^sub>R axis m 1) $ a)) = (\<Sum>a\<in>UNIV - {m}. g (p $ a))"
    by (rule sum.cong) (auto simp: axis_def)
  finally show ?thesis
    by (simp add: axis_def)
qed

lemma res_on_line:
  fixes p :: "real^'n" and m :: 'n
  defines "c \<equiv> (\<Sum>a\<in>UNIV - {m}. cos (p $ a))"
    and "s \<equiv> (\<Sum>a\<in>UNIV - {m}. sin (p $ a))"
    and "tc \<equiv> (\<Sum>a\<in>UNIV - {m}. p $ a * cos (p $ a))"
    and "ts \<equiv> (\<Sum>a\<in>UNIV - {m}. p $ a * sin (p $ a))"
  shows "res_s m (p + r *\<^sub>R axis m 1) = slice_s c s (p $ m + r)"
    and "res_f m (p + r *\<^sub>R axis m 1) = slice_f c s tc ts (p $ m + r)"
proof -
  let ?t = "p + r *\<^sub>R axis m 1"
  have m: "?t $ m = p $ m + r"
    by (simp add: axis_def)
  have 1: "phase_cos_sum ?t = c + cos (p $ m + r)"
    unfolding phase_cos_sum_def c_def by (rule sum_coordinate_shift)
  have 2: "phase_sin_sum ?t = s + sin (p $ m + r)"
    unfolding phase_sin_sum_def s_def by (rule sum_coordinate_shift)
  have 3: "phase_lin_cos_sum ?t = tc + (p $ m + r) * cos (p $ m + r)"
    unfolding phase_lin_cos_sum_def tc_def by (rule sum_coordinate_shift[where g = "\<lambda>y. y * cos y"])
  have 4: "phase_lin_sin_sum ?t = ts + (p $ m + r) * sin (p $ m + r)"
    unfolding phase_lin_sin_sum_def ts_def by (rule sum_coordinate_shift[where g = "\<lambda>y. y * sin y"])
  show s_eq: "res_s m ?t = slice_s c s (p $ m + r)"
    by (simp add: res_s_def slice_s_def m 1 2)
  have "res_q m ?t = slice_q c s tc ts (p $ m + r)"
    by (simp add: res_q_def slice_q_def m 1 2 3 4)
  moreover have "res_W ?t = slice_W c s (p $ m + r)"
    by (simp add: res_W_def slice_W_def 1 2)
  moreover have "res_P ?t = slice_P c s tc ts (p $ m + r)"
    by (simp add: res_P_def slice_P_def 1 2 3 4)
  ultimately show "res_f m ?t = slice_f c s tc ts (p $ m + r)"
    by (simp add: res_f_def slice_f_def s_eq)
qed


subsection \<open>The one-variable function is not identically zero\<close>

lemma slice_s_alt: "slice_s c s x = c * sin x - s * cos x"
  by (simp add: slice_s_def algebra_simps)

lemma slice_q_alt: "slice_q c s tc ts x = x * (c * cos x + s * sin x) - (tc * cos x + ts * sin x)"
proof -
  have "slice_q c s tc ts x
      = x * (c * cos x + s * sin x) + x * (cos x * cos x + sin x * sin x)
        - (tc * cos x + ts * sin x) - x * (cos x * cos x + sin x * sin x)"
    unfolding slice_q_def by (simp only: algebra_simps)
  then show ?thesis
    by simp
qed

lemma slice_P_alt:
  "slice_P c s tc ts x = 2 * (ts * c - tc * s + ts * cos x - tc * sin x + x * (c * sin x - s * cos x))"
  by (simp add: slice_P_def algebra_simps)

lemma slice_f_period:
  fixes x :: real
  shows "slice_f c s tc ts (x + 2 * pi) - slice_f c s tc ts x
       = 2 * pi * (2 * (slice_s c s x)\<^sup>2 + (c * cos x + s * sin x) * slice_W c s x)"
proof -
  have s: "slice_s c s (x + 2 * pi) = slice_s c s x"
    by (simp add: slice_s_def)
  have W: "slice_W c s (x + 2 * pi) = slice_W c s x"
    by (simp add: slice_W_def)
  have q: "slice_q c s tc ts (x + 2 * pi) = slice_q c s tc ts x + 2 * pi * (c * cos x + s * sin x)"
    unfolding slice_q_alt sin_periodic cos_periodic by (simp only: algebra_simps)
  have P: "slice_P c s tc ts (x + 2 * pi) = slice_P c s tc ts x + 4 * pi * slice_s c s x"
    unfolding slice_P_alt slice_s_alt sin_periodic cos_periodic by (simp only: algebra_simps)
  show ?thesis
    unfolding slice_f_def s W q P by (simp add: algebra_simps power2_eq_square)
qed

lemma slice_half_period:
  fixes x :: real
  shows "slice_s c s (x + pi) = - slice_s c s x"
    and "slice_W c s (x + pi) = slice_W c s x - 4 * (c * cos x + s * sin x)"
  by (simp_all add: slice_s_alt slice_W_def power2_eq_square algebra_simps)

lemma slice_f_not_all_zero:
  fixes x0 :: real
  assumes "slice_s c s x0 \<noteq> 0"
  shows "\<exists>x::real. slice_f c s tc ts x \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>x::real. slice_f c s tc ts x \<noteq> 0)"
  then have z: "slice_f c s tc ts x = 0" for x :: real
    by blast
  define S where "S = slice_s c s x0"
  define C where "C = c * cos x0 + s * sin x0"
  define W where "W = slice_W c s x0"
  have 1: "2 * S\<^sup>2 + C * W = 0"
    using slice_f_period[of c s tc ts x0] by (simp add: z S_def C_def W_def)
  have e1: "slice_s c s (x0 + pi) = - S"
    by (simp add: slice_half_period S_def)
  have e2: "slice_W c s (x0 + pi) = W - 4 * C"
    by (simp add: slice_half_period W_def C_def)
  have e3: "c * cos (x0 + pi) + s * sin (x0 + pi) = - C"
    by (simp add: C_def)
  have "2 * (slice_s c s (x0 + pi))\<^sup>2
      + (c * cos (x0 + pi) + s * sin (x0 + pi)) * slice_W c s (x0 + pi) = 0"
    using slice_f_period[of c s tc ts "x0 + pi"] by (simp add: z)
  then have 2: "2 * S\<^sup>2 - C * (W - 4 * C) = 0"
    unfolding e1 e2 e3 by simp
  have expanded: "2 * S\<^sup>2 - C * W + 4 * C\<^sup>2 = 0"
    using 2 by (simp add: algebra_simps power2_eq_square)
  have "S\<^sup>2 + C\<^sup>2 = 0"
    using 1 expanded by linarith
  then have "S = 0"
    by (simp add: sum_power2_eq_zero_iff)
  with assms show False
    by (simp add: S_def)
qed

lemma countable_slice_zeros:
  fixes c s tc ts :: real
  shows "countable {x::real. slice_s c s x \<noteq> 0 \<and> slice_f c s tc ts x = 0}"
proof (cases "\<exists>x0::real. slice_s c s x0 \<noteq> 0")
  case False
  then have "{x::real. slice_s c s x \<noteq> 0 \<and> slice_f c s tc ts x = 0} = {}"
    by auto
  then show ?thesis
    by (simp only: countable_empty)
next
  case True
  then obtain x1 :: real where x1: "slice_f c s tc ts x1 \<noteq> 0"
    using slice_f_not_all_zero by blast
  define G :: "complex \<Rightarrow> complex"
    where "G z = slice_f (of_real c) (of_real s) (of_real tc) (of_real ts) z" for z
  have G_real: "G (of_real x) = of_real (slice_f c s tc ts x)" for x :: real
    by (simp add: G_def slice_f_def slice_s_def slice_q_def slice_W_def slice_P_def
        sin_of_real cos_of_real)
  have holo: "G holomorphic_on UNIV"
    unfolding G_def[abs_def] slice_f_def slice_s_def slice_q_def slice_W_def slice_P_def
    by (intro holomorphic_intros)
  have "countable {z. G z = 0}"
  proof (cases "G constant_on UNIV")
    case True
    then obtain y where y: "\<And>z. G z = y"
      by (auto simp: constant_on_def)
    have "y \<noteq> 0"
      using y[of "of_real x1"] x1 by (auto simp: G_real)
    then have "{z. G z = 0} = {}"
      using y by auto
    then show ?thesis
      by simp
  next
    case False
    have "countable {z\<in>UNIV. G z = 0}"
      by (rule holomorphic_countable_zeros[OF holo open_UNIV connected_UNIV fsigma_UNIV False])
    then show ?thesis
      by simp
  qed
  moreover have "of_real ` {x::real. slice_s c s x \<noteq> 0 \<and> slice_f c s tc ts x = 0} \<subseteq> {z. G z = 0}"
    by (auto simp: G_real)
  ultimately have "countable ((of_real :: real \<Rightarrow> complex) ` {x::real. slice_s c s x \<noteq> 0 \<and> slice_f c s tc ts x = 0})"
    using countable_subset by blast
  then show ?thesis
    by (rule countable_image_inj_on) (simp add: inj_on_def)
qed


subsection \<open>The zero set is negligible\<close>

theorem negligible_res_f_zeros:
  fixes m :: "'n::finite"
  shows "negligible {t :: real^'n. res_s m t \<noteq> 0 \<and> res_f m t = 0}"
proof -
  have cont_s: "continuous_on UNIV (res_s m)"
    unfolding res_s_def[abs_def] phase_cos_sum_def phase_sin_sum_def
    by (intro continuous_intros)
  have cont_f: "continuous_on UNIV (res_f m)"
    unfolding res_f_def[abs_def] res_s_def res_q_def res_W_def res_P_def
      phase_cos_sum_def phase_sin_sum_def phase_lin_cos_sum_def phase_lin_sin_sum_def
    by (intro continuous_intros)
  have op: "open {t. res_s m t \<noteq> 0}"
    by (rule open_Collect_neq[OF cont_s continuous_on_const])
  have cl: "closed {t. res_f m t = 0}"
    by (rule closed_Collect_eq[OF cont_f continuous_on_const])
  have "negligible ({t. res_s m t \<noteq> 0} \<inter> {t. res_f m t = 0})"
  proof (rule negligible_of_countable_line_slices_open_closed[OF op cl, where d = "axis m 1"])
    fix p :: "real^'n"
    define c where "c = (\<Sum>a\<in>UNIV - {m}. cos (p $ a))"
    define s where "s = (\<Sum>a\<in>UNIV - {m}. sin (p $ a))"
    define tc where "tc = (\<Sum>a\<in>UNIV - {m}. p $ a * cos (p $ a))"
    define ts where "ts = (\<Sum>a\<in>UNIV - {m}. p $ a * sin (p $ a))"
    have "{r. p + r *\<^sub>R axis m 1 \<in> {t. res_s m t \<noteq> 0} \<inter> {t. res_f m t = 0}}
        = (\<lambda>x. x - p $ m) ` {x. slice_s c s x \<noteq> 0 \<and> slice_f c s tc ts x = 0}"
    proof (intro equalityI subsetI)
      fix r assume "r \<in> {r. p + r *\<^sub>R axis m 1 \<in> {t. res_s m t \<noteq> 0} \<inter> {t. res_f m t = 0}}"
      then have "slice_s c s (p $ m + r) \<noteq> 0 \<and> slice_f c s tc ts (p $ m + r) = 0"
        by (simp add: res_on_line c_def s_def tc_def ts_def)
      then have "p $ m + r \<in> {x. slice_s c s x \<noteq> 0 \<and> slice_f c s tc ts x = 0}"
        by simp
      moreover have "r = (\<lambda>x. x - p $ m) (p $ m + r)"
        by simp
      ultimately show "r \<in> (\<lambda>x. x - p $ m) ` {x. slice_s c s x \<noteq> 0 \<and> slice_f c s tc ts x = 0}"
        by (rule rev_image_eqI)
    next
      fix r assume "r \<in> (\<lambda>x. x - p $ m) ` {x. slice_s c s x \<noteq> 0 \<and> slice_f c s tc ts x = 0}"
      then obtain x where x: "slice_s c s x \<noteq> 0" "slice_f c s tc ts x = 0" and r: "r = x - p $ m"
        by auto
      have "p $ m + r = x"
        by (simp add: r)
      then show "r \<in> {r. p + r *\<^sub>R axis m 1 \<in> {t. res_s m t \<noteq> 0} \<inter> {t. res_f m t = 0}}"
        using x by (simp add: res_on_line c_def s_def tc_def ts_def)
    qed
    then show "countable {r. p + r *\<^sub>R axis m 1 \<in> {t. res_s m t \<noteq> 0} \<inter> {t. res_f m t = 0}}"
      using countable_slice_zeros[of c s tc ts] by simp
  qed
  moreover have "{t. res_s m t \<noteq> 0 \<and> res_f m t = 0} = {t. res_s m t \<noteq> 0} \<inter> {t. res_f m t = 0}"
    by auto
  ultimately show ?thesis
    by simp
qed

lemma continuous_on_res_s: "continuous_on UNIV (res_s m)"
  unfolding res_s_def[abs_def] phase_cos_sum_def phase_sin_sum_def
  by (intro continuous_intros)

lemma continuous_on_res_f: "continuous_on UNIV (res_f m)"
  unfolding res_f_def[abs_def] res_s_def res_q_def res_W_def res_P_def
    phase_cos_sum_def phase_sin_sum_def phase_lin_cos_sum_def phase_lin_sin_sum_def
  by (intro continuous_intros)

lemma res_f_zeros_borel: "{t :: real^'n. res_s m t \<noteq> 0 \<and> res_f m t = 0} \<in> sets borel"
proof -
  have "open {t. res_s m t \<noteq> 0}"
    by (rule open_Collect_neq[OF continuous_on_res_s continuous_on_const])
  then have 1: "{t. res_s m t \<noteq> 0} \<in> sets borel"
    by (rule borel_open)
  have "closed {t. res_f m t = 0}"
    by (rule closed_Collect_eq[OF continuous_on_res_f continuous_on_const])
  then have 2: "{t. res_f m t = 0} \<in> sets borel"
    by (rule borel_closed)
  have eq: "{t. res_s m t \<noteq> 0 \<and> res_f m t = 0} = {t. res_s m t \<noteq> 0} \<inter> {t. res_f m t = 0}"
    by auto
  show ?thesis
    unfolding eq by (rule sets.Int[OF 1 2])
qed

end
