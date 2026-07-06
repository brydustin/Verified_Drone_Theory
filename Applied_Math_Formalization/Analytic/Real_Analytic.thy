section \<open>Real-Analytic ($C^\omega$) Functions and the Analytic Implicit-Function Theorem\<close>

text \<open>
  A self-contained, dimensionally-general theory of real-analytic functions, built on the
  blessed higher-derivative / Taylor API:

  \<^item> 1-D analyticity is phrased via \<open>taylor_poly\<close> / \<open>peano_remainder\<close> from \<open>Taylor_Peano\<close>
    (i.e. the iterated \<open>(deriv ^^ n)\<close>), NOT the deprecated \<open>Nth_derivative\<close>.
  \<^item> Multivariate analyticity is a local convergent power series over the Euclidean basis,
    so it covers every finite dimension uniformly (class \<open>euclidean_space\<close>).

  This theory states the foundation sorry-first: definitions, analytic-implies-smooth,
  the smooth-but-not-analytic witness, closure, the nowhere-dense-zeros workhorse, and the
  target analytic IFT.  It depends on nothing from the drone development; the dipole-specific
  bridge that consumes it lives in a separate theory.
\<close>

theory Real_Analytic
  imports
    "Applied_Math_HigherDiff.Higher_Differentiability_Multi"
    "Applied_Math_HigherDiff.Taylor_Peano"
    "HOL-Analysis.Infinite_Sum"
begin


subsection \<open>$C^\infty$ smoothness (infinitely many continuous derivatives)\<close>

definition Cinfinity_at ::
  "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool" where
  "Cinfinity_at f x \<longleftrightarrow> (\<forall>k. Ck_at k f x)"

definition Cinfinity_on ::
  "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "Cinfinity_on f U \<longleftrightarrow> open U \<and> (\<forall>x\<in>U. Cinfinity_at f x)"

lemma Cinfinity_imp_Ck: "Cinfinity_at f x \<Longrightarrow> Ck_at k f x"
  unfolding Cinfinity_at_def by blast

lemma Cinfinity_on_imp_Ck_on: "Cinfinity_on f U \<Longrightarrow> Ck_on k f U"
  unfolding Cinfinity_on_def Ck_on_def Cinfinity_at_def by blast


subsection \<open>One-dimensional real analyticity via the Peano/Taylor expansion\<close>

text \<open>
  \<open>f\<close> is real-analytic at \<open>c\<close> when, on a neighbourhood, it is smooth and its
  \<open>(deriv ^^ n)\<close> Taylor series converges back to it (equivalently, the Peano remainder
  \<open>peano_remainder n f c x\<close> tends to \<open>0\<close>).
\<close>

definition real_analytic_at_1d :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "real_analytic_at_1d f c \<longleftrightarrow>
     (\<exists>r>0. (\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow> (\<forall>n. f n-times_differentiable_at x))
          \<and> (\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow>
                 (\<lambda>n. (deriv ^^ n) f c / fact n * (x - c) ^ n) sums f x))"


subsection \<open>Multivariate real analyticity (local convergent power series)\<close>

text \<open>The basis monomial (a product over the Euclidean basis) and the finitely-supported multi-indices.\<close>

definition ra_monomial :: "'a::euclidean_space \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> real" where
  "ra_monomial h \<alpha> = (\<Prod>b\<in>Basis. (h \<bullet> b) ^ (\<alpha> b))"

definition ra_idx :: "('a::euclidean_space \<Rightarrow> nat) set" where
  "ra_idx = {\<alpha>. {b. \<alpha> b \<noteq> 0} \<subseteq> Basis}"

definition real_analytic_on ::
  "('a::euclidean_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "real_analytic_on f U \<longleftrightarrow> open U \<and>
     (\<forall>x0\<in>U. \<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x) ra_idx)"

text \<open>On the line, the multivariate notion coincides with the Peano/Taylor one.\<close>

lemma real_analytic_on_1d_iff:
  fixes f :: "real \<Rightarrow> real"
  shows "real_analytic_on f U \<longleftrightarrow> open U \<and> (\<forall>c\<in>U. real_analytic_at_1d f c)"
proof -
  define i :: "nat \<Rightarrow> (real \<Rightarrow> nat)" where "i = (\<lambda>n b. if b = 1 then n else 0)"
  define j :: "(real \<Rightarrow> nat) \<Rightarrow> nat" where "j = (\<lambda>\<alpha>. \<alpha> 1)"
  \<comment> \<open>basic facts about the bijection between @{term ra_idx} and @{term "UNIV::nat set"}\<close>
  have ij: "i (j \<alpha>) = \<alpha>" if "\<alpha> \<in> ra_idx" for \<alpha>
  proof (rule ext)
    fix b :: real
    show "i (j \<alpha>) b = \<alpha> b"
    proof (cases "b = 1")
      case True thus ?thesis by (simp add: i_def j_def)
    next
      case False
      with that have "\<alpha> b = 0" by (auto simp: ra_idx_def)
      with False show ?thesis by (simp add: i_def)
    qed
  qed
  have ji: "j (i n) = n" for n by (simp add: i_def j_def)
  have i_idx: "i n \<in> ra_idx" for n by (auto simp: i_def ra_idx_def)
  have iev: "i n 1 = n" for n by (simp add: i_def)
  \<comment> \<open>the basis monomial on the line is just a power\<close>
  have mono: "ra_monomial h \<alpha> = h ^ (\<alpha> 1)" for h :: real and \<alpha>
    by (simp add: ra_monomial_def)
      \<comment> \<open>@{term "Basis::real set"} is @{term "{1}"} and @{term "inner h 1 = h"}, both [simp]\<close>
  \<comment> \<open>the central reindexing equivalence, for a fixed expansion point and argument\<close>
  have reindex:
    "((\<lambda>n. (deriv ^^ n) f c0 / fact n * (x - c0) ^ n) has_sum s) (UNIV :: nat set)
       = ((\<lambda>\<alpha>. ra_monomial (x - c0) \<alpha> *\<^sub>R (\<lambda>\<beta>. (deriv ^^ (\<beta> 1)) f c0 / fact (\<beta> 1)) \<alpha>)
            has_sum s) ra_idx"
    for c0 x s
    by (rule has_sum_reindex_bij_witness[where i = j and j = i])
       (auto simp: ji i_idx ij mono iev mult.commute)

  show ?thesis
  proof
    \<comment> \<open>(\<Rightarrow>) hard direction: a local power series gives smoothness + Taylor convergence\<close>
    assume A: "real_analytic_on f U"
    then have oU: "open U" by (simp only: real_analytic_on_def)
    have "real_analytic_at_1d f c" if cU: "c \<in> U" for c
    proof -
      from A cU obtain r cc where r: "0 < r"
        and HS: "\<And>x. dist x c < r \<Longrightarrow>
                  ((\<lambda>\<alpha>. ra_monomial (x - c) \<alpha> *\<^sub>R cc \<alpha>) has_sum f x) ra_idx"
        unfolding real_analytic_on_def by blast
      \<comment> \<open>Reindex each unordered sum to an ordinary power series in @{term "x - c"}.\<close>
      have sums_xc: "(\<lambda>n. cc (i n) * (x - c) ^ n) sums f x" if "dist x c < r" for x
      proof -
        have "((\<lambda>n. cc (i n) * (x - c) ^ n) has_sum f x) (UNIV :: nat set)
                = ((\<lambda>\<alpha>. ra_monomial (x - c) \<alpha> *\<^sub>R cc \<alpha>) has_sum f x) ra_idx"
          by (rule has_sum_reindex_bij_witness[where i = j and j = i])
             (auto simp: ji i_idx ij mono iev mult.commute)
        with HS[OF that] have
          "((\<lambda>n. cc (i n) * (x - c) ^ n) has_sum f x) (UNIV :: nat set)" by simp
        thus ?thesis by (rule has_sum_imp_sums)
      qed
      \<comment> \<open>The function equals the convergent power series throughout the ball; term-by-term
         differentiation (\<open>termdiffs\<close>) makes it smooth and identifies its coefficients with the
         Taylor coefficients \<open>(deriv ^^ n) f c / fact n\<close>.\<close>
      define a where "a = (\<lambda>n. cc (i n))"
      have sums_a: "(\<lambda>n. a n * z ^ n) sums f (c + z)" if "\<bar>z\<bar> < r" for z
      proof -
        have "dist (c + z) c < r" using that by (simp only: dist_real_def)
        from sums_xc[OF this] show ?thesis by (simp add: a_def)
      qed
      have summ_a: "summable (\<lambda>n. a n * z ^ n)" if "\<bar>z\<bar> < r" for z
        using sums_a[OF that] by (rule sums_summable)
      \<comment> \<open>summability of every \<open>diffs\<close>-iterate strictly inside the radius\<close>
      have summ_diffs: "summable (\<lambda>m. (diffs ^^ n) a m * z ^ m)" if "\<bar>z\<bar> < r" for n z
        using that
      proof (induction n arbitrary: z)
        case 0
        thus ?case using summ_a by simp
      next
        case (Suc n)
        have "summable (\<lambda>m. diffs ((diffs ^^ n) a) m * z ^ m)"
        proof (rule termdiff_converges[where K = r])
          show "norm z < r" using Suc.prems by simp
          fix w :: real assume "norm w < r"
          hence "\<bar>w\<bar> < r" by simp
          thus "summable (\<lambda>m. (diffs ^^ n) a m * w ^ m)" by (rule Suc.IH)
        qed
        thus ?case by simp
      qed
      \<comment> \<open>the centered power series and its term-by-term derivative\<close>
      define S where "S = (\<lambda>n y. \<Sum>m. (diffs ^^ n) a m * (y - c) ^ m)"
      have S0_eq_f: "S 0 x = f x" if "\<bar>x - c\<bar> < r" for x
      proof -
        from sums_a[of "x - c"] that have "(\<lambda>n. a n * (x - c) ^ n) sums f x" by simp
        thus ?thesis by (simp add: S_def sums_iff)
      qed
      have S_deriv: "(S n has_field_derivative S (Suc n) x) (at x)"
        if "\<bar>x - c\<bar> < r" for n x
      proof -
        have H: "((\<lambda>w. \<Sum>m. (diffs ^^ n) a m * w ^ m)
                   has_field_derivative (\<Sum>m. diffs ((diffs ^^ n) a) m * (x - c) ^ m))
                  (at (x - c))"
        proof (rule termdiffs_strong'[where K = r])
          fix w :: real assume "norm w < r"
          thus "summable (\<lambda>m. (diffs ^^ n) a m * w ^ m)" using summ_diffs by simp
        next
          show "norm (x - c) < r" using that by simp
        qed
        have shift: "((\<lambda>y. y - c) has_field_derivative 1) (at x)"
          by (auto intro!: derivative_eq_intros)
        have "((\<lambda>y. (\<lambda>w. \<Sum>m. (diffs ^^ n) a m * w ^ m) (y - c))
                 has_field_derivative
                 (\<Sum>m. diffs ((diffs ^^ n) a) m * (x - c) ^ m) * 1) (at x)"
          by (rule DERIV_chain'[OF shift]) (use H in simp)
        thus ?thesis by (simp add: S_def)
      qed
      \<comment> \<open>MAIN INDUCTION: \<open>f\<close> is \<open>n\<close>-times differentiable on the ball and \<open>(deriv^^n) f = S n\<close>\<close>
      have main: "\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow>
                    f n-times_differentiable_at x \<and> (deriv ^^ n) f x = S n x" for n
      proof (induction n)
        case 0
        show ?case by (auto simp: S0_eq_f)
      next
        case (Suc n)
        show ?case
        proof (intro allI impI conjI)
          fix x assume xc: "\<bar>x - c\<bar> < r"
          have ballopen: "{y. \<bar>y - c\<bar> < r} = ball c r"
            by (auto simp: dist_real_def abs_minus_commute)
          have eqA: "(deriv ^^ n) f y = S n y" if "\<bar>y - c\<bar> < r" for y
            using Suc.IH that by blast
          have dn_deriv: "((deriv ^^ n) f has_field_derivative S (Suc n) x) (at x)"
          proof (rule has_field_derivative_transform_within_open
                       [where f = "S n" and S = "{y. \<bar>y - c\<bar> < r}"])
            show "(S n has_field_derivative S (Suc n) x) (at x)" by (rule S_deriv[OF xc])
            show "open {y. \<bar>y - c\<bar> < r}" by (simp add: ballopen)
            show "x \<in> {y. \<bar>y - c\<bar> < r}" using xc by simp
            show "\<And>y. y \<in> {y. \<bar>y - c\<bar> < r} \<Longrightarrow> S n y = (deriv ^^ n) f y"
              using eqA by auto
          qed
          show "(deriv ^^ Suc n) f x = S (Suc n) x"
            using dn_deriv by (simp only: kth_deriv_Suc DERIV_imp_deriv)
          show "f (Suc n)-times_differentiable_at x"
            unfolding k_times_differentiable_at.simps(2)
          proof
            show "\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> f n-times_differentiable_at y"
            proof (intro exI[where x = "r - \<bar>x - c\<bar>"] conjI allI impI)
              show "0 < r - \<bar>x - c\<bar>" using xc by simp
              fix y assume "\<bar>y - x\<bar> < r - \<bar>x - c\<bar>"
              hence "\<bar>y - c\<bar> < r" by linarith
              thus "f n-times_differentiable_at y" using Suc.IH by blast
            qed
          next
            have "(deriv ^^ Suc n) f x = S (Suc n) x"
              using dn_deriv by (simp only: kth_deriv_Suc DERIV_imp_deriv)
            with dn_deriv
            show "((deriv ^^ n) f has_derivative (\<lambda>h. (deriv ^^ Suc n) f x * h)) (at x)"
              by (simp only: has_field_derivative_def)
          qed
        qed
      qed
      \<comment> \<open>the \<open>diffs\<close>-iterate evaluated at \<open>0\<close> yields \<open>fact n * a n\<close>\<close>
      have diffs_fact: "(diffs ^^ n) g 0 = fact n * g n" for n and g :: "nat \<Rightarrow> real"
      proof -
        have gen: "fact m * (diffs ^^ n) g m = fact (m + n) * g (m + n)" for m
        proof (induction n arbitrary: g m)
          case 0 show ?case by simp
        next
          case (Suc n)
          have "fact m * (diffs ^^ Suc n) g m = fact m * (diffs ^^ n) (diffs g) m"
            by (simp only: funpow_Suc_right o_apply)
          also have "\<dots> = fact (m + n) * (diffs g) (m + n)"
            using Suc.IH[of m "diffs g"] by simp
          also have "\<dots> = fact (m + n) * (of_nat (Suc (m + n)) * g (Suc (m + n)))"
            by (simp only: diffs_def)
          also have "\<dots> = fact (Suc (m + n)) * g (Suc (m + n))"
            by (simp add: algebra_simps)
          finally show ?case by (simp add: add.commute)
        qed
        from gen[of 0] show ?thesis by simp
      qed
      \<comment> \<open>the two facts originally introduced by \<open>sorry\<close>\<close>
      have coeff: "cc (i n) = (deriv ^^ n) f c / fact n" for n
      proof -
        have "\<bar>c - c\<bar> < r" using r by simp
        with main[of n] have "(deriv ^^ n) f c = S n c" by blast
        also have "S n c = (diffs ^^ n) a 0" by (simp add: S_def)
        also have "\<dots> = fact n * a n" by (rule diffs_fact)
        finally have "(deriv ^^ n) f c = fact n * a n" .
        thus ?thesis by (simp add: a_def)
      qed
      have smooth: "f n-times_differentiable_at x" if "\<bar>x - c\<bar> < r" for x n
        using main[of n] that by blast
      show ?thesis
        unfolding real_analytic_at_1d_def
      proof (intro exI[where x = r] conjI allI impI)
        show "0 < r" by (rule r)
      next
        fix x n assume "\<bar>x - c\<bar> < r" thus "f n-times_differentiable_at x"
          by (rule smooth)
      next
        fix x assume "\<bar>x - c\<bar> < r"
        then have "dist x c < r" by (simp only: dist_real_def)
        from sums_xc[OF this] show
          "(\<lambda>n. (deriv ^^ n) f c / fact n * (x - c) ^ n) sums f x"
          by (simp only: coeff mult.commute)
      qed
    qed
    with oU show "open U \<and> (\<forall>c\<in>U. real_analytic_at_1d f c)" by blast
  next
    \<comment> \<open>(\<Leftarrow>) easy direction: a convergent Taylor series, being absolutely convergent
       strictly inside its radius, gives an unordered (has_sum) expansion.\<close>
    assume B: "open U \<and> (\<forall>c\<in>U. real_analytic_at_1d f c)"
    then have oU: "open U" and AT: "\<And>c. c \<in> U \<Longrightarrow> real_analytic_at_1d f c" by auto
    show "real_analytic_on f U"
      unfolding real_analytic_on_def
    proof (intro conjI ballI)
      show "open U" by (rule oU)
    next
      fix c assume cU: "c \<in> U"
      from AT[OF cU] obtain r where r: "0 < r"
        and TS: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow>
                  (\<lambda>n. (deriv ^^ n) f c / fact n * (x - c) ^ n) sums f x"
        unfolding real_analytic_at_1d_def by blast
      show "\<exists>r>0. \<exists>cc. \<forall>x. dist x c < r \<longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (x - c) \<alpha> *\<^sub>R cc \<alpha>) has_sum f x) ra_idx"
      proof (intro exI[where x = r] exI[where x = "\<lambda>\<beta>. (deriv ^^ (\<beta> 1)) f c / fact (\<beta> 1)"]
                   conjI allI impI)
        show "0 < r" by (rule r)
      next
        fix x assume dx: "dist x c < r"
        then have axc: "\<bar>x - c\<bar> < r" by (simp only: dist_real_def)
        \<comment> \<open>Choose an intermediate radius strictly between @{term "\<bar>x - c\<bar>"} and @{term r}.\<close>
        define d where "d = (\<bar>x - c\<bar> + r) / 2"
        define x1 where "x1 = c + d"
        have d_pos: "0 < d"
        proof -
          have "0 < \<bar>x - c\<bar> + r" using r by linarith
          thus ?thesis unfolding d_def by simp
        qed
        have x1c: "\<bar>x1 - c\<bar> = d" using d_pos by (simp only: x1_def)
        have x1_in: "\<bar>x1 - c\<bar> < r"
        proof -
          have "\<bar>x - c\<bar> + r < 2 * r" using axc by linarith
          thus ?thesis unfolding x1c d_def by simp
        qed
        have lt: "\<bar>x - c\<bar> < \<bar>x1 - c\<bar>"
        proof -
          define a where "a = \<bar>x - c\<bar>"
          have ar: "a < r" using axc by (simp only: a_def)
          have "a * 2 < a + r" using ar by linarith
          hence "a < (a + r) / 2" by (simp only: field_simps)
          thus ?thesis by (simp only: x1c d_def a_def)
        qed
        \<comment> \<open>Convergence at @{term x1} gives summability there; @{thm [source] powser_insidea}
           upgrades it to absolute summability at @{term x}.\<close>
        have sm1: "summable (\<lambda>n. (deriv ^^ n) f c / fact n * (x1 - c) ^ n)"
          using TS[OF x1_in] by (rule sums_summable)
        have absum: "summable (\<lambda>n. norm ((deriv ^^ n) f c / fact n * (x - c) ^ n))"
          by (rule powser_insidea[OF sm1]) (use lt in simp)
        \<comment> \<open>Absolute + ordinary convergence \<Rightarrow> unordered convergence on \<open>UNIV :: nat set\<close>.\<close>
        have HSnat: "((\<lambda>n. (deriv ^^ n) f c / fact n * (x - c) ^ n) has_sum f x) (UNIV :: nat set)"
          by (rule norm_summable_imp_has_sum[OF absum TS[OF axc]])
        show "((\<lambda>\<alpha>. ra_monomial (x - c) \<alpha> *\<^sub>R (\<lambda>\<beta>. (deriv ^^ (\<beta> 1)) f c / fact (\<beta> 1)) \<alpha>)
                 has_sum f x) ra_idx"
          using HSnat by (simp only: reindex[of c x "f x"])
      qed
    qed
  qed
qed

subsection \<open>Multivariate power-series differentiation\<close>

definition ra_inc ::
  "('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> nat)" where
  "ra_inc \<alpha> b = \<alpha>(b := Suc (\<alpha> b))"

definition ra_Dmonomial ::
  "'a::euclidean_space \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> real" where
  "ra_Dmonomial x \<alpha> v =
     (\<Sum>b\<in>Basis.
        real (\<alpha> b) * (v \<bullet> b) *
        (x \<bullet> b) ^ (\<alpha> b - 1) *
        (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<alpha> d)))"

definition ra_dcoeff ::
  "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector) \<Rightarrow>
    'a \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'b" where
  "ra_dcoeff c v \<alpha> =
     (\<Sum>b\<in>Basis.
        (real (Suc (\<alpha> b)) * (v \<bullet> b)) *\<^sub>R
          c (ra_inc \<alpha> b))"



(* ===================== Verified #1-#12 + supporting infrastructure =====================
   Spliced from RA_Base_7 (core_uniform #1,#3-#5,#7 + reindex #2,#6) and WF_V812_full (#8-#12).
   NOTE: lemma #6 ra_derivative_reindex carries the STRENGTHENED per-direction summability
   hypothesis (the original bare summable_on form is false in infinite-dim banach). *)

definition ra_deg :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> nat" where
  "ra_deg \<alpha> = (\<Sum>b\<in>Basis. \<alpha> b)"


subsection \<open>Per-term Frechet derivative (from base file)\<close>

lemma ra_monomial_has_derivative:
  fixes x :: "'a::euclidean_space"
  shows
    "((\<lambda>y. ra_monomial y \<alpha>) has_derivative
        (ra_Dmonomial x \<alpha>))
      (at x)"
proof -
  have factor_deriv:
    "((\<lambda>y. (y \<bullet> b) ^ (\<alpha> b)) has_derivative
        (\<lambda>v. real (\<alpha> b) * (v \<bullet> b) * (x \<bullet> b) ^ (\<alpha> b - 1))) (at x)"
    if "b \<in> Basis" for b
  proof -
    have inner_d: "((\<lambda>y. y \<bullet> b) has_derivative (\<lambda>v. v \<bullet> b)) (at x)"
      using has_derivative_inner_left[OF has_derivative_id] by simp
    show "((\<lambda>y. (y \<bullet> b) ^ (\<alpha> b)) has_derivative
            (\<lambda>v. real (\<alpha> b) * (v \<bullet> b) * (x \<bullet> b) ^ (\<alpha> b - 1))) (at x)"
      using has_derivative_power[OF inner_d, of "\<alpha> b"] by simp
  qed
  have prod_d:
    "((\<lambda>y. \<Prod>b\<in>Basis. (y \<bullet> b) ^ (\<alpha> b)) has_derivative
       (\<lambda>v. \<Sum>b\<in>Basis.
              (real (\<alpha> b) * (v \<bullet> b) * (x \<bullet> b) ^ (\<alpha> b - 1)) *
              (\<Prod>c\<in>Basis - {b}. (x \<bullet> c) ^ (\<alpha> c)))) (at x)"
    by (rule has_derivative_prod[OF factor_deriv])
  have eq1: "(\<lambda>y. ra_monomial y \<alpha>) = (\<lambda>y. \<Prod>b\<in>Basis. (y \<bullet> b) ^ (\<alpha> b))"
    by (simp only: ra_monomial_def)
  have eq2: "ra_Dmonomial x \<alpha> =
      (\<lambda>v. \<Sum>b\<in>Basis.
              (real (\<alpha> b) * (v \<bullet> b) * (x \<bullet> b) ^ (\<alpha> b - 1)) *
              (\<Prod>c\<in>Basis - {b}. (x \<bullet> c) ^ (\<alpha> c)))"
    by (rule ext)
       (simp only: ra_Dmonomial_def mult.commute mult.left_commute mult.assoc)
  show ?thesis
    using prod_d unfolding eq1 eq2 .
qed

lemma ra_term_has_derivative:
  fixes x :: "'a::euclidean_space"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  shows
    "((\<lambda>y. ra_monomial y \<alpha> *\<^sub>R c \<alpha>) has_derivative
        (\<lambda>v. ra_Dmonomial x \<alpha> v *\<^sub>R c \<alpha>))
      (at x)"
  by (rule has_derivative_scaleR_left[OF ra_monomial_has_derivative])

lemma ra_shifted_term_has_derivative:
  fixes x x0 :: "'a::euclidean_space"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  shows
    "((\<lambda>y. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>) has_derivative
        (\<lambda>v. ra_Dmonomial (x - x0) \<alpha> v *\<^sub>R c \<alpha>))
      (at x)"
proof -
  have shift: "((\<lambda>y. y - x0) has_derivative (\<lambda>v. v)) (at x)"
    using has_derivative_diff[OF has_derivative_id has_derivative_const, of x0 "at x"]
    by simp
  have term_at: "((\<lambda>z. ra_monomial z \<alpha> *\<^sub>R c \<alpha>) has_derivative
                   (\<lambda>v. ra_Dmonomial (x - x0) \<alpha> v *\<^sub>R c \<alpha>)) (at (x - x0))"
    by (rule ra_term_has_derivative)
  show ?thesis
    using has_derivative_compose[OF shift term_at] by simp
qed


subsection \<open>Reused infrastructure (copied verbatim, sorry-free)\<close>

lemma ra_lev_finite:
  fixes n :: nat
  shows "finite {\<alpha>::'a::euclidean_space \<Rightarrow> nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n}"
proof -
  have "{\<alpha>::'a \<Rightarrow> nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n}
          \<subseteq> {hh. \<forall>x::'a. (x \<in> Basis \<longrightarrow> hh x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
  proof (rule subsetI)
    fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> {\<alpha>. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n}"
    then have a1: "\<alpha> \<in> ra_idx" and a2: "ra_deg \<alpha> = n" by auto
    have "\<forall>x::'a. (x \<in> Basis \<longrightarrow> \<alpha> x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> \<alpha> x = 0)"
    proof (intro allI conjI impI)
      fix x :: 'a assume xB: "x \<in> Basis"
      have "\<alpha> x \<le> (\<Sum>b\<in>Basis. \<alpha> b)"
        by (rule member_le_sum[OF xB]) auto
      also have "\<dots> = n" using a2 by (simp only: ra_deg_def)
      finally show "\<alpha> x \<in> {0..n}" by simp
    next
      fix x :: 'a assume "x \<notin> Basis"
      with a1 show "\<alpha> x = 0" by (auto simp: ra_idx_def)
    qed
    thus "\<alpha> \<in> {hh. \<forall>x::'a. (x \<in> Basis \<longrightarrow> hh x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
      by simp
  qed
  moreover have "finite {hh::'a\<Rightarrow>nat. \<forall>x. (x \<in> Basis \<longrightarrow> hh x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> hh x = (0::nat))}"
    by (rule finite_set_of_finite_funs) auto
  ultimately show ?thesis by (rule finite_subset)
qed

lemma has_sum_imp_bounded_terms:
  fixes g :: "'i \<Rightarrow> 'b::real_normed_vector"
  assumes "(g has_sum S) A"
  obtains M where "M \<ge> 0" and "\<And>a. a \<in> A \<Longrightarrow> norm (g a) \<le> M"
proof -
  have tend: "(sum g \<longlongrightarrow> S) (finite_subsets_at_top A)"
    using assms by (simp only: has_sum_def)
  have "eventually (\<lambda>F. dist (sum g F) S < 1) (finite_subsets_at_top A)"
    by (rule tendstoD[OF tend]) simp
  then obtain F0 where F0: "finite F0" "F0 \<subseteq> A"
    and near: "\<And>F. finite F \<Longrightarrow> F0 \<subseteq> F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> dist (sum g F) S < 1"
    unfolding eventually_finite_subsets_at_top by metis
  define M where "M = (\<Sum>b\<in>F0. norm (g b)) + 2"
  have Mnn: "M \<ge> 0" unfolding M_def by (simp add: sum_nonneg)
  have "norm (g a) \<le> M" if aA: "a \<in> A" for a
  proof (cases "a \<in> F0")
    case True
    have "norm (g a) \<le> (\<Sum>b\<in>F0. norm (g b))"
      using True F0(1) by (intro member_le_sum) auto
    also have "\<dots> \<le> M" unfolding M_def by simp
    finally show ?thesis .
  next
    case False
    have fin1: "finite (insert a F0)" using F0(1) by simp
    have sub1: "insert a F0 \<subseteq> A" using F0(2) aA by simp
    have d1: "dist (sum g (insert a F0)) S < 1" by (rule near[OF fin1 _ sub1]) auto
    have d0: "dist (sum g F0) S < 1" by (rule near[OF F0(1) order_refl F0(2)])
    have "sum g (insert a F0) = g a + sum g F0"
      using False F0(1) by simp
    hence ga: "g a = (sum g (insert a F0) - S) - (sum g F0 - S)" by simp
    have "norm (g a) \<le> norm (sum g (insert a F0) - S) + norm (sum g F0 - S)"
      by (subst ga) (rule norm_triangle_ineq4)
    also have "\<dots> = dist (sum g (insert a F0)) S + dist (sum g F0) S"
      by (simp only: dist_norm)
    also have "\<dots> < 1 + 1" using d1 d0 by simp
    also have "\<dots> \<le> M" unfolding M_def by (simp add: sum_nonneg)
    finally show ?thesis by simp
  qed
  with Mnn that show ?thesis by blast
qed

lemma poly_geom_summable:
  fixes t :: real and p :: nat
  assumes t: "0 \<le> t" "t < 1"
  shows "summable (\<lambda>n. real ((n+1)^p) * t ^ n)"
proof (cases "t = 0")
  case True
  then show ?thesis by (simp add: summable_comparison_test)
next
  case False
  with t have tpos: "0 < t" by simp
  define c where "c = (1 + t) / 2"
  have c1: "c < 1" using t by (simp add: c_def)
  have ct: "t < c" using False t by (simp add: c_def)
  have cpos: "0 < c" using tpos ct by simp
  have base_lim: "(\<lambda>n. real (n+2) / real (n+1)) \<longlonglongrightarrow> 1"
  proof -
    have lim1: "(\<lambda>n. 1 + inverse (real (Suc n))) \<longlonglongrightarrow> 1"
      by (rule LIMSEQ_inverse_real_of_nat_add)
    have "(\<lambda>n. real (n+2)/real(n+1)) = (\<lambda>n. 1 + inverse (real (Suc n)))"
      by (simp add: field_simps)
    with lim1 show ?thesis by simp
  qed
  have ratio_lim: "(\<lambda>n. real ((n+2)^p) / real ((n+1)^p)) \<longlonglongrightarrow> 1"
  proof -
    have "(\<lambda>n. (real (n+2) / real (n+1)) ^ p) \<longlonglongrightarrow> 1 ^ p"
      using base_lim by (rule tendsto_power)
    moreover have "\<And>n. (real (n+2)/real(n+1))^p = real((n+2)^p)/real((n+1)^p)"
      by (simp add: power_divide)
    ultimately show ?thesis by simp
  qed
  have rt: "(\<lambda>n. real ((n+2)^p) / real ((n+1)^p) * t) \<longlonglongrightarrow> t"
  proof -
    have "(\<lambda>n. real ((n+2)^p) / real ((n+1)^p) * t) \<longlonglongrightarrow> 1 * t"
      using ratio_lim tendsto_const by (rule tendsto_mult)
    thus ?thesis by simp
  qed
  have "eventually (\<lambda>n. real ((n+2)^p) / real ((n+1)^p) * t < c) sequentially"
    using rt ct by (intro order_tendstoD(2)) simp_all
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> real ((n+2)^p) / real ((n+1)^p) * t < c"
    by (auto simp: eventually_sequentially)
  show ?thesis
  proof (rule summable_ratio_test[where c = c and N = N])
    show "c < 1" by (rule c1)
    fix n assume "n \<ge> N"
    have ineq: "real ((n+2)^p) / real ((n+1)^p) * t \<le> c" using N[OF \<open>n\<ge>N\<close>] by simp
    have pos1: "(0::real) < real ((n+1)^p)" by simp
    have key: "real ((n+2)^p) * t^(n+1) \<le> c * (real ((n+1)^p) * t^n)"
    proof -
      have "real ((n+2)^p) * t^(n+1)
              = (real ((n+2)^p) / real ((n+1)^p) * t) * (real ((n+1)^p) * t^n)"
        using pos1 tpos by (simp add: field_simps)
      also have "\<dots> \<le> c * (real ((n+1)^p) * t^n)"
        using ineq pos1 tpos by (intro mult_right_mono) (auto simp: zero_le_mult_iff)
      finally show ?thesis .
    qed
    have tnn: "0 \<le> t ^ n" "0 \<le> t ^ (n+1)" using t by (auto intro: zero_le_power)
    have nn1: "0 \<le> real ((n+1)^p) * t^n" using tnn by simp
    have nn2: "0 \<le> real ((n+2)^p) * t^(n+1)" using tnn by simp
    have e1: "real ((Suc n + 1) ^ p) * t ^ Suc n = real ((n+2)^p) * t^(n+1)" by simp
    have "norm (real ((Suc n + 1) ^ p) * t ^ Suc n) = real ((n+2)^p) * t^(n+1)"
      using nn2 by (simp only: e1 real_norm_def abs_of_nonneg)
    also have "\<dots> \<le> c * (real ((n+1)^p) * t^n)" by (rule key)
    also have "\<dots> = c * norm (real ((n + 1) ^ p) * t ^ n)"
      using nn1 by (simp only: real_norm_def abs_of_nonneg)
    finally show "norm (real ((Suc n + 1) ^ p) * t ^ Suc n) \<le> c * norm (real ((n + 1) ^ p) * t ^ n)" .
  qed
qed

lemma ra_lev_card_le:
  fixes n :: nat
  shows "card {\<alpha>::'a::euclidean_space \<Rightarrow> nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n}
           \<le> (n+1) ^ card (Basis :: 'a set)"
proof -
  define G where "G = {hh::'a\<Rightarrow>nat. \<forall>x. (x \<in> Basis \<longrightarrow> hh x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
  have sub: "{\<alpha>::'a \<Rightarrow> nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n} \<subseteq> G"
  proof (rule subsetI)
    fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> {\<alpha>. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n}"
    then have a1: "\<alpha> \<in> ra_idx" and a2: "ra_deg \<alpha> = n" by auto
    have "\<forall>x::'a. (x \<in> Basis \<longrightarrow> \<alpha> x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> \<alpha> x = 0)"
    proof (intro allI conjI impI)
      fix x :: 'a assume xB: "x \<in> Basis"
      have "\<alpha> x \<le> (\<Sum>b\<in>Basis. \<alpha> b)" by (rule member_le_sum[OF xB]) auto
      also have "\<dots> = n" using a2 by (simp add: ra_deg_def)
      finally show "\<alpha> x \<in> {0..n}" by simp
    next
      fix x :: 'a assume "x \<notin> Basis"
      with a1 show "\<alpha> x = 0" by (auto simp: ra_idx_def)
    qed
    thus "\<alpha> \<in> G" by (simp add: G_def)
  qed
  have finG: "finite G" unfolding G_def
    by (rule finite_set_of_finite_funs) auto
  define R where "R = (\<lambda>hh::'a\<Rightarrow>nat. restrict hh (Basis :: 'a set))"
  have Rinj: "inj_on R G"
  proof (rule inj_onI)
    fix x y assume xG: "x \<in> G" and yG: "y \<in> G" and Rxy: "R x = R y"
    show "x = y"
    proof (rule ext)
      fix b :: 'a
      show "x b = y b"
      proof (cases "b \<in> Basis")
        case True
        have "restrict x Basis b = restrict y Basis b" using Rxy by (simp add: R_def)
        thus ?thesis using True by (simp add: restrict_def)
      next
        case False
        with xG yG show ?thesis by (simp add: G_def)
      qed
    qed
  qed
  have Rimg: "R ` G \<subseteq> (Basis :: 'a set) \<rightarrow>\<^sub>E {0..n}"
  proof
    fix g assume "g \<in> R ` G"
    then obtain hh where hh: "hh \<in> G" and g: "g = R hh" by auto
    have "g \<in> extensional Basis" using g by (simp add: R_def)
    moreover have "g \<in> Basis \<rightarrow> {0..n}"
      using hh g by (auto simp: G_def R_def restrict_def)
    ultimately show "g \<in> (Basis :: 'a set) \<rightarrow>\<^sub>E {0..n}"
      by (auto simp: PiE_def)
  qed
  have cardG: "card G \<le> (n+1) ^ card (Basis :: 'a set)"
  proof -
    have finPiE: "finite ((Basis :: 'a set) \<rightarrow>\<^sub>E {0..n})"
      by (rule finite_PiE) auto
    have "card G = card (R ` G)" by (rule card_image[symmetric, OF Rinj])
    also have "\<dots> \<le> card ((Basis :: 'a set) \<rightarrow>\<^sub>E {0..n})"
      by (rule card_mono[OF finPiE Rimg])
    also have "\<dots> = card {0..n} ^ card (Basis :: 'a set)"
      by (rule card_funcsetE) simp
    also have "\<dots> = (n+1) ^ card (Basis :: 'a set)" by simp
    finally show ?thesis .
  qed
  have "card {\<alpha>::'a \<Rightarrow> nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n} \<le> card G"
    by (rule card_mono[OF finG sub])
  with cardG show ?thesis by linarith
qed


subsection \<open>Coefficient bound\<close>

lemma ra_coeff_bound:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes r: "0 < r"
    and HS: "\<And>z. dist z x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum F z) ra_idx"
    and \<rho>pos: "0 < \<rho>"
    and corner: "\<rho> * norm (\<Sum>b\<in>(Basis::'a set). b) < r"
  obtains M where "M \<ge> 0"
    and "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> norm (c \<alpha>) \<le> M / \<rho> ^ (ra_deg \<alpha>)"
proof -
  define e :: 'a where "e = (\<Sum>b\<in>(Basis::'a set). b)"
  define zc where "zc = x0 + \<rho> *\<^sub>R e"
  have dist_zc: "dist zc x0 < r"
  proof -
    have "dist zc x0 = norm (\<rho> *\<^sub>R e)" by (simp add: zc_def dist_norm)
    also have "\<dots> = \<rho> * norm e" using \<rho>pos by simp
    also have "\<dots> < r" using corner by (simp add: e_def)
    finally show ?thesis .
  qed
  have mono_zc: "ra_monomial (zc - x0) \<alpha> = \<rho> ^ (ra_deg \<alpha>)" if "\<alpha> \<in> ra_idx" for \<alpha>
  proof -
    have inner_e: "e \<bullet> b = 1" if "b \<in> (Basis::'a set)" for b
      using that by (simp add: e_def inner_sum_left inner_Basis)
    have "ra_monomial (zc - x0) \<alpha> = (\<Prod>b\<in>Basis. ((\<rho> *\<^sub>R e) \<bullet> b) ^ (\<alpha> b))"
      by (simp add: ra_monomial_def zc_def)
    also have "\<dots> = (\<Prod>b\<in>(Basis::'a set). \<rho> ^ (\<alpha> b))"
      by (rule prod.cong, auto simp: inner_e)
    also have "\<dots> = \<rho> ^ (\<Sum>b\<in>(Basis::'a set). \<alpha> b)"
      by (simp add: power_sum)
    finally show ?thesis by (simp add: ra_deg_def)
  qed
  obtain M0 where Mnn: "M0 \<ge> 0"
    and bound: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> norm (ra_monomial (zc - x0) \<alpha> *\<^sub>R c \<alpha>) \<le> M0"
    using has_sum_imp_bounded_terms[OF HS[OF dist_zc]] by blast
  have final: "norm (c \<alpha>) \<le> M0 / \<rho> ^ (ra_deg \<alpha>)" if a: "\<alpha> \<in> ra_idx" for \<alpha>
  proof -
    have pos: "0 < \<rho> ^ (ra_deg \<alpha>)" using \<rho>pos by simp
    have "\<rho> ^ (ra_deg \<alpha>) * norm (c \<alpha>)
            = norm (ra_monomial (zc - x0) \<alpha> *\<^sub>R c \<alpha>)"
      using mono_zc[OF a] \<rho>pos by simp
    also have "\<dots> \<le> M0" by (rule bound[OF a])
    finally have "\<rho> ^ (ra_deg \<alpha>) * norm (c \<alpha>) \<le> M0" .
    thus ?thesis using pos by (simp add: mult.commute pos_le_divide_eq)
  qed
  show ?thesis by (rule that[OF Mnn final])
qed

lemma ra_monomial_norm_le:
  fixes h :: "'a::euclidean_space"
  assumes "\<alpha> \<in> ra_idx"
  shows "\<bar>ra_monomial h \<alpha>\<bar> \<le> norm h ^ (ra_deg \<alpha>)"
proof -
  have factor: "\<bar>(h \<bullet> b) ^ (\<alpha> b)\<bar> \<le> norm h ^ (\<alpha> b)" if "b \<in> (Basis::'a set)" for b
  proof -
    have "\<bar>(h \<bullet> b) ^ (\<alpha> b)\<bar> = \<bar>h \<bullet> b\<bar> ^ (\<alpha> b)" by (simp add: power_abs)
    also have "\<dots> \<le> norm h ^ (\<alpha> b)"
    proof (rule power_mono)
      have "\<bar>h \<bullet> b\<bar> \<le> norm h * norm b" by (rule Cauchy_Schwarz_ineq2)
      thus "\<bar>h \<bullet> b\<bar> \<le> norm h" using that by simp
      show "0 \<le> \<bar>h \<bullet> b\<bar>" by simp
    qed
    finally show ?thesis .
  qed
  have "\<bar>ra_monomial h \<alpha>\<bar> = \<bar>\<Prod>b\<in>Basis. (h \<bullet> b) ^ (\<alpha> b)\<bar>"
    by (simp add: ra_monomial_def)
  also have "\<dots> = (\<Prod>b\<in>Basis. \<bar>(h \<bullet> b) ^ (\<alpha> b)\<bar>)"
    by (simp add: abs_prod)
  also have "\<dots> \<le> (\<Prod>b\<in>(Basis::'a set). norm h ^ (\<alpha> b))"
    by (rule prod_mono) (auto simp: factor)
  also have "\<dots> = norm h ^ (\<Sum>b\<in>(Basis::'a set). \<alpha> b)"
    by (simp add: power_sum)
  finally show ?thesis by (simp add: ra_deg_def)
qed


subsection \<open>Directional-derivative monomial norm bound\<close>

text \<open>A clean uniform bound on @{const ra_Dmonomial}: for @{term "\<alpha> \<in> ra_idx"} and
  @{term "norm h \<le> s"} with @{term "0 \<le> s"} and @{term "1 \<le> s"} (so powers are monotone),
  @{term \<open>\<bar>ra_Dmonomial h \<alpha> v\<bar> \<le> norm v * real (ra_deg \<alpha>) * s ^ (ra_deg \<alpha>)\<close>}.\<close>

lemma ra_Dmonomial_norm_le:
  fixes h v :: "'a::euclidean_space"
  assumes a: "\<alpha> \<in> ra_idx" and s1: "1 \<le> s" and hs: "norm h \<le> s"
  shows "\<bar>ra_Dmonomial h \<alpha> v\<bar> \<le> norm v * real (ra_deg \<alpha>) * s ^ (ra_deg \<alpha>)"
proof -
  have spos: "0 \<le> s" using s1 by simp
  have hb: "\<bar>h \<bullet> b\<bar> \<le> s" if "b \<in> (Basis::'a set)" for b
  proof -
    have "\<bar>h \<bullet> b\<bar> \<le> norm h * norm b" by (rule Cauchy_Schwarz_ineq2)
    also have "\<dots> = norm h" using that by simp
    also have "\<dots> \<le> s" by (rule hs)
    finally show ?thesis .
  qed
  have vb: "\<bar>v \<bullet> b\<bar> \<le> norm v" if "b \<in> (Basis::'a set)" for b
  proof -
    have "\<bar>v \<bullet> b\<bar> \<le> norm v * norm b" by (rule Cauchy_Schwarz_ineq2)
    thus ?thesis using that by simp
  qed
  \<comment> \<open>each summand of @{const ra_Dmonomial} is bounded\<close>
  have term_le:
    "\<bar>real (\<alpha> b) * (v \<bullet> b) * (h \<bullet> b) ^ (\<alpha> b - 1) *
        (\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d))\<bar>
       \<le> norm v * real (\<alpha> b) * s ^ (ra_deg \<alpha>)"
    if bB: "b \<in> (Basis::'a set)" for b
  proof -
    have e1: "\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> \<le> s ^ (\<alpha> b - 1)"
    proof -
      have "\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> = \<bar>h \<bullet> b\<bar> ^ (\<alpha> b - 1)" by (simp add: power_abs)
      also have "\<dots> \<le> s ^ (\<alpha> b - 1)" using hb[OF bB] by (intro power_mono) auto
      finally show ?thesis .
    qed
    have e2: "\<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar> \<le> (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d))"
    proof -
      have "\<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>
              = (\<Prod>d\<in>Basis - {b}. \<bar>(h \<bullet> d) ^ (\<alpha> d)\<bar>)" by (simp add: abs_prod)
      also have "\<dots> \<le> (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d))"
      proof (rule prod_mono, intro conjI)
        fix d assume dB: "d \<in> Basis - {b}"
        show "0 \<le> \<bar>(h \<bullet> d) ^ (\<alpha> d)\<bar>" by simp
        have "\<bar>(h \<bullet> d) ^ (\<alpha> d)\<bar> = \<bar>h \<bullet> d\<bar> ^ (\<alpha> d)" by (simp add: power_abs)
        also have "\<dots> \<le> s ^ (\<alpha> d)" using hb dB by (intro power_mono) auto
        finally show "\<bar>(h \<bullet> d) ^ (\<alpha> d)\<bar> \<le> s ^ (\<alpha> d)" .
      qed
      finally show ?thesis .
    qed
    have prod_s: "s ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d)) \<le> s ^ (ra_deg \<alpha>)"
    proof -
      have deg_split: "ra_deg \<alpha> = \<alpha> b + (\<Sum>d\<in>Basis - {b}. \<alpha> d)"
        using bB by (simp add: ra_deg_def sum.remove[where x = b])
      have powsum: "(\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d)) = s ^ (\<Sum>d\<in>Basis - {b}. \<alpha> d)"
        by (simp add: power_sum)
      have "s ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d))
              = s ^ ((\<alpha> b - 1) + (\<Sum>d\<in>Basis - {b}. \<alpha> d))"
        by (simp add: powsum power_add)
      also have "\<dots> \<le> s ^ (ra_deg \<alpha>)"
      proof (rule power_increasing)
        show "(\<alpha> b - 1) + (\<Sum>d\<in>Basis - {b}. \<alpha> d) \<le> ra_deg \<alpha>"
          using deg_split by simp
        show "1 \<le> s" by (rule s1)
      qed
      finally show ?thesis .
    qed
    have vbb: "\<bar>v \<bullet> b\<bar> \<le> norm v" by (rule vb[OF bB])
    have nv0: "0 \<le> norm v" by simp
    have absprod_nn: "0 \<le> \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>" by simp
    have abspow_nn: "0 \<le> \<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar>" by simp
    have sprod_nn: "0 \<le> (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d))" using spos by (simp add: prod_nonneg)
    have spow_nn: "0 \<le> s ^ (\<alpha> b - 1)" using spos by simp
    have "\<bar>real (\<alpha> b) * (v \<bullet> b) * (h \<bullet> b) ^ (\<alpha> b - 1) *
            (\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d))\<bar>
            = real (\<alpha> b) * (\<bar>v \<bullet> b\<bar> * (\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> *
                \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>))"
      by (simp add: abs_mult mult.assoc)
    also have "\<dots> \<le> real (\<alpha> b) * (norm v * (s ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d))))"
    proof (rule mult_left_mono)
      have "\<bar>v \<bullet> b\<bar> * (\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>)
              \<le> norm v * (s ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d)))"
      proof (rule mult_mono)
        show "\<bar>v \<bullet> b\<bar> \<le> norm v" by (rule vbb)
        show "\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>
                \<le> s ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d))"
          by (rule mult_mono[OF e1 e2 spow_nn absprod_nn])
        show "0 \<le> norm v" by simp
        show "0 \<le> \<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>"
          by simp
      qed
      thus "\<bar>v \<bullet> b\<bar> * (\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>)
              \<le> norm v * (s ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d)))" .
      show "0 \<le> real (\<alpha> b)" by simp
    qed
    also have "\<dots> = norm v * real (\<alpha> b) * (s ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s ^ (\<alpha> d)))"
      by (simp add: mult.commute mult.left_commute mult.assoc)
    also have "\<dots> \<le> norm v * real (\<alpha> b) * s ^ (ra_deg \<alpha>)"
    proof (rule mult_left_mono[OF prod_s])
      show "0 \<le> norm v * real (\<alpha> b)" by simp
    qed
    finally show ?thesis .
  qed
  have "\<bar>ra_Dmonomial h \<alpha> v\<bar>
          \<le> (\<Sum>b\<in>Basis. \<bar>real (\<alpha> b) * (v \<bullet> b) * (h \<bullet> b) ^ (\<alpha> b - 1) *
                (\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d))\<bar>)"
    unfolding ra_Dmonomial_def by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>b\<in>Basis. norm v * real (\<alpha> b) * s ^ (ra_deg \<alpha>))"
    by (rule sum_mono) (use term_le in simp)
  also have "\<dots> = norm v * (\<Sum>b\<in>Basis. real (\<alpha> b)) * s ^ (ra_deg \<alpha>)"
    by (simp add: sum_distrib_left sum_distrib_right mult.assoc)
  also have "(\<Sum>b\<in>Basis. real (\<alpha> b)) = real (ra_deg \<alpha>)"
    by (simp add: ra_deg_def)
  finally show ?thesis .
qed


subsection \<open>A degree-weighted geometric majorant is summable on @{const ra_idx}\<close>

text \<open>For @{term "0 \<le> q"} and @{term "q < 1"}, the family
  @{term \<open>real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>\<close>} is summable on @{const ra_idx}.  Every
  finite partial sum is bounded, via the level-card estimate @{thm ra_lev_card_le} and the
  poly-geometric series @{thm poly_geom_summable}, by a fixed multiple of the full
  poly-geometric suminf.\<close>

lemma deg_pow_summable:
  fixes q :: real
  assumes q0: "0 \<le> q" and q1: "q < 1"
  shows "(\<lambda>\<alpha>. real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)
           summable_on (ra_idx :: ('a::euclidean_space \<Rightarrow> nat) set)"
proof (rule nonneg_bdd_above_summable_on)
  fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_idx"
  show "0 \<le> real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>" using q0 by simp
next
  define P where "P = card (Basis :: 'a set) + 1"
  define C where "C = (\<Sum>n. real ((n+1)^P) * q ^ n)"
  have pg_sum: "summable (\<lambda>n. real ((n+1)^P) * q ^ n)"
    by (rule poly_geom_summable[OF q0 q1])
  show "bdd_above (sum (\<lambda>\<alpha>. real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)
            ` {F. F \<subseteq> (ra_idx :: ('a \<Rightarrow> nat) set) \<and> finite F})"
  proof (rule bdd_aboveI2)
    fix F :: "('a \<Rightarrow> nat) set" assume "F \<in> {F. F \<subseteq> ra_idx \<and> finite F}"
    then have Fsub: "F \<subseteq> ra_idx" and Ffin: "finite F" by auto
    define D where "D = (if F = {} then 0 else Max (ra_deg ` F))"
    define lev where "lev = (\<lambda>n. {\<alpha>::'a\<Rightarrow>nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n})"
    define gg where "gg = (\<lambda>\<alpha>::'a\<Rightarrow>nat. real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)"
    have ggnn: "0 \<le> gg \<beta>" if "\<beta> \<in> ra_idx" for \<beta>
      using q0 by (simp add: gg_def)
    have Fincl: "F \<subseteq> (\<Union>n\<in>{..D}. lev n)"
    proof
      fix \<beta> assume bF: "\<beta> \<in> F"
      have "ra_deg \<beta> \<le> D"
      proof (cases "F = {}")
        case True thus ?thesis using bF by simp
      next
        case False
        have "ra_deg \<beta> \<le> Max (ra_deg ` F)" using bF Ffin by (intro Max_ge) auto
        thus ?thesis using False by (simp add: D_def)
      qed
      moreover have "\<beta> \<in> ra_idx" using bF Fsub by auto
      ultimately show "\<beta> \<in> (\<Union>n\<in>{..D}. lev n)" by (auto simp: lev_def)
    qed
    have levfin: "finite (lev n)" for n by (simp add: lev_def ra_lev_finite)
    have Ufin: "finite (\<Union>n\<in>{..D}. lev n)" by (auto intro: levfin)
    have "sum gg F \<le> sum gg (\<Union>n\<in>{..D}. lev n)"
      by (rule sum_mono2[OF Ufin Fincl]) (use ggnn in \<open>auto simp: lev_def\<close>)
    also have "sum gg (\<Union>n\<in>{..D}. lev n) = (\<Sum>n\<le>D. sum gg (lev n))"
    proof (rule sum.UNION_disjoint)
      show "finite {..D}" by simp
      show "\<forall>n\<in>{..D}. finite (lev n)" using levfin by simp
      show "\<forall>m\<in>{..D}. \<forall>n\<in>{..D}. m \<noteq> n \<longrightarrow> lev m \<inter> lev n = {}"
        by (auto simp: lev_def)
    qed
    also have "(\<Sum>n\<le>D. sum gg (lev n)) \<le> (\<Sum>n\<le>D. real ((n+1)^P) * q ^ n)"
    proof (rule sum_mono)
      fix n assume "n \<in> {..D}"
      have levn_deg: "ra_deg \<beta> = n" if "\<beta> \<in> lev n" for \<beta>
        using that by (simp add: lev_def)
      have "sum gg (lev n) = (\<Sum>\<beta>\<in>lev n. real (n + 1) * q ^ n)"
        by (rule sum.cong) (auto simp: gg_def levn_deg)
      also have "\<dots> = real (card (lev n)) * (real (n + 1) * q ^ n)" by simp
      also have "\<dots> \<le> real ((n+1) ^ card (Basis::'a set)) * (real (n + 1) * q ^ n)"
      proof (rule mult_right_mono)
        have "card (lev n) \<le> (n+1) ^ card (Basis::'a set)"
          using ra_lev_card_le[of n] by (simp add: lev_def)
        thus "real (card (lev n)) \<le> real ((n+1) ^ card (Basis::'a set))"
          by (simp only: of_nat_le_iff)
        show "0 \<le> real (n + 1) * q ^ n" using q0 by simp
      qed
      also have "\<dots> = real ((n+1)^P) * q ^ n"
      proof -
        have eqp: "(n+1) ^ P = (n+1) ^ card (Basis::'a set) * (n + 1)"
          by (simp add: P_def)
        have req: "real ((n+1) ^ card (Basis::'a set)) * real (n + 1) = real ((n+1) ^ P)"
        proof -
          have "real ((n+1) ^ card (Basis::'a set)) * real (n + 1)
                  = real ((n+1) ^ card (Basis::'a set) * (n + 1))"
            by (simp only: of_nat_mult)
          also have "\<dots> = real ((n+1) ^ P)" using eqp by simp
          finally show ?thesis .
        qed
        have "real ((n+1) ^ card (Basis::'a set)) * (real (n + 1) * q ^ n)
                = (real ((n+1) ^ card (Basis::'a set)) * real (n + 1)) * q ^ n"
          by (simp add: mult.assoc)
        also have "\<dots> = real ((n+1)^P) * q ^ n" by (simp only: req)
        finally show ?thesis .
      qed
      finally show "sum gg (lev n) \<le> real ((n+1)^P) * q ^ n" .
    qed
    also have "(\<Sum>n\<le>D. real ((n+1)^P) * q ^ n) \<le> (\<Sum>n. real ((n+1)^P) * q ^ n)"
      by (rule sum_le_suminf[OF pg_sum]) (auto simp: q0)
    also have "\<dots> = C" by (simp add: C_def)
    finally show "sum (\<lambda>\<alpha>. real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>) F \<le> C"
      by (simp add: gg_def)
  qed
qed


subsection \<open>@{const ra_idx} is countably infinite\<close>

lemma countable_ra_idx: "countable (ra_idx :: ('a::euclidean_space \<Rightarrow> nat) set)"
proof -
  have inj: "inj_on (\<lambda>\<alpha>. restrict \<alpha> (Basis :: 'a set)) ra_idx"
  proof (rule inj_onI)
    fix x y assume xy: "x \<in> ra_idx" "y \<in> ra_idx"
      and eq: "restrict x (Basis::'a set) = restrict y (Basis::'a set)"
    show "x = y"
    proof (rule ext)
      fix b show "x b = y b"
      proof (cases "b \<in> (Basis::'a set)")
        case True
        have "restrict x Basis b = restrict y Basis b" using eq by simp
        thus ?thesis using True by simp
      next
        case False
        have "x b = 0" using xy(1) False by (force simp: ra_idx_def)
        moreover have "y b = 0" using xy(2) False by (force simp: ra_idx_def)
        ultimately show ?thesis by simp
      qed
    qed
  qed
  have img: "(\<lambda>\<alpha>. restrict \<alpha> (Basis :: 'a set)) ` ra_idx \<subseteq> ((Basis::'a set) \<rightarrow>\<^sub>E (UNIV :: nat set))"
    by (auto simp: PiE_def extensional_def restrict_def)
  have cnt: "countable ((Basis::'a set) \<rightarrow>\<^sub>E (UNIV :: nat set))"
    by (rule countable_PiE) auto
  have "countable ((\<lambda>\<alpha>. restrict \<alpha> (Basis :: 'a set)) ` ra_idx)"
    using img cnt by (rule countable_subset)
  thus ?thesis using inj by (rule countable_image_inj_on)
qed

lemma infinite_ra_idx: "infinite (ra_idx :: ('a::euclidean_space \<Rightarrow> nat) set)"
proof -
  obtain j where jB: "j \<in> (Basis :: 'a set)"
    using nonempty_Basis by blast
  define F where "F = (\<lambda>n::nat. (\<lambda>b::'a. if b = j then n else 0))"
  have injF: "inj F"
  proof (rule injI)
    fix m n assume "F m = F n"
    then have "F m j = F n j" by simp
    thus "m = n" by (simp add: F_def)
  qed
  have rng: "range F \<subseteq> ra_idx"
  proof (rule subsetI)
    fix z assume "z \<in> range F"
    then obtain n where z: "z = F n" by auto
    have "{b. z b \<noteq> 0} \<subseteq> {j}" by (auto simp: z F_def split: if_split_asm)
    also have "\<dots> \<subseteq> Basis" using jB by simp
    finally show "z \<in> ra_idx" by (simp add: ra_idx_def)
  qed
  have "infinite (range F)" using injF by (rule range_inj_infinite)
  with rng show ?thesis using finite_subset by blast
qed

definition ra_enum :: "nat \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat)" where
  "ra_enum = from_nat_into (ra_idx :: ('a \<Rightarrow> nat) set)"

lemma bij_ra_enum: "bij_betw (ra_enum :: nat \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat)) UNIV ra_idx"
  unfolding ra_enum_def
  by (rule bij_betw_from_nat_into[OF countable_ra_idx infinite_ra_idx])

lemma ra_enum_in: "ra_enum n \<in> (ra_idx :: ('a::euclidean_space \<Rightarrow> nat) set)"
  using bij_ra_enum by (auto simp: bij_betw_def)

lemma inj_ra_enum: "inj (ra_enum :: nat \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat))"
  using bij_ra_enum by (auto simp: bij_betw_def)

lemma range_ra_enum: "range (ra_enum :: nat \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat)) = ra_idx"
  using bij_betw_imp_surj_on[OF bij_ra_enum] by simp


subsection \<open>Per-coordinate monomial / derivative bounds\<close>

text \<open>If @{term "\<bar>h \<bullet> b\<bar> \<le> s b"} for all @{term "b \<in> Basis"} then
  @{term \<open>\<bar>ra_monomial h \<alpha>\<bar> \<le> (\<Prod>b\<in>Basis. s b ^ (\<alpha> b))\<close>}.\<close>

lemma ra_monomial_norm_le_coord:
  fixes h :: "'a::euclidean_space"
  assumes hb: "\<And>b. b \<in> Basis \<Longrightarrow> \<bar>h \<bullet> b\<bar> \<le> s b"
  shows "\<bar>ra_monomial h \<alpha>\<bar> \<le> (\<Prod>b\<in>Basis. s b ^ (\<alpha> b))"
proof -
  have "\<bar>ra_monomial h \<alpha>\<bar> = (\<Prod>b\<in>Basis. \<bar>(h \<bullet> b) ^ (\<alpha> b)\<bar>)"
    by (simp add: ra_monomial_def abs_prod)
  also have "\<dots> \<le> (\<Prod>b\<in>Basis. s b ^ (\<alpha> b))"
  proof (rule prod_mono, intro conjI)
    fix b assume bB: "b \<in> (Basis::'a set)"
    show "0 \<le> \<bar>(h \<bullet> b) ^ (\<alpha> b)\<bar>" by simp
    have "\<bar>(h \<bullet> b) ^ (\<alpha> b)\<bar> = \<bar>h \<bullet> b\<bar> ^ (\<alpha> b)" by (simp add: power_abs)
    also have "\<dots> \<le> s b ^ (\<alpha> b)" using hb[OF bB] by (intro power_mono) auto
    finally show "\<bar>(h \<bullet> b) ^ (\<alpha> b)\<bar> \<le> s b ^ (\<alpha> b)" .
  qed
  finally show ?thesis .
qed

text \<open>Per-coordinate bound on the directional derivative monomial.\<close>

lemma ra_Dmonomial_norm_le_coord:
  fixes h v :: "'a::euclidean_space"
  assumes hb: "\<And>b. b \<in> Basis \<Longrightarrow> \<bar>h \<bullet> b\<bar> \<le> s b"
    and spos: "\<And>b. b \<in> Basis \<Longrightarrow> 0 < s b"
  shows "\<bar>ra_Dmonomial h \<alpha> v\<bar>
           \<le> norm v * (\<Sum>b\<in>Basis. real (\<alpha> b) / s b) * (\<Prod>b\<in>Basis. s b ^ (\<alpha> b))"
proof -
  have vb: "\<bar>v \<bullet> b\<bar> \<le> norm v" if "b \<in> (Basis::'a set)" for b
  proof -
    have "\<bar>v \<bullet> b\<bar> \<le> norm v * norm b" by (rule Cauchy_Schwarz_ineq2)
    thus ?thesis using that by simp
  qed
  have prodnn: "0 \<le> (\<Prod>d\<in>Basis. s d ^ (\<alpha> d))"
    using spos by (intro prod_nonneg) (auto intro: less_imp_le)
  have term_le:
    "\<bar>real (\<alpha> b) * (v \<bullet> b) * (h \<bullet> b) ^ (\<alpha> b - 1) *
        (\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d))\<bar>
       \<le> norm v * (real (\<alpha> b) / s b) * (\<Prod>d\<in>Basis. s d ^ (\<alpha> d))"
    if bB: "b \<in> (Basis::'a set)" for b
  proof (cases "\<alpha> b = 0")
    case True
    have rhs_nn: "0 \<le> norm v * (real (\<alpha> b) / s b) * (\<Prod>d\<in>Basis. s d ^ (\<alpha> d))"
      using prodnn spos[OF bB] by (simp add: zero_le_mult_iff)
    show ?thesis using True rhs_nn by simp
  next
    case False
    then have a1: "1 \<le> \<alpha> b" by simp
    have sb_pos: "0 < s b" by (rule spos[OF bB])
    \<comment> \<open>absolute value of the b-summand\<close>
    have e1: "\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> \<le> s b ^ (\<alpha> b - 1)"
    proof -
      have "\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> = \<bar>h \<bullet> b\<bar> ^ (\<alpha> b - 1)" by (simp add: power_abs)
      also have "\<dots> \<le> s b ^ (\<alpha> b - 1)" using hb[OF bB] by (intro power_mono) auto
      finally show ?thesis .
    qed
    have e2: "\<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar> \<le> (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))"
    proof -
      have "\<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>
              = (\<Prod>d\<in>Basis - {b}. \<bar>(h \<bullet> d) ^ (\<alpha> d)\<bar>)" by (simp add: abs_prod)
      also have "\<dots> \<le> (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))"
      proof (rule prod_mono, intro conjI)
        fix d assume dB: "d \<in> Basis - {b}"
        show "0 \<le> \<bar>(h \<bullet> d) ^ (\<alpha> d)\<bar>" by simp
        have "\<bar>(h \<bullet> d) ^ (\<alpha> d)\<bar> = \<bar>h \<bullet> d\<bar> ^ (\<alpha> d)" by (simp add: power_abs)
        also have "\<dots> \<le> s d ^ (\<alpha> d)" using hb dB by (intro power_mono) auto
        finally show "\<bar>(h \<bullet> d) ^ (\<alpha> d)\<bar> \<le> s d ^ (\<alpha> d)" .
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>recombine the @{term "s b ^ (\<alpha> b - 1)"} factor into the full product over the @{term \<open>1/s b\<close>}\<close>
    have prod_id: "s b ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))
                    = (1 / s b) * (\<Prod>d\<in>Basis. s d ^ (\<alpha> d))"
    proof -
      have split: "(\<Prod>d\<in>Basis. s d ^ (\<alpha> d))
                     = s b ^ (\<alpha> b) * (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))"
        using bB by (simp add: prod.remove[where x = b])
      have pw: "s b ^ (\<alpha> b) = s b * s b ^ (\<alpha> b - 1)"
        using a1 by (simp add: power_eq_if)
      have "(1 / s b) * (\<Prod>d\<in>Basis. s d ^ (\<alpha> d))
              = (1 / s b) * (s b * s b ^ (\<alpha> b - 1)) * (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))"
        by (simp add: split pw mult.assoc)
      also have "\<dots> = s b ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))"
        using sb_pos by simp
      finally show ?thesis by (rule sym)
    qed
    have abs_eq:
      "\<bar>real (\<alpha> b) * (v \<bullet> b) * (h \<bullet> b) ^ (\<alpha> b - 1) *
          (\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d))\<bar>
        = real (\<alpha> b) * (\<bar>v \<bullet> b\<bar> *
            (\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>))"
      by (simp add: abs_mult mult.assoc)
    have spow_nn: "0 \<le> s b ^ (\<alpha> b - 1)" using sb_pos by simp
    have sprod_nn: "0 \<le> (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))" using spos by (intro prod_nonneg) (auto intro: less_imp_le)
    have absprod_nn: "0 \<le> \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>" by simp
    have "real (\<alpha> b) * (\<bar>v \<bullet> b\<bar> *
            (\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>))
          \<le> real (\<alpha> b) * (norm v *
            (s b ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))))"
    proof (rule mult_left_mono)
      show "\<bar>v \<bullet> b\<bar> * (\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>)
              \<le> norm v * (s b ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d)))"
      proof (rule mult_mono)
        show "\<bar>v \<bullet> b\<bar> \<le> norm v" by (rule vb[OF bB])
        show "\<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>
                \<le> s b ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))"
          by (rule mult_mono[OF e1 e2 spow_nn absprod_nn])
        show "0 \<le> norm v" by simp
        show "0 \<le> \<bar>(h \<bullet> b) ^ (\<alpha> b - 1)\<bar> * \<bar>\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d)\<bar>" by simp
      qed
      show "0 \<le> real (\<alpha> b)" by simp
    qed
    also have "real (\<alpha> b) * (norm v *
            (s b ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. s d ^ (\<alpha> d))))
          = real (\<alpha> b) * (norm v * ((1 / s b) * (\<Prod>d\<in>Basis. s d ^ (\<alpha> d))))"
      by (simp only: prod_id)
    also have "\<dots> = norm v * (real (\<alpha> b) / s b) * (\<Prod>d\<in>Basis. s d ^ (\<alpha> d))"
      by (simp add: field_simps)
    finally show ?thesis using abs_eq by simp
  qed
  have "\<bar>ra_Dmonomial h \<alpha> v\<bar>
          \<le> (\<Sum>b\<in>Basis. \<bar>real (\<alpha> b) * (v \<bullet> b) * (h \<bullet> b) ^ (\<alpha> b - 1) *
                (\<Prod>d\<in>Basis - {b}. (h \<bullet> d) ^ (\<alpha> d))\<bar>)"
    unfolding ra_Dmonomial_def by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>b\<in>Basis. norm v * (real (\<alpha> b) / s b) * (\<Prod>d\<in>Basis. s d ^ (\<alpha> d)))"
    by (rule sum_mono) (use term_le in simp)
  also have "\<dots> = norm v * (\<Sum>b\<in>Basis. real (\<alpha> b) / s b) * (\<Prod>b\<in>Basis. s b ^ (\<alpha> b))"
    by (simp add: sum_distrib_left sum_distrib_right mult.assoc)
  finally show ?thesis .
qed


subsection \<open>Multivariate geometric majorant (single ratio)\<close>

lemma geom_idx_summable:
  fixes q :: real
  assumes q0: "0 \<le> q" and q1: "q < 1"
  shows "(\<lambda>\<alpha>. q ^ ra_deg \<alpha>) summable_on (ra_idx :: ('a::euclidean_space \<Rightarrow> nat) set)"
proof (rule nonneg_bdd_above_summable_on)
  fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_idx"
  show "0 \<le> q ^ ra_deg \<alpha>" using q0 by simp
next
  define Bnd where "Bnd = (1 / (1 - q)) ^ card (Basis :: 'a set)"
  have geom_sum_le: "(\<Sum>k\<le>N. q ^ k) \<le> 1 / (1 - q)" for N
  proof -
    have nq: "norm q < 1" using q0 q1 by simp
    have "(\<Sum>k\<le>N. q ^ k) \<le> (\<Sum>k. q ^ k)"
      by (rule sum_le_suminf) (use q0 nq summable_geometric[of q] in auto)
    also have "\<dots> = 1 / (1 - q)" using nq by (simp add: suminf_geometric)
    finally show ?thesis .
  qed
  have part_bound: "(\<Sum>\<alpha>\<in>F. q ^ ra_deg \<alpha>) \<le> Bnd"
    if F: "F \<subseteq> ra_idx" "finite F" for F :: "('a \<Rightarrow> nat) set"
  proof -
    define N where "N = Max (insert 0 (\<Union>\<alpha>\<in>F. \<alpha> ` (Basis :: 'a set)))"
    have finUN: "finite (insert 0 (\<Union>\<alpha>\<in>F. \<alpha> ` (Basis :: 'a set)))"
      using F(2) by (simp add: finite_UN_I)
    have Nbound: "\<alpha> b \<le> N" if "\<alpha> \<in> F" "b \<in> Basis" for \<alpha> b
    proof -
      have "\<alpha> b \<in> insert 0 (\<Union>\<alpha>\<in>F. \<alpha> ` (Basis :: 'a set))" using that by auto
      thus ?thesis unfolding N_def using finUN by (intro Max_ge)
    qed
    define R where "R = (\<lambda>\<alpha>::'a\<Rightarrow>nat. restrict \<alpha> (Basis :: 'a set))"
    have R_in: "R \<alpha> \<in> Pi\<^sub>E (Basis :: 'a set) (\<lambda>_. {0..N})" if "\<alpha> \<in> F" for \<alpha>
      using that Nbound by (auto simp: R_def PiE_def Pi_def extensional_def)
    have R_deg: "(\<Sum>b\<in>Basis. R \<alpha> b) = ra_deg \<alpha>" for \<alpha>
      by (simp add: R_def ra_deg_def)
    have R_inj: "inj_on R F"
    proof (rule inj_onI)
      fix a b assume ab: "a \<in> F" "b \<in> F" and Req: "R a = R b"
      show "a = b"
      proof (rule ext)
        fix x show "a x = b x"
        proof (cases "x \<in> Basis")
          case True
          have "restrict a Basis x = restrict b Basis x" using Req by (simp add: R_def)
          thus ?thesis using True by simp
        next
          case False
          have "a \<in> ra_idx" "b \<in> ra_idx" using ab F(1) by auto
          then have "a x = 0" "b x = 0" using False by (auto simp: ra_idx_def)
          thus ?thesis by simp
        qed
      qed
    qed
    have "(\<Sum>\<alpha>\<in>F. q ^ ra_deg \<alpha>) = (\<Sum>g\<in>R ` F. q ^ (\<Sum>b\<in>Basis. g b))"
    proof -
      have "(\<Sum>\<alpha>\<in>F. q ^ ra_deg \<alpha>) = (\<Sum>\<alpha>\<in>F. q ^ (\<Sum>b\<in>Basis. R \<alpha> b))"
        by (simp add: R_deg)
      also have "\<dots> = (\<Sum>g\<in>R ` F. q ^ (\<Sum>b\<in>Basis. g b))"
        by (rule sum.reindex_cong[OF R_inj refl, symmetric]) simp
      finally show ?thesis .
    qed
    also have "\<dots> \<le> (\<Sum>g\<in>Pi\<^sub>E (Basis :: 'a set) (\<lambda>_. {0..N}). q ^ (\<Sum>b\<in>Basis. g b))"
    proof (rule sum_mono2)
      show "finite (Pi\<^sub>E (Basis :: 'a set) (\<lambda>_. {0..N}))" by (intro finite_PiE) auto
      show "R ` F \<subseteq> Pi\<^sub>E (Basis :: 'a set) (\<lambda>_. {0..N})" using R_in by auto
      fix g assume "g \<in> Pi\<^sub>E (Basis :: 'a set) (\<lambda>_. {0..N}) - R ` F"
      show "0 \<le> q ^ (\<Sum>b\<in>Basis. g b)" using q0 by simp
    qed
    also have "\<dots> = (\<Sum>g\<in>Pi\<^sub>E (Basis :: 'a set) (\<lambda>_. {0..N}). (\<Prod>b\<in>Basis. q ^ g b))"
      by (intro sum.cong refl) (simp add: power_sum)
    also have "\<dots> = (\<Prod>b\<in>(Basis :: 'a set). \<Sum>k\<in>{0..N}. q ^ k)"
      by (rule prod_sum_PiE[symmetric]) auto
    also have "\<dots> \<le> (\<Prod>b\<in>(Basis :: 'a set). 1 / (1 - q))"
    proof (rule prod_mono)
      fix b :: 'a assume "b \<in> Basis"
      have "0 \<le> (\<Sum>k\<in>{0..N}. q ^ k)" using q0 by (intro sum_nonneg) simp
      moreover have "(\<Sum>k\<in>{0..N}. q ^ k) \<le> 1 / (1 - q)"
        using geom_sum_le[of N] by (simp add: atMost_atLeast0)
      ultimately show "0 \<le> (\<Sum>k\<in>{0..N}. q ^ k) \<and> (\<Sum>k\<in>{0..N}. q ^ k) \<le> 1 / (1 - q)" by blast
    qed
    also have "\<dots> = Bnd" by (simp add: Bnd_def)
    finally show ?thesis .
  qed
  show "bdd_above (sum (\<lambda>\<alpha>. q ^ ra_deg \<alpha>) ` {F. F \<subseteq> (ra_idx :: ('a \<Rightarrow> nat) set) \<and> finite F})"
    by (rule bdd_aboveI2[where M = Bnd]) (use part_bound in auto)
qed


subsection \<open>Per-coordinate coefficient bound\<close>

text \<open>The per-coordinate Cauchy estimate: from the expansion on a ball of radius @{term r}
  about @{term x0}, with a positive radius vector @{term \<rho>} whose corner
  @{term \<open>x0 + (\<Sum>b\<in>Basis. \<rho> b *\<^sub>R b)\<close>} lies inside the ball, the coefficients obey
  @{term \<open>norm (c \<alpha>) \<le> M / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))\<close>}.\<close>

lemma ra_coeff_bound_coord:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes r: "0 < r"
    and HS: "\<And>z. dist z x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum F z) ra_idx"
    and \<rho>pos: "\<And>b. b \<in> Basis \<Longrightarrow> 0 < \<rho> b"
    and corner: "dist (x0 + (\<Sum>b\<in>(Basis::'a set). \<rho> b *\<^sub>R b)) x0 < r"
  obtains M where "M \<ge> 0"
    and "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> norm (c \<alpha>) \<le> M / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))"
proof -
  define zc where "zc = x0 + (\<Sum>b\<in>(Basis::'a set). \<rho> b *\<^sub>R b)"
  have dist_zc: "dist zc x0 < r" using corner by (simp add: zc_def)
  have inner_zc: "(zc - x0) \<bullet> b = \<rho> b" if "b \<in> (Basis::'a set)" for b
  proof -
    have "(zc - x0) \<bullet> b = (\<Sum>d\<in>(Basis::'a set). \<rho> d *\<^sub>R d) \<bullet> b"
      by (simp add: zc_def)
    also have "\<dots> = (\<Sum>d\<in>(Basis::'a set). \<rho> d * (d \<bullet> b))"
      by (simp only: inner_sum_left inner_scaleR_left)
    also have "\<dots> = \<rho> b"
      using that by (simp add: inner_Basis sum.remove[where x = b] cong: if_cong)
    finally show ?thesis .
  qed
  have mono_zc: "ra_monomial (zc - x0) \<alpha> = (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))" for \<alpha>
    by (simp add: ra_monomial_def) (rule prod.cong[OF refl], simp add: inner_zc)
  have prodpos: "0 < (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))" for \<alpha>
    using \<rho>pos by (intro prod_pos) auto
  obtain M0 where Mnn: "M0 \<ge> 0"
    and bound: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> norm (ra_monomial (zc - x0) \<alpha> *\<^sub>R c \<alpha>) \<le> M0"
    using has_sum_imp_bounded_terms[OF HS[OF dist_zc]] by blast
  have final: "norm (c \<alpha>) \<le> M0 / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))" if a: "\<alpha> \<in> ra_idx" for \<alpha>
  proof -
    have pos: "0 < (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))" by (rule prodpos)
    have "(\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b)) * norm (c \<alpha>)
            = norm (ra_monomial (zc - x0) \<alpha> *\<^sub>R c \<alpha>)"
      using mono_zc[of \<alpha>] pos by simp
    also have "\<dots> \<le> M0" by (rule bound[OF a])
    finally have "(\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b)) * norm (c \<alpha>) \<le> M0" .
    thus ?thesis using pos by (simp add: mult.commute pos_le_divide_eq)
  qed
  show ?thesis by (rule that[OF Mnn final])
qed


subsection \<open>Euclidean norm helpers\<close>

lemma norm_sq_eq_sum_coord:
  fixes w :: "'a::euclidean_space"
  shows "(norm w)\<^sup>2 = (\<Sum>b\<in>Basis. (w \<bullet> b)\<^sup>2)"
proof -
  have "(norm w)\<^sup>2 = w \<bullet> w" by (simp add: power2_norm_eq_inner)
  also have "\<dots> = (\<Sum>b\<in>Basis. (w \<bullet> b) * (w \<bullet> b))"
    by (rule euclidean_inner)
  also have "\<dots> = (\<Sum>b\<in>Basis. (w \<bullet> b)\<^sup>2)" by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma norm_basis_combo_sq:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  shows "(norm (\<Sum>b\<in>(Basis::'a set). f b *\<^sub>R b))\<^sup>2 = (\<Sum>b\<in>(Basis::'a set). (f b)\<^sup>2)"
proof -
  have "(norm (\<Sum>b\<in>(Basis::'a set). f b *\<^sub>R b))\<^sup>2
          = (\<Sum>b\<in>(Basis::'a set). ((\<Sum>d\<in>(Basis::'a set). f d *\<^sub>R d) \<bullet> b)\<^sup>2)"
    by (rule norm_sq_eq_sum_coord)
  also have "\<dots> = (\<Sum>b\<in>(Basis::'a set). (f b)\<^sup>2)"
    by (rule sum.cong[OF refl]) simp
  finally show ?thesis .
qed


subsection \<open>Uniform majorant for the differentiated series near an interior point\<close>

text \<open>Around an interior point @{term x} (with @{term \<open>dist x x0 < r\<close>}) there is a ball
  @{term \<open>ball x \<delta>0\<close>}, a single geometric ratio @{term \<open>q < 1\<close>}, and a constant @{term K},
  such that every term of the differentiated series is dominated, uniformly for @{term z}
  in the ball, by the summable majorant @{term \<open>K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>\<close>}.\<close>

lemma diff_majorant_interior:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes r: "0 < r"
    and HS: "\<And>z. dist z x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum F z) ra_idx"
    and x: "dist x x0 < r"
  obtains \<delta>0 q K where
    "0 < \<delta>0" "0 \<le> q" "q < 1" "0 \<le> K"
    and "(\<lambda>\<alpha>. K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>) summable_on ra_idx"
    and "\<And>z. dist z x < \<delta>0 \<Longrightarrow> dist z x0 < r"
    and "\<And>z \<alpha> v. dist z x < \<delta>0 \<Longrightarrow> \<alpha> \<in> ra_idx \<Longrightarrow>
          norm (ra_Dmonomial (z - x0) \<alpha> v *\<^sub>R c \<alpha>)
            \<le> norm v * (K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)"
proof -
  define h0 where "h0 = x - x0"
  have nh0: "norm h0 < r" using x by (simp add: h0_def dist_norm)
  \<comment> \<open>choose a margin @{term \<delta>} so the per-coordinate corner stays inside the ball\<close>
  \<comment> \<open>the corner-squared distance as a function of margin\<close>
  define csq where "csq = (\<lambda>m::real. (\<Sum>b\<in>(Basis::'a set). (\<bar>h0 \<bullet> b\<bar> + 2 * m)\<^sup>2))"
  have csq0: "csq 0 = (norm h0)\<^sup>2"
  proof -
    have "csq 0 = (\<Sum>b\<in>Basis. (h0 \<bullet> b)\<^sup>2)" by (simp add: csq_def)
    also have "\<dots> = (norm h0)\<^sup>2" by (rule norm_sq_eq_sum_coord[symmetric])
    finally show ?thesis .
  qed
  have csq_cont: "csq \<midarrow>0\<rightarrow> csq 0"
    unfolding csq_def by (intro tendsto_intros)
  have "(norm h0)\<^sup>2 < r\<^sup>2" using nh0 by (simp add: power_strict_mono)
  then have csq0lt: "csq 0 < r\<^sup>2" using csq0 by simp
  have ev_at: "\<forall>\<^sub>F m in at 0. csq m < r\<^sup>2"
    by (rule order_tendstoD(2)[OF csq_cont csq0lt])
  have "at_right (0::real) \<le> at 0" by (simp add: at_le)
  then have "\<forall>\<^sub>F m in at_right (0::real). csq m < r\<^sup>2"
    using ev_at by (rule filter_leD)
  then obtain \<delta>1 where \<delta>1pos: "0 < \<delta>1" and csqlt: "\<And>m. 0 < m \<Longrightarrow> m < \<delta>1 \<Longrightarrow> csq m < r\<^sup>2"
    by (auto simp: eventually_at_right_field)
  define \<delta> where "\<delta> = \<delta>1 / 2"
  have \<delta>pos: "0 < \<delta>" using \<delta>1pos by (simp add: \<delta>_def)
  have \<delta>lt: "\<delta> < \<delta>1" using \<delta>1pos by (simp add: \<delta>_def)
  have csq\<delta>: "csq \<delta> < r\<^sup>2" using csqlt[OF \<delta>pos \<delta>lt] .
  \<comment> \<open>the per-coordinate radii\<close>
  define \<rho> where "\<rho> = (\<lambda>b. \<bar>h0 \<bullet> b\<bar> + 2 * \<delta>)"
  define ss where "ss = (\<lambda>b. \<bar>h0 \<bullet> b\<bar> + \<delta>)"
  have \<rho>pos: "0 < \<rho> b" for b using \<delta>pos by (simp add: \<rho>_def)
  have sspos: "0 < ss b" for b using \<delta>pos by (simp add: ss_def)
  have ss_lt_\<rho>: "ss b < \<rho> b" for b using \<delta>pos by (simp add: ss_def \<rho>_def)
  \<comment> \<open>the single geometric ratio: largest of the per-coordinate ratios\<close>
  define q where "q = Max ((\<lambda>b. ss b / \<rho> b) ` (Basis :: 'a set))"
  have finB: "finite ((\<lambda>b. ss b / \<rho> b) ` (Basis :: 'a set))" by simp
  have neB: "((\<lambda>b. ss b / \<rho> b) ` (Basis :: 'a set)) \<noteq> {}"
    using nonempty_Basis by simp
  have q_ge: "ss b / \<rho> b \<le> q" if "b \<in> (Basis::'a set)" for b
    unfolding q_def using that by (intro Max_ge) auto
  have ratio_lt1: "ss b / \<rho> b < 1" for b
    using ss_lt_\<rho>[of b] \<rho>pos[of b] by (simp add: divide_less_eq)
  have ratio_nn: "0 \<le> ss b / \<rho> b" for b
    using sspos[of b] \<rho>pos[of b] by simp
  have q1: "q < 1" unfolding q_def
    using finB neB ratio_lt1 by (subst Max_less_iff) auto
  have q0: "0 \<le> q"
  proof -
    obtain b where "b \<in> (Basis::'a set)" using nonempty_Basis by blast
    thus ?thesis using q_ge[of b] ratio_nn[of b] by linarith
  qed
  \<comment> \<open>corner condition for the coefficient bound\<close>
  have corner: "dist (x0 + (\<Sum>b\<in>(Basis::'a set). \<rho> b *\<^sub>R b)) x0 < r"
  proof -
    have "dist (x0 + (\<Sum>b\<in>(Basis::'a set). \<rho> b *\<^sub>R b)) x0
            = norm (\<Sum>b\<in>(Basis::'a set). \<rho> b *\<^sub>R b)"
      by (simp add: dist_norm)
    also have "\<dots> = sqrt (\<Sum>b\<in>(Basis::'a set). (\<rho> b)\<^sup>2)"
    proof -
      have "(norm (\<Sum>b\<in>(Basis::'a set). \<rho> b *\<^sub>R b))\<^sup>2 = (\<Sum>b\<in>(Basis::'a set). (\<rho> b)\<^sup>2)"
        by (rule norm_basis_combo_sq)
      moreover have "0 \<le> norm (\<Sum>b\<in>(Basis::'a set). \<rho> b *\<^sub>R b)" by simp
      ultimately show ?thesis by (metis real_sqrt_unique)
    qed
    also have "(\<Sum>b\<in>(Basis::'a set). (\<rho> b)\<^sup>2) = csq \<delta>"
      by (simp add: csq_def \<rho>_def)
    also have "sqrt (csq \<delta>) < sqrt (r\<^sup>2)"
      using csq\<delta> by (intro real_sqrt_less_mono)
    also have "sqrt (r\<^sup>2) = r" using r by simp
    finally show ?thesis .
  qed
  \<comment> \<open>the per-coordinate coefficient bound\<close>
  obtain M where Mnn: "M \<ge> 0"
    and cbound: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> norm (c \<alpha>) \<le> M / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))"
    using ra_coeff_bound_coord[OF r HS \<rho>pos corner] by blast
  define K where "K = M / \<delta>"
  have Knn: "0 \<le> K" using Mnn \<delta>pos by (simp add: K_def)
  \<comment> \<open>summability of the majorant\<close>
  have maj_summ: "(\<lambda>\<alpha>. K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>) summable_on ra_idx"
  proof -
    have "(\<lambda>\<alpha>. real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>) summable_on ra_idx"
      by (rule deg_pow_summable[OF q0 q1])
    then have "(\<lambda>\<alpha>. K * (real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)) summable_on ra_idx"
      by (rule summable_on_cmult_right)
    thus ?thesis by (simp add: mult.assoc)
  qed
  \<comment> \<open>the in-ball implication and the uniform term bound\<close>
  have inball: "dist z x0 < r" if dz: "dist z x < \<delta>" for z
  proof -
    \<comment> \<open>Bound coordinatewise, then sum-of-squares.\<close>
    have coordb: "\<bar>(z - x0) \<bullet> b\<bar> \<le> ss b" if "b \<in> (Basis::'a set)" for b
    proof -
      have "\<bar>(z - x0) \<bullet> b\<bar> = \<bar>(z - x) \<bullet> b + h0 \<bullet> b\<bar>"
        by (simp add: h0_def inner_diff_left)
      also have "\<dots> \<le> \<bar>(z - x) \<bullet> b\<bar> + \<bar>h0 \<bullet> b\<bar>" by (rule abs_triangle_ineq)
      also have "\<bar>(z - x) \<bullet> b\<bar> \<le> norm (z - x)"
      proof -
        have "\<bar>(z - x) \<bullet> b\<bar> \<le> norm (z - x) * norm b" by (rule Cauchy_Schwarz_ineq2)
        thus ?thesis using that by simp
      qed
      also have "norm (z - x) < \<delta>" using dz by (simp add: dist_norm)
      finally show ?thesis by (simp add: ss_def)
    qed
    have "(norm (z - x0))\<^sup>2 = (\<Sum>b\<in>(Basis::'a set). ((z - x0) \<bullet> b)\<^sup>2)"
      by (rule norm_sq_eq_sum_coord)
    also have "\<dots> \<le> (\<Sum>b\<in>(Basis::'a set). (ss b)\<^sup>2)"
    proof (rule sum_mono)
      fix b assume bB: "b \<in> (Basis::'a set)"
      have "((z - x0) \<bullet> b)\<^sup>2 = \<bar>(z - x0) \<bullet> b\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (ss b)\<^sup>2"
        using coordb[OF bB] sspos[of b] by (intro power_mono) auto
      finally show "((z - x0) \<bullet> b)\<^sup>2 \<le> (ss b)\<^sup>2" .
    qed
    also have "(\<Sum>b\<in>(Basis::'a set). (ss b)\<^sup>2) < (\<Sum>b\<in>(Basis::'a set). (\<rho> b)\<^sup>2)"
    proof (rule sum_strict_mono)
      show "finite (Basis :: 'a set)" by simp
      show "(Basis :: 'a set) \<noteq> {}" using nonempty_Basis by simp
      fix b assume "b \<in> (Basis::'a set)"
      show "(ss b)\<^sup>2 < (\<rho> b)\<^sup>2"
        using ss_lt_\<rho>[of b] sspos[of b] \<rho>pos[of b] by (intro power_strict_mono) auto
    qed
    also have "(\<Sum>b\<in>(Basis::'a set). (\<rho> b)\<^sup>2) = csq \<delta>" by (simp add: csq_def \<rho>_def)
    also have "csq \<delta> < r\<^sup>2" by (rule csq\<delta>)
    finally have nlt: "(norm (z - x0))\<^sup>2 < r\<^sup>2" .
    have "norm (z - x0) < r"
      by (rule power2_less_imp_less[OF nlt]) (simp add: r less_imp_le)
    thus ?thesis by (simp add: dist_norm)
  qed
  have termbound:
    "norm (ra_Dmonomial (z - x0) \<alpha> v *\<^sub>R c \<alpha>)
       \<le> norm v * (K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)"
    if dz: "dist z x < \<delta>" and a: "\<alpha> \<in> ra_idx" for z \<alpha> v
  proof -
    have coordb: "\<bar>(z - x0) \<bullet> b\<bar> \<le> ss b" if "b \<in> (Basis::'a set)" for b
    proof -
      have "\<bar>(z - x0) \<bullet> b\<bar> = \<bar>(z - x) \<bullet> b + h0 \<bullet> b\<bar>"
        by (simp add: h0_def inner_diff_left)
      also have "\<dots> \<le> \<bar>(z - x) \<bullet> b\<bar> + \<bar>h0 \<bullet> b\<bar>" by (rule abs_triangle_ineq)
      also have "\<bar>(z - x) \<bullet> b\<bar> \<le> norm (z - x)"
      proof -
        have "\<bar>(z - x) \<bullet> b\<bar> \<le> norm (z - x) * norm b" by (rule Cauchy_Schwarz_ineq2)
        thus ?thesis using that by simp
      qed
      also have "norm (z - x) < \<delta>" using dz by (simp add: dist_norm)
      finally show ?thesis by (simp add: ss_def)
    qed
    \<comment> \<open>the directional-derivative magnitude\<close>
    have Dbound: "\<bar>ra_Dmonomial (z - x0) \<alpha> v\<bar>
                    \<le> norm v * (\<Sum>b\<in>Basis. real (\<alpha> b) / ss b) * (\<Prod>b\<in>Basis. ss b ^ (\<alpha> b))"
      by (rule ra_Dmonomial_norm_le_coord[OF coordb sspos])
    \<comment> \<open>bound the coordinate-weighted sum factor\<close>
    have sumfac: "(\<Sum>b\<in>Basis. real (\<alpha> b) / ss b) \<le> real (ra_deg \<alpha>) / \<delta>"
    proof -
      have "(\<Sum>b\<in>(Basis::'a set). real (\<alpha> b) / ss b) \<le> (\<Sum>b\<in>(Basis::'a set). real (\<alpha> b) / \<delta>)"
      proof (rule sum_mono)
        fix b assume bB: "b \<in> (Basis::'a set)"
        have "\<delta> \<le> ss b" by (simp add: ss_def)
        thus "real (\<alpha> b) / ss b \<le> real (\<alpha> b) / \<delta>"
          using \<delta>pos sspos[of b] by (intro divide_left_mono) (auto simp: zero_le_mult_iff)
      qed
      also have "\<dots> = (\<Sum>b\<in>(Basis::'a set). real (\<alpha> b)) / \<delta>"
        by (simp add: sum_divide_distrib)
      also have "(\<Sum>b\<in>(Basis::'a set). real (\<alpha> b)) = real (ra_deg \<alpha>)"
        by (simp add: ra_deg_def)
      finally show ?thesis .
    qed
    \<comment> \<open>bound the product factor times the coefficient norm\<close>
    have prodq: "(\<Prod>b\<in>Basis. ss b ^ (\<alpha> b)) / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b)) \<le> q ^ ra_deg \<alpha>"
    proof -
      have prodpos: "0 < (\<Prod>b\<in>(Basis::'a set). \<rho> b ^ (\<alpha> b))"
        using \<rho>pos by (intro prod_pos) auto
      have "(\<Prod>b\<in>Basis. ss b ^ (\<alpha> b)) / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))
              = (\<Prod>b\<in>(Basis::'a set). (ss b / \<rho> b) ^ (\<alpha> b))"
        by (simp add: prod_dividef power_divide)
      also have "\<dots> \<le> (\<Prod>b\<in>(Basis::'a set). q ^ (\<alpha> b))"
      proof (rule prod_mono, intro conjI)
        fix b assume bB: "b \<in> (Basis::'a set)"
        show "0 \<le> (ss b / \<rho> b) ^ (\<alpha> b)" using ratio_nn[of b] by simp
        show "(ss b / \<rho> b) ^ (\<alpha> b) \<le> q ^ (\<alpha> b)"
          using q_ge[OF bB] ratio_nn[of b] by (intro power_mono) auto
      qed
      also have "\<dots> = q ^ (\<Sum>b\<in>(Basis::'a set). \<alpha> b)" by (simp add: power_sum)
      finally show ?thesis by (simp add: ra_deg_def)
    qed
    \<comment> \<open>assemble\<close>
    have prodpos: "0 < (\<Prod>b\<in>(Basis::'a set). \<rho> b ^ (\<alpha> b))"
      using \<rho>pos by (intro prod_pos) auto
    have ssprod_nn: "0 \<le> (\<Prod>b\<in>(Basis::'a set). ss b ^ (\<alpha> b))"
      using sspos by (intro prod_nonneg) (auto intro: less_imp_le)
    have deg_nn: "0 \<le> (\<Sum>b\<in>(Basis::'a set). real (\<alpha> b) / ss b)"
      by (intro sum_nonneg) (simp add: sspos less_imp_le)
    have "norm (ra_Dmonomial (z - x0) \<alpha> v *\<^sub>R c \<alpha>)
            = \<bar>ra_Dmonomial (z - x0) \<alpha> v\<bar> * norm (c \<alpha>)"
      by (simp only: norm_scaleR)
    also have "\<dots> \<le> (norm v * (\<Sum>b\<in>Basis. real (\<alpha> b) / ss b) * (\<Prod>b\<in>Basis. ss b ^ (\<alpha> b)))
                      * (M / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b)))"
    proof (rule mult_mono[OF Dbound cbound[OF a]])
      show "0 \<le> norm v * (\<Sum>b\<in>Basis. real (\<alpha> b) / ss b) * (\<Prod>b\<in>Basis. ss b ^ (\<alpha> b))"
        using deg_nn ssprod_nn by (simp add: zero_le_mult_iff)
      show "0 \<le> norm (c \<alpha>)" by simp
    qed
    also have "\<dots> = norm v * (\<Sum>b\<in>Basis. real (\<alpha> b) / ss b) * M
                      * ((\<Prod>b\<in>Basis. ss b ^ (\<alpha> b)) / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b)))"
      by (simp add: field_simps)
    also have "\<dots> \<le> norm v * (real (ra_deg \<alpha>) / \<delta>) * M * (q ^ ra_deg \<alpha>)"
    proof -
      have le1: "norm v * (\<Sum>b\<in>Basis. real (\<alpha> b) / ss b) * M \<le> norm v * (real (ra_deg \<alpha>) / \<delta>) * M"
      proof -
        have "norm v * (\<Sum>b\<in>Basis. real (\<alpha> b) / ss b) \<le> norm v * (real (ra_deg \<alpha>) / \<delta>)"
          by (rule mult_left_mono[OF sumfac]) simp
        thus ?thesis by (rule mult_right_mono[OF _ Mnn])
      qed
      have nn_b: "0 \<le> norm v * (real (ra_deg \<alpha>) / \<delta>) * M"
        using \<delta>pos Mnn by (simp add: zero_le_mult_iff)
      have nn_c: "0 \<le> (\<Prod>b\<in>Basis. ss b ^ (\<alpha> b)) / (\<Prod>b\<in>Basis. \<rho> b ^ (\<alpha> b))"
        using ssprod_nn prodpos by (simp add: zero_le_divide_iff)
      show ?thesis by (rule mult_mono[OF le1 prodq nn_b nn_c])
    qed
    also have "\<dots> = norm v * (K * real (ra_deg \<alpha>) * q ^ ra_deg \<alpha>)"
      by (simp add: K_def field_simps)
    also have "\<dots> \<le> norm v * (K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)"
    proof (rule mult_left_mono)
      have "K * real (ra_deg \<alpha>) * q ^ ra_deg \<alpha> \<le> K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>"
        using Knn q0 by (intro mult_right_mono mult_left_mono) auto
      thus "K * real (ra_deg \<alpha>) * q ^ ra_deg \<alpha> \<le> K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>" .
      show "0 \<le> norm v" by simp
    qed
    finally show ?thesis .
  qed
  show ?thesis
    by (rule that[OF \<delta>pos q0 q1 Knn maj_summ inball termbound])
qed


subsection \<open>Core #7: term-by-term differentiation\<close>

theorem ra_power_series_has_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series: "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f y) ra_idx"
    and x: "dist x x0 < r"
  shows
    "(f has_derivative
       (\<lambda>v. infsum (\<lambda>\<alpha>. ra_Dmonomial (x - x0) \<alpha> v *\<^sub>R c \<alpha>) ra_idx))
      (at x)"
proof -
  \<comment> \<open>uniform majorant near @{term x}\<close>
  obtain \<delta>0 q K where \<delta>0: "0 < \<delta>0" and q0: "0 \<le> q" and q1: "q < 1" and Knn: "0 \<le> K"
    and majsumm: "(\<lambda>\<alpha>. K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>) summable_on ra_idx"
    and inball: "\<And>z. dist z x < \<delta>0 \<Longrightarrow> dist z x0 < r"
    and tbound: "\<And>z \<alpha> v. dist z x < \<delta>0 \<Longrightarrow> \<alpha> \<in> ra_idx \<Longrightarrow>
          norm (ra_Dmonomial (z - x0) \<alpha> v *\<^sub>R c \<alpha>)
            \<le> norm v * (K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)"
    using diff_majorant_interior[OF r series x] by blast
  define D where "D = (\<lambda>\<alpha>::'a\<Rightarrow>nat. K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)"
  have Dnn: "0 \<le> D \<alpha>" for \<alpha> using Knn q0 by (simp add: D_def)
  have D_summ: "D summable_on ra_idx" unfolding D_def using majsumm
    by (metis (lifting) ext deg_pow_summable q0 q1 summable_on_cmult_right
        vector_space_over_itself.scale_scale) 
  define S where "S = ball x \<delta>0"
  have convS: "convex S" by (simp add: S_def)
  have xS: "x \<in> S" using \<delta>0 by (simp add: S_def)
  have openS: "open S" by (simp add: S_def)
  have S_ball: "\<And>z. z \<in> S \<Longrightarrow> dist z x < \<delta>0" by (simp add: S_def dist_commute)
  have S_in_r: "\<And>z. z \<in> S \<Longrightarrow> dist z x0 < r" using inball S_ball by blast
  \<comment> \<open>the enumeration of @{term ra_idx}\<close>
  define en where "en = (ra_enum :: nat \<Rightarrow> ('a \<Rightarrow> nat))"
  have en_in: "en k \<in> ra_idx" for k by (simp add: en_def ra_enum_in)
  have en_inj: "inj en" by (simp add: en_def inj_ra_enum)
  have en_rng: "range en = ra_idx" by (simp add: en_def range_ra_enum)
  \<comment> \<open>partial sums and their derivatives\<close>
  define fn where "fn = (\<lambda>n z. \<Sum>k<n. ra_monomial (z - x0) (en k) *\<^sub>R c (en k))"
  define f'n where
    "f'n = (\<lambda>n z w. \<Sum>k<n. ra_Dmonomial (z - x0) (en k) w *\<^sub>R c (en k))"
  define g' where "g' = (\<lambda>z w. infsum (\<lambda>\<alpha>. ra_Dmonomial (z - x0) \<alpha> w *\<^sub>R c \<alpha>) ra_idx)"
  \<comment> \<open>each @{term \<open>fn n\<close>} has derivative @{term \<open>f'n n z\<close>} at @{term z}\<close>
  have derfn: "((fn n) has_derivative (f'n n z)) (at z within S)" for n z
  proof -
    have "((\<lambda>z. \<Sum>k<n. ra_monomial (z - x0) (en k) *\<^sub>R c (en k))
            has_derivative (\<lambda>w. \<Sum>k<n. ra_Dmonomial (z - x0) (en k) w *\<^sub>R c (en k))) (at z)"
      by (rule has_derivative_sum)
         (rule ra_shifted_term_has_derivative)
    then have "((fn n) has_derivative (f'n n z)) (at z)"
      by (simp add: fn_def f'n_def)
    thus ?thesis by (rule has_derivative_at_withinI)
  qed
  \<comment> \<open>for each @{term z} in @{term S}, the term family (over @{term ra_idx}) is summable,
     hence reindexes to a {term sums} along @{term en}; partial sums @{term \<open>fn n z\<close>}
     converge to @{term \<open>f z\<close>}\<close>
  have termsum_z: "((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f z) ra_idx"
    if "z \<in> S" for z using series[OF S_in_r[OF that]] .
  have fn_lim: "(\<lambda>n. fn n z) \<longlonglongrightarrow> f z" if zS: "z \<in> S" for z
  proof -
    have "((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f z) (range en)"
      using termsum_z[OF zS] by (simp add: en_rng)
    then have "((\<lambda>k. ra_monomial (z - x0) (en k) *\<^sub>R c (en k)) has_sum f z) UNIV"
      using en_inj by (subst (asm) has_sum_reindex) (auto simp: o_def)
    then have "(\<lambda>k. ra_monomial (z - x0) (en k) *\<^sub>R c (en k)) sums f z"
      by (rule has_sum_imp_sums)
    thus ?thesis by (simp add: fn_def sums_def)
  qed
  \<comment> \<open>for each @{term z} in @{term S} and direction @{term w}, the derivative family is
     norm-summable (dominated by @{term \<open>norm w *\<^sub>R D\<close>}); its infsum is @{term \<open>g' z w\<close>}.\<close>
  have Dsummf: "(\<lambda>\<alpha>. ra_Dmonomial (z - x0) \<alpha> w *\<^sub>R c \<alpha>) summable_on ra_idx"
    if zS: "z \<in> S" for z w
  proof (rule abs_summable_summable, rule summable_on_comparison_test
            [where f = "\<lambda>\<alpha>. norm w * D \<alpha>"])
    show "(\<lambda>\<alpha>. norm w * D \<alpha>) summable_on ra_idx"
      by (rule summable_on_cmult_right[OF D_summ])
  next
    fix \<alpha> :: "'a \<Rightarrow> nat" assume a: "\<alpha> \<in> ra_idx"
    show "norm (ra_Dmonomial (z - x0) \<alpha> w *\<^sub>R c \<alpha>) \<le> norm w * D \<alpha>"
      using tbound[OF S_ball[OF zS] a] by (simp add: D_def)
  next
    fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_idx"
    show "0 \<le> norm (ra_Dmonomial (z - x0) \<alpha> w *\<^sub>R c \<alpha>)" by simp
  qed
  have g'sums: "(\<lambda>k. ra_Dmonomial (z - x0) (en k) w *\<^sub>R c (en k)) sums g' z w"
    if zS: "z \<in> S" for z w
  proof -
    have "((\<lambda>\<alpha>. ra_Dmonomial (z - x0) \<alpha> w *\<^sub>R c \<alpha>) has_sum g' z w) ra_idx"
      unfolding g'_def using Dsummf[OF zS] by (rule has_sum_infsum)
    then have "((\<lambda>\<alpha>. ra_Dmonomial (z - x0) \<alpha> w *\<^sub>R c \<alpha>) has_sum g' z w) (range en)"
      by (simp add: en_rng)
    then have "((\<lambda>k. ra_Dmonomial (z - x0) (en k) w *\<^sub>R c (en k)) has_sum g' z w) UNIV"
      using en_inj by (subst (asm) has_sum_reindex) (auto simp: o_def)
    thus ?thesis by (rule has_sum_imp_sums)
  qed
  \<comment> \<open>the majorant series, reindexed along @{term en}, is summable on @{term UNIV}\<close>
  have Den_summ: "summable (\<lambda>k. D (en k))"
  proof -
    have "(D has_sum (infsum D ra_idx)) ra_idx" using D_summ by (rule has_sum_infsum)
    then have "(D has_sum (infsum D ra_idx)) (range en)" by (simp add: en_rng)
    then have "((D \<circ> en) has_sum (infsum D ra_idx)) UNIV"
      using en_inj by (subst (asm) has_sum_reindex)
    then have "(D \<circ> en) sums (infsum D ra_idx)" by (rule has_sum_imp_sums)
    thus ?thesis by (auto simp: o_def summable_def)
  qed
  \<comment> \<open>the uniform-derivative condition for @{thm has_derivative_sequence}\<close>
  have unif: "\<forall>\<^sub>F n in sequentially. \<forall>z\<in>S. \<forall>w. norm (f'n n z w - g' z w) \<le> e * norm w"
    if epos: "0 < e" for e
  proof -
    obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> norm (\<Sum>i. D (en (i + n))) < e"
      using suminf_exist_split[OF epos Den_summ] by blast
    have key: "norm (f'n n z w - g' z w) \<le> e * norm w"
      if nN: "n \<ge> N" and zS: "z \<in> S" for n z w
    proof -
      define gk where "gk = (\<lambda>k. ra_Dmonomial (z - x0) (en k) w *\<^sub>R c (en k))"
      have gk_sums: "gk sums g' z w" using g'sums[OF zS] by (simp add: gk_def)
      have gk_summ: "summable gk" using gk_sums by (simp add: sums_summable)
      have gknorm_le: "norm (gk k) \<le> norm w * D (en k)" for k
        using tbound[OF S_ball[OF zS] en_in[of k]] by (simp add: gk_def D_def)
      \<comment> \<open>norm-summability of @{term gk} via comparison\<close>
      have gknorm_summ: "summable (\<lambda>k. norm (gk k))"
      proof (rule summable_comparison_test')
        show "summable (\<lambda>k. norm w * D (en k))"
          by (rule summable_mult[OF Den_summ])
        fix k show "norm (norm (gk k)) \<le> norm w * D (en k)"
          using gknorm_le[of k] by simp
      qed
      \<comment> \<open>the tail estimate\<close>
      have "norm (f'n n z w - g' z w) = norm ((\<Sum>k<n. gk k) - g' z w)"
        by (simp add: f'n_def gk_def)
      also have "\<dots> = norm (\<Sum>i. gk (i + n))"
      proof -
        have "(\<Sum>i. gk (i + n)) = g' z w - (\<Sum>k<n. gk k)"
          using sums_split_initial_segment[OF gk_sums, of n] by (simp add: sums_iff)
        thus ?thesis by (simp add: norm_minus_commute)
      qed
      also have "\<dots> \<le> (\<Sum>i. norm (gk (i + n)))"
      proof (rule summable_norm)
        show "summable (\<lambda>i. norm (gk (i + n)))"
          using gknorm_summ by (rule summable_ignore_initial_segment[where k = n])
      qed
      also have "\<dots> \<le> (\<Sum>i. norm w * D (en (i + n)))"
      proof (rule suminf_le)
        show "\<And>i. norm (gk (i + n)) \<le> norm w * D (en (i + n))" using gknorm_le by simp
        show "summable (\<lambda>i. norm (gk (i + n)))"
          using gknorm_summ by (rule summable_ignore_initial_segment[where k = n])
        show "summable (\<lambda>i. norm w * D (en (i + n)))"
        proof -
          have "summable (\<lambda>k. norm w * D (en k))" by (rule summable_mult[OF Den_summ])
          thus ?thesis by (rule summable_ignore_initial_segment[where k = n])
        qed
      qed
      also have "\<dots> = norm w * (\<Sum>i. D (en (i + n)))"
        by (rule suminf_mult)
           (rule summable_ignore_initial_segment[OF Den_summ, where k = n, simplified])
      also have "\<dots> \<le> norm w * e"
      proof (rule mult_left_mono)
        have "(\<Sum>i. D (en (i + n))) \<le> norm (\<Sum>i. D (en (i + n)))" by simp
        also have "\<dots> < e" by (rule N[OF nN])
        finally show "(\<Sum>i. D (en (i + n))) \<le> e" by simp
        show "0 \<le> norm w" by simp
      qed
      finally show ?thesis by (simp only: mult.commute)
    qed
    show ?thesis
      unfolding eventually_sequentially using key by blast
  qed
  \<comment> \<open>apply @{thm has_derivative_sequence}\<close>
  have basept: "(\<lambda>n. fn n x) \<longlonglongrightarrow> f x" by (rule fn_lim[OF xS])
  obtain g where g: "\<And>z. z \<in> S \<Longrightarrow> (\<lambda>n. fn n z) \<longlonglongrightarrow> g z \<and> (g has_derivative g' z) (at z within S)"
    using has_derivative_sequence[OF convS derfn unif xS basept] by metis
  \<comment> \<open>@{term g} agrees with @{term f} on @{term S}\<close>
  have g_eq_f: "g z = f z" if zS: "z \<in> S" for z
    using g[OF zS] fn_lim[OF zS] LIMSEQ_unique by blast
  have hd_g_within: "(g has_derivative g' x) (at x within S)" using g[OF xS] by blast
  have atSx: "at x within S = at x" using openS xS by (subst at_within_open, simp_all)
  have hd_g_at: "(g has_derivative g' x) (at x)" using hd_g_within by (simp only: atSx)
  \<comment> \<open>transfer to @{term f}\<close>
  have "(f has_derivative g' x) (at x)"
    by (rule has_derivative_transform_within_open[OF hd_g_at openS xS])
       (simp add: g_eq_f)
  thus ?thesis by (simp only: g'_def)
qed


(* ===================== Lemma #2 + #6 infrastructure (merged from reindex) ===================== *)

subsection \<open>Local copy of @{text ra_inc_in_idx} (lemma #2)\<close>

lemma ra_inc_in_idx:
  fixes \<alpha> :: "'a::euclidean_space \<Rightarrow> nat"
  assumes "\<alpha> \<in> ra_idx" and "b \<in> Basis"
  shows "ra_inc \<alpha> b \<in> ra_idx"
proof -
  have "{c. ra_inc \<alpha> b c \<noteq> 0} \<subseteq> {c. \<alpha> c \<noteq> 0} \<union> {b}"
    by (auto simp: ra_inc_def)
  also have "\<dots> \<subseteq> Basis"
    using assms by (auto simp: ra_idx_def)
  finally show ?thesis by (simp add: ra_idx_def)
qed


subsection \<open>Decrement is the inverse of @{const ra_inc} on the support slice\<close>

definition ra_dec ::
  "('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> nat)" where
  "ra_dec \<alpha> b = \<alpha>(b := \<alpha> b - 1)"

lemma ra_dec_in_idx:
  fixes \<alpha> :: "'a::euclidean_space \<Rightarrow> nat"
  assumes "\<alpha> \<in> ra_idx"
  shows "ra_dec \<alpha> b \<in> ra_idx"
proof -
  have "{c. ra_dec \<alpha> b c \<noteq> 0} \<subseteq> {c. \<alpha> c \<noteq> 0}"
    by (auto simp: ra_dec_def)
  also have "\<dots> \<subseteq> Basis" using assms by (auto simp: ra_idx_def)
  finally show ?thesis by (simp add: ra_idx_def)
qed

lemma ra_inc_dec:
  assumes "1 \<le> \<alpha> b"
  shows "ra_inc (ra_dec \<alpha> b) b = \<alpha>"
  using assms by (auto simp: ra_inc_def ra_dec_def fun_eq_iff)

lemma ra_dec_inc:
  "ra_dec (ra_inc \<alpha> b) b = \<alpha>"
  by (auto simp: ra_inc_def ra_dec_def fun_eq_iff)


subsection \<open>Splitting a monomial off one basis direction\<close>

lemma ra_monomial_split:
  fixes x :: "'a::euclidean_space"
  assumes "b \<in> Basis"
  shows "ra_monomial x \<beta>
          = (x \<bullet> b) ^ (\<beta> b) * (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<beta> d))"
  unfolding ra_monomial_def
  by (subst prod.remove[OF finite_Basis assms]) simp


subsection \<open>The per-basis LHS and RHS pieces\<close>

definition Ppiece ::
  "'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'b"
  where
  "Ppiece x v c b \<alpha> =
     (real (\<alpha> b) * (v \<bullet> b) * (x \<bullet> b) ^ (\<alpha> b - 1) *
        (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<alpha> d))) *\<^sub>R c \<alpha>"

definition Qpiece ::
  "'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'b"
  where
  "Qpiece x v c b \<beta> =
     (real (Suc (\<beta> b)) * (v \<bullet> b)) *\<^sub>R (ra_monomial x \<beta> *\<^sub>R c (ra_inc \<beta> b))"

lemma Dmonomial_eq_sum_Ppiece:
  fixes x v :: "'a::euclidean_space"
  shows "ra_Dmonomial x \<alpha> v *\<^sub>R c \<alpha> = (\<Sum>b\<in>Basis. Ppiece x v c b \<alpha>)"
  unfolding ra_Dmonomial_def Ppiece_def
  by (simp add: scaleR_sum_left)

lemma dcoeff_eq_sum_Qpiece:
  fixes x v :: "'a::euclidean_space"
  shows "ra_monomial x \<alpha> *\<^sub>R ra_dcoeff c v \<alpha> = (\<Sum>b\<in>Basis. Qpiece x v c b \<alpha>)"
  unfolding ra_dcoeff_def Qpiece_def
  by (simp add: scaleR_right.sum) (simp add: algebra_simps)

text \<open>Key pointwise identity: the LHS piece at @{term "ra_inc \<beta> b"} equals the RHS piece at
  @{term \<beta>}.\<close>

lemma Ppiece_inc_eq_Qpiece:
  fixes x v :: "'a::euclidean_space"
  assumes "b \<in> Basis"
  shows "Ppiece x v c b (ra_inc \<beta> b) = Qpiece x v c b \<beta>"
proof -
  have inc_b: "(ra_inc \<beta> b) b = Suc (\<beta> b)" by (simp add: ra_inc_def)
  have inc_d: "\<And>d. d \<noteq> b \<Longrightarrow> (ra_inc \<beta> b) d = \<beta> d" by (simp add: ra_inc_def)
  have prod_eq: "(\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ ((ra_inc \<beta> b) d))
                  = (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<beta> d))"
    by (rule prod.cong) (auto simp: inc_d)
  have mono: "(x \<bullet> b) ^ (\<beta> b) * (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<beta> d)) = ra_monomial x \<beta>"
    using ra_monomial_split[OF assms] by simp
  have "Ppiece x v c b (ra_inc \<beta> b)
        = (real (Suc (\<beta> b)) * (v \<bullet> b) * (x \<bullet> b) ^ (\<beta> b) *
             (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<beta> d))) *\<^sub>R c (ra_inc \<beta> b)"
    unfolding Ppiece_def by (simp add: inc_b prod_eq)
  also have "\<dots> = (real (Suc (\<beta> b)) * (v \<bullet> b)) *\<^sub>R
                    (((x \<bullet> b) ^ (\<beta> b) * (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<beta> d))) *\<^sub>R c (ra_inc \<beta> b))"
    by (simp add: mult.assoc)
  also have "\<dots> = (real (Suc (\<beta> b)) * (v \<bullet> b)) *\<^sub>R (ra_monomial x \<beta> *\<^sub>R c (ra_inc \<beta> b))"
    by (simp add: mono)
  finally show ?thesis by (simp add: Qpiece_def)
qed

text \<open>Off the support (@{term "\<alpha> b = 0"}) the LHS piece vanishes.\<close>

lemma Ppiece_zero_off_support:
  assumes "\<alpha> b = 0"
  shows "Ppiece x v c b \<alpha> = 0"
  by (simp add: Ppiece_def assms)


subsection \<open>Per-basis reindexing of has-sum\<close>

lemma has_sum_Ppiece_iff_Qpiece:
  fixes x v :: "'a::euclidean_space"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes b: "b \<in> Basis"
  shows "(Ppiece x v c b has_sum s) ra_idx \<longleftrightarrow> (Qpiece x v c b has_sum s) ra_idx"
proof -
  define A where "A = {\<alpha> \<in> ra_idx. 1 \<le> \<alpha> b}"
  have restrict: "(Ppiece x v c b has_sum s) ra_idx \<longleftrightarrow> (Ppiece x v c b has_sum s) A"
  proof (rule has_sum_cong_neutral)
    show "\<And>\<alpha>. \<alpha> \<in> ra_idx - A \<Longrightarrow> Ppiece x v c b \<alpha> = 0"
      by (auto simp: A_def intro!: Ppiece_zero_off_support)
  next
    show "\<And>\<alpha>. \<alpha> \<in> A - ra_idx \<Longrightarrow> Ppiece x v c b \<alpha> = 0" by (auto simp: A_def)
  next
    show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<inter> A \<Longrightarrow> Ppiece x v c b \<alpha> = Ppiece x v c b \<alpha>" by simp
  qed
  have reidx: "(Ppiece x v c b has_sum s) A \<longleftrightarrow> (Qpiece x v c b has_sum s) ra_idx"
  proof (rule has_sum_reindex_bij_witness[where i = "\<lambda>\<beta>. ra_inc \<beta> b" and j = "\<lambda>\<alpha>. ra_dec \<alpha> b"])
    fix \<alpha> assume "\<alpha> \<in> A"
    then have "1 \<le> \<alpha> b" by (simp add: A_def)
    thus "ra_inc (ra_dec \<alpha> b) b = \<alpha>" by (rule ra_inc_dec)
  next
    fix \<alpha> assume "\<alpha> \<in> A"
    then have "\<alpha> \<in> ra_idx" by (simp add: A_def)
    thus "ra_dec \<alpha> b \<in> ra_idx" by (rule ra_dec_in_idx)
  next
    fix \<beta> :: "'a \<Rightarrow> nat" assume "\<beta> \<in> ra_idx"
    show "ra_dec (ra_inc \<beta> b) b = \<beta>" by (rule ra_dec_inc)
  next
    fix \<beta> :: "'a \<Rightarrow> nat" assume "\<beta> \<in> ra_idx"
    then have "ra_inc \<beta> b \<in> ra_idx" using b by (rule ra_inc_in_idx)
    moreover have "1 \<le> (ra_inc \<beta> b) b" by (simp add: ra_inc_def)
    ultimately show "ra_inc \<beta> b \<in> A" by (simp add: A_def)
  next
    fix \<alpha> assume "\<alpha> \<in> A"
    then have a1: "1 \<le> \<alpha> b" by (simp add: A_def)
    have "Qpiece x v c b (ra_dec \<alpha> b) = Ppiece x v c b (ra_inc (ra_dec \<alpha> b) b)"
      by (rule Ppiece_inc_eq_Qpiece[OF b, symmetric])
    also have "\<dots> = Ppiece x v c b \<alpha>"
      using ra_inc_dec[where \<alpha> = \<alpha> and b = b, OF a1] by simp
    finally show "Qpiece x v c b (ra_dec \<alpha> b) = Ppiece x v c b \<alpha>" .
  next
    show "s = s" by simp
  qed
  show ?thesis using restrict reidx by blast
qed

lemma summable_Ppiece_iff_Qpiece:
  fixes x v :: "'a::euclidean_space"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes b: "b \<in> Basis"
  shows "Ppiece x v c b summable_on ra_idx \<longleftrightarrow> Qpiece x v c b summable_on ra_idx"
  unfolding summable_on_def using has_sum_Ppiece_iff_Qpiece[OF b] by blast

lemma infsum_Ppiece_eq_Qpiece:
  fixes x v :: "'a::euclidean_space"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes b: "b \<in> Basis"
  shows "infsum (Ppiece x v c b) ra_idx = infsum (Qpiece x v c b) ra_idx"
proof (cases "Ppiece x v c b summable_on ra_idx")
  case True
  then obtain s where s_Def: "(Ppiece x v c b has_sum s) ra_idx"
    by (auto simp: summable_on_def)
  then have "(Qpiece x v c b has_sum s) ra_idx"
    using has_sum_Ppiece_iff_Qpiece[OF b] by blast
  then show ?thesis using infsumI
    using s_Def by blast 
next
  case False
  then have "\<not> Qpiece x v c b summable_on ra_idx"
    using summable_Ppiece_iff_Qpiece[OF b] by blast
  with False show ?thesis by (simp add: infsum_not_exists)
qed


subsection \<open>Pushing @{const infsum} through a finite (basis) sum\<close>

lemma summable_on_finite_sum:
  fixes f :: "'i \<Rightarrow> 'j \<Rightarrow> 'b::{topological_comm_monoid_add}"
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> (f i) summable_on A"
  shows "(\<lambda>a. \<Sum>i\<in>I. f i a) summable_on A"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert x F)
  have fx: "(f x) summable_on A" using insert.prems by simp
  have fF: "\<And>i. i \<in> F \<Longrightarrow> (f i) summable_on A" using insert.prems by simp
  have "(\<lambda>a. f x a + (\<Sum>i\<in>F. f i a)) summable_on A"
    by (rule summable_on_add[OF fx insert.IH[OF fF]])
  thus ?case by (simp add: sum.insert[OF insert.hyps(1,2)])
qed

lemma infsum_finite_sum:
  fixes f :: "'i \<Rightarrow> 'j \<Rightarrow> 'b::banach"
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> (f i) summable_on A"
  shows "infsum (\<lambda>a. \<Sum>i\<in>I. f i a) A = (\<Sum>i\<in>I. infsum (f i) A)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert x F)
  have fx: "(f x) summable_on A" using insert.prems by simp
  have fF: "\<And>i. i \<in> F \<Longrightarrow> (f i) summable_on A" using insert.prems by simp
  have sumF: "(\<lambda>a. \<Sum>i\<in>F. f i a) summable_on A"
    by (rule summable_on_finite_sum[OF insert.hyps(1) fF])
  have IH: "infsum (\<lambda>a. \<Sum>i\<in>F. f i a) A = (\<Sum>i\<in>F. infsum (f i) A)"
    by (rule insert.IH[OF fF])
  have "infsum (\<lambda>a. \<Sum>i\<in>insert x F. f i a) A
        = infsum (\<lambda>a. f x a + (\<Sum>i\<in>F. f i a)) A"
    by (simp add: sum.insert[OF insert.hyps(1,2)])
  also have "\<dots> = infsum (f x) A + infsum (\<lambda>a. \<Sum>i\<in>F. f i a) A"
    by (rule infsum_add[OF fx sumF])
  also have "\<dots> = infsum (f x) A + (\<Sum>i\<in>F. infsum (f i) A)" by (simp add: IH)
  also have "\<dots> = (\<Sum>i\<in>insert x F. infsum (f i) A)"
    by (simp add: sum.insert[OF insert.hyps(1,2)])
  finally show ?case .
qed


subsection \<open>The corrected reindexing identity (lemma #6, strengthened hypothesis)\<close>

text \<open>The bare \<open>summable_on\<close> hypothesis on the differentiated family is too weak in an
  infinite-dimensional \<open>'b::banach\<close> (unordered convergence is strictly weaker than absolute,
  Dvoretzky--Rogers), so the reindex can fail.  The honest hypothesis, supplied by the consumer
  via the norm-summable majorant, is per-basis-direction summability of the once-differentiated
  coefficient series.\<close>

lemma ra_derivative_reindex:
  fixes x v :: "'a::euclidean_space"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes S: "\<And>b. b \<in> Basis \<Longrightarrow>
                (\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R (real (Suc (\<alpha> b)) *\<^sub>R c (ra_inc \<alpha> b)))
                  summable_on ra_idx"
  shows
    "infsum (\<lambda>\<alpha>. ra_Dmonomial x \<alpha> v *\<^sub>R c \<alpha>) ra_idx
       = infsum (\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>) ra_idx"
proof -
  have Qsum: "Qpiece x v c b summable_on ra_idx" if b: "b \<in> Basis" for b
  proof -
    have eq: "Qpiece x v c b
              = (\<lambda>\<alpha>. (v \<bullet> b) *\<^sub>R
                       (ra_monomial x \<alpha> *\<^sub>R (real (Suc (\<alpha> b)) *\<^sub>R c (ra_inc \<alpha> b))))"
      by (rule ext, simp add: Qpiece_def  ac_simps)
    have "(\<lambda>\<alpha>. (v \<bullet> b) *\<^sub>R
              (ra_monomial x \<alpha> *\<^sub>R (real (Suc (\<alpha> b)) *\<^sub>R c (ra_inc \<alpha> b))))
            summable_on ra_idx"
      using summable_on_bounded_linear[OF bounded_linear_scaleR_right[of "v \<bullet> b"], OF S[OF b]]
      by simp
    thus ?thesis by (simp only: eq)
  qed
  have Psum: "Ppiece x v c b summable_on ra_idx" if b: "b \<in> Basis" for b
    using Qsum[OF b] summable_Ppiece_iff_Qpiece[OF b] by blast
  have "infsum (\<lambda>\<alpha>. ra_Dmonomial x \<alpha> v *\<^sub>R c \<alpha>) ra_idx
        = infsum (\<lambda>\<alpha>. \<Sum>b\<in>Basis. Ppiece x v c b \<alpha>) ra_idx"
    by (simp add: Dmonomial_eq_sum_Ppiece)
  also have "\<dots> = (\<Sum>b\<in>Basis. infsum (Ppiece x v c b) ra_idx)"
    by (rule infsum_finite_sum[OF finite_Basis]) (rule Psum)
  also have "\<dots> = (\<Sum>b\<in>Basis. infsum (Qpiece x v c b) ra_idx)"
    by (rule sum.cong[OF refl]) (rule infsum_Ppiece_eq_Qpiece)
  also have "\<dots> = infsum (\<lambda>\<alpha>. \<Sum>b\<in>Basis. Qpiece x v c b \<alpha>) ra_idx"
    by (rule infsum_finite_sum[OF finite_Basis, symmetric]) (rule Qsum)
  also have "\<dots> = infsum (\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>) ra_idx"
    by (simp add: dcoeff_eq_sum_Qpiece)
  finally show ?thesis .
qed


(* ===================== Lemmas #8-#12 (from WF_V812_full) ===================== *)


lemma ra_power_series_differentiable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>)
          has_sum f y) ra_idx"
    and x: "dist x x0 < r"
  shows "f differentiable (at x)"
proof -
  have "(f has_derivative
       (\<lambda>v. infsum (\<lambda>\<alpha>. ra_Dmonomial (x - x0) \<alpha> v *\<^sub>R c \<alpha>) ra_idx))
      (at x)"
    by (rule ra_power_series_has_derivative[OF r series x])
  thus ?thesis
    unfolding differentiable_def by blast
qed


lemma ra_power_series_frechet_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>)
          has_sum f y) ra_idx"
    and x: "dist x x0 < r"
  shows
    "frechet_derivative f (at x) v =
       infsum
         (\<lambda>\<alpha>. ra_Dmonomial (x - x0) \<alpha> v *\<^sub>R c \<alpha>)
         ra_idx"
proof -
  have "(\<lambda>v. infsum (\<lambda>\<alpha>. ra_Dmonomial (x - x0) \<alpha> v *\<^sub>R c \<alpha>) ra_idx)
        = frechet_derivative f (at x)"
    by (rule frechet_derivative_at[OF ra_power_series_has_derivative[OF r series x]])
  thus ?thesis by (rule fun_cong[symmetric])
qed


lemma ra_power_series_continuous_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>)
          has_sum f y) ra_idx"
  shows "continuous_on (ball x0 r) f"
proof (rule continuous_at_imp_continuous_on, clarify)
  fix x assume "x \<in> ball x0 r"
  then have x: "dist x x0 < r" by (simp add: dist_commute)
  have "f differentiable (at x)"
    by (rule ra_power_series_differentiable[OF r series x])
  then have "continuous (at x within UNIV) f"
    by (rule differentiable_imp_continuous_within)
  then show "continuous (at x) f" by simp
qed

text \<open>Auxiliary: summability of the differentiated coefficient family near an interior point,
  for an arbitrary direction.\<close>

lemma ra_Dmono_summable_interior:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series: "\<And>z. dist z x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum F z) ra_idx"
    and y: "dist y x0 < r"
  shows "(\<lambda>\<alpha>. ra_Dmonomial (y - x0) \<alpha> w *\<^sub>R c \<alpha>) summable_on ra_idx"
proof -
  obtain \<delta>0 q K where \<delta>0: "0 < \<delta>0" and q0: "0 \<le> q" and q1: "q < 1" and Knn: "0 \<le> K"
    and majsumm: "(\<lambda>\<alpha>. K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>) summable_on ra_idx"
    and inball: "\<And>z. dist z y < \<delta>0 \<Longrightarrow> dist z x0 < r"
    and tbound: "\<And>z \<alpha> v. dist z y < \<delta>0 \<Longrightarrow> \<alpha> \<in> ra_idx \<Longrightarrow>
          norm (ra_Dmonomial (z - x0) \<alpha> v *\<^sub>R c \<alpha>)
            \<le> norm v * (K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)"
    using diff_majorant_interior[OF r series y] by blast
  \<comment> \<open>derive the scaled majorant summability from the type-annotated @{thm deg_pow_summable}
     (a polymorphic theorem, so its index type unifies freely with the goal's @{typ 'a}),
     avoiding the floating index type of the obtained @{term majsumm}\<close>
  have majw0: "(\<lambda>\<alpha>::'a\<Rightarrow>nat. (norm w * K) * (real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>))
                 summable_on ra_idx"
    by (rule summable_on_cmult_right[OF deg_pow_summable[OF q0 q1]])
  have majw: "(\<lambda>\<alpha>::'a\<Rightarrow>nat. norm w * (K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>))
                summable_on ra_idx"
    using majw0 by (simp add: mult.assoc)
  show ?thesis
  proof (rule abs_summable_summable,
         rule summable_on_comparison_test[OF majw])
    fix \<alpha> :: "'a \<Rightarrow> nat" assume a: "\<alpha> \<in> ra_idx"
    have dyy: "dist y y < \<delta>0" using \<delta>0 by simp
    show "norm (ra_Dmonomial (y - x0) \<alpha> w *\<^sub>R c \<alpha>)
            \<le> norm w * (K * real (ra_deg \<alpha> + 1) * q ^ ra_deg \<alpha>)"
      using tbound[OF dyy a] by simp
  next
    fix \<alpha> :: "'a \<Rightarrow> nat" assume a: "\<alpha> \<in> ra_idx"
    show "0 \<le> norm (ra_Dmonomial (y - x0) \<alpha> w *\<^sub>R c \<alpha>)" by simp
  qed
qed

text \<open>Auxiliary: the single @{const Ppiece} (direction the basis vector @{term b}) is exactly a
  directional derivative term, so it is summable.\<close>

lemma Ppiece_eq_Dmonomial_basis:
  fixes x :: "'a::euclidean_space"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes b: "b \<in> Basis"
  shows "Ppiece x b c b \<alpha> = ra_Dmonomial x \<alpha> b *\<^sub>R c \<alpha>"
proof -
  have "ra_Dmonomial x \<alpha> b
        = (\<Sum>b'\<in>Basis. real (\<alpha> b') * (b \<bullet> b') *
              (x \<bullet> b') ^ (\<alpha> b' - 1) * (\<Prod>d\<in>Basis - {b'}. (x \<bullet> d) ^ (\<alpha> d)))"
    by (simp add: ra_Dmonomial_def)
  also have "\<dots> = real (\<alpha> b) * (b \<bullet> b) *
              (x \<bullet> b) ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<alpha> d))"
  proof (rule sum.remove[OF finite_Basis b, THEN trans])
    have "(\<Sum>b'\<in>Basis - {b}. real (\<alpha> b') * (b \<bullet> b') *
              (x \<bullet> b') ^ (\<alpha> b' - 1) * (\<Prod>d\<in>Basis - {b'}. (x \<bullet> d) ^ (\<alpha> d))) = 0"
      by (rule sum.neutral) (auto simp: inner_Basis b)
    thus "real (\<alpha> b) * (b \<bullet> b) * (x \<bullet> b) ^ (\<alpha> b - 1) *
            (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<alpha> d)) +
          (\<Sum>b'\<in>Basis - {b}. real (\<alpha> b') * (b \<bullet> b') *
              (x \<bullet> b') ^ (\<alpha> b' - 1) * (\<Prod>d\<in>Basis - {b'}. (x \<bullet> d) ^ (\<alpha> d)))
          = real (\<alpha> b) * (b \<bullet> b) *
              (x \<bullet> b) ^ (\<alpha> b - 1) * (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<alpha> d))"
      by simp
  qed
  finally have eqD: "ra_Dmonomial x \<alpha> b
        = real (\<alpha> b) * (b \<bullet> b) * (x \<bullet> b) ^ (\<alpha> b - 1) *
              (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<alpha> d))" .
  have "Ppiece x b c b \<alpha>
        = (real (\<alpha> b) * (b \<bullet> b) * (x \<bullet> b) ^ (\<alpha> b - 1) *
              (\<Prod>d\<in>Basis - {b}. (x \<bullet> d) ^ (\<alpha> d))) *\<^sub>R c \<alpha>"
    by (simp add: Ppiece_def)
  also have "\<dots> = ra_Dmonomial x \<alpha> b *\<^sub>R c \<alpha>" by (simp only: eqD)
  finally show ?thesis .
qed


lemma ra_directional_derivative_series:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>)
          has_sum f y) ra_idx"
    and y: "dist y x0 < r"
  shows
    "((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R
          ra_dcoeff c v \<alpha>)
       has_sum frechet_derivative f (at y) v)
      ra_idx"
proof -
  \<comment> \<open>(i) the Frechet derivative is the differentiated infsum (lemma #9 at @{term y})\<close>
  have fd: "frechet_derivative f (at y) v
            = infsum (\<lambda>\<alpha>. ra_Dmonomial (y - x0) \<alpha> v *\<^sub>R c \<alpha>) ra_idx"
    by (rule ra_power_series_frechet_derivative[OF r series y])
  \<comment> \<open>(iii) the per-basis-direction summability hypothesis for the reindex lemma #6\<close>
  have S6: "(\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R
               (real (Suc (\<alpha> b)) *\<^sub>R c (ra_inc \<alpha> b))) summable_on ra_idx"
    if b: "b \<in> Basis" for b
  proof -
    \<comment> \<open>the differentiated family in direction @{term b} is summable\<close>
    have Dsum: "(\<lambda>\<alpha>. ra_Dmonomial (y - x0) \<alpha> b *\<^sub>R c \<alpha>) summable_on ra_idx"
      by (rule ra_Dmono_summable_interior[OF r series y])
    \<comment> \<open>that family equals @{term \<open>Ppiece (y - x0) b c b\<close>}\<close>
    have Pid: "Ppiece (y - x0) b c b = (\<lambda>\<alpha>. ra_Dmonomial (y - x0) \<alpha> b *\<^sub>R c \<alpha>)"
      by (rule ext) (rule Ppiece_eq_Dmonomial_basis[OF b])
    have Psum: "Ppiece (y - x0) b c b summable_on ra_idx"
      by (simp only: Pid Dsum)
    \<comment> \<open>hence @{term \<open>Qpiece (y - x0) b c b\<close>} is summable\<close>
    have Qsum: "Qpiece (y - x0) b c b summable_on ra_idx"
      using Psum summable_Ppiece_iff_Qpiece[OF b] by blast
    \<comment> \<open>and @{term \<open>Qpiece (y - x0) b c b\<close>} is the desired family (since @{term \<open>b \<bullet> b = 1\<close>})\<close>
    have Qeq: "Qpiece (y - x0) b c b
               = (\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R
                       (real (Suc (\<alpha> b)) *\<^sub>R c (ra_inc \<alpha> b)))"
      by (rule ext) (simp add: Qpiece_def inner_Basis b)
    show ?thesis using Qsum by (simp only: Qeq)
  qed
  \<comment> \<open>(iv) rewrite the infsum via lemma #6\<close>
  have reindex: "infsum (\<lambda>\<alpha>. ra_Dmonomial (y - x0) \<alpha> v *\<^sub>R c \<alpha>) ra_idx
                 = infsum (\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>) ra_idx"
    by (rule ra_derivative_reindex[OF S6])
  \<comment> \<open>(v) the regrouped (Qpiece) family is summable\<close>
  have Qfsum: "Qpiece (y - x0) v c b summable_on ra_idx" if b: "b \<in> Basis" for b
  proof -
    have Pid: "Ppiece (y - x0) v c b summable_on ra_idx \<Longrightarrow> ?thesis"
      using summable_Ppiece_iff_Qpiece[OF b] by blast
    \<comment> \<open>@{term \<open>Ppiece (y - x0) v c b\<close>} is summable: it is dominated by the same majorant.
       We obtain it from the summability of the directional family in direction @{term b}.\<close>
    have Dsum: "(\<lambda>\<alpha>. ra_Dmonomial (y - x0) \<alpha> b *\<^sub>R c \<alpha>) summable_on ra_idx"
      by (rule ra_Dmono_summable_interior[OF r series y])
    have Pbid: "Ppiece (y - x0) b c b = (\<lambda>\<alpha>. ra_Dmonomial (y - x0) \<alpha> b *\<^sub>R c \<alpha>)"
      by (rule ext) (rule Ppiece_eq_Dmonomial_basis[OF b])
    have Pbsum: "Ppiece (y - x0) b c b summable_on ra_idx"
      by (simp only: Pbid Dsum)
    \<comment> \<open>relate @{term \<open>Ppiece (y - x0) v c b\<close>} to @{term \<open>Ppiece (y - x0) b c b\<close>} by the scalar
       @{term \<open>v \<bullet> b\<close>}\<close>
    have scal: "Ppiece (y - x0) v c b = (\<lambda>\<alpha>. (v \<bullet> b) *\<^sub>R Ppiece (y - x0) b c b \<alpha>)"
      by (rule ext) (simp add: Ppiece_def inner_Basis b algebra_simps)
    have "(\<lambda>\<alpha>. (v \<bullet> b) *\<^sub>R Ppiece (y - x0) b c b \<alpha>) summable_on ra_idx"
      by (rule summable_on_bounded_linear[OF bounded_linear_scaleR_right Pbsum])
    then have "Ppiece (y - x0) v c b summable_on ra_idx" by (simp only: scal)
    thus ?thesis using Pid by blast
  qed
  have Qreg: "(\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>)
                = (\<lambda>\<alpha>. \<Sum>b\<in>Basis. Qpiece (y - x0) v c b \<alpha>)"
    by (rule ext) (rule dcoeff_eq_sum_Qpiece)
  have Qsumm: "(\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>) summable_on ra_idx"
    by (simp only: Qreg) (rule summable_on_finite_sum[OF finite_Basis Qfsum])
  \<comment> \<open>assemble: the family has_sum its own infsum, which equals the Frechet derivative\<close>
  have "((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>)
          has_sum infsum (\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>) ra_idx) ra_idx"
    by (rule has_sum_infsum[OF Qsumm])
  also have "infsum (\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>) ra_idx
             = infsum (\<lambda>\<alpha>. ra_Dmonomial (y - x0) \<alpha> v *\<^sub>R c \<alpha>) ra_idx"
    by (rule reindex[symmetric])
  also have "\<dots> = frechet_derivative f (at y) v" by (rule fd[symmetric])
  finally show ?thesis .
qed


text \<open>The pointwise @{const Ck_at} property, by induction on @{term k}, generalised over both the
  function @{term g} and the coefficient family @{term cc} (the derivative field is again a power
  series, with coefficient family @{term \<open>ra_dcoeff cc v\<close>}).\<close>

lemma ra_power_series_Ck_at_aux:
  fixes x0 :: "'a::euclidean_space"
  assumes r: "0 < r"
  shows "\<And>(g::'a \<Rightarrow> 'b::banach) cc x.
           (\<And>z. dist z x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R cc \<alpha>) has_sum g z) ra_idx)
           \<Longrightarrow> x \<in> ball x0 r \<Longrightarrow> Ck_at k g x"
proof (induct k)
  case (0 g cc x)
  then have x: "dist x x0 < r" by (simp add: dist_commute)
  have "g differentiable (at x)"
    by (rule ra_power_series_differentiable[OF r 0(1) x])
  then have "continuous (at x within UNIV) g"
    by (rule differentiable_imp_continuous_within)
  then have "continuous (at x) g" by simp
  thus ?case by simp
next
  case (Suc k g cc x)
  have series: "\<And>z. dist z x0 < r \<Longrightarrow>
                  ((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R cc \<alpha>) has_sum g z) ra_idx"
    by (rule Suc.prems(1))
  have xball: "x \<in> ball x0 r" by (rule Suc.prems(2))
  then have x: "dist x x0 < r" by (simp add: dist_commute)
  \<comment> \<open>(i) a neighbourhood (the ball) on which @{term \<open>Ck_at k g\<close>} holds\<close>
  have nbhd: "open (ball x0 r) \<and> x \<in> ball x0 r \<and> (\<forall>y\<in>ball x0 r. Ck_at k g y)"
  proof (intro conjI ballI)
    show "open (ball x0 r)" by simp
    show "x \<in> ball x0 r" by (rule xball)
    fix y assume yb: "y \<in> ball x0 r"
    show "Ck_at k g y" by (rule Suc.hyps[OF series yb])
  qed
  \<comment> \<open>(ii) @{term g} is differentiable at @{term x}\<close>
  have diff: "g differentiable (at x)"
    by (rule ra_power_series_differentiable[OF r series x])
  \<comment> \<open>(iii) each directional-derivative field is again a @{term \<open>Ck_at k\<close>} power series\<close>
  have dirCk: "Ck_at k (\<lambda>y. frechet_derivative g (at y) v) x" for v
  proof -
    have dseries: "\<And>z. dist z x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (z - x0) \<alpha> *\<^sub>R ra_dcoeff cc v \<alpha>)
                 has_sum frechet_derivative g (at z) v) ra_idx"
      by (rule ra_directional_derivative_series[OF r series])
    show "Ck_at k (\<lambda>y. frechet_derivative g (at y) v) x"
      by (rule Suc.hyps[OF dseries xball])
  qed
  show ?case
    by (simp only: Ck_at.simps(2)) (intro conjI exI[where x = "ball x0 r"] nbhd diff allI dirCk)
qed


lemma ra_power_series_higher_differentiable_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>)
          has_sum f y) ra_idx"
  shows "higher_differentiable_on (ball x0 r) f k"
proof -
  have "Ck_on k f (ball x0 r)"
    unfolding Ck_on_def
  proof (intro conjI ballI)
    show "open (ball x0 r)" by simp
    fix x assume xb: "x \<in> ball x0 r"
    show "Ck_at k f x"
      by (rule ra_power_series_Ck_at_aux[OF r series xb])
  qed
  thus ?thesis
    by (simp add: Ck_on_iff_higher_differentiable_on[OF open_ball])
qed




lemma ra_power_series_Ck_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>)
          has_sum f y) ra_idx"
  shows "Ck_on k f (ball x0 r)"
proof -
  have H:
    "higher_differentiable_on (ball x0 r) f k"
    by (rule ra_power_series_higher_differentiable_on[OF r series])
  show ?thesis
    using H
    by (simp add: Ck_on_iff_higher_differentiable_on)
qed


lemma ra_power_series_Ck_at:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>)
          has_sum f y) ra_idx"
  shows "Ck_at k f x0"
proof -
  have C: "Ck_on k f (ball x0 r)"
    by (rule ra_power_series_Ck_on[OF r series])
  show ?thesis
    using C r
    by (simp add: Ck_on_def)
qed

subsection \<open>(1b) Analytic implies infinitely differentiable\<close>

theorem real_analytic_imp_Cinfinity:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes A: "real_analytic_on f U"
  shows "Cinfinity_on f U"
proof -
  have openU: "open U"
    using A unfolding real_analytic_on_def by blast
  show ?thesis
    unfolding Cinfinity_on_def Cinfinity_at_def
  proof (intro conjI ballI allI)
    show "open U" by (rule openU)
  next
    fix x k
    assume xU: "x \<in> U"
    from A xU obtain r c where
      r: "0 < r"
      and series:
        "\<And>y. dist y x < r \<Longrightarrow>
          ((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>)
            has_sum f y) ra_idx"
      unfolding real_analytic_on_def by blast
    show "Ck_at k f x"
      by (rule ra_power_series_Ck_at[OF r series])
  qed
qed

text \<open>(1c) The $C^\infty$-but-not-analytic witness \<open>exp_bump\<close> lives in the companion theory
  \<open>Real_Analytic_Bump\<close>: it reuses the AFP \<open>Smooth_Manifolds.Bump_Function\<close>, whose heavy
  import must not perturb the core definitions above.  See there for \<open>exp_bump_Cinfinity\<close>
  and \<open>exp_bump_not_real_analytic\<close>.\<close>


lemma real_analytic_on_open_subset:
  assumes F: "real_analytic_on f U"
    and V: "open V"
    and sub: "V \<subseteq> U"
  shows "real_analytic_on f V"
  unfolding real_analytic_on_def
proof (intro conjI ballI)
  show "open V" by (rule V)
next
  fix x assume xV: "x \<in> V"
  hence xU: "x \<in> U"
    using sub by blast
  from F xU show "\<exists>r>0. \<exists>c. \<forall>y. dist y x < r \<longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum f y) ra_idx"
    unfolding real_analytic_on_def by blast
qed


subsection \<open>(1.5) Closure properties\<close>

lemma real_analytic_on_const:
  fixes k :: "'b::real_normed_vector"
  shows "open U \<Longrightarrow> real_analytic_on ((\<lambda>_. k) :: 'a::euclidean_space \<Rightarrow> 'b) U"
proof -
  assume U: "open U"
  define a0 :: "'a \<Rightarrow> nat" where "a0 = (\<lambda>_. 0)"
  have a0_idx: "a0 \<in> ra_idx" by (simp add: ra_idx_def a0_def)
  define c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b" where "c = (\<lambda>\<alpha>. if \<alpha> = a0 then k else 0)"
  have hs: "((\<lambda>\<alpha>. ra_monomial h \<alpha> *\<^sub>R c \<alpha>) has_sum k) ra_idx" for h :: 'a
  proof -
    have sing: "((\<lambda>\<alpha>. ra_monomial h \<alpha> *\<^sub>R c \<alpha>) has_sum
                   (\<Sum>\<alpha>\<in>{a0}. ra_monomial h \<alpha> *\<^sub>R c \<alpha>)) {a0}"
      by (rule has_sum_finite) auto
    have val: "(\<Sum>\<alpha>\<in>{a0}. ra_monomial h \<alpha> *\<^sub>R c \<alpha>) = k"
      by (simp add: c_def ra_monomial_def a0_def)
    have "((\<lambda>\<alpha>. ra_monomial h \<alpha> *\<^sub>R c \<alpha>) has_sum k) ra_idx
            = ((\<lambda>\<alpha>. ra_monomial h \<alpha> *\<^sub>R c \<alpha>) has_sum k) {a0}"
      by (rule has_sum_cong_neutral) (auto simp: c_def a0_idx)
    thus ?thesis using sing val by simp
  qed
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open U" by (rule U)
  next
    fix x0 :: 'a assume "x0 \<in> U"
    show "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
            ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum (\<lambda>_. k) x) ra_idx"
      by (intro exI[where x=1] conjI exI[where x=c] allI impI; simp only: hs)
  qed
qed

lemma real_analytic_on_add:
  assumes F: "real_analytic_on f U" and G: "real_analytic_on g U"
  shows "real_analytic_on (\<lambda>x. f x + g x) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open U" by (rule U)
  next
    fix x0 assume x0: "x0 \<in> U"
    from F x0 have "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x) ra_idx"
      by (simp only: real_analytic_on_def)
    then obtain r1 c1 where r1: "0 < r1"
      and F1: "\<And>x. dist x x0 < r1 \<Longrightarrow>
                ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>) has_sum f x) ra_idx"
      by blast
    from G x0 have "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum g x) ra_idx"
      by (simp only: real_analytic_on_def)
    then obtain r2 c2 where r2: "0 < r2"
      and G1: "\<And>x. dist x x0 < r2 \<Longrightarrow>
                ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>) has_sum g x) ra_idx"
      by blast
    show "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
            ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum (f x + g x)) ra_idx"
    proof (intro exI[where x="min r1 r2"] conjI exI[where x="\<lambda>\<alpha>. c1 \<alpha> + c2 \<alpha>"] allI impI)
      show "0 < min r1 r2" using r1 r2 by simp
    next
      fix x assume d: "dist x x0 < min r1 r2"
      have "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>
                  + ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>) has_sum (f x + g x)) ra_idx"
        by (rule has_sum_add) (use d F1 G1 in auto)
      thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (c1 \<alpha> + c2 \<alpha>)) has_sum (f x + g x)) ra_idx"
        by (simp only: scaleR_add_right)
    qed
  qed
qed

lemma real_analytic_on_scaleR:
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. a *\<^sub>R f x) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open U" by (rule U)
  next
    fix x0 assume x0: "x0 \<in> U"
    from F x0 have "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x) ra_idx"
      by (simp only: real_analytic_on_def)
    then obtain r c where r: "0 < r"
      and F1: "\<And>x. dist x x0 < r \<Longrightarrow>
                ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x) ra_idx"
      by blast
    show "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
            ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum (a *\<^sub>R f x)) ra_idx"
    proof (intro exI[where x=r] conjI exI[where x="\<lambda>\<alpha>. a *\<^sub>R c \<alpha>"] allI impI)
      show "0 < r" by (rule r)
    next
      fix x assume d: "dist x x0 < r"
      have "((\<lambda>\<alpha>. a *\<^sub>R (ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>)) has_sum (a *\<^sub>R f x)) ra_idx"
        by (rule has_sum_scaleR) (rule F1[OF d])
      thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (a *\<^sub>R c \<alpha>)) has_sum (a *\<^sub>R f x)) ra_idx"
        by (simp only: scaleR_left_commute mult.commute)
    qed
  qed
qed

lemma real_analytic_on_mult:
  fixes f g :: "'a::euclidean_space \<Rightarrow> real"
  shows "real_analytic_on f U \<Longrightarrow> real_analytic_on g U \<Longrightarrow> real_analytic_on (\<lambda>x. f x * g x) U"
proof -
  assume F: "real_analytic_on f U" and G: "real_analytic_on g U"
  from F have U: "open U" by (simp only: real_analytic_on_def)

  \<comment> \<open>Explicit (import-free) pointwise sum/difference of multi-indices and the order
     (avoids needing HOL.Library.Function_Algebras, which is NOT imported).\<close>
  define addI :: "('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat)" where
    "addI = (\<lambda>\<alpha> \<beta> b. \<alpha> b + \<beta> b)"
  define subI :: "('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat)" where
    "subI = (\<lambda>\<gamma> \<alpha> b. \<gamma> b - \<alpha> b)"
  define leI :: "('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat) \<Rightarrow> bool" where
    "leI = (\<lambda>\<alpha> \<gamma>. \<forall>b. \<alpha> b \<le> \<gamma> b)"

  \<comment> \<open>(A) ra_idx closed under addI and subI.\<close>
  have idx_add: "addI \<alpha> \<beta> \<in> ra_idx" if "\<alpha> \<in> ra_idx" "\<beta> \<in> ra_idx" for \<alpha> \<beta>
  proof -
    have "{b. addI \<alpha> \<beta> b \<noteq> 0} \<subseteq> {b. \<alpha> b \<noteq> 0} \<union> {b. \<beta> b \<noteq> 0}"
      by (auto simp: addI_def)
    also have "\<dots> \<subseteq> Basis" using that by (auto simp: ra_idx_def)
    finally show ?thesis by (simp add: ra_idx_def)
  qed
  have idx_sub: "subI \<gamma> \<alpha> \<in> ra_idx" if "\<gamma> \<in> ra_idx" for \<gamma> \<alpha>
  proof -
    have "{b. subI \<gamma> \<alpha> b \<noteq> 0} \<subseteq> {b. \<gamma> b \<noteq> 0}" by (auto simp: subI_def)
    also have "\<dots> \<subseteq> Basis" using that by (auto simp: ra_idx_def)
    finally show ?thesis by (simp add: ra_idx_def)
  qed

  \<comment> \<open>(B) the basis monomial is multiplicative in addI.\<close>
  have mono_add: "ra_monomial h (addI \<alpha> \<beta>) = ra_monomial h \<alpha> * ra_monomial h \<beta>"
    for h :: 'a and \<alpha> \<beta>
    by (simp only: ra_monomial_def addI_def power_add prod.distrib)

  \<comment> \<open>(C) finiteness of the lower set inside ra_idx.\<close>
  have idx_lower_fin: "finite {\<alpha>. \<alpha> \<in> ra_idx \<and> leI \<alpha> \<gamma>}" for \<gamma> :: "'a \<Rightarrow> nat"
  proof -
    define N where "N = Max (insert 0 (\<gamma> ` (Basis :: 'a set)))"
    have "{\<alpha>. \<alpha> \<in> ra_idx \<and> leI \<alpha> \<gamma>}
            \<subseteq> {hh. \<forall>x::'a. (x \<in> Basis \<longrightarrow> hh x \<in> {0..N}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
    proof (rule subsetI)
      fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> {\<alpha>. \<alpha> \<in> ra_idx \<and> leI \<alpha> \<gamma>}"
      then have a1: "\<alpha> \<in> ra_idx" and a2: "leI \<alpha> \<gamma>" by auto
      have "\<forall>x::'a. (x \<in> Basis \<longrightarrow> \<alpha> x \<in> {0..N}) \<and> (x \<notin> Basis \<longrightarrow> \<alpha> x = 0)"
      proof (intro allI conjI impI)
        fix x :: 'a assume "x \<in> Basis"
        have "\<alpha> x \<le> \<gamma> x" using a2 by (simp only: leI_def)
        also have "\<gamma> x \<le> N" unfolding N_def using \<open>x \<in> Basis\<close> by (intro Max_ge) auto
        finally show "\<alpha> x \<in> {0..N}" by simp
      next
        fix x :: 'a assume "x \<notin> Basis"
        with a1 show "\<alpha> x = 0" by (auto simp: ra_idx_def)
      qed
      thus "\<alpha> \<in> {hh. \<forall>x::'a. (x \<in> Basis \<longrightarrow> hh x \<in> {0..N}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
        by simp
    qed
    moreover have "finite {hh::'a\<Rightarrow>nat. \<forall>x. (x \<in> Basis \<longrightarrow> hh x \<in> {0..N}) \<and> (x \<notin> Basis \<longrightarrow> hh x = (0::nat))}"
      by (rule finite_set_of_finite_funs) auto
    ultimately show ?thesis by (rule finite_subset)
  qed

  \<comment> \<open>(D) product of two real unordered sums over a common index set (the core
     Fubini/Cauchy step; built from abs_summable_on_Sigma_iff + has_sum_SigmaI).
     We avoid the ambiguous \<open>abs_summable_on\<close> infix in statements by writing
     \<open>(\<lambda>z. norm (...)) summable_on _\<close> directly (which is exactly the abbreviation it
     stands for, so the named lemma rewrites still apply).\<close>
  have prod_has_sum:
    "((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) has_sum (Uv * Vv)) (I \<times> I)"
    if uHS: "(u has_sum Uv) I" and vHS: "(v has_sum Vv) I"
    for u v :: "('a \<Rightarrow> nat) \<Rightarrow> real" and Uv Vv I
  proof -
    have u_abs: "(\<lambda>z. norm (u z)) summable_on I"
      using uHS has_sum_imp_summable summable_on_iff_abs_summable_on_real by blast
    have v_abs: "(\<lambda>z. norm (v z)) summable_on I"
      using vHS has_sum_imp_summable summable_on_iff_abs_summable_on_real by blast
    have inner: "((\<lambda>\<beta>. u \<alpha> * v \<beta>) has_sum (u \<alpha> * Vv)) I" for \<alpha>
      by (rule has_sum_cmult_right[OF vHS])
    have outer: "((\<lambda>\<alpha>. u \<alpha> * Vv) has_sum (Uv * Vv)) I"
      by (rule has_sum_cmult_left[OF uHS])
    have inner_abs: "(\<lambda>\<beta>. norm (u \<alpha> * v \<beta>)) summable_on I" for \<alpha>
    proof -
      have "(\<lambda>\<beta>. norm (u \<alpha>) * norm (v \<beta>)) summable_on I"
        using v_abs by (rule summable_on_cmult_right)
      thus ?thesis by (simp only: norm_mult flip: abs_mult)
    qed
    have tail_abs: "(\<lambda>\<alpha>. norm (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>))) summable_on I"
    proof -
      have eq: "norm (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>)) = norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))" for \<alpha>
      proof -
        have nn: "(\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>)) = norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))"
        proof -
          have "(\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>)) = (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha>) * norm (v \<beta>))"
            by (simp add: abs_mult)
          also have "\<dots> = norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))"
            by (rule infsum_cmult_right) (rule v_abs)
          finally show ?thesis .
        qed
        have ge: "(0::real) \<le> norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))"
          by (intro mult_nonneg_nonneg) (auto intro: infsum_nonneg)
        from nn ge show ?thesis by simp
      qed
      have "(\<lambda>\<alpha>. norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))) summable_on I"
        using u_abs by (rule summable_on_cmult_left)
      thus ?thesis unfolding eq .
    qed
    \<comment> \<open>the two conjuncts of @{thm abs_summable_on_Sigma_iff}, stated in the
       unfolded \<open>(\<lambda>z. norm (...)) summable_on _\<close> form to avoid the ambiguous infix.\<close>
    have conj1: "\<forall>\<alpha>\<in>I. (\<lambda>\<beta>. norm ((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) (\<alpha>, \<beta>))) summable_on I"
    proof
      fix \<alpha> assume "\<alpha> \<in> I"
      have "(\<lambda>\<beta>. norm (u \<alpha> * v \<beta>)) summable_on I" by (rule inner_abs)
      thus "(\<lambda>\<beta>. norm ((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) (\<alpha>, \<beta>))) summable_on I" by simp
    qed
    have conj2: "(\<lambda>\<alpha>. norm (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm ((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) (\<alpha>, \<beta>)))) summable_on I"
    proof -
      have "(\<lambda>\<alpha>. norm (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>))) summable_on I" by (rule tail_abs)
      thus ?thesis by simp
    qed
    \<comment> \<open>fully instantiate @{thm abs_summable_on_Sigma_iff} (avoids the costly higher-order
       match that \<open>subst\<close> would attempt, and keeps the infix off our own statements).\<close>
    have absS: "(\<lambda>z. norm ((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) z)) summable_on (Sigma I (\<lambda>_. I))"
      by (rule Infinite_Sum.abs_summable_on_Sigma_iff
            [where f = "\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>" and A = I and B = "\<lambda>_. I", THEN iffD2,
             OF conjI[OF conj1 conj2]])
    have summ: "(\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) summable_on Sigma I (\<lambda>_. I)"
      by (rule abs_summable_summable[OF absS])
    have "((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) has_sum (Uv * Vv)) (Sigma I (\<lambda>_. I))"
    proof (rule has_sum_SigmaI[where g = "\<lambda>\<alpha>. u \<alpha> * Vv"])
      fix \<alpha> assume "\<alpha> \<in> I"
      have "((\<lambda>\<beta>. u \<alpha> * v \<beta>) has_sum (u \<alpha> * Vv)) I" by (rule inner)
      thus "((\<lambda>\<beta>. (\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) (\<alpha>, \<beta>)) has_sum (u \<alpha> * Vv)) I" by simp
    next
      show "((\<lambda>\<alpha>. u \<alpha> * Vv) has_sum (Uv * Vv)) I" by (rule outer)
    next
      show "(\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) summable_on Sigma I (\<lambda>_. I)" by (rule summ)
    qed
    thus ?thesis by (simp only: Sigma_def)
  qed

  show "real_analytic_on (\<lambda>x. f x * g x) U"
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open U" by (rule U)
  next
    fix x0 assume x0: "x0 \<in> U"
    from F x0 obtain r1 c1 where r1: "0 < r1"
      and F1: "\<And>x. dist x x0 < r1 \<Longrightarrow>
                ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>) has_sum f x) ra_idx"
      unfolding real_analytic_on_def by blast
    from G x0 obtain r2 c2 where r2: "0 < r2"
      and G1: "\<And>x. dist x x0 < r2 \<Longrightarrow>
                ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>) has_sum g x) ra_idx"
      unfolding real_analytic_on_def by blast
    define low where "low = (\<lambda>\<gamma>::'a\<Rightarrow>nat. {\<alpha>. \<alpha> \<in> ra_idx \<and> leI \<alpha> \<gamma>})"
    define cprod :: "('a \<Rightarrow> nat) \<Rightarrow> real" where
      "cprod = (\<lambda>\<gamma>. \<Sum>\<alpha>\<in>low \<gamma>. c1 \<alpha> * c2 (subI \<gamma> \<alpha>))"
    show "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
            ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum (f x * g x)) ra_idx"
    proof (intro exI[where x="min r1 r2"] conjI exI[where x=cprod] allI impI)
      show "0 < min r1 r2" using r1 r2 by simp
    next
      fix x assume dx: "dist x x0 < min r1 r2"
      have dx1: "dist x x0 < r1" using dx min.cobounded1 by (rule order_less_le_trans)
      have dx2: "dist x x0 < r2" using dx min.cobounded2 by (rule order_less_le_trans)
      define h where "h = x - x0"
      have F1': "((\<lambda>\<alpha>. ra_monomial h \<alpha> * c1 \<alpha>) has_sum f x) ra_idx"
        using F1[OF dx1] by (simp add: h_def)
      have G1': "((\<lambda>\<beta>. ra_monomial h \<beta> * c2 \<beta>) has_sum g x) ra_idx"
        using G1[OF dx2] by (simp add: h_def)
      \<comment> \<open>(1) product over ra_idx \<times> ra_idx.\<close>
      have step1:
        "((\<lambda>(\<alpha>,\<beta>). (ra_monomial h \<alpha> * c1 \<alpha>) * (ra_monomial h \<beta> * c2 \<beta>))
             has_sum (f x * g x)) (ra_idx \<times> ra_idx)"
        using prod_has_sum[OF F1' G1'] .
      \<comment> \<open>(2) reindex to the Sigma-convolution via (\<alpha>,\<beta>) \<mapsto> (addI \<alpha> \<beta>, \<alpha>).\<close>
      have step2:
        "((\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum (f x * g x))
            (Sigma ra_idx low)"
      proof -
        have "((\<lambda>(\<alpha>,\<beta>). (ra_monomial h \<alpha> * c1 \<alpha>) * (ra_monomial h \<beta> * c2 \<beta>))
                 has_sum (f x * g x)) (ra_idx \<times> ra_idx)
              = ((\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum (f x * g x))
                 (Sigma ra_idx low)"
        proof (rule has_sum_reindex_bij_witness
                 [where j = "\<lambda>(\<alpha>,\<beta>). (addI \<alpha> \<beta>, \<alpha>)" and i = "\<lambda>(\<gamma>,\<alpha>). (\<alpha>, subI \<gamma> \<alpha>)"])
          fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
          assume "p \<in> ra_idx \<times> ra_idx"
          obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
          show "(case (case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) = p"
            by (simp add: p subI_def addI_def)
        next
          fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
          assume P: "p \<in> ra_idx \<times> ra_idx"
          obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
          have a\<alpha>: "\<alpha> \<in> ra_idx" and a\<beta>: "\<beta> \<in> ra_idx" using P p by auto
          have m1: "addI \<alpha> \<beta> \<in> ra_idx" by (rule idx_add[OF a\<alpha> a\<beta>])
          have m2: "\<alpha> \<in> low (addI \<alpha> \<beta>)"
            using a\<alpha> by (simp add: low_def leI_def addI_def)
          show "(case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) \<in> Sigma ra_idx low"
            using m1 m2 by (simp add: p)
        next
          fix q :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
          assume Q: "q \<in> Sigma ra_idx low"
          obtain \<gamma> \<alpha> where q: "q = (\<gamma>,\<alpha>)" by (cases q)
          have g\<gamma>: "\<gamma> \<in> ra_idx" and l: "leI \<alpha> \<gamma>" using Q q by (auto simp: low_def)
          have "addI \<alpha> (subI \<gamma> \<alpha>) = \<gamma>"
          proof (rule ext)
            fix b have "\<alpha> b \<le> \<gamma> b" using l by (simp only: leI_def)
            thus "addI \<alpha> (subI \<gamma> \<alpha>) b = \<gamma> b" by (simp only: addI_def subI_def)
          qed
          then show "(case (case q of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) = q"
            by (simp add: q)
        next
          fix q :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
          assume Q: "q \<in> Sigma ra_idx low"
          obtain \<gamma> \<alpha> where q: "q = (\<gamma>,\<alpha>)" by (cases q)
          have g\<gamma>: "\<gamma> \<in> ra_idx" and a\<alpha>: "\<alpha> \<in> ra_idx" using Q q by (auto simp: low_def)
          show "(case q of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) \<in> ra_idx \<times> ra_idx"
            by (simp add: q a\<alpha> idx_sub[OF g\<gamma>])
        next
          fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
          assume P: "p \<in> ra_idx \<times> ra_idx"
          obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
          have sub_eq: "subI (addI \<alpha> \<beta>) \<alpha> = \<beta>" by (simp add: addI_def subI_def)
          have mm: "ra_monomial h \<alpha> * ra_monomial h \<beta> = ra_monomial h (addI \<alpha> \<beta>)"
            by (simp only: mono_add)
          have "ra_monomial h (addI \<alpha> \<beta>) * (c1 \<alpha> * c2 (subI (addI \<alpha> \<beta>) \<alpha>))
                  = ra_monomial h (addI \<alpha> \<beta>) * (c1 \<alpha> * c2 \<beta>)" by (simp only: sub_eq)
          also have "\<dots> = (ra_monomial h \<alpha> * ra_monomial h \<beta>) * (c1 \<alpha> * c2 \<beta>)"
            by (simp only: mm)
          also have "\<dots> = (ra_monomial h \<alpha> * c1 \<alpha>) * (ra_monomial h \<beta> * c2 \<beta>)"
            by (simp only: mult.assoc mult.left_commute)
          finally show "(case (case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) of (\<gamma>,\<alpha>) \<Rightarrow>
                            ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>)))
                       = (case p of (\<alpha>,\<beta>) \<Rightarrow> (ra_monomial h \<alpha> * c1 \<alpha>) * (ra_monomial h \<beta> * c2 \<beta>))"
            by (simp add: p)
        qed simp
        with step1 show ?thesis by simp
      qed
      \<comment> \<open>(3) collapse the finite inner sum.\<close>
      have inner_fin:
        "((\<lambda>\<alpha>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum
            (ra_monomial h \<gamma> *\<^sub>R cprod \<gamma>)) (low \<gamma>)" if "\<gamma> \<in> ra_idx" for \<gamma>
      proof -
        have fin: "finite (low \<gamma>)" using idx_lower_fin[of \<gamma>] by (simp only: low_def)
        have "((\<lambda>\<alpha>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum
                 (\<Sum>\<alpha>\<in>low \<gamma>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>)))) (low \<gamma>)"
          by (rule has_sum_finite[OF fin])
        also have "(\<Sum>\<alpha>\<in>low \<gamma>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>)))
                     = ra_monomial h \<gamma> * (\<Sum>\<alpha>\<in>low \<gamma>. c1 \<alpha> * c2 (subI \<gamma> \<alpha>))"
          by (simp only: sum_distrib_left)
        also have "(\<Sum>\<alpha>\<in>low \<gamma>. c1 \<alpha> * c2 (subI \<gamma> \<alpha>)) = cprod \<gamma>"
          by (simp only: cprod_def)
        finally show ?thesis by simp
      qed
      \<comment> \<open>(4) Sigma -> base via has_sum_Sigma'.\<close>
      have "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cprod \<gamma>) has_sum (f x * g x)) ra_idx"
      proof (rule has_sum_Sigma'
               [where f = "\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))"
                  and A = ra_idx and B = low and a = "f x * g x"
                  and b = "\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cprod \<gamma>"])
        show "((\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum (f x * g x))
                (Sigma ra_idx low)" by (rule step2)
      next
        fix \<gamma> :: "'a \<Rightarrow> nat" assume "\<gamma> \<in> ra_idx"
        then have "((\<lambda>\<alpha>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum
                      (ra_monomial h \<gamma> *\<^sub>R cprod \<gamma>)) (low \<gamma>)" by (rule inner_fin)
        thus "((\<lambda>\<alpha>. (\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) (\<gamma>, \<alpha>)) has_sum
                  (ra_monomial h \<gamma> *\<^sub>R cprod \<gamma>)) (low \<gamma>)" by simp
      qed
      thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cprod \<alpha>) has_sum (f x * g x)) ra_idx"
        by (simp only: h_def)
    qed
  qed
qed




subsection \<open>(1.6) Workhorse: a non-vanishing analytic function has nowhere-dense zeros\<close>

text \<open>This is the lemma the drone leaves actually consume: on a connected open set, a
  real-analytic function that is not identically zero has a zero set with empty interior
  (i.e. nowhere dense), regardless of critical points -- which is exactly how the
  analytic route walks around the Gram-minimum (critical-value) wall.\<close>

text \<open>The scalar 1-D case, proved directly by the real-variable identity theorem
  (no complex analysis): the set where all derivatives vanish is clopen in a connected
  domain.  The general multivariate workhorse below reduces to this via real-analytic
  slices.\<close>

text \<open>Helper: if all derivatives of an analytic function vanish at a point, the function
  is identically zero on the analytic Taylor ball around that point.\<close>

lemma analytic_all_derivs_zero_imp_zero_on_ball:
  fixes f :: "real \<Rightarrow> real"
  assumes ana: "real_analytic_at_1d f c"
    and z: "\<forall>n. (deriv ^^ n) f c = 0"
  obtains r where "r > 0" and "\<And>y. \<bar>y - c\<bar> < r \<Longrightarrow> f y = 0"
proof -
  from ana obtain r where r: "r > 0"
    and sums: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow>
                 (\<lambda>n. (deriv ^^ n) f c / fact n * (x - c) ^ n) sums f x"
    unfolding real_analytic_at_1d_def by blast
  have "f y = 0" if "\<bar>y - c\<bar> < r" for y
  proof -
    have "(\<lambda>n. (deriv ^^ n) f c / fact n * (y - c) ^ n) sums f y"
      by (rule sums[OF that])
    moreover have "(\<lambda>n. (deriv ^^ n) f c / fact n * (y - c) ^ n) = (\<lambda>n. 0)"
      using z by simp
    ultimately have "(\<lambda>n. (0::real)) sums f y" by simp
    moreover have "(\<lambda>n. (0::real)) sums 0" by (rule sums_zero)
    ultimately show "f y = 0" by (rule sums_unique2)
  qed
  with r show ?thesis using that by blast
qed

theorem real_analytic_1d_nowhere_dense_zeros:
  fixes f :: "real \<Rightarrow> real"
  assumes ana: "real_analytic_on f U" and conn: "connected U"
    and ex: "\<exists>x\<in>U. f x \<noteq> 0"
  shows "interior (closure {x \<in> U. f x = 0}) = {}"
proof -
  from ana have oU: "open U"
    and at: "\<And>c. c \<in> U \<Longrightarrow> real_analytic_at_1d f c"
    by (auto simp: real_analytic_on_1d_iff)

  text \<open>Smoothness on @{term U}: every derivative exists everywhere on @{term U}.\<close>
  have smooth: "f n-times_differentiable_at x" if "x \<in> U" for n x
  proof -
    from at[OF that] obtain r where r: "r > 0"
      and diff: "\<And>y. \<bar>y - x\<bar> < r \<Longrightarrow> (\<forall>m. f m-times_differentiable_at y)"
      unfolding real_analytic_at_1d_def by blast
    show ?thesis using diff[of x] r by simp
  qed

  define Z where "Z = {x \<in> U. \<forall>n. (deriv ^^ n) f x = 0}"

  text \<open>$Z$ is open in $\mathbb{R}$ and contained in $U$, hence relatively open in $U$.\<close>
  have Zsub: "Z \<subseteq> U" by (auto simp: Z_def)
  have Zopen: "open Z"
  proof (rule openI)
    fix x assume "x \<in> Z"
    then have xU: "x \<in> U" and xz: "\<forall>n. (deriv ^^ n) f x = 0" by (auto simp: Z_def)
    \<comment> \<open>analytic ball where $f \equiv 0$\<close>
    obtain r1 where r1: "r1 > 0"
      and fz: "\<And>y. \<bar>y - x\<bar> < r1 \<Longrightarrow> f y = 0"
      using analytic_all_derivs_zero_imp_zero_on_ball[OF at[OF xU] xz] by blast
    \<comment> \<open>ball inside $U$\<close>
    obtain r2 where r2: "r2 > 0" and ballU: "ball x r2 \<subseteq> U"
      using oU xU open_contains_ball by blast
    define r where "r = min r1 r2"
    have rpos: "r > 0" using r1 r2 by (simp only: r_def)
    have ballsub: "ball x r \<subseteq> Z"
    proof
      fix z assume zb: "z \<in> ball x r"
      then have zd: "dist z x < r" by (simp add: dist_commute)
      have zU: "z \<in> U" using zb ballU by (auto simp: r_def dist_commute)
      \<comment> \<open>$f$ vanishes on an open neighbourhood of $z$, so all derivatives at $z$ vanish.\<close>
      have feq: "eventually (\<lambda>w. f w = (\<lambda>_. 0) w) (nhds z)"
      proof (rule eventually_nhds_in_open[THEN eventually_mono, of "ball x r" z])
        show "open (ball x r)" by simp
        show "z \<in> ball x r" using zb by simp
      next
        fix w assume "w \<in> ball x r"
        then have "\<bar>w - x\<bar> < r" by (simp add: dist_real_def dist_commute)
        then have "\<bar>w - x\<bar> < r1" by (simp only: r_def)
        thus "f w = (\<lambda>_. 0) w" by (simp only: fz)
      qed
      have "(deriv ^^ n) f z = 0" for n
      proof -
        have "(deriv ^^ n) f z = (deriv ^^ n) (\<lambda>_. 0) z"
          by (rule higher_deriv_cong_ev[OF feq refl])
        also have "\<dots> = 0" by (simp add: kth_deriv_const_cases)
        finally show ?thesis .
      qed
      thus "z \<in> Z" using zU by (simp add: Z_def)
    qed
    show "\<exists>e>0. ball x e \<subseteq> Z" using rpos ballsub by blast
  qed
  have ZopenIn: "openin (top_of_set U) Z"
    using Zopen Zsub by (metis Int_absorb1 openin_open_Int)

  text \<open>$Z$ is closed in $U$: each derivative is continuous on $U$.\<close>
  have cont: "continuous_on U ((deriv ^^ n) f)" for n
  proof (rule continuous_at_imp_continuous_on, clarify)
    fix x assume xU: "x \<in> U"
    have "f (Suc n)-times_differentiable_at x" by (rule smooth[OF xU])
    thus "continuous (at x) ((deriv ^^ n) f)"
      by (rule k_times_differentiable_at_imp_isCont_kth_deriv[where j = n and k = n]) simp
  qed
  have Zinter: "Z = (\<Inter>n. {x \<in> U. (deriv ^^ n) f x = 0})"
    by (auto simp: Z_def)
  have ZclosedIn: "closedin (top_of_set U) Z"
    unfolding Zinter
  proof (rule closedin_INT)
    show "(UNIV :: nat set) \<noteq> {}" by simp
    fix n :: nat assume "n \<in> (UNIV :: nat set)"
    show "closedin (top_of_set U) {x \<in> U. (deriv ^^ n) f x = 0}"
      by (rule continuous_closedin_preimage_constant[OF cont])
  qed

  text \<open>If the interior of the closure were nonempty, $Z$ would be nonempty.\<close>
  define W where "W = interior (closure {x \<in> U. f x = 0})"
  have Wopen: "open W" by (simp add: W_def)
  have Zne: "Z \<noteq> {}" if WNE: "W \<noteq> {}"
  proof -
    from WNE obtain w where wW: "w \<in> W" by blast
    \<comment> \<open>$W \cap U$ is open and nonempty\<close>
    have Wsub: "W \<subseteq> closure {x \<in> U. f x = 0}" by (simp only: W_def interior_subset)
    \<comment> \<open>$w$ has a ball inside $W$, which meets $\{x\in U.\ f\,x=0\}\subseteq U$, so $W\cap U\neq\emptyset$\<close>
    obtain e where epos: "e > 0" and eball: "ball w e \<subseteq> W"
      using wW Wopen open_contains_ball by blast
    have wcl: "w \<in> closure {x \<in> U. f x = 0}" using wW Wsub by blast
    have "ball w e \<inter> {x \<in> U. f x = 0} \<noteq> {}"
    proof -
      have "w \<in> ball w e \<inter> closure {x \<in> U. f x = 0}" using wcl epos by simp
      hence "ball w e \<inter> closure {x \<in> U. f x = 0} \<noteq> {}" by blast
      thus "ball w e \<inter> {x \<in> U. f x = 0} \<noteq> {}"
        using open_Int_closure_eq_empty[OF open_ball, of w e "{x \<in> U. f x = 0}"] by blast
    qed
    then obtain u where uU: "u \<in> ball w e" "u \<in> U" "f u = 0" by blast
    have uW: "u \<in> W" using uU(1) eball by blast
    \<comment> \<open>so $V = W \cap U$ is open and nonempty; on it $f \equiv 0$ by continuity\<close>
    define V where "V = W \<inter> U"
    have Vopen: "open V" unfolding V_def by (intro open_Int Wopen oU)
    have uV: "u \<in> V" using uW uU(2) by (simp add: V_def)
    have fzeroV: "f v = 0" if "v \<in> V" for v
    proof -
      have vW: "v \<in> W" and vU: "v \<in> U" using that by (auto simp: V_def)
      have vcl: "v \<in> closure {x \<in> U. f x = 0}" using vW Wsub by blast
      \<comment> \<open>$f$ is continuous at $v$ (a point of the open set $U$)\<close>
      have contv: "continuous (at v) f"
      proof -
        have "f (Suc 0)-times_differentiable_at v" by (rule smooth[OF vU])
        thus ?thesis by (rule k_times_differentiable_at_imp_isCont)
      qed
      \<comment> \<open>limit of zeros through the closure\<close>
      have "isCont f v" using contv by simp
      from vcl obtain s where s: "\<And>k. s k \<in> {x \<in> U. f x = 0}" "s \<longlonglongrightarrow> v"
        using closure_sequential by blast
      have "(\<lambda>k. f (s k)) \<longlonglongrightarrow> f v"
        using \<open>isCont f v\<close> s(2) by (simp only: continuous_within isCont_tendsto_compose)
      moreover have "(\<lambda>k. f (s k)) = (\<lambda>k. 0)" using s(1) by auto
      ultimately have "(\<lambda>k. (0::real)) \<longlonglongrightarrow> f v" by simp
      thus "f v = 0" by (simp only: LIMSEQ_const_iff)
    qed
    \<comment> \<open>$f \equiv 0$ on the open ball around $u$ inside $V$; all derivatives at $u$ vanish\<close>
    obtain \<rho> where \<rho>: "\<rho> > 0" and rball: "ball u \<rho> \<subseteq> V"
      using uV Vopen open_contains_ball by blast
    have feq: "eventually (\<lambda>w. f w = (\<lambda>_. 0) w) (nhds u)"
    proof (rule eventually_nhds_in_open[THEN eventually_mono, of "ball u \<rho>" u])
      show "open (ball u \<rho>)" by simp
      show "u \<in> ball u \<rho>" using \<rho> by simp
    next
      fix w assume "w \<in> ball u \<rho>"
      then have "w \<in> V" using rball by blast
      thus "f w = (\<lambda>_. 0) w" by (simp only: fzeroV)
    qed
    have "(deriv ^^ n) f u = 0" for n
    proof -
      have "(deriv ^^ n) f u = (deriv ^^ n) (\<lambda>_. 0) u"
        by (rule higher_deriv_cong_ev[OF feq refl])
      also have "\<dots> = 0" by (simp add: kth_deriv_const_cases)
      finally show ?thesis .
    qed
    then have "u \<in> Z" using uU(2) by (simp add: Z_def)
    thus "Z \<noteq> {}" by blast
  qed

  text \<open>Connectedness: $Z$ is clopen in $U$, so $Z = \emptyset$ or $Z = U$.\<close>
  have clopen: "Z = {} \<or> Z = U"
    using conn ZopenIn ZclosedIn unfolding connected_clopen by blast

  text \<open>If $W \neq \emptyset$ then $Z \neq \emptyset$, hence $Z = U$, forcing $f \equiv 0$ on $U$,
    contradicting the assumption.\<close>
  show ?thesis
  proof (rule ccontr)
    assume "interior (closure {x \<in> U. f x = 0}) \<noteq> {}"
    then have WNE: "W \<noteq> {}" by (simp add: W_def)
    then have "Z \<noteq> {}" by (rule Zne)
    with clopen have "Z = U" by blast
    have "f x = 0" if "x \<in> U" for x
    proof -
      have "x \<in> Z" using that \<open>Z = U\<close> by simp
      then have "\<forall>n. (deriv ^^ n) f x = 0" by (simp add: Z_def)
      then have "(deriv ^^ 0) f x = 0" by blast
      thus "f x = 0" by simp
    qed
    with ex show False by blast
  qed
qed


subsection \<open>Degree of a multi-index and the monomial scaling identity\<close>


text \<open>Scaling a vector by a real \<open>t\<close> scales the basis monomial by \<open>t^(deg \<alpha>)\<close>.\<close>


text \<open>A convergent real power series about \<open>c\<close> makes \<open>f\<close> real-analytic at \<open>c\<close>
  (term-by-term differentiation identifies the coefficients with the Taylor coefficients).\<close>
lemma real_powser_imp_real_analytic_at_1d:
  fixes f :: "real \<Rightarrow> real"
  assumes r: "0 < r"
    and PS: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow> (\<lambda>n. a n * (x - c) ^ n) sums f x"
  shows "real_analytic_at_1d f c"
proof -
  have sums_a: "(\<lambda>n. a n * z ^ n) sums f (c + z)" if "\<bar>z\<bar> < r" for z
  proof -
    have "\<bar>(c + z) - c\<bar> < r" using that by simp
    from PS[OF this] show ?thesis by simp
  qed
  have summ_a: "summable (\<lambda>n. a n * z ^ n)" if "\<bar>z\<bar> < r" for z
    using sums_a[OF that] by (rule sums_summable)
  have summ_diffs: "summable (\<lambda>m. (diffs ^^ n) a m * z ^ m)" if "\<bar>z\<bar> < r" for n z
    using that
  proof (induction n arbitrary: z)
    case 0
    thus ?case using summ_a by simp
  next
    case (Suc n)
    have "summable (\<lambda>m. diffs ((diffs ^^ n) a) m * z ^ m)"
    proof (rule termdiff_converges[where K = r])
      show "norm z < r" using Suc.prems by simp
      fix w :: real assume "norm w < r"
      hence "\<bar>w\<bar> < r" by simp
      thus "summable (\<lambda>m. (diffs ^^ n) a m * w ^ m)" by (rule Suc.IH)
    qed
    thus ?case by simp
  qed
  define S where "S = (\<lambda>n y. \<Sum>m. (diffs ^^ n) a m * (y - c) ^ m)"
  have S0_eq_f: "S 0 x = f x" if "\<bar>x - c\<bar> < r" for x
  proof -
    from sums_a[of "x - c"] that have "(\<lambda>n. a n * (x - c) ^ n) sums f x" by simp
    thus ?thesis by (simp add: S_def sums_iff)
  qed
  have S_deriv: "(S n has_field_derivative S (Suc n) x) (at x)"
    if "\<bar>x - c\<bar> < r" for n x
  proof -
    have H: "((\<lambda>w. \<Sum>m. (diffs ^^ n) a m * w ^ m)
               has_field_derivative (\<Sum>m. diffs ((diffs ^^ n) a) m * (x - c) ^ m))
              (at (x - c))"
    proof (rule termdiffs_strong'[where K = r])
      fix w :: real assume "norm w < r"
      thus "summable (\<lambda>m. (diffs ^^ n) a m * w ^ m)" using summ_diffs by simp
    next
      show "norm (x - c) < r" using that by simp
    qed
    have shift: "((\<lambda>y. y - c) has_field_derivative 1) (at x)"
      by (auto intro!: derivative_eq_intros)
    have "((\<lambda>y. (\<lambda>w. \<Sum>m. (diffs ^^ n) a m * w ^ m) (y - c))
             has_field_derivative
             (\<Sum>m. diffs ((diffs ^^ n) a) m * (x - c) ^ m) * 1) (at x)"
      by (rule DERIV_chain'[OF shift]) (use H in simp)
    thus ?thesis by (simp add: S_def)
  qed
  have main: "\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow>
                f n-times_differentiable_at x \<and> (deriv ^^ n) f x = S n x" for n
  proof (induction n)
    case 0
    show ?case by (auto simp: S0_eq_f)
  next
    case (Suc n)
    show ?case
    proof (intro allI impI conjI)
      fix x assume xc: "\<bar>x - c\<bar> < r"
      have ballopen: "{y. \<bar>y - c\<bar> < r} = ball c r"
        by (auto simp: dist_real_def abs_minus_commute)
      have eqA: "(deriv ^^ n) f y = S n y" if "\<bar>y - c\<bar> < r" for y
        using Suc.IH that by blast
      have dn_deriv: "((deriv ^^ n) f has_field_derivative S (Suc n) x) (at x)"
      proof (rule has_field_derivative_transform_within_open
                   [where f = "S n" and S = "{y. \<bar>y - c\<bar> < r}"])
        show "(S n has_field_derivative S (Suc n) x) (at x)" by (rule S_deriv[OF xc])
        show "open {y. \<bar>y - c\<bar> < r}" by (simp add: ballopen)
        show "x \<in> {y. \<bar>y - c\<bar> < r}" using xc by simp
        show "\<And>y. y \<in> {y. \<bar>y - c\<bar> < r} \<Longrightarrow> S n y = (deriv ^^ n) f y"
          using eqA by auto
      qed
      show "(deriv ^^ Suc n) f x = S (Suc n) x"
        using dn_deriv by (simp only: kth_deriv_Suc DERIV_imp_deriv)
      show "f (Suc n)-times_differentiable_at x"
        unfolding k_times_differentiable_at.simps(2)
      proof
        show "\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> f n-times_differentiable_at y"
        proof (intro exI[where x = "r - \<bar>x - c\<bar>"] conjI allI impI)
          show "0 < r - \<bar>x - c\<bar>" using xc by simp
          fix y assume "\<bar>y - x\<bar> < r - \<bar>x - c\<bar>"
          hence "\<bar>y - c\<bar> < r" by linarith
          thus "f n-times_differentiable_at y" using Suc.IH by blast
        qed
      next
        have "(deriv ^^ Suc n) f x = S (Suc n) x"
          using dn_deriv by (simp only: kth_deriv_Suc DERIV_imp_deriv)
        with dn_deriv
        show "((deriv ^^ n) f has_derivative (\<lambda>h. (deriv ^^ Suc n) f x * h)) (at x)"
          by (simp only: has_field_derivative_def)
      qed
    qed
  qed
  have diffs_fact: "(diffs ^^ n) g 0 = fact n * g n" for n and g :: "nat \<Rightarrow> real"
  proof -
    have gen: "fact m * (diffs ^^ n) g m = fact (m + n) * g (m + n)" for m
    proof (induction n arbitrary: g m)
      case 0 show ?case by simp
    next
      case (Suc n)
      have "fact m * (diffs ^^ Suc n) g m = fact m * (diffs ^^ n) (diffs g) m"
        by (simp only: funpow_Suc_right o_apply)
      also have "\<dots> = fact (m + n) * (diffs g) (m + n)"
        using Suc.IH[of m "diffs g"] by simp
      also have "\<dots> = fact (m + n) * (of_nat (Suc (m + n)) * g (Suc (m + n)))"
        by (simp only: diffs_def)
      also have "\<dots> = fact (Suc (m + n)) * g (Suc (m + n))"
        by (simp add: algebra_simps)
      finally show ?case by (simp add: add.commute)
    qed
    from gen[of 0] show ?thesis by simp
  qed
  have coeff: "a n = (deriv ^^ n) f c / fact n" for n
  proof -
    have "\<bar>c - c\<bar> < r" using r by simp
    with main[of n] have "(deriv ^^ n) f c = S n c" by blast
    also have "S n c = (diffs ^^ n) a 0" by (simp add: S_def)
    also have "\<dots> = fact n * a n" by (rule diffs_fact)
    finally have "(deriv ^^ n) f c = fact n * a n" .
    thus ?thesis by simp
  qed
  have smooth: "f n-times_differentiable_at x" if "\<bar>x - c\<bar> < r" for x n
    using main[of n] that by blast
  show ?thesis
    unfolding real_analytic_at_1d_def
  proof (intro exI[where x = r] conjI allI impI)
    show "0 < r" by (rule r)
  next
    fix x n assume "\<bar>x - c\<bar> < r" thus "f n-times_differentiable_at x"
      by (rule smooth)
  next
    fix x assume xc: "\<bar>x - c\<bar> < r"
    from PS[OF xc] show
      "(\<lambda>n. (deriv ^^ n) f c / fact n * (x - c) ^ n) sums f x"
      by (simp only: coeff)
  qed
qed

lemma ra_monomial_scaleR:
  fixes d :: "'a::euclidean_space"
  shows "ra_monomial (t *\<^sub>R d) \<alpha> = t ^ (ra_deg \<alpha>) * ra_monomial d \<alpha>"
proof -
  have "ra_monomial (t *\<^sub>R d) \<alpha> = (\<Prod>b\<in>Basis. ((t *\<^sub>R d) \<bullet> b) ^ (\<alpha> b))"
    by (simp only: ra_monomial_def)
  also have "\<dots> = (\<Prod>b\<in>Basis. (t * (d \<bullet> b)) ^ (\<alpha> b))"
    by (simp only: inner_scaleR_left)
  also have "\<dots> = (\<Prod>b\<in>Basis. t ^ (\<alpha> b) * (d \<bullet> b) ^ (\<alpha> b))"
    by (simp only: power_mult_distrib)
  also have "\<dots> = (\<Prod>b\<in>Basis. t ^ (\<alpha> b)) * (\<Prod>b\<in>Basis. (d \<bullet> b) ^ (\<alpha> b))"
    by (simp only: prod.distrib)
  also have "(\<Prod>b\<in>Basis. t ^ (\<alpha> b)) = t ^ (\<Sum>b\<in>Basis. \<alpha> b)"
    by (simp only: power_sum)
  finally show ?thesis by (simp only: ra_deg_def ra_monomial_def)
qed

text \<open>Each degree block of \<open>ra_idx\<close> is finite.\<close>

lemma ra_deg_block_finite:
  fixes n :: nat
  shows "finite {\<alpha>::'a::euclidean_space \<Rightarrow> nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n}"
proof -
  have "{\<alpha>::'a \<Rightarrow> nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n}
          \<subseteq> {hh. \<forall>x::'a. (x \<in> Basis \<longrightarrow> hh x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
  proof (rule subsetI)
    fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> {\<alpha>. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n}"
    then have a1: "\<alpha> \<in> ra_idx" and a2: "ra_deg \<alpha> = n" by auto
    have "\<forall>x::'a. (x \<in> Basis \<longrightarrow> \<alpha> x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> \<alpha> x = 0)"
    proof (intro allI conjI impI)
      fix x :: 'a assume xB: "x \<in> Basis"
      have "\<alpha> x \<le> (\<Sum>b\<in>Basis. \<alpha> b)"
        using xB by (intro member_le_sum) auto
      also have "\<dots> = n" using a2 by (simp only: ra_deg_def)
      finally show "\<alpha> x \<in> {0..n}" by simp
    next
      fix x :: 'a assume "x \<notin> Basis"
      with a1 show "\<alpha> x = 0" by (auto simp: ra_idx_def)
    qed
    thus "\<alpha> \<in> {hh. \<forall>x::'a. (x \<in> Basis \<longrightarrow> hh x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
      by simp
  qed
  moreover have "finite {hh::'a\<Rightarrow>nat. \<forall>x. (x \<in> Basis \<longrightarrow> hh x \<in> {0..n}) \<and> (x \<notin> Basis \<longrightarrow> hh x = (0::nat))}"
    by (rule finite_set_of_finite_funs) auto
  ultimately show ?thesis by (rule finite_subset)
qed

text \<open>The basis monomial is bounded in absolute value by \<open>(norm h) ^ (deg \<alpha>)\<close>.\<close>

lemma abs_ra_monomial_le:
  fixes h :: "'a::euclidean_space"
  shows "\<bar>ra_monomial h \<alpha>\<bar> \<le> (norm h) ^ (ra_deg \<alpha>)"
proof -
  have "\<bar>ra_monomial h \<alpha>\<bar> = (\<Prod>b\<in>Basis. \<bar>h \<bullet> b\<bar> ^ (\<alpha> b))"
    by (simp only: ra_monomial_def abs_prod power_abs)
  also have "\<dots> \<le> (\<Prod>b\<in>Basis. (norm h) ^ (\<alpha> b))"
  proof (rule prod_mono)
    fix b :: 'a assume "b \<in> Basis"
    have "\<bar>h \<bullet> b\<bar> \<le> norm h" using \<open>b \<in> Basis\<close> by (rule Basis_le_norm)
    thus "0 \<le> \<bar>h \<bullet> b\<bar> ^ (\<alpha> b) \<and> \<bar>h \<bullet> b\<bar> ^ (\<alpha> b) \<le> (norm h) ^ (\<alpha> b)"
      by (auto intro: power_mono)
  qed
  also have "\<dots> = (norm h) ^ (\<Sum>b\<in>Basis. \<alpha> b)"
    by (simp only: power_sum)
  finally show ?thesis by (simp only: ra_deg_def)
qed

text \<open>The basis monomial at \<open>0\<close> is the indicator of the zero multi-index.\<close>

lemma ra_monomial_zero:
  fixes \<alpha> :: "'a::euclidean_space \<Rightarrow> nat"
  shows "ra_monomial (0::'a) \<alpha> = (if ra_deg \<alpha> = 0 then 1 else 0)"
proof (cases "ra_deg \<alpha> = 0")
  case True
  then have "\<And>b. b \<in> Basis \<Longrightarrow> \<alpha> b = 0"
    using finite_Basis by (simp add: ra_deg_def)
  thus ?thesis using True by (simp add: ra_monomial_def)
next
  case False
  then obtain b where bB: "b \<in> Basis" and apos: "\<alpha> b \<noteq> 0"
    using finite_Basis by (auto simp: ra_deg_def)
  have "ra_monomial (0::'a) \<alpha> = (\<Prod>b\<in>Basis. (0 \<bullet> b) ^ (\<alpha> b))"
    by (simp only: ra_monomial_def)
  also have "\<dots> = 0"
    using bB apos by (intro prod_zero[OF finite_Basis]) auto
  finally show ?thesis using False by simp
qed

subsection \<open>Real-analytic functions are continuous\<close>

text \<open>Continuity of \<open>f\<close> at \<open>x0\<close>, derived directly from the local convergent power series
  by a domination estimate: \<open>\<bar>f x - f x0\<bar> \<le> (dist x x0 / t) \<cdot> S\<close> for \<open>x\<close> close to \<open>x0\<close>,
  where \<open>S\<close> is the (finite) sum of \<open>t^(deg \<alpha>) \<cdot> \<bar>c \<alpha>\<bar>\<close> over the multi-indices.\<close>

lemma real_analytic_on_imp_continuous:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes ana: "real_analytic_on f U" and xU: "x0 \<in> U"
  shows "continuous (at x0) f"
proof -
  from ana xU obtain r c where r: "0 < r"
    and HS: "\<And>x. dist x x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x) ra_idx"
    unfolding real_analytic_on_def by blast
  define e1 where "e1 = (\<Sum>b\<in>(Basis::'a set). b)"
  define t where "t = r / (2 * (norm e1 + 1))"
  have ne1: "norm e1 + 1 > 0" by (simp add: add_nonneg_pos)
  have t_pos: "0 < t" using r ne1 by (simp add: t_def)
  define x2 where "x2 = x0 + t *\<^sub>R e1"
  have dist_x2: "dist x2 x0 < r"
  proof -
    have "dist x2 x0 = norm (t *\<^sub>R e1)" by (simp add: x2_def dist_norm)
    also have "\<dots> = t * norm e1" using t_pos by simp
    also have "\<dots> \<le> t * (norm e1 + 1)" using t_pos by simp
    also have "t * (norm e1 + 1) = r / 2"
      using ne1 by (simp add: t_def field_simps)
    also have "r / 2 < r" using r by simp
    finally show ?thesis .
  qed
  \<comment> \<open>at \<open>x2\<close> the monomial is exactly \<open>t^(deg \<alpha>)\<close>\<close>
  have mono_x2: "ra_monomial (x2 - x0) \<alpha> = t ^ (ra_deg \<alpha>)" for \<alpha>
  proof -
    have "x2 - x0 = t *\<^sub>R e1" by (simp add: x2_def)
    have inb: "(x2 - x0) \<bullet> b = t" if "b \<in> Basis" for b
    proof -
      have "(x2 - x0) \<bullet> b = (t *\<^sub>R e1) \<bullet> b" by (simp add: x2_def)
      also have "\<dots> = t * (e1 \<bullet> b)" by (simp only: inner_scaleR_left)
      also have "e1 \<bullet> b = 1" using that by (simp add: e1_def inner_sum_left inner_Basis)
      finally show ?thesis by simp
    qed
    have "ra_monomial (x2 - x0) \<alpha> = (\<Prod>b\<in>Basis. ((x2 - x0) \<bullet> b) ^ (\<alpha> b))"
      by (simp only: ra_monomial_def)
    also have "\<dots> = (\<Prod>b\<in>Basis. t ^ (\<alpha> b))"
      by (intro prod.cong refl) (simp only: inb)
    also have "\<dots> = t ^ (\<Sum>b\<in>Basis. \<alpha> b)" by (simp only: power_sum)
    finally show ?thesis by (simp only: ra_deg_def)
  qed
  \<comment> \<open>hence \<open>t^(deg \<alpha>) \<cdot> \<bar>c \<alpha>\<bar>\<close> is summable\<close>
  have HSx2: "((\<lambda>\<alpha>. t ^ (ra_deg \<alpha>) * c \<alpha>) has_sum f x2) ra_idx"
  proof -
    have "((\<lambda>\<alpha>. ra_monomial (x2 - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x2) ra_idx" by (rule HS[OF dist_x2])
    thus ?thesis by (simp add: mono_x2)
  qed
  have abs_summ: "(\<lambda>\<alpha>. t ^ (ra_deg \<alpha>) * \<bar>c \<alpha>\<bar>) summable_on ra_idx"
  proof -
    have sm: "(\<lambda>\<alpha>. t ^ (ra_deg \<alpha>) * c \<alpha>) summable_on ra_idx"
      by (rule has_sum_imp_summable[OF HSx2])
    have "(\<lambda>\<alpha>. norm (t ^ (ra_deg \<alpha>) * c \<alpha>)) summable_on ra_idx"
      using sm[THEN iffD1[OF summable_on_iff_abs_summable_on_real]] .
    moreover have "\<And>\<alpha>. norm (t ^ (ra_deg \<alpha>) * c \<alpha>) = t ^ (ra_deg \<alpha>) * \<bar>c \<alpha>\<bar>"
      using t_pos by (simp add: abs_mult)
    ultimately show ?thesis by simp
  qed
  define S where "S = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. t ^ (ra_deg \<alpha>) * \<bar>c \<alpha>\<bar>)"
  have HSS: "((\<lambda>\<alpha>. t ^ (ra_deg \<alpha>) * \<bar>c \<alpha>\<bar>) has_sum S) ra_idx"
    unfolding S_def using abs_summ by (rule has_sum_infsum)
  \<comment> \<open>the key domination estimate around \<open>x0\<close>\<close>
  have estimate: "\<bar>f x - f x0\<bar> \<le> (dist x x0 / t) * S" if dx: "dist x x0 \<le> t" for x
  proof -
    have dxr: "dist x x0 < r"
    proof -
      have "t \<le> t * (norm e1 + 1)" using t_pos by simp
      also have "t * (norm e1 + 1) = r / 2" using ne1 by (simp add: t_def field_simps)
      also have "r / 2 < r" using r by simp
      finally have "t < r" .
      thus ?thesis using dx by linarith
    qed
    have HSx: "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> * c \<alpha>) has_sum f x) ra_idx"
      using HS[OF dxr] by simp
    have HSx0: "((\<lambda>\<alpha>. ra_monomial ((0::'a)) \<alpha> * c \<alpha>) has_sum f x0) ra_idx"
    proof -
      have "dist x0 x0 < r" using r by simp
      from HS[OF this] show ?thesis by simp
    qed
    \<comment> \<open>the difference is a single \<open>has_sum\<close>\<close>
    have HSdiff: "((\<lambda>\<alpha>. (ra_monomial (x - x0) \<alpha> - ra_monomial (0::'a) \<alpha>) * c \<alpha>)
                     has_sum (f x - f x0)) ra_idx"
    proof -
      have HSm0: "((\<lambda>\<alpha>. - (ra_monomial (0::'a) \<alpha> * c \<alpha>)) has_sum (- f x0)) ra_idx"
        by (subst has_sum_uminus, simp add: HSx0)
      have "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> * c \<alpha> + (- (ra_monomial (0::'a) \<alpha> * c \<alpha>)))
               has_sum (f x + (- f x0))) ra_idx"
        by (rule has_sum_add[OF HSx HSm0])
      thus ?thesis by (simp add: left_diff_distrib)
    qed
    \<comment> \<open>the dominating series \<open>(dist x x0 / t) \<cdot> t^(deg \<alpha>) \<cdot> \<bar>c \<alpha>\<bar>\<close>\<close>
    have HSdom: "((\<lambda>\<alpha>. (dist x x0 / t) * (t ^ (ra_deg \<alpha>) * \<bar>c \<alpha>\<bar>)) has_sum ((dist x x0 / t) * S)) ra_idx"
      by (rule has_sum_cmult_right[OF HSS])
    \<comment> \<open>term-by-term domination\<close>
    have termbound: "\<bar>(ra_monomial (x - x0) \<alpha> - ra_monomial (0::'a) \<alpha>) * c \<alpha>\<bar>
                       \<le> (dist x x0 / t) * (t ^ (ra_deg \<alpha>) * \<bar>c \<alpha>\<bar>)" for \<alpha>
    proof (cases "ra_deg \<alpha> = 0")
      case True
      then have allz: "\<And>b. b \<in> Basis \<Longrightarrow> \<alpha> b = 0"
        using finite_Basis by (simp add: ra_deg_def)
      have e1: "ra_monomial (x - x0) \<alpha> = 1"
        by (simp add: ra_monomial_def allz)
      have e2: "ra_monomial (0::'a) \<alpha> = 1"
        by (simp add: ra_monomial_def allz)
      have "\<bar>(ra_monomial (x - x0) \<alpha> - ra_monomial (0::'a) \<alpha>) * c \<alpha>\<bar> = 0"
        by (simp add: e1 e2)
      moreover have "0 \<le> (dist x x0 / t) * (t ^ (ra_deg \<alpha>) * \<bar>c \<alpha>\<bar>)"
        using t_pos by (intro mult_nonneg_nonneg) auto
      ultimately show ?thesis by linarith
    next
      case False
      then have dpos: "ra_deg \<alpha> \<ge> 1" by simp
      have m0: "ra_monomial (0::'a) \<alpha> = 0" by (simp add: ra_monomial_zero False)
      have nh: "norm (x - x0) = dist x x0" by (simp only: dist_norm)
      have "\<bar>(ra_monomial (x - x0) \<alpha> - ra_monomial (0::'a) \<alpha>) * c \<alpha>\<bar>
              = \<bar>ra_monomial (x - x0) \<alpha>\<bar> * \<bar>c \<alpha>\<bar>" by (simp add: m0 abs_mult)
      also have "\<bar>ra_monomial (x - x0) \<alpha>\<bar> \<le> (dist x x0) ^ (ra_deg \<alpha>)"
        using abs_ra_monomial_le[of "x - x0" \<alpha>] by (simp only: nh)
      also have "(dist x x0) ^ (ra_deg \<alpha>) \<le> (dist x x0 / t) * t ^ (ra_deg \<alpha>)"
      proof -
        obtain k where k: "ra_deg \<alpha> = Suc k" using dpos by (cases "ra_deg \<alpha>") auto
        have dnn: "0 \<le> dist x x0" by simp
        have "(dist x x0) ^ (Suc k) = dist x x0 * (dist x x0) ^ k" by simp
        also have "\<dots> \<le> dist x x0 * t ^ k"
          using dnn dx by (intro mult_left_mono power_mono) auto
        also have "dist x x0 * t ^ k = (dist x x0 / t) * t ^ (Suc k)"
          using t_pos by (simp add: field_simps)
        finally show ?thesis by (simp only: k)
      qed
      finally have "\<bar>(ra_monomial (x - x0) \<alpha> - ra_monomial (0::'a) \<alpha>) * c \<alpha>\<bar>
                      \<le> ((dist x x0 / t) * t ^ (ra_deg \<alpha>)) * \<bar>c \<alpha>\<bar>"
        by (simp only: mult_right_mono)
      thus ?thesis by (simp only: mult.assoc)
    qed
    have "norm (f x - f x0) \<le> (dist x x0 / t) * S"
      by (rule norm_infsum_le[OF HSdiff HSdom]) (use termbound in simp)
    thus ?thesis by simp
  qed
  \<comment> \<open>continuity by the squeeze \<open>\<bar>f x - f x0\<bar> \<le> (dist x x0 / t) \<cdot> S \<rightarrow> 0\<close>\<close>
  have Snn: "0 \<le> S" unfolding S_def
  proof (rule infsum_nonneg)
    fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_idx"
    have "0 \<le> t ^ (ra_deg \<alpha>)" using t_pos by simp
    thus "0 \<le> t ^ (ra_deg \<alpha>) * \<bar>c \<alpha>\<bar>" by (simp only: mult_nonneg_nonneg)
  qed
  \<comment> \<open>the dominating function \<open>x \<mapsto> (dist x x0 / t) \<cdot> S\<close> tends to \<open>0\<close> at \<open>x0\<close>\<close>
  have domlim: "((\<lambda>x. (dist x x0 / t) * S) \<longlongrightarrow> 0) (at x0)"
  proof -
    have idlim: "((\<lambda>x::'a. x) \<longlongrightarrow> x0) (at x0)" by (simp only: tendsto_ident_at)
    have dl: "((\<lambda>x. dist x x0) \<longlongrightarrow> dist x0 x0) (at x0)"
      by (intro tendsto_dist idlim tendsto_const)
    have "((\<lambda>x. dist x x0) \<longlongrightarrow> 0) (at x0)" using dl by simp
    hence "((\<lambda>x. dist x x0 * (S / t)) \<longlongrightarrow> 0 * (S / t)) (at x0)"
      by (rule tendsto_mult_right)
    moreover have "(\<lambda>x. dist x x0 * (S / t)) = (\<lambda>x. (dist x x0 / t) * S)"
      by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>the difference is eventually dominated\<close>
  have evb: "\<forall>\<^sub>F x in at x0. norm (f x - f x0) \<le> norm ((dist x x0 / t) * S)"
  proof -
    have "\<forall>\<^sub>F x in at x0. x \<in> ball x0 t"
      by (rule eventually_at_in_open'[OF open_ball]) (simp add: t_pos)
    then have "\<forall>\<^sub>F x in at x0. dist x x0 < t"
      by (rule eventually_mono) (simp add: dist_commute)
    thus ?thesis
    proof (rule eventually_mono)
      fix x assume "dist x x0 < t"
      hence dxt: "dist x x0 \<le> t" by simp
      have "norm (f x - f x0) = \<bar>f x - f x0\<bar>" by simp
      also have "\<dots> \<le> (dist x x0 / t) * S" by (rule estimate[OF dxt])
      also have "\<dots> = norm ((dist x x0 / t) * S)"
        using t_pos Snn by simp
      finally show "norm (f x - f x0) \<le> norm ((dist x x0 / t) * S)" .
    qed
  qed
  have "((\<lambda>x. f x - f x0) \<longlongrightarrow> 0) (at x0)"
    by (rule Lim_transform_bound[OF evb domlim])
  hence "(f \<longlongrightarrow> f x0) (at x0)" by (simp only: LIM_zero_iff)
  thus ?thesis by (simp only: continuous_at)
qed

subsection \<open>The affine slice of a real-analytic function is real-analytic (at a point)\<close>

text \<open>If \<open>f\<close> is real-analytic at the point \<open>a + t0 *\<^sub>R d\<close> via a local convergent power
  series, then the one-dimensional slice \<open>s \<mapsto> f (a + s *\<^sub>R d)\<close> is real-analytic at \<open>t0\<close>,
  provided the direction \<open>d\<close> is nonzero.\<close>

lemma real_analytic_slice_at_point:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes ana: "real_analytic_on f U"
    and inU: "a + t0 *\<^sub>R d \<in> U"
    and dnz: "d \<noteq> 0"
  shows "real_analytic_at_1d (\<lambda>s. f (a + s *\<^sub>R d)) t0"
proof -
  define x0 where "x0 = a + t0 *\<^sub>R d"
  have oU: "open U" using ana by (simp only: real_analytic_on_def)
  from ana inU obtain r c where r: "0 < r"
    and HS: "\<And>x. dist x x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x) ra_idx"
    unfolding real_analytic_on_def x0_def by blast
  define nd where "nd = norm d"
  have nd_pos: "0 < nd" using dnz by (simp add: nd_def)
  define r' where "r' = r / nd"
  have r'_pos: "0 < r'" using r nd_pos by (simp add: r'_def)
  \<comment> \<open>the slice coefficients: sum the basis-monomial coefficients over each degree block\<close>
  define blk where "blk = (\<lambda>n. {\<alpha>::'a\<Rightarrow>nat. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = n})"
  define acoef where "acoef = (\<lambda>n. \<Sum>\<alpha>\<in>blk n. ra_monomial d \<alpha> * c \<alpha>)"
  have blk_fin: "finite (blk n)" for n
    unfolding blk_def by (rule ra_deg_block_finite)
  \<comment> \<open>the central power-series identity along the slice\<close>
  have PS: "(\<lambda>n. acoef n * (s - t0) ^ n) sums f (a + s *\<^sub>R d)" if slt: "\<bar>s - t0\<bar> < r'" for s
  proof -
    define u where "u = s - t0"
    have ult: "\<bar>u\<bar> < r'" using slt by (simp only: u_def)
    have pt_eq: "a + s *\<^sub>R d = x0 + u *\<^sub>R d"
      by (simp only: x0_def u_def algebra_simps)
    have dist_lt: "dist (x0 + u *\<^sub>R d) x0 < r"
    proof -
      have "dist (x0 + u *\<^sub>R d) x0 = norm (u *\<^sub>R d)" by (simp add: dist_norm)
      also have "\<dots> = \<bar>u\<bar> * nd" by (simp add: nd_def)
      also have "\<dots> < r' * nd" using ult nd_pos by (simp only: mult_strict_right_mono)
      also have "\<dots> = r" using nd_pos by (simp add: r'_def)
      finally show ?thesis .
    qed
    \<comment> \<open>multivariate has_sum at this point, with monomial scaled by \<open>u\<close>\<close>
    have HSu: "((\<lambda>\<alpha>. (u ^ (ra_deg \<alpha>) * ra_monomial d \<alpha>) * c \<alpha>) has_sum f (x0 + u *\<^sub>R d)) ra_idx"
    proof -
      have "((\<lambda>\<alpha>. ra_monomial ((x0 + u *\<^sub>R d) - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f (x0 + u *\<^sub>R d)) ra_idx"
        by (rule HS[OF dist_lt])
      moreover have "(x0 + u *\<^sub>R d) - x0 = u *\<^sub>R d" by simp
      ultimately have "((\<lambda>\<alpha>. ra_monomial (u *\<^sub>R d) \<alpha> *\<^sub>R c \<alpha>) has_sum f (x0 + u *\<^sub>R d)) ra_idx"
        by simp
      thus ?thesis by (simp add: ra_monomial_scaleR)
    qed
    \<comment> \<open>reindex \<open>ra_idx\<close> as the disjoint union of degree blocks\<close>
    have reidx: "((\<lambda>q. u ^ (fst q) * (ra_monomial d (snd q) * c (snd q))) has_sum f (x0 + u *\<^sub>R d))
                   (Sigma (UNIV::nat set) blk)"
    proof -
      have "((\<lambda>\<alpha>. (u ^ (ra_deg \<alpha>) * ra_monomial d \<alpha>) * c \<alpha>) has_sum f (x0 + u *\<^sub>R d)) ra_idx
              = ((\<lambda>q. u ^ (fst q) * (ra_monomial d (snd q) * c (snd q))) has_sum f (x0 + u *\<^sub>R d))
                   (Sigma (UNIV::nat set) blk)"
      proof (rule has_sum_reindex_bij_witness
               [where j = "\<lambda>\<alpha>. (ra_deg \<alpha>, \<alpha>)" and i = snd])
        fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_idx"
        show "snd (ra_deg \<alpha>, \<alpha>) = \<alpha>" by simp
      next
        fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_idx"
        thus "(ra_deg \<alpha>, \<alpha>) \<in> Sigma (UNIV::nat set) blk" by (simp add: blk_def)
      next
        fix q :: "nat \<times> ('a \<Rightarrow> nat)" assume "q \<in> Sigma (UNIV::nat set) blk"
        then obtain m \<beta> where q: "q = (m, \<beta>)" and "\<beta> \<in> blk m" by (cases q) auto
        then have dn: "ra_deg \<beta> = m" by (simp add: blk_def)
        show "(ra_deg (snd q), snd q) = q" by (simp add: q dn)
      next
        fix q :: "nat \<times> ('a \<Rightarrow> nat)" assume "q \<in> Sigma (UNIV::nat set) blk"
        then obtain m \<beta> where q: "q = (m, \<beta>)" and "\<beta> \<in> blk m" by (cases q, simp)
        thus "snd q \<in> ra_idx" by (simp add: blk_def)
      next
        fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_idx"
        show "u ^ (fst (ra_deg \<alpha>, \<alpha>)) * (ra_monomial d (snd (ra_deg \<alpha>, \<alpha>)) * c (snd (ra_deg \<alpha>, \<alpha>)))
                 = (u ^ (ra_deg \<alpha>) * ra_monomial d \<alpha>) * c \<alpha>"
          by (simp add: mult.assoc)
      qed simp
      with HSu show ?thesis by blast
    qed
    \<comment> \<open>collapse each finite degree block\<close>
    have inner: "((\<lambda>\<alpha>. u ^ n * (ra_monomial d \<alpha> * c \<alpha>)) has_sum (acoef n * u ^ n)) (blk n)" for n
    proof -
      have "((\<lambda>\<alpha>. u ^ n * (ra_monomial d \<alpha> * c \<alpha>)) has_sum
               (\<Sum>\<alpha>\<in>blk n. u ^ n * (ra_monomial d \<alpha> * c \<alpha>))) (blk n)"
        by (rule has_sum_finite[OF blk_fin])
      moreover have "(\<Sum>\<alpha>\<in>blk n. u ^ n * (ra_monomial d \<alpha> * c \<alpha>)) = acoef n * u ^ n"
        by (simp only: acoef_def sum_distrib_left mult.commute)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>partition sum: from Sigma to the base nat-indexed series\<close>
    have basesum: "((\<lambda>n. acoef n * u ^ n) has_sum f (x0 + u *\<^sub>R d)) (UNIV::nat set)"
    proof (rule has_sum_Sigma'[where f = "\<lambda>q. u ^ (fst q) * (ra_monomial d (snd q) * c (snd q))"
                                 and B = blk])
      show "((\<lambda>q. u ^ (fst q) * (ra_monomial d (snd q) * c (snd q))) has_sum f (x0 + u *\<^sub>R d))
              (Sigma (UNIV::nat set) blk)" by (rule reidx)
    next
      fix n :: nat assume "n \<in> (UNIV::nat set)"
      show "((\<lambda>\<alpha>. u ^ (fst (n, \<alpha>)) * (ra_monomial d (snd (n, \<alpha>)) * c (snd (n, \<alpha>)))) has_sum (acoef n * u ^ n)) (blk n)"
        using inner[of n] by simp
    qed
    have "(\<lambda>n. acoef n * u ^ n) sums f (x0 + u *\<^sub>R d)"
      by (rule has_sum_imp_sums[OF basesum])
    thus ?thesis by (simp only: pt_eq u_def)
  qed
  show ?thesis
    by (rule real_powser_imp_real_analytic_at_1d[OF r'_pos PS])
qed

subsection \<open>Propagating a zero of an analytic function along a segment\<close>

text \<open>If \<open>f\<close> is real-analytic on the open set \<open>U\<close>, the closed segment from \<open>z\<close> to \<open>y\<close>
  lies in \<open>U\<close>, and \<open>f\<close> vanishes on a neighbourhood of \<open>z\<close>, then \<open>f y = 0\<close>.  This is the
  multivariate identity theorem reduced to the one-dimensional analytic slice along the
  segment.\<close>

lemma slice_zero_propagate:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes ana: "real_analytic_on f U"
    and seg: "closed_segment z y \<subseteq> U"
    and zero_near: "\<exists>\<delta>0>0. \<forall>w. dist w z < \<delta>0 \<longrightarrow> f w = 0"
  shows "f y = 0"
proof (cases "y = z")
  case True
  from zero_near obtain \<delta>0 where d0: "\<delta>0 > 0" and fz: "\<And>w. dist w z < \<delta>0 \<Longrightarrow> f w = 0"
    by blast
  show ?thesis using True fz[of z] d0 by simp
next
  case False
  define d where "d = y - z"
  have dnz: "d \<noteq> 0" using False by (simp add: d_def)
  have oU: "open U" using ana by (simp only: real_analytic_on_def)
  define g where "g = (\<lambda>s::real. f (z + s *\<^sub>R d))"
  \<comment> \<open>parameter set where the line stays in \<open>U\<close>\<close>
  define I where "I = {s::real. z + s *\<^sub>R d \<in> U}"
  have segI: "{0..1} \<subseteq> I"
  proof
    fix s :: real assume s: "s \<in> {0..1}"
    have "z + s *\<^sub>R d = (1 - s) *\<^sub>R z + s *\<^sub>R y"
      by (simp add: d_def algebra_simps)
    moreover have "(1 - s) *\<^sub>R z + s *\<^sub>R y \<in> closed_segment z y"
      using s by (auto simp: in_segment)
    ultimately have "z + s *\<^sub>R d \<in> U" using seg by auto
    thus "s \<in> I" by (simp add: I_def)
  qed
  have Iopen: "open I"
  proof -
    have cont: "continuous (at s) (\<lambda>s::real. z + s *\<^sub>R d)" for s
      by (intro continuous_intros)
    have "open ((\<lambda>s::real. z + s *\<^sub>R d) -` U)"
      by (rule continuous_open_vimage[OF oU cont])
    moreover have "I = (\<lambda>s::real. z + s *\<^sub>R d) -` U"
      by (auto simp: I_def)
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>fatten the compact segment \<open>[0,1]\<close> inside the open set \<open>I\<close>\<close>
  obtain \<delta> where dpos: "\<delta> > 0" and fat: "(\<Union>x\<in>{0..1::real}. ball x \<delta>) \<subseteq> I"
    using compact_subset_open_imp_ball_epsilon_subset[OF compact_Icc Iopen segI]
    by blast
  define J where "J = {s::real. -\<delta> < s \<and> s < 1 + \<delta>}"
  have Jopen: "open J"
    unfolding J_def by (simp add: open_Collect_conj open_Collect_less)
  have Jconn: "connected J"
  proof -
    have "J = {-\<delta><..<1+\<delta>}" by (auto simp: J_def)
    thus ?thesis by (simp only: connected_Ioo)
  qed
  have JsubI: "J \<subseteq> I"
  proof
    fix s :: real assume "s \<in> J"
    then have sb: "-\<delta> < s" "s < 1 + \<delta>" by (auto simp: J_def)
    define x where "x = max 0 (min 1 s)"
    have xseg: "x \<in> {0..1}" by (simp add: x_def)
    have "dist s x < \<delta>"
    proof (cases "s < 0")
      case True thus ?thesis using sb x_def by (simp only: dist_real_def)
    next
      case False
      show ?thesis
      proof (cases "s > 1")
        case True thus ?thesis using sb x_def by (simp only: dist_real_def)
      next
        case False
        with \<open>\<not> s < 0\<close> have "x = s" by (simp only: x_def)
        thus ?thesis using dpos by (simp only: dist_real_def)
      qed
    qed
    then have "s \<in> ball x \<delta>" by (simp add: dist_commute)
    then have "s \<in> (\<Union>x\<in>{0..1::real}. ball x \<delta>)" using xseg by blast
    with fat show "s \<in> I" by blast
  qed
  have onein: "(1::real) \<in> J" using dpos by (simp add: J_def)
  \<comment> \<open>the slice \<open>g\<close> is real-analytic on \<open>J\<close>\<close>
  have gana: "real_analytic_on g J"
  proof -
    have "real_analytic_at_1d g c" if "c \<in> J" for c
    proof -
      have "z + c *\<^sub>R d \<in> U" using that JsubI by (auto simp: I_def)
      thus ?thesis
        unfolding g_def
        by (rule real_analytic_slice_at_point[OF ana _ dnz])
    qed
    thus ?thesis using Jopen by (simp add: real_analytic_on_1d_iff)
  qed
  \<comment> \<open>\<open>g\<close> vanishes on an open subinterval of \<open>J\<close> around \<open>0\<close>\<close>
  from zero_near obtain \<delta>0 where d0: "\<delta>0 > 0" and fz: "\<And>w. dist w z < \<delta>0 \<Longrightarrow> f w = 0"
    by blast
  define \<eta> where "\<eta> = min \<delta> (\<delta>0 / norm d)"
  have eta_pos: "\<eta> > 0" using dpos d0 dnz by (simp add: \<eta>_def)
  have gzero: "g s = 0" if "\<bar>s\<bar> < \<eta>" for s
  proof -
    have ndpos: "norm d > 0" using dnz by simp
    have le1: "\<eta> * norm d \<le> (\<delta>0 / norm d) * norm d"
      using ndpos by (intro mult_right_mono) (auto simp: \<eta>_def)
    have "dist (z + s *\<^sub>R d) z = \<bar>s\<bar> * norm d" by (simp add: dist_norm)
    also have "\<dots> < \<eta> * norm d" using that ndpos by (simp only: mult_strict_right_mono)
    also have "\<dots> \<le> (\<delta>0 / norm d) * norm d" by (rule le1)
    also have "\<dots> = \<delta>0" using ndpos by simp
    finally show ?thesis using fz[of "z + s *\<^sub>R d"] by (simp only: g_def)
  qed
  \<comment> \<open>the zero set of \<open>g\<close> on \<open>J\<close> is not nowhere dense\<close>
  have zeroset_int: "interior (closure {s \<in> J. g s = 0}) \<noteq> {}"
  proof -
    have sub: "{s::real. -\<eta> < s \<and> s < \<eta>} \<subseteq> {s \<in> J. g s = 0}"
    proof
      fix s :: real assume "s \<in> {s. -\<eta> < s \<and> s < \<eta>}"
      then have sb: "-\<eta> < s" "s < \<eta>" by auto
      have "\<bar>s\<bar> < \<eta>" using sb by simp
      have eta_le: "\<eta> \<le> \<delta>" by (simp only: \<eta>_def)
      have "s \<in> J" unfolding J_def using sb eta_le dpos by simp
      then show "s \<in> {s \<in> J. g s = 0}" using gzero \<open>\<bar>s\<bar> < \<eta>\<close> by auto
    qed
    have "open {s::real. -\<eta> < s \<and> s < \<eta>}"
      by (simp add: open_Collect_conj open_Collect_less)
    moreover have "(0::real) \<in> {s::real. -\<eta> < s \<and> s < \<eta>}" using eta_pos by simp
    ultimately have "(0::real) \<in> interior {s \<in> J. g s = 0}"
      using sub interior_maximal by (simp only: interiorI) 
    moreover have "interior {s \<in> J. g s = 0} \<subseteq> interior (closure {s \<in> J. g s = 0})"
      by (intro interior_mono closure_subset)
    ultimately show ?thesis by blast
  qed
  \<comment> \<open>hence by the 1-D nowhere-dense workhorse \<open>g\<close> is identically zero on \<open>J\<close>\<close>
  have "\<not> (\<exists>x\<in>J. g x \<noteq> 0)"
  proof
    assume "\<exists>x\<in>J. g x \<noteq> 0"
    from real_analytic_1d_nowhere_dense_zeros[OF gana Jconn this]
    have "interior (closure {s \<in> J. g s = 0}) = {}" .
    with zeroset_int show False by simp
  qed
  then have "g 1 = 0" using onein by blast
  thus ?thesis by (simp add: g_def d_def)
qed

subsection \<open>The multivariate nowhere-dense-zeros workhorse\<close>

theorem real_analytic_nowhere_dense_zeros:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes ana: "real_analytic_on f U" and conn: "connected U"
    and ex: "\<exists>x\<in>U. f x \<noteq> 0"
  shows "interior (closure {x \<in> U. f x = 0}) = {}"
proof -
  have oU: "open U" using ana by (simp only: real_analytic_on_def)

  text \<open>Continuity of \<open>f\<close> on \<open>U\<close> (proved directly from the local power series).\<close>
  have contf: "continuous (at x) f" if "x \<in> U" for x
    by (rule real_analytic_on_imp_continuous[OF ana that])

  text \<open>The set of points around which \<open>f\<close> vanishes on a ball inside \<open>U\<close>.\<close>
  define Z where "Z = {x \<in> U. \<exists>\<epsilon>>0. ball x \<epsilon> \<subseteq> U \<and> (\<forall>y\<in>ball x \<epsilon>. f y = 0)}"
  have Zsub: "Z \<subseteq> U" by (auto simp: Z_def)

  text \<open>\<open>Z\<close> is open.\<close>
  have Zopen: "open Z"
  proof (rule openI)
    fix x assume "x \<in> Z"
    then obtain \<epsilon> where xU: "x \<in> U" and epos: "\<epsilon> > 0"
      and ballU: "ball x \<epsilon> \<subseteq> U" and fz: "\<forall>y\<in>ball x \<epsilon>. f y = 0"
      by (auto simp: Z_def)
    have "ball x \<epsilon> \<subseteq> Z"
    proof
      fix w assume w: "w \<in> ball x \<epsilon>"
      then obtain \<rho> where rpos: "\<rho> > 0" and rsub: "ball w \<rho> \<subseteq> ball x \<epsilon>"
        using open_contains_ball by (metis open_ball)
      have "w \<in> U" using w ballU by blast
      moreover have "ball w \<rho> \<subseteq> U" using rsub ballU by blast
      moreover have "\<forall>y\<in>ball w \<rho>. f y = 0" using rsub fz by blast
      ultimately show "w \<in> Z" using rpos by (auto simp: Z_def)
    qed
    thus "\<exists>e>0. ball x e \<subseteq> Z" using epos by blast
  qed
  have ZopenIn: "openin (top_of_set U) Z"
    using Zopen Zsub by (metis Int_absorb1 openin_open_Int)

  text \<open>\<open>Z\<close> is closed in \<open>U\<close>: this is the multivariate identity theorem via analytic slices.\<close>
  have Zlimit: "x \<in> Z" if xU: "x \<in> U" and xcl: "x \<in> closure Z" for x
  proof -
    obtain \<rho> where rpos: "\<rho> > 0" and ballU: "ball x \<rho> \<subseteq> U"
      using oU xU open_contains_ball by blast
    \<comment> \<open>a point of \<open>Z\<close> within \<open>\<rho>/2\<close> of \<open>x\<close>\<close>
    have "\<rho>/2 > 0" using rpos by simp
    with xcl have "\<exists>z\<in>Z. dist z x < \<rho>/2"
      using closure_approachable[of x Z] by blast
    then obtain z where zZ: "z \<in> Z" and zx: "dist z x < \<rho>/2" by blast
    from zZ obtain \<delta>0 where d0: "\<delta>0 > 0" and fz0: "\<forall>y\<in>ball z \<delta>0. f y = 0"
      by (auto simp: Z_def)
    have zb: "z \<in> ball x (\<rho>/2)" using zx by (simp add: dist_commute)
    \<comment> \<open>\<open>f\<close> vanishes throughout \<open>ball x (\<rho>/2)\<close>\<close>
    have fvan: "f y = 0" if yb: "y \<in> ball x (\<rho>/2)" for y
    proof -
      have convB: "convex (ball x (\<rho>/2))" by (rule convex_ball)
      have "closed_segment z y \<subseteq> ball x (\<rho>/2)"
        by (rule closed_segment_subset[OF zb yb convB])
      also have "ball x (\<rho>/2) \<subseteq> ball x \<rho>" using rpos by (intro subset_ball) simp
      finally have segU: "closed_segment z y \<subseteq> U" using ballU by blast
      have znear: "\<exists>\<delta>0>0. \<forall>w. dist w z < \<delta>0 \<longrightarrow> f w = 0"
        using d0 fz0 by (auto simp: dist_commute)
      show ?thesis by (rule slice_zero_propagate[OF ana segU znear])
    qed
    have "ball x (\<rho>/2) \<subseteq> ball x \<rho>" using rpos by (intro subset_ball) simp
    then have ballhalf: "ball x (\<rho>/2) \<subseteq> U" using ballU by blast
    have rh: "\<rho>/2 > 0" using rpos by simp
    have "\<exists>\<epsilon>>0. ball x \<epsilon> \<subseteq> U \<and> (\<forall>y\<in>ball x \<epsilon>. f y = 0)"
      using rh ballhalf fvan by blast
    thus "x \<in> Z" using xU by (simp add: Z_def)
  qed
  have Zeq: "Z = U \<inter> closure Z" using Zsub Zlimit closure_subset by blast
  have ZclosedIn: "closedin (top_of_set U) Z"
    by (subst Zeq) (simp add: closedin_closed_Int)

  text \<open>If \<open>W = interior (closure ...)\<close> is nonempty then \<open>Z\<close> is nonempty.\<close>
  define W where "W = interior (closure {x \<in> U. f x = 0})"
  have Wopen: "open W" by (simp add: W_def)
  have Zne: "Z \<noteq> {}" if WNE: "W \<noteq> {}"
  proof -
    from WNE obtain w where wW: "w \<in> W" by blast
    have Wsub: "W \<subseteq> closure {x \<in> U. f x = 0}" by (simp only: W_def interior_subset)
    obtain e where epos: "e > 0" and eball: "ball w e \<subseteq> W"
      using wW Wopen open_contains_ball by blast
    have wcl: "w \<in> closure {x \<in> U. f x = 0}" using wW Wsub by blast
    \<comment> \<open>the open ball \<open>ball w e\<close> meets the zero set, since it meets its closure\<close>
    have "ball w e \<inter> {x \<in> U. f x = 0} \<noteq> {}"
    proof -
      have "w \<in> ball w e \<inter> closure {x \<in> U. f x = 0}" using wcl epos by simp
      hence "ball w e \<inter> closure {x \<in> U. f x = 0} \<noteq> {}" by blast
      thus "ball w e \<inter> {x \<in> U. f x = 0} \<noteq> {}"
        using open_Int_closure_eq_empty[OF open_ball, of w e "{x \<in> U. f x = 0}"] by blast
    qed
    then obtain u where uU: "u \<in> ball w e" "u \<in> U" "f u = 0" by blast
    have uW: "u \<in> W" using uU(1) eball by blast
    define V where "V = W \<inter> U"
    have Vopen: "open V" unfolding V_def by (intro open_Int Wopen oU)
    have uV: "u \<in> V" using uW uU(2) by (simp add: V_def)
    \<comment> \<open>on the open set \<open>V\<close>, \<open>f \<equiv> 0\<close> by continuity through the closure\<close>
    have fzeroV: "f v = 0" if "v \<in> V" for v
    proof -
      have vW: "v \<in> W" and vU: "v \<in> U" using that by (auto simp: V_def)
      have vcl: "v \<in> closure {x \<in> U. f x = 0}" using vW Wsub by blast
      have "isCont f v" using contf[OF vU] by simp
      from vcl obtain s where s: "\<And>k. s k \<in> {x \<in> U. f x = 0}" "s \<longlonglongrightarrow> v"
        using closure_sequential by blast
      have "(\<lambda>k. f (s k)) \<longlonglongrightarrow> f v"
        using \<open>isCont f v\<close> s(2) by (simp only: continuous_within isCont_tendsto_compose)
      moreover have "(\<lambda>k. f (s k)) = (\<lambda>k. 0)" using s(1) by auto
      ultimately have "(\<lambda>k. (0::real)) \<longlonglongrightarrow> f v" by simp
      thus "f v = 0" by (simp only: LIMSEQ_const_iff)
    qed
    \<comment> \<open>a ball around \<open>u\<close> inside \<open>V \<subseteq> U\<close> on which \<open>f \<equiv> 0\<close>: so \<open>u \<in> Z\<close>\<close>
    obtain \<rho> where \<rho>: "\<rho> > 0" and rball: "ball u \<rho> \<subseteq> V"
      using uV Vopen open_contains_ball by blast
    have rballU: "ball u \<rho> \<subseteq> U" using rball by (auto simp: V_def)
    have "\<forall>y\<in>ball u \<rho>. f y = 0" using rball fzeroV by blast
    then have "u \<in> Z" using \<rho> rballU uU(2) by (auto simp: Z_def)
    thus "Z \<noteq> {}" by blast
  qed

  text \<open>Connectedness: \<open>Z\<close> is clopen in \<open>U\<close>, so \<open>Z = \<emptyset>\<close> or \<open>Z = U\<close>.\<close>
  have clopen: "Z = {} \<or> Z = U"
    using conn ZopenIn ZclosedIn unfolding connected_clopen by blast

  show ?thesis
  proof (rule ccontr)
    assume "interior (closure {x \<in> U. f x = 0}) \<noteq> {}"
    then have WNE: "W \<noteq> {}" by (simp add: W_def)
    then have "Z \<noteq> {}" by (rule Zne)
    with clopen have "Z = U" by blast
    have "f x = 0" if "x \<in> U" for x
    proof -
      have "x \<in> Z" using that \<open>Z = U\<close> by simp
      then obtain \<epsilon> where epos: "\<epsilon> > 0" and fz: "\<forall>y\<in>ball x \<epsilon>. f y = 0"
        by (auto simp: Z_def)
      have "x \<in> ball x \<epsilon>" using epos by simp
      thus "f x = 0" using fz by blast
    qed
    with ex show False by blast
  qed
qed



text \<open>Scalar component (inner product with a fixed vector) of an analytic vector
  function is analytic.\<close>

lemma real_analytic_on_inner_component:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. f x \<bullet> b) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open U" by (rule U)
  next
    fix x0 assume x0: "x0 \<in> U"
    from F x0 obtain r c where r: "0 < r"
      and F1: "\<And>x. dist x x0 < r \<Longrightarrow>
                ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x) ra_idx"
      unfolding real_analytic_on_def by blast
    show "\<exists>r>0. \<exists>cc. \<forall>x. dist x x0 < r \<longrightarrow>
            ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cc \<alpha>) has_sum (f x \<bullet> b)) ra_idx"
    proof (intro exI[where x=r] conjI exI[where x="\<lambda>\<alpha>. c \<alpha> \<bullet> b"] allI impI)
      show "0 < r" by (rule r)
    next
      fix x assume d: "dist x x0 < r"
      have bl: "bounded_linear (\<lambda>y::'b. y \<bullet> b)"
        by (rule bounded_linear_inner_left)
      have "((\<lambda>\<alpha>. (ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) \<bullet> b) has_sum (f x \<bullet> b)) ra_idx"
        by (rule has_sum_bounded_linear[OF bl F1[OF d]])
      thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (c \<alpha> \<bullet> b)) has_sum (f x \<bullet> b)) ra_idx"
        by (simp only: inner_scaleR_left scaleR_conv_of_real) simp
    qed
  qed
qed

subsection \<open>Explicit multi-index operations (import-free, mirroring real_analytic_on_mult)\<close>

definition addI :: "('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat)" where
  "addI = (\<lambda>\<alpha> \<beta> b. \<alpha> b + \<beta> b)"
definition subI :: "('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat)" where
  "subI = (\<lambda>\<gamma> \<alpha> b. \<gamma> b - \<alpha> b)"
definition leI :: "('a\<Rightarrow>nat) \<Rightarrow> ('a\<Rightarrow>nat) \<Rightarrow> bool" where
  "leI = (\<lambda>\<alpha> \<gamma>. \<forall>b. \<alpha> b \<le> \<gamma> b)"
definition lowI :: "('a\<Rightarrow>nat) \<Rightarrow> ('a::euclidean_space\<Rightarrow>nat) set" where
  "lowI \<gamma> = {\<alpha>. \<alpha> \<in> ra_idx \<and> leI \<alpha> \<gamma>}"

lemma idx_add: "addI \<alpha> \<beta> \<in> ra_idx" if "\<alpha> \<in> ra_idx" "\<beta> \<in> ra_idx"
  for \<alpha> \<beta> :: "'a::euclidean_space\<Rightarrow>nat"
proof -
  have "{b. addI \<alpha> \<beta> b \<noteq> 0} \<subseteq> {b. \<alpha> b \<noteq> 0} \<union> {b. \<beta> b \<noteq> 0}"
    by (auto simp: addI_def)
  also have "\<dots> \<subseteq> Basis" using that by (auto simp: ra_idx_def)
  finally show ?thesis by (simp add: ra_idx_def)
qed

lemma idx_sub: "subI \<gamma> \<alpha> \<in> ra_idx" if "\<gamma> \<in> ra_idx"
  for \<gamma> \<alpha> :: "'a::euclidean_space\<Rightarrow>nat"
proof -
  have "{b. subI \<gamma> \<alpha> b \<noteq> 0} \<subseteq> {b. \<gamma> b \<noteq> 0}" by (auto simp: subI_def)
  also have "\<dots> \<subseteq> Basis" using that by (auto simp: ra_idx_def)
  finally show ?thesis by (simp add: ra_idx_def)
qed

lemma mono_add: "ra_monomial h (addI \<alpha> \<beta>) = ra_monomial h \<alpha> * ra_monomial h \<beta>"
  for h :: "'a::euclidean_space" and \<alpha> \<beta>
  by (simp only: ra_monomial_def addI_def power_add prod.distrib)

lemma idx_lower_fin: "finite (lowI \<gamma>)" for \<gamma> :: "'a::euclidean_space \<Rightarrow> nat"
proof -
  define N where "N = Max (insert 0 (\<gamma> ` (Basis :: 'a set)))"
  have "lowI \<gamma>
          \<subseteq> {hh. \<forall>x::'a. (x \<in> Basis \<longrightarrow> hh x \<in> {0..N}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
  proof (rule subsetI)
    fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> lowI \<gamma>"
    then have a1: "\<alpha> \<in> ra_idx" and a2: "leI \<alpha> \<gamma>" by (auto simp: lowI_def)
    have "\<forall>x::'a. (x \<in> Basis \<longrightarrow> \<alpha> x \<in> {0..N}) \<and> (x \<notin> Basis \<longrightarrow> \<alpha> x = 0)"
    proof (intro allI conjI impI)
      fix x :: 'a assume "x \<in> Basis"
      have "\<alpha> x \<le> \<gamma> x" using a2 by (simp only: leI_def)
      also have "\<gamma> x \<le> N" unfolding N_def using \<open>x \<in> Basis\<close> by (intro Max_ge) auto
      finally show "\<alpha> x \<in> {0..N}" by simp
    next
      fix x :: 'a assume "x \<notin> Basis"
      with a1 show "\<alpha> x = 0" by (auto simp: ra_idx_def)
    qed
    thus "\<alpha> \<in> {hh. \<forall>x::'a. (x \<in> Basis \<longrightarrow> hh x \<in> {0..N}) \<and> (x \<notin> Basis \<longrightarrow> hh x = 0)}"
      by simp
  qed
  moreover have "finite {hh::'a\<Rightarrow>nat. \<forall>x. (x \<in> Basis \<longrightarrow> hh x \<in> {0..N}) \<and> (x \<notin> Basis \<longrightarrow> hh x = (0::nat))}"
    by (rule finite_set_of_finite_funs) auto
  ultimately show ?thesis by (rule finite_subset)
qed

text \<open>The Fubini/Cauchy product of two real unordered sums over a common index set.\<close>

lemma prod_has_sum:
  "((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) has_sum (Uv * Vv)) (I \<times> I)"
  if uHS: "(u has_sum Uv) I" and vHS: "(v has_sum Vv) I"
  for u v :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real" and Uv Vv I
proof -
  have u_abs: "(\<lambda>z. norm (u z)) summable_on I"
    using uHS has_sum_imp_summable summable_on_iff_abs_summable_on_real by blast
  have v_abs: "(\<lambda>z. norm (v z)) summable_on I"
    using vHS has_sum_imp_summable summable_on_iff_abs_summable_on_real by blast
  have inner: "((\<lambda>\<beta>. u \<alpha> * v \<beta>) has_sum (u \<alpha> * Vv)) I" for \<alpha>
    by (rule has_sum_cmult_right[OF vHS])
  have outer: "((\<lambda>\<alpha>. u \<alpha> * Vv) has_sum (Uv * Vv)) I"
    by (rule has_sum_cmult_left[OF uHS])
  have inner_abs: "(\<lambda>\<beta>. norm (u \<alpha> * v \<beta>)) summable_on I" for \<alpha>
  proof -
    have "(\<lambda>\<beta>. norm (u \<alpha>) * norm (v \<beta>)) summable_on I"
      using v_abs by (rule summable_on_cmult_right)
    thus ?thesis by (simp only: norm_mult flip: abs_mult)
  qed
  have tail_abs: "(\<lambda>\<alpha>. norm (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>))) summable_on I"
  proof -
    have eq: "norm (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>)) = norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))" for \<alpha>
    proof -
      have nn: "(\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>)) = norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))"
      proof -
        have "(\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>)) = (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha>) * norm (v \<beta>))"
          by (simp add: abs_mult)
        also have "\<dots> = norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))"
          by (rule infsum_cmult_right) (rule v_abs)
        finally show ?thesis .
      qed
      have ge: "(0::real) \<le> norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))"
        by (intro mult_nonneg_nonneg) (auto intro: infsum_nonneg)
      from nn ge show ?thesis by simp
    qed
    have "(\<lambda>\<alpha>. norm (u \<alpha>) * (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (v \<beta>))) summable_on I"
      using u_abs by (rule summable_on_cmult_left)
    thus ?thesis unfolding eq .
  qed
  have conj1: "\<forall>\<alpha>\<in>I. (\<lambda>\<beta>. norm ((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) (\<alpha>, \<beta>))) summable_on I"
  proof
    fix \<alpha> assume "\<alpha> \<in> I"
    have "(\<lambda>\<beta>. norm (u \<alpha> * v \<beta>)) summable_on I" by (rule inner_abs)
    thus "(\<lambda>\<beta>. norm ((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) (\<alpha>, \<beta>))) summable_on I" by simp
  qed
  have conj2: "(\<lambda>\<alpha>. norm (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm ((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) (\<alpha>, \<beta>)))) summable_on I"
  proof -
    have "(\<lambda>\<alpha>. norm (\<Sum>\<^sub>\<infinity>\<beta>\<in>I. norm (u \<alpha> * v \<beta>))) summable_on I" by (rule tail_abs)
    thus ?thesis by simp
  qed
  have absS: "(\<lambda>z. norm ((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) z)) summable_on (Sigma I (\<lambda>_. I))"
    by (rule Infinite_Sum.abs_summable_on_Sigma_iff
          [where f = "\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>" and A = I and B = "\<lambda>_. I", THEN iffD2,
           OF conjI[OF conj1 conj2]])
  have summ: "(\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) summable_on Sigma I (\<lambda>_. I)"
    by (rule abs_summable_summable[OF absS])
  have "((\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) has_sum (Uv * Vv)) (Sigma I (\<lambda>_. I))"
  proof (rule has_sum_SigmaI[where g = "\<lambda>\<alpha>. u \<alpha> * Vv"])
    fix \<alpha> assume "\<alpha> \<in> I"
    have "((\<lambda>\<beta>. u \<alpha> * v \<beta>) has_sum (u \<alpha> * Vv)) I" by (rule inner)
    thus "((\<lambda>\<beta>. (\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) (\<alpha>, \<beta>)) has_sum (u \<alpha> * Vv)) I" by simp
  next
    show "((\<lambda>\<alpha>. u \<alpha> * Vv) has_sum (Uv * Vv)) I" by (rule outer)
  next
    show "(\<lambda>(\<alpha>,\<beta>). u \<alpha> * v \<beta>) summable_on Sigma I (\<lambda>_. I)" by (rule summ)
  qed
  thus ?thesis by (simp only: Sigma_def)
qed

text \<open>The explicit Cauchy-product coefficient operator.\<close>

definition ccauchy :: "(('a::euclidean_space\<Rightarrow>nat) \<Rightarrow> real) \<Rightarrow> (('a\<Rightarrow>nat) \<Rightarrow> real) \<Rightarrow> (('a\<Rightarrow>nat) \<Rightarrow> real)" where
  "ccauchy c1 c2 = (\<lambda>\<gamma>. \<Sum>\<alpha>\<in>lowI \<gamma>. c1 \<alpha> * c2 (subI \<gamma> \<alpha>))"

text \<open>Quantitative Cauchy product on a common ball, exposing the (x-independent)
  coefficient family.\<close>

lemma quant_mult:
  fixes c1 c2 :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes F1: "((\<lambda>\<alpha>. ra_monomial h \<alpha> * c1 \<alpha>) has_sum Fv) ra_idx"
    and G1: "((\<lambda>\<beta>. ra_monomial h \<beta> * c2 \<beta>) has_sum Gv) ra_idx"
  shows "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ccauchy c1 c2 \<gamma>) has_sum (Fv * Gv)) ra_idx"
proof -
  have step1:
    "((\<lambda>(\<alpha>,\<beta>). (ra_monomial h \<alpha> * c1 \<alpha>) * (ra_monomial h \<beta> * c2 \<beta>))
         has_sum (Fv * Gv)) (ra_idx \<times> ra_idx)"
    using prod_has_sum[OF F1 G1] .
  have step2:
    "((\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum (Fv * Gv))
        (Sigma ra_idx lowI)"
  proof -
    have "((\<lambda>(\<alpha>,\<beta>). (ra_monomial h \<alpha> * c1 \<alpha>) * (ra_monomial h \<beta> * c2 \<beta>))
             has_sum (Fv * Gv)) (ra_idx \<times> ra_idx)
          = ((\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum (Fv * Gv))
             (Sigma ra_idx lowI)"
    proof (rule has_sum_reindex_bij_witness
             [where j = "\<lambda>(\<alpha>,\<beta>). (addI \<alpha> \<beta>, \<alpha>)" and i = "\<lambda>(\<gamma>,\<alpha>). (\<alpha>, subI \<gamma> \<alpha>)"])
      fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume "p \<in> ra_idx \<times> ra_idx"
      obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
      show "(case (case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) = p"
        by (simp add: p subI_def addI_def)
    next
      fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume P: "p \<in> ra_idx \<times> ra_idx"
      obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
      have a\<alpha>: "\<alpha> \<in> ra_idx" and a\<beta>: "\<beta> \<in> ra_idx" using P p by auto
      have m1: "addI \<alpha> \<beta> \<in> ra_idx" by (rule idx_add[OF a\<alpha> a\<beta>])
      have m2: "\<alpha> \<in> lowI (addI \<alpha> \<beta>)"
        using a\<alpha> by (simp add: lowI_def leI_def addI_def)
      show "(case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) \<in> Sigma ra_idx lowI"
        using m1 m2 by (simp add: p)
    next
      fix q :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume Q: "q \<in> Sigma ra_idx lowI"
      obtain \<gamma> \<alpha> where q: "q = (\<gamma>,\<alpha>)" by (cases q)
      have g\<gamma>: "\<gamma> \<in> ra_idx" and l: "leI \<alpha> \<gamma>" using Q q by (auto simp: lowI_def)
      have "addI \<alpha> (subI \<gamma> \<alpha>) = \<gamma>"
      proof (rule ext)
        fix b have "\<alpha> b \<le> \<gamma> b" using l by (simp only: leI_def)
        thus "addI \<alpha> (subI \<gamma> \<alpha>) b = \<gamma> b" by (simp only: addI_def subI_def)
      qed
      then show "(case (case q of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) = q"
        by (simp add: q)
    next
      fix q :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume Q: "q \<in> Sigma ra_idx lowI"
      obtain \<gamma> \<alpha> where q: "q = (\<gamma>,\<alpha>)" by (cases q)
      have g\<gamma>: "\<gamma> \<in> ra_idx" and a\<alpha>: "\<alpha> \<in> ra_idx" using Q q by (auto simp: lowI_def)
      show "(case q of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) \<in> ra_idx \<times> ra_idx"
        by (simp add: q a\<alpha> idx_sub[OF g\<gamma>])
    next
      fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume P: "p \<in> ra_idx \<times> ra_idx"
      obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
      have sub_eq: "subI (addI \<alpha> \<beta>) \<alpha> = \<beta>" by (simp add: addI_def subI_def)
      have mm: "ra_monomial h \<alpha> * ra_monomial h \<beta> = ra_monomial h (addI \<alpha> \<beta>)"
        by (simp only: mono_add)
      have "ra_monomial h (addI \<alpha> \<beta>) * (c1 \<alpha> * c2 (subI (addI \<alpha> \<beta>) \<alpha>))
              = ra_monomial h (addI \<alpha> \<beta>) * (c1 \<alpha> * c2 \<beta>)" by (simp only: sub_eq)
      also have "\<dots> = (ra_monomial h \<alpha> * ra_monomial h \<beta>) * (c1 \<alpha> * c2 \<beta>)"
        by (simp only: mm)
      also have "\<dots> = (ra_monomial h \<alpha> * c1 \<alpha>) * (ra_monomial h \<beta> * c2 \<beta>)"
        by (simp only: mult.assoc mult.left_commute)
      finally show "(case (case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) of (\<gamma>,\<alpha>) \<Rightarrow>
                        ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>)))
                   = (case p of (\<alpha>,\<beta>) \<Rightarrow> (ra_monomial h \<alpha> * c1 \<alpha>) * (ra_monomial h \<beta> * c2 \<beta>))"
        by (simp add: p)
    qed simp
    with step1 show ?thesis by simp
  qed
  have inner_fin:
    "((\<lambda>\<alpha>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum
        (ra_monomial h \<gamma> *\<^sub>R ccauchy c1 c2 \<gamma>)) (lowI \<gamma>)" if "\<gamma> \<in> ra_idx" for \<gamma>
  proof -
    have fin: "finite (lowI \<gamma>)" by (rule idx_lower_fin)
    have "((\<lambda>\<alpha>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum
             (\<Sum>\<alpha>\<in>lowI \<gamma>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>)))) (lowI \<gamma>)"
      by (rule has_sum_finite[OF fin])
    also have "(\<Sum>\<alpha>\<in>lowI \<gamma>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>)))
                 = ra_monomial h \<gamma> * (\<Sum>\<alpha>\<in>lowI \<gamma>. c1 \<alpha> * c2 (subI \<gamma> \<alpha>))"
      by (simp only: sum_distrib_left)
    also have "(\<Sum>\<alpha>\<in>lowI \<gamma>. c1 \<alpha> * c2 (subI \<gamma> \<alpha>)) = ccauchy c1 c2 \<gamma>"
      by (simp only: ccauchy_def)
    finally show ?thesis by simp
  qed
  have "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ccauchy c1 c2 \<gamma>) has_sum (Fv * Gv)) ra_idx"
  proof (rule has_sum_Sigma'
           [where f = "\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))"
              and A = ra_idx and B = lowI and a = "Fv * Gv"
              and b = "\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ccauchy c1 c2 \<gamma>"])
    show "((\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum (Fv * Gv))
            (Sigma ra_idx lowI)" by (rule step2)
  next
    fix \<gamma> :: "'a \<Rightarrow> nat" assume "\<gamma> \<in> ra_idx"
    then have "((\<lambda>\<alpha>. ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) has_sum
                  (ra_monomial h \<gamma> *\<^sub>R ccauchy c1 c2 \<gamma>)) (lowI \<gamma>)" by (rule inner_fin)
    thus "((\<lambda>\<alpha>. (\<lambda>(\<gamma>,\<alpha>). ra_monomial h \<gamma> * (c1 \<alpha> * c2 (subI \<gamma> \<alpha>))) (\<gamma>, \<alpha>)) has_sum
              (ra_monomial h \<gamma> *\<^sub>R ccauchy c1 c2 \<gamma>)) (lowI \<gamma>)" by simp
  qed
  thus ?thesis .
qed

subsection \<open>Quantitative series-on-a-ball representation\<close>

definition series_on ::
  "'a::euclidean_space \<Rightarrow> real \<Rightarrow> (('a\<Rightarrow>nat)\<Rightarrow>real) \<Rightarrow> ('a\<Rightarrow>real) \<Rightarrow> bool" where
  "series_on x0 r c F \<longleftrightarrow>
     (\<forall>x. dist x x0 < r \<longrightarrow> ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum F x) ra_idx)"

lemma series_on_mono_radius:
  assumes "series_on x0 r c F" and "r' \<le> r"
  shows "series_on x0 r' c F"
  using assms unfolding series_on_def by fastforce

definition czero_idx :: "'a::euclidean_space \<Rightarrow> nat" where
  "czero_idx = (\<lambda>_. 0)"

definition cone :: "('a::euclidean_space\<Rightarrow>nat) \<Rightarrow> real" where
  "cone = (\<lambda>\<alpha>. if \<alpha> = czero_idx then 1 else 0)"

lemma czero_idx_in: "czero_idx \<in> ra_idx"
  by (simp add: ra_idx_def czero_idx_def)

lemma series_on_one: "series_on x0 r cone (\<lambda>_. 1)"
  unfolding series_on_def
proof (intro allI impI)
  fix x :: 'a assume "dist x x0 < r"
  define h where "h = x - x0"
  have sing: "((\<lambda>\<alpha>. ra_monomial h \<alpha> *\<^sub>R cone \<alpha>) has_sum
                 (\<Sum>\<alpha>\<in>{czero_idx}. ra_monomial h \<alpha> *\<^sub>R cone \<alpha>)) {czero_idx}"
    by (rule has_sum_finite) auto
  have val: "(\<Sum>\<alpha>\<in>{czero_idx}. ra_monomial h \<alpha> *\<^sub>R cone \<alpha>) = (1::real)"
    by (simp add: cone_def ra_monomial_def czero_idx_def)
  have "((\<lambda>\<alpha>. ra_monomial h \<alpha> *\<^sub>R cone \<alpha>) has_sum (1::real)) ra_idx
          = ((\<lambda>\<alpha>. ra_monomial h \<alpha> *\<^sub>R cone \<alpha>) has_sum (1::real)) {czero_idx}"
    by (rule has_sum_cong_neutral) (auto simp: cone_def czero_idx_in)
  hence "((\<lambda>\<alpha>. ra_monomial h \<alpha> *\<^sub>R cone \<alpha>) has_sum (1::real)) ra_idx"
    using sing val by simp
  thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cone \<alpha>) has_sum (1::real)) ra_idx"
    by (simp only: h_def)
qed

lemma series_on_mult:
  assumes "series_on x0 r c1 F" and "series_on x0 r c2 G"
  shows "series_on x0 r (ccauchy c1 c2) (\<lambda>x. F x * G x)"
  unfolding series_on_def
proof (intro allI impI)
  fix x :: 'a assume d: "dist x x0 < r"
  have F1: "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> * c1 \<alpha>) has_sum F x) ra_idx"
    using assms(1) d unfolding series_on_def by simp
  have G1: "((\<lambda>\<beta>. ra_monomial (x - x0) \<beta> * c2 \<beta>) has_sum G x) ra_idx"
    using assms(2) d unfolding series_on_def by simp
  show "((\<lambda>\<gamma>. ra_monomial (x - x0) \<gamma> *\<^sub>R ccauchy c1 c2 \<gamma>) has_sum (F x * G x)) ra_idx"
    by (rule quant_mult[OF F1 G1])
qed

definition cpow :: "(('a::euclidean_space\<Rightarrow>nat)\<Rightarrow>real) \<Rightarrow> nat \<Rightarrow> (('a\<Rightarrow>nat)\<Rightarrow>real)" where
  "cpow c n = (ccauchy c ^^ n) cone"

lemma cpow_0: "cpow c 0 = cone" by (simp add: cpow_def)
lemma cpow_Suc: "cpow c (Suc n) = ccauchy c (cpow c n)" by (simp add: cpow_def)

lemma series_on_power:
  assumes "series_on x0 r c F"
  shows "series_on x0 r (cpow c n) (\<lambda>x. (F x) ^ n)"
proof (induction n)
  case 0
  show ?case using series_on_one[of x0 r] by (simp add: cpow_0)
next
  case (Suc n)
  have "series_on x0 r (ccauchy c (cpow c n)) (\<lambda>x. F x * (F x) ^ n)"
    by (rule series_on_mult[OF assms Suc.IH])
  thus ?case by (simp add: cpow_Suc)
qed

lemma series_on_prod:
  fixes F :: "'i \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes "finite I"
    and "\<And>i. i \<in> I \<Longrightarrow> \<exists>c. series_on x0 r c (F i)"
  shows "\<exists>cc. series_on x0 r cc (\<lambda>x. \<Prod>i\<in>I. F i x)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  have "series_on x0 r cone (\<lambda>x. \<Prod>i\<in>{}. F i x)" using series_on_one[of x0 r] by simp
  thus ?case by blast
next
  case (insert j I)
  obtain cj where cj: "series_on x0 r cj (F j)" using insert.prems[of j] by blast
  obtain crest where crest: "series_on x0 r crest (\<lambda>x. \<Prod>i\<in>I. F i x)"
    using insert.prems insert.IH by blast
  have "series_on x0 r (ccauchy cj crest) (\<lambda>x. F j x * (\<Prod>i\<in>I. F i x))"
    by (rule series_on_mult[OF cj crest])
  hence "series_on x0 r (ccauchy cj crest) (\<lambda>x. \<Prod>i\<in>insert j I. F i x)"
    using insert.hyps by simp
  thus ?case by blast
qed

lemma series_on_const:
  "series_on x0 r (\<lambda>\<alpha>. k * cone \<alpha>) (\<lambda>_. k)"
  unfolding series_on_def
proof (intro allI impI)
  fix x :: 'a assume d: "dist x x0 < r"
  have "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cone \<alpha>) has_sum (1::real)) ra_idx"
    using series_on_one[of x0 r] d unfolding series_on_def by simp
  hence "((\<lambda>\<alpha>. k * (ra_monomial (x - x0) \<alpha> *\<^sub>R cone \<alpha>)) has_sum (k * 1)) ra_idx"
    by (rule has_sum_cmult_right)
  thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (k * cone \<alpha>)) has_sum k) ra_idx"
    by (simp add: mult.left_commute)
qed

lemma series_on_add:
  assumes "series_on x0 r c1 F" and "series_on x0 r c2 G"
  shows "series_on x0 r (\<lambda>\<alpha>. c1 \<alpha> + c2 \<alpha>) (\<lambda>x. F x + G x)"
  unfolding series_on_def
proof (intro allI impI)
  fix x :: 'a assume d: "dist x x0 < r"
  have F1: "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>) has_sum F x) ra_idx"
    using assms(1) d unfolding series_on_def by simp
  have G1: "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>) has_sum G x) ra_idx"
    using assms(2) d unfolding series_on_def by simp
  have "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha> + ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>)
            has_sum (F x + G x)) ra_idx"
    by (rule has_sum_add[OF F1 G1])
  thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (c1 \<alpha> + c2 \<alpha>)) has_sum (F x + G x)) ra_idx"
    by (simp only: scaleR_add_right)
qed

lemma series_on_diff:
  assumes "series_on x0 r c1 F" and "series_on x0 r c2 G"
  shows "series_on x0 r (\<lambda>\<alpha>. c1 \<alpha> - c2 \<alpha>) (\<lambda>x. F x - G x)"
  unfolding series_on_def
proof (intro allI impI)
  fix x :: 'a assume d: "dist x x0 < r"
  have F1: "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>) has_sum F x) ra_idx"
    using assms(1) d unfolding series_on_def by simp
  have G1: "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>) has_sum G x) ra_idx"
    using assms(2) d unfolding series_on_def by simp
  have G1': "((\<lambda>\<alpha>. - (ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>)) has_sum (- G x)) ra_idx"
    using G1 by (simp add: has_sum_uminus)
  have "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha> + (- (ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>)))
            has_sum (F x + (- G x))) ra_idx"
    by (rule has_sum_add[OF F1 G1'])
  thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (c1 \<alpha> - c2 \<alpha>)) has_sum (F x - G x)) ra_idx"
    by (simp only: scaleR_diff_right, simp)
qed

text \<open>From a vector series on a ball, the scalar component has a series on the
  same ball.\<close>

lemma series_on_component:
  fixes cf :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::euclidean_space"
  assumes HS: "\<And>x. dist x x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cf \<alpha>) has_sum f x) ra_idx"
  shows "series_on x0 r (\<lambda>\<alpha>. cf \<alpha> \<bullet> b) (\<lambda>x. f x \<bullet> b)"
  unfolding series_on_def
proof (intro allI impI)
  fix x :: 'a assume d: "dist x x0 < r"
  have bl: "bounded_linear (\<lambda>y::'b. y \<bullet> b)" by (rule bounded_linear_inner_left)
  have "((\<lambda>\<alpha>. (ra_monomial (x - x0) \<alpha> *\<^sub>R cf \<alpha>) \<bullet> b) has_sum (f x \<bullet> b)) ra_idx"
    by (rule has_sum_bounded_linear[OF bl HS[OF d]])
  thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (cf \<alpha> \<bullet> b)) has_sum (f x \<bullet> b)) ra_idx"
    by (simp only: inner_scaleR_left scaleR_conv_of_real) simp
qed

text \<open>Quantitative monomial-compose: a series for \<open>x \<mapsto> ra_monomial (f x - z) \<beta>\<close>
  on the SAME ball as f's series.\<close>

lemma series_on_ra_monomial_compose:
  fixes cf :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::euclidean_space"
  assumes HS: "\<And>x. dist x x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cf \<alpha>) has_sum f x) ra_idx"
  shows "\<exists>cc. series_on x0 r cc (\<lambda>x. ra_monomial (f x - z) \<beta>)"
proof -
  have comp: "\<exists>c. series_on x0 r c (\<lambda>x. ((f x - z) \<bullet> b) ^ (\<beta> b))" if "b \<in> Basis" for b
  proof -
    have s1: "series_on x0 r (\<lambda>\<alpha>. cf \<alpha> \<bullet> b) (\<lambda>x. f x \<bullet> b)"
      by (rule series_on_component[OF HS])
    have s2: "series_on x0 r (\<lambda>\<alpha>. (z \<bullet> b) * cone \<alpha>) (\<lambda>_. z \<bullet> b)"
      by (rule series_on_const)
    have "series_on x0 r (\<lambda>\<alpha>. (cf \<alpha> \<bullet> b) - (z \<bullet> b) * cone \<alpha>) (\<lambda>x. (f x \<bullet> b) - (z \<bullet> b))"
      by (rule series_on_diff[OF s1 s2])
    hence "series_on x0 r (\<lambda>\<alpha>. (cf \<alpha> \<bullet> b) - (z \<bullet> b) * cone \<alpha>) (\<lambda>x. (f x - z) \<bullet> b)"
      by (simp only: inner_diff_left)
    hence "series_on x0 r (cpow (\<lambda>\<alpha>. (cf \<alpha> \<bullet> b) - (z \<bullet> b) * cone \<alpha>) (\<beta> b))
              (\<lambda>x. ((f x - z) \<bullet> b) ^ (\<beta> b))"
      by (rule series_on_power)
    thus ?thesis by blast
  qed
  have "\<exists>cc. series_on x0 r cc (\<lambda>x. \<Prod>b\<in>Basis. ((f x - z) \<bullet> b) ^ (\<beta> b))"
    by (rule series_on_prod[OF finite_Basis]) (use comp in simp)
  then obtain cc where "series_on x0 r cc (\<lambda>x. \<Prod>b\<in>Basis. ((f x - z) \<bullet> b) ^ (\<beta> b))"
    by blast
  hence "series_on x0 r cc (\<lambda>x. ra_monomial (f x - z) \<beta>)"
    by (simp only: ra_monomial_def)
  thus ?thesis by blast
qed

subsection \<open>Majorant norm: submultiplicative under the Cauchy product\<close>

definition mfam :: "real \<Rightarrow> (('a::euclidean_space\<Rightarrow>nat)\<Rightarrow>real) \<Rightarrow> (('a\<Rightarrow>nat)\<Rightarrow>real)" where
  "mfam \<sigma> u = (\<lambda>\<alpha>. \<bar>u \<alpha>\<bar> * \<sigma> ^ ra_deg \<alpha>)"

definition majle :: "real \<Rightarrow> (('a::euclidean_space\<Rightarrow>nat)\<Rightarrow>real) \<Rightarrow> real \<Rightarrow> bool" where
  "majle \<sigma> u K \<longleftrightarrow> (mfam \<sigma> u summable_on ra_idx) \<and> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> u \<alpha>) \<le> K"

lemma mfam_nonneg: "0 \<le> \<sigma> \<Longrightarrow> 0 \<le> mfam \<sigma> u \<alpha>"
  by (simp add: mfam_def)

lemma majle_imp_nonneg_sum:
  assumes "0 \<le> \<sigma>" "majle \<sigma> u K"
  shows "0 \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> u \<alpha>)"
  using assms by (auto intro!: infsum_nonneg simp: mfam_nonneg)

lemma majle_one:
  assumes "0 \<le> \<sigma>"
  shows "majle \<sigma> cone 1"
proof -
  have hs': "(mfam \<sigma> cone has_sum 1) ra_idx"
  proof (rule has_sum_finite_neutralI)
    show "finite {czero_idx}"
      by simp
    show "{czero_idx} \<subseteq> ra_idx"
      using czero_idx_in by simp   
    show "(1::real) = (\<Sum>\<alpha>\<in>{czero_idx}. mfam \<sigma> cone \<alpha>)"
      by (simp add: mfam_def cone_def ra_deg_def czero_idx_def)
    show "\<And>x. x \<in> ra_idx - {czero_idx} \<Longrightarrow> mfam \<sigma> Real_Analytic.cone x = 0"
      by (simp add: Real_Analytic.cone_def mfam_def)
  qed
  have s: "mfam \<sigma> cone summable_on ra_idx"
    using hs' has_sum_imp_summable by blast
  have i: "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> cone \<alpha>) = 1"
    by (rule infsumI[OF hs'])
  show ?thesis
    by (simp add: i majle_def s)
qed

text \<open>Convolution of two nonnegative summable families: the inner-low finite sums
  sum (over \<open>ra_idx\<close>) to the product of the totals.\<close>

lemma cauchy_abs_prod:
  fixes u' v' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes Uhs: "(u' has_sum Uv) ra_idx" and Vhs: "(v' has_sum Vv) ra_idx"
  shows "((\<lambda>\<gamma>. \<Sum>\<alpha>\<in>lowI \<gamma>. u' \<alpha> * v' (subI \<gamma> \<alpha>)) has_sum (Uv * Vv)) ra_idx"
proof -
  have prodHS: "((\<lambda>(\<alpha>,\<beta>). u' \<alpha> * v' \<beta>) has_sum (Uv * Vv)) (ra_idx \<times> ra_idx)"
    using prod_has_sum[OF Uhs Vhs] .
  have reix: "((\<lambda>(\<gamma>,\<alpha>). u' \<alpha> * v' (subI \<gamma> \<alpha>)) has_sum (Uv * Vv)) (Sigma ra_idx lowI)"
  proof -
    have "((\<lambda>(\<alpha>,\<beta>). u' \<alpha> * v' \<beta>) has_sum (Uv * Vv)) (ra_idx \<times> ra_idx)
          = ((\<lambda>(\<gamma>,\<alpha>). u' \<alpha> * v' (subI \<gamma> \<alpha>)) has_sum (Uv * Vv)) (Sigma ra_idx lowI)"
    proof (rule has_sum_reindex_bij_witness
             [where j = "\<lambda>(\<alpha>,\<beta>). (addI \<alpha> \<beta>, \<alpha>)" and i = "\<lambda>(\<gamma>,\<alpha>). (\<alpha>, subI \<gamma> \<alpha>)"])
      fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume "p \<in> ra_idx \<times> ra_idx"
      obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
      show "(case (case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) = p"
        by (simp add: p subI_def addI_def)
    next
      fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume P: "p \<in> ra_idx \<times> ra_idx"
      obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
      have a\<alpha>: "\<alpha> \<in> ra_idx" and a\<beta>: "\<beta> \<in> ra_idx" using P p by auto
      have m1: "addI \<alpha> \<beta> \<in> ra_idx" by (rule idx_add[OF a\<alpha> a\<beta>])
      have m2: "\<alpha> \<in> lowI (addI \<alpha> \<beta>)" using a\<alpha> by (simp add: lowI_def leI_def addI_def)
      show "(case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) \<in> Sigma ra_idx lowI"
        using m1 m2 by (simp add: p)
    next
      fix q :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume Q: "q \<in> Sigma ra_idx lowI"
      obtain \<gamma> \<alpha> where q: "q = (\<gamma>,\<alpha>)" by (cases q)
      have g\<gamma>: "\<gamma> \<in> ra_idx" and l: "leI \<alpha> \<gamma>" using Q q by (auto simp: lowI_def)
      have "addI \<alpha> (subI \<gamma> \<alpha>) = \<gamma>"
      proof (rule ext)
        fix b have "\<alpha> b \<le> \<gamma> b" using l by (simp only: leI_def)
        thus "addI \<alpha> (subI \<gamma> \<alpha>) b = \<gamma> b" by (simp only: addI_def subI_def)
      qed
      then show "(case (case q of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) = q"
        by (simp add: q)
    next
      fix q :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume Q: "q \<in> Sigma ra_idx lowI"
      obtain \<gamma> \<alpha> where q: "q = (\<gamma>,\<alpha>)" by (cases q)
      have g\<gamma>: "\<gamma> \<in> ra_idx" and a\<alpha>: "\<alpha> \<in> ra_idx" using Q q by (auto simp: lowI_def)
      show "(case q of (\<gamma>,\<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) \<in> ra_idx \<times> ra_idx"
        by (simp add: q a\<alpha> idx_sub[OF g\<gamma>])
    next
      fix p :: "('a\<Rightarrow>nat) \<times> ('a\<Rightarrow>nat)"
      assume P: "p \<in> ra_idx \<times> ra_idx"
      obtain \<alpha> \<beta> where p: "p = (\<alpha>,\<beta>)" by (cases p)
      have sub_eq: "subI (addI \<alpha> \<beta>) \<alpha> = \<beta>" by (simp add: addI_def subI_def)
      show "(case (case p of (\<alpha>,\<beta>) \<Rightarrow> (addI \<alpha> \<beta>, \<alpha>)) of (\<gamma>,\<alpha>) \<Rightarrow> u' \<alpha> * v' (subI \<gamma> \<alpha>))
                 = (case p of (\<alpha>,\<beta>) \<Rightarrow> u' \<alpha> * v' \<beta>)"
        by (simp add: p sub_eq)
    qed simp
    with prodHS show ?thesis by simp
  qed
  show ?thesis
  proof (rule has_sum_Sigma'
           [where f = "\<lambda>(\<gamma>,\<alpha>). u' \<alpha> * v' (subI \<gamma> \<alpha>)" and A = ra_idx and B = lowI
              and a = "Uv * Vv" and b = "\<lambda>\<gamma>. \<Sum>\<alpha>\<in>lowI \<gamma>. u' \<alpha> * v' (subI \<gamma> \<alpha>)"])
    show "((\<lambda>(\<gamma>,\<alpha>). u' \<alpha> * v' (subI \<gamma> \<alpha>)) has_sum (Uv * Vv)) (Sigma ra_idx lowI)"
      by (rule reix)
  next
    fix \<gamma> :: "'a \<Rightarrow> nat" assume g: "\<gamma> \<in> ra_idx"
    have fin: "finite (lowI \<gamma>)" by (rule idx_lower_fin)
    have "((\<lambda>\<alpha>. u' \<alpha> * v' (subI \<gamma> \<alpha>)) has_sum
             (\<Sum>\<alpha>\<in>lowI \<gamma>. u' \<alpha> * v' (subI \<gamma> \<alpha>))) (lowI \<gamma>)"
      by (rule has_sum_finite[OF fin])
    thus "((\<lambda>\<alpha>. (\<lambda>(\<gamma>,\<alpha>). u' \<alpha> * v' (subI \<gamma> \<alpha>)) (\<gamma>, \<alpha>)) has_sum
              (\<Sum>\<alpha>\<in>lowI \<gamma>. u' \<alpha> * v' (subI \<gamma> \<alpha>))) (lowI \<gamma>)" by simp
  qed
qed

text \<open>Degree is additive across the Cauchy split.\<close>

lemma ra_deg_split:
  fixes \<gamma> :: "'a::euclidean_space \<Rightarrow> nat"
  assumes "\<alpha> \<in> lowI \<gamma>"
  shows "ra_deg \<gamma> = ra_deg \<alpha> + ra_deg (subI \<gamma> \<alpha>)"
proof -
  have l: "leI \<alpha> \<gamma>" using assms by (simp add: lowI_def)
  have "addI \<alpha> (subI \<gamma> \<alpha>) = \<gamma>"
  proof (rule ext)
    fix b have "\<alpha> b \<le> \<gamma> b" using l by (simp only: leI_def)
    thus "addI \<alpha> (subI \<gamma> \<alpha>) b = \<gamma> b" by (simp only: addI_def subI_def)
  qed
  hence "ra_deg \<gamma> = ra_deg (addI \<alpha> (subI \<gamma> \<alpha>))" by simp
  also have "\<dots> = ra_deg \<alpha> + ra_deg (subI \<gamma> \<alpha>)"
    by (simp only: ra_deg_def addI_def sum.distrib)
  finally show ?thesis .
qed

text \<open>The key submultiplicativity estimate.\<close>

lemma majle_ccauchy:
  fixes u v :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes s0: "0 \<le> \<sigma>"
    and U: "majle \<sigma> u KU" and V: "majle \<sigma> v KV"
    and KUnn: "0 \<le> KU" and KVnn: "0 \<le> KV"
  shows "majle \<sigma> (ccauchy u v) (KU * KV)"
proof -
  define u' where "u' = mfam \<sigma> u"
  define v' where "v' = mfam \<sigma> v"
  have u'nn: "0 \<le> u' \<alpha>" for \<alpha> using s0 by (simp add: u'_def mfam_nonneg)
  have v'nn: "0 \<le> v' \<alpha>" for \<alpha> using s0 by (simp add: v'_def mfam_nonneg)
  have u'_sum: "u' summable_on ra_idx" using U by (simp add: majle_def u'_def)
  have v'_sum: "v' summable_on ra_idx" using V by (simp add: majle_def v'_def)
  define Uv where "Uv = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. u' \<alpha>)"
  define Vv where "Vv = (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. v' \<beta>)"
  have Uhs: "(u' has_sum Uv) ra_idx" using u'_sum by (simp add: Uv_def)
  have Vhs: "(v' has_sum Vv) ra_idx" using v'_sum by (simp add: Vv_def)
  have UvKU: "Uv \<le> KU" using U by (simp add: majle_def u'_def Uv_def)
  have VvKV: "Vv \<le> KV" using V by (simp add: majle_def v'_def Vv_def)
  have Uvnn: "0 \<le> Uv" unfolding Uv_def using u'nn u'_sum by (auto intro!: infsum_nonneg)
  have Vvnn: "0 \<le> Vv" unfolding Vv_def using v'nn v'_sum by (auto intro!: infsum_nonneg)
  define S where "S = (\<lambda>\<gamma>. \<Sum>\<alpha>\<in>lowI \<gamma>. u' \<alpha> * v' (subI \<gamma> \<alpha>))"
  have collapse: "(S has_sum (Uv * Vv)) ra_idx"
    unfolding S_def by (rule cauchy_abs_prod[OF Uhs Vhs])
  have collapse_sum: "S summable_on ra_idx"
    using collapse has_sum_imp_summable by blast
  have Snn: "0 \<le> S \<gamma>" for \<gamma>
    unfolding S_def by (intro sum_nonneg mult_nonneg_nonneg u'nn v'nn)
  \<comment> \<open>each Cauchy coefficient majorant term is bounded by the inner-low sum\<close>
  have termbound: "mfam \<sigma> (ccauchy u v) \<gamma> \<le> S \<gamma>" if g: "\<gamma> \<in> ra_idx" for \<gamma>
  proof -
    have fin: "finite (lowI \<gamma>)" by (rule idx_lower_fin)
    have termeq: "\<bar>u \<alpha> * v (subI \<gamma> \<alpha>)\<bar> * \<sigma> ^ ra_deg \<gamma> = u' \<alpha> * v' (subI \<gamma> \<alpha>)"
      if a: "\<alpha> \<in> lowI \<gamma>" for \<alpha>
    proof -
      have dd: "\<sigma> ^ ra_deg \<gamma> = \<sigma> ^ ra_deg \<alpha> * \<sigma> ^ ra_deg (subI \<gamma> \<alpha>)"
        by (simp only: ra_deg_split[OF a] power_add)
      have "\<bar>u \<alpha> * v (subI \<gamma> \<alpha>)\<bar> * \<sigma> ^ ra_deg \<gamma>
              = (\<bar>u \<alpha>\<bar> * \<bar>v (subI \<gamma> \<alpha>)\<bar>) * (\<sigma> ^ ra_deg \<alpha> * \<sigma> ^ ra_deg (subI \<gamma> \<alpha>))"
        by (simp only: abs_mult dd)
      also have "\<dots> = (\<bar>u \<alpha>\<bar> * \<sigma> ^ ra_deg \<alpha>) * (\<bar>v (subI \<gamma> \<alpha>)\<bar> * \<sigma> ^ ra_deg (subI \<gamma> \<alpha>))"
        by (simp only: mult.assoc mult.left_commute)
      finally show ?thesis by (simp only: u'_def v'_def mfam_def)
    qed
    have "mfam \<sigma> (ccauchy u v) \<gamma> = \<bar>\<Sum>\<alpha>\<in>lowI \<gamma>. u \<alpha> * v (subI \<gamma> \<alpha>)\<bar> * \<sigma> ^ ra_deg \<gamma>"
      by (simp only: mfam_def ccauchy_def)
    also have "\<dots> \<le> (\<Sum>\<alpha>\<in>lowI \<gamma>. \<bar>u \<alpha> * v (subI \<gamma> \<alpha>)\<bar>) * \<sigma> ^ ra_deg \<gamma>"
      by (rule mult_right_mono[OF sum_abs]) (use s0 in simp)
    also have "\<dots> = (\<Sum>\<alpha>\<in>lowI \<gamma>. \<bar>u \<alpha> * v (subI \<gamma> \<alpha>)\<bar> * \<sigma> ^ ra_deg \<gamma>)"
      by (simp only: sum_distrib_right)
    also have "\<dots> = (\<Sum>\<alpha>\<in>lowI \<gamma>. u' \<alpha> * v' (subI \<gamma> \<alpha>))"
      by (rule sum.cong[OF refl termeq])
    also have "\<dots> = S \<gamma>" by (simp only: S_def)
    finally show ?thesis .
  qed
  have cnn: "0 \<le> mfam \<sigma> (ccauchy u v) \<gamma>" for \<gamma> using s0 by (simp add: mfam_nonneg)
  have cmaj_sum: "mfam \<sigma> (ccauchy u v) summable_on ra_idx"
  proof (rule summable_on_comparison_test[where f = S and g = "mfam \<sigma> (ccauchy u v)"])
    show "S summable_on ra_idx" by (rule collapse_sum)
  next
    fix \<gamma> :: "'a \<Rightarrow> nat" assume g: "\<gamma> \<in> ra_idx"
    show "mfam \<sigma> (ccauchy u v) \<gamma> \<le> S \<gamma>" by (rule termbound[OF g])
  next
    fix \<gamma> :: "'a \<Rightarrow> nat" assume "\<gamma> \<in> ra_idx"
    show "0 \<le> mfam \<sigma> (ccauchy u v) \<gamma>" by (rule cnn)
  qed
  have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>ra_idx. mfam \<sigma> (ccauchy u v) \<gamma>) \<le> (\<Sum>\<^sub>\<infinity>\<gamma>\<in>ra_idx. S \<gamma>)"
    by (rule infsum_mono[OF cmaj_sum collapse_sum]) (rule termbound)
  also have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>ra_idx. S \<gamma>) = Uv * Vv" by (rule infsumI[OF collapse])
  also have "Uv * Vv \<le> KU * KV"
    using UvKU VvKV Uvnn Vvnn KVnn by (intro mult_mono) auto
  finally have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>ra_idx. mfam \<sigma> (ccauchy u v) \<gamma>) \<le> KU * KV" .
  thus ?thesis using cmaj_sum by (simp add: majle_def)
qed


text \<open>Difference of analytic functions is analytic.\<close>

lemma real_analytic_on_diff:
  fixes f g :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes F: "real_analytic_on f U" and G: "real_analytic_on g U"
  shows "real_analytic_on (\<lambda>x. f x - g x) U"
proof -
  have "real_analytic_on (\<lambda>x. (-1) *\<^sub>R g x) U"
    by (rule real_analytic_on_scaleR[OF G])
  hence "real_analytic_on (\<lambda>x. f x + (-1) *\<^sub>R g x) U"
    by (rule real_analytic_on_add[OF F])
  thus ?thesis by simp
qed

text \<open>A natural power of an analytic scalar function is analytic.\<close>

lemma real_analytic_on_power:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. (f x) ^ n) U"
proof (induction n)
  case 0
  from F have U: "open U" by (simp only: real_analytic_on_def)
  show ?case using real_analytic_on_const[OF U, of "1::real"] by simp
next
  case (Suc n)
  have "real_analytic_on (\<lambda>x. f x * (f x) ^ n) U"
    by (rule real_analytic_on_mult[OF F Suc.IH])
  thus ?case by simp
qed

text \<open>A finite product of analytic scalar functions is analytic.\<close>

lemma real_analytic_on_prod:
  fixes f :: "'i \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes U: "open U"
    and F: "\<And>i. i \<in> I \<Longrightarrow> real_analytic_on (f i) U"
  shows "real_analytic_on (\<lambda>x. \<Prod>i\<in>I. f i x) U"
  using F
proof (induction I rule: infinite_finite_induct)
  case (infinite I)
  have "(\<lambda>x. \<Prod>i\<in>I. f i x) = (\<lambda>x. 1)" using infinite.hyps by simp
  thus ?case using real_analytic_on_const[OF U, of "1::real"] by simp
next
  case empty
  show ?case using real_analytic_on_const[OF U, of "1::real"] by simp
next
  case (insert j I)
  have aj: "real_analytic_on (f j) U" using insert.prems by simp
  have arest: "real_analytic_on (\<lambda>x. \<Prod>i\<in>I. f i x) U"
    using insert.prems by (intro insert.IH) simp
  have "real_analytic_on (\<lambda>x. f j x * (\<Prod>i\<in>I. f i x)) U"
    by (rule real_analytic_on_mult[OF aj arest])
  thus ?case using insert.hyps by simp
qed

text \<open>The basis-monomial of an analytic vector function (in the shifted argument)
  is analytic: \<open>x \<mapsto> ra_monomial (f x - z) \<beta>\<close>.\<close>

lemma real_analytic_on_ra_monomial_compose:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. ra_monomial (f x - z) \<beta>) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  have comp: "real_analytic_on (\<lambda>x. ((f x - z) \<bullet> b) ^ (\<beta> b)) U" if "b \<in> Basis" for b
  proof -
    have "real_analytic_on (\<lambda>x. f x \<bullet> b) U"
      by (rule real_analytic_on_inner_component[OF F])
    moreover have "real_analytic_on (\<lambda>x. z \<bullet> b) U"
      by (rule real_analytic_on_const[OF U])
    ultimately have "real_analytic_on (\<lambda>x. (f x \<bullet> b) - (z \<bullet> b)) U"
      by (rule real_analytic_on_diff)
    hence "real_analytic_on (\<lambda>x. (f x - z) \<bullet> b) U"
      by (simp only: inner_diff_left)
    thus ?thesis by (rule real_analytic_on_power)
  qed
  have "real_analytic_on (\<lambda>x. \<Prod>b\<in>Basis. ((f x - z) \<bullet> b) ^ (\<beta> b)) U"
    by (rule real_analytic_on_prod[OF U]) (use comp in simp)
  thus ?thesis by (simp only: ra_monomial_def)
qed

subsection \<open>Step (a): power lift of a majle bound\<close>

lemma majle_cpow:
  fixes c :: "('a::euclidean_space\<Rightarrow>nat)\<Rightarrow>real"
  assumes s0: "0 \<le> \<sigma>" and K: "majle \<sigma> c K" and Knn: "0 \<le> K"
  shows "majle \<sigma> (cpow c n) (K^n)"
proof (induction n)
  case 0
  show ?case using majle_one[OF s0] by (simp add: cpow_0)
next
  case (Suc n)
  have "majle \<sigma> (ccauchy c (cpow c n)) (K * K^n)"
    by (rule majle_ccauchy[OF s0 K Suc.IH Knn], simp only: Knn zero_le_power)
  thus ?case by (simp add: cpow_Suc)
qed

subsection \<open>Step (b): coefficient bound gives a majle bound\<close>

text \<open>The basis product of a constant base equals the base raised to the degree.\<close>

lemma prod_const_ra_deg:
  fixes t :: real
  shows "(\<Prod>b\<in>(Basis::'a::euclidean_space set). t ^ (\<alpha> b)) = t ^ ra_deg \<alpha>"
  by (simp add: ra_deg_def power_sum)

lemma coeff_majle_of_bound:
  fixes c :: "('b::euclidean_space\<Rightarrow>nat)\<Rightarrow>'d::real_normed_vector"
  assumes Mnn: "0 \<le> M"
    and bound: "\<And>\<alpha>. \<alpha>\<in>ra_idx \<Longrightarrow> norm (c \<alpha>) \<le> M / t ^ (ra_deg \<alpha>)"
    and t: "0 < t" and s0: "0 \<le> \<sigma>" and st: "\<sigma> < t"
  shows "majle \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) (M * (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). (\<sigma>/t) ^ ra_deg \<alpha>))"
proof -
  define q where "q = \<sigma>/t"
  have q0: "0 \<le> q" using s0 t by (simp add: q_def)
  have q1: "q < 1" using st t by (simp add: q_def)
  have geomS: "(\<lambda>\<alpha>::'b\<Rightarrow>nat. q ^ ra_deg \<alpha>) summable_on ra_idx"
    by (rule geom_idx_summable[OF q0 q1])
  have geomMS: "(\<lambda>\<alpha>. M * q ^ ra_deg \<alpha>) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    by (rule summable_on_cmult_right[OF geomS])
  \<comment> \<open>pointwise domination of the majorant family by the geometric majorant\<close>
  have ptwise: "mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha> \<le> M * q ^ ra_deg \<alpha>" if a: "\<alpha>\<in>ra_idx" for \<alpha>
  proof -
    have tpow: "0 < t ^ ra_deg \<alpha>" using t by simp
    have "mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha> = norm (c \<alpha>) * \<sigma> ^ ra_deg \<alpha>"
      by (simp add: mfam_def)
    also have "\<dots> \<le> (M / t ^ ra_deg \<alpha>) * \<sigma> ^ ra_deg \<alpha>"
      by (rule mult_right_mono[OF bound[OF a]]) (use s0 in simp)
    also have "\<dots> = M * (\<sigma> ^ ra_deg \<alpha> / t ^ ra_deg \<alpha>)" by simp
    also have "\<dots> = M * q ^ ra_deg \<alpha>"
      by (simp add: q_def power_divide)
    finally show ?thesis .
  qed
  have nn: "0 \<le> mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha>" for \<alpha> using s0 by (rule mfam_nonneg)
  have summ: "mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) summable_on ra_idx"
    by (rule summable_on_comparison_test[OF geomMS]) (use ptwise nn in auto)
  have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha>)
          \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). M * q ^ ra_deg \<alpha>)"
    by (rule infsum_mono[OF summ geomMS]) (rule ptwise)
  also have "\<dots> = M * (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). q ^ ra_deg \<alpha>)"
    by (rule infsum_cmult_right[OF geomS])
  finally show ?thesis using summ by (simp add: majle_def q_def)
qed

subsection \<open>Majle helpers: domination, scaling, triangle\<close>

text \<open>If \<open>|c1 \<alpha>| \<le> |c2 \<alpha>|\<close> pointwise and \<open>c2\<close> is majle-bounded, so is \<open>c1\<close>.\<close>

lemma majle_dom:
  fixes c1 c2 :: "('a::euclidean_space\<Rightarrow>nat)\<Rightarrow>real"
  assumes s0: "0 \<le> \<sigma>"
    and dom: "\<And>\<alpha>. \<alpha>\<in>ra_idx \<Longrightarrow> \<bar>c1 \<alpha>\<bar> \<le> \<bar>c2 \<alpha>\<bar>"
    and B: "majle \<sigma> c2 K"
  shows "majle \<sigma> c1 K"
proof -
  have c2sum: "mfam \<sigma> c2 summable_on ra_idx" using B by (simp add: majle_def)
  have ptw: "mfam \<sigma> c1 \<alpha> \<le> mfam \<sigma> c2 \<alpha>" if "\<alpha>\<in>ra_idx" for \<alpha>
    unfolding mfam_def using dom[OF that] s0 by (simp add: mult_right_mono)
  have nn: "0 \<le> mfam \<sigma> c1 \<alpha>" for \<alpha> using s0 by (rule mfam_nonneg)
  have c1sum: "mfam \<sigma> c1 summable_on ra_idx"
    by (rule summable_on_comparison_test[OF c2sum]) (use ptw nn in auto)
  have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> c1 \<alpha>) \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> c2 \<alpha>)"
    by (rule infsum_mono[OF c1sum c2sum]) (rule ptw)
  also have "\<dots> \<le> K" using B by (simp add: majle_def)
  finally show ?thesis using c1sum by (simp add: majle_def)
qed

lemma majle_zero:
  "majle \<sigma> ((\<lambda>_. 0) :: ('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real) 0"
  by (simp add: majle_def mfam_def)

lemma majle_cmul:
  fixes c :: "('a::euclidean_space\<Rightarrow>nat)\<Rightarrow>real"
  assumes s0: "0 \<le> \<sigma>" and B: "majle \<sigma> c K"
  shows "majle \<sigma> (\<lambda>\<alpha>. a * c \<alpha>) (\<bar>a\<bar> * K)"
proof -
  have csum: "mfam \<sigma> c summable_on ra_idx" using B by (simp add: majle_def)
  have eq: "mfam \<sigma> (\<lambda>\<alpha>. a * c \<alpha>) = (\<lambda>\<alpha>. \<bar>a\<bar> * mfam \<sigma> c \<alpha>)"
    by (rule ext) (simp add: mfam_def abs_mult)
  have asum: "mfam \<sigma> (\<lambda>\<alpha>. a * c \<alpha>) summable_on ra_idx"
    using summable_on_cmult_right[OF csum, where c = "\<bar>a\<bar>"] by (simp add: eq)
  have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> (\<lambda>\<alpha>. a * c \<alpha>) \<alpha>)
          = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. \<bar>a\<bar> * mfam \<sigma> c \<alpha>)" by (simp add: eq[THEN fun_cong])
  also have "\<dots> = \<bar>a\<bar> * (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> c \<alpha>)"
    by (rule infsum_cmult_right[OF csum])
  also have "\<dots> \<le> \<bar>a\<bar> * K" using B by (simp add: majle_def mult_left_mono)
  finally show ?thesis using asum by (simp add: majle_def)
qed

lemma majle_add:
  fixes c1 c2 :: "('a::euclidean_space\<Rightarrow>nat)\<Rightarrow>real"
  assumes s0: "0 \<le> \<sigma>" and A: "majle \<sigma> c1 K1" and B: "majle \<sigma> c2 K2"
  shows "majle \<sigma> (\<lambda>\<alpha>. c1 \<alpha> + c2 \<alpha>) (K1 + K2)"
proof -
  have c1sum: "mfam \<sigma> c1 summable_on ra_idx" using A by (simp add: majle_def)
  have c2sum: "mfam \<sigma> c2 summable_on ra_idx" using B by (simp add: majle_def)
  have ptw: "mfam \<sigma> (\<lambda>\<alpha>. c1 \<alpha> + c2 \<alpha>) \<alpha> \<le> mfam \<sigma> c1 \<alpha> + mfam \<sigma> c2 \<alpha>" for \<alpha>
  proof -
    have "mfam \<sigma> (\<lambda>\<alpha>. c1 \<alpha> + c2 \<alpha>) \<alpha> = \<bar>c1 \<alpha> + c2 \<alpha>\<bar> * \<sigma> ^ ra_deg \<alpha>"
      by (simp add: mfam_def)
    also have "\<dots> \<le> (\<bar>c1 \<alpha>\<bar> + \<bar>c2 \<alpha>\<bar>) * \<sigma> ^ ra_deg \<alpha>"
      by (rule mult_right_mono) (use s0 in \<open>auto simp: abs_triangle_ineq\<close>)
    also have "\<dots> = mfam \<sigma> c1 \<alpha> + mfam \<sigma> c2 \<alpha>"
      by (simp add: mfam_def distrib_right)
    finally show ?thesis .
  qed
  have nn: "0 \<le> mfam \<sigma> (\<lambda>\<alpha>. c1 \<alpha> + c2 \<alpha>) \<alpha>" for \<alpha> using s0 by (rule mfam_nonneg)
  have sumadd: "(\<lambda>\<alpha>. mfam \<sigma> c1 \<alpha> + mfam \<sigma> c2 \<alpha>) summable_on ra_idx"
    using c1sum c2sum by (rule summable_on_add)
  have addsum: "mfam \<sigma> (\<lambda>\<alpha>. c1 \<alpha> + c2 \<alpha>) summable_on ra_idx"
    by (rule summable_on_comparison_test[OF sumadd]) (use ptw nn in auto)
  have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> (\<lambda>\<alpha>. c1 \<alpha> + c2 \<alpha>) \<alpha>)
          \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> c1 \<alpha> + mfam \<sigma> c2 \<alpha>)"
    by (rule infsum_mono[OF addsum sumadd]) (rule ptw)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> c1 \<alpha>) + (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> c2 \<alpha>)"
    by (rule infsum_add[OF c1sum c2sum])
  also have "\<dots> \<le> K1 + K2" using A B by (simp add: majle_def add_mono)
  finally show ?thesis using addsum by (simp add: majle_def)
qed

lemma majle_vec_sum:
  fixes c :: "'i \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes s0: "0 \<le> \<sigma>"
    and fin: "finite I"
    and maj: "\<And>i. i \<in> I \<Longrightarrow> majle \<sigma> (\<lambda>\<alpha>. norm (c i \<alpha>)) (K i)"
  shows "majle \<sigma> (\<lambda>\<alpha>. norm (\<Sum>i\<in>I. c i \<alpha>)) (\<Sum>i\<in>I. K i)"
  using fin maj
proof (induction I rule: finite_induct)
  case empty
  show ?case
    by (simp add: majle_zero)
next
  case (insert i I)
  have ci: "majle \<sigma> (\<lambda>\<alpha>. norm (c i \<alpha>)) (K i)"
    using insert.prems by simp
  have cI: "majle \<sigma> (\<lambda>\<alpha>. norm (\<Sum>j\<in>I. c j \<alpha>)) (\<Sum>j\<in>I. K j)"
    using insert.IH insert.prems by blast
  have addmaj: "majle \<sigma> (\<lambda>\<alpha>. norm (c i \<alpha>) + norm (\<Sum>j\<in>I. c j \<alpha>))
      (K i + (\<Sum>j\<in>I. K j))"
    by (rule majle_add[OF s0 ci cI])
  have dom: "\<bar>norm (c i \<alpha> + (\<Sum>j\<in>I. c j \<alpha>))\<bar>
      \<le> \<bar>norm (c i \<alpha>) + norm (\<Sum>j\<in>I. c j \<alpha>)\<bar>"
    for \<alpha> :: "'a \<Rightarrow> nat"
    by (simp add: norm_triangle_ineq)
  show ?case
    using insert.hyps
    by (simp add: sum.insert[OF insert.hyps])
       (rule majle_dom[OF s0 _ addmaj], rule dom)
qed

lemma identity_coeff_series_majle:
  obtains cid :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a" where
    "\<And>y. ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R cid \<alpha>) has_sum y) ra_idx"
    "\<And>\<sigma>. 0 \<le> \<sigma> \<Longrightarrow>
      majle \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) (real (card (Basis :: 'a set)) * \<sigma>)"
proof -
  define e :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
    "e = (\<lambda>b x. if x = b then 1 else 0)"
  define cid :: "('a \<Rightarrow> nat) \<Rightarrow> 'a" where
    "cid = (\<lambda>\<alpha>. \<Sum>b\<in>Basis. if \<alpha> = e b then b else 0)"

  have e_idx: "e b \<in> ra_idx" if "b \<in> Basis" for b
    using that by (auto simp: e_def ra_idx_def)

  have e_inj: "inj_on e (Basis :: 'a set)"
  proof (rule inj_onI)
    fix b c :: 'a
    assume b: "b \<in> Basis" and c: "c \<in> Basis" and eq: "e b = e c"
    have h0: "e b b = e c b"
      using eq by simp
    have h: "(1::nat) = (if b = c then 1 else 0)"
      using h0 by (simp add: e_def)
    show "b = c"
    proof (rule ccontr)
      assume "b \<noteq> c"
      with h show False by simp
    qed
  qed

  have mono_e: "ra_monomial y (e b) = y \<bullet> b" if b: "b \<in> Basis" for y b
  proof -
    have "ra_monomial y (e b) =
        (y \<bullet> b) * (\<Prod>c\<in>Basis - {b}. (y \<bullet> c) ^ (e b c))"
      using b by (simp add: ra_monomial_def sum.remove e_def prod.remove)
    also have "\<dots> = y \<bullet> b"
      by (simp add: e_def)
    finally show ?thesis .
  qed

  have deg_e: "ra_deg (e b) = 1" if b: "b \<in> Basis" for b
    using b by (simp add: ra_deg_def e_def sum.remove[where x = b])

  have cid_e: "cid (e b) = b" if b: "b \<in> Basis" for b
  proof -
    have "cid (e b) = (\<Sum>c\<in>Basis. if c = b then c else 0)"
      unfolding cid_def
      by (rule sum.cong) (use b e_inj in \<open>auto simp: inj_on_def\<close>)
    also have "\<dots> = b"
      using b by simp
    finally show ?thesis .
  qed

  have cid_zero: "cid \<alpha> = 0" if "\<alpha> \<in> ra_idx - image e Basis" for \<alpha>
    unfolding cid_def
    by (rule sum.neutral) (use that in auto)

  have series: "((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R cid \<alpha>) has_sum y) ra_idx" for y
  proof (rule has_sum_finite_neutralI)
    show "finite (image e (Basis :: 'a set))"
      by simp
    show "image e (Basis :: 'a set) \<subseteq> ra_idx"
      using e_idx by blast
    have "(\<Sum>\<alpha>\<in>image e Basis. ra_monomial y \<alpha> *\<^sub>R cid \<alpha>) =
        (\<Sum>b\<in>Basis. ra_monomial y (e b) *\<^sub>R cid (e b))"
      by (rule sum.reindex_cong[where l = e, OF e_inj refl]) simp
    also have "\<dots> = (\<Sum>b\<in>Basis. (y \<bullet> b) *\<^sub>R b)"
      by (rule sum.cong) (use mono_e cid_e in auto)
    also have "\<dots> = y"
      by (simp add: euclidean_representation)
    finally show "y = (\<Sum>\<alpha>\<in>image e Basis. ra_monomial y \<alpha> *\<^sub>R cid \<alpha>)"
      by simp
    show "\<And>\<alpha>. \<alpha> \<in> ra_idx - image e Basis \<Longrightarrow> ra_monomial y \<alpha> *\<^sub>R cid \<alpha> = 0"
      by (simp add: cid_zero)
  qed

  have maj: "majle \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) (real (card (Basis :: 'a set)) * \<sigma>)"
    if s0: "0 \<le> \<sigma>" for \<sigma>
  proof -
    have hs: "(mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) has_sum
        (real (card (Basis :: 'a set)) * \<sigma>)) ra_idx"
    proof (rule has_sum_finite_neutralI)
      show "finite (image e (Basis :: 'a set))"
        by simp
      show "image e (Basis :: 'a set) \<subseteq> ra_idx"
        using e_idx by blast
      have "(\<Sum>\<alpha>\<in>image e Basis. mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) \<alpha>) =
          (\<Sum>b\<in>Basis. mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) (e b))"
        by (rule sum.reindex_cong[where l = e, OF e_inj refl]) simp
      also have "\<dots> = (\<Sum>b\<in>(Basis :: 'a set). \<sigma>)"
      proof -
        have term_eq: "mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) (e b) = \<sigma>"
          if b: "b \<in> (Basis :: 'a set)" for b
        proof -
        have "mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) (e b) =
            norm (cid (e b)) * \<sigma> ^ ra_deg (e b)"
          by (simp add: mfam_def)
        also have "\<dots> = \<sigma>"
          using b by (simp add: cid_e deg_e)
          finally show ?thesis .
        qed
        show ?thesis
          by (rule sum.cong[OF refl term_eq])
      qed
      also have "\<dots> = real (card (Basis :: 'a set)) * \<sigma>"
        by simp
      finally show "real (card (Basis :: 'a set)) * \<sigma> =
          (\<Sum>\<alpha>\<in>image e Basis. mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) \<alpha>)"
        by simp
      show "\<And>\<alpha>. \<alpha> \<in> ra_idx - image e Basis \<Longrightarrow>
        mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) \<alpha> = 0"
        by (simp add: cid_zero mfam_def)
    qed
    have summ: "mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) summable_on ra_idx"
      using hs has_sum_imp_summable by blast
    have inf: "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> (\<lambda>\<alpha>. norm (cid \<alpha>)) \<alpha>) =
        real (card (Basis :: 'a set)) * \<sigma>"
      by (rule infsumI[OF hs])
    show ?thesis
      by (simp add: majle_def summ inf)
  qed

  show ?thesis
    by (rule that[OF series maj])
qed

subsection \<open>Combined series_on + majle bookkeeping\<close>

text \<open>A predicate bundling: \<open>c\<close> is the coefficient family of \<open>F\<close> on the ball,
  and is majle-bounded by \<open>K\<close>.\<close>

definition smaj ::
  "'a::euclidean_space \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (('a\<Rightarrow>nat)\<Rightarrow>real) \<Rightarrow> ('a\<Rightarrow>real) \<Rightarrow> real \<Rightarrow> bool" where
  "smaj x0 r \<sigma> c F K \<longleftrightarrow> series_on x0 r c F \<and> majle \<sigma> c K"

lemma smaj_mono_radius:
  assumes "smaj x0 r \<sigma> c F K" and "r' \<le> r"
  shows "smaj x0 r' \<sigma> c F K"
  using assms series_on_mono_radius unfolding smaj_def by blast

lemma smaj_one:
  assumes "0 \<le> \<sigma>"
  shows "smaj x0 r \<sigma> cone (\<lambda>_. 1) 1"
  unfolding smaj_def using series_on_one majle_one[OF assms] by blast

lemma smaj_mult:
  assumes s0: "0 \<le> \<sigma>"
    and A: "smaj x0 r \<sigma> c1 F K1" and B: "smaj x0 r \<sigma> c2 G K2"
    and K1nn: "0 \<le> K1" and K2nn: "0 \<le> K2"
  shows "smaj x0 r \<sigma> (ccauchy c1 c2) (\<lambda>x. F x * G x) (K1 * K2)"
  unfolding smaj_def
proof
  show "series_on x0 r (ccauchy c1 c2) (\<lambda>x. F x * G x)"
    using A B by (auto simp: smaj_def intro: series_on_mult)
  show "majle \<sigma> (ccauchy c1 c2) (K1 * K2)"
    using A B by (auto simp: smaj_def intro: majle_ccauchy[OF s0 _ _ K1nn K2nn])
qed

lemma smaj_pow:
  assumes s0: "0 \<le> \<sigma>"
    and A: "smaj x0 r \<sigma> c F K" and Knn: "0 \<le> K"
  shows "smaj x0 r \<sigma> (cpow c n) (\<lambda>x. (F x) ^ n) (K ^ n)"
  unfolding smaj_def
proof
  show "series_on x0 r (cpow c n) (\<lambda>x. (F x) ^ n)"
    using A by (auto simp: smaj_def intro: series_on_power)
  show "majle \<sigma> (cpow c n) (K ^ n)"
    using A by (auto simp: smaj_def intro: majle_cpow[OF s0 _ Knn])
qed

text \<open>Finite product, carrying both the series and a product majle bound.\<close>

lemma smaj_prod:
  fixes F :: "'i \<Rightarrow> 'a::euclidean_space \<Rightarrow> real"
  assumes s0: "0 \<le> \<sigma>" and fin: "finite I"
    and per: "\<And>i. i \<in> I \<Longrightarrow> \<exists>c. smaj x0 r \<sigma> c (F i) (K i)"
    and Knn: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> K i"
  shows "\<exists>cc. smaj x0 r \<sigma> cc (\<lambda>x. \<Prod>i\<in>I. F i x) (\<Prod>i\<in>I. K i)"
  using fin per Knn
proof (induction I rule: finite_induct)
  case empty
  have "smaj x0 r \<sigma> cone (\<lambda>x. \<Prod>i\<in>{}. F i x) (\<Prod>i\<in>{}. K i)"
    using smaj_one[OF s0] by simp
  thus ?case by blast
next
  case (insert j I)
  obtain cj where cj: "smaj x0 r \<sigma> cj (F j) (K j)" using insert.prems(1)[of j] by blast
  obtain crest where crest: "smaj x0 r \<sigma> crest (\<lambda>x. \<Prod>i\<in>I. F i x) (\<Prod>i\<in>I. K i)"
    using insert.prems insert.IH by blast
  have Kjnn: "0 \<le> K j" using insert.prems(2)[of j] by simp
  have Krestnn: "0 \<le> (\<Prod>i\<in>I. K i)" using insert.prems(2) by (intro prod_nonneg) auto
  have "smaj x0 r \<sigma> (ccauchy cj crest) (\<lambda>x. F j x * (\<Prod>i\<in>I. F i x)) (K j * (\<Prod>i\<in>I. K i))"
    by (rule smaj_mult[OF s0 cj crest Kjnn Krestnn])
  hence "smaj x0 r \<sigma> (ccauchy cj crest) (\<lambda>x. \<Prod>i\<in>insert j I. F i x) (\<Prod>i\<in>insert j I. K i)"
    using insert.hyps by simp
  thus ?case by blast
qed

lemma majle_mono:
  assumes "majle \<sigma> c K" and "K \<le> K'"
  shows "majle \<sigma> c K'"
  using assms by (simp add: majle_def)

lemma smaj_relax:
  assumes "smaj x0 r \<sigma> c F K" and "K \<le> K'"
  shows "smaj x0 r \<sigma> c F K'"
  using assms majle_mono by (auto simp: smaj_def)

text \<open>Product of a base raised to multi-index entries, dominated by a common base
  raised to the total degree.\<close>

lemma prod_pow_le_deg:
  fixes Kb :: "'a::euclidean_space \<Rightarrow> real"
  assumes nn: "\<And>b. b \<in> Basis \<Longrightarrow> 0 \<le> Kb b"
    and le: "\<And>b. b \<in> Basis \<Longrightarrow> Kb b \<le> Kf"
  shows "(\<Prod>b\<in>Basis. (Kb b) ^ (\<beta> b)) \<le> Kf ^ ra_deg \<beta>"
proof -
  have "(\<Prod>b\<in>(Basis::'a set). (Kb b) ^ (\<beta> b)) \<le> (\<Prod>b\<in>(Basis::'a set). Kf ^ (\<beta> b))"
  proof (rule prod_mono)
    fix b assume b: "b \<in> (Basis::'a set)"
    have "0 \<le> (Kb b) ^ (\<beta> b)" using nn[OF b] by simp
    moreover have "(Kb b) ^ (\<beta> b) \<le> Kf ^ (\<beta> b)"
      by (rule power_mono[OF le[OF b] nn[OF b]])
    ultimately show "0 \<le> (Kb b) ^ (\<beta> b) \<and> (Kb b) ^ (\<beta> b) \<le> Kf ^ (\<beta> b)" by simp
  qed
  also have "(\<Prod>b\<in>(Basis::'a set). Kf ^ (\<beta> b)) = Kf ^ ra_deg \<beta>"
    by (rule prod_const_ra_deg)
  finally show ?thesis .
qed

text \<open>The combined monomial-compose: a coefficient family for
  \<open>x \<mapsto> ra_monomial (f x - z) \<beta>\<close> together with a majle bound \<open>Kf ^ ra_deg \<beta>\<close>,
  uniform in \<open>\<beta>\<close>, derived from a single per-component majle constant.\<close>

lemma smaj_ra_monomial_compose:
  fixes cf :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::euclidean_space"
  assumes s0: "0 \<le> \<sigma>"
    and HS: "\<And>x. dist x x0 < r \<Longrightarrow>
              ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cf \<alpha>) has_sum f x) ra_idx"
    and cfmaj: "majle \<sigma> (\<lambda>\<alpha>. norm (cf \<alpha>)) Mc"
    and Kf_ge: "\<And>b. b \<in> Basis \<Longrightarrow> Mc + \<bar>z \<bullet> b\<bar> \<le> Kf"
    and Kf_nn: "0 \<le> Kf"
  shows "\<exists>cc. smaj x0 r \<sigma> cc (\<lambda>x. ra_monomial (f x - z) \<beta>) (Kf ^ ra_deg \<beta>)"
proof -
  define Kb where "Kb = (\<lambda>b. Mc + \<bar>z \<bullet> b\<bar>)"
  have Mc_nn: "0 \<le> Mc" using majle_imp_nonneg_sum[OF s0 cfmaj] cfmaj by (simp add: majle_def)
  have Kbnn: "0 \<le> Kb b" for b using Mc_nn by (simp add: Kb_def)
  have Kble: "Kb b \<le> Kf" if "b \<in> Basis" for b using Kf_ge[OF that] by (simp add: Kb_def)
  \<comment> \<open>per-component smaj for \<open>(f x - z) \<bullet> b\<close>\<close>
  have comp: "smaj x0 r \<sigma> (\<lambda>\<alpha>. (cf \<alpha> \<bullet> b) - (z \<bullet> b) * cone \<alpha>)
                 (\<lambda>x. (f x - z) \<bullet> b) (Kb b)" if b: "b \<in> Basis" for b
    unfolding smaj_def
  proof
    have s1: "series_on x0 r (\<lambda>\<alpha>. cf \<alpha> \<bullet> b) (\<lambda>x. f x \<bullet> b)"
      by (rule series_on_component[OF HS])
    have s2: "series_on x0 r (\<lambda>\<alpha>. (z \<bullet> b) * cone \<alpha>) (\<lambda>_. z \<bullet> b)"
      by (rule series_on_const)
    have "series_on x0 r (\<lambda>\<alpha>. (cf \<alpha> \<bullet> b) - (z \<bullet> b) * cone \<alpha>) (\<lambda>x. (f x \<bullet> b) - (z \<bullet> b))"
      by (rule series_on_diff[OF s1 s2])
    thus "series_on x0 r (\<lambda>\<alpha>. (cf \<alpha> \<bullet> b) - (z \<bullet> b) * cone \<alpha>) (\<lambda>x. (f x - z) \<bullet> b)"
      by (simp only: inner_diff_left)
  next
    have comp_dom: "\<bar>cf \<alpha> \<bullet> b\<bar> \<le> \<bar>norm (cf \<alpha>)\<bar>" if "\<alpha>\<in>ra_idx" for \<alpha>
    proof -
      have "\<bar>cf \<alpha> \<bullet> b\<bar> \<le> norm (cf \<alpha>) * norm b"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> = norm (cf \<alpha>)" using b by simp
      finally show ?thesis by simp
    qed
    have m1: "majle \<sigma> (\<lambda>\<alpha>. cf \<alpha> \<bullet> b) Mc"
      by (rule majle_dom[OF s0 comp_dom cfmaj])
    have m2: "majle \<sigma> (\<lambda>\<alpha>. (z \<bullet> b) * cone \<alpha>) (\<bar>z \<bullet> b\<bar> * 1)"
      by (rule majle_cmul[OF s0 majle_one[OF s0]])
    have m2': "majle \<sigma> (\<lambda>\<alpha>. (z \<bullet> b) * cone \<alpha>) (\<bar>z \<bullet> b\<bar>)" using m2 by simp
    have m2neg: "majle \<sigma> (\<lambda>\<alpha>. - ((z \<bullet> b) * cone \<alpha>)) (\<bar>z \<bullet> b\<bar>)"
    proof -
      have "majle \<sigma> (\<lambda>\<alpha>. (-1) * ((z \<bullet> b) * cone \<alpha>)) (\<bar>-1::real\<bar> * \<bar>z \<bullet> b\<bar>)"
        by (rule majle_cmul[OF s0 m2'])
      thus ?thesis by simp
    qed
    have "majle \<sigma> (\<lambda>\<alpha>. (cf \<alpha> \<bullet> b) + (- ((z \<bullet> b) * cone \<alpha>))) (Mc + \<bar>z \<bullet> b\<bar>)"
      by (rule majle_add[OF s0 m1 m2neg])
    thus "majle \<sigma> (\<lambda>\<alpha>. (cf \<alpha> \<bullet> b) - (z \<bullet> b) * cone \<alpha>) (Kb b)"
      by (simp add: Kb_def)
  qed
  have comppow: "\<exists>c. smaj x0 r \<sigma> c (\<lambda>x. ((f x - z) \<bullet> b) ^ (\<beta> b)) (Kb b ^ (\<beta> b))"
    if b: "b \<in> Basis" for b
    using smaj_pow[OF s0 comp[OF b] Kbnn] by blast
  have "\<exists>cc. smaj x0 r \<sigma> cc (\<lambda>x. \<Prod>b\<in>Basis. ((f x - z) \<bullet> b) ^ (\<beta> b))
              (\<Prod>b\<in>Basis. Kb b ^ (\<beta> b))"
    by (rule smaj_prod[OF s0 finite_Basis])
       (use comppow Kbnn in \<open>auto intro: zero_le_power\<close>)
  then obtain cc where cc: "smaj x0 r \<sigma> cc (\<lambda>x. \<Prod>b\<in>Basis. ((f x - z) \<bullet> b) ^ (\<beta> b))
              (\<Prod>b\<in>Basis. Kb b ^ (\<beta> b))" by blast
  have prodle: "(\<Prod>b\<in>Basis. Kb b ^ (\<beta> b)) \<le> Kf ^ ra_deg \<beta>"
    by (rule prod_pow_le_deg[OF Kbnn Kble])
  have "smaj x0 r \<sigma> cc (\<lambda>x. \<Prod>b\<in>Basis. ((f x - z) \<bullet> b) ^ (\<beta> b)) (Kf ^ ra_deg \<beta>)"
    by (rule smaj_relax[OF cc prodle])
  hence "smaj x0 r \<sigma> cc (\<lambda>x. ra_monomial (f x - z) \<beta>) (Kf ^ ra_deg \<beta>)"
    by (simp only: ra_monomial_def)
  thus ?thesis by blast
qed

subsection \<open>Step (c): composition\<close>

text \<open>Vector-valued continuity of an analytic function, obtained componentwise from
  the scalar continuity lemma.\<close>

lemma real_analytic_on_imp_continuous_vec:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ana: "real_analytic_on f U" and xU: "x0 \<in> U"
  shows "continuous (at x0) f"
proof (subst continuous_componentwise, intro ballI)
  fix b :: 'b assume b: "b \<in> Basis"
  have "real_analytic_on (\<lambda>x. f x \<bullet> b) U"
    by (rule real_analytic_on_inner_component[OF ana])
  thus "continuous (at x0) (\<lambda>x. f x \<bullet> b)"
    by (rule real_analytic_on_imp_continuous[OF _ xU])
qed

text \<open>Only \<open>czero_idx\<close> has degree zero among the multi-indices.\<close>

lemma ra_deg_eq0_iff:
  fixes \<alpha> :: "'a::euclidean_space \<Rightarrow> nat"
  assumes "\<alpha> \<in> ra_idx"
  shows "ra_deg \<alpha> = 0 \<longleftrightarrow> \<alpha> = czero_idx"
proof
  assume d0: "ra_deg \<alpha> = 0"
  have z: "\<alpha> b = 0" if "b \<in> Basis" for b
  proof -
    have "\<alpha> b \<le> (\<Sum>c\<in>Basis. \<alpha> c)" using that by (intro member_le_sum) auto
    also have "\<dots> = 0" using d0 by (simp add: ra_deg_def)
    finally show ?thesis by simp
  qed
  show "\<alpha> = czero_idx"
  proof (rule ext)
    fix b show "\<alpha> b = czero_idx b"
    proof (cases "b \<in> Basis")
      case True thus ?thesis using z by (simp add: czero_idx_def)
    next
      case False thus ?thesis using assms by (auto simp: ra_idx_def czero_idx_def)
    qed
  qed
next
  assume "\<alpha> = czero_idx"
  thus "ra_deg \<alpha> = 0" by (simp add: ra_deg_def czero_idx_def)
qed

lemma ra_series_at_zero_coeff:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes hs: "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R c \<alpha>) has_sum v) ra_idx"
  shows "c czero_idx = v"
proof -
  have neutral: "ra_monomial (0::'a) \<alpha> *\<^sub>R c \<alpha> = 0"
    if "\<alpha> \<in> ra_idx - {czero_idx}" for \<alpha>
  proof -
    have "\<alpha> \<noteq> czero_idx"
      using that by simp
    hence "ra_deg \<alpha> \<noteq> 0"
      using ra_deg_eq0_iff that by auto
    thus ?thesis
      by (simp add: ra_monomial_zero)
  qed
  have "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R c \<alpha>) has_sum v) ra_idx
          = ((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R c \<alpha>) has_sum v) {czero_idx}"
    by (rule has_sum_cong_neutral) (use neutral czero_idx_in in auto)
  with hs have hs1:
    "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R c \<alpha>) has_sum v) {czero_idx}"
    by simp
  moreover have "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R c \<alpha>) has_sum c czero_idx) {czero_idx}"
    by (rule has_sum_finiteI) (auto simp: ra_monomial_zero czero_idx_def ra_deg_def)
  ultimately show ?thesis
    by (metis has_sum_unique)
qed

lemma ra_dcoeff_czero_basis:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes b: "b \<in> Basis"
  shows "ra_dcoeff c b czero_idx = c (\<lambda>x. if x = b then 1 else 0)"
proof -
  define e :: "'a \<Rightarrow> nat" where "e = (\<lambda>x. if x = b then 1 else 0)"
  have inc_b: "ra_inc czero_idx b = e"
    by (rule ext) (simp add: ra_inc_def czero_idx_def e_def)
  have rest0:
    "(\<Sum>x\<in>Basis - {b}.
        (real (Suc (czero_idx x)) * (b \<bullet> x)) *\<^sub>R c (ra_inc czero_idx x)) = 0"
    by (rule sum.neutral) (use b in \<open>auto simp: inner_Basis\<close>)
  have "ra_dcoeff c b czero_idx =
      (real (Suc (czero_idx b)) * (b \<bullet> b)) *\<^sub>R c (ra_inc czero_idx b)
        + (\<Sum>x\<in>Basis - {b}.
            (real (Suc (czero_idx x)) * (b \<bullet> x)) *\<^sub>R c (ra_inc czero_idx x))"
    using b
    by (simp add: ra_dcoeff_def sum.remove[OF finite_Basis b])
  also have "\<dots> = c (ra_inc czero_idx b)"
    using b rest0 by (simp add: czero_idx_def inner_Basis)
  also have "\<dots> = c e"
    by (simp add: inc_b)
  finally show ?thesis
    by (simp add: e_def)
qed

lemma ra_dcoeff_czero_eq_frechet_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b"
  assumes r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f y) ra_idx"
  shows "ra_dcoeff c v czero_idx = frechet_derivative f (at x0) v"
proof -
  have hs: "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R ra_dcoeff c v \<alpha>)
              has_sum frechet_derivative f (at x0) v) ra_idx"
    using ra_directional_derivative_series[OF r series, of x0 v] r
    by simp
  show ?thesis
    by (rule ra_series_at_zero_coeff[OF hs])
qed

lemma ra_linear_coeff_eq_frechet_derivative_basis:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
    and c :: "('a \<Rightarrow> nat) \<Rightarrow> 'b"
  assumes b: "b \<in> Basis"
    and r: "0 < r"
    and series:
      "\<And>y. dist y x0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (y - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f y) ra_idx"
  shows "c (\<lambda>x. if x = b then 1 else 0) = frechet_derivative f (at x0) b"
  using ra_dcoeff_czero_eq_frechet_derivative[OF r series, of b]
        ra_dcoeff_czero_basis[OF b, of c]
  by simp

lemma infsum_split_off:
  fixes f :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes sf: "f summable_on ra_idx" and aA: "a \<in> ra_idx"
  shows "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. f \<alpha>) = f a + (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx - {a}). f \<alpha>)"
proof -
  have nin: "a \<notin> ra_idx - {a}" by simp
  have sub: "f summable_on (ra_idx - {a})"
    by (rule summable_on_subset_banach[OF sf]) auto
  have ins: "insert a (ra_idx - {a}) = ra_idx" using aA by blast
  have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>insert a (ra_idx - {a}). f \<alpha>)
          = f a + (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx - {a}). f \<alpha>)"
    by (rule infsum_insert[OF sub nin])
  thus ?thesis by (simp only: ins)
qed

text \<open>The geometric tail (all nonzero indices) is linearly small in the ratio.\<close>

lemma geom_idx_tail_small:
  fixes q q0 :: real
  assumes q0: "0 \<le> q" and qq0: "q \<le> q0" and q0pos: "0 < q0" and q01: "q0 < 1"
  shows "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a::euclidean_space\<Rightarrow>nat) set). q ^ ra_deg \<alpha>) - 1
           \<le> (q / q0) * (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). q0 ^ ra_deg \<alpha>)"
proof -
  have q0nn: "0 \<le> q0" using q0pos by simp
  have sq: "(\<lambda>\<alpha>::'a\<Rightarrow>nat. q ^ ra_deg \<alpha>) summable_on ra_idx"
    by (rule geom_idx_summable[OF q0 _]) (use qq0 q01 in linarith)
  have sq0: "(\<lambda>\<alpha>::'a\<Rightarrow>nat. q0 ^ ra_deg \<alpha>) summable_on ra_idx"
    by (rule geom_idx_summable[OF q0nn q01])

  \<comment> \<open>split off the single zero-degree term\<close>
  have czin: "(czero_idx::'a\<Rightarrow>nat) \<in> ra_idx"
    by (rule czero_idx_in)

  have srest_q': "(\<lambda>\<alpha>::'a\<Rightarrow>nat. q ^ ra_deg \<alpha>) summable_on (ra_idx - {czero_idx})"
    by (rule summable_on_subset_banach[OF sq]) auto

  have rest_eq:
    "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). q ^ ra_deg \<alpha>)
      = q ^ ra_deg (czero_idx::'a\<Rightarrow>nat)
        + (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q ^ ra_deg \<alpha>)"
    by (rule infsum_split_off[OF sq czin])

  have ztermq: "q ^ ra_deg (czero_idx::'a\<Rightarrow>nat) = 1"
    by (simp add: ra_deg_def czero_idx_def)

  have srest_q:
    "(\<lambda>\<alpha>::'a\<Rightarrow>nat. q ^ ra_deg \<alpha>)
      summable_on ((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)})"
    by (rule summable_on_subset_banach[OF sq]) auto

  have srest_q0:
    "(\<lambda>\<alpha>::'a\<Rightarrow>nat. q0 ^ ra_deg \<alpha>)
      summable_on ((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)})"
    by (rule summable_on_subset_banach[OF sq0]) auto

  have srest_q0scaled:
    "(\<lambda>\<alpha>::'a\<Rightarrow>nat. (q / q0) * q0 ^ ra_deg \<alpha>)
      summable_on ((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)})"
    by (rule summable_on_cmult_right[OF srest_q0])

  have ptw:
    "q ^ ra_deg \<alpha> \<le> (q / q0) * q0 ^ ra_deg \<alpha>"
    if a: "\<alpha> \<in> ((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)})"
    for \<alpha> :: "'a\<Rightarrow>nat"
  proof -
    have ar: "\<alpha> \<in> ra_idx" and anz: "\<alpha> \<noteq> czero_idx"
      using a by auto
    have deg1: "1 \<le> ra_deg \<alpha>"
      using ra_deg_eq0_iff[OF ar] anz
      by (cases "ra_deg \<alpha>") auto

    have "q ^ ra_deg \<alpha> = (q / q0) ^ ra_deg \<alpha> * q0 ^ ra_deg \<alpha>"
      using q0pos by (simp add: power_divide)
    also have "\<dots> \<le> (q / q0) ^ 1 * q0 ^ ra_deg \<alpha>"
    proof (rule mult_right_mono)
      have rn: "0 \<le> q / q0"
        using q0 q0pos by simp
      have r1: "q / q0 \<le> 1"
        using qq0 q0pos by (simp add: divide_le_eq)
      show "(q / q0) ^ ra_deg \<alpha> \<le> (q / q0) ^ 1"
        by (rule power_decreasing[OF deg1 rn r1])
      show "0 \<le> q0 ^ ra_deg \<alpha>"
        using q0nn by simp
    qed
    finally show ?thesis by simp
  qed

  have rest_q_le_scaled_rest_q0:
    "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q ^ ra_deg \<alpha>)
      \<le> (q / q0) *
          (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q0 ^ ra_deg \<alpha>)"
  proof -
    have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q ^ ra_deg \<alpha>)
        \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}).
              (q / q0) * q0 ^ ra_deg \<alpha>)"
      by (rule infsum_mono[OF srest_q srest_q0scaled]) (use ptw in auto)
    also have "\<dots> =
        (q / q0) *
          (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q0 ^ ra_deg \<alpha>)"
      by (rule infsum_cmult_right[OF srest_q0])
    finally show ?thesis .
  qed

  have rest_q0_le_all:
    "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q0 ^ ra_deg \<alpha>)
      \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). q0 ^ ra_deg \<alpha>)"
  proof -
    have rest_eq0:
      "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). q0 ^ ra_deg \<alpha>)
        = q0 ^ ra_deg (czero_idx::'a\<Rightarrow>nat)
          + (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q0 ^ ra_deg \<alpha>)"
      by (rule infsum_split_off[OF sq0 czin])
    have ztermq0: "q0 ^ ra_deg (czero_idx::'a\<Rightarrow>nat) = 1"
      by (simp add: ra_deg_def czero_idx_def)
    show ?thesis
      using rest_eq0 ztermq0 by linarith
  qed

  have key:
    "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q ^ ra_deg \<alpha>)
      \<le> (q / q0) * (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). q0 ^ ra_deg \<alpha>)"
  proof -
    have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q ^ ra_deg \<alpha>)
      \<le> (q / q0) *
          (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q0 ^ ra_deg \<alpha>)"
      by (rule rest_q_le_scaled_rest_q0)
    also have "\<dots> \<le> (q / q0) *
          (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). q0 ^ ra_deg \<alpha>)"
      by (rule mult_left_mono[OF rest_q0_le_all]) (use q0 q0pos in simp)
    finally show ?thesis .
  qed

  have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). q ^ ra_deg \<alpha>) - 1
        = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('a\<Rightarrow>nat) set) - {(czero_idx::'a\<Rightarrow>nat)}). q ^ ra_deg \<alpha>)"
    using rest_eq ztermq by linarith
  also note key
  finally show ?thesis .
qed

subsection \<open>Step (c): dominated Fubini sum of series families\<close>

text \<open>Monomial absolute bound by the majle parameter on the working ball.\<close>

lemma ra_monomial_abs_le_pow:
  fixes h :: "'a::euclidean_space" and \<sigma> :: real
  assumes a: "\<gamma> \<in> ra_idx" and hle: "norm h \<le> \<sigma>"
  shows "\<bar>ra_monomial h \<gamma>\<bar> \<le> \<sigma> ^ ra_deg \<gamma>"
proof -
  have "\<bar>ra_monomial h \<gamma>\<bar> \<le> norm h ^ ra_deg \<gamma>"
    by (rule ra_monomial_norm_le[OF a])
  also have "\<dots> \<le> \<sigma> ^ ra_deg \<gamma>"
    by (rule power_mono[OF hle]) simp
  finally show ?thesis .
qed

text \<open>The genuinely hard lemma: a majle-dominated infinite sum of \<open>series_on\<close>
  families is again a \<open>series_on\<close> family, with explicit coefficient family
  \<open>\<lambda>\<gamma>. \<Sum>\<^sub>\<beta> a \<beta> * CC \<beta> \<gamma>\<close>.  The value of the \<open>\<beta>\<close>-sum is supplied as \<open>G\<close>.\<close>

lemma series_on_majdom:
  fixes CC :: "('b::euclidean_space \<Rightarrow> nat) \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
    and Fn :: "('b \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> real"
    and a  :: "('b \<Rightarrow> nat) \<Rightarrow> real"
    and Kk :: "('b \<Rightarrow> nat) \<Rightarrow> real"
  assumes s0: "0 < \<sigma>" and r\<sigma>: "r \<le> \<sigma>"
    and ser: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> series_on x0 r (CC \<beta>) (Fn \<beta>)"
    and maj: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> majle \<sigma> (CC \<beta>) (Kk \<beta>)"
    and gsum: "(\<lambda>\<beta>. \<bar>a \<beta>\<bar> * Kk \<beta>) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    and Gval: "\<And>x. dist x x0 < r \<Longrightarrow> ((\<lambda>\<beta>. a \<beta> *\<^sub>R Fn \<beta> x) has_sum G x) (ra_idx::('b\<Rightarrow>nat) set)"
  shows "series_on x0 r (\<lambda>\<gamma>. \<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). a \<beta> * CC \<beta> \<gamma>) G"
  unfolding series_on_def
proof (intro allI impI)
  fix x :: 'a assume d: "dist x x0 < r"
  define h where "h = x - x0"
  have hle: "norm h \<le> \<sigma>"
  proof -
    have "norm h < r" using d by (simp add: h_def dist_norm)
    thus ?thesis using r\<sigma> by simp
  qed
  define D where "D = (\<lambda>(\<beta>,\<gamma>). ra_monomial h \<gamma> * (a \<beta> * CC \<beta> \<gamma>))"
  \<comment> \<open>per-\<open>\<beta>\<close> facts\<close>
  have ser\<beta>: "((\<lambda>\<gamma>. ra_monomial h \<gamma> * CC \<beta> \<gamma>) has_sum Fn \<beta> x) (ra_idx::('a\<Rightarrow>nat) set)"
    if b: "\<beta> \<in> ra_idx" for \<beta>
    using ser[OF b] d unfolding series_on_def h_def by simp
  have maj\<beta>sum: "mfam \<sigma> (CC \<beta>) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
    if b: "\<beta> \<in> ra_idx" for \<beta>
    using maj[OF b] by (simp add: majle_def)
  have maj\<beta>le: "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). mfam \<sigma> (CC \<beta>) \<gamma>) \<le> Kk \<beta>"
    if b: "\<beta> \<in> ra_idx" for \<beta>
    using maj[OF b] by (simp add: majle_def)
  \<comment> \<open>pointwise domination of the double family\<close>
  have Dbound: "\<bar>D (\<beta>,\<gamma>)\<bar> \<le> \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>"
    if b: "\<beta> \<in> ra_idx" and g: "\<gamma> \<in> ra_idx" for \<beta> \<gamma>
  proof -
    have "\<bar>D (\<beta>,\<gamma>)\<bar> = \<bar>ra_monomial h \<gamma>\<bar> * (\<bar>a \<beta>\<bar> * \<bar>CC \<beta> \<gamma>\<bar>)"
      by (simp add: D_def abs_mult)
    also have "\<dots> \<le> (\<sigma> ^ ra_deg \<gamma>) * (\<bar>a \<beta>\<bar> * \<bar>CC \<beta> \<gamma>\<bar>)"
      by (rule mult_right_mono[OF ra_monomial_abs_le_pow[OF g hle]]) simp
    also have "\<dots> = \<bar>a \<beta>\<bar> * (\<bar>CC \<beta> \<gamma>\<bar> * \<sigma> ^ ra_deg \<gamma>)"
      by (simp add: mult.assoc mult.left_commute)
    also have "\<dots> = \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>" by (simp add: mfam_def)
    finally show ?thesis .
  qed
  \<comment> \<open>inner abs-summability (over \<open>\<gamma>\<close>) for each \<open>\<beta>\<close>\<close>
  have inner_abs: "(\<lambda>\<gamma>. norm (D (\<beta>,\<gamma>))) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
    if b: "\<beta> \<in> ra_idx" for \<beta>
  proof (rule summable_on_comparison_test[where f = "\<lambda>\<gamma>. \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>"])
    show "(\<lambda>\<gamma>. \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
      by (rule summable_on_cmult_right[OF maj\<beta>sum[OF b]])
  next
    fix \<gamma> :: "'a\<Rightarrow>nat" assume g: "\<gamma> \<in> ra_idx"
    have "norm (D (\<beta>,\<gamma>)) = \<bar>D (\<beta>,\<gamma>)\<bar>" by simp
    also have "\<dots> \<le> \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>" by (rule Dbound[OF b g])
    finally show "norm (D (\<beta>,\<gamma>)) \<le> \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>" .
  next
    fix \<gamma> :: "'a\<Rightarrow>nat" assume "\<gamma> \<in> ra_idx"
    show "0 \<le> norm (D (\<beta>,\<gamma>))" by simp
  qed
  \<comment> \<open>inner total bounded by the g-majorant term\<close>
  have inner_tot_le: "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))) \<le> \<bar>a \<beta>\<bar> * Kk \<beta>"
    if b: "\<beta> \<in> ra_idx" for \<beta>
  proof -
    have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))
            \<le> (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>)"
    proof (rule infsum_mono)
      show "(\<lambda>\<gamma>. norm (D (\<beta>,\<gamma>))) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
        by (rule inner_abs[OF b])
      show "(\<lambda>\<gamma>. \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
        by (rule summable_on_cmult_right[OF maj\<beta>sum[OF b]])
      fix \<gamma> :: "'a\<Rightarrow>nat" assume g: "\<gamma> \<in> ra_idx"
      have "norm (D (\<beta>,\<gamma>)) = \<bar>D (\<beta>,\<gamma>)\<bar>" by simp
      thus "norm (D (\<beta>,\<gamma>)) \<le> \<bar>a \<beta>\<bar> * mfam \<sigma> (CC \<beta>) \<gamma>"
        using Dbound[OF b g] by simp
    qed
    also have "\<dots> = \<bar>a \<beta>\<bar> * (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). mfam \<sigma> (CC \<beta>) \<gamma>)"
      by (rule infsum_cmult_right[OF maj\<beta>sum[OF b]])
    also have "\<dots> \<le> \<bar>a \<beta>\<bar> * Kk \<beta>"
      by (rule mult_left_mono[OF maj\<beta>le[OF b]]) simp
    finally show ?thesis .
  qed
  \<comment> \<open>outer abs-summability of the inner totals\<close>
  have outer_abs: "(\<lambda>\<beta>. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))
                     summable_on (ra_idx::('b\<Rightarrow>nat) set)"
  proof (rule summable_on_comparison_test[where f = "\<lambda>\<beta>. \<bar>a \<beta>\<bar> * Kk \<beta>"])
    show "(\<lambda>\<beta>. \<bar>a \<beta>\<bar> * Kk \<beta>) summable_on (ra_idx::('b\<Rightarrow>nat) set)" by (rule gsum)
  next
    fix \<beta> :: "'b\<Rightarrow>nat" assume b: "\<beta> \<in> ra_idx"
    show "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))) \<le> \<bar>a \<beta>\<bar> * Kk \<beta>"
      by (rule inner_tot_le[OF b])
  next
    fix \<beta> :: "'b\<Rightarrow>nat" assume "\<beta> \<in> ra_idx"
    show "0 \<le> (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))"
      by (rule infsum_nonneg) simp
  qed
  have outer_abs': "(\<lambda>\<beta>. norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))))
                      summable_on (ra_idx::('b\<Rightarrow>nat) set)"
  proof -
    have eq: "(\<lambda>\<beta>. norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))))
                = (\<lambda>\<beta>. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))"
    proof (rule ext)
      fix \<beta> :: "'b\<Rightarrow>nat"
      have "0 \<le> (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))"
        by (rule infsum_nonneg) simp
      thus "norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))
              = (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))" by simp
    qed
    show ?thesis using outer_abs by (simp only: eq)
  qed
  have conj1: "\<forall>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). (\<lambda>\<gamma>. norm (D (\<beta>,\<gamma>))) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
    using inner_abs by blast
  have conj2: "(\<lambda>\<beta>. norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))))
                 summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    by (rule outer_abs')
  \<comment> \<open>the double family is absolutely summable on the product\<close>
  have Dabs: "(\<lambda>z. norm (D z)) summable_on (Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set))"
    by (rule Infinite_Sum.abs_summable_on_Sigma_iff
          [where f = D and A = "ra_idx::('b\<Rightarrow>nat) set" and B = "\<lambda>_. ra_idx::('a\<Rightarrow>nat) set",
           THEN iffD2, OF conjI[OF conj1 conj2]])
  have Dsumm: "D summable_on (Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set))"
    by (rule abs_summable_summable[OF Dabs])
  \<comment> \<open>sum the double family \<open>\<gamma>\<close>-first: total \<open>= G x\<close>\<close>
  have GhsB: "((\<lambda>\<beta>. a \<beta> *\<^sub>R Fn \<beta> x) has_sum G x) (ra_idx::('b\<Rightarrow>nat) set)"
    by (rule Gval[OF d])
  have innerB: "((\<lambda>\<gamma>. D (\<beta>,\<gamma>)) has_sum (a \<beta> *\<^sub>R Fn \<beta> x)) (ra_idx::('a\<Rightarrow>nat) set)"
    if b: "\<beta> \<in> ra_idx" for \<beta>
  proof -
    have "((\<lambda>\<gamma>. a \<beta> * (ra_monomial h \<gamma> * CC \<beta> \<gamma>)) has_sum (a \<beta> * Fn \<beta> x))
            (ra_idx::('a\<Rightarrow>nat) set)"
      by (rule has_sum_cmult_right[OF ser\<beta>[OF b]])
    thus ?thesis
      by (simp add: D_def mult.assoc mult.left_commute)
  qed
  have DhsG: "(D has_sum G x) (Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set))"
  proof (rule has_sum_SigmaI[where g = "\<lambda>\<beta>. a \<beta> *\<^sub>R Fn \<beta> x"])
    fix \<beta> :: "'b\<Rightarrow>nat" assume b: "\<beta> \<in> ra_idx"
    show "((\<lambda>\<gamma>. D (\<beta>,\<gamma>)) has_sum (a \<beta> *\<^sub>R Fn \<beta> x)) (ra_idx::('a\<Rightarrow>nat) set)"
      by (rule innerB[OF b])
  next
    show "((\<lambda>\<beta>. a \<beta> *\<^sub>R Fn \<beta> x) has_sum G x) (ra_idx::('b\<Rightarrow>nat) set)" by (rule GhsB)
  next
    show "D summable_on (Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set))"
      by (rule Dsumm)
  qed
  \<comment> \<open>swap to \<open>\<gamma>\<close>-outer\<close>
  have Dswap: "((\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) has_sum G x)
                 ((ra_idx::('a\<Rightarrow>nat) set) \<times> (ra_idx::('b\<Rightarrow>nat) set))"
  proof -
    have e1: "Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set)
                = (ra_idx::('b\<Rightarrow>nat) set) \<times> (ra_idx::('a\<Rightarrow>nat) set)"
      by simp
    have "(D has_sum G x) ((ra_idx::('b\<Rightarrow>nat) set) \<times> (ra_idx::('a\<Rightarrow>nat) set))"
      using DhsG e1 by simp
    thus ?thesis by (subst has_sum_swap) simp
  qed
  \<comment> \<open>summability of each inner \<open>\<beta>\<close>-slice on the swapped Sigma\<close>
  have Dswap_summ: "(\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) summable_on
                      (Sigma (ra_idx::('a\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('b\<Rightarrow>nat) set))"
    using Dswap has_sum_imp_summable by (simp add: Sigma_def)
  have slice_summ: "(\<lambda>\<beta>. D (\<beta>,\<gamma>)) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    if g: "\<gamma> \<in> ra_idx" for \<gamma>
  proof -
    have "(\<lambda>\<beta>. (\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) (\<gamma>,\<beta>)) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
      by (rule summable_on_SigmaD1[OF _ g]) (use Dswap_summ in \<open>simp add: case_prod_unfold\<close>)
    thus ?thesis by simp
  qed
  \<comment> \<open>identify the inner \<open>\<beta>\<close>-sum and conclude\<close>
  define Cc where "Cc = (\<lambda>\<gamma>. \<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). a \<beta> * CC \<beta> \<gamma>)"
  have inner\<gamma>: "((\<lambda>\<beta>. D (\<beta>,\<gamma>)) has_sum (ra_monomial h \<gamma> *\<^sub>R Cc \<gamma>)) (ra_idx::('b\<Rightarrow>nat) set)"
    if g: "\<gamma> \<in> ra_idx" for \<gamma>
  proof -
    have summabs: "(\<lambda>\<beta>. norm (a \<beta> * CC \<beta> \<gamma>)) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    proof (rule summable_on_comparison_test
             [where f = "\<lambda>\<beta>. (1 / \<sigma> ^ ra_deg \<gamma>) * (\<bar>a \<beta>\<bar> * Kk \<beta>)"])
      show "(\<lambda>\<beta>. (1 / \<sigma> ^ ra_deg \<gamma>) * (\<bar>a \<beta>\<bar> * Kk \<beta>)) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
        by (rule summable_on_cmult_right[OF gsum])
    next
      fix \<beta> :: "'b\<Rightarrow>nat" assume "\<beta> \<in> ra_idx"
      show "0 \<le> norm (a \<beta> * CC \<beta> \<gamma>)" by simp
    next
      fix \<beta> :: "'b\<Rightarrow>nat" assume b: "\<beta> \<in> ra_idx"
      have sp: "0 < \<sigma> ^ ra_deg \<gamma>" using s0 by simp
      have one_term: "\<bar>CC \<beta> \<gamma>\<bar> * \<sigma> ^ ra_deg \<gamma> \<le> Kk \<beta>"
      proof -
        have "\<bar>CC \<beta> \<gamma>\<bar> * \<sigma> ^ ra_deg \<gamma> = mfam \<sigma> (CC \<beta>) \<gamma>" by (simp add: mfam_def)
        also have "\<dots> = (\<Sum>\<gamma>'\<in>{\<gamma>}. mfam \<sigma> (CC \<beta>) \<gamma>')" by simp
        also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>\<gamma>'\<in>(ra_idx::('a\<Rightarrow>nat) set). mfam \<sigma> (CC \<beta>) \<gamma>')"
        proof (rule finite_sum_le_infsum)
          show "mfam \<sigma> (CC \<beta>) summable_on (ra_idx::('a\<Rightarrow>nat) set)" by (rule maj\<beta>sum[OF b])
          show "finite {\<gamma>}" by simp
          show "{\<gamma>} \<subseteq> ra_idx" using g by simp
          fix \<gamma>' :: "'a\<Rightarrow>nat" assume "\<gamma>' \<in> ra_idx - {\<gamma>}"
          show "0 \<le> mfam \<sigma> (CC \<beta>) \<gamma>'" using s0 by (simp add: mfam_nonneg)
        qed
        also have "\<dots> \<le> Kk \<beta>" by (rule maj\<beta>le[OF b])
        finally show ?thesis .
      qed
      have ccle: "\<bar>CC \<beta> \<gamma>\<bar> \<le> Kk \<beta> / \<sigma> ^ ra_deg \<gamma>"
        using one_term sp by (simp add: mult.commute pos_le_divide_eq)
      have "norm (a \<beta> * CC \<beta> \<gamma>) = \<bar>a \<beta>\<bar> * \<bar>CC \<beta> \<gamma>\<bar>" by (simp add: abs_mult)
      also have "\<dots> \<le> \<bar>a \<beta>\<bar> * (Kk \<beta> / \<sigma> ^ ra_deg \<gamma>)"
        by (rule mult_left_mono[OF ccle]) simp
      also have "\<dots> = (1 / \<sigma> ^ ra_deg \<gamma>) * (\<bar>a \<beta>\<bar> * Kk \<beta>)" by simp
      finally show "norm (a \<beta> * CC \<beta> \<gamma>) \<le> (1 / \<sigma> ^ ra_deg \<gamma>) * (\<bar>a \<beta>\<bar> * Kk \<beta>)" .
    qed
    have summ: "(\<lambda>\<beta>. a \<beta> * CC \<beta> \<gamma>) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
      by (rule abs_summable_summable[OF summabs])
    have base: "((\<lambda>\<beta>. a \<beta> * CC \<beta> \<gamma>) has_sum Cc \<gamma>) (ra_idx::('b\<Rightarrow>nat) set)"
      using summ unfolding Cc_def by (rule has_sum_infsum)
    have "((\<lambda>\<beta>. ra_monomial h \<gamma> * (a \<beta> * CC \<beta> \<gamma>)) has_sum (ra_monomial h \<gamma> * Cc \<gamma>))
            (ra_idx::('b\<Rightarrow>nat) set)"
      by (rule has_sum_cmult_right[OF base])
    thus ?thesis by (simp add: D_def)
  qed
  have "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R Cc \<gamma>) has_sum G x) (ra_idx::('a\<Rightarrow>nat) set)"
  proof (rule has_sum_SigmaD[where f = "\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)"
            and B = "\<lambda>_. ra_idx::('b\<Rightarrow>nat) set"])
    show "((\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) has_sum G x)
            (Sigma (ra_idx::('a\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('b\<Rightarrow>nat) set))"
      using Dswap by (simp add: Sigma_def)
  next
    fix \<gamma> :: "'a\<Rightarrow>nat" assume g: "\<gamma> \<in> ra_idx"
    show "((\<lambda>\<beta>. (\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) (\<gamma>,\<beta>)) has_sum (ra_monomial h \<gamma> *\<^sub>R Cc \<gamma>))
            (ra_idx::('b\<Rightarrow>nat) set)"
      using inner\<gamma>[OF g] by simp
  qed
  thus "((\<lambda>\<gamma>. ra_monomial (x - x0) \<gamma> *\<^sub>R (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). a \<beta> * CC \<beta> \<gamma>))
            has_sum G x) (ra_idx::('a\<Rightarrow>nat) set)"
    by (simp add: h_def Cc_def)
qed

text \<open>Vector outer-coefficient version of the dominated Fubini sum.\<close>

lemma series_on_majdom_vec:
  fixes CC :: "('b::euclidean_space \<Rightarrow> nat) \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
    and Fn :: "('b \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> real"
    and vg :: "('b \<Rightarrow> nat) \<Rightarrow> 'c::banach"
    and Kk :: "('b \<Rightarrow> nat) \<Rightarrow> real"
  assumes s0: "0 < \<sigma>" and r\<sigma>: "r \<le> \<sigma>"
    and ser: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> series_on x0 r (CC \<beta>) (Fn \<beta>)"
    and maj: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> majle \<sigma> (CC \<beta>) (Kk \<beta>)"
    and gsum: "(\<lambda>\<beta>. norm (vg \<beta>) * Kk \<beta>) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    and Gval: "\<And>x. dist x x0 < r \<Longrightarrow>
                  ((\<lambda>\<beta>. Fn \<beta> x *\<^sub>R vg \<beta>) has_sum G x) (ra_idx::('b\<Rightarrow>nat) set)"
  shows "\<forall>x. dist x x0 < r \<longrightarrow>
           ((\<lambda>\<gamma>. ra_monomial (x - x0) \<gamma> *\<^sub>R (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). CC \<beta> \<gamma> *\<^sub>R vg \<beta>))
              has_sum G x) (ra_idx::('a\<Rightarrow>nat) set)"
proof (intro allI impI)
  fix x :: 'a assume d: "dist x x0 < r"
  define h where "h = x - x0"
  have hle: "norm h \<le> \<sigma>"
  proof -
    have "norm h < r" using d by (simp add: h_def dist_norm)
    thus ?thesis using r\<sigma> by simp
  qed
  define D where "D = (\<lambda>(\<beta>,\<gamma>). ra_monomial h \<gamma> *\<^sub>R (CC \<beta> \<gamma> *\<^sub>R vg \<beta>))"
  have ser\<beta>: "((\<lambda>\<gamma>. ra_monomial h \<gamma> * CC \<beta> \<gamma>) has_sum Fn \<beta> x) (ra_idx::('a\<Rightarrow>nat) set)"
    if b: "\<beta> \<in> ra_idx" for \<beta>
    using ser[OF b] d unfolding series_on_def h_def by simp
  have maj\<beta>sum: "mfam \<sigma> (CC \<beta>) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
    if b: "\<beta> \<in> ra_idx" for \<beta>
    using maj[OF b] by (simp add: majle_def)
  have maj\<beta>le: "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). mfam \<sigma> (CC \<beta>) \<gamma>) \<le> Kk \<beta>"
    if b: "\<beta> \<in> ra_idx" for \<beta>
    using maj[OF b] by (simp add: majle_def)
  \<comment> \<open>pointwise norm-domination of the double family\<close>
  have Dbound: "norm (D (\<beta>,\<gamma>)) \<le> norm (vg \<beta>) * mfam \<sigma> (CC \<beta>) \<gamma>"
    if b: "\<beta> \<in> ra_idx" and g: "\<gamma> \<in> ra_idx" for \<beta> \<gamma>
  proof -
    have "norm (D (\<beta>,\<gamma>)) = \<bar>ra_monomial h \<gamma>\<bar> * (\<bar>CC \<beta> \<gamma>\<bar> * norm (vg \<beta>))"
      by (simp add: D_def abs_mult)
    also have "\<dots> \<le> (\<sigma> ^ ra_deg \<gamma>) * (\<bar>CC \<beta> \<gamma>\<bar> * norm (vg \<beta>))"
      by (rule mult_right_mono[OF ra_monomial_abs_le_pow[OF g hle]]) simp
    also have "\<dots> = norm (vg \<beta>) * (\<bar>CC \<beta> \<gamma>\<bar> * \<sigma> ^ ra_deg \<gamma>)"
      by (simp add: mult.assoc mult.left_commute)
    also have "\<dots> = norm (vg \<beta>) * mfam \<sigma> (CC \<beta>) \<gamma>" by (simp add: mfam_def)
    finally show ?thesis .
  qed
  have inner_abs: "(\<lambda>\<gamma>. norm (D (\<beta>,\<gamma>))) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
    if b: "\<beta> \<in> ra_idx" for \<beta>
  proof (rule summable_on_comparison_test[where f = "\<lambda>\<gamma>. norm (vg \<beta>) * mfam \<sigma> (CC \<beta>) \<gamma>"])
    show "(\<lambda>\<gamma>. norm (vg \<beta>) * mfam \<sigma> (CC \<beta>) \<gamma>) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
      by (rule summable_on_cmult_right[OF maj\<beta>sum[OF b]])
  next
    fix \<gamma> :: "'a\<Rightarrow>nat" assume g: "\<gamma> \<in> ra_idx"
    show "norm (D (\<beta>,\<gamma>)) \<le> norm (vg \<beta>) * mfam \<sigma> (CC \<beta>) \<gamma>" by (rule Dbound[OF b g])
  next
    fix \<gamma> :: "'a\<Rightarrow>nat" assume "\<gamma> \<in> ra_idx"
    show "0 \<le> norm (D (\<beta>,\<gamma>))" by simp
  qed
  have inner_tot_le: "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))) \<le> norm (vg \<beta>) * Kk \<beta>"
    if b: "\<beta> \<in> ra_idx" for \<beta>
  proof -
    have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))
            \<le> (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (vg \<beta>) * mfam \<sigma> (CC \<beta>) \<gamma>)"
    proof (rule infsum_mono)
      show "(\<lambda>\<gamma>. norm (D (\<beta>,\<gamma>))) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
        by (rule inner_abs[OF b])
      show "(\<lambda>\<gamma>. norm (vg \<beta>) * mfam \<sigma> (CC \<beta>) \<gamma>) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
        by (rule summable_on_cmult_right[OF maj\<beta>sum[OF b]])
      fix \<gamma> :: "'a\<Rightarrow>nat" assume g: "\<gamma> \<in> ra_idx"
      show "norm (D (\<beta>,\<gamma>)) \<le> norm (vg \<beta>) * mfam \<sigma> (CC \<beta>) \<gamma>" by (rule Dbound[OF b g])
    qed
    also have "\<dots> = norm (vg \<beta>) * (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). mfam \<sigma> (CC \<beta>) \<gamma>)"
      by (rule infsum_cmult_right[OF maj\<beta>sum[OF b]])
    also have "\<dots> \<le> norm (vg \<beta>) * Kk \<beta>"
      by (rule mult_left_mono[OF maj\<beta>le[OF b]]) simp
    finally show ?thesis .
  qed
  have outer_abs: "(\<lambda>\<beta>. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))
                     summable_on (ra_idx::('b\<Rightarrow>nat) set)"
  proof (rule summable_on_comparison_test[where f = "\<lambda>\<beta>. norm (vg \<beta>) * Kk \<beta>"])
    show "(\<lambda>\<beta>. norm (vg \<beta>) * Kk \<beta>) summable_on (ra_idx::('b\<Rightarrow>nat) set)" by (rule gsum)
  next
    fix \<beta> :: "'b\<Rightarrow>nat" assume b: "\<beta> \<in> ra_idx"
    show "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))) \<le> norm (vg \<beta>) * Kk \<beta>"
      by (rule inner_tot_le[OF b])
  next
    fix \<beta> :: "'b\<Rightarrow>nat" assume "\<beta> \<in> ra_idx"
    show "0 \<le> (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))"
      by (rule infsum_nonneg) simp
  qed
  have outer_abs': "(\<lambda>\<beta>. norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))))
                      summable_on (ra_idx::('b\<Rightarrow>nat) set)"
  proof -
    have eq: "(\<lambda>\<beta>. norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))))
                = (\<lambda>\<beta>. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))"
    proof (rule ext)
      fix \<beta> :: "'b\<Rightarrow>nat"
      have "0 \<le> (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))"
        by (rule infsum_nonneg) simp
      thus "norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))
              = (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>)))" by simp
    qed
    show ?thesis using outer_abs by (simp only: eq)
  qed
  have conj1: "\<forall>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). (\<lambda>\<gamma>. norm (D (\<beta>,\<gamma>))) summable_on (ra_idx::('a\<Rightarrow>nat) set)"
    using inner_abs by blast
  have conj2: "(\<lambda>\<beta>. norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a\<Rightarrow>nat) set). norm (D (\<beta>,\<gamma>))))
                 summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    by (rule outer_abs')
  have Dabs: "(\<lambda>z. norm (D z)) summable_on (Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set))"
    by (rule Infinite_Sum.abs_summable_on_Sigma_iff
          [where f = D and A = "ra_idx::('b\<Rightarrow>nat) set" and B = "\<lambda>_. ra_idx::('a\<Rightarrow>nat) set",
           THEN iffD2, OF conjI[OF conj1 conj2]])
  have Dsumm: "D summable_on (Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set))"
    by (rule abs_summable_summable[OF Dabs])
  have GhsB: "((\<lambda>\<beta>. Fn \<beta> x *\<^sub>R vg \<beta>) has_sum G x) (ra_idx::('b\<Rightarrow>nat) set)"
    by (rule Gval[OF d])
  have innerB: "((\<lambda>\<gamma>. D (\<beta>,\<gamma>)) has_sum (Fn \<beta> x *\<^sub>R vg \<beta>)) (ra_idx::('a\<Rightarrow>nat) set)"
    if b: "\<beta> \<in> ra_idx" for \<beta>
  proof -
    have "((\<lambda>\<gamma>. (ra_monomial h \<gamma> * CC \<beta> \<gamma>) *\<^sub>R vg \<beta>) has_sum (Fn \<beta> x *\<^sub>R vg \<beta>))
            (ra_idx::('a\<Rightarrow>nat) set)"
      by (rule has_sum_bounded_linear[OF bounded_linear_scaleR_left ser\<beta>[OF b]])
    thus ?thesis by (simp add: D_def)
  qed
  have DhsG: "(D has_sum G x) (Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set))"
  proof (rule has_sum_SigmaI[where g = "\<lambda>\<beta>. Fn \<beta> x *\<^sub>R vg \<beta>"])
    fix \<beta> :: "'b\<Rightarrow>nat" assume b: "\<beta> \<in> ra_idx"
    show "((\<lambda>\<gamma>. D (\<beta>,\<gamma>)) has_sum (Fn \<beta> x *\<^sub>R vg \<beta>)) (ra_idx::('a\<Rightarrow>nat) set)"
      by (rule innerB[OF b])
  next
    show "((\<lambda>\<beta>. Fn \<beta> x *\<^sub>R vg \<beta>) has_sum G x) (ra_idx::('b\<Rightarrow>nat) set)" by (rule GhsB)
  next
    show "D summable_on (Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set))"
      by (rule Dsumm)
  qed
  have Dswap: "((\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) has_sum G x)
                 ((ra_idx::('a\<Rightarrow>nat) set) \<times> (ra_idx::('b\<Rightarrow>nat) set))"
  proof -
    have e1: "Sigma (ra_idx::('b\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('a\<Rightarrow>nat) set)
                = (ra_idx::('b\<Rightarrow>nat) set) \<times> (ra_idx::('a\<Rightarrow>nat) set)" by simp
    have "(D has_sum G x) ((ra_idx::('b\<Rightarrow>nat) set) \<times> (ra_idx::('a\<Rightarrow>nat) set))"
      using DhsG e1 by simp
    thus ?thesis by (subst has_sum_swap) simp
  qed
  have Dswap_summ: "(\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) summable_on
                      (Sigma (ra_idx::('a\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('b\<Rightarrow>nat) set))"
    using Dswap has_sum_imp_summable by (simp add: Sigma_def)
  define Cc where "Cc = (\<lambda>\<gamma>. \<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). CC \<beta> \<gamma> *\<^sub>R vg \<beta>)"
  have inner\<gamma>: "((\<lambda>\<beta>. D (\<beta>,\<gamma>)) has_sum (ra_monomial h \<gamma> *\<^sub>R Cc \<gamma>)) (ra_idx::('b\<Rightarrow>nat) set)"
    if g: "\<gamma> \<in> ra_idx" for \<gamma>
  proof -
    have summabs: "(\<lambda>\<beta>. norm (CC \<beta> \<gamma> *\<^sub>R vg \<beta>)) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    proof (rule summable_on_comparison_test
             [where f = "\<lambda>\<beta>. (1 / \<sigma> ^ ra_deg \<gamma>) * (norm (vg \<beta>) * Kk \<beta>)"])
      show "(\<lambda>\<beta>. (1 / \<sigma> ^ ra_deg \<gamma>) * (norm (vg \<beta>) * Kk \<beta>)) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
        by (rule summable_on_cmult_right[OF gsum])
    next
      fix \<beta> :: "'b\<Rightarrow>nat" assume "\<beta> \<in> ra_idx"
      show "0 \<le> norm (CC \<beta> \<gamma> *\<^sub>R vg \<beta>)" by simp
    next
      fix \<beta> :: "'b\<Rightarrow>nat" assume b: "\<beta> \<in> ra_idx"
      have sp: "0 < \<sigma> ^ ra_deg \<gamma>" using s0 by simp
      have one_term: "\<bar>CC \<beta> \<gamma>\<bar> * \<sigma> ^ ra_deg \<gamma> \<le> Kk \<beta>"
      proof -
        have "\<bar>CC \<beta> \<gamma>\<bar> * \<sigma> ^ ra_deg \<gamma> = mfam \<sigma> (CC \<beta>) \<gamma>" by (simp add: mfam_def)
        also have "\<dots> = (\<Sum>\<gamma>'\<in>{\<gamma>}. mfam \<sigma> (CC \<beta>) \<gamma>')" by simp
        also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>\<gamma>'\<in>(ra_idx::('a\<Rightarrow>nat) set). mfam \<sigma> (CC \<beta>) \<gamma>')"
        proof (rule finite_sum_le_infsum)
          show "mfam \<sigma> (CC \<beta>) summable_on (ra_idx::('a\<Rightarrow>nat) set)" by (rule maj\<beta>sum[OF b])
          show "finite {\<gamma>}" by simp
          show "{\<gamma>} \<subseteq> ra_idx" using g by simp
          fix \<gamma>' :: "'a\<Rightarrow>nat" assume "\<gamma>' \<in> ra_idx - {\<gamma>}"
          show "0 \<le> mfam \<sigma> (CC \<beta>) \<gamma>'" using s0 by (simp add: mfam_nonneg)
        qed
        also have "\<dots> \<le> Kk \<beta>" by (rule maj\<beta>le[OF b])
        finally show ?thesis .
      qed
      have ccle: "\<bar>CC \<beta> \<gamma>\<bar> \<le> Kk \<beta> / \<sigma> ^ ra_deg \<gamma>"
        using one_term sp by (simp add: mult.commute pos_le_divide_eq)
      have "norm (CC \<beta> \<gamma> *\<^sub>R vg \<beta>) = \<bar>CC \<beta> \<gamma>\<bar> * norm (vg \<beta>)" by simp
      also have "\<dots> \<le> (Kk \<beta> / \<sigma> ^ ra_deg \<gamma>) * norm (vg \<beta>)"
        by (rule mult_right_mono[OF ccle]) simp
      also have "\<dots> = (1 / \<sigma> ^ ra_deg \<gamma>) * (norm (vg \<beta>) * Kk \<beta>)" by simp
      finally show "norm (CC \<beta> \<gamma> *\<^sub>R vg \<beta>) \<le> (1 / \<sigma> ^ ra_deg \<gamma>) * (norm (vg \<beta>) * Kk \<beta>)" .
    qed
    have summ: "(\<lambda>\<beta>. CC \<beta> \<gamma> *\<^sub>R vg \<beta>) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
      by (rule abs_summable_summable[OF summabs])
    have base: "((\<lambda>\<beta>. CC \<beta> \<gamma> *\<^sub>R vg \<beta>) has_sum Cc \<gamma>) (ra_idx::('b\<Rightarrow>nat) set)"
      using summ unfolding Cc_def by (rule has_sum_infsum)
    have "((\<lambda>\<beta>. ra_monomial h \<gamma> *\<^sub>R (CC \<beta> \<gamma> *\<^sub>R vg \<beta>)) has_sum (ra_monomial h \<gamma> *\<^sub>R Cc \<gamma>))
            (ra_idx::('b\<Rightarrow>nat) set)"
      by (rule has_sum_scaleR[OF base])
    thus ?thesis by (simp add: D_def)
  qed
  have "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R Cc \<gamma>) has_sum G x) (ra_idx::('a\<Rightarrow>nat) set)"
  proof (rule has_sum_SigmaD[where f = "\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)"
            and B = "\<lambda>_. ra_idx::('b\<Rightarrow>nat) set"])
    show "((\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) has_sum G x)
            (Sigma (ra_idx::('a\<Rightarrow>nat) set) (\<lambda>_. ra_idx::('b\<Rightarrow>nat) set))"
      using Dswap by (simp add: Sigma_def)
  next
    fix \<gamma> :: "'a\<Rightarrow>nat" assume g: "\<gamma> \<in> ra_idx"
    show "((\<lambda>\<beta>. (\<lambda>(\<gamma>,\<beta>). D (\<beta>,\<gamma>)) (\<gamma>,\<beta>)) has_sum (ra_monomial h \<gamma> *\<^sub>R Cc \<gamma>))
            (ra_idx::('b\<Rightarrow>nat) set)"
      using inner\<gamma>[OF g] by simp
  qed
  thus "((\<lambda>\<gamma>. ra_monomial (x - x0) \<gamma> *\<^sub>R (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). CC \<beta> \<gamma> *\<^sub>R vg \<beta>))
            has_sum G x) (ra_idx::('a\<Rightarrow>nat) set)"
    by (simp add: h_def Cc_def)
qed

subsection \<open>Final composition theorem\<close>

text \<open>A coefficient bound with vanishing zero-degree term gives a majle bound whose
  value is the geometric tail (which tends to 0 as \<open>\<sigma>\<close> shrinks).\<close>

lemma majle_tail_bound:
  fixes c :: "('b::euclidean_space\<Rightarrow>nat)\<Rightarrow>'d::real_normed_vector"
  assumes Mnn: "0 \<le> M"
    and c0: "c czero_idx = 0"
    and bound: "\<And>\<alpha>. \<alpha>\<in>ra_idx \<Longrightarrow> norm (c \<alpha>) \<le> M / t ^ (ra_deg \<alpha>)"
    and t: "0 < t" and s0: "0 \<le> \<sigma>" and st: "\<sigma> < t"
  shows "majle \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>))
           (M * ((\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). (\<sigma>/t) ^ ra_deg \<alpha>) - 1))"
proof -
  define q where "q = \<sigma>/t"
  have q0: "0 \<le> q" using s0 t by (simp add: q_def)
  have q1: "q < 1" using st t by (simp add: q_def)
  have geomS: "(\<lambda>\<alpha>::'b\<Rightarrow>nat. q ^ ra_deg \<alpha>) summable_on ra_idx"
    by (rule geom_idx_summable[OF q0 q1])
  have geomMS: "(\<lambda>\<alpha>. M * q ^ ra_deg \<alpha>) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    by (rule summable_on_cmult_right[OF geomS])
  have ptwise: "mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha> \<le> M * q ^ ra_deg \<alpha>" if a: "\<alpha>\<in>ra_idx" for \<alpha>
  proof -
    have "mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha> = norm (c \<alpha>) * \<sigma> ^ ra_deg \<alpha>"
      by (simp add: mfam_def)
    also have "\<dots> \<le> (M / t ^ ra_deg \<alpha>) * \<sigma> ^ ra_deg \<alpha>"
      by (rule mult_right_mono[OF bound[OF a]]) (use s0 in simp)
    also have "\<dots> = M * q ^ ra_deg \<alpha>" by (simp add: q_def power_divide)
    finally show ?thesis .
  qed
  have nn: "0 \<le> mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha>" for \<alpha> using s0 by (rule mfam_nonneg)
  have summ: "mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    by (rule summable_on_comparison_test[OF geomMS]) (use ptwise nn in auto)
  \<comment> \<open>the zero-degree term of the majorant vanishes\<close>
  have mfam0: "mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) czero_idx = 0"
    by (simp add: mfam_def c0)
  have czin: "(czero_idx::'b\<Rightarrow>nat) \<in> ra_idx" by (rule czero_idx_in)
  \<comment> \<open>split off the (zero) zero-degree term of the majorant sum\<close>
  have splitM: "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha>)
                  = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('b\<Rightarrow>nat) set) - {czero_idx}).
                       mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha>)"
    using infsum_split_off[OF summ czin] mfam0 by simp
  \<comment> \<open>and of the geometric sum\<close>
  have splitG: "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). M * q ^ ra_deg \<alpha>)
                  = M * (q ^ ra_deg (czero_idx::'b\<Rightarrow>nat))
                    + (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('b\<Rightarrow>nat) set) - {czero_idx}). M * q ^ ra_deg \<alpha>)"
    using infsum_split_off[OF geomMS czin] by simp
  have geomMSrest: "(\<lambda>\<alpha>. M * q ^ ra_deg \<alpha>) summable_on
                      ((ra_idx::('b\<Rightarrow>nat) set) - {czero_idx})"
    by (rule summable_on_subset_banach[OF geomMS]) auto
  have summrest: "mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) summable_on
                    ((ra_idx::('b\<Rightarrow>nat) set) - {czero_idx})"
    by (rule summable_on_subset_banach[OF summ]) auto
  have tailbound:
    "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('b\<Rightarrow>nat) set) - {czero_idx}). mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha>)
      \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('b\<Rightarrow>nat) set) - {czero_idx}). M * q ^ ra_deg \<alpha>)"
    by (rule infsum_mono[OF summrest geomMSrest]) (use ptwise in auto)
  have geom_eq: "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). M * q ^ ra_deg \<alpha>)
                   = M * (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). q ^ ra_deg \<alpha>)"
    by (rule infsum_cmult_right[OF geomS])
  have ztermq: "q ^ ra_deg (czero_idx::'b\<Rightarrow>nat) = 1"
    by (simp add: ra_deg_def czero_idx_def)
  have "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha>)
          = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('b\<Rightarrow>nat) set) - {czero_idx}). mfam \<sigma> (\<lambda>\<alpha>. norm (c \<alpha>)) \<alpha>)"
    by (rule splitM)
  also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>((ra_idx::('b\<Rightarrow>nat) set) - {czero_idx}). M * q ^ ra_deg \<alpha>)"
    by (rule tailbound)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). M * q ^ ra_deg \<alpha>) - M * 1"
    using splitG ztermq by simp
  also have "\<dots> = M * ((\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('b\<Rightarrow>nat) set). q ^ ra_deg \<alpha>) - 1)"
    using geom_eq by (simp add: algebra_simps)
  finally show ?thesis using summ by (simp add: majle_def q_def)
qed

text \<open>Scaling a real-analytic scalar function by a fixed vector stays analytic.\<close>

lemma real_analytic_on_scaleR_vec:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and v :: "'c::real_normed_vector"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. f x *\<^sub>R v) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open U" by (rule U)
  next
    fix x0 assume x0: "x0 \<in> U"
    from F x0 obtain r c where r: "0 < r"
      and F1: "\<And>x. dist x x0 < r \<Longrightarrow>
                ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x) ra_idx"
      unfolding real_analytic_on_def by blast
    show "\<exists>r>0. \<exists>cc. \<forall>x. dist x x0 < r \<longrightarrow>
            ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cc \<alpha>) has_sum (f x *\<^sub>R v)) ra_idx"
    proof (intro exI[where x=r] conjI exI[where x="\<lambda>\<alpha>. c \<alpha> *\<^sub>R v"] allI impI)
      show "0 < r" by (rule r)
    next
      fix x assume d: "dist x x0 < r"
      have bl: "bounded_linear (\<lambda>t::real. t *\<^sub>R v)" by (rule bounded_linear_scaleR_left)
      have "((\<lambda>\<alpha>. (ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) *\<^sub>R v) has_sum (f x *\<^sub>R v)) ra_idx"
        by (rule has_sum_bounded_linear[OF bl F1[OF d]])
      thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (c \<alpha> *\<^sub>R v)) has_sum (f x *\<^sub>R v)) ra_idx"
        by simp
    qed
  qed
qed

text \<open>Composition of real-analytic functions (target a Banach space).\<close>

lemma real_analytic_on_compose:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    and g :: "'b \<Rightarrow> 'c::banach"
  assumes F: "real_analytic_on f U" and G: "real_analytic_on g V" and FV: "f ` U \<subseteq> V"
  shows "real_analytic_on (\<lambda>x. g (f x)) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  from G have Vopen: "open V" by (simp only: real_analytic_on_def)
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open U" by (rule U)
  next
    fix x0 assume x0: "x0 \<in> U"
    define y0 where "y0 = f x0"
    have y0V: "y0 \<in> V" using FV x0 by (auto simp: y0_def)
    \<comment> \<open>g's local series around \<open>y0\<close>\<close>
    from G y0V obtain \<rho>g cg where \<rho>g: "0 < \<rho>g"
      and Gser: "\<And>y. dist y y0 < \<rho>g \<Longrightarrow>
                  ((\<lambda>\<beta>. ra_monomial (y - y0) \<beta> *\<^sub>R cg \<beta>) has_sum g y) ra_idx"
      unfolding real_analytic_on_def by blast
    \<comment> \<open>Cauchy bound on g's coefficients at a corner inside the \<open>\<rho>g\<close>-ball\<close>
    define eB where "eB = (\<Sum>b\<in>(Basis::'b set). b)"
    have eBpos: "0 < norm eB"
    proof -
      have "eB \<noteq> 0"
      proof
        assume "eB = 0"
        then have "eB \<bullet> (SOME b. b \<in> (Basis::'b set)) = 0" by simp
        moreover obtain b0 :: 'b where b0: "b0 \<in> Basis" using nonempty_Basis by blast
        have "(SOME b. b \<in> (Basis::'b set)) \<in> Basis" using b0 by (rule someI)
        hence "eB \<bullet> (SOME b. b \<in> (Basis::'b set)) = 1"
          by (simp add: eB_def inner_sum_left inner_Basis)
        ultimately show False by simp
      qed
      thus ?thesis by simp
    qed
    define t where "t = \<rho>g / (2 * norm eB)"
    have t0: "0 < t" using \<rho>g eBpos by (simp add: t_def)
    have corner_g: "t * norm (\<Sum>b\<in>(Basis::'b set). b) < \<rho>g"
    proof -
      have "t * norm eB = \<rho>g / 2" using eBpos by (simp add: t_def)
      also have "\<dots> < \<rho>g" using \<rho>g by simp
      finally show ?thesis by (simp add: eB_def)
    qed
    obtain Mg where Mgnn: "Mg \<ge> 0"
      and cgbound: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> norm (cg \<beta>) \<le> Mg / t ^ (ra_deg \<beta>)"
      using ra_coeff_bound[OF \<rho>g Gser t0 corner_g] by blast
    \<comment> \<open>shifted \<open>f\<close>: zero constant coefficient\<close>
    have F': "real_analytic_on (\<lambda>x. f x - y0) U"
      by (rule real_analytic_on_diff[OF F real_analytic_on_const[OF U]])
    from F' x0 obtain rf cf where rf: "0 < rf"
      and Fser: "\<And>x. dist x x0 < rf \<Longrightarrow>
                  ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cf \<alpha>) has_sum (f x - y0)) ra_idx"
      unfolding real_analytic_on_def by blast
    \<comment> \<open>Cauchy bound on the shifted \<open>f\<close>'s coefficients on a smaller ball\<close>
    define eA where "eA = (\<Sum>b\<in>(Basis::'a set). b)"
    have eApos: "0 < norm eA"
    proof -
      have "eA \<noteq> 0"
      proof
        assume "eA = 0"
        moreover obtain a0 :: 'a where a0: "a0 \<in> Basis" using nonempty_Basis by blast
        have "(SOME b. b \<in> (Basis::'a set)) \<in> Basis" using a0 by (rule someI)
        hence "eA \<bullet> (SOME b. b \<in> (Basis::'a set)) = 1"
          by (simp add: eA_def inner_sum_left inner_Basis)
        ultimately show False by simp
      qed
      thus ?thesis by simp
    qed
    define sf where "sf = rf / (2 * norm eA)"
    have sf0: "0 < sf" using rf eApos by (simp add: sf_def)
    have corner_f: "sf * norm (\<Sum>b\<in>(Basis::'a set). b) < rf"
    proof -
      have "sf * norm eA = rf / 2" using eApos by (simp add: sf_def)
      also have "\<dots> < rf" using rf by simp
      finally show ?thesis by (simp add: eA_def)
    qed
    obtain Mf where Mfnn: "Mf \<ge> 0"
      and cfbound: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> norm (cf \<alpha>) \<le> Mf / sf ^ (ra_deg \<alpha>)"
      using ra_coeff_bound[OF rf Fser sf0 corner_f] by blast
    \<comment> \<open>choose \<open>\<sigma>\<close> small: drive the shifted-\<open>f\<close> majorant below \<open>t\<close>\<close>
    define geo where "geo = (\<lambda>q::real. \<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). q ^ ra_deg \<alpha>)"
    \<comment> \<open>the shifted-f majle constant as a function of \<open>\<sigma>\<close>\<close>
    have shifted_const0: "cf czero_idx = 0"
    proof -
      have "((\<lambda>\<alpha>. ra_monomial (x0 - x0) \<alpha> *\<^sub>R cf \<alpha>) has_sum (f x0 - y0)) ra_idx"
        by (rule Fser) (simp add: rf)
      then have hs: "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R cf \<alpha>) has_sum (0::'b)) ra_idx"
        by (simp add: y0_def)
      have neutral: "ra_monomial (0::'a) \<alpha> *\<^sub>R cf \<alpha> = 0"
        if "\<alpha> \<in> ra_idx - {czero_idx}" for \<alpha>
      proof -
        have "\<alpha> \<noteq> czero_idx" using that by simp
        hence "ra_deg \<alpha> \<noteq> 0" using ra_deg_eq0_iff that by auto
        thus ?thesis by (simp add: ra_monomial_zero)
      qed
      have "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R cf \<alpha>) has_sum (0::'b)) ra_idx
              = ((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R cf \<alpha>) has_sum (0::'b)) {czero_idx}"
        by (rule has_sum_cong_neutral) (use neutral czero_idx_in in auto)
      with hs have "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R cf \<alpha>) has_sum (0::'b)) {czero_idx}" by simp
      moreover have "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R cf \<alpha>) has_sum (cf czero_idx)) {czero_idx}"
        by (rule has_sum_finiteI) (auto simp: ra_monomial_zero czero_idx_def ra_deg_def)
      ultimately show ?thesis by (metis has_sum_unique)
    qed
    \<comment> \<open>continuity: \<open>f x\<close> stays in \<open>g\<close>'s ball near \<open>x0\<close>\<close>
    have contf: "continuous (at x0) f" by (rule real_analytic_on_imp_continuous_vec[OF F x0])
    have tend: "(f \<longlongrightarrow> f x0) (at x0)" using contf by (simp add: continuous_at)
    have evb: "\<forall>\<^sub>F x in at x0. f x \<in> ball (f x0) \<rho>g"
      by (rule topological_tendstoD[OF tend]) (use \<rho>g in auto)
    have "\<forall>\<^sub>F x in at x0. dist (f x) (f x0) < \<rho>g"
      using evb by (simp add: dist_commute)
    then obtain \<delta>c where \<delta>c: "0 < \<delta>c"
      and contball: "\<And>x. dist x x0 < \<delta>c \<Longrightarrow> x \<noteq> x0 \<Longrightarrow> dist (f x) y0 < \<rho>g"
      using \<rho>g by (auto simp: eventually_at y0_def dist_commute)
    have contball': "dist (f x) y0 < \<rho>g" if "dist x x0 < \<delta>c" for x
    proof (cases "x = x0")
      case True thus ?thesis using \<rho>g by (simp add: y0_def)
    next
      case False thus ?thesis using contball[OF that] by simp
    qed
    \<comment> \<open>geometric constant for the tail estimate (over \<open>'a\<close>-indices)\<close>
    define gh where "gh = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). (1/2::real) ^ ra_deg \<alpha>)"
    have ghnn: "0 \<le> gh" unfolding gh_def by (rule infsum_nonneg) simp
    define C where "C = Mf * (2 / sf) * gh"
    have Cnn: "0 \<le> C" using Mfnn sf0 ghnn by (simp add: C_def)
    define th where "th = t / (C + 1)"
    have th0: "0 < th" using t0 Cnn by (simp add: th_def)
    \<comment> \<open>the working radius / majle parameter\<close>
    define \<sigma> where "\<sigma> = (min (sf/2) (min \<delta>c (min rf th))) / 2"
    have \<sigma>0: "0 < \<sigma>" using sf0 \<delta>c rf th0 by (simp add: \<sigma>_def)
    have \<sigma>sf2: "\<sigma> \<le> sf/2" using \<delta>c rf th0 sf0 by (simp add: \<sigma>_def)
    have \<sigma>sf: "\<sigma> < sf" using \<sigma>sf2 sf0 by simp
    have \<sigma>\<delta>c: "\<sigma> \<le> \<delta>c" using sf0 rf th0 \<delta>c by (simp add: \<sigma>_def)
    have \<sigma>rf: "\<sigma> \<le> rf" using sf0 \<delta>c th0 rf by (simp add: \<sigma>_def)
    have \<sigma>th: "\<sigma> \<le> th" using sf0 \<delta>c rf th0 by (simp add: \<sigma>_def)
    have qhalf: "\<sigma>/sf \<le> 1/2" using \<sigma>sf2 sf0 by (simp add: divide_le_eq)
    \<comment> \<open>majle bound for shifted-f coefficients, with vanishing zero-term\<close>
    define Mc where "Mc = Mf * ((\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). (\<sigma>/sf) ^ ra_deg \<alpha>) - 1)"
    have \<sigma>nn: "0 \<le> \<sigma>" using \<sigma>0 by simp
    have cfmaj: "majle \<sigma> (\<lambda>\<alpha>. norm (cf \<alpha>)) Mc"
      unfolding Mc_def
      by (rule majle_tail_bound[OF Mfnn shifted_const0 cfbound sf0 \<sigma>nn \<sigma>sf])
    have Mcnn: "0 \<le> Mc"
      using majle_imp_nonneg_sum[OF _ cfmaj] cfmaj \<sigma>0 by (simp add: majle_def)
    \<comment> \<open>the geometric tail is linearly small, hence \<open>Mc < t\<close>\<close>
    have tail_small: "(\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a\<Rightarrow>nat) set). (\<sigma>/sf) ^ ra_deg \<alpha>) - 1 \<le> (\<sigma>/sf)/(1/2) * gh"
      unfolding gh_def
      by (rule geom_idx_tail_small[OF _ qhalf]) (use \<sigma>0 sf0 in auto)
    have Mc_le: "Mc \<le> C * \<sigma>"
    proof -
      have "Mc \<le> Mf * ((\<sigma>/sf)/(1/2) * gh)"
        unfolding Mc_def by (rule mult_left_mono[OF tail_small Mfnn])
      also have "\<dots> = C * \<sigma>" using sf0 by (simp add: C_def field_simps)
      finally show ?thesis .
    qed
    have Mc_lt_t: "Mc < t"
    proof -
      have "C * \<sigma> \<le> C * th" using \<sigma>th Cnn by (simp add: mult_left_mono)
      also have "\<dots> = C * t / (C + 1)" by (simp add: th_def)
      also have "\<dots> < t"
      proof -
        have "C * t / (C + 1) < t \<longleftrightarrow> C * t < t * (C + 1)"
          using Cnn by (simp add: pos_divide_less_eq)
        thus ?thesis using t0 Cnn by (simp add: field_simps)
      qed
      finally show ?thesis using Mc_le by linarith
    qed
    \<comment> \<open>the per-monomial majorant constant\<close>
    define Km where "Km = (Mc + t)/2"
    have Km_ge: "Mc \<le> Km" using Mc_lt_t by (simp add: Km_def)
    have Km_lt: "Km < t" using Mc_lt_t by (simp add: Km_def)
    have Km_nn: "0 \<le> Km" using Mcnn Mc_lt_t by (simp add: Km_def)
    \<comment> \<open>shifted-f series available on radius \<open>rf\<close>, restrict to \<open>\<sigma>\<close>\<close>
    have Fser': "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cf \<alpha>) has_sum (f x - y0)) ra_idx"
      if "dist x x0 < \<sigma>" for x
      using Fser[of x] that \<sigma>rf by simp
    \<comment> \<open>per-\<open>\<beta>\<close> smaj for the composed monomials \<open>x \<mapsto> ra_monomial (f x - y0) \<beta>\<close>\<close>
    have perbeta: "\<exists>cc. smaj x0 \<sigma> \<sigma> cc (\<lambda>x. ra_monomial (f x - y0) \<beta>) (Km ^ ra_deg \<beta>)" for \<beta>
    proof -
      have "\<exists>cc. smaj x0 \<sigma> \<sigma> cc (\<lambda>x. ra_monomial ((f x - y0) - 0) \<beta>) (Km ^ ra_deg \<beta>)"
      proof (rule smaj_ra_monomial_compose[where cf = cf and Mc = Mc])
        show "0 \<le> \<sigma>" using \<sigma>0 by simp
        show "\<And>x. dist x x0 < \<sigma> \<Longrightarrow>
                ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R cf \<alpha>) has_sum (f x - y0)) ra_idx"
          by (rule Fser')
        show "majle \<sigma> (\<lambda>\<alpha>. norm (cf \<alpha>)) Mc" by (rule cfmaj)
        show "\<And>b. b \<in> Basis \<Longrightarrow> Mc + \<bar>(0::'b) \<bullet> b\<bar> \<le> Km" using Km_ge by simp
        show "0 \<le> Km" by (rule Km_nn)
      qed
      thus ?thesis by simp
    qed
    \<comment> \<open>choose the coefficient families\<close>
    have "\<exists>CC. \<forall>\<beta>. smaj x0 \<sigma> \<sigma> (CC \<beta>) (\<lambda>x. ra_monomial (f x - y0) \<beta>) (Km ^ ra_deg \<beta>)"
      by (subst choice_iff[symmetric]) (use perbeta in blast)
    then obtain CC where CCsmaj:
      "\<And>\<beta>. smaj x0 \<sigma> \<sigma> (CC \<beta>) (\<lambda>x. ra_monomial (f x - y0) \<beta>) (Km ^ ra_deg \<beta>)" by blast
    have CCser: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> series_on x0 \<sigma> (CC \<beta>) (\<lambda>x. ra_monomial (f x - y0) \<beta>)"
      using CCsmaj by (simp add: smaj_def)
    have CCmaj: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> majle \<sigma> (CC \<beta>) (Km ^ ra_deg \<beta>)"
      using CCsmaj by (simp add: smaj_def)
    \<comment> \<open>g-coefficient summability against the per-monomial majorant\<close>
    have gsum: "(\<lambda>\<beta>. norm (cg \<beta>) * Km ^ ra_deg \<beta>) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
    proof (rule summable_on_comparison_test
             [where f = "\<lambda>\<beta>. Mg * (Km / t) ^ ra_deg \<beta>"])
      have qlt: "Km / t < 1" using Km_lt t0 by (simp add: divide_less_eq)
      have qnn: "0 \<le> Km / t" using Km_nn t0 by simp
      have "(\<lambda>\<beta>::'b\<Rightarrow>nat. (Km / t) ^ ra_deg \<beta>) summable_on ra_idx"
        by (rule geom_idx_summable[OF qnn qlt])
      thus "(\<lambda>\<beta>. Mg * (Km / t) ^ ra_deg \<beta>) summable_on (ra_idx::('b\<Rightarrow>nat) set)"
        by (rule summable_on_cmult_right)
    next
      fix \<beta> :: "'b\<Rightarrow>nat" assume b: "\<beta> \<in> ra_idx"
      have "norm (cg \<beta>) * Km ^ ra_deg \<beta> \<le> (Mg / t ^ ra_deg \<beta>) * Km ^ ra_deg \<beta>"
        by (rule mult_right_mono[OF cgbound[OF b]]) (use Km_nn in simp)
      also have "\<dots> = Mg * (Km ^ ra_deg \<beta> / t ^ ra_deg \<beta>)" by simp
      also have "\<dots> = Mg * (Km / t) ^ ra_deg \<beta>" by (simp add: power_divide)
      finally show "norm (cg \<beta>) * Km ^ ra_deg \<beta> \<le> Mg * (Km / t) ^ ra_deg \<beta>" .
    next
      fix \<beta> :: "'b\<Rightarrow>nat" assume "\<beta> \<in> ra_idx"
      show "0 \<le> norm (cg \<beta>) * Km ^ ra_deg \<beta>" using Km_nn by simp
    qed
    \<comment> \<open>the \<open>\<beta>\<close>-sum value: \<open>g\<close>'s series at \<open>f x\<close>\<close>
    have Gval: "((\<lambda>\<beta>. ra_monomial (f x - y0) \<beta> *\<^sub>R cg \<beta>) has_sum g (f x)) (ra_idx::('b\<Rightarrow>nat) set)"
      if "dist x x0 < \<sigma>" for x
    proof -
      have "dist (f x) y0 < \<rho>g" using contball'[of x] that \<sigma>\<delta>c by simp
      thus ?thesis by (rule Gser)
    qed
    \<comment> \<open>assemble via the vector dominated-Fubini helper\<close>
    have main: "\<forall>x. dist x x0 < \<sigma> \<longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial (x - x0) \<gamma> *\<^sub>R
              (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('b\<Rightarrow>nat) set). CC \<beta> \<gamma> *\<^sub>R cg \<beta>))
           has_sum g (f x)) (ra_idx::('a\<Rightarrow>nat) set)"
      by (rule series_on_majdom_vec
            [where CC = CC and Fn = "\<lambda>\<beta> x. ra_monomial (f x - y0) \<beta>" and vg = cg
               and Kk = "\<lambda>\<beta>. Km ^ ra_deg \<beta>" and \<sigma> = \<sigma> and r = \<sigma>
               and G = "\<lambda>x. g (f x)"])
         (use \<sigma>0 CCser CCmaj gsum Gval in auto)
    show "\<exists>r>0. \<exists>cc. \<forall>x. dist x x0 < r \<longrightarrow>
            ((\<lambda>\<gamma>. ra_monomial (x - x0) \<gamma> *\<^sub>R cc \<gamma>) has_sum g (f x)) ra_idx"
      using \<sigma>0 main by (intro exI, auto)
  qed
qed

text \<open>
  The analytic implicit-function theorem itself (\<open>real_analytic_implicit_function\<close>) is
  proved in the companion theory \<open>Real_Analytic_IFT\<close>, as the final assembly on top of the
  real-analytic local inverse theorem.  It is stated and established there rather than
  here, so this foundation theory is kept free of unproved targets.
\<close>

end
