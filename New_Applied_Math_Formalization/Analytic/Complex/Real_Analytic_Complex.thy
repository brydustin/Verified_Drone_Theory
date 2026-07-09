section \<open>Complexification bridge for real-analytic functions\<close>

text \<open>
  Connects the real-analytic predicate \<open>real_analytic_on\<close> (theory \<open>Real_Analytic\<close>)
  to the HOL \<open>Complex_Analysis\<close> library, via the classical complexification route:

  \<^item> (A3) the several-variable Cauchy--Riemann criterion: a real-differentiable map of the
    plane whose total derivative is \<open>\<complex>\<close>-linear is holomorphic;
  \<^item> (A2) holomorphic \<open>\<Longrightarrow>\<close> real-\<open>C\<^sup>\<infinity>\<close> (\<open>Cinfinity_on\<close>);
  \<^item> (A1) real-analytic at \<open>c\<close> \<open>\<longleftrightarrow>\<close> a local holomorphic extension on a complex ball.

  These are the bridges consumed by the nowhere-dense-zeros workhorse and the analytic
  implicit-function theorem.  All proofs are complete and machine-checked.
\<close>

theory Real_Analytic_Complex
  imports
    "Applied_Math_Analytic.Real_Analytic"
    "HOL-Complex_Analysis.Complex_Analysis"
begin


subsection \<open>(A3a) A CR-linear self-map of the plane is multiplication by a scalar\<close>

definition CR_linear :: "(complex \<Rightarrow> complex) \<Rightarrow> bool" where
  "CR_linear L \<longleftrightarrow> bounded_linear L \<and> (\<forall>v. L (\<i> * v) = \<i> * L v)"

lemma CR_linear_is_mult:
  assumes "CR_linear L"
  shows "\<exists>a. \<forall>v. L v = a * v"
proof -
  from assms have bl: "bounded_linear L" and cr: "\<And>v. L (\<i> * v) = \<i> * L v"
    by (auto simp: CR_linear_def)
  interpret bounded_linear L by (rule bl)
  have Lof: "L (complex_of_real r) = complex_of_real r * L 1" for r
  proof -
    have "L (complex_of_real r) = L (r *\<^sub>R 1)"
      by (simp add: scaleR_conv_of_real)
    also have "\<dots> = r *\<^sub>R L 1"
      by (rule scaleR)
    also have "\<dots> = complex_of_real r * L 1"
      by (simp add: scaleR_conv_of_real)
    finally show ?thesis .
  qed
  have "L v = L 1 * v" for v
  proof -
    have decomp: "v = complex_of_real (Re v) + \<i> * complex_of_real (Im v)"
      by (simp add: complex_eq_iff)
    have "L v = L (complex_of_real (Re v) + \<i> * complex_of_real (Im v))"
      using decomp by simp
    also have "\<dots> = L (complex_of_real (Re v)) + L (\<i> * complex_of_real (Im v))"
      by (rule add)
    also have "\<dots> = L (complex_of_real (Re v)) + \<i> * L (complex_of_real (Im v))"
      using cr by simp
    also have "\<dots> = complex_of_real (Re v) * L 1 + \<i> * (complex_of_real (Im v) * L 1)"
      by (simp add: Lof)
    also have "\<dots> = L 1 * (complex_of_real (Re v) + \<i> * complex_of_real (Im v))"
      by (simp add: algebra_simps)
    also have "\<dots> = L 1 * v"
      using decomp by simp
    finally show ?thesis .
  qed
  thus ?thesis by blast
qed


subsection \<open>(A3) Several-variable Cauchy--Riemann criterion\<close>

theorem CauchyRiemann_imp_holomorphic:
  fixes f :: "complex \<Rightarrow> complex"
  assumes Sopen: "open S"
    and diff: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative (L x)) (at x)"
    and CR:   "\<And>x. x \<in> S \<Longrightarrow> CR_linear (L x)"
  shows "f holomorphic_on S"
proof -
  have "f field_differentiable (at x)" if xS: "x \<in> S" for x
  proof -
    from CR[OF xS] obtain a where a: "\<And>v. L x v = a * v"
      using CR_linear_is_mult by blast
    from diff[OF xS] have "(f has_derivative (L x)) (at x)" .
    moreover have "L x = (*) a"
      using a by auto
    ultimately have "(f has_derivative (*) a) (at x)" by simp
    hence "(f has_field_derivative a) (at x)"
      by (simp add: has_field_derivative_def mult.commute)
    thus ?thesis
      using field_differentiable_def by blast
  qed
  thus ?thesis
    using Sopen by (simp add: holomorphic_on_open field_differentiable_def)
qed


subsection \<open>(A2) Holomorphic implies real-$C^\infty$\<close>

text \<open>A transfer principle for \<^const>\<open>Ck_at\<close>: it only depends on the values of the function
  on an open neighbourhood of the point.  Mirror of
  @{thm [source] k_times_Fr_differentiable_at_transfer_open}.\<close>

lemma Ck_at_transfer_open:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
    and Hf: "Ck_at k f x"
  shows "Ck_at k g x"
  using U eq Hf
proof (induction k arbitrary: f g x U)
  case 0
  then have cf: "continuous (at x) f" by simp
  have ev: "eventually (\<lambda>y. f y = g y) (nhds x)"
    using 0 by (simp add: eventually_nhds, blast)
  have "isCont g x"
    using cf ev isCont_cong by blast
  then show ?case by simp
next
  case (Suc k)

  from Suc.prems(4) obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding Ck_at.simps(2)
    by blast

  let ?C = "A \<inter> U"
  have C: "open ?C" "x \<in> ?C"
    using A Suc.prems by auto

  have neigh: "\<forall>y\<in>?C. Ck_at k g y"
    by (metis A(3) Int_iff Suc.IH Suc.prems(1,3))

  have dg: "g differentiable (at x)"
    by (metis Suc.prems(1,2,3) df differentiable_eqI)

  have Dg: "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative g (at y) v) x"
  proof
    fix v
    show "Ck_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    proof (cases k)
      case 0
      \<comment> \<open>Need continuity of the directional derivative at \<open>x\<close>; transfer it from \<open>f\<close>.\<close>
      have Df0: "Ck_at 0 (\<lambda>y. frechet_derivative f (at y) v) x"
        using Df 0 by blast
      have eqD0: "\<And>y. y \<in> ?C \<Longrightarrow>
                   frechet_derivative f (at y) v = frechet_derivative g (at y) v"
      proof -
        fix y assume yC: "y \<in> ?C"
        hence yU: "y \<in> U" by auto
        \<comment> \<open>\<open>f\<close> and \<open>g\<close> agree on the open set \<open>U\<close>, so they have the same
            Fréchet derivative at \<open>y\<close>, with no differentiability needed.\<close>
        have iff: "(f has_derivative D) (at y) \<longleftrightarrow> (g has_derivative D) (at y)" for D
        proof
          assume "(f has_derivative D) (at y)"
          thus "(g has_derivative D) (at y)"
            using has_derivative_transform_within_open[OF _ Suc.prems(1) yU]
                  Suc.prems(3) by blast
        next
          assume "(g has_derivative D) (at y)"
          thus "(f has_derivative D) (at y)"
            using has_derivative_transform_within_open[OF _ Suc.prems(1) yU]
                  Suc.prems(3) by (metis (no_types, lifting))
        qed
        have "frechet_derivative f (at y) = frechet_derivative g (at y)"
          unfolding frechet_derivative_def iff ..
        then show "frechet_derivative f (at y) v = frechet_derivative g (at y) v"
          by simp
      qed
      show ?thesis
        using Suc.IH[OF C(1,2), of
            "\<lambda>y. frechet_derivative f (at y) v"
            "\<lambda>y. frechet_derivative g (at y) v"]
          eqD0 Df0 0 by blast
    next
      case (Suc j)

      have eqD:
        "\<And>y. y \<in> ?C \<Longrightarrow> frechet_derivative f (at y) v = frechet_derivative g (at y) v"
      proof -
        fix y
        assume yC: "y \<in> ?C"
        hence yA: "y \<in> A" and yU: "y \<in> U" by auto

        have fy: "Ck_at (Suc j) f y"
          using A(3) Suc yA by blast
        hence dfy: "f differentiable (at y)"
          by simp

        have evy: "eventually (\<lambda>z. f z = g z) (nhds y)"
          using Suc.prems(1) yU Suc.prems(3)
          by (simp add: eventually_nhds, auto)

        have "(f has_derivative frechet_derivative f (at y)) (at y)"
          by (simp add: dfy frechet_derivative_worksI)
        then have "(g has_derivative frechet_derivative f (at y)) (at y)"
          using Suc.prems(1,3) has_derivative_transfer_on_open yU by blast
        moreover have "g differentiable (at y)"
          by (metis Suc.prems(1,3) dfy differentiable_eqI yU)
        hence "(g has_derivative frechet_derivative g (at y)) (at y)"
          by (simp add: frechet_derivative_worksI)
        ultimately have "frechet_derivative f (at y) = frechet_derivative g (at y)"
          by (rule has_derivative_unique)
        then show "frechet_derivative f (at y) v = frechet_derivative g (at y) v"
          by simp
      qed

      have "Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x"
        using Df by blast
      then show ?thesis
        using Suc.IH[OF C(1,2), of
            "\<lambda>y. frechet_derivative f (at y) v"
            "\<lambda>y. frechet_derivative g (at y) v"]
          eqD
        by blast
    qed
  qed

  show "Ck_at (Suc k) g x"
    unfolding Ck_at.simps(2)
    using C neigh dg Dg by blast
qed

text \<open>The real Fréchet derivative of a holomorphic map is \<open>v \<mapsto> deriv f x * v\<close>.\<close>

lemma frechet_derivative_holomorphic:
  assumes holf: "f holomorphic_on U" and U: "open U" and xU: "x \<in> U"
  shows "frechet_derivative f (at x) v = deriv f x * v"
proof -
  have "(f has_field_derivative deriv f x) (at x)"
    using holf U xU by (simp add: holomorphic_derivI)
  hence "(f has_derivative (*) (deriv f x)) (at x)"
    by (rule has_field_derivative_imp_has_derivative)
  hence "(*) (deriv f x) = frechet_derivative f (at x)"
    by (rule frechet_derivative_at)
  hence "frechet_derivative f (at x) v = (*) (deriv f x) v" by simp
  thus ?thesis by simp
qed

lemma holomorphic_imp_differentiable_real:
  assumes holf: "f holomorphic_on U" and U: "open U" and xU: "x \<in> U"
  shows "f differentiable (at x)"
proof -
  have "(f has_field_derivative deriv f x) (at x)"
    using holf U xU by (simp add: holomorphic_derivI)
  hence "(f has_derivative (*) (deriv f x)) (at x)"
    by (rule has_field_derivative_imp_has_derivative)
  thus ?thesis by (auto simp: differentiable_def)
qed

text \<open>Main induction: a constant multiple of a holomorphic function is \<open>C\<^sup>k\<close> at each
  point, for every \<open>k\<close>.\<close>

lemma holomorphic_const_mult_Ck_at:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "f holomorphic_on U" and "open U" and "x \<in> U"
  shows "Ck_at k (\<lambda>y. c * f y) x"
  using assms
proof (induction k arbitrary: f x c)
  case 0
  have "continuous (at x) (\<lambda>y. c * f y)"
  proof -
    have "continuous_on U f"
      using 0 holomorphic_on_imp_continuous_on by blast
    hence "continuous (at x) f"
      using 0 by (simp add: continuous_on_eq_continuous_at)
    thus ?thesis by (intro continuous_intros)
  qed
  thus ?case by simp
next
  case (Suc k)
  note holf = Suc.prems(1) and openU = Suc.prems(2) and xU = Suc.prems(3)

  \<comment> \<open>The scaled map is holomorphic, hence differentiable on \<open>U\<close>.\<close>
  have holcf: "(\<lambda>y. c * f y) holomorphic_on U"
    using holf by (intro holomorphic_intros)

  \<comment> \<open>(i) Neighbourhood: \<open>Ck_at k\<close> holds throughout \<open>U\<close> by the induction hypothesis.\<close>
  have nbhd: "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k (\<lambda>y. c * f y) y)"
  proof (intro exI[of _ U] conjI ballI)
    fix y assume "y \<in> U"
    show "Ck_at k (\<lambda>z. c * f z) y"
      using Suc.IH[OF holf openU \<open>y \<in> U\<close>] .
  qed (use openU xU in auto)

  \<comment> \<open>(ii) Differentiability at \<open>x\<close>.\<close>
  have diff: "(\<lambda>y. c * f y) differentiable (at x)"
    using holomorphic_imp_differentiable_real[OF holcf openU xU] .

  \<comment> \<open>(iii) The directional derivative map is \<open>C\<^sup>k\<close> at \<open>x\<close>.\<close>
  have derivs: "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative (\<lambda>z. c * f z) (at y) v) x"
  proof
    fix v
    \<comment> \<open>On \<open>U\<close> the directional derivative equals \<open>(c * v) * deriv f y\<close>.\<close>
    have eqd: "\<And>y. y \<in> U \<Longrightarrow>
                 frechet_derivative (\<lambda>z. c * f z) (at y) v = (c * v) * deriv f y"
    proof -
      fix y assume yU: "y \<in> U"
      have "frechet_derivative (\<lambda>z. c * f z) (at y) v = deriv (\<lambda>z. c * f z) y * v"
        using frechet_derivative_holomorphic[OF holcf openU yU] by simp
      also have "deriv (\<lambda>z. c * f z) y = c * deriv f y"
        using holf openU yU
        by (simp add: deriv_cmult holomorphic_on_imp_differentiable_at)
      finally show "frechet_derivative (\<lambda>z. c * f z) (at y) v = (c * v) * deriv f y"
        by (simp add: algebra_simps)
    qed
    \<comment> \<open>\<open>deriv f\<close> is holomorphic on \<open>U\<close>, so \<open>(c*v) * deriv f\<close> is \<open>C\<^sup>k\<close> by the IH.\<close>
    have holderiv: "deriv f holomorphic_on U"
      using holf openU by (rule holomorphic_deriv)
    have base: "Ck_at k (\<lambda>y. (c * v) * deriv f y) x"
      using Suc.IH[OF holderiv openU xU] .
    show "Ck_at k (\<lambda>y. frechet_derivative (\<lambda>z. c * f z) (at y) v) x"
      by (rule Ck_at_transfer_open[OF openU xU _ base]) (simp add: eqd)
  qed

  show ?case
    unfolding Ck_at.simps(2)
    using nbhd diff derivs by blast
qed

theorem holomorphic_imp_Cinfinity_on:
  assumes "f holomorphic_on U" and "open U"
  shows "Cinfinity_on f U"
  unfolding Cinfinity_on_def Cinfinity_at_def
proof (intro conjI ballI allI)
  show "open U" by (rule assms(2))
next
  fix x :: complex and k assume xU: "x \<in> U"
  have "Ck_at k (\<lambda>y. 1 * f y) x"
    using holomorphic_const_mult_Ck_at[OF assms(1) assms(2) xU] .
  thus "Ck_at k f x" by simp
qed



definition has_holo_extension_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "has_holo_extension_at f c \<longleftrightarrow>
     (\<exists>r>0. \<exists>g. g holomorphic_on ball (complex_of_real c) r
                \<and> (\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow> g (complex_of_real x) = complex_of_real (f x)))"


lemma real_analytic_at_1d_imp_holo_extension:
  fixes f :: "real \<Rightarrow> real"
  assumes "real_analytic_at_1d f c"
  shows "has_holo_extension_at f c"
proof -
  from assms obtain r where r: "0 < r"
    and TS: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow>
              (\<lambda>n. (deriv ^^ n) f c / fact n * (x - c) ^ n) sums f x"
    unfolding real_analytic_at_1d_def by blast
  \<comment> \<open>the complex coefficients (same as the real Taylor coefficients)\<close>
  define b :: "nat \<Rightarrow> complex" where "b = (\<lambda>n. complex_of_real ((deriv ^^ n) f c / fact n))"
  \<comment> \<open>the complex sum function on the ball; well-defined by summability\<close>
  define g :: "complex \<Rightarrow> complex" where
    "g = (\<lambda>w. \<Sum>n. b n * (w - complex_of_real c) ^ n)"
  \<comment> \<open>The complex power series is summable at every complex point of the ball.\<close>
  have summ_complex: "summable (\<lambda>n. b n * (w - complex_of_real c) ^ n)"
    if w: "w \<in> ball (complex_of_real c) r" for w
  proof -
    have nw: "norm (w - complex_of_real c) < r"
      using w by (simp add: dist_norm norm_minus_commute)
    \<comment> \<open>pick an intermediate real radius @{term s}\<close>
    define s where "s = (norm (w - complex_of_real c) + r) / 2"
    have s_pos: "0 < s"
    proof -
      have "0 < norm (w - complex_of_real c) + r"
        using r norm_ge_zero[of "w - complex_of_real c"] by linarith
      thus ?thesis by (simp add: s_def)
    qed
    have s_lt_r: "s < r" using nw by (simp add: s_def)
    have nw_lt_s: "norm (w - complex_of_real c) < s"
      using nw by (simp add: s_def)
    \<comment> \<open>real series converges at @{term "c + s"}, since @{term "\<bar>s\<bar> < r"}\<close>
    have "\<bar>(c + s) - c\<bar> < r" using s_pos s_lt_r by simp
    from TS[OF this] have realsum:
      "summable (\<lambda>n. (deriv ^^ n) f c / fact n * ((c + s) - c) ^ n)"
      by (rule sums_summable)
    have realsum': "summable (\<lambda>n. (deriv ^^ n) f c / fact n * s ^ n)"
      using realsum by simp
    \<comment> \<open>cast to complex: @{term "b n * (of_real s)^n"} is summable\<close>
    have cast: "summable (\<lambda>n. b n * (complex_of_real s) ^ n)"
    proof -
      have "(\<lambda>n. of_real ((deriv ^^ n) f c / fact n * s ^ n) :: complex)
              = (\<lambda>n. b n * (complex_of_real s) ^ n)"
        by (simp only: b_def of_real_mult of_real_power)
      moreover have "summable (\<lambda>n. of_real ((deriv ^^ n) f c / fact n * s ^ n) :: complex)"
        using realsum' by (rule summable_of_real)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>powser_inside upgrades to summability strictly inside\<close>
    have "norm (w - complex_of_real c) < norm (complex_of_real s)"
      using nw_lt_s s_pos by simp
    from powser_inside[OF cast this]
    show ?thesis .
  qed
  \<comment> \<open>hence at each ball point the series sums to @{term "g w"}\<close>
  have sums_g: "(\<lambda>n. b n * (w - complex_of_real c) ^ n) sums g w"
    if w: "w \<in> ball (complex_of_real c) r" for w
    using summ_complex[OF w] by (simp add: g_def summable_sums)
  \<comment> \<open>holomorphy from power_series_holomorphic\<close>
  have holo: "g holomorphic_on ball (complex_of_real c) r"
  proof (rule power_series_holomorphic)
    fix w :: complex assume "w \<in> ball (complex_of_real c) r"
    thus "(\<lambda>n. b n * (w - complex_of_real c) ^ n) sums g w"
      by (rule sums_g)
  qed
  \<comment> \<open>on the real axis, the series sums to @{term "of_real (f x)"}\<close>
  have realaxis: "g (complex_of_real x) = complex_of_real (f x)"
    if x: "\<bar>x - c\<bar> < r" for x
  proof -
    have wball: "complex_of_real x \<in> ball (complex_of_real c) r"
      using x by (simp add: dist_norm norm_minus_commute flip: of_real_diff)
    have "(\<lambda>n. b n * (complex_of_real x - complex_of_real c) ^ n) sums g (complex_of_real x)"
      by (rule sums_g[OF wball])
    moreover have
      "(\<lambda>n. b n * (complex_of_real x - complex_of_real c) ^ n)
         = (\<lambda>n. complex_of_real ((deriv ^^ n) f c / fact n * (x - c) ^ n))"
      by (simp only: b_def of_real_mult of_real_power flip: of_real_diff)
    ultimately have
      "(\<lambda>n. complex_of_real ((deriv ^^ n) f c / fact n * (x - c) ^ n))
         sums g (complex_of_real x)" by simp
    moreover have
      "(\<lambda>n. complex_of_real ((deriv ^^ n) f c / fact n * (x - c) ^ n))
         sums complex_of_real (f x)"
      using TS[OF x] by (rule sums_of_real)
    ultimately show ?thesis by (rule sums_unique2)
  qed
  show ?thesis
    unfolding has_holo_extension_at_def
    using r holo realaxis by blast
qed


text \<open>Helper: an arbitrary convergent real power series about \<open>c\<close> on \<open>ball c r\<close> makes
  \<open>f\<close> real-analytic \<^emph>\<open>at\<close> \<open>c\<close>.  This replays the term-by-term differentiation / coefficient
  identification of the forward part of \<open>real_analytic_on_1d_iff\<close>, but starting from an
  arbitrary power series rather than the multivariate \<open>has_sum\<close>; it identifies the
  coefficients with the Taylor coefficients and establishes smoothness.\<close>



lemma holo_extension_imp_real_analytic_at_1d:
  fixes f :: "real \<Rightarrow> real"
  assumes "has_holo_extension_at f c"
  shows "real_analytic_at_1d f c"
proof -
  from assms obtain r g where r: "0 < r"
    and holo: "g holomorphic_on ball (complex_of_real c) r"
    and onaxis: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow> g (complex_of_real x) = complex_of_real (f x)"
    unfolding has_holo_extension_at_def by blast
  \<comment> \<open>the real coefficients are the real parts of the complex Taylor coefficients\<close>
  define A :: "nat \<Rightarrow> complex" where
    "A = (\<lambda>n. (deriv ^^ n) g (complex_of_real c) / fact n)"
  define a :: "nat \<Rightarrow> real" where "a = (\<lambda>n. Re (A n))"
  \<comment> \<open>the real power series with coefficients @{term a} sums to @{term "f x"} on the ball\<close>
  have PS: "(\<lambda>n. a n * (x - c) ^ n) sums f x" if x: "\<bar>x - c\<bar> < r" for x
  proof -
    have wball: "complex_of_real x \<in> ball (complex_of_real c) r"
      using x by (simp add: dist_norm norm_minus_commute flip: of_real_diff)
    \<comment> \<open>complex Taylor series of @{term g} at the real point\<close>
    have cseries: "(\<lambda>n. A n * (complex_of_real x - complex_of_real c) ^ n)
                     sums g (complex_of_real x)"
      unfolding A_def by (rule holomorphic_power_series[OF holo wball])
    have eqf: "g (complex_of_real x) = complex_of_real (f x)" by (rule onaxis[OF x])
    \<comment> \<open>rewrite the complex terms and take real parts\<close>
    have term_eq: "A n * (complex_of_real x - complex_of_real c) ^ n
                     = complex_of_real (a n * (x - c) ^ n)
                       + \<i> * complex_of_real (Im (A n) * (x - c) ^ n)" for n
    proof -
      have pw: "(complex_of_real x - complex_of_real c) ^ n
                  = complex_of_real ((x - c) ^ n)"
        by (simp flip: of_real_diff of_real_power)
      have "A n * (complex_of_real x - complex_of_real c) ^ n
              = A n * complex_of_real ((x - c) ^ n)" by (simp only: pw)
      also have "\<dots> = complex_of_real (Re (A n) * (x - c) ^ n)
                       + \<i> * complex_of_real (Im (A n) * (x - c) ^ n)"
        by (simp add: complex_eq_iff)
      finally show ?thesis by (simp add: a_def)
    qed
    have cseries': "(\<lambda>n. complex_of_real (a n * (x - c) ^ n)
                          + \<i> * complex_of_real (Im (A n) * (x - c) ^ n))
                      sums complex_of_real (f x)"
      using cseries by (simp add: term_eq eqf)
    \<comment> \<open>take real parts\<close>
    have "(\<lambda>n. Re (complex_of_real (a n * (x - c) ^ n)
                   + \<i> * complex_of_real (Im (A n) * (x - c) ^ n)))
            sums Re (complex_of_real (f x))"
      by (rule sums_Re[OF cseries'])
    thus ?thesis by simp
  qed
  show ?thesis by (rule real_powser_imp_real_analytic_at_1d[OF r PS])
qed


theorem real_analytic_at_1d_iff_holo_extension:
  fixes f :: "real \<Rightarrow> real"
  shows "real_analytic_at_1d f c \<longleftrightarrow> has_holo_extension_at f c"
  using real_analytic_at_1d_imp_holo_extension holo_extension_imp_real_analytic_at_1d
  by blast

section \<open>Elementary real-analytic functions: \<open>sin\<close>, \<open>cos\<close>, and the \<open>sinc\<close> kernel\<close>

text \<open>The dipole fields (\<open>cvec_dip\<close>, \<open>gain_dip = gdip \<circ> ($1)\<close>, the moment phases, hence
  \<open>gradU\<close> and \<open>mstarg\<close>) are polynomials in \<open>sin\<close>/\<open>cos\<close>/\<open>gsinc\<close> of affine and bilinear
  arguments.  This theory supplies the missing foundation: \<open>sin\<close>, \<open>cos\<close> and the entire
  \<open>sinc\<close> kernel are \<open>real_analytic_on UNIV\<close>, obtained through the proven complexification
  bridge @{thm real_analytic_at_1d_iff_holo_extension} + @{thm real_analytic_on_1d_iff},
  with the classical holomorphic witnesses from \<open>HOL-Complex_Analysis\<close>.  Nothing here
  depends on the dipole development: these are reusable \<open>Real_Analytic_Complex\<close>-level
  facts.\<close>

subsection \<open>\<open>sin\<close> and \<open>cos\<close>\<close>

lemma has_holo_extension_at_sin:
  fixes c :: real
  shows "has_holo_extension_at sin c"
proof -
  have holo: "(sin :: complex \<Rightarrow> complex) holomorphic_on ball (complex_of_real c) 1"
    by (intro holomorphic_intros)
  have agree: "\<forall>x. \<bar>x - c\<bar> < 1 \<longrightarrow> sin (complex_of_real x) = complex_of_real (sin x)"
    by (simp add: sin_of_real)
  have "\<exists>g. g holomorphic_on ball (complex_of_real c) 1
          \<and> (\<forall>x. \<bar>x - c\<bar> < 1 \<longrightarrow> g (complex_of_real x) = complex_of_real (sin x))"
    using holo agree by blast
  thus ?thesis
    unfolding has_holo_extension_at_def
    by (intro exI[of _ 1]) simp
qed

lemma has_holo_extension_at_cos:
  fixes c :: real
  shows "has_holo_extension_at cos c"
proof -
  have holo: "(cos :: complex \<Rightarrow> complex) holomorphic_on ball (complex_of_real c) 1"
    by (intro holomorphic_intros)
  have agree: "\<forall>x. \<bar>x - c\<bar> < 1 \<longrightarrow> cos (complex_of_real x) = complex_of_real (cos x)"
    by (simp add: cos_of_real)
  have "\<exists>g. g holomorphic_on ball (complex_of_real c) 1
          \<and> (\<forall>x. \<bar>x - c\<bar> < 1 \<longrightarrow> g (complex_of_real x) = complex_of_real (cos x))"
    using holo agree by blast
  thus ?thesis
    unfolding has_holo_extension_at_def
    by (intro exI[of _ 1]) simp
qed

theorem real_analytic_on_sin: "real_analytic_on (sin :: real \<Rightarrow> real) UNIV"
  unfolding real_analytic_on_1d_iff
  by (simp add: real_analytic_at_1d_iff_holo_extension has_holo_extension_at_sin)

theorem real_analytic_on_cos: "real_analytic_on (cos :: real \<Rightarrow> real) UNIV"
  unfolding real_analytic_on_1d_iff
  by (simp add: real_analytic_at_1d_iff_holo_extension has_holo_extension_at_cos)

subsection \<open>The entire \<open>sinc\<close> kernel\<close>

text \<open>\<open>rsinc\<close> is the removable-singularity kernel through which the dipole gain
  \<open>gdip\<close> factors (\<open>gsinc\<close> in \<open>Nonemptiness_Robust1\<close> is definitionally identical;
  the bridge theory will transport by \<open>ext\<close>).\<close>

definition rsinc :: "real \<Rightarrow> real" where
  "rsinc x = (if x = 0 then 1 else sin x / x)"

lemma complex_sinc_tendsto: "(\<lambda>z::complex. sin z / z) \<midarrow>0\<rightarrow> 1"
proof -
  have "(sin has_field_derivative cos 0) (at (0::complex))"
    by (rule DERIV_sin)
  hence "((\<lambda>z::complex. (sin z - sin 0) / (z - 0)) \<longlongrightarrow> cos 0) (at 0)"
    by (simp add: has_field_derivative_iff)
  thus ?thesis by simp
qed

lemma complex_sinc_holomorphic:
  "(\<lambda>z::complex. if z = 0 then 1 else sin z / z) holomorphic_on A"
proof -
  have "(\<lambda>z::complex. if z = 0 then 1 else sin z / z) holomorphic_on UNIV"
    by (rule removable_singularity)
       (auto intro!: holomorphic_intros simp: complex_sinc_tendsto)
  thus ?thesis by (rule holomorphic_on_subset) simp
qed

lemma has_holo_extension_at_rsinc:
  fixes c :: real
  shows "has_holo_extension_at rsinc c"
proof -
  have holo: "(\<lambda>z::complex. if z = 0 then 1 else sin z / z)
                holomorphic_on ball (complex_of_real c) 1"
    by (rule complex_sinc_holomorphic)
  have agree: "\<forall>x. \<bar>x - c\<bar> < 1 \<longrightarrow>
        (if complex_of_real x = 0 then 1 else sin (complex_of_real x) / complex_of_real x)
          = complex_of_real (rsinc x)"
    by (auto simp: rsinc_def sin_of_real)
  have "\<exists>g. g holomorphic_on ball (complex_of_real c) 1
          \<and> (\<forall>x. \<bar>x - c\<bar> < 1 \<longrightarrow> g (complex_of_real x) = complex_of_real (rsinc x))"
    using holo agree by blast
  thus ?thesis
    unfolding has_holo_extension_at_def
    by (intro exI[of _ 1]) simp
qed

theorem real_analytic_on_rsinc: "real_analytic_on rsinc UNIV"
  unfolding real_analytic_on_1d_iff
  by (simp add: real_analytic_at_1d_iff_holo_extension has_holo_extension_at_rsinc)

subsection \<open>Composed forms (the shapes the dipole bridge consumes)\<close>

lemma real_analytic_on_sin_comp:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. sin (f x)) U"
  by (rule real_analytic_on_compose[OF f real_analytic_on_sin subset_UNIV])

lemma real_analytic_on_cos_comp:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. cos (f x)) U"
  by (rule real_analytic_on_compose[OF f real_analytic_on_cos subset_UNIV])

lemma real_analytic_on_rsinc_comp:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. rsinc (f x)) U"
  by (rule real_analytic_on_compose[OF f real_analytic_on_rsinc subset_UNIV])

end
