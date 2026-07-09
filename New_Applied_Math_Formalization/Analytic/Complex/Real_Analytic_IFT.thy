section \<open>The analytic implicit-function theorem via complexification\<close>

text \<open>
  Building on the complexification bridge (\<open>Real_Analytic_Complex\<close>), we assemble the
  real-analytic implicit-function theorem.  The plan:

  \<^item> (B1) The \<open>C\<^sup>1\<close> inverse-function theorem from \<open>HOL-Analysis.Derivative\<close> gives a local
    homeomorphism inverse with a derivative; we restate the precise HOL theorem we reuse.
  \<^item> (B2) The inverse of a (locally injective) holomorphic map is holomorphic
    (\<^theory_text>\<open>holomorphic_has_inverse\<close> from \<open>Conformal_Mappings\<close>); via A1/A2 this upgrades the
    \<open>C\<^sup>1\<close> inverse of a real-analytic map to a real-analytic inverse.
  \<^item> (B3) Real restriction: a holomorphic local inverse restricted to the real axis is
    real-analytic (A1 backward).
  \<^item> (C) Assemble: solve \<open>F (x, y) = 0\<close> by inverting the second slot (real-analytic local
    inverse) and composing -- the classical reduction of the implicit-function theorem to
    the inverse-function theorem.

  The final theorem \<open>real_analytic_implicit_function\<close> matches verbatim the statement
  left as \<open>proof hole\<close> in \<open>Real_Analytic\<close>.
\<close>

theory Real_Analytic_IFT
  imports
    Real_Analytic_Complex
    "Applied_Math_Analytic_Inverse.Real_Analytic_Inverse"
    "Applied_Math_HigherDiff.Ck1_C1_Bridge"
begin


subsection \<open>(B1) The reused $C^1$ inverse-function theorem\<close>

text \<open>
  We reuse, verbatim, \<^theory_text>\<open>inverse_function_theorem\<close> from
  \<^file>\<open>~~/src/HOL/Analysis/Derivative.thy\<close> (line 3031):

  \<^theory_text>\<open>
  theorem inverse_function_theorem:
    fixes f::"'a::euclidean_space \<Rightarrow> 'a" and f'::"'a \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'a)"
    assumes "open U"
      and derf: "\<And>x. x \<in> U \<Longrightarrow> (f has_derivative (blinfun_apply (f' x))) (at x)"
      and contf:  "continuous_on U f'"
      and "x0 \<in> U"
      and invf: "invf o\<^sub>L f' x0 = id_blinfun"
    obtains U' V g g' where "open U'" "U' \<subseteq> U" "x0 \<in> U'" "open V" "f x0 \<in> V"
      "homeomorphism U' V f g"
      "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (g' y)) (at y)"
      "\<And>y. y \<in> V \<Longrightarrow> g' y = inv (blinfun_apply (f'(g y)))"
      "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (f'(g y)))"
  \<close>

  The following is a thin convenience wrapper packaging just the existence of a local
  homeomorphism inverse \<open>g\<close> with a derivative, in the form the assembly consumes.  It is a
  direct application of the HOL theorem (assembly-only, no new mathematics).
\<close>

lemma C1_local_inverse:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
    and f' :: "'a \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'a)"
  assumes U: "open U"
    and derf: "\<And>x. x \<in> U \<Longrightarrow> (f has_derivative (blinfun_apply (f' x))) (at x)"
    and contf: "continuous_on U f'"
    and x0: "x0 \<in> U"
    and invf: "invf o\<^sub>L f' x0 = id_blinfun"
  obtains U' V g where
    "open U'" "U' \<subseteq> U" "x0 \<in> U'" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (inv (blinfun_apply (f'(g y))))) (at y)"
proof -
  obtain U' V g g' where
    P: "open U'" "U' \<subseteq> U" "x0 \<in> U'" "open V" "f x0 \<in> V"
       "homeomorphism U' V f g"
       "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (g' y)) (at y)"
       "\<And>y. y \<in> V \<Longrightarrow> g' y = inv (blinfun_apply (f'(g y)))"
       "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (f'(g y)))"
    using inverse_function_theorem[OF U derf contf x0 invf] by blast
  have derg': "(g has_derivative (inv (blinfun_apply (f'(g y))))) (at y)" if "y \<in> V" for y
    using P(7)[OF that] P(8)[OF that] by simp
  show ?thesis
    by (rule that[of U' V g]) (use P derg' in blast)+
qed


subsection \<open>(B2) Inverse of a holomorphic map is holomorphic\<close>

text \<open>
  We reuse \<^theory_text>\<open>holomorphic_has_inverse\<close> from
  \<^file>\<open>~~/src/HOL/Complex_Analysis/Conformal_Mappings.thy\<close> (line 1092):

  \<^theory_text>\<open>
  proposition holomorphic_has_inverse:
    assumes holf: "f holomorphic_on S" and "open S" and injf: "inj_on f S"
    obtains g where "g holomorphic_on (f ` S)"
      "\<And>z. z \<in> S \<Longrightarrow> deriv f z * deriv g (f z) = 1"
      "\<And>z. z \<in> S \<Longrightarrow> g(f z) = z"
  \<close>

  This is exactly the holomorphic open-mapping inverse we need; the wrapper below names it.
\<close>

lemma holo_inverse_holomorphic:
  assumes "f holomorphic_on S" and "open S" and "inj_on f S"
  obtains g where "g holomorphic_on (f ` S)" "\<And>z. z \<in> S \<Longrightarrow> g (f z) = z"
proof -
  obtain g where "g holomorphic_on (f ` S)"
    and "\<And>z. z \<in> S \<Longrightarrow> deriv f z * deriv g (f z) = 1"
    and "\<And>z. z \<in> S \<Longrightarrow> g (f z) = z"
    using holomorphic_has_inverse[OF assms] by blast
  then show ?thesis using that by blast
qed


subsection \<open>(B3) Restrict a holomorphic inverse to the reals\<close>

text \<open>
  If a holomorphic local inverse \<open>g\<close> maps real points to real points near \<open>c\<close>, its real
  restriction \<open>\<lambda>x. Re (g (of_real x))\<close> is real-analytic at \<open>c\<close> (apply A1 backward,
  \<open>holo_extension_imp_real_analytic_at_1d\<close>).  Stated for the scalar slot; the
  several-variable version is reduced to coordinates in the assembly.
\<close>

lemma holo_inverse_restrict_real_analytic:
  fixes g :: "complex \<Rightarrow> complex"
  assumes "g holomorphic_on ball (complex_of_real c) r" and "r > 0"
    and real: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow> g (complex_of_real x) \<in> \<real>"
  shows "real_analytic_at_1d (\<lambda>x. Re (g (complex_of_real x))) c"
proof -
  have "has_holo_extension_at (\<lambda>x. Re (g (complex_of_real x))) c"
    unfolding has_holo_extension_at_def
  proof (intro exI conjI allI impI)
    show "0 < r" by (rule assms(2))
    show "g holomorphic_on ball (complex_of_real c) r" by (rule assms(1))
    fix x
    assume "\<bar>x - c\<bar> < r"
    thus "g (complex_of_real x) = complex_of_real (Re (g (complex_of_real x)))"
      using real[of x] by simp
  qed
  thus ?thesis
    by (rule holo_extension_imp_real_analytic_at_1d)
qed

lemma holo_extension_axis_deriv:
  fixes f :: "real \<Rightarrow> real" and G :: "complex \<Rightarrow> complex"
  assumes holo: "G holomorphic_on ball (complex_of_real c) r"
    and r: "0 < r"
    and axis: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow> G (complex_of_real x) = complex_of_real (f x)"
    and derf: "(f has_field_derivative L) (at c)"
  shows "deriv G (complex_of_real c) = complex_of_real L"
proof -
  have cball: "complex_of_real c \<in> ball (complex_of_real c) r"
    using r by simp
  have Gder: "(G has_field_derivative deriv G (complex_of_real c)) (at (complex_of_real c))"
    using holo cball by (rule holomorphic_derivI[OF _ open_ball])
  have of_real_der: "((\<lambda>x::real. complex_of_real x) has_vector_derivative 1) (at c)"
    by (auto intro!: derivative_eq_intros simp: has_real_derivative_iff_has_vector_derivative)
  have axis_der:
    "((\<lambda>x. G (complex_of_real x)) has_vector_derivative deriv G (complex_of_real c)) (at c)"
    using field_vector_diff_chain_at[OF of_real_der Gder]
    by (simp add: comp_def)
  have axis_der':
    "((\<lambda>x. complex_of_real (f x)) has_vector_derivative deriv G (complex_of_real c)) (at c)"
  proof (rule has_vector_derivative_transform_within_open[OF axis_der])
    show "open {x. \<bar>x - c\<bar> < r}"
    proof -
      have "{x. \<bar>x - c\<bar> < r} = ball c r"
        by (auto simp: dist_real_def abs_minus_commute)
      thus ?thesis by simp
    qed
    show "c \<in> {x. \<bar>x - c\<bar> < r}"
      using r by simp
    fix x assume "x \<in> {x. \<bar>x - c\<bar> < r}"
    thus "G (complex_of_real x) = complex_of_real (f x)"
      by (simp add: axis)
  qed
  have f_der_vec: "(f has_vector_derivative L) (at c)"
    using derf by (simp add: has_real_derivative_iff_has_vector_derivative)
  have of_real_der_fc: "((\<lambda>x::real. complex_of_real x) has_vector_derivative 1) (at (f c))"
    by (auto intro!: derivative_eq_intros simp: has_real_derivative_iff_has_vector_derivative)
  have f_axis_der:
    "((\<lambda>x. complex_of_real (f x)) has_vector_derivative complex_of_real L) (at c)"
    using vector_diff_chain_at[OF f_der_vec of_real_der_fc]
    by (simp add: comp_def scaleR_conv_of_real)
  show ?thesis
    by (rule vector_derivative_unique_at[OF axis_der' f_axis_der])
qed

lemma real_analytic_at_1d_transform_near:
  fixes f g :: "real \<Rightarrow> real"
  assumes ana: "real_analytic_at_1d f c"
    and e: "0 < e"
    and eq: "\<And>x. \<bar>x - c\<bar> < e \<Longrightarrow> g x = f x"
  shows "real_analytic_at_1d g c"
proof -
  from real_analytic_at_1d_imp_holo_extension[OF ana]
  obtain r G where r: "0 < r"
    and holo: "G holomorphic_on ball (complex_of_real c) r"
    and axis: "\<And>x. \<bar>x - c\<bar> < r \<Longrightarrow> G (complex_of_real x) = complex_of_real (f x)"
    unfolding has_holo_extension_at_def by blast
  define s where "s = min r e"
  have s: "0 < s"
    using r e by (simp add: s_def)
  have "has_holo_extension_at g c"
    unfolding has_holo_extension_at_def
  proof (intro exI conjI allI impI)
    show "0 < s" by (rule s)
    show "G holomorphic_on ball (complex_of_real c) s"
      using holo by (rule holomorphic_on_subset) (auto simp: s_def)
    fix x
    assume x: "\<bar>x - c\<bar> < s"
    hence xr: "\<bar>x - c\<bar> < r" and xe: "\<bar>x - c\<bar> < e"
      by (auto simp: s_def)
    show "G (complex_of_real x) = complex_of_real (g x)"
      using axis[OF xr] eq[OF xe] by simp
  qed
  thus ?thesis
    by (rule holo_extension_imp_real_analytic_at_1d)
qed

lemma real_analytic_on_bounded_linear:
  fixes L :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U" and L: "bounded_linear L"
  shows "real_analytic_on L U"
proof -
  interpret L: bounded_linear L by (rule L)
  define e :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where "e = (\<lambda>b c. if c = b then 1 else 0)"
  have e_idx: "e b \<in> ra_idx" if "b \<in> Basis" for b
    using that by (auto simp: e_def ra_idx_def)
  have mono_e: "ra_monomial h (e b) = h \<bullet> b" if "b \<in> Basis" for b h
    using that by (simp add: e_def ra_monomial_def prod.remove)
  have e_inj: "inj_on e Basis"
    by (auto simp: inj_on_def e_def fun_eq_iff)
  have zero_notin: "(czero_idx::'a \<Rightarrow> nat) \<notin> image e Basis"
  proof
    assume "(czero_idx::'a \<Rightarrow> nat) \<in> image e Basis"
    then obtain b where b: "b \<in> Basis" "czero_idx = e b" by blast
    have "(0::nat) = 1"
      using b by (metis czero_idx_def e_def)
    thus False by simp
  qed
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open U" by (rule U)
  next
    fix x0 assume "x0 \<in> U"
    define A where "A = insert (czero_idx::'a \<Rightarrow> nat) (image e Basis)"
    define coeff where
      "coeff = (\<lambda>\<alpha>::'a \<Rightarrow> nat.
        if \<alpha> = czero_idx then L x0 else L (\<Sum>b\<in>Basis. if \<alpha> = e b then b else 0))"
    have finA: "finite A" by (simp add: A_def)
    have Asub: "A \<subseteq> ra_idx"
      using e_idx by (auto simp: A_def czero_idx_in)
    have neutral: "ra_monomial h \<alpha> *\<^sub>R coeff \<alpha> = 0" if a: "\<alpha> \<in> ra_idx - A" for h \<alpha>
    proof -
      have z: "(\<Sum>b\<in>Basis. if \<alpha> = e b then b else 0) = 0"
        using a by (intro sum.neutral) (auto simp: A_def)
      show ?thesis using a z by (simp add: A_def coeff_def)
    qed
    have coeff_e: "coeff (e b) = L b" if b: "b \<in> Basis" for b
    proof -
      have eb_ne: "e b \<noteq> (czero_idx::'a \<Rightarrow> nat)"
        using b zero_notin by (metis image_eqI)
      have "(\<Sum>c\<in>Basis. if e b = e c then c else 0) =
            (\<Sum>c\<in>Basis. if c = b then c else 0)"
        using b e_inj by (intro sum.cong) (auto simp: inj_on_def)
      also have "... = b"
        using b by simp
      finally show ?thesis using eb_ne by (simp add: coeff_def)
    qed
    have sum_img: "(\<Sum>\<alpha>\<in>image e Basis. ra_monomial h \<alpha> *\<^sub>R coeff \<alpha>) = L h" for h
    proof -
      have "(\<Sum>\<alpha>\<in>image e Basis. ra_monomial h \<alpha> *\<^sub>R coeff \<alpha>) =
            (\<Sum>b\<in>Basis. ra_monomial h (e b) *\<^sub>R coeff (e b))"
        by (rule sum.reindex_cong[OF e_inj]) auto
      also have "... = (\<Sum>b\<in>Basis. (h \<bullet> b) *\<^sub>R L b)"
        by (intro sum.cong refl) (simp add: mono_e coeff_e)
      also have "... = L (\<Sum>b\<in>Basis. (h \<bullet> b) *\<^sub>R b)"
        by (simp add: L.sum L.scaleR)
      also have "... = L h"
        by (simp add: euclidean_representation)
      finally show ?thesis .
    qed
    have zero_term: "ra_monomial h (czero_idx::'a \<Rightarrow> nat) *\<^sub>R coeff czero_idx = L x0" for h
      by (simp add: coeff_def czero_idx_def ra_monomial_def)
    have sumA: "(\<Sum>\<alpha>\<in>A. ra_monomial h \<alpha> *\<^sub>R coeff \<alpha>) = L (x0 + h)" for h
    proof -
      have "(\<Sum>\<alpha>\<in>A. ra_monomial h \<alpha> *\<^sub>R coeff \<alpha>) =
            ra_monomial h czero_idx *\<^sub>R coeff czero_idx +
            (\<Sum>\<alpha>\<in>image e Basis. ra_monomial h \<alpha> *\<^sub>R coeff \<alpha>)"
        using zero_notin by (simp add: A_def)
      also have "... = L x0 + L h"
        by (simp add: zero_term sum_img)
      also have "... = L (x0 + h)"
        by (simp add: L.add)
      finally show ?thesis .
    qed
    show "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum L x) ra_idx"
    proof (intro exI[where x=1] conjI exI[where x=coeff] allI impI)
      show "0 < (1::real)" by simp
    next
      fix x assume "dist x x0 < (1::real)"
      have "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R coeff \<alpha>)
          has_sum (\<Sum>\<alpha>\<in>A. ra_monomial (x - x0) \<alpha> *\<^sub>R coeff \<alpha>)) ra_idx"
      proof (rule has_sum_finite_neutralI)
        show "finite A" by (rule finA)
        show "A \<subseteq> ra_idx" by (rule Asub)
        fix \<alpha>
        assume "\<alpha> \<in> ra_idx - A"
        thus "ra_monomial (x - x0) \<alpha> *\<^sub>R coeff \<alpha> = 0"
          by (rule neutral)
      next
        show "(\<Sum>\<alpha>\<in>A. ra_monomial (x - x0) \<alpha> *\<^sub>R coeff \<alpha>) =
              (\<Sum>\<alpha>\<in>A. ra_monomial (x - x0) \<alpha> *\<^sub>R coeff \<alpha>)"
          by (rule refl)
      qed
      thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R coeff \<alpha>) has_sum L x) ra_idx"
        by (simp add: sumA)
    qed
  qed
qed

lemma real_analytic_on_Pair:
  assumes F: "real_analytic_on f U" and G: "real_analytic_on g U"
  shows "real_analytic_on (\<lambda>x. (f x, g x)) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  show ?thesis
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
    show "\<exists>r>0. \<exists>c. \<forall>x. dist x x0 < r \<longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R c \<alpha>) has_sum (f x, g x)) ra_idx"
    proof (intro exI[where x="min r1 r2"] conjI
        exI[where x="\<lambda>\<alpha>. (c1 \<alpha>, c2 \<alpha>)"] allI impI)
      show "0 < min r1 r2" using r1 r2 by simp
    next
      fix x assume d: "dist x x0 < min r1 r2"
      have t1: "((\<lambda>A. \<Sum>\<alpha>\<in>A. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>) \<longlongrightarrow> f x)
          (finite_subsets_at_top ra_idx)"
        using F1[of x] d unfolding has_sum_def by simp
      have t2: "((\<lambda>A. \<Sum>\<alpha>\<in>A. ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>) \<longlongrightarrow> g x)
          (finite_subsets_at_top ra_idx)"
        using G1[of x] d unfolding has_sum_def by simp
      have "((\<lambda>A. ((\<Sum>\<alpha>\<in>A. ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>),
                     (\<Sum>\<alpha>\<in>A. ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>)))
          \<longlongrightarrow> (f x, g x)) (finite_subsets_at_top ra_idx)"
        by (rule tendsto_Pair[OF t1 t2])
      hence pair_tendsto:
        "((\<lambda>A. \<Sum>\<alpha>\<in>A. (ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>,
                         ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>))
          \<longlongrightarrow> (f x, g x)) (finite_subsets_at_top ra_idx)"
        by (simp add: sum_prod)
      have "((\<lambda>\<alpha>. (ra_monomial (x - x0) \<alpha> *\<^sub>R c1 \<alpha>,
                       ra_monomial (x - x0) \<alpha> *\<^sub>R c2 \<alpha>))
          has_sum (f x, g x)) ra_idx"
        unfolding has_sum_def by (rule pair_tendsto)
      thus "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> *\<^sub>R (c1 \<alpha>, c2 \<alpha>))
          has_sum (f x, g x)) ra_idx"
        by simp
    qed
  qed
qed

lemma real_analytic_on_sum:
  fixes f :: "'i \<Rightarrow> 'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U"
    and fin: "finite I"
    and ana: "\<And>i. i \<in> I \<Longrightarrow> real_analytic_on (f i) U"
  shows "real_analytic_on (\<lambda>x. \<Sum>i\<in>I. f i x) U"
  using fin ana
proof (induction I rule: finite_induct)
  case empty
  show ?case
    by (simp add: real_analytic_on_const[OF U])
next
  case (insert i I)
  have fi: "real_analytic_on (f i) U"
    using insert.prems by simp
  have fI: "real_analytic_on (\<lambda>x. \<Sum>j\<in>I. f j x) U"
    using insert.IH insert.prems by blast
  have "real_analytic_on (\<lambda>x. f i x + (\<Sum>j\<in>I. f j x)) U"
    by (rule real_analytic_on_add[OF fi fI])
  thus ?case
    using insert.hyps by simp
qed

lemma real_analytic_on_componentwise:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes U: "open U"
    and ana: "\<And>b. b \<in> Basis \<Longrightarrow> real_analytic_on (\<lambda>x. f x \<bullet> b) U"
  shows "real_analytic_on f U"
proof -
  have term_ana: "\<And>b. b \<in> Basis \<Longrightarrow> real_analytic_on (\<lambda>x. (f x \<bullet> b) *\<^sub>R b) U"
    by (rule real_analytic_on_scaleR_vec[OF ana])
  have "real_analytic_on (\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) U"
    by (rule real_analytic_on_sum[OF U finite_Basis]) (use term_ana in blast)
  thus ?thesis
    by (simp add: euclidean_representation)
qed

lemma real_analytic_on_fst:
  assumes "open U"
  shows "real_analytic_on (fst :: ('a::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'a) U"
  by (rule real_analytic_on_bounded_linear[OF assms bounded_linear_fst])

lemma real_analytic_on_snd:
  assumes "open U"
  shows "real_analytic_on (snd :: ('a::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b) U"
  by (rule real_analytic_on_bounded_linear[OF assms bounded_linear_snd])

lemma real_analytic_on_Pair_const:
  fixes c :: "'b::euclidean_space"
  assumes "open U"
  shows "real_analytic_on (\<lambda>x::'a::euclidean_space. (x, c)) U"
  by (rule real_analytic_on_Pair)
     (rule real_analytic_on_bounded_linear[OF assms bounded_linear_ident],
      rule real_analytic_on_const[OF assms])


subsection \<open>(B) Real-analyticity of a real-analytic map's local inverse\<close>

text \<open>
  Combining A1 (real-analytic \<open>\<Rightarrow>\<close> holomorphic extension), B2 (holomorphic inverse is
  holomorphic), and B3 (real restriction), the local inverse of a real-analytic
  diffeomorphism is real-analytic.  Stated abstractly so the implicit-function assembly can
  invoke it on the second slot.
\<close>

lemma real_analytic_C1_local_homeomorphism:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
proof -
  have Cinf: "Cinfinity_on f U"
    by (rule real_analytic_imp_Cinfinity[OF ana])
  have C1: "Ck_on (Suc 0) f U"
    by (rule Cinfinity_on_imp_Ck_on[OF Cinf])
  have derf: "\<And>x. x \<in> U \<Longrightarrow> (f has_derivative blinfun_apply (Dblinfun f x)) (at x)"
    by (rule Ck1_on_imp_has_derivative_blinfun[OF C1])
  have contf: "continuous_on U (Dblinfun f)"
    by (rule Ck1_on_imp_continuous_Dblinfun[OF C1])

  obtain L where Lder: "(f has_derivative L) (at x0)" and bijL: "bij L"
    using reg by blast
  have d0: "(f has_derivative blinfun_apply (Dblinfun f x0)) (at x0)"
    using derf x0 by blast
  have D_eq: "blinfun_apply (Dblinfun f x0) = L"
    by (rule has_derivative_unique[OF d0 Lder])
  have blL: "bounded_linear L"
    by (rule has_derivative_bounded_linear[OF Lder])
  have injL: "inj L"
    using bijL by (simp add: bij_def)
  have bl_invL: "bounded_linear (inv L)"
    by (rule inj_linear_imp_inv_bounded_linear[OF blL injL])
  define invf :: "'a \<Rightarrow>\<^sub>L 'a" where "invf = Blinfun (inv L)"
  have invf_apply: "blinfun_apply invf = inv L"
    unfolding invf_def by (rule bounded_linear_Blinfun_apply[OF bl_invL])
  have invf_id: "invf o\<^sub>L Dblinfun f x0 = id_blinfun"
  proof (rule blinfun_eqI)
    fix h
    show "blinfun_apply (invf o\<^sub>L Dblinfun f x0) h = blinfun_apply id_blinfun h"
      by (simp add: D_eq invf_apply inv_f_f[OF injL])
  qed

  show ?thesis
  proof (rule C1_local_inverse[OF U derf contf x0 invf_id])
    fix U' V g
    assume inv: "open U'" "U' \<subseteq> U" "x0 \<in> U'" "open V" "f x0 \<in> V"
      "homeomorphism U' V f g"
    assume "\<And>y. y \<in> V \<Longrightarrow>
      (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
    show thesis
      by (rule that[of U' V g, OF inv(1) inv(3) inv(2) inv(4) inv(5) inv(6)])
  qed
qed

lemma real_analytic_C1_local_inverse_data:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
    "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
proof -
  have Cinf: "Cinfinity_on f U"
    by (rule real_analytic_imp_Cinfinity[OF ana])
  have C1: "Ck_on (Suc 0) f U"
    by (rule Cinfinity_on_imp_Ck_on[OF Cinf])
  have derf: "\<And>x. x \<in> U \<Longrightarrow> (f has_derivative blinfun_apply (Dblinfun f x)) (at x)"
    by (rule Ck1_on_imp_has_derivative_blinfun[OF C1])
  have contf: "continuous_on U (Dblinfun f)"
    by (rule Ck1_on_imp_continuous_Dblinfun[OF C1])

  obtain L where Lder: "(f has_derivative L) (at x0)" and bijL: "bij L"
    using reg by blast
  have d0: "(f has_derivative blinfun_apply (Dblinfun f x0)) (at x0)"
    using derf x0 by blast
  have D_eq: "blinfun_apply (Dblinfun f x0) = L"
    by (rule has_derivative_unique[OF d0 Lder])
  have blL: "bounded_linear L"
    by (rule has_derivative_bounded_linear[OF Lder])
  have injL: "inj L"
    using bijL by (simp add: bij_def)
  have bl_invL: "bounded_linear (inv L)"
    by (rule inj_linear_imp_inv_bounded_linear[OF blL injL])
  define invf :: "'a \<Rightarrow>\<^sub>L 'a" where "invf = Blinfun (inv L)"
  have invf_apply: "blinfun_apply invf = inv L"
    unfolding invf_def by (rule bounded_linear_Blinfun_apply[OF bl_invL])
  have invf_id: "invf o\<^sub>L Dblinfun f x0 = id_blinfun"
  proof (rule blinfun_eqI)
    fix h
    show "blinfun_apply (invf o\<^sub>L Dblinfun f x0) h = blinfun_apply id_blinfun h"
      by (simp add: D_eq invf_apply inv_f_f[OF injL])
  qed

  show ?thesis
  proof (rule inverse_function_theorem[OF U derf contf x0 invf_id])
    fix U' V g g'
    assume inv: "open U'" "U' \<subseteq> U" "x0 \<in> U'" "open V" "f x0 \<in> V"
      "homeomorphism U' V f g"
    assume derg: "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative g' y) (at y)"
    assume g'_eq: "\<And>y. y \<in> V \<Longrightarrow> g' y = inv (blinfun_apply (Dblinfun f (g y)))"
    assume bijg: "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
    have derg': "\<And>y. y \<in> V \<Longrightarrow>
      (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
      using derg g'_eq by simp
    show thesis
      by (rule that[of U' V g, OF inv(1) inv(3) inv(2) inv(4) inv(5) inv(6) derg' bijg])
  qed
qed

lemma real_analytic_C1_local_inverse_data_real:
  fixes f :: "real \<Rightarrow> real"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and der0: "(f has_real_derivative L0) (at x0)"
    and nz0: "L0 \<noteq> 0"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
    "\<And>y. y \<in> V \<Longrightarrow> \<exists>L. (f has_real_derivative L) (at (g y)) \<and> L \<noteq> 0"
proof -
  have bij0: "bij ((*) L0 :: real \<Rightarrow> real)"
  proof (rule bijI)
    show "inj ((*) L0 :: real \<Rightarrow> real)"
      using nz0 by (auto intro!: injI)
    show "surj ((*) L0 :: real \<Rightarrow> real)"
    proof (rule surjI)
      fix y :: real
      show "L0 * (y / L0) = y"
        using nz0 by simp
    qed
  qed
  have reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
    using has_field_derivative_imp_has_derivative[OF der0] bij0 by blast

  have Cinf: "Cinfinity_on f U"
    by (rule real_analytic_imp_Cinfinity[OF ana])
  have C1: "Ck_on (Suc 0) f U"
    by (rule Cinfinity_on_imp_Ck_on[OF Cinf])
  have derf: "\<And>x. x \<in> U \<Longrightarrow> (f has_derivative blinfun_apply (Dblinfun f x)) (at x)"
    by (rule Ck1_on_imp_has_derivative_blinfun[OF C1])

  show ?thesis
  proof (rule real_analytic_C1_local_inverse_data[OF ana U x0 reg])
    fix U' V g
    assume inv: "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
      "homeomorphism U' V f g"
    assume derg: "\<And>y. y \<in> V \<Longrightarrow>
      (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
    assume bijg: "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
    have nz_der: "\<exists>L. (f has_real_derivative L) (at (g y)) \<and> L \<noteq> 0" if yV: "y \<in> V" for y
    proof -
      have gyU': "g y \<in> U'"
        using homeomorphism_image2[OF inv(6)] yV by blast
      have gyU: "g y \<in> U"
        using inv(3) gyU' by blast
      have dgy: "(f has_derivative blinfun_apply (Dblinfun f (g y))) (at (g y))"
        using derf[OF gyU] .
      obtain L where Lder: "(f has_real_derivative L) (at (g y))"
        using has_real_derivative[OF dgy] by blast
      have D_eq: "blinfun_apply (Dblinfun f (g y)) = (*) L"
        using has_derivative_unique[OF dgy has_field_derivative_imp_has_derivative[OF Lder]] .
      have "L \<noteq> 0"
      proof
        assume L0: "L = 0"
        have zeroD: "blinfun_apply (Dblinfun f (g y)) = ((\<lambda>_. 0) :: real \<Rightarrow> real)"
          using D_eq L0 by (simp add: fun_eq_iff)
        have not_bij_zero: "\<not> bij ((\<lambda>_. 0) :: real \<Rightarrow> real)"
        proof
          assume "bij ((\<lambda>_. 0) :: real \<Rightarrow> real)"
          hence "inj ((\<lambda>_. 0) :: real \<Rightarrow> real)"
            by (simp add: bij_def)
          hence "(0::real) = 1"
            by (rule injD) simp_all
          thus False by simp
        qed
        hence "\<not> bij (blinfun_apply (Dblinfun f (g y)))"
          using zeroD not_bij_zero by simp
        thus False
          using bijg[OF yV] by contradiction
      qed
      thus ?thesis
        using Lder by blast
    qed
    show thesis
      by (rule that[of U' V g, OF inv(1) inv(2) inv(3) inv(4) inv(5) inv(6) derg nz_der])
  qed
qed

theorem real_analytic_local_inverse_real:
  fixes f :: "real \<Rightarrow> real"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and der0: "(f has_real_derivative L0) (at x0)"
    and nz0: "L0 \<noteq> 0"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "real_analytic_on g V"
proof -
  show ?thesis
  proof (rule real_analytic_C1_local_inverse_data_real[OF ana U x0 der0 nz0])
    fix U' V g
    assume inv: "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
      "homeomorphism U' V f g"
    assume derg: "\<And>y. y \<in> V \<Longrightarrow>
      (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
    assume nz_der: "\<And>y. y \<in> V \<Longrightarrow>
      \<exists>L. (f has_real_derivative L) (at (g y)) \<and> L \<noteq> 0"

    have ana_g: "real_analytic_on g V"
      unfolding real_analytic_on_1d_iff
    proof (intro conjI ballI)
      show "open V" by (rule inv(4))
    next
      fix y assume yV: "y \<in> V"
      have gyU': "g y \<in> U'"
        using homeomorphism_image2[OF inv(6)] yV by blast
      have gyU: "g y \<in> U"
        using inv(3) gyU' by blast
      have fgy: "f (g y) = y"
        by (rule homeomorphism_apply2[OF inv(6) yV])

      obtain L where Lder: "(f has_real_derivative L) (at (g y))"
        and Lnz: "L \<noteq> 0"
        using nz_der[OF yV] by blast

      have f_ana_at: "real_analytic_at_1d f (g y)"
        using ana gyU by (auto simp: real_analytic_on_1d_iff)
      from real_analytic_at_1d_imp_holo_extension[OF f_ana_at]
      obtain rf G where rf: "0 < rf"
        and Gholo: "G holomorphic_on ball (complex_of_real (g y)) rf"
        and Gaxis: "\<And>x. \<bar>x - g y\<bar> < rf \<Longrightarrow>
          G (complex_of_real x) = complex_of_real (f x)"
        unfolding has_holo_extension_at_def by blast

      have Gder: "deriv G (complex_of_real (g y)) = complex_of_real L"
        by (rule holo_extension_axis_deriv[OF Gholo rf Gaxis Lder])
      have Gder_nz: "deriv G (complex_of_real (g y)) \<noteq> 0"
        using Gder Lnz by simp

      have centre_rf: "complex_of_real (g y) \<in> ball (complex_of_real (g y)) rf"
        using rf by simp
      obtain rc where rc: "0 < rc"
        and rc_sub: "ball (complex_of_real (g y)) rc \<subseteq> ball (complex_of_real (g y)) rf"
        and Gimage_open: "open (G ` ball (complex_of_real (g y)) rc)"
        and Ginj: "inj_on G (ball (complex_of_real (g y)) rc)"
        using has_complex_derivative_locally_invertible[OF Gholo centre_rf open_ball Gder_nz]
        by blast
      have Gholo_rc: "G holomorphic_on ball (complex_of_real (g y)) rc"
        using Gholo rc_sub by (rule holomorphic_on_subset)
      obtain H where Hholo: "H holomorphic_on G ` ball (complex_of_real (g y)) rc"
        and HG: "\<And>z. z \<in> ball (complex_of_real (g y)) rc \<Longrightarrow> H (G z) = z"
        using holo_inverse_holomorphic[OF Gholo_rc open_ball Ginj] by blast

      have Gy: "G (complex_of_real (g y)) = complex_of_real y"
        using Gaxis[of "g y"] rf fgy by simp
      have y_in_image: "complex_of_real y \<in> G ` ball (complex_of_real (g y)) rc"
      proof (rule image_eqI)
        show "complex_of_real y = G (complex_of_real (g y))"
          using Gy by simp
        show "complex_of_real (g y) \<in> ball (complex_of_real (g y)) rc"
          using rc by simp
      qed
      obtain rh where rh: "0 < rh"
        and rh_sub: "ball (complex_of_real y) rh \<subseteq> G ` ball (complex_of_real (g y)) rc"
        using openE[OF Gimage_open y_in_image] by blast

      obtain rv where rv: "0 < rv" and rv_sub: "ball y rv \<subseteq> V"
        using openE[OF inv(4) yV] by blast

      have contg_y: "continuous (at y) g"
        using homeomorphism_cont2[OF inv(6)] inv(4) yV
        by (simp add: continuous_on_eq_continuous_at)
      have contg_eps: "\<And>e. 0 < e \<Longrightarrow>
        \<exists>d>0. \<forall>t. dist t y < d \<longrightarrow> dist (g t) (g y) < e"
        using contg_y by (simp add: continuous_at_eps_delta dist_real_def)
      obtain rg where rg: "0 < rg"
        and g_close: "\<And>t. dist t y < rg \<Longrightarrow> dist (g t) (g y) < rc"
        using contg_eps[OF rc] by blast

      define eps where "eps = min rh (min rv rg)"
      have eps: "0 < eps"
        using rh rv rg by (simp add: eps_def)
      have eps_le: "eps \<le> rh" "eps \<le> rv" "eps \<le> rg"
        by (auto simp: eps_def)

      have eps_ball_sub: "ball (complex_of_real y) eps \<subseteq> ball (complex_of_real y) rh"
        using eps_le by auto
      have eps_image_sub: "ball (complex_of_real y) eps \<subseteq> G ` ball (complex_of_real (g y)) rc"
        using eps_ball_sub rh_sub by (rule subset_trans)
      have Hholo_eps: "H holomorphic_on ball (complex_of_real y) eps"
        using Hholo eps_image_sub by (rule holomorphic_on_subset)

      have H_real_axis: "H (complex_of_real t) = complex_of_real (g t)"
        if ty: "\<bar>t - y\<bar> < eps" for t
      proof -
        have tV: "t \<in> V"
          using rv_sub ty eps_le by (auto simp: dist_real_def)
        have gt_dist: "dist (g t) (g y) < rc"
          using g_close[of t] ty eps_le by (simp add: dist_real_def)
        have gt_rc: "complex_of_real (g t) \<in> ball (complex_of_real (g y)) rc"
          using gt_dist by (simp add: dist_commute)
        have gt_rf: "complex_of_real (g t) \<in> ball (complex_of_real (g y)) rf"
          using rc_sub gt_rc by blast
        have gt_rf_dist: "dist (complex_of_real (g t)) (complex_of_real (g y)) < rf"
          using gt_rf by (simp add: dist_commute)
        have gt_rf_real: "\<bar>g t - g y\<bar> < rf"
        proof -
          have "complex_of_real (g t) - complex_of_real (g y) =
              complex_of_real (g t - g y)"
            by simp
          hence "norm (complex_of_real (g t - g y)) < rf"
            using gt_rf_dist by (simp add: dist_norm)
          thus ?thesis
            by (simp add: cmod_def)
        qed
        have Gt: "G (complex_of_real (g t)) = complex_of_real t"
          using Gaxis[OF gt_rf_real] homeomorphism_apply2[OF inv(6) tV] by simp
        show ?thesis
          using HG[OF gt_rc] Gt by simp
      qed

      have H_real: "H (complex_of_real t) \<in> \<real>" if "\<bar>t - y\<bar> < eps" for t
        using H_real_axis[OF that] by simp
      have h_ana: "real_analytic_at_1d (\<lambda>t. Re (H (complex_of_real t))) y"
        by (rule holo_inverse_restrict_real_analytic[OF Hholo_eps eps H_real])

      show "real_analytic_at_1d g y"
      proof (rule real_analytic_at_1d_transform_near[OF h_ana eps])
        fix t assume "\<bar>t - y\<bar> < eps"
        thus "g t = Re (H (complex_of_real t))"
          using H_real_axis[of t] by simp
      qed
    qed

    show thesis
      by (rule that[of U' V g, OF inv(1) inv(2) inv(3) inv(4) inv(5) inv(6) ana_g])
  qed
qed

theorem real_analytic_local_inverse_real_bij:
  fixes f :: "real \<Rightarrow> real"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "real_analytic_on g V"
proof -
  obtain L where Lder: "(f has_derivative L) (at x0)" and bijL: "bij L"
    using reg by blast
  obtain L0 where L0der: "(f has_real_derivative L0) (at x0)"
    using has_real_derivative[OF Lder] by blast
  have L_eq: "L = (*) L0"
    using has_derivative_unique[OF Lder has_field_derivative_imp_has_derivative[OF L0der]] .
  have L0_nz: "L0 \<noteq> 0"
  proof
    assume L0_zero: "L0 = 0"
    have L_zero: "L = ((\<lambda>_. 0) :: real \<Rightarrow> real)"
      using L_eq L0_zero by (simp add: fun_eq_iff)
    have not_bij_zero: "\<not> bij ((\<lambda>_. 0) :: real \<Rightarrow> real)"
    proof
      assume "bij ((\<lambda>_. 0) :: real \<Rightarrow> real)"
      hence "inj ((\<lambda>_. 0) :: real \<Rightarrow> real)"
        by (simp add: bij_def)
      hence "(0::real) = 1"
        by (rule injD) simp_all
      thus False by simp
    qed
    show False
      using bijL L_zero not_bij_zero by simp
  qed
  show thesis
  proof (rule real_analytic_local_inverse_real[OF ana U x0 L0der L0_nz])
    fix U' V g
    assume "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
      "homeomorphism U' V f g" "real_analytic_on g V"
    thus thesis
      by (rule that)
  qed
qed

lemma singleton_basis_coordinate_homeomorphism:
  fixes b :: "'a::euclidean_space"
  assumes b: "Basis = {b}"
  shows "homeomorphism (UNIV::'a set) (UNIV::real set)
    (\<lambda>x. x \<bullet> b) (\<lambda>t. t *\<^sub>R b)"
proof (rule homeomorphismI)
  have bB: "b \<in> Basis"
    using b by auto
  show "continuous_on (UNIV::'a set) (\<lambda>x. x \<bullet> b)"
    by (intro continuous_intros)
  show "continuous_on (UNIV::real set) (\<lambda>t. t *\<^sub>R b)"
    by (intro continuous_intros)
  show "(\<lambda>x::'a. x \<bullet> b) ` UNIV \<subseteq> (UNIV::real set)"
    by simp
  show "(\<lambda>t::real. t *\<^sub>R b) ` UNIV \<subseteq> (UNIV::'a set)"
    by simp
  show "(x \<bullet> b) *\<^sub>R b = x" for x :: 'a
    using euclidean_representation[of x, unfolded b] by simp
  show "(t *\<^sub>R b) \<bullet> b = t" for t :: real
    using bB by (simp add: inner_Basis)
qed

lemma singleton_basis_coordinate_open_image:
  fixes b :: "'a::euclidean_space"
  assumes b: "Basis = {b}" and U: "open U"
  shows "open ((\<lambda>x::'a. x \<bullet> b) ` U)"
proof -
  have hom: "homeomorphism (UNIV::'a set) (UNIV::real set)
      (\<lambda>x. x \<bullet> b) (\<lambda>t. t *\<^sub>R b)"
    by (rule singleton_basis_coordinate_homeomorphism[OF b])
  have "openin (top_of_set (UNIV::real set)) ((\<lambda>x::'a. x \<bullet> b) ` U)"
    by (rule homeomorphism_imp_open_map[OF hom]) (use U in simp)
  thus ?thesis
    by simp
qed

lemma singleton_basis_coordinate_scaleR_open_image:
  fixes b :: "'a::euclidean_space"
  assumes b: "Basis = {b}" and U: "open U"
  shows "open ((\<lambda>t::real. t *\<^sub>R b) ` U :: 'a set)"
proof -
  have hom: "homeomorphism (UNIV::real set) (UNIV::'a set)
      (\<lambda>t. t *\<^sub>R b) (\<lambda>x. x \<bullet> b)"
    by (rule homeomorphism_symD[OF singleton_basis_coordinate_homeomorphism[OF b]])
  have "openin (top_of_set (UNIV::'a set)) ((\<lambda>t::real. t *\<^sub>R b) ` U)"
    by (rule homeomorphism_imp_open_map[OF hom]) (use U in simp)
  thus ?thesis
    by simp
qed

theorem real_analytic_local_inverse_Basis_singleton:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a" and b :: "'a"
  assumes b: "Basis = {b}"
    and ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "real_analytic_on g V"
proof -
  let ?phi = "\<lambda>x::'a. x \<bullet> b"
  let ?psi = "\<lambda>t::real. t *\<^sub>R b"
  have bB: "b \<in> Basis"
    using b by auto
  have psi_phi: "?psi (?phi x) = x" for x :: 'a
    using euclidean_representation[of x, unfolded b] by simp
  have phi_psi: "?phi (?psi t) = t" for t :: real
    using bB by (simp add: inner_Basis)

  define UR :: "real set" where "UR = ?phi ` U"
  define xR :: real where "xR = ?phi x0"
  define fR :: "real \<Rightarrow> real" where "fR = (\<lambda>t. ?phi (f (?psi t)))"

  have UR_open: "open UR"
    unfolding UR_def by (rule singleton_basis_coordinate_open_image[OF b U])
  have xR_UR: "xR \<in> UR"
    using x0 by (auto simp: UR_def xR_def)
  have psi_image: "?psi ` UR \<subseteq> U"
    unfolding UR_def using psi_phi by force
  have psi_ana: "real_analytic_on ?psi UR"
    by (rule real_analytic_on_bounded_linear[OF UR_open bounded_linear_scaleR_left])
  have fpsi_ana: "real_analytic_on (\<lambda>t. f (?psi t)) UR"
    by (rule real_analytic_on_compose[OF psi_ana ana psi_image])
  have phi_ana_UNIV: "real_analytic_on ?phi (UNIV::'a set)"
    by (rule real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_inner_left])
  have fR_ana: "real_analytic_on fR UR"
    unfolding fR_def
    by (rule real_analytic_on_compose[OF fpsi_ana phi_ana_UNIV]) simp

  obtain L where Lder: "(f has_derivative L) (at x0)" and bijL: "bij L"
    using reg by blast
  define LR :: "real \<Rightarrow> real" where "LR = (\<lambda>t. ?phi (L (?psi t)))"
  have psi_xR: "?psi xR = x0"
    by (simp add: xR_def psi_phi)
  have psi_bl: "bounded_linear ?psi"
    by (rule bounded_linear_scaleR_left)
  have phi_bl: "bounded_linear ?phi"
    by (rule bounded_linear_inner_left)
  have psi_der: "(?psi has_derivative ?psi) (at xR)"
    by (rule bounded_linear.has_derivative[OF psi_bl has_derivative_ident])
  have fpsi_der: "((\<lambda>t. f (?psi t)) has_derivative (\<lambda>t. L (?psi t))) (at xR)"
    using has_derivative_compose[OF psi_der, of f L] Lder psi_xR by simp
  have phi_der: "(?phi has_derivative ?phi) (at (f (?psi xR)))"
    by (rule bounded_linear.has_derivative[OF phi_bl has_derivative_ident])
  have fR_der: "(fR has_derivative LR) (at xR)"
    unfolding fR_def LR_def
    using has_derivative_compose[OF fpsi_der phi_der] by simp
  have bijLR: "bij LR"
  proof (rule bijI)
    show "inj LR"
    proof (rule injI)
      fix s t :: real
      assume eq: "LR s = LR t"
      have "L (?psi s) = L (?psi t)"
        using eq by (metis LR_def psi_phi)
      hence psi_eq: "?psi s = ?psi t"
        using bijL unfolding bij_def inj_def by blast
      from psi_eq have phi_eq: "?phi (?psi s) = ?phi (?psi t)"
        by (rule arg_cong)
      show "s = t"
        using phi_eq phi_psi[of s] phi_psi[of t] by metis
    qed
    show "surj LR"
      unfolding surj_def
    proof
      fix y :: real
      show "\<exists>x. y = LR x"
      proof (intro exI[where x="?phi (inv L (?psi y))"])
        have "LR (?phi (inv L (?psi y))) =
            ?phi (L (?psi (?phi (inv L (?psi y)))))"
          by (simp add: LR_def)
        also have "\<dots> = ?phi (?psi y)"
          using bijL by (simp add: bij_def psi_phi surj_f_inv_f)
        also have "\<dots> = y"
          by (rule phi_psi)
        finally show "y = LR (?phi (inv L (?psi y)))"
          by simp
      qed
    qed
  qed
  have regR: "\<exists>L. (fR has_derivative L) (at xR) \<and> bij L"
    using fR_der bijLR by blast

  obtain UR' VR h where UR'_open: "open UR'" and xR_UR': "xR \<in> UR'"
    and UR'_sub: "UR' \<subseteq> UR" and VR_open: "open VR"
    and fR_xR_VR: "fR xR \<in> VR"
    and homeoR: "homeomorphism UR' VR fR h"
    and h_ana: "real_analytic_on h VR"
    using real_analytic_local_inverse_real_bij[OF fR_ana UR_open xR_UR regR] by blast

  define U' :: "'a set" where "U' = ?psi ` UR'"
  define V :: "'a set" where "V = ?psi ` VR"
  define g :: "'a \<Rightarrow> 'a" where "g = (\<lambda>y. ?psi (h (?phi y)))"

  have U'_open: "open U'"
    unfolding U'_def by (rule singleton_basis_coordinate_scaleR_open_image[OF b UR'_open])
  have x0_U': "x0 \<in> U'"
    unfolding U'_def using xR_UR' psi_xR by blast
  have U'_sub: "U' \<subseteq> U"
  proof
    fix y assume "y \<in> U'"
    then obtain t where t: "t \<in> UR'" and y: "y = ?psi t"
      unfolding U'_def by blast
    obtain x where x: "x \<in> U" and t_eq: "t = ?phi x"
      using UR'_sub t unfolding UR_def by blast
    show "y \<in> U"
      using x y t_eq psi_phi[of x] by simp
  qed
  have V_open: "open V"
    unfolding V_def by (rule singleton_basis_coordinate_scaleR_open_image[OF b VR_open])
  have fR_xR: "fR xR = ?phi (f x0)"
    by (simp add: fR_def psi_xR)
  have fx0_eq: "f x0 = ?psi (fR xR)"
    using fR_xR psi_phi[of "f x0"] by simp
  have fx0_V: "f x0 \<in> V"
    unfolding V_def using fR_xR_VR fx0_eq by blast

  have phi_U'_sub: "?phi ` U' \<subseteq> UR'"
  proof
    fix s assume "s \<in> ?phi ` U'"
    then obtain y t where y: "y = ?psi t" and t: "t \<in> UR'" and s: "s = ?phi y"
      unfolding U'_def by blast
    have "s = t"
      using s y phi_psi[of t] by metis
    thus "s \<in> UR'"
      using t by simp
  qed
  have phi_V_sub: "?phi ` V \<subseteq> VR"
  proof
    fix s assume "s \<in> ?phi ` V"
    then obtain y t where y: "y = ?psi t" and t: "t \<in> VR" and s: "s = ?phi y"
      unfolding V_def by blast
    have "s = t"
      using s y phi_psi[of t] by metis
    thus "s \<in> VR"
      using t by simp
  qed
  have f_image: "f ` U' \<subseteq> V"
  proof
    fix y assume "y \<in> f ` U'"
    then obtain x t where x: "x = ?psi t" and t: "t \<in> UR'" and y: "y = f x"
      unfolding U'_def by blast
    have fRt: "fR t \<in> VR"
      using homeomorphism_image1[OF homeoR] t by blast
    have "f x = ?psi (fR t)"
      using x by (simp add: fR_def psi_phi)
    thus "y \<in> V"
      using y fRt by (auto simp: V_def)
  qed
  have g_image: "g ` V \<subseteq> U'"
  proof
    fix y assume "y \<in> g ` V"
    then obtain z t where z: "z = ?psi t" and t: "t \<in> VR" and y: "y = g z"
      unfolding V_def by blast
    have ht: "h t \<in> UR'"
      using homeomorphism_image2[OF homeoR] t by blast
    have z_coord: "?phi z = t"
      using z phi_psi[of t] by metis
    have "g z = ?psi (h t)"
      by (simp add: g_def z_coord)
    thus "y \<in> U'"
      using y ht by (auto simp: U'_def)
  qed
  have gf: "g (f x) = x" if x: "x \<in> U'" for x
  proof -
    obtain t where t: "t \<in> UR'" and xeq: "x = ?psi t"
      using x unfolding U'_def by blast
    have "g (f x) = ?psi (h (?phi (f (?psi t))))"
      by (simp add: g_def xeq)
    also have "\<dots> = ?psi (h (fR t))"
      by (simp add: fR_def)
    also have "\<dots> = ?psi t"
      using homeomorphism_apply1[OF homeoR t] by simp
    also have "\<dots> = x"
      by (simp add: xeq)
    finally show ?thesis .
  qed
  have fg: "f (g y) = y" if y: "y \<in> V" for y
  proof -
    obtain t where t: "t \<in> VR" and yeq: "y = ?psi t"
      using y unfolding V_def by blast
    have ht: "h t \<in> UR'"
      using homeomorphism_image2[OF homeoR] t by blast
    have y_coord: "?phi y = t"
      using yeq phi_psi[of t] by metis
    have "f (g y) = f (?psi (h t))"
      by (simp add: g_def y_coord)
    also have "\<dots> = ?psi (fR (h t))"
      by (simp add: fR_def psi_phi)
    also have "\<dots> = ?psi t"
      using homeomorphism_apply2[OF homeoR t] by simp
    also have "\<dots> = y"
      by (simp add: yeq)
    finally show ?thesis .
  qed

  have f_cont_U: "continuous_on U f"
    by (rule continuous_at_imp_continuous_on)
       (use ana in \<open>auto intro: real_analytic_on_imp_continuous_vec\<close>)
  have f_cont_U': "continuous_on U' f"
    by (rule continuous_on_subset[OF f_cont_U U'_sub])
  have phi_cont_V: "continuous_on V ?phi"
    by (intro continuous_intros)
  have h_cont_phi: "continuous_on V (\<lambda>y. h (?phi y))"
    by (rule continuous_on_compose2[OF homeomorphism_cont2[OF homeoR] phi_cont_V phi_V_sub])
  have psi_cont_UNIV: "continuous_on UNIV ?psi"
    by (intro continuous_intros)
  have g_cont_V: "continuous_on V g"
    unfolding g_def
    by (rule continuous_on_compose2[OF psi_cont_UNIV h_cont_phi]) simp
  have homeo: "homeomorphism U' V f g"
    by (rule homeomorphismI[OF f_cont_U' g_cont_V f_image g_image gf fg])

  have phi_ana_V: "real_analytic_on ?phi V"
    by (rule real_analytic_on_bounded_linear[OF V_open bounded_linear_inner_left])
  have h_phi_ana: "real_analytic_on (\<lambda>y. h (?phi y)) V"
    by (rule real_analytic_on_compose[OF phi_ana_V h_ana phi_V_sub])
  have g_ana: "real_analytic_on g V"
    unfolding g_def by (rule real_analytic_on_scaleR_vec[OF h_phi_ana])

  show ?thesis
    by (rule that[OF U'_open x0_U' U'_sub V_open fx0_V homeo g_ana])
qed

theorem real_analytic_local_inverse_dim1:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes dim1: "DIM('a) = 1"
    and ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "real_analytic_on g V"
proof -
  have "card (Basis :: 'a set) = 1"
    using dim1 by (simp only: dim_UNIV)
  then obtain b :: 'a where b: "Basis = {b}"
    by (rule card_1_singletonE)
  show ?thesis
    by (rule real_analytic_local_inverse_Basis_singleton[OF b ana U x0 reg that])
qed

lemma real_analytic_on_has_derivative_Dblinfun:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ana: "real_analytic_on f U"
    and xU: "x \<in> U"
  shows "(f has_derivative blinfun_apply (Dblinfun f x)) (at x)"
proof -
  from ana xU obtain r c where r0: "0 < r"
    and ser: "\<And>y. dist y x < r \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum f y) ra_idx"
    unfolding real_analytic_on_def by blast
  define D where "D = (\<lambda>v. infsum
    (\<lambda>\<alpha>. ra_Dmonomial (x - x) \<alpha> v *\<^sub>R c \<alpha>) ra_idx)"
  have xdist: "dist x x < r"
    using r0 by simp
  have derD: "(f has_derivative D) (at x)"
    unfolding D_def
    by (rule ra_power_series_has_derivative[OF r0 ser xdist])
  have diff: "f differentiable (at x)"
    using derD unfolding differentiable_def by blast
  have D_eq: "D = frechet_derivative f (at x)"
    by (rule frechet_derivative_at[OF derD])
  show ?thesis
    using derD diff by (simp add: D_eq blinfun_apply_Dblinfun)
qed

text \<open>
  \<open>real_analytic_on\<close> is a local property: if every point of an open set \<open>V\<close> has a
  neighbourhood on which \<open>g\<close> is real-analytic, then \<open>g\<close> is real-analytic on all of \<open>V\<close>.
\<close>

lemma real_analytic_on_locality:
  fixes g :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes V: "open V"
    and loc: "\<And>y. y \<in> V \<Longrightarrow>
      \<exists>W. open W \<and> y \<in> W \<and> W \<subseteq> V \<and> real_analytic_on g W"
  shows "real_analytic_on g V"
  unfolding real_analytic_on_def
proof (intro conjI ballI)
  show "open V" by (rule V)
next
  fix x assume xV: "x \<in> V"
  from loc[OF xV] obtain W where W: "open W" "x \<in> W" "W \<subseteq> V"
    and gW: "real_analytic_on g W" by blast
  from gW W(2) show "\<exists>r>0. \<exists>c. \<forall>y. dist y x < r \<longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum g y) ra_idx"
    unfolding real_analytic_on_def by blast
qed

text \<open>
  If \<open>G\<close> is real-analytic on \<open>V0\<close> and \<open>g\<close> agrees with \<open>G\<close> on an open subset \<open>W\<close>,
  then \<open>g\<close> is real-analytic on \<open>W\<close>: shrink each expansion radius so the series ball
  stays inside \<open>W\<close>, where \<open>g = G\<close>.
\<close>

lemma real_analytic_on_cong_nbhd:
  fixes g G :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes G: "real_analytic_on G V0"
    and W: "open W" and sub: "W \<subseteq> V0"
    and eq: "\<And>y. y \<in> W \<Longrightarrow> g y = G y"
  shows "real_analytic_on g W"
  unfolding real_analytic_on_def
proof (intro conjI ballI)
  show "open W" by (rule W)
next
  fix x assume xW: "x \<in> W"
  hence xV0: "x \<in> V0" using sub by blast
  from G xV0 obtain \<rho> c where \<rho>: "0 < \<rho>"
    and ser: "\<And>y. dist y x < \<rho> \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum G y) ra_idx"
    unfolding real_analytic_on_def by blast
  from W xW obtain \<delta> where \<delta>: "0 < \<delta>" and ballW: "ball x \<delta> \<subseteq> W"
    using open_contains_ball by blast
  define r where "r = min \<rho> \<delta>"
  have r0: "0 < r" using \<rho> \<delta> by (simp add: r_def)
  have "\<forall>y. dist y x < r \<longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum g y) ra_idx"
  proof (intro allI impI)
    fix y assume d: "dist y x < r"
    have dr: "dist y x < \<rho>" using d by (simp add: r_def)
    have dd: "dist y x < \<delta>" using d by (simp add: r_def)
    have "y \<in> ball x \<delta>" using dd by (simp add: dist_commute)
    hence yW: "y \<in> W" using ballW by blast
    have "((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum G y) ra_idx"
      by (rule ser[OF dr])
    thus "((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum g y) ra_idx"
      by (simp add: eq[OF yW])
  qed
  with r0 show "\<exists>r>0. \<exists>c. \<forall>y. dist y x < r \<longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (y - x) \<alpha> *\<^sub>R c \<alpha>) has_sum g y) ra_idx"
    by blast
qed

lemma real_analytic_C1_local_inverse_data_analytic_normalized:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and zero_U: "0 \<in> U"
    and f0: "f 0 = 0"
    and der0: "(f has_derivative id) (at 0)"
    and U'_open: "open U'"
    and zero_U': "0 \<in> U'"
    and U'_sub: "U' \<subseteq> U"
    and V_open: "open V"
    and zero_V: "0 \<in> V"
    and homeo: "homeomorphism U' V f g"
    and derg: "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
    and bijg: "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
  shows "real_analytic_on g V"
  \<comment> \<open>At each \<open>y0 \<in> V\<close> we normalise \<open>f\<close> at the base point \<open>x0 = g y0\<close>, apply the analytic
      formal right inverse of the normalised map, and identify the resulting analytic map
      with \<open>g\<close> near \<open>y0\<close> using injectivity of \<open>f\<close> on \<open>U'\<close>.\<close>
proof (rule real_analytic_on_locality[OF V_open])
  fix y0 :: 'a assume y0V: "y0 \<in> V"
  \<comment> \<open>Base point and its derivative data.\<close>
  define x0 where "x0 = g y0"
  have x0U': "x0 \<in> U'"
    using homeomorphism_image2[OF homeo] y0V by (auto simp: x0_def)
  have x0U: "x0 \<in> U" using x0U' U'_sub by blast
  have fx0: "f x0 = y0"
    using homeomorphism_apply2[OF homeo y0V] by (simp add: x0_def)
  define Dap where "Dap = blinfun_apply (Dblinfun f x0)"
  have der: "(f has_derivative Dap) (at x0)"
    unfolding Dap_def by (rule real_analytic_on_has_derivative_Dblinfun[OF ana x0U])
  have bijDap: "bij Dap"
    using bijg[OF y0V] by (simp add: Dap_def x0_def)
  have injDap: "inj Dap" using bijDap by (simp add: bij_def)
  have surjDap: "surj Dap" using bijDap by (simp add: bij_def)
  have blDap: "bounded_linear Dap"
    by (rule has_derivative_bounded_linear[OF der])
  define Dinv where "Dinv = inv Dap"
  have bl_Dinv: "bounded_linear Dinv"
    unfolding Dinv_def by (rule inj_linear_imp_inv_bounded_linear[OF blDap injDap])
  interpret Dinv: bounded_linear Dinv by (rule bl_Dinv)
  have Dinv_D: "Dinv (Dap u) = u" for u
    by (simp add: Dinv_def inv_f_f[OF injDap])
  have D_Dinv: "Dap (Dinv z) = z" for z
    by (simp add: Dinv_def surj_f_inv_f[OF surjDap])
  have Dinv0: "Dinv 0 = 0" by (rule Dinv.zero)
  \<comment> \<open>The normalised map \<open>ftil u = Dinv (f (x0 + u) - y0)\<close>, analytic near \<open>0\<close>.\<close>
  define ftil where "ftil = (\<lambda>u. Dinv (f (x0 + u) - y0))"
  obtain \<delta>0 where \<delta>0: "0 < \<delta>0" and ballU: "ball x0 \<delta>0 \<subseteq> U"
    using U x0U by (metis open_contains_ball)
  define W0 where "W0 = ball (0::'a) \<delta>0"
  have openW0: "open W0" by (simp add: W0_def)
  have zeroW0: "0 \<in> W0" using \<delta>0 by (simp add: W0_def)
  have shift_ana: "real_analytic_on (\<lambda>u. x0 + u) W0"
    by (rule real_analytic_on_add[OF real_analytic_on_const[OF openW0]
        real_analytic_on_bounded_linear[OF openW0 bounded_linear_ident]])
  have shift_img: "(\<lambda>u. x0 + u) ` W0 \<subseteq> U"
  proof
    fix z assume "z \<in> (\<lambda>u. x0 + u) ` W0"
    then obtain u where u: "u \<in> W0" and z: "z = x0 + u" by blast
    have "norm u < \<delta>0" using u by (simp add: W0_def dist_norm)
    hence "dist z x0 < \<delta>0" by (simp add: z dist_norm)
    thus "z \<in> U" using ballU by (auto simp: mem_ball dist_commute)
  qed
  have fshift_ana: "real_analytic_on (\<lambda>u. f (x0 + u)) W0"
    by (rule real_analytic_on_compose[OF shift_ana ana shift_img])
  have fshift_diff: "real_analytic_on (\<lambda>u. f (x0 + u) - y0) W0"
    by (rule real_analytic_on_diff[OF fshift_ana real_analytic_on_const[OF openW0]])
  have Dinv_ana: "real_analytic_on Dinv (UNIV::'a set)"
    by (rule real_analytic_on_bounded_linear[OF open_UNIV bl_Dinv])
  have ftil_ana: "real_analytic_on ftil W0"
    unfolding ftil_def
    by (rule real_analytic_on_compose[OF fshift_diff Dinv_ana subset_UNIV])
  have ftil0: "ftil 0 = 0"
    by (simp add: ftil_def fx0 Dinv0)
  \<comment> \<open>The derivative of \<open>ftil\<close> at \<open>0\<close> is the identity.\<close>
  have sh_der: "((+) x0 has_derivative (\<lambda>x. x)) (at 0)"
    by (rule shift_has_derivative_id)
  have der': "(f has_derivative Dap) (at ((+) x0 0))" using der by simp
  have comp1: "((f \<circ> (+) x0) has_derivative (Dap \<circ> (\<lambda>x. x))) (at 0)"
    by (rule diff_chain_at[OF sh_der der'])
  have step1: "((\<lambda>u. f (x0 + u)) has_derivative Dap) (at 0)"
    using comp1 by (simp add: comp_def)
  have step2: "((\<lambda>u. f (x0 + u) - y0) has_derivative Dap) (at 0)"
  proof -
    have "((\<lambda>u. f (x0 + u) - y0) has_derivative (\<lambda>h. Dap h - 0)) (at 0)"
      by (rule has_derivative_diff[OF step1 has_derivative_const])
    thus ?thesis by simp
  qed
  have step3: "(ftil has_derivative (\<lambda>h. Dinv (Dap h))) (at 0)"
    unfolding ftil_def
    by (rule bounded_linear.has_derivative[OF bl_Dinv step2])
  have ftil_der: "(ftil has_derivative id) (at 0)"
  proof -
    have "(\<lambda>h. Dinv (Dap h)) = id" by (rule ext) (simp add: Dinv_D)
    with step3 show ?thesis by simp
  qed
  \<comment> \<open>Analytic formal right inverse \<open>Hfun\<close> of the normalised map.\<close>
  obtain \<sigma> bphi where \<sigma>0: "0 < \<sigma>"
    and Hana: "real_analytic_on
        (\<lambda>h. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) (ball (0::'a) (\<sigma> / 2))"
    and Hsum: "\<And>h. norm h < \<sigma> \<Longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)) (ra_idx::('a \<Rightarrow> nat) set)"
    and Hinv: "\<And>h. norm h < \<sigma> \<Longrightarrow>
        ftil (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) = h"
  proof (rule normalized_analytic_formal_right_inverse[OF ftil_ana zeroW0 ftil0 ftil_der])
    fix s :: real and bp :: "('a \<Rightarrow> nat) \<Rightarrow> 'a"
    assume A1: "0 < s"
      and A2: "real_analytic_on
          (\<lambda>h. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bp \<gamma>) (ball (0::'a) (s / 2))"
      and A3: "\<And>h. norm h < s \<Longrightarrow>
          ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bp \<gamma>)
            has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R cfix bp \<gamma>)) (ra_idx::('a \<Rightarrow> nat) set)"
      and A4: "\<And>h. norm h < s \<Longrightarrow>
          ftil (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bp \<gamma>) = h"
    show thesis by (rule that[OF A1 A2 A3 A4])
  qed
  define Hfun :: "'a \<Rightarrow> 'a" where
    "Hfun = (\<lambda>h. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)"
  have Hana': "real_analytic_on Hfun (ball (0::'a) (\<sigma> / 2))"
    using Hana by (simp only: Hfun_def)
  have Hsum': "\<And>h. norm h < \<sigma> \<Longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) has_sum Hfun h) (ra_idx::('a \<Rightarrow> nat) set)"
    using Hsum by (simp only: Hfun_def)
  have Hinv': "\<And>h. norm h < \<sigma> \<Longrightarrow> ftil (Hfun h) = h"
    using Hinv by (simp only: Hfun_def)
  have H0: "Hfun 0 = 0"
  proof -
    have n0: "norm (0::'a) < \<sigma>" using \<sigma>0 by simp
    have "((\<lambda>\<gamma>. ra_monomial (0::'a) \<gamma> *\<^sub>R cfix bphi \<gamma>) has_sum Hfun 0)
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule Hsum'[OF n0])
    hence "cfix bphi czero_idx = Hfun 0"
      by (rule ra_series_at_zero_coeff)
    thus ?thesis by (simp add: cfix_czero)
  qed
  \<comment> \<open>Affine change of variable \<open>Lfun y = Dinv (y - y0)\<close> and the domain \<open>W2\<close>.\<close>
  define Lfun where "Lfun = (\<lambda>y. Dinv (y - y0))"
  have Lfun_y0: "Lfun y0 = 0" by (simp add: Lfun_def Dinv0)
  have Lfun_ana: "real_analytic_on Lfun (UNIV::'a set)"
    unfolding Lfun_def
    by (rule real_analytic_on_compose[OF
        real_analytic_on_diff[OF
          real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_ident]
          real_analytic_on_const[OF open_UNIV]]
        Dinv_ana subset_UNIV])
  obtain K where K0: "0 < K" and Kbound: "\<And>z. norm (Dinv z) \<le> norm z * K"
    using Dinv.pos_bounded by blast
  define \<epsilon>2 where "\<epsilon>2 = (\<sigma> / 2) / K"
  have \<epsilon>20: "0 < \<epsilon>2" using \<sigma>0 K0 by (simp add: \<epsilon>2_def)
  define W2 where "W2 = ball y0 \<epsilon>2"
  have openW2: "open W2" by (simp add: W2_def)
  have y0W2: "y0 \<in> W2" using \<epsilon>20 by (simp add: W2_def)
  have Lfun_small: "norm (Lfun y) < \<sigma> / 2" if yW2: "y \<in> W2" for y
  proof -
    have dy: "norm (y - y0) < \<epsilon>2"
      using yW2 by (simp add: W2_def dist_norm norm_minus_commute)
    have "norm (Lfun y) = norm (Dinv (y - y0))" by (simp add: Lfun_def)
    also have "\<dots> \<le> norm (y - y0) * K" by (rule Kbound)
    also have "\<dots> < \<epsilon>2 * K" using mult_strict_right_mono[OF dy K0] .
    also have "\<dots> = \<sigma> / 2" using K0 by (simp add: \<epsilon>2_def)
    finally show ?thesis .
  qed
  have Lfun_img: "Lfun ` W2 \<subseteq> ball (0::'a) (\<sigma> / 2)"
  proof
    fix z assume "z \<in> Lfun ` W2"
    then obtain y where y: "y \<in> W2" and z: "z = Lfun y" by blast
    show "z \<in> ball (0::'a) (\<sigma> / 2)"
      using Lfun_small[OF y] by (simp add: z dist_norm)
  qed
  \<comment> \<open>The candidate analytic inverse \<open>Gfun y = x0 + Hfun (Lfun y)\<close>.\<close>
  define Gfun where "Gfun = (\<lambda>y. x0 + Hfun (Lfun y))"
  have Lfun_ana_W2: "real_analytic_on Lfun W2"
    by (rule real_analytic_on_open_subset[OF Lfun_ana openW2 subset_UNIV])
  have HL_ana: "real_analytic_on (\<lambda>y. Hfun (Lfun y)) W2"
    by (rule real_analytic_on_compose[OF Lfun_ana_W2 Hana' Lfun_img])
  have Gfun_ana: "real_analytic_on Gfun W2"
    unfolding Gfun_def
    by (rule real_analytic_on_add[OF real_analytic_on_const[OF openW2] HL_ana])
  have Gfun_y0: "Gfun y0 = x0"
    by (simp add: Gfun_def Lfun_y0 H0)
  \<comment> \<open>\<open>Gfun\<close> is continuous and maps a neighbourhood of \<open>y0\<close> into \<open>U'\<close>.\<close>
  have contG: "continuous (at y0) Gfun"
    by (rule real_analytic_on_imp_continuous_vec[OF Gfun_ana y0W2])
  have GU'_ev: "eventually (\<lambda>y. Gfun y \<in> U') (at y0)"
  proof (rule topological_tendstoD)
    show "(Gfun \<longlongrightarrow> Gfun y0) (at y0)" using contG by (simp add: continuous_at)
    show "open U'" by (rule U'_open)
    show "Gfun y0 \<in> U'" using Gfun_y0 x0U' by simp
  qed
  obtain \<epsilon>4 where \<epsilon>40: "0 < \<epsilon>4"
    and GU'ball: "\<forall>y. y \<noteq> y0 \<and> dist y y0 < \<epsilon>4 \<longrightarrow> Gfun y \<in> U'"
    using GU'_ev by (auto simp: eventually_at)
  have GU': "Gfun y \<in> U'" if "dist y y0 < \<epsilon>4" for y
  proof (cases "y = y0")
    case True thus ?thesis using Gfun_y0 x0U' by simp
  next
    case False thus ?thesis using GU'ball that by blast
  qed
  \<comment> \<open>The final neighbourhood \<open>W3\<close> on which \<open>g\<close> agrees with \<open>Gfun\<close>.\<close>
  obtain \<epsilon>V where \<epsilon>V0: "0 < \<epsilon>V" and ballV: "ball y0 \<epsilon>V \<subseteq> V"
    using V_open y0V by (metis open_contains_ball)
  define \<epsilon> where "\<epsilon> = min \<epsilon>2 (min \<epsilon>V \<epsilon>4)"
  have \<epsilon>0: "0 < \<epsilon>" using \<epsilon>20 \<epsilon>V0 \<epsilon>40 by (simp add: \<epsilon>_def)
  have e_le2: "\<epsilon> \<le> \<epsilon>2" unfolding \<epsilon>_def by (rule min.cobounded1)
  have e_leV: "\<epsilon> \<le> \<epsilon>V" unfolding \<epsilon>_def
    by (meson min.cobounded1 min.cobounded2 order_trans)
  have e_le4: "\<epsilon> \<le> \<epsilon>4" unfolding \<epsilon>_def
    by (meson min.cobounded2 order_trans)
  define W3 where "W3 = ball y0 \<epsilon>"
  have openW3: "open W3" by (simp add: W3_def)
  have y0W3: "y0 \<in> W3" using \<epsilon>0 by (simp add: W3_def)
  have W3_W2: "W3 \<subseteq> W2" unfolding W3_def W2_def by (rule subset_ball[OF e_le2])
  have W3_V: "W3 \<subseteq> V"
  proof -
    have "W3 \<subseteq> ball y0 \<epsilon>V" unfolding W3_def by (rule subset_ball[OF e_leV])
    thus ?thesis using ballV by blast
  qed
  have eqGg: "g y = Gfun y" if yW3: "y \<in> W3" for y
  proof -
    have dyy0: "dist y y0 < \<epsilon>" using yW3 by (simp add: W3_def dist_commute)
    have yW2: "y \<in> W2" using yW3 W3_W2 by blast
    have Lsmall: "norm (Lfun y) < \<sigma>"
    proof -
      have "norm (Lfun y) < \<sigma> / 2" by (rule Lfun_small[OF yW2])
      also have "\<dots> < \<sigma>" using \<sigma>0 by simp
      finally show ?thesis .
    qed
    have fGy: "f (Gfun y) = y"
    proof -
      have "ftil (Hfun (Lfun y)) = Lfun y" by (rule Hinv'[OF Lsmall])
      hence "Dinv (f (x0 + Hfun (Lfun y)) - y0) = Dinv (y - y0)"
        by (simp add: ftil_def Lfun_def)
      hence "Dap (Dinv (f (x0 + Hfun (Lfun y)) - y0)) = Dap (Dinv (y - y0))"
        by simp
      hence "f (x0 + Hfun (Lfun y)) - y0 = y - y0"
        by (simp add: D_Dinv)
      hence "f (x0 + Hfun (Lfun y)) = y" by simp
      thus ?thesis by (simp add: Gfun_def)
    qed
    have GyU': "Gfun y \<in> U'"
    proof (rule GU')
      show "dist y y0 < \<epsilon>4" using dyy0 e_le4 by linarith
    qed
    have "g (f (Gfun y)) = Gfun y"
      by (rule homeomorphism_apply1[OF homeo GyU'])
    thus "g y = Gfun y" using fGy by simp
  qed
  have "real_analytic_on g W3"
    by (rule real_analytic_on_cong_nbhd[OF Gfun_ana openW3 W3_W2 eqGg])
  thus "\<exists>W. open W \<and> y0 \<in> W \<and> W \<subseteq> V \<and> real_analytic_on g W"
    using openW3 y0W3 W3_V by blast
qed

theorem real_analytic_local_inverse_normalized:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and zero_U: "0 \<in> U"
    and f0: "f 0 = 0"
    and der0: "(f has_derivative id) (at 0)"
  obtains U' V g where
    "open U'" "0 \<in> U'" "U' \<subseteq> U" "open V" "0 \<in> V"
    "homeomorphism U' V f g"
    "real_analytic_on g V"
proof -
  have reg: "\<exists>L. (f has_derivative L) (at 0) \<and> bij L"
    using der0 by (intro exI[where x=id]) (simp add: bij_id)
  show ?thesis
  proof (rule real_analytic_C1_local_inverse_data[OF ana U zero_U reg])
    fix U' V g
    assume U'_open: "open U'"
      and zero_U': "0 \<in> U'"
      and U'_sub: "U' \<subseteq> U"
      and V_open: "open V"
      and f0_V: "f 0 \<in> V"
      and homeo: "homeomorphism U' V f g"
      and derg: "\<And>y. y \<in> V \<Longrightarrow>
        (g has_derivative (inv (blinfun_apply (Dblinfun f (g y))))) (at y)"
      and bijg: "\<And>y. y \<in> V \<Longrightarrow> bij (blinfun_apply (Dblinfun f (g y)))"
    have zero_V: "0 \<in> V"
      using f0 f0_V by simp
    have g_ana: "real_analytic_on g V"
      by (rule real_analytic_C1_local_inverse_data_analytic_normalized
          [OF ana U zero_U f0 der0 U'_open zero_U' U'_sub V_open zero_V homeo derg bijg])
    show thesis
      by (rule that[OF U'_open zero_U' U'_sub V_open zero_V homeo g_ana])
  qed
qed

theorem real_analytic_local_inverse:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and U: "open U"
    and x0: "x0 \<in> U"
    and reg: "\<exists>L. (f has_derivative L) (at x0) \<and> bij L"
  obtains U' V g where
    "open U'" "x0 \<in> U'" "U' \<subseteq> U" "open V" "f x0 \<in> V"
    "homeomorphism U' V f g"
    "real_analytic_on g V"
  \<comment> \<open>HARD LEAF: B1 gives the \<open>C\<^sup>1\<close> local homeomorphism inverse \<open>g\<close>; A1+A2 lift \<open>f\<close> to a
      holomorphic complexification whose inverse is holomorphic (B2); B3 restricts that
      inverse to the reals to conclude \<open>real_analytic_on g V\<close>.  Assembly of A1/A2/B1/B2/B3.\<close>
proof -
  obtain L where Lder: "(f has_derivative L) (at x0)" and bijL: "bij L"
    using reg by blast
  have blL: "bounded_linear L"
    using Lder by (rule has_derivative_bounded_linear)
  have linL: "linear L"
    using blL by (rule bounded_linear.linear)
  have injL: "inj L" and surjL: "surj L"
    using bijL by (auto simp: bij_def)
  have blInvL: "bounded_linear (inv L)"
    by (rule inj_linear_imp_inv_bounded_linear[OF blL injL])
  have linInvL: "linear (inv L)"
    using blInvL by (rule bounded_linear.linear)

  let ?U0 = "(+) (- x0) ` U"
  let ?F = "\<lambda>x. inv L (f (x0 + x) - f x0)"
  have U0_open: "open ?U0"
    using U open_translation by blast
  have zero_U0: "0 \<in> ?U0"
    using x0 by force
  have shift_image: "(\<lambda>x. x0 + x) ` ?U0 \<subseteq> U"
    by auto

  have id_ana: "real_analytic_on (\<lambda>x::'a. x) ?U0"
    by (rule real_analytic_on_bounded_linear[OF U0_open bounded_linear_ident])
  have shift_ana: "real_analytic_on (\<lambda>x::'a. x0 + x) ?U0"
    by (rule real_analytic_on_add[OF real_analytic_on_const[OF U0_open] id_ana])
  have fshift_ana: "real_analytic_on (\<lambda>x. f (x0 + x)) ?U0"
    using real_analytic_on_compose[OF shift_ana ana shift_image] by simp
  have fshift0_ana: "real_analytic_on (\<lambda>x. f (x0 + x) - f x0) ?U0"
    by (rule real_analytic_on_diff[OF fshift_ana real_analytic_on_const[OF U0_open]])
  have invL_ana_UNIV: "real_analytic_on (inv L) UNIV"
    by (rule real_analytic_on_bounded_linear[OF open_UNIV blInvL])
  have F_ana: "real_analytic_on ?F ?U0"
    by (rule real_analytic_on_compose[OF fshift0_ana invL_ana_UNIV]) simp

  have F0: "?F 0 = 0"
    using linInvL by (simp add: linear_0)
  have shift_der: "((\<lambda>x::'a. x0 + x) has_derivative id) (at 0)"
    by (auto intro!: derivative_eq_intros)
  have Lder_shift0: "(f has_derivative L) (at ((\<lambda>x::'a. x0 + x) 0))"
    using Lder by simp
  have fshift_der: "((\<lambda>x. f (x0 + x)) has_derivative L) (at 0)"
    using has_derivative_compose[OF shift_der Lder_shift0] by (simp add: comp_def)
  have const_der: "((\<lambda>x::'a. f x0) has_derivative (\<lambda>h. 0)) (at 0)"
    by (rule has_derivative_const)
  have fshift0_der: "((\<lambda>x. f (x0 + x) - f x0) has_derivative L) (at 0)"
    using has_derivative_diff[OF fshift_der const_der] by simp
  have invL_der:
    "((inv L) has_derivative inv L) (at ((\<lambda>x. f (x0 + x) - f x0) 0))"
    by (rule bounded_linear.has_derivative[OF blInvL has_derivative_ident])
  have F_der_raw: "(?F has_derivative (\<lambda>h. inv L (L h))) (at 0)"
    using has_derivative_compose[OF fshift0_der invL_der] by (simp add: comp_def)
  have invL_L: "inv L (L h) = h" for h
    using injL by (simp add: inv_f_f)
  have F_der: "(?F has_derivative id) (at 0)"
    by (rule has_derivative_eq_rhs[OF F_der_raw]) (simp add: fun_eq_iff invL_L)

  obtain U0' V0 h where U0'_open: "open U0'" and zero_U0': "0 \<in> U0'"
    and U0'_sub: "U0' \<subseteq> ?U0" and V0_open: "open V0" and zero_V0: "0 \<in> V0"
    and homeo0: "homeomorphism U0' V0 ?F h"
    and h_ana: "real_analytic_on h V0"
    by (rule real_analytic_local_inverse_normalized[OF F_ana U0_open zero_U0 F0 F_der]) blast

  define U' where "U' = (+) x0 ` U0'"
  define V where "V = (\<lambda>z. f x0 + L z) ` V0"
  define g where "g = (\<lambda>y. x0 + h (inv L (y - f x0)))"
  let ?S = "\<lambda>y. inv L (y - f x0)"

  have U'_open: "open U'"
    unfolding U'_def using U0'_open open_translation by blast
  have x0_U': "x0 \<in> U'"
    unfolding U'_def using zero_U0' by force
  have U'_sub: "U' \<subseteq> U"
  proof
    fix y assume "y \<in> U'"
    then obtain z where z: "z \<in> U0'" and y: "y = x0 + z"
      unfolding U'_def by blast
    obtain u where u: "u \<in> U" and z_eq: "z = - x0 + u"
      using U0'_sub z by blast
    show "y \<in> U"
      using u y z_eq by simp
  qed
  have L_V0_open: "open (L ` V0)"
    using V0_open linL surjL by (rule open_surjective_linear_image)
  have V_eq: "V = (+) (f x0) ` (L ` V0)"
    unfolding V_def by auto
  have V_open: "open V"
    unfolding V_eq using L_V0_open open_translation by blast
  have fx0_V: "f x0 \<in> V"
    unfolding V_def using zero_V0 linL by (force simp: linear_0)

  have S_V_sub: "?S ` V \<subseteq> V0"
  proof
    fix s assume "s \<in> ?S ` V"
    then obtain y z where z: "z \<in> V0" and y: "y = f x0 + L z"
      and s: "s = ?S y"
      unfolding V_def by blast
    have "s = z"
      using s y injL by (simp add: inv_f_f)
    thus "s \<in> V0"
      using z by simp
  qed

  have f_image: "f ` U' \<subseteq> V"
  proof
    fix y assume "y \<in> f ` U'"
    then obtain x z where z: "z \<in> U0'" and x: "x = x0 + z" and y: "y = f x"
      unfolding U'_def by blast
    have Fz: "?F z \<in> V0"
      using homeomorphism_image1[OF homeo0] z by blast
    have L_Fz: "L (?F z) = f (x0 + z) - f x0"
      using surjL by (simp add: surj_f_inv_f)
    have "f x = f x0 + L (?F z)"
      using x L_Fz by simp
    thus "y \<in> V"
      unfolding V_def using y Fz by blast
  qed

  have g_image: "g ` V \<subseteq> U'"
  proof
    fix y assume "y \<in> g ` V"
    then obtain v z where z: "z \<in> V0" and v: "v = f x0 + L z" and y: "y = g v"
      unfolding V_def by blast
    have hz: "h z \<in> U0'"
      using homeomorphism_image2[OF homeo0] z by blast
    have coord: "?S v = z"
      using v injL by (simp add: inv_f_f)
    have "y = x0 + h z"
      using y coord by (simp add: g_def)
    thus "y \<in> U'"
      unfolding U'_def using hz by blast
  qed

  have gf: "g (f x) = x" if x: "x \<in> U'" for x
  proof -
    obtain z where z: "z \<in> U0'" and xeq: "x = x0 + z"
      using x unfolding U'_def by blast
    have "g (f x) = x0 + h (?F z)"
      using xeq by (simp add: g_def)
    also have "\<dots> = x0 + z"
      using homeomorphism_apply1[OF homeo0 z] by simp
    also have "\<dots> = x"
      using xeq by simp
    finally show ?thesis .
  qed

  have fg: "f (g y) = y" if y: "y \<in> V" for y
  proof -
    obtain z where z: "z \<in> V0" and yeq: "y = f x0 + L z"
      using y unfolding V_def by blast
    have coord: "?S y = z"
      using yeq injL by (simp add: inv_f_f)
    have hz: "h z \<in> U0'"
      using homeomorphism_image2[OF homeo0] z by blast
    have F_hz: "?F (h z) = z"
      by (rule homeomorphism_apply2[OF homeo0 z])
    have L_Fhz: "L (?F (h z)) = f (x0 + h z) - f x0"
      using surjL by (simp add: surj_f_inv_f)
    have "f (g y) = f (x0 + h z)"
      using coord by (simp add: g_def)
    also have "\<dots> = f x0 + L z"
      using F_hz L_Fhz by simp
    also have "\<dots> = y"
      using yeq by simp
    finally show ?thesis .
  qed

  have f_cont_U: "continuous_on U f"
    by (rule continuous_at_imp_continuous_on)
       (use ana in \<open>auto intro: real_analytic_on_imp_continuous_vec\<close>)
  have f_cont_U': "continuous_on U' f"
    by (rule continuous_on_subset[OF f_cont_U U'_sub])
  have S_cont: "continuous_on V ?S"
  proof -
    have diff_cont: "continuous_on V (\<lambda>y. y - f x0)"
      by (intro continuous_intros)
    have inv_cont: "continuous_on UNIV (inv L)"
      using bounded_linear.continuous_on[OF blInvL continuous_on_id[of UNIV]]
      by (simp add: o_def)
    show ?thesis
      by (rule continuous_on_compose2[OF inv_cont diff_cont]) simp
  qed
  have h_cont_S: "continuous_on V (\<lambda>y. h (?S y))"
    by (rule continuous_on_compose2[OF homeomorphism_cont2[OF homeo0] S_cont S_V_sub])
  have g_cont_V: "continuous_on V g"
    unfolding g_def by (intro continuous_intros h_cont_S)
  have homeo: "homeomorphism U' V f g"
    by (rule homeomorphismI[OF f_cont_U' g_cont_V f_image g_image gf fg])

  have diff_ana: "real_analytic_on (\<lambda>y::'a. y - f x0) V"
    by (rule real_analytic_on_diff)
       (rule real_analytic_on_bounded_linear[OF V_open bounded_linear_ident],
        rule real_analytic_on_const[OF V_open])
  have S_ana: "real_analytic_on ?S V"
    by (rule real_analytic_on_compose[OF diff_ana invL_ana_UNIV]) simp
  have hS_ana: "real_analytic_on (\<lambda>y. h (?S y)) V"
    by (rule real_analytic_on_compose[OF S_ana h_ana S_V_sub])
  have g_ana: "real_analytic_on g V"
    unfolding g_def
    by (rule real_analytic_on_add[OF real_analytic_on_const[OF V_open] hS_ana])

  show ?thesis
    by (rule that[OF U'_open x0_U' U'_sub V_open fx0_V homeo g_ana])
qed


subsection \<open>(C) The analytic implicit-function theorem (assembly)\<close>

text \<open>
  Classical reduction: define \<open>\<Phi> (x, y) = (x, F (x, y))\<close>.  At \<open>(x0, y0)\<close> the derivative of
  \<open>\<Phi>\<close> is block-triangular with identity in the first slot and the (invertible by \<open>reg\<close>)
  second-slot partial \<open>L\<close>, hence \<open>\<Phi>\<close> is a local diffeomorphism.  \<open>\<Phi>\<close> is real-analytic
  (\<open>F\<close> is, the projection is), so by \<open>real_analytic_local_inverse\<close> it has a
  real-analytic local inverse \<open>\<Psi> = (\<lambda>(x,z). (x, h (x, z)))\<close>.  Then
  \<open>g x := h (x, 0)\<close> is real-analytic (composition with the analytic constant-\<open>0\<close> slice),
  satisfies \<open>g x0 = y0\<close> and \<open>F (x, g x) = 0\<close>.

\<close>

theorem real_analytic_implicit_function:
  fixes F :: "('a::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b"
  assumes ana: "real_analytic_on F W"
    and Wopen: "open W"
    and pW: "(x0, y0) \<in> W"
    and F0: "F (x0, y0) = 0"
    and reg: "\<exists>L. ((\<lambda>y. F (x0, y)) has_derivative L) (at y0) \<and> bij L"
  obtains U g where
      "open U" and "x0 \<in> U" and "g x0 = y0"
      and "real_analytic_on g U"
      and "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0"
  \<comment> \<open>HARD LEAF (assembly): build \<open>\<Phi> (x,y) = (x, F (x,y))\<close> on \<open>W\<close>, real-analytic by the
      closure lemmas; its derivative at \<open>(x0,y0)\<close> is bijective (block-triangular with \<open>id\<close>
      and the invertible \<open>L\<close> from \<open>reg\<close>); apply \<open>real_analytic_local_inverse\<close> to get a
      real-analytic inverse \<open>\<Psi>\<close>; extract the solution slot \<open>g x = snd (\<Psi> (x, (x,0)))\<close>;
      \<open>g x0 = y0\<close> and \<open>F (x, g x) = 0\<close> follow from \<open>\<Phi>\<close>/\<open>\<Psi>\<close> being mutually inverse and
      \<open>F0\<close>; \<open>real_analytic_on g\<close> follows from \<open>real_analytic_on_compose\<close> /
      \<open>real_analytic_on_const\<close>.  The remaining hard leaf is
      \<open>real_analytic_local_inverse\<close>.\<close>
proof -
  let ?Phi = "\<lambda>p::'a \<times> 'b. (fst p, F p)"
  let ?p0 = "(x0, y0)"
  obtain L where Lder: "((\<lambda>y. F (x0, y)) has_derivative L) (at y0)"
    and bijL: "bij L"
    using reg by blast

  have Phi_ana: "real_analytic_on ?Phi W"
    by (rule real_analytic_on_Pair[OF real_analytic_on_fst[OF Wopen] ana])

  have C1_F: "Ck_at (Suc 0) F ?p0"
    using real_analytic_imp_Cinfinity[OF ana] pW
    unfolding Cinfinity_on_def Cinfinity_at_def
    by blast
  hence Fdiff: "F differentiable at ?p0"
    by (simp only: Ck_at.simps(2))
  then obtain A where Fder: "(F has_derivative A) (at ?p0)"
    unfolding differentiable_def by blast

  have slice_der: "((\<lambda>y. F (x0, y)) has_derivative (\<lambda>dy. A (0, dy))) (at y0)"
  proof -
    have pair_der: "((\<lambda>y. (x0, y)) has_derivative (\<lambda>dy. (0, dy))) (at y0)"
    proof -
      have cder: "((\<lambda>y::'b. x0) has_derivative (\<lambda>dy. 0)) (at y0)"
        by (rule has_derivative_const)
      have idder: "((\<lambda>y::'b. y) has_derivative (\<lambda>dy. dy)) (at y0)"
        by (rule has_derivative_ident)
      show ?thesis
        using has_derivative_Pair[OF cder idder] by simp
    qed
    show ?thesis
      using has_derivative_compose[OF pair_der Fder] by simp
  qed
  have L_eq: "L = (\<lambda>dy. A (0, dy))"
    by (rule has_derivative_unique[OF Lder slice_der])

  let ?B = "\<lambda>h::'a \<times> 'b. (fst h, A h)"
  have Phi_der: "(?Phi has_derivative ?B) (at ?p0)"
  proof -
    have fst_der: "((fst :: ('a \<times> 'b) \<Rightarrow> 'a) has_derivative fst) (at ?p0)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_fst has_derivative_ident])
    show ?thesis
      using has_derivative_Pair[OF fst_der Fder] by simp
  qed

  have blA: "bounded_linear A"
    using Fder by (rule has_derivative_bounded_linear)
  interpret A: bounded_linear A by (rule blA)
  have surjL: "surj L" and injL: "inj L"
    using bijL by (auto simp: bij_def)

  let ?C = "\<lambda>q::'a \<times> 'b. (fst q, inv L (snd q - A (fst q, 0)))"
  have B_C: "?B (?C q) = q" for q
  proof -
    let ?w = "snd q - A (fst q, 0)"
    have decomp: "(fst q, inv L ?w) = (fst q, 0) + (0, inv L ?w)"
      by simp
    have Aq: "A (fst q, inv L ?w) = A (fst q, 0) + A (0, inv L ?w)"
      by (subst decomp) (rule A.add)
    have A0_inv: "A (0, inv L ?w) = ?w"
    proof -
      have "A (0, inv L ?w) = L (inv L ?w)"
        using L_eq by simp
      also have "... = ?w"
        using surjL by (rule surj_f_inv_f)
      finally show ?thesis .
    qed
    have Aeq: "A (fst q, inv L ?w) = snd q"
      using Aq A0_inv by simp
    show ?thesis
      using Aeq
      by simp
  qed
  have C_B: "?C (?B h) = h" for h
  proof -
    have Ah: "A h = A (fst h, 0) + A (0, snd h)"
    proof -
      have decomp: "h = (fst h, 0) + (0, snd h)"
        by simp
      show ?thesis
        by (subst decomp) (rule A.add)
    qed
    have "A h - A (fst h, 0) = L (snd h)"
      using Ah L_eq by simp
    thus ?thesis
      using injL by (simp add: inv_f_f)
  qed
  have bijB: "bij ?B"
  proof (rule bijI)
    show "inj ?B"
    proof (rule injI)
      fix x y :: "'a \<times> 'b"
      assume "?B x = ?B y"
      hence H: "?C (?B x) = ?C (?B y)"
        by simp
      have Cx: "?C (?B x) = x"
        by (rule C_B)
      have Cy: "?C (?B y) = y"
        by (rule C_B)
      show "x = y"
        using H Cx Cy by metis
    qed
    show "surj ?B"
      unfolding surj_def
    proof
      fix y :: "'a \<times> 'b"
      have "?B (?C y) = y"
        by (rule B_C)
      hence "y = ?B (?C y)"
        by simp
      show "\<exists>x. y = ?B x"
        using \<open>y = ?B (?C y)\<close> by blast
    qed
  qed

  obtain U' V Psi where U'_open: "open U'" and p0_U': "?p0 \<in> U'"
    and U'_sub: "U' \<subseteq> W" and V_open: "open V"
    and Phi_p0_V: "?Phi ?p0 \<in> V"
    and homeo: "homeomorphism U' V ?Phi Psi"
    and Psi_ana: "real_analytic_on Psi V"
  proof (rule real_analytic_local_inverse[OF Phi_ana Wopen pW])
    show "\<exists>L. (?Phi has_derivative L) (at ?p0) \<and> bij L"
      using Phi_der bijB by blast
  qed blast

  define U where "U = {x. (x, 0::'b) \<in> V}"
  define g where "g = (\<lambda>x. snd (Psi (x, 0::'b)))"

  have U_open: "open U"
  proof -
    have cont_slice: "continuous_on UNIV (\<lambda>x::'a. (x, 0::'b))"
      by (intro continuous_intros)
    have "open (UNIV \<inter> (\<lambda>x::'a. (x, 0::'b)) -` V)"
      by (rule continuous_open_preimage[OF cont_slice open_UNIV V_open])
    thus ?thesis
      by (simp add: U_def vimage_def)
  qed
  have x0_U: "x0 \<in> U"
    using Phi_p0_V F0 by (simp add: U_def)
  have g_x0: "g x0 = y0"
    using homeomorphism_apply1[OF homeo p0_U'] F0
    by (simp add: g_def)

  have slice_ana: "real_analytic_on (\<lambda>x::'a. (x, 0::'b)) U"
    by (rule real_analytic_on_Pair_const[OF U_open])
  have slice_image: "(\<lambda>x::'a. (x, 0::'b)) ` U \<subseteq> V"
    by (auto simp: U_def)
  have Psi_slice_ana: "real_analytic_on (\<lambda>x::'a. Psi (x, 0::'b)) U"
    using real_analytic_on_compose[OF slice_ana Psi_ana slice_image] by simp
  have g_ana: "real_analytic_on g U"
  proof -
    have snd_ana: "real_analytic_on (snd :: ('a \<times> 'b) \<Rightarrow> 'b) UNIV"
      by (rule real_analytic_on_snd) simp
    have "real_analytic_on (\<lambda>x::'a. snd (Psi (x, 0::'b))) U"
      by (rule real_analytic_on_compose[OF Psi_slice_ana snd_ana]) simp
    thus ?thesis
      by (simp add: g_def)
  qed

  have solution: "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0"
  proof
    fix x assume xU: "x \<in> U"
    have x0V: "(x, 0::'b) \<in> V"
      using xU by (simp add: U_def)
    have Psi_in: "Psi (x, 0::'b) \<in> U'"
      using homeomorphism_image2[OF homeo] x0V by blast
    have Phi_Psi: "?Phi (Psi (x, 0::'b)) = (x, 0::'b)"
      by (rule homeomorphism_apply2[OF homeo x0V])
    have fst_Psi: "fst (Psi (x, 0::'b)) = x"
      using Phi_Psi by simp
    have F_Psi: "F (Psi (x, 0::'b)) = 0"
      using Phi_Psi by simp
    have "(x, g x) = Psi (x, 0::'b)"
      using fst_Psi by (simp add: g_def prod_eq_iff)
    thus "(x, g x) \<in> W \<and> F (x, g x) = 0"
      using Psi_in U'_sub F_Psi by auto
  qed

  show ?thesis
    by (rule that[OF U_open x0_U g_x0 g_ana solution])
qed

end
