section \<open>Functions whose restrictions to lines are entire\<close>

theory Line_Entire_Functions
  imports
    "HOL-Complex_Analysis.Complex_Analysis"
    Meager_Sets
begin

subsection \<open>Zero sets\<close>

lemma continuous_identity_zero_nowhere_dense:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cont: "continuous_on UNIV f"
    and identity: "\<And>U. \<lbrakk>open U; U \<noteq> {}; \<forall>x\<in>U. f x = 0\<rbrakk> \<Longrightarrow> (\<forall>x. f x = 0)"
    and nontriv: "\<exists>x. f x \<noteq> 0"
  shows "nowhere_dense {x. f x = 0}"
proof -
  have clo: "closed {x. f x = 0}"
    using closed_Collect_eq[OF cont continuous_on_const] by simp
  have "interior {x. f x = 0} = {}"
  proof (rule ccontr)
    assume ne: "interior {x. f x = 0} \<noteq> {}"
    have "\<forall>x\<in>interior {x. f x = 0}. f x = 0"
      using interior_subset by auto
    from identity[OF open_interior ne this] nontriv show False by blast
  qed
  with clo show ?thesis
    by (simp only: nowhere_dense_def closure_closed)
qed

lemma slice_zero_nowhere_dense:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and V :: "'a set"
  assumes cont: "continuous_on UNIV f"
    and identity: "\<And>U. \<lbrakk>open U; U \<noteq> {}; \<forall>x\<in>U. f x = 0\<rbrakk> \<Longrightarrow> (\<forall>x. f x = 0)"
    and nontriv: "\<exists>x. f x \<noteq> 0"
  shows "nowhere_dense {x \<in> V. f x = 0}"
  by (rule nowhere_dense_subset[OF _ continuous_identity_zero_nowhere_dense[OF cont identity nontriv]])
     auto

lemma lines_entire_identity:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lines: "\<And>a v. \<exists>F. F holomorphic_on UNIV
                       \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v)))"
    and Uopen: "open U" and Une: "U \<noteq> {}" and Uzero: "\<forall>x\<in>U. f x = 0"
  shows "\<forall>y. f y = 0"
proof
  fix y
  obtain a where aU: "a \<in> U" using Une by blast
  show "f y = 0"
  proof (cases "y = a")
    case True thus ?thesis using aU Uzero by blast
  next
    case False
    define v where "v = y - a"
    have v0: "v \<noteq> 0" using False by (simp add: v_def)
    obtain F where Fhol: "F holomorphic_on UNIV"
      and Fval: "\<And>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v))"
      using lines by blast
    obtain e where e0: "e > 0" and eball: "ball a e \<subseteq> U"
      using Uopen aU open_contains_ball by blast
    define d where "d = e / norm v"
    have nv0: "norm v > 0" using v0 by simp
    have d0: "d > 0" using e0 nv0 by (simp add: d_def)
    have van: "F (complex_of_real t) = 0" if t: "\<bar>t\<bar> < d" for t
    proof -
      have "norm (t *\<^sub>R v) = \<bar>t\<bar> * norm v" by simp
      also have "\<dots> < d * norm v"
        using t nv0 by (simp add: mult_strict_right_mono)
      also have "\<dots> = e" using nv0 by (simp add: d_def)
      finally have "a + t *\<^sub>R v \<in> ball a e" by (simp add: dist_norm)
      hence "f (a + t *\<^sub>R v) = 0" using eball Uzero by blast
      thus ?thesis using Fval by simp
    qed
    define Z where "Z = complex_of_real ` {t. \<bar>t\<bar> < d}"
    have lim: "(0::complex) islimpt Z"
      unfolding islimpt_approachable
    proof (intro allI impI)
      fix \<epsilon>::real assume "\<epsilon> > 0"
      define t where "t = min d \<epsilon> / 2"
      have tpos: "t > 0" using d0 \<open>\<epsilon> > 0\<close> by (simp add: t_def)
      have "t < d" using d0 \<open>\<epsilon> > 0\<close> by (simp add: t_def)
      hence "complex_of_real t \<in> Z" using tpos by (auto simp: Z_def)
      moreover have "complex_of_real t \<noteq> 0" using tpos by simp
      moreover have "dist (complex_of_real t) 0 < \<epsilon>"
        using tpos \<open>\<epsilon> > 0\<close> by (simp add: t_def dist_norm)
      ultimately show "\<exists>x'\<in>Z. x' \<noteq> 0 \<and> dist x' 0 < \<epsilon>" by blast
    qed
    have F1: "F (complex_of_real 1) = 0"
    proof (rule analytic_continuation[OF Fhol open_UNIV connected_UNIV
              subset_UNIV UNIV_I lim _ UNIV_I])
      fix z assume "z \<in> Z"
      then obtain t where "z = complex_of_real t" "\<bar>t\<bar> < d" by (auto simp: Z_def)
      thus "F z = 0" using van by simp
    qed
    have "complex_of_real (f (a + 1 *\<^sub>R v)) = F (complex_of_real 1)"
      using Fval[of 1] by simp
    also have "\<dots> = 0" using F1 by simp
    finally have "f (a + v) = 0" by simp
    thus ?thesis by (simp add: v_def)
  qed
qed

lemma lines_entire_slice_nowhere_dense:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and V :: "'a set"
  assumes cont: "continuous_on UNIV f"
    and lines: "\<And>a v. \<exists>F. F holomorphic_on UNIV
                       \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v)))"
    and nontriv: "\<exists>x. f x \<noteq> 0"
  shows "nowhere_dense {x \<in> V. f x = 0}"
  by (rule slice_zero_nowhere_dense[OF cont _ nontriv])
     (rule lines_entire_identity[OF lines])

lemma holomorphic_cnj_reflect:
  assumes "G holomorphic_on UNIV"
  shows "(\<lambda>z. cnj (G (cnj z))) holomorphic_on UNIV"
proof -
  have bl: "bounded_linear cnj" by (rule bounded_linear_cnj)
  have "(\<lambda>z. cnj (G (cnj z))) field_differentiable (at z)" for z :: complex
  proof -
    have "G field_differentiable (at (cnj z))"
      using assms by (simp add: holomorphic_on_def)
    then obtain D where D: "(G has_field_derivative D) (at (cnj z))"
      unfolding field_differentiable_def by blast
    have cnjd: "(cnj has_derivative cnj) (at z)"
      using bounded_linear.has_derivative[OF bl has_derivative_ident] by simp
    have Gd: "(G has_derivative (*) D) (at (cnj z))"
      by (rule has_field_derivative_imp_has_derivative[OF D])
    have comp1: "((\<lambda>w. G (cnj w)) has_derivative (\<lambda>x. D * cnj x)) (at z)"
      using diff_chain_at[OF cnjd Gd] by (simp add: o_def)
    have comp2: "((\<lambda>w. cnj (G (cnj w))) has_derivative (\<lambda>x. cnj (D * cnj x))) (at z)"
      using bounded_linear.has_derivative[OF bl comp1] by (simp add: o_def)
    have "(\<lambda>x. cnj (D * cnj x)) = (\<lambda>x. cnj D * x)"
      by simp
    with comp2 have "((\<lambda>w. cnj (G (cnj w))) has_derivative (\<lambda>x. cnj D * x)) (at z)" by simp
    then show "(\<lambda>z. cnj (G (cnj z))) field_differentiable (at z)"
      unfolding field_differentiable_def has_field_derivative_def by blast
  qed
  thus ?thesis
    by (auto simp: holomorphic_on_def intro: field_differentiable_at_within)
qed

subsection \<open>Closure properties\<close>

definition cline_entire :: "('a::euclidean_space \<Rightarrow> complex) \<Rightarrow> bool" where
  "cline_entire g \<longleftrightarrow>
     (\<forall>a v. \<exists>G. G holomorphic_on UNIV
              \<and> (\<forall>t::real. G (complex_of_real t) = g (a + t *\<^sub>R v)))"

definition rline_entire :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> bool" where
  "rline_entire f \<longleftrightarrow>
     (\<forall>a v. \<exists>F. F holomorphic_on UNIV
              \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v))))"

lemma cline_entire_const: "cline_entire (\<lambda>x. c)"
  unfolding cline_entire_def by (intro allI exI[of _ "\<lambda>_. c"]) simp

lemma cline_entire_add:
  assumes "cline_entire g1" and "cline_entire g2"
  shows "cline_entire (\<lambda>x. g1 x + g2 x)"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  obtain G1 where G1: "G1 holomorphic_on UNIV"
      "\<And>t::real. G1 (complex_of_real t) = g1 (a + t *\<^sub>R v)"
    using assms(1) unfolding cline_entire_def by blast
  obtain G2 where G2: "G2 holomorphic_on UNIV"
      "\<And>t::real. G2 (complex_of_real t) = g2 (a + t *\<^sub>R v)"
    using assms(2) unfolding cline_entire_def by blast
  show "\<exists>G. G holomorphic_on UNIV
            \<and> (\<forall>t::real. G (complex_of_real t) = g1 (a + t *\<^sub>R v) + g2 (a + t *\<^sub>R v))"
    by (intro exI[of _ "\<lambda>z. G1 z + G2 z"])
       (auto simp: G1 G2 intro!: holomorphic_intros)
qed

lemma cline_entire_mult:
  assumes "cline_entire g1" and "cline_entire g2"
  shows "cline_entire (\<lambda>x. g1 x * g2 x)"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  obtain G1 where G1: "G1 holomorphic_on UNIV"
      "\<And>t::real. G1 (complex_of_real t) = g1 (a + t *\<^sub>R v)"
    using assms(1) unfolding cline_entire_def by blast
  obtain G2 where G2: "G2 holomorphic_on UNIV"
      "\<And>t::real. G2 (complex_of_real t) = g2 (a + t *\<^sub>R v)"
    using assms(2) unfolding cline_entire_def by blast
  show "\<exists>G. G holomorphic_on UNIV
            \<and> (\<forall>t::real. G (complex_of_real t) = g1 (a + t *\<^sub>R v) * g2 (a + t *\<^sub>R v))"
    by (intro exI[of _ "\<lambda>z. G1 z * G2 z"])
       (auto simp: G1 G2 intro!: holomorphic_intros)
qed

lemma cline_entire_sum:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> cline_entire (g i)"
  shows "cline_entire (\<lambda>x. \<Sum>i\<in>I. g i x)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case using cline_entire_const[of 0] by simp
next
  case (insert i I)
  have "cline_entire (\<lambda>x. g i x + (\<Sum>j\<in>I. g j x))"
    by (rule cline_entire_add) (use insert in auto)
  thus ?case using insert.hyps by simp
qed

lemma cline_entire_cis_linear:
  fixes lf :: "'a::euclidean_space \<Rightarrow> real"
  assumes "bounded_linear lf"
  shows "cline_entire (\<lambda>x. cis (lf x))"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  have aff: "lf (a + t *\<^sub>R v) = lf a + t * lf v" for t::real
    by (simp add: assms linear_simps(1,5))
  let ?G = "\<lambda>z. exp (\<i> * (complex_of_real (lf a) + z * complex_of_real (lf v)))"
  have "?G holomorphic_on UNIV" by (intro holomorphic_intros)
  moreover have "?G (complex_of_real t) = cis (lf (a + t *\<^sub>R v))" for t::real
    by (simp add: aff cis_conv_exp algebra_simps flip: of_real_mult of_real_add)
  ultimately show "\<exists>G. G holomorphic_on UNIV
                       \<and> (\<forall>t::real. G (complex_of_real t) = cis (lf (a + t *\<^sub>R v)))"
    by blast
qed

lemma rline_entire_Re:
  assumes "cline_entire g"
  shows "rline_entire (\<lambda>x. Re (g x))"
  unfolding rline_entire_def
proof (intro allI)
  fix a v
  obtain G where G: "G holomorphic_on UNIV"
      "\<And>t::real. G (complex_of_real t) = g (a + t *\<^sub>R v)"
    using assms unfolding cline_entire_def by blast
  let ?F = "\<lambda>z. (G z + cnj (G (cnj z))) / 2"
  have "?F holomorphic_on UNIV"
    using G(1) holomorphic_cnj_reflect[OF G(1)] by (intro holomorphic_intros) auto
  moreover have "?F (complex_of_real t) = complex_of_real (Re (g (a + t *\<^sub>R v)))" for t::real
    by (simp add: G(2) complex_add_cnj)
  ultimately show "\<exists>F. F holomorphic_on UNIV
                       \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (Re (g (a + t *\<^sub>R v))))"
    by blast
qed

lemma rline_entire_add:
  assumes "rline_entire f1" and "rline_entire f2"
  shows "rline_entire (\<lambda>x. f1 x + f2 x)"
  unfolding rline_entire_def
proof (intro allI)
  fix a v
  obtain F1 where F1: "F1 holomorphic_on UNIV"
      "\<And>t::real. F1 (complex_of_real t) = complex_of_real (f1 (a + t *\<^sub>R v))"
    using assms(1) unfolding rline_entire_def by blast
  obtain F2 where F2: "F2 holomorphic_on UNIV"
      "\<And>t::real. F2 (complex_of_real t) = complex_of_real (f2 (a + t *\<^sub>R v))"
    using assms(2) unfolding rline_entire_def by blast
  show "\<exists>F. F holomorphic_on UNIV
            \<and> (\<forall>t::real. F (complex_of_real t)
                        = complex_of_real (f1 (a + t *\<^sub>R v) + f2 (a + t *\<^sub>R v)))"
    by (intro exI[of _ "\<lambda>z. F1 z + F2 z"])
       (auto simp: F1 F2 intro!: holomorphic_intros)
qed

lemma rline_entire_mult:
  assumes "rline_entire f1" and "rline_entire f2"
  shows "rline_entire (\<lambda>x. f1 x * f2 x)"
  unfolding rline_entire_def
proof (intro allI)
  fix a v
  obtain F1 where F1: "F1 holomorphic_on UNIV"
      "\<And>t::real. F1 (complex_of_real t) = complex_of_real (f1 (a + t *\<^sub>R v))"
    using assms(1) unfolding rline_entire_def by blast
  obtain F2 where F2: "F2 holomorphic_on UNIV"
      "\<And>t::real. F2 (complex_of_real t) = complex_of_real (f2 (a + t *\<^sub>R v))"
    using assms(2) unfolding rline_entire_def by blast
  show "\<exists>F. F holomorphic_on UNIV
            \<and> (\<forall>t::real. F (complex_of_real t)
                        = complex_of_real (f1 (a + t *\<^sub>R v) * f2 (a + t *\<^sub>R v)))"
    by (intro exI[of _ "\<lambda>z. F1 z * F2 z"])
       (auto simp: F1 F2 intro!: holomorphic_intros)
qed

lemma rline_entire_scale:
  assumes "rline_entire f"
  shows "rline_entire (\<lambda>x. c * f x)"
  using rline_entire_mult[OF rline_entire_Re[OF cline_entire_const[of "complex_of_real c"]] assms]
  by simp

lemma rline_entire_const: "rline_entire (\<lambda>x. c)"
  using rline_entire_Re[OF cline_entire_const[of "complex_of_real c"]] by simp

lemma rline_entire_sum:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> rline_entire (g i)"
  shows "rline_entire (\<lambda>x. \<Sum>i\<in>I. g i x)"
  using assms by (induction I rule: finite_induct) (auto intro: rline_entire_const rline_entire_add)

lemma rline_entire_prod:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> rline_entire (g i)"
  shows "rline_entire (\<lambda>x. \<Prod>i\<in>I. g i x)"
  using assms by (induction I rule: finite_induct) (auto intro: rline_entire_const rline_entire_mult)

lemma rline_entire_det_fun:
  fixes A :: "'a::euclidean_space \<Rightarrow> real^'n^'n"
  assumes "\<And>i j. rline_entire (\<lambda>x. A x $ i $ j)"
  shows "rline_entire (\<lambda>x. matrix_det (A x))"
  unfolding matrix_det_def
  by (auto intro!: rline_entire_sum rline_entire_scale rline_entire_prod assms finite_permutations)

lemma rline_entire_coord:
  fixes n :: "'n::finite" and k :: 2
  shows "rline_entire (\<lambda>x::(real^2)^'n. (x $ n) $ k)"
  unfolding rline_entire_def
proof (intro allI)
  fix a v :: "(real^2)^'n"
  let ?F = "\<lambda>z. complex_of_real ((a $ n) $ k) + z * complex_of_real ((v $ n) $ k)"
  have "?F holomorphic_on UNIV" by (intro holomorphic_intros)
  moreover have "?F (complex_of_real t) = complex_of_real (((a + t *\<^sub>R v) $ n) $ k)" for t::real
    by (simp flip: of_real_mult of_real_add)
  ultimately show "\<exists>F. F holomorphic_on UNIV
                       \<and> (\<forall>t::real. F (complex_of_real t)
                                   = complex_of_real (((a + t *\<^sub>R v) $ n) $ k))"
    by blast
qed

lemma cline_entire_of_real_linear:
  fixes lf :: "'a::euclidean_space \<Rightarrow> real"
  assumes "bounded_linear lf"
  shows "cline_entire (\<lambda>x. complex_of_real (lf x))"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  have aff: "lf (a + t *\<^sub>R v) = lf a + t * lf v" for t::real
    by (simp add: assms linear_simps(1,5))
  let ?G = "\<lambda>z. complex_of_real (lf a) + z * complex_of_real (lf v)"
  have "?G holomorphic_on UNIV" by (intro holomorphic_intros)
  moreover have "?G (complex_of_real t) = complex_of_real (lf (a + t *\<^sub>R v))" for t::real
    by (simp add: aff)
  ultimately show "\<exists>G. G holomorphic_on UNIV
                       \<and> (\<forall>t::real. G (complex_of_real t) = complex_of_real (lf (a + t *\<^sub>R v)))"
    by blast
qed

lemma cline_entire_cnj:
  assumes "cline_entire g"
  shows "cline_entire (\<lambda>x. cnj (g x))"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  obtain G where G: "G holomorphic_on UNIV"
      "\<And>t::real. G (complex_of_real t) = g (a + t *\<^sub>R v)"
    using assms unfolding cline_entire_def by blast
  let ?H = "\<lambda>z. cnj (G (cnj z))"
  have "?H holomorphic_on UNIV" by (rule holomorphic_cnj_reflect[OF G(1)])
  moreover have "?H (complex_of_real t) = cnj (g (a + t *\<^sub>R v))" for t::real
    by (simp add: G(2))
  ultimately show "\<exists>H. H holomorphic_on UNIV
                       \<and> (\<forall>t::real. H (complex_of_real t) = cnj (g (a + t *\<^sub>R v)))"
    by blast
qed

end
