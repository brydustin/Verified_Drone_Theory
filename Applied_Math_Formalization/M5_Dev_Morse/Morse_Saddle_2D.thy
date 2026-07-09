theory Morse_Saddle_2D
  imports "HOL-Analysis.Analysis"
begin

text \<open>Foundational, GENERAL (reusable / AFP-candidate) development: the local structure of the
  zero set of a 2-variable function at a nondegenerate SADDLE point.  Built as a proof hole-scaffold:
  the main theorem @{text saddle_form_two_arcs} is assembled from two clean stubs
  (@{text factor_indef_C1}, @{text level_zero_C1_arc}); the Hadamard bridge @{text hadamard2}
  is the third (foundational) stub.  Each stub is an independent agent target.\<close>

text \<open>A scalar field on a set, with an explicit continuous gradient field (our C1 notion).\<close>

definition C1field :: "(real^2 \<Rightarrow> real) \<Rightarrow> (real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "C1field f g S \<longleftrightarrow> (\<forall>x\<in>S. (f has_derivative (\<lambda>h. inner (g x) h)) (at x)) \<and> continuous_on S g"

subsection \<open>STUB 1 (algebra): factoring an indefinite C1 binary form\<close>

text \<open>An indefinite binary quadratic form with C1 coefficients (and \<open>a p \<noteq> 0\<close>) factors into two
  transverse C1 linear factors.  Roots \<open>r\<^sub>\<plusminus> = (-b \<plusminus> sqrt(b\<^sup>2-ac))/a\<close>; continuity/C1 from the
  strictly-positive discriminant.  AGENT TARGET.\<close>

lemma factor_indef_C1:
  fixes a b c :: "real^2 \<Rightarrow> real" and ga gb gc :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0"
    and aC1: "C1field a ga (ball p \<rho>0)" and bC1: "C1field b gb (ball p \<rho>0)"
    and cC1: "C1field c gc (ball p \<rho>0)"
    and a0: "a p \<noteq> 0" and indef: "(b p)\<^sup>2 - a p * c p > 0"
  obtains rp rm :: "real^2 \<Rightarrow> real" and grp grm :: "real^2 \<Rightarrow> real^2" and \<rho> :: real
    where "0 < \<rho>" "\<rho> \<le> \<rho>0"
      "C1field rp grp (ball p \<rho>)" "C1field rm grm (ball p \<rho>)" "rp p \<noteq> rm p"
      "\<And>x Y1 Y2. x \<in> ball p \<rho> \<Longrightarrow>
          a x * Y1\<^sup>2 + 2 * b x * Y1 * Y2 + c x * Y2\<^sup>2
        = a x * (Y1 - rp x * Y2) * (Y1 - rm x * Y2)"
proof -
  \<comment> \<open>component derivatives and continuity from the C1field hypotheses\<close>
  have da: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (a has_derivative (\<lambda>h. inner (ga x) h)) (at x)"
    and db: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (b has_derivative (\<lambda>h. inner (gb x) h)) (at x)"
    and dc: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (c has_derivative (\<lambda>h. inner (gc x) h)) (at x)"
    using aC1 bC1 cC1 unfolding C1field_def by blast+
  have cga0: "continuous_on (ball p \<rho>0) ga" and cgb0: "continuous_on (ball p \<rho>0) gb"
    and cgc0: "continuous_on (ball p \<rho>0) gc"
    using aC1 bC1 cC1 unfolding C1field_def by blast+
  have ca0: "continuous_on (ball p \<rho>0) a"
    by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
       (use da in \<open>blast intro: has_derivative_continuous\<close>)
  have cb0: "continuous_on (ball p \<rho>0) b"
    by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
       (use db in \<open>blast intro: has_derivative_continuous\<close>)
  have cc0: "continuous_on (ball p \<rho>0) c"
    by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
       (use dc in \<open>blast intro: has_derivative_continuous\<close>)

  define D :: "real^2 \<Rightarrow> real" where "D = (\<lambda>y. (b y)^2 - a y * c y)"
  define gD :: "real^2 \<Rightarrow> real^2"
    where "gD = (\<lambda>y. 2 *\<^sub>R (b y *\<^sub>R gb y) - (c y *\<^sub>R ga y + a y *\<^sub>R gc y))"
  have Dp: "D p > 0" using indef unfolding D_def by simp

  \<comment> \<open>STEP 1: pick the radius so that D>0 and a\<noteq>0 throughout\<close>
  have cD0: "continuous_on (ball p \<rho>0) D"
    unfolding D_def using ca0 cb0 cc0 by (intro continuous_intros)
  define U where "U = (ball p \<rho>0 \<inter> D -` {0<..}) \<inter> (ball p \<rho>0 \<inter> a -` (-{0::real}))"
  have opU: "open U"
    unfolding U_def
    by (intro open_Int continuous_open_preimage[OF cD0 open_ball]
              continuous_open_preimage[OF ca0 open_ball]) auto
  have pU: "p \<in> U" unfolding U_def using \<rho>0 a0 Dp by simp
  obtain \<rho>1 where \<rho>1: "\<rho>1 > 0" "ball p \<rho>1 \<subseteq> U"
    using opU pU open_contains_ball by metis
  define \<rho> where "\<rho> = min \<rho>1 \<rho>0"
  have rpos: "0 < \<rho>" using \<rho>1 \<rho>0 unfolding \<rho>_def by simp
  have rle: "\<rho> \<le> \<rho>0" unfolding \<rho>_def by simp
  have ballsub: "ball p \<rho> \<subseteq> ball p \<rho>0" unfolding \<rho>_def by (simp add: subset_ball)
  have Dpos: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> D x > 0"
    and anz: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> a x \<noteq> 0"
  proof -
    fix x :: "real^2" assume "x \<in> ball p \<rho>"
    then have "x \<in> ball p \<rho>1" unfolding \<rho>_def by auto
    then have "x \<in> U" using \<rho>1 by auto
    thus "D x > 0" "a x \<noteq> 0" unfolding U_def by auto
  qed

  \<comment> \<open>continuity of all pieces on the small ball\<close>
  have ca: "continuous_on (ball p \<rho>) a" using ca0 ballsub by (rule continuous_on_subset)
  have cb: "continuous_on (ball p \<rho>) b" using cb0 ballsub by (rule continuous_on_subset)
  have cc: "continuous_on (ball p \<rho>) c" using cc0 ballsub by (rule continuous_on_subset)
  have cga: "continuous_on (ball p \<rho>) ga" using cga0 ballsub by (rule continuous_on_subset)
  have cgb: "continuous_on (ball p \<rho>) gb" using cgb0 ballsub by (rule continuous_on_subset)
  have cgc: "continuous_on (ball p \<rho>) gc" using cgc0 ballsub by (rule continuous_on_subset)
  have cD: "continuous_on (ball p \<rho>) D"
    unfolding D_def using ca cb cc by (intro continuous_intros)
  have csqrtD: "continuous_on (ball p \<rho>) (\<lambda>y. sqrt (D y))"
    using cD by (rule continuous_on_real_sqrt)
  have sqrtnz: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> sqrt (D x) \<noteq> 0"
  proof -
    fix x :: "real^2" assume "x \<in> ball p \<rho>"
    then have "D x > 0" by (rule Dpos)
    thus "sqrt (D x) \<noteq> 0" by simp
  qed
  have cgD: "continuous_on (ball p \<rho>) gD"
    unfolding gD_def using ca cb cc cga cgb cgc by (intro continuous_intros)
  have cinv: "continuous_on (ball p \<rho>) (\<lambda>y. inverse (sqrt (D y)) / 2)"
    using csqrtD sqrtnz cD by (intro continuous_intros) auto

  \<comment> \<open>STEP 2: the roots and their gradients\<close>
  define rp :: "real^2 \<Rightarrow> real" where "rp = (\<lambda>y. (- b y + sqrt (D y)) / a y)"
  define rm :: "real^2 \<Rightarrow> real" where "rm = (\<lambda>y. (- b y - sqrt (D y)) / a y)"
  define gnp :: "real^2 \<Rightarrow> real^2"
    where "gnp = (\<lambda>y. - gb y + (inverse (sqrt (D y)) / 2) *\<^sub>R gD y)"
  define gnm :: "real^2 \<Rightarrow> real^2"
    where "gnm = (\<lambda>y. - gb y - (inverse (sqrt (D y)) / 2) *\<^sub>R gD y)"
  define grp :: "real^2 \<Rightarrow> real^2"
    where "grp = (\<lambda>y. (a y / (a y * a y)) *\<^sub>R gnp y
                       - ((- b y + sqrt (D y)) / (a y * a y)) *\<^sub>R ga y)"
  define grm :: "real^2 \<Rightarrow> real^2"
    where "grm = (\<lambda>y. (a y / (a y * a y)) *\<^sub>R gnm y
                       - ((- b y - sqrt (D y)) / (a y * a y)) *\<^sub>R ga y)"

  \<comment> \<open>derivative of the sqrt(D) bit, valid on the small ball\<close>
  have dsqrt: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow>
      ((\<lambda>y. sqrt (D y)) has_derivative (\<lambda>h. inner ((inverse (sqrt (D x)) / 2) *\<^sub>R gD x) h)) (at x)"
  proof -
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    then have xin0: "x \<in> ball p \<rho>0" using ballsub by blast
    have dD: "(D has_derivative (\<lambda>h. inner (gD x) h)) (at x)"
      unfolding D_def gD_def
      apply (rule has_derivative_eq_rhs)
       apply (rule derivative_intros da[OF xin0] db[OF xin0] dc[OF xin0])+
      apply (rule ext)
      apply (simp add: inner_diff_left inner_add_left inner_scaleR_left power2_eq_square algebra_simps)
      done
    show "((\<lambda>y. sqrt (D y)) has_derivative (\<lambda>h. inner ((inverse (sqrt (D x)) / 2) *\<^sub>R gD x) h)) (at x)"
      apply (rule has_derivative_eq_rhs)
       apply (rule has_derivative_real_sqrt[OF Dpos[OF xin] dD])
      apply (rule ext)
      apply (simp add: inner_scaleR_left)
      done
  qed

  \<comment> \<open>C1field rp grp\<close>
  have rpC1: "C1field rp grp (ball p \<rho>)"
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    then have xin0: "x \<in> ball p \<rho>0" using ballsub by blast
    have dnp: "((\<lambda>y. - b y + sqrt (D y)) has_derivative (\<lambda>h. inner (gnp x) h)) (at x)"
      unfolding gnp_def
      apply (rule has_derivative_eq_rhs)
       apply (rule has_derivative_add has_derivative_minus db[OF xin0] dsqrt[OF xin])+
      apply (rule ext)
      apply (simp add: inner_diff_left inner_add_left inner_minus_left inner_scaleR_left)
      done
    have dq: "(rp has_derivative
        (\<lambda>h. (inner (gnp x) h * a x - (- b x + sqrt (D x)) * inner (ga x) h) / (a x * a x))) (at x)"
      unfolding rp_def by (rule has_derivative_divide'[OF dnp da[OF xin0] anz[OF xin]])
    have match: "(\<lambda>h. (inner (gnp x) h * a x - (- b x + sqrt (D x)) * inner (ga x) h) / (a x * a x))
               = (\<lambda>h. inner (grp x) h)"
      unfolding grp_def
      by (rule ext) (simp add: inner_diff_left inner_scaleR_left field_simps)
    show "(rp has_derivative (\<lambda>h. inner (grp x) h)) (at x)" using dq unfolding match .
  next
    have cden: "continuous_on (ball p \<rho>) (\<lambda>y. a y / (a y * a y))"
      using ca anz by (intro continuous_intros) auto
    have cnump: "continuous_on (ball p \<rho>) (\<lambda>y. (- b y + sqrt (D y)) / (a y * a y))"
      using cb csqrtD ca anz cD by (intro continuous_intros) auto
    have cgnp: "continuous_on (ball p \<rho>) gnp"
      unfolding gnp_def using cgb cinv cgD
      by (intro continuous_on_add continuous_on_minus continuous_on_scaleR)
    show "continuous_on (ball p \<rho>) grp"
      unfolding grp_def using cden cgnp cnump cga
      by (intro continuous_on_diff continuous_on_scaleR)
  qed

  \<comment> \<open>C1field rm grm (mirror, sign flip on sqrt)\<close>
  have rmC1: "C1field rm grm (ball p \<rho>)"
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    then have xin0: "x \<in> ball p \<rho>0" using ballsub by blast
    have dnm: "((\<lambda>y. - b y - sqrt (D y)) has_derivative (\<lambda>h. inner (gnm x) h)) (at x)"
      unfolding gnm_def
      apply (rule has_derivative_eq_rhs)
       apply (rule has_derivative_diff has_derivative_minus db[OF xin0] dsqrt[OF xin])+
      apply (rule ext)
      apply (simp add: inner_diff_left inner_add_left inner_minus_left inner_scaleR_left)
      done
    have dq: "(rm has_derivative
        (\<lambda>h. (inner (gnm x) h * a x - (- b x - sqrt (D x)) * inner (ga x) h) / (a x * a x))) (at x)"
      unfolding rm_def by (rule has_derivative_divide'[OF dnm da[OF xin0] anz[OF xin]])
    have match: "(\<lambda>h. (inner (gnm x) h * a x - (- b x - sqrt (D x)) * inner (ga x) h) / (a x * a x))
               = (\<lambda>h. inner (grm x) h)"
      unfolding grm_def
      by (rule ext) (simp add: inner_diff_left inner_scaleR_left field_simps)
    show "(rm has_derivative (\<lambda>h. inner (grm x) h)) (at x)" using dq unfolding match .
  next
    have cden: "continuous_on (ball p \<rho>) (\<lambda>y. a y / (a y * a y))"
      using ca anz by (intro continuous_intros) auto
    have cnumm: "continuous_on (ball p \<rho>) (\<lambda>y. (- b y - sqrt (D y)) / (a y * a y))"
      using cb csqrtD ca anz cD by (intro continuous_intros) auto
    have cgnm: "continuous_on (ball p \<rho>) gnm"
      unfolding gnm_def using cgb cinv cgD
      by (intro continuous_on_diff continuous_on_minus continuous_on_scaleR)
    show "continuous_on (ball p \<rho>) grm"
      unfolding grm_def using cden cgnm cnumm cga
      by (intro continuous_on_diff continuous_on_scaleR)
  qed

  \<comment> \<open>STEP 3: transversality of the roots at p\<close>
  have pin: "p \<in> ball p \<rho>" using rpos by simp
  have rootneq: "rp p \<noteq> rm p"
  proof -
    have "sqrt (D p) > 0" using Dp by simp
    moreover have "a p \<noteq> 0" using a0 .
    ultimately have "(- b p + sqrt (D p)) / a p \<noteq> (- b p - sqrt (D p)) / a p"
      by (simp add: divide_eq_eq)
    thus ?thesis unfolding rp_def rm_def .
  qed

  \<comment> \<open>STEP 4: the factoring identity (Vieta).  Abstract sqrt into a fresh \<open>s\<close> so
        \<open>field_simps\<close> treats it opaquely; close via \<open>s * s = b\<^sup>2 - a c\<close>.\<close>
  have vieta: "\<And>ax bx cx Y1 Y2 :: real. ax \<noteq> 0 \<Longrightarrow> 0 \<le> bx^2 - ax * cx \<Longrightarrow>
      ax * Y1^2 + 2 * bx * Y1 * Y2 + cx * Y2^2
        = ax * (Y1 - (- bx + sqrt (bx^2 - ax * cx)) / ax * Y2)
              * (Y1 - (- bx - sqrt (bx^2 - ax * cx)) / ax * Y2)"
  proof -
    fix ax bx cx Y1 Y2 :: real
    assume axnz: "ax \<noteq> 0" and Dnn: "0 \<le> bx^2 - ax * cx"
    define s where "s = sqrt (bx^2 - ax * cx)"
    have ss: "s * s = bx * bx - ax * cx"
      unfolding s_def using Dnn by (simp add: power2_eq_square[symmetric])
    show "ax * Y1^2 + 2 * bx * Y1 * Y2 + cx * Y2^2
          = ax * (Y1 - (- bx + sqrt (bx^2 - ax * cx)) / ax * Y2)
                * (Y1 - (- bx - sqrt (bx^2 - ax * cx)) / ax * Y2)"
      unfolding s_def[symmetric] using axnz by (simp add: field_simps power2_eq_square ss)
  qed
  have factor: "\<And>x Y1 Y2. x \<in> ball p \<rho> \<Longrightarrow>
      a x * Y1\<^sup>2 + 2 * b x * Y1 * Y2 + c x * Y2\<^sup>2
        = a x * (Y1 - rp x * Y2) * (Y1 - rm x * Y2)"
  proof -
    fix x :: "real^2" and Y1 Y2 :: real assume xin: "x \<in> ball p \<rho>"
    have axnz: "a x \<noteq> 0" using anz[OF xin] .
    have Dnn: "0 \<le> (b x)^2 - a x * c x" using Dpos[OF xin] unfolding D_def by simp
    show "a x * Y1\<^sup>2 + 2 * b x * Y1 * Y2 + c x * Y2\<^sup>2
          = a x * (Y1 - rp x * Y2) * (Y1 - rm x * Y2)"
      unfolding rp_def rm_def D_def by (rule vieta[OF axnz Dnn])
  qed

  show ?thesis
    by (rule that[OF rpos rle rpC1 rmC1 rootneq factor])
qed

subsection \<open>STUB 2 (implicit function): C1 zero set of a regular scalar field is a C1 arc\<close>

text \<open>A C1 scalar field with nonzero gradient at \<open>p\<close> has, locally, a zero set that is a single
  C1 arc through \<open>p\<close>.  This is the implicit function theorem; derive it from
  @{thm inverse_function_theorem} (Derivative.thy), exactly as the proven
  \<open>crossTheta_local_C1_graph\<close> does for the specific case.  AGENT TARGET.\<close>

text \<open>Component-assembly: the graph map over coordinate 1 has the expected derivative.\<close>

lemma has_derivative_graph_map_1:
  fixes lf :: "real^2 \<Rightarrow> real" and T :: "real^2 \<Rightarrow> real" and z :: "real^2"
  assumes "(lf has_derivative T) (at z)"
  shows "((\<lambda>z. vector [z$1, lf z] :: real^2) has_derivative (\<lambda>h. vector [h$1, T h])) (at z)"
proof -
  have e: "(\<lambda>z. vector [z$1, lf z] :: real^2)
         = (\<lambda>z. (z$1) *\<^sub>R axis 1 1 + (lf z) *\<^sub>R axis 2 1)"
    by (rule ext)
       (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                  vector_add_component vector_scaleR_component axis_def)
  have d1: "((\<lambda>z::real^2. z$1) has_derivative (\<lambda>h. h$1)) (at z)"
    by (simp add: bounded_linear_vec_nth bounded_linear_imp_has_derivative)
  have hd: "((\<lambda>z. (z$1) *\<^sub>R axis 1 1 + (lf z) *\<^sub>R (axis 2 1 :: real^2))
          has_derivative (\<lambda>h. (h$1) *\<^sub>R axis 1 1 + (T h) *\<^sub>R (axis 2 1 :: real^2))) (at z)"
    by (rule derivative_eq_intros d1 assms refl)+
  have eq2: "(\<lambda>h. (h$1) *\<^sub>R axis 1 1 + (T h) *\<^sub>R (axis 2 1 :: real^2))
               = (\<lambda>h. vector [h$1, T h] :: real^2)"
    by (rule ext)
       (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                  vector_add_component vector_scaleR_component axis_def)
  from hd show ?thesis unfolding e eq2[symmetric] .
qed

text \<open>CORE: the \<open>\<partial>\<^sub>2 lf \<noteq> 0\<close> case --- graph over coordinate 1.\<close>

lemma level_zero_C1_arc_2:
  fixes lf :: "real^2 \<Rightarrow> real" and glf :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0" and lC1: "C1field lf glf (ball p \<rho>0)"
    and lp: "lf p = 0" and reg: "glf p $ 2 \<noteq> 0"
  obtains \<gamma> :: "real \<Rightarrow> real^2" and a b \<rho> :: real where "a \<le> b" "0 < \<rho>"
      "\<gamma> C1_differentiable_on {a..b}" "p \<in> \<gamma> ` {a..b}"
      "{x. lf x = 0} \<inter> ball p \<rho> \<subseteq> \<gamma> ` {a..b}"
      "\<gamma> ` {a..b} \<subseteq> ball p \<rho>0"
      "inj_on \<gamma> {a..b}"
      "\<gamma> ` {a..b} \<subseteq> {x. lf x = 0}"
proof -
  have lder: "(lf has_derivative (\<lambda>h. inner (glf x) h)) (at x)" if "x \<in> ball p \<rho>0" for x :: "real^2"
    using lC1 that unfolding C1field_def by blast
  have gcont: "continuous_on (ball p \<rho>0) glf" using lC1 unfolding C1field_def by blast
  define D1 :: "real^2 \<Rightarrow> real" where "D1 = (\<lambda>z::real^2. glf z $ 1)"
  define D2 :: "real^2 \<Rightarrow> real" where "D2 = (\<lambda>z::real^2. glf z $ 2)"
  \<comment> \<open>shrink to a ball inside \<open>ball p \<rho>0\<close> where \<open>D2 \<noteq> 0\<close>\<close>
  have D2cont: "continuous_on (ball p \<rho>0) D2"
    unfolding D2_def using gcont
    by (auto intro!: continuous_on_compose2[OF linear_continuous_on[OF bounded_linear_vec_nth]])
  have pball0: "p \<in> ball p \<rho>0" using \<rho>0 by simp
  have D2reg: "D2 p \<noteq> 0" using reg by (simp add: D2_def)
  have D2atp: "continuous (at p) D2"
    using D2cont pball0 open_ball
    by (simp add: continuous_on_eq_continuous_at)
  have "\<forall>\<^sub>F x in at p. D2 x \<noteq> 0"
    using D2atp D2reg unfolding continuous_at by (rule tendsto_imp_eventually_ne)
  then obtain d1 where d1pos: "d1 > 0" and d1ne: "\<And>x. x \<in> ball p d1 \<Longrightarrow> x \<noteq> p \<Longrightarrow> D2 x \<noteq> 0"
    unfolding eventually_at by (auto simp: dist_commute)
  define \<epsilon>0 where "\<epsilon>0 = min d1 \<rho>0"
  have \<epsilon>00: "\<epsilon>0 > 0" using d1pos \<rho>0 by (simp add: \<epsilon>0_def)
  have ballin: "ball p \<epsilon>0 \<subseteq> ball p \<rho>0" by (simp add: \<epsilon>0_def subset_ball)
  have D2ne0: "D2 z \<noteq> 0" if "z \<in> ball p \<epsilon>0" for z :: "real^2"
  proof (cases "z = p")
    case True thus ?thesis using D2reg by simp
  next
    case False
    have "z \<in> ball p d1" using that by (simp add: \<epsilon>0_def)
    thus ?thesis using d1ne[OF _ False] by blast
  qed
  define H :: "real^2 \<Rightarrow> real^2" where "H = (\<lambda>z. vector [z$1, lf z])"
  define gi :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2" where
    "gi = (\<lambda>x k. vector [k$1, (k$2 - D1 x * k$1) / D2 x])"
  \<comment> \<open>the derivative of \<open>H\<close> on the ball\<close>
  have Hder: "(H has_derivative (\<lambda>h. vector [h$1, D1 x * h$1 + D2 x * h$2])) (at x)"
    if x: "x \<in> ball p \<epsilon>0" for x :: "real^2"
  proof -
    have inrho: "x \<in> ball p \<rho>0" using ballin x by blast
    have "(lf has_derivative (\<lambda>h. D1 x * h$1 + D2 x * h$2)) (at x)"
    proof -
      have "(lf has_derivative (\<lambda>h. inner (glf x) h)) (at x)" using lder[OF inrho] .
      moreover have "inner (glf x) h = D1 x * h$1 + D2 x * h$2" for h :: "real^2"
        unfolding D1_def D2_def by (simp add: inner_vec_def sum_2)
      ultimately show ?thesis by simp
    qed
    thus ?thesis unfolding H_def by (rule has_derivative_graph_map_1)
  qed
  \<comment> \<open>injectivity of \<open>H\<close> on the ball via Rolle on vertical fibres\<close>
  have fibre_fd: "((\<lambda>t. lf (vector [c, t])) has_field_derivative D2 (vector [c, t])) (at t)"
    if cb: "vector [c, t] \<in> ball p \<epsilon>0" for c t :: real
  proof -
    have inrho: "vector [c, t] \<in> ball p \<rho>0" using ballin cb by blast
    have line_der: "((\<lambda>u::real. vector [c, u] :: real^2) has_derivative (\<lambda>du. du *\<^sub>R axis 2 1)) (at t)"
    proof -
      have eq: "(\<lambda>u::real. vector [c, u] :: real^2) = (\<lambda>u. (c *\<^sub>R axis 1 1) + u *\<^sub>R axis 2 1)"
        by (rule ext)
           (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                      vector_add_component vector_scaleR_component axis_def)
      show ?thesis unfolding eq by (auto intro!: derivative_eq_intros)
    qed
    have comp: "((lf \<circ> (\<lambda>u. vector [c, u])) has_derivative
                  ((\<lambda>h. inner (glf (vector [c, t])) h) \<circ> (\<lambda>du. du *\<^sub>R axis 2 1))) (at t)"
      by (rule diff_chain_at[OF line_der lder[OF inrho]])
    have eqf: "((\<lambda>h. inner (glf (vector [c, t])) h) \<circ> (\<lambda>du. du *\<^sub>R axis 2 1))
             = (*) (D2 (vector [c, t]))"
      by (rule ext) (simp add: D2_def comp_def cart_eq_inner_axis mult.commute)
    have lhs: "(lf \<circ> (\<lambda>u. vector [c, u])) = (\<lambda>u. lf (vector [c, u]))"
      by (simp add: comp_def)
    from comp have "((\<lambda>u. lf (vector [c, u])) has_derivative (*) (D2 (vector [c, t]))) (at t)"
      unfolding eqf lhs .
    thus ?thesis by (simp add: has_field_derivative_def)
  qed
  have fibre_in: "vector [c, \<xi>] \<in> ball p \<epsilon>0"
    if zb: "z \<in> ball p \<epsilon>0" and z'b: "z' \<in> ball p \<epsilon>0" and c1: "z$1 = c" and c2: "z'$1 = c"
       and bet: "\<xi> \<in> closed_segment (z$2) (z'$2)" for z z' :: "real^2" and c \<xi> :: real
  proof -
    obtain \<alpha> where l: "0 \<le> \<alpha>" "\<alpha> \<le> 1" and xeq: "\<xi> = (1 - \<alpha>) * (z$2) + \<alpha> * (z'$2)"
      using bet by (auto simp: closed_segment_def)
    have eqv: "vector [c, \<xi>] = (1 - \<alpha>) *\<^sub>R z + \<alpha> *\<^sub>R z'"
      using c1 c2 xeq
      by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                    vector_add_component vector_scaleR_component algebra_simps)
    have "vector [c, \<xi>] \<in> closed_segment z z'"
      unfolding closed_segment_def using l eqv by (auto intro!: exI[where x = \<alpha>])
    thus ?thesis
      using zb z'b convex_ball convex_contains_segment by blast
  qed
  have inj: "inj_on H (ball p \<epsilon>0)"
  proof (rule inj_onI)
    fix z z' :: "real^2" assume zb: "z \<in> ball p \<epsilon>0" and z'b: "z' \<in> ball p \<epsilon>0"
      and Heq: "H z = H z'"
    have c_eq: "z'$1 = z$1" using Heq unfolding H_def by (metis vector_2)
    have lf_eq: "lf z = lf z'" using Heq unfolding H_def by (metis vector_2)
    have zrw: "z = vector [z$1, z$2]" and z'rw: "z' = vector [z'$1, z'$2]"
      by (simp_all add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2)
    show "z = z'"
    proof (rule ccontr)
      assume ne: "z \<noteq> z'"
      have w2: "z$2 \<noteq> z'$2" using ne c_eq zrw z'rw by (metis)
      define f where "f = (\<lambda>t. lf (vector [z$1, t]))"
      have fz: "f (z$2) = lf z" using zrw by (simp add: f_def)
      have fz': "f (z'$2) = lf z'" using z'rw c_eq by (simp add: f_def)
      have feq: "f (z$2) = f (z'$2)" using fz fz' lf_eq by simp
      define lo where "lo = min (z$2) (z'$2)"
      define hi where "hi = max (z$2) (z'$2)"
      have lohi: "lo < hi" using w2 by (simp add: lo_def hi_def)
      have flohi: "f lo = f hi"
        using feq by (auto simp: lo_def hi_def min_def max_def)
      \<comment> \<open>every fibre point between \<open>z$2\<close>,\<open>z'$2\<close> stays in the ball, so \<open>f\<close> is differentiable there\<close>
      have fib: "vector [z$1, t] \<in> ball p \<epsilon>0" if "t \<in> closed_segment (z$2) (z'$2)" for t :: real
        by (rule fibre_in[where z=z and z'=z' and c="z$1", OF zb z'b refl c_eq that])
      have segLH: "closed_segment lo hi = closed_segment (z$2) (z'$2)"
        by (simp add: lo_def hi_def closed_segment_eq_real_ivl)
      have derf: "(f has_field_derivative D2 (vector [z$1, t])) (at t)"
        if "t \<in> closed_segment (z$2) (z'$2)" for t
        using fibre_fd[OF fib[OF that]] by (simp add: f_def)
      have segIvl: "closed_segment (z$2) (z'$2) = {lo..hi}"
        using segLH lohi by (simp add: closed_segment_eq_real_ivl lo_def hi_def)
      have contf: "continuous_on {lo..hi} f"
      proof -
        have "continuous (at t) f" if "lo \<le> t" "t \<le> hi" for t
        proof -
          have "t \<in> closed_segment (z$2) (z'$2)"
            using that segIvl by simp
          thus ?thesis using DERIV_isCont[OF derf] by blast
        qed
        thus ?thesis by (simp add: continuous_at_imp_continuous_on)
      qed
      have difff: "f differentiable (at t)" if "lo < t" "t < hi" for t
      proof -
        have "t \<in> closed_segment (z$2) (z'$2)"
          using that segIvl by simp
        thus ?thesis using derf real_differentiable_def by blast
      qed
      obtain \<xi> where xi: "lo < \<xi>" "\<xi> < hi" and d0: "DERIV f \<xi> :> 0"
        using Rolle[OF lohi flohi contf] difff by auto
      have xiseg: "\<xi> \<in> closed_segment (z$2) (z'$2)"
        using xi segIvl by simp
      have "DERIV f \<xi> :> D2 (vector [z$1, \<xi>])" using derf[OF xiseg] by simp
      hence z0: "D2 (vector [z$1, \<xi>]) = 0" using d0 DERIV_unique by blast
      have "vector [z$1, \<xi>] \<in> ball p \<epsilon>0" by (rule fib[OF xiseg])
      thus False using D2ne0 z0 by blast
    qed
  qed
  \<comment> \<open>homeomorphism via invariance of domain\<close>
  have contH: "continuous_on (ball p \<epsilon>0) H"
  proof -
    have veq: "H = (\<lambda>z. (z$1) *\<^sub>R axis 1 1 + (lf z) *\<^sub>R axis 2 1)"
      unfolding H_def
      by (rule ext)
         (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                    vector_add_component vector_scaleR_component axis_def)
    have lfcont: "continuous_on (ball p \<epsilon>0) lf"
    proof -
      have "continuous (at x) lf" if "x \<in> ball p \<epsilon>0" for x :: "real^2"
        using lder[OF ballin[THEN subsetD, OF that]] has_derivative_continuous by blast
      thus ?thesis by (simp add: continuous_at_imp_continuous_on)
    qed
    show ?thesis
      unfolding veq
      by (intro continuous_intros lfcont
                linear_continuous_on[OF bounded_linear_vec_nth])
  qed
  obtain g where homeo: "homeomorphism (ball p \<epsilon>0) (H ` ball p \<epsilon>0) H g"
    using invariance_of_domain_homeomorphism[OF open_ball contH _ inj] by auto
  have openimg: "open (H ` ball p \<epsilon>0)"
    by (rule invariance_of_domain[OF contH open_ball inj])
  \<comment> \<open>inverse derivative\<close>
  have ginv_bl: "bounded_linear (gi x)" if "D2 x \<noteq> 0" for x :: "real^2"
  proof -
    have "linear (gi x)"
    proof (rule linearI)
      fix u v :: "real^2"
      show "gi x (u + v) = gi x u + gi x v"
        unfolding gi_def using that
        by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                      vector_add_component field_simps)
    next
      fix c :: real and u :: "real^2"
      show "gi x (c *\<^sub>R u) = c *\<^sub>R gi x u"
        unfolding gi_def using that
        by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                      vector_scaleR_component field_simps)
    qed
    thus ?thesis by (simp add: linear_conv_bounded_linear)
  qed
  have ginv_id: "gi x \<circ> (\<lambda>h. vector [h$1, D1 x * h$1 + D2 x * h$2]) = id" if "D2 x \<noteq> 0" for x :: "real^2"
    unfolding gi_def comp_def
    by (rule ext)
       (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2 that field_simps)
  have gder: "(g has_derivative gi x) (at (H x))" if x: "x \<in> ball p \<epsilon>0" for x :: "real^2"
  proof (rule has_derivative_inverse_basic_x[OF Hder[OF x]])
    show "bounded_linear (gi x)" by (rule ginv_bl[OF D2ne0[OF x]])
    show "gi x \<circ> (\<lambda>h. vector [h$1, D1 x * h$1 + D2 x * h$2]) = id" by (rule ginv_id[OF D2ne0[OF x]])
    show "continuous (at (H x)) g"
      using homeomorphism_cont2[OF homeo] openimg x
      by (auto simp: continuous_on_eq_continuous_at)
    show "g (H x) = x" by (rule homeomorphism_apply1[OF homeo x])
    show "open (H ` ball p \<epsilon>0)" by (rule openimg)
    show "H x \<in> H ` ball p \<epsilon>0" using x by simp
    show "\<And>y. y \<in> H ` ball p \<epsilon>0 \<Longrightarrow> H (g y) = y" by (rule homeomorphism_apply2[OF homeo])
  qed
  \<comment> \<open>the arc \<open>\<phi> s = g (s,0)\<close>\<close>
  define \<phi> :: "real \<Rightarrow> real^2" where "\<phi> = (\<lambda>s. g (vector [s, 0]))"
  have Hp: "H p = vector [p$1, 0]" unfolding H_def using lp by simp
  have pball: "p \<in> ball p \<epsilon>0" using \<epsilon>00 by simp
  have v0in: "vector [p$1, 0] \<in> H ` ball p \<epsilon>0" by (metis Hp imageI pball)
  have iotacont: "continuous_on UNIV (\<lambda>s::real. vector [s, 0] :: real^2)"
  proof -
    have eq: "(\<lambda>s::real. vector [s, 0] :: real^2) = (\<lambda>s. s *\<^sub>R axis 1 1)"
      by (rule ext)
         (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                    vector_scaleR_component axis_def)
    show ?thesis unfolding eq by (auto intro!: continuous_intros)
  qed
  have sopen: "open {s::real. vector [s, 0] \<in> H ` ball p \<epsilon>0}"
    using open_vimage[OF openimg iotacont] by (simp add: vimage_def)
  obtain \<eta> where \<eta>0: "\<eta> > 0" and \<eta>in: "ball (p$1) \<eta> \<subseteq> {s::real. vector [s, 0] \<in> H ` ball p \<epsilon>0}"
    using sopen v0in open_contains_ball by (metis (mono_tags, lifting) mem_Collect_eq)
  define a where "a = p$1 - \<eta>/2"
  define b where "b = p$1 + \<eta>/2"
  have ab_in: "vector [s, 0] \<in> H ` ball p \<epsilon>0" if "s \<in> {a..b}" for s :: real
  proof -
    have "s \<in> ball (p$1) \<eta>" using that \<eta>0 by (auto simp: a_def b_def dist_real_def)
    thus ?thesis using \<eta>in by blast
  qed
  have phiH: "H (\<phi> s) = vector [s, 0]" if "s \<in> {a..b}" for s :: real
    unfolding \<phi>_def using homeomorphism_apply2[OF homeo ab_in[OF that]] .
  have phi_ball: "\<phi> s \<in> ball p \<epsilon>0" if "s \<in> {a..b}" for s :: real
  proof -
    have "\<phi> s \<in> g ` (H ` ball p \<epsilon>0)" unfolding \<phi>_def using ab_in[OF that] by simp
    also have "g ` (H ` ball p \<epsilon>0) = ball p \<epsilon>0"
      using homeo by (simp add: homeomorphism_def)
    finally show ?thesis .
  qed
  have phi0: "lf (\<phi> s) = 0" if "s \<in> {a..b}" for s :: real
  proof -
    have "lf (\<phi> s) = (H (\<phi> s)) $ 2" unfolding H_def by (simp add: vector_2)
    also have "\<dots> = 0" using phiH[OF that] by (simp add: vector_2)
    finally show ?thesis .
  qed
  \<comment> \<open>velocity \<open>\<phi>' s = (1, -D1/D2)\<close>, continuous \<Rightarrow> C1\<close>
  define vel :: "real \<Rightarrow> real^2" where "vel = (\<lambda>s. vector [1, - D1 (\<phi> s) / D2 (\<phi> s)])"
  have phivec: "(\<phi> has_vector_derivative vel s) (at s)" if s: "s \<in> {a..b}" for s :: real
  proof -
    have iotader: "((\<lambda>s::real. vector [s, 0] :: real^2) has_derivative (\<lambda>t. vector [t, 0])) (at s)"
    proof -
      have eq: "\<And>u::real. (vector [u, 0] :: real^2) = u *\<^sub>R axis 1 1"
        by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                      vector_scaleR_component axis_def)
      show ?thesis unfolding eq by (auto intro!: derivative_eq_intros)
    qed
    have gd: "(g has_derivative gi (\<phi> s)) (at (vector [s, 0]))"
      using gder[OF phi_ball[OF s]] phiH[OF s] by simp
    have "((g \<circ> (\<lambda>s::real. vector [s, 0])) has_derivative (gi (\<phi> s) \<circ> (\<lambda>t. vector [t, 0]))) (at s)"
      by (rule diff_chain_at[OF iotader gd])
    moreover have "(gi (\<phi> s) \<circ> (\<lambda>t::real. vector [t, 0])) = (\<lambda>t. t *\<^sub>R vel s)"
      unfolding gi_def vel_def comp_def
      by (rule ext)
         (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                    vector_scaleR_component D2ne0[OF phi_ball[OF s]] field_simps)
    ultimately have "((g \<circ> (\<lambda>s::real. vector [s, 0])) has_vector_derivative vel s) (at s)"
      by (simp add: has_vector_derivative_def)
    thus ?thesis by (simp add: \<phi>_def comp_def)
  qed
  have velcont: "continuous_on {a..b} vel"
  proof -
    have phicont: "continuous_on {a..b} \<phi>"
      by (meson phivec continuous_at_imp_continuous_on has_vector_derivative_continuous)
    have proj: "continuous_on UNIV (\<lambda>z::real^2. z $ i)" for i
      using linear_continuous_on[OF bounded_linear_vec_nth] by blast
    have D1c: "continuous_on (ball p \<rho>0) D1"
      unfolding D1_def using gcont
      by (auto intro!: continuous_on_compose2[OF linear_continuous_on[OF bounded_linear_vec_nth]])
    have phimaps: "\<phi> ` {a..b} \<subseteq> ball p \<rho>0" using phi_ball ballin by blast
    have num: "continuous_on {a..b} (\<lambda>s. D1 (\<phi> s))"
      by (rule continuous_on_compose2[OF D1c phicont phimaps])
    have D2c: "continuous_on (ball p \<rho>0) D2" by (rule D2cont)
    have den: "continuous_on {a..b} (\<lambda>s. D2 (\<phi> s))"
      by (rule continuous_on_compose2[OF D2c phicont phimaps])
    have dne: "\<And>s. s \<in> {a..b} \<Longrightarrow> D2 (\<phi> s) \<noteq> 0"
      using D2ne0 phi_ball by blast
    have kcont: "continuous_on {a..b} (\<lambda>s. - D1 (\<phi> s) / D2 (\<phi> s))"
      using num den dne by (auto intro!: continuous_intros)
    have velrw: "vel = (\<lambda>s. axis 1 1 + (- D1 (\<phi> s) / D2 (\<phi> s)) *\<^sub>R axis (2::2) 1)"
      unfolding vel_def
      by (rule ext)
         (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2 axis_def)
    show ?thesis
      unfolding velrw
      by (intro continuous_on_add continuous_on_scaleR continuous_on_const kcont)
  qed
  have philoc: "\<phi> ` {a..b} \<subseteq> {x. lf x = 0}" using phi0 by auto
  have phiinj: "inj_on \<phi> {a..b}"
  proof (rule inj_onI)
    fix s t assume s: "s \<in> {a..b}" and t: "t \<in> {a..b}" and eq: "\<phi> s = \<phi> t"
    have "(vector [s,0]::real^2) = H (\<phi> s)" using phiH[OF s] by simp
    also have "\<dots> = H (\<phi> t)" using eq by simp
    also have "\<dots> = vector [t,0]" using phiH[OF t] by simp
    finally show "s = t" by (metis vector_2)
  qed
  show ?thesis
  proof (rule that[where a = a and b = b and \<gamma> = \<phi> and \<rho> = "min \<epsilon>0 (\<eta>/2)"])
    show "a \<le> b" using \<eta>0 by (simp add: a_def b_def)
    show "0 < min \<epsilon>0 (\<eta>/2)" using \<epsilon>00 \<eta>0 by simp
    show "\<phi> C1_differentiable_on {a..b}"
      unfolding C1_differentiable_on_def using phivec velcont by blast
    show "p \<in> \<phi> ` {a..b}"
    proof -
      have "\<phi> (p$1) = p"
        unfolding \<phi>_def by (simp add: Hp[symmetric] homeomorphism_apply1[OF homeo pball])
      moreover have "p$1 \<in> {a..b}" using \<eta>0 by (simp add: a_def b_def)
      ultimately show ?thesis by force
    qed
    show "{x. lf x = 0} \<inter> ball p (min \<epsilon>0 (\<eta>/2)) \<subseteq> \<phi> ` {a..b}"
    proof
      fix x :: "real^2" assume "x \<in> {x. lf x = 0} \<inter> ball p (min \<epsilon>0 (\<eta>/2))"
      hence cz: "lf x = 0" and wbe: "dist x p < \<epsilon>0" and wbh: "dist x p < \<eta>/2"
        by (auto simp: dist_commute min_less_iff_conj)
      have xball: "x \<in> ball p \<epsilon>0" using wbe by (simp add: dist_commute)
      have Hx: "H x = vector [x$1, 0]" unfolding H_def using cz by simp
      have "x = g (H x)" using homeomorphism_apply1[OF homeo xball] by simp
      also have "\<dots> = \<phi> (x$1)" by (simp add: \<phi>_def Hx)
      finally have eqphi: "x = \<phi> (x$1)" .
      have "\<bar>x$1 - p$1\<bar> \<le> dist x p"
        using component_le_norm_cart[of "x - p" 1]
        by (simp add: dist_norm vector_minus_component)
      hence "\<bar>x$1 - p$1\<bar> < \<eta>/2" using wbh by simp
      hence "x$1 \<in> {a..b}" unfolding a_def b_def atLeastAtMost_iff by (smt (verit))
      with eqphi show "x \<in> \<phi> ` {a..b}" by blast
    qed
    show "\<phi> ` {a..b} \<subseteq> ball p \<rho>0" using phi_ball ballin by blast
    show "inj_on \<phi> {a..b}" by (rule phiinj)
    show "\<phi> ` {a..b} \<subseteq> {x. lf x = 0}" by (rule philoc)
  qed
qed

text \<open>Coordinate swap, used to reduce the \<open>\<partial>\<^sub>1 lf \<noteq> 0\<close> case to the \<open>\<partial>\<^sub>2\<close> case.\<close>

definition sw :: "real^2 \<Rightarrow> real^2" where "sw z = vector [z$2, z$1]"

lemma sw_components [simp]: "sw z $ 1 = z $ 2" "sw z $ 2 = z $ 1"
  by (simp_all add: sw_def vector_2)

lemma sw_sw [simp]: "sw (sw z) = z"
  by (simp add: sw_def Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2)

lemma sw_linear: "linear sw"
  by (rule linearI)
     (simp_all add: sw_def Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
                    vector_add_component vector_scaleR_component)

lemma sw_bl: "bounded_linear sw"
  using sw_linear by (simp add: linear_conv_bounded_linear)

lemma sw_inner: "inner (sw u) v = inner u (sw v)"
  by (simp add: inner_vec_def sum_2 sw_def vector_2 mult.commute)

lemma sw_dist [simp]: "dist (sw x) (sw y) = dist x y"
proof -
  have "dist (sw x) (sw y) = norm (sw (x - y))"
    by (simp add: dist_norm linear_diff[OF sw_linear])
  also have "\<dots> = norm (x - y)"
    by (simp add: norm_eq_sqrt_inner sw_inner inner_vec_def sum_2 sw_def vector_2)
  finally show ?thesis by (simp add: dist_norm)
qed

lemma sw_ball: "sw ` ball c r = ball (sw c) r"
proof (rule set_eqI)
  fix y :: "real^2"
  have "y \<in> sw ` ball c r \<longleftrightarrow> sw y \<in> ball c r"
    by (metis (no_types, opaque_lifting) imageI image_iff sw_sw)
  also have "\<dots> \<longleftrightarrow> y \<in> ball (sw c) r"
    by (simp add: dist_commute) (metis sw_dist sw_sw dist_commute)
  finally show "(y \<in> sw ` ball c r) = (y \<in> ball (sw c) r)" .
qed

lemma C1_sw_comp:
  fixes \<gamma> :: "real \<Rightarrow> real^2"
  assumes "\<gamma> C1_differentiable_on S"
  shows "(sw \<circ> \<gamma>) C1_differentiable_on S"
proof -
  from assms obtain D where vd: "\<And>x. x \<in> S \<Longrightarrow> (\<gamma> has_vector_derivative D x) (at x)"
    and Dc: "continuous_on S D"
    unfolding C1_differentiable_on_def by blast
  have vd': "((sw \<circ> \<gamma>) has_vector_derivative sw (D x)) (at x)" if "x \<in> S" for x
  proof -
    have "(\<gamma> has_derivative (\<lambda>t. t *\<^sub>R D x)) (at x)"
      using vd[OF that] unfolding has_vector_derivative_def .
    hence "((\<lambda>s. sw (\<gamma> s)) has_derivative (\<lambda>t. sw (t *\<^sub>R D x))) (at x)"
      by (rule bounded_linear.has_derivative[OF sw_bl])
    moreover have "(\<lambda>t. sw (t *\<^sub>R D x)) = (\<lambda>t. t *\<^sub>R sw (D x))"
      by (rule ext) (simp add: linear_cmul[OF sw_linear])
    ultimately show ?thesis
      by (simp add: has_vector_derivative_def comp_def)
  qed
  have "continuous_on S (\<lambda>x. sw (D x))"
    by (rule continuous_on_compose2[OF linear_continuous_on[OF sw_bl] Dc]) auto
  thus ?thesis
    unfolding C1_differentiable_on_def using vd' by force
qed

text \<open>The symmetric case \<open>\<partial>\<^sub>1 lf \<noteq> 0\<close>, by reduction to @{thm level_zero_C1_arc_2} via the swap.\<close>

lemma level_zero_C1_arc_1:
  fixes lf :: "real^2 \<Rightarrow> real" and glf :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0" and lC1: "C1field lf glf (ball p \<rho>0)"
    and lp: "lf p = 0" and reg: "glf p $ 1 \<noteq> 0"
  obtains \<gamma> :: "real \<Rightarrow> real^2" and a b \<rho> :: real where "a \<le> b" "0 < \<rho>"
      "\<gamma> C1_differentiable_on {a..b}" "p \<in> \<gamma> ` {a..b}"
      "{x. lf x = 0} \<inter> ball p \<rho> \<subseteq> \<gamma> ` {a..b}"
      "\<gamma> ` {a..b} \<subseteq> ball p \<rho>0"
      "inj_on \<gamma> {a..b}"
      "\<gamma> ` {a..b} \<subseteq> {x. lf x = 0}"
proof -
  define lf' :: "real^2 \<Rightarrow> real" where "lf' = (\<lambda>x. lf (sw x))"
  define glf' :: "real^2 \<Rightarrow> real^2" where "glf' = (\<lambda>x. sw (glf (sw x)))"
  define p' :: "real^2" where "p' = sw p"
  have lder: "(lf has_derivative (\<lambda>h. inner (glf x) h)) (at x)" if "x \<in> ball p \<rho>0" for x :: "real^2"
    using lC1 that unfolding C1field_def by blast
  have gcont: "continuous_on (ball p \<rho>0) glf" using lC1 unfolding C1field_def by blast
  have swmap: "sw x \<in> ball p \<rho>0" if "x \<in> ball p' \<rho>0" for x :: "real^2"
  proof -
    have "sw x \<in> sw ` ball p' \<rho>0" using that by simp
    also have "sw ` ball p' \<rho>0 = ball (sw p') \<rho>0" by (rule sw_ball)
    also have "sw p' = p" by (simp add: p'_def)
    finally show ?thesis .
  qed
  have lC1': "C1field lf' glf' (ball p' \<rho>0)"
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x :: "real^2" assume x: "x \<in> ball p' \<rho>0"
    have swx: "sw x \<in> ball p \<rho>0" by (rule swmap[OF x])
    have swd: "(sw has_derivative sw) (at x)" by (rule bounded_linear_imp_has_derivative[OF sw_bl])
    have lfd: "(lf has_derivative (\<lambda>h. inner (glf (sw x)) h)) (at (sw x))" by (rule lder[OF swx])
    have "((\<lambda>z. lf (sw z)) has_derivative (\<lambda>z. inner (glf (sw x)) (sw z))) (at x)"
      by (rule has_derivative_compose[OF swd lfd])
    moreover have "(\<lambda>z. inner (glf (sw x)) (sw z)) = (\<lambda>h. inner (glf' x) h)"
      by (rule ext) (simp add: glf'_def sw_inner)
    ultimately show "(lf' has_derivative (\<lambda>h. inner (glf' x) h)) (at x)"
      unfolding lf'_def by simp
  next
    have "continuous_on (ball p' \<rho>0) (\<lambda>x. sw (glf (sw x)))"
    proof (rule continuous_on_compose2[OF linear_continuous_on[OF sw_bl]
                  continuous_on_compose2[OF gcont linear_continuous_on[OF sw_bl]]])
      show "sw ` ball p' \<rho>0 \<subseteq> ball p \<rho>0" using swmap by blast
    qed auto
    thus "continuous_on (ball p' \<rho>0) glf'" unfolding glf'_def .
  qed
  have lp': "lf' p' = 0" using lp by (simp add: lf'_def p'_def)
  have reg': "glf' p' $ 2 \<noteq> 0" using reg by (simp add: glf'_def p'_def)
  obtain \<gamma>' :: "real \<Rightarrow> real^2" and a b \<rho> :: real where
      ab: "a \<le> b" and rho: "0 < \<rho>"
    and c1: "\<gamma>' C1_differentiable_on {a..b}"
    and pin: "p' \<in> \<gamma>' ` {a..b}"
    and cov: "{x. lf' x = 0} \<inter> ball p' \<rho> \<subseteq> \<gamma>' ` {a..b}"
    and imgsub: "\<gamma>' ` {a..b} \<subseteq> ball p' \<rho>0"
    and inj': "inj_on \<gamma>' {a..b}"
    and loc': "\<gamma>' ` {a..b} \<subseteq> {x. lf' x = 0}"
    by (rule level_zero_C1_arc_2[OF \<rho>0 lC1' lp' reg'])
  define \<gamma> :: "real \<Rightarrow> real^2" where "\<gamma> = sw \<circ> \<gamma>'"
  show ?thesis
  proof (rule that[where a=a and b=b and \<rho>=\<rho> and \<gamma>=\<gamma>])
    show "a \<le> b" by (rule ab)
    show "0 < \<rho>" by (rule rho)
    show "\<gamma> C1_differentiable_on {a..b}" unfolding \<gamma>_def by (rule C1_sw_comp[OF c1])
    show "p \<in> \<gamma> ` {a..b}"
    proof -
      from pin obtain t where t: "t \<in> {a..b}" and "p' = \<gamma>' t" by blast
      hence "p = \<gamma> t" unfolding \<gamma>_def p'_def by (simp add: comp_def) (metis sw_sw)
      thus ?thesis using t by blast
    qed
    show "{x. lf x = 0} \<inter> ball p \<rho> \<subseteq> \<gamma> ` {a..b}"
    proof
      fix x :: "real^2" assume "x \<in> {x. lf x = 0} \<inter> ball p \<rho>"
      hence lz: "lf x = 0" and xb: "x \<in> ball p \<rho>" by auto
      have "lf' (sw x) = 0" using lz by (simp add: lf'_def)
      moreover have "sw x \<in> ball p' \<rho>"
        using xb by (simp add: p'_def dist_commute) 
      ultimately have "sw x \<in> \<gamma>' ` {a..b}" using cov by blast
      then obtain t where t: "t \<in> {a..b}" and "sw x = \<gamma>' t" by blast
      hence "x = \<gamma> t" unfolding \<gamma>_def by (simp add: comp_def) (metis sw_sw)
      thus "x \<in> \<gamma> ` {a..b}" using t by blast
    qed
    show "\<gamma> ` {a..b} \<subseteq> ball p \<rho>0"
    proof -
      have "\<gamma> ` {a..b} = sw ` (\<gamma>' ` {a..b})" unfolding \<gamma>_def by (simp add: image_comp)
      also have "\<dots> \<subseteq> sw ` (ball p' \<rho>0)" using imgsub by (rule image_mono)
      also have "sw ` (ball p' \<rho>0) = ball (sw p') \<rho>0" by (rule sw_ball)
      also have "sw p' = p" by (simp add: p'_def)
      finally show ?thesis .
    qed
    show "inj_on \<gamma> {a..b}"
    proof (rule inj_onI)
      fix s t assume "s\<in>{a..b}" "t\<in>{a..b}" "\<gamma> s = \<gamma> t"
      hence "sw (\<gamma>' s) = sw (\<gamma>' t)" by (simp add: \<gamma>_def comp_def)
      hence "\<gamma>' s = \<gamma>' t" by (metis sw_sw)
      thus "s = t" using inj' \<open>s\<in>{a..b}\<close> \<open>t\<in>{a..b}\<close> by (meson inj_onD)
    qed
    show "\<gamma> ` {a..b} \<subseteq> {x. lf x = 0}"
    proof
      fix x assume "x \<in> \<gamma> ` {a..b}"
      then obtain t where t: "t\<in>{a..b}" and "x = \<gamma> t" by blast
      hence xe: "x = sw (\<gamma>' t)" by (simp add: \<gamma>_def comp_def)
      have "\<gamma>' t \<in> \<gamma>' ` {a..b}" using t by (rule imageI)
      hence "lf' (\<gamma>' t) = 0" using loc' by auto
      thus "x \<in> {x. lf x = 0}" using xe by (simp add: lf'_def)
    qed
  qed
qed

text \<open>MAIN: dispatch on which component of the gradient is nonzero.\<close>

lemma level_zero_C1_arc:
  fixes lf :: "real^2 \<Rightarrow> real" and glf :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0" and lC1: "C1field lf glf (ball p \<rho>0)"
    and lp: "lf p = 0" and reg: "glf p \<noteq> 0"
  obtains \<gamma> :: "real \<Rightarrow> real^2" and a b \<rho> :: real where "a \<le> b" "0 < \<rho>"
      "\<gamma> C1_differentiable_on {a..b}" "p \<in> \<gamma> ` {a..b}"
      "{x. lf x = 0} \<inter> ball p \<rho> \<subseteq> \<gamma> ` {a..b}"
      "\<gamma> ` {a..b} \<subseteq> ball p \<rho>0"
      "inj_on \<gamma> {a..b}"
      "\<gamma> ` {a..b} \<subseteq> {x. lf x = 0}"
proof -
  have "glf p $ 1 \<noteq> 0 \<or> glf p $ 2 \<noteq> 0"
    using reg
    by (metis sw_def sw_sw zero_index)
  then consider (c1) "glf p $ 1 \<noteq> 0" | (c2) "glf p $ 2 \<noteq> 0" by blast
  thus thesis
  proof cases
    case c1
    show thesis
      by (rule level_zero_C1_arc_1[OF \<rho>0 lC1 lp c1])
         (rule that)
  next
    case c2
    show thesis
      by (rule level_zero_C1_arc_2[OF \<rho>0 lC1 lp c2])
         (rule that)
  qed
qed

subsection \<open>MAIN: the zero set of an indefinite C1 form is two transverse C1 arcs\<close>

text \<open>Assembled from the two stubs above (no further proof hole).\<close>

theorem saddle_form_two_arcs:
  fixes f a b c :: "real^2 \<Rightarrow> real" and ga gb gc :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0"
    and aC1: "C1field a ga (ball p \<rho>0)" and bC1: "C1field b gb (ball p \<rho>0)"
    and cC1: "C1field c gc (ball p \<rho>0)"
    and a0: "a p \<noteq> 0" and indef: "(b p)\<^sup>2 - a p * c p > 0"
    and form: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow>
        f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
  obtains \<gamma>1 \<gamma>2 :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real where
      "0 < r" "a1 \<le> b1" "a2 \<le> b2"
      "\<gamma>1 C1_differentiable_on {a1..b1}" "\<gamma>2 C1_differentiable_on {a2..b2}"
      "p \<in> \<gamma>1 ` {a1..b1}" "p \<in> \<gamma>2 ` {a2..b2}"
      "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
      "\<gamma>1 ` {a1..b1} \<subseteq> ball p \<rho>0" "\<gamma>2 ` {a2..b2} \<subseteq> ball p \<rho>0"
      "inj_on \<gamma>1 {a1..b1}" "inj_on \<gamma>2 {a2..b2}"
      "\<gamma>1 ` {a1..b1} \<subseteq> {x. f x = 0}" "\<gamma>2 ` {a2..b2} \<subseteq> {x. f x = 0}"
proof -
  \<comment> \<open>STEP 1: \<open>a \<noteq> 0\<close> on a small ball around \<open>p\<close>.\<close>
  have da: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (a has_derivative (\<lambda>h. inner (ga x) h)) (at x)"
    using aC1 unfolding C1field_def by blast
  have ca0: "continuous_on (ball p \<rho>0) a"
    by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
       (use da in \<open>blast intro: has_derivative_continuous\<close>)
  define Ua where "Ua = ball p \<rho>0 \<inter> a -` (-{0::real})"
  have opUa: "open Ua"
    unfolding Ua_def
    by (intro open_Int continuous_open_preimage[OF ca0 open_ball]) auto
  have pUa: "p \<in> Ua" unfolding Ua_def using \<rho>0 a0 by simp
  obtain \<rho>a1 where \<rho>a1: "\<rho>a1 > 0" "ball p \<rho>a1 \<subseteq> Ua"
    using opUa pUa open_contains_ball by metis
  define \<rho>a where "\<rho>a = min \<rho>a1 \<rho>0"
  have \<rho>apos: "\<rho>a > 0" using \<rho>a1 \<rho>0 unfolding \<rho>a_def by simp
  have anz: "\<And>x. x \<in> ball p \<rho>a \<Longrightarrow> a x \<noteq> 0"
  proof -
    fix x :: "real^2" assume "x \<in> ball p \<rho>a"
    then have "x \<in> ball p \<rho>a1" unfolding \<rho>a_def by auto
    then have "x \<in> Ua" using \<rho>a1 by auto
    thus "a x \<noteq> 0" unfolding Ua_def by auto
  qed

  \<comment> \<open>STEP 2: factor the form via @{thm factor_indef_C1}.  Structured elimination so the
      remaining steps run inside the factoring data (no \<open>by metis\<close>/\<open>blast\<close> on the obtains-rule).\<close>
  show ?thesis
  proof (rule factor_indef_C1[OF \<rho>0 aC1 bC1 cC1 a0 indef])
    fix rp rm :: "real^2 \<Rightarrow> real" and grp grm :: "real^2 \<Rightarrow> real^2" and \<rho>1 :: real
    assume rpos1: "0 < \<rho>1" and rle1: "\<rho>1 \<le> \<rho>0"
      and rpC1: "C1field rp grp (ball p \<rho>1)" and rmC1: "C1field rm grm (ball p \<rho>1)"
      and rootneq: "rp p \<noteq> rm p"
      and factor: "\<And>x Y1 Y2. x \<in> ball p \<rho>1 \<Longrightarrow>
          a x * Y1\<^sup>2 + 2 * b x * Y1 * Y2 + c x * Y2\<^sup>2
        = a x * (Y1 - rp x * Y2) * (Y1 - rm x * Y2)"

  \<comment> \<open>STEP 3: the two linear factors and their gradient fields.\<close>
  define lp :: "real^2 \<Rightarrow> real" where "lp = (\<lambda>x. (x-p)$1 - rp x * ((x-p)$2))"
  define lm :: "real^2 \<Rightarrow> real" where "lm = (\<lambda>x. (x-p)$1 - rm x * ((x-p)$2))"
  define glp :: "real^2 \<Rightarrow> real^2"
    where "glp = (\<lambda>x. axis 1 1 - ((x-p)$2) *\<^sub>R grp x - rp x *\<^sub>R axis 2 1)"
  define glm :: "real^2 \<Rightarrow> real^2"
    where "glm = (\<lambda>x. axis 1 1 - ((x-p)$2) *\<^sub>R grm x - rm x *\<^sub>R axis 2 1)"

  \<comment> \<open>STEP 4: \<open>C1field lp glp\<close> and \<open>C1field lm glm\<close>.\<close>
  have lpC1: "C1field lp glp (ball p \<rho>1)"
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>1"
    have drp: "(rp has_derivative (\<lambda>h. inner (grp x) h)) (at x)"
      using rpC1 xin unfolding C1field_def by blast
    have "(lp has_derivative
        (\<lambda>h. h$1 - (inner (grp x) h * ((x-p)$2) + rp x * (h$2)))) (at x)"
      unfolding lp_def
      apply (rule has_derivative_eq_rhs)
       apply (rule derivative_eq_intros drp
                bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
          apply (auto intro!: derivative_eq_intros drp
                bounded_linear.has_derivative[OF bounded_linear_vec_nth])
      done
    moreover have "(\<lambda>h::real^2. h$1 - (inner (grp x) h * ((x-p)$2) + rp x * (h$2)))
                 = (\<lambda>h. inner (glp x) h)"
      unfolding glp_def
      by (rule ext)
         (simp add: inner_diff_left inner_scaleR_left inner_axis' algebra_simps)
    ultimately show "(lp has_derivative (\<lambda>h. inner (glp x) h)) (at x)" by simp
  next
    have crp: "continuous_on (ball p \<rho>1) rp"
      by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
         (use rpC1[unfolded C1field_def] in \<open>blast intro: has_derivative_continuous\<close>)
    have cgrp: "continuous_on (ball p \<rho>1) grp"
      using rpC1 unfolding C1field_def by blast
    show "continuous_on (ball p \<rho>1) glp"
      unfolding glp_def using crp cgrp by (intro continuous_intros) auto
  qed
  have lmC1: "C1field lm glm (ball p \<rho>1)"
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>1"
    have drm: "(rm has_derivative (\<lambda>h. inner (grm x) h)) (at x)"
      using rmC1 xin unfolding C1field_def by blast
    have "(lm has_derivative
        (\<lambda>h. h$1 - (inner (grm x) h * ((x-p)$2) + rm x * (h$2)))) (at x)"
      unfolding lm_def
      apply (rule has_derivative_eq_rhs)
       apply (rule derivative_eq_intros drm
                bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
          apply (auto intro!: derivative_eq_intros drm
                bounded_linear.has_derivative[OF bounded_linear_vec_nth])
      done
    moreover have "(\<lambda>h::real^2. h$1 - (inner (grm x) h * ((x-p)$2) + rm x * (h$2)))
                 = (\<lambda>h. inner (glm x) h)"
      unfolding glm_def
      by (rule ext)
         (simp add: inner_diff_left inner_scaleR_left inner_axis' algebra_simps)
    ultimately show "(lm has_derivative (\<lambda>h. inner (glm x) h)) (at x)" by simp
  next
    have crm: "continuous_on (ball p \<rho>1) rm"
      by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
         (use rmC1[unfolded C1field_def] in \<open>blast intro: has_derivative_continuous\<close>)
    have cgrm: "continuous_on (ball p \<rho>1) grm"
      using rmC1 unfolding C1field_def by blast
    show "continuous_on (ball p \<rho>1) glm"
      unfolding glm_def using crm cgrm by (intro continuous_intros) auto
  qed

  \<comment> \<open>STEP 5: \<open>lp p = 0\<close>, \<open>glp p \<noteq> 0\<close> (and likewise for \<open>lm\<close>).\<close>
  have lpp: "lp p = 0" unfolding lp_def by simp
  have lmp: "lm p = 0" unfolding lm_def by simp
  have glpp: "glp p \<noteq> 0"
  proof -
    have c1: "(glp p) $ 1 = 1"
      unfolding glp_def by (simp add: vector_component_simps axis_def)
    show ?thesis
    proof
      assume "glp p = 0"
      then have "(glp p) $ 1 = 0" by simp
      with c1 show False by simp
    qed
  qed
  have glmp: "glm p \<noteq> 0"
  proof -
    have c1: "(glm p) $ 1 = 1"
      unfolding glm_def by (simp add: vector_component_simps axis_def)
    show ?thesis
    proof
      assume "glm p = 0"
      then have "(glm p) $ 1 = 0" by simp
      with c1 show False by simp
    qed
  qed

  \<comment> \<open>STEP 7 (needed before assembly): \<open>f x = a x * lp x * lm x\<close> on \<open>ball p \<rho>1\<close>.\<close>
  have feq: "\<And>x. x \<in> ball p \<rho>1 \<Longrightarrow> f x = a x * lp x * lm x"
  proof -
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>1"
    then have xin0: "x \<in> ball p \<rho>0" using rle1 by (auto simp: subset_ball)
    have "f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
      using form[OF xin0] .
    also have "\<dots> = a x * ((x-p)$1 - rp x * ((x-p)$2)) * ((x-p)$1 - rm x * ((x-p)$2))"
      using factor[OF xin] .
    also have "\<dots> = a x * lp x * lm x"
      unfolding lp_def lm_def by (simp add: algebra_simps)
    finally show "f x = a x * lp x * lm x" .
  qed

  \<comment> \<open>STEP 6 + 8: apply @{thm level_zero_C1_arc} to each factor and assemble.\<close>
  show ?thesis
  proof (rule level_zero_C1_arc[OF rpos1 lpC1 lpp glpp])
    fix \<gamma>1 :: "real \<Rightarrow> real^2" and a1 b1 \<rho>1' :: real
    assume a1b1: "a1 \<le> b1" and rho1'pos: "0 < \<rho>1'"
      and gam1C1: "\<gamma>1 C1_differentiable_on {a1..b1}"
      and pgam1: "p \<in> \<gamma>1 ` {a1..b1}"
      and cover1: "{x. lp x = 0} \<inter> ball p \<rho>1' \<subseteq> \<gamma>1 ` {a1..b1}"
      and imgsub1: "\<gamma>1 ` {a1..b1} \<subseteq> ball p \<rho>1"
      and inj1: "inj_on \<gamma>1 {a1..b1}"
      and loc1: "\<gamma>1 ` {a1..b1} \<subseteq> {x. lp x = 0}"
    show ?thesis
    proof (rule level_zero_C1_arc[OF rpos1 lmC1 lmp glmp])
      fix \<gamma>2 :: "real \<Rightarrow> real^2" and a2 b2 \<rho>2' :: real
      assume a2b2: "a2 \<le> b2" and rho2'pos: "0 < \<rho>2'"
        and gam2C1: "\<gamma>2 C1_differentiable_on {a2..b2}"
        and pgam2: "p \<in> \<gamma>2 ` {a2..b2}"
        and cover2: "{x. lm x = 0} \<inter> ball p \<rho>2' \<subseteq> \<gamma>2 ` {a2..b2}"
        and imgsub2: "\<gamma>2 ` {a2..b2} \<subseteq> ball p \<rho>1"
        and inj2: "inj_on \<gamma>2 {a2..b2}"
        and loc2: "\<gamma>2 ` {a2..b2} \<subseteq> {x. lm x = 0}"
      define r where "r = min \<rho>a (min \<rho>1 (min \<rho>1' \<rho>2'))"
      have rpos: "0 < r"
        unfolding r_def using \<rho>apos rpos1 rho1'pos rho2'pos by simp
      have cover: "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
      proof
        fix x :: "real^2" assume "x \<in> {x. f x = 0} \<inter> ball p r"
        then have fx0: "f x = 0" and xr: "x \<in> ball p r" by auto
        have xa: "x \<in> ball p \<rho>a" using xr unfolding r_def by (auto simp: subset_ball)
        have x1: "x \<in> ball p \<rho>1" using xr unfolding r_def by (auto simp: subset_ball)
        have x1': "x \<in> ball p \<rho>1'" using xr unfolding r_def by (auto simp: subset_ball)
        have x2': "x \<in> ball p \<rho>2'" using xr unfolding r_def by (auto simp: subset_ball)
        have axnz: "a x \<noteq> 0" using anz[OF xa] .
        have "a x * lp x * lm x = 0" using feq[OF x1] fx0 by simp
        then have "lp x * lm x = 0" using axnz by simp
        then have "lp x = 0 \<or> lm x = 0" by simp
        thus "x \<in> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
        proof
          assume "lp x = 0"
          then have "x \<in> {x. lp x = 0} \<inter> ball p \<rho>1'" using x1' by simp
          then have "x \<in> \<gamma>1 ` {a1..b1}" using cover1 by blast
          thus ?thesis by blast
        next
          assume "lm x = 0"
          then have "x \<in> {x. lm x = 0} \<inter> ball p \<rho>2'" using x2' by simp
          then have "x \<in> \<gamma>2 ` {a2..b2}" using cover2 by blast
          thus ?thesis by blast
        qed
      qed
      have ballsub1: "ball p \<rho>1 \<subseteq> ball p \<rho>0" using rle1 by (rule subset_ball)
      have img1: "\<gamma>1 ` {a1..b1} \<subseteq> ball p \<rho>0" using imgsub1 ballsub1 by (rule order_trans)
      have img2: "\<gamma>2 ` {a2..b2} \<subseteq> ball p \<rho>0" using imgsub2 ballsub1 by (rule order_trans)
      have locf1: "\<gamma>1 ` {a1..b1} \<subseteq> {x. f x = 0}"
      proof
        fix x assume xin: "x \<in> \<gamma>1 ` {a1..b1}"
        hence lpx: "lp x = 0" using loc1 by blast
        from xin have "x \<in> ball p \<rho>1" using imgsub1 by blast
        hence "f x = a x * lp x * lm x" by (rule feq)
        also have "\<dots> = 0" using lpx by simp
        finally show "x \<in> {x. f x = 0}" by simp
      qed
      have locf2: "\<gamma>2 ` {a2..b2} \<subseteq> {x. f x = 0}"
      proof
        fix x assume xin: "x \<in> \<gamma>2 ` {a2..b2}"
        hence lmx: "lm x = 0" using loc2 by blast
        from xin have "x \<in> ball p \<rho>1" using imgsub2 by blast
        hence "f x = a x * lp x * lm x" by (rule feq)
        also have "\<dots> = 0" using lmx by simp
        finally show "x \<in> {x. f x = 0}" by simp
      qed
      show ?thesis
        by (rule that[OF rpos a1b1 a2b2 gam1C1 gam2C1 pgam1 pgam2 cover img1 img2
                         inj1 inj2 locf1 locf2])
    qed
  qed
  qed
qed

lemma C1field_sw:
  fixes h :: "real^2 \<Rightarrow> real" and gh :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes hC1: "C1field h gh (ball p \<rho>0)"
  shows "C1field (\<lambda>x. h (sw x)) (\<lambda>x. sw (gh (sw x))) (ball (sw p) \<rho>0)"
  unfolding C1field_def
proof (intro conjI ballI)
  have hder: "(h has_derivative (\<lambda>k. inner (gh x) k)) (at x)" if "x \<in> ball p \<rho>0" for x :: "real^2"
    using hC1 that unfolding C1field_def by blast
  have gcont: "continuous_on (ball p \<rho>0) gh" using hC1 unfolding C1field_def by blast
  have swmap: "sw x \<in> ball p \<rho>0" if "x \<in> ball (sw p) \<rho>0" for x :: "real^2"
  proof -
    have "sw x \<in> sw ` ball (sw p) \<rho>0" using that by simp
    also have "sw ` ball (sw p) \<rho>0 = ball (sw (sw p)) \<rho>0" by (rule sw_ball)
    also have "sw (sw p) = p" by simp
    finally show ?thesis .
  qed
  fix x :: "real^2" assume x: "x \<in> ball (sw p) \<rho>0"
  have swx: "sw x \<in> ball p \<rho>0" by (rule swmap[OF x])
  have swd: "(sw has_derivative sw) (at x)" by (rule bounded_linear_imp_has_derivative[OF sw_bl])
  have hd: "(h has_derivative (\<lambda>k. inner (gh (sw x)) k)) (at (sw x))" by (rule hder[OF swx])
  have "((\<lambda>z. h (sw z)) has_derivative (\<lambda>z. inner (gh (sw x)) (sw z))) (at x)"
    by (rule has_derivative_compose[OF swd hd])
  moreover have "(\<lambda>z. inner (gh (sw x)) (sw z)) = (\<lambda>k. inner (sw (gh (sw x))) k)"
    by (rule ext) (simp add: sw_inner)
  ultimately show "((\<lambda>x. h (sw x)) has_derivative (\<lambda>k. inner (sw (gh (sw x))) k)) (at x)" by simp
next
  have gcont: "continuous_on (ball p \<rho>0) gh" using hC1 unfolding C1field_def by blast
  have swmap: "sw x \<in> ball p \<rho>0" if "x \<in> ball (sw p) \<rho>0" for x :: "real^2"
  proof -
    have "sw x \<in> sw ` ball (sw p) \<rho>0" using that by simp
    also have "sw ` ball (sw p) \<rho>0 = ball (sw (sw p)) \<rho>0" by (rule sw_ball)
    also have "sw (sw p) = p" by simp
    finally show ?thesis .
  qed
  show "continuous_on (ball (sw p) \<rho>0) (\<lambda>x. sw (gh (sw x)))"
  proof (rule continuous_on_compose2[OF linear_continuous_on[OF sw_bl]
                continuous_on_compose2[OF gcont linear_continuous_on[OF sw_bl]]])
    show "sw ` ball (sw p) \<rho>0 \<subseteq> ball p \<rho>0" using swmap by blast
  qed auto
qed

subsection \<open>MAIN (c-form): same as @{thm saddle_form_two_arcs} with nondegeneracy on \<open>c\<close>\<close>

text \<open>Coordinate-swapped variant of @{thm saddle_form_two_arcs}: the nondegeneracy hypothesis is on
  the \<open>c\<close> coefficient (\<open>c p \<noteq> 0\<close>) rather than on \<open>a\<close>.  Proved by applying @{thm saddle_form_two_arcs}
  to the swapped data \<open>f \<circ> sw\<close>, \<open>a' = c \<circ> sw\<close>, \<open>b' = b \<circ> sw\<close>, \<open>c' = a \<circ> sw\<close> at \<open>sw p\<close> (the quadratic
  form is invariant under simultaneously swapping the two coordinates and the roles of \<open>a\<close>, \<open>c\<close>),
  then transporting the resulting arcs back through the isometry @{const sw}.\<close>

theorem saddle_form_two_arcs_cform:
  fixes f a b c :: "real^2 \<Rightarrow> real" and ga gb gc :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0"
    and aC1: "C1field a ga (ball p \<rho>0)" and bC1: "C1field b gb (ball p \<rho>0)"
    and cC1: "C1field c gc (ball p \<rho>0)"
    and c0: "c p \<noteq> 0" and indef: "(b p)\<^sup>2 - a p * c p > 0"
    and form: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow>
        f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
  obtains \<gamma>1 \<gamma>2 :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real where
      "0 < r" "a1 \<le> b1" "a2 \<le> b2"
      "\<gamma>1 C1_differentiable_on {a1..b1}" "\<gamma>2 C1_differentiable_on {a2..b2}"
      "p \<in> \<gamma>1 ` {a1..b1}" "p \<in> \<gamma>2 ` {a2..b2}"
      "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
      "\<gamma>1 ` {a1..b1} \<subseteq> ball p \<rho>0" "\<gamma>2 ` {a2..b2} \<subseteq> ball p \<rho>0"
      "inj_on \<gamma>1 {a1..b1}" "inj_on \<gamma>2 {a2..b2}"
      "\<gamma>1 ` {a1..b1} \<subseteq> {x. f x = 0}" "\<gamma>2 ` {a2..b2} \<subseteq> {x. f x = 0}"
proof -
  define f' :: "real^2 \<Rightarrow> real" where "f' = (\<lambda>x. f (sw x))"
  define a' :: "real^2 \<Rightarrow> real" where "a' = (\<lambda>x. c (sw x))"
  define b' :: "real^2 \<Rightarrow> real" where "b' = (\<lambda>x. b (sw x))"
  define c' :: "real^2 \<Rightarrow> real" where "c' = (\<lambda>x. a (sw x))"
  define ga' :: "real^2 \<Rightarrow> real^2" where "ga' = (\<lambda>x. sw (gc (sw x)))"
  define gb' :: "real^2 \<Rightarrow> real^2" where "gb' = (\<lambda>x. sw (gb (sw x)))"
  define gc' :: "real^2 \<Rightarrow> real^2" where "gc' = (\<lambda>x. sw (ga (sw x)))"
  define p' :: "real^2" where "p' = sw p"

  \<comment> \<open>Swapped C1 fields, via @{thm C1field_sw}.\<close>
  have a'C1: "C1field a' ga' (ball p' \<rho>0)"
    unfolding a'_def ga'_def p'_def by (rule C1field_sw[OF cC1])
  have b'C1: "C1field b' gb' (ball p' \<rho>0)"
    unfolding b'_def gb'_def p'_def by (rule C1field_sw[OF bC1])
  have c'C1: "C1field c' gc' (ball p' \<rho>0)"
    unfolding c'_def gc'_def p'_def by (rule C1field_sw[OF aC1])

  \<comment> \<open>Swapped nondegeneracy and discriminant.\<close>
  have a'0: "a' p' \<noteq> 0" using c0 unfolding a'_def p'_def by simp
  have indef': "(b' p')\<^sup>2 - a' p' * c' p' > 0"
    using indef unfolding a'_def b'_def c'_def p'_def by (simp add: mult.commute)

  \<comment> \<open>Swapped quadratic form.  For \<open>x \<in> ball p' \<rho>0\<close> we have \<open>sw x \<in> ball p \<rho>0\<close>, and the swap
      exchanges the two coordinate differences: \<open>(sw x - p)$1 = (x - p')$2\<close>, \<open>(sw x - p)$2 = (x - p')$1\<close>.\<close>
  have swmap: "sw x \<in> ball p \<rho>0" if "x \<in> ball p' \<rho>0" for x :: "real^2"
  proof -
    have "sw x \<in> sw ` ball p' \<rho>0" using that by simp
    also have "sw ` ball p' \<rho>0 = ball (sw p') \<rho>0" by (rule sw_ball)
    also have "sw p' = p" by (simp add: p'_def)
    finally show ?thesis .
  qed
  have form': "f' x = a' x * ((x-p')$1)\<^sup>2 + 2 * b' x * ((x-p')$1) * ((x-p')$2)
                    + c' x * ((x-p')$2)\<^sup>2"
    if x: "x \<in> ball p' \<rho>0" for x :: "real^2"
  proof -
    have swx: "sw x \<in> ball p \<rho>0" by (rule swmap[OF x])
    \<comment> \<open>The swap exchanges the two coordinate differences.\<close>
    have d1: "(sw x - p)$1 = (x - p')$2"
      by (simp add: p'_def vector_minus_component)
    have d2: "(sw x - p)$2 = (x - p')$1"
      by (simp add: p'_def vector_minus_component)
    have "f' x = f (sw x)" unfolding f'_def ..
    also have "\<dots> = a (sw x) * ((sw x - p)$1)\<^sup>2
                    + 2 * b (sw x) * ((sw x - p)$1) * ((sw x - p)$2)
                    + c (sw x) * ((sw x - p)$2)\<^sup>2"
      using form[OF swx] .
    also have "\<dots> = c' x * ((x-p')$2)\<^sup>2
                    + 2 * b' x * ((x-p')$2) * ((x-p')$1)
                    + a' x * ((x-p')$1)\<^sup>2"
      unfolding a'_def b'_def c'_def by (simp only: d1 d2)
    also have "\<dots> = a' x * ((x-p')$1)\<^sup>2 + 2 * b' x * ((x-p')$1) * ((x-p')$2)
                    + c' x * ((x-p')$2)\<^sup>2"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed

  \<comment> \<open>Apply the proven theorem to the swapped data, then transport the arcs back through \<open>sw\<close>.\<close>
  show ?thesis
  proof (rule saddle_form_two_arcs[OF \<rho>0 a'C1 b'C1 c'C1 a'0 indef' form'])
    fix \<gamma>1' \<gamma>2' :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real
    assume rpos: "0 < r" and a1b1: "a1 \<le> b1" and a2b2: "a2 \<le> b2"
      and g1C1: "\<gamma>1' C1_differentiable_on {a1..b1}"
      and g2C1: "\<gamma>2' C1_differentiable_on {a2..b2}"
      and pg1: "p' \<in> \<gamma>1' ` {a1..b1}"
      and pg2: "p' \<in> \<gamma>2' ` {a2..b2}"
      and cov: "{x. f' x = 0} \<inter> ball p' r \<subseteq> \<gamma>1' ` {a1..b1} \<union> \<gamma>2' ` {a2..b2}"
      and imgsub1: "\<gamma>1' ` {a1..b1} \<subseteq> ball p' \<rho>0"
      and imgsub2: "\<gamma>2' ` {a2..b2} \<subseteq> ball p' \<rho>0"
      and inj1': "inj_on \<gamma>1' {a1..b1}"
      and inj2': "inj_on \<gamma>2' {a2..b2}"
      and loc1': "\<gamma>1' ` {a1..b1} \<subseteq> {x. f' x = 0}"
      and loc2': "\<gamma>2' ` {a2..b2} \<subseteq> {x. f' x = 0}"
    define \<gamma>1 :: "real \<Rightarrow> real^2" where "\<gamma>1 = sw \<circ> \<gamma>1'"
    define \<gamma>2 :: "real \<Rightarrow> real^2" where "\<gamma>2 = sw \<circ> \<gamma>2'"
    have g1: "\<gamma>1 C1_differentiable_on {a1..b1}" unfolding \<gamma>1_def by (rule C1_sw_comp[OF g1C1])
    have g2: "\<gamma>2 C1_differentiable_on {a2..b2}" unfolding \<gamma>2_def by (rule C1_sw_comp[OF g2C1])
    have pin1: "p \<in> \<gamma>1 ` {a1..b1}"
    proof -
      from pg1 obtain t where t: "t \<in> {a1..b1}" and "p' = \<gamma>1' t" by blast
      hence "p = \<gamma>1 t" unfolding \<gamma>1_def p'_def by (simp add: comp_def) (metis sw_sw)
      thus ?thesis using t by blast
    qed
    have pin2: "p \<in> \<gamma>2 ` {a2..b2}"
    proof -
      from pg2 obtain t where t: "t \<in> {a2..b2}" and "p' = \<gamma>2' t" by blast
      hence "p = \<gamma>2 t" unfolding \<gamma>2_def p'_def by (simp add: comp_def) (metis sw_sw)
      thus ?thesis using t by blast
    qed
    have cover: "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
    proof
      fix x :: "real^2" assume "x \<in> {x. f x = 0} \<inter> ball p r"
      hence fx0: "f x = 0" and xr: "x \<in> ball p r" by auto
      have f'sw: "f' (sw x) = 0" using fx0 unfolding f'_def by simp
      have swxb: "sw x \<in> ball p' r"
        using xr by (simp add: p'_def dist_commute)
      have "sw x \<in> {x. f' x = 0} \<inter> ball p' r" using f'sw swxb by simp
      hence "sw x \<in> \<gamma>1' ` {a1..b1} \<union> \<gamma>2' ` {a2..b2}" using cov by blast
      thus "x \<in> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
      proof
        assume "sw x \<in> \<gamma>1' ` {a1..b1}"
        then obtain t where t: "t \<in> {a1..b1}" and "sw x = \<gamma>1' t" by blast
        hence "x = \<gamma>1 t" unfolding \<gamma>1_def by (simp add: comp_def) (metis sw_sw)
        thus ?thesis using t by blast
      next
        assume "sw x \<in> \<gamma>2' ` {a2..b2}"
        then obtain t where t: "t \<in> {a2..b2}" and "sw x = \<gamma>2' t" by blast
        hence "x = \<gamma>2 t" unfolding \<gamma>2_def by (simp add: comp_def) (metis sw_sw)
        thus ?thesis using t by blast
      qed
    qed
    have img1: "\<gamma>1 ` {a1..b1} \<subseteq> ball p \<rho>0"
    proof -
      have "\<gamma>1 ` {a1..b1} = sw ` (\<gamma>1' ` {a1..b1})" unfolding \<gamma>1_def by (simp add: image_comp)
      also have "\<dots> \<subseteq> sw ` (ball p' \<rho>0)" using imgsub1 by (rule image_mono)
      also have "sw ` (ball p' \<rho>0) = ball (sw p') \<rho>0" by (rule sw_ball)
      also have "sw p' = p" by (simp add: p'_def)
      finally show ?thesis .
    qed
    have img2: "\<gamma>2 ` {a2..b2} \<subseteq> ball p \<rho>0"
    proof -
      have "\<gamma>2 ` {a2..b2} = sw ` (\<gamma>2' ` {a2..b2})" unfolding \<gamma>2_def by (simp add: image_comp)
      also have "\<dots> \<subseteq> sw ` (ball p' \<rho>0)" using imgsub2 by (rule image_mono)
      also have "sw ` (ball p' \<rho>0) = ball (sw p') \<rho>0" by (rule sw_ball)
      also have "sw p' = p" by (simp add: p'_def)
      finally show ?thesis .
    qed
    have injf1: "inj_on \<gamma>1 {a1..b1}"
    proof (rule inj_onI)
      fix s t assume "s\<in>{a1..b1}" "t\<in>{a1..b1}" "\<gamma>1 s = \<gamma>1 t"
      hence "sw (\<gamma>1' s) = sw (\<gamma>1' t)" by (simp add: \<gamma>1_def comp_def)
      hence "\<gamma>1' s = \<gamma>1' t" by (metis sw_sw)
      thus "s = t" using inj1' \<open>s\<in>{a1..b1}\<close> \<open>t\<in>{a1..b1}\<close> by (meson inj_onD)
    qed
    have injf2: "inj_on \<gamma>2 {a2..b2}"
    proof (rule inj_onI)
      fix s t assume "s\<in>{a2..b2}" "t\<in>{a2..b2}" "\<gamma>2 s = \<gamma>2 t"
      hence "sw (\<gamma>2' s) = sw (\<gamma>2' t)" by (simp add: \<gamma>2_def comp_def)
      hence "\<gamma>2' s = \<gamma>2' t" by (metis sw_sw)
      thus "s = t" using inj2' \<open>s\<in>{a2..b2}\<close> \<open>t\<in>{a2..b2}\<close> by (meson inj_onD)
    qed
    have locf1: "\<gamma>1 ` {a1..b1} \<subseteq> {x. f x = 0}"
    proof
      fix x assume "x \<in> \<gamma>1 ` {a1..b1}"
      then obtain t where t: "t\<in>{a1..b1}" and "x = \<gamma>1 t" by blast
      hence xe: "x = sw (\<gamma>1' t)" by (simp add: \<gamma>1_def comp_def)
      have "\<gamma>1' t \<in> \<gamma>1' ` {a1..b1}" using t by (rule imageI)
      hence "f' (\<gamma>1' t) = 0" using loc1' by auto
      thus "x \<in> {x. f x = 0}" using xe by (simp add: f'_def)
    qed
    have locf2: "\<gamma>2 ` {a2..b2} \<subseteq> {x. f x = 0}"
    proof
      fix x assume "x \<in> \<gamma>2 ` {a2..b2}"
      then obtain t where t: "t\<in>{a2..b2}" and "x = \<gamma>2 t" by blast
      hence xe: "x = sw (\<gamma>2' t)" by (simp add: \<gamma>2_def comp_def)
      have "\<gamma>2' t \<in> \<gamma>2' ` {a2..b2}" using t by (rule imageI)
      hence "f' (\<gamma>2' t) = 0" using loc2' by auto
      thus "x \<in> {x. f x = 0}" using xe by (simp add: f'_def)
    qed
    show ?thesis
      by (rule that[OF rpos a1b1 a2b2 g1 g2 pin1 pin2 cover img1 img2
                       injf1 injf2 locf1 locf2])
  qed
qed

theorem saddle_form_two_arcs_purecross:
  fixes f a b c :: "real^2 \<Rightarrow> real" and ga gb gc :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0"
    and aC1: "C1field a ga (ball p \<rho>0)" and bC1: "C1field b gb (ball p \<rho>0)" and cC1: "C1field c gc (ball p \<rho>0)"
    and a0: "a p = 0" and c0: "c p = 0" and b0: "b p \<noteq> 0"
    and form: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
  obtains \<gamma>1 \<gamma>2 :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real where
      "0 < r" "a1 \<le> b1" "a2 \<le> b2" "\<gamma>1 C1_differentiable_on {a1..b1}" "\<gamma>2 C1_differentiable_on {a2..b2}"
      "p \<in> \<gamma>1 ` {a1..b1}" "p \<in> \<gamma>2 ` {a2..b2}"
      "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
      "\<gamma>1 ` {a1..b1} \<subseteq> ball p \<rho>0" "\<gamma>2 ` {a2..b2} \<subseteq> ball p \<rho>0"
      "inj_on \<gamma>1 {a1..b1}" "inj_on \<gamma>2 {a2..b2}"
      "\<gamma>1 ` {a1..b1} \<subseteq> {x. f x = 0}" "\<gamma>2 ` {a2..b2} \<subseteq> {x. f x = 0}"
proof -
  \<comment> \<open>component derivatives and continuity from the C1field hypotheses\<close>
  have da: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (a has_derivative (\<lambda>h. inner (ga x) h)) (at x)"
    and db: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (b has_derivative (\<lambda>h. inner (gb x) h)) (at x)"
    and dc: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (c has_derivative (\<lambda>h. inner (gc x) h)) (at x)"
    using aC1 bC1 cC1 unfolding C1field_def by blast+
  have cga0: "continuous_on (ball p \<rho>0) ga" and cgb0: "continuous_on (ball p \<rho>0) gb"
    and cgc0: "continuous_on (ball p \<rho>0) gc"
    using aC1 bC1 cC1 unfolding C1field_def by blast+
  have ca0: "continuous_on (ball p \<rho>0) a"
    by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
       (use da in \<open>blast intro: has_derivative_continuous\<close>)
  have cb0: "continuous_on (ball p \<rho>0) b"
    by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
       (use db in \<open>blast intro: has_derivative_continuous\<close>)
  have cc0: "continuous_on (ball p \<rho>0) c"
    by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
       (use dc in \<open>blast intro: has_derivative_continuous\<close>)

  define D :: "real^2 \<Rightarrow> real" where "D = (\<lambda>y. (b y)^2 - a y * c y)"
  define gD :: "real^2 \<Rightarrow> real^2"
    where "gD = (\<lambda>y. 2 *\<^sub>R (b y *\<^sub>R gb y) - (c y *\<^sub>R ga y + a y *\<^sub>R gc y))"
  have Dp: "D p > 0" using a0 c0 b0 unfolding D_def by simp

  \<comment> \<open>sign casework: get sg with sg*sg=1 and w p \<noteq> 0\<close>
  define sg :: real where "sg = (if b p > 0 then 1 else -1)"
  have sg1: "sg * sg = 1" unfolding sg_def by simp
  have sqrtDp: "sqrt (D p) = \<bar>b p\<bar>"
  proof -
    have "D p = (b p)^2" using a0 c0 unfolding D_def by simp
    thus ?thesis by (simp add: real_sqrt_abs)
  qed
  have wp_ne: "- b p - sg * sqrt (D p) \<noteq> 0"
  proof (cases "b p > 0")
    case True
    then have "sg = 1" by (simp add: sg_def)
    moreover have "sqrt (D p) = b p" using sqrtDp True by simp
    ultimately show ?thesis using True by simp
  next
    case False
    then have "b p < 0" using b0 by simp
    then have "sg = -1" by (simp add: sg_def)
    moreover have "sqrt (D p) = - b p" using sqrtDp \<open>b p < 0\<close> by simp
    ultimately show ?thesis using \<open>b p < 0\<close> by simp
  qed

  \<comment> \<open>define w and its gradient field\<close>
  define w :: "real^2 \<Rightarrow> real" where "w = (\<lambda>y. - b y - sg *\<^sub>R sqrt (D y))"
  have wp_ne': "w p \<noteq> 0" using wp_ne unfolding w_def by simp

  \<comment> \<open>STEP 1: pick the radius so that D>0 and w\<noteq>0 throughout\<close>
  have cD0: "continuous_on (ball p \<rho>0) D"
    unfolding D_def using ca0 cb0 cc0 by (intro continuous_intros)
  have cw0: "continuous_on (ball p \<rho>0) w"
    unfolding w_def using cb0 cD0
    by (intro continuous_intros continuous_on_real_sqrt) auto
  define U where "U = (ball p \<rho>0 \<inter> D -` {0<..}) \<inter> (ball p \<rho>0 \<inter> w -` (-{0::real}))"
  have opU: "open U"
    unfolding U_def
    by (intro open_Int continuous_open_preimage[OF cD0 open_ball]
              continuous_open_preimage[OF cw0 open_ball]) auto
  have pU: "p \<in> U" unfolding U_def using \<rho>0 wp_ne' Dp by simp
  obtain \<rho>1 where \<rho>1: "\<rho>1 > 0" "ball p \<rho>1 \<subseteq> U"
    using opU pU open_contains_ball by metis
  define \<rho> where "\<rho> = min \<rho>1 \<rho>0"
  have rpos: "0 < \<rho>" using \<rho>1 \<rho>0 unfolding \<rho>_def by simp
  have rle: "\<rho> \<le> \<rho>0" unfolding \<rho>_def by simp
  have ballsub: "ball p \<rho> \<subseteq> ball p \<rho>0" unfolding \<rho>_def by (simp add: subset_ball)
  have Dpos: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> D x > 0"
    and wnz: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> w x \<noteq> 0"
  proof -
    fix x :: "real^2" assume "x \<in> ball p \<rho>"
    then have "x \<in> ball p \<rho>1" unfolding \<rho>_def by auto
    then have "x \<in> U" using \<rho>1 by auto
    thus "D x > 0" "w x \<noteq> 0" unfolding U_def by auto
  qed

  \<comment> \<open>continuity of all pieces on the small ball\<close>
  have ca: "continuous_on (ball p \<rho>) a" using ca0 ballsub by (rule continuous_on_subset)
  have cb: "continuous_on (ball p \<rho>) b" using cb0 ballsub by (rule continuous_on_subset)
  have cc: "continuous_on (ball p \<rho>) c" using cc0 ballsub by (rule continuous_on_subset)
  have cga: "continuous_on (ball p \<rho>) ga" using cga0 ballsub by (rule continuous_on_subset)
  have cgb: "continuous_on (ball p \<rho>) gb" using cgb0 ballsub by (rule continuous_on_subset)
  have cgc: "continuous_on (ball p \<rho>) gc" using cgc0 ballsub by (rule continuous_on_subset)
  have cD: "continuous_on (ball p \<rho>) D"
    unfolding D_def using ca cb cc by (intro continuous_intros)
  have cw: "continuous_on (ball p \<rho>) w" using cw0 ballsub by (rule continuous_on_subset)
  have csqrtD: "continuous_on (ball p \<rho>) (\<lambda>y. sqrt (D y))"
    using cD by (rule continuous_on_real_sqrt)
  have sqrtnz: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> sqrt (D x) \<noteq> 0"
  proof -
    fix x :: "real^2" assume "x \<in> ball p \<rho>"
    then have "D x > 0" by (rule Dpos)
    thus "sqrt (D x) \<noteq> 0" by simp
  qed
  have cgD: "continuous_on (ball p \<rho>) gD"
    unfolding gD_def using ca cb cc cga cgb cgc by (intro continuous_intros)
  have cinv: "continuous_on (ball p \<rho>) (\<lambda>y. inverse (sqrt (D y)) / 2)"
    using csqrtD sqrtnz cD by (intro continuous_intros) auto

  \<comment> \<open>derivative of sqrt(D), valid on the small ball (mirrors factor_indef_C1)\<close>
  have dsqrt: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow>
      ((\<lambda>y. sqrt (D y)) has_derivative (\<lambda>h. inner ((inverse (sqrt (D x)) / 2) *\<^sub>R gD x) h)) (at x)"
  proof -
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    then have xin0: "x \<in> ball p \<rho>0" using ballsub by blast
    have dD: "(D has_derivative (\<lambda>h. inner (gD x) h)) (at x)"
      unfolding D_def gD_def
      apply (rule has_derivative_eq_rhs)
       apply (rule derivative_intros da[OF xin0] db[OF xin0] dc[OF xin0])+
      apply (rule ext)
      apply (simp add: inner_diff_left inner_add_left inner_scaleR_left power2_eq_square algebra_simps)
      done
    show "((\<lambda>y. sqrt (D y)) has_derivative (\<lambda>h. inner ((inverse (sqrt (D x)) / 2) *\<^sub>R gD x) h)) (at x)"
      apply (rule has_derivative_eq_rhs)
       apply (rule has_derivative_real_sqrt[OF Dpos[OF xin] dD])
      apply (rule ext)
      apply (simp add: inner_scaleR_left)
      done
  qed

  \<comment> \<open>gradient field of w = -b - sg*sqrt(D)\<close>
  define gw :: "real^2 \<Rightarrow> real^2"
    where "gw = (\<lambda>y. - gb y - sg *\<^sub>R ((inverse (sqrt (D y)) / 2) *\<^sub>R gD y))"
  have dw: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> (w has_derivative (\<lambda>h. inner (gw x) h)) (at x)"
  proof -
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    then have xin0: "x \<in> ball p \<rho>0" using ballsub by blast
    show "(w has_derivative (\<lambda>h. inner (gw x) h)) (at x)"
      unfolding w_def gw_def
      apply (rule has_derivative_eq_rhs)
       apply (rule has_derivative_diff has_derivative_minus db[OF xin0]
                   has_derivative_scaleR_right dsqrt[OF xin])+
      apply (rule ext)
      apply (simp add: inner_diff_left inner_minus_left inner_scaleR_left)
      done
  qed
  have cgw: "continuous_on (ball p \<rho>) gw"
    unfolding gw_def using cgb cinv cgD
    by (intro continuous_on_diff continuous_on_minus continuous_on_scaleR continuous_on_const)

  \<comment> \<open>r1 = c / w and its gradient (mirror grp in factor_indef_C1: num=c, den=w)\<close>
  define r1 :: "real^2 \<Rightarrow> real" where "r1 = (\<lambda>y. c y / w y)"
  define gr1 :: "real^2 \<Rightarrow> real^2"
    where "gr1 = (\<lambda>y. (w y / (w y * w y)) *\<^sub>R gc y - (c y / (w y * w y)) *\<^sub>R gw y)"
  have r1C1: "C1field r1 gr1 (ball p \<rho>)"
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    have dq: "(r1 has_derivative
        (\<lambda>h. (inner (gc x) h * w x - c x * inner (gw x) h) / (w x * w x))) (at x)"
      unfolding r1_def by (rule has_derivative_divide'[OF dc[OF ballsub[THEN subsetD, OF xin]] dw[OF xin] wnz[OF xin]])
    have match: "(\<lambda>h. (inner (gc x) h * w x - c x * inner (gw x) h) / (w x * w x))
               = (\<lambda>h. inner (gr1 x) h)"
      unfolding gr1_def
      by (rule ext) (simp add: inner_diff_left inner_scaleR_left field_simps)
    show "(r1 has_derivative (\<lambda>h. inner (gr1 x) h)) (at x)" using dq unfolding match .
  next
    have cden: "continuous_on (ball p \<rho>) (\<lambda>y. w y / (w y * w y))"
      using cw wnz by (intro continuous_intros) auto
    have cnum: "continuous_on (ball p \<rho>) (\<lambda>y. c y / (w y * w y))"
      using cc cw wnz by (intro continuous_intros) auto
    show "continuous_on (ball p \<rho>) gr1"
      unfolding gr1_def using cden cgc cnum cgw
      by (intro continuous_on_diff continuous_on_scaleR)
  qed
  have r1p: "r1 p = 0"
    unfolding r1_def using c0 wp_ne' by simp

  \<comment> \<open>FACTOR 1: l1 = (x-p)$1 - r1 x * (x-p)$2  (mirrors lp in saddle_form_two_arcs)\<close>
  define l1 :: "real^2 \<Rightarrow> real" where "l1 = (\<lambda>x. (x-p)$1 - r1 x * ((x-p)$2))"
  define gl1 :: "real^2 \<Rightarrow> real^2"
    where "gl1 = (\<lambda>x. axis 1 1 - ((x-p)$2) *\<^sub>R gr1 x - r1 x *\<^sub>R axis 2 1)"
  have l1C1: "C1field l1 gl1 (ball p \<rho>)"
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    have dr1: "(r1 has_derivative (\<lambda>h. inner (gr1 x) h)) (at x)"
      using r1C1 xin unfolding C1field_def by blast
    have "(l1 has_derivative
        (\<lambda>h. h$1 - (inner (gr1 x) h * ((x-p)$2) + r1 x * (h$2)))) (at x)"
      unfolding l1_def
      apply (rule has_derivative_eq_rhs)
       apply (rule derivative_eq_intros dr1
                bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
          apply (auto intro!: derivative_eq_intros dr1
                bounded_linear.has_derivative[OF bounded_linear_vec_nth])
      done
    moreover have "(\<lambda>h::real^2. h$1 - (inner (gr1 x) h * ((x-p)$2) + r1 x * (h$2)))
                 = (\<lambda>h. inner (gl1 x) h)"
      unfolding gl1_def
      by (rule ext)
         (simp add: inner_diff_left inner_scaleR_left inner_axis' algebra_simps)
    ultimately show "(l1 has_derivative (\<lambda>h. inner (gl1 x) h)) (at x)" by simp
  next
    have cr1: "continuous_on (ball p \<rho>) r1"
      by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
         (use r1C1[unfolded C1field_def] in \<open>blast intro: has_derivative_continuous\<close>)
    have cgr1: "continuous_on (ball p \<rho>) gr1"
      using r1C1 unfolding C1field_def by blast
    show "continuous_on (ball p \<rho>) gl1"
      unfolding gl1_def using cr1 cgr1 by (intro continuous_intros) auto
  qed
  have l1p: "l1 p = 0" unfolding l1_def by simp
  have gl1p1: "(gl1 p) $ 1 = 1"
    unfolding gl1_def by (simp add: vector_component_simps axis_def)
  have gl1p: "gl1 p \<noteq> 0"
  proof
    assume "gl1 p = 0"
    then have "(gl1 p) $ 1 = 0" by simp
    with gl1p1 show False by simp
  qed

  \<comment> \<open>FACTOR 2: l2 = a x * (x-p)$1 + (a x * r1 x + 2 * b x) * (x-p)$2\<close>
  define m :: "real^2 \<Rightarrow> real" where "m = (\<lambda>x. a x * r1 x + 2 * b x)"
  define gm :: "real^2 \<Rightarrow> real^2"
    where "gm = (\<lambda>x. r1 x *\<^sub>R ga x + a x *\<^sub>R gr1 x + 2 *\<^sub>R gb x)"
  define l2 :: "real^2 \<Rightarrow> real" where "l2 = (\<lambda>x. a x * ((x-p)$1) + m x * ((x-p)$2))"
  define gl2 :: "real^2 \<Rightarrow> real^2"
    where "gl2 = (\<lambda>x. ((x-p)$1) *\<^sub>R ga x + a x *\<^sub>R axis 1 1
                      + ((x-p)$2) *\<^sub>R gm x + m x *\<^sub>R axis 2 1)"
  have dm: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> (m has_derivative (\<lambda>h. inner (gm x) h)) (at x)"
  proof -
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    then have xin0: "x \<in> ball p \<rho>0" using ballsub by blast
    have dr1: "(r1 has_derivative (\<lambda>h. inner (gr1 x) h)) (at x)"
      using r1C1 xin unfolding C1field_def by blast
    show "(m has_derivative (\<lambda>h. inner (gm x) h)) (at x)"
      unfolding m_def gm_def
      apply (rule has_derivative_eq_rhs)
       apply (rule has_derivative_add has_derivative_mult da[OF xin0] dr1
                   has_derivative_scaleR_right db[OF xin0] has_derivative_const)+
      apply (rule ext)
      apply (simp add: inner_add_left inner_scaleR_left algebra_simps)
      done
  qed
  have cm: "continuous_on (ball p \<rho>) m"
    by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
       (use dm in \<open>blast intro: has_derivative_continuous\<close>)
  have cgm: "continuous_on (ball p \<rho>) gm"
  proof -
    have cr1: "continuous_on (ball p \<rho>) r1"
      by (rule continuous_on_eq_continuous_at[THEN iffD2, OF open_ball, rule_format])
         (use r1C1[unfolded C1field_def] in \<open>blast intro: has_derivative_continuous\<close>)
    have cgr1: "continuous_on (ball p \<rho>) gr1" using r1C1 unfolding C1field_def by blast
    show ?thesis
      unfolding gm_def using cr1 cga ca cgr1 cgb
      by (intro continuous_on_add continuous_on_scaleR continuous_on_const)
  qed
  have l2C1: "C1field l2 gl2 (ball p \<rho>)"
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    then have xin0: "x \<in> ball p \<rho>0" using ballsub by blast
    have "(l2 has_derivative
        (\<lambda>h. (inner (ga x) h * ((x-p)$1) + a x * (h$1))
           + (inner (gm x) h * ((x-p)$2) + m x * (h$2)))) (at x)"
      unfolding l2_def
      apply (rule has_derivative_eq_rhs)
       apply (rule derivative_eq_intros da[OF xin0] dm[OF xin]
                bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
            apply (auto intro!: derivative_eq_intros da[OF xin0] dm[OF xin]
                bounded_linear.has_derivative[OF bounded_linear_vec_nth])
      done
    moreover have "(\<lambda>h::real^2. (inner (ga x) h * ((x-p)$1) + a x * (h$1))
           + (inner (gm x) h * ((x-p)$2) + m x * (h$2)))
                 = (\<lambda>h. inner (gl2 x) h)"
      unfolding gl2_def
      by (rule ext)
         (simp add: inner_add_left inner_scaleR_left inner_axis' algebra_simps)
    ultimately show "(l2 has_derivative (\<lambda>h. inner (gl2 x) h)) (at x)" by simp
  next
    show "continuous_on (ball p \<rho>) gl2"
      unfolding gl2_def using ca cga cm cgm
      by (intro continuous_intros) auto
  qed
  have l2p: "l2 p = 0" unfolding l2_def by simp
  have gl2p2: "(gl2 p) $ 2 = 2 * b p"
  proof -
    have "m p = 2 * b p" unfolding m_def using a0 by simp
    thus ?thesis
      unfolding gl2_def by (simp add: vector_component_simps axis_def)
  qed
  have gl2p: "gl2 p \<noteq> 0"
  proof
    assume "gl2 p = 0"
    then have "(gl2 p) $ 2 = 0" by simp
    with gl2p2 b0 show False by simp
  qed

  \<comment> \<open>the product factorization a Y1^2 + 2 b Y1 Y2 + c Y2^2 = (Y1 - r1 Y2)(a Y1 + (a r1 + 2 b) Y2)\<close>
  have factor: "\<And>x Y1 Y2. x \<in> ball p \<rho> \<Longrightarrow>
      a x * Y1\<^sup>2 + 2 * b x * Y1 * Y2 + c x * Y2\<^sup>2
        = (Y1 - r1 x * Y2) * (a x * Y1 + (a x * r1 x + 2 * b x) * Y2)"
  proof -
    fix x :: "real^2" and Y1 Y2 :: real assume xin: "x \<in> ball p \<rho>"
    define s where "s = sqrt (D x)"
    have ssx: "s * s = (b x)*(b x) - a x * c x"
      using Dpos[OF xin] unfolding s_def D_def
      by (simp add: power2_eq_square[symmetric])
    have wxnz: "w x \<noteq> 0" by (rule wnz[OF xin])
    have wxval: "w x = - b x - sg * s" unfolding w_def s_def by simp
    \<comment> \<open>r1 x = c x / w x is a root of a*l^2 + 2b*l + c\<close>
    have root: "a x * (r1 x)^2 + 2 * b x * (r1 x) + c x = 0"
    proof -
      have key: "a x * c x + 2 * b x * w x + w x * w x = 0"
        unfolding wxval using ssx sg1 by (simp add: algebra_simps power2_eq_square)
      have "a x * (c x / w x)^2 + 2 * b x * (c x / w x) + c x
          = (a x * c x * c x + 2 * b x * c x * w x + c x * (w x * w x)) / (w x * w x)"
        using wxnz by (simp add: power2_eq_square field_simps)
      also have "\<dots> = (c x * (a x * c x + 2 * b x * w x + w x * w x)) / (w x * w x)"
        by (simp add: algebra_simps)
      also have "\<dots> = 0" using key by simp
      finally show ?thesis unfolding r1_def .
    qed
    have "(Y1 - r1 x * Y2) * (a x * Y1 + (a x * r1 x + 2 * b x) * Y2)
        = a x * Y1^2 + 2 * b x * Y1 * Y2 - (a x * (r1 x)^2 + 2 * b x * (r1 x)) * Y2^2"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = a x * Y1^2 + 2 * b x * Y1 * Y2 + c x * Y2^2"
    proof -
      have "a x * (r1 x)^2 + 2 * b x * (r1 x) = - c x" using root by algebra
      hence "(a x * (r1 x)^2 + 2 * b x * (r1 x)) * Y2^2 = (- c x) * Y2^2" by simp
      thus ?thesis by simp
    qed
    finally show "a x * Y1\<^sup>2 + 2 * b x * Y1 * Y2 + c x * Y2\<^sup>2
        = (Y1 - r1 x * Y2) * (a x * Y1 + (a x * r1 x + 2 * b x) * Y2)" by simp
  qed

  \<comment> \<open>f x = l1 x * l2 x on ball p \<rho>\<close>
  have feq: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow> f x = l1 x * l2 x"
  proof -
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>"
    then have xin0: "x \<in> ball p \<rho>0" using rle by (auto simp: subset_ball)
    have "f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
      using form[OF xin0] .
    also have "\<dots> = ((x-p)$1 - r1 x * ((x-p)$2))
                    * (a x * ((x-p)$1) + (a x * r1 x + 2 * b x) * ((x-p)$2))"
      using factor[OF xin] .
    also have "\<dots> = l1 x * l2 x"
      unfolding l1_def l2_def m_def by (simp add: algebra_simps)
    finally show "f x = l1 x * l2 x" .
  qed

  \<comment> \<open>assembly: apply level_zero_C1_arc to each factor (mirrors saddle_form_two_arcs)\<close>
  show ?thesis
  proof (rule level_zero_C1_arc[OF rpos l1C1 l1p gl1p])
    fix \<gamma>1 :: "real \<Rightarrow> real^2" and a1 b1 \<rho>1' :: real
    assume a1b1: "a1 \<le> b1" and rho1'pos: "0 < \<rho>1'"
      and gam1C1: "\<gamma>1 C1_differentiable_on {a1..b1}"
      and pgam1: "p \<in> \<gamma>1 ` {a1..b1}"
      and cover1: "{x. l1 x = 0} \<inter> ball p \<rho>1' \<subseteq> \<gamma>1 ` {a1..b1}"
      and imgsub1: "\<gamma>1 ` {a1..b1} \<subseteq> ball p \<rho>"
      and inj1: "inj_on \<gamma>1 {a1..b1}"
      and loc1: "\<gamma>1 ` {a1..b1} \<subseteq> {x. l1 x = 0}"
    show ?thesis
    proof (rule level_zero_C1_arc[OF rpos l2C1 l2p gl2p])
      fix \<gamma>2 :: "real \<Rightarrow> real^2" and a2 b2 \<rho>2' :: real
      assume a2b2: "a2 \<le> b2" and rho2'pos: "0 < \<rho>2'"
        and gam2C1: "\<gamma>2 C1_differentiable_on {a2..b2}"
        and pgam2: "p \<in> \<gamma>2 ` {a2..b2}"
        and cover2: "{x. l2 x = 0} \<inter> ball p \<rho>2' \<subseteq> \<gamma>2 ` {a2..b2}"
        and imgsub2: "\<gamma>2 ` {a2..b2} \<subseteq> ball p \<rho>"
        and inj2: "inj_on \<gamma>2 {a2..b2}"
        and loc2: "\<gamma>2 ` {a2..b2} \<subseteq> {x. l2 x = 0}"
      define r where "r = min \<rho> (min \<rho>1' \<rho>2')"
      have rpos': "0 < r"
        unfolding r_def using rpos rho1'pos rho2'pos by simp
      have cover: "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
      proof
        fix x :: "real^2" assume "x \<in> {x. f x = 0} \<inter> ball p r"
        then have fx0: "f x = 0" and xr: "x \<in> ball p r" by auto
        have x1: "x \<in> ball p \<rho>" using xr unfolding r_def by (auto simp: subset_ball)
        have x1': "x \<in> ball p \<rho>1'" using xr unfolding r_def by (auto simp: subset_ball)
        have x2': "x \<in> ball p \<rho>2'" using xr unfolding r_def by (auto simp: subset_ball)
        have "l1 x * l2 x = 0" using feq[OF x1] fx0 by simp
        then have "l1 x = 0 \<or> l2 x = 0" by simp
        thus "x \<in> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
        proof
          assume "l1 x = 0"
          then have "x \<in> {x. l1 x = 0} \<inter> ball p \<rho>1'" using x1' by simp
          then have "x \<in> \<gamma>1 ` {a1..b1}" using cover1 by blast
          thus ?thesis by blast
        next
          assume "l2 x = 0"
          then have "x \<in> {x. l2 x = 0} \<inter> ball p \<rho>2'" using x2' by simp
          then have "x \<in> \<gamma>2 ` {a2..b2}" using cover2 by blast
          thus ?thesis by blast
        qed
      qed
      have img1: "\<gamma>1 ` {a1..b1} \<subseteq> ball p \<rho>0" using imgsub1 ballsub by (rule order_trans)
      have img2: "\<gamma>2 ` {a2..b2} \<subseteq> ball p \<rho>0" using imgsub2 ballsub by (rule order_trans)
      have locf1: "\<gamma>1 ` {a1..b1} \<subseteq> {x. f x = 0}"
      proof
        fix x assume xin: "x \<in> \<gamma>1 ` {a1..b1}"
        hence l1x: "l1 x = 0" using loc1 by blast
        from xin have "x \<in> ball p \<rho>" using imgsub1 by blast
        hence "f x = l1 x * l2 x" by (rule feq)
        also have "\<dots> = 0" using l1x by simp
        finally show "x \<in> {x. f x = 0}" by simp
      qed
      have locf2: "\<gamma>2 ` {a2..b2} \<subseteq> {x. f x = 0}"
      proof
        fix x assume xin: "x \<in> \<gamma>2 ` {a2..b2}"
        hence l2x: "l2 x = 0" using loc2 by blast
        from xin have "x \<in> ball p \<rho>" using imgsub2 by blast
        hence "f x = l1 x * l2 x" by (rule feq)
        also have "\<dots> = 0" using l2x by simp
        finally show "x \<in> {x. f x = 0}" by simp
      qed
      show ?thesis
        by (rule that[OF rpos' a1b1 a2b2 gam1C1 gam2C1 pgam1 pgam2 cover img1 img2
                         inj1 inj2 locf1 locf2])
    qed
  qed
qed

end
