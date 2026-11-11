theory main_scratch
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

lemma level_zero_C1_arc:
  fixes lf :: "real^2 \<Rightarrow> real" and glf :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0" and lC1: "C1field lf glf (ball p \<rho>0)"
    and lp: "lf p = 0" and reg: "glf p \<noteq> 0"
  obtains \<gamma> :: "real \<Rightarrow> real^2" and a b \<rho> :: real where "a \<le> b" "0 < \<rho>"
      "\<gamma> C1_differentiable_on {a..b}" "p \<in> \<gamma> ` {a..b}"
      "{x. lf x = 0} \<inter> ball p \<rho> \<subseteq> \<gamma> ` {a..b}"
  sorry

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
    show ?thesis
    proof (rule level_zero_C1_arc[OF rpos1 lmC1 lmp glmp])
      fix \<gamma>2 :: "real \<Rightarrow> real^2" and a2 b2 \<rho>2' :: real
      assume a2b2: "a2 \<le> b2" and rho2'pos: "0 < \<rho>2'"
        and gam2C1: "\<gamma>2 C1_differentiable_on {a2..b2}"
        and pgam2: "p \<in> \<gamma>2 ` {a2..b2}"
        and cover2: "{x. lm x = 0} \<inter> ball p \<rho>2' \<subseteq> \<gamma>2 ` {a2..b2}"
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
      show ?thesis
        by (rule that[OF rpos a1b1 a2b2 gam1C1 gam2C1 pgam1 pgam2 cover])
    qed
  qed
  qed
qed

subsection \<open>STUB 3 (Hadamard, foundational): C3 + first-order-flat = indefinite C1 form\<close>

text \<open>Hadamard's lemma (2nd order, with C1 remainder coefficients): a \<open>C3\<close> function vanishing
  to first order at \<open>p\<close> equals a quadratic form with C1 coefficients whose values at \<open>p\<close> are
  half the second partials.  No multivariate Taylor in HOL-Analysis \<Rightarrow> build from the 1D
  fundamental theorem of calculus along the segments \<open>t \<mapsto> p + t\<cdot>(x-p)\<close> (Leibniz/parametric
  integral for the C1 dependence).  The smoothness hypothesis \<open>SMOOTH3 f (ball p \<rho>0)\<close> below is a
  PLACEHOLDER; the agent should replace it with the exact provable HOL-Analysis predicate and
  report it (for \<open>crossTheta\<close> any reasonable C-inf predicate holds).  AGENT TARGET.\<close>

lemma hadamard2:
  fixes f :: "real^2 \<Rightarrow> real" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0"
    \<comment> \<open>SMOOTH3 placeholder + \<open>f p = 0\<close> + \<open>Df p = 0\<close> to be made precise by the agent\<close>
  shows "True"
  by simp

end
