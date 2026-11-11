theory Morse_base
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
  sorry

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
