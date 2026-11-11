section \<open>The first two derivatives of the dipole gain\<close>

theory Dipole_Gain_Derivatives
  imports
    Dipole_Pattern
begin

subsection \<open>The zeros of the first derivative\<close>

definition gsincd :: "real \<Rightarrow> real" where
  "gsincd x = (x * cos x - sin x) / x^2"

lemma gsinc_has_real_derivative:
  fixes x :: real
  assumes x0: "x \<noteq> 0"
  shows "(gsinc has_real_derivative gsincd x) (at x)"
proof -
  have raw: "((\<lambda>y. sin y / y) has_real_derivative (cos x * x - sin x * 1) / (x * x)) (at x)"
    by (rule DERIV_divide[OF DERIV_sin DERIV_ident x0])
  have eq: "(cos x * x - sin x * 1) / (x * x) = gsincd x"
    by (simp add: gsincd_def power2_eq_square mult.commute)
  have step: "((\<lambda>y. sin y / y) has_real_derivative gsincd x) (at x)"
    using raw unfolding eq .
  show ?thesis
  proof (rule has_field_derivative_transform_within_open[OF step, where S = "- {0::real}"])
    show "open (- {0::real})" by (rule open_Compl) (rule closed_singleton)
    show "x \<in> - {0::real}" using x0 by simp
    show "\<And>y. y \<in> - {0::real} \<Longrightarrow> sin y / y = gsinc y"
      by (simp add: gsinc_def)
  qed
qed

lemma sin_less_self:
  fixes x :: real
  assumes x0: "0 < x" and xpi: "x \<le> pi"
  shows "sin x < x"
proof -
  have ex: "\<exists>z::real. 0 < z \<and> z < x \<and> sin x - sin 0 = (x - 0) * cos z"
    by (rule MVT2[OF x0]) (rule DERIV_sin)
  then obtain z :: real where z0: "0 < z" and zx: "z < x"
    and eq: "sin x - sin 0 = (x - 0) * cos z"
    by (elim exE conjE)
  have zpi: "z \<le> pi" using zx xpi by linarith
  have "cos z < cos 0"
    by (rule cos_monotone_0_pi[OF order.refl z0 zpi])
  hence cz1: "cos z < 1" by simp
  have sx: "sin x = x * cos z" using eq by simp
  have "x * cos z < x * 1" by (rule mult_strict_left_mono[OF cz1 x0])
  with sx show ?thesis by simp
qed

lemma gsinc_pos:
  fixes x :: real
  assumes x0: "0 < x" and xpi: "x < pi"
  shows "0 < gsinc x"
proof -
  have "0 < sin x / x" by (rule divide_pos_pos[OF sin_gt_zero[OF x0 xpi] x0])
  with x0 show ?thesis by (simp add: gsinc_def)
qed

lemma cot_minus_inverse_has_real_derivative:
  fixes x :: real
  assumes x0: "0 < x" and xpi: "x < pi"
  shows "((\<lambda>y. cos y / sin y - 1 / y) has_real_derivative
           inverse (x^2) - inverse ((sin x)^2)) (at x)"
proof -
  have sx: "sin x \<noteq> 0" using sin_gt_zero[OF x0 xpi] by simp
  have xne: "x \<noteq> 0" using x0 by simp
  have d1raw: "((\<lambda>y. cos y / sin y) has_real_derivative
                 (- sin x * sin x - cos x * cos x) / (sin x * sin x)) (at x)"
    by (rule DERIV_divide[OF DERIV_cos DERIV_sin sx])
  have num: "- sin x * sin x - cos x * cos x = - 1"
    using sin_cos_squared_add[of x, unfolded power2_eq_square] by linarith
  have e1: "(- sin x * sin x - cos x * cos x) / (sin x * sin x) = - inverse ((sin x)^2)"
    unfolding num by (simp add: power2_eq_square inverse_eq_divide)
  have d1: "((\<lambda>y. cos y / sin y) has_real_derivative - inverse ((sin x)^2)) (at x)"
    using d1raw unfolding e1 .
  have d2raw: "((\<lambda>y. 1 / y) has_real_derivative (0 * x - 1 * 1) / (x * x)) (at x)"
    by (rule DERIV_divide[OF DERIV_const DERIV_ident xne])
  have e2: "(0 * x - 1 * 1) / (x * x) = - inverse (x^2)"
    by (simp add: power2_eq_square inverse_eq_divide)
  have d2: "((\<lambda>y. 1 / y) has_real_derivative - inverse (x^2)) (at x)"
    using d2raw unfolding e2 .
  have dd: "((\<lambda>y. cos y / sin y - 1 / y) has_real_derivative
              - inverse ((sin x)^2) - (- inverse (x^2))) (at x)"
    by (rule DERIV_diff[OF d1 d2])
  have e3: "- inverse ((sin x)^2) - (- inverse (x^2)) = inverse (x^2) - inverse ((sin x)^2)"
    by simp
  show ?thesis using dd unfolding e3 .
qed

lemma cot_minus_inverse_deriv_neg:
  fixes x :: real
  assumes x0: "0 < x" and xpi: "x < pi"
  shows "inverse (x^2) - inverse ((sin x)^2) < 0"
proof -
  have spos: "0 < sin x" by (rule sin_gt_zero[OF x0 xpi])
  have slt: "sin x < x" by (rule sin_less_self[OF x0 less_imp_le[OF xpi]])
  have p2: "(sin x)^2 < x^2"
    using power_strict_mono[OF slt less_imp_le[OF spos], of 2] by simp
  have "inverse (x^2) < inverse ((sin x)^2)"
    by (rule less_imp_inverse_less[OF p2 zero_less_power[OF spos]])
  thus ?thesis by linarith
qed

lemma gsinc_wronskian_pos:
  fixes a b :: real
  assumes a0: "0 < a" and ab: "a < b" and bpi: "b < pi"
  shows "0 < gsincd a * gsinc b - gsinc a * gsincd b"
proof -
  have api: "a < pi" using ab bpi by linarith
  have b0: "0 < b" using a0 ab by linarith
  define h :: "real \<Rightarrow> real" where "h = (\<lambda>y. cos y / sin y - 1 / y)"
  have mono: "h b < h a"
  proof (rule DERIV_neg_imp_decreasing[OF ab])
    fix x :: real assume ax: "a \<le> x" and xb: "x \<le> b"
    have x0: "0 < x" using a0 ax by linarith
    have xpi: "x < pi" using xb bpi by linarith
    show "\<exists>y. DERIV h x :> y \<and> y < 0"
    proof (rule exI[of _ "inverse (x^2) - inverse ((sin x)^2)"], rule conjI)
      show "DERIV h x :> inverse (x^2) - inverse ((sin x)^2)"
        unfolding h_def by (rule cot_minus_inverse_has_real_derivative[OF x0 xpi])
      show "inverse (x^2) - inverse ((sin x)^2) < 0"
        by (rule cot_minus_inverse_deriv_neg[OF x0 xpi])
    qed
  qed
  have fac: "gsincd x = gsinc x * h x" if x0: "0 < x" and xpi: "x < pi" for x :: real
  proof -
    have sx: "sin x \<noteq> 0" using sin_gt_zero[OF x0 xpi] by simp
    have xne: "x \<noteq> 0" using x0 by simp
    show ?thesis
      using sx xne unfolding gsincd_def gsinc_def h_def
      by (simp add: power2_eq_square divide_simps algebra_simps)
  qed
  have ga: "0 < gsinc a" by (rule gsinc_pos[OF a0 api])
  have gb: "0 < gsinc b" by (rule gsinc_pos[OF b0 bpi])
  have key: "gsincd a * gsinc b - gsinc a * gsincd b = gsinc a * gsinc b * (h a - h b)"
    unfolding fac[OF a0 api] fac[OF b0 bpi] by (simp add: algebra_simps)
  have hpos: "0 < h a - h b" using mono by linarith
  have "0 < gsinc a * gsinc b * (h a - h b)"
    by (rule mult_pos_pos[OF mult_pos_pos[OF ga gb] hpos])
  with key show ?thesis by simp
qed

lemma cos_strict_bounds_of_sin_nonzero:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0"
  shows "cos \<theta> < 1" and "- 1 < cos \<theta>"
proof -
  have ne1: "cos \<theta> \<noteq> 1"
  proof
    assume "cos \<theta> = 1"
    hence "(sin \<theta>)^2 = 0" by (simp add: sin_squared_eq)
    hence "sin \<theta> = 0" by (simp add: power2_eq_square)
    with s0 show False by simp
  qed
  have nem1: "cos \<theta> \<noteq> - 1"
  proof
    assume "cos \<theta> = - 1"
    hence "(sin \<theta>)^2 = 0" by (simp add: sin_squared_eq)
    hence "sin \<theta> = 0" by (simp add: power2_eq_square)
    with s0 show False by simp
  qed
  show "cos \<theta> < 1" using cos_le_one[of \<theta>] ne1 by linarith
  show "- 1 < cos \<theta>" using cos_ge_minus_one[of \<theta>] nem1 by linarith
qed

lemma gdip_has_real_derivative:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0"
  shows "(gdip has_real_derivative
           pi^2/4 * ((pi/2) * sin \<theta>) *
           (gsincd ((pi/2)*(1 - cos \<theta>)) * gsinc ((pi/2)*(1 + cos \<theta>))
            - gsinc ((pi/2)*(1 - cos \<theta>)) * gsincd ((pi/2)*(1 + cos \<theta>)))) (at \<theta>)"
proof -
  have c1: "cos \<theta> < 1" and c2: "- 1 < cos \<theta>"
    by (rule cos_strict_bounds_of_sin_nonzero[OF s0])+
  have um0: "(pi/2)*(1 - cos \<theta>) \<noteq> 0"
  proof -
    have "1 - cos \<theta> \<noteq> 0" using c1 by linarith
    thus ?thesis by simp
  qed
  have up0: "(pi/2)*(1 + cos \<theta>) \<noteq> 0"
  proof -
    have "1 + cos \<theta> \<noteq> 0" using c2 by linarith
    thus ?thesis by simp
  qed
  have dm: "((\<lambda>t. (pi/2)*(1 - cos t)) has_real_derivative (pi/2) * sin \<theta>) (at \<theta>)"
    by (auto intro!: derivative_eq_intros)
  have dp: "((\<lambda>t. (pi/2)*(1 + cos t)) has_real_derivative - ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (auto intro!: derivative_eq_intros)
  have cA: "((\<lambda>t. gsinc ((pi/2)*(1 - cos t))) has_real_derivative
              gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF gsinc_has_real_derivative[OF um0] dm])
  have cB: "((\<lambda>t. gsinc ((pi/2)*(1 + cos t))) has_real_derivative
              gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF gsinc_has_real_derivative[OF up0] dp])
  have prodd: "((\<lambda>t. gsinc ((pi/2)*(1 - cos t)) * gsinc ((pi/2)*(1 + cos t)))
                 has_real_derivative
                 gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 + cos \<theta>))
                 + gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 - cos \<theta>)))
               (at \<theta>)"
    by (rule DERIV_mult[OF cA cB])
  have cm: "((\<lambda>t. (pi^2/4) * (gsinc ((pi/2)*(1 - cos t)) * gsinc ((pi/2)*(1 + cos t))))
              has_real_derivative
              (pi^2/4) * (gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 + cos \<theta>))
                          + gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 - cos \<theta>))))
            (at \<theta>)"
    by (rule DERIV_cmult[OF prodd])
  have geq: "gdip = (\<lambda>t. (pi^2/4) * (gsinc ((pi/2)*(1 - cos t)) * gsinc ((pi/2)*(1 + cos t))))"
    by (rule ext) (simp add: gdip_def)
  have raw: "(gdip has_real_derivative
               (pi^2/4) * (gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 + cos \<theta>))
                           + gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 - cos \<theta>))))
             (at \<theta>)"
    unfolding geq by (rule cm)
  have alg: "(pi^2/4) * (gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 + cos \<theta>))
                         + gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 - cos \<theta>)))
           = pi^2/4 * ((pi/2) * sin \<theta>) *
             (gsincd ((pi/2)*(1 - cos \<theta>)) * gsinc ((pi/2)*(1 + cos \<theta>))
              - gsinc ((pi/2)*(1 - cos \<theta>)) * gsincd ((pi/2)*(1 + cos \<theta>)))"
    by (simp add: algebra_simps)
  show ?thesis using raw unfolding alg .
qed

lemma frechet_derivative_real_at_one:
  fixes f :: "real \<Rightarrow> real" and x D :: real
  assumes der: "(f has_real_derivative D) (at x)"
  shows "frechet_derivative f (at x) 1 = D"
proof -
  have hd: "(f has_derivative (*) D) (at x)"
    using der unfolding has_field_derivative_def .
  have feq: "(*) D = frechet_derivative f (at x)"
    by (rule frechet_derivative_at[OF hd])
  show ?thesis using fun_cong[OF feq, of 1] by simp
qed

lemma gdip_deriv_zero_iff:
  fixes \<theta> :: real
  assumes "sin \<theta> \<noteq> 0"
  shows "frechet_derivative gdip (at \<theta>) 1 = 0 \<longleftrightarrow> cos \<theta> = 0"
proof -
  let ?um = "(pi/2)*(1 - cos \<theta>)"
  let ?up = "(pi/2)*(1 + cos \<theta>)"
  let ?br = "gsincd ?um * gsinc ?up - gsinc ?um * gsincd ?up"
  let ?D = "pi^2/4 * ((pi/2) * sin \<theta>) * ?br"
  have eval: "frechet_derivative gdip (at \<theta>) 1 = ?D"
    by (rule frechet_derivative_real_at_one[OF gdip_has_real_derivative[OF assms]])
  have c1: "cos \<theta> < 1" and c2: "- 1 < cos \<theta>"
    by (rule cos_strict_bounds_of_sin_nonzero[OF assms])+
  have um_pos: "0 < ?um"
  proof -
    have "0 < 1 - cos \<theta>" using c1 by linarith
    thus ?thesis by (rule mult_pos_pos[OF pi_half_gt_zero])
  qed
  have up_pos: "0 < ?up"
  proof -
    have "0 < 1 + cos \<theta>" using c2 by linarith
    thus ?thesis by (rule mult_pos_pos[OF pi_half_gt_zero])
  qed
  have um_pi: "?um < pi"
  proof -
    have "1 - cos \<theta> < 2" using c2 by linarith
    hence "?um < (pi/2) * 2" by (rule mult_strict_left_mono[OF _ pi_half_gt_zero])
    thus ?thesis by simp
  qed
  have up_pi: "?up < pi"
  proof -
    have "1 + cos \<theta> < 2" using c1 by linarith
    hence "?up < (pi/2) * 2" by (rule mult_strict_left_mono[OF _ pi_half_gt_zero])
    thus ?thesis by simp
  qed
  show ?thesis
  proof
    assume z: "frechet_derivative gdip (at \<theta>) 1 = 0"
    have D0: "?D = 0" using z eval by simp
    show "cos \<theta> = 0"
    proof (rule ccontr)
      assume ne: "cos \<theta> \<noteq> 0"
      have bne: "?br \<noteq> 0"
      proof (cases "0 < cos \<theta>")
        case True
        have diff: "?up - ?um = pi * cos \<theta>" by (simp add: field_simps)
        have "0 < pi * cos \<theta>" by (rule mult_pos_pos[OF pi_gt_zero True])
        hence lt: "?um < ?up" using diff by linarith
        have "0 < ?br" by (rule gsinc_wronskian_pos[OF um_pos lt up_pi])
        thus ?thesis by linarith
      next
        case False
        have neg: "cos \<theta> < 0" using False ne by linarith
        have diff: "?um - ?up = pi * (- cos \<theta>)" by (simp add: field_simps)
        have "0 < - cos \<theta>" using neg by linarith
        hence "0 < pi * (- cos \<theta>)" by (rule mult_pos_pos[OF pi_gt_zero])
        hence lt: "?up < ?um" using diff by linarith
        have rev: "0 < gsincd ?up * gsinc ?um - gsinc ?up * gsincd ?um"
          by (rule gsinc_wronskian_pos[OF up_pos lt um_pi])
        have flip: "?br = - (gsincd ?up * gsinc ?um - gsinc ?up * gsincd ?um)"
          by (simp add: algebra_simps)
        show ?thesis using rev flip by linarith
      qed
      have "?D \<noteq> 0" using assms bne by simp
      with D0 show False by simp
    qed
  next
    assume c0: "cos \<theta> = 0"
    have D0: "?D = 0" using c0 by (simp add: mult.commute)
    show "frechet_derivative gdip (at \<theta>) 1 = 0"
      by (rule trans[OF eval D0])
  qed
qed

lemma frechet_gdip_zero_arg: "frechet_derivative gdip (at \<theta>) 0 = 0" for \<theta> :: real
  using linear_frechet_derivative[OF gdip_differentiable] linear_0 by blast

subsection \<open>The second derivative at the horizontal plane\<close>

definition gsincdd :: "real \<Rightarrow> real" where
  "gsincdd x = (- (x^2) * sin x - 2 * x * cos x + 2 * sin x) / x^3"

lemma gsincd_has_deriv:
  fixes x :: real
  assumes x0: "x \<noteq> 0"
  shows "(gsincd has_real_derivative gsincdd x) (at x)"
proof -
  have num: "((\<lambda>y. y * cos y - sin y) has_real_derivative (- x * sin x)) (at x)"
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have den: "((\<lambda>y. y^2) has_real_derivative (2 * x)) (at x)"
    by (auto intro!: derivative_eq_intros)
  have x2: "x^2 \<noteq> 0" using x0 by simp
  have raw: "((\<lambda>y. (y * cos y - sin y) / y^2) has_real_derivative
              ((- x * sin x) * x^2 - (x * cos x - sin x) * (2 * x)) / (x^2 * x^2)) (at x)"
    by (rule DERIV_divide[OF num den x2])
  have eq: "((- x * sin x) * x^2 - (x * cos x - sin x) * (2 * x)) / (x^2 * x^2) = gsincdd x"
    using x0 by (simp add: gsincdd_def power2_eq_square power3_eq_cube field_simps)
  have step: "((\<lambda>y. (y * cos y - sin y) / y^2) has_real_derivative gsincdd x) (at x)"
    using raw unfolding eq .
  show ?thesis
  proof (rule has_field_derivative_transform_within_open[OF step, where S = "- {0::real}"])
    show "open (- {0::real})" by (rule open_Compl) (rule closed_singleton)
    show "x \<in> - {0::real}" using x0 by simp
    show "\<And>y. y \<in> - {0::real} \<Longrightarrow> (y * cos y - sin y) / y^2 = gsincd y"
      by (simp add: gsincd_def)
  qed
qed

definition um :: "real \<Rightarrow> real" where "um t = (pi/2)*(1 - cos t)"

definition up :: "real \<Rightarrow> real" where "up t = (pi/2)*(1 + cos t)"

definition D1f :: "real \<Rightarrow> real" where
  "D1f t = pi^2/4 * ((pi/2) * sin t) *
             (gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))"

lemma gdip_deriv_field_eq_D1f:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0"
  shows "frechet_derivative gdip (at \<theta>) 1 = D1f \<theta>"
proof -
  have "(gdip has_real_derivative D1f \<theta>) (at \<theta>)"
    using gdip_has_real_derivative[OF s0] unfolding D1f_def um_def up_def .
  thus ?thesis by (rule frechet_derivative_real_at_one)
qed

lemma D1f_has_deriv:
  fixes \<theta> :: real
  assumes um0: "um \<theta> \<noteq> 0" and up0: "up \<theta> \<noteq> 0"
  shows "(D1f has_real_derivative
           pi^2/4 *
           ( (pi/2) * cos \<theta>
              * (gsincd (um \<theta>) * gsinc (up \<theta>) - gsinc (um \<theta>) * gsincd (up \<theta>))
            + (pi/2) * sin \<theta>
              * ( ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                     + gsincd (um \<theta>) * (gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) )
                  - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                     + gsinc (um \<theta>) * (gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) ) )))
         (at \<theta>)"
proof -
  have dum: "(um has_real_derivative ((pi/2) * sin \<theta>)) (at \<theta>)"
    unfolding um_def by (auto intro!: derivative_eq_intros)
  have dup: "(up has_real_derivative (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    unfolding up_def by (auto intro!: derivative_eq_intros)
  have gsmum: "((\<lambda>t. gsinc (um t)) has_real_derivative
                 gsincd (um \<theta>) * ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF gsinc_has_real_derivative[OF um0] dum])
  have gsdmum: "((\<lambda>t. gsincd (um t)) has_real_derivative
                  gsincdd (um \<theta>) * ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF gsincd_has_deriv[OF um0] dum])
  have gsmup: "((\<lambda>t. gsinc (up t)) has_real_derivative
                 gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    by (rule DERIV_chain2[OF gsinc_has_real_derivative[OF up0] dup])
  have gsdmup: "((\<lambda>t. gsincd (up t)) has_real_derivative
                  gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    by (rule DERIV_chain2[OF gsincd_has_deriv[OF up0] dup])
  have pref: "((\<lambda>t. (pi/2) * sin t) has_real_derivative ((pi/2) * cos \<theta>)) (at \<theta>)"
    by (auto intro!: derivative_eq_intros)
  have br1: "((\<lambda>t. gsincd (um t) * gsinc (up t)) has_real_derivative
               gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                + gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsincd (um \<theta>)) (at \<theta>)"
    by (rule DERIV_mult[OF gsdmum gsmup])
  have br2: "((\<lambda>t. gsinc (um t) * gsincd (up t)) has_real_derivative
               gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                + gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsinc (um \<theta>)) (at \<theta>)"
    by (rule DERIV_mult[OF gsmum gsdmup])
  have br: "((\<lambda>t. gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))
              has_real_derivative
              ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                 + gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsincd (um \<theta>) )
              - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                 + gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsinc (um \<theta>) )) (at \<theta>)"
    by (rule DERIV_diff[OF br1 br2])
  define BR where
    "BR = ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                 + gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsincd (um \<theta>) )
              - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                 + gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsinc (um \<theta>) )"
  define BV where
    "BV = gsincd (um \<theta>) * gsinc (up \<theta>) - gsinc (um \<theta>) * gsincd (up \<theta>)"
  have brBR: "((\<lambda>t. gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))
                 has_real_derivative BR) (at \<theta>)"
    unfolding BR_def by (rule br)
  have prod: "((\<lambda>t. ((pi/2) * sin t)
                    * (gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t)))
                 has_real_derivative
                 (pi/2) * cos \<theta> * BV + BR * ((pi/2) * sin \<theta>)) (at \<theta>)"
    unfolding BV_def by (rule DERIV_mult[OF pref brBR])
  have D1f_reassoc: "D1f = (\<lambda>t. pi^2/4 * (((pi/2) * sin t)
                    * (gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))))"
    by (rule ext) (simp add: D1f_def mult.assoc)
  have raw: "(D1f has_real_derivative
                pi^2/4 * ((pi/2) * cos \<theta> * BV + BR * ((pi/2) * sin \<theta>))) (at \<theta>)"
    unfolding D1f_reassoc by (rule DERIV_cmult[OF prod])
  have eqval: "pi^2/4 * ((pi/2) * cos \<theta> * BV + BR * ((pi/2) * sin \<theta>))
       = pi^2/4 *
           ( (pi/2) * cos \<theta>
              * (gsincd (um \<theta>) * gsinc (up \<theta>) - gsinc (um \<theta>) * gsincd (up \<theta>))
            + (pi/2) * sin \<theta>
              * ( ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                     + gsincd (um \<theta>) * (gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) )
                  - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                     + gsinc (um \<theta>) * (gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) ) ))"
    unfolding BR_def BV_def by (simp add: algebra_simps)
  show ?thesis using raw unfolding eqval .
qed

lemma gdip_second_deriv_at_cos_zero:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0" and cz: "cos \<theta> = 0"
  shows "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative
            (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)) (at \<theta>)"
proof -
  have umpi: "um \<theta> = pi/2" using cz by (simp add: um_def)
  have uppi: "up \<theta> = pi/2" using cz by (simp add: up_def)
  have pih: "(pi/2::real) \<noteq> 0" using pi_gt_zero by simp
  have um0: "um \<theta> \<noteq> 0" unfolding umpi by (rule pih)
  have up0: "up \<theta> \<noteq> 0" unfolding uppi by (rule pih)
  define V where
    "V = pi^2/4 *
           ( (pi/2) * cos \<theta>
              * (gsincd (um \<theta>) * gsinc (up \<theta>) - gsinc (um \<theta>) * gsincd (up \<theta>))
            + (pi/2) * sin \<theta>
              * ( ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                     + gsincd (um \<theta>) * (gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) )
                  - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                     + gsinc (um \<theta>) * (gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) ) ))"
  have d1: "(D1f has_real_derivative V) (at \<theta>)"
    unfolding V_def by (rule D1f_has_deriv[OF um0 up0])
  have openS: "open {x::real. sin x \<noteq> 0}"
    using continuous_on_id continuous_on_sin
    by (subst open_Collect_neq, auto, simp add: continuous_at_imp_continuous_on)
  have memS: "\<theta> \<in> {x::real. sin x \<noteq> 0}" using s0 by simp
  have agree: "D1f x = frechet_derivative gdip (at x) 1" if "x \<in> {x. sin x \<noteq> 0}" for x
    using that by (simp add: gdip_deriv_field_eq_D1f)
  have d2: "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative V) (at \<theta>)"
    by (rule has_field_derivative_transform_within_open[OF d1 openS memS agree])
  have sin2: "(sin \<theta>)^2 = 1" using cz sin_cos_squared_add[of \<theta>] by simp
  have Veq: "V = (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)"
  proof -
    have "V = pi^2/4 * (((pi/2) * sin \<theta>)
              * ( (gsincdd (pi/2) * ((pi/2) * sin \<theta>)) * gsinc (pi/2)
                 + gsincd (pi/2) * (gsincd (pi/2) * (- ((pi/2) * sin \<theta>)))
                 - ( (gsincd (pi/2) * ((pi/2) * sin \<theta>)) * gsincd (pi/2)
                    + gsinc (pi/2) * (gsincdd (pi/2) * (- ((pi/2) * sin \<theta>))) )))"
      unfolding V_def umpi uppi using cz by simp
    also have "\<dots> = pi^2/4 * ((pi/2) * sin \<theta>) * ((pi/2) * sin \<theta>)
                      * (2 * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2))"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = pi^2/4 * ((pi/2)^2 * (sin \<theta>)^2)
                      * (2 * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2))"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = pi^2/4 * ((pi/2)^2 * 1)
                      * (2 * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2))"
      unfolding sin2 by simp
    also have "\<dots> = (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)"
      by (simp add: power2_eq_square power4_eq_xxxx field_simps)
    finally show ?thesis .
  qed
  show ?thesis using d2 unfolding Veq .
qed

lemma gsinc_pi_half: "gsinc (pi/2) = 2/pi"
  using pi_gt_zero by (simp add: gsinc_def)

lemma gsincd_pi_half: "gsincd (pi/2) = - (4/pi^2)"
  using pi_gt_zero by (simp add: gsincd_def power2_eq_square field_simps)

lemma gsincdd_pi_half: "gsincdd (pi/2) = 16/pi^3 - 2/pi"
proof -
  have "gsincdd (pi/2) = (- ((pi/2)^2) * 1 - 2 * (pi/2) * 0 + 2 * 1) / (pi/2)^3"
    by (simp add: gsincdd_def)
  also have "\<dots> = (2 - pi^2/4) / (pi^3/8)"
    by (simp add: power2_eq_square power3_eq_cube field_simps)
  also have "\<dots> = 16/pi^3 - 2/pi"
    using pi_gt_zero by (simp add: power2_eq_square power3_eq_cube field_simps)
  finally show ?thesis .
qed

lemma gdip_secondderiv_value:
  "(pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2) = (16 - 4*pi^2)/8"
proof -
  have br: "gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2 = 16/pi^4 - 4/pi^2"
    unfolding gsinc_pi_half gsincd_pi_half gsincdd_pi_half
    using pi_gt_zero
    by (simp add: power2_eq_square power3_eq_cube power4_eq_xxxx field_simps)
  have "(pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)
      = (pi^4/8) * (16/pi^4 - 4/pi^2)"
    unfolding br by simp
  also have "\<dots> = (16 - 4*pi^2)/8"
    using pi_gt_zero by (simp add: power4_eq_xxxx power2_eq_square field_simps)
  finally show ?thesis .
qed

lemma gdip_secondderiv_value_nonzero: "(16 - 4*pi^2)/8 \<noteq> (0::real)"
proof -
  have "(2::real) < pi" using pi_gt3 by simp
  hence "(2::real)^2 < pi^2"
    by (rule power_strict_mono) auto
  hence "(16::real) < 4 * pi^2" by (simp add: power2_eq_square)
  thus ?thesis by simp
qed

lemma gdip_scalar_second_deriv_nonzero:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0" and cz: "cos \<theta> = 0"
  shows "frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at \<theta>) 1 \<noteq> 0"
proof -
  have hd: "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative
              (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)) (at \<theta>)"
    by (rule gdip_second_deriv_at_cos_zero[OF s0 cz])
  have "frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at \<theta>) 1
       = (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)"
    by (rule frechet_derivative_real_at_one[OF hd])
  also have "\<dots> = (16 - 4*pi^2)/8" by (rule gdip_secondderiv_value)
  finally show ?thesis using gdip_secondderiv_value_nonzero by simp
qed

end
