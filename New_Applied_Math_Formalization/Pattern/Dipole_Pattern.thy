section \<open>The dipole pattern and the steering wavevector\<close>

theory Dipole_Pattern
  imports
    Pattern_Derivatives
    Moment_Map
begin

lemma frechet_derivative_at':
  "(f has_derivative f') (at x) \<Longrightarrow> frechet_derivative f (at x) = f'"
  by (rule frechet_derivative_at[symmetric])

subsection \<open>Smoothness of the building blocks\<close>

lemma sin_cos_Ck_on:
  "Ck_on n (sin::real \<Rightarrow> real) UNIV \<and> Ck_on n (cos::real \<Rightarrow> real) UNIV"
proof (induction n)
  case 0
  have a: "Ck_on 0 (sin::real \<Rightarrow> real) UNIV"
    by (simp only: Ck_on_0_iff) (intro conjI open_UNIV continuous_intros)
  have b: "Ck_on 0 (cos::real \<Rightarrow> real) UNIV"
    by (simp only: Ck_on_0_iff) (intro conjI open_UNIV continuous_intros)
  show ?case using a b by blast
next
  case (Suc n)
  have IHs: "Ck_on n (sin::real \<Rightarrow> real) UNIV"
    using Suc.IH by (rule conjunct1)
  have IHc: "Ck_on n (cos::real \<Rightarrow> real) UNIV"
    using Suc.IH by (rule conjunct2)
  have dsin: "sin differentiable (at x)" for x :: real
    using has_field_derivative_imp_has_derivative[OF DERIV_sin] by (blast intro: differentiableI)
  have dcos: "cos differentiable (at x)" for x :: real
    using has_field_derivative_imp_has_derivative[OF DERIV_cos] by (blast intro: differentiableI)
  have ms: "Ck_on n (\<lambda>x. frechet_derivative sin (at x) v) UNIV" for v :: real
  proof -
    have "(\<lambda>x::real. frechet_derivative sin (at x) v) = (\<lambda>x. cos x * v)"
    proof (rule ext)
      fix x :: real
      have "frechet_derivative sin (at x) = (*) (cos x)"
        by (rule frechet_derivative_at[symmetric,
              OF has_field_derivative_imp_has_derivative[OF DERIV_sin]])
      thus "frechet_derivative sin (at x) v = cos x * v" by simp
    qed
    moreover have "Ck_on n (\<lambda>x. cos x * v) UNIV"
      by (rule Ck_on_mult[OF IHc Ck_on_const[OF open_UNIV]])
    ultimately show ?thesis by simp
  qed
  have mc: "Ck_on n (\<lambda>x. frechet_derivative cos (at x) v) UNIV" for v :: real
  proof -
    have "(\<lambda>x::real. frechet_derivative cos (at x) v) = (\<lambda>x. sin x * (- v))"
    proof (rule ext)
      fix x :: real
      have "frechet_derivative cos (at x) = (*) (- sin x)"
        by (rule frechet_derivative_at[symmetric,
              OF has_field_derivative_imp_has_derivative[OF DERIV_cos]])
      thus "frechet_derivative cos (at x) v = sin x * (- v)" by simp
    qed
    moreover have "Ck_on n (\<lambda>x. sin x * (- v)) UNIV"
      by (rule Ck_on_mult[OF IHs Ck_on_const[OF open_UNIV]])
    ultimately show ?thesis by simp
  qed
  show ?case using dsin dcos ms mc by (simp add: Ck_on_Suc_iff)
qed

lemma cis_Ck_on: "Ck_on n cis UNIV"
proof -
  have eq: "cis = (\<lambda>t. cos t *\<^sub>R (1::complex) + sin t *\<^sub>R \<i>)"
    by (rule ext) (simp add: cis.code complex_eq_iff)
  have s: "Ck_on n (sin::real \<Rightarrow> real) UNIV"
    using sin_cos_Ck_on by (rule conjunct1)
  have c: "Ck_on n (cos::real \<Rightarrow> real) UNIV"
    using sin_cos_Ck_on by (rule conjunct2)
  have t1: "Ck_on n (\<lambda>t. cos t *\<^sub>R (1::complex)) UNIV"
    by (rule Ck_on_bilinear[OF bounded_bilinear_scaleR c Ck_on_const[OF open_UNIV]])
  have t2: "Ck_on n (\<lambda>t. sin t *\<^sub>R \<i>) UNIV"
    by (rule Ck_on_bilinear[OF bounded_bilinear_scaleR s Ck_on_const[OF open_UNIV]])
  have "Ck_on n (\<lambda>t. cos t *\<^sub>R (1::complex) + sin t *\<^sub>R \<i>) UNIV"
    by (rule Ck_on_add[OF t1 t2])
  thus ?thesis by (simp add: eq)
qed

lemma Ck_on_real_deriv_chain:
  fixes J :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes ch: "\<And>k x. (J k has_real_derivative J (Suc k) x) (at x)"
  shows "Ck_on n (J k) UNIV"
proof (induction n arbitrary: k)
  case 0
  have "continuous_on UNIV (J k)"
    by (auto intro: continuous_at_imp_continuous_on DERIV_isCont[OF ch])
  thus ?case by (simp add: Ck_on_0_iff)
next
  case (Suc n)
  have d: "J k differentiable (at x)" for x
    using ch[of k x] by (blast intro: differentiableI has_field_derivative_imp_has_derivative)
  have fd: "Ck_on n (\<lambda>x. frechet_derivative (J k) (at x) v) UNIV" for v :: real
  proof -
    have "(\<lambda>x. frechet_derivative (J k) (at x) v) = (\<lambda>x. J (Suc k) x * v)"
    proof (rule ext)
      fix x :: real
      have "frechet_derivative (J k) (at x) = (*) (J (Suc k) x)"
        by (rule frechet_derivative_at[symmetric,
              OF has_field_derivative_imp_has_derivative[OF ch]])
      thus "frechet_derivative (J k) (at x) v = J (Suc k) x * v" by simp
    qed
    moreover have "Ck_on n (\<lambda>x. J (Suc k) x * v) UNIV"
      by (rule Ck_on_mult[OF Suc.IH Ck_on_const[OF open_UNIV]])
    ultimately show ?thesis by simp
  qed
  show ?case using d fd by (simp add: Ck_on_Suc_iff)
qed

subsection \<open>The dipole gain\<close>

definition gsinc :: "real \<Rightarrow> real" where "gsinc x = (if x = 0 then 1 else sin x / x)"

definition Jsinc :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "Jsinc k x = integral (cbox 0 1) (\<lambda>t. t^k * cos (x*t + real k * (pi/2)))"

lemma Jsinc_deriv: "(Jsinc k has_real_derivative Jsinc (Suc k) x) (at x)"
proof -
  have d: "((\<lambda>x. t^k * cos (x*t + real k * (pi/2))) has_field_derivative
              (- (t^(Suc k) * sin (x*t + real k * (pi/2))))) (at x within UNIV)"
    if "x \<in> (UNIV::real set)" "t \<in> cbox (0::real) 1" for x t :: real
    by (auto intro!: derivative_eq_intros simp: algebra_simps power_Suc)
  have ib: "(\<lambda>t. t^k * cos (x*t + real k * (pi/2))) integrable_on cbox 0 1"
    if "x \<in> (UNIV::real set)" for x :: real
    by (auto intro!: integrable_continuous_real continuous_intros)
  have cf: "continuous_on (UNIV \<times> cbox 0 1)
              (\<lambda>(x,t). - (t^(Suc k) * sin (x*t + real k * (pi/2))))"
    by (auto intro!: continuous_intros simp: case_prod_beta)
  have L: "(Jsinc k has_real_derivative
              integral (cbox 0 1) (\<lambda>t. - (t^(Suc k) * sin (x*t + real k * (pi/2)))))
            (at x within UNIV)"
    unfolding Jsinc_def
    by (rule leibniz_rule_field_derivative[OF d ib cf UNIV_I convex_UNIV])
  have cshift: "cos (a + pi/2) = - sin a" for a :: real
    by (simp add: cos_add)
  have eq: "integral (cbox 0 1) (\<lambda>t. - (t^(Suc k) * sin (x*t + real k * (pi/2))))
            = Jsinc (Suc k) x"
    unfolding Jsinc_def
  proof (rule integral_cong)
    fix t :: real assume "t \<in> cbox 0 1"
    have phase: "x*t + real (Suc k) * (pi/2) = (x*t + real k * (pi/2)) + pi/2"
      by (simp add: algebra_simps)
    have "cos (x*t + real (Suc k) * (pi/2)) = - sin (x*t + real k * (pi/2))"
      unfolding phase by (rule cshift)
    thus "- (t^(Suc k) * sin (x*t + real k * (pi/2)))
            = t^(Suc k) * cos (x*t + real (Suc k) * (pi/2))"
      by simp
  qed
  from L eq show ?thesis by simp
qed

lemma Jsinc_Ck_on: "Ck_on n (Jsinc k) UNIV"
  by (intro Ck_on_real_deriv_chain Jsinc_deriv)

lemma Jsinc_0: "Jsinc 0 = gsinc"
proof (rule ext)
  fix x :: real
  have base: "Jsinc 0 x = integral {0..1} (\<lambda>t. cos (x*t))"
    by (simp add: Jsinc_def)
  show "Jsinc 0 x = gsinc x"
  proof (cases "x = 0")
    case True
    have "integral {0..1} (\<lambda>t::real. cos (x*t)) = integral {0..1} (\<lambda>t::real. 1)"
      using True by simp
    also have "\<dots> = 1" by simp
    finally show ?thesis using base True by (simp add: gsinc_def)
  next
    case False
    have "((\<lambda>t. cos (x*t)) has_integral (sin (x*1)/x - sin (x*0)/x)) {0..1}"
    proof (rule fundamental_theorem_of_calculus)
      show "(0::real) \<le> 1" by simp
    next
      fix t :: real assume "t \<in> {0..1}"
      have "((\<lambda>t. sin (x*t)/x) has_real_derivative cos (x*t)) (at t)"
        using False by (auto intro!: derivative_eq_intros)
      thus "((\<lambda>t. sin (x*t)/x) has_vector_derivative cos (x*t)) (at t within {0..1})"
        by (simp add: has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
    qed
    hence "integral {0..1} (\<lambda>t. cos (x*t)) = sin (x*1)/x - sin (x*0)/x"
      by (rule integral_unique)
    thus ?thesis using base False by (simp add: gsinc_def)
  qed
qed

lemma gsinc_Ck_on: "Ck_on n gsinc UNIV"
  using Jsinc_Ck_on[where k = 0] by (simp add: Jsinc_0)

definition edip :: "real \<Rightarrow> real" where "edip \<theta> = cos (pi/2 * cos \<theta>) / sin \<theta>"

definition gdip :: "real \<Rightarrow> real" where
  "gdip \<theta> = (pi^2/4) * (gsinc ((pi/2)*(1 - cos \<theta>)) * gsinc ((pi/2)*(1 + cos \<theta>)))"

lemma gdip_Ck_on: "Ck_on n gdip UNIV"
proof -
  have cosn: "Ck_on n (cos::real \<Rightarrow> real) UNIV"
    using sin_cos_Ck_on by (rule conjunct2)
  have am: "Ck_on n (\<lambda>\<theta>::real. (pi/2)*(1 - cos \<theta>)) UNIV"
    by (intro Ck_on_mult Ck_on_sub Ck_on_const cosn open_UNIV)
  have ap: "Ck_on n (\<lambda>\<theta>::real. (pi/2)*(1 + cos \<theta>)) UNIV"
    by (intro Ck_on_mult Ck_on_add Ck_on_const cosn open_UNIV)
  have gm: "Ck_on n (\<lambda>\<theta>. gsinc ((pi/2)*(1 - cos \<theta>))) UNIV"
    by (rule Ck_on_compose[OF gsinc_Ck_on am]) simp
  have gp: "Ck_on n (\<lambda>\<theta>. gsinc ((pi/2)*(1 + cos \<theta>))) UNIV"
    by (rule Ck_on_compose[OF gsinc_Ck_on ap]) simp
  show ?thesis
    unfolding gdip_def
    by (intro Ck_on_mult Ck_on_const gm gp open_UNIV)
qed

lemma gdip_eq_edip_sq: "gdip \<theta> = (edip \<theta>)\<^sup>2"
proof (cases "sin \<theta> = 0")
  case True
  have "(cos \<theta>)\<^sup>2 = 1" using sin_cos_squared_add[of \<theta>] True by simp
  hence cc: "cos \<theta> = 1 \<or> cos \<theta> = - 1" by (simp add: power2_eq_1_iff)
  hence num0: "cos (pi/2 * cos \<theta>) = 0" by (auto simp: cos_pi_half)
  have E: "(edip \<theta>)\<^sup>2 = 0" using True num0 by (simp add: edip_def)
  have z0: "gsinc 0 = 1" by (simp add: gsinc_def)
  have p0: "gsinc pi = 0" using pi_gt_zero by (simp add: gsinc_def)
  have G: "gdip \<theta> = 0"
    using cc by (auto simp: gdip_def z0 p0)
  show ?thesis using E G by simp
next
  case False
  have sineq: "sin \<theta> * sin \<theta> = 1 - cos \<theta> * cos \<theta>"
    using sin_cos_squared_add[of \<theta>] by (simp add: power2_eq_square algebra_simps)
  have c1: "cos \<theta> \<noteq> 1"
  proof
    assume "cos \<theta> = 1"
    with sineq have "sin \<theta> * sin \<theta> = 0" by simp
    hence "sin \<theta> = 0" by simp
    with False show False ..
  qed
  have cm1: "cos \<theta> \<noteq> - 1"
  proof
    assume "cos \<theta> = - 1"
    with sineq have "sin \<theta> * sin \<theta> = 0" by simp
    hence "sin \<theta> = 0" by simp
    with False show False ..
  qed
  have A0: "(pi/2)*(1 - cos \<theta>) \<noteq> 0"
  proof
    assume "(pi/2)*(1 - cos \<theta>) = 0"
    hence "1 - cos \<theta> = 0" using pi_gt_zero by simp
    with c1 show False by simp
  qed
  have B0: "(pi/2)*(1 + cos \<theta>) \<noteq> 0"
  proof
    assume "(pi/2)*(1 + cos \<theta>) = 0"
    hence "1 + cos \<theta> = 0" using pi_gt_zero by simp
    with cm1 show False by simp
  qed
  \<comment> \<open>product-to-sum + double angle: \<open>sin A sin B = cos\<^sup>2(\<pi>/2 cos\<theta>)\<close> with \<open>A+B=\<pi>\<close>, \<open>A-B=-\<pi>cos\<theta>\<close>\<close>
  have prod: "sin ((pi/2)*(1 - cos \<theta>)) * sin ((pi/2)*(1 + cos \<theta>)) = (cos (pi/2 * cos \<theta>))\<^sup>2"
  proof -
    have e1: "(pi/2)*(1 - cos \<theta>) - (pi/2)*(1 + cos \<theta>) = - (pi * cos \<theta>)"
      by (simp add: field_simps)
    have e2: "(pi/2)*(1 - cos \<theta>) + (pi/2)*(1 + cos \<theta>) = pi"
      by (simp add: field_simps)
    have "sin ((pi/2)*(1 - cos \<theta>)) * sin ((pi/2)*(1 + cos \<theta>))
          = (cos ((pi/2)*(1 - cos \<theta>) - (pi/2)*(1 + cos \<theta>))
             - cos ((pi/2)*(1 - cos \<theta>) + (pi/2)*(1 + cos \<theta>))) / 2"
      by (simp add: cos_diff cos_add)
    also have "\<dots> = (cos (- (pi * cos \<theta>)) - cos pi) / 2"
      by (simp only: e1 e2)
    also have "\<dots> = (cos (pi * cos \<theta>) + 1) / 2"
      by simp
    also have "\<dots> = (cos (pi/2 * cos \<theta>))\<^sup>2"
      using cos_double_cos[of "pi/2 * cos \<theta>"] by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have AB: "((pi/2)*(1 - cos \<theta>)) * ((pi/2)*(1 + cos \<theta>)) = (pi\<^sup>2/4) * (sin \<theta>)\<^sup>2"
  proof -
    have s: "(sin \<theta>)\<^sup>2 = 1 - (cos \<theta>)\<^sup>2"
      using sin_cos_squared_add[of \<theta>] by (simp add: algebra_simps)
    have "((pi/2)*(1 - cos \<theta>)) * ((pi/2)*(1 + cos \<theta>)) = (pi\<^sup>2/4) * (1 - (cos \<theta>)\<^sup>2)"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> = (pi\<^sup>2/4) * (sin \<theta>)\<^sup>2" using s by simp
    finally show ?thesis .
  qed
  have "gdip \<theta> = (pi\<^sup>2/4)
          * ((sin ((pi/2)*(1 - cos \<theta>)) * sin ((pi/2)*(1 + cos \<theta>)))
             / (((pi/2)*(1 - cos \<theta>)) * ((pi/2)*(1 + cos \<theta>))))"
    unfolding gdip_def
    using A0 B0 gsinc_def by fastforce  
    
  also have "\<dots> = (pi\<^sup>2/4) * ((cos (pi/2 * cos \<theta>))\<^sup>2 / ((pi\<^sup>2/4) * (sin \<theta>)\<^sup>2))"
    using AB prod by presburger
  also have "\<dots> = (cos (pi/2 * cos \<theta>))\<^sup>2 / (sin \<theta>)\<^sup>2"
    using pi_gt_zero False by simp
  also have "\<dots> = (edip \<theta>)\<^sup>2"
    by (simp add: edip_def power_divide)
  finally show ?thesis .
qed

definition gain_dip :: "angle \<Rightarrow> real" where "gain_dip \<omega> = gdip (\<omega> $ 1)"

lemma gain_dip_Ck_on: "Ck_on n gain_dip UNIV"
proof -
  have proj: "Ck_on n (\<lambda>\<omega>::real^2. \<omega> $ 1) UNIV"
    by (rule Ck_on_component[OF Ck_on_id[OF open_UNIV]])
  have "Ck_on n (\<lambda>\<omega>::real^2. gdip (\<omega> $ 1)) UNIV"
    by (rule Ck_on_compose[OF gdip_Ck_on proj]) simp
  thus ?thesis by (simp add: gain_dip_def[abs_def])
qed

lemma gdip_differentiable: "gdip differentiable (at (x::real))"
  using gdip_Ck_on[of "Suc 0"] unfolding Ck_on_Suc_iff by blast

lemma gdip_deriv_differentiable:
  fixes t :: real
  shows "(\<lambda>t. frechet_derivative gdip (at t) v) differentiable (at t)"
proof -
  have "Ck_on (Suc 0) (\<lambda>y. frechet_derivative gdip (at y) v) UNIV"
    using gdip_Ck_on[of "Suc (Suc 0)"] unfolding Ck_on_Suc_iff[of "Suc 0"] by blast
  thus ?thesis unfolding Ck_on_Suc_iff by blast
qed

subsection \<open>The steering wavevector\<close>

definition kx :: "angle \<Rightarrow> real" where "kx \<omega> = sin (\<omega>$1) * cos (\<omega>$2)"

definition ky :: "angle \<Rightarrow> real" where "ky \<omega> = sin (\<omega>$1) * sin (\<omega>$2)"

definition kz :: "angle \<Rightarrow> real" where "kz \<omega> = cos (\<omega>$1)"

lemma proj_Ck_on: "Ck_on n (\<lambda>\<omega>::real^2. \<omega> $ i) UNIV"
  by (rule Ck_on_component[OF Ck_on_id[OF open_UNIV]])

lemma sin_proj_Ck_on: "Ck_on n (\<lambda>\<omega>::real^2. sin (\<omega> $ i)) UNIV"
  by (rule Ck_on_compose[OF conjunct1[OF sin_cos_Ck_on] proj_Ck_on]) simp

lemma cos_proj_Ck_on: "Ck_on n (\<lambda>\<omega>::real^2. cos (\<omega> $ i)) UNIV"
  by (rule Ck_on_compose[OF conjunct2[OF sin_cos_Ck_on] proj_Ck_on]) simp

lemma kx_Ck_on: "Ck_on n kx UNIV"
  unfolding kx_def[abs_def]
  by (rule Ck_on_mult[OF sin_proj_Ck_on cos_proj_Ck_on])

lemma ky_Ck_on: "Ck_on n ky UNIV"
  unfolding ky_def[abs_def]
  by (rule Ck_on_mult[OF sin_proj_Ck_on sin_proj_Ck_on])

lemma kz_Ck_on: "Ck_on n kz UNIV"
  unfolding kz_def[abs_def]
  by (rule cos_proj_Ck_on)

definition cvec_dip :: "angle \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> real^2" where
  "cvec_dip \<omega>0 \<omega>s \<omega> =
     ((kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) *\<^sub>R axis 1 1
   + ((ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) *\<^sub>R axis 2 1"

lemma cvec_dip_Ck_on: "Ck_on n (cvec_dip \<omega>0 \<omega>s) UNIV"
proof -
  have comp1: "Ck_on n
      (\<lambda>\<omega>. (kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) UNIV"
    by (intro Ck_on_add Ck_on_sub Ck_on_mult Ck_on_const kx_Ck_on kz_Ck_on open_UNIV)
  have comp2: "Ck_on n
      (\<lambda>\<omega>. (ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) UNIV"
    by (intro Ck_on_add Ck_on_sub Ck_on_mult Ck_on_const ky_Ck_on kz_Ck_on open_UNIV)
  have s1: "Ck_on n (\<lambda>\<omega>. ((kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s))
              *\<^sub>R (axis 1 1 :: real^2)) UNIV"
    by (rule Ck_on_bilinear[OF bounded_bilinear_scaleR comp1 Ck_on_const[OF open_UNIV]])
  have s2: "Ck_on n (\<lambda>\<omega>. ((ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s))
              *\<^sub>R (axis 2 1 :: real^2)) UNIV"
    by (rule Ck_on_bilinear[OF bounded_bilinear_scaleR comp2 Ck_on_const[OF open_UNIV]])
  show ?thesis
    unfolding cvec_dip_def[abs_def]
    by (rule Ck_on_add[OF s1 s2])
qed

lemma has_derivative_proj:
  "((\<lambda>\<omega>::real^2. \<omega> $ i) has_derivative (\<lambda>h. h $ i)) (at \<omega>)"
  by (auto intro!: bounded_linear.has_derivative[OF bounded_linear_vec_nth]
                   has_derivative_ident)

lemma gain_dip_has_derivative:
  \<comment> \<open>the chain rule through the projection onto the polar angle\<close>
  "(gain_dip has_derivative
      (\<lambda>v. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1))) (at \<omega>)"
proof -
  have "((gdip \<circ> (\<lambda>\<omega>. vec_nth \<omega> 1)) has_derivative
          (frechet_derivative gdip (at (vec_nth \<omega> 1)) \<circ> (\<lambda>v. vec_nth v 1))) (at \<omega>)"
    by (rule diff_chain_at[OF has_derivative_proj
          frechet_derivative_works[THEN iffD1, OF gdip_differentiable]])
  thus ?thesis
    by (metis (no_types, lifting) ext gain_dip_def o_def)
qed

lemma has_derivative_kx:
  "(kx has_derivative (\<lambda>h. cos (\<omega>$1) * cos (\<omega>$2) * (h$1) - sin (\<omega>$1) * sin (\<omega>$2) * (h$2)))
     (at \<omega>)"
  unfolding kx_def[abs_def]
  by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)

lemma has_derivative_ky:
  "(ky has_derivative (\<lambda>h. cos (\<omega>$1) * sin (\<omega>$2) * (h$1) + sin (\<omega>$1) * cos (\<omega>$2) * (h$2)))
     (at \<omega>)"
  unfolding ky_def[abs_def]
  by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)

lemma has_derivative_kz:
  "(kz has_derivative (\<lambda>h. - sin (\<omega>$1) * (h$1))) (at \<omega>)"
  unfolding kz_def[abs_def]
  by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)

definition Dcvec_dip :: "angle \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> real^2 \<Rightarrow> real^2" where
  \<comment> \<open>the Jacobian of @{const cvec_dip}\<close>
  "Dcvec_dip \<omega>0 \<omega>s \<omega> =
     (\<lambda>h. ((cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2) * (vec_nth h 1)
              - sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2) * (vec_nth h 2))
              + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (- sin (vec_nth \<omega> 1) * (vec_nth h 1))) *\<^sub>R axis 1 1
          + ((cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2) * (vec_nth h 1)
              + sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2) * (vec_nth h 2))
              + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (- sin (vec_nth \<omega> 1) * (vec_nth h 1))) *\<^sub>R axis 2 1)"

lemma has_derivative_cvec_dip:
  "(cvec_dip \<omega>0 \<omega>s has_derivative Dcvec_dip \<omega>0 \<omega>s \<omega>) (at \<omega>)"
  \<comment> \<open>Deterministic, \<^emph>\<open>fast\<close> proof: build the derivative tree \<^emph>\<open>bottom-up\<close> by explicit
      \<open>[OF]\<close> composition of the \<^emph>\<open>specific\<close> non-eq \<open>has_derivative\<close> rules --- pure first-order
      resolution, \<^bold>\<open>no\<close> \<open>auto\<close>/\<open>rule+\<close> backtracking and \<^bold>\<open>no\<close> higher-order unification search
      against \<open>derivative_eq_intros\<close>.  @{thm has_derivative_eq_rhs} lets us state the clean
      derivative; one \<open>simp\<close> clears the \<open>- 0\<close> cruft.\<close>
  unfolding cvec_dip_def[abs_def] Dcvec_dip_def[abs_def]
  by (rule has_derivative_eq_rhs[OF
        has_derivative_add[OF
          has_derivative_scaleR_left[OF
            has_derivative_add[OF
              has_derivative_diff[OF has_derivative_kx has_derivative_const]
              has_derivative_mult_right[OF
                has_derivative_diff[OF has_derivative_kz has_derivative_const]]]]
          has_derivative_scaleR_left[OF
            has_derivative_add[OF
              has_derivative_diff[OF has_derivative_ky has_derivative_const]
              has_derivative_mult_right[OF
                has_derivative_diff[OF has_derivative_kz has_derivative_const]]]]]])
     (simp add: algebra_simps fun_eq_iff)

lemma frechet_derivative_cvec_dip:
  "frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at \<omega>) = Dcvec_dip \<omega>0 \<omega>s \<omega>"
  by (rule frechet_derivative_at[symmetric, OF has_derivative_cvec_dip])

lemma jacobian_cvec_dip:
  "jacobian (cvec_dip \<omega>0 \<omega>s) (at \<omega>) = matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
  by (simp add: jacobian_def frechet_derivative_cvec_dip)

definition D2cvec_dip :: "angle \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> planar \<Rightarrow> planar \<Rightarrow> planar" where
  \<comment> \<open>the explicit Hessian (second derivative) of \<open>cvec_dip\<close> --- a \<open>sin/cos\<close> bilinear form
      in the directions \<open>h, h'\<close>; \<open>vec_nth\<close> (not \<open>$\<close>) for fast parsing, still prints as \<open>$\<close>.\<close>
  "D2cvec_dip \<omega>0 \<omega>s \<omega> h =
     (\<lambda>h'. ((- vec_nth h 1 * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
              - vec_nth h 2 * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
              - ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * vec_nth h 1 * cos (vec_nth \<omega> 1)) * vec_nth h' 1
            + (- vec_nth h 1 * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
              - vec_nth h 2 * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)) * vec_nth h' 2) *\<^sub>R axis 1 1
          + ((- vec_nth h 1 * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
              + vec_nth h 2 * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
              - ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * vec_nth h 1 * cos (vec_nth \<omega> 1)) * vec_nth h' 1
            + (vec_nth h 1 * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
              - vec_nth h 2 * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)) * vec_nth h' 2) *\<^sub>R axis 2 1)"

lemma has_derivative_Dcvec_dip:
  "((\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) has_derivative D2cvec_dip \<omega>0 \<omega>s \<omega> h) (at \<omega>)"
proof -
  \<comment> \<open>The beam-lift coefficients are \<^emph>\<open>constants\<close> in \<open>\<omega>\<close>; naming them with \<open>define\<close> stops
      \<open>auto\<close> from applying the quotient rule (which would spawn a spurious
      \<open>kz \<omega>\<^sub>s \<noteq> kz \<omega>\<^sub>0\<close> side-condition).  We fold them back in the final assembly.\<close>
  define Dx where "Dx = (kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  define Dy where "Dy = (ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  have dP1: "((\<lambda>y. (cos (vec_nth y 1) * cos (vec_nth y 2) * (vec_nth h 1)
                     - sin (vec_nth y 1) * sin (vec_nth y 2) * (vec_nth h 2))
                   + Dx * (- sin (vec_nth y 1) * (vec_nth h 1)))
              has_derivative
              (\<lambda>h'. (- vec_nth h 1 * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
                     - vec_nth h 2 * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
                     - Dx * vec_nth h 1 * cos (vec_nth \<omega> 1)) * vec_nth h' 1
                   + (- vec_nth h 1 * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
                     - vec_nth h 2 * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)) * vec_nth h' 2)) (at \<omega>)"
    by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)
  have dP2: "((\<lambda>y. (cos (vec_nth y 1) * sin (vec_nth y 2) * (vec_nth h 1)
                     + sin (vec_nth y 1) * cos (vec_nth y 2) * (vec_nth h 2))
                   + Dy * (- sin (vec_nth y 1) * (vec_nth h 1)))
              has_derivative
              (\<lambda>h'. (- vec_nth h 1 * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
                     + vec_nth h 2 * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
                     - Dy * vec_nth h 1 * cos (vec_nth \<omega> 1)) * vec_nth h' 1
                   + (vec_nth h 1 * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
                     - vec_nth h 2 * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)) * vec_nth h' 2)) (at \<omega>)"
    by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)
  show ?thesis
    unfolding D2cvec_dip_def[abs_def] Dcvec_dip_def[abs_def] Dx_def[symmetric] Dy_def[symmetric]
    by (rule has_derivative_add[OF has_derivative_scaleR_left[OF dP1]
                                   has_derivative_scaleR_left[OF dP2]])
qed

subsection \<open>The pattern is smooth; its gradient and Hessian are continuous\<close>

definition U_dip :: "angle \<Rightarrow> angle \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> real" where
  "U_dip \<omega>0 \<omega>s x \<omega> = U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>"

lemma A_cart_dip_Ck_on: "Ck_on n (\<lambda>\<omega>. A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>) UNIV"
proof -
  have summand: "Ck_on n (\<lambda>\<omega>. cis (- ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ j)))) UNIV" for j
  proof -
    have arg: "Ck_on n (\<lambda>\<omega>. - ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ j))) UNIV"
      by (intro Ck_on_neg Ck_on_inner cvec_dip_Ck_on Ck_on_const open_UNIV)
    show ?thesis
      by (rule Ck_on_compose[OF cis_Ck_on arg]) simp
  qed
  have "Ck_on n (\<lambda>\<omega>. \<Sum>j\<in>UNIV. cis (- ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ j)))) UNIV"
    by (rule Ck_on_sum) (simp_all add: summand)
  thus ?thesis by (simp add: A_cart_def)
qed

lemma U_dip_Ck_on: "Ck_on n (U_dip \<omega>0 \<omega>s x) UNIV"
proof -
  have AA: "Ck_on n (\<lambda>\<omega>. (cmod (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))\<^sup>2) UNIV"
  proof -
    have "(\<lambda>\<omega>. (cmod (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))\<^sup>2)
          = (\<lambda>\<omega>. inner (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>) (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))"
      by (rule ext) (simp add: power2_norm_eq_inner)
    thus ?thesis
      using Ck_on_inner[OF A_cart_dip_Ck_on[of n \<omega>0 \<omega>s x] A_cart_dip_Ck_on[of n \<omega>0 \<omega>s x]] by simp
  qed
  have "Ck_on n (\<lambda>\<omega>. gain_dip \<omega> * (cmod (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))\<^sup>2) UNIV"
    by (rule Ck_on_mult[OF gain_dip_Ck_on AA])
  thus ?thesis by (simp add: U_dip_def[abs_def] U_cart_def[abs_def])
qed

lemma U_dip_Ck2: "Ck_on 2 (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x) UNIV"
  using U_dip_Ck_on[of 2 \<omega>0 \<omega>s x] by (simp add: U_dip_def[abs_def])

lemma gradU_dip_has_derivative:
  "(gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x
      has_derivative (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)) (at \<omega>)"
  by (rule gradU_has_derivative_of_C2[OF U_dip_Ck2 UNIV_I])

lemma gradU_dip_continuous_on:
  "continuous_on S (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
proof (rule continuous_at_imp_continuous_on, rule ballI)
  fix \<omega> assume "\<omega> \<in> S"
  show "continuous (at \<omega>) (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
    by (rule has_derivative_continuous[OF gradU_dip_has_derivative])
qed

lemma norm_gradU_dip_continuous_on:
  "continuous_on S (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  by (intro continuous_on_norm gradU_dip_continuous_on)

lemma HessU_dip_continuous_on:
  "continuous_on S (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
proof -
  have eq: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x = \<nabla>\<^sup>2 (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
    by (rule ext) (simp add: HessU_def)
  have "continuous_on UNIV (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
    unfolding eq by (rule Ck_2_imp_hessian_continuous[OF U_dip_Ck2])
  thus ?thesis by (rule continuous_on_subset) simp
qed

lemma continuous_on_A_moment_joint:
    "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
  (\<lambda>p. A_moment (fst p) (snd p))"
    unfolding A_moment_def phase_def
    by (intro continuous_on_sum continuous_on_cis continuous_intros
              bounded_linear.continuous_on[OF
  bounded_linear_vec_nth])

lemma continuous_on_M1_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
     (\<lambda>p. M1_moment (fst p) (snd p))"
  unfolding M1_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_M2_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
     (\<lambda>p. M2_moment (fst p) (snd p))"
  unfolding M2_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_cvec_dip:
  "continuous_on UNIV (cvec_dip \<omega>0 \<omega>s)"
  by (rule Ck_on_imp_continuous_on[OF cvec_dip_Ck_on])

lemma continuous_on_pair_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. (fst p, cvec_dip \<omega>0 \<omega>s (snd p)))"
  by (intro continuous_on_Pair continuous_on_fst[OF continuous_on_id]
            continuous_on_compose2[OF continuous_on_cvec_dip
                                      continuous_on_snd[OF continuous_on_id] subset_UNIV])

lemma continuous_on_A_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. A_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_A_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M1_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M1_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_M1_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M2_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M2_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_M2_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_gain_dip:
  "continuous_on UNIV gain_dip"
  by (rule Ck_on_imp_continuous_on[OF gain_dip_Ck_on])

lemma continuous_on_Dcvec_dip:
  "continuous_on UNIV (\<lambda>\<omega>. Dcvec_dip \<omega>0 \<omega>s \<omega> h)"
proof -
  have "Ck_on (Suc 0) (\<lambda>\<omega>. frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at \<omega>) h) UNIV"
    using cvec_dip_Ck_on[of "Suc (Suc 0)" \<omega>0 \<omega>s] unfolding Ck_on_Suc_iff[of "Suc 0"] by blast
  hence "continuous_on UNIV (\<lambda>\<omega>. frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at \<omega>) h)"
    by (rule Ck_on_imp_continuous_on)
  thus ?thesis by (simp add: frechet_derivative_cvec_dip)
qed

lemma continuous_on_D2cvec_dip:
  "continuous_on UNIV (\<lambda>\<omega>. D2cvec_dip \<omega>0 \<omega>s \<omega> h h')"
proof -
  have C1: "Ck_on (Suc 0) (\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) UNIV"
  proof -
    have "Ck_on (Suc 0) (\<lambda>y. frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at y) h) UNIV"
      using cvec_dip_Ck_on[of "Suc (Suc 0)" \<omega>0 \<omega>s] unfolding Ck_on_Suc_iff[of "Suc 0"] by blast
    thus ?thesis by (simp add: frechet_derivative_cvec_dip)
  qed
  from C1 have "Ck_on 0 (\<lambda>x. frechet_derivative (\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) (at x) h') UNIV"
    unfolding Ck_on_Suc_iff by blast
  hence "continuous_on UNIV (\<lambda>x. frechet_derivative (\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) (at x) h')"
    by (rule Ck_on_imp_continuous_on)
  thus ?thesis
    by (simp add: frechet_derivative_at[OF has_derivative_Dcvec_dip])
qed

lemma continuous_on_frechet_gdip_proj:
  "continuous_on UNIV (\<lambda>\<omega>::real^2. frechet_derivative gdip (at (\<omega>$1)) r)"
proof -
  have g: "continuous_on UNIV (\<lambda>t::real. frechet_derivative gdip (at t) r)"
  proof -
    have "Ck_on (Suc 0) (\<lambda>t. frechet_derivative gdip (at t) r) UNIV"
      using gdip_Ck_on[of "Suc (Suc 0)"] unfolding Ck_on_Suc_iff[of "Suc 0"] by blast
    thus ?thesis by (rule Ck_on_imp_continuous_on)
  qed
  show ?thesis
    by (rule continuous_on_compose2[OF g
          bounded_linear.continuous_on[OF bounded_linear_vec_nth continuous_on_id] subset_UNIV])
qed

lemma continuous_on_frechet2_gdip_proj:
  "continuous_on UNIV
     (\<lambda>\<omega>::real^2. frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) c) (at \<omega>) v)"
proof -
  have outer1: "Ck_on (Suc 0) (\<lambda>t. frechet_derivative gdip (at t) c) UNIV"
    using gdip_Ck_on[of "Suc (Suc 0)"] unfolding Ck_on_Suc_iff[of "Suc 0"] by blast
  have f1C1: "Ck_on (Suc 0) (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) c) UNIV"
    by (rule Ck_on_compose[OF outer1 proj_Ck_on]) simp
  from f1C1 have "Ck_on 0
       (\<lambda>x. frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) c) (at x) v) UNIV"
    unfolding Ck_on_Suc_iff by blast
  thus ?thesis by (rule Ck_on_imp_continuous_on)
qed

end
