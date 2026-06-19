theory Scratch_m5_gdip2
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>(M5 genuine core) The scalar second derivative of the sinc-factored dipole gain
  at a cos-zero is nonzero: \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close>.  This kills both D2 and D5.

  Strategy:
  \<^item> \<open>gdip2 \<omega>\<close> is, by the projection bridge, the scalar second derivative of \<open>gdip\<close> at \<open>\<omega>$1\<close>;
  \<^item> the first-derivative FIELD of \<open>gdip\<close> agrees on the open set \<open>{sin \<noteq> 0}\<close> with the explicit
    \<open>D1 t = (\<pi>\<^sup>2/4)((\<pi>/2)sin t)(gsincd(u\<^sub>-)gsinc(u\<^sub>+) - gsinc(u\<^sub>-)gsincd(u\<^sub>+))\<close> (R4 \<open>g1_gdip_has_deriv\<close>);
  \<^item> differentiating \<open>D1\<close> again (chain/product, with \<open>u\<^sub>\<pm> \<noteq> 0\<close> near a cos-zero) and evaluating
    at \<open>cos \<theta> = 0\<close> (where \<open>u\<^sub>- = u\<^sub>+ = \<pi>/2\<close>, the bracket vanishes) gives the value above.\<close>


section \<open>The explicit second derivative of \<open>gsinc\<close> off zero\<close>

text \<open>\<open>gsincdd x = (- x\<^sup>2 sin x - 2 x cos x + 2 sin x)/x\<^sup>3\<close> is the derivative of \<open>gsincd\<close>.\<close>

definition gsincdd :: "real \<Rightarrow> real" where
  "gsincdd x = (- (x^2) * sin x - 2 * x * cos x + 2 * sin x) / x^3"

lemma gsincd_has_deriv:
  fixes x :: real
  assumes x0: "x \<noteq> 0"
  shows "(gsincd has_real_derivative gsincdd x) (at x)"
proof -
  \<comment> \<open>differentiate \<open>(x cos x - sin x)/x\<^sup>2\<close> directly; the numerator derivative is \<open>- x sin x\<close>\<close>
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


section \<open>The explicit first-derivative field of \<open>gdip\<close> and its derivative\<close>

text \<open>Abbreviations for the two sinc arguments and the bracket.\<close>

definition um :: "real \<Rightarrow> real" where "um t = (pi/2)*(1 - cos t)"
definition up :: "real \<Rightarrow> real" where "up t = (pi/2)*(1 + cos t)"

definition D1f :: "real \<Rightarrow> real" where
  "D1f t = pi^2/4 * ((pi/2) * sin t) *
             (gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))"

text \<open>On \<open>{sin \<noteq> 0}\<close>, the first-derivative field of \<open>gdip\<close> is exactly \<open>D1f\<close> (R4).\<close>

lemma gdip_deriv_field_eq_D1f:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0"
  shows "frechet_derivative gdip (at \<theta>) 1 = D1f \<theta>"
proof -
  have "(gdip has_real_derivative D1f \<theta>) (at \<theta>)"
    using g1_gdip_has_deriv[OF s0] unfolding D1f_def um_def up_def .
  thus ?thesis by (rule g1_frechet_eval)
qed

text \<open>Derivative of \<open>D1f\<close> at a point where both sinc arguments are nonzero
  (in particular near a cos-zero).  We give the full product/chain expansion.\<close>

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
  \<comment> \<open>derivatives of the two arguments\<close>
  have dum: "(um has_real_derivative ((pi/2) * sin \<theta>)) (at \<theta>)"
    unfolding um_def by (auto intro!: derivative_eq_intros)
  have dup: "(up has_real_derivative (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    unfolding up_def by (auto intro!: derivative_eq_intros)
  \<comment> \<open>chain rule for the four sinc/sincd composites\<close>
  have gsmum: "((\<lambda>t. gsinc (um t)) has_real_derivative
                 gsincd (um \<theta>) * ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF g1_gsinc_has_deriv[OF um0] dum])
  have gsdmum: "((\<lambda>t. gsincd (um t)) has_real_derivative
                  gsincdd (um \<theta>) * ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF gsincd_has_deriv[OF um0] dum])
  have gsmup: "((\<lambda>t. gsinc (up t)) has_real_derivative
                 gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    by (rule DERIV_chain2[OF g1_gsinc_has_deriv[OF up0] dup])
  have gsdmup: "((\<lambda>t. gsincd (up t)) has_real_derivative
                  gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    by (rule DERIV_chain2[OF gsincd_has_deriv[OF up0] dup])
  \<comment> \<open>the prefactor \<open>(\<pi>/2) sin t\<close>\<close>
  have pref: "((\<lambda>t. (pi/2) * sin t) has_real_derivative ((pi/2) * cos \<theta>)) (at \<theta>)"
    by (auto intro!: derivative_eq_intros)
  \<comment> \<open>assemble explicitly; \<open>DERIV_mult\<close> gives \<open>Da * g x + Db * f x\<close>\<close>
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
  \<comment> \<open>product of prefactor and bracket; \<open>DERIV_mult\<close> orientation \<open>Da * g x + Db * f x\<close>\<close>
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


section \<open>The second-derivative field of \<open>gdip\<close> agrees with \<open>D1f'\<close> near a cos-zero\<close>

text \<open>The first-derivative field \<open>t \<mapsto> \<partial>gdip(t) 1\<close> equals \<open>D1f\<close> on the open set
  \<open>{sin \<noteq> 0}\<close>, which contains every cos-zero.  Hence at a cos-zero the second
  derivative of \<open>gdip\<close> equals the derivative of \<open>D1f\<close>.\<close>

lemma gdip_second_deriv_at_cos_zero:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0" and cz: "cos \<theta> = 0"
  shows "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative
            (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)) (at \<theta>)"
proof -
  \<comment> \<open>at a cos-zero both sinc arguments equal \<open>\<pi>/2 \<noteq> 0\<close>\<close>
  have umpi: "um \<theta> = pi/2" using cz by (simp add: um_def)
  have uppi: "up \<theta> = pi/2" using cz by (simp add: up_def)
  have pih: "(pi/2::real) \<noteq> 0" using pi_gt_zero by simp
  have um0: "um \<theta> \<noteq> 0" unfolding umpi by (rule pih)
  have up0: "up \<theta> \<noteq> 0" unfolding uppi by (rule pih)
  \<comment> \<open>\<open>D1f\<close> is differentiable at \<open>\<theta>\<close> with the explicit derivative\<close>
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
  \<comment> \<open>open neighborhood on which the gdip-derivative field equals \<open>D1f\<close>\<close>
  have openS: "open {x::real. sin x \<noteq> 0}"
    by (rule open_Collect_neq) (auto intro!: continuous_intros)
  have memS: "\<theta> \<in> {x::real. sin x \<noteq> 0}" using s0 by simp
  have agree: "D1f x = frechet_derivative gdip (at x) 1" if "x \<in> {x. sin x \<noteq> 0}" for x
    using that by (simp add: gdip_deriv_field_eq_D1f)
  have d2: "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative V) (at \<theta>)"
    by (rule has_field_derivative_transform_within_open[OF d1 openS memS agree])
  \<comment> \<open>evaluate \<open>V\<close> at the cos-zero: prefactor-derivative term drops (\<open>cos \<theta> = 0\<close>),
      arguments collapse to \<open>\<pi>/2\<close>; \<open>(\<pi>/2 sin \<theta>)\<^sup>2 = \<pi>\<^sup>2/4\<close> via \<open>sin\<^sup>2\<theta> = 1\<close>\<close>
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


section \<open>The numeric value: \<open>gdip''(cos-zero) = (16 - 4\<pi>\<^sup>2)/8\<close>\<close>

text \<open>\<open>gsinc(\<pi>/2) = 2/\<pi>\<close>, \<open>gsincd(\<pi>/2) = -4/\<pi>\<^sup>2\<close>, \<open>gsincdd(\<pi>/2) = 16/\<pi>\<^sup>3 - 2/\<pi>\<close>.\<close>

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


section \<open>Bridge from \<open>gdip2\<close> to the scalar second derivative\<close>

text \<open>\<open>gdip2\<close> is the \<open>e\<^sub>1\<close>-directional second derivative of the gain (verbatim copy of the
  BeamHess definition; not present in the heap, so re-declared here).\<close>

definition gdip2 :: "real^2 \<Rightarrow> real" where
  "gdip2 \<omega> = frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>) (axis 1 1)"

text \<open>Re-proof of the projection bridge (heap-only deps): the \<open>e\<^sub>1\<close>-directional second
  derivative of the \<open>\<eta>\<close>-field \<open>\<eta> \<mapsto> \<partial>gdip(\<eta>$1) 1\<close> equals the scalar second derivative
  of \<open>t \<mapsto> \<partial>gdip(t) 1\<close> at \<open>\<omega>$1\<close>.\<close>

lemma gdip2_eq_scalar_second_deriv:
  fixes \<omega> :: "real^2"
  shows "gdip2 \<omega> = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
proof -
  have d1: "(\<lambda>t. frechet_derivative gdip (at t) 1) differentiable (at (\<omega>$1))"
    by (rule gdip_deriv_differentiable)
  obtain D where D: "((\<lambda>t. frechet_derivative gdip (at t) 1) has_derivative D) (at (\<omega>$1))"
    using d1 unfolding differentiable_def by blast
  have proj: "((\<lambda>\<eta>::real^2. \<eta>$1) has_derivative (\<lambda>h. h$1)) (at \<omega>)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_ident])
  have "((\<lambda>t. frechet_derivative gdip (at t) 1) \<circ> (\<lambda>\<eta>::real^2. \<eta>$1) has_derivative
            (D \<circ> (\<lambda>h. h$1))) (at \<omega>)"
    by (rule diff_chain_at[OF proj D])
  hence hd: "((\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) has_derivative
            (\<lambda>h. D (h$1))) (at \<omega>)"
    by (simp add: o_def)
  have Deq: "D = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1))"
    by (rule frechet_derivative_at[OF D])
  have fd: "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>)
          = (\<lambda>h. D (h$1))"
    by (rule frechet_derivative_at[symmetric, OF hd])
  have one: "((axis (1::2) 1)::real^2)$1 = 1" by (simp add: axis_def)
  have "gdip2 \<omega> = frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>) (axis 1 1)"
    by (simp add: gdip2_def)
  also have "\<dots> = D ((axis (1::2) 1)$1)" by (subst fd) (rule refl)
  also have "\<dots> = D 1" using one by simp
  also have "\<dots> = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
    using fun_cong[OF Deq, of 1] by simp
  finally show ?thesis .
qed


section \<open>The target lemma (verbatim statement)\<close>

lemma gdip2_nonzero_of_cos_zero:
  fixes \<omega> :: "real^2"
  assumes s1: "sin (\<omega> $ 1) \<noteq> 0" and cz: "cos (\<omega> $ 1) = 0"
  shows "gdip2 \<omega> \<noteq> 0"
proof -
  have hd: "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative
              (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)) (at (\<omega>$1))"
    by (rule gdip_second_deriv_at_cos_zero[OF s1 cz])
  have val: "frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1
           = (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)"
    by (rule g1_frechet_eval[OF hd])
  have "gdip2 \<omega> = (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)"
    unfolding gdip2_eq_scalar_second_deriv val ..
  also have "\<dots> = (16 - 4*pi^2)/8" by (rule gdip_secondderiv_value)
  finally show ?thesis using gdip_secondderiv_value_nonzero by simp
qed

end
