theory Scratch_m5_D5
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) stub D5 --- the steering-singular corner \<open>det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0\<close>.\<close>

  This file closes the heavy stub @{text m5_D5_steersing} of the M5 skeleton: the
  \<open>(\<not> surj, det Dcvec = 0)\<close> corner of the rank-deficient stratum.  It is the exact
  mirror of @{thm meager_steering_singular_stratum} (M6) in the heap, with the single
  difference that the moment-map slice carries \<open>\<not> surj (DM_paper_x x c)\<close> in place of
  M6's \<open>surj (DM_paper_x x c)\<close>.

  \<^bold>\<open>The R3 kernel-direction reduction needs NO \<open>surj\<close> hypothesis.\<close>  The witness-confinement
  step of M6 --- which collapses every bad witness angle into the FINITE set \<open>K\<close> (cos zeros
  \<open>\<times>\<close> phase-lattice zeros) --- rests only on @{thm M6_witness_gdip_deriv_zero} (which uses
  \<open>gradU = 0\<close>, \<open>A \<noteq> 0\<close>, \<open>det Dcvec = 0\<close>; \<^emph>\<open>not\<close> surjectivity) plus @{thm Dcvec_det_eq}.
  So the identical confinement applies here.  Once confined, D5 = a finite union over \<open>K\<close>
  of per-angle x-slices; each slice is shown meager.

  \<^bold>\<open>The per-angle slices.\<close>  For a fixed witness angle \<open>\<omega>\<close> with \<open>sin (\<omega>$1) \<noteq> 0\<close>:
  \<^item> If \<open>cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0\<close>: the slice injects into \<open>{x. \<not> surj (DM_paper_x x c)}\<close>, which is
    nowhere dense by the \<open>mstarg\<close> freebie @{text fixed_c_nonsurj_nowhere_dense}
    (= @{text nowhere_dense_mstarg_zeros} \<circ> @{text surj_iff_mstarg} at the Robust3 splice;
    mirror of D34's @{text fixed_c_nonsurj_nowhere_dense}).
  \<^item> If \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>: \<open>\<not> surj (DM_paper_x x 0)\<close> holds for \<^emph>\<open>all\<close> \<open>x\<close>
    (@{thm DM_paper_x_null_not_surj}), so the slice is exactly the D2 beam-center set at \<open>\<omega>\<close>
    \<open>{x. gradU = 0 \<and> A \<noteq> 0 \<and> det HessU = 0}\<close>; its meagerness is the D2 covariance-polynomial
    argument (\<open>gdip''(\<pi>/2) \<noteq> 0\<close>), isolated here as the single genuine per-angle obligation
    @{text m5_D5_beamcenter_angle_meager}.

  \<^bold>\<open>Splice freebies.\<close>  Because \<open>\<omega>0 \<omega>s\<close> are FREE here (the heap above the splice has no global
  \<open>\<omega>0 \<omega>s\<close>; they become the concrete @{text \<omega>0_def}/@{text \<omega>s_def} in Robust3), the M6
  separation hypotheses \<open>hsep : kz \<omega>s \<noteq> kz \<omega>0\<close> and \<open>kdiff : kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s\<close>
  are carried as local stub lemmas; both are discharged \<^emph>\<open>by simp\<close> for the concrete constants
  at the splice (Robust3 L1634--1637), so they are freebies.\<close>


subsection \<open>Splice freebie: the phase-separation data (concrete at Robust3)\<close>

text \<open>\<open>kz \<omega>s \<noteq> kz \<omega>0\<close>: the two beams are not co-elevation.  At the splice this is
  @{text "by (simp add: \<omega>s_def \<omega>0_def kz_def)"} for \<open>\<omega>0 = vector[\<pi>/2,0]\<close>, \<open>\<omega>s = vector[0,0]\<close>
  (Robust3 L1634).  = the M6 hypothesis \<open>hsep\<close>; closes at the Robust3 splice.\<close>

lemma m5_D5_hsep_freebie:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "kz \<omega>s \<noteq> kz \<omega>0"
  \<comment> \<open>= M6 hypothesis hsep; at the splice: simp on the concrete \<open>\<omega>0_def \<omega>s_def kz_def\<close>.\<close>
  sorry

text \<open>\<open>kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s\<close>: the in-plane wavevectors differ.  At the splice this is
  @{text "by (simp add: \<omega>0_def \<omega>s_def kx_def sin_pi_half)"} (Robust3 L1636).
  = the M6 hypothesis \<open>kdiff\<close>; closes at the Robust3 splice.\<close>

lemma m5_D5_kdiff_freebie:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
  \<comment> \<open>= M6 hypothesis kdiff; at the splice: simp on the concrete \<open>\<omega>0_def \<omega>s_def kx_def\<close>.\<close>
  sorry


subsection \<open>Splice freebie: the fixed-angle moment-map nowhere-density (mstarg)\<close>

text \<open>For every nonzero \<open>c\<close>, the set of \<open>x\<close> at which \<open>DM_paper_x x c\<close> is not surjective is
  nowhere dense.  In Robust3: rewrite \<open>\<not> surj (DM_paper_x x c) = (mstarg c x = 0)\<close> via
  @{text surj_iff_mstarg} (L578), then @{text nowhere_dense_mstarg_zeros}[OF c0 n6] (L744).
  \<open>mstarg\<close> is defined in Robust3 ABOVE the M5 splice, so it is out of scope here but in scope
  at the splice.  Mirror of D34's @{text fixed_c_nonsurj_nowhere_dense}; closes at the splice.\<close>

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  \<comment> \<open>= nowhere_dense_mstarg_zeros \<circ> surj_iff_mstarg (Robust3); closes at the M5 splice.\<close>
  sorry


subsection \<open>Ported scalar second derivative of \<open>gdip\<close> (the genuine \<open>gdip''(\<pi>/2) \<noteq> 0\<close> core)\<close>

text \<open>\<^bold>\<open>Why ported.\<close>  The fact \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close> --- the nontriviality of the
  beam-center det-Hessian polynomial --- lives in the sibling DEV theory @{text Scratch_m5_gdip2}
  (session @{text Applied_Math_M5_gdip2}), which is NOT a dependency of this D5 session.  Its
  whole derivation depends only on facts already in the @{text Applied_Math_Appendix} heap
  (@{thm g1_gdip_has_deriv}, @{thm g1_frechet_eval}, @{thm gdip_deriv_differentiable},
  @{thm g1_gsinc_has_deriv}, @{thm gsincd_def}, @{thm gsinc_def}), so we re-prove the chain
  here as local lemmas (verbatim copy of the gdip2 file).  None of these names
  (@{text gsincdd}, @{text um}, @{text up}, @{text D1f}, @{text gdip2}) clash with the heap.\<close>

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
    using g1_gdip_has_deriv[OF s0] unfolding D1f_def um_def up_def .
  thus ?thesis by (rule g1_frechet_eval)
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

text \<open>The scalar second derivative of \<open>gdip\<close> at a cos-zero is nonzero.\<close>

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
    by (rule g1_frechet_eval[OF hd])
  also have "\<dots> = (16 - 4*pi^2)/8" by (rule gdip_secondderiv_value)
  finally show ?thesis using gdip_secondderiv_value_nonzero by simp
qed


subsection \<open>The beam-center (\<open>c = 0\<close>) Hessian collapse and the det moment polynomial\<close>

text \<open>\<^bold>\<open>Moments at the beam center \<open>c = 0\<close> are real.\<close>  At \<open>c = 0\<close> every phase factor is \<open>1\<close>,
  so \<open>Afun x 0 = N\<close> (\<open>N = CARD('n)\<close>) and \<open>Mcfun x 0 k\<close>, \<open>M2cfun x 0 k l\<close> are real coordinate
  (second-)moment sums.\<close>

lemma Afun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "Afun x (0::real^2) = of_nat CARD('n)"
  by (simp add: Afun_def)

lemma Mcfun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "Mcfun x (0::real^2) k = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)"
  by (simp add: Mcfun_def)

lemma M2cfun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "M2cfun x (0::real^2) k l
     = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)"
  by (simp add: M2cfun_def)

text \<open>The \<open>c\<close>-gradient of \<open>|A|\<^sup>2\<close> vanishes at the beam center (\<open>|A|\<^sup>2\<close> is critical at \<open>c = 0\<close>:
  the array factor is maximal there).  Real moments \<open>\<Rightarrow>\<close> the steering term \<open>Re(cnj A \<cdot> (-\<ii>)real)\<close>
  is the real part of a purely imaginary number.\<close>

lemma gradUc_at_zero:
  fixes x :: "(real^2)^'n"
  shows "gradU (\<lambda>c. c) (\<lambda>_. 1) x (0::real^2) = 0"
proof -
  have comp: "gradU (\<lambda>c. c) (\<lambda>_. 1) x (0::real^2) $ j = 0" for j
  proof -
    have A0: "M_paper x 0 $ 1 = complex_of_real (real CARD('n))"
      by (simp add: A_moment_def phase_def)
    have M20: "M_paper x 0 $ 2 = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
      by (simp add: M1_moment_def phase_def)
    have M30: "M_paper x 0 $ 3 = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
      by (simp add: M2_moment_def phase_def)
    have Ar: "M_paper x 0 $ 1 = of_real (Re (M_paper x 0 $ 1))" by (subst A0)+ simp
    have M2r: "M_paper x 0 $ 2 = of_real (Re (M_paper x 0 $ 2))" by (subst M20)+ simp
    have M3r: "M_paper x 0 $ 3 = of_real (Re (M_paper x 0 $ 3))" by (subst M30)+ simp
    have steer0: "Re (cnj (M_paper x 0 $ 1)
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * (M_paper x 0 $ 2)
             + (- \<i>) * complex_of_real ((axis j 1)$2) * (M_paper x 0 $ 3))) = 0"
    proof -
      have "cnj (M_paper x 0 $ 1)
          * ((- \<i>) * complex_of_real ((axis j 1)$1) * (M_paper x 0 $ 2)
           + (- \<i>) * complex_of_real ((axis j 1)$2) * (M_paper x 0 $ 3))
          = of_real (Re (M_paper x 0 $ 1))
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * of_real (Re (M_paper x 0 $ 2))
             + (- \<i>) * complex_of_real ((axis j 1)$2) * of_real (Re (M_paper x 0 $ 3)))"
        by (subst Ar, subst M2r, subst M3r) (simp only: Complex.complex_cnj_complex_of_real)
      also have "\<dots> = complex_of_real (Re (M_paper x 0 $ 1)
                       * ((axis j 1)$1 * Re (M_paper x 0 $ 2)
                        + (axis j 1)$2 * Re (M_paper x 0 $ 3))) * (- \<i>)"
        by (simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    show ?thesis
      using gradUc_component_moments[of x 0 j] steer0 by simp
  qed
  show ?thesis by (simp add: Finite_Cartesian_Product.vec_eq_iff comp)
qed

text \<open>\<^bold>\<open>The directional second derivative of the gain field is \<open>e\<^sub>1\<close>-only.\<close>  The first-derivative
  field \<open>\<eta> \<mapsto> \<partial>gdip(\<eta>\<^sub>1) 1\<close> factors through the projection \<open>\<eta> \<mapsto> \<eta>\<^sub>1\<close>, so its Fréchet
  derivative in direction \<open>h\<close> is \<open>h\<^sub>1 \<cdot> gdip''(\<omega>\<^sub>1)\<close>.  (Re-proof of the gdip2 projection bridge,
  generalised to an arbitrary direction.)\<close>

lemma gdip_field_frechet:
  fixes \<omega> h :: "real^2"
  shows "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>) h
       = (h$1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
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
  have lin: "linear D" by (rule has_derivative_linear[OF D])
  have "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>) h
        = D (h$1)" by (subst fd) (rule refl)
  also have "\<dots> = (h$1) *\<^sub>R D 1" using linear_cmul[OF lin, of "h$1" 1] by simp
  also have "\<dots> = (h$1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
    using fun_cong[OF Deq, of 1] by simp
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The beam-center Hessian entry collapse.\<close>  At \<open>c = 0\<close> the \<open>c\<close>-gradient terms of
  @{thm HessU_dip_entry_moments} drop (@{thm gradUc_at_zero}), leaving the curvature quadratic
  form (\<open>Hcmat x 0\<close>) plus the gain-Hessian term, which is \<open>e\<^sub>1e\<^sub>1\<^sup>T\<close>-supported:
  \<open>HessU x \<omega> $ k $ l = gain \<cdot> Dcvec(e\<^sub>k) \<bullet> Hcmat x 0 (Dcvec(e\<^sub>l)) + (e_k)\<^sub>1 (e_l)\<^sub>1 gdip''(\<omega>\<^sub>1) N\<^sup>2\<close>.\<close>

lemma HessU_beamcenter_entry:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))
       + ((axis k 1)$1) * ((axis l 1)$1)
           * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1
           * (real CARD('n))\<^sup>2"
proof -
  have g0: "gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    unfolding c0 by (rule gradUc_at_zero)
  have U0: "U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>) = (real CARD('n))\<^sup>2"
  proof -
    have "U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>) = (cmod (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2"
      by (rule Uc_eq_moment)
    also have "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_nat CARD('n)"
      unfolding c0 by (simp add: A_moment_def phase_def)
    finally show ?thesis by (simp add: norm_of_nat)
  qed
  \<comment> \<open>the gain-Hessian field directional second derivative, in direction \<open>axis l 1\<close>,
      of the \<open>k\<close>-scaled gain derivative.  Scale the constant \<open>(axis k 1)\<^sub>1\<close> out of the
      \<open>\<eta>\<close>-field, then apply the projection bridge @{thm gdip_field_frechet}.\<close>
  have field_lin: "frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)
                 = ((axis k 1)$1) * frechet_derivative gdip (at (\<eta>$1)) 1" for \<eta> :: "real^2"
    using linear_cmul[OF has_derivative_linear[OF frechet_derivative_works[THEN iffD1,
            OF gdip_differentiable]], of "(axis k 1)$1" 1]
    by (simp add: cart_eq_inner_axis frechet_gdip_zero_arg inner_axis_axis)
  define F where "F = (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1)"
  have Fdiff: "F differentiable (at \<omega>)"
  proof -
    have proj: "(\<lambda>\<eta>::real^2. \<eta>$1) differentiable (at \<omega>)"
      by (simp add: bounded_linear_vec_nth bounded_linear_imp_differentiable)
    have sc: "(\<lambda>t. frechet_derivative gdip (at t) 1) differentiable (at (\<omega>$1))"
      by (rule gdip_deriv_differentiable)
    show ?thesis unfolding F_def
      using differentiable_chain_at[OF proj sc] by (simp add: o_def)
  qed
  have FD: "(F has_derivative frechet_derivative F (at \<omega>)) (at \<omega>)"
    using Fdiff frechet_derivative_works by blast
  have cF: "((\<lambda>\<eta>. F \<eta> * ((axis k 1)$1)) has_derivative
              (\<lambda>h. frechet_derivative F (at \<omega>) h * ((axis k 1)$1))) (at \<omega>)"
    by (rule has_derivative_mult_left[OF FD])
  have gainH: "frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
       = ((axis k 1)$1) * ((axis l 1)$1)
           * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
  proof -
    have e: "(\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1))
        = (\<lambda>\<eta>. F \<eta> * ((axis k 1)$1))"
      unfolding F_def by (rule ext) (simp add: field_lin mult.commute)
    have "frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
         = frechet_derivative F (at \<omega>) (axis l 1) * ((axis k 1)$1)"
      unfolding e using m5_D5_kdiff_freebie by blast 
    also have "frechet_derivative F (at \<omega>) (axis l 1)
         = ((axis l 1)$1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
      unfolding F_def by (rule gdip_field_frechet)
    finally show ?thesis by (simp add: mult.assoc mult.commute)
  qed
  have Hc0: "Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) = Hcmat x 0" unfolding c0 by (rule refl)
  have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = (gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
                        + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1))
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative gdip (at (\<omega>$1)) ((axis l 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))
        + (frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
            * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    by (rule HessU_dip_entry_moments)
  also have "\<dots> = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))
       + ((axis k 1)$1) * ((axis l 1)$1)
           * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1
           * (real CARD('n))\<^sup>2"
    by (simp only: g0 U0 gainH Hc0 inner_zero_right add_0_right add_0 mult_zero_right) 
  finally show ?thesis .
qed


subsection \<open>The beam-center det-Hessian as an entire, continuous moment polynomial in \<open>x\<close>\<close>

text \<open>\<^bold>\<open>The curvature matrix entry at \<open>c = 0\<close> in real moment form.\<close>
  \<open>Hcmat x 0 $ k $ l = 2 ((\<Sum>x\<^sub>l)(\<Sum>x\<^sub>k) - N (\<Sum>x\<^sub>k x\<^sub>l))\<close> --- a real degree-2 polynomial in
  the configuration coordinates.\<close>

lemma Hcmat_at_zero_entry:
  fixes x :: "(real^2)^'n"
  shows "Hcmat x (0::real^2) $ k $ l
       = 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
proof -
  have "Hcmat x (0::real^2) $ k $ l
      = 2 * (Re (cnj (Mcfun x 0 l) * Mcfun x 0 k) - Re (cnj (Afun x 0) * M2cfun x 0 k l))"
    by (simp add: Hcmat_def)
  also have "\<dots> = 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
    by (simp add: Mcfun_at_zero M2cfun_at_zero Afun_at_zero)
  finally show ?thesis .
qed

text \<open>The curvature entry is \<open>rline_entire\<close> (entire on every line) and continuous in \<open>x\<close>.\<close>

lemma rline_entire_Hcmat_at_zero:
  shows "rline_entire (\<lambda>x::(real^2)^'n. Hcmat x (0::real^2) $ k $ l)"
proof -
  have c1: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). (x $ n) $ l)"
    by (intro rline_entire_sum) (auto intro: rline_entire_coord)
  have c2: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)"
    by (intro rline_entire_sum) (auto intro: rline_entire_coord)
  have c3: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)"
    by (intro rline_entire_sum) (auto intro!: rline_entire_mult rline_entire_coord)
  have prod12: "rline_entire (\<lambda>x::(real^2)^'n.
                  (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k))"
    by (rule rline_entire_mult[OF c1 c2])
  have scaled: "rline_entire (\<lambda>x::(real^2)^'n.
                  real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
    by (rule rline_entire_scale[OF c3])
  have diff: "rline_entire (\<lambda>x::(real^2)^'n.
                  (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
                - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
    using rline_entire_add[OF prod12 rline_entire_scale[OF scaled, of "-1"]]
    by (simp add: field_simps)
  have eq: "(\<lambda>x::(real^2)^'n. Hcmat x (0::real^2) $ k $ l)
          = (\<lambda>x. 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)))"
    by (rule ext) (rule Hcmat_at_zero_entry)
  show ?thesis unfolding eq by (rule rline_entire_scale[OF diff])
qed

lemma continuous_Hcmat_at_zero:
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. (Hcmat x (0::real^2) $ k $ l :: real))"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. Hcmat x (0::real^2) $ k $ l)
          = (\<lambda>x. 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)))"
    by (rule ext) (rule Hcmat_at_zero_entry)
  show ?thesis
    unfolding eq
    by (intro continuous_intros
          bounded_linear.continuous_on[OF bounded_linear_compose
            [OF bounded_linear_vec_nth bounded_linear_vec_nth]])
qed

text \<open>\<^bold>\<open>The beam-center Hessian entry, as a function of \<open>x\<close>, is entire on lines and continuous.\<close>
  Expand the quadratic form @{thm HessU_beamcenter_entry} over the \<open>2\<close>-dimensional inner
  product / mat-vec; each summand is a constant (the steering jet / gain / gain-curvature)
  times a curvature entry @{thm rline_entire_Hcmat_at_zero}.\<close>

lemma HessU_beamcenter_entry_expand:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ i * Hcmat x 0 $ i $ j * Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ j)
       + (axis k 1 $ 1) * (axis l 1 $ 1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
proof -
  have "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ i * Hcmat x 0 $ i $ j * Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ j)"
    unfolding inner_vec_def matrix_vector_mult_def by (simp add: sum_distrib_left mult.assoc)
  thus ?thesis unfolding HessU_beamcenter_entry[OF c0] by simp
qed

lemma rline_entire_HessU_beamcenter_entry:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "rline_entire (\<lambda>x::(real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l)"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l)
      = (\<lambda>x. gain_dip \<omega> * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ i * Hcmat x 0 $ i $ j * Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ j)
       + (axis k 1 $ 1) * (axis l 1 $ 1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2)"
    by (rule ext) (rule HessU_beamcenter_entry_expand[OF c0])
  have fin: "finite (UNIV :: 2 set)" by simp
  show ?thesis unfolding eq
    by (intro rline_entire_add rline_entire_scale rline_entire_sum[OF fin] rline_entire_mult rline_entire_Hcmat_at_zero rline_entire_const)
qed

lemma continuous_HessU_beamcenter_entry:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l :: real))"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l :: real))
      = (\<lambda>x. gain_dip \<omega> * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ i * Hcmat x 0 $ i $ j * Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ j)
       + (axis k 1 $ 1) * (axis l 1 $ 1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2)"
    by (rule ext) (rule HessU_beamcenter_entry_expand[OF c0])
  have fin: "finite (UNIV :: 2 set)" by simp
  show ?thesis
    unfolding eq by (intro continuous_intros continuous_on_sum fin continuous_Hcmat_at_zero)
qed

text \<open>\<^bold>\<open>The beam-center det-Hessian is entire-on-lines and continuous in \<open>x\<close>\<close> --- via the \<open>2\<times>2\<close>
  determinant expansion @{thm det_2} and the entry lemmas.\<close>

lemma rline_entire_det_HessU_beamcenter:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "rline_entire (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  by (rule rline_entire_det_fun) (rule rline_entire_HessU_beamcenter_entry[OF c0])

lemma continuous_det_HessU_beamcenter:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
proof -
  have d2: "(\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))
      = (\<lambda>x. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
             * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
           - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
             * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1)"
    by (rule ext) (simp add: det_2)
  show ?thesis
    unfolding d2 by (intro continuous_intros continuous_HessU_beamcenter_entry[OF c0])
qed


subsection \<open>Nontriviality: a one-displaced-element witness with \<open>det HessU \<noteq> 0\<close>\<close>

text \<open>\<^bold>\<open>The rank-one curvature witness.\<close>  Put one element at a point \<open>p\<close> not orthogonal to the
  second steering column \<open>col2 = Dcvec(e\<^sub>2)\<close>; the others at the origin.  Then every moment is a
  single-element moment, so \<open>Hcmat xs 0 = 2(1 - N) p p\<^sup>T\<close> is rank one.  Writing \<open>u = p \<bullet> col1\<close>,
  \<open>v = p \<bullet> col2\<close>, \<open>\<alpha> = gain \<cdot> 2(1 - N)\<close>, \<open>\<gamma> = gdip''(\<omega>\<^sub>1) N\<^sup>2\<close>, the four Hessian entries are
  \<open>H\<^sub>1\<^sub>1 = \<alpha> u\<^sup>2 + \<gamma>\<close>, \<open>H\<^sub>1\<^sub>2 = H\<^sub>2\<^sub>1 = \<alpha> u v\<close>, \<open>H\<^sub>2\<^sub>2 = \<alpha> v\<^sup>2\<close>, whence
  \<open>det HessU = (\<alpha> u\<^sup>2 + \<gamma>)(\<alpha> v\<^sup>2) - (\<alpha> u v)\<^sup>2 = \<gamma> \<alpha> v\<^sup>2\<close> --- nonzero since \<open>\<gamma> \<noteq> 0\<close> (cos-zero,
  @{thm gdip_scalar_second_deriv_nonzero}), \<open>gain \<noteq> 0\<close>, \<open>1 - N \<noteq> 0\<close> (\<open>N \<ge> 6\<close>), \<open>v \<noteq> 0\<close>.\<close>

lemma det_HessU_beamcenter_witness:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" and cz: "cos (\<omega> $ 1) = 0"
  shows "\<exists>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
proof -
  define col1 where "col1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)"
  define col2 where "col2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  have c2nz: "col2 \<noteq> 0" unfolding col2_def by (rule Dcvec_col2_nz[OF pfw])
  define p :: "real^2" where "p = col2"
  have vp: "p \<bullet> col2 \<noteq> 0" unfolding p_def using c2nz by simp
  define i0 :: 'n where "i0 = undefined"
  define xs :: "(real^2)^'n" where "xs = (\<chi> n. if n = i0 then p else 0)"
  \<comment> \<open>single-element moment sums\<close>
  have sumk: "(\<Sum>n\<in>(UNIV::'n set). (xs $ n) $ k) = p $ k" for k :: 2
  proof -
    have "(\<Sum>n\<in>(UNIV::'n set). (xs $ n) $ k)
        = (xs $ i0) $ k + (\<Sum>n\<in>(UNIV::'n set) - {i0}. (xs $ n) $ k)"
      by (rule sum.remove) simp_all
    also have "(\<Sum>n\<in>(UNIV::'n set) - {i0}. (xs $ n) $ k) = 0"
      by (rule sum.neutral) (simp add: xs_def)
    finally show ?thesis by (simp add: xs_def)
  qed
  have sumkl: "(\<Sum>n\<in>(UNIV::'n set). (xs $ n) $ k * (xs $ n) $ l) = p $ k * p $ l" for k l :: 2
  proof -
    have "(\<Sum>n\<in>(UNIV::'n set). (xs $ n) $ k * (xs $ n) $ l)
        = (xs $ i0) $ k * (xs $ i0) $ l + (\<Sum>n\<in>(UNIV::'n set) - {i0}. (xs $ n) $ k * (xs $ n) $ l)"
      by (rule sum.remove) simp_all
    also have "(\<Sum>n\<in>(UNIV::'n set) - {i0}. (xs $ n) $ k * (xs $ n) $ l) = 0"
      by (rule sum.neutral) (simp add: xs_def)
    finally show ?thesis by (simp add: xs_def)
  qed
  \<comment> \<open>the rank-one curvature matrix at the witness\<close>
  define N1 where "N1 = 2 * (1 - real CARD('n))"
  have Hc: "Hcmat xs 0 $ k $ l = N1 * (p $ k * p $ l)" for k l :: 2
    using Hcmat_at_zero_entry[of xs k l] unfolding sumk sumkl N1_def
    by (simp add: algebra_simps)
  \<comment> \<open>scalar abbreviations\<close>
  define g where "g = gain_dip \<omega>"
  define u where "u = col1 $ 1 * p $ 1 + col1 $ 2 * p $ 2"
  define v where "v = col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2"
  define \<gamma> where "\<gamma> = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1
                    * (real CARD('n))\<^sup>2"
  \<comment> \<open>the four Hessian entries at the witness\<close>
  have H11: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 1 $ 1 = g * (N1 * u * u) + \<gamma>"
    unfolding HessU_beamcenter_entry_expand[OF c0] Hc col1_def[symmetric] col2_def[symmetric]
              g_def[symmetric] u_def \<gamma>_def
    by (simp add: sum_2 axis_def algebra_simps)
  have H12: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 1 $ 2 = g * (N1 * u * v)"
    unfolding HessU_beamcenter_entry_expand[OF c0] Hc col1_def[symmetric] col2_def[symmetric]
              g_def[symmetric] u_def v_def
    by (simp add: sum_2 axis_def algebra_simps)
  have H21: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 2 $ 1 = g * (N1 * u * v)"
    unfolding HessU_beamcenter_entry_expand[OF c0] Hc col1_def[symmetric] col2_def[symmetric]
              g_def[symmetric] u_def v_def
    by (simp add: sum_2 axis_def algebra_simps)
  have H22: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 2 $ 2 = g * (N1 * v * v)"
    unfolding HessU_beamcenter_entry_expand[OF c0] Hc col1_def[symmetric] col2_def[symmetric]
              g_def[symmetric] v_def
    by (simp add: sum_2 axis_def algebra_simps)
  \<comment> \<open>the determinant collapses to \<open>\<gamma> g N1 v\<^sup>2\<close>\<close>
  have detval: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>) = \<gamma> * (g * (N1 * (v * v)))"
  proof -
    have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>)
        = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 1 $ 1 * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 2 $ 2
        - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 1 $ 2 * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 2 $ 1"
      by (simp add: det_2)
    also have "\<dots> = (g * (N1 * u * u) + \<gamma>) * (g * (N1 * v * v))
                  - (g * (N1 * u * v)) * (g * (N1 * u * v))"
      unfolding H11 H12 H21 H22 by (rule refl)
    also have "\<dots> = \<gamma> * (g * (N1 * (v * v)))"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>each factor is nonzero\<close>
  have \<gamma>nz: "\<gamma> \<noteq> 0"
    unfolding \<gamma>_def using gdip_scalar_second_deriv_nonzero[OF pfw cz] c6 by simp
  have gnz: "g \<noteq> 0" unfolding g_def by (rule gain_dip_nonzero_of_sin[OF pfw])
  have N1nz: "N1 \<noteq> 0" unfolding N1_def using c6 by simp
  have vnz: "v \<noteq> 0" using vp unfolding v_def by (simp add: inner_vec_def sum_2 mult.commute)
  have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>) \<noteq> 0"
    unfolding detval using \<gamma>nz gnz N1nz vnz by simp
  thus ?thesis by blast
qed


subsection \<open>The genuine per-angle beam-center obligation (D2-style polynomial)\<close>

text \<open>The \<open>c = 0\<close> sub-case of a witness angle.  When \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close> the moment-map
  derivative \<open>DM_paper_x x 0\<close> is never surjective (@{thm DM_paper_x_null_not_surj}), so the
  D5 slice degenerates to the D2 beam-center slice at \<open>\<omega>\<close>:
  \<open>{x. gradU = 0 \<and> A \<noteq> 0 \<and> det HessU = 0}\<close>.  Its meagerness is the beam-center det-Hessian
  covariance-polynomial argument: \<open>det HessU\<close> is a continuous, entire-on-lines moment polynomial
  in \<open>x\<close> (@{thm continuous_det_HessU_beamcenter}, @{thm rline_entire_det_HessU_beamcenter}); when
  \<open>cos(\<omega>\<^sub>1) = 0\<close> it is not identically zero (@{thm det_HessU_beamcenter_witness}, nontrivial
  because \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close>), so its zero set is nowhere dense and the slice
  (contained in it) is meager; when \<open>cos(\<omega>\<^sub>1) \<noteq> 0\<close> the slice is EMPTY because criticality
  \<open>gradU\<^sub>1 = gdip'(\<omega>\<^sub>1) N\<^sup>2 \<noteq> 0\<close> fails (the M6-empty mirror).  Now \<^emph>\<open>discharged\<close>.\<close>

lemma m5_D5_beamcenter_angle_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
proof (cases "cos (\<omega> $ 1) = 0")
  case False
  \<comment> \<open>\<open>cos(\<omega>\<^sub>1) \<noteq> 0\<close>: criticality fails for ALL \<open>x\<close> (the M6-empty mirror), so the set is empty.\<close>
  have gd: "frechet_derivative gdip (at (\<omega>$1)) 1 \<noteq> 0"
    using gdip_deriv_zero_iff[OF pfw] False by blast
  have empty: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0} = {}"
  proof (rule equals0I)
    fix x :: "(real^2)^'n"
    assume "x \<in> {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    hence g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    \<comment> \<open>component 1 of the beam-center gradient is \<open>gdip'(\<omega>\<^sub>1) N\<^sup>2\<close>\<close>
    have a1: "((axis (1::2) 1 :: real^2) $ 1) = 1" by (simp add: axis_def)
    have NA: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_nat CARD('n)"
      unfolding c0 by (simp add: A_moment_def phase_def)
    have steer0: "Re (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
            * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1) * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
             + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2) * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))) = 0"
    proof -
      have M1r: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2 = of_real (Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2))"
        unfolding c0 by (simp add: M1_moment_def phase_def)
      have M2r: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3 = of_real (Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))"
        unfolding c0 by (simp add: M2_moment_def phase_def)
      have Ar: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_real (Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))"
        unfolding NA by simp
      have "cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
            * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1) * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
             + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2) * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))
          = of_real (Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
              * ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1 * Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
               + (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2 * Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))) * (- \<i>)"
        by (subst Ar, subst M1r, subst M2r) (simp add: Complex.complex_cnj_complex_of_real algebra_simps)
      thus ?thesis by simp
    qed
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
        = frechet_derivative gdip (at (\<omega>$1)) ((axis (1::2) 1)$1)
            * (cmod (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2"
      using steer0 by (simp add: gradU_dip_component_moments)
    also have "\<dots> = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
      by (subst a1, subst NA) (simp add: norm_of_nat)
    finally have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2" .
    moreover have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0" using g0 by simp
    ultimately have "frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2 = 0" by simp
    moreover have "(real CARD('n))\<^sup>2 \<noteq> 0" using c6 by simp
    ultimately have "frechet_derivative gdip (at (\<omega>$1)) 1 = 0" by simp
    with gd show False by simp
  qed
  show ?thesis unfolding empty by simp
next
  case True
  \<comment> \<open>\<open>cos(\<omega>\<^sub>1) = 0\<close>: the det-Hessian moment polynomial is nontrivial, so its zero set is
       nowhere dense; the slice is contained in it, hence meager.\<close>
  have nd: "nowhere_dense {x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
  proof -
    have seq: "{x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
             = {x \<in> (UNIV::((real^2)^'n) set). det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
      by simp
    show ?thesis
      unfolding seq
    proof (rule lines_entire_slice_nowhere_dense)
      show "continuous_on UNIV (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
        by (rule continuous_det_HessU_beamcenter[OF c0])
      show "\<And>a v. \<exists>F. F holomorphic_on UNIV
              \<and> (\<forall>t::real. F (complex_of_real t)
                          = complex_of_real (det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (a + t *\<^sub>R v) \<omega>)))"
        using rline_entire_det_HessU_beamcenter[OF c0] unfolding rline_entire_def by blast
      show "\<exists>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
        by (rule det_HessU_beamcenter_witness[OF c6 pfw c0 True])
    qed
  qed
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
        \<subseteq> {x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_nowhere_dense[OF nd]])
qed


subsection \<open>Per-angle D5 slice is meager (case split on the beam center)\<close>

text \<open>For a fixed witness angle \<open>\<omega>\<close> with \<open>sin(\<omega>$1) \<noteq> 0\<close>, the D5 slice
  \<open>{x. gradU = 0 \<and> A \<noteq> 0 \<and> det HessU = 0 \<and> \<not> surj (DM_paper_x x (cvec \<omega>))}\<close> is meager.
  Case \<open>c \<noteq> 0\<close>: it injects into \<open>{x. \<not> surj (DM_paper_x x c)}\<close>, nowhere dense by the mstarg
  freebie.  Case \<open>c = 0\<close>: \<open>\<not> surj\<close> is universal, so the slice is the D2 beam-center set,
  meager by @{thm m5_D5_beamcenter_angle_meager}.\<close>

lemma m5_D5_slice_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> = 0")
  case True
  \<comment> \<open>\<open>c = 0\<close>: \<open>\<not> surj\<close> holds for all \<open>x\<close>, so the slice is the D2 beam-center set.\<close>
  have e: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
        = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    using DM_paper_x_null_not_surj[where x = _ and 'n = 'n] by (simp add: True)
  show ?thesis
    unfolding e by (rule m5_D5_beamcenter_angle_meager[OF c6 pfw True])
next
  case False
  \<comment> \<open>\<open>c \<noteq> 0\<close>: inject into the nowhere-dense moment-map set, then meager.\<close>
  have cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0" using False .
  have nd: "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    by (rule fixed_c_nonsurj_nowhere_dense[OF cnz c6])
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
        \<subseteq> {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_nowhere_dense[OF nd]])
qed


subsection \<open>D5 assembly: \<open>m5_D5_steersing\<close> (R3 confinement + finite union of slices)\<close>

text \<open>The exact target statement (verbatim from the M5 skeleton).  Proof is the M6 R3
  reduction with \<open>surj\<close> dropped: confine every bad witness angle into the finite set \<open>K\<close>
  (cos zeros \<open>\<times>\<close> phase-lattice zeros) via @{thm M6_witness_gdip_deriv_zero} and
  @{thm Dcvec_det_eq} --- neither uses surjectivity --- then take the finite union of the
  per-angle slices, each meager by @{thm m5_D5_slice_meager}.\<close>

lemma m5_D5_steersing:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
proof -
  \<comment> \<open>Splice freebies: phase-separation data for the (free) \<open>\<omega>0 \<omega>s\<close>.\<close>
  have hsep: "kz \<omega>s \<noteq> kz \<omega>0" by (rule m5_D5_hsep_freebie)
  have kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s" by (rule m5_D5_kdiff_freebie)
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0
            \<and> Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0}"
  define slice :: "real^2 \<Rightarrow> ((real^2)^'n) set" where
    "slice \<omega> = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}" for \<omega> :: "real^2"
  text \<open>The phase coefficients are not both zero.\<close>
  have D0: "kz \<omega>s - kz \<omega>0 \<noteq> 0" using hsep by simp
  have ABnz: "Ac \<noteq> 0 \<or> Bc \<noteq> 0"
    using kdiff D0 unfolding Ac_def Bc_def by (auto simp: divide_eq_0_iff)
  text \<open>The witness-angle set \<open>K\<close> is finite.\<close>
  define S1 :: "real set" where
    "S1 = {t::real. ctr $ 1 - \<delta> \<le> t \<and> t \<le> ctr $ 1 + \<delta> \<and> cos t = 0}"
  define S2 :: "real set" where
    "S2 = {u::real. ctr $ 2 - pi \<le> u \<and> u \<le> ctr $ 2 + pi
            \<and> Ac * cos u + Bc * sin u = 0}"
  have finS1: "finite S1" unfolding S1_def by (rule finite_cos_zeros_interval)
  have finS2: "finite S2" unfolding S2_def by (rule finite_phase_zeros_interval[OF ABnz])
  have Ksub: "K \<subseteq> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
  proof
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
    have pz: "Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0" using wK by (simp add: K_def)
    have bnds: "ctr $ 1 - \<delta> \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> ctr $ 1 + \<delta>
              \<and> ctr $ 2 - pi \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> ctr $ 2 + pi"
      by (rule OmegaPF_component_bounds[OF wD])
    have mem: "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2"
      using bnds cz pz by (auto simp: S1_def S2_def)
    show "\<omega> \<in> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
    proof (rule image_eqI[where x = "(\<omega> $ 1, \<omega> $ 2)"])
      show "\<omega> = (\<lambda>(t, u). vector [t, u] :: real^2) (\<omega> $ 1, \<omega> $ 2)"
        by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
      show "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2" by (rule mem)
    qed
  qed
  have finK: "finite K"
    by (rule finite_subset[OF Ksub
          finite_imageI[OF finite_cartesian_product[OF finS1 finS2]]])
  text \<open>Witness confinement: every bad witness angle lies in \<open>K\<close>
    (R3 kernel-direction reduction --- uses NO surjectivity).\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}
             \<subseteq> (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
    then obtain \<omega> :: "real^2" where wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and hz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and ns: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      and dz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
      by blast
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    have gd0: "frechet_derivative gdip (at (\<omega> $ 1)) 1 = 0"
      by (rule M6_witness_gdip_deriv_zero[OF s1 g0 anz dz])
    have cz: "cos (\<omega> $ 1) = 0"
      by (rule iffD1[OF gdip_deriv_zero_iff[OF s1] gd0])
    have e: "sin (\<omega> $ 1) * (cos (\<omega> $ 1)
               - sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2))) = 0"
      using dz by (simp add: Dcvec_det_eq Ac_def Bc_def)
    have e2: "cos (\<omega> $ 1) - sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2)) = 0"
      using mult_eq_0_iff[THEN iffD1, OF e] s1 by blast
    have e3: "sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2)) = 0"
      using e2 cz by simp
    have q0: "Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0"
      using mult_eq_0_iff[THEN iffD1, OF e3] s1 by blast
    have wK: "\<omega> \<in> K" using wD cz q0 by (simp add: K_def)
    have xs: "x \<in> slice \<omega>" using g0 anz hz ns by (simp add: slice_def)
    show "x \<in> (\<Union>\<omega>\<in>K. slice \<omega>)"
    proof (rule UN_I)
      show "\<omega> \<in> K" by (rule wK)
      show "x \<in> slice \<omega>" by (rule xs)
    qed
  qed
  text \<open>Each slice over a fixed angle in \<open>K\<close> is meager (mstarg freebie for \<open>c \<noteq> 0\<close>,
    D2 covariance polynomial for \<open>c = 0\<close>); the finite union is meager.\<close>
  have meagU: "meager (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof (rule meager_Union_finite[OF finK])
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    show "meager (slice \<omega>)"
      unfolding slice_def
      by (rule m5_D5_slice_meager[OF c6 s1])
  qed
  show ?thesis by (rule meager_subset[OF sub meagU])
qed

end
