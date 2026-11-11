section \<open>Degenerate critical points at the main beam\<close>

theory Main_Beam_Stratum
  imports
    Critical_Slices
begin

subsection \<open>The Hessian at the main beam\<close>

lemma A_moment_at_zero:
  fixes x :: "(real^2)^'n"
  shows "A_moment x (0::real^2) = of_nat CARD('n)"
  by (simp add: A_moment_cis)

lemma first_moment_at_zero:
  fixes x :: "(real^2)^'n"
  shows "first_moment x (0::real^2) k = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)"
  by (simp add: first_moment_cis)

lemma second_moment_at_zero:
  fixes x :: "(real^2)^'n"
  shows "second_moment x (0::real^2) k l
     = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)"
  by (simp add: second_moment_cis)

lemma gradUc_at_zero:
  fixes x :: "(real^2)^'n"
  shows "gradU (\<lambda>c. c) (\<lambda>_. 1) x (0::real^2) = 0"
proof -
  have comp: "gradU (\<lambda>c. c) (\<lambda>_. 1) x (0::real^2) $ j = 0" for j
  proof -
    have A0: "moment_map x 0 $ 1 = complex_of_real (real CARD('n))"
      by (simp add: A_moment_def phase_def)
    have M20: "moment_map x 0 $ 2 = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
      by (simp add: first_moment_def phase_def)
    have M30: "moment_map x 0 $ 3 = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
      by (simp add: first_moment_def phase_def)
    have Ar: "moment_map x 0 $ 1 = of_real (Re (moment_map x 0 $ 1))" by (subst A0)+ simp
    have M2r: "moment_map x 0 $ 2 = of_real (Re (moment_map x 0 $ 2))" by (subst M20)+ simp
    have M3r: "moment_map x 0 $ 3 = of_real (Re (moment_map x 0 $ 3))" by (subst M30)+ simp
    have steer0: "Re (cnj (moment_map x 0 $ 1)
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * (moment_map x 0 $ 2)
             + (- \<i>) * complex_of_real ((axis j 1)$2) * (moment_map x 0 $ 3))) = 0"
    proof -
      have "cnj (moment_map x 0 $ 1)
          * ((- \<i>) * complex_of_real ((axis j 1)$1) * (moment_map x 0 $ 2)
           + (- \<i>) * complex_of_real ((axis j 1)$2) * (moment_map x 0 $ 3))
          = of_real (Re (moment_map x 0 $ 1))
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * of_real (Re (moment_map x 0 $ 2))
             + (- \<i>) * complex_of_real ((axis j 1)$2) * of_real (Re (moment_map x 0 $ 3)))"
        by (subst Ar, subst M2r, subst M3r) (simp only: Complex.complex_cnj_complex_of_real)
      also have "\<dots> = complex_of_real (Re (moment_map x 0 $ 1)
                       * ((axis j 1)$1 * Re (moment_map x 0 $ 2)
                        + (axis j 1)$2 * Re (moment_map x 0 $ 3))) * (- \<i>)"
        by (simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    show ?thesis
      using gradUc_component_moments[of x 0 j] steer0 by simp
  qed
  show ?thesis by (simp add: Finite_Cartesian_Product.vec_eq_iff comp)
qed

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
    have "U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>) = (cmod (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2"
      by (rule Uc_eq_moment)
    also have "moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_nat CARD('n)"
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
      unfolding e using frechet_derivative_at[OF cF] by metis 
    also have "frechet_derivative F (at \<omega>) (axis l 1)
         = ((axis l 1)$1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
      unfolding F_def by (rule gdip_field_frechet)
    finally show ?thesis by (simp only: mult.assoc mult.commute)
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

lemma Hcmat_at_zero_entry:
  fixes x :: "(real^2)^'n"
  shows "Hcmat x (0::real^2) $ k $ l
       = 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
proof -
  have "Hcmat x (0::real^2) $ k $ l
      = 2 * (Re (cnj (first_moment x 0 l) * first_moment x 0 k) - Re (cnj (A_moment x 0) * second_moment x 0 k l))"
    by (simp add: Hcmat_def)
  also have "\<dots> = 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
    by (simp add: first_moment_at_zero second_moment_at_zero A_moment_at_zero)
  finally show ?thesis .
qed

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

lemma rline_entire_det_HessU_beamcenter:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "rline_entire (\<lambda>x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  by (rule rline_entire_det_fun) (rule rline_entire_HessU_beamcenter_entry[OF c0])

lemma continuous_det_HessU_beamcenter:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
proof -
  have d2: "(\<lambda>x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))
      = (\<lambda>x. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
             * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
           - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
             * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1)"
    by (rule ext) (simp add: det_2)
  show ?thesis
    unfolding d2 by (intro continuous_intros continuous_HessU_beamcenter_entry[OF c0])
qed

lemma det_HessU_beamcenter_witness:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes card2: "2 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" and cz: "cos (\<omega> $ 1) = 0"
  shows "\<exists>x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
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
  have detval: "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>) = \<gamma> * (g * (N1 * (v * v)))"
  proof -
    have "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>)
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
    unfolding \<gamma>_def using gdip_scalar_second_deriv_nonzero[OF pfw cz] card2 by simp
  have gnz: "g \<noteq> 0" unfolding g_def by (rule gain_dip_nonzero_of_sin[OF pfw])
  have N1nz: "N1 \<noteq> 0" unfolding N1_def using card2 by simp
  have vnz: "v \<noteq> 0" using vp unfolding v_def by (simp add: inner_vec_def sum_2 mult.commute)
  have "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>) \<noteq> 0"
    unfolding detval using \<gamma>nz gnz N1nz vnz by simp
  thus ?thesis by blast
qed

lemma beamcenter_angle_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes card2: "2 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
proof (cases "cos (\<omega> $ 1) = 0")
  case False
  \<comment> \<open>\<open>cos(\<omega>\<^sub>1) \<noteq> 0\<close>: no configuration is critical, so the set is empty\<close>
  have gd: "frechet_derivative gdip (at (\<omega>$1)) 1 \<noteq> 0"
    using gdip_deriv_zero_iff[OF pfw] False by blast
  have empty: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0} = {}"
  proof (rule equals0I)
    fix x :: "(real^2)^'n"
    assume "x \<in> {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    hence g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    \<comment> \<open>component 1 of the beam-center gradient is \<open>gdip'(\<omega>\<^sub>1) N\<^sup>2\<close>\<close>
    have a1: "((axis (1::2) 1 :: real^2) $ 1) = 1" by (simp add: axis_def)
    have NA: "moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_nat CARD('n)"
      unfolding c0 by (simp add: A_moment_def phase_def)
    have steer0: "Re (cnj (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
            * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1) * (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
             + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2) * (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))) = 0"
    proof -
      have M1r: "moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2 = of_real (Re (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2))"
        unfolding c0 by (simp add: first_moment_def phase_def)
      have M2r: "moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3 = of_real (Re (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))"
        unfolding c0 by (simp add: first_moment_def phase_def)
      have Ar: "moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_real (Re (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))"
        unfolding NA by simp
      have "cnj (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
            * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1) * (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
             + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2) * (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))
          = of_real (Re (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
              * ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1 * Re (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
               + (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2 * Re (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))) * (- \<i>)"
        by (subst Ar, subst M1r, subst M2r) (simp add: Complex.complex_cnj_complex_of_real algebra_simps)
      thus ?thesis by simp
    qed
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
        = frechet_derivative gdip (at (\<omega>$1)) ((axis (1::2) 1)$1)
            * (cmod (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2"
      using steer0 by (simp add: gradU_dip_component_moments)
    also have "\<dots> = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
      by (subst a1, subst NA) (simp add: norm_of_nat)
    finally have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2" .
    moreover have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0" using g0 by simp
    ultimately have "frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2 = 0" by simp
    moreover have "(real CARD('n))\<^sup>2 \<noteq> 0" using card2 by simp
    ultimately have "frechet_derivative gdip (at (\<omega>$1)) 1 = 0" by simp
    with gd show False by simp
  qed
  show ?thesis unfolding empty by simp
next
  case True
  \<comment> \<open>\<open>cos(\<omega>\<^sub>1) = 0\<close>: the matrix_det-Hessian moment polynomial is nontrivial, so its zero set is
       nowhere dense; the slice is contained in it, hence meager.\<close>
  have nd: "nowhere_dense {x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
  proof -
    have seq: "{x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
             = {x \<in> (UNIV::((real^2)^'n) set). matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
      by simp
    show ?thesis
      unfolding seq
    proof (rule lines_entire_slice_nowhere_dense)
      show "continuous_on UNIV (\<lambda>x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
        by (rule continuous_det_HessU_beamcenter[OF c0])
      show "\<And>a v. \<exists>F. F holomorphic_on UNIV
              \<and> (\<forall>t::real. F (complex_of_real t)
                          = complex_of_real (matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (a + t *\<^sub>R v) \<omega>)))"
        using rline_entire_det_HessU_beamcenter[OF c0] unfolding rline_entire_def by blast
      show "\<exists>x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
        by (rule det_HessU_beamcenter_witness[OF card2 pfw c0 True])
    qed
  qed
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
        \<subseteq> {x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_nowhere_dense[OF nd]])
qed

subsection \<open>Critical points at the main beam\<close>

lemma moment_map_at_zero_A:
  fixes x :: "(real^2)^'n"
  shows "moment_map x 0 $ 1 = of_nat CARD('n)"
proof -
  have "A_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). cis 0)"
    by (simp add: A_moment_def phase_def)
  also have "\<dots> = of_nat CARD('n)" by simp
  finally show ?thesis by simp
qed

lemma moment_map_at_zero_M1:
  fixes x :: "(real^2)^'n"
  shows "moment_map x 0 $ 2 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
proof -
  have "first_moment x 0 1 = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 1) * cis 0)"
    by (simp add: first_moment_def phase_def)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 1))" by simp
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)" by simp
  finally show ?thesis by simp
qed

lemma moment_map_at_zero_M2:
  fixes x :: "(real^2)^'n"
  shows "moment_map x 0 $ 3 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
proof -
  have "first_moment x 0 2 = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 2) * cis 0)"
    by (simp add: first_moment_def phase_def)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 2))" by simp
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)" by simp
  finally show ?thesis by simp
qed

lemma moment_map_at_zero_real123:
  fixes x :: "(real^2)^'n"
  shows "moment_map x 0 $ 1 = of_real (Re (moment_map x 0 $ 1))"
    and "moment_map x 0 $ 2 = of_real (Re (moment_map x 0 $ 2))"
    and "moment_map x 0 $ 3 = of_real (Re (moment_map x 0 $ 3))"
proof -
  have e1: "moment_map x 0 $ 1 = of_real (real CARD('n))"
    using moment_map_at_zero_A[of x] by (metis of_real_of_nat_eq)
  have e2: "moment_map x 0 $ 2 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
    by (rule moment_map_at_zero_M1)
  have e3: "moment_map x 0 $ 3 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
    by (rule moment_map_at_zero_M2)
  show "moment_map x 0 $ 1 = of_real (Re (moment_map x 0 $ 1))"
    by (subst e1)+ simp
  show "moment_map x 0 $ 2 = of_real (Re (moment_map x 0 $ 2))"
    by (subst e2)+ simp
  show "moment_map x 0 $ 3 = of_real (Re (moment_map x 0 $ 3))"
    by (subst e3)+ simp
qed

lemma gradU_at_beamcenter_component:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
       = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
           * (cmod (moment_map x 0 $ 1))\<^sup>2"
proof -
  define A where "A = moment_map x 0 $ 1"
  define M2 where "M2 = moment_map x 0 $ 2"
  define M3 where "M3 = moment_map x 0 $ 3"
  define dj1 where "dj1 = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1"
  define dj2 where "dj2 = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2"
  have Ar: "A = of_real (Re A)" unfolding A_def by (rule moment_map_at_zero_real123(1))
  have M2r: "M2 = of_real (Re M2)" unfolding M2_def by (rule moment_map_at_zero_real123(2))
  have M3r: "M3 = of_real (Re M3)" unfolding M3_def by (rule moment_map_at_zero_real123(3))
  text \<open>The steering term: \<open>Re(cnj A \<cdot> ((-\<ii>) dj1 M2 + (-\<ii>) dj2 M3))\<close> is the real
    part of a purely-imaginary complex number, hence zero.\<close>
  have steer0: "Re (cnj A * ((- \<i>) * complex_of_real dj1 * M2
                            + (- \<i>) * complex_of_real dj2 * M3)) = 0"
  proof -
    have "cnj A * ((- \<i>) * complex_of_real dj1 * M2 + (- \<i>) * complex_of_real dj2 * M3)
        = of_real (Re A) * ((- \<i>) * complex_of_real dj1 * of_real (Re M2)
                          + (- \<i>) * complex_of_real dj2 * of_real (Re M3))"
      using Ar M2r M3r by (metis Complex.complex_cnj_complex_of_real)
    also have "\<dots> = complex_of_real (Re A * (dj1 * Re M2 + dj2 * Re M3)) * (- \<i>)"
      by (simp add: algebra_simps)
    finally have "cnj A * ((- \<i>) * complex_of_real dj1 * M2 + (- \<i>) * complex_of_real dj2 * M3)
                = complex_of_real (Re A * (dj1 * Re M2 + dj2 * Re M3)) * (- \<i>)" .
    thus ?thesis by simp
  qed
  have base: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
       = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
             * (cmod (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2
           + gain_dip \<omega> * (2 * Re (cnj (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
                * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1)
                     * (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
                 + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                     * (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))))"
    by (rule gradU_dip_component_moments)
  show ?thesis
    unfolding base c0
    using steer0 unfolding A_def M2_def M3_def dj1_def dj2_def by simp
qed

lemma gradU_at_beamcenter_comp1:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
       = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
proof -
  have a1: "((axis (1::2) 1 :: real^2) $ 1) = 1" by (simp add: axis_def)
  have NA: "cmod (moment_map x 0 $ 1) = real CARD('n)"
    using moment_map_at_zero_A[of x] by (simp add: norm_of_nat)
  have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
       = frechet_derivative gdip (at (\<omega>$1)) ((axis (1::2) 1)$1)
           * (cmod (moment_map x 0 $ 1))\<^sup>2"
    by (rule gradU_at_beamcenter_component[OF c0, of x 1])
  also have "\<dots> = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
    by (subst a1, subst NA, rule refl)
  finally show ?thesis .
qed

lemma beamcenter_critical_cos_zero:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes s1: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
    and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "cos (\<omega> $ 1) = 0"
proof -
  have Npos: "(0::real) < real CARD('n)" by simp
  have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0" using g0 by simp
  hence "frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2 = 0"
    using gradU_at_beamcenter_comp1[OF c0, of x] by simp
  hence gd0: "frechet_derivative gdip (at (\<omega>$1)) 1 = 0"
    using Npos by simp
  show ?thesis by (rule iffD1[OF gdip_deriv_zero_iff[OF s1] gd0])
qed

lemma beamcenter_K_finite:
  fixes ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  shows "finite {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  \<comment> \<open>At \<open>cos(\<omega>\<^sub>1)=0\<close> (so \<open>kz \<omega>=0\<close>,
      \<open>sin(\<omega>\<^sub>1)=\<plusminus>1\<close>) the two scalar equations \<open>cvec\<^sub>1=cvec\<^sub>2=0\<close> read
      \<open>sin(\<omega>\<^sub>1)\<cdot>cos(\<omega>\<^sub>2)=P\<close>, \<open>sin(\<omega>\<^sub>1)\<cdot>sin(\<omega>\<^sub>2)=Q\<close> with constants
      \<open>P=kx \<omega>s+Ac\<cdot>kz \<omega>s\<close>, \<open>Q=ky \<omega>s+Bc\<cdot>kz \<omega>s\<close> (\<open>Ac,Bc\<close> the usual ratios).
      Eliminating \<open>sin(\<omega>\<^sub>1)\<close> gives the phase relation \<open>Q\<cdot>cos(\<omega>\<^sub>2)-P\<cdot>sin(\<omega>\<^sub>2)=0\<close>;
      if \<open>P=Q=0\<close> the locus is empty (forces \<open>cos\<^sup>2+sin\<^sup>2=0\<close>), else the phase
      relation has finitely many \<open>\<omega>\<^sub>2\<close> in the box (@{thm finite_phase_zeros_interval});
      \<open>cos(\<omega>\<^sub>1)=0\<close> pins \<open>\<omega>\<^sub>1\<close> to a finite set (@{thm finite_cos_zeros_interval}).\<close>
proof -
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define P :: real where "P = kx \<omega>s + Ac * kz \<omega>s"
  define Q :: real where "Q = ky \<omega>s + Bc * kz \<omega>s"
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  \<comment> \<open>The two scalar beam-center equations at \<open>cos(\<omega>\<^sub>1)=0\<close>.\<close>
  have eqs: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P \<and> sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
    if cz: "cos (\<omega> $ 1) = 0" and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" for \<omega> :: "real^2"
  proof -
    have kzw: "kz \<omega> = 0" using cz by (simp add: kz_def)
    have c1: "cvec_dip \<omega>0 \<omega>s \<omega> $ 1 = 0" and c2: "cvec_dip \<omega>0 \<omega>s \<omega> $ 2 = 0"
      using c0 by simp_all
    have e1: "(kx \<omega> - kx \<omega>s) + Ac * (kz \<omega> - kz \<omega>s) = 0"
      using c1 unfolding cvec_dip_def Ac_def by (simp add: axis_def)
    have e2: "(ky \<omega> - ky \<omega>s) + Bc * (kz \<omega> - kz \<omega>s) = 0"
      using c2 unfolding cvec_dip_def Bc_def by (simp add: axis_def)
    have p1: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P"
      using e1 kzw unfolding P_def kx_def by (simp add: algebra_simps)
    have p2: "sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
      using e2 kzw unfolding Q_def ky_def by (simp add: algebra_simps)
    show ?thesis using p1 p2 by blast
  qed
  \<comment> \<open>The \<open>\<omega>\<^sub>1\<close> coordinate ranges over the finite cos-zero set inside the box.\<close>
  define S1 :: "real set" where
    "S1 = {t::real. ctr $ 1 - \<delta> \<le> t \<and> t \<le> ctr $ 1 + \<delta> \<and> cos t = 0}"
  have finS1: "finite S1" unfolding S1_def by (rule finite_cos_zeros_interval)
  show ?thesis
  proof (cases "P = 0 \<and> Q = 0")
    case True
    \<comment> \<open>\<open>P=Q=0\<close>: any witness forces \<open>cos(\<omega>\<^sub>2)=sin(\<omega>\<^sub>2)=0\<close>, impossible; \<open>K\<close> is empty.\<close>
    have "K = {}"
    proof (rule ccontr)
      assume "K \<noteq> {}"
      then obtain \<omega> :: "real^2" where wK: "\<omega> \<in> K" by blast
      have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
      have c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
      have s1: "sin (\<omega> $ 1) \<noteq> 0"
      proof -
        have "sin (\<omega> $ 1) ^ 2 = 1"
          using sin_cos_squared_add[of "\<omega> $ 1"] cz by simp
        thus ?thesis by (auto simp: power2_eq_square)
      qed
      have "sin (\<omega> $ 1) * cos (\<omega> $ 2) = 0" "sin (\<omega> $ 1) * sin (\<omega> $ 2) = 0"
        using eqs[OF cz c0] True by simp_all
      hence "cos (\<omega> $ 2) = 0" "sin (\<omega> $ 2) = 0" using s1 by simp_all
      thus False using sin_cos_squared_add[of "\<omega> $ 2"] by simp
    qed
    thus ?thesis by (simp flip: K_def)
  next
    case False
    hence ABnz: "Q \<noteq> 0 \<or> - P \<noteq> 0" by auto
    \<comment> \<open>\<open>\<omega>\<^sub>2\<close> ranges over the finite zero set of the phase form \<open>Q\<cdot>cos - P\<cdot>sin\<close>.\<close>
    define S2 :: "real set" where
      "S2 = {u::real. ctr $ 2 - pi \<le> u \<and> u \<le> ctr $ 2 + pi
              \<and> Q * cos u + (- P) * sin u = 0}"
    have finS2: "finite S2" unfolding S2_def by (rule finite_phase_zeros_interval[OF ABnz])
    have Ksub: "K \<subseteq> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
    proof
      fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
      have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
      have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
      have c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
      have bnds: "ctr $ 1 - \<delta> \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> ctr $ 1 + \<delta>
                \<and> ctr $ 2 - pi \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> ctr $ 2 + pi"
        by (rule OmegaPF_component_bounds[OF wD])
      have p1: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P"
        and p2: "sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
        using eqs[OF cz c0] by simp_all
      \<comment> \<open>Eliminate \<open>sin(\<omega>\<^sub>1)\<close>: \<open>Q\<cdot>cos(\<omega>\<^sub>2) - P\<cdot>sin(\<omega>\<^sub>2) = sin(\<omega>\<^sub>1)\<cdot>(Q\<cdot>cos\<cdot>... )\<close>.\<close>
      have pz: "Q * cos (\<omega> $ 2) + (- P) * sin (\<omega> $ 2) = 0"
      proof -
        have "Q * cos (\<omega> $ 2) + (- P) * sin (\<omega> $ 2)
            = (sin (\<omega> $ 1) * sin (\<omega> $ 2)) * cos (\<omega> $ 2)
            - (sin (\<omega> $ 1) * cos (\<omega> $ 2)) * sin (\<omega> $ 2)"
          by (simp add: p1[symmetric] p2[symmetric])
        also have "\<dots> = 0" by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      have mem: "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2"
        using bnds cz pz by (auto simp: S1_def S2_def)
      show "\<omega> \<in> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
      proof (rule image_eqI[where x = "(\<omega> $ 1, \<omega> $ 2)"])
        show "\<omega> = (\<lambda>(t, u). vector [t, u] :: real^2) (\<omega> $ 1, \<omega> $ 2)"
          by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
        show "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2" by (rule mem)
      qed
    qed
    have "finite K"
      by (rule finite_subset[OF Ksub
            finite_imageI[OF finite_cartesian_product[OF finS1 finS2]]])
    thus ?thesis by (simp flip: K_def)
  qed
qed

lemma beamcenter_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes card2: "2 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "nowhere_dense {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  \<comment> \<open>\<open>cos \<omega>\<^sub>1 = 0\<close>: the slice is a subset of the
      nowhere-dense matrix_det-Hessian zero set (\<open>gdip''(\<pi>/2) \<noteq> 0\<close>).  \<open>cos \<omega>\<^sub>1 \<noteq> 0\<close>: the slice is
      empty by criticality (@{thm beamcenter_critical_cos_zero}).\<close>
proof (cases "cos (\<omega> $ 1) = 0")
  case True
  have nd: "nowhere_dense {x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
  proof -
    have seq: "{x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
             = {x \<in> (UNIV::((real^2)^'n) set). matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
      by simp
    show ?thesis
      unfolding seq
    proof (rule lines_entire_slice_nowhere_dense)
      show "continuous_on UNIV (\<lambda>x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
        by (rule continuous_det_HessU_beamcenter[OF cz])
      show "\<And>a v. \<exists>F. F holomorphic_on UNIV
              \<and> (\<forall>t::real. F (complex_of_real t)
                          = complex_of_real (matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (a + t *\<^sub>R v) \<omega>)))"
        using rline_entire_det_HessU_beamcenter[OF cz] unfolding rline_entire_def by blast
      show "\<exists>x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
        by (rule det_HessU_beamcenter_witness[OF card2 pfw cz True])
    qed
  qed
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}
        \<subseteq> {x::(real^2)^'n. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by blast
  show ?thesis by (rule nowhere_dense_subset[OF sub nd])
next
  case False
  have empty: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0} = {}"
  proof (rule equals0I)
    fix x :: "(real^2)^'n"
    assume "x \<in> {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
    hence g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    have "cos (\<omega> $ 1) = 0" by (rule beamcenter_critical_cos_zero[OF pfw cz g0])
    with False show False by simp
  qed
  show ?thesis unfolding empty by simp
qed

lemma meager_main_beam:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes card2: "2 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (jacobian (cvec_dip \<omega>0 \<omega>s) (at \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
proof -
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  have finK: "finite K"
    unfolding K_def by (rule beamcenter_K_finite)
  define slice :: "real^2 \<Rightarrow> ((real^2)^'n) set" where
    "slice \<omega> = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}" for \<omega> :: "real^2"
  text \<open>Every witness angle lies in \<open>K\<close>.\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}
             \<subseteq> (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
    then obtain \<omega> :: "real^2" where wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and hz: "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and dnz: "matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      and cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
      by blast
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    have cosz: "cos (\<omega> $ 1) = 0"
      by (rule beamcenter_critical_cos_zero[OF s1 cz g0])
    have wK: "\<omega> \<in> K" using wD cosz cz by (simp add: K_def)
    have xs: "x \<in> slice \<omega>"
      using g0 hz anz dnz by (simp add: slice_def)
    show "x \<in> (\<Union>\<omega>\<in>K. slice \<omega>)"
    proof (rule UN_I)
      show "\<omega> \<in> K" by (rule wK)
      show "x \<in> slice \<omega>" by (rule xs)
    qed
  qed
  text \<open>Each slice over a fixed angle in \<open>K\<close> is nowhere dense; the finite union is meager.\<close>
  have meagU: "meager (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof (rule meager_Union_finite[OF finK])
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    show "meager (slice \<omega>)"
      unfolding slice_def
      by (rule meager_nowhere_dense[OF beamcenter_slice_nowhere_dense[OF card2 s1 cz]])
  qed
  show ?thesis unfolding jacobian_cvec_dip by (rule meager_subset[OF sub meagU])
qed

end
