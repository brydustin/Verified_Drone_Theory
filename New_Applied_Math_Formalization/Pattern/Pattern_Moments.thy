section \<open>Gradient and Hessian of the pattern through the moments\<close>

theory Pattern_Moments
  imports
    Dipole_Pattern
begin

subsection \<open>The gradient through the first moments\<close>

definition Mmom :: "(angle \<Rightarrow> planar) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> 2 \<Rightarrow> complex" where
  \<comment> \<open>the \<open>k\<close>-th first moment of the array, \<open>M\<^sub>k = \<Sum>\<^sub>n (x\<^sub>n)\<^sub>k cis(-c\<bullet>x\<^sub>n)\<close>\<close>
  "Mmom cvec x \<omega> k = (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * cis (-(cvec \<omega> \<bullet> (x$n))))"

lemma dA_cart_via_moments:
  "dA_cart cvec dc x \<omega> h
     = (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$k) * Mmom cvec x \<omega> k)"
proof -
  have "dA_cart cvec dc x \<omega> h
      = (\<Sum>n\<in>UNIV. \<Sum>k\<in>UNIV.
           (- \<i>) * complex_of_real ((dc h)$k) * complex_of_real ((x$n)$k)
             * cis (-(cvec \<omega> \<bullet> (x$n))))"
    unfolding dA_cart_def
    by (simp add: inner_vec_def of_real_sum of_real_mult
                  sum_distrib_left sum_distrib_right mult.assoc)
  also have "\<dots> = (\<Sum>k\<in>UNIV. \<Sum>n\<in>UNIV.
           (- \<i>) * complex_of_real ((dc h)$k) * complex_of_real ((x$n)$k)
             * cis (-(cvec \<omega> \<bullet> (x$n))))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$k) * Mmom cvec x \<omega> k)"
    by (simp add: Mmom_def sum_distrib_left mult.assoc)
  finally show ?thesis .
qed

lemma gradU_component_via_moments:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and dc :: "angle \<Rightarrow> planar" and dgain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes dcvec: "(cvec has_derivative dc) (at \<omega>)"
    and dgn: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega> $ j
         = dgain (axis j 1) * (cmod (A_cart cvec x \<omega>))\<^sup>2
           + gain \<omega> * (2 * Re (cnj (A_cart cvec x \<omega>)
                  * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)))"
proof -
  have comp: "gradU cvec gain x \<omega> $ j = dU_cart cvec dc gain dgain x \<omega> (axis j 1)"
    by (simp add: gradU_explicit[OF dcvec dgn] axis_def if_distrib sum.delta cong: if_cong)
  show ?thesis
    by (simp add: comp dU_cart_def dA_cart_via_moments)
qed

lemma gradU_component_real_moments:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and dc :: "angle \<Rightarrow> planar" and dgain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes dcvec: "(cvec has_derivative dc) (at \<omega>)"
    and dgn: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega> $ j
         = dgain (axis j 1) * ((Re (A_cart cvec x \<omega>))\<^sup>2 + (Im (A_cart cvec x \<omega>))\<^sup>2)
           + gain \<omega> * (2 * (\<Sum>k\<in>UNIV. (dc (axis j 1))$k
                  * (Re (A_cart cvec x \<omega>) * Im (Mmom cvec x \<omega> k)
                     - Im (A_cart cvec x \<omega>) * Re (Mmom cvec x \<omega> k))))"
proof -
  let ?A = "A_cart cvec x \<omega>"
  have cmod2: "(cmod ?A)\<^sup>2 = (Re ?A)\<^sup>2 + (Im ?A)\<^sup>2"
    by (simp add: cmod_power2)
  have reterm:
    "Re (cnj ?A * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k))
     = (\<Sum>k\<in>UNIV. (dc (axis j 1))$k
            * (Re ?A * Im (Mmom cvec x \<omega> k) - Im ?A * Re (Mmom cvec x \<omega> k)))"
  proof -
    have "Re (cnj ?A * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k))
        = (\<Sum>k\<in>UNIV. Re (cnj ?A * ((- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)))"
      by (simp add: sum_distrib_left Re_sum)
    also have "\<dots> = (\<Sum>k\<in>UNIV. (dc (axis j 1))$k
            * (Re ?A * Im (Mmom cvec x \<omega> k) - Im ?A * Re (Mmom cvec x \<omega> k)))"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have G: "gradU cvec gain x \<omega> $ j
        = dgain (axis j 1) * (cmod ?A)\<^sup>2
          + gain \<omega> * (2 * Re (cnj ?A
                * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)))"
    by (rule gradU_component_via_moments[OF dcvec dgn])
  show ?thesis by (simp only: G cmod2 reterm)
qed

lemma moment_map_proj_A:   "moment_map x (cvec \<omega>) $ 1 = A_cart cvec x \<omega>"
  by (simp add: A_moment_def phase_def A_cart_def)

lemma moment_map_proj_M1:  "moment_map x (cvec \<omega>) $ 2 = Mmom cvec x \<omega> 1"
  by (simp add: M1_moment_def phase_def Mmom_def)

lemma moment_map_proj_M2:  "moment_map x (cvec \<omega>) $ 3 = Mmom cvec x \<omega> 2"
  by (simp add: M2_moment_def phase_def Mmom_def)

lemma gradU_component_via_moment_map:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and dc :: "angle \<Rightarrow> planar" and dgain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes dcvec: "(cvec has_derivative dc) (at \<omega>)"
    and dgn: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega> $ j
         = dgain (axis j 1) * (cmod (moment_map x (cvec \<omega>) $ 1))\<^sup>2
           + gain \<omega> * (2 * Re (cnj (moment_map x (cvec \<omega>) $ 1)
                * ((- \<i>) * complex_of_real ((dc (axis j 1))$1) * (moment_map x (cvec \<omega>) $ 2)
                 + (- \<i>) * complex_of_real ((dc (axis j 1))$2) * (moment_map x (cvec \<omega>) $ 3))))"
proof -
  have G: "gradU cvec gain x \<omega> $ j
        = dgain (axis j 1) * (cmod (A_cart cvec x \<omega>))\<^sup>2
          + gain \<omega> * (2 * Re (cnj (A_cart cvec x \<omega>)
                * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)))"
    by (rule gradU_component_via_moments[OF dcvec dgn])
  have S: "(\<Sum>k\<in>(UNIV::2 set). (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)
        = (- \<i>) * complex_of_real ((dc (axis j 1))$1) * Mmom cvec x \<omega> 1
        + (- \<i>) * complex_of_real ((dc (axis j 1))$2) * Mmom cvec x \<omega> 2"
    by (simp add: sum_2)
  show ?thesis
    by (simp only: G S moment_map_proj_A moment_map_proj_M1 moment_map_proj_M2)
qed

subsection \<open>Derivatives in the wavevector\<close>

definition Mcfun :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> complex" where
  "Mcfun x c k = (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * cis (-(c \<bullet> (x$n))))"

definition M2cfun :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> 2 \<Rightarrow> complex" where
  "M2cfun x c k l =
     (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * complex_of_real ((x$n)$l) * cis (-(c \<bullet> (x$n))))"

lemma A_cart_eq_A_moment: "A_cart cvec x \<omega> = A_moment x (cvec \<omega>)"
  by (simp add: A_cart_def A_moment_cis)

lemma Mmom_eq_Mcfun: "Mmom cvec x \<omega> k = Mcfun x (cvec \<omega>) k"
  by (simp add: Mmom_def Mcfun_def)

lemma has_derivative_A_moment_c:
  "(A_moment x has_derivative
      (\<lambda>h. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
proof -
  have tderiv: "((\<lambda>c. cis (-(c \<bullet> (x$n)))) has_derivative
                (\<lambda>h. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
    for n
  proof -
    have inner_d: "((\<lambda>c::real^2. -(c \<bullet> (x$n))) has_derivative (\<lambda>h. -(h \<bullet> (x$n)))) (at c)"
      by (auto intro!: derivative_eq_intros)
    have cis_d: "(cis has_derivative (\<lambda>r. r *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))) (at (-(c \<bullet> (x$n))))"
      by (auto intro!: derivative_eq_intros)
    have "((\<lambda>c. cis (-(c \<bullet> (x$n)))) has_derivative
            (\<lambda>h. (-(h \<bullet> (x$n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))) (at c)"
      using has_derivative_compose[OF inner_d cis_d] by (simp add: o_def)
    moreover have "(\<lambda>h. (-(h \<bullet> (x$n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))
                 = (\<lambda>h. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))"
      by (rule ext) (simp add: scaleR_conv_of_real algebra_simps)
    ultimately show ?thesis by simp
  qed
  show ?thesis unfolding A_moment_cis
    by (rule has_derivative_sum) (rule tderiv)
qed

lemma has_derivative_cis_c:
  fixes x :: "(real^2)^'n" and c :: "real^2" and n :: 'n
  shows "((\<lambda>c. cis (-(c \<bullet> (x$n)))) has_derivative
      (\<lambda>h. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
proof -
  have inner_d: "((\<lambda>c::real^2. -(c \<bullet> (x$n))) has_derivative (\<lambda>h. -(h \<bullet> (x$n)))) (at c)"
    by (auto intro!: derivative_eq_intros)
  have cis_d: "(cis has_derivative (\<lambda>r. r *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))) (at (-(c \<bullet> (x$n))))"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>c. cis (-(c \<bullet> (x$n)))) has_derivative
          (\<lambda>h. (-(h \<bullet> (x$n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))) (at c)"
    using has_derivative_compose[OF inner_d cis_d] by (simp add: o_def)
  moreover have "(\<lambda>h. (-(h \<bullet> (x$n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))
               = (\<lambda>h. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))"
    by (rule ext) (simp add: scaleR_conv_of_real algebra_simps)
  ultimately show ?thesis by simp
qed

lemma has_derivative_Mcfun_c:
  "((\<lambda>c. Mcfun x c k) has_derivative
      (\<lambda>h. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                       * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
proof -
  have tderiv: "((\<lambda>c. complex_of_real ((x$n)$k) * cis (-(c \<bullet> (x$n)))) has_derivative
                (\<lambda>h. (- \<i>) * complex_of_real ((x$n)$k)
                       * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
    for n
  proof -
    have "((\<lambda>c. complex_of_real ((x$n)$k) * cis (-(c \<bullet> (x$n)))) has_derivative
            (\<lambda>h. complex_of_real ((x$n)$k)
                  * ((- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
                + 0 * cis (-(c \<bullet> (x$n))))) (at c)"
      by (rule has_derivative_mult[OF has_derivative_const has_derivative_cis_c])
    moreover have "(\<lambda>h. complex_of_real ((x$n)$k)
                  * ((- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
                + 0 * cis (-(c \<bullet> (x$n))))
                 = (\<lambda>h. (- \<i>) * complex_of_real ((x$n)$k)
                       * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))"
      by (rule ext) (simp add: algebra_simps)
    ultimately show ?thesis by simp
  qed
  show ?thesis unfolding Mcfun_def
    by (rule has_derivative_sum) (rule tderiv)
qed

lemma gradU_c_field:
  "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ j
     = 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j))"
proof -
  have d1: "((\<lambda>c::real^2. c) has_derivative (\<lambda>h. h)) (at c)"
    by (rule has_derivative_ident)
  have d2: "((\<lambda>_::real^2. 1::real) has_derivative (\<lambda>_. 0)) (at c)"
    by (rule has_derivative_const)
  have "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ j
        = (\<lambda>_. 0) (axis j 1)
            * ((Re (A_cart (\<lambda>c. c) x c))\<^sup>2 + (Im (A_cart (\<lambda>c. c) x c))\<^sup>2)
          + (\<lambda>_. 1) c * (2 * (\<Sum>k\<in>UNIV. ((\<lambda>h. h) (axis j 1))$k
                 * (Re (A_cart (\<lambda>c. c) x c) * Im (Mmom (\<lambda>c. c) x c k)
                    - Im (A_cart (\<lambda>c. c) x c) * Re (Mmom (\<lambda>c. c) x c k))))"
    by (rule gradU_component_real_moments[OF d1 d2])
  also have "\<dots> = 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j))"
    by (simp add: A_cart_eq_A_moment Mmom_eq_Mcfun axis_def if_distrib sum.delta cong: if_cong,
        smt (verit, ccfv_SIG) exhaust_2 sum_2 zero_neq_one)
  finally show ?thesis .
qed

lemma inner_real2_sum: "(h::real^2) \<bullet> (p::real^2) = (\<Sum>l\<in>UNIV. (h$l) * (p$l))"
  by (simp add: inner_vec_def)

lemma Re_DA_moment:
  fixes x :: "(real^2)^'n" and c h :: "real^2"
  shows "Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
       = (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l))"
proof -
  have "Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
      = (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (h$l) * ((x$n)$l * Im (cis (-(c \<bullet> (x$n))))))"
    by (simp add: Re_sum inner_real2_sum sum_distrib_right mult.assoc)
  also have "\<dots> = (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (h$l) * ((x$n)$l * Im (cis (-(c \<bullet> (x$n))))))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l))"
    by (simp add: sum_distrib_left Mcfun_def Im_sum)
  finally show ?thesis .
qed

lemma Im_DA_moment:
  fixes x :: "(real^2)^'n" and c h :: "real^2"
  shows "Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
       = - (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))"
proof -
  have "Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
      = - (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (h$l) * ((x$n)$l * Re (cis (-(c \<bullet> (x$n))))))"
    by (simp add: Im_sum inner_real2_sum sum_distrib_right mult.assoc sum_negf)
  also have "\<dots> = - (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (h$l) * ((x$n)$l * Re (cis (-(c \<bullet> (x$n))))))"
    by (rule arg_cong[where f = uminus]) (rule sum.swap)
  also have "\<dots> = - (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))"
    by (simp add: sum_distrib_left Mcfun_def Re_sum)
  finally show ?thesis .
qed

lemma Im_M2cfun:
  fixes x :: "(real^2)^'n"
  shows "Im (M2cfun x c k l) = (\<Sum>n\<in>UNIV. ((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n)))))"
  by (simp add: M2cfun_def Im_sum)

lemma Re_M2cfun:
  fixes x :: "(real^2)^'n"
  shows "Re (M2cfun x c k l) = (\<Sum>n\<in>UNIV. ((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n)))))"
  by (simp add: M2cfun_def Re_sum)

lemma ReDMfun:
  fixes x :: "(real^2)^'n" and c h :: "real^2"
  shows "Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
       = (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c k l))"
proof -
  have perterm: "((x$n)$k * (h \<bullet> (x$n))) * Im (cis (-(c \<bullet> (x$n))))
       = (\<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n))))))" for n
  proof -
    have "((x$n)$k * (h \<bullet> (x$n))) * Im (cis (-(c \<bullet> (x$n))))
        = (\<Sum>l\<in>UNIV. (x$n)$k * ((h$l) * (x$n)$l)) * Im (cis (-(c \<bullet> (x$n))))"
      by (simp add: inner_real2_sum sum_distrib_left)
    also have "\<dots> = (\<Sum>l\<in>UNIV. ((x$n)$k * ((h$l) * (x$n)$l)) * Im (cis (-(c \<bullet> (x$n)))))"
      by (simp add: sum_distrib_right sum_negf)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n))))))"
      by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have "Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
      = (\<Sum>n\<in>UNIV. ((x$n)$k * (h \<bullet> (x$n))) * Im (cis (-(c \<bullet> (x$n)))))"
    by (simp add: Re_sum)
  also have "\<dots> = (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n))))))"
    by (rule sum.cong[OF refl]) (rule perterm)
  also have "\<dots> = (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n))))))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c k l))"
    by (simp add: sum_distrib_left Im_M2cfun)
  finally show ?thesis .
qed

lemma ImDMfun:
  fixes x :: "(real^2)^'n" and c h :: "real^2"
  shows "Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
       = - (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c k l))"
proof -
  have perterm: "((x$n)$k * (h \<bullet> (x$n))) * Re (cis (-(c \<bullet> (x$n))))
       = (\<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n))))))" for n
  proof -
    have "((x$n)$k * (h \<bullet> (x$n))) * Re (cis (-(c \<bullet> (x$n))))
        = (\<Sum>l\<in>UNIV. (x$n)$k * ((h$l) * (x$n)$l)) * Re (cis (-(c \<bullet> (x$n))))"
      by (simp add: inner_real2_sum sum_distrib_left)
    also have "\<dots> = (\<Sum>l\<in>UNIV. ((x$n)$k * ((h$l) * (x$n)$l)) * Re (cis (-(c \<bullet> (x$n)))))"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n))))))"
      by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have "Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
      = - (\<Sum>n\<in>UNIV. ((x$n)$k * (h \<bullet> (x$n))) * Re (cis (-(c \<bullet> (x$n)))))"
    by (simp add: Im_sum sum_negf)
  also have "\<dots> = - (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n))))))"
    by (rule arg_cong[where f = uminus], rule sum.cong[OF refl], rule perterm)
  also have "\<dots> = - (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n))))))"
    by (rule arg_cong[where f = uminus]) (rule sum.swap)
  also have "\<dots> = - (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c k l))"
    by (simp add: sum_distrib_left Re_M2cfun)
  finally show ?thesis .
qed

definition Hcmat :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> real^2^2" where
  "Hcmat x c = (\<chi> k. \<chi> l. 2 * (Re (cnj (Mcfun x c l) * Mcfun x c k)
                               - Re (cnj (A_moment x c) * M2cfun x c k l)))"

lemma dRe_A_moment:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "((\<lambda>c. Re (A_moment x c)) has_derivative (\<lambda>h. \<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l))) (at c)"
proof (rule has_derivative_eq_rhs)
  show "((\<lambda>c. Re (A_moment x c)) has_derivative
          (\<lambda>h. Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))) (at c)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_A_moment_c])
  show "(\<lambda>h. Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))
        = (\<lambda>h. \<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l))"
    by (rule ext) (rule Re_DA_moment)
qed

lemma dIm_A_moment:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "((\<lambda>c. Im (A_moment x c)) has_derivative (\<lambda>h. - (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l)))) (at c)"
proof (rule has_derivative_eq_rhs)
  show "((\<lambda>c. Im (A_moment x c)) has_derivative
          (\<lambda>h. Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))) (at c)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_A_moment_c])
  show "(\<lambda>h. Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))
        = (\<lambda>h. - (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l)))"
    by (rule ext) (rule Im_DA_moment)
qed

lemma dRe_Mcfun:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "((\<lambda>c. Re (Mcfun x c k)) has_derivative
            (\<lambda>h. \<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c k l))) (at c)"
proof (rule has_derivative_eq_rhs)
  show "((\<lambda>c. Re (Mcfun x c k)) has_derivative
          (\<lambda>h. Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                     * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))) (at c)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Mcfun_c])
  show "(\<lambda>h. Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                     * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))
        = (\<lambda>h. \<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c k l))"
    by (rule ext) (rule ReDMfun)
qed

lemma dIm_Mcfun:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "((\<lambda>c. Im (Mcfun x c k)) has_derivative
            (\<lambda>h. - (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c k l)))) (at c)"
proof (rule has_derivative_eq_rhs)
  show "((\<lambda>c. Im (Mcfun x c k)) has_derivative
          (\<lambda>h. Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                     * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))) (at c)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Mcfun_c])
  show "(\<lambda>h. Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                     * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))
        = (\<lambda>h. - (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c k l)))"
    by (rule ext) (rule ImDMfun)
qed

lemma has_derivative_gradU_c:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "(gradU (\<lambda>c. c) (\<lambda>_. 1) x has_derivative (\<lambda>h. Hcmat x c *v h)) (at c)"
proof -
  have field_eq: "gradU (\<lambda>c. c) (\<lambda>_. 1) x
        = (\<lambda>c. \<chi> j. 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j)))"
  proof (rule ext)
    fix c :: "real^2"
    have "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ i
          = (\<chi> j. 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j))) $ i"
      for i by (simp add: gradU_c_field)
    thus "gradU (\<lambda>c. c) (\<lambda>_. 1) x c
          = (\<chi> j. 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j)))"
      by (simp add: Finite_Cartesian_Product.vec_eq_iff)
  qed
  have comp: "((\<lambda>c. 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j)))
                has_derivative (\<lambda>h. (Hcmat x c *v h) $ j)) (at c)" for j
  proof (rule has_derivative_eq_rhs)
    show "((\<lambda>c. 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j)))
            has_derivative
            (\<lambda>h. 2 * ((Re (A_moment x c) * (- (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c j l)))
                       + (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l)) * Im (Mcfun x c j))
                    - (Im (A_moment x c) * (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c j l))
                       + (- (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))) * Re (Mcfun x c j)))
                 + 0 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j)))) (at c)"
      by (rule has_derivative_mult[OF has_derivative_const
                has_derivative_diff[OF has_derivative_mult[OF dRe_A_moment dIm_Mcfun]
                                       has_derivative_mult[OF dIm_A_moment dRe_Mcfun]]])
    show "(\<lambda>h. 2 * ((Re (A_moment x c) * (- (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c j l)))
                       + (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l)) * Im (Mcfun x c j))
                    - (Im (A_moment x c) * (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c j l))
                       + (- (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))) * Re (Mcfun x c j)))
                 + 0 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j)))
          = (\<lambda>h. (Hcmat x c *v h) $ j)"
    proof (rule ext)
      fix h :: "real^2"
      have "(Hcmat x c *v h) $ j
          = (\<Sum>l\<in>UNIV. (h$l) * (2 * (Re (Mcfun x c l) * Re (Mcfun x c j) + Im (Mcfun x c l) * Im (Mcfun x c j)
                  - (Re (A_moment x c) * Re (M2cfun x c j l) + Im (A_moment x c) * Im (M2cfun x c j l)))))"
        by (simp add: matrix_vector_mult_def Hcmat_def mult.commute)
      thus "2 * ((Re (A_moment x c) * (- (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c j l)))
                   + (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l)) * Im (Mcfun x c j))
                - (Im (A_moment x c) * (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c j l))
                   + (- (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))) * Re (Mcfun x c j)))
             + 0 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j))
           = (Hcmat x c *v h) $ j"
        by (simp add: sum_distrib_left sum_distrib_right sum_subtractf sum_negf sum.distrib algebra_simps)
    qed
  qed
  have "(gradU (\<lambda>c. c) (\<lambda>_. 1) x has_derivative (\<lambda>h. Hcmat x c *v h)) (at c)"
    unfolding field_eq
  proof (subst has_derivative_componentwise_within, intro ballI)
    fix b :: "real^2" assume "b \<in> Basis"
    then obtain j where bj: "b = axis j 1" by (auto simp: Basis_vec_def)
    have "((\<lambda>c. (\<chi> j. 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j))) \<bullet> b)
            has_derivative (\<lambda>h. (Hcmat x c *v h) \<bullet> b)) (at c within UNIV)"
      using comp[of j] by (simp add: bj inner_axis)
    thus "((\<lambda>c. (\<chi> j. 2 * (Re (A_moment x c) * Im (Mcfun x c j) - Im (A_moment x c) * Re (Mcfun x c j))) \<bullet> b)
            has_derivative (\<lambda>h. ((\<lambda>h. Hcmat x c *v h) h) \<bullet> b)) (at c within UNIV)"
      by simp
  qed
  thus ?thesis .
qed

subsection \<open>The pattern as a function of the wavevector\<close>

lemma U_cart_factor:
  "U_cart cvec gain x \<omega> = gain \<omega> * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)"
  by (simp add: U_cart_def A_cart_eq_A_moment)

lemma has_derivative_Uc_c:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "(U_cart (\<lambda>c. c) (\<lambda>_. 1) x has_derivative (\<lambda>v. v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x c)) (at c)"
proof -
  have hd: "(U_cart (\<lambda>c. c) (\<lambda>_. 1) x
              has_derivative dU_cart (\<lambda>c. c) (\<lambda>h. h) (\<lambda>_. 1) (\<lambda>_. 0) x c) (at c)"
    by (rule has_derivative_U_cart[OF has_derivative_ident has_derivative_const])
  have "GDERIV (U_cart (\<lambda>c. c) (\<lambda>_. 1) x) c :> \<nabla> (U_cart (\<lambda>c. c) (\<lambda>_. 1) x) c"
    by (rule grad_fun_satisfies_GDERIV[OF has_derivative_to_gradient[OF hd]])
  thus ?thesis by (simp add: gderiv_def gradU_def)
qed

lemma has_derivative_U_via_c:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
    and Dg: "(gain has_derivative dgain) (at \<omega>)"
  shows "(U_cart cvec gain x has_derivative
            (\<lambda>v. gain \<omega> * (Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                 + dgain v * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))) (at \<omega>)"
proof -
  have chain: "((\<lambda>\<omega>. U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                  has_derivative (\<lambda>v. Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))) (at \<omega>)"
    using diff_chain_at[OF Dc has_derivative_Uc_c] by (simp add: o_def)
  have "((\<lambda>\<omega>. gain \<omega> * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
          has_derivative (\<lambda>v. gain \<omega> * (Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                              + dgain v * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))) (at \<omega>)"
    by (rule has_derivative_mult[OF Dg chain])
  moreover have "U_cart cvec gain x = (\<lambda>\<omega>. gain \<omega> * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))"
    by (rule ext) (rule U_cart_factor)
  ultimately show ?thesis by simp
qed

lemma has_derivative_gradU_c_along_cvec:
  fixes cvec :: "angle \<Rightarrow> planar" and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
  shows "((\<lambda>\<omega>. gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
            has_derivative (\<lambda>v. Hcmat x (cvec \<omega>) *v (Dcvec v))) (at \<omega>)"
  using diff_chain_at[OF Dc has_derivative_gradU_c] by (simp add: o_def)

lemma has_derivative_V_along_cvec:
  fixes cvec :: "angle \<Rightarrow> planar" and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
  shows "((\<lambda>\<omega>. U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
            has_derivative (\<lambda>v. Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))) (at \<omega>)"
  using diff_chain_at[OF Dc has_derivative_Uc_c] by (simp add: o_def)

lemma gradU_via_c:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
    and Dg: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega>
         = (\<Sum>i\<in>UNIV. (gain \<omega> * (Dcvec (axis i 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                       + dgain (axis i 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)) *\<^sub>R axis i 1)"
proof -
  have "\<nabla> (U_cart cvec gain x) \<omega>
      = (\<Sum>i\<in>UNIV. (\<lambda>v. gain \<omega> * (Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                          + dgain v * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)) (axis i 1) *\<^sub>R axis i 1)"
    by (rule grad_fun_eq[OF has_derivative_to_gradient[OF has_derivative_U_via_c[OF Dc Dg]]])
  thus ?thesis by (simp add: gradU_def)
qed

lemma gradU_via_c_component:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
    and Dg: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega> $ k
         = gain \<omega> * (Dcvec (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
           + dgain (axis k 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)"
proof -
  have "gradU cvec gain x \<omega> $ k
      = (\<Sum>i\<in>UNIV. (gain \<omega> * (Dcvec (axis i 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                     + dgain (axis i 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                   * (axis (i::2) 1 $ k))"
    by (simp add: gradU_via_c[OF Dc Dg] sum_component)
  also have "\<dots> = gain \<omega> * (Dcvec (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                   + dgain (axis k 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)"
    by (simp add: axis_def if_distrib sum.delta cong: if_cong)
  finally show ?thesis .
qed

lemma gain_dip_deriv_field_differentiable:
  fixes \<omega> :: "real^2"
  shows "(\<lambda>\<omega>::real^2. frechet_derivative gdip (at (\<omega>$1)) s) differentiable (at \<omega>)"
proof -
  have proj: "(\<lambda>\<omega>::real^2. \<omega>$1) differentiable (at \<omega>)"
    using has_derivative_proj by (blast intro: differentiableI)
  have inner: "(\<lambda>t::real. frechet_derivative gdip (at t) s) differentiable (at (\<omega>$1))"
    by (rule gdip_deriv_differentiable)
  show ?thesis
    using differentiable_chain_at[OF proj inner] by (simp add: o_def)
qed

lemma gradU_dip_component_field:
  fixes x :: "(real^2)^'n"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k
         = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
           + frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
             * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)"
  by (rule gradU_via_c_component[OF has_derivative_cvec_dip gain_dip_has_derivative])

lemma has_derivative_gradU_dip_component:
  fixes x :: "(real^2)^'n"
  shows "((\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) has_derivative
    (\<lambda>h. (gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> h))
                        + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) h)
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative gdip (at (\<omega>$1)) (h$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))
        + (frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> h \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) h
            * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))) (at \<omega>)"
proof -
  have dGain: "(gain_dip has_derivative (\<lambda>v. frechet_derivative gdip (at (\<omega>$1)) (v$1))) (at \<omega>)"
    by (rule gain_dip_has_derivative)
  have dDc: "((\<lambda>\<omega>. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) has_derivative D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) (at \<omega>)"
    by (rule has_derivative_Dcvec_dip)
  have dgcV: "((\<lambda>\<omega>. gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
                has_derivative (\<lambda>v. Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> v))) (at \<omega>)"
    by (rule has_derivative_gradU_c_along_cvec[OF has_derivative_cvec_dip])
  have dGD: "((\<lambda>\<omega>. frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)) has_derivative
              frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>)) (at \<omega>)"
    by (rule frechet_derivative_works[THEN iffD1, OF gain_dip_deriv_field_differentiable])
  have dV: "((\<lambda>\<omega>. U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
              has_derivative (\<lambda>v. Dcvec_dip \<omega>0 \<omega>s \<omega> v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at \<omega>)"
    by (rule has_derivative_V_along_cvec[OF has_derivative_cvec_dip])
  have dIP: "((\<lambda>\<omega>. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
              has_derivative
              (\<lambda>h. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> h))
                   + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) h) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at \<omega>)"
    by (rule has_derivative_inner[OF dDc dgcV])
  have field: "(\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k)
             = (\<lambda>\<omega>. gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
                    + frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
                      * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    by (rule ext) (rule gradU_dip_component_field)
  show ?thesis
    unfolding field
    by (rule has_derivative_add[OF has_derivative_mult[OF dGain dIP] has_derivative_mult[OF dGD dV]])
qed

lemma HessU_dip_eq_componentderiv:
  fixes x :: "(real^2)^'n"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
         = frechet_derivative (\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) (at \<omega>) (axis l 1)"
proof -
  have "((\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k)
          has_derivative (\<lambda>v. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v) $ k)) (at \<omega>)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth gradU_dip_has_derivative])
  hence "frechet_derivative (\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) (at \<omega>) (axis l 1)
         = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v axis l 1) $ k"
    by (simp add: frechet_derivative_at')
  also have "\<dots> = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l"
    by (simp add: matrix_vector_mult_def axis_def if_distrib sum.delta cong: if_cong)
  finally show ?thesis by (rule sym)
qed

lemma HessU_dip_entry_moments:
  fixes x :: "(real^2)^'n"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
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
proof -
  \<comment> \<open>Step 1: the \<open>(k,l)\<close> Hessian entry is the directional derivative, along \<open>e\<^sub>l = axis l 1\<close>,
        of the \<open>k\<close>-th component of the gradient field.\<close>
  have step1: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
      = frechet_derivative (\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) (at \<omega>) (axis l 1)"
    by (rule HessU_dip_eq_componentderiv)
  \<comment> \<open>Step 2: the total (Frechet) derivative of that scalar component field is the explicit
        moment-space linear map established in @{thm has_derivative_gradU_dip_component} --- a sum of
        the curvature term \<open>\<nabla>\<^sub>c\<^sup>2V\<close> (via \<open>Hcmat\<close>), the second-order chart jet \<open>D\<^sup>2cvec_dip\<close>, and the
        gain's first/second \<open>\<omega>\<close>-derivatives times \<open>\<nabla>\<^sub>cV\<close> and \<open>V\<close>.\<close>
  have step2: "frechet_derivative (\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) (at \<omega>)
      = (\<lambda>h. (gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> h))
                        + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) h)
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative gdip (at (\<omega>$1)) (h$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))
        + (frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> h \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) h
            * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))"
    by (rule frechet_derivative_at'[OF has_derivative_gradU_dip_component])
  \<comment> \<open>Step 3: evaluate that linear map at \<open>e\<^sub>l = axis l 1\<close> (\<open>\<beta>\<close>-reduction substitutes \<open>h := axis l 1\<close>),
        which is exactly the claimed moment expression.\<close>
  show ?thesis
    unfolding step1 step2 by (rule refl)
qed

lemma gradU_dip_component_moments:
  fixes x :: "(real^2)^'n"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
         = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
             * (cmod (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2
           + gain_dip \<omega> * (2 * Re (cnj (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
                * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1)
                     * (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
                 + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                     * (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))))"
  by (rule gradU_component_via_moment_map[OF has_derivative_cvec_dip gain_dip_has_derivative])

lemma Uc_eq_moment:
  fixes x :: "(real^2)^'n"
  shows "U_cart (\<lambda>c. c) (\<lambda>_. 1) x c = (cmod (moment_map x c $ 1))\<^sup>2"
proof -
  have "moment_map x c $ 1 = A_moment x c"
    using moment_map_proj_A[of x "\<lambda>c. c" c] by (simp add: A_cart_eq_A_moment)
  thus ?thesis by (simp add: U_cart_def A_cart_eq_A_moment)
qed

lemma gradUc_component_moments:
  fixes x :: "(real^2)^'n"
  shows "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ j
       = 2 * Re (cnj (moment_map x c $ 1)
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * (moment_map x c $ 2)
             + (- \<i>) * complex_of_real ((axis j 1)$2) * (moment_map x c $ 3)))"
proof -
  have d1: "((\<lambda>c::real^2. c) has_derivative (\<lambda>v. v)) (at c)" by (rule has_derivative_ident)
  have d2: "((\<lambda>_::real^2. 1::real) has_derivative (\<lambda>_. 0)) (at c)" by (rule has_derivative_const)
  show ?thesis
    using gradU_component_via_moment_map[OF d1 d2] by simp
qed

subsection \<open>Continuity in configuration and angle\<close>

lemma continuous_on_Mcfun_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set) (\<lambda>p. Mcfun (fst p) (snd p) k)"
  unfolding Mcfun_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_M2cfun_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set) (\<lambda>p. M2cfun (fst p) (snd p) k l)"
  unfolding M2cfun_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_Mcfun_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. Mcfun (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) k)"
  using continuous_on_compose2[OF continuous_on_Mcfun_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M2cfun_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M2cfun (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) k l)"
  using continuous_on_compose2[OF continuous_on_M2cfun_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_Hcmat_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. Hcmat (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  unfolding Hcmat_def
  by (intro continuous_on_vec_lambda continuous_intros
            continuous_on_A_moment_cvec_dip continuous_on_Mcfun_cvec_dip
            continuous_on_M2cfun_cvec_dip)

lemma continuous_on_gradUc_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. gradU (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
proof -
  have "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
          (\<lambda>p. \<chi> j. gradU (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) $ j)"
  proof (intro continuous_on_vec_lambda)
    fix j :: 2
    show "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
            (\<lambda>p. gradU (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) $ j)"
      by (simp only: gradUc_component_moments moment_map_components,
          intro continuous_intros continuous_on_A_moment_cvec_dip
                continuous_on_M1_moment_cvec_dip continuous_on_M2_moment_cvec_dip)
  qed
  thus ?thesis by (simp add: vec_lambda_eta)
qed

lemma continuous_on_Uc_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. U_cart (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
proof -
  have *: "(\<lambda>p::(planar^'n) \<times> (real^2). U_cart (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
         = (\<lambda>p. (cmod (A_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p))))\<^sup>2)"
    by (rule ext) (simp add: Uc_eq_moment moment_map_components)
  show ?thesis
    unfolding *
    by (intro continuous_intros continuous_on_A_moment_cvec_dip)
qed

lemma continuous_on_matvec:
  fixes A :: "'a::topological_space \<Rightarrow> real^('m::finite)^('p::finite)"
    and v :: "'a \<Rightarrow> real^'m"
  assumes "continuous_on S A" and "continuous_on S v"
  shows "continuous_on S (\<lambda>x. A x *v v x)"
  unfolding matrix_vector_mult_def
  by (intro continuous_on_vec_lambda continuous_on_sum continuous_intros
            continuous_on_component assms)

lemma continuous_on_gain_dip_snd:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set) (\<lambda>p. gain_dip (snd p))"
  by (rule continuous_on_compose2[OF continuous_on_gain_dip
        continuous_on_snd[OF continuous_on_id] subset_UNIV])

lemma continuous_on_Dcvec_dip_snd:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set) (\<lambda>p. Dcvec_dip \<omega>0 \<omega>s (snd p) h)"
  by (rule continuous_on_compose2[OF continuous_on_Dcvec_dip
        continuous_on_snd[OF continuous_on_id] subset_UNIV])

lemma continuous_on_D2cvec_dip_snd:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set) (\<lambda>p. D2cvec_dip \<omega>0 \<omega>s (snd p) h h')"
  by (rule continuous_on_compose2[OF continuous_on_D2cvec_dip
        continuous_on_snd[OF continuous_on_id] subset_UNIV])

lemma continuous_on_frechet_gdip_proj_snd:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. frechet_derivative gdip (at ((snd p)$1)) r)"
  by (rule continuous_on_compose2[OF continuous_on_frechet_gdip_proj
        continuous_on_snd[OF continuous_on_id] subset_UNIV])

lemma continuous_on_frechet2_gdip_proj_snd:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) c) (at (snd p)) v)"
  by (rule continuous_on_compose2[OF continuous_on_frechet2_gdip_proj
        continuous_on_snd[OF continuous_on_id] subset_UNIV])

lemma continuous_on_HessU_dip_entry:
    "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
       (\<lambda>p. vec_nth (vec_nth (HessU (cvec_dip \<omega>0
  \<omega>s) gain_dip (fst p) (snd p)) k) l)"
    by (simp only: HessU_dip_entry_moments,
        intro continuous_intros 
              continuous_on_matvec continuous_on_gain_dip_snd
              continuous_on_Dcvec_dip_snd 
              continuous_on_D2cvec_dip_snd
              continuous_on_frechet_gdip_proj_snd 
              continuous_on_frechet2_gdip_proj_snd
              continuous_on_Hcmat_cvec_dip continuous_on_gradUc_cvec_dip 
              continuous_on_Uc_cvec_dip)

lemma continuous_on_HessU_dip_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))"
proof -
  have "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
          (\<lambda>p. \<chi> k. \<chi> l. vec_nth (vec_nth
                  (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) k) l)"
    by (intro continuous_on_vec_lambda continuous_on_HessU_dip_entry)
  thus ?thesis by (simp add: vec_lambda_eta)
qed

lemma continuous_on_DA_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set) (\<lambda>p. DA_moment (fst p) (snd p) h)"
  unfolding DA_moment_def d_phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_DM1_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set) (\<lambda>p. DM1_moment (fst p) (snd p) h)"
  unfolding DM1_moment_def phase_def d_phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_DM2_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set) (\<lambda>p. DM2_moment (fst p) (snd p) h)"
  unfolding DM2_moment_def phase_def d_phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_DA_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. DA_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) h)"
  using continuous_on_compose2[OF continuous_on_DA_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_DM1_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. DM1_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) h)"
  using continuous_on_compose2[OF continuous_on_DM1_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_DM2_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. DM2_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) h)"
  using continuous_on_compose2[OF continuous_on_DM2_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

subsection \<open>Surjectivity of linear maps\<close>

lemma surj_matrix_vector_iff_det:
  fixes A :: "real^'n^'n"
  shows "surj ((*v) A) \<longleftrightarrow> matrix_det A \<noteq> 0"
proof
  assume "matrix_det A \<noteq> 0"
  hence "invertible A" by (simp add: invertible_det_nz)
  hence "bij ((*v) A)" by (simp add: invertible_eq_bij)
  thus "surj ((*v) A)" by (simp add: bij_betw_def)
next
  assume "surj ((*v) A)"
  then obtain B where AB: "A ** B = mat 1"
    using matrix_right_invertible_surjective by blast
  have "B ** A = mat 1" by (rule matrix_left_right_inverse1[OF AB])
  with AB have "invertible A" unfolding invertible_def by blast
  thus "matrix_det A \<noteq> 0" by (simp add: invertible_det_nz)
qed

lemma det_2_symmetric:
  fixes A :: "real^2^2"
  assumes "A $ 1 $ 2 = A $ 2 $ 1"
  shows "matrix_det A = A $ 1 $ 1 * A $ 2 $ 2 - (A $ 1 $ 2)\<^sup>2"
  using assms by (simp add: det_2 power2_eq_square)

lemma surj_partial_imp_surj_joint:
  fixes Dj :: "('a::real_normed_vector \<times> 'b::real_normed_vector) \<Rightarrow> 'c::real_normed_vector"
  assumes s: "surj Dx" and rel: "\<And>h. Dj (h, 0) = Dx h"
  shows "surj Dj"
proof -
  have "y \<in> range Dj" for y
  proof -
    from s obtain h where "Dx h = y" by (metis surjD)
    hence "Dj (h, 0) = y" using rel by simp
    thus ?thesis by (metis rangeI)
  qed
  thus ?thesis by auto
qed

lemma joint_deriv_restricts_to_partial:
  fixes G :: "('a::real_normed_vector \<times> 'b::real_normed_vector) \<Rightarrow> 'c::real_normed_vector"
  assumes Dj: "(G has_derivative Dj) (at (x, w))"
    and Dx: "((\<lambda>y. G (y, w)) has_derivative Dx) (at x)"
  shows "Dj (h, 0) = Dx h"
proof -
  have sec: "((\<lambda>y. (y, w)) has_derivative (\<lambda>h. (h, 0))) (at x)"
    by (auto intro!: derivative_eq_intros)
  have "((G \<circ> (\<lambda>y. (y, w))) has_derivative (Dj \<circ> (\<lambda>h. (h, 0)))) (at x)"
    by (rule diff_chain_at[OF sec Dj])
  hence "((\<lambda>y. G (y, w)) has_derivative (\<lambda>h. Dj (h, 0))) (at x)"
    by (simp add: o_def)
  from has_derivative_unique[OF this Dx]
  show "Dj (h, 0) = Dx h" by (metis fun_cong)
qed

end
