section \<open>Derivatives of the array factor and of the pattern\<close>

theory Pattern_Derivatives
  imports
    Array_Factor
begin

subsection \<open>Derivatives in the configuration\<close>

definition dA_cart ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> planar) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> complex"
where
  "dA_cart cvec dc x \<omega> h =
     (\<Sum>n\<in>UNIV.
        (- \<i>) * complex_of_real (dc h \<bullet> (x $ n))
        * cis (-(cvec \<omega> \<bullet> (x $ n))))"

definition dU_cart ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> planar) \<Rightarrow>
   (angle \<Rightarrow> real) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow>
   (planar^'n) \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> real"
where
  "dU_cart cvec dc gain dgain x \<omega> h =
     dgain h * (cmod (A_cart cvec x \<omega>))\<^sup>2
   + gain \<omega> * (2 * Re (cnj (A_cart cvec x \<omega>)
             * dA_cart cvec dc x \<omega> h))"

lemma has_derivative_cis_neg_inner:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc   :: "angle \<Rightarrow> planar"
    and y    :: planar
    and \<omega>    :: angle
  assumes neg_inner_deriv:
    "((\<lambda>\<omega>. - (cvec \<omega> \<bullet> y))
       has_derivative
         (\<lambda>h. - (dc h \<bullet> y)))
     (at \<omega>)"
  shows
    "((\<lambda>\<omega>. cis (-(cvec \<omega> \<bullet> y)))
       has_derivative
         (\<lambda>h. (- (dc h \<bullet> y)) *\<^sub>R
              (\<i> * cis (-(cvec \<omega> \<bullet> y)))))
     (at \<omega>)"
proof -
  have cis_deriv:
    "(cis has_derivative
       (\<lambda>r. r *\<^sub>R (\<i> * cis (-(cvec \<omega> \<bullet> y)))))
     (at (-(cvec \<omega> \<bullet> y)))"
    by (auto intro!: derivative_eq_intros)

  have comp:
    "((cis \<circ> (\<lambda>\<omega>. - (cvec \<omega> \<bullet> y)))
       has_derivative
         ((\<lambda>r. r *\<^sub>R (\<i> * cis (-(cvec \<omega> \<bullet> y))))
            \<circ> (\<lambda>h. - (dc h \<bullet> y))))
     (at \<omega>)"
    using neg_inner_deriv cis_deriv diff_chain_at has_derivative_ident
    by (subst has_derivative_compose, blast, simp_all)
  then show ?thesis
    by (simp add: o_def)
qed

lemma has_derivative_cis_neg_inner_complex:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc   :: "angle \<Rightarrow> planar"
    and y    :: planar
    and \<omega>    :: angle
  assumes neg_inner_deriv:
    "((\<lambda>\<omega>. - (cvec \<omega> \<bullet> y))
       has_derivative
         (\<lambda>h. - (dc h \<bullet> y)))
     (at \<omega>)"
  shows
    "((\<lambda>\<omega>. cis (-(cvec \<omega> \<bullet> y)))
       has_derivative
         (\<lambda>h. \<i> * complex_of_real (-(dc h \<bullet> y))
              * cis (-(cvec \<omega> \<bullet> y))))
     (at \<omega>)"
proof -
  have h:
    "((\<lambda>\<omega>. cis (-(cvec \<omega> \<bullet> y)))
       has_derivative
         (\<lambda>h. (- (dc h \<bullet> y)) *\<^sub>R
              (\<i> * cis (-(cvec \<omega> \<bullet> y)))))
     (at \<omega>)"
    using neg_inner_deriv
    by (rule has_derivative_cis_neg_inner)

  then show ?thesis
    by (simp add: scaleR_conv_of_real algebra_simps)
qed

lemma has_derivative_A_cart_term:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc   :: "angle \<Rightarrow> planar"
    and x    :: "planar^'n"
    and \<omega>    :: angle
  assumes cvec_deriv:
    "(cvec has_derivative dc) (at \<omega>)"
  shows
    "((\<lambda>\<omega>. cis (-(cvec \<omega> \<bullet> (x $ n))))
       has_derivative
         (\<lambda>h. (- \<i>) * complex_of_real (dc h \<bullet> (x $ n))
              * cis (-(cvec \<omega> \<bullet> (x $ n)))))
     (at \<omega>)"
proof -
  let ?y = "x $ n"

  have inner_deriv:
    "((\<lambda>\<omega>. cvec \<omega> \<bullet> ?y)
       has_derivative
         (\<lambda>h. dc h \<bullet> ?y))
     (at \<omega>)"
  proof -
    have inner_at:
      "((\<lambda>z::planar. z \<bullet> ?y)
         has_derivative
           (\<lambda>h. h \<bullet> ?y))
       (at (cvec \<omega>))"
      by (auto intro!: derivative_eq_intros)

    have comp:
      "(((\<lambda>z::planar. z \<bullet> ?y) \<circ> cvec)
         has_derivative
           ((\<lambda>h. h \<bullet> ?y) \<circ> dc))
       (at \<omega>)"
      using cvec_deriv inner_at diff_chain_at
      by (subst has_derivative_compose, blast, simp_all)

    then show ?thesis
      by (simp only: o_def)
  qed

  have neg_inner_deriv:
    "((\<lambda>\<omega>. - (cvec \<omega> \<bullet> ?y))
       has_derivative
         (\<lambda>h. - (dc h \<bullet> ?y)))
     (at \<omega>)"
    using inner_deriv
    by (auto intro!: derivative_eq_intros)

  have cis_deriv:
    "((\<lambda>\<omega>. cis (-(cvec \<omega> \<bullet> ?y)))
       has_derivative
         (\<lambda>h. \<i> * complex_of_real (-(dc h \<bullet> ?y))
              * cis (-(cvec \<omega> \<bullet> ?y))))
     (at \<omega>)"
    using neg_inner_deriv
    by (rule has_derivative_cis_neg_inner_complex)

  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma has_derivative_A_cart:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc   :: "angle \<Rightarrow> planar"
    and x    :: "planar^'n"
    and \<omega>    :: angle
  assumes cvec_deriv:
    "(cvec has_derivative dc) (at \<omega>)"
  shows
    "((\<lambda>\<omega>. A_cart cvec x \<omega>) has_derivative dA_cart cvec dc x \<omega>) (at \<omega>)"
proof -
  have term_deriv:
    "\<And>n. ((\<lambda>\<omega>. cis (-(cvec \<omega> \<bullet> (x $ n))))
       has_derivative
         (\<lambda>h. (- \<i>) * complex_of_real (dc h \<bullet> (x $ n))
              * cis (-(cvec \<omega> \<bullet> (x $ n)))))
     (at \<omega>)"
    using cvec_deriv
    by (rule has_derivative_A_cart_term)

  have sum_deriv:
    "((\<lambda>\<omega>. \<Sum>n\<in>UNIV. cis (-(cvec \<omega> \<bullet> (x $ n))))
       has_derivative
         (\<lambda>h. \<Sum>n\<in>UNIV.
              (- \<i>) * complex_of_real (dc h \<bullet> (x $ n))
              * cis (-(cvec \<omega> \<bullet> (x $ n)))))
     (at \<omega>)"
    by (rule has_derivative_sum, rule term_deriv)

  then show ?thesis
    unfolding A_cart_def dA_cart_def
    by simp
qed

lemma has_derivative_cmod_sq_A_cart:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc   :: "angle \<Rightarrow> planar"
    and x    :: "planar^'n"
    and \<omega>    :: angle
  assumes cvec_deriv:
    "(cvec has_derivative dc) (at \<omega>)"
  shows
    "((\<lambda>\<omega>. (cmod (A_cart cvec x \<omega>))\<^sup>2)
       has_derivative
         (\<lambda>h. 2 * Re (cnj (A_cart cvec x \<omega>)
                    * dA_cart cvec dc x \<omega> h)))
     (at \<omega>)"
proof -
  let ?A = "\<lambda>u. A_cart cvec x u"
  let ?dA = "dA_cart cvec dc x \<omega>"

  have A_deriv:
    "(?A has_derivative ?dA) (at \<omega>)"
    using cvec_deriv
    by (rule has_derivative_A_cart)

  have cmod_sq_id:
    "\<And>z::complex. (cmod z)\<^sup>2 = Re (cnj z * z)"
    by (simp add: power2_eq_square, metis cmod_power2 power2_eq_square)

  have cnj_deriv:
    "((\<lambda>u. cnj (?A u)) has_derivative (\<lambda>h. cnj (?dA h))) (at \<omega>)"
    using A_deriv
    by (auto intro!: derivative_eq_intros)

  have prod_deriv:
    "((\<lambda>u. cnj (?A u) * ?A u)
       has_derivative
         (\<lambda>h. cnj (?dA h) * ?A \<omega> + cnj (?A \<omega>) * ?dA h))
     (at \<omega>)"
    using cnj_deriv A_deriv
    by (auto intro!: derivative_eq_intros simp add: algebra_simps)

  have Re_at:
    "(Re has_derivative (\<lambda>z. Re z))
       (at (cnj (?A \<omega>) * ?A \<omega>))"
    by (auto intro!: derivative_eq_intros)

  have Re_deriv:
    "((\<lambda>u. Re (cnj (?A u) * ?A u))
       has_derivative
         (\<lambda>h. Re (cnj (?dA h) * ?A \<omega> + cnj (?A \<omega>) * ?dA h)))
     (at \<omega>)"
  proof -
    have comp:
      "((Re \<circ> (\<lambda>u. cnj (?A u) * ?A u))
         has_derivative
           ((\<lambda>z. Re z) \<circ>
             (\<lambda>h. cnj (?dA h) * ?A \<omega> + cnj (?A \<omega>) * ?dA h)))
       (at \<omega>)"
      using prod_deriv Re_at
      by (simp add: diff_chain_at)

    then show ?thesis
      by (simp add: o_def)
  qed

  have simp_deriv:
    "\<And>h. Re (cnj (?dA h) * ?A \<omega> + cnj (?A \<omega>) * ?dA h)
        = 2 * Re (cnj (?A \<omega>) * ?dA h)"
  proof -
    fix h
    have "Re (cnj (?dA h) * ?A \<omega>)
        = Re (cnj (cnj (?A \<omega>) * ?dA h))"
      by (simp add: algebra_simps)
    also have "... = Re (cnj (?A \<omega>) * ?dA h)"
      by simp
    finally have h1:
      "Re (cnj (?dA h) * ?A \<omega>)
       = Re (cnj (?A \<omega>) * ?dA h)" .
    show "Re (cnj (?dA h) * ?A \<omega> + cnj (?A \<omega>) * ?dA h)
        = 2 * Re (cnj (?A \<omega>) * ?dA h)"
      by (simp add: h1)
  qed

  have
    "((\<lambda>u. Re (cnj (?A u) * ?A u))
       has_derivative
         (\<lambda>h. 2 * Re (cnj (?A \<omega>) * ?dA h)))
     (at \<omega>)"
    using Re_deriv
    by (simp add: simp_deriv)

  then show ?thesis
    by (simp add: cmod_sq_id)
qed

lemma has_derivative_U_cart:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc    :: "angle \<Rightarrow> planar"
    and gain  :: "angle \<Rightarrow> real"
    and dgain :: "angle \<Rightarrow> real"
    and x     :: "planar^'n"
    and \<omega>     :: angle
  assumes cvec_deriv:
    "(cvec has_derivative dc) (at \<omega>)"
  assumes gain_deriv:
    "(gain has_derivative dgain) (at \<omega>)"
  shows
    "((\<lambda>\<omega>. U_cart cvec gain x \<omega>) has_derivative dU_cart cvec dc gain dgain x \<omega>) (at \<omega>)"
proof -
  have amp_deriv:
    "((\<lambda>\<omega>. (cmod (A_cart cvec x \<omega>))\<^sup>2)
       has_derivative
         (\<lambda>h. 2 * Re (cnj (A_cart cvec x \<omega>)
                    * dA_cart cvec dc x \<omega> h)))
     (at \<omega>)"
    using cvec_deriv
    by (rule has_derivative_cmod_sq_A_cart)

  have prod_deriv:
    "((\<lambda>\<omega>. gain \<omega> * (cmod (A_cart cvec x \<omega>))\<^sup>2)
       has_derivative
         (\<lambda>h. dgain h * (cmod (A_cart cvec x \<omega>))\<^sup>2
            + gain \<omega> * (2 * Re (cnj (A_cart cvec x \<omega>)
                    * dA_cart cvec dc x \<omega> h))))
     (at \<omega>)"
  proof -
    have h:
      "((\<lambda>\<omega>. gain \<omega> * (cmod (A_cart cvec x \<omega>))\<^sup>2)
         has_derivative
           (\<lambda>h. gain \<omega> * (2 * Re (cnj (A_cart cvec x \<omega>)
                    * dA_cart cvec dc x \<omega> h))
              + dgain h * (cmod (A_cart cvec x \<omega>))\<^sup>2))
       (at \<omega>)"
      using gain_deriv amp_deriv
      by (rule has_derivative_mult)

    then show ?thesis
      by (simp add: algebra_simps)
  qed

  then show ?thesis
    unfolding U_cart_def dU_cart_def
    by simp
qed

subsection \<open>Gradient and Hessian in the angle\<close>

text \<open>Gradient and Hessian of the pattern in the angle: the operators \<open>\<nabla>\<close> and \<open>\<nabla>\<^sup>2\<close> of the analysis library.\<close>

definition gradU :: "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> planar^'n \<Rightarrow> angle \<Rightarrow> planar" where
  "gradU cvec gain x \<omega> = \<nabla> (U_cart cvec gain x) \<omega>"

definition HessU :: "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> planar^'n \<Rightarrow> angle \<Rightarrow> real^2^2" where
  "HessU cvec gain x \<omega> = \<nabla>\<^sup>2 (U_cart cvec gain x) \<omega>"

lemma gradU_explicit:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and dc :: "angle \<Rightarrow> planar" and dgain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes "(cvec has_derivative dc) (at \<omega>)"
    and "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega>
           = (\<Sum>i\<in>UNIV. dU_cart cvec dc gain dgain x \<omega> (axis i 1) *\<^sub>R axis i 1)"
proof -
  have "((U_cart cvec gain x) has_derivative dU_cart cvec dc gain dgain x \<omega>) (at \<omega>)"
    using has_derivative_U_cart[OF assms, where x = x] by simp
  from has_derivative_to_gradient[OF this]
  have "GDERIV (U_cart cvec gain x) \<omega>
          :> (\<Sum>i\<in>UNIV. dU_cart cvec dc gain dgain x \<omega> (axis i 1) *\<^sub>R axis i 1)" .
  thus ?thesis unfolding gradU_def by (rule grad_fun_eq)
qed

lemma gradU_has_derivative_of_C2:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes "Ck_on 2 (U_cart cvec gain x) U" and "\<omega> \<in> U"
  shows "(gradU cvec gain x has_derivative (\<lambda>v. HessU cvec gain x \<omega> *v v)) (at \<omega>)"
proof -
  have H: "HESS (U_cart cvec gain x) \<omega> :> \<nabla>\<^sup>2 (U_cart cvec gain x) \<omega>"
    by (rule Ck_2_imp_hessian_exists[OF assms])
  have gfun: "gradU cvec gain x = \<nabla> (U_cart cvec gain x)"
    by (rule ext) (simp add: gradU_def)
  from H have D: "(\<nabla> (U_cart cvec gain x)
                    has_derivative (\<lambda>v. \<nabla>\<^sup>2 (U_cart cvec gain x) \<omega> *v v)) (at \<omega>)"
    unfolding has_hessian_def .
  show ?thesis unfolding gfun HessU_def by (rule D)
qed

end
