theory Nonemptiness_Paper
  imports
    Parametric_Transversality_Euclidean
    Nonemptiness_Array_Factor
    Nonemptiness_Feasibility
    Nonemptiness_Spine
    Regular_Value_Theorem
    "HOL-Complex_Analysis.Conformal_Mappings"
begin

text \<open>
  Working file for the formalization of
   \<open>../Applied Math/nonemptiness_unified_singlefile_complete.tex\<close>.

  This theory is intentionally organized in the same order as the TeX document.
  The rule is: prove each lemma/proposition before using it later.

  We keep the closeout lemma separate (it is already proved in
   Nonemptiness_Spine as \<open>nonemptiness_from_meager_branches\<close>.
\<close>


section \<open>Setup\<close>

text \<open>
  TeX Section 2 defines: \<open>k\<close>, \<open>\<Delta>k\<close>, \<open>D\<^sub>x,D\<^sub>y\<close>, \<open>cvec\<close>, and the pattern
  \<open>U(x,\<omega>) = g(\<omega>) * |A(x,\<omega>)|^2\<close>.

  This has not yet been mirrored fully in Isabelle; currently we have a generic
  \<open>cvec\<close> and \<open>array factor\<close> layer in theory Nonemptiness_Array_Factor.
\<close>


type_synonym angle = "real^2"   (* (theta, phi) as a 2-vector *)
type_synonym planar = "real^2"

section \<open>Cartesian Array Factor and Steered Derivatives\<close>

text \<open>
 
  The paper's steering-center angle is represented by a fixed parameter
  @{term \<omega>s}.  If @{term kvec} is the paper's wave-vector map, then the
  phase vector used below is

    kvec \<omega> - kvec \<omega>s.

  The paper writes the element factor inside the squared modulus,

    | e(\<omega>) * A(x,\<omega>) |^2.

  In this formalization we use

    gain \<omega> = (e \<omega>)^2,

  so that

    |e(\<omega>) * A(x,\<omega>)|^2 = gain \<omega> * |A(x,\<omega>)|^2.
\<close>

subsection \<open>Amplitude, gain, and objective\<close>

definition A_cart ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> complex"
where
  "A_cart cvec x \<omega> = (\<Sum>n\<in>UNIV. cis (-(cvec \<omega> \<bullet> (x $ n))))"

definition U_cart ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> real"
where
  "U_cart cvec gain x \<omega> = gain \<omega> * (cmod (A_cart cvec x \<omega>))\<^sup>2"

definition gain_from_element ::
  "(angle \<Rightarrow> real) \<Rightarrow> angle \<Rightarrow> real"
where
  "gain_from_element e \<omega> = (e \<omega>)\<^sup>2"

subsection \<open>Steered wave-vector\<close>

text \<open>
  The paper's phase term is

    exp(-i * ([k(\<omega>) - k(\<omega>s)] \<sqdot> r'_n(x))).

  Thus the generic @{term cvec} used by @{term A_cart} should be instantiated
  as @{term "cvec_steered kvec \<omega>s"}.
\<close>

definition cvec_steered ::
  "(angle \<Rightarrow> planar) \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> planar"
where
  "cvec_steered kvec \<omega>s \<omega> = kvec \<omega> - kvec \<omega>s"

lemma A_cart_steered_expand:
  "A_cart (cvec_steered kvec \<omega>s) x \<omega> =
     (\<Sum>n\<in>UNIV. cis (-((kvec \<omega> - kvec \<omega>s) \<bullet> (x $ n))))"
  unfolding A_cart_def cvec_steered_def
  by simp

lemma U_cart_paper_expand:
  "U_cart (cvec_steered kvec \<omega>s) (gain_from_element e) x \<omega> =
     (e \<omega>)\<^sup>2 *
       (cmod (\<Sum>n\<in>UNIV. cis (-((kvec \<omega> - kvec \<omega>s) \<bullet> (x $ n)))))\<^sup>2"
  unfolding U_cart_def A_cart_def cvec_steered_def gain_from_element_def
  by simp

subsection \<open>Derivatives of the Cartesian amplitude and objective\<close>

text \<open>
  Since @{typ angle} is @{typ "real^2"}, derivatives with respect to the
  angle variable are Fréchet derivatives.

  If

    @{term "(cvec has_derivative dc) (at \<omega>)"}

  then @{term dc} is the linear derivative map of @{term cvec} at @{term \<omega>}.
  Similarly, if

    @{term "(gain has_derivative dgain) (at \<omega>)"}

  then @{term dgain} is the linear derivative map of @{term gain} at @{term \<omega>}.
\<close>

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

lemma differentiable_A_cart:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc   :: "angle \<Rightarrow> planar"
    and x    :: "planar^'n"
    and \<omega>    :: angle
  assumes cvec_deriv:
    "(cvec has_derivative dc) (at \<omega>)"
  shows
    "(\<lambda>\<omega>. A_cart cvec x \<omega>) differentiable (at \<omega>)"
  using has_derivative_A_cart[OF cvec_deriv]
  unfolding differentiable_def
  by blast

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

lemma differentiable_U_cart:
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
    "(\<lambda>\<omega>. U_cart cvec gain x \<omega>) differentiable (at \<omega>)"
  using has_derivative_U_cart[OF cvec_deriv gain_deriv]
  unfolding differentiable_def
  by blast

subsection \<open>Derivative of the squared element factor\<close>

lemma has_derivative_gain_from_element:
  fixes e  :: "angle \<Rightarrow> real"
    and de :: "angle \<Rightarrow> real"
    and \<omega>  :: angle
  assumes e_deriv:
    "(e has_derivative de) (at \<omega>)"
  shows
    "((gain_from_element e) has_derivative (\<lambda>h. 2 * e \<omega> * de h)) (at \<omega>)"
proof -
  have h:
    "((\<lambda>\<omega>. e \<omega> * e \<omega>) has_derivative (\<lambda>h. e \<omega> * de h + de h * e \<omega>)) (at \<omega>)"
    using e_deriv e_deriv
    by (rule has_derivative_mult)
  then show ?thesis
    unfolding gain_from_element_def
    by (simp add: power2_eq_square algebra_simps)
qed

subsection \<open>Steered derivative theorems\<close>

lemma has_derivative_cvec_steered:
  fixes kvec :: "angle \<Rightarrow> planar"
    and dk   :: "angle \<Rightarrow> planar"
    and \<omega> \<omega>s :: angle
  assumes kvec_deriv:
    "(kvec has_derivative dk) (at \<omega>)"
  shows
    "((cvec_steered kvec \<omega>s) has_derivative dk) (at \<omega>)"
  unfolding cvec_steered_def
  using kvec_deriv
  by (auto intro!: derivative_eq_intros)

lemma has_derivative_U_cart_steered:
  fixes kvec  :: "angle \<Rightarrow> planar"
    and dk    :: "angle \<Rightarrow> planar"
    and gain  :: "angle \<Rightarrow> real"
    and dgain :: "angle \<Rightarrow> real"
    and x     :: "planar^'n"
    and \<omega> \<omega>s  :: angle
  assumes kvec_deriv:
    "(kvec has_derivative dk) (at \<omega>)"
  assumes gain_deriv:
    "(gain has_derivative dgain) (at \<omega>)"
  shows
    "((\<lambda>\<omega>. U_cart (cvec_steered kvec \<omega>s) gain x \<omega>)
       has_derivative
         dU_cart (cvec_steered kvec \<omega>s) dk gain dgain x \<omega>)
     (at \<omega>)"
proof -
  have cvec_deriv:
    "((cvec_steered kvec \<omega>s) has_derivative dk) (at \<omega>)"
    using kvec_deriv
    by (rule has_derivative_cvec_steered)

  show ?thesis
    using cvec_deriv gain_deriv
    by (rule has_derivative_U_cart)
qed

lemma has_derivative_U_cart_paper:
  fixes kvec :: "angle \<Rightarrow> planar"
    and dk   :: "angle \<Rightarrow> planar"
    and e    :: "angle \<Rightarrow> real"
    and de   :: "angle \<Rightarrow> real"
    and x    :: "planar^'n"
    and \<omega> \<omega>s :: angle
  assumes kvec_deriv:
    "(kvec has_derivative dk) (at \<omega>)"
  assumes e_deriv:
    "(e has_derivative de) (at \<omega>)"
  shows
    "((\<lambda>\<omega>. U_cart (cvec_steered kvec \<omega>s) (gain_from_element e) x \<omega>)
       has_derivative
         dU_cart (cvec_steered kvec \<omega>s) dk (gain_from_element e)
           (\<lambda>h. 2 * e \<omega> * de h) x \<omega>)
     (at \<omega>)"
proof -
  have gain_deriv:
    "((gain_from_element e) has_derivative (\<lambda>h. 2 * e \<omega> * de h)) (at \<omega>)"
    using e_deriv
    by (rule has_derivative_gain_from_element)

  show ?thesis
    using kvec_deriv gain_deriv
    by (rule has_derivative_U_cart_steered)
qed

subsection \<open>Line-direction derivatives\<close>

lemma has_vector_derivative_along_from_has_derivative:
  fixes F :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and F' :: "'a \<Rightarrow> 'b"
    and x h :: 'a
  assumes F_deriv:
    "(F has_derivative F') (at x)"
  shows
    "((\<lambda>t::real. F (x + t *\<^sub>R h))
       has_vector_derivative F' h)
     (at 0)"
proof -
  let ?path = "\<lambda>t::real. x + t *\<^sub>R h"

  have path_deriv:
    "(?path has_derivative (\<lambda>r. r *\<^sub>R h)) (at 0)"
    by (auto intro!: derivative_eq_intros)

  have comp:
    "((F \<circ> ?path) has_derivative (F' \<circ> (\<lambda>r. r *\<^sub>R h))) (at 0)"
    using path_deriv F_deriv
    by (simp add: diff_chain_at)

  have bl:
    "bounded_linear F'"
    using F_deriv
    unfolding has_derivative_def
    by simp

  have deriv_eq:
    "(F' \<circ> (\<lambda>r. r *\<^sub>R h)) = (\<lambda>r. r *\<^sub>R F' h)"
    by (simp add: bl comp_def linear_simps)

  show ?thesis
    unfolding has_vector_derivative_def
  proof -
    have "(\<lambda>t::real. F (x + t *\<^sub>R h)) = F \<circ> ?path"
      by auto
    then show "((\<lambda>t::real. F (x + t *\<^sub>R h))
        has_derivative (\<lambda>r. r *\<^sub>R F' h)) (at 0)"
      using comp deriv_eq
      by argo
  qed
qed

lemma has_vector_derivative_A_cart_along:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc   :: "angle \<Rightarrow> planar"
    and x    :: "planar^'n"
    and \<omega> h  :: angle
  assumes cvec_deriv:
    "(cvec has_derivative dc) (at \<omega>)"
  shows
    "((\<lambda>t::real. A_cart cvec x (\<omega> + t *\<^sub>R h))
       has_vector_derivative dA_cart cvec dc x \<omega> h)
     (at 0)"
  using has_derivative_A_cart[OF cvec_deriv]
  by (rule has_vector_derivative_along_from_has_derivative)

lemma has_vector_derivative_cmod_sq_A_cart_along:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc   :: "angle \<Rightarrow> planar"
    and x    :: "planar^'n"
    and \<omega> h  :: angle
  assumes cvec_deriv:
    "(cvec has_derivative dc) (at \<omega>)"
  shows
    "((\<lambda>t::real. (cmod (A_cart cvec x (\<omega> + t *\<^sub>R h)))\<^sup>2)
       has_vector_derivative
         2 * Re (cnj (A_cart cvec x \<omega>) * dA_cart cvec dc x \<omega> h))
     (at 0)"
  using has_derivative_cmod_sq_A_cart[OF cvec_deriv]
  by (rule has_vector_derivative_along_from_has_derivative)

lemma has_vector_derivative_U_cart_along:
  fixes cvec :: "angle \<Rightarrow> planar"
    and dc    :: "angle \<Rightarrow> planar"
    and gain  :: "angle \<Rightarrow> real"
    and dgain :: "angle \<Rightarrow> real"
    and x     :: "planar^'n"
    and \<omega> h   :: angle
  assumes cvec_deriv:
    "(cvec has_derivative dc) (at \<omega>)"
  assumes gain_deriv:
    "(gain has_derivative dgain) (at \<omega>)"
  shows
    "((\<lambda>t::real. U_cart cvec gain x (\<omega> + t *\<^sub>R h))
       has_vector_derivative dU_cart cvec dc gain dgain x \<omega> h)
     (at 0)"
  using has_derivative_U_cart[OF cvec_deriv gain_deriv]
  by (rule has_vector_derivative_along_from_has_derivative)

lemma has_vector_derivative_U_cart_steered_along:
  fixes kvec  :: "angle \<Rightarrow> planar"
    and dk    :: "angle \<Rightarrow> planar"
    and gain  :: "angle \<Rightarrow> real"
    and dgain :: "angle \<Rightarrow> real"
    and x     :: "planar^'n"
    and \<omega> \<omega>s h :: angle
  assumes kvec_deriv:
    "(kvec has_derivative dk) (at \<omega>)"
  assumes gain_deriv:
    "(gain has_derivative dgain) (at \<omega>)"
  shows
    "((\<lambda>t::real. U_cart (cvec_steered kvec \<omega>s) gain x (\<omega> + t *\<^sub>R h))
       has_vector_derivative
         dU_cart (cvec_steered kvec \<omega>s) dk gain dgain x \<omega> h)
     (at 0)"
proof -
  have cvec_deriv:
    "((cvec_steered kvec \<omega>s) has_derivative dk) (at \<omega>)"
    using kvec_deriv
    by (rule has_derivative_cvec_steered)

  show ?thesis
    using cvec_deriv gain_deriv
    by (rule has_vector_derivative_U_cart_along)
qed

lemma has_vector_derivative_U_cart_paper_along:
  fixes kvec :: "angle \<Rightarrow> planar"
    and dk   :: "angle \<Rightarrow> planar"
    and e    :: "angle \<Rightarrow> real"
    and de   :: "angle \<Rightarrow> real"
    and x    :: "planar^'n"
    and \<omega> \<omega>s h :: angle
  assumes kvec_deriv:
    "(kvec has_derivative dk) (at \<omega>)"
  assumes e_deriv:
    "(e has_derivative de) (at \<omega>)"
  shows
    "((\<lambda>t::real. U_cart (cvec_steered kvec \<omega>s) (gain_from_element e) x (\<omega> + t *\<^sub>R h))
       has_vector_derivative
         dU_cart (cvec_steered kvec \<omega>s) dk (gain_from_element e)
           (\<lambda>h. 2 * e \<omega> * de h) x \<omega> h)
     (at 0)"
proof -
  have gain_deriv:
    "((gain_from_element e) has_derivative (\<lambda>h. 2 * e \<omega> * de h)) (at \<omega>)"
    using e_deriv
    by (rule has_derivative_gain_from_element)

  show ?thesis
    using kvec_deriv gain_deriv
    by (rule has_vector_derivative_U_cart_steered_along)
qed

section \<open>Open Feasible Family and Two-Triple Cover\<close>

subsection \<open>Proposition: Open Feasible Family (Constructive Core)\<close>

text \<open>
  The TeX proof of Proposition~(Open feasible family) has two parts:
  \<^item> an explicit configuration with exact nulling at \<open>\<omega>\<^sub>N\<close> (root-of-unity construction);
  \<^item> a continuity argument that an open neighborhood preserves strict inequalities
    (spacing and null bound).

  We formalize the first part now. The second part is packaged abstractly in
  Nonemptiness_Feasibility and will be instantiated later.
\<close>

lemma root_of_unity_nulling:
  fixes c :: planar and q s :: planar and L :: real
  assumes "N > 1"
    and cq: "c \<bullet> q = 1"
    and cs: "c \<bullet> s = 0"
  defines "p n \<equiv> (2*pi*real n/real N) *\<^sub>R q + (real (Suc n) * L) *\<^sub>R s"
  shows "(\<Sum>n<N. cis (-(c \<bullet> p n))) = 0"
proof -
  have sum_cis_roots_unity: "(\<Sum>n<N. cis (2*pi*real n/real N)) = 0"
  proof -
    define \<omega> where "\<omega> = cis (2 * pi / real N)"
    have deMoivre_local: "(cis a :: complex) ^ m = cis (real m * a)" for a m
      by (induction m) (simp_all add: algebra_simps cis_mult)
    have [simp]: "\<omega> \<noteq> 1"
    proof
      assume h: "\<omega> = 1"
      from h assms obtain k :: int where hk: "2 * pi / real N = 2 * pi * of_int k"
        by (auto simp: \<omega>_def complex_eq_iff cos_one_2pi_int mult_ac)
      from hk assms have "real N * of_int k = 1"
        by (simp add: field_simps)
      then have "of_int (int N * k) = (1::real)"
        by simp
      then have "int N * k = 1"
        using of_int_eq_iff by blast
      then have "int N = 1"
        by (auto simp: zmult_eq_1_iff)
      then show False
        using assms by simp
    qed

    have "(\<Sum>n<N. cis (2*pi*real n/real N)) = (\<Sum>n<N. \<omega> ^ n)"
    proof (rule sum.cong[OF refl])
      fix n assume "n \<in> {..<N}"
      have "cis (2*pi*real n/real N) = cis (real n * (2*pi/real N))"
        by (simp add: mult_ac)
      also have "\<dots> = (cis (2*pi/real N)) ^ n"
      proof -
        have hpow: "(cis (2*pi/real N) :: complex) ^ n = cis (real n * (2*pi/real N))"
          by (rule deMoivre_local)
        show ?thesis
          using hpow by simp
      qed
      finally show "cis (2*pi*real n/real N) = \<omega> ^ n"
        by (simp add: \<omega>_def)
    qed
    also have "\<dots> = (\<omega> ^ N - 1) / (\<omega> - 1)"
      by (subst geometric_sum[OF \<open>\<omega> \<noteq> 1\<close>]) simp
    also have "\<omega> ^ N - 1 = cis (2 * pi) - 1"
      using assms by (simp add: \<omega>_def deMoivre_local field_simps)
    also have "\<dots> = 0"
      by (simp add: complex_eq_iff)
    finally show ?thesis
      by simp
  qed
  have "c \<bullet> p n = 2*pi*real n/real N" for n
    by (simp only: p_def inner_add_right inner_scaleR_right cq cs)
  then have "(\<Sum>n<N. cis (-(c \<bullet> p n))) = (\<Sum>n<N. cis (-(2*pi*real n/real N)))"
    by simp
  also have "\<dots> = 0"
  proof -
    have "(\<Sum>n<N. cis (-(2*pi*real n/real N))) = (\<Sum>n<N. cnj (cis (2*pi*real n/real N)))"
      by (simp add: cis_cnj)
    also have "\<dots> = cnj (\<Sum>n<N. cis (2*pi*real n/real N))"
      by (simp only: cnj_sum)
    also have "\<dots> = 0"
      using sum_cis_roots_unity by simp
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

theorem prop_openfeas:
  fixes cvec :: "angle \<Rightarrow> planar" and \<omega>N :: angle
  assumes "N > 1" and "cvec \<omega>N \<noteq> 0"
  shows "\<exists>ps::planar list. length ps = N \<and> array_factor cvec ps \<omega>N = 0"
proof -
  obtain q s :: planar
    where cq: "cvec \<omega>N \<bullet> q = 1" and cs: "cvec \<omega>N \<bullet> s = 0"
    by (meson assms(2) hyperplane_eq_Ex)
  define L :: real where "L = 1"
  define p where "p n = (2*pi*real n/real N) *\<^sub>R q + (real (Suc n) * L) *\<^sub>R s" for n
  define ps where "ps = map p [0..<N]"

  have hlen: "length ps = N"
    by (simp add: ps_def)

  have hsum: "(\<Sum>n<N. cis (-(cvec \<omega>N \<bullet> p n))) = 0"
    using root_of_unity_nulling[OF assms(1) cq cs, of L] by (simp add: p_def)

  have "array_factor cvec ps \<omega>N = 0"
  proof -
    have "array_factor cvec ps \<omega>N = sum_list (map (\<lambda>x. cis (-(cvec \<omega>N \<bullet> x))) ps)"
      by (simp add: array_factor_def)
    also have "\<dots> = sum_list (map (\<lambda>n. cis (-(cvec \<omega>N \<bullet> p n))) [0..<N])"
      by (simp add: ps_def o_def)
    also have "\<dots> = sum (\<lambda>n. cis (-(cvec \<omega>N \<bullet> p n))) (set [0..<N])"
      by (simp add: interv_sum_list_conv_sum_set_nat)
    also have "\<dots> = (\<Sum>n<N. cis (-(cvec \<omega>N \<bullet> p n)))"
      by (simp add: atLeast0LessThan)
    also have "\<dots> = 0"
      by (rule hsum)
    finally show ?thesis.
  qed

  then show ?thesis
    using hlen by (intro exI[of _ ps], blast)
qed

text \<open>
  The combinatorial heart of the two-triple cover (TeX Lemma~(Two-triple cover)).
  For a noncollinear triple \<open>T\<close> the set \<open>B(T) \<subseteq> S\<^sup>1\<close> of directions orthogonal to an
  edge is finite. Rotating the second triple by \<open>\<alpha>\<close> sends \<open>B(T\<^sub>2)\<close> to \<open>B(T\<^sub>2)+\<alpha>\<close>; the
  "bad" rotations are the finite set \<open>{\<beta>-\<gamma> : \<beta>\<in>B(T\<^sub>1), \<gamma>\<in>B(T\<^sub>2)}\<close>. Choosing \<open>\<alpha>\<close>
  outside it makes \<open>B(T\<^sub>1)\<close> and \<open>B(T\<^sub>2)+\<alpha>\<close> disjoint, so every direction is good for at
  least one triple. We prove this avoidance fact; the geometric packaging of the
  triples and the working set \<open>V\<close> is downstream openness.
\<close>

lemma lem_twotriplecover:
  fixes B1 B2 :: "real set"
  assumes "finite B1" and "finite B2"
  shows "\<exists>\<alpha>. \<forall>\<beta>\<in>B1. \<forall>\<gamma>\<in>B2. \<beta> \<noteq> \<gamma> + \<alpha>"
proof -
  have "finite ((\<lambda>(\<beta>, \<gamma>). \<beta> - \<gamma>) ` (B1 \<times> B2))"
    using assms by simp
  then obtain \<alpha> where "\<alpha> \<notin> (\<lambda>(\<beta>, \<gamma>). \<beta> - \<gamma>) ` (B1 \<times> B2)"
    using ex_new_if_finite[OF infinite_UNIV_char_0] by blast
  then show ?thesis by force
qed


section \<open>Global Lemma for @{term "cvec = 0"}\<close>

text \<open>
  The norm-comparison core of the TeX argument: a point \<open>c\<close> on a sphere lying on the
  secant line through two sphere points \<open>a \<noteq> b\<close>, \<open>c = b + \<alpha>(a - b)\<close>, must be one of
  the endpoints (\<open>\<alpha> \<in> {0,1}\<close>). In the paper this yields \<open>\<alpha>(1-\<alpha>)|k(\<omega>\<^sub>0)-k(\<omega>\<^sub>s)|\<^sup>2 = 0\<close>,
  hence \<open>k(\<omega>) \<in> {k(\<omega>\<^sub>0), k(\<omega>\<^sub>s)}\<close>.
\<close>

lemma secant_sphere:
  fixes a b c :: "'a::real_inner" and \<rho> \<alpha> :: real
  assumes na: "norm a = \<rho>" and nb: "norm b = \<rho>" and nc: "norm c = \<rho>"
    and hc: "c = b + \<alpha> *\<^sub>R (a - b)" and hab: "a \<noteq> b"
  shows "\<alpha> = 0 \<or> \<alpha> = 1"
proof -
  have expand: "\<And>t::real. (norm (b + t *\<^sub>R (a - b)))\<^sup>2
                  = (norm b)\<^sup>2 + 2*t*(b \<bullet> (a - b)) + t\<^sup>2 * (norm (a - b))\<^sup>2"
    by (simp only: power2_norm_eq_inner)
       (simp only: inner_add_left inner_add_right inner_scaleR_left inner_scaleR_right
                  inner_diff_left inner_diff_right inner_commute power2_eq_square)
  have anz: "a - b \<noteq> 0" using hab by simp
  then have nz: "(norm (a - b))\<^sup>2 > 0" by simp
  have hF1: "2*\<alpha>*(b \<bullet> (a - b)) + \<alpha>\<^sup>2 * (norm (a - b))\<^sup>2 = 0"
  proof -
    have "(norm c)\<^sup>2 = (norm b)\<^sup>2 + 2*\<alpha>*(b \<bullet> (a - b)) + \<alpha>\<^sup>2 * (norm (a - b))\<^sup>2"
      using hc expand[of \<alpha>] by simp
    then show ?thesis using na nb nc by simp
  qed
  have hF2: "2*(b \<bullet> (a - b)) + (norm (a - b))\<^sup>2 = 0"
  proof -
    have "(norm a)\<^sup>2 = (norm (b + 1 *\<^sub>R (a - b)))\<^sup>2" by simp
    also have "\<dots> = (norm b)\<^sup>2 + 2*(b \<bullet> (a - b)) + (norm (a - b))\<^sup>2"
      using expand[of 1] by simp
    finally show ?thesis using na nb by simp
  qed
  have "(\<alpha>\<^sup>2 - \<alpha>) * (norm (a - b))\<^sup>2
          = (2*\<alpha>*(b \<bullet> (a - b)) + \<alpha>\<^sup>2 * (norm (a - b))\<^sup>2)
            - \<alpha> * (2*(b \<bullet> (a - b)) + (norm (a - b))\<^sup>2)"
    by (simp add: algebra_simps)
  also have "\<dots> = 0" using hF1 hF2 by simp
  finally have "(\<alpha>\<^sup>2 - \<alpha>) * (norm (a - b))\<^sup>2 = 0" .
  with nz have "\<alpha>\<^sup>2 - \<alpha> = 0" by simp
  then have "\<alpha> * (\<alpha> - 1) = 0" by (simp only: power2_eq_square algebra_simps)
  then show ?thesis by simp
qed

text \<open>
  The 3-D wavevector \<open>k(\<omega>) = (sin\<theta> cos\<phi>, sin\<theta> sin\<phi>, cos\<theta>)\<close> (unit-normalized; the
  physical scale \<open>2\<pi>/\<lambda>\<close> is irrelevant to vanishing of \<open>cvec\<close>), modeled as a real
  triple so its components are plain projections. The planar effective wavevector
  \<open>cvec\<^sub>0\<close> is the paper's \<open>(\<Delta>k\<^sub>x + D\<^sub>x \<Delta>k\<^sub>z, \<Delta>k\<^sub>y + D\<^sub>y \<Delta>k\<^sub>z)\<close> with beam-lift constants
  \<open>D\<^sub>x = (k\<^sub>x(\<omega>\<^sub>0)-k\<^sub>x(\<omega>\<^sub>s))/(k\<^sub>z(\<omega>\<^sub>s)-k\<^sub>z(\<omega>\<^sub>0))\<close>, similarly \<open>D\<^sub>y\<close>.
\<close>

type_synonym wavevec = "real \<times> real \<times> real"

definition kx :: "angle \<Rightarrow> real" where "kx \<omega> = sin (\<omega>$1) * cos (\<omega>$2)"
definition ky :: "angle \<Rightarrow> real" where "ky \<omega> = sin (\<omega>$1) * sin (\<omega>$2)"
definition kz :: "angle \<Rightarrow> real" where "kz \<omega> = cos (\<omega>$1)"

definition kvec :: "angle \<Rightarrow> wavevec" where
  "kvec \<omega> = (kx \<omega>, ky \<omega>, kz \<omega>)"

lemma norm_kvec [simp]: "norm (kvec \<omega>) = 1"
proof -
  have s1: "(sin (\<omega>$1))\<^sup>2 = 1 - (cos (\<omega>$1))\<^sup>2"
    using sin_cos_squared_add[of "\<omega>$1"] by (metis add_diff_cancel_right')
  have s2: "(sin (\<omega>$2))\<^sup>2 = 1 - (cos (\<omega>$2))\<^sup>2"
    using sin_cos_squared_add[of "\<omega>$2"] by (metis add_diff_cancel_right')
  have "inner (kvec \<omega>) (kvec \<omega>) = (kx \<omega>)\<^sup>2 + (ky \<omega>)\<^sup>2 + (kz \<omega>)\<^sup>2"
    by (simp add: kvec_def inner_prod_def power2_eq_square)
  also have "\<dots> = 1"
    unfolding kx_def ky_def kz_def
    by (simp only: s1 s2 algebra_simps)
  finally have "inner (kvec \<omega>) (kvec \<omega>) = 1" .
  then have "(norm (kvec \<omega>))\<^sup>2 = 1"
    by (simp add: power2_norm_eq_inner)
  then show ?thesis
    using norm_ge_zero[of "kvec \<omega>"] by (auto simp: power2_eq_1_iff)
qed

definition cvec0 :: "angle \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> real \<times> real" where
  "cvec0 \<omega>0 \<omega>s \<omega> =
     ( (kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s),
       (ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s) )"

theorem lem_czero:
  fixes \<omega>0 \<omega>s \<omega> :: angle
  assumes hsep: "kz \<omega>0 \<noteq> kz \<omega>s"
    and hz: "cvec0 \<omega>0 \<omega>s \<omega> = (0, 0)"
  shows "kvec \<omega> = kvec \<omega>0 \<or> kvec \<omega> = kvec \<omega>s"
proof -
  define az where "az = kz \<omega>0 - kz \<omega>s"
  have az0: "az \<noteq> 0" using hsep by (simp add: az_def)
  have den0: "kz \<omega>s - kz \<omega>0 \<noteq> 0" using az0 by (simp add: az_def)
  have hz1: "(kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s) = 0"
    using hz by (simp add: cvec0_def)
  have hz2: "(ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s) = 0"
    using hz by (simp add: cvec0_def)
  define al where "al = (kz \<omega> - kz \<omega>s) / az"
  have X: "kx \<omega> - kx \<omega>s = al * (kx \<omega>0 - kx \<omega>s)"
    using hz1 az0 den0 by (simp add: al_def az_def field_simps)
  have Y: "ky \<omega> - ky \<omega>s = al * (ky \<omega>0 - ky \<omega>s)"
    using hz2 az0 den0 by (simp add: al_def az_def field_simps)
  have Z: "kz \<omega> - kz \<omega>s = al * (kz \<omega>0 - kz \<omega>s)"
    using az0 by (simp add: al_def az_def)
  have key: "kvec \<omega> = kvec \<omega>s + al *\<^sub>R (kvec \<omega>0 - kvec \<omega>s)"
    using X Y Z by (simp add: kvec_def prod_eq_iff algebra_simps)
  have hne: "kvec \<omega>0 \<noteq> kvec \<omega>s"
    using az0 by (auto simp: kvec_def az_def)
  from secant_sphere[OF norm_kvec norm_kvec norm_kvec key hne]
  have "al = 0 \<or> al = 1" .
  then show ?thesis
  proof
    assume "al = 0"
    then show ?thesis using key by simp
  next
    assume "al = 1"
    then show ?thesis using key by (simp add: algebra_simps)
  qed
qed


section \<open>Regular-Stratum Zeros of the Array Factor\<close>

theorem lem_Azero_surj:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes "odd CARD('n)" "cvec \<omega> \<noteq> 0" "af cvec x \<omega> = 0"
  shows "\<exists>h. dxA cvec x \<omega> h = 1"
  using dxA_surj[OF assms, of 1] .

subsection \<open>Transversality Predicate (Minimal)\<close>

definition transverse0_on ::
  "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "transverse0_on f S \<longleftrightarrow>
     (\<forall>x\<in>S. f x = 0 \<longrightarrow> (\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f'))"

lemma surj_comp:
  assumes "surj f" and "surj g"
  shows "surj (g \<circ> f)"
  using assms unfolding surj_def
  by (metis comp_apply) 

lemma has_derivative_cplx_r2_within:
  fixes z :: complex
  shows "(cplx_r2 has_derivative cplx_r2) (at z within S)"
  by (simp add: has_derivative_at_withinI has_derivative_cplx_r2)

definition r2_cplx :: "real^2 \<Rightarrow> complex" where
  "r2_cplx v = Complex (v $ 1) (v $ 2)"

lemma r2_cplx_cplx_r2 [simp]: "r2_cplx (cplx_r2 z) = z"
  unfolding r2_cplx_def cplx_r2_def
  by (simp add: complex_eq_iff vec_eq_iff forall_2)

lemma cplx_r2_r2_cplx [simp]: "cplx_r2 (r2_cplx v) = v"
  unfolding r2_cplx_def cplx_r2_def
  by (simp add: vec_eq_iff forall_2)

lemma bounded_linear_r2_cplx: "bounded_linear r2_cplx"
  unfolding r2_cplx_def
  by (intro bounded_linearI')
     (simp_all add: vec_eq_iff forall_2 complex_eq_iff)

lemma has_derivative_r2_cplx [derivative_intros]:
  fixes v :: "real^2"
  shows "(r2_cplx has_derivative r2_cplx) (at v)"
  by (simp only: bounded_linear_r2_cplx bounded_linear_imp_has_derivative)

lemma surj_r2_cplx: "surj r2_cplx"
  by (metis UNIV_eq_I r2_cplx_cplx_r2 rangeI)

lemma regular_value_on_cplx_r2_comp:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
  shows "regular_value_on (\<lambda>z. cplx_r2 (A z)) (V\<times>\<Omega>reg) 0"
proof (rule regular_value_onI)
  fix z
  assume zS: "z \<in> V \<times> \<Omega>reg"
  assume hz: "(\<lambda>z. cplx_r2 (A z)) z = 0"
  then have Az0: "A z = 0"
    by (simp only: cplx_r2_0_iff)
  from joint_trans zS Az0 obtain F where
    derA: "((\<lambda>z. A z) has_derivative F) (at z within V \<times> \<Omega>reg)"
    and surjF: "surj F"
    by blast
  have derc: "(cplx_r2 has_derivative cplx_r2) (at (A z) within UNIV)"
    by (simp add: has_derivative_cplx_r2)
  have derG:
      "((\<lambda>z. cplx_r2 (A z)) has_derivative (cplx_r2 \<circ> F)) (at z within V \<times> \<Omega>reg)"
    using has_derivative_compose[OF derA derc]
    by (simp add: o_def)
  have "surj (cplx_r2 \<circ> F)"
    by (rule surj_comp[OF surjF surj_cplx_r2])
  then show "\<exists>f'. ((\<lambda>z. cplx_r2 (A z)) has_derivative f') (at z within V \<times> \<Omega>reg) \<and> surj f'"
    using derG by blast
qed

text \<open>
  \<open>C\<^sup>1\<close>-lifting: if \<open>A\<close> is continuously Fr\<a>chet-differentiable on \<open>S\<close> (a continuous
  blinfun derivative), so is \<open>cplx_r2 \<circ> A\<close>, since \<open>cplx_r2\<close> is bounded-linear. This
  is exactly the smoothness input {thm charts_core_Nn} needs (the chart construction
  rests on the inverse function theorem, hence on \<open>C\<^sup>1\<close>, not merely a surjective
  derivative at the zeros).
\<close>

lemma C1_cplx_r2_comp:
  fixes A :: "'a::euclidean_space \<Rightarrow> complex" and S :: "'a set"
  assumes "\<exists>A'. (\<forall>z\<in>S. (A has_derivative blinfun_apply (A' z)) (at z)) \<and> continuous_on S A'"
  shows "\<exists>G'. (\<forall>z\<in>S. ((\<lambda>z. cplx_r2 (A z)) has_derivative blinfun_apply (G' z)) (at z))
                \<and> continuous_on S G'"
proof -
  obtain A' :: "'a \<Rightarrow> ('a \<Rightarrow>\<^sub>L complex)"
    where A'd: "\<And>z. z\<in>S \<Longrightarrow> (A has_derivative blinfun_apply (A' z)) (at z)"
      and A'c: "continuous_on S A'"
    using assms by blast
  define cr2 :: "complex \<Rightarrow>\<^sub>L (real^2)" where "cr2 = Blinfun cplx_r2"
  have cr2_apply: "blinfun_apply cr2 = cplx_r2"
    unfolding cr2_def by (rule bounded_linear_Blinfun_apply[OF bounded_linear_cplx_r2])
  define G' where "G' = (\<lambda>z. cr2 o\<^sub>L A' z)"
  have apply_eq: "blinfun_apply (G' z) = (\<lambda>h. cplx_r2 (blinfun_apply (A' z) h))" for z
    using G'_def cr2_apply by fastforce
  have der: "((\<lambda>z. cplx_r2 (A z)) has_derivative blinfun_apply (G' z)) (at z)"
    if z: "z \<in> S" for z
    using bounded_linear.has_derivative[OF bounded_linear_cplx_r2 A'd[OF z]]
    by (simp add: apply_eq)
  have cont: "continuous_on S G'"
    unfolding G'_def
    using bounded_bilinear.bounded_linear_right[OF bounded_bilinear_blinfun_compose]
          A'c bounded_linear.continuous_on by blast
  show ?thesis using der cont by blast
qed

lemma transverse0_on_cplx_r2_iff:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  shows "transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg \<longleftrightarrow>
         transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg"
  unfolding transverse0_on_def
proof
  assume H: "\<forall>\<omega>\<in>\<Omega>reg.
      cplx_r2 (A (x, \<omega>)) = 0 \<longrightarrow>
      (\<exists>f'. ((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f')"
  show "\<forall>\<omega>\<in>\<Omega>reg.
      A (x, \<omega>) = 0 \<longrightarrow>
      (\<exists>f'. ((\<lambda>\<omega>. A (x, \<omega>)) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f')"
  proof (intro ballI impI)
    fix \<omega> :: "real^2"
    assume w: "\<omega> \<in> \<Omega>reg"
    assume Az0: "A (x, \<omega>) = 0"
    have "cplx_r2 (A (x, \<omega>)) = 0"
      using Az0 by (simp only: cplx_r2_0_iff)
	    then obtain f' where der:
	        "((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative f') (at \<omega> within \<Omega>reg)"
	      and surj_f': "surj f'"
	      using H w by blast
            have der_r2: "(r2_cplx has_derivative r2_cplx) (at (cplx_r2 (A (x, \<omega>))) within UNIV)"
              by (simp add: has_derivative_at_withinI has_derivative_r2_cplx)
            have derA:
                "((\<lambda>\<omega>. A (x, \<omega>)) has_derivative (r2_cplx \<circ> f')) (at \<omega> within \<Omega>reg)"
              using has_derivative_compose[OF der der_r2]
              by (simp add: o_def)
            have surjF: "surj (r2_cplx \<circ> f')"
              by (rule surj_comp[OF surj_f' surj_r2_cplx])
	    show "\<exists>f'. ((\<lambda>\<omega>. A (x, \<omega>)) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f'"
	      using derA surjF by blast
	  qed
next
  assume H: "\<forall>\<omega>\<in>\<Omega>reg.
      A (x, \<omega>) = 0 \<longrightarrow>
      (\<exists>f'. ((\<lambda>\<omega>. A (x, \<omega>)) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f')"
  show "\<forall>\<omega>\<in>\<Omega>reg.
      cplx_r2 (A (x, \<omega>)) = 0 \<longrightarrow>
      (\<exists>f'. ((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f')"
  proof (intro ballI impI)
    fix \<omega> :: "real^2"
    assume w: "\<omega> \<in> \<Omega>reg"
    assume hz: "cplx_r2 (A (x, \<omega>)) = 0"
    then have Az0: "A (x, \<omega>) = 0"
      by (simp only: cplx_r2_0_iff)
    from H w Az0 obtain F where derA:
        "((\<lambda>\<omega>. A (x, \<omega>)) has_derivative F) (at \<omega> within \<Omega>reg)"
      and surjF: "surj F"
      by blast
    have derc: "(cplx_r2 has_derivative cplx_r2) (at (A (x, \<omega>)) within UNIV)"
      by (simp add: has_derivative_cplx_r2)
    have derG:
        "((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative (cplx_r2 \<circ> F)) (at \<omega> within \<Omega>reg)"
      using has_derivative_compose[OF derA derc] by (simp add: o_def)
    have "surj (cplx_r2 \<circ> F)"
      by (rule surj_comp[OF surjF surj_cplx_r2])
    then show "\<exists>f'. ((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f'"
      using derG by blast
  qed
qed


text \<open>
  The Euclidean chart pipeline in \<open>Parametric_Transversality_Euclidean_Base\<close>
  is typed for a \<^emph>\<open>single-level\<close> parameter space \<open>real^'m\<close>, and records the
  rank defect as \<open>rank (matrix \<dots>) < CARD('m)\<close> --- which only type-checks for
  \<open>real^'m\<close> (the entries must form a \<^class>\<open>field\<close>). Here the parameter space is the
  product \<open>(real^2)^'n\<close>, so we record the two pipeline obligations at that type, with
  the rank defect expressed coordinate-free as \<open>\<not> surj\<close>. These are the genuine
  (still-open) analytic obligations for the antenna parameter space; they will be
  discharged from the general regular-value theorem.
\<close>

text \<open>
  Algebraic core of the chart construction. At a regular zero \<open>(x,\<omega>)\<close> of \<open>G\<close> the
  full derivative \<open>DG = [D\<^sub>x G \<bar> D\<^sub>\<omega> G]\<close> is surjective, so the zero set is a manifold
  whose tangent space is \<open>ker DG\<close>. The projection \<open>\<pi>\<^sub>V\<close> to the \<open>x\<close>-factor, restricted
  to this tangent space, is surjective (the chart point is \<^emph>\<open>regular\<close> for \<open>\<pi>\<^sub>V\<close>)
  \<^emph>\<open>iff\<close> the \<open>\<omega>\<close>-partial \<open>D\<^sub>\<omega> G\<close> is surjective. Equivalently: the chart point is
  \<open>\<pi>\<^sub>V\<close>-\<^emph>\<open>critical\<close> exactly when the \<open>\<omega>\<close>-derivative degenerates --- which is precisely
  the \<^emph>\<open>bad\<close> set covered by \<open>charts_core_Nn\<close> and fed to
  \<open>negligible_singular_image_2n\<close>. The proof is pure linear algebra: \<open>\<pi>\<^sub>V (ker DG)\<close>
  is everything iff \<open>range D\<^sub>x G \<subseteq> range D\<^sub>\<omega> G\<close>, which under joint surjectivity is
  equivalent to \<open>range D\<^sub>\<omega> G = UNIV\<close>.
\<close>

lemma proj_kernel_full_iff_partial_surj:
  fixes Dx :: "'a::euclidean_space \<Rightarrow> 'c::euclidean_space"
    and Dw :: "'b::euclidean_space \<Rightarrow> 'c"
  assumes linw: "linear Dw"
    and joint: "surj (\<lambda>p. Dx (fst p) + Dw (snd p))"
  shows "(fst ` {p. Dx (fst p) + Dw (snd p) = 0} = UNIV) \<longleftrightarrow> surj Dw"
proof
  assume L: "fst ` {p. Dx (fst p) + Dw (snd p) = 0} = UNIV"
  have "\<exists>y. c = Dw y" for c
  proof -
    obtain p where p: "Dx (fst p) + Dw (snd p) = c"
      by (metis (no_types, lifting) joint surj_def)
    have "fst p \<in> fst ` {p. Dx (fst p) + Dw (snd p) = 0}" using L by simp
    then obtain q where q: "fst q = fst p" "Dx (fst q) + Dw (snd q) = 0"
      by force
    have "Dx (fst p) + Dw (snd q) = 0" using q by simp
    hence Dxp: "Dx (fst p) = - Dw (snd q)"
      by (simp add: eq_neg_iff_add_eq_0)
    have "c = Dw (snd p) - Dw (snd q)" using p Dxp by simp
    also have "\<dots> = Dw (snd p - snd q)" using linw by (simp add: linear_diff)
    finally show ?thesis by blast
  qed
  thus "surj Dw" by (auto simp: surj_def)
next
  assume R: "surj Dw"
  have "a \<in> fst ` {p. Dx (fst p) + Dw (snd p) = 0}" for a
  proof -
    obtain b where b: "Dw b = - Dx a" using R by (metis surjD)
    have "Dx (fst (a, b)) + Dw (snd (a, b)) = 0" using b by simp
    thus ?thesis by (intro image_eqI[where x = "(a, b)"]) auto
  qed
  thus "fst ` {p. Dx (fst p) + Dw (snd p) = 0} = UNIV" by auto
qed

text \<open>
  Specialisation to a chart derivative. If \<open>D\<phi>\<close> is a linear parametrisation of the
  kernel of a surjective \<open>L = DG\<close> (\<open>range D\<phi> = ker L\<close>, as delivered by
  @{thm regular_value_local_chart}), then the \<open>x\<close>-factor projection \<open>fst \<circ> D\<phi>\<close> is
  surjective \<^emph>\<open>iff\<close> the \<open>\<omega>\<close>-partial \<open>b \<mapsto> L(0,b)\<close> is. This is the bridge from the
  chart's regularity for the projection to non-degeneracy of \<open>D\<^sub>\<omega> G\<close>.
\<close>

lemma chart_proj_surj_iff:
  fixes L :: "('a::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b"
    and D\<phi> :: "'a \<Rightarrow> ('a \<times> 'b)"
  assumes linL: "linear L" and surjL: "surj L"
    and rngD: "range D\<phi> = {w. L w = 0}"
  shows "surj (\<lambda>h. fst (D\<phi> h)) \<longleftrightarrow> surj (\<lambda>b. L (0, b))"
proof -
  have split: "L (a, 0) + L (0, b) = L (a, b)" for a b
    by (metis add.commute add_0 add_Pair linL linear_add)
  have joint: "surj (\<lambda>p. L (fst p, 0) + L (0, snd p))"
  proof -
    have "(\<lambda>p. L (fst p, 0) + L (0, snd p)) = L"
      by (rule ext, metis split prod.collapse)
    thus ?thesis
      using surjL by presburger
  qed
  have lin_embed: "linear (\<lambda>b::'b. ((0::'a), b))"
    by (rule linearI) (auto simp: zero_prod_def)
  have linw: "linear (\<lambda>b. L (0, b))"
    using linear_compose[OF lin_embed linL] by (simp add: o_def)
  have key: "(fst ` {p. L (fst p, 0) + L (0, snd p) = 0} = UNIV) \<longleftrightarrow> surj (\<lambda>b. L (0,b))"
    by (rule proj_kernel_full_iff_partial_surj[OF linw joint])
  have setEq: "{p. L (fst p, 0) + L (0, snd p) = 0} = {w. L w = 0}"
    using split by auto 
  have rangeEq: "range (\<lambda>h. fst (D\<phi> h)) = fst ` {w. L w = 0}"
    by (metis image_image rngD)
  show ?thesis
    using key by (simp only: setEq flip: rangeEq)
qed

lemma charts_core_Nn:
  fixes V :: "((real^2)^'n) set" and \<Omega> :: "(real^2) set"
    and G :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^2)"
  assumes "open V" "V \<noteq> {}" "open \<Omega>"
    and "regular_value_on G (V\<times>\<Omega>) 0"
    and C1: "\<exists>G'. (\<forall>z\<in>V\<times>\<Omega>. (G has_derivative blinfun_apply (G' z)) (at z))
                  \<and> continuous_on (V\<times>\<Omega>) G'"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
             (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
           \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  sorry

text \<open>
  Sard for the antenna parameter space. \<open>baby_Sard\<close> is hard-typed to
  \<open>real^'m \<Rightarrow> real^'n\<close> (it uses \<^const>\<open>matrix\<close>/\<^const>\<open>rank\<close>), but our parameter
  space is the \<^emph>\<open>nested\<close> vector \<open>(real^2)^'n\<close>. Since \<open>(real^2)^'n\<close> has dimension
  \<open>2 * CARD('n)\<close>, the flat vector type of equal cardinality and the required
  \<^class>\<open>wellorder\<close> sort is \<open>real^('n bit0)\<close>. We build a linear isomorphism
  \<open>\<Phi> : (real^2)^'n \<cong> real^('n bit0)\<close> (from some index bijection, which exists by
  equal cardinality), transport the map through it, apply \<open>baby_Sard\<close>, and
  push negligibility back with \<open>negligible_locally_Lipschitz_image\<close>.
\<close>

lemma card_n2_bit0:
  "card (UNIV :: ('n::finite \<times> 2) set) = card (UNIV :: ('n bit0) set)"
  by simp

lemma exists_index_bij:
  "\<exists>\<beta> :: 'n::finite bit0 \<Rightarrow> ('n \<times> 2). bij \<beta>"
proof -
  have "card (UNIV :: ('n bit0) set) = card (UNIV :: ('n \<times> 2) set)"
    by (simp add: card_n2_bit0)
  then show ?thesis
    by (metis finite_same_card_bij finite_class.finite_UNIV)
qed

lemma negligible_singular_image_2n:
  fixes f :: "(real^2)^'n \<Rightarrow> (real^2)^'n"
    and f' :: "(real^2)^'n \<Rightarrow> ((real^2)^'n \<Rightarrow> (real^2)^'n)"
  assumes der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and ns:  "\<And>x. x \<in> S \<Longrightarrow> \<not> surj (f' x)"
  shows "negligible (f ` S)"
proof -
  obtain \<beta> :: "'n bit0 \<Rightarrow> ('n \<times> 2)" where b: "bij \<beta>"
    using exists_index_bij by blast
  define \<gamma> where "\<gamma> = inv \<beta>"
  have g\<beta>: "\<gamma> (\<beta> k) = k" for k unfolding \<gamma>_def
    by (metis b bij_inv_eq_iff)
  have \<beta>g: "\<beta> (\<gamma> p) = p" for p unfolding \<gamma>_def by (meson b bij_inv_eq_iff)

  define \<Phi> :: "(real^2)^'n \<Rightarrow> real^('n bit0)"
    where "\<Phi> v = (\<chi> k. (v $ fst (\<beta> k)) $ snd (\<beta> k))" for v
  define \<Psi> :: "real^('n bit0) \<Rightarrow> (real^2)^'n"
    where "\<Psi> w = (\<chi> i. \<chi> j. w $ \<gamma> (i,j))" for w

  have lin\<Phi>: "linear \<Phi>"
    by (rule linearI) (auto simp: \<Phi>_def vec_eq_iff)
  have lin\<Psi>: "linear \<Psi>"
    by (rule linearI) (auto simp: \<Psi>_def vec_eq_iff)

  have \<Psi>\<Phi>: "\<Psi> (\<Phi> v) = v" for v
    by (simp add: \<Phi>_def \<Psi>_def vec_eq_iff \<beta>g)
  have \<Phi>\<Psi>: "\<Phi> (\<Psi> w) = w" for w
    by (simp add: \<Phi>_def \<Psi>_def vec_eq_iff g\<beta>)

  define h :: "real^('n bit0) \<Rightarrow> real^('n bit0)"
    where "h = (\<lambda>y. \<Phi> (f (\<Psi> y)))"

  have der_h:
    "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow>
      (h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
  proof -
    fix y assume yS: "y \<in> \<Phi> ` S"
    have \<Psi>yS: "\<Psi> y \<in> S" using yS \<Psi>\<Phi> by auto
    have d\<Psi>: "(\<Psi> has_derivative \<Psi>) (at y within \<Phi> ` S)"
      using lin\<Psi> by (simp add: linear_imp_has_derivative)
    have df: "(f has_derivative f' (\<Psi> y)) (at (\<Psi> y) within \<Psi> ` (\<Phi> ` S))"
      by (metis (mono_tags, lifting) \<Psi>\<Phi> \<Psi>yS der has_derivative_subset image_iff image_subsetI)
    have d_f\<Psi>:
      "((\<lambda>y. f (\<Psi> y)) has_derivative (\<lambda>z. f' (\<Psi> y) (\<Psi> z))) (at y within \<Phi> ` S)"
      by (simp add: df has_derivative_in_compose lin\<Psi> linear_imp_has_derivative)
    have d\<Phi>: "(\<Phi> has_derivative \<Phi>) (at (f (\<Psi> y)) within (\<lambda>y. f (\<Psi> y)) ` (\<Phi> ` S))"
      using lin\<Phi> by (simp add: linear_imp_has_derivative)
    show "(h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
      unfolding h_def
      using has_derivative_in_compose[OF d_f\<Psi> d\<Phi>] by simp
  qed

  have ns_h:
    "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow> \<not> surj (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"
  proof
    fix y assume yS: "y \<in> \<Phi> ` S"
    assume sur: "surj (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"
    have \<Psi>yS: "\<Psi> y \<in> S" using yS \<Psi>\<Phi> by auto
    have "surj (f' (\<Psi> y))"
      unfolding surj_def
    proof clarify
      fix u :: "(real^2)^'n"
      from sur obtain z where z: "\<Phi> (f' (\<Psi> y) (\<Psi> z)) = \<Phi> u"
        by (metis (mono_tags, lifting) surj_def)
      show "\<exists>x. u = f' (\<Psi> y) x"
      proof (intro exI[where x = "\<Psi> z"])
        have "\<Psi> (\<Phi> (f' (\<Psi> y) (\<Psi> z))) = \<Psi> (\<Phi> u)" using z by simp
        then show "u = f' (\<Psi> y) (\<Psi> z)" by (simp add: \<Psi>\<Phi>)
      qed
    qed
    then show False using ns[OF \<Psi>yS] by contradiction
  qed

  have neg_h: "negligible (h ` (\<Phi> ` S))"
  proof (rule baby_Sard[where f = h and S = "\<Phi> ` S"
            and f' = "\<lambda>y z. \<Phi> (f' (\<Psi> y) (\<Psi> z))"])
    show "CARD('n bit0) \<le> CARD('n bit0)" by simp
    show "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow>
        (h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
      using der_h by blast
  next
    fix y assume yS: "y \<in> \<Phi> ` S"
    have \<Psi>yS: "\<Psi> y \<in> S" using yS \<Psi>\<Phi> by auto
    have linf': "linear (f' (\<Psi> y))" using der[OF \<Psi>yS] has_derivative_linear by blast
    have ling: "linear (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"
      using linear_compose[OF linear_compose[OF lin\<Psi> linf'] lin\<Phi>] by (simp add: o_def)
    have "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) \<noteq> CARD('n bit0)"
      by (metis full_rank_surjective ling matrix_vector_mul(2) ns_h yS)
    moreover have "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) \<le> CARD('n bit0)"
      by (metis min.idem rank_bound)
    ultimately show "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) < CARD('n bit0)" by simp
  qed

  have image_eq: "f ` S = \<Psi> ` (h ` (\<Phi> ` S))"
    unfolding h_def using \<Psi>\<Phi> by (smt (verit, best) image_cong image_image)

  show ?thesis
    unfolding image_eq
  proof (rule negligible_locally_Lipschitz_image[OF _ neg_h])
    show "DIM(real^('n bit0)) \<le> DIM((real^2)^'n)" by simp
  next
    fix x :: "real^('n bit0)" assume "x \<in> h ` (\<Phi> ` S)"
    obtain K where K: "\<And>z. norm (\<Psi> z) \<le> K * norm z"
      using lin\<Psi> linear_conv_bounded_linear bounded_linear.bounded linear_bounded by blast
    show "\<exists>T B. open T \<and> x \<in> T \<and>
            (\<forall>y\<in>(h ` (\<Phi> ` S)) \<inter> T. norm (\<Psi> y - \<Psi> x) \<le> B * norm (y - x))"
      by (rule exI[of _ UNIV], rule exI[of _ K], auto simp: linear_diff[OF lin\<Psi>, symmetric] K)
  qed
qed

lemma negligible_proj_charts_Nn:
  fixes charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
  assumes "\<And>i x. x \<in> Crit i \<Longrightarrow>
            ((fst \<circ> charts i) has_derivative blinfun_apply (D i x)) (at x within Crit i)"
    and "\<And>i x. x \<in> Crit i \<Longrightarrow> \<not> surj (blinfun_apply (D i x))"
  shows "negligible (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
proof -
  have "negligible ((fst \<circ> charts i) ` (Crit i))" for i
    by (rule negligible_singular_image_2n
          [where f = "fst \<circ> charts i" and S = "Crit i"
             and f' = "\<lambda>x. blinfun_apply (D i x)"])
       (use assms in blast)+
  then show ?thesis by (rule negligible_Union_nat)
qed

lemma parametric_transversality_negligible_complex:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}"
    and "open \<Omega>reg"
    and joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
    and A_C1: "\<exists>A'. (\<forall>z\<in>V\<times>\<Omega>reg. (A has_derivative blinfun_apply (A' z)) (at z))
                    \<and> continuous_on (V\<times>\<Omega>reg) A'"
  shows "negligible {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg}"
proof -
  have reg0: "regular_value_on (\<lambda>z. cplx_r2 (A z)) (V \<times> \<Omega>reg) 0"
    using regular_value_on_cplx_r2_comp[OF joint_trans] .
  have eq_bad:
      "{x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg}
       =
       {x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. cplx_r2 (A (x,\<omega>)) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. cplx_r2 (A (x,u))) has_derivative D) (at \<omega> within \<Omega>reg) \<and> surj D))}"
    unfolding transverse0_on_def by auto
  have bad_negligible:
    "negligible {x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. cplx_r2 (A (x,\<omega>)) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. cplx_r2 (A (x,u))) has_derivative D)
                       (at \<omega> within \<Omega>reg) \<and> surj D))}"
  proof -
    let ?G = "\<lambda>z. cplx_r2 (A z)"

    obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
       and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
       and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      where cover:
      "{x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. ?G (x,\<omega>) = 0 \<and>
          (\<not> (\<exists>D\<omega>. ((\<lambda>u. ?G (x,u)) has_derivative D\<omega>)
                    (at \<omega> within \<Omega>reg) \<and> surj D\<omega>))}
       \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der:
      "\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)"
      and rank:
      "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      using charts_core_Nn[OF assms(1) assms(2) assms(3) reg0
              C1_cplx_r2_comp[OF A_C1]]
      by blast

    have negligible_cover:
      "negligible (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    proof (rule negligible_proj_charts_Nn)
      show "\<And>i x. x \<in> Crit i \<Longrightarrow>
        ((fst \<circ> charts i) has_derivative blinfun_apply (D i x))
          (at x within Crit i)"
        using der by blast
      show "\<And>i x. x \<in> Crit i \<Longrightarrow> \<not> surj (blinfun_apply (D i x))"
        using rank by blast
    qed

    show ?thesis
      using negligible_cover cover negligible_subset by blast
  qed
  then have "negligible {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg}"
    by (simp add: eq_bad)
  then show ?thesis
    by (simp only: transverse0_on_cplx_r2_iff)
qed


section \<open>Negligible Sets Are Meager (meagerness engine for the bad-set branches)\<close>

text \<open>
  All four bad-set branches reduce, via parametric transversality, to: the bad set is
  contained in a countable union of \<^emph>\<open>lower-dimensional\<close> smooth images, which are
  Lebesgue-negligible (\<^const>\<open>negligible\<close>). This module is the reusable bridge from
  \<^const>\<open>negligible\<close> to the paper's \<^const>\<open>meager\<close>: a closed negligible subset of a
  Euclidean space is nowhere dense, and a set covered by countably many such pieces is
  meager. It is exactly the topological half of \<open>lem:smooth-chart-meager\<close>.
\<close>

lemma meager_nowhere_dense:
  fixes A :: "'a::topological_space set"
  assumes "nowhere_dense A"
  shows "meager A"
  using assms unfolding meager_def by (intro exI[of _ "\<lambda>_. A"]) auto

lemma nowhere_dense_closed_negligible:
  fixes A :: "'a::euclidean_space set"
  assumes "closed A" and "negligible A"
  shows "nowhere_dense A"
proof -
  have "interior A = {}"
  proof (rule ccontr)
    assume ne: "interior A \<noteq> {}"
    have "\<not> negligible (interior A)"
      by (rule open_not_negligible[OF open_interior ne])
    moreover have "negligible (interior A)"
      by (rule negligible_subset[OF assms(2) interior_subset])
    ultimately show False by blast
  qed
  with assms(1) show ?thesis
    by (simp only: nowhere_dense_def closure_closed)
qed

lemma meager_negligible_closed_cover:
  fixes A :: "'a::euclidean_space set"
  assumes "A \<subseteq> (\<Union>n::nat. K n)"
    and "\<And>n. closed (K n)" and "\<And>n. negligible (K n)"
  shows "meager A"
proof -
  have "meager (\<Union>n. K n)"
  proof (rule meager_Union_nat)
    fix n
    show "meager (K n)"
      by (rule meager_nowhere_dense[OF nowhere_dense_closed_negligible[OF assms(2) assms(3)]])
  qed
  then show ?thesis
    using assms(1) by (rule meager_subset[rotated])
qed

lemma nowhere_dense_mono:
  fixes A B :: "'a::topological_space set"
  assumes "B \<subseteq> A" and "nowhere_dense A"
  shows "nowhere_dense B"
proof -
  have "interior (closure B) \<subseteq> interior (closure A)"
    by (intro interior_mono closure_mono assms(1))
  with assms(2) show ?thesis
    by (simp only: nowhere_dense_def subset_empty)
qed

text \<open>
  The real-analytic nowhere-density engine. A continuous real function whose
  zero set has the \<^emph>\<open>identity property\<close> (vanishing on any nonempty open set forces
  it to vanish everywhere) and that is not identically zero has a nowhere-dense
  zero set: the level set \<open>{x. f x = 0}\<close> is closed, and an open subset of it would
  force \<open>f \<equiv> 0\<close>, so its interior is empty. The identity hypothesis is precisely
  the real-analytic identity theorem; for a finite exponential sum (the array
  factor, a trigonometric polynomial in \<open>x\<close>) it holds because vanishing on an
  open set kills all Taylor coefficients. This is the engine that discharges the
  \<open>slice_nowhere_dense\<close> input of \<open>prop_foldnonzero\<close>.
\<close>

lemma continuous_identity_zero_nowhere_dense:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes cont: "continuous_on UNIV f"
    and identity: "\<And>U. \<lbrakk>open U; U \<noteq> {}; \<forall>x\<in>U. f x = 0\<rbrakk> \<Longrightarrow> (\<forall>x. f x = 0)"
    and nontriv: "\<exists>x. f x \<noteq> 0"
  shows "nowhere_dense {x. f x = 0}"
proof -
  have clo: "closed {x. f x = 0}"
    using closed_Collect_eq[OF cont continuous_on_const] by simp
  have "interior {x. f x = 0} = {}"
  proof (rule ccontr)
    assume ne: "interior {x. f x = 0} \<noteq> {}"
    have "\<forall>x\<in>interior {x. f x = 0}. f x = 0"
      using interior_subset by auto
    from identity[OF open_interior ne this] nontriv show False by blast
  qed
  with clo show ?thesis
    by (simp only: nowhere_dense_def closure_closed)
qed

text \<open>
  Relative form used at the call site: the slice-zero set inside an open working
  set \<open>V\<close> is a subset of the global zero set, hence nowhere dense by
  \<open>nowhere_dense_mono\<close>. This produces exactly the \<open>slice_nowhere_dense\<close> hypothesis
  shape of \<open>prop_foldnonzero\<close>.
\<close>

lemma slice_zero_nowhere_dense:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and V :: "'a set"
  assumes cont: "continuous_on UNIV f"
    and identity: "\<And>U. \<lbrakk>open U; U \<noteq> {}; \<forall>x\<in>U. f x = 0\<rbrakk> \<Longrightarrow> (\<forall>x. f x = 0)"
    and nontriv: "\<exists>x. f x \<noteq> 0"
  shows "nowhere_dense {x \<in> V. f x = 0}"
  by (rule nowhere_dense_mono[OF _ continuous_identity_zero_nowhere_dense[OF cont identity nontriv]])
     auto

text \<open>
  The real-analytic identity theorem, supplied by \<^emph>\<open>1-D line restriction\<close>. If
  every line restriction \<open>t \<mapsto> f (a + t \<cdot> v)\<close> of a real function extends to an
  entire function of a complex variable, then \<open>f\<close> vanishing on a nonempty open
  set forces \<open>f \<equiv> 0\<close>: connect any target \<open>y\<close> to a base point \<open>a\<close> in the open set
  by a line; the entire restriction \<open>F\<close> vanishes on a real neighbourhood of \<open>0\<close>
  (the part of the line still inside the open set), so by \<open>analytic_continuation\<close>
  \<open>F \<equiv> 0\<close>, whence \<open>f y = F(1) = 0\<close>. For the array factor (a finite exponential
  sum) the line restrictions are \<open>cis\<close> of affine arguments, manifestly entire, so
  this discharges the \<open>identity\<close> hypothesis of the nowhere-density engine.
\<close>

lemma lines_entire_identity:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lines: "\<And>a v. \<exists>F. F holomorphic_on UNIV
                       \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v)))"
    and Uopen: "open U" and Une: "U \<noteq> {}" and Uzero: "\<forall>x\<in>U. f x = 0"
  shows "\<forall>y. f y = 0"
proof
  fix y
  obtain a where aU: "a \<in> U" using Une by blast
  show "f y = 0"
  proof (cases "y = a")
    case True thus ?thesis using aU Uzero by blast
  next
    case False
    define v where "v = y - a"
    have v0: "v \<noteq> 0" using False by (simp add: v_def)
    obtain F where Fhol: "F holomorphic_on UNIV"
      and Fval: "\<And>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v))"
      using lines by blast
    obtain e where e0: "e > 0" and eball: "ball a e \<subseteq> U"
      using Uopen aU open_contains_ball by blast
    define d where "d = e / norm v"
    have nv0: "norm v > 0" using v0 by simp
    have d0: "d > 0" using e0 nv0 by (simp add: d_def)
    have van: "F (complex_of_real t) = 0" if t: "\<bar>t\<bar> < d" for t
    proof -
      have "norm (t *\<^sub>R v) = \<bar>t\<bar> * norm v" by simp
      also have "\<dots> < d * norm v"
        using t nv0 by (simp add: mult_strict_right_mono)
      also have "\<dots> = e" using nv0 by (simp add: d_def)
      finally have "a + t *\<^sub>R v \<in> ball a e" by (simp add: dist_norm)
      hence "f (a + t *\<^sub>R v) = 0" using eball Uzero by blast
      thus ?thesis using Fval by simp
    qed
    define Z where "Z = complex_of_real ` {t. \<bar>t\<bar> < d}"
    have lim: "(0::complex) islimpt Z"
      unfolding islimpt_approachable
    proof (intro allI impI)
      fix \<epsilon>::real assume "\<epsilon> > 0"
      define t where "t = min d \<epsilon> / 2"
      have tpos: "t > 0" using d0 \<open>\<epsilon> > 0\<close> by (simp add: t_def)
      have "t < d" using d0 \<open>\<epsilon> > 0\<close> by (simp add: t_def)
      hence "complex_of_real t \<in> Z" using tpos by (auto simp: Z_def)
      moreover have "complex_of_real t \<noteq> 0" using tpos by simp
      moreover have "dist (complex_of_real t) 0 < \<epsilon>"
        using tpos \<open>\<epsilon> > 0\<close> by (simp add: t_def dist_norm)
      ultimately show "\<exists>x'\<in>Z. x' \<noteq> 0 \<and> dist x' 0 < \<epsilon>" by blast
    qed
    have F1: "F (complex_of_real 1) = 0"
    proof (rule analytic_continuation[OF Fhol open_UNIV connected_UNIV
              subset_UNIV UNIV_I lim _ UNIV_I])
      fix z assume "z \<in> Z"
      then obtain t where "z = complex_of_real t" "\<bar>t\<bar> < d" by (auto simp: Z_def)
      thus "F z = 0" using van by simp
    qed
    have "complex_of_real (f (a + 1 *\<^sub>R v)) = F (complex_of_real 1)"
      using Fval[of 1] by simp
    also have "\<dots> = 0" using F1 by simp
    finally have "f (a + v) = 0" by simp
    thus ?thesis by (simp add: v_def)
  qed
qed

text \<open>
  Combining the line-restriction identity theorem with the nowhere-density
  engine: a continuous, nontrivial \<open>f\<close> with entire line restrictions has a
  nowhere-dense zero set (relative to any working set \<open>V\<close>). This is the
  array-factor-shaped discharge of \<open>slice_nowhere_dense\<close>.
\<close>

lemma lines_entire_slice_nowhere_dense:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and V :: "'a set"
  assumes cont: "continuous_on UNIV f"
    and lines: "\<And>a v. \<exists>F. F holomorphic_on UNIV
                       \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v)))"
    and nontriv: "\<exists>x. f x \<noteq> 0"
  shows "nowhere_dense {x \<in> V. f x = 0}"
  by (rule slice_zero_nowhere_dense[OF cont _ nontriv])
     (rule lines_entire_identity[OF lines])


text \<open>
  Schwarz reflection holomorphicity: if \<open>G\<close> is entire then so is
  \<open>z \<mapsto> cnj (G (cnj z))\<close>. Real chain rule: \<open>cnj\<close> is \<^const>\<open>bounded_linear\<close>, so
  composing the field-derivative of \<open>G\<close> at \<open>cnj z\<close> on both sides conjugates
  it, giving the field derivative \<open>cnj D\<close> at \<open>z\<close>.
\<close>

lemma holomorphic_cnj_reflect:
  assumes "G holomorphic_on UNIV"
  shows "(\<lambda>z. cnj (G (cnj z))) holomorphic_on UNIV"
proof -
  have bl: "bounded_linear cnj" by (rule bounded_linear_cnj)
  have "(\<lambda>z. cnj (G (cnj z))) field_differentiable (at z)" for z :: complex
  proof -
    have "G field_differentiable (at (cnj z))"
      using assms by (simp add: holomorphic_on_def)
    then obtain D where D: "(G has_field_derivative D) (at (cnj z))"
      unfolding field_differentiable_def by blast
    have cnjd: "(cnj has_derivative cnj) (at z)"
      using bounded_linear.has_derivative[OF bl has_derivative_ident] by simp
    have Gd: "(G has_derivative (*) D) (at (cnj z))"
      by (rule has_field_derivative_imp_has_derivative[OF D])
    have comp1: "((\<lambda>w. G (cnj w)) has_derivative (\<lambda>x. D * cnj x)) (at z)"
      using diff_chain_at[OF cnjd Gd] by (simp add: o_def)
    have comp2: "((\<lambda>w. cnj (G (cnj w))) has_derivative (\<lambda>x. cnj (D * cnj x))) (at z)"
      using bounded_linear.has_derivative[OF bl comp1] by (simp add: o_def)
    have "(\<lambda>x. cnj (D * cnj x)) = (\<lambda>x. cnj D * x)"
      by simp
    with comp2 have "((\<lambda>w. cnj (G (cnj w))) has_derivative (\<lambda>x. cnj D * x)) (at z)" by simp
    then show "(\<lambda>z. cnj (G (cnj z))) field_differentiable (at z)"
      unfolding field_differentiable_def has_field_derivative_def by blast
  qed
  thus ?thesis
    by (auto simp: holomorphic_on_def intro: field_differentiable_at_within)
qed

subsection \<open>Concrete Modeling: the Array Factor has Entire Line Restrictions\<close>

text \<open>
  An algebra of functions whose line restrictions extend to entire functions of
  one complex variable. \<open>cline_entire\<close> is the complex-valued predicate,
  \<open>rline_entire\<close> the real-valued one (matching the \<open>lines\<close> hypothesis of
  \<open>lines_entire_identity\<close>). The array factor \<open>A_cart\<close> lands in \<open>cline_entire\<close>
  (a finite sum of \<open>cis\<close> of linear forms), and the power pattern \<open>U_cart\<close>
  (\<open>= g\<cdot>|A|\<^sup>2\<close>) lands in \<open>rline_entire\<close>, so its slice-zero set is nowhere dense
  once nontrivial. This turns the analytic \<open>identity\<close> hypothesis into the purely
  structural fact that each summand is \<open>cis\<close> of an affine function of the line
  parameter.
\<close>

definition cline_entire :: "('a::euclidean_space \<Rightarrow> complex) \<Rightarrow> bool" where
  "cline_entire g \<longleftrightarrow>
     (\<forall>a v. \<exists>G. G holomorphic_on UNIV
              \<and> (\<forall>t::real. G (complex_of_real t) = g (a + t *\<^sub>R v)))"

definition rline_entire :: "('a::euclidean_space \<Rightarrow> real) \<Rightarrow> bool" where
  "rline_entire f \<longleftrightarrow>
     (\<forall>a v. \<exists>F. F holomorphic_on UNIV
              \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v))))"

lemma cline_entire_const: "cline_entire (\<lambda>x. c)"
  unfolding cline_entire_def by (intro allI exI[of _ "\<lambda>_. c"]) simp

lemma cline_entire_add:
  assumes "cline_entire g1" and "cline_entire g2"
  shows "cline_entire (\<lambda>x. g1 x + g2 x)"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  obtain G1 where G1: "G1 holomorphic_on UNIV"
      "\<And>t::real. G1 (complex_of_real t) = g1 (a + t *\<^sub>R v)"
    using assms(1) unfolding cline_entire_def by blast
  obtain G2 where G2: "G2 holomorphic_on UNIV"
      "\<And>t::real. G2 (complex_of_real t) = g2 (a + t *\<^sub>R v)"
    using assms(2) unfolding cline_entire_def by blast
  show "\<exists>G. G holomorphic_on UNIV
            \<and> (\<forall>t::real. G (complex_of_real t) = g1 (a + t *\<^sub>R v) + g2 (a + t *\<^sub>R v))"
    by (intro exI[of _ "\<lambda>z. G1 z + G2 z"])
       (auto simp: G1 G2 intro!: holomorphic_intros)
qed

lemma cline_entire_mult:
  assumes "cline_entire g1" and "cline_entire g2"
  shows "cline_entire (\<lambda>x. g1 x * g2 x)"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  obtain G1 where G1: "G1 holomorphic_on UNIV"
      "\<And>t::real. G1 (complex_of_real t) = g1 (a + t *\<^sub>R v)"
    using assms(1) unfolding cline_entire_def by blast
  obtain G2 where G2: "G2 holomorphic_on UNIV"
      "\<And>t::real. G2 (complex_of_real t) = g2 (a + t *\<^sub>R v)"
    using assms(2) unfolding cline_entire_def by blast
  show "\<exists>G. G holomorphic_on UNIV
            \<and> (\<forall>t::real. G (complex_of_real t) = g1 (a + t *\<^sub>R v) * g2 (a + t *\<^sub>R v))"
    by (intro exI[of _ "\<lambda>z. G1 z * G2 z"])
       (auto simp: G1 G2 intro!: holomorphic_intros)
qed

lemma cline_entire_sum:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> cline_entire (g i)"
  shows "cline_entire (\<lambda>x. \<Sum>i\<in>I. g i x)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case using cline_entire_const[of 0] by simp
next
  case (insert i I)
  have "cline_entire (\<lambda>x. g i x + (\<Sum>j\<in>I. g j x))"
    by (rule cline_entire_add) (use insert in auto)
  thus ?case using insert.hyps by simp
qed

lemma cline_entire_cis_linear:
  fixes lf :: "'a::euclidean_space \<Rightarrow> real"
  assumes "bounded_linear lf"
  shows "cline_entire (\<lambda>x. cis (lf x))"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  have aff: "lf (a + t *\<^sub>R v) = lf a + t * lf v" for t::real
    by (simp add: assms linear_simps(1,5))
  let ?G = "\<lambda>z. exp (\<i> * (complex_of_real (lf a) + z * complex_of_real (lf v)))"
  have "?G holomorphic_on UNIV" by (intro holomorphic_intros)
  moreover have "?G (complex_of_real t) = cis (lf (a + t *\<^sub>R v))" for t::real
    by (simp add: aff cis_conv_exp algebra_simps flip: of_real_mult of_real_add)
  ultimately show "\<exists>G. G holomorphic_on UNIV
                       \<and> (\<forall>t::real. G (complex_of_real t) = cis (lf (a + t *\<^sub>R v)))"
    by blast
qed

lemma rline_entire_Re:
  assumes "cline_entire g"
  shows "rline_entire (\<lambda>x. Re (g x))"
  unfolding rline_entire_def
proof (intro allI)
  fix a v
  obtain G where G: "G holomorphic_on UNIV"
      "\<And>t::real. G (complex_of_real t) = g (a + t *\<^sub>R v)"
    using assms unfolding cline_entire_def by blast
  let ?F = "\<lambda>z. (G z + cnj (G (cnj z))) / 2"
  have "?F holomorphic_on UNIV"
    using G(1) holomorphic_cnj_reflect[OF G(1)] by (intro holomorphic_intros) auto
  moreover have "?F (complex_of_real t) = complex_of_real (Re (g (a + t *\<^sub>R v)))" for t::real
    by (simp add: G(2) complex_add_cnj)
  ultimately show "\<exists>F. F holomorphic_on UNIV
                       \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (Re (g (a + t *\<^sub>R v))))"
    by blast
qed

lemma rline_entire_Im:
  assumes "cline_entire g"
  shows "rline_entire (\<lambda>x. Im (g x))"
  unfolding rline_entire_def
proof (intro allI)
  fix a v
  obtain G where G: "G holomorphic_on UNIV"
      "\<And>t::real. G (complex_of_real t) = g (a + t *\<^sub>R v)"
    using assms unfolding cline_entire_def by blast
  let ?F = "\<lambda>z. (G z - cnj (G (cnj z))) / (2 * \<i>)"
  have "?F holomorphic_on UNIV"
    using G(1) holomorphic_cnj_reflect[OF G(1)] by (intro holomorphic_intros) auto
  moreover have "?F (complex_of_real t) = complex_of_real (Im (g (a + t *\<^sub>R v)))" for t::real
    by (simp add: G(2) complex_diff_cnj, simp add: mult.commute)
  ultimately show "\<exists>F. F holomorphic_on UNIV
                       \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (Im (g (a + t *\<^sub>R v))))"
    by blast
qed

lemma rline_entire_add:
  assumes "rline_entire f1" and "rline_entire f2"
  shows "rline_entire (\<lambda>x. f1 x + f2 x)"
  unfolding rline_entire_def
proof (intro allI)
  fix a v
  obtain F1 where F1: "F1 holomorphic_on UNIV"
      "\<And>t::real. F1 (complex_of_real t) = complex_of_real (f1 (a + t *\<^sub>R v))"
    using assms(1) unfolding rline_entire_def by blast
  obtain F2 where F2: "F2 holomorphic_on UNIV"
      "\<And>t::real. F2 (complex_of_real t) = complex_of_real (f2 (a + t *\<^sub>R v))"
    using assms(2) unfolding rline_entire_def by blast
  show "\<exists>F. F holomorphic_on UNIV
            \<and> (\<forall>t::real. F (complex_of_real t)
                        = complex_of_real (f1 (a + t *\<^sub>R v) + f2 (a + t *\<^sub>R v)))"
    by (intro exI[of _ "\<lambda>z. F1 z + F2 z"])
       (auto simp: F1 F2 intro!: holomorphic_intros)
qed

lemma rline_entire_mult:
  assumes "rline_entire f1" and "rline_entire f2"
  shows "rline_entire (\<lambda>x. f1 x * f2 x)"
  unfolding rline_entire_def
proof (intro allI)
  fix a v
  obtain F1 where F1: "F1 holomorphic_on UNIV"
      "\<And>t::real. F1 (complex_of_real t) = complex_of_real (f1 (a + t *\<^sub>R v))"
    using assms(1) unfolding rline_entire_def by blast
  obtain F2 where F2: "F2 holomorphic_on UNIV"
      "\<And>t::real. F2 (complex_of_real t) = complex_of_real (f2 (a + t *\<^sub>R v))"
    using assms(2) unfolding rline_entire_def by blast
  show "\<exists>F. F holomorphic_on UNIV
            \<and> (\<forall>t::real. F (complex_of_real t)
                        = complex_of_real (f1 (a + t *\<^sub>R v) * f2 (a + t *\<^sub>R v)))"
    by (intro exI[of _ "\<lambda>z. F1 z * F2 z"])
       (auto simp: F1 F2 intro!: holomorphic_intros)
qed

lemma rline_entire_scale:
  assumes "rline_entire f"
  shows "rline_entire (\<lambda>x. c * f x)"
  using rline_entire_mult[OF rline_entire_Re[OF cline_entire_const[of "complex_of_real c"]] assms]
  by simp

lemma rline_entire_cmod_sq:
  assumes "cline_entire g"
  shows "rline_entire (\<lambda>x. (cmod (g x))\<^sup>2)"
proof -
  have eq: "(\<lambda>x. (cmod (g x))\<^sup>2) = (\<lambda>x. Re (g x) * Re (g x) + Im (g x) * Im (g x))"
    by (rule ext, subst cmod_power2, simp add: power2_eq_square)
  show ?thesis
    unfolding eq by (intro rline_entire_add rline_entire_mult rline_entire_Re rline_entire_Im assms)
qed

text \<open>
  The array factor is a finite sum of \<open>cis\<close> of linear forms in \<open>x\<close>, hence has
  entire line restrictions; the power pattern \<open>U = g\<cdot>|A|\<^sup>2\<close> inherits this.
\<close>

lemma cline_entire_A_cart:
  fixes cvec :: "angle \<Rightarrow> planar" and \<omega> :: angle
  shows "cline_entire (\<lambda>x::planar^'n. A_cart cvec x \<omega>)"
  unfolding A_cart_def
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  have "bounded_linear (\<lambda>x::planar^'n. - (cvec \<omega> \<bullet> (x $ n)))"
    by (rule bounded_linear_minus
              [OF bounded_linear_compose[OF bounded_linear_inner_right bounded_linear_vec_nth]])
  thus "cline_entire (\<lambda>x::planar^'n. cis (- (cvec \<omega> \<bullet> (x $ n))))"
    by (rule cline_entire_cis_linear)
qed

lemma rline_entire_U_cart:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real" and \<omega> :: angle
  shows "rline_entire (\<lambda>x::planar^'n. U_cart cvec g x \<omega>)"
  unfolding U_cart_def
  by (rule rline_entire_scale[OF rline_entire_cmod_sq[OF cline_entire_A_cart]])

text \<open>
  Continuity of the array factor and the power pattern as functions of \<open>x\<close>
  (the \<open>lines_entire_slice_nowhere_dense\<close> engine also needs global continuity).
\<close>

lemma continuous_on_A_cart:
  fixes cvec :: "angle \<Rightarrow> planar" and \<omega> :: angle
  shows "continuous_on UNIV (\<lambda>x::planar^'n. A_cart cvec x \<omega>)"
  unfolding A_cart_def
  by (intro continuous_intros)

lemma continuous_on_U_cart:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real" and \<omega> :: angle
  shows "continuous_on UNIV (\<lambda>x::planar^'n. U_cart cvec g x \<omega>)"
  unfolding U_cart_def
  by (intro continuous_intros continuous_on_A_cart)

text \<open>
  Concrete discharge of \<open>slice_nowhere_dense\<close> for the power pattern: whenever the
  pattern is not identically zero (the nontriviality input), its zero set inside
  any working set \<open>V\<close> is nowhere dense.
\<close>

lemma U_cart_zero_nowhere_dense:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real"
    and \<omega> :: angle and V :: "(planar^'n) set"
  assumes nontriv: "\<exists>x::planar^'n. U_cart cvec g x \<omega> \<noteq> 0"
  shows "nowhere_dense {x \<in> V. U_cart cvec g x \<omega> = 0}"
proof (rule lines_entire_slice_nowhere_dense[OF continuous_on_U_cart _ nontriv])
  show "\<And>a v. \<exists>F. F holomorphic_on UNIV
                  \<and> (\<forall>t::real. F (complex_of_real t)
                              = complex_of_real (U_cart cvec g (a + t *\<^sub>R v) \<omega>))"
    using rline_entire_U_cart unfolding rline_entire_def by blast
qed


subsection \<open>The Fold-Slice Derivative \<open>\<partial>\<^sub>s U\<close> has Entire Line Restrictions\<close>

text \<open>
  Two more closure lemmas needed for the slice derivative: complex-of-real
  \<^emph>\<open>linear forms\<close> (entire line restrictions because the restriction is affine in
  the line parameter) and complex \<^emph>\<open>conjugation\<close> (entire via Schwarz reflection).
\<close>

lemma cline_entire_of_real_linear:
  fixes lf :: "'a::euclidean_space \<Rightarrow> real"
  assumes "bounded_linear lf"
  shows "cline_entire (\<lambda>x. complex_of_real (lf x))"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  have aff: "lf (a + t *\<^sub>R v) = lf a + t * lf v" for t::real
    by (simp add: assms linear_simps(1,5))
  let ?G = "\<lambda>z. complex_of_real (lf a) + z * complex_of_real (lf v)"
  have "?G holomorphic_on UNIV" by (intro holomorphic_intros)
  moreover have "?G (complex_of_real t) = complex_of_real (lf (a + t *\<^sub>R v))" for t::real
    by (simp add: aff)
  ultimately show "\<exists>G. G holomorphic_on UNIV
                       \<and> (\<forall>t::real. G (complex_of_real t) = complex_of_real (lf (a + t *\<^sub>R v)))"
    by blast
qed

lemma cline_entire_cnj:
  assumes "cline_entire g"
  shows "cline_entire (\<lambda>x. cnj (g x))"
  unfolding cline_entire_def
proof (intro allI)
  fix a v
  obtain G where G: "G holomorphic_on UNIV"
      "\<And>t::real. G (complex_of_real t) = g (a + t *\<^sub>R v)"
    using assms unfolding cline_entire_def by blast
  let ?H = "\<lambda>z. cnj (G (cnj z))"
  have "?H holomorphic_on UNIV" by (rule holomorphic_cnj_reflect[OF G(1)])
  moreover have "?H (complex_of_real t) = cnj (g (a + t *\<^sub>R v))" for t::real
    by (simp add: G(2))
  ultimately show "\<exists>H. H holomorphic_on UNIV
                       \<and> (\<forall>t::real. H (complex_of_real t) = cnj (g (a + t *\<^sub>R v)))"
    by blast
qed

text \<open>
  The bare array factor and its fold-slice derivative for a fixed wavevector
  \<open>c = cvec \<omega>\<close> and its tangent-direction derivative \<open>c' = \<partial>\<^sub>s (cvec \<omega>)\<close>. The
  derivative array factor \<open>\<partial>\<^sub>s A = \<Sum>\<^sub>n (-\<i>)(c'\<bullet>x\<^sub>n) cis(-(c\<bullet>x\<^sub>n))\<close> is a finite sum
  of (linear form)\<open>\<cdot>\<close>(\<open>cis\<close> of a linear form), hence \<open>cline_entire\<close>.
\<close>

lemma cline_entire_af:
  fixes c :: planar
  shows "cline_entire (\<lambda>x::planar^'n. \<Sum>n\<in>UNIV. cis (- (c \<bullet> (x $ n))))"
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  have "bounded_linear (\<lambda>x::planar^'n. - (c \<bullet> (x $ n)))"
    by (rule bounded_linear_minus
              [OF bounded_linear_compose[OF bounded_linear_inner_right bounded_linear_vec_nth]])
  thus "cline_entire (\<lambda>x::planar^'n. cis (- (c \<bullet> (x $ n))))"
    by (rule cline_entire_cis_linear)
qed

lemma cline_entire_dsA:
  fixes c c' :: planar
  shows "cline_entire
           (\<lambda>x::planar^'n. \<Sum>n\<in>UNIV.
              (- \<i>) * complex_of_real (c' \<bullet> (x $ n)) * cis (- (c \<bullet> (x $ n))))"
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  have lin1: "bounded_linear (\<lambda>x::planar^'n. c' \<bullet> (x $ n))"
    by (rule bounded_linear_compose[OF bounded_linear_inner_right bounded_linear_vec_nth])
  have lin2: "bounded_linear (\<lambda>x::planar^'n. - (c \<bullet> (x $ n)))"
    by (rule bounded_linear_minus
              [OF bounded_linear_compose[OF bounded_linear_inner_right bounded_linear_vec_nth]])
  show "cline_entire
          (\<lambda>x::planar^'n. (- \<i>) * complex_of_real (c' \<bullet> (x $ n)) * cis (- (c \<bullet> (x $ n))))"
    by (rule cline_entire_mult
              [OF cline_entire_mult[OF cline_entire_const cline_entire_of_real_linear[OF lin1]]
                  cline_entire_cis_linear[OF lin2]])
qed

text \<open>
  The fold-slice derivative \<open>\<partial>\<^sub>s U\<close> in closed form (chain rule for
  \<open>U = g\<cdot>|A|\<^sup>2\<close> along the fold curve): with \<open>gv = g \<omega>\<close>, \<open>gv' = \<partial>\<^sub>s (g \<omega>)\<close>,
  \<open>\<partial>\<^sub>s U = gv'\<cdot>|A|\<^sup>2 + gv\<cdot>2\<real>(\<^bold>\<bar>A\<cdot>\<partial>\<^sub>s A)\<close>. As a function of \<open>x\<close> it is a real
  combination of the entire-line-restriction building blocks, hence
  \<open>rline_entire\<close> and globally continuous; its slice-zero set is therefore nowhere
  dense whenever the slice is nontrivial. This is the array-factor-shaped
  discharge of the \<open>slice_nowhere_dense\<close> hypothesis of \<open>prop_foldnonzero\<close> for the
  actual fold-critical slice function.
\<close>

definition dsU_cart :: "planar \<Rightarrow> planar \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (planar^'n) \<Rightarrow> real" where
  "dsU_cart c c' gv gv' x =
     gv' * (cmod (\<Sum>n\<in>UNIV. cis (- (c \<bullet> (x $ n)))))\<^sup>2
   + gv * (2 * Re (cnj (\<Sum>n\<in>UNIV. cis (- (c \<bullet> (x $ n))))
                   * (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (c' \<bullet> (x $ n))
                                * cis (- (c \<bullet> (x $ n))))))"

lemma rline_entire_dsU_cart:
  shows "rline_entire (\<lambda>x::planar^'n. dsU_cart c c' gv gv' x)"
proof -
  have A: "cline_entire (\<lambda>x::planar^'n. \<Sum>n\<in>UNIV. cis (- (c \<bullet> (x $ n))))"
    by (rule cline_entire_af)
  have dsA: "cline_entire
               (\<lambda>x::planar^'n. \<Sum>n\<in>UNIV.
                  (- \<i>) * complex_of_real (c' \<bullet> (x $ n)) * cis (- (c \<bullet> (x $ n))))"
    by (rule cline_entire_dsA)
  have P: "rline_entire (\<lambda>x::planar^'n. (cmod (\<Sum>n\<in>UNIV. cis (- (c \<bullet> (x $ n)))))\<^sup>2)"
    by (rule rline_entire_cmod_sq[OF A])
  have Q: "rline_entire
             (\<lambda>x::planar^'n. Re (cnj (\<Sum>n\<in>UNIV. cis (- (c \<bullet> (x $ n))))
                   * (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (c' \<bullet> (x $ n))
                                * cis (- (c \<bullet> (x $ n))))))"
    by (rule rline_entire_Re[OF cline_entire_mult[OF cline_entire_cnj[OF A] dsA]])
  have "rline_entire
          (\<lambda>x::planar^'n.
             gv' * (cmod (\<Sum>n\<in>UNIV. cis (- (c \<bullet> (x $ n)))))\<^sup>2
           + gv * (2 * Re (cnj (\<Sum>n\<in>UNIV. cis (- (c \<bullet> (x $ n))))
                   * (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (c' \<bullet> (x $ n))
                                * cis (- (c \<bullet> (x $ n)))))))"
    by (intro rline_entire_add rline_entire_scale P Q)
  thus ?thesis unfolding dsU_cart_def .
qed

lemma continuous_on_dsU_cart:
  shows "continuous_on UNIV (\<lambda>x::planar^'n. dsU_cart c c' gv gv' x)"
  unfolding dsU_cart_def
  by (intro continuous_intros)

lemma dsU_cart_zero_nowhere_dense:
  fixes c c' :: planar and gv gv' :: real and V :: "(planar^'n) set"
  assumes nontriv: "\<exists>x::planar^'n. dsU_cart c c' gv gv' x \<noteq> 0"
  shows "nowhere_dense {x \<in> V. dsU_cart c c' gv gv' x = 0}"
proof (rule lines_entire_slice_nowhere_dense[OF continuous_on_dsU_cart _ nontriv])
  show "\<And>a v. \<exists>F. F holomorphic_on UNIV
                  \<and> (\<forall>t::real. F (complex_of_real t)
                              = complex_of_real (dsU_cart c c' gv gv' (a + t *\<^sub>R v)))"
    using rline_entire_dsU_cart unfolding rline_entire_def by blast
qed

text \<open>
  Bridge to the rigorous Fréchet derivative \<^const>\<open>dU_cart\<close>: for a fixed steering
  angle \<open>\<omega>\<close> and fold-tangent direction \<open>h\<close>, the directional derivative
  \<open>\<partial>\<^sub>s U = dU_cart cvec dc gain dgain x \<omega> h\<close> is, as a function of \<open>x\<close>, exactly the
  closed form \<^const>\<open>dsU_cart\<close> with the wavevector \<open>c = cvec \<omega>\<close>, its steered
  derivative \<open>c' = dc h\<close>, the gain \<open>gv = gain \<omega>\<close>, and \<open>gv' = dgain h\<close>. Hence the
  genuine derivative inherits the entire-line-restriction structure, so its
  slice-zero set is nowhere dense whenever nontrivial --- the fully concrete
  discharge of \<open>slice_nowhere_dense\<close> for \<open>prop_foldnonzero\<close>.
\<close>

lemma dU_cart_eq_dsU_cart:
  "dU_cart cvec dc gain dgain x \<omega> h
     = dsU_cart (cvec \<omega>) (dc h) (gain \<omega>) (dgain h) x"
  unfolding dU_cart_def dsU_cart_def A_cart_def dA_cart_def
  by simp

lemma rline_entire_dU_cart:
  "rline_entire (\<lambda>x::planar^'n. dU_cart cvec dc gain dgain x \<omega> h)"
  unfolding dU_cart_eq_dsU_cart by (rule rline_entire_dsU_cart)

lemma dU_cart_zero_nowhere_dense:
  fixes cvec dc :: "angle \<Rightarrow> planar" and gain dgain :: "angle \<Rightarrow> real"
    and \<omega> h :: angle and V :: "(planar^'n) set"
  assumes nontriv: "\<exists>x::planar^'n. dU_cart cvec dc gain dgain x \<omega> h \<noteq> 0"
  shows "nowhere_dense {x \<in> V. dU_cart cvec dc gain dgain x \<omega> h = 0}"
  unfolding dU_cart_eq_dsU_cart
  using nontriv unfolding dU_cart_eq_dsU_cart
  by (rule dsU_cart_zero_nowhere_dense)

text \<open>
  Meager version of the regular-stratum transversality bad set (the rung that
  \<open>prop_regzero\<close> consumes). The chart cover from @{thm charts_core_Nn} is a
  countable union of \<^emph>\<open>closed\<close> Lebesgue-negligible pieces, so the bad set is
  meager by @{thm meager_negligible_closed_cover}.
\<close>

lemma parametric_transversality_meager_complex:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}"
    and "open \<Omega>reg"
    and joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
    and A_C1: "\<exists>A'. (\<forall>z\<in>V\<times>\<Omega>reg. (A has_derivative blinfun_apply (A' z)) (at z))
                    \<and> continuous_on (V\<times>\<Omega>reg) A'"
  shows "meager {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg}"
proof -
  have reg0: "regular_value_on (\<lambda>z. cplx_r2 (A z)) (V \<times> \<Omega>reg) 0"
    using regular_value_on_cplx_r2_comp[OF joint_trans] .
  have eq_bad:
      "{x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg}
       =
       {x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. cplx_r2 (A (x,\<omega>)) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. cplx_r2 (A (x,u))) has_derivative D) (at \<omega> within \<Omega>reg) \<and> surj D))}"
    unfolding transverse0_on_def by auto
  have bad_meager:
    "meager {x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. cplx_r2 (A (x,\<omega>)) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. cplx_r2 (A (x,u))) has_derivative D)
                       (at \<omega> within \<Omega>reg) \<and> surj D))}"
  proof -
    let ?G = "\<lambda>z. cplx_r2 (A z)"

    obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
       and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
       and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      where cover:
      "{x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. ?G (x,\<omega>) = 0 \<and>
          (\<not> (\<exists>D\<omega>. ((\<lambda>u. ?G (x,u)) has_derivative D\<omega>)
                    (at \<omega> within \<Omega>reg) \<and> surj D\<omega>))}
       \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der:
      "\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)"
      and rank:
      "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clsd:
      "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
      using charts_core_Nn[OF assms(1) assms(2) assms(3) reg0
              C1_cplx_r2_comp[OF A_C1]]
      by blast

    have negligible_cover:
      "negligible (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    proof (rule negligible_proj_charts_Nn)
      show "\<And>i x. x \<in> Crit i \<Longrightarrow>
        ((fst \<circ> charts i) has_derivative blinfun_apply (D i x))
          (at x within Crit i)"
        using der by blast
      show "\<And>i x. x \<in> Crit i \<Longrightarrow> \<not> surj (blinfun_apply (D i x))"
        using rank by blast
    qed

    show ?thesis
    proof (rule meager_negligible_closed_cover
                  [where K = "\<lambda>i. (fst \<circ> charts i) ` (Crit i)"])
      show "{x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. ?G (x,\<omega>) = 0 \<and>
              (\<not> (\<exists>D\<omega>. ((\<lambda>u. ?G (x,u)) has_derivative D\<omega>)
                        (at \<omega> within \<Omega>reg) \<and> surj D\<omega>))}
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
        by (rule cover)
      show "\<And>i. closed ((fst \<circ> charts i) ` (Crit i))"
        using clsd by blast
      show "\<And>i. negligible ((fst \<circ> charts i) ` (Crit i))"
        using negligible_cover by (auto intro: negligible_subset)
    qed
  qed
  then have "meager {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg}"
    by (simp add: eq_bad)
  then show ?thesis
    by (simp only: transverse0_on_cplx_r2_iff)
qed

theorem prop_regzero:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}" and "open \<Omega>reg"
    and joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
    and A_C1: "\<exists>A'. (\<forall>z\<in>V\<times>\<Omega>reg. (A has_derivative blinfun_apply (A' z)) (at z))
                    \<and> continuous_on (V\<times>\<Omega>reg) A'"
  shows "meager {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg}"
  by (rule parametric_transversality_meager_complex[OF assms(1-3) joint_trans A_C1])


section \<open>The Singular Curve Is a Fold\<close>

text \<open>
  The explicit fold fields. With the moving frame \<open>e_r(\<phi>) = (\<cos>\<phi>, \<sin>\<phi>)\<close>,
  \<open>e_\<phi>(\<phi>) = (-\<sin>\<phi>, \<cos>\<phi>)\<close> and (ignoring the additive \<open>\<omega>\<^sub>s\<close> constant)
  \<open>cvec(\<theta>,\<phi>) = \<sin>\<theta> e_r(\<phi>) + \<cos>\<theta> D + c\<^sub>0\<close>, the partials are
  \<open>\<partial>\<^sub>\<phi> cvec = \<sin>\<theta> e_\<phi>\<close>, \<open>\<partial>\<^sub>\<theta> cvec = \<cos>\<theta> e_r - \<sin>\<theta> D\<close>, and the Jacobian determinant is
  \<open>\<det> D\<^sub>\<omega> cvec = h(\<theta>,\<phi>) \<sin>\<theta>\<close> with \<open>h = \<cos>\<theta> - \<sin>\<theta> (D \<cdot> e_r)\<close>. The singular curve
  \<open>\<Sigma> = {h \<sin>\<theta> = 0}\<close> is where the differential drops rank.
\<close>

definition e_r :: "real \<Rightarrow> real \<times> real" where "e_r \<phi> = (cos \<phi>, sin \<phi>)"
definition e_p :: "real \<Rightarrow> real \<times> real" where "e_p \<phi> = (- sin \<phi>, cos \<phi>)"

definition cvecf :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<times> real" where
  "cvecf D c0 \<theta> \<phi> = sin \<theta> *\<^sub>R e_r \<phi> + cos \<theta> *\<^sub>R D + c0"

text \<open>
  The \<open>2 \<times> 2\<close> Jacobian \<open>D\<^sub>\<omega> cvec\<close> as a Cartesian matrix \<^typ>\<open>real^2^2\<close>, with columns
  the partials \<open>\<partial>\<^sub>\<theta> cvec\<close> (column 1) and \<open>\<partial>\<^sub>\<phi> cvec\<close> (column 2). Its determinant is the
  standard HOL-Analysis \<^const>\<open>det\<close> (evaluated via @{thm [source] det_2}).
\<close>

definition Jcvec :: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2^2" where
  "Jcvec D \<theta> \<phi> =
     (\<chi> i j. if j = 1
              then (if i = 1 then cos \<theta> * cos \<phi> - sin \<theta> * fst D
                             else cos \<theta> * sin \<phi> - sin \<theta> * snd D)
              else (if i = 1 then - (sin \<theta> * sin \<phi>) else sin \<theta> * cos \<phi>))"

lemma e_r_vector_deriv: "(e_r has_vector_derivative e_p \<phi>) (at \<phi>)"
proof -
  have c: "((\<lambda>\<phi>. cos \<phi>) has_vector_derivative - sin \<phi>) (at \<phi>)"
    by (simp add: has_vector_derivative_def) (auto intro!: derivative_eq_intros)
  have s: "((\<lambda>\<phi>. sin \<phi>) has_vector_derivative cos \<phi>) (at \<phi>)"
    by (simp add: has_vector_derivative_def) (auto intro!: derivative_eq_intros)
  show ?thesis
    unfolding e_r_def e_p_def
    by (auto intro!: has_vector_derivative_Pair c s)
qed

lemma cvecf_phi_deriv:
  "((\<lambda>\<phi>. cvecf D c0 \<theta> \<phi>) has_vector_derivative (sin \<theta> *\<^sub>R e_p \<phi>)) (at \<phi>)"
  unfolding cvecf_def
  by (auto intro!: derivative_eq_intros e_r_vector_deriv)

lemma cvecf_theta_deriv:
  "((\<lambda>\<theta>. cvecf D c0 \<theta> \<phi>) has_vector_derivative (cos \<theta> *\<^sub>R e_r \<phi> - sin \<theta> *\<^sub>R D)) (at \<theta>)"
  unfolding cvecf_def
  by (auto intro!: derivative_eq_intros)

lemma det_Jcvec:
  "det (Jcvec D \<theta> \<phi>) = (cos \<theta> - sin \<theta> * (D \<bullet> e_r \<phi>)) * sin \<theta>"
proof -
  have py: "cos \<phi> * cos \<phi> + sin \<phi> * sin \<phi> = 1"
    using sin_cos_squared_add[of \<phi>] by (simp add: power2_eq_square)
  have m: "D \<bullet> e_r \<phi> = fst D * cos \<phi> + snd D * sin \<phi>"
    by (simp add: e_r_def inner_prod_def)
  have raw: "det (Jcvec D \<theta> \<phi>)
      = (cos \<theta> * cos \<phi> - sin \<theta> * fst D) * (sin \<theta> * cos \<phi>)
        - (- (sin \<theta> * sin \<phi>)) * (cos \<theta> * sin \<phi> - sin \<theta> * snd D)"
    by (simp add: det_2 Jcvec_def)
  show ?thesis
    unfolding raw m using py by algebra
qed

theorem lem_foldfields:
  fixes D c0 :: "real \<times> real" and \<theta> \<phi> :: real
  shows "((\<lambda>\<phi>. cvecf D c0 \<theta> \<phi>) has_vector_derivative (sin \<theta> *\<^sub>R e_p \<phi>)) (at \<phi>)"
    and "((\<lambda>\<theta>. cvecf D c0 \<theta> \<phi>) has_vector_derivative (cos \<theta> *\<^sub>R e_r \<phi> - sin \<theta> *\<^sub>R D)) (at \<theta>)"
    and "det (Jcvec D \<theta> \<phi>) = (cos \<theta> - sin \<theta> * (D \<bullet> e_r \<phi>)) * sin \<theta>"
  using cvecf_phi_deriv cvecf_theta_deriv det_Jcvec by blast+


section \<open>Fold Zeros of the Array Factor\<close>

text \<open>
  TeX Proposition~(Fold zeros are nongeneric) is the same pattern as the regular
  stratum, but with a 1-dimensional parameter (a chart on the fold curve) instead of
  an open 2D domain. Each chart yields a smooth map \<open>V \<times> I \<to> \<complex>\<close> transverse to 0,
  hence its zero set projects meagerly to \<open>V\<close>; a finite union stays meager.
\<close>

lemma chart_zero_projection_meager_stub:
  fixes V :: "((real^2)^'n) set" and I :: "real set"
    and F :: "(((real^2)^'n) \<times> real) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}"
    and "I \<subseteq> UNIV"
    and F_smooth: "\<forall>z\<in>V\<times>I. F differentiable at z"
    and Dx_surj:
      "\<forall>(x,t)\<in>V\<times>I. F (x,t) = 0 \<longrightarrow>
        (\<exists>D. ((\<lambda>y. F (y,t)) has_derivative D) (at x within V) \<and> surj D)"
  shows "meager {x\<in>V. \<exists>t\<in>I. F (x,t) = 0}"
  sorry

lemma meager_Union_finite:
  fixes A :: "'i \<Rightarrow> 'a::topological_space set"
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> meager (A i)"
  shows "meager (\<Union>i\<in>I. A i)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert i I)
  have "meager ((\<Union>j\<in>insert i I. A j)) \<longleftrightarrow> meager (A i \<union> (\<Union>j\<in>I. A j))"
    by auto
  moreover have "meager (A i \<union> (\<Union>j\<in>I. A j))"
    using insert by (intro meager_Un) auto
  ultimately show ?case
    by simp
qed

theorem prop_foldzero:
  fixes V :: "((real^2)^'n) set"
    and L :: nat
    and I :: "nat \<Rightarrow> real set"
    and F :: "nat \<Rightarrow> ((((real^2)^'n) \<times> real) \<Rightarrow> complex)"
  assumes V: "open V" "V \<noteq> {}"
    and charts:
      "\<And>l. l < L \<Longrightarrow> meager {x\<in>V. \<exists>t\<in>I l. F l (x,t) = 0}"
  shows "meager {x\<in>V. \<exists>l<L. \<exists>t\<in>I l. F l (x,t) = 0}"
proof -
  define S where "S l = {x\<in>V. \<exists>t\<in>I l. F l (x,t) = 0}" for l
  have hS: "\<And>l. l \<in> {..<L} \<Longrightarrow> meager (S l)"
    using charts by (simp add: S_def)
  have "meager (\<Union>l\<in>{..<L}. S l)"
    by (rule meager_Union_finite) (use hS in auto)
  moreover have "{x\<in>V. \<exists>l<L. \<exists>t\<in>I l. F l (x,t) = 0} = (\<Union>l\<in>{..<L}. S l)"
    by (auto simp: S_def)
  ultimately show ?thesis
    by simp
qed


section \<open>Fold Critical Points with @{term "A \<noteq> 0"}\<close>

text \<open>
  TeX Lemma~\<open>lem:Efinite\<close>: \<open>E = {\<omega>\<in>\<Sigma> : g\<^sub>\<theta>(\<omega>) = 0}\<close> is finite. We model the
  element-gain \<open>\<theta>\<close>-derivative \<open>g\<^sub>\<theta>\<close> as real-analytic (the real restriction of an
  entire function \<open>G\<close>) and not identically zero on the compact \<open>\<theta>\<close>-interval \<open>\<Theta>\<close>;
  the fold curve \<open>\<Sigma>\<close> has a finite \<open>\<phi>\<close>-fibre over each \<open>\<theta>\<close> (at most two solutions).
  The remaining obligation is the real-analytic isolated-zeros fact (zeros of a
  nontrivial real-analytic function on a compact interval are finite).
\<close>

theorem lem_Efinite:
  fixes g\<theta> :: "real \<Rightarrow> real" and G :: "complex \<Rightarrow> complex"
    and \<Theta> :: "real set" and \<Sigma> :: "(real \<times> real) set"
  assumes \<Theta>_compact: "compact \<Theta>" and \<Theta>_interval: "is_interval \<Theta>"
    and \<Sigma>_\<theta>range: "\<And>\<theta> \<phi>. (\<theta>, \<phi>) \<in> \<Sigma> \<Longrightarrow> \<theta> \<in> \<Theta>"
    and \<phi>_fibre_finite: "\<And>\<theta>. finite {\<phi>. (\<theta>, \<phi>) \<in> \<Sigma>}"
    and g\<theta>_restriction: "\<And>t. g\<theta> t = Re (G (complex_of_real t))"
    and G_entire: "G holomorphic_on UNIV"
    and g\<theta>_not_identically_zero: "\<exists>t\<in>\<Theta>. g\<theta> t \<noteq> 0"
  shows "finite {\<omega> \<in> \<Sigma>. g\<theta> (fst \<omega>) = 0}"
proof -
  \<comment> \<open>The analytic kernel: zeros of the nontrivial real-analytic
      \<open>g\<^sub>\<theta> = \<real> \<circ> G\<close> on the compact \<open>\<Theta>\<close> are finite. Build the entire reflection
      \<open>H z = (G z + cnj (G (cnj z)))/2\<close>, which is \<^emph>\<open>real on the reals\<close> and equals
      \<open>g\<^sub>\<theta>\<close> there; by \<open>isolated_zeros\<close> its zero set has no limit point, and a
      no-limit-point subset of the compact \<open>cor ` \<Theta>\<close> is finite.\<close>
  have theta_zeros_finite: "finite {t \<in> \<Theta>. g\<theta> t = 0}"
  proof -
    define H where "H = (\<lambda>z. (G z + cnj (G (cnj z))) / 2)"
    have Href: "(\<lambda>z. cnj (G (cnj z))) holomorphic_on UNIV"
      by (rule holomorphic_cnj_reflect[OF G_entire])
    have Hhol: "H holomorphic_on UNIV"
      unfolding H_def using G_entire Href by (intro holomorphic_intros) auto
    have Hreal: "H (complex_of_real t) = complex_of_real (g\<theta> t)" for t
    proof -
      have "H (complex_of_real t)
              = (G (complex_of_real t) + cnj (G (complex_of_real t))) / 2"
        by (simp add: H_def)
      also have "\<dots> = complex_of_real (Re (G (complex_of_real t)))"
        by (simp add: complex_add_cnj)
      finally show ?thesis by (simp add: g\<theta>_restriction)
    qed
    obtain t0 where t0: "t0 \<in> \<Theta>" "g\<theta> t0 \<noteq> 0"
      using g\<theta>_not_identically_zero by blast
    have Hnz: "H (complex_of_real t0) \<noteq> 0"
      using t0(2) by (simp add: Hreal)
    have nolim: "\<not> z islimpt {w. H w = 0}" for z
    proof (cases "H z = 0")
      case True
      obtain r where r: "0 < r"
          and rz: "\<And>w. w \<in> ball z r - {z} \<Longrightarrow> H w \<noteq> 0"
        using isolated_zeros[OF Hhol open_UNIV connected_UNIV UNIV_I True UNIV_I Hnz]
        by metis
      show ?thesis
        using Hhol Hnz analytic_continuation by blast       
    next
      case False
      have "continuous (at z) H"
        using Hhol holomorphic_on_imp_continuous_on[of H UNIV]
        by (simp add: continuous_on_eq_continuous_at)
      then obtain e where e: "0 < e" "\<And>y. dist z y < e \<Longrightarrow> H y \<noteq> 0"
        using continuous_at_avoid[of z H 0] False by blast
      show ?thesis
        using False Hhol analytic_continuation by blast       
    qed
    have compactK: "compact (complex_of_real ` \<Theta>)"
      by (intro compact_continuous_image \<Theta>_compact continuous_intros)
    have "finite ((complex_of_real ` \<Theta>) \<inter> {w. H w = 0})"
      by (rule finite_not_islimpt_in_compact[OF compactK]) (use nolim in blast)
    moreover have "complex_of_real ` {t \<in> \<Theta>. g\<theta> t = 0}
                     \<subseteq> (complex_of_real ` \<Theta>) \<inter> {w. H w = 0}"
      using Hreal by auto
    ultimately have "finite (complex_of_real ` {t \<in> \<Theta>. g\<theta> t = 0})"
      by (rule rev_finite_subset)
    then show "finite {t \<in> \<Theta>. g\<theta> t = 0}"
      by (rule finite_imageD) (simp add: inj_on_def)
  qed
  \<comment> \<open>Each bad \<open>\<omega> = (\<theta>,\<phi>)\<close> has \<open>\<theta> \<in> \<Theta>\<close> with \<open>g\<^sub>\<theta>(\<theta>) = 0\<close>, so it lies in the
      \<open>\<phi>\<close>-fibre over one of finitely many \<open>\<theta>\<close>.\<close>
  have "{\<omega> \<in> \<Sigma>. g\<theta> (fst \<omega>) = 0}
          \<subseteq> (\<Union>t \<in> {t \<in> \<Theta>. g\<theta> t = 0}. (\<lambda>\<phi>. (t, \<phi>)) ` {\<phi>. (t, \<phi>) \<in> \<Sigma>})"
  proof
    fix \<omega> assume "\<omega> \<in> {\<omega> \<in> \<Sigma>. g\<theta> (fst \<omega>) = 0}"
    then have \<omega>\<Sigma>: "\<omega> \<in> \<Sigma>" and g0: "g\<theta> (fst \<omega>) = 0" by auto
    obtain t \<phi> where \<omega>eq: "\<omega> = (t, \<phi>)" by (cases \<omega>)
    from \<omega>\<Sigma> \<omega>eq have "\<phi> \<in> {\<phi>. (t, \<phi>) \<in> \<Sigma>}" by simp
    moreover from \<omega>\<Sigma> \<omega>eq \<Sigma>_\<theta>range have "t \<in> \<Theta>" by simp
    moreover from g0 \<omega>eq have "g\<theta> t = 0" by simp
    ultimately show "\<omega> \<in> (\<Union>t \<in> {t \<in> \<Theta>. g\<theta> t = 0}. (\<lambda>\<phi>. (t, \<phi>)) ` {\<phi>. (t, \<phi>) \<in> \<Sigma>})"
      using \<omega>eq by blast
  qed
  moreover have "finite (\<Union>t \<in> {t \<in> \<Theta>. g\<theta> t = 0}. (\<lambda>\<phi>. (t, \<phi>)) ` {\<phi>. (t, \<phi>) \<in> \<Sigma>})"
    by (rule finite_UN_I[OF theta_zeros_finite])
       (simp add: \<phi>_fibre_finite)
  ultimately show ?thesis
    by (rule finite_subset)
qed

text \<open>
  TeX Proposition~\<open>prop:foldnonzero\<close>: the nonzero-\<open>A\<close> fold-critical bad set is
  meager in \<open>V\<close>. As in the TeX proof, every such critical point lies over the
  finite exceptional set \<open>E\<close> (Lemma~\<open>lem:Efinite\<close>), and for each \<open>\<omega>\<in>E\<close> the slice
  function \<open>F\<^sub>\<omega>(x) = \<partial>\<^sub>s U(x,\<omega>)\<close> is a nontrivial real-analytic function of \<open>x\<close>,
  so its zero set in the connected open \<open>V\<close> is nowhere dense. The bad set is
  contained in their finite union, hence meager. The nowhere-density of each
  slice-zero set is the real-analytic input, recorded here as a hypothesis; this
  theorem is the (proved) reduction assembling the finite union.
\<close>

theorem prop_foldnonzero:
  fixes V Bad :: "((real^2)^'n) set" and E :: "(real^2) set"
    and Fcrit :: "(real^2) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
  assumes E_finite: "finite E"
    and reduce_to_E: "Bad \<subseteq> (\<Union>\<omega>\<in>E. {x \<in> V. Fcrit \<omega> x = 0})"
    and slice_nowhere_dense:
      "\<And>\<omega>. \<omega> \<in> E \<Longrightarrow> nowhere_dense {x \<in> V. Fcrit \<omega> x = 0}"
  shows "meager Bad"
proof -
  have "meager (\<Union>\<omega>\<in>E. {x \<in> V. Fcrit \<omega> x = 0})"
    by (rule meager_Union_finite[OF E_finite])
       (rule meager_nowhere_dense[OF slice_nowhere_dense])
  then show ?thesis
    by (rule meager_subset[OF reduce_to_E])
qed


section \<open>Regular-Stratum Nonzero-A Degenerate Critical Points\<close>

text \<open>
  TeX Proposition~\<open>prop:regnonzero\<close>: the regular-stratum nonzero-\<open>A\<close> bad set
  \<open>B\<^sub>reg,\<noteq>0\<close> is meager in \<open>V\<close>. The TeX proof partitions the bad locus \<open>Z\<close> by the
  surjective set \<open>W\<^sub>surj\<close> and by \<open>H\<equiv>0\<close> into four pieces: the regular codim-3
  piece \<open>\<pi>\<^sub>V(Z\<^sub>reg)\<close> and the codim-5 Hessian-zero stratum (both meager by
  \<open>prop:dimZ\<close> + \<open>lem:smooth-chart-meager\<close>), the Case-B set (meager by
  \<open>cor:caseBmeager\<close>, Appendix~\<open>app:caseB\<close>), and the residual \<open>H\<equiv>0\<close> set
  (meager by \<open>prop:h0res-meager\<close>, Appendix~\<open>app:H0res\<close>). Those four meagerness
  facts are the deep appendix results, recorded here as hypotheses; this theorem
  is the (proved) reduction that assembles them.
\<close>

text \<open>
  The explicit \<open>12 \<times> 12\<close> real Jacobian minor \<open>J\<close> of \<open>D\<^sub>x M\<close> at the chosen
  six-element configuration (TeX Figure~\<open>fig:bigmatrix\<close>), evaluated at
  \<open>\<kappa> = 1\<close>. Rows are the twelve real moment components
  \<open>\<real>A, \<I>A, \<real>M\<^sub>1, \<I>M\<^sub>1, \<real>M\<^sub>2, \<I>M\<^sub>2, \<real>M\<^sub>1\<^sub>1, \<I>M\<^sub>1\<^sub>1, \<real>M\<^sub>1\<^sub>2, \<I>M\<^sub>1\<^sub>2, \<real>M\<^sub>2\<^sub>2, \<I>M\<^sub>2\<^sub>2\<close>;
  the twelve columns are \<open>\<partial>\<^sub>u\<^sub>n M, \<partial>\<^sub>v\<^sub>n M\<close> for \<open>n = 1..6\<close>. (The determinant is
  transpose-invariant, so the row/column reading is immaterial.)
\<close>

definition bigJ :: "real^12^12" where
  "bigJ = vector
    [ vector [0, 0, - sqrt 3 / 2, 0, - sqrt 3 / 2, 0, 0, 0, sqrt 3 / 2, 0, sqrt 3 / 2, 0],
      vector [- 1, 0, - 1/2, 0, 1/2, 0, 1, 0, 1/2, 0, - 1/2, 0],
      vector [1, 0, 1/2 - pi * sqrt 3 / 6, 0, - 1/2 - pi * sqrt 3 / 3, 0,
              - 1, 0, - 1/2 + 2 * pi * sqrt 3 / 3, 0, 1/2 + 5 * pi * sqrt 3 / 6, 0],
      vector [0, 0, - sqrt 3 / 2 - pi / 6, 0, - sqrt 3 / 2 + pi / 3, 0,
              pi, 0, sqrt 3 / 2 + 2 * pi / 3, 0, sqrt 3 / 2 - 5 * pi / 6, 0],
      vector [0, 1, - sqrt 3, 1/2, 0, - 1/2, 0, - 1, sqrt 3, - 1/2, sqrt 3, 1/2],
      vector [- 2, 0, - 1, - sqrt 3 / 2, 0, - sqrt 3 / 2, 0, 0, 1, sqrt 3 / 2, - 1, sqrt 3 / 2],
      vector [0, 0, pi / 3 - pi^2 * sqrt 3 / 18, 0, - 2 * pi / 3 - 2 * pi^2 * sqrt 3 / 9, 0,
              - 2 * pi, 0, - 4 * pi / 3 + 8 * pi^2 * sqrt 3 / 9, 0,
              5 * pi / 3 + 25 * pi^2 * sqrt 3 / 18, 0],
      vector [0, 0, - pi * sqrt 3 / 3 - pi^2 / 18, 0, - 2 * pi * sqrt 3 / 3 + 2 * pi^2 / 9, 0,
              pi^2, 0, 4 * pi * sqrt 3 / 3 + 8 * pi^2 / 9, 0,
              5 * pi * sqrt 3 / 3 - 25 * pi^2 / 18, 0],
      vector [2, 0, 1 - pi * sqrt 3 / 3, pi / 6, 0, - pi / 3, 0, - pi,
              - 1 + 4 * pi * sqrt 3 / 3, - 2 * pi / 3, 1 + 5 * pi * sqrt 3 / 3, 5 * pi / 6],
      vector [0, 0, - sqrt 3 - pi / 3, - pi * sqrt 3 / 6, 0, - pi * sqrt 3 / 3, 0, 0,
              sqrt 3 + 4 * pi / 3, 2 * pi * sqrt 3 / 3, sqrt 3 - 5 * pi / 3, 5 * pi * sqrt 3 / 6],
      vector [0, 4, - 2 * sqrt 3, 2, 0, 0, 0, 0, 2 * sqrt 3, - 2, 2 * sqrt 3, 2],
      vector [- 4, 0, - 2, - 2 * sqrt 3, 0, 0, 0, 0, 2, 2 * sqrt 3, - 2, 2 * sqrt 3] ]"

text \<open>
  TeX Lemma~\<open>lem:Msurj\<close>, determinant core (\<open>det J = -5\<pi>\<^sup>8/3\<close> at \<open>\<kappa> = 1\<close>;
  the general value is \<open>-5\<pi>\<^sup>8/(3\<kappa>\<^sup>2)\<close>). This is the standalone arithmetic
  fact: the explicit symbolic determinant evaluation of the configuration
  matrix \<^const>\<open>bigJ\<close>. Stated without proof; the (omitted) proof is the
  four-subsubsection cofactor/Vandermonde computation of TeX
  Section~\<open>sssec:msurj-config\<close>. Being nonzero, it is the engine behind the
  \<open>big_det\<close> hypothesis of \<open>Dx_moment_map_surjective\<close> below.
\<close>

lemma bigJ_det: "det bigJ = - (5 * pi^8) / 3"
  sorry

lemma bigJ_det_nonzero: "det bigJ \<noteq> 0"
proof -
  have "pi > 0" by (rule pi_gt_zero)
  hence "pi^8 > 0" by simp
  thus ?thesis unfolding bigJ_det by simp
qed

text \<open>
  The configuration matrix has full rank, hence the parameter-derivative is
  surjective \<^emph>\<open>at the base point\<close>. This is the pointwise content of
  \<open>lem:Msurj\<close> that the determinant delivers: it discharges the \<open>big_det\<close>
  base-point premise of \<open>Dx_moment_map_surjective\<close> once the concrete moment
  map's derivative at the six-element configuration is identified with
  \<^term>\<open>(*v) bigJ\<close>. The open-dense upgrade is a \<^emph>\<open>separate\<close> argument (real-analytic
  lower semicontinuity of rank), not implied by the single-point determinant.
\<close>

lemma bigJ_full_rank: "rank bigJ = CARD(12)"
proof -
  have "rank bigJ \<noteq> CARD(12) \<Longrightarrow> rank bigJ < CARD(12)"
    using rank_bound[of bigJ] by simp
  with bigJ_det_nonzero det_eq_0_rank[of bigJ] show ?thesis by auto
qed

lemma bigJ_surj: "surj ((*v) bigJ)"
  using bigJ_full_rank full_rank_surjective[of bigJ] by simp

text \<open>
  TeX Lemma~\<open>lem:Msurj\<close> (Surjectivity of \<open>D\<^sub>x M\<close>). For \<open>N = CARD('n) \<ge> 6\<close> and
  \<open>c \<noteq> 0\<close>, the parameter-derivative of the moment map
  \<open>M(\<cdot>,c) : \<real>\<^sup>2\<^sup>N \<rightarrow> \<complex>\<^sup>6 \<cong> \<real>\<^sup>1\<^sup>2\<close> (the six moments
  \<open>A, M\<^sub>1, M\<^sub>2, M\<^sub>1\<^sub>1, M\<^sub>1\<^sub>2, M\<^sub>2\<^sub>2\<close>) is surjective on an open dense subset of \<open>V\<close>.
  The omitted proof is the explicit \<open>12 \<times> 12\<close> real Jacobian minor at the
  six-element configuration, yielding the big determinant
  \<open>det J = -5\<pi>\<^sup>8 / (3\<kappa>\<^sup>2) \<noteq> 0\<close>, followed by a lower-semicontinuity upgrade
  of pointwise surjectivity to an open dense set. This feeds the \<open>ZH0surj\<close>
  piece of \<open>prop_regnonzero\<close>. The conclusion is guarded by a \<open>big_det\<close>
  hypothesis (existence of one regular base point), so the recorded obligation
  is the open-dense propagation, not an (otherwise false) absolute surjectivity
  claim. TODO: model the six moments concretely and discharge.
\<close>

lemma Dx_moment_map_surjective:
  fixes V :: "((real^2)^'n) set"
    and \<M> :: "(real^2)^'n \<Rightarrow> complex^6"
    and D\<M> :: "(real^2)^'n \<Rightarrow> ((real^2)^'n \<Rightarrow> complex^6)"
  assumes "open V" and "V \<noteq> {}"
    and N_ge_6: "6 \<le> CARD('n)"
    and deriv: "\<And>x. x \<in> V \<Longrightarrow> (\<M> has_derivative D\<M> x) (at x within V)"
    and big_det: "\<exists>x\<^sub>0\<in>V. surj (D\<M> x\<^sub>0)"
  shows "\<exists>U. open U \<and> U \<subseteq> V \<and> V \<subseteq> closure U \<and> (\<forall>x\<in>U. surj (D\<M> x))"
  sorry

theorem prop_regnonzero:
  fixes V Breg_nonzero Zreg ZH0surj BcaseB BH0res :: "((real^2)^'n) set"
  assumes decompose:
      "Breg_nonzero \<inter> V
         \<subseteq> (Zreg \<inter> V) \<union> (ZH0surj \<inter> V) \<union> (BcaseB \<inter> V) \<union> (BH0res \<inter> V)"
    and meager_Zreg:    "meager (Zreg \<inter> V)"
    and meager_ZH0surj: "meager (ZH0surj \<inter> V)"
    and meager_BcaseB:  "meager (BcaseB \<inter> V)"
    and meager_BH0res:  "meager (BH0res \<inter> V)"
  shows "meager (Breg_nonzero \<inter> V)"
proof -
  have "meager ((Zreg \<inter> V) \<union> (ZH0surj \<inter> V) \<union> (BcaseB \<inter> V) \<union> (BH0res \<inter> V))"
    by (intro meager_Un meager_Zreg meager_ZH0surj meager_BcaseB meager_BH0res)
  then show ?thesis
    by (rule meager_subset[OF decompose])
qed


section \<open>Closeout\<close>

text \<open>
  TeX Theorem~(Odd-\<open>N\<close> nonemptiness), \<open>thm:final\<close>. The Baire closeout: given a
  nonempty open feasible working set \<open>V \<subseteq> Fset\<close> and the four branch meagerness
  facts (Props \<open>prop:regzero\<close>, \<open>prop:foldzero\<close>, \<open>prop:foldnonzero\<close>,
  \<open>prop:regnonzero\<close>) plus soundness of \<open>X0\<close>, the robust feasible set is nonempty.

  This is the genuine closeout, discharged by the fully-proved combinator
  \<open>nonemptiness_from_meager_branches\<close> (\<open>Nonemptiness_Spine\<close>). The four
  meagerness facts remain explicit hypotheses here: they are the deep branch
  results, still to be established for the concrete array-factor bad sets (Props
  \<open>prop_regzero\<close>/\<open>prop_foldzero\<close> are proved modulo the transversality stubs;
  \<open>prop_foldnonzero\<close>/\<open>prop_regnonzero\<close> remain). Once all four are proved
  unconditionally for the concrete sets, instantiating this theorem yields the
  odd-\<open>N\<close> nonemptiness theorem with no remaining hypotheses.
\<close>

theorem thm_final:
  fixes Fset V :: "((real^2)^'n) set"
    and X0 :: "real \<Rightarrow> ((real^2)^'n) set"
    and Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero :: "((real^2)^'n) set"
  assumes V_open: "open V" and V_nonempty: "V \<noteq> {}" and V_subset_Fset: "V \<subseteq> Fset"
    and meager_reg_nonzero:  "meager (Breg_nonzero \<inter> V)"
    and meager_reg_zero:     "meager (Breg_zero \<inter> V)"
    and meager_fold_zero:    "meager (Bfold_zero \<inter> V)"
    and meager_fold_nonzero: "meager (Bfold_nonzero \<inter> V)"
    and X0_sound:
      "\<And>x. x \<in> V - bad_union Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero
            \<Longrightarrow> \<exists>\<xi>>0. x \<in> X0 \<xi>"
  shows "\<exists>\<xi>>0. Fzero Fset X0 \<xi> \<noteq> {}"
  by (rule nonemptiness_from_meager_branches[OF assms])

text \<open>
  Existence-only alternative closeout: if each bad branch is Lebesgue-negligible
  in the nonempty open working set \<open>V\<close>, then the good set is nonempty (no Baire
  category needed).  This is weaker than the intended meager/genericity story,
  but it is often sufficient to obtain nonemptiness of the robust feasible set.
\<close>

theorem thm_final_negligible:
  fixes Fset V :: "((real^2)^'n) set"
    and X0 :: "real \<Rightarrow> ((real^2)^'n) set"
    and Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero :: "((real^2)^'n) set"
  assumes V_open: "open V" and V_nonempty: "V \<noteq> {}" and V_subset_Fset: "V \<subseteq> Fset"
    and neg_reg_nonzero:  "negligible (Breg_nonzero \<inter> V)"
    and neg_reg_zero:     "negligible (Breg_zero \<inter> V)"
    and neg_fold_zero:    "negligible (Bfold_zero \<inter> V)"
    and neg_fold_nonzero: "negligible (Bfold_nonzero \<inter> V)"
    and X0_sound:
      "\<And>x. x \<in> V - bad_union Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero
            \<Longrightarrow> \<exists>\<xi>>0. x \<in> X0 \<xi>"
  shows "\<exists>\<xi>>0. Fzero Fset X0 \<xi> \<noteq> {}"
  by (rule nonemptiness_from_negligible_branches[OF assms])

end
