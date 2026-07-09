theory Scratch_m5_beamhess
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>(M5) shared analytic core of the two beam-center stubs D2 and D5.

  At a beam-center angle (\<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>) all moments \<open>M_paper x 0\<close> are REAL,
  so the \<open>c\<close>-gradient \<open>\<nabla>\<^sub>c V\<close> vanishes and the angular Hessian collapses to the
  covariance form
    \<open>HessU x \<omega> = gain \<cdot> D\<^sup>T (Hcmat x 0) D + gdip''(\<omega>\<^sub>1) N\<^sup>2 e\<^sub>1 e\<^sub>1\<^sup>T\<close>,
  where \<open>Hcmat x 0\<close> is the (real) covariance matrix of \<open>x\<close>.  Its determinant is a
  polynomial in the (real) second moments of \<open>x\<close>; nontrivial because
  \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close>, so its zero locus is nowhere dense in \<open>x\<close>.\<close>


section \<open>Real moments at a beam center\<close>

text \<open>At \<open>c = 0\<close>, the steering vector vanishes, so all phases are \<open>1\<close> and every
  moment function is real.  (Copies of D2's \<open>M_paper_at_zero_*\<close> helpers, plus the
  \<open>Mcfun\<close>/\<open>M2cfun\<close>/\<open>Afun\<close> moment functions that the Hessian entry formula uses.)\<close>

lemma M_paper_at_zero_A:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 1 = of_nat CARD('n)"
proof -
  have "A_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). cis 0)"
    by (simp add: A_moment_def phase_def)
  also have "\<dots> = of_nat CARD('n)" by simp
  finally show ?thesis by simp
qed

lemma M_paper_at_zero_M1:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 2 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
proof -
  have "M1_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 1) * cis 0)"
    by (simp add: M1_moment_def phase_def)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 1))" by simp
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)" by simp
  finally show ?thesis by simp
qed

lemma M_paper_at_zero_M2:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 3 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
proof -
  have "M2_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 2) * cis 0)"
    by (simp add: M2_moment_def phase_def)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 2))" by simp
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)" by simp
  finally show ?thesis by simp
qed

lemma M_paper_at_zero_real123:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 1 = of_real (Re (M_paper x 0 $ 1))"
    and "M_paper x 0 $ 2 = of_real (Re (M_paper x 0 $ 2))"
    and "M_paper x 0 $ 3 = of_real (Re (M_paper x 0 $ 3))"
proof -
  have e1: "M_paper x 0 $ 1 = of_real (real CARD('n))"
    using M_paper_at_zero_A[of x] by (metis of_real_of_nat_eq)
  have e2: "M_paper x 0 $ 2 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
    by (rule M_paper_at_zero_M1)
  have e3: "M_paper x 0 $ 3 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
    by (rule M_paper_at_zero_M2)
  show "M_paper x 0 $ 1 = of_real (Re (M_paper x 0 $ 1))"
    by (subst e1)+ simp
  show "M_paper x 0 $ 2 = of_real (Re (M_paper x 0 $ 2))"
    by (subst e2)+ simp
  show "M_paper x 0 $ 3 = of_real (Re (M_paper x 0 $ 3))"
    by (subst e3)+ simp
qed

lemma Afun_at_zero_real:
  fixes x :: "(real^2)^'n"
  shows "Afun x 0 = of_real (Re (Afun x 0))"
proof -
  have "Afun x 0 = (\<Sum>n\<in>(UNIV::'n set). cis 0)"
    by (simp add: Afun_def)
  also have "\<dots> = of_real (real CARD('n))" by simp
  finally show ?thesis by simp
qed

lemma Mcfun_at_zero_real:
  fixes x :: "(real^2)^'n"
  shows "Mcfun x 0 k = of_real (Re (Mcfun x 0 k))"
proof -
  have "Mcfun x 0 k = (\<Sum>n\<in>(UNIV::'n set). complex_of_real ((x$n)$k) * cis 0)"
    by (simp add: Mcfun_def)
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x$n)$k)" by simp
  finally show ?thesis by simp
qed

lemma M2cfun_at_zero_real:
  fixes x :: "(real^2)^'n"
  shows "M2cfun x 0 k l = of_real (Re (M2cfun x 0 k l))"
proof -
  have "M2cfun x 0 k l
      = (\<Sum>n\<in>(UNIV::'n set). complex_of_real ((x$n)$k) * complex_of_real ((x$n)$l) * cis 0)"
    by (simp add: M2cfun_def)
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l))" by simp
  finally show ?thesis by simp
qed


section \<open>The \<open>c\<close>-gradient \<open>\<nabla>\<^sub>c V\<close> vanishes at a beam center\<close>

text \<open>At \<open>c = 0\<close> the first three moments are real, so the steering term
  \<open>2 Re(cnj A ((-\<ii>) d\<^sub>1 M\<^sub>1 + (-\<ii>) d\<^sub>2 M\<^sub>2))\<close> is the real part of a purely imaginary
  number, hence \<open>0\<close>.  This is the c-side counterpart of D2's \<open>gradU_at_beamcenter\<close>.\<close>

lemma gradUc_at_beamcenter:
  fixes x :: "(real^2)^'n"
  shows "gradU (\<lambda>c. c) (\<lambda>_. 1) x 0 = (0 :: real^2)"
proof -
  have comp: "gradU (\<lambda>c. c) (\<lambda>_. 1) x 0 $ j = 0" for j
  proof -
    define A where "A = M_paper x 0 $ 1"
    define M1 where "M1 = M_paper x 0 $ 2"
    define M2 where "M2 = M_paper x 0 $ 3"
    define d1 where "d1 = (axis j 1 :: real^2)$1"
    define d2 where "d2 = (axis j 1 :: real^2)$2"
    have Ar: "A = of_real (Re A)" unfolding A_def by (rule M_paper_at_zero_real123(1))
    have M1r: "M1 = of_real (Re M1)" unfolding M1_def by (rule M_paper_at_zero_real123(2))
    have M2r: "M2 = of_real (Re M2)" unfolding M2_def by (rule M_paper_at_zero_real123(3))
    have steer0: "Re (cnj A * ((- \<i>) * complex_of_real d1 * M1
                            + (- \<i>) * complex_of_real d2 * M2)) = 0"
    proof -
      have "cnj A * ((- \<i>) * complex_of_real d1 * M1 + (- \<i>) * complex_of_real d2 * M2)
          = of_real (Re A) * ((- \<i>) * complex_of_real d1 * of_real (Re M1)
                            + (- \<i>) * complex_of_real d2 * of_real (Re M2))"
        using Ar M1r M2r by (metis Complex.complex_cnj_complex_of_real)
      also have "\<dots> = complex_of_real (Re A * (d1 * Re M1 + d2 * Re M2)) * (- \<i>)"
        by (simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    have base: "gradU (\<lambda>c. c) (\<lambda>_. 1) x 0 $ j
       = 2 * Re (cnj (M_paper x 0 $ 1)
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * (M_paper x 0 $ 2)
             + (- \<i>) * complex_of_real ((axis j 1)$2) * (M_paper x 0 $ 3)))"
      by (rule gradUc_component_moments)
    show ?thesis
      unfolding base using steer0 unfolding A_def M1_def M2_def d1_def d2_def by simp
  qed
  show ?thesis by (simp add: Finite_Cartesian_Product.vec_eq_iff comp)
qed

text \<open>And the value \<open>V = |A|\<^sup>2 = N\<^sup>2\<close> at a beam center.\<close>

lemma Uc_at_beamcenter:
  fixes x :: "(real^2)^'n"
  shows "U_cart (\<lambda>c. c) (\<lambda>_. 1) x 0 = (real CARD('n))\<^sup>2"
proof -
  have "U_cart (\<lambda>c. c) (\<lambda>_. 1) x 0 = (cmod (M_paper x 0 $ 1))\<^sup>2"
    by (rule Uc_eq_moment)
  also have "M_paper x 0 $ 1 = of_nat CARD('n)"
    by (simp add: M_paper_proj_A A_cart_def A_moment_def phase_def)
  finally show ?thesis by (simp add: norm_of_nat)
qed


section \<open>The Hessian collapses to the covariance form at a beam center\<close>

text \<open>Using \<open>\<nabla>\<^sub>c V = 0\<close> the three \<open>\<nabla>\<^sub>c V\<close>-terms of the general entry formula
  @{thm HessU_dip_entry_moments} drop, leaving the curvature term \<open>gain \<cdot> e\<^sub>k\<^sup>T D\<^sup>T H\<^sub>c D e\<^sub>l\<close>
  and the \<open>gdip''\<close>-term \<open>(\<partial>\<^sub>\<omega>\<partial>gdip)\<^sub>k\<^sub>l \<cdot> V\<close>.\<close>

lemma HessU_at_beamcenter_entry:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))
       + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
           * (real CARD('n))\<^sup>2"
proof -
  have gc: "gradU (\<lambda>c. c) (\<lambda>_. 1) x 0 = (0 :: real^2)"
    by (rule gradUc_at_beamcenter)
  have uc: "U_cart (\<lambda>c. c) (\<lambda>_. 1) x 0 = (real CARD('n))\<^sup>2"
    by (rule Uc_at_beamcenter)
  show ?thesis
    unfolding HessU_dip_entry_moments c0 gc uc by simp
qed


section \<open>The beam-center Hessian entries are polynomials (line-entire) in \<open>x\<close>\<close>

text \<open>At \<open>c = 0\<close> the moment functions are real polynomials in the Cartesian coordinates of
  \<open>x\<close>, so they have entire line restrictions.  We give the real-valued (\<open>rline_entire\<close>)
  forms of \<open>Re (Afun x 0)\<close>, \<open>Re (Mcfun x 0 k)\<close>, \<open>Re (M2cfun x 0 k l)\<close>, then assemble
  \<open>Hcmat x 0 $ i $ j\<close> and the whole Hessian entry.\<close>

lemma Re_Afun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "Re (Afun x 0) = real CARD('n)"
proof -
  have "Afun x 0 = (\<Sum>n\<in>(UNIV::'n set). cis 0)" by (simp add: Afun_def)
  also have "\<dots> = of_nat CARD('n)" by simp
  finally show ?thesis by simp
qed

lemma Re_Mcfun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "Re (Mcfun x 0 k) = (\<Sum>n\<in>(UNIV::'n set). (x$n)$k)"
proof -
  have "Mcfun x 0 k = (\<Sum>n\<in>(UNIV::'n set). complex_of_real ((x$n)$k) * cis 0)"
    by (simp add: Mcfun_def)
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x$n)$k)" by simp
  finally show ?thesis by simp
qed

lemma Re_M2cfun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "Re (M2cfun x 0 k l) = (\<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l))"
proof -
  have "M2cfun x 0 k l
      = (\<Sum>n\<in>(UNIV::'n set). complex_of_real ((x$n)$k) * complex_of_real ((x$n)$l) * cis 0)"
    by (simp add: M2cfun_def)
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l))" by simp
  finally show ?thesis by simp
qed

text \<open>The \<open>(k,l)\<close> entry of the covariance matrix \<open>Hcmat x 0\<close> in real polynomial form.\<close>

lemma Hcmat_at_zero_entry:
  fixes x :: "(real^2)^'n"
  shows "Hcmat x 0 $ k $ l
       = 2 * ((\<Sum>n\<in>(UNIV::'n set). (x$n)$l) * (\<Sum>n\<in>(UNIV::'n set). (x$n)$k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l)))"
proof -
  have a: "Afun x 0 = of_real (Re (Afun x 0))" by (rule Afun_at_zero_real)
  have m_l: "Mcfun x 0 l = of_real (Re (Mcfun x 0 l))" by (rule Mcfun_at_zero_real)
  have m_k: "Mcfun x 0 k = of_real (Re (Mcfun x 0 k))" by (rule Mcfun_at_zero_real)
  have m2: "M2cfun x 0 k l = of_real (Re (M2cfun x 0 k l))" by (rule M2cfun_at_zero_real)
  have re1: "Re (cnj (Mcfun x 0 l) * Mcfun x 0 k)
           = (\<Sum>n\<in>(UNIV::'n set). (x$n)$l) * (\<Sum>n\<in>(UNIV::'n set). (x$n)$k)"
    by (subst m_l, subst m_k) (simp add: Re_Mcfun_at_zero)
  have re2: "Re (cnj (Afun x 0) * M2cfun x 0 k l)
           = real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l))"
    by (subst a, subst m2) (simp add: Re_Afun_at_zero Re_M2cfun_at_zero)
  show ?thesis
    unfolding Hcmat_def vec_lambda_beta using re1 re2 by simp
qed

text \<open>Each covariance entry, as a function of \<open>x\<close>, has entire line restrictions (it is a
  real polynomial in the Cartesian coordinates).\<close>

lemma rline_entire_Hcmat_at_zero:
  fixes k l :: 2
  shows "rline_entire (\<lambda>x::(real^2)^'n. Hcmat x 0 $ k $ l)"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. Hcmat x 0 $ k $ l)
      = (\<lambda>x. 2 * ((\<Sum>n\<in>(UNIV::'n set). (x$n)$l) * (\<Sum>n\<in>(UNIV::'n set). (x$n)$k))
            + (- 2 * real CARD('n)) * (\<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l)))"
    by (rule ext) (simp add: Hcmat_at_zero_entry algebra_simps)
  have s_l: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). (x$n)$l)"
    by (intro rline_entire_sum) (auto intro: rline_entire_coord)
  have s_k: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). (x$n)$k)"
    by (intro rline_entire_sum) (auto intro: rline_entire_coord)
  have s_kl: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l))"
    by (intro rline_entire_sum)
       (auto intro: rline_entire_mult rline_entire_coord)
  have p1: "rline_entire (\<lambda>x::(real^2)^'n.
        2 * ((\<Sum>n\<in>(UNIV::'n set). (x$n)$l) * (\<Sum>n\<in>(UNIV::'n set). (x$n)$k)))"
    by (rule rline_entire_scale[OF rline_entire_mult[OF s_l s_k]])
  have p2: "rline_entire (\<lambda>x::(real^2)^'n.
        (- 2 * real CARD('n)) * (\<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l)))"
    by (rule rline_entire_scale[OF s_kl])
  show ?thesis
    unfolding eq by (rule rline_entire_add[OF p1 p2])
qed

text \<open>The quadratic form \<open>e\<^sub>k\<^sup>T D\<^sup>T H\<^sub>c D e\<^sub>l\<close> expanded entrywise over the 2-dim inner
  product and matrix-vector product (cf. \<open>qform\<close> in \<open>det_HessU_at_null\<close>).\<close>

lemma Hcmat_qform_at_zero:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
          \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
       = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 1)
           * ((Hcmat x 0 $ 1 $ 1) * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1)
              + (Hcmat x 0 $ 1 $ 2) * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2))
       + (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 2)
           * ((Hcmat x 0 $ 2 $ 1) * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1)
              + (Hcmat x 0 $ 2 $ 2) * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2))"
  unfolding inner_vec_def matrix_vector_mult_def
  by (simp add: sum_2)

text \<open>Each beam-center Hessian entry, as a function of \<open>x\<close>, has entire line restrictions.
  The \<open>Dcvec\<close> coefficients and the \<open>gdip''\<close>/\<open>N\<^sup>2\<close> term are constants in \<open>x\<close>; the
  \<open>x\<close>-dependence routes solely through the four covariance entries.\<close>

lemma rline_entire_HessU_at_beamcenter_entry:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and k l :: 2
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "rline_entire (\<lambda>x::(real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l)"
proof -
  define G where "G = frechet_derivative
        (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
      * (real CARD('n))\<^sup>2"
  define a1 where "a1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 1"
  define a2 where "a2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 2"
  define b1 where "b1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1"
  define b2 where "b2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2"
  have eq: "(\<lambda>x::(real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l)
      = (\<lambda>x. gain_dip \<omega> * (a1 * ((Hcmat x 0 $ 1 $ 1) * b1 + (Hcmat x 0 $ 1 $ 2) * b2)
                          + a2 * ((Hcmat x 0 $ 2 $ 1) * b1 + (Hcmat x 0 $ 2 $ 2) * b2))
             + G)"
    by (rule ext)
       (simp add: HessU_at_beamcenter_entry[OF c0] Hcmat_qform_at_zero
                  G_def a1_def a2_def b1_def b2_def)
  \<comment> \<open>rline-entire building blocks\<close>
  have h11: "rline_entire (\<lambda>x::(real^2)^'n. Hcmat x 0 $ 1 $ 1)" by (rule rline_entire_Hcmat_at_zero)
  have h12: "rline_entire (\<lambda>x::(real^2)^'n. Hcmat x 0 $ 1 $ 2)" by (rule rline_entire_Hcmat_at_zero)
  have h21: "rline_entire (\<lambda>x::(real^2)^'n. Hcmat x 0 $ 2 $ 1)" by (rule rline_entire_Hcmat_at_zero)
  have h22: "rline_entire (\<lambda>x::(real^2)^'n. Hcmat x 0 $ 2 $ 2)" by (rule rline_entire_Hcmat_at_zero)
  have inner1: "rline_entire (\<lambda>x::(real^2)^'n.
        a1 * ((Hcmat x 0 $ 1 $ 1) * b1 + (Hcmat x 0 $ 1 $ 2) * b2))"
    by (intro rline_entire_scale rline_entire_add
              rline_entire_mult[OF h11 rline_entire_const]
              rline_entire_mult[OF h12 rline_entire_const])
  have inner2: "rline_entire (\<lambda>x::(real^2)^'n.
        a2 * ((Hcmat x 0 $ 2 $ 1) * b1 + (Hcmat x 0 $ 2 $ 2) * b2))"
    by (intro rline_entire_scale rline_entire_add
              rline_entire_mult[OF h21 rline_entire_const]
              rline_entire_mult[OF h22 rline_entire_const])
  have qf: "rline_entire (\<lambda>x::(real^2)^'n.
        gain_dip \<omega> * (a1 * ((Hcmat x 0 $ 1 $ 1) * b1 + (Hcmat x 0 $ 1 $ 2) * b2)
                    + a2 * ((Hcmat x 0 $ 2 $ 1) * b1 + (Hcmat x 0 $ 2 $ 2) * b2)))"
    by (rule rline_entire_scale[OF rline_entire_add[OF inner1 inner2]])
  show ?thesis
    unfolding eq by (rule rline_entire_add[OF qf rline_entire_const])
qed

text \<open>Hence the determinant of the beam-center Hessian, as a function of \<open>x\<close>, has entire
  line restrictions.\<close>

lemma rline_entire_det_HessU_at_beamcenter:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "rline_entire (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  by (rule rline_entire_det_fun)
     (rule rline_entire_HessU_at_beamcenter_entry[OF c0])


section \<open>Continuity of the beam-center Hessian determinant in \<open>x\<close>\<close>

text \<open>The covariance entries are polynomials in the Cartesian coordinates, hence
  continuous; the Hessian entries are polynomial in them; the determinant follows by
  @{thm continuous_on_det_fun}.\<close>

lemma continuous_on_Hcmat_at_zero_entry:
  fixes k l :: 2
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. Hcmat x 0 $ k $ l)"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. Hcmat x 0 $ k $ l)
      = (\<lambda>x. 2 * ((\<Sum>n\<in>(UNIV::'n set). (x$n)$l) * (\<Sum>n\<in>(UNIV::'n set). (x$n)$k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). ((x$n)$k) * ((x$n)$l))))"
    by (rule ext) (rule Hcmat_at_zero_entry)
  have c: "continuous_on UNIV (\<lambda>x::(real^2)^'n. (x$n)$j)" for n :: 'n and j :: 2
    by (rule bounded_linear.continuous_on[OF
          bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth]
          continuous_on_id])
  show ?thesis
    unfolding eq
    by (intro continuous_on_mult continuous_on_const continuous_on_diff
              continuous_on_sum c)
qed

lemma continuous_on_HessU_at_beamcenter_entry:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and k l :: 2
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l)"
proof -
  define G where "G = frechet_derivative
        (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
      * (real CARD('n))\<^sup>2"
  define a1 where "a1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 1"
  define a2 where "a2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 2"
  define b1 where "b1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1"
  define b2 where "b2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2"
  have eq: "(\<lambda>x::(real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l)
      = (\<lambda>x. gain_dip \<omega> * (a1 * ((Hcmat x 0 $ 1 $ 1) * b1 + (Hcmat x 0 $ 1 $ 2) * b2)
                          + a2 * ((Hcmat x 0 $ 2 $ 1) * b1 + (Hcmat x 0 $ 2 $ 2) * b2))
             + G)"
    by (rule ext)
       (simp add: HessU_at_beamcenter_entry[OF c0] Hcmat_qform_at_zero
                  G_def a1_def a2_def b1_def b2_def)
  show ?thesis
    unfolding eq
    by (intro continuous_on_add continuous_on_mult continuous_on_const
              continuous_on_Hcmat_at_zero_entry)
qed

lemma continuous_on_det_HessU_at_beamcenter:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  by (rule continuous_on_det_fun)
     (rule continuous_on_HessU_at_beamcenter_entry[OF c0])


section \<open>The \<open>gdip''\<close> term collapses to a single \<open>e\<^sub>1 e\<^sub>1\<close> entry\<close>

text \<open>The gain's second-\<open>\<omega>\<close>-derivative term
  \<open>G\<^sub>k\<^sub>l = (\<partial>\<^sub>\<omega> \<partial>gdip)\<^sub>k\<^sub>l = frechet_derivative (\<lambda>\<eta>. \<partial>gdip(\<eta>\<^sub>1)((e\<^sub>k)\<^sub>1)) (at \<omega>) (e\<^sub>l)\<close>
  vanishes whenever \<open>k = 2\<close> (because \<open>(e\<^sub>2)\<^sub>1 = 0\<close> and \<open>\<partial>gdip(\<cdot>) 0 = 0\<close>) and whenever
  \<open>l = 2\<close> (the inner field depends on \<open>\<eta>\<close> only through \<open>\<eta>\<^sub>1\<close>, so its derivative in the
  \<open>e\<^sub>2\<close>-direction is \<open>0\<close>).  Only \<open>G\<^sub>1\<^sub>1\<close> survives; we abbreviate it \<open>gdip2 \<omega>\<close>.\<close>

definition gdip2 :: "real^2 \<Rightarrow> real" where
  "gdip2 \<omega> = frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>) (axis 1 1)"

lemma Gterm_k2_zero:
  fixes \<omega> :: "real^2"
  shows "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) ((axis (2::2) 1)$1)) (at \<omega>) v
       = 0"
proof -
  have a0: "((axis (2::2) 1) :: real^2)$1 = 0" by (simp add: axis_def)
  have "(\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) ((axis (2::2) 1)$1))
      = (\<lambda>\<eta>::real^2. (0::real))"
    by (rule ext) (simp add: a0 frechet_gdip_zero_arg)
  thus ?thesis by (simp add: frechet_derivative_const)
qed

text \<open>The inner field \<open>\<eta> \<mapsto> \<partial>gdip(\<eta>\<^sub>1) r\<close> factors through \<open>\<eta> \<mapsto> \<eta>\<^sub>1\<close>, so its
  total derivative at \<open>\<omega>\<close> sends \<open>h \<mapsto> (deriv-of-\<open>t \<mapsto> \<partial>gdip(t) r\<close> at \<omega>\<^sub>1) * h\<^sub>1\<close>; in
  particular the \<open>e\<^sub>2\<close>-directional derivative is \<open>0\<close> and the \<open>e\<^sub>1\<close>-directional one is the
  scalar second derivative.\<close>

lemma frechet2_gdip_proj_has_derivative:
  fixes \<omega> :: "real^2" and r :: real
  shows "((\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) r) has_derivative
            (\<lambda>h. frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) r) (at (\<omega>$1)) (h$1))) (at \<omega>)"
proof -
  \<comment> \<open>inner one-variable field is differentiable (gdip is \<open>C\<^sup>\<infinity>\<close>)\<close>
  have d1: "(\<lambda>t. frechet_derivative gdip (at t) r) differentiable (at (\<omega>$1))"
    by (rule gdip_deriv_differentiable)
  obtain D where D: "((\<lambda>t. frechet_derivative gdip (at t) r) has_derivative D) (at (\<omega>$1))"
    using d1 unfolding differentiable_def by blast
  have proj: "((\<lambda>\<eta>::real^2. \<eta>$1) has_derivative (\<lambda>h. h$1)) (at \<omega>)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_ident])
  have "((\<lambda>t. frechet_derivative gdip (at t) r) \<circ> (\<lambda>\<eta>::real^2. \<eta>$1) has_derivative
            (D \<circ> (\<lambda>h. h$1))) (at \<omega>)"
    by (rule diff_chain_at[OF proj D])
  hence hd: "((\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) r) has_derivative
            (\<lambda>h. D (h$1))) (at \<omega>)"
    by (simp add: o_def)
  have Deq: "D = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) r) (at (\<omega>$1))"
    by (rule frechet_derivative_at[OF D])
  show ?thesis using hd unfolding Deq .
qed

lemma Gterm_l2_zero:
  fixes \<omega> :: "real^2" and r :: real
  shows "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) r) (at \<omega>) (axis 2 1) = 0"
proof -
  have a0: "((axis (2::2) 1) :: real^2)$1 = 0" by (simp add: axis_def)
  have fd: "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) r) (at \<omega>)
          = (\<lambda>h. frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) r) (at (\<omega>$1)) (h$1))"
    by (rule frechet_derivative_at[symmetric, OF frechet2_gdip_proj_has_derivative])
  have "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) r) (at \<omega>) (axis 2 1)
      = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) r) (at (\<omega>$1)) ((axis (2::2) 1)$1)"
    by (subst fd) (rule refl)
  also have "\<dots> = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) r) (at (\<omega>$1)) 0"
    by (simp add: a0)
  also have "\<dots> = 0"
    using linear_frechet_derivative[OF gdip_deriv_differentiable] linear_0 by blast
  finally show ?thesis .
qed


section \<open>The four beam-center Hessian entries in terms of the quadratic form\<close>

text \<open>The \<open>gdip''\<close>-term \<open>G\<^sub>k\<^sub>l\<close> contributes only at \<open>(1,1)\<close>, where it equals \<open>gdip2 \<omega>\<close>.\<close>

lemma Gterm_eq:
  fixes \<omega> :: "real^2" and k l :: 2
  shows "frechet_derivative
           (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
       = (if k = 1 \<and> l = 1 then gdip2 \<omega> else 0)"
proof (cases "k = 1")
  case k1: True
  have one: "((axis (1::2) 1)::real^2)$1 = 1" by (simp add: axis_def)
  show ?thesis
  proof (cases "l = 1")
    case True
    show ?thesis using k1 True
      by (simp add: one gdip2_def)
  next
    case False
    hence l2: "l = 2" by (metis (full_types) exhaust_2)
    show ?thesis using k1 l2
      by (simp add: one Gterm_l2_zero)
  qed
next
  case False
  hence k2: "k = 2" by (metis (full_types) exhaust_2)
  show ?thesis using k2 by (simp add: Gterm_k2_zero)
qed

text \<open>Abbreviating \<open>q\<^sub>k\<^sub>l = e\<^sub>k\<^sup>T D\<^sup>T H\<^sub>c D e\<^sub>l\<close>, the four entries are
  \<open>H\<^sub>1\<^sub>1 = gain q\<^sub>1\<^sub>1 + gdip2 \<omega> N\<^sup>2\<close>, \<open>H\<^sub>1\<^sub>2 = gain q\<^sub>1\<^sub>2\<close>, \<open>H\<^sub>2\<^sub>1 = gain q\<^sub>2\<^sub>1\<close>,
  \<open>H\<^sub>2\<^sub>2 = gain q\<^sub>2\<^sub>2\<close>.\<close>

definition qf :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> 2 \<Rightarrow> real" where
  "qf x \<omega>0 \<omega>s \<omega> k l = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                       \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))"

lemma HessU_entry_qf:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2" and k l :: 2
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * qf x \<omega>0 \<omega>s \<omega> k l
       + (if k = 1 \<and> l = 1 then gdip2 \<omega> * (real CARD('n))\<^sup>2 else 0)"
  unfolding HessU_at_beamcenter_entry[OF c0] qf_def Gterm_eq by simp

text \<open>The master determinant formula at a beam center.\<close>

lemma det_HessU_at_beamcenter:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
       = (gain_dip \<omega>)\<^sup>2 * (qf x \<omega>0 \<omega>s \<omega> 1 1 * qf x \<omega>0 \<omega>s \<omega> 2 2
                          - qf x \<omega>0 \<omega>s \<omega> 1 2 * qf x \<omega>0 \<omega>s \<omega> 2 1)
       + gain_dip \<omega> * gdip2 \<omega> * (real CARD('n))\<^sup>2 * qf x \<omega>0 \<omega>s \<omega> 2 2"
proof -
  have det2: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
      = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
        * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
      - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
        * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
    by (simp add: det_2)
  have e11: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
           = gain_dip \<omega> * qf x \<omega>0 \<omega>s \<omega> 1 1 + gdip2 \<omega> * (real CARD('n))\<^sup>2"
    using HessU_entry_qf[OF c0, where x = x and k = 1 and l = 1] by simp
  have e12: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2 = gain_dip \<omega> * qf x \<omega>0 \<omega>s \<omega> 1 2"
    using HessU_entry_qf[OF c0, where x = x and k = 1 and l = 2] by simp
  have e21: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1 = gain_dip \<omega> * qf x \<omega>0 \<omega>s \<omega> 2 1"
    using HessU_entry_qf[OF c0, where x = x and k = 2 and l = 1] by simp
  have e22: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2 = gain_dip \<omega> * qf x \<omega>0 \<omega>s \<omega> 2 2"
    using HessU_entry_qf[OF c0, where x = x and k = 2 and l = 2] by simp
  show ?thesis
    unfolding det2 e11 e12 e21 e22
    by (simp add: power2_eq_square algebra_simps)
qed


section \<open>The genuine residual: the second derivative \<open>gdip''\<close> at a cos-zero is nonzero\<close>

text \<open>\<^bold>\<open>GENUINE remaining math (NOT a Robust3 splice freebie).\<close>  At a cos-zero
  \<open>\<omega>\<^sub>1 = \<pi>/2 \<bmod> \<pi>\<close> the scalar second derivative of the dipole gain is
  \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close>.  This is the single-variable computation of the
  second derivative of the \<open>sinc\<close>-factored \<open>gdip\<close> (the first-derivative analysis underlies
  @{thm gdip_deriv_zero_iff}); we isolate its non-vanishing as a scoped proof hole.  It is the
  irreducible analytic core shared by both beam-center stubs.\<close>

lemma gdip2_nonzero_of_cos_zero:
  fixes \<omega> :: "real^2"
  assumes s1: "sin (\<omega> $ 1) \<noteq> 0" and cz: "cos (\<omega> $ 1) = 0"
  shows "gdip2 \<omega> \<noteq> 0"
  \<comment> \<open>GENUINE residual: \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close>, the second-derivative
      computation of the \<open>sinc\<close>-factored dipole gain.  NOT a Robust3 splice freebie.\<close>
  sorry


section \<open>Nontriviality witness: a one-point-displaced configuration\<close>

text \<open>For the one-point-displaced configuration \<open>x\<^sub>s = (\<dots>, p, \<dots>)\<close> (one element at
  \<open>p\<close>, all others at \<open>0\<close>), the covariance matrix is the rank-one form
  \<open>Hcmat x\<^sub>s 0 = 2(1-N) p p\<^sup>T\<close>.\<close>

lemma Hcmat_one_point:
  fixes p :: "real^2" and i0 :: "'n::finite"
  defines "xs \<equiv> (\<chi> n. if n = i0 then p else (0::real^2))"
  shows "Hcmat (xs::(real^2)^'n) 0 $ k $ l = 2 * (1 - real CARD('n)) * (p$k) * (p$l)"
proof -
  have s1: "(\<Sum>n\<in>(UNIV::'n set). (xs$n)$j) = p$j" for j
  proof -
    have "(\<Sum>n\<in>(UNIV::'n set). (xs$n)$j) = (xs$i0)$j + (\<Sum>n\<in>(UNIV::'n set)-{i0}. (xs$n)$j)"
      by (rule sum.remove) simp_all
    also have "(\<Sum>n\<in>(UNIV::'n set)-{i0}. (xs$n)$j) = (\<Sum>n\<in>(UNIV::'n set)-{i0}. 0)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    finally show ?thesis by (simp add: xs_def)
  qed
  have s2: "(\<Sum>n\<in>(UNIV::'n set). ((xs$n)$k) * ((xs$n)$l)) = (p$k) * (p$l)"
  proof -
    have "(\<Sum>n\<in>(UNIV::'n set). ((xs$n)$k) * ((xs$n)$l))
        = ((xs$i0)$k) * ((xs$i0)$l)
          + (\<Sum>n\<in>(UNIV::'n set)-{i0}. ((xs$n)$k) * ((xs$n)$l))"
      by (rule sum.remove) simp_all
    also have "(\<Sum>n\<in>(UNIV::'n set)-{i0}. ((xs$n)$k) * ((xs$n)$l))
             = (\<Sum>n\<in>(UNIV::'n set)-{i0}. 0)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    finally show ?thesis by (simp add: xs_def)
  qed
  show ?thesis
    unfolding Hcmat_at_zero_entry s1 s2 by (simp add: algebra_simps)
qed

text \<open>The quadratic form for the one-point witness: \<open>q\<^sub>k\<^sub>l = 2(1-N)(D e\<^sub>k \<bullet> p)(D e\<^sub>l \<bullet> p)\<close>.\<close>

lemma qf_one_point:
  fixes p :: "real^2" and i0 :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  defines "xs \<equiv> (\<chi> n. if n = i0 then p else (0::real^2))"
  shows "qf (xs::(real^2)^'n) \<omega>0 \<omega>s \<omega> k l
       = 2 * (1 - real CARD('n))
           * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> p)
           * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) \<bullet> p)"
proof -
  define c where "c = 2 * (1 - real CARD('n))"
  have H: "Hcmat (xs::(real^2)^'n) 0 $ i $ j = c * (p$i) * (p$j)" for i j
    unfolding c_def xs_def by (rule Hcmat_one_point)
  have "qf (xs::(real^2)^'n) \<omega>0 \<omega>s \<omega> k l
      = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 1)
          * ((Hcmat (xs::(real^2)^'n) 0 $ 1 $ 1) * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1)
             + (Hcmat (xs::(real^2)^'n) 0 $ 1 $ 2) * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2))
      + (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 2)
          * ((Hcmat (xs::(real^2)^'n) 0 $ 2 $ 1) * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1)
             + (Hcmat (xs::(real^2)^'n) 0 $ 2 $ 2) * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2))"
    unfolding qf_def by (rule Hcmat_qform_at_zero)
  also have "\<dots> = c * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> p)
                    * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) \<bullet> p)"
    unfolding H by (simp add: inner_vec_def sum_2 algebra_simps)
  finally show ?thesis unfolding c_def .
qed

text \<open>Choosing \<open>p = D e\<^sub>2\<close> (nonzero off the poles) makes the \<open>gain\<^sup>2\<close>-term vanish (rank-one
  covariance) and the witness determinant collapses to the nonzero
  \<open>gain \<cdot> gdip2 \<omega> \<cdot> N\<^sup>2 \<cdot> 2(1-N) \<cdot> (D e\<^sub>2 \<bullet> D e\<^sub>2)\<close>.\<close>

lemma det_HessU_nontrivial_witness:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0" and cz: "cos (\<omega> $ 1) = 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "\<exists>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
proof -
  define i0 :: 'n where "i0 = undefined"
  define p :: "real^2" where "p = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  define xs :: "(real^2)^'n" where "xs = (\<chi> n. if n = i0 then p else 0)"
  define N where "N = real CARD('n)"
  define D2p where "D2p = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> p"
  define D1p where "D1p = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> p"
  \<comment> \<open>the four quadratic-form values at the witness\<close>
  have q11: "qf xs \<omega>0 \<omega>s \<omega> 1 1 = 2 * (1 - N) * D1p * D1p"
    unfolding xs_def N_def D1p_def by (rule qf_one_point)
  have q22: "qf xs \<omega>0 \<omega>s \<omega> 2 2 = 2 * (1 - N) * D2p * D2p"
    unfolding xs_def N_def D2p_def by (rule qf_one_point)
  have q12: "qf xs \<omega>0 \<omega>s \<omega> 1 2 = 2 * (1 - N) * D1p * D2p"
    unfolding xs_def N_def D1p_def D2p_def by (rule qf_one_point)
  have q21: "qf xs \<omega>0 \<omega>s \<omega> 2 1 = 2 * (1 - N) * D2p * D1p"
    unfolding xs_def N_def D1p_def D2p_def by (rule qf_one_point)
  \<comment> \<open>rank-one covariance kills the \<open>gain\<^sup>2\<close>-term\<close>
  have cross0: "qf xs \<omega>0 \<omega>s \<omega> 1 1 * qf xs \<omega>0 \<omega>s \<omega> 2 2
              - qf xs \<omega>0 \<omega>s \<omega> 1 2 * qf xs \<omega>0 \<omega>s \<omega> 2 1 = 0"
    unfolding q11 q22 q12 q21 by (simp add: algebra_simps)
  have detval: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>)
              = gain_dip \<omega> * gdip2 \<omega> * N\<^sup>2 * (2 * (1 - N) * D2p * D2p)"
  proof -
    have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>)
        = (gain_dip \<omega>)\<^sup>2 * (qf xs \<omega>0 \<omega>s \<omega> 1 1 * qf xs \<omega>0 \<omega>s \<omega> 2 2
                           - qf xs \<omega>0 \<omega>s \<omega> 1 2 * qf xs \<omega>0 \<omega>s \<omega> 2 1)
        + gain_dip \<omega> * gdip2 \<omega> * (real CARD('n))\<^sup>2 * qf xs \<omega>0 \<omega>s \<omega> 2 2"
      by (rule det_HessU_at_beamcenter[OF c0])
    also have "\<dots> = gain_dip \<omega> * gdip2 \<omega> * (real CARD('n))\<^sup>2 * qf xs \<omega>0 \<omega>s \<omega> 2 2"
      unfolding cross0 by simp
    also have "\<dots> = gain_dip \<omega> * gdip2 \<omega> * N\<^sup>2 * (2 * (1 - N) * D2p * D2p)"
      unfolding q22 N_def by simp
    finally show ?thesis .
  qed
  \<comment> \<open>each factor is nonzero\<close>
  have gnz: "gain_dip \<omega> \<noteq> 0" by (rule gain_dip_nonzero_of_sin[OF pfw])
  have g2nz: "gdip2 \<omega> \<noteq> 0" by (rule gdip2_nonzero_of_cos_zero[OF pfw cz])
  have Nnz: "N\<^sup>2 \<noteq> 0" unfolding N_def using c6 by simp
  have N1: "(1 - N) \<noteq> 0" unfolding N_def using c6 by simp
  have pnz: "p \<noteq> 0" unfolding p_def by (rule Dcvec_col2_nz[OF pfw])
  have D2p_eq: "D2p = p \<bullet> p" unfolding D2p_def p_def by simp
  have D2pnz: "D2p \<noteq> 0" unfolding D2p_eq using pnz by simp
  have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>) \<noteq> 0"
    unfolding detval using gnz g2nz Nnz N1 D2pnz by simp
  thus ?thesis by blast
qed


section \<open>Off a cos-zero, criticality at a beam center is impossible\<close>

text \<open>At a beam center the first gradient component is \<open>gdip'(\<omega>\<^sub>1) N\<^sup>2\<close> (copy of D2's
  \<open>gradU_at_beamcenter\<close> machinery, restated here).  If \<open>cos(\<omega>\<^sub>1) \<noteq> 0\<close> (off the poles)
  then \<open>gdip'(\<omega>\<^sub>1) \<noteq> 0\<close>, so \<open>gradU $ 1 \<noteq> 0\<close> for \<^emph>\<open>every\<close> \<open>x\<close>, hence the criticality
  conjunct \<open>gradU = 0\<close> is never satisfied.\<close>

lemma gradU_at_beamcenter_component:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
       = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
           * (cmod (M_paper x 0 $ 1))\<^sup>2"
proof -
  define A where "A = M_paper x 0 $ 1"
  define M2 where "M2 = M_paper x 0 $ 2"
  define M3 where "M3 = M_paper x 0 $ 3"
  define dj1 where "dj1 = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1"
  define dj2 where "dj2 = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2"
  have Ar: "A = of_real (Re A)" unfolding A_def by (rule M_paper_at_zero_real123(1))
  have M2r: "M2 = of_real (Re M2)" unfolding M2_def by (rule M_paper_at_zero_real123(2))
  have M3r: "M3 = of_real (Re M3)" unfolding M3_def by (rule M_paper_at_zero_real123(3))
  have steer0: "Re (cnj A * ((- \<i>) * complex_of_real dj1 * M2
                            + (- \<i>) * complex_of_real dj2 * M3)) = 0"
  proof -
    have "cnj A * ((- \<i>) * complex_of_real dj1 * M2 + (- \<i>) * complex_of_real dj2 * M3)
        = of_real (Re A) * ((- \<i>) * complex_of_real dj1 * of_real (Re M2)
                          + (- \<i>) * complex_of_real dj2 * of_real (Re M3))"
      using Ar M2r M3r by (metis Complex.complex_cnj_complex_of_real)
    also have "\<dots> = complex_of_real (Re A * (dj1 * Re M2 + dj2 * Re M3)) * (- \<i>)"
      by (simp add: algebra_simps)
    finally show ?thesis by simp
  qed
  have base: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
       = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
             * (cmod (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2
           + gain_dip \<omega> * (2 * Re (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
                * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1)
                     * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
                 + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                     * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))))"
    by (rule gradU_dip_component_moments)
  show ?thesis
    unfolding base c0
    using steer0 unfolding A_def M2_def M3_def dj1_def dj2_def by simp
qed

lemma gradU_beamcenter_comp1:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
       = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
proof -
  have a1: "((axis (1::2) 1 :: real^2) $ 1) = 1" by (simp add: axis_def)
  have NA: "cmod (M_paper x 0 $ 1) = real CARD('n)"
    using M_paper_at_zero_A[of x] by (simp add: norm_of_nat)
  have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
       = frechet_derivative gdip (at (\<omega>$1)) ((axis (1::2) 1)$1)
           * (cmod (M_paper x 0 $ 1))\<^sup>2"
    by (rule gradU_at_beamcenter_component[OF c0, of x 1])
  also have "\<dots> = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
    by (subst a1, subst NA, rule refl)
  finally show ?thesis .
qed

lemma beamcenter_bad_empty_of_cos_ne:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and s1: "sin (\<omega> $ 1) \<noteq> 0"
    and cn: "cos (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "{x :: (real^2)^'n. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and> P x} = {}"
proof -
  have Npos: "(0::real) < real CARD('n)" using c6 by simp
  have gd: "frechet_derivative gdip (at (\<omega>$1)) 1 \<noteq> 0"
    using gdip_deriv_zero_iff[OF s1] cn by blast
  { fix x :: "(real^2)^'n"
    assume "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    hence "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0" by simp
    hence "frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2 = 0"
      using gradU_beamcenter_comp1[OF c0, of x] by simp
    hence False using gd Npos by simp
  }
  thus ?thesis by blast
qed


section \<open>The det-zero locus is nowhere dense at a beam center (cos-zero case)\<close>

text \<open>Apply the analytic-slice engine to \<open>x \<mapsto> det (HessU x \<omega>)\<close>: it is continuous, has
  entire line restrictions, and (at a cos-zero) is not identically zero by the one-point
  witness.\<close>

lemma det_HessU_zero_nowhere_dense_cos0:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and cz: "cos (\<omega> $ 1) = 0" and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "nowhere_dense {x :: (real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
proof -
  define f where "f = (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  have cont: "continuous_on UNIV f"
    unfolding f_def by (rule continuous_on_det_HessU_at_beamcenter[OF c0])
  have rl: "rline_entire f"
    unfolding f_def by (rule rline_entire_det_HessU_at_beamcenter[OF c0])
  have ntv: "\<exists>x. f x \<noteq> 0"
    unfolding f_def by (rule det_HessU_nontrivial_witness[OF c6 pfw cz c0])
  have nd: "nowhere_dense {x \<in> (UNIV :: ((real^2)^'n) set). f x = 0}"
  proof (rule lines_entire_slice_nowhere_dense[OF cont _ ntv])
    show "\<And>a v. \<exists>F. F holomorphic_on UNIV
            \<and> (\<forall>t::real. F (complex_of_real t) = complex_of_real (f (a + t *\<^sub>R v)))"
      using rl unfolding rline_entire_def by blast
  qed
  have seq: "{x \<in> (UNIV :: ((real^2)^'n) set). f x = 0}
           = {x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by (auto simp: f_def)
  show ?thesis using nd unfolding seq .
qed


section \<open>Target 1 (D2): the beam-center slice is nowhere dense\<close>

lemma m5_D2_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "nowhere_dense {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
proof (cases "cos (\<omega> $ 1) = 0")
  case True
  have nd: "nowhere_dense {x :: (real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by (rule det_HessU_zero_nowhere_dense_cos0[OF c6 pfw True cz])
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}
        \<subseteq> {x :: (real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by blast
  show ?thesis by (rule nowhere_dense_subset[OF sub nd])
next
  case False
  have e: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0} = {}"
    by (rule beamcenter_bad_empty_of_cos_ne[OF c6 pfw False cz])
  show ?thesis unfolding e by (rule nowhere_dense_empty)
qed


section \<open>Target 2 (D5): the beam-center slice is meager\<close>

lemma m5_D5_beamcenter_angle_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
proof (cases "cos (\<omega> $ 1) = 0")
  case True
  have nd: "nowhere_dense {x :: (real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by (rule det_HessU_zero_nowhere_dense_cos0[OF c6 pfw True c0])
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
        \<subseteq> {x :: (real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by blast
  show ?thesis by (rule meager_subset[OF sub meager_nowhere_dense[OF nd]])
next
  case False
  have e: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0} = {}"
    by (rule beamcenter_bad_empty_of_cos_ne[OF c6 pfw False c0])
  show ?thesis unfolding e by (rule meager_empty)
qed

end
