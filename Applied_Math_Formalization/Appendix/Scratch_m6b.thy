theory Scratch_m6b
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>(M6b) development: the \<open>A = 0\<close> degenerate stratum is meager, via the planar
  engine applied to \<open>G = cplx_r2 \<circ> af\<close> with GLOBAL regular value (odd \<open>N\<close>:
  \<open>dxA_surj\<close>; at \<open>cvec = 0\<close> the array factor equals \<open>CARD('n) \<noteq> 0\<close>, vacuous).
  Witness bridge: at a null, \<open>HessU = gain \<cdot> (Dcvec\<^sup>T (Hcmat|\<^sub>n\<^sub>u\<^sub>l\<^sub>l) Dcvec)\<close> with
  \<open>Hcmat|\<^sub>n\<^sub>u\<^sub>l\<^sub>l\<close> the first-moment Gram, so
  \<open>det HessU = 4 gain\<^sup>2 (det sliceJac A)\<^sup>2\<close> and degeneracy with \<open>gain \<noteq> 0\<close> forces
  a singular slice Jacobian.\<close>

section \<open>B4: the Hessian at array-factor nulls\<close>

lemma Hcmat_at_null:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  assumes null: "Afun x c = 0"
  shows "Hcmat x c = (\<chi> k. \<chi> l. 2 * Re (cnj (Mcfun x c l) * Mcfun x c k))"
  unfolding Hcmat_def using null by simp

lemma gradUc_at_null:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  assumes null: "M_paper x c $ 1 = 0"
  shows "gradU (\<lambda>c. c) (\<lambda>_. 1) x c = 0"
proof -
  have "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ j = 0" for j
    using gradUc_component_moments[of x c j, unfolded null] by simp
  thus ?thesis by (simp add: Finite_Cartesian_Product.vec_eq_iff)
qed

lemma Uc_at_null:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  assumes null: "M_paper x c $ 1 = 0"
  shows "U_cart (\<lambda>c. c) (\<lambda>_. 1) x c = 0"
  using Uc_eq_moment[of x c, unfolded null] by simp

lemma HessU_at_null:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes null: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
            \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))"
  unfolding HessU_dip_entry_moments
  by (simp add: gradUc_at_null[OF null] Uc_at_null[OF null])

text \<open>The determinant identity at nulls: \<open>det HessU = 4 gain\<^sup>2 (detJ \<cdot> Im(cnj M\<^sub>2 M\<^sub>3))\<^sup>2\<close>,
  where \<open>detJ = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))\<close> and \<open>M\<^sub>2, M\<^sub>3\<close> are the first
  moments.  The slice Jacobian of \<open>cplx_r2 \<circ> af\<close> has determinant
  \<open>detJ \<cdot> Im(cnj M\<^sub>2 M\<^sub>3)\<close>, hence \<open>det HessU = 4 gain\<^sup>2 (det sliceJac)\<^sup>2\<close>.\<close>

lemma det_HessU_at_null:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes nullA: "Afun x (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
  shows "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
       = 4 * (gain_dip \<omega>)\<^sup>2
           * (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
              * Im (cnj (Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 1)
                    * Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 2))\<^sup>2"
proof -
  have AmA: "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) = Afun x (cvec_dip \<omega>0 \<omega>s \<omega>)"
    by (simp add: A_moment_def Afun_def phase_def)
  have nullM: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = 0"
    by (simp add: M_paper_proj_A A_cart_eq_Afun AmA nullA)
  \<comment> \<open>scalarize: gain, the four Jacobian entries, and the moment Gram data\<close>
  define g where "g = gain_dip \<omega>"
  define j11 where "j11 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 1"
  define j21 where "j21 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 2"
  define j12 where "j12 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) $ 1"
  define j22 where "j22 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) $ 2"
  define \<mu>1 where "\<mu>1 = Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 1"
  define \<mu>2 where "\<mu>2 = Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 2"
  define n1 where "n1 = Re (cnj \<mu>1 * \<mu>1)"
  define n2 where "n2 = Re (cnj \<mu>2 * \<mu>2)"
  define r12 where "r12 = Re (cnj \<mu>1 * \<mu>2)"
  define i12 where "i12 = Im (cnj \<mu>1 * \<mu>2)"
  \<comment> \<open>the Gram relation \<open>n1 n2 = r12\<^sup>2 + i12\<^sup>2\<close>\<close>
  have gram: "n1 * n2 = r12\<^sup>2 + i12\<^sup>2"
  proof -
    have "n1 = (cmod \<mu>1)\<^sup>2" unfolding n1_def
      by (metis complex_norm_square mult.commute Re_complex_of_real)
    moreover have "n2 = (cmod \<mu>2)\<^sup>2" unfolding n2_def
      by (metis complex_norm_square mult.commute Re_complex_of_real)
    moreover have "(cmod (cnj \<mu>1 * \<mu>2))\<^sup>2 = r12\<^sup>2 + i12\<^sup>2"
      unfolding r12_def i12_def by (simp add: cmod_power2)
    moreover have "(cmod (cnj \<mu>1 * \<mu>2))\<^sup>2 = (cmod \<mu>1)\<^sup>2 * (cmod \<mu>2)\<^sup>2"
      by (simp add: norm_mult power_mult_distrib)
    ultimately show ?thesis by simp
  qed
  have r21: "Re (cnj \<mu>2 * \<mu>1) = r12"
    unfolding r12_def by simp
  have i21: "Im (cnj \<mu>2 * \<mu>1) = - i12"
    unfolding i12_def by simp
  have ReSym: "\<And>a b::complex. Re (cnj a * b) = Re (cnj b * a)" by simp
  \<comment> \<open>the four Hessian entries at the null, in scalar form\<close>
  have HcN: "Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>)
           = (\<chi> k. \<chi> l. 2 * Re (cnj (Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) l)
                              * Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) k))"
    by (rule Hcmat_at_null[OF nullA])
  have entry: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
      = g * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
           \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))" for k l
    unfolding g_def by (rule HessU_at_null[OF nullM])
  \<comment> \<open>expand the quadratic form entrywise (2-dim inner product and matvec)\<close>
  have qform: "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
        \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
      = 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 1
               * (n1 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1)
                  + r12 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2))
           + Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 2
               * (r12 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1)
                  + n2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2)))" for k l
    unfolding HcN inner_vec_def matrix_vector_mult_def
    using ReSym
    by (simp add: sum_2 n1_def n2_def r12_def \<mu>1_def \<mu>2_def algebra_simps)
  \<comment> \<open>determinant via the 2x2 formula and pure algebra\<close>
  have detJ: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = j11 * j22 - j12 * j21"
    unfolding j11_def j12_def j21_def j22_def
    by (simp add: det_2 matrix_def axis_def)
  have det2: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
      = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
        * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
      - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
        * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
    by (simp add: det_2)
  have detH: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
      = 4 * (g * g) * ((j11 * j22 - j12 * j21) * (j11 * j22 - j12 * j21))
          * (n1 * n2 - r12 * r12)"
    unfolding det2 entry qform
    unfolding j11_def[symmetric] j12_def[symmetric] j21_def[symmetric] j22_def[symmetric]
    by (simp add: algebra_simps)
  have sub: "n1 * n2 - r12 * r12 = i12 * i12"
    using gram by (simp add: power2_eq_square)
  show ?thesis
    unfolding g_def[symmetric] \<mu>1_def[symmetric] \<mu>2_def[symmetric] i12_def[symmetric] detJ
    by (simp add: detH sub power2_eq_square algebra_simps)
qed

section \<open>B1/B2: the array factor as an \<open>\<real>\<^sup>2\<close>-valued jointly-\<open>C\<^sup>1\<close> map\<close>

definition afR2 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (((real^2)^'n) \<times> (real^2)) \<Rightarrow> real^2" where
  "afR2 \<omega>0 \<omega>s p = cplx_r2 (af (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p))"

lemma afR2_joint_C1:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "\<exists>G'::(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2)).
            (\<forall>z. (afR2 \<omega>0 \<omega>s has_derivative blinfun_apply (G' z)) (at z))
          \<and> continuous_on UNIV G'"
  sorry

section \<open>B3: global regular value (odd \<open>N\<close>)\<close>

lemma afR2_regular_value:
  fixes \<omega>0 \<omega>s :: "real^2" and V :: "((real^2)^'n) set"
  assumes oddN: "odd CARD('n)"
  shows "regular_value_on (afR2 \<omega>0 \<omega>s) (V \<times> (UNIV :: (real^2) set)) 0"
  sorry

section \<open>B4': degenerate null forbids a surjective slice derivative\<close>

lemma null_no_surj_slice:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2" and C :: "(real^2) set"
  assumes oC: "open C" and wC: "\<omega> \<in> C"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and null: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0"
    and hess0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
  shows "\<not> (\<exists>D. ((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D) (at \<omega> within C) \<and> surj D)"
  sorry

section \<open>(M6b) assembly\<close>

lemma meager_Azero_degenerate_stratum_scratch:
  fixes V :: "((real^2)^'n) set" and ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and oddN: "odd CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
  sorry

end
