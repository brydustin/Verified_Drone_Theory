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
  assumes null: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = 0"
  shows "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
       = 4 * (gain_dip \<omega>)\<^sup>2
           * (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
              * Im (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
                    * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3)))\<^sup>2"
  sorry

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
