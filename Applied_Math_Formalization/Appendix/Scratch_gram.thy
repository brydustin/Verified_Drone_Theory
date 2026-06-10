theory Scratch_gram
  imports "Applied_Math_Appendix.Nonemptiness_Robust"
begin

thm adjoint_works adjoint_linear linear_injective_0 det_nz_iff_inj

lemma surj_iff_gram_invertible:
  fixes A :: "'a::euclidean_space \<Rightarrow> (real^'m)"
  assumes lin: "linear A"
  shows "surj A \<longleftrightarrow> invertible (matrix (A \<circ> adjoint A))"
proof -
  have linAd: "linear (adjoint A)" by (rule adjoint_linear[OF lin])
  have linG: "linear (A \<circ> adjoint A)" using lin linAd by (subst linear_compose, auto)
  show ?thesis
  proof
    assume surjA: "surj A"
    have inj_adj: "inj (adjoint A)"
      unfolding linear_injective_0[OF linAd]
    proof (intro allI impI)
      fix y assume z: "adjoint A y = 0"
      obtain x where x: "A x = y" using surjA by (metis surjD)
      have "inner y y = inner (A x) y" using x by simp
      also have "\<dots> = inner x (adjoint A y)" by (simp add: adjoint_works[OF lin])
      also have "\<dots> = 0" using z by simp
      finally have "inner y y = 0" .
      thus "y = 0" by simp
    qed
    have inj_G: "inj (A \<circ> adjoint A)"
      unfolding linear_injective_0[OF linG]
    proof (intro allI impI)
      fix y assume z: "(A \<circ> adjoint A) y = 0"
      have "inner ((A \<circ> adjoint A) y) y = inner (adjoint A y) (adjoint A y)"
        by (simp add: o_def adjoint_works[OF lin])
      hence "inner (adjoint A y) (adjoint A y) = 0" using z by simp
      hence "adjoint A y = 0" by simp
      thus "y = 0" using inj_adj linAd by (metis linear_injective_0)
    qed
    thus "invertible (matrix (A \<circ> adjoint A))"
      by (metis det_nz_iff_inj[OF linG] invertible_det_nz)
  next
    assume invG: "invertible (matrix (A \<circ> adjoint A))"
    have "inj (A \<circ> adjoint A)" by (metis invG det_nz_iff_inj[OF linG] invertible_det_nz)
    hence "surj (A \<circ> adjoint A)" using linG by (metis linear_injective_imp_surjective)
    thus "surj A" by (metis comp_apply surjD surjI)
  qed
qed

definition mstarg :: "planar \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

lemma linear_DM_paper_x: "linear (DM_paper_x x c)"
  by (metis has_derivative_M_paper_x has_derivative_bounded_linear bounded_linear.linear)

lemma surj_iff_mstarg: "surj (DM_paper_x x c) \<longleftrightarrow> mstarg c x \<noteq> 0"
proof -
  have lTDF: "linear (transC \<circ> DM_paper_x x c)"
    by (intro linear_compose linear_transC linear_DM_paper_x)
  have seq: "surj (DM_paper_x x c) \<longleftrightarrow> surj (transC \<circ> DM_paper_x x c)"
  proof
    assume "surj (DM_paper_x x c)"
    thus "surj (transC \<circ> DM_paper_x x c)" using surj_transC comp_surj by blast
  next
    assume s: "surj (transC \<circ> DM_paper_x x c)"
    have "surj (transC_inv \<circ> (transC \<circ> DM_paper_x x c))"
      using s surj_transC_inv comp_surj by blast
    moreover have "transC_inv \<circ> (transC \<circ> DM_paper_x x c) = DM_paper_x x c"
      by (rule ext) (simp add: transC_inv_left)
    ultimately show "surj (DM_paper_x x c)" by simp
  qed
  show ?thesis
    unfolding mstarg_def
    using seq surj_iff_gram_invertible[OF lTDF] invertible_det_nz by blast
qed

lemma matrix_gram_entry:
  "vec_nth (vec_nth (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c))) i) j
   = (\<Sum>e\<in>Basis. vec_nth (transC (DM_paper_x x c e)) j * vec_nth (transC (DM_paper_x x c e)) i)"
proof -
  define B where "B = transC \<circ> DM_paper_x x c"
  have lB: "linear B" unfolding B_def by (intro linear_compose linear_transC linear_DM_paper_x)
  have key: "inner (adjoint B (axis k (1::real))) e = vec_nth (B e) k"
    for k :: 12 and e
  proof -
    have "inner (adjoint B (axis k (1::real))) e = inner e (adjoint B (axis k (1::real)))"
      by (rule inner_commute)
    also have "\<dots> = inner (B e) (axis k (1::real))" by (rule adjoint_works[OF lB])
    also have "\<dots> = vec_nth (B e) k" by (simp add: inner_axis)
    finally show ?thesis .
  qed
  have "vec_nth (vec_nth (matrix (B \<circ> adjoint B)) i) j = vec_nth (B (adjoint B (axis j (1::real)))) i"
    by (simp add: matrix_def o_def)
  also have "\<dots> = inner (B (adjoint B (axis j (1::real)))) (axis i (1::real))"
    by (simp add: inner_axis)
  also have "\<dots> = inner (adjoint B (axis j (1::real))) (adjoint B (axis i (1::real)))"
    by (simp add: adjoint_works[OF lB])
  also have "\<dots> = (\<Sum>e\<in>Basis. inner (adjoint B (axis j (1::real))) e * inner (adjoint B (axis i (1::real))) e)"
    by (rule euclidean_inner)
  also have "\<dots> = (\<Sum>e\<in>Basis. vec_nth (B e) j * vec_nth (B e) i)" by (simp add: key)
  finally show ?thesis by (simp add: B_def o_def)
qed

lemma cont_transC_DM_entry:
  "continuous_on UNIV (\<lambda>x. vec_nth (transC (DM_paper_x x c e)) k)"
proof -
  have "continuous_on UNIV (\<lambda>x. DM_paper_x x c e)"
   by (simp add: DM_paper_x_eq_MM continuous_on_DM_paper_x_vec)
  hence "continuous_on UNIV (\<lambda>x. transC (DM_paper_x x c e))"
    by (rule bounded_linear.continuous_on[OF bounded_linear_transC])
  thus ?thesis by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
qed

lemma cont_matrix_G_entry:
  "continuous_on UNIV
     (\<lambda>x. vec_nth (vec_nth (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c))) i) j)"
proof -
  have "continuous_on UNIV
          (\<lambda>x. \<Sum>e\<in>Basis. vec_nth (transC (DM_paper_x x c e)) j * vec_nth (transC (DM_paper_x x c e)) i)"
    by (intro continuous_on_sum continuous_on_mult cont_transC_DM_entry)
  thus ?thesis by (simp add: matrix_gram_entry)
qed

lemma cont_mstarg: "continuous_on UNIV (\<lambda>x. mstarg c x)"
  unfolding mstarg_def by (rule continuous_on_det_fun) (rule cont_matrix_G_entry)

lemma bl_neg_inner_gen: "bounded_linear (\<lambda>x::(real^2)^'n. - (c \<bullet> (x $ n)))"
  by (intro bounded_linear_minus bounded_linear_compose[OF bounded_linear_inner_right bounded_linear_vec_nth])

lemma cline_entire_phase_gen: "cline_entire (\<lambda>x::(real^2)^'n. phase c x n)"
  unfolding phase_def by (rule cline_entire_cis_linear[OF bl_neg_inner_gen])

lemma cline_entire_dphase_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_phase c x h n)"
proof -
  have "cline_entire (\<lambda>x::(real^2)^'n.
          complex_of_real (- (c \<bullet> (h $ n))) * (\<i> * cis (- (c \<bullet> (x $ n)))))"
    by (intro cline_entire_mult cline_entire_const cline_entire_cis_linear[OF bl_neg_inner_gen])
  thus ?thesis unfolding d_phase_def by (simp add: scaleR_conv_of_real)
qed

lemmas moment_cline_intros_gen =
  cline_entire_sum cline_entire_add cline_entire_mult cline_entire_const
  cline_entire_phase_gen cline_entire_dphase_gen cline_entire_of_real_rline
  rline_entire_coord rline_entire_const rline_entire_add rline_entire_mult rline_entire_scale

lemma cline_entire_dA_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_A_moment_x x c h)"
  unfolding d_A_moment_x_def by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM1_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M1_moment_x x c h)"
  unfolding d_M1_moment_x_def by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM2_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M2_moment_x x c h)"
  unfolding d_M2_moment_x_def by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM11_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M11_moment_x x c h)"
  unfolding d_M11_moment_x_def power2_eq_square by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM12_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M12_moment_x x c h)"
  unfolding d_M12_moment_x_def w_M12_def dw_M12_def by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM22_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M22_moment_x x c h)"
  unfolding d_M22_moment_x_def power2_eq_square by (intro moment_cline_intros_gen) simp

lemma cline_entire_DM_comp_gen: "cline_entire (\<lambda>x::(real^2)^'n. DM_paper_x x c h $ m)"
proof -
  from exhaust_6[of m] consider (m1) "m=(1::6)" | (m2) "m=(2::6)" | (m3) "m=(3::6)"
    | (m4) "m=(4::6)" | (m5) "m=(5::6)" | (m6) "m=(6::6)" by blast
  then show ?thesis
  proof cases
    case m1 then show ?thesis
      by (metis (no_types, lifting) ext DA_paper_x_def DM_paper_x_components(1) cline_entire_dA_gen d_A_moment_x_def)
  next
    case m2 then show ?thesis
      by (metis (no_types, lifting) ext DM1_paper_x_def DM_paper_x_components(2) cline_entire_dM1_gen d_M1_moment_x_def)
  next
    case m3 then show ?thesis
      by (metis (no_types, lifting) ext DM2_paper_x_def DM_paper_x_components(3) cline_entire_dM2_gen d_M2_moment_x_def)
  next
    case m4 then show ?thesis
      by (metis (no_types, lifting) ext DM11_paper_x_def DM_paper_x_components(4) cline_entire_dM11_gen d_M11_moment_x_def)
  next
    case m5 then show ?thesis
      by (metis (no_types, lifting) DM12_paper_x_def DM_paper_x_components(5) cline_entire_dM12_gen cline_entire_def d_M12_moment_x_def)
  next
    case m6 then show ?thesis
      by (metis (no_types, lifting) ext DM22_paper_x_def DM_paper_x_components(6) cline_entire_dM22_gen d_M22_moment_x_def)
  qed
qed

lemma rline_entire_transC_comp_gen:
  fixes w :: "(real^2)^'n \<Rightarrow> complex^6" and i :: 12
  assumes "\<And>m. cline_entire (\<lambda>x. w x $ m)"
  shows "rline_entire (\<lambda>x. vec_nth (transC (w x)) i)"
  using exhaust_12[of i]
  by (elim disjE)
     (simp_all add: transC_def rline_entire_Re[OF assms] rline_entire_Im[OF assms])

lemma rline_entire_transC_DM:
  "rline_entire (\<lambda>x::(real^2)^'n. vec_nth (transC (DM_paper_x x c e)) k)"
  by (rule rline_entire_transC_comp_gen[OF cline_entire_DM_comp_gen])

lemma rline_entire_matrix_G_entry:
  "rline_entire
     (\<lambda>x::(real^2)^'n. vec_nth (vec_nth (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c))) i) j)"
proof -
  have "rline_entire
          (\<lambda>x::(real^2)^'n. \<Sum>e\<in>Basis. vec_nth (transC (DM_paper_x x c e)) j * vec_nth (transC (DM_paper_x x c e)) i)"
    by (auto intro!: rline_entire_sum rline_entire_mult rline_entire_transC_DM)
  thus ?thesis by (simp add: matrix_gram_entry)
qed

lemma rline_entire_mstarg: "rline_entire (\<lambda>x::(real^2)^'n. mstarg c x)"
  unfolding mstarg_def by (rule rline_entire_det_fun) (rule rline_entire_matrix_G_entry)

lemma DM_paper_x_regular_point_exists:
  fixes c :: planar
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x0::(real^2)^'n. surj (DM_paper_x x0 c)" sorry

lemma mstarg_nonzero:
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x::(real^2)^'n. mstarg c x \<noteq> 0"
proof -
  obtain x0 :: "(real^2)^'n" where "surj (DM_paper_x x0 c)"
    using DM_paper_x_regular_point_exists[OF assms] by blast
  thus ?thesis using surj_iff_mstarg by blast
qed

lemma nowhere_dense_mstarg_zeros:
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. mstarg c x = 0}"
proof -
  have lines: "\<exists>F. F holomorphic_on UNIV
                  \<and> (\<forall>t. F (complex_of_real t) = complex_of_real (mstarg c (a + t *\<^sub>R v)))" for a v
    using rline_entire_mstarg unfolding rline_entire_def by blast
  have "nowhere_dense {x::(real^2)^'n \<in> UNIV. mstarg c x = 0}"
    by (rule lines_entire_slice_nowhere_dense[OF cont_mstarg lines]) (use mstarg_nonzero[OF c0 n6] in blast)
  thus ?thesis by simp
qed

lemma DM_paper_x_open_dense_surjective_gen_sound:
  fixes V :: "((real^2)^'n) set" and c :: planar
  assumes V: "open V" and c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "\<exists>U. open U \<and> U \<subseteq> V \<and> V \<subseteq> closure U \<and> (\<forall>x\<in>U. surj (DM_paper_x x c))"
proof (intro exI[of _ "V \<inter> {x::(real^2)^'n. mstarg c x \<noteq> 0}"] conjI)
  show "open (V \<inter> {x. mstarg c x \<noteq> 0})"
    using V open_Collect_neq[OF cont_mstarg continuous_on_const] by blast
  show "V \<inter> {x. mstarg c x \<noteq> 0} \<subseteq> V" by blast
  have cl0: "closed {x::(real^2)^'n. mstarg c x = 0}"
    by (rule closed_Collect_eq[OF cont_mstarg continuous_on_const])
  have int0: "interior {x::(real^2)^'n. mstarg c x = 0} = {}"
    using nowhere_dense_mstarg_zeros[OF c0 n6] cl0 by (simp only: nowhere_dense_def closure_closed)
  have dense: "closure {x::(real^2)^'n. mstarg c x \<noteq> 0} = UNIV"
    by (simp add: Collect_neg_eq closure_complement int0)
  show "V \<subseteq> closure (V \<inter> {x. mstarg c x \<noteq> 0})"
    using open_Int_closure_subset[OF V, of "{x. mstarg c x \<noteq> 0}"] dense by simp
  show "\<forall>x\<in>V \<inter> {x. mstarg c x \<noteq> 0}. surj (DM_paper_x x c)"
    by (auto simp: surj_iff_mstarg)
qed

end
