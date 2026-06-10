theory Scratch_chk
  imports "Applied_Math_Appendix.Nonemptiness_Robust"
begin

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

end
