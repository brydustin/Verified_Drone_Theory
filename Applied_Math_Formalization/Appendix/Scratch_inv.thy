theory Scratch_inv
  imports "Applied_Math_Appendix.Nonemptiness_Robust"
begin

lemma UNIV_3: "(UNIV::3 set) = {1,2,3}" using exhaust_3 by auto
lemma sum_3: "sum f (UNIV::3 set) = f 1 + f 2 + f 3" unfolding UNIV_3 by (simp add: ac_simps)

definition Smat_c :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex^3^3" where
  "Smat_c a b p q = vector
    [ vector [of_real (a\<^sup>2),   of_real (2 * a * b),     of_real (b\<^sup>2)],
      vector [of_real (a * p), of_real (a * q + b * p), of_real (b * q)],
      vector [of_real (p\<^sup>2),   of_real (2 * p * q),     of_real (q\<^sup>2)] ]"

lemma invertible_Smat_c:
  assumes "a * q - b * p \<noteq> 0" shows "invertible (Smat_c a b p q)" sorry

definition Lmat :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex^6^6" where
  "Lmat a b p q = vector
    [ vector [1, 0, 0, 0, 0, 0],
      vector [0, of_real a, of_real b, 0, 0, 0],
      vector [0, of_real p, of_real q, 0, 0, 0],
      vector [0, 0, 0, of_real (a\<^sup>2),  of_real (2 * a * b),     of_real (b\<^sup>2)],
      vector [0, 0, 0, of_real (a * p), of_real (a * q + b * p), of_real (b * q)],
      vector [0, 0, 0, of_real (p\<^sup>2),  of_real (2 * p * q),     of_real (q\<^sup>2)] ]"

lemma Lmat_apply:
  "Lmat a b p q *v w = vector
    [ w $ 1, of_real a * w $ 2 + of_real b * w $ 3, of_real p * w $ 2 + of_real q * w $ 3,
      of_real (a\<^sup>2) * w $ 4 + of_real (2 * a * b) * w $ 5 + of_real (b\<^sup>2) * w $ 6,
      of_real (a * p) * w $ 4 + of_real (a * q + b * p) * w $ 5 + of_real (b * q) * w $ 6,
      of_real (p\<^sup>2) * w $ 4 + of_real (2 * p * q) * w $ 5 + of_real (q\<^sup>2) * w $ 6 ]"
  unfolding Finite_Cartesian_Product.vec_eq_iff
proof (intro allI)
  fix i :: 6
  show "(Lmat a b p q *v w) $ i = vector
    [ w $ 1, of_real a * w $ 2 + of_real b * w $ 3, of_real p * w $ 2 + of_real q * w $ 3,
      of_real (a\<^sup>2) * w $ 4 + of_real (2 * a * b) * w $ 5 + of_real (b\<^sup>2) * w $ 6,
      of_real (a * p) * w $ 4 + of_real (a * q + b * p) * w $ 5 + of_real (b * q) * w $ 6,
      of_real (p\<^sup>2) * w $ 4 + of_real (2 * p * q) * w $ 5 + of_real (q\<^sup>2) * w $ 6 ] $ i"
    using exhaust_6[of i] by (elim disjE; simp add: Lmat_def matrix_vector_mult_def sum_6)
qed

lemma surj_Lmat:
  assumes ne: "a * q - b * p \<noteq> 0"
  shows "surj ((*v) (Lmat a b p q))"
proof -
  have lin: "linear ((*v) (Lmat a b p q))" by (rule matrix_vector_mul_linear)
  have rne: "(of_real (a * q - b * p) :: complex) \<noteq> 0" using ne by fastforce
  have ker: "w = 0" if Z: "Lmat a b p q *v w = 0" for w :: "complex^6"
  proof -
    have V: "vector
      [ w $ 1, of_real a * w $ 2 + of_real b * w $ 3, of_real p * w $ 2 + of_real q * w $ 3,
        of_real (a\<^sup>2) * w $ 4 + of_real (2*a*b) * w $ 5 + of_real (b\<^sup>2) * w $ 6,
        of_real (a*p) * w $ 4 + of_real (a*q+b*p) * w $ 5 + of_real (b*q) * w $ 6,
        of_real (p\<^sup>2) * w $ 4 + of_real (2*p*q) * w $ 5 + of_real (q\<^sup>2) * w $ 6 ] = (0::complex^6)"
      using Z by (simp add: Lmat_apply)
    have e1: "w $ 1 = 0" using arg_cong[where f="\<lambda>v. v $ (1::6)", OF V] by simp
    have e2: "of_real a * w $ 2 + of_real b * w $ 3 = 0" using arg_cong[where f="\<lambda>v. v $ (2::6)", OF V] by simp
    have e3: "of_real p * w $ 2 + of_real q * w $ 3 = 0" using arg_cong[where f="\<lambda>v. v $ (3::6)", OF V] by simp
    have e4: "of_real (a\<^sup>2) * w $ 4 + of_real (2*a*b) * w $ 5 + of_real (b\<^sup>2) * w $ 6 = 0" using arg_cong[where f="\<lambda>v. v $ (4::6)", OF V] by simp
    have e5: "of_real (a*p) * w $ 4 + of_real (a*q+b*p) * w $ 5 + of_real (b*q) * w $ 6 = 0" using arg_cong[where f="\<lambda>v. v $ (5::6)", OF V] by simp
    have e6: "of_real (p\<^sup>2) * w $ 4 + of_real (2*p*q) * w $ 5 + of_real (q\<^sup>2) * w $ 6 = 0" using arg_cong[where f="\<lambda>v. v $ (6::6)", OF V] by simp
    have w2: "w $ 2 = 0"
    proof -
      have "of_real (a*q-b*p) * w $ 2 = of_real q * (of_real a * w $ 2 + of_real b * w $ 3) - of_real b * (of_real p * w $ 2 + of_real q * w $ 3)"
        by (simp add: of_real_diff of_real_mult algebra_simps)
      also have "... = 0" using e2 e3 by simp
      finally show ?thesis using rne by simp
    qed
    have w3: "w $ 3 = 0"
    proof -
      have "of_real (a*q-b*p) * w $ 3 = of_real a * (of_real p * w $ 2 + of_real q * w $ 3) - of_real p * (of_real a * w $ 2 + of_real b * w $ 3)"
        by (simp add: of_real_diff of_real_mult algebra_simps)
      also have "... = 0" using e2 e3 by simp
      finally show ?thesis using rne by simp
    qed
    have Sz: "Smat_c a b p q *v (vector [w$4, w$5, w$6] :: complex^3) = 0"
      unfolding Finite_Cartesian_Product.vec_eq_iff
    proof (intro allI)
      fix i :: 3
      show "(Smat_c a b p q *v (vector [w$4, w$5, w$6])) $ i = (0::complex^3) $ i"
        using exhaust_3[of i] e4 e5 e6
        by (elim disjE; simp add: Smat_c_def matrix_vector_mult_def sum_3 algebra_simps)
    qed
    have z3: "(vector [w$4, w$5, w$6] :: complex^3) = 0"
    proof -
      obtain B :: "complex^3^3" where B: "B ** Smat_c a b p q = mat 1"
        using invertible_Smat_c[OF ne] unfolding invertible_def by blast
      have "(vector [w$4, w$5, w$6] :: complex^3) = (B ** Smat_c a b p q) *v vector [w$4, w$5, w$6]"
        by (simp add: B matrix_vector_mul_lid)
      also have "... = B *v (Smat_c a b p q *v vector [w$4, w$5, w$6])"
        by (simp add: matrix_vector_mul_assoc[symmetric])
      also have "... = B *v 0" using Sz by simp
      also have "... = 0" by (simp add: matrix_vector_mult_0)
      finally show ?thesis .
    qed
    have w4: "w$4 = 0" using arg_cong[where f="\<lambda>v. v $ (1::3)", OF z3] by simp
    have w5: "w$5 = 0" using arg_cong[where f="\<lambda>v. v $ (2::3)", OF z3] by simp
    have w6: "w$6 = 0" using arg_cong[where f="\<lambda>v. v $ (3::3)", OF z3] by simp
    show "w = 0" using e1 w2 w3 w4 w5 w6 by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_6)
  qed
  have inj: "inj ((*v) (Lmat a b p q))" using lin ker by (simp add: linear_injective_0)
  show ?thesis using lin inj by (metis linear_injective_imp_surjective)
qed
end
