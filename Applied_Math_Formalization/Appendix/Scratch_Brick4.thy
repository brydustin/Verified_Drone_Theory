theory Scratch_Brick4
  imports Nonemptiness_Robust2
begin

text \<open>Scratch brick 4 foundation: the 6x6 transport matrix, its action, the bridge.\<close>

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
    [ w $ 1,
      of_real a * w $ 2 + of_real b * w $ 3,
      of_real p * w $ 2 + of_real q * w $ 3,
      of_real (a\<^sup>2) * w $ 4 + of_real (2 * a * b) * w $ 5 + of_real
(b\<^sup>2) * w $ 6,
      of_real (a * p) * w $ 4 + of_real (a * q + b * p) * w $ 5 + of_real (b *
q) * w $ 6,
      of_real (p\<^sup>2) * w $ 4 + of_real (2 * p * q) * w $ 5 + of_real
(q\<^sup>2) * w $ 6 ]"
  unfolding Finite_Cartesian_Product.vec_eq_iff
proof (intro allI)
  fix i :: 6
  show "(Lmat a b p q *v w) $ i =
    vector
    [ w $ 1,
      of_real a * w $ 2 + of_real b * w $ 3,
      of_real p * w $ 2 + of_real q * w $ 3,
      of_real (a\<^sup>2) * w $ 4 + of_real (2 * a * b) * w $ 5 + of_real
(b\<^sup>2) * w $ 6,
      of_real (a * p) * w $ 4 + of_real (a * q + b * p) * w $ 5 + of_real (b *
q) * w $ 6,
      of_real (p\<^sup>2) * w $ 4 + of_real (2 * p * q) * w $ 5 + of_real
(q\<^sup>2) * w $ 6 ] $ i"
    using exhaust_6[of i]
    by (elim disjE; simp add: Lmat_def matrix_vector_mult_def sum_6)
qed

lemma M_paper_transport:
  fixes T :: "real^2^2"
  assumes Tc: "transpose T *v c = c0_paper"
  shows "M_paper (applyT T y) c
       = Lmat (T $ 1 $ 1) (T $ 1 $ 2) (T $ 2 $ 1) (T $ 2 $ 2) *v M_paper y c0_paper"
  by (simp add: M_paper_applyT[OF Tc] Lmat_apply)

end
