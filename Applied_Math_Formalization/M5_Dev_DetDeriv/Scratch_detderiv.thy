theory Scratch_detderiv
  imports "HOL-Analysis.Analysis"
begin

text \<open>\<^bold>\<open>Reusable helper toward \<open>has_derivative_mstarg_joint_C1\<close>.\<close>  The Frechet
  derivative of a determinant of a matrix whose entries are differentiable
  functions, given as the explicit Leibniz/Jacobi form (so downstream continuity
  of the derivative is checkable).  No \<open>has_derivative\<close>+\<open>det\<close> lemma exists in
  HOL-Analysis or the AFP; this mirrors the proven \<open>continuous_on_det_fun\<close> /
  \<open>rline_entire_det_fun\<close> (unfold \<open>det_def\<close>, then \<open>has_derivative_sum\<close>/\<open>_prod\<close>).\<close>

lemma has_derivative_det_fun:
  fixes A :: "'a::real_normed_vector \<Rightarrow> (real^'m^'m)"
    and A' :: "'a \<Rightarrow> (real^'m^'m)"
  assumes ent: "\<And>i j. ((\<lambda>x. A x $ i $ j) has_derivative (\<lambda>h. A' h $ i $ j)) (at s within S)"
  shows "((\<lambda>x. det (A x)) has_derivative
            (\<lambda>h. \<Sum>p\<in>{p. p permutes (UNIV::'m set)}. of_int (sign p) *
                  (\<Sum>i\<in>UNIV. (A' h $ i $ p i) * (\<Prod>j\<in>(UNIV-{i}). A s $ j $ p j)))) (at s within S)"
  unfolding det_def
proof (rule has_derivative_sum)
  fix p :: "'m \<Rightarrow> 'm" assume "p \<in> {p. p permutes UNIV}"
  have pr: "((\<lambda>x. \<Prod>i\<in>UNIV. A x $ i $ p i) has_derivative
              (\<lambda>h. \<Sum>i\<in>UNIV. (A' h $ i $ p i) * (\<Prod>j\<in>(UNIV-{i}). A s $ j $ p j))) (at s within S)"
    by (rule has_derivative_prod) (rule ent)
  show "((\<lambda>x. of_int (sign p) * (\<Prod>i\<in>UNIV. A x $ i $ p i)) has_derivative
          (\<lambda>h. of_int (sign p) *
                (\<Sum>i\<in>UNIV. (A' h $ i $ p i) * (\<Prod>j\<in>(UNIV-{i}). A s $ j $ p j)))) (at s within S)"
    using has_derivative_mult[OF has_derivative_const pr] by simp
qed

end
