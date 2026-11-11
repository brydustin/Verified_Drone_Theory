section \<open>The moments of a configuration and their derivatives\<close>

theory Moment_Map
  imports
    Array_Factor
begin

subsection \<open>Phases and moments\<close>

definition phase :: "planar \<Rightarrow> (planar^'n) \<Rightarrow> 'n \<Rightarrow> complex"
  where "phase c y n = cis (-(c \<bullet> (y $ n)))"

definition d_phase :: "planar \<Rightarrow> (planar^'n) \<Rightarrow> (planar^'n) \<Rightarrow> 'n \<Rightarrow> complex"
  where "d_phase c x h n = -(c \<bullet> (h $ n)) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n))))"

definition A_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "A_moment x c = (\<Sum>n\<in>UNIV. phase c x n)"

definition first_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> 2 \<Rightarrow> complex"
  where "first_moment x c k = (\<Sum>n\<in>UNIV. of_real ((x $ n) $ k) * phase c x n)"

definition second_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> 2 \<Rightarrow> 2 \<Rightarrow> complex"
  where "second_moment x c k l = (\<Sum>n\<in>UNIV. of_real ((x $ n) $ k * (x $ n) $ l) * phase c x n)"

definition moment_map :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex^3"
  where "moment_map x c = vector [A_moment x c, first_moment x c 1, first_moment x c 2]"

lemma moment_map_components [simp]:
  shows "moment_map x c $ 1 = A_moment x c"
    and "moment_map x c $ 2 = first_moment x c 1"
    and "moment_map x c $ 3 = first_moment x c 2"
  unfolding moment_map_def
  by ((simp add: vector_def)+)

lemma A_moment_cis: "A_moment x c = (\<Sum>n\<in>UNIV. cis (-(c \<bullet> (x$n))))"
  by (simp add: A_moment_def phase_def)

lemma first_moment_cis:
  "first_moment x c k = (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * cis (-(c \<bullet> (x$n))))"
  by (simp add: first_moment_def phase_def)

lemma second_moment_cis:
  "second_moment x c k l
     = (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * complex_of_real ((x$n)$l) * cis (-(c \<bullet> (x$n))))"
  by (simp add: second_moment_def phase_def mult.assoc)

subsection \<open>Derivatives in the configuration\<close>

lemma has_derivative_inner_const_nth_x:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. c \<bullet> (y $ n)) has_derivative (\<lambda>h. c \<bullet> (h $ n)))
         (at x within V)"
proof -
  have lin: "linear (\<lambda>y :: planar^'n. c \<bullet> (y $ n))"
    by (intro linearI) (simp_all add: inner_right_distrib)
  show ?thesis using linear_imp_has_derivative[OF lin] .
qed

lemma has_derivative_cis_neg_inner_x:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. cis (-(c \<bullet> (y $ n)))) has_derivative
            (\<lambda>h. (-(c \<bullet> (h $ n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n))))))
         (at x within V)"
proof -
  have neg_inner_deriv:
    "((\<lambda>y :: planar^'n. -(c \<bullet> (y $ n))) has_derivative (\<lambda>h. -(c \<bullet> (h $ n))))
         (at x within V)"
    using has_derivative_inner_const_nth_x[where c = c and n = n and x = x and V = V]
    by (rule has_derivative_minus)
  have cis_deriv:
    "(cis has_derivative (\<lambda>r. r *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n))))))
         (at (-(c \<bullet> (x $ n))))"
    by (auto intro!: derivative_eq_intros)
  show ?thesis
    using has_derivative_compose[OF neg_inner_deriv cis_deriv] by (simp add: o_def)
qed

lemma has_derivative_nth_k_x:
  fixes n :: "'n::finite" and k :: 2
  shows "((\<lambda>y :: planar^'n. (y $ n) $ k) has_derivative (\<lambda>h. (h $ n) $ k))
         (at x within V)"
proof -
  have lin: "linear (\<lambda>y :: planar^'n. (y $ n) $ k)"
    by (intro linearI) simp_all
  show ?thesis using linear_imp_has_derivative[OF lin] .
qed

lemma has_derivative_of_real_lift:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "(f has_derivative f') (at x within V)"
  shows "((\<lambda>y. of_real (f y) :: complex) has_derivative (\<lambda>h. of_real (f' h)))
         (at x within V)"
proof -
  have lin: "linear (of_real :: real \<Rightarrow> complex)"
    by (intro linearI) (simp_all add: scaleR_conv_of_real)
  have outer: "(of_real has_derivative (of_real :: real \<Rightarrow> complex))
                  (at (f x) within f ` V)"
    using linear_imp_has_derivative[OF lin] .
  show ?thesis
    using has_derivative_in_compose[OF assms outer] by (simp add: o_def)
qed

lemma has_derivative_phase_x:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. phase c y n) has_derivative (\<lambda>h. d_phase c x h n))
         (at x within V)"
  unfolding phase_def d_phase_def
  by (rule has_derivative_cis_neg_inner_x)

lemma has_derivative_first_moment_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real ((y $ n) $ k) * phase c y n)
            has_derivative
            (\<lambda>h. of_real ((h $ n) $ k) * phase c x n
               + of_real ((x $ n) $ k) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ k) :: complex) has_derivative
      (\<lambda>h. of_real ((h $ n) $ k))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_x])
  have prod:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ k) * phase c y n)
       has_derivative
       (\<lambda>h. of_real ((x $ n) $ k) * d_phase c x h n
          + of_real ((h $ n) $ k) * phase c x n))
     (at x within V)"
    using d_real has_derivative_phase_x
    by (rule has_derivative_mult)
  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

definition DA_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n \<Rightarrow> complex)"
  where "DA_moment x c = (\<lambda>h. \<Sum>i\<in>UNIV. d_phase c x h i)"

definition Dfirst_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> 2 \<Rightarrow> (planar^'n \<Rightarrow> complex)"
  where
  "Dfirst_moment x c k =
     (\<lambda>h. \<Sum>i\<in>UNIV. of_real ((h $ i) $ k) * phase c x i + of_real ((x $ i) $ k) * d_phase c x h i)"

lemma has_derivative_A_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. A_moment y c) has_derivative (\<lambda>h. DA_moment x c h))
         (at x within V)"
  unfolding A_moment_def DA_moment_def
  by (rule has_derivative_sum) (use has_derivative_phase_x in blast)

lemma has_derivative_first_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. first_moment y c k) has_derivative (\<lambda>h. Dfirst_moment x c k h))
         (at x within V)"
  unfolding first_moment_def Dfirst_moment_def
  by (rule has_derivative_sum) (use has_derivative_first_moment_term in blast)

definition Dmoment_map :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> ((planar^'n) \<Rightarrow> complex^3)"
  where
  "Dmoment_map x c =
     (\<lambda>h. vector [DA_moment x c h, Dfirst_moment x c 1 h, Dfirst_moment x c 2 h])"

lemma Dmoment_map_components:
  shows "Dmoment_map x c h $ 1 = DA_moment x c h"
    and "Dmoment_map x c h $ 2 = Dfirst_moment x c 1 h"
    and "Dmoment_map x c h $ 3 = Dfirst_moment x c 2 h"
  unfolding Dmoment_map_def
  by ((simp add: vector_def)+)

lemma has_derivative_moment_map:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. moment_map y c) has_derivative Dmoment_map x c) (at x within V)"
proof -
  have comps:
    "\<forall>k :: 3. ((\<lambda>y. moment_map y c $ k) has_derivative (\<lambda>h. Dmoment_map x c h $ k))
              (at x within V)"
  proof (intro allI)
    fix k :: 3
    consider "k = 1" | "k = 2" | "k = 3"
      using exhaust_3 by metis
    thus "((\<lambda>y. moment_map y c $ k) has_derivative (\<lambda>h. Dmoment_map x c h $ k))
            (at x within V)"
    proof cases
      case 1 thus ?thesis
        using has_derivative_A_moment_x[where c=c and x=x and V=V]
        by (simp add: Dmoment_map_components)
    next
      case 2 thus ?thesis
        using has_derivative_first_moment_x[where c=c and x=x and V=V and k=1]
        by (simp add: Dmoment_map_components)
    next
      case 3 thus ?thesis
        using has_derivative_first_moment_x[where c=c and x=x and V=V and k=2]
        by (simp add: Dmoment_map_components)
    qed
  qed
  have vec_der:
    "((\<lambda>y. \<chi> k. moment_map y c $ k) has_derivative (\<lambda>h. \<chi> k. Dmoment_map x c h $ k))
     (at x within V)"
  proof (subst has_derivative_componentwise_within, intro ballI)
    fix b :: "complex^3" assume bB: "b \<in> Basis"
    from bB obtain k :: 3 and e :: complex
      where b_eq: "b = axis k e" and e_basis: "e \<in> Basis"
      unfolding Basis_vec_def by auto
    have indiv:
      "((\<lambda>y. moment_map y c $ k) has_derivative (\<lambda>h. Dmoment_map x c h $ k))
       (at x within V)"
      using comps by blast
    have inner_d:
      "((\<lambda>z :: complex. z \<bullet> e) has_derivative (\<lambda>z. z \<bullet> e))
         (at (moment_map x c $ k) within (\<lambda>y. moment_map y c $ k) ` V)"
      using bounded_linear_inner_left[of e] has_derivative_ident
      by (rule bounded_linear.has_derivative)       
    have d_compose:
      "((\<lambda>y. (moment_map y c $ k) \<bullet> e) has_derivative
          (\<lambda>h. (Dmoment_map x c h $ k) \<bullet> e))
       (at x within V)"
      using has_derivative_in_compose[OF indiv inner_d]
      by (simp add: o_def)
    show "((\<lambda>y. (\<chi> k. moment_map y c $ k) \<bullet> b) has_derivative
           (\<lambda>y. (\<chi> k. Dmoment_map x c y $ k) \<bullet> b))
          (at x within V)"
      using d_compose by (simp add: b_eq inner_axis)
  qed

  have lhs: "(\<lambda>y. \<chi> k. moment_map y c $ k) = (\<lambda>y. moment_map y c)"
    by (simp add: fun_eq_iff vec_eq_iff)
  have rhs: "(\<lambda>h. \<chi> k. Dmoment_map x c h $ k) = Dmoment_map x c"
    by (simp add: fun_eq_iff vec_eq_iff)

  show ?thesis
    using vec_der by (simp only: lhs rhs)
qed

end
