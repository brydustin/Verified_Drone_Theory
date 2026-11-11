section \<open>The moments of a configuration and their derivatives\<close>

theory Moment_Map
  imports
    Array_Factor
begin

lemma exhaust_6:
  fixes x :: 6
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5 \<or> x = 6"
proof (induct x)
  case (of_int z)
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4 \<or> z = 5" by fastforce
  then show ?case by auto
qed

subsection \<open>Phases and moments\<close>

definition phase :: "planar \<Rightarrow> (planar^'n) \<Rightarrow> 'n \<Rightarrow> complex"
  where "phase c y n = cis (-(c \<bullet> (y $ n)))"

definition d_phase :: "planar \<Rightarrow> (planar^'n) \<Rightarrow> (planar^'n) \<Rightarrow> 'n \<Rightarrow> complex"
  where "d_phase c x h n = -(c \<bullet> (h $ n)) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n))))"

definition w_M12 :: "planar \<Rightarrow> real"
  where "w_M12 p = (p $ 1) * (p $ 2)"

definition dw_M12 :: "planar \<Rightarrow> planar \<Rightarrow> real"
  where "dw_M12 p dp = (dp $ 1) * (p $ 2) + (p $ 1) * (dp $ 2)"

definition A_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "A_moment x c = (\<Sum>n\<in>UNIV. phase c x n)"

definition M1_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M1_moment x c = (\<Sum>n\<in>UNIV. of_real ((x $ n) $ 1) * phase c x n)"

definition M2_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M2_moment x c = (\<Sum>n\<in>UNIV. of_real ((x $ n) $ 2) * phase c x n)"

definition M11_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M11_moment x c = (\<Sum>n\<in>UNIV. of_real (((x $ n) $ 1)\<^sup>2) * phase c x n)"

definition M12_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M12_moment x c = (\<Sum>n\<in>UNIV. of_real (w_M12 (x $ n)) * phase c x n)"

definition M22_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M22_moment x c = (\<Sum>n\<in>UNIV. of_real (((x $ n) $ 2)\<^sup>2) * phase c x n)"

definition moment_map :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex^6"
  where
  "moment_map x c = vector
    [ A_moment   x c,
      M1_moment  x c,
      M2_moment  x c,
      M11_moment x c,
      M12_moment x c,
      M22_moment x c ]"

lemma moment_map_components [simp]:
  shows "moment_map x c $ 1 = A_moment   x c"
    and "moment_map x c $ 2 = M1_moment  x c"
    and "moment_map x c $ 3 = M2_moment  x c"
    and "moment_map x c $ 4 = M11_moment x c"
    and "moment_map x c $ 5 = M12_moment x c"
    and "moment_map x c $ 6 = M22_moment x c"
  unfolding moment_map_def
  by ((simp add: vector_def)+)

lemma A_moment_cis: "A_moment x c = (\<Sum>n\<in>UNIV. cis (-(c \<bullet> (x$n))))"
  by (simp add: A_moment_def phase_def)

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

lemma has_derivative_A_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. phase c y n) has_derivative (\<lambda>h. d_phase c x h n))
         (at x within V)"
  by (rule has_derivative_phase_x)

lemma has_derivative_nth_k_sq_x:
  fixes x :: "planar^'n"
    and V :: "(planar^'n) set"
    and n :: "'n::finite"
    and k :: 2
  shows "((\<lambda>y :: planar^'n. ((y $ n) $ k)\<^sup>2)
            has_derivative
            (\<lambda>h. 2 * ((x $ n) $ k) * ((h $ n) $ k)))
         (at x within V)"
proof -
  have d_nth:
    "((\<lambda>y :: planar^'n. (y $ n) $ k)
        has_derivative
        (\<lambda>h. (h $ n) $ k))
     (at x within V)"
    by (rule has_derivative_nth_k_x)

  have d_prod:
    "((\<lambda>y :: planar^'n. ((y $ n) $ k) * ((y $ n) $ k))
        has_derivative
        (\<lambda>h. ((x $ n) $ k) * ((h $ n) $ k)
           + ((h $ n) $ k) * ((x $ n) $ k)))
     (at x within V)"
    using d_nth d_nth
    by (rule has_derivative_mult)

  then show ?thesis
    by (simp add: power2_eq_square algebra_simps)
qed

lemma has_derivative_M1_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 1) * phase c y n)
            has_derivative
            (\<lambda>h. of_real ((h $ n) $ 1) * phase c x n
               + of_real ((x $ n) $ 1) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 1) :: complex) has_derivative
      (\<lambda>h. of_real ((h $ n) $ 1))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_x])

  have d_phase:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
      (\<lambda>h. d_phase c x h n)) (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 1) * phase c y n)
       has_derivative
       (\<lambda>h. of_real ((x $ n) $ 1) * d_phase c x h n
          + of_real ((h $ n) $ 1) * phase c x n))
     (at x within V)"
    using d_real d_phase
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

lemma has_derivative_M2_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 2) * phase c y n)
            has_derivative
            (\<lambda>h. of_real ((h $ n) $ 2) * phase c x n
               + of_real ((x $ n) $ 2) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 2) :: complex) has_derivative
      (\<lambda>h. of_real ((h $ n) $ 2))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_x])

  have dph:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
      (\<lambda>h. d_phase c x h n)) (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 2) * phase c y n)
       has_derivative
       (\<lambda>h. of_real ((x $ n) $ 2) * d_phase c x h n
          + of_real ((h $ n) $ 2) * phase c x n))
     (at x within V)"
    using d_real dph
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

lemma has_derivative_M11_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 1)\<^sup>2) * phase c y n)
            has_derivative
            (\<lambda>h. of_real (2 * ((x $ n) $ 1) * ((h $ n) $ 1)) * phase c x n
               + of_real (((x $ n) $ 1)\<^sup>2) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 1)\<^sup>2) :: complex) has_derivative
        (\<lambda>h. of_real (2 * ((x $ n) $ 1) * ((h $ n) $ 1)))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_sq_x])

  have dph:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
        (\<lambda>h. d_phase c x h n))
     (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 1)\<^sup>2) * phase c y n)
        has_derivative
        (\<lambda>h. of_real (((x $ n) $ 1)\<^sup>2) * d_phase c x h n
           + of_real (2 * ((x $ n) $ 1) * ((h $ n) $ 1)) * phase c x n))
     (at x within V)"
    using d_real dph
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

lemma has_derivative_M12_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real (w_M12 (y $ n)) * phase c y n)
            has_derivative
            (\<lambda>h. of_real (dw_M12 (x $ n) (h $ n)) * phase c x n
               + of_real (w_M12 (x $ n)) * d_phase c x h n))
         (at x within V)"
proof -
  have d1:
    "((\<lambda>y :: planar^'n. (y $ n) $ 1) has_derivative (\<lambda>h. (h $ n) $ 1))
     (at x within V)"
    by (rule has_derivative_nth_k_x)

  have d2:
    "((\<lambda>y :: planar^'n. (y $ n) $ 2) has_derivative (\<lambda>h. (h $ n) $ 2))
     (at x within V)"
    by (rule has_derivative_nth_k_x)

  have d_prod:
    "((\<lambda>y :: planar^'n. ((y $ n) $ 1) * ((y $ n) $ 2))
        has_derivative
        (\<lambda>h. ((x $ n) $ 1) * ((h $ n) $ 2)
           + ((h $ n) $ 1) * ((x $ n) $ 2)))
     (at x within V)"
    using d1 d2
    by (rule has_derivative_mult)

  have d_w:
    "((\<lambda>y :: planar^'n. w_M12 (y $ n)) has_derivative
        (\<lambda>h. dw_M12 (x $ n) (h $ n)))
     (at x within V)"
    using d_prod
    unfolding w_M12_def dw_M12_def
    by (simp add: algebra_simps)

  have d_real:
    "((\<lambda>y :: planar^'n. of_real (w_M12 (y $ n)) :: complex)
        has_derivative
        (\<lambda>h. of_real (dw_M12 (x $ n) (h $ n))))
     (at x within V)"
    by (rule has_derivative_of_real_lift[OF d_w])

  have dph:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
        (\<lambda>h. d_phase c x h n))
     (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real (w_M12 (y $ n)) * phase c y n)
        has_derivative
        (\<lambda>h. of_real (w_M12 (x $ n)) * d_phase c x h n
           + of_real (dw_M12 (x $ n) (h $ n)) * phase c x n))
     (at x within V)"
    using d_real dph
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

lemma has_derivative_M22_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 2)\<^sup>2) * phase c y n)
            has_derivative
            (\<lambda>h. of_real (2 * ((x $ n) $ 2) * ((h $ n) $ 2)) * phase c x n
               + of_real (((x $ n) $ 2)\<^sup>2) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 2)\<^sup>2) :: complex) has_derivative
        (\<lambda>h. of_real (2 * ((x $ n) $ 2) * ((h $ n) $ 2)))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_sq_x])

  have dph:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
        (\<lambda>h. d_phase c x h n))
     (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 2)\<^sup>2) * phase c y n)
        has_derivative
        (\<lambda>h. of_real (((x $ n) $ 2)\<^sup>2) * d_phase c x h n
           + of_real (2 * ((x $ n) $ 2) * ((h $ n) $ 2)) * phase c x n))
     (at x within V)"
    using d_real dph
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

definition DA_moment ::
  "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n \<Rightarrow> complex)"
where
  "DA_moment x c =
     (\<lambda>h. \<Sum>i\<in>UNIV. d_phase c x h i)"

definition DM1_moment ::
  "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n \<Rightarrow> complex)"
where
  "DM1_moment x c =
     (\<lambda>h. \<Sum>i\<in>UNIV.
        of_real ((h $ i) $ 1) * phase c x i
        + of_real ((x $ i) $ 1) * d_phase c x h i)"

definition DM2_moment ::
  "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n \<Rightarrow> complex)"
where
  "DM2_moment x c =
     (\<lambda>h. \<Sum>i\<in>UNIV.
        of_real ((h $ i) $ 2) * phase c x i
        + of_real ((x $ i) $ 2) * d_phase c x h i)"

definition DM11_moment ::
  "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n \<Rightarrow> complex)"
where
  "DM11_moment x c =
     (\<lambda>h. \<Sum>i\<in>UNIV.
        of_real (2 * ((x $ i) $ 1) * ((h $ i) $ 1)) * phase c x i
        + of_real (((x $ i) $ 1)\<^sup>2) * d_phase c x h i)"

definition DM12_moment ::
  "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n \<Rightarrow> complex)"
where
  "DM12_moment x c =
     (\<lambda>h. \<Sum>i\<in>UNIV.
        of_real (dw_M12 (x $ i) (h $ i)) * phase c x i
        + of_real (w_M12 (x $ i)) * d_phase c x h i)"

definition DM22_moment ::
  "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n \<Rightarrow> complex)"
where
  "DM22_moment x c =
     (\<lambda>h. \<Sum>i\<in>UNIV.
        of_real (2 * ((x $ i) $ 2) * ((h $ i) $ 2)) * phase c x i
        + of_real (((x $ i) $ 2)\<^sup>2) * d_phase c x h i)"

lemma has_derivative_A_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. A_moment y c) has_derivative (\<lambda>h. DA_moment x c h))
         (at x within V)"
  unfolding A_moment_def DA_moment_def
  by (rule has_derivative_sum) (use has_derivative_A_term in blast)

lemma has_derivative_M1_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M1_moment y c) has_derivative (\<lambda>h. DM1_moment x c h))
         (at x within V)"
  unfolding M1_moment_def DM1_moment_def
  by (rule has_derivative_sum) (use has_derivative_M1_term in blast)

lemma has_derivative_M2_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M2_moment y c) has_derivative (\<lambda>h. DM2_moment x c h))
         (at x within V)"
  unfolding M2_moment_def DM2_moment_def
  by (rule has_derivative_sum) (use has_derivative_M2_term in blast)

lemma has_derivative_M11_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M11_moment y c) has_derivative (\<lambda>h. DM11_moment x c h))
         (at x within V)"
  unfolding M11_moment_def DM11_moment_def
  by (rule has_derivative_sum) (use has_derivative_M11_term in blast)

lemma has_derivative_M12_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M12_moment y c) has_derivative (\<lambda>h. DM12_moment x c h))
         (at x within V)"
  unfolding M12_moment_def DM12_moment_def
  by (rule has_derivative_sum) (use has_derivative_M12_term in blast)

lemma has_derivative_M22_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M22_moment y c) has_derivative (\<lambda>h. DM22_moment x c h))
         (at x within V)"
  unfolding M22_moment_def DM22_moment_def
  by (rule has_derivative_sum) (use has_derivative_M22_term in blast)

definition Dmoment_map ::
  "(planar^'n) \<Rightarrow> planar \<Rightarrow> ((planar^'n) \<Rightarrow> complex^6)"
where
  "Dmoment_map x c =
     (\<lambda>h. \<chi> k.
        if k = 1 then DA_moment x c h
        else if k = 2 then DM1_moment x c h
        else if k = 3 then DM2_moment x c h
        else if k = 4 then DM11_moment x c h
        else if k = 5 then DM12_moment x c h
        else DM22_moment x c h)"

lemma has_derivative_moment_map:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. moment_map y c) has_derivative Dmoment_map x c) (at x within V)"
proof -
  have comps:
    "\<forall>k :: 6. ((\<lambda>y. moment_map y c $ k) has_derivative (\<lambda>h. Dmoment_map x c h $ k))
              (at x within V)"
  proof (intro allI)
    fix k :: 6
    consider "k = 1" | "k = 2" | "k = 3" | "k = 4" | "k = 5" | "k = 6"
      using exhaust_6 by metis
    thus "((\<lambda>y. moment_map y c $ k) has_derivative (\<lambda>h. Dmoment_map x c h $ k))
            (at x within V)"
    proof cases
      case 1 thus ?thesis
        using has_derivative_A_moment_x[where c=c and x=x and V=V]
        by (simp add: Dmoment_map_def)
    next
      case 2 thus ?thesis
        using has_derivative_M1_moment_x[where c=c and x=x and V=V]
        by (simp add: Dmoment_map_def)
    next
      case 3 thus ?thesis
        using has_derivative_M2_moment_x[where c=c and x=x and V=V]
        by (simp add: Dmoment_map_def)
    next
      case 4 thus ?thesis
        using has_derivative_M11_moment_x[where c=c and x=x and V=V]
        by (simp add: Dmoment_map_def)
    next
      case 5 thus ?thesis
        using has_derivative_M12_moment_x[where c=c and x=x and V=V]
        by (simp add: Dmoment_map_def)
    next
      case 6 thus ?thesis
        using has_derivative_M22_moment_x[where c=c and x=x and V=V]
        by (simp add: Dmoment_map_def)
    qed
  qed
  have vec_der:
    "((\<lambda>y. \<chi> k. moment_map y c $ k) has_derivative (\<lambda>h. \<chi> k. Dmoment_map x c h $ k))
     (at x within V)"
  proof (subst has_derivative_componentwise_within, intro ballI)
    fix b :: "complex^6" assume bB: "b \<in> Basis"
    from bB obtain k :: 6 and e :: complex
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

lemma Dmoment_map_components:
  shows "Dmoment_map x c h $ 1 = DA_moment x c h"
    and "Dmoment_map x c h $ 2 = DM1_moment x c h"
    and "Dmoment_map x c h $ 3 = DM2_moment x c h"
    and "Dmoment_map x c h $ 4 = DM11_moment x c h"
    and "Dmoment_map x c h $ 5 = DM12_moment x c h"
    and "Dmoment_map x c h $ 6 = DM22_moment x c h"
  unfolding Dmoment_map_def
  by simp_all

end
