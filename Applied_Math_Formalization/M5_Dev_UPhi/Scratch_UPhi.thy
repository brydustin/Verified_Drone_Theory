theory Scratch_UPhi
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

definition F_eta :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "F_eta \<eta> \<kappa> u = cos (\<kappa> * u) - \<kappa> * (u - \<eta>) * sin (\<kappa> * u)"

theorem real_analytic_on_F_eta:
  "real_analytic_on (F_eta \<eta> \<kappa>) UNIV"
proof -
  have id: "real_analytic_on (\<lambda>u::real. u) UNIV"
    by (rule real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_ident])
  show ?thesis
    unfolding F_eta_def[abs_def]
    by (intro real_analytic_on_diff real_analytic_on_mult real_analytic_on_const
        real_analytic_on_cos_comp real_analytic_on_sin_comp id open_UNIV)
qed

theorem F_eta_at_0:
  "F_eta \<eta> \<kappa> 0 = 1"
  unfolding F_eta_def by simp

theorem F_eta_zeros_nowhere_dense:
  "interior (closure {u. F_eta \<eta> \<kappa> u = 0}) = {}"
proof -
  have ex: "\<exists>u\<in>UNIV. F_eta \<eta> \<kappa> u \<noteq> 0"
    by (rule bexI[where x=0]) (simp_all add: F_eta_at_0)
  have "interior (closure {u \<in> UNIV. F_eta \<eta> \<kappa> u = 0}) = {}"
    by (rule real_analytic_1d_nowhere_dense_zeros
        [OF real_analytic_on_F_eta connected_UNIV ex])
  thus ?thesis by simp
qed

section \<open>Tier 2 substrate: parallel-slot derivative of Phi_par\<close>

lemma DM_paper_x_slot_1:
  fixes c v :: "real^2"
  shows "vec_nth (DM_paper_x x c (slot m v)) 1
       = -(c \<bullet> v) *\<^sub>R (\<i> * phase c x m)"
proof -
  have "vec_nth (DM_paper_x x c (slot m v)) 1 = DA_paper_x x c (slot m v)"
    by (simp add: DM_paper_x_def)
  also have "\<dots> = d_A_moment_x x c (slot m v)"
    by (rule DA_paper_eq_d_moment)
  also have "\<dots> = -(c \<bullet> v) *\<^sub>R (\<i> * phase c x m)"
    by (rule d_A_moment_x_slot)
  finally show ?thesis .
qed

lemma DM_paper_x_slot_2:
  fixes c v :: "real^2"
  shows "vec_nth (DM_paper_x x c (slot m v)) 2
       = of_real (vec_nth v 1) * phase c x m
         + of_real (vec_nth (vec_nth x m) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))"
proof -
  have "vec_nth (DM_paper_x x c (slot m v)) 2 = DM1_paper_x x c (slot m v)"
    by (simp add: DM_paper_x_def)
  also have "\<dots> = d_M1_moment_x x c (slot m v)"
    by (rule DM1_paper_eq_d_moment)
  also have "\<dots> = of_real (vec_nth v 1) * phase c x m
         + of_real (vec_nth (vec_nth x m) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))"
    by (rule d_M1_moment_x_slot)
  finally show ?thesis .
qed

lemma DM_paper_x_slot_3:
  fixes c v :: "real^2"
  shows "vec_nth (DM_paper_x x c (slot m v)) 3
       = of_real (vec_nth v 2) * phase c x m
         + of_real (vec_nth (vec_nth x m) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))"
proof -
  have "vec_nth (DM_paper_x x c (slot m v)) 3 = DM2_paper_x x c (slot m v)"
    by (simp add: DM_paper_x_def)
  also have "\<dots> = d_M2_moment_x x c (slot m v)"
    by (rule DM2_paper_eq_d_moment)
  also have "\<dots> = of_real (vec_nth v 2) * phase c x m
         + of_real (vec_nth (vec_nth x m) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))"
    by (rule d_M2_moment_x_slot)
  finally show ?thesis .
qed

theorem Phi_par_slot_value:
  fixes m :: "'n::finite" and v \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  shows "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m v)
      = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
               (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
               (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
               (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) 1
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
          * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
               (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
               (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
               (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) 2"
proof -
  have hd: "((\<lambda>y. e_par \<omega>0 \<omega>s \<omega> \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
       (\<lambda>h. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
              * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                   (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                   (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                   (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 1
            + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
              * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                   (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                   (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                   (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 2)) (at x)"
    by (rule has_derivative_gradU_inner_x)
  have eq: "(\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s)
      = (\<lambda>y. e_par \<omega>0 \<omega>s \<omega> \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)"
    by (rule ext) (simp add: Phi_par_def inner_commute)
  show ?thesis
    unfolding eq
    by (rule fun_cong[OF frechet_derivative_at[OF hd, symmetric]])
qed

corollary Phi_par_parallel_slot_value:
  fixes m :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  shows "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
          (slot m (cvec_dip \<omega>0 \<omega>s \<omega>))
      = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
               (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
               (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
               (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
               (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m (cvec_dip \<omega>0 \<omega>s \<omega>)))) 1
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
          * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
               (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
               (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
               (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
               (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m (cvec_dip \<omega>0 \<omega>s \<omega>)))) 2"
  by (rule Phi_par_slot_value)

definition ucoord :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "ucoord c p = (c \<bullet> p) / norm c"

definition eta_par :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "eta_par \<omega>0 \<omega>s \<omega> =
     frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
       / (2 * gain_dip \<omega>)"

lemma uphi_E1_deriv_F_eta:
  assumes g: "g \<noteq> 0" and eta: "\<eta> = g1 / (2 * g)"
  shows "2 * g * (- cos (\<kappa> * u) + \<kappa> * u * sin (\<kappa> * u))
           - g1 * \<kappa> * sin (\<kappa> * u)
       = - 2 * g * F_eta \<eta> \<kappa> u"
  using g unfolding eta F_eta_def
  by (simp add: field_simps)

lemma uphi_scalar_zero_iff:
  assumes a: "a \<noteq> 0" and g: "g \<noteq> 0" and k: "\<kappa> \<noteq> 0"
  shows "(- 2 * a * g * \<kappa> * F_eta \<eta> \<kappa> u = 0) \<longleftrightarrow> F_eta \<eta> \<kappa> u = 0"
  using a g k by auto

(* NEEDS FROM MAIN BRANCH: c-adapted gauge dictionary for Phi_par.
   This is the missing bridge from the invariant derivative formula above to
   the paper's gauge variables a,b,b1 and E1 = g1*a + 2*g*b1 on b=0.
   It should be proved by specializing Phi_par_parallel_slot_value with
   c = cvec_dip omega0 omegas omega, using Phi_par = 0 to drop the d(a)*E1
   term, and rewriting the single-slot contribution as
   -2*a*g*kappa*F_eta eta kappa u. *)
theorem Phi_par_parallel_slot_F_eta_identification:
  fixes m :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  defines "c \<equiv> cvec_dip \<omega>0 \<omega>s \<omega>"
    and "\<kappa> \<equiv> norm (cvec_dip \<omega>0 \<omega>s \<omega>)"
    and "\<eta> \<equiv> eta_par \<omega>0 \<omega>s \<omega>"
    and "u \<equiv> ucoord (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x m)"
    and "a \<equiv> Re (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "c \<noteq> 0"
    and b0: "Im (vec_nth (M_paper x c) 1) = 0"
    and crit: "Phi_par x \<omega> \<omega>0 \<omega>s = 0"
  shows "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m c)
       = - 2 * a * gain_dip \<omega> * \<kappa> * F_eta \<eta> \<kappa> u"
  sorry

theorem uphi_reduce_pointwise:
  fixes m :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  defines "c \<equiv> cvec_dip \<omega>0 \<omega>s \<omega>"
    and "\<kappa> \<equiv> norm (cvec_dip \<omega>0 \<omega>s \<omega>)"
    and "\<eta> \<equiv> eta_par \<omega>0 \<omega>s \<omega>"
    and "u \<equiv> ucoord (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x m)"
    and "a \<equiv> Re (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "c \<noteq> 0"
    and b0: "Im (vec_nth (M_paper x c) 1) = 0"
    and crit: "Phi_par x \<omega> \<omega>0 \<omega>s = 0"
    and apos: "a > 0"
    and gpos: "gain_dip \<omega> > 0"
  shows "(frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m c) = 0)
       \<longleftrightarrow> F_eta \<eta> \<kappa> u = 0"
proof -
  have knz: "\<kappa> \<noteq> 0"
    using cnz unfolding c_def \<kappa>_def by simp
  have anz: "a \<noteq> 0" using apos by simp
  have gnz: "gain_dip \<omega> \<noteq> 0" using gpos by simp
  have cnz': "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    using cnz unfolding c_def by simp
  have b0': "Im (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) = 0"
    using b0 unfolding c_def by simp
  have id: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m c)
       = - 2 * a * gain_dip \<omega> * \<kappa> * F_eta \<eta> \<kappa> u"
    unfolding c_def \<kappa>_def \<eta>_def u_def a_def
    by (rule Phi_par_parallel_slot_F_eta_identification[OF detnz cnz' b0' crit])
  show ?thesis
    unfolding id using uphi_scalar_zero_iff[OF anz gnz knz, of \<eta> u] by simp
qed

end
