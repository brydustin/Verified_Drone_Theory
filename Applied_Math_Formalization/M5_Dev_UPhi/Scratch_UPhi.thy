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

end
