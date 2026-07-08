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

end
