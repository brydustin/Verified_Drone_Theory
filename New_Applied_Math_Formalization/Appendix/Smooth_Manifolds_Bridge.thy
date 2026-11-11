theory Smooth_Manifolds_Bridge
  imports "HOL-Analysis.Analysis" "Smooth_Manifolds.Smooth"
begin

text \<open>Isabelle2026 ships \<open>Higher_Differentiability_Multi\<close> in HOL-Analysis.  The only fact the
  capstone chain needs that is not there is the link to the AFP predicate.\<close>

lemma Ck_on_iff_higher_differentiable_on:
  assumes "open U"
  shows "Ck_on k f U \<longleftrightarrow> higher_differentiable_on U f k"
  using assms
proof (induction k arbitrary: f U)
  case 0
  show ?case
  proof
    assume "Ck_on 0 f U"
    then have "\<forall>x\<in>U. continuous (at x) f"
      by (simp add: Ck_on_def)
    then have "\<forall>x\<in>U. continuous (at x within U) f"
      using continuous_at_imp_continuous_at_within by blast
    then show "higher_differentiable_on U f 0"
      by (simp add: continuous_on_eq_continuous_within higher_differentiable_on.simps(1))
  next
    assume "higher_differentiable_on U f 0"
    then have "continuous_on U f"
      using higher_differentiable_on.simps(1) by blast
    then have "\<forall>x\<in>U. continuous (at x within U) f"
      using continuous_on_eq_continuous_within by blast
    then have "\<forall>x\<in>U. continuous (at x) f"
      by (metis "0" at_within_open)
    then show "Ck_on 0 f U"
      using "0" by (simp add: Ck_on_def)
  qed
next
  case (Suc k)
  show ?case
  proof
    assume "Ck_on (Suc k) f U"
    then have U_open: "open U"
      and Cat: "\<forall>x\<in>U. Ck_at (Suc k) f x"
      by (auto simp: Ck_on_def)
    have diff: "\<forall>x\<in>U. f differentiable (at x)"
      using Cat by auto
    have der_Ck_on: "\<forall>v. Ck_on k (\<lambda>y. frechet_derivative f (at y) v) U"
      using Cat Ck_on_def U_open by fastforce
    have der_higher: "\<forall>v. higher_differentiable_on U (\<lambda>y. frechet_derivative f (at y) v) k"
      using Suc.IH[OF U_open] der_Ck_on by blast
    then show "higher_differentiable_on U f (Suc k)"
      using diff higher_differentiable_on.simps(2) by blast
  next
    assume H: "higher_differentiable_on U f (Suc k)"
    then have diff: "\<forall>x\<in>U. f differentiable (at x)"
      and der_higher:
        "\<forall>v. higher_differentiable_on U (\<lambda>y. frechet_derivative f (at y) v) k"
      using H higher_differentiable_on.simps(2) by blast+
    have Hk: "higher_differentiable_on U f k"
      using H by (rule higher_differentiable_on_SucD)
    have CkU: "Ck_on k f U"
      using Suc.IH[OF Suc.prems] Hk by blast
    have der_Ck_on: "\<forall>v. Ck_on k (\<lambda>y. frechet_derivative f (at y) v) U"
      using Suc.IH[OF Suc.prems] der_higher by blast
    show "Ck_on (Suc k) f U"
      by (metis CkU Ck_at.simps(2) Ck_on_def der_Ck_on diff)
  qed
qed


end
