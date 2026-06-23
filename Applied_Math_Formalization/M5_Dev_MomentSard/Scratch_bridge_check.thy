theory Scratch_bridge_check
  imports Scratch_mstargc1
begin

text \<open>Isolated verification of the RESIDUAL-B agent's reusable bridge
  \<open>gradU_joint_surj_of_detHess\<close>: det HessU \<noteq> 0 \<Longrightarrow> the joint gradU derivative is
  surjective (the IFT-applicability input), SOUNDLY via gradU's omega-Hessian
  (NOT via any mstarg regular value).  Checked against the prebuilt
  Applied_Math_Appendix heap.\<close>

lemma gradU_joint_surj_of_detHess:
  fixes x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes h: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
  shows "\<exists>G'::(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2)).
            (\<forall>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                     has_derivative blinfun_apply (G' z)) (at z))
          \<and> continuous_on UNIV G'
          \<and> surj (blinfun_apply (G' (x,\<omega>)))"
proof -
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG': "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                          has_derivative blinfun_apply (G' z)) (at z)"
      and contG': "continuous_on UNIV G'"
    using gradU_dip_joint_C1 by blast
  have slice_eq:
    "(\<lambda>u::real^2. (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x,u))
       = (\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u)"
    by simp
  have ex: "\<exists>D\<omega>. ((\<lambda>u. (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x,u))
                   has_derivative D\<omega>) (at \<omega> within UNIV) \<and> surj D\<omega>"
  proof -
    have "\<exists>D\<omega>. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D\<omega>)
                (at \<omega> within UNIV) \<and> surj D\<omega>"
      using not_surj_omega_deriv_iff_detHess_dip[OF open_UNIV UNIV_I] h by blast
    thus ?thesis unfolding slice_eq .
  qed
  have surjpart: "surj (\<lambda>k. blinfun_apply (G' (x,\<omega>)) (0,k))"
    using exists_surj_deriv_iff_partial[OF open_UNIV UNIV_I derG'[of "(x,\<omega>)"]] ex
    by blast
  have surjfull: "surj (blinfun_apply (G' (x,\<omega>)))"
  proof -
    have sub: "range (\<lambda>k. blinfun_apply (G' (x,\<omega>)) (0,k))
                 \<subseteq> range (blinfun_apply (G' (x,\<omega>)))" by auto
    have full: "range (\<lambda>k. blinfun_apply (G' (x,\<omega>)) (0,k)) = UNIV"
      using surjpart by (simp add: surj_def)
    from sub full show ?thesis unfolding surj_def by (metis subset_UNIV subset_antisym)
  qed
  show ?thesis using derG' contG' surjfull by blast
qed

end
