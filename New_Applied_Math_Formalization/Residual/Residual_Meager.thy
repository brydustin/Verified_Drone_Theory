section \<open>The residual is meager\<close>

theory Residual_Meager
  imports
    Residual_Aligned
begin

text \<open>The two halves together: a point of @{const residual_set} is aligned or it is not.  Hence the
  residual set over the design box is meager.\<close>

lemma aligned_conf_iff_res_s:
  "aligned_conf x c \<longleftrightarrow> (\<forall>m. res_s m (phase_coords c x) = 0)"
  unfolding aligned_conf_def Im_A_phase by simp

lemma OmegaPF_design_compact: "compact (OmegaPF design_beam (pi / 4))"
  by (rule OmegaPF_compact)

theorem residual_set_design_cover:
  assumes card4: "4 \<le> CARD('n::finite)"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
     {x. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). x \<in> residual_set design_beam design_source {\<omega>}} \<subseteq> (\<Union>n. K n)
     \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  let ?\<Omega> = "OmegaPF design_beam (pi / 4)"
  let ?c = "cvec_dip design_beam design_source"
  define NA :: "((real^2)^'n) set" where
    "NA = {x. \<exists>\<omega>\<in>?\<Omega>. x \<in> residual_set design_beam design_source {\<omega>}
           \<and> (\<exists>m. res_s m (phase_coords (?c \<omega>) x) \<noteq> 0)}"
  define AL :: "((real^2)^'n) set" where
    "AL = {x. \<exists>\<omega>\<in>?\<Omega>. ?c \<omega> \<noteq> 0 \<and> A_moment x (?c \<omega>) \<noteq> 0 \<and> aligned_conf x (?c \<omega>)}"
  have "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set. NA \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
    unfolding NA_def by (rule nonaligned_residual_cover)
  then obtain KN :: "nat \<Rightarrow> ((real^2)^'n) set"
    where KN: "NA \<subseteq> (\<Union>n. KN n) \<and> (\<forall>n. closed (KN n)) \<and> (\<forall>n. negligible (KN n))" ..
  have "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set. AL \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
    unfolding AL_def by (rule aligned_bad_closed_cover[OF card4 OmegaPF_design_compact])
  then obtain KA :: "nat \<Rightarrow> ((real^2)^'n) set"
    where KA: "AL \<subseteq> (\<Union>n. KA n) \<and> (\<forall>n. closed (KA n)) \<and> (\<forall>n. negligible (KA n))" ..
  define F :: "bool \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set" where "F b n = (if b then KN n else KA n)" for b n
  have Fc: "closed (F b n)" and Fn: "negligible (F b n)" for b n
    using KN KA by (simp_all add: F_def)
  have "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      (\<Union>b. \<Union>n. F b n) \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
    by (rule countable_family_of_covers[OF Fc Fn])
  then obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where KP: "(\<Union>b. \<Union>n. F b n) \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))" ..
  have KNsub: "(\<Union>n. KN n) \<subseteq> (\<Union>b. \<Union>n. F b n)"
  proof -
    have "(\<Union>n. F True n) \<subseteq> (\<Union>b. \<Union>n. F b n)"
      by (rule UN_upper) simp
    then show ?thesis
      by (simp add: F_def)
  qed
  have KAsub: "(\<Union>n. KA n) \<subseteq> (\<Union>b. \<Union>n. F b n)"
  proof -
    have "(\<Union>n. F False n) \<subseteq> (\<Union>b. \<Union>n. F b n)"
      by (rule UN_upper) simp
    then show ?thesis
      by (simp add: F_def)
  qed
  have sub: "{x. \<exists>\<omega>\<in>?\<Omega>. x \<in> residual_set design_beam design_source {\<omega>}} \<subseteq> (\<Union>n. K n)"
  proof (rule subsetI)
    fix x :: "(real^2)^'n"
    assume "x \<in> {x. \<exists>\<omega>\<in>?\<Omega>. x \<in> residual_set design_beam design_source {\<omega>}}"
    then have "\<exists>\<omega>\<in>?\<Omega>. x \<in> residual_set design_beam design_source {\<omega>}"
      by (rule CollectD)
    then obtain \<omega> where box: "\<omega> \<in> ?\<Omega>" and bad: "x \<in> residual_set design_beam design_source {\<omega>}" ..
    have cnz: "?c \<omega> \<noteq> 0"
      by (rule residual_set_design_nondegenerate(1)[OF bad])
    have "A_cart ?c x \<omega> \<noteq> 0"
      using bad unfolding residual_set_def by simp
    then have Anz: "A_moment x (?c \<omega>) \<noteq> 0"
      by (rule A_moment_nz_of_A_cart)
    have "x \<in> (\<Union>b. \<Union>n. F b n)"
    proof (cases "\<exists>m. res_s m (phase_coords (?c \<omega>) x) \<noteq> 0")
      case True
      then have "x \<in> NA"
        unfolding NA_def using box bad by blast
      then have "x \<in> (\<Union>n. KN n)"
        by (rule subsetD[OF KN[THEN conjunct1]])
      then show ?thesis
        by (rule subsetD[OF KNsub])
    next
      case False
      then have "aligned_conf x (?c \<omega>)"
        by (simp add: aligned_conf_iff_res_s)
      then have "x \<in> AL"
        unfolding AL_def using box cnz Anz by blast
      then have "x \<in> (\<Union>n. KA n)"
        by (rule subsetD[OF KA[THEN conjunct1]])
      then show ?thesis
        by (rule subsetD[OF KAsub])
    qed
    then show "x \<in> (\<Union>n. K n)"
      by (rule subsetD[OF KP[THEN conjunct1]])
  qed
  show ?thesis
    by (rule exI[of _ K]) (rule conjI[OF sub KP[THEN conjunct2]])
qed

text \<open>The rank-deficient stratum inside any set \<open>V\<close>, for \<open>\<omega>\<^sub>0 = design_beam\<close>, \<open>\<omega>\<^sub>s = design_source\<close>, centre
  \<open>design_beam\<close> and half-width \<open>\<pi>/4\<close>.\<close>

theorem residual_meager_design:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> matrix_det (jacobian (cvec_dip design_beam design_source) (at \<omega>)) \<noteq> 0
          \<and> cvec_dip design_beam design_source \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip design_beam design_source) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where KP: "{x. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). x \<in> residual_set design_beam design_source {\<omega>}} \<subseteq> (\<Union>n. K n)
       \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
    using residual_set_design_cover[OF card4] ..
  have "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> matrix_det (jacobian (cvec_dip design_beam design_source) (at \<omega>)) \<noteq> 0
          \<and> cvec_dip design_beam design_source \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip design_beam design_source) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}
      \<subseteq> {x. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). x \<in> residual_set design_beam design_source {\<omega>}}"
    unfolding residual_set_def by auto
  then have cover: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> matrix_det (jacobian (cvec_dip design_beam design_source) (at \<omega>)) \<noteq> 0
          \<and> cvec_dip design_beam design_source \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip design_beam design_source) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}
      \<subseteq> (\<Union>n. K n)"
    by (rule subset_trans[OF _ KP[THEN conjunct1]])
  show ?thesis
    by (rule meager_negligible_closed_cover[OF cover]) (use KP in simp_all)
qed

end
