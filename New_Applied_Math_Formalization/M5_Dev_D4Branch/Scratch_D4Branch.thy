theory Scratch_D4Branch
  imports "Applied_Math_M5_Wiring.Scratch_Wiring"
begin

section \<open>D4 Branch-P: reducing the retained bad fibre to the gradU chart engine\<close>

text \<open>
  This scratch leaf targets the hardest remaining permanent obligation,
  @{const branchP_indep_closed_cover_core_all}.  The point of this first
  iteration is deliberately narrow: prove the sound structural reduction and
  do not assert the missing Branch-P regularity theorem.

  The permanent @{const BadXGW} already contains @{term "det (HessU c g x w) = 0"}.
  Hence it lies in the ordinary @{thm charts_core_Nn} bad set for
  @{term "(\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))"} over any open
  steering neighbourhood containing the witness angles.  The verified bridge is
  @{thm not_surj_omega_deriv_iff_detHess_dip}.
\<close>

definition gradU_engine_bad ::
  "((real^2)^'n::finite) set \<Rightarrow> (real^2) set \<Rightarrow> real^2 \<Rightarrow> real^2
    \<Rightarrow> ((real^2)^'n) set" where
  "gradU_engine_bad V \<Omega> \<omega>0 \<omega>s =
     {x\<in>V. \<exists>\<omega>\<in>\<Omega>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and>
        \<not> (\<exists>D\<omega>. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u)
              has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)}"

lemma countable_subcover_of_openin_cover:
  fixes M :: "'a::second_countable_topology set"
    and \<F> :: "'a set set"
  assumes openF: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S"
    and cover: "M \<subseteq> \<Union>\<F>"
  obtains \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "M \<subseteq> \<Union>\<F>'"
proof -
  have scM: "second_countable (top_of_set M)"
    using second_countable_subtopology[OF second_countable_euclidean, of M] by simp
  have lindM: "Lindelof_space (top_of_set M)"
    using second_countable_imp_Lindelof_space[OF scM] .
  have union_top: "\<Union>\<F> = topspace (top_of_set M)"
  proof
    show "\<Union>\<F> \<subseteq> topspace (top_of_set M)"
      by (meson Sup_le_iff openF openin_subset)
    show "topspace (top_of_set M) \<subseteq> \<Union>\<F>"
      using cover by simp
  qed
  have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<F> \<and> \<Union>\<V> = topspace (top_of_set M)"
    using lindM openF union_top unfolding Lindelof_space_def
    by (meson Top1_Ch3.countable_def countableE)
  then obtain \<V> where Vprops:
      "countable \<V> \<and> \<V> \<subseteq> \<F> \<and> \<Union>\<V> = topspace (top_of_set M)"
    by (elim exE)
  show ?thesis
    by (rule that[of \<V>]) (use Vprops in auto)
qed

lemma BadXGW_subset_gradU_engine_bad:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> \<Omega> :: "(real^2) set"
  assumes Oopen: "open \<Omega>" and Gsub: "\<Gamma> \<subseteq> \<Omega>"
  shows "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> gradU_engine_bad V \<Omega> \<omega>0 \<omega>s"
proof
  fix x :: "(real^2)^'n"
  assume xbad: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
  then obtain \<omega> where wG: "\<omega> \<in> \<Gamma>"
    and grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and det0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
    unfolding BadXGW_def by blast
  have xV: "x \<in> V" using xbad by blast
  have wO: "\<omega> \<in> \<Omega>" using Gsub wG by blast
  have nsurj_omega:
    "\<not> (\<exists>D\<omega>. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u)
          has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)"
    using not_surj_omega_deriv_iff_detHess_dip[OF Oopen wO] det0 by blast
  show "x \<in> gradU_engine_bad V \<Omega> \<omega>0 \<omega>s"
    unfolding gradU_engine_bad_def
    using xV wO grad0 nsurj_omega by blast
qed

lemma BadXGW_subset_D3BadXG_H0core:
  "(BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n::finite) set)
      \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s \<Gamma>"
  unfolding BadXGW_def D3BadXG_H0core_def by blast

subsection \<open>Explicit x-partial rank defect and cokernel covectors\<close>

text \<open>
  The last conjunct of @{const BadXGW} is stated as failure of an existential
  surjective derivative.  For the countability route we need the equivalent
  explicit rank-defect form, and then the standard cokernel-covector witness.
\<close>

definition gradU_x_partial_dip ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n::finite) \<Rightarrow> real^2
    \<Rightarrow> (((real^2)^'n) \<Rightarrow> real^2)" where
  "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> =
     (\<lambda>h. \<chi> j. dEjm
        (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1))
        (gain_dip \<omega>)
        ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1)
        ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
        (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
        (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h))"

lemma gradU_x_partial_dip_has_derivative:
  fixes x :: "(real^2)^'n::finite"
  shows "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
      has_derivative gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>) (at x)"
  unfolding gradU_x_partial_dip_def
  by (rule has_derivative_gradU_dip_x_explicit)

lemma gradU_x_partial_dip_bounded_linear:
  fixes x :: "(real^2)^'n::finite"
  shows "bounded_linear (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
  using gradU_x_partial_dip_has_derivative has_derivative_bounded_linear by blast

lemma gradU_x_partial_dip_linear:
  fixes x :: "(real^2)^'n::finite"
  shows "linear (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
  using bounded_linear.linear[OF gradU_x_partial_dip_bounded_linear] .

lemma gradU_x_partial_dip_surj_iff_has_surj_derivative:
  fixes x :: "(real^2)^'n::finite"
  shows "(\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx) (at x) \<and> surj Dx)
    \<longleftrightarrow> surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
proof
  assume "\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
      has_derivative Dx) (at x) \<and> surj Dx"
  then obtain Dx :: "((real^2)^'n) \<Rightarrow> real^2" where
    d: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx) (at x)"
    and s: "surj Dx"
    by blast
  have "Dx = gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>"
    by (rule has_derivative_unique[OF d gradU_x_partial_dip_has_derivative])
  with s show "surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
    by simp
next
  assume "surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
  then show "\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx) (at x) \<and> surj Dx"
    using gradU_x_partial_dip_has_derivative by blast
qed

definition gradU_x_rank_defect_dip ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n::finite) \<Rightarrow> real^2 \<Rightarrow> bool" where
  "gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>
    \<longleftrightarrow> \<not> surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"

definition gradU_x_cokernel_covector_dip ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n::finite) \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool"
  where
  "gradU_x_cokernel_covector_dip \<omega>0 \<omega>s x \<omega> ell
    \<longleftrightarrow> ell \<noteq> 0 \<and>
      (\<forall>h. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> h = 0)"

lemma not_surj_linear_iff_exists_cokernel_vector:
  fixes L :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lin: "linear L"
  shows "\<not> surj L \<longleftrightarrow>
    (\<exists>ell::'b. ell \<noteq> 0 \<and> (\<forall>h. ell \<bullet> L h = 0))"
proof
  assume nsurj: "\<not> surj L"
  have surj_iff_inj_adj: "surj L \<longleftrightarrow> inj (adjoint L)"
  proof -
    have "surj (adjoint (adjoint L)) = inj (adjoint L)"
      by (rule surj_adjoint_iff_inj[OF adjoint_linear[OF lin]])
    then show ?thesis
      by (simp add: adjoint_adjoint[OF lin])
  qed
  have n_inj_adj: "\<not> inj (adjoint L)"
    using nsurj surj_iff_inj_adj by simp
  have lin_adj: "linear (adjoint L)"
    by (rule adjoint_linear[OF lin])
  obtain ell :: 'b where ellnz: "ell \<noteq> 0" and adj0: "adjoint L ell = 0"
    using n_inj_adj unfolding linear_injective_0[OF lin_adj] by blast
  have ann: "ell \<bullet> L h = 0" for h
  proof -
    have "adjoint L ell \<bullet> h = ell \<bullet> L h"
      by (rule adjoint_clauses(2)[OF lin])
    with adj0 show ?thesis
      by simp
  qed
  show "\<exists>ell::'b. ell \<noteq> 0 \<and> (\<forall>h. ell \<bullet> L h = 0)"
    using ellnz ann by blast
next
  assume "\<exists>ell::'b. ell \<noteq> 0 \<and> (\<forall>h. ell \<bullet> L h = 0)"
  then obtain ell :: 'b where ellnz: "ell \<noteq> 0" and ann: "\<And>h. ell \<bullet> L h = 0"
    by blast
  show "\<not> surj L"
  proof
    assume surjL: "surj L"
    then obtain h where Lh: "ell = L h"
      unfolding surj_def by blast
    have "ell \<bullet> ell = 0"
      using ann[of h] Lh by simp
    with ellnz show False
      by (simp only: inner_eq_zero_iff)
  qed
qed

lemma gradU_x_rank_defect_dip_iff_cokernel_covector:
  fixes x :: "(real^2)^'n::finite"
  shows "gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>
    \<longleftrightarrow> (\<exists>ell. gradU_x_cokernel_covector_dip \<omega>0 \<omega>s x \<omega> ell)"
proof -
  have lin: "linear (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
    by (rule gradU_x_partial_dip_linear)
  have "\<not> surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)
      \<longleftrightarrow> (\<exists>ell. ell \<noteq> 0 \<and>
        (\<forall>h. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> h = 0))"
    by (rule not_surj_linear_iff_exists_cokernel_vector[OF lin])
  then show ?thesis
    unfolding gradU_x_rank_defect_dip_def gradU_x_cokernel_covector_dip_def .
qed

lemma BadXGW_x_derivative_failure_iff_cokernel_covector:
  fixes x :: "(real^2)^'n::finite"
  shows "(\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx) (at x) \<and> surj Dx))
    \<longleftrightarrow> (\<exists>ell. gradU_x_cokernel_covector_dip \<omega>0 \<omega>s x \<omega> ell)"
proof -
  have witness:
    "(\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx) (at x) \<and> surj Dx)
      \<longleftrightarrow> surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
    by (rule gradU_x_partial_dip_surj_iff_has_surj_derivative)
  have cov:
    "\<not> surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)
      \<longleftrightarrow> (\<exists>ell. gradU_x_cokernel_covector_dip \<omega>0 \<omega>s x \<omega> ell)"
  proof -
    have lin: "linear (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
      by (rule gradU_x_partial_dip_linear)
    show ?thesis
      using not_surj_linear_iff_exists_cokernel_vector[OF lin]
      unfolding gradU_x_cokernel_covector_dip_def by simp
  qed
  show ?thesis
    using witness cov by blast
qed

lemma BadXGW_x_derivative_failure_iff_rank_defect:
  fixes x :: "(real^2)^'n::finite"
  shows "(\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx) (at x) \<and> surj Dx))
    \<longleftrightarrow> gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>"
proof -
  have witness:
    "(\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx) (at x) \<and> surj Dx)
      \<longleftrightarrow> surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
    by (rule gradU_x_partial_dip_surj_iff_has_surj_derivative)
  show ?thesis
    using witness unfolding gradU_x_rank_defect_dip_def by blast
qed

lemma d3_H0core_chart_core_negligible_closed_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and \<gamma> :: "(real^2) set"
  assumes core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>n. K n) \<and>
      (\<forall>n. closed (K n)) \<and>
      (\<forall>n. negligible (K n))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using core unfolding d3_detHess_arc_chart_core_def by blast
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have Kcover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>n. K n)"
    using cover unfolding K_def by blast
  have Kclosed: "closed (K n)" for n
    using clo unfolding K_def by blast
  have Kneg: "negligible (K n)" for n
    unfolding K_def
    by (rule negligible_singular_image_2n
          [where f = "fst \<circ> charts n" and S = "Crit n"
             and f' = "\<lambda>x. blinfun_apply (D n x)"])
       (use der rank in blast)+
  show ?thesis
    using Kcover Kclosed Kneg by blast
qed

lemma branchP_indep_closed_cover_core_of_d3_H0core_chart_core:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> :: "(real^2) set"
  assumes core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<Gamma>"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where coverH: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>n. K n)"
      and closedK: "\<forall>n. closed (K n)"
      and negligibleK: "\<forall>n. negligible (K n)"
    using d3_H0core_chart_core_negligible_closed_cover[OF core] by blast
  have coverB: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>n. K n)"
    using BadXGW_subset_D3BadXG_H0core coverH
    by fastforce 
  show ?thesis
    unfolding branchP_indep_closed_cover_core_def
    using coverB closedK negligibleK by blast
qed

definition branchP_bad_angles ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> (real^2) set" where
  "branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> =
    {\<omega> \<in> \<Gamma>. \<exists>x\<in>V. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}}"

definition branchP_joint_rank_bad ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> (((real^2)^'n) \<times> (real^2)) set" where
  "branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma> =
    {(x, \<omega>). x \<in> V \<and> \<omega> \<in> \<Gamma> \<and>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and>
      det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0 \<and>
      A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0 \<and>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0 \<and>
      cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and>
      \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)) \<and>
      gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>}"

definition branchP_joint_cokernel_bad ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<times> (real^2)) set" where
  "branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma> =
    {((x, \<omega>), ell).
      (x, \<omega>) \<in> branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma> \<and>
      gradU_x_cokernel_covector_dip \<omega>0 \<omega>s x \<omega> ell}"

lemma branchP_bad_angles_eq_snd_image_joint_rank_bad:
  "branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> =
    snd ` branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma>"
proof -
  have single_iff: "\<And>x \<omega>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
      \<longleftrightarrow>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and>
      det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0 \<and>
      A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0 \<and>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0 \<and>
      cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and>
      \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)) \<and>
      gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>"
  proof -
    fix x :: "(real^2)^'n" and \<omega> :: "real^2"
    have key: "(\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
          has_derivative Dx) (at x) \<and> surj Dx))
        \<longleftrightarrow> gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>"
      by (rule BadXGW_x_derivative_failure_iff_rank_defect)
    show "x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
      \<longleftrightarrow>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and>
      det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0 \<and>
      A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0 \<and>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0 \<and>
      cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and>
      \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)) \<and>
      gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>"
      unfolding BadXGW_def using key by auto
  qed
  show ?thesis
    unfolding branchP_bad_angles_def branchP_joint_rank_bad_def
    using single_iff by (auto simp: image_def)
qed

lemma branchP_joint_rank_bad_eq_fst_image_joint_cokernel_bad:
  "branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma> =
    fst ` branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>"
proof (rule subset_antisym)
  show "branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma> \<subseteq> fst ` branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>"
  proof
    fix p
    assume p_in: "p \<in> branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma>"
    obtain x \<omega> where p_def: "p = (x, \<omega>)" by (cases p)
    have rd: "gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>"
      using p_in unfolding p_def branchP_joint_rank_bad_def by blast
    obtain ell where ellc: "gradU_x_cokernel_covector_dip \<omega>0 \<omega>s x \<omega> ell"
      using rd gradU_x_rank_defect_dip_iff_cokernel_covector by blast
    have "((x, \<omega>), ell) \<in> branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>"
      unfolding branchP_joint_cokernel_bad_def
      using p_in p_def ellc by auto
    thus "p \<in> fst ` branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>"
      unfolding p_def
      by (simp add: rev_image_eqI)  
  qed
next
  show "fst ` branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma> \<subseteq> branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma>"
  proof
    fix p
    assume "p \<in> fst ` branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>"
    then obtain q where q_in: "q \<in> branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>" and p_eq: "p = fst q"
      by (elim imageE)
    obtain x \<omega> ell where q_def: "q = ((x, \<omega>), ell)" by (cases q) auto
    have "(x, \<omega>) \<in> branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma>"
      using q_in unfolding q_def branchP_joint_cokernel_bad_def by blast
    thus "p \<in> branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma>"
      using p_eq q_def by simp
  qed
qed

lemma branchP_bad_angles_eq_cokernel_projection:
  "branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> =
    snd ` (fst ` branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>)"
  using branchP_bad_angles_eq_snd_image_joint_rank_bad
    branchP_joint_rank_bad_eq_fst_image_joint_cokernel_bad
  by metis
  

lemma countable_branchP_bad_angles_of_countable_joint_rank_bad:
  assumes "countable (branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma>)"
  shows "countable (branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>)"
  using assms
  by (simp add: branchP_bad_angles_eq_snd_image_joint_rank_bad,
         metis Top1_Ch3.countable_def empty_is_image image_image inj_on_inv_into subsetI
         top1_countable_nonempty_eq_image_nat)

lemma countable_branchP_bad_angles_of_countable_joint_cokernel_bad:
  assumes "countable (branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>)"
  shows "countable (branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>)"
  using assms
  by (simp add: branchP_bad_angles_eq_cokernel_projection, 
          metis Top1_Ch3.countable_def empty_is_image image_image inj_on_inv_into subsetI
          top1_countable_nonempty_eq_image_nat)

lemma branchP_bad_angle_cvec_nonzero:
  assumes "\<omega> \<in> branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>"
  shows "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  using assms unfolding branchP_bad_angles_def BadXGW_def by blast

lemma branchP_bad_angle_Dcvec_det_nonzero:
  assumes "\<omega> \<in> branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>"
  shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  using assms unfolding branchP_bad_angles_def BadXGW_def by blast

lemma branchP_bad_angle_gain_nonzero:
  assumes Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and wbad: "\<omega> \<in> branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>"
  shows "gain_dip \<omega> \<noteq> 0"
proof -
  have "\<omega> \<in> \<Gamma>"
    using wbad unfolding branchP_bad_angles_def by simp
  hence "\<omega> \<in> OmegaPF ctr \<delta>"
    using Gsub by blast
  hence "sin (\<omega> $ 1) \<noteq> 0"
    using pf by blast
  thus ?thesis
    by (rule gain_dip_nonzero_of_sin)
qed

lemma branchP_bad_angles_empty_imp_no_BadXGW:
  assumes empty: "branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> = {}"
  shows "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n::finite) set) = {}"
proof
  show "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> {}"
  proof
    fix x :: "(real^2)^'n"
    assume xbad: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
    have xV: "x \<in> V"
      using xbad by simp
    obtain \<omega> where wG: "\<omega> \<in> \<Gamma>" and xsingle: "x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}"
      using xbad unfolding BadXGW_def by blast
    have "\<omega> \<in> branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>"
      unfolding branchP_bad_angles_def using wG xV xsingle by blast
    thus "x \<in> ({} :: ((real^2)^'n) set)"
      using empty by simp
  qed
  show "({} :: ((real^2)^'n) set) \<subseteq> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
    by simp
qed

lemma branchP_fixed_omega_cover_of_bad_angle_range_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and om :: "nat \<Rightarrow> real^2"
    and \<Gamma> :: "(real^2) set"
  assumes bad_cover: "branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> \<subseteq> range om"
  shows "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
proof
  fix x :: "(real^2)^'n"
  assume xbad: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
  have xV: "x \<in> V"
    using xbad by simp
  obtain \<omega> where wG: "\<omega> \<in> \<Gamma>" and xsingle: "x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}"
    using xbad unfolding BadXGW_def by blast
  have wbad: "\<omega> \<in> branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>"
    unfolding branchP_bad_angles_def using wG xV xsingle by blast
  then obtain i where weq: "\<omega> = om i"
    using bad_cover by blast
  have "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {om i}"
    using xsingle weq BadXGW_subset_D3BadXG_H0core by blast
  hence "x \<in> V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i}"
    using xV by simp
  thus "x \<in> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
    by blast
qed

lemma branchP_indep_closed_cover_core_of_gradU_engine_charts:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> \<Omega> :: "(real^2) set"
  assumes Oopen: "open \<Omega>" and Gsub: "\<Gamma> \<subseteq> \<Omega>"
    and charts:
      "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
          (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
          (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
        gradU_engine_bad V \<Omega> \<omega>0 \<omega>s
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
        (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)) \<and>
        (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
        (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "gradU_engine_bad V \<Omega> \<omega>0 \<omega>s
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using charts by blast
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have badsub: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> gradU_engine_bad V \<Omega> \<omega>0 \<omega>s"
    by (rule BadXGW_subset_gradU_engine_bad[OF Oopen Gsub])
  have Kcover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    using badsub cover unfolding K_def by blast
  have Kclosed: "closed (K n)" for n
    using clo unfolding K_def by blast
  have Knegligible: "negligible (K n)" for n
    unfolding K_def
    by (rule negligible_singular_image_2n
          [where f = "fst \<circ> charts n" and S = "Crit n"
             and f' = "\<lambda>x. blinfun_apply (D n x)"])
       (use der rank in blast)+
  show ?thesis
    unfolding branchP_indep_closed_cover_core_def
    using Kcover Kclosed Knegligible by blast
qed

lemma branchP_indep_closed_cover_core_of_gradU_regular_value:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> \<Omega> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}"
    and Oopen: "open \<Omega>" and Gsub: "\<Gamma> \<subseteq> \<Omega>"
    and reg: "regular_value_on
      (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
      (V \<times> \<Omega>) 0"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof -
  obtain G' :: "(((real^2)^'n) \<times> (real^2))
      \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          has_derivative blinfun_apply (G' z)) (at z)"
      and contG: "continuous_on UNIV G'"
    using gradU_dip_joint_C1 by blast
  have C1: "\<exists>G'. (\<forall>z\<in>V \<times> \<Omega>.
          ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
            has_derivative blinfun_apply (G' z)) (at z))
        \<and> continuous_on (V \<times> \<Omega>) G'"
  proof (intro exI[where x = G'] conjI ballI)
    show "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
            has_derivative blinfun_apply (G' z)) (at z)"
      if "z \<in> V \<times> \<Omega>" for z
      by (rule derG)
    show "continuous_on (V \<times> \<Omega>) G'"
      by (rule continuous_on_subset[OF contG]) blast
  qed
  have charts:
      "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
          (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
          (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
        gradU_engine_bad V \<Omega> \<omega>0 \<omega>s
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
        (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)) \<and>
        (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
        (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    using charts_core_Nn[
      where V = V and \<Omega> = \<Omega>
        and G = "(\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))",
      OF openV Vne Oopen reg C1]
    unfolding gradU_engine_bad_def
    by simp
  show ?thesis
    by (rule branchP_indep_closed_cover_core_of_gradU_engine_charts[OF Oopen Gsub charts])
qed

lemma branchP_indep_closed_cover_core_of_countable_closed_covers:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> :: "(real^2) set"
    and K :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. \<Union>j. K i j)"
    and closedK: "\<And>i j. closed (K i j)"
    and negligibleK: "\<And>i j. negligible (K i j)"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof -
  define i_of :: "nat \<Rightarrow> nat" where "i_of n = fst (prod_decode n)" for n
  define j_of :: "nat \<Rightarrow> nat" where "j_of n = snd (prod_decode n)" for n
  define K' :: "nat \<Rightarrow> ((real^2)^'n) set" where
    "K' n = K (i_of n) (j_of n)" for n
  have Kcover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K' n)"
  proof
    fix x :: "(real^2)^'n"
    assume xbad: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
    then obtain i j where xK: "x \<in> K i j"
      using cover by blast
    define n where "n = prod_encode (i, j)"
    have "i_of n = i"
      unfolding i_of_def n_def by simp
    moreover have "j_of n = j"
      unfolding j_of_def n_def by simp
    ultimately have "x \<in> K' n"
      using xK unfolding K'_def by simp
    thus "x \<in> (\<Union>n. K' n)" by blast
  qed
  have Kclosed: "closed (K' n)" for n
    unfolding K'_def by (rule closedK)
  have Kneg: "negligible (K' n)" for n
    unfolding K'_def by (rule negligibleK)
  show ?thesis
    unfolding branchP_indep_closed_cover_core_def
    using Kcover Kclosed Kneg by blast
qed

lemma gradU_engine_charts_negligible_closed_cover:
  fixes W :: "((real^2)^'n::finite) set"
    and \<Omega> :: "(real^2) set"
  assumes charts:
      "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
          (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
          (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
        gradU_engine_bad W \<Omega> \<omega>0 \<omega>s
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
        (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)) \<and>
        (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
        (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      gradU_engine_bad W \<Omega> \<omega>0 \<omega>s \<subseteq> (\<Union>n. K n) \<and>
      (\<forall>n. closed (K n)) \<and>
      (\<forall>n. negligible (K n))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "gradU_engine_bad W \<Omega> \<omega>0 \<omega>s
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using charts by blast
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have Kclosed: "closed (K n)" for n
    using clo unfolding K_def by blast
  have Kneg: "negligible (K n)" for n
    unfolding K_def
    by (rule negligible_singular_image_2n
          [where f = "fst \<circ> charts n" and S = "Crit n"
             and f' = "\<lambda>x. blinfun_apply (D n x)"])
       (use der rank in blast)+
  show ?thesis
    using cover Kclosed Kneg unfolding K_def by blast
qed

lemma branchP_indep_closed_cover_core_of_countable_gradU_engine_closed_covers:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> :: "(real^2) set"
    and S :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. S i)"
    and local_covers: "\<And>i. \<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      S i \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof -
  define K :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set" where
    "K i = (SOME K :: nat \<Rightarrow> ((real^2)^'n) set.
      S i \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n)))" for i
  have Kall: "S i \<subseteq> (\<Union>n. K i n)
        \<and> (\<forall>n. closed (K i n)) \<and> (\<forall>n. negligible (K i n))" for i
  proof -
    have "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      S i \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
      by (rule local_covers)
    thus ?thesis
      unfolding K_def by (rule someI_ex)
  qed
  have coverK: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. \<Union>j. K i j)"
  proof
    fix x :: "(real^2)^'n"
    assume xbad: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
    then obtain i where xS: "x \<in> S i"
      using cover by blast
    then obtain j where "x \<in> K i j"
      using Kall[of i] by blast
    thus "x \<in> (\<Union>i. \<Union>j. K i j)"
      by blast
  qed
  have closedK: "closed (K i j)" for i j
    using Kall[of i] by blast
  have negligibleK: "negligible (K i j)" for i j
    using Kall[of i] by blast
  show ?thesis
    by (rule branchP_indep_closed_cover_core_of_countable_closed_covers
        [OF coverK closedK negligibleK])
qed

lemma branchP_indep_closed_cover_core_of_countable_gradU_engine_charts:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> :: "(real^2) set"
    and W :: "nat \<Rightarrow> ((real^2)^'n) set"
    and \<Omega> :: "nat \<Rightarrow> (real^2) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. gradU_engine_bad (W i) (\<Omega> i) \<omega>0 \<omega>s)"
    and charts: "\<And>i.
      \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
          (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
          (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
        gradU_engine_bad (W i) (\<Omega> i) \<omega>0 \<omega>s
          \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
        (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x)))
            (at x within Crit j)) \<and>
        (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
        (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof (rule branchP_indep_closed_cover_core_of_countable_gradU_engine_closed_covers[OF cover])
  fix i
  show "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      gradU_engine_bad (W i) (\<Omega> i) \<omega>0 \<omega>s \<subseteq> (\<Union>n. K n) \<and>
      (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
    by (rule gradU_engine_charts_negligible_closed_cover[OF charts])
qed

lemma branchP_indep_closed_cover_core_of_countable_gradU_regular_value_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> :: "(real^2) set"
    and W :: "nat \<Rightarrow> ((real^2)^'n) set"
    and \<Omega> :: "nat \<Rightarrow> (real^2) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. gradU_engine_bad (W i) (\<Omega> i) \<omega>0 \<omega>s)"
    and openW: "\<And>i. open (W i)"
    and Wne: "\<And>i. W i \<noteq> {}"
    and openO: "\<And>i. open (\<Omega> i)"
    and reg: "\<And>i. regular_value_on
      (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
      (W i \<times> \<Omega> i) 0"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof -
  obtain G' :: "(((real^2)^'n) \<times> (real^2))
      \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          has_derivative blinfun_apply (G' z)) (at z)"
      and contG: "continuous_on UNIV G'"
    using gradU_dip_joint_C1 by blast
  have charts: "\<And>i.
      \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
          (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
          (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
        gradU_engine_bad (W i) (\<Omega> i) \<omega>0 \<omega>s
          \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
        (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x)))
            (at x within Crit j)) \<and>
        (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
        (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  proof -
    fix i
    have C1: "\<exists>G'. (\<forall>z\<in>W i \<times> \<Omega> i.
          ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
            has_derivative blinfun_apply (G' z)) (at z))
        \<and> continuous_on (W i \<times> \<Omega> i) G'"
    proof (intro exI[where x = G'] conjI ballI)
      show "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
              has_derivative blinfun_apply (G' z)) (at z)"
        if "z \<in> W i \<times> \<Omega> i" for z
        by (rule derG)
      show "continuous_on (W i \<times> \<Omega> i) G'"
        by (rule continuous_on_subset[OF contG]) blast
    qed
    show "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
          (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
          (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
        gradU_engine_bad (W i) (\<Omega> i) \<omega>0 \<omega>s
          \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
        (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x)))
            (at x within Crit j)) \<and>
        (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
        (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
      using charts_core_Nn[
        where V = "W i" and \<Omega> = "\<Omega> i"
          and G = "(\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))",
        OF openW Wne openO reg C1]
      unfolding gradU_engine_bad_def
      by simp
  qed
  show ?thesis
    by (rule branchP_indep_closed_cover_core_of_countable_gradU_engine_charts[OF cover charts])
qed

lemma branchP_indep_closed_cover_core_of_countable_steering_regular_value_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> :: "(real^2) set"
    and \<Omega> :: "nat \<Rightarrow> (real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}"
    and Gcover: "\<Gamma> \<subseteq> (\<Union>i. \<Omega> i)"
    and openO: "\<And>i. open (\<Omega> i)"
    and reg: "\<And>i. regular_value_on
      (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
      (V \<times> \<Omega> i) 0"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof -
  have cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. gradU_engine_bad V (\<Omega> i) \<omega>0 \<omega>s)"
  proof
    fix x :: "(real^2)^'n"
    assume xbad: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
    then obtain \<omega> where wG: "\<omega> \<in> \<Gamma>"
      and grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and det0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      unfolding BadXGW_def by blast
    obtain i where wO: "\<omega> \<in> \<Omega> i"
      using Gcover wG by blast
    have nsurj_omega:
      "\<not> (\<exists>D\<omega>. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u)
            has_derivative D\<omega>) (at \<omega> within \<Omega> i) \<and> surj D\<omega>)"
      using not_surj_omega_deriv_iff_detHess_dip[OF openO[of i] wO] det0
      by blast
    have "x \<in> gradU_engine_bad V (\<Omega> i) \<omega>0 \<omega>s"
      unfolding gradU_engine_bad_def
      using xbad wO grad0 nsurj_omega by blast
    thus "x \<in> (\<Union>i. gradU_engine_bad V (\<Omega> i) \<omega>0 \<omega>s)"
      by blast
  qed
  show ?thesis
    by (rule branchP_indep_closed_cover_core_of_countable_gradU_regular_value_patches
        [where W = "\<lambda>_. V" and \<Omega> = \<Omega>, OF cover])
       (use openV Vne openO reg in blast)+
qed

lemma branchP_indep_closed_cover_core_empty:
  fixes V :: "((real^2)^'n::finite) set"
  assumes empty: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) = {}"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
  unfolding branchP_indep_closed_cover_core_def empty
  by (intro exI[where x = "\<lambda>_. {}"]) simp

theorem branchP_indep_closed_cover_core_of_countable_regular_bad_angles:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> :: "(real^2) set"
  assumes countable_bad: "countable (branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>)"
    and gnz: "\<And>\<omega>. \<omega> \<in> branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> \<Longrightarrow> gain_dip \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof (cases "branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> = {}")
  case True
  show ?thesis
    by (rule branchP_indep_closed_cover_core_empty
        [OF branchP_bad_angles_empty_imp_no_BadXGW[OF True]])
next
  case False
  define om where "om = from_nat_into (branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>)"
  have bad_cover: "branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> \<subseteq> range om"
    unfolding om_def
    by (rule subset_range_from_nat_into,
        metis countable_bad top1_countable_nonempty_eq_image_nat uncountable_def)
  have om_bad: "om i \<in> branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>" for i
    unfolding om_def by (rule from_nat_into[OF False])
  define S :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "S i = V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i}" for i
  have coverS: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. S i)"
    using branchP_fixed_omega_cover_of_bad_angle_range_cover[OF bad_cover]
    unfolding S_def .
  have local_covers: "\<And>i. \<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      S i \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
  proof -
    fix i
    have core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {om i}"
      by (rule fixed_omega_H0core_chart_core_of_generic_conditions)
         (use branchP_bad_angle_cvec_nonzero[OF om_bad]
              branchP_bad_angle_Dcvec_det_nonzero[OF om_bad]
              gnz[OF om_bad] card2 in blast)+
    show "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      S i \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
      unfolding S_def
      by (rule d3_H0core_chart_core_negligible_closed_cover[OF core])
  qed
  show ?thesis
    by (rule branchP_indep_closed_cover_core_of_countable_gradU_engine_closed_covers
        [OF coverS local_covers])
qed

theorem branchP_indep_closed_cover_core_of_countable_bad_angles_in_OmegaPF:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Gamma> :: "(real^2) set"
  assumes Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and countable_bad: "countable (branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>)"
    and card2: "2 \<le> CARD('n)"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof (rule branchP_indep_closed_cover_core_of_countable_regular_bad_angles)
  show "countable (branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>)"
    by (rule countable_bad)
  show "\<And>\<omega>. \<omega> \<in> branchP_bad_angles V \<omega>0 \<omega>s \<Gamma> \<Longrightarrow> gain_dip \<omega> \<noteq> 0"
    by (rule branchP_bad_angle_gain_nonzero[OF Gsub pf])
  show "2 \<le> CARD('n)"
    by (rule card2)
qed

theorem branchP_indep_closed_cover_core_all_of_countable_bad_angles:
  fixes V :: "((real^2)^'n::finite) set"
  assumes pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and countable_bad: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
      countable (branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>)"
    and card2: "2 \<le> CARD('n)"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branchP_indep_closed_cover_core_all_def
proof (intro allI impI)
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
    by (rule branchP_indep_closed_cover_core_of_countable_bad_angles_in_OmegaPF
        [OF Gsub pf countable_bad[OF Gsub Gindep] card2])
qed

lemma branchP_indep_closed_cover_core_all_of_countable_gradU_regular_value_patches:
  fixes V :: "((real^2)^'n::finite) set"
  assumes local_patches: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
      \<exists>(W :: nat \<Rightarrow> ((real^2)^'n) set) (\<Omega> :: nat \<Rightarrow> (real^2) set).
        (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. gradU_engine_bad (W i) (\<Omega> i) \<omega>0 \<omega>s) \<and>
        (\<forall>i. open (W i)) \<and>
        (\<forall>i. W i \<noteq> {}) \<and>
        (\<forall>i. open (\<Omega> i)) \<and>
        (\<forall>i. regular_value_on
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          (W i \<times> \<Omega> i) 0)"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branchP_indep_closed_cover_core_all_def
proof (intro allI impI)
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain W :: "nat \<Rightarrow> ((real^2)^'n) set" and \<Omega> :: "nat \<Rightarrow> (real^2) set"
    where cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. gradU_engine_bad (W i) (\<Omega> i) \<omega>0 \<omega>s)"
      and openW: "\<forall>i. open (W i)"
      and Wne: "\<forall>i. W i \<noteq> {}"
      and openO: "\<forall>i. open (\<Omega> i)"
      and reg: "\<forall>i. regular_value_on
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          (W i \<times> \<Omega> i) 0"
    using local_patches[OF Gsub Gindep] by blast
  show "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
    by (rule branchP_indep_closed_cover_core_of_countable_gradU_regular_value_patches
        [OF cover])
       (use openW Wne openO reg in blast)+
qed

lemma branchP_indep_closed_cover_core_all_of_countable_steering_regular_value_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}"
    and local_covers: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
      \<exists>\<Omega> :: nat \<Rightarrow> (real^2) set.
        \<Gamma> \<subseteq> (\<Union>i. \<Omega> i) \<and>
        (\<forall>i. open (\<Omega> i)) \<and>
        (\<forall>i. regular_value_on
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          (V \<times> \<Omega> i) 0)"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branchP_indep_closed_cover_core_all_def
proof (intro allI impI)
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain \<Omega> :: "nat \<Rightarrow> (real^2) set"
    where Gcover: "\<Gamma> \<subseteq> (\<Union>i. \<Omega> i)"
      and openO: "\<forall>i. open (\<Omega> i)"
      and reg: "\<forall>i. regular_value_on
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          (V \<times> \<Omega> i) 0"
    using local_covers[OF Gsub Gindep] by blast
  show "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
    by (rule branchP_indep_closed_cover_core_of_countable_steering_regular_value_cover
        [OF openV Vne Gcover])
       (use openO reg in blast)+
qed

lemma branchP_indep_closed_cover_core_all_of_gradU_regular_value_neighbourhoods:
  fixes V :: "((real^2)^'n::finite) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}"
    and local_reg: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
      \<exists>\<Omega>. open \<Omega> \<and> \<Gamma> \<subseteq> \<Omega> \<and>
        regular_value_on
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          (V \<times> \<Omega>) 0"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branchP_indep_closed_cover_core_all_def
proof (intro allI impI)
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain \<Omega> where Oopen: "open \<Omega>" and GO: "\<Gamma> \<subseteq> \<Omega>"
    and reg: "regular_value_on
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          (V \<times> \<Omega>) 0"
    using local_reg[OF Gsub Gindep] by blast
  show "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
    by (rule branchP_indep_closed_cover_core_of_gradU_regular_value
        [OF openV Vne Oopen GO reg])
qed

section \<open>The projective covector charts (\<section>7b): \<open>Psi_a\<close> and its perp-slot value\<close>

text \<open>
  Chart A of the free cokernel covector \<open>\<lambda> = (1,a)\<close>: \<open>gradU_x_rank_defect_dip\<close> in this
  chart says \<open>x\<close> is a critical point (full \<open>x\<close>-gradient zero) of the single scalar
  \<open>Psi_a := gradU_1 + a \<cdot> gradU_2\<close>, mirroring the existing \<open>Phi_par := gradU\<bullet>e_par\<close>
  pattern with the \<open>\<omega>\<close>-derived direction \<open>e_par\<close> replaced by the free direction
  \<open>(1,a)\<close>.  See Sketch.md \<section>7b for the semi-formal derivation.
\<close>

lemma gradU_dip_component_x_has_derivative:
  fixes x :: "(real^2)^'n::finite"
  shows "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j)
      has_derivative (\<lambda>h. gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> h $ j)) (at x)"
  by (rule bounded_linear.has_derivative
        [OF bounded_linear_vec_nth gradU_x_partial_dip_has_derivative])

definition Psi_a_dip ::
  "real \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n::finite) \<Rightarrow> real^2 \<Rightarrow> real" where
  "Psi_a_dip a \<omega>0 \<omega>s x \<omega> =
     gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
     + a * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2)"

definition Psi_a_x_partial_dip ::
  "real \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n::finite) \<Rightarrow> real^2
    \<Rightarrow> (((real^2)^'n) \<Rightarrow> real)" where
  "Psi_a_x_partial_dip a \<omega>0 \<omega>s x \<omega> =
     (\<lambda>h. gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> h $ 1
        + a * (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> h $ 2))"

lemma Psi_a_dip_has_derivative:
  fixes x :: "(real^2)^'n::finite"
  shows "((\<lambda>y. Psi_a_dip a \<omega>0 \<omega>s y \<omega>)
      has_derivative Psi_a_x_partial_dip a \<omega>0 \<omega>s x \<omega>) (at x)"
  unfolding Psi_a_dip_def[abs_def] Psi_a_x_partial_dip_def
  by (auto intro!: derivative_eq_intros gradU_dip_component_x_has_derivative)

text \<open>
  The perp-slot value of \<open>Psi_a\<close>'s \<open>x\<close>-gradient, obtained by mixing the TWO
  already-proven \<open>gradU\<close>-component perp-slot values (@{thm gradU_dip_xderiv_perp_slot})
  with weights \<open>1\<close> and \<open>a\<close>.  For \<open>v\<close> perpendicular to \<open>c = cvec_dip \<omega>0 \<omega>s \<omega>\<close>, this
  vanishes identically iff EITHER every antenna is phase-aligned with \<open>A\<close>
  (\<open>Im(cnj A \<cdot> \<phi>\<^sub>m) = 0\<close> for all \<open>m\<close> -- the SAME phase-alignment condition already
  used in the D3 Bnonzero split), OR the combined direction
  \<open>Dcvec_dip(axis 1) + a\<cdot>Dcvec_dip(axis 2)\<close> is itself parallel to \<open>c\<close> (so its inner
  product against every perp \<open>v\<close> is zero).
\<close>

theorem Psi_a_dip_xderiv_perp_slot:
  fixes x :: "(real^2)^'n::finite" and v :: "real^2" and m :: 'n and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes perp: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v = 0"
  shows "Psi_a_x_partial_dip a \<omega>0 \<omega>s x \<omega> (slot m v)
       = 2 * gain_dip \<omega>
           * ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v)
              + a * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v))
           * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                 * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
proof -
  have key: "\<And>j :: 2. gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ j
      = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> v)
          * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
  proof -
    fix j :: 2
    have "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ j
        = (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
                (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) $ j"
      unfolding gradU_x_partial_dip_def by simp
    also have "\<dots> = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> v)
          * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
      using gradU_dip_xderiv_perp_slot[OF perp, where x = x and m = m]
      by (simp add: Finite_Cartesian_Product.vec_eq_iff)
    finally show "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ j
      = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> v)
          * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)" .
  qed
  have step1: "Psi_a_x_partial_dip a \<omega>0 \<omega>s x \<omega> (slot m v)
      = gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ 1
        + a * (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ 2)"
    unfolding Psi_a_x_partial_dip_def by simp
  also have step2: "\<dots>
      = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v)
          * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)
        + a * (2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v)
          * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m))"
    by (simp only: key[of 1] key[of 2])
  also have "\<dots> = 2 * gain_dip \<omega>
           * ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v)
              + a * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v))
           * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                 * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
    by (simp only: algebra_simps)
  finally show ?thesis .
qed

text \<open>
  The GENERAL (not perp-restricted) slot value of \<open>dEjm\<close>, sympy-verified in
  Sketch.md \<section>7c against the raw \<open>dEjm\<close> definition.  At \<open>c\<bullet>v=0\<close> this
  collapses to @{thm dEjm_perp_slot_value}, a consistency check on both.
\<close>

lemma dEjm_slot_value:
  fixes c v :: "real^2" and \<gamma> :: "real^2"
  shows "dEjm p g (vec_nth \<gamma> 1) (vec_nth \<gamma> 2) (M_paper x c) (DM_paper_x x c (slot m v))
       = p * (2 * (c \<bullet> v) * Im (cnj (vec_nth (M_paper x c) 1) * phase c x m))
       + g * (2 * (c \<bullet> v)
                * (vec_nth \<gamma> 1 * Re (cnj (phase c x m) * vec_nth (M_paper x c) 2)
                  + vec_nth \<gamma> 2 * Re (cnj (phase c x m) * vec_nth (M_paper x c) 3))
            + 2 * (\<gamma> \<bullet> v) * Im (cnj (vec_nth (M_paper x c) 1) * phase c x m)
            - 2 * (c \<bullet> v) * (\<gamma> \<bullet> vec_nth x m)
                * Re (cnj (vec_nth (M_paper x c) 1) * phase c x m))"
proof -
  have d1: "vec_nth (DM_paper_x x c (slot m v)) 1 = -(c \<bullet> v) *\<^sub>R (\<i> * phase c x m)"
    by (simp add: DM_paper_x_def DA_paper_eq_d_moment d_A_moment_x_slot)
  have d2: "vec_nth (DM_paper_x x c (slot m v)) 2
      = of_real (vec_nth v 1) * phase c x m
        + of_real (vec_nth (vec_nth x m) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))"
    by (simp add: DM_paper_x_def DM1_paper_eq_d_moment d_M1_moment_x_slot)
  have d3: "vec_nth (DM_paper_x x c (slot m v)) 3
      = of_real (vec_nth v 2) * phase c x m
        + of_real (vec_nth (vec_nth x m) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))"
    by (simp add: DM_paper_x_def DM2_paper_eq_d_moment d_M2_moment_x_slot)
  have raw: "dEjm p g (vec_nth \<gamma> 1) (vec_nth \<gamma> 2) (M_paper x c) (DM_paper_x x c (slot m v))
      = p * (2 * Re (vec_nth (M_paper x c) 1) * Re (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))
           + 2 * Im (vec_nth (M_paper x c) 1) * Im (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m)))
        + g * (2 * Re (cnj (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))
                * ((- \<i>) * complex_of_real (vec_nth \<gamma> 1) * vec_nth (M_paper x c) 2
                 + (- \<i>) * complex_of_real (vec_nth \<gamma> 2) * vec_nth (M_paper x c) 3)
              + cnj (vec_nth (M_paper x c) 1)
                * ((- \<i>) * complex_of_real (vec_nth \<gamma> 1)
                    * (of_real (vec_nth v 1) * phase c x m
                       + of_real (vec_nth (vec_nth x m) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m)))
                 + (- \<i>) * complex_of_real (vec_nth \<gamma> 2)
                    * (of_real (vec_nth v 2) * phase c x m
                       + of_real (vec_nth (vec_nth x m) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))))))"
    unfolding dEjm_def by (simp only: d1 d2 d3)
  show ?thesis
    unfolding raw
    by (simp add: inner_vec_def sum_2 complex_eq_iff algebra_simps)
qed

theorem gradU_dip_xderiv_slot:
  fixes x :: "(real^2)^'n::finite" and v :: "real^2" and m :: 'n and \<omega> \<omega>0 \<omega>s :: "real^2"
    and j :: 2
  shows "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ j
       = frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1)
           * (2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v)
                * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                      * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m))
         + gain_dip \<omega>
             * (2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v)
                  * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1
                       * Re (cnj (phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)
                             * vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 2)
                     + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2
                       * Re (cnj (phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)
                             * vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 3))
                + 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> v)
                    * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                          * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)
                - 2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v)
                    * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> vec_nth x m)
                    * Re (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                          * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m))"
proof -
  have "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ j
      = (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
                (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) $ j"
    unfolding gradU_x_partial_dip_def by simp
  thus ?thesis by (simp add: dEjm_slot_value)
qed

text \<open>
  The GENERAL slot value of \<open>Psi_a\<close>'s \<open>x\<close>-gradient: the \<open>(1,a)\<close>-combination of
  the two @{thm gradU_dip_xderiv_slot} rows.  Unlike the perp-only
  @{thm Psi_a_dip_xderiv_perp_slot}, this covers EVERY \<open>v\<close> (not just those
  perpendicular to \<open>c\<close>), so together with linearity in \<open>h\<close> it fully
  characterises \<open>gradU_x_rank_defect_dip\<close> in chart A.
\<close>

theorem Psi_a_dip_xderiv_slot:
  fixes x :: "(real^2)^'n::finite" and v :: "real^2" and m :: 'n and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "Psi_a_x_partial_dip a \<omega>0 \<omega>s x \<omega> (slot m v)
       = frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis 1 1) 1)
           * (2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v)
                * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                      * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m))
         + gain_dip \<omega>
             * (2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v)
                  * ((vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)) 1
                        + a * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 1)
                       * Re (cnj (phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)
                             * vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 2)
                     + (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)) 2
                        + a * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 2)
                       * Re (cnj (phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)
                             * vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 3))
                + 2 * ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v)
                       + a * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v))
                    * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                          * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)
                - 2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v)
                    * ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> vec_nth x m)
                       + a * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> vec_nth x m))
                    * Re (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                          * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m))"
proof -
  have ax20: "vec_nth (axis (2::2) 1) 1 = (0::real)"
    by (simp add: axis_def)
  have p2: "frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (2::2) 1) 1) = 0"
    by (simp only: ax20 frechet_gdip_zero_arg)
  have step1: "Psi_a_x_partial_dip a \<omega>0 \<omega>s x \<omega> (slot m v)
      = gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ 1
        + a * (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ 2)"
    unfolding Psi_a_x_partial_dip_def by simp
  show ?thesis
    unfolding step1 gradU_dip_xderiv_slot p2
    by (simp add: algebra_simps)
qed

section \<open>\<section>7e: the joint (x,\<omega>) regular-value route -- case (a), det HessU \<noteq> 0\<close>

text \<open>
  Per Sketch.md \<section>7e: @{thm branchP_indep_closed_cover_core_of_gradU_regular_value}
  (already proven, above) reduces the whole D4 target to a single hypothesis:
  \<open>0\<close> is a regular value of \<open>gradU\<close> treated as a map on the JOINT \<open>(x,\<omega>)\<close>
  space.  This is a case split at each zero of \<open>gradU\<close>.  Case (a), handled
  here: if \<open>det HessU \<noteq> 0\<close>, the \<open>\<omega>\<close>-block alone is already invertible, so
  the joint derivative is surjective regardless of the \<open>x\<close>-block.
\<close>

lemma joint_regular_of_detHessU_nonzero:
  fixes x :: "(real^2)^'n::finite" and \<omega> :: "real^2"
  assumes detH: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
  shows "\<exists>Dxw. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
        has_derivative Dxw) (at (x, \<omega>)) \<and> surj Dxw"
proof -
  have fx: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
      gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>) (at x within UNIV)"
    by (rule has_derivative_at_withinI[OF gradU_x_partial_dip_has_derivative])
  have fy: "\<And>x' \<omega>'. x' \<in> (UNIV::((real^2)^'n) set) \<Longrightarrow> \<omega>' \<in> (UNIV::(real^2) set) \<Longrightarrow>
      ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' u) has_derivative
        blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))) (at \<omega>' within UNIV)"
  proof -
    fix x' :: "(real^2)^'n" and \<omega>' :: "real^2"
    have "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' u) has_derivative
            (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>' *v v)) (at \<omega>' within UNIV)"
      by (rule has_derivative_at_withinI[OF gradU_dip_has_derivative])
    thus "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' u) has_derivative
            blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))) (at \<omega>' within UNIV)"
      by (simp only: bounded_linear_Blinfun_apply matrix_vector_mul_bounded_linear)
  qed
  have fycont: "continuous (at (x, \<omega>) within UNIV \<times> UNIV)
      (\<lambda>(x', \<omega>'). Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))"
  proof -
    have "continuous (at (x, \<omega>) within UNIV)
        (\<lambda>z. Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst z) (snd z))))"
      using continuous_on_HessU_blinfun_joint
      by (simp add: continuous_on_eq_continuous_within, blast)
    thus ?thesis by (simp only: case_prod_unfold UNIV_Times_UNIV)
  qed
  have joint: "((\<lambda>(x', \<omega>'). gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>') has_derivative
       (\<lambda>(tx, ty). gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> tx
            + blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))) ty))
     (at (x, \<omega>) within UNIV \<times> UNIV)"
    by (rule has_derivative_partialsI[OF fx fy fycont UNIV_I convex_UNIV])
  define Dxw where "Dxw = (\<lambda>p::(((real^2)^'n) \<times> (real^2)). gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (fst p)
       + HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v (snd p))"
  have joint': "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) has_derivative Dxw) (at (x, \<omega>))"
    using joint
    by (metis (no_types, lifting) ext Dxw_def UNIV_Times_UNIV cond_case_prod_eta fy prod.collapse
        gradU_dip_has_derivative has_derivative_unique iso_tuple_UNIV_I old.prod.inject)    
  have surjDxw: "surj Dxw"
  proof -
    have surjH: "surj ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
      using detH surj_matrix_vector_iff_det by blast
    have surjH': "\<exists>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v = t" for t :: "real^2"
    proof -
      from surjH obtain v where "t = (*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) v"
        by (metis surj_def)
      hence "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v = t" by simp
      thus ?thesis by blast
    qed
    have x0: "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> 0 = 0"
      using linear_0[OF gradU_x_partial_dip_linear] .
    show ?thesis
    proof (rule surjI[of Dxw "\<lambda>t. (0, SOME v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v = t)"])
      fix t :: "real^2"
      have someV: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>
          *v (SOME v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v = t) = t"
        by (rule someI_ex[of "\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v = t"])
           (use surjH' in blast)
      show "Dxw (0, SOME v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v = t) = t"
        unfolding Dxw_def using x0 someV by simp
    qed
  qed
  show ?thesis
    using joint' surjDxw by blast
qed

text \<open>
  Case (b1) (Sketch.md \<section>7f): the symmetric counterpart of case (a).  If the
  \<open>x\<close>-block ALONE (\<open>gradU_x_partial_dip\<close>, i.e. NOT \<open>BadXGW\<close>'s own
  rank-defect conjunct) is already surjective, the joint derivative is
  surjective too, regardless of \<open>HessU\<close>.  Together with case (a), this
  covers every zero of \<open>gradU\<close> EXCEPT points literally inside \<open>BadXGW\<close>
  itself (where \<open>det HessU=0\<close> AND the \<open>x\<close>-block is ALSO rank-deficient) --
  per the \<section>7f numerics, that residual locus is where the genuine
  remaining difficulty lives.
\<close>

lemma joint_regular_of_x_partial_surj:
  fixes x :: "(real^2)^'n::finite" and \<omega> :: "real^2"
  assumes surjX: "surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>)"
  shows "\<exists>Dxw. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
        has_derivative Dxw) (at (x, \<omega>)) \<and> surj Dxw"
proof -
  have fx: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
      gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>) (at x within UNIV)"
    by (rule has_derivative_at_withinI[OF gradU_x_partial_dip_has_derivative])
  have fy: "\<And>x' \<omega>'. x' \<in> (UNIV::((real^2)^'n) set) \<Longrightarrow> \<omega>' \<in> (UNIV::(real^2) set) \<Longrightarrow>
      ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' u) has_derivative
        blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))) (at \<omega>' within UNIV)"
  proof -
    fix x' :: "(real^2)^'n" and \<omega>' :: "real^2"
    have "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' u) has_derivative
            (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>' *v v)) (at \<omega>' within UNIV)"
      by (rule has_derivative_at_withinI[OF gradU_dip_has_derivative])
    thus "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' u) has_derivative
            blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))) (at \<omega>' within UNIV)"
      by (simp only: bounded_linear_Blinfun_apply matrix_vector_mul_bounded_linear)
  qed
  have fycont: "continuous (at (x, \<omega>) within UNIV \<times> UNIV)
      (\<lambda>(x', \<omega>'). Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))"
  proof -
    have "continuous (at (x, \<omega>) within UNIV)
        (\<lambda>z. Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst z) (snd z))))"
      using continuous_on_HessU_blinfun_joint
      by (simp only: continuous_on_eq_continuous_within, blast)
    thus ?thesis by (simp only: case_prod_unfold UNIV_Times_UNIV)
  qed
  have joint: "((\<lambda>(x', \<omega>'). gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>') has_derivative
       (\<lambda>(tx, ty). gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> tx
            + blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))) ty))
     (at (x, \<omega>) within UNIV \<times> UNIV)"
    by (rule has_derivative_partialsI[OF fx fy fycont UNIV_I convex_UNIV])
  define Dxw where "Dxw = (\<lambda>p::(((real^2)^'n) \<times> (real^2)). gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (fst p)
       + HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v (snd p))"
  have joint': "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) has_derivative Dxw) (at (x, \<omega>))"
    using joint
    by (metis (no_types, lifting) ext Dxw_def UNIV_Times_UNIV cond_case_prod_eta fy prod.collapse
        gradU_dip_has_derivative has_derivative_unique iso_tuple_UNIV_I old.prod.inject)
  have surjDxw: "surj Dxw"
  proof -
    have H0: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v 0 = 0"
      by simp
    show ?thesis
    proof (rule surjI[of Dxw "\<lambda>t. (SOME v. gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> v = t, 0)"])
      fix t :: "real^2"
      from surjX obtain v where v: "t = gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> v"
        by (metis surj_def)
      have someV: "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>
          (SOME v. gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> v = t) = t"
        by (rule someI_ex[of "\<lambda>v. gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> v = t"]) (use v in blast)
      show "Dxw (SOME v. gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> v = t, 0) = t"
        unfolding Dxw_def using H0 someV by simp
    qed
  qed
  show ?thesis
    using joint' surjDxw by blast
qed

section \<open>\<section>7j: the explicit aligned-residual cover (stage A: quantization)\<close>

text \<open>
  Sketch.md \<section>7j: the aligned part of \<open>BadXGW\<close> (configurations whose phases
  are all real multiples of \<open>A\<close>) is covered by countably many closed
  negligible sets, EXPLICITLY -- no genericity, no Sard, no IFT.  Stage A
  proves the quantization: at an aligned configuration with \<open>A \<noteq> 0\<close> and
  \<open>c \<noteq> 0\<close>, every antenna lies on one of the countably many phase-lines
  \<open>{y. c\<bullet>y = \<alpha> + k\<pi>}\<close>, giving the explicit parametrization by
  \<open>(\<omega>, \<alpha>, s) \<in> \<real>\<^sup>2\<times>\<real>\<times>\<real>\<^sup>n\<close> -- dimension \<open>n+3 < 2n\<close> once \<open>CARD('n) \<ge> 4\<close>.
\<close>

definition aligned_conf :: "((real^2)^'n::finite) \<Rightarrow> (real^2) \<Rightarrow> bool" where
  "aligned_conf x c \<longleftrightarrow> (\<forall>m. Im (cnj (A_moment x c) * phase c x m) = 0)"

lemma perp2_self_inner: "perp2 c \<bullet> perp2 c = c \<bullet> c"
  unfolding perp2_def
  by (simp add: inner_vec_def sum_2 vector_2 power2_eq_square)

lemma lagrange2:
  fixes c w :: "real^2"
  shows "(c \<bullet> c) * (w \<bullet> w) = (c \<bullet> w)^2 + (perp2 c \<bullet> w)^2"
  unfolding perp2_def
  by (simp add: inner_vec_def sum_2 vector_2 power2_eq_square algebra_simps)

lemma perp2_decomp2:
  fixes c v :: "real^2"
  assumes cnz: "c \<noteq> 0"
  shows "v = ((c \<bullet> v)/(c \<bullet> c)) *\<^sub>R c + ((perp2 c \<bullet> v)/(c \<bullet> c)) *\<^sub>R perp2 c"
proof -
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz by simp
  define w where
    "w = v - ((c \<bullet> v)/(c \<bullet> c)) *\<^sub>R c - ((perp2 c \<bullet> v)/(c \<bullet> c)) *\<^sub>R perp2 c"
  have orth1: "c \<bullet> w = 0"
    unfolding w_def
    using ccnz
    by (simp add: inner_diff_right perp2_orth)
  have orth2: "perp2 c \<bullet> w = 0"
  proof -
    have pc: "perp2 c \<bullet> c = 0"
      using perp2_orth inner_commute by metis
    show ?thesis
      unfolding w_def
      using ccnz
      by (simp add: inner_diff_right perp2_self_inner pc)
  qed
  have "(c \<bullet> c) * (w \<bullet> w) = 0"
    using lagrange2[of c w] orth1 orth2 by simp
  hence "w \<bullet> w = 0"
    using ccnz by simp
  hence "w = 0"
    by simp
  thus ?thesis
    unfolding w_def
    by (metis add.commute add.right_neutral diff_add_cancel)
qed

lemma aligned_relation:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  assumes al: "aligned_conf x c"
  shows "Re (A_moment x c) * sin (c \<bullet> vec_nth x m)
       + Im (A_moment x c) * cos (c \<bullet> vec_nth x m) = 0"
proof -
  have ph: "phase c x m = cis (- (c \<bullet> vec_nth x m))"
    by (simp add: phase_def)
  have base: "Im (cnj (A_moment x c) * phase c x m) = 0"
    using al unfolding aligned_conf_def by blast
  have "Im (cnj (A_moment x c) * cis (- (c \<bullet> vec_nth x m))) = 0"
    using base unfolding ph .
  moreover have "Im (cnj (A_moment x c) * cis (- (c \<bullet> vec_nth x m)))
      = Re (A_moment x c) * sin (- (c \<bullet> vec_nth x m))
        - Im (A_moment x c) * cos (- (c \<bullet> vec_nth x m))"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma aligned_pairwise_sin_zero:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  assumes Anz: "A_moment x c \<noteq> 0" and al: "aligned_conf x c"
  shows "sin (c \<bullet> vec_nth x m - c \<bullet> vec_nth x m') = 0"
proof -
  define rA where "rA = Re (A_moment x c)"
  define iA where "iA = Im (A_moment x c)"
  define t where "t q = c \<bullet> vec_nth x q" for q :: 'n
  have rel: "rA * sin (t q) + iA * cos (t q) = 0" for q
    unfolding rA_def iA_def t_def by (rule aligned_relation[OF al])
  have rzero: "rA * sin (t m - t m') = 0"
  proof -
    have "rA * sin (t m - t m')
        = (rA * sin (t m)) * cos (t m') - cos (t m) * (rA * sin (t m'))"
      by (simp add: sin_diff algebra_simps)
    also have "\<dots> = (- iA * cos (t m)) * cos (t m') - cos (t m) * (- iA * cos (t m'))"
      using rel[of m] rel[of m'] by (simp add: algebra_simps, 
          smt (verit) Groups.mult_ac(2) calculation mult_eq_0_iff mult_minus_left sin_diff
          vector_space_over_itself.scale_left_commute)
    also have "\<dots> = 0"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have izero: "iA * sin (t m - t m') = 0"
  proof -
    have "iA * sin (t m - t m')
        = sin (t m) * (iA * cos (t m')) - (iA * cos (t m)) * sin (t m')"
      by (simp add: sin_diff algebra_simps)
    also have "\<dots> = sin (t m) * (- rA * sin (t m')) - (- rA * sin (t m)) * sin (t m')"
      using rel[of m] rel[of m'] by (simp add: algebra_simps,
          smt (verit, ccfv_threshold) Groups.mult_ac(2) mult_eq_0_iff rzero sin_diff)
    also have "\<dots> = 0"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have "rA \<noteq> 0 \<or> iA \<noteq> 0"
    using Anz unfolding rA_def iA_def by (metis complex.expand zero_complex.simps)
  thus ?thesis
    using rzero izero unfolding t_def by auto
qed

lemma aligned_quantization:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  assumes cnz: "c \<noteq> 0" and Anz: "A_moment x c \<noteq> 0" and al: "aligned_conf x c"
  obtains k :: "'n \<Rightarrow> int" and \<alpha> :: real and s :: "real^'n"
  where "\<alpha> \<in> {0..pi}"
    and "\<And>m. vec_nth x m
        = ((\<alpha> + of_int (k m) * pi)/(c \<bullet> c)) *\<^sub>R c + (vec_nth s m) *\<^sub>R perp2 c"
proof -
  define t where "t q = c \<bullet> vec_nth x q" for q :: 'n
  define m0 where "m0 = (SOME q :: 'n. True)"
  have step: "\<exists>i::int. t q - t m0 = of_int i * pi" for q
    using aligned_pairwise_sin_zero[OF Anz al, of q m0]
    unfolding t_def by (simp add: sin_zero_iff_int2)
  define i where "i q = (SOME j::int. t q - t m0 = of_int j * pi)" for q
  have ieq: "t q - t m0 = of_int (i q) * pi" for q
    unfolding i_def by (rule someI_ex[OF step])
  define quo where "quo = floor (t m0 / pi)"
  define \<alpha> where "\<alpha> = t m0 - of_int quo * pi"
  have alo: "0 \<le> \<alpha>"
  proof -
    have "of_int quo \<le> t m0 / pi"
      unfolding quo_def by (rule of_int_floor_le)
    hence "of_int quo * pi \<le> t m0"
      using pi_gt_zero by (simp add: pos_le_divide_eq mult.commute)
    thus ?thesis unfolding \<alpha>_def by simp
  qed
  have ahi: "\<alpha> \<le> pi"
  proof -
    have "t m0 / pi < of_int quo + 1"
      unfolding quo_def by auto 
    hence "t m0 < (of_int quo + 1) * pi"
      using pi_gt_zero by (simp add: pos_divide_less_eq mult.commute)
    thus ?thesis unfolding \<alpha>_def by (simp add: algebra_simps)
  qed
  define k where "k q = i q + quo" for q
  have teq: "t q = \<alpha> + of_int (k q) * pi" for q
    using ieq[of q] unfolding \<alpha>_def k_def by (simp add: algebra_simps)
  define s where "s = (\<chi> q. (perp2 c \<bullet> vec_nth x q)/(c \<bullet> c))"
  have xeq: "vec_nth x q
      = ((\<alpha> + of_int (k q) * pi)/(c \<bullet> c)) *\<^sub>R c + (vec_nth s q) *\<^sub>R perp2 c" for q
  proof -
    have "vec_nth x q = ((c \<bullet> vec_nth x q)/(c \<bullet> c)) *\<^sub>R c
        + ((perp2 c \<bullet> vec_nth x q)/(c \<bullet> c)) *\<^sub>R perp2 c"
      by (rule perp2_decomp2[OF cnz])
    thus ?thesis
      using teq[of q] unfolding t_def s_def by simp
  qed
  show thesis
    by (rule that[of \<alpha> k s]) (use alo ahi xeq in auto)
qed

lemma A_moment_nz_of_A_cart:
  assumes "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
  shows "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0"
  using assms by (simp add: A_cart_eq_Afun Afun_eq_A_moment)

section \<open>\<section>7j stage B: the parametrization maps and their closed negligible images\<close>

definition align_param_map ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> ('n::finite \<Rightarrow> int)
    \<Rightarrow> ((real^2) \<times> real \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)" where
  "align_param_map \<omega>0 \<omega>s k p =
     (\<chi> m. ((fst (snd p) + of_int (k m) * pi)
              /(cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)))
             *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst p)
           + (vec_nth (snd (snd p)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst p)))"

definition align_dom ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat
    \<Rightarrow> ((real^2) \<times> real \<times> (real^('n::finite))) set" where
  "align_dom \<omega>0 \<omega>s K0 j = {p. fst p \<in> K0
      \<and> 1/real (Suc j) \<le> cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)
      \<and> fst (snd p) \<in> {0..pi}
      \<and> snd (snd p) \<in> cball 0 (real j)}"

lemma bounded_linear_perp2: "bounded_linear perp2"
proof (rule bounded_linear_intro[of perp2 1])
  show "\<And>x y. perp2 (x + y) = perp2 x + perp2 y"
    unfolding perp2_def
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2)
  show "\<And>r x. perp2 (r *\<^sub>R x) = r *\<^sub>R perp2 x"
    unfolding perp2_def
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2)
  show "\<And>x. norm (perp2 x) \<le> norm x * 1"
    by (simp add: norm_eq_sqrt_inner perp2_self_inner)
qed

lemma bounded_linear_axis:
  fixes m :: "'k::finite"
  shows "bounded_linear (axis m :: real^2 \<Rightarrow> (real^2)^'k)"
proof (rule bounded_linear_intro[of _ 1])
  fix x y :: "real^2"
  show "axis m (x + y) = axis m x + axis m y"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 'k
    show "vec_nth (axis m (x + y)) i = vec_nth (axis m x + axis m y) i"
    proof (cases "i = m")
      case True
      thus ?thesis by (simp add: axis_def)
    next
      case False
      have l: "vec_nth (axis m (x + y)) i = (0::real^2)"
        using False by (simp add: axis_def)
      have r: "vec_nth (axis m x + axis m y) i = (0::real^2) + (0::real^2)"
        using False by (simp add: axis_def)
      show ?thesis
        unfolding l r by simp
    qed
  qed
next
  fix r :: real and x :: "real^2"
  show "axis m (r *\<^sub>R x) = r *\<^sub>R axis m x"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 'k
    show "vec_nth (axis m (r *\<^sub>R x)) i = vec_nth (r *\<^sub>R axis m x) i"
    proof (cases "i = m")
      case True
      thus ?thesis by (simp add: axis_def)
    next
      case False
      have l: "vec_nth (axis m (r *\<^sub>R x)) i = (0::real^2)"
        using False by (simp add: axis_def)
      have r2: "vec_nth (r *\<^sub>R axis m x) i = r *\<^sub>R (0::real^2)"
        using False by (simp add: axis_def)
      show ?thesis
        unfolding l r2 by simp
    qed
  qed
next
  fix x :: "real^2"
  have "(axis m x :: (real^2)^'k) \<bullet> axis m x
      = (\<Sum>i\<in>UNIV. vec_nth (axis m x :: (real^2)^'k) i
           \<bullet> vec_nth (axis m x :: (real^2)^'k) i)"
    by (simp add: inner_vec_def)
  also have "\<dots> = (\<Sum>i\<in>(UNIV::'k set). if i = m then x \<bullet> x else 0)"
    by (rule sum.cong[OF refl]) (simp add: axis_def)
  also have "\<dots> = x \<bullet> x"
    by (simp add: sum.delta)
  finally have "(axis m x :: (real^2)^'k) \<bullet> axis m x = x \<bullet> x" .
  thus "norm (axis m x :: (real^2)^'k) \<le> norm x * 1"
    by (simp add: norm_eq_sqrt_inner)
qed

lemma vec_lambda_eq_sum_axis:
  fixes F :: "'k::finite \<Rightarrow> 'a::real_normed_vector"
  shows "(\<chi> m. F m) = (\<Sum>m\<in>UNIV. axis m (F m))"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix i :: 'k
  have "vec_nth (\<Sum>m\<in>UNIV. axis m (F m)) i = (\<Sum>m\<in>UNIV. vec_nth (axis m (F m)) i)"
    by simp
  also have "\<dots> = (\<Sum>m\<in>UNIV. if m = i then F m else 0)"
    by (rule sum.cong[OF refl]) (simp add: axis_def)
  also have "\<dots> = F i"
    by (simp add: sum.delta)
  finally show "vec_nth (\<chi> m. F m) i = vec_nth (\<Sum>m\<in>UNIV. axis m (F m)) i"
    by simp
qed

lemma align_dom_denom_pos:
  assumes "p \<in> align_dom \<omega>0 \<omega>s K0 j"
  shows "cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p) \<noteq> 0"
proof -
  have "(0::real) < 1/real (Suc j)" by simp
  moreover have "1/real (Suc j) \<le> cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)"
    using assms unfolding align_dom_def by blast
  ultimately show ?thesis by linarith
qed

lemma cvec_fst_differentiable:
  fixes S :: "((real^2) \<times> real \<times> (real^('n::finite))) set"
    and p :: "(real^2) \<times> real \<times> (real^'n)"
  shows "(\<lambda>q. cvec_dip \<omega>0 \<omega>s (fst q)) differentiable (at p within S)"
proof -
  have c: "cvec_dip \<omega>0 \<omega>s differentiable (at (fst p))"
    using has_derivative_cvec_dip differentiable_def by blast
  have f: "fst differentiable (at p within S)"
    by (simp add: bounded_linear_imp_differentiable bounded_linear_fst)
  have "(cvec_dip \<omega>0 \<omega>s \<circ> fst) differentiable (at p within S)"
    by (rule differentiable_chain_within[OF f differentiable_at_withinI[OF c]])
  thus ?thesis by (simp add: o_def)
qed

lemma align_param_map_differentiable_on:
  fixes k :: "'n::finite \<Rightarrow> int"
  shows "align_param_map \<omega>0 \<omega>s k differentiable_on
      (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^'n)) set)"
proof -
  define D where "D = (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^'n)) set)"
  have comp: "(\<lambda>p. axis m (((fst (snd p) + of_int (k m) * pi)
              /(cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)))
             *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst p)
           + (vec_nth (snd (snd p)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst p))))
      differentiable (at p within D)"
    if pin: "p \<in> D" for m and p :: "(real^2) \<times> real \<times> (real^'n)"
  proof -
    have cd: "(\<lambda>q. cvec_dip \<omega>0 \<omega>s (fst q))
        differentiable (at p within D)"
      by (rule cvec_fst_differentiable)
    have bl_alph: "bounded_linear (\<lambda>q::((real^2) \<times> real \<times> (real^'n)). fst (snd q))"
      by (rule bounded_linear_compose[OF bounded_linear_fst bounded_linear_snd])
    have alph: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)). fst (snd q))
        differentiable (at p within D)"
      by (rule bounded_linear_imp_differentiable[OF bl_alph])
    have bl_ss: "bounded_linear (\<lambda>q::((real^2) \<times> real \<times> (real^'n)). snd (snd q))"
      by (rule bounded_linear_compose[OF bounded_linear_snd bounded_linear_snd])
    have bl_sm: "bounded_linear (\<lambda>q::((real^2) \<times> real \<times> (real^'n)). vec_nth (snd (snd q)) m)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth bl_ss])
    have sm: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)). vec_nth (snd (snd q)) m)
        differentiable (at p within D)"
      by (rule bounded_linear_imp_differentiable[OF bl_sm])
    have dnz: "cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p) \<noteq> 0"
      using align_dom_denom_pos pin unfolding D_def by blast
    have inner_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)).
          cvec_dip \<omega>0 \<omega>s (fst q) \<bullet> cvec_dip \<omega>0 \<omega>s (fst q))
        differentiable (at p within D)"
      by (rule differentiable_inner[OF cd cd])
    have perp_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)). perp2 (cvec_dip \<omega>0 \<omega>s (fst q)))
        differentiable (at p within D)"
    proof -
      have "(perp2 \<circ> (\<lambda>q::((real^2) \<times> real \<times> (real^'n)). cvec_dip \<omega>0 \<omega>s (fst q)))
          differentiable (at p within D)"
        by (rule differentiable_chain_within[OF cd
              bounded_linear_imp_differentiable[OF bounded_linear_perp2]])
      thus ?thesis by (simp add: o_def)
    qed
    have numer_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)). fst (snd q) + of_int (k m) * pi)
        differentiable (at p within D)"
      by (rule differentiable_add[OF alph differentiable_const])
    have quot_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)).
          (fst (snd q) + of_int (k m) * pi)
            /(cvec_dip \<omega>0 \<omega>s (fst q) \<bullet> cvec_dip \<omega>0 \<omega>s (fst q)))
        differentiable (at p within D)"
      by (rule differentiable_divide[OF numer_d inner_d dnz])
    have sc1_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)).
          ((fst (snd q) + of_int (k m) * pi)
            /(cvec_dip \<omega>0 \<omega>s (fst q) \<bullet> cvec_dip \<omega>0 \<omega>s (fst q)))
           *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst q))
        differentiable (at p within D)"
      by (rule differentiable_scaleR[OF quot_d cd])
    have sc2_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)).
          (vec_nth (snd (snd q)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst q)))
        differentiable (at p within D)"
      by (rule differentiable_scaleR[OF sm perp_d])
    have core: "(\<lambda>p. ((fst (snd p) + of_int (k m) * pi)
              /(cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)))
             *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst p)
           + (vec_nth (snd (snd p)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst p)))
        differentiable (at p within D)"
      by (rule differentiable_add[OF sc1_d sc2_d])
    show ?thesis
      using differentiable_chain_within[OF core
            bounded_linear_imp_differentiable[OF bounded_linear_axis]]
      by (simp add: o_def)
  qed
  have eq: "align_param_map \<omega>0 \<omega>s k
      = (\<lambda>p. \<Sum>m\<in>UNIV. axis m (((fst (snd p) + of_int (k m) * pi)
              /(cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)))
             *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst p)
           + (vec_nth (snd (snd p)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst p))))"
    unfolding align_param_map_def
    by (rule ext) (rule vec_lambda_eq_sum_axis)
  have "align_param_map \<omega>0 \<omega>s k differentiable_on D"
    unfolding eq differentiable_on_def
    by (intro ballI differentiable_sum comp, simp_all) 
  thus ?thesis
    unfolding D_def .
qed

lemma align_param_map_continuous_on:
  "continuous_on (align_dom \<omega>0 \<omega>s K0 j) (align_param_map \<omega>0 \<omega>s k)"
  by (rule differentiable_imp_continuous_on[OF align_param_map_differentiable_on])

lemma compact_align_dom:
  assumes K0c: "compact K0"
  shows "compact (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^('n::finite))) set)"
proof -
  have eq: "(align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^'n)) set)
      = (K0 \<times> {0..pi} \<times> cball 0 (real j))
        \<inter> {p. 1/real (Suc j)
            \<le> cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)}"
    unfolding align_dom_def by (auto simp: mem_Times_iff)
  have cpt: "compact ((K0 \<times> {0..pi} \<times> cball 0 (real j))
      :: ((real^2) \<times> real \<times> (real^'n)) set)"
    by (intro compact_Times K0c compact_Icc compact_cball)
  have cont: "continuous_on (UNIV :: ((real^2) \<times> real \<times> (real^'n)) set)
      (\<lambda>p. cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p))"
    by (intro continuous_on_inner
          continuous_on_compose2[OF continuous_on_cvec_dip
            continuous_on_fst[OF continuous_on_id] subset_UNIV])
  have cls: "closed {p :: ((real^2) \<times> real \<times> (real^'n)).
      1/real (Suc j) \<le> cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)}"
    by (intro closed_Collect_le continuous_on_const cont)
  show ?thesis
    unfolding eq by (rule compact_Int_closed[OF cpt cls])
qed

lemma align_image_closed:
  assumes K0c: "compact K0"
  shows "closed (align_param_map \<omega>0 \<omega>s k
      ` (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^('n::finite))) set))"
  by (intro compact_imp_closed compact_continuous_image
        align_param_map_continuous_on compact_align_dom K0c)

lemma align_image_negligible:
  assumes card4: "4 \<le> CARD('n::finite)"
  shows "negligible (align_param_map \<omega>0 \<omega>s k
      ` (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^'n)) set))"
proof (rule negligible_differentiable_image_lowdim)
  show "DIM((real^2) \<times> real \<times> (real^'n)) < DIM((real^2)^'n)"
    using card4 by simp
  show "align_param_map \<omega>0 \<omega>s k differentiable_on align_dom \<omega>0 \<omega>s K0 j"
    by (rule align_param_map_differentiable_on)
qed

lemma aligned_in_align_param_image:
  fixes x :: "(real^2)^'n::finite" and \<omega> :: "real^2"
  assumes wK0: "\<omega> \<in> K0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and Anz: "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0"
    and al: "aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)"
  shows "\<exists>(k::'n \<Rightarrow> int) (j::nat).
      x \<in> align_param_map \<omega>0 \<omega>s k ` align_dom \<omega>0 \<omega>s K0 j"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  obtain k :: "'n \<Rightarrow> int" and \<alpha> :: real and s :: "real^'n"
    where arange: "\<alpha> \<in> {0..pi}"
      and xeq: "\<And>m. vec_nth x m
        = ((\<alpha> + of_int (k m) * pi)/(c \<bullet> c)) *\<^sub>R c + (vec_nth s m) *\<^sub>R perp2 c"
    using aligned_quantization[OF cnz[folded c_def] Anz[folded c_def] al[folded c_def]]
    by metis
  have ccpos: "0 < c \<bullet> c"
    using cnz unfolding c_def by (metis inner_gt_zero_iff)
  obtain j1 :: nat where j1: "inverse (real (Suc j1)) < c \<bullet> c"
    using reals_Archimedean[OF ccpos] by blast
  obtain j2 :: nat where j2: "norm s \<le> real j2"
    using real_arch_simple by blast
  define j where "j = max j1 j2"
  have denom_ok: "1/real (Suc j) \<le> c \<bullet> c"
  proof -
    have "1/real (Suc j) \<le> 1/real (Suc j1)"
      unfolding j_def by (simp only: frac_le)
    also have "\<dots> < c \<bullet> c"
      using j1 by (simp only: inverse_eq_divide)
    finally show ?thesis by linarith
  qed
  have s_ok: "s \<in> cball 0 (real j)"
    using j2 unfolding j_def by (simp add: dist_norm)
  define p where "p = (\<omega>, \<alpha>, s)"
  have pin: "p \<in> align_dom \<omega>0 \<omega>s K0 j"
    unfolding align_dom_def p_def
    using wK0 denom_ok arange s_ok unfolding c_def by simp
  have "align_param_map \<omega>0 \<omega>s k p = x"
    unfolding align_param_map_def p_def
    by (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
      (simp add: c_def[symmetric] xeq[symmetric])
  thus ?thesis
    using pin by (metis imageI)
qed

section \<open>\<section>7j stage C: countable assembly and the conditional Branch-P core\<close>

theorem aligned_bad_closed_cover:
  fixes \<omega>0 \<omega>s :: "real^2" and K0 :: "(real^2) set"
  assumes card4: "4 \<le> CARD('n::finite)"
    and K0c: "compact K0"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      {x. \<exists>\<omega>\<in>K0. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
            \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)} \<subseteq> (\<Union>n. K n)
    \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  have cnt: "Countable_Set.countable (UNIV :: (('n \<Rightarrow> int) \<times> nat) set)"
    by (rule countableI_type)
  have ne: "(UNIV :: (('n \<Rightarrow> int) \<times> nat) set) \<noteq> {}"
    by blast
  define enum where "enum = from_nat_into (UNIV :: (('n \<Rightarrow> int) \<times> nat) set)"
  have enum_surj: "range enum = (UNIV :: (('n \<Rightarrow> int) \<times> nat) set)"
    unfolding enum_def by (rule range_from_nat_into[OF ne cnt])
  define K :: "nat \<Rightarrow> ((real^2)^'n) set" where
    "K n = align_param_map \<omega>0 \<omega>s (fst (enum n))
        ` align_dom \<omega>0 \<omega>s K0 (snd (enum n))" for n
  have closedK: "closed (K n)" for n
    unfolding K_def by (rule align_image_closed[OF K0c])
  have negK: "negligible (K n)" for n
    unfolding K_def by (rule align_image_negligible[OF card4])
  have cover: "{x. \<exists>\<omega>\<in>K0. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
        \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
        \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)} \<subseteq> (\<Union>n. K n)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x. \<exists>\<omega>\<in>K0. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
        \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
        \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}"
    then obtain \<omega> where wK0: "\<omega> \<in> K0"
      and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
      and Anz: "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0"
      and al: "aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)"
      by blast
    obtain k :: "'n \<Rightarrow> int" and j :: nat
      where img: "x \<in> align_param_map \<omega>0 \<omega>s k ` align_dom \<omega>0 \<omega>s K0 j"
      using aligned_in_align_param_image[OF wK0 cnz Anz al] by blast
    obtain n where "enum n = (k, j)"
      using enum_surj by (metis UNIV_I imageE)
    hence "x \<in> K n"
      unfolding K_def using img by simp
    thus "x \<in> (\<Union>n. K n)" by blast
  qed
  show ?thesis
    using cover closedK negK by blast
qed

theorem branchP_indep_closed_cover_core_of_nonaligned_cover:
  fixes V :: "((real^2)^'n::finite) set" and \<Gamma> :: "(real^2) set"
  assumes card4: "4 \<le> CARD('n)"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and NA: "\<exists>KN :: nat \<Rightarrow> ((real^2)^'n) set.
        {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
            \<and> \<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}
          \<subseteq> (\<Union>n. KN n)
        \<and> (\<forall>n. closed (KN n)) \<and> (\<forall>n. negligible (KN n))"
  shows "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
proof -
  have exKA: "\<exists>KA :: nat \<Rightarrow> ((real^2)^'n) set.
      {x. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
            \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)} \<subseteq> (\<Union>n. KA n)
      \<and> (\<forall>n. closed (KA n)) \<and> (\<forall>n. negligible (KA n))"
    by (rule aligned_bad_closed_cover[OF card4 OmegaPF_compact])
  obtain KA :: "nat \<Rightarrow> ((real^2)^'n) set"
    where coverA: "{x. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
            \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)} \<subseteq> (\<Union>n. KA n)"
      and closedA: "\<forall>n. closed (KA n)"
      and negA: "\<forall>n. negligible (KA n)"
    using exKA by blast
  obtain KN :: "nat \<Rightarrow> ((real^2)^'n) set"
    where coverN: "{x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
            \<and> \<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}
          \<subseteq> (\<Union>n. KN n)"
      and closedN: "\<forall>n. closed (KN n)"
      and negN: "\<forall>n. negligible (KN n)"
    using NA by blast
  define K2 :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set" where
    "K2 i j = (if i = 0 then KA j else KN j)" for i j
  have coverB: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. \<Union>j. K2 i j)"
  proof
    fix x :: "(real^2)^'n"
    assume xbad: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
    have xV: "x \<in> V" using xbad by simp
    obtain \<omega> where wG: "\<omega> \<in> \<Gamma>" and xsingle: "x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}"
      using xbad unfolding BadXGW_def by blast
    show "x \<in> (\<Union>i. \<Union>j. K2 i j)"
    proof (cases "aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)")
      case True
      have cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
        using xsingle unfolding BadXGW_def by blast
      have Acnz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
        using xsingle unfolding BadXGW_def by blast
      have Anz: "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0"
        by (rule A_moment_nz_of_A_cart[OF Acnz])
      have wPF: "\<omega> \<in> OmegaPF ctr \<delta>"
        using wG Gsub by blast
      have "x \<in> {x. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
            \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}"
        using wPF cnz Anz True by blast
      then obtain n where "x \<in> KA n"
        using coverA by blast
      hence "x \<in> K2 0 n"
        unfolding K2_def by simp
      thus ?thesis by blast
    next
      case False
      have "x \<in> {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
            \<and> \<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}"
        using xV wG xsingle False by blast
      then obtain n where "x \<in> KN n"
        using coverN by blast
      hence "x \<in> K2 1 n"
        unfolding K2_def by simp
      thus ?thesis by blast
    qed
  qed
  have closedK2: "closed (K2 i j)" for i j
    unfolding K2_def using closedA closedN by simp
  have negK2: "negligible (K2 i j)" for i j
    unfolding K2_def using negA negN by simp
  show ?thesis
    by (rule branchP_indep_closed_cover_core_of_countable_closed_covers
        [OF coverB closedK2 negK2])
qed

text \<open>
  The quantified (capstone-facing) form: the ONLY remaining hypothesis for
  D4's \<open>branchP_indep_closed_cover_core_all\<close> is now the NON-aligned cover
  (Sketch.md \<section>7j / task \<open>#14\<close>: empirically empty, lives on the branch-2
  locus).  The aligned residual -- including the \<section>7j irregular sub-locus
  where the joint Jacobian genuinely drops rank -- is handled UNCONDITIONALLY
  by the explicit phase-line parametrization above.
\<close>

theorem branchP_indep_closed_cover_core_all_of_nonaligned_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and NA: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>KN :: nat \<Rightarrow> ((real^2)^'n) set.
          {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
              \<and> \<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}
            \<subseteq> (\<Union>n. KN n)
          \<and> (\<forall>n. closed (KN n)) \<and> (\<forall>n. negligible (KN n))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branchP_indep_closed_cover_core_all_def
proof (intro allI impI)
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
    by (rule branchP_indep_closed_cover_core_of_nonaligned_cover
        [OF card4 Gsub NA[OF Gsub Gindep]])
qed

section \<open>\<section>7k/\<section>7l: the non-aligned dichotomy -- rank defect off the aligned
locus forces the SPECIAL covector (the branch-2 locus)\<close>

text \<open>
  Sketch.md \<section>7g/\<section>7k formalized.  At a non-aligned rank-defect point, the
  cokernel covector \<open>ell\<close> of the \<open>x\<close>-block must satisfy
  \<open>(ell\<^sub>1\<gamma>\<^sub>1+ell\<^sub>2\<gamma>\<^sub>2) \<bullet> perp2 c = 0\<close> (the "special covector" condition,
  \<open>ell\<^sub>1\<gamma>\<^sub>1+ell\<^sub>2\<gamma>\<^sub>2 \<parallel> c\<close>), because the perp-slot directions collapse the
  \<open>x\<close>-block onto multiples of \<open>Im(cnj A\<cdot>\<phi>_m)\<close> -- nonzero at some antenna by
  non-alignment.  This turns task \<open>#14\<close>'s hypothesis into a cover of the
  EXPLICIT locus \<open>branch2_locus\<close> (numerically empty at generic \<omega>, \<section>7k).
\<close>

definition branch2_locus ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n::finite) set" where
  "branch2_locus \<omega>0 \<omega>s \<omega> = {x. \<exists>ell::real^2. ell \<noteq> 0
      \<and> (vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0
      \<and> (\<forall>m. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>
              (slot m (cvec_dip \<omega>0 \<omega>s \<omega>)) = 0)}"

lemma gradU_x_partial_perp_slot:
  fixes x :: "(real^2)^'n::finite" and v :: "real^2" and m :: 'n
    and j :: 2
  assumes perp: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v = 0"
  shows "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ j
       = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> v)
           * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                 * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
proof -
  have "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m v) $ j
      = (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
                (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) $ j"
    unfolding gradU_x_partial_dip_def by simp
  also have "\<dots> = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> v)
        * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
              * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
    using gradU_dip_xderiv_perp_slot[OF perp, where x = x and m = m]
    by (simp add: Finite_Cartesian_Product.vec_eq_iff)
  finally show ?thesis .
qed

lemma cokernel_perp_slot_alignment_link:
  fixes x :: "(real^2)^'n::finite" and ell :: "real^2" and m :: 'n
  shows "ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
       = 2 * gain_dip \<omega>
           * ((vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
               + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
                \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
           * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                 * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
proof -
  have p: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    by (rule perp2_orth)
  have comp: "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) $ j
       = 2 * gain_dip \<omega>
           * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
           * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                 * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)" for j :: 2
    by (rule gradU_x_partial_perp_slot[OF p])
  have "ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> (slot m (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
      = vec_nth ell 1 * (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>
            (slot m (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) $ 1)
        + vec_nth ell 2 * (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>
            (slot m (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) $ 2)"
    by (simp add: inner_vec_def sum_2)
  also have "\<dots> = 2 * gain_dip \<omega>
      * (vec_nth ell 1 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
         + vec_nth ell 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
      * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
            * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
    unfolding comp by (simp add: algebra_simps)
  also have "vec_nth ell 1 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
         + vec_nth ell 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
      = (vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)"
    by (simp add: inner_add_left algebra_simps)
  finally show ?thesis .
qed

theorem nonaligned_rank_defect_in_branch2_locus:
  fixes x :: "(real^2)^'n::finite" and \<omega> :: "real^2"
  assumes cok: "gradU_x_cokernel_covector_dip \<omega>0 \<omega>s x \<omega> ell"
    and nal: "\<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)"
    and gnz: "gain_dip \<omega> \<noteq> 0"
  shows "x \<in> branch2_locus \<omega>0 \<omega>s \<omega>"
proof -
  have lnz: "ell \<noteq> 0"
    and kill: "\<And>h. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> h = 0"
    using cok unfolding gradU_x_cokernel_covector_dip_def by auto
  obtain m0 :: 'n where
    Imnz: "Im (cnj (A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>))
        * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m0) \<noteq> 0"
    using nal unfolding aligned_conf_def by blast
  have Imnz': "Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
        * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m0) \<noteq> 0"
    using Imnz by simp
  have "2 * gain_dip \<omega>
      * ((vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
          + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
           \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
      * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
            * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m0) = 0"
    using kill[of "slot m0 (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))"]
    unfolding cokernel_perp_slot_alignment_link .
  hence special: "(vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
      + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
       \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    using gnz Imnz' by auto
  have E1: "\<forall>m. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>
      (slot m (cvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
    using kill by blast
  show ?thesis
    unfolding branch2_locus_def
    using lnz special E1 by blast
qed

text \<open>
  The sharpened capstone: D4's remaining hypothesis is a countable closed
  negligible cover of \<open>BadXGW \<inter> branch2_locus\<close> -- an explicit locus cut by
  the special-covector equations, with no alignment-negation left in the
  statement.  Per \<section>7k this locus is numerically EMPTY at generic \<omega> (the
  \<open>(n+1)\<close>-in-\<open>n\<close> overdetermination of its \<open>t\<close>-sector).
\<close>

theorem branchP_indep_closed_cover_core_all_of_branch2_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and NA2: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>KN :: nat \<Rightarrow> ((real^2)^'n) set.
          {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
              \<and> x \<in> branch2_locus \<omega>0 \<omega>s \<omega>}
            \<subseteq> (\<Union>n. KN n)
          \<and> (\<forall>n. closed (KN n)) \<and> (\<forall>n. negligible (KN n))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_nonaligned_covers[OF card4])
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain KN :: "nat \<Rightarrow> ((real^2)^'n) set"
    where coverB2: "{x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
            \<and> x \<in> branch2_locus \<omega>0 \<omega>s \<omega>}
          \<subseteq> (\<Union>n. KN n)"
      and closedB2: "\<forall>n. closed (KN n)"
      and negB2: "\<forall>n. negligible (KN n)"
    using NA2[OF Gsub Gindep] by blast
  have sub: "{x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
        \<and> \<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}
      \<subseteq> {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
        \<and> x \<in> branch2_locus \<omega>0 \<omega>s \<omega>}"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
        \<and> \<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}"
    then obtain \<omega> where xV: "x \<in> V" and wG: "\<omega> \<in> \<Gamma>"
      and xbad: "x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}"
      and nal: "\<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)"
      by blast
    have rdfail: "\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx) (at x) \<and> surj Dx)"
      using xbad unfolding BadXGW_def by blast
    obtain ell where cok: "gradU_x_cokernel_covector_dip \<omega>0 \<omega>s x \<omega> ell"
      using BadXGW_x_derivative_failure_iff_cokernel_covector[THEN iffD1, OF rdfail]
      by blast
    have gnz: "gain_dip \<omega> \<noteq> 0"
      using pf Gsub wG gain_dip_nonzero_of_sin by blast
    have "x \<in> branch2_locus \<omega>0 \<omega>s \<omega>"
      by (rule nonaligned_rank_defect_in_branch2_locus[OF cok nal gnz])
    thus "x \<in> {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
        \<and> x \<in> branch2_locus \<omega>0 \<omega>s \<omega>}"
      using xV wG xbad by blast
  qed
  show "\<exists>KN :: nat \<Rightarrow> ((real^2)^'n) set.
      {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
          \<and> \<not> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}
        \<subseteq> (\<Union>n. KN n)
      \<and> (\<forall>n. closed (KN n)) \<and> (\<forall>n. negligible (KN n))"
    using sub coverB2 closedB2 negB2 by (meson order_trans)
qed

section \<open>\<section>7m: the branch-2 residual in \<open>(t,u)\<close> coordinates\<close>

text \<open>
  First formal step of the \<open>(t,u)\<close>-coordinate programme from Sketch.md \<section>7k/7m.
  This does not yet expand the branch-2 equations into scalar trigonometric
  equations; it proves the exact coordinate image containment that later
  refinements will strengthen.
\<close>

definition tu_param_map ::
  "real^2 \<Rightarrow> (real^'n) \<Rightarrow> (real^'n) \<Rightarrow> (real^2)^'n" where
  "tu_param_map c t u =
    (\<chi> m. ((vec_nth t m) / (inner c c)) *\<^sub>R c
       + ((vec_nth u m) / (inner c c)) *\<^sub>R (perp2 c))"

lemma tu_param_map_reconstruct:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  assumes cnz: "c \<noteq> 0"
  shows "tu_param_map c
      (\<chi> m. c \<bullet> vec_nth x m) (\<chi> m. perp2 c \<bullet> vec_nth x m) = x"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix m :: 'n
  have decomp: "vec_nth x m =
      ((c \<bullet> vec_nth x m) / (c \<bullet> c)) *\<^sub>R c
      + ((perp2 c \<bullet> vec_nth x m) / (c \<bullet> c)) *\<^sub>R (perp2 c)"
    by (rule perp2_decomp2[OF cnz])
  show "vec_nth (tu_param_map c
      (\<chi> m. c \<bullet> vec_nth x m) (\<chi> m. perp2 c \<bullet> vec_nth x m)) m = vec_nth x m"
    unfolding tu_param_map_def using decomp by simp
qed

lemma tu_param_map_t_coord:
  fixes c :: "real^2" and t u :: "real^'n"
  assumes cnz: "c \<noteq> 0"
  shows "c \<bullet> vec_nth (tu_param_map c t u) m = vec_nth t m"
proof -
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz by simp
  show ?thesis
    unfolding tu_param_map_def
    using ccnz perp2_orth[of c]
    by (simp add: inner_add_right)
qed

lemma tu_param_map_u_coord:
  fixes c :: "real^2" and t u :: "real^'n"
  assumes cnz: "c \<noteq> 0"
  shows "perp2 c \<bullet> vec_nth (tu_param_map c t u) m = vec_nth u m"
proof -
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz by simp
  have pc: "perp2 c \<bullet> c = 0"
    using perp2_orth inner_commute by metis
  show ?thesis
    unfolding tu_param_map_def
    using ccnz pc
    by (simp add: inner_add_right perp2_self_inner)
qed

lemma tu_param_map_t_axis:
  fixes c :: "real^2" and m :: "'n::finite"
  assumes cnz: "c \<noteq> 0"
  shows "tu_param_map c (axis m (inner c c) :: real^'n) (0 :: real^'n) = slot m c"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix q :: 'n
  have ccnz: "inner c c \<noteq> 0"
    using cnz by simp
  show "vec_nth (tu_param_map c (axis m (inner c c) :: real^'n) (0 :: real^'n)) q =
      vec_nth (slot m c) q"
    using ccnz
    by (cases "q = m") (simp_all add: tu_param_map_def slot_def axis_def field_simps)
qed

lemma tu_param_map_u_axis:
  fixes c :: "real^2" and m :: "'n::finite"
  assumes cnz: "c \<noteq> 0"
  shows "tu_param_map c (0 :: real^'n) (axis m (inner c c) :: real^'n) =
      slot m (perp2 c)"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix q :: 'n
  have ccnz: "inner c c \<noteq> 0"
    using cnz by simp
  show "vec_nth (tu_param_map c (0 :: real^'n) (axis m (inner c c) :: real^'n)) q =
      vec_nth (slot m (perp2 c)) q"
    using ccnz
    by (cases "q = m") (simp_all add: tu_param_map_def slot_def axis_def field_simps)
qed

lemma tu_param_map_inner:
  fixes c w :: "real^2" and t u :: "real^'n"
  shows "w \<bullet> vec_nth (tu_param_map c t u) m =
      (vec_nth t m / (inner c c)) * (w \<bullet> c)
      + (vec_nth u m / (inner c c)) * (w \<bullet> perp2 c)"
  unfolding tu_param_map_def
  by (simp add: inner_add_right)

definition branch2_bad ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "branch2_bad V \<omega>0 \<omega>s \<Gamma> =
    {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
        \<and> x \<in> branch2_locus \<omega>0 \<omega>s \<omega>}"

definition branch2_tu_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> (real^'n))) set" where
  "branch2_tu_system V \<omega>0 \<omega>s \<Gamma> =
    {p. fst p \<in> \<Gamma> \<and>
      (let \<omega> = fst p;
           t = fst (snd p);
           u = snd (snd p);
           x = tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>) t u
       in x \<in> V \<and> x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
          \<and> x \<in> branch2_locus \<omega>0 \<omega>s \<omega>)}"

theorem branch2_bad_subset_tu_system_image:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_bad V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> (\<lambda>p. tu_param_map (cvec_dip \<omega>0 \<omega>s (fst p))
            (fst (snd p)) (snd (snd p)))
          ` branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_bad V \<omega>0 \<omega>s \<Gamma>"
  then obtain \<omega> where xV: "x \<in> V" and wG: "\<omega> \<in> \<Gamma>"
    and xbad: "x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}"
    and xb2: "x \<in> branch2_locus \<omega>0 \<omega>s \<omega>"
    unfolding branch2_bad_def by blast
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  have cnz: "c \<noteq> 0"
    using xbad unfolding BadXGW_def c_def by blast
  define t :: "real^'n" where "t = (\<chi> m. c \<bullet> vec_nth x m)"
  define u :: "real^'n" where "u = (\<chi> m. perp2 c \<bullet> vec_nth x m)"
  have recon: "tu_param_map c t u = x"
    unfolding t_def u_def by (rule tu_param_map_reconstruct[OF cnz])
  have pin: "(\<omega>, (t, u)) \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
      unfolding branch2_tu_system_def Let_def c_def[symmetric]
    using wG xV xbad xb2 recon by (simp add: c_def)
  have "(\<lambda>p. tu_param_map (cvec_dip \<omega>0 \<omega>s (fst p))
      (fst (snd p)) (snd (snd p))) (\<omega>, (t, u)) = x"
    using recon unfolding c_def by simp
  thus "x \<in> (\<lambda>p. tu_param_map (cvec_dip \<omega>0 \<omega>s (fst p))
          (fst (snd p)) (snd (snd p)))
          ` branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
    using pin by blast
qed

definition branch2_tu_radial_locus ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "branch2_tu_radial_locus \<omega>0 \<omega>s \<omega> t u \<longleftrightarrow>
    (\<exists>ell::real^2. ell \<noteq> 0
      \<and> (vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0
      \<and> (\<forall>m. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s
              (tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>) t u) \<omega>
              (tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>)
                (axis m (inner (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>)) :: real^'n)
                (0 :: real^'n)) = 0))"

lemma branch2_locus_imp_branch2_tu_radial_locus:
  fixes t u :: "real^'n::finite"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and b2: "tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>) t u \<in> branch2_locus \<omega>0 \<omega>s \<omega>"
  shows "branch2_tu_radial_locus \<omega>0 \<omega>s \<omega> t u"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?x = "tu_param_map ?c t u"
  obtain ell :: "real^2" where ellnz: "ell \<noteq> 0"
    and special: "(vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 ?c = 0"
    and radial: "\<forall>m. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s ?x \<omega> (slot m ?c) = 0"
    using b2 unfolding branch2_locus_def by blast
  have axis_eq: "tu_param_map ?c
      (axis m (inner ?c ?c) :: real^'n) (0 :: real^'n) = slot m ?c" for m
    by (rule tu_param_map_t_axis[OF cnz])
  have radial': "\<forall>m. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s ?x \<omega>
      (tu_param_map ?c (axis m (inner ?c ?c) :: real^'n) (0 :: real^'n)) = 0"
    using radial axis_eq by simp
  show ?thesis
    unfolding branch2_tu_radial_locus_def
    using ellnz special radial' by blast
qed

lemma branch2_tu_system_imp_radial_locus:
  fixes V :: "((real^2)^'n::finite) set"
    and p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
  assumes pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
  shows "branch2_tu_radial_locus \<omega>0 \<omega>s (fst p) (fst (snd p)) (snd (snd p))"
proof -
  let ?\<omega> = "fst p"
  let ?t = "fst (snd p)"
  let ?u = "snd (snd p)"
  let ?c = "cvec_dip \<omega>0 \<omega>s ?\<omega>"
  let ?x = "tu_param_map ?c ?t ?u"
  have xbad: "?x \<in> BadXGW \<omega>0 \<omega>s {?\<omega>}"
    and xb2: "?x \<in> branch2_locus \<omega>0 \<omega>s ?\<omega>"
    using pin unfolding branch2_tu_system_def Let_def by auto
  have cnz: "?c \<noteq> 0"
    using xbad unfolding BadXGW_def by blast
  show ?thesis
    by (rule branch2_locus_imp_branch2_tu_radial_locus[OF cnz xb2])
qed

definition gradU_radial_slot_rhs ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n::finite) \<Rightarrow> real^2 \<Rightarrow> 'n \<Rightarrow> real^2" where
  "gradU_radial_slot_rhs \<omega>0 \<omega>s x \<omega> m =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega> in
      (\<chi> j. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1)
          * (2 * (c \<bullet> c)
              * Im (cnj (vec_nth (M_paper x c) 1) * phase c x m))
        + gain_dip \<omega>
          * (2 * (c \<bullet> c)
              * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1
                  * Re (cnj (phase c x m) * vec_nth (M_paper x c) 2)
                + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2
                  * Re (cnj (phase c x m) * vec_nth (M_paper x c) 3))
            + 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> c)
                * Im (cnj (vec_nth (M_paper x c) 1) * phase c x m)
            - 2 * (c \<bullet> c)
                * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> vec_nth x m)
                * Re (cnj (vec_nth (M_paper x c) 1) * phase c x m))))"

lemma gradU_x_partial_radial_slot_closed:
  fixes x :: "(real^2)^'n::finite" and m :: 'n
  shows "gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>
      (slot m (cvec_dip \<omega>0 \<omega>s \<omega>)) =
    gradU_radial_slot_rhs \<omega>0 \<omega>s x \<omega> m"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix j :: 2
  show "vec_nth (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>
        (slot m (cvec_dip \<omega>0 \<omega>s \<omega>))) j =
      vec_nth (gradU_radial_slot_rhs \<omega>0 \<omega>s x \<omega> m) j"
    unfolding gradU_radial_slot_rhs_def Let_def
    by (simp add: gradU_dip_xderiv_slot)
qed

definition branch2_tu_radial_formula_locus ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "branch2_tu_radial_formula_locus \<omega>0 \<omega>s \<omega> t u \<longleftrightarrow>
    (\<exists>ell::real^2. ell \<noteq> 0
      \<and> (vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0
      \<and> (\<forall>m. ell \<bullet> gradU_radial_slot_rhs \<omega>0 \<omega>s
              (tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>) t u) \<omega> m = 0))"

lemma branch2_tu_radial_locus_imp_formula_locus:
  fixes t u :: "real^'n::finite"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and rad: "branch2_tu_radial_locus \<omega>0 \<omega>s \<omega> t u"
  shows "branch2_tu_radial_formula_locus \<omega>0 \<omega>s \<omega> t u"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?x = "tu_param_map ?c t u"
  obtain ell :: "real^2" where ellnz: "ell \<noteq> 0"
    and special: "(vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 ?c = 0"
    and radial_axis: "\<forall>m. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s ?x \<omega>
      (tu_param_map ?c (axis m (inner ?c ?c) :: real^'n) (0 :: real^'n)) = 0"
    using rad unfolding branch2_tu_radial_locus_def by blast
  have axis_eq: "tu_param_map ?c
      (axis m (inner ?c ?c) :: real^'n) (0 :: real^'n) = slot m ?c" for m
    by (rule tu_param_map_t_axis[OF cnz])
  have radial_slot: "\<forall>m. ell \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s ?x \<omega> (slot m ?c) = 0"
    using radial_axis axis_eq by simp
  have radial_formula:
    "\<forall>m. ell \<bullet> gradU_radial_slot_rhs \<omega>0 \<omega>s ?x \<omega> m = 0"
    using radial_slot by (simp add: gradU_x_partial_radial_slot_closed)
  show ?thesis
    unfolding branch2_tu_radial_formula_locus_def
    using ellnz special radial_formula by blast
qed

lemma branch2_tu_system_imp_radial_formula_locus:
  fixes V :: "((real^2)^'n::finite) set"
    and p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
  assumes pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
  shows "branch2_tu_radial_formula_locus \<omega>0 \<omega>s (fst p) (fst (snd p)) (snd (snd p))"
proof -
  let ?\<omega> = "fst p"
  let ?t = "fst (snd p)"
  let ?u = "snd (snd p)"
  let ?c = "cvec_dip \<omega>0 \<omega>s ?\<omega>"
  let ?x = "tu_param_map ?c ?t ?u"
  have xbad: "?x \<in> BadXGW \<omega>0 \<omega>s {?\<omega>}"
    using pin unfolding branch2_tu_system_def Let_def by auto
  have cnz: "?c \<noteq> 0"
    using xbad unfolding BadXGW_def by blast
  have rad: "branch2_tu_radial_locus \<omega>0 \<omega>s ?\<omega> ?t ?u"
    by (rule branch2_tu_system_imp_radial_locus[OF pin])
  show ?thesis
    by (rule branch2_tu_radial_locus_imp_formula_locus[OF cnz rad])
qed

definition gradU_radial_tu_slot_rhs ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> 'n \<Rightarrow> real^2"
  where
  "gradU_radial_tu_slot_rhs \<omega>0 \<omega>s \<omega> t u m =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega>;
         x = tu_param_map c t u
     in (\<chi> j. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1)
          * (2 * (c \<bullet> c)
              * Im (cnj (vec_nth (M_paper x c) 1) * phase c x m))
        + gain_dip \<omega>
          * (2 * (c \<bullet> c)
              * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1
                  * Re (cnj (phase c x m) * vec_nth (M_paper x c) 2)
                + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2
                  * Re (cnj (phase c x m) * vec_nth (M_paper x c) 3))
            + 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> c)
                * Im (cnj (vec_nth (M_paper x c) 1) * phase c x m)
            - 2 * (c \<bullet> c)
                * ((vec_nth t m / (inner c c))
                    * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> c)
                  + (vec_nth u m / (inner c c))
                    * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> perp2 c))
                * Re (cnj (vec_nth (M_paper x c) 1) * phase c x m))))"

lemma gradU_radial_slot_rhs_tu:
  fixes t u :: "real^'n::finite"
  shows "gradU_radial_slot_rhs \<omega>0 \<omega>s
      (tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>) t u) \<omega> m =
    gradU_radial_tu_slot_rhs \<omega>0 \<omega>s \<omega> t u m"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix j :: 2
  show "vec_nth (gradU_radial_slot_rhs \<omega>0 \<omega>s
        (tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>) t u) \<omega> m) j =
      vec_nth (gradU_radial_tu_slot_rhs \<omega>0 \<omega>s \<omega> t u m) j"
    unfolding gradU_radial_slot_rhs_def gradU_radial_tu_slot_rhs_def Let_def
    by (simp add: tu_param_map_inner)
qed

definition branch2_tu_radial_tu_formula_locus ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "branch2_tu_radial_tu_formula_locus \<omega>0 \<omega>s \<omega> t u \<longleftrightarrow>
    (\<exists>ell::real^2. ell \<noteq> 0
      \<and> (vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0
      \<and> (\<forall>m. ell \<bullet> gradU_radial_tu_slot_rhs \<omega>0 \<omega>s \<omega> t u m = 0))"

lemma branch2_tu_radial_formula_locus_imp_tu_formula_locus:
  fixes t u :: "real^'n::finite"
  assumes form: "branch2_tu_radial_formula_locus \<omega>0 \<omega>s \<omega> t u"
  shows "branch2_tu_radial_tu_formula_locus \<omega>0 \<omega>s \<omega> t u"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?x = "tu_param_map ?c t u"
  obtain ell :: "real^2" where ellnz: "ell \<noteq> 0"
    and special: "(vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 ?c = 0"
    and radial_formula:
      "\<forall>m. ell \<bullet> gradU_radial_slot_rhs \<omega>0 \<omega>s ?x \<omega> m = 0"
    using form unfolding branch2_tu_radial_formula_locus_def by blast
  have radial_tu:
      "\<forall>m. ell \<bullet> gradU_radial_tu_slot_rhs \<omega>0 \<omega>s \<omega> t u m = 0"
    using radial_formula by (simp add: gradU_radial_slot_rhs_tu)
  show ?thesis
    unfolding branch2_tu_radial_tu_formula_locus_def
    using ellnz special radial_tu by blast
qed

lemma branch2_tu_system_imp_radial_tu_formula_locus:
  fixes V :: "((real^2)^'n::finite) set"
    and p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
  assumes pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
  shows "branch2_tu_radial_tu_formula_locus \<omega>0 \<omega>s (fst p) (fst (snd p)) (snd (snd p))"
proof -
  have form: "branch2_tu_radial_formula_locus \<omega>0 \<omega>s
      (fst p) (fst (snd p)) (snd (snd p))"
    by (rule branch2_tu_system_imp_radial_formula_locus[OF pin])
  show ?thesis
    by (rule branch2_tu_radial_formula_locus_imp_tu_formula_locus[OF form])
qed

subsection \<open>\<section>7q: pulled-back phase and moment sums\<close>

text \<open>
  The next layer removes the opaque \<open>phase\<close> and first three \<open>M_paper\<close>
  entries from the radial-slot formula after substituting \<open>x = T_c(t,u)\<close>.
  The phase and \<open>A\<close> moment depend only on \<open>t\<close>; the ambient-coordinate
  moments \<open>M1\<close> and \<open>M2\<close> become explicit affine-weighted sums in \<open>(t,u)\<close>.
\<close>

definition phase_t :: "real^'n \<Rightarrow> 'n \<Rightarrow> complex" where
  "phase_t t m = cis (-(vec_nth t m))"

definition A_t_moment :: "real^('n::finite) \<Rightarrow> complex" where
  "A_t_moment t = (\<Sum>m\<in>UNIV. phase_t t m)"

definition tu_coord ::
  "real^2 \<Rightarrow> real^'n \<Rightarrow> real^'n \<Rightarrow> 'n \<Rightarrow> 2 \<Rightarrow> real" where
  "tu_coord c t u m j =
    (vec_nth t m / inner c c) * vec_nth c j
    + (vec_nth u m / inner c c) * vec_nth (perp2 c) j"

definition M1_tu_moment ::
  "real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> complex" where
  "M1_tu_moment c t u =
    (\<Sum>m\<in>UNIV. of_real (tu_coord c t u m 1) * phase_t t m)"

definition M2_tu_moment ::
  "real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> complex" where
  "M2_tu_moment c t u =
    (\<Sum>m\<in>UNIV. of_real (tu_coord c t u m 2) * phase_t t m)"

lemma phase_t_tu_param_map:
  fixes c :: "real^2" and t u :: "real^'n::finite"
  assumes cnz: "c \<noteq> 0"
  shows "phase c (tu_param_map c t u) m = phase_t t m"
  unfolding phase_def phase_t_def
  by (simp add: tu_param_map_t_coord[OF cnz])

lemma tu_param_map_component:
  fixes c :: "real^2" and t u :: "real^'n"
  shows "vec_nth (vec_nth (tu_param_map c t u) m) j = tu_coord c t u m j"
  unfolding tu_param_map_def tu_coord_def
  by simp

lemma A_moment_tu_param_map:
  fixes c :: "real^2" and t u :: "real^'n::finite"
  assumes cnz: "c \<noteq> 0"
  shows "A_moment (tu_param_map c t u) c = A_t_moment t"
  unfolding A_moment_def A_t_moment_def
  by (rule sum.cong[OF refl]) (simp add: phase_t_tu_param_map[OF cnz])

lemma M1_moment_tu_param_map:
  fixes c :: "real^2" and t u :: "real^'n::finite"
  assumes cnz: "c \<noteq> 0"
  shows "M1_moment (tu_param_map c t u) c = M1_tu_moment c t u"
  unfolding M1_moment_def M1_tu_moment_def
  by (rule sum.cong[OF refl])
     (simp add: phase_t_tu_param_map[OF cnz] tu_param_map_component)

lemma M2_moment_tu_param_map:
  fixes c :: "real^2" and t u :: "real^'n::finite"
  assumes cnz: "c \<noteq> 0"
  shows "M2_moment (tu_param_map c t u) c = M2_tu_moment c t u"
  unfolding M2_moment_def M2_tu_moment_def
  by (rule sum.cong[OF refl])
     (simp add: phase_t_tu_param_map[OF cnz] tu_param_map_component)

lemma M_paper_tu_components_123:
  fixes c :: "real^2" and t u :: "real^'n::finite"
  assumes cnz: "c \<noteq> 0"
  shows "vec_nth (M_paper (tu_param_map c t u) c) 1 = A_t_moment t"
    and "vec_nth (M_paper (tu_param_map c t u) c) 2 = M1_tu_moment c t u"
    and "vec_nth (M_paper (tu_param_map c t u) c) 3 = M2_tu_moment c t u"
  using cnz
  by (simp_all add: A_moment_tu_param_map M1_moment_tu_param_map M2_moment_tu_param_map)

definition gradU_radial_tu_moment_rhs ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> 'n \<Rightarrow> real^2"
  where
  "gradU_radial_tu_moment_rhs \<omega>0 \<omega>s \<omega> t u m =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega> in
      (\<chi> j. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1)
          * (2 * (c \<bullet> c)
              * Im (cnj (A_t_moment t) * phase_t t m))
        + gain_dip \<omega>
          * (2 * (c \<bullet> c)
              * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1
                  * Re (cnj (phase_t t m) * M1_tu_moment c t u)
                + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2
                  * Re (cnj (phase_t t m) * M2_tu_moment c t u))
            + 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> c)
                * Im (cnj (A_t_moment t) * phase_t t m)
            - 2 * (c \<bullet> c)
                * ((vec_nth t m / (inner c c))
                    * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> c)
                  + (vec_nth u m / (inner c c))
                    * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> perp2 c))
                * Re (cnj (A_t_moment t) * phase_t t m))))"

lemma gradU_radial_tu_slot_rhs_moments:
  fixes t u :: "real^'n::finite"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "gradU_radial_tu_slot_rhs \<omega>0 \<omega>s \<omega> t u m =
    gradU_radial_tu_moment_rhs \<omega>0 \<omega>s \<omega> t u m"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix j :: 2
  show "vec_nth (gradU_radial_tu_slot_rhs \<omega>0 \<omega>s \<omega> t u m) j =
      vec_nth (gradU_radial_tu_moment_rhs \<omega>0 \<omega>s \<omega> t u m) j"
    using cnz
    unfolding gradU_radial_tu_slot_rhs_def gradU_radial_tu_moment_rhs_def Let_def
    by (simp add: phase_t_tu_param_map A_moment_tu_param_map
        M1_moment_tu_param_map M2_moment_tu_param_map M_paper_tu_components_123)
qed

definition branch2_tu_radial_moment_formula_locus ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "branch2_tu_radial_moment_formula_locus \<omega>0 \<omega>s \<omega> t u \<longleftrightarrow>
    (\<exists>ell::real^2. ell \<noteq> 0
      \<and> (vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0
      \<and> (\<forall>m. ell \<bullet> gradU_radial_tu_moment_rhs \<omega>0 \<omega>s \<omega> t u m = 0))"

lemma branch2_tu_radial_tu_formula_locus_imp_moment_formula_locus:
  fixes t u :: "real^'n::finite"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and form: "branch2_tu_radial_tu_formula_locus \<omega>0 \<omega>s \<omega> t u"
  shows "branch2_tu_radial_moment_formula_locus \<omega>0 \<omega>s \<omega> t u"
proof -
  obtain ell :: "real^2" where ellnz: "ell \<noteq> 0"
    and special: "(vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    and radial_tu:
      "\<forall>m. ell \<bullet> gradU_radial_tu_slot_rhs \<omega>0 \<omega>s \<omega> t u m = 0"
    using form unfolding branch2_tu_radial_tu_formula_locus_def by blast
  have radial_moments:
      "\<forall>m. ell \<bullet> gradU_radial_tu_moment_rhs \<omega>0 \<omega>s \<omega> t u m = 0"
    using radial_tu cnz by (simp add: gradU_radial_tu_slot_rhs_moments)
  show ?thesis
    unfolding branch2_tu_radial_moment_formula_locus_def
    using ellnz special radial_moments by blast
qed

lemma branch2_tu_system_imp_radial_moment_formula_locus:
  fixes V :: "((real^2)^'n::finite) set"
    and p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
  assumes pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
  shows "branch2_tu_radial_moment_formula_locus \<omega>0 \<omega>s
      (fst p) (fst (snd p)) (snd (snd p))"
proof -
  let ?\<omega> = "fst p"
  let ?t = "fst (snd p)"
  let ?u = "snd (snd p)"
  let ?c = "cvec_dip \<omega>0 \<omega>s ?\<omega>"
  let ?x = "tu_param_map ?c ?t ?u"
  have xbad: "?x \<in> BadXGW \<omega>0 \<omega>s {?\<omega>}"
    using pin unfolding branch2_tu_system_def Let_def by auto
  have cnz: "?c \<noteq> 0"
    using xbad unfolding BadXGW_def by blast
  have form: "branch2_tu_radial_tu_formula_locus \<omega>0 \<omega>s ?\<omega> ?t ?u"
    by (rule branch2_tu_system_imp_radial_tu_formula_locus[OF pin])
  show ?thesis
    by (rule branch2_tu_radial_tu_formula_locus_imp_moment_formula_locus[OF cnz form])
qed

subsection \<open>\<section>7r: finite scalar residual for the branch-2 equations\<close>

text \<open>
  The special-covector side condition is one scalar equation, and the radial
  equations form one scalar equation for each antenna index.  We bundle them
  as a single residual in \<open>real \<times> real^'n\<close>, while keeping the projective
  covector \<open>ell\<close> existential for the next charting step.
\<close>

definition branch2_special_coeffs :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "branch2_special_coeffs \<omega>0 \<omega>s \<omega> =
    (\<chi> j. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))"

lemma branch2_special_condition_eq:
  fixes ell :: "real^2"
  shows "(vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
         + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))
          \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)
      = ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s \<omega>"
  unfolding branch2_special_coeffs_def
  by (simp add: inner_vec_def sum_2 inner_add_left algebra_simps)

definition branch2_radial_scalar_eq ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow>
    real^2 \<Rightarrow> 'n \<Rightarrow> real" where
  "branch2_radial_scalar_eq \<omega>0 \<omega>s \<omega> t u ell m =
    ell \<bullet> gradU_radial_tu_moment_rhs \<omega>0 \<omega>s \<omega> t u m"

definition branch2_tu_scalar_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow>
    real^2 \<Rightarrow> real \<times> (real^'n)" where
  "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell =
    (ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s \<omega>,
     (\<chi> m. branch2_radial_scalar_eq \<omega>0 \<omega>s \<omega> t u ell m))"

definition branch2_tu_scalar_system_locus ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "branch2_tu_scalar_system_locus \<omega>0 \<omega>s \<omega> t u \<longleftrightarrow>
    (\<exists>ell::real^2. ell \<noteq> 0
      \<and> branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell = (0, (0 :: real^'n)))"

lemma branch2_tu_radial_moment_formula_locus_iff_scalar_system_locus:
  fixes t u :: "real^'n::finite"
  shows "branch2_tu_radial_moment_formula_locus \<omega>0 \<omega>s \<omega> t u
      \<longleftrightarrow> branch2_tu_scalar_system_locus \<omega>0 \<omega>s \<omega> t u"
  unfolding branch2_tu_radial_moment_formula_locus_def
    branch2_tu_scalar_system_locus_def branch2_tu_scalar_residual_def
    branch2_radial_scalar_eq_def
  by (auto simp: branch2_special_condition_eq Finite_Cartesian_Product.vec_eq_iff)

lemma branch2_tu_system_imp_scalar_system_locus:
  fixes V :: "((real^2)^'n::finite) set"
    and p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
  assumes pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
  shows "branch2_tu_scalar_system_locus \<omega>0 \<omega>s
      (fst p) (fst (snd p)) (snd (snd p))"
  using branch2_tu_system_imp_radial_moment_formula_locus[OF pin]
  by (simp add: branch2_tu_radial_moment_formula_locus_iff_scalar_system_locus)

subsection \<open>\<section>7s: projective covector charts\<close>

definition ell_chart1 :: "real \<Rightarrow> real^2" where
  "ell_chart1 a = (\<chi> j. if j = 1 then 1 else a)"

definition ell_chart2 :: "real \<Rightarrow> real^2" where
  "ell_chart2 a = (\<chi> j. if j = 2 then 1 else a)"

lemma ell_chart1_simps [simp]:
  "vec_nth (ell_chart1 a) 1 = 1"
  "vec_nth (ell_chart1 a) 2 = a"
  unfolding ell_chart1_def by simp_all

lemma ell_chart2_simps [simp]:
  "vec_nth (ell_chart2 a) 1 = a"
  "vec_nth (ell_chart2 a) 2 = 1"
  unfolding ell_chart2_def by simp_all

lemma ell_chart1_nonzero [simp]: "ell_chart1 a \<noteq> 0"
  by (metis ell_chart1_simps(1) zero_index zero_neq_one)

lemma ell_chart2_nonzero [simp]: "ell_chart2 a \<noteq> 0"
  by (metis ell_chart2_simps(2) zero_index zero_neq_one)

lemma branch2_tu_scalar_residual_scaleR:
  fixes ell :: "real^2"
  shows "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u (r *\<^sub>R ell) =
    (r * fst (branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell),
     r *\<^sub>R snd (branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell))"
  unfolding branch2_tu_scalar_residual_def branch2_radial_scalar_eq_def
  by (simp add: inner_scaleR_left Finite_Cartesian_Product.vec_eq_iff)

lemma branch2_tu_scalar_residual_scaleR_zero:
  fixes ell :: "real^2" and t u :: "real^'n::finite"
  assumes zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell = (0, (0 :: real^'n))"
  shows "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u (r *\<^sub>R ell) = (0, (0 :: real^'n))"
  using zero by (simp add: branch2_tu_scalar_residual_scaleR)

lemma scaleR_ell_chart1:
  fixes ell :: "real^2"
  assumes e1: "vec_nth ell 1 \<noteq> 0"
  shows "(inverse (vec_nth ell 1)) *\<^sub>R ell = ell_chart1 (vec_nth ell 2 / vec_nth ell 1)"
  using e1
  by (simp add: ell_chart1_def Finite_Cartesian_Product.vec_eq_iff forall_2 field_simps)

lemma scaleR_ell_chart2:
  fixes ell :: "real^2"
  assumes e2: "vec_nth ell 2 \<noteq> 0"
  shows "(inverse (vec_nth ell 2)) *\<^sub>R ell = ell_chart2 (vec_nth ell 1 / vec_nth ell 2)"
  using e2
  by (simp add: ell_chart2_def Finite_Cartesian_Product.vec_eq_iff forall_2 field_simps)

definition branch2_tu_scalar_chart1_locus ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s \<omega> t u \<longleftrightarrow>
    (\<exists>a::real. branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u (ell_chart1 a)
      = (0, (0 :: real^'n)))"

definition branch2_tu_scalar_chart2_locus ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^'n \<Rightarrow> bool" where
  "branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s \<omega> t u \<longleftrightarrow>
    (\<exists>a::real. branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u (ell_chart2 a)
      = (0, (0 :: real^'n)))"

lemma nonzero_real2_component_cases:
  fixes ell :: "real^2"
  assumes ellnz: "ell \<noteq> 0"
  shows "vec_nth ell 1 \<noteq> 0 \<or> vec_nth ell 2 \<noteq> 0"
  using ellnz
  by (auto simp: Finite_Cartesian_Product.vec_eq_iff forall_2)

lemma branch2_tu_scalar_system_locus_imp_chart_locus:
  fixes t u :: "real^'n::finite"
  assumes sys: "branch2_tu_scalar_system_locus \<omega>0 \<omega>s \<omega> t u"
  shows "branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s \<omega> t u
      \<or> branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s \<omega> t u"
proof -
  obtain ell :: "real^2" where ellnz: "ell \<noteq> 0"
    and zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell = (0, (0 :: real^'n))"
    using sys unfolding branch2_tu_scalar_system_locus_def by blast
  consider (one) "vec_nth ell 1 \<noteq> 0" | (two) "vec_nth ell 2 \<noteq> 0"
    using nonzero_real2_component_cases[OF ellnz] by blast
  thus ?thesis
  proof cases
    case one
    have scaled: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u
        ((inverse (vec_nth ell 1)) *\<^sub>R ell) = (0, (0 :: real^'n))"
      by (rule branch2_tu_scalar_residual_scaleR_zero[OF zero])
    have "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u
        (ell_chart1 (vec_nth ell 2 / vec_nth ell 1)) = (0, (0 :: real^'n))"
      using scaled scaleR_ell_chart1[OF one] by simp
    thus ?thesis
      unfolding branch2_tu_scalar_chart1_locus_def by blast
  next
    case two
    have scaled: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u
        ((inverse (vec_nth ell 2)) *\<^sub>R ell) = (0, (0 :: real^'n))"
      by (rule branch2_tu_scalar_residual_scaleR_zero[OF zero])
    have "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u
        (ell_chart2 (vec_nth ell 1 / vec_nth ell 2)) = (0, (0 :: real^'n))"
      using scaled scaleR_ell_chart2[OF two] by simp
    thus ?thesis
      unfolding branch2_tu_scalar_chart2_locus_def by blast
  qed
qed

lemma branch2_tu_scalar_chart_locus_imp_system_locus:
  fixes t u :: "real^'n::finite"
  assumes chart: "branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s \<omega> t u
      \<or> branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s \<omega> t u"
  shows "branch2_tu_scalar_system_locus \<omega>0 \<omega>s \<omega> t u"
  using chart
proof
  assume c1: "branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s \<omega> t u"
  then obtain a :: real where
    zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u (ell_chart1 a) =
      (0, (0 :: real^'n))"
    unfolding branch2_tu_scalar_chart1_locus_def by blast
  show ?thesis
    unfolding branch2_tu_scalar_system_locus_def
    using zero ell_chart1_nonzero by blast
next
  assume c2: "branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s \<omega> t u"
  then obtain a :: real where
    zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u (ell_chart2 a) =
      (0, (0 :: real^'n))"
    unfolding branch2_tu_scalar_chart2_locus_def by blast
  show ?thesis
    unfolding branch2_tu_scalar_system_locus_def
    using zero ell_chart2_nonzero by blast
qed

lemma branch2_tu_scalar_system_locus_iff_chart_loci:
  fixes t u :: "real^'n::finite"
  shows "branch2_tu_scalar_system_locus \<omega>0 \<omega>s \<omega> t u
      \<longleftrightarrow> branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s \<omega> t u
        \<or> branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s \<omega> t u"
  using branch2_tu_scalar_system_locus_imp_chart_locus
    branch2_tu_scalar_chart_locus_imp_system_locus
  by blast

lemma branch2_tu_system_imp_scalar_chart_locus:
  fixes V :: "((real^2)^'n::finite) set"
    and p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
  assumes pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
  shows "branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s (fst p) (fst (snd p)) (snd (snd p))
      \<or> branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s (fst p) (fst (snd p)) (snd (snd p))"
  using branch2_tu_system_imp_scalar_system_locus[OF pin]
    branch2_tu_scalar_system_locus_imp_chart_locus
  by blast

subsection \<open>\<section>7t: reducing the branch-2 cover to the two chart images\<close>

definition branch2_tu_x_map ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<Rightarrow>
    (real^2)^'n" where
  "branch2_tu_x_map \<omega>0 \<omega>s p =
    (let \<omega> = fst p; t = fst (snd p); u = snd (snd p)
     in tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>) t u)"

definition branch2_tu_chart1_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow>
    ((real^2) \<times> ((real^'n) \<times> (real^'n))) set" where
  "branch2_tu_chart1_system V \<omega>0 \<omega>s \<Gamma> =
    {p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>.
      branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p))}"

definition branch2_tu_chart2_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow>
    ((real^2) \<times> ((real^'n) \<times> (real^'n))) set" where
  "branch2_tu_chart2_system V \<omega>0 \<omega>s \<Gamma> =
    {p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>.
      branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p))}"

definition branch2_tu_chart1_image ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow>
    ((real^2)^'n) set" where
  "branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma> =
    branch2_tu_x_map \<omega>0 \<omega>s ` branch2_tu_chart1_system V \<omega>0 \<omega>s \<Gamma>"

definition branch2_tu_chart2_image ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow>
    ((real^2)^'n) set" where
  "branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma> =
    branch2_tu_x_map \<omega>0 \<omega>s ` branch2_tu_chart2_system V \<omega>0 \<omega>s \<Gamma>"

lemma branch2_bad_subset_tu_chart_images:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_bad V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma>
        \<union> branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma>"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_bad V \<omega>0 \<omega>s \<Gamma>"
  have "x \<in> (\<lambda>p. tu_param_map (cvec_dip \<omega>0 \<omega>s (fst p))
            (fst (snd p)) (snd (snd p)))
          ` branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
    using branch2_bad_subset_tu_system_image[of V \<omega>0 \<omega>s \<Gamma>] xin by blast
  then obtain p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
    where pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
      and xeq: "x = tu_param_map (cvec_dip \<omega>0 \<omega>s (fst p))
            (fst (snd p)) (snd (snd p))"
    by blast
  have chart: "branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p))
      \<or> branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p))"
    by (rule branch2_tu_system_imp_scalar_chart_locus[OF pin])
  have xmap: "branch2_tu_x_map \<omega>0 \<omega>s p = x"
    using xeq unfolding branch2_tu_x_map_def Let_def by simp
  show "x \<in> branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma>
        \<union> branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma>"
    using chart pin xmap
    unfolding branch2_tu_chart1_image_def branch2_tu_chart2_image_def
      branch2_tu_chart1_system_def branch2_tu_chart2_system_def
    by blast
qed

lemma closed_negligible_cover_Un:
  fixes S1 S2 :: "'a::euclidean_space set"
    and K1 K2 :: "nat \<Rightarrow> 'a set"
  assumes cover1: "S1 \<subseteq> (\<Union>n. K1 n)"
    and closed1: "\<forall>n. closed (K1 n)"
    and neg1: "\<forall>n. negligible (K1 n)"
    and cover2: "S2 \<subseteq> (\<Union>n. K2 n)"
    and closed2: "\<forall>n. closed (K2 n)"
    and neg2: "\<forall>n. negligible (K2 n)"
  shows "\<exists>K :: nat \<Rightarrow> 'a set.
      S1 \<union> S2 \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  have cnt: "Countable_Set.countable (UNIV :: (bool \<times> nat) set)"
    by (rule countableI_type)
  have ne: "(UNIV :: (bool \<times> nat) set) \<noteq> {}"
    by blast
  define enum where "enum = from_nat_into (UNIV :: (bool \<times> nat) set)"
  have enum_surj: "range enum = (UNIV :: (bool \<times> nat) set)"
    unfolding enum_def by (rule range_from_nat_into[OF ne cnt])
  define K :: "nat \<Rightarrow> 'a set" where
    "K n = (if fst (enum n) then K1 (snd (enum n)) else K2 (snd (enum n)))" for n
  have cover: "S1 \<union> S2 \<subseteq> (\<Union>n. K n)"
  proof
    fix x :: 'a
    assume xin: "x \<in> S1 \<union> S2"
    show "x \<in> (\<Union>n. K n)"
    proof (cases "x \<in> S1")
      case True
      then obtain j where xj: "x \<in> K1 j"
        using cover1 by blast
      obtain n where "enum n = (True, j)"
        using enum_surj by (metis UNIV_I imageE)
      hence "x \<in> K n"
        unfolding K_def using xj by simp
      thus ?thesis by blast
    next
      case False
      hence "x \<in> S2"
        using xin by blast
      then obtain j where xj: "x \<in> K2 j"
        using cover2 by blast
      obtain n where "enum n = (False, j)"
        using enum_surj by (metis UNIV_I imageE)
      hence "x \<in> K n"
        unfolding K_def using xj by simp
      thus ?thesis by blast
    qed
  qed
  have closedK: "closed (K n)" for n
    unfolding K_def using closed1 closed2 by simp
  have negK: "negligible (K n)" for n
    unfolding K_def using neg1 neg2 by simp
  show ?thesis
    using cover closedK negK by blast
qed

theorem branch2_bad_closed_cover_of_tu_chart_image_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes chart1: "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    and chart2: "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_bad V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  obtain K1 :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover1: "branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K1 n)"
      and closed1: "\<forall>n. closed (K1 n)"
      and neg1: "\<forall>n. negligible (K1 n)"
    using chart1 by blast
  obtain K2 :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover2: "branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K2 n)"
      and closed2: "\<forall>n. closed (K2 n)"
      and neg2: "\<forall>n. negligible (K2 n)"
    using chart2 by blast
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where coverU: "branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma>
          \<union> branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K n)"
      and closedK: "\<forall>n. closed (K n)"
      and negK: "\<forall>n. negligible (K n)"
    using closed_negligible_cover_Un[OF cover1 closed1 neg1 cover2 closed2 neg2] by blast
  have coverB: "branch2_bad V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K n)"
    using branch2_bad_subset_tu_chart_images[of V \<omega>0 \<omega>s \<Gamma>] coverU by blast
  show ?thesis
    using coverB closedK negK by blast
qed

theorem branchP_indep_closed_cover_core_all_of_tu_chart_image_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K1 n)
          \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    and chart2: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K2 n)
          \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_branch2_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where coverB: "branch2_bad V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K n)"
      and closedK: "\<forall>n. closed (K n)"
      and negK: "\<forall>n. negligible (K n)"
    using branch2_bad_closed_cover_of_tu_chart_image_covers
        [OF chart1[OF Gsub Gindep] chart2[OF Gsub Gindep]]
    by blast
  show "\<exists>KN :: nat \<Rightarrow> ((real^2)^'n) set.
      {x \<in> V. \<exists>\<omega>\<in>\<Gamma>. x \<in> BadXGW \<omega>0 \<omega>s {\<omega>}
          \<and> x \<in> branch2_locus \<omega>0 \<omega>s \<omega>}
        \<subseteq> (\<Union>n. KN n)
      \<and> (\<forall>n. closed (KN n)) \<and> (\<forall>n. negligible (KN n))"
    using coverB closedK negK unfolding branch2_bad_def by blast
qed

subsection \<open>\<section>7u: chart residuals with the projective parameter exposed\<close>

definition branch2_chart_param_x_map ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    (((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow>
    (real^2)^'n" where
  "branch2_chart_param_x_map \<omega>0 \<omega>s q =
    branch2_tu_x_map \<omega>0 \<omega>s (fst q)"

definition branch2_chart1_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    (((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow>
    real \<times> (real^'n)" where
  "branch2_chart1_residual \<omega>0 \<omega>s q =
    (let p = fst q; a = snd q
     in branch2_tu_scalar_residual \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p)) (ell_chart1 a))"

definition branch2_chart2_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    (((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow>
    real \<times> (real^'n)" where
  "branch2_chart2_residual \<omega>0 \<omega>s q =
    (let p = fst q; a = snd q
     in branch2_tu_scalar_residual \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p)) (ell_chart2 a))"

definition branch2_chart1_param_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow>
    (((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real) set" where
  "branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma> =
    {q. fst q \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>
      \<and> branch2_chart1_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))}"

definition branch2_chart2_param_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow>
    (((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real) set" where
  "branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma> =
    {q. fst q \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>
      \<and> branch2_chart2_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))}"

definition branch2_chart1_param_image ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow>
    ((real^2)^'n) set" where
  "branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma> =
    branch2_chart_param_x_map \<omega>0 \<omega>s ` branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"

definition branch2_chart2_param_image ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow>
    ((real^2)^'n) set" where
  "branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma> =
    branch2_chart_param_x_map \<omega>0 \<omega>s ` branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"

lemma branch2_tu_chart1_image_eq_param_image:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma> =
      branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>"
proof
  show "branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>"
  proof
    fix x :: "(real^2)^'n"
    assume xin: "x \<in> branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma>"
    then obtain p where pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
      and chart: "branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p))"
      and xeq: "x = branch2_tu_x_map \<omega>0 \<omega>s p"
      unfolding branch2_tu_chart1_image_def branch2_tu_chart1_system_def by blast
    obtain a :: real where
      zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p)) (ell_chart1 a) = (0, (0 :: real^'n))"
      using chart unfolding branch2_tu_scalar_chart1_locus_def by blast
    have qin: "(p, a) \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"
      using pin zero
      unfolding branch2_chart1_param_system_def branch2_chart1_residual_def Let_def
      by simp
    have "branch2_chart_param_x_map \<omega>0 \<omega>s (p, a) = x"
      using xeq unfolding branch2_chart_param_x_map_def by simp
    thus "x \<in> branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>"
      unfolding branch2_chart1_param_image_def using qin by blast
  qed
next
  show "branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma>"
  proof
    fix x :: "(real^2)^'n"
    assume xin: "x \<in> branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>"
    then obtain q where qin: "q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"
      and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
      unfolding branch2_chart1_param_image_def by blast
    let ?p = "fst q"
    have pin: "?p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
      and zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s
        (fst ?p) (fst (snd ?p)) (snd (snd ?p)) (ell_chart1 (snd q)) =
        (0, (0 :: real^'n))"
      using qin
      unfolding branch2_chart1_param_system_def branch2_chart1_residual_def Let_def
      by auto
    have chart: "branch2_tu_scalar_chart1_locus \<omega>0 \<omega>s
        (fst ?p) (fst (snd ?p)) (snd (snd ?p))"
      unfolding branch2_tu_scalar_chart1_locus_def using zero by blast
    have pchart: "?p \<in> branch2_tu_chart1_system V \<omega>0 \<omega>s \<Gamma>"
      unfolding branch2_tu_chart1_system_def using pin chart by blast
    have "x = branch2_tu_x_map \<omega>0 \<omega>s ?p"
      using xeq unfolding branch2_chart_param_x_map_def by simp
    thus "x \<in> branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma>"
      unfolding branch2_tu_chart1_image_def using pchart by blast
  qed
qed

lemma branch2_tu_chart2_image_eq_param_image:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma> =
      branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>"
proof
  show "branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>"
  proof
    fix x :: "(real^2)^'n"
    assume xin: "x \<in> branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma>"
    then obtain p where pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
      and chart: "branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p))"
      and xeq: "x = branch2_tu_x_map \<omega>0 \<omega>s p"
      unfolding branch2_tu_chart2_image_def branch2_tu_chart2_system_def by blast
    obtain a :: real where
      zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s
        (fst p) (fst (snd p)) (snd (snd p)) (ell_chart2 a) = (0, (0 :: real^'n))"
      using chart unfolding branch2_tu_scalar_chart2_locus_def by blast
    have qin: "(p, a) \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"
      using pin zero
      unfolding branch2_chart2_param_system_def branch2_chart2_residual_def Let_def
      by simp
    have "branch2_chart_param_x_map \<omega>0 \<omega>s (p, a) = x"
      using xeq unfolding branch2_chart_param_x_map_def by simp
    thus "x \<in> branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>"
      unfolding branch2_chart2_param_image_def using qin by blast
  qed
next
  show "branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma>"
  proof
    fix x :: "(real^2)^'n"
    assume xin: "x \<in> branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>"
    then obtain q where qin: "q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"
      and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
      unfolding branch2_chart2_param_image_def by blast
    let ?p = "fst q"
    have pin: "?p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
      and zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s
        (fst ?p) (fst (snd ?p)) (snd (snd ?p)) (ell_chart2 (snd q)) =
        (0, (0 :: real^'n))"
      using qin
      unfolding branch2_chart2_param_system_def branch2_chart2_residual_def Let_def
      by auto
    have chart: "branch2_tu_scalar_chart2_locus \<omega>0 \<omega>s
        (fst ?p) (fst (snd ?p)) (snd (snd ?p))"
      unfolding branch2_tu_scalar_chart2_locus_def using zero by blast
    have pchart: "?p \<in> branch2_tu_chart2_system V \<omega>0 \<omega>s \<Gamma>"
      unfolding branch2_tu_chart2_system_def using pin chart by blast
    have "x = branch2_tu_x_map \<omega>0 \<omega>s ?p"
      using xeq unfolding branch2_chart_param_x_map_def by simp
    thus "x \<in> branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma>"
      unfolding branch2_tu_chart2_image_def using pchart by blast
  qed
qed

theorem branchP_indep_closed_cover_core_all_of_chart_param_image_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K1 n)
          \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    and chart2: "\<And>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K2 n)
          \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_tu_chart_image_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_tu_chart1_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    using chart1[OF Gsub Gindep]
    by (simp add: branch2_tu_chart1_image_eq_param_image)
  show "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_tu_chart2_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
    using chart2[OF Gsub Gindep]
    by (simp add: branch2_tu_chart2_image_eq_param_image)
qed

subsection \<open>\<section>7v: countable bounded slices of the chart parameter images\<close>

definition branch2_chart_param_omega ::
  "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow> real^2" where
  "branch2_chart_param_omega q = fst (fst q)"

definition branch2_chart_param_t ::
  "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow> real^'n" where
  "branch2_chart_param_t q = fst (snd (fst q))"

definition branch2_chart_param_u ::
  "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow> real^'n" where
  "branch2_chart_param_u q = snd (snd (fst q))"

definition branch2_chart_param_a ::
  "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow> real" where
  "branch2_chart_param_a q = snd q"

definition branch2_chart_param_bounded ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    (((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart_param_bounded \<omega>0 \<omega>s q j \<longleftrightarrow>
    (let c = cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) in
      1 / real (Suc j) \<le> c \<bullet> c
      \<and> norm (branch2_chart_param_t q) \<le> real (Suc j)
      \<and> norm (branch2_chart_param_u q) \<le> real (Suc j)
      \<and> abs (branch2_chart_param_a q) \<le> real (Suc j))"

lemma branch2_tu_system_cvec_nonzero:
  fixes V :: "((real^2)^'n::finite) set"
    and p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
  assumes pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
  shows "cvec_dip \<omega>0 \<omega>s (fst p) \<noteq> 0"
  using pin unfolding branch2_tu_system_def BadXGW_def Let_def by blast

lemma branch2_chart_param_bounded_exists:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
  shows "\<exists>j. branch2_chart_param_bounded \<omega>0 \<omega>s q j"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q)"
  have ccpos: "0 < ?c \<bullet> ?c"
    using cnz by (metis inner_gt_zero_iff)
  obtain j0 :: nat where j0: "inverse (real (Suc j0)) < ?c \<bullet> ?c"
    using reals_Archimedean[OF ccpos] by blast
  obtain j1 :: nat where j1: "norm (branch2_chart_param_t q) \<le> real j1"
    using real_arch_simple by blast
  obtain j2 :: nat where j2: "norm (branch2_chart_param_u q) \<le> real j2"
    using real_arch_simple by blast
  obtain j3 :: nat where j3: "abs (branch2_chart_param_a q) \<le> real j3"
    using real_arch_simple by blast
  define j where "j = max j0 (max j1 (max j2 j3))"
  have denom_ok: "1 / real (Suc j) \<le> ?c \<bullet> ?c"
  proof -
    have "1 / real (Suc j) \<le> 1 / real (Suc j0)"
      unfolding j_def by (simp only: frac_le)
    also have "\<dots> < ?c \<bullet> ?c"
      using j0 by (simp only: inverse_eq_divide)
    finally show ?thesis by linarith
  qed
  have t_ok: "norm (branch2_chart_param_t q) \<le> real (Suc j)"
  proof -
    have "j1 \<le> j"
      unfolding j_def by simp
    hence "real j1 \<le> real (Suc j)"
      by linarith
    thus ?thesis using j1 by linarith
  qed
  have u_ok: "norm (branch2_chart_param_u q) \<le> real (Suc j)"
  proof -
    have "j2 \<le> j"
      unfolding j_def by simp
    hence "real j2 \<le> real (Suc j)"
      by linarith
    thus ?thesis using j2 by linarith
  qed
  have a_ok: "abs (branch2_chart_param_a q) \<le> real (Suc j)"
  proof -
    have "j3 \<le> j"
      unfolding j_def by simp
    hence "real j3 \<le> real (Suc j)"
      by linarith
    thus ?thesis using j3 by linarith
  qed
  show ?thesis
    unfolding branch2_chart_param_bounded_def Let_def
    using denom_ok t_ok u_ok a_ok by blast
qed

lemma branch2_chart1_param_system_bounded_exists:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "(((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real)"
  assumes qin: "q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"
  shows "\<exists>j. branch2_chart_param_bounded \<omega>0 \<omega>s q j"
proof -
  have pin: "fst q \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
    using qin unfolding branch2_chart1_param_system_def by blast
  have cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    using branch2_tu_system_cvec_nonzero[OF pin]
    unfolding branch2_chart_param_omega_def by simp
  show ?thesis
    by (rule branch2_chart_param_bounded_exists[OF cnz])
qed

lemma branch2_chart2_param_system_bounded_exists:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "(((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real)"
  assumes qin: "q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"
  shows "\<exists>j. branch2_chart_param_bounded \<omega>0 \<omega>s q j"
proof -
  have pin: "fst q \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
    using qin unfolding branch2_chart2_param_system_def by blast
  have cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    using branch2_tu_system_cvec_nonzero[OF pin]
    unfolding branch2_chart_param_omega_def by simp
  show ?thesis
    by (rule branch2_chart_param_bounded_exists[OF cnz])
qed

definition branch2_chart1_param_slice_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    (((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real) set" where
  "branch2_chart1_param_slice_system V \<omega>0 \<omega>s \<Gamma> j =
    {q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>.
      branch2_chart_param_bounded \<omega>0 \<omega>s q j}"

definition branch2_chart2_param_slice_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    (((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real) set" where
  "branch2_chart2_param_slice_system V \<omega>0 \<omega>s \<Gamma> j =
    {q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>.
      branch2_chart_param_bounded \<omega>0 \<omega>s q j}"

definition branch2_chart1_param_slice_image ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    ((real^2)^'n) set" where
  "branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j =
    branch2_chart_param_x_map \<omega>0 \<omega>s ` branch2_chart1_param_slice_system V \<omega>0 \<omega>s \<Gamma> j"

definition branch2_chart2_param_slice_image ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    ((real^2)^'n) set" where
  "branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j =
    branch2_chart_param_x_map \<omega>0 \<omega>s ` branch2_chart2_param_slice_system V \<omega>0 \<omega>s \<Gamma> j"

lemma branch2_chart1_param_image_subset_slice_images:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> (\<Union>j. branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j)"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>"
  then obtain q where qin: "q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"
    and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
    unfolding branch2_chart1_param_image_def by blast
  obtain j where bj: "branch2_chart_param_bounded \<omega>0 \<omega>s q j"
    using branch2_chart1_param_system_bounded_exists[OF qin] by blast
  have "q \<in> branch2_chart1_param_slice_system V \<omega>0 \<omega>s \<Gamma> j"
    using qin bj unfolding branch2_chart1_param_slice_system_def by blast
  hence "x \<in> branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j"
    unfolding branch2_chart1_param_slice_image_def using xeq by blast
  thus "x \<in> (\<Union>j. branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j)"
    by blast
qed

lemma branch2_chart2_param_image_subset_slice_images:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> (\<Union>j. branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j)"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>"
  then obtain q where qin: "q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"
    and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
    unfolding branch2_chart2_param_image_def by blast
  obtain j where bj: "branch2_chart_param_bounded \<omega>0 \<omega>s q j"
    using branch2_chart2_param_system_bounded_exists[OF qin] by blast
  have "q \<in> branch2_chart2_param_slice_system V \<omega>0 \<omega>s \<Gamma> j"
    using qin bj unfolding branch2_chart2_param_slice_system_def by blast
  hence "x \<in> branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j"
    unfolding branch2_chart2_param_slice_image_def using xeq by blast
  thus "x \<in> (\<Union>j. branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j)"
    by blast
qed

lemma closed_negligible_cover_of_slice_covers:
  fixes S :: "'a::euclidean_space set"
    and Slice :: "nat \<Rightarrow> 'a set"
    and K :: "nat \<Rightarrow> nat \<Rightarrow> 'a set"
  assumes coverS: "S \<subseteq> (\<Union>j. Slice j)"
    and coverK: "\<And>j. Slice j \<subseteq> (\<Union>n. K j n)"
    and closedK: "\<And>j n. closed (K j n)"
    and negK: "\<And>j n. negligible (K j n)"
  shows "\<exists>K' :: nat \<Rightarrow> 'a set.
      S \<subseteq> (\<Union>n. K' n)
      \<and> (\<forall>n. closed (K' n)) \<and> (\<forall>n. negligible (K' n))"
proof -
  define i_of :: "nat \<Rightarrow> nat" where "i_of n = fst (prod_decode n)" for n
  define j_of :: "nat \<Rightarrow> nat" where "j_of n = snd (prod_decode n)" for n
  define K' :: "nat \<Rightarrow> 'a set" where
    "K' n = K (i_of n) (j_of n)" for n
  have cover: "S \<subseteq> (\<Union>n. K' n)"
  proof
    fix x :: 'a
    assume xS: "x \<in> S"
    then obtain i where xi: "x \<in> Slice i"
      using coverS by blast
    then obtain j where xj: "x \<in> K i j"
      using coverK by blast
    define n where "n = prod_encode (i, j)"
    have "i_of n = i"
      unfolding i_of_def n_def by simp
    moreover have "j_of n = j"
      unfolding j_of_def n_def by simp
    ultimately have "x \<in> K' n"
      unfolding K'_def using xj by simp
    thus "x \<in> (\<Union>n. K' n)" by blast
  qed
  have closedK': "\<forall>n. closed (K' n)"
    unfolding K'_def using closedK by simp
  have negK': "\<forall>n. negligible (K' n)"
    unfolding K'_def using negK by simp
  show ?thesis
    using cover closedK' negK' by blast
qed

theorem branchP_indep_closed_cover_core_all_of_chart_param_slice_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
          \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
          \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_chart_param_image_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
  proof -
    have ex1: "\<forall>j. \<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
        branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
        \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
      using chart1[OF Gsub Gindep] by blast
    then obtain K1 :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
      where cover1: "\<And>j. branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>n. K1 j n)"
        and closed1: "\<And>j n. closed (K1 j n)"
        and neg1: "\<And>j n. negligible (K1 j n)"
      by metis
    show ?thesis
      by (rule closed_negligible_cover_of_slice_covers
          [OF branch2_chart1_param_image_subset_slice_images cover1 closed1 neg1])
  qed
  show "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  proof -
    have ex2: "\<forall>j. \<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
        branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
        \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
      using chart2[OF Gsub Gindep] by blast
    then obtain K2 :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
      where cover2: "\<And>j. branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>n. K2 j n)"
        and closed2: "\<And>j n. closed (K2 j n)"
        and neg2: "\<And>j n. negligible (K2 j n)"
      by metis
    show ?thesis
      by (rule closed_negligible_cover_of_slice_covers
          [OF branch2_chart2_param_image_subset_slice_images cover2 closed2 neg2])
  qed
qed

subsection \<open>\<section>7w: the special covector cancels the \<open>u\<close>-moment dependence\<close>

definition branch2_ell_combo ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "branch2_ell_combo \<omega>0 \<omega>s \<omega> ell =
    vec_nth ell 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
    + vec_nth ell 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"

lemma branch2_ell_combo_perp_eq_special:
  fixes ell :: "real^2"
  shows "branch2_ell_combo \<omega>0 \<omega>s \<omega> ell \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)
      = ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s \<omega>"
  unfolding branch2_ell_combo_def branch2_special_coeffs_def
  by (simp add: inner_vec_def sum_2 inner_add_left algebra_simps)

lemma real2_parallel_of_perp2_orth:
  fixes c v :: "real^2"
  assumes cnz: "c \<noteq> 0"
    and orth: "v \<bullet> perp2 c = 0"
  shows "v = ((v \<bullet> c) / (c \<bullet> c)) *\<^sub>R c"
proof -
  have decomp: "v = ((c \<bullet> v)/(c \<bullet> c)) *\<^sub>R c
      + ((perp2 c \<bullet> v)/(c \<bullet> c)) *\<^sub>R perp2 c"
    by (rule perp2_decomp2[OF cnz])
  have "perp2 c \<bullet> v = 0"
    using orth by (simp add: inner_commute)
  thus ?thesis
    using decomp by (simp add: inner_commute)
qed

lemma tu_coord_combo_eq_inner:
  fixes c L :: "real^2" and t u :: "real^'n::finite"
  shows "vec_nth L 1 * tu_coord c t u m 1
      + vec_nth L 2 * tu_coord c t u m 2
      = L \<bullet> vec_nth (tu_param_map c t u) m"
  by (simp add: inner_vec_def sum_2 tu_param_map_component)

lemma tu_coord_combo_special_no_u:
  fixes c L :: "real^2" and t u :: "real^'n::finite"
  assumes orth: "L \<bullet> perp2 c = 0"
  shows "vec_nth L 1 * tu_coord c t u m 1
      + vec_nth L 2 * tu_coord c t u m 2
      = (vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)"
proof -
  have "vec_nth L 1 * tu_coord c t u m 1
      + vec_nth L 2 * tu_coord c t u m 2
      = L \<bullet> vec_nth (tu_param_map c t u) m"
    by (rule tu_coord_combo_eq_inner)
  also have "\<dots> = (vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)
      + (vec_nth u m / (c \<bullet> c)) * (L \<bullet> perp2 c)"
    by (rule tu_param_map_inner)
  also have "\<dots> = (vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)"
    using orth by simp
  finally show ?thesis .
qed

definition M12_tu_special_moment ::
  "real^2 \<Rightarrow> real^('n::finite) \<Rightarrow> real^2 \<Rightarrow> complex" where
  "M12_tu_special_moment c t L =
    (\<Sum>m\<in>UNIV. of_real ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)) * phase_t t m)"

lemma M12_tu_moment_combo_special_no_u:
  fixes c L :: "real^2" and t u :: "real^'n::finite"
  assumes orth: "L \<bullet> perp2 c = 0"
  shows "of_real (vec_nth L 1) * M1_tu_moment c t u
      + of_real (vec_nth L 2) * M2_tu_moment c t u
      = M12_tu_special_moment c t L"
proof -
  have "of_real (vec_nth L 1) * M1_tu_moment c t u
      + of_real (vec_nth L 2) * M2_tu_moment c t u
    = (\<Sum>m\<in>UNIV.
        (of_real (vec_nth L 1) * of_real (tu_coord c t u m 1)
        + of_real (vec_nth L 2) * of_real (tu_coord c t u m 2))
        * phase_t t m)"
    unfolding M1_tu_moment_def M2_tu_moment_def
    by (simp add: sum_distrib_left sum.distrib algebra_simps)
  also have "\<dots> =
      (\<Sum>m\<in>UNIV.
        of_real ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)) * phase_t t m)"
  proof (rule sum.cong[OF refl])
    fix m :: 'n
    have coord: "vec_nth L 1 * tu_coord c t u m 1
        + vec_nth L 2 * tu_coord c t u m 2
        = (vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)"
      by (rule tu_coord_combo_special_no_u[OF orth])
    show "(of_real (vec_nth L 1) * of_real (tu_coord c t u m 1)
        + of_real (vec_nth L 2) * of_real (tu_coord c t u m 2))
        * phase_t t m =
        of_real ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)) * phase_t t m"
    proof -
      have coeff: "(of_real (vec_nth L 1) * of_real (tu_coord c t u m 1)
          + of_real (vec_nth L 2) * of_real (tu_coord c t u m 2) :: complex)
          = of_real ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c))"
        using coord by (simp add: algebra_simps, 
              metis (no_types, lifting) of_real_add of_real_divide of_real_mult)
      show ?thesis
        by (simp add: coeff)
    qed
  qed
  finally show ?thesis
    unfolding M12_tu_special_moment_def .
qed

lemma branch2_tu_scalar_residual_zero_ell_combo_perp:
  fixes ell :: "real^2" and t u :: "real^'n::finite"
  assumes zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell = (0, (0 :: real^'n))"
  shows "branch2_ell_combo \<omega>0 \<omega>s \<omega> ell \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
proof -
  have "ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s \<omega> = 0"
    using zero unfolding branch2_tu_scalar_residual_def by simp
  thus ?thesis
    by (simp add: branch2_ell_combo_perp_eq_special)
qed

lemma branch2_chart1_residual_zero_ell_combo_perp:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes zero: "branch2_chart1_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
  shows "branch2_ell_combo \<omega>0 \<omega>s (branch2_chart_param_omega q)
      (ell_chart1 (branch2_chart_param_a q))
        \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q)) = 0"
  using branch2_tu_scalar_residual_zero_ell_combo_perp[of \<omega>0 \<omega>s
      "branch2_chart_param_omega q" "branch2_chart_param_t q"
      "branch2_chart_param_u q" "ell_chart1 (branch2_chart_param_a q)"]
    zero
  unfolding branch2_chart1_residual_def branch2_chart_param_omega_def
    branch2_chart_param_t_def branch2_chart_param_u_def branch2_chart_param_a_def Let_def
  by simp

lemma branch2_chart2_residual_zero_ell_combo_perp:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes zero: "branch2_chart2_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
  shows "branch2_ell_combo \<omega>0 \<omega>s (branch2_chart_param_omega q)
      (ell_chart2 (branch2_chart_param_a q))
        \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q)) = 0"
  using branch2_tu_scalar_residual_zero_ell_combo_perp[of \<omega>0 \<omega>s
      "branch2_chart_param_omega q" "branch2_chart_param_t q"
      "branch2_chart_param_u q" "ell_chart2 (branch2_chart_param_a q)"]
    zero
  unfolding branch2_chart2_residual_def branch2_chart_param_omega_def
    branch2_chart_param_t_def branch2_chart_param_u_def branch2_chart_param_a_def Let_def
  by simp

lemma branch2_tu_scalar_residual_zero_M12_combo_no_u:
  fixes ell :: "real^2" and t u :: "real^'n::finite"
  assumes zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell = (0, (0 :: real^'n))"
  shows "of_real (vec_nth (branch2_ell_combo \<omega>0 \<omega>s \<omega> ell) 1)
        * M1_tu_moment (cvec_dip \<omega>0 \<omega>s \<omega>) t u
      + of_real (vec_nth (branch2_ell_combo \<omega>0 \<omega>s \<omega> ell) 2)
        * M2_tu_moment (cvec_dip \<omega>0 \<omega>s \<omega>) t u
      = M12_tu_special_moment (cvec_dip \<omega>0 \<omega>s \<omega>) t
          (branch2_ell_combo \<omega>0 \<omega>s \<omega> ell)"
proof -
  have orth: "branch2_ell_combo \<omega>0 \<omega>s \<omega> ell
      \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    by (rule branch2_tu_scalar_residual_zero_ell_combo_perp[OF zero])
  show ?thesis
    by (rule M12_tu_moment_combo_special_no_u[OF orth])
qed

lemma Re_complex_linear_combo:
  fixes z M1 M2 :: complex and a b :: real
  shows "a * Re (z * M1) + b * Re (z * M2)
      = Re (z * (of_real a * M1 + of_real b * M2))"
  by (simp add: algebra_simps)

definition branch2_ell_gain_deriv ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "branch2_ell_gain_deriv \<omega> ell =
    ell \<bullet> (\<chi> j. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))"

definition branch2_radial_scalar_L_eq ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow>
    real^'n \<Rightarrow> real^2 \<Rightarrow> 'n \<Rightarrow> real" where
  "branch2_radial_scalar_L_eq \<omega>0 \<omega>s \<omega> t u ell m =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega>;
         L = branch2_ell_combo \<omega>0 \<omega>s \<omega> ell;
         A = A_t_moment t;
         ph = phase_t t m
     in branch2_ell_gain_deriv \<omega> ell
          * (2 * (c \<bullet> c) * Im (cnj A * ph))
        + gain_dip \<omega>
          * (2 * (c \<bullet> c)
              * (vec_nth L 1 * Re (cnj ph * M1_tu_moment c t u)
                + vec_nth L 2 * Re (cnj ph * M2_tu_moment c t u))
            + 2 * (L \<bullet> c) * Im (cnj A * ph)
            - 2 * (c \<bullet> c)
                * ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)
                  + (vec_nth u m / (c \<bullet> c)) * (L \<bullet> perp2 c))
                * Re (cnj A * ph)))"

definition branch2_radial_scalar_reduced_eq ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^('n::finite) \<Rightarrow>
    real^2 \<Rightarrow> 'n \<Rightarrow> real" where
  "branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega>;
         L = branch2_ell_combo \<omega>0 \<omega>s \<omega> ell;
         A = A_t_moment t;
         ph = phase_t t m;
         ML = M12_tu_special_moment c t L
     in branch2_ell_gain_deriv \<omega> ell
          * (2 * (c \<bullet> c) * Im (cnj A * ph))
        + gain_dip \<omega>
          * (2 * (c \<bullet> c) * Re (cnj ph * ML)
            + 2 * (L \<bullet> c) * Im (cnj A * ph)
            - 2 * (c \<bullet> c)
                * ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c))
                * Re (cnj A * ph)))"

lemma branch2_radial_scalar_eq_L_form:
  fixes ell :: "real^2" and t u :: "real^'n::finite"
  shows "branch2_radial_scalar_eq \<omega>0 \<omega>s \<omega> t u ell m =
      branch2_radial_scalar_L_eq \<omega>0 \<omega>s \<omega> t u ell m"
  unfolding branch2_radial_scalar_eq_def branch2_radial_scalar_L_eq_def
    branch2_ell_gain_deriv_def gradU_radial_tu_moment_rhs_def Let_def
  by (simp add: inner_vec_def sum_2 branch2_ell_combo_def algebra_simps)

lemma branch2_radial_scalar_L_eq_special_no_u:
  fixes ell :: "real^2" and t u :: "real^'n::finite"
  assumes orth: "branch2_ell_combo \<omega>0 \<omega>s \<omega> ell
      \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
  shows "branch2_radial_scalar_L_eq \<omega>0 \<omega>s \<omega> t u ell m =
      branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?L = "branch2_ell_combo \<omega>0 \<omega>s \<omega> ell"
  let ?M1 = "M1_tu_moment ?c t u"
  let ?M2 = "M2_tu_moment ?c t u"
  let ?ML = "M12_tu_special_moment ?c t ?L"
  let ?ph = "phase_t t m"
  have Mcombo: "of_real (vec_nth ?L 1) * ?M1 + of_real (vec_nth ?L 2) * ?M2 = ?ML"
    by (rule M12_tu_moment_combo_special_no_u[OF orth])
  have Recombo: "vec_nth ?L 1 * Re (cnj ?ph * ?M1)
      + vec_nth ?L 2 * Re (cnj ?ph * ?M2)
      = Re (cnj ?ph * ?ML)"
  proof -
    have "vec_nth ?L 1 * Re (cnj ?ph * ?M1)
        + vec_nth ?L 2 * Re (cnj ?ph * ?M2)
        = Re (cnj ?ph * (of_real (vec_nth ?L 1) * ?M1
            + of_real (vec_nth ?L 2) * ?M2))"
      by (rule Re_complex_linear_combo)
    also have "\<dots> = Re (cnj ?ph * ?ML)"
      using Mcombo by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding branch2_radial_scalar_L_eq_def branch2_radial_scalar_reduced_eq_def Let_def
    using orth Recombo by (simp add: algebra_simps)
qed

lemma branch2_radial_scalar_eq_special_no_u:
  fixes ell :: "real^2" and t u :: "real^'n::finite"
  assumes orth: "branch2_ell_combo \<omega>0 \<omega>s \<omega> ell
      \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
  shows "branch2_radial_scalar_eq \<omega>0 \<omega>s \<omega> t u ell m =
      branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m"
  using branch2_radial_scalar_eq_L_form[of \<omega>0 \<omega>s \<omega> t u ell m]
    branch2_radial_scalar_L_eq_special_no_u[OF orth]
  by simp

lemma branch2_tu_scalar_residual_zero_radial_reduced:
  fixes ell :: "real^2" and t u :: "real^'n::finite"
  assumes zero: "branch2_tu_scalar_residual \<omega>0 \<omega>s \<omega> t u ell = (0, (0 :: real^'n))"
  shows "branch2_radial_scalar_eq \<omega>0 \<omega>s \<omega> t u ell m =
      branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m"
  by (rule branch2_radial_scalar_eq_special_no_u
      [OF branch2_tu_scalar_residual_zero_ell_combo_perp[OF zero]])

lemma branch2_chart1_residual_zero_radial_reduced:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes zero: "branch2_chart1_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
  shows "branch2_radial_scalar_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (branch2_chart_param_u q) (ell_chart1 (branch2_chart_param_a q)) m =
      branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (ell_chart1 (branch2_chart_param_a q)) m"
  using branch2_tu_scalar_residual_zero_radial_reduced[of \<omega>0 \<omega>s
      "branch2_chart_param_omega q" "branch2_chart_param_t q"
      "branch2_chart_param_u q" "ell_chart1 (branch2_chart_param_a q)"]
    zero
  unfolding branch2_chart1_residual_def branch2_chart_param_omega_def
    branch2_chart_param_t_def branch2_chart_param_u_def branch2_chart_param_a_def Let_def
  by simp

lemma branch2_chart2_residual_zero_radial_reduced:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes zero: "branch2_chart2_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
  shows "branch2_radial_scalar_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (branch2_chart_param_u q) (ell_chart2 (branch2_chart_param_a q)) m =
      branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (ell_chart2 (branch2_chart_param_a q)) m"
  using branch2_tu_scalar_residual_zero_radial_reduced[of \<omega>0 \<omega>s
      "branch2_chart_param_omega q" "branch2_chart_param_t q"
      "branch2_chart_param_u q" "ell_chart2 (branch2_chart_param_a q)"]
    zero
  unfolding branch2_chart2_residual_def branch2_chart_param_omega_def
    branch2_chart_param_t_def branch2_chart_param_u_def branch2_chart_param_a_def Let_def
  by simp

subsection \<open>\<section>7y: reduced base systems plus a bounded free fibre\<close>

definition branch2_base_param_omega ::
  "(((real^2) \<times> (real^'n::finite)) \<times> real) \<Rightarrow> real^2" where
  "branch2_base_param_omega r = fst (fst r)"

definition branch2_base_param_t ::
  "(((real^2) \<times> (real^'n::finite)) \<times> real) \<Rightarrow> real^'n" where
  "branch2_base_param_t r = snd (fst r)"

definition branch2_base_param_a ::
  "(((real^2) \<times> (real^'n::finite)) \<times> real) \<Rightarrow> real" where
  "branch2_base_param_a r = snd r"

definition branch2_base_param_of_chart ::
  "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)
    \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)" where
  "branch2_base_param_of_chart q =
    ((branch2_chart_param_omega q, branch2_chart_param_t q), branch2_chart_param_a q)"

definition branch2_base_param_bounded ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real) \<Rightarrow>
    nat \<Rightarrow> bool" where
  "branch2_base_param_bounded \<omega>0 \<omega>s r j \<longleftrightarrow>
    (let c = cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) in
      1 / real (Suc j) \<le> c \<bullet> c
      \<and> norm (branch2_base_param_t r) \<le> real (Suc j)
      \<and> abs (branch2_base_param_a r) \<le> real (Suc j))"

definition branch2_u_param_bounded :: "real^('n::finite) \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_u_param_bounded u j \<longleftrightarrow> norm u \<le> real (Suc j)"

lemma branch2_chart_param_bounded_imp_base_u_bounded:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes bounded: "branch2_chart_param_bounded \<omega>0 \<omega>s q j"
  shows "branch2_base_param_bounded \<omega>0 \<omega>s (branch2_base_param_of_chart q) j
      \<and> branch2_u_param_bounded (branch2_chart_param_u q) j"
  using bounded
  unfolding branch2_chart_param_bounded_def branch2_base_param_bounded_def
    branch2_u_param_bounded_def branch2_base_param_of_chart_def
    branch2_base_param_omega_def branch2_base_param_t_def branch2_base_param_a_def
    Let_def
  by simp

definition branch2_chart1_reduced_base_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)
    \<Rightarrow> real \<times> (real^'n)" where
  "branch2_chart1_reduced_base_residual \<omega>0 \<omega>s r =
    (let \<omega> = branch2_base_param_omega r;
         t = branch2_base_param_t r;
         ell = ell_chart1 (branch2_base_param_a r)
     in (ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s \<omega>,
        (\<chi> m. branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m)))"

definition branch2_chart2_reduced_base_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)
    \<Rightarrow> real \<times> (real^'n)" where
  "branch2_chart2_reduced_base_residual \<omega>0 \<omega>s r =
    (let \<omega> = branch2_base_param_omega r;
         t = branch2_base_param_t r;
         ell = ell_chart2 (branch2_base_param_a r)
     in (ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s \<omega>,
        (\<chi> m. branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m)))"

lemma branch2_chart1_residual_zero_imp_reduced_base_residual_zero:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes zero: "branch2_chart1_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
  shows "branch2_chart1_reduced_base_residual \<omega>0 \<omega>s
      (branch2_base_param_of_chart q) = (0, (0 :: real^'n))"
proof -
  have special_zero: "ell_chart1 (branch2_chart_param_a q)
      \<bullet> branch2_special_coeffs \<omega>0 \<omega>s (branch2_chart_param_omega q) = 0"
    using zero
    unfolding branch2_chart1_residual_def branch2_tu_scalar_residual_def
      branch2_chart_param_omega_def branch2_chart_param_t_def
      branch2_chart_param_u_def branch2_chart_param_a_def Let_def
    by simp
  have radial_zero: "branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s
      (branch2_chart_param_omega q) (branch2_chart_param_t q)
      (ell_chart1 (branch2_chart_param_a q)) m = 0" for m
  proof -
    have old_zero: "branch2_radial_scalar_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (branch2_chart_param_u q) (ell_chart1 (branch2_chart_param_a q)) m = 0"
      using zero
      unfolding branch2_chart1_residual_def branch2_tu_scalar_residual_def
        branch2_chart_param_omega_def branch2_chart_param_t_def
        branch2_chart_param_u_def branch2_chart_param_a_def Let_def
      by (metis snd_conv vec_lambda_beta zero_index)
    have red_eq: "branch2_radial_scalar_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (branch2_chart_param_u q) (ell_chart1 (branch2_chart_param_a q)) m =
        branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (ell_chart1 (branch2_chart_param_a q)) m"
      by (rule branch2_chart1_residual_zero_radial_reduced[OF zero])
    show ?thesis
      using old_zero red_eq by simp
  qed
  show ?thesis
    unfolding branch2_chart1_reduced_base_residual_def branch2_base_param_of_chart_def
      branch2_base_param_omega_def branch2_base_param_t_def branch2_base_param_a_def
    using special_zero radial_zero
    by (simp add: Finite_Cartesian_Product.vec_eq_iff)
qed

lemma branch2_chart2_residual_zero_imp_reduced_base_residual_zero:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes zero: "branch2_chart2_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
  shows "branch2_chart2_reduced_base_residual \<omega>0 \<omega>s
      (branch2_base_param_of_chart q) = (0, (0 :: real^'n))"
proof -
  have special_zero: "ell_chart2 (branch2_chart_param_a q)
      \<bullet> branch2_special_coeffs \<omega>0 \<omega>s (branch2_chart_param_omega q) = 0"
    using zero
    unfolding branch2_chart2_residual_def branch2_tu_scalar_residual_def
      branch2_chart_param_omega_def branch2_chart_param_t_def
      branch2_chart_param_u_def branch2_chart_param_a_def Let_def
    by simp
  have radial_zero: "branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s
      (branch2_chart_param_omega q) (branch2_chart_param_t q)
      (ell_chart2 (branch2_chart_param_a q)) m = 0" for m
  proof -
    have old_zero: "branch2_radial_scalar_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (branch2_chart_param_u q) (ell_chart2 (branch2_chart_param_a q)) m = 0"
      using zero
      unfolding branch2_chart2_residual_def branch2_tu_scalar_residual_def
        branch2_chart_param_omega_def branch2_chart_param_t_def
        branch2_chart_param_u_def branch2_chart_param_a_def Let_def
      by (simp add: Finite_Cartesian_Product.zero_vec_def)
    have red_eq: "branch2_radial_scalar_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (branch2_chart_param_u q) (ell_chart2 (branch2_chart_param_a q)) m =
        branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s
        (branch2_chart_param_omega q) (branch2_chart_param_t q)
        (ell_chart2 (branch2_chart_param_a q)) m"
      by (rule branch2_chart2_residual_zero_radial_reduced[OF zero])
    show ?thesis
      using old_zero red_eq by simp
  qed
  show ?thesis
    unfolding branch2_chart2_reduced_base_residual_def branch2_base_param_of_chart_def
      branch2_base_param_omega_def branch2_base_param_t_def branch2_base_param_a_def
    using special_zero radial_zero
    by (simp add: Finite_Cartesian_Product.vec_eq_iff)
qed

definition branch2_chart1_reduced_base_system ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    (((real^2) \<times> (real^'n::finite)) \<times> real) set" where
  "branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j =
    {r. branch2_base_param_omega r \<in> \<Gamma>
      \<and> branch2_base_param_bounded \<omega>0 \<omega>s r j
      \<and> branch2_chart1_reduced_base_residual \<omega>0 \<omega>s r = (0, (0 :: real^'n))}"

definition branch2_chart2_reduced_base_system ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    (((real^2) \<times> (real^'n::finite)) \<times> real) set" where
  "branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j =
    {r. branch2_base_param_omega r \<in> \<Gamma>
      \<and> branch2_base_param_bounded \<omega>0 \<omega>s r j
      \<and> branch2_chart2_reduced_base_residual \<omega>0 \<omega>s r = (0, (0 :: real^'n))}"

definition branch2_base_fibre_x_map ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    ((((real^2) \<times> (real^'n::finite)) \<times> real) \<times> (real^'n)) \<Rightarrow>
      (real^2)^'n" where
  "branch2_base_fibre_x_map \<omega>0 \<omega>s ru =
    (let r = fst ru; u = snd ru;
         c = cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r)
     in tu_param_map c (branch2_base_param_t r) u)"

lemma branch2_base_fibre_x_map_of_chart:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  shows "branch2_base_fibre_x_map \<omega>0 \<omega>s
      (branch2_base_param_of_chart q, branch2_chart_param_u q)
      = branch2_chart_param_x_map \<omega>0 \<omega>s q"
  unfolding branch2_base_fibre_x_map_def branch2_chart_param_x_map_def
    branch2_tu_x_map_def branch2_base_param_of_chart_def
    branch2_base_param_omega_def branch2_base_param_t_def
    branch2_chart_param_omega_def branch2_chart_param_t_def
    branch2_chart_param_u_def Let_def
  by simp

definition branch2_chart1_reduced_slice_image ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow> ((real^2)^'n::finite) set" where
  "branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j =
    branch2_base_fibre_x_map \<omega>0 \<omega>s `
      {ru. fst ru \<in> branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j}"

definition branch2_chart2_reduced_slice_image ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow> ((real^2)^'n::finite) set" where
  "branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j =
    branch2_base_fibre_x_map \<omega>0 \<omega>s `
      {ru. fst ru \<in> branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j}"

lemma branch2_chart1_param_slice_image_subset_reduced_slice_image:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j"
  then obtain q where qslice: "q \<in> branch2_chart1_param_slice_system V \<omega>0 \<omega>s \<Gamma> j"
    and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
    unfolding branch2_chart1_param_slice_image_def by blast
  let ?r = "branch2_base_param_of_chart q"
  let ?u = "branch2_chart_param_u q"
  have qsys: "q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"
    and bounded: "branch2_chart_param_bounded \<omega>0 \<omega>s q j"
    using qslice unfolding branch2_chart1_param_slice_system_def by auto
  have omega_in: "branch2_base_param_omega ?r \<in> \<Gamma>"
    using qsys
    unfolding branch2_chart1_param_system_def branch2_tu_system_def
      branch2_base_param_of_chart_def branch2_base_param_omega_def
      branch2_chart_param_omega_def
    by auto
  have base_u_bounded: "branch2_base_param_bounded \<omega>0 \<omega>s ?r j
      \<and> branch2_u_param_bounded ?u j"
    by (rule branch2_chart_param_bounded_imp_base_u_bounded[OF bounded])
  have zero: "branch2_chart1_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
    using qsys unfolding branch2_chart1_param_system_def by blast
  have red_zero: "branch2_chart1_reduced_base_residual \<omega>0 \<omega>s ?r =
      (0, (0 :: real^'n))"
    by (rule branch2_chart1_residual_zero_imp_reduced_base_residual_zero[OF zero])
  have rin: "?r \<in> branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
    using omega_in base_u_bounded red_zero
    unfolding branch2_chart1_reduced_base_system_def by blast
  have pairin: "(?r, ?u) \<in>
      {ru. fst ru \<in> branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j}"
    using rin base_u_bounded by simp
  have xeq': "x = branch2_base_fibre_x_map \<omega>0 \<omega>s (?r, ?u)"
    by (simp add: branch2_base_fibre_x_map_of_chart xeq)
  show "x \<in> branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
    unfolding branch2_chart1_reduced_slice_image_def
    using pairin xeq' by blast
qed

lemma branch2_chart2_param_slice_image_subset_reduced_slice_image:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j"
  then obtain q where qslice: "q \<in> branch2_chart2_param_slice_system V \<omega>0 \<omega>s \<Gamma> j"
    and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
    unfolding branch2_chart2_param_slice_image_def by blast
  let ?r = "branch2_base_param_of_chart q"
  let ?u = "branch2_chart_param_u q"
  have qsys: "q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"
    and bounded: "branch2_chart_param_bounded \<omega>0 \<omega>s q j"
    using qslice unfolding branch2_chart2_param_slice_system_def by auto
  have omega_in: "branch2_base_param_omega ?r \<in> \<Gamma>"
    using qsys
    unfolding branch2_chart2_param_system_def branch2_tu_system_def
      branch2_base_param_of_chart_def branch2_base_param_omega_def
      branch2_chart_param_omega_def
    by auto
  have base_u_bounded: "branch2_base_param_bounded \<omega>0 \<omega>s ?r j
      \<and> branch2_u_param_bounded ?u j"
    by (rule branch2_chart_param_bounded_imp_base_u_bounded[OF bounded])
  have zero: "branch2_chart2_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
    using qsys unfolding branch2_chart2_param_system_def by blast
  have red_zero: "branch2_chart2_reduced_base_residual \<omega>0 \<omega>s ?r =
      (0, (0 :: real^'n))"
    by (rule branch2_chart2_residual_zero_imp_reduced_base_residual_zero[OF zero])
  have rin: "?r \<in> branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
    using omega_in base_u_bounded red_zero
    unfolding branch2_chart2_reduced_base_system_def by blast
  have pairin: "(?r, ?u) \<in>
      {ru. fst ru \<in> branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j}"
    using rin base_u_bounded by simp
  have xeq': "x = branch2_base_fibre_x_map \<omega>0 \<omega>s (?r, ?u)"
    by (simp add: branch2_base_fibre_x_map_of_chart xeq) 
  show "x \<in> branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
    unfolding branch2_chart2_reduced_slice_image_def
    using pairin xeq' by blast
qed

theorem branchP_indep_closed_cover_core_all_of_reduced_slice_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
          \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
          \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_chart_param_slice_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain K1 :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover1: "branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)"
      and closed1: "\<forall>n. closed (K1 n)"
      and neg1: "\<forall>n. negligible (K1 n)"
    using chart1[OF Gsub Gindep] by blast
  show "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart1_param_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    using branch2_chart1_param_slice_image_subset_reduced_slice_image[of V \<omega>0 \<omega>s \<Gamma> j]
      cover1 closed1 neg1 by blast
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain K2 :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover2: "branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)"
      and closed2: "\<forall>n. closed (K2 n)"
      and neg2: "\<forall>n. negligible (K2 n)"
    using chart2[OF Gsub Gindep] by blast
  show "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart2_param_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
    using branch2_chart2_param_slice_image_subset_reduced_slice_image[of V \<omega>0 \<omega>s \<Gamma> j]
      cover2 closed2 neg2 by blast
qed

subsection \<open>\<section>7z: low-dimensional parametrizations of the reduced slices\<close>

lemma closed_negligible_cover_of_lowdim_image:
  fixes F :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    and C :: "'a set"
  assumes dimlt: "DIM('a) < DIM('b)"
    and diff: "F differentiable_on C"
    and closed_image: "closed (F ` C)"
  shows "\<exists>K :: nat \<Rightarrow> 'b set.
      F ` C \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  have neg_image: "negligible (F ` C)"
    by (rule negligible_differentiable_image_lowdim[OF dimlt diff])
  define K :: "nat \<Rightarrow> 'b set" where
    "K n = (if n = 0 then F ` C else {})" for n
  have cover: "F ` C \<subseteq> (\<Union>n. K n)"
    unfolding K_def by simp
  have closedK: "\<forall>n. closed (K n)"
    unfolding K_def using closed_image by simp
  have negK: "\<forall>n. negligible (K n)"
    unfolding K_def using neg_image by simp
  show ?thesis
    using cover closedK negK by blast
qed

lemma branch2_lowdim_source_dim_lt:
  assumes card4: "4 \<le> CARD('n::finite)"
  shows "DIM((real^2) \<times> (real^'n)) < DIM((real^2)^'n)"
  using card4 by simp

lemma closed_negligible_cover_of_branch2_lowdim_param_image:
  fixes S :: "((real^2)^'n::finite) set"
    and C :: "((real^2) \<times> (real^'n)) set"
    and F :: "((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)"
  assumes card4: "4 \<le> CARD('n)"
    and cover: "S \<subseteq> F ` C"
    and diff: "F differentiable_on C"
    and closed_image: "closed (F ` C)"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      S \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  have dimlt: "DIM((real^2) \<times> (real^'n)) < DIM((real^2)^'n)"
    by (rule branch2_lowdim_source_dim_lt[OF card4])
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover_image: "F ` C \<subseteq> (\<Union>n. K n)"
      and closedK: "\<forall>n. closed (K n)"
      and negK: "\<forall>n. negligible (K n)"
    using closed_negligible_cover_of_lowdim_image[OF dimlt diff closed_image]
    by blast
  have coverS: "S \<subseteq> (\<Union>n. K n)"
    using cover cover_image by blast
  show ?thesis
    using coverS closedK negK by blast
qed

lemma closed_negligible_cover_of_branch2_countable_lowdim_param_images:
  fixes S :: "((real^2)^'n::finite) set"
    and C :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) set"
    and F :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)"
  assumes card4: "4 \<le> CARD('n)"
    and cover: "S \<subseteq> (\<Union>i. F i ` C i)"
    and diff: "\<And>i. F i differentiable_on C i"
    and closed_image: "\<And>i. closed (F i ` C i)"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      S \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  have dimlt: "DIM((real^2) \<times> (real^'n)) < DIM((real^2)^'n)"
    by (rule branch2_lowdim_source_dim_lt[OF card4])
  define K :: "nat \<Rightarrow> ((real^2)^'n) set" where
    "K i = F i ` C i" for i
  have closedK: "\<forall>i. closed (K i)"
    unfolding K_def using closed_image by simp
  have negK: "\<forall>i. negligible (K i)"
  proof
    fix i
    show "negligible (K i)"
      unfolding K_def
      by (rule negligible_differentiable_image_lowdim[OF dimlt diff])
  qed
  show ?thesis
    using cover closedK negK unfolding K_def by blast
qed

theorem branchP_indep_closed_cover_core_all_of_reduced_lowdim_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: ((real^2) \<times> (real^'n)) set.
        \<exists>F :: ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
          branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> F ` C
          \<and> F differentiable_on C \<and> closed (F ` C)"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: ((real^2) \<times> (real^'n)) set.
        \<exists>F :: ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
          branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> F ` C
          \<and> F differentiable_on C \<and> closed (F ` C)"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_reduced_slice_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "((real^2) \<times> (real^'n)) set"
    and F :: "((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)"
    where cover: "branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> F ` C"
      and diff: "F differentiable_on C"
      and closed_image: "closed (F ` C)"
    using chart1[OF Gsub Gindep] by blast
  show "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    by (rule closed_negligible_cover_of_branch2_lowdim_param_image
        [OF card4 cover diff closed_image])
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "((real^2) \<times> (real^'n)) set"
    and F :: "((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)"
    where cover: "branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> F ` C"
      and diff: "F differentiable_on C"
      and closed_image: "closed (F ` C)"
    using chart2[OF Gsub Gindep] by blast
  show "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
    by (rule closed_negligible_cover_of_branch2_lowdim_param_image
        [OF card4 cover diff closed_image])
qed

theorem branchP_indep_closed_cover_core_all_of_reduced_countable_lowdim_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) set.
        \<exists>F :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
          branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. F i ` C i)
          \<and> (\<forall>i. F i differentiable_on C i)
          \<and> (\<forall>i. closed (F i ` C i))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) set.
        \<exists>F :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
          branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. F i ` C i)
          \<and> (\<forall>i. F i differentiable_on C i)
          \<and> (\<forall>i. closed (F i ` C i))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_reduced_slice_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) set"
    and F :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)"
    where cover: "branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. F i ` C i)"
      and diff: "\<forall>i. F i differentiable_on C i"
      and closed_image: "\<forall>i. closed (F i ` C i)"
    using chart1[OF Gsub Gindep]
    by meson 
  show "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    by (rule closed_negligible_cover_of_branch2_countable_lowdim_param_images
        [OF card4 cover]) (use diff closed_image in auto)
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) set"
    and F :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)"
    where cover: "branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. F i ` C i)"
      and diff: "\<forall>i. F i differentiable_on C i"
      and closed_image: "\<forall>i. closed (F i ` C i)"
    using chart2[OF Gsub Gindep]
    by meson
  show "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
    by (rule closed_negligible_cover_of_branch2_countable_lowdim_param_images
        [OF card4 cover], use diff closed_image in auto)
qed

subsection \<open>\<section>7aa: base-chart parametrizations from the reduced rank theorem\<close>

definition branch2_u_slice_domain :: "nat \<Rightarrow> (real^'n::finite) set" where
  "branch2_u_slice_domain j = {u. branch2_u_param_bounded u j}"

definition branch2_lifted_base_chart_x_map ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)) \<Rightarrow>
    ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)" where
  "branch2_lifted_base_chart_x_map \<omega>0 \<omega>s psi su =
    branch2_base_fibre_x_map \<omega>0 \<omega>s (psi (fst su), snd su)"

lemma branch2_chart1_reduced_slice_image_subset_lifted_base_charts:
  fixes C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)"
  assumes base_cover: "branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. psi i ` C i)"
  shows "branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          ` (C i \<times> branch2_u_slice_domain j))"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
  then obtain ru
    where ru_dom: "fst ru \<in> branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j"
      and xeq: "x = branch2_base_fibre_x_map \<omega>0 \<omega>s ru"
    unfolding branch2_chart1_reduced_slice_image_def by blast
  obtain i s where sC: "s \<in> C i" and r_eq: "fst ru = psi i s"
    using base_cover ru_dom by blast
  have u_dom: "snd ru \<in> branch2_u_slice_domain j"
    using ru_dom unfolding branch2_u_slice_domain_def by blast
  have su_dom: "(s, snd ru) \<in> C i \<times> branch2_u_slice_domain j"
    using sC u_dom by simp
  have "x = branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i) (s, snd ru)"
    using xeq r_eq unfolding branch2_lifted_base_chart_x_map_def
    by (simp add: branch2_base_fibre_x_map_def) 
  thus "x \<in> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
      ` (C i \<times> branch2_u_slice_domain j))"
    using su_dom by blast
qed

lemma branch2_chart2_reduced_slice_image_subset_lifted_base_charts:
  fixes C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)"
  assumes base_cover: "branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. psi i ` C i)"
  shows "branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          ` (C i \<times> branch2_u_slice_domain j))"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
  then obtain ru
    where ru_dom: "fst ru \<in> branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j"
      and xeq: "x = branch2_base_fibre_x_map \<omega>0 \<omega>s ru"
    unfolding branch2_chart2_reduced_slice_image_def by blast
  obtain i s where sC: "s \<in> C i" and r_eq: "fst ru = psi i s"
    using base_cover ru_dom by blast
  have u_dom: "snd ru \<in> branch2_u_slice_domain j"
    using ru_dom unfolding branch2_u_slice_domain_def by blast
  have su_dom: "(s, snd ru) \<in> C i \<times> branch2_u_slice_domain j"
    using sC u_dom by simp
  have "x = branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i) (s, snd ru)"
    using xeq r_eq unfolding branch2_lifted_base_chart_x_map_def
    by (metis split_pairs2) 
  thus "x \<in> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
      ` (C i \<times> branch2_u_slice_domain j))"
    using su_dom by blast
qed

theorem branchP_indep_closed_cover_core_all_of_reduced_base_chart_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> (real^2) set.
        \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
          branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. psi i ` C i)
          \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                differentiable_on (C i \<times> branch2_u_slice_domain j))
          \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                ` (C i \<times> branch2_u_slice_domain j)))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> (real^2) set.
        \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
          branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. psi i ` C i)
          \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                differentiable_on (C i \<times> branch2_u_slice_domain j))
          \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                ` (C i \<times> branch2_u_slice_domain j)))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_reduced_countable_lowdim_parametrizations
    [OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)"
    where base_cover:
        "branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. psi i ` C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
      and closed_image: "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          ` (C i \<times> branch2_u_slice_domain j))"
    using chart1[OF Gsub Gindep] by meson
  show "\<exists>C :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) set.
      \<exists>F :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
        branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. F i ` C i)
        \<and> (\<forall>i. F i differentiable_on C i) \<and> (\<forall>i. closed (F i ` C i))"
  proof (intro exI[where x = "\<lambda>i. C i \<times> branch2_u_slice_domain j"]
      exI[where x = "\<lambda>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)"] conjI)
    show "branch2_chart1_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
            ` (C i \<times> branch2_u_slice_domain j))"
      by (rule branch2_chart1_reduced_slice_image_subset_lifted_base_charts[OF base_cover])
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff .
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using closed_image .
  qed
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)"
    where base_cover:
        "branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. psi i ` C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
      and closed_image: "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          ` (C i \<times> branch2_u_slice_domain j))"
    using chart2[OF Gsub Gindep] by meson
  show "\<exists>C :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) set.
      \<exists>F :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
        branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. F i ` C i)
        \<and> (\<forall>i. F i differentiable_on C i) \<and> (\<forall>i. closed (F i ` C i))"
  proof (intro exI[where x = "\<lambda>i. C i \<times> branch2_u_slice_domain j"]
      exI[where x = "\<lambda>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)"] conjI)
    show "branch2_chart2_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
            ` (C i \<times> branch2_u_slice_domain j))"
      by (rule branch2_chart2_reduced_slice_image_subset_lifted_base_charts[OF base_cover])
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff .
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using closed_image .
  qed
qed

subsection \<open>\<section>7ab0: IFT-ready coordinates for the reduced base residuals\<close>

definition branch2_base_assoc ::
  "(((real^2) \<times> (real^'n::finite)) \<times> real)
    \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))" where
  "branch2_base_assoc r =
    (branch2_base_param_omega r,
      (branch2_base_param_t r, branch2_base_param_a r))"

definition branch2_base_unassoc ::
  "((real^2) \<times> ((real^'n::finite) \<times> real))
    \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)" where
  "branch2_base_unassoc z = ((fst z, fst (snd z)), snd (snd z))"

definition branch2_residual_to_IFT_range ::
  "real \<times> (real^'n::finite) \<Rightarrow> ((real^'n) \<times> real)" where
  "branch2_residual_to_IFT_range y = (snd y, fst y)"

definition branch2_residual_from_IFT_range ::
  "((real^'n::finite) \<times> real) \<Rightarrow> real \<times> (real^'n)" where
  "branch2_residual_from_IFT_range y = (snd y, fst y)"

definition branch2_chart1_reduced_base_IFT_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    ((real^2) \<times> ((real^'n::finite) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)" where
  "branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s z =
    branch2_residual_to_IFT_range
      (branch2_chart1_reduced_base_residual \<omega>0 \<omega>s (branch2_base_unassoc z))"

definition branch2_chart2_reduced_base_IFT_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    ((real^2) \<times> ((real^'n::finite) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)" where
  "branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s z =
    branch2_residual_to_IFT_range
      (branch2_chart2_reduced_base_residual \<omega>0 \<omega>s (branch2_base_unassoc z))"

lemma branch2_base_unassoc_assoc[simp]:
  fixes r :: "(((real^2) \<times> (real^'n::finite)) \<times> real)"
  shows "branch2_base_unassoc (branch2_base_assoc r) = r"
  unfolding branch2_base_assoc_def branch2_base_unassoc_def
    branch2_base_param_omega_def branch2_base_param_t_def branch2_base_param_a_def
  by simp

lemma branch2_base_assoc_unassoc[simp]:
  fixes z :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
  shows "branch2_base_assoc (branch2_base_unassoc z) = z"
  unfolding branch2_base_assoc_def branch2_base_unassoc_def
    branch2_base_param_omega_def branch2_base_param_t_def branch2_base_param_a_def
  by simp

lemma branch2_residual_from_to_IFT_range[simp]:
  fixes y :: "real \<times> (real^'n::finite)"
  shows "branch2_residual_from_IFT_range (branch2_residual_to_IFT_range y) = y"
  unfolding branch2_residual_to_IFT_range_def branch2_residual_from_IFT_range_def by simp

lemma branch2_residual_to_from_IFT_range[simp]:
  fixes y :: "(real^'n::finite) \<times> real"
  shows "branch2_residual_to_IFT_range (branch2_residual_from_IFT_range y) = y"
  unfolding branch2_residual_to_IFT_range_def branch2_residual_from_IFT_range_def by simp

lemma branch2_residual_to_IFT_range_zero_iff[simp]:
  "branch2_residual_to_IFT_range y = (0 :: real^'n::finite, 0) \<longleftrightarrow>
    y = (0, (0 :: real^'n))"
  unfolding branch2_residual_to_IFT_range_def
  by (cases y, simp add: conj_commute)

lemma branch2_chart1_reduced_base_IFT_residual_zero_iff:
  fixes z :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
  shows "branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0) \<longleftrightarrow>
    branch2_chart1_reduced_base_residual \<omega>0 \<omega>s (branch2_base_unassoc z)
      = (0, (0 :: real^'n))"
  unfolding branch2_chart1_reduced_base_IFT_residual_def by simp

lemma branch2_chart2_reduced_base_IFT_residual_zero_iff:
  fixes z :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
  shows "branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0) \<longleftrightarrow>
    branch2_chart2_reduced_base_residual \<omega>0 \<omega>s (branch2_base_unassoc z)
      = (0, (0 :: real^'n))"
  unfolding branch2_chart2_reduced_base_IFT_residual_def by simp

lemma branch2_chart1_reduced_base_system_assoc_iff:
  fixes r :: "(((real^2) \<times> (real^'n::finite)) \<times> real)"
  shows "r \<in> branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    branch2_base_param_omega r \<in> \<Gamma>
    \<and> branch2_base_param_bounded \<omega>0 \<omega>s r j
    \<and> branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0)"
  unfolding branch2_chart1_reduced_base_system_def
    branch2_chart1_reduced_base_IFT_residual_def
  by simp

lemma branch2_chart2_reduced_base_system_assoc_iff:
  fixes r :: "(((real^2) \<times> (real^'n::finite)) \<times> real)"
  shows "r \<in> branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    branch2_base_param_omega r \<in> \<Gamma>
    \<and> branch2_base_param_bounded \<omega>0 \<omega>s r j
    \<and> branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0)"
  unfolding branch2_chart2_reduced_base_system_def
    branch2_chart2_reduced_base_IFT_residual_def
  by simp

lemma branch2_chart1_reduced_base_IFT_residual_local_chart:
  fixes z0 :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
    and G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
  assumes zero: "branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s z0 = (0, 0)"
    and der: "\<And>z. (branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg: "surj (blinfun_apply (G' z0))"
  shows "\<exists>U u0 \<phi> g D\<phi>.
      open (U :: (real^2) set) \<and> u0 \<in> U \<and> \<phi> u0 = z0
      \<and> \<phi> differentiable_on U
      \<and> \<phi> ` U \<subseteq> {z. branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)}
      \<and> openin (top_of_set {z. branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` U)
      \<and> homeomorphism U (\<phi> ` U) \<phi> g
      \<and> (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u))
      \<and> (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u))
             = {w. blinfun_apply (G' (\<phi> u)) w = 0})"
proof -
  have zero': "branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s z0 = 0"
    using zero by (simp add: zero_prod_def)
  show ?thesis
    using regular_value_local_chart
      [where W = UNIV and p = z0
        and G = "branch2_chart1_reduced_base_IFT_residual \<omega>0 \<omega>s"
        and G' = G',
        OF open_UNIV UNIV_I zero']
      der cont reg
    by (auto simp: zero_prod_def)
qed

lemma branch2_chart2_reduced_base_IFT_residual_local_chart:
  fixes z0 :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
    and G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
  assumes zero: "branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s z0 = (0, 0)"
    and der: "\<And>z. (branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg: "surj (blinfun_apply (G' z0))"
  shows "\<exists>U u0 \<phi> g D\<phi>.
      open (U :: (real^2) set) \<and> u0 \<in> U \<and> \<phi> u0 = z0
      \<and> \<phi> differentiable_on U
      \<and> \<phi> ` U \<subseteq> {z. branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)}
      \<and> openin (top_of_set {z. branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` U)
      \<and> homeomorphism U (\<phi> ` U) \<phi> g
      \<and> (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u))
      \<and> (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u))
             = {w. blinfun_apply (G' (\<phi> u)) w = 0})"
proof -
  have zero': "branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s z0 = 0"
    using zero by (simp add: zero_prod_def)
  show ?thesis
    using regular_value_local_chart
      [where W = UNIV and p = z0
        and G = "branch2_chart2_reduced_base_IFT_residual \<omega>0 \<omega>s"
        and G' = G',
        OF open_UNIV UNIV_I zero']
      der cont reg
    by (auto simp: zero_prod_def)
qed

subsection \<open>\<section>7ab: the remaining rank/IFT obligation\<close>

definition branch2_chart1_reduced_base_regular_rank ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart1_reduced_base_regular_rank V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<forall>r\<in>branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
      \<exists>D :: (((real^2) \<times> (real^'n)) \<times> real) \<Rightarrow> real \<times> (real^'n).
        ((branch2_chart1_reduced_base_residual \<omega>0 \<omega>s) has_derivative D) (at r)
        \<and> surj D)"

definition branch2_chart2_reduced_base_regular_rank ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart2_reduced_base_regular_rank V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<forall>r\<in>branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
      \<exists>D :: (((real^2) \<times> (real^'n)) \<times> real) \<Rightarrow> real \<times> (real^'n).
        ((branch2_chart2_reduced_base_residual \<omega>0 \<omega>s) has_derivative D) (at r)
        \<and> surj D)"

definition branch2_reduced_base_regular_rank_all ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow>
    real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branch2_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
    (\<forall>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
      branch2_chart1_reduced_base_regular_rank V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_reduced_base_regular_rank V \<omega>0 \<omega>s \<Gamma> j)"

definition branch2_chart1_reduced_base_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart1_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j))))"

definition branch2_chart2_reduced_base_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart2_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j))))"

definition branch2_reduced_base_IFT_parametrizations_all ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow>
    real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branch2_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
    (\<forall>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
      branch2_chart1_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j)"

definition branch2_chart1_reduced_base_assoc_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart1_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>\<phi> :: nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
        branch2_base_assoc ` branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              ` (C i \<times> branch2_u_slice_domain j))))"

definition branch2_chart2_reduced_base_assoc_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart2_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>\<phi> :: nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
        branch2_base_assoc ` branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              ` (C i \<times> branch2_u_slice_domain j))))"

definition branch2_reduced_base_assoc_IFT_parametrizations_all ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow>
    real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branch2_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
    (\<forall>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
      branch2_chart1_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j)"

lemma branch2_chart1_reduced_base_IFT_parametrizations_of_assoc:
  fixes V :: "((real^2)^'n::finite) set"
  assumes assoc: "branch2_chart1_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
  shows "branch2_chart1_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
proof -
  have assoc_ex: "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>\<phi> :: nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
        branch2_base_assoc ` branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              ` (C i \<times> branch2_u_slice_domain j)))"
    using assoc
    unfolding branch2_chart1_reduced_base_assoc_IFT_parametrizations_def .
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and \<phi> :: "nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))"
    where assoc_cover:
        "branch2_base_assoc ` branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
          (\<lambda>s. branch2_base_unassoc (\<phi> i s))
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
      and closed_image: "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
          (\<lambda>s. branch2_base_unassoc (\<phi> i s))
          ` (C i \<times> branch2_u_slice_domain j))"
    using assoc_ex by auto
  have base_cover: "branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
  proof 
    fix r :: "(((real^2) \<times> (real^'n)) \<times> real)"
    assume rin: "r \<in> branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
    then have "branch2_base_assoc r \<in>
        branch2_base_assoc ` branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
      by blast
    then obtain i s where sC: "s \<in> C i" and seq: "branch2_base_assoc r = \<phi> i s"
      using assoc_cover by blast
    have "r = branch2_base_unassoc (\<phi> i s)"
      using seq by (metis branch2_base_unassoc_assoc)
    thus "r \<in> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
      using sC by blast
  qed
  show ?thesis
    unfolding branch2_chart1_reduced_base_IFT_parametrizations_def
  proof (intro exI[where x = C]
      exI[where x = "\<lambda>i s. branch2_base_unassoc (\<phi> i s)"] conjI)
    show "branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
      using base_cover .
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
        ((\<lambda>i s. branch2_base_unassoc (\<phi> i s)) i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff by simp
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
        ((\<lambda>i s. branch2_base_unassoc (\<phi> i s)) i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using closed_image by simp
  qed
qed

lemma branch2_chart2_reduced_base_IFT_parametrizations_of_assoc:
  fixes V :: "((real^2)^'n::finite) set"
  assumes assoc: "branch2_chart2_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
  shows "branch2_chart2_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
proof -
  have assoc_ex: "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>\<phi> :: nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
        branch2_base_assoc ` branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              ` (C i \<times> branch2_u_slice_domain j)))"
    using assoc
    unfolding branch2_chart2_reduced_base_assoc_IFT_parametrizations_def .
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and \<phi> :: "nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))"
    where assoc_cover:
        "branch2_base_assoc ` branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
          (\<lambda>s. branch2_base_unassoc (\<phi> i s))
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
      and closed_image: "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
          (\<lambda>s. branch2_base_unassoc (\<phi> i s))
          ` (C i \<times> branch2_u_slice_domain j))"
    using assoc_ex by auto
  have base_cover: "branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
  proof
    fix r :: "(((real^2) \<times> (real^'n)) \<times> real)"
    assume rin: "r \<in> branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
    then have "branch2_base_assoc r \<in>
        branch2_base_assoc ` branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
      by blast
    then obtain i s where sC: "s \<in> C i" and seq: "branch2_base_assoc r = \<phi> i s"
      using assoc_cover by blast
    have "r = branch2_base_unassoc (\<phi> i s)"
      using seq by (metis branch2_base_unassoc_assoc)
    thus "r \<in> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
      using sC by blast
  qed
  show ?thesis
    unfolding branch2_chart2_reduced_base_IFT_parametrizations_def
  proof (intro exI[where x = C]
      exI[where x = "\<lambda>i s. branch2_base_unassoc (\<phi> i s)"] conjI)
    show "branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
      using base_cover .
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
        ((\<lambda>i s. branch2_base_unassoc (\<phi> i s)) i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff by simp
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
        ((\<lambda>i s. branch2_base_unassoc (\<phi> i s)) i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using closed_image by simp
  qed
qed

lemma branch2_reduced_base_IFT_parametrizations_all_of_assoc:
  assumes assoc: "branch2_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branch2_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branch2_reduced_base_IFT_parametrizations_all_def
proof (intro allI impI conjI)
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  have both: "branch2_chart1_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
    using assoc Gsub Gindep
    unfolding branch2_reduced_base_assoc_IFT_parametrizations_all_def by blast
  show "branch2_chart1_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
    by (rule branch2_chart1_reduced_base_IFT_parametrizations_of_assoc[OF conjunct1[OF both]])
  show "branch2_chart2_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
    by (rule branch2_chart2_reduced_base_IFT_parametrizations_of_assoc[OF conjunct2[OF both]])
qed

theorem branchP_indep_closed_cover_core_all_of_reduced_base_IFT_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and ift: "branch2_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_reduced_base_chart_parametrizations
    [OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart1_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j)))"
    using ift Gsub Gindep
    unfolding branch2_reduced_base_IFT_parametrizations_all_def
      branch2_chart1_reduced_base_IFT_parametrizations_def
    by blast
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart2_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j)))"
    using ift Gsub Gindep
    unfolding branch2_reduced_base_IFT_parametrizations_all_def
      branch2_chart2_reduced_base_IFT_parametrizations_def
    by blast
qed

theorem branchP_indep_closed_cover_core_all_of_reduced_base_assoc_IFT_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and assoc: "branch2_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_reduced_base_IFT_parametrizations
    [OF card4 pf])
  show "branch2_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
    by (rule branch2_reduced_base_IFT_parametrizations_all_of_assoc[OF assoc])
qed

theorem branchP_indep_closed_cover_core_all_of_reduced_base_regular_rank_and_assoc_IFT_chart_theorem:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and regular_rank: "branch2_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
    and rank_to_assoc:
      "branch2_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s \<Longrightarrow>
        branch2_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_reduced_base_assoc_IFT_parametrizations
    [OF card4 pf])
  show "branch2_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
    by (rule rank_to_assoc[OF regular_rank])
qed

theorem branchP_indep_closed_cover_core_all_of_reduced_base_regular_rank_and_IFT_chart_theorem:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and regular_rank: "branch2_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
    and rank_to_ift:
      "branch2_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s \<Longrightarrow>
        branch2_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof -
  have ift: "branch2_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
    by (rule rank_to_ift[OF regular_rank])
  show ?thesis
    by (rule branchP_indep_closed_cover_core_all_of_reduced_base_IFT_parametrizations
        [OF card4 pf ift])
qed

subsection \<open>\<section>7ac: repaired reduced-base residual after the radial-sum degeneracy\<close>

text \<open>
  The residual in \<section>7ab keeps all radial scalar slots.  The semi-formal
  audit in Sketch.md \<section>7n found the exact identity that their sum is
  identically zero, so the old full-rank target is too strong.  This section
  names the repaired target: one fixed radial slot is replaced by the
  determinant-free reduced \<open>gradU\<close> scalar, and the bounded pieces carry the
  nonzero Jacobian determinant already present in @{const BadXGW}.
\<close>

definition branch2_base_param_bounded_det ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real) \<Rightarrow>
    nat \<Rightarrow> bool" where
  "branch2_base_param_bounded_det \<omega>0 \<omega>s r j \<longleftrightarrow>
    branch2_base_param_bounded \<omega>0 \<omega>s r j
    \<and> 1 / real (Suc j)
        \<le> abs (det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))))"

definition branch2_chart_param_bounded_det ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    (((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real) \<Rightarrow>
    nat \<Rightarrow> bool" where
  "branch2_chart_param_bounded_det \<omega>0 \<omega>s q j \<longleftrightarrow>
    branch2_chart_param_bounded \<omega>0 \<omega>s q j
    \<and> 1 / real (Suc j)
        \<le> abs (det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q))))"

lemma branch2_base_param_bounded_det_imp_cvec_nonzero:
  assumes bounded: "branch2_base_param_bounded_det \<omega>0 \<omega>s r j"
  shows "cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0"
proof -
  have cpos: "0 < cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r)
      \<bullet> cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r)"
    using bounded
    unfolding branch2_base_param_bounded_det_def branch2_base_param_bounded_def
    by (smt (verit, best) divide_pos_pos of_nat_0_less_iff zero_less_Suc
        less_le_trans)
  show ?thesis
    using cpos by auto
qed

lemma branch2_base_param_bounded_det_imp_Dcvec_det_nonzero:
  assumes bounded: "branch2_base_param_bounded_det \<omega>0 \<omega>s r j"
  shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0"
proof -
  have detpos:
    "0 < abs (det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))))"
    using bounded
    unfolding branch2_base_param_bounded_det_def
    by (smt (verit, best) divide_pos_pos of_nat_0_less_iff zero_less_Suc
        less_le_trans)
  show ?thesis
    using detpos by auto
qed

lemma branch2_chart_param_bounded_det_imp_base_u_bounded_det:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes bounded: "branch2_chart_param_bounded_det \<omega>0 \<omega>s q j"
  shows "branch2_base_param_bounded_det \<omega>0 \<omega>s (branch2_base_param_of_chart q) j
      \<and> branch2_u_param_bounded (branch2_chart_param_u q) j"
proof -
  have chart_bounded: "branch2_chart_param_bounded \<omega>0 \<omega>s q j"
    using bounded unfolding branch2_chart_param_bounded_det_def by blast
  have base_u: "branch2_base_param_bounded \<omega>0 \<omega>s (branch2_base_param_of_chart q) j
      \<and> branch2_u_param_bounded (branch2_chart_param_u q) j"
    by (rule branch2_chart_param_bounded_imp_base_u_bounded[OF chart_bounded])
  have det_bound: "1 / real (Suc j)
      \<le> abs (det (matrix (Dcvec_dip \<omega>0 \<omega>s
          (branch2_base_param_omega (branch2_base_param_of_chart q)))))"
    using bounded
    unfolding branch2_chart_param_bounded_det_def branch2_base_param_of_chart_def
      branch2_base_param_omega_def branch2_chart_param_omega_def
    by simp
  show ?thesis
    using base_u det_bound
    unfolding branch2_base_param_bounded_det_def by blast
qed

definition branch2_repair_slot :: "'n::finite" where
  "branch2_repair_slot = (SOME m. True)"

definition branch2_cross_combo ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "branch2_cross_combo \<omega>0 \<omega>s \<omega> =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega>;
         \<gamma>1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1);
         \<gamma>2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)
     in (\<gamma>2 \<bullet> perp2 c) *\<^sub>R \<gamma>1 - (\<gamma>1 \<bullet> perp2 c) *\<^sub>R \<gamma>2)"

lemma branch2_cross_combo_perp:
  "branch2_cross_combo \<omega>0 \<omega>s \<omega> \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
  unfolding branch2_cross_combo_def Let_def
  by (simp add: inner_diff_left inner_scaleR_left algebra_simps)

subsection \<open>\<section>7ah: division-free rewrite toward global C1 smoothness\<close>

text \<open>
  Both repaired residuals contain terms of the shape
  \<open>(t\<^sub>m / (c \<bullet> c)) * (L \<bullet> c)\<close>, which is a genuine \<open>0/0\<close> at \<open>c = cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>
  under Isabelle's \<open>x/0 = 0\<close> convention.  For \<open>branch2_radial_scalar_reduced_eq\<close> an
  explicit outer \<open>(c \<bullet> c)\<close> factor cancels this cleanly for *any* \<open>L\<close> (the term is then
  \<open>0\<close> at \<open>c = 0\<close> on both sides, since \<open>L \<bullet> c = L \<bullet> 0 = 0\<close> there too).  For
  \<open>branch2_reduced_gradU_scalar\<close> (the repair-slot \<open>R\<^sup>*\<close>) there is no such outer factor,
  and \<open>L \<bullet> c\<close> for \<open>L = branch2_cross_combo\<close> is a genuine quadratic vanishing at
  \<open>c = 0\<close> --- the fix is the exact 2D Binet-Cauchy identity
  \<open>branch2_cross_combo \<omega>0 \<omega>s \<omega> \<bullet> c = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (c \<bullet> c)\<close>,
  which exposes the missing \<open>(c \<bullet> c)\<close> factor and lets the same cancellation apply.
\<close>

lemma cc_times_div_times_Lc_eq:
  fixes c L :: "real^2" and x :: real
  shows "(c \<bullet> c) * (x / (c \<bullet> c)) * (L \<bullet> c) = x * (L \<bullet> c)"
proof (cases "c \<bullet> c = 0")
  case True
  hence "c = 0" by simp
  hence "L \<bullet> c = 0" by simp
  with True show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed

lemma branch2_cross_combo_inner_c_eq_det:
  "branch2_cross_combo \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>
    = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)"
  unfolding branch2_cross_combo_def Let_def perp2_def
  by (simp add: det_2 matrix_def inner_vec_def sum_2 algebra_simps)

definition A_t_weighted_moment :: "real^('n::finite) \<Rightarrow> complex" where
  "A_t_weighted_moment t = (\<Sum>m\<in>UNIV. of_real (vec_nth t m) * phase_t t m)"

text \<open>
  The unconditional (no \<open>c \<noteq> 0\<close> needed!) division-free identity: multiplying
  \<open>M12_tu_special_moment\<close> by the very \<open>(c \<bullet> c)\<close> that appears in its own raw
  \<open>t\<^sub>m/(c \<bullet> c)\<close> denominator cancels it for \<^emph>\<open>any\<close> \<open>L\<close>, not just
  \<open>branch2_cross_combo\<close> --- at \<open>c = 0\<close> both sides are \<open>0\<close> trivially
  (\<open>L \<bullet> 0 = 0\<close> regardless of \<open>L\<close>).  This is exactly what makes
  \<open>branch2_radial_scalar_reduced_eq\<close> (whose \<open>M12\<close> term already carries an
  explicit outer \<open>(c \<bullet> c)\<close> factor) smooth everywhere without needing to
  touch its definition at all.
\<close>

lemma cc_times_M12_tu_special_moment_eq:
  fixes t :: "real^('n::finite)" and c L :: "real^2"
  shows "of_real (c \<bullet> c) * M12_tu_special_moment c t L
    = of_real (L \<bullet> c) * A_t_weighted_moment t"
proof (cases "c \<bullet> c = 0")
  case True
  hence c0: "c = 0" by simp
  hence "L \<bullet> c = 0" by simp
  moreover have "M12_tu_special_moment c t L = 0"
    unfolding M12_tu_special_moment_def using c0 by simp
  ultimately show ?thesis using True by simp
next
  case False
  have step: "of_real (c \<bullet> c) * (of_real ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)) * phase_t t m)
      = of_real (L \<bullet> c) * (of_real (vec_nth t m) * phase_t t m)" for m
  proof -
    have "(c \<bullet> c) * ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)) = vec_nth t m * (L \<bullet> c)"
      using cc_times_div_times_Lc_eq[of c "vec_nth t m" L] by (simp add: mult.assoc)
    hence "of_real ((c \<bullet> c) * ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)))
        = of_real (vec_nth t m * (L \<bullet> c))"
      by simp
    thus ?thesis
      by (simp add: of_real_mult mult.assoc)
  qed
  have "of_real (c \<bullet> c) * M12_tu_special_moment c t L
      = (\<Sum>m\<in>UNIV. of_real (c \<bullet> c) * (of_real ((vec_nth t m / (c \<bullet> c)) * (L \<bullet> c)) * phase_t t m))"
    unfolding M12_tu_special_moment_def
    by (simp only: sum_distrib_left)
  also have "\<dots> = (\<Sum>m\<in>UNIV. of_real (L \<bullet> c) * (of_real (vec_nth t m) * phase_t t m))"
    by (rule sum.cong[OF refl], rule step)
  also have "\<dots> = of_real (L \<bullet> c) * A_t_weighted_moment t"
    unfolding A_t_weighted_moment_def by (simp only: sum_distrib_left)
  finally show ?thesis .
qed

lemma branch2_radial_scalar_reduced_eq_smooth_form:
  fixes t :: "real^('n::finite)" and ell :: "real^2"
  shows "branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega>;
         L = branch2_ell_combo \<omega>0 \<omega>s \<omega> ell;
         A = A_t_moment t;
         AW = A_t_weighted_moment t;
         ph = phase_t t m
     in branch2_ell_gain_deriv \<omega> ell * (2 * (c \<bullet> c) * Im (cnj A * ph))
        + gain_dip \<omega> * (2 * (L \<bullet> c) * Re (cnj ph * AW)
            + 2 * (L \<bullet> c) * Im (cnj A * ph)
            - 2 * vec_nth t m * (L \<bullet> c) * Re (cnj A * ph)))"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?L = "branch2_ell_combo \<omega>0 \<omega>s \<omega> ell"
  let ?A = "A_t_moment t"
  let ?AW = "A_t_weighted_moment t"
  let ?ph = "phase_t t m"
  let ?ML = "M12_tu_special_moment ?c t ?L"
  have cc_ML: "(?c \<bullet> ?c) * ?ML = of_real (?L \<bullet> ?c) * ?AW"
    by (rule cc_times_M12_tu_special_moment_eq)
  have cc_ML_Re: "(?c \<bullet> ?c) * Re ?ML = (?L \<bullet> ?c) * Re ?AW"
    using arg_cong[OF cc_ML, of Re] by simp
  have cc_ML_Im: "(?c \<bullet> ?c) * Im ?ML = (?L \<bullet> ?c) * Im ?AW"
    using arg_cong[OF cc_ML, of Im] by simp
  have div_term: "(?c \<bullet> ?c) * ((vec_nth t m / (?c \<bullet> ?c)) * (?L \<bullet> ?c)) = vec_nth t m * (?L \<bullet> ?c)"
    using cc_times_div_times_Lc_eq[of ?c "vec_nth t m" ?L] by (simp add: mult.assoc)
  show ?thesis
    unfolding branch2_radial_scalar_reduced_eq_def Let_def
    by (simp add: cc_ML_Re cc_ML_Im div_term algebra_simps
        del: div_by_1 mult_cancel_left mult_cancel_left1 mult_cancel_left2)
qed

lemma M12_tu_special_moment_cross_combo_eq:
  fixes t :: "real^('n::finite)"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "M12_tu_special_moment (cvec_dip \<omega>0 \<omega>s \<omega>) t (branch2_cross_combo \<omega>0 \<omega>s \<omega>)
    = of_real (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))) * A_t_weighted_moment t"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?L = "branch2_cross_combo \<omega>0 \<omega>s \<omega>"
  let ?d = "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))"
  have cc_ne: "?c \<bullet> ?c \<noteq> 0"
    using cnz by simp
  have Lc: "?L \<bullet> ?c = ?d * (?c \<bullet> ?c)"
    by (rule branch2_cross_combo_inner_c_eq_det)
  have "(vec_nth t m / (?c \<bullet> ?c)) * (?L \<bullet> ?c) = ?d * vec_nth t m" for m
  proof -
    have "(vec_nth t m / (?c \<bullet> ?c)) * (?L \<bullet> ?c)
        = (vec_nth t m / (?c \<bullet> ?c)) * (?d * (?c \<bullet> ?c))"
      by (simp add: Lc)
    also have "\<dots> = ?d * ((?c \<bullet> ?c) * (vec_nth t m / (?c \<bullet> ?c)))"
      by (simp add: algebra_simps)
    also have "\<dots> = ?d * vec_nth t m"
      using cc_ne by simp
    finally show ?thesis .
  qed
  thus ?thesis
    unfolding M12_tu_special_moment_def A_t_weighted_moment_def
    by (simp only: of_real_mult sum_distrib_left mult.assoc)
qed

subsection \<open>\<section>7ai: the Ck_on smoothness toolkit for the repaired residuals\<close>

text \<open>
  Every primitive the two repaired residuals are built from is globally
  \<open>C\<^sup>\<infinity>\<close> (in fact real-analytic): \<open>gdip\<close>, \<open>gain_dip\<close>, \<open>cvec_dip\<close> are already
  \<open>higher_differentiable_on UNIV \<dots> n\<close> for every \<open>n\<close> on the heap
  (\<open>gdip_higher_differentiable_on\<close>, \<open>gain_dip_higher_differentiable_on\<close>,
  \<open>cvec_dip_higher_differentiable_on\<close>); \<open>Dcvec_dip\<close> and directional derivatives
  of \<open>gdip\<close> inherit this by peeling one \<open>Ck_at (Suc n)\<close> layer via
  @{thm Ck_at.simps(2)}.  Combined with the existing \<open>Ck_on\<close> calculus
  (\<open>Ck_on_add/sub/mult/inner/compose/sum\<close>), this gives Ck\<open>_on\<close> for every
  composite quantity (\<open>branch2_ell_combo\<close>, \<open>branch2_cross_combo\<close>,
  \<open>branch2_special_coeffs\<close>, \<open>det (matrix (Dcvec_dip \<dots>))\<close>,
  \<open>branch2_ell_gain_deriv\<close>, \<open>phase_t\<close>, \<open>A_t_moment\<close>, \<open>A_t_weighted_moment\<close>).
\<close>

lemma gdip_Ck_on_n: "Ck_on n gdip UNIV"
  using gdip_higher_differentiable_on[of n]
  by (simp add: Ck_on_iff_higher_differentiable_on)

lemma gain_dip_Ck_on_n: "Ck_on n gain_dip UNIV"
  using gain_dip_higher_differentiable_on[of n]
  by (simp add: Ck_on_iff_higher_differentiable_on)

lemma cvec_dip_Ck_on_n:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "Ck_on n (cvec_dip \<omega>0 \<omega>s) UNIV"
  using cvec_dip_higher_differentiable_on[of \<omega>0 \<omega>s n]
  by (simp add: Ck_on_iff_higher_differentiable_on)

lemma frechet_derivative_gdip_dir_Ck_on:
  fixes v :: real
  shows "Ck_on n (\<lambda>\<theta>. frechet_derivative gdip (at \<theta>) v) UNIV"
proof -
  have Cat: "Ck_at (Suc n) gdip x" for x
    using gdip_Ck_on_n[of "Suc n"] unfolding Ck_on_def by blast
  have unfold: "Ck_at (Suc n) gdip x =
      ((\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at n gdip y))
       \<and> gdip differentiable (at x)
       \<and> (\<forall>v. Ck_at n (\<lambda>y. frechet_derivative gdip (at y) v) x))" for x
    by (rule Ck_at.simps(2))
  have step: "Ck_at n (\<lambda>y. frechet_derivative gdip (at y) v) x" for x
    using Cat[of x] unfold[of x] by blast
  show ?thesis
    unfolding Ck_on_def using step open_UNIV by blast
qed

lemma Dcvec_dip_dir_Ck_on:
  fixes \<omega>0 \<omega>s h :: "real^2"
  shows "Ck_on n (\<lambda>\<omega>. Dcvec_dip \<omega>0 \<omega>s \<omega> h) UNIV"
proof -
  have Cat: "Ck_at (Suc n) (cvec_dip \<omega>0 \<omega>s) x" for x
    using cvec_dip_Ck_on_n[of "Suc n" \<omega>0 \<omega>s]
    unfolding Ck_on_def by blast
  have unfold: "Ck_at (Suc n) (cvec_dip \<omega>0 \<omega>s) x =
      ((\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at n (cvec_dip \<omega>0 \<omega>s) y))
       \<and> (cvec_dip \<omega>0 \<omega>s) differentiable (at x)
       \<and> (\<forall>v. Ck_at n (\<lambda>y. frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at y) v) x))" for x
    by (rule Ck_at.simps(2))
  have step: "Ck_at n (\<lambda>y. frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at y) h) x" for x
    using Cat[of x] unfold[of x] by blast
  hence step2: "Ck_at n (\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) x" for x
    using frechet_derivative_cvec_dip by (simp add: fun_eq_iff)
  show ?thesis
    unfolding Ck_on_def using step2 open_UNIV by blast
qed

lemma vec_nth_Ck_on_n:
  fixes j :: "'k::finite"
  shows "Ck_on n (\<lambda>x :: real^'k. vec_nth x j) UNIV"
proof -
  have "(\<lambda>x :: real^'k. vec_nth x j) = (\<lambda>x. inner x (axis j 1))"
    by (rule ext) (simp add: inner_axis)
  thus ?thesis
    using Ck_on_inner[OF Ck_on_id[OF open_UNIV] Ck_on_const[where c = "axis j 1" and U = UNIV, OF open_UNIV]]
    by simp
qed

lemma perp2_Ck_on_n: "Ck_on n perp2 UNIV"
  using bounded_linear.higher_differentiable_on[OF bounded_linear_perp2, of UNIV n]
  by (simp add: Ck_on_iff_higher_differentiable_on)

lemma branch2_ell_combo_Ck_on_n:
  fixes \<omega>0 \<omega>s :: "real^2" and ell :: "real^2"
  shows "Ck_on n (\<lambda>\<omega>. branch2_ell_combo \<omega>0 \<omega>s \<omega> ell) UNIV"
  unfolding branch2_ell_combo_def
  by (intro Ck_on_add Ck_on_scaleR Dcvec_dip_dir_Ck_on Ck_on_const open_UNIV)

lemma Dcvec_dip_dir_component_Ck_on_n:
  fixes \<omega>0 \<omega>s h :: "real^2" and j :: 2
  shows "Ck_on n (\<lambda>\<omega>. vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> h) j) UNIV"
proof (rule Ck_on_compose[OF vec_nth_Ck_on_n Dcvec_dip_dir_Ck_on])
  show "\<And>y :: real^2. y \<in> UNIV \<Longrightarrow> Dcvec_dip \<omega>0 \<omega>s y h \<in> UNIV" by simp
qed

lemma frechet_derivative_gdip_dir_proj_Ck_on_n:
  fixes v :: real
  shows "Ck_on n (\<lambda>\<omega>::real^2. frechet_derivative gdip (at (vec_nth \<omega> 1)) v) UNIV"
proof (rule Ck_on_compose[OF frechet_derivative_gdip_dir_Ck_on vec_nth_Ck_on_n[where 'k = 2]])
  show "\<And>\<omega> :: real^2. \<omega> \<in> UNIV \<Longrightarrow> vec_nth \<omega> 1 \<in> (UNIV :: real set)" by simp
qed

lemma perp2_cvec_dip_Ck_on_n:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "Ck_on n (\<lambda>\<omega>. perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)) UNIV"
proof (rule Ck_on_compose[OF perp2_Ck_on_n cvec_dip_Ck_on_n])
  show "\<And>y :: real^2. y \<in> UNIV \<Longrightarrow> cvec_dip \<omega>0 \<omega>s y \<in> UNIV" by simp
qed

text \<open>
  The project's \<open>Ck_on_scaleR\<close>/\<open>Ck_on_mult\<close> wrappers only cover a
  \<^emph>\<open>constant\<close> scalar / real-valued factors.  The underlying AFP fact
  \<open>bounded_bilinear.higher_differentiable_on\<close> is fully general (any bounded
  bilinear operator, including a \<^emph>\<open>varying\<close> real scalar times a vector, or
  multiplication in any \<open>real_normed_algebra\<close> such as \<open>complex\<close>); these two
  wrappers expose that generality for \<open>Ck_on\<close>.
\<close>

lemma Ck_on_scaleR_fun:
  fixes c :: "'a::real_normed_vector \<Rightarrow> real" and f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "Ck_on k c U" and "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. c y *\<^sub>R f y) U"
proof -
  have oU: "open U" using assms(1) by (simp add: Ck_on_def)
  have hc: "higher_differentiable_on U c k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have hf: "higher_differentiable_on U f k"
    using assms(2) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U (\<lambda>y. c y *\<^sub>R f y) k"
    using higher_differentiable_on_scaleR[OF hc hf oU] .
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_mult_alg:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y * g y) U"
proof -
  have oU: "open U" using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have hg: "higher_differentiable_on U g k"
    using assms(2) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U (\<lambda>y. f y * g y) k"
    using higher_differentiable_on_mult[OF hf hg oU] .
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma det_matrix_Dcvec_dip_Ck_on_n:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "Ck_on n (\<lambda>\<omega>. det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))) UNIV"
proof -
  have eq: "\<And>\<omega>. det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) =
      vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1)) 1
        * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2
      - vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1
        * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1)) 2"
    by (simp add: det_2 matrix_def)
  show ?thesis
    unfolding eq
    by (intro Ck_on_sub Ck_on_mult Dcvec_dip_dir_component_Ck_on_n)
qed

lemma branch2_cross_combo_Ck_on_n:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "Ck_on n (\<lambda>\<omega>. branch2_cross_combo \<omega>0 \<omega>s \<omega>) UNIV"
  unfolding branch2_cross_combo_def Let_def
  by (intro Ck_on_sub Ck_on_scaleR_fun Ck_on_inner Dcvec_dip_dir_Ck_on
      perp2_cvec_dip_Ck_on_n; simp)

lemma branch2_ell_gain_deriv_Ck_on_n:
  fixes ell :: "real^2"
  shows "Ck_on n (\<lambda>\<omega>. branch2_ell_gain_deriv \<omega> ell) UNIV"
proof -
  have eq: "\<And>\<omega>. branch2_ell_gain_deriv \<omega> ell =
      vec_nth ell 1 * frechet_derivative gdip (at (vec_nth \<omega> 1)) 1
      + vec_nth ell 2 * frechet_derivative gdip (at (vec_nth \<omega> 1)) 0"
    unfolding branch2_ell_gain_deriv_def
    by (simp add: inner_vec_def sum_2 axis_def)
  show ?thesis
    unfolding eq
    by (intro Ck_on_add Ck_on_mult Ck_on_const frechet_derivative_gdip_dir_proj_Ck_on_n
        open_UNIV)
qed

text \<open>
  \<^bold>\<open>Division-free by construction.\<close>  The raw \<open>M12_tu_special_moment c t L\<close>
  formula (with \<open>L = branch2_cross_combo\<close>) hides a genuine \<open>0/0\<close> at
  \<open>c = cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>: Isabelle's \<open>x/0 = 0\<close> convention silently
  returns \<open>0\<close> there, while the true (limiting) value is
  \<open>det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))\<close> times a nonzero factor whenever that
  determinant is nonzero --- a genuine jump discontinuity, not a formalization
  nicety.  \<open>branch2_cross_combo_inner_c_eq_det\<close> exposes the missing
  \<open>(c \<bullet> c)\<close> factor exactly, so we define \<open>R\<^sup>*\<close> directly via the smooth
  \<open>det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * Im (cnj A * A_t_weighted_moment t)\<close>
  form; \<open>branch2_reduced_gradU_scalar_eq_gradU_cross\<close> below reconnects this
  to the gradU cross-formula exactly as before whenever \<open>c \<noteq> 0\<close> (the only
  regime the repaired pipeline ever uses).
\<close>

definition branch2_reduced_gradU_scalar ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real) \<Rightarrow> real" where
  "branch2_reduced_gradU_scalar \<omega>0 \<omega>s r =
    (let \<omega> = branch2_base_param_omega r;
         t = branch2_base_param_t r;
         A = A_t_moment t;
         AW = A_t_weighted_moment t;
         \<gamma>1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1);
         \<gamma>2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1);
         c = cvec_dip \<omega>0 \<omega>s \<omega>;
         p1 = frechet_derivative gdip (at (vec_nth \<omega> 1))
                (vec_nth (axis (1::2) 1) 1);
         p2 = frechet_derivative gdip (at (vec_nth \<omega> 1))
                (vec_nth (axis (2::2) 1) 1);
         d = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
     in ((\<gamma>2 \<bullet> perp2 c) * p1 - (\<gamma>1 \<bullet> perp2 c) * p2) * (cmod A)\<^sup>2
        + gain_dip \<omega> * (2 * d * Re (cnj A * ((- \<i>) * AW))))"

lemma branch2_reduced_gradU_scalar_eq_raw_M12_form:
  fixes r :: "(((real^2) \<times> (real^'n::finite)) \<times> real)"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0"
  shows "branch2_reduced_gradU_scalar \<omega>0 \<omega>s r =
    (let \<omega> = branch2_base_param_omega r;
         t = branch2_base_param_t r;
         c = cvec_dip \<omega>0 \<omega>s \<omega>;
         A = A_t_moment t;
         \<gamma>1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1);
         \<gamma>2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1);
         p1 = frechet_derivative gdip (at (vec_nth \<omega> 1))
                (vec_nth (axis (1::2) 1) 1);
         p2 = frechet_derivative gdip (at (vec_nth \<omega> 1))
                (vec_nth (axis (2::2) 1) 1);
         L = branch2_cross_combo \<omega>0 \<omega>s \<omega>
     in ((\<gamma>2 \<bullet> perp2 c) * p1 - (\<gamma>1 \<bullet> perp2 c) * p2) * (cmod A)\<^sup>2
        + gain_dip \<omega> * (2 * Re (cnj A * ((- \<i>) * M12_tu_special_moment c t L))))"
proof -
  let ?\<omega> = "branch2_base_param_omega r"
  let ?t = "branch2_base_param_t r"
  let ?c = "cvec_dip \<omega>0 \<omega>s ?\<omega>"
  let ?A = "A_t_moment ?t"
  let ?AW = "A_t_weighted_moment ?t"
  let ?L = "branch2_cross_combo \<omega>0 \<omega>s ?\<omega>"
  let ?d = "det (matrix (Dcvec_dip \<omega>0 \<omega>s ?\<omega>))"
  have M12: "M12_tu_special_moment ?c ?t ?L = of_real ?d * ?AW"
    by (rule M12_tu_special_moment_cross_combo_eq[OF cnz])
  have Re_eq: "Re (cnj ?A * ((- \<i>) * M12_tu_special_moment ?c ?t ?L))
      = ?d * Re (cnj ?A * ((- \<i>) * ?AW))"
  proof -
    have "Re (cnj ?A * ((- \<i>) * M12_tu_special_moment ?c ?t ?L))
        = Re (cnj ?A * ((- \<i>) * (of_real ?d * ?AW)))"
      by (simp add: M12)
    also have "\<dots> = Re (of_real ?d * (cnj ?A * ((- \<i>) * ?AW)))"
      by (simp add: algebra_simps)
    also have "\<dots> = ?d * Re (cnj ?A * ((- \<i>) * ?AW))"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding branch2_reduced_gradU_scalar_def Let_def Re_eq
    by simp
qed

lemma branch2_reduced_gradU_scalar_eq_gradU_cross:
  fixes t u :: "real^'n::finite"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "branch2_reduced_gradU_scalar \<omega>0 \<omega>s ((\<omega>, t), a) =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega>;
         \<gamma>1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1);
         \<gamma>2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1);
         x = tu_param_map c t u
     in (\<gamma>2 \<bullet> perp2 c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1)
        - (\<gamma>1 \<bullet> perp2 c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2))"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?\<gamma>1 = "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1)"
  let ?\<gamma>2 = "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)"
  let ?L = "branch2_cross_combo \<omega>0 \<omega>s \<omega>"
  let ?A = "A_t_moment t"
  let ?M1 = "M1_tu_moment ?c t u"
  let ?M2 = "M2_tu_moment ?c t u"
  let ?M\<gamma>1 = "of_real (vec_nth ?\<gamma>1 1) * ?M1 + of_real (vec_nth ?\<gamma>1 2) * ?M2"
  let ?M\<gamma>2 = "of_real (vec_nth ?\<gamma>2 1) * ?M1 + of_real (vec_nth ?\<gamma>2 2) * ?M2"
  have Mcombo: "of_real (vec_nth ?L 1) * M1_tu_moment ?c t u
      + of_real (vec_nth ?L 2) * M2_tu_moment ?c t u =
      M12_tu_special_moment ?c t ?L"
    by (rule M12_tu_moment_combo_special_no_u[OF branch2_cross_combo_perp])
  have Lcombo: "of_real (?\<gamma>2 \<bullet> perp2 ?c) * ?M\<gamma>1
      - of_real (?\<gamma>1 \<bullet> perp2 ?c) * ?M\<gamma>2 =
      M12_tu_special_moment ?c t ?L"
    using Mcombo
    unfolding branch2_cross_combo_def Let_def
    by (simp add: algebra_simps)
  have Recombo: "(?\<gamma>2 \<bullet> perp2 ?c) * Re (cnj ?A * ((- \<i>) * ?M\<gamma>1))
      - (?\<gamma>1 \<bullet> perp2 ?c) * Re (cnj ?A * ((- \<i>) * ?M\<gamma>2))
      = Re (cnj ?A * ((- \<i>) * M12_tu_special_moment ?c t ?L))"
  proof -
    have left_expand: "of_real (?\<gamma>2 \<bullet> perp2 ?c) * (cnj ?A * ((- \<i>) * ?M\<gamma>1))
        - of_real (?\<gamma>1 \<bullet> perp2 ?c) * (cnj ?A * ((- \<i>) * ?M\<gamma>2))
        = cnj ?A * ((- \<i>) *
            (of_real (?\<gamma>2 \<bullet> perp2 ?c) * ?M\<gamma>1
              - of_real (?\<gamma>1 \<bullet> perp2 ?c) * ?M\<gamma>2))"
      by (simp add: algebra_simps)
    have right_reduce: "cnj ?A * ((- \<i>) *
            (of_real (?\<gamma>2 \<bullet> perp2 ?c) * ?M\<gamma>1
              - of_real (?\<gamma>1 \<bullet> perp2 ?c) * ?M\<gamma>2))
        = cnj ?A * ((- \<i>) * M12_tu_special_moment ?c t ?L)"
      using Lcombo by simp
    have "of_real (?\<gamma>2 \<bullet> perp2 ?c) * (cnj ?A * ((- \<i>) * ?M\<gamma>1))
        - of_real (?\<gamma>1 \<bullet> perp2 ?c) * (cnj ?A * ((- \<i>) * ?M\<gamma>2))
        = cnj ?A * ((- \<i>) * M12_tu_special_moment ?c t ?L)"
      using left_expand right_reduce by simp
    hence "Re (of_real (?\<gamma>2 \<bullet> perp2 ?c) * (cnj ?A * ((- \<i>) * ?M\<gamma>1))
        - of_real (?\<gamma>1 \<bullet> perp2 ?c) * (cnj ?A * ((- \<i>) * ?M\<gamma>2)))
        = Re (cnj ?A * ((- \<i>) * M12_tu_special_moment ?c t ?L))"
      by simp
    thus ?thesis by (simp add: algebra_simps)
  qed
  have Recombo_gain: "gain_dip \<omega> *
      (2 * ((?\<gamma>2 \<bullet> perp2 ?c) * Re (cnj ?A * ((- \<i>) * ?M\<gamma>1))
        - (?\<gamma>1 \<bullet> perp2 ?c) * Re (cnj ?A * ((- \<i>) * ?M\<gamma>2))))
      = gain_dip \<omega> *
        (2 * Re (cnj ?A * ((- \<i>) * M12_tu_special_moment ?c t ?L)))"
    using Recombo by simp
  have comp1: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (tu_param_map ?c t u) \<omega> $ 1 =
      frechet_derivative gdip (at (vec_nth \<omega> 1))
        (vec_nth (axis (1::2) 1) 1) * (cmod ?A)\<^sup>2
      + gain_dip \<omega> * (2 * Re (cnj ?A * ((- \<i>) * ?M\<gamma>1)))"
    using cnz
    by (simp add: gradU_dip_component_moments M_paper_tu_components_123
        A_moment_tu_param_map M1_moment_tu_param_map M2_moment_tu_param_map
        algebra_simps)
  have comp2: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (tu_param_map ?c t u) \<omega> $ 2 =
      frechet_derivative gdip (at (vec_nth \<omega> 1))
        (vec_nth (axis (2::2) 1) 1) * (cmod ?A)\<^sup>2
      + gain_dip \<omega> * (2 * Re (cnj ?A * ((- \<i>) * ?M\<gamma>2)))"
    using cnz
    by (simp add: gradU_dip_component_moments M_paper_tu_components_123
        A_moment_tu_param_map M1_moment_tu_param_map M2_moment_tu_param_map
        algebra_simps)
  have cross_expanded: "(?\<gamma>2 \<bullet> perp2 ?c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (tu_param_map ?c t u) \<omega> $ 1)
      - (?\<gamma>1 \<bullet> perp2 ?c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (tu_param_map ?c t u) \<omega> $ 2)
      = ((?\<gamma>2 \<bullet> perp2 ?c)
            * frechet_derivative gdip (at (vec_nth \<omega> 1))
                (vec_nth (axis (1::2) 1) 1)
          - (?\<gamma>1 \<bullet> perp2 ?c)
            * frechet_derivative gdip (at (vec_nth \<omega> 1))
                (vec_nth (axis (2::2) 1) 1)) * (cmod ?A)\<^sup>2
        + gain_dip \<omega> *
            (2 * ((?\<gamma>2 \<bullet> perp2 ?c) * Re (cnj ?A * ((- \<i>) * ?M\<gamma>1))
              - (?\<gamma>1 \<bullet> perp2 ?c) * Re (cnj ?A * ((- \<i>) * ?M\<gamma>2))))"
    apply (subst comp1)
    apply (subst comp2)
    by (simp add: algebra_simps)
  have cross: "(?\<gamma>2 \<bullet> perp2 ?c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (tu_param_map ?c t u) \<omega> $ 1)
      - (?\<gamma>1 \<bullet> perp2 ?c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (tu_param_map ?c t u) \<omega> $ 2)
      = ((?\<gamma>2 \<bullet> perp2 ?c)
            * frechet_derivative gdip (at (vec_nth \<omega> 1))
                (vec_nth (axis (1::2) 1) 1)
          - (?\<gamma>1 \<bullet> perp2 ?c)
            * frechet_derivative gdip (at (vec_nth \<omega> 1))
                (vec_nth (axis (2::2) 1) 1)) * (cmod ?A)\<^sup>2
        + gain_dip \<omega> * (2 * Re
            (cnj ?A * ((- \<i>) * M12_tu_special_moment ?c t ?L)))"
  proof -
    have "(?\<gamma>2 \<bullet> perp2 ?c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
          (tu_param_map ?c t u) \<omega> $ 1)
        - (?\<gamma>1 \<bullet> perp2 ?c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
          (tu_param_map ?c t u) \<omega> $ 2)
        = ((?\<gamma>2 \<bullet> perp2 ?c)
              * frechet_derivative gdip (at (vec_nth \<omega> 1))
                  (vec_nth (axis (1::2) 1) 1)
            - (?\<gamma>1 \<bullet> perp2 ?c)
              * frechet_derivative gdip (at (vec_nth \<omega> 1))
                  (vec_nth (axis (2::2) 1) 1)) * (cmod ?A)\<^sup>2
          + gain_dip \<omega> *
              (2 * ((?\<gamma>2 \<bullet> perp2 ?c) * Re (cnj ?A * ((- \<i>) * ?M\<gamma>1))
                - (?\<gamma>1 \<bullet> perp2 ?c) * Re (cnj ?A * ((- \<i>) * ?M\<gamma>2))))"
      by (rule cross_expanded)
    also have "\<dots> = ((?\<gamma>2 \<bullet> perp2 ?c)
              * frechet_derivative gdip (at (vec_nth \<omega> 1))
                  (vec_nth (axis (1::2) 1) 1)
            - (?\<gamma>1 \<bullet> perp2 ?c)
              * frechet_derivative gdip (at (vec_nth \<omega> 1))
                  (vec_nth (axis (2::2) 1) 1)) * (cmod ?A)\<^sup>2
          + gain_dip \<omega> * (2 * Re
              (cnj ?A * ((- \<i>) * M12_tu_special_moment ?c t ?L)))"
      by (simp only: Recombo_gain)
    finally show ?thesis .
  qed
  show ?thesis
  proof -
    have omega_eq: "branch2_base_param_omega ((\<omega>, t), a) = \<omega>"
      unfolding branch2_base_param_omega_def by simp
    have t_eq: "branch2_base_param_t ((\<omega>, t), a) = t"
      unfolding branch2_base_param_t_def by simp
    have cnz': "cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega ((\<omega>, t), a)) \<noteq> 0"
      using cnz unfolding omega_eq .
    show ?thesis
      unfolding branch2_reduced_gradU_scalar_eq_raw_M12_form[OF cnz']
        omega_eq t_eq Let_def
      using cross
      by (simp add: algebra_simps)
  qed
qed

lemma branch2_reduced_gradU_scalar_zero_of_gradU_zero:
  fixes t u :: "real^'n::finite"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
      (tu_param_map (cvec_dip \<omega>0 \<omega>s \<omega>) t u) \<omega> = 0"
  shows "branch2_reduced_gradU_scalar \<omega>0 \<omega>s ((\<omega>, t), a) = 0"
proof -
  have eq: "branch2_reduced_gradU_scalar \<omega>0 \<omega>s ((\<omega>, t), a) =
    (let c = cvec_dip \<omega>0 \<omega>s \<omega>;
         \<gamma>1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1);
         \<gamma>2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1);
         x = tu_param_map c t u
     in (\<gamma>2 \<bullet> perp2 c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1)
        - (\<gamma>1 \<bullet> perp2 c) * (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2))"
    by (rule branch2_reduced_gradU_scalar_eq_gradU_cross[OF cnz])
  show ?thesis
    using eq grad0 by (simp add: Let_def)
qed

definition branch2_chart1_repaired_reduced_base_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    (((real^2) \<times> (real^'n::finite)) \<times> real) \<Rightarrow> real \<times> (real^'n)" where
  "branch2_chart1_repaired_reduced_base_residual \<omega>0 \<omega>s r =
    (let \<omega> = branch2_base_param_omega r;
         t = branch2_base_param_t r;
         ell = ell_chart1 (branch2_base_param_a r)
     in (ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s \<omega>,
        (\<chi> m. if m = branch2_repair_slot
          then branch2_reduced_gradU_scalar \<omega>0 \<omega>s r
          else branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m)))"

definition branch2_chart2_repaired_reduced_base_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    (((real^2) \<times> (real^'n::finite)) \<times> real) \<Rightarrow> real \<times> (real^'n)" where
  "branch2_chart2_repaired_reduced_base_residual \<omega>0 \<omega>s r =
    (let \<omega> = branch2_base_param_omega r;
         t = branch2_base_param_t r;
         ell = ell_chart2 (branch2_base_param_a r)
     in (ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s \<omega>,
        (\<chi> m. if m = branch2_repair_slot
          then branch2_reduced_gradU_scalar \<omega>0 \<omega>s r
          else branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s \<omega> t ell m)))"

lemma branch2_slot_swap_zero:
  fixes F :: "real^'n::finite" and s R :: real
  assumes old: "(s, F) = (0, (0 :: real^'n))"
    and R0: "R = 0"
  shows "(s, (\<chi> m. if m = branch2_repair_slot then R else vec_nth F m))
      = (0, (0 :: real^'n))"
proof -
  have s0: "s = 0"
    using old by simp
  have F0: "vec_nth F m = 0" for m
    using old by (simp add: Finite_Cartesian_Product.vec_eq_iff)
  show ?thesis
    using s0 F0 R0 by (simp add: Finite_Cartesian_Product.vec_eq_iff)
qed

lemma branch2_chart1_residual_zero_imp_repaired_reduced_base_residual_zero:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    and grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (branch2_chart_param_x_map \<omega>0 \<omega>s q) (branch2_chart_param_omega q) = 0"
    and zero: "branch2_chart1_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
  shows "branch2_chart1_repaired_reduced_base_residual \<omega>0 \<omega>s
      (branch2_base_param_of_chart q) = (0, (0 :: real^'n))"
proof -
  have old_zero: "branch2_chart1_reduced_base_residual \<omega>0 \<omega>s
      (branch2_base_param_of_chart q) = (0, (0 :: real^'n))"
    by (rule branch2_chart1_residual_zero_imp_reduced_base_residual_zero[OF zero])
  have grad0_tu: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
      (tu_param_map (cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q))
        (branch2_chart_param_t q) (branch2_chart_param_u q))
      (branch2_chart_param_omega q) = 0"
    using grad0
    unfolding branch2_chart_param_x_map_def branch2_tu_x_map_def Let_def
      branch2_chart_param_omega_def branch2_chart_param_t_def
      branch2_chart_param_u_def
    by simp
  have Rzero: "branch2_reduced_gradU_scalar \<omega>0 \<omega>s
      (branch2_base_param_of_chart q) = 0"
  proof -
    have "branch2_reduced_gradU_scalar \<omega>0 \<omega>s
        ((branch2_chart_param_omega q, branch2_chart_param_t q),
          branch2_chart_param_a q) = 0"
      by (rule branch2_reduced_gradU_scalar_zero_of_gradU_zero[OF cnz grad0_tu])
    thus ?thesis
      unfolding branch2_base_param_of_chart_def by simp
  qed
  let ?r = "branch2_base_param_of_chart q"
  let ?\<omega> = "branch2_base_param_omega ?r"
  let ?ell = "ell_chart1 (branch2_base_param_a ?r)"
  let ?F = "(\<chi> m. branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s ?\<omega>
      (branch2_base_param_t ?r) ?ell m)"
  let ?s = "?ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s ?\<omega>"
  have old_pair: "(?s, ?F) = (0, (0 :: real^'n))"
    using old_zero
    unfolding branch2_chart1_reduced_base_residual_def Let_def by simp
  have new_pair: "(?s, (\<chi> m. if m = branch2_repair_slot
          then branch2_reduced_gradU_scalar \<omega>0 \<omega>s ?r
          else vec_nth ?F m)) = (0, (0 :: real^'n))"
    by (rule branch2_slot_swap_zero[OF old_pair Rzero])
  show ?thesis
    using new_pair
    unfolding branch2_chart1_repaired_reduced_base_residual_def
    by (auto simp: Let_def Finite_Cartesian_Product.vec_eq_iff split: if_splits)
qed

lemma branch2_chart2_residual_zero_imp_repaired_reduced_base_residual_zero:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    and grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (branch2_chart_param_x_map \<omega>0 \<omega>s q) (branch2_chart_param_omega q) = 0"
    and zero: "branch2_chart2_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
  shows "branch2_chart2_repaired_reduced_base_residual \<omega>0 \<omega>s
      (branch2_base_param_of_chart q) = (0, (0 :: real^'n))"
proof -
  have old_zero: "branch2_chart2_reduced_base_residual \<omega>0 \<omega>s
      (branch2_base_param_of_chart q) = (0, (0 :: real^'n))"
    by (rule branch2_chart2_residual_zero_imp_reduced_base_residual_zero[OF zero])
  have grad0_tu: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
      (tu_param_map (cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q))
        (branch2_chart_param_t q) (branch2_chart_param_u q))
      (branch2_chart_param_omega q) = 0"
    using grad0
    unfolding branch2_chart_param_x_map_def branch2_tu_x_map_def Let_def
      branch2_chart_param_omega_def branch2_chart_param_t_def
      branch2_chart_param_u_def
    by simp
  have Rzero: "branch2_reduced_gradU_scalar \<omega>0 \<omega>s
      (branch2_base_param_of_chart q) = 0"
  proof -
    have "branch2_reduced_gradU_scalar \<omega>0 \<omega>s
        ((branch2_chart_param_omega q, branch2_chart_param_t q),
          branch2_chart_param_a q) = 0"
      by (rule branch2_reduced_gradU_scalar_zero_of_gradU_zero[OF cnz grad0_tu])
    thus ?thesis
      unfolding branch2_base_param_of_chart_def by simp
  qed
  let ?r = "branch2_base_param_of_chart q"
  let ?\<omega> = "branch2_base_param_omega ?r"
  let ?ell = "ell_chart2 (branch2_base_param_a ?r)"
  let ?F = "(\<chi> m. branch2_radial_scalar_reduced_eq \<omega>0 \<omega>s ?\<omega>
      (branch2_base_param_t ?r) ?ell m)"
  let ?s = "?ell \<bullet> branch2_special_coeffs \<omega>0 \<omega>s ?\<omega>"
  have old_pair: "(?s, ?F) = (0, (0 :: real^'n))"
    using old_zero
    unfolding branch2_chart2_reduced_base_residual_def Let_def by simp
  have new_pair: "(?s, (\<chi> m. if m = branch2_repair_slot
          then branch2_reduced_gradU_scalar \<omega>0 \<omega>s ?r
          else vec_nth ?F m)) = (0, (0 :: real^'n))"
    by (rule branch2_slot_swap_zero[OF old_pair Rzero])
  show ?thesis
    using new_pair
    unfolding branch2_chart2_repaired_reduced_base_residual_def
    by (auto simp: Let_def Finite_Cartesian_Product.vec_eq_iff split: if_splits)
qed

definition branch2_chart1_repaired_reduced_base_system ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    (((real^2) \<times> (real^'n::finite)) \<times> real) set" where
  "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j =
    {r. branch2_base_param_omega r \<in> \<Gamma>
      \<and> branch2_base_param_bounded_det \<omega>0 \<omega>s r j
      \<and> branch2_chart1_repaired_reduced_base_residual \<omega>0 \<omega>s r =
          (0, (0 :: real^'n))}"

definition branch2_chart2_repaired_reduced_base_system ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    (((real^2) \<times> (real^'n::finite)) \<times> real) set" where
  "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j =
    {r. branch2_base_param_omega r \<in> \<Gamma>
      \<and> branch2_base_param_bounded_det \<omega>0 \<omega>s r j
      \<and> branch2_chart2_repaired_reduced_base_residual \<omega>0 \<omega>s r =
          (0, (0 :: real^'n))}"

definition branch2_chart1_repaired_reduced_base_IFT_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    ((real^2) \<times> ((real^'n::finite) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)" where
  "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z =
    branch2_residual_to_IFT_range
      (branch2_chart1_repaired_reduced_base_residual \<omega>0 \<omega>s
        (branch2_base_unassoc z))"

definition branch2_chart2_repaired_reduced_base_IFT_residual ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow>
    ((real^2) \<times> ((real^'n::finite) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)" where
  "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z =
    branch2_residual_to_IFT_range
      (branch2_chart2_repaired_reduced_base_residual \<omega>0 \<omega>s
        (branch2_base_unassoc z))"

definition branch2_chart1_repaired_reduced_base_regular_rank ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart1_repaired_reduced_base_regular_rank V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<forall>r\<in>branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
      \<exists>D :: (((real^2) \<times> (real^'n)) \<times> real) \<Rightarrow> real \<times> (real^'n).
        ((branch2_chart1_repaired_reduced_base_residual \<omega>0 \<omega>s)
          has_derivative D) (at r)
        \<and> surj D)"

definition branch2_chart2_repaired_reduced_base_regular_rank ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart2_repaired_reduced_base_regular_rank V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<forall>r\<in>branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
      \<exists>D :: (((real^2) \<times> (real^'n)) \<times> real) \<Rightarrow> real \<times> (real^'n).
        ((branch2_chart2_repaired_reduced_base_residual \<omega>0 \<omega>s)
          has_derivative D) (at r)
        \<and> surj D)"

definition branch2_repaired_reduced_base_regular_rank_all ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow>
    real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branch2_repaired_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
    (\<forall>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
      branch2_chart1_repaired_reduced_base_regular_rank V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_repaired_reduced_base_regular_rank V \<omega>0 \<omega>s \<Gamma> j)"

subsection \<open>\<section>7ad: determinant-threaded repaired slice cover endpoint\<close>

lemma branch2_tu_system_Dcvec_det_nonzero:
  fixes V :: "((real^2)^'n::finite) set"
    and p :: "(real^2) \<times> ((real^'n) \<times> (real^'n))"
  assumes pin: "p \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
  shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s (fst p))) \<noteq> 0"
  using pin unfolding branch2_tu_system_def BadXGW_def Let_def by blast

lemma branch2_chart_param_bounded_det_exists:
  fixes q :: "(((real^2) \<times> ((real^'n::finite) \<times> (real^'n))) \<times> real)"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q))) \<noteq> 0"
  shows "\<exists>j. branch2_chart_param_bounded_det \<omega>0 \<omega>s q j"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q)"
  let ?det = "det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q)))"
  have ccpos: "0 < ?c \<bullet> ?c"
    using cnz by (metis inner_gt_zero_iff)
  have detpos: "0 < abs ?det"
    using detnz by simp
  obtain j0 :: nat where j0: "inverse (real (Suc j0)) < ?c \<bullet> ?c"
    using reals_Archimedean[OF ccpos] by blast
  obtain j1 :: nat where j1: "norm (branch2_chart_param_t q) \<le> real j1"
    using real_arch_simple by blast
  obtain j2 :: nat where j2: "norm (branch2_chart_param_u q) \<le> real j2"
    using real_arch_simple by blast
  obtain j3 :: nat where j3: "abs (branch2_chart_param_a q) \<le> real j3"
    using real_arch_simple by blast
  obtain j4 :: nat where j4: "inverse (real (Suc j4)) < abs ?det"
    using reals_Archimedean[OF detpos] by blast
  define j where "j = max j0 (max j1 (max j2 (max j3 j4)))"
  have c_ok: "1 / real (Suc j) \<le> ?c \<bullet> ?c"
  proof -
    have "1 / real (Suc j) \<le> 1 / real (Suc j0)"
      unfolding j_def by (simp only: frac_le)
    also have "\<dots> < ?c \<bullet> ?c"
      using j0 by (simp only: inverse_eq_divide)
    finally show ?thesis by linarith
  qed
  have t_ok: "norm (branch2_chart_param_t q) \<le> real (Suc j)"
  proof -
    have "j1 \<le> j"
      unfolding j_def by simp
    hence "real j1 \<le> real (Suc j)"
      by linarith
    thus ?thesis using j1 by linarith
  qed
  have u_ok: "norm (branch2_chart_param_u q) \<le> real (Suc j)"
  proof -
    have "j2 \<le> j"
      unfolding j_def by simp
    hence "real j2 \<le> real (Suc j)"
      by linarith
    thus ?thesis using j2 by linarith
  qed
  have a_ok: "abs (branch2_chart_param_a q) \<le> real (Suc j)"
  proof -
    have "j3 \<le> j"
      unfolding j_def by simp
    hence "real j3 \<le> real (Suc j)"
      by linarith
    thus ?thesis using j3 by linarith
  qed
  have det_ok: "1 / real (Suc j) \<le> abs ?det"
  proof -
    have "1 / real (Suc j) \<le> 1 / real (Suc j4)"
      unfolding j_def by (simp only: frac_le)
    also have "\<dots> < abs ?det"
      using j4 by (simp only: inverse_eq_divide)
    finally show ?thesis by linarith
  qed
  show ?thesis
    unfolding branch2_chart_param_bounded_det_def branch2_chart_param_bounded_def
      Let_def
    using c_ok t_ok u_ok a_ok det_ok by blast
qed

lemma branch2_chart1_param_system_bounded_det_exists:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "(((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real)"
  assumes qin: "q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"
  shows "\<exists>j. branch2_chart_param_bounded_det \<omega>0 \<omega>s q j"
proof -
  have pin: "fst q \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
    using qin unfolding branch2_chart1_param_system_def by blast
  have cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    using branch2_tu_system_cvec_nonzero[OF pin]
    unfolding branch2_chart_param_omega_def by simp
  have detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q))) \<noteq> 0"
    using branch2_tu_system_Dcvec_det_nonzero[OF pin]
    unfolding branch2_chart_param_omega_def by simp
  show ?thesis
    by (rule branch2_chart_param_bounded_det_exists[OF cnz detnz])
qed

lemma branch2_chart2_param_system_bounded_det_exists:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "(((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real)"
  assumes qin: "q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"
  shows "\<exists>j. branch2_chart_param_bounded_det \<omega>0 \<omega>s q j"
proof -
  have pin: "fst q \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
    using qin unfolding branch2_chart2_param_system_def by blast
  have cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    using branch2_tu_system_cvec_nonzero[OF pin]
    unfolding branch2_chart_param_omega_def by simp
  have detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q))) \<noteq> 0"
    using branch2_tu_system_Dcvec_det_nonzero[OF pin]
    unfolding branch2_chart_param_omega_def by simp
  show ?thesis
    by (rule branch2_chart_param_bounded_det_exists[OF cnz detnz])
qed

definition branch2_chart1_param_det_slice_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    (((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real) set" where
  "branch2_chart1_param_det_slice_system V \<omega>0 \<omega>s \<Gamma> j =
    {q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>.
      branch2_chart_param_bounded_det \<omega>0 \<omega>s q j}"

definition branch2_chart2_param_det_slice_system ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    (((real^2) \<times> ((real^'n) \<times> (real^'n))) \<times> real) set" where
  "branch2_chart2_param_det_slice_system V \<omega>0 \<omega>s \<Gamma> j =
    {q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>.
      branch2_chart_param_bounded_det \<omega>0 \<omega>s q j}"

definition branch2_chart1_param_det_slice_image ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    ((real^2)^'n) set" where
  "branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j =
    branch2_chart_param_x_map \<omega>0 \<omega>s `
      branch2_chart1_param_det_slice_system V \<omega>0 \<omega>s \<Gamma> j"

definition branch2_chart2_param_det_slice_image ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow>
    ((real^2)^'n) set" where
  "branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j =
    branch2_chart_param_x_map \<omega>0 \<omega>s `
      branch2_chart2_param_det_slice_system V \<omega>0 \<omega>s \<Gamma> j"

lemma branch2_chart1_param_image_subset_det_slice_images:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> (\<Union>j. branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j)"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma>"
  then obtain q where qin: "q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"
    and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
    unfolding branch2_chart1_param_image_def by blast
  obtain j where bj: "branch2_chart_param_bounded_det \<omega>0 \<omega>s q j"
    using branch2_chart1_param_system_bounded_det_exists[OF qin] by blast
  have "q \<in> branch2_chart1_param_det_slice_system V \<omega>0 \<omega>s \<Gamma> j"
    using qin bj unfolding branch2_chart1_param_det_slice_system_def by blast
  hence "x \<in> branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j"
    unfolding branch2_chart1_param_det_slice_image_def using xeq by blast
  thus "x \<in> (\<Union>j. branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j)"
    by blast
qed

lemma branch2_chart2_param_image_subset_det_slice_images:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> (\<Union>j. branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j)"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma>"
  then obtain q where qin: "q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"
    and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
    unfolding branch2_chart2_param_image_def by blast
  obtain j where bj: "branch2_chart_param_bounded_det \<omega>0 \<omega>s q j"
    using branch2_chart2_param_system_bounded_det_exists[OF qin] by blast
  have "q \<in> branch2_chart2_param_det_slice_system V \<omega>0 \<omega>s \<Gamma> j"
    using qin bj unfolding branch2_chart2_param_det_slice_system_def by blast
  hence "x \<in> branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j"
    unfolding branch2_chart2_param_det_slice_image_def using xeq by blast
  thus "x \<in> (\<Union>j. branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j)"
    by blast
qed

theorem branchP_indep_closed_cover_core_all_of_chart_param_det_slice_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
          \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
          \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_chart_param_image_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set"
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart1_param_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
  proof -
    have ex1: "\<forall>j. \<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
        branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
        \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
      using chart1[OF Gsub Gindep] by blast
    then obtain K1 :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
      where cover1: "\<And>j. branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>n. K1 j n)"
        and closed1: "\<And>j n. closed (K1 j n)"
        and neg1: "\<And>j n. negligible (K1 j n)"
      by metis
    show ?thesis
      by (rule closed_negligible_cover_of_slice_covers
          [OF branch2_chart1_param_image_subset_det_slice_images cover1 closed1 neg1])
  qed
  show "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart2_param_image V \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  proof -
    have ex2: "\<forall>j. \<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
        branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
        \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
      using chart2[OF Gsub Gindep] by blast
    then obtain K2 :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
      where cover2: "\<And>j. branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>n. K2 j n)"
        and closed2: "\<And>j n. closed (K2 j n)"
        and neg2: "\<And>j n. negligible (K2 j n)"
      by metis
    show ?thesis
      by (rule closed_negligible_cover_of_slice_covers
          [OF branch2_chart2_param_image_subset_det_slice_images cover2 closed2 neg2])
  qed
qed

lemma branch2_chart1_param_det_slice_image_subset_repaired_reduced_slice_image:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> branch2_base_fibre_x_map \<omega>0 \<omega>s `
        {ru. fst ru \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<and> branch2_u_param_bounded (snd ru) j}"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j"
  then obtain q where qslice: "q \<in> branch2_chart1_param_det_slice_system V \<omega>0 \<omega>s \<Gamma> j"
    and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
    unfolding branch2_chart1_param_det_slice_image_def by blast
  let ?r = "branch2_base_param_of_chart q"
  let ?u = "branch2_chart_param_u q"
  have qsys: "q \<in> branch2_chart1_param_system V \<omega>0 \<omega>s \<Gamma>"
    and bounded: "branch2_chart_param_bounded_det \<omega>0 \<omega>s q j"
    using qslice unfolding branch2_chart1_param_det_slice_system_def by auto
  have pin: "fst q \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
    using qsys unfolding branch2_chart1_param_system_def by blast
  have omega_in: "branch2_base_param_omega ?r \<in> \<Gamma>"
    using qsys
    unfolding branch2_chart1_param_system_def branch2_tu_system_def
      branch2_base_param_of_chart_def branch2_base_param_omega_def
      branch2_chart_param_omega_def
    by auto
  have cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    using branch2_tu_system_cvec_nonzero[OF pin]
    unfolding branch2_chart_param_omega_def by simp
  have grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (branch2_chart_param_x_map \<omega>0 \<omega>s q) (branch2_chart_param_omega q) = 0"
    using pin
    unfolding branch2_tu_system_def BadXGW_def branch2_chart_param_x_map_def
      branch2_tu_x_map_def branch2_chart_param_omega_def Let_def
    by auto
  have base_u_bounded: "branch2_base_param_bounded_det \<omega>0 \<omega>s ?r j
      \<and> branch2_u_param_bounded ?u j"
    by (rule branch2_chart_param_bounded_det_imp_base_u_bounded_det[OF bounded])
  have zero: "branch2_chart1_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
    using qsys unfolding branch2_chart1_param_system_def by blast
  have red_zero: "branch2_chart1_repaired_reduced_base_residual \<omega>0 \<omega>s ?r =
      (0, (0 :: real^'n))"
    by (rule branch2_chart1_residual_zero_imp_repaired_reduced_base_residual_zero
        [OF cnz grad0 zero])
  have rin: "?r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
    using omega_in base_u_bounded red_zero
    unfolding branch2_chart1_repaired_reduced_base_system_def by blast
  have pairin: "(?r, ?u) \<in>
      {ru. fst ru \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j}"
    using rin base_u_bounded by simp
  have xeq': "x = branch2_base_fibre_x_map \<omega>0 \<omega>s (?r, ?u)"
    by (simp add: branch2_base_fibre_x_map_of_chart xeq)
  show "x \<in> branch2_base_fibre_x_map \<omega>0 \<omega>s `
        {ru. fst ru \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<and> branch2_u_param_bounded (snd ru) j}"
    using pairin xeq' by blast
qed

lemma branch2_chart2_param_det_slice_image_subset_repaired_reduced_slice_image:
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> branch2_base_fibre_x_map \<omega>0 \<omega>s `
        {ru. fst ru \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<and> branch2_u_param_bounded (snd ru) j}"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j"
  then obtain q where qslice: "q \<in> branch2_chart2_param_det_slice_system V \<omega>0 \<omega>s \<Gamma> j"
    and xeq: "x = branch2_chart_param_x_map \<omega>0 \<omega>s q"
    unfolding branch2_chart2_param_det_slice_image_def by blast
  let ?r = "branch2_base_param_of_chart q"
  let ?u = "branch2_chart_param_u q"
  have qsys: "q \<in> branch2_chart2_param_system V \<omega>0 \<omega>s \<Gamma>"
    and bounded: "branch2_chart_param_bounded_det \<omega>0 \<omega>s q j"
    using qslice unfolding branch2_chart2_param_det_slice_system_def by auto
  have pin: "fst q \<in> branch2_tu_system V \<omega>0 \<omega>s \<Gamma>"
    using qsys unfolding branch2_chart2_param_system_def by blast
  have omega_in: "branch2_base_param_omega ?r \<in> \<Gamma>"
    using qsys
    unfolding branch2_chart2_param_system_def branch2_tu_system_def
      branch2_base_param_of_chart_def branch2_base_param_omega_def
      branch2_chart_param_omega_def
    by auto
  have cnz: "cvec_dip \<omega>0 \<omega>s (branch2_chart_param_omega q) \<noteq> 0"
    using branch2_tu_system_cvec_nonzero[OF pin]
    unfolding branch2_chart_param_omega_def by simp
  have grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (branch2_chart_param_x_map \<omega>0 \<omega>s q) (branch2_chart_param_omega q) = 0"
    using pin
    unfolding branch2_tu_system_def BadXGW_def branch2_chart_param_x_map_def
      branch2_tu_x_map_def branch2_chart_param_omega_def Let_def
    by auto
  have base_u_bounded: "branch2_base_param_bounded_det \<omega>0 \<omega>s ?r j
      \<and> branch2_u_param_bounded ?u j"
    by (rule branch2_chart_param_bounded_det_imp_base_u_bounded_det[OF bounded])
  have zero: "branch2_chart2_residual \<omega>0 \<omega>s q = (0, (0 :: real^'n))"
    using qsys unfolding branch2_chart2_param_system_def by blast
  have red_zero: "branch2_chart2_repaired_reduced_base_residual \<omega>0 \<omega>s ?r =
      (0, (0 :: real^'n))"
    by (rule branch2_chart2_residual_zero_imp_repaired_reduced_base_residual_zero
        [OF cnz grad0 zero])
  have rin: "?r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
    using omega_in base_u_bounded red_zero
    unfolding branch2_chart2_repaired_reduced_base_system_def by blast
  have pairin: "(?r, ?u) \<in>
      {ru. fst ru \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j}"
    using rin base_u_bounded by simp
  have xeq': "x = branch2_base_fibre_x_map \<omega>0 \<omega>s (?r, ?u)"
    by (simp add: branch2_base_fibre_x_map_of_chart xeq)
  show "x \<in> branch2_base_fibre_x_map \<omega>0 \<omega>s `
        {ru. fst ru \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<and> branch2_u_param_bounded (snd ru) j}"
    using pairin xeq' by blast
qed

definition branch2_chart1_repaired_reduced_slice_image ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow> ((real^2)^'n::finite) set" where
  "branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j =
    branch2_base_fibre_x_map \<omega>0 \<omega>s `
      {ru. fst ru \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j}"

definition branch2_chart2_repaired_reduced_slice_image ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat \<Rightarrow> ((real^2)^'n::finite) set" where
  "branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j =
    branch2_base_fibre_x_map \<omega>0 \<omega>s `
      {ru. fst ru \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j}"

lemma branch2_chart1_param_det_slice_image_subset_repaired_reduced_slice_image':
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
  using branch2_chart1_param_det_slice_image_subset_repaired_reduced_slice_image[of V \<omega>0 \<omega>s \<Gamma> j]
  unfolding branch2_chart1_repaired_reduced_slice_image_def .

lemma branch2_chart2_param_det_slice_image_subset_repaired_reduced_slice_image':
  fixes V :: "((real^2)^'n::finite) set"
  shows "branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
  using branch2_chart2_param_det_slice_image_subset_repaired_reduced_slice_image[of V \<omega>0 \<omega>s \<Gamma> j]
  unfolding branch2_chart2_repaired_reduced_slice_image_def .

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_slice_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
          \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
          branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
          \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_chart_param_det_slice_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain K1 :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover1: "branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)"
      and closed1: "\<forall>n. closed (K1 n)"
      and neg1: "\<forall>n. negligible (K1 n)"
    using chart1[OF Gsub Gindep] by blast
  show "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart1_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    using branch2_chart1_param_det_slice_image_subset_repaired_reduced_slice_image'[of V \<omega>0 \<omega>s \<Gamma> j]
      cover1 closed1 neg1 by blast
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain K2 :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover2: "branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)"
      and closed2: "\<forall>n. closed (K2 n)"
      and neg2: "\<forall>n. negligible (K2 n)"
    using chart2[OF Gsub Gindep] by blast
  show "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart2_param_det_slice_image V \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
    using branch2_chart2_param_det_slice_image_subset_repaired_reduced_slice_image'[of V \<omega>0 \<omega>s \<Gamma> j]
      cover2 closed2 neg2 by blast
qed

subsection \<open>\<section>7ae: repaired reduced-base chart capstones\<close>

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_countable_lowdim_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) set.
        \<exists>F :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
          branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>i. F i ` C i)
          \<and> (\<forall>i. F i differentiable_on C i)
          \<and> (\<forall>i. closed (F i ` C i))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) set.
        \<exists>F :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
          branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>i. F i ` C i)
          \<and> (\<forall>i. F i differentiable_on C i)
          \<and> (\<forall>i. closed (F i ` C i))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_slice_covers[OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) set"
    and F :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)"
    where cover: "branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. F i ` C i)"
      and diff: "\<forall>i. F i differentiable_on C i"
      and closed_image: "\<forall>i. closed (F i ` C i)"
    using chart1[OF Gsub Gindep] by meson
  show "\<exists>K1 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K1 n)
      \<and> (\<forall>n. closed (K1 n)) \<and> (\<forall>n. negligible (K1 n))"
    by (rule closed_negligible_cover_of_branch2_countable_lowdim_param_images
        [OF card4 cover]) (use diff closed_image in auto)
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) set"
    and F :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)"
    where cover: "branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. F i ` C i)"
      and diff: "\<forall>i. F i differentiable_on C i"
      and closed_image: "\<forall>i. closed (F i ` C i)"
    using chart2[OF Gsub Gindep] by meson
  show "\<exists>K2 :: nat \<Rightarrow> ((real^2)^'n) set.
      branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j \<subseteq> (\<Union>n. K2 n)
      \<and> (\<forall>n. closed (K2 n)) \<and> (\<forall>n. negligible (K2 n))"
    by (rule closed_negligible_cover_of_branch2_countable_lowdim_param_images
        [OF card4 cover], use diff closed_image in auto)
qed

lemma branch2_chart1_repaired_reduced_slice_image_subset_lifted_base_charts:
  fixes C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)"
  assumes base_cover: "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. psi i ` C i)"
  shows "branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          ` (C i \<times> branch2_u_slice_domain j))"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
  then obtain ru
    where ru_dom: "fst ru \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j"
      and xeq: "x = branch2_base_fibre_x_map \<omega>0 \<omega>s ru"
    unfolding branch2_chart1_repaired_reduced_slice_image_def by blast
  obtain i s where sC: "s \<in> C i" and r_eq: "fst ru = psi i s"
    using base_cover ru_dom by blast
  have u_dom: "snd ru \<in> branch2_u_slice_domain j"
    using ru_dom unfolding branch2_u_slice_domain_def by blast
  have su_dom: "(s, snd ru) \<in> C i \<times> branch2_u_slice_domain j"
    using sC u_dom by simp
  have "x = branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i) (s, snd ru)"
    using xeq r_eq unfolding branch2_lifted_base_chart_x_map_def
    by (simp add: branch2_base_fibre_x_map_def)
  thus "x \<in> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
      ` (C i \<times> branch2_u_slice_domain j))"
    using su_dom by blast
qed

lemma branch2_chart2_repaired_reduced_slice_image_subset_lifted_base_charts:
  fixes C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)"
  assumes base_cover: "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. psi i ` C i)"
  shows "branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          ` (C i \<times> branch2_u_slice_domain j))"
proof
  fix x :: "(real^2)^'n"
  assume xin: "x \<in> branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j"
  then obtain ru
    where ru_dom: "fst ru \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<and> branch2_u_param_bounded (snd ru) j"
      and xeq: "x = branch2_base_fibre_x_map \<omega>0 \<omega>s ru"
    unfolding branch2_chart2_repaired_reduced_slice_image_def by blast
  obtain i s where sC: "s \<in> C i" and r_eq: "fst ru = psi i s"
    using base_cover ru_dom by blast
  have u_dom: "snd ru \<in> branch2_u_slice_domain j"
    using ru_dom unfolding branch2_u_slice_domain_def by blast
  have su_dom: "(s, snd ru) \<in> C i \<times> branch2_u_slice_domain j"
    using sC u_dom by simp
  have "x = branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i) (s, snd ru)"
    using xeq r_eq unfolding branch2_lifted_base_chart_x_map_def
    by (simp add: branch2_base_fibre_x_map_def)
  thus "x \<in> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
      ` (C i \<times> branch2_u_slice_domain j))"
    using su_dom by blast
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_chart_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> (real^2) set.
        \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
          branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>i. psi i ` C i)
          \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                differentiable_on (C i \<times> branch2_u_slice_domain j))
          \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                ` (C i \<times> branch2_u_slice_domain j)))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> (real^2) set.
        \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
          branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>i. psi i ` C i)
          \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                differentiable_on (C i \<times> branch2_u_slice_domain j))
          \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                ` (C i \<times> branch2_u_slice_domain j)))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_countable_lowdim_parametrizations
    [OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)"
    where base_cover:
        "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
      and closed_image: "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          ` (C i \<times> branch2_u_slice_domain j))"
    using chart1[OF Gsub Gindep] by meson
  show "\<exists>C :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) set.
      \<exists>F :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
        branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. F i ` C i)
        \<and> (\<forall>i. F i differentiable_on C i) \<and> (\<forall>i. closed (F i ` C i))"
  proof (intro exI[where x = "\<lambda>i. C i \<times> branch2_u_slice_domain j"]
      exI[where x = "\<lambda>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)"] conjI)
    show "branch2_chart1_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
            ` (C i \<times> branch2_u_slice_domain j))"
      by (rule branch2_chart1_repaired_reduced_slice_image_subset_lifted_base_charts
          [OF base_cover])
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff .
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using closed_image .
  qed
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)"
    where base_cover:
        "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
      and closed_image: "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          ` (C i \<times> branch2_u_slice_domain j))"
    using chart2[OF Gsub Gindep] by meson
  show "\<exists>C :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) set.
      \<exists>F :: nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<Rightarrow> ((real^2)^'n).
        branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. F i ` C i)
        \<and> (\<forall>i. F i differentiable_on C i) \<and> (\<forall>i. closed (F i ` C i))"
  proof (intro exI[where x = "\<lambda>i. C i \<times> branch2_u_slice_domain j"]
      exI[where x = "\<lambda>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)"] conjI)
    show "branch2_chart2_repaired_reduced_slice_image \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
            ` (C i \<times> branch2_u_slice_domain j))"
      by (rule branch2_chart2_repaired_reduced_slice_image_subset_lifted_base_charts
          [OF base_cover])
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff .
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using closed_image .
  qed
qed

lemma branch2_chart1_repaired_reduced_base_IFT_residual_zero_iff:
  fixes z :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
  shows "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0) \<longleftrightarrow>
    branch2_chart1_repaired_reduced_base_residual \<omega>0 \<omega>s (branch2_base_unassoc z)
      = (0, (0 :: real^'n))"
  unfolding branch2_chart1_repaired_reduced_base_IFT_residual_def by simp

lemma branch2_chart2_repaired_reduced_base_IFT_residual_zero_iff:
  fixes z :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
  shows "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0) \<longleftrightarrow>
    branch2_chart2_repaired_reduced_base_residual \<omega>0 \<omega>s (branch2_base_unassoc z)
      = (0, (0 :: real^'n))"
  unfolding branch2_chart2_repaired_reduced_base_IFT_residual_def by simp

lemma branch2_chart1_repaired_reduced_base_system_assoc_iff:
  fixes r :: "(((real^2) \<times> (real^'n::finite)) \<times> real)"
  shows "r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    branch2_base_param_omega r \<in> \<Gamma>
    \<and> branch2_base_param_bounded_det \<omega>0 \<omega>s r j
    \<and> branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0)"
  unfolding branch2_chart1_repaired_reduced_base_system_def
    branch2_chart1_repaired_reduced_base_IFT_residual_def
  by simp

lemma branch2_chart2_repaired_reduced_base_system_assoc_iff:
  fixes r :: "(((real^2) \<times> (real^'n::finite)) \<times> real)"
  shows "r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    branch2_base_param_omega r \<in> \<Gamma>
    \<and> branch2_base_param_bounded_det \<omega>0 \<omega>s r j
    \<and> branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0)"
  unfolding branch2_chart2_repaired_reduced_base_system_def
    branch2_chart2_repaired_reduced_base_IFT_residual_def
  by simp

lemma branch2_chart1_repaired_reduced_base_IFT_residual_local_chart:
  fixes z0 :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
    and G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
  assumes zero: "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z0 = (0, 0)"
    and der: "\<And>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg: "surj (blinfun_apply (G' z0))"
  shows "\<exists>U u0 \<phi> g D\<phi>.
      open (U :: (real^2) set) \<and> u0 \<in> U \<and> \<phi> u0 = z0
      \<and> \<phi> differentiable_on U
      \<and> \<phi> ` U \<subseteq> {z. branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)}
      \<and> openin (top_of_set {z. branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` U)
      \<and> homeomorphism U (\<phi> ` U) \<phi> g
      \<and> (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u))
      \<and> (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u))
             = {w. blinfun_apply (G' (\<phi> u)) w = 0})"
proof -
  have zero': "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z0 = 0"
    using zero by (simp add: zero_prod_def)
  show ?thesis
    using regular_value_local_chart
      [where W = UNIV and p = z0
        and G = "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s"
        and G' = G',
        OF open_UNIV UNIV_I zero']
      der cont reg
    by (auto simp: zero_prod_def)
qed

lemma branch2_chart2_repaired_reduced_base_IFT_residual_local_chart:
  fixes z0 :: "(real^2) \<times> ((real^'n::finite) \<times> real)"
    and G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
  assumes zero: "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z0 = (0, 0)"
    and der: "\<And>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg: "surj (blinfun_apply (G' z0))"
  shows "\<exists>U u0 \<phi> g D\<phi>.
      open (U :: (real^2) set) \<and> u0 \<in> U \<and> \<phi> u0 = z0
      \<and> \<phi> differentiable_on U
      \<and> \<phi> ` U \<subseteq> {z. branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)}
      \<and> openin (top_of_set {z. branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` U)
      \<and> homeomorphism U (\<phi> ` U) \<phi> g
      \<and> (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u))
      \<and> (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u))
             = {w. blinfun_apply (G' (\<phi> u)) w = 0})"
proof -
  have zero': "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z0 = 0"
    using zero by (simp add: zero_prod_def)
  show ?thesis
    using regular_value_local_chart
      [where W = UNIV and p = z0
        and G = "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s"
        and G' = G',
        OF open_UNIV UNIV_I zero']
      der cont reg
    by (auto simp: zero_prod_def)
qed

definition branch2_chart1_repaired_reduced_base_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart1_repaired_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j))))"

definition branch2_chart2_repaired_reduced_base_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart2_repaired_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j))))"

definition branch2_repaired_reduced_base_IFT_parametrizations_all ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow>
    real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branch2_repaired_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
    (\<forall>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
      branch2_chart1_repaired_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_repaired_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j)"

definition branch2_chart1_repaired_reduced_base_assoc_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart1_repaired_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>\<phi> :: nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
        branch2_base_assoc ` branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              ` (C i \<times> branch2_u_slice_domain j))))"

definition branch2_chart2_repaired_reduced_base_assoc_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart2_repaired_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>\<phi> :: nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
        branch2_base_assoc ` branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
              (\<lambda>s. branch2_base_unassoc (\<phi> i s))
              ` (C i \<times> branch2_u_slice_domain j))))"

definition branch2_repaired_reduced_base_assoc_IFT_parametrizations_all ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow>
    real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branch2_repaired_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
    (\<forall>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
      branch2_chart1_repaired_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_repaired_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j)"

lemma branch2_chart1_repaired_reduced_base_IFT_parametrizations_of_assoc:
  fixes V :: "((real^2)^'n::finite) set"
  assumes assoc: "branch2_chart1_repaired_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
  shows "branch2_chart1_repaired_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
proof -
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and \<phi> :: "nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))"
    where assoc_cover:
        "branch2_base_assoc ` branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
          (\<lambda>s. branch2_base_unassoc (\<phi> i s))
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
      and closed_image: "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
          (\<lambda>s. branch2_base_unassoc (\<phi> i s))
          ` (C i \<times> branch2_u_slice_domain j))"
    using assoc
    unfolding branch2_chart1_repaired_reduced_base_assoc_IFT_parametrizations_def
    by auto
  have base_cover: "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
  proof
    fix r :: "(((real^2) \<times> (real^'n)) \<times> real)"
    assume rin: "r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
    then have "branch2_base_assoc r \<in>
        branch2_base_assoc ` branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
      by blast
    then obtain i s where sC: "s \<in> C i" and seq: "branch2_base_assoc r = \<phi> i s"
      using assoc_cover by blast
    have "r = branch2_base_unassoc (\<phi> i s)"
      using seq by (metis branch2_base_unassoc_assoc)
    thus "r \<in> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
      using sC by blast
  qed
  show ?thesis
    unfolding branch2_chart1_repaired_reduced_base_IFT_parametrizations_def
  proof (intro exI[where x = C]
      exI[where x = "\<lambda>i s. branch2_base_unassoc (\<phi> i s)"] conjI)
    show "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
      using base_cover .
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
        ((\<lambda>i s. branch2_base_unassoc (\<phi> i s)) i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff by simp
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
        ((\<lambda>i s. branch2_base_unassoc (\<phi> i s)) i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using closed_image by simp
  qed
qed

lemma branch2_chart2_repaired_reduced_base_IFT_parametrizations_of_assoc:
  fixes V :: "((real^2)^'n::finite) set"
  assumes assoc: "branch2_chart2_repaired_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
  shows "branch2_chart2_repaired_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
proof -
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and \<phi> :: "nat \<Rightarrow> (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))"
    where assoc_cover:
        "branch2_base_assoc ` branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. \<phi> i ` C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
          (\<lambda>s. branch2_base_unassoc (\<phi> i s))
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
      and closed_image: "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
          (\<lambda>s. branch2_base_unassoc (\<phi> i s))
          ` (C i \<times> branch2_u_slice_domain j))"
    using assoc
    unfolding branch2_chart2_repaired_reduced_base_assoc_IFT_parametrizations_def
    by auto
  have base_cover: "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
  proof
    fix r :: "(((real^2) \<times> (real^'n)) \<times> real)"
    assume rin: "r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
    then have "branch2_base_assoc r \<in>
        branch2_base_assoc ` branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
      by blast
    then obtain i s where sC: "s \<in> C i" and seq: "branch2_base_assoc r = \<phi> i s"
      using assoc_cover by blast
    have "r = branch2_base_unassoc (\<phi> i s)"
      using seq by (metis branch2_base_unassoc_assoc)
    thus "r \<in> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
      using sC by blast
  qed
  show ?thesis
    unfolding branch2_chart2_repaired_reduced_base_IFT_parametrizations_def
  proof (intro exI[where x = C]
      exI[where x = "\<lambda>i s. branch2_base_unassoc (\<phi> i s)"] conjI)
    show "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. (\<lambda>s. branch2_base_unassoc (\<phi> i s)) ` C i)"
      using base_cover .
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
        ((\<lambda>i s. branch2_base_unassoc (\<phi> i s)) i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff by simp
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
        ((\<lambda>i s. branch2_base_unassoc (\<phi> i s)) i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using closed_image by simp
  qed
qed

lemma branch2_repaired_reduced_base_IFT_parametrizations_all_of_assoc:
  fixes V :: "((real^2)^'n::finite) set"
  assumes assoc: "branch2_repaired_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branch2_repaired_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branch2_repaired_reduced_base_IFT_parametrizations_all_def
proof (intro allI impI conjI)
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  have both: "branch2_chart1_repaired_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_repaired_reduced_base_assoc_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
    using assoc Gsub Gindep
    unfolding branch2_repaired_reduced_base_assoc_IFT_parametrizations_all_def by blast
  show "branch2_chart1_repaired_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
    by (rule branch2_chart1_repaired_reduced_base_IFT_parametrizations_of_assoc
        [OF conjunct1[OF both]])
  show "branch2_chart2_repaired_reduced_base_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
    by (rule branch2_chart2_repaired_reduced_base_IFT_parametrizations_of_assoc
        [OF conjunct2[OF both]])
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_IFT_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and ift: "branch2_repaired_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_base_chart_parametrizations
    [OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j)))"
    using ift Gsub Gindep
    unfolding branch2_repaired_reduced_base_IFT_parametrizations_all_def
      branch2_chart1_repaired_reduced_base_IFT_parametrizations_def
    by blast
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j)))"
    using ift Gsub Gindep
    unfolding branch2_repaired_reduced_base_IFT_parametrizations_all_def
      branch2_chart2_repaired_reduced_base_IFT_parametrizations_def
    by blast
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_assoc_IFT_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and assoc: "branch2_repaired_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_base_IFT_parametrizations
    [OF card4 pf])
  show "branch2_repaired_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
    by (rule branch2_repaired_reduced_base_IFT_parametrizations_all_of_assoc[OF assoc])
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_regular_rank_and_assoc_IFT_chart_theorem:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and regular_rank: "branch2_repaired_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
    and rank_to_assoc:
      "branch2_repaired_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s \<Longrightarrow>
        branch2_repaired_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_base_assoc_IFT_parametrizations
    [OF card4 pf])
  show "branch2_repaired_reduced_base_assoc_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
    by (rule rank_to_assoc[OF regular_rank])
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_regular_rank_and_IFT_chart_theorem:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and regular_rank: "branch2_repaired_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
    and rank_to_ift:
      "branch2_repaired_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s \<Longrightarrow>
        branch2_repaired_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof -
  have ift: "branch2_repaired_reduced_base_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
    by (rule rank_to_ift[OF regular_rank])
  show ?thesis
    by (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_base_IFT_parametrizations
        [OF card4 pf ift])
qed

subsection \<open>\<section>7af: compact repaired IFT chart endpoint\<close>

lemma compact_branch2_u_slice_domain:
  "compact (branch2_u_slice_domain j :: (real^'n::finite) set)"
proof -
  have eq: "branch2_u_slice_domain j = cball (0 :: real^'n) (real (Suc j))"
    unfolding branch2_u_slice_domain_def branch2_u_param_bounded_def
    by (auto simp: dist_norm)
  show ?thesis
    unfolding eq by (rule compact_cball)
qed

lemma compact_branch2_lifted_base_chart_domain:
  fixes C :: "(real^2) set"
  assumes compactC: "compact C"
  shows "compact (C \<times> branch2_u_slice_domain j :: ((real^2) \<times> (real^'n::finite)) set)"
  by (rule compact_Times[OF compactC compact_branch2_u_slice_domain])

lemma closed_branch2_lifted_base_chart_image_of_continuous:
  fixes C :: "(real^2) set"
    and psi :: "real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)"
  assumes compactC: "compact C"
    and cont: "continuous_on (C \<times> branch2_u_slice_domain j)
      (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s psi)"
  shows "closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s psi
      ` (C \<times> branch2_u_slice_domain j))"
  by (intro compact_imp_closed compact_continuous_image cont
      compact_branch2_lifted_base_chart_domain compactC)

lemma closed_branch2_lifted_base_chart_image_of_differentiable:
  fixes C :: "(real^2) set"
    and psi :: "real^2 \<Rightarrow> (((real^2) \<times> (real^'n::finite)) \<times> real)"
  assumes compactC: "compact C"
    and diff: "branch2_lifted_base_chart_x_map \<omega>0 \<omega>s psi
      differentiable_on (C \<times> branch2_u_slice_domain j)"
  shows "closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s psi
      ` (C \<times> branch2_u_slice_domain j))"
  by (rule closed_branch2_lifted_base_chart_image_of_continuous
      [OF compactC differentiable_imp_continuous_on[OF diff]])

lemma branch2_lifted_base_chart_x_map_differentiable_on_cvec_nonzero:
  fixes C :: "(real^2) set"
    and \<phi> :: "real^2 \<Rightarrow> ((real^2) \<times> ((real^'n::finite) \<times> real))"
  assumes der\<phi>: "\<And>s. s \<in> C \<Longrightarrow> \<phi> differentiable (at s)"
    and cnz: "\<And>s. s \<in> C \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s (fst (\<phi> s)) \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> s)) \<noteq> 0"
  shows "branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
      (\<lambda>s. branch2_base_unassoc (\<phi> s))
      differentiable_on (C \<times> branch2_u_slice_domain j)"
proof -
  define D where "D = (C \<times> branch2_u_slice_domain j :: ((real^2) \<times> (real^'n)) set)"
  have comp: "(\<lambda>p. axis m
        (((vec_nth (fst (snd (\<phi> (fst p)))) m)
            / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))
                \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))))
          *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))
        + ((vec_nth (snd p) m)
            / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))
                \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))))
          *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p))))))
      differentiable (at p within D)"
    if pin: "p \<in> D" for m and p :: "(real^2) \<times> (real^'n)"
  proof -
    have fstpC: "fst p \<in> C"
      using pin unfolding D_def by auto
    have \<phi>d_at: "\<phi> differentiable (at (fst p))"
      by (rule der\<phi>[OF fstpC])
    have fst_d: "fst differentiable (at p within D)"
      by (simp add: bounded_linear_imp_differentiable bounded_linear_fst)
    have z_d: "(\<lambda>q::(real^2) \<times> (real^'n). \<phi> (fst q))
        differentiable (at p within D)"
    proof -
      have "(\<phi> \<circ> fst) differentiable (at p within D)"
        by (rule differentiable_chain_within
            [OF fst_d differentiable_at_withinI[OF \<phi>d_at]])
      thus ?thesis by (simp add: o_def)
    qed
    have omega_d: "(\<lambda>q::(real^2) \<times> (real^'n). fst (\<phi> (fst q)))
        differentiable (at p within D)"
    proof -
      have "(fst \<circ> (\<lambda>q::(real^2) \<times> (real^'n). \<phi> (fst q)))
          differentiable (at p within D)"
        by (rule differentiable_chain_within
            [OF z_d bounded_linear_imp_differentiable[OF bounded_linear_fst]])
      thus ?thesis by (simp add: o_def)
    qed
    have c_d: "(\<lambda>q::(real^2) \<times> (real^'n).
          cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q))))
        differentiable (at p within D)"
    proof -
      have c_at: "cvec_dip \<omega>0 \<omega>s differentiable (at (fst (\<phi> (fst p))))"
        using has_derivative_cvec_dip differentiable_def by blast
      have "(cvec_dip \<omega>0 \<omega>s \<circ>
          (\<lambda>q::(real^2) \<times> (real^'n). fst (\<phi> (fst q))))
          differentiable (at p within D)"
        by (rule differentiable_chain_within
            [OF omega_d differentiable_at_withinI[OF c_at]])
      thus ?thesis by (simp add: o_def)
    qed
    have sndz_d: "(\<lambda>q::(real^2) \<times> (real^'n). snd (\<phi> (fst q)))
        differentiable (at p within D)"
    proof -
      have "(snd \<circ> (\<lambda>q::(real^2) \<times> (real^'n). \<phi> (fst q)))
          differentiable (at p within D)"
        by (rule differentiable_chain_within
            [OF z_d bounded_linear_imp_differentiable[OF bounded_linear_snd]])
      thus ?thesis by (simp add: o_def)
    qed
    have t_d: "(\<lambda>q::(real^2) \<times> (real^'n). fst (snd (\<phi> (fst q))))
        differentiable (at p within D)"
    proof -
      have "(fst \<circ> (\<lambda>q::(real^2) \<times> (real^'n). snd (\<phi> (fst q))))
          differentiable (at p within D)"
        by (rule differentiable_chain_within
            [OF sndz_d bounded_linear_imp_differentiable[OF bounded_linear_fst]])
      thus ?thesis by (simp add: o_def)
    qed
    have tm_d: "(\<lambda>q::(real^2) \<times> (real^'n). vec_nth (fst (snd (\<phi> (fst q)))) m)
        differentiable (at p within D)"
    proof -
      have "((\<lambda>v::real^'n. vec_nth v m) \<circ>
          (\<lambda>q::(real^2) \<times> (real^'n). fst (snd (\<phi> (fst q)))))
          differentiable (at p within D)"
        by (rule differentiable_chain_within
            [OF t_d bounded_linear_imp_differentiable[OF bounded_linear_vec_nth]])
      thus ?thesis by (simp add: o_def)
    qed
    have um_d: "(\<lambda>q::(real^2) \<times> (real^'n). vec_nth (snd q) m)
        differentiable (at p within D)"
    proof -
      have bl: "bounded_linear (\<lambda>q::(real^2) \<times> (real^'n). vec_nth (snd q) m)"
        by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_snd])
      show ?thesis
        by (rule bounded_linear_imp_differentiable[OF bl])
    qed
    have denom_d: "(\<lambda>q::(real^2) \<times> (real^'n).
          cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))
            \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q))))
        differentiable (at p within D)"
      by (rule differentiable_inner[OF c_d c_d])
    have denom_nz: "cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))
        \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p))) \<noteq> 0"
      by (rule cnz[OF fstpC])
    have perp_d: "(\<lambda>q::(real^2) \<times> (real^'n).
          perp2 (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
        differentiable (at p within D)"
    proof -
      have "(perp2 \<circ> (\<lambda>q::(real^2) \<times> (real^'n).
          cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
          differentiable (at p within D)"
        by (rule differentiable_chain_within
            [OF c_d bounded_linear_imp_differentiable[OF bounded_linear_perp2]])
      thus ?thesis by (simp add: o_def)
    qed
    have tq_d: "(\<lambda>q::(real^2) \<times> (real^'n).
          vec_nth (fst (snd (\<phi> (fst q)))) m
          / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))
              \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
        differentiable (at p within D)"
      by (rule differentiable_divide[OF tm_d denom_d denom_nz])
    have uq_d: "(\<lambda>q::(real^2) \<times> (real^'n).
          vec_nth (snd q) m
          / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))
              \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
        differentiable (at p within D)"
      by (rule differentiable_divide[OF um_d denom_d denom_nz])
    have sc1_d: "(\<lambda>q::(real^2) \<times> (real^'n).
          (vec_nth (fst (snd (\<phi> (fst q)))) m
          / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))
              \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
          *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q))))
        differentiable (at p within D)"
      by (rule differentiable_scaleR[OF tq_d c_d])
    have sc2_d: "(\<lambda>q::(real^2) \<times> (real^'n).
          (vec_nth (snd q) m
          / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))
              \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
          *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
        differentiable (at p within D)"
      by (rule differentiable_scaleR[OF uq_d perp_d])
    have core: "(\<lambda>q::(real^2) \<times> (real^'n).
        ((vec_nth (fst (snd (\<phi> (fst q)))) m)
            / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))
                \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
          *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))
        + ((vec_nth (snd q) m)
            / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))
                \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
          *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst q)))))
        differentiable (at p within D)"
      by (rule differentiable_add[OF sc1_d sc2_d])
    show ?thesis
      using differentiable_chain_within[OF core
            bounded_linear_imp_differentiable[OF bounded_linear_axis]]
      by (simp add: o_def)
  qed
  have eq: "branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
      (\<lambda>s. branch2_base_unassoc (\<phi> s))
    = (\<lambda>p. \<Sum>m\<in>UNIV. axis m
        (((vec_nth (fst (snd (\<phi> (fst p)))) m)
            / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))
                \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))))
          *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))
        + ((vec_nth (snd p) m)
            / (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))
                \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p)))))
          *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst (\<phi> (fst p))))))"
    unfolding branch2_lifted_base_chart_x_map_def branch2_base_fibre_x_map_def
      branch2_base_unassoc_def branch2_base_param_omega_def branch2_base_param_t_def
      tu_param_map_def Let_def
    by (rule ext) (simp add: vec_lambda_eq_sum_axis)
  have "branch2_lifted_base_chart_x_map \<omega>0 \<omega>s
      (\<lambda>s. branch2_base_unassoc (\<phi> s)) differentiable_on D"
    unfolding eq differentiable_on_def
    by (intro ballI differentiable_sum comp, simp_all)
  thus ?thesis
    unfolding D_def .
qed

lemma compact_cball_cvec_threshold_of_continuous_chart:
  fixes \<phi> :: "real^2 \<Rightarrow> ((real^2) \<times> ((real^'n::finite) \<times> real))"
  assumes cont\<phi>: "continuous_on (cball u0 \<rho>) \<phi>"
  shows "compact (cball u0 \<rho> \<inter>
      {s. a \<le> cvec_dip \<omega>0 \<omega>s (fst (\<phi> s)) \<bullet>
              cvec_dip \<omega>0 \<omega>s (fst (\<phi> s))})"
proof -
  let ?f = "\<lambda>s. cvec_dip \<omega>0 \<omega>s (fst (\<phi> s)) \<bullet>
      cvec_dip \<omega>0 \<omega>s (fst (\<phi> s))"
  have contf: "continuous_on (cball u0 \<rho>) ?f"
    by (intro continuous_on_inner
        continuous_on_compose2[OF continuous_on_cvec_dip
          continuous_on_compose2[OF continuous_on_fst cont\<phi> subset_UNIV]
          subset_UNIV]
        continuous_on_id)
  have closedin: "closedin (top_of_set (cball u0 \<rho>))
      (cball u0 \<rho> \<inter> {s. a \<le> ?f s})"
    using continuous_closedin_preimage[OF contf closed_atLeast, of a]
    by (simp add: vimage_def Int_commute Collect_conj_eq)
  show ?thesis
    by (rule closedin_compact[OF compact_cball closedin])
qed

definition branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. compact (C i))
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j)))"

definition branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>C :: nat \<Rightarrow> (real^2) set.
     \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. compact (C i))
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j)))"

definition branch2_repaired_reduced_base_compact_IFT_parametrizations_all ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow>
    real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branch2_repaired_reduced_base_compact_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
    (\<forall>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
      branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j)"

subsection \<open>\<section>7ag: C1 regular-rank interface for the repaired IFT bridge\<close>

text \<open>
Informal sketch for the remaining C1 regular-rank theorem.

For each repaired chart we need one global derivative field \<open>G'\<close> for the
IFT residual
\<open>branch2_chart?_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s\<close>.  This is a
smoothness problem, not a covering problem: after reassociating the variables,
each residual component is built from projections, the chart map
\<open>ell_chart?\<close>, the moment/phase expressions in \<open>t\<close>, elementary real and
complex algebra, \<open>cvec_dip\<close>/\<open>Dcvec_dip\<close>, and the first derivative of
\<open>gdip\<close>.  The intended construction is to take \<open>G' z\<close> to be the Frechet
derivative of that residual at \<open>z\<close>.  The derivative proof should follow the
same pattern as the earlier joint-C1 arguments: prove the two coordinate
partials with the existing smoothness facts for \<open>gdip\<close>, \<open>cvec_dip\<close>, and the
moment maps, assemble them with \<open>has_derivative_partialsI\<close>, and use the
second differentiability/continuity facts for \<open>gdip\<close> to discharge
\<open>continuous_on UNIV G'\<close>.

The only genuinely geometric part is pointwise surjectivity.  At a system point
\<open>r\<close>, the defining bounded-det condition supplies both \<open>cvec_dip \<noteq> 0\<close> and
\<open>det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0\<close>.  The
unrepaired radial rows give the expected independent directions except at the
old bad slot; the repaired row replaces that slot by the cross-form residual
\<open>branch2_reduced_gradU_scalar\<close>.  The rank algebra should show that the row
family consisting of the special-coefficient row, the unrepaired radial rows
away from \<open>branch2_repair_slot\<close>, and this cross row spans
\<open>(real^'n) \<times> real\<close>.  Chart 1 and chart 2 have the same rank argument after
expanding \<open>ell_chart1\<close> or \<open>ell_chart2\<close>; only the affine chart expression for
\<open>ell\<close> changes.

The formal lemmas immediately below separate these two inputs.  Once the global
C1 fields and the two pointwise surjectivity facts are proved, the all-level
regular-rank theorem follows by definition unfolding.
\<close>

definition branch2_chart1_repaired_reduced_base_C1_regular_rank ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>G' :: ((real^2) \<times> ((real^'n) \<times> real))
        \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real)).
        (\<forall>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
            has_derivative blinfun_apply (G' z)) (at z))
      \<and> continuous_on UNIV G'
      \<and> (\<forall>r\<in>branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
            surj (blinfun_apply (G' (branch2_base_assoc r)))))"

definition branch2_chart2_repaired_reduced_base_C1_regular_rank ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
    (real^2) set \<Rightarrow> nat \<Rightarrow> bool" where
  "branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j \<longleftrightarrow>
    (\<exists>G' :: ((real^2) \<times> ((real^'n) \<times> real))
        \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real)).
        (\<forall>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
            has_derivative blinfun_apply (G' z)) (at z))
      \<and> continuous_on UNIV G'
      \<and> (\<forall>r\<in>branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
            surj (blinfun_apply (G' (branch2_base_assoc r)))))"

definition branch2_repaired_reduced_base_C1_regular_rank_all ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow>
    real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branch2_repaired_reduced_base_C1_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
    (\<forall>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
      (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
      branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j)"

lemma branch2_chart1_repaired_reduced_base_C1_regular_rankI_from_field:
  fixes V :: "((real^2)^'n::finite) set"
    and G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
  assumes der: "\<And>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg: "\<And>r. r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<Longrightarrow> surj (blinfun_apply (G' (branch2_base_assoc r)))"
  shows "branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
  unfolding branch2_chart1_repaired_reduced_base_C1_regular_rank_def
  by (intro exI[where x = G'] conjI allI ballI der cont reg)

lemma branch2_chart2_repaired_reduced_base_C1_regular_rankI_from_field:
  fixes V :: "((real^2)^'n::finite) set"
    and G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
  assumes der: "\<And>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg: "\<And>r. r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<Longrightarrow> surj (blinfun_apply (G' (branch2_base_assoc r)))"
  shows "branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
  unfolding branch2_chart2_repaired_reduced_base_C1_regular_rank_def
  by (intro exI[where x = G'] conjI allI ballI der cont reg)

theorem branch2_repaired_reduced_base_C1_regular_rank_allI_from_fields:
  fixes V :: "((real^2)^'n::finite) set"
    and G1' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    and G2' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
  assumes der1: "\<And>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply (G1' z)) (at z)"
    and cont1: "continuous_on UNIV G1'"
    and reg1: "\<And>\<Gamma> j r. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (\<And>\<omega>. \<omega> \<in> \<Gamma> \<Longrightarrow> \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
      r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<Longrightarrow> surj (blinfun_apply (G1' (branch2_base_assoc r)))"
    and der2: "\<And>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply (G2' z)) (at z)"
    and cont2: "continuous_on UNIV G2'"
    and reg2: "\<And>\<Gamma> j r. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (\<And>\<omega>. \<omega> \<in> \<Gamma> \<Longrightarrow> \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
      r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<Longrightarrow> surj (blinfun_apply (G2' (branch2_base_assoc r)))"
  shows "branch2_repaired_reduced_base_C1_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branch2_repaired_reduced_base_C1_regular_rank_all_def
proof (intro allI impI conjI)
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep0: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  have Gindep: "\<And>\<omega>. \<omega> \<in> \<Gamma> \<Longrightarrow> \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    using Gindep0 by blast
  show "branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
    by (rule branch2_chart1_repaired_reduced_base_C1_regular_rankI_from_field
        [OF der1 cont1]) (rule reg1[OF Gsub Gindep])
  show "branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
    by (rule branch2_chart2_repaired_reduced_base_C1_regular_rankI_from_field
        [OF der2 cont2]) (rule reg2[OF Gsub Gindep])
qed

lemma Ck1_on_imp_has_derivative_blinfun_rnv:
  fixes G :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes C1: "Ck_on (Suc 0) G W"
  shows "\<And>z. z \<in> W \<Longrightarrow> (G has_derivative blinfun_apply (Dblinfun G z)) (at z)"
proof -
  fix z assume zW: "z \<in> W"
  have "Ck_at (Suc 0) G z"
    using C1 zW by (simp add: Ck_on_def)
  hence diff: "G differentiable (at z)"
    by (rule Ck1_atD)
  show "(G has_derivative blinfun_apply (Dblinfun G z)) (at z)"
    using diff by (simp add: blinfun_apply_Dblinfun frechet_derivative_works)
qed

lemma Ck1_on_imp_continuous_Dblinfun_branch2_base:
  fixes G :: "((real^2) \<times> ((real^'n::finite) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)"
  assumes C1: "Ck_on (Suc 0) G W"
  shows "continuous_on W (Dblinfun G)"
proof (rule continuous_on_blinfun_componentwise)
  fix i :: "((real^2) \<times> ((real^'n) \<times> real))"
  assume i: "i \<in> Basis"
  have W_open: "open W"
    using C1 by (simp add: Ck_on_def)
  have cont_dir: "continuous_on W (\<lambda>z. frechet_derivative G (at z) i)"
  proof (rule continuous_at_imp_continuous_on, rule ballI)
    fix z assume zW: "z \<in> W"
    have "Ck_at (Suc 0) G z"
      using C1 zW by (simp add: Ck_on_def)
    thus "continuous (at z) (\<lambda>z. frechet_derivative G (at z) i)"
      by (rule Ck1_atD(2))
  qed
  have eq: "\<And>z. z \<in> W \<Longrightarrow> blinfun_apply (Dblinfun G z) i =
      frechet_derivative G (at z) i"
  proof -
    fix z assume zW: "z \<in> W"
    have "Ck_at (Suc 0) G z"
      using C1 zW by (simp add: Ck_on_def)
    hence "G differentiable (at z)"
      by (rule Ck1_atD)
    thus "blinfun_apply (Dblinfun G z) i = frechet_derivative G (at z) i"
      by (simp add: blinfun_apply_Dblinfun)
  qed
  show "continuous_on W (\<lambda>z. blinfun_apply (Dblinfun G z) i)"
    using cont_dir eq by (simp cong: continuous_on_cong)
qed

lemma branch2_chart1_repaired_reduced_base_C1_field_from_Ck1:
  assumes C1: "Ck_on (Suc 0)
    (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
      ((real^2) \<times> ((real^'n::finite) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)) UNIV"
  shows "(\<And>(z :: ((real^2) \<times> ((real^'n::finite) \<times> real))).
      (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply
        (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s) z)) (at z))"
    and "continuous_on UNIV
      (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)))"
proof -
  show "\<And>(z :: ((real^2) \<times> ((real^'n) \<times> real))).
      (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply
        (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s) z)) (at z)"
  proof -
    fix z :: "((real^2) \<times> ((real^'n) \<times> real))"
    show "(branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply
          (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s) z)) (at z)"
      by (rule Ck1_on_imp_has_derivative_blinfun_rnv
          [where G = "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
              ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)"
             and W = UNIV, OF C1]) simp
  qed
  show "continuous_on UNIV
      (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)))"
    by (rule Ck1_on_imp_continuous_Dblinfun_branch2_base
        [where G = "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
            ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)"
           and W = UNIV, OF C1])
qed

lemma branch2_chart2_repaired_reduced_base_C1_field_from_Ck1:
  assumes C1: "Ck_on (Suc 0)
    (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
      ((real^2) \<times> ((real^'n::finite) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)) UNIV"
  shows "(\<And>(z :: ((real^2) \<times> ((real^'n::finite) \<times> real))).
      (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply
        (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s) z)) (at z))"
    and "continuous_on UNIV
      (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)))"
proof -
  show "\<And>(z :: ((real^2) \<times> ((real^'n) \<times> real))).
      (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply
        (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s) z)) (at z)"
  proof -
    fix z :: "((real^2) \<times> ((real^'n) \<times> real))"
    show "(branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply
          (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s) z)) (at z)"
      by (rule Ck1_on_imp_has_derivative_blinfun_rnv
          [where G = "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
              ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)"
             and W = UNIV, OF C1]) simp
  qed
  show "continuous_on UNIV
      (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)))"
    by (rule Ck1_on_imp_continuous_Dblinfun_branch2_base
        [where G = "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
            ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)"
           and W = UNIV, OF C1])
qed

lemma branch2_chart1_repaired_reduced_base_system_cvec_nonzero:
  assumes rin: "r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  shows "cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0"
proof -
  have "branch2_base_param_bounded_det \<omega>0 \<omega>s r j"
    using rin unfolding branch2_chart1_repaired_reduced_base_system_def by blast
  thus ?thesis
    by (rule branch2_base_param_bounded_det_imp_cvec_nonzero)
qed

lemma branch2_chart2_repaired_reduced_base_system_cvec_nonzero:
  assumes rin: "r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  shows "cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0"
proof -
  have "branch2_base_param_bounded_det \<omega>0 \<omega>s r j"
    using rin unfolding branch2_chart2_repaired_reduced_base_system_def by blast
  thus ?thesis
    by (rule branch2_base_param_bounded_det_imp_cvec_nonzero)
qed

lemma branch2_chart1_repaired_reduced_base_system_Dcvec_det_nonzero:
  assumes rin: "r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0"
proof -
  have "branch2_base_param_bounded_det \<omega>0 \<omega>s r j"
    using rin unfolding branch2_chart1_repaired_reduced_base_system_def by blast
  thus ?thesis
    by (rule branch2_base_param_bounded_det_imp_Dcvec_det_nonzero)
qed

lemma branch2_chart2_repaired_reduced_base_system_Dcvec_det_nonzero:
  assumes rin: "r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0"
proof -
  have "branch2_base_param_bounded_det \<omega>0 \<omega>s r j"
    using rin unfolding branch2_chart2_repaired_reduced_base_system_def by blast
  thus ?thesis
    by (rule branch2_base_param_bounded_det_imp_Dcvec_det_nonzero)
qed

theorem branch2_repaired_reduced_base_C1_regular_rank_allI_from_pointwise_rank:
  fixes V :: "((real^2)^'n::finite) set"
    and G1' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    and G2' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
  assumes der1: "\<And>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply (G1' z)) (at z)"
    and cont1: "continuous_on UNIV G1'"
    and reg1: "\<And>r. branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0) \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0 \<Longrightarrow>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0
      \<Longrightarrow> surj (blinfun_apply (G1' (branch2_base_assoc r)))"
    and der2: "\<And>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply (G2' z)) (at z)"
    and cont2: "continuous_on UNIV G2'"
    and reg2: "\<And>r. branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0) \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0 \<Longrightarrow>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0
      \<Longrightarrow> surj (blinfun_apply (G2' (branch2_base_assoc r)))"
  shows "branch2_repaired_reduced_base_C1_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branch2_repaired_reduced_base_C1_regular_rank_allI_from_fields
    [OF der1 cont1 _ der2 cont2])
  fix \<Gamma> :: "(real^2) set" and j :: nat
    and r :: "(((real^2) \<times> (real^'n)) \<times> real)"
  assume rin: "r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  have zero: "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      (branch2_base_assoc r) = (0, 0)"
    using rin branch2_chart1_repaired_reduced_base_system_assoc_iff[of r \<omega>0 \<omega>s \<Gamma> j]
    by blast
  show "surj (blinfun_apply (G1' (branch2_base_assoc r)))"
    by (rule reg1[OF zero
          branch2_chart1_repaired_reduced_base_system_cvec_nonzero[OF rin]
          branch2_chart1_repaired_reduced_base_system_Dcvec_det_nonzero[OF rin]])
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
    and r :: "(((real^2) \<times> (real^'n)) \<times> real)"
  assume rin: "r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  have zero: "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      (branch2_base_assoc r) = (0, 0)"
    using rin branch2_chart2_repaired_reduced_base_system_assoc_iff[of r \<omega>0 \<omega>s \<Gamma> j]
    by blast
  show "surj (blinfun_apply (G2' (branch2_base_assoc r)))"
    by (rule reg2[OF zero
          branch2_chart2_repaired_reduced_base_system_cvec_nonzero[OF rin]
          branch2_chart2_repaired_reduced_base_system_Dcvec_det_nonzero[OF rin]])
qed

theorem branch2_repaired_reduced_base_C1_regular_rank_allI_from_Ck1_and_pointwise_rank:
  fixes V :: "((real^2)^'n::finite) set"
  assumes C1_1: "Ck_on (Suc 0)
      (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)) UNIV"
    and C1_2: "Ck_on (Suc 0)
      (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)) UNIV"
    and reg1: "\<And>(r :: (((real^2) \<times> (real^'n)) \<times> real)).
      branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0) \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0 \<Longrightarrow>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0
      \<Longrightarrow> surj (blinfun_apply
        (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
            ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real))
          (branch2_base_assoc r)))"
    and reg2: "\<And>(r :: (((real^2) \<times> (real^'n)) \<times> real)).
      branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0) \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0 \<Longrightarrow>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0
      \<Longrightarrow> surj (blinfun_apply
        (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
            ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real))
          (branch2_base_assoc r)))"
  shows "branch2_repaired_reduced_base_C1_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branch2_repaired_reduced_base_C1_regular_rank_allI_from_pointwise_rank
    [where G1' = "Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real))"
       and G2' = "Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real))"])
  show "\<And>(z :: ((real^2) \<times> ((real^'n) \<times> real))).
      (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply
        (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s) z)) (at z)"
    by (rule branch2_chart1_repaired_reduced_base_C1_field_from_Ck1(1)[OF C1_1])
  show "continuous_on UNIV
      (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)))"
    by (rule branch2_chart1_repaired_reduced_base_C1_field_from_Ck1(2)[OF C1_1])
  show "\<And>(r :: (((real^2) \<times> (real^'n)) \<times> real)).
    branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      (branch2_base_assoc r) = (0, 0) \<Longrightarrow>
    cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0 \<Longrightarrow>
    det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0 \<Longrightarrow>
    surj (blinfun_apply
      (Dblinfun (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
          ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real))
        (branch2_base_assoc r)))"
    by (rule reg1)
  show "\<And>(z :: ((real^2) \<times> ((real^'n) \<times> real))).
      (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      has_derivative blinfun_apply
        (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s) z)) (at z)"
    by (rule branch2_chart2_repaired_reduced_base_C1_field_from_Ck1(1)[OF C1_2])
  show "continuous_on UNIV
      (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
        ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real)))"
    by (rule branch2_chart2_repaired_reduced_base_C1_field_from_Ck1(2)[OF C1_2])
  show "\<And>(r :: (((real^2) \<times> (real^'n)) \<times> real)).
    branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      (branch2_base_assoc r) = (0, 0) \<Longrightarrow>
    cvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r) \<noteq> 0 \<Longrightarrow>
    det (matrix (Dcvec_dip \<omega>0 \<omega>s (branch2_base_param_omega r))) \<noteq> 0 \<Longrightarrow>
    surj (blinfun_apply
      (Dblinfun (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s ::
          ((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow> ((real^'n) \<times> real))
        (branch2_base_assoc r)))"
    by (rule reg2)
qed

lemma branch2_chart1_repaired_reduced_base_C1_regular_rankD:
  fixes V :: "((real^2)^'n::finite) set"
  assumes c1: "branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
  obtains G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    where "\<And>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
      and "continuous_on UNIV G'"
      and "\<And>r. r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<Longrightarrow> surj (blinfun_apply (G' (branch2_base_assoc r)))"
proof -
  obtain G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    where der: "\<forall>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
      and cont: "continuous_on UNIV G'"
      and reg: "\<forall>r\<in>branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
        surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using c1 unfolding branch2_chart1_repaired_reduced_base_C1_regular_rank_def
    by blast
  show ?thesis
    by (rule that[of G']) (use der cont reg in auto)
qed

lemma branch2_chart2_repaired_reduced_base_C1_regular_rankD:
  fixes V :: "((real^2)^'n::finite) set"
  assumes c1: "branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
  obtains G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    where "\<And>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
      and "continuous_on UNIV G'"
      and "\<And>r. r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<Longrightarrow> surj (blinfun_apply (G' (branch2_base_assoc r)))"
proof -
  obtain G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    where der: "\<forall>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
      and cont: "continuous_on UNIV G'"
      and reg: "\<forall>r\<in>branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
        surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using c1 unfolding branch2_chart2_repaired_reduced_base_C1_regular_rank_def
    by blast
  show ?thesis
    by (rule that[of G']) (use der cont reg in auto)
qed

lemma branch2_chart1_repaired_reduced_base_C1_regular_rank_local_chart:
  fixes V :: "((real^2)^'n::finite) set"
    and r :: "(((real^2) \<times> (real^'n)) \<times> real)"
  assumes c1: "branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
    and rin: "r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  shows "\<exists>U u0 \<phi> g D\<phi>.
      open (U :: (real^2) set) \<and> u0 \<in> U \<and> \<phi> u0 = branch2_base_assoc r
      \<and> \<phi> differentiable_on U
      \<and> \<phi> ` U \<subseteq> {z. branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)}
      \<and> openin (top_of_set {z. branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` U)
      \<and> homeomorphism U (\<phi> ` U) \<phi> g
      \<and> (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u))"
proof -
  obtain G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    where der_all:
      "\<forall>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg_all0: "\<forall>r\<in>branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
      surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using c1 unfolding branch2_chart1_repaired_reduced_base_C1_regular_rank_def
    by blast
  have der: "\<And>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    using der_all by blast
  have reg_all: "\<And>r. r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<Longrightarrow> surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using reg_all0 by blast
  have zero: "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      (branch2_base_assoc r) = (0, 0)"
    using rin branch2_chart1_repaired_reduced_base_system_assoc_iff[of r \<omega>0 \<omega>s \<Gamma> j]
    by blast
  have reg: "surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using reg_all[OF rin] .
  show ?thesis
    using branch2_chart1_repaired_reduced_base_IFT_residual_local_chart
      [OF zero der cont reg]
    by blast
qed

lemma branch2_chart2_repaired_reduced_base_C1_regular_rank_local_chart:
  fixes V :: "((real^2)^'n::finite) set"
    and r :: "(((real^2) \<times> (real^'n)) \<times> real)"
  assumes c1: "branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
    and rin: "r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  shows "\<exists>U u0 \<phi> g D\<phi>.
      open (U :: (real^2) set) \<and> u0 \<in> U \<and> \<phi> u0 = branch2_base_assoc r
      \<and> \<phi> differentiable_on U
      \<and> \<phi> ` U \<subseteq> {z. branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)}
      \<and> openin (top_of_set {z. branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` U)
      \<and> homeomorphism U (\<phi> ` U) \<phi> g
      \<and> (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u))"
proof -
  obtain G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    where der_all:
      "\<forall>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg_all0: "\<forall>r\<in>branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
      surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using c1 unfolding branch2_chart2_repaired_reduced_base_C1_regular_rank_def
    by blast
  have der: "\<And>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    using der_all by blast
  have reg_all: "\<And>r. r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<Longrightarrow> surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using reg_all0 by blast
  have zero: "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      (branch2_base_assoc r) = (0, 0)"
    using rin branch2_chart2_repaired_reduced_base_system_assoc_iff[of r \<omega>0 \<omega>s \<Gamma> j]
    by blast
  have reg: "surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using reg_all[OF rin] .
  show ?thesis
    using branch2_chart2_repaired_reduced_base_IFT_residual_local_chart
      [OF zero der cont reg]
    by blast
qed

lemma branch2_chart1_repaired_reduced_base_C1_regular_rank_cball_chart:
  fixes V :: "((real^2)^'n::finite) set"
    and r :: "(((real^2) \<times> (real^'n)) \<times> real)"
  assumes c1: "branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
    and rin: "r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  shows "\<exists>(u0 :: real^2) \<rho> \<phi> D\<phi>.
      0 < \<rho> \<and> \<phi> u0 = branch2_base_assoc r
      \<and> (\<forall>u\<in>cball u0 \<rho>.
          branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
          \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u))
      \<and> continuous_on (cball u0 \<rho>) \<phi>
      \<and> branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho>
      \<and> openin (top_of_set {z. branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` ball u0 \<rho>)"
proof -
  obtain G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    where der_all:
      "\<forall>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg_all0: "\<forall>r\<in>branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
      surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using c1 unfolding branch2_chart1_repaired_reduced_base_C1_regular_rank_def
    by blast
  have der: "\<And>z. (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    using der_all by blast
  have reg_all: "\<And>r. r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<Longrightarrow> surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using reg_all0 by blast
  have zero: "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      (branch2_base_assoc r) = 0"
    using rin branch2_chart1_repaired_reduced_base_system_assoc_iff[of r \<omega>0 \<omega>s \<Gamma> j]
    by (auto simp: zero_prod_def)
  have reg: "surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using reg_all[OF rin] .
  have der_UNIV: "\<And>z. z \<in> UNIV \<Longrightarrow>
      (branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    using der by simp
  have bz:
    "\<exists>u0 :: real^2.
      \<exists>\<rho> :: real.
      \<exists>\<phi> :: (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
      \<exists>D\<phi>.
        0 < \<rho>
      \<and> \<phi> u0 = branch2_base_assoc r
      \<and> (\<forall>u\<in>cball u0 \<rho>.
          \<phi> u \<in> UNIV
        \<and> branch2_chart1_repaired_reduced_base_IFT_residual
            \<omega>0 \<omega>s (\<phi> u) = (0, 0)
        \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)
        \<and> range (blinfun_apply (D\<phi> u)) =
            {w. blinfun_apply (G' (\<phi> u)) w = (0, 0)})
      \<and> continuous_on (cball u0 \<rho>) \<phi>
      \<and> branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho>
      \<and> openin
          (top_of_set
            {z \<in> UNIV.
              branch2_chart1_repaired_reduced_base_IFT_residual
                \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` ball u0 \<rho>)"
    using bad_zero_chart
      [where W = UNIV
        and G = "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s"
        and G' = G'
        and q = "branch2_base_assoc r",
        OF open_UNIV der_UNIV cont reg UNIV_I zero]
    by (auto simp: zero_prod_def)
  show ?thesis
    using bz by (auto simp: zero_prod_def, metis (lifting) centre_in_ball image_eqI)
qed

lemma branch2_chart2_repaired_reduced_base_C1_regular_rank_cball_chart:
  fixes V :: "((real^2)^'n::finite) set"
    and r :: "(((real^2) \<times> (real^'n)) \<times> real)"
  assumes c1: "branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
    and rin: "r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  shows "\<exists>(u0 :: real^2) \<rho> \<phi> D\<phi>.
      0 < \<rho> \<and> \<phi> u0 = branch2_base_assoc r
      \<and> (\<forall>u\<in>cball u0 \<rho>.
          branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
          \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u))
      \<and> continuous_on (cball u0 \<rho>) \<phi>
      \<and> branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho>
      \<and> openin (top_of_set {z. branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` ball u0 \<rho>)"
proof -
  obtain G' :: "((real^2) \<times> ((real^'n) \<times> real))
      \<Rightarrow> (((real^2) \<times> ((real^'n) \<times> real)) \<Rightarrow>\<^sub>L ((real^'n) \<times> real))"
    where der_all:
      "\<forall>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    and cont: "continuous_on UNIV G'"
    and reg_all0: "\<forall>r\<in>branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j.
      surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using c1 unfolding branch2_chart2_repaired_reduced_base_C1_regular_rank_def
    by blast
  have der: "\<And>z. (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    using der_all by blast
  have reg_all: "\<And>r. r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<Longrightarrow> surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using reg_all0 by blast
  have zero: "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
      (branch2_base_assoc r) = 0"
    using rin branch2_chart2_repaired_reduced_base_system_assoc_iff[of r \<omega>0 \<omega>s \<Gamma> j]
    by (auto simp: zero_prod_def)
  have reg: "surj (blinfun_apply (G' (branch2_base_assoc r)))"
    using reg_all[OF rin] .
  have der_UNIV: "\<And>z. z \<in> UNIV \<Longrightarrow>
      (branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        has_derivative blinfun_apply (G' z)) (at z)"
    using der by simp
  have bz:
    "\<exists>u0 :: real^2.
      \<exists>\<rho> :: real.
      \<exists>\<phi> :: (real^2) \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
      \<exists>D\<phi>.
        0 < \<rho>
      \<and> \<phi> u0 = branch2_base_assoc r
      \<and> (\<forall>u\<in>cball u0 \<rho>.
          branch2_chart2_repaired_reduced_base_IFT_residual
            \<omega>0 \<omega>s (\<phi> u) = (0, 0)
        \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)
        \<and> range (blinfun_apply (D\<phi> u)) =
            {w. blinfun_apply (G' (\<phi> u)) w = (0, 0)})
      \<and> continuous_on (cball u0 \<rho>) \<phi>
      \<and> branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho>
      \<and> openin
          (top_of_set
            {z. branch2_chart2_repaired_reduced_base_IFT_residual
                  \<omega>0 \<omega>s z = (0, 0)})
          (\<phi> ` ball u0 \<rho>)"
    using bad_zero_chart
      [where W = UNIV
        and G = "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s"
        and G' = G'
        and q = "branch2_base_assoc r",
        OF open_UNIV der_UNIV cont reg UNIV_I zero]
    by (auto simp: zero_prod_def)
  show ?thesis
    using bz by blast
qed


lemma branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations_of_C1_regular_rank:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega>0 \<omega>s :: "real^2"
    and \<Gamma> :: "(real^2) set"
    and j :: nat
  assumes c1: "branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
  shows "branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
proof (cases "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
    = ({} :: ((((real^2) \<times> (real^'n)) \<times> real)) set)")
  case True
  have empty_cover: "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i::nat. ((\<lambda>_. undefined)
          :: real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)) ` ({} :: (real^2) set))"
    using True by simp
  show ?thesis
    unfolding branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations_def
    by (intro exI[where x = "\<lambda>_. {}"]
        exI[where x = "\<lambda>_ _. undefined"] conjI empty_cover) auto
next
  case False
  define S :: "(((real^2) \<times> (real^'n)) \<times> real) set"
    where "S = branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  define Z :: "((real^2) \<times> ((real^'n) \<times> real)) set"
    where "Z = {z. branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)}"
  define A :: "((real^2) \<times> ((real^'n) \<times> real)) set"
    where "A = branch2_base_assoc ` S"
  define \<F> :: "(((real^2) \<times> ((real^'n) \<times> real)) set) set"
    where "\<F> =
    {A \<inter> (\<phi> ` ball u0 \<rho>) |(u0 :: real^2) \<rho> \<phi> D\<phi> r.
      r \<in> S \<and>
      0 < \<rho> \<and> \<phi> u0 = branch2_base_assoc r \<and>
      (\<forall>u\<in>cball u0 \<rho>.
        branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
        \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
      continuous_on (cball u0 \<rho>) \<phi> \<and>
      branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho> \<and>
      openin (top_of_set Z) (\<phi> ` ball u0 \<rho>)}"
  have S_ne: "S \<noteq> {}"
    using False unfolding S_def by simp
  have A_ne: "A \<noteq> {}"
    using S_ne unfolding A_def by blast
  have A_sub_Z: "A \<subseteq> Z"
  proof
    fix z assume "z \<in> A"
    then obtain r where rS: "r \<in> S" and z: "z = branch2_base_assoc r"
      unfolding A_def by blast
    have "branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0)"
      using rS unfolding S_def
      using branch2_chart1_repaired_reduced_base_system_assoc_iff[of r \<omega>0 \<omega>s \<Gamma> j]
      by blast
    thus "z \<in> Z"
      unfolding Z_def z by simp
  qed
  have openF: "\<And>U. U \<in> \<F> \<Longrightarrow> openin (top_of_set A) U"
  proof -
    fix U assume "U \<in> \<F>"
    then obtain u0 :: "real^2"
      and \<rho> :: real
      and \<phi> :: "real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))" where
      U_def: "U = A \<inter> \<phi> ` ball u0 \<rho>"
      and openU: "openin (top_of_set Z) (\<phi> ` ball u0 \<rho>)"
      unfolding \<F>_def mem_Collect_eq by (elim exE conjE) metis
    have "openin (top_of_set A) (A \<inter> (\<phi> ` ball u0 \<rho>))"
      using openU A_sub_Z
      by (simp add: inf.absorb_iff2 openin_subtopology_Int2, 
          metis openin_subtopology_Int2 subtopology_subtopology)
    thus "openin (top_of_set A) U"
      unfolding U_def .
  qed
  have coverF: "A \<subseteq> \<Union>\<F>"
  proof
    fix z assume zA: "z \<in> A"
    then obtain r where rS: "r \<in> S" and z: "z = branch2_base_assoc r"
      unfolding A_def by blast
    have rin: "r \<in> branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
      using rS unfolding S_def .
    obtain u0 :: "real^2"
      and \<rho> :: real
      and \<phi> :: "real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))"
      and D\<phi> :: "real^2 \<Rightarrow> (real^2, ((real^2) \<times> ((real^'n) \<times> real))) blinfun" where
      rho: "0 < \<rho>" and phi0: "\<phi> u0 = branch2_base_assoc r"
      and der: "\<forall>u\<in>cball u0 \<rho>.
          branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
          \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)"
      and cont: "continuous_on (cball u0 \<rho>) \<phi>"
      and image: "branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho>"
      and open_set: "openin (top_of_set Z) (\<phi> ` ball u0 \<rho>)"
      using branch2_chart1_repaired_reduced_base_C1_regular_rank_cball_chart
        [OF c1 rin]
      unfolding Z_def by (elim exE conjE) metis
    have Uin: "A \<inter> \<phi> ` ball u0 \<rho> \<in> \<F>"
      unfolding \<F>_def mem_Collect_eq
      by (rule exI[of _ u0], rule exI[of _ \<rho>], rule exI[of _ \<phi>],
          rule exI[of _ D\<phi>], rule exI[of _ r], intro conjI,
          rule refl, rule rS, rule rho, rule phi0, rule der, rule cont,
          rule image, rule open_set)
    have "z \<in> A \<inter> \<phi> ` ball u0 \<rho>"
      using zA z image by blast
    thus "z \<in> \<Union>\<F>"
      using Uin by blast
  qed
  obtain fs where fs_sub: "fs \<subseteq> \<F>" and fs_cnt: "countable fs" and fs_cover: "A \<subseteq> \<Union>fs"
    by (rule countable_subcover_of_openin_cover[OF openF coverF])
  have fs_ne: "fs \<noteq> {}"
    using A_ne fs_cover by blast
  define U where "U = from_nat_into fs"
  have UinF: "U i \<in> \<F>" for i
    using from_nat_into[OF fs_ne, of i] fs_sub unfolding U_def by blast
  have Urange: "fs \<subseteq> range U"
    unfolding U_def
    by (metis fs_cnt subset_range_from_nat_into top1_countable_nonempty_eq_image_nat uncountable_def) 
  have witness_ex: "\<forall>i.
      \<exists>u0 :: real^2. \<exists>\<rho> :: real.
      \<exists>\<phi> :: real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
      \<exists>D\<phi> :: real^2 \<Rightarrow> (real^2, ((real^2) \<times> ((real^'n) \<times> real))) blinfun.
      \<exists>r :: ((real^2) \<times> (real^'n)) \<times> real.
      r \<in> S \<and>
      0 < \<rho> \<and> \<phi> u0 = branch2_base_assoc r \<and>
      (\<forall>u\<in>cball u0 \<rho>.
        branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
        \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
      continuous_on (cball u0 \<rho>) \<phi> \<and>
      branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho> \<and>
      openin (top_of_set Z) (\<phi> ` ball u0 \<rho>) \<and>
      U i = A \<inter> \<phi> ` ball u0 \<rho>"
  proof
    fix i
    show "\<exists>u0 :: real^2. \<exists>\<rho> :: real.
      \<exists>\<phi> :: real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
      \<exists>D\<phi> :: real^2 \<Rightarrow> (real^2, ((real^2) \<times> ((real^'n) \<times> real))) blinfun.
      \<exists>r :: ((real^2) \<times> (real^'n)) \<times> real.
      r \<in> S \<and>
      0 < \<rho> \<and> \<phi> u0 = branch2_base_assoc r \<and>
      (\<forall>u\<in>cball u0 \<rho>.
        branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
        \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
      continuous_on (cball u0 \<rho>) \<phi> \<and>
      branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho> \<and>
      openin (top_of_set Z) (\<phi> ` ball u0 \<rho>) \<and>
      U i = A \<inter> \<phi> ` ball u0 \<rho>"
      using UinF[of i] unfolding \<F>_def mem_Collect_eq
      by (elim exE conjE) (intro exI conjI; assumption)
  qed
  then obtain u0 :: "nat \<Rightarrow> real^2"
    and \<rho> :: "nat \<Rightarrow> real"
    and \<phi> :: "nat \<Rightarrow> real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))"
    and D\<phi> :: "nat \<Rightarrow> real^2 \<Rightarrow> (real^2, ((real^2) \<times> ((real^'n) \<times> real))) blinfun"
    and r :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<times> real" where wit:
    "\<And>i. r i \<in> S \<and>
      0 < \<rho> i \<and> \<phi> i (u0 i) = branch2_base_assoc (r i) \<and>
      (\<forall>u\<in>cball (u0 i) (\<rho> i).
        branch2_chart1_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> i u) = (0, 0)
        \<and> (\<phi> i has_derivative blinfun_apply (D\<phi> i u)) (at u)) \<and>
      continuous_on (cball (u0 i) (\<rho> i)) (\<phi> i) \<and>
      branch2_base_assoc (r i) \<in> \<phi> i ` ball (u0 i) (\<rho> i) \<and>
      openin (top_of_set Z) (\<phi> i ` ball (u0 i) (\<rho> i)) \<and>
      U i = A \<inter> \<phi> i ` ball (u0 i) (\<rho> i)"
    by metis
  define i_of where "i_of n = fst (prod_decode n)" for n
  define k_of where "k_of n = snd (prod_decode n)" for n
  define C where "C n =
    (cball (u0 (i_of n)) (\<rho> (i_of n)) \<inter>
      {s. 1 / real (Suc (k_of n)) \<le>
        cvec_dip \<omega>0 \<omega>s (fst (\<phi> (i_of n) s)) \<bullet>
        cvec_dip \<omega>0 \<omega>s (fst (\<phi> (i_of n) s))})" for n
  define psi where "psi n s = branch2_base_unassoc (\<phi> (i_of n) s)" for n s
  have coverC: "S \<subseteq> (\<Union>n. psi n ` C n)"
  proof
    fix x assume xS: "x \<in> S"
    have zA: "branch2_base_assoc x \<in> A"
      using xS unfolding A_def by blast
    then obtain Ob where Ofs: "Ob \<in> fs" and zO: "branch2_base_assoc x \<in> Ob"
      using fs_cover by blast
    obtain i where Oeq: "Ob = U i"
      using Urange Ofs by blast
    have zUi: "branch2_base_assoc x \<in> U i"
      using zO Oeq by simp
    then obtain s where sball: "s \<in> ball (u0 i) (\<rho> i)"
      and phis: "\<phi> i s = branch2_base_assoc x"
      using wit[of i]
      by auto 
    have xbounded: "branch2_base_param_bounded_det \<omega>0 \<omega>s x j"
      using xS unfolding S_def branch2_chart1_repaired_reduced_base_system_def by blast
    have thresh: "1 / real (Suc j) \<le>
        cvec_dip \<omega>0 \<omega>s (fst (\<phi> i s)) \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> i s))"
      using xbounded phis
      unfolding branch2_base_param_bounded_det_def branch2_base_assoc_def
        branch2_base_param_omega_def
      by (metis branch2_base_param_bounded_def branch2_base_param_omega_def fst_conv)
      
    define n where "n = prod_encode (i, j)"
    have i_n: "i_of n = i"
      unfolding i_of_def n_def by simp
    have k_n: "k_of n = j"
      unfolding k_of_def n_def by simp
    have sC: "s \<in> C n"
      using sball thresh unfolding C_def i_n k_n by auto
    have "x = psi n s"
      using phis unfolding psi_def i_n by simp
    thus "x \<in> (\<Union>n. psi n ` C n)"
      using sC by blast
  qed
  have compactC: "compact (C n)" for n
    unfolding C_def
    by (rule compact_cball_cvec_threshold_of_continuous_chart)
       (use wit in blast)
  have diffC: "branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi n)
      differentiable_on (C n \<times> branch2_u_slice_domain j)" for n
  proof -
    have der: "\<And>s. s \<in> C n \<Longrightarrow> \<phi> (i_of n) differentiable (at s)"
      unfolding C_def differentiable_def
      using wit[of "i_of n"] by blast
    have cnz: "\<And>s. s \<in> C n \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s (fst (\<phi> (i_of n) s)) \<bullet>
      cvec_dip \<omega>0 \<omega>s (fst (\<phi> (i_of n) s)) \<noteq> 0"
      unfolding C_def by auto
    show ?thesis
      unfolding psi_def
      by (rule branch2_lifted_base_chart_x_map_differentiable_on_cvec_nonzero
          [OF der cnz])
  qed
  show ?thesis
    unfolding branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations_def
  proof (intro exI[where x = C] exI[where x = psi] conjI)
    show "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. psi i ` C i)"
      using coverC unfolding S_def .
    show "\<forall>i. compact (C i)"
      by (rule allI, rule compactC)
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      by (rule allI, rule diffC)
  qed
qed

lemma branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations_of_C1_regular_rank:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega>0 \<omega>s :: "real^2"
    and \<Gamma> :: "(real^2) set"
    and j :: nat
  assumes c1: "branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
  shows "branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
proof (cases "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
    = ({} :: ((((real^2) \<times> (real^'n)) \<times> real)) set)")
  case True
  have empty_cover: "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
      \<subseteq> (\<Union>i::nat. ((\<lambda>_. undefined)
          :: real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)) ` ({} :: (real^2) set))"
    using True by simp
  show ?thesis
    unfolding branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations_def
    by (intro exI[where x = "\<lambda>_. {}"]
        exI[where x = "\<lambda>_ _. undefined"] conjI empty_cover) auto
next
  case False
  define S :: "(((real^2) \<times> (real^'n)) \<times> real) set"
    where "S = branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
  define Z :: "((real^2) \<times> ((real^'n) \<times> real)) set"
    where "Z = {z. branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s z = (0, 0)}"
  define A :: "((real^2) \<times> ((real^'n) \<times> real)) set"
    where "A = branch2_base_assoc ` S"
  define \<F> :: "(((real^2) \<times> ((real^'n) \<times> real)) set) set"
    where "\<F> =
    {A \<inter> (\<phi> ` ball u0 \<rho>) |(u0 :: real^2) \<rho> \<phi> D\<phi> r.
      r \<in> S \<and>
      0 < \<rho> \<and> \<phi> u0 = branch2_base_assoc r \<and>
      (\<forall>u\<in>cball u0 \<rho>.
        branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
        \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
      continuous_on (cball u0 \<rho>) \<phi> \<and>
      branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho> \<and>
      openin (top_of_set Z) (\<phi> ` ball u0 \<rho>)}"
  have S_ne: "S \<noteq> {}"
    using False unfolding S_def by simp
  have A_ne: "A \<noteq> {}"
    using S_ne unfolding A_def by blast
  have A_sub_Z: "A \<subseteq> Z"
  proof
    fix z assume "z \<in> A"
    then obtain r where rS: "r \<in> S" and z: "z = branch2_base_assoc r"
      unfolding A_def by blast
    have "branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s
        (branch2_base_assoc r) = (0, 0)"
      using rS unfolding S_def
      using branch2_chart2_repaired_reduced_base_system_assoc_iff[of r \<omega>0 \<omega>s \<Gamma> j]
      by blast
    thus "z \<in> Z"
      unfolding Z_def z by simp
  qed
  have openF: "\<And>U. U \<in> \<F> \<Longrightarrow> openin (top_of_set A) U"
  proof -
    fix U assume "U \<in> \<F>"
    then obtain u0 :: "real^2"
      and \<rho> :: real
      and \<phi> :: "real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))" where
      U_def: "U = A \<inter> \<phi> ` ball u0 \<rho>"
      and openU: "openin (top_of_set Z) (\<phi> ` ball u0 \<rho>)"
      unfolding \<F>_def mem_Collect_eq by (elim exE conjE) metis
    have "openin (top_of_set A) (A \<inter> (\<phi> ` ball u0 \<rho>))"
      using openU A_sub_Z
      by (simp only: inf.absorb_iff2 openin_subtopology_Int2, 
          metis openin_subtopology_Int2 subtopology_subtopology)
    thus "openin (top_of_set A) U"
      unfolding U_def .
  qed
  have coverF: "A \<subseteq> \<Union>\<F>"
  proof
    fix z assume zA: "z \<in> A"
    then obtain r where rS: "r \<in> S" and z: "z = branch2_base_assoc r"
      unfolding A_def by blast
    have rin: "r \<in> branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j"
      using rS unfolding S_def .
    obtain u0 :: "real^2"
      and \<rho> :: real
      and \<phi> :: "real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))"
      and D\<phi> :: "real^2 \<Rightarrow> (real^2, ((real^2) \<times> ((real^'n) \<times> real))) blinfun" where
      rho: "0 < \<rho>" and phi0: "\<phi> u0 = branch2_base_assoc r"
      and der: "\<forall>u\<in>cball u0 \<rho>.
          branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
          \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)"
      and cont: "continuous_on (cball u0 \<rho>) \<phi>"
      and image: "branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho>"
      and open_set: "openin (top_of_set Z) (\<phi> ` ball u0 \<rho>)"
      using branch2_chart2_repaired_reduced_base_C1_regular_rank_cball_chart
        [OF c1 rin]
      unfolding Z_def by (elim exE conjE) metis
    have Uin: "A \<inter> \<phi> ` ball u0 \<rho> \<in> \<F>"
      unfolding \<F>_def mem_Collect_eq
      by (rule exI[of _ u0], rule exI[of _ \<rho>], rule exI[of _ \<phi>],
          rule exI[of _ D\<phi>], rule exI[of _ r], intro conjI,
          rule refl, rule rS, rule rho, rule phi0, rule der, rule cont,
          rule image, rule open_set)
    have "z \<in> A \<inter> \<phi> ` ball u0 \<rho>"
      using zA z image by blast
    thus "z \<in> \<Union>\<F>"
      using Uin by blast
  qed
  obtain fs where fs_sub: "fs \<subseteq> \<F>" and fs_cnt: "countable fs" and fs_cover: "A \<subseteq> \<Union>fs"
    by (rule countable_subcover_of_openin_cover[OF openF coverF])
  have fs_ne: "fs \<noteq> {}"
    using A_ne fs_cover by blast
  define U where "U = from_nat_into fs"
  have UinF: "U i \<in> \<F>" for i
    using from_nat_into[OF fs_ne, of i] fs_sub unfolding U_def by blast
  have Urange: "fs \<subseteq> range U"
    unfolding U_def
    by (metis fs_cnt subset_range_from_nat_into top1_countable_nonempty_eq_image_nat uncountable_def) 
  have witness_ex: "\<forall>i.
      \<exists>u0 :: real^2. \<exists>\<rho> :: real.
      \<exists>\<phi> :: real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
      \<exists>D\<phi> :: real^2 \<Rightarrow> (real^2, ((real^2) \<times> ((real^'n) \<times> real))) blinfun.
      \<exists>r :: ((real^2) \<times> (real^'n)) \<times> real.
      r \<in> S \<and>
      0 < \<rho> \<and> \<phi> u0 = branch2_base_assoc r \<and>
      (\<forall>u\<in>cball u0 \<rho>.
        branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
        \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
      continuous_on (cball u0 \<rho>) \<phi> \<and>
      branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho> \<and>
      openin (top_of_set Z) (\<phi> ` ball u0 \<rho>) \<and>
      U i = A \<inter> \<phi> ` ball u0 \<rho>"
  proof
    fix i
    show "\<exists>u0 :: real^2. \<exists>\<rho> :: real.
      \<exists>\<phi> :: real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real)).
      \<exists>D\<phi> :: real^2 \<Rightarrow> (real^2, ((real^2) \<times> ((real^'n) \<times> real))) blinfun.
      \<exists>r :: ((real^2) \<times> (real^'n)) \<times> real.
      r \<in> S \<and>
      0 < \<rho> \<and> \<phi> u0 = branch2_base_assoc r \<and>
      (\<forall>u\<in>cball u0 \<rho>.
        branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> u) = (0, 0)
        \<and> (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
      continuous_on (cball u0 \<rho>) \<phi> \<and>
      branch2_base_assoc r \<in> \<phi> ` ball u0 \<rho> \<and>
      openin (top_of_set Z) (\<phi> ` ball u0 \<rho>) \<and>
      U i = A \<inter> \<phi> ` ball u0 \<rho>"
      using UinF[of i] unfolding \<F>_def mem_Collect_eq
      by (elim exE conjE) (intro exI conjI; assumption)
  qed
  then obtain u0 :: "nat \<Rightarrow> real^2"
    and \<rho> :: "nat \<Rightarrow> real"
    and \<phi> :: "nat \<Rightarrow> real^2 \<Rightarrow> ((real^2) \<times> ((real^'n) \<times> real))"
    and D\<phi> :: "nat \<Rightarrow> real^2 \<Rightarrow> (real^2, ((real^2) \<times> ((real^'n) \<times> real))) blinfun"
    and r :: "nat \<Rightarrow> ((real^2) \<times> (real^'n)) \<times> real" where wit:
    "\<And>i. r i \<in> S \<and>
      0 < \<rho> i \<and> \<phi> i (u0 i) = branch2_base_assoc (r i) \<and>
      (\<forall>u\<in>cball (u0 i) (\<rho> i).
        branch2_chart2_repaired_reduced_base_IFT_residual \<omega>0 \<omega>s (\<phi> i u) = (0, 0)
        \<and> (\<phi> i has_derivative blinfun_apply (D\<phi> i u)) (at u)) \<and>
      continuous_on (cball (u0 i) (\<rho> i)) (\<phi> i) \<and>
      branch2_base_assoc (r i) \<in> \<phi> i ` ball (u0 i) (\<rho> i) \<and>
      openin (top_of_set Z) (\<phi> i ` ball (u0 i) (\<rho> i)) \<and>
      U i = A \<inter> \<phi> i ` ball (u0 i) (\<rho> i)"
    by metis
  define i_of where "i_of n = fst (prod_decode n)" for n
  define k_of where "k_of n = snd (prod_decode n)" for n
  define C where "C n =
    (cball (u0 (i_of n)) (\<rho> (i_of n)) \<inter>
      {s. 1 / real (Suc (k_of n)) \<le>
        cvec_dip \<omega>0 \<omega>s (fst (\<phi> (i_of n) s)) \<bullet>
        cvec_dip \<omega>0 \<omega>s (fst (\<phi> (i_of n) s))})" for n
  define psi where "psi n s = branch2_base_unassoc (\<phi> (i_of n) s)" for n s
  have coverC: "S \<subseteq> (\<Union>n. psi n ` C n)"
  proof
    fix x assume xS: "x \<in> S"
    have zA: "branch2_base_assoc x \<in> A"
      using xS unfolding A_def by blast
    then obtain Ob where Ofs: "Ob \<in> fs" and zO: "branch2_base_assoc x \<in> Ob"
      using fs_cover by blast
    obtain i where Oeq: "Ob = U i"
      using Urange Ofs by blast
    have zUi: "branch2_base_assoc x \<in> U i"
      using zO Oeq by simp
    then obtain s where sball: "s \<in> ball (u0 i) (\<rho> i)"
      and phis: "\<phi> i s = branch2_base_assoc x"
      using wit[of i]
      by auto 
    have xbounded: "branch2_base_param_bounded_det \<omega>0 \<omega>s x j"
      using xS unfolding S_def branch2_chart2_repaired_reduced_base_system_def by blast
    have thresh: "1 / real (Suc j) \<le>
        cvec_dip \<omega>0 \<omega>s (fst (\<phi> i s)) \<bullet> cvec_dip \<omega>0 \<omega>s (fst (\<phi> i s))"
      using xbounded phis
      unfolding branch2_base_param_bounded_det_def branch2_base_assoc_def
        branch2_base_param_omega_def
      by (metis branch2_base_param_bounded_def branch2_base_param_omega_def fst_conv)
      
    define n where "n = prod_encode (i, j)"
    have i_n: "i_of n = i"
      unfolding i_of_def n_def by simp
    have k_n: "k_of n = j"
      unfolding k_of_def n_def by simp
    have sC: "s \<in> C n"
      using sball thresh unfolding C_def i_n k_n by auto
    have "x = psi n s"
      using phis unfolding psi_def i_n by simp
    thus "x \<in> (\<Union>n. psi n ` C n)"
      using sC by blast
  qed
  have compactC: "compact (C n)" for n
    unfolding C_def
    by (rule compact_cball_cvec_threshold_of_continuous_chart)
       (use wit in blast)
  have diffC: "branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi n)
      differentiable_on (C n \<times> branch2_u_slice_domain j)" for n
  proof -
    have der: "\<And>s. s \<in> C n \<Longrightarrow> \<phi> (i_of n) differentiable (at s)"
      unfolding C_def differentiable_def
      using wit[of "i_of n"] by blast
    have cnz: "\<And>s. s \<in> C n \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s (fst (\<phi> (i_of n) s)) \<bullet>
      cvec_dip \<omega>0 \<omega>s (fst (\<phi> (i_of n) s)) \<noteq> 0"
      unfolding C_def by auto
    show ?thesis
      unfolding psi_def
      by (rule branch2_lifted_base_chart_x_map_differentiable_on_cvec_nonzero
          [OF der cnz])
  qed
  show ?thesis
    unfolding branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations_def
  proof (intro exI[where x = C] exI[where x = psi] conjI)
    show "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. psi i ` C i)"
      using coverC unfolding S_def .
    show "\<forall>i. compact (C i)"
      by (rule allI, rule compactC)
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      by (rule allI, rule diffC)
  qed
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_compact_chart_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and chart1: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> (real^2) set.
        \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
          branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>i. psi i ` C i)
          \<and> (\<forall>i. compact (C i))
          \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                differentiable_on (C i \<times> branch2_u_slice_domain j))"
    and chart2: "\<And>\<Gamma> j. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
        \<exists>C :: nat \<Rightarrow> (real^2) set.
        \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
          branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
            \<subseteq> (\<Union>i. psi i ` C i)
          \<and> (\<forall>i. compact (C i))
          \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
                differentiable_on (C i \<times> branch2_u_slice_domain j))"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_base_chart_parametrizations
    [OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)"
    where base_cover:
        "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)"
      and compactC: "\<forall>i. compact (C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
    using chart1[OF Gsub Gindep] by meson
  show "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j)))"
  proof (intro exI[where x = C] exI[where x = psi] conjI)
    show "branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. psi i ` C i)"
      using base_cover .
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff .
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using compactC diff
      by (intro allI closed_branch2_lifted_base_chart_image_of_differentiable) auto
  qed
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  obtain C :: "nat \<Rightarrow> (real^2) set"
    and psi :: "nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real)"
    where base_cover:
        "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)"
      and compactC: "\<forall>i. compact (C i)"
      and diff: "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
          differentiable_on (C i \<times> branch2_u_slice_domain j)"
    using chart2[OF Gsub Gindep] by meson
  show "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))
        \<and> (\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              ` (C i \<times> branch2_u_slice_domain j)))"
  proof (intro exI[where x = C] exI[where x = psi] conjI)
    show "branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
        \<subseteq> (\<Union>i. psi i ` C i)"
      using base_cover .
    show "\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        differentiable_on (C i \<times> branch2_u_slice_domain j)"
      using diff .
    show "\<forall>i. closed (branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
        ` (C i \<times> branch2_u_slice_domain j))"
      using compactC diff
      by (intro allI closed_branch2_lifted_base_chart_image_of_differentiable) auto
  qed
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_compact_IFT_parametrizations:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and ift: "branch2_repaired_reduced_base_compact_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
proof (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_base_compact_chart_parametrizations
    [OF card4 pf])
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart1_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. compact (C i))
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))"
    using ift Gsub Gindep
    unfolding branch2_repaired_reduced_base_compact_IFT_parametrizations_all_def
      branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations_def
    by blast
next
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  show "\<exists>C :: nat \<Rightarrow> (real^2) set.
      \<exists>psi :: nat \<Rightarrow> real^2 \<Rightarrow> (((real^2) \<times> (real^'n)) \<times> real).
        branch2_chart2_repaired_reduced_base_system \<omega>0 \<omega>s \<Gamma> j
          \<subseteq> (\<Union>i. psi i ` C i)
        \<and> (\<forall>i. compact (C i))
        \<and> (\<forall>i. branch2_lifted_base_chart_x_map \<omega>0 \<omega>s (psi i)
              differentiable_on (C i \<times> branch2_u_slice_domain j))"
    using ift Gsub Gindep
    unfolding branch2_repaired_reduced_base_compact_IFT_parametrizations_all_def
      branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations_def
    by blast
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_regular_rank_and_compact_IFT_chart_theorem:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and regular_rank: "branch2_repaired_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
    and rank_to_compact_ift:
      "branch2_repaired_reduced_base_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s \<Longrightarrow>
        branch2_repaired_reduced_base_compact_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  by (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_base_compact_IFT_parametrizations
    [OF card4 pf], rule rank_to_compact_ift[OF regular_rank])


theorem branch2_repaired_reduced_base_compact_IFT_parametrizations_all_of_C1_regular_rank:
  fixes V :: "((real^2)^'n::finite) set"
  assumes c1: "branch2_repaired_reduced_base_C1_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branch2_repaired_reduced_base_compact_IFT_parametrizations_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding branch2_repaired_reduced_base_compact_IFT_parametrizations_all_def
proof (intro allI impI)
  fix \<Gamma> :: "(real^2) set" and j :: nat
  assume Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
  have c1_chart1: "branch2_chart1_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
    using c1 Gsub Gindep
    unfolding branch2_repaired_reduced_base_C1_regular_rank_all_def
    by blast
  have c1_chart2: "branch2_chart2_repaired_reduced_base_C1_regular_rank V \<omega>0 \<omega>s \<Gamma> j"
    using c1 Gsub Gindep
    unfolding branch2_repaired_reduced_base_C1_regular_rank_all_def
    by blast
  show "branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j
      \<and> branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations V \<omega>0 \<omega>s \<Gamma> j"
    by (intro conjI
        branch2_chart1_repaired_reduced_base_compact_IFT_parametrizations_of_C1_regular_rank
        branch2_chart2_repaired_reduced_base_compact_IFT_parametrizations_of_C1_regular_rank
        c1_chart1 c1_chart2)
qed

theorem branchP_indep_closed_cover_core_all_of_repaired_reduced_base_C1_regular_rank_and_compact_IFT_chart_theorem:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and c1_regular_rank: "branch2_repaired_reduced_base_C1_regular_rank_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  by (rule branchP_indep_closed_cover_core_all_of_repaired_reduced_base_compact_IFT_parametrizations
    [OF card4 pf],
    rule branch2_repaired_reduced_base_compact_IFT_parametrizations_all_of_C1_regular_rank
      [OF c1_regular_rank])


end
