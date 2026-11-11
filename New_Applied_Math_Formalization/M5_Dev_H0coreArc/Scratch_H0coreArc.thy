theory Scratch_H0coreArc
  imports
    Applied_Math_M5_Wiring.Scratch_Wiring
    Applied_Math_M5_ArcBridge.Scratch_ArcBridge
begin

text \<open>
  Leaf scratch for the HessU=0 residual of D3.

  Build command:

    isabelle build -b -d . \
      -d /home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology \
      -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys \
      -d M5_Dev_Wiring -d M5_Dev_ArcBridge -d M5_Dev_H0coreArc \
      Applied_Math_M5_H0coreArc

  The local construction targeted here is documented in Sketch.md, section
  6h/6j--6m.  The countable fixed-angle wrappers below are still useful,
  but Sketch.md \<section>6m records that the tempting row-reduction from the
  x-derivative of \<open>H_par\<close> to the \<open>T3rad\<close> row of \<open>Jac3_H0cub\<close> is false
  for the honest vanishing cut.
\<close>

lemma H0coreArc_regular_angle_open:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
  obtains U where "open U" "\<omega> \<in> U"
    "\<And>\<eta>. \<eta> \<in> U \<Longrightarrow> cvec_dip \<omega>0 \<omega>s \<eta> \<noteq> 0"
    "\<And>\<eta>. \<eta> \<in> U \<Longrightarrow> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<eta>)) \<noteq> 0"
    "\<And>\<eta>. \<eta> \<in> U \<Longrightarrow> gain_dip \<eta> \<noteq> 0"
proof -
  obtain U0 where open0: "open U0" and \<omega>0U: "\<omega> \<in> U0"
    and gain0: "\<And>\<eta>. \<eta> \<in> U0 \<Longrightarrow> gain_dip \<eta> \<noteq> 0"
    and det0: "\<And>\<eta>. \<eta> \<in> U0 \<Longrightarrow> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<eta>)) \<noteq> 0"
    using e_par_closed_form_rhs_local_eq[OF detnz gnz] by metis
  define U1 where "U1 = {\<eta>. cvec_dip \<omega>0 \<omega>s \<eta> \<noteq> 0}"
  have open1: "open U1"
    unfolding U1_def
    using open_Collect_neq[OF continuous_on_cvec_dip continuous_on_const] by simp
  have \<omega>1U: "\<omega> \<in> U1"
    using cnz unfolding U1_def by simp
  define U where "U = U0 \<inter> U1"
  have openU: "open U"
    unfolding U_def using open0 open1 by auto
  have \<omega>U: "\<omega> \<in> U"
    unfolding U_def using \<omega>0U \<omega>1U by simp
  have cU: "cvec_dip \<omega>0 \<omega>s \<eta> \<noteq> 0" if "\<eta> \<in> U" for \<eta>
    using that unfolding U_def U1_def by simp
  have dU: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<eta>)) \<noteq> 0" if "\<eta> \<in> U" for \<eta>
    using that det0 unfolding U_def by simp
  have gU: "gain_dip \<eta> \<noteq> 0" if "\<eta> \<in> U" for \<eta>
    using that gain0 unfolding U_def by simp
  show ?thesis
    by (rule that[OF openU \<omega>U cU dU gU])
qed

lemma H0coreArc_regular_arc_interval:
  fixes \<phi> :: "real \<Rightarrow> real^2"
  assumes cont: "continuous (at t0) \<phi>"
    and cnz: "cvec_dip \<omega>0 \<omega>s (\<phi> t0) \<noteq> 0"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s (\<phi> t0))) \<noteq> 0"
    and gnz: "gain_dip (\<phi> t0) \<noteq> 0"
  obtains \<epsilon> where "0 < \<epsilon>"
    "\<And>t. dist t t0 < \<epsilon> \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (\<phi> t) \<noteq> 0"
    "\<And>t. dist t t0 < \<epsilon> \<Longrightarrow> det (matrix (Dcvec_dip \<omega>0 \<omega>s (\<phi> t))) \<noteq> 0"
    "\<And>t. dist t t0 < \<epsilon> \<Longrightarrow> gain_dip (\<phi> t) \<noteq> 0"
proof -
  obtain U where openU: "open U" and phiU: "\<phi> t0 \<in> U"
    and cU: "\<And>\<eta>. \<eta> \<in> U \<Longrightarrow> cvec_dip \<omega>0 \<omega>s \<eta> \<noteq> 0"
    and dU: "\<And>\<eta>. \<eta> \<in> U \<Longrightarrow> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<eta>)) \<noteq> 0"
    and gU: "\<And>\<eta>. \<eta> \<in> U \<Longrightarrow> gain_dip \<eta> \<noteq> 0"
    by (rule H0coreArc_regular_angle_open[OF cnz detnz gnz], blast)
  obtain r where rpos: "0 < r" and rball: "ball (\<phi> t0) r \<subseteq> U"
    using openU phiU open_contains_ball by blast
  obtain \<epsilon> where epspos: "0 < \<epsilon>"
    and close: "\<And>t. dist t t0 < \<epsilon> \<Longrightarrow> dist (\<phi> t) (\<phi> t0) < r"
    using cont rpos
    unfolding continuous_at_eps_delta
    using Elementary_Metric_Spaces.continuous_at_eps_delta by blast
  have inU: "\<phi> t \<in> U" if "dist t t0 < \<epsilon>" for t
    using rball close[OF that]
    by (simp add: dist_commute subset_eq) 
  show ?thesis
    by (rule that[OF epspos])
       (use cU dU gU inU in blast)+
qed

theorem H0coreArc_fixed_omega_chart_core_of_regular_angle:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
  by (rule fixed_omega_H0core_chart_core_of_generic_conditions[OF cnz detnz gnz card2])

theorem H0coreArc_fixed_omega_chart_core_on_regular_arc_interval:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> :: "real \<Rightarrow> real^2"
  assumes eps: "0 < \<epsilon>"
    and cnz: "\<And>t. dist t t0 < \<epsilon> \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (\<phi> t) \<noteq> 0"
    and detnz: "\<And>t. dist t t0 < \<epsilon> \<Longrightarrow>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s (\<phi> t))) \<noteq> 0"
    and gnz: "\<And>t. dist t t0 < \<epsilon> \<Longrightarrow> gain_dip (\<phi> t) \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
    and tnear: "dist t t0 < \<epsilon>"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> t}"
  by (rule H0coreArc_fixed_omega_chart_core_of_regular_angle
      [OF cnz[OF tnear] detnz[OF tnear] gnz[OF tnear] card2])

theorem H0coreArc_chart_core_of_countable_regular_fixed_omega_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and om :: "nat \<Rightarrow> real^2"
    and \<gamma> :: "(real^2) set"
  assumes cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
    and cnz: "\<And>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
    and detnz: "\<And>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0"
    and gnz: "\<And>i. gain_dip (om i) \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof (rule d3_chart_core_of_countable_fixed_omega_cover[OF cover])
  fix i
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {om i}"
    by (rule H0coreArc_fixed_omega_chart_core_of_regular_angle
        [OF cnz[of i] detnz[of i] gnz[of i] card2])
qed

theorem H0coreArc_chart_core_all_of_countable_regular_fixed_omega_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and cover: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>om :: nat \<Rightarrow> real^2.
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})
      \<and> (\<forall>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0)
      \<and> (\<forall>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0)
      \<and> (\<forall>i. gain_dip (om i) \<noteq> 0)"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  obtain om :: "nat \<Rightarrow> real^2"
    where cov: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
      and cnz: "\<forall>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
      and detnz: "\<forall>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0"
      and gnz: "\<forall>i. gain_dip (om i) \<noteq> 0"
    using cover[OF arc gsub] by blast
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  proof (rule H0coreArc_chart_core_of_countable_regular_fixed_omega_cover[OF cov])
    show "\<And>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
      using cnz by blast
    show "\<And>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0"
      using detnz by blast
    show "\<And>i. gain_dip (om i) \<noteq> 0"
      using gnz by blast
    show "2 \<le> CARD('n)"
      by (rule card2)
  qed
qed

definition H0coreArc_bad_angles ::
    "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
      (real^2) set \<Rightarrow> (real^2) set"
  where "H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> =
    {\<omega> \<in> \<gamma>. \<exists>x\<in>V. x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}}"

theorem H0coreArc_chart_core_of_no_bad_angles:
  fixes V :: "((real^2)^'n::finite) set"
    and \<gamma> :: "(real^2) set"
  assumes empty: "H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> = {}"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof -
  have core_empty: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) = {}"
  proof
    show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> {}"
    proof
      fix x
      assume xbad: "x \<in> (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
      have xV: "x \<in> V"
        using xbad by simp
      obtain \<omega> where omega_gamma: "\<omega> \<in> \<gamma>"
        and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
        and det0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
        and cnz0: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
        and nsurjM: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
        and nsurjG: "\<not> (\<exists>Dx.
          ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x)
            \<and> surj Dx)"
        using xbad unfolding D3BadXG_H0core_def by blast
      have xsingle: "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}"
        unfolding D3BadXG_H0core_def
        using gz det0 cnz0 nsurjM nsurjG by blast
      have "\<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>"
        unfolding H0coreArc_bad_angles_def
        using omega_gamma xV xsingle by blast
      thus "x \<in> ({} :: ((real^2)^'n) set)"
        using empty by simp
    qed
    show "({} :: ((real^2)^'n) set)
        \<subseteq> (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
      by simp
  qed
  show ?thesis
    unfolding d3_detHess_arc_chart_core_def core_empty
    using chart_core_data_empty by simp
qed

lemma H0coreArc_fixed_omega_cover_of_bad_angle_range_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and om :: "nat \<Rightarrow> real^2"
    and \<gamma> :: "(real^2) set"
  assumes bad_cover: "H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<subseteq> range om"
  shows "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
proof
  fix x
  assume xbad: "x \<in> (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
  have xV: "x \<in> V"
    using xbad by simp
  obtain \<omega> where omega_gamma: "\<omega> \<in> \<gamma>"
    and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and det0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
    and cnz0: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and nsurjM: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    and nsurjG: "\<not> (\<exists>Dx.
      ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x)
        \<and> surj Dx)"
    using xbad unfolding D3BadXG_H0core_def by blast
  have xsingle: "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}"
    unfolding D3BadXG_H0core_def
    using gz det0 cnz0 nsurjM nsurjG by blast
  have "\<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>"
    unfolding H0coreArc_bad_angles_def
    using omega_gamma xV xsingle by blast
  then obtain i where omega_eq: "\<omega> = om i"
    using bad_cover by blast
  have "x \<in> V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i}"
    using xV xsingle omega_eq by simp
  thus "x \<in> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
    by blast
qed

theorem H0coreArc_chart_core_of_countable_regular_bad_angles:
  fixes V :: "((real^2)^'n::finite) set"
    and om :: "nat \<Rightarrow> real^2"
    and \<gamma> :: "(real^2) set"
  assumes bad_cover: "H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<subseteq> range om"
    and cnz: "\<And>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
    and detnz: "\<And>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0"
    and gnz: "\<And>i. gain_dip (om i) \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof (rule H0coreArc_chart_core_of_countable_regular_fixed_omega_cover[where om = om])
  show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
    by (rule H0coreArc_fixed_omega_cover_of_bad_angle_range_cover[OF bad_cover])
  show "\<And>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
    by (rule cnz)
  show "\<And>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0"
    by (rule detnz)
  show "\<And>i. gain_dip (om i) \<noteq> 0"
    by (rule gnz)
  show "2 \<le> CARD('n)"
    by (rule card2)
qed

theorem H0coreArc_chart_core_of_countable_regular_bad_angle_set:
  fixes V :: "((real^2)^'n::finite) set"
    and \<gamma> :: "(real^2) set"
  assumes countable_bad: "countable (H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>)"
    and cnz: "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and detnz: "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and gnz: "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
      gain_dip \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof (cases "H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> = {}")
  case True
  show ?thesis
    by (rule H0coreArc_chart_core_of_no_bad_angles[OF True])
next
  case False
  define om where "om = from_nat_into (H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>)"
  have bad_cover: "H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<subseteq> range om"
    unfolding om_def
    by (rule subset_range_from_nat_into, 
        metis assms(1) top1_countable_nonempty_eq_image_nat uncountable_def)
  have om_bad: "om i \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>" for i
    unfolding om_def
    by (rule from_nat_into[OF False])
  show ?thesis
  proof (rule H0coreArc_chart_core_of_countable_regular_bad_angles
      [where om = om, OF bad_cover])
    show "\<And>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
      by (rule cnz[OF om_bad])
    show "\<And>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0"
      by (rule detnz[OF om_bad])
    show "\<And>i. gain_dip (om i) \<noteq> 0"
      by (rule gnz[OF om_bad])
    show "2 \<le> CARD('n)"
      by (rule card2)
  qed
qed

theorem H0coreArc_chart_core_all_of_countable_regular_bad_angle_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and cover: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>om :: nat \<Rightarrow> real^2.
        H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<subseteq> range om
      \<and> (\<forall>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0)
      \<and> (\<forall>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0)
      \<and> (\<forall>i. gain_dip (om i) \<noteq> 0)"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  obtain om :: "nat \<Rightarrow> real^2"
    where bad_cover: "H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<subseteq> range om"
      and cnz: "\<forall>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
      and detnz: "\<forall>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0"
      and gnz: "\<forall>i. gain_dip (om i) \<noteq> 0"
    using cover[OF arc gsub] by blast
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  proof (rule H0coreArc_chart_core_of_countable_regular_bad_angles
      [where om = om, OF bad_cover])
    show "\<And>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
      using cnz by blast
    show "\<And>i. det (matrix (Dcvec_dip \<omega>0 \<omega>s (om i))) \<noteq> 0"
      using detnz by blast
    show "\<And>i. gain_dip (om i) \<noteq> 0"
      using gnz by blast
    show "2 \<le> CARD('n)"
      by (rule card2)
  qed
qed

theorem H0coreArc_chart_core_all_of_countable_regular_bad_angle_sets:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and countable_bad: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      countable (H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>)"
    and cnz: "\<And>\<gamma> \<omega>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
      cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and detnz: "\<And>\<gamma> \<omega>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
      det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and gnz: "\<And>\<gamma> \<omega>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
      gain_dip \<omega> \<noteq> 0"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  proof (rule H0coreArc_chart_core_of_countable_regular_bad_angle_set)
    show "countable (H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma>)"
      by (rule countable_bad[OF arc gsub])
    show "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
      by (rule cnz[OF arc gsub])
    show "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
        det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      by (rule detnz[OF arc gsub])
    show "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<Longrightarrow>
        gain_dip \<omega> \<noteq> 0"
      by (rule gnz[OF arc gsub])
    show "2 \<le> CARD('n)"
      by (rule card2)
  qed
qed

theorem H0coreArc_chart_core_of_countable_robust4_bad_angles:
  fixes V :: "((real^2)^'n::finite) set"
    and om :: "nat \<Rightarrow> real^2"
    and \<gamma> :: "(real^2) set"
  assumes bad_cover: "H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
      \<subseteq> range om"
    and w1lo: "\<And>i. 0 < vec_nth (om i) 1"
    and w1hi: "\<And>i. vec_nth (om i) 1 < pi"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>"
proof (rule d3_chart_core_of_countable_fixed_omega_cover[where om = om])
  show "(V \<inter> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
      :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {om i})"
    by (rule H0coreArc_fixed_omega_cover_of_bad_angle_range_cover[OF bad_cover])
  show "\<And>i. d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) {om i}"
    by (simp add: card2 fixed_omega_H0core_chart_core_robust4_all_angles w1hi w1lo)    
qed

theorem H0coreArc_chart_core_of_countable_robust4_bad_angle_set:
  fixes V :: "((real^2)^'n::finite) set"
    and \<gamma> :: "(real^2) set"
  assumes countable_bad:
      "countable (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>)"
    and w1lo: "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
      \<Longrightarrow> 0 < vec_nth \<omega> 1"
    and w1hi: "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
      \<Longrightarrow> vec_nth \<omega> 1 < pi"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>"
proof (cases "H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma> = {}")
  case True
  show ?thesis
    by (rule H0coreArc_chart_core_of_no_bad_angles[OF True])
next
  case False
  define om where
    "om = from_nat_into (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>)"
  have bad_cover: "H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
      \<subseteq> range om"
    unfolding om_def
    by (rule subset_range_from_nat_into, 
        meson Countable_Set.countable_def Top1_Ch3.countable_def assms(1))
  have om_bad: "om i \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>"
    for i
    unfolding om_def
    by (rule from_nat_into[OF False])
  show ?thesis
  proof (rule H0coreArc_chart_core_of_countable_robust4_bad_angles
      [where om = om, OF bad_cover])
    show "\<And>i. 0 < vec_nth (om i) 1"
      by (rule w1lo[OF om_bad])
    show "\<And>i. vec_nth (om i) 1 < pi"
      by (rule w1hi[OF om_bad])
    show "2 \<le> CARD('n)"
      by (rule card2)
  qed
qed

lemma H0coreArc_robust4_OmegaPF_w1_strip:
  fixes \<omega> :: "real^2"
  assumes wO: "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
  shows "0 < vec_nth \<omega> 1"
    and "vec_nth \<omega> 1 < pi"
proof -
  have lo: "pi / 2 - pi / 4 \<le> vec_nth \<omega> 1"
    using OmegaPF_component_bounds[OF wO] by (simp only: vector_2)
  have hi: "vec_nth \<omega> 1 \<le> pi / 2 + pi / 4"
    using OmegaPF_component_bounds[OF wO] by (simp only: vector_2)
  show "0 < vec_nth \<omega> 1"
    using lo pi_gt_zero by linarith
  show "vec_nth \<omega> 1 < pi"
    using hi pi_gt_zero by linarith
qed

theorem H0coreArc_chart_core_all_robust4_of_countable_bad_angle_sets:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and countable_bad: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow>
      \<gamma> \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      countable (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>)"
  shows "d3_detHess_arc_chart_core_all V (vector [pi / 2, 0]) (pi / 4)
    (vector [pi / 2, 0]) (vector [0, 0])"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
  show "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>"
  proof (rule H0coreArc_chart_core_of_countable_robust4_bad_angle_set)
    show "countable
        (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>)"
      by (rule countable_bad[OF arc gsub])
    show "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
        \<Longrightarrow> 0 < vec_nth \<omega> 1"
    proof -
      fix \<omega>
      assume wbad: "\<omega> \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>"
      have "\<omega> \<in> \<gamma>"
        using wbad unfolding H0coreArc_bad_angles_def by simp
      hence "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
        using gsub by blast
      thus "0 < vec_nth \<omega> 1"
        by (rule H0coreArc_robust4_OmegaPF_w1_strip(1))
    qed
    show "\<And>\<omega>. \<omega> \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
        \<Longrightarrow> vec_nth \<omega> 1 < pi"
    proof -
      fix \<omega>
      assume wbad: "\<omega> \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>"
      have "\<omega> \<in> \<gamma>"
        using wbad unfolding H0coreArc_bad_angles_def by simp
      hence "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
        using gsub by blast
      thus "vec_nth \<omega> 1 < pi"
        by (rule H0coreArc_robust4_OmegaPF_w1_strip(2))
    qed
    show "2 \<le> CARD('n)"
      by (rule card2)
  qed
qed

definition h0arc_phi_row ::
    "(real \<Rightarrow> real^2) \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
      ((real^2)^'n::finite) \<Rightarrow> real \<Rightarrow> real"
  where "h0arc_phi_row \<phi> \<omega>0 \<omega>s x t = Phi_par x (\<phi> t) \<omega>0 \<omega>s"

definition h0arc_grad2_row ::
    "(real \<Rightarrow> real^2) \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
      ((real^2)^'n::finite) \<Rightarrow> real \<Rightarrow> real"
  where "h0arc_grad2_row \<phi> \<omega>0 \<omega>s x t =
    vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 2"

definition h0arc_hpar_row ::
    "(real \<Rightarrow> real^2) \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow>
      ((real^2)^'n::finite) \<Rightarrow> real \<Rightarrow> real"
  where "h0arc_hpar_row \<phi> \<omega>0 \<omega>s x t = H_par x (\<phi> t) \<omega>0 \<omega>s"

lemma H0coreArc_fibre_rows_zero:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and Hz: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "Phi_par x \<omega> \<omega>0 \<omega>s = 0"
    and "vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2 = 0"
    and "H_par x \<omega> \<omega>0 \<omega>s = 0"
  using Phi_par_zero_of_gradU_zero[OF gz] gz H_par_zero_of_HessU_zero[OF Hz]
  by simp_all

lemma H0coreArc_arc_rows_zero:
  fixes x :: "(real^2)^'n::finite" and \<phi> :: "real \<Rightarrow> real^2"
  assumes gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0"
    and Hz: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0"
  shows "h0arc_phi_row \<phi> \<omega>0 \<omega>s x t = 0"
    and "h0arc_grad2_row \<phi> \<omega>0 \<omega>s x t = 0"
    and "h0arc_hpar_row \<phi> \<omega>0 \<omega>s x t = 0"
  unfolding h0arc_phi_row_def h0arc_grad2_row_def h0arc_hpar_row_def
  using H0coreArc_fibre_rows_zero[OF gz Hz] by simp_all

text \<open>
  Row-reduction status (Sketch.md \<section>6m):

    The once-planned 3-by-3 determinant of the x-derivative rows

      \<open>(h0arc_phi_row, h0arc_grad2_row, h0arc_hpar_row)\<close>

    in the columns

      \<open>slot i c\<close>, \<open>slot j c\<close>, \<open>slot k (perp2 c)\<close>

    does not reduce to \<open>Jac3_H0cub\<close> for raw \<open>H_par\<close>.  After decomposing
    \<open>D2cvec_dip(e_par,e_par)\<close> in the local basis
    \<open>{cvec_dip, Dcvec_dip(axis 2)}\<close> and reducing modulo the first two rows,
    the third row remains in the span of \<open>D_x Wc\<close> and
    \<open>D_x Wc_d2(c,c)\<close>; it cannot manufacture the \<open>r^3 cos r\<close> profile in
    \<open>D_x T3rad\<close>.  Do not use \<open>T3rad\<close> as an IFT cut unless a genuinely
    different vanishing third cut is first proved.
\<close>

end
