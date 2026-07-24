theory Scratch_ActualD3Core
  imports "Applied_Math_M5_ActualD3Xi.Scratch_ActualD3Xi"
begin

section \<open>An arc core for the actual retained D3 set\<close>

text \<open>
  The old predicate \<open>d3_detHess_arc_chart_core\<close> asks its charts to cover
  \<open>D3BadXG_H0core\<close>.  That superset deliberately omits the retained
  conditions \<open>A_cart \<noteq> 0\<close> and \<open>det Dcvec_dip \<noteq> 0\<close>.  The null
  antipodal counterexample shows that this enlargement is too coarse for an
  angle-countability argument.  The predicate below has exactly the same
  chart data, but its coverage obligation is the actual set
  \<open>D3BadXG\<close>.
\<close>

definition d3_actual_arc_chart_core ::
    "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2
      \<Rightarrow> (real^2) set \<Rightarrow> bool"
  where
  "d3_actual_arc_chart_core V \<omega>0 \<omega>s \<gamma> \<longleftrightarrow>
    (\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       (V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative
            (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` Crit i)))"

lemma d3_actual_arc_chart_core_of_H0core:
  fixes V :: "((real^2)^'n::finite) set"
  assumes core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  shows "d3_actual_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof -
  have sub:
      "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma>"
    using D3BadXG_subset_H0core by blast
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover:
      "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma>
          :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative
          (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        \<not> surj (blinfun_apply (D i x))"
      and closed: "\<forall>i. closed ((fst \<circ> charts i) ` Crit i)"
    using core unfolding d3_detHess_arc_chart_core_def by blast
  have actual_cover:
      "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
    using sub cover by blast
  show ?thesis
    unfolding d3_actual_arc_chart_core_def
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D]
        conjI actual_cover der rank closed)
qed

lemma d3_actual_arc_projection_meager:
  fixes V :: "((real^2)^'n::finite) set"
  assumes core: "d3_actual_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  shows "meager
      (V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n::finite) set)"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover:
      "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative
          (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        \<not> surj (blinfun_apply (D i x))"
      and closed: "\<forall>i. closed ((fst \<circ> charts i) ` Crit i)"
    using core unfolding d3_actual_arc_chart_core_def by blast
  define K where "K = (\<lambda>i. (fst \<circ> charts i) ` Crit i)"
  have Kcover:
      "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. K i)"
    using cover unfolding K_def by simp
  have Kclosed: "closed (K i)" for i
    using closed unfolding K_def by blast
  have Kneg: "negligible (K i)" for i
    unfolding K_def
    by (rule negligible_singular_image_2n[
          where f="fst \<circ> charts i" and S="Crit i"
            and f'="\<lambda>x. blinfun_apply (D i x)"])
       (use der rank in blast)+
  show ?thesis
    by (rule meager_negligible_closed_cover[OF Kcover])
       (use Kclosed Kneg in blast)+
qed

lemma d3_actual_arc_chart_core_of_countable_fixed_omega_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and om :: "nat \<Rightarrow> real^2"
  assumes cover:
      "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n::finite) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG \<omega>0 \<omega>s {om i})"
    and core: "\<And>i. d3_actual_arc_chart_core V \<omega>0 \<omega>s {om i}"
  shows "d3_actual_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof -
  define S where
    "S = (\<lambda>i. V \<inter> D3BadXG \<omega>0 \<omega>s {om i}
      :: ((real^2)^'n) set)"
  have data: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative
            (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
  proof -
    fix i
    obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<times> (real^2))"
        and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
        and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      where cov:
        "(V \<inter> D3BadXG \<omega>0 \<omega>s {om i} :: ((real^2)^'n) set)
          \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)"
        and der: "\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative
            (blinfun_apply (D j x))) (at x within Crit j)"
        and rank: "\<forall>j x. x \<in> Crit j \<longrightarrow>
          \<not> surj (blinfun_apply (D j x))"
        and closed: "\<forall>j. closed ((fst \<circ> charts j) ` Crit j)"
      using core[of i]
      unfolding d3_actual_arc_chart_core_def by blast
    show "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative
            (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
      unfolding S_def
      by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D]
          conjI cov der rank closed)
  qed
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where all_data:
      "(\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative
            (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
  proof -
    have ex_data:
      "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       (\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative
            (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
      by (rule chart_core_data_countable_UN[OF data])
    then show ?thesis
    proof (elim exE)
      fix charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<times> (real^2))"
        and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
        and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      assume all_data:
        "(\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)
       \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative
              (blinfun_apply (D j x))) (at x within Crit j))
       \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
            \<not> surj (blinfun_apply (D j x)))
       \<and> (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
      show ?thesis by (rule that[OF all_data])
    qed
  qed
  from all_data have union_cover:
      "(\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)"
    by blast
  from all_data have der: "\<forall>j x. x \<in> Crit j \<longrightarrow>
      ((fst \<circ> charts j) has_derivative
        (blinfun_apply (D j x))) (at x within Crit j)"
    by blast
  from all_data have rank: "\<forall>j x. x \<in> Crit j \<longrightarrow>
      \<not> surj (blinfun_apply (D j x))"
    by blast
  from all_data have closed:
      "\<forall>j. closed ((fst \<circ> charts j) ` Crit j)"
    by blast
  have actual_cover:
      "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)"
    using cover union_cover unfolding S_def by blast
  show ?thesis
    unfolding d3_actual_arc_chart_core_def
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D]
        conjI actual_cover der rank closed)
qed

definition D3ActualArc_bad_angles ::
    "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2
      \<Rightarrow> (real^2) set \<Rightarrow> (real^2) set"
  where
  "D3ActualArc_bad_angles V \<omega>0 \<omega>s \<gamma> =
    {\<omega> \<in> \<gamma>. \<exists>x\<in>V. x \<in> D3BadXG \<omega>0 \<omega>s {\<omega>}}"

lemma D3ActualArc_fixed_omega_cover_of_bad_angle_range_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and om :: "nat \<Rightarrow> real^2"
  assumes bad_cover:
      "D3ActualArc_bad_angles V \<omega>0 \<omega>s \<gamma> \<subseteq> range om"
  shows "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n::finite) set)
      \<subseteq> (\<Union>i. V \<inter> D3BadXG \<omega>0 \<omega>s {om i})"
proof
  fix x
  assume xbad:
      "x \<in> (V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma>
        :: ((real^2)^'n) set)"
  have xV: "x \<in> V" using xbad by simp
  obtain \<omega> where wgamma: "\<omega> \<in> \<gamma>"
      and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and h0: "det (HessU
        (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and detnz:
        "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
      and nsurjM:
        "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      and nsurjG: "\<not> (\<exists>Dx.
        ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
          has_derivative Dx) (at x) \<and> surj Dx)"
    using xbad unfolding D3BadXG_def by blast
  have xsingle: "x \<in> D3BadXG \<omega>0 \<omega>s {\<omega>}"
    unfolding D3BadXG_def
    using gz h0 anz detnz cnz nsurjM nsurjG by blast
  have wbad: "\<omega> \<in> D3ActualArc_bad_angles V \<omega>0 \<omega>s \<gamma>"
    unfolding D3ActualArc_bad_angles_def
    using wgamma xV xsingle by blast
  obtain i where weq: "\<omega> = om i"
    using bad_cover wbad by blast
  have "x \<in> V \<inter> D3BadXG \<omega>0 \<omega>s {om i}"
    using xV xsingle weq by simp
  then show "x \<in> (\<Union>i. V \<inter> D3BadXG \<omega>0 \<omega>s {om i})"
    by blast
qed

lemma d3_actual_arc_chart_core_of_no_bad_angles:
  fixes V :: "((real^2)^'n::finite) set"
  assumes empty: "D3ActualArc_bad_angles V \<omega>0 \<omega>s \<gamma> = {}"
  shows "d3_actual_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof -
  have fibre:
      "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n::finite) set)
        = {}"
  proof
    show "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma>
        :: ((real^2)^'n) set) \<subseteq> {}"
    proof
      fix x
      assume xbad:
          "x \<in> (V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma>
            :: ((real^2)^'n) set)"
      have xV: "x \<in> V" using xbad by simp
      obtain \<omega> where wgamma: "\<omega> \<in> \<gamma>"
          and gz:
            "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
          and h0: "det (HessU
            (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
          and anz:
            "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
          and detnz:
            "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
          and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
          and nsurjM:
            "\<not> surj
              (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
          and nsurjG: "\<not> (\<exists>Dx.
            ((\<lambda>y. gradU
                (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
              has_derivative Dx) (at x) \<and> surj Dx)"
        using xbad unfolding D3BadXG_def by blast
      have xsingle: "x \<in> D3BadXG \<omega>0 \<omega>s {\<omega>}"
        unfolding D3BadXG_def
        using gz h0 anz detnz cnz nsurjM nsurjG by blast
      have wbad:
          "\<omega> \<in> D3ActualArc_bad_angles V \<omega>0 \<omega>s \<gamma>"
        unfolding D3ActualArc_bad_angles_def
        using wgamma xV xsingle by blast
      show "x \<in> ({} :: ((real^2)^'n) set)"
        using empty wbad by simp
    qed
    show "({} :: ((real^2)^'n) set)
        \<subseteq> V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma>"
      by simp
  qed
  show ?thesis
    unfolding d3_actual_arc_chart_core_def fibre
    using chart_core_data_empty by simp
qed

theorem d3_actual_arc_chart_core_of_countable_robust4_bad_angle_set:
  fixes V :: "((real^2)^'n::finite) set"
  assumes countable_bad:
      "Top1_Ch3.countable
        (D3ActualArc_bad_angles V
          (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>)"
    and w1lo: "\<And>\<omega>. \<omega> \<in> D3ActualArc_bad_angles V
        (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
      \<Longrightarrow> 0 < vec_nth \<omega> 1"
    and w1hi: "\<And>\<omega>. \<omega> \<in> D3ActualArc_bad_angles V
        (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
      \<Longrightarrow> vec_nth \<omega> 1 < pi"
    and card2: "2 \<le> CARD('n)"
  shows "d3_actual_arc_chart_core V
      (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>"
proof (cases "D3ActualArc_bad_angles V
    (vector [pi / 2, 0]) (vector [0, 0]) \<gamma> = {}")
  case True
  show ?thesis
    by (rule d3_actual_arc_chart_core_of_no_bad_angles[OF True])
next
  case False
  define om where
    "om = from_nat_into
      (D3ActualArc_bad_angles V
        (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>)"
  have bad_cover:
      "D3ActualArc_bad_angles V
          (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
        \<subseteq> range om"
    unfolding om_def
    by (rule subset_range_from_nat_into,
        meson Countable_Set.countable_def Top1_Ch3.countable_def
          countable_bad)
  have om_bad:
      "om i \<in> D3ActualArc_bad_angles V
        (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>" for i
    unfolding om_def by (rule from_nat_into[OF False])
  show ?thesis
  proof (rule d3_actual_arc_chart_core_of_countable_fixed_omega_cover[
      where om=om])
    show "(V \<inter> D3BadXG
          (vector [pi / 2, 0]) (vector [0, 0]) \<gamma>
          :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG
          (vector [pi / 2, 0]) (vector [0, 0]) {om i})"
      by (rule D3ActualArc_fixed_omega_cover_of_bad_angle_range_cover[
          OF bad_cover])
    fix i
    have h0:
        "d3_detHess_arc_chart_core V
          (vector [pi / 2, 0]) (vector [0, 0]) {om i}"
      by (simp add: card2
          fixed_omega_H0core_chart_core_robust4_all_angles
          w1lo[OF om_bad] w1hi[OF om_bad])
    show "d3_actual_arc_chart_core V
        (vector [pi / 2, 0]) (vector [0, 0]) {om i}"
      by (rule d3_actual_arc_chart_core_of_H0core[OF h0])
  qed
qed

lemma robust4_horizontal_actual_arc_core_of_countable_bad_angles:
  fixes V :: "((real^2)^'n::finite) set"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and countable_bad:
      "Top1_Ch3.countable
        (D3ActualArc_bad_angles V
          (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc y))"
    and card2: "2 \<le> CARD('n)"
  shows "d3_actual_arc_chart_core V
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)"
proof (rule d3_actual_arc_chart_core_of_countable_robust4_bad_angle_set[
    OF countable_bad])
  fix \<omega>
  assume bad: "\<omega> \<in> D3ActualArc_bad_angles V
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)"
  have wA: "\<omega> \<in> robust4_horizontal_arc y"
    using bad unfolding D3ActualArc_bad_angles_def by simp
  show "0 < vec_nth \<omega> 1"
    by (rule robust4_horizontal_arc_first_strip(1)[OF wA y3])
next
  fix \<omega>
  assume bad: "\<omega> \<in> D3ActualArc_bad_angles V
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)"
  have wA: "\<omega> \<in> robust4_horizontal_arc y"
    using bad unfolding D3ActualArc_bad_angles_def by simp
  show "vec_nth \<omega> 1 < pi"
    by (rule robust4_horizontal_arc_first_strip(2)[OF wA y3])
next
  show "2 \<le> CARD('n)" by (rule card2)
qed

section \<open>The actual three-arc D3 theorem on the repaired core\<close>

theorem m5_D34_D3_collinear_robust4_of_three_actual_arc_cores:
  fixes V :: "((real^2)^'n::finite) set"
  assumes core_neg:
      "d3_actual_arc_chart_core V
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc (-pi))"
    and core_zero:
      "d3_actual_arc_chart_core V
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc 0)"
    and core_pos:
      "d3_actual_arc_chart_core V
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc pi)"
  shows "meager {x \<in> V.
      \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
        gradU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega> = 0
      \<and> det (HessU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega>) = 0
      \<and> A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega> \<noteq> 0
      \<and> det (matrix
          (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0
      \<and> cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>y. gradU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip y \<omega>) has_derivative Dx) (at x)
          \<and> surj Dx)
      \<and> phase_collinear
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
proof -
  let ?w0 = "vector [pi / 2, 0] :: real^2"
  let ?ws = "vector [0, 0] :: real^2"
  let ?box = "OmegaPF ?w0 (pi / 4)"
  let ?neg = "robust4_horizontal_arc (-pi)"
  let ?zero = "robust4_horizontal_arc 0"
  let ?pos = "robust4_horizontal_arc pi"
  let ?L = "{\<omega> \<in> ?box. phase_collinear ?w0 ?ws \<omega>}"
  let ?S = "{x \<in> V.
      \<exists>\<omega>\<in>?box.
        gradU (cvec_dip ?w0 ?ws) gain_dip x \<omega> = 0
      \<and> det (HessU (cvec_dip ?w0 ?ws) gain_dip x \<omega>) = 0
      \<and> A_cart (cvec_dip ?w0 ?ws) x \<omega> \<noteq> 0
      \<and> det (matrix (Dcvec_dip ?w0 ?ws \<omega>)) \<noteq> 0
      \<and> cvec_dip ?w0 ?ws \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip ?w0 ?ws \<omega>))
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>y. gradU (cvec_dip ?w0 ?ws) gain_dip y \<omega>)
            has_derivative Dx) (at x) \<and> surj Dx)
      \<and> phase_collinear ?w0 ?ws \<omega>}"
  have eqS:
      "?S = (V \<inter> D3BadXG ?w0 ?ws ?L :: ((real^2)^'n) set)"
    unfolding D3BadXG_def by blast
  have mneg:
      "meager (V \<inter> D3BadXG ?w0 ?ws ?neg :: ((real^2)^'n) set)"
    by (rule d3_actual_arc_projection_meager[OF core_neg])
  have mzero:
      "meager (V \<inter> D3BadXG ?w0 ?ws ?zero :: ((real^2)^'n) set)"
    by (rule d3_actual_arc_projection_meager[OF core_zero])
  have mpos:
      "meager (V \<inter> D3BadXG ?w0 ?ws ?pos :: ((real^2)^'n) set)"
    by (rule d3_actual_arc_projection_meager[OF core_pos])
  have meager_union:
      "meager ((V \<inter> D3BadXG ?w0 ?ws ?neg)
        \<union> (V \<inter> D3BadXG ?w0 ?ws ?zero)
        \<union> (V \<inter> D3BadXG ?w0 ?ws ?pos)
        :: ((real^2)^'n) set)"
    by (rule meager_Un[OF meager_Un[OF mneg mzero] mpos])
  have cover:
      "(V \<inter> D3BadXG ?w0 ?ws ?L :: ((real^2)^'n) set)
        \<subseteq> (V \<inter> D3BadXG ?w0 ?ws ?neg)
          \<union> (V \<inter> D3BadXG ?w0 ?ws ?zero)
          \<union> (V \<inter> D3BadXG ?w0 ?ws ?pos)"
    unfolding robust4_phase_collinear_locus_exact D3BadXG_def by blast
  have "meager ?S"
    unfolding eqS by (rule meager_subset[OF cover meager_union])
  then show ?thesis .
qed

theorem m5_D34_D3_collinear_robust4_of_three_actual_bad_angle_sets:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and count_neg:
      "Top1_Ch3.countable
        (D3ActualArc_bad_angles V
          (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc (-pi)))"
    and count_zero:
      "Top1_Ch3.countable
        (D3ActualArc_bad_angles V
          (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc 0))"
    and count_pos:
      "Top1_Ch3.countable
        (D3ActualArc_bad_angles V
          (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc pi))"
  shows "meager {x \<in> V.
      \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
        gradU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega> = 0
      \<and> det (HessU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega>) = 0
      \<and> A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega> \<noteq> 0
      \<and> det (matrix
          (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0
      \<and> cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>y. gradU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip y \<omega>) has_derivative Dx) (at x)
          \<and> surj Dx)
      \<and> phase_collinear
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
proof (rule m5_D34_D3_collinear_robust4_of_three_actual_arc_cores)
  show "d3_actual_arc_chart_core V
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc (-pi))"
    by (rule robust4_horizontal_actual_arc_core_of_countable_bad_angles[
        OF _ count_neg card2]) simp
  show "d3_actual_arc_chart_core V
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc 0)"
    by (rule robust4_horizontal_actual_arc_core_of_countable_bad_angles[
        OF _ count_zero card2]) simp
  show "d3_actual_arc_chart_core V
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc pi)"
    by (rule robust4_horizontal_actual_arc_core_of_countable_bad_angles[
        OF _ count_pos card2]) simp
qed

end
