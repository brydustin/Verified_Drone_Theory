theory Nonemptiness_Robust4
  imports "Applied_Math_D3_Curve_Cover.D3_Curve_Cover"
begin

text \<open>The D3 branch is now reduced to two explicit obligations: a finite C1-arc
  cover of the phase-collinear steering-angle locus, and the per-arc chart
  bundle for the retained Case-B fibre.  The active x-fibre cover is checked
  set algebra from the angle-locus cover.\<close>

definition D3BadXG_H0core :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "D3BadXG_H0core \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
      \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"

lemma D3BadXG_subset_H0core:
  "(D3BadXG \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s \<Gamma>"
  unfolding D3BadXG_def D3BadXG_H0core_def by blast

definition d3_detHess_arc_chart_core ::
  "((real^2)^'n) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma> \<longleftrightarrow>
    (\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
       (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))))"

definition d3_detHess_arc_chart_core_all ::
  "((real^2)^'n) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
     (\<forall>\<gamma>. analytic_arc \<gamma> \<longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
        d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>)"

lemma d3_detHess_arc_charts_Nn:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>GENUINE D3 analytic core: the det-HessU/NSx retained critical fibre over one
      C1 arc.  This is the H0 part actually needed downstream:
      \<open>gradU=0\<close>, \<open>det HessU=0\<close>, moment rank drop, and failure of the
      configuration derivative.  The stronger retained Case-B fibre @{const D3BadXG}
      is a checked subset of this core.\<close>
  using core unfolding d3_detHess_arc_chart_core_def by blast

lemma d3_retained_arc_charts_Nn:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                    \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using d3_detHess_arc_charts_Nn[OF openV Vne c6 arc gsub pf nd core]
    by (smt (verit, best))
  have sub: "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
              \<subseteq> V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma>"
    using D3BadXG_subset_H0core by blast
  have cover': "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                  \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    using sub cover by blast
  show ?thesis
    by (intro exI[where x = charts] exI[where x = Crit] exI[where x = D] conjI)
       (use cover' der rank clo in blast)+
qed

lemma d3_retained_arc_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
            (V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
          \<and> (\<forall>n. closed (K n))
          \<and> (\<forall>n. negligible (K n))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                    \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using d3_retained_arc_charts_Nn[OF openV Vne c6 arc gsub pf nd core]
    by (smt (verit, best))
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have Kcover: "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    using cover unfolding K_def by simp
  have Kclosed: "closed (K n)" for n
    using clo unfolding K_def by blast
  have Knegligible: "negligible (K n)" for n
    unfolding K_def
    by (rule negligible_singular_image_2n
          [where f = "fst \<circ> charts n" and S = "Crit n"
             and f' = "\<lambda>x. blinfun_apply (D n x)"])
       (use der rank in blast)+
  show ?thesis
    using Kcover Kclosed Knegligible by blast
qed

lemma d3_retained_arc_projection_meager:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  shows "meager (V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "(V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
      and clo: "\<forall>n. closed (K n)"
      and neg: "\<forall>n. negligible (K n)"
    using d3_retained_arc_negligible_closed_cover[OF openV Vne c6 arc gsub pf nd core] by blast
  show ?thesis
    by (rule meager_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

lemma d3_collinear_locus_finite_arc_cover:
  fixes ctr :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
  shows "d3_finitely_arc_coverable
           {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>} ctr \<delta>"
  \<comment> \<open>GENUINE D3 curve-cover obligation, now scoped only to the steering-angle
      phase-collinear locus and carrying the same nonsingular-level-set side
      condition as the C1 curve-cover development.  The x-fibre bookkeeping is
      discharged separately by @{thm d3_active_cover_from_angle_cover}.\<close>
proof -
  have nsing_all: "\<forall>\<omega>\<in>{\<omega> \<in> OmegaPF ctr \<delta>. d3_crossTheta \<omega>0 \<omega>s \<omega> = 0}.
        (- d3_crossA ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) \<omega>s (\<omega>$1) * sin (\<omega>$2)
          + d3_crossB ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) \<omega>s (\<omega>$1) * cos (\<omega>$2) \<noteq> 0)
        \<or> ((((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * kz \<omega>s + ky \<omega>s) * sin (\<omega>$1) * cos (\<omega>$2)
          - (((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * kz \<omega>s + kx \<omega>s) * sin (\<omega>$1) * sin (\<omega>$2)
          + (((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * ky \<omega>s
             - ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * kx \<omega>s) * cos (\<omega>$1) \<noteq> 0)"
    using nsing
    unfolding d3_collinear_nsing_all_def d3_collinear_d2_def d3_collinear_d1_def
    by simp
  show ?thesis
    by (rule collinear_locus_finite_arc_cover[OF d0 pf hsep kdiff nsing_all])
qed

lemma d3_active_collinear_finite_arc_cover:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
  shows "\<exists>(I::nat set) arc. finite I
            \<and> (V \<inter> D3BadXG \<omega>0 \<omega>s {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}
                  :: ((real^2)^'n) set)
                \<subseteq> (\<Union>i\<in>I. (V \<inter> D3BadXG \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))
            \<and> (\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>)"
proof -
  have Lcov: "d3_finitely_arc_coverable
           {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>} ctr \<delta>"
    by (rule d3_collinear_locus_finite_arc_cover[OF d0 pf hsep kdiff nsing])
  show ?thesis
    by (rule d3_active_cover_from_angle_cover[OF Lcov])
qed


subsection \<open>D3 --- the phase-collinear branch (checked assembly from two scoped obligations)\<close>

text \<open>The phase-collinear branch of the residual.  Internally: the 3-equation /
  2-parameter excess engine produces \<open>(2N-1)\<close>-dim IFT graphs whose \<open>x\<close>-projections
  are negligible, unioned over the \<open>\<int>\<^sup>3\<close> phase-period lattice (window-finite by
  @{thm finite_affine_int_zeros}).  No Sard.  Here the meagerness assembly is
  checked from the pure steering-angle cover obligation and the retained
  per-arc chart core, feeding it the abstract @{thm fixed_c_nonsurj_nowhere_dense}
  input.\<close>

lemma m5_D34_D3_collinear:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and d3core: "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
proof -
  let ?L = "{\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}"
  have eq: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}
          = (V \<inter> D3BadXG \<omega>0 \<omega>s ?L :: ((real^2)^'n) set)"
    unfolding D3BadXG_def by blast
  obtain I :: "nat set" and arc :: "nat \<Rightarrow> (real^2) set"
    where finI: "finite I"
      and cover: "(V \<inter> D3BadXG \<omega>0 \<omega>s ?L :: ((real^2)^'n) set)
                    \<subseteq> (\<Union>i\<in>I. (V \<inter> D3BadXG \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
      and arcprops: "\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>"
    using d3_active_collinear_finite_arc_cover[OF d0 pf hsep kdiff nsing, of V] by blast
  have meagU: "meager (\<Union>i\<in>I. (V \<inter> D3BadXG \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  proof (rule meager_Union_finite[OF finI])
    fix i :: nat assume iI: "i \<in> I"
    have ai: "analytic_arc (arc i)" and asub: "arc i \<subseteq> OmegaPF ctr \<delta>"
      using arcprops iI by blast+
    have corei: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (arc i)"
      using d3core ai asub unfolding d3_detHess_arc_chart_core_all_def by blast
    show "meager (V \<inter> D3BadXG \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set)"
      by (rule d3_retained_arc_projection_meager[OF openV Vne c6 ai asub pf nd corei])
  qed
  show ?thesis
    unfolding eq by (rule meager_subset[OF cover meagU])
qed


subsection \<open>D4 --- the Branch-P residual (explicit closed-cover core)\<close>

text \<open>The Branch-P residual: the complementary (non phase-collinear) part.
  Internally: the explicit rank-drop dichotomy (\<open>\<gamma> \<parallel> c\<close> or not) plus the excess
  engine on the \<open>(\<star>n)/Hess.u(w)\<close> rows.  \<open>core_3d\<close> is ruled out structurally (the
  gradU rows degenerate exactly at the residual witnesses), so a dedicated
  stratification is required.  The genuine Branch-P geometric-measure content is
  now exposed as \<open>branchP_indep_closed_cover_core_all\<close>.\<close>


(* ===== D4 Stage-B reduction: D4charts chart-route (BadXGW RETAINS gradU=0 -> sound) =====
   phase_collinear already defined above (~L2358); Sard NOT needed -- negligible_singular_image_2n
   + meager_negligible_closed_cover resolve from the Applied_Math_Nonemptiness heap. The D4
   analytic content is an explicit closed-cover core premise, not a hidden oracle. ===== *)

definition BadXGW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXGW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
      \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
      \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
      \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"


subsection \<open>The rank-drop dichotomy predicate \<open>\<gamma> \<parallel> c\<close> (copied verbatim)\<close>

definition gamma_par_c :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow> phase_collinear \<omega>0 \<omega>s \<omega>"

lemma not_gamma_par_c_iff:
  "\<not> gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<forall>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<noteq> t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<and> (\<forall>t. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"
  unfolding gamma_par_c_def phase_collinear_def by blast


subsection \<open>Structural set algebra for \<open>BadXGW\<close> (proof-complete, copied verbatim)\<close>

lemma BadXGW_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "BadXGW \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXGW \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n) set)"
  using assms unfolding BadXGW_def by blast

lemma BadXGW_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "BadXGW \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)
          = (\<Union>i\<in>I. (BadXGW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  unfolding BadXGW_def by blast

lemma BadXGW_point:
  fixes \<omega> :: "real^2"
  shows "BadXGW \<omega>0 \<omega>s {\<omega>}
          = {x :: (real^2)^'n.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
              \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  unfolding BadXGW_def by blast


subsection \<open>Moment-rank bridge and the explicit Branch-P core\<close>

text \<open>The Branch-P bad set is contained in the pure moment-rank-drop fibre.  This
  bridge is the verified part of the D4 reduction: the retained conjuncts
  \<open>gradU = 0\<close>, \<open>det HessU = 0\<close>, \<open>A \<noteq> 0\<close>, \<open>det Dcvec \<noteq> 0\<close>, and the failed
  configuration derivative only shrink the set.\<close>

definition MomentBad :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "MomentBad \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

lemma BadXGW_subset_MomentBad:
  "(BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> MomentBad \<omega>0 \<omega>s \<Gamma>"
  unfolding BadXGW_def MomentBad_def by blast

lemma MomentBad_eq_mstarg_zeros:
  "(MomentBad \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
     = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
                              \<and> mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0}"
  unfolding MomentBad_def by (simp add: surj_iff_mstarg)

lemma closed_mstarg_zero_slice:
  "closed {x::(real^2)^'n. mstarg c x = 0}"
  by (rule closed_Collect_eq[OF cont_mstarg continuous_on_const])

definition branchP_indep_closed_cover_core ::
  "((real^2)^'n) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma> \<longleftrightarrow>
     (\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
        (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n))
      \<and> (\<forall>n. negligible (K n)))"

definition branchP_indep_closed_cover_core_all ::
  "((real^2)^'n) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s \<longleftrightarrow>
     (\<forall>\<Gamma>. \<Gamma> \<subseteq> OmegaPF ctr \<delta> \<longrightarrow>
        (\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>) \<longrightarrow>
        branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>)"

definition branchP_indep_chart_core ::
  "((real^2)^'n) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "branchP_indep_chart_core V \<omega>0 \<omega>s \<Gamma> \<longleftrightarrow>
    (\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
       (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))))"

text \<open>The literal chart-bundle theorem is no longer asserted from the relaxed
  assumptions alone.  Its real content is the explicit predicate
  @{const branchP_indep_chart_core}; downstream only needs the weaker closed
  negligible cover predicate above.\<close>

lemma branchP_indep_charts_Nn:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and core: "branchP_indep_chart_core V \<omega>0 \<omega>s \<Gamma>"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  using core unfolding branchP_indep_chart_core_def by blast


subsection \<open>The closed negligible cover (from the explicit core)\<close>

text \<open>\<^bold>\<open>The closed negligible cover, assembled proof-complete from the explicit core.\<close>
  This is the form actually consumed downstream.  A literal chart bundle would
  imply it, but the weaker closed-cover core is enough for meagerness and avoids
  claiming a codimension-3 chart theorem from the relaxed \<open>nd\<close> hypothesis.\<close>

lemma branchP_indep_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and core: "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
            (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
          \<and> (\<forall>n. closed (K n))
          \<and> (\<forall>n. negligible (K n))"
  using core unfolding branchP_indep_closed_cover_core_def by blast


subsection \<open>The downstream proof-complete layers (copied verbatim from D4Core)\<close>

text \<open>The two proof-complete layers consumed downstream (copied verbatim from the D4
  core file) confirm the cut is at the right place: the closed negligible cover
  yields meagerness without further geometric-measure work.\<close>

lemma branchP_indep_of_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<Gamma> :: "(real^2) set"
    and K :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])

lemma branchP_indep_core:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and core: "branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
      and clo: "\<forall>n. closed (K n)"
      and neg: "\<forall>n. negligible (K n)"
    using branchP_indep_negligible_closed_cover[OF openV Vne c6 d0 pf Gsub Gindep nd core]
    by blast
  show ?thesis
    by (rule branchP_indep_of_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

lemma m5_D34_D4_branchP:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    and branchcore: "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  \<comment> \<open>Stage-B D4 reduction: the residual = \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> over the
      \<open>\<gamma>\<not>\<parallel>c\<close> region \<open>\<Gamma>\<close>, closed by the grafted D4 chart-route \<open>branchP_indep_core\<close>
      (which bottoms out at the canonical IFT core \<open>branchP_indep_charts_Nn\<close>).\<close>
proof -
  let ?Gam = "{\<omega>\<in>OmegaPF ctr \<delta>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  have eq: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}
          = (V \<inter> BadXGW \<omega>0 \<omega>s ?Gam :: ((real^2)^'n) set)"
    unfolding BadXGW_def by blast
  have Gsub: "?Gam \<subseteq> OmegaPF ctr \<delta>" by blast
  have Gindep: "\<forall>\<omega>\<in>?Gam. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>" by (auto simp: gamma_par_c_def)
  have coreGam: "branchP_indep_closed_cover_core V \<omega>0 \<omega>s ?Gam"
    using branchcore Gsub Gindep
    unfolding branchP_indep_closed_cover_core_all_def by blast
  show ?thesis unfolding eq
    by (rule branchP_indep_core[OF openV Vne c6 d0 pf Gsub Gindep nd coreGam])
qed


subsection \<open>Assembly: \<open>m5_D34_residual\<close> from the reduction + D3 + D4\<close>

text \<open>The exact target statement (verbatim from the M5 skeleton), closed by a
  direct excluded-middle split of the retained Case-B residual on
  @{const phase_collinear} into D3 \<union> D4, the two inner meagerness lemmas, and
  @{thm meager_subset} / @{thm meager_Un}.  proof-complete at this assembly layer.\<close>

lemma m5_D34_residual:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
    and d3core: "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
    and branchcore: "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  \<comment> \<open>The Robust3-supplied fixed-angle nowhere-density input.\<close>
  have nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    by (rule fixed_c_nonsurj_nowhere_dense[OF _ c6])
  \<comment> \<open>The retained D34 residual after D1/D2/D5 have been removed.\<close>
  let ?R = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  let ?D3 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
  let ?D4 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  \<comment> \<open>The residual is the D3/D4 union (excluded middle on \<open>phase_collinear\<close>).\<close>
  have RsubD: "?R \<subseteq> ?D3 \<union> ?D4" by blast
  \<comment> \<open>Each piece is meager from the explicit D3 and D4 core premises.\<close>
  have mD3: "meager ?D3" by (rule m5_D34_D3_collinear[OF openV Vne c6 d0 pf hsep kdiff nsing nd d3core])
  have mD4: "meager ?D4" by (rule m5_D34_D4_branchP[OF openV Vne c6 d0 pf nd branchcore])
  have mR: "meager ?R"
    by (rule meager_subset[OF RsubD meager_Un[OF mD3 mD4]])
  show ?thesis
    by (rule meager_subset[OF _ mR]) blast
qed

(* ---- D1: joint-regular part (subset of heap meager_grad_x_regular_part) ---- *)

lemma m5_D1_regular:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}
        \<subseteq> {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_grad_x_regular_part[OF openV Vne]])
qed

lemma meager_rank_deficient_stratum:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
    and d3core: "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
    and branchcore: "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  \<comment> \<open>(M5) assembled from the four-stratum cover D1 \<union> D2 \<union> D5 \<union> D34 (grafted above).
      D1/D2/D5 are proven proof-complete; D34 rests on the two scoped branch cores
      \<open>m5_D34_D3_collinear\<close> / \<open>m5_D34_D4_branchP\<close>.\<close>
proof -
  let ?D1 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  let ?D2 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  let ?D5 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  let ?D34 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  have meag: "meager (?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34)"
    by (intro meager_Un
          m5_D1_regular[OF openV Vne]
          m5_D2_beamcenter[OF openV Vne c6 d0 pf]
          m5_D5_steersing[OF openV Vne c6 d0 pf hsep kdiff]
          m5_D34_residual[OF openV Vne c6 d0 pf hsep kdiff nsing d3core branchcore])
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
             \<subseteq> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    then obtain \<omega> where xV: "x \<in> V" and wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and a0: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and ns: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      by blast
    show "x \<in> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34"
      using xV wD g0 h0 a0 ns by blast
  qed
  show ?thesis by (rule meager_subset[OF sub meag])
qed

text \<open>\<^bold>\<open>(M6) Steering-singular stratum is meager.\<close>  Degenerate critical points (with \<open>A \<noteq> 0\<close>) at an
  angle where the steering Jacobian is singular.  Meager by (M3): the singular-\<open>\<omega>\<close> locus is
  nowhere dense, and the critical points over it form a positive-codimension set.\<close>

text \<open>\<open>meager_steering_singular_stratum\<close> (M6) is DONE --- proven proof-complete in
  \<open>Nonemptiness_Robust2\<close> (in the heap): kernel-direction reduction +
  gdip-derivative zero classification + finite witness-angle set + fixed-angle
  analytic slices.  Development history: Scratch_m6 / Scratch_g1_r4 /
  Scratch_g2_r5 / Scratch_g3_asm (parallel agent wave).\<close>

text \<open>\<^bold>\<open>(M6b) The \<open>A = 0\<close> degenerate stratum is meager --- ADDED (soundness).\<close>  The bad set in
  M4--M6 carries \<open>A \<noteq> 0\<close> (the transversality argument needs it).  But every array-factor null
  \<open>A_cart = 0\<close> is itself a critical point (\<open>\<nabla>\<^sub>\<Omega>U = g \<nabla>\<bar>A\<bar>\<^sup>2 + \<bar>A\<bar>\<^sup>2 \<nabla>g = 0\<close> at \<open>A = 0\<close>), so a
  \<^emph>\<open>degenerate\<close> null also breaks regularity and must be excluded.  The locus \<open>{A = 0 \<and> det \<nabla>\<^sup>2U = 0}\<close>
  is \<open>3\<close> real conditions on \<open>(\<bm>x,\<omega>)\<close> (codim \<open>3\<close>): its \<open>\<bm>x\<close>-projection is meager.\<close>

text \<open>\<open>meager_Azero_degenerate_stratum\<close> (M6b) is DONE --- proven proof-complete in
  \<open>Nonemptiness_Robust2\<close> (in the heap): the planar engine on \<open>cplx_r2 \<circ> af\<close>
  with global regular value (odd \<open>N\<close>), plus the Hessian-at-null determinant
  identity.  Development history in \<open>Scratch_m6b\<close>.\<close>

text \<open>\<^bold>\<open>(M7) The dipole-specific bad set is meager --- CORRECTED to the FULL set.\<close>  By @{thm
  Phibad_dip_imp_detHess0}, \<open>\<Phi> = 0\<close> gives \<open>\<nabla>\<^sub>\<Omega>U = 0 \<and> det (\<nabla>\<^sup>2U) = 0\<close>; then every witnessing \<open>\<omega>\<close> falls
  into exactly one of \<^bold>\<open>four\<close> strata --- regular (M4), rank-deficient (M5), steering-singular (M6),
  or array-null \<open>A = 0\<close> (M6b) --- whose union is meager.  \<^bold>\<open>SOUNDNESS FIX:\<close> the conclusion is now the
  \<^bold>\<open>full\<close> degenerate-critical set \<open>{\<exists>\<omega>. \<Phi> = 0}\<close> (no spurious \<open>A \<noteq> 0\<close>), so its complement gives a point
  with \<^emph>\<open>no\<close> degenerate critical at any \<open>\<omega>\<close> --- what the capstone actually needs.  \<^bold>\<open>This is the lemma
  the capstone consumes\<close>, in place of the unprovable generic \<open>Phi_bad_meager\<close>.\<close>

lemma Phi_bad_meager_dip:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and oddN: "odd CARD('n)"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
    and d3core: "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
    and branchcore: "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
proof -
  let ?reg = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  let ?def = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  let ?steer = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  let ?null = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
  have meag4: "meager (?reg \<union> ?def \<union> ?steer \<union> ?null)"
    by (intro meager_Un meager_bad_regular_stratum_on[OF openV Vne c6]
              meager_rank_deficient_stratum[OF openV Vne c6 d0 pf hsep kdiff nsing d3core branchcore]
              meager_steering_singular_stratum[OF openV Vne c6 d0 pf hsep kdiff]
              meager_Azero_degenerate_stratum[OF openV Vne c6 oddN d0 pf])
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}
             \<subseteq> ?reg \<union> ?def \<union> ?steer \<union> ?null"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    then obtain \<omega> where xV: "x \<in> V" and wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and pb: "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    from Phibad_dip_imp_detHess0[OF pb]
    have g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and d0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" by blast+
    show "x \<in> ?reg \<union> ?def \<union> ?steer \<union> ?null"
      using xV wD g0 d0
      by fastforce
  qed
  show ?thesis by (rule meager_subset[OF sub meag4])
qed


subsection \<open>The capstone: \<open>\<F>\<^sub>0\<close> is nonempty for appropriately chosen \<open>\<xi>, \<kappa>, \<epsilon>\<close>\<close>

text \<open>TeX Lemma~\eqref{F0} (D_edit_May18, the 2-D version, L1288/F0\_nonempty\_proof\_2D):
  for appropriately chosen \<open>\<xi>,\<kappa>,\<epsilon> > 0\<close>, \<open>\<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = \<F> \<inter> X\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close> is nonempty.

  \<^bold>\<open>No regularity is assumed.\<close>  The analytic input --- a feasible \<open>x\<^sub>0\<close> whose pattern is
  \<^emph>\<open>regular\<close> (\<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> on the \<open>\<epsilon>\<close>-sphere, and \<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> or \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> on \<open>\<Omega>\<^sup>~\<close>) ---
  is a \<^emph>\<open>consequence\<close> of \<open>Phi_bad_meager\<close> + Baire (the degenerate configurations are
  meager, so their complement inside the open interior of the feasible body is dense and
  in particular nonempty), packaged for the actual pattern as the obligation
  \<open>regular_feasible_point_dip\<close> below.  This is precisely what the determinant computation was
  for.  Given that point, the margins \<open>\<kappa> = min\<^bsub>\<partial>B\<^sub>\<epsilon>\<^esub>\<parallel>\<nabla>\<^sub>\<Omega>U\<parallel>\<close> and
  \<open>\<xi> = min\<^bsub>\<Omega>\<^sup>~\<^esub>(\<parallel>\<nabla>\<^sub>\<Omega>U\<parallel> + \<sigma>\<^sub>m\<^sub>i\<^sub>n(H))\<close> are positive by Weierstrass, and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.
  We split the analytic core (\<open>F0_nonempty_of_witness\<close>) from the witness, so the concrete
  dipole capstone \<open>F0_dip_nonempty\<close> discharges the \<^emph>\<open>continuity\<close> half from proven facts and
  leaves only the genuine existence-of-a-regular-feasible-point hole.\<close>

lemma mem_imp_ne_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}" by blast

text \<open>\<^bold>\<open>The capstone core, parametrised by the regular feasible witness.\<close>  Given a feasible
  \<open>x\<^sub>0\<close> and radius \<open>\<epsilon>>0\<close> whose pattern is regular --- gradient nonvanishing on the
  \<open>\<epsilon>\<close>-sphere, gradient-or-nondegenerate on the annulus, with the relevant norms continuous
  --- the positive margins \<open>\<kappa>,\<xi>\<close> exist by Weierstrass and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.  This is the
  purely analytic half of \<open>F0_nonempty\<close>; the witness itself (the determinant/Baire payoff)
  is the separate obligation.  Isolating it lets the \<^emph>\<open>concrete dipole\<close> capstone discharge
  the continuity conjuncts from the proven @{thm norm_gradU_dip_continuous_on} /
  @{thm sigma_min_HessU_dip_continuous_on}, rather than assuming them.\<close>

lemma F0_nonempty_of_witness:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real"
    and R dmin A B D \<delta>null pmin :: real and \<omega>null ctr :: planar
    and x0 :: "planar^'n" and \<epsilon> :: real and \<Omega>dom :: "planar set"
  assumes \<epsilon>0: "0 < \<epsilon>" and cOm: "compact \<Omega>dom"
    and feas: "x0 \<in> Ffeas cvec g R dmin A B D \<omega>null ctr \<delta>null pmin"
    and cdN: "continuous_on (sphere ctr \<epsilon>) (\<lambda>\<omega>. norm (gradU cvec g x0 \<omega>))"
    and cdsum: "continuous_on (\<Omega>dom - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
    and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU cvec g x0 \<omega> \<noteq> 0"
    and rO: "\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
                gradU cvec g x0 y \<noteq> 0 \<or> 0 < sigma_min (HessU cvec g x0 y)"
  shows "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
            \<and> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>
                \<noteq> ({}::(planar^'n) set)"
proof -
  \<comment> \<open>the positive \<open>\<kappa>\<close>-margin on the \<open>\<epsilon>\<close>-sphere (Weierstrass)\<close>
  have sph_ne: "sphere ctr \<epsilon> \<noteq> {}"
  proof -
    have "dist (ctr + \<epsilon> *\<^sub>R axis (1::2) 1) ctr = \<epsilon>"
      using \<epsilon>0 by (simp add: dist_norm abs_of_pos)
    hence "ctr + \<epsilon> *\<^sub>R axis (1::2) 1 \<in> sphere ctr \<epsilon>"
      by (simp add: dist_commute)
    thus ?thesis by blast
  qed
  obtain \<omega>m where \<omega>m: "\<omega>m \<in> sphere ctr \<epsilon>"
      and \<omega>min: "\<forall>\<omega>\<in>sphere ctr \<epsilon>.
                    norm (gradU cvec g x0 \<omega>m) \<le> norm (gradU cvec g x0 \<omega>)"
    using continuous_attains_inf[OF compact_sphere sph_ne cdN] by blast
  define \<kappa> where "\<kappa> = norm (gradU cvec g x0 \<omega>m)"
  have \<kappa>pos: "0 < \<kappa>" using bspec[OF rsph \<omega>m] unfolding \<kappa>_def by simp
  have inXrob: "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>"
    using \<omega>min unfolding Xrobust_def \<kappa>_def by simp
  \<comment> \<open>the positive \<open>\<xi>\<close>-margin on \<open>\<Omega>\<^sup>~\<close> (vacuous if \<open>\<Omega>\<^sup>~ = \<emptyset>\<close>)\<close>
  show ?thesis
  proof (cases "\<Omega>dom - ball ctr \<epsilon> = {}")
    case True
    have "x0 \<in> X0 cvec g ctr (\<Omega>dom) 1 \<kappa> \<epsilon>"
      using inXrob True unfolding X0_def by blast
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin 1 \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin 1 \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    moreover have "(0::real) < 1" by simp
    ultimately show ?thesis using \<kappa>pos \<epsilon>0 by blast
  next
    case False
    obtain ym where ym: "ym \<in> \<Omega>dom - ball ctr \<epsilon>"
        and ymin: "\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
              norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)
              \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y)"
      using continuous_attains_inf[OF compact_minus_ball[OF cOm] False cdsum] by blast
    define \<xi> where "\<xi> = norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)"
    have \<xi>pos: "0 < \<xi>"
    proof (cases "gradU cvec g x0 ym = 0")
      case True
      with bspec[OF rO ym] have "0 < sigma_min (HessU cvec g x0 ym)" by simp
      thus ?thesis unfolding \<xi>_def
        using norm_ge_zero[of "gradU cvec g x0 ym"] by linarith
    next
      case False
      hence "0 < norm (gradU cvec g x0 ym)" by simp
      thus ?thesis unfolding \<xi>_def
        using sigma_min_nonneg[of "HessU cvec g x0 ym"] by linarith
    qed
    have "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>
          \<and> (\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
                \<xi> \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
      using inXrob ymin unfolding \<xi>_def by blast
    hence "x0 \<in> X0 cvec g ctr (\<Omega>dom) \<xi> \<kappa> \<epsilon>" unfolding X0_def by simp
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    thus ?thesis using \<xi>pos \<kappa>pos \<epsilon>0 by blast
  qed
qed

subsection \<open>The capstone for the ACTUAL dipole pattern \<open>U_dip\<close>\<close>

text \<open>\<^bold>\<open>The genuine remaining obligation, for the actual function.\<close>  Specialised to the
  concrete steered dipole \<open>cvec = cvec\<^sub>dip \<omega>\<^sub>0 \<omega>\<^sub>s\<close>, \<open>g = gain\<^sub>dip\<close>: there is a feasible
  configuration \<open>x\<^sub>0\<close> and radius \<open>\<epsilon>>0\<close> whose pattern is regular (gradient nonvanishing on
  \<open>\<partial>B\<^sub>\<epsilon>\<close>, gradient-or-nondegenerate on \<open>\<Omega>\<^sup>~\<close>).  This is \<^emph>\<open>exactly\<close> the determinant/Baire
  payoff (degenerate configs meager, @{thm Phi_bad_meager_dip} + Baire inside the feasible
  interior); crucially the \<^emph>\<open>continuity\<close> half is no longer part of this hole --- it is
  discharged below from the proven dipole facts.\<close>

text \<open>\<^bold>\<open>The Baire scaffold for \<open>regular_feasible_point_dip\<close> (\<^bold>\<open>statements only\<close>; proofs deferred).\<close>\<close>

text \<open>\<^bold>\<open>(C0) A nonzero smallest singular value is exactly invertibility.\<close>  For a real \<open>2\<times>2\<close>
  matrix the smallest singular value @{const sigma_min} is positive iff the determinant is
  nonzero --- the bridge between the degeneracy slot \<open>det (\<nabla>\<^sup>2U) = 0\<close> and the capstone's
  \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> nondegeneracy margin.\<close>

lemma sigma_min_pos_iff_invertible:
  fixes H :: "real^2^2"
  shows "0 < sigma_min H \<longleftrightarrow> det H \<noteq> 0"
proof -
  have lin: "linear ((*v) H)" by (rule matrix_vector_mul_linear)
  have bdd: "bdd_below ((\<lambda>v. norm (H *v v)) ` sphere 0 1)"
    by (rule bdd_belowI[of _ 0]) auto
  have cont: "continuous_on (sphere (0::real^2) 1) (\<lambda>v. norm (H *v v))"
    by (rule continuous_on_norm[OF
          bounded_linear.continuous_on[OF matrix_vector_mul_bounded_linear continuous_on_id]])
  \<comment> \<open>Step 1: positivity of the smallest singular value \<open>\<longleftrightarrow>\<close> nonvanishing on the unit sphere.\<close>
  have nz_iff: "0 < sigma_min H \<longleftrightarrow> (\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0)"
  proof
    assume pos: "0 < sigma_min H"
    show "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    proof
      fix v assume v: "v \<in> sphere (0::real^2) 1"
      have "sigma_min H \<le> norm (H *v v)"
        unfolding sigma_min_def by (rule cINF_lower[OF bdd v])
      with pos show "H *v v \<noteq> 0" by auto
    qed
  next
    assume nz: "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    obtain v0 where v0: "v0 \<in> sphere (0::real^2) 1"
        and v0min: "\<forall>v\<in>sphere (0::real^2) 1. norm (H *v v0) \<le> norm (H *v v)"
      using continuous_attains_inf[OF compact_sphere sphere01_ne cont] by blast
    have "sigma_min H = norm (H *v v0)"
    proof -
      have "sigma_min H \<le> norm (H *v v0)"
        unfolding sigma_min_def by (rule cINF_lower[OF bdd v0])
      moreover have "norm (H *v v0) \<le> sigma_min H"
        unfolding sigma_min_def by (rule cINF_greatest[OF sphere01_ne]) (rule v0min[rule_format])
      ultimately show ?thesis by linarith
    qed
    moreover have "0 < norm (H *v v0)" using nz v0 by auto
    ultimately show "0 < sigma_min H" by simp
  qed
  \<comment> \<open>Step 2: nonvanishing on the unit sphere \<open>\<longleftrightarrow>\<close> injectivity (normalise an arbitrary nonzero
      kernel vector to the sphere).\<close>
  have inj_iff: "(\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0) \<longleftrightarrow> inj ((*v) H)"
  proof
    assume nz: "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    show "inj ((*v) H)"
    proof (rule injI)
      fix a b assume eq: "H *v a = H *v b"
      have z: "H *v (a - b) = 0"
        using eq by (simp add: matrix_vector_mult_diff_distrib)
      show "a = b"
      proof (rule ccontr)
        assume "a \<noteq> b"
        hence ab: "a - b \<noteq> 0" by simp
        define u where "u = inverse (norm (a - b)) *\<^sub>R (a - b)"
        have nu: "norm u = 1"
        proof -
          have "norm u = \<bar>inverse (norm (a - b))\<bar> * norm (a - b)"
            by (simp add: u_def)
          also have "\<dots> = inverse (norm (a - b)) * norm (a - b)" by simp
          also have "\<dots> = 1" using ab by simp
          finally show ?thesis .
        qed
        have "u \<in> sphere (0::real^2) 1" using nu by (simp add: dist_norm)
        moreover have "H *v u = 0"
          by (simp add: u_def matrix_vector_mult_scaleR z)
        ultimately show False using nz by auto
      qed
    qed
  next
    assume inj: "inj ((*v) H)"
    show "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    proof
      fix v assume v: "v \<in> sphere (0::real^2) 1"
      hence "v \<noteq> 0" by (auto simp: dist_norm)
      moreover have "H *v (0::real^2) = 0" by simp
      ultimately show "H *v v \<noteq> 0" using inj by (metis injD)
    qed
  qed
  \<comment> \<open>Step 3: injectivity of a square linear map \<open>\<longleftrightarrow>\<close> nonzero determinant.\<close>
  have det_iff: "inj ((*v) H) \<longleftrightarrow> det H \<noteq> 0"
    using det_nz_iff_inj[OF lin] by simp
  show ?thesis using nz_iff inj_iff det_iff by blast
qed

text \<open>\<^bold>\<open>(C1) The feasible body has nonempty interior (Slater).\<close>  If \<^emph>\<open>some\<close> configuration satisfies
  every constraint \<^emph>\<open>strictly\<close> --- all spacings exceed \<open>d\<^sub>min\<close>, the null power is below \<open>\<delta>\<^sub>null\<close>,
  the main power lies strictly between \<open>p\<^sub>min\<close> and the Cauchy--Schwarz cap, and \<open>\<parallel>\<bm>x\<parallel> < R\<close> --- then
  (each constraint function being continuous) that point is interior to @{const Ffeas}.  The
  hypothesis is the genuine strict-feasibility input; it does not mention \<open>interior\<close>.\<close>

lemma Ffeas_interior_nonempty:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes "\<exists>x::(real^2)^'n.
       (\<forall>p. fst p \<noteq> snd p \<longrightarrow> dmin < spdist A B D (x $ fst p) (x $ snd p))
     \<and> Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < \<delta>null
     \<and> pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr
     \<and> Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr < gain_dip ctr * (real CARD('n))\<^sup>2
     \<and> norm x < R"
  shows "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
proof -
  from assms obtain x :: "(real^2)^'n"
    where spac0: "\<forall>p. fst p \<noteq> snd p \<longrightarrow> dmin < spdist A B D (x $ fst p) (x $ snd p)"
      and Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < \<delta>null"
      and Pgt: "pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr"
      and nx: "norm x < R" by blast
  have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (x $ fst p) (x $ snd p)"
    using spac0 by blast
  have inR: "x \<in> ball 0 R" using nx by (simp add: dist_norm)
  obtain \<rho> where \<rho>: "0 < \<rho>"
      and sub: "ball x \<rho>
                \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
    using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
  have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
    by (rule interior_maximal[OF sub open_ball])
  moreover have "x \<in> ball x \<rho>" using \<rho> by simp
  ultimately show ?thesis by blast
qed

text \<open>\<^bold>\<open>(C2) Baire: a regular configuration exists inside the feasible interior.\<close>  The degenerate
  configurations are meager (@{thm Phi_bad_meager_dip}, the \<^bold>\<open>full\<close> bad set, including \<open>A = 0\<close>), so
  their complement is comeager, hence dense, hence meets the nonempty open feasible interior ---
  yielding a feasible \<open>x\<^sub>0\<close> carrying \<^bold>\<open>no\<close> degenerate critical point at \<^bold>\<open>any\<close> \<open>\<omega>\<close> (\<open>\<Phi> \<noteq> 0\<close> everywhere).
  \<^bold>\<open>SOUNDNESS FIX:\<close> the conclusion no longer carries the spurious \<open>A \<noteq> 0\<close> --- array-factor nulls
  (\<open>A = 0\<close>) are critical points (\<open>\<nabla>\<^sub>\<Omega>U = 0\<close>) too, and a \<^emph>\<open>degenerate\<close> null would break the
  capstone's regularity, so it must also be excluded.\<close>

lemma regular_config_exists:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
    and int_ne: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
    and d3core: "d3_detHess_arc_chart_core_all
          (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
             :: ((real^2)^'n) set)) ctr \<delta> \<omega>0 \<omega>s"
    and branchcore: "branchP_indep_closed_cover_core_all
          (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
             :: ((real^2)^'n) set)) ctr \<delta> \<omega>0 \<omega>s"
  shows "\<exists>x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                          :: ((real^2)^'n) set).
            \<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
proof -
  define I where "I = interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: ((real^2)^'n) set)"
  have openI: "open I" unfolding I_def by (rule open_interior)
  have Ine: "I \<noteq> {}" unfolding I_def by (rule int_ne)
  have d3coreI: "d3_detHess_arc_chart_core_all I ctr \<delta> \<omega>0 \<omega>s"
    using d3core unfolding I_def by simp
  have branchcoreI: "branchP_indep_closed_cover_core_all I ctr \<delta> \<omega>0 \<omega>s"
    using branchcore unfolding I_def by simp
  have meagB: "meager {x \<in> I. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    by (rule Phi_bad_meager_dip[OF openI Ine c6 oddN hsep kdiff d0 pf nsing d3coreI branchcoreI])
  have "\<not> I \<subseteq> {x \<in> I. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
  proof
    assume sub: "I \<subseteq> {x \<in> I. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    have "meager I" by (rule meager_subset[OF sub meagB])
    moreover have "\<not> meager I" by (rule open_nonempty_not_meager[OF openI Ine])
    ultimately show False by simp
  qed
  then obtain x0 where x0I: "x0 \<in> I"
    and x0nB: "x0 \<notin> {x \<in> I. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}" by blast
  have x0Iexp: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
    using x0I unfolding I_def by assumption
  have reg: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
    using x0I x0nB by blast
  from x0Iexp reg
  have conjx0: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)
        \<and> (\<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)" by (rule conjI)
  \<comment> \<open>Composition fully established: \<open>x0Iexp\<close> (\<open>x0 \<in> interior\<close>) and \<open>reg\<close> (\<open>\<forall>\<omega>. \<Phi> \<noteq> 0\<close>) are the
      witness data.  Only the final \<^emph>\<open>bounded-existential introduction\<close> \<open>\<exists>x0\<in>interior. \<dots>\<close> with
      witness \<open>x0\<close> is left open --- a witness-instantiation tactic step (\<open>bexI\<close>/\<open>rule_tac x=x0\<close>)
      that needs live goal/type inspection to dispatch against the large \<open>interior (Ffeas \<dots>)\<close>
      term; it is mathematically immediate from \<open>x0Iexp\<close> and \<open>reg\<close>.\<close>
  show ?thesis
  proof (rule bexI[where x = x0])
    show "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0" by (rule reg)
  next
    show "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
      by (rule x0Iexp)
  qed
qed

text \<open>\<^bold>\<open>(C3) From ``no degenerate critical point'' to the sphere/annulus regularity.\<close>  If \<open>x\<^sub>0\<close> has
  no degenerate critical point in \<open>\<Omega>\<close> (at every \<open>\<omega>\<close>, either \<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> or \<open>det (\<nabla>\<^sup>2U) \<noteq> 0\<close>), then for
  a suitable radius \<open>\<epsilon> > 0\<close> the gradient is nonvanishing on the sphere \<open>\<partial>B\<^sub>\<epsilon>\<close> and
  gradient-or-nondegenerate on the annulus \<open>\<Omega> - B\<^sub>\<epsilon>\<close> --- exactly the conclusion shape of
  \<open>regular_feasible_point_dip\<close> below.  (Nondegenerate critical points are isolated, so \<open>\<epsilon>\<close> can dodge
  them; degeneracy \<open>det = 0\<close> is rephrased as \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n > 0\<close> via @{thm sigma_min_pos_iff_invertible}.)\<close>

lemma isolated_nondeg_zero:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes hd: "(f has_derivative L) (at c)" and injL: "inj L" and fc: "f c = 0"
  shows "\<exists>d>0. \<forall>y. dist y c < d \<longrightarrow> y \<noteq> c \<longrightarrow> f y \<noteq> 0"
proof -
  have linL: "linear L" using hd by (rule has_derivative_linear)
  obtain B where B0: "0 < B" and Bn: "\<And>v. B * norm v \<le> norm (L v)"
    using linear_inj_bounded_below_pos[OF linL injL] by blast
  have "\<forall>e>0. \<exists>d>0. \<forall>y. norm (y - c) < d \<longrightarrow> norm (f y - f c - L (y - c)) \<le> e * norm (y - c)"
    using hd by (simp add: has_derivative_at_alt)
  then obtain d where d0: "0 < d"
      and db: "\<And>y. norm (y - c) < d \<Longrightarrow> norm (f y - f c - L (y - c)) \<le> (B/2) * norm (y - c)"
    using B0 half_gt_zero by blast
  have "\<forall>y. dist y c < d \<longrightarrow> y \<noteq> c \<longrightarrow> f y \<noteq> 0"
  proof (intro allI impI)
    fix y assume yd: "dist y c < d" and yc: "y \<noteq> c"
    have nyc: "0 < norm (y - c)" using yc by simp
    have ndc: "norm (y - c) < d" using yd by (simp add: dist_norm)
    have a1: "B * norm (y - c) \<le> norm (L (y - c))" by (rule Bn)
    have a2: "norm (f y - L (y - c)) \<le> (B/2) * norm (y - c)" using db[OF ndc] fc by simp
    have "(B/2) * norm (y - c) = B * norm (y - c) - (B/2) * norm (y - c)" by simp
    also have "\<dots> \<le> norm (L (y - c)) - norm (f y - L (y - c))" using a1 a2 by linarith
    also have "\<dots> \<le> norm (f y)"
      using norm_triangle_ineq2[of "L (y - c)" "f y"] by (simp add: norm_minus_commute)
    finally have "(B/2) * norm (y - c) \<le> norm (f y)" .
    moreover have "0 < (B/2) * norm (y - c)" using nyc B0 by simp
    ultimately have "0 < norm (f y)" by linarith
    thus "f y \<noteq> 0" by auto
  qed
  thus ?thesis using d0 by blast
qed


lemma sphere_subset_Omega:
  fixes ctr :: "real^2"
  assumes "\<epsilon> \<le> pi/2"
  shows "sphere ctr \<epsilon> \<subseteq> Omega ctr"
proof
  fix y assume "y \<in> sphere ctr \<epsilon>"
  hence dy: "dist y ctr = \<epsilon>" by (simp add: dist_commute sphere_def)
  show "y \<in> Omega ctr"
    unfolding Omega_def mem_box_cart
  proof (intro allI)
    fix i :: 2
    have b: "\<bar>y$i - ctr$i\<bar> \<le> pi/2"
    proof -
      have "\<bar>y$i - ctr$i\<bar> = \<bar>(y - ctr)$i\<bar>" by simp
      also have "\<dots> \<le> norm (y - ctr)" by (rule component_le_norm_cart)
      also have "\<dots> = \<epsilon>" using dy by (simp add: dist_norm)
      finally show ?thesis using assms by simp
    qed
    have v: "pi/2 \<le> (vector [pi/2, pi] :: real^2) $ i"
      using exhaust_2[of i] by (auto simp: vector_2 pi_gt_zero)
    have lo: "(ctr - vector [pi/2, pi]) $ i = ctr $ i - vector [pi/2, pi] $ i"
      by (simp add: vector_minus_component)
    have hi: "(ctr + vector [pi/2, pi]) $ i = ctr $ i + vector [pi/2, pi] $ i"
      by (simp add: vector_add_component)
    have b1: "y$i - ctr$i \<le> pi/2" using abs_le_D1[OF b] .
    have b2: "ctr$i - y$i \<le> pi/2" using abs_le_D2[OF b] by simp
    show "(ctr - vector [pi/2, pi]) $ i \<le> y $ i \<and> y $ i \<le> (ctr + vector [pi/2, pi]) $ i"
      using lo hi v b1 b2 by linarith
  qed
qed

lemma no_degenerate_to_sphere_annulus:
  fixes x0 :: "(real^2)^'n" and ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and nd: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  shows "\<exists>\<epsilon>>0. (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
proof -
  define f where "f = gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0"
  define C where "C = {\<omega>. \<omega> \<in> OmegaPF ctr \<delta> \<and> f \<omega> = 0}"
  have fcont: "continuous_on UNIV f" unfolding f_def by (rule gradU_dip_continuous_on)
  have isol: "\<not> c islimpt C" if cC: "c \<in> C" for c
  proof -
    from cC have cO: "c \<in> OmegaPF ctr \<delta>" and fc0: "f c = 0" by (auto simp: C_def)
    have dnz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c) \<noteq> 0"
      using nd cO fc0 unfolding f_def by blast
    hence inv: "invertible (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c)" by (simp add: invertible_det_nz)
    have injL: "inj ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c))"
      using inv by (metis matrix_left_invertible_injective invertible_def)
    have hd: "(f has_derivative ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c))) (at c)"
      unfolding f_def by (rule gradU_dip_has_derivative)
    obtain d where d0: "0 < d" and dd: "\<And>y. dist y c < d \<Longrightarrow> y \<noteq> c \<Longrightarrow> f y \<noteq> 0"
      using isolated_nondeg_zero[OF hd injL fc0] by blast
    show "\<not> c islimpt C" using dd d0 by (force simp: islimpt_approachable C_def)
  qed
  have Cint: "C = OmegaPF ctr \<delta> \<inter> {y. f y = 0}" by (auto simp: C_def)
  have Ccomp: "compact C"
    unfolding Cint by (rule compact_Int_closed[OF OmegaPF_compact closed_Collect_eq[OF fcont continuous_on_const]])
  have Cfin: "finite C" using Ccomp isol by (metis compact_eq_Bolzano_Weierstrass order_refl)
  define R where "R = (\<lambda>c. dist c ctr) ` C"
  have Rfin: "finite R" unfolding R_def using Cfin by simp
  have "infinite {0<..\<delta>::real}" using d0 by (simp add: infinite_Ioc)
  hence "infinite ({0<..\<delta>::real} - R)" using Rfin by (rule Diff_infinite_finite[rotated])
  then obtain \<epsilon> where \<epsilon>m: "\<epsilon> \<in> {0<..\<delta>::real} - R" using infinite_imp_nonempty by blast
  have \<epsilon>0: "0 < \<epsilon>" and \<epsilon>pi: "\<epsilon> \<le> \<delta>" and \<epsilon>R: "\<epsilon> \<notin> R" using \<epsilon>m by auto
  have sphere: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. f \<omega> \<noteq> 0"
  proof
    fix \<omega> assume w: "\<omega> \<in> sphere ctr \<epsilon>"
    hence wO: "\<omega> \<in> OmegaPF ctr \<delta>" using sphere_subset_OmegaPF[OF \<epsilon>pi dpi] by blast
    have dw: "dist \<omega> ctr = \<epsilon>" using w by (simp add: dist_commute sphere_def)
    show "f \<omega> \<noteq> 0"
    proof
      assume "f \<omega> = 0"
      hence "\<omega> \<in> C" using wO by (simp add: C_def)
      hence "dist \<omega> ctr \<in> R" by (simp add: R_def)
      thus False using \<epsilon>R dw by simp
    qed
  qed
  have annulus: "\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                   f y \<noteq> 0 \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
  proof
    fix y assume "y \<in> OmegaPF ctr \<delta> - ball ctr \<epsilon>"
    hence yO: "y \<in> OmegaPF ctr \<delta>" by simp
    show "f y \<noteq> 0 \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    proof (cases "f y = 0")
      case True
      hence "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y) \<noteq> 0"
        using nd yO unfolding f_def by blast
      thus ?thesis by (simp add: sigma_min_pos_iff_invertible)
    next
      case False thus ?thesis by blast
    qed
  qed
  show ?thesis using \<epsilon>0 sphere annulus unfolding f_def by blast
qed

lemma regular_feasible_point_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
    and feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: (planar^'n) set) \<noteq> {}"
    and d3core: "d3_detHess_arc_chart_core_all
          (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
             :: (planar^'n) set)) ctr \<delta> \<omega>0 \<omega>s"
    and branchcore: "branchP_indep_closed_cover_core_all
          (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
             :: (planar^'n) set)) ctr \<delta> \<omega>0 \<omega>s"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
  \<comment> \<open>\<^bold>\<open>SOUNDNESS FIX:\<close> requires \<open>feasible\<close> (the feasible body has nonempty interior).  Without
      it the claim is false for infeasible parameters (e.g.\ \<open>pmin > gain_dip ctr * N\<^sup>2\<close> forces
      \<open>Ffeas = {}\<close>).  The composition below is \<^bold>\<open>machine-checked\<close> from the explicit D3
      and Branch-P core premises.\<close>
proof -
  obtain x0 :: "planar^'n"
    where x0I: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
      and x0reg: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
    using regular_config_exists[OF c6 oddN hsep kdiff d0 pf nsing feasible d3core branchcore] by blast
  have x0F: "x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
    using x0I interior_subset by blast
  have nondeg: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  proof (intro ballI notI)
    fix \<omega> assume "\<omega> \<in> OmegaPF ctr \<delta>"
      and deg: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0"
    from deg have g: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0"
      and dz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0" by auto
    have e: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>)
              = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 1
                  * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 2 $ 2
                - (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2"
      by (rule det_2_symmetric[OF HessU_dip_symmetric])
    from e dz have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 1
                      * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 2 $ 2
                    = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2" by simp
    with g have "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0"
      using Phibad_zero_iff by blast
    with x0reg \<open>\<omega> \<in> OmegaPF ctr \<delta>\<close> show False by auto
  qed
  obtain \<epsilon> :: real where \<epsilon>0: "0 < \<epsilon>"
      and sph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
      and ann: "\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    using no_degenerate_to_sphere_annulus[OF d0 dpi nondeg] by blast
  have c1: "0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
    using \<epsilon>0 x0F sph ann by (intro conjI)
  show ?thesis
  proof (rule exI[where x = x0], rule exI[where x = \<epsilon>])
    show "0 < \<epsilon>
          \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
          \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
          \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
      by (rule c1)
  qed
qed

text \<open>\<^bold>\<open>The regular feasible witness for the dipole, with continuity DISCHARGED.\<close>  We bolt the
  two Weierstrass continuity conjuncts --- proven proof-complete in
  @{thm norm_gradU_dip_continuous_on} and @{thm sigma_min_HessU_dip_continuous_on} --- onto
  the regular feasible point, so what remains assumed is purely the existence of that point.\<close>

lemma regular_feasible_witness_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
    and feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: (planar^'n) set) \<noteq> {}"
    and d3core: "d3_detHess_arc_chart_core_all
          (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
             :: (planar^'n) set)) ctr \<delta> \<omega>0 \<omega>s"
    and branchcore: "branchP_indep_closed_cover_core_all
          (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
             :: (planar^'n) set)) ctr \<delta> \<omega>0 \<omega>s"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> continuous_on (sphere ctr \<epsilon>)
                  (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>))
            \<and> continuous_on (OmegaPF ctr \<delta> - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)
                       + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
proof -
  obtain x0 :: "planar^'n" and \<epsilon> :: real
    where \<epsilon>0: "0 < \<epsilon>"
      and feas: "x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
      and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
      and rO: "\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    using regular_feasible_point_dip[OF c6 oddN hsep kdiff d0 dpi pf nsing feasible d3core branchcore] by blast
  have c1: "continuous_on (sphere ctr \<epsilon>)
              (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>))"
    by (rule norm_gradU_dip_continuous_on)
  have c2: "continuous_on (OmegaPF ctr \<delta> - ball ctr \<epsilon>)
              (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)
                   + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
    by (intro continuous_on_add norm_gradU_dip_continuous_on
              sigma_min_HessU_dip_continuous_on)
  show ?thesis using \<epsilon>0 feas c1 c2 rsph rO by blast
qed

text \<open>\<^bold>\<open>The concrete capstone: \<open>\<F>\<^sub>0\<close> for the ACTUAL dipole pattern is nonempty.\<close>  This is
  \<open>thm:final\<close>'s nonemptiness for the real radiation intensity \<open>U_dip = g(\<omega>)\<bar>A(\<bm>x,\<omega>)\<bar>\<^sup>2\<close>
  with the steered wavevector \<open>cvec\<^sub>dip\<close> and the smooth dipole gain \<open>gain\<^sub>dip = \<bar>e(\<theta>)\<bar>\<^sup>2\<close>
  --- no abstract \<open>cvec\<close>/\<open>g\<close>.  The continuity half is fully proven; the remaining
  analytic inputs are the explicit D3 and Branch-P core premises threaded below.\<close>

theorem F0_dip_nonempty:
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and d3core: "\<And>(V::(planar^'n) set) ctr \<delta> \<omega>0 \<omega>s.
          d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
    and branchcore: "\<And>(V::(planar^'n) set) ctr \<delta> \<omega>0 \<omega>s.
          branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "\<exists>A B D \<omega>0 \<omega>s \<omega>null ctr \<delta> R dmin \<delta>null pmin \<xi> \<kappa> \<epsilon>.
            0 < \<delta> \<and> 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr (OmegaPF ctr \<delta>) \<delta>null pmin \<xi> \<kappa> \<epsilon>
              \<noteq> ({}::(planar^'n) set)"
  \<comment> \<open>\<^bold>\<open>The odd-\<open>N\<close> capstone.\<close>  The hypotheses are the dimension restriction \<open>c6\<close> and
      oddness (as in TeX \<open>thm:final\<close>; oddness powers \<open>dxA_surj\<close> in the \<open>A = 0\<close> stratum); the design
      (steering \<open>\<omega>\<^sub>0,\<omega>\<^sub>s,\<omega>\<^sub>null\<close>, geometry \<open>A,B,D\<close>, tolerances \<open>d\<^sub>min,\<delta>\<^sub>null,p\<^sub>min,R\<close> and margins) is
      \<^emph>\<open>delivered by the construction\<close>, not assumed.  Feasibility is discharged by the explicit
      Slater witness (@{thm feasible_witness_exists}): the actual \<open>cvec_dip\<close> nulls at \<open>\<omega>\<^sub>null\<close>
      (roots of unity, \<open>A(\<bm>x,\<omega>\<^sub>null)=0\<close>), the main-beam power is pinned to the cap for \<^emph>\<open>every\<close>
      configuration (@{thm Upow_at_main}: \<open>cvec_dip(\<omega>\<^sub>0)=0\<close>), and we pick \<open>p\<^sub>min,d\<^sub>min,\<delta>\<^sub>null\<close> to make
      the witness strictly feasible --- everything is under our control.\<close>
proof -
  define \<omega>0 :: planar where "\<omega>0 = vector [pi/2, 0]"
  define \<omega>s :: planar where "\<omega>s = vector [0, 0]"
  define \<omega>null :: planar where "\<omega>null = vector [pi, 0]"
  have hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    by (simp add: \<omega>s_def \<omega>0_def kz_def)
  have kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    by (simp add: \<omega>0_def \<omega>s_def kx_def sin_pi_half)
  have d0: "(0::real) < pi/4" by simp
  have dpi: "(pi::real)/4 \<le> pi" by simp
  have pf: "\<forall>\<omega>\<in>OmegaPF \<omega>0 (pi/4). sin (\<omega> $ 1) \<noteq> 0"
  proof
    fix \<omega> :: planar assume "\<omega> \<in> OmegaPF \<omega>0 (pi/4)"
    hence mb: "(\<omega>0 - vector [pi/4, pi]) $ 1 \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> (\<omega>0 + vector [pi/4, pi]) $ 1"
      unfolding OmegaPF_def mem_box_cart by blast
    have l1: "(\<omega>0 - vector [pi/4, pi]) $ 1 = pi/4"
      by (simp add: \<omega>0_def vector_minus_component vector_2)
    have l2: "(\<omega>0 + vector [pi/4, pi]) $ 1 = 3*pi/4"
      by (simp add: \<omega>0_def vector_add_component vector_2)
    have lo: "0 < \<omega> $ 1" and hi: "\<omega> $ 1 < pi" using mb l1 l2 pi_gt_zero by linarith+
    have "0 < sin (\<omega> $ 1)" by (rule sin_gt_zero[OF lo hi])
    thus "sin (\<omega> $ 1) \<noteq> 0" by simp
  qed
  have nsing: "d3_collinear_nsing_all \<omega>0 (pi/4) \<omega>0 \<omega>s"
  proof (unfold d3_collinear_nsing_all_def, intro ballI)
    fix \<omega> :: planar
    assume wL: "\<omega> \<in> {\<omega> \<in> OmegaPF \<omega>0 (pi/4). d3_crossTheta \<omega>0 \<omega>s \<omega> = 0}"
    hence wO: "\<omega> \<in> OmegaPF \<omega>0 (pi/4)"
      and z: "d3_crossTheta \<omega>0 \<omega>s \<omega> = 0" by auto
    have mb: "(\<omega>0 - vector [pi/4, pi]) $ 1 \<le> \<omega> $ 1
        \<and> \<omega> $ 1 \<le> (\<omega>0 + vector [pi/4, pi]) $ 1"
      using wO unfolding OmegaPF_def mem_box_cart by blast
    have l1: "(\<omega>0 - vector [pi/4, pi]) $ 1 = pi/4"
      by (simp only: \<omega>0_def vector_minus_component vector_2)
    have l2: "(\<omega>0 + vector [pi/4, pi]) $ 1 = 3*pi/4"
      by (simp add: \<omega>0_def vector_add_component vector_2)
    have lo: "0 < \<omega> $ 1" and hi: "\<omega> $ 1 < pi"
      using mb l1 l2 pi_gt_zero by linarith+
    have c_lt1: "cos (\<omega> $ 1) < 1"
    proof -
      have h0: "0 < (\<omega> $ 1) / 2" using lo by simp
      have h2: "(\<omega> $ 1) / 2 < 2" using hi pi_less_4 by linarith
      have "cos (2 * ((\<omega> $ 1) / 2)) < 1"
        by (rule cos_double_less_one[OF h0 h2])
      thus ?thesis by simp
    qed
    have cne: "cos (\<omega> $ 1) - 1 \<noteq> 0" using c_lt1 by linarith
    have trig_collapse: "cos (\<omega>$1) * (cos (\<omega>$1) * sin (\<omega>$2))
        + sin (\<omega>$1) * (sin (\<omega>$1) * sin (\<omega>$2)) = sin (\<omega>$2)"
    proof -
      have "cos (\<omega>$1) * (cos (\<omega>$1) * sin (\<omega>$2))
          + sin (\<omega>$1) * (sin (\<omega>$1) * sin (\<omega>$2))
          = (cos (\<omega>$1) * cos (\<omega>$1) + sin (\<omega>$1) * sin (\<omega>$1)) * sin (\<omega>$2)"
        by (simp only: mult.assoc distrib_right)
      also have "\<dots> = sin (\<omega>$2)"
        by (simp only: sin_cos_squared_add3)
      finally show ?thesis .
    qed
    have theta_eq: "d3_crossTheta \<omega>0 \<omega>s \<omega> = (cos (\<omega>$1) - 1) * sin (\<omega>$2)"
      by (simp add: d3_crossTheta_def cvec_dip_def Dcvec_dip_def
          \<omega>0_def \<omega>s_def kx_def ky_def kz_def axis_def vector_2
          sin_pi_half cos_pi_half algebra_simps trig_collapse)
    have s2z: "sin (\<omega>$2) = 0" using z theta_eq cne by auto
    have c2nz: "cos (\<omega>$2) \<noteq> 0"
    proof
      assume c2z: "cos (\<omega>$2) = 0"
      have "\<bar>cos (\<omega>$2)\<bar> = (1::real)" by (rule sin_zero_abs_cos_one[OF s2z])
      thus False using c2z by simp
    qed
    have d2eq: "d3_collinear_d2 \<omega>0 \<omega>s \<omega> = (cos (\<omega>$1) - 1) * cos (\<omega>$2)"
      by (simp add: d3_collinear_d2_def d3_crossA_def d3_crossB_def
          \<omega>0_def \<omega>s_def kx_def ky_def kz_def vector_2
          sin_pi_half cos_pi_half algebra_simps)
    have "d3_collinear_d2 \<omega>0 \<omega>s \<omega> \<noteq> 0"
      using cne c2nz d2eq by simp
    thus "d3_collinear_d2 \<omega>0 \<omega>s \<omega> \<noteq> 0
       \<or> d3_collinear_d1 \<omega>0 \<omega>s \<omega> \<noteq> 0" by blast
  qed
  have cn: "cvec_dip \<omega>0 \<omega>s \<omega>null \<noteq> 0"
  proof -
    have "cvec_dip \<omega>0 \<omega>s \<omega>null $ 1 = - 2"
      by (simp add: cvec_dip_def \<omega>0_def \<omega>s_def \<omega>null_def kx_def ky_def kz_def
                    sin_pi_half cos_pi_half axis_def)
    hence "cvec_dip \<omega>0 \<omega>s \<omega>null $ 1 \<noteq> 0" by simp
    thus ?thesis by (metis zero_index)
  qed
  have N1: "CARD('n) > 1" using c6 by simp
  have spos: "(0::real) < 1" by simp
  obtain x :: "planar^'n"
    where afz: "af (cvec_dip \<omega>0 \<omega>s) x \<omega>null = 0"
      and spac0: "\<forall>m m'. m \<noteq> m' \<longrightarrow> (1::real) \<le> spdist 0 0 1 (x $ m) (x $ m')"
    using feasible_witness_exists[OF N1 cn spos] by meson
  define R :: real where "R = norm x + 1"
  have g0pos: "0 < gain_dip \<omega>0"
  proof -
    have "sin (\<omega>0 $ 1) \<noteq> 0" by (simp add: \<omega>0_def sin_pi_half)
    hence "gain_dip \<omega>0 \<noteq> 0" by (rule gain_dip_nonzero_of_sin)
    moreover have "0 \<le> gain_dip \<omega>0" by (rule gain_dip_nonneg)
    ultimately show ?thesis by simp
  qed
  have feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
                    :: (planar^'n) set) \<noteq> {}"
  proof -
    have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. (1/2::real) < spdist 0 0 1 (x $ fst p) (x $ snd p)"
      using spac0 by fastforce
    have Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < 1"
      using afz by (simp add: Upow_def)
    have Pgt: "(0::real) < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0"
    proof -
      have "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0 = gain_dip \<omega>0 * (real CARD('n))\<^sup>2"
        by (rule Upow_at_main[OF hsep])
      moreover have "0 < (real CARD('n))\<^sup>2" using N1 by simp
      ultimately show ?thesis using mult_pos_pos[OF g0pos] by simp
    qed
    have inR: "x \<in> ball 0 R" by (simp add: R_def dist_norm)
    obtain \<rho> where \<rho>: "0 < \<rho>"
        and sub: "ball x \<rho> \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0"
      using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
    have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0)"
      by (rule interior_maximal[OF sub open_ball])
    moreover have "x \<in> ball x \<rho>" using \<rho> by simp
    ultimately show ?thesis by blast
  qed
  have "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 (OmegaPF \<omega>0 (pi/4)) 1 0 \<xi> \<kappa> \<epsilon>
              \<noteq> ({}::(planar^'n) set)"
  proof -
    have d3core_feas: "d3_detHess_arc_chart_core_all
        (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
           :: (planar^'n) set)) \<omega>0 (pi/4) \<omega>0 \<omega>s"
      by (rule d3core)
    have branchcore_feas: "branchP_indep_closed_cover_core_all
        (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
           :: (planar^'n) set)) \<omega>0 (pi/4) \<omega>0 \<omega>s"
      by (rule branchcore)
    show ?thesis
      using regular_feasible_witness_dip[
          OF c6 oddN hsep kdiff d0 dpi pf nsing feasible d3core_feas branchcore_feas]
    by (blast intro: F0_nonempty_of_witness OmegaPF_compact)
  qed
  thus ?thesis using d0 by blast
qed

end
