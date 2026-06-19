theory Scratch_m5_d3sound
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
          "Applied_Math_Sard.Sard_Negligible"
begin

text \<open>\<^bold>\<open>(M5) Core D3 (SOUND) --- fixing the \<open>analytic_arc\<close> definition and re-proving the
  per-arc x-projection chain against it.\<close>

  \<^bold>\<open>Wave-7 bug fix.\<close>  The earlier @{text analytic_arc} was \<^emph>\<open>continuous-only\<close>
  (\<open>\<gamma> = \<phi> ` {a..b}\<close> with merely \<open>continuous_on {a..b} \<phi>\<close>).  That predicate is
  UNSOUND for a "1-dimensional arc" abstraction: by the Hahn--Mazurkiewicz theorem
  a continuous image of a compact interval may be a Peano space-filling curve
  whose image is a full 2-cell (positive area, NOT negligible).  We replace it by
  the STRENGTHENED \<open>C\<^sup>1\<close> predicate
  \<open>analytic_arc \<gamma> \<longleftrightarrow> (\<exists>a b \<phi>. a \<le> b \<and> \<phi> C1_differentiable_on {a..b} \<and> \<gamma> = \<phi> ` {a..b})\<close>.

  \<^bold>\<open>The soundness gate.\<close>  We prove @{text analytic_arc_negligible}:
  \<open>analytic_arc \<gamma> \<Longrightarrow> negligible \<gamma>\<close>.  This certifies the fixed definition is
  genuinely 1-dimensional: a \<open>C\<^sup>1\<close> (hence locally Lipschitz, hence
  differentiable_on) image of a 1-dim interval is negligible in the plane
  (@{thm negligible_differentiable_image_lowdim}, since \<open>DIM(real) = 1 < 2 = DIM(real^2)\<close>).
  The Peano counterexample is now excluded.

  \<^bold>\<open>The D3 chain, re-proved against the SOUND def.\<close>  Strengthening the hypothesis
  \<open>analytic_arc \<gamma>\<close> only MAKES THE LEMMAS EASIER (the conclusions are unchanged);
  every structural / reduction / assembly layer is reproduced sorry-free.  The
  single isolated genuine analytic core (the IFT chart bundle) is carried as the
  one precisely-scoped \<open>sorry\<close> @{text excess_arc_charts_Nn}, exactly as the
  reduction files do, and the closed-negligible cover
  @{text excess_arc_negligible_closed_cover} and the meagerness
  @{text excess_arc_projection_meager} are assembled sorry-free from it.\<close>


subsection \<open>The STRENGTHENED analytic-arc predicate (Wave-7 fix: \<open>C\<^sup>1\<close>, not continuous)\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> \<phi> C1_differentiable_on {a..b}
                          \<and> \<gamma> = \<phi> ` {a..b})"


subsection \<open>STEP 1 --- the soundness gate: a \<open>C\<^sup>1\<close> arc in the plane is negligible\<close>

text \<open>\<^bold>\<open>Soundness gate (sorry-free).\<close>  The strengthened @{const analytic_arc} is
  genuinely 1-dimensional: the underlying \<open>C\<^sup>1\<close> map \<open>\<phi> :: real \<Rightarrow> real^2\<close> is
  differentiable on the compact interval \<open>{a..b}\<close>, and a differentiable image of a
  set of strictly lower Euclidean dimension is negligible.  Since
  \<open>DIM(real) = 1 < 2 = DIM(real^2)\<close>, @{thm negligible_differentiable_image_lowdim}
  applies directly.  This is the gate that the previous continuous-only definition
  FAILED (a Peano curve has \<open>DIM\<close>-mismatch-free domain but is not differentiable,
  so it cannot pass this gate), confirming the fix is genuine.\<close>

lemma analytic_arc_negligible:
  fixes \<gamma> :: "(real^2) set"
  assumes "analytic_arc \<gamma>"
  shows "negligible \<gamma>"
proof -
  from assms obtain a b \<phi> where ab: "a \<le> b"
    and C1: "\<phi> C1_differentiable_on {a..b}"
    and \<gamma>eq: "\<gamma> = \<phi> ` {a..b}"
    unfolding analytic_arc_def by blast
  have diffat: "\<And>x. x \<in> {a..b} \<Longrightarrow> \<phi> differentiable (at x)"
    using C1 by (simp add: C1_differentiable_on_eq)
  have diffon: "\<phi> differentiable_on {a..b}"
    by (rule differentiable_at_imp_differentiable_on) (rule diffat)
  have dimlt: "DIM(real) < DIM(real^2)"
    by simp
  show ?thesis
    unfolding \<gamma>eq
    by (rule negligible_differentiable_image_lowdim[OF dimlt diffon])
qed


subsection \<open>The curve-confined excess locus and its x-projection (copied verbatim)\<close>

definition BadXW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"


subsection \<open>Structural set algebra for \<open>BadXW\<close> (sorry-free)\<close>

lemma BadXW_empty:
  "BadXW \<omega>0 \<omega>s {} = ({} :: ((real^2)^'n) set)"
  unfolding BadXW_def by blast

lemma BadXW_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "BadXW \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXW \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n) set)"
  using assms unfolding BadXW_def by blast

lemma BadXW_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "BadXW \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)
          = (\<Union>i\<in>I. (BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  unfolding BadXW_def by blast

lemma BadXW_point:
  fixes \<omega> :: "real^2"
  shows "BadXW \<omega>0 \<omega>s {\<omega>}
          = {x :: (real^2)^'n. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
                              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  unfolding BadXW_def by blast


subsection \<open>The per-fixed-angle slice is nowhere dense / meager (sorry-free from \<open>nd\<close>)\<close>

lemma fixed_omega_slice_nowhere_dense:
  fixes \<omega> :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  by (rule nd[OF c0])

lemma fixed_omega_slice_meager:
  fixes \<omega> :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  by (rule meager_nowhere_dense[OF fixed_omega_slice_nowhere_dense[OF c0 nd]])

lemma fixed_omega_proj_meager:
  fixes V :: "((real^2)^'n) set" and \<omega> :: "real^2"
  assumes nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s {\<omega>})"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0")
  case True
  have sub: "(V \<inter> BadXW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)
             \<subseteq> {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    unfolding BadXW_def by blast
  show ?thesis
    by (rule meager_subset[OF sub fixed_omega_slice_meager[OF True nd]])
next
  case False
  hence "(V \<inter> BadXW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set) = {}"
    unfolding BadXW_def by blast
  thus ?thesis by simp
qed


subsection \<open>Degenerate sanity checks: the cut is sound at the extreme instances\<close>

lemma excess_empty_arc_meager:
  fixes V :: "((real^2)^'n) set"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s {} :: ((real^2)^'n) set)"
  by (simp add: BadXW_empty)

lemma excess_point_arc_meager:
  fixes V :: "((real^2)^'n) set" and \<omega> :: "real^2"
  assumes nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)"
  by (rule fixed_omega_proj_meager[OF nd])

lemma excess_finite_arc_meager:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes fin: "finite \<gamma>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
proof -
  have eq: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
              = (\<Union>\<omega>\<in>\<gamma>. V \<inter> BadXW \<omega>0 \<omega>s {\<omega>})"
    unfolding BadXW_def by blast
  have "meager (\<Union>\<omega>\<in>\<gamma>. (V \<inter> BadXW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set))"
    by (rule meager_Union_finite[OF fin]) (rule fixed_omega_proj_meager[OF nd])
  thus ?thesis unfolding eq .
qed


subsection \<open>The irreducible IFT-chart bundle (the single isolated analytic \<open>sorry\<close>)\<close>

text \<open>\<^bold>\<open>The genuine analytic content, isolated as one precisely-scoped statement.\<close>
  Over the (now \<open>C\<^sup>1\<close>) analytic arc \<open>\<gamma> = \<phi> ` {a..b}\<close> the curve-confined
  moment-Jacobian bad fibre \<open>V \<inter> BadXW \<omega>0 \<omega>s \<gamma>\<close> admits a chart bundle in the exact
  shape consumed by @{thm negligible_proj_charts_Nn} / @{thm charts_core_Nn}: a
  COUNTABLE family of charts
  \<open>charts i :: (real^2)^'n \<Rightarrow> ((real^2)^'n \<times> (real^2))\<close> with critical sets \<open>Crit i\<close>
  and blinfun derivatives \<open>D i\<close> such that
  \<^enum> the bad fibre is covered by the \<open>x\<close>-projections \<open>(fst \<circ> charts i) ` Crit i\<close>;
  \<^enum> on each \<open>Crit i\<close> the projection \<open>fst \<circ> charts i\<close> has derivative \<open>D i x\<close>;
  \<^enum> that derivative is NON-surjective on \<open>(real^2)^'n\<close> (codimension \<open>\<ge> 1\<close>); and
  \<^enum> each \<open>x\<close>-projection piece \<open>(fst \<circ> charts i) ` Crit i\<close> is CLOSED.

  ROUTE to discharge (mirrors @{thm parametric_transversality_negligible_complex}
  and @{thm parametric_transversality_meager_planar_config}).  The moment-Jacobian
  rank drop \<open>\<not> surj (DM_paper_x x c)\<close> is, off the per-\<open>\<omega>\<close> nowhere-dense base
  supplied by @{text nd}, a transversality failure of the joint \<open>C\<^sup>1\<close> map
  \<open>(x,\<omega>) \<mapsto> M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)\<close> (joint derivative in \<open>x\<close> from
  @{thm has_derivative_M_paper_x}; in the arc parameter via the now-\<open>C\<^sup>1\<close> map \<open>\<phi>\<close>
  composed with @{thm cvec_dip_higher_differentiable_on}; base-point continuity
  from @{thm continuous_on_DM_paper_x_vec}).  Feed the resulting regular-value
  field into @{thm charts_core_Nn} on each compact sub-arc box.  This is the
  implicit-function-theorem chart of the determinantal locus, the genuine
  multi-week content; it does NOT follow from @{text nd} alone (purely topological
  per fixed \<open>\<omega>\<close>; uncountable unions of nowhere-dense sets need not be meager).
  NOT a splice freebie.\<close>

lemma excess_arc_charts_Nn:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>GENUINE analytic core: the IFT chart of the per-arc moment-Jacobian bad
      fibre in the @{thm charts_core_Nn} output shape (route above).  The single
      irreducible \<open>sorry\<close> of this file; it does NOT follow from @{text nd} alone.
      NOT a splice freebie.\<close>
  sorry


subsection \<open>The analytic core: the closed negligible cover (sorry-free from the chart bundle)\<close>

text \<open>\<^bold>\<open>The closed negligible cover, assembled sorry-free from the chart bundle.\<close>
  From the chart bundle @{thm excess_arc_charts_Nn} the pieces
  \<open>K i = (fst \<circ> charts i) ` (Crit i)\<close> are CLOSED (chart output) and NEGLIGIBLE
  (@{thm negligible_singular_image_2n}: the projection has non-surjective
  derivative on \<open>Crit i\<close>), and they cover the bad fibre.\<close>

lemma excess_arc_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
            (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
          \<and> (\<forall>n. closed (K n))
          \<and> (\<forall>n. negligible (K n))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                    \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using excess_arc_charts_Nn[OF openV Vne c6 arc gsub pf nd]
    by (smt (verit, best))
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have Kcover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
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


subsection \<open>Assembly bridge + the verbatim per-arc target (sorry-free from the core)\<close>

lemma excess_arc_projection_of_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
    and K :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])

lemma excess_arc_projection_meager:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
      and clo: "\<forall>n. closed (K n)"
      and neg: "\<forall>n. negligible (K n)"
    using excess_arc_negligible_closed_cover[OF openV Vne c6 arc gsub pf nd] by blast
  show ?thesis
    by (rule excess_arc_projection_of_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

end
