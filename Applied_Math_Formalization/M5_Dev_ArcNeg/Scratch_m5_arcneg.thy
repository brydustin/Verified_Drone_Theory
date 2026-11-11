theory Scratch_m5_arcneg
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) Core D3 --- the deep per-arc x-projection closed-negligible cover:
  @{text excess_arc_negligible_closed_cover}.\<close>

  This file isolates the GENUINE analytic core of the M5 excess engine that the
  reduction file @{file \<open>../M5_Dev_ArcProj/Scratch_m5_arcproj.thy\<close>} carries as its
  single irreducible \<open>proof hole\<close>: over a single analytic arc \<open>\<gamma> = \<phi> ` {a..b}\<close>, the
  \<open>x\<close>-projection of the curve-confined bad fibre \<open>V \<inter> BadXW \<omega>0 \<omega>s \<gamma>\<close> is covered by
  countably many CLOSED NEGLIGIBLE \<open>x\<close>-sets.

  All set-algebra / reduction / assembly layers are reproduced proof-complete
  (copied verbatim from the reduction file).  The single isolated analytic content
  is the closed-negligible-cover obligation, which we reduce as far as is
  legitimately possible to the irreducible implicit-function-theorem chart step.

  \<^bold>\<open>The heap workhorses this reduces to.\<close>
  \<^item> @{thm negligible_singular_image_2n}: if \<open>f :: (real^2)^'n \<Rightarrow> (real^2)^'n\<close> has,
    at every point of \<open>S\<close>, a NON-surjective derivative \<open>f' x\<close>, then \<open>f ` S\<close> is
    NEGLIGIBLE.  (The \<open>2N\<close>-dim flatten / baby-Sard / Lipschitz-image engine.)
  \<^item> @{thm negligible_proj_charts_Nn}: the packaged consequence --- a COUNTABLE family
    of charts \<open>charts i :: (real^2)^'n \<Rightarrow> ((real^2)^'n \<times> (real^2))\<close> with critical
    sets \<open>Crit i\<close> on which \<open>fst \<circ> charts i\<close> has non-surjective derivative gives a
    NEGLIGIBLE union \<open>\<Union>i. (fst \<circ> charts i) ` Crit i\<close>.
  \<^item> @{thm meager_negligible_closed_cover}: a countable closed negligible cover is
    meager (the bridge consumed by the reduction file).
  \<^item> @{thm has_derivative_M_paper_x} / @{const DM_paper_x} /
    @{thm continuous_on_DM_paper_x_vec}: the joint-\<open>C\<^sup>1\<close> moment-map data.
  \<^item> @{thm cvec_dip_higher_differentiable_on}: the steering map along the arc is
    \<open>C\<^sup>\<infinity>\<close>, hence the joint map \<open>(x,t) \<mapsto> M_paper x (cvec_dip \<omega>0 \<omega>s (\<phi> t))\<close> is
    jointly \<open>C\<^sup>1\<close>.

  \<^bold>\<open>Soundness of the cut.\<close>  The target statement is copied VERBATIM (hypotheses
  and conclusion) from the reduction file.  The degenerate sanity checks of the
  reduction file (empty / point / finite arc) already confirm the statement is
  true at those extremes; the genuine content is the UNCOUNTABLE arc, for which
  the closed-negligible cover is constructed via the IFT chart of the per-arc bad
  fibre as a lower-dimensional \<open>C\<^sup>1\<close> image whose \<open>x\<close>-projection is negligible.\<close>


subsection \<open>The analytic-arc predicate (copied verbatim)\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> continuous_on {a..b} \<phi>
                          \<and> \<gamma> = \<phi> ` {a..b})"


subsection \<open>The curve-confined excess locus and its x-projection (copied verbatim)\<close>

definition BadXW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"


subsection \<open>Structural set algebra for \<open>BadXW\<close> (proof-complete)\<close>

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


subsection \<open>The irreducible IFT-chart bundle (the single isolated analytic \<open>proof hole\<close>)\<close>

text \<open>\<^bold>\<open>The genuine analytic content, isolated as one precisely-scoped statement.\<close>
  Over the analytic arc \<open>\<gamma> = \<phi> ` {a..b}\<close> the curve-confined moment-Jacobian bad
  fibre \<open>V \<inter> BadXW \<omega>0 \<omega>s \<gamma>\<close> admits a chart bundle in the exact shape consumed by
  @{thm negligible_proj_charts_Nn}: a COUNTABLE family of charts
  \<open>charts i :: (real^2)^'n \<Rightarrow> ((real^2)^'n \<times> (real^2))\<close> with critical sets \<open>Crit i\<close>
  and blinfun derivatives \<open>D i\<close> such that
  \<^enum> the bad fibre is covered by the \<open>x\<close>-projections \<open>(fst \<circ> charts i) ` Crit i\<close>;
  \<^enum> on each \<open>Crit i\<close> the projection \<open>fst \<circ> charts i\<close> has derivative \<open>D i x\<close>;
  \<^enum> that derivative is NON-surjective on \<open>(real^2)^'n\<close> (the codimension \<open>\<ge> 1\<close>
    rank drop), and
  \<^enum> each \<open>x\<close>-projection piece \<open>(fst \<circ> charts i) ` Crit i\<close> is CLOSED.

  This is EXACTLY the output shape of the heap engine @{thm charts_core_Nn} (the
  bad-zero / @{const bad_zero_chart} IFT construction): bad-pair set is the
  \<open>fst\<close>-projection of bad zeros, each charted as a graph of the kernel of the
  regular-value derivative, with the projection's derivative non-surjective and the
  chart image closed.

  ROUTE to discharge this \<open>proof hole\<close> (mirrors @{thm parametric_transversality_negligible_complex}).
  The moment-Jacobian rank drop \<open>\<not> surj (DM_paper_x x c)\<close> is, off the per-\<open>\<omega>\<close>
  nowhere-dense base supplied by @{text nd}, a transversality failure of the joint
  \<open>C\<^sup>1\<close> map \<open>(x,\<omega>) \<mapsto> M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)\<close> (joint derivative from
  @{thm has_derivative_M_paper_x} in \<open>x\<close>, @{thm cvec_dip_higher_differentiable_on}
  composed with the continuous arc map \<open>\<phi>\<close> in the arc parameter; base-point
  continuity from @{thm continuous_on_DM_paper_x_vec}); feed the resulting
  regular-value field into @{thm charts_core_Nn} on each compact sub-arc box.  This
  is the implicit-function-theorem chart of the determinantal locus and the genuine
  multi-week content; it does NOT follow from @{text nd} alone (which is purely
  topological per fixed \<open>\<omega>\<close>, with no derivative / closedness / joint-regularity
  data, and uncountable unions of nowhere-dense sets need not be meager).
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
      irreducible \<open>proof hole\<close> of this file; it does NOT follow from @{text nd} alone.
      NOT a splice freebie.\<close>
  sorry


subsection \<open>The analytic core: the closed negligible cover (proof-complete from the chart bundle)\<close>

text \<open>\<^bold>\<open>The closed negligible cover, assembled proof-complete from the chart bundle.\<close>
  From the chart bundle @{thm excess_arc_charts_Nn} the pieces
  \<open>K i = (fst \<circ> charts i) ` (Crit i)\<close> are CLOSED (chart output) and NEGLIGIBLE
  (@{thm negligible_singular_image_2n}: the projection has non-surjective derivative
  on \<open>Crit i\<close>), and they cover the bad fibre.  This turns the IFT-chart content into
  the countable closed negligible cover the reduction layer consumes.\<close>

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
    using excess_arc_charts_Nn[OF openV Vne c6 arc gsub pf nd] by blast
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


subsection \<open>The verbatim per-arc target, assembled from the analytic core (proof-complete)\<close>

text \<open>The two proof-complete layers consumed downstream (copied verbatim from the
  reduction file) confirm the cut is at the right place: the closed-negligible
  cover yields meagerness without further analytic work.\<close>

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
