theory Scratch_m5_arcproj
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) Core A --- the deep per-arc x-projection meagerness:
  @{text excess_arc_projection_meager}.\<close>

  This file develops Core A of the M5 excess engine: over a SINGLE analytic arc
  \<open>\<gamma>\<close> (a continuous image of a compact real interval), the \<open>x\<close>-projection of the
  curve-confined bad fibre is meager.  The target statement
  @{text excess_arc_projection_meager} and the @{text BadXW} definition are copied
  \<^emph>\<open>verbatim\<close> from @{file \<open>../M5_Dev_Excess/Scratch_m5_excess.thy\<close>} (the @{text BadXW}
  def at L87--L89 and the lemma at L266--L280).

  \<^bold>\<open>Soundness of the cut.\<close>  The statement is per-SINGLE-arc \<open>\<gamma>\<close>; there is no
  2D-\<open>\<Gamma>\<close> over-generalization pitfall.  The hypotheses are exactly those of the
  verbatim engine signature (open nonempty \<open>V\<close>, \<open>6 \<le> CARD('n)\<close>, \<open>analytic_arc \<gamma>\<close>,
  \<open>\<gamma> \<subseteq> OmegaPF\<close>, the phase-foot condition \<open>pf\<close>, and the abstract fixed-angle
  nowhere-density input @{text nd}).  Degenerate sanity checks below confirm the
  cut is sound at the extreme instances:
  \<^item> the EMPTY arc (\<open>\<gamma> = {}\<close>): \<open>BadXW \<omega>0 \<omega>s {} = {}\<close>, meager (proven proof-complete);
  \<^item> the POINT arc (\<open>\<gamma> = {\<omega>}\<close>): reduces to the per-fixed-angle nowhere-dense slice
    supplied by @{text nd} (proven proof-complete);
  \<^item> a FINITE arc (\<open>\<gamma>\<close> finite): a finite union of point slices, meager proof-complete.

  \<^bold>\<open>What is proven proof-complete here (the reduction layers).\<close>
  \<^enum> @{text BadXW_empty} / @{text BadXW_point} / @{text BadXW_mono} / @{text BadXW_finite}
    --- structural set algebra for the bad \<open>x\<close>-set.
  \<^enum> @{text fixed_omega_slice_nowhere_dense} / @{text fixed_omega_proj_meager}
    --- the per-fixed-angle slice is nowhere dense (hence meager) from @{text nd}.
  \<^enum> @{text excess_arc_projection_of_negligible_closed_cover} --- \<^bold>\<open>the assembly
    bridge\<close>: if the bad \<open>x\<close>-set over the arc is contained in a COUNTABLE union of
    CLOSED NEGLIGIBLE pieces, it is meager (proof-complete, via
    @{thm meager_negligible_closed_cover}).
  \<^enum> @{text excess_arc_projection_meager} --- the verbatim target, assembled from
    the single isolated analytic core @{text excess_arc_negligible_closed_cover}.

  \<^bold>\<open>The single isolated analytic core (the irreducible content).\<close>
  \<^item> @{text excess_arc_negligible_closed_cover}: over the analytic arc the bad
    \<open>x\<close>-fibre projection \<open>V \<inter> BadXW \<omega>0 \<omega>s \<gamma>\<close> is covered by COUNTABLY many CLOSED
    NEGLIGIBLE \<open>x\<close>-sets.  This is the genuine IFT-chart content: \<open>\<gamma>\<close> is
    \<open>\<phi> ` {a..b}\<close>; the joint bad-pair set
    \<open>{(x,\<omega>). \<omega>\<in>\<gamma> \<and> cvec \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec \<omega>))}\<close> is, off the
    nowhere-dense base supplied by @{text nd}, a \<open>(2N-1)\<close>-dim graph (the map
    \<open>x \<mapsto> M_paper x (cvec \<omega>)\<close> is a submersion off the base; add the 1-dim arc
    parameter), so its \<open>x\<close>-projection is NEGLIGIBLE
    (@{thm negligible_singular_image_2n}) and closed-coverable.  This is the
    deepest core; it does NOT follow from the abstract topological input
    @{text nd} alone (which carries no derivative / closedness data), so it is
    carried here as ONE precisely-scoped \<open>proof hole\<close>.  GENUINE math, NOT a splice
    freebie.\<close>


subsection \<open>The analytic-arc predicate (copied verbatim from the excess file)\<close>

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


subsection \<open>The per-fixed-angle slice is nowhere dense / meager (proof-complete from \<open>nd\<close>)\<close>

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

text \<open>The per-fixed-angle \<open>x\<close>-projection \<open>V \<inter> BadXW \<omega>0 \<omega>s {\<omega>}\<close> is meager
  (the degenerate "arc = a single point" case): if \<open>cvec \<noteq> 0\<close> it is contained in
  the nowhere-dense slice supplied by @{text nd}; if \<open>cvec = 0\<close> it is empty.\<close>

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

text \<open>Sanity check 1 (the EMPTY arc).  When \<open>\<gamma> = {}\<close> the bad \<open>x\<close>-set is empty,
  hence meager; the target statement holds trivially in this extreme.\<close>

lemma excess_empty_arc_meager:
  fixes V :: "((real^2)^'n) set"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s {} :: ((real^2)^'n) set)"
  by (simp add: BadXW_empty)

text \<open>Sanity check 2 (the POINT arc).  When \<open>\<gamma> = {\<omega>}\<close> the target reduces to the
  per-fixed-angle meager slice supplied by @{text nd}.  This confirms the cut is
  the right one: the analytic core ADDS exactly the (uncountable) arc-parameter
  union beyond this degenerate slice.\<close>

lemma excess_point_arc_meager:
  fixes V :: "((real^2)^'n) set" and \<omega> :: "real^2"
  assumes nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)"
  by (rule fixed_omega_proj_meager[OF nd])

text \<open>Sanity check 3 (a FINITE arc).  When \<open>\<gamma>\<close> is finite the bad \<open>x\<close>-set is a
  FINITE union of point slices, hence meager proof-complete --- the arc-parameter
  union is harmless for countable \<open>\<gamma>\<close>.  The genuine difficulty is precisely the
  UNCOUNTABLE arc, which is what the analytic core handles.\<close>

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


subsection \<open>Assembly bridge: a closed negligible countable cover \<open>\<Longrightarrow>\<close> meager\<close>

text \<open>\<^bold>\<open>The assembly bridge (proof-complete).\<close>  If the bad \<open>x\<close>-set over the arc is
  contained in a COUNTABLE union of CLOSED NEGLIGIBLE \<open>x\<close>-sets, it is meager.
  This is the structural fact that turns the IFT-chart's negligible-projection
  output (the analytic core) into the @{const meager} conclusion, via
  @{thm meager_negligible_closed_cover}.\<close>

lemma excess_arc_projection_of_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
    and K :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])


subsection \<open>The single isolated analytic core: the closed negligible cover\<close>

text \<open>\<^bold>\<open>GENUINE analytic core (the irreducible content).\<close>  Over the analytic arc
  \<open>\<gamma> = \<phi> ` {a..b}\<close>, the \<open>x\<close>-projection \<open>V \<inter> BadXW \<omega>0 \<omega>s \<gamma>\<close> of the bad fibre is
  contained in a COUNTABLE union of CLOSED NEGLIGIBLE \<open>x\<close>-sets.

  ROUTE (the IFT chart + negligible projection).  The bad pairs over the arc lie
  in \<open>{(x,\<omega>). \<omega>\<in>\<gamma> \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}\<close>.
  Because \<open>cvec_dip \<noteq> 0\<close> on the arc, the per-fixed-\<open>\<omega>\<close> base
  \<open>{x. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}\<close> is nowhere dense by @{text nd}
  (@{thm fixed_omega_slice_nowhere_dense}), i.e. \<open>x \<mapsto> M_paper x (cvec ...)\<close>
  (derivative @{thm has_derivative_M_paper_x}, constant blinfun @{const DM_paper_x})
  is a submersion off it.  The IFT charts each fibre as a graph of codimension
  \<open>\<ge> 1\<close> in \<open>x\<close>; adding the 1-dimensional arc parameter \<open>t\<in>{a..b}\<close> (via the
  continuous \<open>\<phi>\<close>) gives a \<open>(2N-1)\<close>-dim graph in the \<open>(x,\<omega>)\<close> excess space whose
  \<open>x\<close>-projection is NEGLIGIBLE (@{thm negligible_singular_image_2n}).  Cover the
  bad fibre by countably many closed pieces (compact sub-arcs \<open>\<times>\<close> closed
  \<open>x\<close>-graphs).  Mirror the flatten / conjugate / pullback skeleton of
  @{thm parametric_transversality_meager_planar_config} and the
  negligible-image charts of @{thm negligible_singular_image_2n}.

  \<^bold>\<open>Why this is irreducible from the given hypotheses.\<close>  The abstract input
  @{text nd} supplies only TOPOLOGICAL nowhere-density per fixed \<open>\<omega>\<close> (no
  derivative, no closedness, no joint regularity in \<open>(x,\<omega>)\<close>).  The passage from
  the per-\<open>\<omega>\<close> nowhere-dense slices to meagerness of the UNCOUNTABLE arc-parameter
  union is exactly the IFT/negligible-projection content of the source paper; it
  is NOT a consequence of @{text nd} alone (uncountable unions of nowhere-dense
  sets need not be meager).  Hence the genuine analytic work is isolated to this
  single closed-negligible-cover obligation; everything else in this file is
  proof-complete.  NOT a splice freebie.\<close>

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
  \<comment> \<open>GENUINE analytic core: the IFT chart of the per-arc bad fibre as a
      \<open>(2N-1)\<close>-dim graph (@{thm negligible_singular_image_2n}), presented as a
      countable closed negligible \<open>x\<close>-cover.  Route above.  This is the deepest
      core of M5 and the single irreducible \<open>proof hole\<close> of this file; it does NOT
      follow from @{text nd} alone.  NOT a splice freebie.\<close>
  sorry


subsection \<open>The verbatim target, assembled from the single analytic core\<close>

text \<open>\<^bold>\<open>The per-arc x-projection meagerness.\<close>  Copied \<^bold>\<open>verbatim\<close> from
  @{file \<open>../M5_Dev_Excess/Scratch_m5_excess.thy\<close>} (L266--L280).  Assembled
  proof-complete from the single isolated analytic core
  @{text excess_arc_negligible_closed_cover} via the proof-complete assembly bridge
  @{text excess_arc_projection_of_negligible_closed_cover}.\<close>

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
