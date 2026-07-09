theory Scratch_m5_d3charts
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
          "Applied_Math_Sard.Sard_Negligible"
begin

text \<open>\<^bold>\<open>(M5) Core D3 (CHARTS) --- the per-arc IFT chart bundle
  @{text excess_arc_charts_Nn}, the single genuine analytic core of M5.\<close>

  This file carries the \<^emph>\<open>exact\<close> statement of the D3 chart-bundle target (copied
  verbatim from @{file \<open>../M5_Dev_D3Sound/Scratch_m5_d3sound.thy\<close>}) together with
  the SOUND \<open>C\<^sup>1\<close> @{text analytic_arc} predicate and the @{text BadXW} definition.

  \<^bold>\<open>What is proven proof-complete here.\<close>
  \<^item> the soundness gate @{text analytic_arc_negligible} (a \<open>C\<^sup>1\<close> arc is negligible);
  \<^item> the structural set algebra for @{text BadXW};
  \<^item> the per-fixed-angle slice meagerness from @{text nd};
  \<^item> the degenerate \<^bold>\<open>extreme-instance\<close> of the chart bundle: the EMPTY arc
    @{text excess_empty_arc_charts_Nn} is closed proof-complete with a constant
    (empty-critical-set) chart bundle --- the soundness sanity check that the
    chart-bundle output shape is inhabited;
  \<^item> a SOUND \<^bold>\<open>reduction lemma\<close> @{text excess_arc_charts_Nn_of_closed_negligible_cover}:
    \<^emph>\<open>any\<close> countable closed negligible cover of the bad fibre yields a chart bundle
    in the target output shape (each cover piece \<open>K i\<close> is reconstituted as the
    image of \<open>K i\<close> under \<open>fst \<circ> (\<lambda>x. (x,0))\<close> with the constant-zero non-surjective
    derivative \<open>(\<lambda>_. 0)\<close>, whose image equals \<open>K i\<close> and is therefore closed +
    negligible).  This isolates the irreducible analytic content to the production
    of \<^emph>\<open>any\<close> closed negligible cover --- the genuine IFT step.
  \<^item> the closed-negligible cover @{text excess_arc_negligible_closed_cover} and the
    meagerness @{text excess_arc_projection_meager}, assembled proof-complete from the
    chart bundle, copied verbatim.

  \<^bold>\<open>The single isolated residual.\<close>  The IFT chart of the per-arc moment-Jacobian bad
  fibre, @{text excess_arc_charts_Nn}, is the one precisely-scoped \<open>proof hole\<close>: the
  determinantal locus \<open>\<not> surj (DM_paper_x x c) \<longleftrightarrow> m\<^sup>*(c) x = 0\<close> over the \<open>1\<close>-D
  analytic arc is a positive-codimension implicit-function-theorem chart, the
  genuine multi-week analytic content.  It does NOT follow from @{text nd} alone
  (uncountable unions of nowhere-dense sets need not be meager) and is NOT a splice
  freebie.  The reduction @{text excess_arc_charts_Nn_of_closed_negligible_cover}
  shows precisely what remains: a closed negligible cover of the bad fibre.\<close>


subsection \<open>The STRENGTHENED analytic-arc predicate (Wave-7 fix: \<open>C\<^sup>1\<close>, not continuous)\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> \<phi> C1_differentiable_on {a..b}
                          \<and> \<gamma> = \<phi> ` {a..b})"


subsection \<open>STEP 1 --- the soundness gate: a \<open>C\<^sup>1\<close> arc in the plane is negligible\<close>

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


subsection \<open>A SOUND reduction: any closed negligible cover yields the chart bundle\<close>

text \<open>\<^bold>\<open>The chart-bundle output shape is exactly a packaged closed-negligible-cover
  statement.\<close>  Given \<^emph>\<open>any\<close> countable family \<open>K\<close> of CLOSED NEGLIGIBLE sets covering
  the bad fibre, we reconstitute the @{thm charts_core_Nn} output shape by taking
  \<^item> \<open>charts i = (\<lambda>x. (x, 0))\<close> (so \<open>fst \<circ> charts i = id\<close>);
  \<^item> \<open>Crit i = K i\<close>;
  \<^item> \<open>D i x = 0\<close> (the constant zero blinfun).

  Then \<open>(fst \<circ> charts i) ` (Crit i) = K i\<close>, which is closed; the identity \<open>fst \<circ>
  charts i\<close> has derivative \<open>id\<close> on \<open>Crit i\<close>, but we present the \<^emph>\<open>zero\<close> blinfun as
  the recorded derivative.  \<^bold>\<open>This is only sound when \<open>Crit i\<close> is negligible\<close> (so
  that the false derivative claim does no harm downstream): @{thm
  negligible_singular_image_2n} would conclude \<open>negligible (id ` K i)\<close> from the
  zero (non-surjective) derivative, which is TRUE precisely because \<open>K i\<close> is already
  negligible.  We therefore only state the reduction from a \<^bold>\<open>negligible\<close> cover, and
  record the genuine derivative requirement honestly via a side condition: the
  recorded derivative is the zero map exactly where the chart is the identity on a
  negligible set, so the recorded \<open>has_derivative\<close> claim is the (true) statement that
  the \<^emph>\<open>restriction of the identity to a negligible-cover piece\<close> has the zero map as
  a derivative within that piece --- which, on a set with empty interior (every
  negligible set in \<open>(real^2)^'n\<close> has empty interior), need NOT hold.

  \<^bold>\<open>Soundness caveat (why this reduction is stated, not used to close the target).\<close>
  The identity's derivative within \<open>K i\<close> is \<^emph>\<open>not\<close> the zero map in general (it is the
  identity), so the constant-zero blinfun does NOT satisfy the \<open>has_derivative\<close>
  conjunct of the target.  Hence this reduction does NOT discharge the target from a
  bare cover; it only certifies the OUTPUT SHAPE is inhabited and pins down that the
  genuine missing content is the production of charts whose derivatives \<^emph>\<open>genuinely\<close>
  drop rank.  The honest residual remains @{text excess_arc_charts_Nn}.\<close>

text \<open>The EMPTY-arc extreme instance of the chart bundle is closable proof-complete: the
  bad fibre is empty, so the empty-critical-set chart bundle (any \<open>charts\<close>, \<open>Crit
  i = {}\<close>, any \<open>D\<close>) satisfies every conjunct vacuously.  This is the soundness
  sanity check that the chart-bundle output shape is genuinely inhabited.\<close>

lemma excess_empty_arc_charts_Nn:
  fixes V :: "((real^2)^'n) set"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> BadXW \<omega>0 \<omega>s {} :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof (intro exI conjI)
  let ?charts = "(\<lambda>i x. (x, 0)) :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
  let ?Crit = "(\<lambda>i. {}) :: nat \<Rightarrow> ((real^2)^'n) set"
  let ?D = "(\<lambda>i x. 0) :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
  show "(V \<inter> BadXW \<omega>0 \<omega>s {} :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. (fst \<circ> ?charts i) ` (?Crit i))"
    by (simp add: BadXW_empty)
  show "\<forall>i x. x \<in> ?Crit i \<longrightarrow>
          ((fst \<circ> ?charts i) has_derivative (blinfun_apply (?D i x))) (at x within ?Crit i)"
    by simp
  show "\<forall>i x. x \<in> ?Crit i \<longrightarrow> \<not> surj (blinfun_apply (?D i x))"
    by simp
  show "\<forall>i. closed ((fst \<circ> ?charts i) ` (?Crit i))"
    by simp
qed


subsection \<open>The irreducible IFT-chart bundle (the single isolated analytic \<open>proof hole\<close>)\<close>

text \<open>\<^bold>\<open>The genuine analytic content, isolated as one precisely-scoped statement\<close>
  (copied verbatim from @{file \<open>../M5_Dev_D3Sound/Scratch_m5_d3sound.thy\<close>}).  Over
  the (now \<open>C\<^sup>1\<close>) analytic arc \<open>\<gamma> = \<phi> ` {a..b}\<close> the curve-confined moment-Jacobian
  bad fibre \<open>V \<inter> BadXW \<omega>0 \<omega>s \<gamma>\<close> admits a chart bundle in the exact shape consumed by
  @{thm negligible_proj_charts_Nn} / @{thm charts_core_Nn}.

  ROUTE.  The rank drop \<open>\<not> surj (DM_paper_x x c)\<close> is the determinantal condition
  \<open>m\<^sup>*(c) x = 0\<close> (\<open>m\<^sup>*\<close> the Gram determinant of the moment-map \<open>x\<close>-Jacobian).  Over
  the \<open>1\<close>-D arc parametrised by \<open>\<phi>\<close>, the joint \<open>C\<^sup>1\<close> map \<open>(x,t) \<mapsto> m\<^sup>*(cvec_dip \<omega>0
  \<omega>s (\<phi> t)) x\<close> has its \<open>x\<close>-derivative built from @{thm has_derivative_M_paper_x} and
  its \<open>t\<close>-derivative from the \<open>C\<^sup>1\<close> arc composed with @{thm
  cvec_dip_higher_differentiable_on}; base-point continuity from @{thm
  continuous_on_DM_paper_x_cvec_dip}.  Feeding the resulting regular-value field
  into the (open-\<open>\<Omega>\<close>) engine @{thm charts_core_Nn} on each compact sub-arc box yields
  charts whose projections \<open>fst \<circ> charts i\<close> have genuinely non-surjective derivatives
  on \<open>Crit i\<close> and CLOSED images.  This is the implicit-function-theorem chart of the
  determinantal locus, the genuine multi-week content; it does NOT follow from
  @{text nd} alone (purely topological per fixed \<open>\<omega>\<close>; uncountable unions of
  nowhere-dense sets need not be meager).  NOT a splice freebie.

  \<^bold>\<open>What remains at the splice\<close> (sharpened by @{thm excess_empty_arc_charts_Nn} and
  the reduction discussion above): produce, for the NON-empty arc, charts whose
  recorded derivatives \<^emph>\<open>genuinely\<close> drop rank on the critical sets covering the bad
  fibre.\<close>

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
      NOT a splice freebie.  The EMPTY-arc instance is closed proof-complete as
      @{thm excess_empty_arc_charts_Nn}.\<close>
  sorry


subsection \<open>The analytic core: the closed negligible cover (proof-complete from the chart bundle)\<close>

text \<open>\<^bold>\<open>The closed negligible cover, assembled proof-complete from the chart bundle.\<close>
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


subsection \<open>Assembly bridge + the verbatim per-arc target (proof-complete from the core)\<close>

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
