theory Scratch_m5_indepcore
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) D4 core --- @{text branchP_indep_core}, the deep linear-independence
  rank-drop on the 2-D non-collinear region.\<close>

  This file develops the single genuine analytic core of the Branch-P leaf
  (@{text branchP_indep_core}), copied \<^emph>\<open>verbatim\<close> from
  @{file \<open>../M5_Dev_BranchP/Scratch_m5_branchp.thy\<close>} (the @{text phase_collinear} /
  @{text gamma_par_c} / @{text BadXGW} defs and the lemma @{text branchP_indep_core},
  L245--L259).

  \<^bold>\<open>SOUNDNESS NOTICE.\<close>  The bad set \<open>BadXGW\<close> RETAINS the codimension-giving
  constraints \<open>gradU = 0 \<and> det Dcvec \<noteq> 0\<close>; this is exactly the difference from the
  prior unsound D4 (which dropped \<open>gradU = 0\<close> and fed the engine's bare \<open>BadXW\<close> a
  genuinely 2-D angle region, where per-fibre nowhere-dense slices sweep the whole
  space and meagerness is FALSE).  We never weaken a hypothesis to make a proof go
  through; every helper below is stated soundly and the degenerate extremes are
  sanity-checked.

  \<^bold>\<open>What this file establishes SOUND, sorry-free (the reduction layers).\<close>
  \<^enum> @{text BadXGW_point} / @{text BadXGW_mono} / @{text BadXGW_UN} --- structural
    set algebra for the retained bad \<open>x\<close>-set.
  \<^enum> @{text fixed_omega_branchP_meager} --- per-fixed-angle slice meagerness from the
    abstract @{text nd} input (degenerate "single angle" sanity check, sorry-free).
  \<^enum> @{text branchP_indep_of_negligible_closed_cover} --- \<^bold>\<open>THE ASSEMBLY BRIDGE\<close>: if
    \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> is contained in a COUNTABLE union of CLOSED NEGLIGIBLE
    \<open>x\<close>-pieces, it is meager (sorry-free, via @{thm meager_negligible_closed_cover}).
    This discharges the meagerness \<open>\<Leftarrow>\<close> negligible-cover implication that is the
    structural half of the analytic core.
  \<^enum> @{text branchP_indep_core} --- the verbatim target, assembled sorry-free from a
    SINGLE remaining geometric-measure obligation
    (@{text branchP_indep_negligible_closed_cover}).

  \<^bold>\<open>The single remaining irreducible obligation (ONE scoped MATH sorry).\<close>
  @{text branchP_indep_negligible_closed_cover}: over the linear-independence
  (\<open>\<gamma> \<not>\<parallel> c\<close>) region, the bad \<open>(x,\<omega>)\<close> locus cut by \<open>gradU = 0\<close> (two scalar equations)
  and the moment rank-drop \<open>\<not> surj (DM_paper_x x (cvec \<omega>))\<close> is a \<open>(2N-1)\<close>-dim C1
  graph in \<open>(x,\<omega>)\<close>-space (dimension \<open>2N + 2\<close>); its \<open>x\<close>-projection is NEGLIGIBLE
  (@{thm negligible_singular_image_2n}) and closed-coverable.  This is the genuine
  geometric-measure content (the \<open>(2N-1)\<close>-dim singular image), the EXACT analogue of
  the ArcProj sibling's @{text excess_arc_negligible_closed_cover}: same projection
  machinery, different codimension source (here \<open>gradU = 0\<close> on a 2-D region; there a
  1-D analytic arc).  It does NOT follow from the abstract topological @{text nd}
  alone (which carries no derivative / closedness / joint-regularity data over the
  uncountable angle union), so it is the single isolated \<open>sorry\<close>.
  \<open>freebie_at_splice = false\<close>.\<close>


subsection \<open>The phase-collinear predicate (copied verbatim from BranchP/D34/Engine)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>The retained-constraint bad \<open>x\<close>-set (copied verbatim from BranchP)\<close>

definition BadXGW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXGW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"


subsection \<open>The rank-drop dichotomy predicate \<open>\<gamma> \<parallel> c\<close> (copied verbatim)\<close>

definition gamma_par_c :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow> phase_collinear \<omega>0 \<omega>s \<omega>"

lemma not_gamma_par_c_iff:
  "\<not> gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<forall>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<noteq> t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<and> (\<forall>t. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"
  unfolding gamma_par_c_def phase_collinear_def by blast


subsection \<open>Structural set algebra for \<open>BadXGW\<close> (sorry-free)\<close>

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
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
              \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  unfolding BadXGW_def by blast


subsection \<open>Per-fixed-angle slice meagerness (sorry-free from \<open>nd\<close>)\<close>

text \<open>The degenerate "angle set is a single point" sanity check: the per-angle bad
  slice is contained in the nowhere-dense slice supplied by @{text nd} (when
  \<open>cvec \<noteq> 0\<close>), or empty (when \<open>cvec = 0\<close>), hence meager.  Sorry-free.  This confirms
  the cut at @{text branchP_indep_core} is on the right object: the genuine core
  ADDS exactly the uncountable angle-parameter union beyond this degenerate slice.\<close>

lemma fixed_omega_branchP_meager:
  fixes V :: "((real^2)^'n) set" and \<omega> :: "real^2"
  assumes nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s {\<omega>})"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0")
  case True
  have sub: "(V \<inter> BadXGW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)
             \<subseteq> {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    unfolding BadXGW_def by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_nowhere_dense[OF nd[OF True]]])
next
  case False
  hence "(V \<inter> BadXGW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set) = {}"
    unfolding BadXGW_def by blast
  thus ?thesis by simp
qed

text \<open>Sanity check (a FINITE angle set).  When \<open>\<Gamma>\<close> is finite the bad \<open>x\<close>-set is a
  FINITE union of point slices, hence meager sorry-free --- the angle union is
  harmless for countable \<open>\<Gamma>\<close>.  The genuine difficulty is precisely the UNCOUNTABLE
  2-D region, which is what the analytic core handles.\<close>

lemma branchP_finite_meager:
  fixes V :: "((real^2)^'n) set" and \<Gamma> :: "(real^2) set"
  assumes fin: "finite \<Gamma>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
proof -
  have eq: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
              = (\<Union>\<omega>\<in>\<Gamma>. V \<inter> BadXGW \<omega>0 \<omega>s {\<omega>})"
    unfolding BadXGW_def by blast
  have "meager (\<Union>\<omega>\<in>\<Gamma>. (V \<inter> BadXGW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set))"
    by (rule meager_Union_finite[OF fin]) (rule fixed_omega_branchP_meager[OF nd])
  thus ?thesis unfolding eq .
qed


subsection \<open>Assembly bridge: closed negligible countable cover \<open>\<Longrightarrow>\<close> meager (sorry-free)\<close>

text \<open>\<^bold>\<open>The assembly bridge (sorry-free).\<close>  If the bad \<open>x\<close>-set over the angle region
  is contained in a COUNTABLE union of CLOSED NEGLIGIBLE \<open>x\<close>-sets, it is meager.
  This is the structural fact that turns the geometric-measure output of the core
  (the negligible \<open>x\<close>-projection of the \<open>(2N-1)\<close>-dim graph) into the @{const meager}
  conclusion, via @{thm meager_negligible_closed_cover}.  Mirrors the ArcProj
  sibling's @{text excess_arc_projection_of_negligible_closed_cover}.\<close>

lemma branchP_indep_of_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<Gamma> :: "(real^2) set"
    and K :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])


subsection \<open>The single isolated geometric-measure obligation: the closed negligible cover\<close>

text \<open>\<^bold>\<open>GENUINE geometric-measure core (the irreducible content of D4).\<close>  Over the
  linear-independence (\<open>\<gamma> \<not>\<parallel> c\<close>) region \<open>\<Gamma> \<subseteq> OmegaPF\<close>, the retained-constraint bad
  \<open>x\<close>-projection \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> is contained in a COUNTABLE union of CLOSED
  NEGLIGIBLE \<open>x\<close>-sets.

  ROUTE (the linear-independence rank-drop + negligible projection).  On \<open>\<gamma> \<not>\<parallel> c\<close>
  (@{thm not_gamma_par_c_iff}), the pair \<open>\<gamma> = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)\<close>,
  \<open>c = cvec_dip \<omega>0 \<omega>s \<omega>\<close> is linearly independent; together with \<open>det Dcvec \<noteq> 0\<close>
  the steering map is a local diffeomorphism in \<open>\<omega>\<close> (the @{const gradU}
  has-derivative bridges + the @{const DM_paper_x} Jacobian).  The bad \<open>(x,\<omega>)\<close>
  locus is cut by \<open>gradU = 0\<close> (two scalar equations) and the moment rank-drop
  \<open>\<not> surj (DM_paper_x x (cvec \<omega>))\<close> (codim \<open>\<ge> 1\<close> in \<open>x\<close> off the nowhere-dense base
  supplied by @{text nd}); net dimension \<open>\<le> 2N + 2 - 3 = 2N - 1\<close>.  \<open>core_3d\<close> is
  ruled out structurally because the \<open>gradU\<close> rows degenerate exactly at the residual
  witnesses, so the \<open>x\<close>-projection of the \<open>(2N-1)\<close>-dim graph is NEGLIGIBLE
  (@{thm negligible_singular_image_2n}) and closed-coverable.  Mirror the
  flatten / conjugate / pullback skeleton of
  @{thm parametric_transversality_meager_planar_config} and the negligible-image
  charts of @{thm negligible_singular_image_2n}.

  \<^bold>\<open>Why irreducible from the given hypotheses.\<close>  The abstract input @{text nd} gives
  only per-fixed-\<open>\<omega>\<close> topological nowhere-density (no derivative, no closedness, no
  joint regularity in \<open>(x,\<omega>)\<close>).  The passage from the per-\<open>\<omega>\<close> nowhere-dense slices to
  meagerness of the UNCOUNTABLE 2-D angle union is exactly the IFT / negligible-
  projection content of the source paper; uncountable unions of nowhere-dense sets
  need not be meager, so it is NOT a consequence of @{text nd} alone.  This is the
  EXACT analogue of the ArcProj sibling core (same projection machinery; the
  codimension source is \<open>gradU = 0\<close> on a 2-D region here, a 1-D analytic arc there),
  and the single isolated \<open>sorry\<close> of this file.  NOT a splice freebie.\<close>

lemma branchP_indep_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
            (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
          \<and> (\<forall>n. closed (K n))
          \<and> (\<forall>n. negligible (K n))"
  \<comment> \<open>GENUINE geometric-measure core: the linear-independence rank-drop cut of the
      bad \<open>(x,\<omega>)\<close> locus as a \<open>(2N-1)\<close>-dim graph (@{thm negligible_singular_image_2n}),
      presented as a countable closed negligible \<open>x\<close>-cover.  Route above.  This is
      the deepest core of D4 and the single irreducible \<open>sorry\<close> of this file; it does
      NOT follow from @{text nd} alone.  NOT a splice freebie.\<close>
  sorry


subsection \<open>The verbatim target @{text branchP_indep_core}, assembled from the core\<close>

text \<open>\<^bold>\<open>The genuine NEW Branch-P core.\<close>  Copied \<^bold>\<open>verbatim\<close> from
  @{file \<open>../M5_Dev_BranchP/Scratch_m5_branchp.thy\<close>} (L245--L259).  Assembled
  sorry-free from the single isolated geometric-measure obligation
  @{text branchP_indep_negligible_closed_cover} via the sorry-free assembly bridge
  @{text branchP_indep_of_negligible_closed_cover}.\<close>

lemma branchP_indep_core:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
      and clo: "\<forall>n. closed (K n)"
      and neg: "\<forall>n. negligible (K n)"
    using branchP_indep_negligible_closed_cover[OF openV Vne c6 d0 pf Gsub Gindep nd]
    by blast
  show ?thesis
    by (rule branchP_indep_of_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

end
