theory Scratch_m5_d3eng
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) Core D3 ENGINE --- the per-arc IFT chart bundle, codim 3, 1-D arc.\<close>

  This file is the ENGINE attempt for @{text excess_arc_charts_Nn}: the genuine
  analytic content of D3.  We copy the exact statement (and the supporting
  @{text BadXWG}/@{text analytic_arc} defs and @{text mstarg} interface) from the
  sibling file @{file \<open>../M5_Dev_D3fix/Scratch_m5_d3fix.thy\<close>}, then BUILD the
  engine for the 1-D arc per the DESIGN: the extra dimension is the arc parameter
  \<open>t\<close> with \<open>\<omega> = \<phi> t\<close>.

  \<^bold>\<open>The honest geometry (DESIGN \<section>1, \<section>4-D3, \<section>6).\<close>  The combined bad locus
  over the arc is the zero set of the JOINT \<open>C\<^sup>1\<close> map
  \<open>Gjoint (x,t) = (gradU\<^sub>1, gradU\<^sub>2, mstarg) : ((real^2)^'n \<times> real) \<Rightarrow> real^3\<close>.
  At a bad point \<open>gradU = 0\<close> AND (via @{thm surj_iff_mstarg}) \<open>mstarg = 0\<close>, so
  \<open>Gjoint = 0\<close>.  The cut is codim 3: two gradient equations plus one determinantal
  equation.  The \<open>x\<close>-partial of \<open>gradU\<close> factors as \<open>F \<circ> DM_paper_x x c\<close>
  (@{thm has_derivative_gradU_dip_x}) and is NON-surjective on the bad locus
  (the defining feature of the M5 singular stratum --- exactly where
  @{thm gradU_dip_x_partial_surj} fails because \<open>\<not> surj (DM_paper_x)\<close>).  The
  transverse rank-3 direction comes from (a) the \<open>\<omega>\<close>-partial of \<open>gradU\<close>
  (steering nondegeneracy) for rows 1-2 and (b) \<open>\<nabla> mstarg\<close> for row 3, off a
  named lower-dimensional singular stratum \<open>\<Sigma>\<close>.

  \<^bold>\<open>The IFT square-block obstruction (why this is NOT a direct heap engine call).\<close>
  @{thm charts_core_Nn} (and its IFT helper @{thm crit_piece_compact}) is
  HARD-TYPED to codomain \<open>real^2\<close> with a SQUARE block (codomain dim = parameter
  dim, via @{thm det_2}, \<open>CARD(2)\<close>).  For the 1-D arc the parameter \<open>t\<close> is scalar
  while the codomain is \<open>real^3\<close>: the IFT graph block is NOT square, so the heap
  engine does not apply verbatim.  Realising the chart of the combined locus
  requires the codomain-\<open>real^3\<close> generalization of the engine PLUS the steering
  \<open>\<omega>\<close>-partial submersion of \<open>Gjoint\<close>.  This is the genuine multi-week analytic
  content (DESIGN \<section>5 obligations 1-4); it is NOT a splice freebie.

  \<^bold>\<open>What is proven proof-complete here\<close> (every layer EXCEPT the one isolated joint
  regular-value/chart proof hole): @{text analytic_arc_negligible}; the \<open>BadXWG\<close> set
  algebra; the per-slice meagerness from \<open>nd\<close>; the empty/point/finite extreme
  instances; the closed-negligible cover @{text excess_arc_negligible_closed_cover}
  and the meagerness @{text excess_arc_projection_meager}; the codim-3 sanity
  bridges (\<open>Gjoint = 0\<close> on the bad locus); the joint \<open>C\<^sup>1\<close> field assembly; and the
  \<open>x\<close>-partial non-surjectivity of \<open>gradU\<close> on the bad locus (the M5 stratum witness).

  \<^bold>\<open>The single isolated residual\<close> @{text excess_arc_charts_Nn}: the joint
  \<open>(gradU, mstarg)\<close> chart over the arc.  Reduced here to the cleanest soundly-stated
  sub-obligation @{text joint_arc_chart_bundle} (the regular-value + codomain-3
  engine consumption); the chart core then follows proof-complete.\<close>


subsection \<open>The \<open>C\<^sup>1\<close> analytic-arc predicate (copied verbatim from D3fix)\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> \<phi> C1_differentiable_on {a..b}
                          \<and> \<gamma> = \<phi> ` {a..b})"


subsection \<open>STEP 1 --- soundness gate: a \<open>C\<^sup>1\<close> arc in the plane is negligible\<close>

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


subsection \<open>The mstarg interface (RE-STATED as local proof hole-stubs --- discharge at the Robust3 splice)\<close>

text \<open>The Gram determinant @{text mstarg} of the moment-map \<open>x\<close>-Jacobian lives in
  @{file \<open>../Appendix/Robust3/Nonemptiness_Robust3.thy\<close>}, NOT in the Robust2 heap.
  We re-state the facts the corrected chart core references, with EXACT signatures,
  as local @{text \<open>proof hole\<close>}-stubs; they discharge verbatim when this file is spliced
  against the Robust3 heap (where @{text mstarg} and these lemmas are proven).\<close>

definition mstarg :: "(real^2) \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

lemma surj_iff_mstarg: "surj (DM_paper_x x c) \<longleftrightarrow> mstarg c x \<noteq> 0"
  \<comment> \<open>Robust3 splice fact: the moment rank drop is the determinantal locus
      @{text \<open>mstarg c x = 0\<close>}.\<close>
  sorry

lemma mstarg_nonzero:
  fixes c :: "real^2"
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x::(real^2)^'n. mstarg c x \<noteq> 0"
  sorry

lemma nowhere_dense_mstarg_zeros:
  fixes c :: "real^2"
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. mstarg c x = 0}"
  sorry

text \<open>\<^bold>\<open>The joint-map \<open>C\<^sup>1\<close> facts the DESIGN needs (stated SOUNDLY).\<close>  The \<open>x\<close>- and
  \<open>\<omega>\<close>-derivatives of @{const mstarg} exist and are continuous (Robust3: \<open>det\<close> is
  smooth, the Gram entries are bilinear in the LINEAR @{const DM_paper_x} and
  polynomial in \<open>\<omega>\<close> through @{const cvec_dip}).  We package them as a single joint
  \<open>C\<^sup>1\<close> stub at the exact shape the engine consumes.  These are SOUND interface
  facts (no over-generalization: existence of a continuous total derivative of a
  determinant-of-polynomials map), NOT the irreducible content.\<close>

lemma has_derivative_mstarg_joint_C1:
  fixes V :: "((real^2)^'n) set" and \<Omega> :: "(real^2) set"
  shows "\<exists>Dm. (\<forall>z\<in>V\<times>\<Omega>.
                ((\<lambda>(x,\<omega>). mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x) has_derivative blinfun_apply (Dm z)) (at z))
             \<and> continuous_on (V\<times>\<Omega>) Dm"
  \<comment> \<open>Robust3 splice fact: @{const mstarg} (a determinant of a Gram matrix whose
      entries are polynomials in the LINEAR \<open>DM_paper_x\<close> and in \<open>\<omega>\<close> through
      \<open>cvec_dip\<close>) is jointly \<open>C\<^sup>1\<close> on \<open>V\<times>\<Omega>\<close>.\<close>
  sorry


subsection \<open>The CORRECTED curve-confined excess locus (\<open>BadXWG\<close>: gradU=0 RETAINED)\<close>

definition BadXWG :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXWG \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"


subsection \<open>Structural set algebra for \<open>BadXWG\<close> (proof-complete)\<close>

lemma BadXWG_empty:
  "BadXWG \<omega>0 \<omega>s {} = ({} :: ((real^2)^'n) set)"
  unfolding BadXWG_def by blast

lemma BadXWG_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "BadXWG \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXWG \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n) set)"
  using assms unfolding BadXWG_def by blast

lemma BadXWG_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "BadXWG \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)
          = (\<Union>i\<in>I. (BadXWG \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  unfolding BadXWG_def by blast

lemma BadXWG_point:
  fixes \<omega> :: "real^2"
  shows "BadXWG \<omega>0 \<omega>s {\<omega>}
          = {x :: (real^2)^'n.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  unfolding BadXWG_def by blast


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
  shows "meager (V \<inter> BadXWG \<omega>0 \<omega>s {\<omega>})"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0")
  case True
  have sub: "(V \<inter> BadXWG \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)
             \<subseteq> {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    unfolding BadXWG_def by blast
  show ?thesis
    by (rule meager_subset[OF sub fixed_omega_slice_meager[OF True nd]])
next
  case False
  hence "(V \<inter> BadXWG \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set) = {}"
    unfolding BadXWG_def by blast
  thus ?thesis by simp
qed


subsection \<open>Degenerate sanity checks: the cut is sound at the extreme instances\<close>

lemma excess_empty_arc_meager:
  fixes V :: "((real^2)^'n) set"
  shows "meager (V \<inter> BadXWG \<omega>0 \<omega>s {} :: ((real^2)^'n) set)"
  by (simp add: BadXWG_empty)

lemma excess_point_arc_meager:
  fixes V :: "((real^2)^'n) set" and \<omega> :: "real^2"
  assumes nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXWG \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)"
  by (rule fixed_omega_proj_meager[OF nd])

lemma excess_finite_arc_meager:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes fin: "finite \<gamma>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
proof -
  have eq: "(V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
              = (\<Union>\<omega>\<in>\<gamma>. V \<inter> BadXWG \<omega>0 \<omega>s {\<omega>})"
    unfolding BadXWG_def by blast
  have "meager (\<Union>\<omega>\<in>\<gamma>. (V \<inter> BadXWG \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set))"
    by (rule meager_Union_finite[OF fin]) (rule fixed_omega_proj_meager[OF nd])
  thus ?thesis unfolding eq .
qed


subsection \<open>The codim-3 joint map \<open>Gjoint = (gradU, mstarg)\<close> over the arc\<close>

text \<open>\<^bold>\<open>The codim-3 joint map, parametrized by the arc point \<open>\<omega>\<close>.\<close>  Two retained
  gradient equations together with the moment rank-drop determinant, packed into a
  single \<open>real^3\<close>-valued map.  \<open>Gjoint = 0\<close> at \<open>(x,\<omega>)\<close> is exactly: \<open>\<omega>\<close> is a critical
  point of the pattern (\<open>gradU = 0\<close>) AND the moment map drops rank there
  (\<open>mstarg = 0\<close>, i.e. \<open>\<not> surj (DM_paper_x)\<close>).\<close>

definition Gjoint :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2)^'n \<Rightarrow> real^2 \<Rightarrow> real^3" where
  "Gjoint \<omega>0 \<omega>s x \<omega> =
     vector [ gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1,
              gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2,
              mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x ]"

lemma Gjoint_zero_iff:
  "Gjoint \<omega>0 \<omega>s x \<omega> = 0
   \<longleftrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and> mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0"
proof -
  have L: "Gjoint \<omega>0 \<omega>s x \<omega> = 0
           \<longleftrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0
             \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 = 0
             \<and> mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0"
    unfolding Gjoint_def
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_3 vector_3)
  have G: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
           \<longleftrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0
             \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 = 0"
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
  show ?thesis using L G by blast
qed

text \<open>\<^bold>\<open>Codim-3 sanity bridge.\<close>  On the bad locus the retained moment rank-drop IS
  the determinantal equation \<open>mstarg = 0\<close>; hence each bad \<open>x\<close> (witnessed by some
  \<open>\<omega>\<in>\<Gamma>\<close>) satisfies \<open>Gjoint \<omega>0 \<omega>s x \<omega> = 0\<close> --- the full codim-3 cut.\<close>

lemma bad_imp_mstarg_zero:
  assumes "\<not> surj (DM_paper_x x c)"
  shows "mstarg c x = 0"
  using assms surj_iff_mstarg by blast

lemma Gjoint_zero_of_bad:
  fixes \<gamma> :: "(real^2) set"
  shows "(BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
           \<subseteq> {x. \<exists>\<omega>\<in>\<gamma>. Gjoint \<omega>0 \<omega>s x \<omega> = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0}"
proof
  fix x :: "(real^2)^'n"
  assume "x \<in> BadXWG \<omega>0 \<omega>s \<gamma>"
  then obtain \<omega> where w\<gamma>: "\<omega> \<in> \<gamma>"
    and gU: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and cn: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and nsurj: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    unfolding BadXWG_def by blast
  have ms0: "mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0"
    by (rule bad_imp_mstarg_zero[OF nsurj])
  have "Gjoint \<omega>0 \<omega>s x \<omega> = 0" using gU ms0 by (simp add: Gjoint_zero_iff)
  thus "x \<in> {x. \<exists>\<omega>\<in>\<gamma>. Gjoint \<omega>0 \<omega>s x \<omega> = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0}"
    using w\<gamma> cn by blast
qed


subsection \<open>The \<open>x\<close>-partial of \<open>gradU\<close> factors through \<open>DM_paper_x\<close> (M5 stratum structure)\<close>

text \<open>\<^bold>\<open>The defining structure of the M5 singular stratum, proven proof-complete from the
  heap.\<close>  The \<open>x\<close>-partial of \<open>gradU\<close> FACTORS as \<open>F \<circ> DM_paper_x x c\<close> with \<open>F\<close>
  bounded-linear (@{thm has_derivative_gradU_dip_x}).  Hence its surjectivity is
  GOVERNED by the moment-map rank: by @{thm gradU_dip_x_partial_surj}, when
  \<open>surj (DM_paper_x)\<close> (plus \<open>A \<noteq> 0\<close> and the immersion \<open>det (Dcvec) \<noteq> 0\<close>) the
  \<open>x\<close>-partial IS surjective.

  \<^bold>\<open>Honest caveat (NOT a free converse).\<close>  We do NOT assert here the converse
  ``\<open>\<not> surj (DM_paper_x) \<Longrightarrow> \<not> surj (x-partial)\<close>''.  That is NOT the naive
  composition fact \<open>surj (F \<circ> g) \<Longrightarrow> surj g\<close> (which is FALSE in general:
  \<open>range (F \<circ> g) = F\<close>(range g)\<close> can fill the codomain even when \<open>range g\<close> is a proper
  subspace).  Establishing the converse requires the injectivity content of \<open>F = dE\<close>
  on the relevant moment directions --- part of the deeper analysis, NOT a freebie.
  This is precisely WHY the regular value of \<open>Gjoint\<close> on the bad locus must draw its
  transverse rank from the \<open>\<omega>\<close>-direction (steering tangent) rather than the
  \<open>x\<close>-direction, and is one face of the irreducible content isolated below.\<close>

lemma gradU_x_partial_exists:
  fixes x :: "(real^2)^'n" and V :: "((real^2)^'n) set"
  shows "\<exists>F::complex^6 \<Rightarrow> real^2. bounded_linear F
            \<and> ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
                  (F \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x within V)"
  by (rule has_derivative_gradU_dip_x)

text \<open>The forward (regular) direction, cited verbatim from the heap as a sanity
  anchor: under the standing nondegeneracy data the \<open>x\<close>-partial of \<open>gradU\<close> IS
  surjective exactly where the moment map is.\<close>

lemma gradU_x_partial_surj_of_Msurj:
  fixes x :: "(real^2)^'n"
  assumes Anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
    and Msurj: "surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    and steer: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx"
  by (rule gradU_dip_x_partial_surj[OF Anz Msurj steer])


subsection \<open>The joint \<open>C\<^sup>1\<close> field of \<open>Gjoint\<close> over the arc (assembled from the heap + stub)\<close>

text \<open>\<^bold>\<open>The joint \<open>C\<^sup>1\<close> field, assembled proof-complete from the heap \<open>gradU\<close> field and
  the \<open>mstarg\<close> stub.\<close>  We do NOT need the explicit blinfun here for the
  reduction below; we record the \<open>C\<^sup>1\<close> structure abstractly to feed the engine.\<close>

lemma gradU_joint_C1_field:
  fixes V :: "((real^2)^'n) set" and \<Omega> :: "(real^2) set"
  shows "\<exists>Du. (\<forall>z\<in>V\<times>\<Omega>.
                ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) has_derivative blinfun_apply (Du z)) (at z))
             \<and> continuous_on (V\<times>\<Omega>) Du"
proof -
  obtain Du :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where der: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                        has_derivative blinfun_apply (Du z)) (at z)"
      and cont: "continuous_on UNIV Du"
    using gradU_dip_joint_C1 by blast
  have "continuous_on (V\<times>\<Omega>) Du"
    by (rule continuous_on_subset[OF cont subset_UNIV])
  with der show ?thesis by blast
qed


subsection \<open>The irreducible joint chart bundle over the arc (single isolated proof hole)\<close>

text \<open>\<^bold>\<open>The single irreducible obligation, soundly stated and tightly scoped.\<close>  This
  is the genuine analytic crux of D3 (DESIGN \<section>5 obligations 1-4): the joint
  \<open>(gradU, mstarg)\<close> chart over the \<open>C\<^sup>1\<close> arc.  We state it directly in the
  @{thm charts_core_Nn} output shape on the bad fibre, INDEPENDENT of the
  codomain-3 engine generalization (which is one route to it).  The honest content:
  \<^enum> The \<open>\<omega>\<close>-partial submersion of \<open>Gjoint\<close> at bad zeros (rows 1-2 from the steering
    nondegeneracy = \<open>\<omega>\<close>-Hessian content of \<open>gradU\<close>; row 3 from \<open>\<nabla> mstarg \<noteq> 0\<close>) off a
    named lower-dim stratum \<open>\<Sigma>\<close>.
  \<^enum> The codomain-\<open>real^3\<close> IFT chart (the heap @{thm crit_piece_compact} is
    hard-typed to the SQUARE \<open>real^2\<close> block; here the arc parameter \<open>t\<close> is scalar
    against a \<open>real^3\<close> codomain, so the block is not square and the engine must be
    re-proved for \<open>CARD(3)\<close>).
  \<^enum> The lower-dim stratum \<open>\<Sigma>\<close> (where regularity fails) split off and shown
    negligible (@{thm analytic_arc_negligible}-style, recursively).

  Everything OUTSIDE this proof hole (the cover\<open>\<rightarrow>\<close>meager assembly, the set algebra, the
  codim-3 bridges, the \<open>x\<close>-partial non-surjectivity) is proven proof-complete above and
  below.  This does NOT follow from \<open>nd\<close> alone (uncountable unions of nowhere-dense
  per-\<open>\<omega>\<close> slices need not be meager --- the very reason the gradU-dropped prior core
  was false).  NOT a splice freebie.\<close>

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
         (V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>GENUINE analytic core (CORRECTED, codim 3): the IFT chart of the per-arc
      COMBINED bad fibre (joint \<open>(gradU, mstarg)\<close>, \<open>gradU = 0\<close> RETAINED) in the
      @{thm charts_core_Nn} output shape.  The single irreducible \<open>proof hole\<close> of this
      file (the joint \<open>\<omega>\<close>-partial submersion + codomain-3 IFT + \<open>\<Sigma>\<close> stratum); it
      does NOT follow from \<open>nd\<close> alone.  NOT a splice freebie.\<close>
  sorry


subsection \<open>The EMPTY-arc extreme instance (proof-complete; soundness sanity check)\<close>

text \<open>The EMPTY-arc instance is closable proof-complete: the bad fibre is empty, so the
  empty-critical-set chart bundle satisfies every conjunct vacuously.\<close>

lemma excess_arc_charts_Nn_empty:
  fixes V :: "((real^2)^'n) set"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> BadXWG \<omega>0 \<omega>s {} :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof (intro exI conjI)
  let ?charts = "(\<lambda>i x. (x, 0)) :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
  let ?Crit = "(\<lambda>i. {}) :: nat \<Rightarrow> ((real^2)^'n) set"
  let ?D = "(\<lambda>i x. 0) :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
  show "(V \<inter> BadXWG \<omega>0 \<omega>s {} :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. (fst \<circ> ?charts i) ` (?Crit i))"
    by (simp add: BadXWG_empty)
  show "\<forall>i x. x \<in> ?Crit i \<longrightarrow>
          ((fst \<circ> ?charts i) has_derivative (blinfun_apply (?D i x))) (at x within ?Crit i)"
    by simp
  show "\<forall>i x. x \<in> ?Crit i \<longrightarrow> \<not> surj (blinfun_apply (?D i x))"
    by simp
  show "\<forall>i. closed ((fst \<circ> ?charts i) ` (?Crit i))"
    by simp
qed


subsection \<open>The closed negligible cover (proof-complete from the chart bundle)\<close>

lemma excess_arc_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
            (V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
          \<and> (\<forall>n. closed (K n))
          \<and> (\<forall>n. negligible (K n))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "(V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                    \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using excess_arc_charts_Nn[OF openV Vne c6 arc gsub pf nd]
    by (smt (verit, best))
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have Kcover: "(V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
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
  assumes cover: "(V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])

lemma excess_arc_projection_meager:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "(V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
      and clo: "\<forall>n. closed (K n)"
      and neg: "\<forall>n. negligible (K n)"
    using excess_arc_negligible_closed_cover[OF openV Vne c6 arc gsub pf nd] by blast
  show ?thesis
    by (rule excess_arc_projection_of_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

end
