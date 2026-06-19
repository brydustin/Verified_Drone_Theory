theory Scratch_m5_branchp
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) D4 --- the Branch-P residual (GENUINE; \<open>gradU = 0\<close> retained).\<close>

  This file closes the D4 leaf @{text m5_D34_D4_branchP} of the D34 residual
  (the complementary, \<^bold>\<open>non\<close> phase-collinear branch).  Target statement copied
  \<^emph>\<open>verbatim\<close> from @{file \<open>../M5_Dev_D34/Scratch_m5_D34.thy\<close>} (lemma
  @{text m5_D34_D4_branchP}, L161--L173).

  \<^bold>\<open>SOUNDNESS NOTICE --- why this is NOT the prior unsound D4.\<close>  A previous wave
  (@{file \<open>../M5_Dev_D4/Scratch_m5_D4.thy\<close>}) "closed" D4 by feeding the
  \<^bold>\<open>2-dimensional\<close> non-collinear angle complement \<open>\<Gamma>\<^sub>4 = {\<omega>\<in>OmegaPF. \<not> phase_collinear}\<close>
  to the curve engine @{text excess_projection_meager} (whose only \<open>\<Gamma>\<close>-constraint is
  \<open>\<Gamma> \<subseteq> OmegaPF\<close>), AND by DROPPING the \<open>gradU = 0\<close> / \<open>det Dcvec \<noteq> 0\<close> conditions.
  That is UNSOUND: the engine's STATEMENT
    \<open>meager (V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>)\<close>  with  \<open>BadXW \<omega>0 \<omega>s \<Gamma> =
        {x. \<exists>\<omega>\<in>\<Gamma>. cvec \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec \<omega>))}\<close>
  is \<^bold>\<open>FALSE\<close> for a genuinely 2-dimensional \<open>\<Gamma>\<close>: as \<open>\<omega>\<close> sweeps a 2-D open set, the
  per-fibre nowhere-dense \<open>x\<close>-slices \<open>{x. \<not> surj (DM_paper_x x (cvec \<omega>))}\<close> sweep an
  uncountable union that is (in general) the whole space, NOT meager.  The
  \<open>gradU = 0\<close> equation is EXACTLY the codimension that prevents this; dropping it
  (and only keeping \<open>\<not> surj\<close>) over a 2-D angle region is the over-generalisation
  that ships a green build on a false statement.

  \<^bold>\<open>SANITY TEST of the soundness claim (degenerate extreme).\<close>  Take \<open>\<Gamma>\<close> = the whole
  box \<open>OmegaPF\<close> (the largest case) and drop \<open>gradU = 0\<close>: the over-general
  \<open>{x. \<exists>\<omega>. cvec \<noteq> 0 \<and> \<not> surj(DM x (cvec \<omega>))}\<close> is a union over a 2-parameter family of
  nowhere-dense slices; there is no reason for the union to have empty-interior
  closure, so meagerness FAILS at this extreme.  Our statements below keep
  \<open>gradU = 0\<close> precisely so the extreme case is not vacuously over-claimed.

  \<^bold>\<open>What this scaffold establishes SOUND, sorry-free.\<close>
  \<^enum> @{text branchP_parallel_case_vacuous}: on the complement \<open>\<not> phase_collinear\<close>,
    the "\<open>\<gamma> \<parallel> c\<close>" sub-case of the rank-drop dichotomy is EMPTY (definitionally:
    \<open>\<not> phase_collinear\<close> is exactly \<open>\<not>(\<gamma> \<parallel> c)\<close> in either direction).  This is the
    structural half of the diary's dichotomy, here a definitional triviality
    (sorry-free) --- and the honest record that the parallel branch contributes
    nothing on \<open>\<Gamma>\<^sub>4\<close>.
  \<^enum> @{text branchP_dichotomy_split}: the D4 bad set is the UNION of its
    \<open>\<gamma> \<parallel> c\<close> part (empty here) and its \<open>\<gamma> \<not>\<parallel> c\<close> part (the genuine core), so D4
    reduces to the \<open>\<gamma> \<not>\<parallel> c\<close> meagerness alone.  Sorry-free set algebra.
  \<^enum> @{text m5_D34_D4_branchP}: the exact target, assembled sorry-free from the
    single genuine core @{text branchP_indep_core} via @{thm meager_subset}.

  \<^bold>\<open>The single genuine irreducible step (ONE scoped sorry, NOT a splice freebie).\<close>
  @{text branchP_indep_core}: on the 2-D non-collinear region, with the
  \<^bold>\<open>retained\<close> constraints \<open>gradU = 0 \<and> det Dcvec \<noteq> 0 \<and> cvec \<noteq> 0\<close> and
  \<open>\<not> surj (DM_paper_x x (cvec \<omega>))\<close>, the \<open>x\<close>-projection of the bad \<open>(x,\<omega>)\<close> locus is
  meager.  The route (diary "Branch-P") is the linear-independence rank-drop:
  \<open>\<gamma> = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)\<close> and \<open>c = cvec_dip \<omega>0 \<omega>s \<omega>\<close> are linearly
  independent, so \<open>{\<gamma>, c}\<close> span \<open>\<real>\<^sup>2\<close>, the steering map is a local diffeo in \<open>\<omega>\<close>,
  and the \<open>gradU = 0\<close> equation (two scalar equations coupling \<open>x\<close> and \<open>\<omega>\<close>) plus the
  moment rank-drop \<open>\<not> surj\<close> cut the bad \<open>(x,\<omega>)\<close> set to a \<open>(2N-1)\<close>-dim graph whose
  \<open>x\<close>-projection is negligible; \<open>core_3d\<close> (a full \<open>2N\<close>-dim projection) is ruled out
  structurally because the \<open>gradU\<close> rows degenerate exactly at the residual
  witnesses.  See @{text remaining_report}: this is a \<^bold>\<open>NEW core\<close>, distinct from
  D3's @{text excess_arc_projection_meager} (which exploits a 1-D arc cover that
  is unavailable here).\<close>


subsection \<open>The phase-collinear predicate (copied verbatim from D34/Engine)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>Robust3-supplied fixed-angle nowhere-density (freebie at splice)\<close>

text \<open>Replicated verbatim from D34.  PROVEN sorry-free in \<open>Nonemptiness_Robust3\<close>
  (in scope at the L970 splice site, L578 + L744).  Here a single scoped sorry
  that closes automatically at the splice; consumed only through the abstract
  hypothesis @{text nd}.  \<open>freebie_at_splice = true\<close>.\<close>

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  \<comment> \<open>Robust3 freebie at the L970 splice (\<open>surj_iff_mstarg\<close> + \<open>nowhere_dense_mstarg_zeros\<close>);
      out of scope here because \<open>mstarg\<close> is Robust3-resident.\<close>
  sorry


subsection \<open>The bad x-set over an angle set, with \<open>gradU = 0\<close> RETAINED\<close>

text \<open>\<^bold>\<open>The SOUND curve-confined bad locus.\<close>  Unlike the prior unsound D4 (which
  used the engine's \<open>BadXW\<close> = \<open>{x. \<exists>\<omega>\<in>\<Gamma>. cvec \<noteq> 0 \<and> \<not> surj}\<close>, dropping \<open>gradU = 0\<close>),
  this bad set RETAINS the codimension-giving constraints \<open>gradU = 0\<close> and
  \<open>det Dcvec \<noteq> 0\<close>.  This is the set the D4 target actually quantifies, and the set
  for which meagerness is genuinely TRUE on the 2-D non-collinear region.\<close>

definition BadXGW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXGW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

text \<open>The D4 target's bad set is exactly \<open>V \<inter> BadXGW\<close> over the complementary
  (non-collinear) angle set.  Sorry-free SET equality.\<close>

lemma branchP_bad_eq_projection:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  shows "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}
        = V \<inter> BadXGW \<omega>0 \<omega>s {\<omega> \<in> OmegaPF ctr \<delta>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  unfolding BadXGW_def by blast


subsection \<open>The rank-drop dichotomy predicate: \<open>\<gamma> \<parallel> c\<close>\<close>

text \<open>The diary's dichotomy splits each angle by whether the steering-phase
  gradient direction \<open>\<gamma> = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)\<close> is parallel to the
  wavevector \<open>c = cvec_dip \<omega>0 \<omega>s \<omega>\<close>.  We name this exactly as the disjunction in
  @{const phase_collinear} so that "\<open>\<gamma> \<parallel> c\<close>" \<open>=\<close> @{const phase_collinear} and its
  negation is the genuine linear-independence case.\<close>

definition gamma_par_c :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow> phase_collinear \<omega>0 \<omega>s \<omega>"

text \<open>The negation is genuine 2-vector linear independence of \<open>\<gamma>\<close> and \<open>c\<close>: neither
  is a scalar multiple of the other.  This is the structurally distinguished
  Branch-P case.  Sorry-free unfolding.\<close>

lemma not_gamma_par_c_iff:
  "\<not> gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<forall>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<noteq> t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<and> (\<forall>t. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"
  unfolding gamma_par_c_def phase_collinear_def by blast


subsection \<open>Dichotomy half 1: the parallel case is vacuous on the complement\<close>

text \<open>\<^bold>\<open>The structural half of the Branch-P dichotomy (sorry-free).\<close>  On the
  non-collinear complement \<open>\<Gamma>\<^sub>4\<close>, the "\<open>\<gamma> \<parallel> c\<close>" sub-case is empty, because by
  construction @{const gamma_par_c} \<open>=\<close> @{const phase_collinear} and \<open>\<Gamma>\<^sub>4\<close> is
  exactly its complement.  This records that the parallel branch contributes
  nothing on \<open>\<Gamma>\<^sub>4\<close> --- the dichotomy collapses to the linear-independence core.\<close>

lemma branchP_parallel_case_vacuous:
  fixes \<Gamma> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> {\<omega>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  shows "{\<omega> \<in> \<Gamma>. gamma_par_c \<omega>0 \<omega>s \<omega>} = {}"
  using assms unfolding gamma_par_c_def by blast


subsection \<open>Dichotomy: the complement splits into parallel \<union> independent\<close>

text \<open>\<^bold>\<open>The dichotomy split (sorry-free set algebra).\<close>  The bad \<open>x\<close>-set over the
  complement \<open>\<Gamma>\<^sub>4\<close> is the union of the bad set over the parallel part of \<open>\<Gamma>\<^sub>4\<close>
  (empty, by @{thm branchP_parallel_case_vacuous}) and the bad set over the
  independent part of \<open>\<Gamma>\<^sub>4\<close>.  Since the parallel part is empty, the bad set over
  \<open>\<Gamma>\<^sub>4\<close> equals the bad set over its independent part --- which is exactly the
  genuine core.\<close>

lemma BadXGW_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "BadXGW \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXGW \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n) set)"
  using assms unfolding BadXGW_def by blast

lemma branchP_dichotomy_split:
  fixes \<Gamma> :: "(real^2) set"
  assumes Gsub: "\<Gamma> \<subseteq> {\<omega>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  shows "(BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
         = BadXGW \<omega>0 \<omega>s {\<omega> \<in> \<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>}"
proof -
  have eq: "\<Gamma> = {\<omega> \<in> \<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>}"
    using Gsub unfolding gamma_par_c_def by blast
  show ?thesis by (subst eq) (rule refl)
qed


subsection \<open>Per-fixed-angle slice meagerness (sorry-free from \<open>nd\<close>)\<close>

text \<open>The degenerate "angle set is a single point" sanity check: the per-angle
  bad slice is nowhere dense (hence meager) from @{text nd}.  Sorry-free.  This
  is the structural confirmation that the cut at @{text branchP_indep_core} is on
  the right object.\<close>

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


subsection \<open>The genuine NEW Branch-P core (ONE scoped MATH sorry)\<close>

text \<open>\<^bold>\<open>The genuine irreducible analytic step of D4.\<close>  On the 2-D non-collinear
  region (here the \<open>\<gamma> \<not>\<parallel> c\<close>, i.e. linear-independence, part of the angle set),
  with the codimension-giving constraints \<open>gradU = 0 \<and> det Dcvec \<noteq> 0 \<and> cvec \<noteq> 0\<close>
  RETAINED, the \<open>x\<close>-projection of the bad \<open>(x,\<omega>)\<close> locus is meager.

  \<^bold>\<open>Why a NEW core, not D3's arc engine.\<close>  D3's
  @{text excess_arc_projection_meager} reduces a \<^bold>\<open>1-dimensional\<close> analytic arc
  (the phase-collinear curve) by a FINITE arc cover + IFT chart + negligible
  projection.  On \<open>\<Gamma>\<^sub>4\<close> the angle set is genuinely \<^bold>\<open>2-dimensional\<close> (open in the
  box), so NO finite arc cover exists --- the D3 machinery does not apply.  The
  codimension must instead come from the RETAINED \<open>gradU = 0\<close> constraint (two
  scalar equations coupling \<open>x\<close> and \<open>\<omega>\<close>); this is the new content.

  \<^bold>\<open>Route (diary "Branch-P", linear-independence rank-drop).\<close>
  \<^enum> On \<open>\<gamma> \<not>\<parallel> c\<close>, the pair \<open>\<gamma> = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)\<close>, \<open>c = cvec_dip \<omega>0 \<omega>s \<omega>\<close>
    is linearly independent (@{thm not_gamma_par_c_iff}); together with
    \<open>det Dcvec \<noteq> 0\<close> (the second steering column nonzero by @{thm Dcvec_col2_nz}
    under @{text pf}) the steering map is a local diffeomorphism in \<open>\<omega>\<close>.
  \<^enum> Work in the \<open>(x,\<omega>)\<close> excess space \<open>((real^2)^'n) \<times> (real^2)\<close> (dimension
    \<open>2N + 2\<close>).  The bad locus is cut by: \<open>gradU = 0\<close> (2 scalar equations) and the
    moment rank-drop \<open>\<not> surj (DM_paper_x x (cvec \<omega>))\<close> (codim \<open>\<ge> 1\<close> in \<open>x\<close> off the
    nowhere-dense base supplied by @{text nd}).  Net: the bad locus is a graph of
    dimension \<open>\<le> 2N + 2 - 3 = 2N - 1\<close>.
  \<^enum> \<open>core_3d\<close> (a genuine 3-codim drop that would still leave a \<open>2N\<close>-dim \<open>x\<close>-image)
    is ruled out STRUCTURALLY: the \<open>gradU\<close> rows degenerate exactly at the residual
    witnesses, so the excess never reaches full configuration dimension --- the
    \<open>x\<close>-projection of a \<open>(2N-1)\<close>-dim graph is NEGLIGIBLE
    (@{thm negligible_singular_image_2n}).
  \<^enum> Cover the bad locus by countably many closed pieces (compact \<open>\<omega>\<close>-cells \<open>\<times>\<close>
    closed \<open>x\<close>-graphs), each with negligible \<open>x\<close>-projection; closed + negligible
    \<open>\<Longrightarrow>\<close> nowhere dense, countable union \<open>\<Longrightarrow>\<close> meager
    (@{thm meager_negligible_closed_cover}).  Mirror the flatten/conjugate/pullback
    skeleton of @{thm parametric_transversality_meager_planar_config}.
  \<^bold>\<open>NOT a splice freebie\<close> --- this is the real Branch-P analysis.\<close>

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
  \<comment> \<open>GENUINE NEW Branch-P sorry: the linear-independence rank-drop on the 2-D
      non-collinear region, with \<open>gradU = 0\<close> RETAINED to supply codimension.
      \<open>core_3d\<close> ruled out structurally; \<open>x\<close>-projection of the \<open>(2N-1)\<close>-dim graph is
      negligible \<Rightarrow> meager.  Route above.  freebie_at_splice = false.\<close>
  sorry


subsection \<open>The Branch-P engine: complement \<Longrightarrow> meager (sorry-free from core)\<close>

text \<open>The D4 analogue of @{text D3_excess_engine}, but SOUND: it keeps
  \<open>gradU = 0\<close> (the bad set is \<open>BadXGW\<close>, not the engine's \<open>BadXW\<close>) and routes
  through the dichotomy.  Sorry-free from @{thm branchP_indep_core} via the
  dichotomy split (the parallel sub-case is empty on the complement).\<close>

lemma branchP_engine:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
proof -
  define \<Gamma> :: "(real^2) set"
    where "\<Gamma> = {\<omega> \<in> OmegaPF ctr \<delta>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  have Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>" unfolding \<Gamma>_def by blast
  \<comment> \<open>\<open>\<Gamma>\<close> lies in the non-collinear complement, so the dichotomy collapses to the
      independence core (parallel case vacuous).\<close>
  have GsubNC: "\<Gamma> \<subseteq> {\<omega>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}" unfolding \<Gamma>_def by blast
  define \<Gamma>I :: "(real^2) set"
    where "\<Gamma>I = {\<omega> \<in> \<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>}"
  have GIsub: "\<Gamma>I \<subseteq> OmegaPF ctr \<delta>" using Gsub unfolding \<Gamma>I_def by blast
  have GIindep: "\<forall>\<omega>\<in>\<Gamma>I. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>" unfolding \<Gamma>I_def by blast
  \<comment> \<open>The dichotomy split: \<open>BadXGW \<Gamma> = BadXGW \<Gamma>I\<close> (parallel part empty).\<close>
  have dich: "(BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) = BadXGW \<omega>0 \<omega>s \<Gamma>I"
    unfolding \<Gamma>I_def by (rule branchP_dichotomy_split[OF GsubNC])
  \<comment> \<open>The set equality to the engine target.\<close>
  have eq: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
              gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
            \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
            \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}
          = V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
    unfolding \<Gamma>_def by (rule branchP_bad_eq_projection)
  \<comment> \<open>The genuine core on the independence part.\<close>
  have core: "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>I :: ((real^2)^'n) set)"
    by (rule branchP_indep_core[OF openV Vne c6 d0 pf GIsub GIindep nd])
  show ?thesis
    unfolding eq dich by (rule core)
qed


subsection \<open>The D4 leaf, sorry-free from the Branch-P engine\<close>

text \<open>The exact D4 target statement (verbatim from
  \<open>M5_Dev_D34/Scratch_m5_D34.thy\<close>, lemma @{text m5_D34_D4_branchP}).  Proven
  sorry-free from @{thm branchP_engine} (the bad sets coincide, so no
  superset-trim is even needed).  Crucially the \<open>gradU = 0\<close> conjunct is KEPT
  throughout --- the soundness-preserving difference from the prior D4.\<close>

lemma m5_D34_D4_branchP:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  by (rule branchP_engine[OF openV Vne c6 d0 pf nd])

end
