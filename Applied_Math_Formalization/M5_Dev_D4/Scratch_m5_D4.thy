theory Scratch_m5_D4
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) D4 --- the Branch-P residual (complementary, NON phase-collinear).\<close>

  This file wires the D4 leaf @{text m5_D34_D4_branchP} (the complementary
  branch of the D34 residual) against the SAME parametric excess engine
  @{text excess_projection_meager} that D3 consumes.  The engine lemma is stated
  \<^emph>\<open>parametrically\<close> in the angle set \<open>\<Gamma>\<close> (any subset of the bounded angle box
  @{term "OmegaPF ctr \<delta>"}), so at the STATEMENT level D4 reduces to it verbatim,
  exactly mirroring @{text D3_excess_engine} but with the COMPLEMENTARY angle set
  \<open>\<Gamma> = {\<omega>\<in>OmegaPF. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}\<close> in place of the phase-collinear one.

  \<^bold>\<open>Does D4 introduce a NEW genuine core beyond the engine?\<close>  At the level of the
  Isabelle obligation: \<^bold>\<open>NO\<close>.  The engine lemma @{text excess_projection_meager}
  requires only \<open>\<Gamma> \<subseteq> OmegaPF ctr \<delta>\<close> (hypothesis @{text Gsub}); the complementary
  set satisfies this by @{method blast}.  So D4 closes from the engine with NO new
  proof obligation of its own --- the only proof obligation it leans on is the shared engine proof obligation
  @{text excess_projection_meager} (shared with D3, \<open>freebie_at_splice = false\<close>),
  plus the Robust3-resident @{text fixed_c_nonsurj_nowhere_dense} freebie that is
  consumed only through the abstract hypothesis @{text nd}.

  \<^bold>\<open>The honest mathematical caveat.\<close>  Although the engine's STATEMENT is
  \<open>\<Gamma>\<close>-agnostic, the engine's recommended PROOF route (finite cover of \<open>\<Gamma>\<close> by
  \<open>\<int>\<^sup>3\<close>-period analytic ARCS via @{thm finite_affine_int_zeros}, then IFT charts)
  is honest only for a \<^bold>\<open>one-parameter\<close> angle curve.  The phase-collinear locus
  \<open>\<Gamma>\<^sub>3\<close> (D3) is such a codimension-1 curve; the COMPLEMENT \<open>\<Gamma>\<^sub>4\<close> (D4) is
  2-\<^bold>\<open>dimensional\<close> (open in the box), so the finite-arc cover does NOT discharge
  it directly.  The genuine NEW Branch-P math is the rank-drop DICHOTOMY
  (\<open>\<gamma> \<parallel> c\<close> or not) that recovers codimension on the 2D complement --- \<open>core_3d\<close>
  being ruled out structurally.  In THIS scaffold that extra content is folded
  INTO the proof of the shared engine proof hole @{text excess_projection_meager}
  itself (which is parametric in \<open>\<Gamma>\<close> and must therefore be proven so as to cover
  BOTH the 1-dim curve and the 2-dim complement).  We isolate the Branch-P
  dichotomy obligation explicitly below as @{text branchP_dichotomy} (a precisely
  scoped NEW proof hole, \<open>freebie_at_splice = false\<close>) and RECORD how the engine proof hole
  must subsume it, but the D4 LEAF itself needs no proof hole beyond the engine.\<close>


subsection \<open>The phase-collinear predicate (copied verbatim from D34/Engine)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>Robust3-supplied fixed-angle nowhere-density (freebie at splice)\<close>

text \<open>Replicated verbatim from D34/Engine.  PROVEN proof-complete in
  \<open>Nonemptiness_Robust3\<close> (in scope at the splice site, L578 + L744).  Here a single
  scoped proof hole that closes automatically at the L970 splice.  In the engine proper
  it is consumed only through the abstract hypothesis @{text nd}.\<close>

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  \<comment> \<open>Robust3 freebie at splice (mstarg machinery above the splice site).\<close>
  sorry


subsection \<open>The curve-confined excess locus (copied verbatim from Engine)\<close>

definition BadXW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

text \<open>The engine's bad set is the intersection of \<open>V\<close> with \<open>BadXW\<close> over the angle
  set --- here specialised to the \<^bold>\<open>complementary\<close> (non phase-collinear) curve.
  proof-complete SET equality (mirrors @{text engine_bad_eq_projection}).\<close>

lemma engine_bad_eq_projection_compl:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  shows "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}
        = V \<inter> BadXW \<omega>0 \<omega>s {\<omega> \<in> OmegaPF ctr \<delta>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  unfolding BadXW_def by blast


subsection \<open>The shared parametric excess engine (stub: shared with D3/Engine)\<close>

text \<open>\<^bold>\<open>The Sard-free excess engine\<close> --- copied VERBATIM from
  \<open>M5_Dev_Engine/Scratch_m5_engine.thy\<close>, lemma @{text excess_projection_meager}.
  It is stated parametrically in \<open>\<Gamma>\<close> (only @{text Gsub} \<open>\<Gamma> \<subseteq> OmegaPF ctr \<delta>\<close>) so
  that D4 reuses it verbatim with the complementary curve.  This is the ONE shared
  genuine MATH proof hole (the irreducible analytic core of M5).  \<^bold>\<open>NOT\<close> a splice
  freebie --- this is the real analysis, shared between D3 and D4.

  For D4 specifically, proving this lemma at the COMPLEMENTARY (2-dimensional)
  \<open>\<Gamma>\<close> requires the Branch-P rank-drop dichotomy @{text branchP_dichotomy} below;
  see that lemma for the genuine NEW obligation D4 contributes to the engine.\<close>

lemma excess_projection_meager:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>)"
  \<comment> \<open>SHARED genuine MATH proof hole (with D3/Engine).  freebie_at_splice = false.\<close>
  sorry


subsection \<open>The genuine NEW Branch-P obligation (the 2D rank-drop dichotomy)\<close>

text \<open>\<^bold>\<open>The Branch-P dichotomy --- the genuine NEW math D4 contributes.\<close>

  This is the obligation that the engine's finite-ARC cover does NOT supply when
  \<open>\<Gamma>\<close> is the 2-dimensional complement \<open>\<Gamma>\<^sub>4 = {\<omega>\<in>OmegaPF. \<not> phase_collinear ...}\<close>.
  Over the codimension-1 phase-collinear curve (D3) the bad fibre is charted by a
  single IFT graph; over the 2D complement one must instead split each angle
  \<open>\<omega>\<in>\<Gamma>\<^sub>4\<close> by the rank-drop dichotomy:

  \<^item> \<^bold>\<open>(\<gamma> \<parallel> c)\<close>: the steering-phase gradient direction \<open>\<gamma> = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)\<close>
    is parallel to \<open>c = cvec_dip \<omega>0 \<omega>s \<omega>\<close> --- but on \<open>\<Gamma>\<^sub>4\<close> we are in the COMPLEMENT
    of @{const phase_collinear}, i.e. exactly \<open>\<not>(\<gamma> \<parallel> c)\<close>, so this case is empty
    on \<open>\<Gamma>\<^sub>4\<close>;
  \<^item> \<^bold>\<open>(\<gamma> \<not>\<parallel> c)\<close>: \<open>\<gamma>\<close> and \<open>c\<close> are linearly independent, so the two steering
    Jacobian columns \<open>{Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1), Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)}\<close>
    (the latter nonzero by @{thm Dcvec_col2_nz} under @{text pf}) span enough of the
    \<open>(c, \<gamma>)\<close> excess directions that the moment-rank-drop equation, ADJOINED to the
    2 free angle parameters, still cuts a \<open>(2N-1)\<close>-dim graph in the \<open>(x,\<omega>)\<close> excess
    space --- \<open>core_3d\<close> (a genuine 3-codim drop forcing a 2N-dim bad projection) is
    ruled out STRUCTURALLY because the \<open>gradU\<close> rows degenerate exactly at the
    residual witnesses, so the excess never reaches full configuration dimension.

  Concretely the obligation the engine needs from D4 is: on the complementary
  curve, the \<open>x\<close>-projection of the bad \<open>(x,\<omega>)\<close> locus is STILL negligible
  (codimension \<open>\<ge> 1\<close> survives the extra angle parameter).  We state it as
  meagerness of \<open>V \<inter> BadXW\<close> over the complement, which is precisely the engine
  conclusion at \<open>\<Gamma>\<^sub>4\<close>; the NEW content is that the dichotomy keeps it codim-1.\<close>

lemma branchP_dichotomy:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s {\<omega> \<in> OmegaPF ctr \<delta>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>})"
  \<comment> \<open>GENUINE NEW Branch-P proof hole: the 2D rank-drop dichotomy that recovers
      codimension on the complement.  freebie_at_splice = false.  In the final
      splice this is exactly @{text excess_projection_meager} instantiated at the
      complementary 2D curve, whose proof must carry the dichotomy.\<close>
  sorry


subsection \<open>The D4 excess engine, proof-complete from the shared core\<close>

text \<open>The D4 analogue of @{text D3_excess_engine}: the complementary bad set is
  \<open>V \<inter> BadXW\<close> over the complementary curve, which is a subset of \<open>OmegaPF\<close>, so the
  parametric engine @{thm excess_projection_meager} applies VERBATIM.  proof-complete
  here (the analysis is in the shared engine proof hole).\<close>

lemma D4_excess_engine:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
proof -
  define \<Gamma> :: "(real^2) set"
    where "\<Gamma> = {\<omega> \<in> OmegaPF ctr \<delta>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  have Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>" unfolding \<Gamma>_def by blast
  have eq: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
              cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
            \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}
          = V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>"
    unfolding \<Gamma>_def by (rule engine_bad_eq_projection_compl)
  show ?thesis
    unfolding eq
    by (rule excess_projection_meager[OF openV Vne c6 d0 pf Gsub nd])
qed


subsection \<open>The D4 leaf, proof-complete from the excess engine\<close>

text \<open>The exact D4 target statement (verbatim from
  \<open>M5_Dev_D34/Scratch_m5_D34.thy\<close>, lemma @{text m5_D34_D4_branchP}).  The D4 bad
  set is a subset of the excess engine's bad set (dropping \<open>gradU = 0\<close> and
  \<open>det Dcvec \<noteq> 0\<close> only enlarges the set), so it is meager by @{thm meager_subset}.
  Proven proof-complete from @{thm D4_excess_engine}.\<close>

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
proof -
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}
        \<subseteq> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub D4_excess_engine[OF openV Vne c6 d0 pf nd]])
qed

end
