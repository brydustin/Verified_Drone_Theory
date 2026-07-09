theory Scratch_m5_d3fix
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) Core D3 (CHARTS) --- CORRECTED per-arc IFT chart bundle, codim 3.\<close>

  \<^bold>\<open>The bug being fixed.\<close>  The prior D3 core proved meagerness of the
  curve-confined bad fibre @{text BadXW} that drops the @{text \<open>gradU = 0\<close>}
  constraint, retaining ONLY the moment rank-drop @{text \<open>\<not> surj (DM_paper_x x c)\<close>}.
  Over a fixed \<open>\<omega>\<close> the rank-drop locus \<open>mstarg c x = 0\<close> is codim 1 in
  \<open>x\<close>-space \<open>(real^2)^'n\<close> (dim \<open>2N\<close>); sweeping \<open>\<omega>\<close> along the 1-D arc adds one
  free parameter, dropping the codim to 0 --- a FULL-MEASURE (non-meager) set.
  So @{text BadXW} meagerness over a 1-D arc is \<^emph>\<open>FALSE\<close>.  The downstream
  @{text m5_D34_D3_collinear} only NEEDS the smaller set with @{text \<open>gradU = 0\<close>}
  retained; the prior file enlarged it (dropping a conjunct) before proving
  meagerness, which is unsound.

  \<^bold>\<open>The fix.\<close>  Define @{text BadXWG} by ADDING back the conjunct
  @{text \<open>gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0\<close>} (mirroring D4's @{text BadXGW}).
  Re-thread the entire chart chain over @{text BadXWG}; the chain reductions are
  gradU-agnostic (they carry the set abstractly through
  @{thm negligible_singular_image_2n} / @{thm meager_negligible_closed_cover}), so
  the threading is mechanical and the per-slice / cover layers stay proof-complete.

  \<^bold>\<open>The codim count (sanity test).\<close>  The combined bad locus is cut by
  TWO scalar gradient equations @{text \<open>gradU = 0\<close>} (\<open>\<omega>\<close>-Hessian content) PLUS the
  one determinantal moment equation @{text \<open>mstarg c x = 0\<close>}: three independent
  scalar conditions, codim 3.  Over the 1-D arc this is the genuine IFT chart of
  the joint \<open>C\<^sup>1\<close> map \<open>G = (gradU, mstarg)\<close>, whose \<open>\<omega>\<close>-partial regularity is forced
  by the \<open>C\<^sup>1\<close> arc tangent.  This does NOT follow from @{text nd} alone (the very
  reason the prior @{text BadXW} core was false: an uncountable union of
  nowhere-dense per-\<open>\<omega>\<close> slices need not be meager).

  \<^bold>\<open>What is proven proof-complete here.\<close>
  \<^item> @{text analytic_arc_negligible} (a \<open>C\<^sup>1\<close> arc is negligible);
  \<^item> the structural set algebra for @{text BadXWG} (@{text empty}/@{text mono}/
    @{text UN}/@{text point});
  \<^item> the per-fixed-angle slice meagerness from @{text nd} over @{text BadXWG}
    (strictly easier than over @{text BadXW}: adding @{text \<open>gradU = 0\<close>} only
    shrinks the slice);
  \<^item> the EMPTY-arc extreme instance @{text excess_arc_charts_Nn_empty};
  \<^item> the closed-negligible cover @{text excess_arc_negligible_closed_cover} and the
    meagerness @{text excess_arc_projection_meager}, assembled proof-complete from the
    (corrected) chart bundle;
  \<^item> the CORRECTED downstream connector @{text m5_D34_D3_collinear_fixed}: the
    canonical D3 leaf statement (which already KEEPS @{text \<open>gradU = 0\<close>}), now
    re-derived by routing through @{text BadXWG} (the SOUND embedding) instead of
    @{text BadXW} --- confirming the corrected target feeds the consumer.

  \<^bold>\<open>The single isolated residual.\<close>  The IFT chart of the per-arc combined
  bad fibre @{text excess_arc_charts_Nn} is the one precisely-scoped \<open>proof hole\<close>,
  now SOUND (codim 3, @{text \<open>gradU = 0\<close>} retained).  It is the genuine multi-week
  analytic content (the joint \<open>(gradU, mstarg)\<close> transversality over the arc), NOT a
  splice freebie.\<close>


subsection \<open>The \<open>C\<^sup>1\<close> analytic-arc predicate (copied verbatim from D3charts)\<close>

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
  against the Robust3 heap (where @{text mstarg} and these lemmas are proven).

  These stubs are SOUND interface facts (proven in Robust3), NOT the irreducible
  analytic content; the genuine residual is @{text excess_arc_charts_Nn} below.\<close>

definition mstarg :: "(real^2) \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

lemma surj_iff_mstarg: "surj (DM_paper_x x c) \<longleftrightarrow> mstarg c x \<noteq> 0"
  \<comment> \<open>Robust3 splice fact: the moment rank drop is the determinantal locus
      @{text \<open>mstarg c x = 0\<close>}.  Stubbed here; proven at line 578 of Robust3.\<close>
  sorry

lemma mstarg_nonzero:
  fixes c :: "real^2"
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x::(real^2)^'n. mstarg c x \<noteq> 0"
  \<comment> \<open>Robust3 splice fact: for a nonzero steering vector the moment Jacobian is
      generically full rank.\<close>
  sorry

lemma nowhere_dense_mstarg_zeros:
  fixes c :: "real^2"
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. mstarg c x = 0}"
  \<comment> \<open>Robust3 splice fact: the per-\<open>\<omega>\<close> determinantal zero set is nowhere dense.\<close>
  sorry


subsection \<open>The CORRECTED curve-confined excess locus (\<open>BadXWG\<close>: gradU=0 RETAINED)\<close>

text \<open>\<^bold>\<open>The corrected bad \<open>x\<close>-set\<close>: exactly the prior @{text BadXW} PLUS the retained
  conjunct @{text \<open>gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0\<close>}.  This is the
  per-arc sibling of D4's @{text BadXGW} restricted to the 1-D arc (D4 lives on the
  2-D linear-independence region; D3 on the arc).  Keeping @{text \<open>gradU = 0\<close>} is
  what makes the locus codim 3 (hence meager) rather than the false codim-0 of the
  prior @{text BadXW}.\<close>

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

text \<open>The per-\<open>\<omega>\<close> slice of @{text BadXWG} is a SUBSET of the corresponding slice of
  the prior @{text BadXW} (adding @{text \<open>gradU = 0\<close>} only shrinks it), so the same
  @{text nd} input still gives meagerness --- strictly easier than before.\<close>

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


subsection \<open>The EMPTY-arc extreme instance of the chart bundle (proof-complete)\<close>

text \<open>The EMPTY-arc instance is closable proof-complete: the bad fibre is empty, so the
  empty-critical-set chart bundle satisfies every conjunct vacuously.  Soundness
  sanity check that the (corrected) chart-bundle output shape is inhabited.\<close>

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


subsection \<open>The irreducible IFT-chart bundle (single isolated analytic \<open>proof hole\<close>, codim 3)\<close>

text \<open>\<^bold>\<open>The genuine analytic content, corrected and isolated as ONE precisely-scoped
  statement.\<close>  Over the (\<open>C\<^sup>1\<close>) analytic arc \<open>\<gamma> = \<phi> ` {a..b}\<close>, the CORRECTED
  curve-confined bad fibre \<open>V \<inter> BadXWG \<omega>0 \<omega>s \<gamma>\<close> (now KEEPING \<open>gradU = 0\<close>) admits a
  chart bundle in the exact shape consumed by @{thm negligible_singular_image_2n}
  / @{thm charts_core_Nn}.

  ROUTE (DESIGN \<section>4).  The combined rank drop is the JOINT \<open>C\<^sup>1\<close> map
  \<open>G (x,t) = (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t), mstarg (cvec_dip \<omega>0 \<omega>s (\<phi> t)) x)
   : ((real^2)^'n \<times> real) \<Rightarrow> (real^2 \<times> real)\<close> (codomain \<open>real^3\<close>).  At a bad point
  \<open>gradU = 0\<close> AND (via @{thm surj_iff_mstarg}) \<open>mstarg = 0\<close>, so \<open>G = 0\<close>; the chart's
  \<open>t\<close>-partial surjectivity (regular value of \<open>G\<close>) is forced by the \<open>C\<^sup>1\<close> arc tangent
  \<open>\<phi>' t\<close>, NOT by the \<open>x\<close>-partial (which is exactly what fails on the bad locus ---
  the defining feature of the M5 singular stratum).  The \<open>x\<close>-partial of \<open>gradU\<close> is
  @{thm has_derivative_gradU_dip_x}; of @{const mstarg} it comes through
  @{thm has_derivative_M_paper_x} and the Gram determinant; \<open>x\<close>-regularity feeds via
  @{thm regular_value_on_via_x_partial}.  Feeding the regular-value field into the
  (codomain-generalized) engine @{thm charts_core_Nn} on each compact sub-arc box
  yields charts whose \<open>x\<close>-projections \<open>fst \<circ> charts i\<close> have genuinely non-surjective
  derivatives on \<open>Crit i\<close> and CLOSED images.

  \<^bold>\<open>Codim 3 (sanity test).\<close>  Two gradient equations \<open>gradU = 0\<close> plus one
  determinantal equation \<open>mstarg = 0\<close>: three independent scalar conditions.  This is
  why retaining \<open>gradU = 0\<close> is essential --- dropping it (the prior @{text BadXW})
  gives codim 1 over a fixed \<open>\<omega>\<close>, hence codim 0 (full measure, NON-meager) once \<open>\<omega>\<close>
  sweeps the 1-D arc.  The corrected core does NOT follow from @{text nd} alone
  (uncountable unions of nowhere-dense slices need not be meager) and is NOT a
  splice freebie.\<close>

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
      @{thm charts_core_Nn} output shape (route above).  The single irreducible
      \<open>proof hole\<close> of this file; it does NOT follow from @{text nd} alone.  NOT a splice
      freebie.  The EMPTY-arc instance is closed proof-complete as
      @{thm excess_arc_charts_Nn_empty}.\<close>
  sorry


subsection \<open>The closed negligible cover (proof-complete from the corrected chart bundle)\<close>

text \<open>\<^bold>\<open>The closed negligible cover, assembled proof-complete from the chart bundle.\<close>
  From @{thm excess_arc_charts_Nn} the pieces \<open>K i = (fst \<circ> charts i) ` (Crit i)\<close>
  are CLOSED (chart output) and NEGLIGIBLE (@{thm negligible_singular_image_2n}:
  the projection has non-surjective derivative on \<open>Crit i\<close>), and they cover the
  corrected bad fibre.  This layer is gradU-agnostic: it consumes the chart bundle
  abstractly, so the @{text BadXW}\<open>\<rightarrow>\<close>@{text BadXWG} rename threads automatically.\<close>

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


subsection \<open>The corrected D3 connector feeds \<open>m5_D34_D3_collinear\<close> (SOUND embedding)\<close>

text \<open>\<^bold>\<open>Confirmation that the corrected target re-derives the consumer.\<close>  The canonical
  downstream leaf @{text m5_D34_D3_collinear} (Robust3) has a goal set that ALREADY
  KEEPS @{text \<open>gradU = 0\<close>}.  The prior file embedded that goal into @{text BadXW}
  (DROPPING @{text \<open>gradU = 0\<close>}) before proving meagerness --- an UNSOUND enlargement
  to a non-meager set.  Here we embed the SAME goal into the corrected
  @{text BadXWG} (which RETAINS @{text \<open>gradU = 0\<close>}): a genuine subset (no conjunct
  is dropped), so meagerness of @{text BadXWG} legitimately transfers to the goal.

  We bundle the @{text finitely_arc_coverable} cover of the collinear locus as an
  explicit hypothesis (it is the SEPARATE terminal proof obligation
  @{text collinear_locus_finite_arc_cover}, proven in Robust3 and provided by the
  sibling reduction --- NOT part of this file's chart obligation).  This lemma
  certifies that the corrected per-arc core, threaded through @{text BadXWG},
  produces exactly the canonical D3 leaf statement.\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"

lemma m5_D34_D3_collinear_fixed:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and I :: "nat set" and arc :: "nat \<Rightarrow> (real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    \<comment> \<open>The collinear locus is finitely \<open>C\<^sup>1\<close>-arc-coverable (the SEPARATE Robust3
        terminal proof hole @{text collinear_locus_finite_arc_cover}, supplied here as a
        hypothesis; NOT part of this file's chart obligation).\<close>
    and finI: "finite I"
    and Lcov: "{\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>} \<subseteq> (\<Union>i\<in>I. arc i)"
    and arcprop: "\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
proof -
  define L :: "(real^2) set" where "L = {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}"
  \<comment> \<open>\<^bold>\<open>SOUND embedding\<close>: the D3 goal (which KEEPS \<open>gradU = 0\<close>) injects into the
      CORRECTED @{text BadXWG} fibre over \<open>L\<close> --- a genuine subset (no conjunct
      dropped), unlike the prior unsound @{text BadXW} embedding.\<close>
  have sub1: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}
        \<subseteq> (V \<inter> BadXWG \<omega>0 \<omega>s L :: ((real^2)^'n) set)"
    unfolding BadXWG_def L_def by blast
  have sub2: "(V \<inter> BadXWG \<omega>0 \<omega>s L :: ((real^2)^'n) set)
              \<subseteq> V \<inter> BadXWG \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)"
    using BadXWG_mono[OF Lcov[folded L_def]] by blast
  have eqU: "(V \<inter> BadXWG \<omega>0 \<omega>s (\<Union>i\<in>I. arc i) :: ((real^2)^'n) set)
              = (\<Union>i\<in>I. V \<inter> BadXWG \<omega>0 \<omega>s (arc i))"
    by (subst BadXWG_UN) blast
  have meagU: "meager (\<Union>i\<in>I. (V \<inter> BadXWG \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  proof (rule meager_Union_finite[OF finI])
    fix i :: nat assume iI: "i \<in> I"
    have ai: "analytic_arc (arc i)" and asub: "arc i \<subseteq> OmegaPF ctr \<delta>"
      using arcprop iI by blast+
    show "meager (V \<inter> BadXWG \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set)"
      by (rule excess_arc_projection_meager[OF openV Vne c6 ai asub pf nd])
  qed
  have meagAll: "meager (V \<inter> BadXWG \<omega>0 \<omega>s (\<Union>i\<in>I. arc i) :: ((real^2)^'n) set)"
    unfolding eqU by (rule meagU)
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}
        \<subseteq> (V \<inter> BadXWG \<omega>0 \<omega>s (\<Union>i\<in>I. arc i) :: ((real^2)^'n) set)"
    using sub1 sub2 by blast
  show ?thesis by (rule meager_subset[OF sub meagAll])
qed

end
