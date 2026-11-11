theory Scratch_m5_d3sound_detHess
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) Core D3 (SOUND, codim 3) --- per-C\<^sup>1-arc IFT chart bundle of
  \<open>V \<inter> BadXWG \<omega>0 \<omega>s \<gamma>\<close> via the DET-HESSU SPLIT.\<close>

  STATUS: DRAFT. Cannot run \<open>isabelle build\<close> here; the assembly/structural/cover
  layers are written to be discharged from CONFIRMED heap lemmas (signatures
  grepped + read), and the two genuine analytic residuals are isolated as
  precisely-scoped \<open>proof hole\<close>s with exact statements.

  \<^bold>\<open>The SOUND target (confirmed: \<open>gradU = 0\<close> RETAINED).\<close>  Over a \<open>C\<^sup>1\<close> arc
  \<open>\<gamma> = \<phi> ` {a..b}\<close>, the bad fibre
    \<open>BadXWG \<omega>0 \<omega>s \<gamma> = {x. \<exists>\<omega>\<in>\<gamma>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
                          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}\<close>
  (verbatim from @{file \<open>../M5_Dev_D3fix/Scratch_m5_d3fix.thy\<close>} line 131-135,
  and @{file \<open>../M5_Dev_D3eng/Scratch_m5_d3eng.thy\<close>} line 130-134) admits a chart
  bundle in the @{thm charts_core_Nn} output shape.  This is the SOUND core: it
  RETAINS \<open>gradU = 0\<close> (codim 3), unlike the FALSE \<open>BadXW\<close> of D3charts/D3proof/
  D3Sound which DROPS it (codim 1 per fixed \<open>\<omega>\<close> \<Rightarrow> codim 0 = full measure over the
  1-D arc).

  \<^bold>\<open>WHY the det-HessU split (and NOT the unconditional \<open>Gjoint\<close>).\<close>  The
  alternative route (D3eng/D4eng) builds the joint map
  \<open>Gjoint = (gradU\<^sub>1, gradU\<^sub>2, mstarg) : (real^2)^'n \<times> real^2 \<to> real^3\<close> and asserts
  \<open>0\<close> is a regular value off a singular stratum \<open>\<Sigma>\<^sub>0\<close>.  But (repo M5_ENGINE_MAP.md,
  ``Chart crux'') the UNCONDITIONAL \<open>Gjoint\<close> submersion is FALSE, and D4eng's
  quarantine lemma @{text Sigma0_bad_charts} (no nondegeneracy hypotheses) is
  ``not credibly true''.  The SOUND route is to split the bad set on
  \<open>det (HessU)\<close>:

  \<^item> \<^bold>\<open>\<open>det HessU = 0\<close> part\<close>: \<open>{gradU = 0 \<and> det HessU = 0 \<and> \<not> surj (DM_paper_x)}\<close>.
    On this part the \<open>\<omega>\<close>-partial rank-drop \<open>=\<close> \<open>det HessU = 0\<close> via the VERIFIED
    bridge @{thm not_surj_omega_deriv_iff_detHess_dip} (Robust1:4245).  This is
    the \<open>charts_core_Nn[G = gradU]\<close> shape with param \<open>=\<close> codom \<open>= real^2\<close>: the
    heap engine fits AS-IS, no codomain generalization, no \<open>\<Sigma>\<^sub>0\<close>.  The remaining
    obstruction is the REGULAR VALUE of \<open>gradU\<close> on this part (it is NOT free: the
    bad locus has \<open>\<not> surj (DM_paper_x)\<close>, so the \<open>x\<close>-partial of \<open>gradU\<close> need not
    surject and @{thm regular_value_on_gradU_dip} does not apply directly).

  \<^item> \<^bold>\<open>\<open>det HessU \<noteq> 0\<close> part\<close>: \<open>{gradU = 0 \<and> det HessU \<noteq> 0 \<and> \<not> surj (DM_paper_x)}\<close>.
    Here the \<open>\<omega>\<close>-Hessian is invertible, so the IFT gives a \<open>C\<^sup>1\<close> graph
    \<open>\<omega> = \<omega>\<^sup>*(x)\<close> of critical points; the residual is the moment rank-drop
    \<open>\<not> surj (DM_paper_x x (cvec (\<omega>\<^sup>*(x))))\<close> ALONG that graph --- the genuine
    multi-week moment-rank transversality.

  \<^bold>\<open>The 1-D ARC dimension verdict (the prompt's crux).\<close>  The engine
  @{thm charts_core_Nn} is typed with parameter \<open>\<Omega> :: (real^2) set\<close> --- a 2-D
  \<open>\<omega>\<close>-set, NOT a scalar arc parameter \<open>t\<close>.  The arc \<open>\<gamma>\<close> is 1-D, but it is a SUBSET
  of the 2-D \<open>\<omega>\<close>-space \<open>real^2\<close>.  RESOLUTION: do NOT reparametrize by the scalar
  \<open>t\<close>; instead embed the arc into a 2-D open neighbourhood \<open>\<Omega>\<close> (e.g. the open
  steering-nondegenerate set, exactly as D4eng @{text branchP_indep_charts_Nn}
  does for the 2-D region) and run the SAME \<open>real^2\<close>-parameter engine.  The arc's
  1-dimensionality is then used ONLY in the soundness gate
  @{thm analytic_arc_negligible} and is irrelevant to the engine's typing.  So
  there is NO genuine 1-D-arc engine-dimension obstruction for the
  \<open>det HessU = 0\<close> half --- it reduces to the 2-D \<open>charts_core_Nn[gradU]\<close> over
  \<open>\<Omega> \<supseteq> \<gamma>\<close>, identical typing to D4.  (The false \<open>Gjoint\<close> route's ``scalar \<open>t\<close> vs
  \<open>real^3\<close> codomain'' non-square block is an ARTIFACT of that wrong route; the
  det-HessU split never forms it.)\<close>


subsection \<open>The \<open>C\<^sup>1\<close> analytic-arc predicate (verbatim from D3fix)\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> \<phi> C1_differentiable_on {a..b}
                          \<and> \<gamma> = \<phi> ` {a..b})"


subsection \<open>STEP 1 --- soundness gate: a \<open>C\<^sup>1\<close> arc in the plane is negligible (proof-complete)\<close>

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
  have dimlt: "DIM(real) < DIM(real^2)" by simp
  show ?thesis
    unfolding \<gamma>eq
    by (rule negligible_differentiable_image_lowdim[OF dimlt diffon])
qed


subsection \<open>The \<open>mstarg\<close> interface (Robust3-resident; LOCAL stubs, discharge at splice)\<close>

definition mstarg :: "(real^2) \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

lemma surj_iff_mstarg: "surj (DM_paper_x x c) \<longleftrightarrow> mstarg c x \<noteq> 0"
  \<comment> \<open>Robust3 splice fact (PROVEN at Robust3:578); stub here.\<close>
  sorry

lemma nowhere_dense_mstarg_zeros:
  fixes c :: "real^2"
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. mstarg c x = 0}"
  \<comment> \<open>Robust3 splice fact; stub here.\<close>
  sorry


subsection \<open>The SOUND bad \<open>x\<close>-set \<open>BadXWG\<close> (gradU=0 RETAINED) --- verbatim from D3fix\<close>

definition BadXWG :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXWG \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

lemma BadXWG_empty: "BadXWG \<omega>0 \<omega>s {} = ({} :: ((real^2)^'n) set)"
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


subsection \<open>The DET-HESSU SPLIT of the bad fibre (proof-complete set algebra)\<close>

text \<open>\<^bold>\<open>The split.\<close>  Every bad \<open>x\<close> is witnessed by some \<open>\<omega>\<in>\<gamma>\<close> at which either
  \<open>det (HessU) = 0\<close> or \<open>det (HessU) \<noteq> 0\<close>.  This partitions \<open>BadXWG\<close> into the two
  halves the design treats separately.  Pure logic on the witness; proof-complete.\<close>

definition BadXWG_H0 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXWG_H0 \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

definition BadXWG_Hn :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXWG_Hn \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

lemma BadXWG_detHess_split:
  fixes \<Gamma> :: "(real^2) set"
  shows "(BadXWG \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
           = BadXWG_H0 \<omega>0 \<omega>s \<Gamma> \<union> BadXWG_Hn \<omega>0 \<omega>s \<Gamma>"
  unfolding BadXWG_def BadXWG_H0_def BadXWG_Hn_def by blast


subsection \<open>\<section>A  The \<open>det HessU = 0\<close> half: \<open>charts_core_Nn[G = gradU]\<close> over \<open>\<Omega> \<supseteq> \<gamma>\<close>\<close>

text \<open>\<^bold>\<open>The \<open>\<omega>\<close>-partial bridge (proof-complete from the heap).\<close>  For \<open>\<omega>\<close> interior to an
  open \<open>\<Omega>\<close>, the engine's non-surjectivity test on the \<open>\<omega>\<close>-partial of \<open>gradU\<close> is
  LITERALLY \<open>det (HessU) = 0\<close> (@{thm not_surj_omega_deriv_iff_detHess_dip}).  This
  is what makes the \<open>det HessU = 0\<close> half land in \<open>charts_core_Nn[gradU]\<close>'s bad set
  WITHOUT any codomain-3 generalization.\<close>

lemma omega_partial_nonsurj_of_detHess0:
  fixes x :: "(real^2)^'n"
  assumes O: "open \<Omega>" and w: "\<omega> \<in> \<Omega>"
    and h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
  shows "\<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                  (at \<omega> within \<Omega>) \<and> surj D)"
  by (rule dip_slice_no_surj_deriv[OF O w h0])

text \<open>\<^bold>\<open>The engine bad set over \<open>\<Omega>\<close> (with \<open>G = gradU\<close>) CONTAINS the \<open>det HessU = 0\<close>
  half, provided \<open>\<gamma> \<subseteq> \<Omega>\<close> with \<open>\<Omega>\<close> OPEN.\<close>  At a witness \<open>\<omega>\<close> we have
  \<open>gradU(x,\<omega>) = 0\<close> (membership) and, since \<open>det HessU = 0\<close>, the \<open>\<omega>\<close>-partial of
  \<open>gradU\<close> at \<open>(x,\<omega>)\<close> fails to surject \<open>real^2\<close> (bridge above).  Hence \<open>x\<close> is in the
  abstract engine bad set.  Pure logic + the bridge; proof-complete.\<close>

lemma BadXWG_H0_subset_engine_bad:
  fixes V :: "((real^2)^'n) set" and \<gamma> \<Omega> :: "(real^2) set"
  assumes O: "open \<Omega>" and gsub: "\<gamma> \<subseteq> \<Omega>"
  shows "(V \<inter> BadXWG_H0 \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
           \<subseteq> {x\<in>V. \<exists>\<omega>\<in>\<Omega>.
                (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x,\<omega>) = 0 \<and>
                (\<not> (\<exists>D\<omega>. ((\<lambda>u. (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x,u))
                          has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}"
proof
  fix x :: "(real^2)^'n"
  assume "x \<in> V \<inter> BadXWG_H0 \<omega>0 \<omega>s \<gamma>"
  hence xV: "x \<in> V" and xH0: "x \<in> BadXWG_H0 \<omega>0 \<omega>s \<gamma>" by auto
  from xH0 obtain \<omega> where w\<gamma>: "\<omega> \<in> \<gamma>"
    and gU: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
    unfolding BadXWG_H0_def by blast
  have w\<Omega>: "\<omega> \<in> \<Omega>" using w\<gamma> gsub by blast
  have gU': "(\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x,\<omega>) = 0"
    using gU by simp
  have nos: "\<not> (\<exists>D\<omega>. ((\<lambda>u. (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x,u))
                       has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)"
    using omega_partial_nonsurj_of_detHess0[OF O w\<Omega> h0] by simp
  show "x \<in> {x\<in>V. \<exists>\<omega>\<in>\<Omega>.
              (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x,\<omega>) = 0 \<and>
              (\<not> (\<exists>D\<omega>. ((\<lambda>u. (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x,u))
                        has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}"
    using xV w\<Omega> gU' nos by blast
qed

text \<open>\<^bold>\<open>RESIDUAL A --- the regular value of \<open>gradU\<close> on the \<open>det HessU = 0\<close> half.\<close>
  To fire @{thm charts_core_Nn} with \<open>G = gradU\<close> we need \<open>0\<close> a regular value of
  \<open>gradU\<close> on an OPEN \<open>V \<times> \<Omega>\<close>.  @{thm regular_value_on_gradU_dip} supplies this ONLY
  on the locus \<open>{surj (DM_paper_x) \<and> det (Dcvec) \<noteq> 0 \<and> A \<noteq> 0}\<close> --- but the bad
  locus has \<open>\<not> surj (DM_paper_x)\<close>, so it does NOT apply there.  On the bad locus
  the \<open>x\<close>-partial of \<open>gradU\<close> need not be surjective (the converse
  \<open>\<not> surj (DM) \<Rightarrow> \<not> surj (x-partial)\<close> is NOT free; cf. D3eng honest caveat
  L302-310), and the \<open>\<omega>\<close>-partial is non-surjective exactly because
  \<open>det HessU = 0\<close>.  So \<open>0\<close> is in general NOT a regular value of \<open>gradU\<close> on the
  \<open>det HessU = 0\<close> bad locus, and the naive \<open>charts_core_Nn[gradU]\<close> call FAILS
  exactly here.

  This is the genuine residual of \<section>A, isolated as a precisely-scoped \<open>proof hole\<close>: the
  CHART BUNDLE of the \<open>det HessU = 0\<close> half directly (NOT via an unconditional
  regular value).  The honest content is a 2-jet / Morse-theoretic stratification
  of the degenerate-critical locus \<open>{gradU = 0 \<and> det HessU = 0}\<close>, intersected with
  the moment rank-drop \<open>\<not> surj (DM_paper_x)\<close>; the analogous 2-D heap result is
  @{thm meager_grad_x_regular_part} but that covers only the \<open>x\<close>-partial-SURJECTIVE
  sub-locus (\<open>= D1\<close>), NOT the \<open>\<not> surj\<close> bad locus here.\<close>

lemma BadXWG_H0_charts_Nn:
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
         (V \<inter> BadXWG_H0 \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>RESIDUAL A (codim \<open>\<ge> 2\<close>: \<open>gradU = 0 \<and> det HessU = 0\<close>, plus moment rank-drop):
      the chart bundle of the DEGENERATE-critical \<open>\<inter>\<close> moment-rank-drop locus over
      the arc.  The \<open>\<omega>\<close>-partial non-surjectivity is FREE (bridge
      @{thm not_surj_omega_deriv_iff_detHess_dip}), so this lands in the
      \<open>real^2\<close>-typed heap @{thm charts_core_Nn} shape with NO codomain
      generalization --- but the engine's REGULAR-VALUE hypothesis is NOT free on
      the \<open>\<not> surj (DM_paper_x)\<close> locus.  Genuine analytic content.  NOT a splice
      freebie.\<close>
  sorry


subsection \<open>\<section>B  The \<open>det HessU \<noteq> 0\<close> half: IFT graph \<open>\<omega> = \<omega>\<^sup>*(x)\<close> + moment rank-drop\<close>

text \<open>\<^bold>\<open>The IFT graph step (proof-complete reduction of the obligation).\<close>  On the
  \<open>det HessU \<noteq> 0\<close> half the \<open>\<omega>\<close>-Hessian \<open>(*v) (HessU \<dots> x \<omega>)\<close> is INVERTIBLE
  (@{thm surj_matrix_vector_iff_det}: \<open>det \<noteq> 0 \<Longrightarrow> surj \<Longrightarrow>\<close> bijective on \<open>real^2\<close>),
  so by the implicit function theorem applied to \<open>F (x,\<omega>) = gradU (\<dots>) x \<omega>\<close> at a
  critical \<open>(x\<^sub>0,\<omega>\<^sub>0)\<close> with invertible \<open>\<partial>\<^sub>\<omega>F\<close>, the critical set \<open>{gradU = 0}\<close> is
  LOCALLY a \<open>C\<^sup>1\<close> graph \<open>\<omega> = \<omega>\<^sup>*(x)\<close> over an \<open>x\<close>-neighbourhood.  The residual is the
  moment rank-drop \<open>\<not> surj (DM_paper_x x (cvec (\<omega>\<^sup>*(x))))\<close> ALONG that graph: a
  determinantal locus \<open>mstarg (cvec (\<omega>\<^sup>*(x))) x = 0\<close> in \<open>x\<close>-space \<open>(real^2)^'n\<close>
  (dim \<open>2N\<close>), which is the chart whose \<open>x\<close>-projection has non-surjective derivative.

  This half does NOT suffer the codim/engine-typing mismatch: it is a single \<open>C\<^sup>1\<close>
  graph (the IFT eliminates \<open>\<omega>\<close>), reducing to a moment-determinant chart in pure
  \<open>x\<close>-space.  The \<open>1\<close>-parameter arc enters only through the soundness gate (the arc
  is negligible), not through the graph.\<close>

text \<open>\<^bold>\<open>RESIDUAL B --- the moment-rank-drop chart along the IFT graph.\<close>  Isolated as a
  precisely-scoped \<open>proof hole\<close>.\<close>

lemma BadXWG_Hn_charts_Nn:
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
         (V \<inter> BadXWG_Hn \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>RESIDUAL B (\<open>det HessU \<noteq> 0\<close>): the \<open>\<omega>\<close>-Hessian is invertible, so the IFT gives a
      \<open>C\<^sup>1\<close> critical graph \<open>\<omega> = \<omega>\<^sup>*(x)\<close>; the chart is the moment rank-drop locus
      \<open>mstarg (cvec (\<omega>\<^sup>*(x))) x = 0\<close> along it.  Genuine moment-rank-drop
      transversality content.  NOT a splice freebie.\<close>
  sorry


subsection \<open>The chart bundle of \<open>BadXWG\<close> --- ASSEMBLED from the two halves (proof-complete)\<close>

text \<open>\<^bold>\<open>Bundle union (proof-complete).\<close>  Two \<open>charts_core_Nn\<close>-shape bundles, both indexed
  by \<open>nat\<close>, union into one by even/odd interleaving.  Copied verbatim from D4eng
  @{text charts_bundle_union}; mechanical.\<close>

lemma charts_bundle_union:
  fixes A B :: "((real^2)^'n) set"
    and chartsA chartsB :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and CritA CritB :: "nat \<Rightarrow> ((real^2)^'n) set"
    and DA DB :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
  assumes coverA: "A \<subseteq> (\<Union>i. (fst \<circ> chartsA i) ` (CritA i))"
    and derA: "\<forall>i x. x \<in> CritA i \<longrightarrow>
          ((fst \<circ> chartsA i) has_derivative (blinfun_apply (DA i x))) (at x within CritA i)"
    and rankA: "\<forall>i x. x \<in> CritA i \<longrightarrow> \<not> surj (blinfun_apply (DA i x))"
    and cloA: "\<forall>i. closed ((fst \<circ> chartsA i) ` (CritA i))"
    and coverB: "B \<subseteq> (\<Union>i. (fst \<circ> chartsB i) ` (CritB i))"
    and derB: "\<forall>i x. x \<in> CritB i \<longrightarrow>
          ((fst \<circ> chartsB i) has_derivative (blinfun_apply (DB i x))) (at x within CritB i)"
    and rankB: "\<forall>i x. x \<in> CritB i \<longrightarrow> \<not> surj (blinfun_apply (DB i x))"
    and cloB: "\<forall>i. closed ((fst \<circ> chartsB i) ` (CritB i))"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (A \<union> B) \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define charts where "charts i = (if even i then chartsA (i div 2) else chartsB (i div 2))" for i
  define Crit where "Crit i = (if even i then CritA (i div 2) else CritB (i div 2))" for i
  define D where "D i = (if even i then DA (i div 2) else DB (i div 2))" for i
  have piece: "(fst \<circ> charts i) ` (Crit i)
                 = (if even i then (fst \<circ> chartsA (i div 2)) ` (CritA (i div 2))
                              else (fst \<circ> chartsB (i div 2)) ` (CritB (i div 2)))" for i
    by (simp add: charts_def Crit_def)
  have UNeq: "(\<Union>i. (fst \<circ> charts i) ` (Crit i))
                = (\<Union>i. (fst \<circ> chartsA i) ` (CritA i)) \<union> (\<Union>i. (fst \<circ> chartsB i) ` (CritB i))"
  proof (intro equalityI subsetI)
    fix y assume "y \<in> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    then obtain i where "y \<in> (fst \<circ> charts i) ` (Crit i)" by blast
    thus "y \<in> (\<Union>i. (fst \<circ> chartsA i) ` (CritA i)) \<union> (\<Union>i. (fst \<circ> chartsB i) ` (CritB i))"
      using piece by (cases "even i") auto
  next
    fix y assume "y \<in> (\<Union>i. (fst \<circ> chartsA i) ` (CritA i)) \<union> (\<Union>i. (fst \<circ> chartsB i) ` (CritB i))"
    thus "y \<in> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    proof
      assume "y \<in> (\<Union>i. (fst \<circ> chartsA i) ` (CritA i))"
      then obtain i where yi: "y \<in> (fst \<circ> chartsA i) ` (CritA i)" by blast
      have eq: "(fst \<circ> charts (2*i)) ` (Crit (2*i)) = (fst \<circ> chartsA i) ` (CritA i)"
        by (simp add: charts_def Crit_def)
      have "y \<in> (fst \<circ> charts (2*i)) ` (Crit (2*i))" using yi eq by simp
      thus ?thesis by blast
    next
      assume "y \<in> (\<Union>i. (fst \<circ> chartsB i) ` (CritB i))"
      then obtain i where yi: "y \<in> (fst \<circ> chartsB i) ` (CritB i)" by blast
      have eq: "(fst \<circ> charts (2*i+1)) ` (Crit (2*i+1)) = (fst \<circ> chartsB i) ` (CritB i)"
        by (simp add: charts_def Crit_def)
      have "y \<in> (fst \<circ> charts (2*i+1)) ` (Crit (2*i+1))" using yi eq by simp
      thus ?thesis by blast
    qed
  qed
  show ?thesis
  proof (intro exI[where x = charts] exI[where x = Crit] exI[where x = D] conjI)
    show "(A \<union> B) \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      using coverA coverB UNeq by blast
  next
    show "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      by (auto simp: charts_def Crit_def D_def derA derB split: if_splits)
  next
    show "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      by (auto simp: charts_def Crit_def D_def rankA rankB split: if_splits)
  next
    show "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
      by (auto simp: piece cloA cloB)
  qed
qed

text \<open>\<^bold>\<open>The SOUND target, assembled proof-complete from RESIDUAL A + RESIDUAL B.\<close>  This is
  the file's main deliverable: \<open>excess_arc_charts_Nn\<close> (the canonical D3 core over
  \<open>BadXWG\<close>) reduced to exactly the two det-HessU residuals via the proof-complete
  split + union.  Everything between the two residuals and the target is mechanical.\<close>

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
proof -
  \<comment> \<open>Piece A: the \<open>det HessU = 0\<close> half (RESIDUAL A).\<close>
  obtain chartsA :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and CritA :: "nat \<Rightarrow> ((real^2)^'n) set"
     and DA :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where coverA: "(V \<inter> BadXWG_H0 \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                     \<subseteq> (\<Union>i. (fst \<circ> chartsA i) ` (CritA i))"
      and derA: "\<forall>i x. x \<in> CritA i \<longrightarrow>
            ((fst \<circ> chartsA i) has_derivative (blinfun_apply (DA i x))) (at x within CritA i)"
      and rankA: "\<forall>i x. x \<in> CritA i \<longrightarrow> \<not> surj (blinfun_apply (DA i x))"
      and cloA: "\<forall>i. closed ((fst \<circ> chartsA i) ` (CritA i))"
    using BadXWG_H0_charts_Nn[OF openV Vne c6 arc gsub pf nd] by (smt (verit, best))
  \<comment> \<open>Piece B: the \<open>det HessU \<noteq> 0\<close> half (RESIDUAL B).\<close>
  obtain chartsB :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and CritB :: "nat \<Rightarrow> ((real^2)^'n) set"
     and DB :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where coverB: "(V \<inter> BadXWG_Hn \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                     \<subseteq> (\<Union>i. (fst \<circ> chartsB i) ` (CritB i))"
      and derB: "\<forall>i x. x \<in> CritB i \<longrightarrow>
            ((fst \<circ> chartsB i) has_derivative (blinfun_apply (DB i x))) (at x within CritB i)"
      and rankB: "\<forall>i x. x \<in> CritB i \<longrightarrow> \<not> surj (blinfun_apply (DB i x))"
      and cloB: "\<forall>i. closed ((fst \<circ> chartsB i) ` (CritB i))"
    using BadXWG_Hn_charts_Nn[OF openV Vne c6 arc gsub pf nd] by (smt (verit, best))
  \<comment> \<open>Union the two bundles.  \<open>charts_bundle_union\<close> is applied with
       \<open>A = V \<inter> BadXWG_H0\<close>, \<open>B = V \<inter> BadXWG_Hn\<close> (the exact LHS of \<open>coverA\<close>/\<open>coverB\<close>),
       so NO \<open>Int_commute\<close> juggling is needed.\<close>
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where Ucover: "((V \<inter> BadXWG_H0 \<omega>0 \<omega>s \<gamma>) \<union> (V \<inter> BadXWG_Hn \<omega>0 \<omega>s \<gamma>) :: ((real^2)^'n) set)
                     \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and Uder: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and Urank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and Uclo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using charts_bundle_union[OF coverA derA rankA cloA coverB derB rankB cloB]
    by (smt (verit, best))
  \<comment> \<open>The full bad fibre is the union of the two halves (proof-complete split).\<close>
  have bad_eq: "(V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                  = (V \<inter> BadXWG_H0 \<omega>0 \<omega>s \<gamma>) \<union> (V \<inter> BadXWG_Hn \<omega>0 \<omega>s \<gamma>)"
    using BadXWG_detHess_split[of \<omega>0 \<omega>s \<gamma>] by blast
  have bad_in: "(V \<inter> BadXWG \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                  \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    using Ucover bad_eq by blast
  show ?thesis
    by (intro exI[where x = charts] exI[where x = Crit] exI[where x = D] conjI)
       (use bad_in Uder Urank Uclo in blast)+
qed


subsection \<open>The closed negligible cover + meagerness (proof-complete from the bundle)\<close>

text \<open>From here on the layers are gradU-agnostic and copied verbatim from D3fix:
  they consume the bundle abstractly through @{thm negligible_singular_image_2n}
  and @{thm meager_negligible_closed_cover}.  proof-complete given the bundle.\<close>

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
    by (rule meager_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

end
