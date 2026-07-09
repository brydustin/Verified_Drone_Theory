theory Scratch_m5_D34
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) stub D34 --- the residual rank-deficient stratum.\<close>

  This file closes the heavy stub @{text m5_D34_residual} of the M5 skeleton:
  the \<^emph>\<open>non-beam-center, det-nonsingular, NON-(x-partial-regular)\<close> residual of the
  rank-deficient stratum.  Per the diary it is the union of two diary pieces:
  \<^item> \<^bold>\<open>D3\<close> (phase-collinear branch): a 3-equation / 2-parameter "excess engine"
    (implicit-function-theorem charts \<rightarrow> \<open>(2N-1)\<close>-dim graphs with negligible
    \<open>x\<close>-projections, NO Sard needed) + a \<open>\<int>\<^sup>3\<close>-lattice union over phase-period integers.
  \<^item> \<^bold>\<open>D4\<close> (Branch-P residual): an explicit rank-drop dichotomy (\<open>\<gamma>\<close> parallel-or-not
    to \<open>c\<close>) + the excess engine on the \<open>(\<star>n)/Hess.u(w)\<close> rows.

  \<^bold>\<open>Scaffold status.\<close>  The assembly (D34 \<subseteq> D3 \<union> D4, each meager \<Rightarrow> union meager
  \<Rightarrow> subset meager) is proven here, proof-complete at the assembly layer.  The two
  internal pieces @{text m5_D34_D3_collinear} and @{text m5_D34_D4_branchP} are
  the genuine multi-week obligations and carry one precisely-scoped \<open>proof hole\<close> each
  (see @{text remaining_report}).  We also prove the structural \<^bold>\<open>reduction\<close>
  @{text m5_D34_subset_mstarg_residual}: the full D34 bad set injects into the
  smaller residual carrying only \<open>gradU = 0 \<and> det Dcvec \<noteq> 0 \<and> cvec \<noteq> 0 \<and>
  \<not> surj (DM_paper_x x c)\<close>, dropping the redundant \<open>det HessU = 0\<close>, \<open>A \<noteq> 0\<close>, and
  \<open>\<not> x-regular\<close> conjuncts.  This is the residual the excess engine actually
  consumes; the reduction is proven here with no proof hole, so the remaining
  mathematical content is isolated to the two excess-engine lemmas D3/D4.

  NOTE on the heap layer: the \<open>mstarg\<close> machinery (@{text surj_iff_mstarg},
  @{text nowhere_dense_mstarg_zeros}) that turns \<open>\<not>surj (DM_paper_x x c)\<close> into a
  nowhere-dense \<open>{x. mstarg c x = 0}\<close> lives in \<open>Nonemptiness_Robust3\<close> --- the
  same file as the M5 assembly, ABOVE it (mstarg at L572, the M5 lemma at L970) ---
  so it IS in scope when this proof is spliced into its home.  This dev file
  imports only \<open>Nonemptiness_Robust2\<close>, so those two facts are restated here as
  named local hypotheses fed to the inner lemmas (clearly flagged as
  "Robust3-supplied").\<close>


subsection \<open>The D3/D4 separating predicate (proof-internal)\<close>

text \<open>\<^bold>\<open>The phase-collinear predicate.\<close>  This is the proof-internal predicate that
  cuts the residual into the diary's two branches D3 (phase-collinear) and D4
  (Branch-P).  Per the diary, D4's rank-drop dichotomy is "\<open>\<gamma> \<parallel> c\<close> or not":
  the steering-phase gradient direction \<open>\<gamma>\<close> aligned (or not) with the wavevector
  \<open>c = cvec_dip \<omega>0 \<omega>s \<omega>\<close>.  We capture the \<^emph>\<open>phase-collinear\<close> branch concretely as
  collinearity of \<open>cvec_dip \<omega>0 \<omega>s \<omega>\<close> with the first steering-Jacobian column
  \<open>Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)\<close> (the \<open>\<gamma>\<close>-direction representative).  For the
  \<^emph>\<open>assembly\<close> this predicate only needs to be SOME boolean so that the
  excluded-middle cover \<open>D3 \<union> D4\<close> is exhaustive; the concrete geometric content is
  what the two inner lemmas exploit.\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>Local restatements of the Robust3-supplied moment-map facts\<close>

text \<open>These two are PROVEN proof-complete in \<open>Nonemptiness_Robust3\<close> (in scope at the
  splice site): @{text surj_iff_mstarg} (L578) and @{text nowhere_dense_mstarg_zeros}
  (L744).  We package them as a locale-free abstraction \<open>regzero\<close> so the D3/D4
  inner lemmas are stated against an ABSTRACT "non-regular set is nowhere dense
  per fixed nonzero c" predicate.  In the splice these become the actual mstarg
  lemmas; here they are the named obligations the engine rests on.\<close>

text \<open>The abstract fixed-angle nowhere-density input the excess engine needs:
  for every nonzero \<open>c\<close>, the set of \<open>x\<close> at which \<open>DM_paper_x x c\<close> is not surjective
  is nowhere dense.  (= @{text "nowhere_dense_mstarg_zeros"} composed with
  @{text "surj_iff_mstarg"} in Robust3.)\<close>

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  \<comment> \<open>Robust3: rewrite \<open>\<not>surj (DM_paper_x x c) = (mstarg c x = 0)\<close> via
      @{text surj_iff_mstarg}, then @{text nowhere_dense_mstarg_zeros}[OF c0 n6].
      Not available here because \<open>mstarg\<close> is defined in Robust3, above the splice
      site; in scope at the splice.\<close>
  sorry


subsection \<open>The structural reduction: drop the redundant conjuncts\<close>

text \<open>The full D34 bad set injects into the residual carrying only the geometric
  data the excess engine actually consumes: \<open>gradU = 0\<close> (the critical-point
  equation), \<open>det Dcvec \<noteq> 0\<close> (the steering-nonsingular geometry), \<open>cvec \<noteq> 0\<close>,
  and \<open>\<not> surj (DM_paper_x x cvec)\<close> (the moment-map rank-drop = the nowhere-dense
  input).  The conjuncts \<open>det HessU = 0\<close>, \<open>A \<noteq> 0\<close>, and the \<open>\<not> x-regular\<close>
  existential are dropped (they only enlarge the set).  Proven proof-complete.\<close>

lemma m5_D34_subset_mstarg_residual:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  shows "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}
        \<subseteq> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  by blast


subsection \<open>Proven building block: the fixed-angle slice is nowhere dense\<close>

text \<open>For a FIXED steering angle \<open>\<omega>\<close> with nonzero wavevector \<open>cvec_dip \<omega>0 \<omega>s \<omega>\<close>,
  the set of \<open>x\<close> at which the moment-map derivative \<open>DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)\<close>
  is not surjective is nowhere dense --- hence meager.  This is the per-angle
  payload of the excess engine, derived proof-complete from the abstract input
  @{text nd} (the Robust3 \<open>mstarg\<close> fact).  The genuine remaining work in D3/D4 is
  precisely the passage from this PER-ANGLE meagerness to meagerness of the
  UNCOUNTABLE \<open>x\<close>-projection \<open>\<Union>\<^bsub>\<omega>\<in>OmegaPF\<^esub>\<close> of the slices --- which needs the
  excess engine (IFT charts + lattice / dichotomy), NOT a mere countable union.\<close>

lemma fixed_omega_slice_meager:
  fixes \<omega> :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  by (rule meager_nowhere_dense[OF nd[OF c0]])


subsection \<open>D3 --- the phase-collinear branch (one scoped proof hole)\<close>

text \<open>The phase-collinear branch of the residual.  Internally: the 3-equation /
  2-parameter excess engine produces \<open>(2N-1)\<close>-dim IFT graphs whose \<open>x\<close>-projections
  are negligible, unioned over the \<open>\<int>\<^sup>3\<close> phase-period lattice (window-finite by
  @{thm finite_affine_int_zeros}).  No Sard.  Here we carry the resulting
  meagerness as a single scoped \<open>proof hole\<close> and feed it the abstract
  @{thm fixed_c_nonsurj_nowhere_dense} input.\<close>

lemma m5_D34_D3_collinear:
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
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
  sorry


subsection \<open>D4 --- the Branch-P residual (one scoped proof hole)\<close>

text \<open>The Branch-P residual: the complementary (non phase-collinear) part.
  Internally: the explicit rank-drop dichotomy (\<open>\<gamma> \<parallel> c\<close> or not) plus the excess
  engine on the \<open>(\<star>n)/Hess.u(w)\<close> rows.  \<open>core_3d\<close> is ruled out structurally (the
  gradU rows degenerate exactly at the residual witnesses), so a dedicated
  stratification is required.  Carried as a single scoped \<open>proof hole\<close>.\<close>

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
  sorry


subsection \<open>Assembly: \<open>m5_D34_residual\<close> from the reduction + D3 + D4\<close>

text \<open>The exact target statement (verbatim from the M5 skeleton), closed by:
  the structural reduction @{thm m5_D34_subset_mstarg_residual}, the
  excluded-middle split of the residual on the proof-internal predicate
  @{const phase_collinear} into D3 \<union> D4, the two inner meagerness lemmas, and
  @{thm meager_subset} / @{thm meager_Un}.  proof-complete at this assembly layer.\<close>

lemma m5_D34_residual:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  \<comment> \<open>The Robust3-supplied fixed-angle nowhere-density (here a single scoped proof hole).\<close>
  have nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    by (rule fixed_c_nonsurj_nowhere_dense[OF _ c6])
  \<comment> \<open>The residual the excess engine consumes (gradU = 0, det Dcvec \<noteq> 0,
       cvec \<noteq> 0, DM not surjective).\<close>
  let ?R = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  let ?D3 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
  let ?D4 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  \<comment> \<open>The residual is the D3/D4 union (excluded middle on \<open>phase_collinear\<close>).\<close>
  have RsubD: "?R \<subseteq> ?D3 \<union> ?D4" by blast
  \<comment> \<open>Each piece is meager (the two genuine obligations, stubbed inside).\<close>
  have mD3: "meager ?D3" by (rule m5_D34_D3_collinear[OF openV Vne c6 d0 pf nd])
  have mD4: "meager ?D4" by (rule m5_D34_D4_branchP[OF openV Vne c6 d0 pf nd])
  have mR: "meager ?R"
    by (rule meager_subset[OF RsubD meager_Un[OF mD3 mD4]])
  \<comment> \<open>The full D34 bad set injects into the residual (structural reduction).\<close>
  show ?thesis
    by (rule meager_subset[OF m5_D34_subset_mstarg_residual mR])
qed

end
