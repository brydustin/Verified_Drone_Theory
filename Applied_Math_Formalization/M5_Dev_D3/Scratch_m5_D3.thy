theory Scratch_m5_D3
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) D3 --- the phase-collinear branch of the rank-deficient residual.\<close>

  This file closes the D3 leaf @{text m5_D34_D3_collinear} of the D34 residual
  (see \<open>M5_Dev_D34/Scratch_m5_D34.thy\<close>).  D3 is the \<^emph>\<open>phase-collinear\<close> branch:
  the part of the residual where the steering wavevector \<open>cvec_dip \<omega>0 \<omega>s \<omega>\<close> is
  collinear with the first steering-Jacobian column \<open>Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)\<close>.

  \<^bold>\<open>Mathematical content (diary D3).\<close>  The bad set is
    \<open>{x \<in> V. \<exists>\<omega>\<in>OmegaPF. gradU = 0 \<and> det Dcvec \<noteq> 0 \<and> cvec \<noteq> 0
        \<and> \<not> surj (DM_paper_x x (cvec \<omega>)) \<and> phase_collinear \<omega>0 \<omega>s \<omega>}\<close>.
  For each FIXED angle \<open>\<omega>\<close> the slice \<open>{x. \<not> surj (DM_paper_x x (cvec \<omega>))}\<close> is
  nowhere dense (the Robust3 \<open>mstarg\<close> fact, supplied abstractly as @{text nd}),
  hence meager.  The genuine difficulty is the passage from this PER-ANGLE
  meagerness to meagerness of the \<open>x\<close>-projection of the \<^bold>\<open>uncountable\<close> union over
  \<open>\<omega>\<in>OmegaPF\<close> (a cbox in \<open>real^2\<close>): a mere countable union does not apply.

  \<^bold>\<open>Engine (Sard-free "excess engine").\<close>  On the phase-collinear locus the bad
  \<open>(x,\<omega>)\<close> set is cut by the 3-equation / 2-parameter system (\<open>gradU = 0\<close> is two
  scalar equations, plus the rank-drop equation \<open>mstarg (cvec \<omega>) x = 0\<close>); the
  implicit-function theorem charts this excess locus as a union of
  \<open>(2N-1)\<close>-dimensional graphs whose \<open>x\<close>-projections are negligible (codimension
  read off the explicit chart, no regular-value count), assembled over the
  \<open>\<int>\<^sup>3\<close> phase-period lattice (window-finite by @{thm finite_affine_int_zeros}).
  Negligible \<open>\<Rightarrow>\<close> meager.

  \<^bold>\<open>Scaffold status.\<close>  All reduction / plumbing layers are proven proof-complete:
  \<^item> @{text fixed_c_nonsurj_nowhere_dense} --- Robust3-supplied (mstarg), the ONE
    \<^emph>\<open>freebie\<close> proof hole that closes automatically at the L970 splice site (replicated
    verbatim from D34, flagged freebie).
  \<^item> @{text fixed_omega_slice_meager} --- per-angle meagerness, proof-complete from
    @{text nd} (replicated from D34).
  \<^item> @{text m5_D34_subset_mstarg_residual} --- the structural reduction
    (replicated from D34), proof-complete.
  \<^item> @{text D3_excess_engine} --- the genuine analytic core: the ONE
    precisely-scoped \<^emph>\<open>math\<close> proof hole (the IFT-chart + \<open>\<int>\<^sup>3\<close>-lattice excess engine
    on the phase-collinear locus), with an exact statement and recommended route.
  \<^item> @{text m5_D34_D3_collinear} --- the D3 leaf, proven proof-complete FROM
    @{text D3_excess_engine} by a structural subset reduction.

  So the entire D3 obligation is reduced to the single excess-engine lemma; D4
  reuses the same engine (statement parametric in the dichotomy locus).\<close>


subsection \<open>The phase-collinear predicate (copied verbatim from D34)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>Robust3-supplied fixed-angle nowhere-density (freebie at splice)\<close>

text \<open>Replicated verbatim from D34.  PROVEN proof-complete in \<open>Nonemptiness_Robust3\<close>
  (in scope at the splice site): @{text surj_iff_mstarg} (L578) and
  @{text nowhere_dense_mstarg_zeros} (L744).  Here it is a single scoped proof hole
  that closes automatically at the L970 splice (a Robust3-resident freebie).\<close>

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  \<comment> \<open>Robust3: rewrite \<open>\<not>surj (DM_paper_x x c) = (mstarg c x = 0)\<close> via
      @{text surj_iff_mstarg}, then @{text nowhere_dense_mstarg_zeros}[OF c0 n6].
      Not available here because \<open>mstarg\<close> is defined in Robust3, above the splice
      site; in scope at the splice.  FREEBIE at splice.\<close>
  sorry


subsection \<open>The structural reduction (copied verbatim from D34)\<close>

text \<open>The full D34 bad set injects into the residual carrying only the geometric
  data the excess engine consumes.  Proven proof-complete.\<close>

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


subsection \<open>Per-angle slice meagerness (copied verbatim from D34)\<close>

text \<open>For a FIXED steering angle \<open>\<omega>\<close> with nonzero wavevector, the set of \<open>x\<close> at
  which \<open>DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)\<close> is not surjective is nowhere dense,
  hence meager.  proof-complete from the abstract input @{text nd}.\<close>

lemma fixed_omega_slice_meager:
  fixes \<omega> :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  by (rule meager_nowhere_dense[OF nd[OF c0]])


subsection \<open>The excess engine on the phase-collinear locus (one MATH proof hole)\<close>

text \<open>\<^bold>\<open>The genuine analytic core of D3.\<close>  This is the Sard-free "excess engine"
  specialised to the phase-collinear locus.  It states directly the meagerness
  of the \<open>x\<close>-projection of the uncountable union over \<open>\<omega>\<in>OmegaPF\<close> of the bad
  slices, on the phase-collinear locus, GIVEN the per-angle nowhere-density input
  @{text nd}.  All the surrounding structure (the reduction, the leaf statement)
  is proven proof-complete against this lemma; the lemma itself carries the single
  scoped MATH proof hole.

  \<^bold>\<open>Why this is the right cut.\<close>  The bad set of @{text m5_D34_D3_collinear} is a
  superset-trimmed instance of this engine's bad set: dropping the \<open>gradU = 0\<close>
  and \<open>det Dcvec \<noteq> 0\<close> conjuncts only enlarges the set, so D3 follows by
  @{thm meager_subset}.  Conversely the engine keeps exactly the data the IFT
  charts need: \<open>cvec \<noteq> 0\<close> (so \<open>mstarg (cvec \<omega>) x\<close> is a nontrivial polynomial in
  the moments), \<open>\<not> surj\<close> (= the rank-drop equation \<open>mstarg = 0\<close>), and
  \<open>phase_collinear\<close> (which collapses the \<open>\<gamma>\<close>-vs-\<open>c\<close> direction to a single scalar
  parameter, giving the 3-equation / 2-parameter excess count).

  \<^bold>\<open>Recommended route (multi-week math, ONE proof hole).\<close>
  \<^enum> Fix the phase-period lattice.  On \<open>OmegaPF\<close> the collinearity condition
    \<open>phase_collinear \<omega>0 \<omega>s \<omega>\<close> is, after clearing \<open>cvec_dip\<close>/\<open>Dcvec_dip\<close> by their
    explicit trigonometric forms (\<^const>\<open>cvec_dip\<close>, \<^const>\<open>Dcvec_dip\<close>), an analytic
    equation \<open>\<Theta>(\<omega>$1, \<omega>$2) = 0\<close>.  Its zero set inside the bounded box \<open>OmegaPF\<close> is
    covered by a FINITE set of analytic arcs indexed by the \<open>\<int>\<^sup>3\<close> phase period
    (window-finite: each transcendental factor \<open>cos\<close>/\<open>sin\<close>/\<open>a cos + b sin\<close> meets
    the box in finitely many points by @{thm finite_affine_int_zeros} /
    @{thm finite_cos_zeros_interval} / @{thm finite_phase_zeros_interval}).
  \<^enum> Chart the excess locus.  Over each arc, the bad \<open>(x,\<omega>)\<close> set lies in
    \<open>{(x,\<omega>). mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0}\<close>; the moment map \<open>x \<mapsto> M_paper x c\<close>
    is a submersion in \<open>x\<close> away from the nowhere-dense base (this is exactly the
    content of @{thm fixed_c_nonsurj_nowhere_dense} / the Robust3 \<open>mstarg\<close>
    machinery), so the implicit-function theorem charts the slice as a graph of
    codimension \<open>\<ge> 1\<close> in \<open>x\<close>.  Summing the (finite) \<open>\<omega>\<close>-arc parameter (dimension
    \<open>1\<close>) against the codimension gives a total \<open>(2N-1)\<close>-dimensional graph in the
    \<open>(x,\<omega>)\<close> excess space; its \<open>x\<close>-projection has measure zero (negligible).
  \<^enum> Assemble.  Negligible \<open>\<Rightarrow>\<close> meager (a negligible set in \<open>(real^2)^'n\<close> is meager
    since it has empty interior closure on each chart); the finite union over the
    lattice arcs is meager by @{thm meager_Union_finite}; the bad set injects into
    it by the subset above.  Mirror the flatten-conjugate-pullback skeleton of
    @{thm parametric_transversality_meager_planar_config}
    (\<open>\<Phi>\<close>/\<open>\<Psi>\<close> iso to \<open>real^('n bit0)\<close>, @{thm meager_homeo_image}) for the index
    bookkeeping; mirror @{thm meager_steering_singular_stratum} for the
    finite-witness-arc confinement.

  When spliced into Robust3, @{text nd} is the actual mstarg fact and this lemma
  is the lone genuine D3 obligation.\<close>

lemma D3_excess_engine:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
  \<comment> \<open>GENUINE MATH proof hole.  The Sard-free excess engine on the phase-collinear
      locus: IFT-chart \<open>(2N-1)\<close>-dim graphs over the \<open>\<int>\<^sup>3\<close> phase-period lattice,
      x-projection negligible \<Rightarrow> meager.  Route above.  Inputs available:
      @{text nd} (per-angle nowhere density), @{text c6}, @{text pf} (sin \<noteq> 0 on
      OmegaPF, so \<open>Dcvec\<close> second column nonzero \<Rightarrow> collinearity is one scalar
      equation), @{text d0}.  Not a splice freebie --- this is the real analysis.\<close>
  sorry


subsection \<open>The D3 leaf, proof-complete from the excess engine\<close>

text \<open>The exact target statement (verbatim from
  \<open>M5_Dev_D34/Scratch_m5_D34.thy\<close>, lemma @{text m5_D34_D3_collinear}).  The D3
  bad set is a subset of the excess engine's bad set (dropping \<open>gradU = 0\<close> and
  \<open>det Dcvec \<noteq> 0\<close> only enlarges the set), so it is meager by @{thm meager_subset}.
  Proven proof-complete from @{thm D3_excess_engine}.\<close>

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
proof -
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}
        \<subseteq> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub D3_excess_engine[OF openV Vne c6 d0 pf nd]])
qed

end
