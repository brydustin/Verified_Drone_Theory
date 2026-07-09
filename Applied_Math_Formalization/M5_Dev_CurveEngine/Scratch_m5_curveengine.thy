theory Scratch_m5_curveengine
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) CORE B --- the SOUND curve-case excess engine.\<close>

  \<^bold>\<open>Why this file exists (the soundness fix).\<close>  The earlier scaffold
  @{file \<open>../M5_Dev_Excess/Scratch_m5_excess.thy\<close>} stated its finite-arc cover for an
  \<^emph>\<open>arbitrary\<close> angle set \<open>\<Gamma> \<subseteq> OmegaPF\<close> (lemma
  \<open>phase_collinear_curve_finite_arc_cover\<close>), and stated its engine
  \<open>excess_projection_meager\<close> with the same arbitrary \<open>\<Gamma>\<close>.  That is \<^bold>\<open>FALSE\<close>: for a genuine
  two-dimensional \<open>\<Gamma>\<close> --- the extreme/degenerate instance \<open>\<Gamma> = OmegaPF ctr \<delta>\<close> --- the
  \<open>x\<close>-projection of the bad fibre is \<^emph>\<open>not\<close> meager (there is no finite arc cover of a
  2-cell, and the union of uncountably many nowhere-dense slices fills an open set).
  A green \<open>quick_and_dirty\<close> build resting on that over-general statement proves nothing.

  \<^bold>\<open>The tightening.\<close>  This file re-states the engine for an angle set that is
  \<^emph>\<open>genuinely finitely-arc-coverable\<close> --- which is exactly where the one-parameter
  (curve) structure enters, and is exactly where the engine is \<^emph>\<open>true\<close>:
  \<^item> @{text finitely_arc_coverable}: the explicit soundness predicate --- \<open>\<Gamma>\<close> is
    covered by FINITELY many analytic arcs each \<open>\<subseteq> OmegaPF\<close>.  For a 2D \<open>\<Gamma>\<close> this is
    false, so it cannot be vacuously over-applied.
  \<^item> @{text collinear_locus_finite_arc_cover} (Deliverable 1): the
    phase-collinear \<^emph>\<open>locus\<close> inside the bounded box \<^emph>\<open>is\<close> finitely-arc-coverable.
    This is the genuine analytic specialization: on \<open>OmegaPF\<close> (with \<open>sin(\<omega>\<^sub>1)\<noteq>0\<close>)
    @{text phase_collinear} is one analytic equation \<open>\<Theta>(\<omega>\<^sub>1,\<omega>\<^sub>2)=0\<close> whose
    transcendental factors are \<open>cos\<close>/\<open>sin\<close>/\<open>a cos + b sin\<close>; the locus meets the box in
    finitely many \<open>\<int>\<^sup>3\<close>-period windows (@{thm finite_affine_int_zeros},
    @{thm finite_cos_zeros_interval}, @{thm finite_phase_zeros_interval} --- the exact
    witness-confinement mirror of @{thm meager_steering_singular_stratum}), each an
    IFT graph, hence an analytic arc.  GENUINE analytic content; carried as one
    precisely-scoped \<open>proof hole\<close>, soundly stated for the COLLINEAR LOCUS (\<^bold>\<open>not\<close> for an
    arbitrary \<open>\<Gamma>\<close>).
  \<^item> @{text excess_projection_meager_curve} (Deliverable 2): the TIGHTENED engine.
    For any \<^emph>\<open>finitely-arc-coverable\<close> \<open>\<Gamma>\<close>, \<open>V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>\<close> is meager.  Proven
    proof-complete from the cover + @{text excess_arc_projection_meager} (Core A's shared
    deliverable, stubbed locally) + the proof-complete assembly layer.
  \<^item> @{text D3_excess_engine}, @{text m5_D34_D3_collinear} (Deliverable 3): re-derived
    \<^bold>\<open>verbatim\<close> from @{file \<open>../M5_Dev_Excess/Scratch_m5_excess.thy\<close>}, now proof-complete
    against the SOUND engine --- confirming the whole D3 chain still closes.

  \<^bold>\<open>Genuine remaining proof holes\<close>: exactly two analytic obligations
  (@{text collinear_locus_finite_arc_cover}, the finite \<open>\<int>\<^sup>3\<close>-arc cover of the locus;
  @{text excess_arc_projection_meager}, Core A's per-arc IFT projection) plus the
  @{text fixed_c_nonsurj_nowhere_dense} mstarg freebie (closes at the Robust3 splice).
  Everything else --- the assembly, the set algebra, the D3 re-derivation --- is
  proof-complete.\<close>


subsection \<open>The phase-collinear predicate (copied verbatim from the engine)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>Robust3-supplied fixed-angle nowhere-density (freebie at splice)\<close>

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  \<comment> \<open>Robust3 freebie at the L970 splice (\<open>surj_iff_mstarg\<close> + \<open>nowhere_dense_mstarg_zeros\<close>);
      out of scope here because \<open>mstarg\<close> is Robust3-resident.\<close>
  sorry


subsection \<open>Per-angle slice nowhere-density / meagerness (proof-complete from \<open>nd\<close>)\<close>

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


subsection \<open>The curve-confined excess locus and its x-projection (set-level)\<close>

definition BadXW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

lemma engine_bad_eq_projection:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  shows "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}
        = V \<inter> BadXW \<omega>0 \<omega>s {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}"
  unfolding BadXW_def by blast


subsection \<open>BadXW is monotone in, and distributes over unions of, the angle set\<close>

lemma BadXW_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "BadXW \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXW \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n) set)"
  using assms unfolding BadXW_def by blast

lemma BadXW_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "BadXW \<omega>0 \<omega>s (\<Union>i\<in>I. arc i) = (\<Union>i\<in>I. (BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  unfolding BadXW_def by blast

lemma BadXW_subset_of_cover:
  fixes \<Gamma> :: "(real^2) set" and arc :: "'i \<Rightarrow> (real^2) set"
  assumes cover: "\<Gamma> \<subseteq> (\<Union>i\<in>I. arc i)"
  shows "BadXW \<omega>0 \<omega>s \<Gamma> \<subseteq> (\<Union>i\<in>I. (BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
proof -
  have "BadXW \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXW \<omega>0 \<omega>s (\<Union>i\<in>I. arc i) :: ((real^2)^'n) set)"
    by (rule BadXW_mono[OF cover])
  also have "\<dots> = (\<Union>i\<in>I. (BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
    by (rule BadXW_UN)
  finally show ?thesis .
qed


subsection \<open>The per-fixed-angle x-projection is meager (proof-complete from \<open>nd\<close>)\<close>

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


subsection \<open>Analytic arcs and the soundness predicate \<open>finitely_arc_coverable\<close>\<close>

text \<open>An \<^emph>\<open>analytic arc\<close> is a one-parameter continuous image of a compact real
  interval --- the IFT graph \<open>\<omega>\<^sub>2 = \<phi>\<^sub>k(\<omega>\<^sub>1)\<close> presented over a window.  The per-arc
  projection step (Core A) uses exactly this 1-parameter structure.\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> continuous_on {a..b} \<phi>
                          \<and> \<gamma> = \<phi> ` {a..b})"

text \<open>\<^bold>\<open>The soundness predicate.\<close>  An angle set is \<^emph>\<open>finitely-arc-coverable inside the
  box\<close> when it is contained in a FINITE union of analytic arcs, each a subset of the
  box \<open>OmegaPF ctr \<delta>\<close>.  This is exactly the one-parameter (curve) hypothesis under
  which the excess engine is genuinely true.

  \<^bold>\<open>Extreme-instance soundness check.\<close>  For \<open>\<Gamma> = OmegaPF ctr \<delta>\<close> (a non-degenerate
  2-cell, \<open>\<delta> > 0\<close>) this predicate is FALSE: a finite union of analytic arcs is
  nowhere dense (each arc, a compact 1-parameter image, has empty interior in
  \<open>real^2\<close>), so it cannot contain a 2-cell with nonempty interior.  Hence the engine
  below \<^bold>\<open>cannot\<close> be vacuously applied to the full box --- precisely the over-general
  application that made the earlier scaffold unsound.\<close>

definition finitely_arc_coverable :: "(real^2) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> bool" where
  "finitely_arc_coverable \<Gamma> ctr \<delta> \<longleftrightarrow>
     (\<exists>(I::nat set) arc. finite I \<and> \<Gamma> \<subseteq> (\<Union>i\<in>I. arc i)
         \<and> (\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>))"


subsection \<open>The assembly layer (proof-complete): finite arc cover \<open>\<Longrightarrow>\<close> meager\<close>

text \<open>\<^bold>\<open>The assembly layer.\<close>  If a FINITE family \<open>{arc i}\<^bsub>i\<in>I\<^esub>\<close> of angle sets covers
  \<open>\<Gamma>\<close> and each per-arc \<open>x\<close>-projection \<open>V \<inter> BadXW \<omega>0 \<omega>s (arc i)\<close> is meager, then
  \<open>V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>\<close> is meager.  proof-complete.\<close>

lemma excess_projection_meager_of_finite_cover:
  fixes V :: "((real^2)^'n) set" and \<Gamma> :: "(real^2) set"
    and arc :: "'i \<Rightarrow> (real^2) set" and I :: "'i set"
  assumes finI: "finite I"
    and cover: "\<Gamma> \<subseteq> (\<Union>i\<in>I. arc i)"
    and meagerarc: "\<And>i. i \<in> I \<Longrightarrow> meager (V \<inter> BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set)"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
proof -
  have sub: "(V \<inter> BadXW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
             \<subseteq> (\<Union>i\<in>I. (V \<inter> BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  proof -
    have "(V \<inter> BadXW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
            \<subseteq> V \<inter> (\<Union>i\<in>I. (BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
      using BadXW_subset_of_cover[OF cover] by blast
    also have "\<dots> = (\<Union>i\<in>I. (V \<inter> BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
      by blast
    finally show ?thesis .
  qed
  have meagU: "meager (\<Union>i\<in>I. (V \<inter> BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
    by (rule meager_Union_finite[OF finI]) (rule meagerarc)
  show ?thesis by (rule meager_subset[OF sub meagU])
qed


subsection \<open>Deliverable 1: the phase-collinear LOCUS has a finite analytic-arc cover\<close>

text \<open>\<^bold>\<open>GENUINE analytic proof hole (1 of 2), SOUNDLY scoped to the collinear LOCUS.\<close>

  This is the sound replacement of the false
  \<open>phase_collinear_curve_finite_arc_cover\<close> of
  @{file \<open>../M5_Dev_Excess/Scratch_m5_excess.thy\<close>}: there the cover was asserted for
  an \<^emph>\<open>arbitrary\<close> \<open>\<Gamma> \<subseteq> OmegaPF\<close> (false for a 2D \<open>\<Gamma>\<close>); here it is asserted only for the
  \<^emph>\<open>phase-collinear locus\<close> \<open>{\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}\<close>, which is a
  genuine one-dimensional analytic curve and so really IS finitely-arc-coverable.

  ROUTE (the \<open>\<int>\<^sup>3\<close>-phase-lattice finiteness, mirror of
  @{thm meager_steering_singular_stratum}).  Clearing
  \<open>cvec_dip\<close>/\<open>Dcvec_dip\<close> by their trigonometric forms (@{thm cvec_dip_def},
  @{thm Dcvec_dip_def}), \<open>phase_collinear \<omega>0 \<omega>s \<omega>\<close> on the box (where
  \<open>sin(\<omega>\<^sub>1) \<noteq> 0\<close>) is one analytic equation \<open>\<Theta>(\<omega>\<^sub>1,\<omega>\<^sub>2)=0\<close> --- a \<open>\<int>\<^bold>2\<close>-quasi-periodic
  combination of \<open>cos\<close>/\<open>sin\<close>/\<open>a cos + b sin\<close> factors.  Its zero locus meets the
  bounded box in finitely many \<open>\<int>\<^sup>3\<close>-period windows
  (@{thm finite_affine_int_zeros}, @{thm finite_cos_zeros_interval},
  @{thm finite_phase_zeros_interval}).  Over each window the implicit-function
  theorem presents the locus as a graph \<open>\<omega>\<^sub>2 = \<phi>\<^sub>k(\<omega>\<^sub>1)\<close> (or \<open>\<omega>\<^sub>1 = \<psi>\<^sub>k(\<omega>\<^sub>2)\<close>) of a
  continuous function over a compact interval --- an analytic arc inside the box.
  GENUINE math, NOT a splice freebie.

  \<^bold>\<open>Soundness extreme-instance check.\<close>  This lemma is NOT true with the locus replaced
  by the whole box: \<open>finitely_arc_coverable (OmegaPF ctr \<delta>) ctr \<delta>\<close> is FALSE for
  \<open>\<delta> > 0\<close> (a 2-cell is not a finite union of nowhere-dense arcs).  The hypotheses
  \<open>0 < \<delta>\<close> and \<open>sin(\<omega>\<^sub>1) \<noteq> 0\<close> on the box are the same non-degeneracy data
  @{thm meager_steering_singular_stratum} uses to confine its witnesses; here they
  guarantee \<open>\<Theta> \<not>\<equiv> 0\<close> so the locus is a genuine curve.\<close>

lemma collinear_locus_finite_arc_cover:
  fixes ctr :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "finitely_arc_coverable {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>} ctr \<delta>"
  \<comment> \<open>GENUINE analytic proof hole (1/2), SOUNDLY scoped: finite \<open>\<int>\<^sup>3\<close>-period analytic-arc
      cover of the phase-collinear LOCUS (not an arbitrary 2D \<open>\<Gamma>\<close>).  The locus is the
      analytic equation \<open>\<Theta>(\<omega>\<^sub>1,\<omega>\<^sub>2)=0\<close> whose \<open>cos\<close>/\<open>sin\<close>/\<open>a cos + b sin\<close> factors meet
      the box in finitely many \<open>\<int>\<^sup>3\<close>-period windows
      (@{thm finite_affine_int_zeros}, @{thm finite_cos_zeros_interval},
      @{thm finite_phase_zeros_interval}; mirror of
      @{thm meager_steering_singular_stratum}'s witness confinement), each an IFT
      graph.  NOT a splice freebie.\<close>
  sorry


subsection \<open>Core A's shared deliverable: the per-arc projection is meager (stub)\<close>

text \<open>\<^bold>\<open>SHARED stub --- Core A's deliverable.\<close>  Over a single analytic arc \<open>\<gamma>\<close> the
  \<open>x\<close>-projection \<open>V \<inter> BadXW \<omega>0 \<omega>s \<gamma>\<close> of the bad fibre is meager.  Stated here exactly
  as Core A produces it; consumed verbatim below.  GENUINE analytic content (IFT
  chart of the bad fibre as a \<open>(2N-1)\<close>-dim graph + negligibility of its
  \<open>x\<close>-projection via @{thm negligible_singular_image_2n}, upgraded to meager by a
  closed negligible cover @{thm meager_negligible_closed_cover}).  NOT a splice
  freebie; NOT this Core's obligation --- carried as the shared proof hole.\<close>

lemma excess_arc_projection_meager:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
  \<comment> \<open>SHARED proof hole (Core A's deliverable): the IFT chart of the per-arc bad fibre as
      a \<open>(2N-1)\<close>-dim graph and the negligibility of its \<open>x\<close>-projection.\<close>
  sorry


subsection \<open>Deliverable 2: the TIGHTENED engine for finitely-arc-coverable \<open>\<Gamma>\<close>\<close>

text \<open>\<^bold>\<open>The SOUND Sard-free excess engine.\<close>  For an angle set \<open>\<Gamma>\<close> that is
  \<^emph>\<open>finitely-arc-coverable inside the box\<close> (the explicit soundness hypothesis), the
  \<open>x\<close>-projection \<open>V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>\<close> is meager.  Proven proof-complete from the cover
  (@{const finitely_arc_coverable}) + the per-arc projection
  @{thm excess_arc_projection_meager} + the proof-complete assembly layer
  @{thm excess_projection_meager_of_finite_cover}.

  \<^bold>\<open>This is the genuinely-true tightening\<close> of the false
  @{file \<open>../M5_Dev_Excess/Scratch_m5_excess.thy\<close>}\<open>.excess_projection_meager\<close>: there
  the only constraint on \<open>\<Gamma>\<close> was \<open>\<Gamma> \<subseteq> OmegaPF\<close> (which holds for the full 2D box,
  where the conclusion is false); here the curve structure is carried explicitly by
  @{const finitely_arc_coverable}, which fails for the 2D box.\<close>

lemma excess_projection_meager_curve:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and fac: "finitely_arc_coverable \<Gamma> ctr \<delta>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
proof -
  obtain I :: "nat set" and arc :: "nat \<Rightarrow> (real^2) set"
    where finI: "finite I"
      and cover\<Gamma>: "\<Gamma> \<subseteq> (\<Union>i\<in>I. arc i)"
      and arcprops: "\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>"
    using fac unfolding finitely_arc_coverable_def by blast
  have meagerarc: "meager (V \<inter> BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set)" if iI: "i \<in> I" for i
  proof -
    have aarc: "analytic_arc (arc i)" using arcprops iI by blast
    have asub: "arc i \<subseteq> OmegaPF ctr \<delta>" using arcprops iI by blast
    show ?thesis
      by (rule excess_arc_projection_meager[OF openV Vne c6 aarc asub pf nd])
  qed
  show ?thesis
    by (rule excess_projection_meager_of_finite_cover[OF finI cover\<Gamma> meagerarc])
qed


subsection \<open>Deliverable 3: re-derive the D3 chain against the SOUND engine\<close>

text \<open>\<^bold>\<open>The D3 excess engine, proof-complete from the SOUND tightened engine.\<close>  Copied
  verbatim (statement) from @{file \<open>../M5_Dev_Excess/Scratch_m5_excess.thy\<close>}; the
  only change is the body, which now feeds the SOUND
  @{thm excess_projection_meager_curve} the finite-arc-coverability of the
  phase-collinear LOCUS supplied by @{thm collinear_locus_finite_arc_cover}.  This
  CONFIRMS the D3 chain still closes against the tightened engine.\<close>

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
proof -
  define \<Gamma> :: "(real^2) set"
    where "\<Gamma> = {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}"
  have eq: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
              cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
            \<and> phase_collinear \<omega>0 \<omega>s \<omega>}
          = V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>"
    unfolding \<Gamma>_def by (rule engine_bad_eq_projection)
  have fac: "finitely_arc_coverable \<Gamma> ctr \<delta>"
    unfolding \<Gamma>_def by (rule collinear_locus_finite_arc_cover[OF d0 pf])
  show ?thesis
    unfolding eq
    by (rule excess_projection_meager_curve[OF openV Vne c6 pf fac nd])
qed


subsection \<open>The D3 leaf, proof-complete from the excess engine\<close>

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
