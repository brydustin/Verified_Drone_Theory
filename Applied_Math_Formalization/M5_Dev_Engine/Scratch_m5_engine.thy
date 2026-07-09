theory Scratch_m5_engine
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) D3/D4 --- the Sard-free excess engine.\<close>

  This file builds the \<^emph>\<open>excess engine\<close> scaffold that unlocks BOTH D3
  (@{text m5_D34_D3_collinear}, the phase-collinear branch) and D4
  (@{text m5_D34_D4_branchP}, the complementary branch).  It is the genuine
  analytic core of M5 (@{text meager_rank_deficient_stratum}).

  \<^bold>\<open>The obligation.\<close>  For an open nonempty configuration window \<open>V\<close> and the steered
  dipole wavevector \<open>cvec_dip \<omega>0 \<omega>s \<omega>\<close>, prove

    \<open>meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> phase_collinear \<omega>0 \<omega>s \<omega>}\<close>

  given, abstractly, the per-angle nowhere-density input
    \<open>nd : \<And>c. c \<noteq> 0 \<Longrightarrow> nowhere_dense {x. \<not> surj (DM_paper_x x c)}\<close>
  (the Robust3 \<open>mstarg\<close> fact, supplied at the splice site).

  \<^bold>\<open>Why it is hard (the irreducible core).\<close>  For each \<^emph>\<open>fixed\<close> angle \<open>\<omega>\<close> the bad
  \<open>x\<close>-slice \<open>{x. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}\<close> is nowhere dense
  (hence meager) by @{text nd}.  But the bad set is the \<open>x\<close>-projection of the
  \<^bold>\<open>uncountable\<close> union over \<open>\<omega>\<close> in a one-parameter analytic curve
  \<open>\<Gamma> = {\<omega>\<in>OmegaPF. phase_collinear \<omega>0 \<omega>s \<omega>}\<close> of those slices.  A countable-union
  argument (@{thm meager_Union_finite} / @{thm meager_Un}) does \<^bold>\<open>not\<close> apply: the
  union is over a continuum of angles.  This is exactly the gap that the Sard-free
  excess engine fills.

  \<^bold>\<open>Engine architecture (this file).\<close>  We split the obligation into:
  \<^enum> @{text engine_bad_subset_projection} --- a proof-complete SET-LEVEL reduction:
    the bad set injects into the \<open>x\<close>-projection of the curve-confined excess locus
    \<open>BadXW \<Gamma> = {x. \<exists>\<omega>\<in>\<Gamma>. cvec \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec \<omega>))}\<close> over the
    phase-collinear angle curve \<open>\<Gamma>\<close>.
  \<^enum> @{text fixed_omega_slice_nowhere_dense} / @{text fixed_omega_slice_meager} ---
    proof-complete per-angle nowhere-density / meagerness from @{text nd}.
  \<^enum> @{text excess_projection_meager} --- the ONE genuine MATH proof hole: meagerness of
    the \<open>x\<close>-projection of the curve-confined excess locus.  This is the IFT-chart +
    \<open>\<int>\<^sup>3\<close>-phase-lattice negligibility engine.  Stated \<^bold>\<open>parametrically\<close> in the angle
    set \<open>\<Gamma>\<close> (any subset of \<open>OmegaPF\<close>) so that D4 reuses it verbatim with the
    complementary curve.  Recommended route attached.
  \<^enum> @{text D3_excess_engine} --- the D3 target, proof-complete from (1)+(3).
  \<^enum> @{text m5_D34_D3_collinear} --- the verbatim D3 leaf, proof-complete from
    @{text D3_excess_engine} by @{thm meager_subset}.

  So the entire D3 (and, by reuse, D4) obligation is reduced to the single
  abstract lemma @{text excess_projection_meager}.\<close>


subsection \<open>The phase-collinear predicate (copied verbatim from D34/D3)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>Robust3-supplied fixed-angle nowhere-density (freebie at splice)\<close>

text \<open>Replicated verbatim from D34/D3.  PROVEN proof-complete in
  \<open>Nonemptiness_Robust3\<close> (in scope at the splice site): @{text surj_iff_mstarg}
  (L578) and @{text nowhere_dense_mstarg_zeros} (L744).  Here it is a single
  scoped proof hole that closes automatically at the L970 splice (a Robust3-resident
  freebie).  In the engine proper this fact is consumed only \<^emph>\<open>through\<close> the
  abstract hypothesis @{text nd}, never directly.\<close>

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  \<comment> \<open>Robust3: rewrite \<open>\<not>surj (DM_paper_x x c) = (mstarg c x = 0)\<close> via
      @{text surj_iff_mstarg}, then @{text nowhere_dense_mstarg_zeros}[OF c0 n6].
      Not available here because \<open>mstarg\<close> is defined in Robust3, above the splice
      site; in scope at the splice.  FREEBIE at splice.\<close>
  sorry


subsection \<open>Per-angle slice nowhere-density / meagerness (proof-complete from \<open>nd\<close>)\<close>

text \<open>For a FIXED steering angle \<open>\<omega>\<close> with nonzero wavevector, the set of \<open>x\<close> at
  which \<open>DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)\<close> is not surjective is nowhere dense,
  hence meager.  proof-complete from the abstract input @{text nd}.\<close>

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

text \<open>\<open>BadXW \<omega>0 \<omega>s \<Gamma>\<close> is the \<open>x\<close>-projection of the bad \<open>(x,\<omega>)\<close> excess locus over an
  angle set \<open>\<Gamma>\<close>: the set of configurations \<open>x\<close> for which SOME angle \<open>\<omega>\<in>\<Gamma>\<close> has a
  nonzero wavevector and a rank-deficient moment map.  The bad set of the engine
  is exactly \<open>BadXW \<omega>0 \<omega>s \<Gamma>\<close> intersected with \<open>V\<close>, with \<open>\<Gamma>\<close> the phase-collinear
  curve inside \<open>OmegaPF\<close>.\<close>

definition BadXW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

text \<open>The engine's bad set is the intersection of \<open>V\<close> with \<open>BadXW\<close> over the
  phase-collinear angle curve.  proof-complete SET equality.\<close>

lemma engine_bad_eq_projection:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  shows "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}
        = V \<inter> BadXW \<omega>0 \<omega>s {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}"
  unfolding BadXW_def by blast


subsection \<open>The genuine analytic core (one MATH proof hole, parametric in \<open>\<Gamma>\<close>)\<close>

text \<open>\<^bold>\<open>The Sard-free excess engine.\<close>  Meagerness of the \<open>x\<close>-projection \<open>V \<inter> BadXW\<close>
  of the bad \<open>(x,\<omega>)\<close> excess locus over a one-parameter analytic angle curve \<open>\<Gamma>\<close>
  inside the bounded box \<open>OmegaPF\<close>.

  This is the ONE genuine MATH proof hole.  It is stated \<^bold>\<open>parametrically\<close> in the angle
  set \<open>\<Gamma>\<close> (any subset of the box \<open>OmegaPF ctr \<delta>\<close>) precisely so that D4 reuses it
  verbatim with the complementary (non phase-collinear) curve in place of the
  phase-collinear one.  The inputs are exactly what the IFT chart needs:

  \<^item> @{text nd}: per-angle nowhere density (\<Rightarrow> each fixed-\<open>\<omega>\<close> slice is the zero set
    of the moment-rank polynomial \<open>mstarg (cvec_dip \<omega>0 \<omega>s \<omega>)\<close> in the configuration
    moments, a nontrivial polynomial because \<open>cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0\<close>);
  \<^item> @{text c6}: \<open>6 \<le> CARD('n)\<close> (enough emitters for the moment map to have full
    target rank generically);
  \<^item> @{text d0}, @{text pf}: \<open>0 < \<delta>\<close> and \<open>sin (\<omega>$1) \<noteq> 0\<close> on the box, so the second
    Jacobian column \<open>Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)\<close> is nonzero (@{thm Dcvec_col2_nz}
    needs \<open>sin (\<omega>$1) \<noteq> 0\<close>) \<Rightarrow> the steering map is an immersion in the \<open>\<omega>\<^sub>2\<close> direction,
    so the collinearity equation \<open>\<Theta>(\<omega>$1,\<omega>$2) = 0\<close> cuts a genuine codimension-1 arc.

  \<^bold>\<open>Recommended route (multi-week math, ONE proof hole).\<close>
  \<^enum> \<^bold>\<open>Fix the phase-period lattice.\<close>  Clearing \<open>cvec_dip\<close>/\<open>Dcvec_dip\<close> by their
    explicit trigonometric forms (@{thm cvec_dip_def}, @{thm Dcvec_dip_def}; the
    cross-product collinearity condition), \<open>\<omega> \<in> \<Gamma>\<close> is an analytic equation
    \<open>\<Theta>(\<omega>$1,\<omega>$2) = 0\<close> whose transcendental factors are \<open>cos\<close>/\<open>sin\<close>/\<open>a cos + b sin\<close>;
    each meets the bounded box \<open>OmegaPF\<close> in finitely many \<open>\<int>\<^sup>3\<close>-period windows
    (@{thm finite_affine_int_zeros}, @{thm finite_cos_zeros_interval},
    @{thm finite_phase_zeros_interval}), so \<open>\<Gamma>\<close> is covered by a FINITE family of
    analytic arcs \<open>\<gamma>\<^sub>1, ..., \<gamma>\<^sub>m\<close> each a graph \<open>\<omega>$2 = \<phi>\<^sub>k(\<omega>$1)\<close> (or \<open>\<omega>$1 = \<psi>\<^sub>k(\<omega>$2)\<close>)
    over a real interval.
  \<^enum> \<^bold>\<open>Chart the excess locus by the IFT.\<close>  Over each arc \<open>\<gamma>\<^sub>k\<close> the bad pairs lie in
    \<open>{(x,\<omega>). \<omega> \<in> \<gamma>\<^sub>k \<and> mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0}\<close>.  Because \<open>cvec_dip \<noteq> 0\<close>
    on the arc (@{text c6}, @{text pf}), \<open>x \<mapsto> M_paper x (cvec_dip ...)\<close> is a
    submersion off the nowhere-dense base (the content of @{text nd} /
    @{thm fixed_c_nonsurj_nowhere_dense}), so the implicit-function theorem charts
    each fibre as a graph of codimension \<open>\<ge> 1\<close> in \<open>x\<close>.  Summing the 1-dimensional
    arc parameter against the \<open>x\<close>-codimension gives a \<open>(2N-1)\<close>-dimensional graph in
    the \<open>(x,\<omega>)\<close> excess space.
  \<^enum> \<^bold>\<open>Project and assemble.\<close>  The \<open>x\<close>-projection of a \<open>(2N-1)\<close>-dim graph in
    \<open>2N\<close>-space is negligible; negligible \<Rightarrow> meager
    (@{thm meager_negligible_closed_cover}); the finite union over the arcs is
    meager (@{thm meager_Union_finite}); \<open>V \<inter> BadXW\<close> injects into it.  Mirror the
    flatten/conjugate/pullback skeleton of
    @{thm parametric_transversality_meager_planar_config} for the \<open>\<Phi>\<close>/\<open>\<Psi>\<close> index
    bookkeeping and @{thm meager_homeo_image}; mirror the finite-witness-arc
    confinement of @{thm meager_steering_singular_stratum}.

  \<^bold>\<open>Why this is the right cut.\<close>  It is the smallest statement that (a) is purely
  analytic (no \<open>gradU\<close>/\<open>HessU\<close>/\<open>det Dcvec\<close> dressing --- those are dropped by the
  set-level subset @{thm meager_subset} in @{text D3_excess_engine}), (b) is
  parametric in \<open>\<Gamma>\<close> so D4 reuses it, and (c) carries exactly the IFT/lattice
  inputs (@{text nd}, @{text c6}, @{text pf}, @{text d0}) and nothing else.\<close>

lemma excess_projection_meager:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>)"
  \<comment> \<open>GENUINE MATH proof hole (the irreducible analytic core of M5, reused by D4).
      The Sard-free excess engine: finite cover of the bounded angle curve \<open>\<Gamma>\<close> by
      \<open>\<int>\<^sup>3\<close>-period analytic arcs (@{thm finite_affine_int_zeros}); IFT-chart each
      arc's bad fibre as a \<open>(2N-1)\<close>-dim graph (submersion off the nowhere-dense
      base supplied by @{text nd}); \<open>x\<close>-projection negligible \<Rightarrow> meager
      (@{thm meager_negligible_closed_cover}); finite union meager
      (@{thm meager_Union_finite}).  Route above.  NOT a splice freebie --- this
      is the real analysis.\<close>
  sorry


subsection \<open>The D3 excess engine, proof-complete from the abstract core\<close>

text \<open>The D3 target (verbatim from \<open>M5_Dev_D3/Scratch_m5_D3.thy\<close>, lemma
  @{text D3_excess_engine}).  proof-complete from @{text excess_projection_meager}
  via the set equality @{thm engine_bad_eq_projection} (the phase-collinear curve
  is a subset of \<open>OmegaPF\<close>).\<close>

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
  have Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>" unfolding \<Gamma>_def by blast
  have eq: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
              cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
            \<and> phase_collinear \<omega>0 \<omega>s \<omega>}
          = V \<inter> BadXW \<omega>0 \<omega>s \<Gamma>"
    unfolding \<Gamma>_def by (rule engine_bad_eq_projection)
  show ?thesis
    unfolding eq
    by (rule excess_projection_meager[OF openV Vne c6 d0 pf Gsub nd])
qed


subsection \<open>The D3 leaf, proof-complete from the excess engine\<close>

text \<open>The exact D3 target statement (verbatim from
  \<open>M5_Dev_D3/Scratch_m5_D3.thy\<close>, lemma @{text m5_D34_D3_collinear}).  The D3 bad
  set is a subset of the excess engine's bad set (dropping \<open>gradU = 0\<close> and
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
