theory Scratch_m5_d3proof
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) Core D3 (CHARTS) PROOF FILE --- the per-arc IFT chart bundle
  @{text excess_arc_charts_Nn}.\<close>

  This is the prover-agent companion to @{file
  \<open>../M5_Dev_D3charts/Scratch_m5_d3charts.thy\<close>}.  The exact statement of the
  D3 chart-bundle target, the SOUND \<open>C\<^sup>1\<close> @{text analytic_arc} predicate and the
  @{text BadXW} definition are copied VERBATIM.  We then reduce the chart-bundle
  target to the smallest honest analytic residual by APPLYING the heap engine
  @{thm charts_core_Nn} to a joint scalar-determinant map over the 1-D arc.\<close>


subsection \<open>mstarg interface (STUB = Robust3-resident, discharges at splice)\<close>

text \<open>\<^const>\<open>mstarg\<close> lives in the strictly-higher session
  \<open>Applied_Math_Appendix_Full.Nonemptiness_Robust3\<close> and is NOT in the
  \<open>Applied_Math_Appendix\<close> heap that this file imports.  We re-declare the
  definition and the four facts we use as LOCAL stubs with the EXACT Robust3
  signatures; each discharges verbatim at the Robust3 splice.\<close>

definition mstarg :: "real^2 \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  \<comment> \<open>STUB = Robust3-resident, discharges at splice\<close>
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

lemma surj_iff_mstarg: "surj (DM_paper_x x c) \<longleftrightarrow> mstarg c x \<noteq> 0"
  \<comment> \<open>STUB = Robust3-resident, discharges at splice\<close>
  sorry

lemma rline_entire_mstarg: "rline_entire (\<lambda>x::(real^2)^'n. mstarg c x)"
  \<comment> \<open>STUB = Robust3-resident, discharges at splice\<close>
  sorry

lemma nowhere_dense_mstarg_zeros:
  "c \<noteq> 0 \<Longrightarrow> 6 \<le> CARD('n) \<Longrightarrow> nowhere_dense {x::(real^2)^'n. mstarg c x = 0}"
  \<comment> \<open>STUB = Robust3-resident, discharges at splice\<close>
  sorry

lemma mstarg_nonzero:
  "c \<noteq> 0 \<Longrightarrow> 6 \<le> CARD('n) \<Longrightarrow> \<exists>x::(real^2)^'n. mstarg c x \<noteq> 0"
  \<comment> \<open>STUB = Robust3-resident, discharges at splice\<close>
  sorry


subsection \<open>The STRENGTHENED analytic-arc predicate (copied verbatim, \<open>C\<^sup>1\<close>)\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> \<phi> C1_differentiable_on {a..b}
                          \<and> \<gamma> = \<phi> ` {a..b})"


subsection \<open>STEP 1 --- the soundness gate: a \<open>C\<^sup>1\<close> arc in the plane is negligible\<close>

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


subsection \<open>The curve-confined excess locus (copied verbatim)\<close>

definition BadXW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0 \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"


subsection \<open>Structural set algebra for \<open>BadXW\<close> (proof-complete)\<close>

lemma BadXW_empty:
  "BadXW \<omega>0 \<omega>s {} = ({} :: ((real^2)^'n) set)"
  unfolding BadXW_def by blast

lemma BadXW_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "BadXW \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXW \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n) set)"
  using assms unfolding BadXW_def by blast

lemma BadXW_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "BadXW \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)
          = (\<Union>i\<in>I. (BadXW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  unfolding BadXW_def by blast

lemma BadXW_point:
  fixes \<omega> :: "real^2"
  shows "BadXW \<omega>0 \<omega>s {\<omega>}
          = {x :: (real^2)^'n. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
                              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  unfolding BadXW_def by blast


subsection \<open>BadXW as a slice union of mstarg zero-sets (proof-complete from stubs)\<close>

text \<open>The rank-drop condition is exactly the determinantal locus
  \<open>mstarg (cvec \<omega>) x = 0\<close>.  This rewrites @{const BadXW} into the SLICE form
  consumed by the joint-Sard cover.\<close>

lemma BadXW_eq_mstarg_slices:
  fixes \<Gamma> :: "(real^2) set"
  shows "(BadXW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
          = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
                                    \<and> mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0}"
  unfolding BadXW_def using surj_iff_mstarg by auto


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


subsection \<open>Degenerate sanity checks: the cut is sound at the extreme instances\<close>

lemma excess_empty_arc_meager:
  fixes V :: "((real^2)^'n) set"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s {} :: ((real^2)^'n) set)"
  by (simp add: BadXW_empty)

lemma excess_finite_arc_meager:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes fin: "finite \<gamma>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
proof -
  have eq: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
              = (\<Union>\<omega>\<in>\<gamma>. V \<inter> BadXW \<omega>0 \<omega>s {\<omega>})"
    unfolding BadXW_def by blast
  have "meager (\<Union>\<omega>\<in>\<gamma>. (V \<inter> BadXW \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set))"
    by (rule meager_Union_finite[OF fin]) (rule fixed_omega_proj_meager[OF nd])
  thus ?thesis unfolding eq .
qed


subsection \<open>The EMPTY-arc extreme instance of the chart bundle (proof-complete)\<close>

lemma excess_empty_arc_charts_Nn:
  fixes V :: "((real^2)^'n) set"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> BadXW \<omega>0 \<omega>s {} :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof (intro exI conjI)
  let ?charts = "(\<lambda>i x. (x, 0)) :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
  let ?Crit = "(\<lambda>i. {}) :: nat \<Rightarrow> ((real^2)^'n) set"
  let ?D = "(\<lambda>i x. 0) :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
  show "(V \<inter> BadXW \<omega>0 \<omega>s {} :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. (fst \<circ> ?charts i) ` (?Crit i))"
    by (simp add: BadXW_empty)
  show "\<forall>i x. x \<in> ?Crit i \<longrightarrow>
          ((fst \<circ> ?charts i) has_derivative (blinfun_apply (?D i x))) (at x within ?Crit i)"
    by simp
  show "\<forall>i x. x \<in> ?Crit i \<longrightarrow> \<not> surj (blinfun_apply (?D i x))"
    by simp
  show "\<forall>i. closed ((fst \<circ> ?charts i) ` (?Crit i))"
    by simp
qed


subsection \<open>The irreducible analytic core, isolated by ENGINE APPLICATION\<close>

text \<open>\<^bold>\<open>The honest reduction.\<close>  The heap engine @{thm charts_core_Nn} produces a
  chart bundle in the EXACT target output shape from a joint map \<open>G\<close> over an open
  parameter set \<open>\<Omega>\<close>, provided \<open>G\<close> is a regular value at \<open>0\<close> and jointly \<open>C\<^sup>1\<close>.  Its
  output bad set is the \<open>x\<close>-projection of \<open>{(x,\<omega>) : G(x,\<omega>)=0 \<and> \<omega>-partial not surj}\<close>.

  The single irreducible analytic residual of D3 is therefore: produce, over the
  open interior of the arc box, such a joint map \<open>G\<close> whose engine bad set CONTAINS
  the curve-confined fibre \<open>V \<inter> BadXW \<omega>0 \<omega>s \<gamma>\<close>.  We state this residual as
  @{text excess_arc_engine_field} and DISCHARGE the target chart bundle from it
  by a SOUND application of @{thm charts_core_Nn} (no further analytic content).

  This is strictly tighter than the raw target: the engine application, the
  chart-shape rewrap, and the cover-subset step are all proven proof-complete here;
  only the regular-value field over the 1-D arc remains \<open>proof hole\<close>.\<close>

text \<open>The residual: a joint regular-value field over the (open) arc-interior whose
  engine bad set covers the curve-confined fibre.  Stated with the OPEN parameter
  set \<open>\<Omega>\<close> and the exact @{thm charts_core_Nn} hypotheses, plus the COVER obligation
  that ties the engine output to @{const BadXW}.\<close>

lemma excess_arc_engine_field:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>(\<Omega>::(real^2) set) (G::(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^2)).
            open \<Omega> \<and> regular_value_on G (V\<times>\<Omega>) 0 \<and>
            (\<exists>G'. (\<forall>z\<in>V\<times>\<Omega>. (G has_derivative blinfun_apply (G' z)) (at z))
                  \<and> continuous_on (V\<times>\<Omega>) G') \<and>
            (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
              \<subseteq> {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
                   (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>)
                            (at \<omega> within \<Omega>) \<and> surj D\<omega>))}"
  \<comment> \<open>GENUINE analytic core, isolated.  Over the open interior of the 1-D arc box
      one feeds the joint scalar-determinant field \<open>G(x,\<omega>) = (mstarg (cvec \<omega>) x, 0)\<close>
      (padded to \<open>real\<^sup>2\<close>); the regular-value claim is the joint transversality of
      the moment-Jacobian determinant off the singular stratum, and the cover
      obligation is the IFT chart of the determinantal locus over the arc.  This
      is the multi-week analytic residual; it does NOT follow from @{text nd}.\<close>
  sorry


subsection \<open>The chart-bundle target, DISCHARGED from the engine field (proof-complete)\<close>

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
         (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  obtain \<Omega> :: "(real^2) set" and G :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^2)"
    where Oopen: "open \<Omega>"
      and reg: "regular_value_on G (V\<times>\<Omega>) 0"
      and C1: "\<exists>G'. (\<forall>z\<in>V\<times>\<Omega>. (G has_derivative blinfun_apply (G' z)) (at z))
                    \<and> continuous_on (V\<times>\<Omega>) G'"
      and cov: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                  \<subseteq> {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
                       (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>)
                                (at \<omega> within \<Omega>) \<and> surj D\<omega>))}"
    using excess_arc_engine_field[OF openV Vne c6 arc gsub pf nd]
    by (smt (verit, best))
  \<comment> \<open>Apply the heap engine to the engine field --- pure assembly, proof-complete.\<close>
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where eng_cover:
        "{x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
             (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
           \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using charts_core_Nn[OF openV Vne Oopen reg C1]
    by (smt (verit, best))
  have cover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                  \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    using cov eng_cover by blast
  show ?thesis
    by (intro exI[where x = charts] exI[where x = Crit] exI[where x = D] conjI)
       (use cover der rank clo in blast)+
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
            (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
          \<and> (\<forall>n. closed (K n))
          \<and> (\<forall>n. negligible (K n))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
                    \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using excess_arc_charts_Nn[OF openV Vne c6 arc gsub pf nd]
    by (smt (verit, best))
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have Kcover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
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
  assumes cover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])

lemma excess_arc_projection_meager:
  fixes V :: "((real^2)^'n) set" and \<gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "(V \<inter> BadXW \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
      and clo: "\<forall>n. closed (K n)"
      and neg: "\<forall>n. negligible (K n)"
    using excess_arc_negligible_closed_cover[OF openV Vne c6 arc gsub pf nd] by blast
  show ?thesis
    by (rule excess_arc_projection_of_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

end
