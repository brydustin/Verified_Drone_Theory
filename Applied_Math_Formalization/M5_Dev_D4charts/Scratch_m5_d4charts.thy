theory Scratch_m5_d4charts
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
          "Applied_Math_Sard.Sard_Negligible"
begin

text \<open>\<^bold>\<open>(M5) D4 charts --- the isolated IFT chart-bundle obligation
  @{text branchP_indep_charts_Nn} (rank-drop chart bundle).\<close>

  This file isolates and discharges (as far as is legitimately possible from the
  given hypotheses) the single genuine analytic core of the M5 D4 reduction: the
  IFT chart bundle of the retained-constraint bad \<open>(x,\<omega>)\<close> locus over the
  2-dimensional linear-independence (\<open>\<gamma> \<not>\<parallel> c\<close>) region.  The target statement
  @{text branchP_indep_charts_Nn}, together with the \<open>BadXGW\<close> / \<open>gamma_par_c\<close> /
  \<open>phase_collinear\<close> definitions and the structural set-algebra lemmas, is copied
  \<^bold>\<open>verbatim\<close> from
  @{file \<open>../M5_Dev_D4Core/Scratch_m5_d4core.thy\<close>} (the D4 core file).

  \<^bold>\<open>What is proven SOUND, sorry-free here.\<close>
  \<^enum> @{text BadXGW_point} / @{text BadXGW_mono} / @{text BadXGW_UN} --- structural set
    algebra for the retained bad \<open>x\<close>-set (copied verbatim).
  \<^enum> @{text not_gamma_par_c_iff} --- the linear-independence dichotomy unfolding.
  \<^enum> @{text branchP_indep_negligible_closed_cover} / @{text
    branchP_indep_of_negligible_closed_cover} / @{text branchP_indep_core} --- the
    downstream layers assembled \<^bold>\<open>sorry-free\<close> from the chart bundle via
    @{thm negligible_singular_image_2n} and @{thm meager_negligible_closed_cover};
    these confirm the cut is at the right place.

  \<^bold>\<open>The single remaining irreducible obligation (ONE scoped MATH sorry).\<close>
  @{text branchP_indep_charts_Nn}.  This is the implicit-function-theorem chart of
  the retained-constraint bad locus, in the EXACT output shape of the heap engine
  @{thm charts_core_Nn} (and consumed by @{thm negligible_singular_image_2n}).

  \<^bold>\<open>Engine analysis (why this does NOT reduce to a heap engine call).\<close>  The heap
  chart engine @{thm charts_core_Nn} produces precisely this bundle, but from a
  joint map \<open>G :: ((real^2)^'n \<times> real^2) \<Rightarrow> real^2\<close> whose bad set is governed by the
  \<^emph>\<open>\<omega>-partial\<close> non-surjectivity \<open>\<not> (\<exists>D\<omega>. (\<lambda>u. G(x,u)) has_derivative D\<omega> \<dots> \<and> surj D\<omega>)\<close>.
  \<^enum> If one takes \<open>G = gradU\<close>, the engine's \<open>\<omega>\<close>-partial rank drop is, via
    @{thm gradU_has_derivative_of_C2}, exactly \<open>det (HessU x \<omega>) = 0\<close> --- the
    \<^emph>\<open>\<omega>\<close>-Hessian degeneracy --- which is a DIFFERENT condition from the moment
    \<open>x\<close>-Jacobian rank drop \<open>\<not> surj (DM_paper_x x c)\<close> that \<open>BadXGW\<close> retains.
    Nothing forces \<open>\<not> surj (DM_paper_x x c) \<Longrightarrow> det (HessU x \<omega>) = 0\<close>, so
    \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> \<subseteq>\<close> the engine bad set FAILS for this \<open>G\<close>.
  \<^enum> The complex engine @{thm parametric_transversality_negligible_complex} (and its
    inner @{thm charts_core_Nn} call) again controls the \<^emph>\<open>\<omega>\<close>-partial of a
    complex-valued map, whereas \<open>BadXGW\<close>'s rank drop \<open>\<not> surj (DM_paper_x x c)\<close>
    is the \<^emph>\<open>x\<close>-partial of the moment map (a map to \<open>complex^6\<close>); the variable roles
    are transposed, so no inclusion into the engine bad set holds either.
  The codimension source of \<open>BadXGW\<close> is the \<^emph>\<open>conjunction\<close> \<open>gradU = 0\<close> (two
  scalar equations cutting the locus) together with the moment rank drop; building
  the joint \<open>C\<^sup>1\<close> map whose chart realises that combined rank drop --- the local
  diffeomorphism supplied by \<open>\<gamma> \<not>\<parallel> c\<close> and \<open>det (Dcvec) \<noteq> 0\<close> --- and feeding it
  through @{thm charts_core_Nn} on each compact sub-box is the genuine multi-week
  implicit-function-theorem content.  It does NOT follow from the abstract
  per-fixed-\<open>\<omega>\<close> topological input @{text nd} alone (no derivative, no closedness, no
  joint regularity; uncountable unions of nowhere-dense sets need not be meager).
  This is the EXACT analogue of the ArcNeg / D3Sound siblings'
  @{text excess_arc_charts_Nn}, and is the single isolated \<open>sorry\<close> of this file.
  \<open>freebie_at_splice = false\<close>.\<close>


subsection \<open>The phase-collinear predicate (copied verbatim from D4Core)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>The retained-constraint bad \<open>x\<close>-set (copied verbatim from D4Core)\<close>

definition BadXGW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXGW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"


subsection \<open>The rank-drop dichotomy predicate \<open>\<gamma> \<parallel> c\<close> (copied verbatim)\<close>

definition gamma_par_c :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow> phase_collinear \<omega>0 \<omega>s \<omega>"

lemma not_gamma_par_c_iff:
  "\<not> gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<forall>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<noteq> t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<and> (\<forall>t. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"
  unfolding gamma_par_c_def phase_collinear_def by blast


subsection \<open>Structural set algebra for \<open>BadXGW\<close> (sorry-free, copied verbatim)\<close>

lemma BadXGW_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "BadXGW \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXGW \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n) set)"
  using assms unfolding BadXGW_def by blast

lemma BadXGW_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "BadXGW \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)
          = (\<Union>i\<in>I. (BadXGW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  unfolding BadXGW_def by blast

lemma BadXGW_point:
  fixes \<omega> :: "real^2"
  shows "BadXGW \<omega>0 \<omega>s {\<omega>}
          = {x :: (real^2)^'n.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
              \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  unfolding BadXGW_def by blast


subsection \<open>The irreducible IFT-chart bundle (the single isolated analytic \<open>sorry\<close>)\<close>

text \<open>\<^bold>\<open>The genuine geometric-measure content, isolated as one precisely-scoped
  statement.\<close>  Over the linear-independence (\<open>\<gamma> \<not>\<parallel> c\<close>) region \<open>\<Gamma> \<subseteq> OmegaPF ctr \<delta>\<close>,
  the retained-constraint bad \<open>x\<close>-fibre \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> admits a chart bundle in
  the EXACT shape consumed by @{thm negligible_proj_charts_Nn} (the @{thm
  charts_core_Nn} output): a COUNTABLE family of charts
  \<open>charts i :: (real^2)^'n \<Rightarrow> ((real^2)^'n \<times> (real^2))\<close> with critical sets \<open>Crit i\<close>
  and blinfun derivatives \<open>D i\<close> such that
  \<^enum> the bad fibre is covered by the \<open>x\<close>-projections \<open>(fst \<circ> charts i) ` Crit i\<close>;
  \<^enum> on each \<open>Crit i\<close> the projection \<open>fst \<circ> charts i\<close> has derivative \<open>D i x\<close>;
  \<^enum> that derivative is NON-surjective on \<open>(real^2)^'n\<close> (the codimension \<open>\<ge> 1\<close>
    rank-drop from RETAINED \<open>gradU = 0\<close> + the moment rank-drop), and
  \<^enum> each \<open>x\<close>-projection piece \<open>(fst \<circ> charts i) ` Crit i\<close> is CLOSED.

  This is the implicit-function-theorem chart of the retained-constraint locus.  See
  the file header for the engine analysis showing why neither @{thm charts_core_Nn}
  (G = \<open>gradU\<close>: its \<open>\<omega>\<close>-partial rank drop is \<open>det (HessU) = 0\<close>, not the moment
  \<open>x\<close>-Jacobian rank drop) nor @{thm parametric_transversality_negligible_complex}
  (its rank drop is the \<open>\<omega>\<close>-partial of a complex map, with the variable roles
  transposed relative to the \<open>x\<close>-partial @{const DM_paper_x}) yields an inclusion of
  \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> into the engine bad set.  The codimension source is the
  conjunction \<open>gradU = 0\<close> \<open>\<and>\<close> the moment rank drop; realising the chart of that
  combined locus is the genuine multi-week IFT content and does NOT follow from
  @{text nd} alone.  NOT a splice freebie.\<close>

lemma branchP_indep_charts_Nn:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>GENUINE geometric-measure core: the IFT chart of the retained-constraint bad
      \<open>(x,\<omega>)\<close> locus in the @{thm charts_core_Nn} output shape.  The single irreducible
      \<open>sorry\<close> of this file; it does NOT follow from @{text nd} alone (see header).
      NOT a splice freebie.\<close>
  sorry


subsection \<open>The verbatim target: the closed negligible cover (sorry-free from the bundle)\<close>

text \<open>\<^bold>\<open>The closed negligible cover, assembled sorry-free from the chart bundle.\<close>
  From the chart bundle @{thm branchP_indep_charts_Nn} the pieces
  \<open>K i = (fst \<circ> charts i) ` (Crit i)\<close> are CLOSED (chart output) and NEGLIGIBLE
  (@{thm negligible_singular_image_2n}: the projection has non-surjective derivative
  on \<open>Crit i\<close>), and they cover the bad fibre.  This turns the IFT-chart content into
  the countable closed negligible cover the reduction layer consumes.  The target
  statement is copied VERBATIM from the D4 core file.\<close>

lemma branchP_indep_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
            (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
          \<and> (\<forall>n. closed (K n))
          \<and> (\<forall>n. negligible (K n))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
                    \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using branchP_indep_charts_Nn[OF openV Vne c6 d0 pf Gsub Gindep nd]
    by (smt (verit, best))
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have Kcover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
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


subsection \<open>The downstream sorry-free layers (copied verbatim from D4Core)\<close>

text \<open>The two sorry-free layers consumed downstream (copied verbatim from the D4
  core file) confirm the cut is at the right place: the closed negligible cover
  yields meagerness without further geometric-measure work.\<close>

lemma branchP_indep_of_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<Gamma> :: "(real^2) set"
    and K :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])

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
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
      and clo: "\<forall>n. closed (K n)"
      and neg: "\<forall>n. negligible (K n)"
    using branchP_indep_negligible_closed_cover[OF openV Vne c6 d0 pf Gsub Gindep nd]
    by blast
  show ?thesis
    by (rule branchP_indep_of_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

end
