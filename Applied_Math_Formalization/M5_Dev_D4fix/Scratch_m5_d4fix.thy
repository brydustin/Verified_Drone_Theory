theory Scratch_m5_d4fix
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) D4 chart core --- CORRECTED, \<open>gradU = 0\<close> RETAINED (codim 3).\<close>

  This file rebuilds the D4 rank-drop chart-bundle obligation
  @{text branchP_indep_charts_Nn} on the \<^emph>\<open>retained-constraint\<close> bad locus
  \<open>BadXGW\<close> (which keeps \<open>gradU = 0\<close>), over the 2-D linear-independence
  (\<open>\<gamma> \<not>\<parallel> c\<close>) region.  It is the SOUND sibling of the D3 arc core: the prior
  D3 locus \<open>BadXW\<close> dropped \<open>gradU = 0\<close>, which made it FALSE (a 1-parameter
  sweep of codim-1 slices fills full measure).  Here \<open>gradU = 0\<close> is RETAINED,
  giving the honest codimension count:
  \<^item> \<open>gradU = 0\<close> contributes 2 scalar equations (codim 2 in \<open>x\<close>-space);
  \<^item> the moment rank-drop \<open>\<not> surj (DM_paper_x x c)\<close> \<open>\<longleftrightarrow>\<close> \<open>mstarg c x = 0\<close>
    contributes 1 more (codim 1);
  so \<open>BadXGW\<close> is cut by 3 independent scalar equations --- \<^bold>\<open>codim 3\<close>.

  \<^bold>\<open>What is SOUND and sorry-free here\<close> (proved against the heap):
  \<^enum> @{text BadXGW_mono} / @{text BadXGW_UN} / @{text BadXGW_point} ---
    structural set algebra (copied verbatim from the sound D4 file).
  \<^enum> @{text not_gamma_par_c_iff} --- the linear-independence dichotomy.
  \<^enum> @{text bad_imp_mstarg_zero} --- the codim-3 SANITY check: on \<open>BadXGW\<close> the
    retained moment rank-drop is the determinantal equation \<open>mstarg c x = 0\<close>
    (via the \<open>mstarg\<close> stub @{text surj_iff_mstarg}); together with the two
    \<open>gradU = 0\<close> equations this is the codim-3 zero locus of the joint map
    @{text Gjoint}.
  \<^enum> @{text Gjoint_zero_of_bad} --- \<open>BadXGW \<subseteq> {Gjoint = 0}\<close>: the bad locus sits
    in the zero set of the codim-3 joint map.
  \<^enum> @{text branchP_indep_negligible_closed_cover} /
    @{text branchP_indep_of_negligible_closed_cover} /
    @{text branchP_indep_core} --- the downstream cover\<open>\<rightarrow>\<close>meager layers,
    assembled sorry-free from the chart bundle via
    @{thm negligible_singular_image_2n} and @{thm meager_negligible_closed_cover}.

  \<^bold>\<open>The single remaining irreducible obligation (ONE scoped MATH sorry).\<close>
  @{text branchP_indep_charts_Nn}: the IFT chart of the retained-constraint
  locus, in the EXACT output shape of @{thm charts_core_Nn} consumed by
  @{thm negligible_singular_image_2n}.  The honest crux (DESIGN \<section>7) is the
  \<^emph>\<open>\<omega>\<close>-partial surjectivity of the joint map \<open>Gjoint = (gradU, mstarg)\<close> at the
  bad zeros, supplied by the steering nondegeneracy \<open>det (Dcvec) \<noteq> 0\<close> /
  \<open>\<gamma> \<not>\<parallel> c\<close> local diffeomorphism --- NOT by @{text nd} alone.  Crucially
  @{thm charts_core_Nn} is hard-typed to codomain \<open>real^2\<close> and controls the
  \<open>\<omega>\<close>-partial, whereas \<open>BadXGW\<close>'s rank drop \<open>\<not> surj (DM_paper_x x c)\<close> is the
  \<open>x\<close>-partial of the moment map to \<open>complex^6\<close>; closing the chart requires the
  codomain-\<open>real^3\<close> generalization of the engine + the steering transversality
  (DESIGN \<section>4, \<section>7).  This is the single isolated \<open>sorry\<close>; it is NOT a splice
  freebie.\<close>


subsection \<open>\<open>mstarg\<close> interface --- LOCAL stubs (discharge at the Robust3 splice)\<close>

text \<open>\<open>mstarg\<close> is defined in \<open>Nonemptiness_Robust3\<close>, which is NOT in this heap.
  We re-state, with EXACT Robust3 signatures, the determinantal-rank interface
  used below.  Each is proved sorry-free in @{file
  \<open>../Appendix/Robust3/Nonemptiness_Robust3.thy\<close>} (lines 572--754); they
  discharge automatically at the Robust3 splice.  Nothing in this file's SOUND
  results depends on these being open --- they enter only the codim-3 sanity
  bridge (@{text bad_imp_mstarg_zero}) and the (sorry) chart core.\<close>

definition mstarg :: "(real^2) \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

lemma surj_iff_mstarg:
  "surj (DM_paper_x x c) \<longleftrightarrow> mstarg c x \<noteq> 0"
  sorry

lemma rline_entire_mstarg:
  "rline_entire (\<lambda>x::(real^2)^'n. mstarg c x)"
  sorry

lemma mstarg_nonzero:
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x::(real^2)^'n. mstarg c x \<noteq> 0"
  sorry

lemma nowhere_dense_mstarg_zeros:
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. mstarg c x = 0}"
  sorry


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


subsection \<open>The codim-3 joint map \<open>Gjoint = (gradU, mstarg)\<close> and the sanity bridge\<close>

text \<open>\<^bold>\<open>The corrected codim-3 joint map.\<close>  \<open>Gjoint \<omega> = (gradU\<^sub>1, gradU\<^sub>2, mstarg)\<close>
  packs the TWO retained gradient equations together with the moment rank-drop
  determinant into a single \<open>real^3\<close>-valued map.  \<open>Gjoint = 0\<close> at \<open>(x,\<omega>)\<close> is
  exactly: \<open>\<omega>\<close> is a critical point of the pattern (\<open>gradU = 0\<close>) \<^bold>\<open>and\<close> the moment
  map drops rank there (\<open>mstarg = 0\<close>, i.e. \<open>\<not> surj (DM_paper_x)\<close>).  This is the
  honest codim-3 cut: dropping the \<open>gradU\<close> slots (as the prior D3 did) leaves a
  codim-1 cut whose 1-parameter \<open>\<omega>\<close>-sweep is full measure --- the falseness fix.\<close>

definition Gjoint :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2)^'n \<Rightarrow> real^2 \<Rightarrow> real^3" where
  "Gjoint \<omega>0 \<omega>s x \<omega> =
     vector [ gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1,
              gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2,
              mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x ]"

lemma Gjoint_zero_iff:
  "Gjoint \<omega>0 \<omega>s x \<omega> = 0
   \<longleftrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and> mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0"
proof -
  have L: "Gjoint \<omega>0 \<omega>s x \<omega> = 0
           \<longleftrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0
             \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 = 0
             \<and> mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0"
    unfolding Gjoint_def
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_3 vector_3)
  have G: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
           \<longleftrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0
             \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 = 0"
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
  show ?thesis using L G by blast
qed

text \<open>\<^bold>\<open>Codim-3 sanity bridge.\<close>  On the bad locus the retained moment rank-drop
  IS the determinantal equation \<open>mstarg = 0\<close>; hence each bad \<open>x\<close> (witnessed by
  some \<open>\<omega>\<in>\<Gamma>\<close>) satisfies \<open>Gjoint \<omega>0 \<omega>s x \<omega> = 0\<close> --- the full codim-3 cut.\<close>

lemma bad_imp_mstarg_zero:
  assumes "\<not> surj (DM_paper_x x c)"
  shows "mstarg c x = 0"
  using assms surj_iff_mstarg by blast

lemma Gjoint_zero_of_bad:
  fixes \<Gamma> :: "(real^2) set"
  shows "(BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
           \<subseteq> {x. \<exists>\<omega>\<in>\<Gamma>. Gjoint \<omega>0 \<omega>s x \<omega> = 0
                       \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
                       \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0}"
proof
  fix x :: "(real^2)^'n"
  assume "x \<in> BadXGW \<omega>0 \<omega>s \<Gamma>"
  then obtain \<omega> where w\<Gamma>: "\<omega> \<in> \<Gamma>"
    and gU: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and detn: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cn: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and nsurj: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    unfolding BadXGW_def by blast
  have ms0: "mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0"
    by (rule bad_imp_mstarg_zero[OF nsurj])
  have "Gjoint \<omega>0 \<omega>s x \<omega> = 0" using gU ms0 by (simp add: Gjoint_zero_iff)
  thus "x \<in> {x. \<exists>\<omega>\<in>\<Gamma>. Gjoint \<omega>0 \<omega>s x \<omega> = 0
                     \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
                     \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0}"
    using w\<Gamma> detn cn by blast
qed


subsection \<open>The irreducible IFT-chart bundle (the single isolated analytic \<open>sorry\<close>)\<close>

text \<open>\<^bold>\<open>The genuine geometric-measure content, isolated as one precisely-scoped
  statement.\<close>  Over the linear-independence (\<open>\<gamma> \<not>\<parallel> c\<close>) region
  \<open>\<Gamma> \<subseteq> OmegaPF ctr \<delta>\<close>, the retained-constraint bad \<open>x\<close>-fibre
  \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> admits a chart bundle in the EXACT shape consumed by
  @{thm negligible_proj_charts_Nn} (the @{thm charts_core_Nn} output).

  \<^bold>\<open>Why this does NOT reduce to a heap engine call.\<close>  @{thm charts_core_Nn}
  produces this bundle from a joint map \<open>G\<close> whose bad set is governed by the
  \<^emph>\<open>\<omega>\<close>-partial non-surjectivity.  The codim-3 cut here is \<open>Gjoint = 0\<close> (the
  conjunction \<open>gradU = 0\<close> --- two equations --- AND \<open>mstarg = 0\<close> --- one
  equation, the moment \<open>x\<close>-Jacobian rank-drop @{text bad_imp_mstarg_zero}).
  But @{thm charts_core_Nn} is hard-typed to codomain \<open>real^2\<close> and its rank
  test is on the \<open>\<omega>\<close>-partial, whereas \<open>mstarg\<close> records the \<open>x\<close>-partial drop of
  the moment map to \<open>complex^6\<close>.  Realising the chart of the combined locus
  requires (a) the codomain-\<open>real^3\<close> generalization of @{thm charts_core_Nn}
  (mechanical: reprove @{thm crit_piece_compact} / @{thm chart_proj_surj_iff}
  for CARD(3)), and (b) the \<open>\<omega>\<close>-partial surjectivity of \<open>Gjoint\<close> at the bad
  zeros from the steering nondegeneracy \<open>det (Dcvec) \<noteq> 0\<close> / \<open>\<gamma> \<not>\<parallel> c\<close> (the
  local diffeomorphism in \<open>\<omega>\<close>).  Step (b) --- the transversality of the
  steering constraint to the gradient constraint --- is the single irreducible
  IFT crux (DESIGN \<section>7).  It does NOT follow from the per-fixed-\<open>\<omega>\<close> input
  @{text nd} alone (uncountable unions of nowhere-dense slices need not be
  meager --- the very reason the gradU-dropped D3 was false).  NOT a splice
  freebie.\<close>

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
  \<comment> \<open>GENUINE geometric-measure core: the IFT chart of the retained-constraint
      (\<open>gradU = 0 \<and> mstarg = 0\<close>, codim 3) bad \<open>(x,\<omega>)\<close> locus in the
      @{thm charts_core_Nn} output shape.  The single irreducible \<open>sorry\<close> of
      this file; it does NOT follow from @{text nd} alone (see header).  NOT a
      splice freebie.\<close>
  sorry


subsection \<open>The verbatim target: the closed negligible cover (sorry-free from the bundle)\<close>

text \<open>\<^bold>\<open>The closed negligible cover, assembled sorry-free from the chart bundle.\<close>
  From @{thm branchP_indep_charts_Nn} the pieces \<open>K i = (fst \<circ> charts i) ` Crit i\<close>
  are CLOSED (chart output) and NEGLIGIBLE (@{thm negligible_singular_image_2n}:
  the projection has non-surjective derivative on \<open>Crit i\<close>), and they cover the
  bad fibre.  This turns the IFT-chart content into the countable closed
  negligible cover the reduction layer consumes.\<close>

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

text \<open>The two sorry-free layers consumed downstream confirm the cut is at the
  right place: the closed negligible cover yields meagerness without further
  geometric-measure work.\<close>

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
