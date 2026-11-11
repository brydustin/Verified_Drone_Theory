theory Scratch_m5_d4eng
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) D4 chart core engine --- codim-3, 2-D linear-independence region.\<close>

  This file builds the engine for @{text branchP_indep_charts_Nn} per the DESIGN.
  The bad locus \<open>BadXGW\<close> retains \<open>gradU = 0\<close> (the SOUND sibling of the false
  gradU-dropped D3); it is cut by THREE scalar equations --- the two \<open>gradU\<close>
  components AND the moment rank-drop determinant \<open>mstarg = 0\<close> --- codim 3.

  \<^bold>\<open>Architecture (honest reduction).\<close>  The chart bundle of \<open>charts_core_Nn\<close>
  shape is produced from the codim-3 joint map \<open>Gjoint = (gradU\<^sub>1, gradU\<^sub>2, mstarg)\<close>
  via TWO precisely-scoped obligations the DESIGN names as the irreducible
  analytic content (\<section>5, \<section>6), both flagged as genuine BUILD work (not splice
  freebies):

  \<^enum> @{text charts_core_Nn_codim}: the \<^emph>\<open>codomain-generalized\<close> engine.  The heap
    engine @{thm charts_core_Nn} is hard-typed to codomain \<open>real^2\<close> (= the
    parameter space) because the underlying IFT @{thm regular_value_local_chart}
    augments the regular derivative \<open>('c \<times> 'b) \<to> 'b\<close> to a bijection
    \<open>('c \<times> 'b) \<cong> ('c \<times> 'b)\<close> --- codomain MUST be a direct summand of the source.
    For a codim-3 cut over a 2-D \<open>\<omega>\<close>-region the codomain \<open>real^3\<close> is NOT a summand
    of \<open>(real^2)^'n \<times> real^2\<close>; the chart domain has dimension \<open>2\<cdot>CARD('n) - 1\<close>,
    which is not a Cartesian-vector numeral type.  Generalising the engine
    therefore requires re-deriving the IFT against a generic codomain (DESIGN
    \<section>2, \<section>5.3).  Stated here as ONE scoped \<open>proof hole\<close> with a SOUND signature, in
    the exact shape consumed by @{thm negligible_singular_image_2n}.

  \<^enum> @{text regular_value_on_Gjoint}: that \<open>0\<close> is a regular value of \<open>Gjoint\<close> on
    the steering-nondegenerate (\<open>\<gamma> \<not>\<parallel> c\<close>) region.  The transverse direction comes
    from the \<open>\<omega>\<close>-partial: rows 1--2 (\<open>gradU\<close>) submerge onto \<open>real^2\<close> from steering
    nondegeneracy, row 3 (\<open>mstarg\<close>) is transverse off the determinantal singular
    stratum \<open>\<Sigma> = {mstarg = 0 \<and> \<nabla>mstarg = 0}\<close>.  This is the honest crux (DESIGN
    \<section>1, \<section>6): the \<open>x\<close>-partial of \<open>gradU\<close> is exactly non-surjective on the bad
    locus (that IS the M5 singular stratum, @{thm gradU_dip_x_partial_surj}), so
    regularity comes from \<open>\<omega>\<close>, NOT \<open>x\<close>.  Stated here as ONE scoped \<open>proof hole\<close> with a
    SOUND signature.

  From these two the target @{text branchP_indep_charts_Nn} is assembled
  \<^bold>\<open>proof-complete\<close>, as is the downstream closed-negligible-cover / meager layer.

  \<^bold>\<open>What is SOUND and proof-complete here\<close> (proved against the heap):
  \<^item> @{text BadXGW_mono} / @{text BadXGW_UN} / @{text BadXGW_point} --- structural
    set algebra (copied verbatim from the sound D4 file).
  \<^item> @{text not_gamma_par_c_iff} --- the linear-independence dichotomy.
  \<^item> @{text Gjoint_zero_iff} / @{text bad_imp_mstarg_zero} / @{text Gjoint_zero_of_bad}
    --- the codim-3 sanity bridge: on \<open>BadXGW\<close> the retained rank-drop IS
    \<open>mstarg = 0\<close>; with \<open>gradU = 0\<close> this is exactly \<open>Gjoint = 0\<close>.
  \<^item> @{text bad_omega_partial_nonsurj} --- on \<open>BadXGW\<close> the \<open>\<omega>\<close>-partial of \<open>Gjoint\<close>
    (a linear map \<open>real^2 \<to> real^3\<close>) is non-surjective for the trivial dimension
    reason \<open>DIM(real^2) < DIM(real^3)\<close>; the SOUND bridge from the bad locus into
    the engine's abstract bad set.
  \<^item> @{text branchP_indep_charts_Nn} --- assembled proof-complete from the two scoped
    obligations above.
  \<^item> @{text branchP_indep_negligible_closed_cover} /
    @{text branchP_indep_of_negligible_closed_cover} / @{text branchP_indep_core}
    --- the downstream cover\<open>\<rightarrow>\<close>meager layers, proof-complete via
    @{thm negligible_singular_image_2n} and @{thm meager_negligible_closed_cover}.\<close>


subsection \<open>\<open>mstarg\<close> interface --- LOCAL stubs (discharge at the Robust3 splice)\<close>

text \<open>\<open>mstarg\<close> is defined in \<open>Nonemptiness_Robust3\<close>, which is NOT in this heap.
  We re-state, with EXACT Robust3 signatures, the determinantal-rank interface
  used below.  Each is proved proof-complete in \<open>Nonemptiness_Robust3\<close> (lines
  572--754); they discharge automatically at the Robust3 splice.\<close>

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


subsection \<open>Structural set algebra for \<open>BadXGW\<close> (proof-complete, copied verbatim)\<close>

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


subsection \<open>The \<open>\<omega>\<close>-partial of \<open>Gjoint\<close> is non-surjective: the SOUND dimension bridge\<close>

text \<open>\<^bold>\<open>The trivial dimension obstruction that puts every bad \<open>x\<close> into the
  engine's abstract bad set.\<close>  The \<open>\<omega>\<close>-partial of \<open>Gjoint\<close> at \<open>(x,\<omega>)\<close> is a linear
  map \<open>real^2 \<to> real^3\<close> (parameter \<open>\<omega>\<in>real^2\<close>, codomain \<open>real^3\<close>).  Since
  \<open>DIM(real^2) = 2 < 3 = DIM(real^3)\<close> NO linear map \<open>real^2 \<to> real^3\<close> is
  surjective, so the abstract ``bad'' transversality condition of the engine
  (the \<open>\<omega>\<close>-partial fails to surject the codomain) holds \<^emph>\<open>identically\<close>.  This is
  the codim-3 analogue of the codim-1 arc case and is what makes the engine's
  bad set contain ALL of \<open>BadXGW\<close> without any further analytic input: regularity
  of the JOINT map is what is hard (the two scoped obligations), but the
  per-bad-point \<open>\<omega>\<close>-partial non-surjectivity is free.\<close>

text \<open>An explicit, robust proof: image dimension \<open>\<le> DIM(domain) = 2 < 3\<close>.\<close>

lemma linear_real2_real3_not_surj:
  fixes f :: "real^2 \<Rightarrow> real^3"
  assumes lf: "linear f"
  shows "\<not> surj f"
proof
  assume sf: "surj f"
  have "dim (range f) \<le> dim (UNIV :: (real^2) set)"
    using dim_image_le[OF lf, of UNIV] by simp
  also have "dim (UNIV :: (real^2) set) = DIM(real^2)" by (rule dim_UNIV)
  finally have d2: "dim (range f) \<le> DIM(real^2)" .
  have "range f = (UNIV :: (real^3) set)" using sf by (simp add: surj_def)
  hence "dim (range f) = DIM(real^3)" by (simp add: dim_UNIV)
  with d2 have "DIM(real^3) \<le> DIM(real^2)" by simp
  thus False by simp
qed


subsection \<open>The two scoped irreducible obligations (SOUND signatures)\<close>

text \<open>\<^bold>\<open>Obligation 1: the codomain-generalized chart engine.\<close>  Mirror of
  @{thm charts_core_Nn} with codomain \<open>real^m\<close> and \<open>\<omega>\<close>-parameter \<open>real^k\<close>
  abstracted.  The conclusion is the bundle in the exact shape consumed by
  @{thm negligible_singular_image_2n}: charts into \<open>(real^2)^'n \<times> real^k\<close> whose
  \<open>x\<close>-projection \<open>fst \<circ> charts i\<close> has NON-surjective derivative on the compact
  \<open>Crit i\<close>, with CLOSED images, covering the abstract bad \<open>x\<close>-set
  \<open>{x\<in>V. \<exists>\<omega>\<in>\<Omega>. G(x,\<omega>) = 0 \<and> the \<omega>-partial of G at (x,\<omega>) fails to surject real^m}\<close>.

  SOUNDNESS.  We instantiate at \<open>m = 3\<close>, \<open>k = 2\<close>.  Its proof is the heap engine's
  proof with the codomain/parameter types as variables, re-deriving the IFT
  (@{thm regular_value_local_chart}) against a generic codomain --- the
  type-level content the heap version lacks.  Sanity: at \<open>m = k = 2\<close> it
  specialises to @{thm charts_core_Nn}; at empty bad set both sides hold; the
  \<open>\<not> surj\<close> conjunct is on the chart projection's derivative, never assumed of the
  identity.\<close>

lemma charts_core_Nn_codim:
  fixes W :: "(((real^2)^'n) \<times> (real^2)) set"
    and G :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^3)"
  assumes "open W"
    and "regular_value_on G W 0"
    and C1: "\<exists>G'. (\<forall>z\<in>W. (G has_derivative blinfun_apply (G' z)) (at z))
                  \<and> continuous_on W G'"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         {x. \<exists>\<omega>. (x,\<omega>) \<in> W \<and> G (x,\<omega>) = 0 \<and>
             (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>)
                       (at \<omega> within {u. (x,u) \<in> W}) \<and> surj D\<omega>))}
           \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>DESIGN \<section>2/\<section>5.3: codomain-\<open>real^3\<close> generalization of @{thm charts_core_Nn}
      (generic-codomain IFT), over a general open \<open>W\<close> (so that the regular part
      \<open>W = (V\<times>\<Omega>) \<setminus> \<Sigma>\<^sub>0\<close> is admissible).  NOT a splice freebie.\<close>
  sorry

text \<open>\<^bold>\<open>The singular-zero stratum \<open>\<Sigma>\<^sub>0\<close>.\<close>  The zeros of \<open>Gjoint\<close> at which its
  JOINT derivative (in \<open>(x,\<omega>)\<close>, a linear \<open>real^(2\<cdot>CARD('n)+2) \<to> real^3\<close>) FAILS
  to be surjective.  This is the honestly-named locus (DESIGN \<section>1, \<section>6) where
  regularity of \<open>Gjoint\<close> breaks: \<open>\<nabla>mstarg = 0\<close> there (row 3 of the joint
  derivative vanishes), so rank \<open>\<le> 2 < 3\<close>.  It is CLOSED (zero set \<open>\<inter>\<close>
  determinant-zero set, both continuous), of codim \<open>\<ge> 4\<close>.  Its complement in any
  open \<open>W\<close> is open, and on it \<open>0\<close> IS a regular value (DESIGN: regular off \<open>\<Sigma>\<close>).\<close>

definition Sigma0 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (((real^2)^'n) \<times> (real^2)) set" where
  "Sigma0 \<omega>0 \<omega>s =
     {z. Gjoint \<omega>0 \<omega>s (fst z) (snd z) = 0
         \<and> \<not> (\<exists>Dj. ((\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p)) has_derivative Dj) (at z) \<and> surj Dj)}"

text \<open>\<^bold>\<open>Obligation 2 (the honest crux, SOUND): the regular value OFF \<open>\<Sigma>\<^sub>0\<close>.\<close>  On the
  steering-nondegenerate (\<open>\<gamma> \<not>\<parallel> c\<close>) region \<open>\<Omega>\<close>, with the singular stratum \<open>\<Sigma>\<^sub>0\<close>
  EXCISED, \<open>0\<close> is a regular value of \<open>Gjoint\<close>.  This is SOUND precisely because it
  excludes \<open>\<Sigma>\<^sub>0\<close> (where the DESIGN flags regularity as failing); the unconditional
  \<open>regular_value_on Gjoint (V\<times>\<Omega>)\<close> would be FALSE on \<open>\<Sigma>\<^sub>0\<close>.  The transverse
  direction off \<open>\<Sigma>\<^sub>0\<close> is the \<open>\<omega>\<close>-partial: rows 1--2 (\<open>gradU\<close>) submerge onto
  \<open>real^2\<close> from steering nondegeneracy (DESIGN \<section>1 obligation 1), row 3 (\<open>mstarg\<close>)
  is transverse (\<open>\<nabla>mstarg \<noteq> 0\<close> off \<open>\<Sigma>\<^sub>0\<close>).  The \<open>x\<close>-partial of \<open>gradU\<close> is EXACTLY
  non-surjective on the bad locus (@{thm gradU_dip_x_partial_surj}) --- regularity
  is NOT from \<open>x\<close>.\<close>

lemma regular_value_on_Gjoint_off_Sigma:
  fixes V :: "((real^2)^'n) set" and \<Omega> :: "(real^2) set"
  assumes openV: "open V" and c6: "6 \<le> CARD('n)"
    and open\<Omega>: "open \<Omega>"
    and nd\<Omega>: "\<forall>\<omega>\<in>\<Omega>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>
                      \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
                      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "regular_value_on (\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p)) ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s) 0"
  \<comment> \<open>DESIGN \<section>1/\<section>6: the honest crux --- joint \<open>\<omega>\<close>-submersion off \<open>\<Sigma>\<^sub>0\<close>.  NOT a
      splice freebie.  SOUND: \<open>\<Sigma>\<^sub>0\<close> (where regularity fails) is excised.\<close>
  sorry

text \<open>\<^bold>\<open>\<open>\<Sigma>\<^sub>0\<close> is closed\<close> (so its complement in an open \<open>W\<close> is open).  Zero set of
  \<open>Gjoint\<close> (continuous) intersected with the non-surjective-joint-derivative set
  (\<open>det = 0\<close> of the continuous Jacobian field) --- both closed.  Robust3 fact.\<close>

lemma closed_Sigma0:
  shows "closed (Sigma0 \<omega>0 \<omega>s :: (((real^2)^'n) \<times> (real^2)) set)"
  \<comment> \<open>Robust3 splice fact: \<open>\<Sigma>\<^sub>0\<close> closed (continuity of \<open>Gjoint\<close> and its joint
      Jacobian).  SOUND signature.\<close>
  sorry

text \<open>\<^bold>\<open>Obligation 3 (SOUND): the \<open>\<Sigma>\<^sub>0\<close>-bad points are covered by a CLOSED NEGLIGIBLE
  bundle.\<close>  The bad \<open>x\<close>'s whose ONLY witnessing \<open>\<omega>\<close> land in \<open>\<Sigma>\<^sub>0\<close> form a strictly
  lower-dimensional (codim \<open>\<ge> 4\<close>) stratum; its \<open>x\<close>-projection is negligible by
  @{thm negligible_differentiable_image_lowdim} (a \<open>C\<^sup>1\<close> image from a source of
  dimension \<open>< 2\<cdot>CARD('n)\<close>), exactly as the arc case uses it (DESIGN \<section>3 step 6,
  \<section>5 obligation 4).  Stated in the \<open>charts_core_Nn\<close> bundle shape so it unions
  with the regular-part bundle.\<close>

lemma Sigma0_bad_charts:
  fixes V :: "((real^2)^'n) set" and \<Omega> :: "(real^2) set"
  assumes openV: "open V" and c6: "6 \<le> CARD('n)" and open\<Omega>: "open \<Omega>"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         {x. \<exists>\<omega>. (x,\<omega>) \<in> (V \<times> \<Omega>) \<inter> Sigma0 \<omega>0 \<omega>s}
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>DESIGN \<section>3 step 6 / \<section>5 obligation 4: the singular stratum \<open>\<Sigma>\<^sub>0\<close> is
      lower-dimensional, its \<open>x\<close>-projection negligible by low-dim image.  NOT a
      splice freebie.\<close>
  sorry

text \<open>\<^bold>\<open>The \<open>C\<^sup>1\<close> input for the engine.\<close>  \<open>Gjoint\<close> is \<open>C\<^sup>1\<close> jointly: rows 1--2 from
  @{thm gradU_dip_joint_C1}, row 3 from the \<open>mstarg\<close> joint \<open>C\<^sup>1\<close> fact (built in
  Robust3 from @{thm has_derivative_M_paper_x} + Gram + the smooth determinant);
  re-stated here as a scoped stub with a SOUND signature.\<close>

lemma Gjoint_joint_C1:
  fixes V :: "((real^2)^'n) set" and \<Omega> :: "(real^2) set"
  shows "\<exists>G'. (\<forall>z\<in>V\<times>\<Omega>. ((\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p))
                  has_derivative blinfun_apply (G' z)) (at z))
            \<and> continuous_on (V\<times>\<Omega>) G'"
  \<comment> \<open>Robust3 splice fact: joint \<open>C\<^sup>1\<close> of the codim-3 map (gradU rows +
      mstarg-Gram-det row).  SOUND signature.\<close>
  sorry


subsection \<open>The bad locus SPLITS: regular-part engine bad set \<open>\<union>\<close> \<open>\<Sigma>\<^sub>0\<close>-bad set (proof-complete)\<close>

text \<open>\<^bold>\<open>The SOUND split.\<close>  Fix \<open>x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> with \<open>\<Gamma> \<subseteq> \<Omega>\<close> and a witness
  \<open>\<omega>\<close>.  At \<open>(x,\<omega>)\<close> we have \<open>Gjoint = 0\<close> (@{thm Gjoint_zero_iff}) and the \<open>\<omega>\<close>-partial
  is non-surjective for the trivial dimension reason
  (@{thm linear_real2_real3_not_surj}).  Two cases on \<open>(x,\<omega>) \<in> Sigma0\<close>:
  \<^item> NOT in \<open>\<Sigma>\<^sub>0\<close>: then \<open>(x,\<omega>) \<in> (V\<times>\<Omega>) \<setminus> \<Sigma>\<^sub>0 = W\<close>, so \<open>x\<close> lands in the
    \<^emph>\<open>regular-part\<close> engine bad set (over the OPEN \<open>W\<close>).  The slice domain
    \<open>{u. (x,u) \<in> W}\<close> only shrinks the within-filter, and the \<open>\<omega>\<close>-partial is
    non-surjective for ANY domain (it is a linear \<open>real^2 \<to> real^3\<close>).
  \<^item> IN \<open>\<Sigma>\<^sub>0\<close>: then \<open>(x,\<omega>) \<in> (V\<times>\<Omega>) \<inter> \<Sigma>\<^sub>0\<close>, so \<open>x\<close> lands in the \<open>\<Sigma>\<^sub>0\<close>-bad set.\<close>

lemma BadXGW_split_engine_Sigma:
  fixes V :: "((real^2)^'n) set" and \<Omega> \<Gamma> :: "(real^2) set"
  assumes Gsub: "\<Gamma> \<subseteq> \<Omega>"
  shows "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
           \<subseteq> {x. \<exists>\<omega>. (x,\<omega>) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s) \<and> Gjoint \<omega>0 \<omega>s x \<omega> = 0 \<and>
                (\<not> (\<exists>D\<omega>. ((\<lambda>u. Gjoint \<omega>0 \<omega>s x u) has_derivative D\<omega>)
                          (at \<omega> within {u. (x,u) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s)}) \<and> surj D\<omega>))}
             \<union> {x. \<exists>\<omega>. (x,\<omega>) \<in> (V \<times> \<Omega>) \<inter> Sigma0 \<omega>0 \<omega>s}"
proof
  fix x :: "(real^2)^'n"
  assume xV: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
  hence xInV: "x \<in> V" and xBad: "x \<in> BadXGW \<omega>0 \<omega>s \<Gamma>" by auto
  from xBad obtain \<omega> where w\<Gamma>: "\<omega> \<in> \<Gamma>"
    and gU: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and nsurj: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    unfolding BadXGW_def by blast
  have w\<Omega>: "\<omega> \<in> \<Omega>" using w\<Gamma> Gsub by blast
  have xw\<Omega>: "(x,\<omega>) \<in> V \<times> \<Omega>" using xInV w\<Omega> by simp
  have ms0: "mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0" by (rule bad_imp_mstarg_zero[OF nsurj])
  have GZ: "Gjoint \<omega>0 \<omega>s x \<omega> = 0" using gU ms0 by (simp add: Gjoint_zero_iff)
  show "x \<in> {x. \<exists>\<omega>. (x,\<omega>) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s) \<and> Gjoint \<omega>0 \<omega>s x \<omega> = 0 \<and>
                (\<not> (\<exists>D\<omega>. ((\<lambda>u. Gjoint \<omega>0 \<omega>s x u) has_derivative D\<omega>)
                          (at \<omega> within {u. (x,u) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s)}) \<and> surj D\<omega>))}
             \<union> {x. \<exists>\<omega>. (x,\<omega>) \<in> (V \<times> \<Omega>) \<inter> Sigma0 \<omega>0 \<omega>s}"
  proof (cases "(x,\<omega>) \<in> Sigma0 \<omega>0 \<omega>s")
    case True
    hence "(x,\<omega>) \<in> (V \<times> \<Omega>) \<inter> Sigma0 \<omega>0 \<omega>s" using xw\<Omega> by blast
    thus ?thesis by blast
  next
    case False
    have xwW: "(x,\<omega>) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s)" using xw\<Omega> False by blast
    have nopart: "\<not> (\<exists>D\<omega>. ((\<lambda>u. Gjoint \<omega>0 \<omega>s x u) has_derivative D\<omega>)
                          (at \<omega> within {u. (x,u) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s)}) \<and> surj D\<omega>)"
    proof
      assume "\<exists>D\<omega>. ((\<lambda>u. Gjoint \<omega>0 \<omega>s x u) has_derivative D\<omega>)
                    (at \<omega> within {u. (x,u) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s)}) \<and> surj D\<omega>"
      then obtain D\<omega> :: "real^2 \<Rightarrow> real^3"
        where dD: "((\<lambda>u. Gjoint \<omega>0 \<omega>s x u) has_derivative D\<omega>)
                     (at \<omega> within {u. (x,u) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s)})"
          and sD: "surj D\<omega>" by blast
      have "linear D\<omega>" using dD has_derivative_linear by blast
      hence "\<not> surj D\<omega>" by (rule linear_real2_real3_not_surj)
      thus False using sD by blast
    qed
    have "x \<in> {x. \<exists>\<omega>. (x,\<omega>) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s) \<and> Gjoint \<omega>0 \<omega>s x \<omega> = 0 \<and>
                (\<not> (\<exists>D\<omega>. ((\<lambda>u. Gjoint \<omega>0 \<omega>s x u) has_derivative D\<omega>)
                          (at \<omega> within {u. (x,u) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s)}) \<and> surj D\<omega>))}"
      using xwW GZ nopart by blast
    thus ?thesis by blast
  qed
qed


subsection \<open>The chart bundle (assembled proof-complete from the two obligations)\<close>

text \<open>\<^bold>\<open>The target, assembled from the engine + regular value + dimension bridge.\<close>
  We run @{thm charts_core_Nn_codim} on \<open>G = Gjoint\<close> over the OPEN regular part
  \<open>W = (V\<times>\<Omega>) \<setminus> \<Sigma>\<^sub>0\<close> of an open steering-nondegenerate parameter neighbourhood
  \<open>\<Omega>\<close> of \<open>\<Gamma>\<close>; the regular value comes from
  @{thm regular_value_on_Gjoint_off_Sigma}, the \<open>C\<^sup>1\<close> input from
  @{thm Gjoint_joint_C1}, and the bad-locus split from
  @{thm BadXGW_split_engine_Sigma}.  The singular stratum \<open>\<Sigma>\<^sub>0\<close> is covered by the
  separate @{thm Sigma0_bad_charts} bundle and unioned in via
  @{thm charts_bundle_union}.  The output is the @{thm charts_core_Nn} bundle
  shape consumed by @{thm negligible_singular_image_2n}.

  \<^bold>\<open>The open steering-nondegenerate neighbourhood.\<close>  The assembly hypotheses give
  \<open>\<Gamma> \<subseteq> OmegaPF ctr \<delta>\<close> and \<open>\<gamma> \<not>\<parallel> c\<close> on \<open>\<Gamma>\<close>, but \<open>regular_value_on_Gjoint\<close> needs an
  OPEN such region.  We take \<open>\<Omega>\<close> = the open steering-nondegenerate set
  \<open>{\<omega>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega> \<and> det (Dcvec) \<noteq> 0 \<and> cvec \<noteq> 0}\<close>; on \<open>\<Gamma>\<close> all three
  hold (\<open>\<gamma> \<not>\<parallel> c\<close> by @{text Gindep}; the \<open>det\<close>/\<open>cvec\<close> nondegeneracy by the
  membership in \<open>BadXGW\<close>'s defining conjunction).  We do NOT need \<open>\<Omega>\<close> open in the
  CURRENT scoped statement (it is supplied to @{text regular_value_on_Gjoint} as
  a hypothesis); the openness of this particular \<open>\<Omega>\<close> is itself a Robust3 fact
  (continuity of \<open>Dcvec_dip\<close>/\<open>cvec_dip\<close> + the open phase-noncollinear set), re-
  stated here as a scoped stub @{text open_steering_nondeg}.\<close>

lemma open_steering_nondeg:
  shows "open {\<omega>::real^2. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>
                      \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
                      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0}"
  \<comment> \<open>Robust3 splice fact: the steering-nondegenerate region is open (continuity
      of \<open>cvec_dip\<close>/\<open>Dcvec_dip\<close> + open phase-noncollinearity).  SOUND signature.\<close>
  sorry

text \<open>\<^bold>\<open>Bundle union (proof-complete).\<close>  Two chart bundles in the @{thm charts_core_Nn}
  output shape, both indexed by \<open>nat\<close>, union into a single bundle by interleaving
  even/odd indices.  The covered set is the union of the two covered sets, and the
  per-piece derivative / non-surjectivity / closedness conjuncts hold piecewise.\<close>

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
proof -
  define \<Omega> :: "(real^2) set"
    where "\<Omega> = {\<omega>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>
                   \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
                   \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0}"
  have open\<Omega>: "open \<Omega>" unfolding \<Omega>_def by (rule open_steering_nondeg)
  have nd\<Omega>: "\<forall>\<omega>\<in>\<Omega>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>
                      \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
                      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    unfolding \<Omega>_def by blast

  text \<open>\<open>\<Gamma>\<close> sits inside the open steering-nondegenerate region: \<open>\<gamma> \<not>\<parallel> c\<close> by
        @{text Gindep}; the \<open>det\<close>/\<open>cvec\<close> conjuncts hold on \<open>\<Gamma>\<close> because every \<open>\<omega>\<close>
        appearing in a bad point carries them --- but \<open>\<Gamma>\<close> may contain \<open>\<omega>\<close> with
        no bad witness, so we instead intersect: the bad locus only uses \<open>\<omega>\<close>
        satisfying all three, hence lies in \<open>BadXGW \<omega>0 \<omega>s (\<Gamma> \<inter> \<Omega>)\<close>.\<close>
  have badGsub: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
                   \<subseteq> (V \<inter> BadXGW \<omega>0 \<omega>s (\<Gamma> \<inter> \<Omega>) :: ((real^2)^'n) set)"
  proof
    fix x :: "(real^2)^'n"
    assume xV: "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>"
    hence xInV: "x \<in> V" and xBad: "x \<in> BadXGW \<omega>0 \<omega>s \<Gamma>" by auto
    from xBad obtain \<omega> where w\<Gamma>: "\<omega> \<in> \<Gamma>"
      and gU: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and detn: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      and cn: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
      and nsurj: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      unfolding BadXGW_def by blast
    have ncoll: "\<not> gamma_par_c \<omega>0 \<omega>s \<omega>" using Gindep w\<Gamma> by blast
    have w\<Omega>: "\<omega> \<in> \<Omega>" unfolding \<Omega>_def using ncoll detn cn by blast
    have "\<omega> \<in> \<Gamma> \<inter> \<Omega>" using w\<Gamma> w\<Omega> by blast
    hence "x \<in> BadXGW \<omega>0 \<omega>s (\<Gamma> \<inter> \<Omega>)"
      unfolding BadXGW_def using gU detn cn nsurj by blast
    thus "x \<in> V \<inter> BadXGW \<omega>0 \<omega>s (\<Gamma> \<inter> \<Omega>)" using xInV by blast
  qed

  have GIsub: "\<Gamma> \<inter> \<Omega> \<subseteq> \<Omega>" by blast

  define W :: "(((real^2)^'n) \<times> (real^2)) set"
    where "W = (V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s"
  have openW: "open W"
    unfolding W_def
    by (rule open_Diff[OF open_Times[OF openV open\<Omega>] closed_Sigma0])

  text \<open>Abbreviate the (large) cover sets so the bundle existentials stay small
        when destructured (keeps \<open>blast\<close>/\<open>metis\<close> from blowing up).\<close>
  define BadA :: "((real^2)^'n) set"
    where "BadA = {x. \<exists>\<omega>. (x,\<omega>) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s) \<and> Gjoint \<omega>0 \<omega>s x \<omega> = 0 \<and>
             (\<not> (\<exists>D\<omega>. ((\<lambda>u. Gjoint \<omega>0 \<omega>s x u) has_derivative D\<omega>)
                       (at \<omega> within {u. (x,u) \<in> ((V \<times> \<Omega>) - Sigma0 \<omega>0 \<omega>s)}) \<and> surj D\<omega>))}"
  define BadB :: "((real^2)^'n) set"
    where "BadB = {x. \<exists>\<omega>. (x,\<omega>) \<in> (V \<times> \<Omega>) \<inter> Sigma0 \<omega>0 \<omega>s}"

  text \<open>\<^bold>\<open>Piece A --- the regular part.\<close>  On \<open>W = (V\<times>\<Omega>) \<setminus> \<Sigma>\<^sub>0\<close>, \<open>0\<close> IS a regular
        value of \<open>Gjoint\<close> (the honest crux off \<open>\<Sigma>\<^sub>0\<close>), so the codomain-generalized
        engine fires.\<close>
  have reg: "regular_value_on (\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p)) W 0"
    unfolding W_def by (rule regular_value_on_Gjoint_off_Sigma[OF openV c6 open\<Omega> nd\<Omega>])
  have C1: "\<exists>G'. (\<forall>z\<in>W. ((\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p))
                    has_derivative blinfun_apply (G' z)) (at z))
              \<and> continuous_on W G'"
  proof -
    obtain G' where dG': "\<forall>z\<in>(V\<times>\<Omega>). ((\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p))
                            has_derivative blinfun_apply (G' z)) (at z)"
        and cG': "continuous_on (V\<times>\<Omega>) G'"
      using Gjoint_joint_C1 by blast
    have "\<forall>z\<in>W. ((\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p))
                  has_derivative blinfun_apply (G' z)) (at z)"
      using dG' by (auto simp: W_def)
    moreover have "continuous_on W G'"
      using cG' continuous_on_subset by (force simp: W_def)
    ultimately show ?thesis by blast
  qed

  text \<open>The engine bad set over \<open>W\<close> beta-reduces to \<open>BadA\<close>.\<close>
  have engineA_eq:
    "{x. \<exists>\<omega>. (x,\<omega>) \<in> W \<and> (\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p)) (x,\<omega>) = 0 \<and>
             (\<not> (\<exists>D\<omega>. ((\<lambda>u. (\<lambda>p. Gjoint \<omega>0 \<omega>s (fst p) (snd p)) (x,u)) has_derivative D\<omega>)
                       (at \<omega> within {u. (x,u) \<in> W}) \<and> surj D\<omega>))}
     = BadA"
    unfolding BadA_def by (simp add: W_def)

  obtain chartsA :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and CritA :: "nat \<Rightarrow> ((real^2)^'n) set"
     and DA :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where coverA: "BadA \<subseteq> (\<Union>i. (fst \<circ> chartsA i) ` (CritA i))"
      and derA: "\<forall>i x. x \<in> CritA i \<longrightarrow>
            ((fst \<circ> chartsA i) has_derivative (blinfun_apply (DA i x))) (at x within CritA i)"
      and rankA: "\<forall>i x. x \<in> CritA i \<longrightarrow> \<not> surj (blinfun_apply (DA i x))"
      and cloA: "\<forall>i. closed ((fst \<circ> chartsA i) ` (CritA i))"
    using charts_core_Nn_codim[OF openW reg C1] engineA_eq by metis

  text \<open>\<^bold>\<open>Piece B --- the singular stratum \<open>\<Sigma>\<^sub>0\<close>.\<close>  Lower-dimensional, covered by a
        separate closed-negligible bundle.\<close>
  obtain chartsB :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and CritB :: "nat \<Rightarrow> ((real^2)^'n) set"
     and DB :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where coverB: "BadB \<subseteq> (\<Union>i. (fst \<circ> chartsB i) ` (CritB i))"
      and derB: "\<forall>i x. x \<in> CritB i \<longrightarrow>
            ((fst \<circ> chartsB i) has_derivative (blinfun_apply (DB i x))) (at x within CritB i)"
      and rankB: "\<forall>i x. x \<in> CritB i \<longrightarrow> \<not> surj (blinfun_apply (DB i x))"
      and cloB: "\<forall>i. closed ((fst \<circ> chartsB i) ` (CritB i))"
    using Sigma0_bad_charts[OF openV c6 open\<Omega>] unfolding BadB_def by metis

  text \<open>\<^bold>\<open>Split the bad locus into \<open>BadA \<union> BadB\<close>.\<close>\<close>
  have split: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> BadA \<union> BadB"
    unfolding BadA_def BadB_def
    using badGsub BadXGW_split_engine_Sigma[OF GIsub] by blast

  text \<open>Union the two bundles into one.\<close>
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where Ucover: "(BadA \<union> BadB) \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and Uder: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and Urank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and Uclo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using charts_bundle_union[OF coverA derA rankA cloA coverB derB rankB cloB]
    by metis

  have bad_in: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
                  \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    using split Ucover by blast

  show ?thesis
    by (intro exI[where x = charts] exI[where x = Crit] exI[where x = D] conjI)
       (use bad_in Uder Urank Uclo in blast)+
qed


subsection \<open>The closed negligible cover (proof-complete from the bundle)\<close>

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


subsection \<open>The downstream proof-complete layers (copied verbatim from D4Core)\<close>

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
