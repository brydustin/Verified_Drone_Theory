section \<open>Degenerate critical points where the gradient is regular in the configuration\<close>

theory Regular_Stratum
  imports
    Null_Stratum
begin

lemma dip_slice_no_surj_deriv:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2" and C :: "(real^2) set"
  assumes oC: "open C" and wC: "\<omega> \<in> C"
    and hess0: "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
  shows "\<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                  (at \<omega> within C) \<and> surj D)"
proof
  assume "\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                (at \<omega> within C) \<and> surj D"
  then obtain D where
    dD: "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D) (at \<omega> within C)"
    and sD: "surj D" by (elim exE conjE)
  have dD': "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D) (at \<omega>)"
    using dD by (simp add: at_within_open[OF wC oC])
  have dH: "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative
              (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)) (at \<omega>)"
    by (rule gradU_dip_has_derivative)
  have DH: "D = (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)"
    by (rule has_derivative_unique[OF dD' dH])
  have "surj ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
    using sD unfolding DH by simp
  then have "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
    by (simp add: surj_matrix_vector_iff_det)
  with hess0 show False by simp
qed

lemma meager_grad_x_regular_part:
  fixes V :: "((real^2)^'n) set" and \<omega>0 \<omega>s :: "real^2"
  assumes openV: "open V" and Vne: "V \<noteq> {}"
  shows "meager {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  \<comment> \<open>The explicit x-partial field (the RHS of @{thm has_derivative_gradU_dip_x_explicit}).\<close>
  define DxF :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) \<Rightarrow> real^2" where
    "DxF x \<omega> = (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>)) (Dmoment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) h))"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
  have FX: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative DxF x \<omega>) (at x)"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
    unfolding DxF_def by (rule has_derivative_gradU_dip_x_explicit)
  have blDxF: "bounded_linear (DxF x \<omega>)" for x :: "(real^2)^'n" and \<omega> :: "real^2"
    using FX has_derivative_bounded_linear by blast

  \<comment> \<open>Step 2: the existential witness condition is surjectivity of the explicit field.\<close>
  have witness_iff:
    "(\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)
       \<longleftrightarrow> surj (DxF x \<omega>)"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
  proof
    assume "\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx"
    then obtain Dx :: "((real^2)^'n) \<Rightarrow> real^2" where
      d: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x)"
      and s: "surj Dx" by (elim exE conjE)
    have "Dx = DxF x \<omega>" by (rule has_derivative_unique[OF d FX])
    with s show "surj (DxF x \<omega>)" by simp
  next
    assume sx: "surj (DxF x \<omega>)"
    show "\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx"
      by (intro exI[where x="DxF x \<omega>"] conjI FX sx)
  qed

  \<comment> \<open>Step 3: the surjectivity locus is open (continuous Blinfun field + open surj locus).\<close>
  have apB: "blinfun_apply (Blinfun (DxF x \<omega>)) = DxF x \<omega>"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
    by (rule bounded_linear_Blinfun_apply[OF blDxF])
  have contB: "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
                 (\<lambda>z. Blinfun (DxF (fst z) (snd z)))"
  proof (rule continuous_on_blinfun_componentwise)
    fix i :: "(real^2)^'n" assume "i \<in> Basis"
    show "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
            (\<lambda>z. blinfun_apply (Blinfun (DxF (fst z) (snd z))) i)"
      unfolding apB
      unfolding DxF_def
      using continuous_on_gradU_dip_xpartial_applied[where i=i] by simp
  qed
  have oW: "open {z :: ((real^2)^'n) \<times> (real^2). surj (DxF (fst z) (snd z))}"
  proof -
    have isc: "continuous (at p) (\<lambda>z :: ((real^2)^'n) \<times> (real^2). Blinfun (DxF (fst z) (snd z)))"
      for p :: "((real^2)^'n) \<times> (real^2)"
      using continuous_on_eq_continuous_at[OF open_UNIV, THEN iffD1, OF contB] by blast
    have eq: "{z :: ((real^2)^'n) \<times> (real^2). surj (DxF (fst z) (snd z))}
            = (\<lambda>z :: ((real^2)^'n) \<times> (real^2). Blinfun (DxF (fst z) (snd z)))
                -` {A :: ((real^2)^'n) \<Rightarrow>\<^sub>L (real^2). surj (blinfun_apply A)}"
      by (auto simp: apB)
    show ?thesis unfolding eq
      by (rule continuous_open_vimage[OF open_surj_blinfun isc])
  qed

  \<comment> \<open>The open locus over \<open>V\<close>.\<close>
  define WV :: "(((real^2)^'n) \<times> (real^2)) set"
    where "WV = (V \<times> UNIV) \<inter> {z. surj (DxF (fst z) (snd z))}"
  have oWV: "open WV"
    unfolding WV_def by (intro open_Int open_Times openV open_UNIV oW)

  \<comment> \<open>Global \<open>C\<^sup>1\<close> data for the joint gradient field.\<close>
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                       has_derivative blinfun_apply (G' z)) (at z)"
      and contG': "continuous_on UNIV G'"
    using gradU_dip_joint_C1 by blast

  \<comment> \<open>Step 4: regular value on the locus, directly from the surjective x-partial.\<close>
  have regWV: "regular_value_on
      (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) WV 0"
  proof (rule regular_value_on_via_x_partial)
    show "open WV" by (rule oWV)
  next
    fix x :: "(real^2)^'n" and w :: "real^2"
    assume mem: "(x, w) \<in> WV"
      and G0: "(\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x, w) = 0"
    have sx: "surj (DxF x w)" using mem unfolding WV_def by simp
    show "\<exists>Dj Dx. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) has_derivative Dj)
                    (at (x, w))
                \<and> ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst (y, w)) (snd (y, w)))
                     has_derivative Dx) (at x)
                \<and> surj Dx"
    proof (intro exI conjI)
      show "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
               has_derivative blinfun_apply (G' (x, w))) (at (x, w))"
        by (rule derG)
    next
      show "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst (y, w)) (snd (y, w)))
               has_derivative DxF x w) (at x)"
        using FX[where x=x and \<omega>=w] by simp
    next
      show "surj (DxF x w)" by (rule sx)
    qed
  qed

  \<comment> \<open>Countable product-box cover of the locus.\<close>
  obtain A :: "nat \<Rightarrow> ((real^2)^'n) set" and B :: "nat \<Rightarrow> (real^2) set"
    where boxA: "\<And>n. open (A n)" and boxB: "\<And>n. open (B n)"
      and boxsub: "\<And>n. A n \<times> B n \<subseteq> WV"
      and boxun: "(\<Union>n. A n \<times> B n) = WV"
    using open_prod_nat_cover[OF oWV] by blast

  \<comment> \<open>the set of the transversality theorem over each box\<close>
  define bad :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "bad n = {x \<in> A n. \<exists>\<omega>\<in>B n.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and>
        \<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                 (at \<omega> within B n) \<and> surj D)}" for n
  have mbad: "\<And>n. meager (bad n)"
  proof -
    fix n :: nat
    show "meager (bad n)"
    proof (cases "A n = {}")
      case True
      then have "bad n = {}" unfolding bad_def by simp
      then show ?thesis by simp
    next
      case False
      have derGn: "\<And>z. z \<in> A n \<times> B n \<Longrightarrow>
          ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
             has_derivative blinfun_apply (G' z)) (at z)"
        by (rule derG)
      have contGn: "continuous_on (A n \<times> B n) G'"
        by (rule continuous_on_subset[OF contG' subset_UNIV])
      have regn: "regular_value_on
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (A n \<times> B n) 0"
        by (rule regular_value_on_subset[OF regWV boxsub])
      have "meager {x \<in> A n. \<exists>\<omega>\<in>B n.
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x, \<omega>) = 0 \<and>
          \<not> (\<exists>D. ((\<lambda>u. (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x, u))
                   has_derivative D) (at \<omega> within B n) \<and> surj D)}"
        using parametric_transversality_meager_planar_config[OF boxA False boxB
                derGn contGn regn] by blast
      then show ?thesis unfolding bad_def by simp
    qed
  qed
  have un_meager: "meager (\<Union>n. bad n)"
    by (rule meager_Union_nat) (rule mbad)

  \<comment> \<open>Step 5: the set is contained in the union of these sets.\<close>
  have set_rw: "{x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x)
                     \<and> surj Dx)}
       = {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> surj (DxF x \<omega>)}"
    unfolding witness_iff by (rule refl)
  have inj_sub: "{x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> surj (DxF x \<omega>)} \<subseteq> (\<Union>n. bad n)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> surj (DxF x \<omega>)}"
    then obtain \<omega> :: "real^2" where
      xV: "x \<in> V" and
      g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" and
      h0: "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" and
      sx: "surj (DxF x \<omega>)"
      by blast
    have inWV: "(x, \<omega>) \<in> WV"
      unfolding WV_def using xV sx by simp
    then obtain n where "(x, \<omega>) \<in> A n \<times> B n"
      using boxun by blast
    then have xA: "x \<in> A n" and wB: "\<omega> \<in> B n" by auto
    have nos: "\<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                       (at \<omega> within B n) \<and> surj D)"
      by (rule dip_slice_no_surj_deriv[OF boxB wB h0])
    have "x \<in> bad n"
      unfolding bad_def using xA wB g0 nos by blast
    then show "x \<in> (\<Union>n. bad n)" by blast
  qed

  show ?thesis
    unfolding set_rw by (rule meager_subset[OF inj_sub un_meager])
qed

end
