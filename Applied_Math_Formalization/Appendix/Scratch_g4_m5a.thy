theory Scratch_g4_m5a
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5a) The x-partial-regular part of the rank-deficient stratum is meager.\<close>
  Mirror of @{thm meager_bad_regular_stratum} (M4): here the open locus \<open>W\<close> is the set of
  pairs \<open>(x,\<omega>)\<close> where the explicit x-partial of \<open>\<nabla>\<^sub>\<Omega>U_dip\<close> is surjective (DERIVATIVE-DISCIPLINE:
  the stratum condition is an existential \<open>has_derivative\<close>, equivalent to surjectivity of the
  explicit field by uniqueness of derivatives).  \<open>W\<close> is open via the continuous Blinfun field
  and @{thm open_surj_blinfun}; the regular value on \<open>W \<inter> (V \<times> UNIV)\<close> comes directly from
  @{thm regular_value_on_via_x_partial}; box cover + engine + Hessian-degeneracy injection
  exactly as in M4.\<close>

lemma meager_grad_x_regular_part:
  fixes V :: "((real^2)^'n) set" and \<omega>0 \<omega>s :: "real^2"
  assumes openV: "open V" and Vne: "V \<noteq> {}"
  shows "meager {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  \<comment> \<open>The explicit x-partial field (the RHS of @{thm has_derivative_gradU_dip_x_explicit}).\<close>
  define DxF :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) \<Rightarrow> real^2" where
    "DxF x \<omega> = (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h))"
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

  \<comment> \<open>The engine's bad set over each box.\<close>
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

  \<comment> \<open>Step 5: the M5a bad set injects into the union of engine bad sets.\<close>
  have set_rw: "{x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x)
                     \<and> surj Dx)}
       = {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> surj (DxF x \<omega>)}"
    unfolding witness_iff by (rule refl)
  have inj_sub: "{x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> surj (DxF x \<omega>)} \<subseteq> (\<Union>n. bad n)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> surj (DxF x \<omega>)}"
    then obtain \<omega> :: "real^2" where
      xV: "x \<in> V" and
      g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" and
      h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" and
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
