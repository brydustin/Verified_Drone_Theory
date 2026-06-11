theory Nonemptiness_Robust2
  imports "Applied_Math_Appendix_Base.Nonemptiness_Robust1"
begin

section \<open>Robust feasible set, part 2: the diagonal \<open>Sym\<^sup>2T\<close> moment transport laws\<close>

text \<open>This small theory is the second half of the original \<open>Nonemptiness_Robust\<close>:
  the two diagonal moment transport laws \<open>M11_moment_applyT\<close> / \<open>M22_moment_applyT\<close>
  ([E] brick 3, \<open>Sym\<^sup>2T\<close>).  Their original proofs carried pointwise \<open>key\<close>/\<open>sum_key\<close>
  identities with ~24 raw \<open>T $ i $ j\<close> vec-nth occurrences, which hang elaboration
  at parse time (the \<open>*\<close>-overload pathology documented at \<open>M12_moment_applyT\<close> in
  \<open>Nonemptiness_Robust3\<close>); under parallel scheduling they blew past the session
  timeout.  Here the proofs are rewritten with the matrix entries abbreviated as
  scalars (\<^theory_text>\<open>define t11 \<dots>\<close>), which parses immediately.  The expensive-but-stable
  first half lives in the \<open>Applied_Math_Appendix_Base\<close> heap (\<open>Nonemptiness_Robust1\<close>).\<close>

lemma M11_moment_applyT:
  fixes T :: "real^2^2"
  assumes "transpose T *v c = c0_paper"
  shows "M11_moment (applyT T y) c
       = of_real ((T $ 1 $ 1)\<^sup>2) * M11_moment y c0_paper
       + of_real (2 * (T $ 1 $ 1) * (T $ 1 $ 2)) * M12_moment y c0_paper
       + of_real ((T $ 1 $ 2)\<^sup>2) * M22_moment y c0_paper"
proof -
  define t11 where "t11 = T $ 1 $ 1"
  define t12 where "t12 = T $ 1 $ 2"
  have key: "\<And>n.
       phase c (applyT T y) n * (of_real ((applyT T y $ n) $ 1))\<^sup>2
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2))"
  proof -
    fix n
    have ph: "phase c (applyT T y) n = phase c0_paper y n"
      by (rule phase_applyT[OF assms])
    have lin: "(applyT T y $ n) $ 1 = t11 * (y $ n) $ 1 + t12 * (y $ n) $ 2"
      unfolding t11_def t12_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    show "phase c (applyT T y) n * (of_real ((applyT T y $ n) $ 1))\<^sup>2
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2))"
      using ph lin
      by (simp add: w_M12_def of_real_add of_real_mult power2_eq_square algebra_simps)
  qed

  have sum_key:
    "(\<Sum>n\<in>UNIV. phase c (applyT T y) n
          * (of_real ((applyT T y $ n) $ 1))\<^sup>2)
     =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2)))"
  proof -
    have "(\<Sum>n\<in>UNIV. phase c (applyT T y) n
          * (of_real ((applyT T y $ n) $ 1))\<^sup>2)
       =
      (\<Sum>n\<in>UNIV.
         phase c0_paper y n
           * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2))
       + phase c0_paper y n
           * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12))
       + phase c0_paper y n
           * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2)))"
      by (rule sum.cong, rule refl, simp add: key)
    also have "\<dots> =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2)))"
      by (simp add: sum.distrib add.assoc)
    finally show ?thesis .
  qed

  show ?thesis
    unfolding M11_moment_def M12_moment_def M22_moment_def
    using sum_key[unfolded t11_def t12_def]
    by (simp add: sum_distrib_left algebra_simps power2_eq_square ac_simps)
qed

lemma M22_moment_applyT:
  fixes T :: "real^2^2"
  assumes "transpose T *v c = c0_paper"
  shows "M22_moment (applyT T y) c
       = of_real ((T $ 2 $ 1)\<^sup>2) * M11_moment y c0_paper
       + of_real (2 * (T $ 2 $ 1) * (T $ 2 $ 2)) * M12_moment y c0_paper
       + of_real ((T $ 2 $ 2)\<^sup>2) * M22_moment y c0_paper"
proof -
  define t21 where "t21 = T $ 2 $ 1"
  define t22 where "t22 = T $ 2 $ 2"
  have key: "\<And>n.
       phase c (applyT T y) n * (of_real ((applyT T y $ n) $ 2))\<^sup>2
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2))"
  proof -
    fix n
    have ph: "phase c (applyT T y) n = phase c0_paper y n"
      by (rule phase_applyT[OF assms])
    have lin: "(applyT T y $ n) $ 2 = t21 * (y $ n) $ 1 + t22 * (y $ n) $ 2"
      unfolding t21_def t22_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    show "phase c (applyT T y) n * (of_real ((applyT T y $ n) $ 2))\<^sup>2
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2))"
      using ph lin
      by (simp add: w_M12_def of_real_add of_real_mult power2_eq_square algebra_simps)
  qed

  have sum_key:
    "(\<Sum>n\<in>UNIV. phase c (applyT T y) n
          * (of_real ((applyT T y $ n) $ 2))\<^sup>2)
     =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2)))"
  proof -
    have "(\<Sum>n\<in>UNIV. phase c (applyT T y) n
          * (of_real ((applyT T y $ n) $ 2))\<^sup>2)
       =
      (\<Sum>n\<in>UNIV.
         phase c0_paper y n
           * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2))
       + phase c0_paper y n
           * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22))
       + phase c0_paper y n
           * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2)))"
      by (rule sum.cong, rule refl, simp add: key)
    also have "\<dots> =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2)))"
      by (simp add: sum.distrib add.assoc)
    finally show ?thesis .
  qed

  show ?thesis
    unfolding M11_moment_def M12_moment_def M22_moment_def
    using sum_key[unfolded t21_def t22_def]
    by (simp add: sum_distrib_left algebra_simps power2_eq_square ac_simps)
qed



section \<open>The planar-config transversality engine\<close>

text \<open>Transport of the sorry-free Euclidean engine
  \<open>parametric_transversality_meager_euclidean_stub\<close> from \<open>\<real>\<^sup>m\<close> to the
  configuration type \<open>(\<real>\<^sup>2)^'n\<close>: flatten via the linear homeomorphism
  \<open>(real^2)^'n \<cong> real^('n bit0)\<close> (the \<open>\<Phi>/\<Psi>\<close> iso lifted from
  \<open>negligible_singular_image_2n\<close>; \<open>'n bit0\<close> is \<open>{finite,wellorder}\<close> by
  \<open>Numeral_Type\<close>), conjugate \<open>G\<close>/\<open>G'\<close> through the fixed bounded-linear pair
  map, transport \<open>regular_value_on\<close>, run the engine, and pull the bad set
  back through \<open>meager_homeo_image\<close>.  This is the workhorse for the four
  strata meagerness lemmas (M4--M6b in \<open>Nonemptiness_Robust3\<close>).\<close>

lemma parametric_transversality_meager_planar_config:
  fixes V :: "((real^2)^'n::finite) set"
    and \<Omega> :: "(real^2) set"
    and G :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^2)"
    and G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and openOm: "open \<Omega>"
    and derG: "\<And>z. z \<in> V \<times> \<Omega> \<Longrightarrow> (G has_derivative blinfun_apply (G' z)) (at z)"
    and contG': "continuous_on (V \<times> \<Omega>) G'"
    and reg0: "regular_value_on G (V \<times> \<Omega>) 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>\<Omega>. G (x, \<omega>) = 0
            \<and> \<not> (\<exists>D. ((\<lambda>u. G (x, u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D)}"
proof -
  \<comment> \<open>The flattening iso, lifted from @{thm negligible_singular_image_2n}'s proof.\<close>
  obtain \<beta> :: "'n bit0 \<Rightarrow> ('n \<times> 2)" where b: "bij \<beta>"
    using exists_index_bij by blast
  define \<gamma> :: "('n \<times> 2) \<Rightarrow> 'n bit0" where "\<gamma> = Hilbert_Choice.inv \<beta>"
  have g\<beta>: "\<gamma> (\<beta> k) = k" for k unfolding \<gamma>_def by (metis b bij_inv_eq_iff)
  have \<beta>g: "\<beta> (\<gamma> p) = p" for p unfolding \<gamma>_def by (meson b bij_inv_eq_iff)
  define \<Phi> :: "(real^2)^'n \<Rightarrow> real^('n bit0)"
    where "\<Phi> v = (\<chi> k. (v $ fst (\<beta> k)) $ snd (\<beta> k))" for v
  define \<Psi> :: "real^('n bit0) \<Rightarrow> (real^2)^'n"
    where "\<Psi> w = (\<chi> i. \<chi> j. w $ \<gamma> (i,j))" for w
  have lin\<Phi>: "linear \<Phi>"
  proof (rule Real_Vector_Spaces.linearI)
    show "\<And>u v :: (real^2)^'n. \<Phi> (u + v) = \<Phi> u + \<Phi> v"
      by (simp add: \<Phi>_def Finite_Cartesian_Product.vec_eq_iff
          Finite_Cartesian_Product.plus_vec_def)
    show "\<And>c :: real. \<And>u :: (real^2)^'n. \<Phi> (c *\<^sub>R u) = c *\<^sub>R \<Phi> u"
      by (simp add: \<Phi>_def Finite_Cartesian_Product.vec_eq_iff scaleR_vec_def)
  qed
  have lin\<Psi>: "linear \<Psi>"
  proof (rule Real_Vector_Spaces.linearI)
    show "\<And>u v :: real^('n bit0). \<Psi> (u + v) = \<Psi> u + \<Psi> v"
      by (simp add: \<Psi>_def Finite_Cartesian_Product.vec_eq_iff
          Finite_Cartesian_Product.plus_vec_def)
    show "\<And>c :: real. \<And>u :: real^('n bit0). \<Psi> (c *\<^sub>R u) = c *\<^sub>R \<Psi> u"
      by (simp add: \<Psi>_def Finite_Cartesian_Product.vec_eq_iff scaleR_vec_def)
  qed
  have \<Psi>\<Phi>: "\<Psi> (\<Phi> v) = v" for v
    by (simp add: \<Phi>_def \<Psi>_def Finite_Cartesian_Product.vec_eq_iff \<beta>g)
  have \<Phi>\<Psi>: "\<Phi> (\<Psi> w) = w" for w
    by (simp add: \<Phi>_def \<Psi>_def Finite_Cartesian_Product.vec_eq_iff g\<beta>)

  have bl\<Psi>: "bounded_linear \<Psi>" using lin\<Psi> linear_conv_bounded_linear by blast
  have bl\<Phi>: "bounded_linear \<Phi>" using lin\<Phi> linear_conv_bounded_linear by blast
  have surj\<Psi>: "surj \<Psi>" by (metis \<Psi>\<Phi> surjI)
  have surj\<Phi>: "surj \<Phi>" by (metis \<Phi>\<Psi> surjI)
  have homeo\<Psi>: "homeomorphism UNIV UNIV \<Psi> \<Phi>"
    unfolding homeomorphism_def
    using surj\<Psi> surj\<Phi>
    by (auto simp: \<Psi>\<Phi> \<Phi>\<Psi> linear_continuous_on[OF bl\<Psi>] linear_continuous_on[OF bl\<Phi>])

  \<comment> \<open>The conjugating pair map and its blinfun.\<close>
  define pm :: "((real^('n bit0)) \<times> (real^2)) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    where "pm z = (\<Psi> (fst z), snd z)" for z
  have blpm: "bounded_linear pm"
    unfolding pm_def
    by (intro bounded_linear_Pair bounded_linear_compose[OF bl\<Psi> bounded_linear_fst]
        bounded_linear_snd)
  define P :: "((real^('n bit0)) \<times> (real^2)) \<Rightarrow>\<^sub>L (((real^2)^'n) \<times> (real^2))"
    where "P = Blinfun pm"
  have P_apply: "blinfun_apply P = pm"
    unfolding P_def using blpm by (rule bounded_linear_Blinfun_apply)

  \<comment> \<open>Flattened data.\<close>
  define Ve :: "(real^('n bit0)) set" where "Ve = \<Phi> ` V"
  define Ge :: "((real^('n bit0)) \<times> (real^2)) \<Rightarrow> (real^2)"
    where "Ge z = G (pm z)" for z
  define Ge' :: "((real^('n bit0)) \<times> (real^2)) \<Rightarrow> (((real^('n bit0)) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where "Ge' z = (G' (pm z)) o\<^sub>L P" for z

  have Ve_alt: "Ve = \<Psi> -` V"
    unfolding Ve_def by (force simp: \<Psi>\<Phi> \<Phi>\<Psi>)
  have openVe: "open Ve"
    unfolding Ve_alt
    by (rule open_vimage[OF openV]) (rule linear_continuous_on[OF bl\<Psi>])
  have Vene: "Ve \<noteq> {}" unfolding Ve_def using Vne by blast
  have pm_im: "\<And>z. z \<in> Ve \<times> \<Omega> \<Longrightarrow> pm z \<in> V \<times> \<Omega>"
    unfolding pm_def Ve_alt by (auto simp: mem_Times_iff)
  have pm_surj_on: "pm ` (Ve \<times> \<Omega>) = V \<times> \<Omega>"
  proof
    show "pm ` (Ve \<times> \<Omega>) \<subseteq> V \<times> \<Omega>" using pm_im by blast
    show "V \<times> \<Omega> \<subseteq> pm ` (Ve \<times> \<Omega>)"
    proof
      fix q :: "(((real^2)^'n) \<times> (real^2))" assume qin: "q \<in> V \<times> \<Omega>"
      have "pm (\<Phi> (fst q), snd q) = q"
        unfolding pm_def by (simp add: \<Psi>\<Phi>)
      moreover have "(\<Phi> (fst q), snd q) \<in> Ve \<times> \<Omega>"
        using qin unfolding Ve_def by (auto simp: mem_Times_iff)
      ultimately show "q \<in> pm ` (Ve \<times> \<Omega>)" by force
    qed
  qed

  \<comment> \<open>C1 data transports by composition with the fixed bounded linear pm.\<close>
  have derGe: "\<And>z. z \<in> Ve \<times> \<Omega> \<Longrightarrow> (Ge has_derivative blinfun_apply (Ge' z)) (at z)"
  proof -
    fix z :: "((real^('n bit0)) \<times> (real^2))" assume zin: "z \<in> Ve \<times> \<Omega>"
    have dpm: "(pm has_derivative pm) (at z)"
      by (rule bounded_linear_imp_has_derivative[OF blpm])
    have dG: "(G has_derivative blinfun_apply (G' (pm z))) (at (pm z))"
      by (rule derG[OF pm_im[OF zin]])
    have "((G \<circ> pm) has_derivative (blinfun_apply (G' (pm z)) \<circ> pm)) (at z)"
      by (rule diff_chain_at[OF dpm dG])
    then show "(Ge has_derivative blinfun_apply (Ge' z)) (at z)"
      unfolding Ge_def Ge'_def o_def
      by (simp add: blinfun_compose.rep_eq P_apply o_def)
  qed

  have contGe': "continuous_on (Ve \<times> \<Omega>) Ge'"
  proof -
    have contpm: "continuous_on (Ve \<times> \<Omega>) pm"
      by (rule continuous_on_subset[OF linear_continuous_on[OF blpm] subset_UNIV])
    have 1: "continuous_on (Ve \<times> \<Omega>) (\<lambda>z. G' (pm z))"
      by (rule continuous_on_compose2[OF contG' contpm]) (use pm_im in blast)
    have blcomp: "bounded_linear (\<lambda>A. A o\<^sub>L P)"
      by (rule bounded_bilinear.bounded_linear_left[OF bounded_bilinear_blinfun_compose])
    have "continuous_on (Ve \<times> \<Omega>) (\<lambda>z. (G' (pm z)) o\<^sub>L P)"
      by (rule continuous_on_compose2[OF linear_continuous_on[OF blcomp] 1]) blast
    then show ?thesis unfolding Ge'_def .
  qed

  have reg0e: "regular_value_on Ge (Ve \<times> \<Omega>) 0"
  proof (rule regular_value_onI)
    fix z :: "((real^('n bit0)) \<times> (real^2))"
    assume zin: "z \<in> Ve \<times> \<Omega>" and Gz0: "Ge z = 0"
    have pmin: "pm z \<in> V \<times> \<Omega>" using pm_im[OF zin] .
    have gz0: "G (pm z) = 0" using Gz0 unfolding Ge_def .
    have ex: "\<exists>f'. (G has_derivative f') (at (pm z) within V \<times> \<Omega>) \<and> surj f'"
      by (rule mp[OF bspec[OF reg0[unfolded regular_value_on_def] pmin] gz0])
    then obtain D :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^2)"
      where D: "(G has_derivative D) (at (pm z) within V \<times> \<Omega>)" and sD: "surj D"
      by (elim exE conjE)
    have dpm: "(pm has_derivative pm) (at z within Ve \<times> \<Omega>)"
      by (rule has_derivative_at_withinI[OF bounded_linear_imp_has_derivative[OF blpm]])
    have Dw: "(G has_derivative D) (at (pm z) within pm ` (Ve \<times> \<Omega>))"
      using D pm_surj_on by simp
    have comp: "((\<lambda>w. G (pm w)) has_derivative (\<lambda>w. D (pm w))) (at z within Ve \<times> \<Omega>)"
      by (rule has_derivative_in_compose[OF dpm Dw])
    have spm: "surj pm"
      unfolding surj_def
    proof
      fix q :: "(((real^2)^'n) \<times> (real^2))"
      show "\<exists>x. q = pm x"
        by (rule exI[of _ "(\<Phi> (fst q), snd q)"]) (simp add: pm_def \<Psi>\<Phi>)
    qed
    have sDpm: "surj (\<lambda>w. D (pm w))"
      using comp_surj[OF spm sD] by (simp add: o_def)
    show "\<exists>f'. (Ge has_derivative f') (at z within Ve \<times> \<Omega>) \<and> surj f'"
      using comp sDpm unfolding Ge_def by blast
  qed

  \<comment> \<open>Run the sorry-free Euclidean engine at \<open>'m = 'n bit0\<close>.\<close>
  have core: "meager {w \<in> Ve. \<exists>\<omega>\<in>\<Omega>. Ge (w, \<omega>) = 0 \<and>
        \<not> (\<exists>D\<omega>. ((\<lambda>u. Ge (w, u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)}"
    using parametric_transversality_meager_euclidean_stub[OF openVe Vene openOm derGe contGe' reg0e]
    by blast

  \<comment> \<open>Pull the bad set back through the homeomorphism \<open>\<Psi>\<close>.\<close>
  have slice: "\<And>w u. Ge (w, u) = G (\<Psi> w, u)"
    unfolding Ge_def pm_def by simp
  have setim: "{x \<in> V. \<exists>\<omega>\<in>\<Omega>. G (x, \<omega>) = 0
            \<and> \<not> (\<exists>D. ((\<lambda>u. G (x, u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D)}
       = \<Psi> ` {w \<in> Ve. \<exists>\<omega>\<in>\<Omega>. Ge (w, \<omega>) = 0 \<and>
            \<not> (\<exists>D\<omega>. ((\<lambda>u. Ge (w, u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)}"
  proof (rule Set.set_eqI)
    fix x :: "(real^2)^'n"
    have slice_phix: "(\<lambda>u. Ge (\<Phi> x, u)) = (\<lambda>u. G (x, u))"
      by (simp add: slice \<Psi>\<Phi>)
    show "x \<in> {x \<in> V. \<exists>\<omega>\<in>\<Omega>. G (x, \<omega>) = 0
            \<and> \<not> (\<exists>D. ((\<lambda>u. G (x, u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D)}
       \<longleftrightarrow> x \<in> \<Psi> ` {w \<in> Ve. \<exists>\<omega>\<in>\<Omega>. Ge (w, \<omega>) = 0 \<and>
            \<not> (\<exists>D\<omega>. ((\<lambda>u. Ge (w, u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)}"
    proof
      assume xin: "x \<in> {x \<in> V. \<exists>\<omega>\<in>\<Omega>. G (x, \<omega>) = 0
            \<and> \<not> (\<exists>D. ((\<lambda>u. G (x, u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D)}"
      then have xV: "x \<in> V" and cond: "\<exists>\<omega>\<in>\<Omega>. G (x, \<omega>) = 0
            \<and> \<not> (\<exists>D. ((\<lambda>u. G (x, u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D)"
        by auto
      have "\<Phi> x \<in> Ve" using xV unfolding Ve_def by blast
      moreover have "\<exists>\<omega>\<in>\<Omega>. Ge (\<Phi> x, \<omega>) = 0 \<and>
            \<not> (\<exists>D\<omega>. ((\<lambda>u. Ge (\<Phi> x, u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)"
        using cond unfolding slice_phix by (simp add: slice \<Psi>\<Phi>)
      moreover have "x = \<Psi> (\<Phi> x)" by (simp add: \<Psi>\<Phi>)
      ultimately show "x \<in> \<Psi> ` {w \<in> Ve. \<exists>\<omega>\<in>\<Omega>. Ge (w, \<omega>) = 0 \<and>
            \<not> (\<exists>D\<omega>. ((\<lambda>u. Ge (w, u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)}"
        by blast
    next
      assume "x \<in> \<Psi> ` {w \<in> Ve. \<exists>\<omega>\<in>\<Omega>. Ge (w, \<omega>) = 0 \<and>
            \<not> (\<exists>D\<omega>. ((\<lambda>u. Ge (w, u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)}"
      then obtain w :: "real^('n bit0)"
        where xw: "x = \<Psi> w" and wVe: "w \<in> Ve"
          and condw: "\<exists>\<omega>\<in>\<Omega>. Ge (w, \<omega>) = 0 \<and>
            \<not> (\<exists>D\<omega>. ((\<lambda>u. Ge (w, u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)"
        by blast
      have xV: "x \<in> V" using wVe unfolding Ve_alt xw by auto
      have slw: "(\<lambda>u. Ge (w, u)) = (\<lambda>u. G (x, u))"
        unfolding xw by (simp add: slice)
      have "\<exists>\<omega>\<in>\<Omega>. G (x, \<omega>) = 0
            \<and> \<not> (\<exists>D. ((\<lambda>u. G (x, u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D)"
        using condw unfolding slw[symmetric] by (simp add: slice xw)
      then show "x \<in> {x \<in> V. \<exists>\<omega>\<in>\<Omega>. G (x, \<omega>) = 0
            \<and> \<not> (\<exists>D. ((\<lambda>u. G (x, u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D)}"
        using xV by blast
    qed
  qed

  show ?thesis
    unfolding setim by (rule meager_homeo_image[OF homeo\<Psi> core])
qed




section \<open>(M4) The regular stratum is meager\<close>

text \<open>Cover the open triple-regularity locus (\<open>A \<noteq> 0\<close>, \<open>surj DM\<close>, steering
  nonsingular) over \<open>V\<close> by countably many open product boxes
  (Helper 2, second countability), run
  \<open>parametric_transversality_meager_planar_config\<close> on each box (the joint
  \<open>C\<^sup>1\<close> field from \<open>gradU_dip_joint_C1\<close> and the regular value from
  \<open>regular_value_on_gradU_dip\<close> restrict to boxes, Helper 1), and inject the
  degenerate-critical set: \<open>det HessU = 0\<close> forbids a surjective slice
  derivative since the slice derivative IS the Hessian (Helper 3,
  \<open>gradU_dip_has_derivative\<close> + uniqueness at interior points).  Helpers 1-3
  are generic and reused by the remaining strata (M5/M6/M6b).\<close>

subsection \<open>Helper 1: \<open>regular_value_on\<close> restricts to subsets\<close>

lemma regular_value_on_subset:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes reg: "regular_value_on f S y" and sub: "T \<subseteq> S"
  shows "regular_value_on f T y"
proof (rule regular_value_onI)
  fix x assume xT: "x \<in> T" and fx: "f x = y"
  have xS: "x \<in> S" using xT sub by blast
  have ex: "\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f'"
    by (rule mp[OF bspec[OF reg[unfolded regular_value_on_def] xS] fx])
  then obtain f' where d: "(f has_derivative f') (at x within S)" and s: "surj f'"
    by (elim exE conjE)
  have "(f has_derivative f') (at x within T)"
    by (rule has_derivative_subset[OF d sub])
  then show "\<exists>f'. (f has_derivative f') (at x within T) \<and> surj f'"
    using s by blast
qed

subsection \<open>Helper 2: countable product-box cover of an open set in a product space\<close>

lemma open_prod_nat_cover:
  fixes W :: "(('a::second_countable_topology) \<times> ('b::second_countable_topology)) set"
  assumes oW: "open W"
  shows "\<exists>A :: nat \<Rightarrow> 'a set. \<exists>B :: nat \<Rightarrow> 'b set.
           (\<forall>n. open (A n)) \<and> (\<forall>n. open (B n)) \<and> (\<forall>n. A n \<times> B n \<subseteq> W)
         \<and> (\<Union>n. A n \<times> B n) = W"
proof -
  obtain BA :: "'a set set" where cA: "Countable_Set.countable BA" and tA: "topological_basis BA"
    using ex_countable_basis by blast
  obtain BB :: "'b set set" where cB: "Countable_Set.countable BB" and tB: "topological_basis BB"
    using ex_countable_basis by blast
  define P :: "('a set \<times> 'b set) set"
    where "P = {q \<in> BA \<times> BB. fst q \<times> snd q \<subseteq> W}"
  have cAB: "Countable_Set.countable (BA \<times> BB)"
    by (intro countable_SIGMA cA cB)
  have Psub: "P \<subseteq> BA \<times> BB" unfolding P_def by auto
  have cP: "Countable_Set.countable P" by (rule countable_subset[OF Psub cAB])
  have cover: "(\<Union>q\<in>P. fst q \<times> snd q) = W"
  proof
    show "(\<Union>q\<in>P. fst q \<times> snd q) \<subseteq> W" unfolding P_def by auto
    show "W \<subseteq> (\<Union>q\<in>P. fst q \<times> snd q)"
    proof
      fix p assume pW: "p \<in> W"
      obtain a b where pab: "p = (a, b)" by fastforce
      have exAB: "\<exists>Ao Bo. open Ao \<and> open Bo \<and> (a, b) \<in> Ao \<times> Bo \<and> Ao \<times> Bo \<subseteq> W"
        by (rule bspec[OF oW[unfolded open_prod_def] pW[unfolded pab]])
      then obtain Ao Bo where ABo0: "open Ao" "open Bo" "(a, b) \<in> Ao \<times> Bo" "Ao \<times> Bo \<subseteq> W"
        by (elim exE conjE)
      have ABo: "open Ao" "open Bo" "a \<in> Ao" "b \<in> Bo" "Ao \<times> Bo \<subseteq> W"
        using ABo0 by auto
      obtain UA where UA: "UA \<in> BA" "a \<in> UA" "UA \<subseteq> Ao"
        using topological_basisE[OF tA ABo(1) ABo(3)] by blast
      obtain UB where UB: "UB \<in> BB" "b \<in> UB" "UB \<subseteq> Bo"
        using topological_basisE[OF tB ABo(2) ABo(4)] by blast
      have UTsub: "UA \<times> UB \<subseteq> W" using UA(3) UB(3) ABo(5) by blast
      have qP: "(UA, UB) \<in> P" unfolding P_def using UA(1) UB(1) UTsub by auto
      show "p \<in> (\<Union>q\<in>P. fst q \<times> snd q)"
        using qP UA(2) UB(2) unfolding pab by force
    qed
  qed
  show ?thesis
  proof (cases "P = {}")
    case True
    then have Wempty: "W = {}" using cover by simp
    show ?thesis
      by (intro exI[of _ "\<lambda>n. ({} :: 'a set)"] exI[of _ "\<lambda>n. ({} :: 'b set)"])
         (simp add: Wempty)
  next
    case False
    define F where "F = from_nat_into P"
    have FP: "\<And>n. F n \<in> P" unfolding F_def by (rule from_nat_into[OF False])
    have rF: "range F = P" unfolding F_def by (rule range_from_nat_into[OF False cP])
    have uF: "(\<Union>n. fst (F n) \<times> snd (F n)) = (\<Union>q\<in>P. fst q \<times> snd q)"
    proof -
      have "(\<Union>n. fst (F n) \<times> snd (F n)) = (\<Union>q\<in>range F. fst q \<times> snd q)" by blast
      also have "\<dots> = (\<Union>q\<in>P. fst q \<times> snd q)" unfolding rF by (rule refl)
      finally show ?thesis .
    qed
    have FAB: "\<And>n. F n \<in> BA \<times> BB" using FP Psub by blast
    have openA: "\<And>n. open (fst (F n))"
    proof -
      fix n :: nat
      have "fst (F n) \<in> BA" using FAB[of n] by (simp add: mem_Times_iff)
      then show "open (fst (F n))" by (rule topological_basis_open[OF tA])
    qed
    have openB: "\<And>n. open (snd (F n))"
    proof -
      fix n :: nat
      have "snd (F n) \<in> BB" using FAB[of n] by (simp add: mem_Times_iff)
      then show "open (snd (F n))" by (rule topological_basis_open[OF tB])
    qed
    have subW: "\<And>n. fst (F n) \<times> snd (F n) \<subseteq> W"
      using FP unfolding P_def by auto
    show ?thesis
      by (intro exI[of _ "\<lambda>n. fst (F n)"] exI[of _ "\<lambda>n. snd (F n)"] conjI)
         (use openA openB subW uF cover in auto)
  qed
qed

subsection \<open>Helper 3: degenerate Hessian forbids a surjective slice derivative\<close>

lemma dip_slice_no_surj_deriv:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2" and C :: "(real^2) set"
  assumes oC: "open C" and wC: "\<omega> \<in> C"
    and hess0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
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
  then have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
    by (simp add: surj_matrix_vector_iff_det)
  with hess0 show False by simp
qed

subsection \<open>(M4) The regular stratum is meager\<close>

lemma meager_bad_regular_stratum:
  fixes V :: "((real^2)^'n) set" and \<omega>0 \<omega>s :: "real^2"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
proof -
  \<comment> \<open>The open triple-regularity locus over \<open>V\<close>.\<close>
  define WV :: "(((real^2)^'n) \<times> (real^2)) set"
    where "WV = {p \<in> V \<times> UNIV. A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
                             \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
                             \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}"
  have WVeq: "WV = (V \<times> UNIV) \<inter> {p :: ((real^2)^'n) \<times> (real^2).
                 A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
               \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
               \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}"
    unfolding WV_def by auto
  have oWV: "open WV"
    unfolding WVeq
    by (intro open_Int open_Times openV open_UNIV open_A_cart_nonzero)
  have regWV: "regular_value_on
      (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) WV 0"
    unfolding WV_def by (rule regular_value_on_gradU_dip[OF openV c6])
  \<comment> \<open>Global \<open>C\<^sup>1\<close> data for the joint gradient field.\<close>
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                       has_derivative blinfun_apply (G' z)) (at z)"
      and contG': "continuous_on UNIV G'"
    using gradU_dip_joint_C1 by blast
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
  \<comment> \<open>The M4 bad set injects into the union of engine bad sets.\<close>
  have inj_sub: "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0} \<subseteq> (\<Union>n. bad n)"
  proof
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
    then obtain \<omega> :: "real^2" where
      xV: "x \<in> V" and
      g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" and
      h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" and
      anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0" and
      dms: "surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))" and
      dcz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      by blast
    have inWV: "(x, \<omega>) \<in> WV"
      unfolding WV_def using xV anz dms dcz by simp
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
  show ?thesis by (rule meager_subset[OF inj_sub un_meager])
qed




section \<open>The pole-free angular domain \<open>OmegaPF\<close> (soundness fix)\<close>

text \<open>The paper's full angular box \<open>Omega ctr\<close> (theta-half-width \<open>\<pi>/2\<close>) ALWAYS
  contains pole points \<open>\<omega>\<^sub>1 \<in> \<pi>\<int>\<close>, where the dipole gain vanishes to second
  order and hence EVERY configuration is degenerate-critical (gradU = 0 with
  singular Hessian).  All robust-margin statements over that box are
  unsatisfiable.  Following the paper's own 2D-cut reduction (D_edit L1253),
  the spine is restated over the fat pole-free box \<open>OmegaPF ctr \<delta>\<close> with
  \<open>\<delta> < \<pi>/2\<close> chosen so the theta-interval avoids \<open>\<pi>\<int>\<close>.\<close>

definition OmegaPF :: "planar \<Rightarrow> real \<Rightarrow> planar set" where
  "OmegaPF ctr \<delta> = cbox (ctr - vector [\<delta>, pi]) (ctr + vector [\<delta>, pi])"

lemma OmegaPF_compact: "compact (OmegaPF ctr \<delta>)"
  unfolding OmegaPF_def by (rule compact_cbox)

lemma compact_minus_ball: "compact S \<Longrightarrow> compact (S - ball c \<epsilon>)"
proof -
  assume cS: "compact S"
  have "S - ball c \<epsilon> = S \<inter> (- ball c \<epsilon>)" by auto
  moreover have "compact (S \<inter> (- ball c \<epsilon>))"
    by (rule compact_Int_closed[OF cS closed_Compl[OF open_ball]])
  ultimately show ?thesis by simp
qed

lemma sphere_subset_OmegaPF:
  fixes ctr :: "real^2"
  assumes ed: "\<epsilon> \<le> \<delta>" and dpi: "\<delta> \<le> pi"
  shows "sphere ctr \<epsilon> \<subseteq> OmegaPF ctr \<delta>"
proof
  fix y assume "y \<in> sphere ctr \<epsilon>"
  hence dy: "dist y ctr = \<epsilon>" by (simp add: dist_commute sphere_def)
  show "y \<in> OmegaPF ctr \<delta>"
    unfolding OmegaPF_def mem_box_cart
  proof (intro allI)
    fix i :: 2
    have b: "\<bar>y$i - ctr$i\<bar> \<le> \<delta>"
    proof -
      have "\<bar>y$i - ctr$i\<bar> = \<bar>(y - ctr)$i\<bar>" by simp
      also have "\<dots> \<le> norm (y - ctr)" by (rule component_le_norm_cart)
      also have "\<dots> = \<epsilon>" using dy by (simp add: dist_norm)
      finally show ?thesis using ed by simp
    qed
    have v: "\<delta> \<le> (vector [\<delta>, pi] :: real^2) $ i"
      using exhaust_2[of i] dpi by (auto simp: vector_2)
    have lo: "(ctr - vector [\<delta>, pi]) $ i = ctr $ i - vector [\<delta>, pi] $ i"
      by (simp add: vector_minus_component)
    have hi: "(ctr + vector [\<delta>, pi]) $ i = ctr $ i + vector [\<delta>, pi] $ i"
      by (simp add: vector_add_component)
    have b1: "y$i - ctr$i \<le> \<delta>" using abs_le_D1[OF b] .
    have b2: "ctr$i - y$i \<le> \<delta>" using abs_le_D2[OF b] by simp
    show "(ctr - vector [\<delta>, pi]) $ i \<le> y $ i \<and> y $ i \<le> (ctr + vector [\<delta>, pi]) $ i"
      using lo hi v b1 b2 by linarith
  qed
qed

text \<open>(M4 restricted) The regular stratum over ANY witness domain \<open>K\<close> is meager ---
  free from the unrestricted version by \<open>meager_subset\<close>.\<close>

lemma meager_bad_regular_stratum_on:
  fixes V :: "((real^2)^'n) set" and \<omega>0 \<omega>s :: "real^2" and K :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>K. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  by (rule meager_subset[OF _ meager_bad_regular_stratum[OF openV Vne c6]]) auto


end
