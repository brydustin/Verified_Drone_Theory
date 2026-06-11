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




section \<open>(M6b) The \<open>A = 0\<close> degenerate stratum is meager\<close>

text \<open>The planar engine applied to \<open>G = cplx_r2 \<circ> af\<close> with GLOBAL regular value
  on \<open>V \<times> UNIV\<close> (odd \<open>N\<close>: \<open>dxA_surj\<close>; \<open>cvec = 0\<close> zeros are vacuous since
  \<open>af = CARD \<noteq> 0\<close>) --- no box cover needed.  Witness bridge: at an
  array-factor null every \<open>HessU\<close> term except the \<open>Hcmat\<close> block vanishes and
  \<open>Hcmat\<close> reduces to the first-moment Gram, giving
  \<open>det HessU = 4 gain\<^sup>2 (det(matrix Dcvec) \<cdot> Im(cnj \<mu>\<^sub>1 \<mu>\<^sub>2))\<^sup>2\<close>; the same quantity
  is the slice-Jacobian determinant of \<open>afR2\<close>, so degeneracy with
  \<open>gain \<noteq> 0\<close> (pole-free) forbids a surjective slice derivative.\<close>

section \<open>B4: the Hessian at array-factor nulls\<close>

lemma Hcmat_at_null:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  assumes null: "Afun x c = 0"
  shows "Hcmat x c = (\<chi> k. \<chi> l. 2 * Re (cnj (Mcfun x c l) * Mcfun x c k))"
  unfolding Hcmat_def using null by simp

lemma gradUc_at_null:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  assumes null: "M_paper x c $ 1 = 0"
  shows "gradU (\<lambda>c. c) (\<lambda>_. 1) x c = 0"
proof -
  have "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ j = 0" for j
    using gradUc_component_moments[of x c j, unfolded null] by simp
  thus ?thesis by (simp add: Finite_Cartesian_Product.vec_eq_iff)
qed

lemma Uc_at_null:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  assumes null: "M_paper x c $ 1 = 0"
  shows "U_cart (\<lambda>c. c) (\<lambda>_. 1) x c = 0"
  using Uc_eq_moment[of x c, unfolded null] by simp

lemma HessU_at_null:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes null: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
            \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))"
  unfolding HessU_dip_entry_moments
  by (simp add: gradUc_at_null[OF null] Uc_at_null[OF null])

text \<open>The determinant identity at nulls: \<open>det HessU = 4 gain\<^sup>2 (detJ \<cdot> Im(cnj M\<^sub>2 M\<^sub>3))\<^sup>2\<close>,
  where \<open>detJ = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))\<close> and \<open>M\<^sub>2, M\<^sub>3\<close> are the first
  moments.  The slice Jacobian of \<open>cplx_r2 \<circ> af\<close> has determinant
  \<open>detJ \<cdot> Im(cnj M\<^sub>2 M\<^sub>3)\<close>, hence \<open>det HessU = 4 gain\<^sup>2 (det sliceJac)\<^sup>2\<close>.\<close>

lemma det_HessU_at_null:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes nullA: "Afun x (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
  shows "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
       = 4 * (gain_dip \<omega>)\<^sup>2
           * (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
              * Im (cnj (Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 1)
                    * Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 2))\<^sup>2"
proof -
  have AmA: "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) = Afun x (cvec_dip \<omega>0 \<omega>s \<omega>)"
    by (simp add: A_moment_def Afun_def phase_def)
  have nullM: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = 0"
    by (simp add: M_paper_proj_A A_cart_eq_Afun AmA nullA)
  \<comment> \<open>scalarize: gain, the four Jacobian entries, and the moment Gram data\<close>
  define g where "g = gain_dip \<omega>"
  define j11 where "j11 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 1"
  define j21 where "j21 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 2"
  define j12 where "j12 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) $ 1"
  define j22 where "j22 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) $ 2"
  define \<mu>1 where "\<mu>1 = Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 1"
  define \<mu>2 where "\<mu>2 = Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 2"
  define n1 where "n1 = Re (cnj \<mu>1 * \<mu>1)"
  define n2 where "n2 = Re (cnj \<mu>2 * \<mu>2)"
  define r12 where "r12 = Re (cnj \<mu>1 * \<mu>2)"
  define i12 where "i12 = Im (cnj \<mu>1 * \<mu>2)"
  \<comment> \<open>the Gram relation \<open>n1 n2 = r12\<^sup>2 + i12\<^sup>2\<close>\<close>
  have gram: "n1 * n2 = r12\<^sup>2 + i12\<^sup>2"
  proof -
    have "n1 = (cmod \<mu>1)\<^sup>2" unfolding n1_def
      by (metis complex_norm_square mult.commute Re_complex_of_real)
    moreover have "n2 = (cmod \<mu>2)\<^sup>2" unfolding n2_def
      by (metis complex_norm_square mult.commute Re_complex_of_real)
    moreover have "(cmod (cnj \<mu>1 * \<mu>2))\<^sup>2 = r12\<^sup>2 + i12\<^sup>2"
      unfolding r12_def i12_def by (simp add: cmod_power2)
    moreover have "(cmod (cnj \<mu>1 * \<mu>2))\<^sup>2 = (cmod \<mu>1)\<^sup>2 * (cmod \<mu>2)\<^sup>2"
      by (simp add: norm_mult power_mult_distrib)
    ultimately show ?thesis by simp
  qed
  have r21: "Re (cnj \<mu>2 * \<mu>1) = r12"
    unfolding r12_def by simp
  have i21: "Im (cnj \<mu>2 * \<mu>1) = - i12"
    unfolding i12_def by simp
  have ReSym: "\<And>a b::complex. Re (cnj a * b) = Re (cnj b * a)" by simp
  \<comment> \<open>the four Hessian entries at the null, in scalar form\<close>
  have HcN: "Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>)
           = (\<chi> k. \<chi> l. 2 * Re (cnj (Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) l)
                              * Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) k))"
    by (rule Hcmat_at_null[OF nullA])
  have entry: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
      = g * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
           \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))" for k l
    unfolding g_def by (rule HessU_at_null[OF nullM])
  \<comment> \<open>expand the quadratic form entrywise (2-dim inner product and matvec)\<close>
  have qform: "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
        \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
      = 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 1
               * (n1 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1)
                  + r12 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2))
           + Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ 2
               * (r12 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 1)
                  + n2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ 2)))" for k l
    unfolding HcN inner_vec_def matrix_vector_mult_def
    using ReSym
    by (simp add: sum_2 n1_def n2_def r12_def \<mu>1_def \<mu>2_def algebra_simps)
  \<comment> \<open>determinant via the 2x2 formula and pure algebra\<close>
  have detJ: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = j11 * j22 - j12 * j21"
    unfolding j11_def j12_def j21_def j22_def
    by (simp add: det_2 matrix_def axis_def)
  have det2: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
      = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
        * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
      - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
        * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
    by (simp add: det_2)
  have detH: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
      = 4 * (g * g) * ((j11 * j22 - j12 * j21) * (j11 * j22 - j12 * j21))
          * (n1 * n2 - r12 * r12)"
    unfolding det2 entry qform
    unfolding j11_def[symmetric] j12_def[symmetric] j21_def[symmetric] j22_def[symmetric]
    by (simp add: algebra_simps)
  have sub: "n1 * n2 - r12 * r12 = i12 * i12"
    using gram by (simp add: power2_eq_square)
  show ?thesis
    unfolding g_def[symmetric] \<mu>1_def[symmetric] \<mu>2_def[symmetric] i12_def[symmetric] detJ
    by (simp add: detH sub power2_eq_square algebra_simps)
qed

section \<open>B1/B2: the array factor as an \<open>\<real>\<^sup>2\<close>-valued jointly-\<open>C\<^sup>1\<close> map\<close>

definition afR2 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (((real^2)^'n) \<times> (real^2)) \<Rightarrow> real^2" where
  "afR2 \<omega>0 \<omega>s p = cplx_r2 (af (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p))"

lemma af_eq_Afun: "af cvec x \<omega> = Afun x (cvec \<omega>)"
  by (simp add: af_def Afun_def)

lemma Afun_eq_A_moment: "Afun x c = A_moment x c"
  by (simp add: Afun_def A_moment_def phase_def)

lemma cplx_r2_zero: "cplx_r2 0 = 0"
  using bounded_linear_cplx_r2 by (simp add: linear_0 bounded_linear.linear)

lemma afR2_joint_C1:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "\<exists>G'::(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2)).
            (\<forall>z. (afR2 \<omega>0 \<omega>s has_derivative blinfun_apply (G' z)) (at z))
          \<and> continuous_on UNIV G'"
proof -
  define dcw :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^2) \<Rightarrow> real^2"
    where "dcw z = (\<lambda>k. cplx_r2 (\<Sum>n\<in>UNIV.
      (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s (snd z) k) \<bullet> ((fst z) $ n))
        * cis (- ((cvec_dip \<omega>0 \<omega>s (snd z)) \<bullet> ((fst z) $ n)))))" for z
  define D :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (((real^2)^'n) \<times> (real^2)) \<Rightarrow> real^2"
    where "D z = (\<lambda>w. cplx_r2 (DA_paper_x (fst z) (cvec_dip \<omega>0 \<omega>s (snd z)) (fst w))
                      + dcw z (snd w))" for z

  \<comment> \<open>the \<open>\<bm>x\<close>-partial\<close>
  have FX: "((\<lambda>y. cplx_r2 (Afun y (cvec_dip \<omega>0 \<omega>s \<omega>))) has_derivative
             (\<lambda>h. cplx_r2 (DA_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h))) (at x within UNIV)"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
  proof -
    have eqf: "(\<lambda>y. Afun y (cvec_dip \<omega>0 \<omega>s \<omega>)) = (\<lambda>y. A_moment y (cvec_dip \<omega>0 \<omega>s \<omega>))"
      by (rule ext) (rule Afun_eq_A_moment)
    have eqd: "DA_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) = d_A_moment_x x (cvec_dip \<omega>0 \<omega>s \<omega>)"
      by (rule ext) (simp add: DA_paper_x_def d_A_moment_x_def)
    have "((\<lambda>y. A_moment y (cvec_dip \<omega>0 \<omega>s \<omega>)) has_derivative
           d_A_moment_x x (cvec_dip \<omega>0 \<omega>s \<omega>)) (at x within UNIV)"
      by (rule has_derivative_A_moment_x)
    hence "((\<lambda>y. Afun y (cvec_dip \<omega>0 \<omega>s \<omega>)) has_derivative
           DA_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)) (at x within UNIV)"
      unfolding eqf eqd by assumption
    thus ?thesis
      by (rule bounded_linear.has_derivative[OF bounded_linear_cplx_r2])
  qed

  \<comment> \<open>the \<open>\<omega>\<close>-partial (chain through \<open>Dcvec\<close>, into \<open>cplx_r2\<close>)\<close>
  have FY0: "((\<lambda>u. cplx_r2 (Afun x (cvec_dip \<omega>0 \<omega>s u))) has_derivative dcw (x, \<omega>)) (at \<omega>)"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
  proof -
    have c1: "(cvec_dip \<omega>0 \<omega>s has_derivative Dcvec_dip \<omega>0 \<omega>s \<omega>) (at \<omega>)"
      by (rule has_derivative_cvec_dip)
    have c2: "(Afun x has_derivative
        (\<lambda>h. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n))
              * cis (-((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x$n))))) (at (cvec_dip \<omega>0 \<omega>s \<omega>))"
      by (rule has_derivative_Afun_c)
    have chain: "((\<lambda>u. Afun x (cvec_dip \<omega>0 \<omega>s u)) has_derivative
        (\<lambda>k. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> k) \<bullet> (x$n))
              * cis (-((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x$n))))) (at \<omega>)"
      using diff_chain_at[OF c1 c2] by (simp add: o_def)
    show ?thesis
      unfolding dcw_def fst_conv snd_conv
      by (rule bounded_linear.has_derivative[OF bounded_linear_cplx_r2 chain])
  qed
  have blw: "bounded_linear (dcw z)" for z
  proof -
    obtain x \<omega> where zxy: "z = (x, \<omega>)" by fastforce
    show ?thesis
      using FY0[of x \<omega>] has_derivative_bounded_linear unfolding zxy by blast
  qed
  have FY: "x' \<in> (UNIV :: ((real^2)^'n) set) \<Longrightarrow> \<omega>' \<in> (UNIV :: (real^2) set) \<Longrightarrow>
       ((\<lambda>u. cplx_r2 (Afun x' (cvec_dip \<omega>0 \<omega>s u))) has_derivative
          blinfun_apply (Blinfun (dcw (x', \<omega>')))) (at \<omega>' within UNIV)"
    for x' :: "(real^2)^'n" and \<omega>' :: "real^2"
    using FY0[of x' \<omega>'] has_derivative_at_withinI
    by (simp add: bounded_linear_Blinfun_apply blw)

  \<comment> \<open>joint continuity of the \<open>\<omega>\<close>-partial field, componentwise\<close>
  have cvs: "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
               (\<lambda>z. cvec_dip \<omega>0 \<omega>s (snd z))"
    by (rule continuous_on_compose2[OF continuous_on_cvec_dip
          continuous_on_snd[OF continuous_on_id] subset_UNIV])
  have xn: "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
               (\<lambda>z. (fst z) $ n)" for n
    by (rule bounded_linear.continuous_on[OF
          bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_fst]
          continuous_on_id])
  have contdcw: "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set) (\<lambda>z. dcw z w)"
    for w :: "real^2"
  proof -
    have inner_sum: "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
        (\<lambda>z. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s (snd z) w) \<bullet> ((fst z) $ n))
              * cis (- ((cvec_dip \<omega>0 \<omega>s (snd z)) \<bullet> ((fst z) $ n))))"
      by (intro continuous_on_sum continuous_on_cis continuous_intros
            continuous_on_Dcvec_dip_snd cvs xn)
    show ?thesis
      unfolding dcw_def
      by (rule bounded_linear.continuous_on[OF bounded_linear_cplx_r2 inner_sum])
  qed
  have contB: "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
                 (\<lambda>z. Blinfun (dcw z))"
  proof (rule continuous_on_blinfun_componentwise)
    fix w :: "real^2" assume "w \<in> Basis"
    show "continuous_on UNIV (\<lambda>z. blinfun_apply (Blinfun (dcw z)) w)"
      using contdcw by (simp add: bounded_linear_Blinfun_apply blw)
  qed
  have FYC: "continuous (at (x, \<omega>) within UNIV \<times> UNIV)
               (\<lambda>(x', \<omega>'). Blinfun (dcw (x', \<omega>')))"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
  proof -
    have "continuous (at (x, \<omega>) within UNIV)
            (\<lambda>z. Blinfun (dcw z))"
      using contB unfolding continuous_on_eq_continuous_within by blast
    thus ?thesis by (simp add: case_prod_unfold UNIV_Times_UNIV)
  qed

  \<comment> \<open>joint derivative at every point\<close>
  have blDA: "bounded_linear (\<lambda>h. cplx_r2 (DA_paper_x (fst z) (cvec_dip \<omega>0 \<omega>s (snd z)) h))"
    for z :: "((real^2)^'n) \<times> (real^2)"
    by (rule has_derivative_bounded_linear[OF FX[where x = "fst z" and \<omega> = "snd z"]])
  have blD: "bounded_linear (D z)" for z
    unfolding D_def
    by (intro bounded_linear_add
          bounded_linear_compose[OF blDA bounded_linear_fst]
          bounded_linear_compose[OF blw bounded_linear_snd])
  have hd: "(afR2 \<omega>0 \<omega>s has_derivative D z) (at z)" for z
  proof -
    obtain x \<omega> where zxy: "z = (x, \<omega>)" by fastforce
    have pd: "((\<lambda>(x', \<omega>'). cplx_r2 (Afun x' (cvec_dip \<omega>0 \<omega>s \<omega>'))) has_derivative
             (\<lambda>(tx, ty). cplx_r2 (DA_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) tx)
                + blinfun_apply (Blinfun (dcw (x, \<omega>))) ty))
           (at (x, \<omega>) within UNIV \<times> UNIV)"
      by (rule has_derivative_partialsI[OF FX FY FYC UNIV_I convex_UNIV])
    have feq: "(\<lambda>(x', \<omega>'). cplx_r2 (Afun x' (cvec_dip \<omega>0 \<omega>s \<omega>'))) = afR2 \<omega>0 \<omega>s"
      by (rule ext) (simp add: afR2_def af_eq_Afun split_beta)
    have deq: "(\<lambda>(tx, ty). cplx_r2 (DA_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) tx)
                 + blinfun_apply (Blinfun (dcw (x, \<omega>))) ty) = D (x, \<omega>)"
      unfolding D_def
      by (rule ext) (simp add: split_beta bounded_linear_Blinfun_apply[OF blw])
    have filt2: "(at (x, \<omega>) within (UNIV :: ((real^2)^'n) set) \<times> (UNIV :: (real^2) set))
                 = at (x, \<omega>)"
      by (simp add: UNIV_Times_UNIV)
    show ?thesis
      using pd unfolding zxy feq deq filt2 .
  qed

  \<comment> \<open>continuity of the full field\<close>
  have dcw0: "dcw z 0 = 0" for z
    unfolding dcw_def
    by (simp add: Dcvec_dip_def cplx_r2_zero)
  have da0: "DA_paper_x x c 0 = 0" for x :: "(real^2)^'n" and c :: "real^2"
    by (simp add: DA_paper_x_def d_phase_def)
  have cont: "continuous_on UNIV (\<lambda>z. Blinfun (D z))"
  proof (rule continuous_on_blinfun_componentwise)
    fix w :: "((real^2)^'n) \<times> (real^2)" assume "w \<in> Basis"
    then consider b where "b \<in> Basis" "w = (b, 0)" | e where "e \<in> Basis" "w = (0, e)"
      unfolding Basis_prod_def by auto
    thus "continuous_on UNIV (\<lambda>z. blinfun_apply (Blinfun (D z)) w)"
    proof cases
      case 1
      have cDA: "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
          (\<lambda>z. DA_paper_x (fst z) (cvec_dip \<omega>0 \<omega>s (snd z)) b)"
        unfolding DA_paper_x_def d_phase_def
        by (intro continuous_on_sum continuous_on_cis continuous_intros cvs xn)
      have cDA2: "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
          (\<lambda>z. cplx_r2 (DA_paper_x (fst z) (cvec_dip \<omega>0 \<omega>s (snd z)) b))"
        by (rule bounded_linear.continuous_on[OF bounded_linear_cplx_r2 cDA])
      have "continuous_on UNIV (\<lambda>z. D z w)"
        unfolding D_def \<open>w = (b, 0)\<close> fst_conv snd_conv
        by (simp add: dcw0 cDA2)
      thus ?thesis by (simp add: bounded_linear_Blinfun_apply blD)
    next
      case 2
      have "continuous_on UNIV (\<lambda>z. D z w)"
        unfolding D_def \<open>w = (0, e)\<close> fst_conv snd_conv
        using contdcw da0 by (simp add: cplx_r2_zero)
      thus ?thesis by (simp add: bounded_linear_Blinfun_apply blD)
    qed
  qed
  show ?thesis
  proof (intro exI[where x="\<lambda>z. Blinfun (D z)"] conjI allI)
    fix z
    show "(afR2 \<omega>0 \<omega>s has_derivative blinfun_apply (Blinfun (D z))) (at z)"
      using hd[of z] by (simp add: bounded_linear_Blinfun_apply blD)
  qed (rule cont)
qed

section \<open>B3: global regular value (odd \<open>N\<close>)\<close>

lemma dxA_eq_DA: "dxA cvec x \<omega> h = DA_paper_x x (cvec \<omega>) h"
  by (simp add: dxA_def DA_paper_x_def d_phase_def sum_distrib_left
        scaleR_conv_of_real algebra_simps)

text \<open>The TIGHT form: \<open>0\<close> is a regular value of the array factor on ALL of
  configuration-times-angle space --- no domain hypothesis whatsoever.  The
  witness derivative is the globally-defined joint \<open>C\<^sup>1\<close> field; its
  restriction to \<open>\<bm>x\<close>-directions equals the \<open>\<bm>x\<close>-partial by
  \<open>has_derivative_unique\<close>, so \<open>dxA_surj\<close>'s surjectivity lifts by pure range
  inclusion.  Any set-restricted form follows by \<open>regular_value_on_subset\<close>.\<close>

lemma afR2_regular_value_UNIV:
  fixes \<omega>0 \<omega>s :: "real^2"
  assumes oddN: "odd CARD('n)"
  shows "regular_value_on (afR2 \<omega>0 \<omega>s)
           (UNIV :: ((((real^2)^'n) \<times> (real^2)) set)) 0"
proof (rule regular_value_onI)
  fix z :: "((real^2)^'n) \<times> (real^2)"
  assume zin: "z \<in> (UNIV :: ((((real^2)^'n) \<times> (real^2)) set))"
    and z0: "afR2 \<omega>0 \<omega>s z = 0"
  obtain x \<omega> where zxy: "z = (x, \<omega>)" by fastforce
  have af0: "af (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0"
    using z0 unfolding zxy afR2_def by simp
  have cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  proof
    assume c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
    have "af (cvec_dip \<omega>0 \<omega>s) x \<omega> = of_nat (CARD('n))"
      by (simp add: af_def c0)
    moreover have "CARD('n) \<noteq> 0" using oddN by presburger
    ultimately show False using af0 by simp
  qed
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  have cnz': "c \<noteq> 0" unfolding c_def by (rule cnz)
  \<comment> \<open>the \<open>\<bm>x\<close>-partial at the zero\<close>
  have FXz: "((\<lambda>y. cplx_r2 (Afun y c)) has_derivative
              (\<lambda>h. cplx_r2 (DA_paper_x x c h))) (at x)"
  proof -
    have eqf: "(\<lambda>y. Afun y c) = (\<lambda>y. A_moment y c)"
      by (rule ext) (rule Afun_eq_A_moment)
    have eqd: "DA_paper_x x c = d_A_moment_x x c"
      by (rule ext) (simp add: DA_paper_x_def d_A_moment_x_def)
    have "((\<lambda>y. A_moment y c) has_derivative d_A_moment_x x c) (at x within UNIV)"
      by (rule has_derivative_A_moment_x)
    hence "((\<lambda>y. Afun y c) has_derivative DA_paper_x x c) (at x within UNIV)"
      unfolding eqf eqd by assumption
    thus ?thesis
      by (rule bounded_linear.has_derivative[OF bounded_linear_cplx_r2])
  qed
  \<comment> \<open>the joint derivative from B2, and the embedded slice\<close>
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG: "\<And>u. (afR2 \<omega>0 \<omega>s has_derivative blinfun_apply (G' u)) (at u)"
    using afR2_joint_C1[of \<omega>0 \<omega>s] by blast
  define D where "D = blinfun_apply (G' z)"
  have derD: "(afR2 \<omega>0 \<omega>s has_derivative D) (at z)"
    unfolding D_def by (rule derG)
  have emb: "((\<lambda>y. (y, \<omega>)) has_derivative (\<lambda>h. (h, 0))) (at x)"
    by (rule has_derivative_Pair[OF has_derivative_ident has_derivative_const])
  have sliceD: "((\<lambda>y. afR2 \<omega>0 \<omega>s (y, \<omega>)) has_derivative (\<lambda>h. D (h, 0))) (at x)"
    using diff_chain_at[OF emb derD[unfolded zxy]] by (simp add: o_def)
  have sliceF: "(\<lambda>y. afR2 \<omega>0 \<omega>s (y, \<omega>)) = (\<lambda>y. cplx_r2 (Afun y c))"
    by (rule ext) (simp add: afR2_def af_eq_Afun c_def)
  have uniq: "(\<lambda>h. D (h, 0)) = (\<lambda>h. cplx_r2 (DA_paper_x x c h))"
    by (rule has_derivative_unique[OF sliceD[unfolded sliceF] FXz])
  \<comment> \<open>surjectivity, lifted from \<open>dxA_surj\<close>\<close>
  have surjDA: "surj (\<lambda>h. DA_paper_x x c h)"
    unfolding surj_def
  proof
    fix w :: complex
    obtain h where "dxA (cvec_dip \<omega>0 \<omega>s) x \<omega> h = w"
      using dxA_surj[OF oddN cnz af0] by blast
    hence "DA_paper_x x c h = w"
      unfolding c_def by (simp add: dxA_eq_DA)
    thus "\<exists>h'. w = DA_paper_x x c h'" by auto
  qed
  have surjcDA: "surj (\<lambda>h. cplx_r2 (DA_paper_x x c h))"
    using comp_surj[OF surjDA surj_cplx_r2] by (simp add: o_def)
  have surjslice: "surj (\<lambda>h. D (h, 0))"
    unfolding uniq by (rule surjcDA)
  have surjD: "surj D"
    unfolding surj_def
  proof
    fix y :: "real^2"
    obtain h where "y = D (h, 0)" using surjslice unfolding surj_def by blast
    thus "\<exists>w. y = D w" by blast
  qed
  show "\<exists>f'. (afR2 \<omega>0 \<omega>s has_derivative f') (at z within UNIV) \<and> surj f'"
    using derD surjD by blast
qed

lemma afR2_regular_value:
  fixes \<omega>0 \<omega>s :: "real^2" and V :: "((real^2)^'n) set"
  assumes oddN: "odd CARD('n)"
  shows "regular_value_on (afR2 \<omega>0 \<omega>s) (V \<times> (UNIV :: (real^2) set)) 0"
  by (rule regular_value_on_subset[OF afR2_regular_value_UNIV[OF oddN] subset_UNIV])

section \<open>B4': degenerate null forbids a surjective slice derivative\<close>

lemma afR2_omega_partial:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative
      (\<lambda>k. cplx_r2 (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> k) \<bullet> (x $ n))
            * cis (- ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ n)))))) (at \<omega>)"
proof -
  have c1: "(cvec_dip \<omega>0 \<omega>s has_derivative Dcvec_dip \<omega>0 \<omega>s \<omega>) (at \<omega>)"
    by (rule has_derivative_cvec_dip)
  have c2: "(Afun x has_derivative
      (\<lambda>h. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n))
            * cis (-((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x$n))))) (at (cvec_dip \<omega>0 \<omega>s \<omega>))"
    by (rule has_derivative_Afun_c)
  have chain: "((\<lambda>u. Afun x (cvec_dip \<omega>0 \<omega>s u)) has_derivative
      (\<lambda>k. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> k) \<bullet> (x$n))
            * cis (-((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x$n))))) (at \<omega>)"
    using diff_chain_at[OF c1 c2] by (simp add: o_def)
  have feq: "(\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) = (\<lambda>u. cplx_r2 (Afun x (cvec_dip \<omega>0 \<omega>s u)))"
    by (rule ext) (simp add: afR2_def af_eq_Afun)
  show ?thesis
    unfolding feq
    by (rule bounded_linear.has_derivative[OF bounded_linear_cplx_r2 chain])
qed

lemma null_no_surj_slice:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2" and C :: "(real^2) set"
  assumes oC: "open C" and wC: "\<omega> \<in> C"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and null: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0"
    and hess0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
  shows "\<not> (\<exists>D. ((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D) (at \<omega> within C) \<and> surj D)"
proof
  assume "\<exists>D. ((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D) (at \<omega> within C) \<and> surj D"
  then obtain D where
    dD: "((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D) (at \<omega> within C)"
    and sD: "surj D" by (elim exE conjE)
  have dD': "((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D) (at \<omega>)"
    using dD by (simp add: at_within_open[OF wC oC])
  define S :: "(real^2) \<Rightarrow> complex"
    where "S k = (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> k) \<bullet> (x $ n))
            * cis (- ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ n))))" for k
  have dT: "((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative (\<lambda>k. cplx_r2 (S k))) (at \<omega>)"
    unfolding S_def[abs_def] by (rule afR2_omega_partial)
  have DEq: "D = (\<lambda>k. cplx_r2 (S k))"
    by (rule has_derivative_unique[OF dD' dT])
  \<comment> \<open>scalarize\<close>
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define \<mu>1 where "\<mu>1 = Mcfun x c 1"
  define \<mu>2 where "\<mu>2 = Mcfun x c 2"
  have Sval: "S k = (- \<i>) * (complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> k) $ 1) * \<mu>1
                  + complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> k) $ 2) * \<mu>2)" for k
    unfolding S_def \<mu>1_def \<mu>2_def Mcfun_def c_def
    by (simp add: inner_vec_def sum_2 sum.distrib sum_subtractf sum_negf
          sum_distrib_left of_real_add of_real_mult algebra_simps)
  \<comment> \<open>the slice determinant\<close>
  have linD: "linear D" using dD' has_derivative_linear by blast
  have matD: "(\<lambda>y. matrix D *v y) = D"
    by (rule matrix_vector_mul(2)[OF linD])
  have surjM: "surj (\<lambda>y. matrix D *v y)"
    unfolding matD by (rule sD)
  have detD: "det (matrix D) \<noteq> 0"
    using surjM by (simp add: surj_matrix_vector_iff_det)
  have ent: "matrix D $ i $ j = cplx_r2 (S (axis j 1)) $ i" for i j
    unfolding DEq matrix_def by simp
  have e11: "matrix D $ 1 $ 1 = Re (S (axis 1 1))"
    unfolding ent by (simp add: cplx_r2_def vector_2)
  have e21: "matrix D $ 2 $ 1 = Im (S (axis 1 1))"
    unfolding ent by (simp add: cplx_r2_def vector_2)
  have e12: "matrix D $ 1 $ 2 = Re (S (axis 2 1))"
    unfolding ent by (simp add: cplx_r2_def vector_2)
  have e22: "matrix D $ 2 $ 2 = Im (S (axis 2 1))"
    unfolding ent by (simp add: cplx_r2_def vector_2)
  have detD_eq: "det (matrix D) = Im (cnj (S (axis 1 1)) * S (axis 2 1))"
    by (simp add: det_2 e11 e12 e21 e22 algebra_simps)
  \<comment> \<open>compute the determinant in moment form\<close>
  define j11 where "j11 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 1"
  define j21 where "j21 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 2"
  define j12 where "j12 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) $ 1"
  define j22 where "j22 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) $ 2"
  have Imform: "Im (cnj (S (axis 1 1)) * S (axis 2 1))
      = (j11 * j22 - j12 * j21) * Im (cnj \<mu>1 * \<mu>2)"
    unfolding Sval j11_def j12_def j21_def j22_def
    by (simp add: algebra_simps)
  have detJ: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = j11 * j22 - j12 * j21"
    unfolding j11_def j12_def j21_def j22_def
    by (simp add: det_2 matrix_def axis_def)
  \<comment> \<open>the B4 connection: degeneracy kills exactly this quantity\<close>
  have nullA: "Afun x (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    using null by (simp add: A_cart_eq_Afun)
  have "4 * (gain_dip \<omega>)\<^sup>2
          * (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * Im (cnj \<mu>1 * \<mu>2))\<^sup>2 = 0"
    using det_HessU_at_null[OF nullA] hess0
    unfolding \<mu>1_def \<mu>2_def c_def by simp
  hence z0: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * Im (cnj \<mu>1 * \<mu>2) = 0"
    using gnz by simp
  have z1: "(j11 * j22 - j12 * j21) * Im (cnj \<mu>1 * \<mu>2) = 0"
    using z0 unfolding detJ .
  have z2: "det (matrix D) = (j11 * j22 - j12 * j21) * Im (cnj \<mu>1 * \<mu>2)"
    unfolding detD_eq Imform by (rule refl)
  show False using detD z2 z1 by simp
qed

section \<open>(M6b) assembly\<close>

lemma A_cart_eq_af: "A_cart cvec x \<omega> = af cvec x \<omega>"
  by (simp add: A_cart_def af_def)

lemma meager_Azero_degenerate_stratum:
  fixes V :: "((real^2)^'n) set" and ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and oddN: "odd CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
proof -
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG: "\<And>u. (afR2 \<omega>0 \<omega>s has_derivative blinfun_apply (G' u)) (at u)"
      and contG: "continuous_on UNIV G'"
    using afR2_joint_C1[of \<omega>0 \<omega>s] by blast
  have derGn: "\<And>z. z \<in> V \<times> (UNIV :: (real^2) set) \<Longrightarrow>
      (afR2 \<omega>0 \<omega>s has_derivative blinfun_apply (G' z)) (at z)"
    by (rule derG)
  have contGn: "continuous_on (V \<times> (UNIV :: (real^2) set)) G'"
    by (rule continuous_on_subset[OF contG subset_UNIV])
  have regn: "regular_value_on (afR2 \<omega>0 \<omega>s) (V \<times> (UNIV :: (real^2) set)) 0"
    by (rule afR2_regular_value[OF oddN])
  have core: "meager {x \<in> V. \<exists>\<omega>\<in>(UNIV :: (real^2) set).
      afR2 \<omega>0 \<omega>s (x, \<omega>) = 0 \<and>
      \<not> (\<exists>D. ((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D) (at \<omega> within UNIV) \<and> surj D)}"
    using parametric_transversality_meager_planar_config[OF openV Vne open_UNIV
            derGn contGn regn] by blast
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}
       \<subseteq> {x \<in> V. \<exists>\<omega>\<in>(UNIV :: (real^2) set).
      afR2 \<omega>0 \<omega>s (x, \<omega>) = 0 \<and>
      \<not> (\<exists>D. ((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D) (at \<omega> within UNIV) \<and> surj D)}"
  proof
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
    then obtain \<omega> where xV: "x \<in> V" and wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and a0: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0"
      by blast
    have gnz: "gain_dip \<omega> \<noteq> 0"
      using bspec[OF pf wD] by (rule gain_dip_nonzero_of_sin)
    have af0: "afR2 \<omega>0 \<omega>s (x, \<omega>) = 0"
      using a0 by (simp add: afR2_def A_cart_eq_af[symmetric])
    have nos: "\<not> (\<exists>D. ((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D)
                       (at \<omega> within (UNIV :: (real^2) set)) \<and> surj D)"
      by (rule null_no_surj_slice[OF open_UNIV UNIV_I gnz a0 h0])
    show "x \<in> {x \<in> V. \<exists>\<omega>\<in>(UNIV :: (real^2) set).
        afR2 \<omega>0 \<omega>s (x, \<omega>) = 0 \<and>
        \<not> (\<exists>D. ((\<lambda>u. afR2 \<omega>0 \<omega>s (x, u)) has_derivative D) (at \<omega> within UNIV) \<and> surj D)}"
      using xV af0 nos by blast
  qed
  show ?thesis by (rule meager_subset[OF sub core])
qed




section \<open>(M6) The steering-singular stratum is meager\<close>

text \<open>Assembled from the parallel wave (agents G1/G2/G3): R4 = the gdip-derivative
  zero classification (log-derivative monotonicity of gsinc); R5 = fixed-angle
  slices nowhere dense (component-2 criticality + the analytic-slice engine +
  a one-displaced-element witness; empty at \<open>cvec = 0\<close> via surj-DM);
  R3 = the kernel-direction reduction; assembly = witness angles confined to a
  FINITE set (cos zeros x phase-lattice zeros), finite union of slices.\<close>


section \<open>G1: the zero set of the \<open>gdip\<close> derivative on \<open>{\<theta>. sin \<theta> \<noteq> 0}\<close>\<close>

text \<open>We show \<open>frechet_derivative gdip (at \<theta>) 1 = 0 \<longleftrightarrow> cos \<theta> = 0\<close> whenever
  \<open>sin \<theta> \<noteq> 0\<close>.  Strategy: an explicit derivative of \<open>gsinc\<close> off zero, the chain/product
  derivative of \<open>gdip\<close>, and a strict-monotonicity argument for the bracket
  \<open>gsinc' u\<^sup>- gsinc u\<^sup>+ - gsinc u\<^sup>- gsinc' u\<^sup>+\<close> via \<open>h x = cos x / sin x - 1/x\<close>
  (strictly decreasing on \<open>(0, \<pi>)\<close> because \<open>0 < sin x < x\<close> there).\<close>

subsection \<open>The explicit derivative of \<open>gsinc\<close> off zero\<close>

definition gsincd :: "real \<Rightarrow> real" where
  "gsincd x = (x * cos x - sin x) / x^2"

lemma g1_gsinc_has_deriv:
  fixes x :: real
  assumes x0: "x \<noteq> 0"
  shows "(gsinc has_real_derivative gsincd x) (at x)"
proof -
  have raw: "((\<lambda>y. sin y / y) has_real_derivative (cos x * x - sin x * 1) / (x * x)) (at x)"
    by (rule DERIV_divide[OF DERIV_sin DERIV_ident x0])
  have eq: "(cos x * x - sin x * 1) / (x * x) = gsincd x"
    by (simp add: gsincd_def power2_eq_square mult.commute)
  have step: "((\<lambda>y. sin y / y) has_real_derivative gsincd x) (at x)"
    using raw unfolding eq .
  show ?thesis
  proof (rule has_field_derivative_transform_within_open[OF step, where S = "- {0::real}"])
    show "open (- {0::real})" by (rule open_Compl) (rule closed_singleton)
    show "x \<in> - {0::real}" using x0 by simp
    show "\<And>y. y \<in> - {0::real} \<Longrightarrow> sin y / y = gsinc y"
      by (simp add: gsinc_def)
  qed
qed

subsection \<open>Strict bound \<open>sin x < x\<close> on \<open>(0, \<pi>]\<close>\<close>

lemma g1_sin_lt:
  fixes x :: real
  assumes x0: "0 < x" and xpi: "x \<le> pi"
  shows "sin x < x"
proof -
  have ex: "\<exists>z::real. 0 < z \<and> z < x \<and> sin x - sin 0 = (x - 0) * cos z"
    by (rule MVT2[OF x0]) (rule DERIV_sin)
  then obtain z :: real where z0: "0 < z" and zx: "z < x"
    and eq: "sin x - sin 0 = (x - 0) * cos z"
    by (elim exE conjE)
  have zpi: "z \<le> pi" using zx xpi by linarith
  have "cos z < cos 0"
    by (rule cos_monotone_0_pi[OF order.refl z0 zpi])
  hence cz1: "cos z < 1" by simp
  have sx: "sin x = x * cos z" using eq by simp
  have "x * cos z < x * 1" by (rule mult_strict_left_mono[OF cz1 x0])
  with sx show ?thesis by simp
qed

subsection \<open>Positivity of \<open>gsinc\<close> on \<open>(0, \<pi>)\<close>\<close>

lemma g1_gsinc_pos:
  fixes x :: real
  assumes x0: "0 < x" and xpi: "x < pi"
  shows "0 < gsinc x"
proof -
  have "0 < sin x / x" by (rule divide_pos_pos[OF sin_gt_zero[OF x0 xpi] x0])
  with x0 show ?thesis by (simp add: gsinc_def)
qed

subsection \<open>The auxiliary function \<open>h x = cos x / sin x - 1/x\<close>\<close>

lemma g1_h_deriv:
  fixes x :: real
  assumes x0: "0 < x" and xpi: "x < pi"
  shows "((\<lambda>y. cos y / sin y - 1 / y) has_real_derivative
           inverse (x^2) - inverse ((sin x)^2)) (at x)"
proof -
  have sx: "sin x \<noteq> 0" using sin_gt_zero[OF x0 xpi] by simp
  have xne: "x \<noteq> 0" using x0 by simp
  have d1raw: "((\<lambda>y. cos y / sin y) has_real_derivative
                 (- sin x * sin x - cos x * cos x) / (sin x * sin x)) (at x)"
    by (rule DERIV_divide[OF DERIV_cos DERIV_sin sx])
  have num: "- sin x * sin x - cos x * cos x = - 1"
    using sin_cos_squared_add[of x, unfolded power2_eq_square] by linarith
  have e1: "(- sin x * sin x - cos x * cos x) / (sin x * sin x) = - inverse ((sin x)^2)"
    unfolding num by (simp add: power2_eq_square inverse_eq_divide)
  have d1: "((\<lambda>y. cos y / sin y) has_real_derivative - inverse ((sin x)^2)) (at x)"
    using d1raw unfolding e1 .
  have d2raw: "((\<lambda>y. 1 / y) has_real_derivative (0 * x - 1 * 1) / (x * x)) (at x)"
    by (rule DERIV_divide[OF DERIV_const DERIV_ident xne])
  have e2: "(0 * x - 1 * 1) / (x * x) = - inverse (x^2)"
    by (simp add: power2_eq_square inverse_eq_divide)
  have d2: "((\<lambda>y. 1 / y) has_real_derivative - inverse (x^2)) (at x)"
    using d2raw unfolding e2 .
  have dd: "((\<lambda>y. cos y / sin y - 1 / y) has_real_derivative
              - inverse ((sin x)^2) - (- inverse (x^2))) (at x)"
    by (rule DERIV_diff[OF d1 d2])
  have e3: "- inverse ((sin x)^2) - (- inverse (x^2)) = inverse (x^2) - inverse ((sin x)^2)"
    by simp
  show ?thesis using dd unfolding e3 .
qed

lemma g1_hderiv_neg:
  fixes x :: real
  assumes x0: "0 < x" and xpi: "x < pi"
  shows "inverse (x^2) - inverse ((sin x)^2) < 0"
proof -
  have spos: "0 < sin x" by (rule sin_gt_zero[OF x0 xpi])
  have slt: "sin x < x" by (rule g1_sin_lt[OF x0 less_imp_le[OF xpi]])
  have p2: "(sin x)^2 < x^2"
    using power_strict_mono[OF slt less_imp_le[OF spos], of 2] by simp
  have "inverse (x^2) < inverse ((sin x)^2)"
    by (rule less_imp_inverse_less[OF p2 zero_less_power[OF spos]])
  thus ?thesis by linarith
qed

subsection \<open>The key bracket positivity\<close>

lemma g1_bracket_pos:
  fixes a b :: real
  assumes a0: "0 < a" and ab: "a < b" and bpi: "b < pi"
  shows "0 < gsincd a * gsinc b - gsinc a * gsincd b"
proof -
  have api: "a < pi" using ab bpi by linarith
  have b0: "0 < b" using a0 ab by linarith
  define h :: "real \<Rightarrow> real" where "h = (\<lambda>y. cos y / sin y - 1 / y)"
  have mono: "h b < h a"
  proof (rule DERIV_neg_imp_decreasing[OF ab])
    fix x :: real assume ax: "a \<le> x" and xb: "x \<le> b"
    have x0: "0 < x" using a0 ax by linarith
    have xpi: "x < pi" using xb bpi by linarith
    show "\<exists>y. DERIV h x :> y \<and> y < 0"
    proof (rule exI[of _ "inverse (x^2) - inverse ((sin x)^2)"], rule conjI)
      show "DERIV h x :> inverse (x^2) - inverse ((sin x)^2)"
        unfolding h_def by (rule g1_h_deriv[OF x0 xpi])
      show "inverse (x^2) - inverse ((sin x)^2) < 0"
        by (rule g1_hderiv_neg[OF x0 xpi])
    qed
  qed
  have fac: "gsincd x = gsinc x * h x" if x0: "0 < x" and xpi: "x < pi" for x :: real
  proof -
    have sx: "sin x \<noteq> 0" using sin_gt_zero[OF x0 xpi] by simp
    have xne: "x \<noteq> 0" using x0 by simp
    show ?thesis
      using sx xne unfolding gsincd_def gsinc_def h_def
      by (simp add: power2_eq_square divide_simps algebra_simps)
  qed
  have ga: "0 < gsinc a" by (rule g1_gsinc_pos[OF a0 api])
  have gb: "0 < gsinc b" by (rule g1_gsinc_pos[OF b0 bpi])
  have key: "gsincd a * gsinc b - gsinc a * gsincd b = gsinc a * gsinc b * (h a - h b)"
    unfolding fac[OF a0 api] fac[OF b0 bpi] by (simp add: algebra_simps)
  have hpos: "0 < h a - h b" using mono by linarith
  have "0 < gsinc a * gsinc b * (h a - h b)"
    by (rule mult_pos_pos[OF mult_pos_pos[OF ga gb] hpos])
  with key show ?thesis by simp
qed

subsection \<open>\<open>cos \<theta>\<close> stays strictly inside \<open>[-1, 1]\<close> when \<open>sin \<theta> \<noteq> 0\<close>\<close>

lemma g1_cos_lt:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0"
  shows "cos \<theta> < 1" and "- 1 < cos \<theta>"
proof -
  have ne1: "cos \<theta> \<noteq> 1"
  proof
    assume "cos \<theta> = 1"
    hence "(sin \<theta>)^2 = 0" by (simp add: sin_squared_eq)
    hence "sin \<theta> = 0" by (simp add: power2_eq_square)
    with s0 show False by simp
  qed
  have nem1: "cos \<theta> \<noteq> - 1"
  proof
    assume "cos \<theta> = - 1"
    hence "(sin \<theta>)^2 = 0" by (simp add: sin_squared_eq)
    hence "sin \<theta> = 0" by (simp add: power2_eq_square)
    with s0 show False by simp
  qed
  show "cos \<theta> < 1" using cos_le_one[of \<theta>] ne1 by linarith
  show "- 1 < cos \<theta>" using cos_ge_minus_one[of \<theta>] nem1 by linarith
qed

subsection \<open>The explicit derivative of \<open>gdip\<close>\<close>

lemma g1_gdip_has_deriv:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0"
  shows "(gdip has_real_derivative
           pi^2/4 * ((pi/2) * sin \<theta>) *
           (gsincd ((pi/2)*(1 - cos \<theta>)) * gsinc ((pi/2)*(1 + cos \<theta>))
            - gsinc ((pi/2)*(1 - cos \<theta>)) * gsincd ((pi/2)*(1 + cos \<theta>)))) (at \<theta>)"
proof -
  have c1: "cos \<theta> < 1" and c2: "- 1 < cos \<theta>"
    by (rule g1_cos_lt[OF s0])+
  have um0: "(pi/2)*(1 - cos \<theta>) \<noteq> 0"
  proof -
    have "1 - cos \<theta> \<noteq> 0" using c1 by linarith
    thus ?thesis by simp
  qed
  have up0: "(pi/2)*(1 + cos \<theta>) \<noteq> 0"
  proof -
    have "1 + cos \<theta> \<noteq> 0" using c2 by linarith
    thus ?thesis by simp
  qed
  have dm: "((\<lambda>t. (pi/2)*(1 - cos t)) has_real_derivative (pi/2) * sin \<theta>) (at \<theta>)"
    by (auto intro!: derivative_eq_intros)
  have dp: "((\<lambda>t. (pi/2)*(1 + cos t)) has_real_derivative - ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (auto intro!: derivative_eq_intros)
  have cA: "((\<lambda>t. gsinc ((pi/2)*(1 - cos t))) has_real_derivative
              gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF g1_gsinc_has_deriv[OF um0] dm])
  have cB: "((\<lambda>t. gsinc ((pi/2)*(1 + cos t))) has_real_derivative
              gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF g1_gsinc_has_deriv[OF up0] dp])
  have prodd: "((\<lambda>t. gsinc ((pi/2)*(1 - cos t)) * gsinc ((pi/2)*(1 + cos t)))
                 has_real_derivative
                 gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 + cos \<theta>))
                 + gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 - cos \<theta>)))
               (at \<theta>)"
    by (rule DERIV_mult[OF cA cB])
  have cm: "((\<lambda>t. (pi^2/4) * (gsinc ((pi/2)*(1 - cos t)) * gsinc ((pi/2)*(1 + cos t))))
              has_real_derivative
              (pi^2/4) * (gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 + cos \<theta>))
                          + gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 - cos \<theta>))))
            (at \<theta>)"
    by (rule DERIV_cmult[OF prodd])
  have geq: "gdip = (\<lambda>t. (pi^2/4) * (gsinc ((pi/2)*(1 - cos t)) * gsinc ((pi/2)*(1 + cos t))))"
    by (rule ext) (simp add: gdip_def)
  have raw: "(gdip has_real_derivative
               (pi^2/4) * (gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 + cos \<theta>))
                           + gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 - cos \<theta>))))
             (at \<theta>)"
    unfolding geq by (rule cm)
  have alg: "(pi^2/4) * (gsincd ((pi/2)*(1 - cos \<theta>)) * ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 + cos \<theta>))
                         + gsincd ((pi/2)*(1 + cos \<theta>)) * - ((pi/2) * sin \<theta>) * gsinc ((pi/2)*(1 - cos \<theta>)))
           = pi^2/4 * ((pi/2) * sin \<theta>) *
             (gsincd ((pi/2)*(1 - cos \<theta>)) * gsinc ((pi/2)*(1 + cos \<theta>))
              - gsinc ((pi/2)*(1 - cos \<theta>)) * gsincd ((pi/2)*(1 + cos \<theta>)))"
    by (simp add: algebra_simps)
  show ?thesis using raw unfolding alg .
qed

subsection \<open>Evaluating the Fréchet derivative at direction \<open>1\<close>\<close>

lemma g1_frechet_eval:
  fixes f :: "real \<Rightarrow> real" and x D :: real
  assumes der: "(f has_real_derivative D) (at x)"
  shows "frechet_derivative f (at x) 1 = D"
proof -
  have hd: "(f has_derivative (*) D) (at x)"
    using der unfolding has_field_derivative_def .
  have feq: "(*) D = frechet_derivative f (at x)"
    by (rule frechet_derivative_at[OF hd])
  show ?thesis using fun_cong[OF feq, of 1] by simp
qed

subsection \<open>The goal lemma\<close>

lemma gdip_deriv_zero_iff:
  fixes \<theta> :: real
  assumes "sin \<theta> \<noteq> 0"
  shows "frechet_derivative gdip (at \<theta>) 1 = 0 \<longleftrightarrow> cos \<theta> = 0"
proof -
  let ?um = "(pi/2)*(1 - cos \<theta>)"
  let ?up = "(pi/2)*(1 + cos \<theta>)"
  let ?br = "gsincd ?um * gsinc ?up - gsinc ?um * gsincd ?up"
  let ?D = "pi^2/4 * ((pi/2) * sin \<theta>) * ?br"
  have eval: "frechet_derivative gdip (at \<theta>) 1 = ?D"
    by (rule g1_frechet_eval[OF g1_gdip_has_deriv[OF assms]])
  have c1: "cos \<theta> < 1" and c2: "- 1 < cos \<theta>"
    by (rule g1_cos_lt[OF assms])+
  have um_pos: "0 < ?um"
  proof -
    have "0 < 1 - cos \<theta>" using c1 by linarith
    thus ?thesis by (rule mult_pos_pos[OF pi_half_gt_zero])
  qed
  have up_pos: "0 < ?up"
  proof -
    have "0 < 1 + cos \<theta>" using c2 by linarith
    thus ?thesis by (rule mult_pos_pos[OF pi_half_gt_zero])
  qed
  have um_pi: "?um < pi"
  proof -
    have "1 - cos \<theta> < 2" using c2 by linarith
    hence "?um < (pi/2) * 2" by (rule mult_strict_left_mono[OF _ pi_half_gt_zero])
    thus ?thesis by simp
  qed
  have up_pi: "?up < pi"
  proof -
    have "1 + cos \<theta> < 2" using c1 by linarith
    hence "?up < (pi/2) * 2" by (rule mult_strict_left_mono[OF _ pi_half_gt_zero])
    thus ?thesis by simp
  qed
  show ?thesis
  proof
    assume z: "frechet_derivative gdip (at \<theta>) 1 = 0"
    have D0: "?D = 0" using z eval by simp
    show "cos \<theta> = 0"
    proof (rule ccontr)
      assume ne: "cos \<theta> \<noteq> 0"
      have bne: "?br \<noteq> 0"
      proof (cases "0 < cos \<theta>")
        case True
        have diff: "?up - ?um = pi * cos \<theta>" by (simp add: field_simps)
        have "0 < pi * cos \<theta>" by (rule mult_pos_pos[OF pi_gt_zero True])
        hence lt: "?um < ?up" using diff by linarith
        have "0 < ?br" by (rule g1_bracket_pos[OF um_pos lt up_pi])
        thus ?thesis by linarith
      next
        case False
        have neg: "cos \<theta> < 0" using False ne by linarith
        have diff: "?um - ?up = pi * (- cos \<theta>)" by (simp add: field_simps)
        have "0 < - cos \<theta>" using neg by linarith
        hence "0 < pi * (- cos \<theta>)" by (rule mult_pos_pos[OF pi_gt_zero])
        hence lt: "?up < ?um" using diff by linarith
        have rev: "0 < gsincd ?up * gsinc ?um - gsinc ?up * gsincd ?um"
          by (rule g1_bracket_pos[OF up_pos lt um_pi])
        have flip: "?br = - (gsincd ?up * gsinc ?um - gsinc ?up * gsincd ?um)"
          by (simp add: algebra_simps)
        show ?thesis using rev flip by linarith
      qed
      have "?D \<noteq> 0" using assms bne by simp
      with D0 show False by simp
    qed
  next
    assume c0: "cos \<theta> = 0"
    have D0: "?D = 0" using c0 by (simp add: mult.commute)
    show "frechet_derivative gdip (at \<theta>) 1 = 0"
      by (rule trans[OF eval D0])
  qed
qed


text \<open>(G2) Brick R5 of the M6 stratum: the fixed-\<open>\<omega>\<close> steering-singular slices are
  nowhere dense.  CASE \<open>cvec = 0\<close>: the slice is empty because the first component of
  \<open>DM_paper_x\<close> degenerates to \<open>0\<close>, killing surjectivity.  CASE \<open>cvec \<noteq> 0\<close>: criticality
  component 2 forces the moment expression \<open>F\<close> (built from \<open>col\<^sub>2 = Dcvec(e\<^sub>2)\<close>) to vanish,
  and \<open>{F = 0}\<close> is nowhere dense by the analytic-slice engine
  (\<open>lines_entire_slice_nowhere_dense\<close>): \<open>F\<close> is continuous, has entire line restrictions,
  and is not identically zero (one-displaced-element witness).\<close>

section \<open>Generic topology helper\<close>

lemma nowhere_dense_subset:
  fixes A B :: "'a::topological_space set"
  assumes sub: "A \<subseteq> B" and nd: "nowhere_dense B"
  shows "nowhere_dense A"
proof -
  have "interior (closure A) \<subseteq> interior (closure B)"
    by (intro interior_mono closure_mono sub)
  thus ?thesis using nd unfolding nowhere_dense_def by auto
qed

section \<open>Inlined proven helpers (gdip derivative at 0; second steering column)\<close>

lemma frechet_gdip_zero_arg: "frechet_derivative gdip (at \<theta>) 0 = 0" for \<theta> :: real
  using linear_frechet_derivative[OF gdip_differentiable] linear_0 by blast

lemma Dcvec_col2:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) $ 1 = - sin (\<omega>$1) * sin (\<omega>$2)"
    and "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) $ 2 = sin (\<omega>$1) * cos (\<omega>$2)"
  by (simp_all add: Dcvec_dip_def axis_def)

lemma Dcvec_col2_nz:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<noteq> 0"
proof
  assume z: "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) = 0"
  have "- sin (\<omega>$1) * sin (\<omega>$2) = 0" and "sin (\<omega>$1) * cos (\<omega>$2) = 0"
    using z Dcvec_col2[of \<omega>0 \<omega>s \<omega>] by (metis zero_index)+
  hence "sin (\<omega>$2) = 0" and "cos (\<omega>$2) = 0" using pfw by auto
  thus False using sin_cos_squared_add[of "\<omega>$2"] by simp
qed

section \<open>Degenerate steering (\<open>c = 0\<close>): no surjective moment derivative\<close>

lemma DM_paper_x_null_comp1:
  fixes x h :: "(real^2)^'n"
  shows "DM_paper_x x (0::real^2) h $ 1 = 0"
  by (simp add: DM_paper_x_def DA_paper_x_def d_phase_def)

lemma DM_paper_x_null_not_surj:
  fixes x :: "(real^2)^'n"
  shows "\<not> surj (DM_paper_x x (0::real^2))"
proof
  assume s: "surj (DM_paper_x x (0::real^2))"
  have "\<exists>h :: (real^2)^'n. (axis 1 1 :: complex^6) = DM_paper_x x (0::real^2) h"
    using s unfolding surj_def by blast
  then obtain h :: "(real^2)^'n"
    where h: "(axis 1 1 :: complex^6) = DM_paper_x x (0::real^2) h"
    by (elim exE)
  have "(axis 1 1 :: complex^6) $ 1 = 0"
    using h DM_paper_x_null_comp1[of x h] by simp
  moreover have "(axis 1 1 :: complex^6) $ 1 = 1" by (simp add: axis_def)
  ultimately show False by simp
qed

section \<open>The slice function in moment coordinates: continuity\<close>

lemma contA_moment:
  fixes c :: "real^2"
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. A_moment y c)"
  unfolding A_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
        bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma contM1_moment:
  fixes c :: "real^2"
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. M1_moment y c)"
  unfolding M1_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
        bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma contM2_moment:
  fixes c :: "real^2"
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. M2_moment y c)"
  unfolding M2_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
        bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma contF_moments:
  fixes c :: "real^2" and q1 q2 :: complex
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
            * (q1 * M1_moment y c + q2 * M2_moment y c)))"
  by (intro continuous_on_mult continuous_on_const continuous_on_add
        bounded_linear.continuous_on[OF bounded_linear_Re]
        bounded_linear.continuous_on[OF bounded_linear_cnj]
        contA_moment contM1_moment contM2_moment)

section \<open>The slice function in moment coordinates: entire line restrictions\<close>

lemma clA_moment:
  fixes c :: "real^2"
  shows "cline_entire (\<lambda>y::(real^2)^'n. A_moment y c)"
  unfolding A_moment_def phase_def
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  assume "n \<in> (UNIV :: 'n set)"
  have bl: "bounded_linear (\<lambda>y::(real^2)^'n. - (c \<bullet> (y $ n)))"
    by (rule bounded_linear_minus[OF bounded_linear_compose
          [OF bounded_linear_inner_right bounded_linear_vec_nth]])
  show "cline_entire (\<lambda>y::(real^2)^'n. cis (- (c \<bullet> (y $ n))))"
    by (rule cline_entire_cis_linear[OF bl])
qed

lemma clM1_moment:
  fixes c :: "real^2"
  shows "cline_entire (\<lambda>y::(real^2)^'n. M1_moment y c)"
  unfolding M1_moment_def phase_def
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  assume "n \<in> (UNIV :: 'n set)"
  have bl: "bounded_linear (\<lambda>y::(real^2)^'n. - (c \<bullet> (y $ n)))"
    by (rule bounded_linear_minus[OF bounded_linear_compose
          [OF bounded_linear_inner_right bounded_linear_vec_nth]])
  have blc: "bounded_linear (\<lambda>y::(real^2)^'n. (y $ n) $ 1)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  show "cline_entire (\<lambda>y::(real^2)^'n. complex_of_real ((y $ n) $ 1) * cis (- (c \<bullet> (y $ n))))"
    by (rule cline_entire_mult[OF cline_entire_of_real_linear[OF blc]
          cline_entire_cis_linear[OF bl]])
qed

lemma clM2_moment:
  fixes c :: "real^2"
  shows "cline_entire (\<lambda>y::(real^2)^'n. M2_moment y c)"
  unfolding M2_moment_def phase_def
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  assume "n \<in> (UNIV :: 'n set)"
  have bl: "bounded_linear (\<lambda>y::(real^2)^'n. - (c \<bullet> (y $ n)))"
    by (rule bounded_linear_minus[OF bounded_linear_compose
          [OF bounded_linear_inner_right bounded_linear_vec_nth]])
  have blc: "bounded_linear (\<lambda>y::(real^2)^'n. (y $ n) $ 2)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  show "cline_entire (\<lambda>y::(real^2)^'n. complex_of_real ((y $ n) $ 2) * cis (- (c \<bullet> (y $ n))))"
    by (rule cline_entire_mult[OF cline_entire_of_real_linear[OF blc]
          cline_entire_cis_linear[OF bl]])
qed

lemma rlineF_moments:
  fixes c :: "real^2" and q1 q2 :: complex
  shows "rline_entire (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
            * (q1 * M1_moment y c + q2 * M2_moment y c)))"
proof -
  have m1: "cline_entire (\<lambda>y::(real^2)^'n. q1 * M1_moment y c)"
    by (rule cline_entire_mult[OF cline_entire_const clM1_moment])
  have m2: "cline_entire (\<lambda>y::(real^2)^'n. q2 * M2_moment y c)"
    by (rule cline_entire_mult[OF cline_entire_const clM2_moment])
  have z: "cline_entire (\<lambda>y::(real^2)^'n. q1 * M1_moment y c + q2 * M2_moment y c)"
    by (rule cline_entire_add[OF m1 m2])
  have w: "cline_entire (\<lambda>y::(real^2)^'n.
             cnj (A_moment y c) * (q1 * M1_moment y c + q2 * M2_moment y c))"
    by (rule cline_entire_mult[OF cline_entire_cnj[OF clA_moment] z])
  have r: "rline_entire (\<lambda>y::(real^2)^'n.
             Re (cnj (A_moment y c) * (q1 * M1_moment y c + q2 * M2_moment y c)))"
    by (rule rline_entire_Re[OF w])
  show ?thesis by (rule rline_entire_scale[OF r])
qed

section \<open>The slice function is not identically zero\<close>

lemma F_moments_witness:
  fixes c col2 :: "real^2"
  assumes cnz: "c \<noteq> 0" and c2nz: "col2 \<noteq> 0" and c6: "6 \<le> CARD('n)"
  shows "\<exists>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment y c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment y c)) \<noteq> 0"
proof -
  \<comment> \<open>a direction seen by both \<open>c\<close> and \<open>col2\<close>\<close>
  have qex: "\<exists>q::real^2. c \<bullet> q \<noteq> 0 \<and> col2 \<bullet> q \<noteq> 0"
  proof (cases "col2 \<bullet> c = 0")
    case True
    have cc: "c \<bullet> c \<noteq> 0" using cnz by simp
    have c2c2: "col2 \<bullet> col2 \<noteq> 0" using c2nz by simp
    have e1: "c \<bullet> (c + col2) = c \<bullet> c"
      using True by (simp add: inner_add_right inner_commute)
    have e2: "col2 \<bullet> (c + col2) = col2 \<bullet> col2"
      using True by (simp add: inner_add_right)
    show ?thesis
      by (intro exI[of _ "c + col2"] conjI) (simp_all add: e1 e2 cnz c2nz)
  next
    case False
    have cc: "c \<bullet> c \<noteq> 0" using cnz by simp
    have "col2 \<bullet> c \<noteq> 0" using False by simp
    thus ?thesis using cc by (intro exI[of _ c] conjI)
  qed
  then obtain q :: "real^2" where cq: "c \<bullet> q \<noteq> 0" and colq: "col2 \<bullet> q \<noteq> 0"
    by (elim exE conjE)
  \<comment> \<open>the displaced position: phase \<open>\<pi>/2\<close> along \<open>c\<close>, nonzero \<open>col2\<close>-component\<close>
  define p :: "real^2" where "p = ((pi/2)/(c \<bullet> q)) *\<^sub>R q"
  have cp: "c \<bullet> p = pi/2"
    using cq unfolding p_def by (simp add: inner_scaleR_right)
  have Kp: "col2 \<bullet> p \<noteq> 0"
    using cq colq pi_gt_zero unfolding p_def by (auto simp: inner_scaleR_right)
  \<comment> \<open>one-displaced-element configuration\<close>
  define i0 :: 'n where "i0 = undefined"
  define xs :: "(real^2)^'n" where "xs = (\<chi> n. if n = i0 then p else 0)"
  have xsi: "xs $ i0 = p" by (simp add: xs_def)
  have split: "(\<Sum>n\<in>(UNIV::'n set). f n) = f i0 + (\<Sum>n\<in>UNIV - {i0}. f n)"
    for f :: "'n \<Rightarrow> complex"
    by (rule sum.remove) simp_all
  \<comment> \<open>the three moments at the witness\<close>
  have Ast: "A_moment xs c = - \<i> + of_nat (CARD('n) - 1)"
  proof -
    have 1: "A_moment xs c
        = cis (- (c \<bullet> (xs $ i0))) + (\<Sum>n\<in>UNIV - {i0}. cis (- (c \<bullet> (xs $ n))))"
      unfolding A_moment_def phase_def by (rule split)
    have 2: "(\<Sum>n\<in>UNIV - {i0}. cis (- (c \<bullet> (xs $ n)))) = (\<Sum>n\<in>(UNIV::'n set) - {i0}. 1)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    have 3: "(\<Sum>n\<in>(UNIV::'n set) - {i0}. (1::complex)) = of_nat (CARD('n) - 1)"
      by (simp add: card_Diff_singleton)
    show ?thesis using 1 2 3 cp xsi by simp
  qed
  have M1st: "M1_moment xs c = complex_of_real (p $ 1) * (- \<i>)"
  proof -
    have 1: "M1_moment xs c
        = complex_of_real ((xs $ i0) $ 1) * cis (- (c \<bullet> (xs $ i0)))
          + (\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ 1) * cis (- (c \<bullet> (xs $ n))))"
      unfolding M1_moment_def phase_def by (rule split)
    have 2: "(\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ 1) * cis (- (c \<bullet> (xs $ n))))
        = (\<Sum>n\<in>(UNIV::'n set) - {i0}. 0)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    show ?thesis using 1 2 cp xsi by simp
  qed
  have M2st: "M2_moment xs c = complex_of_real (p $ 2) * (- \<i>)"
  proof -
    have 1: "M2_moment xs c
        = complex_of_real ((xs $ i0) $ 2) * cis (- (c \<bullet> (xs $ i0)))
          + (\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ 2) * cis (- (c \<bullet> (xs $ n))))"
      unfolding M2_moment_def phase_def by (rule split)
    have 2: "(\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ 2) * cis (- (c \<bullet> (xs $ n))))
        = (\<Sum>n\<in>(UNIV::'n set) - {i0}. 0)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    show ?thesis using 1 2 cp xsi by simp
  qed
  \<comment> \<open>the value of the slice function at the witness\<close>
  have Fval: "2 * Re (cnj (A_moment xs c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment xs c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment xs c))
      = - (2 * real (CARD('n) - 1) * (col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2))"
    by (simp add: Ast M1st M2st algebra_simps)
  have Kc: "col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2 = col2 \<bullet> p"
    by (simp add: inner_vec_def sum_2)
  have r1: "real (CARD('n) - 1) \<noteq> 0" using c6 by simp
  have nz: "- (2 * real (CARD('n) - 1) * (col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2)) \<noteq> 0"
    unfolding Kc using Kp r1 by simp
  have "2 * Re (cnj (A_moment xs c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment xs c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment xs c)) \<noteq> 0"
    unfolding Fval by (rule nz)
  thus ?thesis by blast
qed

section \<open>The analytic-slice engine applied to \<open>F\<close>\<close>

lemma F_moments_nowhere_dense:
  fixes c col2 :: "real^2"
  assumes cnz: "c \<noteq> 0" and c2nz: "col2 \<noteq> 0" and c6: "6 \<le> CARD('n)"
  shows "nowhere_dense {y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment y c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment y c)) = 0}"
proof -
  define B :: "(real^2)^'n \<Rightarrow> real" where
    "B = (\<lambda>y. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment y c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment y c)))"
  have cont: "continuous_on UNIV B"
    unfolding B_def by (rule contF_moments)
  have rl: "rline_entire B"
    unfolding B_def by (rule rlineF_moments)
  have ntv: "\<exists>y. B y \<noteq> 0"
    unfolding B_def by (rule F_moments_witness[OF cnz c2nz c6])
  have nd: "nowhere_dense {y \<in> (UNIV :: ((real^2)^'n) set). B y = 0}"
  proof (rule lines_entire_slice_nowhere_dense[OF cont _ ntv])
    show "\<And>a v. \<exists>G. G holomorphic_on UNIV
            \<and> (\<forall>t::real. G (complex_of_real t) = complex_of_real (B (a + t *\<^sub>R v)))"
      using rl unfolding rline_entire_def by blast
  qed
  have seq: "{y \<in> (UNIV :: ((real^2)^'n) set). B y = 0} = {y::(real^2)^'n. B y = 0}"
    by auto
  have nd': "nowhere_dense {y::(real^2)^'n. B y = 0}"
    using nd unfolding seq .
  show ?thesis using nd' unfolding B_def .
qed

section \<open>Brick R5: fixed-\<open>\<omega>\<close> slices are nowhere dense\<close>

lemma M6_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "nowhere_dense {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> = 0")
  case True
  have e: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))} = {}"
    using DM_paper_x_null_not_surj by (auto simp: True)
  show ?thesis unfolding e by simp
next
  case False
  define c :: "real^2" where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define col2 :: "real^2" where "col2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  define F :: "(real^2)^'n \<Rightarrow> real" where
    "F = (\<lambda>y. 2 * Re (cnj (M_paper y c $ 1)
       * ((- \<i>) * complex_of_real (col2 $ 1) * (M_paper y c $ 2)
        + (- \<i>) * complex_of_real (col2 $ 2) * (M_paper y c $ 3))))"
  have cnz: "c \<noteq> 0" using False by (simp add: c_def)
  have c2nz: "col2 \<noteq> 0" unfolding col2_def by (rule Dcvec_col2_nz[OF pfw])
  have gnz: "gain_dip \<omega> \<noteq> 0" by (rule gain_dip_nonzero_of_sin[OF pfw])
  have Feq: "F = (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment y c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment y c)))"
    unfolding F_def by simp
  have ndF: "nowhere_dense {y::(real^2)^'n. F y = 0}"
    unfolding Feq by (rule F_moments_nowhere_dense[OF cnz c2nz c6])
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))} \<subseteq> {y::(real^2)^'n. F y = 0}"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    hence g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    have comp2: "gain_dip \<omega> * F x = gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2"
      unfolding F_def c_def col2_def
      using frechet_gdip_zero_arg[of "\<omega>$1"]
      by (simp add: gradU_dip_component_moments axis_def)
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 = 0" using g0 by simp
    hence "gain_dip \<omega> * F x = 0" using comp2 by simp
    hence "F x = 0" using gnz by simp
    thus "x \<in> {y::(real^2)^'n. F y = 0}" by simp
  qed
  show ?thesis by (rule nowhere_dense_subset[OF sub ndF])
qed

lemma cols_dependent_2d:
  fixes u v :: "real^2"
  assumes det0: "u $ 1 * v $ 2 - v $ 1 * u $ 2 = 0" and vnz: "v \<noteq> 0"
  shows "\<exists>t. u = t *\<^sub>R v"
proof (cases "v $ 1 = 0")
  case True
  with vnz have v2: "v $ 2 \<noteq> 0"
    by (metis exhaust_2 Finite_Cartesian_Product.vec_eq_iff zero_index)
  have u1: "u $ 1 = 0" using det0 True v2 by simp
  show ?thesis
  proof (intro exI[of _ "u $ 2 / v $ 2"])
    show "u = (u $ 2 / v $ 2) *\<^sub>R v"
      using u1 True v2
      by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
  qed
next
  case False
  show ?thesis
  proof (intro exI[of _ "u $ 1 / v $ 1"])
    have "u $ 2 = u $ 1 * v $ 2 / v $ 1" using det0 False by (simp add: field_simps)
    thus "u = (u $ 1 / v $ 1) *\<^sub>R v"
      using False by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 field_simps)
  qed
qed


lemma M6_witness_gdip_deriv_zero:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
    and detz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
  shows "frechet_derivative gdip (at (\<omega>$1)) 1 = 0"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define gd where "gd = frechet_derivative gdip (at (\<omega>$1)) 1"
  define aa where "aa = (cmod (M_paper x c $ 1))\<^sup>2"
  define g where "g = gain_dip \<omega>"
  define col1 where "col1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)"
  define col2 where "col2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  define T :: "(real^2) \<Rightarrow> real"
    where "T v = 2 * Re (cnj (M_paper x c $ 1)
       * ((- \<i>) * complex_of_real (v $ 1) * (M_paper x c $ 2)
        + (- \<i>) * complex_of_real (v $ 2) * (M_paper x c $ 3)))" for v
  have gnz: "g \<noteq> 0"
    unfolding g_def using pfw by (rule gain_dip_nonzero_of_sin)
  have aanz: "0 < aa"
  proof -
    have "M_paper x c $ 1 = A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>"
      unfolding c_def by (rule M_paper_proj_A)
    hence "M_paper x c $ 1 \<noteq> 0" using anz by simp
    thus ?thesis unfolding aa_def by simp
  qed
  have g0c: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j = 0" for j
    using g0 by simp
  have e1: "gd * aa + g * T col1 = 0"
  proof -
    have "gd * aa + g * T col1 = gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1"
      unfolding gd_def aa_def g_def col1_def T_def c_def
      by (simp add: gradU_dip_component_moments axis_def)
    thus ?thesis using g0c[of 1] by simp
  qed
  have e2: "g * T col2 = 0"
  proof -
    have "g * T col2 = gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2"
      unfolding g_def col2_def T_def c_def
      using frechet_gdip_zero_arg[of "\<omega>$1"]
      by (simp add: gradU_dip_component_moments axis_def)
    thus ?thesis using g0c[of 2] by simp
  qed
  have Tc2: "T col2 = 0" using e2 gnz by simp
  have c2nz: "col2 \<noteq> 0" unfolding col2_def by (rule Dcvec_col2_nz[OF pfw])
  have det0': "col1 $ 1 * col2 $ 2 - col2 $ 1 * col1 $ 2 = 0"
    using detz unfolding col1_def col2_def by (simp add: det_2 matrix_def)
  obtain t where t: "col1 = t *\<^sub>R col2"
    using cols_dependent_2d[OF det0' c2nz] by blast
  have Tt: "T (t *\<^sub>R col2) = t * T col2"
    unfolding T_def by (simp add: of_real_mult algebra_simps)
  have "gd * aa = 0" using e1 t Tt Tc2 by simp
  with aanz have "gd = 0" by simp
  thus ?thesis unfolding gd_def .
qed


section \<open>The steering determinant formula (copied verbatim from Nonemptiness_Robust3)\<close>

lemma Dcvec_det_eq:
    fixes \<omega>0 \<omega>s \<omega> :: "real^2"
    shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
           = sin (\<omega>$1) * (cos (\<omega>$1)
               - sin (\<omega>$1) * (((kx \<omega>0 - kx
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * cos (\<omega>$2)
                            + ((ky \<omega>0 - ky \<omega>s)/(kz
  \<omega>s - kz \<omega>0)) * sin (\<omega>$2)))"
proof -
  have "cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (cos (\<omega> $h 2) * cos (\<omega> $h 2))) +
           (cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (sin (\<omega> $h 2) * sin (\<omega> $h 2))) +
           ((kx \<omega>0 * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2))) -
             kx \<omega>s * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2)))) /
            (kz \<omega>s - kz \<omega>0) + (kx \<omega>s * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2))) -
             kx \<omega>0 * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2)))) / (kz \<omega>s - kz \<omega>0))) =
       cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (cos (\<omega> $h 2) * cos (\<omega> $h 2) + sin (\<omega> $h 2) * sin (\<omega> $h 2)))"
    by argo
  then show ?thesis
    by (simp add: det_2 matrix_def Dcvec_dip_def axis_def sin_cos_squared_add[of "\<omega>$2"]
  algebra_simps)
qed

section \<open>Finiteness bookkeeping: affine integer lattices meet bounded intervals finitely\<close>

lemma finite_affine_int_zeros:
  fixes c d lo hi :: real
  assumes c0: "0 < c"
  shows "finite {t::real. lo \<le> t \<and> t \<le> hi \<and> (\<exists>i::int. t = of_int i * c + d)}"
proof -
  have sub: "{t::real. lo \<le> t \<and> t \<le> hi \<and> (\<exists>i::int. t = of_int i * c + d)}
               \<subseteq> (\<lambda>i::int. of_int i * c + d) ` {\<lceil>(lo - d) / c\<rceil> .. \<lfloor>(hi - d) / c\<rfloor>}"
  proof
    fix t :: real
    assume "t \<in> {t::real. lo \<le> t \<and> t \<le> hi \<and> (\<exists>i::int. t = of_int i * c + d)}"
    then have h1: "lo \<le> t" and h2: "t \<le> hi"
      and hex: "\<exists>i::int. t = of_int i * c + d" by auto
    obtain i :: int where ti: "t = of_int i * c + d" using hex by (elim exE)
    have b1: "lo - d \<le> of_int i * c" using h1 ti by linarith
    have b2: "of_int i * c \<le> hi - d" using h2 ti by linarith
    have "(lo - d) / c \<le> of_int i"
      using b1 c0 by (simp add: pos_divide_le_eq)
    hence l: "\<lceil>(lo - d) / c\<rceil> \<le> i" by (simp add: ceiling_le_iff)
    have "of_int i \<le> (hi - d) / c"
      using b2 c0 by (simp add: pos_le_divide_eq)
    hence h: "i \<le> \<lfloor>(hi - d) / c\<rfloor>" by (simp add: le_floor_iff)
    show "t \<in> (\<lambda>i::int. of_int i * c + d) ` {\<lceil>(lo - d) / c\<rceil> .. \<lfloor>(hi - d) / c\<rfloor>}"
    proof (rule image_eqI[of _ _ i])
      show "t = of_int i * c + d" by (rule ti)
      show "i \<in> {\<lceil>(lo - d) / c\<rceil> .. \<lfloor>(hi - d) / c\<rfloor>}" using l h by simp
    qed
  qed
  show ?thesis
    by (rule finite_subset[OF sub finite_imageI[OF finite_atLeastAtMost_int]])
qed

lemma finite_cos_zeros_interval:
  fixes lo hi :: real
  shows "finite {t::real. lo \<le> t \<and> t \<le> hi \<and> cos t = 0}"
proof -
  have eq: "{t::real. lo \<le> t \<and> t \<le> hi \<and> cos t = 0}
          = {t::real. lo \<le> t \<and> t \<le> hi \<and> (\<exists>i::int. t = of_int i * pi + pi/2)}"
    by (simp add: cos_zero_iff_int2)
  show ?thesis unfolding eq by (rule finite_affine_int_zeros[OF pi_gt_zero])
qed

lemma finite_phase_zeros_interval:
  fixes a b lo hi :: real
  assumes ab: "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "finite {u::real. lo \<le> u \<and> u \<le> hi \<and> a * cos u + b * sin u = 0}"
proof -
  define R :: real where "R = sqrt (a\<^sup>2 + b\<^sup>2)"
  have pos: "0 < a\<^sup>2 + b\<^sup>2" using ab by (simp add: sum_power2_gt_zero_iff)
  have R0: "0 < R" unfolding R_def by (rule real_sqrt_gt_zero[OF pos])
  have Rne: "R \<noteq> 0" using R0 by simp
  have nn: "0 \<le> a\<^sup>2 + b\<^sup>2" using pos by linarith
  have Rsq: "R\<^sup>2 = a\<^sup>2 + b\<^sup>2" unfolding R_def by (rule real_sqrt_pow2[OF nn])
  have ne: "a\<^sup>2 + b\<^sup>2 \<noteq> 0" using pos by auto
  have unit: "(b/R)\<^sup>2 + (a/R)\<^sup>2 = 1"
  proof -
    have "(b/R)\<^sup>2 + (a/R)\<^sup>2 = (b\<^sup>2 + a\<^sup>2) / R\<^sup>2"
      by (simp add: power_divide add_divide_distrib)
    also have "\<dots> = 1"
      using ne by (simp add: Rsq add.commute)
    finally show ?thesis .
  qed
  obtain \<psi> :: real where psi1: "b/R = cos \<psi>" and psi2: "a/R = sin \<psi>"
    using sincos_total_2pi[OF unit] by blast
  have key: "a * cos u + b * sin u = R * sin (u + \<psi>)" for u :: real
  proof -
    have "a * cos u + b * sin u = R * (sin u * (b/R) + cos u * (a/R))"
      using Rne by (simp add: field_simps)
    also have "\<dots> = R * (sin u * cos \<psi> + cos u * sin \<psi>)"
      unfolding psi1 psi2 by (rule refl)
    also have "\<dots> = R * sin (u + \<psi>)"
      by (simp add: sin_add)
    finally show ?thesis .
  qed
  have eq: "{u::real. lo \<le> u \<and> u \<le> hi \<and> a * cos u + b * sin u = 0}
          = {u::real. lo \<le> u \<and> u \<le> hi \<and> (\<exists>i::int. u = of_int i * pi + (- \<psi>))}"
  proof (rule Set.set_eqI)
    fix u :: real
    have "a * cos u + b * sin u = 0 \<longleftrightarrow> sin (u + \<psi>) = 0"
      using Rne by (simp add: key)
    also have "\<dots> \<longleftrightarrow> (\<exists>i::int. u + \<psi> = of_int i * pi)"
      by (rule sin_zero_iff_int2)
    also have "\<dots> \<longleftrightarrow> (\<exists>i::int. u = of_int i * pi + (- \<psi>))"
    proof
      assume "\<exists>i::int. u + \<psi> = of_int i * pi"
      then obtain i :: int where "u + \<psi> = of_int i * pi" by (elim exE)
      hence "u = of_int i * pi + (- \<psi>)" by linarith
      thus "\<exists>i::int. u = of_int i * pi + (- \<psi>)" by (rule exI)
    next
      assume "\<exists>i::int. u = of_int i * pi + (- \<psi>)"
      then obtain i :: int where "u = of_int i * pi + (- \<psi>)" by (elim exE)
      hence "u + \<psi> = of_int i * pi" by linarith
      thus "\<exists>i::int. u + \<psi> = of_int i * pi" by (rule exI)
    qed
    finally have cc: "a * cos u + b * sin u = 0
                  \<longleftrightarrow> (\<exists>i::int. u = of_int i * pi + (- \<psi>))" .
    show "u \<in> {u::real. lo \<le> u \<and> u \<le> hi \<and> a * cos u + b * sin u = 0}
      \<longleftrightarrow> u \<in> {u::real. lo \<le> u \<and> u \<le> hi \<and> (\<exists>i::int. u = of_int i * pi + (- \<psi>))}"
      using cc by simp
  qed
  show ?thesis unfolding eq by (rule finite_affine_int_zeros[OF pi_gt_zero])
qed

section \<open>OmegaPF component bounds\<close>

lemma OmegaPF_component_bounds:
  fixes ctr \<omega> :: "real^2" and \<delta> :: real
  assumes "\<omega> \<in> OmegaPF ctr \<delta>"
  shows "ctr $ 1 - \<delta> \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> ctr $ 1 + \<delta>
       \<and> ctr $ 2 - pi \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> ctr $ 2 + pi"
proof -
  have mb: "\<forall>i. (ctr - vector [\<delta>, pi]) $ i \<le> \<omega> $ i
              \<and> \<omega> $ i \<le> (ctr + vector [\<delta>, pi]) $ i"
    using assms unfolding OmegaPF_def mem_box_cart by blast
  have m1: "(ctr - vector [\<delta>, pi]) $ 1 \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> (ctr + vector [\<delta>, pi]) $ 1"
    by (rule spec[OF mb])
  have m2: "(ctr - vector [\<delta>, pi]) $ 2 \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> (ctr + vector [\<delta>, pi]) $ 2"
    by (rule spec[OF mb])
  show ?thesis using m1 m2 by simp
qed

section \<open>(M6) ASSEMBLY: the steering-singular stratum is meager\<close>

lemma meager_steering_singular_stratum:
  fixes V :: "((real^2)^'n) set" and ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
proof -
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0
            \<and> Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0}"
  define slice :: "real^2 \<Rightarrow> ((real^2)^'n) set" where
    "slice \<omega> = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}" for \<omega> :: "real^2"
  text \<open>The phase coefficients are not both zero.\<close>
  have D0: "kz \<omega>s - kz \<omega>0 \<noteq> 0" using hsep by simp
  have ABnz: "Ac \<noteq> 0 \<or> Bc \<noteq> 0"
    using kdiff D0 unfolding Ac_def Bc_def by (auto simp: divide_eq_0_iff)
  text \<open>The witness-angle set \<open>K\<close> is finite.\<close>
  define S1 :: "real set" where
    "S1 = {t::real. ctr $ 1 - \<delta> \<le> t \<and> t \<le> ctr $ 1 + \<delta> \<and> cos t = 0}"
  define S2 :: "real set" where
    "S2 = {u::real. ctr $ 2 - pi \<le> u \<and> u \<le> ctr $ 2 + pi
            \<and> Ac * cos u + Bc * sin u = 0}"
  have finS1: "finite S1" unfolding S1_def by (rule finite_cos_zeros_interval)
  have finS2: "finite S2" unfolding S2_def by (rule finite_phase_zeros_interval[OF ABnz])
  have Ksub: "K \<subseteq> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
  proof
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
    have pz: "Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0" using wK by (simp add: K_def)
    have bnds: "ctr $ 1 - \<delta> \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> ctr $ 1 + \<delta>
              \<and> ctr $ 2 - pi \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> ctr $ 2 + pi"
      by (rule OmegaPF_component_bounds[OF wD])
    have mem: "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2"
      using bnds cz pz by (auto simp: S1_def S2_def)
    show "\<omega> \<in> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
    proof (rule image_eqI[where x = "(\<omega> $ 1, \<omega> $ 2)"])
      show "\<omega> = (\<lambda>(t, u). vector [t, u] :: real^2) (\<omega> $ 1, \<omega> $ 2)"
        by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
      show "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2" by (rule mem)
    qed
  qed
  have finK: "finite K"
    by (rule finite_subset[OF Ksub
          finite_imageI[OF finite_cartesian_product[OF finS1 finS2]]])
  text \<open>Witness confinement: every bad witness angle lies in \<open>K\<close>.\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}
             \<subseteq> (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
    then obtain \<omega> :: "real^2" where wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and hz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and sj: "surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      and dz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
      by blast
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    have gd0: "frechet_derivative gdip (at (\<omega> $ 1)) 1 = 0"
      by (rule M6_witness_gdip_deriv_zero[OF s1 g0 anz dz])
    have cz: "cos (\<omega> $ 1) = 0"
      by (rule iffD1[OF gdip_deriv_zero_iff[OF s1] gd0])
    have e: "sin (\<omega> $ 1) * (cos (\<omega> $ 1)
               - sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2))) = 0"
      using dz by (simp add: Dcvec_det_eq Ac_def Bc_def)
    have e2: "cos (\<omega> $ 1) - sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2)) = 0"
      using mult_eq_0_iff[THEN iffD1, OF e] s1 by blast
    have e3: "sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2)) = 0"
      using e2 cz by simp
    have q0: "Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0"
      using mult_eq_0_iff[THEN iffD1, OF e3] s1 by blast
    have wK: "\<omega> \<in> K" using wD cz q0 by (simp add: K_def)
    have xs: "x \<in> slice \<omega>" using g0 anz sj by (simp add: slice_def)
    show "x \<in> (\<Union>\<omega>\<in>K. slice \<omega>)"
    proof (rule UN_I)
      show "\<omega> \<in> K" by (rule wK)
      show "x \<in> slice \<omega>" by (rule xs)
    qed
  qed
  text \<open>Each slice over a fixed angle in \<open>K\<close> is nowhere dense, hence meager;
    the finite union is meager; the bad set is contained in it.\<close>
  have meagU: "meager (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof (rule meager_Union_finite[OF finK])
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    show "meager (slice \<omega>)"
      unfolding slice_def
      by (rule meager_nowhere_dense[OF M6_slice_nowhere_dense[OF c6 s1]])
  qed
  show ?thesis by (rule meager_subset[OF sub meagU])
qed




section \<open>(M5a) The x-partial-regular part is meager\<close>

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
