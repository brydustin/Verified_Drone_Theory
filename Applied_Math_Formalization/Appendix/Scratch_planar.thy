theory Scratch_planar
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>Development scratch for \<open>parametric_transversality_meager_planar_config\<close>:
  transport the proof-complete Euclidean engine to the configuration type
  \<open>(real^2)^'n\<close> via the \<open>\<Phi>/\<Psi>\<close> flattening iso (lifted from the proof of
  \<open>negligible_singular_image_2n\<close> in \<open>Nonemptiness_Paper\<close>).\<close>

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

  \<comment> \<open>Run the proof-complete Euclidean engine at \<open>'m = 'n bit0\<close>.\<close>
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

end
