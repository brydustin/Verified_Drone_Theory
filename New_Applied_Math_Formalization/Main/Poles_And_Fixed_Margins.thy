section \<open>Poles and fixed margins\<close>

theory Poles_And_Fixed_Margins
  imports
    Degenerate_Configurations
begin

text \<open>Two facts behind the form of the final theorems.  The angular box must stay away from the
  poles of the dipole pattern, because there the pattern of every configuration has a degenerate
  critical point.  And the margins must be allowed to depend on the configuration: for fixed
  margins a ball of feasible configurations lies outside the robust set.\<close>

subsection \<open>Poles of the dipole pattern\<close>

lemma gdip_pole:
  fixes \<theta> :: real
  assumes "sin \<theta> = 0"
  shows "gdip \<theta> = 0"
proof -
  have "(cos \<theta>)\<^sup>2 = 1"
    using assms sin_cos_squared_add[of \<theta>] by simp
  then have "cos \<theta> = 1 \<or> cos \<theta> = - 1"
    by (simp add: power2_eq_1_iff)
  then show ?thesis
  proof
    assume c: "cos \<theta> = 1"
    have "gsinc (pi / 2 * (1 + cos \<theta>)) = 0"
      unfolding c by (simp add: gsinc_def)
    then show ?thesis
      by (simp add: gdip_def)
  next
    assume c: "cos \<theta> = - 1"
    have "gsinc (pi / 2 * (1 - cos \<theta>)) = 0"
      unfolding c by (simp add: gsinc_def)
    then show ?thesis
      by (simp add: gdip_def)
  qed
qed

lemma gdip_deriv_pole:
  fixes \<theta> v :: real
  assumes "sin \<theta> = 0"
  shows "frechet_derivative gdip (at \<theta>) v = 0"
proof -
  have d: "(gdip has_derivative frechet_derivative gdip (at \<theta>)) (at \<theta>)"
    using gdip_differentiable[of \<theta>] unfolding frechet_derivative_works .
  have z: "gdip \<theta> = 0"
    by (rule gdip_pole[OF assms])
  have "\<forall>y\<in>UNIV. gdip \<theta> \<le> gdip y"
    unfolding z by (simp add: gdip_eq_edip_sq)
  then have "frechet_derivative gdip (at \<theta>) = (\<lambda>v. 0)"
    by (intro differential_zero_maxmin[OF UNIV_I open_UNIV d] disjI2)
  then show ?thesis
    by simp
qed

text \<open>At a pole the pattern of every configuration has a degenerate critical point.\<close>

lemma pole_degenerate:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes pole: "sin (\<omega> $ 1) = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
proof -
  have g: "gain_dip \<omega> = 0"
    by (simp add: gain_dip_def gdip_pole[OF pole])
  show "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], rule allI)
    fix j :: 2
    show "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j = (0::real^2) $ j"
      unfolding gradU_dip_component_moments by (simp add: g gdip_deriv_pole[OF pole])
  qed
  have row: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ l = 0" for l :: 2
    unfolding HessU_dip_entry_moments
    by (simp add: g gdip_deriv_pole[OF pole] axis_def frechet_gdip_zero_arg)
  have "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
      = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1 * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
        - (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2)\<^sup>2"
    by (rule det_2_symmetric[OF HessU_dip_symmetric])
  also have "\<dots> = 0"
    by (simp add: row HessU_dip_symmetric[of \<omega>0 \<omega>s x \<omega> 1 2])
  finally show "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" .
qed

lemma sigma_min_eq_0_iff: "sigma_min H = 0 \<longleftrightarrow> matrix_det H = 0" for H :: "real^2^2"
  using sigma_min_pos_iff_invertible[of H] sigma_min_nonneg[of H] by linarith

lemma degenerate_not_in_X0:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real" and x :: "planar^'n"
  assumes mem: "\<omega> \<in> \<Omega> - ball ctr \<epsilon>"
    and grad: "gradU cvec g x \<omega> = 0" and det: "matrix_det (HessU cvec g x \<omega>) = 0"
    and xi: "0 < \<xi>"
  shows "x \<notin> X0 cvec g ctr \<Omega> \<xi> \<kappa> \<epsilon>"
proof
  assume "x \<in> X0 cvec g ctr \<Omega> \<xi> \<kappa> \<epsilon>"
  then have "\<xi> \<le> norm (gradU cvec g x \<omega>) + sigma_min (HessU cvec g x \<omega>)"
    using mem unfolding X0_def by blast
  moreover have "sigma_min (HessU cvec g x \<omega>) = 0"
    using det by (simp add: sigma_min_eq_0_iff)
  ultimately show False
    using xi by (simp add: grad)
qed

text \<open>Hence no configuration is robust on an angular domain that contains a pole outside the
  excluded disc.\<close>

lemma X0_empty_of_pole:
  fixes \<Omega> :: "(real^2) set" and \<omega> ctr \<omega>0 \<omega>s :: "real^2"
  assumes mem: "\<omega> \<in> \<Omega> - ball ctr \<epsilon>" and pole: "sin (\<omega> $ 1) = 0" and xi: "0 < \<xi>"
  shows "X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr \<Omega> \<xi> \<kappa> \<epsilon> = ({} :: ((real^2)^'n) set)"
proof -
  have "x \<notin> X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr \<Omega> \<xi> \<kappa> \<epsilon>" for x :: "(real^2)^'n"
    by (rule degenerate_not_in_X0[OF mem pole_degenerate[OF pole] xi])
  then show ?thesis
    by blast
qed

text \<open>The box of half-width \<open>\<pi>/2\<close> in the polar angle around a main beam with
  \<open>\<pi>/2 \<le> \<theta>\<^sub>0 \<le> \<pi>\<close> contains the pole \<open>\<theta> = \<pi>\<close>.\<close>

theorem X0_empty_on_box_with_pole:
  fixes ctr \<omega>0 \<omega>s :: "real^2"
  assumes c1: "pi / 2 \<le> ctr $ 1" and c2: "ctr $ 1 \<le> pi" and xi: "0 < \<xi>" and eps: "\<epsilon> \<le> pi"
  shows "X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr (OmegaPF ctr (pi / 2)) \<xi> \<kappa> \<epsilon> = ({} :: ((real^2)^'n) set)"
proof -
  define \<omega> :: "real^2" where "\<omega> = vector [pi, ctr $ 2 + pi]"
  have w1: "\<omega> $ 1 = pi" and w2: "\<omega> $ 2 = ctr $ 2 + pi"
    by (simp_all add: \<omega>_def)
  have box: "\<omega> \<in> OmegaPF ctr (pi / 2)"
    unfolding OmegaPF_def mem_box_cart
  proof
    fix i :: 2
    show "(ctr - vector [pi / 2, pi]) $ i \<le> \<omega> $ i \<and> \<omega> $ i \<le> (ctr + vector [pi / 2, pi]) $ i"
      using exhaust_2[of i] c1 c2 by (auto simp: w1 w2)
  qed
  have "pi = dist (\<omega> $ 2) (ctr $ 2)"
    by (simp add: w2 dist_real_def)
  also have "\<dots> \<le> dist \<omega> ctr"
    by (rule dist_vec_nth_le)
  finally have "\<omega> \<notin> ball ctr \<epsilon>"
    using eps by (simp add: dist_commute)
  then have mem: "\<omega> \<in> OmegaPF ctr (pi / 2) - ball ctr \<epsilon>"
    using box by blast
  show ?thesis
    by (rule X0_empty_of_pole[OF mem _ xi]) (simp add: w1)
qed

subsection \<open>Fixed margins\<close>

lemma X0_closed:
  fixes \<Omega> :: "(real^2) set" and ctr \<omega>0 \<omega>s :: "real^2"
  shows "closed (X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr \<Omega> \<xi> \<kappa> \<epsilon> :: ((real^2)^'n) set)"
proof -
  have pair: "continuous_on UNIV (\<lambda>x :: (real^2)^'n. (x, \<omega>))" for \<omega> :: "real^2"
    by (intro continuous_intros)
  have cg: "continuous_on UNIV (\<lambda>x :: (real^2)^'n. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)"
    for \<omega> :: "real^2"
    using continuous_on_compose2[OF continuous_on_gradU_dip_joint[of \<omega>0 \<omega>s] pair[of \<omega>]] by simp
  have cH: "continuous_on UNIV (\<lambda>x :: (real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)"
    for \<omega> :: "real^2"
    using continuous_on_compose2[OF continuous_on_HessU_dip_joint[of \<omega>0 \<omega>s] pair[of \<omega>]] by simp
  have cs: "continuous_on UNIV (\<lambda>x :: (real^2)^'n. sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
    for \<omega> :: "real^2"
    using continuous_on_compose2[OF sigma_min_continuous_on[of UNIV] cH[of \<omega>]] by simp
  have k1: "closed {x :: (real^2)^'n. \<kappa> \<le> norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)}"
    for \<omega> :: "real^2"
    by (intro closed_Collect_le continuous_on_const continuous_on_norm cg)
  have k2: "closed {x :: (real^2)^'n. \<xi> \<le> norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
                + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)}" for \<omega> :: "real^2"
    by (intro closed_Collect_le continuous_on_const continuous_on_add continuous_on_norm cg cs)
  have eq: "(X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr \<Omega> \<xi> \<kappa> \<epsilon> :: ((real^2)^'n) set)
      = (\<Inter>\<omega>\<in>sphere ctr \<epsilon>. {x. \<kappa> \<le> norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)})
        \<inter> (\<Inter>\<omega>\<in>\<Omega> - ball ctr \<epsilon>. {x. \<xi> \<le> norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
                + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)})"
    unfolding X0_def Xrobust_def by blast
  show ?thesis
    unfolding eq by (intro closed_Int closed_INT ballI k1 k2)
qed

text \<open>At a null of the array factor of a configuration whose relays lie on a line through the
  origin, the pattern has a degenerate critical point.\<close>

lemma collinear_null_degenerate:
  fixes x :: "(real^2)^'n" and v \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes col: "\<forall>m. \<exists>r. x $ m = r *\<^sub>R v"
    and null: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  have A0: "A_moment x c = 0"
    using null by (simp add: A_cart_eq_A_moment c_def)
  show "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], rule allI)
    fix j :: 2
    show "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j = (0::real^2) $ j"
      unfolding gradU_dip_component_moments c_def[symmetric] by (simp add: A0)
  qed
  obtain r :: "'n \<Rightarrow> real" where r: "\<And>m. x $ m = r m *\<^sub>R v"
    using col by metis
  define S where "S = (\<Sum>n\<in>UNIV. complex_of_real (r n) * cis (- (c \<bullet> (x $ n))))"
  have Mk: "Mcfun x c k = complex_of_real (v $ k) * S" for k :: 2
  proof -
    have t: "complex_of_real ((x $ n) $ k) = complex_of_real (v $ k) * complex_of_real (r n)" for n
      by (subst r[of n]) (simp add: mult.commute)
    show ?thesis
      unfolding Mcfun_def S_def sum_distrib_left
      by (rule sum.cong[OF refl]) (simp only: t mult.assoc)
  qed
  have im0: "Im (cnj (Mcfun x c 1) * Mcfun x c 2) = 0"
    unfolding Mk by (simp add: algebra_simps)
  have "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
      = 4 * (gain_dip \<omega>)\<^sup>2 * (matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
            * Im (cnj (Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 1) * Mcfun x (cvec_dip \<omega>0 \<omega>s \<omega>) 2))\<^sup>2"
    by (rule det_HessU_at_null) (use A0 in \<open>simp add: c_def\<close>)
  also have "\<dots> = 0"
    using im0 by (simp add: c_def)
  finally show "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" .
qed

text \<open>The strictly feasible configuration is of this kind.  So for fixed margins a ball of feasible
  configurations lies outside the robust set, whenever the null direction belongs to the angular
  domain and lies outside the excluded disc.\<close>

theorem feasible_ball_outside_X0:
  fixes dmin \<delta>null pmin A B D \<xi> \<kappa> \<epsilon> :: real and \<omega>null :: "real^2" and \<Omega> :: "(real^2) set"
  assumes N1: "1 < CARD('n)"
    and null_pos: "0 < \<delta>null"
    and power: "pmin < gain_dip design_beam * (real CARD('n))\<^sup>2"
    and null_dir: "cvec_dip design_beam design_source \<omega>null \<noteq> 0"
    and null_in: "\<omega>null \<in> \<Omega> - ball design_beam \<epsilon>"
    and xi: "0 < \<xi>"
  shows "\<exists>R0. \<forall>R\<ge>R0. \<exists>(x::(real^2)^'n) r. 0 < r
          \<and> ball x r \<subseteq> Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
                \<omega>null design_beam \<delta>null pmin
          \<and> ball x r \<inter> X0 (cvec_dip design_beam design_source) gain_dip design_beam \<Omega> \<xi> \<kappa> \<epsilon> = {}"
proof -
  let ?c = "cvec_dip design_beam design_source"
  obtain x :: "(real^2)^'n" and v :: "real^2"
    where afz: "A_cart ?c x \<omega>null = 0" and col: "\<forall>m. \<exists>r. x $ m = r *\<^sub>R v"
      and feas: "\<And>R. norm x + 1 \<le> R \<Longrightarrow> \<exists>\<rho>>0. ball x \<rho> \<subseteq> Ffeas ?c gain_dip
                R dmin A B D \<omega>null design_beam \<delta>null pmin"
    using design_strictly_feasible_collinear[OF N1 null_pos power null_dir, of dmin A B D] by blast
  have "x \<notin> X0 ?c gain_dip design_beam \<Omega> \<xi> \<kappa> \<epsilon>"
    by (rule degenerate_not_in_X0[OF null_in collinear_null_degenerate[OF col afz] xi])
  then have "x \<in> - X0 ?c gain_dip design_beam \<Omega> \<xi> \<kappa> \<epsilon>"
    by simp
  moreover have "open (- X0 ?c gain_dip design_beam \<Omega> \<xi> \<kappa> \<epsilon> :: ((real^2)^'n) set)"
    by (rule open_Compl[OF X0_closed])
  ultimately obtain e where e0: "0 < e"
    and eb: "ball x e \<subseteq> - X0 ?c gain_dip design_beam \<Omega> \<xi> \<kappa> \<epsilon>"
    using open_contains_ball by blast
  show ?thesis
  proof (intro exI[of _ "norm x + 1"] allI impI)
    fix R :: real assume R: "norm x + 1 \<le> R"
    obtain \<rho> where \<rho>0: "0 < \<rho>"
      and \<rho>b: "ball x \<rho> \<subseteq> Ffeas ?c gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin"
      using feas[OF R] by blast
    have "0 < min \<rho> e"
      using \<rho>0 e0 by simp
    moreover have "ball x (min \<rho> e) \<subseteq> Ffeas ?c gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin"
      using \<rho>b subset_ball[of "min \<rho> e" \<rho> x] by auto
    moreover have "ball x (min \<rho> e) \<inter> X0 ?c gain_dip design_beam \<Omega> \<xi> \<kappa> \<epsilon> = {}"
      using eb subset_ball[of "min \<rho> e" e x] by auto
    ultimately show "\<exists>(x::(real^2)^'n) r. 0 < r
          \<and> ball x r \<subseteq> Ffeas ?c gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin
          \<and> ball x r \<inter> X0 ?c gain_dip design_beam \<Omega> \<xi> \<kappa> \<epsilon> = {}"
      by blast
  qed
qed

subsection \<open>The zero set of the wavevector\<close>

text \<open>The hypothesis on the null direction: it is neither vertical nor the main beam.\<close>

lemma design_cvec_eq_0_iff:
  fixes \<omega> :: "real^2"
  assumes t0: "0 \<le> \<omega> $ 1" and t1: "\<omega> $ 1 \<le> pi" and p0: "- pi \<le> \<omega> $ 2" and p1: "\<omega> $ 2 \<le> pi"
  shows "cvec_dip design_beam design_source \<omega> = 0 \<longleftrightarrow> \<omega> $ 1 = 0 \<or> \<omega> = design_beam"
proof -
  define \<theta> where "\<theta> = \<omega> $ 1"
  define \<phi> where "\<phi> = \<omega> $ 2"
  have c0: "cvec_dip design_beam design_source \<omega> = 0
        \<longleftrightarrow> sin \<theta> * cos \<phi> + cos \<theta> - 1 = 0 \<and> sin \<theta> * sin \<phi> = 0"
    unfolding Finite_Cartesian_Product.vec_eq_iff forall_2 by (simp add: design_cvec \<theta>_def \<phi>_def)
  have wb: "\<omega> = design_beam \<longleftrightarrow> \<theta> = pi / 2 \<and> \<phi> = 0"
    unfolding Finite_Cartesian_Product.vec_eq_iff forall_2 by (simp add: design_beam_def \<theta>_def \<phi>_def)
  have "sin \<theta> * cos \<phi> + cos \<theta> - 1 = 0 \<and> sin \<theta> * sin \<phi> = 0 \<longleftrightarrow> \<theta> = 0 \<or> (\<theta> = pi / 2 \<and> \<phi> = 0)"
  proof
    assume "sin \<theta> * cos \<phi> + cos \<theta> - 1 = 0 \<and> sin \<theta> * sin \<phi> = 0"
    then have e1: "sin \<theta> * cos \<phi> + cos \<theta> - 1 = 0" and e2: "sin \<theta> * sin \<phi> = 0"
      by simp_all
    show "\<theta> = 0 \<or> (\<theta> = pi / 2 \<and> \<phi> = 0)"
    proof (cases "sin \<theta> = 0")
      case True
      have "\<theta> = 0 \<or> \<theta> = pi"
      proof (rule ccontr)
        assume "\<not> (\<theta> = 0 \<or> \<theta> = pi)"
        then have "0 < \<theta>" and "\<theta> < pi"
          using t0 t1 by (auto simp: \<theta>_def)
        then have "0 < sin \<theta>"
          by (rule sin_gt_zero)
        with True show False
          by simp
      qed
      moreover have "\<theta> \<noteq> pi"
      proof
        assume "\<theta> = pi"
        with e1 show False
          by simp
      qed
      ultimately show ?thesis
        by simp
    next
      case False
      then have sp: "sin \<phi> = 0"
        using e2 by simp
      have "(cos \<phi>)\<^sup>2 = 1"
        using sp sin_cos_squared_add[of \<phi>] by simp
      then have "cos \<phi> = 1 \<or> cos \<phi> = - 1"
        by (simp add: power2_eq_1_iff)
      then show ?thesis
      proof
        assume cp: "cos \<phi> = 1"
        have s: "sin \<theta> + cos \<theta> = 1"
          using e1 cp by simp
        have "(sin \<theta> + cos \<theta>)\<^sup>2 = (sin \<theta>)\<^sup>2 + (cos \<theta>)\<^sup>2 + 2 * sin \<theta> * cos \<theta>"
          by (rule power2_sum)
        then have "2 * sin \<theta> * cos \<theta> = 0"
          using sin_cos_squared_add[of \<theta>] s by simp
        then have ct: "cos \<theta> = 0"
          using False by simp
        have th: "\<theta> = pi / 2"
          by (rule cos_inj_pi[where y = "pi / 2"]) (use ct t0 t1 in \<open>simp_all add: \<theta>_def\<close>)
        have "cos \<bar>\<phi>\<bar> = cos 0"
          using cp by simp
        then have "\<bar>\<phi>\<bar> = 0"
          by (rule cos_inj_pi[rotated 4]) (use p0 p1 in \<open>auto simp: \<phi>_def\<close>)
        then show ?thesis
          using th by simp
      next
        assume cp: "cos \<phi> = - 1"
        have s: "cos \<theta> = 1 + sin \<theta>"
          using e1 cp by simp
        have "(1 + sin \<theta>)\<^sup>2 = 1 + (sin \<theta>)\<^sup>2 + 2 * sin \<theta>"
          using power2_sum[of 1 "sin \<theta>"] by simp
        moreover have "(cos \<theta>)\<^sup>2 = (1 + sin \<theta>)\<^sup>2"
          using s by simp
        ultimately have "(sin \<theta>)\<^sup>2 + sin \<theta> = 0"
          using sin_cos_squared_add[of \<theta>] by linarith
        then have "sin \<theta> * (sin \<theta> + 1) = 0"
          by (simp add: power2_eq_square algebra_simps)
        then have "sin \<theta> = - 1"
          using False by simp
        moreover have "0 \<le> sin \<theta>"
          by (rule sin_ge_zero) (use t0 t1 in \<open>simp_all add: \<theta>_def\<close>)
        ultimately show ?thesis
          by simp
      qed
    qed
  next
    assume "\<theta> = 0 \<or> (\<theta> = pi / 2 \<and> \<phi> = 0)"
    then show "sin \<theta> * cos \<phi> + cos \<theta> - 1 = 0 \<and> sin \<theta> * sin \<phi> = 0"
    proof
      assume "\<theta> = 0"
      then show ?thesis
        by simp
    next
      assume "\<theta> = pi / 2 \<and> \<phi> = 0"
      then have th: "\<theta> = pi / 2" and ph: "\<phi> = 0"
        by simp_all
      show ?thesis
        unfolding th ph by simp
    qed
  qed
  then show ?thesis
    unfolding c0 wb by (simp add: \<theta>_def)
qed

end
