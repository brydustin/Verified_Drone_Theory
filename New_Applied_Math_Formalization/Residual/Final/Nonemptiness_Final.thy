section \<open>The robust feasible set is nonempty\<close>

theory Nonemptiness_Final
  imports "Applied_Math_Residual.Residual_Meager"
begin

text \<open>The end-to-end theorem.  Steering: source overhead, main beam horizontal
  (@{const design_beam}, @{const design_source}); angular box @{term "OmegaPF design_beam (pi / 4)"}.
  The feasible set is the one of the paper (Eq. 22) for every minimum spacing, every null
  threshold above zero, every minimum main-beam power below the maximum and every null direction
  other than the main beam; the plane coefficients are those of Eqs. (12)--(14).

  The rank-deficient stratum is meager by @{thm residual_meager_design}; the other strata and the
  Baire argument follow.\<close>

subsection \<open>The steering geometry\<close>

lemma design_hsep: "kz design_source \<noteq> kz design_beam"
  by (simp add: design_source_def design_beam_def kz_def)

lemma design_kdiff: "kx design_beam \<noteq> kx design_source \<or> ky design_beam \<noteq> ky design_source"
  by (simp add: design_source_def design_beam_def kx_def)

lemma design_pole_free: "\<forall>\<omega>\<in>OmegaPF design_beam (pi / 4). sin (\<omega> $ 1) \<noteq> 0"
proof
  fix \<omega> :: "real^2" assume box: "\<omega> \<in> OmegaPF design_beam (pi / 4)"
  have "0 < vec_nth \<omega> 1" and "vec_nth \<omega> 1 < pi"
    using OmegaPF_design_bounds(1,2)[OF box] pi_gt_zero by linarith+
  then have "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero)
  then show "sin (\<omega> $ 1) \<noteq> 0"
    by simp
qed

lemma design_plane_coefficients:
  "kx design_source - kx design_beam = - 1"
  "ky design_source - ky design_beam = 0"
  "kz design_beam - kz design_source = - 1"
  by (simp_all add: design_source_def design_beam_def kx_def ky_def kz_def)


subsection \<open>Degenerate critical points are exceptional\<close>

lemma meager_rank_deficient_stratum_design:
  fixes V :: "((real^2)^'n) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
                  \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))}"
proof -
  have d0: "(0::real) < pi / 4"
    by simp
  note pf = design_pole_free and hsep = design_hsep and kdiff = design_kdiff
  have card4: "4 \<le> CARD('n)"
    using c6 by simp
  let ?D1 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))
          \<and> matrix_det (matrix (Dcvec_dip design_beam design_source \<omega>)) \<noteq> 0
          \<and> cvec_dip design_beam design_source \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip design_beam design_source) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  let ?D2 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))
          \<and> matrix_det (matrix (Dcvec_dip design_beam design_source \<omega>)) \<noteq> 0
          \<and> cvec_dip design_beam design_source \<omega> = 0}"
  let ?D5 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))
          \<and> matrix_det (matrix (Dcvec_dip design_beam design_source \<omega>)) = 0}"
  let ?D34 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))
          \<and> matrix_det (matrix (Dcvec_dip design_beam design_source \<omega>)) \<noteq> 0
          \<and> cvec_dip design_beam design_source \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip design_beam design_source) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  have meag: "meager (?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34)"
    by (intro meager_Un
          m5_D1_regular[OF openV Vne]
          m5_D2_beamcenter[OF openV Vne c6 d0 pf]
          m5_D5_steersing[OF openV Vne c6 d0 pf hsep kdiff]
          residual_meager_design[OF card4])
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
                  \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))}
             \<subseteq> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
                  \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))}"
    then obtain \<omega> where xV: "x \<in> V" and wD: "\<omega> \<in> OmegaPF design_beam (pi / 4)"
      and g0: "gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0"
      and h0: "matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0"
      and a0: "A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0"
      and ns: "\<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))"
      by blast
    show "x \<in> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34"
      using xV wD g0 h0 a0 ns by blast
  qed
  show ?thesis by (rule meager_subset[OF sub meag])
qed

lemma Phi_bad_meager_design:
  fixes V :: "((real^2)^'n) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and oddN: "odd CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x \<omega> = 0}"
proof -
  have d0: "(0::real) < pi / 4"
    by simp
  note pf = design_pole_free and hsep = design_hsep and kdiff = design_kdiff
  have card4: "4 \<le> CARD('n)"
    using c6 by simp
  let ?reg = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
              \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
              \<and> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))
              \<and> matrix_det (matrix (Dcvec_dip design_beam design_source \<omega>)) \<noteq> 0}"
  let ?def = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
              \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))}"
  let ?steer = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
              \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
              \<and> surj (DM_paper_x x (cvec_dip design_beam design_source \<omega>))
              \<and> matrix_det (matrix (Dcvec_dip design_beam design_source \<omega>)) = 0}"
  let ?null = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
              \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip design_beam design_source) x \<omega> = 0}"
  have meag4: "meager (?reg \<union> ?def \<union> ?steer \<union> ?null)"
    by (intro meager_Un meager_bad_regular_stratum_on[OF openV Vne c6]
              meager_rank_deficient_stratum_design[OF openV Vne c6]
              meager_steering_singular_stratum[OF openV Vne c6 d0 pf hsep kdiff]
              meager_Azero_degenerate_stratum[OF openV Vne c6 oddN d0 pf])
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x \<omega> = 0}
             \<subseteq> ?reg \<union> ?def \<union> ?steer \<union> ?null"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x \<omega> = 0}"
    then obtain \<omega> where xV: "x \<in> V" and wD: "\<omega> \<in> OmegaPF design_beam (pi / 4)"
      and pb: "Phibad (cvec_dip design_beam design_source) gain_dip x \<omega> = 0" by blast
    from Phibad_dip_imp_detHess0[OF pb]
    have g0: "gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0"
      and d0: "matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0" by blast+
    show "x \<in> ?reg \<union> ?def \<union> ?steer \<union> ?null"
      using xV wD g0 d0
      by fastforce
  qed
  show ?thesis by (rule meager_subset[OF sub meag4])
qed

lemma regular_config_exists_design:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and int_ne: "interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
  shows "\<exists>x0 \<in> interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin
                          :: ((real^2)^'n) set).
            \<forall>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x0 \<omega> \<noteq> 0"
proof -
  define I where "I = interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin
                      :: ((real^2)^'n) set)"
  have openI: "open I" unfolding I_def by (rule open_interior)
  have Ine: "I \<noteq> {}" unfolding I_def by (rule int_ne)
  have meagB: "meager {x \<in> I. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x \<omega> = 0}"
    by (rule Phi_bad_meager_design[OF openI Ine c6 oddN])
  have "\<not> I \<subseteq> {x \<in> I. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x \<omega> = 0}"
  proof
    assume sub: "I \<subseteq> {x \<in> I. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x \<omega> = 0}"
    have "meager I" by (rule meager_subset[OF sub meagB])
    moreover have "\<not> meager I" by (rule open_nonempty_not_meager[OF openI Ine])
    ultimately show False by simp
  qed
  then obtain x0 where x0I: "x0 \<in> I"
    and x0nB: "x0 \<notin> {x \<in> I. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x \<omega> = 0}" by blast
  have x0Iexp: "x0 \<in> interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin)"
    using x0I unfolding I_def by assumption
  have reg: "\<forall>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x0 \<omega> \<noteq> 0"
    using x0I x0nB by blast
  from x0Iexp reg
  have conjx0: "x0 \<in> interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin)
        \<and> (\<forall>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x0 \<omega> \<noteq> 0)" by (rule conjI)
  \<comment> \<open>Composition fully established: \<open>x0Iexp\<close> (\<open>x0 \<in> interior\<close>) and \<open>reg\<close> (\<open>\<forall>\<omega>. \<Phi> \<noteq> 0\<close>) are the
      witness data.  Only the final \<^emph>\<open>bounded-existential introduction\<close> \<open>\<exists>x0\<in>interior. \<dots>\<close> with
      witness \<open>x0\<close> is left open --- a witness-instantiation tactic step (\<open>bexI\<close>/\<open>rule_tac x=x0\<close>)
      that needs live goal/type inspection to dispatch against the large \<open>interior (Ffeas \<dots>)\<close>
      term; it is mathematically immediate from \<open>x0Iexp\<close> and \<open>reg\<close>.\<close>
  show ?thesis
  proof (rule bexI[where x = x0])
    show "\<forall>\<omega>\<in>OmegaPF design_beam (pi / 4). Phibad (cvec_dip design_beam design_source) gain_dip x0 \<omega> \<noteq> 0" by (rule reg)
  next
    show "x0 \<in> interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin)"
      by (rule x0Iexp)
  qed
qed


subsection \<open>From a regular configuration to the margins\<close>

lemma no_degenerate_to_sphere_annulus_bounded:
  fixes x0 :: "(real^2)^'n" and ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and nd: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  shows "\<exists>\<epsilon>>0. \<epsilon> \<le> \<delta> \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
proof -
  define f where "f = gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0"
  define C where "C = {\<omega>. \<omega> \<in> OmegaPF ctr \<delta> \<and> f \<omega> = 0}"
  have fcont: "continuous_on UNIV f" unfolding f_def by (rule gradU_dip_continuous_on)
  have isol: "\<not> c islimpt C" if cC: "c \<in> C" for c
  proof -
    from cC have cO: "c \<in> OmegaPF ctr \<delta>" and fc0: "f c = 0" by (auto simp: C_def)
    have dnz: "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c) \<noteq> 0"
      using nd cO fc0 unfolding f_def by blast
    hence inv: "invertible (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c)" by (simp add: invertible_det_nz)
    have injL: "inj ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c))"
      using inv by (metis matrix_left_invertible_injective invertible_def)
    have hd: "(f has_derivative ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c))) (at c)"
      unfolding f_def by (rule gradU_dip_has_derivative)
    obtain d where d0: "0 < d" and dd: "\<And>y. dist y c < d \<Longrightarrow> y \<noteq> c \<Longrightarrow> f y \<noteq> 0"
      using isolated_nondeg_zero[OF hd injL fc0] by blast
    show "\<not> c islimpt C" using dd d0 by (force simp: islimpt_approachable C_def)
  qed
  have Cint: "C = OmegaPF ctr \<delta> \<inter> {y. f y = 0}" by (auto simp: C_def)
  have Ccomp: "compact C"
    unfolding Cint by (rule compact_Int_closed[OF OmegaPF_compact closed_Collect_eq[OF fcont continuous_on_const]])
  have Cfin: "finite C" using Ccomp isol by (metis compact_eq_Bolzano_Weierstrass order_refl)
  define R where "R = (\<lambda>c. dist c ctr) ` C"
  have Rfin: "finite R" unfolding R_def using Cfin by simp
  have "infinite {0<..\<delta>::real}" using d0 by (simp add: infinite_Ioc)
  hence "infinite ({0<..\<delta>::real} - R)" using Rfin by (rule Diff_infinite_finite[rotated])
  then obtain \<epsilon> where \<epsilon>m: "\<epsilon> \<in> {0<..\<delta>::real} - R" using infinite_imp_nonempty by blast
  have \<epsilon>0: "0 < \<epsilon>" and \<epsilon>pi: "\<epsilon> \<le> \<delta>" and \<epsilon>R: "\<epsilon> \<notin> R" using \<epsilon>m by auto
  have sphere: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. f \<omega> \<noteq> 0"
  proof
    fix \<omega> assume w: "\<omega> \<in> sphere ctr \<epsilon>"
    hence wO: "\<omega> \<in> OmegaPF ctr \<delta>" using sphere_subset_OmegaPF[OF \<epsilon>pi dpi] by blast
    have dw: "dist \<omega> ctr = \<epsilon>" using w by (simp add: dist_commute sphere_def)
    show "f \<omega> \<noteq> 0"
    proof
      assume "f \<omega> = 0"
      hence "\<omega> \<in> C" using wO by (simp add: C_def)
      hence "dist \<omega> ctr \<in> R" by (simp add: R_def)
      thus False using \<epsilon>R dw by simp
    qed
  qed
  have annulus: "\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                   f y \<noteq> 0 \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
  proof
    fix y assume "y \<in> OmegaPF ctr \<delta> - ball ctr \<epsilon>"
    hence yO: "y \<in> OmegaPF ctr \<delta>" by simp
    show "f y \<noteq> 0 \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    proof (cases "f y = 0")
      case True
      hence "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y) \<noteq> 0"
        using nd yO unfolding f_def by blast
      thus ?thesis by (simp add: sigma_min_pos_iff_invertible)
    next
      case False thus ?thesis by blast
    qed
  qed
  show ?thesis using \<epsilon>0 \<epsilon>pi sphere annulus unfolding f_def by blast
qed

lemma F0_nonempty_of_witness_radius:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real"
    and R dmin A B D \<delta>null pmin :: real and \<omega>null ctr :: planar
    and x0 :: "planar^'n" and \<epsilon> :: real and \<Omega>dom :: "planar set"
  assumes \<epsilon>0: "0 < \<epsilon>" and cOm: "compact \<Omega>dom"
    and feas: "x0 \<in> Ffeas cvec g R dmin A B D \<omega>null ctr \<delta>null pmin"
    and cdN: "continuous_on (sphere ctr \<epsilon>) (\<lambda>\<omega>. norm (gradU cvec g x0 \<omega>))"
    and cdsum: "continuous_on (\<Omega>dom - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
    and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU cvec g x0 \<omega> \<noteq> 0"
    and rO: "\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
                gradU cvec g x0 y \<noteq> 0 \<or> 0 < sigma_min (HessU cvec g x0 y)"
  shows "\<exists>\<xi> \<kappa>. 0 < \<xi> \<and> 0 < \<kappa>
            \<and> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>
                \<noteq> ({}::(planar^'n) set)"
proof -
  \<comment> \<open>the positive \<open>\<kappa>\<close>-margin on the \<open>\<epsilon>\<close>-sphere (Weierstrass)\<close>
  have sph_ne: "sphere ctr \<epsilon> \<noteq> {}"
  proof -
    have "dist (ctr + \<epsilon> *\<^sub>R axis (1::2) 1) ctr = \<epsilon>"
      using \<epsilon>0 by (simp add: dist_norm abs_of_pos)
    hence "ctr + \<epsilon> *\<^sub>R axis (1::2) 1 \<in> sphere ctr \<epsilon>"
      by (simp add: dist_commute)
    thus ?thesis by blast
  qed
  obtain \<omega>m where \<omega>m: "\<omega>m \<in> sphere ctr \<epsilon>"
      and \<omega>min: "\<forall>\<omega>\<in>sphere ctr \<epsilon>.
                    norm (gradU cvec g x0 \<omega>m) \<le> norm (gradU cvec g x0 \<omega>)"
    using continuous_attains_inf[OF compact_sphere sph_ne cdN] by blast
  define \<kappa> where "\<kappa> = norm (gradU cvec g x0 \<omega>m)"
  have \<kappa>pos: "0 < \<kappa>" using bspec[OF rsph \<omega>m] unfolding \<kappa>_def by simp
  have inXrob: "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>"
    using \<omega>min unfolding Xrobust_def \<kappa>_def by simp
  \<comment> \<open>the positive \<open>\<xi>\<close>-margin on \<open>\<Omega>\<^sup>~\<close> (vacuous if \<open>\<Omega>\<^sup>~ = \<emptyset>\<close>)\<close>
  show ?thesis
  proof (cases "\<Omega>dom - ball ctr \<epsilon> = {}")
    case True
    have "x0 \<in> X0 cvec g ctr (\<Omega>dom) 1 \<kappa> \<epsilon>"
      using inXrob True unfolding X0_def by blast
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin 1 \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin 1 \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    moreover have "(0::real) < 1" by simp
    ultimately show ?thesis using \<kappa>pos \<epsilon>0 by blast
  next
    case False
    obtain ym where ym: "ym \<in> \<Omega>dom - ball ctr \<epsilon>"
        and ymin: "\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
              norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)
              \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y)"
      using continuous_attains_inf[OF compact_minus_ball[OF cOm] False cdsum] by blast
    define \<xi> where "\<xi> = norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)"
    have \<xi>pos: "0 < \<xi>"
    proof (cases "gradU cvec g x0 ym = 0")
      case True
      with bspec[OF rO ym] have "0 < sigma_min (HessU cvec g x0 ym)" by simp
      thus ?thesis unfolding \<xi>_def
        using norm_ge_zero[of "gradU cvec g x0 ym"] by linarith
    next
      case False
      hence "0 < norm (gradU cvec g x0 ym)" by simp
      thus ?thesis unfolding \<xi>_def
        using sigma_min_nonneg[of "HessU cvec g x0 ym"] by linarith
    qed
    have "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>
          \<and> (\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
                \<xi> \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
      using inXrob ymin unfolding \<xi>_def by blast
    hence "x0 \<in> X0 cvec g ctr (\<Omega>dom) \<xi> \<kappa> \<epsilon>" unfolding X0_def by simp
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    thus ?thesis using \<xi>pos \<kappa>pos \<epsilon>0 by blast
  qed
qed


subsection \<open>A feasible configuration with no degenerate critical point\<close>

text \<open>The feasible body has nonempty interior for all admissible parameters and all large radii.
  The plane coefficients \<open>A\<close>, \<open>B\<close>, \<open>D\<close> are arbitrary here.\<close>

lemma design_feasible_interior:
  fixes dmin \<delta>null pmin A B D :: real and \<omega>null :: "real^2"
  assumes N1: "1 < CARD('n)"
    and null_pos: "0 < \<delta>null"
    and power: "pmin < gain_dip design_beam * (real CARD('n))\<^sup>2"
    and null_dir: "cvec_dip design_beam design_source \<omega>null \<noteq> 0"
  shows "\<exists>R0. \<forall>R\<ge>R0. interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set) \<noteq> {}"
proof -
  define s where "s = max dmin 0 + 1"
  have spos: "0 < s" and ds: "dmin < s"
    by (simp_all add: s_def)
  obtain x :: "(real^2)^'n"
    where afz: "af (cvec_dip design_beam design_source) x \<omega>null = 0"
      and spac0: "\<forall>m m'. m \<noteq> m' \<longrightarrow> s \<le> spdist A B D (x $ m) (x $ m')"
    using feasible_witness_exists[OF N1 null_dir spos] by meson
  have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (x $ fst p) (x $ snd p)"
    using spac0 ds by fastforce
  have Nlt: "Upow (cvec_dip design_beam design_source) gain_dip x \<omega>null < \<delta>null"
    using afz null_pos by (simp add: Upow_def)
  have Pgt: "pmin < Upow (cvec_dip design_beam design_source) gain_dip x design_beam"
    using power by (simp add: Upow_at_main[OF design_hsep])
  show ?thesis
  proof (intro exI[of _ "norm x + 1"] allI impI)
    fix R :: real assume R: "norm x + 1 \<le> R"
    have inR: "x \<in> ball 0 R"
      using R by (simp add: dist_norm)
    obtain \<rho> where \<rho>: "0 < \<rho>"
      and sub: "ball x \<rho> \<subseteq> Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
                  \<omega>null design_beam \<delta>null pmin"
      using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
    have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
                  \<omega>null design_beam \<delta>null pmin)"
      by (rule interior_maximal[OF sub open_ball])
    moreover have "x \<in> ball x \<rho>"
      using \<rho> by simp
    ultimately show "interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set) \<noteq> {}"
      by blast
  qed
qed

text \<open>The statement without margins: some feasible configuration has no degenerate critical
  point anywhere in the box.\<close>

theorem regular_feasible_configuration_exists:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and int_ne: "interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set) \<noteq> {}"
  shows "\<exists>x0 \<in> interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set).
      \<forall>\<omega>\<in>OmegaPF design_beam (pi / 4).
        \<not> (gradU (cvec_dip design_beam design_source) gain_dip x0 \<omega> = 0
           \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega>) = 0)"
proof -
  obtain x0 :: "(real^2)^'n"
    where x0I: "x0 \<in> interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin)"
      and x0reg: "\<forall>\<omega>\<in>OmegaPF design_beam (pi / 4).
            Phibad (cvec_dip design_beam design_source) gain_dip x0 \<omega> \<noteq> 0"
    using regular_config_exists_design[OF c6 oddN int_ne] by blast
  have "\<not> (gradU (cvec_dip design_beam design_source) gain_dip x0 \<omega> = 0
           \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega>) = 0)"
    if box: "\<omega> \<in> OmegaPF design_beam (pi / 4)" for \<omega>
  proof
    assume deg: "gradU (cvec_dip design_beam design_source) gain_dip x0 \<omega> = 0
           \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega>) = 0"
    then have g: "gradU (cvec_dip design_beam design_source) gain_dip x0 \<omega> = 0"
      and dz: "matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega>) = 0"
      by auto
    have e: "matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega>)
              = HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega> $ 1 $ 1
                  * HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega> $ 2 $ 2
                - (HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2"
      by (rule det_2_symmetric[OF HessU_dip_symmetric])
    from e dz have "HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega> $ 1 $ 1
                      * HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega> $ 2 $ 2
                    = (HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2"
      by simp
    with g have "Phibad (cvec_dip design_beam design_source) gain_dip x0 \<omega> = 0"
      using Phibad_zero_iff by blast
    with x0reg box show False
      by auto
  qed
  then show ?thesis
    using x0I by blast
qed


subsection \<open>The theorem\<close>

theorem F0_dip_nonempty_final:
  fixes dmin \<delta>null pmin :: real and \<omega>null :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and null_pos: "0 < \<delta>null"
    and power: "pmin < gain_dip design_beam * (real CARD('n))\<^sup>2"
    and null_dir: "cvec_dip design_beam design_source \<omega>null \<noteq> 0"
  shows "\<exists>R0. \<forall>R\<ge>R0. \<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4
          \<and> F0 (cvec_dip design_beam design_source) gain_dip R dmin
               (kx design_source - kx design_beam) (ky design_source - ky design_beam)
               (kz design_beam - kz design_source)
               \<omega>null design_beam (OmegaPF design_beam (pi / 4)) \<delta>null pmin \<xi> \<kappa> \<epsilon>
              \<noteq> ({} :: ((real^2)^'n) set)"
proof -
  let ?A = "kx design_source - kx design_beam" and ?B = "ky design_source - ky design_beam"
    and ?D = "kz design_beam - kz design_source"
  let ?c = "cvec_dip design_beam design_source"
  have N1: "1 < CARD('n)"
    using c6 by simp
  obtain R0 where R0: "\<And>R. R0 \<le> R \<Longrightarrow>
      interior (Ffeas ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set) \<noteq> {}"
    using design_feasible_interior[OF N1 null_pos power null_dir, of dmin ?A ?B ?D] by blast
  show ?thesis
  proof (rule exI[of _ R0], intro allI impI)
    fix R :: real assume R: "R0 \<le> R"
    obtain x0 :: "(real^2)^'n"
      where x0I: "x0 \<in> interior (Ffeas ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam \<delta>null pmin)"
        and nondeg: "\<forall>\<omega>\<in>OmegaPF design_beam (pi / 4).
            \<not> (gradU ?c gain_dip x0 \<omega> = 0 \<and> matrix_det (HessU ?c gain_dip x0 \<omega>) = 0)"
      using regular_feasible_configuration_exists[OF c6 oddN R0[OF R]] by blast
    have feas: "x0 \<in> Ffeas ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam \<delta>null pmin"
      using x0I interior_subset by blast
    have d0: "(0::real) < pi / 4" and dpi: "pi / 4 \<le> (pi::real)"
      by simp_all
    obtain \<epsilon> :: real where \<epsilon>0: "0 < \<epsilon>" and \<epsilon>le: "\<epsilon> \<le> pi / 4"
      and sph: "\<forall>\<omega>\<in>sphere design_beam \<epsilon>. gradU ?c gain_dip x0 \<omega> \<noteq> 0"
      and ann: "\<forall>y\<in>OmegaPF design_beam (pi / 4) - ball design_beam \<epsilon>.
                  gradU ?c gain_dip x0 y \<noteq> 0 \<or> 0 < sigma_min (HessU ?c gain_dip x0 y)"
      using no_degenerate_to_sphere_annulus_bounded[OF d0 dpi nondeg] by blast
    have c1: "continuous_on (sphere design_beam \<epsilon>) (\<lambda>\<omega>. norm (gradU ?c gain_dip x0 \<omega>))"
      by (rule norm_gradU_dip_continuous_on)
    have c2: "continuous_on (OmegaPF design_beam (pi / 4) - ball design_beam \<epsilon>)
              (\<lambda>y. norm (gradU ?c gain_dip x0 y) + sigma_min (HessU ?c gain_dip x0 y))"
      by (intro continuous_on_add norm_gradU_dip_continuous_on sigma_min_HessU_dip_continuous_on)
    have "\<exists>\<xi> \<kappa>. 0 < \<xi> \<and> 0 < \<kappa>
          \<and> F0 ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam (OmegaPF design_beam (pi / 4))
               \<delta>null pmin \<xi> \<kappa> \<epsilon> \<noteq> ({} :: ((real^2)^'n) set)"
      by (rule F0_nonempty_of_witness_radius[OF \<epsilon>0 OmegaPF_compact feas c1 c2 sph ann])
    then show "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4
          \<and> F0 ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam (OmegaPF design_beam (pi / 4))
               \<delta>null pmin \<xi> \<kappa> \<epsilon> \<noteq> ({} :: ((real^2)^'n) set)"
      using \<epsilon>0 \<epsilon>le by blast
  qed
qed

text \<open>The same with the constants written out: \<open>\<omega>\<^sub>0 = (\<pi>/2, 0)\<close>, \<open>\<omega>\<^sub>s = (0, 0)\<close>, and
  \<open>A = -1\<close>, \<open>B = 0\<close>, \<open>D = -1\<close>.\<close>

corollary F0_dip_nonempty_final_explicit:
  fixes dmin \<delta>null pmin :: real and \<omega>null :: "real^2"
  assumes "6 \<le> CARD('n)" and "odd CARD('n)"
    and "0 < \<delta>null"
    and "pmin < gain_dip (vector [pi / 2, 0]) * (real CARD('n))\<^sup>2"
    and "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>null \<noteq> 0"
  shows "\<exists>R0. \<forall>R\<ge>R0. \<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4
          \<and> F0 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) gain_dip R dmin (- 1) 0 (- 1)
               \<omega>null (vector [pi / 2, 0]) (OmegaPF (vector [pi / 2, 0]) (pi / 4)) \<delta>null pmin \<xi> \<kappa> \<epsilon>
              \<noteq> ({} :: ((real^2)^'n) set)"
  using F0_dip_nonempty_final[OF assms(1,2,3) assms(4,5)[folded design_beam_def design_source_def]]
  unfolding design_plane_coefficients unfolding design_beam_def design_source_def .


subsection \<open>An instance with no vacuous constraint\<close>

text \<open>Minimum spacing \<open>1/4\<close>, null threshold \<open>1/100\<close>, main-beam power at least \<open>1\<close>, null
  direction \<open>(\<pi>/2, \<pi>/2)\<close>.  The element gain is \<open>1\<close> both in the main beam and in the null
  direction, so the null constraint really constrains the array factor, and \<open>1 < N\<^sup>2\<close>.\<close>

lemma gdip_pi_half: "gdip (pi / 2) = 1"
  by (simp add: gdip_def gsinc_pi_half power2_eq_square)

lemma gain_dip_at_height_pi_half: "gain_dip (vector [pi / 2, \<phi>]) = 1"
  by (simp add: gain_dip_def gdip_pi_half)

corollary F0_dip_nonempty_example:
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
  shows "\<exists>R0. \<forall>R\<ge>R0. \<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4
          \<and> F0 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) gain_dip R (1 / 4) (- 1) 0 (- 1)
               (vector [pi / 2, pi / 2]) (vector [pi / 2, 0])
               (OmegaPF (vector [pi / 2, 0]) (pi / 4)) (1 / 100) 1 \<xi> \<kappa> \<epsilon>
              \<noteq> ({} :: ((real^2)^'n) set)"
proof (rule F0_dip_nonempty_final_explicit[OF c6 oddN])
  show "(0::real) < 1 / 100"
    by simp
  have "(6::real)\<^sup>2 \<le> (real CARD('n))\<^sup>2"
    by (rule power_mono) (use c6 in simp_all)
  then show "1 < gain_dip (vector [pi / 2, 0]) * (real CARD('n))\<^sup>2"
    by (simp add: gain_dip_at_height_pi_half)
  have "vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 2])) 2 = 1"
    using design_cvec(2)[of "vector [pi / 2, pi / 2]"]
    by (simp add: design_beam_def design_source_def)
  then show "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 2]) \<noteq> 0"
    by (metis zero_index zero_neq_one)
qed

end
