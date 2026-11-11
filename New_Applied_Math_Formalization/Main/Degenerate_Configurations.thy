section \<open>Degenerate configurations are nowhere dense; robust feasible configurations exist\<close>

theory Degenerate_Configurations
  imports
    Applied_Math_Residual.Residual_Meager
    Applied_Math_Pattern.Feasibility_Witness
begin

lemma mem_imp_ne_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}" by blast

lemma isolated_nondeg_zero:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes hd: "(f has_derivative L) (at c)" and injL: "inj L" and fc: "f c = 0"
  shows "\<exists>d>0. \<forall>y. dist y c < d \<longrightarrow> y \<noteq> c \<longrightarrow> f y \<noteq> 0"
proof -
  have linL: "linear L" using hd by (rule has_derivative_linear)
  obtain B where B0: "0 < B" and Bn: "\<And>v. B * norm v \<le> norm (L v)"
    using linear_inj_bounded_below_pos[OF linL injL] by blast
  have "\<forall>e>0. \<exists>d>0. \<forall>y. norm (y - c) < d \<longrightarrow> norm (f y - f c - L (y - c)) \<le> e * norm (y - c)"
    using hd by (simp add: has_derivative_at_alt)
  then obtain d where d0: "0 < d"
      and db: "\<And>y. norm (y - c) < d \<Longrightarrow> norm (f y - f c - L (y - c)) \<le> (B/2) * norm (y - c)"
    using B0 half_gt_zero by blast
  have "\<forall>y. dist y c < d \<longrightarrow> y \<noteq> c \<longrightarrow> f y \<noteq> 0"
  proof (intro allI impI)
    fix y assume yd: "dist y c < d" and yc: "y \<noteq> c"
    have nyc: "0 < norm (y - c)" using yc by simp
    have ndc: "norm (y - c) < d" using yd by (simp add: dist_norm)
    have a1: "B * norm (y - c) \<le> norm (L (y - c))" by (rule Bn)
    have a2: "norm (f y - L (y - c)) \<le> (B/2) * norm (y - c)" using db[OF ndc] fc by simp
    have "(B/2) * norm (y - c) = B * norm (y - c) - (B/2) * norm (y - c)" by simp
    also have "\<dots> \<le> norm (L (y - c)) - norm (f y - L (y - c))" using a1 a2 by linarith
    also have "\<dots> \<le> norm (f y)"
      using norm_triangle_ineq2[of "L (y - c)" "f y"] by (simp add: norm_minus_commute)
    finally have "(B/2) * norm (y - c) \<le> norm (f y)" .
    moreover have "0 < (B/2) * norm (y - c)" using nyc B0 by simp
    ultimately have "0 < norm (f y)" by linarith
    thus "f y \<noteq> 0" by auto
  qed
  thus ?thesis using d0 by blast
qed

text \<open>The end-to-end theorems.  Steering: source overhead, main beam horizontal
  (@{const design_beam}, @{const design_source}); angular box @{term "OmegaPF design_beam (pi / 4)"}.
  The feasible set is the one of the paper (Eq. 22) for every minimum spacing, every null
  threshold above zero, every minimum main-beam power below the maximum and every null direction
  other than the main beam; the plane coefficients are those of Eqs. (12)--(14).

  The only hypotheses on the number \<open>N\<close> of relays are that it is odd and at least \<open>5\<close>.\<close>

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

subsection \<open>Degenerate configurations\<close>

text \<open>A configuration is degenerate if its pattern has a degenerate critical point in the box.\<close>

definition degenerate_configurations :: "((real^2)^'n) set" where
  "degenerate_configurations = {x. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
        gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
      \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0}"

text \<open>A degenerate critical point is of one of five kinds: a null of the array factor, a direction
  at which the wavevector map is singular, the main beam, a point at which the gradient is a
  submersion in the configuration, or a point of the residual set.  Each kind projects to a
  meager set of configurations.\<close>

theorem degenerate_configurations_meager:
  assumes c5: "5 \<le> CARD('n)" and oddN: "odd CARD('n)"
  shows "meager (degenerate_configurations :: ((real^2)^'n) set)"
proof -
  have d0: "(0::real) < pi / 4"
    by simp
  note pf = design_pole_free and hsep = design_hsep and kdiff = design_kdiff
  have card2: "2 \<le> CARD('n)" and card4: "4 \<le> CARD('n)"
    using c5 by simp_all
  let ?V = "UNIV :: ((real^2)^'n) set"
  let ?null = "{x \<in> ?V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> = 0}"
  let ?sing = "{x \<in> ?V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> matrix_det (jacobian (cvec_dip design_beam design_source) (at \<omega>)) = 0}"
  let ?beam = "{x \<in> ?V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> matrix_det (jacobian (cvec_dip design_beam design_source) (at \<omega>)) \<noteq> 0
          \<and> cvec_dip design_beam design_source \<omega> = 0}"
  let ?reg = "{x \<in> ?V. \<exists>\<omega> :: real^2. gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
            \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip design_beam design_source) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  let ?res = "{x \<in> ?V. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4).
            gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip design_beam design_source) x \<omega> \<noteq> 0
          \<and> matrix_det (jacobian (cvec_dip design_beam design_source) (at \<omega>)) \<noteq> 0
          \<and> cvec_dip design_beam design_source \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip design_beam design_source) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  have meag: "meager (?null \<union> ?sing \<union> ?beam \<union> ?reg \<union> ?res)"
    by (intro meager_Un
          meager_Azero_degenerate_stratum[OF open_UNIV UNIV_not_empty oddN d0 pf]
          meager_steering_singular[OF card2 pf hsep kdiff]
          meager_main_beam[OF card2 pf]
          meager_grad_x_regular_part[OF open_UNIV UNIV_not_empty]
          residual_meager_design[OF card4])
  have sub: "degenerate_configurations \<subseteq> ?null \<union> ?sing \<union> ?beam \<union> ?reg \<union> ?res"
  proof (rule subsetI)
    fix x :: "(real^2)^'n" assume "x \<in> degenerate_configurations"
    then obtain \<omega> where wD: "\<omega> \<in> OmegaPF design_beam (pi / 4)"
      and g0: "gradU (cvec_dip design_beam design_source) gain_dip x \<omega> = 0"
      and h0: "matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x \<omega>) = 0"
      unfolding degenerate_configurations_def by blast
    have xV: "x \<in> ?V"
      by simp
    show "x \<in> ?null \<union> ?sing \<union> ?beam \<union> ?reg \<union> ?res"
    proof (cases "A_cart (cvec_dip design_beam design_source) x \<omega> = 0")
      case True
      then have "x \<in> ?null"
        using xV wD g0 h0 by blast
      then show ?thesis by blast
    next
      case a0: False
      show ?thesis
      proof (cases "matrix_det (jacobian (cvec_dip design_beam design_source) (at \<omega>)) = 0")
        case True
        then have "x \<in> ?sing"
          using xV wD g0 h0 a0 by blast
        then show ?thesis by blast
      next
        case dnz: False
        show ?thesis
        proof (cases "cvec_dip design_beam design_source \<omega> = 0")
          case cz: True
          have "x \<in> ?beam"
            using xV wD g0 h0 a0 dnz cz by blast
          then show ?thesis by blast
        next
          case cnz: False
          show ?thesis
          proof (cases "(\<exists>Dx. ((\<lambda>y. gradU (cvec_dip design_beam design_source) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)")
            case True
            then have "x \<in> ?reg"
              using xV g0 h0 by blast
            then show ?thesis by blast
          next
            case nreg: False
            have "x \<in> ?res"
              using xV wD g0 h0 a0 dnz cnz nreg by blast
            then show ?thesis by blast
          qed
        qed
      qed
    qed
  qed
  show ?thesis by (rule meager_subset[OF sub meag])
qed

text \<open>The set is closed: it is the projection of a closed set along the compact box.\<close>

lemma closed_exists_compact:
  fixes K :: "'a::euclidean_space set" and C :: "('a \<times> 'b::euclidean_space) set"
  assumes K: "compact K" and C: "closed C"
  shows "closed {x. \<exists>\<omega>\<in>K. (\<omega>, x) \<in> C}"
proof -
  have "closedin (top_of_set (K \<times> (UNIV :: 'b set))) ((K \<times> UNIV) \<inter> C)"
    by (rule closedin_closed_Int[OF C])
  then have "closedin (top_of_set (UNIV :: 'b set)) {x. \<exists>\<omega>. \<omega> \<in> K \<and> (\<omega>, x) \<in> (K \<times> UNIV) \<inter> C}"
    by (rule closedin_compact_projection[OF K])
  moreover have "{x. \<exists>\<omega>. \<omega> \<in> K \<and> (\<omega>, x) \<in> (K \<times> UNIV) \<inter> C} = {x. \<exists>\<omega>\<in>K. (\<omega>, x) \<in> C}"
    by auto
  ultimately show ?thesis
    by simp
qed

lemma continuous_on_gradU_dip_joint:
  "continuous_on (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
     (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))"
proof -
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where d: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                     has_derivative blinfun_apply (G' z)) (at z)"
    using gradU_dip_joint_C1 by blast
  show ?thesis
    by (rule has_derivative_continuous_on[where f' = "\<lambda>z. blinfun_apply (G' z)"]) (simp add: d)
qed

lemma continuous_on_gradU_dip_swap:
  "continuous_on UNIV
     (\<lambda>q :: (real^2) \<times> ((real^2)^'n). gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (snd q) (fst q))"
proof -
  have swap: "continuous_on UNIV (\<lambda>q :: (real^2) \<times> ((real^2)^'n). (snd q, fst q))"
    by (intro continuous_intros)
  show ?thesis
    using continuous_on_compose2[OF continuous_on_gradU_dip_joint swap, of \<omega>0 \<omega>s] by simp
qed

lemma continuous_on_HessU_dip_swap:
  "continuous_on UNIV
     (\<lambda>q :: (real^2) \<times> ((real^2)^'n). HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (snd q) (fst q))"
proof -
  have swap: "continuous_on UNIV (\<lambda>q :: (real^2) \<times> ((real^2)^'n). (snd q, fst q))"
    by (intro continuous_intros)
  show ?thesis
    using continuous_on_compose2[OF continuous_on_HessU_dip_joint swap, of \<omega>0 \<omega>s] by simp
qed

lemma degenerate_set_closed:
  fixes ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  shows "closed {x :: (real^2)^'n. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
proof -
  define g :: "(real^2) \<times> ((real^2)^'n) \<Rightarrow> real^2"
    where "g = (\<lambda>q. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (snd q) (fst q))"
  define h :: "(real^2) \<times> ((real^2)^'n) \<Rightarrow> real"
    where "h = (\<lambda>q. matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (snd q) (fst q)))"
  have swap: "continuous_on UNIV (\<lambda>q :: (real^2) \<times> ((real^2)^'n). (snd q, fst q))"
    by (intro continuous_intros)
  have cg: "continuous_on UNIV g"
    unfolding g_def by (rule continuous_on_gradU_dip_swap)
  have ce: "continuous_on UNIV
      (\<lambda>q :: (real^2) \<times> ((real^2)^'n). vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (snd q) (fst q)) k) l)"
    for k l :: 2
    using continuous_on_compose2[OF continuous_on_HessU_dip_entry swap, of \<omega>0 \<omega>s k l] by simp
  have ch: "continuous_on UNIV h"
    unfolding h_def det_2 by (intro continuous_intros ce)
  have clo: "closed {q. g q = 0 \<and> h q = 0}"
    by (intro closed_Collect_conj closed_Collect_eq cg ch continuous_on_const)
  have "closed {x. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. (\<omega>, x) \<in> {q. g q = 0 \<and> h q = 0}}"
    by (rule closed_exists_compact[OF OmegaPF_compact clo])
  then show ?thesis
    by (simp add: g_def h_def)
qed

text \<open>A closed meager set has empty interior, by the Baire category theorem.\<close>

theorem degenerate_configurations_nowhere_dense:
  assumes c5: "5 \<le> CARD('n)" and oddN: "odd CARD('n)"
  shows "closed (degenerate_configurations :: ((real^2)^'n) set)"
    and "nowhere_dense (degenerate_configurations :: ((real^2)^'n) set)"
proof -
  show cl: "closed (degenerate_configurations :: ((real^2)^'n) set)"
    unfolding degenerate_configurations_def by (rule degenerate_set_closed)
  have "interior (degenerate_configurations :: ((real^2)^'n) set) = {}"
  proof (rule ccontr)
    assume ne: "interior (degenerate_configurations :: ((real^2)^'n) set) \<noteq> {}"
    have "meager (interior (degenerate_configurations :: ((real^2)^'n) set))"
      by (rule meager_subset[OF interior_subset degenerate_configurations_meager[OF c5 oddN]])
    moreover have "\<not> meager (interior (degenerate_configurations :: ((real^2)^'n) set))"
      by (rule open_nonempty_not_meager[OF open_interior ne])
    ultimately show False
      by simp
  qed
  then show "nowhere_dense (degenerate_configurations :: ((real^2)^'n) set)"
    unfolding nowhere_dense_def using cl by simp
qed

corollary nondegenerate_open_dense:
  assumes c5: "5 \<le> CARD('n)" and oddN: "odd CARD('n)"
  shows "open (- (degenerate_configurations :: ((real^2)^'n) set))"
    and "closure (- (degenerate_configurations :: ((real^2)^'n) set)) = UNIV"
proof -
  note nd = degenerate_configurations_nowhere_dense[OF c5 oddN]
  show "open (- (degenerate_configurations :: ((real^2)^'n) set))"
    by (rule open_Compl[OF nd(1)])
  show "closure (- (degenerate_configurations :: ((real^2)^'n) set)) = UNIV"
    using nd unfolding nowhere_dense_def by (simp add: closure_complement)
qed

subsection \<open>From a configuration without degenerate critical points to the margins\<close>

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

lemma X0_of_witness_radius:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real" and ctr :: planar
    and x0 :: "planar^'n" and \<epsilon> :: real and \<Omega>dom :: "planar set"
  assumes \<epsilon>0: "0 < \<epsilon>" and cOm: "compact \<Omega>dom"
    and cdN: "continuous_on (sphere ctr \<epsilon>) (\<lambda>\<omega>. norm (gradU cvec g x0 \<omega>))"
    and cdsum: "continuous_on (\<Omega>dom - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
    and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU cvec g x0 \<omega> \<noteq> 0"
    and rO: "\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
                gradU cvec g x0 y \<noteq> 0 \<or> 0 < sigma_min (HessU cvec g x0 y)"
  shows "\<exists>\<xi> \<kappa>. 0 < \<xi> \<and> 0 < \<kappa> \<and> x0 \<in> X0 cvec g ctr \<Omega>dom \<xi> \<kappa> \<epsilon>"
proof -
  have sph_ne: "sphere ctr \<epsilon> \<noteq> {}"
  proof -
    have "dist (ctr + \<epsilon> *\<^sub>R axis (1::2) 1) ctr = \<epsilon>"
      using \<epsilon>0 by (simp add: dist_norm abs_of_pos)
    hence "ctr + \<epsilon> *\<^sub>R axis (1::2) 1 \<in> sphere ctr \<epsilon>"
      by (simp add: dist_commute)
    thus ?thesis by blast
  qed
  obtain \<omega>m where \<omega>m: "\<omega>m \<in> sphere ctr \<epsilon>"
      and \<omega>min: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. norm (gradU cvec g x0 \<omega>m) \<le> norm (gradU cvec g x0 \<omega>)"
    using continuous_attains_inf[OF compact_sphere sph_ne cdN] by blast
  define \<kappa> where "\<kappa> = norm (gradU cvec g x0 \<omega>m)"
  have \<kappa>pos: "0 < \<kappa>" using bspec[OF rsph \<omega>m] unfolding \<kappa>_def by simp
  have inXrob: "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>"
    using \<omega>min unfolding Xrobust_def \<kappa>_def by simp
  show ?thesis
  proof (cases "\<Omega>dom - ball ctr \<epsilon> = {}")
    case True
    have "x0 \<in> X0 cvec g ctr \<Omega>dom 1 \<kappa> \<epsilon>"
      using inXrob True unfolding X0_def by blast
    moreover have "(0::real) < 1" by simp
    ultimately show ?thesis using \<kappa>pos by blast
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
    hence "x0 \<in> X0 cvec g ctr \<Omega>dom \<xi> \<kappa> \<epsilon>" unfolding X0_def by simp
    thus ?thesis using \<xi>pos \<kappa>pos by blast
  qed
qed

text \<open>A configuration without degenerate critical points in the box is robust for suitable margins.\<close>

theorem nondegenerate_in_X0:
  fixes x :: "(real^2)^'n" and ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and nd: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                              \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0)"
  shows "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> \<delta>
          \<and> x \<in> X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr (OmegaPF ctr \<delta>) \<xi> \<kappa> \<epsilon>"
proof -
  obtain \<epsilon> :: real where \<epsilon>0: "0 < \<epsilon>" and \<epsilon>le: "\<epsilon> \<le> \<delta>"
    and sph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> \<noteq> 0"
    and ann: "\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x y \<noteq> 0
                \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x y)"
    using no_degenerate_to_sphere_annulus_bounded[OF d0 dpi nd] by blast
  have c1: "continuous_on (sphere ctr \<epsilon>) (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
    by (rule norm_gradU_dip_continuous_on)
  have c2: "continuous_on (OmegaPF ctr \<delta> - ball ctr \<epsilon>)
            (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x y)
                 + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x y))"
    by (intro continuous_on_add norm_gradU_dip_continuous_on sigma_min_HessU_dip_continuous_on)
  obtain \<xi> \<kappa> where "0 < \<xi>" and "0 < \<kappa>"
    and "x \<in> X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr (OmegaPF ctr \<delta>) \<xi> \<kappa> \<epsilon>"
    using X0_of_witness_radius[OF \<epsilon>0 OmegaPF_compact c1 c2 sph ann] by blast
  then show ?thesis
    using \<epsilon>0 \<epsilon>le by blast
qed

text \<open>With smaller margins, the robust set contains a ball around each of its points.\<close>

lemma continuous_on_sigma_min_HessU_dip_swap:
  "continuous_on UNIV
     (\<lambda>q :: (real^2) \<times> ((real^2)^'n). sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (snd q) (fst q)))"
  using continuous_on_compose2[OF sigma_min_continuous_on[of UNIV] continuous_on_HessU_dip_swap[of \<omega>0 \<omega>s]]
  by simp

lemma X0_lower_margins_ball:
  fixes x :: "(real^2)^'n" and \<Omega> :: "(real^2) set" and ctr \<omega>0 \<omega>s :: "real^2"
  assumes cO: "compact \<Omega>" and xi: "\<xi>' < \<xi>" and ka: "\<kappa>' < \<kappa>"
    and mem: "x \<in> X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr \<Omega> \<xi> \<kappa> \<epsilon>"
  shows "\<exists>e>0. ball x e \<subseteq> X0 (cvec_dip \<omega>0 \<omega>s) gain_dip ctr \<Omega> \<xi>' \<kappa>' \<epsilon>"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s"
  define n :: "(real^2) \<times> ((real^2)^'n) \<Rightarrow> real"
    where "n = (\<lambda>q. norm (gradU ?c gain_dip (snd q) (fst q)))"
  define m :: "(real^2) \<times> ((real^2)^'n) \<Rightarrow> real"
    where "m = (\<lambda>q. norm (gradU ?c gain_dip (snd q) (fst q))
                    + sigma_min (HessU ?c gain_dip (snd q) (fst q)))"
  have cn: "continuous_on UNIV n"
    unfolding n_def by (intro continuous_on_norm continuous_on_gradU_dip_swap)
  have cm: "continuous_on UNIV m"
    unfolding m_def
    by (intro continuous_on_add continuous_on_norm continuous_on_gradU_dip_swap
          continuous_on_sigma_min_HessU_dip_swap)
  define B1 where "B1 = {y :: (real^2)^'n. \<exists>\<omega>\<in>sphere ctr \<epsilon>. (\<omega>, y) \<in> {q. n q \<le> \<kappa>'}}"
  define B2 where "B2 = {y :: (real^2)^'n. \<exists>\<omega>\<in>\<Omega> - ball ctr \<epsilon>. (\<omega>, y) \<in> {q. m q \<le> \<xi>'}}"
  have c1: "closed B1"
    unfolding B1_def
    by (intro closed_exists_compact compact_sphere closed_Collect_le cn continuous_on_const)
  have c2: "closed B2"
    unfolding B2_def
    by (intro closed_exists_compact compact_minus_ball[OF cO] closed_Collect_le cm continuous_on_const)
  have x1: "x \<notin> B1"
  proof
    assume "x \<in> B1"
    then obtain \<omega> where w: "\<omega> \<in> sphere ctr \<epsilon>" and le: "norm (gradU ?c gain_dip x \<omega>) \<le> \<kappa>'"
      by (auto simp: B1_def n_def)
    have "\<kappa> \<le> norm (gradU ?c gain_dip x \<omega>)"
      using mem w unfolding X0_def Xrobust_def by blast
    with le ka show False
      by linarith
  qed
  have x2: "x \<notin> B2"
  proof
    assume "x \<in> B2"
    then obtain y where y: "y \<in> \<Omega> - ball ctr \<epsilon>"
      and le: "norm (gradU ?c gain_dip x y) + sigma_min (HessU ?c gain_dip x y) \<le> \<xi>'"
      by (auto simp: B2_def m_def)
    have "\<xi> \<le> norm (gradU ?c gain_dip x y) + sigma_min (HessU ?c gain_dip x y)"
      using mem y unfolding X0_def by blast
    with le xi show False
      by linarith
  qed
  have op: "open (- (B1 \<union> B2))"
    by (intro open_Compl closed_Un c1 c2)
  have xin: "x \<in> - (B1 \<union> B2)"
    using x1 x2 by simp
  obtain e where e0: "0 < e" and eb: "ball x e \<subseteq> - (B1 \<union> B2)"
    using op xin unfolding open_contains_ball by blast
  have "ball x e \<subseteq> X0 ?c gain_dip ctr \<Omega> \<xi>' \<kappa>' \<epsilon>"
  proof
    fix y assume "y \<in> ball x e"
    then have y1: "y \<notin> B1" and y2: "y \<notin> B2"
      using eb by auto
    have r1: "\<kappa>' \<le> norm (gradU ?c gain_dip y \<omega>)" if w: "\<omega> \<in> sphere ctr \<epsilon>" for \<omega>
    proof (rule ccontr)
      assume "\<not> \<kappa>' \<le> norm (gradU ?c gain_dip y \<omega>)"
      then have "norm (gradU ?c gain_dip y \<omega>) \<le> \<kappa>'"
        by simp
      then have "y \<in> B1"
        unfolding B1_def n_def using w by auto
      with y1 show False
        by simp
    qed
    have r2: "\<xi>' \<le> norm (gradU ?c gain_dip y z) + sigma_min (HessU ?c gain_dip y z)"
      if z: "z \<in> \<Omega> - ball ctr \<epsilon>" for z
    proof (rule ccontr)
      assume "\<not> \<xi>' \<le> norm (gradU ?c gain_dip y z) + sigma_min (HessU ?c gain_dip y z)"
      then have "norm (gradU ?c gain_dip y z) + sigma_min (HessU ?c gain_dip y z) \<le> \<xi>'"
        by simp
      then have "y \<in> B2"
        unfolding B2_def m_def using z by auto
      with y2 show False
        by simp
    qed
    show "y \<in> X0 ?c gain_dip ctr \<Omega> \<xi>' \<kappa>' \<epsilon>"
      unfolding X0_def Xrobust_def using r1 r2 by blast
  qed
  then show ?thesis
    using e0 by blast
qed

subsection \<open>A feasible configuration with no degenerate critical point\<close>

text \<open>A strictly feasible configuration, for all admissible parameters and all large radii.  Its
  relays lie on a line through the origin.  The plane coefficients \<open>A\<close>, \<open>B\<close>, \<open>D\<close> are arbitrary
  here.\<close>

lemma design_strictly_feasible_collinear:
  fixes dmin \<delta>null pmin A B D :: real and \<omega>null :: "real^2"
  assumes N1: "1 < CARD('n)"
    and null_pos: "0 < \<delta>null"
    and power: "pmin < gain_dip design_beam * (real CARD('n))\<^sup>2"
    and null_dir: "cvec_dip design_beam design_source \<omega>null \<noteq> 0"
  shows "\<exists>(x::(real^2)^'n) v. A_cart (cvec_dip design_beam design_source) x \<omega>null = 0
          \<and> (\<forall>m. \<exists>r. x $ m = r *\<^sub>R v)
          \<and> (\<forall>R\<ge>norm x + 1. \<exists>\<rho>>0. ball x \<rho> \<subseteq> Ffeas (cvec_dip design_beam design_source) gain_dip
                R dmin A B D \<omega>null design_beam \<delta>null pmin)"
proof -
  define s where "s = max dmin 0 + 1"
  have spos: "0 < s" and ds: "dmin < s"
    by (simp_all add: s_def)
  obtain x :: "(real^2)^'n" and v :: "real^2"
    where afz: "A_cart (cvec_dip design_beam design_source) x \<omega>null = 0"
      and spac0: "\<forall>m m'. m \<noteq> m' \<longrightarrow> s \<le> spdist A B D (x $ m) (x $ m')"
      and col: "\<forall>m. \<exists>r. x $ m = r *\<^sub>R v"
    using feasible_witness_exists[OF N1 null_dir spos] by meson
  have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (x $ fst p) (x $ snd p)"
    using spac0 ds by fastforce
  have Nlt: "U_cart (cvec_dip design_beam design_source) gain_dip x \<omega>null < \<delta>null"
    using afz null_pos by (simp add: U_cart_def)
  have Pgt: "pmin < U_cart (cvec_dip design_beam design_source) gain_dip x design_beam"
    using power by (simp add: U_cart_at_main[OF design_hsep])
  have "\<exists>\<rho>>0. ball x \<rho> \<subseteq> Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
                  \<omega>null design_beam \<delta>null pmin" if R: "norm x + 1 \<le> R" for R
  proof -
    have inR: "x \<in> ball 0 R"
      using R by (simp add: dist_norm)
    show ?thesis
      by (rule ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR])
  qed
  then show ?thesis
    using afz col by blast
qed

lemma design_feasible_interior:
  fixes dmin \<delta>null pmin A B D :: real and \<omega>null :: "real^2"
  assumes N1: "1 < CARD('n)"
    and null_pos: "0 < \<delta>null"
    and power: "pmin < gain_dip design_beam * (real CARD('n))\<^sup>2"
    and null_dir: "cvec_dip design_beam design_source \<omega>null \<noteq> 0"
  shows "\<exists>R0. \<forall>R\<ge>R0. interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set) \<noteq> {}"
proof -
  obtain x :: "(real^2)^'n"
    where feas: "\<And>R. norm x + 1 \<le> R \<Longrightarrow> \<exists>\<rho>>0. ball x \<rho> \<subseteq> Ffeas (cvec_dip design_beam design_source)
                gain_dip R dmin A B D \<omega>null design_beam \<delta>null pmin"
    using design_strictly_feasible_collinear[OF N1 null_pos power null_dir, of dmin A B D] by blast
  show ?thesis
  proof (intro exI[of _ "norm x + 1"] allI impI)
    fix R :: real assume R: "norm x + 1 \<le> R"
    obtain \<rho> where \<rho>: "0 < \<rho>"
      and sub: "ball x \<rho> \<subseteq> Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
                  \<omega>null design_beam \<delta>null pmin"
      using feas[OF R] by blast
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

text \<open>Some configuration in the interior of the feasible set has no degenerate critical point
  anywhere in the box.\<close>

theorem regular_feasible_configuration_exists:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null :: "real^2"
  assumes c5: "5 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and int_ne: "interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set) \<noteq> {}"
  shows "\<exists>x0 \<in> interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set).
      \<forall>\<omega>\<in>OmegaPF design_beam (pi / 4).
        \<not> (gradU (cvec_dip design_beam design_source) gain_dip x0 \<omega> = 0
           \<and> matrix_det (HessU (cvec_dip design_beam design_source) gain_dip x0 \<omega>) = 0)"
proof -
  let ?I = "interior (Ffeas (cvec_dip design_beam design_source) gain_dip R dmin A B D
            \<omega>null design_beam \<delta>null pmin :: ((real^2)^'n) set)"
  have "\<not> ?I \<subseteq> degenerate_configurations"
  proof
    assume sub: "?I \<subseteq> degenerate_configurations"
    have "meager ?I"
      by (rule meager_subset[OF sub degenerate_configurations_meager[OF c5 oddN]])
    moreover have "\<not> meager ?I"
      by (rule open_nonempty_not_meager[OF open_interior int_ne])
    ultimately show False
      by simp
  qed
  then obtain x0 where "x0 \<in> ?I" and "x0 \<notin> degenerate_configurations"
    by blast
  then show ?thesis
    unfolding degenerate_configurations_def by blast
qed

text \<open>The configurations without degenerate critical points are dense in every open set, in
  particular in the interior of the feasible set.\<close>

corollary nondegenerate_dense_in_open:
  fixes U :: "((real^2)^'n) set"
  assumes c5: "5 \<le> CARD('n)" and oddN: "odd CARD('n)" and U: "open U"
  shows "U \<subseteq> closure (U - degenerate_configurations)"
proof -
  have "U \<inter> closure (- degenerate_configurations) \<subseteq> closure (U \<inter> - degenerate_configurations)"
    by (rule open_Int_closure_subset[OF U])
  moreover have "closure (- (degenerate_configurations :: ((real^2)^'n) set)) = UNIV"
    by (rule nondegenerate_open_dense(2)[OF c5 oddN])
  moreover have "U \<inter> - degenerate_configurations = U - degenerate_configurations"
    by (rule Diff_eq[symmetric])
  ultimately show ?thesis
    by simp
qed

subsection \<open>The theorem\<close>

text \<open>For suitable margins the robust feasible set contains a ball.\<close>

theorem F0_dip_interior_nonempty:
  fixes dmin \<delta>null pmin :: real and \<omega>null :: "real^2"
  assumes c5: "5 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and null_pos: "0 < \<delta>null"
    and power: "pmin < gain_dip design_beam * (real CARD('n))\<^sup>2"
    and null_dir: "cvec_dip design_beam design_source \<omega>null \<noteq> 0"
  shows "\<exists>R0. \<forall>R\<ge>R0. \<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4
          \<and> interior (F0 (cvec_dip design_beam design_source) gain_dip R dmin
               (kx design_source - kx design_beam) (ky design_source - ky design_beam)
               (kz design_beam - kz design_source)
               \<omega>null design_beam (OmegaPF design_beam (pi / 4)) \<delta>null pmin \<xi> \<kappa> \<epsilon>)
              \<noteq> ({} :: ((real^2)^'n) set)"
proof -
  let ?A = "kx design_source - kx design_beam" and ?B = "ky design_source - ky design_beam"
    and ?D = "kz design_beam - kz design_source"
  let ?c = "cvec_dip design_beam design_source"
  have N1: "1 < CARD('n)"
    using c5 by simp
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
      using regular_feasible_configuration_exists[OF c5 oddN R0[OF R]] by blast
    obtain \<rho> where \<rho>0: "0 < \<rho>"
      and \<rho>b: "ball x0 \<rho> \<subseteq> Ffeas ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam \<delta>null pmin"
      using x0I unfolding mem_interior by blast
    have d0: "(0::real) < pi / 4" and dpi: "pi / 4 \<le> (pi::real)"
      by simp_all
    obtain \<xi> \<kappa> \<epsilon> :: real where pos: "0 < \<xi>" "0 < \<kappa>" "0 < \<epsilon>" "\<epsilon> \<le> pi / 4"
      and rob: "x0 \<in> X0 ?c gain_dip design_beam (OmegaPF design_beam (pi / 4)) \<xi> \<kappa> \<epsilon>"
      using nondegenerate_in_X0[OF d0 dpi nondeg] by blast
    have h1: "\<xi> / 2 < \<xi>" and h2: "\<kappa> / 2 < \<kappa>"
      using pos by simp_all
    obtain e where e0: "0 < e"
      and eb: "ball x0 e \<subseteq> X0 ?c gain_dip design_beam (OmegaPF design_beam (pi / 4)) (\<xi> / 2) (\<kappa> / 2) \<epsilon>"
      using X0_lower_margins_ball[OF OmegaPF_compact h1 h2 rob] by blast
    have sub: "ball x0 (min \<rho> e) \<subseteq> F0 ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam
               (OmegaPF design_beam (pi / 4)) \<delta>null pmin (\<xi> / 2) (\<kappa> / 2) \<epsilon>"
      unfolding F0_def
      using \<rho>b eb subset_ball[of "min \<rho> e" \<rho> x0] subset_ball[of "min \<rho> e" e x0] by auto
    have "x0 \<in> interior (F0 ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam
               (OmegaPF design_beam (pi / 4)) \<delta>null pmin (\<xi> / 2) (\<kappa> / 2) \<epsilon>)"
      by (rule interiorI[OF open_ball _ sub]) (use \<rho>0 e0 in simp)
    then have ne: "interior (F0 ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam
               (OmegaPF design_beam (pi / 4)) \<delta>null pmin (\<xi> / 2) (\<kappa> / 2) \<epsilon>)
            \<noteq> ({} :: ((real^2)^'n) set)"
      by (rule mem_imp_ne_empty)
    have p1: "0 < \<xi> / 2" and p2: "0 < \<kappa> / 2"
      using pos by simp_all
    show "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4
          \<and> interior (F0 ?c gain_dip R dmin ?A ?B ?D \<omega>null design_beam (OmegaPF design_beam (pi / 4))
               \<delta>null pmin \<xi> \<kappa> \<epsilon>) \<noteq> ({} :: ((real^2)^'n) set)"
      using p1 p2 pos(3,4) ne by blast
  qed
qed

text \<open>In particular it is nonempty.\<close>

corollary F0_dip_nonempty_final:
  fixes dmin \<delta>null pmin :: real and \<omega>null :: "real^2"
  assumes c5: "5 \<le> CARD('n)" and oddN: "odd CARD('n)"
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
  let ?F0 = "\<lambda>R \<xi> \<kappa> \<epsilon>. (F0 (cvec_dip design_beam design_source) gain_dip R dmin
               (kx design_source - kx design_beam) (ky design_source - ky design_beam)
               (kz design_beam - kz design_source)
               \<omega>null design_beam (OmegaPF design_beam (pi / 4)) \<delta>null pmin \<xi> \<kappa> \<epsilon> :: ((real^2)^'n) set)"
  obtain R0 where R0: "\<And>R. R0 \<le> R \<Longrightarrow> \<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4
          \<and> interior (?F0 R \<xi> \<kappa> \<epsilon>) \<noteq> {}"
    using F0_dip_interior_nonempty[OF c5 oddN null_pos power null_dir] by blast
  show ?thesis
  proof (rule exI[of _ R0], intro allI impI)
    fix R :: real assume "R0 \<le> R"
    then obtain \<xi> \<kappa> \<epsilon> where pos: "0 < \<xi>" "0 < \<kappa>" "0 < \<epsilon>" "\<epsilon> \<le> pi / 4"
      and ne: "interior (?F0 R \<xi> \<kappa> \<epsilon>) \<noteq> {}"
      using R0 by blast
    have "?F0 R \<xi> \<kappa> \<epsilon> \<noteq> {}"
    proof
      assume "?F0 R \<xi> \<kappa> \<epsilon> = {}"
      then have "interior (?F0 R \<xi> \<kappa> \<epsilon>) = interior {}"
        by (rule arg_cong)
      with ne show False
        by simp
    qed
    then show "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4 \<and> ?F0 R \<xi> \<kappa> \<epsilon> \<noteq> {}"
      using pos by blast
  qed
qed

text \<open>The same with the constants written out: \<open>\<omega>\<^sub>0 = (\<pi>/2, 0)\<close>, \<open>\<omega>\<^sub>s = (0, 0)\<close>, and
  \<open>A = -1\<close>, \<open>B = 0\<close>, \<open>D = -1\<close>.\<close>

corollary F0_dip_nonempty_final_explicit:
  fixes dmin \<delta>null pmin :: real and \<omega>null :: "real^2"
  assumes "5 \<le> CARD('n)" and "odd CARD('n)"
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
  assumes c5: "5 \<le> CARD('n)" and oddN: "odd CARD('n)"
  shows "\<exists>R0. \<forall>R\<ge>R0. \<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon> \<and> \<epsilon> \<le> pi / 4
          \<and> F0 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) gain_dip R (1 / 4) (- 1) 0 (- 1)
               (vector [pi / 2, pi / 2]) (vector [pi / 2, 0])
               (OmegaPF (vector [pi / 2, 0]) (pi / 4)) (1 / 100) 1 \<xi> \<kappa> \<epsilon>
              \<noteq> ({} :: ((real^2)^'n) set)"
proof (rule F0_dip_nonempty_final_explicit[OF c5 oddN])
  show "(0::real) < 1 / 100"
    by simp
  have "(5::real)\<^sup>2 \<le> (real CARD('n))\<^sup>2"
    by (rule power_mono) (use c5 in simp_all)
  then show "1 < gain_dip (vector [pi / 2, 0]) * (real CARD('n))\<^sup>2"
    by (simp add: gain_dip_at_height_pi_half)
  have "vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 2])) 2 = 1"
    using design_cvec(2)[of "vector [pi / 2, pi / 2]"]
    by (simp add: design_beam_def design_source_def)
  then show "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 2]) \<noteq> 0"
    by (metis zero_index zero_neq_one)
qed

end
