theory Nonemptiness_Robust4
  imports "Applied_Math_D3_Curve_Cover.D3_Curve_Cover"
begin

text \<open>Lemmas used by \<open>Nonemptiness_Final\<close> that hold for every steering geometry: the retained
  bad set \<open>BadXGW\<close>, the regular stratum, the interior of the feasible body, and the passage
  from a regular feasible configuration to a point of \<open>F0\<close>.\<close>


subsection \<open>Arc cover of the phase-collinear locus\<close>

text \<open>Not used by the final theorem.\<close>

lemma d3_collinear_locus_finite_arc_cover:
  fixes ctr :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
  shows "d3_finitely_arc_coverable
           {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>} ctr \<delta>"
proof -
  have nsing_all: "\<forall>\<omega>\<in>{\<omega> \<in> OmegaPF ctr \<delta>. d3_crossTheta \<omega>0 \<omega>s \<omega> = 0}.
        (- d3_crossA ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) \<omega>s (\<omega>$1) * sin (\<omega>$2)
          + d3_crossB ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) \<omega>s (\<omega>$1) * cos (\<omega>$2) \<noteq> 0)
        \<or> ((((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * kz \<omega>s + ky \<omega>s) * sin (\<omega>$1) * cos (\<omega>$2)
          - (((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * kz \<omega>s + kx \<omega>s) * sin (\<omega>$1) * sin (\<omega>$2)
          + (((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * ky \<omega>s
             - ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * kx \<omega>s) * cos (\<omega>$1) \<noteq> 0)"
    using nsing
    unfolding d3_collinear_nsing_all_def d3_collinear_d2_def d3_collinear_d1_def
    by simp
  show ?thesis
    by (rule collinear_locus_finite_arc_cover[OF d0 pf hsep kdiff nsing_all])
qed

lemma d3_active_collinear_finite_arc_cover:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and nsing: "d3_collinear_nsing_all ctr \<delta> \<omega>0 \<omega>s"
  shows "\<exists>(I::nat set) arc. finite I
            \<and> (V \<inter> D3BadXG \<omega>0 \<omega>s {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}
                  :: ((real^2)^'n) set)
                \<subseteq> (\<Union>i\<in>I. (V \<inter> D3BadXG \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))
            \<and> (\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>)"
proof -
  have Lcov: "d3_finitely_arc_coverable
           {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>} ctr \<delta>"
    by (rule d3_collinear_locus_finite_arc_cover[OF d0 pf hsep kdiff nsing])
  show ?thesis
    by (rule d3_active_cover_from_angle_cover[OF Lcov])
qed


subsection \<open>The retained bad set\<close>

text \<open>Degenerate critical points with nonzero array factor and regular steering Jacobian at
  which neither the moment map nor the configuration derivative of the gradient is onto.\<close>

definition BadXGW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXGW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
      \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
      \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
      \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"


subsection \<open>The predicate \<open>\<gamma> \<parallel> c\<close>\<close>

definition gamma_par_c :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow> phase_collinear \<omega>0 \<omega>s \<omega>"

lemma not_gamma_par_c_iff:
  "\<not> gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<forall>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<noteq> t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<and> (\<forall>t. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"
  unfolding gamma_par_c_def phase_collinear_def by blast


subsection \<open>Set algebra for \<open>BadXGW\<close>\<close>

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
              \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
              \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  unfolding BadXGW_def by blast


subsection \<open>Moment-rank bridge\<close>

text \<open>The bad set lies in the fibre where the moment map is not onto.\<close>

definition MomentBad :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "MomentBad \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"

lemma BadXGW_subset_MomentBad:
  "(BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> MomentBad \<omega>0 \<omega>s \<Gamma>"
  unfolding BadXGW_def MomentBad_def by blast

lemma MomentBad_eq_mstarg_zeros:
  "(MomentBad \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
     = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
                              \<and> mstarg (cvec_dip \<omega>0 \<omega>s \<omega>) x = 0}"
  unfolding MomentBad_def by (simp add: surj_iff_mstarg)

lemma closed_mstarg_zero_slice:
  "closed {x::(real^2)^'n. mstarg c x = 0}"
  by (rule closed_Collect_eq[OF cont_mstarg continuous_on_const])

lemma branchP_indep_of_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<Gamma> :: "(real^2) set"
    and K :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])


subsection \<open>The regular stratum\<close>

lemma m5_D1_regular:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}
        \<subseteq> {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_grad_x_regular_part[OF openV Vne]])
qed


subsection \<open>From a regular feasible configuration to a point of \<open>F0\<close>\<close>

text \<open>Given a feasible \<open>x\<^sub>0\<close> and a radius \<open>\<epsilon> > 0\<close> with the gradient nonvanishing on the
  \<open>\<epsilon>\<close>-sphere and gradient-or-nondegenerate on the annulus, the margins \<open>\<kappa>\<close>, \<open>\<xi>\<close> exist by
  compactness and \<open>x\<^sub>0 \<in> F0\<close>.\<close>

lemma mem_imp_ne_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}" by blast

lemma F0_nonempty_of_witness:
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
  shows "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
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

text \<open>For a real \<open>2\<times>2\<close> matrix, @{const sigma_min} is positive iff the determinant is
  nonzero.\<close>

lemma sigma_min_pos_iff_invertible:
  fixes H :: "real^2^2"
  shows "0 < sigma_min H \<longleftrightarrow> matrix_det H \<noteq> 0"
proof -
  have lin: "linear ((*v) H)" by (rule matrix_vector_mul_linear)
  have bdd: "bdd_below ((\<lambda>v. norm (H *v v)) ` sphere 0 1)"
    by (rule bdd_belowI[of _ 0]) auto
  have cont: "continuous_on (sphere (0::real^2) 1) (\<lambda>v. norm (H *v v))"
    by (rule continuous_on_norm[OF
          bounded_linear.continuous_on[OF matrix_vector_mul_bounded_linear continuous_on_id]])
  \<comment> \<open>Step 1: positivity of the smallest singular value \<open>\<longleftrightarrow>\<close> nonvanishing on the unit sphere.\<close>
  have nz_iff: "0 < sigma_min H \<longleftrightarrow> (\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0)"
  proof
    assume pos: "0 < sigma_min H"
    show "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    proof
      fix v assume v: "v \<in> sphere (0::real^2) 1"
      have "sigma_min H \<le> norm (H *v v)"
        unfolding sigma_min_def by (rule cINF_lower[OF bdd v])
      with pos show "H *v v \<noteq> 0" by auto
    qed
  next
    assume nz: "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    obtain v0 where v0: "v0 \<in> sphere (0::real^2) 1"
        and v0min: "\<forall>v\<in>sphere (0::real^2) 1. norm (H *v v0) \<le> norm (H *v v)"
      using continuous_attains_inf[OF compact_sphere sphere01_ne cont] by blast
    have "sigma_min H = norm (H *v v0)"
    proof -
      have "sigma_min H \<le> norm (H *v v0)"
        unfolding sigma_min_def by (rule cINF_lower[OF bdd v0])
      moreover have "norm (H *v v0) \<le> sigma_min H"
        unfolding sigma_min_def by (rule cINF_greatest[OF sphere01_ne]) (rule v0min[rule_format])
      ultimately show ?thesis by linarith
    qed
    moreover have "0 < norm (H *v v0)" using nz v0 by auto
    ultimately show "0 < sigma_min H" by simp
  qed
  \<comment> \<open>Step 2: nonvanishing on the unit sphere \<open>\<longleftrightarrow>\<close> injectivity (normalise an arbitrary nonzero
      kernel vector to the sphere).\<close>
  have inj_iff: "(\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0) \<longleftrightarrow> inj ((*v) H)"
  proof
    assume nz: "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    show "inj ((*v) H)"
    proof (rule injI)
      fix a b assume eq: "H *v a = H *v b"
      have z: "H *v (a - b) = 0"
        using eq by (simp add: matrix_vector_mult_diff_distrib)
      show "a = b"
      proof (rule ccontr)
        assume "a \<noteq> b"
        hence ab: "a - b \<noteq> 0" by simp
        define u where "u = inverse (norm (a - b)) *\<^sub>R (a - b)"
        have nu: "norm u = 1"
        proof -
          have "norm u = \<bar>inverse (norm (a - b))\<bar> * norm (a - b)"
            by (simp add: u_def)
          also have "\<dots> = inverse (norm (a - b)) * norm (a - b)" by simp
          also have "\<dots> = 1" using ab by simp
          finally show ?thesis .
        qed
        have "u \<in> sphere (0::real^2) 1" using nu by (simp add: dist_norm)
        moreover have "H *v u = 0"
          by (simp add: u_def matrix_vector_mult_scaleR z)
        ultimately show False using nz by auto
      qed
    qed
  next
    assume inj: "inj ((*v) H)"
    show "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    proof
      fix v assume v: "v \<in> sphere (0::real^2) 1"
      hence "v \<noteq> 0" by (auto simp: dist_norm)
      moreover have "H *v (0::real^2) = 0" by simp
      ultimately show "H *v v \<noteq> 0" using inj by (metis injD)
    qed
  qed
  \<comment> \<open>Step 3: injectivity of a square linear map \<open>\<longleftrightarrow>\<close> nonzero determinant.\<close>
  have det_iff: "inj ((*v) H) \<longleftrightarrow> matrix_det H \<noteq> 0"
    using det_nz_iff_inj[OF lin] by simp
  show ?thesis using nz_iff inj_iff det_iff by blast
qed

text \<open>A strictly feasible configuration is interior to @{const Ffeas}.\<close>

lemma Ffeas_interior_nonempty:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes "\<exists>x::(real^2)^'n.
       (\<forall>p. fst p \<noteq> snd p \<longrightarrow> dmin < spdist A B D (x $ fst p) (x $ snd p))
     \<and> Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < \<delta>null
     \<and> pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr
     \<and> Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr < gain_dip ctr * (real CARD('n))\<^sup>2
     \<and> norm x < R"
  shows "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
proof -
  from assms obtain x :: "(real^2)^'n"
    where spac0: "\<forall>p. fst p \<noteq> snd p \<longrightarrow> dmin < spdist A B D (x $ fst p) (x $ snd p)"
      and Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < \<delta>null"
      and Pgt: "pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr"
      and nx: "norm x < R" by blast
  have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (x $ fst p) (x $ snd p)"
    using spac0 by blast
  have inR: "x \<in> ball 0 R" using nx by (simp add: dist_norm)
  obtain \<rho> where \<rho>: "0 < \<rho>"
      and sub: "ball x \<rho>
                \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
    using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
  have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
    by (rule interior_maximal[OF sub open_ball])
  moreover have "x \<in> ball x \<rho>" using \<rho> by simp
  ultimately show ?thesis by blast
qed

text \<open>A nondegenerate zero is isolated.  Hence a configuration with no degenerate critical
  point in the box is regular on a small sphere and on the annulus around the centre.\<close>

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


lemma sphere_subset_Omega:
  fixes ctr :: "real^2"
  assumes "\<epsilon> \<le> pi/2"
  shows "sphere ctr \<epsilon> \<subseteq> Omega ctr"
proof
  fix y assume "y \<in> sphere ctr \<epsilon>"
  hence dy: "dist y ctr = \<epsilon>" by (simp add: dist_commute sphere_def)
  show "y \<in> Omega ctr"
    unfolding Omega_def mem_box_cart
  proof (intro allI)
    fix i :: 2
    have b: "\<bar>y$i - ctr$i\<bar> \<le> pi/2"
    proof -
      have "\<bar>y$i - ctr$i\<bar> = \<bar>(y - ctr)$i\<bar>" by simp
      also have "\<dots> \<le> norm (y - ctr)" by (rule component_le_norm_cart)
      also have "\<dots> = \<epsilon>" using dy by (simp add: dist_norm)
      finally show ?thesis using assms by simp
    qed
    have v: "pi/2 \<le> (vector [pi/2, pi] :: real^2) $ i"
      using exhaust_2[of i] by (auto simp: vector_2 pi_gt_zero)
    have lo: "(ctr - vector [pi/2, pi]) $ i = ctr $ i - vector [pi/2, pi] $ i"
      by (simp add: vector_minus_component)
    have hi: "(ctr + vector [pi/2, pi]) $ i = ctr $ i + vector [pi/2, pi] $ i"
      by (simp add: vector_add_component)
    have b1: "y$i - ctr$i \<le> pi/2" using abs_le_D1[OF b] .
    have b2: "ctr$i - y$i \<le> pi/2" using abs_le_D2[OF b] by simp
    show "(ctr - vector [pi/2, pi]) $ i \<le> y $ i \<and> y $ i \<le> (ctr + vector [pi/2, pi]) $ i"
      using lo hi v b1 b2 by linarith
  qed
qed

lemma no_degenerate_to_sphere_annulus:
  fixes x0 :: "(real^2)^'n" and ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and nd: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  shows "\<exists>\<epsilon>>0. (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
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
  show ?thesis using \<epsilon>0 sphere annulus unfolding f_def by blast
qed

end
