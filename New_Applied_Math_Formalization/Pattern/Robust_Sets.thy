section \<open>The robust feasible sets\<close>

theory Robust_Sets
  imports
    Feasible_Set
    Dipole_Pattern
begin

subsection \<open>The smallest singular value\<close>

definition sigma_min :: "real^2^2 \<Rightarrow> real" where
  \<comment> \<open>smallest singular value: \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) = inf\<^bsub>\<parallel>v\<parallel>=1\<^esub> \<parallel>H v\<parallel>\<close> (the operator-norm characterisation)\<close>
  "sigma_min H = (INF v \<in> sphere 0 1. norm (H *v v))"

lemma sphere01_ne: "sphere (0::real^2) 1 \<noteq> {}"
  by simp

lemma sigma_min_nonneg: "0 \<le> sigma_min H"
  unfolding sigma_min_def by (rule cINF_greatest[OF sphere01_ne]) simp

lemma sigma_min_diff_le:
  fixes H1 H2 :: "real^2^2"
  shows "sigma_min H1 - sigma_min H2 \<le> onorm ((*v) (H1 - H2))"
proof -
  let ?L = "onorm ((*v) (H1 - H2))"
  have bdd: "bdd_below ((\<lambda>v. norm (H1 *v v)) ` sphere 0 1)"
    by (rule bdd_belowI[of _ 0]) auto
  have step: "sigma_min H1 - ?L \<le> norm (H2 *v v)" if v: "v \<in> sphere (0::real^2) 1" for v
  proof -
    have nv: "norm v = 1" using v by (simp add: dist_norm)
    have le1: "sigma_min H1 \<le> norm (H1 *v v)"
      unfolding sigma_min_def by (rule cINF_lower[OF bdd v])
    have tri: "norm (H1 *v v) \<le> norm (H2 *v v) + norm ((H1 - H2) *v v)"
      using norm_triangle_sub[of "H1 *v v" "H2 *v v"]
      by (simp add: matrix_vector_mult_diff_rdistrib)
    have onb: "norm ((H1 - H2) *v v) \<le> ?L"
      using onorm[OF matrix_vector_mul_bounded_linear, of "H1 - H2" v] nv by simp
    from le1 tri onb show ?thesis by linarith
  qed
  have main: "sigma_min H1 - ?L \<le> sigma_min H2"
  proof -
    have "sigma_min H1 - ?L \<le> (INF v\<in>sphere (0::real^2) 1. norm (H2 *v v))"
      by (rule cINF_greatest[OF sphere01_ne]) (rule step)
    thus ?thesis by (simp add: sigma_min_def)
  qed
  thus ?thesis by linarith
qed

lemma onorm_mv_le4:
  fixes M :: "real^2^2"
  shows "onorm ((*v) M) \<le> 4 * norm M"
proof -
  have "onorm ((*v) M) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
    by (rule onorm_le_matrix_component_sum)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::2 set). \<Sum>j\<in>(UNIV::2 set). norm M)"
    by (intro sum_mono)
       (rule order_trans[OF component_le_norm_cart Finite_Cartesian_Product.norm_nth_le])
  also have "\<dots> = 4 * norm M" by simp
  finally show ?thesis .
qed

lemma sigma_min_continuous_on:
  "continuous_on (S::(real^2^2) set) sigma_min"
proof -
  have "4-lipschitz_on UNIV (sigma_min :: real^2^2 \<Rightarrow> real)"
  proof (rule lipschitz_onI)
    show "(0::real) \<le> 4" by simp
    fix H1 H2 :: "real^2^2"
    have b1: "sigma_min H1 - sigma_min H2 \<le> onorm ((*v) (H1 - H2))"
      by (rule sigma_min_diff_le)
    have b2: "sigma_min H2 - sigma_min H1 \<le> onorm ((*v) (H2 - H1))"
      by (rule sigma_min_diff_le)
    have nc: "norm (H2 - H1) = norm (H1 - H2)" by (simp add: norm_minus_commute)
    have "\<bar>sigma_min H1 - sigma_min H2\<bar> \<le> 4 * norm (H1 - H2)"
      using b1 b2 onorm_mv_le4[of "H1 - H2"] onorm_mv_le4[of "H2 - H1"] nc
      by (simp add: abs_le_iff)
    thus "dist (sigma_min H1) (sigma_min H2) \<le> 4 * dist H1 H2"
      by (simp add: dist_norm dist_real_def)
  qed
  hence "continuous_on UNIV (sigma_min :: real^2^2 \<Rightarrow> real)"
    by (rule lipschitz_on_continuous_on)
  thus ?thesis by (rule continuous_on_subset) simp
qed

lemma sigma_min_HessU_dip_continuous_on:
  "continuous_on S (\<lambda>\<omega>. sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  using continuous_on_compose[OF HessU_dip_continuous_on
          continuous_on_subset[OF sigma_min_continuous_on subset_UNIV]]
  by (simp add: o_def)

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

subsection \<open>The sets\<close>

definition Xrobust ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> planar \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((planar)^'n) set"
  where
  "Xrobust cvec g ctr \<epsilon> \<kappa> =
     {x. \<forall>\<omega>\<in>sphere ctr \<epsilon>. \<kappa> \<le> norm (gradU cvec g x \<omega>)}"

definition X0 ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> planar \<Rightarrow> (planar) set
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((planar)^'n) set"
  where
  "X0 cvec g ctr \<Omega> \<xi> \<kappa> \<epsilon> =
     {x \<in> Xrobust cvec g ctr \<epsilon> \<kappa>.
        \<forall>y \<in> \<Omega> - ball ctr \<epsilon>. \<xi> \<le> norm (gradU cvec g x y) + sigma_min (HessU cvec g x y)}"

definition F0 ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> planar \<Rightarrow> planar \<Rightarrow> (planar) set \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((planar)^'n) set"
  where
  "F0 cvec g R dmin A B D \<omega>null ctr \<Omega> \<delta>null pmin \<xi> \<kappa> \<epsilon> =
     Ffeas cvec g R dmin A B D \<omega>null ctr \<delta>null pmin
     \<inter> X0 cvec g ctr \<Omega> \<xi> \<kappa> \<epsilon>"

subsection \<open>The angular box without poles\<close>

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

end
