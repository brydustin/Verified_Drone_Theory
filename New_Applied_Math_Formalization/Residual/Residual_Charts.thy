section \<open>Chart maps for the residual\<close>

theory Residual_Charts
  imports
    Residual_Design
begin

text \<open>A chart is given by the two angle functions \<open>th\<close>, \<open>ph\<close> on the
  source space \<open>\<real>\<^sup>N \<times> \<real>\<^sup>N \<ni> (t, w)\<close>.  The map rebuilds the configuration from the phases \<open>t\<close>
  and the perpendicular coordinates, where the \<open>m\<close>-th perpendicular coordinate is solved from
  @{thm design_perp_equation}.  Its image of \<open>{res_f m t = 0}\<close> is covered by countably many
  compact negligible sets.\<close>

subsection \<open>Reconstruction from phase and perpendicular coordinates\<close>

definition tu_param_map :: "real^2 \<Rightarrow> real^'n \<Rightarrow> real^'n \<Rightarrow> (real^2)^'n" where
  "tu_param_map c t u = (\<chi> a. (vec_nth t a / (c \<bullet> c)) *\<^sub>R c + (vec_nth u a / (c \<bullet> c)) *\<^sub>R perp2 c)"

lemma planar_decomposition:
  fixes c v :: "real^2"
  assumes cnz: "c \<noteq> 0"
  shows "((c \<bullet> v) / (c \<bullet> c)) *\<^sub>R c + ((perp2 c \<bullet> v) / (c \<bullet> c)) *\<^sub>R perp2 c = v"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix i :: 2
  have cc: "c \<bullet> c \<noteq> 0"
    using cnz by simp
  have 1: "(c \<bullet> v) * vec_nth c 1 + (perp2 c \<bullet> v) * vec_nth (perp2 c) 1 = (c \<bullet> c) * vec_nth v 1"
    by (simp add: inner2 perp2_nth algebra_simps)
  have 2: "(c \<bullet> v) * vec_nth c 2 + (perp2 c \<bullet> v) * vec_nth (perp2 c) 2 = (c \<bullet> c) * vec_nth v 2"
    by (simp add: inner2 perp2_nth algebra_simps)
  have "vec_nth (((c \<bullet> v) / (c \<bullet> c)) *\<^sub>R c + ((perp2 c \<bullet> v) / (c \<bullet> c)) *\<^sub>R perp2 c) j
      = ((c \<bullet> v) * vec_nth c j + (perp2 c \<bullet> v) * vec_nth (perp2 c) j) / (c \<bullet> c)" for j :: 2
    by (simp add: add_divide_distrib)
  then show "vec_nth (((c \<bullet> v) / (c \<bullet> c)) *\<^sub>R c + ((perp2 c \<bullet> v) / (c \<bullet> c)) *\<^sub>R perp2 c) i = vec_nth v i"
    using 1 2 cc exhaust_2[of i] by auto
qed

lemma tu_param_map_reconstruct:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  assumes cnz: "c \<noteq> 0"
  shows "tu_param_map c (phase_coords c x) (perp_coords c x) = x"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix a :: 'n
  show "vec_nth (tu_param_map c (phase_coords c x) (perp_coords c x)) a = vec_nth x a"
    using planar_decomposition[OF cnz, of "vec_nth x a"]
    by (simp add: tu_param_map_def phase_coords_def perp_coords_def)
qed

subsection \<open>Differentiability tools\<close>

lemma differentiable_sin_real [simp]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "f differentiable (at x)"
  shows "(\<lambda>x. sin (f x)) differentiable (at x)"
proof -
  have "sin differentiable (at (f x))"
    unfolding real_differentiable_def by (blast intro: DERIV_sin)
  then show ?thesis
    by (rule differentiable_compose[OF _ assms])
qed

lemma differentiable_cos_real [simp]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "f differentiable (at x)"
  shows "(\<lambda>x. cos (f x)) differentiable (at x)"
proof -
  have "cos differentiable (at (f x))"
    unfolding real_differentiable_def by (blast intro: DERIV_cos)
  then show ?thesis
    by (rule differentiable_compose[OF _ assms])
qed

lemma differentiable_arccos_real:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "f differentiable (at x)" and "- 1 < f x" and "f x < 1"
  shows "(\<lambda>x. arccos (f x)) differentiable (at x)"
proof -
  have "arccos differentiable (at (f x))"
    unfolding real_differentiable_def using DERIV_arccos[OF assms(2,3)] by blast
  then show ?thesis
    by (rule differentiable_compose[OF _ assms(1)])
qed

lemma differentiable_vec_nth_real [simp]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real^'n"
  assumes "f differentiable (at x)"
  shows "(\<lambda>x. vec_nth (f x) a) differentiable (at x)"
  by (rule differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_vec_nth] assms])

lemma differentiable_fst_snd [simp]:
  "(fst :: 'a::real_normed_vector \<times> 'b::real_normed_vector \<Rightarrow> 'a) differentiable (at z)"
  "(snd :: 'a::real_normed_vector \<times> 'b::real_normed_vector \<Rightarrow> 'b) differentiable (at z)"
  by (simp_all add: bounded_linear_imp_differentiable bounded_linear_fst bounded_linear_snd)

lemma differentiable_res [simp]:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real^'n"
  assumes f: "f differentiable (at x)"
  shows "(\<lambda>x. res_s m (f x)) differentiable (at x)"
    and "(\<lambda>x. res_q m (f x)) differentiable (at x)"
    and "(\<lambda>x. res_W (f x)) differentiable (at x)"
    and "(\<lambda>x. res_P (f x)) differentiable (at x)"
    and "(\<lambda>x. res_f m (f x)) differentiable (at x)"
  unfolding res_s_def res_q_def res_W_def res_P_def res_f_def
    phase_cos_sum_def phase_sin_sum_def phase_lin_cos_sum_def phase_lin_sin_sum_def
  using f by simp_all

lemma differentiable_planar_array:
  fixes Y :: "'a::euclidean_space \<Rightarrow> (real^2)^'n"
  assumes "\<And>a i. (\<lambda>z. vec_nth (vec_nth (Y z) a) i) differentiable (at z)"
  shows "Y differentiable (at z)"
proof (subst differentiable_componentwise_within, intro ballI)
  fix b :: "(real^2)^'n" assume "b \<in> Basis"
  then obtain a and v :: "real^2" where v: "v \<in> Basis" and b: "b = axis a v"
    by (auto simp: Basis_vec_def)
  then obtain i :: 2 where vi: "v = axis i 1"
    by (auto simp: Basis_vec_def)
  have "(\<lambda>z. Y z \<bullet> b) = (\<lambda>z. vec_nth (vec_nth (Y z) a) i)"
    by (simp add: b vi inner_axis)
  then show "(\<lambda>z. Y z \<bullet> b) differentiable (at z)"
    using assms by simp
qed

lemma gdip_nonzero_of_sin: "sin \<theta> \<noteq> 0 \<Longrightarrow> gdip \<theta> \<noteq> 0"
  using gain_dip_nonzero_of_sin[of "vector [\<theta>, 0]"] by (simp add: gain_dip_def)

subsection \<open>The chart map\<close>

definition chart_c1 :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "chart_c1 th ph z = sin (th z) * cos (ph z) + cos (th z) - 1"

definition chart_c2 :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "chart_c2 th ph z = sin (th z) * sin (ph z)"

definition chart_rho :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real" where
  "chart_rho th ph z = frechet_derivative gdip (at (th z)) 1 * sin (ph z) * (cos (th z) - 1)
     / (2 * gdip (th z) * (cos (th z) - sin (th z) * cos (ph z)))"

definition chart_um ::
  "((real^'n) \<times> (real^'n) \<Rightarrow> real) \<Rightarrow> ((real^'n) \<times> (real^'n) \<Rightarrow> real) \<Rightarrow> 'n \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> real" where
  "chart_um th ph m z = (chart_rho th ph z * res_W (fst z)
       - (\<Sum>b\<in>UNIV - {m}. vec_nth (snd z) b * res_s b (fst z))) / res_s m (fst z)"

definition chart_u ::
  "((real^'n) \<times> (real^'n) \<Rightarrow> real) \<Rightarrow> ((real^'n) \<times> (real^'n) \<Rightarrow> real) \<Rightarrow> 'n \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> real^'n" where
  "chart_u th ph m z = (\<chi> b. if b = m then chart_um th ph m z else vec_nth (snd z) b)"

definition chart_map ::
  "((real^'n) \<times> (real^'n) \<Rightarrow> real) \<Rightarrow> ((real^'n) \<times> (real^'n) \<Rightarrow> real) \<Rightarrow> 'n \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> (real^2)^'n" where
  "chart_map th ph m z = tu_param_map (vector [chart_c1 th ph z, chart_c2 th ph z]) (fst z) (chart_u th ph m z)"

definition chart_nondeg ::
  "((real^'n) \<times> (real^'n) \<Rightarrow> real) \<Rightarrow> ((real^'n) \<times> (real^'n) \<Rightarrow> real) \<Rightarrow> 'n \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> real" where
  "chart_nondeg th ph m z = res_s m (fst z)
     * (sin (th z) * (cos (th z) - sin (th z) * cos (ph z))
        * ((chart_c1 th ph z)\<^sup>2 + (chart_c2 th ph z)\<^sup>2))"

lemma chart_map_components:
  "vec_nth (vec_nth (chart_map th ph m z) a) 1
     = (vec_nth (fst z) a * chart_c1 th ph z - vec_nth (chart_u th ph m z) a * chart_c2 th ph z)
       / ((chart_c1 th ph z)\<^sup>2 + (chart_c2 th ph z)\<^sup>2)"
  "vec_nth (vec_nth (chart_map th ph m z) a) 2
     = (vec_nth (fst z) a * chart_c2 th ph z + vec_nth (chart_u th ph m z) a * chart_c1 th ph z)
       / ((chart_c1 th ph z)\<^sup>2 + (chart_c2 th ph z)\<^sup>2)"
  by (simp_all add: chart_map_def tu_param_map_def inner2 perp2_nth power2_eq_square
      add_divide_distrib diff_divide_distrib)

lemma chart_map_differentiable:
  fixes th ph :: "(real^'n) \<times> (real^'n) \<Rightarrow> real"
  assumes dth: "th differentiable (at z)" and dph: "ph differentiable (at z)"
    and nd: "chart_nondeg th ph m z \<noteq> 0"
  shows "chart_map th ph m differentiable (at z)"
proof -
  have s_nz: "res_s m (fst z) \<noteq> 0" and sin_nz: "sin (th z) \<noteq> 0"
    and d_nz: "cos (th z) - sin (th z) * cos (ph z) \<noteq> 0"
    and q_nz: "(chart_c1 th ph z)\<^sup>2 + (chart_c2 th ph z)\<^sup>2 \<noteq> 0"
    using nd unfolding chart_nondeg_def by auto
  have g_nz: "gdip (th z) \<noteq> 0"
    by (rule gdip_nonzero_of_sin[OF sin_nz])
  have dg: "(\<lambda>z. gdip (th z)) differentiable (at z)"
    by (rule differentiable_compose[OF gdip_differentiable dth])
  have dgd: "(\<lambda>z. frechet_derivative gdip (at (th z)) 1) differentiable (at z)"
    by (rule differentiable_compose[OF gdip_deriv_differentiable dth])
  have dc1: "chart_c1 th ph differentiable (at z)"
    unfolding chart_c1_def[abs_def] using dth dph by simp
  have dc2: "chart_c2 th ph differentiable (at z)"
    unfolding chart_c2_def[abs_def] using dth dph by simp
  have drho: "chart_rho th ph differentiable (at z)"
    unfolding chart_rho_def[abs_def] using dth dph dg dgd g_nz d_nz by simp
  have dum: "chart_um th ph m differentiable (at z)"
    unfolding chart_um_def[abs_def] using drho s_nz by simp
  have du: "(\<lambda>z. vec_nth (chart_u th ph m z) a) differentiable (at z)" for a
  proof (cases "a = m")
    case True
    then have "(\<lambda>z. vec_nth (chart_u th ph m z) a) = chart_um th ph m"
      by (simp add: chart_u_def)
    then show ?thesis
      using dum by simp
  next
    case False
    then have "(\<lambda>z. vec_nth (chart_u th ph m z) a) = (\<lambda>z. vec_nth (snd z) a)"
      by (simp add: chart_u_def)
    then show ?thesis
      by simp
  qed
  show ?thesis
  proof (rule differentiable_planar_array)
    fix a :: 'n and i :: 2
    show "(\<lambda>z. vec_nth (vec_nth (chart_map th ph m z) a) i) differentiable (at z)"
      using exhaust_2[of i] dc1 dc2 du[of a] q_nz
      by (auto simp: chart_map_components)
  qed
qed

subsection \<open>The image of the zero set of \<open>res_f\<close>\<close>

theorem chart_image_cover:
  fixes th ph :: "(real^'n) \<times> (real^'n) \<Rightarrow> real" and Dom :: "((real^'n) \<times> (real^'n)) set" and m :: 'n
  assumes op: "open Dom"
    and dth: "\<And>z. z \<in> Dom \<Longrightarrow> th differentiable (at z)"
    and dph: "\<And>z. z \<in> Dom \<Longrightarrow> ph differentiable (at z)"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      chart_map th ph m ` {z \<in> Dom. chart_nondeg th ph m z \<noteq> 0 \<and> res_f m (fst z) = 0} \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  define D where "D = {z \<in> Dom. chart_nondeg th ph m z \<noteq> 0}"
  define S where "S = {z \<in> D. res_f m (fst z) = 0}"
  have "chart_nondeg th ph m differentiable (at z)" if "z \<in> Dom" for z
    unfolding chart_nondeg_def[abs_def] chart_c1_def chart_c2_def
    using dth[OF that] dph[OF that] by simp
  then have "continuous_on Dom (chart_nondeg th ph m)"
    by (intro differentiable_imp_continuous_on differentiable_at_imp_differentiable_on)
  then have "open (chart_nondeg th ph m -` (- {0}) \<inter> Dom)"
    using continuous_on_open_vimage[OF op] by blast
  moreover have "D = chart_nondeg th ph m -` (- {0}) \<inter> Dom"
    by (auto simp: D_def)
  ultimately have openD: "open D"
    by simp
  have diffD: "chart_map th ph m differentiable (at z)" if "z \<in> D" for z
    using that unfolding D_def by (auto intro: chart_map_differentiable dth dph)
  have diff_on: "chart_map th ph m differentiable_on D"
    by (rule differentiable_at_imp_differentiable_on) (rule diffD)

  text \<open>The set \<open>S\<close> is negligible, hence so is its image.\<close>
  have "S \<subseteq> {t. res_s m t \<noteq> 0 \<and> res_f m t = 0} \<times> UNIV"
    by (auto simp: S_def D_def chart_nondeg_def)
  moreover have "negligible ({t :: real^'n. res_s m t \<noteq> 0 \<and> res_f m t = 0} \<times> (UNIV :: (real^'n) set))"
    by (rule negligible_Times_UNIV[OF res_f_zeros_borel negligible_res_f_zeros])
  ultimately have negS: "negligible S"
    by (rule negligible_subset[rotated])
  have dim: "DIM((real^'n) \<times> (real^'n)) \<le> DIM((real^2)^'n)"
    by simp
  have neg_image: "negligible (chart_map th ph m ` S)"
    by (rule negligible_differentiable_image_negligible[OF dim negS])
       (rule differentiable_on_subset[OF diff_on], auto simp: S_def)

  text \<open>Compact pieces.\<close>
  obtain C :: "nat \<Rightarrow> ((real^'n) \<times> (real^'n)) set"
    where Ccompact: "\<And>n. compact (C n)" and CD: "\<And>n. C n \<subseteq> D" and Cunion: "(\<Union>n. C n) = D"
    using open_sigma_compact_exhaustion[OF openD] by metis
  define Z where "Z = {z :: (real^'n) \<times> (real^'n). res_f m (fst z) = 0}"
  have "continuous_on UNIV (\<lambda>z :: (real^'n) \<times> (real^'n). res_f m (fst z))"
    by (rule continuous_on_compose2[OF continuous_on_res_f continuous_on_fst[OF continuous_on_id]]) simp
  then have closedZ: "closed Z"
    unfolding Z_def by (rule closed_Collect_eq[OF _ continuous_on_const])
  define K where "K n = chart_map th ph m ` (C n \<inter> Z)" for n
  have "closed (K n)" for n
  proof -
    have "compact (C n \<inter> Z)"
      by (rule compact_Int_closed[OF Ccompact closedZ])
    moreover have "continuous_on (C n \<inter> Z) (chart_map th ph m)"
      by (rule differentiable_imp_continuous_on[OF differentiable_on_subset[OF diff_on]])
         (use CD in auto)
    ultimately have "compact (K n)"
      unfolding K_def by (rule compact_continuous_image[rotated])
    then show ?thesis
      by (rule compact_imp_closed)
  qed
  moreover have "negligible (K n)" for n
  proof (rule negligible_subset[OF neg_image])
    show "K n \<subseteq> chart_map th ph m ` S"
      using CD by (auto simp: K_def S_def Z_def)
  qed
  moreover have "chart_map th ph m ` S \<subseteq> (\<Union>n. K n)"
  proof
    fix y assume "y \<in> chart_map th ph m ` S"
    then obtain z where z: "z \<in> S" and y: "y = chart_map th ph m z"
      by blast
    then have "z \<in> D" and "z \<in> Z"
      by (simp_all add: S_def Z_def)
    then obtain n where "z \<in> C n"
      using Cunion by blast
    then show "y \<in> (\<Union>n. K n)"
      using \<open>z \<in> Z\<close> y by (auto simp: K_def)
  qed
  moreover have "{z \<in> Dom. chart_nondeg th ph m z \<noteq> 0 \<and> res_f m (fst z) = 0} = S"
    by (auto simp: S_def D_def)
  ultimately show ?thesis
    by auto
qed

end
