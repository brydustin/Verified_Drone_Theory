theory Nonemptiness_Paper
  imports
    Parametric_Transversality_Euclidean
    Nonemptiness_Array_Factor
    Nonemptiness_Feasibility
    Nonemptiness_Spine
begin

text \<open>
  Working file for the formalization of
   \<open>../Applied Math/nonemptiness_unified_singlefile_complete.tex\<close>.

  This theory is intentionally organized in the same order as the TeX document.
  The rule is: prove each lemma/proposition before using it later.

  We keep the closeout lemma separate (it is already proved in
   Nonemptiness_Spine as \<open>nonemptiness_from_meager_branches\<close>.
\<close>


section \<open>Setup\<close>

text \<open>
  TeX Section 2 defines: \<open>k\<close>, \<open>\<Delta>k\<close>, \<open>D\<^sub>x,D\<^sub>y\<close>, \<open>cvec\<close>, and the pattern
  \<open>U(x,\<omega>) = g(\<omega>) * |A(x,\<omega>)|^2\<close>.

  This has not yet been mirrored fully in Isabelle; currently we have a generic
  \<open>cvec\<close> and \<open>array factor\<close> layer in theory Nonemptiness_Array_Factor.
\<close>

subsection \<open>Concrete Carriers Used in the Proof\<close>

type_synonym angle = "real^2"   (* (theta, phi) as a 2-vector *)
type_synonym planar = "real^2"

definition A_cart ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> complex"
where
  "A_cart cvec x \<omega> = (\<Sum>n\<in>UNIV. cis (-(cvec \<omega> \<bullet> (x $ n))))"

definition U_cart ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> real"
where
  "U_cart cvec g x \<omega> = g \<omega> * (cmod (A_cart cvec x \<omega>))\<^sup>2"


section \<open>Open Feasible Family and Two-Triple Cover\<close>

subsection \<open>Proposition: Open Feasible Family (Constructive Core)\<close>

text \<open>
  The TeX proof of Proposition~(Open feasible family) has two parts:
  \<^item> an explicit configuration with exact nulling at \<open>\<omega>\<^sub>N\<close> (root-of-unity construction);
  \<^item> a continuity argument that an open neighborhood preserves strict inequalities
    (spacing and null bound).

  We formalize the first part now. The second part is packaged abstractly in
  Nonemptiness_Feasibility and will be instantiated later.
\<close>

lemma root_of_unity_nulling:
  fixes c :: planar and q s :: planar and L :: real
  assumes "N > 1"
    and cq: "c \<bullet> q = 1"
    and cs: "c \<bullet> s = 0"
  defines "p n \<equiv> (2*pi*real n/real N) *\<^sub>R q + (real (Suc n) * L) *\<^sub>R s"
  shows "(\<Sum>n<N. cis (-(c \<bullet> p n))) = 0"
proof -
  have sum_cis_roots_unity: "(\<Sum>n<N. cis (2*pi*real n/real N)) = 0"
  proof -
    define \<omega> where "\<omega> = cis (2 * pi / real N)"
    have deMoivre_local: "(cis a :: complex) ^ m = cis (real m * a)" for a m
      by (induction m) (simp_all add: algebra_simps cis_mult)
    have [simp]: "\<omega> \<noteq> 1"
    proof
      assume h: "\<omega> = 1"
      from h assms obtain k :: int where hk: "2 * pi / real N = 2 * pi * of_int k"
        by (auto simp: \<omega>_def complex_eq_iff cos_one_2pi_int mult_ac)
      from hk assms have "real N * of_int k = 1"
        by (simp add: field_simps)
      then have "of_int (int N * k) = (1::real)"
        by simp
      then have "int N * k = 1"
        using of_int_eq_iff by blast
      then have "int N = 1"
        by (auto simp: zmult_eq_1_iff)
      then show False
        using assms by simp
    qed

    have "(\<Sum>n<N. cis (2*pi*real n/real N)) = (\<Sum>n<N. \<omega> ^ n)"
    proof (rule sum.cong[OF refl])
      fix n assume "n \<in> {..<N}"
      have "cis (2*pi*real n/real N) = cis (real n * (2*pi/real N))"
        by (simp add: mult_ac)
      also have "\<dots> = (cis (2*pi/real N)) ^ n"
      proof -
        have hpow: "(cis (2*pi/real N) :: complex) ^ n = cis (real n * (2*pi/real N))"
          by (rule deMoivre_local)
        show ?thesis
          using hpow by simp
      qed
      finally show "cis (2*pi*real n/real N) = \<omega> ^ n"
        by (simp add: \<omega>_def)
    qed
    also have "\<dots> = (\<omega> ^ N - 1) / (\<omega> - 1)"
      by (subst geometric_sum[OF \<open>\<omega> \<noteq> 1\<close>]) simp
    also have "\<omega> ^ N - 1 = cis (2 * pi) - 1"
      using assms by (simp add: \<omega>_def deMoivre_local field_simps)
    also have "\<dots> = 0"
      by (simp add: complex_eq_iff)
    finally show ?thesis
      by simp
  qed
  have "c \<bullet> p n = 2*pi*real n/real N" for n
    by (simp only: p_def inner_add_right inner_scaleR_right cq cs)
  then have "(\<Sum>n<N. cis (-(c \<bullet> p n))) = (\<Sum>n<N. cis (-(2*pi*real n/real N)))"
    by simp
  also have "\<dots> = 0"
  proof -
    have "(\<Sum>n<N. cis (-(2*pi*real n/real N))) = (\<Sum>n<N. cnj (cis (2*pi*real n/real N)))"
      by (simp add: cis_cnj)
    also have "\<dots> = cnj (\<Sum>n<N. cis (2*pi*real n/real N))"
      by (simp only: cnj_sum)
    also have "\<dots> = 0"
      using sum_cis_roots_unity by simp
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

theorem prop_openfeas:
  fixes cvec :: "angle \<Rightarrow> planar" and \<omega>N :: angle
  assumes "N > 1" and "cvec \<omega>N \<noteq> 0"
  shows "\<exists>ps::planar list. length ps = N \<and> array_factor cvec ps \<omega>N = 0"
proof -
  obtain q s :: planar
    where cq: "cvec \<omega>N \<bullet> q = 1" and cs: "cvec \<omega>N \<bullet> s = 0"
    by (meson assms(2) hyperplane_eq_Ex)
  define L :: real where "L = 1"
  define p where "p n = (2*pi*real n/real N) *\<^sub>R q + (real (Suc n) * L) *\<^sub>R s" for n
  define ps where "ps = map p [0..<N]"

  have hlen: "length ps = N"
    by (simp add: ps_def)

  have hsum: "(\<Sum>n<N. cis (-(cvec \<omega>N \<bullet> p n))) = 0"
    using root_of_unity_nulling[OF assms(1) cq cs, of L] by (simp add: p_def)

  have "array_factor cvec ps \<omega>N = 0"
  proof -
    have "array_factor cvec ps \<omega>N = sum_list (map (\<lambda>x. cis (-(cvec \<omega>N \<bullet> x))) ps)"
      by (simp add: array_factor_def)
    also have "\<dots> = sum_list (map (\<lambda>n. cis (-(cvec \<omega>N \<bullet> p n))) [0..<N])"
      by (simp add: ps_def o_def)
    also have "\<dots> = sum (\<lambda>n. cis (-(cvec \<omega>N \<bullet> p n))) (set [0..<N])"
      by (simp add: interv_sum_list_conv_sum_set_nat)
    also have "\<dots> = (\<Sum>n<N. cis (-(cvec \<omega>N \<bullet> p n)))"
      by (simp add: atLeast0LessThan)
    also have "\<dots> = 0"
      by (rule hsum)
    finally show ?thesis.
  qed

  then show ?thesis
    using hlen by (intro exI[of _ ps], blast)
qed

text \<open>
  The combinatorial heart of the two-triple cover (TeX Lemma~(Two-triple cover)).
  For a noncollinear triple \<open>T\<close> the set \<open>B(T) \<subseteq> S\<^sup>1\<close> of directions orthogonal to an
  edge is finite. Rotating the second triple by \<open>\<alpha>\<close> sends \<open>B(T\<^sub>2)\<close> to \<open>B(T\<^sub>2)+\<alpha>\<close>; the
  "bad" rotations are the finite set \<open>{\<beta>-\<gamma> : \<beta>\<in>B(T\<^sub>1), \<gamma>\<in>B(T\<^sub>2)}\<close>. Choosing \<open>\<alpha>\<close>
  outside it makes \<open>B(T\<^sub>1)\<close> and \<open>B(T\<^sub>2)+\<alpha>\<close> disjoint, so every direction is good for at
  least one triple. We prove this avoidance fact; the geometric packaging of the
  triples and the working set \<open>V\<close> is downstream openness.
\<close>

lemma lem_twotriplecover:
  fixes B1 B2 :: "real set"
  assumes "finite B1" and "finite B2"
  shows "\<exists>\<alpha>. \<forall>\<beta>\<in>B1. \<forall>\<gamma>\<in>B2. \<beta> \<noteq> \<gamma> + \<alpha>"
proof -
  have "finite ((\<lambda>(\<beta>, \<gamma>). \<beta> - \<gamma>) ` (B1 \<times> B2))"
    using assms by simp
  then obtain \<alpha> where "\<alpha> \<notin> (\<lambda>(\<beta>, \<gamma>). \<beta> - \<gamma>) ` (B1 \<times> B2)"
    using ex_new_if_finite[OF infinite_UNIV_char_0] by blast
  then show ?thesis by force
qed


section \<open>Global Lemma for @{term "cvec = 0"}\<close>

text \<open>
  The norm-comparison core of the TeX argument: a point \<open>c\<close> on a sphere lying on the
  secant line through two sphere points \<open>a \<noteq> b\<close>, \<open>c = b + \<alpha>(a - b)\<close>, must be one of
  the endpoints (\<open>\<alpha> \<in> {0,1}\<close>). In the paper this yields \<open>\<alpha>(1-\<alpha>)|k(\<omega>\<^sub>0)-k(\<omega>\<^sub>s)|\<^sup>2 = 0\<close>,
  hence \<open>k(\<omega>) \<in> {k(\<omega>\<^sub>0), k(\<omega>\<^sub>s)}\<close>.
\<close>

lemma secant_sphere:
  fixes a b c :: "'a::real_inner" and \<rho> \<alpha> :: real
  assumes na: "norm a = \<rho>" and nb: "norm b = \<rho>" and nc: "norm c = \<rho>"
    and hc: "c = b + \<alpha> *\<^sub>R (a - b)" and hab: "a \<noteq> b"
  shows "\<alpha> = 0 \<or> \<alpha> = 1"
proof -
  have expand: "\<And>t::real. (norm (b + t *\<^sub>R (a - b)))\<^sup>2
                  = (norm b)\<^sup>2 + 2*t*(b \<bullet> (a - b)) + t\<^sup>2 * (norm (a - b))\<^sup>2"
    by (simp only: power2_norm_eq_inner)
       (simp only: inner_add_left inner_add_right inner_scaleR_left inner_scaleR_right
                  inner_diff_left inner_diff_right inner_commute power2_eq_square)
  have anz: "a - b \<noteq> 0" using hab by simp
  then have nz: "(norm (a - b))\<^sup>2 > 0" by simp
  have hF1: "2*\<alpha>*(b \<bullet> (a - b)) + \<alpha>\<^sup>2 * (norm (a - b))\<^sup>2 = 0"
  proof -
    have "(norm c)\<^sup>2 = (norm b)\<^sup>2 + 2*\<alpha>*(b \<bullet> (a - b)) + \<alpha>\<^sup>2 * (norm (a - b))\<^sup>2"
      using hc expand[of \<alpha>] by simp
    then show ?thesis using na nb nc by simp
  qed
  have hF2: "2*(b \<bullet> (a - b)) + (norm (a - b))\<^sup>2 = 0"
  proof -
    have "(norm a)\<^sup>2 = (norm (b + 1 *\<^sub>R (a - b)))\<^sup>2" by simp
    also have "\<dots> = (norm b)\<^sup>2 + 2*(b \<bullet> (a - b)) + (norm (a - b))\<^sup>2"
      using expand[of 1] by simp
    finally show ?thesis using na nb by simp
  qed
  have "(\<alpha>\<^sup>2 - \<alpha>) * (norm (a - b))\<^sup>2
          = (2*\<alpha>*(b \<bullet> (a - b)) + \<alpha>\<^sup>2 * (norm (a - b))\<^sup>2)
            - \<alpha> * (2*(b \<bullet> (a - b)) + (norm (a - b))\<^sup>2)"
    by (simp add: algebra_simps)
  also have "\<dots> = 0" using hF1 hF2 by simp
  finally have "(\<alpha>\<^sup>2 - \<alpha>) * (norm (a - b))\<^sup>2 = 0" .
  with nz have "\<alpha>\<^sup>2 - \<alpha> = 0" by simp
  then have "\<alpha> * (\<alpha> - 1) = 0" by (simp only: power2_eq_square algebra_simps)
  then show ?thesis by simp
qed

text \<open>
  The 3-D wavevector \<open>k(\<omega>) = (sin\<theta> cos\<phi>, sin\<theta> sin\<phi>, cos\<theta>)\<close> (unit-normalized; the
  physical scale \<open>2\<pi>/\<lambda>\<close> is irrelevant to vanishing of \<open>cvec\<close>), modeled as a real
  triple so its components are plain projections. The planar effective wavevector
  \<open>cvec\<^sub>0\<close> is the paper's \<open>(\<Delta>k\<^sub>x + D\<^sub>x \<Delta>k\<^sub>z, \<Delta>k\<^sub>y + D\<^sub>y \<Delta>k\<^sub>z)\<close> with beam-lift constants
  \<open>D\<^sub>x = (k\<^sub>x(\<omega>\<^sub>0)-k\<^sub>x(\<omega>\<^sub>s))/(k\<^sub>z(\<omega>\<^sub>s)-k\<^sub>z(\<omega>\<^sub>0))\<close>, similarly \<open>D\<^sub>y\<close>.
\<close>

type_synonym wavevec = "real \<times> real \<times> real"

definition kx :: "angle \<Rightarrow> real" where "kx \<omega> = sin (\<omega>$1) * cos (\<omega>$2)"
definition ky :: "angle \<Rightarrow> real" where "ky \<omega> = sin (\<omega>$1) * sin (\<omega>$2)"
definition kz :: "angle \<Rightarrow> real" where "kz \<omega> = cos (\<omega>$1)"

definition kvec :: "angle \<Rightarrow> wavevec" where
  "kvec \<omega> = (kx \<omega>, ky \<omega>, kz \<omega>)"

lemma norm_kvec [simp]: "norm (kvec \<omega>) = 1"
proof -
  have s1: "(sin (\<omega>$1))\<^sup>2 = 1 - (cos (\<omega>$1))\<^sup>2"
    using sin_cos_squared_add[of "\<omega>$1"] by (metis add_diff_cancel_right')
  have s2: "(sin (\<omega>$2))\<^sup>2 = 1 - (cos (\<omega>$2))\<^sup>2"
    using sin_cos_squared_add[of "\<omega>$2"] by (metis add_diff_cancel_right')
  have "inner (kvec \<omega>) (kvec \<omega>) = (kx \<omega>)\<^sup>2 + (ky \<omega>)\<^sup>2 + (kz \<omega>)\<^sup>2"
    by (simp add: kvec_def inner_prod_def power2_eq_square)
  also have "\<dots> = 1"
    unfolding kx_def ky_def kz_def
    by (simp only: s1 s2 algebra_simps)
  finally have "inner (kvec \<omega>) (kvec \<omega>) = 1" .
  then have "(norm (kvec \<omega>))\<^sup>2 = 1"
    by (simp add: power2_norm_eq_inner)
  then show ?thesis
    using norm_ge_zero[of "kvec \<omega>"] by (auto simp: power2_eq_1_iff)
qed

definition cvec0 :: "angle \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> real \<times> real" where
  "cvec0 \<omega>0 \<omega>s \<omega> =
     ( (kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s),
       (ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s) )"

theorem lem_czero:
  fixes \<omega>0 \<omega>s \<omega> :: angle
  assumes hsep: "kz \<omega>0 \<noteq> kz \<omega>s"
    and hz: "cvec0 \<omega>0 \<omega>s \<omega> = (0, 0)"
  shows "kvec \<omega> = kvec \<omega>0 \<or> kvec \<omega> = kvec \<omega>s"
proof -
  define az where "az = kz \<omega>0 - kz \<omega>s"
  have az0: "az \<noteq> 0" using hsep by (simp add: az_def)
  have den0: "kz \<omega>s - kz \<omega>0 \<noteq> 0" using az0 by (simp add: az_def)
  have hz1: "(kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s) = 0"
    using hz by (simp add: cvec0_def)
  have hz2: "(ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s) = 0"
    using hz by (simp add: cvec0_def)
  define al where "al = (kz \<omega> - kz \<omega>s) / az"
  have X: "kx \<omega> - kx \<omega>s = al * (kx \<omega>0 - kx \<omega>s)"
    using hz1 az0 den0 by (simp add: al_def az_def field_simps)
  have Y: "ky \<omega> - ky \<omega>s = al * (ky \<omega>0 - ky \<omega>s)"
    using hz2 az0 den0 by (simp add: al_def az_def field_simps)
  have Z: "kz \<omega> - kz \<omega>s = al * (kz \<omega>0 - kz \<omega>s)"
    using az0 by (simp add: al_def az_def)
  have key: "kvec \<omega> = kvec \<omega>s + al *\<^sub>R (kvec \<omega>0 - kvec \<omega>s)"
    using X Y Z by (simp add: kvec_def prod_eq_iff algebra_simps)
  have hne: "kvec \<omega>0 \<noteq> kvec \<omega>s"
    using az0 by (auto simp: kvec_def az_def)
  from secant_sphere[OF norm_kvec norm_kvec norm_kvec key hne]
  have "al = 0 \<or> al = 1" .
  then show ?thesis
  proof
    assume "al = 0"
    then show ?thesis using key by simp
  next
    assume "al = 1"
    then show ?thesis using key by (simp add: algebra_simps)
  qed
qed


section \<open>Regular-Stratum Zeros of the Array Factor\<close>

theorem lem_Azero_surj:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes "odd CARD('n)" "cvec \<omega> \<noteq> 0" "af cvec x \<omega> = 0"
  shows "\<exists>h. dxA cvec x \<omega> h = 1"
  using dxA_surj[OF assms, of 1] .

subsection \<open>Transversality Predicate (Minimal)\<close>

definition transverse0_on ::
  "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "transverse0_on f S \<longleftrightarrow>
     (\<forall>x\<in>S. f x = 0 \<longrightarrow> (\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f'))"

lemma surj_comp:
  assumes "surj f" and "surj g"
  shows "surj (g \<circ> f)"
  using assms unfolding surj_def
  by (metis comp_apply) 

lemma has_derivative_cplx_r2_within:
  fixes z :: complex
  shows "(cplx_r2 has_derivative cplx_r2) (at z within S)"
  by (simp add: has_derivative_at_withinI has_derivative_cplx_r2)

definition r2_cplx :: "real^2 \<Rightarrow> complex" where
  "r2_cplx v = Complex (v $ 1) (v $ 2)"

lemma r2_cplx_cplx_r2 [simp]: "r2_cplx (cplx_r2 z) = z"
  unfolding r2_cplx_def cplx_r2_def
  by (simp add: complex_eq_iff vec_eq_iff forall_2)

lemma cplx_r2_r2_cplx [simp]: "cplx_r2 (r2_cplx v) = v"
  unfolding r2_cplx_def cplx_r2_def
  by (simp add: vec_eq_iff forall_2)

lemma bounded_linear_r2_cplx: "bounded_linear r2_cplx"
  unfolding r2_cplx_def
  by (intro bounded_linearI')
     (simp_all add: vec_eq_iff forall_2 complex_eq_iff)

lemma has_derivative_r2_cplx [derivative_intros]:
  fixes v :: "real^2"
  shows "(r2_cplx has_derivative r2_cplx) (at v)"
  by (simp only: bounded_linear_r2_cplx bounded_linear_imp_has_derivative)

lemma surj_r2_cplx: "surj r2_cplx"
  by (metis UNIV_eq_I r2_cplx_cplx_r2 rangeI)

lemma regular_value_on_cplx_r2_comp:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
  shows "regular_value_on (\<lambda>z. cplx_r2 (A z)) (V\<times>\<Omega>reg) 0"
proof (rule regular_value_onI)
  fix z
  assume zS: "z \<in> V \<times> \<Omega>reg"
  assume hz: "(\<lambda>z. cplx_r2 (A z)) z = 0"
  then have Az0: "A z = 0"
    by (simp only: cplx_r2_0_iff)
  from joint_trans zS Az0 obtain F where
    derA: "((\<lambda>z. A z) has_derivative F) (at z within V \<times> \<Omega>reg)"
    and surjF: "surj F"
    by blast
  have derc: "(cplx_r2 has_derivative cplx_r2) (at (A z) within UNIV)"
    by (simp add: has_derivative_cplx_r2)
  have derG:
      "((\<lambda>z. cplx_r2 (A z)) has_derivative (cplx_r2 \<circ> F)) (at z within V \<times> \<Omega>reg)"
    using has_derivative_compose[OF derA derc]
    by (simp add: o_def)
  have "surj (cplx_r2 \<circ> F)"
    by (rule surj_comp[OF surjF surj_cplx_r2])
  then show "\<exists>f'. ((\<lambda>z. cplx_r2 (A z)) has_derivative f') (at z within V \<times> \<Omega>reg) \<and> surj f'"
    using derG by blast
qed

lemma transverse0_on_cplx_r2_iff:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  shows "transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg \<longleftrightarrow>
         transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg"
  unfolding transverse0_on_def
proof
  assume H: "\<forall>\<omega>\<in>\<Omega>reg.
      cplx_r2 (A (x, \<omega>)) = 0 \<longrightarrow>
      (\<exists>f'. ((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f')"
  show "\<forall>\<omega>\<in>\<Omega>reg.
      A (x, \<omega>) = 0 \<longrightarrow>
      (\<exists>f'. ((\<lambda>\<omega>. A (x, \<omega>)) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f')"
  proof (intro ballI impI)
    fix \<omega> :: "real^2"
    assume w: "\<omega> \<in> \<Omega>reg"
    assume Az0: "A (x, \<omega>) = 0"
    have "cplx_r2 (A (x, \<omega>)) = 0"
      using Az0 by (simp only: cplx_r2_0_iff)
	    then obtain f' where der:
	        "((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative f') (at \<omega> within \<Omega>reg)"
	      and surj_f': "surj f'"
	      using H w by blast
            have der_r2: "(r2_cplx has_derivative r2_cplx) (at (cplx_r2 (A (x, \<omega>))) within UNIV)"
              by (simp add: has_derivative_at_withinI has_derivative_r2_cplx)
            have derA:
                "((\<lambda>\<omega>. A (x, \<omega>)) has_derivative (r2_cplx \<circ> f')) (at \<omega> within \<Omega>reg)"
              using has_derivative_compose[OF der der_r2]
              by (simp add: o_def)
            have surjF: "surj (r2_cplx \<circ> f')"
              by (rule surj_comp[OF surj_f' surj_r2_cplx])
	    show "\<exists>f'. ((\<lambda>\<omega>. A (x, \<omega>)) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f'"
	      using derA surjF by blast
	  qed
next
  assume H: "\<forall>\<omega>\<in>\<Omega>reg.
      A (x, \<omega>) = 0 \<longrightarrow>
      (\<exists>f'. ((\<lambda>\<omega>. A (x, \<omega>)) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f')"
  show "\<forall>\<omega>\<in>\<Omega>reg.
      cplx_r2 (A (x, \<omega>)) = 0 \<longrightarrow>
      (\<exists>f'. ((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f')"
  proof (intro ballI impI)
    fix \<omega> :: "real^2"
    assume w: "\<omega> \<in> \<Omega>reg"
    assume hz: "cplx_r2 (A (x, \<omega>)) = 0"
    then have Az0: "A (x, \<omega>) = 0"
      by (simp only: cplx_r2_0_iff)
    from H w Az0 obtain F where derA:
        "((\<lambda>\<omega>. A (x, \<omega>)) has_derivative F) (at \<omega> within \<Omega>reg)"
      and surjF: "surj F"
      by blast
    have derc: "(cplx_r2 has_derivative cplx_r2) (at (A (x, \<omega>)) within UNIV)"
      by (simp add: has_derivative_cplx_r2)
    have derG:
        "((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative (cplx_r2 \<circ> F)) (at \<omega> within \<Omega>reg)"
      using has_derivative_compose[OF derA derc] by (simp add: o_def)
    have "surj (cplx_r2 \<circ> F)"
      by (rule surj_comp[OF surjF surj_cplx_r2])
    then show "\<exists>f'. ((\<lambda>\<omega>. cplx_r2 (A (x, \<omega>))) has_derivative f') (at \<omega> within \<Omega>reg) \<and> surj f'"
      using derG by blast
  qed
qed


text \<open>
  The Euclidean chart pipeline in \<open>Parametric_Transversality_Euclidean_Base\<close>
  is typed for a \<^emph>\<open>single-level\<close> parameter space \<open>real^'m\<close>, and records the
  rank defect as \<open>rank (matrix \<dots>) < CARD('m)\<close> --- which only type-checks for
  \<open>real^'m\<close> (the entries must form a \<^class>\<open>field\<close>). Here the parameter space is the
  product \<open>(real^2)^'n\<close>, so we record the two pipeline obligations at that type, with
  the rank defect expressed coordinate-free as \<open>\<not> surj\<close>. These are the genuine
  (still-open) analytic obligations for the antenna parameter space; they will be
  discharged from the general regular-value theorem.
\<close>

lemma charts_core_Nn:
  fixes V :: "((real^2)^'n) set" and \<Omega> :: "(real^2) set"
    and G :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^2)"
  assumes "open V" "V \<noteq> {}" "open \<Omega>"
    and "regular_value_on G (V\<times>\<Omega>) 0"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
             (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
           \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  sorry

text \<open>
  Sard for the antenna parameter space. \<open>baby_Sard\<close> is hard-typed to
  \<open>real^'m \<Rightarrow> real^'n\<close> (it uses \<^const>\<open>matrix\<close>/\<^const>\<open>rank\<close>), but our parameter
  space is the \<^emph>\<open>nested\<close> vector \<open>(real^2)^'n\<close>. Since \<open>(real^2)^'n\<close> has dimension
  \<open>2 * CARD('n)\<close>, the flat vector type of equal cardinality and the required
  \<^class>\<open>wellorder\<close> sort is \<open>real^('n bit0)\<close>. We build a linear isomorphism
  \<open>\<Phi> : (real^2)^'n \<cong> real^('n bit0)\<close> (from some index bijection, which exists by
  equal cardinality), transport the map through it, apply \<open>baby_Sard\<close>, and
  push negligibility back with \<open>negligible_locally_Lipschitz_image\<close>.
\<close>

lemma card_n2_bit0:
  "card (UNIV :: ('n::finite \<times> 2) set) = card (UNIV :: ('n bit0) set)"
  by simp

lemma exists_index_bij:
  "\<exists>\<beta> :: 'n::finite bit0 \<Rightarrow> ('n \<times> 2). bij \<beta>"
proof -
  have "card (UNIV :: ('n bit0) set) = card (UNIV :: ('n \<times> 2) set)"
    by (simp add: card_n2_bit0)
  then show ?thesis
    by (metis finite_same_card_bij finite_class.finite_UNIV)
qed

lemma negligible_singular_image_2n:
  fixes f :: "(real^2)^'n \<Rightarrow> (real^2)^'n"
    and f' :: "(real^2)^'n \<Rightarrow> ((real^2)^'n \<Rightarrow> (real^2)^'n)"
  assumes der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
      and ns:  "\<And>x. x \<in> S \<Longrightarrow> \<not> surj (f' x)"
  shows "negligible (f ` S)"
proof -
  obtain \<beta> :: "'n bit0 \<Rightarrow> ('n \<times> 2)" where b: "bij \<beta>"
    using exists_index_bij by blast
  define \<gamma> where "\<gamma> = inv \<beta>"
  have g\<beta>: "\<gamma> (\<beta> k) = k" for k unfolding \<gamma>_def
    by (metis b bij_inv_eq_iff)
  have \<beta>g: "\<beta> (\<gamma> p) = p" for p unfolding \<gamma>_def by (meson b bij_inv_eq_iff)

  define \<Phi> :: "(real^2)^'n \<Rightarrow> real^('n bit0)"
    where "\<Phi> v = (\<chi> k. (v $ fst (\<beta> k)) $ snd (\<beta> k))" for v
  define \<Psi> :: "real^('n bit0) \<Rightarrow> (real^2)^'n"
    where "\<Psi> w = (\<chi> i. \<chi> j. w $ \<gamma> (i,j))" for w

  have lin\<Phi>: "linear \<Phi>"
    by (rule linearI) (auto simp: \<Phi>_def vec_eq_iff)
  have lin\<Psi>: "linear \<Psi>"
    by (rule linearI) (auto simp: \<Psi>_def vec_eq_iff)

  have \<Psi>\<Phi>: "\<Psi> (\<Phi> v) = v" for v
    by (simp add: \<Phi>_def \<Psi>_def vec_eq_iff \<beta>g)
  have \<Phi>\<Psi>: "\<Phi> (\<Psi> w) = w" for w
    by (simp add: \<Phi>_def \<Psi>_def vec_eq_iff g\<beta>)

  define h :: "real^('n bit0) \<Rightarrow> real^('n bit0)"
    where "h = (\<lambda>y. \<Phi> (f (\<Psi> y)))"

  have der_h:
    "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow>
      (h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
  proof -
    fix y assume yS: "y \<in> \<Phi> ` S"
    have \<Psi>yS: "\<Psi> y \<in> S" using yS \<Psi>\<Phi> by auto
    have d\<Psi>: "(\<Psi> has_derivative \<Psi>) (at y within \<Phi> ` S)"
      using lin\<Psi> by (simp add: linear_imp_has_derivative)
    have df: "(f has_derivative f' (\<Psi> y)) (at (\<Psi> y) within \<Psi> ` (\<Phi> ` S))"
      by (metis (mono_tags, lifting) \<Psi>\<Phi> \<Psi>yS der has_derivative_subset image_iff image_subsetI)
    have d_f\<Psi>:
      "((\<lambda>y. f (\<Psi> y)) has_derivative (\<lambda>z. f' (\<Psi> y) (\<Psi> z))) (at y within \<Phi> ` S)"
      by (simp add: df has_derivative_in_compose lin\<Psi> linear_imp_has_derivative)
    have d\<Phi>: "(\<Phi> has_derivative \<Phi>) (at (f (\<Psi> y)) within (\<lambda>y. f (\<Psi> y)) ` (\<Phi> ` S))"
      using lin\<Phi> by (simp add: linear_imp_has_derivative)
    show "(h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
      unfolding h_def
      using has_derivative_in_compose[OF d_f\<Psi> d\<Phi>] by simp
  qed

  have ns_h:
    "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow> \<not> surj (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"
  proof
    fix y assume yS: "y \<in> \<Phi> ` S"
    assume sur: "surj (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"
    have \<Psi>yS: "\<Psi> y \<in> S" using yS \<Psi>\<Phi> by auto
    have "surj (f' (\<Psi> y))"
      unfolding surj_def
    proof clarify
      fix u :: "(real^2)^'n"
      from sur obtain z where z: "\<Phi> (f' (\<Psi> y) (\<Psi> z)) = \<Phi> u"
        by (metis (mono_tags, lifting) surj_def)
      show "\<exists>x. u = f' (\<Psi> y) x"
      proof (intro exI[where x = "\<Psi> z"])
        have "\<Psi> (\<Phi> (f' (\<Psi> y) (\<Psi> z))) = \<Psi> (\<Phi> u)" using z by simp
        then show "u = f' (\<Psi> y) (\<Psi> z)" by (simp add: \<Psi>\<Phi>)
      qed
    qed
    then show False using ns[OF \<Psi>yS] by contradiction
  qed

  have neg_h: "negligible (h ` (\<Phi> ` S))"
  proof (rule baby_Sard[where f = h and S = "\<Phi> ` S"
            and f' = "\<lambda>y z. \<Phi> (f' (\<Psi> y) (\<Psi> z))"])
    show "CARD('n bit0) \<le> CARD('n bit0)" by simp
    show "\<And>y. y \<in> \<Phi> ` S \<Longrightarrow>
        (h has_derivative (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) (at y within \<Phi> ` S)"
      using der_h by blast
  next
    fix y assume yS: "y \<in> \<Phi> ` S"
    have \<Psi>yS: "\<Psi> y \<in> S" using yS \<Psi>\<Phi> by auto
    have linf': "linear (f' (\<Psi> y))" using der[OF \<Psi>yS] has_derivative_linear by blast
    have ling: "linear (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))"
      using linear_compose[OF linear_compose[OF lin\<Psi> linf'] lin\<Phi>] by (simp add: o_def)
    have "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) \<noteq> CARD('n bit0)"
      by (metis full_rank_surjective ling matrix_vector_mul(2) ns_h yS)
    moreover have "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) \<le> CARD('n bit0)"
      by (metis min.idem rank_bound)
    ultimately show "rank (matrix (\<lambda>z. \<Phi> (f' (\<Psi> y) (\<Psi> z)))) < CARD('n bit0)" by simp
  qed

  have image_eq: "f ` S = \<Psi> ` (h ` (\<Phi> ` S))"
    unfolding h_def using \<Psi>\<Phi> by (smt (verit, best) image_cong image_image)

  show ?thesis
    unfolding image_eq
  proof (rule negligible_locally_Lipschitz_image[OF _ neg_h])
    show "DIM(real^('n bit0)) \<le> DIM((real^2)^'n)" by simp
  next
    fix x :: "real^('n bit0)" assume "x \<in> h ` (\<Phi> ` S)"
    obtain K where K: "\<And>z. norm (\<Psi> z) \<le> K * norm z"
      using lin\<Psi> linear_conv_bounded_linear bounded_linear.bounded linear_bounded by blast
    show "\<exists>T B. open T \<and> x \<in> T \<and>
            (\<forall>y\<in>(h ` (\<Phi> ` S)) \<inter> T. norm (\<Psi> y - \<Psi> x) \<le> B * norm (y - x))"
      by (rule exI[of _ UNIV], rule exI[of _ K], auto simp: linear_diff[OF lin\<Psi>, symmetric] K)
  qed
qed

lemma negligible_proj_charts_Nn:
  fixes charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
  assumes "\<And>i x. x \<in> Crit i \<Longrightarrow>
            ((fst \<circ> charts i) has_derivative blinfun_apply (D i x)) (at x within Crit i)"
    and "\<And>i x. x \<in> Crit i \<Longrightarrow> \<not> surj (blinfun_apply (D i x))"
  shows "negligible (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
proof -
  have "negligible ((fst \<circ> charts i) ` (Crit i))" for i
    by (rule negligible_singular_image_2n
          [where f = "fst \<circ> charts i" and S = "Crit i"
             and f' = "\<lambda>x. blinfun_apply (D i x)"])
       (use assms in blast)+
  then show ?thesis by (rule negligible_Union_nat)
qed

lemma parametric_transversality_negligible_complex:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}"
    and "open \<Omega>reg"
    and joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
  shows "negligible {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg}"
proof -
  have reg0: "regular_value_on (\<lambda>z. cplx_r2 (A z)) (V \<times> \<Omega>reg) 0"
    using regular_value_on_cplx_r2_comp[OF joint_trans] .
  have eq_bad:
      "{x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg}
       =
       {x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. cplx_r2 (A (x,\<omega>)) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. cplx_r2 (A (x,u))) has_derivative D) (at \<omega> within \<Omega>reg) \<and> surj D))}"
    unfolding transverse0_on_def by auto
  have bad_negligible:
    "negligible {x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. cplx_r2 (A (x,\<omega>)) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. cplx_r2 (A (x,u))) has_derivative D)
                       (at \<omega> within \<Omega>reg) \<and> surj D))}"
  proof -
    let ?G = "\<lambda>z. cplx_r2 (A z)"

    obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
       and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
       and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      where cover:
      "{x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. ?G (x,\<omega>) = 0 \<and>
          (\<not> (\<exists>D\<omega>. ((\<lambda>u. ?G (x,u)) has_derivative D\<omega>)
                    (at \<omega> within \<Omega>reg) \<and> surj D\<omega>))}
       \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der:
      "\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)"
      and rank:
      "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      using charts_core_Nn[OF assms(1) assms(2) assms(3) reg0]
      by blast

    have negligible_cover:
      "negligible (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    proof (rule negligible_proj_charts_Nn)
      show "\<And>i x. x \<in> Crit i \<Longrightarrow>
        ((fst \<circ> charts i) has_derivative blinfun_apply (D i x))
          (at x within Crit i)"
        using der by blast
      show "\<And>i x. x \<in> Crit i \<Longrightarrow> \<not> surj (blinfun_apply (D i x))"
        using rank by blast
    qed

    show ?thesis
      using negligible_cover cover negligible_subset by blast
  qed
  then have "negligible {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg}"
    by (simp add: eq_bad)
  then show ?thesis
    by (simp only: transverse0_on_cplx_r2_iff)
qed


section \<open>Negligible Sets Are Meager (meagerness engine for the bad-set branches)\<close>

text \<open>
  All four bad-set branches reduce, via parametric transversality, to: the bad set is
  contained in a countable union of \<^emph>\<open>lower-dimensional\<close> smooth images, which are
  Lebesgue-negligible (\<^const>\<open>negligible\<close>). This module is the reusable bridge from
  \<^const>\<open>negligible\<close> to the paper's \<^const>\<open>meager\<close>: a closed negligible subset of a
  Euclidean space is nowhere dense, and a set covered by countably many such pieces is
  meager. It is exactly the topological half of \<open>lem:smooth-chart-meager\<close>.
\<close>

lemma meager_nowhere_dense:
  fixes A :: "'a::topological_space set"
  assumes "nowhere_dense A"
  shows "meager A"
  using assms unfolding meager_def by (intro exI[of _ "\<lambda>_. A"]) auto

lemma nowhere_dense_closed_negligible:
  fixes A :: "'a::euclidean_space set"
  assumes "closed A" and "negligible A"
  shows "nowhere_dense A"
proof -
  have "interior A = {}"
  proof (rule ccontr)
    assume ne: "interior A \<noteq> {}"
    have "\<not> negligible (interior A)"
      by (rule open_not_negligible[OF open_interior ne])
    moreover have "negligible (interior A)"
      by (rule negligible_subset[OF assms(2) interior_subset])
    ultimately show False by blast
  qed
  with assms(1) show ?thesis
    by (simp only: nowhere_dense_def closure_closed)
qed

lemma meager_negligible_closed_cover:
  fixes A :: "'a::euclidean_space set"
  assumes "A \<subseteq> (\<Union>n::nat. K n)"
    and "\<And>n. closed (K n)" and "\<And>n. negligible (K n)"
  shows "meager A"
proof -
  have "meager (\<Union>n. K n)"
  proof (rule meager_Union_nat)
    fix n
    show "meager (K n)"
      by (rule meager_nowhere_dense[OF nowhere_dense_closed_negligible[OF assms(2) assms(3)]])
  qed
  then show ?thesis
    using assms(1) by (rule meager_subset[rotated])
qed

text \<open>
  Meager version of the regular-stratum transversality bad set (the rung that
  \<open>prop_regzero\<close> consumes). The chart cover from @{thm charts_core_Nn} is a
  countable union of \<^emph>\<open>closed\<close> Lebesgue-negligible pieces, so the bad set is
  meager by @{thm meager_negligible_closed_cover}.
\<close>

lemma parametric_transversality_meager_complex:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}"
    and "open \<Omega>reg"
    and joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
  shows "meager {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg}"
proof -
  have reg0: "regular_value_on (\<lambda>z. cplx_r2 (A z)) (V \<times> \<Omega>reg) 0"
    using regular_value_on_cplx_r2_comp[OF joint_trans] .
  have eq_bad:
      "{x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg}
       =
       {x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. cplx_r2 (A (x,\<omega>)) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. cplx_r2 (A (x,u))) has_derivative D) (at \<omega> within \<Omega>reg) \<and> surj D))}"
    unfolding transverse0_on_def by auto
  have bad_meager:
    "meager {x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. cplx_r2 (A (x,\<omega>)) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. cplx_r2 (A (x,u))) has_derivative D)
                       (at \<omega> within \<Omega>reg) \<and> surj D))}"
  proof -
    let ?G = "\<lambda>z. cplx_r2 (A z)"

    obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
       and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
       and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      where cover:
      "{x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. ?G (x,\<omega>) = 0 \<and>
          (\<not> (\<exists>D\<omega>. ((\<lambda>u. ?G (x,u)) has_derivative D\<omega>)
                    (at \<omega> within \<Omega>reg) \<and> surj D\<omega>))}
       \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der:
      "\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x)))
            (at x within Crit i)"
      and rank:
      "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clsd:
      "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
      using charts_core_Nn[OF assms(1) assms(2) assms(3) reg0]
      by blast

    have negligible_cover:
      "negligible (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    proof (rule negligible_proj_charts_Nn)
      show "\<And>i x. x \<in> Crit i \<Longrightarrow>
        ((fst \<circ> charts i) has_derivative blinfun_apply (D i x))
          (at x within Crit i)"
        using der by blast
      show "\<And>i x. x \<in> Crit i \<Longrightarrow> \<not> surj (blinfun_apply (D i x))"
        using rank by blast
    qed

    show ?thesis
    proof (rule meager_negligible_closed_cover
                  [where K = "\<lambda>i. (fst \<circ> charts i) ` (Crit i)"])
      show "{x\<in>V. \<exists>\<omega>\<in>\<Omega>reg. ?G (x,\<omega>) = 0 \<and>
              (\<not> (\<exists>D\<omega>. ((\<lambda>u. ?G (x,u)) has_derivative D\<omega>)
                        (at \<omega> within \<Omega>reg) \<and> surj D\<omega>))}
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
        by (rule cover)
      show "\<And>i. closed ((fst \<circ> charts i) ` (Crit i))"
        using clsd by blast
      show "\<And>i. negligible ((fst \<circ> charts i) ` (Crit i))"
        using negligible_cover by (auto intro: negligible_subset)
    qed
  qed
  then have "meager {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. cplx_r2 (A (x,\<omega>))) \<Omega>reg}"
    by (simp add: eq_bad)
  then show ?thesis
    by (simp only: transverse0_on_cplx_r2_iff)
qed

theorem prop_regzero:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}" and "open \<Omega>reg"
    and A_smooth: "(\<forall>z\<in>V\<times>\<Omega>reg. A differentiable at z)"
    and joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
  shows "meager {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg}"
  by (rule parametric_transversality_meager_complex[OF assms(1-3) joint_trans])


section \<open>The Singular Curve Is a Fold\<close>

text \<open>
  The explicit fold fields. With the moving frame \<open>e_r(\<phi>) = (\<cos>\<phi>, \<sin>\<phi>)\<close>,
  \<open>e_\<phi>(\<phi>) = (-\<sin>\<phi>, \<cos>\<phi>)\<close> and (ignoring the additive \<open>\<omega>\<^sub>s\<close> constant)
  \<open>cvec(\<theta>,\<phi>) = \<sin>\<theta> e_r(\<phi>) + \<cos>\<theta> D + c\<^sub>0\<close>, the partials are
  \<open>\<partial>\<^sub>\<phi> cvec = \<sin>\<theta> e_\<phi>\<close>, \<open>\<partial>\<^sub>\<theta> cvec = \<cos>\<theta> e_r - \<sin>\<theta> D\<close>, and the Jacobian determinant is
  \<open>\<det> D\<^sub>\<omega> cvec = h(\<theta>,\<phi>) \<sin>\<theta>\<close> with \<open>h = \<cos>\<theta> - \<sin>\<theta> (D \<cdot> e_r)\<close>. The singular curve
  \<open>\<Sigma> = {h \<sin>\<theta> = 0}\<close> is where the differential drops rank.
\<close>

definition e_r :: "real \<Rightarrow> real \<times> real" where "e_r \<phi> = (cos \<phi>, sin \<phi>)"
definition e_p :: "real \<Rightarrow> real \<times> real" where "e_p \<phi> = (- sin \<phi>, cos \<phi>)"

definition cvecf :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<times> real" where
  "cvecf D c0 \<theta> \<phi> = sin \<theta> *\<^sub>R e_r \<phi> + cos \<theta> *\<^sub>R D + c0"

text \<open>
  The \<open>2 \<times> 2\<close> Jacobian \<open>D\<^sub>\<omega> cvec\<close> as a Cartesian matrix \<^typ>\<open>real^2^2\<close>, with columns
  the partials \<open>\<partial>\<^sub>\<theta> cvec\<close> (column 1) and \<open>\<partial>\<^sub>\<phi> cvec\<close> (column 2). Its determinant is the
  standard HOL-Analysis \<^const>\<open>det\<close> (evaluated via @{thm [source] det_2}).
\<close>

definition Jcvec :: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2^2" where
  "Jcvec D \<theta> \<phi> =
     (\<chi> i j. if j = 1
              then (if i = 1 then cos \<theta> * cos \<phi> - sin \<theta> * fst D
                             else cos \<theta> * sin \<phi> - sin \<theta> * snd D)
              else (if i = 1 then - (sin \<theta> * sin \<phi>) else sin \<theta> * cos \<phi>))"

lemma e_r_vector_deriv: "(e_r has_vector_derivative e_p \<phi>) (at \<phi>)"
proof -
  have c: "((\<lambda>\<phi>. cos \<phi>) has_vector_derivative - sin \<phi>) (at \<phi>)"
    by (simp add: has_vector_derivative_def) (auto intro!: derivative_eq_intros)
  have s: "((\<lambda>\<phi>. sin \<phi>) has_vector_derivative cos \<phi>) (at \<phi>)"
    by (simp add: has_vector_derivative_def) (auto intro!: derivative_eq_intros)
  show ?thesis
    unfolding e_r_def e_p_def
    by (auto intro!: has_vector_derivative_Pair c s)
qed

lemma cvecf_phi_deriv:
  "((\<lambda>\<phi>. cvecf D c0 \<theta> \<phi>) has_vector_derivative (sin \<theta> *\<^sub>R e_p \<phi>)) (at \<phi>)"
  unfolding cvecf_def
  by (auto intro!: derivative_eq_intros e_r_vector_deriv)

lemma cvecf_theta_deriv:
  "((\<lambda>\<theta>. cvecf D c0 \<theta> \<phi>) has_vector_derivative (cos \<theta> *\<^sub>R e_r \<phi> - sin \<theta> *\<^sub>R D)) (at \<theta>)"
  unfolding cvecf_def
  by (auto intro!: derivative_eq_intros)

lemma det_Jcvec:
  "det (Jcvec D \<theta> \<phi>) = (cos \<theta> - sin \<theta> * (D \<bullet> e_r \<phi>)) * sin \<theta>"
proof -
  have py: "cos \<phi> * cos \<phi> + sin \<phi> * sin \<phi> = 1"
    using sin_cos_squared_add[of \<phi>] by (simp add: power2_eq_square)
  have m: "D \<bullet> e_r \<phi> = fst D * cos \<phi> + snd D * sin \<phi>"
    by (simp add: e_r_def inner_prod_def)
  have raw: "det (Jcvec D \<theta> \<phi>)
      = (cos \<theta> * cos \<phi> - sin \<theta> * fst D) * (sin \<theta> * cos \<phi>)
        - (- (sin \<theta> * sin \<phi>)) * (cos \<theta> * sin \<phi> - sin \<theta> * snd D)"
    by (simp add: det_2 Jcvec_def)
  show ?thesis
    unfolding raw m using py by algebra
qed

theorem lem_foldfields:
  fixes D c0 :: "real \<times> real" and \<theta> \<phi> :: real
  shows "((\<lambda>\<phi>. cvecf D c0 \<theta> \<phi>) has_vector_derivative (sin \<theta> *\<^sub>R e_p \<phi>)) (at \<phi>)"
    and "((\<lambda>\<theta>. cvecf D c0 \<theta> \<phi>) has_vector_derivative (cos \<theta> *\<^sub>R e_r \<phi> - sin \<theta> *\<^sub>R D)) (at \<theta>)"
    and "det (Jcvec D \<theta> \<phi>) = (cos \<theta> - sin \<theta> * (D \<bullet> e_r \<phi>)) * sin \<theta>"
  using cvecf_phi_deriv cvecf_theta_deriv det_Jcvec by blast+


section \<open>Fold Zeros of the Array Factor\<close>

text \<open>
  TeX Proposition~(Fold zeros are nongeneric) is the same pattern as the regular
  stratum, but with a 1-dimensional parameter (a chart on the fold curve) instead of
  an open 2D domain. Each chart yields a smooth map \<open>V \<times> I \<to> \<complex>\<close> transverse to 0,
  hence its zero set projects meagerly to \<open>V\<close>; a finite union stays meager.
\<close>

lemma chart_zero_projection_meager_stub:
  fixes V :: "((real^2)^'n) set" and I :: "real set"
    and F :: "(((real^2)^'n) \<times> real) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}"
    and "I \<subseteq> UNIV"
    and F_smooth: "\<forall>z\<in>V\<times>I. F differentiable at z"
    and Dx_surj:
      "\<forall>(x,t)\<in>V\<times>I. F (x,t) = 0 \<longrightarrow>
        (\<exists>D. ((\<lambda>y. F (y,t)) has_derivative D) (at x within V) \<and> surj D)"
  shows "meager {x\<in>V. \<exists>t\<in>I. F (x,t) = 0}"
  sorry

lemma meager_Union_finite:
  fixes A :: "'i \<Rightarrow> 'a::topological_space set"
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> meager (A i)"
  shows "meager (\<Union>i\<in>I. A i)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert i I)
  have "meager ((\<Union>j\<in>insert i I. A j)) \<longleftrightarrow> meager (A i \<union> (\<Union>j\<in>I. A j))"
    by auto
  moreover have "meager (A i \<union> (\<Union>j\<in>I. A j))"
    using insert by (intro meager_Un) auto
  ultimately show ?case
    by simp
qed

theorem prop_foldzero:
  fixes V :: "((real^2)^'n) set"
    and L :: nat
    and I :: "nat \<Rightarrow> real set"
    and F :: "nat \<Rightarrow> ((((real^2)^'n) \<times> real) \<Rightarrow> complex)"
  assumes V: "open V" "V \<noteq> {}"
    and charts:
      "\<And>l. l < L \<Longrightarrow> meager {x\<in>V. \<exists>t\<in>I l. F l (x,t) = 0}"
  shows "meager {x\<in>V. \<exists>l<L. \<exists>t\<in>I l. F l (x,t) = 0}"
proof -
  define S where "S l = {x\<in>V. \<exists>t\<in>I l. F l (x,t) = 0}" for l
  have hS: "\<And>l. l \<in> {..<L} \<Longrightarrow> meager (S l)"
    using charts by (simp add: S_def)
  have "meager (\<Union>l\<in>{..<L}. S l)"
    by (rule meager_Union_finite) (use hS in auto)
  moreover have "{x\<in>V. \<exists>l<L. \<exists>t\<in>I l. F l (x,t) = 0} = (\<Union>l\<in>{..<L}. S l)"
    by (auto simp: S_def)
  ultimately show ?thesis
    by simp
qed


section \<open>Fold Critical Points with @{term "A \<noteq> 0"}\<close>

text \<open>
  TeX Lemma~\<open>lem:Efinite\<close>: \<open>E = {\<omega>\<in>\<Sigma> : g\<^sub>\<theta>(\<omega>) = 0}\<close> is finite. We model the
  element-gain \<open>\<theta>\<close>-derivative \<open>g\<^sub>\<theta>\<close> as real-analytic (the real restriction of an
  entire function \<open>G\<close>) and not identically zero on the compact \<open>\<theta>\<close>-interval \<open>\<Theta>\<close>;
  the fold curve \<open>\<Sigma>\<close> has a finite \<open>\<phi>\<close>-fibre over each \<open>\<theta>\<close> (at most two solutions).
  The remaining obligation is the real-analytic isolated-zeros fact (zeros of a
  nontrivial real-analytic function on a compact interval are finite).
\<close>

theorem lem_Efinite:
  fixes g\<theta> :: "real \<Rightarrow> real" and G :: "complex \<Rightarrow> complex"
    and \<Theta> :: "real set" and \<Sigma> :: "(real \<times> real) set"
  assumes \<Theta>_compact: "compact \<Theta>" and \<Theta>_interval: "is_interval \<Theta>"
    and \<Sigma>_\<theta>range: "\<And>\<theta> \<phi>. (\<theta>, \<phi>) \<in> \<Sigma> \<Longrightarrow> \<theta> \<in> \<Theta>"
    and \<phi>_fibre_finite: "\<And>\<theta>. finite {\<phi>. (\<theta>, \<phi>) \<in> \<Sigma>}"
    and g\<theta>_restriction: "\<And>t. g\<theta> t = Re (G (complex_of_real t))"
    and G_entire: "G holomorphic_on UNIV"
    and g\<theta>_not_identically_zero: "\<exists>t\<in>\<Theta>. g\<theta> t \<noteq> 0"
  shows "finite {\<omega> \<in> \<Sigma>. g\<theta> (fst \<omega>) = 0}"
proof -
  \<comment> \<open>The genuine analytic kernel: zeros of the nontrivial real-analytic
      \<open>g\<^sub>\<theta> = \<real> \<circ> G\<close> on the compact interval \<open>\<Theta>\<close> are finite. This is the only
      remaining obligation; the rest of the proof is fibre bookkeeping.
      (Provable via Schwarz reflection \<open>z \<mapsto> cnj (G (cnj z))\<close> + the holomorphic
      isolated-zeros theorem (\<open>isolated_zeros\<close>), once
      \<open>HOL-Complex_Analysis.Conformal_Mappings\<close> is in scope.)\<close>
  have theta_zeros_finite: "finite {t \<in> \<Theta>. g\<theta> t = 0}"
    sorry
  \<comment> \<open>Each bad \<open>\<omega> = (\<theta>,\<phi>)\<close> has \<open>\<theta> \<in> \<Theta>\<close> with \<open>g\<^sub>\<theta>(\<theta>) = 0\<close>, so it lies in the
      \<open>\<phi>\<close>-fibre over one of finitely many \<open>\<theta>\<close>.\<close>
  have "{\<omega> \<in> \<Sigma>. g\<theta> (fst \<omega>) = 0}
          \<subseteq> (\<Union>t \<in> {t \<in> \<Theta>. g\<theta> t = 0}. (\<lambda>\<phi>. (t, \<phi>)) ` {\<phi>. (t, \<phi>) \<in> \<Sigma>})"
  proof
    fix \<omega> assume "\<omega> \<in> {\<omega> \<in> \<Sigma>. g\<theta> (fst \<omega>) = 0}"
    then have \<omega>\<Sigma>: "\<omega> \<in> \<Sigma>" and g0: "g\<theta> (fst \<omega>) = 0" by auto
    obtain t \<phi> where \<omega>eq: "\<omega> = (t, \<phi>)" by (cases \<omega>)
    from \<omega>\<Sigma> \<omega>eq have "\<phi> \<in> {\<phi>. (t, \<phi>) \<in> \<Sigma>}" by simp
    moreover from \<omega>\<Sigma> \<omega>eq \<Sigma>_\<theta>range have "t \<in> \<Theta>" by simp
    moreover from g0 \<omega>eq have "g\<theta> t = 0" by simp
    ultimately show "\<omega> \<in> (\<Union>t \<in> {t \<in> \<Theta>. g\<theta> t = 0}. (\<lambda>\<phi>. (t, \<phi>)) ` {\<phi>. (t, \<phi>) \<in> \<Sigma>})"
      using \<omega>eq by blast
  qed
  moreover have "finite (\<Union>t \<in> {t \<in> \<Theta>. g\<theta> t = 0}. (\<lambda>\<phi>. (t, \<phi>)) ` {\<phi>. (t, \<phi>) \<in> \<Sigma>})"
    by (rule finite_UN_I[OF theta_zeros_finite])
       (simp add: \<phi>_fibre_finite)
  ultimately show ?thesis
    by (rule finite_subset)
qed

text \<open>
  TeX Proposition~\<open>prop:foldnonzero\<close>: the nonzero-\<open>A\<close> fold-critical bad set is
  meager in \<open>V\<close>. As in the TeX proof, every such critical point lies over the
  finite exceptional set \<open>E\<close> (Lemma~\<open>lem:Efinite\<close>), and for each \<open>\<omega>\<in>E\<close> the slice
  function \<open>F\<^sub>\<omega>(x) = \<partial>\<^sub>s U(x,\<omega>)\<close> is a nontrivial real-analytic function of \<open>x\<close>,
  so its zero set in the connected open \<open>V\<close> is nowhere dense. The bad set is
  contained in their finite union, hence meager. The nowhere-density of each
  slice-zero set is the real-analytic input, recorded here as a hypothesis; this
  theorem is the (proved) reduction assembling the finite union.
\<close>

theorem prop_foldnonzero:
  fixes V Bad :: "((real^2)^'n) set" and E :: "(real^2) set"
    and Fcrit :: "(real^2) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
  assumes E_finite: "finite E"
    and reduce_to_E: "Bad \<subseteq> (\<Union>\<omega>\<in>E. {x \<in> V. Fcrit \<omega> x = 0})"
    and slice_nowhere_dense:
      "\<And>\<omega>. \<omega> \<in> E \<Longrightarrow> nowhere_dense {x \<in> V. Fcrit \<omega> x = 0}"
  shows "meager Bad"
proof -
  have "meager (\<Union>\<omega>\<in>E. {x \<in> V. Fcrit \<omega> x = 0})"
    by (rule meager_Union_finite[OF E_finite])
       (rule meager_nowhere_dense[OF slice_nowhere_dense])
  then show ?thesis
    by (rule meager_subset[OF reduce_to_E])
qed


section \<open>Regular-Stratum Nonzero-A Degenerate Critical Points\<close>

text \<open>
  TeX Proposition~\<open>prop:regnonzero\<close>: the regular-stratum nonzero-\<open>A\<close> bad set
  \<open>B\<^sub>reg,\<noteq>0\<close> is meager in \<open>V\<close>. The TeX proof partitions the bad locus \<open>Z\<close> by the
  surjective set \<open>W\<^sub>surj\<close> and by \<open>H\<equiv>0\<close> into four pieces: the regular codim-3
  piece \<open>\<pi>\<^sub>V(Z\<^sub>reg)\<close> and the codim-5 Hessian-zero stratum (both meager by
  \<open>prop:dimZ\<close> + \<open>lem:smooth-chart-meager\<close>), the Case-B set (meager by
  \<open>cor:caseBmeager\<close>, Appendix~\<open>app:caseB\<close>), and the residual \<open>H\<equiv>0\<close> set
  (meager by \<open>prop:h0res-meager\<close>, Appendix~\<open>app:H0res\<close>). Those four meagerness
  facts are the deep appendix results, recorded here as hypotheses; this theorem
  is the (proved) reduction that assembles them.
\<close>

text \<open>
  The explicit \<open>12 \<times> 12\<close> real Jacobian minor \<open>J\<close> of \<open>D\<^sub>x M\<close> at the chosen
  six-element configuration (TeX Figure~\<open>fig:bigmatrix\<close>), evaluated at
  \<open>\<kappa> = 1\<close>. Rows are the twelve real moment components
  \<open>\<real>A, \<I>A, \<real>M\<^sub>1, \<I>M\<^sub>1, \<real>M\<^sub>2, \<I>M\<^sub>2, \<real>M\<^sub>1\<^sub>1, \<I>M\<^sub>1\<^sub>1, \<real>M\<^sub>1\<^sub>2, \<I>M\<^sub>1\<^sub>2, \<real>M\<^sub>2\<^sub>2, \<I>M\<^sub>2\<^sub>2\<close>;
  the twelve columns are \<open>\<partial>\<^sub>u\<^sub>n M, \<partial>\<^sub>v\<^sub>n M\<close> for \<open>n = 1..6\<close>. (The determinant is
  transpose-invariant, so the row/column reading is immaterial.)
\<close>

definition bigJ :: "real^12^12" where
  "bigJ = vector
    [ vector [0, 0, - sqrt 3 / 2, 0, - sqrt 3 / 2, 0, 0, 0, sqrt 3 / 2, 0, sqrt 3 / 2, 0],
      vector [- 1, 0, - 1/2, 0, 1/2, 0, 1, 0, 1/2, 0, - 1/2, 0],
      vector [1, 0, 1/2 - pi * sqrt 3 / 6, 0, - 1/2 - pi * sqrt 3 / 3, 0,
              - 1, 0, - 1/2 + 2 * pi * sqrt 3 / 3, 0, 1/2 + 5 * pi * sqrt 3 / 6, 0],
      vector [0, 0, - sqrt 3 / 2 - pi / 6, 0, - sqrt 3 / 2 + pi / 3, 0,
              pi, 0, sqrt 3 / 2 + 2 * pi / 3, 0, sqrt 3 / 2 - 5 * pi / 6, 0],
      vector [0, 1, - sqrt 3, 1/2, 0, - 1/2, 0, - 1, sqrt 3, - 1/2, sqrt 3, 1/2],
      vector [- 2, 0, - 1, - sqrt 3 / 2, 0, - sqrt 3 / 2, 0, 0, 1, sqrt 3 / 2, - 1, sqrt 3 / 2],
      vector [0, 0, pi / 3 - pi^2 * sqrt 3 / 18, 0, - 2 * pi / 3 - 2 * pi^2 * sqrt 3 / 9, 0,
              - 2 * pi, 0, - 4 * pi / 3 + 8 * pi^2 * sqrt 3 / 9, 0,
              5 * pi / 3 + 25 * pi^2 * sqrt 3 / 18, 0],
      vector [0, 0, - pi * sqrt 3 / 3 - pi^2 / 18, 0, - 2 * pi * sqrt 3 / 3 + 2 * pi^2 / 9, 0,
              pi^2, 0, 4 * pi * sqrt 3 / 3 + 8 * pi^2 / 9, 0,
              5 * pi * sqrt 3 / 3 - 25 * pi^2 / 18, 0],
      vector [2, 0, 1 - pi * sqrt 3 / 3, pi / 6, 0, - pi / 3, 0, - pi,
              - 1 + 4 * pi * sqrt 3 / 3, - 2 * pi / 3, 1 + 5 * pi * sqrt 3 / 3, 5 * pi / 6],
      vector [0, 0, - sqrt 3 - pi / 3, - pi * sqrt 3 / 6, 0, - pi * sqrt 3 / 3, 0, 0,
              sqrt 3 + 4 * pi / 3, 2 * pi * sqrt 3 / 3, sqrt 3 - 5 * pi / 3, 5 * pi * sqrt 3 / 6],
      vector [0, 4, - 2 * sqrt 3, 2, 0, 0, 0, 0, 2 * sqrt 3, - 2, 2 * sqrt 3, 2],
      vector [- 4, 0, - 2, - 2 * sqrt 3, 0, 0, 0, 0, 2, 2 * sqrt 3, - 2, 2 * sqrt 3] ]"

text \<open>
  TeX Lemma~\<open>lem:Msurj\<close>, determinant core (\<open>det J = -5\<pi>\<^sup>8/3\<close> at \<open>\<kappa> = 1\<close>;
  the general value is \<open>-5\<pi>\<^sup>8/(3\<kappa>\<^sup>2)\<close>). This is the standalone arithmetic
  fact: the explicit symbolic determinant evaluation of the configuration
  matrix \<^const>\<open>bigJ\<close>. Stated without proof; the (omitted) proof is the
  four-subsubsection cofactor/Vandermonde computation of TeX
  Section~\<open>sssec:msurj-config\<close>. Being nonzero, it is the engine behind the
  \<open>big_det\<close> hypothesis of \<open>Dx_moment_map_surjective\<close> below.
\<close>

lemma bigJ_det: "det bigJ = - (5 * pi^8) / 3"
  sorry

lemma bigJ_det_nonzero: "det bigJ \<noteq> 0"
proof -
  have "pi > 0" by (rule pi_gt_zero)
  hence "pi^8 > 0" by simp
  thus ?thesis unfolding bigJ_det by simp
qed

text \<open>
  The configuration matrix has full rank, hence the parameter-derivative is
  surjective \<^emph>\<open>at the base point\<close>. This is the pointwise content of
  \<open>lem:Msurj\<close> that the determinant delivers: it discharges the \<open>big_det\<close>
  base-point premise of \<open>Dx_moment_map_surjective\<close> once the concrete moment
  map's derivative at the six-element configuration is identified with
  \<^term>\<open>(*v) bigJ\<close>. The open-dense upgrade is a \<^emph>\<open>separate\<close> argument (real-analytic
  lower semicontinuity of rank), not implied by the single-point determinant.
\<close>

lemma bigJ_full_rank: "rank bigJ = CARD(12)"
proof -
  have "rank bigJ \<noteq> CARD(12) \<Longrightarrow> rank bigJ < CARD(12)"
    using rank_bound[of bigJ] by simp
  with bigJ_det_nonzero det_eq_0_rank[of bigJ] show ?thesis by auto
qed

lemma bigJ_surj: "surj ((*v) bigJ)"
  using bigJ_full_rank full_rank_surjective[of bigJ] by simp

text \<open>
  TeX Lemma~\<open>lem:Msurj\<close> (Surjectivity of \<open>D\<^sub>x M\<close>). For \<open>N = CARD('n) \<ge> 6\<close> and
  \<open>c \<noteq> 0\<close>, the parameter-derivative of the moment map
  \<open>M(\<cdot>,c) : \<real>\<^sup>2\<^sup>N \<rightarrow> \<complex>\<^sup>6 \<cong> \<real>\<^sup>1\<^sup>2\<close> (the six moments
  \<open>A, M\<^sub>1, M\<^sub>2, M\<^sub>1\<^sub>1, M\<^sub>1\<^sub>2, M\<^sub>2\<^sub>2\<close>) is surjective on an open dense subset of \<open>V\<close>.
  The omitted proof is the explicit \<open>12 \<times> 12\<close> real Jacobian minor at the
  six-element configuration, yielding the big determinant
  \<open>det J = -5\<pi>\<^sup>8 / (3\<kappa>\<^sup>2) \<noteq> 0\<close>, followed by a lower-semicontinuity upgrade
  of pointwise surjectivity to an open dense set. This feeds the \<open>ZH0surj\<close>
  piece of \<open>prop_regnonzero\<close>. The conclusion is guarded by a \<open>big_det\<close>
  hypothesis (existence of one regular base point), so the recorded obligation
  is the open-dense propagation, not an (otherwise false) absolute surjectivity
  claim. TODO: model the six moments concretely and discharge.
\<close>

lemma Dx_moment_map_surjective:
  fixes V :: "((real^2)^'n) set"
    and \<M> :: "(real^2)^'n \<Rightarrow> complex^6"
    and D\<M> :: "(real^2)^'n \<Rightarrow> ((real^2)^'n \<Rightarrow> complex^6)"
  assumes "open V" and "V \<noteq> {}"
    and N_ge_6: "6 \<le> CARD('n)"
    and deriv: "\<And>x. x \<in> V \<Longrightarrow> (\<M> has_derivative D\<M> x) (at x within V)"
    and big_det: "\<exists>x\<^sub>0\<in>V. surj (D\<M> x\<^sub>0)"
  shows "\<exists>U. open U \<and> U \<subseteq> V \<and> V \<subseteq> closure U \<and> (\<forall>x\<in>U. surj (D\<M> x))"
  sorry

theorem prop_regnonzero:
  fixes V Breg_nonzero Zreg ZH0surj BcaseB BH0res :: "((real^2)^'n) set"
  assumes decompose:
      "Breg_nonzero \<inter> V
         \<subseteq> (Zreg \<inter> V) \<union> (ZH0surj \<inter> V) \<union> (BcaseB \<inter> V) \<union> (BH0res \<inter> V)"
    and meager_Zreg:    "meager (Zreg \<inter> V)"
    and meager_ZH0surj: "meager (ZH0surj \<inter> V)"
    and meager_BcaseB:  "meager (BcaseB \<inter> V)"
    and meager_BH0res:  "meager (BH0res \<inter> V)"
  shows "meager (Breg_nonzero \<inter> V)"
proof -
  have "meager ((Zreg \<inter> V) \<union> (ZH0surj \<inter> V) \<union> (BcaseB \<inter> V) \<union> (BH0res \<inter> V))"
    by (intro meager_Un meager_Zreg meager_ZH0surj meager_BcaseB meager_BH0res)
  then show ?thesis
    by (rule meager_subset[OF decompose])
qed


section \<open>Closeout\<close>

text \<open>
  TeX Theorem~(Odd-\<open>N\<close> nonemptiness), \<open>thm:final\<close>. The Baire closeout: given a
  nonempty open feasible working set \<open>V \<subseteq> Fset\<close> and the four branch meagerness
  facts (Props \<open>prop:regzero\<close>, \<open>prop:foldzero\<close>, \<open>prop:foldnonzero\<close>,
  \<open>prop:regnonzero\<close>) plus soundness of \<open>X0\<close>, the robust feasible set is nonempty.

  This is the genuine closeout, discharged by the fully-proved combinator
  \<open>nonemptiness_from_meager_branches\<close> (\<open>Nonemptiness_Spine\<close>). The four
  meagerness facts remain explicit hypotheses here: they are the deep branch
  results, still to be established for the concrete array-factor bad sets (Props
  \<open>prop_regzero\<close>/\<open>prop_foldzero\<close> are proved modulo the transversality stubs;
  \<open>prop_foldnonzero\<close>/\<open>prop_regnonzero\<close> remain). Once all four are proved
  unconditionally for the concrete sets, instantiating this theorem yields the
  odd-\<open>N\<close> nonemptiness theorem with no remaining hypotheses.
\<close>

theorem thm_final:
  fixes Fset V :: "((real^2)^'n) set"
    and X0 :: "real \<Rightarrow> ((real^2)^'n) set"
    and Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero :: "((real^2)^'n) set"
  assumes V_open: "open V" and V_nonempty: "V \<noteq> {}" and V_subset_Fset: "V \<subseteq> Fset"
    and meager_reg_nonzero:  "meager (Breg_nonzero \<inter> V)"
    and meager_reg_zero:     "meager (Breg_zero \<inter> V)"
    and meager_fold_zero:    "meager (Bfold_zero \<inter> V)"
    and meager_fold_nonzero: "meager (Bfold_nonzero \<inter> V)"
    and X0_sound:
      "\<And>x. x \<in> V - bad_union Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero
            \<Longrightarrow> \<exists>\<xi>>0. x \<in> X0 \<xi>"
  shows "\<exists>\<xi>>0. Fzero Fset X0 \<xi> \<noteq> {}"
  by (rule nonemptiness_from_meager_branches[OF assms])

text \<open>
  Existence-only alternative closeout: if each bad branch is Lebesgue-negligible
  in the nonempty open working set \<open>V\<close>, then the good set is nonempty (no Baire
  category needed).  This is weaker than the intended meager/genericity story,
  but it is often sufficient to obtain nonemptiness of the robust feasible set.
\<close>

theorem thm_final_negligible:
  fixes Fset V :: "((real^2)^'n) set"
    and X0 :: "real \<Rightarrow> ((real^2)^'n) set"
    and Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero :: "((real^2)^'n) set"
  assumes V_open: "open V" and V_nonempty: "V \<noteq> {}" and V_subset_Fset: "V \<subseteq> Fset"
    and neg_reg_nonzero:  "negligible (Breg_nonzero \<inter> V)"
    and neg_reg_zero:     "negligible (Breg_zero \<inter> V)"
    and neg_fold_zero:    "negligible (Bfold_zero \<inter> V)"
    and neg_fold_nonzero: "negligible (Bfold_nonzero \<inter> V)"
    and X0_sound:
      "\<And>x. x \<in> V - bad_union Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero
            \<Longrightarrow> \<exists>\<xi>>0. x \<in> X0 \<xi>"
  shows "\<exists>\<xi>>0. Fzero Fset X0 \<xi> \<noteq> {}"
  by (rule nonemptiness_from_negligible_branches[OF assms])

end
