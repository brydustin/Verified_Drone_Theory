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

text \<open>
  Parametric transversality is the missing analytic engine behind TeX
  Proposition~(Generic regular-stratum zeros are regular). We record it as one lemma
  so that later work can focus on proving it properly (likely via Sard on the
  projection from the joint zero set).
\<close>

lemma parametric_transversality_meager_stub:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}"
    and "open \<Omega>reg"
    and A_smooth: "(\<forall>z\<in>V\<times>\<Omega>reg. A differentiable at z)"
    and joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
  shows "meager {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg}"
proof -
  text \<open>
    This lemma is intended to be proved by the reusable Euclidean pipeline:

    1. Replace the complex equation \<open>A = 0\<close> by a real 2-vector equation
       \<open>G = (Re \<circ> A, Im \<circ> A)\<close>.
    2. From @{term joint_trans} conclude: \<open>0\<close> is a regular value of \<open>G\<close> on \<open>V\<times>\<Omega>reg\<close>.
    3. Use the (implicit-function-theorem based) regular value theorem to obtain a
       codim-2 embedded submanifold structure on the joint zero set
       \<open>M = {(x,\<omega>)\<in>V\<times>\<Omega>reg. G(x,\<omega>) = 0}\<close>, covered by countably many smooth charts.
    4. Show: failure of transversality of the slice \<open>\<omega> \<mapsto> A(x,\<omega>)\<close> occurs exactly at
       parameters \<open>x\<close> that are critical values of the projection \<open>\<pi> : M \<to> V\<close>.
    5. Apply Sard in each chart (via @{thm baby_Sard}) to obtain that the critical
       value set is Lebesgue-negligible in \<open>((real^2)^'n)\<close>.
    6. Convert negligible-to-meager using the lemmas below.
  \<close>

  (* Implemented later by reducing to the Euclidean pipeline theorem
     @{thm parametric_transversality_negligible_stub} and then using the
     negligible→meager lemmas in this file. *)
  show ?thesis
    sorry
qed

text \<open>
  Proof idea (to replace the \<open>sorry\<close>): let \<open>G(x,\<omega>) = (Re (A(x,\<omega>)), Im (A(x,\<omega>)))\<close>.
  The assumption @{term joint_trans} says \<open>0\<close> is a regular value of \<open>G\<close>, hence the joint
  zero set \<open>M = {(x,\<omega>)\<in>V\<times>\<Omega>reg. G(x,\<omega>) = 0}\<close> is a codimension-2 submanifold of
  \<open>V\<times>\<Omega>reg\<close>. For a fixed parameter \<open>x\<close>, failure of @{term "transverse0_on (\<lambda>\<omega>. A(x,\<omega>)) \<Omega>reg"}
  means there is a point \<open>(x,\<omega>)\<in>M\<close> where the derivative in the \<open>\<omega>\<close>-direction is not surjective.
  Standard parametric transversality identifies such \<open>x\<close> as critical values of the projection
  \<open>\<pi> : M \<to> V\<close>. One can then show the critical value set is Lebesgue-negligible using
  @{thm baby_Sard} (after representing \<open>M\<close> in local charts), and hence meager via the
  negligible-to-meager lemmas below.
\<close>

theorem prop_regzero:
  fixes V :: "((real^2)^'n) set" and \<Omega>reg :: "(real^2) set"
    and A :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> complex"
  assumes "open V" and "V \<noteq> {}" and "open \<Omega>reg"
    and A_smooth: "(\<forall>z\<in>V\<times>\<Omega>reg. A differentiable at z)"
    and joint_trans:
      "\<forall>(x,\<omega>)\<in>V\<times>\<Omega>reg. A (x,\<omega>) = 0 \<longrightarrow>
        (\<exists>F. ((\<lambda>z. A z) has_derivative F) (at (x,\<omega>) within V\<times>\<Omega>reg) \<and> surj F)"
  shows "meager {x\<in>V. \<not> transverse0_on (\<lambda>\<omega>. A (x,\<omega>)) \<Omega>reg}"
  by (rule parametric_transversality_meager_stub[OF assms(1-3) A_smooth joint_trans])


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

theorem lem_Efinite:
  shows True
  sorry

theorem prop_foldnonzero:
  shows True
  sorry


section \<open>Regular-Stratum Nonzero-A Degenerate Critical Points\<close>

theorem prop_regnonzero:
  shows True
  sorry


section \<open>Closeout\<close>

text \<open>
  TeX Theorem~(Odd-N nonemptiness). This should become a short composition proof:
  combine the four meagerness results, then apply
  \<open>nonemptiness_from_meager_branches\<close>.
\<close>

theorem thm_final:
  shows True
  sorry

end
