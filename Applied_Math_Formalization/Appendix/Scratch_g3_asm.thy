theory Scratch_g3_asm
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>Goal G3: the (M6) steering-singular stratum ASSEMBLY.  The two upstream
  lemmas \<open>gdip_deriv_zero_iff\<close> and \<open>M6_slice_nowhere_dense\<close> are being proven by
  sibling agents and are included here as stubbed stubs (spliced later).
  Everything else is proof-complete.\<close>

section \<open>Upstream stubs (sibling agents; spliced later)\<close>

lemma gdip_deriv_zero_iff:
  fixes \<theta> :: real
  assumes "sin \<theta> \<noteq> 0"
  shows "frechet_derivative gdip (at \<theta>) 1 = 0 \<longleftrightarrow> cos \<theta> = 0"
  sorry

lemma M6_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "nowhere_dense {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  sorry

section \<open>Proven helpers (verified in sibling scratch; inlined verbatim)\<close>

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

lemma frechet_gdip_zero_arg: "frechet_derivative gdip (at \<theta>) 0 = 0" for \<theta> :: real
  using linear_frechet_derivative[OF gdip_differentiable] linear_0 by blast

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

lemma meager_steering_singular_stratum_scratch:
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

end
