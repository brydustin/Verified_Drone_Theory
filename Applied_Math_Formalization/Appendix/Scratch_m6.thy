theory Scratch_m6
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>(M6) development: the steering-singular stratum.  STRUCTURE (diary
  2026-06-11): on the pole-free box the second column of \<open>Dcvec\<close> is
  \<open>sin\<theta>\<cdot>(-sin\<phi>, cos\<phi>) \<noteq> 0\<close>, so rank-1 degeneracy makes the columns dependent
  and criticality with \<open>A \<noteq> 0\<close> forces \<open>gdip'(\<theta>) = 0\<close> (the kernel-direction
  reduction); with strict monotonicity of \<open>gdip\<close> off \<open>\<pi>/2\<close> the witness angles
  are FINITELY many; each fixed-\<omega> slice is nowhere dense by the
  analytic-slice machinery (or empty when \<open>cvec = 0\<close>, via the \<open>surj DM\<close>
  conjunct).\<close>

section \<open>Brick R1: 2-dim column dependence\<close>

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

section \<open>Brick R2: the second steering column never vanishes off the poles\<close>

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

section \<open>Brick R3: the kernel-direction reduction\<close>

text \<open>At every M6 witness off the poles, the \<open>\<theta>\<close>-derivative of the dipole
  gain vanishes: criticality reads \<open>gd'\<bar>A\<bar>\<^sup>2 e\<^sub>1 + g J\<^sup>T w = 0\<close>; component 2 gives
  \<open>col\<^sub>2 \<bullet> w = 0\<close>; rank-1 dependence \<open>col\<^sub>1 = t col\<^sub>2\<close> kills the moment term in
  component 1, leaving \<open>gd' \<bar>A\<bar>\<^sup>2 = 0\<close> with \<open>\<bar>A\<bar>\<^sup>2 > 0\<close>.\<close>

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
  \<comment> \<open>the two component equations in scalar form\<close>
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
  \<comment> \<open>rank-1 dependence of the steering columns\<close>
  have c2nz: "col2 \<noteq> 0" unfolding col2_def by (rule Dcvec_col2_nz[OF pfw])
  have det0': "col1 $ 1 * col2 $ 2 - col2 $ 1 * col1 $ 2 = 0"
    using detz unfolding col1_def col2_def by (simp add: det_2 matrix_def)
  obtain t where t: "col1 = t *\<^sub>R col2"
    using cols_dependent_2d[OF det0' c2nz] by blast
  have Tt: "T (t *\<^sub>R col2) = t * T col2"
    unfolding T_def by (simp add: of_real_mult algebra_simps)
  \<comment> \<open>conclude\<close>
  have "gd * aa = 0" using e1 t Tt Tc2 by simp
  with aanz have "gd = 0" by simp
  thus ?thesis unfolding gd_def .
qed

section \<open>Brick R4: gdip-derivative zeros are exactly \<open>cos \<theta> = 0\<close> (off poles)\<close>

lemma gdip_deriv_zero_iff:
  fixes \<theta> :: real
  assumes "sin \<theta> \<noteq> 0"
  shows "frechet_derivative gdip (at \<theta>) 1 = 0 \<longleftrightarrow> cos \<theta> = 0"
  sorry

section \<open>Brick R5: fixed-\<omega> slices are nowhere dense\<close>

lemma M6_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "nowhere_dense {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  sorry

section \<open>(M6) assembly\<close>

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
  sorry

end
