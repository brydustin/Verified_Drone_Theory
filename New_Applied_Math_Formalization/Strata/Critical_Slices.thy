section \<open>The configurations critical at a fixed angle\<close>

theory Critical_Slices
  imports
    Null_Stratum
    Applied_Math_Pattern.Dipole_Gain_Derivatives
    Applied_Math_Analysis.Line_Entire_Functions
begin

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

lemma continuous_on_A_moment_config:
  fixes c :: "real^2"
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. A_moment y c)"
  unfolding A_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
        bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_first_moment_config:
  fixes c :: "real^2"
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. first_moment y c k)"
  unfolding first_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
        bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_slice_moments:
  fixes c :: "real^2" and q1 q2 :: complex
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
            * (q1 * first_moment y c 1 + q2 * first_moment y c 2)))"
  by (intro continuous_on_mult continuous_on_const continuous_on_add
        bounded_linear.continuous_on[OF bounded_linear_Re]
        bounded_linear.continuous_on[OF bounded_linear_cnj]
        continuous_on_A_moment_config continuous_on_first_moment_config)

lemma cline_entire_A_moment:
  fixes c :: "real^2"
  shows "cline_entire (\<lambda>y::(real^2)^'n. A_moment y c)"
  unfolding A_moment_def phase_def
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  assume "n \<in> (UNIV :: 'n set)"
  have bl: "bounded_linear (\<lambda>y::(real^2)^'n. - (c \<bullet> (y $ n)))"
    by (rule bounded_linear_minus[OF bounded_linear_compose
          [OF bounded_linear_inner_right bounded_linear_vec_nth]])
  show "cline_entire (\<lambda>y::(real^2)^'n. cis (- (c \<bullet> (y $ n))))"
    by (rule cline_entire_cis_linear[OF bl])
qed

lemma cline_entire_first_moment:
  fixes c :: "real^2"
  shows "cline_entire (\<lambda>y::(real^2)^'n. first_moment y c k)"
  unfolding first_moment_def phase_def
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  assume "n \<in> (UNIV :: 'n set)"
  have bl: "bounded_linear (\<lambda>y::(real^2)^'n. - (c \<bullet> (y $ n)))"
    by (rule bounded_linear_minus[OF bounded_linear_compose
          [OF bounded_linear_inner_right bounded_linear_vec_nth]])
  have blc: "bounded_linear (\<lambda>y::(real^2)^'n. (y $ n) $ k)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  show "cline_entire (\<lambda>y::(real^2)^'n. complex_of_real ((y $ n) $ k) * cis (- (c \<bullet> (y $ n))))"
    by (rule cline_entire_mult[OF cline_entire_of_real_linear[OF blc]
          cline_entire_cis_linear[OF bl]])
qed

lemma rline_entire_slice_moments:
  fixes c :: "real^2" and q1 q2 :: complex
  shows "rline_entire (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
            * (q1 * first_moment y c 1 + q2 * first_moment y c 2)))"
proof -
  have m1: "cline_entire (\<lambda>y::(real^2)^'n. q1 * first_moment y c 1)"
    by (rule cline_entire_mult[OF cline_entire_const cline_entire_first_moment])
  have m2: "cline_entire (\<lambda>y::(real^2)^'n. q2 * first_moment y c 2)"
    by (rule cline_entire_mult[OF cline_entire_const cline_entire_first_moment])
  have z: "cline_entire (\<lambda>y::(real^2)^'n. q1 * first_moment y c 1 + q2 * first_moment y c 2)"
    by (rule cline_entire_add[OF m1 m2])
  have w: "cline_entire (\<lambda>y::(real^2)^'n.
             cnj (A_moment y c) * (q1 * first_moment y c 1 + q2 * first_moment y c 2))"
    by (rule cline_entire_mult[OF cline_entire_cnj[OF cline_entire_A_moment] z])
  have r: "rline_entire (\<lambda>y::(real^2)^'n.
             Re (cnj (A_moment y c) * (q1 * first_moment y c 1 + q2 * first_moment y c 2)))"
    by (rule rline_entire_Re[OF w])
  show ?thesis by (rule rline_entire_scale[OF r])
qed

lemma slice_moments_witness:
  fixes c col2 :: "real^2"
  assumes cnz: "c \<noteq> 0" and c2nz: "col2 \<noteq> 0" and card2: "2 \<le> CARD('n)"
  shows "\<exists>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * first_moment y c 1
        + (- \<i>) * complex_of_real (col2 $ 2) * first_moment y c 2)) \<noteq> 0"
proof -
  \<comment> \<open>a direction seen by both \<open>c\<close> and \<open>col2\<close>\<close>
  have qex: "\<exists>q::real^2. c \<bullet> q \<noteq> 0 \<and> col2 \<bullet> q \<noteq> 0"
  proof (cases "col2 \<bullet> c = 0")
    case True
    have cc: "c \<bullet> c \<noteq> 0" using cnz by simp
    have c2c2: "col2 \<bullet> col2 \<noteq> 0" using c2nz by simp
    have e1: "c \<bullet> (c + col2) = c \<bullet> c"
      using True by (simp add: inner_add_right inner_commute)
    have e2: "col2 \<bullet> (c + col2) = col2 \<bullet> col2"
      using True by (simp add: inner_add_right)
    show ?thesis
      by (intro exI[of _ "c + col2"] conjI) (simp_all add: e1 e2 cnz c2nz)
  next
    case False
    have cc: "c \<bullet> c \<noteq> 0" using cnz by simp
    have "col2 \<bullet> c \<noteq> 0" using False by simp
    thus ?thesis using cc by (intro exI[of _ c] conjI)
  qed
  then obtain q :: "real^2" where cq: "c \<bullet> q \<noteq> 0" and colq: "col2 \<bullet> q \<noteq> 0"
    by (elim exE conjE)
  \<comment> \<open>the displaced position: phase \<open>\<pi>/2\<close> along \<open>c\<close>, nonzero \<open>col2\<close>-component\<close>
  define p :: "real^2" where "p = ((pi/2)/(c \<bullet> q)) *\<^sub>R q"
  have cp: "c \<bullet> p = pi/2"
    using cq unfolding p_def by (simp add: inner_scaleR_right)
  have Kp: "col2 \<bullet> p \<noteq> 0"
    using cq colq pi_gt_zero unfolding p_def by (auto simp: inner_scaleR_right)
  \<comment> \<open>one-displaced-element configuration\<close>
  define i0 :: 'n where "i0 = undefined"
  define xs :: "(real^2)^'n" where "xs = (\<chi> n. if n = i0 then p else 0)"
  have xsi: "xs $ i0 = p" by (simp add: xs_def)
  have split: "(\<Sum>n\<in>(UNIV::'n set). f n) = f i0 + (\<Sum>n\<in>UNIV - {i0}. f n)"
    for f :: "'n \<Rightarrow> complex"
    by (rule sum.remove) simp_all
  \<comment> \<open>the three moments at the witness\<close>
  have Ast: "A_moment xs c = - \<i> + of_nat (CARD('n) - 1)"
  proof -
    have 1: "A_moment xs c
        = cis (- (c \<bullet> (xs $ i0))) + (\<Sum>n\<in>UNIV - {i0}. cis (- (c \<bullet> (xs $ n))))"
      unfolding A_moment_def phase_def by (rule split)
    have 2: "(\<Sum>n\<in>UNIV - {i0}. cis (- (c \<bullet> (xs $ n)))) = (\<Sum>n\<in>(UNIV::'n set) - {i0}. 1)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    have 3: "(\<Sum>n\<in>(UNIV::'n set) - {i0}. (1::complex)) = of_nat (CARD('n) - 1)"
      by (simp add: card_Diff_singleton)
    show ?thesis using 1 2 3 cp xsi by simp
  qed
  have Mst: "first_moment xs c k = complex_of_real (p $ k) * (- \<i>)" for k
  proof -
    have 1: "first_moment xs c k
        = complex_of_real ((xs $ i0) $ k) * cis (- (c \<bullet> (xs $ i0)))
          + (\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ k) * cis (- (c \<bullet> (xs $ n))))"
      unfolding first_moment_def phase_def by (rule split)
    have 2: "(\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ k) * cis (- (c \<bullet> (xs $ n))))
        = (\<Sum>n\<in>(UNIV::'n set) - {i0}. 0)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    show ?thesis using 1 2 cp xsi by simp
  qed
  \<comment> \<open>the value of the slice function at the witness\<close>
  have Fval: "2 * Re (cnj (A_moment xs c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * first_moment xs c 1
        + (- \<i>) * complex_of_real (col2 $ 2) * first_moment xs c 2))
      = - (2 * real (CARD('n) - 1) * (col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2))"
    by (simp add: Ast Mst algebra_simps)
  have Kc: "col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2 = col2 \<bullet> p"
    by (simp add: inner_vec_def sum_2)
  have r1: "real (CARD('n) - 1) \<noteq> 0" using card2 by simp
  have nz: "- (2 * real (CARD('n) - 1) * (col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2)) \<noteq> 0"
    unfolding Kc using Kp r1 by simp
  have "2 * Re (cnj (A_moment xs c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * first_moment xs c 1
        + (- \<i>) * complex_of_real (col2 $ 2) * first_moment xs c 2)) \<noteq> 0"
    unfolding Fval by (rule nz)
  thus ?thesis by blast
qed

lemma slice_moments_nowhere_dense:
  fixes c col2 :: "real^2"
  assumes cnz: "c \<noteq> 0" and c2nz: "col2 \<noteq> 0" and card2: "2 \<le> CARD('n)"
  shows "nowhere_dense {y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * first_moment y c 1
        + (- \<i>) * complex_of_real (col2 $ 2) * first_moment y c 2)) = 0}"
proof -
  define B :: "(real^2)^'n \<Rightarrow> real" where
    "B = (\<lambda>y. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * first_moment y c 1
        + (- \<i>) * complex_of_real (col2 $ 2) * first_moment y c 2)))"
  have cont: "continuous_on UNIV B"
    unfolding B_def by (rule continuous_on_slice_moments)
  have rl: "rline_entire B"
    unfolding B_def by (rule rline_entire_slice_moments)
  have ntv: "\<exists>y. B y \<noteq> 0"
    unfolding B_def by (rule slice_moments_witness[OF cnz c2nz card2])
  have nd: "nowhere_dense {y \<in> (UNIV :: ((real^2)^'n) set). B y = 0}"
  proof (rule lines_entire_slice_nowhere_dense[OF cont _ ntv])
    show "\<And>a v. \<exists>G. G holomorphic_on UNIV
            \<and> (\<forall>t::real. G (complex_of_real t) = complex_of_real (B (a + t *\<^sub>R v)))"
      using rl unfolding rline_entire_def by blast
  qed
  have seq: "{y \<in> (UNIV :: ((real^2)^'n) set). B y = 0} = {y::(real^2)^'n. B y = 0}"
    by auto
  have nd': "nowhere_dense {y::(real^2)^'n. B y = 0}"
    using nd unfolding seq .
  show ?thesis using nd' unfolding B_def .
qed

lemma critical_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes card2: "2 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and cnz0: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "nowhere_dense {x :: (real^2)^'n. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
proof -
  define c :: "real^2" where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define col2 :: "real^2" where "col2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  define F :: "(real^2)^'n \<Rightarrow> real" where
    "F = (\<lambda>y. 2 * Re (cnj (moment_map y c $ 1)
       * ((- \<i>) * complex_of_real (col2 $ 1) * (moment_map y c $ 2)
        + (- \<i>) * complex_of_real (col2 $ 2) * (moment_map y c $ 3))))"
  have cnz: "c \<noteq> 0" using cnz0 by (simp add: c_def)
  have c2nz: "col2 \<noteq> 0" unfolding col2_def by (rule Dcvec_col2_nz[OF pfw])
  have gnz: "gain_dip \<omega> \<noteq> 0" by (rule gain_dip_nonzero_of_sin[OF pfw])
  have Feq: "F = (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * first_moment y c 1
        + (- \<i>) * complex_of_real (col2 $ 2) * first_moment y c 2)))"
    unfolding F_def by simp
  have ndF: "nowhere_dense {y::(real^2)^'n. F y = 0}"
    unfolding Feq by (rule slice_moments_nowhere_dense[OF cnz c2nz card2])
  have sub: "{x :: (real^2)^'n. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}
      \<subseteq> {y::(real^2)^'n. F y = 0}"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x :: (real^2)^'n. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    hence g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    have comp2: "gain_dip \<omega> * F x = gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2"
      unfolding F_def c_def col2_def
      using frechet_gdip_zero_arg[of "\<omega>$1"]
      by (simp add: gradU_dip_component_moments axis_def)
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 = 0" using g0 by simp
    hence "gain_dip \<omega> * F x = 0" using comp2 by simp
    hence "F x = 0" using gnz by simp
    thus "x \<in> {y::(real^2)^'n. F y = 0}" by simp
  qed
  show ?thesis by (rule nowhere_dense_subset[OF sub ndF])
qed

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

lemma steering_singular_gdip_deriv_zero:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
    and detz: "matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
  shows "frechet_derivative gdip (at (\<omega>$1)) 1 = 0"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define gd where "gd = frechet_derivative gdip (at (\<omega>$1)) 1"
  define aa where "aa = (cmod (moment_map x c $ 1))\<^sup>2"
  define g where "g = gain_dip \<omega>"
  define col1 where "col1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)"
  define col2 where "col2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  define T :: "(real^2) \<Rightarrow> real"
    where "T v = 2 * Re (cnj (moment_map x c $ 1)
       * ((- \<i>) * complex_of_real (v $ 1) * (moment_map x c $ 2)
        + (- \<i>) * complex_of_real (v $ 2) * (moment_map x c $ 3)))" for v
  have gnz: "g \<noteq> 0"
    unfolding g_def using pfw by (rule gain_dip_nonzero_of_sin)
  have aanz: "0 < aa"
  proof -
    have "moment_map x c $ 1 = A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>"
      unfolding c_def by (rule moment_map_proj_A)
    hence "moment_map x c $ 1 \<noteq> 0" using anz by simp
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

end
