theory Nonemptiness_Robust2
  imports Nonemptiness_Robust
begin

lemma M12_moment_applyT:
  fixes T :: "real^2^2"
  assumes "transpose T *v c = c0_paper"
  shows "M12_moment (applyT T y) c
       = of_real ((T $ 1 $ 1) * (T $ 2 $ 1)) * M11_moment y c0_paper
       + of_real ((T $ 1 $ 1) * (T $ 2 $ 2) + (T $ 1 $ 2) * (T $ 2 $ 1)) * M12_moment y c0_paper
       + of_real ((T $ 1 $ 2) * (T $ 2 $ 2)) * M22_moment y c0_paper"
proof -
  \<comment> \<open>Abbreviate the four matrix entries as scalars: the pointwise \<open>key\<close>
      identity otherwise carries ~24 vec-nth occurrences and hangs elaboration
      at parse time (the *-overload graph noted at \<^const>\<open>w_M12\<close>).  With the
      entries named, it parses immediately.\<close>
  define t11 where "t11 = T $ 1 $ 1"
  define t12 where "t12 = T $ 1 $ 2"
  define t21 where "t21 = T $ 2 $ 1"
  define t22 where "t22 = T $ 2 $ 2"
  have key: "\<And>n.
       phase c (applyT T y) n * of_real (w_M12 (applyT T y $ n))
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22))"
  proof -
    fix n
    have ph: "phase c (applyT T y) n = phase c0_paper y n"
      by (rule phase_applyT[OF assms])
    have lin1: "(applyT T y $ n) $ 1 = t11 * (y $ n) $ 1 + t12 * (y $ n) $ 2"
      unfolding t11_def t12_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    have lin2: "(applyT T y $ n) $ 2 = t21 * (y $ n) $ 1 + t22 * (y $ n) $ 2"
      unfolding t21_def t22_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    show "phase c (applyT T y) n * of_real (w_M12 (applyT T y $ n))
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22))"
      using ph lin1 lin2
      by (simp add: w_M12_def of_real_add of_real_mult power2_eq_square algebra_simps)
  qed

  have sum_key:
    "(\<Sum>n\<in>UNIV. phase c (applyT T y) n * of_real (w_M12 (applyT T y $ n)))
     =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22)))"
  proof -
    have "(\<Sum>n\<in>UNIV. phase c (applyT T y) n * of_real (w_M12 (applyT T y $ n)))
       =
      (\<Sum>n\<in>UNIV.
         phase c0_paper y n
           * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
           * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
           * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22)))"
      by (rule sum.cong, rule refl, simp add: key)
    also have "\<dots> =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22)))"
      by (simp add: sum.distrib add.assoc)
    finally show ?thesis .
  qed

  show ?thesis
      unfolding M11_moment_def M12_moment_def M22_moment_def
      using sum_key[unfolded t11_def t12_def t21_def t22_def]
      by (simp add: sum_distrib_left algebra_simps power2_eq_square ac_simps)
qed


text \<open>\<^bold>\<open>[E] brick 4a: the vector moment law.\<close>  Bundling the six \<open>*_moment_applyT\<close>
  laws into one equation \<open>M_paper(applyT T y) c = L\<^sub>T (M_paper y c\<^sub>0)\<close>.  The four matrix
  entries are named \<open>a,b,p,q\<close> via \<^theory_text>\<open>defines\<close> so the explicit transported vector parses
  (a bare \<open>T$i$j\<close> form would carry ~16 vec-nth occurrences and hang elaboration).\<close>

lemma M_paper_applyT:
  fixes T :: "real^2^2" and a b p q :: real
  assumes Tc: "transpose T *v c = c0_paper"
  defines "a \<equiv> T $ 1 $ 1" and "b \<equiv> T $ 1 $ 2"
      and "p \<equiv> T $ 2 $ 1" and "q \<equiv> T $ 2 $ 2"
  shows "M_paper (applyT T y) c = vector
    [ A_moment y c0_paper,
      of_real a * M1_moment y c0_paper + of_real b * M2_moment y c0_paper,
      of_real p * M1_moment y c0_paper + of_real q * M2_moment y c0_paper,
      of_real (a\<^sup>2) * M11_moment y c0_paper
        + of_real (2 * a * b) * M12_moment y c0_paper
        + of_real (b\<^sup>2) * M22_moment y c0_paper,
      of_real (a * p) * M11_moment y c0_paper
        + of_real (a * q + b * p) * M12_moment y c0_paper
        + of_real (b * q) * M22_moment y c0_paper,
      of_real (p\<^sup>2) * M11_moment y c0_paper
        + of_real (2 * p * q) * M12_moment y c0_paper
        + of_real (q\<^sup>2) * M22_moment y c0_paper ]"
proof (subst Finite_Cartesian_Product.vec_eq_iff, intro allI)
  fix i :: 6
  consider "i = 1" | "i = 2" | "i = 3" | "i = 4" | "i = 5" | "i = 6"
    using exhaust_6 by metis
  then show "M_paper (applyT T y) c $ i =
      vector
        [ A_moment y c0_paper,
          of_real a * M1_moment y c0_paper + of_real b * M2_moment y c0_paper,
          of_real p * M1_moment y c0_paper + of_real q * M2_moment y c0_paper,
          of_real (a\<^sup>2) * M11_moment y c0_paper
            + of_real (2 * a * b) * M12_moment y c0_paper
            + of_real (b\<^sup>2) * M22_moment y c0_paper,
          of_real (a * p) * M11_moment y c0_paper
            + of_real (a * q + b * p) * M12_moment y c0_paper
            + of_real (b * q) * M22_moment y c0_paper,
          of_real (p\<^sup>2) * M11_moment y c0_paper
            + of_real (2 * p * q) * M12_moment y c0_paper
            + of_real (q\<^sup>2) * M22_moment y c0_paper ] $ i"
  proof cases
    case 1 then show ?thesis
      by (simp add: A_moment_applyT[OF Tc] vector_def)
  next
    case 2 then show ?thesis
      unfolding a_def b_def by (simp add: M1_moment_applyT[OF Tc] vector_def)
  next
    case 3 then show ?thesis
      unfolding p_def q_def by (simp add: M2_moment_applyT[OF Tc] vector_def)
  next
    case 4 then show ?thesis
      unfolding a_def b_def by (simp add: M11_moment_applyT[OF Tc] vector_def)
  next
    case 5 then show ?thesis
      unfolding a_def b_def p_def q_def
      by (simp add: M12_moment_applyT[OF Tc] vector_def)
  next
    case 6 then show ?thesis
      unfolding p_def q_def by (simp add: M22_moment_applyT[OF Tc] vector_def)
  qed
qed


text \<open>\<^bold>\<open>[E] brick 4b: the \<open>Sym\<^sup>2\<close> block is invertible.\<close>  The second-order transport
  block --- the \<open>3\<times>3\<close> matrix carrying \<open>(M\<^sub>1\<^sub>1, M\<^sub>1\<^sub>2, M\<^sub>2\<^sub>2)\<close> --- is the symmetric square
  of \<open>T = ((a,b),(p,q))\<close>.  Its determinant is \<open>(det T)\<^sup>3 = (aq - bp)\<^sup>3\<close>, so it is
  invertible exactly when \<open>T\<close> is.  This is the one genuinely nonlinear step of the
  steering transport.\<close>

definition Smat :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^3^3" where
  "Smat a b p q = vector
    [ vector [a\<^sup>2,    2 * a * b,      b\<^sup>2],
      vector [a * p,  a * q + b * p,  b * q],
      vector [p\<^sup>2,    2 * p * q,      q\<^sup>2] ]"

lemma det_Smat:
  "det (Smat a b p q) = (a * q - b * p) ^ 3"
  unfolding Smat_def
  by (simp add: det_3 vector_3 power2_eq_square power3_eq_cube algebra_simps)

lemma invertible_Smat:
  assumes "a * q - b * p \<noteq> 0"
  shows "invertible (Smat a b p q)"
proof -
  have "det (Smat a b p q) = (a * q - b * p) ^ 3" by (rule det_Smat)
  with assms have "det (Smat a b p q) \<noteq> 0" by simp
  thus ?thesis by (simp add: invertible_det_nz)
qed


lemma DM_paper_x_regular_point_exists:
  fixes c :: planar
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x0::(real^2)^'n. surj (DM_paper_x x0 c)"
  sorry

text \<open>\<^bold>\<open>(M2) Open-dense submersion at a fixed nonzero wavevector.\<close>  From one regular point (M1) plus
  lower semicontinuity of rank (\<open>rank_lower_semicont_open_dense_propagation\<close>, currently a \<open>sorry\<close> in
  \<open>Nonemptiness_Paper\<close>), the moment-map derivative is surjective on an open dense subset of any open
  \<open>V\<close>.  This is the general-wavevector analogue of \<open>DM_paper_open_dense_surjective\<close>.\<close>

lemma DM_paper_x_open_dense_surjective_gen:
  fixes V :: "((real^2)^'n) set" and c :: planar
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)" and "c \<noteq> 0"
  shows "\<exists>U. open U \<and> U \<subseteq> V \<and> V \<subseteq> closure U \<and> (\<forall>x\<in>U. surj (DM_paper_x x c))"
  sorry

text \<open>\<^bold>\<open>(M3) The steering-singular angle locus is nowhere dense.\<close>  \<open>Dcvec_dip\<close> is real-analytic in
  \<open>\<omega>\<close> and not everywhere singular, so its singular set is a proper analytic subset --- closed with
  empty interior.\<close>

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

lemma pythagorean_squared:
  fixes m :: real
  shows
    "cos m * (cos m * (cos m * cos m))
      + (sin m * (sin m * (sin m * sin m))
      + cos m * (cos m * (sin m * (sin m * 2)))) = 1"
proof -
  let ?c = "cos m"
  let ?s = "sin m"

  have cs: "?c * ?c + ?s * ?s = 1"
    using sin_cos_squared_add[of m]
    by (simp add: power2_eq_square add.commute)

  have
    "?c * (?c * (?c * ?c))
      + (?s * (?s * (?s * ?s))
      + ?c * (?c * (?s * (?s * 2))))
     = (?c * ?c + ?s * ?s) * (?c * ?c + ?s * ?s)"
    by (smt (verit, del_insts) Groups.mult_ac(2) ab_semigroup_mult_class.mult_ac(1) 
        mult_2 mult_hom.hom_add)
  also have "... = 1"
    using cs by simp
  finally show ?thesis.
qed

lemma sin_cos_lin_not_const0:
    fixes M a b :: real
    assumes ab: "a < b"
    shows "\<exists>s. a < s \<and> s < b \<and> sin s * (cos s -
  sin s * M) \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence Z: "\<And>s. a < s \<Longrightarrow> s < b
  \<Longrightarrow> sin s * (cos s - sin s * M) = 0" by auto
    define F  where "F  = (\<lambda>s::real. sin s * (cos s - sin s
  * M))"
    define F1 where "F1 = (\<lambda>s::real. (cos s * cos s - sin s
  * sin s) - M * (2 * sin s * cos s))"
    define F2 where "F2 = (\<lambda>s::real. - (4 * (sin s * cos
  s)) - M * (2 * (cos s * cos s - sin s * sin s)))"
    have FZ:  "F s = 0" if "a < s" "s < b" for s using Z[OF that]
  by (simp add: F_def)
    have dF:  "(F  has_real_derivative F1 s) (at s)" for s
      unfolding F_def F1_def by (auto intro!: derivative_eq_intros
  simp: algebra_simps)
    have dF1: "(F1 has_real_derivative F2 s) (at s)" for s
      unfolding F1_def F2_def by (auto intro!: derivative_eq_intros
  simp: algebra_simps)
    have F1Z: "F1 s = 0" if "a < s" "s < b" for s
    proof -
      have "(F has_real_derivative 0) (at s)"
      proof (rule has_field_derivative_transform_within_open[where
  f = "\<lambda>_. 0" and S = "{a<..<b}"])
        show "((\<lambda>_. 0::real) has_real_derivative 0) (at s)"
  by (rule DERIV_const)
        show "open {a<..<b}" by simp
        show "s \<in> {a<..<b}" using that by simp
        show "\<And>y. y \<in> {a<..<b} \<Longrightarrow> (0::real) = F y" 
          using FZ by simp
      qed   
      with dF[of s] show "F1 s = 0" by (metis DERIV_unique)
    qed
    define m where "m = (a + b) / 2"
    have m_mem: "m \<in> {a<..<b}" using ab by (simp add: m_def)
    have e1: "F1 m = 0" using F1Z m_mem by simp
    have "(F1 has_real_derivative 0) (at m)"
    proof (rule has_field_derivative_transform_within_open[where f
  = "\<lambda>_. 0" and S = "{a<..<b}"])
      show "((\<lambda>_. 0::real) has_real_derivative 0) (at m)"
        by (rule DERIV_const)
      show "open {a<..<b}" by simp
      show "m \<in> {a<..<b}" using m_mem by simp
      show "\<And>y. y \<in> {a<..<b} \<Longrightarrow> (0::real) =  F1 y" using F1Z by simp
    qed
    with dF1[of m] have e2: "F2 m = 0" by (metis DERIV_unique)
    define X where "X = cos m * cos m - sin m * sin m"
    define Y where "Y = 2 * sin m * cos m"
    have pyth: "X * X + Y * Y = 1" 
      using sin_cos_squared_add[of m] using pythagorean_squared
      by (simp add: X_def Y_def power2_eq_square algebra_simps)
    have eq1: "X - M * Y = 0" using e1 by (simp add: F1_def X_def
  Y_def)
    have eq2: "Y + M * X = 0" using e2 by (simp add: F2_def X_def
  Y_def algebra_simps)
    have "(1 + M * M) * X = 0" 
      using eq1 eq2 by (smt (verit, del_insts) mult_not_zero zero_le_mult_iff)
    hence "X = 0"
      by (metis more_arith_simps(6) mult_eq_0_iff sum_squares_eq_zero_iff) 
    moreover from this eq2 have "Y = 0" by simp
    ultimately show False using pyth by simp
  qed


lemma steering_singular_nowhere_dense:
    shows "nowhere_dense {\<omega>::angle. det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  proof -   
    define g where "g = (\<lambda>u::real. ((kx \<omega>0 - kx
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * cos u
                                   + ((ky \<omega>0 - ky
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * sin u)"
    define f where "f = (\<lambda>\<omega>::real^2. sin
  (\<omega>$1) * (cos (\<omega>$1) - sin (\<omega>$1) * g
  (\<omega>$2)))"
    have feq: "{\<omega>::angle. det (matrix (Dcvec_dip \<omega>0
  \<omega>s \<omega>)) = 0} = {\<omega>. f \<omega> = 0}"
      by (simp add: f_def g_def Dcvec_det_eq)
    have contf: "continuous_on UNIV f"
      unfolding f_def g_def
      by (intro continuous_intros bounded_linear.continuous_on[OF bounded_linear_vec_nth])
    have closedE: "closed {\<omega>::real^2. f \<omega> = 0}"
      by (rule closed_Collect_eq[OF contf continuous_on_const])
    have intE: "interior {\<omega>::real^2. f \<omega> = 0} = {}"
    proof (rule ccontr)
      assume "interior {\<omega>. f \<omega> = 0} \<noteq> {}"
      then obtain c where "c \<in> interior {\<omega>. f \<omega> =
  0}" by blast
      then obtain r where r: "0 < r" and bsub: "ball c r  \<subseteq> {\<omega>. f \<omega> = 0}"
        using mem_interior by blast
      have inb: "sin s * (cos s - sin s * g (c$2)) = 0" if hs:
  "\<bar>s - c$1\<bar> < r" for s
      proof -
        have "vector [s, c$2] - c = axis 1 (s - c$1)"
          by (simp add: vec_eq_iff forall_2 vector_2 axis_def,
              smt (verit, del_insts) Finite_Cartesian_Product.minus_vec_def 
              exhaust_2 vec_lambda_unique vector_2(1,2) verit_minus_simplify(1))
        hence "dist (vector [s, c$2] :: real^2) c = \<bar>s -  c$1\<bar>"
          by (simp add: dist_norm norm_eq_sqrt_inner inner_axis_axis)
        hence "vector [s, c$2] \<in> ball c r" using hs by (simp add: dist_commute)
        hence "f (vector [s, c$2]) = 0" using bsub by blast
        thus ?thesis by (simp add: f_def vector_2)
      qed
      have lt: "c$1 - r < c$1 + r" using r by simp
      obtain s where "c$1 - r < s" "s < c$1 + r" "sin s * (cos s - sin s * g (c$2)) \<noteq> 0"
        using sin_cos_lin_not_const0[where M = "g (c$2)" and a = "c$1 - r" and b = "c$1 + r"] lt 
        by blast
      moreover from this have "\<bar>s - c$1\<bar> < r" by simp
      ultimately show False using inb by blast
    qed
    show ?thesis
      using closedE intE by (simp add: feq nowhere_dense_def closure_closed)
  qed

text \<open>\<^bold>\<open>(M4) Regular stratum is meager.\<close>  On the open locus where \<open>A \<noteq> 0\<close>, \<open>surj (DM_paper_x \<dots>)\<close>,
  and \<open>det (Dcvec) \<noteq> 0\<close>, \<open>0\<close> is a regular value (@{thm regular_value_on_gradU_dip}); covering this
  open (non-product) locus by countably many product boxes and applying
  {thm parametric_transversality_meager_planar_config} on each, the degenerate-critical projection
  over the regular stratum is meager.\<close>

lemma meager_bad_regular_stratum:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  sorry

text \<open>\<^bold>\<open>(M5) Rank-deficient stratum is meager.\<close>  The set of configurations carrying a degenerate
  critical point (with \<open>A \<noteq> 0\<close>) at an angle where the moment map \<^emph>\<open>fails\<close> to be a submersion.  This
  is the projection of a positive-codimension set; meager by the \<open>m_star = 0\<close> nowhere-density (M2)
  combined with a parametric argument over \<open>\<omega>\<close>.\<close>

lemma meager_rank_deficient_stratum:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  sorry

text \<open>\<^bold>\<open>(M6) Steering-singular stratum is meager.\<close>  Degenerate critical points (with \<open>A \<noteq> 0\<close>) at an
  angle where the steering Jacobian is singular.  Meager by (M3): the singular-\<open>\<omega>\<close> locus is
  nowhere dense, and the critical points over it form a positive-codimension set.\<close>

lemma meager_steering_singular_stratum:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  sorry

text \<open>\<^bold>\<open>(M6b) The \<open>A = 0\<close> degenerate stratum is meager --- ADDED (soundness).\<close>  The bad set in
  M4--M6 carries \<open>A \<noteq> 0\<close> (the transversality argument needs it).  But every array-factor null
  \<open>A_cart = 0\<close> is itself a critical point (\<open>\<nabla>\<^sub>\<Omega>U = g \<nabla>\<bar>A\<bar>\<^sup>2 + \<bar>A\<bar>\<^sup>2 \<nabla>g = 0\<close> at \<open>A = 0\<close>), so a
  \<^emph>\<open>degenerate\<close> null also breaks regularity and must be excluded.  The locus \<open>{A = 0 \<and> det \<nabla>\<^sup>2U = 0}\<close>
  is \<open>3\<close> real conditions on \<open>(\<bm>x,\<omega>)\<close> (codim \<open>3\<close>): its \<open>\<bm>x\<close>-projection is meager.\<close>

lemma meager_Azero_degenerate_stratum:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
  sorry

text \<open>\<^bold>\<open>(M7) The dipole-specific bad set is meager --- CORRECTED to the FULL set.\<close>  By @{thm
  Phibad_dip_imp_detHess0}, \<open>\<Phi> = 0\<close> gives \<open>\<nabla>\<^sub>\<Omega>U = 0 \<and> det (\<nabla>\<^sup>2U) = 0\<close>; then every witnessing \<open>\<omega>\<close> falls
  into exactly one of \<^bold>\<open>four\<close> strata --- regular (M4), rank-deficient (M5), steering-singular (M6),
  or array-null \<open>A = 0\<close> (M6b) --- whose union is meager.  \<^bold>\<open>SOUNDNESS FIX:\<close> the conclusion is now the
  \<^bold>\<open>full\<close> degenerate-critical set \<open>{\<exists>\<omega>. \<Phi> = 0}\<close> (no spurious \<open>A \<noteq> 0\<close>), so its complement gives a point
  with \<^emph>\<open>no\<close> degenerate critical at any \<open>\<omega>\<close> --- what the capstone actually needs.  \<^bold>\<open>This is the lemma
  the capstone consumes\<close>, in place of the unprovable generic \<open>Phi_bad_meager\<close>.\<close>

lemma Phi_bad_meager_dip:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
proof -
  let ?reg = "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  let ?def = "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  let ?steer = "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  let ?null = "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
  have meag4: "meager (?reg \<union> ?def \<union> ?steer \<union> ?null)"
    by (intro meager_Un meager_bad_regular_stratum[OF assms]
              meager_rank_deficient_stratum[OF assms]
              meager_steering_singular_stratum[OF assms]
              meager_Azero_degenerate_stratum[OF assms])
  have sub: "{x \<in> V. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}
             \<subseteq> ?reg \<union> ?def \<union> ?steer \<union> ?null"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    then obtain \<omega> where xV: "x \<in> V"
      and pb: "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    from Phibad_dip_imp_detHess0[OF pb]
    have g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and d0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" by blast+
    show "x \<in> ?reg \<union> ?def \<union> ?steer \<union> ?null"
      using xV g0 d0
      by fastforce 
  qed
  show ?thesis by (rule meager_subset[OF sub meag4])
qed


subsection \<open>The capstone: \<open>\<F>\<^sub>0\<close> is nonempty for appropriately chosen \<open>\<xi>, \<kappa>, \<epsilon>\<close>\<close>

text \<open>TeX Lemma~\eqref{F0} (D_edit_May18, the 2-D version, L1288/F0\_nonempty\_proof\_2D):
  for appropriately chosen \<open>\<xi>,\<kappa>,\<epsilon> > 0\<close>, \<open>\<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = \<F> \<inter> X\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close> is nonempty.

  \<^bold>\<open>No regularity is assumed.\<close>  The analytic input --- a feasible \<open>x\<^sub>0\<close> whose pattern is
  \<^emph>\<open>regular\<close> (\<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> on the \<open>\<epsilon>\<close>-sphere, and \<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> or \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> on \<open>\<Omega>\<^sup>~\<close>) ---
  is a \<^emph>\<open>consequence\<close> of \<open>Phi_bad_meager\<close> + Baire (the degenerate configurations are
  meager, so their complement inside the open interior of the feasible body is dense and
  in particular nonempty), packaged for the actual pattern as the obligation
  \<open>regular_feasible_point_dip\<close> below.  This is precisely what the determinant computation was
  for.  Given that point, the margins \<open>\<kappa> = min\<^bsub>\<partial>B\<^sub>\<epsilon>\<^esub>\<parallel>\<nabla>\<^sub>\<Omega>U\<parallel>\<close> and
  \<open>\<xi> = min\<^bsub>\<Omega>\<^sup>~\<^esub>(\<parallel>\<nabla>\<^sub>\<Omega>U\<parallel> + \<sigma>\<^sub>m\<^sub>i\<^sub>n(H))\<close> are positive by Weierstrass, and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.
  We split the analytic core (\<open>F0_nonempty_of_witness\<close>) from the witness, so the concrete
  dipole capstone \<open>F0_dip_nonempty\<close> discharges the \<^emph>\<open>continuity\<close> half from proven facts and
  leaves only the genuine existence-of-a-regular-feasible-point hole.\<close>

lemma mem_imp_ne_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}" by blast

text \<open>\<^bold>\<open>The capstone core, parametrised by the regular feasible witness.\<close>  Given a feasible
  \<open>x\<^sub>0\<close> and radius \<open>\<epsilon>>0\<close> whose pattern is regular --- gradient nonvanishing on the
  \<open>\<epsilon>\<close>-sphere, gradient-or-nondegenerate on the annulus, with the relevant norms continuous
  --- the positive margins \<open>\<kappa>,\<xi>\<close> exist by Weierstrass and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.  This is the
  purely analytic half of \<open>F0_nonempty\<close>; the witness itself (the determinant/Baire payoff)
  is the separate obligation.  Isolating it lets the \<^emph>\<open>concrete dipole\<close> capstone discharge
  the continuity conjuncts from the proven @{thm norm_gradU_dip_continuous_on} /
  @{thm sigma_min_HessU_dip_continuous_on}, rather than assuming them.\<close>

lemma F0_nonempty_of_witness:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real"
    and R dmin A B D \<delta>null pmin :: real and \<omega>null ctr :: planar
    and x0 :: "planar^'n" and \<epsilon> :: real
  assumes \<epsilon>0: "0 < \<epsilon>"
    and feas: "x0 \<in> Ffeas cvec g R dmin A B D \<omega>null ctr \<delta>null pmin"
    and cdN: "continuous_on (sphere ctr \<epsilon>) (\<lambda>\<omega>. norm (gradU cvec g x0 \<omega>))"
    and cdsum: "continuous_on (Omega ctr - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
    and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU cvec g x0 \<omega> \<noteq> 0"
    and rO: "\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                gradU cvec g x0 y \<noteq> 0 \<or> 0 < sigma_min (HessU cvec g x0 y)"
  shows "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
            \<and> F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>
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
  proof (cases "Omega ctr - ball ctr \<epsilon> = {}")
    case True
    have "x0 \<in> X0 cvec g ctr (Omega ctr) 1 \<kappa> \<epsilon>"
      using inXrob True unfolding X0_def by blast
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin 1 \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin 1 \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    moreover have "(0::real) < 1" by simp
    ultimately show ?thesis using \<kappa>pos \<epsilon>0 by blast
  next
    case False
    obtain ym where ym: "ym \<in> Omega ctr - ball ctr \<epsilon>"
        and ymin: "\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
              norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)
              \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y)"
      using continuous_attains_inf[OF Omega_minus_ball_compact False cdsum] by blast
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
          \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                \<xi> \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
      using inXrob ymin unfolding \<xi>_def by blast
    hence "x0 \<in> X0 cvec g ctr (Omega ctr) \<xi> \<kappa> \<epsilon>" unfolding X0_def by simp
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    thus ?thesis using \<xi>pos \<kappa>pos \<epsilon>0 by blast
  qed
qed

subsection \<open>The capstone for the ACTUAL dipole pattern \<open>U_dip\<close>\<close>

text \<open>\<^bold>\<open>The genuine remaining obligation, for the actual function.\<close>  Specialised to the
  concrete steered dipole \<open>cvec = cvec\<^sub>dip \<omega>\<^sub>0 \<omega>\<^sub>s\<close>, \<open>g = gain\<^sub>dip\<close>: there is a feasible
  configuration \<open>x\<^sub>0\<close> and radius \<open>\<epsilon>>0\<close> whose pattern is regular (gradient nonvanishing on
  \<open>\<partial>B\<^sub>\<epsilon>\<close>, gradient-or-nondegenerate on \<open>\<Omega>\<^sup>~\<close>).  This is \<^emph>\<open>exactly\<close> the determinant/Baire
  payoff (degenerate configs meager, @{thm Phi_bad_meager_dip} + Baire inside the feasible
  interior); crucially the \<^emph>\<open>continuity\<close> half is no longer part of this hole --- it is
  discharged below from the proven dipole facts.\<close>

text \<open>\<^bold>\<open>The Baire scaffold for \<open>regular_feasible_point_dip\<close> (\<^bold>\<open>statements only\<close>; proofs deferred).\<close>\<close>

text \<open>\<^bold>\<open>(C0) A nonzero smallest singular value is exactly invertibility.\<close>  For a real \<open>2\<times>2\<close>
  matrix the smallest singular value @{const sigma_min} is positive iff the determinant is
  nonzero --- the bridge between the degeneracy slot \<open>det (\<nabla>\<^sup>2U) = 0\<close> and the capstone's
  \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> nondegeneracy margin.\<close>

lemma sigma_min_pos_iff_invertible:
  fixes H :: "real^2^2"
  shows "0 < sigma_min H \<longleftrightarrow> det H \<noteq> 0"
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
  have det_iff: "inj ((*v) H) \<longleftrightarrow> det H \<noteq> 0"
    using det_nz_iff_inj[OF lin] by simp
  show ?thesis using nz_iff inj_iff det_iff by blast
qed

text \<open>\<^bold>\<open>(C1) The feasible body has nonempty interior (Slater).\<close>  If \<^emph>\<open>some\<close> configuration satisfies
  every constraint \<^emph>\<open>strictly\<close> --- all spacings exceed \<open>d\<^sub>min\<close>, the null power is below \<open>\<delta>\<^sub>null\<close>,
  the main power lies strictly between \<open>p\<^sub>min\<close> and the Cauchy--Schwarz cap, and \<open>\<parallel>\<bm>x\<parallel> < R\<close> --- then
  (each constraint function being continuous) that point is interior to @{const Ffeas}.  The
  hypothesis is the genuine strict-feasibility input; it does not mention \<open>interior\<close>.\<close>

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

text \<open>\<^bold>\<open>(C2) Baire: a regular configuration exists inside the feasible interior.\<close>  The degenerate
  configurations are meager (@{thm Phi_bad_meager_dip}, the \<^bold>\<open>full\<close> bad set, including \<open>A = 0\<close>), so
  their complement is comeager, hence dense, hence meets the nonempty open feasible interior ---
  yielding a feasible \<open>x\<^sub>0\<close> carrying \<^bold>\<open>no\<close> degenerate critical point at \<^bold>\<open>any\<close> \<open>\<omega>\<close> (\<open>\<Phi> \<noteq> 0\<close> everywhere).
  \<^bold>\<open>SOUNDNESS FIX:\<close> the conclusion no longer carries the spurious \<open>A \<noteq> 0\<close> --- array-factor nulls
  (\<open>A = 0\<close>) are critical points (\<open>\<nabla>\<^sub>\<Omega>U = 0\<close>) too, and a \<^emph>\<open>degenerate\<close> null would break the
  capstone's regularity, so it must also be excluded.\<close>

lemma regular_config_exists:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
    and int_ne: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
  shows "\<exists>x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                          :: ((real^2)^'n) set).
            \<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
proof -
  define I where "I = interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: ((real^2)^'n) set)"
  have openI: "open I" unfolding I_def by (rule open_interior)
  have Ine: "I \<noteq> {}" unfolding I_def by (rule int_ne)
  have meagB: "meager {x \<in> I. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    by (rule Phi_bad_meager_dip[OF openI Ine c6])
  have "\<not> I \<subseteq> {x \<in> I. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
  proof
    assume sub: "I \<subseteq> {x \<in> I. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    have "meager I" by (rule meager_subset[OF sub meagB])
    moreover have "\<not> meager I" by (rule open_nonempty_not_meager[OF openI Ine])
    ultimately show False by simp
  qed
  then obtain x0 where x0I: "x0 \<in> I"
    and x0nB: "x0 \<notin> {x \<in> I. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}" by blast
  have x0Iexp: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
    using x0I unfolding I_def by assumption
  have reg: "\<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
    using x0I x0nB by blast
  from x0Iexp reg
  have conjx0: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)
        \<and> (\<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)" by (rule conjI)
  \<comment> \<open>Composition fully established: \<open>x0Iexp\<close> (\<open>x0 \<in> interior\<close>) and \<open>reg\<close> (\<open>\<forall>\<omega>. \<Phi> \<noteq> 0\<close>) are the
      witness data.  Only the final \<^emph>\<open>bounded-existential introduction\<close> \<open>\<exists>x0\<in>interior. \<dots>\<close> with
      witness \<open>x0\<close> is left open --- a witness-instantiation tactic step (\<open>bexI\<close>/\<open>rule_tac x=x0\<close>)
      that needs live goal/type inspection to dispatch against the large \<open>interior (Ffeas \<dots>)\<close>
      term; it is mathematically immediate from \<open>x0Iexp\<close> and \<open>reg\<close>.\<close>
  show ?thesis
  proof (rule bexI[where x = x0])
    show "\<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0" by (rule reg)
  next
    show "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
      by (rule x0Iexp)
  qed
qed

text \<open>\<^bold>\<open>(C3) From ``no degenerate critical point'' to the sphere/annulus regularity.\<close>  If \<open>x\<^sub>0\<close> has
  no degenerate critical point in \<open>\<Omega>\<close> (at every \<open>\<omega>\<close>, either \<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> or \<open>det (\<nabla>\<^sup>2U) \<noteq> 0\<close>), then for
  a suitable radius \<open>\<epsilon> > 0\<close> the gradient is nonvanishing on the sphere \<open>\<partial>B\<^sub>\<epsilon>\<close> and
  gradient-or-nondegenerate on the annulus \<open>\<Omega> - B\<^sub>\<epsilon>\<close> --- exactly the conclusion shape of
  \<open>regular_feasible_point_dip\<close> below.  (Nondegenerate critical points are isolated, so \<open>\<epsilon>\<close> can dodge
  them; degeneracy \<open>det = 0\<close> is rephrased as \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n > 0\<close> via @{thm sigma_min_pos_iff_invertible}.)\<close>

lemma no_degenerate_to_sphere_annulus:
  fixes x0 :: "(real^2)^'n" and ctr \<omega>0 \<omega>s :: angle
  assumes "\<forall>\<omega>\<in>Omega ctr. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  shows "\<exists>\<epsilon>>0. (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
  sorry

lemma regular_feasible_point_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
    and feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: (planar^'n) set) \<noteq> {}"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
  \<comment> \<open>\<^bold>\<open>SOUNDNESS FIX:\<close> requires \<open>feasible\<close> (the feasible body has nonempty interior).  Without
      it the claim is false for infeasible parameters (e.g.\ \<open>pmin > gain_dip ctr * N\<^sup>2\<close> forces
      \<open>Ffeas = {}\<close>).  The composition below is \<^bold>\<open>machine-checked\<close>; only the leaf lemmas remain
      \<open>sorry\<close>.\<close>
proof -
  obtain x0 :: "planar^'n"
    where x0I: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
      and x0reg: "\<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
    using regular_config_exists[OF c6 feasible] by blast
  have x0F: "x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
    using x0I interior_subset by blast
  have nondeg: "\<forall>\<omega>\<in>Omega ctr. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  proof (intro ballI notI)
    fix \<omega> assume "\<omega> \<in> Omega ctr"
      and deg: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0"
    from deg have g: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0"
      and dz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0" by auto
    have e: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>)
              = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 1
                  * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 2 $ 2
                - (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2"
      by (rule det_2_symmetric[OF HessU_dip_symmetric])
    from e dz have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 1
                      * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 2 $ 2
                    = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2" by simp
    with g have "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0"
      using Phibad_zero_iff by blast
    with x0reg show False by simp
  qed
  obtain \<epsilon> :: real where \<epsilon>0: "0 < \<epsilon>"
      and sph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
      and ann: "\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    using no_degenerate_to_sphere_annulus[OF nondeg] by blast
  have c1: "0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
    using \<epsilon>0 x0F sph ann by (intro conjI)
  show ?thesis
  proof (rule exI[where x = x0], rule exI[where x = \<epsilon>])
    show "0 < \<epsilon>
          \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
          \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
          \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
      by (rule c1)
  qed
qed

text \<open>\<^bold>\<open>The regular feasible witness for the dipole, with continuity DISCHARGED.\<close>  We bolt the
  two Weierstrass continuity conjuncts --- proven sorry-free in
  @{thm norm_gradU_dip_continuous_on} and @{thm sigma_min_HessU_dip_continuous_on} --- onto
  the regular feasible point, so what remains assumed is purely the existence of that point.\<close>

lemma regular_feasible_witness_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
    and feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: (planar^'n) set) \<noteq> {}"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> continuous_on (sphere ctr \<epsilon>)
                  (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>))
            \<and> continuous_on (Omega ctr - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)
                       + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
proof -
  obtain x0 :: "planar^'n" and \<epsilon> :: real
    where \<epsilon>0: "0 < \<epsilon>"
      and feas: "x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
      and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
      and rO: "\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    using regular_feasible_point_dip[OF c6 feasible] by blast
  have c1: "continuous_on (sphere ctr \<epsilon>)
              (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>))"
    by (rule norm_gradU_dip_continuous_on)
  have c2: "continuous_on (Omega ctr - ball ctr \<epsilon>)
              (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)
                   + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
    by (intro continuous_on_add norm_gradU_dip_continuous_on
              sigma_min_HessU_dip_continuous_on)
  show ?thesis using \<epsilon>0 feas c1 c2 rsph rO by blast
qed

text \<open>\<^bold>\<open>The concrete capstone: \<open>\<F>\<^sub>0\<close> for the ACTUAL dipole pattern is nonempty.\<close>  This is
  \<open>thm:final\<close>'s nonemptiness for the real radiation intensity \<open>U_dip = g(\<omega>)\<bar>A(\<bm>x,\<omega>)\<bar>\<^sup>2\<close>
  with the steered wavevector \<open>cvec\<^sub>dip\<close> and the smooth dipole gain \<open>gain\<^sub>dip = \<bar>e(\<theta>)\<bar>\<^sup>2\<close>
  --- no abstract \<open>cvec\<close>/\<open>g\<close>.  The continuity half is fully proven; the only assumption is
  the regular feasible point (the determinant/Baire payoff, @{thm regular_feasible_point_dip}).\<close>

theorem F0_dip_nonempty:
  assumes c6: "6 \<le> CARD('n)"
  shows "\<exists>A B D \<omega>0 \<omega>s \<omega>null ctr R dmin \<delta>null pmin \<xi> \<kappa> \<epsilon>.
            0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>
              \<noteq> ({}::(planar^'n) set)"
  \<comment> \<open>\<^bold>\<open>Unconditional capstone.\<close>  The only hypothesis is the dimension restriction \<open>c6\<close>; the design
      (steering \<open>\<omega>\<^sub>0,\<omega>\<^sub>s,\<omega>\<^sub>null\<close>, geometry \<open>A,B,D\<close>, tolerances \<open>d\<^sub>min,\<delta>\<^sub>null,p\<^sub>min,R\<close> and margins) is
      \<^emph>\<open>delivered by the construction\<close>, not assumed.  Feasibility is discharged by the explicit
      Slater witness (@{thm feasible_witness_exists}): the actual \<open>cvec_dip\<close> nulls at \<open>\<omega>\<^sub>null\<close>
      (roots of unity, \<open>A(\<bm>x,\<omega>\<^sub>null)=0\<close>), the main-beam power is pinned to the cap for \<^emph>\<open>every\<close>
      configuration (@{thm Upow_at_main}: \<open>cvec_dip(\<omega>\<^sub>0)=0\<close>), and we pick \<open>p\<^sub>min,d\<^sub>min,\<delta>\<^sub>null\<close> to make
      the witness strictly feasible --- everything is under our control.\<close>
proof -
  define \<omega>0 :: planar where "\<omega>0 = vector [pi/2, 0]"
  define \<omega>s :: planar where "\<omega>s = vector [0, 0]"
  define \<omega>null :: planar where "\<omega>null = vector [pi, 0]"
  have hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    by (simp add: \<omega>s_def \<omega>0_def kz_def)
  have cn: "cvec_dip \<omega>0 \<omega>s \<omega>null \<noteq> 0"
  proof -
    have "cvec_dip \<omega>0 \<omega>s \<omega>null $ 1 = - 2"
      by (simp add: cvec_dip_def \<omega>0_def \<omega>s_def \<omega>null_def kx_def ky_def kz_def
                    sin_pi_half cos_pi_half axis_def)
    hence "cvec_dip \<omega>0 \<omega>s \<omega>null $ 1 \<noteq> 0" by simp
    thus ?thesis by (metis zero_index)
  qed
  have N1: "CARD('n) > 1" using c6 by simp
  have spos: "(0::real) < 1" by simp
  obtain x :: "planar^'n"
    where afz: "af (cvec_dip \<omega>0 \<omega>s) x \<omega>null = 0"
      and spac0: "\<forall>m m'. m \<noteq> m' \<longrightarrow> (1::real) \<le> spdist 0 0 1 (x $ m) (x $ m')"
    using feasible_witness_exists[OF N1 cn spos] by meson
  define R :: real where "R = norm x + 1"
  have g0pos: "0 < gain_dip \<omega>0"
  proof -
    have "sin (\<omega>0 $ 1) \<noteq> 0" by (simp add: \<omega>0_def sin_pi_half)
    hence "gain_dip \<omega>0 \<noteq> 0" by (rule gain_dip_nonzero_of_sin)
    moreover have "0 \<le> gain_dip \<omega>0" by (rule gain_dip_nonneg)
    ultimately show ?thesis by simp
  qed
  have feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
                    :: (planar^'n) set) \<noteq> {}"
  proof -
    have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. (1/2::real) < spdist 0 0 1 (x $ fst p) (x $ snd p)"
      using spac0 by fastforce
    have Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < 1"
      using afz by (simp add: Upow_def)
    have Pgt: "(0::real) < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0"
    proof -
      have "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0 = gain_dip \<omega>0 * (real CARD('n))\<^sup>2"
        by (rule Upow_at_main[OF hsep])
      moreover have "0 < (real CARD('n))\<^sup>2" using N1 by simp
      ultimately show ?thesis using mult_pos_pos[OF g0pos] by simp
    qed
    have inR: "x \<in> ball 0 R" by (simp add: R_def dist_norm)
    obtain \<rho> where \<rho>: "0 < \<rho>"
        and sub: "ball x \<rho> \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0"
      using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
    have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0)"
      by (rule interior_maximal[OF sub open_ball])
    moreover have "x \<in> ball x \<rho>" using \<rho> by simp
    ultimately show ?thesis by blast
  qed
  have "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 (Omega \<omega>0) 1 0 \<xi> \<kappa> \<epsilon>
              \<noteq> ({}::(planar^'n) set)"
    using regular_feasible_witness_dip[OF c6 feasible]
    by (blast intro: F0_nonempty_of_witness)
  thus ?thesis by blast
qed

end