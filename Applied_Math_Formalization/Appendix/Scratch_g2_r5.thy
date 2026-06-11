theory Scratch_g2_r5
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>(G2) Brick R5 of the M6 stratum: the fixed-\<open>\<omega>\<close> steering-singular slices are
  nowhere dense.  CASE \<open>cvec = 0\<close>: the slice is empty because the first component of
  \<open>DM_paper_x\<close> degenerates to \<open>0\<close>, killing surjectivity.  CASE \<open>cvec \<noteq> 0\<close>: criticality
  component 2 forces the moment expression \<open>F\<close> (built from \<open>col\<^sub>2 = Dcvec(e\<^sub>2)\<close>) to vanish,
  and \<open>{F = 0}\<close> is nowhere dense by the analytic-slice engine
  (\<open>lines_entire_slice_nowhere_dense\<close>): \<open>F\<close> is continuous, has entire line restrictions,
  and is not identically zero (one-displaced-element witness).\<close>

section \<open>Generic topology helper\<close>

lemma nowhere_dense_subset:
  fixes A B :: "'a::topological_space set"
  assumes sub: "A \<subseteq> B" and nd: "nowhere_dense B"
  shows "nowhere_dense A"
proof -
  have "interior (closure A) \<subseteq> interior (closure B)"
    by (intro interior_mono closure_mono sub)
  thus ?thesis using nd unfolding nowhere_dense_def by auto
qed

section \<open>Inlined proven helpers (gdip derivative at 0; second steering column)\<close>

lemma frechet_gdip_zero_arg: "frechet_derivative gdip (at \<theta>) 0 = 0" for \<theta> :: real
  using linear_frechet_derivative[OF gdip_differentiable] linear_0 by blast

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

section \<open>Degenerate steering (\<open>c = 0\<close>): no surjective moment derivative\<close>

lemma DM_paper_x_null_comp1:
  fixes x h :: "(real^2)^'n"
  shows "DM_paper_x x (0::real^2) h $ 1 = 0"
  by (simp add: DM_paper_x_def DA_paper_x_def d_phase_def)

lemma DM_paper_x_null_not_surj:
  fixes x :: "(real^2)^'n"
  shows "\<not> surj (DM_paper_x x (0::real^2))"
proof
  assume s: "surj (DM_paper_x x (0::real^2))"
  have "\<exists>h :: (real^2)^'n. (axis 1 1 :: complex^6) = DM_paper_x x (0::real^2) h"
    using s unfolding surj_def by blast
  then obtain h :: "(real^2)^'n"
    where h: "(axis 1 1 :: complex^6) = DM_paper_x x (0::real^2) h"
    by (elim exE)
  have "(axis 1 1 :: complex^6) $ 1 = 0"
    using h DM_paper_x_null_comp1[of x h] by simp
  moreover have "(axis 1 1 :: complex^6) $ 1 = 1" by (simp add: axis_def)
  ultimately show False by simp
qed

section \<open>The slice function in moment coordinates: continuity\<close>

lemma contA_moment:
  fixes c :: "real^2"
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. A_moment y c)"
  unfolding A_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
        bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma contM1_moment:
  fixes c :: "real^2"
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. M1_moment y c)"
  unfolding M1_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
        bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma contM2_moment:
  fixes c :: "real^2"
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. M2_moment y c)"
  unfolding M2_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
        bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma contF_moments:
  fixes c :: "real^2" and q1 q2 :: complex
  shows "continuous_on UNIV (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
            * (q1 * M1_moment y c + q2 * M2_moment y c)))"
  by (intro continuous_on_mult continuous_on_const continuous_on_add
        bounded_linear.continuous_on[OF bounded_linear_Re]
        bounded_linear.continuous_on[OF bounded_linear_cnj]
        contA_moment contM1_moment contM2_moment)

section \<open>The slice function in moment coordinates: entire line restrictions\<close>

lemma clA_moment:
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

lemma clM1_moment:
  fixes c :: "real^2"
  shows "cline_entire (\<lambda>y::(real^2)^'n. M1_moment y c)"
  unfolding M1_moment_def phase_def
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  assume "n \<in> (UNIV :: 'n set)"
  have bl: "bounded_linear (\<lambda>y::(real^2)^'n. - (c \<bullet> (y $ n)))"
    by (rule bounded_linear_minus[OF bounded_linear_compose
          [OF bounded_linear_inner_right bounded_linear_vec_nth]])
  have blc: "bounded_linear (\<lambda>y::(real^2)^'n. (y $ n) $ 1)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  show "cline_entire (\<lambda>y::(real^2)^'n. complex_of_real ((y $ n) $ 1) * cis (- (c \<bullet> (y $ n))))"
    by (rule cline_entire_mult[OF cline_entire_of_real_linear[OF blc]
          cline_entire_cis_linear[OF bl]])
qed

lemma clM2_moment:
  fixes c :: "real^2"
  shows "cline_entire (\<lambda>y::(real^2)^'n. M2_moment y c)"
  unfolding M2_moment_def phase_def
proof (rule cline_entire_sum)
  show "finite (UNIV :: 'n set)" by simp
next
  fix n :: 'n
  assume "n \<in> (UNIV :: 'n set)"
  have bl: "bounded_linear (\<lambda>y::(real^2)^'n. - (c \<bullet> (y $ n)))"
    by (rule bounded_linear_minus[OF bounded_linear_compose
          [OF bounded_linear_inner_right bounded_linear_vec_nth]])
  have blc: "bounded_linear (\<lambda>y::(real^2)^'n. (y $ n) $ 2)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  show "cline_entire (\<lambda>y::(real^2)^'n. complex_of_real ((y $ n) $ 2) * cis (- (c \<bullet> (y $ n))))"
    by (rule cline_entire_mult[OF cline_entire_of_real_linear[OF blc]
          cline_entire_cis_linear[OF bl]])
qed

lemma rlineF_moments:
  fixes c :: "real^2" and q1 q2 :: complex
  shows "rline_entire (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
            * (q1 * M1_moment y c + q2 * M2_moment y c)))"
proof -
  have m1: "cline_entire (\<lambda>y::(real^2)^'n. q1 * M1_moment y c)"
    by (rule cline_entire_mult[OF cline_entire_const clM1_moment])
  have m2: "cline_entire (\<lambda>y::(real^2)^'n. q2 * M2_moment y c)"
    by (rule cline_entire_mult[OF cline_entire_const clM2_moment])
  have z: "cline_entire (\<lambda>y::(real^2)^'n. q1 * M1_moment y c + q2 * M2_moment y c)"
    by (rule cline_entire_add[OF m1 m2])
  have w: "cline_entire (\<lambda>y::(real^2)^'n.
             cnj (A_moment y c) * (q1 * M1_moment y c + q2 * M2_moment y c))"
    by (rule cline_entire_mult[OF cline_entire_cnj[OF clA_moment] z])
  have r: "rline_entire (\<lambda>y::(real^2)^'n.
             Re (cnj (A_moment y c) * (q1 * M1_moment y c + q2 * M2_moment y c)))"
    by (rule rline_entire_Re[OF w])
  show ?thesis by (rule rline_entire_scale[OF r])
qed

section \<open>The slice function is not identically zero\<close>

lemma F_moments_witness:
  fixes c col2 :: "real^2"
  assumes cnz: "c \<noteq> 0" and c2nz: "col2 \<noteq> 0" and c6: "6 \<le> CARD('n)"
  shows "\<exists>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment y c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment y c)) \<noteq> 0"
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
  have M1st: "M1_moment xs c = complex_of_real (p $ 1) * (- \<i>)"
  proof -
    have 1: "M1_moment xs c
        = complex_of_real ((xs $ i0) $ 1) * cis (- (c \<bullet> (xs $ i0)))
          + (\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ 1) * cis (- (c \<bullet> (xs $ n))))"
      unfolding M1_moment_def phase_def by (rule split)
    have 2: "(\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ 1) * cis (- (c \<bullet> (xs $ n))))
        = (\<Sum>n\<in>(UNIV::'n set) - {i0}. 0)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    show ?thesis using 1 2 cp xsi by simp
  qed
  have M2st: "M2_moment xs c = complex_of_real (p $ 2) * (- \<i>)"
  proof -
    have 1: "M2_moment xs c
        = complex_of_real ((xs $ i0) $ 2) * cis (- (c \<bullet> (xs $ i0)))
          + (\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ 2) * cis (- (c \<bullet> (xs $ n))))"
      unfolding M2_moment_def phase_def by (rule split)
    have 2: "(\<Sum>n\<in>UNIV - {i0}. complex_of_real ((xs $ n) $ 2) * cis (- (c \<bullet> (xs $ n))))
        = (\<Sum>n\<in>(UNIV::'n set) - {i0}. 0)"
      by (rule sum.cong[OF refl]) (simp add: xs_def)
    show ?thesis using 1 2 cp xsi by simp
  qed
  \<comment> \<open>the value of the slice function at the witness\<close>
  have Fval: "2 * Re (cnj (A_moment xs c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment xs c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment xs c))
      = - (2 * real (CARD('n) - 1) * (col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2))"
    by (simp add: Ast M1st M2st algebra_simps)
  have Kc: "col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2 = col2 \<bullet> p"
    by (simp add: inner_vec_def sum_2)
  have r1: "real (CARD('n) - 1) \<noteq> 0" using c6 by simp
  have nz: "- (2 * real (CARD('n) - 1) * (col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2)) \<noteq> 0"
    unfolding Kc using Kp r1 by simp
  have "2 * Re (cnj (A_moment xs c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment xs c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment xs c)) \<noteq> 0"
    unfolding Fval by (rule nz)
  thus ?thesis by blast
qed

section \<open>The analytic-slice engine applied to \<open>F\<close>\<close>

lemma F_moments_nowhere_dense:
  fixes c col2 :: "real^2"
  assumes cnz: "c \<noteq> 0" and c2nz: "col2 \<noteq> 0" and c6: "6 \<le> CARD('n)"
  shows "nowhere_dense {y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment y c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment y c)) = 0}"
proof -
  define B :: "(real^2)^'n \<Rightarrow> real" where
    "B = (\<lambda>y. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment y c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment y c)))"
  have cont: "continuous_on UNIV B"
    unfolding B_def by (rule contF_moments)
  have rl: "rline_entire B"
    unfolding B_def by (rule rlineF_moments)
  have ntv: "\<exists>y. B y \<noteq> 0"
    unfolding B_def by (rule F_moments_witness[OF cnz c2nz c6])
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

section \<open>Brick R5: fixed-\<open>\<omega>\<close> slices are nowhere dense\<close>

lemma M6_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "nowhere_dense {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> = 0")
  case True
  have e: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))} = {}"
    using DM_paper_x_null_not_surj by (auto simp: True)
  show ?thesis unfolding e by simp
next
  case False
  define c :: "real^2" where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define col2 :: "real^2" where "col2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  define F :: "(real^2)^'n \<Rightarrow> real" where
    "F = (\<lambda>y. 2 * Re (cnj (M_paper y c $ 1)
       * ((- \<i>) * complex_of_real (col2 $ 1) * (M_paper y c $ 2)
        + (- \<i>) * complex_of_real (col2 $ 2) * (M_paper y c $ 3))))"
  have cnz: "c \<noteq> 0" using False by (simp add: c_def)
  have c2nz: "col2 \<noteq> 0" unfolding col2_def by (rule Dcvec_col2_nz[OF pfw])
  have gnz: "gain_dip \<omega> \<noteq> 0" by (rule gain_dip_nonzero_of_sin[OF pfw])
  have Feq: "F = (\<lambda>y::(real^2)^'n. 2 * Re (cnj (A_moment y c)
       * ((- \<i>) * complex_of_real (col2 $ 1) * M1_moment y c
        + (- \<i>) * complex_of_real (col2 $ 2) * M2_moment y c)))"
    unfolding F_def by simp
  have ndF: "nowhere_dense {y::(real^2)^'n. F y = 0}"
    unfolding Feq by (rule F_moments_nowhere_dense[OF cnz c2nz c6])
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))} \<subseteq> {y::(real^2)^'n. F y = 0}"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
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

end
