section \<open>The gradient field is continuously differentiable in configuration and angle\<close>

theory Gradient_Field_C1
  imports
    Pattern_Moments
    Applied_Math_Analysis.Parametric_Transversality_Euclidean
begin

lemma regular_value_on_via_x_partial:
  fixes G :: "('a::real_normed_vector \<times> 'b::real_normed_vector) \<Rightarrow> 'c::real_normed_vector"
  assumes openS: "open S"
    and partial: "\<And>x w. (x, w) \<in> S \<Longrightarrow> G (x, w) = 0 \<Longrightarrow>
              (\<exists>Dj Dx. (G has_derivative Dj) (at (x, w))
                     \<and> ((\<lambda>y. G (y, w)) has_derivative Dx) (at x) \<and> surj Dx)"
  shows "regular_value_on G S 0"
proof (rule regular_value_onI)
  fix p assume pS: "p \<in> S" and p0: "G p = 0"
  obtain x w where pxw: "p = (x, w)" by (cases p)
  have xwS: "(x, w) \<in> S" using pS pxw by simp
  have G0: "G (x, w) = 0" using p0 pxw by simp
  obtain Dj Dx where dj: "(G has_derivative Dj) (at (x, w))"
      and dx: "((\<lambda>y. G (y, w)) has_derivative Dx) (at x)" and sx: "surj Dx"
    using partial[OF xwS G0] by blast
  have rel: "\<And>h. Dj (h, 0) = Dx h" by (rule joint_deriv_restricts_to_partial[OF dj dx])
  have sj: "surj Dj" by (rule surj_partial_imp_surj_joint[OF sx rel])
  have atxw: "at (x, w) within S = at (x, w)" by (rule at_within_open[OF xwS openS])
  have "(G has_derivative Dj) (at p within S)"
    unfolding pxw atxw by (rule dj)
  with sj show "\<exists>f'. (G has_derivative f') (at p within S) \<and> surj f'" by blast
qed

lemma gain_dip_nonzero_of_sin:
  fixes \<omega> :: "real^2"
  assumes "sin (\<omega> $ 1) \<noteq> 0"
  shows "gain_dip \<omega> \<noteq> 0"
proof -
  have cb: "(cos (\<omega> $ 1))\<^sup>2 < 1"
  proof -
    have "0 < (sin (\<omega> $ 1))\<^sup>2" using assms by simp
    moreover have "(sin (\<omega> $ 1))\<^sup>2 + (cos (\<omega> $ 1))\<^sup>2 = 1"
      by (rule sin_cos_squared_add)
    ultimately show ?thesis by linarith
  qed
  hence cabs: "\<bar>cos (\<omega> $ 1)\<bar> < 1" by (simp add: abs_square_less_1)
  have c_lo: "- 1 < cos (\<omega> $ 1)" and c_hi: "cos (\<omega> $ 1) < 1"
    using cabs by (auto simp: abs_less_iff)
  have hpi: "0 < pi/2" using pi_gt_zero by simp
  have "0 < cos (pi/2 * cos (\<omega> $ 1))"
  proof (rule cos_gt_zero_pi)
    have "pi/2 * (- 1) < pi/2 * cos (\<omega> $ 1)"
      by (rule mult_strict_left_mono[OF c_lo hpi])
    thus "- (pi/2) < pi/2 * cos (\<omega> $ 1)" by simp
  next
    have "pi/2 * cos (\<omega> $ 1) < pi/2 * 1"
      by (rule mult_strict_left_mono[OF c_hi hpi])
    thus "pi/2 * cos (\<omega> $ 1) < pi/2" by simp
  qed
  hence "cos (pi/2 * cos (\<omega> $ 1)) \<noteq> 0" by simp
  hence "edip (\<omega> $ 1) \<noteq> 0" using assms by (simp add: edip_def)
  hence "(edip (\<omega> $ 1))\<^sup>2 \<noteq> 0" by simp
  hence "gdip (\<omega> $ 1) \<noteq> 0" by (simp add: gdip_eq_edip_sq)
  thus ?thesis by (simp add: gain_dip_def)
qed

lemma has_derivative_Ej_moment:
  fixes M0 :: "complex^6" and p g c1 c2 :: real
  shows "((\<lambda>M. p * ((Re (M$1))\<^sup>2 + (Im (M$1))\<^sup>2)
              + g * (2 * Re (cnj (M$1) * ((- \<i>) * complex_of_real c1 * (M$2)
                                        + (- \<i>) * complex_of_real c2 * (M$3)))))
          has_derivative
          (\<lambda>\<delta>. p * (2 * Re (M0$1) * Re (\<delta>$1) + 2 * Im (M0$1) * Im (\<delta>$1))
             + g * (2 * Re (cnj (\<delta>$1) * ((- \<i>) * complex_of_real c1 * (M0$2)
                                        + (- \<i>) * complex_of_real c2 * (M0$3))
                          + cnj (M0$1) * ((- \<i>) * complex_of_real c1 * (\<delta>$2)
                                        + (- \<i>) * complex_of_real c2 * (\<delta>$3))))))
          (at M0)"
proof -
  have proj: "((\<lambda>M::complex^6. M $ k) has_derivative (\<lambda>\<delta>. \<delta> $ k)) (at M0)" for k
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_ident])
  show ?thesis
      by (auto intro!: derivative_eq_intros proj bounded_linear.has_derivative[OF bounded_linear_Re]
                       bounded_linear.has_derivative[OF bounded_linear_Im]
                       bounded_linear.has_derivative[OF bounded_linear_cnj]
                       simp: algebra_simps)
qed

definition Ejm :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex^6 \<Rightarrow> real" where
  "Ejm p g c1 c2 = (\<lambda>M. p * ((Re (M$1))\<^sup>2 + (Im (M$1))\<^sup>2)
              + g * (2 * Re (cnj (M$1) * ((- \<i>) * complex_of_real c1 * (M$2)
                                        + (- \<i>) * complex_of_real c2 * (M$3)))))"

definition dEjm :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex^6 \<Rightarrow> complex^6 \<Rightarrow> real" where
  "dEjm p g c1 c2 M0 = (\<lambda>\<delta>. p * (2 * Re (M0$1) * Re (\<delta>$1) + 2 * Im (M0$1) * Im (\<delta>$1))
              + g * (2 * Re (cnj (\<delta>$1) * ((- \<i>) * complex_of_real c1 * (M0$2)
                                        + (- \<i>) * complex_of_real c2 * (M0$3))
                          + cnj (M0$1) * ((- \<i>) * complex_of_real c1 * (\<delta>$2)
                                        + (- \<i>) * complex_of_real c2 * (\<delta>$3)))))"

lemma has_derivative_Ejm:
  fixes M0 :: "complex^6" and p g c1 c2 :: real
  shows "(Ejm p g c1 c2 has_derivative dEjm p g c1 c2 M0) (at M0)"
  unfolding Ejm_def dEjm_def by (rule has_derivative_Ej_moment)

lemma has_derivative_gradU_dip_component_x:
  fixes x :: "(real^2)^'n"
  shows "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j) has_derivative
            (dEjm (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                  ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                  (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>))
             \<circ> Dmoment_map x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x)"
proof -
  have eq: "(\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j)
            = (\<lambda>y. Ejm (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                       ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                       (moment_map y (cvec_dip \<omega>0 \<omega>s \<omega>)))"
    by (rule ext) (simp add: gradU_dip_component_moments cmod_power2 Ejm_def)
  have dM: "((\<lambda>y. moment_map y (cvec_dip \<omega>0 \<omega>s \<omega>)) has_derivative Dmoment_map x (cvec_dip \<omega>0 \<omega>s \<omega>)) (at x)"
    using has_derivative_moment_map[where V=UNIV] by fastforce
  show ?thesis
      unfolding eq
      using diff_chain_at[OF dM has_derivative_Ejm]
      by (simp add: o_def)
qed

lemma has_derivative_gradU_dip_x_explicit:
    fixes x :: "(real^2)^'n" and V :: "((real^2)^'n) set"
    shows "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s)
  gain_dip y \<omega>) has_derivative
              (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip
  (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                            ((Dcvec_dip \<omega>0 \<omega>s
  \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega>
  (axis j 1))$2)
                            (moment_map x (cvec_dip \<omega>0
  \<omega>s \<omega>))
                            (Dmoment_map x (cvec_dip \<omega>0
  \<omega>s \<omega>) h))) (at x within V)"
  proof (subst has_derivative_componentwise_within, intro ballI)
    fix b :: "real^2" assume "b \<in> Basis"
    then obtain j where bj: "b = axis j 1" by (auto simp:
  Basis_vec_def)
    show "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s)
  gain_dip y \<omega> \<bullet> b) has_derivative
            (\<lambda>h. (\<chi> j. dEjm (frechet_derivative gdip
  (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                            ((Dcvec_dip \<omega>0 \<omega>s
  \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega>
  (axis j 1))$2)
                            (moment_map x (cvec_dip \<omega>0
  \<omega>s \<omega>))
                            (Dmoment_map x (cvec_dip \<omega>0
  \<omega>s \<omega>) h)) \<bullet> b)) (at x within V)"
      using has_derivative_gradU_dip_component_x[where j=j, THEN
  has_derivative_at_withinI]
      by (simp add: bj inner_axis o_def)
  qed

lemma continuous_on_gradU_dip_xpartial_applied:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. (\<chi> j. dEjm (frechet_derivative gdip (at ((snd p)$1)) ((axis j 1)$1)) (gain_dip (snd p))
                  ((Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1))$2)
                  (moment_map (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
                  (Dmoment_map (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) i)) :: real^2)"
proof (intro continuous_on_vec_lambda)
  fix j :: 2
  show "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
          (\<lambda>p. dEjm (frechet_derivative gdip (at ((snd p)$1)) ((axis j 1)$1)) (gain_dip (snd p))
                  ((Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1))$2)
                  (moment_map (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
                  (Dmoment_map (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) i))"
    unfolding dEjm_def
    by (simp only: moment_map_components Dmoment_map_components,
        intro continuous_intros
              continuous_on_frechet_gdip_proj_snd continuous_on_gain_dip_snd
              continuous_on_Dcvec_dip_snd
              continuous_on_A_moment_cvec_dip continuous_on_M1_moment_cvec_dip
              continuous_on_M2_moment_cvec_dip
              continuous_on_DA_moment_cvec_dip continuous_on_DM1_moment_cvec_dip
              continuous_on_DM2_moment_cvec_dip)
qed

lemma norm_adjoint_blinfun_le:
  fixes L :: "'a::euclidean_space \<Rightarrow>\<^sub>L 'b::euclidean_space"
  shows "norm (adjoint (blinfun_apply L) x) \<le> norm L * norm x"
proof -
  have lin: "linear (blinfun_apply L)"
    by (rule bounded_linear.linear[OF blinfun.bounded_linear_right])
  have "(norm (adjoint (blinfun_apply L) x))\<^sup>2
        = adjoint (blinfun_apply L) x \<bullet> adjoint (blinfun_apply L) x"
    by (rule power2_norm_eq_inner)
  also have "\<dots> = x \<bullet> blinfun_apply L (adjoint (blinfun_apply L) x)"
    by (rule adjoint_clauses(2)[OF lin])
  also have "\<dots> \<le> norm x * norm (blinfun_apply L (adjoint (blinfun_apply L) x))"
    by (rule norm_cauchy_schwarz)
  also have "\<dots> \<le> norm x * (norm L * norm (adjoint (blinfun_apply L) x))"
    by (rule mult_left_mono[OF norm_blinfun norm_ge_zero])
  also have "\<dots> = (norm L * norm x) * norm (adjoint (blinfun_apply L) x)"
    by (simp add: ac_simps)
  finally have key: "(norm (adjoint (blinfun_apply L) x))\<^sup>2
                      \<le> (norm L * norm x) * norm (adjoint (blinfun_apply L) x)" .
  show ?thesis
  proof (cases "adjoint (blinfun_apply L) x = 0")
    case True thus ?thesis by simp
  next
    case False
    hence pos: "0 < norm (adjoint (blinfun_apply L) x)" by simp
    have ineq: "norm (adjoint (blinfun_apply L) x) * norm (adjoint (blinfun_apply L) x)
                \<le> (norm L * norm x) * norm (adjoint (blinfun_apply L) x)"
      using key by (simp add: power2_eq_square)
    show ?thesis by (rule mult_right_le_imp_le[OF ineq pos])
  qed
qed

lemma adjoint_blinfun_diff:
  fixes A B :: "'a::euclidean_space \<Rightarrow>\<^sub>L 'b::euclidean_space"
  shows "adjoint (blinfun_apply (A - B)) y
         = adjoint (blinfun_apply A) y - adjoint (blinfun_apply B) y"
proof (rule euclidean_eqI)
  fix i :: 'a assume "i \<in> Basis"
  have lAB: "linear (blinfun_apply (A - B))" and lA: "linear (blinfun_apply A)"
    and lB: "linear (blinfun_apply B)"
    by (rule bounded_linear.linear[OF blinfun.bounded_linear_right])+
  have "adjoint (blinfun_apply (A - B)) y \<bullet> i = y \<bullet> blinfun_apply (A - B) i"
    by (rule adjoint_clauses(2)[OF lAB])
  also have "\<dots> = y \<bullet> blinfun_apply A i - y \<bullet> blinfun_apply B i"
    by (simp add: blinfun.diff_left inner_diff_right)
  also have "\<dots> = (adjoint (blinfun_apply A) y - adjoint (blinfun_apply B) y) \<bullet> i"
    by (simp add: adjoint_clauses(2)[OF lA] adjoint_clauses(2)[OF lB] inner_diff_left)
  finally show "adjoint (blinfun_apply (A - B)) y \<bullet> i
                = (adjoint (blinfun_apply A) y - adjoint (blinfun_apply B) y) \<bullet> i" .
qed

lemma open_surj_blinfun:
  "open {A::('a::euclidean_space) \<Rightarrow>\<^sub>L ('b::euclidean_space). surj (blinfun_apply A)}"
proof (unfold open_dist, intro ballI)
  fix A0 :: "'a \<Rightarrow>\<^sub>L 'b" assume "A0 \<in> {A. surj (blinfun_apply A)}"
  hence sA0: "surj (blinfun_apply A0)" by simp
  have lin0: "linear (blinfun_apply A0)"
    by (rule bounded_linear.linear[OF blinfun.bounded_linear_right])
  have "surj (adjoint (adjoint (blinfun_apply A0))) = inj (adjoint (blinfun_apply A0))"
    by (rule surj_adjoint_iff_inj[OF adjoint_linear[OF lin0]])
  hence injAdj0: "inj (adjoint (blinfun_apply A0))"
    using sA0 by (simp add: adjoint_adjoint[OF lin0])
  obtain B where Bpos: "0 < B"
      and Bb: "\<And>w. B * norm w \<le> norm (adjoint (blinfun_apply A0) w)"
    using linear_inj_bounded_below_pos[OF adjoint_linear[OF lin0] injAdj0] by blast
  show "\<exists>e>0. \<forall>y. dist y A0 < e \<longrightarrow> y \<in> {A. surj (blinfun_apply A)}"
  proof (intro exI[where x=B] conjI Bpos allI impI)
    fix y :: "'a \<Rightarrow>\<^sub>L 'b" assume dy: "dist y A0 < B"
    have liny: "linear (blinfun_apply y)"
      by (rule bounded_linear.linear[OF blinfun.bounded_linear_right])
    have inj_y: "inj (adjoint (blinfun_apply y))"
    proof (rule injI)
      fix u v assume eq: "adjoint (blinfun_apply y) u = adjoint (blinfun_apply y) v"
      have z: "adjoint (blinfun_apply y) (u - v) = 0"
      proof -
        have "adjoint (blinfun_apply y) (u - v)
              = adjoint (blinfun_apply y) u - adjoint (blinfun_apply y) v"
          by (rule linear_diff[OF adjoint_linear[OF liny]])
        thus ?thesis using eq by simp
      qed
      have "B * norm (u - v) \<le> norm (adjoint (blinfun_apply A0) (u - v))" by (rule Bb)
      also have "\<dots> = norm (adjoint (blinfun_apply (A0 - y)) (u - v))"
        using z by (simp add: adjoint_blinfun_diff)
      also have "\<dots> \<le> norm (A0 - y) * norm (u - v)" by (rule norm_adjoint_blinfun_le)
      also have "\<dots> = dist y A0 * norm (u - v)"
        by (simp add: dist_blinfun_def norm_minus_commute)
      finally have le: "B * norm (u - v) \<le> dist y A0 * norm (u - v)" .
      have "norm (u - v) \<le> 0"
      proof (rule ccontr)
        assume "\<not> norm (u - v) \<le> 0"
        hence "0 < norm (u - v)" by simp
        with le have "B \<le> dist y A0" by (simp add: mult_le_cancel_right)
        with dy show False by simp
      qed
      thus "u = v" by simp
    qed
    have "surj (adjoint (adjoint (blinfun_apply y))) = inj (adjoint (blinfun_apply y))"
      by (rule surj_adjoint_iff_inj[OF adjoint_linear[OF liny]])
    hence "surj (blinfun_apply y)"
      using inj_y by (simp add: adjoint_adjoint[OF liny])
    thus "y \<in> {A. surj (blinfun_apply A)}" by simp
  qed
qed

lemma continuous_on_HessU_blinfun_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>z. Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst z) (snd z))))"
proof (rule continuous_on_blinfun_componentwise)
  fix e :: "real^2" assume "e \<in> Basis"
  have "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
          (\<lambda>z. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst z) (snd z) *v e)"
    by (rule continuous_on_matvec[OF continuous_on_HessU_dip_joint continuous_on_const])
  thus "continuous_on UNIV
          (\<lambda>z. blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst z) (snd z)))) e)"    
    using continuous_on_HessU_dip_joint continuous_on_const continuous_on_matvec
    by (simp add: bounded_linear_Blinfun_apply matrix_vector_mul_bounded_linear, blast)
qed

lemma gradU_dip_joint_C1:
  shows "\<exists>G'::(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2)).
            (\<forall>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                     has_derivative blinfun_apply (G' z)) (at z))
          \<and> continuous_on UNIV G'"
proof -
  define Dx where
    "Dx x \<omega> = (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>)) (Dmoment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) h))"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
  define D where
    "D z = (\<lambda>w::((real^2)^'n) \<times> (real^2). Dx (fst z) (snd z) (fst w)
              + HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst z) (snd z) *v (snd w))"
    for z :: "((real^2)^'n) \<times> (real^2)"
  have FX: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx x \<omega>) (at x within UNIV)"
    for x :: "(real^2)^'n" and \<omega> :: "real^2"
    unfolding Dx_def by (rule has_derivative_gradU_dip_x_explicit)
  have blDx: "bounded_linear (Dx x \<omega>)" for x \<omega>
    using FX has_derivative_bounded_linear by blast
  have dx0: "Dx x \<omega> 0 = 0" for x \<omega>
    by (metis blDx bounded_linear.linear linear_0)
  have blD: "bounded_linear (D z)" for z
    unfolding D_def
    by (intro bounded_linear_add bounded_linear_compose[OF blDx bounded_linear_fst]
              bounded_linear_compose[OF matrix_vector_mul_bounded_linear bounded_linear_snd])
  have hd: "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) has_derivative D z) (at z)" for z
  proof -
    obtain x \<omega> where z: "z = (x, \<omega>)" by fastforce
    have FY: "\<And>x' \<omega>'. x' \<in> (UNIV::((real^2)^'n) set) \<Longrightarrow> \<omega>' \<in> (UNIV::(real^2) set) \<Longrightarrow>
                ((\<lambda>\<omega>''. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>'') has_derivative
                 blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))) (at \<omega>' within UNIV)"
    proof -
      fix x' :: "(real^2)^'n" and \<omega>' :: "real^2"
      have "((\<lambda>\<omega>''. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>'') has_derivative
              (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>' *v v)) (at \<omega>' within UNIV)"
        by (rule has_derivative_at_withinI[OF gradU_dip_has_derivative])
      thus "((\<lambda>\<omega>''. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>'') has_derivative
              blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))) (at \<omega>' within UNIV)"
        by (simp add: bounded_linear_Blinfun_apply matrix_vector_mul_bounded_linear)
    qed
    have FYC: "continuous (at (x, \<omega>) within UNIV \<times> UNIV)
                 (\<lambda>(x', \<omega>'). Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>')))"
    proof -
      have "continuous (at (x, \<omega>) within UNIV)
              (\<lambda>z. Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst z) (snd z))))"
        using continuous_on_HessU_blinfun_joint 
        by (simp add: continuous_on_eq_continuous_within, blast)
      thus ?thesis by (simp add: case_prod_unfold UNIV_Times_UNIV)
    qed
    have "((\<lambda>(x', \<omega>'). gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x' \<omega>') has_derivative
             (\<lambda>(tx, ty). Dx x \<omega> tx
                  + blinfun_apply (Blinfun ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))) ty))
           (at (x, \<omega>) within UNIV \<times> UNIV)"
      by (rule has_derivative_partialsI[OF FX FY FYC UNIV_I convex_UNIV])
    thus ?thesis
      unfolding z D_def
      by (simp add: bounded_linear_Blinfun_apply matrix_vector_mul_bounded_linear
                    case_prod_unfold UNIV_Times_UNIV)
  qed
  have cont: "continuous_on UNIV (\<lambda>z. Blinfun (D z))"
  proof (rule continuous_on_blinfun_componentwise)
    fix w :: "((real^2)^'n) \<times> (real^2)" assume "w \<in> Basis"
    then consider b where "b \<in> Basis" "w = (b, 0)" | e where "e \<in> Basis" "w = (0, e)"
      unfolding Basis_prod_def by auto
    thus "continuous_on UNIV (\<lambda>z. blinfun_apply (Blinfun (D z)) w)"
    proof cases
      case 1
      have "continuous_on UNIV (\<lambda>z. D z w)"
        unfolding D_def \<open>w = (b, 0)\<close> Dx_def
        using continuous_on_gradU_dip_xpartial_applied[where i=b] by simp
      thus ?thesis by (simp add: bounded_linear_Blinfun_apply blD)
    next
      case 2
      have "continuous_on UNIV (\<lambda>z. D z w)"
        unfolding D_def \<open>w = (0, e)\<close>
        by (simp add: dx0 continuous_on_matvec[OF continuous_on_HessU_dip_joint continuous_on_const])
      thus ?thesis by (simp add: bounded_linear_Blinfun_apply blD)
    qed
  qed
  show ?thesis
  proof (intro exI[where x="\<lambda>z. Blinfun (D z)"] conjI allI)
    fix z
    show "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
             has_derivative blinfun_apply (Blinfun (D z))) (at z)"
      using hd[of z] by (simp add: bounded_linear_Blinfun_apply blD)
  qed (rule cont)
qed

lemma HessU_dip_symmetric:
  fixes x :: "(real^2)^'n"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ i $ j
       = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j $ i"
  unfolding HessU_def
  by (rule mixed_partials_commute[OF open_UNIV UNIV_I U_dip_Ck2])

end
