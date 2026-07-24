theory Scratch_ActualD3
  imports "Applied_Math_M5_D3ArcCount.Scratch_D3ArcCount"
begin

section \<open>The actual Robust4 phase-collinear locus\<close>

text \<open>
  The capstone does not consume arbitrary arcs in an arbitrary angular box.
  Its actual design is
  \<open>\<omega>\<^sub>0 = (\<pi>/2,0)\<close>, \<open>\<omega>\<^sub>s = (0,0)\<close>, and
  \<open>\<delta> = \<pi>/4\<close>.  At this design the determinant which tests phase
  collinearity factors explicitly.  This is a load-bearing use of the
  determinant calculation: it identifies the entire D3 angular locus.
\<close>

lemma d3_crossTheta_robust4:
  fixes \<omega> :: "real^2"
  shows "d3_crossTheta (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
      = (cos (vec_nth \<omega> 1) - 1) * sin (vec_nth \<omega> 2)"
proof -
  have trig_collapse:
      "cos (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
        + sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
        = sin (vec_nth \<omega> 2)"
  proof -
    have "cos (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
        + sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
        = (cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 1)
            + sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1)) * sin (vec_nth \<omega> 2)"
      by (simp only: mult.assoc distrib_right)
    also have "\<dots> = sin (vec_nth \<omega> 2)"
      by (simp only: sin_cos_squared_add3)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: d3_crossTheta_def cvec_dip_def Dcvec_dip_def
        kx_def ky_def kz_def axis_def algebra_simps trig_collapse)
qed

definition robust4_horizontal_arc :: "real \<Rightarrow> (real^2) set" where
  "robust4_horizontal_arc y =
     (\<lambda>t::real. vector [t, y] :: real^2) ` {pi / 4..3 * pi / 4}"

lemma robust4_horizontal_arc_analytic:
  "analytic_arc (robust4_horizontal_arc y)"
proof -
  have eqv:
      "(\<lambda>t::real. vector [t, y] :: real^2)
        = (\<lambda>t. t *\<^sub>R vector [1, 0] + vector [0, y])"
    by (rule ext, simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
  have c1:
      "(\<lambda>t::real. vector [t, y] :: real^2)
        C1_differentiable_on {pi / 4..3 * pi / 4}"
    unfolding eqv C1_differentiable_on_def
    by (intro exI[where x="\<lambda>_. vector [1, 0]"] conjI ballI)
       (auto intro!: derivative_eq_intros continuous_on_const
          simp: has_vector_derivative_def)
  show ?thesis
    unfolding robust4_horizontal_arc_def analytic_arc_def
    using c1 pi_gt_zero
    by (intro exI[where x="pi / 4"] exI[where x="3 * pi / 4"]
          exI[where x="\<lambda>t::real. vector [t, y] :: real^2"]) auto
qed

lemma robust4_horizontal_arc_components:
  assumes "\<omega> \<in> robust4_horizontal_arc y"
  shows "vec_nth \<omega> 1 \<in> {pi / 4..3 * pi / 4}"
    and "vec_nth \<omega> 2 = y"
  using assms unfolding robust4_horizontal_arc_def
  by auto

lemma robust4_horizontal_arc_subset_OmegaPF:
  assumes y: "y \<in> {-pi, 0, pi}"
  shows "robust4_horizontal_arc y
      \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
proof
  fix \<omega>
  assume "\<omega> \<in> robust4_horizontal_arc y"
  then obtain t where t: "t \<in> {pi / 4..3 * pi / 4}"
    and w: "\<omega> = vector [t, y]"
    unfolding robust4_horizontal_arc_def by blast
  show "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    unfolding w OmegaPF_def mem_box_cart
  proof
    fix i :: 2
    show "vec_nth ((vector [pi / 2, 0] :: real^2) - vector [pi / 4, pi]) i
          \<le> vec_nth (vector [t, y] :: real^2) i
        \<and> vec_nth (vector [t, y] :: real^2) i
          \<le> vec_nth ((vector [pi / 2, 0] :: real^2) + vector [pi / 4, pi]) i"
      using exhaust_2[of i] t y pi_gt_zero
      by auto
  qed
qed

lemma robust4_OmegaPF_phase_collinear_iff_second_coordinate:
  assumes wO: "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
  shows "phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
      \<longleftrightarrow> vec_nth \<omega> 2 \<in> {-pi, 0, pi}"
proof -
  have b: "pi / 4 \<le> vec_nth \<omega> 1 \<and> vec_nth \<omega> 1 \<le> 3 * pi / 4
      \<and> -pi \<le> vec_nth \<omega> 2 \<and> vec_nth \<omega> 2 \<le> pi"
    using OmegaPF_component_bounds[OF wO] by simp
  have lo: "0 < vec_nth \<omega> 1" and hi: "vec_nth \<omega> 1 < pi"
    using b pi_gt_zero by linarith+
  have c_lt1: "cos (vec_nth \<omega> 1) < 1"
  proof -
    have h0: "0 < vec_nth \<omega> 1 / 2" using lo by simp
    have h2: "vec_nth \<omega> 1 / 2 < 2" using hi pi_less_4 by linarith
    have "cos (2 * (vec_nth \<omega> 1 / 2)) < 1"
      by (rule cos_double_less_one[OF h0 h2])
    thus ?thesis by simp
  qed
  have cne: "cos (vec_nth \<omega> 1) - 1 \<noteq> 0" using c_lt1 by linarith
  have phase_iff_sin:
      "phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
        \<longleftrightarrow> sin (vec_nth \<omega> 2) = 0"
    using cne
    by (simp add: phase_collinear_iff_d3_crossTheta d3_crossTheta_robust4)
  have sin_iff_three: "sin (vec_nth \<omega> 2) = 0
      \<longleftrightarrow> vec_nth \<omega> 2 \<in> {-pi, 0, pi}"
  proof
    assume z: "sin (vec_nth \<omega> 2) = 0"
    show "vec_nth \<omega> 2 \<in> {-pi, 0, pi}"
    proof (cases "vec_nth \<omega> 2 = -pi")
      case True
      then show ?thesis by simp
    next
      case npi: False
      show ?thesis
      proof (cases "vec_nth \<omega> 2 = pi")
        case True
        then show ?thesis by simp
      next
        case pi: False
        have "-pi < vec_nth \<omega> 2" and "vec_nth \<omega> 2 < pi"
          using b npi pi by linarith+
        hence "vec_nth \<omega> 2 = 0"
          using sin_eq_0_pi z by blast
        thus ?thesis by simp
      qed
    qed
  next
    assume "vec_nth \<omega> 2 \<in> {-pi, 0, pi}"
    thus "sin (vec_nth \<omega> 2) = 0" by auto
  qed
  show ?thesis using phase_iff_sin sin_iff_three by blast
qed

theorem robust4_phase_collinear_locus_exact:
  "{\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4).
       phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}
    = robust4_horizontal_arc (-pi)
        \<union> robust4_horizontal_arc 0
        \<union> robust4_horizontal_arc pi"
proof
  show "{\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4).
       phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}
      \<subseteq> robust4_horizontal_arc (-pi)
        \<union> robust4_horizontal_arc 0
        \<union> robust4_horizontal_arc pi"
  proof
    fix \<omega>
    assume w:
      "\<omega> \<in> {\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4).
        phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
    hence wO: "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
      and pc: "phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>"
      by auto
    have t: "vec_nth \<omega> 1 \<in> {pi / 4..3 * pi / 4}"
      using OmegaPF_component_bounds[OF wO] by simp
    have y: "vec_nth \<omega> 2 \<in> {-pi, 0, pi}"
      using robust4_OmegaPF_phase_collinear_iff_second_coordinate[OF wO] pc
      by blast
    have weq: "\<omega> = vector [vec_nth \<omega> 1, vec_nth \<omega> 2]"
      by (simp only: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
          exhaust_2)
    have wh: "\<omega> \<in> robust4_horizontal_arc (vec_nth \<omega> 2)"
      unfolding robust4_horizontal_arc_def
      using t weq by blast
    show "\<omega> \<in> robust4_horizontal_arc (-pi)
        \<union> robust4_horizontal_arc 0
        \<union> robust4_horizontal_arc pi"
      using wh y by auto
  qed
next
  show "robust4_horizontal_arc (-pi)
        \<union> robust4_horizontal_arc 0
        \<union> robust4_horizontal_arc pi
      \<subseteq> {\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4).
        phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
  proof
    fix \<omega>
    assume w: "\<omega> \<in> robust4_horizontal_arc (-pi)
        \<union> robust4_horizontal_arc 0
        \<union> robust4_horizontal_arc pi"
    have subneg: "robust4_horizontal_arc (-pi)
        \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
      by (rule robust4_horizontal_arc_subset_OmegaPF) simp
    have subzero: "robust4_horizontal_arc 0
        \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
      by (rule robust4_horizontal_arc_subset_OmegaPF) simp
    have subpos: "robust4_horizontal_arc pi
        \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
      by (rule robust4_horizontal_arc_subset_OmegaPF) simp
    have wO: "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
      using w subneg subzero subpos by blast
    have "vec_nth \<omega> 2 \<in> {-pi, 0, pi}"
      using w robust4_horizontal_arc_components(2) by blast
    hence "phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>"
      using robust4_OmegaPF_phase_collinear_iff_second_coordinate[OF wO]
      by blast
    with wO show "\<omega> \<in> {\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4).
        phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
      by simp
  qed
qed


section \<open>D3 at the actual design needs only three arc cores\<close>

lemma robust4_OmegaPF_sin_first_nonzero:
  "\<forall>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
      sin (vec_nth \<omega> 1) \<noteq> 0"
proof (intro ballI)
  fix \<omega> :: "real^2"
  assume wO: "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
  have lo: "0 < vec_nth \<omega> 1"
    by (rule H0coreArc_robust4_OmegaPF_w1_strip(1)[OF wO])
  have hi: "vec_nth \<omega> 1 < pi"
    by (rule H0coreArc_robust4_OmegaPF_w1_strip(2)[OF wO])
  have "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero[OF lo hi])
  thus "sin (vec_nth \<omega> 1) \<noteq> 0" by simp
qed

text \<open>
  This is the design-specific replacement for the generic
  \<open>m5_D34_D3_collinear\<close> premise.  The theorem mentions the actual dipole
  wavevector, gain, box, and design angles in its conclusion.  It does not
  quantify over arbitrary arcs: only the three arcs which the determinant
  calculation above proves to be the actual collinear locus occur as inputs.
\<close>

theorem m5_D34_D3_collinear_robust4_of_three_arc_cores:
  fixes V :: "((real^2)^'n::finite) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and core_neg:
      "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc (-pi))"
    and core_zero:
      "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc 0)"
    and core_pos:
      "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc pi)"
  shows "meager {x \<in> V.
      \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
        gradU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) gain_dip x \<omega> = 0
      \<and> det (HessU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip x \<omega>) = 0
      \<and> A_cart (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega> \<noteq> 0
      \<and> det (matrix (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0
      \<and> cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
      \<and> \<not> surj
          (DM_paper_x x (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>y. gradU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip y \<omega>) has_derivative Dx) (at x)
          \<and> surj Dx)
      \<and> phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
proof -
  let ?w0 = "vector [pi / 2, 0] :: real^2"
  let ?ws = "vector [0, 0] :: real^2"
  let ?box = "OmegaPF ?w0 (pi / 4)"
  let ?neg = "robust4_horizontal_arc (-pi)"
  let ?zero = "robust4_horizontal_arc 0"
  let ?pos = "robust4_horizontal_arc pi"
  let ?L = "{\<omega> \<in> ?box. phase_collinear ?w0 ?ws \<omega>}"
  let ?S = "{x \<in> V.
      \<exists>\<omega>\<in>?box.
        gradU (cvec_dip ?w0 ?ws) gain_dip x \<omega> = 0
      \<and> det (HessU (cvec_dip ?w0 ?ws) gain_dip x \<omega>) = 0
      \<and> A_cart (cvec_dip ?w0 ?ws) x \<omega> \<noteq> 0
      \<and> det (matrix (Dcvec_dip ?w0 ?ws \<omega>)) \<noteq> 0
      \<and> cvec_dip ?w0 ?ws \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip ?w0 ?ws \<omega>))
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>y. gradU (cvec_dip ?w0 ?ws) gain_dip y \<omega>)
            has_derivative Dx) (at x) \<and> surj Dx)
      \<and> phase_collinear ?w0 ?ws \<omega>}"
  have eqS:
      "?S = (V \<inter> D3BadXG ?w0 ?ws ?L :: ((real^2)^'n) set)"
    unfolding D3BadXG_def by blast
  have pf: "\<forall>\<omega>\<in>?box. sin (vec_nth \<omega> 1) \<noteq> 0"
    by (rule robust4_OmegaPF_sin_first_nonzero)
  have nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
      nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    by (rule fixed_c_nonsurj_nowhere_dense[OF _ c6])
  have subneg: "?neg \<subseteq> ?box"
    by (rule robust4_horizontal_arc_subset_OmegaPF) simp
  have subzero: "?zero \<subseteq> ?box"
    by (rule robust4_horizontal_arc_subset_OmegaPF) simp
  have subpos: "?pos \<subseteq> ?box"
    by (rule robust4_horizontal_arc_subset_OmegaPF) simp
  have mneg: "meager
      (V \<inter> D3BadXG ?w0 ?ws ?neg :: ((real^2)^'n) set)"
    by (rule d3_retained_arc_projection_meager
        [OF openV Vne c6 robust4_horizontal_arc_analytic subneg pf nd core_neg])
  have mzero: "meager
      (V \<inter> D3BadXG ?w0 ?ws ?zero :: ((real^2)^'n) set)"
    by (rule d3_retained_arc_projection_meager
        [OF openV Vne c6 robust4_horizontal_arc_analytic subzero pf nd core_zero])
  have mpos: "meager
      (V \<inter> D3BadXG ?w0 ?ws ?pos :: ((real^2)^'n) set)"
    by (rule d3_retained_arc_projection_meager
        [OF openV Vne c6 robust4_horizontal_arc_analytic subpos pf nd core_pos])
  have meager_union:
      "meager ((V \<inter> D3BadXG ?w0 ?ws ?neg)
        \<union> (V \<inter> D3BadXG ?w0 ?ws ?zero)
        \<union> (V \<inter> D3BadXG ?w0 ?ws ?pos)
        :: ((real^2)^'n) set)"
    by (rule meager_Un[OF meager_Un[OF mneg mzero] mpos])
  have cover:
      "(V \<inter> D3BadXG ?w0 ?ws ?L :: ((real^2)^'n) set)
        \<subseteq> (V \<inter> D3BadXG ?w0 ?ws ?neg)
          \<union> (V \<inter> D3BadXG ?w0 ?ws ?zero)
          \<union> (V \<inter> D3BadXG ?w0 ?ws ?pos)"
    unfolding robust4_phase_collinear_locus_exact D3BadXG_def by blast
  have "meager ?S"
    unfolding eqS by (rule meager_subset[OF cover meager_union])
  thus ?thesis .
qed

lemma robust4_horizontal_arc_core_of_countable_bad_angles:
  fixes V :: "((real^2)^'n::finite) set"
  assumes y: "y \<in> {-pi, 0, pi}"
    and countable_bad:
      "countable
        (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc y))"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)"
proof (rule H0coreArc_chart_core_of_countable_robust4_bad_angle_set
    [OF countable_bad])
  fix \<omega>
  assume bad:
    "\<omega> \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)"
  have wa: "\<omega> \<in> robust4_horizontal_arc y"
    using bad unfolding H0coreArc_bad_angles_def by simp
  have wO: "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    using robust4_horizontal_arc_subset_OmegaPF[OF y] wa by blast
  show "0 < vec_nth \<omega> 1"
    by (rule H0coreArc_robust4_OmegaPF_w1_strip(1)[OF wO])
next
  fix \<omega>
  assume bad:
    "\<omega> \<in> H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)"
  have wa: "\<omega> \<in> robust4_horizontal_arc y"
    using bad unfolding H0coreArc_bad_angles_def by simp
  have wO: "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    using robust4_horizontal_arc_subset_OmegaPF[OF y] wa by blast
  show "vec_nth \<omega> 1 < pi"
    by (rule H0coreArc_robust4_OmegaPF_w1_strip(2)[OF wO])
next
  show "2 \<le> CARD('n)" by (rule card2)
qed

text \<open>
  Consequently the open D3 input is not countability on every compact
  \<open>C\<^sup>1\<close> image in the box.  At the actual design it is enough to prove
  countability for the three displayed bad-angle sets.
\<close>

theorem m5_D34_D3_collinear_robust4_of_three_countable_bad_angle_sets:
  fixes V :: "((real^2)^'n::finite) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and count_neg:
      "countable
        (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc (-pi)))"
    and count_zero:
      "countable
        (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc 0))"
    and count_pos:
      "countable
        (H0coreArc_bad_angles V (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc pi))"
  shows "meager {x \<in> V.
      \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
        gradU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) gain_dip x \<omega> = 0
      \<and> det (HessU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip x \<omega>) = 0
      \<and> A_cart (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega> \<noteq> 0
      \<and> det (matrix (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0
      \<and> cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
      \<and> \<not> surj
          (DM_paper_x x (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>y. gradU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip y \<omega>) has_derivative Dx) (at x)
          \<and> surj Dx)
      \<and> phase_collinear (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
proof (rule m5_D34_D3_collinear_robust4_of_three_arc_cores
    [OF openV Vne c6])
  have card2: "2 \<le> CARD('n)" using c6 by linarith
  show "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc (-pi))"
    by (rule robust4_horizontal_arc_core_of_countable_bad_angles
        [OF _ count_neg card2]) simp
  show "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc 0)"
    by (rule robust4_horizontal_arc_core_of_countable_bad_angles
        [OF _ count_zero card2]) simp
  show "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc pi)"
    by (rule robust4_horizontal_arc_core_of_countable_bad_angles
        [OF _ count_pos card2]) simp
qed

end
