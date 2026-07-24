theory Scratch_ActualD3Argument
  imports
    "Applied_Math_M5_ActualD3Core.Scratch_ActualD3Core"
    "Applied_Math_M5_AlignedCover.Scratch_AlignedCover"
begin

lemma zero_fst_scaleR_snd:
  "((0::'a::real_vector), r *\<^sub>R (b::'b::real_vector)) = r *\<^sub>R (0, b)"
  by (simp add: scaleR_prod_def)

section \<open>The actual horizontal-arc geometry\<close>

text \<open>
  The three components of the actual Robust4 phase-collinear locus are the
  horizontal arcs at second angle \<open>-\<pi>\<close>, \<open>0\<close>, and \<open>\<pi>\<close>.
  At those angles the actual coupling vector is horizontal.  Its first
  steering derivative is horizontal as well.  These elementary facts are the
  design-specific symmetry which is absent from the general H0 core.
\<close>

lemma robust4_horizontal_arc_sin_second_zero:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
  shows "sin (vec_nth \<omega> 2) = 0"
proof -
  have phi: "vec_nth \<omega> 2 = y"
    by (rule robust4_horizontal_arc_components(2)[OF wA])
  show ?thesis using phi y3 by auto
qed

lemma robust4_horizontal_arc_actual_cvec_second_zero:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
  shows "vec_nth
      (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 2 = 0"
proof -
  have phi: "vec_nth \<omega> 2 = y"
    by (rule robust4_horizontal_arc_components(2)[OF wA])
  show ?thesis
    using phi y3
    by (auto simp: cvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half)
qed

lemma robust4_horizontal_arc_actual_Dc_axis1_second_zero:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
  shows "vec_nth
      (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
        (axis 1 1)) 2 = 0"
proof -
  have phi: "vec_nth \<omega> 2 = y"
    by (rule robust4_horizontal_arc_components(2)[OF wA])
  show ?thesis
    using phi y3
    by (auto simp: Dcvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half)
qed

lemma robust4_horizontal_arc_actual_s1_factor_zero:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
  shows "d3_s1_global_factor
      (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
proof -
  have c2: "vec_nth
      (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 2 = 0"
    by (rule robust4_horizontal_arc_actual_cvec_second_zero[OF wA y3])
  have d2: "vec_nth
      (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
        (axis 1 1)) 2 = 0"
    by (rule robust4_horizontal_arc_actual_Dc_axis1_second_zero[OF wA y3])
  show ?thesis
    unfolding d3_s1_global_factor_def
    using c2 d2
    by (simp add: perp2_def inner_vec_def sum_2)
qed

lemma robust4_horizontal_arc_actual_s2_factor_nonzero:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
  shows "d3_s2_global_factor
      (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
proof -
  have lo: "0 < vec_nth \<omega> 1"
    by (rule robust4_horizontal_arc_first_strip(1)[OF wA y3])
  have hi: "vec_nth \<omega> 1 < pi"
    by (rule robust4_horizontal_arc_first_strip(2)[OF wA y3])
  have sinpos: "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero[OF lo hi])
  have gnz: "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_sin) (use sinpos in force)
  have factors:
      "d3_s1_global_factor
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
       \<or> d3_s2_global_factor
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
    by (rule d3_s1_or_s2_global_factor_nonzero[OF cnz detnz gnz])
  have s1z:
      "d3_s1_global_factor
        (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
    by (rule robust4_horizontal_arc_actual_s1_factor_zero[OF wA y3])
  show ?thesis using factors s1z by blast
qed

lemma gradU_dip_frechet_derivative_component:
  fixes x u :: "(real^2)^'n::finite"
    and \<omega> \<omega>0 \<omega>s :: "real^2" and j :: 2
  shows "vec_nth
      (frechet_derivative
        (\<lambda>z. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>)
        (at x) u) j
    = frechet_derivative
        (\<lambda>z. vec_nth
          (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>) j)
        (at x) u"
proof -
  have diff:
      "(\<lambda>z. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>)
        differentiable (at x)"
    using gradU_dip_differentiable_x[
      where x=x and V=UNIV and \<omega>=\<omega> and \<omega>0=\<omega>0
        and \<omega>s=\<omega>s]
    by simp
  obtain D where hd:
      "((\<lambda>z. gradU
          (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>)
        has_derivative D) (at x)"
    using diff unfolding differentiable_def by blast
  have hdF:
      "((\<lambda>z. gradU
          (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>)
        has_derivative
          frechet_derivative
            (\<lambda>z. gradU
              (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>)
            (at x)) (at x)"
    using hd frechet_derivative_at[OF hd] by simp
  have hcomp:
      "((\<lambda>z. vec_nth
          (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>) j)
        has_derivative
          (\<lambda>h. vec_nth
            (frechet_derivative
              (\<lambda>z. gradU
                (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>)
              (at x) h) j)) (at x)"
    by (rule bounded_linear.has_derivative[
        OF bounded_linear_vec_nth hdF])
  have eq:
      "frechet_derivative
          (\<lambda>z. vec_nth
            (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>) j)
          (at x)
       = (\<lambda>h. vec_nth
          (frechet_derivative
            (\<lambda>z. gradU
              (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>)
            (at x) h) j)"
    by (rule sym, rule frechet_derivative_at[OF hcomp])
  show ?thesis
    using fun_cong[OF eq, of u] by simp
qed

lemma robust4_horizontal_arc_actual_schur_perp_slot_value:
  fixes x :: "(real^2)^'n::finite" and t y :: real and k :: 'n
  assumes tI: "t \<in> {pi / 4..3 * pi / 4}"
    and y3: "y \<in> {-pi, 0, pi}"
  shows "arc_schur_L
      (vector [pi / 2, 0]) (vector [0, 0])
      (\<lambda>s. vector [s, y]) (\<lambda>_. vector [1, 0])
      (\<lambda>_. t) x
      (slot k
        (perp2
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [t, y]))))
    = d3_s2_perp_slot
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [t, y]) k x"
proof -
  have wA: "(vector [t, y] :: real^2) \<in> robust4_horizontal_arc y"
    using tI unfolding robust4_horizontal_arc_def by blast
  have s1z:
      "d3_s1_global_factor
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [t, y]) = 0"
    by (rule robust4_horizontal_arc_actual_s1_factor_zero[OF wA y3])
  have slot1:
      "d3_s1_perp_slot
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [t, y]) k x = 0"
    unfolding d3_s1_perp_slot_value
    using s1z by simp
  have vec1:
      "vec_nth
        (frechet_derivative
          (\<lambda>z. gradU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip z (vector [t, y]))
          (at x)
          (slot k
            (perp2
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
                (vector [t, y]))))) 1 = 0"
    unfolding gradU_dip_frechet_derivative_component
      d3_s1_perp_slot_def[symmetric]
    by (rule slot1)
  have vec2:
      "vec_nth
        (frechet_derivative
          (\<lambda>z. gradU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip z (vector [t, y]))
          (at x)
          (slot k
            (perp2
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
                (vector [t, y]))))) 2
      = d3_s2_perp_slot
          (vector [pi / 2, 0]) (vector [0, 0])
          (vector [t, y]) k x"
    unfolding gradU_dip_frechet_derivative_component
      d3_s2_perp_slot_def
    by simp
  show ?thesis
    unfolding arc_schur_L_def
    using vec1 vec2 by simp
qed

lemma Im_cnj_pair_zero_of_common_nonzero:
  fixes a z w :: complex
  assumes anz: "a \<noteq> 0"
    and az: "Im (cnj a * z) = 0"
    and aw: "Im (cnj a * w) = 0"
  shows "Im (cnj z * w) = 0"
proof -
  have normsq: "Re a ^ 2 + Im a ^ 2 \<noteq> 0"
    using anz cmod_power2[of a] by auto
  have lagrange:
      "(Re a ^ 2 + Im a ^ 2) * Im (cnj z * w)
       = Re (cnj a * z) * Im (cnj a * w)
         - Im (cnj a * z) * Re (cnj a * w)"
    by (simp add: power2_eq_square algebra_simps)
  have "(Re a ^ 2 + Im a ^ 2) * Im (cnj z * w) = 0"
    using lagrange az aw by simp
  then show ?thesis using normsq by (metis mult_eq_0_iff)
qed

definition robust4_actual_phase_aligned ::
    "((real^2)^'n::finite) \<Rightarrow> real^2 \<Rightarrow> bool"
  where
  "robust4_actual_phase_aligned x \<omega> \<longleftrightarrow>
    (\<forall>k::'n.
      Im (cnj
          (vec_nth
            (M_paper x
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) 1)
        * phase
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
            x k) = 0)"

lemma robust4_actual_phase_aligned_pair_zero:
  assumes aligned:
      "robust4_actual_phase_aligned (x :: (real^2)^'n::finite) \<omega>"
    and Anz:
      "A_cart
        (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega>
        \<noteq> 0"
  shows "Im
      (cnj
        (phase
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) x i)
       * phase
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) x j)
      = 0"
proof -
  let ?c =
    "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>"
  let ?A = "vec_nth (M_paper x ?c) 1"
  have Aeq:
      "?A =
        A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega>"
    by (rule M_paper_proj_A)
  have Aneq: "?A \<noteq> 0"
    using Anz Aeq by simp
  have ai: "Im (cnj ?A * phase ?c x i) = 0"
    using aligned unfolding robust4_actual_phase_aligned_def by blast
  have aj: "Im (cnj ?A * phase ?c x j) = 0"
    using aligned unfolding robust4_actual_phase_aligned_def by blast
  show ?thesis
    by (rule Im_cnj_pair_zero_of_common_nonzero[OF Aneq ai aj])
qed

lemma robust4_actual_phase_aligned_iff_aligned_conf:
  "robust4_actual_phase_aligned (x :: (real^2)^'n::finite) \<omega>
    \<longleftrightarrow>
   aligned_conf x
    (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)"
  unfolding robust4_actual_phase_aligned_def aligned_conf_def
  by (simp add: M_paper_proj_A A_cart_eq_Afun Afun_eq_A_moment)

definition D3ActualAlignedProjection ::
    "((real^2)^'n::finite) set"
  where
  "D3ActualAlignedProjection =
    {x. \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
      cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
      \<and> A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega>
          \<noteq> 0
      \<and> robust4_actual_phase_aligned x \<omega>}"

theorem robust4_actual_aligned_projection_closed_negligible_cover:
  assumes card4: "4 \<le> CARD('n::finite)"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      D3ActualAlignedProjection \<subseteq> (\<Union>n. K n)
    \<and> (\<forall>n. closed (K n))
    \<and> (\<forall>n. negligible (K n))"
proof -
  have exK:
      "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
        {x. \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
            cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
          \<and> A_moment x
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
              \<noteq> 0
          \<and> aligned_conf x
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)}
          \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n))
      \<and> (\<forall>n. negligible (K n))"
    by (rule aligned_bad_closed_cover[OF card4 OmegaPF_compact])
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover:
      "{x. \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
          cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
        \<and> A_moment x
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
            \<noteq> 0
        \<and> aligned_conf x
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)}
        \<subseteq> (\<Union>n. K n)"
      and closed: "\<forall>n. closed (K n)"
      and negligible: "\<forall>n. negligible (K n)"
    using exK by blast
  have sub:
      "D3ActualAlignedProjection \<subseteq>
        {x. \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
          cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
        \<and> A_moment x
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
            \<noteq> 0
        \<and> aligned_conf x
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)}"
  proof
    fix x
    assume xin: "x \<in> D3ActualAlignedProjection"
    then obtain \<omega> where wPF:
        "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
      and cnz:
        "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
          \<noteq> 0"
      and Acnz:
        "A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega>
          \<noteq> 0"
      and aligned: "robust4_actual_phase_aligned x \<omega>"
      unfolding D3ActualAlignedProjection_def by blast
    have Amnz:
        "A_moment x
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
          \<noteq> 0"
      by (rule A_moment_nz_of_A_cart[OF Acnz])
    have aligned':
        "aligned_conf x
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)"
      using aligned
      unfolding robust4_actual_phase_aligned_iff_aligned_conf .
    show "x \<in>
        {x. \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
          cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
        \<and> A_moment x
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
            \<noteq> 0
        \<and> aligned_conf x
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)}"
      using wPF cnz Amnz aligned' by blast
  qed
  have "D3ActualAlignedProjection \<subseteq> (\<Union>n. K n)"
    using sub cover by blast
  then show ?thesis
    using closed negligible by blast
qed

corollary robust4_actual_aligned_projection_meager:
  assumes card4: "4 \<le> CARD('n::finite)"
  shows "meager (D3ActualAlignedProjection :: ((real^2)^'n) set)"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "D3ActualAlignedProjection \<subseteq> (\<Union>n. K n)"
      and closed: "\<forall>n. closed (K n)"
      and negligible: "\<forall>n. negligible (K n)"
    using robust4_actual_aligned_projection_closed_negligible_cover[
      OF card4]
    by blast
  show ?thesis
    by (rule meager_negligible_closed_cover[OF cover])
       (use closed negligible in blast)+
qed

theorem robust4_horizontal_arc_actual_schur_or_phase_aligned:
  fixes x :: "(real^2)^'n::finite" and t y :: real
  assumes tI: "t \<in> {pi / 4..3 * pi / 4}"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
          (vector [t, y]))) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
        (vector [t, y]) \<noteq> 0"
  shows
    "(\<exists>r. arc_schur_L
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>s. vector [s, y]) (\<lambda>_. vector [1, 0])
        (\<lambda>_. t) x r \<noteq> 0)
     \<or>
     robust4_actual_phase_aligned x (vector [t, y])"
proof (cases "robust4_actual_phase_aligned x (vector [t, y])")
  case False
  have notall:
      "\<not> (\<forall>k::'n.
        Im (cnj
            (vec_nth
              (M_paper x
                (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
                  (vector [t, y]))) 1)
          * phase
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
                (vector [t, y])) x k) = 0)"
    using False unfolding robust4_actual_phase_aligned_def .
  then obtain k :: 'n where phase_nz:
      "Im (cnj
          (vec_nth
            (M_paper x
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
                (vector [t, y]))) 1)
        * phase
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
              (vector [t, y])) x k) \<noteq> 0"
    by blast
  have wA:
      "(vector [t, y] :: real^2) \<in> robust4_horizontal_arc y"
    using tI unfolding robust4_horizontal_arc_def by blast
  have facnz:
      "d3_s2_global_factor
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [t, y]) \<noteq> 0"
    by (rule robust4_horizontal_arc_actual_s2_factor_nonzero[
        OF wA y3 detnz cnz])
  have slot_nz:
      "d3_s2_perp_slot
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [t, y]) k x \<noteq> 0"
    unfolding d3_s2_perp_slot_value
    using facnz phase_nz by simp
  have schur_nz:
      "arc_schur_L
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>s. vector [s, y]) (\<lambda>_. vector [1, 0])
        (\<lambda>_. t) x
        (slot k
          (perp2
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
              (vector [t, y])))) \<noteq> 0"
    unfolding robust4_horizontal_arc_actual_schur_perp_slot_value[
        OF tI y3]
    by (rule slot_nz)
  show ?thesis
    by (rule disjI1, rule exI[of _
        "slot k
          (perp2
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
              (vector [t, y])))"], rule schur_nz)
next
  case True
  show ?thesis by (rule disjI2, rule True)
qed

lemma robust4_horizontal_arc_actual_e_par_second_zero:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
  shows "vec_nth
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 2 = 0"
proof -
  have lo: "0 < vec_nth \<omega> 1"
    by (rule robust4_horizontal_arc_first_strip(1)[OF wA y3])
  have hi: "vec_nth \<omega> 1 < pi"
    by (rule robust4_horizontal_arc_first_strip(2)[OF wA y3])
  have sinpos: "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero[OF lo hi])
  have gnz: "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_sin) (use sinpos in force)
  have s1z:
      "d3_s1_global_factor
        (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
    by (rule robust4_horizontal_arc_actual_s1_factor_zero[OF wA y3])
  have form:
      "e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega> =
        vector [
          d3_s2_global_factor
              (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
            / (2 * gain_dip \<omega>
                * det (matrix
                    (Dcvec_dip
                      (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))),
          - d3_s1_global_factor
              (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
            / (2 * gain_dip \<omega>
                * det (matrix
                    (Dcvec_dip
                      (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)))]"
    by (rule e_par_closed_form[OF detnz gnz])
  show ?thesis
    unfolding form
    using s1z by (simp add: vector_2)
qed

lemma robust4_horizontal_arc_actual_D2c_e_par_second_zero:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
  shows "vec_nth
      (D2cvec_dip
        (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
        (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
        (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) 2 = 0"
proof -
  have phi: "vec_nth \<omega> 2 = y"
    by (rule robust4_horizontal_arc_components(2)[OF wA])
  have e2: "vec_nth
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 2 = 0"
    by (rule robust4_horizontal_arc_actual_e_par_second_zero[
        OF wA y3 detnz])
  show ?thesis
    using phi y3 e2
    by (auto simp: D2cvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half algebra_simps)
qed

lemma robust4_horizontal_arc_actual_D2c_e_par_parallel:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
  obtains r where
    "D2cvec_dip
        (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
        (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
        (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
      = r *\<^sub>R
        cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>"
proof -
  let ?c =
    "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>"
  let ?d =
    "D2cvec_dip
      (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)"
  have c2: "vec_nth ?c 2 = 0"
    by (rule robust4_horizontal_arc_actual_cvec_second_zero[OF wA y3])
  have d2: "vec_nth ?d 2 = 0"
    by (rule robust4_horizontal_arc_actual_D2c_e_par_second_zero[
        OF wA y3 detnz])
  have c1nz: "vec_nth ?c 1 \<noteq> 0"
  proof
    assume "vec_nth ?c 1 = 0"
    with c2 have "?c = 0"
      by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
    with cnz show False by contradiction
  qed
  have eq: "?d = (vec_nth ?d 1 / vec_nth ?c 1) *\<^sub>R ?c"
    using c1nz c2 d2
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2
        vector_scaleR_component)
  show ?thesis by (rule that[OF eq])
qed

lemma robust4_horizontal_arc_actual_e_par_first_nonzero:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
  shows "vec_nth
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 1 \<noteq> 0"
proof -
  let ?w0 = "vector [pi / 2, 0] :: real^2"
  let ?ws = "vector [0, 0] :: real^2"
  let ?e = "e_par ?w0 ?ws \<omega>"
  have e2: "vec_nth ?e 2 = 0"
    by (rule robust4_horizontal_arc_actual_e_par_second_zero[
        OF wA y3 detnz])
  have enz: "?e \<noteq> 0"
  proof
    assume ez: "?e = 0"
    have "cvec_dip ?w0 ?ws \<omega> = 0"
      using Dcvec_dip_e_par[OF detnz]
      unfolding ez
      by (simp add: Dcvec_dip_def)
    with cnz show False by contradiction
  qed
  show ?thesis
  proof
    assume e1: "vec_nth ?e 1 = 0"
    from e1 e2 have "?e = 0"
      by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
    with enz show False by contradiction
  qed
qed

lemma robust4_horizontal_arc_actual_Xi_horizontal_value:
  fixes x :: "(real^2)^'n::finite"
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
  shows "Xi x
      (vector [pi / 2, 0]) (vector [0, 0]) \<omega> (vector [1, 0])
    = vec_nth
        (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 1
      * vec_nth
          (vec_nth
            (HessU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip x \<omega>) 1) 1"
proof -
  have e2: "vec_nth
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 2 = 0"
    by (rule robust4_horizontal_arc_actual_e_par_second_zero[
        OF wA y3 detnz])
  show ?thesis
    unfolding Xi_def
    using e2
    by (simp add: matrix_vector_mult_def inner_vec_def sum_2 vector_2
        algebra_simps)
qed

lemma robust4_horizontal_arc_actual_Xi_horizontal_nonzero_iff:
  fixes x :: "(real^2)^'n::finite"
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
  shows "Xi x
      (vector [pi / 2, 0]) (vector [0, 0]) \<omega> (vector [1, 0])
        \<noteq> 0
    \<longleftrightarrow>
      vec_nth
        (vec_nth
          (HessU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip x \<omega>) 1) 1 \<noteq> 0"
proof -
  have e1nz: "vec_nth
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 1 \<noteq> 0"
    by (rule robust4_horizontal_arc_actual_e_par_first_nonzero[
        OF wA y3 detnz cnz])
  show ?thesis
    unfolding robust4_horizontal_arc_actual_Xi_horizontal_value[
        OF wA y3 detnz]
    using e1nz by simp
qed

theorem robust4_horizontal_arc_actual_Xi_horizontal_zeros_nowhere_dense:
  fixes \<omega> :: "real^2"
  assumes card2: "2 \<le> CARD('n::finite)"
    and wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
  shows "interior
      (closure {x::(real^2)^'n.
        Xi x
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega> (vector [1, 0])
          = 0})
      = {}"
proof (rule Xi_zeros_nowhere_dense)
  show "2 \<le> CARD('n)" by (rule card2)
  show "det (matrix
      (Dcvec_dip
        (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    by (rule detnz)
  show "cvec_dip
      (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
    by (rule cnz)
  show "vec_nth
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 1 \<noteq> 0"
    by (rule robust4_horizontal_arc_actual_e_par_first_nonzero[
        OF wA y3 detnz cnz])
  have lo: "0 < vec_nth \<omega> 1"
    by (rule robust4_horizontal_arc_first_strip(1)[OF wA y3])
  have hi: "vec_nth \<omega> 1 < pi"
    by (rule robust4_horizontal_arc_first_strip(2)[OF wA y3])
  have sinpos: "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero[OF lo hi])
  show "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_sin) (use sinpos in force)
  show "vec_nth (vector [1, 0] :: real^2) 1 \<noteq> 0"
    by (simp add: vector_2)
qed

section \<open>Joint-incidence charts for the actual retained set\<close>

definition d3_projection_chart_data ::
    "((real^2)^'n::finite) set \<Rightarrow> bool"
  where
  "d3_projection_chart_data S \<longleftrightarrow>
    (\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative
            (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` Crit i)))"

lemma d3_projection_chart_data_empty:
  "d3_projection_chart_data ({} :: ((real^2)^'n::finite) set)"
  unfolding d3_projection_chart_data_def
  by (rule chart_core_data_empty)

lemma d3_projection_chart_data_mono:
  fixes S T :: "((real^2)^'n::finite) set"
  assumes sub: "S \<subseteq> T"
    and data: "d3_projection_chart_data T"
  shows "d3_projection_chart_data S"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "T \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative
          (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        \<not> surj (blinfun_apply (D i x))"
      and closed: "\<forall>i. closed ((fst \<circ> charts i) ` Crit i)"
    using data unfolding d3_projection_chart_data_def by blast
  have cover': "S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
    using sub cover by blast
  show ?thesis
    unfolding d3_projection_chart_data_def
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D]
        conjI cover' der rank closed)
qed

lemma d3_projection_chart_data_countable_UN:
  fixes S :: "nat \<Rightarrow> ((real^2)^'n::finite) set"
  assumes data: "\<And>i. d3_projection_chart_data (S i)"
  shows "d3_projection_chart_data (\<Union>i::nat. S i)"
proof -
  have raw: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative
            (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
    using data unfolding d3_projection_chart_data_def by blast
  show ?thesis
    unfolding d3_projection_chart_data_def
    by (rule chart_core_data_countable_UN[OF raw])
qed

lemma d3_projection_chart_data_meager:
  fixes S :: "((real^2)^'n::finite) set"
  assumes data: "d3_projection_chart_data S"
  shows "meager S"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative
          (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        \<not> surj (blinfun_apply (D i x))"
      and closed: "\<forall>i. closed ((fst \<circ> charts i) ` Crit i)"
    using data unfolding d3_projection_chart_data_def by blast
  define K where "K = (\<lambda>i. (fst \<circ> charts i) ` Crit i)"
  have Kcover: "S \<subseteq> (\<Union>i. K i)"
    using cover unfolding K_def by simp
  have Kclosed: "closed (K i)" for i
    using closed unfolding K_def by blast
  have Kneg: "negligible (K i)" for i
    unfolding K_def
    by (rule negligible_singular_image_2n[
          where f="fst \<circ> charts i" and S="Crit i"
            and f'="\<lambda>x. blinfun_apply (D i x)"])
       (use der rank in blast)+
  show ?thesis
    by (rule meager_negligible_closed_cover[OF Kcover])
       (use Kclosed Kneg in blast)+
qed

lemma d3_actual_arc_chart_core_iff_projection_data:
  "d3_actual_arc_chart_core V \<omega>0 \<omega>s \<gamma>
    \<longleftrightarrow>
   d3_projection_chart_data
      (V \<inter> D3BadXG \<omega>0 \<omega>s \<gamma>)"
  unfolding d3_actual_arc_chart_core_def d3_projection_chart_data_def ..

definition D3ActualArcIncidence ::
    "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2
      \<Rightarrow> (real \<Rightarrow> real^2) \<Rightarrow> real set
      \<Rightarrow> (((real^2)^'n) \<times> real) set"
  where
  "D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I =
    {q. fst q \<in> V \<and> snd q \<in> I
      \<and> fst q \<in> D3BadXG \<omega>0 \<omega>s {\<phi> (snd q)}}"

lemma D3ActualArcIncidence_fst_image:
  "fst ` D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I
    = (V \<inter> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)
        :: ((real^2)^'n::finite) set)"
proof
  show "fst ` D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I
      \<subseteq> (V \<inter> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)
        :: ((real^2)^'n) set)"
  proof
    fix x
    assume "x \<in> fst ` D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I"
    then obtain q where qI:
        "q \<in> D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I"
      and xeq: "x = fst q"
      by blast
    have xV: "fst q \<in> V"
      and tI: "snd q \<in> I"
      and xbad:
        "fst q \<in> D3BadXG \<omega>0 \<omega>s {\<phi> (snd q)}"
      using qI unfolding D3ActualArcIncidence_def by auto
    have sub: "{\<phi> (snd q)} \<subseteq> \<phi> ` I"
      using tI by blast
    have "fst q \<in> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)"
      using D3BadXG_mono[OF sub] xbad by blast
    with xV xeq show
      "x \<in> (V \<inter> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)
        :: ((real^2)^'n) set)"
      by simp
  qed
next
  show "(V \<inter> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)
      :: ((real^2)^'n) set)
      \<subseteq> fst ` D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I"
  proof
    fix x
    assume xall:
        "x \<in> (V \<inter> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)
          :: ((real^2)^'n) set)"
    have xV: "x \<in> V" using xall by simp
    have xbad: "x \<in> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)"
      using xall by simp
    obtain t where tI: "t \<in> I"
      and xsingle: "x \<in> D3BadXG \<omega>0 \<omega>s {\<phi> t}"
      using xbad unfolding D3BadXG_def by blast
    have "(x,t) \<in> D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I"
      unfolding D3ActualArcIncidence_def
      using xV tI xsingle by simp
    then show
      "x \<in> fst ` D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I"
      by force
  qed
qed

theorem d3_projection_chart_data_fst_image_of_Lindelof_patches:
  fixes M :: "(((real^2)^'n::finite) \<times> real) set"
  assumes local: "\<And>q. q \<in> M \<Longrightarrow>
    \<exists>S C.
       openin (top_of_set M) S
     \<and> q \<in> S
     \<and> fst ` S \<subseteq> C
     \<and> d3_projection_chart_data C"
  shows "d3_projection_chart_data (fst ` M)"
proof -
  define \<F> where
    "\<F> = {S. openin (top_of_set M) S
      \<and> (\<exists>C. fst ` S \<subseteq> C
        \<and> d3_projection_chart_data C)}"
  have Fopen: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S"
    unfolding \<F>_def by blast
  have Fcover: "M \<subseteq> \<Union>\<F>"
  proof
    fix q
    assume qM: "q \<in> M"
    obtain S C where Sopen: "openin (top_of_set M) S"
      and qS: "q \<in> S"
      and fstsub: "fst ` S \<subseteq> C"
      and Cdata: "d3_projection_chart_data C"
      using local[OF qM] by blast
    have "S \<in> \<F>"
      unfolding \<F>_def using Sopen fstsub Cdata by blast
    with qS show "q \<in> \<Union>\<F>" by blast
  qed
  obtain \<F>' where F'sub: "\<F>' \<subseteq> \<F>"
    and F'cnt: "countable \<F>'"
    and coverF': "M \<subseteq> \<Union>\<F>'"
    by (rule countable_subcover_of_openin_cover[OF Fopen Fcover])
  show ?thesis
  proof (cases "M = {}")
    case True
    show ?thesis
      using d3_projection_chart_data_empty
      unfolding True by simp
  next
    case False
    have F'ne: "\<F>' \<noteq> {}"
      using coverF' False by auto
    obtain e :: "nat \<Rightarrow> (((real^2)^'n) \<times> real) set"
      where eimg: "\<Union>(range e) = \<Union>\<F>'"
        and erng: "\<And>i. e i \<in> \<F>'"
    proof -
      let ?e = "from_nat_into \<F>'"
      have img: "\<Union>(range ?e) = \<Union>\<F>'"
        by (metis F'cnt F'ne range_from_nat_into
            top1_countable_nonempty_eq_image_nat uncountable_def)
      have rng: "\<And>i. ?e i \<in> \<F>'"
        using F'ne by (simp add: from_nat_into)
      show ?thesis by (rule that[OF img rng])
    qed
    have exC: "\<forall>i. \<exists>C.
        fst ` e i \<subseteq> C \<and> d3_projection_chart_data C"
    proof
      fix i
      have "e i \<in> \<F>"
        using erng[of i] F'sub by blast
      then show "\<exists>C.
          fst ` e i \<subseteq> C \<and> d3_projection_chart_data C"
        unfolding \<F>_def by blast
    qed
    obtain C :: "nat \<Rightarrow> ((real^2)^'n) set"
      where Cpick: "\<And>i.
        fst ` e i \<subseteq> C i
        \<and> d3_projection_chart_data (C i)"
      using exC unfolding choice_iff by blast
    have proj_sub: "fst ` M \<subseteq> (\<Union>i. C i)"
    proof
      fix x
      assume xproj: "x \<in> fst ` M"
      then obtain q where qM: "q \<in> M" and xeq: "x = fst q"
        by blast
      have "q \<in> \<Union>\<F>'"
        using coverF' qM by blast
      then have "q \<in> \<Union>(range e)"
        using eimg by simp
      then obtain i where qi: "q \<in> e i" by blast
      have "fst q \<in> C i"
        using Cpick[of i] qi by blast
      with xeq show "x \<in> (\<Union>i. C i)" by blast
    qed
    have union_data:
        "d3_projection_chart_data (\<Union>i. C i)"
      by (rule d3_projection_chart_data_countable_UN)
         (use Cpick in blast)
    show ?thesis
      by (rule d3_projection_chart_data_mono[
          OF proj_sub union_data])
  qed
qed

theorem d3_actual_arc_chart_core_of_Lindelof_incidence_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> :: "real \<Rightarrow> real^2"
    and \<omega>0 \<omega>s :: "real^2"
    and I :: "real set"
    and M :: "(((real^2)^'n) \<times> real) set"
  defines "M \<equiv> D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> I"
  assumes local: "\<And>q. q \<in> M \<Longrightarrow>
    \<exists>S C.
       openin (top_of_set M) S
     \<and> q \<in> S
     \<and> fst ` S \<subseteq> C
     \<and> d3_projection_chart_data C"
  shows "d3_actual_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` I)"
proof -
  define \<F> where
    "\<F> = {S. openin (top_of_set M) S
      \<and> (\<exists>C. fst ` S \<subseteq> C
        \<and> d3_projection_chart_data C)}"
  have Fopen: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S"
    unfolding \<F>_def by blast
  have Fcover: "M \<subseteq> \<Union>\<F>"
  proof
    fix q
    assume qM: "q \<in> M"
    obtain S C where Sopen: "openin (top_of_set M) S"
      and qS: "q \<in> S"
      and fstsub: "fst ` S \<subseteq> C"
      and Cdata: "d3_projection_chart_data C"
      using local[OF qM] by blast
    have "S \<in> \<F>"
      unfolding \<F>_def using Sopen fstsub Cdata by blast
    with qS show "q \<in> \<Union>\<F>" by blast
  qed
  obtain \<F>' where F'sub: "\<F>' \<subseteq> \<F>"
    and F'cnt: "countable \<F>'"
    and coverF': "M \<subseteq> \<Union>\<F>'"
    by (rule countable_subcover_of_openin_cover[OF Fopen Fcover])
  show ?thesis
  proof (cases "M = {}")
    case True
    have target_empty:
        "(V \<inter> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)
          :: ((real^2)^'n) set) = {}"
      using D3ActualArcIncidence_fst_image[
        of V \<omega>0 \<omega>s \<phi> I]
      unfolding M_def[symmetric] True by simp
    show ?thesis
      unfolding d3_actual_arc_chart_core_iff_projection_data target_empty
      by (rule d3_projection_chart_data_empty)
  next
    case False
    have F'ne: "\<F>' \<noteq> {}"
      using coverF' False by auto
    obtain e :: "nat \<Rightarrow> (((real^2)^'n) \<times> real) set"
      where eimg: "\<Union>(range e) = \<Union>\<F>'"
        and erng: "\<And>i. e i \<in> \<F>'"
    proof -
      let ?e = "from_nat_into \<F>'"
      have img: "\<Union>(range ?e) = \<Union>\<F>'"
        by (metis F'cnt F'ne range_from_nat_into
            top1_countable_nonempty_eq_image_nat uncountable_def)
      have rng: "\<And>i. ?e i \<in> \<F>'"
        using F'ne by (simp add: from_nat_into)
      show ?thesis by (rule that[OF img rng])
    qed
    have exC: "\<forall>i. \<exists>C.
        fst ` e i \<subseteq> C \<and> d3_projection_chart_data C"
    proof
      fix i
      have "e i \<in> \<F>"
        using erng[of i] F'sub by blast
      then show "\<exists>C.
          fst ` e i \<subseteq> C \<and> d3_projection_chart_data C"
        unfolding \<F>_def by blast
    qed
    obtain C :: "nat \<Rightarrow> ((real^2)^'n) set"
      where Cpick: "\<And>i.
        fst ` e i \<subseteq> C i
        \<and> d3_projection_chart_data (C i)"
      using exC unfolding choice_iff by blast
    have proj_sub:
        "fst ` M \<subseteq> (\<Union>i. C i)"
    proof
      fix x
      assume xproj: "x \<in> fst ` M"
      then obtain q where qM: "q \<in> M" and xeq: "x = fst q"
        by blast
      have "q \<in> \<Union>\<F>'"
        using coverF' qM by blast
      then have "q \<in> \<Union>(range e)"
        using eimg by simp
      then obtain i where qi: "q \<in> e i" by blast
      have "fst q \<in> C i"
        using Cpick[of i] qi by blast
      with xeq show "x \<in> (\<Union>i. C i)" by blast
    qed
    have union_data:
        "d3_projection_chart_data (\<Union>i. C i)"
      by (rule d3_projection_chart_data_countable_UN)
         (use Cpick in blast)
    have target_sub:
        "(V \<inter> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)
          :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. C i)"
      using proj_sub D3ActualArcIncidence_fst_image[
        of V \<omega>0 \<omega>s \<phi> I]
      unfolding M_def by simp
    have target_data:
        "d3_projection_chart_data
          (V \<inter> D3BadXG \<omega>0 \<omega>s (\<phi> ` I)
            :: ((real^2)^'n) set)"
      by (rule d3_projection_chart_data_mono[
          OF target_sub union_data])
    show ?thesis
      unfolding d3_actual_arc_chart_core_iff_projection_data
      by (rule target_data)
  qed
qed

lemma arc_schur_point_open_actual_patch:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
    and q :: "((real^2)^'n) \<times> real"
    and r :: "(real^2)^'n"
    and \<omega>0 \<omega>s :: "real^2"
    and a b :: real
    and M :: "(((real^2)^'n) \<times> real) set"
  defines "M \<equiv>
      D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> {a<..<b}"
  assumes qM: "q \<in> M"
    and phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow>
      (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    and trans:
      "vec_nth
        (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
          (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    and schur:
      "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi>
        (\<lambda>_. snd q) (fst q) r \<noteq> 0"
  shows "\<exists>S C.
       openin (top_of_set M) S
     \<and> q \<in> S
     \<and> fst ` S \<subseteq> C
     \<and> d3_projection_chart_data C"
proof -
  have tab: "a < snd q" "snd q < b"
    using qM unfolding M_def D3ActualArcIncidence_def by auto
  have xbad:
      "fst q \<in> D3BadXG \<omega>0 \<omega>s {\<phi> (snd q)}"
    using qM unfolding M_def D3ActualArcIncidence_def by simp
  have crit:
      "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (fst q) (\<phi> (snd q)) = 0"
    using xbad unfolding D3BadXG_def by blast
  obtain B \<epsilon> \<tau> \<rho> C
      and charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where data:
       "open B
     \<and> fst q \<in> B
     \<and> 0 < \<epsilon>
     \<and> {snd q-\<epsilon><..<snd q+\<epsilon>} \<subseteq> {a<..<b}
     \<and> \<tau> (fst q) = snd q
     \<and> (\<forall>x\<in>B.
          \<tau> x \<in> {snd q-\<epsilon><..<snd q+\<epsilon>})
     \<and> (\<forall>x\<in>B.
          vec_nth
            (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
              x (\<phi> (\<tau> x))) 1 = 0)
     \<and> (\<forall>x\<in>B.
          \<forall>t\<in>{snd q-\<epsilon><..<snd q+\<epsilon>}.
          vec_nth
            (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
              x (\<phi> t)) 1 = 0
          \<longrightarrow> t = \<tau> x)
     \<and> (\<forall>x\<in>B.
          vec_nth
            (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
              x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0)
     \<and> 0 < \<rho>
     \<and> C = cball (fst q) \<rho>
          \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball (fst q) \<rho> \<subseteq> B
     \<and> fst q \<in> C
     \<and> (\<forall>x\<in>C.
          arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
     \<and> (\<forall>x t.
          x \<in> cball (fst q) \<rho>
          \<longrightarrow> t \<in> {snd q-\<epsilon><..<snd q+\<epsilon>}
          \<longrightarrow>
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0
          \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative
            (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` Crit i))"
    using arc_schur_point_local_critical_cover_chart_core_data[
      OF phid phic tab crit trans schur]
    by presburger
  define A where
    "A = ball (fst q) \<rho>
      \<times> {snd q-\<epsilon><..<snd q+\<epsilon>}"
  define S where "S = M \<inter> A"
  have openA: "open A"
    unfolding A_def by (intro open_Times) simp_all
  have openS: "openin (top_of_set M) S"
    unfolding S_def openin_open_eq using openA by blast
  have qS: "q \<in> S"
    unfolding S_def A_def
    using qM data by (cases q) auto
  have fstsub: "fst ` S \<subseteq> C"
  proof
    fix x
    assume "x \<in> fst ` S"
    then obtain p where pS: "p \<in> S" and xeq: "x = fst p"
      by blast
    have pM: "p \<in> M"
      and pxball: "fst p \<in> ball (fst q) \<rho>"
      and ptint:
        "snd p \<in> {snd q-\<epsilon><..<snd q+\<epsilon>}"
      using pS unfolding S_def A_def by auto
    have pbad:
        "fst p \<in> D3BadXG \<omega>0 \<omega>s {\<phi> (snd p)}"
      using pM unfolding M_def D3ActualArcIncidence_def by simp
    have pgz:
        "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
          (fst p) (\<phi> (snd p)) = 0"
      using pbad unfolding D3BadXG_def by blast
    have pxcball: "fst p \<in> cball (fst q) \<rho>"
      using pxball by simp
    have "fst p \<in> C"
      using data pxcball ptint pgz by blast
    with xeq show "x \<in> C" by simp
  qed
  have Cdata: "d3_projection_chart_data C"
    unfolding d3_projection_chart_data_def
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D])
       (use data in blast)
  show ?thesis
    by (intro exI[of _ S] exI[of _ C]
        conjI openS qS fstsub Cdata)
qed

theorem d3_actual_arc_chart_core_of_pointwise_arc_schur_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
    and M :: "(((real^2)^'n) \<times> real) set"
    and \<omega>0 \<omega>s :: "real^2"
    and a b :: real
  defines "M \<equiv>
      D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> {a<..<b}"
  assumes phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow>
      (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    and trans: "\<And>q. q \<in> M \<Longrightarrow>
      vec_nth
        (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
          (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    and schur: "\<And>q. q \<in> M \<Longrightarrow>
      \<exists>r. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi>
        (\<lambda>_. snd q) (fst q) r \<noteq> 0"
  shows "d3_actual_arc_chart_core V \<omega>0 \<omega>s
      (\<phi> ` {a<..<b})"
proof (rule d3_actual_arc_chart_core_of_Lindelof_incidence_patches[
    where I="{a<..<b}"])
  fix q
  assume qI:
      "q \<in> D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> {a<..<b}"
  have qM: "q \<in> M"
    using qI unfolding M_def .
  obtain r where rnz:
      "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi>
        (\<lambda>_. snd q) (fst q) r \<noteq> 0"
    using schur[OF qM] by blast
  show "\<exists>S C.
       openin
         (top_of_set
           (D3ActualArcIncidence V \<omega>0 \<omega>s \<phi> {a<..<b})) S
     \<and> q \<in> S
     \<and> fst ` S \<subseteq> C
     \<and> d3_projection_chart_data C"
    by (rule arc_schur_point_open_actual_patch[
        where r=r, OF qI phid phic trans[OF qM] rnz])
qed

theorem robust4_horizontal_actual_nonphase_point_open_patch:
  fixes V :: "((real^2)^'n::finite) set" and y :: real
    and q :: "((real^2)^'n) \<times> real"
    and M :: "(((real^2)^'n) \<times> real) set"
  defines "M \<equiv>
      D3ActualArcIncidence V
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qM: "q \<in> M"
    and Xi_nz:
      "Xi (fst q)
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [snd q, y]) (vector [1, 0]) \<noteq> 0"
    and nonphase:
      "\<not> robust4_actual_phase_aligned
        (fst q) (vector [snd q, y])"
  shows "\<exists>S C.
       openin (top_of_set M) S
     \<and> q \<in> S
     \<and> fst ` S \<subseteq> C
     \<and> d3_projection_chart_data C"
proof -
  have tI:
      "snd q \<in> {pi / 4<..<3 * pi / 4}"
    using qM unfolding M_def D3ActualArcIncidence_def by simp
  have tIclosed:
      "snd q \<in> {pi / 4..3 * pi / 4}"
    using tI by simp
  have wA:
      "(vector [snd q, y] :: real^2)
        \<in> robust4_horizontal_arc y"
    using tIclosed unfolding robust4_horizontal_arc_def by blast
  have xbad:
      "fst q \<in> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        {vector [snd q, y]}"
    using qM unfolding M_def D3ActualArcIncidence_def by simp
  have detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
          (vector [snd q, y]))) \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
        (vector [snd q, y]) \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have h11nz:
      "vec_nth
        (vec_nth
          (HessU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip (fst q) (vector [snd q, y])) 1) 1 \<noteq> 0"
    using Xi_nz
      robust4_horizontal_arc_actual_Xi_horizontal_nonzero_iff[
        OF wA y3 detnz cnz, of "fst q"]
    by simp
  have trans:
      "vec_nth
        (HessU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip (fst q) (vector [snd q, y])
          *v vector [1, 0]) 1 \<noteq> 0"
    using h11nz
    by (simp add: matrix_vector_mult_def sum_2 vector_2)
  obtain r where schur:
      "arc_schur_L
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>t. vector [t, y]) (\<lambda>_. vector [1, 0])
        (\<lambda>_. snd q) (fst q) r \<noteq> 0"
    using robust4_horizontal_arc_actual_schur_or_phase_aligned[
        OF tIclosed y3 detnz cnz, of "fst q"]
      nonphase
    by blast
  have phi_eq:
      "(\<lambda>s::real. vector [s, y] :: real^2)
        = (\<lambda>s. s *\<^sub>R vector [1, 0] + vector [0, y])"
    by (rule ext)
       (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
          vector_add_component vector_scaleR_component)
  have phid:
      "\<And>t. pi / 4 < t \<Longrightarrow> t < 3 * pi / 4 \<Longrightarrow>
        ((\<lambda>s::real. vector [s, y] :: real^2)
          has_vector_derivative vector [1, 0]) (at t)"
    unfolding phi_eq
    by (auto intro!: derivative_eq_intros
        simp: has_vector_derivative_def)
  have phic:
      "continuous_on {pi / 4<..<3 * pi / 4}
        (\<lambda>_::real. vector [1, 0] :: real^2)"
    by (rule continuous_on_const)
  have qI:
      "q \<in> D3ActualArcIncidence V
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
    using qM unfolding M_def .
  show ?thesis
    unfolding M_def
    by (rule arc_schur_point_open_actual_patch[
        OF qI phid phic trans schur])
qed

definition D3ActualNonphaseXiIncidence ::
    "((real^2)^'n::finite) set \<Rightarrow> real
      \<Rightarrow> (((real^2)^'n) \<times> real) set"
  where
  "D3ActualNonphaseXiIncidence V y =
    {q \<in> D3ActualArcIncidence V
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}.
      Xi (fst q)
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [snd q, y]) (vector [1, 0]) \<noteq> 0
      \<and> \<not> robust4_actual_phase_aligned
        (fst q) (vector [snd q, y])}"

theorem robust4_horizontal_actual_nonphase_projection_chart_data:
  fixes V :: "((real^2)^'n::finite) set"
  assumes y3: "y \<in> {-pi, 0, pi}"
  shows "d3_projection_chart_data
      (fst ` D3ActualNonphaseXiIncidence V y)"
proof (rule d3_projection_chart_data_fst_image_of_Lindelof_patches)
  fix q
  assume qN: "q \<in> D3ActualNonphaseXiIncidence V y"
  let ?M =
    "D3ActualArcIncidence V
      (vector [pi / 2, 0]) (vector [0, 0])
      (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
  have qfacts:
      "q \<in> ?M
      \<and> Xi (fst q)
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [snd q, y]) (vector [1, 0]) \<noteq> 0
      \<and> \<not> robust4_actual_phase_aligned
        (fst q) (vector [snd q, y])"
    using qN unfolding D3ActualNonphaseXiIncidence_def by simp
  have qM: "q \<in> ?M"
    using qfacts by (rule conjunct1)
  have Xi_nz:
      "Xi (fst q)
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [snd q, y]) (vector [1, 0]) \<noteq> 0"
    using qfacts by (rule conjunct1[OF conjunct2])
  have nonphase:
      "\<not> robust4_actual_phase_aligned
        (fst q) (vector [snd q, y])"
    using qfacts by (rule conjunct2[OF conjunct2])
  have patch:
      "\<exists>S C.
        openin (top_of_set ?M) S
      \<and> q \<in> S
      \<and> fst ` S \<subseteq> C
      \<and> d3_projection_chart_data C"
    by (rule robust4_horizontal_actual_nonphase_point_open_patch[
        where V=V and y=y and q=q,
        OF y3 qM Xi_nz nonphase])
  obtain S C where Sopen: "openin (top_of_set ?M) S"
    and qS: "q \<in> S"
    and fstsub: "fst ` S \<subseteq> C"
    and Cdata: "d3_projection_chart_data C"
    using patch by blast
  define S' where
    "S' = S \<inter> D3ActualNonphaseXiIncidence V y"
  have Nsub:
      "D3ActualNonphaseXiIncidence V y \<subseteq> ?M"
    unfolding D3ActualNonphaseXiIncidence_def by auto
  have S'open:
      "openin
        (top_of_set (D3ActualNonphaseXiIncidence V y)) S'"
  proof -
    have Ssub: "S \<subseteq> ?M"
      using openin_subset[OF Sopen] by simp
    have MS: "?M \<inter> S = S"
      using Ssub by auto
    have Mopen: "openin (top_of_set ?M) (?M \<inter> S)"
      unfolding MS by (rule Sopen)
    have Nopen:
        "openin
          (top_of_set (D3ActualNonphaseXiIncidence V y))
          (D3ActualNonphaseXiIncidence V y \<inter> S)"
      by (rule openin_subtopology_Int_subset[OF Mopen Nsub])
    show ?thesis
      unfolding S'_def using Nopen by (simp add: Int_commute)
  qed
  have qS': "q \<in> S'"
    unfolding S'_def using qS qN by simp
  have fstsub': "fst ` S' \<subseteq> C"
    unfolding S'_def using fstsub by blast
  show "\<exists>S C.
      openin
        (top_of_set (D3ActualNonphaseXiIncidence V y)) S
    \<and> q \<in> S
    \<and> fst ` S \<subseteq> C
    \<and> d3_projection_chart_data C"
    by (intro exI[of _ S'] exI[of _ C]
        conjI S'open qS' fstsub' Cdata)
qed

corollary robust4_horizontal_actual_nonphase_projection_meager:
  fixes V :: "((real^2)^'n::finite) set"
  assumes y3: "y \<in> {-pi, 0, pi}"
  shows "meager (fst ` D3ActualNonphaseXiIncidence V y)"
  by (rule d3_projection_chart_data_meager[
      OF robust4_horizontal_actual_nonphase_projection_chart_data[
        OF y3]])

definition D3ActualXiZeroNonphaseIncidence ::
    "((real^2)^'n::finite) set \<Rightarrow> real
      \<Rightarrow> (((real^2)^'n) \<times> real) set"
  where
  "D3ActualXiZeroNonphaseIncidence V y =
    {q \<in> D3ActualArcIncidence V
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}.
      Xi (fst q)
        (vector [pi / 2, 0]) (vector [0, 0])
        (vector [snd q, y]) (vector [1, 0]) = 0
      \<and> \<not> robust4_actual_phase_aligned
        (fst q) (vector [snd q, y])}"

theorem robust4_horizontal_actual_interior_projection_decomp:
  fixes V :: "((real^2)^'n::finite) set"
  assumes y3: "y \<in> {-pi, 0, pi}"
  shows "fst ` D3ActualArcIncidence V
      (vector [pi / 2, 0]) (vector [0, 0])
      (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}
    \<subseteq>
      D3ActualAlignedProjection
      \<union> fst ` D3ActualNonphaseXiIncidence V y
      \<union> fst ` D3ActualXiZeroNonphaseIncidence V y"
proof
  fix x
  assume xin:
      "x \<in> fst ` D3ActualArcIncidence V
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
  then obtain q where qM:
      "q \<in> D3ActualArcIncidence V
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
    and xeq: "x = fst q"
    by blast
  have tI: "snd q \<in> {pi / 4<..<3 * pi / 4}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have wA:
      "(vector [snd q, y] :: real^2) \<in> robust4_horizontal_arc y"
    using tI unfolding robust4_horizontal_arc_def by auto
  have wPF:
      "(vector [snd q, y] :: real^2)
        \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    using robust4_horizontal_arc_subset_OmegaPF[OF y3] wA by blast
  have xbad:
      "fst q \<in> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        {vector [snd q, y]}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
        (vector [snd q, y]) \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have Acnz:
      "A_cart
        (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
        (fst q) (vector [snd q, y]) \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  show "x \<in>
      D3ActualAlignedProjection
      \<union> fst ` D3ActualNonphaseXiIncidence V y
      \<union> fst ` D3ActualXiZeroNonphaseIncidence V y"
  proof (cases
      "robust4_actual_phase_aligned
        (fst q) (vector [snd q, y])")
    case True
    have "fst q \<in> D3ActualAlignedProjection"
      unfolding D3ActualAlignedProjection_def
      using wPF cnz Acnz True by blast
    with xeq show ?thesis by simp
  next
    case nonphase: False
    show ?thesis
    proof (cases
        "Xi (fst q)
          (vector [pi / 2, 0]) (vector [0, 0])
          (vector [snd q, y]) (vector [1, 0]) = 0")
      case False
      have "q \<in> D3ActualNonphaseXiIncidence V y"
        unfolding D3ActualNonphaseXiIncidence_def
        using qM nonphase False by simp
      with xeq show ?thesis by blast
    next
      case True
      have "q \<in> D3ActualXiZeroNonphaseIncidence V y"
        unfolding D3ActualXiZeroNonphaseIncidence_def
        using qM nonphase True by simp
      with xeq show ?thesis by blast
    qed
  qed
qed

theorem robust4_horizontal_actual_interior_projection_meager_of_Xi_zero:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and y3: "y \<in> {-pi, 0, pi}"
    and residual:
      "meager (fst ` D3ActualXiZeroNonphaseIncidence V y)"
  shows "meager
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        ((\<lambda>t. vector [t, y]) ` {pi / 4<..<3 * pi / 4})
        :: ((real^2)^'n) set)"
proof -
  have aligned: "meager
      (D3ActualAlignedProjection :: ((real^2)^'n) set)"
    by (rule robust4_actual_aligned_projection_meager[OF card4])
  have nonphase:
      "meager (fst ` D3ActualNonphaseXiIncidence V y)"
    by (rule robust4_horizontal_actual_nonphase_projection_meager[OF y3])
  have union_meager:
      "meager
        (D3ActualAlignedProjection
          \<union> fst ` D3ActualNonphaseXiIncidence V y
          \<union> fst ` D3ActualXiZeroNonphaseIncidence V y)"
    by (rule meager_Un[OF meager_Un[OF aligned nonphase] residual])
  have sub:
      "fst ` D3ActualArcIncidence V
        (vector [pi / 2, 0]) (vector [0, 0])
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}
      \<subseteq>
        D3ActualAlignedProjection
        \<union> fst ` D3ActualNonphaseXiIncidence V y
        \<union> fst ` D3ActualXiZeroNonphaseIncidence V y"
    by (rule robust4_horizontal_actual_interior_projection_decomp[OF y3])
  have image_meager:
      "meager
        (fst ` D3ActualArcIncidence V
          (vector [pi / 2, 0]) (vector [0, 0])
          (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4})"
    by (rule meager_subset[OF sub union_meager])
  show ?thesis
    using image_meager
    unfolding D3ActualArcIncidence_fst_image .
qed

lemma robust4_horizontal_actual_endpoint_projection_meager:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and endpoint: "t \<in> {pi / 4, 3 * pi / 4}"
  shows "meager
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        {vector [t, y]}
        :: ((real^2)^'n) set)"
proof (rule d3_actual_arc_projection_meager)
  show "d3_actual_arc_chart_core V
      (vector [pi / 2, 0]) (vector [0, 0]) {vector [t, y]}"
  proof (rule d3_actual_arc_chart_core_of_H0core)
    show "d3_detHess_arc_chart_core V
        (vector [pi / 2, 0]) (vector [0, 0]) {vector [t, y]}"
    proof (rule fixed_omega_H0core_chart_core_robust4_all_angles)
      show "0 < vec_nth (vector [t, y] :: real^2) 1"
        using endpoint pi_gt_zero by (auto simp: vector_2; linarith)
      show "vec_nth (vector [t, y] :: real^2) 1 < pi"
        using endpoint pi_gt_zero by (auto simp: vector_2; linarith)
      show "2 \<le> CARD('n)" by (rule card2)
    qed
  qed
qed

lemma D3BadXG_singleton_witness:
  assumes xbad:
      "x \<in> (D3BadXG \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n::finite) set)"
  obtains \<omega> where "\<omega> \<in> \<Gamma>"
    and "x \<in> D3BadXG \<omega>0 \<omega>s {\<omega>}"
  using xbad unfolding D3BadXG_def by blast

lemma robust4_horizontal_actual_arc_projection_subset:
  fixes V :: "((real^2)^'n::finite) set"
  shows "(V \<inter> D3BadXG
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)
      :: ((real^2)^'n) set)
    \<subseteq>
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        ((\<lambda>t. vector [t, y]) ` {pi / 4<..<3 * pi / 4}))
      \<union>
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        {vector [pi / 4, y]})
      \<union>
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        {vector [3 * pi / 4, y]})"
proof
  fix x
  assume xin:
      "x \<in> (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc y)
        :: ((real^2)^'n) set)"
  have xV: "x \<in> V"
    using xin by simp
  have xbad:
      "x \<in> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc y)"
    using xin by simp
  obtain \<omega> where wA: "\<omega> \<in> robust4_horizontal_arc y"
    and xsingle:
      "x \<in> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0]) {\<omega>}"
    by (rule D3BadXG_singleton_witness[OF xbad])
  obtain t where tI: "t \<in> {pi / 4..3 * pi / 4}"
    and weq: "\<omega> = vector [t, y]"
    using wA unfolding robust4_horizontal_arc_def by blast
  have cases:
      "t = pi / 4 \<or> t = 3 * pi / 4
        \<or> t \<in> {pi / 4<..<3 * pi / 4}"
    using tI by auto
  show "x \<in>
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        ((\<lambda>t. vector [t, y]) ` {pi / 4<..<3 * pi / 4}))
      \<union>
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        {vector [pi / 4, y]})
      \<union>
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        {vector [3 * pi / 4, y]})"
  proof (rule disjE[OF cases])
    assume "t = pi / 4"
    with xV xsingle weq show ?thesis by simp
  next
    assume rest:
        "t = 3 * pi / 4 \<or> t \<in> {pi / 4<..<3 * pi / 4}"
    show ?thesis
    proof (rule disjE[OF rest])
      assume "t = 3 * pi / 4"
      with xV xsingle weq show ?thesis by simp
    next
      assume tint: "t \<in> {pi / 4<..<3 * pi / 4}"
      have omem:
          "vector [t, y]
            \<in> (\<lambda>s. vector [s, y])
              ` {pi / 4<..<3 * pi / 4}"
        using tint by blast
      have sub:
          "{\<omega>} \<subseteq>
            (\<lambda>s. vector [s, y])
              ` {pi / 4<..<3 * pi / 4}"
        using omem weq by simp
      have xopen:
          "x \<in> D3BadXG
            (vector [pi / 2, 0]) (vector [0, 0])
            ((\<lambda>s. vector [s, y])
              ` {pi / 4<..<3 * pi / 4})"
        using D3BadXG_mono[OF sub] xsingle by blast
      with xV show ?thesis by simp
    qed
  qed
qed

theorem robust4_horizontal_actual_arc_projection_meager_of_Xi_zero:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and y3: "y \<in> {-pi, 0, pi}"
    and residual:
      "meager (fst ` D3ActualXiZeroNonphaseIncidence V y)"
  shows "meager
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc y)
        :: ((real^2)^'n) set)"
proof -
  have card2: "2 \<le> CARD('n)"
    using card4 by simp
  have interior:
      "meager
        (V \<inter> D3BadXG
          (vector [pi / 2, 0]) (vector [0, 0])
          ((\<lambda>t. vector [t, y]) ` {pi / 4<..<3 * pi / 4})
          :: ((real^2)^'n) set)"
    by (rule
        robust4_horizontal_actual_interior_projection_meager_of_Xi_zero[
          OF card4 y3 residual])
  have left:
      "meager
        (V \<inter> D3BadXG
          (vector [pi / 2, 0]) (vector [0, 0])
          {vector [pi / 4, y]}
          :: ((real^2)^'n) set)"
    by (rule robust4_horizontal_actual_endpoint_projection_meager[
        OF card2]) simp
  have right:
      "meager
        (V \<inter> D3BadXG
          (vector [pi / 2, 0]) (vector [0, 0])
          {vector [3 * pi / 4, y]}
          :: ((real^2)^'n) set)"
    by (rule robust4_horizontal_actual_endpoint_projection_meager[
        OF card2]) simp
  have union_meager:
      "meager
        ((V \<inter> D3BadXG
            (vector [pi / 2, 0]) (vector [0, 0])
            ((\<lambda>t. vector [t, y]) ` {pi / 4<..<3 * pi / 4}))
        \<union>
         (V \<inter> D3BadXG
            (vector [pi / 2, 0]) (vector [0, 0])
            {vector [pi / 4, y]})
        \<union>
         (V \<inter> D3BadXG
            (vector [pi / 2, 0]) (vector [0, 0])
            {vector [3 * pi / 4, y]})
          :: ((real^2)^'n) set)"
    by (rule meager_Un[OF meager_Un[OF interior left] right])
  show ?thesis
    by (rule meager_subset[
        OF robust4_horizontal_actual_arc_projection_subset union_meager])
qed

theorem m5_D34_D3_collinear_robust4_of_three_actual_arc_meager:
  fixes V :: "((real^2)^'n::finite) set"
  assumes neg:
      "meager
        (V \<inter> D3BadXG
          (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc (-pi))
          :: ((real^2)^'n) set)"
    and zero:
      "meager
        (V \<inter> D3BadXG
          (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc 0)
          :: ((real^2)^'n) set)"
    and pos:
      "meager
        (V \<inter> D3BadXG
          (vector [pi / 2, 0]) (vector [0, 0])
          (robust4_horizontal_arc pi)
          :: ((real^2)^'n) set)"
  shows "meager {x \<in> V.
      \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
        gradU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega> = 0
      \<and> det
          (HessU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip x \<omega>) = 0
      \<and> A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          x \<omega> \<noteq> 0
      \<and> det
          (matrix
            (Dcvec_dip
              (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))
          \<noteq> 0
      \<and> cvec_dip
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
      \<and> \<not> surj
          (DM_paper_x x
            (cvec_dip
              (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>y. gradU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip y \<omega>) has_derivative Dx) (at x)
          \<and> surj Dx)
      \<and> phase_collinear
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
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
  have unions:
      "meager
        ((V \<inter> D3BadXG ?w0 ?ws ?neg)
          \<union> (V \<inter> D3BadXG ?w0 ?ws ?zero)
          \<union> (V \<inter> D3BadXG ?w0 ?ws ?pos)
          :: ((real^2)^'n) set)"
    by (rule meager_Un[OF meager_Un[OF neg zero] pos])
  have cover:
      "(V \<inter> D3BadXG ?w0 ?ws ?L :: ((real^2)^'n) set)
        \<subseteq>
          (V \<inter> D3BadXG ?w0 ?ws ?neg)
          \<union> (V \<inter> D3BadXG ?w0 ?ws ?zero)
          \<union> (V \<inter> D3BadXG ?w0 ?ws ?pos)"
    unfolding robust4_phase_collinear_locus_exact D3BadXG_def by blast
  have "meager ?S"
    unfolding eqS by (rule meager_subset[OF cover unions])
  then show ?thesis .
qed

theorem m5_D34_D3_collinear_robust4_of_actual_Xi_zero_residuals:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card4: "4 \<le> CARD('n)"
    and neg_residual:
      "meager
        (fst ` D3ActualXiZeroNonphaseIncidence V (-pi))"
    and zero_residual:
      "meager
        (fst ` D3ActualXiZeroNonphaseIncidence V 0)"
    and pos_residual:
      "meager
        (fst ` D3ActualXiZeroNonphaseIncidence V pi)"
  shows "meager {x \<in> V.
      \<exists>\<omega>\<in>OmegaPF (vector [pi / 2, 0]) (pi / 4).
        gradU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega> = 0
      \<and> det
          (HessU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip x \<omega>) = 0
      \<and> A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          x \<omega> \<noteq> 0
      \<and> det
          (matrix
            (Dcvec_dip
              (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))
          \<noteq> 0
      \<and> cvec_dip
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
      \<and> \<not> surj
          (DM_paper_x x
            (cvec_dip
              (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>y. gradU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip y \<omega>) has_derivative Dx) (at x)
          \<and> surj Dx)
      \<and> phase_collinear
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega>}"
proof (rule m5_D34_D3_collinear_robust4_of_three_actual_arc_meager)
  show "meager
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc (-pi))
        :: ((real^2)^'n) set)"
    by (rule robust4_horizontal_actual_arc_projection_meager_of_Xi_zero[
        OF card4 _ neg_residual]) simp
  show "meager
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc 0)
        :: ((real^2)^'n) set)"
    by (rule robust4_horizontal_actual_arc_projection_meager_of_Xi_zero[
        OF card4 _ zero_residual]) simp
  show "meager
      (V \<inter> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc pi)
        :: ((real^2)^'n) set)"
    by (rule robust4_horizontal_actual_arc_projection_meager_of_Xi_zero[
        OF card4 _ pos_residual]) simp
qed

theorem robust4_actual_Xi_zero_incidence_Hessian_reduction:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "((real^2)^'n) \<times> real"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qR: "q \<in> D3ActualXiZeroNonphaseIncidence V y"
  shows
    "vec_nth
        (vec_nth
          (HessU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip (fst q) (vector [snd q, y])) 1) 1 = 0
    \<and> vec_nth
        (vec_nth
          (HessU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip (fst q) (vector [snd q, y])) 1) 2 = 0
    \<and> H_par (fst q) (vector [snd q, y])
        (vector [pi / 2, 0]) (vector [0, 0]) = 0"
proof -
  let ?om = "vector [snd q, y] :: real^2"
  let ?center = "vector [pi / 2, 0] :: real^2"
  let ?steer = "vector [0, 0] :: real^2"
  let ?H =
    "HessU (cvec_dip ?center ?steer) gain_dip (fst q) ?om"
  have qM:
      "q \<in> D3ActualArcIncidence V ?center ?steer
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
    and Xi0:
      "Xi (fst q) ?center ?steer ?om (vector [1, 0]) = 0"
    using qR unfolding D3ActualXiZeroNonphaseIncidence_def by simp_all
  have tI: "snd q \<in> {pi / 4<..<3 * pi / 4}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have wA: "?om \<in> robust4_horizontal_arc y"
    using tI unfolding robust4_horizontal_arc_def by auto
  have xbad: "fst q \<in> D3BadXG ?center ?steer {?om}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have detnz:
      "det (matrix (Dcvec_dip ?center ?steer ?om)) \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have cnz: "cvec_dip ?center ?steer ?om \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have detH: "det ?H = 0"
    using xbad unfolding D3BadXG_def by blast
  have h11:
      "vec_nth (vec_nth ?H 1) 1 = 0"
    using Xi0
      robust4_horizontal_arc_actual_Xi_horizontal_nonzero_iff[
        OF wA y3 detnz cnz, of "fst q"]
    by simp
  have detform:
      "det ?H =
        vec_nth (vec_nth ?H 1) 1 * vec_nth (vec_nth ?H 2) 2
        - (vec_nth (vec_nth ?H 1) 2)\<^sup>2"
    by (rule det_2_symmetric[OF HessU_dip_symmetric])
  have h12:
      "vec_nth (vec_nth ?H 1) 2 = 0"
    using detH h11 detform by simp
  have e2:
      "vec_nth (e_par ?center ?steer ?om) 2 = 0"
    by (rule robust4_horizontal_arc_actual_e_par_second_zero[
        OF wA y3 detnz])
  have hpar:
      "H_par (fst q) ?om ?center ?steer = 0"
    unfolding H_par_def
    using h11 e2 by simp
  show ?thesis
    using h11 h12 hpar by simp
qed

theorem robust4_actual_Xi_zero_incidence_gradU2_arc_derivative_zero:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "((real^2)^'n) \<times> real"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qR: "q \<in> D3ActualXiZeroNonphaseIncidence V y"
  shows "((\<lambda>t. vec_nth
      (gradU
        (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
        gain_dip (fst q) (vector [t, y])) 2)
      has_field_derivative 0) (at (snd q))"
proof -
  let ?om = "vector [snd q, y] :: real^2"
  let ?center = "vector [pi / 2, 0] :: real^2"
  let ?steer = "vector [0, 0] :: real^2"
  let ?H =
    "HessU (cvec_dip ?center ?steer) gain_dip (fst q) ?om"
  have red:
      "vec_nth (vec_nth ?H 1) 1 = 0
    \<and> vec_nth (vec_nth ?H 1) 2 = 0
    \<and> H_par (fst q) ?om ?center ?steer = 0"
    by (rule robust4_actual_Xi_zero_incidence_Hessian_reduction[
        OF y3 qR])
  have h12: "vec_nth (vec_nth ?H 1) 2 = 0"
    using red by simp
  have sym:
      "vec_nth (vec_nth ?H 1) 2
        = vec_nth (vec_nth ?H 2) 1"
    by (rule HessU_dip_symmetric)
  have h21: "vec_nth (vec_nth ?H 2) 1 = 0"
    using h12 sym by simp
  have phi_eq:
      "(\<lambda>s::real. vector [s, y] :: real^2)
        = (\<lambda>s. s *\<^sub>R vector [1, 0] + vector [0, y])"
    by (rule ext)
       (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2
          vector_add_component vector_scaleR_component)
  have phid:
      "((\<lambda>s::real. vector [s, y] :: real^2)
        has_derivative (\<lambda>r. r *\<^sub>R vector [1, 0]))
        (at (snd q))"
    unfolding phi_eq
    by (auto intro!: derivative_eq_intros)
  have gd:
      "(gradU (cvec_dip ?center ?steer) gain_dip (fst q)
        has_derivative (\<lambda>v. ?H *v v)) (at ?om)"
    by (rule gradU_dip_has_derivative)
  have chain:
      "((\<lambda>t. gradU
          (cvec_dip ?center ?steer) gain_dip
          (fst q) (vector [t, y]))
        has_derivative
          (\<lambda>r. ?H *v (r *\<^sub>R vector [1, 0])))
        (at (snd q))"
    using diff_chain_at[OF phid gd]
    by (simp add: o_def)
  have comp2:
      "((\<lambda>t. vec_nth
          (gradU
            (cvec_dip ?center ?steer) gain_dip
            (fst q) (vector [t, y])) 2)
        has_derivative
          (\<lambda>r. vec_nth
            (?H *v (r *\<^sub>R vector [1, 0])) 2))
        (at (snd q))"
    by (rule bounded_linear.has_derivative[
        OF bounded_linear_vec_nth chain])
  have action0:
      "vec_nth (?H *v (r *\<^sub>R vector [1, 0])) 2 = 0" for r
    using h21
    by (simp add: matrix_vector_mult_def sum_2 vector_2)
  show ?thesis
    unfolding has_field_derivative_def
    by (rule has_derivative_eq_rhs[OF comp2])
       (simp add: fun_eq_iff action0)
qed

theorem robust4_actual_Xi_zero_nonphase_s2_witness:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "((real^2)^'n) \<times> real"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qR: "q \<in> D3ActualXiZeroNonphaseIncidence V y"
  obtains k :: 'n where
    "d3_s2_perp_slot
      (vector [pi / 2, 0]) (vector [0, 0])
      (vector [snd q, y]) k (fst q) \<noteq> 0"
proof -
  let ?om = "vector [snd q, y] :: real^2"
  let ?center = "vector [pi / 2, 0] :: real^2"
  let ?steer = "vector [0, 0] :: real^2"
  have qM:
      "q \<in> D3ActualArcIncidence V ?center ?steer
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
    and nonphase:
      "\<not> robust4_actual_phase_aligned (fst q) ?om"
    using qR unfolding D3ActualXiZeroNonphaseIncidence_def by simp_all
  have tI: "snd q \<in> {pi / 4<..<3 * pi / 4}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have wA: "?om \<in> robust4_horizontal_arc y"
    using tI unfolding robust4_horizontal_arc_def by auto
  have xbad: "fst q \<in> D3BadXG ?center ?steer {?om}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have detnz:
      "det (matrix (Dcvec_dip ?center ?steer ?om)) \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have cnz: "cvec_dip ?center ?steer ?om \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  obtain k :: 'n where phase_nz:
      "Im (cnj
          (vec_nth
            (M_paper (fst q) (cvec_dip ?center ?steer ?om)) 1)
        * phase (cvec_dip ?center ?steer ?om) (fst q) k) \<noteq> 0"
    using nonphase
    unfolding robust4_actual_phase_aligned_def by blast
  have facnz:
      "d3_s2_global_factor ?center ?steer ?om \<noteq> 0"
    by (rule robust4_horizontal_arc_actual_s2_factor_nonzero[
        OF wA y3 detnz cnz])
  have snz:
      "d3_s2_perp_slot ?center ?steer ?om k (fst q) \<noteq> 0"
    unfolding d3_s2_perp_slot_value
    using facnz phase_nz by simp
  show thesis
    by (rule that[OF snz])
qed

section \<open>The actual cubic regular-value map\<close>

text \<open>
  On the exact residual, the two equations which remain useful for eliminating
  the horizontal arc parameter are

    \<^item> the second component of the actual steering gradient, and
    \<^item> the \<open>(1,1)\<close> entry of the actual steering Hessian.

  The second coordinate of the auxiliary parameter below is deliberately
  ignored.  This harmless padding turns the one-dimensional arc parameter into
  a copy of \<open>\<real>\<^sup>2\<close>, so that the existing regular-value chart engine
  applies.  It also makes the parameter partial permanently nonsurjective,
  which is exactly the rank defect needed for the projection to configuration
  space.
\<close>

definition robust4_actual_cubic_map ::
    "real \<Rightarrow> (((real^2)^'n::finite) \<times> (real^2)) \<Rightarrow> real^2"
  where
  "robust4_actual_cubic_map y p =
    vector [
      vec_nth
        (gradU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip (fst p)
          (vector [vec_nth (snd p) 1, y])) 2,
      vec_nth
        (vec_nth
          (HessU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip (fst p)
            (vector [vec_nth (snd p) 1, y])) 1) 1]"

definition robust4_actual_arc_cubic ::
    "((real^2)^'n::finite) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where
  "robust4_actual_arc_cubic x y t =
    deriv
      (\<lambda>s. vec_nth
        (vec_nth
          (HessU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip x (vector [s, y])) 1) 1)
      t"

lemma real_analytic_on_robust4_actual_cubic_map:
  "real_analytic_on
      (robust4_actual_cubic_map y ::
        (((real^2)^'n::finite) \<times> (real^2)) \<Rightarrow> real^2)
      UNIV"
proof -
  let ?sigma =
    "\<lambda>p::((real^2)^'n) \<times> (real^2).
      (fst p, vector [vec_nth (snd p) 1, y] :: real^2)"
  have fst_ana:
      "real_analytic_on
        (fst :: (((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((real^2)^'n))
        UNIV"
    by (rule real_analytic_on_fst[OF open_UNIV])
  have snd1_ana:
      "real_analytic_on
        (\<lambda>p::((real^2)^'n) \<times> (real^2).
          vec_nth (snd p) 1) UNIV"
  proof -
    have bl:
        "bounded_linear
          (\<lambda>p::((real^2)^'n) \<times> (real^2).
            vec_nth (snd p) 1)"
      by (rule bounded_linear_compose[
          OF bounded_linear_vec_nth bounded_linear_snd])
    show ?thesis
      by (rule real_analytic_on_bounded_linear[OF open_UNIV bl])
  qed
  have om_eq:
      "(\<lambda>p::((real^2)^'n) \<times> (real^2).
          vector [vec_nth (snd p) 1, y] :: real^2)
       =
       (\<lambda>p. vec_nth (snd p) 1 *\<^sub>R axis 1 1
          + y *\<^sub>R axis 2 1)"
    by (rule ext)
       (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2
          vector_2 axis_def)
  have om_ana:
      "real_analytic_on
        (\<lambda>p::((real^2)^'n) \<times> (real^2).
          vector [vec_nth (snd p) 1, y] :: real^2) UNIV"
    unfolding om_eq
    by (intro real_analytic_on_add real_analytic_on_scaleR_vec
          snd1_ana real_analytic_on_const[OF open_UNIV])
  have sigma_ana: "real_analytic_on ?sigma UNIV"
    by (rule real_analytic_on_Pair[OF fst_ana om_ana])
  have grad_ana:
      "real_analytic_on
        (\<lambda>p::((real^2)^'n) \<times> (real^2).
          gradU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip (fst p) (snd p)) UNIV"
    by (rule real_analytic_on_gradU_dip)
  have grad_comp_ana:
      "real_analytic_on
        (\<lambda>p::((real^2)^'n) \<times> (real^2).
          vec_nth
            (gradU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip (fst p)
              (vector [vec_nth (snd p) 1, y])) 2)
        UNIV"
  proof -
    have composed:
        "real_analytic_on
          (\<lambda>p::((real^2)^'n) \<times> (real^2).
            gradU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip (fst (?sigma p)) (snd (?sigma p)))
          UNIV"
      by (rule real_analytic_on_compose[
          OF sigma_ana grad_ana subset_UNIV])
    show ?thesis
      using real_analytic_on_compose[
        OF composed real_analytic_on_vec_nth subset_UNIV]
      by simp
  qed
  have hess_ana:
      "real_analytic_on
        (\<lambda>p::((real^2)^'n) \<times> (real^2).
          vec_nth
            (vec_nth
              (HessU
                (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
                gain_dip (fst p) (snd p)) 1) 1)
        UNIV"
    by (rule real_analytic_on_HessU_dip_entry)
  have hess_comp_ana:
      "real_analytic_on
        (\<lambda>p::((real^2)^'n) \<times> (real^2).
          vec_nth
            (vec_nth
              (HessU
                (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
                gain_dip (fst p)
                (vector [vec_nth (snd p) 1, y])) 1) 1)
        UNIV"
    using real_analytic_on_compose[
      OF sigma_ana hess_ana subset_UNIV]
    by simp
  have map_eq:
      "(robust4_actual_cubic_map y ::
          (((real^2)^'n) \<times> (real^2)) \<Rightarrow> real^2)
       =
       (\<lambda>p.
          vec_nth
            (gradU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip (fst p)
              (vector [vec_nth (snd p) 1, y])) 2
            *\<^sub>R axis 1 1
        + vec_nth
            (vec_nth
              (HessU
                (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
                gain_dip (fst p)
                (vector [vec_nth (snd p) 1, y])) 1) 1
            *\<^sub>R axis 2 1)"
    by (rule ext)
       (simp add: robust4_actual_cubic_map_def
          Finite_Cartesian_Product.vec_eq_iff forall_2
          vector_2 axis_def)
  show ?thesis
    unfolding map_eq
    by (intro real_analytic_on_add real_analytic_on_scaleR_vec
          grad_comp_ana hess_comp_ana
          real_analytic_on_const[OF open_UNIV])
qed

lemma robust4_actual_cubic_map_C1:
  obtains G' ::
      "(((real^2)^'n::finite) \<times> (real^2))
        \<Rightarrow>
        ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
  where
    "\<And>p. (robust4_actual_cubic_map y
      has_derivative blinfun_apply (G' p)) (at p)"
    and "continuous_on UNIV G'"
proof -
  have Cinf:
      "Cinfinity_on
        (robust4_actual_cubic_map y ::
          (((real^2)^'n) \<times> (real^2)) \<Rightarrow> real^2)
        UNIV"
    by (rule real_analytic_imp_Cinfinity[
        OF real_analytic_on_robust4_actual_cubic_map])
  have C1:
      "Ck_on (Suc 0)
        (robust4_actual_cubic_map y ::
          (((real^2)^'n) \<times> (real^2)) \<Rightarrow> real^2)
        UNIV"
    by (rule Cinfinity_on_imp_Ck_on[OF Cinf])
  let ?G' =
    "\<lambda>p::((real^2)^'n) \<times> (real^2).
      Dblinfun (robust4_actual_cubic_map y) p"
  have der:
      "(robust4_actual_cubic_map y
        has_derivative blinfun_apply (?G' p)) (at p)" for p
    by (rule Ck1_on_imp_has_derivative_blinfun[OF C1])
       simp
  have cont: "continuous_on UNIV ?G'"
    by (rule Ck1_on_imp_continuous_Dblinfun[OF C1])
  show thesis
    by (rule that[OF der cont])
qed

lemma surj_linear_vec2_of_triangular_witnesses:
  fixes L :: "'a::real_vector \<Rightarrow> real^2"
  assumes lin: "linear L"
    and first_nz: "vec_nth (L u) 1 \<noteq> 0"
    and second_first_zero: "vec_nth (L v) 1 = 0"
    and second_nz: "vec_nth (L v) 2 \<noteq> 0"
  shows "surj L"
proof (unfold surj_def, intro allI)
  fix z :: "real^2"
  define a where "a = vec_nth z 1 / vec_nth (L u) 1"
  define b where
    "b = (vec_nth z 2 - a * vec_nth (L u) 2)
      / vec_nth (L v) 2"
  let ?w = "a *\<^sub>R u + b *\<^sub>R v"
  have Lw: "L ?w = a *\<^sub>R L u + b *\<^sub>R L v"
    using lin by (simp add: linear_add linear_cmul)
  have first: "vec_nth (L ?w) 1 = vec_nth z 1"
    unfolding Lw
    using first_nz second_first_zero
    by (simp add: a_def)
  have second: "vec_nth (L ?w) 2 = vec_nth z 2"
    unfolding Lw
    using second_nz
    by (simp add: b_def)
  have "L ?w = z"
    using first second
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
  then show "\<exists>w. z = L w"
    by blast
qed

theorem robust4_actual_cubic_map_derivative_surj:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "((real^2)^'n) \<times> real"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qR: "q \<in> D3ActualXiZeroNonphaseIncidence V y"
    and cubic_nz:
      "robust4_actual_arc_cubic (fst q) y (snd q) \<noteq> 0"
  shows "surj
      (blinfun_apply
        (Dblinfun
          (robust4_actual_cubic_map y ::
            (((real^2)^'n) \<times> (real^2)) \<Rightarrow> real^2)
          (fst q, vector [snd q, 0])))"
proof -
  let ?x = "fst q"
  let ?t = "snd q"
  let ?center = "vector [pi / 2, 0] :: real^2"
  let ?steer = "vector [0, 0] :: real^2"
  let ?omega = "vector [?t, y] :: real^2"
  let ?pad = "vector [?t, 0] :: real^2"
  let ?G =
    "(robust4_actual_cubic_map y ::
      (((real^2)^'n) \<times> (real^2)) \<Rightarrow> real^2)"
  let ?p = "(?x, ?pad)"
  let ?D = "blinfun_apply (Dblinfun ?G ?p)"

  have Gd: "(?G has_derivative ?D) (at ?p)"
    by (rule real_analytic_on_has_derivative_Dblinfun[
        OF real_analytic_on_robust4_actual_cubic_map])
       simp
  have linD: "linear ?D"
    by (rule bounded_linear.linear[OF blinfun.bounded_linear_right])

  obtain k :: 'n where sk:
      "d3_s2_perp_slot ?center ?steer ?omega k ?x \<noteq> 0"
    by (rule robust4_actual_Xi_zero_nonphase_s2_witness[
        OF y3 qR])
  let ?c = "cvec_dip ?center ?steer ?omega"
  let ?u = "slot k (perp2 ?c)"

  have xembed:
      "((\<lambda>z::(real^2)^'n. (z, ?pad))
        has_derivative (\<lambda>h. (h, 0))) (at ?x)"
    by (auto intro!: derivative_eq_intros)
  have xchain:
      "((\<lambda>z::(real^2)^'n. ?G (z, ?pad))
        has_derivative (\<lambda>h. ?D (h, 0))) (at ?x)"
  proof -
    note chain =
      has_derivative_compose[OF xembed Gd]
    show ?thesis
      using chain by (simp add: o_def)
  qed
  have xcomponent:
      "((\<lambda>z::(real^2)^'n. vec_nth (?G (z, ?pad)) 1)
        has_derivative
          (\<lambda>h. vec_nth (?D (h, 0)) 1)) (at ?x)"
    using bounded_linear.has_derivative[
      OF bounded_linear_vec_nth xchain] .
  have xcomponent_actual:
      "((\<lambda>z::(real^2)^'n.
          vec_nth
            (gradU (cvec_dip ?center ?steer) gain_dip z ?omega) 2)
        has_derivative
          (\<lambda>h. vec_nth (?D (h, 0)) 1)) (at ?x)"
    using xcomponent
    by (simp add: robust4_actual_cubic_map_def)
  have xcomponent_frechet:
      "((\<lambda>z::(real^2)^'n.
          vec_nth
            (gradU (cvec_dip ?center ?steer) gain_dip z ?omega) 2)
        has_derivative
          frechet_derivative
            (\<lambda>z::(real^2)^'n.
              vec_nth
                (gradU (cvec_dip ?center ?steer)
                  gain_dip z ?omega) 2)
            (at ?x)) (at ?x)"
    by (rule has_derivative_gradU_dip_component2_x_frechet)
  have xder_eq:
      "(\<lambda>h. vec_nth (?D (h, 0)) 1)
       =
       frechet_derivative
        (\<lambda>z::(real^2)^'n.
          vec_nth
            (gradU (cvec_dip ?center ?steer) gain_dip z ?omega) 2)
        (at ?x)"
    by (rule has_derivative_unique[
        OF xcomponent_actual xcomponent_frechet])
  have Du_first:
      "vec_nth (?D (?u, 0)) 1 \<noteq> 0"
  proof -
    have at_u:
        "vec_nth (?D (?u, 0)) 1 =
          frechet_derivative
            (\<lambda>z::(real^2)^'n.
              vec_nth
                (gradU (cvec_dip ?center ?steer)
                  gain_dip z ?omega) 2)
            (at ?x) ?u"
      by (rule fun_cong[OF xder_eq])
    show ?thesis
      using at_u sk
      unfolding d3_s2_perp_slot_def by simp
  qed

  have phi_eq:
      "(\<lambda>s::real. vector [s, 0] :: real^2)
       =
       (\<lambda>s. s *\<^sub>R vector [1, 0])"
    by (rule ext)
       (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
  have phid:
      "((\<lambda>s::real. vector [s, 0] :: real^2)
        has_derivative
          (\<lambda>r. r *\<^sub>R (vector [1, 0] :: real^2))) (at ?t)"
    unfolding phi_eq
    by (auto intro!: derivative_eq_intros)
  have t_embed:
      "((\<lambda>s::real. (?x, vector [s, 0] :: real^2))
        has_derivative
          (\<lambda>r. (0, r *\<^sub>R (vector [1, 0] :: real^2))))
        (at ?t)"
    by (rule has_derivative_Pair)
       (auto intro!: derivative_eq_intros phid)
  have tchain:
      "((\<lambda>s::real. ?G (?x, vector [s, 0]))
        has_derivative
          (\<lambda>r. ?D
            (0, r *\<^sub>R (vector [1, 0] :: real^2)))) (at ?t)"
  proof -
    note chain =
      has_derivative_compose[OF t_embed Gd]
    show ?thesis
      using chain by (simp add: o_def)
  qed
  have tcomponent1:
      "((\<lambda>s::real. vec_nth (?G (?x, vector [s, 0])) 1)
        has_derivative
          (\<lambda>r. vec_nth
            (?D (0, r *\<^sub>R (vector [1, 0] :: real^2))) 1))
        (at ?t)"
    using bounded_linear.has_derivative[
      OF bounded_linear_vec_nth tchain] .
  have tcomponent1_actual:
      "((\<lambda>s::real.
          vec_nth
            (gradU (cvec_dip ?center ?steer)
              gain_dip ?x (vector [s, y])) 2)
        has_derivative
          (\<lambda>r. vec_nth
            (?D (0, r *\<^sub>R (vector [1, 0] :: real^2))) 1))
        (at ?t)"
    using tcomponent1
    by (simp add: robust4_actual_cubic_map_def)
  have tcomponent1_real:
      "((\<lambda>s::real.
          vec_nth
            (gradU (cvec_dip ?center ?steer)
              gain_dip ?x (vector [s, y])) 2)
        has_real_derivative
          vec_nth (?D (0, vector [1, 0])) 1) (at ?t)"
    unfolding has_field_derivative_def
    by (metis (mono_tags, lifting) has_derivative_unique has_field_derivative_def mult_zero_left phi_eq qR
        robust4_actual_Xi_zero_incidence_gradU2_arc_derivative_zero tcomponent1_actual y3)       
  have tcomponent1_zero:
      "((\<lambda>s::real.
          vec_nth
            (gradU (cvec_dip ?center ?steer)
              gain_dip ?x (vector [s, y])) 2)
        has_real_derivative 0) (at ?t)"
    by (rule
        robust4_actual_Xi_zero_incidence_gradU2_arc_derivative_zero[
          OF y3 qR])
  have Dt_first:
      "vec_nth (?D (0, vector [1, 0])) 1 = 0"
    by (rule DERIV_unique[
        OF tcomponent1_real tcomponent1_zero])

  have tcomponent2:
      "((\<lambda>s::real. vec_nth (?G (?x, vector [s, 0])) 2)
        has_derivative
          (\<lambda>r. vec_nth
            (?D (0, r *\<^sub>R (vector [1, 0] :: real^2))) 2))
        (at ?t)"
    using bounded_linear.has_derivative[
      OF bounded_linear_vec_nth tchain] .
  have tcomponent2_actual:
      "((\<lambda>s::real.
          vec_nth
            (vec_nth
              (HessU (cvec_dip ?center ?steer)
                gain_dip ?x (vector [s, y])) 1) 1)
        has_derivative
          (\<lambda>r. vec_nth
            (?D (0, r *\<^sub>R (vector [1, 0] :: real^2))) 2))
        (at ?t)"
    using tcomponent2
    by (simp add: robust4_actual_cubic_map_def)
  have tcomponent2_real:
      "((\<lambda>s::real.
          vec_nth
            (vec_nth
              (HessU (cvec_dip ?center ?steer)
                gain_dip ?x (vector [s, y])) 1) 1)
        has_real_derivative
          vec_nth (?D (0, vector [1, 0])) 2) (at ?t)"
    unfolding has_field_derivative_def
    by (metis (no_types, lifting) frechet_derivative_at has_field_derivative_def has_real_derivative 
        more_arith_simps(6) phi_eq tcomponent2_actual)   
  have Dt_second:
      "vec_nth (?D (0, vector [1, 0])) 2 =
        robust4_actual_arc_cubic ?x y ?t"
    unfolding robust4_actual_arc_cubic_def
    using DERIV_imp_deriv[OF tcomponent2_real] by simp
  have Dt_second_nz:
      "vec_nth (?D (0, vector [1, 0])) 2 \<noteq> 0"
    using Dt_second cubic_nz by simp
  show ?thesis
    by (rule surj_linear_vec2_of_triangular_witnesses[
        OF linD Du_first Dt_first Dt_second_nz])
qed

lemma nonsurj_linear_vec2_first_zero_of_vertical_witness:
  fixes L :: "'a::real_vector \<Rightarrow> real^2"
  assumes lin: "linear L"
    and ns: "\<not> surj L"
    and vertical: "vec_nth (L v) 1 = 0"
    and vnz: "vec_nth (L v) 2 \<noteq> 0"
  shows "vec_nth (L u) 1 = 0"
proof (rule ccontr)
  assume unz: "\<not> vec_nth (L u) 1 = 0"
  have onto: "surj L"
  proof (unfold surj_def, intro allI)
    fix y :: "real^2"
    define a where "a = vec_nth y 1 / vec_nth (L u) 1"
    define b where
      "b = (vec_nth y 2 - a * vec_nth (L u) 2)
        / vec_nth (L v) 2"
    let ?z = "a *\<^sub>R u + b *\<^sub>R v"
    have Lz: "L ?z = a *\<^sub>R L u + b *\<^sub>R L v"
      using lin by (simp add: linear_add linear_cmul)
    have first: "vec_nth (L ?z) 1 = vec_nth y 1"
      unfolding Lz
      using unz vertical
      by (simp add: a_def)
    have second: "vec_nth (L ?z) 2 = vec_nth y 2"
      unfolding Lz
      using vnz
      by (simp add: b_def)
    have Lzy: "L ?z = y"
      using first second
      by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
    show "\<exists>x. y = L x"
      by (rule exI[of _ ?z]) (use Lzy in simp)
  qed
  show False
    using ns onto by contradiction
qed

theorem robust4_actual_Xi_zero_incidence_gradU_first_row_zero:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "((real^2)^'n) \<times> real"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qR: "q \<in> D3ActualXiZeroNonphaseIncidence V y"
  shows "\<And>u. vec_nth
      (frechet_derivative
        (\<lambda>z. gradU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip z (vector [snd q, y]))
        (at (fst q)) u) 1 = 0"
proof -
  let ?om = "vector [snd q, y] :: real^2"
  let ?center = "vector [pi / 2, 0] :: real^2"
  let ?steer = "vector [0, 0] :: real^2"
  let ?F =
    "\<lambda>z. gradU (cvec_dip ?center ?steer) gain_dip z ?om"
  let ?D = "frechet_derivative ?F (at (fst q))"
  have qM:
      "q \<in> D3ActualArcIncidence V ?center ?steer
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
    using qR unfolding D3ActualXiZeroNonphaseIncidence_def by simp
  have tI: "snd q \<in> {pi / 4<..<3 * pi / 4}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have wA: "?om \<in> robust4_horizontal_arc y"
    using tI unfolding robust4_horizontal_arc_def by auto
  have xbad: "fst q \<in> D3BadXG ?center ?steer {?om}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have detnz:
      "det (matrix (Dcvec_dip ?center ?steer ?om)) \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have cnz: "cvec_dip ?center ?steer ?om \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have diff0: "?F differentiable (at (fst q) within UNIV)"
    by (rule gradU_dip_differentiable_x)
  have diff: "?F differentiable (at (fst q))"
    using diff0 by simp
  obtain D0 where D0: "(?F has_derivative D0) (at (fst q))"
    using diff unfolding differentiable_def by blast
  have hd: "(?F has_derivative ?D) (at (fst q))"
    using D0 frechet_derivative_at[OF D0] by simp
  have lin: "linear ?D"
    using has_derivative_bounded_linear[OF hd]
    by (rule bounded_linear.linear)
  have ns: "\<not> surj ?D"
  proof
    assume "surj ?D"
    with hd have "\<exists>Dx. (?F has_derivative Dx) (at (fst q))
        \<and> surj Dx"
      by blast
    then show False
      using xbad unfolding D3BadXG_def by blast
  qed
  obtain k :: 'n where sk:
      "d3_s2_perp_slot ?center ?steer ?om k (fst q) \<noteq> 0"
    by (rule robust4_actual_Xi_zero_nonphase_s2_witness[
        OF y3 qR])
  let ?v = "slot k (perp2 (cvec_dip ?center ?steer ?om))"
  have first: "vec_nth (?D ?v) 1 = 0"
  proof -
    have s1z:
        "d3_s1_global_factor ?center ?steer ?om = 0"
      by (rule robust4_horizontal_arc_actual_s1_factor_zero[OF wA y3])
    have slot1:
        "d3_s1_perp_slot ?center ?steer ?om k (fst q) = 0"
      unfolding d3_s1_perp_slot_value
      using s1z by simp
    show ?thesis
      unfolding gradU_dip_frechet_derivative_component
        d3_s1_perp_slot_def[symmetric]
      by (rule slot1)
  qed
  have second: "vec_nth (?D ?v) 2 \<noteq> 0"
    unfolding gradU_dip_frechet_derivative_component
    using sk unfolding d3_s2_perp_slot_def by simp
  show "vec_nth (?D u) 1 = 0" for u
    by (rule nonsurj_linear_vec2_first_zero_of_vertical_witness[
        OF lin ns first second])
qed

theorem robust4_actual_Xi_zero_incidence_Phi_par_x_derivative_zero:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "((real^2)^'n) \<times> real"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qR: "q \<in> D3ActualXiZeroNonphaseIncidence V y"
  shows "\<And>u. frechet_derivative
      (\<lambda>z. Phi_par z (vector [snd q, y])
        (vector [pi / 2, 0]) (vector [0, 0]))
      (at (fst q)) u = 0"
proof -
  let ?om = "vector [snd q, y] :: real^2"
  let ?center = "vector [pi / 2, 0] :: real^2"
  let ?steer = "vector [0, 0] :: real^2"
  let ?F =
    "\<lambda>z. gradU (cvec_dip ?center ?steer) gain_dip z ?om"
  let ?D = "frechet_derivative ?F (at (fst q))"
  let ?e = "e_par ?center ?steer ?om"
  have qM:
      "q \<in> D3ActualArcIncidence V ?center ?steer
        (\<lambda>t. vector [t, y]) {pi / 4<..<3 * pi / 4}"
    using qR unfolding D3ActualXiZeroNonphaseIncidence_def by simp
  have tI: "snd q \<in> {pi / 4<..<3 * pi / 4}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have wA: "?om \<in> robust4_horizontal_arc y"
    using tI unfolding robust4_horizontal_arc_def by auto
  have xbad: "fst q \<in> D3BadXG ?center ?steer {?om}"
    using qM unfolding D3ActualArcIncidence_def by simp
  have detnz:
      "det (matrix (Dcvec_dip ?center ?steer ?om)) \<noteq> 0"
    using xbad unfolding D3BadXG_def by blast
  have e2: "vec_nth ?e 2 = 0"
    by (rule robust4_horizontal_arc_actual_e_par_second_zero[
        OF wA y3 detnz])
  have row1: "vec_nth (?D u) 1 = 0" for u
    by (rule
        robust4_actual_Xi_zero_incidence_gradU_first_row_zero[
          OF y3 qR])
  have diff0: "?F differentiable (at (fst q) within UNIV)"
    by (rule gradU_dip_differentiable_x)
  have diff: "?F differentiable (at (fst q))"
    using diff0 by simp
  obtain D0 where D0: "(?F has_derivative D0) (at (fst q))"
    using diff unfolding differentiable_def by blast
  have hd: "(?F has_derivative ?D) (at (fst q))"
    using D0 frechet_derivative_at[OF D0] by simp
  have outer:
      "((\<lambda>r::real^2. r \<bullet> ?e)
        has_derivative (\<lambda>h. h \<bullet> ?e)) (at (?F (fst q)))"
    by (rule bounded_linear.has_derivative[
        OF bounded_linear_inner_left has_derivative_ident])
  have comp:
      "((\<lambda>z. ?F z \<bullet> ?e)
        has_derivative (\<lambda>h. ?D h \<bullet> ?e)) (at (fst q))"
    using diff_chain_at[OF hd outer] by (simp add: o_def)
  have phi_hd:
      "((\<lambda>z. Phi_par z ?om ?center ?steer)
        has_derivative (\<lambda>h. ?D h \<bullet> ?e)) (at (fst q))"
    using comp unfolding Phi_par_def .
  have deriv_value: "\<And>u. frechet_derivative
        (\<lambda>z. Phi_par z ?om ?center ?steer)
        (at (fst q)) u = ?D u \<bullet> ?e"
    by (rule sym,
        rule fun_cong[OF frechet_derivative_at[OF phi_hd]])
  show "frechet_derivative
      (\<lambda>z. Phi_par z ?om ?center ?steer)
      (at (fst q)) u = 0" for u
    unfolding deriv_value
    using row1[of u] e2
    by (simp add: inner_vec_def sum_2)
qed

corollary robust4_actual_Xi_zero_incidence_Lambda_zero:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "((real^2)^'n) \<times> real"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qR: "q \<in> D3ActualXiZeroNonphaseIncidence V y"
  shows "Lambda_ij (fst q) (vector [snd q, y])
      (vector [pi / 2, 0]) (vector [0, 0]) i j = 0"
  unfolding Lambda_ij_def
  using
    robust4_actual_Xi_zero_incidence_Phi_par_x_derivative_zero[
      OF y3 qR, of
        "slot i
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [snd q, y]))"]
    robust4_actual_Xi_zero_incidence_Phi_par_x_derivative_zero[
      OF y3 qR, of
        "slot j
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [snd q, y]))"]
  by simp

corollary robust4_actual_Xi_zero_incidence_Jac3_H12zero_zero:
  fixes V :: "((real^2)^'n::finite) set"
    and q :: "((real^2)^'n) \<times> real"
  assumes y3: "y \<in> {-pi, 0, pi}"
    and qR: "q \<in> D3ActualXiZeroNonphaseIncidence V y"
  shows "Jac3_H12zero (fst q) (vector [snd q, y])
      (vector [pi / 2, 0]) (vector [0, 0]) i j k = 0"
  unfolding Jac3_H12zero_def det3_def
  using
    robust4_actual_Xi_zero_incidence_Phi_par_x_derivative_zero[
      OF y3 qR, of
        "slot i
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [snd q, y]))"]
    robust4_actual_Xi_zero_incidence_Phi_par_x_derivative_zero[
      OF y3 qR, of
        "slot j
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [snd q, y]))"]
    robust4_actual_Xi_zero_incidence_Phi_par_x_derivative_zero[
      OF y3 qR, of
        "slot k
          (perp2
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
              (vector [snd q, y])))"]
  by simp

section \<open>The residual Hessian term is radial on the actual arcs\<close>

lemma Wc_d1_parallel_dir_slot_perp_zero:
  fixes c d :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  assumes dpar: "d = r *\<^sub>R c"
  shows "frechet_derivative (\<lambda>y. Wc_d1 y c d) (at x)
      (slot m (perp2 c)) = 0"
proof -
  define G where "G = (\<lambda>u::real. - (r * u * sin u))"
  have eqf: "(\<lambda>y. Wc_d1 y c d) =
      (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        G (c \<bullet> (vec_nth y n - vec_nth y p)))"
    unfolding G_def
    by (rule ext)
       (simp add: Wc_d1_def dpar sum_negf sum_subtractf sum_distrib_left
          algebra_simps)
  have dG: "(G has_field_derivative
      (- (r * (sin u + u * cos u)))) (at u)" for u :: real
    unfolding G_def
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  show ?thesis
    unfolding eqf
    by (rule pair_phase_sum_perp_slot_zero[OF dG])
qed

theorem robust4_horizontal_arc_actual_H_par_slot_perp_zero:
  fixes x :: "(real^2)^'n::finite" and m :: 'n
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
  shows "frechet_derivative
      (\<lambda>z. H_par z \<omega>
        (vector [pi / 2, 0]) (vector [0, 0])) (at x)
      (slot m
        (perp2
          (cvec_dip
            (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))) = 0"
proof -
  let ?w0 = "vector [pi / 2, 0] :: real^2"
  let ?ws = "vector [0, 0] :: real^2"
  let ?c = "cvec_dip ?w0 ?ws \<omega>"
  let ?e = "e_par ?w0 ?ws \<omega>"
  let ?d = "D2cvec_dip ?w0 ?ws \<omega> ?e ?e"
  obtain r where dpar: "?d = r *\<^sub>R ?c"
    by (rule robust4_horizontal_arc_actual_D2c_e_par_parallel[
        OF wA y3 detnz cnz])
  define A where
    "A = deriv gdip (vec_nth \<omega> 1) * vec_nth ?e 1"
  define B where
    "B = deriv (deriv gdip) (vec_nth \<omega> 1)
      * vec_nth ?e 1 * vec_nth ?e 1"
  define G where
    "G = (\<lambda>u::real.
      A * (- (u * sin u))
      + B * cos u
      + gain_dip \<omega>
          * (r * (- (u * sin u)) + (- (u\<^sup>2 * cos u)))
      + A * (- (u * sin u)))"
  have eqf:
      "(\<lambda>z. H_par z \<omega> ?w0 ?ws) =
        (\<lambda>z. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          G (?c \<bullet> (vec_nth z n - vec_nth z p)))"
    unfolding G_def
    by (rule ext)
       (simp add: H_par_radial_dictionary[OF detnz]
          A_def B_def dpar Wc_def Wc_d1_def Wc_d2_def
          sum.distrib sum_negf sum_subtractf sum_distrib_left
          power2_eq_square algebra_simps)
  have dG: "(G has_field_derivative
      (A * (- (sin u + u * cos u))
       + B * (- sin u)
       + gain_dip \<omega>
          * (r * (- (sin u + u * cos u))
             + (- (2 * u * cos u - u\<^sup>2 * sin u)))
       + A * (- (sin u + u * cos u)))) (at u)" for u :: real
    unfolding G_def
    by (auto intro!: derivative_eq_intros
        simp: power2_eq_square algebra_simps)
  show ?thesis
    unfolding eqf
    by (rule pair_phase_sum_perp_slot_zero[OF dG])
qed

corollary robust4_horizontal_arc_actual_Jac3_H12zero_nonzero:
  fixes x :: "(real^2)^'n::finite" and i j k :: 'n
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
    and s_k_nz:
      "frechet_derivative
        (\<lambda>z. vec_nth
          (gradU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip z \<omega>) 2) (at x)
        (slot k
          (perp2
            (cvec_dip
              (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))) \<noteq> 0"
    and lambda_nz:
      "Lambda_ij x \<omega>
        (vector [pi / 2, 0]) (vector [0, 0]) i j \<noteq> 0"
  shows "Jac3_H12zero x \<omega>
      (vector [pi / 2, 0]) (vector [0, 0]) i j k \<noteq> 0"
proof (rule Jac3_H12zero_nonzero_criterion[
    OF detnz _ s_k_nz lambda_nz])
  show "frechet_derivative
      (\<lambda>z. H_par z \<omega>
        (vector [pi / 2, 0]) (vector [0, 0])) (at x)
      (slot k
        (perp2
          (cvec_dip
            (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))) = 0"
    by (rule robust4_horizontal_arc_actual_H_par_slot_perp_zero[
        OF wA y3 detnz cnz])
qed

section \<open>The moment-rank conjunct in the actual D3 set is redundant\<close>

lemma robust4_nonsurj_DM_of_nonsurj_gradU_x:
  fixes x :: "(real^2)^'n::finite"
  assumes anz:
      "A_cart
        (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega> \<noteq> 0"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and nsurjG: "\<not> (\<exists>Dx.
      ((\<lambda>z. gradU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip z \<omega>) has_derivative Dx) (at x)
      \<and> surj Dx)"
  shows "\<not> surj
      (DM_paper_x x
        (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))"
proof
  assume msurj:
      "surj
        (DM_paper_x x
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))"
  have "\<exists>Dx.
      ((\<lambda>z. gradU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip z \<omega>) has_derivative Dx) (at x)
      \<and> surj Dx"
    by (rule gradU_dip_x_partial_surj[OF anz msurj detnz])
  with nsurjG show False by contradiction
qed

definition robust4_D3BadXG_reduced ::
    "(real^2) set \<Rightarrow> ((real^2)^'n::finite) set"
  where
  "robust4_D3BadXG_reduced \<Gamma> =
    {x. \<exists>\<omega>\<in>\<Gamma>.
        gradU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega> = 0
      \<and> det (HessU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega>) = 0
      \<and> A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega> \<noteq> 0
      \<and> det (matrix
          (Dcvec_dip
            (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0
      \<and> cvec_dip
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0
      \<and> \<not> (\<exists>Dx.
          ((\<lambda>z. gradU
              (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip z \<omega>) has_derivative Dx) (at x)
          \<and> surj Dx)}"

theorem robust4_D3BadXG_eq_reduced:
  "(D3BadXG
      (vector [pi / 2, 0]) (vector [0, 0]) \<Gamma>
      :: ((real^2)^'n::finite) set)
    = robust4_D3BadXG_reduced \<Gamma>"
proof
  show "(D3BadXG
      (vector [pi / 2, 0]) (vector [0, 0]) \<Gamma>
      :: ((real^2)^'n) set)
      \<subseteq> robust4_D3BadXG_reduced \<Gamma>"
    unfolding D3BadXG_def robust4_D3BadXG_reduced_def by blast
next
  show "robust4_D3BadXG_reduced \<Gamma>
      \<subseteq> (D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0]) \<Gamma>
        :: ((real^2)^'n) set)"
  proof
    fix x
    assume xr: "x \<in> robust4_D3BadXG_reduced \<Gamma>"
    then obtain \<omega> where wG: "\<omega> \<in> \<Gamma>"
      and gz:
        "gradU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega> = 0"
      and h0:
        "det (HessU
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
          gain_dip x \<omega>) = 0"
      and anz:
        "A_cart
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])) x \<omega> \<noteq> 0"
      and detnz:
        "det (matrix
          (Dcvec_dip
            (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
      and cnz:
        "cvec_dip
          (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
      and nsurjG: "\<not> (\<exists>Dx.
        ((\<lambda>z. gradU
            (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
            gain_dip z \<omega>) has_derivative Dx) (at x)
        \<and> surj Dx)"
      unfolding robust4_D3BadXG_reduced_def by blast
    have nsurjM:
        "\<not> surj
          (DM_paper_x x
            (cvec_dip
              (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))"
      by (rule robust4_nonsurj_DM_of_nonsurj_gradU_x[
          OF anz detnz nsurjG])
    show "x \<in> D3BadXG
        (vector [pi / 2, 0]) (vector [0, 0]) \<Gamma>"
      unfolding D3BadXG_def
      using wG gz h0 anz detnz cnz nsurjM nsurjG by blast
  qed
qed

end
