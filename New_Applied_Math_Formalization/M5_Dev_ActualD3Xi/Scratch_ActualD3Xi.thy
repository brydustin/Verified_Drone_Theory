theory Scratch_ActualD3Xi
  imports
    "Applied_Math_M5_ActualD3.Scratch_ActualD3"
    "Applied_Math_M5_D3Generic.Scratch_D3Generic"
begin

section \<open>The Hessian witness on the actual outer collinear arcs\<close>

text \<open>
  The exact collinear-locus calculation in @{thm
  robust4_phase_collinear_locus_exact} leaves three horizontal arcs.  The
  tangent of each is \<open>(1,0)\<close>.  On the two outer arcs
  \<open>\<omega>\<^sub>2 = \<plusminus>\<pi>\<close>, the first component of
  \<open>e_par\<close> is nonzero whenever the two nondegeneracy conditions already
  retained by the actual D3 set hold.

  This is where the determinant formula in @{thm e_par_closed_form} becomes
  load-bearing: its denominator contains \<open>det (matrix Dcvec_dip)\<close>, and its
  first numerator is \<open>d3_s2_global_factor\<close>.  The following calculation
  proves that numerator nonzero on the actual outer arcs.
\<close>

lemma robust4_horizontal_arc_first_strip:
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and y3: "y \<in> {-pi, 0, pi}"
  shows "0 < vec_nth \<omega> 1" and "vec_nth \<omega> 1 < pi"
proof -
  have sub: "robust4_horizontal_arc y
      \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    by (rule robust4_horizontal_arc_subset_OmegaPF[OF y3])
  have wO: "\<omega> \<in> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    using sub wA by blast
  show "0 < vec_nth \<omega> 1"
    by (rule H0coreArc_robust4_OmegaPF_w1_strip(1)[OF wO])
  show "vec_nth \<omega> 1 < pi"
    by (rule H0coreArc_robust4_OmegaPF_w1_strip(2)[OF wO])
qed

lemma robust4_outer_arc_d3_s2_global_factor_nonzero:
  fixes \<omega> :: "real^2" and y :: real
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and outer: "y \<in> {-pi, pi}"
  shows "d3_s2_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
proof -
  have phi: "vec_nth \<omega> 2 = y"
    using robust4_horizontal_arc_components[OF wA] by blast+
  have y3: "y \<in> {-pi, 0, pi}" using outer by auto
  have lo: "0 < vec_nth \<omega> 1" and hi: "vec_nth \<omega> 1 < pi"
    by (rule robust4_horizontal_arc_first_strip[OF wA y3])+
  have sinpos: "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero[OF lo hi])
  have gnz: "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_sin) (use sinpos in force)
  have cosy: "cos (vec_nth \<omega> 2) = -1"
    using outer phi by auto
  have trig_collapse:
      "sin (vec_nth \<omega> 1)
          * (sin (vec_nth \<omega> 1)
              * (cos (vec_nth \<omega> 2) * cos (vec_nth \<omega> 2)))
       + sin (vec_nth \<omega> 1)
          * (sin (vec_nth \<omega> 1)
              * (sin (vec_nth \<omega> 2) * sin (vec_nth \<omega> 2)))
       = sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1)"
  proof -
    have "sin (vec_nth \<omega> 1)
            * (sin (vec_nth \<omega> 1)
                * (cos (vec_nth \<omega> 2) * cos (vec_nth \<omega> 2)))
         + sin (vec_nth \<omega> 1)
            * (sin (vec_nth \<omega> 1)
                * (sin (vec_nth \<omega> 2) * sin (vec_nth \<omega> 2)))
       = (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1))
           * (cos (vec_nth \<omega> 2) * cos (vec_nth \<omega> 2)
               + sin (vec_nth \<omega> 2) * sin (vec_nth \<omega> 2))"
      by (simp only: mult.assoc distrib_left)
    also have "\<dots> = sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1)"
      by (simp only: sin_cos_squared_add3)
    finally show ?thesis .
  qed
  have dot_eq:
      "Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> (axis 2 1)
          \<bullet> perp2 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
       = sin (vec_nth \<omega> 1)
          * (sin (vec_nth \<omega> 1)
              + cos (vec_nth \<omega> 2) * (cos (vec_nth \<omega> 1) - 1))"
    using trig_collapse
    by (simp add: Dcvec_dip_def cvec_dip_def perp2_def kx_def ky_def kz_def
        axis_def inner_vec_def sum_2 vector_2 sin_pi_half cos_pi_half
        algebra_simps)
  have bracket_pos:
      "0 < sin (vec_nth \<omega> 1) + 1 - cos (vec_nth \<omega> 1)"
    using sinpos cos_le_one[of "vec_nth \<omega> 1"] by linarith
  have dot_nz:
      "Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> (axis 2 1)
          \<bullet> perp2 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
       \<noteq> 0"
    using dot_eq cosy sinpos bracket_pos by simp
  show ?thesis
    unfolding d3_s2_global_factor_def
    using gnz dot_nz by simp
qed

lemma robust4_outer_arc_e_par_first_nonzero:
  fixes \<omega> :: "real^2" and y :: real
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and outer: "y \<in> {-pi, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
  shows "vec_nth
      (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 1 \<noteq> 0"
proof -
  have y3: "y \<in> {-pi, 0, pi}" using outer by auto
  have lo: "0 < vec_nth \<omega> 1" and hi: "vec_nth \<omega> 1 < pi"
    by (rule robust4_horizontal_arc_first_strip[OF wA y3])+
  have sinpos: "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero[OF lo hi])
  have gnz: "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_sin) (use sinpos in force)
  have facnz:
      "d3_s2_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
    by (rule robust4_outer_arc_d3_s2_global_factor_nonzero[OF wA outer])
  have form:
      "e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega> =
        vector [
          d3_s2_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
            / (2 * gain_dip \<omega>
                * det (matrix
                    (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>))),
          - d3_s1_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega>
            / (2 * gain_dip \<omega>
                * det (matrix
                    (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)))]"
    by (rule e_par_closed_form[OF detnz gnz])
  show ?thesis
    unfolding form
    using facnz detnz gnz by (simp add: vector_2)
qed

text \<open>
  We can now instantiate the analytic Hessian witness theorem with the literal
  dipole function, literal Robust4 design, and literal horizontal tangent.
  Thus, at every retained nondegenerate angle on either outer arc, the
  configurations where that tangent lies in the Hessian kernel form a
  nowhere-dense analytic zero set.

  This is a fixed-angle theorem.  It does not assert that the projection over
  an uncountable interval of angles is countable; that missing quantifier
  exchange is precisely the remaining D3 bridge.
\<close>

theorem robust4_outer_arc_Xi_horizontal_zeros_nowhere_dense:
  fixes \<omega> :: "real^2" and y :: real
  assumes card2: "2 \<le> CARD('n::finite)"
    and wA: "\<omega> \<in> robust4_horizontal_arc y"
    and outer: "y \<in> {-pi, pi}"
    and detnz:
      "det (matrix
        (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    and cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
  shows "interior
      (closure {x::(real^2)^'n.
        Xi x (vector [pi / 2, 0]) (vector [0, 0]) \<omega> (vector [1, 0]) = 0})
      = {}"
proof (rule Xi_zeros_nowhere_dense)
  show "2 \<le> CARD('n)" by (rule card2)
  show "det (matrix
      (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)) \<noteq> 0"
    by (rule detnz)
  show "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
    by (rule cnz)
  show "vec_nth (e_par (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 1 \<noteq> 0"
    by (rule robust4_outer_arc_e_par_first_nonzero[OF wA outer detnz])
  have y3: "y \<in> {-pi, 0, pi}" using outer by auto
  have lo: "0 < vec_nth \<omega> 1" and hi: "vec_nth \<omega> 1 < pi"
    by (rule robust4_horizontal_arc_first_strip[OF wA y3])+
  have sinpos: "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero[OF lo hi])
  show "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_sin) (use sinpos in force)
  show "vec_nth (vector [1, 0] :: real^2) 1 \<noteq> 0"
    by (simp add: vector_2)
qed

end
