theory Scratch_momentsard
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>Second-derivative layer toward \<open>has_derivative_mstarg_joint_C1\<close>.\<close>
  \<open>mstarg\<close>'s x-dependence runs through the moment Jacobian \<open>DM_paper_x x c\<close>, whose
  components \<open>d_*_moment_x\<close> are built from \<open>d_phase\<close>.  Differentiating \<open>mstarg\<close> in x
  therefore needs the x-derivative of \<open>d_phase\<close> --- the SECOND derivative of the phase
  factor, the building block the heap stops short of (it only proves the first
  derivative, \<open>has_derivative_phase_x\<close>).  Since
  \<open>d_phase c y h n = -(c \<bullet> (h$n)) *\<^sub>R (\<i> * cis (-(c \<bullet> (y$n))))\<close> is a constant scaleR of
  \<open>\<i>\<close> times \<open>cis(-(c\<bullet>(y$n)))\<close>, its x-derivative follows from the proven
  \<open>has_derivative_cis_neg_inner_x\<close> (Moment_Map) plus the scaleR/mult rules.\<close>

lemma has_derivative_d_phase_x:
  fixes c :: planar and x :: "planar^'n" and h :: "planar^'n"
    and n :: 'n and V :: "(planar^'n) set"
  shows "((\<lambda>y::planar^'n. d_phase c y h n) has_derivative
            (\<lambda>k. (of_real (-(c \<bullet> (h $ n))) * \<i>) *
                   ((-(c \<bullet> (k $ n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n)))))))
         (at x within V)"
proof -
  have inner: "((\<lambda>y::planar^'n. cis (-(c \<bullet> (y $ n)))) has_derivative
                  (\<lambda>k. (-(c \<bullet> (k $ n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n)))))) (at x within V)"
    by (rule has_derivative_cis_neg_inner_x)
  \<comment> \<open>Collapse the scaleR-of-mult to a single complex-constant multiple of \<open>cis\<close>,
      so the const-mult + \<open>simp\<close> closes exactly as in \<open>has_derivative_det_fun\<close>.\<close>
  have rw: "(\<lambda>y::planar^'n. d_phase c y h n)
              = (\<lambda>y. (of_real (-(c \<bullet> (h $ n))) * \<i>) * cis (-(c \<bullet> (y $ n))))"
    unfolding d_phase_def by (simp add: scaleR_conv_of_real mult.assoc)
  have base: "((\<lambda>y::planar^'n. (of_real (-(c \<bullet> (h $ n))) * \<i>) * cis (-(c \<bullet> (y $ n))))
                 has_derivative
                 (\<lambda>k. (of_real (-(c \<bullet> (h $ n))) * \<i>)
                        * ((-(c \<bullet> (k $ n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n)))))
                      + 0 * cis (-(c \<bullet> (x $ n))))) (at x within V)"
    by (rule has_derivative_mult[OF has_derivative_const inner])
  show ?thesis
    unfolding rw using base by simp
qed

text \<open>\<^bold>\<open>Moment-component second derivatives.\<close>  Each \<open>d_*_moment_x\<close> is a finite sum
  (over \<open>n\<close>) of \<open>d_phase\<close>-terms times polynomial weights, so its x-derivative assembles
  from \<open>has_derivative_d_phase_x\<close> (the phase 2nd derivative), \<open>has_derivative_phase_x\<close>
  (the 1st), and the component-derivative lemmas.  The A-moment is the clean prototype:
  \<open>d_A_moment_x = \<Sum>\<^sub>n d_phase\<close>, so its x-derivative is the sum of the phase 2nd derivatives.\<close>

lemma has_derivative_d_A_moment_x:
  fixes c :: planar and x h :: "planar^'n" and V :: "(planar^'n) set"
  shows "((\<lambda>y::planar^'n. d_A_moment_x y c h) has_derivative
            (\<lambda>k. \<Sum>n\<in>UNIV. (of_real (-(c \<bullet> (h $ n))) * \<i>) *
                            ((-(c \<bullet> (k $ n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n)))))))
         (at x within V)"
  unfolding d_A_moment_x_def
  by (rule has_derivative_sum) (rule has_derivative_d_phase_x)

text \<open>The weighted moments carry a polynomial weight in x, so their second x-derivatives
  are proven as differentiability (existence) via differentiableI + derivative_intros over
  the bricks: the phase 1st (has_derivative_phase_x) and 2nd (has_derivative_d_phase_x)
  derivatives, plus the component-projection derivative.  This gives the milestone
  "DM_paper_x differentiable in x"; explicit continuous forms for the C1 assembly come
  later.  M1, M2 (linear weight p1, p2):\<close>

lemma differentiable_d_M1_moment_x:
  fixes c :: planar and x h :: "planar^'n" and V :: "(planar^'n) set"
  shows "(\<lambda>y::planar^'n. d_M1_moment_x y c h) differentiable (at x within V)"
  unfolding d_M1_moment_x_def
  by (rule differentiableI, rule has_derivative_sum, rule has_derivative_add,
      rule has_derivative_mult[OF has_derivative_const has_derivative_phase_x],
      rule has_derivative_mult[OF has_derivative_of_real_lift[OF has_derivative_nth_k_x]
                                  has_derivative_d_phase_x])

lemma differentiable_d_M2_moment_x:
  fixes c :: planar and x h :: "planar^'n" and V :: "(planar^'n) set"
  shows "(\<lambda>y::planar^'n. d_M2_moment_x y c h) differentiable (at x within V)"
  unfolding d_M2_moment_x_def
  by (rule differentiableI, rule has_derivative_sum, rule has_derivative_add,
      rule has_derivative_mult[OF has_derivative_const has_derivative_phase_x],
      rule has_derivative_mult[OF has_derivative_of_real_lift[OF has_derivative_nth_k_x]
                                  has_derivative_d_phase_x])

end
