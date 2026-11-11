theory Scratch_D3Xi
  imports "Applied_Math_M5_D3Hess.Scratch_D3Hess"
begin

text \<open>
  Leaf scratch for the next checkable Xi-witness step after Sketch.md
  section 6n: construct the single-bump point that solves the two first
  criticality equations C1/C2.  This avoids editing the active
  D3Hess scratch leaf directly.
\<close>

definition single_bump_W :: "real \<Rightarrow> real \<Rightarrow> real" where
  "single_bump_W n1 \<phi> = n1\<^sup>2 + 1 + 2 * n1 * cos \<phi>"

definition single_bump_C1_rhs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "single_bump_C1_rhs n1 g gp e1 \<phi> =
     gp * e1 * single_bump_W n1 \<phi> / (2 * n1 * g)"

definition single_bump_C2_target :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "single_bump_C2_target n1 g gp pe1 \<phi> =
     gp * pe1 * single_bump_W n1 \<phi> / (2 * n1 * g * sin \<phi>)"

definition single_bump_phase_point :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2" where
  "single_bump_phase_point c d \<phi> y =
     (\<phi> / (c \<bullet> c)) *\<^sub>R c
       + ((y - \<phi> * (d \<bullet> c) / (c \<bullet> c)) / (d \<bullet> perp2 c)) *\<^sub>R perp2 c"

definition S_dip :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "S_dip \<omega>0 \<omega>s \<omega> w =
     (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
        / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
     + Q_dip \<omega>0 \<omega>s \<omega>
        * (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w
            \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))"

lemma single_bump_phase_point_phase:
  fixes c d :: "real^2"
  assumes cnz: "c \<noteq> 0"
    and dpnz: "d \<bullet> perp2 c \<noteq> 0"
  shows "c \<bullet> single_bump_phase_point c d \<phi> y = \<phi>"
proof -
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz inner_self_eq_zero_iff_vec2 by blast
  have cperp: "c \<bullet> perp2 c = 0"
    by (rule perp2_orth)
  show ?thesis
    unfolding single_bump_phase_point_def
    using ccnz cperp by (simp add: inner_add_right)
qed

lemma single_bump_phase_point_target:
  fixes c d :: "real^2"
  assumes cnz: "c \<noteq> 0"
    and dpnz: "d \<bullet> perp2 c \<noteq> 0"
  shows "d \<bullet> single_bump_phase_point c d \<phi> y = y"
proof -
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz inner_self_eq_zero_iff_vec2 by blast
  show ?thesis
    unfolding single_bump_phase_point_def
    using ccnz dpnz by (simp add: inner_add_right field_simps)
qed

lemma single_bump_phase_point_probe:
  fixes a c d :: "real^2"
  assumes cnz: "c \<noteq> 0"
    and dpnz: "d \<bullet> perp2 c \<noteq> 0"
  shows "a \<bullet> single_bump_phase_point c d \<phi> y
      = \<phi> * (a \<bullet> c) / (c \<bullet> c)
        + (y - \<phi> * (d \<bullet> c) / (c \<bullet> c)) * (a \<bullet> perp2 c) / (d \<bullet> perp2 c)"
proof -
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz inner_self_eq_zero_iff_vec2 by blast
  show ?thesis
    unfolding single_bump_phase_point_def
    using ccnz dpnz by (simp add: inner_add_right field_simps)
qed

lemma single_bump_phase_point_probe_projection:
  fixes a c d :: "real^2"
  assumes cnz: "c \<noteq> 0"
    and dpnz: "d \<bullet> perp2 c \<noteq> 0"
    and yphi: "y = \<phi> * pe1 / e1"
    and Qeq: "Q = (pe1 / e1 - (d \<bullet> c) / (c \<bullet> c)) / (d \<bullet> perp2 c)"
  shows "a \<bullet> single_bump_phase_point c d \<phi> y
      = \<phi> * ((a \<bullet> c) / (c \<bullet> c) + Q * (a \<bullet> perp2 c))"
proof -
  have "a \<bullet> single_bump_phase_point c d \<phi> y
      = \<phi> * (a \<bullet> c) / (c \<bullet> c)
        + (y - \<phi> * (d \<bullet> c) / (c \<bullet> c)) * (a \<bullet> perp2 c) / (d \<bullet> perp2 c)"
    by (rule single_bump_phase_point_probe[OF cnz dpnz])
  also have "\<dots> = \<phi> * ((a \<bullet> c) / (c \<bullet> c) + Q * (a \<bullet> perp2 c))"
    unfolding yphi Qeq by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma single_bump_C1_rhs_zero:
  assumes n1nz: "n1 \<noteq> 0"
    and gnz: "g \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs n1 g gp e1 \<phi>"
  shows "- (2 * n1 * g * \<phi> * sin \<phi>) + gp * e1 * single_bump_W n1 \<phi> = 0"
proof -
  have "- (2 * n1 * g * \<phi> * sin \<phi>) + gp * e1 * single_bump_W n1 \<phi>
      = - (2 * n1 * g * single_bump_C1_rhs n1 g gp e1 \<phi>)
        + gp * e1 * single_bump_W n1 \<phi>"
    using root by simp
  also have "\<dots> = 0"
    unfolding single_bump_C1_rhs_def using n1nz gnz by (simp add: field_simps)
  finally show ?thesis .
qed

lemma single_bump_C2_target_zero:
  assumes n1nz: "n1 \<noteq> 0"
    and gnz: "g \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
  shows "- (2 * n1 * g * single_bump_C2_target n1 g gp pe1 \<phi> * sin \<phi>)
      + gp * pe1 * single_bump_W n1 \<phi> = 0"
  unfolding single_bump_C2_target_def
  using n1nz gnz sinnz by (simp add: field_simps)

lemma single_bump_C2_target_eq_phi_pe1_over_e1:
  assumes n1nz: "n1 \<noteq> 0"
    and gnz: "g \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and e1nz: "e1 \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs n1 g gp e1 \<phi>"
  shows "single_bump_C2_target n1 g gp pe1 \<phi> = \<phi> * pe1 / e1"
proof -
  have eq: "gp * e1 * single_bump_W n1 \<phi> = 2 * n1 * g * \<phi> * sin \<phi>"
    using root n1nz gnz unfolding single_bump_C1_rhs_def
    by (simp add: field_simps)
  have "gp * single_bump_W n1 \<phi> = 2 * n1 * g * \<phi> * sin \<phi> / e1"
    using eq e1nz by (simp add: field_simps)
  thus ?thesis
    unfolding single_bump_C2_target_def
    using n1nz gnz sinnz e1nz by (simp add: field_simps)
qed

lemma dot_e_perp2_zero_imp_zero:
  fixes v e :: "real^2"
  assumes enz: "e \<noteq> 0"
    and ve: "v \<bullet> e = 0"
    and vp: "v \<bullet> perp2 e = 0"
  shows "v = 0"
  using orthogonal_decomp_perp2[OF enz, of v] ve vp by simp

theorem single_bump_gradU_zero_of_phase_root_and_C2_target:
  fixes i :: "'n::finite"
    and \<omega>0 \<omega>s \<omega> :: "real^2"
    and \<phi> :: real
  defines "c \<equiv> cvec_dip \<omega>0 \<omega>s \<omega>"
    and "e \<equiv> e_par \<omega>0 \<omega>s \<omega>"
    and "d \<equiv> Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))"
    and "n1 \<equiv> real (CARD('n)) - 1"
    and "g \<equiv> gain_dip \<omega>"
    and "gp \<equiv> deriv gdip (vec_nth \<omega> 1)"
    and "e1 \<equiv> vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
    and "pe1 \<equiv> vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1"
    and "y \<equiv> single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>"
    and "p \<equiv> single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
      (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
      (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
        (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>)"
  assumes card2: "2 \<le> CARD('n)"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs n1 g gp e1 \<phi>"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> = 0"
proof -
  have n1nz: "n1 \<noteq> 0"
  proof -
    have "2 \<le> real CARD('n)"
      using card2 by simp
    then have "0 < n1"
      unfolding n1_def by linarith
    then show ?thesis by simp
  qed
  have gnz': "g \<noteq> 0"
    using gnz unfolding g_def .
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have ce: "Dcvec_dip \<omega>0 \<omega>s \<omega> e = c"
    unfolding e_def c_def by (rule Dcvec_dip_e_par[OF detnz])
  have enz: "e \<noteq> 0"
  proof
    assume ez: "e = 0"
    hence "c = 0"
      using ce linear_0[OF lin] by simp
    thus False
      using cnz unfolding c_def by simp
  qed
  have eenz: "e \<bullet> e \<noteq> 0"
    using enz inner_self_eq_zero_iff_vec2 by blast
  have cnz': "c \<noteq> 0"
    using cnz unfolding c_def .
  have dpnz: "d \<bullet> perp2 c \<noteq> 0"
  proof -
    have "d \<bullet> perp2 c =
        det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (e \<bullet> e)"
      unfolding d_def c_def e_def by (rule pivot_nonzero[OF detnz])
    thus ?thesis
      using detnz eenz by simp
  qed
  have y_eq: "y = single_bump_C2_target n1 g gp pe1 \<phi>"
    unfolding y_def n1_def g_def gp_def pe1_def by simp
  have p_eq: "p = single_bump_phase_point c d \<phi> y"
    unfolding p_def c_def d_def y_def n1_def g_def gp_def pe1_def by simp
  have phase: "c \<bullet> p = \<phi>"
    unfolding p_eq by (rule single_bump_phase_point_phase[OF cnz' dpnz])
  have target: "d \<bullet> p = y"
    unfolding p_eq by (rule single_bump_phase_point_target[OF cnz' dpnz])
  have dot_e: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> e = 0"
  proof -
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> e
        = - (2 * n1 * g * \<phi> * sin \<phi>)
          + gp * e1 * single_bump_W n1 \<phi>"
      using phase
      by (simp add: c_def e_def n1_def g_def gp_def e1_def single_bump_W_def
          gradU_dip_dot_e_par_single_bump[OF detnz])
    also have "\<dots> = 0"
      by (rule single_bump_C1_rhs_zero[OF n1nz gnz' root])
    finally show ?thesis .
  qed
  have dot_perp: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> perp2 e = 0"
  proof -
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> perp2 e
        = - (2 * n1 * g * y * sin \<phi>)
          + gp * pe1 * single_bump_W n1 \<phi>"
      using phase target
      by (simp add: c_def e_def d_def n1_def g_def gp_def pe1_def single_bump_W_def
          gradU_dip_dot_perp2_e_par_single_bump)
    also have "\<dots> = 0"
      unfolding y_eq
      by (rule single_bump_C2_target_zero[OF n1nz gnz' sinnz])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule dot_e_perp2_zero_imp_zero[OF enz dot_e dot_perp])
qed

end
