theory Scratch_D3Assembly
  imports "Applied_Math_M5_D3Xi.Scratch_D3Xi"
begin

text \<open>
  Assembly leaf, per Sketch.md \<section>6p/\<section>6l: combine Codex's critical-point
  construction (\<open>Scratch_D3Xi.thy\<close>) with Claude's \<open>\<Xi>\<close>-value formula
  (\<open>Scratch_D3Hess.thy\<close>'s \<open>Xi_single_bump_raw\<close>) and \<open>R_dip\<close> nonvanishing to
  finish \<open>Xi_nonzero_witness_exists\<close>.  New leaf per this project's own
  convention (\<section>6j/\<section>6n): assembly work does not edit either upstream
  scratch theory.
\<close>

section \<open>Codex's point equals \<open>(\<phi>/(c \<bullet> c)) c + \<phi> Q_dip \<bullet> perp2(c)\<close> given (C1)\<close>

lemma single_bump_C2_target_eq_phi_pe1_e1:
  fixes n1 g gp e1 pe1 \<phi> :: real
  assumes e1nz: "e1 \<noteq> 0"
    and gnz: "g \<noteq> 0"
    and n1nz: "n1 \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs n1 g gp e1 \<phi>"
  shows "single_bump_C2_target n1 g gp pe1 \<phi> = \<phi> * pe1 / e1"
proof -
  have step: "gp * single_bump_W n1 \<phi> * e1 = 2 * n1 * g * \<phi> * sin \<phi>"
  proof -
    have "\<phi> * sin \<phi> = gp * e1 * single_bump_W n1 \<phi> / (2 * n1 * g)"
      using root unfolding single_bump_C1_rhs_def .
    hence "\<phi> * sin \<phi> * (2 * n1 * g) = gp * e1 * single_bump_W n1 \<phi>"
      using gnz n1nz by (simp add: field_simps)
    thus ?thesis by (simp add: algebra_simps)
  qed
  have "single_bump_C2_target n1 g gp pe1 \<phi>
      = gp * pe1 * single_bump_W n1 \<phi> / (2 * n1 * g * sin \<phi>)"
    unfolding single_bump_C2_target_def ..
  also have "\<dots> = pe1 * (gp * single_bump_W n1 \<phi> * e1) / (2 * n1 * g * sin \<phi> * e1)"
    using e1nz by (simp add: field_simps)
  also have "\<dots> = pe1 * (2 * n1 * g * \<phi> * sin \<phi>) / (2 * n1 * g * sin \<phi> * e1)"
    unfolding step ..
  also have "\<dots> = \<phi> * pe1 / e1"
    using gnz n1nz sinnz by (simp add: field_simps)
  finally show ?thesis .
qed

lemma single_bump_phase_point_closed_form:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2" and \<phi> :: real and i :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and n1nz: "real (CARD('n)) - 1 \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
  shows "single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
      (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
      (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
        (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>)
    = (\<phi> / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)) *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>
      + (\<phi> * Q_dip \<omega>0 \<omega>s \<omega>) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define e where "e = e_par \<omega>0 \<omega>s \<omega>"
  define d where "d = Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 e)"
  define y where "y = single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 e) 1) \<phi>"
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have ce: "Dcvec_dip \<omega>0 \<omega>s \<omega> e = c"
    unfolding e_def c_def by (rule Dcvec_dip_e_par[OF detnz])
  have enz: "e \<noteq> 0"
  proof
    assume ez: "e = 0"
    hence "c = 0" using ce linear_0[OF lin] by simp
    thus False using cnz unfolding c_def by simp
  qed
  have eenz: "e \<bullet> e \<noteq> 0"
    using enz inner_self_eq_zero_iff_vec2 by blast
  have cnz': "c \<noteq> 0" using cnz unfolding c_def .
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz' inner_self_eq_zero_iff_vec2 by blast
  have pivot: "d \<bullet> perp2 c = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (e \<bullet> e)"
    unfolding d_def c_def e_def by (rule pivot_nonzero[OF detnz])
  have dpnz: "d \<bullet> perp2 c \<noteq> 0"
    unfolding pivot using detnz eenz by simp
  have e1nz': "vec_nth e 1 \<noteq> 0"
    unfolding e_def by (rule e1nz)
  have y_eq: "y = \<phi> * vec_nth (perp2 e) 1 / vec_nth e 1"
    unfolding y_def e_def[symmetric]
    using e1nz' gnz n1nz sinnz root
    by (intro single_bump_C2_target_eq_phi_pe1_e1) (simp_all add: e_def)
  have Qval_raw: "Q_dip \<omega>0 \<omega>s \<omega> =
      (vec_nth (perp2 e) 1 / vec_nth e 1 - (d \<bullet> c) / (c \<bullet> c))
        / (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (e \<bullet> e))"
    unfolding Q_dip_def e_def c_def d_def ..
  have Qval: "Q_dip \<omega>0 \<omega>s \<omega> =
      (vec_nth (perp2 e) 1 / vec_nth e 1 - (d \<bullet> c) / (c \<bullet> c)) / (d \<bullet> perp2 c)"
    unfolding Qval_raw pivot ..
  have coeff_eq: "(y - \<phi> * (d \<bullet> c) / (c \<bullet> c)) / (d \<bullet> perp2 c) = \<phi> * Q_dip \<omega>0 \<omega>s \<omega>"
    unfolding y_eq Qval
    using e1nz' ccnz by (simp add: field_simps)
  have coeff_eq_raw: "(single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
        (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>
      - \<phi> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>)) \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
        / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>))
      / (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>)) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
    = \<phi> * Q_dip \<omega>0 \<omega>s \<omega>"
    using coeff_eq unfolding y_def c_def d_def e_def by simp
  show ?thesis
    unfolding single_bump_phase_point_def coeff_eq_raw ..
qed

lemma single_bump_phase_point_dot_general:
  fixes \<omega>0 \<omega>s \<omega> v :: "real^2" and \<phi> :: real and i :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and n1nz: "real (CARD('n)) - 1 \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
  shows "v \<bullet> single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
      (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
      (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
        (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>)
    = \<phi> * ((v \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>) / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
        + Q_dip \<omega>0 \<omega>s \<omega> * (v \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"
  unfolding single_bump_phase_point_closed_form[OF detnz cnz e1nz gnz n1nz sinnz root]
  by (simp add: inner_add_right algebra_simps)

corollary single_bump_phase_point_dot_eq_phi_R:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2" and \<phi> :: real and i :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and n1nz: "real (CARD('n)) - 1 \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
  shows "Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet>
      single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
        (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
        (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
          (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>)
    = \<phi> * R_dip \<omega>0 \<omega>s \<omega> w"
  unfolding single_bump_phase_point_dot_general[OF detnz cnz e1nz gnz n1nz sinnz root]
    R_dip_def ..

corollary single_bump_phase_point_dot_eq_phi_S:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2" and \<phi> :: real and i :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and n1nz: "real (CARD('n)) - 1 \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
  shows "D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet>
      single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
        (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
        (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
          (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>)
    = \<phi> * ((D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
          / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
        + Q_dip \<omega>0 \<omega>s \<omega>
          * (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"
  by (rule single_bump_phase_point_dot_general[OF detnz cnz e1nz gnz n1nz sinnz root])

section \<open>The closed \<open>\<Xi>\<close> value at the critical point, and its bounded residual\<close>

definition single_bump_S_raw :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "single_bump_S_raw \<omega>0 \<omega>s \<omega> w =
     (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
       / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
     + Q_dip \<omega>0 \<omega>s \<omega> * (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))"

definition single_bump_residual :: "'n::finite itself \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real" where
  "single_bump_residual (TYPE('n)) \<omega>0 \<omega>s \<omega> w \<phi> =
     - 2 * (real (CARD('n)) - 1)
       * single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
           (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>
       * (deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * R_dip \<omega>0 \<omega>s \<omega> w
          + gain_dip \<omega> * single_bump_S_raw \<omega>0 \<omega>s \<omega> w
          + deriv gdip (vec_nth \<omega> 1) * vec_nth w 1)
     + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
       * ((real (CARD('n)) - 1)\<^sup>2 + 1 + 2 * (real (CARD('n)) - 1) * cos \<phi>)"

lemma Xi_at_phase_point_closed:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2" and \<phi> :: real and i :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and n1nz: "real (CARD('n)) - 1 \<noteq> 0"
    and phinz: "\<phi> \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
  shows "Xi (slot i (single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
        (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
        (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
          (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>))) \<omega>0 \<omega>s \<omega> w
    = - 2 * (real (CARD('n)) - 1) * gain_dip \<omega> * R_dip \<omega>0 \<omega>s \<omega> w * \<phi>\<^sup>2 * cos \<phi>
      + single_bump_residual TYPE('n) \<omega>0 \<omega>s \<omega> w \<phi>"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define e where "e = e_par \<omega>0 \<omega>s \<omega>"
  define d where "d = Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 e)"
  define p where "p = single_bump_phase_point c d \<phi>
      (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
        (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 e) 1) \<phi>)"
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have ce: "Dcvec_dip \<omega>0 \<omega>s \<omega> e = c"
    unfolding e_def c_def by (rule Dcvec_dip_e_par[OF detnz])
  have enz: "e \<noteq> 0"
  proof
    assume ez: "e = 0"
    hence "c = 0" using ce linear_0[OF lin] by simp
    thus False using cnz unfolding c_def by simp
  qed
  have eenz: "e \<bullet> e \<noteq> 0"
    using enz inner_self_eq_zero_iff_vec2 by blast
  have cnz': "c \<noteq> 0" using cnz unfolding c_def .
  have pivot: "d \<bullet> perp2 c = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (e \<bullet> e)"
    unfolding d_def c_def e_def by (rule pivot_nonzero[OF detnz])
  have dpnz: "d \<bullet> perp2 c \<noteq> 0"
    unfolding pivot using detnz eenz by simp
  have phase: "c \<bullet> p = \<phi>"
    unfolding p_def c_def[symmetric] by (rule single_bump_phase_point_phase[OF cnz' dpnz])
  have phase_raw: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p = \<phi>"
    using phase unfolding c_def .
  have dotR: "Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> p = \<phi> * R_dip \<omega>0 \<omega>s \<omega> w"
    unfolding p_def c_def d_def e_def
    by (rule single_bump_phase_point_dot_eq_phi_R[OF detnz cnz e1nz gnz n1nz sinnz root])
  have dotS: "D2cvec_dip \<omega>0 \<omega>s \<omega> e w \<bullet> p = \<phi> * single_bump_S_raw \<omega>0 \<omega>s \<omega> w"
    unfolding p_def c_def d_def e_def single_bump_S_raw_def
    by (rule single_bump_phase_point_dot_eq_phi_S[OF detnz cnz e1nz gnz n1nz sinnz root])
  have raw: "Xi (slot i p) \<omega>0 \<omega>s \<omega> w
      = - (2 * (real (CARD('n)) - 1) * deriv gdip (vec_nth \<omega> 1) * vec_nth e 1
            * (\<phi> * R_dip \<omega>0 \<omega>s \<omega> w) * sin \<phi>)
        + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth e 1
          * ((real (CARD('n)) - 1)\<^sup>2 + 1 + 2 * (real (CARD('n)) - 1) * cos \<phi>)
        - (2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * (\<phi> * single_bump_S_raw \<omega>0 \<omega>s \<omega> w) * sin \<phi>)
        - (2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * \<phi> * (\<phi> * R_dip \<omega>0 \<omega>s \<omega> w) * cos \<phi>)
        - (2 * (real (CARD('n)) - 1) * deriv gdip (vec_nth \<omega> 1) * vec_nth w 1
            * \<phi> * sin \<phi>)"
    unfolding Xi_single_bump_raw[OF detnz] e_def[symmetric] phase_raw dotR dotS ..
  have sin_eq: "sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth e 1) \<phi> / \<phi>"
    using root phinz unfolding e_def by (simp add: field_simps)
  have p_raw: "p = single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
      (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
      (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
        (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>)"
    unfolding p_def c_def d_def e_def ..
  show ?thesis
    unfolding p_raw[symmetric] raw single_bump_residual_def sin_eq e_def
    using phinz by (simp add: field_simps power2_eq_square)
qed

section \<open>Bounding the residual and the final existence theorem\<close>

lemma single_bump_W_bounds:
  fixes n1 \<phi> :: real
  assumes n1pos: "0 < n1"
  shows "0 \<le> single_bump_W n1 \<phi>" "single_bump_W n1 \<phi> \<le> (n1 + 1)\<^sup>2"
proof -
  have lo: "single_bump_W n1 \<phi> \<ge> n1\<^sup>2 + 1 - 2 * n1"
    unfolding single_bump_W_def
    using cos_ge_minus_one[of \<phi>] mult_left_mono[of "-1" "cos \<phi>" "2 * n1"] n1pos
    by simp
  have hi: "single_bump_W n1 \<phi> \<le> n1\<^sup>2 + 1 + 2 * n1"
    unfolding single_bump_W_def
    using cos_le_one[of \<phi>] mult_left_mono[of "cos \<phi>" 1 "2 * n1"] n1pos
    by simp
  have sq_lo: "n1\<^sup>2 + 1 - 2 * n1 = (n1 - 1)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
  have sq_hi: "n1\<^sup>2 + 1 + 2 * n1 = (n1 + 1)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
  show "0 \<le> single_bump_W n1 \<phi>"
    using lo sq_lo zero_le_power2[of "n1 - 1"] by linarith
  show "single_bump_W n1 \<phi> \<le> (n1 + 1)\<^sup>2"
    using hi sq_hi by linarith
qed

lemma single_bump_C1_rhs_bound:
  fixes n1 g gp e1 \<phi> :: real
  assumes n1pos: "0 < n1" and gnz: "g \<noteq> 0"
  shows "\<bar>single_bump_C1_rhs n1 g gp e1 \<phi>\<bar> \<le> \<bar>gp * e1\<bar> * (n1 + 1)\<^sup>2 / (2 * n1 * \<bar>g\<bar>)"
proof -
  have W0: "0 \<le> single_bump_W n1 \<phi>" and Whi: "single_bump_W n1 \<phi> \<le> (n1 + 1)\<^sup>2"
    using single_bump_W_bounds[OF n1pos] by auto
  have absW: "\<bar>single_bump_W n1 \<phi>\<bar> = single_bump_W n1 \<phi>"
    using W0 by simp
  have "\<bar>single_bump_C1_rhs n1 g gp e1 \<phi>\<bar>
      = \<bar>gp * e1\<bar> * \<bar>single_bump_W n1 \<phi>\<bar> / (2 * n1 * \<bar>g\<bar>)"
    unfolding single_bump_C1_rhs_def
    using n1pos by (simp add: abs_mult abs_divide)
  also have "\<dots> \<le> \<bar>gp * e1\<bar> * (n1 + 1)\<^sup>2 / (2 * n1 * \<bar>g\<bar>)"
    unfolding absW
  proof (rule divide_right_mono)
    show "\<bar>gp * e1\<bar> * single_bump_W n1 \<phi> \<le> \<bar>gp * e1\<bar> * (n1 + 1)\<^sup>2"
      using Whi by (rule mult_left_mono) simp
    show "0 \<le> 2 * n1 * \<bar>g\<bar>" using n1pos by simp
  qed
  finally show ?thesis .
qed

text \<open>The residual bound: a FIXED constant, independent of \<open>\<phi>\<close>, Sketch.md \<section>6o.\<close>

definition single_bump_residual_bound :: "'n::finite itself \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "single_bump_residual_bound (TYPE('n)) \<omega>0 \<omega>s \<omega> w =
     2 * (real (CARD('n)) - 1)
       * (\<bar>deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1\<bar> * (real (CARD('n)))\<^sup>2
          / (2 * (real (CARD('n)) - 1) * \<bar>gain_dip \<omega>\<bar>))
       * \<bar>deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * R_dip \<omega>0 \<omega>s \<omega> w
          + gain_dip \<omega> * single_bump_S_raw \<omega>0 \<omega>s \<omega> w
          + deriv gdip (vec_nth \<omega> 1) * vec_nth w 1\<bar>
     + \<bar>deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1\<bar>
       * (real (CARD('n)))\<^sup>2"

lemma single_bump_residual_le_bound:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2" and \<phi> :: real and i :: "'n::finite"
  assumes n1pos: "0 < real (CARD('n)) - 1"
    and gnz: "gain_dip \<omega> \<noteq> 0"
  shows "\<bar>single_bump_residual TYPE('n) \<omega>0 \<omega>s \<omega> w \<phi>\<bar> \<le> single_bump_residual_bound TYPE('n) \<omega>0 \<omega>s \<omega> w"
proof -
  define n1 where "n1 = real (CARD('n)) - 1"
  define B where "B = single_bump_C1_rhs n1 (gain_dip \<omega>) (deriv gdip (vec_nth \<omega> 1))
      (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
  define Kcomb where "Kcomb = deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * R_dip \<omega>0 \<omega>s \<omega> w
      + gain_dip \<omega> * single_bump_S_raw \<omega>0 \<omega>s \<omega> w
      + deriv gdip (vec_nth \<omega> 1) * vec_nth w 1"
  have n1pos': "0 < n1"
    using n1pos unfolding n1_def .
  have Bbound: "\<bar>B\<bar> \<le> \<bar>deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1\<bar> * (n1 + 1)\<^sup>2 / (2 * n1 * \<bar>gain_dip \<omega>\<bar>)"
    unfolding B_def by (rule single_bump_C1_rhs_bound[OF n1pos' gnz])
  have n1eq: "n1 + 1 = real (CARD('n))"
    unfolding n1_def by simp
  have residual_eq: "single_bump_residual TYPE('n) \<omega>0 \<omega>s \<omega> w \<phi>
      = - 2 * n1 * B * Kcomb
        + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * (n1\<^sup>2 + 1 + 2 * n1 * cos \<phi>)"
    unfolding single_bump_residual_def n1_def B_def Kcomb_def ..
  have cosb: "n1\<^sup>2 + 1 + 2 * n1 * cos \<phi> \<le> (n1 + 1)\<^sup>2"
    using single_bump_W_bounds(2)[of n1 \<phi>] n1pos unfolding n1_def single_bump_W_def
    by (simp add: n1_def)
  have cosb0: "0 \<le> n1\<^sup>2 + 1 + 2 * n1 * cos \<phi>"
    using single_bump_W_bounds(1)[of n1 \<phi>] n1pos unfolding n1_def single_bump_W_def
    by (simp add: n1_def)
  have "\<bar>single_bump_residual TYPE('n) \<omega>0 \<omega>s \<omega> w \<phi>\<bar>
      \<le> \<bar>2 * n1 * B * Kcomb\<bar>
        + \<bar>deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
            * (n1\<^sup>2 + 1 + 2 * n1 * cos \<phi>)\<bar>"
    unfolding residual_eq
    using abs_triangle_ineq[of "- (2 * n1 * B * Kcomb)"
        "deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * (n1\<^sup>2 + 1 + 2 * n1 * cos \<phi>)"]
    by simp
  also have "\<dots> \<le> 2 * n1 * (\<bar>deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1\<bar>
        * (n1 + 1)\<^sup>2 / (2 * n1 * \<bar>gain_dip \<omega>\<bar>)) * \<bar>Kcomb\<bar>
        + \<bar>deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1\<bar>
          * (n1 + 1)\<^sup>2"
  proof (rule add_mono)
    show "\<bar>2 * n1 * B * Kcomb\<bar>
        \<le> 2 * n1 * (\<bar>deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1\<bar>
             * (n1 + 1)\<^sup>2 / (2 * n1 * \<bar>gain_dip \<omega>\<bar>)) * \<bar>Kcomb\<bar>"
    proof -
      have "\<bar>2 * n1 * B * Kcomb\<bar> = (2 * n1) * \<bar>B\<bar> * \<bar>Kcomb\<bar>"
        using n1pos' by (simp add: abs_mult abs_of_pos)
      also have "\<dots> \<le> (2 * n1) * (\<bar>deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1\<bar>
            * (n1 + 1)\<^sup>2 / (2 * n1 * \<bar>gain_dip \<omega>\<bar>)) * \<bar>Kcomb\<bar>"
        using Bbound n1pos' by (intro mult_right_mono mult_left_mono) (simp_all add: abs_of_pos[OF n1pos'])
      finally show ?thesis by simp
    qed
  next
    show "\<bar>deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
            * (n1\<^sup>2 + 1 + 2 * n1 * cos \<phi>)\<bar>
        \<le> \<bar>deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1\<bar>
          * (n1 + 1)\<^sup>2"
      unfolding abs_mult abs_of_nonneg[OF cosb0]
      using cosb by (intro mult_left_mono) simp_all
  qed
  finally show ?thesis
    unfolding single_bump_residual_bound_def n1eq[symmetric] n1_def[symmetric] Kcomb_def[symmetric]
    by simp
qed

theorem Xi_nonzero_witness_of_good_phase:
  fixes i :: "'n::finite"
    and \<omega>0 \<omega>s \<omega> w :: "real^2"
    and \<phi> :: real
  defines "p \<equiv> single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
      (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
      (single_bump_C2_target (real (CARD('n)) - 1) (gain_dip \<omega>)
        (deriv gdip (vec_nth \<omega> 1)) (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1) \<phi>)"
  assumes card2: "2 \<le> CARD('n)"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and phinz: "\<phi> \<noteq> 0"
    and sinnz: "sin \<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
    and dominates: "single_bump_residual_bound TYPE('n) \<omega>0 \<omega>s \<omega> w
        < \<bar>- 2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * R_dip \<omega>0 \<omega>s \<omega> w * \<phi>\<^sup>2 * cos \<phi>\<bar>"
  shows "\<exists>x::(real^2)^'n.
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
    \<and> Xi x \<omega>0 \<omega>s \<omega> w \<noteq> 0"
proof -
  define n1 where "n1 = real (CARD('n)) - 1"
  have n1pos: "0 < n1"
  proof -
    have "2 \<le> real CARD('n)"
      using card2 by simp
    thus ?thesis
      unfolding n1_def by linarith
  qed
  have n1nz: "n1 \<noteq> 0"
    using n1pos by simp
  have root_n1: "\<phi> * sin \<phi> = single_bump_C1_rhs n1 (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
    using root unfolding n1_def .
  have n1nz_expanded: "real (CARD('n)) - 1 \<noteq> 0"
    using n1nz unfolding n1_def .
  have crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> = 0"
    unfolding p_def
    by (rule single_bump_gradU_zero_of_phase_root_and_C2_target[OF card2 detnz cnz gnz sinnz root])
  define L where "L = - 2 * n1 * gain_dip \<omega> * R_dip \<omega>0 \<omega>s \<omega> w * \<phi>\<^sup>2 * cos \<phi>"
  define E where "E = single_bump_residual TYPE('n) \<omega>0 \<omega>s \<omega> w \<phi>"
  have xi_eq: "Xi (slot i p) \<omega>0 \<omega>s \<omega> w = L + E"
    unfolding L_def E_def p_def n1_def
    by (rule Xi_at_phase_point_closed[OF detnz cnz e1nz gnz n1nz_expanded phinz sinnz root])
  have E_le: "\<bar>E\<bar> \<le> single_bump_residual_bound TYPE('n) \<omega>0 \<omega>s \<omega> w"
    unfolding E_def
    by (rule single_bump_residual_le_bound[OF _ gnz]) (simp add: n1_def[symmetric] n1pos)
  have E_lt_L: "\<bar>E\<bar> < \<bar>L\<bar>"
    using E_le dominates unfolding L_def n1_def by linarith
  have L_plus_E_nz: "L + E \<noteq> 0"
  proof
    assume z: "L + E = 0"
    hence "L = - E"
      by simp
    hence "\<bar>L\<bar> = \<bar>E\<bar>"
      by simp
    thus False
      using E_lt_L by simp
  qed
  have xi_nz: "Xi (slot i p) \<omega>0 \<omega>s \<omega> w \<noteq> 0"
    using xi_eq L_plus_E_nz by simp
  show ?thesis
    by (intro exI[of _ "slot i p"] conjI crit xi_nz)
qed


section \<open>The sin-free radial point and the final root-window assembly\<close>

definition single_bump_radial_point ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real^2" where
  "single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi> =
     single_bump_phase_point (cvec_dip \<omega>0 \<omega>s \<omega>)
       (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))) \<phi>
       (\<phi> * vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1 / vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)"

lemma single_bump_radial_point_closed_form:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2" and \<phi> :: real
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
  shows "single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi>
    = (\<phi> / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)) *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>
      + (\<phi> * Q_dip \<omega>0 \<omega>s \<omega>) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define e where "e = e_par \<omega>0 \<omega>s \<omega>"
  define d where "d = Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 e)"
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have ce: "Dcvec_dip \<omega>0 \<omega>s \<omega> e = c"
    unfolding e_def c_def by (rule Dcvec_dip_e_par[OF detnz])
  have enz: "e \<noteq> 0"
  proof
    assume ez: "e = 0"
    hence "c = 0" using ce linear_0[OF lin] by simp
    thus False using cnz unfolding c_def by simp
  qed
  have eenz: "e \<bullet> e \<noteq> 0"
    using enz inner_self_eq_zero_iff_vec2 by blast
  have cnz': "c \<noteq> 0" using cnz unfolding c_def .
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz' inner_self_eq_zero_iff_vec2 by blast
  have pivot: "d \<bullet> perp2 c = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (e \<bullet> e)"
    unfolding d_def c_def e_def by (rule pivot_nonzero[OF detnz])
  have e1nz': "vec_nth e 1 \<noteq> 0"
    using e1nz unfolding e_def .
  have Qval_raw: "Q_dip \<omega>0 \<omega>s \<omega> =
      (vec_nth (perp2 e) 1 / vec_nth e 1 - (d \<bullet> c) / (c \<bullet> c))
        / (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (e \<bullet> e))"
    unfolding Q_dip_def e_def c_def d_def ..
  have Qval: "Q_dip \<omega>0 \<omega>s \<omega> =
      (vec_nth (perp2 e) 1 / vec_nth e 1 - (d \<bullet> c) / (c \<bullet> c)) / (d \<bullet> perp2 c)"
    unfolding Qval_raw pivot ..
  have coeff_eq:
      "(\<phi> * vec_nth (perp2 e) 1 / vec_nth e 1 - \<phi> * (d \<bullet> c) / (c \<bullet> c))
        / (d \<bullet> perp2 c) = \<phi> * Q_dip \<omega>0 \<omega>s \<omega>"
    unfolding Qval using e1nz' ccnz by (simp add: field_simps)
  show ?thesis
    unfolding single_bump_radial_point_def single_bump_phase_point_def
      c_def d_def e_def coeff_eq
    by (simp add: Qval c_def d_def e_def right_diff_distrib)
qed

lemma single_bump_radial_point_dot_general:
  fixes \<omega>0 \<omega>s \<omega> v :: "real^2" and \<phi> :: real
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
  shows "v \<bullet> single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi>
    = \<phi> * ((v \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>) / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
        + Q_dip \<omega>0 \<omega>s \<omega> * (v \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"
  unfolding single_bump_radial_point_closed_form[OF detnz cnz e1nz]
  by (simp add: inner_add_right algebra_simps)

corollary single_bump_radial_point_dot_eq_phi_R:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2" and \<phi> :: real
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
  shows "Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi>
    = \<phi> * R_dip \<omega>0 \<omega>s \<omega> w"
  unfolding single_bump_radial_point_dot_general[OF detnz cnz e1nz]
    R_dip_def ..

corollary single_bump_radial_point_dot_eq_phi_S:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2" and \<phi> :: real
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
  shows "D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet> single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi>
    = \<phi> * single_bump_S_raw \<omega>0 \<omega>s \<omega> w"
  unfolding single_bump_radial_point_dot_general[OF detnz cnz e1nz]
    single_bump_S_raw_def ..

lemma single_bump_C2_radial_zero:
  assumes n1nz: "n1 \<noteq> 0"
    and gnz: "g \<noteq> 0"
    and e1nz: "e1 \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs n1 g gp e1 \<phi>"
  shows "- (2 * n1 * g * (\<phi> * pe1 / e1) * sin \<phi>)
      + gp * pe1 * single_bump_W n1 \<phi> = 0"
proof -
  have eq: "gp * e1 * single_bump_W n1 \<phi> = 2 * n1 * g * \<phi> * sin \<phi>"
    using root n1nz gnz unfolding single_bump_C1_rhs_def
    by (simp add: field_simps)
  have "gp * pe1 * single_bump_W n1 \<phi>
      = pe1 * (2 * n1 * g * \<phi> * sin \<phi>) / e1"
    using eq e1nz by (simp add: field_simps)
  thus ?thesis
    using e1nz by (simp add: field_simps)
qed

theorem single_bump_gradU_zero_of_phase_root_radial:
  fixes i :: "'n::finite"
    and \<omega>0 \<omega>s \<omega> :: "real^2"
    and \<phi> :: real
  defines "p \<equiv> single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi>"
    and "n1 \<equiv> real (CARD('n)) - 1"
    and "g \<equiv> gain_dip \<omega>"
    and "gp \<equiv> deriv gdip (vec_nth \<omega> 1)"
    and "e \<equiv> e_par \<omega>0 \<omega>s \<omega>"
    and "e1 \<equiv> vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
    and "pe1 \<equiv> vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1"
  assumes card2: "2 \<le> CARD('n)"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs n1 g gp e1 \<phi>"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> = 0"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define d where "d = Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 e)"
  have n1nz: "n1 \<noteq> 0"
  proof -
    have "2 \<le> real CARD('n)"
      using card2 by simp
    hence "0 < n1"
      unfolding n1_def by linarith
    thus ?thesis by simp
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
    hence "c = 0" using ce linear_0[OF lin] by simp
    thus False using cnz unfolding c_def by simp
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
  have p_phase: "c \<bullet> p = \<phi>"
    unfolding p_def single_bump_radial_point_def c_def d_def e_def
    using assms(10,5) c_def d_def dpnz single_bump_phase_point_phase by blast
  have p_target: "d \<bullet> p = \<phi> * pe1 / e1"
    unfolding p_def single_bump_radial_point_def c_def d_def e_def pe1_def e1_def
    using assms(5) c_def cnz' d_def dpnz single_bump_phase_point_target by blast
  have dot_e: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> e = 0"
  proof -
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> e
        = - (2 * n1 * g * \<phi> * sin \<phi>)
          + gp * e1 * single_bump_W n1 \<phi>"
      using p_phase
      by (simp add: c_def e_def n1_def g_def gp_def e1_def single_bump_W_def
          gradU_dip_dot_e_par_single_bump[OF detnz])
    also have "\<dots> = 0"
      by (rule single_bump_C1_rhs_zero[OF n1nz gnz' root])
    finally show ?thesis .
  qed
  have dot_perp: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> perp2 e = 0"
  proof -
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> perp2 e
        = - (2 * n1 * g * (\<phi> * pe1 / e1) * sin \<phi>)
          + gp * pe1 * single_bump_W n1 \<phi>"
      using p_phase p_target
      by (simp add: c_def d_def e_def n1_def g_def gp_def pe1_def single_bump_W_def
          gradU_dip_dot_perp2_e_par_single_bump)
    also have "\<dots> = 0"
      by (rule single_bump_C2_radial_zero[OF n1nz gnz' _ root])
         (simp add: e1_def e1nz)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule dot_e_perp2_zero_imp_zero[OF enz dot_e dot_perp])
qed

lemma Xi_at_radial_point_closed:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2" and \<phi> :: real and i :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and n1nz: "real (CARD('n)) - 1 \<noteq> 0"
    and phinz: "\<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
  shows "Xi (slot i (single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi>)) \<omega>0 \<omega>s \<omega> w
    = - 2 * (real (CARD('n)) - 1) * gain_dip \<omega> * R_dip \<omega>0 \<omega>s \<omega> w * \<phi>\<^sup>2 * cos \<phi>
      + single_bump_residual TYPE('n) \<omega>0 \<omega>s \<omega> w \<phi>"
proof -
  define p where "p = single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi>"
  have phase: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p = \<phi>"
  proof -
    define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
    define e where "e = e_par \<omega>0 \<omega>s \<omega>"
    define d where "d = Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 e)"
    have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
      by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
    have ce: "Dcvec_dip \<omega>0 \<omega>s \<omega> e = c"
      unfolding e_def c_def by (rule Dcvec_dip_e_par[OF detnz])
    have enz: "e \<noteq> 0"
    proof
      assume ez: "e = 0"
      hence "c = 0" using ce linear_0[OF lin] by simp
      thus False using cnz unfolding c_def by simp
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
    show ?thesis
      unfolding p_def single_bump_radial_point_def c_def d_def e_def
      using c_def cnz' d_def dpnz e_def single_bump_phase_point_phase by blast
  qed
  have dotR: "Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> p = \<phi> * R_dip \<omega>0 \<omega>s \<omega> w"
    unfolding p_def by (rule single_bump_radial_point_dot_eq_phi_R[OF detnz cnz e1nz])
  have dotS: "D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet> p =
      \<phi> * single_bump_S_raw \<omega>0 \<omega>s \<omega> w"
    unfolding p_def by (rule single_bump_radial_point_dot_eq_phi_S[OF detnz cnz e1nz])
  have raw: "Xi (slot i p) \<omega>0 \<omega>s \<omega> w
      = - (2 * (real (CARD('n)) - 1) * deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
            * (\<phi> * R_dip \<omega>0 \<omega>s \<omega> w) * sin \<phi>)
        + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * ((real (CARD('n)) - 1)\<^sup>2 + 1 + 2 * (real (CARD('n)) - 1) * cos \<phi>)
        - (2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * (\<phi> * single_bump_S_raw \<omega>0 \<omega>s \<omega> w) * sin \<phi>)
        - (2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * \<phi> * (\<phi> * R_dip \<omega>0 \<omega>s \<omega> w) * cos \<phi>)
        - (2 * (real (CARD('n)) - 1) * deriv gdip (vec_nth \<omega> 1) * vec_nth w 1
            * \<phi> * sin \<phi>)"
    unfolding Xi_single_bump_raw[OF detnz] phase dotR dotS ..
  have sin_eq: "sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi> / \<phi>"
    using root phinz by (simp add: field_simps)
  show ?thesis
    unfolding p_def[symmetric] raw single_bump_residual_def sin_eq
    using phinz by (simp add: field_simps power2_eq_square)
qed

theorem Xi_nonzero_witness_of_good_phase_radial:
  fixes i :: "'n::finite"
    and \<omega>0 \<omega>s \<omega> w :: "real^2"
    and \<phi> :: real
  assumes card2: "2 \<le> CARD('n)"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and phinz: "\<phi> \<noteq> 0"
    and root: "\<phi> * sin \<phi> = single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
    and dominates: "single_bump_residual_bound TYPE('n) \<omega>0 \<omega>s \<omega> w
        < \<bar>- 2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * R_dip \<omega>0 \<omega>s \<omega> w * \<phi>\<^sup>2 * cos \<phi>\<bar>"
  shows "\<exists>x::(real^2)^'n.
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
    \<and> Xi x \<omega>0 \<omega>s \<omega> w \<noteq> 0"
proof -
  define p where "p = single_bump_radial_point \<omega>0 \<omega>s \<omega> \<phi>"
  define n1 where "n1 = real (CARD('n)) - 1"
  have n1pos: "0 < n1"
  proof -
    have "2 \<le> real CARD('n)"
      using card2 by simp
    thus ?thesis
      unfolding n1_def by linarith
  qed
  have n1nz: "n1 \<noteq> 0"
    using n1pos by simp
  have n1nz_expanded: "real (CARD('n)) - 1 \<noteq> 0"
    using n1nz unfolding n1_def .
  have root_n1: "\<phi> * sin \<phi> = single_bump_C1_rhs n1 (gain_dip \<omega>)
      (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
    using root unfolding n1_def .
  have crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> = 0"
    unfolding p_def
    using assms(2,3,4,5,7) card2 single_bump_gradU_zero_of_phase_root_radial by blast
  define L where "L = - 2 * n1 * gain_dip \<omega> * R_dip \<omega>0 \<omega>s \<omega> w * \<phi>\<^sup>2 * cos \<phi>"
  define E where "E = single_bump_residual TYPE('n) \<omega>0 \<omega>s \<omega> w \<phi>"
  have xi_eq: "Xi (slot i p) \<omega>0 \<omega>s \<omega> w = L + E"
    unfolding L_def E_def p_def n1_def
    by (rule Xi_at_radial_point_closed[OF detnz cnz e1nz gnz n1nz_expanded phinz root])
  have E_le: "\<bar>E\<bar> \<le> single_bump_residual_bound TYPE('n) \<omega>0 \<omega>s \<omega> w"
    unfolding E_def
    by (rule single_bump_residual_le_bound[OF _ gnz]) (simp add: n1_def[symmetric] n1pos)
  have E_lt_L: "\<bar>E\<bar> < \<bar>L\<bar>"
    using E_le dominates unfolding L_def n1_def by linarith
  have L_plus_E_nz: "L + E \<noteq> 0"
  proof
    assume z: "L + E = 0"
    hence "L = - E"
      by simp
    hence "\<bar>L\<bar> = \<bar>E\<bar>"
      by simp
    thus False
      using E_lt_L by simp
  qed
  have xi_nz: "Xi (slot i p) \<omega>0 \<omega>s \<omega> w \<noteq> 0"
    using xi_eq L_plus_E_nz by simp
  show ?thesis
    by (intro exI[of _ "slot i p"] conjI crit xi_nz)
qed

theorem Xi_nonzero_witness_exists:
  fixes i :: "'n::finite"
    and \<omega>0 \<omega>s \<omega> w :: "real^2"
  assumes card2: "2 \<le> CARD('n)"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and w1nz: "vec_nth w 1 \<noteq> 0"
  shows "\<exists>x::(real^2)^'n.
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
    \<and> Xi x \<omega>0 \<omega>s \<omega> w \<noteq> 0"
proof -
  define n1 where "n1 = real (CARD('n)) - 1"
  define gp where "gp = deriv gdip (vec_nth \<omega> 1)"
  define e1 where "e1 = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define R where "R = R_dip \<omega>0 \<omega>s \<omega> w"
  define Cbound where "Cbound = \<bar>gp * e1\<bar> * (n1 + 1)\<^sup>2 / (2 * n1 * \<bar>gain_dip \<omega>\<bar>)"
  define Rbound where "Rbound = single_bump_residual_bound TYPE('n) \<omega>0 \<omega>s \<omega> w"
  define s2 where "s2 = sqrt 2 / 2"
  define A where "A = 2 * n1 * \<bar>gain_dip \<omega>\<bar> * \<bar>R\<bar>"
  have n1pos: "0 < n1"
  proof -
    have "2 \<le> real CARD('n)"
      using card2 by simp
    thus ?thesis
      unfolding n1_def by linarith
  qed
  have n1nz: "n1 \<noteq> 0"
    using n1pos by simp
  have gnz_abs: "\<bar>gain_dip \<omega>\<bar> > 0"
    using gnz by simp
  have Rnz: "R \<noteq> 0"
    unfolding R_def
    using R_dip_eq_zero_iff[OF detnz cnz e1nz, of w] w1nz by simp
  have Rabs_pos: "\<bar>R\<bar> > 0"
    using Rnz by simp
  have Apos: "0 < A"
    unfolding A_def using n1pos gnz_abs Rabs_pos by simp
  have s2pos: "0 < s2"
    unfolding s2_def using real_sqrt_gt_zero[of 2] by simp
  have Cbound_ge0: "0 \<le> Cbound"
    unfolding Cbound_def using n1pos gnz_abs by simp
  define K where "K = max 1 (max (Cbound / s2 + 1) (Rbound / (A * s2) + 1))"
  have Kge1: "1 \<le> K"
    unfolding K_def by simp
  have Kpos: "0 < K"
    using Kge1 by linarith
  have KC: "Cbound < K * s2"
  proof -
    have "Cbound / s2 + 1 \<le> K"
      unfolding K_def by simp
    hence "Cbound / s2 < K"
      by linarith
    hence "Cbound < K * s2"
      using s2pos by (simp add: field_simps)
    thus ?thesis .
  qed
  have KR: "Rbound < A * K\<^sup>2 * s2"
  proof -
    have "Rbound / (A * s2) + 1 \<le> K"
      unfolding K_def by simp
    hence "Rbound / (A * s2) < K"
      by linarith
    hence Rlt: "Rbound < A * s2 * K"
      using Apos s2pos by (simp add: field_simps)
    have "K \<le> K\<^sup>2"
      using Kge1 Kpos by (simp add: power2_eq_square mult_left_le_one_le)
    hence "A * s2 * K \<le> A * s2 * K\<^sup>2"
      using Apos s2pos by (intro mult_left_mono) simp_all
    also have "\<dots> = A * K\<^sup>2 * s2"
      by (simp add: algebra_simps)
    finally show ?thesis
      using Rlt by linarith
  qed
  have twopi_pos: "0 < 2 * pi"
    using pi_gt_zero by simp
  obtain M where Mlarge: "K + pi / 4 < real M * (2 * pi)"
    using reals_Archimedean3[OF twopi_pos, rule_format, of "K + pi / 4"] by blast
  define lo where "lo = real (2 * M) * pi - pi / 4"
  have twoM_eq: "real (2 * M) * pi = real M * (2 * pi)"
    by (simp add: algebra_simps)
  have Klo: "K < lo"
    using Mlarge unfolding lo_def twoM_eq by linarith
  have lopos: "0 < lo"
    using Kpos Klo by linarith
  have Mbig: "(real (2 * M) * pi - pi / 4) * (sqrt 2 / 2) > Cbound"
    using KC Klo s2pos unfolding lo_def[symmetric] s2_def
    by (meson less_trans mult_strict_right_mono)
  define B where "B = (\<lambda>t. single_bump_C1_rhs n1 (gain_dip \<omega>) gp e1 t)"
  have Bbound: "\<And>t. \<bar>B t\<bar> \<le> Cbound"
    unfolding B_def Cbound_def
    by (rule single_bump_C1_rhs_bound[OF n1pos gnz])
  have Bcont: "continuous_on UNIV B"
    unfolding B_def single_bump_C1_rhs_def single_bump_W_def
    by (intro continuous_intros, simp add: assms(5) n1nz)
  obtain \<phi> where philo: "real (2 * M) * pi - pi / 4 < \<phi>"
      and root: "\<phi> * sin \<phi> = B \<phi>"
      and cosgt: "cos \<phi> > sqrt 2 / 2"
    using phi_sin_eq_B_root_exists_even[OF Bbound Bcont Mbig] by blast
  have phigtlo: "lo < \<phi>"
    using philo unfolding lo_def .
  have phipos: "0 < \<phi>"
    using lopos phigtlo by linarith
  have phinz: "\<phi> \<noteq> 0"
    using phipos by simp
  have root_expanded: "\<phi> * sin \<phi> =
      single_bump_C1_rhs (real (CARD('n)) - 1) (gain_dip \<omega>)
        (deriv gdip (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) \<phi>"
    using root unfolding B_def n1_def gp_def e1_def .
  have cospos: "0 < cos \<phi>"
    using cosgt s2pos unfolding s2_def by linarith
  have phi_sq_gt: "lo\<^sup>2 < \<phi>\<^sup>2"
    using lopos phigtlo
    by (simp add: power_strict_mono)
  have lead_lower: "Rbound < A * \<phi>\<^sup>2 * cos \<phi>"
  proof -
    have "Rbound < A * lo\<^sup>2 * s2"
    proof -
      have "K\<^sup>2 < lo\<^sup>2"
        using Kpos Klo
        by (simp add: power_strict_mono)
      hence "A * K\<^sup>2 * s2 < A * lo\<^sup>2 * s2"
        using Apos s2pos by (intro mult_strict_left_mono mult_strict_right_mono) simp_all
      thus ?thesis
        using KR by linarith
    qed
    also have "\<dots> < A * \<phi>\<^sup>2 * cos \<phi>"
    proof -
      have "A * lo\<^sup>2 * s2 < A * \<phi>\<^sup>2 * s2"
        using Apos s2pos phi_sq_gt by (intro mult_strict_left_mono mult_strict_right_mono) simp_all
      also have "\<dots> < A * \<phi>\<^sup>2 * cos \<phi>"
        using Apos phi_sq_gt lopos phigtlo cosgt unfolding s2_def
        by (intro mult_strict_left_mono) (simp_all add: zero_less_power)
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  have lead_abs: "\<bar>- 2 * (real (CARD('n)) - 1) * gain_dip \<omega>
          * R_dip \<omega>0 \<omega>s \<omega> w * \<phi>\<^sup>2 * cos \<phi>\<bar>
      = A * \<phi>\<^sup>2 * cos \<phi>"
    unfolding A_def R_def n1_def
    using n1pos cospos
    by (simp add: abs_mult)
  have dominates: "single_bump_residual_bound TYPE('n) \<omega>0 \<omega>s \<omega> w
      < \<bar>- 2 * (real (CARD('n)) - 1) * gain_dip \<omega>
          * R_dip \<omega>0 \<omega>s \<omega> w * \<phi>\<^sup>2 * cos \<phi>\<bar>"
    unfolding Rbound_def[symmetric] lead_abs
    by (rule lead_lower)
  show ?thesis
    by (rule Xi_nonzero_witness_of_good_phase_radial
          [OF card2 detnz cnz e1nz gnz phinz root_expanded dominates])
qed

end
