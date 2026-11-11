theory Scratch_H0Counterexample
  imports "Applied_Math_M5_ActualD3Xi.Scratch_ActualD3Xi"
begin

section \<open>Why the H0core countability route cannot be the final D3 proof\<close>

text \<open>
  The actual retained D3 set requires \<open>A_cart \<noteq> 0\<close>.  Its auxiliary
  superset \<open>D3BadXG_H0core\<close> drops that condition.  This matters: at every
  nonzero wavevector a two-element antipodal configuration has zero array
  factor, is a degenerate angular critical point, and has both rank failures
  appearing in \<open>D3BadXG_H0core\<close>.  We formalize that obstruction below.
\<close>

definition antipodal_pair :: "real^2 \<Rightarrow> (real^2)^2" where
  "antipodal_pair c =
    vector [0, (pi / (c \<bullet> c)) *\<^sub>R c]"

lemma DM_paper_x_two_not_surj:
  fixes x :: "(real^2)^2" and c :: "real^2"
  shows "\<not> surj (DM_paper_x x c)"
proof
  assume surj: "surj (DM_paper_x x c)"
  have deriv:
      "((\<lambda>y. M_paper y c) has_derivative DM_paper_x x c) (at x)"
    using has_derivative_M_paper_x[where V=UNIV] by fastforce
  have lin: "linear (DM_paper_x x c)"
    using has_derivative_linear[OF deriv] .
  have dle:
      "dim (range (DM_paper_x x c))
        \<le> dim (UNIV :: ((real^2)^2) set)"
    using dim_image_le[OF lin, of "UNIV :: ((real^2)^2) set"]
    by simp
  have "dim (UNIV :: (complex^6) set)
        \<le> dim (UNIV :: ((real^2)^2) set)"
    using dle surj by simp
  then show False by simp
qed

lemma antipodal_pair_second_inner:
  assumes cnz: "c \<noteq> 0"
  shows "c \<bullet> vec_nth (antipodal_pair c) 2 = pi"
proof -
  have cc: "c \<bullet> c \<noteq> 0"
    using cnz by simp
  show ?thesis
    unfolding antipodal_pair_def
    using cc by (simp add: vector_2 inner_scaleR_right)
qed

lemma antipodal_pair_phase_1 [simp]:
  "phase c (antipodal_pair c) 1 = 1"
  unfolding phase_def antipodal_pair_def
  by (simp add: vector_2)

lemma antipodal_pair_phase_2 [simp]:
  assumes cnz: "c \<noteq> 0"
  shows "phase c (antipodal_pair c) 2 = -1"
  unfolding phase_def
  using antipodal_pair_second_inner[OF cnz]
  by (simp add: complex_eq_iff)

lemma antipodal_pair_Afun_zero [simp]:
  assumes cnz: "c \<noteq> 0"
  shows "Afun (antipodal_pair c) c = 0"
  unfolding Afun_def phase_def[symmetric]
  using antipodal_pair_phase_2[OF cnz]
  by (simp add: sum_2)

lemma antipodal_pair_Mcfun:
  assumes cnz: "c \<noteq> 0"
  shows "Mcfun (antipodal_pair c) c k =
    - complex_of_real
        (vec_nth ((pi / (c \<bullet> c)) *\<^sub>R c) k)"
proof -
  have ph2:
      "phase c (vector [0, (pi / (c \<bullet> c)) *\<^sub>R c] :: (real^2)^2) 2
        = -1"
    using antipodal_pair_phase_2[OF cnz]
    unfolding antipodal_pair_def .
  show ?thesis
    unfolding Mcfun_def phase_def[symmetric] antipodal_pair_def
    using ph2
    by (simp add: sum_2 vector_2 algebra_simps)
qed

lemma antipodal_pair_M1_moment:
  assumes cnz: "c \<noteq> 0"
  shows "M1_moment (antipodal_pair c) c =
    - complex_of_real
        (vec_nth ((pi / (c \<bullet> c)) *\<^sub>R c) 1)"
  using antipodal_pair_Mcfun[OF cnz, of 1]
  by (simp add: Mcfun_def M1_moment_def phase_def)

lemma antipodal_pair_M2_moment:
  assumes cnz: "c \<noteq> 0"
  shows "M2_moment (antipodal_pair c) c =
    - complex_of_real
        (vec_nth ((pi / (c \<bullet> c)) *\<^sub>R c) 2)"
  using antipodal_pair_Mcfun[OF cnz, of 2]
  by (simp add: Mcfun_def M2_moment_def phase_def)

lemma antipodal_pair_DM_first:
  assumes cnz: "c \<noteq> 0"
  shows "vec_nth (DM_paper_x (antipodal_pair c) c h) 1 =
    \<i> * complex_of_real (c \<bullet> (vec_nth h 2 - vec_nth h 1))"
proof -
  have ph2:
      "phase c (vector [0, (pi / (c \<bullet> c)) *\<^sub>R c] :: (real^2)^2) 2
        = -1"
    using antipodal_pair_phase_2[OF cnz]
    unfolding antipodal_pair_def .
  have cis2:
      "cis (- (c \<bullet> ((pi / (c \<bullet> c)) *\<^sub>R c))) = -1"
    using ph2 unfolding phase_def by (simp add: vector_2)
  show ?thesis
    unfolding DM_paper_x_components(1) DA_paper_x_def d_phase_def
      antipodal_pair_def
    using cis2
    by (simp add: sum_2 vector_2 inner_diff_right scaleR_conv_of_real
        algebra_simps)
qed

lemma gradU_antipodal_pair_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
      (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)) \<omega> = 0"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix j :: 2
  have m0:
      "vec_nth
        (M_paper (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>))
          (cvec_dip \<omega>0 \<omega>s \<omega>)) 1 = 0"
    using antipodal_pair_Afun_zero[OF cnz]
    by (simp add: A_moment_def Afun_def phase_def)
  have a0:
      "A_moment (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>))
        (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    using antipodal_pair_Afun_zero[OF cnz]
    by (simp add: A_moment_def Afun_def phase_def)
  show "vec_nth
      (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)) \<omega>) j
      = vec_nth (0::real^2) j"
    by (simp add: gradU_dip_component_moments m0 a0)
qed

lemma det_HessU_antipodal_pair_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
      (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)) \<omega>) = 0"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  have null: "Afun (antipodal_pair ?c) ?c = 0"
    by (rule antipodal_pair_Afun_zero[OF cnz])
  have cross:
      "Im (cnj (Mcfun (antipodal_pair ?c) ?c 1)
        * Mcfun (antipodal_pair ?c) ?c 2) = 0"
    using antipodal_pair_Mcfun[OF cnz, of 1]
      antipodal_pair_Mcfun[OF cnz, of 2]
    by simp
  have form:
      "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
          (antipodal_pair ?c) \<omega>)
       = 4 * (gain_dip \<omega>)\<^sup>2
           * (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
              * Im (cnj (Mcfun (antipodal_pair ?c) ?c 1)
                    * Mcfun (antipodal_pair ?c) ?c 2))\<^sup>2"
    by (rule det_HessU_at_null[OF null])
  show ?thesis
    using form cross
    by simp
qed

definition antipodal_grad_x_derivative ::
    "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^2 \<Rightarrow> real^2)"
  where
  "antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega> =
    (\<lambda>h. \<chi> j.
      dEjm
        (frechet_derivative gdip (at (vec_nth \<omega> 1))
          (vec_nth (axis j 1) 1))
        (gain_dip \<omega>)
        (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
        (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
        (M_paper
          (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>))
          (cvec_dip \<omega>0 \<omega>s \<omega>))
        (DM_paper_x
          (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>))
          (cvec_dip \<omega>0 \<omega>s \<omega>) h))"

lemma antipodal_grad_x_derivative_value:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega> h =
    (2 * gain_dip \<omega>
      * Im (vec_nth
          (DM_paper_x
            (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>))
            (cvec_dip \<omega>0 \<omega>s \<omega>) h) 1)) *\<^sub>R
    (\<chi> j.
      Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)
        \<bullet> ((pi /
          (cvec_dip \<omega>0 \<omega>s \<omega>
            \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)) *\<^sub>R
          cvec_dip \<omega>0 \<omega>s \<omega>))"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix j :: 2
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?q = "(pi / (?c \<bullet> ?c)) *\<^sub>R ?c"
  let ?x = "antipodal_pair ?c"
  have cc: "?c \<bullet> ?c \<noteq> 0"
    using cnz by simp
  have a0: "vec_nth (M_paper ?x ?c) 1 = 0"
    using antipodal_pair_Afun_zero[OF cnz]
    by (simp add: A_moment_def Afun_def phase_def)
  have m1: "vec_nth (M_paper ?x ?c) 2 =
      - complex_of_real (vec_nth ?q 1)"
    using antipodal_pair_M1_moment[OF cnz] by simp
  have m2: "vec_nth (M_paper ?x ?c) 3 =
      - complex_of_real (vec_nth ?q 2)"
    using antipodal_pair_M2_moment[OF cnz] by simp
  have dot:
      "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1
          * vec_nth ?q 1
       + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2
          * vec_nth ?q 2
       = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> ?q"
    by (simp add: inner_vec_def sum_2)
  show "vec_nth (antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega> h) j =
      vec_nth
        ((2 * gain_dip \<omega>
            * Im (vec_nth (DM_paper_x ?x ?c h) 1)) *\<^sub>R
          (\<chi> j.
            Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> ?q)) j"
    unfolding antipodal_grad_x_derivative_def vec_lambda_beta
      vector_scaleR_component dEjm_def real_scaleR_def
    apply (simp only: a0 m1 m2)
    apply (simp add: dot inner_vec_def sum_2 field_simps cc algebra_simps)
    done
qed

lemma antipodal_grad_x_derivative_has_derivative:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
      has_derivative antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega>)
      (at (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)))"
  unfolding antipodal_grad_x_derivative_def
  using has_derivative_gradU_dip_x_explicit[
      where V=UNIV
        and x="antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)"
        and \<omega>=\<omega> and \<omega>0=\<omega>0 and \<omega>s=\<omega>s]
  by fastforce

lemma scalar_multiple_map_into_real2_not_surj:
  fixes a :: "'a \<Rightarrow> real" and v :: "real^2"
  shows "\<not> surj (\<lambda>x. a x *\<^sub>R v)"
proof
  assume s: "surj (\<lambda>x. a x *\<^sub>R v)"
  show False
  proof (cases "v = 0")
    case True
    obtain x where hx: "(vector [1, 0] :: real^2) = a x *\<^sub>R v"
      using s unfolding surj_def by blast
    have "vec_nth (vector [1, 0] :: real^2) 1 =
        vec_nth (a x *\<^sub>R v) 1"
      using hx by simp
    then show False using True
      by (simp add: vector_2)
  next
    case False
    have pnz: "perp2 v \<noteq> 0"
      by (rule perp2_nz[OF False])
    obtain x where hx: "perp2 v = a x *\<^sub>R v"
      using s unfolding surj_def by blast
    have inner_eq:
        "(a x *\<^sub>R v) \<bullet> perp2 v = perp2 v \<bullet> perp2 v"
      using arg_cong[where f="\<lambda>z::real^2. z \<bullet> perp2 v", OF hx]
      by simp
    have lhs0: "(a x *\<^sub>R v) \<bullet> perp2 v = 0"
      by (simp add: inner_scaleR_left perp2_orth)
    have rhspos: "0 < perp2 v \<bullet> perp2 v"
      using pnz by (metis inner_gt_zero_iff)
    show False using inner_eq lhs0 rhspos by simp
  qed
qed

lemma antipodal_grad_x_derivative_not_surj:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "\<not> surj (antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega>)"
proof -
  let ?c = "cvec_dip \<omega>0 \<omega>s \<omega>"
  let ?x = "antipodal_pair ?c"
  let ?v = "(\<chi> j.
      Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)
        \<bullet> ((pi / (?c \<bullet> ?c)) *\<^sub>R ?c))"
  let ?a = "\<lambda>h::(real^2)^2.
      2 * gain_dip \<omega> * Im (vec_nth (DM_paper_x ?x ?c h) 1)"
  have eq:
      "antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega>
        = (\<lambda>h. ?a h *\<^sub>R ?v)"
  proof (rule ext)
    fix h :: "(real^2)^2"
    show "antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega> h
        = ?a h *\<^sub>R ?v"
      by (rule antipodal_grad_x_derivative_value[OF cnz])
  qed
  show ?thesis
    unfolding eq
    by (rule scalar_multiple_map_into_real2_not_surj)
qed

lemma antipodal_pair_has_no_surjective_grad_x_derivative:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "\<not> (\<exists>Dx.
      ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx)
        (at (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)))
      \<and> surj Dx)"
proof
  assume "\<exists>Dx.
      ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx)
        (at (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)))
      \<and> surj Dx"
  then obtain Dx where dx:
      "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative Dx)
        (at (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)))"
    and sx: "surj Dx"
    by blast
  have hd:
      "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
        has_derivative antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega>)
        (at (antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)))"
    by (rule antipodal_grad_x_derivative_has_derivative)
  have "Dx = antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega>"
    by (rule has_derivative_unique[OF dx hd])
  then have "surj (antipodal_grad_x_derivative \<omega>0 \<omega>s \<omega>)"
    using sx by simp
  then show False
    using antipodal_grad_x_derivative_not_surj[OF cnz] by contradiction
qed

lemma antipodal_pair_in_D3BadXG_H0core:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)
      \<in> (D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^2) set)"
  unfolding D3BadXG_H0core_def
  using cnz gradU_antipodal_pair_zero[OF cnz]
    det_HessU_antipodal_pair_zero[OF cnz]
    DM_paper_x_two_not_surj[
      where x="antipodal_pair (cvec_dip \<omega>0 \<omega>s \<omega>)"
        and c="cvec_dip \<omega>0 \<omega>s \<omega>"]
    antipodal_pair_has_no_surjective_grad_x_derivative[OF cnz]
  by blast

lemma robust4_outer_arc_cvec_nonzero:
  fixes \<omega> :: "real^2" and y :: real
  assumes wA: "\<omega> \<in> robust4_horizontal_arc y"
    and outer: "y \<in> {-pi, pi}"
  shows "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
proof
  assume cz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
  have fac:
      "d3_s2_global_factor
        (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
    by (rule robust4_outer_arc_d3_s2_global_factor_nonzero[OF wA outer])
  show False
    using fac cz
    unfolding d3_s2_global_factor_def
    by (simp add: perp2_def inner_vec_def sum_2 vector_2)
qed

lemma robust4_outer_arc_subset_H0core_bad_angles_two:
  assumes outer: "y \<in> {-pi, pi}"
  shows "robust4_horizontal_arc y \<subseteq>
      H0coreArc_bad_angles (UNIV :: ((real^2)^2) set)
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc y)"
proof
  fix \<omega>
  assume wA: "\<omega> \<in> robust4_horizontal_arc y"
  have cnz:
      "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
    by (rule robust4_outer_arc_cvec_nonzero[OF wA outer])
  have bad:
      "antipodal_pair
          (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
        \<in> (D3BadXG_H0core
          (vector [pi / 2, 0]) (vector [0, 0]) {\<omega>}
          :: ((real^2)^2) set)"
    by (rule antipodal_pair_in_D3BadXG_H0core[OF cnz])
  show "\<omega> \<in> H0coreArc_bad_angles (UNIV :: ((real^2)^2) set)
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)"
    unfolding H0coreArc_bad_angles_def
    using wA bad by blast
qed

lemma robust4_outer_arc_H0core_bad_angles_two_eq:
  assumes outer: "y \<in> {-pi, pi}"
  shows "H0coreArc_bad_angles (UNIV :: ((real^2)^2) set)
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)
    = robust4_horizontal_arc y"
proof
  show "H0coreArc_bad_angles (UNIV :: ((real^2)^2) set)
      (vector [pi / 2, 0]) (vector [0, 0])
      (robust4_horizontal_arc y)
      \<subseteq> robust4_horizontal_arc y"
    unfolding H0coreArc_bad_angles_def by blast
  show "robust4_horizontal_arc y
      \<subseteq> H0coreArc_bad_angles (UNIV :: ((real^2)^2) set)
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc y)"
    by (rule robust4_outer_arc_subset_H0core_bad_angles_two[OF outer])
qed

lemma real_closed_interval_not_top1_countable:
  fixes a b :: real
  assumes lt: "a < b"
  shows "\<not> Top1_Ch3.countable {a..b}"
proof
  assume cnt: "Top1_Ch3.countable {a..b}"
  have hol_cnt: "Countable_Set.countable {a..b}"
    using cnt
    unfolding Top1_Ch3.countable_def Countable_Set.countable_def
    by blast
  have "uncountable {a..b}"
    using lt by (simp add: uncountable_closed_interval)
  then show False using hol_cnt by simp
qed

lemma robust4_horizontal_arc_not_countable:
  "\<not> Top1_Ch3.countable (robust4_horizontal_arc y)"
proof
  assume cnt: "Top1_Ch3.countable (robust4_horizontal_arc y)"
  obtain f :: "real^2 \<Rightarrow> nat" where inj:
      "inj_on f (robust4_horizontal_arc y)"
    using cnt unfolding Top1_Ch3.countable_def by blast
  let ?I = "{pi / 4..3 * pi / 4}"
  have inj_comp:
      "inj_on (\<lambda>t::real. f (vector [t, y])) ?I"
  proof (rule inj_onI)
    fix a b :: real
    assume aI: "a \<in> ?I" and bI: "b \<in> ?I"
      and eq: "f (vector [a, y] :: real^2)
        = f (vector [b, y] :: real^2)"
    have va: "(vector [a, y] :: real^2) \<in> robust4_horizontal_arc y"
      using aI unfolding robust4_horizontal_arc_def by blast
    have vb: "(vector [b, y] :: real^2) \<in> robust4_horizontal_arc y"
      using bI unfolding robust4_horizontal_arc_def by blast
    have veq: "(vector [a, y] :: real^2) = vector [b, y]"
      using inj va vb eq unfolding inj_on_def by blast
    have "vec_nth (vector [a, y] :: real^2) 1
        = vec_nth (vector [b, y] :: real^2) 1"
      using veq by simp
    then show "a = b" by (simp add: vector_2)
  qed
  have int_cnt: "Top1_Ch3.countable ?I"
    unfolding Top1_Ch3.countable_def
    using inj_comp by blast
  have lt: "pi / 4 < 3 * pi / 4"
    using pi_gt_zero by linarith
  show False
    using int_cnt real_closed_interval_not_top1_countable[OF lt]
    by contradiction
qed

theorem H0coreArc_bad_angles_outer_robust4_not_countable_two:
  assumes outer: "y \<in> {-pi, pi}"
  shows "\<not> Top1_Ch3.countable
      (H0coreArc_bad_angles (UNIV :: ((real^2)^2) set)
        (vector [pi / 2, 0]) (vector [0, 0])
        (robust4_horizontal_arc y))"
  unfolding robust4_outer_arc_H0core_bad_angles_two_eq[OF outer]
  by (rule robust4_horizontal_arc_not_countable)

end
