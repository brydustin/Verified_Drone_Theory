section \<open>The three equations at a point of the residual\<close>

theory Residual_Equations
  imports
    Applied_Math_Strata.Steering_Singular_Stratum
    Applied_Math_Strata.Regular_Stratum
    Residual_Phase_Equation
begin

subsection \<open>The residual set\<close>

definition residual_set :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "residual_set \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
    \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
    \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
    \<and> matrix_det (jacobian (cvec_dip \<omega>0 \<omega>s) (at \<omega>)) \<noteq> 0
    \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
    \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"

text \<open>At a point of @{const residual_set} where antenna \<open>m\<close> is not
  phase-aligned, the phases \<open>t\<^sub>a = c \<bullet> x\<^sub>a\<close> and the perpendicular coordinates
  \<open>u\<^sub>a = perp2 c \<bullet> x\<^sub>a\<close> satisfy three equations.  Nothing here depends on the steering angles.\<close>

subsection \<open>Slots and planar algebra\<close>

definition slot :: "'n::finite \<Rightarrow> real^2 \<Rightarrow> (real^2)^'n" where
  "slot j v = (\<chi> m. if m = j then v else 0)"

lemma slot_nth: "vec_nth (slot j v) n = (if n = j then v else 0)"
  by (simp add: slot_def)

definition perp2 :: "real^2 \<Rightarrow> real^2" where
  "perp2 c = vector [- vec_nth c 2, vec_nth c 1]"

lemma perp2_nth: "vec_nth (perp2 c) 1 = - vec_nth c 2" "vec_nth (perp2 c) 2 = vec_nth c 1"
  by (simp_all add: perp2_def)

definition cross2 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "cross2 a b = vec_nth a 1 * vec_nth b 2 - vec_nth a 2 * vec_nth b 1"

lemma inner2: "a \<bullet> b = vec_nth a 1 * vec_nth b 1 + vec_nth a 2 * vec_nth b 2" for a b :: "real^2"
  by (simp add: inner_vec_def sum_2)

lemma inner_perp2_self: "c \<bullet> perp2 c = 0"
  by (simp add: inner2 perp2_nth)

lemma parallel_of_inner_perp2_zero:
  fixes c L :: "real^2"
  assumes cnz: "c \<noteq> 0" and orth: "L \<bullet> perp2 c = 0"
  shows "L = ((L \<bullet> c) / (c \<bullet> c)) *\<^sub>R c"
proof -
  have cc: "c \<bullet> c \<noteq> 0"
    using cnz by simp
  have e: "vec_nth L 2 * vec_nth c 1 = vec_nth L 1 * vec_nth c 2"
    using orth by (simp add: inner2 perp2_nth)
  have e': "vec_nth L 1 * vec_nth c 2 = vec_nth L 2 * vec_nth c 1"
    using e by simp
  have "vec_nth L 1 * (c \<bullet> c)
      = vec_nth L 1 * (vec_nth c 1 * vec_nth c 1) + (vec_nth L 1 * vec_nth c 2) * vec_nth c 2"
    by (simp add: inner2 algebra_simps)
  also have "\<dots> = vec_nth L 1 * (vec_nth c 1 * vec_nth c 1) + (vec_nth L 2 * vec_nth c 1) * vec_nth c 2"
    by (simp only: e')
  also have "\<dots> = (L \<bullet> c) * vec_nth c 1"
    by (simp add: inner2 algebra_simps)
  finally have 1: "vec_nth L 1 * (c \<bullet> c) = (L \<bullet> c) * vec_nth c 1" .
  have "vec_nth L 2 * (c \<bullet> c)
      = (vec_nth L 2 * vec_nth c 1) * vec_nth c 1 + vec_nth L 2 * (vec_nth c 2 * vec_nth c 2)"
    by (simp add: inner2 algebra_simps)
  also have "\<dots> = (vec_nth L 1 * vec_nth c 2) * vec_nth c 1 + vec_nth L 2 * (vec_nth c 2 * vec_nth c 2)"
    by (simp only: e)
  also have "\<dots> = (L \<bullet> c) * vec_nth c 2"
    by (simp add: inner2 algebra_simps)
  finally have 2: "vec_nth L 2 * (c \<bullet> c) = (L \<bullet> c) * vec_nth c 2" .
  show ?thesis
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 2
    show "vec_nth L i = vec_nth (((L \<bullet> c) / (c \<bullet> c)) *\<^sub>R c) i"
      using 1 2 cc exhaust_2[of i] by (auto simp: field_simps)
  qed
qed

lemma cramer_first:
  fixes c a b :: "real^2"
  assumes "e1 *\<^sub>R a + e2 *\<^sub>R b = k *\<^sub>R c"
  shows "e1 * cross2 a b = k * cross2 c b"
proof -
  have 1: "e1 * vec_nth a 1 + e2 * vec_nth b 1 = k * vec_nth c 1"
    using arg_cong[OF assms, of "\<lambda>v. vec_nth v 1"] by simp
  have 2: "e1 * vec_nth a 2 + e2 * vec_nth b 2 = k * vec_nth c 2"
    using arg_cong[OF assms, of "\<lambda>v. vec_nth v 2"] by simp
  have "e1 * cross2 a b
      = (e1 * vec_nth a 1 + e2 * vec_nth b 1) * vec_nth b 2
        - (e1 * vec_nth a 2 + e2 * vec_nth b 2) * vec_nth b 1"
    by (simp add: cross2_def algebra_simps)
  also have "\<dots> = k * vec_nth c 1 * vec_nth b 2 - k * vec_nth c 2 * vec_nth b 1"
    by (simp only: 1 2)
  finally show ?thesis
    by (simp add: cross2_def algebra_simps)
qed

lemma cramer_combination:
  fixes w a b :: "real^2"
  shows "cross2 w b *\<^sub>R a + cross2 a w *\<^sub>R b = cross2 a b *\<^sub>R w"
proof -
  show ?thesis
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 2
    show "vec_nth (cross2 w b *\<^sub>R a + cross2 a w *\<^sub>R b) i = vec_nth (cross2 a b *\<^sub>R w) i"
      using exhaust_2[of i] by (auto simp: cross2_def algebra_simps)
  qed
qed

lemma matrix_det_cross2:
  fixes f :: "real^2 \<Rightarrow> real^2"
  shows "matrix_det (matrix f) = cross2 (f (axis 1 1)) (f (axis 2 1))"
  by (simp add: det_2 matrix_def cross2_def)

lemma not_surj_linear_cokernel:
  fixes L :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes lin: "linear L" and nsurj: "\<not> surj L"
  shows "\<exists>ell::'b. ell \<noteq> 0 \<and> (\<forall>h. ell \<bullet> L h = 0)"
proof -
  have "surj (adjoint (adjoint L)) = inj (adjoint L)"
    by (rule surj_adjoint_iff_inj[OF adjoint_linear[OF lin]])
  then have "\<not> inj (adjoint L)"
    using nsurj by (simp add: adjoint_adjoint[OF lin])
  then obtain ell :: 'b where ellnz: "ell \<noteq> 0" and adj0: "adjoint L ell = 0"
    unfolding linear_injective_0[OF adjoint_linear[OF lin]] by blast
  have "ell \<bullet> L h = 0" for h
    using adjoint_clauses(2)[OF lin, of ell h] adj0 by simp
  then show ?thesis
    using ellnz by blast
qed

subsection \<open>Moment derivatives in a slot direction\<close>

lemma d_phase_slot:
  "d_phase c x (slot j v) n
     = (if n = j then -(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))) else 0)"
  by (simp add: d_phase_def slot_nth)

lemma DA_moment_slot:
  "DA_moment x c (slot j v) = -(c \<bullet> v) *\<^sub>R (\<i> * phase c x j)"
proof -
  have "DA_moment x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j then -(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))) else 0)"
    unfolding DA_moment_def by (rule sum.cong[OF refl]) (simp add: d_phase_slot)
  also have "\<dots> = -(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j)))"
    by (simp add: sum.delta')
  finally show ?thesis
    by (simp add: phase_def)
qed

lemma DM1_moment_slot:
  "DM1_moment x c (slot j v)
     = of_real (vec_nth v 1) * phase c x j
       + of_real (vec_nth (vec_nth x j) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x j))"
proof -
  have "DM1_moment x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j
          then of_real (vec_nth v 1) * phase c x n
             + of_real (vec_nth (vec_nth x n) 1)
                 * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))))
          else 0)"
    unfolding DM1_moment_def
    by (rule sum.cong[OF refl]) (simp add: d_phase_slot slot_nth)
  also have "\<dots> = of_real (vec_nth v 1) * phase c x j
       + of_real (vec_nth (vec_nth x j) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j))))"
    by (simp add: sum.delta')
  finally show ?thesis
    by (simp add: phase_def)
qed

lemma DM2_moment_slot:
  "DM2_moment x c (slot j v)
     = of_real (vec_nth v 2) * phase c x j
       + of_real (vec_nth (vec_nth x j) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x j))"
proof -
  have "DM2_moment x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j
          then of_real (vec_nth v 2) * phase c x n
             + of_real (vec_nth (vec_nth x n) 2)
                 * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))))
          else 0)"
    unfolding DM2_moment_def
    by (rule sum.cong[OF refl]) (simp add: d_phase_slot slot_nth)
  also have "\<dots> = of_real (vec_nth v 2) * phase c x j
       + of_real (vec_nth (vec_nth x j) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j))))"
    by (simp add: sum.delta')
  finally show ?thesis
    by (simp add: phase_def)
qed

text \<open>The slot value of the \<open>x\<close>-derivative of one gradient component, for an arbitrary gain
  derivative \<open>p\<close> and steering column \<open>\<gamma>\<close>.\<close>

lemma dEjm_slot_value:
  fixes c v \<gamma> :: "real^2"
  shows "dEjm p g (vec_nth \<gamma> 1) (vec_nth \<gamma> 2) (moment_map x c) (Dmoment_map x c (slot m v))
       = p * (2 * (c \<bullet> v) * Im (cnj (A_moment x c) * phase c x m))
       + g * (2 * (c \<bullet> v)
                * (vec_nth \<gamma> 1 * Re (cnj (phase c x m) * M1_moment x c)
                  + vec_nth \<gamma> 2 * Re (cnj (phase c x m) * M2_moment x c))
            + 2 * (\<gamma> \<bullet> v) * Im (cnj (A_moment x c) * phase c x m)
            - 2 * (c \<bullet> v) * (\<gamma> \<bullet> vec_nth x m)
                * Re (cnj (A_moment x c) * phase c x m))"
proof -
  have d1: "vec_nth (Dmoment_map x c (slot m v)) 1 = -(c \<bullet> v) *\<^sub>R (\<i> * phase c x m)"
    by (simp add: Dmoment_map_def DA_moment_slot)
  have d2: "vec_nth (Dmoment_map x c (slot m v)) 2
      = of_real (vec_nth v 1) * phase c x m
        + of_real (vec_nth (vec_nth x m) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))"
    by (simp add: Dmoment_map_def DM1_moment_slot)
  have d3: "vec_nth (Dmoment_map x c (slot m v)) 3
      = of_real (vec_nth v 2) * phase c x m
        + of_real (vec_nth (vec_nth x m) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x m))"
    by (simp add: Dmoment_map_def DM2_moment_slot)
  show ?thesis
    unfolding dEjm_def d1 d2 d3
    by (simp add: inner2 algebra_simps)
qed

lemma dEjm_combination:
  "e1 * dEjm p1 g a1 a2 M d + e2 * dEjm p2 g b1 b2 M d
     = dEjm (e1 * p1 + e2 * p2) g (e1 * a1 + e2 * b1) (e1 * a2 + e2 * b2) M d"
  by (simp add: dEjm_def algebra_simps)

subsection \<open>Moments in phase coordinates\<close>

definition phase_coords :: "real^2 \<Rightarrow> (real^2)^'n \<Rightarrow> real^'n" where
  "phase_coords c x = (\<chi> a. c \<bullet> vec_nth x a)"

definition perp_coords :: "real^2 \<Rightarrow> (real^2)^'n \<Rightarrow> real^'n" where
  "perp_coords c x = (\<chi> a. perp2 c \<bullet> vec_nth x a)"

lemma phase_parts:
  "Re (phase c x a) = cos (vec_nth (phase_coords c x) a)"
  "Im (phase c x a) = - sin (vec_nth (phase_coords c x) a)"
  by (simp_all add: phase_def phase_coords_def)

lemma A_moment_parts:
  "Re (A_moment x c) = phase_cos_sum (phase_coords c x)"
  "Im (A_moment x c) = - phase_sin_sum (phase_coords c x)"
  by (simp_all add: A_moment_def phase_cos_sum_def phase_sin_sum_def phase_parts sum_negf)

lemma weighted_moment_parts:
  fixes w :: "real^2" and x :: "(real^2)^'n"
  shows "Re (of_real (vec_nth w 1) * M1_moment x c + of_real (vec_nth w 2) * M2_moment x c)
       = (\<Sum>a\<in>UNIV. (w \<bullet> vec_nth x a) * cos (vec_nth (phase_coords c x) a))"
    and "Im (of_real (vec_nth w 1) * M1_moment x c + of_real (vec_nth w 2) * M2_moment x c)
       = - (\<Sum>a\<in>UNIV. (w \<bullet> vec_nth x a) * sin (vec_nth (phase_coords c x) a))"
proof -
  have "Re (of_real (vec_nth w 1) * M1_moment x c + of_real (vec_nth w 2) * M2_moment x c)
      = (\<Sum>a\<in>UNIV. vec_nth w 1 * (vec_nth (vec_nth x a) 1 * cos (vec_nth (phase_coords c x) a))
                   + vec_nth w 2 * (vec_nth (vec_nth x a) 2 * cos (vec_nth (phase_coords c x) a)))"
    by (simp add: M1_moment_def M2_moment_def phase_parts sum.distrib sum_distrib_left)
  also have "\<dots> = (\<Sum>a\<in>UNIV. (w \<bullet> vec_nth x a) * cos (vec_nth (phase_coords c x) a))"
    by (rule sum.cong) (simp_all add: inner2 algebra_simps)
  finally show "Re (of_real (vec_nth w 1) * M1_moment x c + of_real (vec_nth w 2) * M2_moment x c)
       = (\<Sum>a\<in>UNIV. (w \<bullet> vec_nth x a) * cos (vec_nth (phase_coords c x) a))" .
  have split: "(\<Sum>a\<in>UNIV. (w \<bullet> vec_nth x a) * f a)
      = (\<Sum>a\<in>UNIV. vec_nth w 1 * (vec_nth (vec_nth x a) 1 * f a))
        + (\<Sum>a\<in>UNIV. vec_nth w 2 * (vec_nth (vec_nth x a) 2 * f a))" for f :: "'n \<Rightarrow> real"
    unfolding sum.distrib[symmetric] by (rule sum.cong) (simp_all add: inner2 algebra_simps)
  show "Im (of_real (vec_nth w 1) * M1_moment x c + of_real (vec_nth w 2) * M2_moment x c)
       = - (\<Sum>a\<in>UNIV. (w \<bullet> vec_nth x a) * sin (vec_nth (phase_coords c x) a))"
    unfolding split
    by (simp add: M1_moment_def M2_moment_def phase_parts sum_distrib_left sum_negf)
qed

text \<open>The quantities that occur in the slot formula and in the gradient, in terms of the
  functions of @{theory Applied_Math_Residual.Residual_Phase_Equation}.\<close>

lemma Im_A_phase:
  "Im (cnj (A_moment x c) * phase c x a) = - res_s a (phase_coords c x)"
  by (simp add: res_s_def A_moment_parts phase_parts algebra_simps)

lemma Re_A_phase:
  "Re (cnj (A_moment x c) * phase c x a)
     = cos (vec_nth (phase_coords c x) a) * phase_cos_sum (phase_coords c x)
       + sin (vec_nth (phase_coords c x) a) * phase_sin_sum (phase_coords c x)"
  by (simp add: A_moment_parts phase_parts algebra_simps)

lemma cmod_A_sq: "(cmod (A_moment x c))\<^sup>2 = res_W (phase_coords c x)"
  by (simp add: cmod_power2 res_W_def A_moment_parts)

lemma lin_sums_coords:
  "(\<Sum>a\<in>UNIV. (c \<bullet> vec_nth x a) * cos (vec_nth (phase_coords c x) a))
     = phase_lin_cos_sum (phase_coords c x)"
  "(\<Sum>a\<in>UNIV. (c \<bullet> vec_nth x a) * sin (vec_nth (phase_coords c x) a))
     = phase_lin_sin_sum (phase_coords c x)"
  by (simp_all add: phase_lin_cos_sum_def phase_lin_sin_sum_def phase_coords_def)

lemma Re_phase_cmoment:
  "vec_nth c 1 * Re (cnj (phase c x a) * M1_moment x c)
     + vec_nth c 2 * Re (cnj (phase c x a) * M2_moment x c)
   = cos (vec_nth (phase_coords c x) a) * phase_lin_cos_sum (phase_coords c x)
     + sin (vec_nth (phase_coords c x) a) * phase_lin_sin_sum (phase_coords c x)"
proof -
  let ?Z = "of_real (vec_nth c 1) * M1_moment x c + of_real (vec_nth c 2) * M2_moment x c"
  have "vec_nth c 1 * Re (cnj (phase c x a) * M1_moment x c)
        + vec_nth c 2 * Re (cnj (phase c x a) * M2_moment x c)
      = Re (phase c x a) * Re ?Z + Im (phase c x a) * Im ?Z"
    by (simp add: algebra_simps)
  then show ?thesis
    unfolding weighted_moment_parts lin_sums_coords by (simp add: phase_parts)
qed

lemma Re_A_cmoment:
  "Re (cnj (A_moment x c)
        * ((- \<i>) * (of_real (vec_nth c 1) * M1_moment x c + of_real (vec_nth c 2) * M2_moment x c)))
   = - res_P (phase_coords c x) / 2"
proof -
  let ?Z = "of_real (vec_nth c 1) * M1_moment x c + of_real (vec_nth c 2) * M2_moment x c"
  have "Re (cnj (A_moment x c) * ((- \<i>) * ?Z))
      = Re (A_moment x c) * Im ?Z - Im (A_moment x c) * Re ?Z"
    by (simp add: algebra_simps)
  then show ?thesis
    unfolding weighted_moment_parts lin_sums_coords
    by (simp add: res_P_def A_moment_parts algebra_simps)
qed

lemma Re_A_perpmoment:
  "Re (cnj (A_moment x c)
        * ((- \<i>) * (of_real (vec_nth (perp2 c) 1) * M1_moment x c
                    + of_real (vec_nth (perp2 c) 2) * M2_moment x c)))
   = - (\<Sum>b\<in>UNIV. vec_nth (perp_coords c x) b * res_s b (phase_coords c x))"
proof -
  let ?t = "phase_coords c x" and ?u = "perp_coords c x"
  let ?Z = "of_real (vec_nth (perp2 c) 1) * M1_moment x c
            + of_real (vec_nth (perp2 c) 2) * M2_moment x c"
  have u: "perp2 c \<bullet> vec_nth x a = vec_nth ?u a" for a
    by (simp add: perp_coords_def)
  have "Re (cnj (A_moment x c) * ((- \<i>) * ?Z))
      = Re (A_moment x c) * Im ?Z - Im (A_moment x c) * Re ?Z"
    by (simp add: algebra_simps)
  also have "\<dots> = - phase_cos_sum ?t * (\<Sum>b\<in>UNIV. vec_nth ?u b * sin (vec_nth ?t b))
                  + phase_sin_sum ?t * (\<Sum>b\<in>UNIV. vec_nth ?u b * cos (vec_nth ?t b))"
    unfolding weighted_moment_parts u by (simp add: A_moment_parts)
  also have "\<dots> = - (\<Sum>b\<in>UNIV. phase_cos_sum ?t * (vec_nth ?u b * sin (vec_nth ?t b))
                          - phase_sin_sum ?t * (vec_nth ?u b * cos (vec_nth ?t b)))"
    by (simp add: sum_subtractf sum_distrib_left sum_negf)
  also have "(\<Sum>b\<in>UNIV. phase_cos_sum ?t * (vec_nth ?u b * sin (vec_nth ?t b))
                          - phase_sin_sum ?t * (vec_nth ?u b * cos (vec_nth ?t b)))
           = (\<Sum>b\<in>UNIV. vec_nth ?u b * res_s b ?t)"
    by (rule sum.cong) (simp_all add: res_s_def algebra_simps)
  finally show ?thesis .
qed

subsection \<open>Combinations of the gradient and of its \<open>x\<close>-derivative\<close>

lemma frechet_gdip_axis:
  "frechet_derivative gdip (at \<theta>) (vec_nth (axis (1::2) (1::real)) 1) = frechet_derivative gdip (at \<theta>) 1"
  "frechet_derivative gdip (at \<theta>) (vec_nth (axis (2::2) (1::real)) 1) = 0"
  by (simp_all add: axis_def frechet_gdip_zero_arg)

text \<open>For a covector \<open>e\<close> write \<open>L = e\<^sub>1 \<gamma>\<^sub>1 + e\<^sub>2 \<gamma>\<^sub>2\<close>.\<close>

lemma gradU_combination:
  fixes x :: "(real^2)^'n" and e \<omega> \<omega>0 \<omega>s :: "real^2"
  defines "L \<equiv> vec_nth e 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) + vec_nth e 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  shows "e \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>
       = vec_nth e 1 * frechet_derivative gdip (at (vec_nth \<omega> 1)) 1
           * (cmod (A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>)))\<^sup>2
         + gain_dip \<omega> * (2 * Re (cnj (A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>))
             * ((- \<i>) * (of_real (vec_nth L 1) * M1_moment x (cvec_dip \<omega>0 \<omega>s \<omega>)
                         + of_real (vec_nth L 2) * M2_moment x (cvec_dip \<omega>0 \<omega>s \<omega>)))))"
  unfolding inner2 L_def
  by (simp add: gradU_dip_component_moments frechet_gdip_axis algebra_simps)

lemma gradU_x_derivative_slot_combination:
  fixes x :: "(real^2)^'n" and e v \<omega> \<omega>0 \<omega>s :: "real^2"
  defines "c \<equiv> cvec_dip \<omega>0 \<omega>s \<omega>"
    and "L \<equiv> vec_nth e 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) + vec_nth e 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  shows "e \<bullet> (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (moment_map x c) (Dmoment_map x c (slot a v)))
       = vec_nth e 1 * frechet_derivative gdip (at (vec_nth \<omega> 1)) 1
           * (2 * (c \<bullet> v) * Im (cnj (A_moment x c) * phase c x a))
         + gain_dip \<omega> * (2 * (c \<bullet> v)
                * (vec_nth L 1 * Re (cnj (phase c x a) * M1_moment x c)
                  + vec_nth L 2 * Re (cnj (phase c x a) * M2_moment x c))
            + 2 * (L \<bullet> v) * Im (cnj (A_moment x c) * phase c x a)
            - 2 * (c \<bullet> v) * (L \<bullet> vec_nth x a)
                * Re (cnj (A_moment x c) * phase c x a))"
proof -
  let ?p = "\<lambda>j::2. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j (1::real)) 1)"
  let ?g = "\<lambda>j::2. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)"
  let ?d = "\<lambda>j::2. dEjm (?p j) (gain_dip \<omega>) (vec_nth (?g j) 1) (vec_nth (?g j) 2)
                  (moment_map x c) (Dmoment_map x c (slot a v))"
  have "e \<bullet> (\<chi> j. ?d j) = vec_nth e 1 * ?d 1 + vec_nth e 2 * ?d 2"
    by (simp add: inner2)
  also have "\<dots> = dEjm (vec_nth e 1 * ?p 1 + vec_nth e 2 * ?p 2) (gain_dip \<omega>)
                     (vec_nth L 1) (vec_nth L 2) (moment_map x c) (Dmoment_map x c (slot a v))"
    unfolding dEjm_combination L_def by simp
  also have "vec_nth e 1 * ?p 1 + vec_nth e 2 * ?p 2
           = vec_nth e 1 * frechet_derivative gdip (at (vec_nth \<omega> 1)) 1"
    by (simp add: frechet_gdip_axis)
  finally show ?thesis
    unfolding dEjm_slot_value by simp
qed

subsection \<open>The equations\<close>

theorem residual_point_equations:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s c \<gamma>1 \<gamma>2 :: "real^2" and t u :: "real^'n" and m :: 'n
  assumes c: "c = cvec_dip \<omega>0 \<omega>s \<omega>"
    and g1: "\<gamma>1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)" and g2: "\<gamma>2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
    and t: "t = phase_coords c x" and u: "u = perp_coords c x"
    and gd: "gd = frechet_derivative gdip (at (vec_nth \<omega> 1)) 1"
    and grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and nsurj: "\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)"
    and cnz: "c \<noteq> 0" and det: "cross2 \<gamma>1 \<gamma>2 \<noteq> 0" and gnz: "gain_dip \<omega> \<noteq> 0"
    and nal: "res_s m t \<noteq> 0"
  shows "res_f m t = 0"
    and "gd * res_s m t * cross2 c \<gamma>2 + gain_dip \<omega> * (res_s m t + res_q m t) * cross2 \<gamma>1 \<gamma>2 = 0"
    and "2 * gain_dip \<omega> * cross2 \<gamma>1 \<gamma>2 * (\<Sum>b\<in>UNIV. vec_nth u b * res_s b t)
         = gd * cross2 (perp2 c) \<gamma>2 * res_W t"
proof -
  define g where "g = gain_dip \<omega>"
  define Dx where "Dx = (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (moment_map x (cvec_dip \<omega>0 \<omega>s \<omega>)) (Dmoment_map x (cvec_dip \<omega>0 \<omega>s \<omega>) h))"
  have der: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x)"
    unfolding Dx_def by (rule has_derivative_gradU_dip_x_explicit)
  have nsurjD: "\<not> surj Dx"
    using nsurj der by blast
  have linD: "linear Dx"
    using der has_derivative_linear by blast
  obtain ell :: "real^2" where ellnz: "ell \<noteq> 0" and ann: "\<And>h. ell \<bullet> Dx h = 0"
    using not_surj_linear_cokernel[OF linD nsurjD] by blast
  define L where "L = vec_nth ell 1 *\<^sub>R \<gamma>1 + vec_nth ell 2 *\<^sub>R \<gamma>2"
  define P where "P = vec_nth ell 1 * gd"

  text \<open>The cokernel covector annihilates every slot derivative.\<close>
  have slot0: "P * (2 * (c \<bullet> v) * Im (cnj (A_moment x c) * phase c x a))
         + g * (2 * (c \<bullet> v)
                * (vec_nth L 1 * Re (cnj (phase c x a) * M1_moment x c)
                  + vec_nth L 2 * Re (cnj (phase c x a) * M2_moment x c))
            + 2 * (L \<bullet> v) * Im (cnj (A_moment x c) * phase c x a)
            - 2 * (c \<bullet> v) * (L \<bullet> vec_nth x a)
                * Re (cnj (A_moment x c) * phase c x a)) = 0" for a v
    using ann[of "slot a v"]
    unfolding Dx_def gradU_x_derivative_slot_combination
    by (simp add: P_def L_def g_def c g1 g2 gd)

  text \<open>Perpendicular slot of the witness: \<open>L\<close> is parallel to \<open>c\<close>.\<close>
  have ImA: "Im (cnj (A_moment x c) * phase c x a) = - res_s a t" for a
    unfolding t by (rule Im_A_phase)
  have ReA: "Re (cnj (A_moment x c) * phase c x a)
      = cos (vec_nth t a) * phase_cos_sum t + sin (vec_nth t a) * phase_sin_sum t" for a
    unfolding t by (rule Re_A_phase)
  have "g * (2 * (L \<bullet> perp2 c) * (- res_s m t)) = 0"
    using slot0[of "perp2 c" m] unfolding ImA inner_perp2_self by simp
  then have Lperp: "L \<bullet> perp2 c = 0"
    using gnz nal by (simp add: g_def)
  define k where "k = (L \<bullet> c) / (c \<bullet> c)"
  have Lk: "L = k *\<^sub>R c"
    unfolding k_def by (rule parallel_of_inner_perp2_zero[OF cnz Lperp])
  have ell1: "vec_nth ell 1 * cross2 \<gamma>1 \<gamma>2 = k * cross2 c \<gamma>2"
    by (rule cramer_first) (use Lk in \<open>simp add: L_def\<close>)
  have knz: "k \<noteq> 0"
  proof
    assume "k = 0"
    then have L0: "vec_nth ell 1 *\<^sub>R \<gamma>1 + vec_nth ell 2 *\<^sub>R \<gamma>2 = 0 *\<^sub>R c"
      using Lk by (simp add: L_def)
    have "vec_nth ell 1 * cross2 \<gamma>1 \<gamma>2 = 0"
      using cramer_first[OF L0] by simp
    moreover have "vec_nth ell 2 *\<^sub>R \<gamma>2 + vec_nth ell 1 *\<^sub>R \<gamma>1 = 0 *\<^sub>R c"
      using L0 by (simp add: add.commute)
    then have "vec_nth ell 2 * cross2 \<gamma>2 \<gamma>1 = 0 * cross2 c \<gamma>1"
      by (rule cramer_first)
    moreover have "cross2 \<gamma>2 \<gamma>1 = - cross2 \<gamma>1 \<gamma>2"
      by (simp add: cross2_def)
    ultimately have "vec_nth ell 1 = 0" "vec_nth ell 2 = 0"
      using det by auto
    then have "vec_nth ell i = vec_nth (0::real^2) i" for i :: 2
      using exhaust_2[of i] by auto
    then have "ell = 0"
      by (intro Finite_Cartesian_Product.vec_eq_iff[THEN iffD2] allI)
    then show False
      using ellnz by simp
  qed
  have gk: "g * k \<noteq> 0"
    using gnz knz by (simp add: g_def)
  have L1: "vec_nth L 1 = k * vec_nth c 1" and L2: "vec_nth L 2 = k * vec_nth c 2"
    using Lk by simp_all
  have Lc: "L \<bullet> w = k * (c \<bullet> w)" for w
    using Lk by simp
  have cc: "c \<bullet> c \<noteq> 0"
    using cnz by simp

  text \<open>Radial slots: one equation for every antenna.\<close>
  have radial: "P * res_s a t + g * k * (res_s a t + res_q a t) = 0" for a
  proof -
    have tc: "c \<bullet> vec_nth x a = vec_nth t a"
      by (simp add: t phase_coords_def)
    define r1 where "r1 = Re (cnj (phase c x a) * M1_moment x c)"
    define r2 where "r2 = Re (cnj (phase c x a) * M2_moment x c)"
    define lin where "lin = cos (vec_nth t a) * phase_lin_cos_sum t + sin (vec_nth t a) * phase_lin_sin_sum t"
    define amp where "amp = cos (vec_nth t a) * phase_cos_sum t + sin (vec_nth t a) * phase_sin_sum t"
    have r12: "vec_nth c 1 * r1 + vec_nth c 2 * r2 = lin"
      unfolding r1_def r2_def lin_def t by (rule Re_phase_cmoment)
    have Lr: "vec_nth L 1 * r1 + vec_nth L 2 * r2 = k * lin"
      unfolding L1 L2 r12[symmetric] by (simp add: algebra_simps)
    have F: "P * (2 * (c \<bullet> c) * (- res_s a t))
         + g * (2 * (c \<bullet> c) * (k * lin) + 2 * (k * (c \<bullet> c)) * (- res_s a t)
                - 2 * (c \<bullet> c) * (k * vec_nth t a) * amp) = 0"
      using slot0[of c a]
      unfolding ImA ReA r1_def[symmetric] r2_def[symmetric] Lr Lc tc
        lin_def[symmetric] amp_def[symmetric] .
    have E: "2 * (c \<bullet> c) * (- (P * res_s a t) - g * k * (res_s a t + res_q a t))
        = P * (2 * (c \<bullet> c) * (- res_s a t))
         + g * (2 * (c \<bullet> c) * (k * lin) + 2 * (k * (c \<bullet> c)) * (- res_s a t)
                - 2 * (c \<bullet> c) * (k * vec_nth t a) * amp)"
      unfolding res_q_def lin_def amp_def by (simp add: algebra_simps)
    have "2 * (c \<bullet> c) * (- (P * res_s a t) - g * k * (res_s a t + res_q a t)) = 0"
      unfolding E by (rule F)
    then have "- (P * res_s a t) - g * k * (res_s a t + res_q a t) = 0"
      using cc by simp
    then show ?thesis
      by linarith
  qed

  text \<open>The component of \<open>gradU = 0\<close> along the cokernel covector.\<close>
  have B1: "(cmod (A_moment x c))\<^sup>2 = res_W t"
    unfolding t by (rule cmod_A_sq)
  have scale: "Re (cnj (A_moment x c) * ((- \<i>) * (of_real r * Z)))
      = r * Re (cnj (A_moment x c) * ((- \<i>) * Z))" for r Z
    by (simp add: algebra_simps)
  have scalar: "P * res_W t - g * k * res_P t = 0"
  proof -
    define Zc where "Zc = of_real (vec_nth c 1) * M1_moment x c + of_real (vec_nth c 2) * M2_moment x c"
    have "ell \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      by (simp add: grad0)
    then have F: "P * (cmod (A_moment x c))\<^sup>2
        + g * (2 * Re (cnj (A_moment x c)
             * ((- \<i>) * (of_real (vec_nth L 1) * M1_moment x c + of_real (vec_nth L 2) * M2_moment x c)))) = 0"
      unfolding gradU_combination by (simp only: P_def L_def g_def c g1 g2 gd)
    have Z: "of_real (vec_nth L 1) * M1_moment x c + of_real (vec_nth L 2) * M2_moment x c = of_real k * Zc"
      unfolding Zc_def L1 L2 by (simp add: algebra_simps)
    have B2: "Re (cnj (A_moment x c) * ((- \<i>) * Zc)) = - res_P t / 2"
      unfolding Zc_def t by (rule Re_A_cmoment)
    have "P * res_W t + g * (2 * (k * (- res_P t / 2))) = 0"
      using F unfolding Z scale B1 B2 .
    then show ?thesis
      by (simp add: algebra_simps)
  qed

  show f0: "res_f m t = 0"
  proof -
    have sc: "g * k * res_P t = P * res_W t"
      using scalar by simp
    have ra: "g * k * (res_s m t + res_q m t) = - (P * res_s m t)"
      using radial[of m] by linarith
    have "g * k * res_f m t
        = res_s m t * (g * k * res_P t) + (g * k * (res_s m t + res_q m t)) * res_W t"
      by (simp add: res_f_def algebra_simps)
    also have "\<dots> = res_s m t * (P * res_W t) + (- (P * res_s m t)) * res_W t"
      by (simp only: sc ra)
    also have "\<dots> = 0"
      by (simp add: algebra_simps)
    finally show ?thesis
      using gk by simp
  qed

  show "gd * res_s m t * cross2 c \<gamma>2 + gain_dip \<omega> * (res_s m t + res_q m t) * cross2 \<gamma>1 \<gamma>2 = 0"
  proof -
    have "k * (gd * res_s m t * cross2 c \<gamma>2 + g * (res_s m t + res_q m t) * cross2 \<gamma>1 \<gamma>2)
        = (k * cross2 c \<gamma>2) * gd * res_s m t
          + (g * k * (res_s m t + res_q m t)) * cross2 \<gamma>1 \<gamma>2"
      by (simp add: algebra_simps)
    also have "\<dots> = (vec_nth ell 1 * cross2 \<gamma>1 \<gamma>2) * gd * res_s m t
          + (g * k * (res_s m t + res_q m t)) * cross2 \<gamma>1 \<gamma>2"
      by (simp only: ell1)
    also have "\<dots> = (P * res_s m t + g * k * (res_s m t + res_q m t)) * cross2 \<gamma>1 \<gamma>2"
      by (simp add: P_def algebra_simps)
    also have "\<dots> = 0"
      by (simp only: radial mult_zero_left)
    finally show ?thesis
      using knz by (simp add: g_def)
  qed

  show "2 * gain_dip \<omega> * cross2 \<gamma>1 \<gamma>2 * (\<Sum>b\<in>UNIV. vec_nth u b * res_s b t)
         = gd * cross2 (perp2 c) \<gamma>2 * res_W t"
  proof -
    define e :: "real^2" where "e = vector [cross2 (perp2 c) \<gamma>2, cross2 \<gamma>1 (perp2 c)]"
    define d where "d = cross2 \<gamma>1 \<gamma>2"
    define Zp where "Zp = of_real (vec_nth (perp2 c) 1) * M1_moment x c
                         + of_real (vec_nth (perp2 c) 2) * M2_moment x c"
    define S where "S = (\<Sum>b\<in>UNIV. vec_nth u b * res_s b t)"
    have e12: "vec_nth e 1 = cross2 (perp2 c) \<gamma>2" "vec_nth e 2 = cross2 \<gamma>1 (perp2 c)"
      by (simp_all add: e_def)
    have Le: "vec_nth e 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) + vec_nth e 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)
            = d *\<^sub>R perp2 c"
      unfolding e12 d_def g1[symmetric] g2[symmetric] by (rule cramer_combination)
    have "e \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      by (simp add: grad0)
    then have F: "vec_nth e 1 * gd * (cmod (A_moment x c))\<^sup>2
        + g * (2 * Re (cnj (A_moment x c)
             * ((- \<i>) * (of_real (vec_nth (d *\<^sub>R perp2 c) 1) * M1_moment x c
                         + of_real (vec_nth (d *\<^sub>R perp2 c) 2) * M2_moment x c)))) = 0"
      unfolding gradU_combination Le by (simp only: g_def c gd)
    have Z: "of_real (vec_nth (d *\<^sub>R perp2 c) 1) * M1_moment x c
           + of_real (vec_nth (d *\<^sub>R perp2 c) 2) * M2_moment x c = of_real d * Zp"
      unfolding Zp_def by (simp add: algebra_simps)
    have B3: "Re (cnj (A_moment x c) * ((- \<i>) * Zp)) = - S"
      unfolding Zp_def S_def t u by (rule Re_A_perpmoment)
    have "vec_nth e 1 * gd * res_W t + g * (2 * (d * (- S))) = 0"
      using F unfolding Z scale B1 B3 .
    then have "2 * g * d * S = gd * vec_nth e 1 * res_W t"
      by (simp add: algebra_simps)
    then show ?thesis
      unfolding e12 g_def d_def S_def .
  qed
qed

text \<open>The same for the residual set.\<close>

corollary residual_set_point_equations:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2" and m :: 'n
  defines "c \<equiv> cvec_dip \<omega>0 \<omega>s \<omega>"
    and "\<gamma>1 \<equiv> Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)" and "\<gamma>2 \<equiv> Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
    and "gd \<equiv> frechet_derivative gdip (at (vec_nth \<omega> 1)) 1"
  defines "t \<equiv> phase_coords c x" and "u \<equiv> perp_coords c x"
  assumes bad: "x \<in> residual_set \<omega>0 \<omega>s {\<omega>}"
    and pole_free: "sin (vec_nth \<omega> 1) \<noteq> 0"
    and nal: "res_s m t \<noteq> 0"
  shows "res_f m t = 0"
    and "gd * res_s m t * cross2 c \<gamma>2 + gain_dip \<omega> * (res_s m t + res_q m t) * cross2 \<gamma>1 \<gamma>2 = 0"
    and "2 * gain_dip \<omega> * cross2 \<gamma>1 \<gamma>2 * (\<Sum>b\<in>UNIV. vec_nth u b * res_s b t)
         = gd * cross2 (perp2 c) \<gamma>2 * res_W t"
proof -
  have grad0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and detD: "matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "c \<noteq> 0"
    and nsurj: "\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)"
    using bad unfolding residual_set_def c_def jacobian_cvec_dip by auto
  have det: "cross2 \<gamma>1 \<gamma>2 \<noteq> 0"
    using detD unfolding matrix_det_cross2 \<gamma>1_def \<gamma>2_def .
  have gnz: "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_sin) (use pole_free in simp)
  note eqs = residual_point_equations[OF c_def[THEN meta_eq_to_obj_eq] \<gamma>1_def[THEN meta_eq_to_obj_eq]
      \<gamma>2_def[THEN meta_eq_to_obj_eq] t_def[THEN meta_eq_to_obj_eq] u_def[THEN meta_eq_to_obj_eq]
      gd_def[THEN meta_eq_to_obj_eq] grad0 nsurj cnz det gnz nal]
  show "res_f m t = 0"
    and "gd * res_s m t * cross2 c \<gamma>2 + gain_dip \<omega> * (res_s m t + res_q m t) * cross2 \<gamma>1 \<gamma>2 = 0"
    and "2 * gain_dip \<omega> * cross2 \<gamma>1 \<gamma>2 * (\<Sum>b\<in>UNIV. vec_nth u b * res_s b t)
         = gd * cross2 (perp2 c) \<gamma>2 * res_W t"
    by (rule eqs)+
qed

end
