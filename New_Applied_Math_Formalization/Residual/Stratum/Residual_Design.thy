section \<open>The radial equation for the steering geometry of the capstone\<close>

theory Residual_Design
  imports Residual_Equations
begin

text \<open>Source overhead and main beam horizontal: \<open>\<omega>\<^sub>0 = (\<pi>/2, 0)\<close>, \<open>\<omega>\<^sub>s = (0, 0)\<close>.  For these angles
  the determinants in @{thm BadXGW_point_equations} are explicit and the radial equation is linear
  in \<open>cos \<phi>\<close> (\<open>Sketch.md\<close> \<section>8, L3).\<close>

definition design_beam :: "real^2" where
  "design_beam = vector [pi / 2, 0]"

definition design_source :: "real^2" where
  "design_source = vector [0, 0]"

lemma design_cvec:
  "vec_nth (cvec_dip design_beam design_source \<omega>) 1
     = sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2) + cos (vec_nth \<omega> 1) - 1"
  "vec_nth (cvec_dip design_beam design_source \<omega>) 2 = sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)"
  by (simp_all add: cvec_dip_def design_beam_def design_source_def kx_def ky_def kz_def axis_def)

lemma design_Dcvec1:
  "vec_nth (Dcvec_dip design_beam design_source \<omega> (axis 1 1)) 1
     = cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2) - sin (vec_nth \<omega> 1)"
  "vec_nth (Dcvec_dip design_beam design_source \<omega> (axis 1 1)) 2
     = cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)"
  by (simp_all add: Dcvec_dip_def design_beam_def design_source_def kx_def ky_def kz_def axis_def)

lemma design_Dcvec2:
  "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 1 = - (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))"
  "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 2 = sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)"
  by (simp_all add: Dcvec_dip_def axis_def)

lemma design_cross2:
  fixes \<omega> :: "real^2"
  defines "c \<equiv> cvec_dip design_beam design_source \<omega>"
    and "\<gamma>1 \<equiv> Dcvec_dip design_beam design_source \<omega> (axis 1 1)"
    and "\<gamma>2 \<equiv> Dcvec_dip design_beam design_source \<omega> (axis 2 1)"
  shows "cross2 \<gamma>1 \<gamma>2
       = sin (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) - sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2))"
    and "cross2 c \<gamma>2
       = sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) + (cos (vec_nth \<omega> 1) - 1) * cos (vec_nth \<omega> 2))"
    and "cross2 (perp2 c) \<gamma>2
       = sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2) * (cos (vec_nth \<omega> 1) - 1)"
proof -
  define st ct sp cp where "st = sin (vec_nth \<omega> 1)" and "ct = cos (vec_nth \<omega> 1)"
    and "sp = sin (vec_nth \<omega> 2)" and "cp = cos (vec_nth \<omega> 2)"
  have unit: "cp * cp + sp * sp = 1"
    by (simp add: cp_def sp_def)
  have c1: "vec_nth c 1 = st * cp + ct - 1" and c2: "vec_nth c 2 = st * sp"
    by (simp_all add: c_def design_cvec st_def ct_def sp_def cp_def)
  have a1: "vec_nth \<gamma>1 1 = ct * cp - st" and a2: "vec_nth \<gamma>1 2 = ct * sp"
    by (simp_all add: \<gamma>1_def design_Dcvec1 st_def ct_def sp_def cp_def)
  have b1: "vec_nth \<gamma>2 1 = - (st * sp)" and b2: "vec_nth \<gamma>2 2 = st * cp"
    by (simp_all add: \<gamma>2_def design_Dcvec2 st_def ct_def sp_def cp_def)
  have "cross2 \<gamma>1 \<gamma>2 = st * ct * (cp * cp + sp * sp) - st * st * cp"
    unfolding cross2_def a1 a2 b1 b2 by (simp add: algebra_simps)
  then show "cross2 \<gamma>1 \<gamma>2
       = sin (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) - sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2))"
    unfolding unit by (simp add: st_def ct_def cp_def algebra_simps)
  have "cross2 c \<gamma>2 = st * st * (cp * cp + sp * sp) + st * (ct - 1) * cp"
    unfolding cross2_def c1 c2 b1 b2 by (simp add: algebra_simps)
  then show "cross2 c \<gamma>2
       = sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) + (cos (vec_nth \<omega> 1) - 1) * cos (vec_nth \<omega> 2))"
    unfolding unit by (simp add: st_def ct_def cp_def algebra_simps)
  show "cross2 (perp2 c) \<gamma>2
       = sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2) * (cos (vec_nth \<omega> 1) - 1)"
    unfolding cross2_def perp2_nth c1 c2 b1 b2
    by (simp add: st_def ct_def sp_def cp_def algebra_simps)
qed

text \<open>A linear system used twice below.\<close>

lemma radial_coefficients_zero:
  fixes X Z a b :: real
  assumes K: "X * a + Z * (1 - b) = 0" and N: "X * b + Z * a = 0"
    and unit: "b * b + a * a = 1" and b1: "b \<noteq> 1"
  shows "Z = 0" and "X = 0"
proof -
  have "Z * (b - 1) = (X * a + Z * (1 - b)) * b - (X * b + Z * a) * a + Z * (b * b + a * a - 1)"
    by (simp add: algebra_simps)
  then have "Z * (b - 1) = 0"
    unfolding K N unit by simp
  then show Z: "Z = 0"
    using b1 by simp
  have "X = (X * a + Z * (1 - b)) * a + (X * b + Z * a) * b - X * (b * b + a * a - 1) - Z * a"
    by (simp add: algebra_simps)
  then have "X = - (Z * a)"
    unfolding K N unit by simp
  then show "X = 0"
    using Z by simp
qed

definition design_rho :: "real^2 \<Rightarrow> real" where
  "design_rho \<omega> = frechet_derivative gdip (at (vec_nth \<omega> 1)) 1 * sin (vec_nth \<omega> 2)
       * (cos (vec_nth \<omega> 1) - 1)
     / (2 * gdip (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) - sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)))"

lemma BadXGW_design_nondegenerate:
  fixes x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes bad: "x \<in> BadXGW design_beam design_source {\<omega>}"
  shows "cvec_dip design_beam design_source \<omega> \<noteq> 0"
    and "sin (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) - sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)) \<noteq> 0"
proof -
  show "cvec_dip design_beam design_source \<omega> \<noteq> 0"
    using bad unfolding BadXGW_def by auto
  have "matrix_det (matrix (Dcvec_dip design_beam design_source \<omega>)) \<noteq> 0"
    using bad unfolding BadXGW_def by auto
  then show "sin (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) - sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)) \<noteq> 0"
    unfolding matrix_det_cross2 design_cross2 .
qed

context
  fixes x :: "(real^2)^'n" and \<omega> :: "real^2" and m :: 'n
  assumes bad: "x \<in> BadXGW design_beam design_source {\<omega>}"
    and pole_free: "sin (vec_nth \<omega> 1) \<noteq> 0"
    and nal: "res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0"
begin

text \<open>\<open>K cos \<phi> = Num\<close>, with \<open>K\<close> and \<open>Num\<close> depending on \<open>\<theta>\<close> and the phases only.\<close>

theorem design_radial_equation:
  defines "t \<equiv> phase_coords (cvec_dip design_beam design_source \<omega>) x"
    and "gd \<equiv> frechet_derivative gdip (at (vec_nth \<omega> 1)) 1"
  shows "(gain_dip \<omega> * (res_s m t + res_q m t) * sin (vec_nth \<omega> 1)
            + gd * res_s m t * (1 - cos (vec_nth \<omega> 1))) * cos (vec_nth \<omega> 2)
       = gain_dip \<omega> * (res_s m t + res_q m t) * cos (vec_nth \<omega> 1)
            + gd * res_s m t * sin (vec_nth \<omega> 1)"
proof -
  define st ct cp where "st = sin (vec_nth \<omega> 1)" and "ct = cos (vec_nth \<omega> 1)"
    and "cp = cos (vec_nth \<omega> 2)"
  define X where "X = gain_dip \<omega> * (res_s m t + res_q m t)"
  define Z where "Z = gd * res_s m t"
  have "gd * res_s m t * (st * (st + (ct - 1) * cp)) + gain_dip \<omega> * (res_s m t + res_q m t) * (st * (ct - st * cp)) = 0"
    using BadXGW_point_equations(2)[OF bad pole_free nal]
    unfolding design_cross2 t_def gd_def st_def ct_def cp_def .
  moreover have "st * ((X * ct + Z * st) - (X * st + Z * (1 - ct)) * cp)
      = gd * res_s m t * (st * (st + (ct - 1) * cp)) + gain_dip \<omega> * (res_s m t + res_q m t) * (st * (ct - st * cp))"
    unfolding X_def Z_def by (simp add: algebra_simps)
  ultimately have "st * ((X * ct + Z * st) - (X * st + Z * (1 - ct)) * cp) = 0"
    by simp
  then have "(X * ct + Z * st) - (X * st + Z * (1 - ct)) * cp = 0"
    using pole_free by (simp add: st_def)
  then show ?thesis
    unfolding X_def Z_def st_def ct_def cp_def by simp
qed

text \<open>If the coefficient \<open>K\<close> vanishes, the point is at the height of the main beam.\<close>

theorem design_radial_degenerate:
  defines "t \<equiv> phase_coords (cvec_dip design_beam design_source \<omega>) x"
    and "gd \<equiv> frechet_derivative gdip (at (vec_nth \<omega> 1)) 1"
  assumes K0: "gain_dip \<omega> * (res_s m t + res_q m t) * sin (vec_nth \<omega> 1)
            + gd * res_s m t * (1 - cos (vec_nth \<omega> 1)) = 0"
  shows "cos (vec_nth \<omega> 1) = 0"
proof -
  define X where "X = gain_dip \<omega> * (res_s m t + res_q m t)"
  define Z where "Z = gd * res_s m t"
  have K: "X * sin (vec_nth \<omega> 1) + Z * (1 - cos (vec_nth \<omega> 1)) = 0"
    using K0 by (simp add: X_def Z_def)
  have "(gain_dip \<omega> * (res_s m t + res_q m t) * sin (vec_nth \<omega> 1)
            + gd * res_s m t * (1 - cos (vec_nth \<omega> 1))) * cos (vec_nth \<omega> 2)
       = gain_dip \<omega> * (res_s m t + res_q m t) * cos (vec_nth \<omega> 1)
            + gd * res_s m t * sin (vec_nth \<omega> 1)"
    unfolding t_def gd_def by (rule design_radial_equation)
  then have N: "X * cos (vec_nth \<omega> 1) + Z * sin (vec_nth \<omega> 1) = 0"
    unfolding K0 by (simp add: X_def Z_def)
  have unit: "cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 1) + sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1) = 1"
    by simp
  have ne1: "cos (vec_nth \<omega> 1) \<noteq> 1"
  proof
    assume "cos (vec_nth \<omega> 1) = 1"
    then have "sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1) = 0"
      using unit by simp
    then show False
      using pole_free by simp
  qed
  have "Z = 0"
    by (rule radial_coefficients_zero(1)[OF K N unit ne1])
  then have "gd = 0"
    using nal by (simp add: Z_def t_def)
  then show ?thesis
    unfolding gd_def using gdip_deriv_zero_iff[OF pole_free] by simp
qed

text \<open>The perpendicular coordinates lie on a hyperplane: \<open>\<Sum>\<^sub>b u\<^sub>b s\<^sub>b = \<rho>(\<omega>) W\<close>.\<close>

theorem design_perp_equation:
  defines "t \<equiv> phase_coords (cvec_dip design_beam design_source \<omega>) x"
    and "u \<equiv> perp_coords (cvec_dip design_beam design_source \<omega>) x"
  shows "(\<Sum>b\<in>UNIV. vec_nth u b * res_s b t) = design_rho \<omega> * res_W t"
proof -
  define st ct sp cp where "st = sin (vec_nth \<omega> 1)" and "ct = cos (vec_nth \<omega> 1)"
    and "sp = sin (vec_nth \<omega> 2)" and "cp = cos (vec_nth \<omega> 2)"
  define gd where "gd = frechet_derivative gdip (at (vec_nth \<omega> 1)) 1"
  define g where "g = gdip (vec_nth \<omega> 1)"
  define S where "S = (\<Sum>b\<in>UNIV. vec_nth u b * res_s b t)"
  define W where "W = res_W t"
  have gg: "gain_dip \<omega> = g"
    by (simp add: gain_dip_def g_def)
  have E3: "2 * g * (st * (ct - st * cp)) * S = gd * (st * sp * (ct - 1)) * W"
    using BadXGW_point_equations(3)[OF bad pole_free nal]
    unfolding design_cross2 gg t_def[symmetric] u_def[symmetric]
      st_def[symmetric] ct_def[symmetric] sp_def[symmetric] cp_def[symmetric]
      gd_def[symmetric] S_def[symmetric] W_def[symmetric] .
  have gnz: "g \<noteq> 0"
    using gain_dip_nonzero_of_sin[of \<omega>] pole_free gg by simp
  have stnz: "st \<noteq> 0"
    using pole_free by (simp add: st_def)
  have dnz: "ct - st * cp \<noteq> 0"
    using BadXGW_design_nondegenerate(2)[OF bad] by (simp add: st_def ct_def cp_def)
  have "st * (2 * g * (ct - st * cp) * S) = st * (gd * sp * (ct - 1) * W)"
    using E3 by (simp add: algebra_simps)
  then have "2 * g * (ct - st * cp) * S = gd * sp * (ct - 1) * W"
    using stnz by simp
  then have "S = gd * sp * (ct - 1) / (2 * g * (ct - st * cp)) * W"
    using gnz dnz by (simp add: field_simps)
  then show ?thesis
    unfolding S_def W_def design_rho_def gd_def g_def st_def ct_def sp_def cp_def .
qed

end

end
