section \<open>The non-aligned residual is covered by closed negligible sets\<close>

theory Residual_Chart_Cover
  imports
    Residual_Charts
begin

text \<open>Six charts per antenna \<open>m\<close>.  The source is \<open>(t, w)\<close>; the entry \<open>w\<^sub>m\<close> is the parameter of
  the curve on which the angle lies.  Charts \<open>0\<close> and \<open>1\<close>: \<open>\<theta> = w\<^sub>m\<close> and
  \<open>\<phi> = \<plusminus> arccos (N / K)\<close>, from @{thm design_radial_equation}.  Charts \<open>2, 3, 4\<close>: \<open>\<theta> = w\<^sub>m\<close> and
  \<open>\<phi> \<in> {-\<pi>, 0, \<pi>}\<close>.  Chart \<open>5\<close>: \<open>\<theta> = \<pi>/2\<close> and \<open>\<phi> = w\<^sub>m\<close>, the case \<open>K = 0\<close>.\<close>

subsection \<open>The charts\<close>

definition src_p :: "'n \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> real" where
  "src_p m z = vec_nth (snd z) m"

definition rad_K :: "'n \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> real" where
  "rad_K m z = gdip (src_p m z) * (res_s m (fst z) + res_q m (fst z)) * sin (src_p m z)
     + frechet_derivative gdip (at (src_p m z)) 1 * res_s m (fst z) * (1 - cos (src_p m z))"

definition rad_N :: "'n \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> real" where
  "rad_N m z = gdip (src_p m z) * (res_s m (fst z) + res_q m (fst z)) * cos (src_p m z)
     + frechet_derivative gdip (at (src_p m z)) 1 * res_s m (fst z) * sin (src_p m z)"

definition chart_th :: "'n \<Rightarrow> nat \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> real" where
  "chart_th m k z = (if k < 5 then src_p m z else pi / 2)"

definition chart_ph :: "'n \<Rightarrow> nat \<Rightarrow> (real^'n) \<times> (real^'n) \<Rightarrow> real" where
  "chart_ph m k z =
     (if k = 0 then arccos (rad_N m z / rad_K m z)
      else if k = 1 then - arccos (rad_N m z / rad_K m z)
      else if k = 2 then - pi
      else if k = 3 then 0
      else if k = 4 then pi
      else src_p m z)"

definition chart_Dom :: "'n \<Rightarrow> nat \<Rightarrow> ((real^'n) \<times> (real^'n)) set" where
  "chart_Dom m k = (if k < 2 then {z. rad_K m z \<noteq> 0 \<and> (rad_N m z)\<^sup>2 < (rad_K m z)\<^sup>2} else UNIV)"

lemma src_p_differentiable [simp]: "src_p m differentiable (at z)"
  unfolding src_p_def[abs_def] by simp

lemma rad_differentiable [simp]:
  "rad_K m differentiable (at z)" "rad_N m differentiable (at z)"
proof -
  have dg: "(\<lambda>z. gdip (src_p m z)) differentiable (at z)"
    by (rule differentiable_compose[OF gdip_differentiable src_p_differentiable])
  have dgd: "(\<lambda>z. frechet_derivative gdip (at (src_p m z)) 1) differentiable (at z)"
    by (rule differentiable_compose[OF gdip_deriv_differentiable src_p_differentiable])
  show "rad_K m differentiable (at z)"
    unfolding rad_K_def[abs_def] using dg dgd by simp
  show "rad_N m differentiable (at z)"
    unfolding rad_N_def[abs_def] using dg dgd by simp
qed

lemma ratio_in_unit_interval:
  fixes N K :: real
  assumes "K \<noteq> 0" and "N\<^sup>2 < K\<^sup>2"
  shows "- 1 < N / K" and "N / K < 1"
proof -
  have "(N / K)\<^sup>2 < 1"
    using assms by (simp add: power_divide)
  then have "\<bar>N / K\<bar> < 1"
    using abs_square_less_1[of "N / K"] by blast
  then have "N / K < 1 \<and> - (N / K) < 1"
    by (rule abs_less_iff[THEN iffD1])
  then show "- 1 < N / K" and "N / K < 1"
    by linarith+
qed

lemma chart_Dom_open: "open (chart_Dom m k)"
proof (cases "k < 2")
  case True
  have cK: "continuous_on UNIV (rad_K m)" and cN: "continuous_on UNIV (rad_N m)"
    by (intro differentiable_imp_continuous_on differentiable_at_imp_differentiable_on rad_differentiable)+
  have "open {z. rad_K m z \<noteq> 0}"
    by (rule open_Collect_neq[OF cK continuous_on_const])
  moreover have "open {z. (rad_N m z)\<^sup>2 < (rad_K m z)\<^sup>2}"
    by (rule open_Collect_less) (intro continuous_intros cN cK)+
  moreover have "chart_Dom m k = {z. rad_K m z \<noteq> 0} \<inter> {z. (rad_N m z)\<^sup>2 < (rad_K m z)\<^sup>2}"
    using True by (auto simp: chart_Dom_def)
  ultimately show ?thesis
    by (simp add: open_Int)
next
  case False
  then show ?thesis
    by (simp add: chart_Dom_def)
qed

lemma chart_th_differentiable: "chart_th m k differentiable (at z)"
  unfolding chart_th_def[abs_def] by (cases "k < 5") simp_all

lemma chart_ph_differentiable:
  assumes "z \<in> chart_Dom m k"
  shows "chart_ph m k differentiable (at z)"
proof -
  have arc: "(\<lambda>z. arccos (rad_N m z / rad_K m z)) differentiable (at z)" if "k < 2"
  proof (rule differentiable_arccos_real)
    have K: "rad_K m z \<noteq> 0" and lt: "(rad_N m z)\<^sup>2 < (rad_K m z)\<^sup>2"
      using assms that by (simp_all add: chart_Dom_def)
    show "(\<lambda>z. rad_N m z / rad_K m z) differentiable (at z)"
      using K by simp
    show "- 1 < rad_N m z / rad_K m z" and "rad_N m z / rad_K m z < 1"
      by (rule ratio_in_unit_interval[OF K lt])+
  qed
  consider "k = 0" | "k = 1" | "k = 2" | "k = 3" | "k = 4" | "5 \<le> k"
    by linarith
  then show ?thesis
  proof cases
    case 1
    then have "chart_ph m k = (\<lambda>z. arccos (rad_N m z / rad_K m z))"
      by (simp add: chart_ph_def[abs_def])
    then show ?thesis
      using arc 1 by simp
  next
    case 2
    then have "chart_ph m k = (\<lambda>z. - arccos (rad_N m z / rad_K m z))"
      by (simp add: chart_ph_def[abs_def])
    then show ?thesis
      using arc 2 by simp
  next
    case 3
    then have "chart_ph m k = (\<lambda>z. - pi)"
      by (simp add: chart_ph_def[abs_def])
    then show ?thesis
      by simp
  next
    case 4
    then have "chart_ph m k = (\<lambda>z. 0)"
      by (simp add: chart_ph_def[abs_def])
    then show ?thesis
      by simp
  next
    case 5
    then have "chart_ph m k = (\<lambda>z. pi)"
      by (simp add: chart_ph_def[abs_def])
    then show ?thesis
      by simp
  next
    case 6
    then have "chart_ph m k = src_p m"
      by (auto simp: chart_ph_def[abs_def])
    then show ?thesis
      by simp
  qed
qed

text \<open>The pieces of chart \<open>k\<close> for antenna \<open>m\<close>.\<close>

lemma chart_pieces:
  "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      chart_map (chart_th m k) (chart_ph m k) m
        ` {z \<in> chart_Dom m k. chart_nondeg (chart_th m k) (chart_ph m k) m z \<noteq> 0 \<and> res_f m (fst z) = 0}
        \<subseteq> (\<Union>n. K n)
      \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
  by (rule chart_image_cover[OF chart_Dom_open chart_th_differentiable chart_ph_differentiable])

subsection \<open>Every non-aligned point of the bad set is in a chart image\<close>

lemma OmegaPF_design_bounds:
  assumes "\<omega> \<in> OmegaPF design_beam (pi / 4)"
  shows "pi / 4 \<le> vec_nth \<omega> 1" and "vec_nth \<omega> 1 \<le> 3 * pi / 4"
    and "- pi \<le> vec_nth \<omega> 2" and "vec_nth \<omega> 2 \<le> pi"
proof -
  have mb: "vec_nth (design_beam - vector [pi / 4, pi]) i \<le> vec_nth \<omega> i
      \<and> vec_nth \<omega> i \<le> vec_nth (design_beam + vector [pi / 4, pi]) i" for i :: 2
    using assms unfolding OmegaPF_def mem_box_cart by blast
  show "pi / 4 \<le> vec_nth \<omega> 1" and "vec_nth \<omega> 1 \<le> 3 * pi / 4"
    using mb[of 1] by (simp_all add: design_beam_def)
  show "- pi \<le> vec_nth \<omega> 2" and "vec_nth \<omega> 2 \<le> pi"
    using mb[of 2] by (simp_all add: design_beam_def)
qed

lemma chart_covers_point:
  fixes x :: "(real^2)^'n" and \<omega> :: "real^2" and m :: 'n
    and th ph :: "(real^'n) \<times> (real^'n) \<Rightarrow> real"
  defines "c \<equiv> cvec_dip design_beam design_source \<omega>"
  defines "t \<equiv> phase_coords c x" and "u \<equiv> perp_coords c x"
  assumes bad: "x \<in> residual_set design_beam design_source {\<omega>}"
    and pole_free: "sin (vec_nth \<omega> 1) \<noteq> 0"
    and nal: "res_s m t \<noteq> 0"
    and z: "z = (t, (\<chi> b. if b = m then p0 else vec_nth u b))"
    and th: "th z = vec_nth \<omega> 1" and ph: "ph z = vec_nth \<omega> 2"
  shows "chart_map th ph m z = x"
    and "chart_nondeg th ph m z \<noteq> 0"
    and "res_f m (fst z) = 0"
proof -
  have nal': "res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0"
    using nal by (simp add: t_def c_def)
  have cnz: "c \<noteq> 0"
    unfolding c_def by (rule residual_set_design_nondegenerate(1)[OF bad])
  have fz: "fst z = t" and sz: "vec_nth (snd z) b = (if b = m then p0 else vec_nth u b)" for b
    by (simp_all add: z)
  have c1: "chart_c1 th ph z = vec_nth c 1" and c2: "chart_c2 th ph z = vec_nth c 2"
    by (simp_all add: chart_c1_def chart_c2_def th ph c_def design_cvec)
  have cv: "vector [chart_c1 th ph z, chart_c2 th ph z] = c"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 2
    show "vec_nth (vector [chart_c1 th ph z, chart_c2 th ph z]) i = vec_nth c i"
      using exhaust_2[of i] c1 c2 by auto
  qed
  have rho: "chart_rho th ph z = design_rho \<omega>"
    by (simp add: chart_rho_def design_rho_def th ph)
  have E3: "(\<Sum>b\<in>UNIV. vec_nth u b * res_s b t) = design_rho \<omega> * res_W t"
    unfolding u_def t_def c_def by (rule design_perp_equation[OF bad pole_free nal'])
  have split: "(\<Sum>b\<in>UNIV. vec_nth u b * res_s b t)
      = vec_nth u m * res_s m t + (\<Sum>b\<in>UNIV - {m}. vec_nth u b * res_s b t)"
    by (rule sum.remove) simp_all
  have rest: "(\<Sum>b\<in>UNIV - {m}. vec_nth (snd z) b * res_s b t)
      = (\<Sum>b\<in>UNIV - {m}. vec_nth u b * res_s b t)"
    by (rule sum.cong) (auto simp: sz)
  have "chart_um th ph m z
      = (design_rho \<omega> * res_W t - (\<Sum>b\<in>UNIV - {m}. vec_nth u b * res_s b t)) / res_s m t"
    by (simp only: chart_um_def rho fz rest)
  also have "\<dots> = (vec_nth u m * res_s m t) / res_s m t"
    unfolding E3[symmetric] split by simp
  also have "\<dots> = vec_nth u m"
    using nal by simp
  finally have um: "chart_um th ph m z = vec_nth u m" .
  have uu: "chart_u th ph m z = u"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix b :: 'n
    show "vec_nth (chart_u th ph m z) b = vec_nth u b"
      by (simp add: chart_u_def um sz)
  qed
  show "chart_map th ph m z = x"
    unfolding chart_map_def cv uu fz t_def u_def by (rule tu_param_map_reconstruct[OF cnz])
  have "sin (th z) * (cos (th z) - sin (th z) * cos (ph z)) \<noteq> 0"
    unfolding th ph by (rule residual_set_design_nondegenerate(2)[OF bad])
  moreover have "(chart_c1 th ph z)\<^sup>2 + (chart_c2 th ph z)\<^sup>2 = c \<bullet> c"
    by (simp add: c1 c2 inner2 power2_eq_square)
  moreover have "c \<bullet> c \<noteq> 0"
    using cnz by simp
  ultimately show "chart_nondeg th ph m z \<noteq> 0"
    unfolding chart_nondeg_def fz using nal by simp
  show "res_f m (fst z) = 0"
    unfolding fz t_def c_def by (rule residual_set_point_equations(1)[OF bad pole_free nal'])
qed

lemma nonaligned_point_in_chart_image:
  fixes x :: "(real^2)^'n" and \<omega> :: "real^2" and m :: 'n
  assumes box: "\<omega> \<in> OmegaPF design_beam (pi / 4)"
    and bad: "x \<in> residual_set design_beam design_source {\<omega>}"
    and nal: "res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0"
  shows "\<exists>k. x \<in> chart_map (chart_th m k) (chart_ph m k) m
        ` {z \<in> chart_Dom m k. chart_nondeg (chart_th m k) (chart_ph m k) m z \<noteq> 0 \<and> res_f m (fst z) = 0}"
proof -
  define \<theta> \<phi> where "\<theta> = vec_nth \<omega> 1" and "\<phi> = vec_nth \<omega> 2"
  define c where "c = cvec_dip design_beam design_source \<omega>"
  define t where "t = phase_coords c x"
  define u where "u = perp_coords c x"
  note b = OmegaPF_design_bounds[OF box]
  have \<theta>pos: "0 < \<theta>" and \<theta>pi: "\<theta> < pi"
    using b(1,2) pi_gt_zero unfolding \<theta>_def by linarith+
  have pole_free: "sin (vec_nth \<omega> 1) \<noteq> 0"
    using sin_gt_zero[OF \<theta>pos \<theta>pi] by (simp add: \<theta>_def)
  have nal_t: "res_s m t \<noteq> 0"
    using nal by (simp add: t_def c_def)
  define K0 where "K0 = gdip \<theta> * (res_s m t + res_q m t) * sin \<theta>
     + frechet_derivative gdip (at \<theta>) 1 * res_s m t * (1 - cos \<theta>)"
  define N0 where "N0 = gdip \<theta> * (res_s m t + res_q m t) * cos \<theta>
     + frechet_derivative gdip (at \<theta>) 1 * res_s m t * sin \<theta>"
  have radial: "K0 * cos \<phi> = N0"
    using design_radial_equation[OF bad pole_free nal]
    unfolding K0_def N0_def \<theta>_def \<phi>_def t_def c_def by (simp add: gain_dip_def)

  text \<open>A point of the source with \<open>w\<^sub>m = p0\<close>, and the three facts once the angles match.\<close>
  have cover: "x \<in> chart_map (chart_th m k) (chart_ph m k) m
        ` {z \<in> chart_Dom m k. chart_nondeg (chart_th m k) (chart_ph m k) m z \<noteq> 0 \<and> res_f m (fst z) = 0}"
    if th: "chart_th m k (t, (\<chi> b. if b = m then p0 else vec_nth u b)) = \<theta>"
      and ph: "chart_ph m k (t, (\<chi> b. if b = m then p0 else vec_nth u b)) = \<phi>"
      and dom: "(t, (\<chi> b. if b = m then p0 else vec_nth u b)) \<in> chart_Dom m k" for k p0
  proof -
    define z where "z = (t, (\<chi> b. if b = m then p0 else vec_nth u b))"
    note facts = chart_covers_point[where th = "chart_th m k" and ph = "chart_ph m k",
        OF bad pole_free nal_t[unfolded t_def c_def]
        z_def[unfolded t_def u_def c_def] th[folded z_def, unfolded \<theta>_def] ph[folded z_def, unfolded \<phi>_def]]
    have "chart_map (chart_th m k) (chart_ph m k) m z = x"
      and "chart_nondeg (chart_th m k) (chart_ph m k) m z \<noteq> 0"
      and "res_f m (fst z) = 0"
      by (rule facts)+
    moreover have "z \<in> chart_Dom m k"
      using dom by (simp add: z_def)
    ultimately show ?thesis
      by (metis (mono_tags, lifting) imageI mem_Collect_eq)
  qed
  have p_src: "src_p m (t, (\<chi> b. if b = m then p0 else vec_nth u b)) = p0" for p0
    by (simp add: src_p_def)
  have radK: "rad_K m (t, (\<chi> b. if b = m then \<theta> else vec_nth u b)) = K0"
    and radN: "rad_N m (t, (\<chi> b. if b = m then \<theta> else vec_nth u b)) = N0"
    by (simp_all add: rad_K_def rad_N_def p_src K0_def N0_def)

  consider (arcs) "\<phi> = - pi \<or> \<phi> = 0 \<or> \<phi> = pi"
    | (deg) "\<not> (\<phi> = - pi \<or> \<phi> = 0 \<or> \<phi> = pi)" "K0 = 0"
    | (upper) "0 < \<phi>" "\<phi> < pi" "K0 \<noteq> 0"
    | (lower) "- pi < \<phi>" "\<phi> < 0" "K0 \<noteq> 0"
    using b(3,4) unfolding \<phi>_def by argo
  then show ?thesis
  proof cases
    case arcs
    then consider "\<phi> = - pi" | "\<phi> = 0" | "\<phi> = pi"
      by blast
    then show ?thesis
    proof cases
      case 1
      show ?thesis
        by (rule exI[of _ 2], rule cover[of 2 \<theta>]) (simp_all add: chart_th_def chart_ph_def chart_Dom_def p_src 1)
    next
      case 2
      show ?thesis
        by (rule exI[of _ 3], rule cover[of 3 \<theta>]) (simp_all add: chart_th_def chart_ph_def chart_Dom_def p_src 2)
    next
      case 3
      show ?thesis
        by (rule exI[of _ 4], rule cover[of 4 \<theta>]) (simp_all add: chart_th_def chart_ph_def chart_Dom_def p_src 3)
    qed
  next
    case deg
    have "gain_dip \<omega> * (res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x)
              + res_q m (phase_coords (cvec_dip design_beam design_source \<omega>) x)) * sin (vec_nth \<omega> 1)
          + frechet_derivative gdip (at (vec_nth \<omega> 1)) 1
              * res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) * (1 - cos (vec_nth \<omega> 1)) = 0"
      using deg(2) unfolding K0_def \<theta>_def t_def c_def by (simp add: gain_dip_def)
    then have "cos \<theta> = 0"
      unfolding \<theta>_def by (rule design_radial_degenerate[OF bad pole_free nal])
    then have "arccos (cos \<theta>) = pi / 2"
      by simp
    then have \<theta>half: "\<theta> = pi / 2"
      using arccos_cos[of \<theta>] \<theta>pos \<theta>pi by simp
    show ?thesis
      by (rule exI[of _ 5], rule cover[of 5 \<phi>]) (simp_all add: chart_th_def chart_ph_def chart_Dom_def p_src \<theta>half)
  next
    case upper
    have cosphi: "cos \<phi> = N0 / K0"
      using radial upper(3) by (simp add: field_simps)
    have "sin \<phi> \<noteq> 0"
      using sin_gt_zero[OF upper(1,2)] by simp
    then have "(cos \<phi>)\<^sup>2 < 1"
      using sin_cos_squared_add[of \<phi>] by (smt (verit) zero_less_power2)
    then have "N0\<^sup>2 < K0\<^sup>2"
      using upper(3) unfolding cosphi by (simp add: power_divide)
    moreover have "arccos (N0 / K0) = \<phi>"
      unfolding cosphi[symmetric] using arccos_cos[of \<phi>] upper(1,2) by simp
    ultimately show ?thesis
      by (intro exI[of _ 0] cover[of 0 \<theta>])
         (simp_all add: chart_th_def chart_ph_def chart_Dom_def p_src radK radN upper(3))
  next
    case lower
    have cosphi: "cos \<phi> = N0 / K0"
      using radial lower(3) by (simp add: field_simps)
    have "0 < sin (- \<phi>)"
      by (rule sin_gt_zero) (use lower(1,2) in simp_all)
    then have "sin \<phi> \<noteq> 0"
      by simp
    then have "(cos \<phi>)\<^sup>2 < 1"
      using sin_cos_squared_add[of \<phi>] by (smt (verit) zero_less_power2)
    then have "N0\<^sup>2 < K0\<^sup>2"
      using lower(3) unfolding cosphi by (simp add: power_divide)
    moreover have "- arccos (N0 / K0) = \<phi>"
      unfolding cosphi[symmetric] using arccos_cos2[of \<phi>] lower(1,2) by simp
    ultimately show ?thesis
      by (intro exI[of _ 1] cover[of 1 \<theta>])
         (simp_all add: chart_th_def chart_ph_def chart_Dom_def p_src radK radN lower(3))
  qed
qed

subsection \<open>The cover\<close>

lemma countable_family_of_covers:
  fixes F :: "'i::countable \<Rightarrow> nat \<Rightarrow> 'a::euclidean_space set"
  assumes "\<And>i n. closed (F i n)" and "\<And>i n. negligible (F i n)"
  shows "\<exists>K :: nat \<Rightarrow> 'a set. (\<Union>i. \<Union>n. F i n) \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  define K where "K j = F (fst (Countable.from_nat j :: 'i \<times> nat)) (snd (Countable.from_nat j :: 'i \<times> nat))" for j
  have "F i n \<subseteq> (\<Union>j. K j)" for i n
  proof -
    have "K (Countable.to_nat (i, n)) = F i n"
      by (simp add: K_def)
    then show ?thesis
      by blast
  qed
  then have sub: "(\<Union>i. \<Union>n. F i n) \<subseteq> (\<Union>j. K j)"
    by blast
  have cl: "\<forall>j. closed (K j)" and ng: "\<forall>j. negligible (K j)"
    by (simp_all add: K_def assms)
  show ?thesis
    by (rule exI[of _ K]) (rule conjI[OF sub conjI[OF cl ng]])
qed

theorem nonaligned_residual_cover:
  "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
     {x. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). x \<in> residual_set design_beam design_source {\<omega>}
           \<and> (\<exists>m. res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0)}
       \<subseteq> (\<Union>n. K n)
     \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  define img :: "'n \<times> nat \<Rightarrow> ((real^2)^'n) set" where
    "img i = chart_map (chart_th (fst i) (snd i)) (chart_ph (fst i) (snd i)) (fst i)
        ` {z \<in> chart_Dom (fst i) (snd i).
            chart_nondeg (chart_th (fst i) (snd i)) (chart_ph (fst i) (snd i)) (fst i) z \<noteq> 0
            \<and> res_f (fst i) (fst z) = 0}" for i
  have "\<forall>i. \<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      img i \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
    unfolding img_def using chart_pieces by blast
  then have "\<exists>F :: 'n \<times> nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set.
      \<forall>i. img i \<subseteq> (\<Union>n. F i n) \<and> (\<forall>n. closed (F i n)) \<and> (\<forall>n. negligible (F i n))"
    by (rule choice)
  then obtain F :: "'n \<times> nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
    where FP: "\<forall>i. img i \<subseteq> (\<Union>n. F i n) \<and> (\<forall>n. closed (F i n)) \<and> (\<forall>n. negligible (F i n))" ..
  have F: "img i \<subseteq> (\<Union>n. F i n)" for i
    using FP[THEN spec, of i] by (rule conjunct1)
  have Fc: "closed (F i n)" for i n
    using FP[THEN spec, of i] by simp
  have Fn: "negligible (F i n)" for i n
    using FP[THEN spec, of i] by simp
  have "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      (\<Union>i. \<Union>n. F i n) \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
    by (rule countable_family_of_covers[OF Fc Fn])
  then obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where KP: "(\<Union>i. \<Union>n. F i n) \<subseteq> (\<Union>n. K n) \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))" ..
  have K: "(\<Union>i. \<Union>n. F i n) \<subseteq> (\<Union>n. K n)"
    using KP by (rule conjunct1)
  have Kcn: "(\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
    using KP by (rule conjunct2)
  have sub: "{x. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). x \<in> residual_set design_beam design_source {\<omega>}
           \<and> (\<exists>m. res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0)}
       \<subseteq> (\<Union>n. K n)"
  proof (rule subsetI)
    fix x :: "(real^2)^'n"
    assume "x \<in> {x. \<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). x \<in> residual_set design_beam design_source {\<omega>}
           \<and> (\<exists>m. res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0)}"
    then have "\<exists>\<omega>\<in>OmegaPF design_beam (pi / 4). x \<in> residual_set design_beam design_source {\<omega>}
           \<and> (\<exists>m. res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0)"
      by (rule CollectD)
    then obtain \<omega> where box: "\<omega> \<in> OmegaPF design_beam (pi / 4)"
      and rest: "x \<in> residual_set design_beam design_source {\<omega>}
           \<and> (\<exists>m. res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0)" ..
    have bad: "x \<in> residual_set design_beam design_source {\<omega>}"
      using rest by (rule conjunct1)
    obtain m where nal: "res_s m (phase_coords (cvec_dip design_beam design_source \<omega>) x) \<noteq> 0"
      using rest[THEN conjunct2] ..
    obtain k where "x \<in> chart_map (chart_th m k) (chart_ph m k) m
        ` {z \<in> chart_Dom m k. chart_nondeg (chart_th m k) (chart_ph m k) m z \<noteq> 0 \<and> res_f m (fst z) = 0}"
      using nonaligned_point_in_chart_image[OF box bad nal] ..
    then have "x \<in> img (m, k)"
      by (simp add: img_def)
    then have "x \<in> (\<Union>n. F (m, k) n)"
      by (rule subsetD[OF F])
    moreover have "(\<Union>n. F (m, k) n) \<subseteq> (\<Union>i. \<Union>n. F i n)"
      by (rule UN_upper) simp
    ultimately have "x \<in> (\<Union>i. \<Union>n. F i n)"
      by (rule rev_subsetD)
    then show "x \<in> (\<Union>n. K n)"
      by (rule subsetD[OF K])
  qed
  show ?thesis
    by (rule exI[of _ K]) (rule conjI[OF sub Kcn])
qed

end
