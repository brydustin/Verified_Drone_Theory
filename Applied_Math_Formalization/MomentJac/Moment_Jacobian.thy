theory Moment_Jacobian
  imports
    Applied_Math_BlockDet.Moment_Map
    Applied_Math_BlockDet.Block_Determinants_BigJ
begin

subsection \<open>The canonical six-element base configuration\<close>

text \<open>
  TeX Section ``Surjectivity of the moment map'' fixes a canonical
  6-element configuration in \<open>c\<close>-adapted coordinates:
  \begin{align*}
    (u_1, v_1) &= (0,           2), &
    (u_2, v_2) &= (\pi/3\kappa, 2), &
    (u_3, v_3) &= (2\pi/3\kappa, 0), \\
    (u_4, v_4) &= (\pi/\kappa,  0), &
    (u_5, v_5) &= (4\pi/3\kappa, 2), &
    (u_6, v_6) &= (5\pi/3\kappa, 2),
  \end{align*}
  with steering parameter \<open>c = \<kappa> e\<^sub>\<parallel> = (\<kappa>, 0)\<close>. At \<open>\<kappa> = 1\<close> the
  rescaled coordinates \<open>t_n := \<kappa> u_n = u_n\<close> take the equally-spaced
  values \<open>0, \<pi>/3, 2\<pi>/3, \<pi>, 4\<pi>/3, 5\<pi>/3\<close> (sixth roots of unity in
  phase). \<^const>\<open>bigJ\<close> is the \<open>12 \<times> 12\<close> Jacobian \<open>D\<^sub>x M_paper\<close> evaluated at
  this base point, also at \<open>\<kappa> = 1\<close>.
\<close>

definition x0_paper :: "planar^6"
  where "x0_paper = vector
    [ vector [0,        2],
      vector [pi/3,     2],
      vector [2*pi/3,   0],
      vector [pi,       0],
      vector [4*pi/3,   2],
      vector [5*pi/3,   2] ]"

definition c0_paper :: "planar"
  where "c0_paper = vector [1, 0]"

text \<open>The six base-point coordinates, exposed as simp rules for the
  later Jacobian identification \<open>D\<^sub>x M_paper(x0_paper, c0_paper) = (*v) bigJ\<close>.\<close>

lemma x0_paper_entries [simp]:
  "x0_paper $ 1 = vector [0,       2]"
  "x0_paper $ 2 = vector [pi/3,    2]"
  "x0_paper $ 3 = vector [2*pi/3,  0]"
  "x0_paper $ 4 = vector [pi,      0]"
  "x0_paper $ 5 = vector [4*pi/3,  2]"
  "x0_paper $ 6 = vector [5*pi/3,  2]"
  unfolding x0_paper_def by simp_all

lemma c0_paper_entries [simp]:
  "c0_paper $ 1 = 1"
  "c0_paper $ 2 = 0"
  unfolding c0_paper_def by simp_all

text \<open>The \<open>t_n = \<kappa> u_n\<close> values at \<open>\<kappa> = 1\<close>; \<open>cos t_n, sin t_n\<close> reduce to the
  sixth roots of unity, matching the explicit numeric entries of \<^const>\<open>bigJ\<close>.\<close>

lemma x0_paper_t_values:
  "(x0_paper $ 1) $ 1 = 0"
  "(x0_paper $ 2) $ 1 = pi/3"
  "(x0_paper $ 3) $ 1 = 2*pi/3"
  "(x0_paper $ 4) $ 1 = pi"
  "(x0_paper $ 5) $ 1 = 4*pi/3"
  "(x0_paper $ 6) $ 1 = 5*pi/3"
  by simp_all

lemma x0_paper_v_values:
  "(x0_paper $ 1) $ 2 = 2"
  "(x0_paper $ 2) $ 2 = 2"
  "(x0_paper $ 3) $ 2 = 0"
  "(x0_paper $ 4) $ 2 = 0"
  "(x0_paper $ 5) $ 2 = 2"
  "(x0_paper $ 6) $ 2 = 2"
  by simp_all

text \<open>\<open>c = \<kappa> e\<^sub>\<parallel>\<close> with \<open>\<kappa> > 0\<close> requires the steering vector be nonzero.\<close>

lemma c0_paper_nonzero: "c0_paper \<noteq> 0"
  using c0_paper_entries(1) by fastforce

text \<open>
  \<^bold>\<open>Closed-form phase values at the base configuration.\<close> Since
  \<open>c0_paper = (1,0)\<close>, the steering form at point \<open>n\<close> is
  \<open>c0_paper \<bullet> (x0_paper $ n) = u_n\<close>, the first coordinate, taking the six
  equally-spaced values \<open>0, \<pi>/3, 2\<pi>/3, \<pi>, 4\<pi>/3, 5\<pi>/3\<close>. The phase factor is
  \<open>cis(-u_n) = cos u_n - \<imath> sin u_n\<close>, so the entire Jacobian
  \<open>D\<^sub>x M_paper(x0_paper, c0_paper)\<close> is expressible through \<open>cos\<close>/\<open>sin\<close> at these
  six angles. We record their values (sixth roots of unity) once; this is the
  arithmetic substrate of the identification \<open>D\<^sub>x M_paper = (*v) bigJ\<close>.
\<close>

lemma sqrt3_sq: "sqrt 3 * sqrt 3 = 3"
  using real_sqrt_pow2[of 3] by (simp add: power2_eq_square)

lemma base_trig_values:
  shows "cos (0::real) = 1" and "sin (0::real) = 0"
    and "cos (pi/3) = 1/2" and "sin (pi/3) = sqrt 3 / 2"
    and "cos (2*pi/3) = - (1/2)" and "sin (2*pi/3) = sqrt 3 / 2"
    and "cos pi = - 1" and "sin pi = 0"
    and "cos (4*pi/3) = - (1/2)" and "sin (4*pi/3) = - (sqrt 3 / 2)"
    and "cos (5*pi/3) = 1/2" and "sin (5*pi/3) = - (sqrt 3 / 2)"
proof -
  have c3: "cos (pi/3) = 1/2" by (rule cos_60)
  have s3: "sin (pi/3) = sqrt 3 / 2" by (rule sin_60)

  text \<open>\<open>2\<pi>/3 = \<pi>/3 + \<pi>/3\<close>: the \<open>cos\<close> needs \<open>sqrt 3 \<cdot> sqrt 3 = 3\<close>.\<close>
  have c2: "cos (2*pi/3) = - (1/2)"
  proof -
    have "cos (2*pi/3) = cos (pi/3 + pi/3)" by simp
    also have "\<dots> = cos (pi/3) * cos (pi/3) - sin (pi/3) * sin (pi/3)"
      by (rule cos_add)
    also have "\<dots> = 1/2 * (1/2) - sqrt 3 / 2 * (sqrt 3 / 2)"
      by (simp only: c3 s3)
    also have "\<dots> = 1/4 - 3 / 4" by (simp add: sqrt3_sq)
    also have "\<dots> = - (1/2)" by simp
    finally show ?thesis .
  qed
  have s2: "sin (2*pi/3) = sqrt 3 / 2"
  proof -
    have "sin (2*pi/3) = sin (pi/3 + pi/3)" by simp
    also have "\<dots> = sin (pi/3) * cos (pi/3) + cos (pi/3) * sin (pi/3)"
      by (rule sin_add)
    also have "\<dots> = sqrt 3 / 2" by (simp add: c3 s3)
    finally show ?thesis .
  qed

  text \<open>\<open>4\<pi>/3 = \<pi> + \<pi>/3\<close>: both are linear in \<open>sqrt 3\<close>.\<close>
  have c4: "cos (4*pi/3) = - (1/2)"
  proof -
    have "cos (4*pi/3) = cos (pi + pi/3)" by simp
    also have "\<dots> = cos pi * cos (pi/3) - sin pi * sin (pi/3)" by (rule cos_add)
    also have "\<dots> = - (1/2)" by (simp add: c3 s3)
    finally show ?thesis .
  qed
  have s4: "sin (4*pi/3) = - (sqrt 3 / 2)"
  proof -
    have "sin (4*pi/3) = sin (pi + pi/3)" by simp
    also have "\<dots> = sin pi * cos (pi/3) + cos pi * sin (pi/3)" by (rule sin_add)
    also have "\<dots> = - (sqrt 3 / 2)" by (simp add: c3 s3)
    finally show ?thesis .
  qed

  text \<open>\<open>5\<pi>/3 = \<pi> + 2\<pi>/3\<close>: reuse the \<open>2\<pi>/3\<close> values.\<close>
  have c5: "cos (5*pi/3) = 1/2"
  proof -
    have "cos (5*pi/3) = cos (pi + 2*pi/3)" by simp
    also have "\<dots> = cos pi * cos (2*pi/3) - sin pi * sin (2*pi/3)" by (rule cos_add)
    also have "\<dots> = 1/2" by (simp add: c2 s2)
    finally show ?thesis .
  qed
  have s5: "sin (5*pi/3) = - (sqrt 3 / 2)"
  proof -
    have "sin (5*pi/3) = sin (pi + 2*pi/3)" by simp
    also have "\<dots> = sin pi * cos (2*pi/3) + cos pi * sin (2*pi/3)" by (rule sin_add)
    also have "\<dots> = - (sqrt 3 / 2)" by (simp add: c2 s2)
    finally show ?thesis .
  qed

  show "cos (0::real) = 1" by simp
  show "sin (0::real) = 0" by simp
  show "cos (pi/3) = 1/2" by (rule c3)
  show "sin (pi/3) = sqrt 3 / 2" by (rule s3)
  show "cos (2*pi/3) = - (1/2)" by (rule c2)
  show "sin (2*pi/3) = sqrt 3 / 2" by (rule s2)
  show "cos pi = - 1" by simp
  show "sin pi = 0" by simp
  show "cos (4*pi/3) = - (1/2)" by (rule c4)
  show "sin (4*pi/3) = - (sqrt 3 / 2)" by (rule s4)
  show "cos (5*pi/3) = 1/2" by (rule c5)
  show "sin (5*pi/3) = - (sqrt 3 / 2)" by (rule s5)
qed


text \<open>
  Real-linear transports between the moment map's natural domain/codomain
  \<open>(\<real>\<^sup>2)\<^sup>6\<close>, \<open>\<complex>\<^sup>6\<close> and the \<open>\<real>\<^sup>1\<^sup>2\<close> used by \<^const>\<open>bigJ\<close>, plus the
  Jacobian identification \<open>D\<^sub>x M_paper(x0, c0) = (*v) bigJ\<close>.

  \<^bold>\<open>Why this lives here\<close> (and not in \<open>Nonemptiness_Paper\<close>): the nested
  vec-projection \<open>(c$i)$j\<close> in \<^term>\<open>transD_inv\<close> elaborates in milliseconds in
  this \<open>HMA_Connect\<close>/\<open>Conformal_Mappings\<close>-free context, but \<^emph>\<open>hangs / runs out of
  store\<close> when those theories are in scope (as they are in \<open>Nonemptiness_Paper\<close>).
  Baking the definitions into the \<open>Applied_Math_BlockDet\<close> heap means downstream
  theories merely \<^emph>\<open>use\<close> the constants (no re-elaboration of the definition).

  \<^bold>\<open>Proof engineering\<close>: each vec equality is reduced to per-component facts
  discharged by a \<^emph>\<open>bounded\<close> \<open>exhaust_N\<close> case split; a blanket
  \<open>forall_12\<close>/\<open>vec_eq_iff\<close> simp over the nested \<open>vector[\<dots>]\<close> exhausts memory.
\<close>

definition transC :: "complex^6 \<Rightarrow> real^12" where
  "transC z = vector
     [ Re (z$1), Im (z$1), Re (z$2), Im (z$2), Re (z$3), Im (z$3),
       Re (z$4), Im (z$4), Re (z$5), Im (z$5), Re (z$6), Im (z$6) ]"

definition transC_inv :: "real^12 \<Rightarrow> complex^6" where
  "transC_inv y = vector
     [ Complex (y$1)  (y$2),  Complex (y$3)  (y$4),  Complex (y$5)  (y$6),
       Complex (y$7)  (y$8),  Complex (y$9)  (y$10), Complex (y$11) (y$12) ]"

definition transD :: "real^12 \<Rightarrow> (real^2)^6" where
  "transD y = vector
     [ vector [y$1,  y$2],  vector [y$3,  y$4],  vector [y$5,  y$6],
       vector [y$7,  y$8],  vector [y$9,  y$10], vector [y$11, y$12] ]"

definition transD_inv :: "(real^2)^6 \<Rightarrow> real^12" where
  "transD_inv c = vector
     [ (c$1)$1, (c$1)$2, (c$2)$1, (c$2)$2, (c$3)$1, (c$3)$2,
       (c$4)$1, (c$4)$2, (c$5)$1, (c$5)$2, (c$6)$1, (c$6)$2 ]"

lemma linear_transC: "linear transC"
proof (rule linearI)
  fix z w :: "complex^6"
  have "transC (z + w) $ i = (transC z + transC w) $ i" for i :: 12
    using exhaust_12[of i] by (elim disjE; simp add: transC_def)
  thus "transC (z + w) = transC z + transC w" by (simp add: vec_eq_iff)
next
  fix r :: real and z :: "complex^6"
  have "transC (r *\<^sub>R z) $ i = (r *\<^sub>R transC z) $ i" for i :: 12
    using exhaust_12[of i] by (elim disjE; simp add: transC_def)
  thus "transC (r *\<^sub>R z) = r *\<^sub>R transC z" by (simp add: vec_eq_iff)
qed

lemma linear_transD: "linear transD"
proof (rule linearI)
  fix y w :: "real^12"
  have "transD (y + w) $ i = (transD y + transD w) $ i" for i :: 6
    using exhaust_6[of i] by (elim disjE; simp add: transD_def vec_eq_iff forall_2)
  thus "transD (y + w) = transD y + transD w" by (simp add: vec_eq_iff)
next
  fix r :: real and y :: "real^12"
  have "transD (r *\<^sub>R y) $ i = (r *\<^sub>R transD y) $ i" for i :: 6
    using exhaust_6[of i] by (elim disjE; simp add: transD_def vec_eq_iff forall_2)
  thus "transD (r *\<^sub>R y) = r *\<^sub>R transD y" by (simp add: vec_eq_iff)
qed

lemma transC_inv_left: "transC_inv (transC z) = z"
proof -
  have "transC_inv (transC z) $ i = z $ i" for i :: 6
    using exhaust_6[of i] by (elim disjE; simp add: transC_def transC_inv_def)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma transC_inv_right: "transC (transC_inv y) = y"
proof -
  have "transC (transC_inv y) $ i = y $ i" for i :: 12
    using exhaust_12[of i] by (elim disjE; simp add: transC_def transC_inv_def)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma transD_inv_left: "transD_inv (transD y) = y"
proof -
  have "transD_inv (transD y) $ i = y $ i" for i :: 12
    using exhaust_12[of i] by (elim disjE; simp add: transD_def transD_inv_def)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma transD_inv_right: "transD (transD_inv c) = c"
proof -
  have "transD (transD_inv c) $ i = c $ i" for i :: 6
    using exhaust_6[of i] by (elim disjE; simp add: transD_def transD_inv_def vec_eq_iff forall_2)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma bij_transC: "bij transC"
  by (rule o_bij[of transC_inv transC])
     (simp_all add: fun_eq_iff transC_inv_left transC_inv_right)

lemma bij_transD: "bij transD"
  by (rule o_bij[of transD_inv transD])
     (simp_all add: fun_eq_iff transD_inv_left transD_inv_right)


subsection \<open>Connecting the moment map to \<^const>\<open>bigJ\<close>: phase reduction at the base point\<close>

text \<open>
  Because \<open>c0_paper = (1,0)\<close>, the steering form \<open>c0_paper \<bullet> w\<close> is just the first
  coordinate \<open>w$1\<close>. Hence the phase factor at the base configuration collapses to
  \<open>cis(-u_n)\<close> with \<open>u_n = (x0_paper$n)$1\<close> the equally-spaced base angles, and its
  real/imaginary parts are \<open>cos u_n\<close>, \<open>-sin u_n\<close> --- known in closed form
  (\<open>base_trig_values\<close>). This is the bridge from the symbolic moment-map
  derivative to the explicit numeric entries of \<^const>\<open>bigJ\<close>.
\<close>

lemma c0_dot: "c0_paper \<bullet> (w::planar) = w $ 1"
proof -
  have "(UNIV::2 set) = {1, 2}" using exhaust_2 by auto
  thus ?thesis by (simp add: inner_vec_def  sum_2)
qed

lemma phase_c0_x0: "phase c0_paper x0_paper n = cis (- ((x0_paper $ n) $ 1))"
  by (simp add: phase_def c0_dot)

text \<open>The steering form applied to a perturbation direction: also its first coordinate.\<close>

lemma d_phase_c0_x0:
  "d_phase c0_paper x0_paper h n
     = - ((h $ n) $ 1) *\<^sub>R (\<i> * cis (- ((x0_paper $ n) $ 1)))"
  by (simp add: d_phase_def c0_dot)


subsection \<open>The Jacobian identification \<open>D\<^sub>x M_paper(x0,c0) = (*v) bigJ\<close>\<close>

definition MJ :: "real^12 \<Rightarrow> real^12" where
  "MJ = transC \<circ> (DM_paper_x x0_paper c0_paper) \<circ> transD"

lemma linear_MJ: "linear MJ"
  unfolding MJ_def
  by (intro linear_compose linear_transC linear_transD
            bounded_linear.linear[OF bounded_linear_DM_paper_x])

text \<open>
  The 12 columns of \<open>matrix MJ\<close>: for each standard basis direction \<open>axis j 1\<close>
  the moment sums collapse to the single base-point term it touches, and the
  resulting \<open>complex^6\<close> (real/imaginary parts via \<open>base_trig_values\<close>) is exactly
  the \<open>j\<close>-th column of \<^const>\<open>bigJ\<close>. Optimized simp set: \<open>DM_paper_x_components\<close>
  and \<open>cos pi\<close>/\<open>sin pi\<close> are already \<open>[simp]\<close>, so they are omitted here.
\<close>

lemmas MJ_col_simps =
  MJ_def transD_def transC_def axis_def
  d_A_moment_x_def d_M1_moment_x_def d_M2_moment_x_def
  d_M11_moment_x_def d_M12_moment_x_def d_M22_moment_x_def
  sum_6 phase_c0_x0 d_phase_c0_x0 bigJ_def
  base_trig_values(1,2,3,4,5,6,9,10,11,12)
  power_divide power_mult_distrib

lemma MJ_col1: "MJ (axis (1::12) 1) = (\<chi> i. bigJ $ i $ 1)"
proof -
  have "MJ (axis (1::12) 1) $ i = bigJ $ i $ 1" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col2: "MJ (axis (2::12) 1) = (\<chi> i. bigJ $ i $ 2)"
proof -
  have "MJ (axis (2::12) 1) $ i = bigJ $ i $ 2" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col3: "MJ (axis (3::12) 1) = (\<chi> i. bigJ $ i $ 3)"
proof -
  have "MJ (axis (3::12) 1) $ i = bigJ $ i $ 3" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col4: "MJ (axis (4::12) 1) = (\<chi> i. bigJ $ i $ 4)"
proof -
  have "MJ (axis (4::12) 1) $ i = bigJ $ i $ 4" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col5: "MJ (axis (5::12) 1) = (\<chi> i. bigJ $ i $ 5)"
proof -
  have "MJ (axis (5::12) 1) $ i = bigJ $ i $ 5" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col6: "MJ (axis (6::12) 1) = (\<chi> i. bigJ $ i $ 6)"
proof -
  have "MJ (axis (6::12) 1) $ i = bigJ $ i $ 6" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col7: "MJ (axis (7::12) 1) = (\<chi> i. bigJ $ i $ 7)"
proof -
  have "MJ (axis (7::12) 1) $ i = bigJ $ i $ 7" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col8: "MJ (axis (8::12) 1) = (\<chi> i. bigJ $ i $ 8)"
proof -
  have "MJ (axis (8::12) 1) $ i = bigJ $ i $ 8" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col9: "MJ (axis (9::12) 1) = (\<chi> i. bigJ $ i $ 9)"
proof -
  have "MJ (axis (9::12) 1) $ i = bigJ $ i $ 9" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col10: "MJ (axis (10::12) 1) = (\<chi> i. bigJ $ i $ 10)"
proof -
  have "MJ (axis (10::12) 1) $ i = bigJ $ i $ 10" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col11: "MJ (axis (11::12) 1) = (\<chi> i. bigJ $ i $ 11)"
proof -
  have "MJ (axis (11::12) 1) $ i = bigJ $ i $ 11" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

lemma MJ_col12: "MJ (axis (12::12) 1) = (\<chi> i. bigJ $ i $ 12)"
proof -
  have "MJ (axis (12::12) 1) $ i = bigJ $ i $ 12" for i :: 12
    using exhaust_12[of i] dw_M12_def w_M12_def
    by (elim disjE, simp_all add: MJ_col_simps)
  then show ?thesis by (metis (no_types, lifting) ext vec_lambda_eta)
qed

text \<open>Assembling the columns: \<open>matrix MJ = bigJ\<close>, hence \<open>MJ = (*v) bigJ\<close>.\<close>

lemma matrix_MJ: "matrix MJ = bigJ"
proof -
  have cols: "MJ (axis (j::12) 1) = (\<chi> i. bigJ $ i $ j)" for j :: 12
    using exhaust_12[of j]
    by (elim disjE)
       (simp_all add: MJ_col1 MJ_col2 MJ_col3 MJ_col4 MJ_col5 MJ_col6
                      MJ_col7 MJ_col8 MJ_col9 MJ_col10 MJ_col11 MJ_col12)
  have "matrix MJ $ i $ j = bigJ $ i $ j" for i j :: 12
    using cols by (simp add: matrix_def)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma MJ_eq_bigJ: "MJ = (*v) bigJ"
proof -
  have "(*v) (matrix MJ) = MJ"
    by (simp add: linear_MJ) 
  thus ?thesis by (simp add: matrix_MJ)
qed

text \<open>
  \<^bold>\<open>The connection to the actual function.\<close> The Fréchet derivative of the genuine
  moment map \<^const>\<open>M_paper\<close> at the base configuration, transported into
  \<open>\<real>\<^sup>1\<^sup>2\<close>-coordinates, \<^emph>\<open>is\<close> the explicit matrix \<^const>\<open>bigJ\<close>. Surjectivity of the
  derivative therefore follows from \<open>bigJ_surj\<close>.
\<close>

lemma surj_DM_paper_base: "surj (DM_paper_x x0_paper c0_paper)"
proof -
  have surjMJ: "surj MJ" using bigJ_surj by (simp add: MJ_eq_bigJ)
  have surjCi: "surj transC_inv" by (metis surjI transC_inv_left)
  have surjDi: "surj transD_inv" by (metis surjI transD_inv_left)
  have dm: "DM_paper_x x0_paper c0_paper = transC_inv \<circ> MJ \<circ> transD_inv"
    by (rule ext) (simp add: MJ_def transC_inv_left transD_inv_right)
  show ?thesis
    using comp_surj[OF surjDi comp_surj[OF surjMJ surjCi]] dm by simp
qed

text \<open>
  The base point is not merely \<^emph>\<open>regular\<close> (surjective derivative) but
  \<^emph>\<open>non-degenerate\<close>: the transported Jacobian has nonzero determinant
  \<open>det bigJ = -(5\<cdot>\<pi>\<^sup>8)/3 \<noteq> 0\<close>. This is the seed of the open-dense argument
  (P1.6): the determinant is a nontrivial real-analytic function of the
  configuration, so its zero set is nowhere dense.
\<close>

lemma det_matrix_MJ: "det (matrix MJ) = det bigJ"
  by (simp add: matrix_MJ)

lemma det_matrix_MJ_nonzero: "det (matrix MJ) \<noteq> 0"
  using bigJ_det_nonzero by (simp add: matrix_MJ)

end
