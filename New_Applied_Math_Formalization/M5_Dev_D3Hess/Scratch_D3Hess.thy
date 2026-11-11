theory Scratch_D3Hess
  imports "Applied_Math_M5_Wiring.Scratch_Wiring"
begin

section \<open>Toward closing the arc-bridge's degenerate residual: HessU's
  rank-1 kernel direction via the (e_par, perp2 e_par) basis\<close>

text \<open>Goal: the arc-bridge (\<open>Scratch_ArcBridge.thy\<close>) needs, at a critical
  point \<open>(x,\<omega>=\<phi> t)\<close> with \<open>det HessU = 0\<close>, that \<open>HessU \<bullet>v D\<phi> t\<close> has SOME
  nonzero component (else `t` cannot be eliminated at all -- the arc's
  velocity lies exactly in \<open>ker HessU\<close>).  \<open>Phi_par\<close>'s already-proven
  \<open>\<omega>\<close>-derivative dictionary gives, AT a critical point, the RADIAL
  projection of \<open>HessU \<bullet>v h\<close> for ANY direction \<open>h\<close>, with no det-HessU
  hypothesis at all:
    \<open>d/d\<omega>[Phi_par](h) = (HessU \<bullet>v h) \<bullet> e_par\<close>.
  Decomposing an arbitrary \<open>h\<close> (in particular \<open>h = D\<phi> t\<close>) into its
  \<open>e_par\<close>/\<open>perp2 e_par\<close> components turns this into a genuinely COMPUTABLE
  linear combination of \<open>H_par\<close> (already in closed radial form) and a
  "cross" term \<open>H_cross\<close>, itself just another instance of the SAME
  \<open>Phi_par\<close> \<omega>-derivative dictionary at \<open>h = perp2 e_par\<close>.\<close>

definition H_cross :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "H_cross x \<omega> \<omega>0 \<omega>s
     = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v perp2 (e_par \<omega>0 \<omega>s \<omega>))
         \<bullet> e_par \<omega>0 \<omega>s \<omega>"

lemma H_cross_eq_Phi_par_omega_critical:
  fixes x :: "(real^2)^'n::finite" and \<omega>0 \<omega>s \<omega> :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "H_cross x \<omega> \<omega>0 \<omega>s
      = frechet_derivative (\<lambda>\<eta>. Phi_par x \<eta> \<omega>0 \<omega>s) (at \<omega>) (perp2 (e_par \<omega>0 \<omega>s \<omega>))"
  unfolding H_cross_def
  by (rule frechet_derivative_Phi_par_omega_critical[OF detnz gnz crit, symmetric])

text \<open>The basic bilinear decomposition: for ANY \<open>h\<close>, writing it in the
  (orthogonal, equal-length) \<open>e_par\<close>/\<open>perp2 e_par\<close> basis expresses
  \<open>(HessU \<bullet>v h) \<bullet> e_par\<close> as a linear combination of \<open>H_par\<close> and
  \<open>H_cross\<close> alone -- no \<open>H_perp\<close> needed for THIS (the radial-row) direction.\<close>

lemma HessU_radial_row_decomp:
  fixes x :: "(real^2)^'n::finite" and \<omega>0 \<omega>s \<omega> h :: "real^2"
  assumes enz: "e_par \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "(HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v h) \<bullet> e_par \<omega>0 \<omega>s \<omega>
      = (h \<bullet> e_par \<omega>0 \<omega>s \<omega> / (e_par \<omega>0 \<omega>s \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>)) * H_par x \<omega> \<omega>0 \<omega>s
      + (h \<bullet> perp2 (e_par \<omega>0 \<omega>s \<omega>) / (e_par \<omega>0 \<omega>s \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>)) * H_cross x \<omega> \<omega>0 \<omega>s"
proof -
  define e where "e = e_par \<omega>0 \<omega>s \<omega>"
  define p where "p = perp2 e"
  define \<rho>2 where "\<rho>2 = e \<bullet> e"
  have rnz: "\<rho>2 \<noteq> 0"
    unfolding \<rho>2_def e_def using enz by simp
  have porth: "p \<bullet> e = 0"
    unfolding p_def using perp2_orth[of e] by (simp add: inner_commute)
  have pnorm: "p \<bullet> p = \<rho>2"
    unfolding p_def \<rho>2_def
    by (simp add: perp2_def inner_vec_def sum_2 vector_2 algebra_simps)
  have hexp: "h = (h \<bullet> e / \<rho>2) *\<^sub>R e + (h \<bullet> p / \<rho>2) *\<^sub>R p"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 2
    have p1: "vec_nth p 1 = - vec_nth e 2"
      unfolding p_def by (rule perp2_component_1)
    have p2: "vec_nth p 2 = vec_nth e 1"
      unfolding p_def by (rule perp2_component_2)
    have he: "h \<bullet> e = vec_nth h 1 * vec_nth e 1 + vec_nth h 2 * vec_nth e 2"
      by (simp add: inner_vec_def sum_2)
    have hp: "h \<bullet> p = vec_nth h 1 * vec_nth p 1 + vec_nth h 2 * vec_nth p 2"
      by (simp add: inner_vec_def sum_2)
    have key: "(h \<bullet> e) * vec_nth e i + (h \<bullet> p) * vec_nth p i = vec_nth h i * \<rho>2"
      using exhaust_2[of i]
    proof
      assume i1: "i = 1"
      show ?thesis
        unfolding i1 he hp p1 p2 \<rho>2_def by (simp add: inner_vec_def sum_2 algebra_simps)
    next
      assume i2: "i = 2"
      show ?thesis
        unfolding i2 he hp p1 p2 \<rho>2_def by (simp add: inner_vec_def sum_2 algebra_simps)
    qed
    show "vec_nth h i
        = vec_nth ((h \<bullet> e / \<rho>2) *\<^sub>R e + (h \<bullet> p / \<rho>2) *\<^sub>R p) i"
      using rnz key by (simp add: vector_scaleR_component field_simps)
  qed
  have lin: "\<And>v w :: real^2. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v (v + w)) \<bullet> e
      = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v) \<bullet> e
        + (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v w) \<bullet> e"
    by (simp add: matrix_vector_right_distrib inner_add_left)
  have scal: "\<And>c v. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v (c *\<^sub>R v)) \<bullet> e
      = c * ((HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v) \<bullet> e)"
    by (simp add: matrix_vector_mult_scaleR)
  have "(HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v h) \<bullet> e
      = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>
          *v ((h \<bullet> e / \<rho>2) *\<^sub>R e + (h \<bullet> p / \<rho>2) *\<^sub>R p)) \<bullet> e"
    using hexp by simp
  also have "\<dots> = (h \<bullet> e / \<rho>2) * ((HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v e) \<bullet> e)
      + (h \<bullet> p / \<rho>2) * ((HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v p) \<bullet> e)"
    unfolding lin scal ..
  also have "(HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v e) \<bullet> e = H_par x \<omega> \<omega>0 \<omega>s"
    unfolding e_def by (rule H_par_eq_quadform[symmetric])
  also have "(HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v p) \<bullet> e = H_cross x \<omega> \<omega>0 \<omega>s"
    unfolding p_def e_def H_cross_def ..
  finally show ?thesis
    unfolding e_def p_def \<rho>2_def by simp
qed

definition H_perp :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "H_perp x \<omega> \<omega>0 \<omega>s
     = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v perp2 (e_par \<omega>0 \<omega>s \<omega>))
         \<bullet> perp2 (e_par \<omega>0 \<omega>s \<omega>)"

text \<open>The det-zero algebraic relation between the three entries, in the
  (non-orthonormal, equal-length) \<open>e_par\<close>/\<open>perp2 e_par\<close> basis: since that
  basis is an orthogonal rotation-and-scale of the standard one,
  \<open>det HessU\<close> is literally \<open>(H_par\<cdot>H_perp - H_cross\<^sup>2) / \<rho>\<^sup>4\<close>.\<close>

lemma HessU_det_via_par_cross_perp:
  fixes x :: "(real^2)^'n::finite" and \<omega>0 \<omega>s \<omega> :: "real^2"
  assumes enz: "e_par \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) * (e_par \<omega>0 \<omega>s \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>)\<^sup>2
      = H_par x \<omega> \<omega>0 \<omega>s * H_perp x \<omega> \<omega>0 \<omega>s - (H_cross x \<omega> \<omega>0 \<omega>s)\<^sup>2"
proof -
  define H where "H = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>"
  define e where "e = e_par \<omega>0 \<omega>s \<omega>"
  define p where "p = perp2 e"
  define \<rho>2 where "\<rho>2 = e \<bullet> e"
  have rnz: "\<rho>2 \<noteq> 0"
    unfolding \<rho>2_def e_def using enz by simp
  have porth: "p \<bullet> e = 0"
    unfolding p_def using perp2_orth[of e] by (simp add: inner_commute)
  have pnorm: "p \<bullet> p = \<rho>2"
    unfolding p_def \<rho>2_def
    by (simp add: perp2_def inner_vec_def sum_2 vector_2 algebra_simps)
  have sym: "H $ 1 $ 2 = H $ 2 $ 1"
    unfolding H_def by (rule HessU_dip_symmetric)
  \<comment> \<open>express \<open>e\<close>, \<open>p\<close> in coordinates and expand both sides by \<open>vec_nth\<close>/matrix
      arithmetic -- purely mechanical 2x2 algebra, no analytic content.\<close>
  have e1: "vec_nth p 1 = - vec_nth e 2"
    unfolding p_def by (rule perp2_component_1)
  have e2: "vec_nth p 2 = vec_nth e 1"
    unfolding p_def by (rule perp2_component_2)
  have detH: "det H = H $ 1 $ 1 * H $ 2 $ 2 - H $ 1 $ 2 * H $ 2 $ 1"
    by (simp only: det_2)
  have Hpar: "H_par x \<omega> \<omega>0 \<omega>s = (H *v e) \<bullet> e"
    unfolding H_def e_def by (rule H_par_eq_quadform)
  have Hcross: "H_cross x \<omega> \<omega>0 \<omega>s = (H *v p) \<bullet> e"
    unfolding H_def e_def p_def H_cross_def ..
  have Hperp: "H_perp x \<omega> \<omega>0 \<omega>s = (H *v p) \<bullet> p"
    unfolding H_def e_def p_def H_perp_def ..
  have expand_par: "(H *v e) \<bullet> e
      = H $ 1 $ 1 * (vec_nth e 1)\<^sup>2 + 2 * H $ 1 $ 2 * vec_nth e 1 * vec_nth e 2
        + H $ 2 $ 2 * (vec_nth e 2)\<^sup>2"
    using sym by (simp add: matrix_vector_mult_def inner_vec_def sum_2 power2_eq_square algebra_simps)
  have expand_cross: "(H *v p) \<bullet> e
      = H $ 1 $ 1 * vec_nth p 1 * vec_nth e 1 + H $ 1 $ 2 * vec_nth p 1 * vec_nth e 2
        + H $ 2 $ 1 * vec_nth p 2 * vec_nth e 1 + H $ 2 $ 2 * vec_nth p 2 * vec_nth e 2"
    using sym by (simp add: matrix_vector_mult_def inner_vec_def sum_2 algebra_simps)
  have expand_perp: "(H *v p) \<bullet> p
      = H $ 1 $ 1 * (vec_nth p 1)\<^sup>2 + 2 * H $ 1 $ 2 * vec_nth p 1 * vec_nth p 2
        + H $ 2 $ 2 * (vec_nth p 2)\<^sup>2"
    using sym by (simp add: matrix_vector_mult_def inner_vec_def sum_2 power2_eq_square algebra_simps)
  have "H_par x \<omega> \<omega>0 \<omega>s * H_perp x \<omega> \<omega>0 \<omega>s - (H_cross x \<omega> \<omega>0 \<omega>s)\<^sup>2
      = (det H) * ((vec_nth e 1)\<^sup>2 + (vec_nth e 2)\<^sup>2)\<^sup>2"
    unfolding Hpar Hcross Hperp expand_par expand_cross expand_perp detH e1 e2
    using sym by (simp add: power2_eq_square algebra_simps)
  also have "(vec_nth e 1)\<^sup>2 + (vec_nth e 2)\<^sup>2 = e \<bullet> e"
    by (simp add: inner_vec_def sum_2 power2_eq_square)
  finally show ?thesis
    unfolding H_def e_def[symmetric] by simp
qed

section \<open>The transversality scalar \<open>\<Xi>\<close>: does an arc's velocity lie in \<open>ker HessU\<close>?\<close>

text \<open>Sketch.md \<section>4: the basis-independent replacement for testing "component 1
  of \<open>HessU \<bullet>v D\<phi>(t)\<close>" -- \<open>\<Xi>(x) := (HessU(x,\<omega>0) \<bullet>v w) \<bullet> e_par(\<omega>0)\<close> for a frozen
  angle \<open>\<omega>0\<close> and frozen arc tangent \<open>w\<close>. \<open>\<Xi> = 0\<close> captures exactly "\<open>w \<in> ker HessU\<close>",
  nothing more or less -- so \<open>trans\<close> fails at a fixed \<open>t0\<close> iff \<open>\<Xi>(x) = 0\<close> there.\<close>

definition Xi :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "Xi x \<omega>0 \<omega>s \<omega> w = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v w) \<bullet> e_par \<omega>0 \<omega>s \<omega>"

text \<open>Free from \<open>HessU_radial_row_decomp\<close>: \<open>\<Xi>\<close> is a linear combination of \<open>H_par\<close>
  and \<open>H_cross\<close> alone, weighted by \<open>w\<close>'s components in the \<open>(e_par, perp2 e_par)\<close>
  basis.  This is Sketch.md \<section>6b/\<section>6d's opening move, now a one-line consequence
  of infrastructure already proven above -- no new analytic content.\<close>

lemma Xi_eq_par_cross_combo:
  fixes x :: "(real^2)^'n::finite" and \<omega>0 \<omega>s \<omega> w :: "real^2"
  assumes enz: "e_par \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "Xi x \<omega>0 \<omega>s \<omega> w
      = (w \<bullet> e_par \<omega>0 \<omega>s \<omega> / (e_par \<omega>0 \<omega>s \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>)) * H_par x \<omega> \<omega>0 \<omega>s
      + (w \<bullet> perp2 (e_par \<omega>0 \<omega>s \<omega>) / (e_par \<omega>0 \<omega>s \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>)) * H_cross x \<omega> \<omega>0 \<omega>s"
  unfolding Xi_def by (rule HessU_radial_row_decomp[OF enz])

text \<open>Sketch.md \<section>6f: the \<open>w \<parallel> e_par\<close> case is NOT degenerate for \<open>\<Xi>\<close> -- it
  makes \<open>\<Xi>\<close> collapse to the already-closed-form \<open>H_par\<close>, with no leftover
  \<open>perp2\<close>-direction term.  Free from bilinearity of the Hessian quadratic form.\<close>

lemma Xi_at_e_par: "Xi x \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) = H_par x \<omega> \<omega>0 \<omega>s"
  unfolding Xi_def by (rule H_par_eq_quadform[symmetric])

text \<open>The mirror case, Sketch.md \<section>6f/\<section>6g: \<open>w \<parallel> perp2(e_par)\<close> makes \<open>\<Xi>\<close>
  collapse to \<open>H_cross\<close> instead -- the residual sliver whose single-bump witness
  vanishes exactly (\<section>6g), needing a two-bump fix (not pursued here).\<close>

lemma Xi_at_perp2_e_par: "Xi x \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>)) = H_cross x \<omega> \<omega>0 \<omega>s"
  unfolding Xi_def H_cross_def ..

section \<open>A single-bump critical witness for \<open>\<Xi>\<close> (Sketch.md \<section>6d)\<close>

text \<open>One antenna at position \<open>p\<close>, all other \<open>CARD('n) - 1\<close> antennas at the
  origin.  This is a simpler family than the two-bump machinery used elsewhere
  (\<open>slot i w1 + slot j w2\<close>): \<open>\<Xi>\<close> is not a row-indexed determinant like
  \<open>Lambda_rad_ij\<close>/\<open>Lambda_cub_ij\<close>, so it needs no second bump for asymmetry, and
  the single-bump family works for an arbitrary \<open>p\<close> (not just \<open>p \<propto> c\<close>).\<close>

text \<open>The master computation: for ANY function \<open>h\<close> of the raw (uncontracted)
  pairwise-difference vector that is EVEN (\<open>h(-v) = h(v)\<close> -- true of every
  summand shape \<open>Wc\<close>/\<open>Wc_d1\<close>/\<open>Wc_dd\<close> actually use, since \<open>cos\<close> is even and each
  extra linear weight factor flips sign exactly enough times to cancel), the
  single-bump double pair-sum collapses to a two-term closed form.  This one
  lemma is the common engine behind all three closed forms below.\<close>

lemma single_bump_double_sum:
  fixes h :: "real^2 \<Rightarrow> real" and p :: "real^2" and i :: "'n::finite"
  assumes heven: "\<And>v. h (- v) = h v"
  shows "(\<Sum>n\<in>UNIV. \<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))
      = (1 + (real (CARD('n)) - 1)\<^sup>2) * h 0 + 2 * (real (CARD('n)) - 1) * h p"
proof -
  have cardpos: "0 < CARD('n)"
    using UNIV_I by (simp add: card_gt_0_iff)
  have cardreal: "real (CARD('n) - 1) = real (CARD('n)) - 1"
    using cardpos by simp
  have fin: "finite (UNIV::'n set)"
    by simp
  have row_ne: "(\<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))
      = h p + (real (CARD('n)) - 1) * h 0" if nne: "n \<noteq> i" for n :: 'n
  proof -
    have body: "h (vec_nth (slot i p) n - vec_nth (slot i p) m)
        = (if m = i then h p else h 0)" for m :: 'n
      using nne heven[of p] by (simp add: slot_nth)
    have "(\<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))
        = (\<Sum>m\<in>UNIV. if m = i then h p else h 0)"
      by (rule sum.cong[OF refl]) (rule body)
    also have "\<dots> = (if i = i then h p else h 0) + (\<Sum>m\<in>UNIV - {i}. if m = i then h p else h 0)"
      by (rule sum.remove[OF fin UNIV_I])
    also have "(\<Sum>m\<in>UNIV - {i}. if m = i then h p else h 0) = (\<Sum>m\<in>UNIV - {i}. h 0)"
      by (rule sum.cong[OF refl]) auto
    also have "\<dots> = real (card (UNIV - {i})) * h 0" by simp
    also have "card (UNIV - {i}) = CARD('n) - 1"
      by (simp add: card_Diff_singleton)
    finally show ?thesis using cardreal by simp
  qed
  have row_eq: "(\<Sum>m\<in>UNIV. h (vec_nth (slot i p) i - vec_nth (slot i p) m))
      = h 0 + (real (CARD('n)) - 1) * h p"
  proof -
    have body: "h (vec_nth (slot i p) i - vec_nth (slot i p) m)
        = (if m = i then h 0 else h p)" for m :: 'n
      by (simp add: slot_nth)
    have "(\<Sum>m\<in>UNIV. h (vec_nth (slot i p) i - vec_nth (slot i p) m))
        = (\<Sum>m\<in>UNIV. if m = i then h 0 else h p)"
      by (rule sum.cong[OF refl]) (rule body)
    also have "\<dots> = (if i = i then h 0 else h p) + (\<Sum>m\<in>UNIV - {i}. if m = i then h 0 else h p)"
      by (rule sum.remove[OF fin UNIV_I])
    also have "(\<Sum>m\<in>UNIV - {i}. if m = i then h 0 else h p) = (\<Sum>m\<in>UNIV - {i}. h p)"
      by (rule sum.cong[OF refl]) auto
    also have "\<dots> = real (card (UNIV - {i})) * h p" by simp
    also have "card (UNIV - {i}) = CARD('n) - 1"
      by (simp add: card_Diff_singleton)
    finally show ?thesis using cardreal by simp
  qed
  have "(\<Sum>n\<in>UNIV. \<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))
      = (\<Sum>m\<in>UNIV. h (vec_nth (slot i p) i - vec_nth (slot i p) m))
        + (\<Sum>n\<in>UNIV - {i}. \<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))"
    by (rule sum.remove[OF fin UNIV_I])
    \<comment> \<open>note: LHS here matches the un-eta'd sum, so unification succeeds directly\<close>
  also have "(\<Sum>n\<in>UNIV - {i}. \<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))
      = (\<Sum>n\<in>UNIV - {i}. h p + (real (CARD('n)) - 1) * h 0)"
    by (rule sum.cong[OF refl]) (simp add: row_ne)
  also have "\<dots> = real (card (UNIV - {i})) * (h p + (real (CARD('n)) - 1) * h 0)"
    by simp
  also have "card (UNIV - {i}) = CARD('n) - 1"
    by (simp add: card_Diff_singleton)
  finally show ?thesis
    unfolding row_eq using cardreal by (simp add: algebra_simps power2_eq_square)
qed

lemma Wc_single_bump:
  fixes p c :: "real^2" and i :: "'n::finite"
  shows "Wc (slot i p) c
      = (real (CARD('n)) - 1)\<^sup>2 + 1 + 2 * (real (CARD('n)) - 1) * cos (c \<bullet> p)"
proof -
  have heven: "cos (c \<bullet> (- v)) = cos (c \<bullet> v)" for v :: "real^2"
    by simp
  have "Wc (slot i p) c
      = (\<Sum>n\<in>UNIV. \<Sum>m\<in>UNIV. cos (c \<bullet> (vec_nth (slot i p) n - vec_nth (slot i p) m)))"
    unfolding Wc_def ..
  also have "\<dots> = (1 + (real (CARD('n)) - 1)\<^sup>2) * cos (c \<bullet> 0)
      + 2 * (real (CARD('n)) - 1) * cos (c \<bullet> p)"
    using single_bump_double_sum[of "\<lambda>v. cos (c \<bullet> v)" i p] heven by simp
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma Wc_d1_single_bump:
  fixes p c d :: "real^2" and i :: "'n::finite"
  shows "Wc_d1 (slot i p) c d = - (2 * (real (CARD('n)) - 1) * (d \<bullet> p) * sin (c \<bullet> p))"
proof -
  define h where "h = (\<lambda>v::real^2. (d \<bullet> v) * sin (c \<bullet> v))"
  have heven: "h (- v) = h v" for v :: "real^2"
    unfolding h_def by simp
  have h0: "h 0 = 0"
    unfolding h_def by simp
  have "Wc_d1 (slot i p) c d
      = - (\<Sum>n\<in>UNIV. \<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))"
    unfolding Wc_d1_def h_def ..
  also have "(\<Sum>n\<in>UNIV. \<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))
      = 2 * (real (CARD('n)) - 1) * h p"
    using single_bump_double_sum[of h i p] heven h0 by simp
  finally show ?thesis
    unfolding h_def by simp
qed

lemma Wc_dd_single_bump:
  fixes p c d u :: "real^2" and i :: "'n::finite"
  shows "Wc_dd (slot i p) c d u
      = - (2 * (real (CARD('n)) - 1) * (d \<bullet> p) * (u \<bullet> p) * cos (c \<bullet> p))"
proof -
  define h where "h = (\<lambda>v::real^2. (d \<bullet> v) * (u \<bullet> v) * cos (c \<bullet> v))"
  have heven: "h (- v) = h v" for v :: "real^2"
    unfolding h_def by simp
  have h0: "h 0 = 0"
    unfolding h_def by simp
  have "Wc_dd (slot i p) c d u
      = - (\<Sum>n\<in>UNIV. \<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))"
    unfolding Wc_dd_def h_def ..
  also have "(\<Sum>n\<in>UNIV. \<Sum>m\<in>UNIV. h (vec_nth (slot i p) n - vec_nth (slot i p) m))
      = 2 * (real (CARD('n)) - 1) * h p"
    using single_bump_double_sum[of h i p] heven h0 by simp
  finally show ?thesis
    unfolding h_def by simp
qed

section \<open>Criticality along a direction \<open>h\<close>, in closed \<open>Wc\<close>/\<open>Wc_d1\<close> form\<close>

text \<open>Bridge \<open>gradU\<close> (an abstract \<open>\<nabla>\<close>/\<open>grad_fun\<close> THE-value) to the concrete
  \<open>Wc\<close>/\<open>Wc_d1\<close> closed form, via the already-proven factored derivative
  \<open>has_derivative_U_dip_omega_factored\<close> and the \<open>grad_fun\<close>/\<open>has_gradient\<close>
  dictionary from \<open>Higher_Differentiability_Multi.thy\<close>.  This is the missing
  link Sketch.md \<section>6d's (C1)/(C2) use by hand (\<open>\<nabla>_\<omega>U(x,\<omega>)\<cdot>k = gain\<cdot>Wc_d1(x,c;Dc(k))
  + g'(\<omega>$1)\<cdot>k$1\<cdot>Wc(x,c)\<close>).\<close>

lemma gradU_dip_dot:
  fixes x :: "(real^2)^'n::finite" and \<omega>0 \<omega>s \<omega> h :: "real^2"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> \<bullet> h
      = frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth h 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
        + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> h)"
proof -
  have hd: "((\<lambda>\<omega>'. U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>') has_derivative
      (\<lambda>h. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth h 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
         + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> h))) (at \<omega>)"
    by (rule has_derivative_U_dip_omega_factored)
  have diffb: "U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x differentiable (at \<omega>)"
    using hd by (rule differentiableI)
  obtain g where g: "GRAD (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x) \<omega> :> g"
    using Fr_diff_imp_gradient_exists[OF diffb] by blast
  have geq: "\<nabla> (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x) \<omega> = g"
    by (rule grad_fun_eq[OF g])
  have gradgrad: "GRAD (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x) \<omega> :> \<nabla> (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x) \<omega>"
    unfolding geq using g .
  have "(\<lambda>h. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth h 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
         + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> h)) h
      = h \<bullet> \<nabla> (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x) \<omega>"
    by (rule frechet_eq_inner_gradient[OF hd gradgrad])
  thus ?thesis
    unfolding gradU_def by (simp add: inner_commute)
qed

text \<open>Specialize to \<open>e_par\<close>/\<open>perp2 e_par\<close>: since \<open>Dc(e_par) = c\<close> (\<open>Dcvec_dip_e_par\<close> --
  \<open>e_par\<close> is BY CONSTRUCTION the direction pushing forward to \<open>c\<close>), criticality
  along \<open>e_par\<close> collapses \<open>Wc_d1\<close>'s direction argument to \<open>c\<close> itself, matching
  Sketch.md \<section>6d's (C1).\<close>

lemma gradU_dip_dot_e_par:
  fixes x :: "(real^2)^'n::finite" and \<omega>0 \<omega>s \<omega> :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>
      = frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
        + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>)"
  using gradU_dip_dot[of \<omega>0 \<omega>s x \<omega> "e_par \<omega>0 \<omega>s \<omega>"]
  unfolding Dcvec_dip_e_par[OF detnz] by simp

section \<open>Toward an isolated-zero (cubic) criterion: kx/ky/kz along a straight
  \<omega>-line, up to third order\<close>

text \<open>The remaining open question for D3 is whether \<open>Z(x0) = {\<omega> :
  gradU(x0,\<omega>)=0}\<close> can be genuinely 1-dimensional (not just isolated,
  possibly with higher multiplicity) at a point where \<open>det HessU(x0,\<omega>0)=0\<close>.
  Resolving this needs a THIRD \<omega>-derivative (cubic) invariant, analogous to
  but distinct from Tier 6's \<open>T3rad\<close> (which is a THIRD c-space radial
  derivative, not an \<omega>-space one).  First building block: the third
  derivative, along a straight \<omega>-line \<open>\<omega>0 + s \<bullet>\<^sub>R w\<close>, of \<open>kx\<close>/\<open>ky\<close>/\<open>kz\<close>
  (hence of \<open>cvec_dip\<close>, which is linear in these) -- pure mechanical
  calculus, no new abstraction, mirroring \<open>Wc_curve_d1/d2/d3\<close>'s style.\<close>

lemma kx_line_d1:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. kx (\<omega>0 + s *\<^sub>R w)) has_field_derivative
      (vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)))
      (at s)"
proof -
  have line1: "vec_nth (\<omega>0 + s *\<^sub>R w) 1 = vec_nth \<omega>0 1 + s * vec_nth w 1"
    by (simp add: vector_add_component vector_scaleR_component)
  have line2: "vec_nth (\<omega>0 + s *\<^sub>R w) 2 = vec_nth \<omega>0 2 + s * vec_nth w 2"
    by (simp add: vector_add_component vector_scaleR_component)
  have eqf: "(\<lambda>s. kx (\<omega>0 + s *\<^sub>R w))
      = (\<lambda>s. sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2))"
    by (rule ext) (simp add: kx_def line1 line2)
  show ?thesis
    unfolding eqf by (auto intro!: derivative_eq_intros)
qed

lemma kx_line_d2:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2))
      has_field_derivative
      (- ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2) * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - 2 * vec_nth w 1 * vec_nth w 2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)))
      (at s)"
  by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)

lemma kx_line_d3:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. - ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2) * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - 2 * vec_nth w 1 * vec_nth w 2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2))
      has_field_derivative
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)))
      (at s)"
  by (auto intro!: derivative_eq_intros simp: power2_eq_square power3_eq_cube algebra_simps)

text \<open>The chained value at \<open>s=0\<close>: the third \<open>s\<close>-derivative of \<open>kx(\<omega>0+s\<bullet>w)\<close>
  at \<open>s=0\<close>, obtained by composing \<open>kx_line_d1/d2/d3\<close> via \<open>DERIV_imp_deriv\<close> +
  \<open>deriv\<close>-uniqueness (each stage's function matches the next stage's premise
  function exactly, so the three \<open>has_field_derivative\<close> facts chain into a
  literal third-derivative-of-\<open>kx\<close>-along-the-line value).\<close>

lemma kx_line_third_deriv:
  fixes \<omega>0 w :: "real^2"
  shows "(deriv (deriv (deriv (\<lambda>s. kx (\<omega>0 + s *\<^sub>R w))))) 0
      = - (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1) * cos (vec_nth \<omega>0 2)
        + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1) * sin (vec_nth \<omega>0 2)"
proof -
  define d1 :: "real \<Rightarrow> real" where "d1 = (\<lambda>s.
      vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2))"
  define d2 :: "real \<Rightarrow> real" where "d2 = (\<lambda>s.
      - ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2) * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - 2 * vec_nth w 1 * vec_nth w 2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2))"
  have feq: "(\<lambda>s. kx (\<omega>0 + s *\<^sub>R w)) = (\<lambda>s. kx (\<omega>0 + s *\<^sub>R w))"
    by (rule refl)
  have step1: "deriv (\<lambda>s. kx (\<omega>0 + s *\<^sub>R w)) = d1"
    by (rule ext) (unfold d1_def, rule DERIV_imp_deriv[OF kx_line_d1])
  have step2: "deriv d1 = d2"
    unfolding d1_def by (rule ext) (unfold d2_def, rule DERIV_imp_deriv[OF kx_line_d2])
  have raw: "(d2 has_field_derivative
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1 + 0 * vec_nth w 1) * cos (vec_nth \<omega>0 2 + 0 * vec_nth w 2)
        + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1 + 0 * vec_nth w 1) * sin (vec_nth \<omega>0 2 + 0 * vec_nth w 2))) (at 0)"
    unfolding d2_def by (rule kx_line_d3)
  have d3at0: "(d2 has_field_derivative
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1) * cos (vec_nth \<omega>0 2)
        + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1) * sin (vec_nth \<omega>0 2))) (at 0)"
    using raw by simp
  have step3: "deriv d2 0 = - (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1) * cos (vec_nth \<omega>0 2)
        + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1) * sin (vec_nth \<omega>0 2)"
    by (rule DERIV_imp_deriv[OF d3at0])
  show ?thesis
    unfolding step1 step2 by (rule step3)
qed

lemma ky_line_d1:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. ky (\<omega>0 + s *\<^sub>R w)) has_field_derivative
      (vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)))
      (at s)"
proof -
  have line1: "vec_nth (\<omega>0 + s *\<^sub>R w) 1 = vec_nth \<omega>0 1 + s * vec_nth w 1"
    by (simp add: vector_add_component vector_scaleR_component)
  have line2: "vec_nth (\<omega>0 + s *\<^sub>R w) 2 = vec_nth \<omega>0 2 + s * vec_nth w 2"
    by (simp add: vector_add_component vector_scaleR_component)
  have eqf: "(\<lambda>s. ky (\<omega>0 + s *\<^sub>R w))
      = (\<lambda>s. sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2))"
    by (rule ext) (simp add: ky_def line1 line2)
  show ?thesis
    unfolding eqf by (auto intro!: derivative_eq_intros)
qed

lemma ky_line_d2:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2))
      has_field_derivative
      (- ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2) * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + 2 * vec_nth w 1 * vec_nth w 2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)))
      (at s)"
  by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)

lemma ky_line_d3:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. - ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2) * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + 2 * vec_nth w 1 * vec_nth w 2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2))
      has_field_derivative
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)))
      (at s)"
  by (auto intro!: derivative_eq_intros simp: power2_eq_square power3_eq_cube algebra_simps)

lemma ky_line_third_deriv:
  fixes \<omega>0 w :: "real^2"
  shows "(deriv (deriv (deriv (\<lambda>s. ky (\<omega>0 + s *\<^sub>R w))))) 0
      = - (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1) * sin (vec_nth \<omega>0 2)
        - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1) * cos (vec_nth \<omega>0 2)"
proof -
  define d1 :: "real \<Rightarrow> real" where "d1 = (\<lambda>s.
      vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2))"
  define d2 :: "real \<Rightarrow> real" where "d2 = (\<lambda>s.
      - ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2) * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + 2 * vec_nth w 1 * vec_nth w 2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2))"
  have step1: "deriv (\<lambda>s. ky (\<omega>0 + s *\<^sub>R w)) = d1"
    by (rule ext) (unfold d1_def, rule DERIV_imp_deriv[OF ky_line_d1])
  have step2: "deriv d1 = d2"
    unfolding d1_def by (rule ext) (unfold d2_def, rule DERIV_imp_deriv[OF ky_line_d2])
  have raw: "(d2 has_field_derivative
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1 + 0 * vec_nth w 1) * sin (vec_nth \<omega>0 2 + 0 * vec_nth w 2)
        - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1 + 0 * vec_nth w 1) * cos (vec_nth \<omega>0 2 + 0 * vec_nth w 2))) (at 0)"
    unfolding d2_def by (rule ky_line_d3)
  have d3at0: "(d2 has_field_derivative
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1) * sin (vec_nth \<omega>0 2)
        - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1) * cos (vec_nth \<omega>0 2))) (at 0)"
    using raw by simp
  have step3: "deriv d2 0 = - (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1) * sin (vec_nth \<omega>0 2)
        - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1) * cos (vec_nth \<omega>0 2)"
    by (rule DERIV_imp_deriv[OF d3at0])
  show ?thesis
    unfolding step1 step2 by (rule step3)
qed

lemma kz_line_d1:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. kz (\<omega>0 + s *\<^sub>R w)) has_field_derivative
      (- vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
proof -
  have line1: "vec_nth (\<omega>0 + s *\<^sub>R w) 1 = vec_nth \<omega>0 1 + s * vec_nth w 1"
    by (simp add: vector_add_component vector_scaleR_component)
  have eqf: "(\<lambda>s. kz (\<omega>0 + s *\<^sub>R w)) = (\<lambda>s. cos (vec_nth \<omega>0 1 + s * vec_nth w 1))"
    by (rule ext) (simp add: kz_def line1)
  show ?thesis
    unfolding eqf by (auto intro!: derivative_eq_intros)
qed

lemma kz_line_d2:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. - vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1)) has_field_derivative
      (- (vec_nth w 1)\<^sup>2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
  by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)

lemma kz_line_d3:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. - (vec_nth w 1)\<^sup>2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1)) has_field_derivative
      (vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
  by (auto intro!: derivative_eq_intros simp: power2_eq_square power3_eq_cube algebra_simps)

lemma kz_line_third_deriv:
  fixes \<omega>0 w :: "real^2"
  shows "(deriv (deriv (deriv (\<lambda>s. kz (\<omega>0 + s *\<^sub>R w))))) 0
      = vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1)"
proof -
  define d1 :: "real \<Rightarrow> real" where "d1 = (\<lambda>s. - vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1))"
  define d2 :: "real \<Rightarrow> real" where "d2 = (\<lambda>s. - (vec_nth w 1)\<^sup>2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1))"
  have step1: "deriv (\<lambda>s. kz (\<omega>0 + s *\<^sub>R w)) = d1"
    by (rule ext) (unfold d1_def, rule DERIV_imp_deriv[OF kz_line_d1])
  have step2: "deriv d1 = d2"
    unfolding d1_def by (rule ext) (unfold d2_def, rule DERIV_imp_deriv[OF kz_line_d2])
  have raw: "(d2 has_field_derivative (vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1 + 0 * vec_nth w 1))) (at 0)"
    unfolding d2_def by (rule kz_line_d3)
  have d3at0: "(d2 has_field_derivative (vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1))) (at 0)"
    using raw by simp
  have step3: "deriv d2 0 = vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1)"
    by (rule DERIV_imp_deriv[OF d3at0])
  show ?thesis
    unfolding step1 step2 by (rule step3)
qed

section \<open>\<open>cvec_dip\<close>'s own third derivative along a line, via linearity\<close>

text \<open>\<open>cvec_dip\<close> is a CONSTANT-coefficient linear combination of \<open>kx\<close>/\<open>ky\<close>/\<open>kz\<close>
  (the \<open>kx \<omega>s\<close>/\<open>ky \<omega>s\<close>/\<open>kz \<omega>s\<close> terms and the \<open>Dx\<close>/\<open>Dy\<close> ratio are all constants
  along the line \<open>\<omega>0+s\<bullet>w\<close>, since they only involve \<open>\<omega>0\<close>,\<open>\<omega>s\<close>), so its third
  derivative is exactly the SAME linear combination of \<open>kx_line_third_deriv\<close>,
  \<open>ky_line_third_deriv\<close>, \<open>kz_line_third_deriv\<close> -- no new differentiation.\<close>

lemma cvec_dip_line_comp1_d1:
  fixes \<omega>0 \<omega>s w :: "real^2"
  defines "Dx \<equiv> (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  shows "((\<lambda>s. vec_nth (cvec_dip \<omega>0 \<omega>s (\<omega>0 + s *\<^sub>R w)) 1) has_field_derivative
      ((vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
        - vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2))
       + Dx * (- vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1))))
      (at s)"
proof -
  have eqf: "(\<lambda>s. vec_nth (cvec_dip \<omega>0 \<omega>s (\<omega>0 + s *\<^sub>R w)) 1)
      = (\<lambda>s. (kx (\<omega>0 + s *\<^sub>R w) - kx \<omega>s) + Dx * (kz (\<omega>0 + s *\<^sub>R w) - kz \<omega>s))"
    unfolding Dx_def
    by (rule ext) (simp add: cvec_dip_def vector_add_component vector_scaleR_component axis_def)
  have dkx: "((\<lambda>s. kx (\<omega>0 + s *\<^sub>R w) - kx \<omega>s) has_field_derivative
      (vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)))
      (at s)"
    using DERIV_diff[OF kx_line_d1 DERIV_const] by simp
  have dkz: "((\<lambda>s. kz (\<omega>0 + s *\<^sub>R w) - kz \<omega>s) has_field_derivative
      (- vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
    using DERIV_diff[OF kz_line_d1 DERIV_const] by simp
  show ?thesis
    unfolding eqf using DERIV_add[OF dkx DERIV_cmult[OF dkz]] .
qed

lemma cvec_dip_line_comp2_d1:
  fixes \<omega>0 \<omega>s w :: "real^2"
  defines "Dy \<equiv> (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  shows "((\<lambda>s. vec_nth (cvec_dip \<omega>0 \<omega>s (\<omega>0 + s *\<^sub>R w)) 2) has_field_derivative
      ((vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
        + vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2))
       + Dy * (- vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1))))
      (at s)"
proof -
  have eqf: "(\<lambda>s. vec_nth (cvec_dip \<omega>0 \<omega>s (\<omega>0 + s *\<^sub>R w)) 2)
      = (\<lambda>s. (ky (\<omega>0 + s *\<^sub>R w) - ky \<omega>s) + Dy * (kz (\<omega>0 + s *\<^sub>R w) - kz \<omega>s))"
    unfolding Dy_def
    by (rule ext) (simp add: cvec_dip_def vector_add_component vector_scaleR_component axis_def)
  have dky: "((\<lambda>s. ky (\<omega>0 + s *\<^sub>R w) - ky \<omega>s) has_field_derivative
      (vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)))
      (at s)"
    using DERIV_diff[OF ky_line_d1 DERIV_const] by simp
  have dkz: "((\<lambda>s. kz (\<omega>0 + s *\<^sub>R w) - kz \<omega>s) has_field_derivative
      (- vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
    using DERIV_diff[OF kz_line_d1 DERIV_const] by simp
  show ?thesis
    unfolding eqf using DERIV_add[OF dky DERIV_cmult[OF dkz]] .
qed

lemma cvec_dip_line_comp1_third_deriv:
  fixes \<omega>0 \<omega>s w :: "real^2"
  defines "Dx \<equiv> (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  shows "(deriv (deriv (deriv (\<lambda>s. vec_nth (cvec_dip \<omega>0 \<omega>s (\<omega>0 + s *\<^sub>R w)) 1)))) 0
      = (deriv (deriv (deriv (\<lambda>s. kx (\<omega>0 + s *\<^sub>R w))))) 0
        + Dx * (deriv (deriv (deriv (\<lambda>s. kz (\<omega>0 + s *\<^sub>R w))))) 0"
proof -
  define d1 :: "real \<Rightarrow> real" where "d1 = (\<lambda>s.
      (vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
        - vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2))
       + Dx * (- vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1)))"
  define d2 :: "real \<Rightarrow> real" where "d2 = (\<lambda>s.
      (- ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2) * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2)
       - 2 * vec_nth w 1 * vec_nth w 2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2))
       + Dx * (- (vec_nth w 1)\<^sup>2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1)))"
  have step1: "deriv (\<lambda>s. vec_nth (cvec_dip \<omega>0 \<omega>s (\<omega>0 + s *\<^sub>R w)) 1) = d1"
    by (rule ext) (unfold d1_def Dx_def, rule DERIV_imp_deriv[OF cvec_dip_line_comp1_d1])
  have step2: "deriv d1 = d2"
    unfolding d1_def d2_def
    by (rule ext) (rule DERIV_imp_deriv[OF DERIV_add[OF kx_line_d2 DERIV_cmult[OF kz_line_d2]]])
  have raw: "(d2 has_field_derivative
      ((- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1 + 0 * vec_nth w 1) * cos (vec_nth \<omega>0 2 + 0 * vec_nth w 2)
        + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1 + 0 * vec_nth w 1) * sin (vec_nth \<omega>0 2 + 0 * vec_nth w 2))
       + Dx * (vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1 + 0 * vec_nth w 1)))) (at 0)"
    unfolding d2_def by (rule DERIV_add[OF kx_line_d3 DERIV_cmult[OF kz_line_d3]])
  have d3at0: "(d2 has_field_derivative
      ((- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1) * cos (vec_nth \<omega>0 2)
        + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1) * sin (vec_nth \<omega>0 2))
       + Dx * (vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1)))) (at 0)"
    using raw by simp
  have step3: "deriv d2 0 = (deriv (deriv (deriv (\<lambda>s. kx (\<omega>0 + s *\<^sub>R w))))) 0
        + Dx * (deriv (deriv (deriv (\<lambda>s. kz (\<omega>0 + s *\<^sub>R w))))) 0"
    unfolding kx_line_third_deriv kz_line_third_deriv
    by (rule DERIV_imp_deriv[OF d3at0])
  show ?thesis
    unfolding step1 step2 by (rule step3)
qed

lemma cvec_dip_line_comp2_third_deriv:
  fixes \<omega>0 \<omega>s w :: "real^2"
  defines "Dy \<equiv> (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  shows "(deriv (deriv (deriv (\<lambda>s. vec_nth (cvec_dip \<omega>0 \<omega>s (\<omega>0 + s *\<^sub>R w)) 2)))) 0
      = (deriv (deriv (deriv (\<lambda>s. ky (\<omega>0 + s *\<^sub>R w))))) 0
        + Dy * (deriv (deriv (deriv (\<lambda>s. kz (\<omega>0 + s *\<^sub>R w))))) 0"
proof -
  define d1 :: "real \<Rightarrow> real" where "d1 = (\<lambda>s.
      (vec_nth w 1 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
        + vec_nth w 2 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2))
       + Dy * (- vec_nth w 1 * sin (vec_nth \<omega>0 1 + s * vec_nth w 1)))"
  define d2 :: "real \<Rightarrow> real" where "d2 = (\<lambda>s.
      (- ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2) * sin (vec_nth \<omega>0 1 + s * vec_nth w 1) * sin (vec_nth \<omega>0 2 + s * vec_nth w 2)
       + 2 * vec_nth w 1 * vec_nth w 2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1) * cos (vec_nth \<omega>0 2 + s * vec_nth w 2))
       + Dy * (- (vec_nth w 1)\<^sup>2 * cos (vec_nth \<omega>0 1 + s * vec_nth w 1)))"
  have step1: "deriv (\<lambda>s. vec_nth (cvec_dip \<omega>0 \<omega>s (\<omega>0 + s *\<^sub>R w)) 2) = d1"
    by (rule ext) (unfold d1_def Dy_def, rule DERIV_imp_deriv[OF cvec_dip_line_comp2_d1])
  have step2: "deriv d1 = d2"
    unfolding d1_def d2_def
    by (rule ext) (rule DERIV_imp_deriv[OF DERIV_add[OF ky_line_d2 DERIV_cmult[OF kz_line_d2]]])
  have raw: "(d2 has_field_derivative
      ((- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1 + 0 * vec_nth w 1) * sin (vec_nth \<omega>0 2 + 0 * vec_nth w 2)
        - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1 + 0 * vec_nth w 1) * cos (vec_nth \<omega>0 2 + 0 * vec_nth w 2))
       + Dy * (vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1 + 0 * vec_nth w 1)))) (at 0)"
    unfolding d2_def by (rule DERIV_add[OF ky_line_d3 DERIV_cmult[OF kz_line_d3]])
  have d3at0: "(d2 has_field_derivative
      ((- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega>0 1) * sin (vec_nth \<omega>0 2)
        - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega>0 1) * cos (vec_nth \<omega>0 2))
       + Dy * (vec_nth w 1 ^ 3 * sin (vec_nth \<omega>0 1)))) (at 0)"
    using raw by simp
  have step3: "deriv d2 0 = (deriv (deriv (deriv (\<lambda>s. ky (\<omega>0 + s *\<^sub>R w))))) 0
        + Dy * (deriv (deriv (deriv (\<lambda>s. kz (\<omega>0 + s *\<^sub>R w))))) 0"
    unfolding ky_line_third_deriv kz_line_third_deriv
    by (rule DERIV_imp_deriv[OF d3at0])
  show ?thesis
    unfolding step1 step2 by (rule step3)
qed

definition D3cvec_dip_line :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "D3cvec_dip_line \<omega>0 \<omega>s \<omega> w =
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
       + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
       + ((kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0))
          * (vec_nth w 1 ^ 3 * sin (vec_nth \<omega> 1))) *\<^sub>R axis 1 1
    + (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
       - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
       + ((ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0))
          * (vec_nth w 1 ^ 3 * sin (vec_nth \<omega> 1))) *\<^sub>R axis 2 1"

lemma cvec_dip_line_has_vector_derivative:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2"
  shows "((\<lambda>s. cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w)) has_vector_derivative
      Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w) (at s)"
proof -
  have line: "((\<lambda>s. \<omega> + s *\<^sub>R w) has_derivative (\<lambda>r. r *\<^sub>R w)) (at s)"
    by (auto intro!: derivative_eq_intros)
  have cder: "((cvec_dip \<omega>0 \<omega>s) has_derivative
      Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w)) (at (\<omega> + s *\<^sub>R w))"
    by (rule has_derivative_cvec_dip)
  have comp: "((\<lambda>s. cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w)) has_derivative
      (Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) \<circ> (\<lambda>r. r *\<^sub>R w))) (at s)"
    using diff_chain_at[of "\<lambda>R. \<omega> + R *\<^sub>R w" "\<lambda>R. R *\<^sub>R w" s "cvec_dip \<omega>0 \<omega>s" "Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w)"]
      has_derivative_cvec_dip[of \<omega>0 \<omega>s "\<omega> + s *\<^sub>R w"]
      has_derivative_transform[of s UNIV "\<lambda>R. cvec_dip \<omega>0 \<omega>s (\<omega> + R *\<^sub>R w)" "cvec_dip \<omega>0 \<omega>s \<circ> (\<lambda>R. \<omega> + R *\<^sub>R w)"
        "Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) \<circ> (\<lambda>R. R *\<^sub>R w)"]
      line o_eq_dest_lhs[of "cvec_dip \<omega>0 \<omega>s" "\<lambda>R. \<omega> + R *\<^sub>R w" "cvec_dip \<omega>0 \<omega>s \<circ> (\<lambda>R. \<omega> + R *\<^sub>R w)"] by blast
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w))"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  show ?thesis
    unfolding has_vector_derivative_def
    by (rule has_derivative_eq_rhs[OF comp])
       (rule ext, simp add: o_def linear_cmul[OF lin])
qed

lemma cvec_dip_line_d1_has_vector_derivative:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2"
  shows "((\<lambda>s. Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w) has_vector_derivative
      D2cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w w) (at s)"
proof -
  have line: "((\<lambda>s. \<omega> + s *\<^sub>R w) has_derivative (\<lambda>r. r *\<^sub>R w)) (at s)"
    by (auto intro!: derivative_eq_intros)
  have dcder: "((\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y w) has_derivative
      D2cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w) (at (\<omega> + s *\<^sub>R w))"
    by (rule has_derivative_Dcvec_dip)
  have comp: "((\<lambda>s. Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w) has_derivative
      (D2cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w \<circ> (\<lambda>r. r *\<^sub>R w))) (at s)"
  proof -
    have "((\<lambda>v. Dcvec_dip \<omega>0 \<omega>s v w) \<circ> (\<lambda>r. \<omega> + r *\<^sub>R w) has_derivative D2cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w \<circ> (\<lambda>r. r *\<^sub>R w)) (at s)"
      by (simp add: dcder diff_chain_at line)
    then show ?thesis
      by (simp add: o_def)
  qed
  have lin: "linear (D2cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_Dcvec_dip]])
  show ?thesis
    unfolding has_vector_derivative_def
    by (rule has_derivative_eq_rhs[OF comp])
       (rule ext, simp add: o_def linear_cmul[OF lin])
qed

lemma cvec_dip_line_d2_has_vector_derivative:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2"
  shows "((\<lambda>s. D2cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w w) has_vector_derivative
      D3cvec_dip_line \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w) (at s)"
proof -
  define Dx where "Dx = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Dy where "Dy = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define f1 where "f1 = (\<lambda>r.
      (- ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2)
          * sin (vec_nth \<omega> 1 + r * vec_nth w 1)
          * cos (vec_nth \<omega> 2 + r * vec_nth w 2)
       - 2 * vec_nth w 1 * vec_nth w 2
          * cos (vec_nth \<omega> 1 + r * vec_nth w 1)
          * sin (vec_nth \<omega> 2 + r * vec_nth w 2))
       + Dx * (- (vec_nth w 1)\<^sup>2
          * cos (vec_nth \<omega> 1 + r * vec_nth w 1)))"
  define f2 where "f2 = (\<lambda>r.
      (- ((vec_nth w 1)\<^sup>2 + (vec_nth w 2)\<^sup>2)
          * sin (vec_nth \<omega> 1 + r * vec_nth w 1)
          * sin (vec_nth \<omega> 2 + r * vec_nth w 2)
       + 2 * vec_nth w 1 * vec_nth w 2
          * cos (vec_nth \<omega> 1 + r * vec_nth w 1)
          * cos (vec_nth \<omega> 2 + r * vec_nth w 2))
       + Dy * (- (vec_nth w 1)\<^sup>2
          * cos (vec_nth \<omega> 1 + r * vec_nth w 1)))"
  define g1 where "g1 =
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega> 1 + s * vec_nth w 1)
          * cos (vec_nth \<omega> 2 + s * vec_nth w 2)
       + (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega> 1 + s * vec_nth w 1)
          * sin (vec_nth \<omega> 2 + s * vec_nth w 2)
       + Dx * (vec_nth w 1 ^ 3
          * sin (vec_nth \<omega> 1 + s * vec_nth w 1)))"
  define g2 where "g2 =
      (- (vec_nth w 1 ^ 3 + 3 * vec_nth w 1 * (vec_nth w 2)\<^sup>2)
          * cos (vec_nth \<omega> 1 + s * vec_nth w 1)
          * sin (vec_nth \<omega> 2 + s * vec_nth w 2)
       - (3 * (vec_nth w 1)\<^sup>2 * vec_nth w 2 + vec_nth w 2 ^ 3)
          * sin (vec_nth \<omega> 1 + s * vec_nth w 1)
          * cos (vec_nth \<omega> 2 + s * vec_nth w 2)
       + Dy * (vec_nth w 1 ^ 3
          * sin (vec_nth \<omega> 1 + s * vec_nth w 1)))"
  have df1: "(f1 has_field_derivative g1) (at s)"
    unfolding f1_def g1_def
    by (rule DERIV_add[OF kx_line_d3 DERIV_cmult[OF kz_line_d3]])
  have df2: "(f2 has_field_derivative g2) (at s)"
    unfolding f2_def g2_def
    by (rule DERIV_add[OF ky_line_d3 DERIV_cmult[OF kz_line_d3]])
  have d1v: "((\<lambda>r. f1 r *\<^sub>R axis 1 1) has_vector_derivative
      g1 *\<^sub>R axis 1 1) (at s)"
    by (rule has_vector_derivative_eq_rhs[OF has_vector_derivative_scaleR[OF df1 has_vector_derivative_const]])
       simp
  have d2v: "((\<lambda>r. f2 r *\<^sub>R axis 2 1) has_vector_derivative
      g2 *\<^sub>R axis 2 1) (at s)"
    by (rule has_vector_derivative_eq_rhs[OF has_vector_derivative_scaleR[OF df2 has_vector_derivative_const]])
       simp
  have dsum: "((\<lambda>r. f1 r *\<^sub>R axis 1 1 + f2 r *\<^sub>R axis 2 1) has_vector_derivative
      g1 *\<^sub>R axis 1 1 + g2 *\<^sub>R axis 2 1) (at s)"
    by (rule has_vector_derivative_add[OF d1v d2v])
  have eqf: "(\<lambda>r. D2cvec_dip \<omega>0 \<omega>s (\<omega> + r *\<^sub>R w) w w)
      = (\<lambda>r. f1 r *\<^sub>R axis 1 1 + f2 r *\<^sub>R axis 2 1)"
  proof (rule ext, rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix r and i :: 2
    show "vec_nth (D2cvec_dip \<omega>0 \<omega>s (\<omega> + r *\<^sub>R w) w w) i
        = vec_nth (f1 r *\<^sub>R axis 1 1 + f2 r *\<^sub>R axis 2 1) i"
      using exhaust_2[of i]
    proof
      assume i1: "i = 1"
      show ?thesis
        unfolding i1
        by (simp add: D2cvec_dip_def f1_def Dx_def vector_add_component
            vector_scaleR_component axis_def power2_eq_square algebra_simps)
    next
      assume i2: "i = 2"
      show ?thesis
        unfolding i2
        by (simp add: D2cvec_dip_def f2_def Dy_def vector_add_component
            vector_scaleR_component axis_def power2_eq_square algebra_simps)
    qed
  qed
  have eqg: "D3cvec_dip_line \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w
      = g1 *\<^sub>R axis 1 1 + g2 *\<^sub>R axis 2 1"
    by (simp add: g1_def g2_def D3cvec_dip_line_def Dx_def Dy_def
        vector_add_component vector_scaleR_component axis_def
        power2_eq_square algebra_simps)
  show ?thesis
    unfolding eqf eqg by (rule dsum)
qed

section \<open>\<open>gain_dip\<close>'s third derivative along a line (needs the \<open>gdip\<close>/\<open>Jsinc\<close>
  higher-differentiability machinery, not raw \<open>derivative_eq_intros\<close>, since
  \<open>gdip\<close>'s \<open>gsinc\<close>-based formula has a removable-singularity structure)\<close>

lemma deriv_gdip_eq_frechet: "deriv gdip x = frechet_derivative gdip (at x) 1"
  using DERIV_deriv_iff_real_differentiable[THEN iffD2, OF gdip_differentiable, of x]
    frechet_derivative_works[THEN iffD1, OF gdip_differentiable, of x]
  by (simp only: g1_frechet_eval)

lemma deriv_gdip_has_field_derivative:
  "(gdip has_field_derivative deriv gdip x) (at x)"
  using DERIV_deriv_iff_real_differentiable[THEN iffD2, OF gdip_differentiable] .

lemma deriv2_gdip_has_field_derivative:
  "((\<lambda>t. deriv gdip t) has_field_derivative deriv (deriv gdip) x) (at x)"
proof -
  have d: "(\<lambda>t. frechet_derivative gdip (at t) 1) differentiable (at x)"
    using gdip_deriv_differentiable[of 1] .
  have eqf: "(\<lambda>t. deriv gdip t) = (\<lambda>t. frechet_derivative gdip (at t) 1)"
    by (rule ext) (rule deriv_gdip_eq_frechet)
  show ?thesis
    unfolding eqf
    using DERIV_deriv_iff_real_differentiable[THEN iffD2] d unfolding eqf[symmetric] by simp
qed

lemma gdip_deriv2_differentiable:
  fixes t :: real
  shows "(\<lambda>t. frechet_derivative (\<lambda>y. frechet_derivative gdip (at y) v) (at t) v) differentiable (at t)"
proof -
  have h3: "higher_differentiable_on UNIV (\<lambda>y. frechet_derivative gdip (at y) v) (Suc 1)"
    using gdip_higher_differentiable_on[of "Suc (Suc 1)"]
    by (simp add: higher_differentiable_on.simps(2))
  have h2: "higher_differentiable_on UNIV
      (\<lambda>y. frechet_derivative (\<lambda>z. frechet_derivative gdip (at z) v) (at y) v) 1"
    using h3 by (simp only: higher_differentiable_on.simps(2))
  hence "(\<lambda>y. frechet_derivative (\<lambda>z. frechet_derivative gdip (at z) v) (at y) v) differentiable_on UNIV"
    by (rule higher_differentiable_on_imp_differentiable_on) simp
  thus ?thesis by (simp add: differentiable_on_def)
qed

lemma deriv3_gdip_has_field_derivative:
  "((\<lambda>t. deriv (deriv gdip) t) has_field_derivative deriv (deriv (deriv gdip)) x) (at x)"
proof -
  have d: "(\<lambda>t. frechet_derivative (\<lambda>y. frechet_derivative gdip (at y) 1) (at t) 1) differentiable (at x)"
    using gdip_deriv2_differentiable[of 1] .
  have eqf1: "(\<lambda>y. frechet_derivative gdip (at y) 1) = deriv gdip"
    by (rule ext) (rule deriv_gdip_eq_frechet[symmetric])
  have eqf2: "(\<lambda>t. frechet_derivative (\<lambda>y. frechet_derivative gdip (at y) 1) (at t) 1)
      = deriv (deriv gdip)"
    unfolding eqf1
    using DERIV_deriv_gdip g1_frechet_eval by blast    
  have d': "(\<lambda>t. deriv (deriv gdip) t) differentiable (at x)"
    using d unfolding eqf2 by simp
  show ?thesis
    using DERIV_deriv_iff_real_differentiable[THEN iffD2, OF d'] .
qed

section \<open>The critical-point-simplified \<open>HessU\<close> moment formula\<close>

text \<open>At a critical point (\<open>gradU = 0\<close>), \<open>HessU_dip_entry_moments\<close>'s raw formula's
  three "mixed" terms (each carrying a factor \<open>Dcvec_dip(e_k) \<bullet> \<nabla>\<^sub>cV\<close> or
  \<open>Dcvec_dip(e_l) \<bullet> \<nabla>\<^sub>cV\<close>) collapse via \<open>gradU_dip_component_field = 0\<close>, leaving a
  genuinely closed "radial-jet" form with no leftover cross term -- the same
  simplification \<open>Hrad2\<close> exploits for the diagonal \<open>k=l=par\<close> case, here done for
  ANY \<open>k,l\<close> in one pass.  This is the formula Sketch.md sections 3/6 use by hand.\<close>

lemma frechet_derivative_deriv_gdip_omega:
  fixes \<omega> :: "real^2"
  shows "((\<lambda>\<eta>::real^2. deriv gdip (vec_nth \<eta> 1)) has_derivative
      (\<lambda>v. deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1)) (at \<omega>)"
proof -
  have step: "((deriv gdip \<circ> (\<lambda>\<eta>. vec_nth \<eta> 1)) has_derivative
      ((\<lambda>h. deriv (deriv gdip) (vec_nth \<omega> 1) * h) \<circ> (\<lambda>v. vec_nth v 1))) (at \<omega>)"
    by (rule diff_chain_at[OF has_derivative_proj
          has_field_derivative_imp_has_derivative[OF deriv2_gdip_has_field_derivative]])
  show ?thesis
    using step by (simp only: o_def mult.commute)
qed

lemma frechet_derivative_gdip_linear:
  fixes t c :: real
  shows "frechet_derivative gdip (at t) c = c * deriv gdip t"
proof -
  have "frechet_derivative gdip (at t) c = frechet_derivative gdip (at t) (c *\<^sub>R 1)"
    by simp
  also have "\<dots> = c *\<^sub>R frechet_derivative gdip (at t) 1"
    by (rule linear_cmul[OF bounded_linear.linear[OF
          has_derivative_bounded_linear[OF frechet_derivative_works[THEN iffD1,
            OF gdip_differentiable]]]])
  also have "\<dots> = c * deriv gdip t"
    by (simp add: deriv_gdip_eq_frechet)
  finally show ?thesis.
qed

section \<open>The single-bump criticality equations (C1)/(C2), Sketch.md \<section>6d\<close>

text \<open>(C1): criticality along \<open>e_par\<close>, evaluated on the single-bump family, as a
  scalar equation purely in the bump phase \<open>\<phi> := c \<bullet> p\<close> -- matches Sketch.md's
  \<open>F1(\<phi>) := -2 n1 g0 \<phi> sin \<phi> + g0' e_par$1 (n1\<^sup>2+1+2n1 cos\<phi>)\<close> exactly, with
  \<open>n1 = CARD('n) - 1\<close>, \<open>g0 = gain_dip \<omega>\<close>, \<open>g0' = deriv gdip (\<omega>$1)\<close>.\<close>

lemma gradU_dip_dot_e_par_single_bump:
  fixes p \<omega>0 \<omega>s \<omega> :: "real^2" and i :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>
      = - (2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p) * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))
        + deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * ((real (CARD('n)) - 1)\<^sup>2 + 1
             + 2 * (real (CARD('n)) - 1) * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))"
  unfolding gradU_dip_dot_e_par[OF detnz] Wc_single_bump Wc_d1_single_bump
  by (simp add: frechet_derivative_gdip_linear algebra_simps)

text \<open>(C2): criticality along \<open>perp2 e_par\<close> on the same family -- linear in the
  \<open>perp2(c)\<close>-offset once \<open>\<phi>\<close> is fixed, matching Sketch.md's linear-in-\<open>r\<close> equation.
  Here \<open>d_perp := Dc(perp2 e_par)\<close> is left abstract (Sketch.md \<section>6e's design-point
  computation instantiates it).\<close>

lemma gradU_dip_dot_perp2_e_par_single_bump:
  fixes p \<omega>0 \<omega>s \<omega> :: "real^2" and i :: "'n::finite"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> \<bullet> perp2 (e_par \<omega>0 \<omega>s \<omega>)
      = - (2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>)) \<bullet> p) * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))
        + deriv gdip (vec_nth \<omega> 1) * vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1
          * ((real (CARD('n)) - 1)\<^sup>2 + 1
             + 2 * (real (CARD('n)) - 1) * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))"
  using gradU_dip_dot[of \<omega>0 \<omega>s "slot i p" \<omega> "perp2 (e_par \<omega>0 \<omega>s \<omega>)"]
  unfolding Wc_single_bump Wc_d1_single_bump
  by (simp add: frechet_derivative_gdip_linear algebra_simps)

text \<open>The pure linear-algebra identity underlying the pivot fact: for ANY 2x2 matrix
  \<open>M\<close> and vector \<open>e\<close>, \<open>(M \<bullet>v perp2 e) \<bullet> perp2 (M \<bullet>v e) = det M \<cdot> (e\<bullet>e)\<close> -- no genericity
  hypothesis needed, pure mechanical 2x2 algebra (same style as
  \<open>HessU_det_via_par_cross_perp\<close> above).\<close>

lemma matrix_perp2_pivot_identity:
  fixes M :: "real^2^2" and e :: "real^2"
  shows "(M *v perp2 e) \<bullet> perp2 (M *v e) = det M * (e \<bullet> e)"
proof -
  have e1: "vec_nth (perp2 e) 1 = - vec_nth e 2"
    by (rule perp2_component_1)
  have e2: "vec_nth (perp2 e) 2 = vec_nth e 1"
    by (rule perp2_component_2)
  have p1: "vec_nth (perp2 (M *v e)) 1 = - vec_nth (M *v e) 2"
    by (rule perp2_component_1)
  have p2: "vec_nth (perp2 (M *v e)) 2 = vec_nth (M *v e) 1"
    by (rule perp2_component_2)
  have Mv1: "vec_nth (M *v e) 1 = M $ 1 $ 1 * vec_nth e 1 + M $ 1 $ 2 * vec_nth e 2"
    by (simp add: matrix_vector_mult_def sum_2)
  have Mv2: "vec_nth (M *v e) 2 = M $ 2 $ 1 * vec_nth e 1 + M $ 2 $ 2 * vec_nth e 2"
    by (simp add: matrix_vector_mult_def sum_2)
  have Mp1: "vec_nth (M *v perp2 e) 1
      = M $ 1 $ 1 * vec_nth (perp2 e) 1 + M $ 1 $ 2 * vec_nth (perp2 e) 2"
    by (simp add: matrix_vector_mult_def sum_2)
  have Mp2: "vec_nth (M *v perp2 e) 2
      = M $ 2 $ 1 * vec_nth (perp2 e) 1 + M $ 2 $ 2 * vec_nth (perp2 e) 2"
    by (simp add: matrix_vector_mult_def sum_2)
  have detM: "det M = M $ 1 $ 1 * M $ 2 $ 2 - M $ 1 $ 2 * M $ 2 $ 1"
    by (simp only: det_2)
  show ?thesis
    unfolding inner_vec_def sum_2 p1 p2 Mp1 Mp2 Mv1 Mv2 e1 e2 detM
    by (simp add: power2_eq_square algebra_simps)
qed

text \<open>The pivot nonvanishing fact, Sketch.md \<section>6d: \<open>d_perp \<bullet> perp2(c) = det(Dc) \<cdot> |e_par|\<^sup>2\<close>
  -- so (C2) always has a unique solution \<open>r(\<phi>)\<close> once \<open>\<phi>\<close> is fixed, given the standing
  hypotheses \<open>det(Dc) \<noteq> 0\<close> (needed for \<open>e_par\<close> to exist at all) and \<open>e_par \<noteq> 0\<close>.\<close>

lemma pivot_nonzero:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>)) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)
       = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (e_par \<omega>0 \<omega>s \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>)"
proof -
  define M where "M = matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have decomp: "\<And>h::real^2. h = vec_nth h 1 *\<^sub>R axis 1 1 + vec_nth h 2 *\<^sub>R axis 2 1"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix h :: "real^2" and i :: 2
    show "vec_nth h i = vec_nth (vec_nth h 1 *\<^sub>R axis 1 1 + vec_nth h 2 *\<^sub>R axis 2 1) i"
      using exhaust_2[of i] by (auto simp: axis_def)
  qed
  have mv: "M *v h = Dcvec_dip \<omega>0 \<omega>s \<omega> h" for h :: "real^2"
  proof -
    have expand: "M *v h
        = vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
      unfolding M_def
    proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
      fix i :: 2
      show "vec_nth (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v h) i
          = vec_nth (vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
                   + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) i"
        by (simp add: matrix_def matrix_vector_mult_def sum_2 algebra_simps)
    qed
    have "Dcvec_dip \<omega>0 \<omega>s \<omega> h
        = vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
      using decomp[of h] linear_add[OF lin] linear_cmul[OF lin] by metis
    with expand show ?thesis by simp
  qed
  have "M *v perp2 (e_par \<omega>0 \<omega>s \<omega>) = Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>))"
    by (rule mv)
  moreover have "M *v e_par \<omega>0 \<omega>s \<omega> = cvec_dip \<omega>0 \<omega>s \<omega>"
    using mv[of "e_par \<omega>0 \<omega>s \<omega>"] Dcvec_dip_e_par[OF detnz] by simp
  ultimately have "Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>)) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)
      = (M *v perp2 (e_par \<omega>0 \<omega>s \<omega>)) \<bullet> perp2 (M *v e_par \<omega>0 \<omega>s \<omega>)"
    by simp
  also have "\<dots> = det M * (e_par \<omega>0 \<omega>s \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>)"
    by (rule matrix_perp2_pivot_identity)
  finally show ?thesis
    unfolding M_def .
qed

section \<open>The transversality-witness scalar \<open>R\<close>: an exact, hypothesis-light
  identity, Sketch.md \<section>6i/\<section>6k\<close>

text \<open>Sketch.md \<section>6i defines \<open>Q\<close>/\<open>R\<close>, the scalars governing the single-bump
  witness's exact (not asymptotic) leading coefficient
  \<open>\<Xi>(p) = -2 n1 g0 R \<phi>\<^sup>2 cos \<phi> + O(1)\<close>. This section proves \<open>R\<close> obeys a
  FULLY GENERAL identity -- pure 2x2 linear algebra, no trig, no Robust4-design-
  point substitution needed: \<open>R \<cdot> e_par$1 = w$1\<close>. Consequently
  \<open>R = 0 \<longleftrightarrow> w$1 = 0\<close> whenever \<open>e_par$1 \<noteq> 0\<close> -- the witness's leading term is
  nonzero exactly when the arc's own angular velocity has nonzero
  \<open>\<theta>\<close>-component, independent of the design-point angle beyond needing
  \<open>e_par$1 \<noteq> 0\<close> itself (conjectured, not yet checked here, to be exactly the
  pre-existing \<open>d3_s2_global_factor \<noteq> 0\<close> condition via \<open>e_par = (s2/D,-s1/D)\<close>,
  Sketch.md \<section>3).\<close>

definition Q_dip :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "Q_dip \<omega>0 \<omega>s \<omega> =
     (vec_nth (perp2 (e_par \<omega>0 \<omega>s \<omega>)) 1 / vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
        - (Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 (e_par \<omega>0 \<omega>s \<omega>)) \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
          / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>))
     / (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * (e_par \<omega>0 \<omega>s \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>))"

definition R_dip :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "R_dip \<omega>0 \<omega>s \<omega> w =
     (Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>) / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)
     + Q_dip \<omega>0 \<omega>s \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))"

text \<open>Norm-preservation of \<open>perp2\<close>: pure component computation.\<close>

lemma perp2_norm_preserving: "perp2 (e::real^2) \<bullet> perp2 e = e \<bullet> e"
  by (simp add: inner_vec_def sum_2 perp2_component_1 perp2_component_2 algebra_simps)

lemma inner_self_eq_zero_iff_vec2: "(e::real^2) \<bullet> e = 0 \<longleftrightarrow> e = 0"
proof
  assume "e \<bullet> e = 0"
  hence eq: "(vec_nth e 1)\<^sup>2 + (vec_nth e 2)\<^sup>2 = 0"
    by (simp add: inner_vec_def sum_2 power2_eq_square)
  have e1sq: "(vec_nth e 1)\<^sup>2 = 0"
    using eq zero_le_power2[of "vec_nth e 2"] zero_le_power2[of "vec_nth e 1"] by linarith
  have e2sq: "(vec_nth e 2)\<^sup>2 = 0"
    using eq zero_le_power2[of "vec_nth e 1"] zero_le_power2[of "vec_nth e 2"] by linarith
  have e1z: "vec_nth e 1 = 0" and e2z: "vec_nth e 2 = 0"
    using e1sq e2sq by simp_all
  show "e = 0"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 2
    show "vec_nth e i = vec_nth (0::real^2) i"
      using exhaust_2[of i] e1z e2z by auto
  qed
qed simp

text \<open>The orthogonal decomposition of any \<open>w\<close> in the \<open>(e, perp2 e)\<close> basis, given
  \<open>e \<noteq> 0\<close> -- since \<open>e \<bullet> perp2 e = 0\<close> (\<open>perp2_orth\<close>) and \<open>perp2 e\<close> has the same
  norm as \<open>e\<close> (\<open>perp2_norm_preserving\<close>).\<close>

lemma orthogonal_decomp_perp2:
  fixes e w :: "real^2"
  assumes enz: "e \<noteq> 0"
  shows "w = ((w \<bullet> e) / (e \<bullet> e)) *\<^sub>R e + ((w \<bullet> perp2 e) / (e \<bullet> e)) *\<^sub>R perp2 e"
proof -
  have eenz: "e \<bullet> e \<noteq> 0"
    using enz inner_self_eq_zero_iff_vec2 by blast
  show ?thesis
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 2
    have lhs: "vec_nth (((w \<bullet> e) / (e \<bullet> e)) *\<^sub>R e + ((w \<bullet> perp2 e) / (e \<bullet> e)) *\<^sub>R perp2 e) i
        = ((w \<bullet> e) * vec_nth e i + (w \<bullet> perp2 e) * vec_nth (perp2 e) i) / (e \<bullet> e)"
      by (simp add: add_divide_distrib)
    have poly: "(w \<bullet> e) * vec_nth e i + (w \<bullet> perp2 e) * vec_nth (perp2 e) i
        = vec_nth w i * (e \<bullet> e)"
      using exhaust_2[of i]
      by (auto simp: inner_vec_def sum_2 perp2_component_1 perp2_component_2 algebra_simps)
    have "((w \<bullet> e) * vec_nth e i + (w \<bullet> perp2 e) * vec_nth (perp2 e) i) / (e \<bullet> e)
        = vec_nth w i"
      unfolding poly using eenz by simp
    with lhs show "vec_nth w i
        = vec_nth (((w \<bullet> e) / (e \<bullet> e)) *\<^sub>R e + ((w \<bullet> perp2 e) / (e \<bullet> e)) *\<^sub>R perp2 e) i"
      by simp
  qed
qed

text \<open>The main identity: \<open>R_dip \<cdot> e_par$1 = w$1\<close>, exactly, given the standing
  hypotheses \<open>det(Dc)\<noteq>0\<close> (needed for \<open>e_par\<close> to exist), \<open>c\<noteq>0\<close> (needed for the
  radial denominator), and \<open>e_par$1\<noteq>0\<close> (needed for \<open>Q_dip\<close> to exist).
  Proof idea (found by direct computer-algebra verification before this
  formalization, then reproduced by hand): decompose \<open>w\<close> in the
  \<open>(e_par, perp2 e_par)\<close> basis (\<open>orthogonal_decomp_perp2\<close>); linearity of
  \<open>Dcvec_dip\<close> pushes the decomposition through to \<open>Dcvec_dip \<omega> w\<close>; the
  \<open>perp2(c)\<close>-component of \<open>Dcvec_dip \<omega> e_par = c\<close> vanishes (\<open>perp2_orth\<close>); and
  the messy \<open>(d_perp \<bullet> c)\<close> cross term appearing in both \<open>R_dip\<close>'s radial piece
  and \<open>Q_dip\<close>'s own definition cancels EXACTLY between the two, leaving only
  \<open>R_dip = \<alpha> - \<beta> \<cdot> e_par$2/e_par$1\<close> where \<open>\<alpha>,\<beta>\<close> are \<open>w\<close>'s \<open>(e_par,perp2 e_par)\<close>
  coordinates -- which is exactly \<open>w$1/e_par$1\<close> by \<open>perp2_component_1\<close>.\<close>

theorem R_dip_times_e_par1_eq_w1:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
  shows "R_dip \<omega>0 \<omega>s \<omega> w * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 = vec_nth w 1"
proof -
  define e where "e = e_par \<omega>0 \<omega>s \<omega>"
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define dperp where "dperp = Dcvec_dip \<omega>0 \<omega>s \<omega> (perp2 e)"
  define ee where "ee = e \<bullet> e"
  define cc where "cc = c \<bullet> c"
  define \<alpha> where "\<alpha> = (w \<bullet> e) / ee"
  define \<beta> where "\<beta> = (w \<bullet> perp2 e) / ee"
  have enz: "e \<noteq> 0"
    using e1nz e_def by (auto simp: inner_self_eq_zero_iff_vec2)
  have eenz: "ee \<noteq> 0"
    using enz ee_def inner_self_eq_zero_iff_vec2 by auto
  have ccnz: "cc \<noteq> 0"
    using cnz cc_def inner_self_eq_zero_iff_vec2 c_def by presburger
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have wdecomp: "w = \<alpha> *\<^sub>R e + \<beta> *\<^sub>R perp2 e"
    unfolding \<alpha>_def \<beta>_def ee_def by (rule orthogonal_decomp_perp2[OF enz])
  have ce: "Dcvec_dip \<omega>0 \<omega>s \<omega> e = c"
    unfolding e_def c_def by (rule Dcvec_dip_e_par[OF detnz])
  have dw: "Dcvec_dip \<omega>0 \<omega>s \<omega> w = \<alpha> *\<^sub>R c + \<beta> *\<^sub>R dperp"
    using arg_cong[OF wdecomp, of "Dcvec_dip \<omega>0 \<omega>s \<omega>"]
    by (simp only: linear_add[OF lin] linear_cmul[OF lin] ce dperp_def)
  have c_perp_c: "c \<bullet> perp2 c = 0"
    by (rule perp2_orth)
  have pivot: "dperp \<bullet> perp2 c = det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * ee"
    unfolding dperp_def ee_def e_def c_def by (rule pivot_nonzero[OF detnz])
  have dw_c: "Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> c = \<alpha> * cc + \<beta> * (dperp \<bullet> c)"
    unfolding dw cc_def by (simp add: inner_add_left algebra_simps)
  have dw_perp2c: "Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> perp2 c
      = \<beta> * (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * ee)"
    unfolding dw using pivot c_perp_c
    by (simp add: inner_add_left algebra_simps)
  have Qval: "Q_dip \<omega>0 \<omega>s \<omega>
      = (vec_nth (perp2 e) 1 / vec_nth e 1 - (dperp \<bullet> c) / cc)
        / (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * ee)"
    unfolding Q_dip_def e_def c_def dperp_def cc_def ee_def by simp
  have Qdet: "Q_dip \<omega>0 \<omega>s \<omega> * (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * ee)
      = vec_nth (perp2 e) 1 / vec_nth e 1 - (dperp \<bullet> c) / cc"
    unfolding Qval
    using mult_eq_0_iff detnz eenz
    by (simp add: nonzero_mult_div_cancel_right)
  have Rval: "R_dip \<omega>0 \<omega>s \<omega> w
      = (Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> c) / cc
        + Q_dip \<omega>0 \<omega>s \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> perp2 c)"
    unfolding R_dip_def e_def c_def cc_def by simp
  also have "\<dots> = \<alpha> + \<beta> * (dperp \<bullet> c) / cc
      + Q_dip \<omega>0 \<omega>s \<omega> * (det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) * ee) * \<beta>"
    unfolding dw_c dw_perp2c
    using ccnz by (simp add: field_simps)
  also have "\<dots> = \<alpha> + \<beta> * (dperp \<bullet> c) / cc
      + (vec_nth (perp2 e) 1 / vec_nth e 1 - (dperp \<bullet> c) / cc) * \<beta>"
    unfolding Qdet by simp
  also have "\<dots> = \<alpha> - \<beta> * (vec_nth e 2 / vec_nth e 1)"
    using e1nz unfolding e_def[symmetric] perp2_component_1
    by (simp add: algebra_simps e1nz)
  finally have Rform: "R_dip \<omega>0 \<omega>s \<omega> w = \<alpha> - \<beta> * (vec_nth e 2 / vec_nth e 1)" .
  have w1: "vec_nth w 1 = \<alpha> * vec_nth e 1 - \<beta> * vec_nth e 2"
    using wdecomp e1nz
    by (simp add: perp2_component_1)
  show ?thesis
    unfolding e_def[symmetric] Rform using e1nz w1
    by (simp add: diff_divide_eq_iff e_def)
qed

corollary R_dip_eq_zero_iff:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
  shows "R_dip \<omega>0 \<omega>s \<omega> w = 0 \<longleftrightarrow> vec_nth w 1 = 0"
  using R_dip_times_e_par1_eq_w1[OF detnz cnz e1nz, of w] e1nz by auto

section \<open>The closed \<open>\<Xi>\<close> value on the single-bump family, unconditional
  (Sketch.md \<section>6o)\<close>

text \<open>The fully general, hypothesis-free dictionary \<open>HessU_quad_dictionary\<close>
  (\<open>D34_Geodesic_Branch.thy\<close>), specialized to \<open>e := e_par\<close> and \<open>x := slot i p\<close>,
  gives \<open>\<Xi>\<close>'s value on the single-bump family in closed \<open>sin\<close>/\<open>cos\<close> form --
  no criticality needed yet (that comes later, via (C1)/(C2), Sketch.md
  \<section>6o's leading-term extraction).\<close>

lemma Xi_single_bump_raw:
  fixes p \<omega>0 \<omega>s \<omega> w :: "real^2" and i :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "Xi (slot i p) \<omega>0 \<omega>s \<omega> w
      = - (2 * (real (CARD('n)) - 1) * deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> p) * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))
        + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * ((real (CARD('n)) - 1)\<^sup>2 + 1
             + 2 * (real (CARD('n)) - 1) * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))
        - (2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w \<bullet> p) * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))
        - (2 * (real (CARD('n)) - 1) * gain_dip \<omega>
            * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p) * (Dcvec_dip \<omega>0 \<omega>s \<omega> w \<bullet> p) * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))
        - (2 * (real (CARD('n)) - 1) * deriv gdip (vec_nth \<omega> 1) * vec_nth w 1
            * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p) * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> p))"
proof -
  have raw: "Xi (slot i p) \<omega>0 \<omega>s \<omega> w =
     ((deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
          * Wc_d1 (slot i p) (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> w)
        + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1
          * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * Wc (slot i p) (cvec_dip \<omega>0 \<omega>s \<omega>))
     + (gain_dip \<omega> * (Wc_d1 (slot i p) (cvec_dip \<omega>0 \<omega>s \<omega>)
            (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) w)
          + Wc_dd (slot i p) (cvec_dip \<omega>0 \<omega>s \<omega>)
            (Dcvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>))
            (Dcvec_dip \<omega>0 \<omega>s \<omega> w))
        + deriv gdip (vec_nth \<omega> 1) * vec_nth w 1
          * Wc_d1 (slot i p) (cvec_dip \<omega>0 \<omega>s \<omega>)
            (Dcvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>)))"
    unfolding Xi_def by (rule HessU_quad_dictionary)
  show ?thesis
    unfolding raw Wc_single_bump Wc_d1_single_bump Wc_dd_single_bump
      Dcvec_dip_e_par[OF detnz]
    by (simp add: power2_eq_square algebra_simps)
qed

section \<open>The (C1) root family: existence via IVT, Sketch.md \<section>6h/\<section>6i\<close>

text \<open>For a bounded \<open>B\<close>, \<open>\<phi> sin \<phi> = B \<phi>\<close> has roots \<open>\<phi>\<close> near every \<open>2M\<pi>\<close>
  (\<open>M\<close> large enough that the window dominates \<open>B\<close>'s bound), with \<open>cos \<phi>\<close>
  bounded away from \<open>0\<close> throughout the whole window -- Sketch.md \<section>6i's
  corrected root-existence claim (no side-condition on \<open>sin \<phi>\<close> needed, unlike
  the original \<section>6d attempt).\<close>

lemma phi_sin_eq_B_root_exists_even:
  fixes B :: "real \<Rightarrow> real" and Cbound :: real and M :: nat
  assumes Bbound: "\<And>t. \<bar>B t\<bar> \<le> Cbound"
    and Bcont: "continuous_on UNIV B"
    and Mbig: "(real (2 * M) * pi - pi / 4) * (sqrt 2 / 2) > Cbound"
  shows "\<exists>\<phi>. real (2 * M) * pi - pi / 4 < \<phi> \<and> \<phi> < real (2 * M) * pi + pi / 4
       \<and> \<phi> * sin \<phi> = B \<phi> \<and> cos \<phi> > sqrt 2 / 2"
proof -
  define N where "N = real (2 * M) * pi"
  define lo where "lo = N - pi / 4"
  define hi where "hi = N + pi / 4"
  define h where "h = (\<lambda>\<phi>. \<phi> * sin \<phi> - B \<phi>)"
  have sinN: "sin N = 0"
    unfolding N_def by (simp add: mult.commute[of "real (2 * M)" pi])
  have cosN: "cos N = 1"
    unfolding N_def by (simp add: mult.commute[of "real (2 * M)" pi])
  have sin_lo: "sin lo = - (sqrt 2 / 2)"
    unfolding lo_def by (simp add: sin_diff sinN cosN cos_45 sin_45)
  have sin_hi: "sin hi = sqrt 2 / 2"
    unfolding hi_def by (simp add: sin_add sinN cosN cos_45 sin_45)
  have loGtCbound: "lo * (sqrt 2 / 2) > Cbound"
    using Mbig unfolding lo_def N_def by simp
  have s2pos: "(0::real) < sqrt 2 / 2"
    using real_sqrt_gt_zero[of 2] by simp
  have lopos: "lo > 0"
  proof -
    have "Cbound \<ge> 0"
      using Bbound[of lo] by simp
    hence "0 < lo * (sqrt 2 / 2)"
      using loGtCbound by linarith
    hence "0 < (sqrt 2 / 2) * lo"
      by (simp add: mult.commute)
    thus ?thesis
      using zero_less_mult_pos[OF _ s2pos] by blast
  qed
  have hipos: "hi > lo"
    unfolding lo_def hi_def by simp
  have hlo: "h lo < 0"
  proof -
    have "h lo = lo * (- (sqrt 2 / 2)) - B lo"
      unfolding h_def sin_lo ..
    also have "\<dots> \<le> - (lo * (sqrt 2 / 2)) + Cbound"
      using Bbound[of lo] by simp
    also have "\<dots> < 0"
      using loGtCbound by simp
    finally show ?thesis .
  qed
  have hhi: "h hi > 0"
  proof -
    have "h hi = hi * (sqrt 2 / 2) - B hi"
      unfolding h_def sin_hi ..
    also have "\<dots> \<ge> lo * (sqrt 2 / 2) - Cbound"
    proof -
      have "B hi \<le> Cbound" using Bbound[of hi] by simp
      moreover have "lo * (sqrt 2 / 2) \<le> hi * (sqrt 2 / 2)"
        using hipos s2pos by (intro mult_right_mono) auto
      ultimately show ?thesis by linarith
    qed
    also have "\<dots> > 0"
      using loGtCbound \<open>lo * (sqrt 2 / 2) - Cbound \<le> hi * (sqrt 2 / 2) - B hi\<close> by fastforce 
    finally show ?thesis
      using \<open>0 < hi * (sqrt 2 / 2) - B hi\<close> h_def sin_hi by presburger 
  qed
  have hcont_on: "continuous_on UNIV h"
    unfolding h_def by (intro continuous_intros Bcont)
  have hcont: "isCont h x" for x
    using continuous_on_eq_continuous_at[OF open_UNIV, THEN iffD1, OF hcont_on] by blast
  have IVTpre: "h lo \<le> 0" "0 \<le> h hi" "lo \<le> hi" "\<forall>x. lo \<le> x \<and> x \<le> hi \<longrightarrow> isCont h x"
    using hlo hhi hipos hcont by auto
  obtain \<phi> where phirange: "lo \<le> \<phi>" "\<phi> \<le> hi" and hzero: "h \<phi> = 0"
    using IVT[OF IVTpre(1) IVTpre(2) IVTpre(3) IVTpre(4)] by blast
  have philo: "lo < \<phi>"
    using phirange hlo hzero by (cases "lo = \<phi>") auto
  have phihi: "\<phi> < hi"
    using phirange hhi hzero by (cases "hi = \<phi>") auto
  define t where "t = \<phi> - N"
  have trange: "- (pi / 4) < t" "t < pi / 4"
    using philo phihi unfolding t_def lo_def hi_def by simp_all
  have phit: "\<phi> = N + t"
    unfolding t_def by simp
  have costcos: "cos \<phi> = cos t"
    unfolding phit by (simp add: cos_add sinN cosN)
  have quarter_le_pi: "pi / 4 \<le> pi"
    using pi_gt_zero by linarith
  have costgt: "cos t > sqrt 2 / 2"
  proof (cases "t \<ge> 0")
    case True
    have "cos (pi / 4) < cos t"
      by (rule cos_monotone_0_pi[OF True trange(2) quarter_le_pi])
    thus ?thesis by (simp only: cos_45)
  next
    case False
    have t0: "- t \<ge> 0" and t1: "- t < pi / 4"
      using False trange(1) by linarith+
    have "cos (pi / 4) < cos (- t)"
      by (rule cos_monotone_0_pi[OF t0 t1 quarter_le_pi])
    thus ?thesis by (simp only: cos_45 cos_minus)
  qed
  show ?thesis
    using philo phihi hzero costgt
    unfolding lo_def[symmetric] hi_def[symmetric] N_def[symmetric]
    unfolding h_def costcos
    using costcos by auto 
qed

section \<open>The second-order assembly and dipole gradient jet\<close>

lemma frechet_derivative_gdip_k_omega:
  fixes \<omega> :: "real^2" and k :: "2"
  shows "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1 :: real^2) 1))
             (at \<omega>) (axis l 1)
       = vec_nth (axis k 1 :: real^2) 1 * deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (axis l 1 :: real^2) 1"
proof -
  have eqf: "(\<lambda>\<eta>::real^2. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1 :: real^2) 1))
      = (\<lambda>\<eta>. vec_nth (axis k 1 :: real^2) 1 * deriv gdip (vec_nth \<eta> 1))"
    by (rule ext) (simp add: frechet_derivative_gdip_linear)
  have hd: "((\<lambda>\<eta>::real^2. vec_nth (axis k 1 :: real^2) 1 * deriv gdip (vec_nth \<eta> 1)) has_derivative
      (\<lambda>v. vec_nth (axis k 1 :: real^2) 1 * (deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1))) (at \<omega>)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult_right[OF
          frechet_derivative_deriv_gdip_omega]]) (rule refl)
  show ?thesis
    unfolding eqf
    using frechet_derivative_at'[OF hd] by (simp only: algebra_simps)
qed

definition K_gdip :: "real \<Rightarrow> real \<Rightarrow> real" where
  \<comment> \<open>the scalar \<open>K(\<theta>) = g''(\<theta>) - 2g'(\<theta>)\<^sup>2/gain\<close> from Sketch.md sections 3/6b -- the
      coefficient of \<open>e_k$1\<cdot>e_l$1\<cdot>V\<close> surviving after the critical-point
      substitution, for a gain value \<open>g\<close> at that angle.\<close>
  "K_gdip \<theta> g = deriv (deriv gdip) \<theta> - 2 * (deriv gdip \<theta>)\<^sup>2 / g"

lemma HessU_dip_entry_moments_crit:
  fixes x :: "(real^2)^'n::finite" and k l :: "2"
  assumes crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                        \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
                      + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1))
                        \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
         + K_gdip (vec_nth \<omega> 1) (gain_dip \<omega>)
           * vec_nth (axis k 1 :: real^2) 1 * vec_nth (axis l 1 :: real^2) 1
           * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)"
proof -
  define IP where "IP = (\<lambda>j::2. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))"
  define V where "V = U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)"
  define g' where "g' = deriv gdip (vec_nth \<omega> 1)"
  define g'' where "g'' = deriv (deriv gdip) (vec_nth \<omega> 1)"
  have field_j: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j = gain_dip \<omega> * IP j
      + vec_nth (axis j 1 :: real^2) 1 * g' * V" for j :: 2
    unfolding IP_def V_def g'_def
    by (simp add: gradU_dip_component_field frechet_derivative_gdip_linear mult.commute)
  have crit_j: "gain_dip \<omega> * IP j = - vec_nth (axis j 1 :: real^2) 1 * g' * V" for j :: 2
    using field_j[of j] crit by (simp add: vec_eq_iff)
  have IP_j: "IP j = - vec_nth (axis j 1 :: real^2) 1 * g' * V / gain_dip \<omega>" for j :: 2
    using crit_j[of j] gnz by (simp add: field_simps)
  have raw: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = (gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                        \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
                      + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1))
                        \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis l 1 :: real^2) 1) * IP k)
        + (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis k 1 :: real^2) 1) * IP l
          + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1 :: real^2) 1))
              (at \<omega>) (axis l 1) * V)"
    unfolding IP_def V_def by (rule HessU_dip_entry_moments)
  have Kl: "frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis l 1 :: real^2) 1) * IP k
      = - vec_nth (axis k 1 :: real^2) 1 * vec_nth (axis l 1 :: real^2) 1 * (g')\<^sup>2 * V / gain_dip \<omega>"
    unfolding IP_j[of k] frechet_derivative_gdip_linear g'_def[symmetric]
    by (simp add: power2_eq_square algebra_simps)
  have Kk: "frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis k 1 :: real^2) 1) * IP l
      = - vec_nth (axis k 1 :: real^2) 1 * vec_nth (axis l 1 :: real^2) 1 * (g')\<^sup>2 * V / gain_dip \<omega>"
    unfolding IP_j[of l] frechet_derivative_gdip_linear g'_def[symmetric]
    by (simp add: power2_eq_square algebra_simps)
  have Kg: "frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1 :: real^2) 1))
              (at \<omega>) (axis l 1)
      = vec_nth (axis k 1 :: real^2) 1 * g'' * vec_nth (axis l 1 :: real^2) 1"
    unfolding g''_def by (rule frechet_derivative_gdip_k_omega)
  show ?thesis
    unfolding raw Kl Kk Kg K_gdip_def V_def[symmetric] g'_def[symmetric] g''_def[symmetric]
    by (simp add: field_simps)
qed

section \<open>\<open>gain_dip\<close>'s third derivative along a line: 1-D chain rule through
  the linear argument \<open>\<omega>0$1 + s\<cdot>w$1\<close>, keeping \<open>deriv gdip\<close>/\<open>deriv\<^sup>2 gdip\<close>/
  \<open>deriv\<^sup>3 gdip\<close> OPAQUE (matching this codebase's established convention:
  \<open>gdip\<close>'s \<open>gsinc\<close>-based closed form is never expanded past its derivative
  jets).\<close>

lemma gain_dip_line_d1:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. gain_dip (\<omega>0 + s *\<^sub>R w)) has_field_derivative
      (vec_nth w 1 * deriv gdip (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
proof -
  have line1: "vec_nth (\<omega>0 + s *\<^sub>R w) 1 = vec_nth \<omega>0 1 + s * vec_nth w 1"
    by (simp add: vector_add_component vector_scaleR_component)
  have eqf: "(\<lambda>s. gain_dip (\<omega>0 + s *\<^sub>R w)) = (\<lambda>s. gdip (vec_nth \<omega>0 1 + s * vec_nth w 1))"
    by (rule ext) (simp add: gain_dip_def line1)
  show ?thesis
    unfolding eqf
    using DERIV_chain2[OF deriv_gdip_has_field_derivative
        DERIV_add[OF DERIV_const DERIV_cmult[OF DERIV_ident]]]
    by (simp add: mult.commute, metis mult_commute_abs)
qed

lemma gain_dip_line_d2:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. vec_nth w 1 * deriv gdip (vec_nth \<omega>0 1 + s * vec_nth w 1)) has_field_derivative
      ((vec_nth w 1)\<^sup>2 * deriv (deriv gdip) (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
proof -
  have "((\<lambda>s. deriv gdip (vec_nth \<omega>0 1 + s * vec_nth w 1)) has_field_derivative
      (vec_nth w 1 * deriv (deriv gdip) (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
    using DERIV_chain2[OF deriv2_gdip_has_field_derivative
        DERIV_add[OF DERIV_const DERIV_cmult[OF DERIV_ident]]]
    by (simp add: mult.commute, metis mult_commute_abs)
  from DERIV_cmult[OF this, of "vec_nth w 1"]
  show ?thesis by (simp only: power2_eq_square algebra_simps)
qed

lemma gain_dip_line_d3:
  fixes \<omega>0 w :: "real^2"
  shows "((\<lambda>s. (vec_nth w 1)\<^sup>2 * deriv (deriv gdip) (vec_nth \<omega>0 1 + s * vec_nth w 1)) has_field_derivative
      ((vec_nth w 1) ^ 3 * deriv (deriv (deriv gdip)) (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
proof -
  have "((\<lambda>s. deriv (deriv gdip) (vec_nth \<omega>0 1 + s * vec_nth w 1)) has_field_derivative
      (vec_nth w 1 * deriv (deriv (deriv gdip)) (vec_nth \<omega>0 1 + s * vec_nth w 1))) (at s)"
    using DERIV_chain2[OF deriv3_gdip_has_field_derivative
        DERIV_add[OF DERIV_const DERIV_cmult[OF DERIV_ident]]]
    by (simp add: mult.commute, metis mult_commute_abs)
  from DERIV_cmult[OF this, of "(vec_nth w 1)\<^sup>2"]
  show ?thesis by (simp only: power2_eq_square power3_eq_cube algebra_simps)
qed

lemma gain_dip_line_third_deriv:
  fixes \<omega>0 w :: "real^2"
  shows "(deriv (deriv (deriv (\<lambda>s. gain_dip (\<omega>0 + s *\<^sub>R w))))) 0
      = vec_nth w 1 ^ 3 * deriv (deriv (deriv gdip)) (vec_nth \<omega>0 1)"
proof -
  define d1 :: "real \<Rightarrow> real" where "d1 = (\<lambda>s. vec_nth w 1 * deriv gdip (vec_nth \<omega>0 1 + s * vec_nth w 1))"
  define d2 :: "real \<Rightarrow> real" where "d2 = (\<lambda>s. (vec_nth w 1)\<^sup>2 * deriv (deriv gdip) (vec_nth \<omega>0 1 + s * vec_nth w 1))"
  have step1: "deriv (\<lambda>s. gain_dip (\<omega>0 + s *\<^sub>R w)) = d1"
    by (rule ext) (unfold d1_def, rule DERIV_imp_deriv[OF gain_dip_line_d1])
  have step2: "deriv d1 = d2"
    unfolding d1_def d2_def by (rule ext) (rule DERIV_imp_deriv[OF gain_dip_line_d2])
  have raw: "(d2 has_field_derivative
      (vec_nth w 1 ^ 3 * deriv (deriv (deriv gdip)) (vec_nth \<omega>0 1 + 0 * vec_nth w 1))) (at 0)"
    unfolding d2_def by (rule gain_dip_line_d3)
  have d3at0: "(d2 has_field_derivative
      (vec_nth w 1 ^ 3 * deriv (deriv (deriv gdip)) (vec_nth \<omega>0 1))) (at 0)"
    using raw by simp
  have step3: "deriv d2 0 = vec_nth w 1 ^ 3 * deriv (deriv (deriv gdip)) (vec_nth \<omega>0 1)"
    by (rule DERIV_imp_deriv[OF d3at0])
  show ?thesis
    unfolding step1 step2 by (rule step3)
qed

section \<open>Mixed third \<open>c\<close>-jet of \<open>Wc\<close>\<close>

text \<open>The isolated-zero cubic needs the full mixed trilinear third \<open>c\<close>-jet,
  not only the diagonal @{const Wc_d3}.  This is the derivative of the
  already-proven mixed bilinear second jet @{const Wc_dd} in an arbitrary
  third direction.\<close>

definition Wc_ddd ::
  "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real"
  where
  "Wc_ddd x c a b u = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (a \<bullet> (vec_nth x n - vec_nth x p))
    * (b \<bullet> (vec_nth x n - vec_nth x p))
    * (u \<bullet> (vec_nth x n - vec_nth x p))
    * sin (c \<bullet> (vec_nth x n - vec_nth x p)))"

lemma Wc_d3_eq_ddd:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc_d3 x c d = Wc_ddd x c d d d"
  by (simp only: Wc_d3_def Wc_ddd_def power3_eq_cube algebra_simps)

lemma DERIV_neg_prod_cos:
  fixes A B C D t :: real
  shows "((\<lambda>s. - (A * B * cos (C + s * D))) has_field_derivative
      A * B * D * sin (C + t * D)) (at t)"
proof -
  have "((\<lambda>s. - (A * B * cos (C + s * D))) has_field_derivative
      - (A * B * (- sin (C + t * D) * D))) (at t)"
    by (auto intro!: derivative_eq_intros)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma Wc_d1_add_dir:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc_d1 x c (a + b) = Wc_d1 x c a + Wc_d1 x c b"
  by (simp only: Wc_d1_def inner_add_left sum.distrib sum_subtractf
      sum_negf algebra_simps)

lemma Wc_d1_scale_dir:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc_d1 x c (r *\<^sub>R a) = r * Wc_d1 x c a"
  by (simp add: Wc_d1_def sum_distrib_left algebra_simps)

lemma Wc_dd_sym:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc_dd x c a b = Wc_dd x c b a"
  by (simp only: Wc_dd_def algebra_simps)

lemma Wc_dd_add_left:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc_dd x c (a + b) u = Wc_dd x c a u + Wc_dd x c b u"
  by (simp only: Wc_dd_def inner_add_left sum.distrib sum_subtractf
      sum_negf sum_distrib_left algebra_simps)

lemma Wc_dd_scale_left:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc_dd x c (r *\<^sub>R a) u = r * Wc_dd x c a u"
  by (simp add: Wc_dd_def sum_distrib_left algebra_simps)

lemma Wc_ddd_sym_ab:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc_ddd x c a b u = Wc_ddd x c b a u"
  by (simp only: Wc_ddd_def algebra_simps)

lemma Wc_ddd_sym_bu:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc_ddd x c a b u = Wc_ddd x c a u b"
  by (simp only: Wc_ddd_def algebra_simps)

lemma has_derivative_Wc_dd_c:
  fixes x :: "(real^2)^'n::finite" and c a b :: "real^2"
  shows "((\<lambda>c'. Wc_dd x c' a b) has_derivative
      (\<lambda>u. Wc_ddd x c a b u)) (at c)"
proof -
  have dgcos: "(cos has_field_derivative (\<lambda>v. - sin v) u) (at u)" for u :: real
    using DERIV_cos[of u] by simp
  have F: "((\<lambda>c'. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      cos (c' \<bullet> (vec_nth x n - vec_nth x p))
        * (- ((a \<bullet> (vec_nth x n - vec_nth x p))
            * (b \<bullet> (vec_nth x n - vec_nth x p)))))
      has_derivative
      (\<lambda>u. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        - sin (c \<bullet> (vec_nth x n - vec_nth x p))
        * (u \<bullet> (vec_nth x n - vec_nth x p))
        * (- ((a \<bullet> (vec_nth x n - vec_nth x p))
            * (b \<bullet> (vec_nth x n - vec_nth x p)))))) (at c)"
    by (rule has_derivative_pair_phase_sum_c_coeff[OF dgcos])
  have eqf: "(\<lambda>c'. Wc_dd x c' a b) = (\<lambda>c'. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      cos (c' \<bullet> (vec_nth x n - vec_nth x p))
        * (- ((a \<bullet> (vec_nth x n - vec_nth x p))
            * (b \<bullet> (vec_nth x n - vec_nth x p)))))"
    by (rule ext) (simp add: Wc_dd_def sum_negf sum.distrib sum_subtractf
        sum_distrib_left sum_distrib_right inner_diff_right algebra_simps)
  have eqd: "(\<lambda>u. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        - sin (c \<bullet> (vec_nth x n - vec_nth x p))
        * (u \<bullet> (vec_nth x n - vec_nth x p))
        * (- ((a \<bullet> (vec_nth x n - vec_nth x p))
            * (b \<bullet> (vec_nth x n - vec_nth x p)))))
      = (\<lambda>u. Wc_ddd x c a b u)"
    by (rule ext) (simp add: Wc_ddd_def algebra_simps)
  show ?thesis
    unfolding eqf using F unfolding eqd .
qed

lemma Wc_d1_curve_mixed:
  fixes x :: "(real^2)^'n::finite" and c a d :: "real^2"
  shows "((\<lambda>t. Wc_d1 x (c + t *\<^sub>R d) a) has_field_derivative
      Wc_dd x (c + t *\<^sub>R d) a d) (at t)"
proof -
  have inner_line: "(c + s *\<^sub>R d) \<bullet> w = (c \<bullet> w) + s * (d \<bullet> w)"
    for s :: real and w :: "real^2"
    by (simp add: inner_add_left inner_scaleR_left)
  have D: "((\<lambda>s. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (a \<bullet> (vec_nth x n - vec_nth x p))
        * sin ((c \<bullet> (vec_nth x n - vec_nth x p))
            + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))
    has_field_derivative
      - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        (a \<bullet> (vec_nth x n - vec_nth x p))
        * (d \<bullet> (vec_nth x n - vec_nth x p))
        * cos ((c \<bullet> (vec_nth x n - vec_nth x p))
            + t * (d \<bullet> (vec_nth x n - vec_nth x p)))))
    (at t)"
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have eqf: "(\<lambda>s. Wc_d1 x (c + s *\<^sub>R d) a) = (\<lambda>s. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (a \<bullet> (vec_nth x n - vec_nth x p))
        * sin ((c \<bullet> (vec_nth x n - vec_nth x p))
            + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))"
    by (rule ext) (simp add: Wc_d1_def inner_line)
  have eqd: "Wc_dd x (c + t *\<^sub>R d) a d
      = - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        (a \<bullet> (vec_nth x n - vec_nth x p))
        * (d \<bullet> (vec_nth x n - vec_nth x p))
        * cos ((c \<bullet> (vec_nth x n - vec_nth x p))
            + t * (d \<bullet> (vec_nth x n - vec_nth x p))))"
    by (simp add: Wc_dd_def inner_line algebra_simps)
  show ?thesis unfolding eqf eqd by (rule D)
qed

lemma Wc_dd_curve_mixed:
  fixes x :: "(real^2)^'n::finite" and c a b d :: "real^2"
  shows "((\<lambda>t. Wc_dd x (c + t *\<^sub>R d) a b) has_field_derivative
      Wc_ddd x (c + t *\<^sub>R d) a b d) (at t)"
proof -
  have inner_line: "(c + s *\<^sub>R d) \<bullet> w = (c \<bullet> w) + s * (d \<bullet> w)"
    for s :: real and w :: "real^2"
    by (simp add: inner_add_left inner_scaleR_left)
  have D: "((\<lambda>s. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (a \<bullet> (vec_nth x n - vec_nth x p))
      * (b \<bullet> (vec_nth x n - vec_nth x p))
      * cos ((c \<bullet> (vec_nth x n - vec_nth x p))
          + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))
    has_field_derivative
      (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        (a \<bullet> (vec_nth x n - vec_nth x p))
        * (b \<bullet> (vec_nth x n - vec_nth x p))
        * (d \<bullet> (vec_nth x n - vec_nth x p))
        * sin ((c \<bullet> (vec_nth x n - vec_nth x p))
            + t * (d \<bullet> (vec_nth x n - vec_nth x p)))))
    (at t)"
  proof -
    have "((\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        - ((a \<bullet> (vec_nth x n - vec_nth x p))
          * (b \<bullet> (vec_nth x n - vec_nth x p))
          * cos ((c \<bullet> (vec_nth x n - vec_nth x p))
              + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))
      has_field_derivative
        (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          (a \<bullet> (vec_nth x n - vec_nth x p))
          * (b \<bullet> (vec_nth x n - vec_nth x p))
          * (d \<bullet> (vec_nth x n - vec_nth x p))
          * sin ((c \<bullet> (vec_nth x n - vec_nth x p))
              + t * (d \<bullet> (vec_nth x n - vec_nth x p)))))
      (at t)"
      by (intro derivative_intros DERIV_neg_prod_cos)
    thus ?thesis
      by (simp only: sum_negf)
  qed
  have eqf: "(\<lambda>s. Wc_dd x (c + s *\<^sub>R d) a b) = (\<lambda>s. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (a \<bullet> (vec_nth x n - vec_nth x p))
      * (b \<bullet> (vec_nth x n - vec_nth x p))
      * cos ((c \<bullet> (vec_nth x n - vec_nth x p))
          + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))"
    by (rule ext) (simp add: Wc_dd_def inner_line)
  have eqd: "Wc_ddd x (c + t *\<^sub>R d) a b d
      = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        (a \<bullet> (vec_nth x n - vec_nth x p))
        * (b \<bullet> (vec_nth x n - vec_nth x p))
        * (d \<bullet> (vec_nth x n - vec_nth x p))
        * sin ((c \<bullet> (vec_nth x n - vec_nth x p))
            + t * (d \<bullet> (vec_nth x n - vec_nth x p))))"
    by (simp add: Wc_ddd_def inner_line algebra_simps)
  show ?thesis unfolding eqf eqd by (rule D)
qed

lemma Wc_path_d1:
  fixes x :: "(real^2)^'n::finite" and cpath :: "real \<Rightarrow> real^2"
  assumes cder: "(cpath has_vector_derivative c1) (at t)"
  shows "((\<lambda>s. Wc x (cpath s)) has_field_derivative Wc_d1 x (cpath t) c1) (at t)"
proof -
  have cder': "((\<lambda>s. cpath s) has_derivative (\<lambda>r. r *\<^sub>R c1)) (at t)"
    using cder by (simp add: has_vector_derivative_def)
  have Wder: "((\<lambda>c'. Wc x c') has_derivative (\<lambda>u. Wc_d1 x (cpath t) u)) (at (cpath t))"
    by (rule has_derivative_Wc_c)
  have comp: "((\<lambda>s. Wc x (cpath s)) has_derivative
      ((\<lambda>u. Wc_d1 x (cpath t) u) \<circ> (\<lambda>r. r *\<^sub>R c1))) (at t)"
    using diff_chain_at[OF cder' Wder] by (simp add: o_def)
  show ?thesis
    unfolding has_field_derivative_def
    by (rule has_derivative_eq_rhs[OF comp])
       (rule ext, simp only: o_def Wc_d1_scale_dir mult.commute)
qed

lemma inner_path_has_field_derivative:
  fixes f :: "real \<Rightarrow> real^2"
  assumes fder: "(f has_vector_derivative v) (at t)"
  shows "((\<lambda>s. f s \<bullet> a) has_field_derivative v \<bullet> a) (at t)"
proof -
  have fder': "(f has_derivative (\<lambda>r. r *\<^sub>R v)) (at t)"
    using fder by (simp only: has_vector_derivative_def)
  have innerder: "((\<lambda>y::real^2. y \<bullet> a) has_derivative (\<lambda>u. u \<bullet> a)) (at (f t))"
    by (rule bounded_linear.has_derivative[OF bounded_linear_inner_left has_derivative_ident])
  have comp: "((\<lambda>s. f s \<bullet> a) has_derivative
      ((\<lambda>u. u \<bullet> a) \<circ> (\<lambda>r. r *\<^sub>R v))) (at t)"
    using diff_chain_at[OF fder' innerder] by (simp only: o_def)
  show ?thesis
    unfolding has_field_derivative_def
    by (rule has_derivative_eq_rhs[OF comp])
       (rule ext, simp only: o_def inner_scaleR_left mult.commute)
qed

lemma Wc_path_d1_vary:
  fixes x :: "(real^2)^'n::finite"
    and cpath apath :: "real \<Rightarrow> real^2"
  assumes cder: "(cpath has_vector_derivative cvel) (at t)"
    and ader: "(apath has_vector_derivative avel) (at t)"
  shows "((\<lambda>s. Wc_d1 x (cpath s) (apath s)) has_field_derivative
      Wc_dd x (cpath t) (apath t) cvel + Wc_d1 x (cpath t) avel) (at t)"
proof -
  have per: "((\<lambda>s. - ((apath s \<bullet> \<delta>) * sin (cpath s \<bullet> \<delta>))) has_field_derivative
      - ((avel \<bullet> \<delta>) * sin (cpath t \<bullet> \<delta>))
      - ((apath t \<bullet> \<delta>) * (cvel \<bullet> \<delta>) * cos (cpath t \<bullet> \<delta>))) (at t)" for \<delta> :: "real^2"
  proof -
    have A: "((\<lambda>s. apath s \<bullet> \<delta>) has_field_derivative avel \<bullet> \<delta>) (at t)"
      by (rule inner_path_has_field_derivative[OF ader])
    have B: "((\<lambda>s. cpath s \<bullet> \<delta>) has_field_derivative cvel \<bullet> \<delta>) (at t)"
      by (rule inner_path_has_field_derivative[OF cder])
    have S: "((\<lambda>s. sin (cpath s \<bullet> \<delta>)) has_field_derivative
        cos (cpath t \<bullet> \<delta>) * (cvel \<bullet> \<delta>)) (at t)"
      using DERIV_chain2[OF DERIV_sin B] by simp
    have P: "((\<lambda>s. (apath s \<bullet> \<delta>) * sin (cpath s \<bullet> \<delta>)) has_field_derivative
        (avel \<bullet> \<delta>) * sin (cpath t \<bullet> \<delta>)
        + (apath t \<bullet> \<delta>) * (cos (cpath t \<bullet> \<delta>) * (cvel \<bullet> \<delta>))) (at t)"
      using DERIV_mult[OF A S] by (simp add: algebra_simps)
    from DERIV_minus[OF P]
    show ?thesis by (simp add: algebra_simps)
  qed
  have D: "((\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      - ((apath s \<bullet> (vec_nth x n - vec_nth x p))
          * sin (cpath s \<bullet> (vec_nth x n - vec_nth x p))))
    has_field_derivative
      (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        - ((avel \<bullet> (vec_nth x n - vec_nth x p))
            * sin (cpath t \<bullet> (vec_nth x n - vec_nth x p)))
        - ((apath t \<bullet> (vec_nth x n - vec_nth x p))
            * (cvel \<bullet> (vec_nth x n - vec_nth x p))
            * cos (cpath t \<bullet> (vec_nth x n - vec_nth x p)))))
    (at t)"
    by (intro derivative_intros per)
  have eqf: "(\<lambda>s. Wc_d1 x (cpath s) (apath s)) = (\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      - ((apath s \<bullet> (vec_nth x n - vec_nth x p))
          * sin (cpath s \<bullet> (vec_nth x n - vec_nth x p))))"
    by (rule ext) (simp add: Wc_d1_def sum_negf)
  have eqd: "Wc_dd x (cpath t) (apath t) cvel + Wc_d1 x (cpath t) avel
      = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        - ((avel \<bullet> (vec_nth x n - vec_nth x p))
            * sin (cpath t \<bullet> (vec_nth x n - vec_nth x p)))
        - ((apath t \<bullet> (vec_nth x n - vec_nth x p))
            * (cvel \<bullet> (vec_nth x n - vec_nth x p))
            * cos (cpath t \<bullet> (vec_nth x n - vec_nth x p))))"
    by (simp add: Wc_dd_def Wc_d1_def sum.distrib sum_negf sum_subtractf
        algebra_simps)
  show ?thesis
    unfolding eqf eqd by (rule D)
qed

lemma Wc_path_d2:
  fixes x :: "(real^2)^'n::finite"
    and cpath c1path :: "real \<Rightarrow> real^2"
  assumes cder: "(cpath has_vector_derivative c1path t) (at t)"
    and c1der: "(c1path has_vector_derivative c2) (at t)"
  shows "((\<lambda>s. Wc_d1 x (cpath s) (c1path s)) has_field_derivative
      Wc_dd x (cpath t) (c1path t) (c1path t) + Wc_d1 x (cpath t) c2) (at t)"
proof -
  have per: "((\<lambda>s. - ((c1path s \<bullet> \<delta>) * sin (cpath s \<bullet> \<delta>))) has_field_derivative
      - ((c2 \<bullet> \<delta>) * sin (cpath t \<bullet> \<delta>))
      - ((c1path t \<bullet> \<delta>) * (c1path t \<bullet> \<delta>) * cos (cpath t \<bullet> \<delta>))) (at t)" for \<delta> :: "real^2"
  proof -
    have A: "((\<lambda>s. c1path s \<bullet> \<delta>) has_field_derivative c2 \<bullet> \<delta>) (at t)"
      by (rule inner_path_has_field_derivative[OF c1der])
    have B: "((\<lambda>s. cpath s \<bullet> \<delta>) has_field_derivative c1path t \<bullet> \<delta>) (at t)"
      by (rule inner_path_has_field_derivative[OF cder])
    have S: "((\<lambda>s. sin (cpath s \<bullet> \<delta>)) has_field_derivative
        cos (cpath t \<bullet> \<delta>) * (c1path t \<bullet> \<delta>)) (at t)"
      using DERIV_chain2[OF DERIV_sin B] by simp
    have P: "((\<lambda>s. (c1path s \<bullet> \<delta>) * sin (cpath s \<bullet> \<delta>)) has_field_derivative
        (c2 \<bullet> \<delta>) * sin (cpath t \<bullet> \<delta>)
        + (c1path t \<bullet> \<delta>) * (cos (cpath t \<bullet> \<delta>) * (c1path t \<bullet> \<delta>))) (at t)"
      using DERIV_mult[OF A S] by (simp add: algebra_simps)
    from DERIV_minus[OF P]
    show ?thesis by (simp add: algebra_simps)
  qed
  have D: "((\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      - ((c1path s \<bullet> (vec_nth x n - vec_nth x p))
          * sin (cpath s \<bullet> (vec_nth x n - vec_nth x p))))
    has_field_derivative
      (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        - ((c2 \<bullet> (vec_nth x n - vec_nth x p))
            * sin (cpath t \<bullet> (vec_nth x n - vec_nth x p)))
        - ((c1path t \<bullet> (vec_nth x n - vec_nth x p))
            * (c1path t \<bullet> (vec_nth x n - vec_nth x p))
            * cos (cpath t \<bullet> (vec_nth x n - vec_nth x p)))))
    (at t)"
    by (intro derivative_intros per)
  have eqf: "(\<lambda>s. Wc_d1 x (cpath s) (c1path s)) = (\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      - ((c1path s \<bullet> (vec_nth x n - vec_nth x p))
          * sin (cpath s \<bullet> (vec_nth x n - vec_nth x p))))"
    by (rule ext) (simp add: Wc_d1_def sum_negf)
  have eqd: "Wc_dd x (cpath t) (c1path t) (c1path t) + Wc_d1 x (cpath t) c2
      = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        - ((c2 \<bullet> (vec_nth x n - vec_nth x p))
            * sin (cpath t \<bullet> (vec_nth x n - vec_nth x p)))
        - ((c1path t \<bullet> (vec_nth x n - vec_nth x p))
            * (c1path t \<bullet> (vec_nth x n - vec_nth x p))
            * cos (cpath t \<bullet> (vec_nth x n - vec_nth x p))))"
    by (simp add: Wc_dd_def Wc_d1_def sum.distrib sum_negf sum_subtractf
        algebra_simps)
  show ?thesis
    unfolding eqf eqd by (rule D)
qed

lemma Wc_path_dd_vary:
  fixes x :: "(real^2)^'n::finite"
    and cpath apath bpath :: "real \<Rightarrow> real^2"
  assumes cder: "(cpath has_vector_derivative cvel) (at t)"
    and ader: "(apath has_vector_derivative avel) (at t)"
    and bder: "(bpath has_vector_derivative bvel) (at t)"
  shows "((\<lambda>s. Wc_dd x (cpath s) (apath s) (bpath s)) has_field_derivative
      Wc_ddd x (cpath t) (apath t) (bpath t) cvel
      + Wc_dd x (cpath t) avel (bpath t)
      + Wc_dd x (cpath t) (apath t) bvel) (at t)"
proof -
  have per: "((\<lambda>s. - ((apath s \<bullet> \<delta>) * (bpath s \<bullet> \<delta>) * cos (cpath s \<bullet> \<delta>)))
      has_field_derivative
        (apath t \<bullet> \<delta>) * (bpath t \<bullet> \<delta>) * (cvel \<bullet> \<delta>) * sin (cpath t \<bullet> \<delta>)
        - ((avel \<bullet> \<delta>) * (bpath t \<bullet> \<delta>) * cos (cpath t \<bullet> \<delta>))
        - ((apath t \<bullet> \<delta>) * (bvel \<bullet> \<delta>) * cos (cpath t \<bullet> \<delta>))) (at t)"
    for \<delta> :: "real^2"
  proof -
    have A: "((\<lambda>s. apath s \<bullet> \<delta>) has_field_derivative avel \<bullet> \<delta>) (at t)"
      by (rule inner_path_has_field_derivative[OF ader])
    have B: "((\<lambda>s. bpath s \<bullet> \<delta>) has_field_derivative bvel \<bullet> \<delta>) (at t)"
      by (rule inner_path_has_field_derivative[OF bder])
    have C: "((\<lambda>s. cpath s \<bullet> \<delta>) has_field_derivative cvel \<bullet> \<delta>) (at t)"
      by (rule inner_path_has_field_derivative[OF cder])
    have Cos: "((\<lambda>s. cos (cpath s \<bullet> \<delta>)) has_field_derivative
        - sin (cpath t \<bullet> \<delta>) * (cvel \<bullet> \<delta>)) (at t)"
      using DERIV_chain2[OF DERIV_cos C] by simp
    have AB: "((\<lambda>s. (apath s \<bullet> \<delta>) * (bpath s \<bullet> \<delta>)) has_field_derivative
        (avel \<bullet> \<delta>) * (bpath t \<bullet> \<delta>) + (apath t \<bullet> \<delta>) * (bvel \<bullet> \<delta>)) (at t)"
      using DERIV_mult[OF A B] by (simp add: algebra_simps)
    have P: "((\<lambda>s. ((apath s \<bullet> \<delta>) * (bpath s \<bullet> \<delta>)) * cos (cpath s \<bullet> \<delta>))
        has_field_derivative
          ((avel \<bullet> \<delta>) * (bpath t \<bullet> \<delta>) + (apath t \<bullet> \<delta>) * (bvel \<bullet> \<delta>))
            * cos (cpath t \<bullet> \<delta>)
          + ((apath t \<bullet> \<delta>) * (bpath t \<bullet> \<delta>))
            * (- sin (cpath t \<bullet> \<delta>) * (cvel \<bullet> \<delta>))) (at t)"
      using DERIV_mult[OF AB Cos] by (simp add: algebra_simps)
    from DERIV_minus[OF P]
    show ?thesis by (simp add: algebra_simps)
  qed
  have D: "((\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      - ((apath s \<bullet> (vec_nth x n - vec_nth x p))
          * (bpath s \<bullet> (vec_nth x n - vec_nth x p))
          * cos (cpath s \<bullet> (vec_nth x n - vec_nth x p))))
    has_field_derivative
      (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        (apath t \<bullet> (vec_nth x n - vec_nth x p))
        * (bpath t \<bullet> (vec_nth x n - vec_nth x p))
        * (cvel \<bullet> (vec_nth x n - vec_nth x p))
        * sin (cpath t \<bullet> (vec_nth x n - vec_nth x p))
        - ((avel \<bullet> (vec_nth x n - vec_nth x p))
            * (bpath t \<bullet> (vec_nth x n - vec_nth x p))
            * cos (cpath t \<bullet> (vec_nth x n - vec_nth x p)))
        - ((apath t \<bullet> (vec_nth x n - vec_nth x p))
            * (bvel \<bullet> (vec_nth x n - vec_nth x p))
            * cos (cpath t \<bullet> (vec_nth x n - vec_nth x p)))))
    (at t)"
    by (intro derivative_intros per)
  have eqf: "(\<lambda>s. Wc_dd x (cpath s) (apath s) (bpath s)) = (\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      - ((apath s \<bullet> (vec_nth x n - vec_nth x p))
          * (bpath s \<bullet> (vec_nth x n - vec_nth x p))
          * cos (cpath s \<bullet> (vec_nth x n - vec_nth x p))))"
    by (rule ext) (simp add: Wc_dd_def sum_negf)
  have eqd: "Wc_ddd x (cpath t) (apath t) (bpath t) cvel
      + Wc_dd x (cpath t) avel (bpath t)
      + Wc_dd x (cpath t) (apath t) bvel
      = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
        (apath t \<bullet> (vec_nth x n - vec_nth x p))
        * (bpath t \<bullet> (vec_nth x n - vec_nth x p))
        * (cvel \<bullet> (vec_nth x n - vec_nth x p))
        * sin (cpath t \<bullet> (vec_nth x n - vec_nth x p))
        - ((avel \<bullet> (vec_nth x n - vec_nth x p))
            * (bpath t \<bullet> (vec_nth x n - vec_nth x p))
            * cos (cpath t \<bullet> (vec_nth x n - vec_nth x p)))
        - ((apath t \<bullet> (vec_nth x n - vec_nth x p))
            * (bvel \<bullet> (vec_nth x n - vec_nth x p))
            * cos (cpath t \<bullet> (vec_nth x n - vec_nth x p))))"
    by (simp add: Wc_ddd_def Wc_dd_def sum.distrib sum_negf sum_subtractf
        algebra_simps)
  show ?thesis
    unfolding eqf eqd by (rule D)
qed

lemma Wc_path_d3_step:
  fixes x :: "(real^2)^'n::finite"
    and cpath c1path c2path :: "real \<Rightarrow> real^2"
  assumes cder: "(cpath has_vector_derivative c1path t) (at t)"
    and c1der: "(c1path has_vector_derivative c2path t) (at t)"
    and c2der: "(c2path has_vector_derivative c3) (at t)"
  shows "((\<lambda>s.
      Wc_dd x (cpath s) (c1path s) (c1path s)
      + Wc_d1 x (cpath s) (c2path s)) has_field_derivative
        Wc_ddd x (cpath t) (c1path t) (c1path t) (c1path t)
        + 3 * Wc_dd x (cpath t) (c1path t) (c2path t)
        + Wc_d1 x (cpath t) c3) (at t)"
proof -
  have dA: "((\<lambda>s. Wc_dd x (cpath s) (c1path s) (c1path s)) has_field_derivative
      Wc_ddd x (cpath t) (c1path t) (c1path t) (c1path t)
      + Wc_dd x (cpath t) (c2path t) (c1path t)
      + Wc_dd x (cpath t) (c1path t) (c2path t)) (at t)"
    by (rule Wc_path_dd_vary[OF cder c1der c1der])
  have dB: "((\<lambda>s. Wc_d1 x (cpath s) (c2path s)) has_field_derivative
      Wc_dd x (cpath t) (c2path t) (c1path t)
      + Wc_d1 x (cpath t) c3) (at t)"
    by (rule Wc_path_d1_vary[OF cder c2der])
  have dsum: "((\<lambda>s.
      Wc_dd x (cpath s) (c1path s) (c1path s)
      + Wc_d1 x (cpath s) (c2path s)) has_field_derivative
        (Wc_ddd x (cpath t) (c1path t) (c1path t) (c1path t)
        + Wc_dd x (cpath t) (c2path t) (c1path t)
        + Wc_dd x (cpath t) (c1path t) (c2path t))
        + (Wc_dd x (cpath t) (c2path t) (c1path t)
        + Wc_d1 x (cpath t) c3)) (at t)"
    by (rule DERIV_add[OF dA dB])
  show ?thesis
    using dsum by (simp add: Wc_dd_sym algebra_simps)
qed

lemma Wc_path_third_deriv:
  fixes x :: "(real^2)^'n::finite"
    and cpath c1path c2path :: "real \<Rightarrow> real^2"
  assumes cder: "\<And>s. (cpath has_vector_derivative c1path s) (at s)"
    and c1der: "\<And>s. (c1path has_vector_derivative c2path s) (at s)"
    and c2der0: "(c2path has_vector_derivative c3) (at 0)"
  shows "(deriv (deriv (deriv (\<lambda>s. Wc x (cpath s))))) 0
      = Wc_ddd x (cpath 0) (c1path 0) (c1path 0) (c1path 0)
        + 3 * Wc_dd x (cpath 0) (c1path 0) (c2path 0)
        + Wc_d1 x (cpath 0) c3"
proof -
  have d1: "deriv (\<lambda>s. Wc x (cpath s))
      = (\<lambda>s. Wc_d1 x (cpath s) (c1path s))"
  proof (rule ext)
    fix s
    show "deriv (\<lambda>s. Wc x (cpath s)) s = Wc_d1 x (cpath s) (c1path s)"
      by (rule DERIV_imp_deriv[OF Wc_path_d1[OF cder]])
  qed
  have d2: "deriv (\<lambda>s. Wc_d1 x (cpath s) (c1path s))
      = (\<lambda>s. Wc_dd x (cpath s) (c1path s) (c1path s)
          + Wc_d1 x (cpath s) (c2path s))"
  proof (rule ext)
    fix s
    show "deriv (\<lambda>s. Wc_d1 x (cpath s) (c1path s)) s
        = Wc_dd x (cpath s) (c1path s) (c1path s) + Wc_d1 x (cpath s) (c2path s)"
      by (rule DERIV_imp_deriv[OF Wc_path_d2[OF cder c1der]])
  qed
  have d3: "deriv (\<lambda>s.
      Wc_dd x (cpath s) (c1path s) (c1path s)
      + Wc_d1 x (cpath s) (c2path s)) 0
      = Wc_ddd x (cpath 0) (c1path 0) (c1path 0) (c1path 0)
        + 3 * Wc_dd x (cpath 0) (c1path 0) (c2path 0)
        + Wc_d1 x (cpath 0) c3"
    by (rule DERIV_imp_deriv[OF Wc_path_d3_step[OF cder c1der c2der0]])
  show ?thesis
    unfolding d1 d2 by (rule d3)
qed

lemma Wc_cvec_dip_line_third_deriv:
  fixes x :: "(real^2)^'n::finite" and \<omega>0 \<omega>s \<omega> w :: "real^2"
  shows "(deriv (deriv (deriv
      (\<lambda>s. Wc x (cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w)))))) 0
      = Wc_ddd x (cvec_dip \<omega>0 \<omega>s \<omega>)
          (Dcvec_dip \<omega>0 \<omega>s \<omega> w)
          (Dcvec_dip \<omega>0 \<omega>s \<omega> w)
          (Dcvec_dip \<omega>0 \<omega>s \<omega> w)
        + 3 * Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>)
          (Dcvec_dip \<omega>0 \<omega>s \<omega> w)
          (D2cvec_dip \<omega>0 \<omega>s \<omega> w w)
        + Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>)
          (D3cvec_dip_line \<omega>0 \<omega>s \<omega> w)"
proof -
  define cpath where "cpath = (\<lambda>s. cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w))"
  define c1path where "c1path = (\<lambda>s. Dcvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w)"
  define c2path where "c2path = (\<lambda>s. D2cvec_dip \<omega>0 \<omega>s (\<omega> + s *\<^sub>R w) w w)"
  have cder: "\<And>s. (cpath has_vector_derivative c1path s) (at s)"
    unfolding cpath_def c1path_def by (rule cvec_dip_line_has_vector_derivative)
  have c1der: "\<And>s. (c1path has_vector_derivative c2path s) (at s)"
    unfolding c1path_def c2path_def by (rule cvec_dip_line_d1_has_vector_derivative)
  have c2der0: "(c2path has_vector_derivative D3cvec_dip_line \<omega>0 \<omega>s \<omega> w) (at 0)"
    unfolding c2path_def
    by (metis (lifting) add.right_neutral cvec_dip_line_d2_has_vector_derivative scaleR_simps(1))
  have raw: "(deriv (deriv (deriv (\<lambda>s. Wc x (cpath s))))) 0
      = Wc_ddd x (cpath 0) (c1path 0) (c1path 0) (c1path 0)
        + 3 * Wc_dd x (cpath 0) (c1path 0) (c2path 0)
        + Wc_d1 x (cpath 0) (D3cvec_dip_line \<omega>0 \<omega>s \<omega> w)"
    by (rule Wc_path_third_deriv[OF cder c1der c2der0])
  show ?thesis
    using raw unfolding cpath_def c1path_def c2path_def by simp
qed

end
