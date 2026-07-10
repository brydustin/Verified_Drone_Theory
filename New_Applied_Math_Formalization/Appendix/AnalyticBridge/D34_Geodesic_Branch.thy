theory D34_Geodesic_Branch
  imports D34_Analytic_Bridge
begin

section \<open>c-space normal coordinates: the flat intensity \<open>Wc\<close> and its radial cubic\<close>

text \<open>\<^bold>\<open>Design (the "geodesic/normal-coordinate" fix for the \<open>H11=H22=0\<close> stratum).\<close>
  The x-dependence of \<open>U_cart cvec gain x \<omega> = gain \<omega> * (cmod (A_cart cvec x \<omega>))\<^sup>2\<close>
  factors entirely through the value \<open>c = cvec \<omega> \<in> \<real>\<^sup>2\<close>: the phases are \<open>c \<bullet> x\<^sub>n\<close>.
  So the natural normal coordinates for the steering manifold are the \<open>c\<close>-coordinates
  themselves (on the branch \<open>det (Dcvec_dip) \<noteq> 0\<close> they are a genuine local chart), and
  the "geodesics" are straight lines \<open>t \<mapsto> c + t \<cdot> d\<close> in \<open>c\<close>-space --- no sphere
  machinery, no chart inversion.

  Define the \<open>c\<close>-space intensity \<open>Wc x c = \<Sum>\<^sub>n\<^sub>p cos (c \<bullet> (x\<^sub>n - x\<^sub>p))\<close> (the standard
  \<open>|\<Sum> cis|\<^sup>2\<close> expansion, proven below as \<open>Wc_eq_cmod_sq\<close>/\<open>U_cart_Wc\<close>).  Its
  \<open>t\<close>-derivatives along \<open>c + t \<cdot> d\<close> are the explicit trig sums \<open>Wc_d1/Wc_d2/Wc_d3\<close>.

  \<^bold>\<open>The point:\<close> for the RADIAL direction \<open>d = c\<close>, every one of these objects is a sum
  of terms \<open>g (c \<bullet> (x\<^sub>n - x\<^sub>p))\<close> for a single scalar function \<open>g\<close> --- so its x-slot
  derivative in ANY slot \<open>m\<close> with direction \<open>v\<close> is a sum of terms carrying the factor
  \<open>c \<bullet> v\<close>, which vanishes IDENTICALLY for \<open>v = perp2 c\<close>.  This is by construction the
  v-slot-independence property whose \<open>H_par\<close> analogue was machine-refuted
  (\<open>h_par_vslot_zero\<close> is false); here it needs no stratum hypotheses at all.  The
  master law is \<open>pair_phase_sum_perp_slot_zero\<close>; the payoff instance for the cubic is
  \<open>T3rad_slot_perp_zero\<close>.\<close>

definition Wc :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real" where
  "Wc x c = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cos (c \<bullet> (vec_nth x n - vec_nth x p)))"

subsection \<open>Connection to the array factor: \<open>Wc\<close> IS \<open>|A|\<^sup>2\<close>\<close>

lemma cnj_cis_neg: "cnj (cis t) = cis (- t)"
  by (simp add: complex_eq_iff)

lemma Wc_eq_cmod_sq:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  shows "Wc x c = (cmod (\<Sum>n\<in>UNIV. cis (- (c \<bullet> vec_nth x n))))\<^sup>2"
proof -
  have expand: "(\<Sum>n\<in>UNIV. cis (- (c \<bullet> vec_nth x n))) * cnj (\<Sum>p\<in>UNIV. cis (- (c \<bullet> vec_nth x p)))
      = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cis ((c \<bullet> vec_nth x p) - (c \<bullet> vec_nth x n)))"
  proof -
    have "cnj (\<Sum>p\<in>UNIV. cis (- (c \<bullet> vec_nth x p))) = (\<Sum>p\<in>UNIV. cis (c \<bullet> vec_nth x p))"
      by (simp add: cnj_cis_neg)
    hence "(\<Sum>n\<in>UNIV. cis (- (c \<bullet> vec_nth x n))) * cnj (\<Sum>p\<in>UNIV. cis (- (c \<bullet> vec_nth x p)))
        = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cis (- (c \<bullet> vec_nth x n)) * cis (c \<bullet> vec_nth x p))"
      by (simp add: sum_product)
    also have "\<dots> = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cis ((c \<bullet> vec_nth x p) - (c \<bullet> vec_nth x n)))"
      by (simp add: cis_mult algebra_simps)
    finally show ?thesis .
  qed
  have modsq: "Re (z * cnj z) = (cmod z)\<^sup>2" for z :: complex
    by (simp add: complex_mult_cnj cmod_power2)
  have "(cmod (\<Sum>n\<in>UNIV. cis (- (c \<bullet> vec_nth x n))))\<^sup>2
      = Re ((\<Sum>n\<in>UNIV. cis (- (c \<bullet> vec_nth x n))) * cnj (\<Sum>p\<in>UNIV. cis (- (c \<bullet> vec_nth x p))))"
    by (rule modsq[symmetric])
  hence Re_eq: "(cmod (\<Sum>n\<in>UNIV. cis (- (c \<bullet> vec_nth x n))))\<^sup>2
      = Re (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cis ((c \<bullet> vec_nth x p) - (c \<bullet> vec_nth x n)))"
    unfolding expand by simp
  have "Re (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cis ((c \<bullet> vec_nth x p) - (c \<bullet> vec_nth x n)))
      = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cos ((c \<bullet> vec_nth x p) - (c \<bullet> vec_nth x n)))"
    by simp
  also have "\<dots> = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cos (c \<bullet> (vec_nth x n - vec_nth x p)))"
    by (intro sum.cong refl) (metis cos_minus inner_diff_right minus_diff_eq)
  finally show ?thesis
    using Re_eq by (simp add: Wc_def)
qed

lemma U_cart_Wc:
  fixes x :: "(real^2)^'n::finite"
  shows "U_cart cvec gain x \<omega> = gain \<omega> * Wc x (cvec \<omega>)"
  unfolding U_cart_def A_cart_def Wc_eq_cmod_sq by simp

lemma U_dip_Wc:
  fixes x :: "(real^2)^'n::finite"
  shows "U_dip \<omega>0 \<omega>s x \<omega> = gain_dip \<omega> * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)"
  unfolding U_dip_def by (rule U_cart_Wc)

subsection \<open>The master pair-phase law: x-derivative of \<open>\<Sum>\<^sub>n\<^sub>p g (c \<bullet> (x\<^sub>n - x\<^sub>p))\<close>\<close>

lemma bounded_linear_pair_inner:
  fixes c :: "real^2" and n p :: "'n::finite"
  shows "bounded_linear (\<lambda>y::(real^2)^'n. c \<bullet> (vec_nth y n - vec_nth y p))"
  by (intro bounded_linear_compose[OF bounded_linear_inner_right]
            bounded_linear_sub bounded_linear_vec_nth)

lemma has_derivative_pair_phase_sum_x:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite"
    and g g' :: "real \<Rightarrow> real"
  assumes dg: "\<And>u. (g has_field_derivative g' u) (at u)"
  shows "((\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c \<bullet> (vec_nth y n - vec_nth y p))) has_derivative
      (\<lambda>h. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x p))
             * (c \<bullet> (vec_nth h n - vec_nth h p)))) (at x)"
proof -
  have summand: "((\<lambda>y. g (c \<bullet> (vec_nth y n - vec_nth y p))) has_derivative
      (\<lambda>h. g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> (vec_nth h n - vec_nth h p)))) (at x)"
    for n p :: 'n
  proof -
    have lin: "((\<lambda>y::(real^2)^'n. c \<bullet> (vec_nth y n - vec_nth y p)) has_derivative
        (\<lambda>h. c \<bullet> (vec_nth h n - vec_nth h p))) (at x)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_pair_inner has_derivative_ident])
    have outer: "(g has_derivative (\<lambda>u. g' (c \<bullet> (vec_nth x n - vec_nth x p)) * u))
        (at (c \<bullet> (vec_nth x n - vec_nth x p)))"
      using dg[of "c \<bullet> (vec_nth x n - vec_nth x p)"]
      unfolding has_field_derivative_def by simp
    show ?thesis
      using has_derivative_compose[OF lin outer] by simp
  qed
  show ?thesis
    by (intro has_derivative_sum) (rule summand)
qed

text \<open>\<^bold>\<open>The master vanishing law.\<close>  For ANY scalar profile \<open>g\<close> (with everywhere-defined
  field derivative), the x-slot derivative of the pair-phase sum in a \<open>perp2 c\<close>
  direction is IDENTICALLY zero: every summand of the derivative carries the factor
  \<open>c \<bullet> (h\<^sub>n - h\<^sub>p)\<close>, which for \<open>h = slot m (perp2 c)\<close> is \<open>\<plusminus>(c \<bullet> perp2 c) = 0\<close> or \<open>c \<bullet> 0 = 0\<close>.
  No criticality, no Hessian conditions, no genericity: an identity in \<open>x\<close>.\<close>

theorem pair_phase_sum_perp_slot_zero:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
    and g g' :: "real \<Rightarrow> real"
  assumes dg: "\<And>u. (g has_field_derivative g' u) (at u)"
  shows "frechet_derivative (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c \<bullet> (vec_nth y n - vec_nth y p)))
           (at x) (slot m (perp2 c)) = 0"
proof -
  have fd: "frechet_derivative (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c \<bullet> (vec_nth y n - vec_nth y p))) (at x)
      = (\<lambda>h. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x p))
               * (c \<bullet> (vec_nth h n - vec_nth h p)))"
    by (rule frechet_derivative_at[OF has_derivative_pair_phase_sum_x[OF dg], symmetric])
  have term0: "c \<bullet> (vec_nth (slot m (perp2 c)) n - vec_nth (slot m (perp2 c)) p) = 0"
    for n p :: 'n
    by (auto simp: slot_nth inner_diff_right perp2_orth)
  show ?thesis
    unfolding fd by (simp add: term0)
qed

subsection \<open>Directional derivatives of \<open>Wc\<close> along straight lines in \<open>c\<close>-space\<close>

definition Wc_d1 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "Wc_d1 x c d = - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (d \<bullet> (vec_nth x n - vec_nth x p)) * sin (c \<bullet> (vec_nth x n - vec_nth x p)))"

definition Wc_d2 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "Wc_d2 x c d = - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (d \<bullet> (vec_nth x n - vec_nth x p))\<^sup>2 * cos (c \<bullet> (vec_nth x n - vec_nth x p)))"

definition Wc_d3 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "Wc_d3 x c d = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (d \<bullet> (vec_nth x n - vec_nth x p)) ^ 3 * sin (c \<bullet> (vec_nth x n - vec_nth x p)))"

lemma Wc_line_expand:
  fixes x :: "(real^2)^'n::finite"
  shows "Wc x (c + t *\<^sub>R d) = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      cos ((c \<bullet> (vec_nth x n - vec_nth x p)) + t * (d \<bullet> (vec_nth x n - vec_nth x p))))"
  by (simp add: Wc_def inner_add_left inner_scaleR_left)

lemma Wc_curve_d1:
  fixes x :: "(real^2)^'n::finite" and c d :: "real^2"
  shows "((\<lambda>t. Wc x (c + t *\<^sub>R d)) has_field_derivative Wc_d1 x (c + t *\<^sub>R d) d) (at t)"
proof -
  have inner_line: "(c + s *\<^sub>R d) \<bullet> w = (c \<bullet> w) + s * (d \<bullet> w)" for s :: real and w :: "real^2"
    by (simp add: inner_add_left inner_scaleR_left)
  have D: "((\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      cos ((c \<bullet> (vec_nth x n - vec_nth x p)) + s * (d \<bullet> (vec_nth x n - vec_nth x p))))
    has_field_derivative
      (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. - ((d \<bullet> (vec_nth x n - vec_nth x p))
        * sin ((c \<bullet> (vec_nth x n - vec_nth x p)) + t * (d \<bullet> (vec_nth x n - vec_nth x p))))))
    (at t)"
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have eqf: "(\<lambda>s. Wc x (c + s *\<^sub>R d)) = (\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      cos ((c \<bullet> (vec_nth x n - vec_nth x p)) + s * (d \<bullet> (vec_nth x n - vec_nth x p))))"
    by (rule ext) (rule Wc_line_expand)
  have eqd: "Wc_d1 x (c + t *\<^sub>R d) d
      = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. - ((d \<bullet> (vec_nth x n - vec_nth x p))
          * sin ((c \<bullet> (vec_nth x n - vec_nth x p)) + t * (d \<bullet> (vec_nth x n - vec_nth x p)))))"
    by (simp add: Wc_d1_def inner_line sum_negf)
  show ?thesis unfolding eqf eqd by (rule D)
qed

lemma Wc_curve_d2:
  fixes x :: "(real^2)^'n::finite" and c d :: "real^2"
  shows "((\<lambda>t. Wc_d1 x (c + t *\<^sub>R d) d) has_field_derivative Wc_d2 x (c + t *\<^sub>R d) d) (at t)"
proof -
  have inner_line: "(c + s *\<^sub>R d) \<bullet> w = (c \<bullet> w) + s * (d \<bullet> w)" for s :: real and w :: "real^2"
    by (simp add: inner_add_left inner_scaleR_left)
  have D: "((\<lambda>s. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. (d \<bullet> (vec_nth x n - vec_nth x p))
      * sin ((c \<bullet> (vec_nth x n - vec_nth x p)) + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))
    has_field_derivative
      - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. (d \<bullet> (vec_nth x n - vec_nth x p))\<^sup>2
        * cos ((c \<bullet> (vec_nth x n - vec_nth x p)) + t * (d \<bullet> (vec_nth x n - vec_nth x p)))))
    (at t)"
    by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)
  have eqf: "(\<lambda>s. Wc_d1 x (c + s *\<^sub>R d) d) = (\<lambda>s. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (d \<bullet> (vec_nth x n - vec_nth x p))
        * sin ((c \<bullet> (vec_nth x n - vec_nth x p)) + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))"
    by (rule ext) (simp add: Wc_d1_def inner_line)
  have eqd: "Wc_d2 x (c + t *\<^sub>R d) d = - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (d \<bullet> (vec_nth x n - vec_nth x p))\<^sup>2
        * cos ((c \<bullet> (vec_nth x n - vec_nth x p)) + t * (d \<bullet> (vec_nth x n - vec_nth x p))))"
    by (simp add: Wc_d2_def inner_line)
  show ?thesis unfolding eqf eqd by (rule D)
qed

lemma DERIV_neg_sq_cos:
  fixes a b t :: real
  shows "((\<lambda>s. - (b\<^sup>2 * cos (a + s * b))) has_field_derivative b ^ 3 * sin (a + t * b)) (at t)"
proof -
  have D: "((\<lambda>s. - (b\<^sup>2 * cos (a + s * b))) has_field_derivative
      b\<^sup>2 * (sin (a + t * b) * b)) (at t)"
    by (auto intro!: derivative_eq_intros)
  show ?thesis using D
    by (simp add: power2_eq_square power3_eq_cube algebra_simps)
qed

lemma Wc_curve_d3:
  fixes x :: "(real^2)^'n::finite" and c d :: "real^2"
  shows "((\<lambda>t. Wc_d2 x (c + t *\<^sub>R d) d) has_field_derivative Wc_d3 x (c + t *\<^sub>R d) d) (at t)"
proof -
  have inner_line: "(c + s *\<^sub>R d) \<bullet> w = (c \<bullet> w) + s * (d \<bullet> w)" for s :: real and w :: "real^2"
    by (simp add: inner_add_left inner_scaleR_left)
  have D: "((\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. - ((d \<bullet> (vec_nth x n - vec_nth x p))\<^sup>2
      * cos ((c \<bullet> (vec_nth x n - vec_nth x p)) + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))
    has_field_derivative
      (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. (d \<bullet> (vec_nth x n - vec_nth x p)) ^ 3
        * sin ((c \<bullet> (vec_nth x n - vec_nth x p)) + t * (d \<bullet> (vec_nth x n - vec_nth x p)))))
    (at t)"
    by (intro derivative_intros DERIV_neg_sq_cos)
  have eqf: "(\<lambda>s. Wc_d2 x (c + s *\<^sub>R d) d) = (\<lambda>s. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      - ((d \<bullet> (vec_nth x n - vec_nth x p))\<^sup>2
        * cos ((c \<bullet> (vec_nth x n - vec_nth x p)) + s * (d \<bullet> (vec_nth x n - vec_nth x p)))))"
    by (rule ext) (simp add: Wc_d2_def inner_line sum_negf)
  have eqd: "Wc_d3 x (c + t *\<^sub>R d) d = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (d \<bullet> (vec_nth x n - vec_nth x p)) ^ 3
        * sin ((c \<bullet> (vec_nth x n - vec_nth x p)) + t * (d \<bullet> (vec_nth x n - vec_nth x p))))"
    by (simp add: Wc_d3_def inner_line)
  show ?thesis unfolding eqf eqd by (rule D)
qed

subsection \<open>The radial cubic \<open>T3rad\<close> and its identically-vanishing perp-slot derivative\<close>

definition T3rad :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real" where
  "T3rad x c = Wc_d3 x c c"

text \<open>With \<open>d = c\<close> the cubic is a single-profile pair-phase sum: \<open>g u = u\<^sup>3 * sin u\<close>.\<close>

lemma T3rad_pair_phase_form:
  fixes x :: "(real^2)^'n::finite"
  shows "T3rad x c = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (\<lambda>u. u ^ 3 * sin u) (c \<bullet> (vec_nth x n - vec_nth x p)))"
  by (simp add: T3rad_def Wc_d3_def)

theorem T3rad_slot_perp_zero:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  shows "frechet_derivative (\<lambda>y. T3rad y c) (at x) (slot m (perp2 c)) = 0"
proof -
  have dg: "((\<lambda>u. u ^ 3 * sin u) has_field_derivative
      (3 * u\<^sup>2 * sin u + u ^ 3 * cos u)) (at u)" for u :: real
    by (auto intro!: derivative_eq_intros simp: power2_eq_square power3_eq_cube algebra_simps)
  have eqf: "(\<lambda>y. T3rad y c) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (\<lambda>u. u ^ 3 * sin u) (c \<bullet> (vec_nth y n - vec_nth y p)))"
    by (rule ext) (rule T3rad_pair_phase_form)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_perp_slot_zero[OF dg])
qed

text \<open>The same master law also gives the perp-slot invariance of \<open>Wc\<close> itself and of the
  radial first/second directional derivatives --- the whole radial jet is v-slot-blind.\<close>

theorem Wc_slot_perp_zero:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  shows "frechet_derivative (\<lambda>y. Wc y c) (at x) (slot m (perp2 c)) = 0"
proof -
  have dg: "(cos has_field_derivative (- sin u)) (at u)" for u :: real
    by (auto intro!: derivative_eq_intros)
  have eqf: "(\<lambda>y. Wc y c) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cos (c \<bullet> (vec_nth y n - vec_nth y p)))"
    by (rule ext) (simp add: Wc_def)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_perp_slot_zero[OF dg])
qed

theorem T1rad_slot_perp_zero:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  shows "frechet_derivative (\<lambda>y. Wc_d1 y c c) (at x) (slot m (perp2 c)) = 0"
proof -
  have dg: "((\<lambda>u. - (u * sin u)) has_field_derivative
      (- (sin u + u * cos u))) (at u)" for u :: real
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have eqf: "(\<lambda>y. Wc_d1 y c c) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (\<lambda>u. - (u * sin u)) (c \<bullet> (vec_nth y n - vec_nth y p)))"
    by (rule ext) (simp add: Wc_d1_def sum_negf)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_perp_slot_zero[OF dg])
qed

theorem T2rad_slot_perp_zero:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  shows "frechet_derivative (\<lambda>y. Wc_d2 y c c) (at x) (slot m (perp2 c)) = 0"
proof -
  have dg: "((\<lambda>u. - (u\<^sup>2 * cos u)) has_field_derivative
      (- (2 * u * cos u - u\<^sup>2 * sin u))) (at u)" for u :: real
    by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)
  have eqf: "(\<lambda>y. Wc_d2 y c c) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (\<lambda>u. - (u\<^sup>2 * cos u)) (c \<bullet> (vec_nth y n - vec_nth y p)))"
    by (rule ext) (simp add: Wc_d2_def sum_negf)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_perp_slot_zero[OF dg])
qed

end
