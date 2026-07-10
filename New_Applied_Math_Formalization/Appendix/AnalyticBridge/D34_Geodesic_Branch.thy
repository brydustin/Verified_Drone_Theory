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


section \<open>The omega-side dictionary: \<open>gradU\<close> and \<open>Phi_par\<close> in \<open>c\<close>-space radial data\<close>

text \<open>\<^bold>\<open>Tier 2 of the normal-coordinate branch.\<close>  The chain rule through the
  factorization \<open>U_dip = gain_dip \<cdot> (Wc x \<circ> cvec_dip)\<close> (@{thm U_dip_Wc}) identifies the
  genuine omega-derivative of \<open>U_dip\<close> with \<open>c\<close>-space radial data:

    \<open>D\<^sub>\<omega>U[h] = Dgain[h] \<cdot> Wc + gain \<cdot> DWc[Dcvec h]\<close>.

  Combined with @{thm gradU_explicit} and Fréchet-derivative uniqueness this gives the
  dictionary \<open>gradU \<bullet> w\<close> = (that functional at \<open>w\<close>) --- no unfolding of the complex-form
  \<open>dU_cart\<close> is ever needed.  Instantiating \<open>w = e_par\<close> (which pushes forward to \<open>c\<close> by
  @{thm Dcvec_dip_e_par}) expresses the EXISTING first-order invariant \<open>Phi_par\<close> in
  radial \<open>c\<close>-jet data: \<open>Phi_par = Dgain[e_par] \<cdot> Wc + gain \<cdot> Wc_d1(c; c)\<close>.  This is the
  first entry of the dictionary that will let the radial cubic \<open>T3rad\<close> (whose perp-slot
  law is already proven unconditionally) play \<open>H_par\<close>'s intended role on the
  \<open>H11 = H22 = 0\<close> stratum.\<close>

subsection \<open>Fréchet derivative of \<open>Wc\<close> in the \<open>c\<close>-variable\<close>

lemma has_derivative_pair_phase_sum_c:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2" and g g' :: "real \<Rightarrow> real"
  assumes dg: "\<And>u. (g has_field_derivative g' u) (at u)"
  shows "((\<lambda>c'. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c' \<bullet> (vec_nth x n - vec_nth x p))) has_derivative
      (\<lambda>u. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x p))
             * (u \<bullet> (vec_nth x n - vec_nth x p)))) (at c)"
proof -
  have summand: "((\<lambda>c'. g (c' \<bullet> (vec_nth x n - vec_nth x p))) has_derivative
      (\<lambda>u. g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p))))
      (at c)" for n p :: 'n
  proof -
    have lin: "((\<lambda>c'::real^2. c' \<bullet> (vec_nth x n - vec_nth x p)) has_derivative
        (\<lambda>u. u \<bullet> (vec_nth x n - vec_nth x p))) (at c)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_inner_left has_derivative_ident])
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

lemma has_derivative_Wc_c:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  shows "((\<lambda>c'. Wc x c') has_derivative (\<lambda>u. Wc_d1 x c u)) (at c)"
proof -
  have dgcos: "(cos has_field_derivative (\<lambda>v. - sin v) u) (at u)" for u :: real
    using DERIV_cos[of u] by simp
  have F: "((\<lambda>c'. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cos (c' \<bullet> (vec_nth x n - vec_nth x p))) has_derivative
      (\<lambda>u. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          - sin (c \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p))))
      (at c)"
    using has_derivative_pair_phase_sum_c[OF dgcos, of x c] by simp
  have eqf: "(\<lambda>c'. Wc x c') = (\<lambda>c'. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cos (c' \<bullet> (vec_nth x n - vec_nth x p)))"
    by (rule ext) (simp add: Wc_def)
  have eqd: "(\<lambda>u. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      - sin (c \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p)))
      = (\<lambda>u. Wc_d1 x c u)"
    by (rule ext) (simp add: Wc_d1_def sum_negf sum_subtractf algebra_simps)
  show ?thesis unfolding eqf using F unfolding eqd .
qed

subsection \<open>The factored omega-derivative of \<open>U_dip\<close>\<close>

lemma has_derivative_U_dip_omega_factored:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>\<omega>'. U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>') has_derivative
      (\<lambda>h. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth h 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
         + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> h))) (at \<omega>)"
proof -
  have eqU: "(\<lambda>\<omega>'. U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>')
      = (\<lambda>\<omega>'. gain_dip \<omega>' * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>'))"
    by (rule ext) (rule U_cart_Wc)
  have compW: "((\<lambda>\<omega>'. Wc x (cvec_dip \<omega>0 \<omega>s \<omega>')) has_derivative
      (\<lambda>h. Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> h))) (at \<omega>)"
    by (rule has_derivative_compose[OF has_derivative_cvec_dip has_derivative_Wc_c])
  have M: "((\<lambda>\<omega>'. gain_dip \<omega>' * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>')) has_derivative
      (\<lambda>h. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth h 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
         + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> h))) (at \<omega>)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF gain_dip_has_derivative compW]])
       (rule ext, simp add: algebra_simps)
  show ?thesis unfolding eqU by (rule M)
qed

subsection \<open>The dictionary: \<open>gradU \<bullet> w\<close> in radial \<open>c\<close>-jet data\<close>

lemma gradU_dip_inner_omega:
  fixes x :: "(real^2)^'n::finite" and w \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> \<bullet> w
       = frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth w 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
       + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> w)"
proof -
  define myF where "myF = (\<lambda>h::real^2.
      frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth h 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
      + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> h))"
  have Umine: "((\<lambda>\<omega>'. U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>') has_derivative myF) (at \<omega>)"
    unfolding myF_def by (rule has_derivative_U_dip_omega_factored)
  have Utheir: "((\<lambda>\<omega>'. U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>') has_derivative
      dU_cart (cvec_dip \<omega>0 \<omega>s) (Dcvec_dip \<omega>0 \<omega>s \<omega>) gain_dip
        (\<lambda>v. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1)) x \<omega>) (at \<omega>)"
    by (rule has_derivative_U_cart[OF has_derivative_cvec_dip gain_dip_has_derivative])
  have uniq: "dU_cart (cvec_dip \<omega>0 \<omega>s) (Dcvec_dip \<omega>0 \<omega>s \<omega>) gain_dip
        (\<lambda>v. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1)) x \<omega> = myF"
    by (rule has_derivative_unique[OF Utheir Umine])
  have gradEq: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>
      = (\<Sum>i\<in>UNIV. myF (axis i 1) *\<^sub>R axis i 1)"
  proof -
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>
        = (\<Sum>i\<in>UNIV. dU_cart (cvec_dip \<omega>0 \<omega>s) (Dcvec_dip \<omega>0 \<omega>s \<omega>) gain_dip
            (\<lambda>v. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1)) x \<omega>
            (axis i 1) *\<^sub>R axis i 1)"
      by (rule gradU_explicit[OF has_derivative_cvec_dip gain_dip_has_derivative])
    thus ?thesis unfolding uniq by simp
  qed
  have blF: "bounded_linear myF"
    by (rule has_derivative_bounded_linear[OF Umine])
  have linF: "linear myF"
    by (rule bounded_linear.linear[OF blF])
  have decomp: "h = vec_nth h 1 *\<^sub>R axis 1 1 + vec_nth h 2 *\<^sub>R axis 2 1" for h :: "real^2"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 2
    show "vec_nth h i = vec_nth (vec_nth h 1 *\<^sub>R axis 1 1 + vec_nth h 2 *\<^sub>R axis 2 1) i"
      using exhaust_2[of i] by (auto simp: axis_def)
  qed
  have Fw: "myF w = vec_nth w 1 *\<^sub>R myF (axis 1 1) + vec_nth w 2 *\<^sub>R myF (axis 2 1)"
    using decomp[of w] linear_add[OF linF] linear_scale[OF linF] by metis
  have axw: "axis i (1::real) \<bullet> w = vec_nth w i" for i :: 2
    by (simp add: inner_axis inner_commute)
  have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> \<bullet> w
      = (\<Sum>i\<in>UNIV. myF (axis i 1) * (axis i 1 \<bullet> w))"
    unfolding gradEq by (simp add: inner_sum_left)
  also have "\<dots> = myF (axis 1 1) * vec_nth w 1 + myF (axis 2 1) * vec_nth w 2"
    by (simp add: sum_2 axw)
  also have "\<dots> = myF w"
    using Fw by simp
  finally show ?thesis unfolding myF_def by simp
qed

subsection \<open>\<open>Phi_par\<close> in radial data, and the level-1 critical identity\<close>

theorem Phi_par_radial_dictionary:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "Phi_par x \<omega> \<omega>0 \<omega>s
       = frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
           * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
       + gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>)"
  unfolding Phi_par_def
  using gradU_dip_inner_omega[where x = x and w = "e_par \<omega>0 \<omega>s \<omega>" and \<omega> = \<omega>
          and \<omega>0 = \<omega>0 and \<omega>s = \<omega>s]
        Dcvec_dip_e_par[OF detnz]
  by simp

corollary Phi_par_zero_radial:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and crit: "Phi_par x \<omega> \<omega>0 \<omega>s = 0"
  shows "gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>)
       = - (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
             * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>))"
  using Phi_par_radial_dictionary[OF detnz, where x = x] crit by linarith


section \<open>Tier 2b: the second-order dictionary and the corrected H12 invariant\<close>

text \<open>\<^bold>\<open>The point of this tier.\<close>  The heap already knows that the omega-derivative of
  the dipole gradient field IS the Hessian (@{thm gradU_dip_has_derivative}).  Running
  the same uniqueness play as Tier 2a one order up yields a hypothesis-free
  \<^emph>\<open>second-order dictionary\<close>: every Hessian contraction \<open>(HessU *v w) \<bullet> e\<close> equals an
  explicit expression in the \<open>c\<close>-jet of \<open>Wc\<close> plus a \<open>D2cvec_dip\<close> correction.

  Contracting with \<open>e = w = e_par\<close> then EXHIBITS, as a machine-checked identity, the
  exact residual term that made the old \<open>H_par\<close> approach unsound: \<open>H_par\<close> equals a
  purely RADIAL \<open>c\<close>-jet combination \<^bold>\<open>plus\<close> \<open>gain \<cdot> Wc_d1(c; D2cvec(e_par, e_par))\<close>.
  Subtracting that explicit correction defines \<open>Hrad2\<close>, the corrected second-order
  invariant, whose x-slot \<open>perp2 c\<close> derivative vanishes by the pair-phase master law
  --- the sound replacement for the refuted \<open>h_par_vslot_zero\<close>.\<close>

subsection \<open>The coefficient \<open>c\<close>-master and the mixed bilinear \<open>Wc_dd\<close>\<close>

lemma has_derivative_pair_phase_sum_c_coeff:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
    and k :: "'n \<Rightarrow> 'n \<Rightarrow> real" and g g' :: "real \<Rightarrow> real"
  assumes dg: "\<And>u. (g has_field_derivative g' u) (at u)"
  shows "((\<lambda>c'. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c' \<bullet> (vec_nth x n - vec_nth x p)) * k n p)
      has_derivative
      (\<lambda>u. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p)) * k n p))
      (at c)"
proof -
  have ksummand: "((\<lambda>c'. g (c' \<bullet> (vec_nth x n - vec_nth x p)) * k n p) has_derivative
      (\<lambda>u. g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p)) * k n p))
      (at c)" for n p :: 'n
  proof -
    have lin: "((\<lambda>c'::real^2. c' \<bullet> (vec_nth x n - vec_nth x p)) has_derivative
        (\<lambda>u. u \<bullet> (vec_nth x n - vec_nth x p))) (at c)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_inner_left has_derivative_ident])
    have outer: "(g has_derivative (\<lambda>u. g' (c \<bullet> (vec_nth x n - vec_nth x p)) * u))
        (at (c \<bullet> (vec_nth x n - vec_nth x p)))"
      using dg[of "c \<bullet> (vec_nth x n - vec_nth x p)"]
      unfolding has_field_derivative_def by simp
    have base: "((\<lambda>c'. g (c' \<bullet> (vec_nth x n - vec_nth x p))) has_derivative
        (\<lambda>u. g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p)))) (at c)"
      using has_derivative_compose[OF lin outer] by simp
    show ?thesis
      using bounded_linear.has_derivative[OF bounded_linear_mult_left base] by simp
  qed
  show ?thesis
    by (intro has_derivative_sum) (rule ksummand)
qed

definition Wc_dd :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "Wc_dd x c d u = - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (d \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p))
        * cos (c \<bullet> (vec_nth x n - vec_nth x p)))"

lemma Wc_d2_eq_dd: "Wc_d2 x c d = Wc_dd x c d d"
  by (simp add: Wc_d2_def Wc_dd_def power2_eq_square)

lemma has_derivative_Wc_d1_c:
  fixes x :: "(real^2)^'n::finite" and c d :: "real^2"
  shows "((\<lambda>c'. Wc_d1 x c' d) has_derivative (\<lambda>u. Wc_dd x c d u)) (at c)"
proof -
  have dgsin: "(sin has_field_derivative (\<lambda>v. cos v) u) (at u)" for u :: real
    using DERIV_sin[of u] by simp
  have F: "((\<lambda>c'. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      sin (c' \<bullet> (vec_nth x n - vec_nth x p)) * (- (d \<bullet> (vec_nth x n - vec_nth x p))))
      has_derivative
      (\<lambda>u. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          cos (c \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p))
            * (- (d \<bullet> (vec_nth x n - vec_nth x p))))) (at c)"
    by (rule has_derivative_pair_phase_sum_c_coeff[OF dgsin])
  have eqf: "(\<lambda>c'. Wc_d1 x c' d) = (\<lambda>c'. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      sin (c' \<bullet> (vec_nth x n - vec_nth x p)) * (- (d \<bullet> (vec_nth x n - vec_nth x p))))"
    by (rule ext) (simp add: Wc_d1_def sum_negf sum_subtractf algebra_simps)
  have eqd: "(\<lambda>u. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      cos (c \<bullet> (vec_nth x n - vec_nth x p)) * (u \<bullet> (vec_nth x n - vec_nth x p))
        * (- (d \<bullet> (vec_nth x n - vec_nth x p))))
      = (\<lambda>u. Wc_dd x c d u)"
    by (rule ext) (simp add: Wc_dd_def sum_subtractf sum.distrib sum_distrib_left
          algebra_simps flip: sum_negf)
  show ?thesis unfolding eqf using F unfolding eqd .
qed

subsection \<open>Derivative of the \<open>Dcvec\<close>-composed radial first derivative\<close>

lemma has_derivative_Wc_d1_comp:
  fixes x :: "(real^2)^'n::finite" and e \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>\<omega>'. Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>') (Dcvec_dip \<omega>0 \<omega>s \<omega>' e)) has_derivative
      (\<lambda>v. Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (D2cvec_dip \<omega>0 \<omega>s \<omega> e v)
         + Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e) (Dcvec_dip \<omega>0 \<omega>s \<omega> v)))
      (at \<omega>)"
proof -
  have per: "((\<lambda>\<omega>'. (Dcvec_dip \<omega>0 \<omega>s \<omega>' e \<bullet> (vec_nth x n - vec_nth x p))
        * sin (cvec_dip \<omega>0 \<omega>s \<omega>' \<bullet> (vec_nth x n - vec_nth x p)))
      has_derivative
      (\<lambda>v. (Dcvec_dip \<omega>0 \<omega>s \<omega> e \<bullet> (vec_nth x n - vec_nth x p))
            * (cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p))
                * (Dcvec_dip \<omega>0 \<omega>s \<omega> v \<bullet> (vec_nth x n - vec_nth x p)))
         + (D2cvec_dip \<omega>0 \<omega>s \<omega> e v \<bullet> (vec_nth x n - vec_nth x p))
            * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p))))
      (at \<omega>)" for n p :: 'n
  proof -
    have hdA: "((\<lambda>\<omega>'. Dcvec_dip \<omega>0 \<omega>s \<omega>' e \<bullet> (vec_nth x n - vec_nth x p)) has_derivative
        (\<lambda>v. D2cvec_dip \<omega>0 \<omega>s \<omega> e v \<bullet> (vec_nth x n - vec_nth x p))) (at \<omega>)"
      using bounded_linear.has_derivative[OF bounded_linear_inner_left
              has_derivative_Dcvec_dip] by simp
    have lin': "((\<lambda>c'::real^2. c' \<bullet> (vec_nth x n - vec_nth x p)) has_derivative
        (\<lambda>u. u \<bullet> (vec_nth x n - vec_nth x p))) (at (cvec_dip \<omega>0 \<omega>s \<omega>))"
      by (rule bounded_linear.has_derivative[OF bounded_linear_inner_left has_derivative_ident])
    have outer': "(sin has_derivative
        (\<lambda>u. cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p)) * u))
        (at (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p)))"
      using DERIV_sin[of "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p)"]
      unfolding has_field_derivative_def by simp
    have sinner: "((\<lambda>c'. sin (c' \<bullet> (vec_nth x n - vec_nth x p))) has_derivative
        (\<lambda>u. cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p))
              * (u \<bullet> (vec_nth x n - vec_nth x p)))) (at (cvec_dip \<omega>0 \<omega>s \<omega>))"
      using has_derivative_compose[OF lin' outer'] by simp
    have hdB: "((\<lambda>\<omega>'. sin (cvec_dip \<omega>0 \<omega>s \<omega>' \<bullet> (vec_nth x n - vec_nth x p))) has_derivative
        (\<lambda>v. cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p))
              * (Dcvec_dip \<omega>0 \<omega>s \<omega> v \<bullet> (vec_nth x n - vec_nth x p)))) (at \<omega>)"
      by (rule has_derivative_compose[OF has_derivative_cvec_dip sinner])
    show ?thesis
      by (rule has_derivative_mult[OF hdA hdB])
  qed
  have F: "((\<lambda>\<omega>'. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (Dcvec_dip \<omega>0 \<omega>s \<omega>' e \<bullet> (vec_nth x n - vec_nth x p))
        * sin (cvec_dip \<omega>0 \<omega>s \<omega>' \<bullet> (vec_nth x n - vec_nth x p))))
      has_derivative
      (\<lambda>v. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          (Dcvec_dip \<omega>0 \<omega>s \<omega> e \<bullet> (vec_nth x n - vec_nth x p))
            * (cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p))
                * (Dcvec_dip \<omega>0 \<omega>s \<omega> v \<bullet> (vec_nth x n - vec_nth x p)))
         + (D2cvec_dip \<omega>0 \<omega>s \<omega> e v \<bullet> (vec_nth x n - vec_nth x p))
            * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p)))))
      (at \<omega>)"
    by (intro has_derivative_minus has_derivative_sum) (rule per)
  have eqf: "(\<lambda>\<omega>'. Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>') (Dcvec_dip \<omega>0 \<omega>s \<omega>' e))
      = (\<lambda>\<omega>'. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          (Dcvec_dip \<omega>0 \<omega>s \<omega>' e \<bullet> (vec_nth x n - vec_nth x p))
            * sin (cvec_dip \<omega>0 \<omega>s \<omega>' \<bullet> (vec_nth x n - vec_nth x p))))"
    by (rule ext) (simp add: Wc_d1_def)
  have eqd: "(\<lambda>v. - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (Dcvec_dip \<omega>0 \<omega>s \<omega> e \<bullet> (vec_nth x n - vec_nth x p))
        * (cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p))
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> v \<bullet> (vec_nth x n - vec_nth x p)))
     + (D2cvec_dip \<omega>0 \<omega>s \<omega> e v \<bullet> (vec_nth x n - vec_nth x p))
        * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x n - vec_nth x p))))
      = (\<lambda>v. Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (D2cvec_dip \<omega>0 \<omega>s \<omega> e v)
           + Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e) (Dcvec_dip \<omega>0 \<omega>s \<omega> v))"
    by (rule ext) (simp add: Wc_d1_def Wc_dd_def sum.distrib sum_subtractf
          sum_distrib_left algebra_simps flip: sum_negf)
  show ?thesis unfolding eqf using F unfolding eqd .
qed

subsection \<open>Two derivatives of the same inner field: Hessian side and factored side\<close>

lemma has_derivative_gradU_inner_e_hess:
  fixes x :: "(real^2)^'n::finite" and e \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>\<omega>'. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>' \<bullet> e) has_derivative
      (\<lambda>v. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v) \<bullet> e)) (at \<omega>)"
  by (rule bounded_linear.has_derivative[OF bounded_linear_inner_left
        gradU_dip_has_derivative])

lemma has_derivative_gradU_inner_e_factored:
  fixes x :: "(real^2)^'n::finite" and e \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>\<omega>'. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>' \<bullet> e) has_derivative
      (\<lambda>v. ((deriv gdip (vec_nth \<omega> 1) * vec_nth e 1)
              * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> v)
            + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1 * vec_nth e 1
              * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>))
         + (gain_dip \<omega> * (Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (D2cvec_dip \<omega>0 \<omega>s \<omega> e v)
              + Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e) (Dcvec_dip \<omega>0 \<omega>s \<omega> v))
            + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1)
              * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e)))) (at \<omega>)"
proof -
  have eqphi: "(\<lambda>\<omega>'. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>' \<bullet> e)
      = (\<lambda>\<omega>'. deriv gdip (vec_nth \<omega>' 1) * vec_nth e 1 * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>')
            + gain_dip \<omega>' * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>') (Dcvec_dip \<omega>0 \<omega>s \<omega>' e))"
    by (rule ext) (simp add: gradU_dip_inner_omega frechet_gdip_eq)
  have hv: "((\<lambda>\<eta>::real^2. vec_nth \<eta> 1) has_derivative (\<lambda>v. vec_nth v 1)) (at \<omega>)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_ident])
  have hdA1: "((\<lambda>\<omega>'. deriv gdip (vec_nth \<omega>' 1)) has_derivative
      (\<lambda>v. deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1)) (at \<omega>)"
    using has_derivative_compose[OF hv
        DERIV_deriv_gdip[unfolded has_field_derivative_def, of "vec_nth \<omega> 1"]]
    by simp
  have hdA: "((\<lambda>\<omega>'. deriv gdip (vec_nth \<omega>' 1) * vec_nth e 1) has_derivative
      (\<lambda>v. deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1 * vec_nth e 1)) (at \<omega>)"
    using bounded_linear.has_derivative[OF bounded_linear_mult_left hdA1] by simp
  have hdB: "((\<lambda>\<omega>'. Wc x (cvec_dip \<omega>0 \<omega>s \<omega>')) has_derivative
      (\<lambda>v. Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> v))) (at \<omega>)"
    by (rule has_derivative_compose[OF has_derivative_cvec_dip has_derivative_Wc_c])
  have term1: "((\<lambda>\<omega>'. (deriv gdip (vec_nth \<omega>' 1) * vec_nth e 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>'))
      has_derivative
      (\<lambda>v. (deriv gdip (vec_nth \<omega> 1) * vec_nth e 1)
              * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> v)
         + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1 * vec_nth e 1
              * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at \<omega>)"
    using has_derivative_mult[OF hdA hdB] by (simp add: algebra_simps)
  have term2: "((\<lambda>\<omega>'. gain_dip \<omega>'
        * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>') (Dcvec_dip \<omega>0 \<omega>s \<omega>' e))
      has_derivative
      (\<lambda>v. gain_dip \<omega> * (Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (D2cvec_dip \<omega>0 \<omega>s \<omega> e v)
              + Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e) (Dcvec_dip \<omega>0 \<omega>s \<omega> v))
         + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1)
              * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e))) (at \<omega>)"
    by (rule has_derivative_mult[OF gain_dip_has_derivative has_derivative_Wc_d1_comp])
  have both: "((\<lambda>\<omega>'. (deriv gdip (vec_nth \<omega>' 1) * vec_nth e 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>')
        + gain_dip \<omega>' * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>') (Dcvec_dip \<omega>0 \<omega>s \<omega>' e))
      has_derivative
      (\<lambda>v. ((deriv gdip (vec_nth \<omega> 1) * vec_nth e 1)
              * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> v)
            + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1 * vec_nth e 1
              * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>))
         + (gain_dip \<omega> * (Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (D2cvec_dip \<omega>0 \<omega>s \<omega> e v)
              + Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e) (Dcvec_dip \<omega>0 \<omega>s \<omega> v))
            + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1)
              * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e)))) (at \<omega>)"
    by (rule has_derivative_add[OF term1 term2])
  have eqphi': "(\<lambda>\<omega>'. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>' \<bullet> e)
      = (\<lambda>\<omega>'. (deriv gdip (vec_nth \<omega>' 1) * vec_nth e 1) * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>')
            + gain_dip \<omega>' * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>') (Dcvec_dip \<omega>0 \<omega>s \<omega>' e))"
    unfolding eqphi by (rule ext) simp
  show ?thesis unfolding eqphi' by (rule both)
qed

subsection \<open>The second-order dictionary (hypothesis-free)\<close>

theorem HessU_quad_dictionary:
  fixes x :: "(real^2)^'n::finite" and e w \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "(HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v w) \<bullet> e
     = ((deriv gdip (vec_nth \<omega> 1) * vec_nth e 1)
          * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> w)
        + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth e 1
          * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>))
     + (gain_dip \<omega> * (Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (D2cvec_dip \<omega>0 \<omega>s \<omega> e w)
          + Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e) (Dcvec_dip \<omega>0 \<omega>s \<omega> w))
        + deriv gdip (vec_nth \<omega> 1) * vec_nth w 1
          * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e))"
proof -
  have uniq: "(\<lambda>v. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v) \<bullet> e)
      = (\<lambda>v. ((deriv gdip (vec_nth \<omega> 1) * vec_nth e 1)
              * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> v)
            + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1 * vec_nth e 1
              * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>))
         + (gain_dip \<omega> * (Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (D2cvec_dip \<omega>0 \<omega>s \<omega> e v)
              + Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e) (Dcvec_dip \<omega>0 \<omega>s \<omega> v))
            + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1)
              * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e)))"
    by (rule has_derivative_unique[OF has_derivative_gradU_inner_e_hess
          has_derivative_gradU_inner_e_factored])
  have "(HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v w) \<bullet> e
      = ((deriv gdip (vec_nth \<omega> 1) * vec_nth e 1)
            * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> w)
          + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth w 1 * vec_nth e 1
            * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>))
       + (gain_dip \<omega> * (Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (D2cvec_dip \<omega>0 \<omega>s \<omega> e w)
            + Wc_dd x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e) (Dcvec_dip \<omega>0 \<omega>s \<omega> w))
          + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth w 1)
            * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (Dcvec_dip \<omega>0 \<omega>s \<omega> e))"
    by (rule fun_cong[OF uniq])
  thus ?thesis by (simp add: frechet_gdip_eq)
qed

subsection \<open>\<open>H_par\<close> as a quadratic form, and its dictionary with the explicit residual\<close>

lemma H_par_eq_quadform:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "H_par x \<omega> \<omega>0 \<omega>s
      = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v e_par \<omega>0 \<omega>s \<omega>) \<bullet> e_par \<omega>0 \<omega>s \<omega>"
  unfolding H_par_def
  by (simp add: matrix_vector_mult_def inner_vec_def sum_2 algebra_simps)

theorem H_par_radial_dictionary:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "H_par x \<omega> \<omega>0 \<omega>s
     = ((deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
          * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>)
        + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>))
     + (gain_dip \<omega> * (Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>)
            (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) (e_par \<omega>0 \<omega>s \<omega>))
          + Wc_d2 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>))
        + deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>))"
  unfolding H_par_eq_quadform HessU_quad_dictionary
  by (simp add: Dcvec_dip_e_par[OF detnz] Wc_d2_eq_dd[symmetric])

subsection \<open>The corrected second-order invariant \<open>Hrad2\<close> and its perp-slot law\<close>

definition Hrad2 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "Hrad2 x \<omega> \<omega>0 \<omega>s = H_par x \<omega> \<omega>0 \<omega>s
     - gain_dip \<omega> * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>)
         (D2cvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) (e_par \<omega>0 \<omega>s \<omega>))"

lemma Hrad2_radial_form:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "Hrad2 x \<omega> \<omega>0 \<omega>s
     = deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
         * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>)
     + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
         * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * Wc x (cvec_dip \<omega>0 \<omega>s \<omega>)
     + gain_dip \<omega> * Wc_d2 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>)
     + deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
         * Wc_d1 x (cvec_dip \<omega>0 \<omega>s \<omega>) (cvec_dip \<omega>0 \<omega>s \<omega>)"
  unfolding Hrad2_def H_par_radial_dictionary[OF detnz]
  by (simp add: algebra_simps)

theorem Hrad2_slot_perp_zero:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and m :: 'n
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x)
           (slot m (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
proof -
  define A where "A = deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define B where "B = deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
      * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define G where "G = (\<lambda>u. A * (- (u * sin u)) + B * cos u
      + gain_dip \<omega> * (- (u\<^sup>2 * cos u)) + A * (- (u * sin u)))"
  have eqf: "(\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      G (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth y n - vec_nth y p)))"
    unfolding G_def
    by (rule ext)
       (simp add: Hrad2_radial_form[OF detnz] A_def B_def Wc_def Wc_d1_def Wc_d2_def
          sum.distrib sum_negf sum_subtractf sum_distrib_left power2_eq_square
          algebra_simps)
  have dG: "(G has_field_derivative
      (A * (- (sin u + u * cos u)) + B * (- sin u)
       + gain_dip \<omega> * (- (2 * u * cos u - u\<^sup>2 * sin u))
       + A * (- (sin u + u * cos u)))) (at u)" for u :: real
    unfolding G_def
    by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_perp_slot_zero[OF dG])
qed

end
