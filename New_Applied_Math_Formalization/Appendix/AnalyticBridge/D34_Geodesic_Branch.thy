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


section \<open>Tier 3: the H12=0 rank-3 criterion rebuilt on \<open>Hrad2\<close> --- no carried hypothesis\<close>

text \<open>\<^bold>\<open>This section supersedes the bridge's \<open>Jac3_H12zero\<close> block.\<close>  That block's
  rank-3 criterion carries \<open>h_par_vslot_zero\<close> as an explicit UNVERIFIED hypothesis ---
  later machine-refuted (see the diary).  Here the same block-triangular determinant is
  rebuilt with the corrected invariant \<open>Hrad2\<close> in \<open>H_par\<close>'s row.  Both perpendicular-slot
  entries now vanish by PROVEN theorems (@{thm Phi_par_perp_slot_zero} for the first row,
  \<open>Hrad2_slot_perp_zero\<close> for the third), so the determinant identity and the rank-3
  criterion hold under \<open>det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0\<close> alone --- the H12=0
  branch obligation no longer rests on any unverified assumption.\<close>

subsection \<open>\<open>Lambda_rad_ij\<close>: the u-slot determinant of \<open>(Phi_par, Hrad2)\<close>\<close>

definition Lambda_rad_ij :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
  "Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j =
     frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>))
       * frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>))
   - frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>))
       * frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>))"

subsection \<open>The block-triangular 3x3 Jacobian on \<open>(Phi_par, gradU\<^sub>2, Hrad2)\<close>\<close>

definition Jac3_H12rad :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
  "Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k =
     det3
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))"

text \<open>\<^bold>\<open>The identity, with NO carried hypothesis.\<close>  Both perp-slot entries in the
  \<open>Phi_par\<close> and \<open>Hrad2\<close> rows vanish by proven theorems, so the determinant collapses
  block-triangularly to \<open>-s\<^sub>k \<cdot> \<Lambda>\<close> where \<open>s\<^sub>k\<close> is the \<open>gradU\<^sub>2\<close> perp-slot entry.\<close>

theorem Jac3_H12rad_identity:
  fixes i j k :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k
       = - (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
              (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
            * Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j)"
proof -
  have perpi: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    by (rule perp2_orth)
  have zk: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
      (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
    by (rule Phi_par_perp_slot_zero[OF detnz perpi])
  have zh: "frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x)
      (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
    by (rule Hrad2_slot_perp_zero[OF detnz])
  show ?thesis
    unfolding Jac3_H12rad_def Lambda_rad_ij_def det3_def zk zh
    by (simp add: algebra_simps)
qed

corollary Jac3_H12rad_nonzero_criterion:
  fixes i j k :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and s_k_nz:
      "frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
           (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) \<noteq> 0"
    and lambda_nz: "Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j \<noteq> 0"
  shows "Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k \<noteq> 0"
  unfolding Jac3_H12rad_identity[OF detnz]
  using s_k_nz lambda_nz by simp


section \<open>Tier 4a: explicit u-slot VALUES for the radial jet (the genericity substrate)\<close>

text \<open>\<^bold>\<open>Why this tier.\<close>  The rank-3 criterion \<open>Jac3_H12rad_nonzero_criterion\<close> has two
  honest side conditions: \<open>s\<^sub>k \<noteq> 0\<close> and \<open>Lambda_rad_ij \<noteq> 0\<close>.  Any genericity argument
  for them needs the slot derivatives of \<open>Hrad2\<close> as EXPLICIT functions of \<open>x\<close> (so the
  real-analytic nowhere-dense machinery can bite).  This tier provides the master
  slot-VALUE law for pair-phase sums and its instances for the whole radial jet.

  Structural bonus: every profile derivative in the radial jet is an ODD function, so
  the two sums in the master formula merge and every slot value collapses to the single
  \<open>m\<close>-row sum \<open>2 (c \<bullet> u) \<Sum>\<^sub>p g' (c \<bullet> (x\<^sub>m - x\<^sub>p))\<close>.\<close>

subsection \<open>The master slot-value law\<close>

theorem pair_phase_sum_slot_value:
  fixes c u :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
    and g g' :: "real \<Rightarrow> real"
  assumes dg: "\<And>v. (g has_field_derivative g' v) (at v)"
  shows "frechet_derivative (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c \<bullet> (vec_nth y n - vec_nth y p)))
           (at x) (slot m u)
       = (c \<bullet> u) * ((\<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x m - vec_nth x p)))
                   - (\<Sum>n\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x m))))"
proof -
  have fd: "frechet_derivative (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c \<bullet> (vec_nth y n - vec_nth y p))) (at x)
      = (\<lambda>h. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x p))
               * (c \<bullet> (vec_nth h n - vec_nth h p)))"
    by (rule frechet_derivative_at[OF has_derivative_pair_phase_sum_x[OF dg], symmetric])
  have sterm: "g' (c \<bullet> (vec_nth x n - vec_nth x p))
        * (c \<bullet> (vec_nth (slot m u) n - vec_nth (slot m u) p))
      = (if n = m then g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> u) else 0)
      - (if p = m then g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> u) else 0)"
    for n p :: 'n
    by (auto simp: slot_nth inner_diff_right algebra_simps)
  have step1: "(\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (if n = m then g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> u) else 0))
      = (\<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x m - vec_nth x p)) * (c \<bullet> u))"
  proof -
    have pull: "(\<Sum>p\<in>UNIV. (if n = m then g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> u) else 0))
        = (if n = m then (\<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> u)) else 0)"
      for n :: 'n
      by (cases "n = m") auto
    show ?thesis by (simp add: pull sum.delta)
  qed
  have step2: "(\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (if p = m then g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> u) else 0))
      = (\<Sum>n\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x m)) * (c \<bullet> u))"
    by (simp add: sum.delta)
  have "frechet_derivative (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c \<bullet> (vec_nth y n - vec_nth y p)))
          (at x) (slot m u)
      = (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          (if n = m then g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> u) else 0))
      - (\<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
          (if p = m then g' (c \<bullet> (vec_nth x n - vec_nth x p)) * (c \<bullet> u) else 0))"
    unfolding fd by (simp add: sterm sum_subtractf)
  also have "\<dots> = (\<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x m - vec_nth x p)) * (c \<bullet> u))
      - (\<Sum>n\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x m)) * (c \<bullet> u))"
    unfolding step1 step2 ..
  also have "\<dots> = (c \<bullet> u) * ((\<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x m - vec_nth x p)))
                            - (\<Sum>n\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x m))))"
    by (simp add: algebra_simps flip: sum_distrib_left)
  finally show ?thesis .
qed

corollary pair_phase_sum_slot_value_odd:
  fixes c u :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
    and g g' :: "real \<Rightarrow> real"
  assumes dg: "\<And>v. (g has_field_derivative g' v) (at v)"
    and oddg: "\<And>v. g' (- v) = - g' v"
  shows "frechet_derivative (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. g (c \<bullet> (vec_nth y n - vec_nth y p)))
           (at x) (slot m u)
       = 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV. g' (c \<bullet> (vec_nth x m - vec_nth x p)))"
proof -
  have flipterm: "g' (c \<bullet> (vec_nth x n - vec_nth x m)) = - g' (c \<bullet> (vec_nth x m - vec_nth x n))"
    for n :: 'n
  proof -
    have "c \<bullet> (vec_nth x n - vec_nth x m) = - (c \<bullet> (vec_nth x m - vec_nth x n))"
      by (simp add: inner_diff_right)
    thus ?thesis by (simp add: oddg)
  qed
  have flipsum: "(\<Sum>n\<in>UNIV. g' (c \<bullet> (vec_nth x n - vec_nth x m)))
      = - (\<Sum>n\<in>UNIV. g' (c \<bullet> (vec_nth x m - vec_nth x n)))"
    by (simp add: flipterm sum_negf)
  show ?thesis
    unfolding pair_phase_sum_slot_value[OF dg] flipsum by simp
qed

subsection \<open>Slot values for the radial jet\<close>

theorem Wc_slot_value:
  fixes c u :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  shows "frechet_derivative (\<lambda>y. Wc y c) (at x) (slot m u)
       = 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV. - sin (c \<bullet> (vec_nth x m - vec_nth x p)))"
proof -
  have dg: "(cos has_field_derivative (\<lambda>v. - sin v) v) (at v)" for v :: real
    using DERIV_cos[of v] by simp
  have oddg: "(\<lambda>v. - sin v) (- v) = - (\<lambda>v. - sin v) v" for v :: real
    by simp
  have eqf: "(\<lambda>y. Wc y c) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV. cos (c \<bullet> (vec_nth y n - vec_nth y p)))"
    by (rule ext) (simp add: Wc_def)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_slot_value_odd[OF dg oddg])
qed

theorem T1rad_slot_value:
  fixes c u :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  shows "frechet_derivative (\<lambda>y. Wc_d1 y c c) (at x) (slot m u)
       = 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV. - (sin (c \<bullet> (vec_nth x m - vec_nth x p))
           + (c \<bullet> (vec_nth x m - vec_nth x p)) * cos (c \<bullet> (vec_nth x m - vec_nth x p))))"
proof -
  have dg: "((\<lambda>v. - (v * sin v)) has_field_derivative
      (\<lambda>v. - (sin v + v * cos v)) v) (at v)" for v :: real
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have oddg: "(\<lambda>v. - (sin v + v * cos v)) (- v) = - (\<lambda>v. - (sin v + v * cos v)) v" for v :: real
    by simp
  have eqf: "(\<lambda>y. Wc_d1 y c c) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (\<lambda>w. - (w * sin w)) (c \<bullet> (vec_nth y n - vec_nth y p)))"
    by (rule ext) (simp add: Wc_d1_def sum_negf)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_slot_value_odd[OF dg oddg])
qed

theorem T2rad_slot_value:
  fixes c u :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  shows "frechet_derivative (\<lambda>y. Wc_d2 y c c) (at x) (slot m u)
       = 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV. - (2 * (c \<bullet> (vec_nth x m - vec_nth x p))
             * cos (c \<bullet> (vec_nth x m - vec_nth x p))
           - (c \<bullet> (vec_nth x m - vec_nth x p))\<^sup>2
             * sin (c \<bullet> (vec_nth x m - vec_nth x p))))"
proof -
  have dg: "((\<lambda>v. - (v\<^sup>2 * cos v)) has_field_derivative
      (\<lambda>v. - (2 * v * cos v - v\<^sup>2 * sin v)) v) (at v)" for v :: real
    by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)
  have oddg: "(\<lambda>v. - (2 * v * cos v - v\<^sup>2 * sin v)) (- v)
      = - (\<lambda>v. - (2 * v * cos v - v\<^sup>2 * sin v)) v" for v :: real
    by (simp add: power2_eq_square algebra_simps)
  have eqf: "(\<lambda>y. Wc_d2 y c c) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (\<lambda>w. - (w\<^sup>2 * cos w)) (c \<bullet> (vec_nth y n - vec_nth y p)))"
    by (rule ext) (simp add: Wc_d2_def sum_negf)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_slot_value_odd[OF dg oddg])
qed

theorem T3rad_slot_value:
  fixes c u :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  shows "frechet_derivative (\<lambda>y. T3rad y c) (at x) (slot m u)
       = 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV.
           3 * (c \<bullet> (vec_nth x m - vec_nth x p))\<^sup>2
             * sin (c \<bullet> (vec_nth x m - vec_nth x p))
           + (c \<bullet> (vec_nth x m - vec_nth x p)) ^ 3
             * cos (c \<bullet> (vec_nth x m - vec_nth x p)))"
proof -
  have dg: "((\<lambda>v. v ^ 3 * sin v) has_field_derivative
      (\<lambda>v. 3 * v\<^sup>2 * sin v + v ^ 3 * cos v) v) (at v)" for v :: real
    by (auto intro!: derivative_eq_intros simp: power2_eq_square power3_eq_cube algebra_simps)
  have oddg: "(\<lambda>v. 3 * v\<^sup>2 * sin v + v ^ 3 * cos v) (- v)
      = - (\<lambda>v. 3 * v\<^sup>2 * sin v + v ^ 3 * cos v) v" for v :: real
    by (simp add: power2_eq_square power3_eq_cube algebra_simps)
  have eqf: "(\<lambda>y. T3rad y c) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      (\<lambda>w. w ^ 3 * sin w) (c \<bullet> (vec_nth y n - vec_nth y p)))"
    by (rule ext) (rule T3rad_pair_phase_form)
  show ?thesis
    unfolding eqf by (rule pair_phase_sum_slot_value_odd[OF dg oddg])
qed

subsection \<open>The \<open>Hrad2\<close> slot value: \<open>Lambda_rad_ij\<close> becomes explicitly computable\<close>

theorem Hrad2_slot_value:
  fixes u \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot m u)
       = 2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> u) * (\<Sum>p\<in>UNIV.
           deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * (- (sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                 + (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                   * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))))
           + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
               * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * (- sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p)))
           + gain_dip \<omega>
             * (- (2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                   * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                 - (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))\<^sup>2
                   * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))))
           + deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * (- (sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                 + (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                   * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p)))))"
proof -
  define A where "A = deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define B where "B = deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
      * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define G where "G = (\<lambda>w. A * (- (w * sin w)) + B * cos w
      + gain_dip \<omega> * (- (w\<^sup>2 * cos w)) + A * (- (w * sin w)))"
  define G' where "G' = (\<lambda>w. A * (- (sin w + w * cos w)) + B * (- sin w)
      + gain_dip \<omega> * (- (2 * w * cos w - w\<^sup>2 * sin w))
      + A * (- (sin w + w * cos w)))"
  have eqf: "(\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      G (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth y n - vec_nth y p)))"
    unfolding G_def
    by (rule ext)
       (simp add: Hrad2_radial_form[OF detnz] A_def B_def Wc_def Wc_d1_def Wc_d2_def
          sum.distrib sum_negf sum_subtractf sum_distrib_left power2_eq_square
          algebra_simps)
  have dG: "(G has_field_derivative G' w) (at w)" for w :: real
    unfolding G_def G'_def
    by (auto intro!: derivative_eq_intros simp: power2_eq_square algebra_simps)
  have oddG: "G' (- w) = - G' w" for w :: real
    unfolding G'_def by (simp add: power2_eq_square algebra_simps)
  have "frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot m u)
      = 2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> u) * (\<Sum>p\<in>UNIV.
          G' (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p)))"
    unfolding eqf by (rule pair_phase_sum_slot_value_odd[OF dG oddG])
  thus ?thesis
    unfolding G'_def A_def B_def by simp
qed


section \<open>Tier 4b: x-analyticity of the slot values (so genericity can run)\<close>

text \<open>\<^bold>\<open>Purpose.\<close>  The nowhere-dense-zeros workhorse needs the slot-derivative functions
  to be real-analytic in the configuration \<open>x\<close>.  Every slot value proven in Tier 4a is a
  finite trig sum in the pair phases \<open>c \<bullet> (x\<^sub>m - x\<^sub>p)\<close> (bounded-linear in \<open>x\<close>), so
  analyticity is pure combinator assembly on the existing \<open>Real_Analytic\<close> stack.  The
  final lemma reduces \<open>Lambda_rad_ij\<close>-analyticity to the two \<open>Phi_par\<close>-factor
  analyticity facts (the moment/\<open>dEjm\<close> composite), making the one remaining gap precise.\<close>

lemma real_analytic_on_xslot_phase:
  fixes c :: "real^2" and m p :: "'n::finite"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n. c \<bullet> (vec_nth x m - vec_nth x p)) UNIV"
  by (rule real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_pair_inner])

theorem real_analytic_on_Wc_slot_value:
  fixes c u :: "real^2" and m :: "'n::finite"
  shows "real_analytic_on
      (\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. Wc y c) (at x) (slot m u)) UNIV"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. Wc y c) (at x) (slot m u))
      = (\<lambda>x. 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV. - sin (c \<bullet> (vec_nth x m - vec_nth x p))))"
    by (rule ext) (rule Wc_slot_value)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
          real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_uminus
          real_analytic_on_sin_comp real_analytic_on_xslot_phase)
qed

theorem real_analytic_on_T1rad_slot_value:
  fixes c u :: "real^2" and m :: "'n::finite"
  shows "real_analytic_on
      (\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. Wc_d1 y c c) (at x) (slot m u)) UNIV"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. Wc_d1 y c c) (at x) (slot m u))
      = (\<lambda>x. 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV. - (sin (c \<bullet> (vec_nth x m - vec_nth x p))
          + (c \<bullet> (vec_nth x m - vec_nth x p)) * cos (c \<bullet> (vec_nth x m - vec_nth x p)))))"
    by (rule ext) (rule T1rad_slot_value)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
          real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_uminus
          real_analytic_on_add real_analytic_on_sin_comp real_analytic_on_cos_comp
          real_analytic_on_xslot_phase)
qed

theorem real_analytic_on_T2rad_slot_value:
  fixes c u :: "real^2" and m :: "'n::finite"
  shows "real_analytic_on
      (\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. Wc_d2 y c c) (at x) (slot m u)) UNIV"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. Wc_d2 y c c) (at x) (slot m u))
      = (\<lambda>x. 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV. - (2 * (c \<bullet> (vec_nth x m - vec_nth x p))
            * cos (c \<bullet> (vec_nth x m - vec_nth x p))
          - (c \<bullet> (vec_nth x m - vec_nth x p))\<^sup>2
            * sin (c \<bullet> (vec_nth x m - vec_nth x p)))))"
    by (rule ext) (rule T2rad_slot_value)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
          real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_uminus
          real_analytic_on_diff real_analytic_on_power
          real_analytic_on_sin_comp real_analytic_on_cos_comp
          real_analytic_on_xslot_phase)
qed

theorem real_analytic_on_T3rad_slot_value:
  fixes c u :: "real^2" and m :: "'n::finite"
  shows "real_analytic_on
      (\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. T3rad y c) (at x) (slot m u)) UNIV"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. T3rad y c) (at x) (slot m u))
      = (\<lambda>x. 2 * (c \<bullet> u) * (\<Sum>p\<in>UNIV.
          3 * (c \<bullet> (vec_nth x m - vec_nth x p))\<^sup>2
            * sin (c \<bullet> (vec_nth x m - vec_nth x p))
          + (c \<bullet> (vec_nth x m - vec_nth x p)) ^ 3
            * cos (c \<bullet> (vec_nth x m - vec_nth x p))))"
    by (rule ext) (rule T3rad_slot_value)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
          real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
          real_analytic_on_power real_analytic_on_sin_comp real_analytic_on_cos_comp
          real_analytic_on_xslot_phase)
qed

theorem real_analytic_on_Hrad2_slot_value:
  fixes u \<omega> \<omega>0 \<omega>s :: "real^2" and m :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "real_analytic_on
      (\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot m u)) UNIV"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x) (slot m u))
      = (\<lambda>x. 2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> u) * (\<Sum>p\<in>UNIV.
           deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * (- (sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                 + (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                   * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))))
           + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
               * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * (- sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p)))
           + gain_dip \<omega>
             * (- (2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                   * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                 - (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))\<^sup>2
                   * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))))
           + deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * (- (sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                 + (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                   * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))))))"
    by (rule ext) (rule Hrad2_slot_value[OF detnz])
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
          real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
          real_analytic_on_diff real_analytic_on_uminus real_analytic_on_power
          real_analytic_on_sin_comp real_analytic_on_cos_comp
          real_analytic_on_xslot_phase)
qed

text \<open>\<^bold>\<open>The remaining gap, made precise.\<close>  \<open>Lambda_rad_ij\<close> is a polynomial in the
  \<open>Phi_par\<close> u-slot derivatives and the \<open>Hrad2\<close> u-slot derivatives.  The \<open>Hrad2\<close> factors
  are analytic by the theorem above; the \<open>Phi_par\<close> factors are the moment/\<open>dEjm\<close>
  composite (see \<open>Phi_par_uslot_value\<close>), whose analyticity assembles from the bridge's
  \<open>real_analytic_on_M*_moment\<close> / \<open>real_analytic_on_DM*_paper_x\<close> stack --- stated here as
  explicit hypotheses so the genericity argument can consume this lemma the moment that
  assembly lands.\<close>

lemma real_analytic_on_Lambda_rad_ij_of_factors:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and i j :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and phi_i: "real_analytic_on (\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>))) UNIV"
    and phi_j: "real_analytic_on (\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>))) UNIV"
  shows "real_analytic_on (\<lambda>x. Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j) UNIV"
  unfolding Lambda_rad_ij_def
  by (intro real_analytic_on_diff real_analytic_on_mult phi_i phi_j
        real_analytic_on_Hrad2_slot_value[OF detnz])


section \<open>Tier 4c: the \<open>Phi_par\<close> factor assembly --- \<open>Lambda_rad_ij\<close> analyticity unconditional\<close>

text \<open>\<^bold>\<open>Purpose.\<close>  Discharge the two hypotheses of
  \<open>real_analytic_on_Lambda_rad_ij_of_factors\<close>: the \<open>Phi_par\<close> u-slot derivative is the
  moment/\<open>dEjm\<close> composite (@{thm Phi_par_uslot_value}), and its x-analyticity assembles
  from the bridge's JOINT \<open>(c, x)\<close> moment-analyticity stack by composing with the
  analytic pairing \<open>x \<mapsto> (c, x)\<close>.  The same route gives analyticity of the \<open>gradU\<^sub>2\<close>
  slot derivative (the \<open>s\<^sub>k\<close> side condition) via
  @{thm has_derivative_gradU_dip_component_x}.  Net result: BOTH side-condition
  functions of the \<open>Jac3_H12rad\<close> rank criterion are real-analytic in \<open>x\<close>, so the
  nowhere-dense-zeros genericity argument can run on them.\<close>

subsection \<open>Fixing the first coordinate of the joint moment lemmas\<close>

lemma real_analytic_on_pair_const_fst:
  fixes c :: "'a::euclidean_space"
  shows "real_analytic_on (\<lambda>x::'b::euclidean_space. (c, x)) UNIV"
proof -
  have bl: "bounded_linear (\<lambda>x::'b. ((0::'a), x))"
    by (intro bounded_linear_Pair bounded_linear_zero bounded_linear_ident)
  have eq: "(\<lambda>x::'b. (c, x)) = (\<lambda>x::'b. (c, (0::'b)) + ((0::'a), x))"
    by (rule ext) (simp add: prod_eq_iff)
  thus ?thesis
    using bl real_analytic_on_add[of "\<lambda>uua. (c, 0) + (0, 0)" UNIV "Pair 0"] 
      real_analytic_on_bounded_linear[of UNIV "Pair 0"]
      real_analytic_on_const[of UNIV "(c, 0) + (0, 0)"] by auto

qed

lemma real_analytic_on_fix_c:
  fixes F :: "(real^2) \<times> ((real^2)^'n::finite) \<Rightarrow> 'b::banach" and c :: "real^2"
  assumes FA: "real_analytic_on F UNIV"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n. F (c, x)) UNIV"
  by (rule real_analytic_on_compose[OF real_analytic_on_pair_const_fst FA subset_UNIV])

lemma real_analytic_on_A_moment_x:
  fixes c :: "real^2"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n::finite. A_moment x c) UNIV"
proof -
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
      (\<lambda>p::(real^2) \<times> ((real^2)^'n). A_moment (snd p) (fst p)) (c, x)) UNIV"
    by (rule real_analytic_on_fix_c[OF real_analytic_on_A_moment])
  thus ?thesis by simp
qed

lemma real_analytic_on_M1_moment_x:
  fixes c :: "real^2"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n::finite. M1_moment x c) UNIV"
proof -
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
      (\<lambda>p::(real^2) \<times> ((real^2)^'n). M1_moment (snd p) (fst p)) (c, x)) UNIV"
    by (rule real_analytic_on_fix_c[OF real_analytic_on_M1_moment])
  thus ?thesis by simp
qed

lemma real_analytic_on_M2_moment_x:
  fixes c :: "real^2"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n::finite. M2_moment x c) UNIV"
proof -
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
      (\<lambda>p::(real^2) \<times> ((real^2)^'n). M2_moment (snd p) (fst p)) (c, x)) UNIV"
    by (rule real_analytic_on_fix_c[OF real_analytic_on_M2_moment])
  thus ?thesis by simp
qed

lemma real_analytic_on_d_A_moment_x_fix:
  fixes c :: "real^2" and h :: "(real^2)^'n::finite"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n. d_A_moment_x x c h) UNIV"
proof -
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
      (\<lambda>p::(real^2) \<times> ((real^2)^'n). d_A_moment_x (snd p) (fst p) h) (c, x)) UNIV"
    by (rule real_analytic_on_fix_c[OF real_analytic_on_d_A_moment_x])
  thus ?thesis by simp
qed

lemma real_analytic_on_d_M1_moment_x_fix:
  fixes c :: "real^2" and h :: "(real^2)^'n::finite"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n. d_M1_moment_x x c h) UNIV"
proof -
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
      (\<lambda>p::(real^2) \<times> ((real^2)^'n). d_M1_moment_x (snd p) (fst p) h) (c, x)) UNIV"
    by (rule real_analytic_on_fix_c[OF real_analytic_on_d_M1_moment_x])
  thus ?thesis by simp
qed

lemma real_analytic_on_d_M2_moment_x_fix:
  fixes c :: "real^2" and h :: "(real^2)^'n::finite"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n. d_M2_moment_x x c h) UNIV"
proof -
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
      (\<lambda>p::(real^2) \<times> ((real^2)^'n). d_M2_moment_x (snd p) (fst p) h) (c, x)) UNIV"
    by (rule real_analytic_on_fix_c[OF real_analytic_on_d_M2_moment_x])
  thus ?thesis by simp
qed

subsection \<open>The \<open>dEjm\<close> composite is analytic in \<open>x\<close>\<close>

lemma real_analytic_on_dEjm_moment:
  fixes P G C1 C2 :: real and c :: "real^2" and h :: "(real^2)^'n::finite"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n.
      dEjm P G C1 C2 (M_paper x c) (DM_paper_x x c h)) UNIV"
proof -
  have eq:
    "(\<lambda>x::(real^2)^'n.
        dEjm P G C1 C2 (M_paper x c) (DM_paper_x x c h))
      =
     (\<lambda>x.
        P * (2 * Re (A_moment x c) * Re (d_A_moment_x x c h)
           + 2 * Im (A_moment x c) * Im (d_A_moment_x x c h))
      + G * (2 * Re
          (cnj (d_A_moment_x x c h)
             * ((- \<i>) * complex_of_real C1 * M1_moment x c
              + (- \<i>) * complex_of_real C2 * M2_moment x c)
           + cnj (A_moment x c)
             * ((- \<i>) * complex_of_real C1 * d_M1_moment_x x c h
              + (- \<i>) * complex_of_real C2 * d_M2_moment_x x c h))))"
  proof (rule ext)
    fix x :: "(real^2)^'n"
    have MA:   "M_paper x c $ 1 = A_moment x c"
      by (rule M_paper_components(1))
    have MM1:  "M_paper x c $ 2 = M1_moment x c"
      by (rule M_paper_components(2))
    have MM2:  "M_paper x c $ 3 = M2_moment x c"
      by (rule M_paper_components(3))
    have DMA:  "DM_paper_x x c h $ 1 = d_A_moment_x x c h"
      by (simp add: DM_paper_x_eq_MM)
    have DMM1: "DM_paper_x x c h $ 2 = d_M1_moment_x x c h"
      by (simp add: DM_paper_x_eq_MM)
    have DMM2: "DM_paper_x x c h $ 3 = d_M2_moment_x x c h"
      by (simp add: DM_paper_x_eq_MM)
    show "dEjm P G C1 C2 (M_paper x c) (DM_paper_x x c h) =
       P * (2 * Re (A_moment x c) * Re (d_A_moment_x x c h)
          + 2 * Im (A_moment x c) * Im (d_A_moment_x x c h))
       + G * (2 * Re
          (cnj (d_A_moment_x x c h)
             * ((- \<i>) * complex_of_real C1 * M1_moment x c
              + (- \<i>) * complex_of_real C2 * M2_moment x c)
           + cnj (A_moment x c)
             * ((- \<i>) * complex_of_real C1 * d_M1_moment_x x c h
              + (- \<i>) * complex_of_real C2 * d_M2_moment_x x c h)))"
      unfolding dEjm_def by (simp only: MA MM1 MM2 DMA DMM1 DMM2)
  qed    
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_add real_analytic_on_mult
          real_analytic_on_const[OF open_UNIV] real_analytic_on_Re real_analytic_on_Im
          real_analytic_on_cnj real_analytic_on_cmult[OF open_UNIV]
          real_analytic_on_A_moment_x real_analytic_on_M1_moment_x
          real_analytic_on_M2_moment_x real_analytic_on_d_A_moment_x_fix
          real_analytic_on_d_M1_moment_x_fix real_analytic_on_d_M2_moment_x_fix)
qed

subsection \<open>The \<open>Phi_par\<close> u-slot factor and the \<open>gradU\<^sub>2\<close> slot factor are analytic\<close>

theorem real_analytic_on_Phi_par_uslot:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and i :: "'n::finite"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
        (slot i (cvec_dip \<omega>0 \<omega>s \<omega>))) UNIV"
proof -
  have eq: "(\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))
      = (\<lambda>x. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
           * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
                (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))) 1
         + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
           * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
                (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))) 2)"
    by (rule ext) (rule Phi_par_uslot_value)
  show ?thesis
    unfolding eq vec_lambda_beta
    by (intro real_analytic_on_add real_analytic_on_mult
          real_analytic_on_const[OF open_UNIV] real_analytic_on_dEjm_moment)
qed

theorem real_analytic_on_gradU2_slot:
  fixes \<omega> \<omega>0 \<omega>s v :: "real^2" and k :: "'n::finite"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
        (slot k v)) UNIV"
proof -
  have fd_eq: "frechet_derivative
      (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
      = (dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (2::2) 1) 1)) (gain_dip \<omega>)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 1)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 2)
             (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
         \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))" for x :: "(real^2)^'n"
  proof -
    have hd: "((\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) has_derivative
        (dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (2::2) 1) 1)) (gain_dip \<omega>)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 1)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 2)
             (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
         \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x)"
      by (rule has_derivative_gradU_dip_component_x)
    show ?thesis
      by (rule frechet_derivative_at[OF hd, symmetric])
  qed
  have eq: "(\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
        (slot k v))
      = (\<lambda>x. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (2::2) 1) 1))
             (gain_dip \<omega>)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 1)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) 2)
             (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
             (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot k v)))"
    by (metis (no_types, lifting) comp_def fd_eq)
  show ?thesis
    unfolding eq by (rule real_analytic_on_dEjm_moment)
qed

subsection \<open>The prize: \<open>Lambda_rad_ij\<close> is real-analytic in \<open>x\<close>, unconditionally in the factors\<close>

theorem real_analytic_on_Lambda_rad_ij:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and i j :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n. Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j) UNIV"
  by (rule real_analytic_on_Lambda_rad_ij_of_factors[OF detnz
        real_analytic_on_Phi_par_uslot real_analytic_on_Phi_par_uslot])


section \<open>Tier 5a: the \<open>s\<^sub>k\<close> witness and its genericity\<close>

text \<open>\<^bold>\<open>The witness.\<close>  At the single-bump configuration \<open>slot k w\<close> (element \<open>k\<close> at
  position \<open>w\<close>, all others at the origin) the \<open>s\<^sub>k\<close> side condition of
  \<open>Jac3_H12rad_nonzero_criterion\<close> evaluates in CLOSED FORM: the perp-slot direction
  kills the \<open>d_A\<close> entry and the moment-drag terms, and what survives is a multiple of
  \<open>gain \<cdot> K \<cdot> (N - 1) \<cdot> sin (c \<bullet> w)\<close>, where \<open>K = C\<^sub>1 c\<^sub>2 - C\<^sub>2 c\<^sub>1\<close> measures the
  non-parallelism of \<open>Dcvec(axis 2)\<close> and \<open>c\<close>.  Choosing \<open>w\<close> with \<open>c \<bullet> w = \<pi>/2\<close> makes
  it nonzero whenever \<open>gain \<noteq> 0\<close>, \<open>K \<noteq> 0\<close>, \<open>CARD('n) \<ge> 2\<close>.  Feeding the witness to
  the multivariate workhorse @{thm real_analytic_nowhere_dense_zeros} (with
  @{thm real_analytic_on_gradU2_slot}) yields the genericity: the bad set
  \<open>{x. s\<^sub>k x = 0}\<close> is nowhere dense.\<close>

subsection \<open>Single-bump evaluation of the moment data\<close>

lemma slot_bump_phase:
  fixes c w :: "real^2" and k n :: "'n::finite"
  shows "phase c (slot k w) n = (if n = k then cis (- (c \<bullet> w)) else 1)"
  by (simp add: phase_def slot_nth)

lemma A_moment_single_bump:
  fixes c w :: "real^2" and k :: "'n::finite"
  shows "A_moment (slot k w) c = cis (- (c \<bullet> w)) + of_nat (CARD('n) - 1)"
proof -
  have "A_moment (slot k w) c = (\<Sum>n\<in>UNIV. if n = k then cis (- (c \<bullet> w)) else 1)"
    unfolding A_moment_def by (rule sum.cong[OF refl]) (simp add: slot_bump_phase)
  also have "\<dots> = (if k = k then cis (- (c \<bullet> w)) else 1)
      + (\<Sum>n\<in>UNIV - {k}. if n = k then cis (- (c \<bullet> w)) else 1)"
    by (rule sum.remove[OF finite UNIV_I])
  also have "(\<Sum>n\<in>UNIV - {k}. if n = k then cis (- (c \<bullet> w)) else (1::complex))
      = of_nat (CARD('n) - 1)"
    by (simp add: card_Diff_singleton)
  finally show ?thesis by simp
qed

lemma perp2_component_1: "vec_nth (perp2 c) 1 = - vec_nth c 2"
  by (simp add: perp2_def)

lemma perp2_component_2: "vec_nth (perp2 c) 2 = vec_nth c 1"
  by (simp add: perp2_def)

lemma DM_perp_slot_1:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite" and k :: 'n
  shows "DM_paper_x x c (slot k (perp2 c)) $ 1 = 0"
  by (simp add: DM_paper_x_eq_MM d_A_moment_x_slot perp2_orth)

lemma DM_perp_slot_2:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite" and k :: 'n
  shows "DM_paper_x x c (slot k (perp2 c)) $ 2
       = of_real (- vec_nth c 2) * phase c x k"
  by (simp add: DM_paper_x_eq_MM d_M1_moment_x_slot perp2_orth perp2_component_1)

lemma DM_perp_slot_3:
  fixes c :: "real^2" and x :: "(real^2)^'n::finite" and k :: 'n
  shows "DM_paper_x x c (slot k (perp2 c)) $ 3
       = of_real (vec_nth c 1) * phase c x k"
  by (simp add: DM_paper_x_eq_MM d_M2_moment_x_slot perp2_orth perp2_component_2)

subsection \<open>The closed-form value of \<open>s\<^sub>k\<close> at the single bump\<close>

theorem gradU2_perp_slot_single_bump:
  fixes \<omega> \<omega>0 \<omega>s w :: "real^2" and k :: "'n::finite"
  shows "frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2)
           (at (slot k w)) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
       = 2 * gain_dip \<omega>
         * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 2
          - vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 1)
         * (real (CARD('n)) - 1) * sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> w)"
proof -
  have hd: "((\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) has_derivative
      (dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (2::2) 1) 1)) (gain_dip \<omega>)
           (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1)
           (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2)
           (M_paper (slot k w) (cvec_dip \<omega>0 \<omega>s \<omega>))
       \<circ> DM_paper_x (slot k w) (cvec_dip \<omega>0 \<omega>s \<omega>))) (at (slot k w))"
    by (rule has_derivative_gradU_dip_component_x)
  have fd_eq: "frechet_derivative
      (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at (slot k w))
      = (dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (2::2) 1) 1)) (gain_dip \<omega>)
           (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1)
           (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2)
           (M_paper (slot k w) (cvec_dip \<omega>0 \<omega>s \<omega>))
       \<circ> DM_paper_x (slot k w) (cvec_dip \<omega>0 \<omega>s \<omega>))"
    by (rule frechet_derivative_at[OF hd, symmetric])
  have P0: "frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (2::2) 1) 1) = 0"
    by (simp add: frechet_gdip_eq axis_def)
  have MA: "M_paper (slot k w) (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1
      = cis (- (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> w)) + of_nat (CARD('n) - 1)"
    by (simp add: A_moment_single_bump)
  have ph: "phase (cvec_dip \<omega>0 \<omega>s \<omega>) (slot k w) k = cis (- (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> w))"
    by (simp add: slot_bump_phase)
  show ?thesis
    unfolding fd_eq o_def dEjm_def P0 MA
    by (simp add: DM_perp_slot_1 DM_perp_slot_2 DM_perp_slot_3 ph
          cis_mult sin_minus cos_minus algebra_simps)
qed

subsection \<open>The witness and the genericity theorem\<close>

corollary gradU2_perp_slot_witness:
  fixes \<omega> \<omega>0 \<omega>s w :: "real^2" and k :: "'n::finite"
  assumes gnz: "gain_dip \<omega> \<noteq> 0"
    and Knz: "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 2
            - vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 1
            \<noteq> 0"
    and Nge2: "2 \<le> CARD('n)"
    and snz: "sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> w) \<noteq> 0"
  shows "frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2)
           (at (slot k w)) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) \<noteq> 0"
proof -
  have Npos: "real (CARD('n)) - 1 \<noteq> 0"
    using Nge2 by simp
  show ?thesis
    unfolding gradU2_perp_slot_single_bump
    using gnz Knz Npos snz by simp
qed

theorem gradU2_perp_slot_zeros_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and k :: "'n::finite"
  assumes gnz: "gain_dip \<omega> \<noteq> 0"
    and Knz: "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 2
            - vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 1
            \<noteq> 0"
    and Nge2: "2 \<le> CARD('n)"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "interior (closure {x::(real^2)^'n.
      frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
        (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0}) = {}"
proof -
  define w where "w = (pi / (2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)))
      *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>"
  have ccnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    using cnz by simp
  have cw: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> w = pi / 2"
    unfolding w_def
    using ccnz by fastforce 
  have snz: "sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> w) \<noteq> 0"
    unfolding cw by simp
  have ex: "\<exists>x\<in>UNIV. frechet_derivative
      (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
        (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) \<noteq> 0"
    using gradU2_perp_slot_witness[OF gnz Knz Nge2 snz, of k] by blast
  have "interior (closure {x \<in> UNIV.
      frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
        (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0}) = {}"
    by (rule real_analytic_nowhere_dense_zeros[OF real_analytic_on_gradU2_slot
          connected_UNIV ex])
  thus ?thesis by simp
qed


section \<open>Tier 5b: the two-bump \<open>Lambda_rad_ij\<close> witness and its genericity\<close>

text \<open>\<^bold>\<open>Why two bumps.\<close>  Both \<open>Phi_par\<close> (via @{thm Phi_par_radial_dictionary}) and
  \<open>Hrad2\<close> (via @{thm Hrad2_radial_form}) are pair-phase functions of \<open>x\<close>, hence
  translation-invariant, so their u-slot derivatives sum to zero over the slots.  On a
  single bump all non-bump rows coincide and \<open>Lambda_rad_ij\<close> vanishes identically by
  that symmetry.  The minimal asymmetric family is the two-bump configuration
  \<open>slot i w\<^sub>1 + slot j w\<^sub>2\<close>; with \<open>c \<bullet> w\<^sub>1 = \<pi>\<close>, \<open>c \<bullet> w\<^sub>2 = \<pi>/2\<close> the determinant
  collapses to a Wronskian of the two radial-jet profiles at \<open>\<pi>\<close> and \<open>\<pi>/2\<close>, giving

    \<open>\<Lambda> = 4\<pi>q\<^sup>2(N-3)(N-2) \<cdot> (2(A+g\<^sub>0)\<^sup>2 - g\<^sub>0(2A+B) + g\<^sub>0\<^sup>2\<pi>\<^sup>2/4)\<close>

  with \<open>q = c \<bullet> c\<close>, \<open>A = gdip'(\<omega>\<^sub>1)e\<^sub>1\<close>, \<open>B = gdip''(\<omega>\<^sub>1)e\<^sub>1\<^sup>2\<close>, \<open>g\<^sub>0 = gain\<close>.  The last
  factor is the explicit design condition \<open>Wnz\<close>.\<close>

subsection \<open>Two-bump row sums for profiles vanishing at 0\<close>

lemma two_bump_nth:
  fixes w1 w2 :: "real^2" and i j p :: "'n::finite"
  assumes ij: "i \<noteq> j"
  shows "vec_nth (slot i w1 + slot j w2) p
       = (if p = i then w1 else if p = j then w2 else 0)"
  using ij by (simp add: slot_nth vector_add_component)

lemma card_ge_two:
  fixes i j :: "'n::finite"
  assumes ij: "i \<noteq> j"
  shows "2 \<le> CARD('n)"
proof -
  have "card {i, j} \<le> CARD('n)"
    by (rule card_mono[OF finite subset_UNIV])
  thus ?thesis using ij by simp
qed

lemma two_bump_row_sum_i:
  fixes f :: "real \<Rightarrow> real" and c w1 w2 :: "real^2" and i j :: "'n::finite"
  assumes ij: "i \<noteq> j" and f0: "f 0 = 0"
  shows "(\<Sum>p\<in>UNIV. f (c \<bullet> (vec_nth (slot i w1 + slot j w2) i
                          - vec_nth (slot i w1 + slot j w2) p)))
       = f (c \<bullet> w1 - c \<bullet> w2) + (real (CARD('n)) - 2) * f (c \<bullet> w1)"
proof -
  have body: "f (c \<bullet> (vec_nth (slot i w1 + slot j w2) i
                    - vec_nth (slot i w1 + slot j w2) p))
      = (if p = i then 0 else if p = j then f (c \<bullet> w1 - c \<bullet> w2) else f (c \<bullet> w1))"
    for p :: 'n
    by (metis (mono_tags, opaque_lifting) assms diff_self diff_zero inner_diff_right two_bump_nth)
  have jmem: "j \<in> UNIV - {i}"
    using ij by simp
  have "(\<Sum>p\<in>UNIV. f (c \<bullet> (vec_nth (slot i w1 + slot j w2) i
                        - vec_nth (slot i w1 + slot j w2) p)))
      = (\<Sum>p\<in>UNIV. if p = i then 0 else if p = j then f (c \<bullet> w1 - c \<bullet> w2)
          else f (c \<bullet> w1))"
    by (rule sum.cong[OF refl]) (rule body)
  also have "\<dots> = (if i = i then 0 else if i = j then f (c \<bullet> w1 - c \<bullet> w2)
        else f (c \<bullet> w1))
      + (\<Sum>p\<in>UNIV - {i}. if p = i then 0 else if p = j then f (c \<bullet> w1 - c \<bullet> w2)
          else f (c \<bullet> w1))"
    by (rule sum.remove[OF finite UNIV_I])
  also have "(\<Sum>p\<in>UNIV - {i}. if p = i then 0 else if p = j then f (c \<bullet> w1 - c \<bullet> w2)
        else f (c \<bullet> w1))
      = (if j = i then 0 else if j = j then f (c \<bullet> w1 - c \<bullet> w2) else f (c \<bullet> w1))
      + (\<Sum>p\<in>UNIV - {i} - {j}. if p = i then 0
          else if p = j then f (c \<bullet> w1 - c \<bullet> w2) else f (c \<bullet> w1))"
    by (rule sum.remove[OF _ jmem]) simp
  also have "(\<Sum>p\<in>UNIV - {i} - {j}. if p = i then 0
        else if p = j then f (c \<bullet> w1 - c \<bullet> w2) else f (c \<bullet> w1))
      = (\<Sum>p\<in>UNIV - {i} - {j}. f (c \<bullet> w1))"
    by (rule sum.cong[OF refl]) auto
  also have "\<dots> = real (card (UNIV - {i} - {j})) * f (c \<bullet> w1)"
    by simp
  also have "card (UNIV - {i} - {j}) = CARD('n) - 2"
    using ij by (simp add: card_Diff_singleton)
  also have "real (CARD('n) - 2) = real (CARD('n)) - 2"
    using card_ge_two[OF ij] by simp
  finally show ?thesis using ij by simp
qed

lemma two_bump_row_sum_j:
  fixes f :: "real \<Rightarrow> real" and c w1 w2 :: "real^2" and i j :: "'n::finite"
  assumes ij: "i \<noteq> j" and f0: "f 0 = 0"
  shows "(\<Sum>p\<in>UNIV. f (c \<bullet> (vec_nth (slot i w1 + slot j w2) j
                          - vec_nth (slot i w1 + slot j w2) p)))
       = f (c \<bullet> w2 - c \<bullet> w1) + (real (CARD('n)) - 2) * f (c \<bullet> w2)"
proof -
  have swap: "slot i w1 + slot j w2 = slot j w2 + slot i w1"
    by (simp add: add.commute)
  show ?thesis
    unfolding swap using assms by (subst two_bump_row_sum_i, simp_all)
qed

subsection \<open>The \<open>Phi_par\<close> u-slot derivative as a radial pair-phase sum\<close>

theorem Phi_par_uslot_radial:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite" and m :: 'n
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m (cvec_dip \<omega>0 \<omega>s \<omega>))
       = 2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>) * (\<Sum>p\<in>UNIV.
           deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * (- sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p)))
           + gain_dip \<omega>
             * (- (sin (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                 + (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p))
                   * cos (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p)))))"
proof -
  define A where "A = deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define G where "G = (\<lambda>u. A * cos u + gain_dip \<omega> * (- (u * sin u)))"
  define G' where "G' = (\<lambda>u. A * (- sin u)
      + gain_dip \<omega> * (- (sin u + u * cos u)))"
  have eqf: "(\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) = (\<lambda>y. \<Sum>n\<in>UNIV. \<Sum>p\<in>UNIV.
      G (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth y n - vec_nth y p)))"
    unfolding G_def
    by (rule ext)
       (simp add: Phi_par_radial_dictionary[OF detnz] frechet_gdip_eq A_def
          Wc_def Wc_d1_def sum.distrib sum_negf sum_subtractf sum_distrib_left
          algebra_simps)
  have dG: "(G has_field_derivative G' u) (at u)" for u :: real
    unfolding G_def G'_def
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have oddG: "G' (- u) = - G' u" for u :: real
    unfolding G'_def by (simp add: algebra_simps)
  have "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m (cvec_dip \<omega>0 \<omega>s \<omega>))
      = 2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>) * (\<Sum>p\<in>UNIV.
          G' (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> (vec_nth x m - vec_nth x p)))"
    unfolding eqf by (rule pair_phase_sum_slot_value_odd[OF dG oddG])
  thus ?thesis
    unfolding G'_def A_def by simp
qed

subsection \<open>The two-bump witness\<close>

theorem Lambda_rad_two_bump_witness:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and i j :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and ij: "i \<noteq> j"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and N4: "4 \<le> CARD('n)"
    and Wnz: "2 * (deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 + gain_dip \<omega>)\<^sup>2
            - gain_dip \<omega> * (2 * deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                  * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
            + (gain_dip \<omega>)\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
  shows "Lambda_rad_ij
      (slot i ((pi / (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>)) *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
       + slot j ((pi / (2 * (cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> cvec_dip \<omega>0 \<omega>s \<omega>))) *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>))
      \<omega> \<omega>0 \<omega>s i j \<noteq> 0"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define q where "q = c \<bullet> c"
  define A where "A = deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define B where "B = deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
      * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define g0 where "g0 = gain_dip \<omega>"
  define Phi' where "Phi' = (\<lambda>u. A * (- sin u) + g0 * (- (sin u + u * cos u)))"
  define Gr' where "Gr' = (\<lambda>u. A * (- (sin u + u * cos u)) + B * (- sin u)
      + g0 * (- (2 * u * cos u - u\<^sup>2 * sin u))
      + A * (- (sin u + u * cos u)))"
  define w1 where "w1 = (pi / q) *\<^sub>R c"
  define w2 where "w2 = (pi / (2 * q)) *\<^sub>R c"
  define x0 where "x0 = slot i w1 + slot j w2"
  define N where "N = real (CARD('n))"
  have qnz: "q \<noteq> 0"
    unfolding q_def c_def using cnz by (simp add: dot_square_norm)
  have t1: "c \<bullet> w1 = pi"
    unfolding w1_def by (simp add: inner_scaleR_right q_def[symmetric] qnz)
  have t2: "c \<bullet> w2 = pi / 2"
    unfolding w2_def by (simp add: inner_scaleR_right q_def[symmetric] qnz)
  have Phi'0: "Phi' 0 = 0"
    unfolding Phi'_def by simp
  have Gr'0: "Gr' 0 = 0"
    unfolding Gr'_def by simp
  have Phi'odd: "Phi' (- u) = - Phi' u" for u :: real
    unfolding Phi'_def by (simp add: algebra_simps)
  have row_Phi_i: "(\<Sum>p\<in>UNIV. Phi' (c \<bullet> (vec_nth x0 i - vec_nth x0 p)))
      = Phi' (pi / 2) + (N - 2) * Phi' pi"
    using two_bump_row_sum_i[of i j Phi' c w1 w2, OF ij Phi'0] t1 t2
    unfolding x0_def N_def by simp
  have row_Phi_j: "(\<Sum>p\<in>UNIV. Phi' (c \<bullet> (vec_nth x0 j - vec_nth x0 p)))
      = - Phi' (pi / 2) + (N - 2) * Phi' (pi / 2)"
    using two_bump_row_sum_j[of i j Phi' c w1 w2, OF ij Phi'0] t1 t2
    unfolding x0_def N_def
    by (simp add: Phi'odd[of "pi/2", symmetric])
  have phi_val: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot m c)
      = 2 * q * (\<Sum>p\<in>UNIV. Phi' (c \<bullet> (vec_nth x0 m - vec_nth x0 p)))" for m :: 'n
    using Phi_par_uslot_radial[OF detnz, of x0 m]
    unfolding c_def[symmetric] q_def[symmetric] Phi'_def A_def g0_def by simp
  have H_val: "frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x0) (slot m c)
      = 2 * q * (\<Sum>p\<in>UNIV. Gr' (c \<bullet> (vec_nth x0 m - vec_nth x0 p)))" for m :: 'n
    using Hrad2_slot_value[OF detnz, of x0 m c]
    unfolding c_def[symmetric] q_def[symmetric] Gr'_def A_def B_def g0_def by simp
  have phi_i: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot i c)
      = 2 * q * (Phi' (pi / 2) + (N - 2) * Phi' pi)"
    unfolding phi_val[of i] row_Phi_i ..
  have phi_j: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot j c)
      = 2 * q * (- Phi' (pi / 2) + (N - 2) * Phi' (pi / 2))"
    unfolding phi_val[of j] row_Phi_j ..
  have row_Gr_i: "(\<Sum>p\<in>UNIV. Gr' (c \<bullet> (vec_nth x0 i - vec_nth x0 p)))
      = Gr' (pi / 2) + (N - 2) * Gr' pi"
    using two_bump_row_sum_i[of i j Gr' c w1 w2, OF ij Gr'0] t1 t2
    unfolding x0_def N_def by simp
  have H_i: "frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x0) (slot i c)
      = 2 * q * (Gr' (pi / 2) + (N - 2) * Gr' pi)"
    unfolding H_val[of i] row_Gr_i ..
  have Gr'odd: "Gr' (- u) = - Gr' u" for u :: real
    unfolding Gr'_def by (simp add: power2_eq_square algebra_simps)
  have row_Gr_j: "(\<Sum>p\<in>UNIV. Gr' (c \<bullet> (vec_nth x0 j - vec_nth x0 p)))
      = - Gr' (pi / 2) + (N - 2) * Gr' (pi / 2)"
    using two_bump_row_sum_j[of i j Gr' c w1 w2, OF ij Gr'0] t1 t2
    unfolding x0_def N_def
    by (simp add: Gr'odd[of "pi/2", symmetric])
  have H_j: "frechet_derivative (\<lambda>y. Hrad2 y \<omega> \<omega>0 \<omega>s) (at x0) (slot j c)
      = 2 * q * (- Gr' (pi / 2) + (N - 2) * Gr' (pi / 2))"
    unfolding H_val[of j] row_Gr_j ..
  have PhiPi: "Phi' pi = pi * g0"
    unfolding Phi'_def by simp
  have PhiHalf: "Phi' (pi / 2) = - (A + g0)"
    unfolding Phi'_def by simp
  have GrPi: "Gr' pi = 2 * pi * A + 2 * pi * g0"
    unfolding Gr'_def by (simp add: power2_eq_square)
  have GrHalf: "Gr' (pi / 2) = - (2 * A) - B + g0 * pi\<^sup>2 / 4"
    unfolding Gr'_def by (simp add: power2_eq_square algebra_simps)
  have Lval: "Lambda_rad_ij x0 \<omega> \<omega>0 \<omega>s i j
      = 4 * q\<^sup>2 * (N - 3) * (N - 2)
        * (Phi' pi * Gr' (pi / 2) - Phi' (pi / 2) * Gr' pi)"
    unfolding Lambda_rad_ij_def c_def[symmetric] phi_i phi_j H_i H_j
    by (simp add: power2_eq_square algebra_simps)
  have Wron: "Phi' pi * Gr' (pi / 2) - Phi' (pi / 2) * Gr' pi
      = pi * (2 * (A + g0)\<^sup>2 - g0 * (2 * A + B) + g0\<^sup>2 * pi\<^sup>2 / 4)"
    unfolding PhiPi PhiHalf GrPi GrHalf
    by (simp add: power2_eq_square field_simps)
  have N3: "N - 3 \<noteq> 0" and N2: "N - 2 \<noteq> 0"
    using N4 unfolding N_def by simp_all
  have Wnz': "2 * (A + g0)\<^sup>2 - g0 * (2 * A + B) + g0\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
    using Wnz unfolding A_def B_def g0_def by argo
  have "Lambda_rad_ij x0 \<omega> \<omega>0 \<omega>s i j \<noteq> 0"
    unfolding Lval Wron
    using qnz N3 N2 Wnz' by simp
  thus ?thesis
    unfolding x0_def w1_def w2_def q_def c_def by simp
qed

theorem Lambda_rad_zeros_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and i j :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and ij: "i \<noteq> j"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and N4: "4 \<le> CARD('n)"
    and Wnz: "2 * (deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 + gain_dip \<omega>)\<^sup>2
            - gain_dip \<omega> * (2 * deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                  * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
            + (gain_dip \<omega>)\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
  shows "interior (closure {x::(real^2)^'n. Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j = 0}) = {}"
proof -
  have ex: "\<exists>x\<in>UNIV. Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j \<noteq> 0"
    using Lambda_rad_two_bump_witness[OF detnz ij cnz N4 Wnz] by blast
  have "interior (closure {x \<in> UNIV. Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j = 0}) = {}"
    by (rule real_analytic_nowhere_dense_zeros[OF real_analytic_on_Lambda_rad_ij[OF detnz]
          connected_UNIV ex])
  thus ?thesis by simp
qed


section \<open>Tier 5c: combined genericity of the H12 radial rank determinant\<close>

text \<open>The two Tier 5 witnesses give nowhere-dense zero sets for the two scalar factors in
  @{thm Jac3_H12rad_identity}.  This assembly theorem packages the consequence needed by
  downstream H12 work: the whole block-triangular rank determinant is nonzero off a meager
  set, under explicit checkable \<omega>-side design conditions.\<close>

lemma gain_dip_nonzero_of_Dcvec_det_nonzero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "gain_dip \<omega> \<noteq> 0"
  using detnz Dcvec_det_zero_of_sin gain_dip_nonzero_of_sin by metis

theorem Jac3_H12rad_zeros_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and i j k :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and ij: "i \<noteq> j"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and N4: "4 \<le> CARD('n)"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and Knz: "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 2
            - vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 1
            \<noteq> 0"
    and Wnz: "2 * (deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 + gain_dip \<omega>)\<^sup>2
            - gain_dip \<omega> * (2 * deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                  * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
            + (gain_dip \<omega>)\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
  shows "meager {x::(real^2)^'n. Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k = 0}"
proof -
  let ?s = "\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
        (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"
  let ?S = "{x::(real^2)^'n. ?s x = 0}"
  let ?L = "{x::(real^2)^'n. Lambda_rad_ij x \<omega> \<omega>0 \<omega>s i j = 0}"
  have Nge2: "2 \<le> CARD('n)"
    using N4 by simp
  have ndS: "nowhere_dense ?S"
    using gradU2_perp_slot_zeros_nowhere_dense[OF gnz Knz Nge2 cnz, of k]
    by (simp add: nowhere_dense_def)
  have ndL: "nowhere_dense ?L"
    using Lambda_rad_zeros_nowhere_dense[OF detnz ij cnz N4 Wnz]
    by (simp add: nowhere_dense_def)
  have sub: "{x::(real^2)^'n. Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k = 0} \<subseteq> ?S \<union> ?L"
    by (auto simp: Jac3_H12rad_identity[OF detnz])
  have "meager (?S \<union> ?L)"
    by (rule meager_Un[OF meager_nowhere_dense[OF ndS] meager_nowhere_dense[OF ndL]])
  thus ?thesis
    by (rule meager_subset[OF sub])
qed

theorem Jac3_H12rad_nonzero_in_open:
  fixes V :: "((real^2)^'n::finite) set" and \<omega> \<omega>0 \<omega>s :: "real^2" and i j k :: 'n
  assumes openV: "open V" and Vne: "V \<noteq> {}"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and ij: "i \<noteq> j"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and N4: "4 \<le> CARD('n)"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and Knz: "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 2
            - vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 1
            \<noteq> 0"
    and Wnz: "2 * (deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 + gain_dip \<omega>)\<^sup>2
            - gain_dip \<omega> * (2 * deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                  * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
            + (gain_dip \<omega>)\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
  shows "\<exists>x\<in>V. Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k \<noteq> 0"
proof -
  let ?B = "{x::(real^2)^'n. Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k = 0}"
  have meagB: "meager ?B"
    by (rule Jac3_H12rad_zeros_meager[OF detnz ij cnz N4 gnz Knz Wnz])
  have "\<not> V \<subseteq> ?B"
  proof
    assume sub: "V \<subseteq> ?B"
    have "meager V"
      by (rule meager_subset[OF sub meagB])
    moreover have "\<not> meager V"
      by (rule open_nonempty_not_meager[OF openV Vne])
    ultimately show False by simp
  qed
  thus ?thesis by blast
qed

theorem Jac3_H12rad_zeros_meager_of_det:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and i j k :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and ij: "i \<noteq> j"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and N4: "4 \<le> CARD('n)"
    and Knz: "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 2
            - vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 1
            \<noteq> 0"
    and Wnz: "2 * (deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 + gain_dip \<omega>)\<^sup>2
            - gain_dip \<omega> * (2 * deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                  * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
            + (gain_dip \<omega>)\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
  shows "meager {x::(real^2)^'n. Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k = 0}"
proof -
  have gnz: "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_Dcvec_det_nonzero[OF detnz])
  show ?thesis
    by (rule Jac3_H12rad_zeros_meager[OF detnz ij cnz N4 gnz Knz Wnz])
qed

theorem Jac3_H12rad_nonzero_in_open_of_det:
  fixes V :: "((real^2)^'n::finite) set" and \<omega> \<omega>0 \<omega>s :: "real^2" and i j k :: 'n
  assumes openV: "open V" and Vne: "V \<noteq> {}"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and ij: "i \<noteq> j"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and N4: "4 \<le> CARD('n)"
    and Knz: "vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 2
            - vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2 * vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>) 1
            \<noteq> 0"
    and Wnz: "2 * (deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 + gain_dip \<omega>)\<^sup>2
            - gain_dip \<omega> * (2 * deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                + deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                  * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1)
            + (gain_dip \<omega>)\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
  shows "\<exists>x\<in>V. Jac3_H12rad x \<omega> \<omega>0 \<omega>s i j k \<noteq> 0"
proof -
  have gnz: "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_Dcvec_det_nonzero[OF detnz])
  show ?thesis
    by (rule Jac3_H12rad_nonzero_in_open[OF openV Vne detnz ij cnz N4 gnz Knz Wnz])
qed

subsection \<open>A concrete Robust4-compatible omega witness\<close>

lemma gdip_pi_half: "gdip (pi / 2) = 1"
  by (simp add: gdip_eq_edip_sq edip_def sin_pi_half cos_pi_half)

lemma deriv_gdip_pi_half: "deriv gdip (pi / 2) = 0"
proof -
  have D0: "DERIV gdip (pi / 2) :> 0"
    using g1_gdip_has_deriv[of "pi / 2"]
    by (simp add: sin_pi_half cos_pi_half)
  show ?thesis
    by (rule DERIV_unique[OF DERIV_gdip D0])
qed

lemma deriv2_gdip_pi_half: "deriv (deriv gdip) (pi / 2) = 2 - pi\<^sup>2 / 2"
proof -
  let ?F = "\<lambda>t::real. (cos (pi / 2 * cos t) / sin t)\<^sup>2"
  let ?F' = "\<lambda>t::real.
      pi * cos (pi / 2 * cos t) * sin (pi / 2 * cos t) / sin t
      - 2 * (cos (pi / 2 * cos t))\<^sup>2 * cos t / (sin t)^3"
  have ev: "eventually (\<lambda>t. gdip t = ?F t) (nhds (pi / 2))"
    by (simp add: gdip_eq_edip_sq edip_def)
  have open_sin: "open {t::real. sin t \<noteq> 0}"
    by (intro open_Collect_neq continuous_intros)
  have base_sin: "pi / 2 \<in> {t::real. sin t \<noteq> 0}"
    by (simp add: sin_pi_half)
  have ev_sin: "eventually (\<lambda>t::real. sin t \<noteq> 0) (nhds (pi / 2))"
  proof -
    have "eventually (\<lambda>t::real. t \<in> {u. sin u \<noteq> 0}) (nhds (pi / 2))"
      by (rule eventually_nhds_in_open[OF open_sin base_sin])
    thus ?thesis by simp
  qed
  have dF: "deriv ?F t = ?F' t" if st: "sin t \<noteq> 0" for t :: real
  proof -
    have D: "DERIV ?F t :> ?F' t"
      using st
      by (auto intro!: derivative_eq_intros
          simp: field_simps power2_eq_square power3_eq_cube)
    show ?thesis by (rule DERIV_imp_deriv[OF D])
  qed
  have ev_dF: "eventually (\<lambda>t. deriv ?F t = ?F' t) (nhds (pi / 2))"
    using ev_sin by eventually_elim (rule dF)
  have "(deriv ^^ 2) gdip (pi / 2) = (deriv ^^ 2) ?F (pi / 2)"
    by (rule higher_deriv_cong_ev[OF ev refl])
  also have "\<dots> = deriv ?F' (pi / 2)"
  proof -
    have "deriv (deriv ?F) (pi / 2) = deriv ?F' (pi / 2)"
      by (rule deriv_cong_ev[OF ev_dF refl])
    thus ?thesis by (simp add: numeral_2_eq_2)
  qed
  also have "\<dots> = 2 - pi\<^sup>2 / 2"
  proof -
    have D2: "DERIV ?F' (pi / 2) :> 2 - pi\<^sup>2 / 2"
      by (auto intro!: derivative_eq_intros
          simp: sin_pi_half cos_pi_half field_simps power2_eq_square)
    show ?thesis by (rule DERIV_imp_deriv[OF D2])
  qed
  finally show ?thesis
    by (simp add: numeral_2_eq_2)
qed

lemma h12rad_robust4_omega_witness_in_OmegaPF:
  "vector [pi / 2, pi / 3] \<in> OmegaPF (vector [pi / 2, 0] :: real^2) (pi / 4)"
proof -
  have pi_pos: "0 < (pi::real)" by simp
  show ?thesis
    unfolding OmegaPF_def mem_box_cart
  proof (intro allI conjI)
    fix i :: 2
    show "(vector [pi / 2, 0] - vector [pi / 4, pi]) $ i \<le>
        (vector [pi / 2, pi / 3] :: real^2) $ i"
      using exhaust_2[of i] pi_pos
      by (auto simp: vector_2 vector_minus_component)
    show "(vector [pi / 2, pi / 3] :: real^2) $ i \<le>
        (vector [pi / 2, 0] + vector [pi / 4, pi]) $ i"
      using exhaust_2[of i] pi_pos
      by (auto simp: vector_2 vector_add_component)
  qed
qed

lemma h12rad_robust4_omega_side_conditions:
  shows "det (matrix (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3]))) \<noteq> 0"
    and "cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3]) \<noteq> 0"
    and "vec_nth (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3]) (axis (2::2) 1)) 1
        * vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3])) 2
        - vec_nth (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3]) (axis (2::2) 1)) 2
          * vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3])) 1
        \<noteq> 0"
    and "2 * (deriv gdip (vec_nth (vector [pi / 2, pi / 3] :: real^2) 1)
            * vec_nth (e_par (vector [pi / 2, 0]) (vector [0, 0])
                (vector [pi / 2, pi / 3])) 1
            + gain_dip (vector [pi / 2, pi / 3]))\<^sup>2
        - gain_dip (vector [pi / 2, pi / 3])
          * (2 * deriv gdip (vec_nth (vector [pi / 2, pi / 3] :: real^2) 1)
              * vec_nth (e_par (vector [pi / 2, 0]) (vector [0, 0])
                  (vector [pi / 2, pi / 3])) 1
            + deriv (deriv gdip) (vec_nth (vector [pi / 2, pi / 3] :: real^2) 1)
              * vec_nth (e_par (vector [pi / 2, 0]) (vector [0, 0])
                  (vector [pi / 2, pi / 3])) 1
              * vec_nth (e_par (vector [pi / 2, 0]) (vector [0, 0])
                  (vector [pi / 2, pi / 3])) 1)
        + (gain_dip (vector [pi / 2, pi / 3]))\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
proof -
  define w0 :: "real^2" where
    "w0 = vector [pi / 2, 0]"
  define ws :: "real^2" where
    "ws = vector [0, 0]"
  define w :: "real^2" where
    "w = vector [pi / 2, pi / 3]"
  have sqrt3_sq: "sqrt 3 * sqrt 3 = (3::real)"
    by (simp add: power2_eq_square[symmetric])
  have detnz: "det (matrix (Dcvec_dip w0 ws w)) \<noteq> 0"
    unfolding w0_def ws_def w_def 
    by (simp add: Dcvec_dip_def kx_def ky_def kz_def det_2 matrix_def axis_def vector_2
        sin_pi_half cos_pi_half cos_60 sin_60 sqrt3_sq)
  show g1: "det (matrix (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
          (vector [pi / 2, pi / 3]))) \<noteq> 0"
    using detnz
    unfolding w0_def ws_def w_def by simp
  have c1: "vec_nth (cvec_dip w0 ws w) 1 = -1 / 2"
    unfolding w0_def ws_def w_def 
    by (simp add: cvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half cos_60 sin_60)
  have c2: "vec_nth (cvec_dip w0 ws w) 2 = sqrt 3 / 2"
    unfolding w0_def ws_def w_def by (simp add: cvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half cos_60 sin_60)
  show "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 3]) \<noteq> 0"
    using c1 w0_def w_def ws_def by fastforce  
  show "Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 3]) (axis 2 1) $h 1 *
    cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 3]) $h 2 -
    Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 3]) (axis 2 1) $h 2 *
    cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 3]) $h 1 \<noteq> 0"
    by (simp add: Dcvec_dip_def cvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half cos_60 sin_60 sqrt3_sq)
  have push: "Dcvec_dip w0 ws w (e_par w0 ws w) = cvec_dip w0 ws w"
    unfolding w0_def ws_def w_def by(subst Dcvec_dip_e_par, simp add: g1, simp)
  have eq2: "vec_nth (Dcvec_dip w0 ws w (e_par w0 ws w)) 2  = vec_nth (cvec_dip w0 ws w) 2"
    using push by simp
  have e2_half: "vec_nth (e_par w0 ws w) 2 / 2 = sqrt 3 / 2"
    unfolding w0_def ws_def w_def using eq2 cos_60 sin_60 w0_def w_def ws_def
    by (simp add: Dcvec_dip_def cvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half cos_60 sin_60)
  have e2: "vec_nth (e_par w0 ws w) 2 = sqrt 3"
    using e2_half by simp
  have eq1: "- (sqrt 3 * vec_nth (e_par w0 ws w) 2 / 2)
      - vec_nth (e_par w0 ws w) 1 = - 1 / 2"
  proof -
    have "vec_nth (Dcvec_dip w0 ws w (e_par w0 ws w)) 1
      = vec_nth (cvec_dip w0 ws w) 1"
      using push by simp
    thus ?thesis
      unfolding w0_def ws_def w_def 
      by (simp add: Dcvec_dip_def cvec_dip_def kx_def ky_def kz_def axis_def vector_2
          sin_pi_half cos_pi_half cos_60 sin_60)
  qed
  have e1: "vec_nth (e_par w0 ws w) 1 = - 1"
  proof -
    have "- (sqrt 3 * sqrt 3 / 2) - vec_nth (e_par w0 ws w) 1 = - 1 / 2"
      using eq1 by (simp add: e2)
    thus ?thesis
      using sqrt3_sq by linarith
  qed
  have gain: "gain_dip w = 1"
    unfolding w_def gain_dip_def by (simp add: gdip_pi_half)
  have d1: "deriv gdip (vec_nth w 1) = 0"
    unfolding w_def by (simp add: deriv_gdip_pi_half)
  have d2: "deriv (deriv gdip) (vec_nth w 1) = 2 - pi\<^sup>2 / 2"
    unfolding w_def by (simp add: deriv2_gdip_pi_half)
  have W_eq: "2 * (deriv gdip (vec_nth w 1) * vec_nth (e_par w0 ws w) 1 + gain_dip w)\<^sup>2
        - gain_dip w * (2 * deriv gdip (vec_nth w 1) * vec_nth (e_par w0 ws w) 1
            + deriv (deriv gdip) (vec_nth w 1) * vec_nth (e_par w0 ws w) 1
              * vec_nth (e_par w0 ws w) 1)
        + (gain_dip w)\<^sup>2 * pi\<^sup>2 / 4 = 3 * pi\<^sup>2 / 4"
    using e1 gain d1 d2 by (simp add: power2_eq_square field_simps)
  have Wpos: "(3::real) * pi\<^sup>2 / 4 \<noteq> 0"
    using pi_gt_zero by simp
  show "2 * (deriv gdip (vec_nth w 1) * vec_nth (e_par w0 ws w) 1 + gain_dip w)\<^sup>2
        - gain_dip w * (2 * deriv gdip (vec_nth w 1) * vec_nth (e_par w0 ws w) 1
            + deriv (deriv gdip) (vec_nth w 1) * vec_nth (e_par w0 ws w) 1
              * vec_nth (e_par w0 ws w) 1)
        + (gain_dip w)\<^sup>2 * pi\<^sup>2 / 4 \<noteq> 0"
    unfolding W_eq using Wpos by simp
qed

theorem Jac3_H12rad_nonzero_in_open_robust4_witness:
  fixes V :: "((real^2)^'n::finite) set" and i j k :: 'n
  assumes openV: "open V" and Vne: "V \<noteq> {}"
    and ij: "i \<noteq> j"
    and N4: "4 \<le> CARD('n)"
  shows "\<exists>x\<in>V. Jac3_H12rad x (vector [pi / 2, pi / 3])
      (vector [pi / 2, 0]) (vector [0, 0]) i j k \<noteq> 0"
proof -
  define w0 :: "real^2" where "w0 = vector [pi / 2, 0]"
  define ws :: "real^2" where "ws = vector [0, 0]"
  define w :: "real^2"  where "w = vector [pi / 2, pi / 3]"

  have detnz: "det (matrix (Dcvec_dip w0 ws w)) \<noteq> 0"
    unfolding w0_def ws_def w_def by (rule h12rad_robust4_omega_side_conditions(1))
  have cnz: "cvec_dip w0 ws w \<noteq> 0"
    unfolding w0_def ws_def w_def by (rule h12rad_robust4_omega_side_conditions(2))
  have Knz: "vec_nth (Dcvec_dip w0 ws w (axis (2::2) 1)) 1
        * vec_nth (cvec_dip w0 ws w) 2
      - vec_nth (Dcvec_dip w0 ws w (axis (2::2) 1)) 2
        * vec_nth (cvec_dip w0 ws w) 1  \<noteq> 0"
    unfolding w0_def ws_def w_def by (rule h12rad_robust4_omega_side_conditions(3))
  have Wnz: "2 * (deriv gdip (vec_nth w 1) * vec_nth (e_par w0 ws w) 1 + gain_dip w)\<^sup>2
      - gain_dip w
          * (2 * deriv gdip (vec_nth w 1)
              * vec_nth (e_par w0 ws w) 1
            + deriv (deriv gdip) (vec_nth w 1)
              * vec_nth (e_par w0 ws w) 1
              * vec_nth (e_par w0 ws w) 1)
      + (gain_dip w)\<^sup>2 * pi\<^sup>2 / 4  \<noteq> 0"
    unfolding w0_def ws_def w_def by (rule h12rad_robust4_omega_side_conditions(4))
  show "\<exists>x\<in>V. Jac3_H12rad x w w0 ws i j k \<noteq> 0"
    by (rule Jac3_H12rad_nonzero_in_open_of_det[OF openV Vne detnz ij cnz N4 Knz Wnz])
qed

end
