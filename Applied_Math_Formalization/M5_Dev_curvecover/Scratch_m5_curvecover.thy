theory Scratch_m5_curvecover
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) Core "3" --- the COLLINEAR LOCUS has a finite \<open>C\<^sup>1\<close>-arc cover.\<close>

  This file discharges (or precisely scopes) the terminal Robust3 sorry
  @{text collinear_locus_finite_arc_cover}: the phase-collinear locus
  \<open>{\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}\<close> is @{text finitely_arc_coverable}
  --- covered by finitely many @{text analytic_arc}'s, each a genuine \<open>C\<^sup>1\<close>
  (@{const C1_differentiable_on}) image of a compact interval, lying inside the box.

  \<^bold>\<open>The C1 soundness requirement.\<close>  The downstream consumer (D3fix /
  @{text excess_arc_charts_Nn}, via @{text analytic_arc_negligible}) needs each arc
  to be NEGLIGIBLE, which only holds for genuinely \<open>C\<^sup>1\<close> arcs (a Peano space-filling
  curve is a continuous image of an interval but is NOT negligible).  So we use the
  \<open>C\<^sup>1\<close> definition of @{text analytic_arc}, NOT the weak @{const continuous_on} one.\<close>


subsection \<open>The \<open>C\<^sup>1\<close> analytic-arc predicate and the soundness target\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> \<phi> C1_differentiable_on {a..b}
                          \<and> \<gamma> = \<phi> ` {a..b})"

definition finitely_arc_coverable :: "(real^2) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> bool" where
  "finitely_arc_coverable \<Gamma> ctr \<delta> \<longleftrightarrow>
     (\<exists>(I::nat set) arc. finite I \<and> \<Gamma> \<subseteq> (\<Union>i\<in>I. arc i)
         \<and> (\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>))"

text \<open>\<^bold>\<open>Soundness wiring check\<close> (sorry-free): a single point is a (degenerate) \<open>C\<^sup>1\<close>
  arc --- the constant map on \<open>{0..0}\<close> is @{const C1_differentiable_on}.  This is the
  degenerate-arc case the curve-structure design uses for the finitely many singular
  points, and it confirms the \<open>C\<^sup>1\<close> @{const analytic_arc} plumbing is correctly wired.\<close>

lemma analytic_arc_singleton: "analytic_arc {p}"
proof -
  have "(\<lambda>t::real. p) C1_differentiable_on {0..0}"
    by (rule C1_differentiable_on_const)
  moreover have "{p} = (\<lambda>t::real. p) ` {0..0}" by simp
  ultimately show ?thesis unfolding analytic_arc_def
    by (intro exI[of _ "0::real"] exI[of _ "0::real"] exI[of _ "\<lambda>t::real. p"]) auto
qed


subsection \<open>The phase-collinear predicate (copied verbatim from the engine)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"


subsection \<open>GENUINE REDUCTION 1: component forms (copied from ArcCover2, sorry-free)\<close>

lemma c1_eq:
  "cvec_dip \<omega>0 \<omega>s \<omega> $ 1
     = (kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)"
  by (simp add: cvec_dip_def axis_def)

lemma c2_eq:
  "cvec_dip \<omega>0 \<omega>s \<omega> $ 2
     = (ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)"
  by (simp add: cvec_dip_def axis_def)

lemma Dc1_eq:
  "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 1
     = cos (\<omega>$1) * cos (\<omega>$2) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (- sin (\<omega>$1))"
  by (simp add: Dcvec_dip_def axis_def)

lemma Dc2_eq:
  "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 2
     = cos (\<omega>$1) * sin (\<omega>$2) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (- sin (\<omega>$1))"
  by (simp add: Dcvec_dip_def axis_def)


subsection \<open>GENUINE REDUCTION 2: phase_collinear = crossTheta vanishes (sorry-free)\<close>

definition crossTheta :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "crossTheta \<omega>0 \<omega>s \<omega> =
     Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 1 * cvec_dip \<omega>0 \<omega>s \<omega> $ 2
   - Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) $ 2 * cvec_dip \<omega>0 \<omega>s \<omega> $ 1"

lemma phase_collinear_iff_crossTheta:
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow> crossTheta \<omega>0 \<omega>s \<omega> = 0"
proof
  define Dc where "Dc = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)"
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  assume "phase_collinear \<omega>0 \<omega>s \<omega>"
  then consider (a) "\<exists>t. Dc = t *\<^sub>R c" | (b) "\<exists>t. c = t *\<^sub>R Dc"
    unfolding phase_collinear_def Dc_def c_def by blast
  thus "crossTheta \<omega>0 \<omega>s \<omega> = 0"
  proof cases
    case a
    then obtain t where t: "Dc = t *\<^sub>R c" by blast
    have "Dc $ 1 * c $ 2 - Dc $ 2 * c $ 1 = 0"
      by (simp add: t)
    thus ?thesis unfolding crossTheta_def Dc_def c_def .
  next
    case b
    then obtain t where t: "c = t *\<^sub>R Dc" by blast
    have "Dc $ 1 * c $ 2 - Dc $ 2 * c $ 1 = 0"
      by (simp add: t algebra_simps)
    thus ?thesis unfolding crossTheta_def Dc_def c_def .
  qed
next
  define Dc where "Dc = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)"
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  assume "crossTheta \<omega>0 \<omega>s \<omega> = 0"
  hence det0: "Dc $ 1 * c $ 2 - c $ 1 * Dc $ 2 = 0"
    unfolding crossTheta_def Dc_def c_def by simp
  show "phase_collinear \<omega>0 \<omega>s \<omega>"
  proof (cases "c = 0")
    case True
    have "c = 0 *\<^sub>R Dc" using True by simp
    thus ?thesis unfolding phase_collinear_def Dc_def c_def by blast
  next
    case False
    obtain t where "Dc = t *\<^sub>R c"
      using cols_dependent_2d[OF det0 False] by blast
    thus ?thesis unfolding phase_collinear_def Dc_def c_def by blast
  qed
qed

lemma collinear_locus_eq_crossTheta_zero:
  "{\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}
     = {\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0}"
  by (simp add: phase_collinear_iff_crossTheta)


subsection \<open>GENUINE REDUCTION 3: separable trig form \<open>\<Theta> = \<alpha>(\<omega>\<^sub>1)cos\<omega>\<^sub>2 + \<beta>(\<omega>\<^sub>1)sin\<omega>\<^sub>2 + \<gamma>(\<omega>\<^sub>1)\<close>\<close>

text \<open>\<^bold>\<open>The decisive structural simplification (sorry-free).\<close>  Clearing the explicit trig
  forms and using the Pythagorean identity, the cross determinant collapses to a
  function that is AFFINE-TRIGONOMETRIC in the second angle:
  \<open>crossTheta = crossA * cos(w2) + crossB * sin(w2) + crossG\<close>, where the three
  coefficient functions \<open>crossA\<close>, \<open>crossB\<close>, \<open>crossG\<close> are
  themselves AFFINE in \<open>cos(w1)\<close> / \<open>sin(w1)\<close> (see the definitions below).  Verified by
  computer algebra; here it is one algebraic @{method simp} identity.  This is FAR
  more tractable than a generic analytic curve: for each fixed \<open>w1\<close> the level set in
  \<open>w2\<close> is the classical \<open>a*cos + b*sin + c = 0\<close> equation.\<close>

text \<open>We carry \<open>Ac, Bc\<close> (the two ratio constants of @{const cvec_dip}) as OPAQUE reals,
  so no division reasoning is needed for the separable identity.\<close>

definition crossA :: "real \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real" where
  "crossA Bc \<omega>s t = Bc - (Bc * kz \<omega>s + ky \<omega>s) * cos t"

definition crossB :: "real \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real" where
  "crossB Ac \<omega>s t = - Ac + (Ac * kz \<omega>s + kx \<omega>s) * cos t"

definition crossG :: "real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real" where
  "crossG Ac Bc \<omega>s t = (Ac * ky \<omega>s - Bc * kx \<omega>s) * sin t"

text \<open>The separable identity is a pure POLYNOMIAL identity in the abstract atoms
  \<open>S,C,s,c\<close> (the four sin/cos values), \<open>Ac,Bc\<close> and \<open>kx\<^sub>s,ky\<^sub>s,kz\<^sub>s\<close>, modulo the single
  relation \<open>C\<^sup>2+S\<^sup>2=1\<close>.  Proved ABSTRACTLY (over generic reals) so the @{method algebra}
  Groebner call sees small atoms and finishes instantly; then instantiated.\<close>

lemma crossTheta_separable_abstract:
  fixes C S c s Ac Bc kxs kys kzs :: real
  assumes pyth: "C * C + S * S = 1"
  shows "(C * c + Ac * (- S)) * ((S * s - kys) + Bc * (C - kzs))
       - (C * s + Bc * (- S)) * ((S * c - kxs) + Ac * (C - kzs))
       = (Bc - (Bc * kzs + kys) * C) * c
         + (- Ac + (Ac * kzs + kxs) * C) * s
         + (Ac * kys - Bc * kxs) * S"
proof -
  have eq: "(C * c + Ac * (- S)) * ((S * s - kys) + Bc * (C - kzs))
       - (C * s + Bc * (- S)) * ((S * c - kxs) + Ac * (C - kzs))
       - ((Bc - (Bc * kzs + kys) * C) * c
         + (- Ac + (Ac * kzs + kxs) * C) * s
         + (Ac * kys - Bc * kxs) * S)
      = (C * C + S * S - 1) * (Bc * c - Ac * s)"
    by (simp add: algebra_simps)
  from pyth have "C * C + S * S - 1 = 0" by simp
  with eq show ?thesis by simp
qed

lemma crossTheta_separable:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2"
  defines "Ac \<equiv> (kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)"
      and "Bc \<equiv> (ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  shows "crossTheta \<omega>0 \<omega>s \<omega>
       = crossA Bc \<omega>s (\<omega>$1) * cos (\<omega>$2)
       + crossB Ac \<omega>s (\<omega>$1) * sin (\<omega>$2)
       + crossG Ac Bc \<omega>s (\<omega>$1)"
proof -
  \<comment> \<open>Abbreviate the two angle components to plain reals.  This avoids a PARSE-TIME
      blowup: the big @{text key} identity below has ~17 \<open>$\<close> (@{const vec_nth})
      occurrences, and the \<open>$\<close>-notation elaborator hangs for many minutes on such a
      term.  With \<open>w1\<close>, \<open>w2\<close> the same identity parses and is discharged instantly.\<close>
  define w1 :: real where "w1 = \<omega>$1"
  define w2 :: real where "w2 = \<omega>$2"
  \<comment> \<open>Expand ONLY the running variable's k-functions; keep \<open>kx \<omega>s\<close>, \<open>kz \<omega>s\<close> opaque.\<close>
  have kxw: "kx \<omega> = sin w1 * cos w2" by (simp add: kx_def w1_def w2_def)
  have kyw: "ky \<omega> = sin w1 * sin w2" by (simp add: ky_def w1_def w2_def)
  have kzw: "kz \<omega> = cos w1"          by (simp add: kz_def w1_def)
  have pyth: "cos w1 * cos w1 + sin w1 * sin w1 = 1"
    using sin_cos_squared_add[of w1] by (simp add: power2_eq_square algebra_simps)
  have key:
    "(cos w1 * cos w2 + Ac * (- sin w1))
        * ((sin w1 * sin w2 - ky \<omega>s) + Bc * (cos w1 - kz \<omega>s))
     - (cos w1 * sin w2 + Bc * (- sin w1))
        * ((sin w1 * cos w2 - kx \<omega>s) + Ac * (cos w1 - kz \<omega>s))
     = (Bc - (Bc * kz \<omega>s + ky \<omega>s) * cos w1) * cos w2
       + (- Ac + (Ac * kz \<omega>s + kx \<omega>s) * cos w1) * sin w2
       + (Ac * ky \<omega>s - Bc * kx \<omega>s) * sin w1"
    by (rule crossTheta_separable_abstract[OF pyth])
  show ?thesis
    unfolding crossTheta_def crossA_def crossB_def crossG_def
              Dc1_eq Dc2_eq c1_eq c2_eq kxw kyw kzw Ac_def[symmetric] Bc_def[symmetric]
              w1_def[symmetric] w2_def[symmetric]
    using key by (simp add: algebra_simps)
qed


subsection \<open>Continuity of \<open>crossTheta\<close> and compactness of the locus (sorry-free)\<close>

text \<open>From the separable form @{thm crossTheta_separable}, \<open>crossTheta\<close> is a continuous
  function of \<open>\<omega>\<close> (a polynomial in \<open>cos/sin\<close> of the two continuous components \<open>\<omega>$1\<close>,
  \<open>\<omega>$2\<close>).  Hence its zero set is closed, and the locus --- a closed subset of the
  compact box @{const OmegaPF} --- is compact.\<close>

lemma continuous_on_crossTheta:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "continuous_on S (\<lambda>\<omega>. crossTheta \<omega>0 \<omega>s \<omega>)"
proof -
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  have eq: "(\<lambda>\<omega>. crossTheta \<omega>0 \<omega>s \<omega>)
          = (\<lambda>\<omega>. crossA Bc \<omega>s (\<omega>$1) * cos (\<omega>$2)
                + crossB Ac \<omega>s (\<omega>$1) * sin (\<omega>$2)
                + crossG Ac Bc \<omega>s (\<omega>$1))"
    unfolding Ac_def Bc_def by (rule ext) (rule crossTheta_separable)
  have c1: "continuous_on S (\<lambda>\<omega>::real^2. \<omega>$1)"
    by (rule linear_continuous_on) (rule bounded_linear_vec_nth)
  have c2: "continuous_on S (\<lambda>\<omega>::real^2. \<omega>$2)"
    by (rule linear_continuous_on) (rule bounded_linear_vec_nth)
  show ?thesis
    unfolding eq crossA_def crossB_def crossG_def
    by (intro continuous_intros c1 c2)
qed

lemma compact_crossTheta_locus:
  fixes ctr :: "real^2"
  shows "compact {\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0}"
proof -
  have z: "{\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0}
            = OmegaPF ctr \<delta> \<inter> (\<lambda>\<omega>. crossTheta \<omega>0 \<omega>s \<omega>) -` {0}"
    by auto
  \<comment> \<open>\<open>crossTheta\<close> is continuous on ALL of \<open>real^2\<close>, so its \<open>0\<close>-preimage is closed.\<close>
  have contU: "continuous_on UNIV (\<lambda>\<omega>. crossTheta \<omega>0 \<omega>s \<omega>)"
    by (rule continuous_on_crossTheta)
  have clpre: "closed ((\<lambda>\<omega>. crossTheta \<omega>0 \<omega>s \<omega>) -` {0})"
    using continuous_closed_preimage[OF contU closed_UNIV closed_singleton] by simp
  have "compact (OmegaPF ctr \<delta> \<inter> (\<lambda>\<omega>. crossTheta \<omega>0 \<omega>s \<omega>) -` {0})"
    by (rule compact_Int_closed[OF OmegaPF_compact clpre])
  thus ?thesis unfolding z .
qed


subsection \<open>Finite-zeros helpers for the singular set (inhomogeneous extensions)\<close>

text \<open>The singular set of @{const crossTheta} (where both partials vanish on the locus)
  reduces, per the design, to \<open>cos \<omega>\<^sub>1 = \<kappa>\<close> equations (degree-\<open>\<le>2\<close> polynomial roots) and
  inhomogeneous \<open>a cos \<omega>\<^sub>2 + b sin \<omega>\<^sub>2 = k\<close> equations.  These two helpers --- the
  inhomogeneous (\<open>k \<noteq> 0\<close>) extensions of the heap's @{thm finite_cos_zeros_interval} /
  @{thm finite_phase_zeros_interval} --- give finiteness on a bounded interval via the
  TWO-coset @{thm cos_eq} / @{thm sin_eq} characterizations.\<close>

lemma finite_cos_eq_zeros_interval:
  fixes lo hi K :: real
  shows "finite {t::real. lo \<le> t \<and> t \<le> hi \<and> cos t = K}"
proof (cases "- 1 \<le> K \<and> K \<le> 1")
  case True
  hence cy: "cos (arccos K) = K" by (simp add: cos_arccos)
  have eq: "{t::real. lo \<le> t \<and> t \<le> hi \<and> cos t = K}
          = {t::real. lo \<le> t \<and> t \<le> hi \<and> (\<exists>i::int. t = of_int i * (2*pi) + arccos K)}
          \<union> {t::real. lo \<le> t \<and> t \<le> hi \<and> (\<exists>i::int. t = of_int i * (2*pi) + (- arccos K))}"
  proof (rule Set.set_eqI)
    fix t :: real
    have ce: "cos t = K
          \<longleftrightarrow> (\<exists>i::int. t = of_int i * (2*pi) + arccos K
                       \<or> t = of_int i * (2*pi) + (- arccos K))"
    proof -
      have "cos t = K \<longleftrightarrow> cos t = cos (arccos K)" using cy by simp
      also have "\<dots> \<longleftrightarrow> (\<exists>n\<in>\<int>. t = arccos K + 2*n*pi \<or> t = - arccos K + 2*n*pi)"
        by (rule cos_eq)
      also have "\<dots> \<longleftrightarrow> (\<exists>i::int. t = of_int i * (2*pi) + arccos K
                                 \<or> t = of_int i * (2*pi) + (- arccos K))"
        by (auto simp: Ints_def algebra_simps)
      finally show ?thesis .
    qed
    show "t \<in> {t::real. lo \<le> t \<and> t \<le> hi \<and> cos t = K}
        \<longleftrightarrow> t \<in> {t::real. lo \<le> t \<and> t \<le> hi \<and> (\<exists>i::int. t = of_int i * (2*pi) + arccos K)}
              \<union> {t::real. lo \<le> t \<and> t \<le> hi \<and> (\<exists>i::int. t = of_int i * (2*pi) + (- arccos K))}"
      using ce by auto
  qed
  have tp: "(0::real) < 2*pi" using pi_gt_zero by simp
  show ?thesis unfolding eq
    by (rule finite_UnI[OF finite_affine_int_zeros[OF tp] finite_affine_int_zeros[OF tp]])
next
  case False
  have empty: "{t::real. lo \<le> t \<and> t \<le> hi \<and> cos t = K} = {}"
  proof (rule equals0I)
    fix t assume "t \<in> {t::real. lo \<le> t \<and> t \<le> hi \<and> cos t = K}"
    hence "cos t = K" by simp
    moreover have "- 1 \<le> cos t" by (rule cos_ge_minus_one)
    moreover have "cos t \<le> 1" by (rule cos_le_one)
    ultimately show False using False by simp
  qed
  show ?thesis unfolding empty by simp
qed

lemma finite_inhom_phase_zeros_interval:
  fixes a b k lo hi :: real
  assumes ab: "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "finite {u::real. lo \<le> u \<and> u \<le> hi \<and> a * cos u + b * sin u = k}"
proof -
  define R :: real where "R = sqrt (a\<^sup>2 + b\<^sup>2)"
  have pos: "0 < a\<^sup>2 + b\<^sup>2" using ab by (simp add: sum_power2_gt_zero_iff)
  have R0: "0 < R" unfolding R_def by (rule real_sqrt_gt_zero[OF pos])
  have Rne: "R \<noteq> 0" using R0 by simp
  have nn: "0 \<le> a\<^sup>2 + b\<^sup>2" using pos by linarith
  have Rsq: "R\<^sup>2 = a\<^sup>2 + b\<^sup>2" unfolding R_def by (rule real_sqrt_pow2[OF nn])
  have ne: "a\<^sup>2 + b\<^sup>2 \<noteq> 0" using pos by auto
  have unit: "(b/R)\<^sup>2 + (a/R)\<^sup>2 = 1"
  proof -
    have "(b/R)\<^sup>2 + (a/R)\<^sup>2 = (b\<^sup>2 + a\<^sup>2) / R\<^sup>2"
      by (simp add: power_divide add_divide_distrib)
    also have "\<dots> = 1" using ne by (simp add: Rsq add.commute)
    finally show ?thesis .
  qed
  obtain \<psi> :: real where psi1: "b/R = cos \<psi>" and psi2: "a/R = sin \<psi>"
    using sincos_total_2pi[OF unit] by blast
  have key: "a * cos u + b * sin u = R * sin (u + \<psi>)" for u :: real
  proof -
    have "a * cos u + b * sin u = R * (sin u * (b/R) + cos u * (a/R))"
      using Rne by (simp add: field_simps)
    also have "\<dots> = R * (sin u * cos \<psi> + cos u * sin \<psi>)" unfolding psi1 psi2 by (rule refl)
    also have "\<dots> = R * sin (u + \<psi>)" by (simp add: sin_add)
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases "- 1 \<le> k/R \<and> k/R \<le> 1")
    case True
    hence sy: "sin (arcsin (k/R)) = k/R" by (simp add: sin_arcsin)
    have eq: "{u::real. lo \<le> u \<and> u \<le> hi \<and> a * cos u + b * sin u = k}
            = {u::real. lo \<le> u \<and> u \<le> hi
                  \<and> (\<exists>i::int. u = of_int i * (2*pi) + (arcsin (k/R) - \<psi>))}
            \<union> {u::real. lo \<le> u \<and> u \<le> hi
                  \<and> (\<exists>i::int. u = of_int i * (2*pi) + (pi - arcsin (k/R) - \<psi>))}"
    proof (rule Set.set_eqI)
      fix u :: real
      have "(a * cos u + b * sin u = k) \<longleftrightarrow> (sin (u + \<psi>) = k/R)"
        using key Rne by (auto simp: field_simps)
      also have "\<dots> \<longleftrightarrow> sin (u + \<psi>) = sin (arcsin (k/R))" using sy by simp
      also have "\<dots> \<longleftrightarrow> (\<exists>n\<in>\<int>. u + \<psi> = arcsin (k/R) + 2*n*pi
                                 \<or> u + \<psi> = - arcsin (k/R) + (2*n+1)*pi)"
        by (rule sin_eq)
      also have "\<dots> \<longleftrightarrow> (\<exists>i::int. u = of_int i * (2*pi) + (arcsin (k/R) - \<psi>)
                                 \<or> u = of_int i * (2*pi) + (pi - arcsin (k/R) - \<psi>))"
        by (auto simp: Ints_def algebra_simps)
      finally
      show "u \<in> {u::real. lo \<le> u \<and> u \<le> hi \<and> a * cos u + b * sin u = k}
          \<longleftrightarrow> u \<in> {u::real. lo \<le> u \<and> u \<le> hi
                    \<and> (\<exists>i::int. u = of_int i * (2*pi) + (arcsin (k/R) - \<psi>))}
                \<union> {u::real. lo \<le> u \<and> u \<le> hi
                    \<and> (\<exists>i::int. u = of_int i * (2*pi) + (pi - arcsin (k/R) - \<psi>))}"
        by auto
    qed
    have tp: "(0::real) < 2*pi" using pi_gt_zero by simp
    show ?thesis unfolding eq
      by (rule finite_UnI[OF finite_affine_int_zeros[OF tp] finite_affine_int_zeros[OF tp]])
  next
    case False
    have empty: "{u::real. lo \<le> u \<and> u \<le> hi \<and> a * cos u + b * sin u = k} = {}"
    proof -
      have "a * cos u + b * sin u \<noteq> k" for u
      proof -
        have e1: "a * cos u + b * sin u = R * sin (u + \<psi>)" by (rule key)
        have "\<bar>R * sin (u + \<psi>)\<bar> \<le> R"
          using R0 by (simp add: abs_mult)
        moreover have "R < \<bar>k\<bar>" using False R0 by (auto simp: divide_simps abs_real_def split: if_splits)
        ultimately show ?thesis using e1 by auto
      qed
      thus ?thesis by blast
    qed
    show ?thesis unfolding empty by simp
  qed
qed


subsection \<open>The single irreducible curve-structure residual: the locus is LOCALLY a \<open>C\<^sup>1\<close> arc\<close>

text \<open>\<^bold>\<open>GENUINE analytic content, isolated as the SMALLEST precisely-scoped \<open>sorry\<close>.\<close>

  By the sorry-free reductions above, the collinear locus is the bounded-box zero set
  of the SINGLE separable-trigonometric equation
  \<open>crossA(\<omega>\<^sub>1)cos\<omega>\<^sub>2 + crossB(\<omega>\<^sub>1)sin\<omega>\<^sub>2 + crossG(\<omega>\<^sub>1) = 0\<close> (@{thm crossTheta_separable}),
  a genuine 1-dimensional real-analytic curve.  The only remaining content is the
  LOCAL curve-structure step: around every locus point there is a relatively-open
  neighbourhood whose intersection with the locus is covered by FINITELY MANY genuine
  \<open>C\<^sup>1\<close> arcs lying in the box.  This is exactly the implicit-function-theorem graph
  (solving \<open>\<omega>\<^sub>2 = \<psi>(\<omega>\<^sub>1)\<close> off \<open>\<partial>\<omega>\<^sub>2\<Theta>=0\<close> via the \<open>arccos\<close>/\<open>arcsin\<close> branch, or
  \<open>\<omega>\<^sub>1 = \<chi>(\<omega>\<^sub>2)\<close> off \<open>\<partial>\<omega>\<^sub>1\<Theta>=0\<close>; the finitely many singular points
  --- where both partials vanish, cut by the additional equations confined by
  @{thm finite_affine_int_zeros} / @{thm finite_cos_zeros_interval} /
  @{thm finite_phase_zeros_interval} --- are degenerate (point) arcs).

  \<^bold>\<open>SOUNDNESS of the residual statement.\<close>  We require FINITELY MANY arcs per point, NOT
  a single arc: at a self-crossing (singular) point of the curve two distinct branches
  meet, so no single \<open>C\<^sup>1\<close> arc can cover the local locus --- demanding one arc would be
  an UNSOUND (false) statement.  A finite family is exactly the true real-analytic
  local structure (finitely many branches).

  HOL-Analysis 2025-2 has NO implicit-function theorem and NO real-analytic
  curve-structure theory (only the INVERSE function theorem
  @{thm inverse_function_theorem} and complex \<open>analytic_on\<close>), so this local graph
  must be built; it is isolated here as the one residual.  \<^bold>\<open>SOUNDNESS of the arcs.\<close>
  Each arc is a genuine @{const analytic_arc} (a \<open>C\<^sup>1\<close> image of a compact interval),
  NOT a mere @{const continuous_on} image --- the downstream
  @{text analytic_arc_negligible} gate needs negligibility, which a space-filling
  (Peano) continuous curve would violate.  NOT a splice freebie.\<close>

subsection \<open>The Fréchet derivative of \<open>crossTheta\<close> (explicit partials)\<close>

text \<open>\<open>crossTheta\<close> is \<open>C\<^sup>1\<close> (indeed \<open>C\<^sup>\<infinity>\<close>): from the separable form it is a trig
  polynomial in the two continuous components \<open>\<omega>$1, \<omega>$2\<close>.  We record the Fréchet
  derivative with its two explicit partial coefficients \<open>\<partial>\<^sub>1, \<partial>\<^sub>2\<close>; the case split in
  @{text locus_locally_C1_arc} (regular vs singular point) and the finiteness of the
  singular set both read off these partials.\<close>

lemma has_derivative_crossTheta:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2"
  defines "Ac \<equiv> (kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)"
      and "Bc \<equiv> (ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  shows "((\<lambda>z. crossTheta \<omega>0 \<omega>s z) has_derivative
     (\<lambda>h. ( (Bc * kz \<omega>s + ky \<omega>s) * sin (\<omega>$1) * cos (\<omega>$2)
            - (Ac * kz \<omega>s + kx \<omega>s) * sin (\<omega>$1) * sin (\<omega>$2)
            + (Ac * ky \<omega>s - Bc * kx \<omega>s) * cos (\<omega>$1) ) * (h$1)
        + ( - (Bc - (Bc * kz \<omega>s + ky \<omega>s) * cos (\<omega>$1)) * sin (\<omega>$2)
            + (- Ac + (Ac * kz \<omega>s + kx \<omega>s) * cos (\<omega>$1)) * cos (\<omega>$2) ) * (h$2)
       )) (at \<omega>)"
proof -
  have sep: "crossTheta \<omega>0 \<omega>s z
       = (Bc - (Bc * kz \<omega>s + ky \<omega>s) * cos (z$1)) * cos (z$2)
       + (- Ac + (Ac * kz \<omega>s + kx \<omega>s) * cos (z$1)) * sin (z$2)
       + (Ac * ky \<omega>s - Bc * kx \<omega>s) * sin (z$1)" for z
    unfolding Ac_def Bc_def
    by (subst crossTheta_separable) (simp add: crossA_def crossB_def crossG_def)
  have d1: "((\<lambda>z::real^2. z$1) has_derivative (\<lambda>h. h$1)) (at \<omega>)"
    by (simp add: bounded_linear_vec_nth bounded_linear_imp_has_derivative)
  have d2: "((\<lambda>z::real^2. z$2) has_derivative (\<lambda>h. h$2)) (at \<omega>)"
    by (simp add: bounded_linear_vec_nth bounded_linear_imp_has_derivative)
  show ?thesis
    unfolding sep
    by (rule derivative_eq_intros refl d1 d2 | simp add: algebra_simps)+
qed

lemma locus_locally_C1_arc:
  fixes ctr :: "real^2" and \<delta> :: real and \<omega>' :: "real^2"
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    and win: "\<omega>' \<in> {\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0}"
  obtains r \<A> where "0 < r" "finite \<A>"
      "\<forall>\<gamma>\<in>\<A>. analytic_arc \<gamma> \<and> \<gamma> \<subseteq> OmegaPF ctr \<delta>"
      "{\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0} \<inter> ball \<omega>' r \<subseteq> \<Union>\<A>"
  \<comment> \<open>GENUINE analytic residual (the single \<open>sorry\<close>): the locus is locally covered by
      finitely many \<open>C\<^sup>1\<close> arcs (IFT branches of the separable equation
      @{thm crossTheta_separable}).  All assembly around it --- continuity, compactness,
      finite subcover, finite union, box containment --- is sorry-free below.\<close>
  sorry


subsection \<open>ASSEMBLY (sorry-free from the local-arc residual + compactness)\<close>

text \<open>Heine--Borel: the compact locus is covered by the per-point balls of
  @{thm locus_locally_C1_arc}; a finite subcover yields finitely many \<open>C\<^sup>1\<close> arcs whose
  union contains the locus and which all lie in the box.  Hence
  @{const finitely_arc_coverable}.\<close>

lemma collinear_locus_crossTheta_finite_arc_cover:
  fixes ctr :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
  shows "finitely_arc_coverable {\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0} ctr \<delta>"
proof -
  define L :: "(real^2) set" where "L = {\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0}"
  have compL: "compact L" unfolding L_def by (rule compact_crossTheta_locus)
  \<comment> \<open>Per-locus-point: a radius \<open>R \<omega>'\<close> and a FINITE SET \<open>AS \<omega>'\<close> of \<open>C\<^sup>1\<close> arcs covering
      the local locus, extracted from the local-arc residual via @{const Eps}.\<close>
  define good :: "real^2 \<Rightarrow> real \<Rightarrow> ((real^2) set) set \<Rightarrow> bool" where
    "good \<omega>' r \<A> \<longleftrightarrow> 0 < r \<and> finite \<A>
        \<and> (\<forall>\<gamma>\<in>\<A>. analytic_arc \<gamma> \<and> \<gamma> \<subseteq> OmegaPF ctr \<delta>)
        \<and> L \<inter> ball \<omega>' r \<subseteq> \<Union>\<A>" for \<omega>' r \<A>
  define R :: "real^2 \<Rightarrow> real" where
    "R = (\<lambda>\<omega>'. SOME r. \<exists>\<A>. good \<omega>' r \<A>)" for \<omega>' :: "real^2"
  define AS :: "real^2 \<Rightarrow> ((real^2) set) set" where
    "AS = (\<lambda>\<omega>'. SOME \<A>. good \<omega>' (R \<omega>') \<A>)" for \<omega>' :: "real^2"
  have spec: "good \<omega>' (R \<omega>') (AS \<omega>')" if w: "\<omega>' \<in> L" for \<omega>' :: "real^2"
  proof -
    have wlocus: "\<omega>' \<in> {\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0}"
      using w unfolding L_def .
    obtain r \<A> where r0: "0 < r" and finA: "finite \<A>"
        and ag: "\<forall>\<gamma>\<in>\<A>. analytic_arc \<gamma> \<and> \<gamma> \<subseteq> OmegaPF ctr \<delta>"
        and cov: "{\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0} \<inter> ball \<omega>' r
                    \<subseteq> \<Union>\<A>"
      using d0 pf hsep kdiff wlocus by (rule locus_locally_C1_arc)
    \<comment> \<open>The local family is already a finite SET of arcs.\<close>
    have g0: "good \<omega>' r \<A>"
      unfolding good_def using r0 finA ag cov unfolding L_def by auto
    have exr: "\<exists>r. \<exists>\<A>. good \<omega>' r \<A>" using g0 by blast
    have Rspec: "\<exists>\<A>. good \<omega>' (R \<omega>') \<A>"
      unfolding R_def by (rule someI_ex[OF exr])
    show "good \<omega>' (R \<omega>') (AS \<omega>')"
      unfolding AS_def by (rule someI_ex[OF Rspec])
  qed
  \<comment> \<open>The balls form an open cover of the compact locus.\<close>
  have cover: "L \<subseteq> (\<Union>\<omega>'\<in>L. ball \<omega>' (R \<omega>'))"
  proof
    fix \<omega>' assume w: "\<omega>' \<in> L"
    have "0 < R \<omega>'" using spec[OF w] unfolding good_def by blast
    hence "\<omega>' \<in> ball \<omega>' (R \<omega>')" by simp
    thus "\<omega>' \<in> (\<Union>\<omega>'\<in>L. ball \<omega>' (R \<omega>'))" using w by blast
  qed
  obtain F where Fsub: "F \<subseteq> L" and Ffin: "finite F"
      and Fcov: "L \<subseteq> (\<Union>\<omega>'\<in>F. ball \<omega>' (R \<omega>'))"
    by (rule compactE_image[OF compL, where f = "\<lambda>\<omega>'. ball \<omega>' (R \<omega>')" and C = L])
       (use cover in auto)
  \<comment> \<open>The total arc collection: union over the finite subcover of the per-point
      finite families.  A finite set of \<open>C\<^sup>1\<close> arcs.\<close>
  define \<A>tot :: "((real^2) set) set" where "\<A>tot = (\<Union>\<omega>'\<in>F. AS \<omega>')"
  have finA: "finite \<A>tot"
    unfolding \<A>tot_def
    by (rule finite_UN_I[OF Ffin]) (use Fsub spec in \<open>auto simp: good_def\<close>)
  have Aarc: "analytic_arc \<gamma> \<and> \<gamma> \<subseteq> OmegaPF ctr \<delta>" if g: "\<gamma> \<in> \<A>tot" for \<gamma>
  proof -
    from g obtain \<omega>' where w: "\<omega>' \<in> F" and gin: "\<gamma> \<in> AS \<omega>'"
      unfolding \<A>tot_def by blast
    have wL: "\<omega>' \<in> L" using Fsub w by blast
    show ?thesis using spec[OF wL] gin unfolding good_def by blast
  qed
  have AcovL: "L \<subseteq> \<Union>\<A>tot"
  proof
    fix \<omega> assume wL: "\<omega> \<in> L"
    from Fcov wL obtain \<omega>' where w: "\<omega>' \<in> F" and inb: "\<omega> \<in> ball \<omega>' (R \<omega>')" by blast
    have wL': "\<omega>' \<in> L" using Fsub w by blast
    have "\<omega> \<in> L \<inter> ball \<omega>' (R \<omega>')" using wL inb by blast
    hence "\<omega> \<in> \<Union>(AS \<omega>')" using spec[OF wL'] unfolding good_def by blast
    then obtain \<gamma> where "\<gamma> \<in> AS \<omega>'" and "\<omega> \<in> \<gamma>" by blast
    moreover have "AS \<omega>' \<subseteq> \<A>tot" unfolding \<A>tot_def using w by blast
    ultimately show "\<omega> \<in> \<Union>\<A>tot" by blast
  qed
  \<comment> \<open>Reindex the finite arc set by a finite \<open>nat\<close> set.\<close>
  obtain g :: "(real^2) set \<Rightarrow> nat" where ginj: "inj_on g \<A>tot"
    using finite_imp_inj_to_nat_seg[OF finA] by blast
  define I :: "nat set" where "I = g ` \<A>tot"
  have finI: "finite I" unfolding I_def using finA by simp
  define arc :: "nat \<Rightarrow> (real^2) set" where
    "arc = (\<lambda>i. the_inv_into \<A>tot g i)" for i :: nat
  have arc_in: "arc i \<in> \<A>tot" if iI: "i \<in> I" for i
  proof -
    from iI obtain \<gamma> where g: "\<gamma> \<in> \<A>tot" and gi: "g \<gamma> = i" unfolding I_def by blast
    have "the_inv_into \<A>tot g i = \<gamma>" using ginj g gi by (metis the_inv_into_f_f)
    thus ?thesis unfolding arc_def using g by simp
  qed
  have arcprop: "analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>" if iI: "i \<in> I" for i
    using Aarc[OF arc_in[OF iI]] .
  have Lcov: "L \<subseteq> (\<Union>i\<in>I. arc i)"
  proof
    fix \<omega> assume wL: "\<omega> \<in> L"
    then obtain \<gamma> where g: "\<gamma> \<in> \<A>tot" and inw: "\<omega> \<in> \<gamma>" using AcovL by blast
    have "the_inv_into \<A>tot g (g \<gamma>) = \<gamma>" using ginj g by (simp add: the_inv_into_f_f)
    hence "\<omega> \<in> arc (g \<gamma>)" unfolding arc_def using inw by simp
    moreover have "g \<gamma> \<in> I" unfolding I_def using g by blast
    ultimately show "\<omega> \<in> (\<Union>i\<in>I. arc i)" by blast
  qed
  have allarc: "\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>"
    using arcprop by blast
  show ?thesis
    unfolding finitely_arc_coverable_def L_def[symmetric]
    by (intro exI[of _ I] exI[of _ arc] conjI finI Lcov allarc)
qed

lemma collinear_locus_finite_arc_cover:
  fixes ctr :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
  shows "finitely_arc_coverable {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>} ctr \<delta>"
  unfolding collinear_locus_eq_crossTheta_zero
  by (rule collinear_locus_crossTheta_finite_arc_cover[OF d0 pf hsep kdiff])

end
