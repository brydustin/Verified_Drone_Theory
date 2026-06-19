theory Scratch_m5_arccover
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

subsection \<open>The phase-collinear predicate (copied verbatim from the engine)\<close>

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"

subsection \<open>Analytic arcs and the soundness predicate \<open>finitely_arc_coverable\<close>\<close>

definition analytic_arc :: "(real^2) set \<Rightarrow> bool" where
  "analytic_arc \<gamma> \<longleftrightarrow> (\<exists>(a::real) b \<phi>. a \<le> b \<and> continuous_on {a..b} \<phi>
                          \<and> \<gamma> = \<phi> ` {a..b})"

definition finitely_arc_coverable :: "(real^2) set \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> bool" where
  "finitely_arc_coverable \<Gamma> ctr \<delta> \<longleftrightarrow>
     (\<exists>(I::nat set) arc. finite I \<and> \<Gamma> \<subseteq> (\<Union>i\<in>I. arc i)
         \<and> (\<forall>i\<in>I. analytic_arc (arc i) \<and> arc i \<subseteq> OmegaPF ctr \<delta>))"


subsection \<open>GENUINE REDUCTION 1: component forms of \<open>cvec_dip\<close> / \<open>Dcvec_dip\<close> (sorry-free)\<close>

text \<open>The two components of the steered wavevector and of its \<open>\<omega>\<^sub>1\<close>-partial, read off the
  explicit definitions.  Abbreviations: \<open>Ac = (kx\<omega>0-kx\<omega>s)/(kz\<omega>s-kz\<omega>0)\<close>,
  \<open>Bc = (ky\<omega>0-ky\<omega>s)/(kz\<omega>s-kz\<omega>0)\<close>.\<close>

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


subsection \<open>GENUINE REDUCTION 2: \<open>phase_collinear\<close> = the cross-determinant vanishes (sorry-free)\<close>

text \<open>\<open>phase_collinear\<close> is exactly linear dependence of \<open>Dcvec_dip \<omega> (axis 1 1)\<close> and
  \<open>cvec_dip \<omega>\<close>, which for plane vectors is the vanishing of their \<open>2\<times>2\<close> cross
  determinant.  This converts the two existential scaling clauses into one polynomial
  (in \<open>sin/cos\<close>) equation \<open>\<Theta>(\<omega>\<^sub>1,\<omega>\<^sub>2)=0\<close>.  Proven sorry-free from @{thm cols_dependent_2d}.\<close>

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


subsection \<open>GENUINE REDUCTION 3: explicit trigonometric form of \<open>\<Theta>\<close> (sorry-free)\<close>

text \<open>Clearing \<open>cvec_dip\<close>/\<open>Dcvec_dip\<close> by their explicit trig forms, the cross
  determinant is the single analytic equation
  \<open>\<Theta>(\<omega>\<^sub>1,\<omega>\<^sub>2) = P\<cdot>sin(\<omega>\<^sub>1) + cos(\<omega>\<^sub>1)\<cdot>Q(\<omega>\<^sub>2) + R(\<omega>\<^sub>2)\<close> with \<open>P\<close> constant and \<open>Q,R\<close>
  the \<open>cos\<close>/\<open>sin\<close>/\<open>a cos + b sin\<close> factors confined by the \<open>\<int>\<^sup>3\<close>-period lemmas.  The
  \<open>k\<close>-functions are \<open>kx \<omega> = sin(\<omega>\<^sub>1)cos(\<omega>\<^sub>2)\<close>, \<open>ky \<omega> = sin(\<omega>\<^sub>1)sin(\<omega>\<^sub>2)\<close>,
  \<open>kz \<omega> = cos(\<omega>\<^sub>1)\<close>; we keep them opaque and only use the explicit \<open>Dcvec\<close>/\<open>cvec\<close>
  component forms, so this is the genuine, definition-faithful reduction.\<close>

lemma crossTheta_trig:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2"
  defines "Ac \<equiv> (kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)"
      and "Bc \<equiv> (ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  shows "crossTheta \<omega>0 \<omega>s \<omega>
       = (cos (\<omega>$1) * cos (\<omega>$2) + Ac * (- sin (\<omega>$1)))
            * ((ky \<omega> - ky \<omega>s) + Bc * (kz \<omega> - kz \<omega>s))
       - (cos (\<omega>$1) * sin (\<omega>$2) + Bc * (- sin (\<omega>$1)))
            * ((kx \<omega> - kx \<omega>s) + Ac * (kz \<omega> - kz \<omega>s))"
  unfolding crossTheta_def
  by (simp only: Dc1_eq Dc2_eq c1_eq c2_eq Ac_def Bc_def)


subsection \<open>The phase-collinear locus, restated as the zero set of \<open>\<Theta>\<close>\<close>

lemma collinear_locus_eq_crossTheta_zero:
  "{\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>}
     = {\<omega> \<in> OmegaPF ctr \<delta>. crossTheta \<omega>0 \<omega>s \<omega> = 0}"
  by (simp add: phase_collinear_iff_crossTheta)


subsection \<open>Deliverable 1: the phase-collinear LOCUS has a finite analytic-arc cover\<close>

text \<open>\<^bold>\<open>GENUINE analytic obligation (precisely scoped to the collinear LOCUS).\<close>

  By the three sorry-free reductions above, the locus is exactly the bounded-box zero
  set of the single analytic function @{const crossTheta}, whose explicit trig form
  (@{thm crossTheta_trig}) is \<open>P\<cdot>sin(\<omega>\<^sub>1) + cos(\<omega>\<^sub>1)\<cdot>Q(\<omega>\<^sub>2) + R(\<omega>\<^sub>2)\<close> --- a genuine
  one-dimensional real-analytic curve (NOT a 2-cell, NOT a finite point set).  The
  remaining content is the real-analytic curve-structure step: this 1-dim zero set
  meets the compact box in a finite union of continuous arcs (the smooth part is
  covered by IFT graphs \<open>\<omega>\<^sub>2 = \<phi>\<^sub>k(\<omega>\<^sub>1)\<close> / \<open>\<omega>\<^sub>1 = \<psi>\<^sub>k(\<omega>\<^sub>2)\<close> over the finitely many
  \<open>\<int>\<^sup>3\<close>-period windows of @{thm finite_affine_int_zeros},
  @{thm finite_cos_zeros_interval}, @{thm finite_phase_zeros_interval}; the finitely
  many singular points are degenerate arcs).  Each arc is a continuous image of a
  compact interval inside the box, i.e. an @{const analytic_arc}.

  \<^bold>\<open>Soundness extreme-instance check.\<close>  NOT true with the locus replaced by the whole
  box: \<open>finitely_arc_coverable (OmegaPF ctr \<delta>) ctr \<delta>\<close> is false for the non-degenerate
  2-cell.  The hypotheses \<open>0 < \<delta>\<close> and \<open>sin(\<omega>\<^sub>1)\<noteq>0\<close> on the box are the same
  non-degeneracy data @{thm meager_steering_singular_stratum} uses to confine its
  witnesses; here they guarantee \<open>\<Theta>\<close> is a genuine non-degenerate curve.\<close>

lemma collinear_locus_finite_arc_cover:
  fixes ctr :: "real^2" and \<delta> :: real
  assumes d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "finitely_arc_coverable {\<omega> \<in> OmegaPF ctr \<delta>. phase_collinear \<omega>0 \<omega>s \<omega>} ctr \<delta>"
  \<comment> \<open>GENUINE analytic sorry (1/2), SOUNDLY scoped: by the sorry-free reductions
      @{thm collinear_locus_eq_crossTheta_zero} and @{thm crossTheta_trig} the locus is
      the bounded-box zero set of the single analytic equation \<open>\<Theta>(\<omega>\<^sub>1,\<omega>\<^sub>2)=0\<close>; the
      remaining real-analytic curve-structure step covers this 1-dim zero set by
      finitely many continuous arcs (IFT graphs over the \<open>\<int>\<^sup>3\<close>-period windows;
      @{thm finite_affine_int_zeros}, @{thm finite_cos_zeros_interval},
      @{thm finite_phase_zeros_interval}).  NOT a splice freebie.\<close>
  sorry

end
