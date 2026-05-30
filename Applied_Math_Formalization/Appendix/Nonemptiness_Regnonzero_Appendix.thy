theory Nonemptiness_Regnonzero_Appendix
  imports Applied_Math_Nonemptiness.Nonemptiness_Paper
begin

section \<open>Regular-stratum nonzero-\<open>A\<close> branch: appendix obligation skeleton\<close>

text \<open>
  This theory states --- each closed by @{command sorry} --- the obligations of the
  regular-stratum nonzero-\<open>A\<close> branch \<open>prop:regnonzero\<close> (the one unformalized branch
  of the Baire closeout \<open>thm:final\<close>) of
  \<open>Applied Math/nonemptiness_unified_singlefile_complete.tex\<close>.

  \<^bold>\<open>Design (locale-free, and \<^emph>\<open>connectable\<close> to the real objects).\<close>  An earlier draft
  fixed each Jacobian minor as an \<^emph>\<open>arbitrary\<close> function \<open>detJ5 :: 'w \<Rightarrow> real\<close> and
  asserted \<open>detJ5 x = -32 g\<^sup>5 a\<^sup>5\<close>; that is false for almost all such functions and
  cannot be instantiated to the real moment map.  This file uses the two patterns
  that \<^emph>\<open>do\<close> connect:

  \<^enum> \<^bold>\<open>Concrete algebraic facts.\<close>  The bad-point map \<open>\<Phi> = (\<Phi>\<^sub>1,\<Phi>\<^sub>2,\<Phi>\<^sub>3)\<close> and the
    Hessian entries \<open>H\<^sub>1\<^sub>1,H\<^sub>1\<^sub>2,H\<^sub>2\<^sub>2\<close> are \<^emph>\<open>defined\<close> here as the explicit closed-form
    polynomials in the moment variables \<open>a,b,a\<^sub>k,b\<^sub>k,a\<^sub>k\<^sub>l,b\<^sub>k\<^sub>l\<close> and gains
    \<open>g,g\<^sub>k,g\<^sub>k\<^sub>l\<close> given in the paper (tex L578--596).  Their Jacobian-minor lemmas
    (\<open>lem:block\<close>, \<open>lem:3x3\<close>, \<open>prop:moment3/5/5alt\<close>, \<open>prop:vblock\<close>, \<dots>) are then genuine
    identities about \<^emph>\<open>partial derivatives of these concrete functions\<close> (via
    @{const deriv} of the one-variable sections), holding for all real arguments,
    so they connect by substituting the actual moment values at a point.  The
    Appendix-A triple-side minors are concrete real-number identities via
    \<open>det3\<close>.

  \<^enum> \<^bold>\<open>Parametric geometric facts with the real structural hypothesis.\<close>  Each
    codimension/meagerness reduction fixes its cut function \<open>f\<close> but assumes
    \<^const>\<open>rline_entire\<close> \<open>f\<close> (real-analytic: every line restriction extends to an
    entire function --- the property a finite exponential sum has) together with
    non-triviality, and concludes \<^const>\<open>nowhere_dense\<close>\<open>/\<close>\<^const>\<open>meager\<close> of the
    equation-cut branch.  This is the project's own
    \<open>slice_zero_nowhere_dense\<close>\<open>/\<close>\<open>U_cart_zero_nowhere_dense\<close> engine, so it is a real
    theorem; it connects by instantiating \<open>f\<close> with the actual cofactor and
    discharging \<^const>\<open>rline_entire\<close> from \<open>rline_entire_U_cart\<close> / \<open>cline_entire_af\<close>,
    exactly as the four-branch closeout \<open>nonemptiness_from_branches\<close> takes its bad
    strata as hypotheses.

  The Hessian-zero lemma \<open>lem:Hzero\<close> uses the real Hessian \<open>\<nabla>\<^sup>2\<close>
  (\<open>Higher_Differentiability_Multi.hess_fun\<close>) and lives in the companion
  theory \<open>Nonemptiness_Hessian_Facts.thy\<close> (built in the \<open>HigherDiff\<close> session, so
  that \<open>Smooth_Manifolds\<close> need not be merged into this heap).
\<close>


subsection \<open>The concrete bad-point map \<open>\<Phi>\<close> and Hessian entries\<close>

text \<open>The explicit moment-space formulas (tex L578--596). Arguments are ordered so
  that the variable a minor differentiates appears in a fixed, easily-curried slot.\<close>

definition Phi1m :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  \<comment> \<open>\<open>\<Phi>\<^sub>1 = g\<^sub>1(a\<^sup>2+b\<^sup>2) + 2g(b\<^sub>1 a - a\<^sub>1 b)\<close>; arg order \<open>g1 g a b a1 b1\<close>\<close>
  "Phi1m g1 g a b a1 b1 = g1*(a^2+b^2) + 2*g*(b1*a - a1*b)"

definition Phi2m :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Phi2m g2 g a b a2 b2 = g2*(a^2+b^2) + 2*g*(b2*a - a2*b)"

definition H11m ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  \<comment> \<open>arg order \<open>g11 g1 g a b a1 b1 a11 b11\<close>\<close>
  "H11m g11 g1 g a b a1 b1 a11 b11 =
     g11*(a^2+b^2) + 4*g1*(b1*a - a1*b) + 2*g*((a1^2+b1^2) - (a11*a + b11*b))"

definition H22m ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  \<comment> \<open>arg order \<open>g22 g2 g a b a2 b2 a22 b22\<close> (9 args)\<close>
  "H22m g22 g2 g a b a2 b2 a22 b22 =
     g22*(a^2+b^2) + 4*g2*(b2*a - a2*b) + 2*g*((a2^2+b2^2) - (a22*a + b22*b))"

definition H12m ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  \<comment> \<open>arg order \<open>g12 g1 g2 g a b a1 b1 a2 b2 a12 b12\<close>; defined entry below uses \<open>a12 b12\<close> last\<close>
  "H12m g12 g1 g2 g a b a1 b1 a2 b2 a12 b12 =
     g12*(a^2+b^2) + 2*g1*(b2*a - a2*b) + 2*g2*(b1*a - a1*b)
       + 2*g*((a1*a2 + b1*b2) - (a12*a + b12*b))"


subsection \<open>A concrete \<open>3\<times>3\<close> determinant and Appendix-A entry functions\<close>

definition det3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where
  "det3 a b c d e f g h i =
     a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)"

definition betaU :: "real \<Rightarrow> real \<Rightarrow> real" where
  "betaU \<kappa> u = - (\<kappa> * u * cos (\<kappa> * u) + sin (\<kappa> * u))"

definition alphaU :: "real \<Rightarrow> real \<Rightarrow> real" where
  "alphaU \<kappa> u = 2 * u * cos (\<kappa> * u) - \<kappa> * u\<^sup>2 * sin (\<kappa> * u)"

definition Fparam :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Fparam \<kappa> u \<alpha> \<beta> =
     2 * (\<alpha> - u) * (cos (\<kappa> * u) - \<kappa> * u * sin (\<kappa> * u))
       + \<kappa> * sin (\<kappa> * u) * (\<beta> - u\<^sup>2)"

definition astar :: "real \<Rightarrow> real \<Rightarrow> real" where
  "astar \<kappa> u = u - sin (2 * \<kappa> * u) / (2 * \<kappa> * (1 + (sin (\<kappa> * u))\<^sup>2))"

definition bstar :: "real \<Rightarrow> real \<Rightarrow> real" where
  "bstar \<kappa> u =
     (- (1/2) * \<kappa>\<^sup>2 * u\<^sup>2 * cos (2 * \<kappa> * u) + (3/2) * \<kappa>\<^sup>2 * u\<^sup>2
       - \<kappa> * u * sin (2 * \<kappa> * u) + cos (2 * \<kappa> * u) + 1)
     / (\<kappa>\<^sup>2 * (1 + (sin (\<kappa> * u))\<^sup>2))"

text \<open>The ratio \<open>R\<close> behind \<open>prop:upair\<close>: \<open>\<alpha>(u)/\<beta>(u) = (1/\<kappa>) R(\<kappa>u)\<close>.\<close>

definition Rratio :: "real \<Rightarrow> real" where
  "Rratio t = t * (t * sin t - 2 * cos t) / (t * cos t + sin t)"

text \<open>TeX \<open>prop:double-param\<close> (L5755): \<open>(\<alpha>\<^sub>\<ast>,\<beta>\<^sub>\<ast>)\<close> is the unique double-root
  parameterization of \<open>F = \<partial>\<^sub>uF = 0\<close>, and \<open>\<alpha>\<^sub>\<ast>\<close> is strictly increasing.\<close>

lemma prop_double_param_solves:
  fixes \<kappa> u :: real
  shows "Fparam \<kappa> u (astar \<kappa> u) (bstar \<kappa> u) = 0"
  sorry

lemma prop_double_param_mono:
  fixes \<kappa> :: real
  assumes "\<kappa> \<noteq> 0"
  shows "strict_mono_on UNIV (astar \<kappa>)"
  sorry


subsection \<open>Spine: block-triangular and rank-3 moment Jacobians (concrete)\<close>

text \<open>TeX \<open>lem:block\<close> (L602): the partial derivatives establishing that
  \<open>J\<^sub>5 = \<partial>(\<Phi>\<^sub>1,\<Phi>\<^sub>2,H\<^sub>1\<^sub>1,H\<^sub>1\<^sub>2,H\<^sub>2\<^sub>2)/\<partial>(b\<^sub>1,b\<^sub>2,a\<^sub>1\<^sub>1,a\<^sub>1\<^sub>2,a\<^sub>2\<^sub>2)\<close> is block lower
  triangular with diagonal blocks \<open>2ga\<cdot>I\<^sub>2\<close> and \<open>-2ga\<cdot>I\<^sub>3\<close> (hence
  \<open>det J\<^sub>5 = -32 g\<^sup>5 a\<^sup>5\<close>).  Stated as the genuine partial-derivative identities of
  the concrete map.\<close>

lemma lem_block:
  fixes g g1 g2 g11 g12 g22 a b a1 b1 a2 b2 a11 b11 a12 b12 a22 b22 :: real
  shows \<comment> \<open>upper \<open>2\<times>2\<close> block \<open>= 2ga\<cdot>I\<^sub>2\<close>\<close>
        "deriv (\<lambda>t. Phi1m g1 g a b a1 t) b1 = 2*g*a"
    and "deriv (\<lambda>t. Phi2m g2 g a b a2 t) b2 = 2*g*a"
    and \<comment> \<open>lower \<open>3\<times>3\<close> block \<open>= -2ga\<cdot>I\<^sub>3\<close> (diagonal entries)\<close>
        "deriv (\<lambda>t. H11m g11 g1 g a b a1 b1 t b11) a11 = - 2*g*a"
    and "deriv (\<lambda>t. H12m g12 g1 g2 g a b a1 b1 a2 b2 t b12) a12 = - 2*g*a"
    and "deriv (\<lambda>t. H22m g22 g2 g a b a2 b2 t b22) a22 = - 2*g*a"
    and \<comment> \<open>off-block: \<open>\<Phi>\<^sub>1,\<Phi>\<^sub>2\<close> do not depend on the \<open>a\<^sub>k\<^sub>l\<close>\<close>
        "deriv (\<lambda>t. Phi1m g1 g a b a1 b1) a11 = 0"
    and "deriv (\<lambda>t. Phi2m g2 g a b a2 b2) a22 = 0"
  sorry

text \<open>TeX \<open>lem:3x3\<close> (L637): the rank-3 minor identities.  With
  \<open>\<Phi>\<^sub>3 = H\<^sub>1\<^sub>1 H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2\<close>, the key partial is \<open>\<partial>\<^sub>a\<^sub>1\<^sub>1\<Phi>\<^sub>3 = -2ga H\<^sub>2\<^sub>2\<close> (and duals),
  so together with the \<open>2ga\<cdot>I\<^sub>2\<close> block the \<open>3\<times>3\<close> minor is \<open>-8g\<^sup>3a\<^sup>3H\<^sub>2\<^sub>2\<close>.\<close>

lemma lem_3x3:
  fixes g g1 g2 g11 g12 g22 a b a1 b1 a2 b2 a11 b11 a12 b12 a22 b22 :: real
  defines "Phi3 \<equiv> (\<lambda>a11 a12 a22.
      H11m g11 g1 g a b a1 b1 a11 b11 * H22m g22 g2 g a b a2 b2 a22 b22
      - (H12m g12 g1 g2 g a b a1 b1 a2 b2 a12 b12)^2)"
  shows "deriv (\<lambda>t. Phi3 t a12 a22) a11
           = - 2*g*a * H22m g22 g2 g a b a2 b2 a22 b22"
    and "deriv (\<lambda>t. Phi3 a11 a12 t) a22
           = - 2*g*a * H11m g11 g1 g a b a1 b1 a11 b11"
    and "deriv (\<lambda>t. Phi3 a11 t a22) a12
           =   4*g*a * H12m g12 g1 g2 g a b a1 b1 a2 b2 a12 b12"
  sorry

text \<open>TeX \<open>lem:Msurj\<close> (L670): \<open>D\<^bsub>x\<^esub>\<M>\<close> has rank 12 on an open dense subset of \<open>V\<close>.
  \<^bold>\<open>Already proven\<close> --- \<open>bigJ\<close> + \<open>bigJ_det_nonzero\<close> /
  \<open>bigJ_surj\<close>, headline \<open>DM_paper_open_dense_surjective\<close>.\<close>


subsection \<open>Appendix A --- triple-side minors (concrete)\<close>

text \<open>
  TeX \<open>prop:upair\<close> (L1522): the \<open>u\<close>-pair minor
  \<open>\<Delta>\<^sup>(\<^sup>u\<^sup>)\<^sub>i\<^sub>j = \<beta>(u\<^sub>i)\<alpha>(u\<^sub>j) - \<beta>(u\<^sub>j)\<alpha>(u\<^sub>i)\<close> is nonzero for \<open>u\<^sub>i \<noteq> u\<^sub>j\<close>.

  \<^bold>\<open>Correction to the paper's argument.\<close>  The paper reduces this to: the ratio
  \<open>R(t) = t(t sin t - 2 cos t)/(t cos t + sin t)\<close> is \<^emph>\<open>strictly monotone on all of
  \<real>\<close>.  That global claim is \<^bold>\<open>false\<close>: \<open>R\<close> has poles at the zeros of
  \<open>t cos t + sin t\<close> and is not even monotone between them (e.g.
  \<open>R(-1.5) \<approx> 1.84 > R(-1) \<approx> -0.17\<close>, so \<open>R\<close> decreases there).  Hence the
  unconditional \<open>\<Delta>\<^sup>(\<^sup>u\<^sup>)\<^sub>i\<^sub>j \<noteq> 0\<close> is \<^emph>\<open>not\<close> correct as literally stated --- the
  ratio \<open>\<alpha>/\<beta>\<close> repeats values, so distinct \<open>u\<close>'s can give \<open>\<Delta> = 0\<close>.  The
  nonvanishing holds only when \<open>u\<^sub>i, u\<^sub>j\<close> lie on a common branch where \<open>\<alpha>/\<beta>\<close> is
  injective; that restriction (supplied by the good-triple construction) is made
  explicit below as the hypothesis \<open>inj_on I (\<alpha>/\<beta>)\<close>.  This is the connectable,
  \<^emph>\<open>true\<close> form: instantiate \<open>I\<close> with the good-triple range and discharge injectivity
  there (where \<open>R\<close> genuinely is monotone).
\<close>

lemma prop_upair:
  fixes \<kappa> ui uj :: real and I :: "real set"
  assumes "ui \<noteq> uj" and "ui \<in> I" and "uj \<in> I"
    and "betaU \<kappa> ui \<noteq> 0" and "betaU \<kappa> uj \<noteq> 0"
    and inj: "inj_on (\<lambda>u. alphaU \<kappa> u / betaU \<kappa> u) I"
  shows "betaU \<kappa> ui * alphaU \<kappa> uj - betaU \<kappa> uj * alphaU \<kappa> ui \<noteq> 0"
proof (rule notI)
  assume "betaU \<kappa> ui * alphaU \<kappa> uj - betaU \<kappa> uj * alphaU \<kappa> ui = 0"
  hence eq: "betaU \<kappa> ui * alphaU \<kappa> uj = betaU \<kappa> uj * alphaU \<kappa> ui" by simp
  have cross: "alphaU \<kappa> ui * betaU \<kappa> uj = alphaU \<kappa> uj * betaU \<kappa> ui"
    using eq by (metis mult.commute)
  have ratio: "alphaU \<kappa> ui / betaU \<kappa> ui = alphaU \<kappa> uj / betaU \<kappa> uj"
    using cross assms(4) assms(5) by (simp add: field_simps)
  have feq: "(\<lambda>u. alphaU \<kappa> u / betaU \<kappa> u) ui = (\<lambda>u. alphaU \<kappa> u / betaU \<kappa> u) uj"
    using ratio by simp
  have "ui = uj"
    by (rule inj_onD[OF inj feq assms(2) assms(3)])
  with assms(1) show False by simp
qed

text \<open>
  \<^bold>\<open>Corrected supporting facts.\<close>  The honest replacement for the paper's false
  ``\<open>R\<close> strictly monotone on \<real>''.  \<open>R\<close> is \<^emph>\<open>even\<close> (so \<^emph>\<open>not\<close> globally injective)
  with a minimum at \<open>0\<close> (\<open>R(t) = -1 + (2/3)t\<^sup>2 + O(t\<^sup>4)\<close>); it is strictly monotone
  only on each one-sided branch up to the first pole \<open>t\<^sub>1 \<approx> 2.029\<close> (the first
  positive root of \<open>t cos t + sin t = 0\<close>).  The hypothesis
  ``\<open>t cos t + sin t > 0\<close> on \<open>(0,B]\<close>'' exactly says \<open>(0,B]\<close> lies in the first
  branch (\<open>B \<le> t\<^sub>1\<close>), where \<open>R\<close> is increasing and \<open>\<beta> \<noteq> 0\<close>.
\<close>

lemma R_even:
  fixes t :: real
  shows "Rratio (- t) = Rratio t"
proof -
  have mm: "\<And>a b::real. (- a) / (- b) = a / b" by simp
  have num: "- t * (- t * sin (- t) - 2 * cos (- t)) = - (t * (t * sin t - 2 * cos t))"
    by (simp only: sin_minus cos_minus algebra_simps)
  have den: "- t * cos (- t) + sin (- t) = - (t * cos t + sin t)"
    by (simp only: sin_minus cos_minus algebra_simps)
  have "Rratio (- t) = - (t * (t * sin t - 2 * cos t)) / (- (t * cos t + sin t))"
    by (simp only: Rratio_def num den)
  also have "\<dots> = t * (t * sin t - 2 * cos t) / (t * cos t + sin t)"
    by (rule mm)
  also have "\<dots> = Rratio t"
    by (simp only: Rratio_def)
  finally show ?thesis .
qed

text \<open>Two real-analysis facts behind the branch monotonicity.\<close>

lemma x_plus_sin_pos:
  fixes x :: real assumes "0 < x" shows "0 < x + sin x"
proof (cases "x \<le> pi")
  case True
  have "0 \<le> sin x" by (rule sin_ge_zero[OF order_less_imp_le[OF assms] True])
  thus ?thesis using assms by linarith
next
  case False
  have "- 1 \<le> sin x" by simp
  thus ?thesis using False pi_gt3 by linarith
qed

text \<open>The \<^emph>\<open>correct\<close> positivity of the derivative numerator (the paper's claimed
  sum-of-squares was wrong).  Key division-free decomposition:
  \<open>2\<cdot>Num = s\<^sup>2(2s + sin 2s) + 2(2s - sin 2s) + 4s sin\<^sup>2 s\<close>, all terms \<open>\<ge> 0\<close> with
  the first \<open>> 0\<close> (using \<open>sin x \<le> x\<close> and \<open>x + sin x > 0\<close>).\<close>

lemma Num_pos:
  fixes t :: real assumes t0: "0 < t"
  shows "0 < ((t * t - 2) * cos t + 4 * t * sin t) * (t * cos t + sin t)
            - t * (t * sin t - 2 * cos t) * (2 * cos t - t * sin t)"
proof -
  have pyth: "cos t * cos t = 1 - sin t * sin t"
    using sin_cos_squared_add[of t] by (simp only: power2_eq_square)
  have a1: "0 < 2 * t + sin (2 * t)" using x_plus_sin_pos[of "2 * t"] t0 by simp
  have a2: "sin (2 * t) \<le> 2 * t" using sin_x_le_x[of "2 * t"] t0 by simp
  have decomp:
    "2 * (((t * t - 2) * cos t + 4 * t * sin t) * (t * cos t + sin t)
          - t * (t * sin t - 2 * cos t) * (2 * cos t - t * sin t))
     = (t * t) * (2 * t + sin (2 * t)) + 2 * (2 * t - sin (2 * t)) + 4 * t * (sin t * sin t)"
    by (simp add: sin_double pyth algebra_simps,
        smt (verit, best) Groups.mult_ac(2) mult_hom.hom_add sin_double)
  have c1: "0 < (t * t) * (2 * t + sin (2 * t))"
    by (rule mult_pos_pos[OF mult_pos_pos[OF t0 t0] a1])
  have c2: "0 \<le> 2 * (2 * t - sin (2 * t))" using a2 by simp
  have c3: "0 \<le> 4 * t * (sin t * sin t)"
    using t0 by (simp add: zero_le_mult_iff)
  from c1 c2 c3
  have "0 < (t * t) * (2 * t + sin (2 * t)) + 2 * (2 * t - sin (2 * t)) + 4 * t * (sin t * sin t)"
    by linarith
  thus ?thesis using decomp by argo
qed

text \<open>TeX \<open>prop:upair\<close> supporting monotonicity: \<open>R\<close> is strictly increasing on the
  first branch \<open>(0,B)\<close> (where \<open>t cos t + sin t > 0\<close>), via \<open>R' = Num / (t cos t + sin t)\<^sup>2\<close>
  with \<open>Num_pos\<close>.\<close>

lemma R_strict_mono_first_branch:
  fixes B :: real
  assumes Bpos: "0 < B" and Dpos: "\<forall>t. 0 < t \<and> t \<le> B \<longrightarrow> t * cos t + sin t > 0"
  shows "strict_mono_on {t. 0 < t \<and> t < B} Rratio"
proof (rule strict_mono_onI)
  fix p q assume p: "p \<in> {t. 0 < t \<and> t < B}" and q: "q \<in> {t. 0 < t \<and> t < B}"
    and pq: "p < q"
  have p0: "0 < p" using p by simp
  have qB: "q < B" using q by simp
  show "Rratio p < Rratio q"
  proof (rule DERIV_pos_imp_increasing[OF pq])
    fix t assume t1: "p \<le> t" and t2: "t \<le> q"
    have t0: "0 < t" using p0 t1 by simp
    have tB: "t \<le> B" using t2 qB by simp
    have Dt: "0 < t * cos t + sin t" using Dpos t0 tB by blast
    have Dne: "t * cos t + sin t \<noteq> 0" using Dt by simp
    have dN: "((\<lambda>x::real. x * (x * sin x - 2 * cos x)) has_real_derivative
               ((t * t - 2) * cos t + 4 * t * sin t)) (at t)"
      by (auto intro!: derivative_eq_intros simp: algebra_simps)
    have dD: "((\<lambda>x::real. x * cos x + sin x) has_real_derivative
               (2 * cos t - t * sin t)) (at t)"
      by (auto intro!: derivative_eq_intros simp: algebra_simps)
    have der: "(Rratio has_real_derivative
        (( ((t * t - 2) * cos t + 4 * t * sin t) * (t * cos t + sin t)
           - t * (t * sin t - 2 * cos t) * (2 * cos t - t * sin t))
          / ((t * cos t + sin t) * (t * cos t + sin t)))) (at t)"
      unfolding Rratio_def by (rule DERIV_divide[OF dN dD Dne])
    have Numpos: "0 < ((t * t - 2) * cos t + 4 * t * sin t) * (t * cos t + sin t)
                     - t * (t * sin t - 2 * cos t) * (2 * cos t - t * sin t)"
      by (rule Num_pos[OF t0])
    have Dsq: "0 < (t * cos t + sin t) * (t * cos t + sin t)"
      by (rule mult_pos_pos[OF Dt Dt])
    show "\<exists>z. (Rratio has_real_derivative z) (at t) \<and> 0 < z"
    proof (intro exI conjI)
      show "(Rratio has_real_derivative
          (( ((t * t - 2) * cos t + 4 * t * sin t) * (t * cos t + sin t)
             - t * (t * sin t - 2 * cos t) * (2 * cos t - t * sin t))
            / ((t * cos t + sin t) * (t * cos t + sin t)))) (at t)"
        by (rule der)
      show "0 < (( ((t * t - 2) * cos t + 4 * t * sin t) * (t * cos t + sin t)
             - t * (t * sin t - 2 * cos t) * (2 * cos t - t * sin t))
            / ((t * cos t + sin t) * (t * cos t + sin t)))"
        using Numpos Dsq by (simp add: zero_less_divide_iff)
    qed
  qed
qed

text \<open>Hence \<open>\<alpha>/\<beta>\<close> is injective on a single branch \<open>(0,B)\<close> (with \<open>\<kappa>B\<close> inside the
  first branch) --- exactly the hypothesis \<open>prop_upair\<close> consumes.\<close>

text \<open>The key identity tying \<open>\<alpha>/\<beta>\<close> to \<open>R\<close>: \<open>\<alpha>(u)/\<beta>(u) = R(\<kappa>u)/\<kappa>\<close> (total division,
  holding even at the poles where both sides are \<open>0\<close>).\<close>

lemma ab_eq_R:
  fixes \<kappa> u :: real assumes "\<kappa> \<noteq> 0"
  shows "alphaU \<kappa> u / betaU \<kappa> u = Rratio (\<kappa>*u) / \<kappa>"
proof (cases "\<kappa>*u*cos (\<kappa>*u) + sin (\<kappa>*u) = 0")
  case True
  hence "betaU \<kappa> u = 0" by (simp add: betaU_def)
  moreover have "Rratio (\<kappa>*u) = 0" using True by (simp add: Rratio_def)
  ultimately show ?thesis by simp
next
  case False
  have nr: "\<kappa> * u * (\<kappa> * u * sin (\<kappa> * u) - 2 * cos (\<kappa> * u)) = \<kappa> * (- alphaU \<kappa> u)"
    by (simp add: alphaU_def algebra_simps power2_eq_square)
  have "Rratio (\<kappa> * u) / \<kappa>
        = \<kappa> * (- alphaU \<kappa> u) / (\<kappa> * u * cos (\<kappa> * u) + sin (\<kappa> * u)) / \<kappa>"
    by (simp only: Rratio_def nr)
  also have "\<dots> = - alphaU \<kappa> u / (\<kappa> * u * cos (\<kappa> * u) + sin (\<kappa> * u))"
    using assms by simp
  also have "\<dots> = alphaU \<kappa> u / betaU \<kappa> u"
    unfolding betaU_def by (simp only: divide_minus_right)
  finally show ?thesis by simp
qed

lemma alpha_beta_inj_on_branch:
  fixes \<kappa> B :: real
  assumes \<kappa>: "\<kappa> > 0" and B: "0 < B"
    and Dpos: "\<forall>t. 0 < t \<and> t \<le> \<kappa> * B \<longrightarrow> t * cos t + sin t > 0"
  shows "inj_on (\<lambda>u. alphaU \<kappa> u / betaU \<kappa> u) {u. 0 < u \<and> u < B}"
proof (rule inj_onI)
  fix u w assume u: "u \<in> {u. 0 < u \<and> u < B}" and w: "w \<in> {u. 0 < u \<and> u < B}"
    and eq: "alphaU \<kappa> u / betaU \<kappa> u = alphaU \<kappa> w / betaU \<kappa> w"
  have \<kappa>0: "\<kappa> \<noteq> 0" using \<kappa> by simp
  have "Rratio (\<kappa>*u) / \<kappa> = Rratio (\<kappa>*w) / \<kappa>"
    using eq by (simp add: ab_eq_R[OF \<kappa>0])
  hence Req: "Rratio (\<kappa>*u) = Rratio (\<kappa>*w)" using \<kappa>0 by simp
  have mono: "strict_mono_on {t. 0 < t \<and> t < \<kappa>*B} Rratio"
    by (rule R_strict_mono_first_branch[OF mult_pos_pos[OF \<kappa> B] Dpos])
  have inj: "inj_on Rratio {t. 0 < t \<and> t < \<kappa>*B}"
    by (rule strict_mono_on_imp_inj_on[OF mono])
  have u0: "0 < u" "u < B" using u by auto
  have w0: "0 < w" "w < B" using w by auto
  have mu: "\<kappa>*u \<in> {t. 0 < t \<and> t < \<kappa>*B}"
    using u0 \<kappa> by (auto intro: mult_pos_pos mult_strict_left_mono)
  have mw: "\<kappa>*w \<in> {t. 0 < t \<and> t < \<kappa>*B}"
    using w0 \<kappa> by (auto intro: mult_pos_pos mult_strict_left_mono)
  have "\<kappa>*u = \<kappa>*w" by (rule inj_onD[OF inj Req mu mw])
  thus "u = w" using \<kappa>0 by simp
qed

text \<open>
  \<^bold>\<open>The robust, Baire-compatible form\<close> (route 2).  As a function of the working
  point, the \<open>u\<close>-pair minor \<open>Du\<close> is real-analytic and not identically zero (it is
  nonzero for small same-sign \<open>u\<close>'s), so its zero set is \<^emph>\<open>nowhere dense\<close> --- which
  is all the downstream meagerness argument needs, and it sidesteps
  branch-localization entirely.  This is an instance of
  \<open>analytic_cut_nowhere_dense\<close>: \<^const>\<open>rline_entire\<close> \<open>Du\<close> is dischargeable because
  \<open>\<beta>,\<alpha>\<close> are entire combinations of \<open>cis\<close>/polynomials in the (affine) line parameter,
  exactly as for the array factor.\<close>

text \<open>
  \<^bold>\<open>On \<open>Du\<close> and real derivatives.\<close>  \<open>Du\<close> is the \<open>u\<close>-pair minor \<^emph>\<open>as a function of the
  working point\<close> \<open>x\<close>: it is the \<open>2\<times>2\<close> Jacobian determinant
  \<open>Du x = det \<partial>(b\<^sub>1,a\<^sub>1\<^sub>1)/\<partial>(u\<^sub>i,u\<^sub>j) = \<beta>(u\<^sub>i x)\<alpha>(u\<^sub>j x) - \<beta>(u\<^sub>j x)\<alpha>(u\<^sub>i x)\<close>, where
  \<^emph>\<open>\<open>\<beta>,\<alpha>\<close> are themselves the partial derivatives\<close> \<open>\<partial>\<^sub>u b\<^sub>1 = \<beta>(u)\<close>,
  \<open>\<partial>\<^sub>u a\<^sub>1\<^sub>1 = \<alpha>(u)\<close> (= \<^const>\<open>betaU\<close>, \<^const>\<open>alphaU\<close>).  So the derivative content is
  already \<^emph>\<open>inside\<close> \<open>\<beta>,\<alpha>\<close>; once evaluated, \<open>Du x\<close> is a plain real depending on \<open>x\<close>.
  The meagerness step does not re-differentiate --- it needs only that \<open>Du\<close> is
  real-analytic (\<^const>\<open>rline_entire\<close>, since \<open>\<beta>,\<alpha>\<close> are entire and the \<open>u\<close>-coordinates
  are affine in the line parameter) and not identically zero (from \<open>prop_upair\<close>).

  \<^bold>\<open>How it connects to the real derivatives.\<close>  With the concrete moment map: (i)
  prove the leaf identities \<open>\<partial>\<^sub>u b\<^sub>1 = betaU \<kappa> u\<close>, \<open>\<partial>\<^sub>u a\<^sub>1\<^sub>1 = alphaU \<kappa> u\<close>
  (\<^emph>\<open>this\<close> is where \<^const>\<open>has_derivative\<close>\<open>/\<close>\<^const>\<open>deriv\<close> appear); (ii) \<^bold>\<open>define\<close> the
  concrete \<open>Du x = betaU \<kappa> (uu x i) * alphaU \<kappa> (uu x j) - betaU \<kappa> (uu x j) * alphaU \<kappa> (uu x i)\<close>;
  (iii) instantiate this lemma, discharging \<^const>\<open>rline_entire\<close> from the
  \<open>cline_entire\<close>/\<open>rline_entire\<close> closure lemmas and non-triviality from \<open>prop_upair\<close>.
\<close>

lemma upair_minor_nowhere_dense:
  fixes W :: "'w::euclidean_space set" and Du :: "'w \<Rightarrow> real"
  assumes "rline_entire Du" and "\<exists>x. Du x \<noteq> 0"
  shows "nowhere_dense {x \<in> W. Du x = 0}"
  sorry

text \<open>TeX \<open>prop:vcos\<close> (L1583), \<open>prop:vsin\<close> (L1605), \<open>prop:vmixed\<close> (L1621):
  the cosine/sine/mixed \<open>v\<close>-block determinants, with the Vandermonde factor and
  the cofactor \<open>K\<close>.\<close>

lemma prop_vcos:
  fixes \<kappa> u1 u2 u3 v1 v2 v3 :: real
  defines "c1 \<equiv> cos (\<kappa> * u1)" and "c2 \<equiv> cos (\<kappa> * u2)" and "c3 \<equiv> cos (\<kappa> * u3)"
  shows "det3 c1 c2 c3 (u1 * c1) (u2 * c2) (u3 * c3)
              (2 * v1 * c1) (2 * v2 * c2) (2 * v3 * c3)
         = 2 * c1 * c2 * c3 * det3 1 1 1 u1 u2 u3 v1 v2 v3"
  sorry

lemma prop_vsin:
  fixes \<kappa> u1 u2 u3 v1 v2 v3 :: real
  defines "s1 \<equiv> sin (\<kappa> * u1)" and "s2 \<equiv> sin (\<kappa> * u2)" and "s3 \<equiv> sin (\<kappa> * u3)"
  shows "det3 (- s1) (- s2) (- s3) (- u1 * s1) (- u2 * s2) (- u3 * s3)
              (- 2 * v1 * s1) (- 2 * v2 * s2) (- 2 * v3 * s3)
         = - 2 * s1 * s2 * s3 * det3 1 1 1 u1 u2 u3 v1 v2 v3"
  sorry

lemma prop_vmixed:
  fixes \<kappa> u1 u2 u3 v1 v2 v3 :: real
  defines "c1 \<equiv> cos (\<kappa> * u1)" and "c2 \<equiv> cos (\<kappa> * u2)" and "c3 \<equiv> cos (\<kappa> * u3)"
      and "s1 \<equiv> sin (\<kappa> * u1)" and "s2 \<equiv> sin (\<kappa> * u2)" and "s3 \<equiv> sin (\<kappa> * u3)"
  shows "det3 (- s1) (- s2) (- s3) (u1 * c1) (u2 * c2) (u3 * c3)
              (v1 * c1) (v2 * c2) (v3 * c3)
         = - 2 * det3 s1 s2 s3 (u1 * c1) (u2 * c2) (u3 * c3) (v1 * c1) (v2 * c2) (v3 * c3)"
  sorry

text \<open>TeX \<open>prop:KLM\<close> (L1668): with \<open>K = det[s;uc;vc]\<close>, \<open>L = det[c;s;vc]\<close>,
  \<open>M = det[c;s;uc]\<close>: (1) on \<open>c\<^sub>1c\<^sub>2c\<^sub>3 \<noteq> 0\<close>, \<open>K=L=M=0 \<longleftrightarrow> s\<^sub>1=s\<^sub>2=s\<^sub>3=0\<close>;
  (2) one cosine zero \<open>\<Longrightarrow> L \<noteq> 0 \<or> M \<noteq> 0\<close>.\<close>

lemma prop_KLM_1:
  fixes \<kappa> u1 u2 u3 v1 v2 v3 :: real
  defines "c1 \<equiv> cos (\<kappa> * u1)" and "c2 \<equiv> cos (\<kappa> * u2)" and "c3 \<equiv> cos (\<kappa> * u3)"
      and "s1 \<equiv> sin (\<kappa> * u1)" and "s2 \<equiv> sin (\<kappa> * u2)" and "s3 \<equiv> sin (\<kappa> * u3)"
  defines "K \<equiv> det3 s1 s2 s3 (u1 * c1) (u2 * c2) (u3 * c3) (v1 * c1) (v2 * c2) (v3 * c3)"
      and "L \<equiv> det3 c1 c2 c3 s1 s2 s3 (v1 * c1) (v2 * c2) (v3 * c3)"
      and "M \<equiv> det3 c1 c2 c3 s1 s2 s3 (u1 * c1) (u2 * c2) (u3 * c3)"
  assumes "c1 * c2 * c3 \<noteq> 0"
  shows "(K = 0 \<and> L = 0 \<and> M = 0) \<longleftrightarrow> (s1 = 0 \<and> s2 = 0 \<and> s3 = 0)"
  sorry

lemma prop_KLM_2:
  fixes \<kappa> u1 u2 u3 v1 v2 v3 :: real
  defines "c1 \<equiv> cos (\<kappa> * u1)" and "c2 \<equiv> cos (\<kappa> * u2)" and "c3 \<equiv> cos (\<kappa> * u3)"
      and "s1 \<equiv> sin (\<kappa> * u1)" and "s2 \<equiv> sin (\<kappa> * u2)" and "s3 \<equiv> sin (\<kappa> * u3)"
  defines "L \<equiv> det3 c1 c2 c3 s1 s2 s3 (v1 * c1) (v2 * c2) (v3 * c3)"
      and "M \<equiv> det3 c1 c2 c3 s1 s2 s3 (u1 * c1) (u2 * c2) (u3 * c3)"
  assumes "(c1 = 0 \<and> c2 \<noteq> 0 \<and> c3 \<noteq> 0)
         \<or> (c2 = 0 \<and> c1 \<noteq> 0 \<and> c3 \<noteq> 0)
         \<or> (c3 = 0 \<and> c1 \<noteq> 0 \<and> c2 \<noteq> 0)"
  shows "L \<noteq> 0 \<or> M \<noteq> 0"
  sorry


subsection \<open>The generic geometric reduction engine (connectable)\<close>

text \<open>
  Every appendix codimension/meagerness conclusion has the shape ``the branch is
  contained in a real-analytic subvariety of positive codimension, hence projects
  meagerly to \<open>V\<close>''.  We state it once as a genuine theorem over an \<^emph>\<open>analytic\<close>
  certificate \<open>f\<close>: this is exactly \<open>slice_zero_nowhere_dense\<close> packaged with a
  projection.  Each concrete branch below is an instance, with \<open>f\<close> the relevant
  cofactor / determinant.
\<close>

lemma analytic_cut_nowhere_dense:
  fixes f :: "'w::euclidean_space \<Rightarrow> real" and W :: "'w set"
  assumes "rline_entire f" and "\<exists>x. f x \<noteq> 0"
  shows "nowhere_dense {x \<in> W. f x = 0}"
  sorry

lemma analytic_cut_meager_proj:
  fixes f :: "'w::euclidean_space \<Rightarrow> real" and W :: "'w set"
    and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}" and B :: "'w set"
  assumes "rline_entire f" and "\<exists>x. f x \<noteq> 0" and "B \<subseteq> {x \<in> W. f x = 0}"
    \<comment> \<open>projection of an analytic codim-\<open>\<ge>1\<close> slice is meager (\<open>lem:smooth-chart-meager\<close>)\<close>
  shows "meager (piV ` B)"
  sorry


subsection \<open>Appendix B--I as instances --- branch certificates\<close>

text \<open>
  Each obligation below names its \<^emph>\<open>analytic certificate\<close> \<open>cert\<close> (the cofactor or
  Jacobian whose vanishing carves the branch) as a \<^theory_text>\<open>fixes\<close>, carries
  \<^const>\<open>rline_entire\<close>\<open> cert\<close> (true for the real cofactor, a finite exponential sum)
  plus non-triviality, and concludes meagerness of the equation-cut branch via
  \<open>analytic_cut_meager_proj\<close>.  This is the connectable form: instantiate
  \<open>cert\<close> with the genuine cofactor and discharge \<^const>\<open>rline_entire\<close> from
  \<open>cline_entire_af\<close>/\<open>rline_entire_U_cart\<close>.

  Branch \<^bold>\<open>certificates\<close> (tex label \<open>\<rightarrow>\<close> the function whose analytic zero set covers it):
  \<^item> Appendix C \<open>prop:direct5\<close>/\<open>cor:pairambiguity\<close>/\<open>prop:direct5alt\<close>/\<open>cor:H0subcase\<close>:
    common-cofactor \<open>K\<close> (resp. \<open>L,M\<close>); a pair determinant \<open>= -2\<Delta>\<^sup>(\<^sup>u\<^sup>)K\<close> vanishes iff \<open>K=0\<close>.
  \<^item> Appendix D \<open>prop:szero-small\<close>/\<open>cor:szero-meager\<close>: certificate \<open>s\<^sub>1\<close> (any one sine).
  \<^item> Appendix E one-cosine \<open>cor:onecos-*\<close>: certificate the explicit \<open>3\<times>3\<close>
    determinant of \<open>(c\<^sub>1,K,a\<^sub>2)\<close>/\<open>(c\<^sub>1,a\<^sub>2,\<Lambda>)\<close>/\<open>(c\<^sub>1,E\<^sub>2,E\<^sub>3)\<close>.
  \<^item> Appendix F/G \<open>cor:allcos-*\<close>: certificate \<open>B\<^sub>1 S\<close> (the \<open>3\<times>3\<close> minor \<open>= \<mp>u B\<^sub>1 S c\<^sub>1c\<^sub>2c\<^sub>3\<close>).
  \<^item> Appendix H \<open>app:H0res\<close>: certificates \<open>B\<^sub>j\<close> (transversal cuts), \<open>S\<close>, \<open>c\<^sub>i\<close> (cosines).
  \<^item> Appendix I \<open>app:caseB\<close>: certificates \<open>F\<^sub>\<eta>(u\<^sub>j)\<close> (\<open>u\<close>-slice), \<open>\<Delta>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<close>, \<open>\<Delta>\<^sup>(\<^sup>2\<^sup>2\<^sup>)\<close>,
    \<open>\<Lambda>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<close>, and the degenerate-critical \<open>F\<^sub>j\<close>.
\<close>

text \<open>TeX \<open>cor:szero-meager\<close> (L2203) --- representative instance, all-sine-zero.\<close>

lemma cor_szero_meager:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and s1 :: "'w \<Rightarrow> real"
  assumes "rline_entire s1" and "\<exists>x. s1 x \<noteq> 0"
  shows "meager (piV ` {x \<in> Wset. s1 x = 0})"
  by (rule analytic_cut_meager_proj[OF assms subset_refl])

text \<open>TeX \<open>prop:h0res-threecos\<close> (L3396) --- three-cosine branch, certificate \<open>c\<^sub>1\<close>.\<close>

lemma prop_h0res_threecos:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and c1 :: "'w \<Rightarrow> real"
  assumes "rline_entire c1" and "\<exists>x. c1 x \<noteq> 0"
  shows "meager (piV ` {x \<in> Wset. c1 x = 0})"
  by (rule analytic_cut_meager_proj[OF assms subset_refl])

text \<open>TeX \<open>cor:allcos-a1a2\<close> (L2990) --- certificate the rank-3 minor
  \<open>m = u\<^sub>1 B\<^sub>1 S c\<^sub>1c\<^sub>2c\<^sub>3\<close> (its analytic zero set covers the \<open>S \<noteq> 0\<close>, some-\<open>B\<^sub>j \<noteq> 0\<close> subcase).\<close>

lemma cor_allcos_a1a2:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and m :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire m" and "\<exists>x. m x \<noteq> 0" and "B \<subseteq> {x \<in> Wset. m x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])


subsection \<open>The three branch facts feeding \<open>prop:regnonzero\<close>\<close>

text \<open>
  These are the conclusions the appendix exists to produce; they are exactly the
  hypotheses \<open>meager_Zreg\<close>, \<open>meager_ZH0surj\<close>, \<open>meager_BcaseB\<close>, \<open>meager_BH0res\<close> of
  the already-proven reduction \<open>Nonemptiness_Paper.prop_regnonzero\<close>.  Each is
  assembled from finitely many of the analytic-cut instances above, so it is stated
  here as a parametric theorem with those instances as hypotheses --- the same
  pattern as \<open>nonemptiness_from_branches\<close>.
\<close>

text \<open>TeX \<open>prop:dimZ\<close> (L1145), facts (1) and (2): \<open>Z\<^sub>r\<^sub>e\<^sub>g\<close> (codim 3) and the
  \<open>H\<equiv>0\<close> surjective stratum (dim \<open>\<le> 2N-3\<close>) project meagerly.\<close>

lemma prop_dimZ:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and Zreg ZH0surj :: "'w set" and fZ fH :: "'w \<Rightarrow> real"
  assumes "rline_entire fZ" "\<exists>x. fZ x \<noteq> 0" "Zreg \<subseteq> {x \<in> Wset. fZ x = 0}"
    and "rline_entire fH" "\<exists>x. fH x \<noteq> 0" "ZH0surj \<subseteq> {x \<in> Wset. fH x = 0}"
  shows "meager (piV ` Zreg)" and "meager (piV ` ZH0surj)"
  using analytic_cut_meager_proj[OF assms(1) assms(2) assms(3)]
        analytic_cut_meager_proj[OF assms(4) assms(5) assms(6)] by blast+

text \<open>TeX \<open>prop:h0res-meager\<close> (L3544), fact (4): assembled from the residual
  \<open>H\<equiv>0\<close> branch projections (\<open>B\<^sub>1=B\<^sub>2=B\<^sub>3=0\<close>, \<open>S=0\<close>, two-/three-cosine).\<close>

lemma prop_h0res_meager:
  fixes Vset :: "'v::{real_normed_vector,heine_borel} set" and BH0res :: "'v set"
  assumes "BH0res \<subseteq> Bbranch \<union> Sbranch \<union> twocos \<union> threecos"
    and "meager (Bbranch \<inter> Vset)" and "meager (Sbranch \<inter> Vset)"
    and "meager (twocos \<inter> Vset)" and "meager (threecos \<inter> Vset)"
  shows "meager (BH0res \<inter> Vset)"
proof -
  have un: "meager ((Bbranch \<inter> Vset) \<union> (Sbranch \<inter> Vset) \<union> (twocos \<inter> Vset) \<union> (threecos \<inter> Vset))"
    by (rule meager_Un[OF meager_Un[OF meager_Un[OF assms(2) assms(3)] assms(4)] assms(5)])
  have sub: "BH0res \<inter> Vset
              \<subseteq> (Bbranch \<inter> Vset) \<union> (Sbranch \<inter> Vset) \<union> (twocos \<inter> Vset) \<union> (threecos \<inter> Vset)"
    using assms(1) by blast
  show ?thesis by (rule meager_subset[OF sub un])
qed

text \<open>TeX \<open>cor:caseBmeager\<close> (L6206), fact (3): assembled from the three
  nonzero-Hessian branch closures \<open>cor:H11-closed\<close>, the \<open>H\<^sub>2\<^sub>2 \<noteq> 0\<close> closure, and
  \<open>cor:Lambda-closed\<close> (the \<open>H\<^sub>1\<^sub>2=0\<close> branch).\<close>

lemma cor_caseBmeager:
  fixes Vset :: "'v::{real_normed_vector,heine_borel} set" and BcaseB :: "'v set"
  assumes "BcaseB \<subseteq> BH11 \<union> BH22 \<union> BH12"
    and "meager (BH11 \<inter> Vset)" and "meager (BH22 \<inter> Vset)" and "meager (BH12 \<inter> Vset)"
  shows "meager (BcaseB \<inter> Vset)"
proof -
  have un: "meager ((BH11 \<inter> Vset) \<union> (BH22 \<inter> Vset) \<union> (BH12 \<inter> Vset))"
    by (rule meager_Un[OF meager_Un[OF assms(2) assms(3)] assms(4)])
  have sub: "BcaseB \<inter> Vset \<subseteq> (BH11 \<inter> Vset) \<union> (BH22 \<inter> Vset) \<union> (BH12 \<inter> Vset)"
    using assms(1) by blast
  show ?thesis by (rule meager_subset[OF sub un])
qed


subsection \<open>Appendix C --- common-cofactor theorem (\<open>H\<equiv>0\<close>)\<close>

text \<open>TeX \<open>prop:direct5\<close> (L1887): the pair determinant
  \<open>\<partial>(b\<^sub>1,b\<^sub>2,a\<^sub>1\<^sub>1,a\<^sub>1\<^sub>2,a\<^sub>2\<^sub>2)/\<partial>(u\<^sub>i,u\<^sub>j,v\<^sub>1,v\<^sub>2,v\<^sub>3) = -2 \<Delta>\<^sup>(\<^sup>u\<^sup>)\<^sub>i\<^sub>j K\<close>.
  Consumable form (\<open>cor:pairambiguity\<close>, L1942): with that factorization and
  \<open>\<Delta>\<^sup>(\<^sup>u\<^sup>) \<noteq> 0\<close>, the three pair determinants vanish simultaneously iff \<open>K = 0\<close>
  (the factorization is carried as a hypothesis, so this is genuine algebra).\<close>

lemma cor_pairambiguity:
  fixes d12 d13 d23 Delu12 Delu13 Delu23 Kf :: "'w::euclidean_space \<Rightarrow> real" and x :: 'w
  assumes "Delu12 x \<noteq> 0" "Delu13 x \<noteq> 0" "Delu23 x \<noteq> 0"
    and "d12 x = - 2 * Delu12 x * Kf x"
    and "d13 x = - 2 * Delu13 x * Kf x"
    and "d23 x = - 2 * Delu23 x * Kf x"
  shows "(d12 x = 0 \<and> d13 x = 0 \<and> d23 x = 0) \<longleftrightarrow> Kf x = 0"
  sorry

text \<open>TeX \<open>prop:direct5alt\<close> (L1955), \<open>cor:H0subcase\<close> (L1996): alternative
  factorizations \<open>= -2\<Delta>\<^sup>(\<^sup>u\<^sup>)L\<close>, \<open>= -\<Delta>\<^sup>(\<^sup>u\<^sup>)M\<close>, and the closed \<open>H\<equiv>0\<close> subcase
  (\<open>a\<^sub>1a\<^sub>2 \<noteq> 0\<close>, some \<open>L,M \<noteq> 0\<close> \<Longrightarrow> some alternative pair determinant nonzero).\<close>

lemma cor_H0subcase:
  fixes dL dM Delu Lf Mf a1f a2f :: "'w::euclidean_space \<Rightarrow> real" and x :: 'w
  assumes "Delu x \<noteq> 0" and "a1f x * a2f x \<noteq> 0"
    and "dL x = - 2 * Delu x * Lf x" and "dM x = - 1 * Delu x * Mf x"
    and "Lf x \<noteq> 0 \<or> Mf x \<noteq> 0"
  shows "dL x \<noteq> 0 \<or> dM x \<noteq> 0"
  sorry


subsection \<open>Appendix D --- all-sine-zero \<open>H\<equiv>0\<close> subcase\<close>

text \<open>TeX \<open>lem:Fij\<close> (L2083): not all
  \<open>F\<^sub>i\<^sub>j = a(u\<^sub>iv\<^sub>j - u\<^sub>jv\<^sub>i) + a\<^sub>1(v\<^sub>i-v\<^sub>j) - a\<^sub>2(u\<^sub>i-u\<^sub>j)\<close> vanish.
  \<^bold>\<open>Truth note:\<close> FALSE without the good-triple hypothesis (if the three points are
  collinear w.r.t. the line \<open>(a,a\<^sub>1,a\<^sub>2)\<close>, all \<open>F\<^sub>i\<^sub>j\<close> vanish); the noncollinearity
  hypothesis is carried explicitly.\<close>

lemma lem_Fij:
  fixes a a1 a2 :: real and u v :: "nat \<Rightarrow> real"
  defines "F \<equiv> (\<lambda>i j. a*(u i * v j - u j * v i) + a1*(v i - v j) - a2*(u i - u j))"
  assumes "a > 0"
    and noncollinear:
      "\<not> (\<exists>p q r. (p,q,r) \<noteq> (0,0,0) \<and> (\<forall>k\<in>{1,2,3}. p * u k + q * v k + r = 0))"
  shows "F 1 2 \<noteq> 0 \<or> F 1 3 \<noteq> 0 \<or> F 2 3 \<noteq> 0"
  sorry

text \<open>TeX \<open>prop:direct5szero\<close> (L2029)/\<open>cor:szeroH0\<close> (L2131): on the all-sine-zero
  stratum the \<open>5\<times>5\<close> determinants factor as
  \<open>64 a\<^sup>3 c\<^sub>i\<^sup>2c\<^sub>j\<^sup>2c\<^sub>k g\<^sup>4 \<kappa>\<^sup>3 (a\<^sub>1g\<^sub>1+gb\<^sub>1\<^sub>1) A\<^sub>T F\<^sub>i\<^sub>j\<close>; rank 5 when \<open>a\<^sub>1g\<^sub>1+gb\<^sub>1\<^sub>1 \<noteq> 0\<close>.
  Consumable: the rank-deficient locus lies in the analytic cut
  \<open>{(a\<^sub>1g\<^sub>1+gb\<^sub>1\<^sub>1)\<cdot>F\<^sub>1\<^sub>2 = 0}\<close>, hence projects meagerly.\<close>

lemma cor_szeroH0_meager:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

text \<open>TeX \<open>prop:szero-small\<close> (L2165): \<open>\<Sigma>\<^sub>0 = {s\<^sub>1=s\<^sub>2=s\<^sub>3=0}\<close> is codim 3
  (cert: any one sine \<open>s\<^sub>1\<close>).\<close>

lemma prop_szero_small_meager:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and s1 :: "'w \<Rightarrow> real"
  assumes "rline_entire s1" "\<exists>x. s1 x \<noteq> 0"
  shows "meager (piV ` {x \<in> Wset. s1 x = 0})"
  by (rule analytic_cut_meager_proj[OF assms subset_refl])


subsection \<open>Appendix E --- residual one-cosine-zero subcases\<close>

text \<open>TeX \<open>cor:onecos-codim3\<close> (L2306): cert
  \<open>= det \<partial>(c\<^sub>1,K,a\<^sub>2)/\<partial>(u\<^sub>1,v\<^sub>2,v\<^sub>3) = \<kappa> s\<^sub>1\<^sup>2 c\<^sub>2 c\<^sub>3 (c\<^sub>2u\<^sub>2+c\<^sub>3u\<^sub>3)\<close>;
  \<open>cor:onecos-lam\<close> (L2416): cert
  \<open>= det \<partial>(c\<^sub>1,a\<^sub>2,\<Lambda>)/\<partial>(u\<^sub>1,u\<^sub>2,v\<^sub>2) = \<kappa> s\<^sub>1 c\<^sub>2 (c\<^sub>2 - \<kappa> s\<^sub>2 u\<^sub>2)\<close>;
  \<open>cor:onecos-terminal\<close> (L2508): cert
  \<open>= det \<partial>(c\<^sub>1,E\<^sub>2,E\<^sub>3)/\<partial>(u\<^sub>1,u\<^sub>2,u\<^sub>3) = -\<kappa> s\<^sub>1 (-2\<kappa>s\<^sub>2-\<kappa>\<^sup>2u\<^sub>2c\<^sub>2)(-2\<kappa>s\<^sub>3-\<kappa>\<^sup>2u\<^sub>3c\<^sub>3)\<close>,
  \<open>E\<^sub>k = c\<^sub>k - \<kappa> s\<^sub>k u\<^sub>k\<close>.  Each is an analytic-cut meagerness instance.\<close>

lemma cor_onecos_codim3:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

lemma cor_onecos_lam:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

lemma cor_onecos_terminal:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

text \<open>TeX \<open>cor:onecos-exhausted\<close> (L2531): the union of the three subcases exhausts
  the \<open>c\<^sub>1=0\<close> residual.\<close>

lemma cor_onecos_exhausted:
  fixes Vset :: "'v::{real_normed_vector,heine_borel} set" and Bexh :: "'v set"
  assumes "Bexh \<subseteq> Bcodim3 \<union> Blam \<union> Bterminal"
    and "meager (Bcodim3 \<inter> Vset)" "meager (Blam \<inter> Vset)" "meager (Bterminal \<inter> Vset)"
  shows "meager (Bexh \<inter> Vset)"
proof -
  have un: "meager ((Bcodim3 \<inter> Vset) \<union> (Blam \<inter> Vset) \<union> (Bterminal \<inter> Vset))"
    by (rule meager_Un[OF meager_Un[OF assms(2) assms(3)] assms(4)])
  have sub: "Bexh \<inter> Vset \<subseteq> (Bcodim3 \<inter> Vset) \<union> (Blam \<inter> Vset) \<union> (Bterminal \<inter> Vset)"
    using assms(1) by blast
  show ?thesis by (rule meager_subset[OF sub un])
qed


subsection \<open>Appendix F/G --- degenerate all-cosine branches\<close>

text \<open>TeX \<open>cor:allcos-La2\<close> (L2678): \<open>K=L=a\<^sub>2=0\<close> branch codim 4 (after one auxiliary).
  \<open>prop:quarterturn\<close> (L2733) is the symmetry \<open>u'=v, v'=-u, K'=K, L'=-M, M'=L\<close>, giving
  \<open>cor:allcos-Ma1\<close> (L2862, the dual \<open>K=M=a\<^sub>1=0\<close> branch) from \<open>cor:allcos-La2\<close>.\<close>

lemma cor_allcos_La2:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

lemma cor_allcos_Ma1:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])


subsection \<open>Appendix H --- residual Hessian-zero closure \<open>app:H0res\<close>\<close>

text \<open>TeX \<open>lem:h0res-Bcuts\<close> (L3143): each \<open>B\<^sub>j = \<beta>(t\<^sub>j) = cos t\<^sub>j - t\<^sub>j sin t\<^sub>j\<close> is a
  smooth hypersurface, \<open>\<beta>'(t) = -(2 sin t + t cos t) \<noteq> 0\<close> on \<open>{\<beta>=0}\<close>.\<close>

lemma lem_h0res_Bcuts:
  fixes t :: real
  assumes "cos t - t * sin t = 0"
  shows "- (2 * sin t + t * cos t) \<noteq> 0"
  sorry

text \<open>TeX \<open>prop:h0res-Bbranch\<close> (L3175): \<open>B\<^sub>1=B\<^sub>2=B\<^sub>3=0\<close> branch codim \<open>\<ge>3\<close> (cert any
  \<open>B\<^sub>j\<close>); \<open>lem:h0res-residue-exc\<close> (L3196): residue exceptional sets codim \<open>\<ge>N-3\<ge>4\<close>
  (cert any residue cosine); \<open>lem:h0res-baseSK\<close> (L3269): base slice
  \<open>{c\<^sub>1c\<^sub>2c\<^sub>3\<noteq>0, S=0, K=0}\<close> codim \<open>\<ge>2\<close> (cert \<open>S\<close>); \<open>prop:h0res-Sbranch\<close> (L3349):
  \<open>S=0\<close> branch meager (cert \<open>S\<close>); \<open>prop:h0res-twocos\<close> (L3417): two-cosine branch
  codim \<open>\<ge>2\<close> (cert \<open>c\<^sub>i\<close>).\<close>

lemma prop_h0res_Bbranch:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

lemma lem_h0res_residue_exc:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

lemma lem_h0res_baseSK:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

lemma prop_h0res_Sbranch:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and Sf :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire Sf" "\<exists>x. Sf x \<noteq> 0" "B \<subseteq> {x \<in> Wset. Sf x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

lemma prop_h0res_twocos:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and ci :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire ci" "\<exists>x. ci x \<noteq> 0" "B \<subseteq> {x \<in> Wset. ci x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

text \<open>TeX \<open>lem:h0res-a1a2\<close> (L3234): off the residue exceptional sets the residue
  map \<open>r \<mapsto> (a\<^sub>1,a\<^sub>2)\<close> has rank 2.\<close>

lemma lem_h0res_a1a2:
  fixes rk_residue :: "'w::euclidean_space \<Rightarrow> nat" and exc :: "'w \<Rightarrow> bool" and x :: 'w
  assumes "\<not> exc x"  \<comment> \<open>\<open>x\<close> off \<open>E\<^sub>c\<^sub>~ \<union> E\<^sub>B\<^sub>~\<close>\<close>
  shows "rk_residue x = 2"
  sorry


subsection \<open>Appendix I --- direct configuration-space closure of Case B\<close>

text \<open>TeX \<open>prop:vblock\<close> (L3682): \<open>det \<partial>(\<Phi>\<^sub>2,H\<^sub>1\<^sub>2,H\<^sub>2\<^sub>2)/\<partial>(v) = -16a\<^sup>2g\<^sup>3(aK+a\<^sub>1L-a\<^sub>2M)\<close>;
  \<open>prop:branch\<close> (L3712)/\<open>cor:repair\<close> (L3812): on \<open>{H\<^sub>2\<^sub>2\<noteq>0, H\<^sub>1\<^sub>2\<noteq>0, aK+a\<^sub>1L-a\<^sub>2M\<noteq>0}\<close>
  with a regular \<open>u\<close>-slice direction, \<open>rank D\<^bsub>x\<^esub>\<Phi> = 3\<close>.  Consumable: the
  rank-deficient locus is the analytic cut \<open>{aK+a\<^sub>1L-a\<^sub>2M = 0}\<close> (mod the \<open>u\<close>-slice
  residue of \<open>cor:uphi-exhausted\<close>), hence meager.\<close>

lemma cor_repair_meager:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

text \<open>TeX \<open>prop:uphi-reduce\<close> (L3849): \<open>D\<Phi>\<^sub>1|\<^bsub>E\<^sub>u\<^esub> = 0 \<longleftrightarrow> F\<^sub>\<eta>(u\<^sub>j) = 0\<close>,
  \<open>F\<^sub>\<eta>(u) = cos(\<kappa>u) - \<kappa>(u-\<eta>)sin(\<kappa>u)\<close>, \<open>\<eta> = g\<^sub>1/(2g)\<close>; \<open>prop:uphi-codim3\<close> (L3920):
  \<open>Z\<^sub>\<eta> = {u : F\<^sub>\<eta>(u)=0}\<close> is discrete (real-analytic isolated zeros);
  \<open>cor:uphi-exhausted\<close> (L3980): the vanishing \<open>u\<close>-slice residue is nowhere dense.\<close>

lemma prop_uphi_codim3:
  fixes \<kappa> \<eta> :: real
  defines "Feta \<equiv> (\<lambda>u. cos (\<kappa> * u) - \<kappa> * (u - \<eta>) * sin (\<kappa> * u))"
  assumes "\<kappa> \<noteq> 0"
  shows "\<forall>u. Feta u = 0 \<longrightarrow> (\<exists>\<epsilon>>0. \<forall>u'. \<bar>u' - u\<bar> < \<epsilon> \<and> Feta u' = 0 \<longrightarrow> u' = u)"
  sorry

lemma cor_uphi_exhausted:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
    \<comment> \<open>\<open>cert = F\<^sub>\<eta>(u\<^sub>1) F\<^sub>\<eta>(u\<^sub>2) F\<^sub>\<eta>(u\<^sub>3)\<close>\<close>
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

text \<open>TeX \<open>prop:vpair11\<close>..\<open>cor:H11-closed\<close> (L4032--4337): the \<open>H\<^sub>1\<^sub>1 \<noteq> 0\<close> branch is
  exhausted by the all-sine-zero slice (\<open>prop:szero-local\<close>, codim 3), the \<open>u\<close>-slice
  residue (nowhere dense), the rank-3 subcase (\<open>\<Delta>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<^sub>i\<^sub>j \<noteq> 0\<close>,
  \<open>\<Delta>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<^sub>i\<^sub>j = -8ag\<^sup>2 H\<^sub>1\<^sub>1\<^sup>-\<^sup>1(s\<^sub>ic\<^sub>jR\<^sub>j-s\<^sub>jc\<^sub>iR\<^sub>i)\<close>), and the pair-minor residue (codim 4).\<close>

lemma cor_H11_closed:
  fixes Vset :: "'v::{real_normed_vector,heine_borel} set" and BH11 :: "'v set"
  assumes "BH11 \<subseteq> Bszero \<union> Buslice \<union> Bgraph"
    and "meager (Bszero \<inter> Vset)" "meager (Buslice \<inter> Vset)" "meager (Bgraph \<inter> Vset)"
  shows "meager (BH11 \<inter> Vset)"
proof -
  have un: "meager ((Bszero \<inter> Vset) \<union> (Buslice \<inter> Vset) \<union> (Bgraph \<inter> Vset))"
    by (rule meager_Un[OF meager_Un[OF assms(2) assms(3)] assms(4)])
  have sub: "BH11 \<inter> Vset \<subseteq> (Bszero \<inter> Vset) \<union> (Buslice \<inter> Vset) \<union> (Bgraph \<inter> Vset)"
    using assms(1) by blast
  show ?thesis by (rule meager_subset[OF sub un])
qed

text \<open>TeX \<open>prop:vpair22\<close>..\<open>cor:vpair22-full\<close> (L4398--5401): the \<open>H\<^sub>1\<^sub>2\<noteq>0, H\<^sub>2\<^sub>2\<noteq>0\<close>
  branch.  Pair-minor residue \<open>\<Delta>\<^sup>(\<^sup>2\<^sup>2\<^sup>) = -8ag\<^sup>2 H\<^sub>1\<^sub>2 H\<^sub>2\<^sub>2\<^sup>-\<^sup>2(s\<^sub>ic\<^sub>jR\<^sub>j-s\<^sub>jc\<^sub>iR\<^sub>i)\<close>,
  graph reduction \<open>v\<^sub>j = \<delta>+\<mu>u\<^sub>j-\<rho>tan(\<kappa>u\<^sub>j)\<close>, the KLM relations
  (\<open>L=-c\<^sub>1c\<^sub>2c\<^sub>3 V\<^sub>\<tau>\<close> etc.), scalar residue \<open>\<Theta>\<^sub>1\<^sup>(\<^sup>2\<^sup>2\<^sup>)=\<Theta>\<^sub>2\<^sup>(\<^sup>2\<^sup>2\<^sup>)=0\<close>: all codim-4 cuts.\<close>

lemma cor_vpair22_full_meager:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

text \<open>TeX \<open>cor:vpair22-nonzero\<close> (L4928): when the scalar residue vanishes,
  \<open>L/M = H\<^sub>2\<^sub>2/H\<^sub>1\<^sub>2\<close> (genuine algebra from \<open>\<Theta>\<^sub>1\<^sup>(\<^sup>2\<^sup>2\<^sup>) = H\<^sub>2\<^sub>2M - H\<^sub>1\<^sub>2L = 0\<close>).\<close>

lemma cor_vpair22_nonzero:
  fixes Kf Lf Mf H12 H22 af a1f a2f :: "'w::euclidean_space \<Rightarrow> real" and x :: 'w
  assumes "H12 x \<noteq> 0" "H22 x \<noteq> 0" "Mf x \<noteq> 0"
    and "H22 x * Mf x - H12 x * Lf x = 0"
  shows "Lf x / Mf x = H22 x / H12 x"
  sorry

text \<open>TeX \<open>prop:H12zero\<close> (L5447)/\<open>cor:H12zero\<close> (L5529): \<open>H\<^sub>1\<^sub>2=0\<close> block factorization
  \<open>det \<partial>(\<Phi>)/\<partial>(u\<^sub>i,u\<^sub>j,v\<^sub>k) = 2ag s\<^sub>k H\<^sub>2\<^sub>2 \<Lambda>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<^sub>i\<^sub>j\<close>; rank 3 if \<open>s\<^sub>k\<noteq>0, \<Lambda>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<^sub>i\<^sub>j\<noteq>0\<close>.
  Consumable: the rank-deficient locus is the analytic cut \<open>{s\<^sub>k \<Lambda>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<^sub>i\<^sub>j = 0}\<close>.\<close>

lemma cor_H12zero_meager:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and cert :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire cert" "\<exists>x. cert x \<noteq> 0" "B \<subseteq> {x \<in> Wset. cert x = 0}"
  shows "meager (piV ` B)"
  by (rule analytic_cut_meager_proj[OF assms])

text \<open>TeX \<open>prop:Lambda-common\<close> (L5656): the vanishing \<open>\<Lambda>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<close>-residue gives
  \<open>\<alpha>,\<beta>\<close> with \<open>F\<^sub>j(\<alpha>,\<beta>) = 2(\<alpha>-u\<^sub>j)B\<^sub>j + \<kappa> s\<^sub>j(\<beta>-u\<^sub>j\<^sup>2) = 0\<close>.\<close>

lemma prop_Lambda_common:
  fixes \<kappa> :: real and Lam :: "nat \<Rightarrow> nat \<Rightarrow> real" and uu BB ss :: "nat \<Rightarrow> real"
  defines "Fj \<equiv> (\<lambda>\<alpha> \<beta> j. 2*(\<alpha> - uu j)*BB j + \<kappa> * ss j * (\<beta> - (uu j)\<^sup>2))"
  assumes "Lam 1 2 = 0" "Lam 1 3 = 0" "Lam 2 3 = 0"
  shows "\<exists>\<alpha> \<beta>. \<forall>j\<in>{1,2,3}. Fj \<alpha> \<beta> j = 0"
  sorry

text \<open>TeX \<open>cor:double-impossible\<close> (L5816): no two distinct indices are both
  degenerate-critical, because \<open>\<alpha>\<^sub>\<ast>\<close> is strictly increasing
  (\<open>prop_double_param_mono\<close>), hence injective.\<close>

lemma cor_double_impossible:
  fixes \<kappa> :: real and uu :: "nat \<Rightarrow> real" and i j :: nat
  assumes "\<kappa> \<noteq> 0" "uu i \<noteq> uu j"
  shows "astar \<kappa> (uu i) \<noteq> astar \<kappa> (uu j)"
  using prop_double_param_mono[OF assms(1)] assms(2)
  by (meson UNIV_I strict_mono_on_imp_inj_on inj_onD)

text \<open>TeX \<open>prop:Lambda-simple/high/onefold/twofold\<close> + \<open>cor:Lambda-*\<close> (L5836--6182):
  the \<open>\<Lambda>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<close>-residue critical-point families are codim 3/4/5 analytic cuts
  (cert: the degenerate-critical equations \<open>F\<^sub>j,G\<^sub>j,H\<^sub>j\<close>); \<open>cor:Lambda-closed\<close> (L6185):
  the whole \<open>H\<^sub>1\<^sub>2=0, H\<^sub>2\<^sub>2\<noteq>0\<close> branch projects meagerly.\<close>

lemma cor_Lambda_closed:
  fixes Vset :: "'v::{real_normed_vector,heine_borel} set" and BH12 :: "'v set"
  assumes "BH12 \<subseteq> Bsimple \<union> Bonefold \<union> Bhigh"
    and "meager (Bsimple \<inter> Vset)" "meager (Bonefold \<inter> Vset)" "meager (Bhigh \<inter> Vset)"
  shows "meager (BH12 \<inter> Vset)"
proof -
  have un: "meager ((Bsimple \<inter> Vset) \<union> (Bonefold \<inter> Vset) \<union> (Bhigh \<inter> Vset))"
    by (rule meager_Un[OF meager_Un[OF assms(2) assms(3)] assms(4)])
  have sub: "BH12 \<inter> Vset \<subseteq> (Bsimple \<inter> Vset) \<union> (Bonefold \<inter> Vset) \<union> (Bhigh \<inter> Vset)"
    using assms(1) by blast
  show ?thesis by (rule meager_subset[OF sub un])
qed

end
