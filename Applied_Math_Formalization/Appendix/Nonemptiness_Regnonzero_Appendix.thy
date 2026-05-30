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
  sorry

text \<open>TeX \<open>prop:h0res-threecos\<close> (L3396) --- three-cosine branch, certificate \<open>c\<^sub>1\<close>.\<close>

lemma prop_h0res_threecos:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and c1 :: "'w \<Rightarrow> real"
  assumes "rline_entire c1" and "\<exists>x. c1 x \<noteq> 0"
  shows "meager (piV ` {x \<in> Wset. c1 x = 0})"
  sorry

text \<open>TeX \<open>cor:allcos-a1a2\<close> (L2990) --- certificate the rank-3 minor
  \<open>m = u\<^sub>1 B\<^sub>1 S c\<^sub>1c\<^sub>2c\<^sub>3\<close> (its analytic zero set covers the \<open>S \<noteq> 0\<close>, some-\<open>B\<^sub>j \<noteq> 0\<close> subcase).\<close>

lemma cor_allcos_a1a2:
  fixes Wset :: "'w::euclidean_space set" and piV :: "'w \<Rightarrow> 'v::{real_normed_vector,heine_borel}"
    and m :: "'w \<Rightarrow> real" and B :: "'w set"
  assumes "rline_entire m" and "\<exists>x. m x \<noteq> 0" and "B \<subseteq> {x \<in> Wset. m x = 0}"
  shows "meager (piV ` B)"
  sorry


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
  sorry

text \<open>TeX \<open>prop:h0res-meager\<close> (L3544), fact (4): assembled from the residual
  \<open>H\<equiv>0\<close> branch projections (\<open>B\<^sub>1=B\<^sub>2=B\<^sub>3=0\<close>, \<open>S=0\<close>, two-/three-cosine).\<close>

lemma prop_h0res_meager:
  fixes Vset :: "'v::{real_normed_vector,heine_borel} set" and BH0res :: "'v set"
  assumes "BH0res \<subseteq> Bbranch \<union> Sbranch \<union> twocos \<union> threecos"
    and "meager (Bbranch \<inter> Vset)" and "meager (Sbranch \<inter> Vset)"
    and "meager (twocos \<inter> Vset)" and "meager (threecos \<inter> Vset)"
  shows "meager (BH0res \<inter> Vset)"
  sorry

text \<open>TeX \<open>cor:caseBmeager\<close> (L6206), fact (3): assembled from the three
  nonzero-Hessian branch closures \<open>cor:H11-closed\<close>, the \<open>H\<^sub>2\<^sub>2 \<noteq> 0\<close> closure, and
  \<open>cor:Lambda-closed\<close> (the \<open>H\<^sub>1\<^sub>2=0\<close> branch).\<close>

lemma cor_caseBmeager:
  fixes Vset :: "'v::{real_normed_vector,heine_borel} set" and BcaseB :: "'v set"
  assumes "BcaseB \<subseteq> BH11 \<union> BH22 \<union> BH12"
    and "meager (BH11 \<inter> Vset)" and "meager (BH22 \<inter> Vset)" and "meager (BH12 \<inter> Vset)"
  shows "meager (BcaseB \<inter> Vset)"
  sorry


subsection \<open>Remaining appendix sub-lemmas (roadmap)\<close>

text \<open>
  The sub-lemmas of Appendices C--I that are not separately stated above all fall
  into the two connectable patterns: either a concrete determinant/rank identity in
  the moment or triple-coordinate variables (state like \<open>lem:3x3\<close> / Appendix A), or
  an analytic-cut meagerness instance (state like \<open>cor:szero-meager\<close>, via
  \<open>analytic_cut_meager_proj\<close> with the certificate listed in the table above).
  In dependency order they are:

  \<^bold>\<open>Appendix C\<close> (\<open>H\<equiv>0\<close> common cofactor): \<open>prop:direct5\<close>, \<open>cor:pairambiguity\<close>,
    \<open>prop:direct5alt\<close>, \<open>cor:H0subcase\<close>.
  \<^bold>\<open>Appendix D\<close> (all-sine-zero): \<open>prop:direct5szero\<close>, \<open>lem:Fij\<close>, \<open>cor:szeroH0\<close>,
    \<open>prop:szero-small\<close>.
  \<^bold>\<open>Appendix E\<close> (one-cosine): \<open>prop:onecos-codim3\<close>, \<open>cor:onecos-codim3\<close>,
    \<open>prop:onecos-lam\<close>, \<open>cor:onecos-lam\<close>, \<open>prop:onecos-terminal\<close>, \<open>cor:onecos-terminal\<close>,
    \<open>cor:onecos-exhausted\<close>.
  \<^bold>\<open>Appendix F\<close> (degenerate all-cosine): \<open>prop:allcos-La2\<close>, \<open>cor:allcos-La2\<close>,
    \<open>prop:quarterturn\<close>, \<open>cor:allcos-Ma1\<close>.
  \<^bold>\<open>Appendix G\<close> (simultaneous zero): \<open>prop:allcos-a1a2\<close>.
  \<^bold>\<open>Appendix H\<close> (\<open>app:H0res\<close>): \<open>lem:h0res-Bcuts\<close>, \<open>prop:h0res-Bbranch\<close>,
    \<open>lem:h0res-residue-exc\<close>, \<open>lem:h0res-a1a2\<close>, \<open>lem:h0res-baseSK\<close>,
    \<open>prop:h0res-Sbranch\<close>, \<open>prop:h0res-twocos\<close>.
  \<^bold>\<open>Appendix I\<close> (\<open>app:caseB\<close>): \<open>prop:vblock\<close>, \<open>prop:branch\<close>, \<open>cor:repair\<close>,
    \<open>prop:uphi-reduce\<close>, \<open>prop:uphi-codim3\<close>, \<open>cor:uphi-exhausted\<close>, \<open>prop:vpair11\<close>,
    \<open>cor:vpair11\<close>, \<open>prop:szero-local\<close>, \<open>prop:vpair11-graph\<close>, \<open>cor:vpair11-graph\<close>,
    \<open>cor:H11-closed\<close>, \<open>prop:vpair22\<close>, \<open>cor:vpair22\<close>, \<open>cor:vpair22-common\<close>,
    \<open>prop:vpair22-graph\<close>, \<open>cor:vpair22-graph\<close>, \<open>prop:vpair22-KLM\<close>,
    \<open>cor:vpair22-nonzero\<close>, \<open>prop:vpair22-elim\<close>, \<open>prop:vpair22-onezero\<close>,
    \<open>cor:vpair22-onezero\<close>, \<open>prop:vpair22-full\<close>, \<open>cor:vpair22-full\<close>, \<open>prop:H12zero\<close>,
    \<open>cor:H12zero\<close>, \<open>prop:Lambda-common\<close>, \<open>prop:double-param\<close>, \<open>cor:double-impossible\<close>,
    \<open>prop:Lambda-simple\<close>, \<open>cor:Lambda-remains\<close>, \<open>prop:Lambda-high\<close>,
    \<open>prop:Lambda-onefold\<close>, \<open>cor:Lambda-refined\<close>, \<open>prop:Lambda-twofold\<close>,
    \<open>cor:Lambda-twofold\<close>, \<open>cor:Lambda-closed\<close>.

  (The concrete double-root functions \<^const>\<open>astar\<close>, \<^const>\<open>bstar\<close>, \<^const>\<open>Fparam\<close>,
  \<^const>\<open>betaU\<close>, \<^const>\<open>alphaU\<close> are already defined above for \<open>prop:upair\<close> and the
  Appendix-I \<open>\<Lambda>\<^sup>(\<^sup>1\<^sup>1\<^sup>)\<close> double-root chain.)
\<close>

end
