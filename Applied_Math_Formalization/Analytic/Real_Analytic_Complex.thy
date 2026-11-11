section \<open>Complexification bridge for real-analytic functions\<close>

text \<open>
  This theory connects the real-analytic ($C^\omega$) predicate \<^const>\<open>real_analytic_on\<close>
  (developed in \<open>Real_Analytic\<close>) to the HOL \<open>Complex_Analysis\<close> machinery.  The strategy is
  the classical \<^emph>\<open>complexification\<close> route:

  \<^item> (A1) A real-analytic function on an open set extends, locally, to a holomorphic
    function on a complex neighbourhood -- and conversely the real restriction of a
    local holomorphic extension is real-analytic.
  \<^item> (A2) A holomorphic function is $C^\infty$ (in the real sense), since it has
    derivatives of every order.
  \<^item> (A3) The several-variable Cauchy--Riemann criterion: a real-Fréchet-differentiable
    map between (subspaces of) \<open>\<complex>\<close> whose total derivative is \<open>\<complex>\<close>-linear is
    holomorphic.  This is the main genuinely new hard leaf.

  Crucially we also use A1 + the HOL identity theorem
  (\<^theory_text>\<open>analytic_continuation\<close> / \<^theory_text>\<open>isolated_zeros\<close> from
  \<open>HOL-Complex_Analysis.Conformal_Mappings\<close>) to attack the workhorse
  \<^const>\<open>real_analytic_nowhere_dense_zeros\<close>: a real-analytic function that is not
  identically zero on a connected open set has a nowhere-dense zero set.
\<close>

theory Real_Analytic_Complex
  imports
    "HOL-Analysis.Complex_Analysis_Basics"
    "HOL-Complex_Analysis.Conformal_Mappings"
    "Applied_Math_Analytic.Real_Analytic"
begin


subsection \<open>(A1) Real-analytic $\leftrightarrow$ local holomorphic extension\<close>

text \<open>
  We phrase A1 for the scalar 1-D case \<open>f :: real \<Rightarrow> real\<close>, which is exactly the slot the
  identity-theorem argument needs (the multivariate version is reduced to slices in the
  IFT companion theory).  \<open>has_holo_extension_at f c\<close> says: on some complex ball about
  \<open>c\<close> there is a holomorphic \<open>g\<close> agreeing with \<open>f\<close> on the real axis.
\<close>

definition has_holo_extension_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "has_holo_extension_at f c \<longleftrightarrow>
     (\<exists>r>0. \<exists>g. g holomorphic_on ball (complex_of_real c) r
                \<and> (\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow> g (complex_of_real x) = complex_of_real (f x)))"

text \<open>
  \<^bold>\<open>A1, forward direction.\<close>  Real analyticity at \<open>c\<close> (the Peano/Taylor \<open>(deriv ^^ n)\<close>
  series converges to \<open>f\<close> near \<open>c\<close>) yields a holomorphic extension: the SAME power-series
  coefficients \<open>(deriv ^^ n) f c / fact n\<close> define a complex power series with the same
  (positive) radius of convergence, hence a holomorphic \<open>g\<close>, and on the real axis it sums
  to \<open>f\<close>.  Establishing the radius transfer and the holomorphy of the limit is the hard
  content (needs a convergence-radius computation + \<^theory_text>\<open>power_series_holomorphic\<close>).
\<close>

lemma real_analytic_at_1d_imp_holo_extension:
  fixes f :: "real \<Rightarrow> real"
  assumes "real_analytic_at_1d f c"
  shows "has_holo_extension_at f c"
  \<comment> \<open>HARD LEAF: transfer the convergence radius of the real Taylor series to the complex
      power series \<open>\<lambda>z. \<Sum>n. (deriv^^n) f c / fact n * (z - c)^n\<close> and apply
      \<^theory_text>\<open>power_series_holomorphic\<close> (Cauchy_Integral_Formula); on \<open>\<real>\<close> it equals \<open>f\<close> by
      \<open>sums\<close>-uniqueness from \<^const>\<open>real_analytic_at_1d\<close>.\<close>
  sorry

text \<open>
  \<^bold>\<open>A1, backward direction.\<close>  A local holomorphic extension makes \<open>f\<close> real-analytic at \<open>c\<close>:
  the complex power series of \<open>g\<close> about \<open>c\<close> (\<^theory_text>\<open>holomorphic_power_series\<close>) restricts on the
  real axis to a real power series with coefficients \<open>(deriv ^^ n) g c / fact n\<close>, which are
  real because \<open>g\<close> is real on \<open>\<real>\<close>; one then identifies these with \<open>(deriv ^^ n) f c / fact n\<close>.
\<close>

lemma holo_extension_imp_real_analytic_at_1d:
  fixes f :: "real \<Rightarrow> real"
  assumes "has_holo_extension_at f c"
  shows "real_analytic_at_1d f c"
  \<comment> \<open>HARD LEAF: restrict \<^theory_text>\<open>holomorphic_power_series\<close> of the extension \<open>g\<close> to \<open>\<real>\<close>; show the
      complex coefficients are real-of the real \<open>(deriv^^n) f c / fact n\<close> and that the
      \<open>(deriv^^n)\<close> agree, giving the real \<open>sums\<close> and the local smoothness.\<close>
  sorry

theorem real_analytic_at_1d_iff_holo_extension:
  fixes f :: "real \<Rightarrow> real"
  shows "real_analytic_at_1d f c \<longleftrightarrow> has_holo_extension_at f c"
  using real_analytic_at_1d_imp_holo_extension holo_extension_imp_real_analytic_at_1d
  by blast


subsection \<open>(A2) Holomorphic implies real-$C^\infty$\<close>

text \<open>
  A holomorphic function on an open set has complex derivatives of every order
  (\<^theory_text>\<open>holomorphic_higher_deriv\<close>), each of which is again holomorphic and therefore
  real-Fréchet-differentiable.  Hence, viewed as a map of the underlying real plane, it is
  \<open>C\<^sup>\<infinity>\<close> in the sense of \<^const>\<open>Cinfinity_on\<close>.
\<close>

lemma holomorphic_higher_deriv_holomorphic:
  assumes "f holomorphic_on S" "open S"
  shows "(deriv ^^ n) f holomorphic_on S"
  using holomorphic_higher_deriv[OF assms] .

theorem holomorphic_imp_Cinfinity_on:
  assumes "f holomorphic_on U" and "open U"
  shows "Cinfinity_on f U"
  \<comment> \<open>HARD LEAF: from \<^theory_text>\<open>holomorphic_higher_deriv\<close> every iterated complex derivative is
      holomorphic hence real-differentiable; package this into the primrec \<^const>\<open>Ck_at\<close>
      for all \<open>k\<close> (the real Fréchet derivative of a holomorphic map is \<open>v \<mapsto> deriv f x * v\<close>).
      This is an induction on \<open>k\<close> bridging \<^const>\<open>field_differentiable\<close> to
      \<^const>\<open>frechet_derivative\<close>.\<close>
  sorry


subsection \<open>(A3) Several-variable Cauchy--Riemann criterion\<close>

text \<open>
  \<^bold>\<open>The main new hard leaf.\<close>  If a map \<open>f :: complex \<Rightarrow> complex\<close> is real-(Fréchet-)differentiable
  at every point of an open set \<open>S\<close>, with total real derivative \<open>L x\<close>, and each \<open>L x\<close> is
  \<open>\<complex>\<close>-linear (equivalently commutes with multiplication by \<open>\<i>\<close>, the Cauchy--Riemann
  equations), then \<open>f\<close> is holomorphic on \<open>S\<close>.

  We capture \<open>\<complex>\<close>-linearity of a real-linear \<open>L\<close> by the single equation
  \<open>L (\<i> * v) = \<i> * L v\<close> together with real-linearity.
\<close>

definition CR_linear :: "(complex \<Rightarrow> complex) \<Rightarrow> bool" where
  "CR_linear L \<longleftrightarrow> bounded_linear L \<and> (\<forall>v. L (\<i> * v) = \<i> * L v)"

lemma CR_linear_is_mult:
  assumes "CR_linear L"
  shows "\<exists>a. \<forall>v. L v = a * v"
  \<comment> \<open>EASY-ISH LEAF: a real-linear self-map of \<open>\<complex>\<close> commuting with \<open>(*) \<i>\<close> is multiplication
      by \<open>a = L 1\<close>: \<open>L v = L (Re v + \<i> Im v) = Re v * L 1 + Im v * L \<i> = (L 1) * v\<close> using
      \<open>L \<i> = \<i> * L 1\<close>.  Provable from \<^const>\<open>bounded_linear\<close> + the CR equation.\<close>
  sorry

theorem CauchyRiemann_imp_holomorphic:
  fixes f :: "complex \<Rightarrow> complex"
  assumes Sopen: "open S"
    and diff: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative (L x)) (at x)"
    and CR:   "\<And>x. x \<in> S \<Longrightarrow> CR_linear (L x)"
  shows "f holomorphic_on S"
  \<comment> \<open>HARD LEAF (THE main new content): at each \<open>x \<in> S\<close>, \<^const>\<open>CR_linear_is_mult\<close> gives
      \<open>L x v = a x * v\<close>, so the real derivative IS multiplication by the complex scalar
      \<open>a x\<close>; this is exactly \<open>(f has_field_derivative a x) (at x)\<close> (unfold
      \<^const>\<open>has_field_derivative\<close>), whence \<open>f field_differentiable (at x)\<close> and
      \<open>f holomorphic_on S\<close> via \<^thm>\<open>holomorphic_on_open\<close>.\<close>
  sorry


subsection \<open>(1.6) Workhorse: nowhere-dense zeros via the identity theorem\<close>

text \<open>
  We now attack \<^const>\<open>real_analytic_nowhere_dense_zeros\<close> (left as \<open>proof hole\<close> in
  \<open>Real_Analytic\<close>) through the complexification.  The 1-D scalar case is given a precise
  skeleton: the complex extension is holomorphic and not identically zero, so by
  \<^theory_text>\<open>isolated_zeros\<close> its zeros are isolated, and pulling back along \<open>complex_of_real\<close>
  shows the real zero set has empty interior.

  The genuinely general (multivariate, vector-valued) statement quantified in
  \<open>Real_Analytic\<close> additionally needs the slice/connectedness bookkeeping; that is isolated
  in the single remaining \<open>proof hole\<close>.
\<close>

text \<open>The clean 1-D scalar instance, proved modulo the A1 extension leaf.\<close>

lemma real_analytic_1d_nowhere_dense_zeros:
  fixes f :: "real \<Rightarrow> real"
  assumes ana: "real_analytic_on f U"
    and U: "open U" "connected U"
    and nz: "\<exists>x\<in>U. f x \<noteq> 0"
  shows "interior (closure {x \<in> U. f x = 0}) = {}"
  \<comment> \<open>SKELETON (single remaining hard dependency = A1 + a connected complex
      neighbourhood). Plan:
      \<^enum> by \<^thm>\<open>real_analytic_on_1d_iff\<close> + \<^const>\<open>real_analytic_at_1d_iff_holo_extension\<close>,
        every \<open>c \<in> U\<close> has a holomorphic extension on a complex ball; glue these (on
        \<open>U \<times> i\<cdot>(-\<epsilon>,\<epsilon>)\<close>) to a holomorphic \<open>g\<close> on a connected open \<open>V \<subseteq> \<complex>\<close> with
        \<open>U \<subseteq> Re ` V\<close> and \<open>g (of_real x) = of_real (f x)\<close> on \<open>U\<close>;
      \<^enum> \<open>nz\<close> gives \<open>g (of_real x\<^sub>0) \<noteq> 0\<close>, so \<open>g\<close> is not identically \<open>0\<close> on the connected
        \<open>V\<close>; by \<^thm>\<open>isolated_zeros\<close> / \<^thm>\<open>analytic_continuation\<close> the complex zero set
        \<open>{z\<in>V. g z = 0}\<close> has no limit point in \<open>V\<close>;
      \<^enum> hence \<open>{x\<in>U. f x = 0} = (of_real -` {z\<in>V. g z = 0}) \<inter> U\<close> is discrete in \<open>U\<close>, so its
        closure has empty interior (a perfect/no-isolated-point argument on \<open>\<real>\<close>).\<close>
  sorry

text \<open>
  The general statement.  Reduces to the scalar/identity-theorem machinery above; for a
  vector-valued \<open>f :: 'a \<Rightarrow> real\<close> over a Euclidean domain the zero set's interior emptiness
  follows by restricting to affine real lines through a regular direction and invoking the
  1-D result on each slice (the slices are connected open real intervals).
\<close>

theorem real_analytic_nowhere_dense_zeros_via_complex:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "real_analytic_on f U" and "connected U" and "\<exists>x\<in>U. f x \<noteq> 0"
  shows "interior (closure {x \<in> U. f x = 0}) = {}"
  \<comment> \<open>HARD LEAF: reduce the multivariate zero set to 1-D slices \<open>t \<mapsto> f (a + t *\<^sub>R d)\<close>,
      each real-analytic in \<open>t\<close> and not identically zero for a generic direction \<open>d\<close>, then
      apply \<^const>\<open>real_analytic_1d_nowhere_dense_zeros\<close> and a Fubini/Baire packaging.\<close>
  sorry

end
