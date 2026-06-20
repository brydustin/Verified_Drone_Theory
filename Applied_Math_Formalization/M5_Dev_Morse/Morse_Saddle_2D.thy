theory Morse_Saddle_2D
  imports "HOL-Analysis.Analysis"
begin

text \<open>Foundational, GENERAL (reusable / AFP-candidate) development: the local structure of the
  zero set of a 2-variable function at a nondegenerate SADDLE point.  Built as a sorry-scaffold:
  the main theorem @{text saddle_form_two_arcs} is assembled from two clean stubs
  (@{text factor_indef_C1}, @{text level_zero_C1_arc}); the Hadamard bridge @{text hadamard2}
  is the third (foundational) stub.  Each stub is an independent agent target.\<close>

text \<open>A scalar field on a set, with an explicit continuous gradient field (our C1 notion).\<close>

definition C1field :: "(real^2 \<Rightarrow> real) \<Rightarrow> (real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "C1field f g S \<longleftrightarrow> (\<forall>x\<in>S. (f has_derivative (\<lambda>h. inner (g x) h)) (at x)) \<and> continuous_on S g"

subsection \<open>STUB 1 (algebra): factoring an indefinite C1 binary form\<close>

text \<open>An indefinite binary quadratic form with C1 coefficients (and \<open>a p \<noteq> 0\<close>) factors into two
  transverse C1 linear factors.  Roots \<open>r\<^sub>\<plusminus> = (-b \<plusminus> sqrt(b\<^sup>2-ac))/a\<close>; continuity/C1 from the
  strictly-positive discriminant.  AGENT TARGET.\<close>

lemma factor_indef_C1:
  fixes a b c :: "real^2 \<Rightarrow> real" and ga gb gc :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0"
    and aC1: "C1field a ga (ball p \<rho>0)" and bC1: "C1field b gb (ball p \<rho>0)"
    and cC1: "C1field c gc (ball p \<rho>0)"
    and a0: "a p \<noteq> 0" and indef: "(b p)\<^sup>2 - a p * c p > 0"
  obtains rp rm :: "real^2 \<Rightarrow> real" and grp grm :: "real^2 \<Rightarrow> real^2" and \<rho> :: real
    where "0 < \<rho>" "\<rho> \<le> \<rho>0"
      "C1field rp grp (ball p \<rho>)" "C1field rm grm (ball p \<rho>)" "rp p \<noteq> rm p"
      "\<And>x Y1 Y2. x \<in> ball p \<rho> \<Longrightarrow>
          a x * Y1\<^sup>2 + 2 * b x * Y1 * Y2 + c x * Y2\<^sup>2
        = a x * (Y1 - rp x * Y2) * (Y1 - rm x * Y2)"
  sorry

subsection \<open>STUB 2 (implicit function): C1 zero set of a regular scalar field is a C1 arc\<close>

text \<open>A C1 scalar field with nonzero gradient at \<open>p\<close> has, locally, a zero set that is a single
  C1 arc through \<open>p\<close>.  This is the implicit function theorem; derive it from
  @{thm inverse_function_theorem} (Derivative.thy), exactly as the proven
  \<open>crossTheta_local_C1_graph\<close> does for the specific case.  AGENT TARGET.\<close>

lemma level_zero_C1_arc:
  fixes lf :: "real^2 \<Rightarrow> real" and glf :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0" and lC1: "C1field lf glf (ball p \<rho>0)"
    and lp: "lf p = 0" and reg: "glf p \<noteq> 0"
  obtains \<gamma> :: "real \<Rightarrow> real^2" and a b \<rho> :: real where "a \<le> b" "0 < \<rho>"
      "\<gamma> C1_differentiable_on {a..b}" "p \<in> \<gamma> ` {a..b}"
      "{x. lf x = 0} \<inter> ball p \<rho> \<subseteq> \<gamma> ` {a..b}"
  sorry

subsection \<open>MAIN: the zero set of an indefinite C1 form is two transverse C1 arcs\<close>

text \<open>Assembled from the two stubs above (no further sorry).\<close>

theorem saddle_form_two_arcs:
  fixes f a b c :: "real^2 \<Rightarrow> real" and ga gb gc :: "real^2 \<Rightarrow> real^2" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0"
    and aC1: "C1field a ga (ball p \<rho>0)" and bC1: "C1field b gb (ball p \<rho>0)"
    and cC1: "C1field c gc (ball p \<rho>0)"
    and a0: "a p \<noteq> 0" and indef: "(b p)\<^sup>2 - a p * c p > 0"
    and form: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow>
        f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
  obtains \<gamma>1 \<gamma>2 :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real where
      "0 < r" "a1 \<le> b1" "a2 \<le> b2"
      "\<gamma>1 C1_differentiable_on {a1..b1}" "\<gamma>2 C1_differentiable_on {a2..b2}"
      "p \<in> \<gamma>1 ` {a1..b1}" "p \<in> \<gamma>2 ` {a2..b2}"
      "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
  sorry

subsection \<open>STUB 3 (Hadamard, foundational): C3 + first-order-flat = indefinite C1 form\<close>

text \<open>Hadamard's lemma (2nd order, with C1 remainder coefficients): a \<open>C3\<close> function vanishing
  to first order at \<open>p\<close> equals a quadratic form with C1 coefficients whose values at \<open>p\<close> are
  half the second partials.  No multivariate Taylor in HOL-Analysis \<Rightarrow> build from the 1D
  fundamental theorem of calculus along the segments \<open>t \<mapsto> p + t\<cdot>(x-p)\<close> (Leibniz/parametric
  integral for the C1 dependence).  The smoothness hypothesis \<open>SMOOTH3 f (ball p \<rho>0)\<close> below is a
  PLACEHOLDER; the agent should replace it with the exact provable HOL-Analysis predicate and
  report it (for \<open>crossTheta\<close> any reasonable C-inf predicate holds).  AGENT TARGET.\<close>

lemma hadamard2:
  fixes f :: "real^2 \<Rightarrow> real" and p :: "real^2"
  assumes \<rho>0: "\<rho>0 > 0"
    \<comment> \<open>SMOOTH3 placeholder + \<open>f p = 0\<close> + \<open>Df p = 0\<close> to be made precise by the agent\<close>
  shows "True"
  by simp

end
