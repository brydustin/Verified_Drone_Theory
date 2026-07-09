section \<open>A $C^\infty$ Function That Is Not Analytic (the flat bump)\<close>

text \<open>
  Item (1c) of the real-analytic development: a witness that $C^\infty \neq C^\omega$.
  It is separated into its own theory because it reuses the AFP
  \<open>Smooth_Manifolds.Bump_Function\<close>, whose heavy import perturbs the elaboration of the
  core \<open>Real_Analytic\<close> definitions (notably \<open>ra_monomial\<close>).
  Keeping it here leaves the core theory light and uncoupled.
\<close>

theory Real_Analytic_Bump
  imports
    Real_Analytic
    "Smooth_Manifolds.Bump_Function"
begin

text \<open>The classic flat bump \<open>x \<mapsto> exp(-1/x)\<close> for \<open>x>0\<close>, \<open>0\<close> otherwise: smooth everywhere,
  but all derivatives vanish at \<open>0\<close> while the function does not, so it is not analytic there.\<close>

definition exp_bump :: "real \<Rightarrow> real" where
  "exp_bump x = (if 0 < x then exp (- (1 / x)) else 0)"

text \<open>This is exactly the AFP flat function @{term Bump_Function.f}
  (since @{term "inverse t = 1 / t"}), so we reuse its smoothness wholesale.\<close>

lemma exp_bump_eq_Bump_f: "exp_bump = Bump_Function.f"
proof (rule ext)
  fix x :: real
  show "exp_bump x = Bump_Function.f x"
    by (simp add: exp_bump_def Bump_Function.f_def inverse_eq_divide)
qed

lemma exp_bump_Cinfinity: "Cinfinity_on exp_bump UNIV"
proof -
  have Ck: "Ck_on k exp_bump UNIV" for k
  proof -
    have "higher_differentiable_on UNIV exp_bump k"
      unfolding exp_bump_eq_Bump_f by (rule Bump_Function.f_higher_differentiable_on)
    thus ?thesis
      by (simp add: Ck_on_iff_higher_differentiable_on[OF open_UNIV])
  qed
  show ?thesis
    unfolding Cinfinity_on_def Cinfinity_at_def
  proof (intro conjI ballI allI)
    show "open (UNIV :: real set)" by simp
  next
    fix x :: real and k assume "x \<in> UNIV"
    from Ck[of k] show "Ck_at k exp_bump x"
      by (simp add: Ck_on_def)
  qed
qed

text \<open>All derivatives of the flat bump vanish at \<open>0\<close> (it is flat there):
  the AFP development establishes this for the \<open>nth_derivative\<close> form, and
  @{thm [source] nth_derivative_eq_kth_deriv} transports it to our \<open>(deriv ^^ n)\<close>.\<close>

lemma exp_bump_flat_deriv: "(deriv ^^ n) exp_bump 0 = 0"
proof -
  have "\<forall>t\<le>0. nth_derivative n Bump_Function.f t 1 = 0"
    using Bump_Function.f_nth_derivative_cases[of n] by blast
  then have "nth_derivative n Bump_Function.f 0 1 = 0" by simp
  moreover have "nth_derivative n Bump_Function.f 0 1 = (deriv ^^ n) Bump_Function.f 0"
    by (simp add: nth_derivative_eq_kth_deriv[OF open_UNIV
            Bump_Function.f_higher_differentiable_on UNIV_I])
  ultimately have "(deriv ^^ n) Bump_Function.f 0 = 0" by simp
  thus ?thesis by (simp add: exp_bump_eq_Bump_f)
qed

lemma exp_bump_not_real_analytic: "\<not> real_analytic_on exp_bump (ball 0 1)"
proof
  assume A: "real_analytic_on exp_bump (ball (0::real) 1)"
  have "0 \<in> ball (0::real) 1" by simp
  with A have "real_analytic_at_1d exp_bump 0"
    using real_analytic_on_1d_iff[of exp_bump "ball 0 1"] by blast
  then obtain r where r: "0 < r"
    and TS: "\<And>x. \<bar>x - 0\<bar> < r \<Longrightarrow>
              (\<lambda>n. (deriv ^^ n) exp_bump 0 / fact n * (x - 0) ^ n) sums exp_bump x"
    unfolding real_analytic_at_1d_def by blast
  \<comment> \<open>A strictly positive point inside the convergence radius.\<close>
  define x0 where "x0 = r / 2"
  have x0_pos: "0 < x0" using r by (simp add: x0_def)
  have "\<bar>x0 - 0\<bar> = x0" using x0_pos by simp
  also have "x0 < r" using r unfolding x0_def by linarith
  finally have x0_lt: "\<bar>x0 - 0\<bar> < r" .
  \<comment> \<open>All Taylor coefficients vanish, so the series is identically zero and sums to 0.\<close>
  have "(\<lambda>n. (deriv ^^ n) exp_bump 0 / fact n * (x0 - 0) ^ n) = (\<lambda>n. 0)"
    by (simp add: exp_bump_flat_deriv)
  with TS[OF x0_lt] have z0: "(\<lambda>n. (0::real)) sums exp_bump x0" by simp
  have "exp_bump x0 = 0"
    using sums_unique2[OF z0 sums_zero] by simp
  \<comment> \<open>But the bump is strictly positive there.\<close>
  moreover have "exp_bump x0 = exp (- (1 / x0))"
    using x0_pos by (simp add: exp_bump_def)
  ultimately show False by simp
qed

end
