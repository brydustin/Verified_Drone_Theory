theory Nonemptiness_Robust
  imports Nonemptiness_Capstone "Applied_Math_HigherDiff.Higher_Differentiability_Multi"
begin

section \<open>The robust feasible set (concrete \<open>thm:final\<close> objects)\<close>

text \<open>
  This theory builds the concrete objects of the flagship theorem \<open>thm:final\<close>
  directly from the array factor \<^const>\<open>af\<close>, so that the final statement reads like
  the paper.  Part 1: the sidelobe power \<open>U\<close>, the feasible set \<open>\<F>\<close>, and the proof
  that \<open>\<F>\<close> is \<^emph>\<open>compact\<close> (closed feasibility constraints inside a bounded ball,
  Heine--Borel).
\<close>


subsection \<open>The sidelobe power \<open>U(\<bm>x,\<omega>) = g(\<omega>)\<bar>A(\<bm>x,\<omega>)\<bar>\<^sup>2\<close>\<close>

definition Upow ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> (real^2)^'n \<Rightarrow> real^2 \<Rightarrow> real"
  where "Upow cvec g x \<omega> = g \<omega> * (cmod (af cvec x \<omega>))\<^sup>2"

text \<open>The array factor, hence the power, is continuous in the configuration \<open>\<bm>x\<close>.\<close>

lemma continuous_on_af_config:
  fixes \<omega> :: "real^2" and cvec :: "real^2 \<Rightarrow> real^2"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. af cvec x \<omega>)"
  unfolding af_def
  by (intro continuous_intros continuous_on_cis)

lemma continuous_on_Upow_config:
  fixes \<omega> :: "real^2" and cvec :: "real^2 \<Rightarrow> real^2" and g :: "real^2 \<Rightarrow> real"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. Upow cvec g x \<omega>)"
  unfolding Upow_def
  by (intro continuous_intros continuous_on_af_config)


subsection \<open>The feasibility constraints \<open>c\<close>, \<open>N\<close>, \<open>P\<close>\<close>

text \<open>TeX \<S>``Existence of Global Minimizer'' (L426):
  \<open>\<F> = c\<^sup>-\<^sup>1({0}) \<inter> N\<^sup>-\<^sup>1([0,\<delta>\<^sub>null]) \<inter> P\<^sup>-\<^sup>1([p\<^sub>m\<^sub>i\<^sub>n, \<bar>e(\<theta>\<^sub>0)\<bar>\<^sup>2N\<^sup>2]) \<inter> B\<^sub>R\<close>, with the spacing
  penalty \<open>c(\<bm>x) = \<Sum>\<^sub>n\<^sub>\<noteq>\<^sub>m max{0, d\<^sub>min - \<bar>r'\<^sub>n - r'\<^sub>m\<bar>}\<close> (so \<open>c(\<bm>x)=0\<close> iff every spacing
  \<open>\<ge> d\<^sub>min\<close>), the null power \<open>N(\<bm>x) = U(\<bm>x,\<omega>\<^sub>null)\<close> and the main-beam power
  \<open>P(\<bm>x) = U(\<bm>x,\<omega>\<^sub>0)\<close>.  The inter-element distance uses the beam-focusing height
  \<open>z = (Ax + By)/D\<close>.\<close>

definition spdist :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  \<comment> \<open>\<open>\<bar>r'\<^sub>n - r'\<^sub>m\<bar>\<close> with \<open>z = (Ax + By)/D\<close>\<close>
  "spdist A B D p q =
     sqrt ((p $ 1 - q $ 1)\<^sup>2 + (p $ 2 - q $ 2)\<^sup>2
            + ((A * (p $ 1 - q $ 1) + B * (p $ 2 - q $ 2)) / D)\<^sup>2)"

definition cpen :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  \<comment> \<open>the spacing penalty \<open>c\<close>\<close>
  "cpen dmin A B D x =
     (\<Sum>p \<in> {p. fst p \<noteq> snd p}. max 0 (dmin - spdist A B D (x $ fst p) (x $ snd p)))"

lemma continuous_on_spdist_config:
  fixes n m :: "'n::finite"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. spdist A B D (x $ n) (x $ m))"
  \<comment> \<open>\<open>/D\<close> rewritten as \<open>\<cdot> inverse D\<close>, so no \<open>D \<noteq> 0\<close> side-condition arises\<close>
  unfolding spdist_def divide_inverse by (intro continuous_intros)

lemma continuous_on_cpen:
  "continuous_on UNIV (\<lambda>x::(real^2)^'n. cpen dmin A B D x)"
  unfolding cpen_def
proof (intro continuous_on_sum)
  fix p :: "'n \<times> 'n"
  show "continuous_on UNIV
          (\<lambda>x::(real^2)^'n. max 0 (dmin - spdist A B D (x $ fst p) (x $ snd p)))"
    by (intro continuous_intros continuous_on_spdist_config)
qed


subsection \<open>The feasible set \<open>\<F>\<close> and its compactness\<close>

definition Ffeas ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((real^2)^'n) set"
  where
  "Ffeas cvec g R dmin A B D \<omega>null \<omega>0 \<delta>null pmin =
       (cpen dmin A B D) -` {0}
     \<inter> (\<lambda>x. Upow cvec g x \<omega>null) -` {0 .. \<delta>null}
     \<inter> (\<lambda>x. Upow cvec g x \<omega>0) -` {pmin .. g \<omega>0 * (real CARD('n))\<^sup>2}
     \<inter> cball 0 R"

theorem Ffeas_compact:
  "compact (Ffeas cvec g R dmin A B D \<omega>null \<omega>0 \<delta>null pmin :: ((real^2)^'n) set)"
proof -
  \<comment> \<open>each constraint is the preimage of a closed set under a continuous map\<close>
  have cc: "closed ((cpen dmin A B D :: (real^2)^'n \<Rightarrow> real) -` {0})"
    by (intro closed_vimage continuous_on_cpen closed_singleton)
  have cN: "closed ((\<lambda>x::(real^2)^'n. Upow cvec g x \<omega>null) -` {0 .. \<delta>null})"
    by (intro closed_vimage continuous_on_Upow_config closed_atLeastAtMost)
  have cP: "closed ((\<lambda>x::(real^2)^'n. Upow cvec g x \<omega>0)
                     -` {pmin .. g \<omega>0 * (real CARD('n))\<^sup>2})"
    by (intro closed_vimage continuous_on_Upow_config closed_atLeastAtMost)
  \<comment> \<open>the three constraints intersect to a closed set\<close>
  have clo: "closed ((cpen dmin A B D :: (real^2)^'n \<Rightarrow> real) -` {0}
                    \<inter> (\<lambda>x. Upow cvec g x \<omega>null) -` {0 .. \<delta>null}
                    \<inter> (\<lambda>x. Upow cvec g x \<omega>0) -` {pmin .. g \<omega>0 * (real CARD('n))\<^sup>2})"
    by (intro closed_Int cc cN cP)
  \<comment> \<open>\<open>\<F>\<close> is that closed set intersected with the compact ball \<open>B\<^sub>R\<close>\<close>
  show ?thesis
    unfolding Ffeas_def by (rule closed_Int_compact[OF clo compact_cball])
qed


subsection \<open>\<open>\<F>\<close> has nonempty interior: a ball around any strictly feasible point\<close>

text \<open>TeX Remark ``ball\_inside\_F'' (L566): for a strictly feasible \<open>x\<^sup>\<dagger>\<close> --- all spacings
  \<open>> d\<^sub>min\<close>, \<open>N(x\<^sup>\<dagger>) < \<delta>\<^sub>null\<close>, \<open>p\<^sub>min < P(x\<^sup>\<dagger>)\<close>, \<open>x\<^sup>\<dagger> \<in> B\<^sub>R\<^sup>\<circ>\<close> --- a whole ball \<open>B\<^sub>\<rho>(x\<^sup>\<dagger>) \<subseteq> \<F>\<close>.
  The upper power constraint \<open>P \<le> \<bar>e(\<theta>\<^sub>0)\<bar>\<^sup>2 N\<^sup>2\<close> holds \<^emph>\<open>globally\<close> because \<open>\<bar>A\<bar> \<le> N\<close>.\<close>

lemma cmod_af_le_card:
  "cmod (af cvec (x::(real^2)^'n) \<omega>) \<le> real CARD('n)"
proof -
  have "cmod (af cvec x \<omega>) \<le> (\<Sum>n\<in>(UNIV::'n set). cmod (cis (- (cvec \<omega> \<bullet> x $ n))))"
    unfolding af_def by (rule norm_sum)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). 1)" by simp
  also have "\<dots> = real CARD('n)" by simp
  finally show ?thesis .
qed

lemma Upow_nonneg:
  assumes "0 \<le> g \<omega>" shows "0 \<le> Upow cvec g x \<omega>"
  unfolding Upow_def using assms by simp

lemma Upow_le_max:
  assumes "0 \<le> g \<omega>"
  shows "Upow cvec g (x::(real^2)^'n) \<omega> \<le> g \<omega> * (real CARD('n))\<^sup>2"
proof -
  have "(cmod (af cvec x \<omega>))\<^sup>2 \<le> (real CARD('n))\<^sup>2"
    by (rule power_mono[OF cmod_af_le_card norm_ge_zero])
  hence "g \<omega> * (cmod (af cvec x \<omega>))\<^sup>2 \<le> g \<omega> * (real CARD('n))\<^sup>2"
    by (rule mult_left_mono[OF _ assms])
  thus ?thesis unfolding Upow_def .
qed

lemma ball_inside_Ffeas:
  fixes xbar :: "(real^2)^'n"
  assumes gnull: "0 \<le> g \<omega>null" and g0: "0 \<le> g \<omega>0"
    and spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (xbar $ fst p) (xbar $ snd p)"
    and Nlt: "Upow cvec g xbar \<omega>null < \<delta>null"
    and Pgt: "pmin < Upow cvec g xbar \<omega>0"
    and inR: "xbar \<in> ball 0 R"
  shows "\<exists>\<rho>>0. ball xbar \<rho> \<subseteq> Ffeas cvec g R dmin A B D \<omega>null \<omega>0 \<delta>null pmin"
proof -
  define Usp where
    "Usp = {x::(real^2)^'n. \<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (x$fst p)(x$snd p)}"
  have op_sp: "open Usp"
  proof -
    have "Usp = (\<Inter>p\<in>{p::'n\<times>'n. fst p \<noteq> snd p}. {x. dmin < spdist A B D (x$fst p)(x$snd p)})"
      unfolding Usp_def by auto
    moreover have "open \<dots>"
    proof (rule open_INT)
      show "finite {p::'n\<times>'n. fst p \<noteq> snd p}" by simp
      show "\<forall>p\<in>{p::'n\<times>'n. fst p \<noteq> snd p}.
              open {x::(real^2)^'n. dmin < spdist A B D (x$fst p)(x$snd p)}"
        by (intro ballI open_Collect_less continuous_on_const continuous_on_spdist_config)
    qed
    ultimately show ?thesis by simp
  qed
  define U where
    "U = Usp \<inter> {x. Upow cvec g x \<omega>null < \<delta>null}
             \<inter> {x. pmin < Upow cvec g x \<omega>0} \<inter> ball 0 R"
  have opU: "open U"
    unfolding U_def
    by (intro open_Int op_sp open_Collect_less continuous_on_Upow_config
              continuous_on_const open_ball)
  have xU: "xbar \<in> U"
    unfolding U_def Usp_def using spac Nlt Pgt inR by simp
  have subF: "U \<subseteq> Ffeas cvec g R dmin A B D \<omega>null \<omega>0 \<delta>null pmin"
  proof
    fix x assume xU': "x \<in> U"
    have "cpen dmin A B D x = 0"
      unfolding cpen_def
    proof (intro sum.neutral ballI)
      fix p :: "'n \<times> 'n" assume "p \<in> {p. fst p \<noteq> snd p}"
      hence "dmin < spdist A B D (x$fst p)(x$snd p)"
        using xU' unfolding U_def Usp_def by simp
      thus "max 0 (dmin - spdist A B D (x$fst p)(x$snd p)) = 0" by simp
    qed
    hence c0: "x \<in> (cpen dmin A B D) -` {0}" by simp
    have "0 \<le> Upow cvec g x \<omega>null"
      unfolding Upow_def by (intro mult_nonneg_nonneg gnull zero_le_power2)
    moreover have "Upow cvec g x \<omega>null < \<delta>null" using xU' unfolding U_def by simp
    ultimately have cN: "x \<in> (\<lambda>x. Upow cvec g x \<omega>null) -` {0..\<delta>null}" by simp
    have "pmin < Upow cvec g x \<omega>0" using xU' unfolding U_def by simp
    moreover have "Upow cvec g x \<omega>0 \<le> g \<omega>0 * (real CARD('n))\<^sup>2"
      by (rule Upow_le_max[where g=g and \<omega>=\<omega>0, OF g0])
    ultimately have cP: "x \<in> (\<lambda>x. Upow cvec g x \<omega>0) -` {pmin .. g \<omega>0 * (real CARD('n))\<^sup>2}"
      by simp
    have "x \<in> ball 0 R" using xU' unfolding U_def by simp
    hence cR: "x \<in> cball 0 R" using ball_subset_cball by blast
    from c0 cN cP cR show "x \<in> Ffeas cvec g R dmin A B D \<omega>null \<omega>0 \<delta>null pmin"
      unfolding Ffeas_def by simp
  qed
  obtain \<rho> where "0 < \<rho>" "ball xbar \<rho> \<subseteq> U" using openE[OF opU xU] by blast
  thus ?thesis using subF by blast
qed


subsection \<open>The robust sets \<open>X\<^sub>r\<^sub>o\<^sub>b\<^sub>u\<^sub>s\<^sub>t(\<epsilon>,\<kappa>)\<close>, \<open>X\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>, and \<open>\<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>\<close>

text \<open>TeX (D_edit_May18, \eqref{X0def}/\eqref{F0}, the \<^emph>\<open>active 2-D formulation\<close>, L1281/L1288).
  With the full 2-D angle \<open>\<omega> = (\<theta>,\<phi>)\<close>, the gradient \<open>\<nabla>\<^sub>\<Omega>U\<close> (a \<open>real^2\<close>) and the \<open>2\<times>2\<close>
  Hessian \<open>H = \<nabla>\<^sup>2\<^sub>\<Omega>U\<close>, both built from the actual pattern \<open>U_cart\<close> through
  Higher_Differentiability_Multi:
  \<^item> \<open>X\<^sub>r\<^sub>o\<^sub>b\<^sub>u\<^sub>s\<^sub>t(\<epsilon>,\<kappa>) = {\<bm>x : \<parallel>\<nabla>\<^sub>\<Omega>U(\<bm>x,\<omega>)\<parallel> \<ge> \<kappa> \<forall> \<omega> \<in> \<partial>B\<^sub>\<epsilon>(ctr)}\<close>;
  \<^item> \<open>X\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = {\<bm>x \<in> X\<^sub>r\<^sub>o\<^sub>b\<^sub>u\<^sub>s\<^sub>t : \<parallel>\<nabla>\<^sub>\<Omega>U(\<bm>x,y)\<parallel> + \<sigma>\<^sub>m\<^sub>i\<^sub>n(H(\<bm>x,y)) \<ge> \<xi> on \<Omega>\<^sup>~ = \<Omega> \\ B\<^sub>\<epsilon>(ctr)}\<close>;
  \<^item> \<open>\<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = \<F> \<inter> X\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.
  Here \<open>\<parallel>\<cdot>\<parallel>\<close> is the Euclidean norm on \<open>real^2\<close> and \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n\<close> is the smallest singular value
  of the symmetric \<open>2\<times>2\<close> Hessian.  \<open>ctr\<close> is the design direction \<open>(\<theta>\<^sub>0,\<phi>\<^sub>0)\<close>;
  \<open>\<partial>B\<^sub>\<epsilon>(ctr) = sphere ctr \<epsilon>\<close>, \<open>B\<^sub>\<epsilon>(ctr) = ball ctr \<epsilon>\<close>.  Crucially \<open>X\<^sub>0\<close> now depends on the real
  derivatives of \<^const>\<open>U_cart\<close> (via \<open>gradU\<close>/\<open>HessU\<close> below), and the nondegeneracy
  margin \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> is exactly the \<open>det \<nabla>\<^sup>2U \<noteq> 0\<close> condition the determinant work secures.\<close>

definition angle2 :: "real \<Rightarrow> real \<Rightarrow> real^2" where
  \<comment> \<open>the angle point \<open>(\<theta>,\<phi>)\<close>\<close>
  "angle2 \<theta> \<phi> = (\<chi> i. if i = 1 then \<theta> else \<phi>)"

definition gradU ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> planar"
  where \<comment> \<open>\<open>\<nabla>\<^sub>\<omega> U_cart\<close> from Higher_Differentiability_Multi\<close>
  "gradU cvec gain x \<omega> = \<nabla> (U_cart cvec gain x) \<omega>"

definition HessU ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> real^2^2"
  where \<comment> \<open>\<open>\<nabla>\<^sup>2\<^sub>\<omega> U_cart\<close> (\<open>hess_fun\<close>) from Higher_Differentiability_Multi\<close>
  "HessU cvec gain x \<omega> = \<nabla>\<^sup>2 (U_cart cvec gain x) \<omega>"

text \<open>\<^bold>\<open>Bridge: \<open>gradU\<close> is the genuine gradient of the concrete \<open>U_cart\<close>.\<close>  The abstract
  \<open>\<nabla>\<close> (\<open>grad_fun\<close>) is a \<open>THE\<close>-value, well-defined only where \<open>U_cart\<close> is differentiable
  in \<open>\<omega>\<close>.  Under differentiability of \<open>cvec\<close> and \<open>gain\<close> at \<open>\<omega>\<close> --- which the \<^emph>\<open>proven\<close>
  @{thm has_derivative_U_cart} turns into a Fréchet derivative \<open>dU_cart\<close> --- the gradient
  is the explicit vector assembled from \<open>dU_cart\<close>'s action on the coordinate axes.  This
  ties \<open>gradU\<close> (hence \<open>Phibad\<close>) to the actual array-factor derivatives, not a floating
  \<open>THE\<close>.\<close>

lemma gradU_explicit:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and dc :: "angle \<Rightarrow> planar" and dgain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes "(cvec has_derivative dc) (at \<omega>)"
    and "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega>
           = (\<Sum>i\<in>UNIV. dU_cart cvec dc gain dgain x \<omega> (axis i 1) *\<^sub>R axis i 1)"
proof -
  have "((U_cart cvec gain x) has_derivative dU_cart cvec dc gain dgain x \<omega>) (at \<omega>)"
    using has_derivative_U_cart[OF assms, where x = x] by simp
  from has_derivative_to_gradient[OF this]
  have "GRAD (U_cart cvec gain x) \<omega>
          :> (\<Sum>i\<in>UNIV. dU_cart cvec dc gain dgain x \<omega> (axis i 1) *\<^sub>R axis i 1)" .
  thus ?thesis unfolding gradU_def by (rule grad_fun_eq)
qed

text \<open>\<^bold>\<open>Bridge: \<open>HessU\<close> is the genuine Hessian (the Jacobian of the gradient field).\<close>
  Like \<open>\<nabla>\<close>, the abstract \<open>\<nabla>\<^sup>2\<close> (\<open>hess_fun\<close>) is a \<open>THE\<close>-value, meaningful only where the
  gradient field \<open>gradU cvec gain x = \<nabla>(U_cart cvec gain x)\<close> is itself differentiable in
  \<open>\<omega>\<close> --- i.e. where \<open>U_cart\<close> is \<open>C\<^sup>2\<close>.  Given that derivative \<open>G\<close> (a consequence of \<open>C\<^sup>2\<close>
  smoothness of the concrete \<open>cvec\<close>/\<open>gain\<close>), \<open>HessU\<close> is exactly its matrix.  This ties
  \<open>HessU\<close> (hence the Hessian-determinant component of \<open>Phibad\<close>) to the genuine second
  derivative of the real pattern, not a floating \<open>THE\<close>.\<close>

lemma HessU_explicit:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle and G :: "planar \<Rightarrow> planar"
  assumes "(gradU cvec gain x has_derivative G) (at \<omega>)"
  shows "HessU cvec gain x \<omega> = matrix G"
proof -
  have linG: "linear G"
    using has_derivative_bounded_linear[OF assms] bounded_linear.linear by blast
  have fun_eq: "\<nabla> (U_cart cvec gain x) = gradU cvec gain x"
    by (rule ext) (simp add: gradU_def)
  have mg: "(\<lambda>v. matrix G *v v) = G"
    by (simp add: linG)
  have "(\<nabla> (U_cart cvec gain x) has_derivative (\<lambda>v. matrix G *v v)) (at \<omega>)"
    using assms unfolding fun_eq mg .
  hence "HESS (U_cart cvec gain x) \<omega> :> matrix G" unfolding has_hessian_def .
  thus ?thesis unfolding HessU_def by (rule hess_fun_eq)
qed

text \<open>\<^bold>\<open>Dropping the assumption, step 1.\<close>  The per-point hypothesis of @{thm HessU_explicit}
  (that the gradient field has a derivative at \<open>\<omega>\<close>) is \<^emph>\<open>false\<close> for an arbitrary \<open>cvec\<close>/\<open>gain\<close>
  but holds wherever \<open>U_cart\<close> is \<open>C\<^sup>2\<close>.  Under \<open>U_cart \<in> C\<^sup>2\<close> on a neighbourhood the gradient
  field \<^emph>\<open>is\<close> differentiable, with derivative the Hessian matrix --- so \<open>gradU\<close> is
  differentiable everywhere on the \<open>C\<^sup>2\<close> locus and \<open>HessU\<close> is the genuine Hessian there.
  The remaining drops are \<open>U_cart \<in> C\<^sup>2 \<Longleftarrow> cvec, gain \<in> C\<^sup>2\<close> (AFP closure lemmas) and,
  for the concrete pattern, \<open>cvec\<^sub>0, \<bar>e\<bar>\<^sup>2\<close> smooth --- leaving no assumption at all.\<close>

lemma gradU_has_derivative_of_C2:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes "Ck_on 2 (U_cart cvec gain x) U" and "\<omega> \<in> U"
  shows "(gradU cvec gain x has_derivative (\<lambda>v. HessU cvec gain x \<omega> *v v)) (at \<omega>)"
proof -
  have H: "HESS (U_cart cvec gain x) \<omega> :> \<nabla>\<^sup>2 (U_cart cvec gain x) \<omega>"
    by (rule Ck_2_imp_hessian_exists[OF assms])
  have gfun: "gradU cvec gain x = \<nabla> (U_cart cvec gain x)"
    by (rule ext) (simp add: gradU_def)
  from H have D: "(\<nabla> (U_cart cvec gain x)
                    has_derivative (\<lambda>v. \<nabla>\<^sup>2 (U_cart cvec gain x) \<omega> *v v)) (at \<omega>)"
    unfolding has_hessian_def .
  show ?thesis unfolding gfun HessU_def by (rule D)
qed

text \<open>\<^bold>\<open>Dropping the assumption, step 2: smoothness of the building blocks.\<close>  Toward
  \<open>U_cart \<in> C\<^sup>2\<close> (hence \<open>gradU\<close> differentiable everywhere) for our actual function, we first
  record that the trigonometric building blocks of the array factor are \<open>C\<^sup>\<infinity>\<close>.  \<open>sin\<close> and
  \<open>cos\<close> are \<open>C\<^sup>n\<close> for every \<open>n\<close> (mutual induction: \<open>sin' = cos\<close>, \<open>cos' = -sin\<close>); hence so is
  \<open>cis t = cos t \<cdot> 1 + sin t \<cdot> \<ii>\<close>.\<close>

lemma sin_cos_higher_differentiable_on:
  "higher_differentiable_on UNIV (sin::real \<Rightarrow> real) n
   \<and> higher_differentiable_on UNIV (cos::real \<Rightarrow> real) n"
proof (induction n)
  case 0
  have a: "higher_differentiable_on UNIV (sin::real \<Rightarrow> real) 0"
    by (simp only: higher_differentiable_on.simps(1)) (intro continuous_intros)
  have b: "higher_differentiable_on UNIV (cos::real \<Rightarrow> real) 0"
    by (simp only: higher_differentiable_on.simps(1)) (intro continuous_intros)
  show ?case using a b by blast
next
  case (Suc n)
  have IHs: "higher_differentiable_on UNIV (sin::real \<Rightarrow> real) n"
    using Suc.IH by (rule conjunct1)
  have IHc: "higher_differentiable_on UNIV (cos::real \<Rightarrow> real) n"
    using Suc.IH by (rule conjunct2)
  have dsin: "sin differentiable (at x)" for x :: real
    using has_field_derivative_imp_has_derivative[OF DERIV_sin] by (blast intro: differentiableI)
  have dcos: "cos differentiable (at x)" for x :: real
    using has_field_derivative_imp_has_derivative[OF DERIV_cos] by (blast intro: differentiableI)
  have ms: "higher_differentiable_on UNIV (\<lambda>x. frechet_derivative sin (at x) v) n" for v :: real
  proof -
    have "(\<lambda>x::real. frechet_derivative sin (at x) v) = (\<lambda>x. cos x * v)"
    proof (rule ext)
      fix x :: real
      have "frechet_derivative sin (at x) = (*) (cos x)"
        by (rule frechet_derivative_at[symmetric,
              OF has_field_derivative_imp_has_derivative[OF DERIV_sin]])
      thus "frechet_derivative sin (at x) v = cos x * v" by simp
    qed
    moreover have "higher_differentiable_on UNIV (\<lambda>x. cos x * v) n"
      by (rule higher_differentiable_on_mult[OF IHc higher_differentiable_on_const open_UNIV])
    ultimately show ?thesis by simp
  qed
  have mc: "higher_differentiable_on UNIV (\<lambda>x. frechet_derivative cos (at x) v) n" for v :: real
  proof -
    have "(\<lambda>x::real. frechet_derivative cos (at x) v) = (\<lambda>x. sin x * (- v))"
    proof (rule ext)
      fix x :: real
      have "frechet_derivative cos (at x) = (*) (- sin x)"
        by (rule frechet_derivative_at[symmetric,
              OF has_field_derivative_imp_has_derivative[OF DERIV_cos]])
      thus "frechet_derivative cos (at x) v = sin x * (- v)" by simp
    qed
    moreover have "higher_differentiable_on UNIV (\<lambda>x. sin x * (- v)) n"
      by (rule higher_differentiable_on_mult[OF IHs higher_differentiable_on_const open_UNIV])
    ultimately show ?thesis by simp
  qed
  show ?case using dsin dcos ms mc by (simp add: higher_differentiable_on_real_Suc)
qed

lemma cis_higher_differentiable_on: "higher_differentiable_on UNIV cis n"
proof -
  have eq: "cis = (\<lambda>t. cos t *\<^sub>R (1::complex) + sin t *\<^sub>R \<i>)"
    by (rule ext) (simp add: cis.code complex_eq_iff)
  have s: "higher_differentiable_on UNIV (sin::real \<Rightarrow> real) n"
    using sin_cos_higher_differentiable_on by (rule conjunct1)
  have c: "higher_differentiable_on UNIV (cos::real \<Rightarrow> real) n"
    using sin_cos_higher_differentiable_on by (rule conjunct2)
  have t1: "higher_differentiable_on UNIV (\<lambda>t. cos t *\<^sub>R (1::complex)) n"
    by (rule higher_differentiable_on_scaleR[OF c higher_differentiable_on_const open_UNIV])
  have t2: "higher_differentiable_on UNIV (\<lambda>t. sin t *\<^sub>R \<i>) n"
    by (rule higher_differentiable_on_scaleR[OF s higher_differentiable_on_const open_UNIV])
  have "higher_differentiable_on UNIV (\<lambda>t. cos t *\<^sub>R (1::complex) + sin t *\<^sub>R \<i>) n"
    by (rule higher_differentiable_on_add[OF t1 t2 open_UNIV])
  thus ?thesis by (simp add: eq)
qed

text \<open>\<^bold>\<open>Reusable kernel for removable smoothness.\<close>  A family \<open>J\<close> of real functions that is
  \<^emph>\<open>closed under differentiation\<close> --- \<open>(J k)' = J (k+1)\<close> everywhere --- is \<open>C\<^sup>\<infinity>\<close> at every
  member.  (\<open>sin\<close>/\<open>cos\<close> are an instance; below we use it for the \<open>sinc\<close> integral family,
  whose derivative chain comes from the Leibniz rule, with \<^emph>\<open>no\<close> \<open>0/0\<close> limit.)\<close>

lemma hdo_real_deriv_chain:
  fixes J :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes ch: "\<And>k x. (J k has_real_derivative J (Suc k) x) (at x)"
  shows "higher_differentiable_on UNIV (J k) n"
proof (induction n arbitrary: k)
  case 0
  have "continuous_on UNIV (J k)"
    by (auto intro: continuous_at_imp_continuous_on DERIV_isCont[OF ch])
  thus ?case by (simp add: higher_differentiable_on.simps(1))
next
  case (Suc n)
  have d: "J k differentiable (at x)" for x
    using ch[of k x] by (blast intro: differentiableI has_field_derivative_imp_has_derivative)
  have fd: "higher_differentiable_on UNIV (\<lambda>x. frechet_derivative (J k) (at x) v) n" for v :: real
  proof -
    have "(\<lambda>x. frechet_derivative (J k) (at x) v) = (\<lambda>x. J (Suc k) x * v)"
    proof (rule ext)
      fix x :: real
      have "frechet_derivative (J k) (at x) = (*) (J (Suc k) x)"
        by (rule frechet_derivative_at[symmetric,
              OF has_field_derivative_imp_has_derivative[OF ch]])
      thus "frechet_derivative (J k) (at x) v = J (Suc k) x * v" by simp
    qed
    moreover have "higher_differentiable_on UNIV (\<lambda>x. J (Suc k) x * v) n"
      by (rule higher_differentiable_on_mult[OF Suc.IH higher_differentiable_on_const open_UNIV])
    ultimately show ?thesis by simp
  qed
  show ?case using d fd by (simp add: higher_differentiable_on.simps(2))
qed

text \<open>\<^bold>\<open>The \<open>sinc\<close> integral family.\<close>  \<open>Jsinc k x = \<integral>\<^sub>0\<^sup>1 t\<^sup>k cos(xt + k\<pi>/2) dt\<close> is the
  \<open>k\<close>-th \<open>x\<close>-derivative of \<open>\<integral>\<^sub>0\<^sup>1 cos(xt) dt = sinc x\<close>, written as an integral so there is
  \<^emph>\<open>no\<close> \<open>0/0\<close>.  The family is closed under differentiation (Leibniz), so by
  @{thm hdo_real_deriv_chain} every \<open>Jsinc k\<close> --- in particular \<open>Jsinc 0 = sinc\<close> --- is
  \<open>C\<^sup>\<infinity>\<close>.  This is the removable-smoothness kernel: the dipole \<open>e\<close> factors through \<open>sinc\<close>.\<close>

definition gsinc :: "real \<Rightarrow> real" where
  "gsinc x = (if x = 0 then 1 else sin x / x)"

definition Jsinc :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "Jsinc k x = integral (cbox 0 1) (\<lambda>t. t^k * cos (x*t + real k * (pi/2)))"

lemma Jsinc_deriv: "(Jsinc k has_real_derivative Jsinc (Suc k) x) (at x)"
proof -
  have d: "((\<lambda>x. t^k * cos (x*t + real k * (pi/2))) has_field_derivative
              (- (t^(Suc k) * sin (x*t + real k * (pi/2))))) (at x within UNIV)"
    if "x \<in> (UNIV::real set)" "t \<in> cbox (0::real) 1" for x t :: real
    by (auto intro!: derivative_eq_intros simp: algebra_simps power_Suc)
  have ib: "(\<lambda>t. t^k * cos (x*t + real k * (pi/2))) integrable_on cbox 0 1"
    if "x \<in> (UNIV::real set)" for x :: real
    by (auto intro!: integrable_continuous_real continuous_intros)
  have cf: "continuous_on (UNIV \<times> cbox 0 1)
              (\<lambda>(x,t). - (t^(Suc k) * sin (x*t + real k * (pi/2))))"
    by (auto intro!: continuous_intros simp: case_prod_beta)
  have L: "(Jsinc k has_real_derivative
              integral (cbox 0 1) (\<lambda>t. - (t^(Suc k) * sin (x*t + real k * (pi/2)))))
            (at x within UNIV)"
    unfolding Jsinc_def
    by (rule leibniz_rule_field_derivative[OF d ib cf UNIV_I convex_UNIV])
  have cshift: "cos (a + pi/2) = - sin a" for a :: real
    by (simp add: cos_add)
  have eq: "integral (cbox 0 1) (\<lambda>t. - (t^(Suc k) * sin (x*t + real k * (pi/2))))
            = Jsinc (Suc k) x"
    unfolding Jsinc_def
  proof (rule integral_cong)
    fix t :: real assume "t \<in> cbox 0 1"
    have phase: "x*t + real (Suc k) * (pi/2) = (x*t + real k * (pi/2)) + pi/2"
      by (simp add: algebra_simps)
    have "cos (x*t + real (Suc k) * (pi/2)) = - sin (x*t + real k * (pi/2))"
      unfolding phase by (rule cshift)
    thus "- (t^(Suc k) * sin (x*t + real k * (pi/2)))
            = t^(Suc k) * cos (x*t + real (Suc k) * (pi/2))"
      by simp
  qed
  from L eq show ?thesis by simp
qed

lemma Jsinc_higher_differentiable_on:
  "higher_differentiable_on UNIV (Jsinc k) n"
  by (intro hdo_real_deriv_chain Jsinc_deriv)

lemma Jsinc_0: "Jsinc 0 = gsinc"
proof (rule ext)
  fix x :: real
  have base: "Jsinc 0 x = integral {0..1} (\<lambda>t. cos (x*t))"
    by (simp add: Jsinc_def)
  show "Jsinc 0 x = gsinc x"
  proof (cases "x = 0")
    case True
    have "integral {0..1} (\<lambda>t::real. cos (x*t)) = integral {0..1} (\<lambda>t::real. 1)"
      using True by simp
    also have "\<dots> = 1" by simp
    finally show ?thesis using base True by (simp add: gsinc_def)
  next
    case False
    have "((\<lambda>t. cos (x*t)) has_integral (sin (x*1)/x - sin (x*0)/x)) {0..1}"
    proof (rule fundamental_theorem_of_calculus)
      show "(0::real) \<le> 1" by simp
    next
      fix t :: real assume "t \<in> {0..1}"
      have "((\<lambda>t. sin (x*t)/x) has_real_derivative cos (x*t)) (at t)"
        using False by (auto intro!: derivative_eq_intros)
      thus "((\<lambda>t. sin (x*t)/x) has_vector_derivative cos (x*t)) (at t within {0..1})"
        by (simp add: has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
    qed
    hence "integral {0..1} (\<lambda>t. cos (x*t)) = sin (x*1)/x - sin (x*0)/x"
      by (rule integral_unique)
    thus ?thesis using base False by (simp add: gsinc_def)
  qed
qed

lemma gsinc_higher_differentiable_on: "higher_differentiable_on UNIV gsinc n"
  using Jsinc_higher_differentiable_on[of 0 n] by (simp add: Jsinc_0)

text \<open>\<^bold>\<open>The concrete dipole element pattern and its gain.\<close>  \<open>edip \<theta> = cos(\<pi>/2 cos\<theta>)/sin\<theta>\<close>
  (tex D_edit L238) is the raw half-wave-dipole pattern, \<open>0/0\<close> at \<open>\<theta>=k\<pi>\<close>.  Its \<^emph>\<open>gain\<close>
  \<open>gdip = \<bar>edip\<bar>\<^sup>2\<close> is given the manifestly-smooth \<open>sinc\<close>-factored form, which is \<open>C\<^sup>\<infinity>\<close>
  everywhere (composition of the smooth \<open>gsinc\<close>), and below is shown to equal \<open>edip\<^sup>2\<close>.\<close>

definition edip :: "real \<Rightarrow> real" where
  "edip \<theta> = cos (pi/2 * cos \<theta>) / sin \<theta>"

definition gdip :: "real \<Rightarrow> real" where
  "gdip \<theta> = (pi^2/4) * (gsinc ((pi/2)*(1 - cos \<theta>)) * gsinc ((pi/2)*(1 + cos \<theta>)))"

lemma gdip_higher_differentiable_on: "higher_differentiable_on UNIV gdip n"
proof -
  have cosn: "higher_differentiable_on UNIV (cos::real \<Rightarrow> real) n"
    using sin_cos_higher_differentiable_on by (rule conjunct2)
  have am: "higher_differentiable_on UNIV (\<lambda>\<theta>::real. (pi/2)*(1 - cos \<theta>)) n"
    by (intro higher_differentiable_on_mult higher_differentiable_on_minus
              higher_differentiable_on_const cosn open_UNIV)
  have ap: "higher_differentiable_on UNIV (\<lambda>\<theta>::real. (pi/2)*(1 + cos \<theta>)) n"
    by (intro higher_differentiable_on_mult higher_differentiable_on_add
              higher_differentiable_on_const cosn open_UNIV)
  have gm: "higher_differentiable_on UNIV (\<lambda>\<theta>. gsinc ((pi/2)*(1 - cos \<theta>))) n"
    using higher_differentiable_on_compose
            [OF gsinc_higher_differentiable_on am _ open_UNIV open_UNIV]
    by (simp add: o_def)
  have gp: "higher_differentiable_on UNIV (\<lambda>\<theta>. gsinc ((pi/2)*(1 + cos \<theta>))) n"
    using higher_differentiable_on_compose
            [OF gsinc_higher_differentiable_on ap _ open_UNIV open_UNIV]
    by (simp add: o_def)
  show ?thesis
    unfolding gdip_def
    by (intro higher_differentiable_on_mult higher_differentiable_on_const
              gm gp open_UNIV)
qed

lemma gdip_eq_edip_sq: "gdip \<theta> = (edip \<theta>)\<^sup>2"
proof (cases "sin \<theta> = 0")
  case True
  have "(cos \<theta>)\<^sup>2 = 1" using sin_cos_squared_add[of \<theta>] True by simp
  hence cc: "cos \<theta> = 1 \<or> cos \<theta> = - 1" by (simp add: power2_eq_1_iff)
  hence num0: "cos (pi/2 * cos \<theta>) = 0" by (auto simp: cos_pi_half)
  have E: "(edip \<theta>)\<^sup>2 = 0" using True num0 by (simp add: edip_def)
  have z0: "gsinc 0 = 1" by (simp add: gsinc_def)
  have p0: "gsinc pi = 0" using pi_gt_zero by (simp add: gsinc_def)
  have G: "gdip \<theta> = 0"
    using cc by (auto simp: gdip_def z0 p0)
  show ?thesis using E G by simp
next
  case False
  have sineq: "sin \<theta> * sin \<theta> = 1 - cos \<theta> * cos \<theta>"
    using sin_cos_squared_add[of \<theta>] by (simp add: power2_eq_square algebra_simps)
  have c1: "cos \<theta> \<noteq> 1"
  proof
    assume "cos \<theta> = 1"
    with sineq have "sin \<theta> * sin \<theta> = 0" by simp
    hence "sin \<theta> = 0" by simp
    with False show False ..
  qed
  have cm1: "cos \<theta> \<noteq> - 1"
  proof
    assume "cos \<theta> = - 1"
    with sineq have "sin \<theta> * sin \<theta> = 0" by simp
    hence "sin \<theta> = 0" by simp
    with False show False ..
  qed
  have A0: "(pi/2)*(1 - cos \<theta>) \<noteq> 0"
  proof
    assume "(pi/2)*(1 - cos \<theta>) = 0"
    hence "1 - cos \<theta> = 0" using pi_gt_zero by simp
    with c1 show False by simp
  qed
  have B0: "(pi/2)*(1 + cos \<theta>) \<noteq> 0"
  proof
    assume "(pi/2)*(1 + cos \<theta>) = 0"
    hence "1 + cos \<theta> = 0" using pi_gt_zero by simp
    with cm1 show False by simp
  qed
  \<comment> \<open>product-to-sum + double angle: \<open>sin A sin B = cos\<^sup>2(\<pi>/2 cos\<theta>)\<close> with \<open>A+B=\<pi>\<close>, \<open>A-B=-\<pi>cos\<theta>\<close>\<close>
  have prod: "sin ((pi/2)*(1 - cos \<theta>)) * sin ((pi/2)*(1 + cos \<theta>)) = (cos (pi/2 * cos \<theta>))\<^sup>2"
  proof -
    have e1: "(pi/2)*(1 - cos \<theta>) - (pi/2)*(1 + cos \<theta>) = - (pi * cos \<theta>)"
      by (simp add: field_simps)
    have e2: "(pi/2)*(1 - cos \<theta>) + (pi/2)*(1 + cos \<theta>) = pi"
      by (simp add: field_simps)
    have "sin ((pi/2)*(1 - cos \<theta>)) * sin ((pi/2)*(1 + cos \<theta>))
          = (cos ((pi/2)*(1 - cos \<theta>) - (pi/2)*(1 + cos \<theta>))
             - cos ((pi/2)*(1 - cos \<theta>) + (pi/2)*(1 + cos \<theta>))) / 2"
      by (simp add: cos_diff cos_add)
    also have "\<dots> = (cos (- (pi * cos \<theta>)) - cos pi) / 2"
      by (simp only: e1 e2)
    also have "\<dots> = (cos (pi * cos \<theta>) + 1) / 2"
      by simp
    also have "\<dots> = (cos (pi/2 * cos \<theta>))\<^sup>2"
      using cos_double_cos[of "pi/2 * cos \<theta>"] by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have AB: "((pi/2)*(1 - cos \<theta>)) * ((pi/2)*(1 + cos \<theta>)) = (pi\<^sup>2/4) * (sin \<theta>)\<^sup>2"
  proof -
    have s: "(sin \<theta>)\<^sup>2 = 1 - (cos \<theta>)\<^sup>2"
      using sin_cos_squared_add[of \<theta>] by (simp add: algebra_simps)
    have "((pi/2)*(1 - cos \<theta>)) * ((pi/2)*(1 + cos \<theta>)) = (pi\<^sup>2/4) * (1 - (cos \<theta>)\<^sup>2)"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> = (pi\<^sup>2/4) * (sin \<theta>)\<^sup>2" using s by simp
    finally show ?thesis .
  qed
  have "gdip \<theta> = (pi\<^sup>2/4)
          * ((sin ((pi/2)*(1 - cos \<theta>)) * sin ((pi/2)*(1 + cos \<theta>)))
             / (((pi/2)*(1 - cos \<theta>)) * ((pi/2)*(1 + cos \<theta>))))"
    unfolding gdip_def
    using A0 B0 gsinc_def by fastforce  
    
  also have "\<dots> = (pi\<^sup>2/4) * ((cos (pi/2 * cos \<theta>))\<^sup>2 / ((pi\<^sup>2/4) * (sin \<theta>)\<^sup>2))"
    using AB prod by presburger
  also have "\<dots> = (cos (pi/2 * cos \<theta>))\<^sup>2 / (sin \<theta>)\<^sup>2"
    using pi_gt_zero False by simp
  also have "\<dots> = (edip \<theta>)\<^sup>2"
    by (simp add: edip_def power_divide)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The literal pattern-squared is smooth, and the gain as a function of the angle.\<close>
  The raw \<open>0/0\<close> function \<open>(cos(\<pi>/2 cos\<theta>)/sin\<theta>)\<^sup>2\<close> \<^emph>\<open>is\<close> \<open>C\<^sup>\<infinity>\<close> --- it equals the smooth
  \<open>gdip\<close> (extensionally), so the smooth extension is genuine, not assumed.  We then take
  the radiation gain to be this extension as a function of \<open>\<omega> = (\<theta>,\<phi>)\<close> (\<open>\<theta> = \<omega>$1\<close>):
  \<open>gain_dip \<omega> = gdip(\<omega>$1) = \<bar>e(\<theta>)\<bar>\<^sup>2\<close>, \<open>C\<^sup>\<infinity>\<close> on \<open>\<real>\<^sup>2\<close>.  \<^bold>\<open>This is the extension that
  defines \<open>U\<close>\<close> --- so \<open>U\<close>'s global derivative facts follow.\<close>

lemma edip_sq_higher_differentiable_on:
  "higher_differentiable_on UNIV (\<lambda>\<theta>. (edip \<theta>)\<^sup>2) n"
proof -
  have "(\<lambda>\<theta>. (edip \<theta>)\<^sup>2) = gdip"
    by (rule ext) (rule gdip_eq_edip_sq[symmetric])
  thus ?thesis by (simp add: gdip_higher_differentiable_on)
qed

definition gain_dip :: "real^2 \<Rightarrow> real" where
  "gain_dip \<omega> = gdip (\<omega> $ 1)"

lemma gain_dip_higher_differentiable_on: "higher_differentiable_on UNIV gain_dip n"
proof -
  have proj: "higher_differentiable_on UNIV (\<lambda>\<omega>::real^2. \<omega> $ 1) n"
  proof -
    have "(\<lambda>\<omega>::real^2. \<omega> $ 1) = (\<lambda>\<omega>. inner \<omega> (axis 1 1))"
      by (rule ext) (simp add: inner_axis)
    thus ?thesis
      using higher_differentiable_on_inner[OF higher_differentiable_on_id
              higher_differentiable_on_const open_UNIV]
      by simp
  qed
  have "higher_differentiable_on UNIV (gdip \<circ> (\<lambda>\<omega>::real^2. \<omega> $ 1)) n"
    by (rule higher_differentiable_on_compose
          [OF gdip_higher_differentiable_on proj _ open_UNIV open_UNIV]) auto
  thus ?thesis
    by (metis (no_types, lifting) ext comp_def gain_dip_def)
qed

text \<open>\<^bold>\<open>The gain derivatives.\<close>  \<open>gain_dip \<omega> = gdip(\<omega>\<^sub>1)\<close> depends only on \<open>\<theta> = \<omega>\<^sub>1\<close>, so its
  Fréchet derivative is \<open>\<partial>\<^bsub>\<theta>\<^esub>gdip \<cdot> h\<^sub>1\<close> (chain rule through the projection) --- the genuine,
  assumption-free derivative of our dipole gain (the \<open>gdip\<close> jet is a fact, \<open>gdip\<close> being \<open>C\<^sup>\<infinity>\<close>).\<close>

lemma gdip_differentiable: "gdip differentiable (at (x::real))"
proof -
  have "gdip differentiable_on UNIV"
    using gdip_higher_differentiable_on[of 1]
    by (rule higher_differentiable_on_imp_differentiable_on) simp
  thus ?thesis by (simp add: differentiable_on_def)
qed

text \<open>\<^bold>\<open>The gain is \<open>C\<^sup>2\<close>: its first-derivative field is again differentiable.\<close>  \<open>gdip\<close> is
  \<open>C\<^sup>\<infinity>\<close>, so \<open>\<partial>gdip\<close> (\<open>\<lambda>t. frechet_derivative gdip (at t) v\<close>) is differentiable --- the
  second-derivative input the Hessian bridge needs for the \<open>gain\<close> factor.\<close>

lemma gdip_deriv_differentiable:
  fixes t :: real
  shows "(\<lambda>t. frechet_derivative gdip (at t) v) differentiable (at t)"
proof -
  have "higher_differentiable_on UNIV (\<lambda>y. frechet_derivative gdip (at y) v) 1"
    using gdip_higher_differentiable_on[of "Suc 1"]
    by (simp add: higher_differentiable_on.simps(2))
  hence "(\<lambda>y. frechet_derivative gdip (at y) v) differentiable_on UNIV"
    by (rule higher_differentiable_on_imp_differentiable_on) simp
  thus ?thesis by (simp add: differentiable_on_def)
qed

text \<open>\<^bold>\<open>Step 2: the concrete steered wavevector \<open>cvec\<^sub>0\<close> is \<open>C\<^sup>\<infinity>\<close>.\<close>  \<open>kx,ky,kz\<close> are \<open>sin/cos\<close>
  of the angle components (smooth); the beam-lift coefficients \<open>(k\<bullet>\<omega>\<^sub>0 - k\<bullet>\<omega>\<^sub>s)/(kz \<omega>\<^sub>s - kz \<omega>\<^sub>0)\<close>
  are \<^emph>\<open>constants\<close> in \<open>\<omega>\<close> (finite by the secant hypothesis), so the planar steered wavevector
  is \<open>C\<^sup>\<infinity>\<close> on \<open>\<real>\<^sup>2\<close>.  \<open>cvec_dip\<close> is the \<open>\<real>\<^sup>2\<close>-valued form feeding \<open>U_cart\<close>.\<close>

lemma proj_higher_differentiable_on:
  "higher_differentiable_on UNIV (\<lambda>\<omega>::real^2. \<omega> $ i) n"
proof -
  have "(\<lambda>\<omega>::real^2. \<omega> $ i) = (\<lambda>\<omega>. inner \<omega> (axis i 1))"
    by (rule ext) (simp add: inner_axis)
  thus ?thesis
    using higher_differentiable_on_inner[OF higher_differentiable_on_id
            higher_differentiable_on_const open_UNIV] by simp
qed

lemma sin_proj_higher_differentiable_on:
  "higher_differentiable_on UNIV (\<lambda>\<omega>::real^2. sin (\<omega> $ i)) n"
proof -
  have sinc: "higher_differentiable_on UNIV (sin::real \<Rightarrow> real) n"
    using sin_cos_higher_differentiable_on by (rule conjunct1)
  have "higher_differentiable_on UNIV (sin \<circ> (\<lambda>\<omega>::real^2. \<omega> $ i)) n"
    by (rule higher_differentiable_on_compose
          [OF sinc proj_higher_differentiable_on _ open_UNIV open_UNIV]) auto
  thus ?thesis by (simp add: o_def)
qed

lemma cos_proj_higher_differentiable_on:
  "higher_differentiable_on UNIV (\<lambda>\<omega>::real^2. cos (\<omega> $ i)) n"
proof -
  have cosc: "higher_differentiable_on UNIV (cos::real \<Rightarrow> real) n"
    using sin_cos_higher_differentiable_on by (rule conjunct2)
  have "higher_differentiable_on UNIV (cos \<circ> (\<lambda>\<omega>::real^2. \<omega> $ i)) n"
    by (rule higher_differentiable_on_compose
          [OF cosc proj_higher_differentiable_on _ open_UNIV open_UNIV]) auto
  thus ?thesis by (simp add: o_def)
qed

lemma kx_higher_differentiable_on: "higher_differentiable_on UNIV kx n"
  unfolding kx_def[abs_def]
  by (rule higher_differentiable_on_mult[OF sin_proj_higher_differentiable_on
        cos_proj_higher_differentiable_on open_UNIV])

lemma ky_higher_differentiable_on: "higher_differentiable_on UNIV ky n"
  unfolding ky_def[abs_def]
  by (rule higher_differentiable_on_mult[OF sin_proj_higher_differentiable_on
        sin_proj_higher_differentiable_on open_UNIV])

lemma kz_higher_differentiable_on: "higher_differentiable_on UNIV kz n"
  unfolding kz_def[abs_def]
  by (rule cos_proj_higher_differentiable_on)

definition cvec_dip :: "angle \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> real^2" where
  \<comment> \<open>the planar steered wavevector \<open>cvec\<^sub>0\<close> as a \<open>\<real>\<^sup>2\<close> vector (axis form, so smoothness
      is immediate); its components are the two entries of @{const cvec0}.\<close>
  "cvec_dip \<omega>0 \<omega>s \<omega> =
     ((kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) *\<^sub>R axis 1 1
   + ((ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) *\<^sub>R axis 2 1"

lemma cvec_dip_higher_differentiable_on:
  "higher_differentiable_on UNIV (cvec_dip \<omega>0 \<omega>s) n"
proof -
  have comp1: "higher_differentiable_on UNIV
      (\<lambda>\<omega>. (kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) n"
    by (intro higher_differentiable_on_add higher_differentiable_on_minus
              higher_differentiable_on_mult higher_differentiable_on_const
              kx_higher_differentiable_on kz_higher_differentiable_on open_UNIV)
  have comp2: "higher_differentiable_on UNIV
      (\<lambda>\<omega>. (ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) n"
    by (intro higher_differentiable_on_add higher_differentiable_on_minus
              higher_differentiable_on_mult higher_differentiable_on_const
              ky_higher_differentiable_on kz_higher_differentiable_on open_UNIV)
  show ?thesis
    unfolding cvec_dip_def[abs_def]
    by (intro higher_differentiable_on_add higher_differentiable_on_scaleR
              higher_differentiable_on_const comp1 comp2 open_UNIV)
qed

text \<open>\<^bold>\<open>The explicit Jacobian of the steering map.\<close>  Since \<open>k\<close> is explicit, the
  Fréchet derivatives of \<open>kx,ky,kz\<close> and of \<open>cvec_dip\<close> are explicit (\<open>sin/cos\<close> of the
  angle components) --- not a \<open>frechet_derivative\<close> placeholder.\<close>

lemma has_derivative_proj:
  "((\<lambda>\<omega>::real^2. \<omega> $ i) has_derivative (\<lambda>h. h $ i)) (at \<omega>)"
  by (auto intro!: bounded_linear.has_derivative[OF bounded_linear_vec_nth]
                   has_derivative_ident)

lemma gain_dip_has_derivative:
  \<comment> \<open>\<open>gain_dip \<omega> = gdip(\<omega>\<^sub>1)\<close> depends only on \<open>\<theta> = \<omega>\<^sub>1\<close>; chain rule through the projection
      gives the genuine, assumption-free Fréchet derivative of our dipole gain.\<close>
  "(gain_dip has_derivative
      (\<lambda>v. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth v 1))) (at \<omega>)"
proof -
  have "((gdip \<circ> (\<lambda>\<omega>. vec_nth \<omega> 1)) has_derivative
          (frechet_derivative gdip (at (vec_nth \<omega> 1)) \<circ> (\<lambda>v. vec_nth v 1))) (at \<omega>)"
    by (rule diff_chain_at[OF has_derivative_proj
          frechet_derivative_works[THEN iffD1, OF gdip_differentiable]])
  thus ?thesis
    by (metis (no_types, lifting) ext gain_dip_def o_def)
qed

lemma has_derivative_kx:
  "(kx has_derivative (\<lambda>h. cos (\<omega>$1) * cos (\<omega>$2) * (h$1) - sin (\<omega>$1) * sin (\<omega>$2) * (h$2)))
     (at \<omega>)"
  unfolding kx_def[abs_def]
  by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)

lemma has_derivative_ky:
  "(ky has_derivative (\<lambda>h. cos (\<omega>$1) * sin (\<omega>$2) * (h$1) + sin (\<omega>$1) * cos (\<omega>$2) * (h$2)))
     (at \<omega>)"
  unfolding ky_def[abs_def]
  by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)

lemma has_derivative_kz:
  "(kz has_derivative (\<lambda>h. - sin (\<omega>$1) * (h$1))) (at \<omega>)"
  unfolding kz_def[abs_def]
  by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)

text \<open>\<^bold>\<open>Building blocks for the \<^emph>\<open>second\<close> derivative\<close> --- the explicit Fréchet derivatives of
  \<open>cos(\<omega>\<^sub>i)\<close> and \<open>sin(\<omega>\<^sub>i)\<close>, used to differentiate the explicit Jacobian \<open>Dcvec_dip\<close> once
  more (giving the genuine, assumption-free second derivative of \<open>cvec_dip\<close>).\<close>

lemma has_derivative_cos_proj:
  "((\<lambda>\<omega>::real^2. cos (\<omega>$i)) has_derivative (\<lambda>h. - sin (\<omega>$i) * (h$i))) (at \<omega>)"
  by (auto intro!: derivative_eq_intros has_derivative_proj)

lemma has_derivative_sin_proj:
  "((\<lambda>\<omega>::real^2. sin (\<omega>$i)) has_derivative (\<lambda>h. cos (\<omega>$i) * (h$i))) (at \<omega>)"
  by (auto intro!: derivative_eq_intros has_derivative_proj)

definition Dcvec_dip :: "angle \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> real^2 \<Rightarrow> real^2" where
  \<comment> \<open>The explicit Jacobian of @{const cvec_dip}.  \<^bold>\<open>Why \<^const>\<open>vec_nth\<close> instead of the \<open>$\<close>
      notation:\<close> in this merged JNF+HMA+Smooth_Manifolds session, parsing the infix \<open>$\<close>
      is super-linearly expensive (notation/type disambiguation), so a single term with
      \<open>\<approx>12\<close> occurrences of \<open>$\<close> takes \<^emph>\<open>minutes\<close> (or hangs) to elaborate, whereas the
      identical term written with the constant \<^const>\<open>vec_nth\<close> elaborates in \<open>< 0.5 s\<close>.
      \<^const>\<open>vec_nth\<close> still \<^emph>\<open>prints\<close> as \<open>\<omega> $ i\<close>, so the displayed maths is unchanged.\<close>
  "Dcvec_dip \<omega>0 \<omega>s \<omega> =
     (\<lambda>h. ((cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2) * (vec_nth h 1)
              - sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2) * (vec_nth h 2))
              + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (- sin (vec_nth \<omega> 1) * (vec_nth h 1))) *\<^sub>R axis 1 1
          + ((cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2) * (vec_nth h 1)
              + sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2) * (vec_nth h 2))
              + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (- sin (vec_nth \<omega> 1) * (vec_nth h 1))) *\<^sub>R axis 2 1)"

lemma has_derivative_cvec_dip:
  "(cvec_dip \<omega>0 \<omega>s has_derivative Dcvec_dip \<omega>0 \<omega>s \<omega>) (at \<omega>)"
  \<comment> \<open>Deterministic, \<^emph>\<open>fast\<close> proof: build the derivative tree \<^emph>\<open>bottom-up\<close> by explicit
      \<open>[OF]\<close> composition of the \<^emph>\<open>specific\<close> non-eq \<open>has_derivative\<close> rules --- pure first-order
      resolution, \<^bold>\<open>no\<close> \<open>auto\<close>/\<open>rule+\<close> backtracking and \<^bold>\<open>no\<close> higher-order unification search
      against \<open>derivative_eq_intros\<close>.  @{thm has_derivative_eq_rhs} lets us state the clean
      derivative; one \<open>simp\<close> clears the \<open>- 0\<close> cruft.\<close>
  unfolding cvec_dip_def[abs_def] Dcvec_dip_def[abs_def]
  by (rule has_derivative_eq_rhs[OF
        has_derivative_add[OF
          has_derivative_scaleR_left[OF
            has_derivative_add[OF
              has_derivative_diff[OF has_derivative_kx has_derivative_const]
              has_derivative_mult_right[OF
                has_derivative_diff[OF has_derivative_kz has_derivative_const]]]]
          has_derivative_scaleR_left[OF
            has_derivative_add[OF
              has_derivative_diff[OF has_derivative_ky has_derivative_const]
              has_derivative_mult_right[OF
                has_derivative_diff[OF has_derivative_kz has_derivative_const]]]]]])
     (simp add: algebra_simps fun_eq_iff)

lemma frechet_derivative_cvec_dip:
  "frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at \<omega>) = Dcvec_dip \<omega>0 \<omega>s \<omega>"
  by (rule frechet_derivative_at[symmetric, OF has_derivative_cvec_dip])

text \<open>\<^bold>\<open>The \<^emph>\<open>second\<close> derivative of \<open>cvec_dip\<close>\<close> --- differentiate the explicit Jacobian
  \<open>Dcvec_dip\<close> once more.  This is the genuine \<open>D\<^sup>2cvec\<^sub>0\<close>, an explicit \<open>sin/cos\<close> bilinear
  form (\<^bold>\<open>not\<close> a \<open>frechet_derivative\<close> placeholder and \<^bold>\<open>nothing assumed\<close>); it discharges the
  second-order hypothesis \<open>cD2\<close> of \<open>has_derivative_dA_via_M2\<close> for our steering map.\<close>

definition D2cvec_dip :: "angle \<Rightarrow> angle \<Rightarrow> angle \<Rightarrow> planar \<Rightarrow> planar \<Rightarrow> planar" where
  \<comment> \<open>the explicit Hessian (second derivative) of \<open>cvec_dip\<close> --- a \<open>sin/cos\<close> bilinear form
      in the directions \<open>h, h'\<close>; \<open>vec_nth\<close> (not \<open>$\<close>) for fast parsing, still prints as \<open>$\<close>.\<close>
  "D2cvec_dip \<omega>0 \<omega>s \<omega> h =
     (\<lambda>h'. ((- vec_nth h 1 * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
              - vec_nth h 2 * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
              - ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * vec_nth h 1 * cos (vec_nth \<omega> 1)) * vec_nth h' 1
            + (- vec_nth h 1 * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
              - vec_nth h 2 * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)) * vec_nth h' 2) *\<^sub>R axis 1 1
          + ((- vec_nth h 1 * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
              + vec_nth h 2 * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
              - ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * vec_nth h 1 * cos (vec_nth \<omega> 1)) * vec_nth h' 1
            + (vec_nth h 1 * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
              - vec_nth h 2 * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)) * vec_nth h' 2) *\<^sub>R axis 2 1)"

lemma has_derivative_Dcvec_dip:
  "((\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) has_derivative D2cvec_dip \<omega>0 \<omega>s \<omega> h) (at \<omega>)"
proof -
  \<comment> \<open>The beam-lift coefficients are \<^emph>\<open>constants\<close> in \<open>\<omega>\<close>; naming them with \<open>define\<close> stops
      \<open>auto\<close> from applying the quotient rule (which would spawn a spurious
      \<open>kz \<omega>\<^sub>s \<noteq> kz \<omega>\<^sub>0\<close> side-condition).  We fold them back in the final assembly.\<close>
  define Dx where "Dx = (kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  define Dy where "Dy = (ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)"
  have dP1: "((\<lambda>y. (cos (vec_nth y 1) * cos (vec_nth y 2) * (vec_nth h 1)
                     - sin (vec_nth y 1) * sin (vec_nth y 2) * (vec_nth h 2))
                   + Dx * (- sin (vec_nth y 1) * (vec_nth h 1)))
              has_derivative
              (\<lambda>h'. (- vec_nth h 1 * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
                     - vec_nth h 2 * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
                     - Dx * vec_nth h 1 * cos (vec_nth \<omega> 1)) * vec_nth h' 1
                   + (- vec_nth h 1 * cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
                     - vec_nth h 2 * sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)) * vec_nth h' 2)) (at \<omega>)"
    by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)
  have dP2: "((\<lambda>y. (cos (vec_nth y 1) * sin (vec_nth y 2) * (vec_nth h 1)
                     + sin (vec_nth y 1) * cos (vec_nth y 2) * (vec_nth h 2))
                   + Dy * (- sin (vec_nth y 1) * (vec_nth h 1)))
              has_derivative
              (\<lambda>h'. (- vec_nth h 1 * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)
                     + vec_nth h 2 * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
                     - Dy * vec_nth h 1 * cos (vec_nth \<omega> 1)) * vec_nth h' 1
                   + (vec_nth h 1 * cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)
                     - vec_nth h 2 * sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)) * vec_nth h' 2)) (at \<omega>)"
    by (auto intro!: derivative_eq_intros has_derivative_proj simp: algebra_simps)
  show ?thesis
    unfolding D2cvec_dip_def[abs_def] Dcvec_dip_def[abs_def] Dx_def[symmetric] Dy_def[symmetric]
    by (rule has_derivative_add[OF has_derivative_scaleR_left[OF dP1]
                                   has_derivative_scaleR_left[OF dP2]])
qed

lemma frechet_derivative_Dcvec_dip:
  "frechet_derivative (\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) (at \<omega>) = D2cvec_dip \<omega>0 \<omega>s \<omega> h"
  by (rule frechet_derivative_at[symmetric, OF has_derivative_Dcvec_dip])

text \<open>\<^bold>\<open>Step 3: the objective \<open>U\<close>, DEFINED FROM the smooth \<open>e\<^sup>2\<close>, is \<open>C\<^sup>\<infinity>\<close> globally.\<close>
  \<open>U_dip = U_cart (cvec_dip \<omega>\<^sub>0 \<omega>\<^sub>s) gain_dip\<close> --- the radiation intensity
  \<open>g(\<omega>)\<bar>A(\<bm>x,\<omega>)\<bar>\<^sup>2\<close> with the steered wavevector and the \<^emph>\<open>smooth\<close> dipole gain
  \<open>g = gain_dip = \<bar>e\<bar>\<^sup>2\<close>.  Because every ingredient is \<open>C\<^sup>\<infinity>\<close> in \<open>\<omega>\<close> (\<open>cis\<close>, \<open>cvec_dip\<close>,
  \<open>gain_dip\<close>), \<open>U_dip\<close> is \<open>C\<^sup>\<infinity>\<close> on all of \<open>\<real>\<^sup>2\<close> --- so its \<open>\<omega>\<close>-gradient and Hessian are
  genuine, global objects (no assumption, dipole nulls included).\<close>

definition U_dip :: "angle \<Rightarrow> angle \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> real" where
  "U_dip \<omega>0 \<omega>s x \<omega> = U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>"

lemma A_cart_dip_higher_differentiable_on:
  "higher_differentiable_on UNIV (\<lambda>\<omega>. A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>) n"
proof -
  have summand: "higher_differentiable_on UNIV
                (\<lambda>\<omega>. cis (- ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ j)))) n" for j
  proof -
    have arg: "higher_differentiable_on UNIV
                 (\<lambda>\<omega>. - ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ j))) n"
      by (intro higher_differentiable_on_uminus higher_differentiable_on_inner
                cvec_dip_higher_differentiable_on higher_differentiable_on_const open_UNIV)
    have "higher_differentiable_on UNIV
            (cis \<circ> (\<lambda>\<omega>. - ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ j)))) n"
      by (rule higher_differentiable_on_compose
            [OF cis_higher_differentiable_on arg _ open_UNIV open_UNIV]) auto
    thus ?thesis by (simp add: o_def)
  qed
  have "higher_differentiable_on UNIV
          (\<lambda>\<omega>. \<Sum>j\<in>UNIV. cis (- ((cvec_dip \<omega>0 \<omega>s \<omega>) \<bullet> (x $ j)))) n"
    by (intro higher_differentiable_on_sum summand open_UNIV)
  thus ?thesis by (simp add: A_cart_def)
qed

lemma U_dip_higher_differentiable_on:
  "higher_differentiable_on UNIV (U_dip \<omega>0 \<omega>s x) n"
proof -
  have AA: "higher_differentiable_on UNIV
              (\<lambda>\<omega>. (cmod (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))\<^sup>2) n"
  proof -
    have "(\<lambda>\<omega>. (cmod (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))\<^sup>2)
          = (\<lambda>\<omega>. inner (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>) (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))"
      by (rule ext) (simp add: power2_norm_eq_inner)
    thus ?thesis
      using higher_differentiable_on_inner[OF A_cart_dip_higher_differentiable_on
              A_cart_dip_higher_differentiable_on open_UNIV] by simp
  qed
  have "higher_differentiable_on UNIV
          (\<lambda>\<omega>. gain_dip \<omega> * (cmod (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))\<^sup>2) n"
    by (rule higher_differentiable_on_mult
          [OF gain_dip_higher_differentiable_on AA open_UNIV])
  thus ?thesis by (simp add: U_dip_def[abs_def] U_cart_def[abs_def])
qed

text \<open>\<^bold>\<open>The global \<open>\<omega>\<close>-derivative facts.\<close>  Since the objective \<open>U_dip\<close> --- built from the
  \<^emph>\<open>smooth\<close> \<open>e\<^sup>2\<close> --- is \<open>C\<^sup>2\<close> everywhere, its gradient field is differentiable at \<^emph>\<open>every\<close>
  \<open>\<omega>\<close> with derivative the Hessian, and the Hessian is the genuine second derivative.
  No assumption, no excluded poles.\<close>

lemma U_dip_Ck2: "Ck_on 2 (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x) UNIV"
proof -
  have "higher_differentiable_on UNIV (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x) 2"
    using U_dip_higher_differentiable_on[of \<omega>0 \<omega>s x 2]
    by (simp add: U_dip_def[abs_def])
  thus ?thesis by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma gradU_dip_has_derivative:
  "(gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x
      has_derivative (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)) (at \<omega>)"
  by (rule gradU_has_derivative_of_C2[OF U_dip_Ck2 UNIV_I])

text \<open>\<^bold>\<open>The dipole gradient field is continuous in \<open>\<omega>\<close>.\<close>  Since @{thm gradU_dip_has_derivative}
  gives a (Fréchet) derivative of \<open>gradU\<close> at \<^emph>\<open>every\<close> \<open>\<omega>\<close>, the gradient field is differentiable
  everywhere, hence continuous on any set --- the genuine, assumption-free continuity of the
  actual dipole gradient (this is one Weierstrass input for the capstone's \<open>\<kappa>\<close>-margin).\<close>

lemma gradU_dip_continuous_on:
  "continuous_on S (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
proof (rule continuous_at_imp_continuous_on, rule ballI)
  fix \<omega> assume "\<omega> \<in> S"
  show "continuous (at \<omega>) (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
    by (rule has_derivative_continuous[OF gradU_dip_has_derivative])
qed

lemma norm_gradU_dip_continuous_on:
  "continuous_on S (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  by (intro continuous_on_norm gradU_dip_continuous_on)

text \<open>\<^bold>\<open>The dipole Hessian is continuous in \<open>\<omega>\<close>.\<close>  \<open>U_dip\<close> is \<open>C\<^sup>2\<close> everywhere
  (@{thm U_dip_Ck2}), so its Hessian \<open>\<nabla>\<^sup>2 = HessU\<close> is continuous (the \<open>C\<^sup>2\<close>-continuity of
  second derivatives, @{thm Ck_2_imp_hessian_continuous}) --- the second Weierstrass input
  (continuity of \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H)\<close> on the annulus) for the capstone's \<open>\<xi>\<close>-margin.\<close>

lemma HessU_dip_continuous_on:
  "continuous_on S (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
proof -
  have eq: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x = \<nabla>\<^sup>2 (U_cart (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
    by (rule ext) (simp add: HessU_def)
  have "continuous_on UNIV (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x)"
    unfolding eq by (rule Ck_2_imp_hessian_continuous[OF U_dip_Ck2])
  thus ?thesis by (rule continuous_on_subset) simp
qed

lemma continuous_on_A_moment_joint:
    "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
  (\<lambda>p. A_moment (fst p) (snd p))"
    unfolding A_moment_def phase_def
    by (intro continuous_on_sum continuous_on_cis continuous_intros
              bounded_linear.continuous_on[OF
  bounded_linear_vec_nth])

lemma continuous_on_M1_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
     (\<lambda>p. M1_moment (fst p) (snd p))"
  unfolding M1_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_M2_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
     (\<lambda>p. M2_moment (fst p) (snd p))"
  unfolding M2_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_M11_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
     (\<lambda>p. M11_moment (fst p) (snd p))"
  unfolding M11_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_M12_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
     (\<lambda>p. M12_moment (fst p) (snd p))"
  unfolding M12_moment_def phase_def w_M12_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_M22_moment_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set)
     (\<lambda>p. M22_moment (fst p) (snd p))"
  unfolding M22_moment_def phase_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

text \<open>\<^bold>\<open>A5 brick 2a: the moment composite \<open>(\<bm>x,\<omega>) \<mapsto> M_paper \<bm>x (cvec_dip \<omega>0 \<omega>s \<omega>)\<close> is jointly
  continuous.\<close>  The dipole steering \<open>cvec_dip\<close> is smooth (@{thm cvec_dip_higher_differentiable_on}),
  hence continuous; composing the pairing \<open>(\<bm>x,\<omega>) \<mapsto> (\<bm>x, cvec_dip \<omega>0 \<omega>s \<omega>)\<close> with the
  jointly-continuous moments (brick 1) routes every \<open>\<bm>x\<close>-dependence of \<open>HessU\<close>/\<open>Dx\<close> through this
  composite.\<close>

lemma continuous_on_cvec_dip:
  "continuous_on UNIV (cvec_dip \<omega>0 \<omega>s)"
  by (rule higher_differentiable_on_imp_continuous_on[OF cvec_dip_higher_differentiable_on])

lemma continuous_on_pair_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. (fst p, cvec_dip \<omega>0 \<omega>s (snd p)))"
  by (intro continuous_on_Pair continuous_on_fst[OF continuous_on_id]
            continuous_on_compose2[OF continuous_on_cvec_dip
                                      continuous_on_snd[OF continuous_on_id] subset_UNIV])

lemma continuous_on_A_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. A_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_A_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M1_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M1_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_M1_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M2_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M2_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_M2_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M11_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M11_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_M11_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M12_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M12_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_M12_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M22_moment_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M22_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_M22_moment_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

text \<open>\<^bold>\<open>A5 brick 2b: the pure-\<open>\<omega>\<close> jets of \<open>HessU_dip_entry_moments\<close> are continuous in \<open>\<omega>\<close>.\<close>
  The gain \<open>gain_dip = gdip\<circ>\<pi>\<^sub>1\<close> and the steering jets \<open>Dcvec_dip\<close>, \<open>D2cvec_dip\<close>, and the gain's
  first/second Fréchet derivatives are all continuous in \<open>\<omega>\<close> --- proved through the \<open>C\<^sup>\<infinity>\<close>
  smoothness of \<open>gdip\<close>/\<open>cvec_dip\<close> (@{thm higher_differentiable_on.simps(2)} extracts the
  derivative-field smoothness, the @{thm frechet_derivative_cvec_dip}/
  @{thm has_derivative_Dcvec_dip} jets identify the explicit forms), so we never touch the
  \<open>sin/cos\<close> formulas or the beam-lift division constant.\<close>

lemma continuous_on_gain_dip:
  "continuous_on UNIV gain_dip"
  unfolding gain_dip_def
  by (rule continuous_on_compose2[OF
        higher_differentiable_on_imp_continuous_on[OF gdip_higher_differentiable_on]
        bounded_linear.continuous_on[OF bounded_linear_vec_nth continuous_on_id] subset_UNIV])

lemma continuous_on_Dcvec_dip:
  "continuous_on UNIV (\<lambda>\<omega>. Dcvec_dip \<omega>0 \<omega>s \<omega> h)"
proof -
  have "higher_differentiable_on UNIV (\<lambda>\<omega>. frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at \<omega>) h) 1"
    using cvec_dip_higher_differentiable_on[of \<omega>0 \<omega>s "Suc 1"]
    by (simp add: higher_differentiable_on.simps(2))
  hence "continuous_on UNIV (\<lambda>\<omega>. frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at \<omega>) h)"
    by (rule higher_differentiable_on_imp_continuous_on)
  thus ?thesis by (simp add: frechet_derivative_cvec_dip)
qed

lemma continuous_on_D2cvec_dip:
  "continuous_on UNIV (\<lambda>\<omega>. D2cvec_dip \<omega>0 \<omega>s \<omega> h h')"
proof -
  have C1: "higher_differentiable_on UNIV (\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) 1"
  proof -
    have "higher_differentiable_on UNIV (\<lambda>y. frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at y) h) 1"
      using cvec_dip_higher_differentiable_on[of \<omega>0 \<omega>s "Suc 1"]
      by (simp add: higher_differentiable_on.simps(2))
    thus ?thesis by (simp add: frechet_derivative_cvec_dip)
  qed
  from C1 have "higher_differentiable_on UNIV
                  (\<lambda>x. frechet_derivative (\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) (at x) h') 0"
    by (simp add: higher_differentiable_on.simps(2))
  hence "continuous_on UNIV (\<lambda>x. frechet_derivative (\<lambda>y. Dcvec_dip \<omega>0 \<omega>s y h) (at x) h')"
    by (rule higher_differentiable_on_imp_continuous_on)
  thus ?thesis
    by (simp add: frechet_derivative_at[OF has_derivative_Dcvec_dip])
qed

lemma continuous_on_frechet_gdip_proj:
  "continuous_on UNIV (\<lambda>\<omega>::real^2. frechet_derivative gdip (at (\<omega>$1)) r)"
proof -
  have g: "continuous_on UNIV (\<lambda>t::real. frechet_derivative gdip (at t) r)"
  proof -
    have "higher_differentiable_on UNIV (\<lambda>t. frechet_derivative gdip (at t) r) 1"
      using gdip_higher_differentiable_on[of "Suc 1"]
      by (simp add: higher_differentiable_on.simps(2))
    thus ?thesis by (rule higher_differentiable_on_imp_continuous_on)
  qed
  show ?thesis
    by (rule continuous_on_compose2[OF g
          bounded_linear.continuous_on[OF bounded_linear_vec_nth continuous_on_id] subset_UNIV])
qed

lemma continuous_on_frechet2_gdip_proj:
  "continuous_on UNIV
     (\<lambda>\<omega>::real^2. frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) c) (at \<omega>) v)"
proof -
  have outer1: "higher_differentiable_on UNIV (\<lambda>t. frechet_derivative gdip (at t) c) 1"
    using gdip_higher_differentiable_on[of "Suc 1"]
    by (simp add: higher_differentiable_on.simps(2))
  have f1C1: "higher_differentiable_on UNIV
                (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) c) 1"
  proof -
    have "higher_differentiable_on UNIV
            ((\<lambda>t. frechet_derivative gdip (at t) c) \<circ> (\<lambda>\<eta>::real^2. \<eta>$1)) 1"
      by (rule higher_differentiable_on_compose
            [OF outer1 proj_higher_differentiable_on _ open_UNIV open_UNIV]) auto
    thus ?thesis by (simp add: o_def)
  qed
  from f1C1 have "higher_differentiable_on UNIV
       (\<lambda>x. frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) c) (at x) v) 0"
    by (simp add: higher_differentiable_on.simps(2))
  thus ?thesis by (rule higher_differentiable_on_imp_continuous_on)
qed

subsection \<open>First contact with the determinant: the moments appear in \<open>dA\<close>\<close>

text \<open>\<^bold>\<open>The moment map enters here.\<close>  The first moments of the configuration,
  \<open>M\<^sub>k(\<bm>x,\<omega>) = \<Sum>\<^sub>n (x\<^sub>n)\<^sub>k e\<^bsup>-\<ii> c(\<omega>)\<bullet>x\<^sub>n\<^esup>\<close>, are exactly the objects the \<open>12\<times>12\<close>
  determinant \<open>bigJ\<close> is the Jacobian of.  The array-factor derivative \<open>dA\<close> is a \<^emph>\<open>linear
  combination of these moments\<close>: \<open>dA(h) = -\<ii> \<Sum>\<^sub>k (dc\,h)\<^sub>k M\<^sub>k\<close>.  This is the first place
  the determinant's world (the moments) literally appears inside our function's
  derivatives --- the on-ramp to \<open>prop:dimZ\<close>/\<open>Phi_bad_meager\<close>.\<close>

definition Mmom :: "(angle \<Rightarrow> planar) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> 2 \<Rightarrow> complex" where
  \<comment> \<open>the \<open>k\<close>-th first moment of the array, \<open>M\<^sub>k = \<Sum>\<^sub>n (x\<^sub>n)\<^sub>k cis(-c\<bullet>x\<^sub>n)\<close>\<close>
  "Mmom cvec x \<omega> k = (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * cis (-(cvec \<omega> \<bullet> (x$n))))"

lemma dA_cart_via_moments:
  "dA_cart cvec dc x \<omega> h
     = (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$k) * Mmom cvec x \<omega> k)"
proof -
  have "dA_cart cvec dc x \<omega> h
      = (\<Sum>n\<in>UNIV. \<Sum>k\<in>UNIV.
           (- \<i>) * complex_of_real ((dc h)$k) * complex_of_real ((x$n)$k)
             * cis (-(cvec \<omega> \<bullet> (x$n))))"
    unfolding dA_cart_def
    by (simp add: inner_vec_def of_real_sum of_real_mult
                  sum_distrib_left sum_distrib_right mult.assoc)
  also have "\<dots> = (\<Sum>k\<in>UNIV. \<Sum>n\<in>UNIV.
           (- \<i>) * complex_of_real ((dc h)$k) * complex_of_real ((x$n)$k)
             * cis (-(cvec \<omega> \<bullet> (x$n))))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$k) * Mmom cvec x \<omega> k)"
    by (simp add: Mmom_def sum_distrib_left mult.assoc)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Second contact: \<open>gradU\<close> in moment coordinates.\<close>  Each angular partial
  \<open>\<partial>U/\<partial>\<omega>\<^sub>j = gradU \<bullet> e\<^sub>j\<close> is, via the product rule and @{thm dA_cart_via_moments}, an
  explicit function of the array factor \<open>A\<close> and the first moments \<open>M\<^sub>k\<close> (and the gain
  data and the \<open>cvec\<close>-Jacobian \<open>dc\<close>).  This is \<open>gradU\<close> expressed through the moment map.\<close>

lemma gradU_component_via_moments:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and dc :: "angle \<Rightarrow> planar" and dgain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes dcvec: "(cvec has_derivative dc) (at \<omega>)"
    and dgn: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega> $ j
         = dgain (axis j 1) * (cmod (A_cart cvec x \<omega>))\<^sup>2
           + gain \<omega> * (2 * Re (cnj (A_cart cvec x \<omega>)
                  * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)))"
proof -
  have comp: "gradU cvec gain x \<omega> $ j = dU_cart cvec dc gain dgain x \<omega> (axis j 1)"
    by (simp add: gradU_explicit[OF dcvec dgn] axis_def if_distrib sum.delta cong: if_cong)
  show ?thesis
    by (simp add: comp dU_cart_def dA_cart_via_moments)
qed

text \<open>\<^bold>\<open>Third contact: the second moments appear when we differentiate the first.\<close>
  \<open>M\<^sub>k\<^sub>l = \<Sum>\<^sub>n (x\<^sub>n)\<^sub>k (x\<^sub>n)\<^sub>l e\<^bsup>-\<ii> c\<bullet>x\<^sub>n\<^esup>\<close> are the second moments (the \<open>M\<^sub>1\<^sub>1,M\<^sub>1\<^sub>2,M\<^sub>2\<^sub>2\<close>
  entries of the moment map).  Differentiating a first moment yields a combination of
  them: \<open>dM\<^sub>k(h) = -\<ii> \<Sum>\<^sub>l (dc\,h)\<^sub>l M\<^sub>k\<^sub>l\<close>.  These are the entries that feed \<open>HessU\<close>.\<close>

definition M2mom :: "(angle \<Rightarrow> planar) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> 2 \<Rightarrow> 2 \<Rightarrow> complex" where
  \<comment> \<open>the \<open>(k,l)\<close> second moment \<open>M\<^sub>k\<^sub>l = \<Sum>\<^sub>n (x\<^sub>n)\<^sub>k (x\<^sub>n)\<^sub>l cis(-c\<bullet>x\<^sub>n)\<close>\<close>
  "M2mom cvec x \<omega> k l =
     (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * complex_of_real ((x$n)$l)
                 * cis (-(cvec \<omega> \<bullet> (x$n))))"

lemma has_derivative_Mmom:
  assumes dcvec: "(cvec has_derivative dc) (at \<omega>)"
  shows "((\<lambda>\<omega>. Mmom cvec x \<omega> k) has_derivative
            (\<lambda>h. \<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$l) * M2mom cvec x \<omega> k l)) (at \<omega>)"
proof -
  have termderiv:
    "((\<lambda>\<omega>. complex_of_real ((x$n)$k) * cis (-(cvec \<omega> \<bullet> (x$n))))
        has_derivative
        (\<lambda>h. complex_of_real ((x$n)$k)
              * ((- \<i>) * complex_of_real (dc h \<bullet> (x$n)) * cis (-(cvec \<omega> \<bullet> (x$n)))))) (at \<omega>)"
    for n
    using has_derivative_mult[OF has_derivative_const has_derivative_A_cart_term[OF dcvec]]
    by simp
  have sumderiv:
    "((\<lambda>\<omega>. Mmom cvec x \<omega> k) has_derivative
        (\<lambda>h. \<Sum>n\<in>UNIV. complex_of_real ((x$n)$k)
              * ((- \<i>) * complex_of_real (dc h \<bullet> (x$n)) * cis (-(cvec \<omega> \<bullet> (x$n)))))) (at \<omega>)"
    unfolding Mmom_def by (rule has_derivative_sum) (rule termderiv)
  have dform:
    "(\<lambda>h. \<Sum>n\<in>UNIV. complex_of_real ((x$n)$k)
            * ((- \<i>) * complex_of_real (dc h \<bullet> (x$n)) * cis (-(cvec \<omega> \<bullet> (x$n)))))
     = (\<lambda>h. \<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$l) * M2mom cvec x \<omega> k l)"
  proof (rule ext)
    fix h
    have "(\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k)
            * ((- \<i>) * complex_of_real (dc h \<bullet> (x$n)) * cis (-(cvec \<omega> \<bullet> (x$n)))))
        = (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$l)
              * (complex_of_real ((x$n)$k) * complex_of_real ((x$n)$l)
                 * cis (-(cvec \<omega> \<bullet> (x$n)))))"
      by (simp add: inner_vec_def of_real_sum of_real_mult
                    sum_distrib_left sum_distrib_right mult.assoc mult.left_commute)
    also have "\<dots> = (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$l)
              * (complex_of_real ((x$n)$k) * complex_of_real ((x$n)$l)
                 * cis (-(cvec \<omega> \<bullet> (x$n)))))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$l) * M2mom cvec x \<omega> k l)"
      by (simp add: M2mom_def sum_distrib_left mult.assoc)
    finally show "(\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k)
            * ((- \<i>) * complex_of_real (dc h \<bullet> (x$n)) * cis (-(cvec \<omega> \<bullet> (x$n)))))
        = (\<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((dc h)$l) * M2mom cvec x \<omega> k l)" .
  qed
  show ?thesis by (rule sumderiv[unfolded dform])
qed

text \<open>\<^bold>\<open>Second derivative of the array factor (rung ii core).\<close>  The first directional
  derivative of \<open>A\<close> is \<open>dA(h) = -\<ii> \<Sum>\<^sub>k (dc\,h)\<^sub>k M\<^sub>k\<close>.  Differentiating the map
  \<open>y \<mapsto> dA\<^bsub>y\<^esub>(h)\<close> once more --- using @{thm has_derivative_Mmom} for \<open>dM\<^sub>k \<rightarrow> M\<^sub>k\<^sub>l\<close> and the
  \<^emph>\<open>second\<close> derivative \<open>E\<close> of \<open>cvec\<close> --- introduces exactly the second moments \<open>M\<^sub>k\<^sub>l\<close>.
  Here \<open>DC y\<close> is the derivative of \<open>cvec\<close> at \<open>y\<close> (a family, since the outer derivative
  varies the base point) and \<open>E = h' \<mapsto> D\<^sup>2cvec(h',h)\<close>.\<close>

lemma has_derivative_dA_via_M2:
  fixes cvec :: "angle \<Rightarrow> planar" and DC :: "angle \<Rightarrow> planar \<Rightarrow> planar"
    and E :: "planar \<Rightarrow> planar" and x :: "planar^'n" and \<omega> h :: planar
  assumes cD: "\<And>y. (cvec has_derivative DC y) (at y)"
    and cD2: "((\<lambda>y. DC y h) has_derivative E) (at \<omega>)"
  shows "((\<lambda>y. \<Sum>k\<in>UNIV. complex_of_real ((DC y h)$k) * Mmom cvec x y k)
            has_derivative
            (\<lambda>h'. \<Sum>k\<in>UNIV.
                complex_of_real ((DC \<omega> h)$k)
                  * (\<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((DC \<omega> h')$l) * M2mom cvec x \<omega> k l)
                + complex_of_real ((E h')$k) * Mmom cvec x \<omega> k))
          (at \<omega>)"
proof -
  have termderiv:
    "((\<lambda>y. complex_of_real ((DC y h)$k) * Mmom cvec x y k)
        has_derivative
        (\<lambda>h'. complex_of_real ((DC \<omega> h)$k)
                * (\<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((DC \<omega> h')$l) * M2mom cvec x \<omega> k l)
              + complex_of_real ((E h')$k) * Mmom cvec x \<omega> k)) (at \<omega>)" for k
  proof -
    have d1: "((\<lambda>y. complex_of_real ((DC y h)$k))
                has_derivative (\<lambda>h'. complex_of_real ((E h')$k))) (at \<omega>)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_of_real
            bounded_linear.has_derivative[OF bounded_linear_vec_nth cD2]])
    have d2: "((\<lambda>y. Mmom cvec x y k) has_derivative
                (\<lambda>h'. \<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((DC \<omega> h')$l) * M2mom cvec x \<omega> k l)) (at \<omega>)"
      by (rule has_derivative_Mmom[OF cD])
    show ?thesis by (rule has_derivative_mult[OF d1 d2])
  qed
  show ?thesis by (rule has_derivative_sum) (rule termderiv)
qed

text \<open>\<^bold>\<open>Concrete second derivative of the array factor for \<open>cvec_dip\<close>\<close> --- discharge the
  hypotheses of @{thm has_derivative_dA_via_M2} with the \<^emph>\<open>proven\<close> first and second
  derivatives of our steering map (@{thm has_derivative_cvec_dip},
  @{thm has_derivative_Dcvec_dip}).  No assumptions: the array factor's second derivative
  for \<open>U_dip\<close> is an explicit combination of the first and second moments \<open>M\<^sub>k, M\<^sub>k\<^sub>l\<close> and the
  \<open>cvec_dip\<close> jet.\<close>

lemma has_derivative_dA_dip:
  "((\<lambda>y. \<Sum>k\<in>UNIV. complex_of_real ((Dcvec_dip \<omega>0 \<omega>s y h)$k) * Mmom (cvec_dip \<omega>0 \<omega>s) x y k)
      has_derivative
      (\<lambda>h'. \<Sum>k\<in>UNIV. complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> h)$k)
              * (\<Sum>l\<in>UNIV. (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> h')$l)
                   * M2mom (cvec_dip \<omega>0 \<omega>s) x \<omega> k l)
            + complex_of_real ((D2cvec_dip \<omega>0 \<omega>s \<omega> h h')$k) * Mmom (cvec_dip \<omega>0 \<omega>s) x \<omega> k))
     (at \<omega>)"
  by (rule has_derivative_dA_via_M2[OF has_derivative_cvec_dip has_derivative_Dcvec_dip])

text \<open>\<^bold>\<open>\<open>gradU\<close> IS the appendix \<open>\<Phi>\<close>-formula.\<close>  Writing \<open>a = Re A\<close>, \<open>b = Im A\<close>,
  \<open>a\<^sub>k = Re M\<^sub>k\<close>, \<open>b\<^sub>k = Im M\<^sub>k\<close>, the angular partial is
  \<open>\<partial>U/\<partial>\<omega>\<^sub>j = \<dot>g\<^sub>j(a\<^sup>2+b\<^sup>2) + 2g \<Sum>\<^sub>k (dc e\<^sub>j)\<^sub>k (b\<^sub>k a - a\<^sub>k b)\<close> --- exactly \<open>Phi1m\<close>/\<open>Phi2m\<close>
  (in \<open>c\<close>-coordinates, where \<open>dc = id\<close>, this is literally \<open>g\<^sub>j(a\<^sup>2+b\<^sup>2)+2g(b\<^sub>j a-a\<^sub>j b)\<close>).
  So the first two components of \<open>\<Phi>\<close> are functions of the moment map \<open>(A,M\<^sub>1,M\<^sub>2)\<close>.\<close>

lemma gradU_component_real_moments:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and dc :: "angle \<Rightarrow> planar" and dgain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes dcvec: "(cvec has_derivative dc) (at \<omega>)"
    and dgn: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega> $ j
         = dgain (axis j 1) * ((Re (A_cart cvec x \<omega>))\<^sup>2 + (Im (A_cart cvec x \<omega>))\<^sup>2)
           + gain \<omega> * (2 * (\<Sum>k\<in>UNIV. (dc (axis j 1))$k
                  * (Re (A_cart cvec x \<omega>) * Im (Mmom cvec x \<omega> k)
                     - Im (A_cart cvec x \<omega>) * Re (Mmom cvec x \<omega> k))))"
proof -
  let ?A = "A_cart cvec x \<omega>"
  have cmod2: "(cmod ?A)\<^sup>2 = (Re ?A)\<^sup>2 + (Im ?A)\<^sup>2"
    by (simp add: cmod_power2)
  have reterm:
    "Re (cnj ?A * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k))
     = (\<Sum>k\<in>UNIV. (dc (axis j 1))$k
            * (Re ?A * Im (Mmom cvec x \<omega> k) - Im ?A * Re (Mmom cvec x \<omega> k)))"
  proof -
    have "Re (cnj ?A * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k))
        = (\<Sum>k\<in>UNIV. Re (cnj ?A * ((- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)))"
      by (simp add: sum_distrib_left Re_sum)
    also have "\<dots> = (\<Sum>k\<in>UNIV. (dc (axis j 1))$k
            * (Re ?A * Im (Mmom cvec x \<omega> k) - Im ?A * Re (Mmom cvec x \<omega> k)))"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have G: "gradU cvec gain x \<omega> $ j
        = dgain (axis j 1) * (cmod ?A)\<^sup>2
          + gain \<omega> * (2 * Re (cnj ?A
                * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)))"
    by (rule gradU_component_via_moments[OF dcvec dgn])
  show ?thesis by (simp only: G cmod2 reterm)
qed

text \<open>\<^bold>\<open>Nothing is assumed: the derivatives of the concrete \<open>cvec\<close>/\<open>gain\<close> are facts.\<close>
  \<open>cvec_dip\<close> and \<open>gain_dip\<close> are \<open>C\<^sup>\<infinity>\<close> (proved), hence differentiable, so the \<open>has_derivative\<close>
  hypotheses of the moment lemmas are \<^emph>\<open>discharged\<close> for our function --- the moment form
  of \<open>gradU\<close> holds for \<open>U_dip\<close> with no hypotheses at all.\<close>

lemma cvec_dip_differentiable: "cvec_dip \<omega>0 \<omega>s differentiable (at \<omega>)"
proof -
  have "cvec_dip \<omega>0 \<omega>s differentiable_on UNIV"
    using cvec_dip_higher_differentiable_on[of \<omega>0 \<omega>s 1]
    by (rule higher_differentiable_on_imp_differentiable_on) simp
  thus ?thesis by (simp add: differentiable_on_def)
qed

lemma gain_dip_differentiable: "gain_dip differentiable (at \<omega>)"
proof -
  have "gain_dip differentiable_on UNIV"
    using gain_dip_higher_differentiable_on[of 1]
    by (rule higher_differentiable_on_imp_differentiable_on) simp
  thus ?thesis by (simp add: differentiable_on_def)
qed

lemma gradU_dip_real_moments:
  "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
   = frechet_derivative gain_dip (at \<omega>) (axis j 1)
       * ((Re (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))\<^sup>2 + (Im (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>))\<^sup>2)
     + gain_dip \<omega> * (2 * (\<Sum>k\<in>UNIV.
           (frechet_derivative (cvec_dip \<omega>0 \<omega>s) (at \<omega>) (axis j 1))$k
             * (Re (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>) * Im (Mmom (cvec_dip \<omega>0 \<omega>s) x \<omega> k)
                - Im (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>) * Re (Mmom (cvec_dip \<omega>0 \<omega>s) x \<omega> k))))"
  by (rule gradU_component_real_moments
        [OF frechet_derivative_works[THEN iffD1, OF cvec_dip_differentiable]
            frechet_derivative_works[THEN iffD1, OF gain_dip_differentiable]])

text \<open>\<^bold>\<open>Toward \<open>HessU\<close> in second moments (rung ii).\<close>  For our \<open>C\<^sup>2\<close> function \<open>U_dip\<close> the
  gradient field is differentiable with derivative the Hessian matrix (@{thm
  gradU_dip_has_derivative}), so the Fréchet derivative of \<open>gradU\<close> \<^emph>\<open>is\<close> \<open>\<lambda>v. HessU \<cdot> v\<close>,
  and the \<open>(k,l)\<close> Hessian entry is the \<open>k\<close>-th component of that derivative in the direction
  \<open>e\<^sub>l\<close>.  This is the entry point for expressing \<open>H\<^sub>k\<^sub>l\<close> through the second moments \<open>M\<^sub>k\<^sub>l\<close>.\<close>

lemma frechet_derivative_gradU_dip:
  "frechet_derivative (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x) (at \<omega>)
     = (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)"
  by (rule frechet_derivative_at[symmetric, OF gradU_dip_has_derivative])

lemma HessU_dip_entry:
  "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
     = frechet_derivative (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x) (at \<omega>) (axis l 1) $ k"
proof -
  have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
          = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v axis l 1) $ k"
    by (simp add: matrix_vector_mult_def axis_def if_distrib sum.delta cong: if_cong)
  also have "\<dots> = frechet_derivative (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x) (at \<omega>) (axis l 1) $ k"
    by (simp add: frechet_derivative_gradU_dip)
  finally show ?thesis .
qed

definition sigma_min :: "real^2^2 \<Rightarrow> real" where
  \<comment> \<open>smallest singular value: \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) = inf\<^bsub>\<parallel>v\<parallel>=1\<^esub> \<parallel>H v\<parallel>\<close> (the operator-norm characterisation)\<close>
  "sigma_min H = (INF v \<in> sphere 0 1. norm (H *v v))"

lemma sphere01_ne: "sphere (0::real^2) 1 \<noteq> {}"
  by simp

lemma sigma_min_nonneg: "0 \<le> sigma_min H"
  unfolding sigma_min_def by (rule cINF_greatest[OF sphere01_ne]) simp

text \<open>\<^bold>\<open>\<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n\<close> is (4-Lipschitz, hence) continuous.\<close>  As an infimum over the unit sphere of
  \<open>\<parallel>H v\<parallel>\<close>, the smallest singular value differs between two matrices by at most the operator
  norm of their difference: for each unit \<open>v\<close>, \<open>\<parallel>H\<^sub>1v\<parallel> \<le> \<parallel>H\<^sub>2v\<parallel> + \<parallel>(H\<^sub>1-H\<^sub>2)v\<parallel> \<le> \<parallel>H\<^sub>2v\<parallel> + \<parallel>H\<^sub>1-H\<^sub>2\<parallel>\<^bsub>op\<^esub>\<close>,
  so \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n H\<^sub>1 - \<sigma>\<^sub>m\<^sub>i\<^sub>n H\<^sub>2 \<le> \<parallel>H\<^sub>1-H\<^sub>2\<parallel>\<^bsub>op\<^esub> \<le> 4\<parallel>H\<^sub>1-H\<^sub>2\<parallel>\<close>.  Continuity then composes with
  @{thm HessU_dip_continuous_on} to give continuity of \<open>\<omega> \<mapsto> \<sigma>\<^sub>m\<^sub>i\<^sub>n(H(\<omega>))\<close>.\<close>

lemma sigma_min_diff_le:
  fixes H1 H2 :: "real^2^2"
  shows "sigma_min H1 - sigma_min H2 \<le> onorm ((*v) (H1 - H2))"
proof -
  let ?L = "onorm ((*v) (H1 - H2))"
  have bdd: "bdd_below ((\<lambda>v. norm (H1 *v v)) ` sphere 0 1)"
    by (rule bdd_belowI[of _ 0]) auto
  have step: "sigma_min H1 - ?L \<le> norm (H2 *v v)" if v: "v \<in> sphere (0::real^2) 1" for v
  proof -
    have nv: "norm v = 1" using v by (simp add: dist_norm)
    have le1: "sigma_min H1 \<le> norm (H1 *v v)"
      unfolding sigma_min_def by (rule cINF_lower[OF bdd v])
    have tri: "norm (H1 *v v) \<le> norm (H2 *v v) + norm ((H1 - H2) *v v)"
      using norm_triangle_sub[of "H1 *v v" "H2 *v v"]
      by (simp add: matrix_vector_mult_diff_rdistrib)
    have onb: "norm ((H1 - H2) *v v) \<le> ?L"
      using onorm[OF matrix_vector_mul_bounded_linear, of "H1 - H2" v] nv by simp
    from le1 tri onb show ?thesis by linarith
  qed
  have main: "sigma_min H1 - ?L \<le> sigma_min H2"
  proof -
    have "sigma_min H1 - ?L \<le> (INF v\<in>sphere (0::real^2) 1. norm (H2 *v v))"
      by (rule cINF_greatest[OF sphere01_ne]) (rule step)
    thus ?thesis by (simp add: sigma_min_def)
  qed
  thus ?thesis by linarith
qed

lemma onorm_mv_le4:
  fixes M :: "real^2^2"
  shows "onorm ((*v) M) \<le> 4 * norm M"
proof -
  have "onorm ((*v) M) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
    by (rule onorm_le_matrix_component_sum)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::2 set). \<Sum>j\<in>(UNIV::2 set). norm M)"
    by (intro sum_mono)
       (rule order_trans[OF component_le_norm_cart Finite_Cartesian_Product.norm_nth_le])
  also have "\<dots> = 4 * norm M" by simp
  finally show ?thesis .
qed

lemma sigma_min_continuous_on:
  "continuous_on (S::(real^2^2) set) sigma_min"
proof -
  have "4-lipschitz_on UNIV (sigma_min :: real^2^2 \<Rightarrow> real)"
  proof (rule lipschitz_onI)
    show "(0::real) \<le> 4" by simp
    fix H1 H2 :: "real^2^2"
    have b1: "sigma_min H1 - sigma_min H2 \<le> onorm ((*v) (H1 - H2))"
      by (rule sigma_min_diff_le)
    have b2: "sigma_min H2 - sigma_min H1 \<le> onorm ((*v) (H2 - H1))"
      by (rule sigma_min_diff_le)
    have nc: "norm (H2 - H1) = norm (H1 - H2)" by (simp add: norm_minus_commute)
    have "\<bar>sigma_min H1 - sigma_min H2\<bar> \<le> 4 * norm (H1 - H2)"
      using b1 b2 onorm_mv_le4[of "H1 - H2"] onorm_mv_le4[of "H2 - H1"] nc
      by (simp add: abs_le_iff)
    thus "dist (sigma_min H1) (sigma_min H2) \<le> 4 * dist H1 H2"
      by (simp add: dist_norm dist_real_def)
  qed
  hence "continuous_on UNIV (sigma_min :: real^2^2 \<Rightarrow> real)"
    by (rule lipschitz_on_continuous_on)
  thus ?thesis by (rule continuous_on_subset) simp
qed

text \<open>\<^bold>\<open>The dipole nondegeneracy margin \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H(\<omega>))\<close> is continuous in \<open>\<omega>\<close>\<close> ---
  composition of the continuous \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n\<close> with the continuous dipole Hessian.\<close>

lemma sigma_min_HessU_dip_continuous_on:
  "continuous_on S (\<lambda>\<omega>. sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  using continuous_on_compose[OF HessU_dip_continuous_on
          continuous_on_subset[OF sigma_min_continuous_on subset_UNIV]]
  by (simp add: o_def)

definition Xrobust ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> planar \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((planar)^'n) set"
  where
  "Xrobust cvec g ctr \<epsilon> \<kappa> =
     {x. \<forall>\<omega>\<in>sphere ctr \<epsilon>. \<kappa> \<le> norm (gradU cvec g x \<omega>)}"

definition X0 ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> planar \<Rightarrow> (planar) set
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((planar)^'n) set"
  where
  "X0 cvec g ctr \<Omega> \<xi> \<kappa> \<epsilon> =
     {x \<in> Xrobust cvec g ctr \<epsilon> \<kappa>.
        \<forall>y \<in> \<Omega> - ball ctr \<epsilon>. \<xi> \<le> norm (gradU cvec g x y) + sigma_min (HessU cvec g x y)}"

definition F0 ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> planar \<Rightarrow> planar \<Rightarrow> (planar) set \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((planar)^'n) set"
  where
  "F0 cvec g R dmin A B D \<omega>null ctr \<Omega> \<delta>null pmin \<xi> \<kappa> \<epsilon> =
     Ffeas cvec g R dmin A B D \<omega>null ctr \<delta>null pmin
     \<inter> X0 cvec g ctr \<Omega> \<xi> \<kappa> \<epsilon>"


subsection \<open>The angular scan domain \<open>\<Omega>\<close> (paper L1253) and its compactness\<close>

text \<open>The paper fixes the angular domain as the box
  \<open>\<Omega> = [\<theta>\<^sub>0-\<pi>/2,\<theta>\<^sub>0+\<pi>/2] \<times> [\<phi>\<^sub>0-\<pi>,\<phi>\<^sub>0+\<pi>]\<close> (D_edit L1253), i.e. centred at the design
  direction \<open>ctr = (\<theta>\<^sub>0,\<phi>\<^sub>0)\<close> with half-widths \<open>(\<pi>/2,\<pi>)\<close>.  As a closed box it is \<^emph>\<open>compact\<close>,
  and so is the annulus \<open>\<Omega>\<^sup>~ = \<Omega> \\ B\<^sub>\<epsilon>(ctr)\<close> --- both are \<^emph>\<open>proved\<close>, not assumed.\<close>

definition Omega :: "planar \<Rightarrow> planar set" where
  \<comment> \<open>\<open>[\<theta>\<^sub>0-\<pi>/2,\<theta>\<^sub>0+\<pi>/2] \<times> [\<phi>\<^sub>0-\<pi>,\<phi>\<^sub>0+\<pi>]\<close>, the box centred at \<open>ctr\<close>\<close>
  "Omega ctr = cbox (ctr - vector [pi/2, pi]) (ctr + vector [pi/2, pi])"

lemma Omega_compact: "compact (Omega ctr)"
  unfolding Omega_def by (rule compact_cbox)

lemma Omega_minus_ball_compact: "compact (Omega ctr - ball c \<epsilon>)"
proof -
  have "Omega ctr - ball c \<epsilon> = Omega ctr \<inter> (- ball c \<epsilon>)" by auto
  moreover have "compact (Omega ctr \<inter> (- ball c \<epsilon>))"
    by (rule compact_Int_closed[OF Omega_compact closed_Compl[OF open_ball]])
  ultimately show ?thesis by simp
qed


subsection \<open>Building blocks of the explicit feasibility witness \<open>\<bar>x\<close> (D_edit L450--566)\<close>

text \<open>\<^bold>\<open>The vanishing sum of \<open>N\<close>th roots of unity.\<close>  \<open>\<Sum>\<^bsub>k<N\<^esub> cis(-2\<pi>k/N) = 0\<close> for \<open>N>1\<close> ---
  the analytic heart of the null constraint: the witness phases are arranged to be exactly
  the \<open>N\<close>th roots of unity, whose sum vanishes (geometric series, @{thm sum_roots_unity}).\<close>

lemma sum_cis_roots_unity:
  assumes "n > 1"
  shows "(\<Sum>k<n. cis (2 * pi * real k / real n)) = 0"
proof -
  have nn: "real n \<noteq> 0" using assms by simp
  define w where "w = cis (2 * pi / real n)"
  have wne: "w \<noteq> 1"
  proof
    assume "w = 1"
    with assms obtain k :: int where "2 * pi / real n = 2 * pi * of_int k"
      by (auto simp: w_def complex_eq_iff cos_one_2pi_int)
    with assms have "real n * of_int k = 1" by (simp add: field_simps)
    also have "real n * of_int k = of_int (int n * k)" by simp
    also have "1 = (of_int 1 :: real)" by simp
    also note of_int_eq_iff
    finally show False using assms by (auto simp: zmult_eq_1_iff)
  qed
  have wn1: "w ^ n = 1"
  proof -
    have "w ^ n = cis (real n * (2 * pi / real n))"
      using Complex.DeMoivre w_def by presburger
    also have "real n * (2 * pi / real n) = 2 * pi" using nn by simp
    finally show ?thesis by simp
  qed
  have "(\<Sum>k<n. cis (2 * pi * real k / real n)) = (\<Sum>k<n. w ^ k)"
    by (intro sum.cong refl, simp add: Complex.DeMoivre Groups.mult_ac(2) w_def)
  also have "\<dots> = (w ^ n - 1) / (w - 1)"
    using wne by (subst geometric_sum) auto
  also have "\<dots> = 0" using wn1 by simp
  finally show ?thesis .
qed

lemma sum_cis_neg_roots_unity:
  assumes "n > 1"
  shows "(\<Sum>k<n. cis (- (2 * pi * real k / real n))) = 0"
proof -
  have "(\<Sum>k<n. cis (- (2 * pi * real k / real n)))
          = cnj (\<Sum>k<n. cis (2 * pi * real k / real n))"
    by (simp add: cnj_sum cis_cnj)
  also have "\<dots> = cnj 0" by (subst sum_cis_roots_unity[OF assms]) simp
  finally show ?thesis by simp
qed

text \<open>\<^bold>\<open>The steering vector collapses at the main beam: \<open>cvec\<^sub>dip \<omega>\<^sub>0 \<omega>\<^sub>s \<omega>\<^sub>0 = 0\<close>.\<close>  The
  beam-lift coefficient times \<open>(k\<^sub>z\<omega>\<^sub>0 - k\<^sub>z\<omega>\<^sub>s)\<close> exactly cancels \<open>(k\<^sub>x\<omega>\<^sub>0 - k\<^sub>x\<omega>\<^sub>s)\<close> (and the
  \<open>y\<close>-analogue), so the reduced wavevector vanishes at \<open>\<omega>\<^sub>0\<close> --- whence \<^emph>\<open>every\<close> configuration
  has full main-beam power (D_edit L413--414: ``maximal main beam power by construction'').\<close>

lemma cvec_dip_at_main:
  assumes "kz \<omega>s \<noteq> kz \<omega>0"
  shows "cvec_dip \<omega>0 \<omega>s \<omega>0 = 0"
proof -
  have d: "kz \<omega>s - kz \<omega>0 \<noteq> 0" using assms by simp
  have c1: "(kx \<omega>0 - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega>0 - kz \<omega>s) = 0"
    using d by (simp add: field_simps)
  have c2: "(ky \<omega>0 - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega>0 - kz \<omega>s) = 0"
    using d by (simp add: field_simps)
  show ?thesis unfolding cvec_dip_def c1 c2 by simp
qed

text \<open>\<^bold>\<open>Full main-beam power for every configuration.\<close>  Since \<open>cvec\<^sub>dip \<omega>\<^sub>0 \<omega>\<^sub>s \<omega>\<^sub>0 = 0\<close>, all \<open>N\<close>
  array phases at \<open>\<omega>\<^sub>0\<close> are \<open>0\<close>, so \<open>A(\<bm>x,\<omega>\<^sub>0) = N\<close> and \<open>P(\<bm>x) = g(\<omega>\<^sub>0) N\<^sup>2 = N\<^sup>2\<bar>e(\<theta>\<^sub>0)\<bar>\<^sup>2\<close>
  for \<^emph>\<open>every\<close> \<open>\<bm>x\<close>; the main-beam constraint reduces to \<open>p\<^sub>min \<le> N\<^sup>2\<bar>e(\<theta>\<^sub>0)\<bar>\<^sup>2\<close>.\<close>

lemma af_at_main:
  assumes "kz \<omega>s \<noteq> kz \<omega>0"
  shows "af (cvec_dip \<omega>0 \<omega>s) (x::(real^2)^'n) \<omega>0 = of_nat CARD('n)"
  by (simp add: af_def cvec_dip_at_main[OF assms])

lemma Upow_at_main:
  assumes "kz \<omega>s \<noteq> kz \<omega>0"
  shows "Upow (cvec_dip \<omega>0 \<omega>s) g (x::(real^2)^'n) \<omega>0 = g \<omega>0 * (real CARD('n))\<^sup>2"
proof -
  have "cmod (af (cvec_dip \<omega>0 \<omega>s) x \<omega>0) = real CARD('n)"
    by (simp add: af_at_main[OF assms])
  thus ?thesis by (simp add: Upow_def)
qed

text \<open>\<^bold>\<open>Inner product on \<open>\<real>\<^sup>2\<close> and the spacing lower bounds.\<close>  The full inter-element
  distance \<open>spdist\<close> dominates each planar coordinate gap, \<open>\<bar>\<Delta>x\<bar>, \<bar>\<Delta>y\<bar> \<le> spdist\<close> (a square
  root of a sum of squares is \<open>\<ge>\<close> the root of one of them) --- so it suffices to spread the
  elements along \<^emph>\<open>one\<close> coordinate to satisfy the spacing constraint.\<close>

lemma inner_real2: "(a::real^2) \<bullet> b = a$1 * b$1 + a$2 * b$2"
  by (simp add: inner_vec_def sum_2)

lemma spdist_ge_abs1: "\<bar>p$1 - q$1\<bar> \<le> spdist A B D p q"
proof -
  have le: "(p $ 1 - q $ 1)\<^sup>2 \<le> (p $ 1 - q $ 1)\<^sup>2 + (p $ 2 - q $ 2)\<^sup>2
              + ((A * (p $ 1 - q $ 1) + B * (p $ 2 - q $ 2)) / D)\<^sup>2"
    using zero_le_power2[of "p$2-q$2"]
          zero_le_power2[of "(A*(p$1-q$1)+B*(p$2-q$2))/D"] by linarith
  have "\<bar>p$1-q$1\<bar> = sqrt ((p$1-q$1)\<^sup>2)" by simp
  also have "\<dots> \<le> spdist A B D p q"
    unfolding spdist_def by (rule real_sqrt_le_mono[OF le])
  finally show ?thesis .
qed

lemma spdist_ge_abs2: "\<bar>p$2 - q$2\<bar> \<le> spdist A B D p q"
proof -
  have le: "(p $ 2 - q $ 2)\<^sup>2 \<le> (p $ 1 - q $ 1)\<^sup>2 + (p $ 2 - q $ 2)\<^sup>2
              + ((A * (p $ 1 - q $ 1) + B * (p $ 2 - q $ 2)) / D)\<^sup>2"
    using zero_le_power2[of "p$1-q$1"]
          zero_le_power2[of "(A*(p$1-q$1)+B*(p$2-q$2))/D"] by linarith
  have "\<bar>p$2-q$2\<bar> = sqrt ((p$2-q$2)\<^sup>2)" by simp
  also have "\<dots> \<le> spdist A B D p q"
    unfolding spdist_def by (rule real_sqrt_le_mono[OF le])
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The null vanishes once the phases are the \<open>N\<close>th roots of unity.\<close>  If the array
  positions, enumerated by a bijection \<open>f\<close> of \<open>{..<N}\<close>, give phase
  \<open>cvec\<^sub>dip(\<omega>\<^sub>null)\<cdot>x\<^bsub>f k\<^esub> = 2\<pi>k/N\<close>, then \<open>A(\<bm>x,\<omega>\<^sub>null) = \<Sum>\<^bsub>k<N\<^esub> e\<^bsup>-2\<pi>\<ii>k/N\<^esup> = 0\<close>
  (reindexing by \<open>f\<close> + @{thm sum_cis_neg_roots_unity}).\<close>

lemma af_null_zero:
  fixes x :: "(real^2)^'n" and f :: "nat \<Rightarrow> 'n"
  assumes N: "CARD('n) > 1"
    and bij: "bij_betw f {..<CARD('n)} (UNIV::'n set)"
    and phase: "\<And>k. k < CARD('n) \<Longrightarrow>
                 cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (x $ f k) = 2 * pi * real k / real CARD('n)"
  shows "af (cvec_dip \<omega>0 \<omega>s) x \<omega>n = 0"
proof -
  have "af (cvec_dip \<omega>0 \<omega>s) x \<omega>n
          = (\<Sum>m\<in>UNIV. cis (- (cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (x $ m))))"
    by (simp add: af_def)
  also have "\<dots> = (\<Sum>k<CARD('n). cis (- (cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (x $ f k))))"
    by (rule sum.reindex_bij_betw[OF bij,
          where g = "\<lambda>m. cis (- (cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (x $ m)))", symmetric])
  also have "\<dots> = (\<Sum>k<CARD('n). cis (- (2 * pi * real k / real CARD('n))))"
    using phase by (intro sum.cong refl) simp
  also have "\<dots> = 0" by (rule sum_cis_neg_roots_unity[OF N])
  finally show ?thesis .
qed

lemma nat_real_abs_diff_ge1:
  fixes k j :: nat
  assumes "k \<noteq> j" shows "(1::real) \<le> \<bar>real k - real j\<bar>"
proof -
  have "k < j \<or> j < k" using assms by linarith
  thus ?thesis
  proof
    assume "k < j" hence "k + 1 \<le> j" by simp
    hence "real k + 1 \<le> real j" using of_nat_le_iff by fastforce
    thus ?thesis by simp
  next
    assume "j < k" hence "j + 1 \<le> k" by simp
    hence "real j + 1 \<le> real k" using of_nat_le_iff by fastforce
    thus ?thesis by simp
  qed
qed

lemma gain_dip_nonneg: "0 \<le> gain_dip \<omega>"
  by (simp add: gain_dip_def gdip_eq_edip_sq)

text \<open>\<^bold>\<open>Parameterised witness construction.\<close>  For any target spacing \<open>s>0\<close> there is a
  configuration that exactly nulls the array factor at \<open>\<omega>\<^sub>null\<close> and whose elements are
  pairwise \<open>\<ge> s\<close> apart (in the \<open>spdist\<close> metric).  Both the closed-feasibility nonemptiness
  (\<open>s = d\<^sub>min\<close>) and the open-interior result (\<open>s > d\<^sub>min\<close>, giving \<^emph>\<open>strict\<close> spacing) specialise
  this.  Construction: enumerate by a bijection \<open>f\<close> of \<open>{..<N}\<close>, place element \<open>f k\<close> to
  solve \<open>\<Q>x'+\<P>y' = 2\<pi>k/N\<close> along the axis with nonzero coefficient, spreading the other
  coordinate as \<open>s\<cdot>k\<close>.\<close>

lemma feasible_witness_exists:
  fixes \<omega>0 \<omega>s \<omega>n :: angle and s A B D :: real
  assumes N: "CARD('n) > 1"
    and cn: "cvec_dip \<omega>0 \<omega>s \<omega>n \<noteq> 0"
    and spos: "0 < s"
  shows "\<exists>x::(real^2)^'n. af (cvec_dip \<omega>0 \<omega>s) x \<omega>n = 0
            \<and> (\<forall>m m'. m \<noteq> m' \<longrightarrow> s \<le> spdist A B D (x $ m) (x $ m'))"
proof -
  define c1 where "c1 = cvec_dip \<omega>0 \<omega>s \<omega>n $ 1"
  define c2 where "c2 = cvec_dip \<omega>0 \<omega>s \<omega>n $ 2"
  define t where "t = (\<lambda>k::nat. 2 * pi * real k / real CARD('n))"
  obtain f where "bij_betw f {0..<CARD('n)} (UNIV::'n set)"
    using ex_bij_betw_nat_finite[of "UNIV::'n set"] N card.infinite gr_implies_not0 by blast
  hence bijf: "bij_betw f {..<CARD('n)} (UNIV::'n set)" by (simp add: atLeast0LessThan)
  define idx where "idx = inv_into {..<CARD('n)} f"
  have idx_inj: "inj idx"
    unfolding idx_def by (metis bijf bij_betw_imp_surj_on inj_on_inv_into order_refl)
  have idx_f: "idx (f k) = k" if "k < CARD('n)" for k
    using that bijf by (simp add: idx_def bij_betw_imp_inj_on inv_into_f_f)
  have ex_p: "\<exists>p::nat \<Rightarrow> real^2.
       (\<forall>k. c1 * (p k $ 1) + c2 * (p k $ 2) = t k)
     \<and> (\<forall>k j. k \<noteq> j \<longrightarrow> s \<le> \<bar>p k $ 1 - p j $ 1\<bar> \<or> s \<le> \<bar>p k $ 2 - p j $ 2\<bar>)"
  proof (cases "c2 = 0")
    case False
    define p where "p = (\<lambda>k. vector [s * real k, (t k - c1 * (s * real k)) / c2] :: real^2)"
    have ph: "c1 * (p k $ 1) + c2 * (p k $ 2) = t k" for k
      using False by (simp add: p_def)
    have sp: "s \<le> \<bar>p k $ 1 - p j $ 1\<bar>" if "k \<noteq> j" for k j
    proof -
      have "p k $ 1 - p j $ 1 = s * (real k - real j)"
        by (simp add: p_def right_diff_distrib)
      hence "\<bar>p k $ 1 - p j $ 1\<bar> = s * \<bar>real k - real j\<bar>"
        using spos by (simp add: abs_mult abs_of_pos)
      moreover have "s * 1 \<le> s * \<bar>real k - real j\<bar>"
        using spos nat_real_abs_diff_ge1[OF that] by (intro mult_left_mono) auto
      ultimately show ?thesis by simp
    qed
    show ?thesis by (intro exI[of _ p] conjI allI impI) (use ph sp in blast)+
  next
    case True
    hence c1ne: "c1 \<noteq> 0"
    proof -
      have "c1 \<noteq> 0 \<or> c2 \<noteq> 0"
        using cn by (auto simp: c1_def c2_def vec_eq_iff forall_2,
          metis (mono_tags, opaque_lifting) Finite_Cartesian_Product.vec_eq_iff exhaust_2 zero_index)
      thus ?thesis using True by simp
    qed
    define p where "p = (\<lambda>k. vector [t k / c1, s * real k] :: real^2)"
    have ph: "c1 * (p k $ 1) + c2 * (p k $ 2) = t k" for k
      using True c1ne by (simp add: p_def)
    have sp: "s \<le> \<bar>p k $ 2 - p j $ 2\<bar>" if "k \<noteq> j" for k j
    proof -
      have "p k $ 2 - p j $ 2 = s * (real k - real j)"
        by (simp add: p_def right_diff_distrib)
      hence "\<bar>p k $ 2 - p j $ 2\<bar> = s * \<bar>real k - real j\<bar>"
        using spos by (simp add: abs_mult abs_of_pos)
      moreover have "s * 1 \<le> s * \<bar>real k - real j\<bar>"
        using spos nat_real_abs_diff_ge1[OF that] by (intro mult_left_mono) auto
      ultimately show ?thesis by simp
    qed
    show ?thesis by (intro exI[of _ p] conjI allI impI) (use ph sp in blast)+
  qed
  obtain p :: "nat \<Rightarrow> real^2"
    where pphase: "\<And>k. c1 * (p k $ 1) + c2 * (p k $ 2) = t k"
      and pspace: "\<And>k j. k \<noteq> j \<Longrightarrow> s \<le> \<bar>p k $ 1 - p j $ 1\<bar> \<or> s \<le> \<bar>p k $ 2 - p j $ 2\<bar>"
    using ex_p by blast
  define xbar where "xbar = (\<chi> m. p (idx m))"
  have xbar_m: "xbar $ m = p (idx m)" for m by (simp add: xbar_def)
  have afz: "af (cvec_dip \<omega>0 \<omega>s) xbar \<omega>n = 0"
  proof (rule af_null_zero[OF N bijf])
    fix k assume k: "k < CARD('n)"
    have "xbar $ f k = p k" using k by (simp add: xbar_m idx_f)
    thus "cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (xbar $ f k) = 2 * pi * real k / real CARD('n)"
      using pphase[of k]
      by (simp add: inner_real2 c1_def[symmetric] c2_def[symmetric] t_def)
  qed
  have spac: "s \<le> spdist A B D (xbar $ m) (xbar $ m')" if mm: "m \<noteq> m'" for m m'
  proof -
    have "idx m \<noteq> idx m'" using mm idx_inj by (auto dest: injD)
    hence disj: "s \<le> \<bar>p (idx m) $ 1 - p (idx m') $ 1\<bar>
               \<or> s \<le> \<bar>p (idx m) $ 2 - p (idx m') $ 2\<bar>"
      by (rule pspace)
    have d1: "\<bar>p (idx m) $ 1 - p (idx m') $ 1\<bar> \<le> spdist A B D (xbar $ m) (xbar $ m')"
      using spdist_ge_abs1[of "xbar $ m" "xbar $ m'" A B D] by (simp add: xbar_m)
    have d2: "\<bar>p (idx m) $ 2 - p (idx m') $ 2\<bar> \<le> spdist A B D (xbar $ m) (xbar $ m')"
      using spdist_ge_abs2[of "xbar $ m" "xbar $ m'" A B D] by (simp add: xbar_m)
    from disj d1 d2 show ?thesis by auto
  qed
  from afz spac show ?thesis by (intro exI[of _ xbar]) blast
qed

text \<open>\<^bold>\<open>The feasible set is nonempty (D_edit Prop.~openfeas / L450--566).\<close>  Under the
  standing well-posedness conditions --- \<open>cvec\<^sub>dip(\<omega>\<^sub>null) \<noteq> 0\<close> (i.e.\ \<open>(\<Q>,\<P>) \<noteq> 0\<close>),
  \<open>N>1\<close>, \<open>d\<^sub>min>0\<close>, \<open>\<delta>\<^sub>null\<ge>0\<close>, \<open>p\<^sub>min \<le> N\<^sup>2\<bar>e(\<theta>\<^sub>0)\<bar>\<^sup>2\<close>, and \<open><cos\<theta>\<^sub>s \<noteq> <cos\<theta>\<^sub>0\<close> --- there is a
  radius \<open>R>0\<close> and an explicit configuration \<open>\<bar>x \<in> \<F>\<close>.  \<^bold>\<open>Construction:\<close> enumerate the
  elements by a bijection \<open>f\<close> of \<open>{..<N}\<close>; place element \<open>f k\<close> so the reduced phase
  \<open>cvec\<^sub>dip(\<omega>\<^sub>null)\<cdot>x\<^bsub>f k\<^esub> = 2\<pi>k/N\<close> (solving the single linear equation \<open>\<Q>x'+\<P>y' = 2\<pi>k/N\<close>
  along whichever of the two axes has a nonzero coefficient, and spreading the \<^emph>\<open>other\<close>
  coordinate as \<open>d\<^sub>min\<cdot>k\<close> for spacing).  Then \<open>A(\<bar>x,\<omega>\<^sub>null)=0\<close> (roots of unity, @{thm
  af_null_zero}), \<open>c(\<bar>x)=0\<close> (spacing along one axis, @{thm spdist_ge_abs1}), \<open>P(\<bar>x)=N\<^sup>2\<bar>e\<bar>\<^sup>2\<close>
  (@{thm Upow_at_main}), and \<open>\<bar>x\<in>B\<^sub>R\<close> for \<open>R\<close> large.\<close>

lemma Ffeas_dip_nonempty:
  fixes \<omega>0 \<omega>s \<omega>n :: angle and dmin \<delta>null pmin A B D :: real
  assumes N: "CARD('n) > 1"
    and cn: "cvec_dip \<omega>0 \<omega>s \<omega>n \<noteq> 0"
    and dpos: "0 < dmin"
    and dnull: "0 \<le> \<delta>null"
    and pmain: "pmin \<le> gain_dip \<omega>0 * (real CARD('n))\<^sup>2"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
  shows "\<exists>R. \<exists>x::(real^2)^'n. 0 < R
            \<and> x \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>n \<omega>0 \<delta>null pmin"
proof -
  obtain x :: "(real^2)^'n"
    where afz: "af (cvec_dip \<omega>0 \<omega>s) x \<omega>n = 0"
      and spac: "\<forall>m m'. m \<noteq> m' \<longrightarrow> dmin \<le> spdist A B D (x $ m) (x $ m')"
    using feasible_witness_exists[OF N cn dpos, of A B D] by blast
  \<comment> \<open>spacing \<open>\<Longrightarrow> c(\<bar>x) = 0\<close>\<close>
  have cpen0: "cpen dmin A B D x = 0"
    unfolding cpen_def
  proof (intro sum.neutral ballI)
    fix q :: "'n \<times> 'n" assume "q \<in> {q. fst q \<noteq> snd q}"
    hence "fst q \<noteq> snd q" by simp
    hence "dmin \<le> spdist A B D (x $ fst q) (x $ snd q)" using spac by blast
    thus "max 0 (dmin - spdist A B D (x $ fst q) (x $ snd q)) = 0" by simp
  qed
  \<comment> \<open>null power \<open>= 0\<close>, main-beam power \<open>= g(\<omega>\<^sub>0)N\<^sup>2\<close>, and a containing ball\<close>
  have nullpow: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>n = 0"
    by (simp add: Upow_def afz)
  have mainpow: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0 = gain_dip \<omega>0 * (real CARD('n))\<^sup>2"
    by (rule Upow_at_main[OF hsep])
  define R where "R = norm x + 1"
  have R0: "0 < R" by (simp add: R_def add_nonneg_pos)
  have inball: "x \<in> cball 0 R" by (simp add: R_def dist_norm)
  \<comment> \<open>assemble membership in \<open>\<F>\<close>\<close>
  have "x \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>n \<omega>0 \<delta>null pmin"
    unfolding Ffeas_def
  proof (intro IntI)
    show "x \<in> cpen dmin A B D -` {0}" using cpen0 by simp
    show "x \<in> (\<lambda>x. Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>n) -` {0..\<delta>null}"
      using nullpow dnull by simp
    show "x \<in> (\<lambda>x. Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0)
                  -` {pmin .. gain_dip \<omega>0 * (real CARD('n))\<^sup>2}"
      using mainpow pmain by simp
    show "x \<in> cball 0 R" by (rule inball)
  qed
  thus ?thesis using R0 by blast
qed

text \<open>\<^bold>\<open>The feasible set has nonempty interior (D_edit Remark~ball\_inside\_F / L566).\<close>  With
  \<^emph>\<open>strict\<close> margins --- a spacing target \<open>s>d\<^sub>min\<close>, \<open>\<delta>\<^sub>null>0\<close>, \<open>p\<^sub>min < N\<^sup>2\<bar>e(\<theta>\<^sub>0)\<bar>\<^sup>2\<close> --- the
  explicit witness is \<^emph>\<open>strictly\<close> feasible, so a whole ball lies in \<open>\<F>\<close> (@{thm
  ball_inside_Ffeas}).  This open feasible body is the Baire arena into which the
  meagerness of degenerate configurations is intersected to extract a \<^emph>\<open>regular\<close> feasible
  point (the remaining step of \<open>regular_feasible_point_dip\<close>).\<close>

lemma Ffeas_dip_has_interior:
  fixes \<omega>0 \<omega>s \<omega>n :: angle and dmin \<delta>null pmin A B D :: real
  assumes N: "CARD('n) > 1"
    and cn: "cvec_dip \<omega>0 \<omega>s \<omega>n \<noteq> 0"
    and dpos: "0 < dmin"
    and dnull: "0 < \<delta>null"
    and pmain: "pmin < gain_dip \<omega>0 * (real CARD('n))\<^sup>2"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
  shows "\<exists>R. \<exists>x::(real^2)^'n. \<exists>\<rho>>0. 0 < R
            \<and> ball x \<rho> \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>n \<omega>0 \<delta>null pmin"
proof -
  \<comment> \<open>build the witness with strict spacing target \<open>s = d\<^sub>min + 1 > d\<^sub>min\<close>\<close>
  have spos: "0 < dmin + 1" using dpos by simp
  obtain x :: "(real^2)^'n"
    where afz: "af (cvec_dip \<omega>0 \<omega>s) x \<omega>n = 0"
      and spac: "\<forall>m m'. m \<noteq> m' \<longrightarrow> dmin + 1 \<le> spdist A B D (x $ m) (x $ m')"
    using feasible_witness_exists[OF N cn spos, of A B D] by blast
  have spac_strict: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (x $ fst p) (x $ snd p)"
  proof (intro ballI)
    fix p :: "'n \<times> 'n" assume "p \<in> {p. fst p \<noteq> snd p}"
    hence "fst p \<noteq> snd p" by simp
    hence "dmin + 1 \<le> spdist A B D (x $ fst p) (x $ snd p)" using spac by blast
    thus "dmin < spdist A B D (x $ fst p) (x $ snd p)" by simp
  qed
  \<comment> \<open>strict null and main-beam margins\<close>
  have Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>n < \<delta>null"
    using dnull by (simp add: Upow_def afz)
  have Pgt: "pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0"
    using pmain by (simp add: Upow_at_main[OF hsep])
  define R where "R = norm x + 1"
  have R0: "0 < R" by (simp add: R_def add_nonneg_pos)
  have inball: "x \<in> ball 0 R" by (simp add: R_def dist_norm)
  \<comment> \<open>a strictly feasible point has a feasible ball around it\<close>
  obtain \<rho> where "0 < \<rho>"
      and "ball x \<rho> \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>n \<omega>0 \<delta>null pmin"
    using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac_strict Nlt Pgt inball]
    by blast
  thus ?thesis using R0 by blast
qed

text \<open>\<^bold>\<open>Open feasible family (D_edit / unified Prop.~openfeas).\<close>  Packaging the interior as
  the paper's statement: there is a \<^emph>\<open>nonempty open\<close> \<open>U\<^sub>feas \<subseteq> \<F>\<close> for the actual dipole.
  This is the exact arena for the Baire step of \<open>regular_feasible_point_dip\<close>: degenerate
  configurations are meager (the determinant payoff \<open>Phi_bad_meager\<close>), so their complement
  inside this nonempty open set is dense, hence contains a regular feasible configuration.\<close>

lemma Ffeas_dip_open_feasible:
  fixes \<omega>0 \<omega>s \<omega>n :: angle and dmin \<delta>null pmin A B D :: real
  assumes N: "CARD('n) > 1"
    and cn: "cvec_dip \<omega>0 \<omega>s \<omega>n \<noteq> 0"
    and dpos: "0 < dmin"
    and dnull: "0 < \<delta>null"
    and pmain: "pmin < gain_dip \<omega>0 * (real CARD('n))\<^sup>2"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
  shows "\<exists>R. \<exists>V::((real^2)^'n) set. 0 < R \<and> open V \<and> V \<noteq> {}
            \<and> V \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>n \<omega>0 \<delta>null pmin"
proof -
  obtain R and x :: "(real^2)^'n" and \<rho> where
    R0: "0 < R" and \<rho>0: "0 < \<rho>"
    and sub: "ball x \<rho> \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>n \<omega>0 \<delta>null pmin"
    using Ffeas_dip_has_interior[OF N cn dpos dnull pmain hsep] by blast
  have "open (ball x \<rho>)" by simp
  moreover have "ball x \<rho> \<noteq> {}" using \<rho>0 by auto
  ultimately show ?thesis using R0 sub by blast
qed


subsection \<open>Step 1 of \<open>prop:dimZ\<close>: \<open>\<Phi>\<close> factors through the moment map \<open>M_paper\<close>\<close>

text \<open>\<^bold>\<open>The bad-point map's ingredients ARE the moment map.\<close>  The local first/second
  moments \<^const>\<open>Mmom\<close>, \<^const>\<open>M2mom\<close> and the array factor \<^const>\<open>A_cart\<close> --- through
  which \<open>gradU\<close>/\<open>HessU\<close> (hence \<open>\<Phi> = Phibad\<close>) are expressed --- are exactly the six
  components of the \<^emph>\<open>determinant-side\<close> moment map \<^const>\<open>M_paper\<close> (whose configuration
  Jacobian is \<open>bigJ\<close>).  This identity is the bridge \<open>\<Phi> = F \<circ> \<M>\<close>: it lets the proven
  \<open>bigJ\<close>-surjectivity (\<open>lem:Msurj\<close>) act on \<open>\<Phi>\<close>'s derivative.\<close>

lemma M_paper_eq_robust_moments:
  "M_paper x (cvec \<omega>) = vector
     [ A_cart cvec x \<omega>, Mmom cvec x \<omega> 1, Mmom cvec x \<omega> 2,
       M2mom cvec x \<omega> 1 1, M2mom cvec x \<omega> 1 2, M2mom cvec x \<omega> 2 2 ]"
proof -
  have a1: "A_moment x (cvec \<omega>) = A_cart cvec x \<omega>"
    by (simp add: A_moment_def phase_def A_cart_def)
  have a2: "M1_moment x (cvec \<omega>) = Mmom cvec x \<omega> 1"
    by (simp add: M1_moment_def phase_def Mmom_def)
  have a3: "M2_moment x (cvec \<omega>) = Mmom cvec x \<omega> 2"
    by (simp add: M2_moment_def phase_def Mmom_def)
  have a4: "M11_moment x (cvec \<omega>) = M2mom cvec x \<omega> 1 1"
    by (simp add: M11_moment_def phase_def M2mom_def power2_eq_square of_real_mult)
  have a5: "M12_moment x (cvec \<omega>) = M2mom cvec x \<omega> 1 2"
    by (simp add: M12_moment_def phase_def M2mom_def w_M12_def of_real_mult)
  have a6: "M22_moment x (cvec \<omega>) = M2mom cvec x \<omega> 2 2"
    by (simp add: M22_moment_def phase_def M2mom_def power2_eq_square of_real_mult)
  show ?thesis
    unfolding M_paper_def by (simp add: a1 a2 a3 a4 a5 a6)
qed

text \<open>The six component projections (reusable rewrites \<open>moment \<rightarrow> M_paper\<close> coordinate).\<close>

lemma M_paper_proj_A:   "M_paper x (cvec \<omega>) $ 1 = A_cart cvec x \<omega>"
  by (simp add: A_moment_def phase_def A_cart_def)
lemma M_paper_proj_M1:  "M_paper x (cvec \<omega>) $ 2 = Mmom cvec x \<omega> 1"
  by (simp add: M1_moment_def phase_def Mmom_def)
lemma M_paper_proj_M2:  "M_paper x (cvec \<omega>) $ 3 = Mmom cvec x \<omega> 2"
  by (simp add: M2_moment_def phase_def Mmom_def)
lemma M_paper_proj_M11: "M_paper x (cvec \<omega>) $ 4 = M2mom cvec x \<omega> 1 1"
  by (simp add: M11_moment_def phase_def M2mom_def power2_eq_square of_real_mult)
lemma M_paper_proj_M12: "M_paper x (cvec \<omega>) $ 5 = M2mom cvec x \<omega> 1 2"
  by (simp add: M12_moment_def phase_def M2mom_def w_M12_def of_real_mult)
lemma M_paper_proj_M22: "M_paper x (cvec \<omega>) $ 6 = M2mom cvec x \<omega> 2 2"
  by (simp add: M22_moment_def phase_def M2mom_def power2_eq_square of_real_mult)

text \<open>\<^bold>\<open>The gradient half of \<open>\<Phi> = F \<circ> \<M>\<close>.\<close>  The angular partials \<open>\<Phi>\<^sub>1 = \<partial>U/\<partial>\<omega>\<^sub>1\<close>,
  \<open>\<Phi>\<^sub>2 = \<partial>U/\<partial>\<omega>\<^sub>2\<close> (the first two components of \<open>Phibad\<close>) depend on \<open>(\<bm>x,\<omega>)\<close> \<^emph>\<open>only through\<close>
  the moment map \<open>M_paper\<close>'s first three coordinates \<open>A, M\<^sub>1, M\<^sub>2\<close> (and the gain/steering
  jet \<open>gain, dgain, dc\<close>, which are parameters).  This is \<open>\<Phi>\<^sub>1\<^sub>,\<^sub>2\<close> as an explicit function of
  \<open>\<M>\<close>.\<close>

lemma gradU_component_via_M_paper:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and dc :: "angle \<Rightarrow> planar" and dgain :: "angle \<Rightarrow> real"
    and x :: "planar^'n" and \<omega> :: angle
  assumes dcvec: "(cvec has_derivative dc) (at \<omega>)"
    and dgn: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega> $ j
         = dgain (axis j 1) * (cmod (M_paper x (cvec \<omega>) $ 1))\<^sup>2
           + gain \<omega> * (2 * Re (cnj (M_paper x (cvec \<omega>) $ 1)
                * ((- \<i>) * complex_of_real ((dc (axis j 1))$1) * (M_paper x (cvec \<omega>) $ 2)
                 + (- \<i>) * complex_of_real ((dc (axis j 1))$2) * (M_paper x (cvec \<omega>) $ 3))))"
proof -
  have G: "gradU cvec gain x \<omega> $ j
        = dgain (axis j 1) * (cmod (A_cart cvec x \<omega>))\<^sup>2
          + gain \<omega> * (2 * Re (cnj (A_cart cvec x \<omega>)
                * (\<Sum>k\<in>UNIV. (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)))"
    by (rule gradU_component_via_moments[OF dcvec dgn])
  have S: "(\<Sum>k\<in>(UNIV::2 set). (- \<i>) * complex_of_real ((dc (axis j 1))$k) * Mmom cvec x \<omega> k)
        = (- \<i>) * complex_of_real ((dc (axis j 1))$1) * Mmom cvec x \<omega> 1
        + (- \<i>) * complex_of_real ((dc (axis j 1))$2) * Mmom cvec x \<omega> 2"
    by (simp add: sum_2)
  show ?thesis
    by (simp only: G S M_paper_proj_A M_paper_proj_M1 M_paper_proj_M2)
qed


subsection \<open>Step 1 Hessian half: the \<open>\<omega>\<close>--\<open>c\<close> bridge and moment-space \<open>c\<close>-derivatives\<close>

text \<open>\<^bold>\<open>The array factor as a function of the wavevector \<open>c\<close>.\<close>  Writing the pattern through
  \<open>c = cvec \<omega>\<close> makes the moments appear by pure differentiation: \<open>\<partial>\<^bsub>c\<^sub>j\<^esub>A = -\<ii> M\<^sub>j\<close> and
  \<open>\<partial>\<^bsub>c\<^sub>k\<^esub>\<partial>\<^bsub>c\<^sub>l\<^esub>A = -M\<^sub>k\<^sub>l\<close>, with \<^emph>\<open>no\<close> steering jet --- the clean moment-space form.  The
  \<open>\<omega>\<close>-derivatives then follow by the chain/product rule through \<open>cvec\<close> and \<open>gain\<close>.\<close>

definition Afun :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> complex" where
  "Afun x c = (\<Sum>n\<in>UNIV. cis (-(c \<bullet> (x$n))))"

definition Mcfun :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> complex" where
  "Mcfun x c k = (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * cis (-(c \<bullet> (x$n))))"

definition M2cfun :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> 2 \<Rightarrow> complex" where
  "M2cfun x c k l =
     (\<Sum>n\<in>UNIV. complex_of_real ((x$n)$k) * complex_of_real ((x$n)$l) * cis (-(c \<bullet> (x$n))))"

lemma A_cart_eq_Afun: "A_cart cvec x \<omega> = Afun x (cvec \<omega>)"
  by (simp add: A_cart_def Afun_def)
lemma Mmom_eq_Mcfun: "Mmom cvec x \<omega> k = Mcfun x (cvec \<omega>) k"
  by (simp add: Mmom_def Mcfun_def)
lemma M2mom_eq_M2cfun: "M2mom cvec x \<omega> k l = M2cfun x (cvec \<omega>) k l"
  by (simp add: M2mom_def M2cfun_def)

text \<open>First \<open>c\<close>-derivative of the array factor: \<open>D\<^sub>c A(h) = -\<ii> \<Sum>\<^sub>n (h\<cdot>x\<^sub>n) e\<^bsup>-\<ii> c\<cdot>x\<^sub>n\<^esup>\<close>.\<close>

lemma has_derivative_Afun_c:
  "(Afun x has_derivative
      (\<lambda>h. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
proof -
  have tderiv: "((\<lambda>c. cis (-(c \<bullet> (x$n)))) has_derivative
                (\<lambda>h. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
    for n
  proof -
    have inner_d: "((\<lambda>c::real^2. -(c \<bullet> (x$n))) has_derivative (\<lambda>h. -(h \<bullet> (x$n)))) (at c)"
      by (auto intro!: derivative_eq_intros)
    have cis_d: "(cis has_derivative (\<lambda>r. r *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))) (at (-(c \<bullet> (x$n))))"
      by (auto intro!: derivative_eq_intros)
    have "((\<lambda>c. cis (-(c \<bullet> (x$n)))) has_derivative
            (\<lambda>h. (-(h \<bullet> (x$n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))) (at c)"
      using has_derivative_compose[OF inner_d cis_d] by (simp add: o_def)
    moreover have "(\<lambda>h. (-(h \<bullet> (x$n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))
                 = (\<lambda>h. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))"
      by (rule ext) (simp add: scaleR_conv_of_real algebra_simps)
    ultimately show ?thesis by simp
  qed
  show ?thesis unfolding Afun_def
    by (rule has_derivative_sum) (rule tderiv)
qed

text \<open>The \<open>j\<close>-th \<open>c\<close>-partial of \<open>A\<close> is \<open>-\<ii>\<close> times the \<open>j\<close>-th moment.\<close>

lemma Afun_c_partial:
  "(\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((axis j 1) \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
     = (- \<i>) * Mcfun x c j"
  by (simp add: Mcfun_def inner_axis sum_distrib_left mult.assoc,
      simp add: cart_eq_inner_axis inner_commute)

text \<open>The per-term \<open>c\<close>-derivative of the phase factor (reused below).\<close>

lemma has_derivative_cis_c:
  fixes x :: "(real^2)^'n" and c :: "real^2" and n :: 'n
  shows "((\<lambda>c. cis (-(c \<bullet> (x$n)))) has_derivative
      (\<lambda>h. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
proof -
  have inner_d: "((\<lambda>c::real^2. -(c \<bullet> (x$n))) has_derivative (\<lambda>h. -(h \<bullet> (x$n)))) (at c)"
    by (auto intro!: derivative_eq_intros)
  have cis_d: "(cis has_derivative (\<lambda>r. r *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))) (at (-(c \<bullet> (x$n))))"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>c. cis (-(c \<bullet> (x$n)))) has_derivative
          (\<lambda>h. (-(h \<bullet> (x$n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))) (at c)"
    using has_derivative_compose[OF inner_d cis_d] by (simp add: o_def)
  moreover have "(\<lambda>h. (-(h \<bullet> (x$n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x$n)))))
               = (\<lambda>h. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))"
    by (rule ext) (simp add: scaleR_conv_of_real algebra_simps)
  ultimately show ?thesis by simp
qed

text \<open>First \<open>c\<close>-derivative of the \<open>k\<close>-th moment: \<open>D\<^sub>c M\<^sub>k(h) = -\<ii> \<Sum>\<^sub>n (x\<^sub>n)\<^sub>k (h\<cdot>x\<^sub>n) e\<^bsup>-\<ii> c\<cdot>x\<^sub>n\<^esup>\<close>;
  its \<open>l\<close>-th partial is \<open>-\<ii> M\<^sub>k\<^sub>l\<close> --- this is where the second moments enter.\<close>

lemma has_derivative_Mcfun_c:
  "((\<lambda>c. Mcfun x c k) has_derivative
      (\<lambda>h. \<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                       * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
proof -
  have tderiv: "((\<lambda>c. complex_of_real ((x$n)$k) * cis (-(c \<bullet> (x$n)))) has_derivative
                (\<lambda>h. (- \<i>) * complex_of_real ((x$n)$k)
                       * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))) (at c)"
    for n
  proof -
    have "((\<lambda>c. complex_of_real ((x$n)$k) * cis (-(c \<bullet> (x$n)))) has_derivative
            (\<lambda>h. complex_of_real ((x$n)$k)
                  * ((- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
                + 0 * cis (-(c \<bullet> (x$n))))) (at c)"
      by (rule has_derivative_mult[OF has_derivative_const has_derivative_cis_c])
    moreover have "(\<lambda>h. complex_of_real ((x$n)$k)
                  * ((- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
                + 0 * cis (-(c \<bullet> (x$n))))
                 = (\<lambda>h. (- \<i>) * complex_of_real ((x$n)$k)
                       * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))"
      by (rule ext) (simp add: algebra_simps)
    ultimately show ?thesis by simp
  qed
  show ?thesis unfolding Mcfun_def
    by (rule has_derivative_sum) (rule tderiv)
qed

lemma Mcfun_c_partial:
  "(\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real ((axis l 1) \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
     = (- \<i>) * M2cfun x c k l"
proof -
  have ax: "(axis l 1) \<bullet> (x$n) = (x$n)$l" for n
    by (simp add: cart_eq_inner_axis inner_commute)
  show ?thesis
    by (simp add: ax M2cfun_def sum_distrib_left mult.assoc)
qed

text \<open>\<^bold>\<open>The \<open>c\<close>-gradient of \<open>\<bar>A\<bar>\<^sup>2\<close> in moment form.\<close>  Specialising
  @{thm gradU_component_real_moments} to \<open>c\<close>-coordinates (\<open>cvec = id\<close>, \<open>gain \<equiv> 1\<close>, so the
  steering/gain jet drops out) gives the clean gradient
  \<open>\<partial>\<^bsub>c\<^sub>j\<^esub>\<bar>A\<bar>\<^sup>2 = 2(\<real>A\<cdot>\<I>M\<^sub>j - \<I>A\<cdot>\<real>M\<^sub>j)\<close> --- the field we differentiate once more for the
  moment-space Hessian.\<close>

lemma gradU_c_field:
  "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ j
     = 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j))"
proof -
  have d1: "((\<lambda>c::real^2. c) has_derivative (\<lambda>h. h)) (at c)"
    by (rule has_derivative_ident)
  have d2: "((\<lambda>_::real^2. 1::real) has_derivative (\<lambda>_. 0)) (at c)"
    by (rule has_derivative_const)
  have "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ j
        = (\<lambda>_. 0) (axis j 1)
            * ((Re (A_cart (\<lambda>c. c) x c))\<^sup>2 + (Im (A_cart (\<lambda>c. c) x c))\<^sup>2)
          + (\<lambda>_. 1) c * (2 * (\<Sum>k\<in>UNIV. ((\<lambda>h. h) (axis j 1))$k
                 * (Re (A_cart (\<lambda>c. c) x c) * Im (Mmom (\<lambda>c. c) x c k)
                    - Im (A_cart (\<lambda>c. c) x c) * Re (Mmom (\<lambda>c. c) x c k))))"
    by (rule gradU_component_real_moments[OF d1 d2])
  also have "\<dots> = 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j))"
    by (simp add: A_cart_eq_Afun Mmom_eq_Mcfun axis_def if_distrib sum.delta cong: if_cong,
        smt (verit, ccfv_SIG) exhaust_2 sum_2 zero_neq_one)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Pushing \<open>\<real>/\<I>\<close> through the derivative sums.\<close>  The directional \<open>c\<close>-derivatives of
  \<open>A\<close> and \<open>M\<^sub>k\<close> collect, after \<open>h\<cdot>x\<^sub>n = \<Sum>\<^sub>l h\<^sub>l (x\<^sub>n)\<^sub>l\<close> and a sum swap, into moments.\<close>

lemma Re_neg_i_of_real: "Re ((- \<i>) * complex_of_real r * z) = r * Im z"
  by simp
lemma Im_neg_i_of_real: "Im ((- \<i>) * complex_of_real r * z) = - (r * Re z)"
  by simp

lemma inner_real2_sum: "(h::real^2) \<bullet> (p::real^2) = (\<Sum>l\<in>UNIV. (h$l) * (p$l))"
  by (simp add: inner_vec_def)

lemma Re_neg_i_of_real2:
  "Re ((- \<i>) * complex_of_real r * complex_of_real s * z) = (r * s) * Im z"
  by simp
lemma Im_neg_i_of_real2:
  "Im ((- \<i>) * complex_of_real r * complex_of_real s * z) = - ((r * s) * Re z)"
  by simp

lemma ReDAfun:
  fixes x :: "(real^2)^'n" and c h :: "real^2"
  shows "Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
       = (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l))"
proof -
  have "Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
      = (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (h$l) * ((x$n)$l * Im (cis (-(c \<bullet> (x$n))))))"
    by (simp add: Re_sum Re_neg_i_of_real inner_real2_sum sum_distrib_right mult.assoc)
  also have "\<dots> = (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (h$l) * ((x$n)$l * Im (cis (-(c \<bullet> (x$n))))))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l))"
    by (simp add: sum_distrib_left Mcfun_def Im_sum)
  finally show ?thesis .
qed

lemma ImDAfun:
  fixes x :: "(real^2)^'n" and c h :: "real^2"
  shows "Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
       = - (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))"
proof -
  have "Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
      = - (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (h$l) * ((x$n)$l * Re (cis (-(c \<bullet> (x$n))))))"
    by (simp add: Im_sum Im_neg_i_of_real inner_real2_sum sum_distrib_right mult.assoc sum_negf)
  also have "\<dots> = - (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (h$l) * ((x$n)$l * Re (cis (-(c \<bullet> (x$n))))))"
    by (rule arg_cong[where f = uminus]) (rule sum.swap)
  also have "\<dots> = - (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))"
    by (simp add: sum_distrib_left Mcfun_def Re_sum)
  finally show ?thesis .
qed

lemma Im_M2cfun:
  fixes x :: "(real^2)^'n"
  shows "Im (M2cfun x c k l) = (\<Sum>n\<in>UNIV. ((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n)))))"
  by (simp add: M2cfun_def Im_sum)

lemma Re_M2cfun:
  fixes x :: "(real^2)^'n"
  shows "Re (M2cfun x c k l) = (\<Sum>n\<in>UNIV. ((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n)))))"
  by (simp add: M2cfun_def Re_sum)

lemma ReDMfun:
  fixes x :: "(real^2)^'n" and c h :: "real^2"
  shows "Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
       = (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c k l))"
proof -
  have perterm: "((x$n)$k * (h \<bullet> (x$n))) * Im (cis (-(c \<bullet> (x$n))))
       = (\<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n))))))" for n
  proof -
    have "((x$n)$k * (h \<bullet> (x$n))) * Im (cis (-(c \<bullet> (x$n))))
        = (\<Sum>l\<in>UNIV. (x$n)$k * ((h$l) * (x$n)$l)) * Im (cis (-(c \<bullet> (x$n))))"
      by (simp add: inner_real2_sum sum_distrib_left)
    also have "\<dots> = (\<Sum>l\<in>UNIV. ((x$n)$k * ((h$l) * (x$n)$l)) * Im (cis (-(c \<bullet> (x$n)))))"
      by (simp add: sum_distrib_right sum_negf)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n))))))"
      by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have "Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
      = (\<Sum>n\<in>UNIV. ((x$n)$k * (h \<bullet> (x$n))) * Im (cis (-(c \<bullet> (x$n)))))"
    by (simp add: Re_sum Re_neg_i_of_real2)
  also have "\<dots> = (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n))))))"
    by (rule sum.cong[OF refl]) (rule perterm)
  also have "\<dots> = (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Im (cis (-(c \<bullet> (x$n))))))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c k l))"
    by (simp add: sum_distrib_left Im_M2cfun)
  finally show ?thesis .
qed

lemma ImDMfun:
  fixes x :: "(real^2)^'n" and c h :: "real^2"
  shows "Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
       = - (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c k l))"
proof -
  have perterm: "((x$n)$k * (h \<bullet> (x$n))) * Re (cis (-(c \<bullet> (x$n))))
       = (\<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n))))))" for n
  proof -
    have "((x$n)$k * (h \<bullet> (x$n))) * Re (cis (-(c \<bullet> (x$n))))
        = (\<Sum>l\<in>UNIV. (x$n)$k * ((h$l) * (x$n)$l)) * Re (cis (-(c \<bullet> (x$n))))"
      by (simp add: inner_real2_sum sum_distrib_left)
    also have "\<dots> = (\<Sum>l\<in>UNIV. ((x$n)$k * ((h$l) * (x$n)$l)) * Re (cis (-(c \<bullet> (x$n)))))"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n))))))"
      by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have "Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n))))
      = - (\<Sum>n\<in>UNIV. ((x$n)$k * (h \<bullet> (x$n))) * Re (cis (-(c \<bullet> (x$n)))))"
    by (simp add: Im_sum Im_neg_i_of_real2 sum_negf)
  also have "\<dots> = - (\<Sum>n\<in>UNIV. \<Sum>l\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n))))))"
    by (rule arg_cong[where f = uminus], rule sum.cong[OF refl], rule perterm)
  also have "\<dots> = - (\<Sum>l\<in>UNIV. \<Sum>n\<in>UNIV. (h$l) * (((x$n)$k * (x$n)$l) * Re (cis (-(c \<bullet> (x$n))))))"
    by (rule arg_cong[where f = uminus]) (rule sum.swap)
  also have "\<dots> = - (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c k l))"
    by (simp add: sum_distrib_left Re_M2cfun)
  finally show ?thesis .
qed

definition Hcmat :: "(real^2)^'n \<Rightarrow> real^2 \<Rightarrow> real^2^2" where
  "Hcmat x c = (\<chi> k. \<chi> l. 2 * (Re (cnj (Mcfun x c l) * Mcfun x c k)
                               - Re (cnj (Afun x c) * M2cfun x c k l)))"

text \<open>\<^bold>\<open>The four \<open>c\<close>-derivatives in moment form.\<close>  Compose \<open>\<real>/\<I>\<close> (bounded-linear) with the
  \<open>c\<close>-derivatives of \<open>A\<close>/\<open>M\<^sub>k\<close> and rewrite via the sum lemmas above: \<open>\<partial>\<^sub>c(\<real>A) = \<Sum>\<^sub>l h\<^sub>l \<I>M\<^sub>l\<close>,
  \<open>\<partial>\<^sub>c(\<I>A) = -\<Sum>\<^sub>l h\<^sub>l \<real>M\<^sub>l\<close>, and the \<open>M\<^sub>k\<close>-analogues with the second moments \<open>M\<^sub>k\<^sub>l\<close>.\<close>

lemma dRe_Afun:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "((\<lambda>c. Re (Afun x c)) has_derivative (\<lambda>h. \<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l))) (at c)"
proof (rule has_derivative_eq_rhs)
  show "((\<lambda>c. Re (Afun x c)) has_derivative
          (\<lambda>h. Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))) (at c)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Afun_c])
  show "(\<lambda>h. Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))
        = (\<lambda>h. \<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l))"
    by (rule ext) (rule ReDAfun)
qed

lemma dIm_Afun:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "((\<lambda>c. Im (Afun x c)) has_derivative (\<lambda>h. - (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l)))) (at c)"
proof (rule has_derivative_eq_rhs)
  show "((\<lambda>c. Im (Afun x c)) has_derivative
          (\<lambda>h. Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))) (at c)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Afun_c])
  show "(\<lambda>h. Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))
        = (\<lambda>h. - (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l)))"
    by (rule ext) (rule ImDAfun)
qed

lemma dRe_Mcfun:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "((\<lambda>c. Re (Mcfun x c k)) has_derivative
            (\<lambda>h. \<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c k l))) (at c)"
proof (rule has_derivative_eq_rhs)
  show "((\<lambda>c. Re (Mcfun x c k)) has_derivative
          (\<lambda>h. Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                     * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))) (at c)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Mcfun_c])
  show "(\<lambda>h. Re (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                     * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))
        = (\<lambda>h. \<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c k l))"
    by (rule ext) (rule ReDMfun)
qed

lemma dIm_Mcfun:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "((\<lambda>c. Im (Mcfun x c k)) has_derivative
            (\<lambda>h. - (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c k l)))) (at c)"
proof (rule has_derivative_eq_rhs)
  show "((\<lambda>c. Im (Mcfun x c k)) has_derivative
          (\<lambda>h. Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                     * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))) (at c)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Mcfun_c])
  show "(\<lambda>h. Im (\<Sum>n\<in>UNIV. (- \<i>) * complex_of_real ((x$n)$k)
                     * complex_of_real (h \<bullet> (x$n)) * cis (-(c \<bullet> (x$n)))))
        = (\<lambda>h. - (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c k l)))"
    by (rule ext) (rule ImDMfun)
qed


lemma Re_cnj_mult: "Re (cnj a * b) = Re a * Re b + Im a * Im b"
  by simp

text \<open>\<^bold>\<open>The \<open>c\<close>-Hessian of \<open>\<bar>A\<bar>\<^sup>2\<close> is the moment matrix \<open>Hcmat\<close>.\<close>  Differentiating the
  \<open>c\<close>-gradient field (@{thm gradU_c_field}) once more --- product rule on
  \<open>2(Re A Im M\<^sub>j - Im A Re M\<^sub>j)\<close> using the four piece-derivatives --- yields, componentwise,
  exactly the \<open>j\<close>-th entry of \<open>Hcmat \<cdot> h\<close>.\<close>

lemma has_derivative_gradU_c:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "(gradU (\<lambda>c. c) (\<lambda>_. 1) x has_derivative (\<lambda>h. Hcmat x c *v h)) (at c)"
proof -
  have field_eq: "gradU (\<lambda>c. c) (\<lambda>_. 1) x
        = (\<lambda>c. \<chi> j. 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j)))"
  proof (rule ext)
    fix c :: "real^2"
    have "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ i
          = (\<chi> j. 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j))) $ i"
      for i by (simp add: gradU_c_field)
    thus "gradU (\<lambda>c. c) (\<lambda>_. 1) x c
          = (\<chi> j. 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j)))"
      by (simp add: Finite_Cartesian_Product.vec_eq_iff)
  qed
  have comp: "((\<lambda>c. 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j)))
                has_derivative (\<lambda>h. (Hcmat x c *v h) $ j)) (at c)" for j
  proof (rule has_derivative_eq_rhs)
    show "((\<lambda>c. 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j)))
            has_derivative
            (\<lambda>h. 2 * ((Re (Afun x c) * (- (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c j l)))
                       + (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l)) * Im (Mcfun x c j))
                    - (Im (Afun x c) * (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c j l))
                       + (- (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))) * Re (Mcfun x c j)))
                 + 0 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j)))) (at c)"
      by (rule has_derivative_mult[OF has_derivative_const
                has_derivative_diff[OF has_derivative_mult[OF dRe_Afun dIm_Mcfun]
                                       has_derivative_mult[OF dIm_Afun dRe_Mcfun]]])
    show "(\<lambda>h. 2 * ((Re (Afun x c) * (- (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c j l)))
                       + (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l)) * Im (Mcfun x c j))
                    - (Im (Afun x c) * (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c j l))
                       + (- (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))) * Re (Mcfun x c j)))
                 + 0 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j)))
          = (\<lambda>h. (Hcmat x c *v h) $ j)"
    proof (rule ext)
      fix h :: "real^2"
      have "(Hcmat x c *v h) $ j
          = (\<Sum>l\<in>UNIV. (h$l) * (2 * (Re (Mcfun x c l) * Re (Mcfun x c j) + Im (Mcfun x c l) * Im (Mcfun x c j)
                  - (Re (Afun x c) * Re (M2cfun x c j l) + Im (Afun x c) * Im (M2cfun x c j l)))))"
        by (simp add: matrix_vector_mult_def Hcmat_def Re_cnj_mult mult.commute)
      thus "2 * ((Re (Afun x c) * (- (\<Sum>l\<in>UNIV. (h$l) * Re (M2cfun x c j l)))
                   + (\<Sum>l\<in>UNIV. (h$l) * Im (Mcfun x c l)) * Im (Mcfun x c j))
                - (Im (Afun x c) * (\<Sum>l\<in>UNIV. (h$l) * Im (M2cfun x c j l))
                   + (- (\<Sum>l\<in>UNIV. (h$l) * Re (Mcfun x c l))) * Re (Mcfun x c j)))
             + 0 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j))
           = (Hcmat x c *v h) $ j"
        by (simp add: sum_distrib_left sum_distrib_right sum_subtractf sum_negf algebra_simps)
    qed
  qed
  have "(gradU (\<lambda>c. c) (\<lambda>_. 1) x has_derivative (\<lambda>h. Hcmat x c *v h)) (at c)"
    unfolding field_eq
  proof (subst has_derivative_componentwise_within, intro ballI)
    fix b :: "real^2" assume "b \<in> Basis"
    then obtain j where bj: "b = axis j 1" by (auto simp: Basis_vec_def)
    have "((\<lambda>c. (\<chi> j. 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j))) \<bullet> b)
            has_derivative (\<lambda>h. (Hcmat x c *v h) \<bullet> b)) (at c within UNIV)"
      using comp[of j] by (simp add: bj inner_axis)
    thus "((\<lambda>c. (\<chi> j. 2 * (Re (Afun x c) * Im (Mcfun x c j) - Im (Afun x c) * Re (Mcfun x c j))) \<bullet> b)
            has_derivative (\<lambda>h. ((\<lambda>h. Hcmat x c *v h) h) \<bullet> b)) (at c within UNIV)"
      by simp
  qed
  thus ?thesis .
qed

text \<open>Hence the \<open>c\<close>-coordinate Hessian of \<open>U\<close> (gain \<open>\<equiv> 1\<close>) IS the moment matrix.\<close>

lemma HessU_c_eq:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "HessU (\<lambda>c. c) (\<lambda>_. 1) x c = Hcmat x c"
proof -
  have "HessU (\<lambda>c. c) (\<lambda>_. 1) x c = matrix (\<lambda>h. Hcmat x c *v h)"
    by (rule HessU_explicit[OF has_derivative_gradU_c])
  thus ?thesis by (simp add: matrix_of_matrix_vector_mul)
qed

text \<open>\<^bold>\<open>The explicit moment entries of the \<open>c\<close>-Hessian\<close> --- so its determinant is manifestly
  a polynomial in the moments \<open>A, M\<^sub>1, M\<^sub>2, M\<^sub>1\<^sub>1, M\<^sub>1\<^sub>2, M\<^sub>2\<^sub>2\<close>.\<close>

lemma Hcmat_11:
  "Hcmat x c $ 1 $ 1
     = 2 * (Re (cnj (Mcfun x c 1) * Mcfun x c 1) - Re (cnj (Afun x c) * M2cfun x c 1 1))"
  by (simp add: Hcmat_def)
lemma Hcmat_22:
  "Hcmat x c $ 2 $ 2
     = 2 * (Re (cnj (Mcfun x c 2) * Mcfun x c 2) - Re (cnj (Afun x c) * M2cfun x c 2 2))"
  by (simp add: Hcmat_def)
lemma Hcmat_12:
  "Hcmat x c $ 1 $ 2
     = 2 * (Re (cnj (Mcfun x c 2) * Mcfun x c 1) - Re (cnj (Afun x c) * M2cfun x c 1 2))"
  by (simp add: Hcmat_def)

text \<open>\<^bold>\<open>The Hessian-determinant component \<open>\<Phi>\<^sub>3\<close> in \<open>c\<close>-coordinates IS a moment polynomial.\<close>
  \<open>det \<nabla>\<^sup>2\<^sub>c U = H\<^sub>1\<^sub>1H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2 = det(Hcmat)\<close>, a polynomial in the six \<open>M_paper\<close> moments
  --- the third component \<open>F\<^sub>3\<close> of the bad-point map factored through \<open>\<M>\<close> (\<open>\<Phi> = F \<circ> \<M>\<close>).\<close>

lemma detHessU_c:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "HessU (\<lambda>c. c) (\<lambda>_. 1) x c $ 1 $ 1 * HessU (\<lambda>c. c) (\<lambda>_. 1) x c $ 2 $ 2
           - (HessU (\<lambda>c. c) (\<lambda>_. 1) x c $ 1 $ 2)\<^sup>2
       = Hcmat x c $ 1 $ 1 * Hcmat x c $ 2 $ 2 - (Hcmat x c $ 1 $ 2)\<^sup>2"
  by (simp add: HessU_c_eq)

text \<open>The fully-factored moment form \<open>4(AB - C\<^sup>2)\<close> (ring identity over the \<open>Re(cnj\<cdot>)\<close> atoms).\<close>

lemma detHessU_c_moments:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "HessU (\<lambda>c. c) (\<lambda>_. 1) x c $ 1 $ 1 * HessU (\<lambda>c. c) (\<lambda>_. 1) x c $ 2 $ 2
           - (HessU (\<lambda>c. c) (\<lambda>_. 1) x c $ 1 $ 2)\<^sup>2
       = 4 * ((Re (cnj (Mcfun x c 1) * Mcfun x c 1) - Re (cnj (Afun x c) * M2cfun x c 1 1))
              * (Re (cnj (Mcfun x c 2) * Mcfun x c 2) - Re (cnj (Afun x c) * M2cfun x c 2 2))
              - (Re (cnj (Mcfun x c 2) * Mcfun x c 1) - Re (cnj (Afun x c) * M2cfun x c 1 2))\<^sup>2)"
proof -
  have ring: "(2*A) * (2*B) - (2*C)\<^sup>2 = 4 * (A*B - C\<^sup>2)" for A B C :: real
    by (simp add: power2_eq_square algebra_simps)
  show ?thesis
    by (simp only: detHessU_c Hcmat_11 Hcmat_22 Hcmat_12 ring)
qed


subsection \<open>The \<open>\<omega>\<close>--\<open>c\<close> bridge: the actual pattern factors as \<open>gain\<cdot>(V\<circ>cvec)\<close>\<close>

text \<open>\<^bold>\<open>The multiplicative factorization.\<close>  The actual radiation intensity is the \<open>c\<close>-pattern
  \<open>V = \<bar>A\<bar>\<^sup>2\<close> (the gain\<open>\<equiv>1\<close> intensity) evaluated at the wavevector \<open>c = cvec \<omega>\<close>, scaled by the
  angular gain \<open>gain \<omega>\<close>: \<open>U(\<bm>x,\<omega>) = gain(\<omega>)\<cdot>V(\<bm>x, cvec \<omega>)\<close>.  This is the bridge along which
  the \<open>\<omega>\<close>-derivatives of \<open>U\<close> reduce (chain + product rule) to the moment-space \<open>c\<close>-derivatives
  \<open>gradU_c\<close>/\<open>Hcmat\<close> already computed.\<close>

lemma U_cart_factor:
  "U_cart cvec gain x \<omega> = gain \<omega> * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)"
  by (simp add: U_cart_def A_cart_eq_Afun)

text \<open>\<^bold>\<open>The \<open>c\<close>-pattern \<open>V\<close> has \<open>gradU_c\<close> as its genuine gradient.\<close>  \<open>V = U_cart (\<lambda>c. c) (\<lambda>_. 1) x\<close>
  is differentiable (the array factor is smooth), so the \<open>THE\<close>-gradient \<open>gradU (\<lambda>c. c) (\<lambda>_. 1) x\<close>
  is its actual Fréchet derivative --- the first-order input for the chain rule of the bridge.\<close>

lemma has_derivative_Uc_c:
  fixes x :: "(real^2)^'n" and c :: "real^2"
  shows "(U_cart (\<lambda>c. c) (\<lambda>_. 1) x has_derivative (\<lambda>v. v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x c)) (at c)"
proof -
  have hd: "(U_cart (\<lambda>c. c) (\<lambda>_. 1) x
              has_derivative dU_cart (\<lambda>c. c) (\<lambda>h. h) (\<lambda>_. 1) (\<lambda>_. 0) x c) (at c)"
    by (rule has_derivative_U_cart[OF has_derivative_ident has_derivative_const])
  have "GRAD (U_cart (\<lambda>c. c) (\<lambda>_. 1) x) c :> \<nabla> (U_cart (\<lambda>c. c) (\<lambda>_. 1) x) c"
    by (rule grad_fun_satisfies_GRAD[OF has_derivative_to_gradient[OF hd]])
  thus ?thesis by (simp add: has_gradient_def gradU_def)
qed

text \<open>\<^bold>\<open>First-order bridge.\<close>  The actual pattern's \<open>\<omega>\<close>-derivative is the chain+product rule
  through \<open>cvec\<close> and \<open>gain\<close>: \<open>D\<^sub>\<omega>U(v) = gain(\<omega>)\,(D\<^sub>\<omega>cvec\,v)\<cdot>\<nabla>\<^sub>cV(cvec \<omega>) + dgain(v)\,V(cvec \<omega>)\<close>,
  with \<open>\<nabla>\<^sub>cV = gradU (\<lambda>c. c) (\<lambda>_. 1) x\<close> the moment-space \<open>c\<close>-gradient.\<close>

lemma has_derivative_U_via_c:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
    and Dg: "(gain has_derivative dgain) (at \<omega>)"
  shows "(U_cart cvec gain x has_derivative
            (\<lambda>v. gain \<omega> * (Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                 + dgain v * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))) (at \<omega>)"
proof -
  have chain: "((\<lambda>\<omega>. U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                  has_derivative (\<lambda>v. Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))) (at \<omega>)"
    using diff_chain_at[OF Dc has_derivative_Uc_c] by (simp add: o_def)
  have "((\<lambda>\<omega>. gain \<omega> * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
          has_derivative (\<lambda>v. gain \<omega> * (Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                              + dgain v * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))) (at \<omega>)"
    by (rule has_derivative_mult[OF Dg chain])
  moreover have "U_cart cvec gain x = (\<lambda>\<omega>. gain \<omega> * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))"
    by (rule ext) (rule U_cart_factor)
  ultimately show ?thesis by simp
qed

text \<open>\<^bold>\<open>Second-order bridge ingredients.\<close>  As \<open>\<omega>\<close> varies, the moment-space \<open>c\<close>-gradient and
  \<open>c\<close>-pattern --- evaluated at \<open>cvec \<omega>\<close> --- vary by the chain rule through \<open>cvec\<close>:
  \<open>D\<^sub>\<omega>[\<nabla>\<^sub>cV(cvec \<omega>)] = Hcmat(cvec \<omega>)\<cdot>(D\<^sub>\<omega>cvec)\<close> and \<open>D\<^sub>\<omega>[V(cvec \<omega>)] = (D\<^sub>\<omega>cvec)\<cdot>\<nabla>\<^sub>cV(cvec \<omega>)\<close>.\<close>

lemma has_derivative_gradU_c_along_cvec:
  fixes cvec :: "angle \<Rightarrow> planar" and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
  shows "((\<lambda>\<omega>. gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
            has_derivative (\<lambda>v. Hcmat x (cvec \<omega>) *v (Dcvec v))) (at \<omega>)"
  using diff_chain_at[OF Dc has_derivative_gradU_c] by (simp add: o_def)

lemma has_derivative_V_along_cvec:
  fixes cvec :: "angle \<Rightarrow> planar" and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
  shows "((\<lambda>\<omega>. U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
            has_derivative (\<lambda>v. Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))) (at \<omega>)"
  using diff_chain_at[OF Dc has_derivative_Uc_c] by (simp add: o_def)

text \<open>\<^bold>\<open>The actual \<open>\<omega>\<close>-gradient field in explicit bridge form.\<close>  Assembling the first-order
  bridge derivative into the gradient vector: \<open>\<nabla>\<^sub>\<omega>U = \<Sum>\<^sub>i [gain(\<omega>)(D\<^sub>\<omega>cvec\,e\<^sub>i)\<cdot>\<nabla>\<^sub>cV + dgain(e\<^sub>i)V] e\<^sub>i\<close>.
  Differentiating this field once more gives \<open>HessU\<close> in moment-space terms.\<close>

lemma gradU_via_c:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
    and Dg: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega>
         = (\<Sum>i\<in>UNIV. (gain \<omega> * (Dcvec (axis i 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                       + dgain (axis i 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)) *\<^sub>R axis i 1)"
proof -
  have "\<nabla> (U_cart cvec gain x) \<omega>
      = (\<Sum>i\<in>UNIV. (\<lambda>v. gain \<omega> * (Dcvec v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                          + dgain v * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)) (axis i 1) *\<^sub>R axis i 1)"
    by (rule grad_fun_eq[OF has_derivative_to_gradient[OF has_derivative_U_via_c[OF Dc Dg]]])
  thus ?thesis by (simp add: gradU_def)
qed

text \<open>\<^bold>\<open>The \<open>k\<close>-th component of the bridge gradient\<close> --- a scalar, easier to differentiate
  for the Hessian than the full vector.\<close>

lemma gradU_via_c_component:
  fixes cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
    and x :: "(real^2)^'n" and \<omega> :: angle
  assumes Dc: "(cvec has_derivative Dcvec) (at \<omega>)"
    and Dg: "(gain has_derivative dgain) (at \<omega>)"
  shows "gradU cvec gain x \<omega> $ k
         = gain \<omega> * (Dcvec (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
           + dgain (axis k 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)"
proof -
  have "gradU cvec gain x \<omega> $ k
      = (\<Sum>i\<in>UNIV. (gain \<omega> * (Dcvec (axis i 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                     + dgain (axis i 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                   * (axis (i::2) 1 $ k))"
    by (simp add: gradU_via_c[OF Dc Dg] sum_component)
  also have "\<dots> = gain \<omega> * (Dcvec (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>))
                   + dgain (axis k 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec \<omega>)"
    by (simp add: axis_def if_distrib sum.delta cong: if_cong)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The gain is \<open>C\<^sup>2\<close> in the \<open>\<omega>\<close> (vec) setting.\<close>  Lift @{thm gdip_deriv_differentiable}
  through the \<open>\<theta> = \<omega>\<^sub>1\<close> projection: \<open>\<lambda>\<omega>. \<partial>gdip(\<omega>\<^sub>1)\<close> is differentiable.\<close>

lemma gain_dip_deriv_field_differentiable:
  fixes \<omega> :: "real^2"
  shows "(\<lambda>\<omega>::real^2. frechet_derivative gdip (at (\<omega>$1)) s) differentiable (at \<omega>)"
proof -
  have proj: "(\<lambda>\<omega>::real^2. \<omega>$1) differentiable (at \<omega>)"
    using has_derivative_proj by (blast intro: differentiableI)
  have inner: "(\<lambda>t::real. frechet_derivative gdip (at t) s) differentiable (at (\<omega>$1))"
    by (rule gdip_deriv_differentiable)
  show ?thesis
    using differentiable_chain_at[OF proj inner] by (simp add: o_def)
qed

text \<open>\<^bold>\<open>The dipole's scalar gradient component as a field of \<open>\<omega>\<close>\<close> --- instantiating the bridge
  at the proven dipole jet (@{thm has_derivative_cvec_dip}, @{thm gain_dip_has_derivative}).
  Differentiating this scalar field once more gives the \<open>k\<close>-th row of \<open>HessU_dip\<close> in
  moment-space terms.\<close>

lemma gradU_dip_component_field:
  fixes x :: "(real^2)^'n"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k
         = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
           + frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
             * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)"
  by (rule gradU_via_c_component[OF has_derivative_cvec_dip gain_dip_has_derivative])

text \<open>\<^bold>\<open>The second-order assembly\<close> --- differentiate the scalar gradient component once more
  (product rule on \<open>gain\<cdot>IP\<close> and \<open>GD\<cdot>V\<close>, inner-product rule on \<open>IP = Dcvec(e\<^sub>k)\<cdot>\<nabla>\<^sub>cV\<close>) using
  the dipole jet derivatives \<open>D\<^sup>2cvec\<close>, \<open>gdip''\<close>, \<open>Hcmat\<close>.  The resulting derivative is the
  \<open>k\<close>-th row of \<open>HessU_dip\<close>, a moment-space expression with the (x-constant) jet as coefficients.\<close>

lemma has_derivative_gradU_dip_component:
  fixes x :: "(real^2)^'n"
  shows "((\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) has_derivative
    (\<lambda>h. (gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> h))
                        + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) h)
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative gdip (at (\<omega>$1)) (h$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))
        + (frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> h \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) h
            * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))) (at \<omega>)"
proof -
  have dGain: "(gain_dip has_derivative (\<lambda>v. frechet_derivative gdip (at (\<omega>$1)) (v$1))) (at \<omega>)"
    by (rule gain_dip_has_derivative)
  have dDc: "((\<lambda>\<omega>. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) has_derivative D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) (at \<omega>)"
    by (rule has_derivative_Dcvec_dip)
  have dgcV: "((\<lambda>\<omega>. gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
                has_derivative (\<lambda>v. Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> v))) (at \<omega>)"
    by (rule has_derivative_gradU_c_along_cvec[OF has_derivative_cvec_dip])
  have dGD: "((\<lambda>\<omega>. frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)) has_derivative
              frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>)) (at \<omega>)"
    by (rule frechet_derivative_works[THEN iffD1, OF gain_dip_deriv_field_differentiable])
  have dV: "((\<lambda>\<omega>. U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
              has_derivative (\<lambda>v. Dcvec_dip \<omega>0 \<omega>s \<omega> v \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at \<omega>)"
    by (rule has_derivative_V_along_cvec[OF has_derivative_cvec_dip])
  have dIP: "((\<lambda>\<omega>. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
              has_derivative
              (\<lambda>h. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> h))
                   + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) h) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at \<omega>)"
    by (rule has_derivative_inner[OF dDc dgcV])
  have field: "(\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k)
             = (\<lambda>\<omega>. gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
                    + frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
                      * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    by (rule ext) (rule gradU_dip_component_field)
  show ?thesis
    unfolding field
    by (rule has_derivative_add[OF has_derivative_mult[OF dGain dIP] has_derivative_mult[OF dGD dV]])
qed

text \<open>\<^bold>\<open>\<open>HessU_dip\<close> entry = the scalar component field's derivative.\<close>  Since \<open>$k\<close> is
  bounded-linear, the \<open>(k,l)\<close> Hessian entry is the derivative of the \<open>k\<close>-th gradient
  component in direction \<open>e\<^sub>l\<close> --- which @{thm has_derivative_gradU_dip_component} computes
  explicitly in moment-space terms.\<close>

lemma HessU_dip_eq_componentderiv:
  fixes x :: "(real^2)^'n"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
         = frechet_derivative (\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) (at \<omega>) (axis l 1)"
proof -
  have "((\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k)
          has_derivative (\<lambda>v. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v) $ k)) (at \<omega>)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth gradU_dip_has_derivative])
  hence "frechet_derivative (\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) (at \<omega>) (axis l 1)
         = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v axis l 1) $ k"
    by (simp add: frechet_derivative_at')
  also have "\<dots> = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l"
    by (simp add: matrix_vector_mult_def axis_def if_distrib sum.delta cong: if_cong)
  finally show ?thesis by (rule sym)
qed

text \<open>\<^bold>\<open>The Hessian entry in moment-space form\<close> --- combine the two: \<open>HessU_dip\<close>'s \<open>(k,l)\<close>
  entry is the explicit moment expression (jet coefficients \<open>Dcvec_dip\<close>, \<open>D\<^sup>2cvec_dip\<close>,
  \<open>\<partial>gdip\<close>, \<open>\<partial>\<^sup>2gdip\<close>, \<open>Hcmat\<close>, all \<open>x\<close>-constant; the \<open>x\<close>-dependence is entirely through the
  moments \<open>\<nabla>\<^sub>cV\<close>, \<open>Hcmat\<close>, \<open>V\<close> = \<open>M_paper\<close>).  So \<open>det HessU_dip\<close> factors through \<open>M_paper\<close>.\<close>

lemma HessU_dip_entry_moments:
  fixes x :: "(real^2)^'n"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = (gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
                        + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1))
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative gdip (at (\<omega>$1)) ((axis l 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))
        + (frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
            * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))"
proof -
  \<comment> \<open>Step 1: the \<open>(k,l)\<close> Hessian entry is the directional derivative, along \<open>e\<^sub>l = axis l 1\<close>,
        of the \<open>k\<close>-th component of the gradient field.\<close>
  have step1: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
      = frechet_derivative (\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) (at \<omega>) (axis l 1)"
    by (rule HessU_dip_eq_componentderiv)
  \<comment> \<open>Step 2: the total (Frechet) derivative of that scalar component field is the explicit
        moment-space linear map established in @{thm has_derivative_gradU_dip_component} --- a sum of
        the curvature term \<open>\<nabla>\<^sub>c\<^sup>2V\<close> (via \<open>Hcmat\<close>), the second-order chart jet \<open>D\<^sup>2cvec_dip\<close>, and the
        gain's first/second \<open>\<omega>\<close>-derivatives times \<open>\<nabla>\<^sub>cV\<close> and \<open>V\<close>.\<close>
  have step2: "frechet_derivative (\<lambda>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k) (at \<omega>)
      = (\<lambda>h. (gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> h))
                        + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) h)
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative gdip (at (\<omega>$1)) (h$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))
        + (frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> h \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) h
            * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))"
    by (rule frechet_derivative_at'[OF has_derivative_gradU_dip_component])
  \<comment> \<open>Step 3: evaluate that linear map at \<open>e\<^sub>l = axis l 1\<close> (\<open>\<beta>\<close>-reduction substitutes \<open>h := axis l 1\<close>),
        which is exactly the claimed moment expression.\<close>
  show ?thesis
    unfolding step1 step2 by (rule refl)
qed

text \<open>\<^bold>\<open>The dipole gradient components \<open>\<Phi>\<^sub>1, \<Phi>\<^sub>2\<close> in moment-space form.\<close>  Specialising
  @{thm gradU_component_via_M_paper} to the \<^emph>\<open>actual\<close> dipole steering/gain
  (\<open>cvec_dip\<close>/\<open>gain_dip\<close>, with their proven derivatives \<open>Dcvec_dip\<close>/\<open>\<partial>gdip\<close>):
  the \<open>j\<close>-th angular partial of \<open>U_dip\<close> depends on \<open>(\<bm>x,\<omega>)\<close> only through the first
  three moment coordinates \<open>A, M\<^sub>1, M\<^sub>2\<close> of \<open>M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)\<close>, with the
  steering/gain jets \<open>Dcvec_dip\<close>, \<open>gain_dip\<close>, \<open>\<partial>gdip\<close> as \<open>\<bm>x\<close>-independent coefficients.
  Together with @{thm HessU_dip_entry_moments} this puts \<^emph>\<open>all three\<close> components of
  \<open>Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip\<close> into moment-space form --- the \<open>\<Phi> = F \<circ> \<M>\<close> factorisation
  for the genuine dipole.\<close>

lemma gradU_dip_component_moments:
  fixes x :: "(real^2)^'n"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
         = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
             * (cmod (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2
           + gain_dip \<omega> * (2 * Re (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
                * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1)
                     * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
                 + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                     * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))))"
  by (rule gradU_component_via_M_paper[OF has_derivative_cvec_dip gain_dip_has_derivative])

text \<open>\<^bold>\<open>The \<open>c\<close>-pattern value and its gradient in moment coordinates.\<close>  Inside the dipole
  Hessian entries (@{thm HessU_dip_entry_moments}) the \<open>\<bm>x\<close>-dependence enters through
  \<open>V = U_cart (\<lambda>c. c) (\<lambda>_. 1) x\<close> and its gradient \<open>\<nabla>\<^sub>cV = gradU (\<lambda>c. c) (\<lambda>_. 1) x\<close>.  Both are
  themselves functions of the moments: \<open>V(c) = |A|\<^sup>2\<close> and \<open>(\<nabla>\<^sub>cV)\<^sub>j = 2 Re(cnj A (-\<ii>) M\<^sub>j)\<close>,
  with \<open>A = \<M>\<^sub>1\<close>, \<open>M\<^sub>1 = \<M>\<^sub>2\<close>, \<open>M\<^sub>2 = \<M>\<^sub>3\<close> the first three coordinates of \<open>M_paper x c\<close>.  These
  collapse the c-side of the Hessian entries onto \<open>M_paper\<close> as well --- completing the
  \<open>\<Phi> = F \<circ> \<M>\<close> factorisation (every \<open>\<bm>x\<close>-dependence routes through \<open>M_paper\<close>).\<close>

lemma Uc_eq_moment:
  fixes x :: "(real^2)^'n"
  shows "U_cart (\<lambda>c. c) (\<lambda>_. 1) x c = (cmod (M_paper x c $ 1))\<^sup>2"
proof -
  have "M_paper x c $ 1 = Afun x c"
    using M_paper_proj_A[of x "\<lambda>c. c" c] by (simp add: A_cart_eq_Afun)
  thus ?thesis by (simp add: U_cart_def A_cart_eq_Afun)
qed

lemma gradUc_component_moments:
  fixes x :: "(real^2)^'n"
  shows "gradU (\<lambda>c. c) (\<lambda>_. 1) x c $ j
       = 2 * Re (cnj (M_paper x c $ 1)
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * (M_paper x c $ 2)
             + (- \<i>) * complex_of_real ((axis j 1)$2) * (M_paper x c $ 3)))"
proof -
  have d1: "((\<lambda>c::real^2. c) has_derivative (\<lambda>v. v)) (at c)" by (rule has_derivative_ident)
  have d2: "((\<lambda>_::real^2. 1::real) has_derivative (\<lambda>_. 0)) (at c)" by (rule has_derivative_const)
  show ?thesis
    using gradU_component_via_M_paper[OF d1 d2] by simp
qed

text \<open>\<^bold>\<open>A5 brick 2c-i: the c-pattern joint terms are jointly continuous in \<open>(\<bm>x,\<omega>)\<close>.\<close>  The
  \<open>\<bm>x\<close>-dependence of every \<open>HessU_dip_entry_moments\<close> term routes through the moment functions
  \<open>Afun\<close>, \<open>Mcfun\<close>, \<open>M2cfun\<close> (\<open>= \<Sum>\<^sub>n w(\<bm>x\<^sub>n) e\<^bsup>-\<ii>c\<bullet>\<bm>x\<^sub>n\<^esup>\<close>, the brick-1 shape).  Their joint
  continuity (in \<open>(\<bm>x,c)\<close>) composed with \<open>cvec_dip\<close> (brick 2a) gives joint continuity of the
  curvature matrix \<open>Hcmat\<close>, the c-gradient \<open>\<nabla>\<^sub>cV\<close>, and the value \<open>V\<close>.\<close>

lemma continuous_on_Afun_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set) (\<lambda>p. Afun (fst p) (snd p))"
  unfolding Afun_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_Mcfun_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set) (\<lambda>p. Mcfun (fst p) (snd p) k)"
  unfolding Mcfun_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_M2cfun_joint:
  "continuous_on (UNIV :: ((planar^'n) \<times> planar) set) (\<lambda>p. M2cfun (fst p) (snd p) k l)"
  unfolding M2cfun_def
  by (intro continuous_on_sum continuous_on_cis continuous_intros
            bounded_linear.continuous_on[OF bounded_linear_vec_nth])

lemma continuous_on_Afun_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. Afun (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  using continuous_on_compose2[OF continuous_on_Afun_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_Mcfun_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. Mcfun (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) k)"
  using continuous_on_compose2[OF continuous_on_Mcfun_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_M2cfun_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. M2cfun (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) k l)"
  using continuous_on_compose2[OF continuous_on_M2cfun_joint
                                 continuous_on_pair_cvec_dip subset_UNIV] by simp

lemma continuous_on_Hcmat_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. Hcmat (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
  unfolding Hcmat_def
  by (intro continuous_on_vec_lambda continuous_intros
            continuous_on_Afun_cvec_dip continuous_on_Mcfun_cvec_dip
            continuous_on_M2cfun_cvec_dip)

lemma continuous_on_gradUc_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. gradU (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
proof -
  have "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
          (\<lambda>p. \<chi> j. gradU (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) $ j)"
  proof (intro continuous_on_vec_lambda)
    fix j :: 2
    show "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
            (\<lambda>p. gradU (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)) $ j)"
      by (simp only: gradUc_component_moments M_paper_components,
          intro continuous_intros continuous_on_A_moment_cvec_dip
                continuous_on_M1_moment_cvec_dip continuous_on_M2_moment_cvec_dip)
  qed
  thus ?thesis by (simp add: vec_lambda_eta)
qed

lemma continuous_on_Uc_cvec_dip:
  "continuous_on (UNIV :: ((planar^'n) \<times> (real^2)) set)
     (\<lambda>p. U_cart (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))"
proof -
  have *: "(\<lambda>p::(planar^'n) \<times> (real^2). U_cart (\<lambda>c. c) (\<lambda>_. 1) (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
         = (\<lambda>p. (cmod (A_moment (fst p) (cvec_dip \<omega>0 \<omega>s (snd p))))\<^sup>2)"
    by (rule ext) (simp add: Uc_eq_moment M_paper_components)
  show ?thesis
    unfolding *
    by (intro continuous_intros continuous_on_A_moment_cvec_dip)
qed

text \<open>\<^bold>\<open>Sard brick (1): the dipole gradient field is \<open>C\<^sup>1\<close> in the configuration \<open>\<bm>x\<close>.\<close>  Fix the
  steering angle \<open>\<omega>\<close>.  Via @{thm gradU_dip_component_moments} the \<open>j\<close>-th gradient component is a
  fixed polynomial in the (\<open>\<bm>x\<close>-smooth) moment coordinates \<open>M_paper \<bm>x c\<close> (with \<open>c = cvec_dip \<omega>\<close>):
  \<open>(\<nabla>U)\<^sub>j = \<partial>gdip (|\<M>\<^sub>1|\<^sup>2) + gain 2 Re(cnj \<M>\<^sub>1 (a\<M>\<^sub>2 + b\<M>\<^sub>3))\<close>.  Since each moment
  coordinate is differentiable in \<open>\<bm>x\<close> (@{thm has_derivative_M_paper_x}) and \<open>cmod\<^sup>2 = Re\<^sup>2 + Im\<^sup>2\<close>,
  the component is differentiable in \<open>\<bm>x\<close> --- the smoothness input \<open>derG\<close>/\<open>contG'\<close> that the
  zero-set chart engine (and the rank step) require, with \<^emph>\<open>no\<close> assumption on \<open>cvec\<close>/\<open>gain\<close>
  smoothness in \<open>\<omega>\<close> (the \<open>\<omega>\<close>-jets enter only as constants here).\<close>

lemma gradU_dip_component_differentiable_x:
  fixes x :: "(real^2)^'n" and V :: "((real^2)^'n) set"
  shows "(\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j) differentiable (at x within V)"
proof -
  have d: "(\<lambda>y. M_paper y (cvec_dip \<omega>0 \<omega>s \<omega>) $ k) differentiable (at x within V)" for k :: 6
    by (rule differentiableI[OF
          bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_M_paper_x]])
  have eq: "(\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j)
          = (\<lambda>y. frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
                   * ((Re (M_paper y (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2
                    + (Im (M_paper y (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2)
                 + gain_dip \<omega> * (2 * Re (cnj (M_paper y (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
                      * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1)
                           * (M_paper y (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
                       + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                           * (M_paper y (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3)))))"
    by (rule ext) (simp add: gradU_dip_component_moments cmod_power2)
  show ?thesis
    unfolding eq
    by (intro differentiable_add differentiable_mult differentiable_const differentiable_power
              differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_Re]]
              differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_Im]]
              differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_cnj]]
              d)
qed

text \<open>\<^bold>\<open>Companion smoothness bricks for the \<open>c\<close>-pattern.\<close>  The same argument shows the gain\<open>\<equiv>1\<close>
  pattern value \<open>V = U_cart (\<lambda>c. c) (\<lambda>_. 1) \<bm>x c\<close> and its \<open>c\<close>-gradient component are differentiable
  in the configuration \<open>\<bm>x\<close> (at a \<^emph>\<open>fixed\<close> wavevector \<open>c\<close>) --- the building blocks for the
  \<open>\<bm>x\<close>-smoothness of the Hessian entries.\<close>

lemma Uc_differentiable_x:
  fixes x :: "(real^2)^'n" and V :: "((real^2)^'n) set" and c :: "real^2"
  shows "(\<lambda>y. U_cart (\<lambda>c. c) (\<lambda>_. 1) y c) differentiable (at x within V)"
proof -
  have d: "(\<lambda>y. M_paper y c $ k) differentiable (at x within V)" for k :: 6
    by (rule differentiableI[OF
          bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_M_paper_x]])
  have eq: "(\<lambda>y. U_cart (\<lambda>c. c) (\<lambda>_. 1) y c)
          = (\<lambda>y. (Re (M_paper y c $ 1))\<^sup>2 + (Im (M_paper y c $ 1))\<^sup>2)"
    by (rule ext) (simp add: Uc_eq_moment cmod_power2)
  show ?thesis
    unfolding eq
    by (intro differentiable_add differentiable_power
              differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_Re]]
              differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_Im]]
              d)
qed

lemma gradUc_component_differentiable_x:
  fixes x :: "(real^2)^'n" and V :: "((real^2)^'n) set" and c :: "real^2"
  shows "(\<lambda>y. gradU (\<lambda>c. c) (\<lambda>_. 1) y c $ j) differentiable (at x within V)"
proof -
  have d: "(\<lambda>y. M_paper y c $ k) differentiable (at x within V)" for k :: 6
    by (rule differentiableI[OF
          bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_M_paper_x]])
  have eq: "(\<lambda>y. gradU (\<lambda>c. c) (\<lambda>_. 1) y c $ j)
          = (\<lambda>y. 2 * Re (cnj (M_paper y c $ 1)
               * ((- \<i>) * complex_of_real ((axis j 1)$1) * (M_paper y c $ 2)
                + (- \<i>) * complex_of_real ((axis j 1)$2) * (M_paper y c $ 3))))"
    by (rule ext) (simp add: gradUc_component_moments)
  show ?thesis
    unfolding eq
    by (intro differentiable_mult differentiable_const differentiable_add
              differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_Re]]
              differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_cnj]]
              d)
qed

text \<open>\<^bold>\<open>Assembling the components into the vector field.\<close>  A map into the euclidean space
  \<open>real^2\<close> is differentiable iff each coordinate \<open>\<bullet> b\<close> (\<open>b\<close> a basis vector \<open>axis j 1\<close>, so
  \<open>\<bullet> b = $ j\<close>) is.  The two scalar bricks @{thm gradU_dip_component_differentiable_x} therefore
  give the full \<open>2\<close>-vector gradient field \<open>\<nabla>\<^sub>\<Omega>U_dip\<close> its differentiability in the configuration
  \<open>\<bm>x\<close> --- the \<open>C\<^sup>1\<close> regularity (\<open>derG\<close>) the Sard/chart engine needs of \<open>G = gradU_dip\<close>.\<close>

lemma gradU_dip_differentiable_x:
  fixes x :: "(real^2)^'n" and V :: "((real^2)^'n) set"
  shows "(\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) differentiable (at x within V)"
proof (subst differentiable_componentwise_within, intro ballI)
  fix b :: "real^2" assume "b \<in> Basis"
  then obtain j where bj: "b = axis j 1" by (auto simp: Basis_vec_def)
  have "(\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j) differentiable (at x within V)"
    by (rule gradU_dip_component_differentiable_x)
  thus "(\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> \<bullet> b) differentiable (at x within V)"
    by (simp add: bj inner_axis)
qed

text \<open>\<^bold>\<open>Surjectivity of a square linear map \<open>\<longleftrightarrow>\<close> nonzero determinant.\<close>  The chart engine
  marks \<open>\<omega>\<close> as \<^emph>\<open>bad\<close> when the \<open>\<omega>\<close>-derivative of \<open>G\<close> fails to be surjective.  For \<open>G =
  \<nabla>\<^sub>\<Omega>U\<close> that derivative is the action \<open>(*v) (\<nabla>\<^sup>2U)\<close> of the Hessian (cf. @{thm
  has_derivative_gradU_c}, @{thm HessU_c_eq}), so the non-surjectivity test is literally
  \<open>det (\<nabla>\<^sup>2U) = 0\<close> --- the third component of \<open>\<Phi>\<close>.  This brick is the linear-algebra hinge:
  for a square matrix \<open>A\<close>, the linear map \<open>h \<mapsto> A *v h\<close> is onto iff \<open>det A \<noteq> 0\<close> (surjective
  \<open>\<Rightarrow>\<close> right-inverse \<open>\<Rightarrow>\<close> two-sided inverse on the square shape \<open>\<Rightarrow>\<close> invertible \<open>\<Rightarrow>\<close> \<open>det \<noteq> 0\<close>;
  conversely \<open>det \<noteq> 0 \<Rightarrow>\<close> invertible \<open>\<Rightarrow>\<close> bijective \<open>\<Rightarrow>\<close> surjective).\<close>

lemma surj_matrix_vector_iff_det:
  fixes A :: "real^'n^'n"
  shows "surj ((*v) A) \<longleftrightarrow> det A \<noteq> 0"
proof
  assume "det A \<noteq> 0"
  hence "invertible A" by (simp add: invertible_det_nz)
  hence "bij ((*v) A)" by (simp add: invertible_eq_bij)
  thus "surj ((*v) A)" by (simp add: bij_betw_def)
next
  assume "surj ((*v) A)"
  then obtain B where AB: "A ** B = mat 1"
    using matrix_right_invertible_surjective by blast
  have "B ** A = mat 1" by (rule matrix_left_right_inverse1[OF AB])
  with AB have "invertible A" unfolding invertible_def by blast
  thus "det A \<noteq> 0" by (simp add: invertible_det_nz)
qed

text \<open>\<^bold>\<open>The \<open>2\<times>2\<close> determinant in \<open>\<Phi>\<close>'s coordinates.\<close>  For a \<^emph>\<open>symmetric\<close> Hessian (\<open>H\<^sub>1\<^sub>2 = H\<^sub>2\<^sub>1\<close>)
  the determinant @{thm det_2} reads \<open>H\<^sub>1\<^sub>1H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2\<close> --- exactly the third slot of \<open>\<Phi>\<close>.\<close>

lemma det_2_symmetric:
  fixes A :: "real^2^2"
  assumes "A $ 1 $ 2 = A $ 2 $ 1"
  shows "det A = A $ 1 $ 1 * A $ 2 $ 2 - (A $ 1 $ 2)\<^sup>2"
  using assms by (simp add: det_2 power2_eq_square)

text \<open>\<^bold>\<open>A surjective \<open>\<bm>x\<close>-partial forces a surjective joint derivative.\<close>  For the regular-value
  input the engine wants the \<^emph>\<open>joint\<close> \<open>(\<bm>x,\<omega>)\<close>-derivative of \<open>G = \<nabla>\<^sub>\<Omega>U\<close> to be onto \<open>\<real>\<^sup>2\<close>.
  But the joint derivative \<open>D\<close> restricts to the configuration partial along \<open>(h,0)\<close>, so if the
  \<^emph>\<open>configuration\<close> derivative alone is already onto (the determinant/\<open>lem:Msurj\<close> payoff: \<open>D\<^sub>\<bm>x\<M>\<close>
  rank \<open>12\<close> \<open>\<Longrightarrow>\<close> \<open>D\<^sub>\<bm>x\<nabla>U\<close> onto when \<open>A \<noteq> 0\<close>), the whole derivative is onto regardless of the
  \<open>\<omega>\<close>-block.  This is the linear-algebra hinge of the submersion step.\<close>

lemma surj_partial_imp_surj_joint:
  fixes Dj :: "('a::real_normed_vector \<times> 'b::real_normed_vector) \<Rightarrow> 'c::real_normed_vector"
  assumes s: "surj Dx" and rel: "\<And>h. Dj (h, 0) = Dx h"
  shows "surj Dj"
proof -
  have "y \<in> range Dj" for y
  proof -
    from s obtain h where "Dx h = y" by (metis surjD)
    hence "Dj (h, 0) = y" using rel by simp
    thus ?thesis by (metis rangeI)
  qed
  thus ?thesis by auto
qed

text \<open>\<^bold>\<open>The joint derivative restricts to the \<open>\<bm>x\<close>-partial along \<open>(h,0)\<close>.\<close>  Composing the
  section \<open>y \<mapsto> (y,\<omega>)\<close> (derivative \<open>h \<mapsto> (h,0)\<close>) with \<open>G\<close> and using uniqueness of the Fréchet
  derivative, the joint derivative \<open>D\<close> of \<open>G\<close> at \<open>(\<bm>x,\<omega>)\<close> satisfies \<open>D(h,0) = D\<^sub>\<bm>x h\<close> for the
  \<open>\<bm>x\<close>-partial \<open>D\<^sub>\<bm>x\<close>.  This supplies the hypothesis of @{thm surj_partial_imp_surj_joint}.\<close>

lemma joint_deriv_restricts_to_partial:
  fixes G :: "('a::real_normed_vector \<times> 'b::real_normed_vector) \<Rightarrow> 'c::real_normed_vector"
  assumes Dj: "(G has_derivative Dj) (at (x, w))"
    and Dx: "((\<lambda>y. G (y, w)) has_derivative Dx) (at x)"
  shows "Dj (h, 0) = Dx h"
proof -
  have sec: "((\<lambda>y. (y, w)) has_derivative (\<lambda>h. (h, 0))) (at x)"
    by (auto intro!: derivative_eq_intros)
  have "((G \<circ> (\<lambda>y. (y, w))) has_derivative (Dj \<circ> (\<lambda>h. (h, 0)))) (at x)"
    by (rule diff_chain_at[OF sec Dj])
  hence "((\<lambda>y. G (y, w)) has_derivative (\<lambda>h. Dj (h, 0))) (at x)"
    by (simp add: o_def)
  from has_derivative_unique[OF this Dx]
  show "Dj (h, 0) = Dx h" by (metis fun_cong)
qed


subsection \<open>Remaining Sard/transversality obligations (\<^bold>\<open>statements only\<close>; proofs deferred)\<close>

text \<open>\<^bold>\<open>The scaffold for \<open>Phi_bad_meager\<close>, stated against the ACTUAL functions.\<close>  These are the
  lemmas that, once proven, discharge \<open>regular_value_on gradU_dip\<close> --- the determinant payoff
  (\<open>lem:Msurj\<close>).  Each carries only the genuinely necessary hypotheses: \<open>A \<noteq> 0\<close> (at \<open>A = 0\<close> every
  configuration is critical and the gradient Jacobian drops rank), surjectivity of the moment-map
  derivative \<open>DM_paper_x\<close> (the proven rank-\<open>12\<close> submersion @{thm Moment_Map.has_derivative_M_paper_x}
  / \<open>bigJ_surj\<close>), and nonsingularity of the steering Jacobian \<open>Dcvec_dip\<close> (the immersion of the
  steering map on its regular locus).  No hypothesis assumes any part of its own conclusion.\<close>

text \<open>\<^bold>\<open>(A1) Regular value from the configuration partial alone.\<close>  On an open product domain, if at
  every zero of \<open>G\<close> the configuration partial \<open>D(\<lambda>y. G(y,\<omega>))\<close> is surjective, then \<open>0\<close> is a regular
  value.  (Pieces @{thm surj_partial_imp_surj_joint}, @{thm joint_deriv_restricts_to_partial}.)\<close>

lemma regular_value_on_via_x_partial:
  fixes G :: "('a::real_normed_vector \<times> 'b::real_normed_vector) \<Rightarrow> 'c::real_normed_vector"
  assumes openS: "open S"
    and partial: "\<And>x w. (x, w) \<in> S \<Longrightarrow> G (x, w) = 0 \<Longrightarrow>
              (\<exists>Dj Dx. (G has_derivative Dj) (at (x, w))
                     \<and> ((\<lambda>y. G (y, w)) has_derivative Dx) (at x) \<and> surj Dx)"
  shows "regular_value_on G S 0"
proof (rule regular_value_onI)
  fix p assume pS: "p \<in> S" and p0: "G p = 0"
  obtain x w where pxw: "p = (x, w)" by (cases p)
  have xwS: "(x, w) \<in> S" using pS pxw by simp
  have G0: "G (x, w) = 0" using p0 pxw by simp
  obtain Dj Dx where dj: "(G has_derivative Dj) (at (x, w))"
      and dx: "((\<lambda>y. G (y, w)) has_derivative Dx) (at x)" and sx: "surj Dx"
    using partial[OF xwS G0] by blast
  have rel: "\<And>h. Dj (h, 0) = Dx h" by (rule joint_deriv_restricts_to_partial[OF dj dx])
  have sj: "surj Dj" by (rule surj_partial_imp_surj_joint[OF sx rel])
  have atxw: "at (x, w) within S = at (x, w)" by (rule at_within_open[OF xwS openS])
  have "(G has_derivative Dj) (at p within S)"
    unfolding pxw atxw by (rule dj)
  with sj show "\<exists>f'. (G has_derivative f') (at p within S) \<and> surj f'" by blast
qed

text \<open>\<^bold>\<open>(A2) The configuration derivative of \<open>gradU_dip\<close> factors through \<open>DM_paper_x\<close>.\<close>  Every
  \<open>\<bm>x\<close>-dependence of the \<open>\<omega>\<close>-gradient routes through the moment map, so \<open>D\<^sub>\<bm>x \<nabla>\<^sub>\<Omega>U = F \<circ> D\<^sub>\<bm>x\<M>\<close> for a
  bounded-linear \<open>F : \<complex>\<^sup>6 \<rightarrow> \<real>\<^sup>2\<close> (the gradient-in-moments Jacobian at the steered wavevector).\<close>

lemma has_derivative_gradU_dip_x:
  fixes x :: "(real^2)^'n" and V :: "((real^2)^'n) set"
  shows "\<exists>F::complex^6 \<Rightarrow> real^2. bounded_linear F
            \<and> ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
                  (F \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x within V)"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define E :: "2 \<Rightarrow> complex^6 \<Rightarrow> real" where
    "E = (\<lambda>j M. frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1) * (cmod (M$1))\<^sup>2
              + gain_dip \<omega> * (2 * Re (cnj (M$1)
                   * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) * (M$2)
                    + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2) * (M$3)))))"
  define \<Phi> :: "complex^6 \<Rightarrow> real^2" where "\<Phi> = (\<lambda>M. (\<chi> j. E j M))"
  \<comment> \<open>the gradient field factors through the moment map\<close>
  have gU: "(\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) = (\<lambda>y. \<Phi> (M_paper y c))"
  proof (rule ext)
    fix y
    have comp: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j = \<Phi> (M_paper y c) $ j" for j :: 2
    proof -
      have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j = E j (M_paper y c)"
        unfolding E_def c_def by (rule gradU_dip_component_moments)
      thus ?thesis by (simp add: \<Phi>_def)
    qed
    show "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> = \<Phi> (M_paper y c)"
      unfolding Finite_Cartesian_Product.vec_eq_iff using comp by blast
  qed
  \<comment> \<open>the moment map's configuration derivative\<close>
  have dM: "((\<lambda>y. M_paper y c) has_derivative DM_paper_x x c) (at x within V)"
    unfolding c_def by (rule has_derivative_M_paper_x)
  \<comment> \<open>\<open>\<Phi>\<close> is (Fréchet) differentiable at the moment point\<close>
  have eproj: "(\<lambda>M::complex^6. M $ k) differentiable (at (M_paper x c))" for k :: 6
    by (rule differentiableI[OF
          bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_ident]])
  have ej: "(\<lambda>M. E j M) differentiable (at (M_paper x c))" for j :: 2
  proof -
    have "(\<lambda>M. E j M)
            = (\<lambda>M. frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
                     * ((Re (M$1))\<^sup>2 + (Im (M$1))\<^sup>2)
                   + gain_dip \<omega> * (2 * Re (cnj (M$1)
                        * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) * (M$2)
                         + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2) * (M$3)))))"
      by (rule ext) (simp add: E_def cmod_power2)
    moreover have "(\<lambda>M::complex^6. frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
                     * ((Re (M$1))\<^sup>2 + (Im (M$1))\<^sup>2)
                   + gain_dip \<omega> * (2 * Re (cnj (M$1)
                        * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) * (M$2)
                         + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2) * (M$3)))))
                   differentiable (at (M_paper x c))"
      by (intro differentiable_add differentiable_mult differentiable_const differentiable_power
                differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_Re]]
                differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_Im]]
                differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_cnj]]
                eproj)
    ultimately show ?thesis by simp
  qed
  have d\<Phi>: "\<Phi> differentiable (at (M_paper x c))"
  proof -
    have "\<Phi> differentiable (at (M_paper x c) within UNIV)"
    proof (subst differentiable_componentwise_within, intro ballI)
      fix b :: "real^2" assume "b \<in> Basis"
      then obtain j where bj: "b = axis j 1" by (auto simp: Basis_vec_def)
      have "(\<lambda>M. \<Phi> M \<bullet> b) = (\<lambda>M. E j M)"
        by (rule ext) (simp add: \<Phi>_def bj inner_axis)
      thus "(\<lambda>M. \<Phi> M \<bullet> b) differentiable (at (M_paper x c) within UNIV)"
        using ej by simp
    qed
    thus ?thesis by simp
  qed
  then obtain D\<Phi> where hD\<Phi>: "(\<Phi> has_derivative D\<Phi>) (at (M_paper x c))"
    by (auto simp: differentiable_def)
  have blD\<Phi>: "bounded_linear D\<Phi>" by (rule has_derivative_bounded_linear[OF hD\<Phi>])
  have chain: "((\<lambda>y. \<Phi> (M_paper y c)) has_derivative (D\<Phi> \<circ> DM_paper_x x c)) (at x within V)"
  proof -
    have "((\<Phi> \<circ> (\<lambda>y. M_paper y c)) has_derivative (D\<Phi> \<circ> DM_paper_x x c)) (at x within V)"
      by (rule diff_chain_within[OF dM has_derivative_at_withinI[OF hD\<Phi>]])
    thus ?thesis by (simp add: o_def)
  qed
  have fin: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
                 (D\<Phi> \<circ> DM_paper_x x c)) (at x within V)"
    unfolding gU by (rule chain)
  show ?thesis using blD\<Phi> fin unfolding c_def by blast
qed

text \<open>\<^bold>\<open>The actual dipole gain is nonzero off the endfire nulls.\<close>  \<open>gain_dip \<omega> = gdip(\<omega>\<^sub>1)\<close> and
  \<open>gdip \<theta> = (edip \<theta>)\<^sup>2\<close>; the half-wave dipole pattern \<open>edip \<theta> = cos(\<pi>/2 cos\<theta>)/sin\<theta>\<close> vanishes only where
  \<open>cos(\<pi>/2 cos\<theta>) = 0 \<longleftrightarrow> cos\<theta> = \<pm>1 \<longleftrightarrow> sin\<theta> = 0\<close>.  So off \<open>sin\<theta> = 0\<close> the gain is strictly positive.
  Crucially the steering determinant carries a \<open>sin(\<omega>\<^sub>1)\<close> factor (its \<open>\<omega>\<close>-column is
  \<open>(-sin\<omega>\<^sub>1 sin\<omega>\<^sub>2, sin\<omega>\<^sub>1 cos\<omega>\<^sub>2)\<close>), so the immersion hypothesis \<open>det(Dcvec) \<noteq> 0\<close> already forces
  \<open>sin(\<omega>\<^sub>1) \<noteq> 0\<close>, hence \<open>gain_dip \<omega> \<noteq> 0\<close> --- no separate gain hypothesis is needed.\<close>

lemma gain_dip_nonzero_of_sin:
  fixes \<omega> :: "real^2"
  assumes "sin (\<omega> $ 1) \<noteq> 0"
  shows "gain_dip \<omega> \<noteq> 0"
proof -
  have cb: "(cos (\<omega> $ 1))\<^sup>2 < 1"
  proof -
    have "0 < (sin (\<omega> $ 1))\<^sup>2" using assms by simp
    moreover have "(sin (\<omega> $ 1))\<^sup>2 + (cos (\<omega> $ 1))\<^sup>2 = 1"
      by (rule sin_cos_squared_add)
    ultimately show ?thesis by linarith
  qed
  hence cabs: "\<bar>cos (\<omega> $ 1)\<bar> < 1" by (simp add: abs_square_less_1)
  have c_lo: "- 1 < cos (\<omega> $ 1)" and c_hi: "cos (\<omega> $ 1) < 1"
    using cabs by (auto simp: abs_less_iff)
  have hpi: "0 < pi/2" using pi_gt_zero by simp
  have "0 < cos (pi/2 * cos (\<omega> $ 1))"
  proof (rule cos_gt_zero_pi)
    have "pi/2 * (- 1) < pi/2 * cos (\<omega> $ 1)"
      by (rule mult_strict_left_mono[OF c_lo hpi])
    thus "- (pi/2) < pi/2 * cos (\<omega> $ 1)" by simp
  next
    have "pi/2 * cos (\<omega> $ 1) < pi/2 * 1"
      by (rule mult_strict_left_mono[OF c_hi hpi])
    thus "pi/2 * cos (\<omega> $ 1) < pi/2" by simp
  qed
  hence "cos (pi/2 * cos (\<omega> $ 1)) \<noteq> 0" by simp
  hence "edip (\<omega> $ 1) \<noteq> 0" using assms by (simp add: edip_def)
  hence "(edip (\<omega> $ 1))\<^sup>2 \<noteq> 0" by simp
  hence "gdip (\<omega> $ 1) \<noteq> 0" by (simp add: gdip_eq_edip_sq)
  thus ?thesis by (simp add: gain_dip_def)
qed

text \<open>\<^bold>\<open>The steering determinant carries the \<open>sin(\<omega>\<^sub>1)\<close> factor.\<close>  At \<open>sin(\<omega>\<^sub>1) = 0\<close> the steering
  Jacobian \<open>Dcvec_dip\<close> sends \<open>axis 2 1\<close> to \<open>0\<close> (its \<open>\<omega>\<close>-column vanishes), so it is not injective and
  its determinant is \<open>0\<close>.  Contrapositively \<open>det \<noteq> 0 \<Longrightarrow> sin(\<omega>\<^sub>1) \<noteq> 0\<close>, which with
  @{thm gain_dip_nonzero_of_sin} yields \<open>gain_dip \<omega> \<noteq> 0\<close> from the immersion hypothesis alone.\<close>

lemma Dcvec_det_zero_of_sin:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2"
  assumes "sin (\<omega> $ 1) = 0"
  shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
proof -
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have z2: "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) = 0"
    using assms unfolding Dcvec_dip_def by (simp add: axis_def)
  have ax_nz: "axis (2::2) (1::real) \<noteq> 0"
    by (metis axis_nth zero_index zero_neq_one)
  have "\<not> inj (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    using z2 ax_nz lin by (metis injD linear_0)
  thus ?thesis using det_nz_iff_inj[OF lin] by blast
qed

text \<open>\<^bold>\<open>(A3) The determinant payoff: the configuration partial is onto \<open>\<real>\<^sup>2\<close>.\<close>  When \<open>A \<noteq> 0\<close>, the
  moment map is a submersion (\<open>surj (DM_paper_x \<dots>)\<close>, \<open>lem:Msurj\<close>), and the steering map is an
  immersion (\<open>det (Dcvec_dip \<dots>) \<noteq> 0\<close>, which also forces \<open>gain_dip \<omega> \<noteq> 0\<close>), the \<open>\<bm>x\<close>-derivative
  of \<open>\<nabla>\<^sub>\<Omega>U\<close> is surjective.\<close>

text \<open>\<^bold>\<open>Analytic core of the determinant payoff.\<close>  For a nonzero complex \<open>a\<close>, the real-linear
  functional \<open>w \<mapsto> Im(\<bar>a\<bar>\<dots>cnj a \<cdot> w)\<close> is onto \<open>\<real>\<close> --- multiplication by the nonzero \<open>cnj a\<close> is a
  \<complex>-bijection and \<open>Im\<close> is onto.  This is why each gradient component's \<open>\<bm>x\<close>-derivative can hit
  any real value once \<open>A \<noteq> 0\<close>.\<close>

lemma surj_Im_cnj_mult:
  fixes a :: complex
  assumes "a \<noteq> 0"
  shows "surj (\<lambda>w. Im (cnj a * w))"
proof -
  have cnz: "cnj a \<noteq> 0" using assms by simp
  show ?thesis
    unfolding surj_def
  proof (intro allI)
    fix y :: real
    have "y = Im (cnj a * (\<i> * complex_of_real y / cnj a))"
      using cnz by (simp add: field_simps)
    thus "\<exists>x. y = Im (cnj a * x)" by blast
  qed
qed

text \<open>\<^bold>\<open>Linear-algebra core of the determinant payoff.\<close>  The two real-linear forms
  \<open>(d\<^sub>2,d\<^sub>3) \<mapsto> 2g\<cdot>Im(cnj a \<cdot> (c\<^sub>j\<^sub>1 d\<^sub>2 + c\<^sub>j\<^sub>2 d\<^sub>3))\<close> (\<open>j = 1,2\<close>) jointly hit all of \<open>\<real>\<^sup>2\<close> when
  \<open>a \<noteq> 0\<close>, \<open>g \<noteq> 0\<close> and the \<open>2\<times>2\<close> coefficient matrix is nonsingular: pick \<open>w\<^sub>j\<close> with
  \<open>2g\<cdot>Im(cnj a\<cdot>w\<^sub>j) = t\<^sub>j\<close> (analytic core), then solve the nonsingular real system
  \<open>c\<^sub>j\<^sub>1 d\<^sub>2 + c\<^sub>j\<^sub>2 d\<^sub>3 = w\<^sub>j\<close> by Cramer's rule.\<close>

lemma surj_moment_grad_map:
  fixes a :: complex and g c11 c12 c21 c22 :: real
  assumes a0: "a \<noteq> 0" and g0: "g \<noteq> 0" and detC: "c11 * c22 - c12 * c21 \<noteq> 0"
  shows "surj (\<lambda>p::complex \<times> complex.
            (2 * g * Im (cnj a * (complex_of_real c11 * fst p + complex_of_real c12 * snd p)),
             2 * g * Im (cnj a * (complex_of_real c21 * fst p + complex_of_real c22 * snd p))))"
proof -
  have cnz: "cnj a \<noteq> 0" using a0 by simp
  have Dr: "c11 * c22 - c12 * c21 \<noteq> 0" using detC by simp
  have Dnz: "complex_of_real (c11 * c22 - c12 * c21) \<noteq> 0"
    by (metis Dr of_real_eq_0_iff)
  have Deq: "complex_of_real (c11 * c22 - c12 * c21)
             = complex_of_real c11 * complex_of_real c22 - complex_of_real c12 * complex_of_real c21"
    by (simp add: of_real_diff of_real_mult)
  show ?thesis
    unfolding surj_def
  proof (intro allI)
    fix t :: "real \<times> real"
    obtain t1 t2 where t: "t = (t1, t2)" by (cases t)
    define w1 where "w1 = \<i> * complex_of_real (t1 / (2 * g)) / cnj a"
    define w2 where "w2 = \<i> * complex_of_real (t2 / (2 * g)) / cnj a"
    have iw1: "2 * g * Im (cnj a * w1) = t1" using cnz g0 by (simp add: w1_def field_simps)
    have iw2: "2 * g * Im (cnj a * w2) = t2" using cnz g0 by (simp add: w2_def field_simps)
    define d2 where "d2 = (complex_of_real c22 * w1 - complex_of_real c12 * w2)
                            / complex_of_real (c11 * c22 - c12 * c21)"
    define d3 where "d3 = (complex_of_real c11 * w2 - complex_of_real c21 * w1)
                            / complex_of_real (c11 * c22 - c12 * c21)"
    have e1: "complex_of_real c11 * d2 + complex_of_real c12 * d3 = w1"
    proof -
      have "complex_of_real c11 * d2 + complex_of_real c12 * d3
            = (complex_of_real c11 * (complex_of_real c22 * w1 - complex_of_real c12 * w2)
               + complex_of_real c12 * (complex_of_real c11 * w2 - complex_of_real c21 * w1))
              / complex_of_real (c11 * c22 - c12 * c21)"
        by (simp add: d2_def d3_def add_divide_distrib)
      also have "\<dots> = (complex_of_real (c11 * c22 - c12 * c21) * w1)
                       / complex_of_real (c11 * c22 - c12 * c21)"
        by (simp add: Deq algebra_simps)
      also have "\<dots> = w1" using Dnz by simp
      finally show ?thesis .
    qed
    have e2: "complex_of_real c21 * d2 + complex_of_real c22 * d3 = w2"
    proof -
      have "complex_of_real c21 * d2 + complex_of_real c22 * d3
            = (complex_of_real c21 * (complex_of_real c22 * w1 - complex_of_real c12 * w2)
               + complex_of_real c22 * (complex_of_real c11 * w2 - complex_of_real c21 * w1))
              / complex_of_real (c11 * c22 - c12 * c21)"
        by (simp add: d2_def d3_def add_divide_distrib)
      also have "\<dots> = (complex_of_real (c11 * c22 - c12 * c21) * w2)
                       / complex_of_real (c11 * c22 - c12 * c21)"
        by (simp add: Deq algebra_simps)
      also have "\<dots> = w2" using Dnz by simp
      finally show ?thesis .
    qed
    have "t = (2 * g * Im (cnj a * (complex_of_real c11 * fst (d2, d3)
                                     + complex_of_real c12 * snd (d2, d3))),
               2 * g * Im (cnj a * (complex_of_real c21 * fst (d2, d3)
                                     + complex_of_real c22 * snd (d2, d3))))"
      by (simp only: t fst_conv snd_conv e1 e2 iw1 iw2)
    thus "\<exists>p. t = (2 * g * Im (cnj a * (complex_of_real c11 * fst p + complex_of_real c12 * snd p)),
                   2 * g * Im (cnj a * (complex_of_real c21 * fst p + complex_of_real c22 * snd p)))"
      by blast
  qed
qed

text \<open>\<^bold>\<open>Explicit moment-space derivative of a gradient component.\<close>  The \<open>j\<close>-th component of
  \<open>\<nabla>\<^sub>\<Omega>U_dip\<close>, read as a function of the moment vector \<open>M \<in> \<complex>\<^sup>6\<close> via
  @{thm gradU_dip_component_moments} (with \<open>p = \<partial>gdip\<close>, \<open>g = gain_dip \<omega>\<close>, \<open>c\<^sub>1,c\<^sub>2\<close> the steering
  Jacobian column), has the explicit Fréchet derivative below: the \<open>\<bar>M\<^sub>1\<bar>\<^sup>2\<close> term differentiates to
  \<open>2Re(M\<^sub>1)Re(\<delta>\<^sub>1)+2Im(M\<^sub>1)Im(\<delta>\<^sub>1)\<close> and the bilinear term by the product rule.\<close>

lemma has_derivative_Ej_moment:
  fixes M0 :: "complex^6" and p g c1 c2 :: real
  shows "((\<lambda>M. p * ((Re (M$1))\<^sup>2 + (Im (M$1))\<^sup>2)
              + g * (2 * Re (cnj (M$1) * ((- \<i>) * complex_of_real c1 * (M$2)
                                        + (- \<i>) * complex_of_real c2 * (M$3)))))
          has_derivative
          (\<lambda>\<delta>. p * (2 * Re (M0$1) * Re (\<delta>$1) + 2 * Im (M0$1) * Im (\<delta>$1))
             + g * (2 * Re (cnj (\<delta>$1) * ((- \<i>) * complex_of_real c1 * (M0$2)
                                        + (- \<i>) * complex_of_real c2 * (M0$3))
                          + cnj (M0$1) * ((- \<i>) * complex_of_real c1 * (\<delta>$2)
                                        + (- \<i>) * complex_of_real c2 * (\<delta>$3))))))
          (at M0)"
proof -
  have proj: "((\<lambda>M::complex^6. M $ k) has_derivative (\<lambda>\<delta>. \<delta> $ k)) (at M0)" for k
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_ident])
  show ?thesis
      by (auto intro!: derivative_eq_intros proj bounded_linear.has_derivative[OF bounded_linear_Re]
                       bounded_linear.has_derivative[OF bounded_linear_Im]
                       bounded_linear.has_derivative[OF bounded_linear_cnj]
                       simp: algebra_simps)
qed

text \<open>\<^bold>\<open>Named moment-gradient component and its derivative.\<close>  Packaging @{thm
  gradU_dip_component_moments} (after \<open>cmod\<^sup>2 = Re\<^sup>2 + Im\<^sup>2\<close>) as the function \<open>Ejm\<close> of the moment
  vector, with explicit Fréchet derivative \<open>dEjm\<close> (= @{thm has_derivative_Ej_moment}), lets us
  chain through @{thm has_derivative_M_paper_x} without rewriting the large derivative term.\<close>

definition Ejm :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex^6 \<Rightarrow> real" where
  "Ejm p g c1 c2 = (\<lambda>M. p * ((Re (M$1))\<^sup>2 + (Im (M$1))\<^sup>2)
              + g * (2 * Re (cnj (M$1) * ((- \<i>) * complex_of_real c1 * (M$2)
                                        + (- \<i>) * complex_of_real c2 * (M$3)))))"

definition dEjm :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex^6 \<Rightarrow> complex^6 \<Rightarrow> real" where
  "dEjm p g c1 c2 M0 = (\<lambda>\<delta>. p * (2 * Re (M0$1) * Re (\<delta>$1) + 2 * Im (M0$1) * Im (\<delta>$1))
              + g * (2 * Re (cnj (\<delta>$1) * ((- \<i>) * complex_of_real c1 * (M0$2)
                                        + (- \<i>) * complex_of_real c2 * (M0$3))
                          + cnj (M0$1) * ((- \<i>) * complex_of_real c1 * (\<delta>$2)
                                        + (- \<i>) * complex_of_real c2 * (\<delta>$3)))))"

lemma has_derivative_Ejm:
  fixes M0 :: "complex^6" and p g c1 c2 :: real
  shows "(Ejm p g c1 c2 has_derivative dEjm p g c1 c2 M0) (at M0)"
  unfolding Ejm_def dEjm_def by (rule has_derivative_Ej_moment)

text \<open>\<^bold>\<open>(iii, step 2) Explicit \<open>\<bm>x\<close>-derivative of a gradient component.\<close>  The chain rule through
  the proven moment-map derivative @{thm has_derivative_M_paper_x}: \<open>\<partial>\<^sub>\<bm>x(\<nabla>\<^sub>\<Omega>U)\<^sub>j = dEjm \<circ> DM\<close>.\<close>

lemma has_derivative_gradU_dip_component_x:
  fixes x :: "(real^2)^'n"
  shows "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j) has_derivative
            (dEjm (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                  ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
             \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x)"
proof -
  have eq: "(\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ j)
            = (\<lambda>y. Ejm (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                       ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                       (M_paper y (cvec_dip \<omega>0 \<omega>s \<omega>)))"
    by (rule ext) (simp add: gradU_dip_component_moments cmod_power2 Ejm_def)
  have dM: "((\<lambda>y. M_paper y (cvec_dip \<omega>0 \<omega>s \<omega>)) has_derivative DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)) (at x)"
    using has_derivative_M_paper_x[where V=UNIV] by fastforce
  show ?thesis
      unfolding eq
      using diff_chain_at[OF dM has_derivative_Ejm]
      by (simp add: o_def)
qed

lemma has_derivative_gradU_dip_x_explicit:
    fixes x :: "(real^2)^'n" and V :: "((real^2)^'n) set"
    shows "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s)
  gain_dip y \<omega>) has_derivative
              (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip
  (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                            ((Dcvec_dip \<omega>0 \<omega>s
  \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega>
  (axis j 1))$2)
                            (M_paper x (cvec_dip \<omega>0
  \<omega>s \<omega>))
                            (DM_paper_x x (cvec_dip \<omega>0
  \<omega>s \<omega>) h))) (at x within V)"
  proof (subst has_derivative_componentwise_within, intro ballI)
    fix b :: "real^2" assume "b \<in> Basis"
    then obtain j where bj: "b = axis j 1" by (auto simp:
  Basis_vec_def)
    show "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s)
  gain_dip y \<omega> \<bullet> b) has_derivative
            (\<lambda>h. (\<chi> j. dEjm (frechet_derivative gdip
  (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                            ((Dcvec_dip \<omega>0 \<omega>s
  \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega>
  (axis j 1))$2)
                            (M_paper x (cvec_dip \<omega>0
  \<omega>s \<omega>))
                            (DM_paper_x x (cvec_dip \<omega>0
  \<omega>s \<omega>) h)) \<bullet> b)) (at x within V)"
      using has_derivative_gradU_dip_component_x[where j=j, THEN
  has_derivative_at_withinI]
      by (simp add: bj inner_axis o_def)
  qed

text \<open>\<^bold>\<open>(iii, step 4 helper) The moment-derivative on the \<open>(M\<^sub>2,M\<^sub>3)\<close>-plane.\<close>  On the moment tangent
  \<open>\<delta> = (0,d\<^sub>2,d\<^sub>3,0,0,0)\<close> the \<open>\<bar>M\<^sub>1\<bar>\<^sup>2\<close> term of \<open>dEjm\<close> vanishes (its \<open>\<delta>\<^sub>1\<close> is \<open>0\<close>), leaving the steering
  bilinear in the \<open>Im\<close>-form (\<open>Re((-\<ii>)w) = Im w\<close>) --- exactly the components of @{thm
  surj_moment_grad_map}.\<close>

lemma dEjm_on_e:
  fixes M0 :: "complex^6" and p g c1 c2 :: real and d2 d3 :: complex
  shows "dEjm p g c1 c2 M0 (axis 2 d2 + axis 3 d3)
         = 2 * g * Im (cnj (M0$1) * (complex_of_real c1 * d2 + complex_of_real c2 * d3))"
proof -
  have key: "Re (cnj (M0$1) * ((- \<i>) * complex_of_real c1 * d2 + (- \<i>) * complex_of_real c2 * d3))
             = Im (cnj (M0$1) * (complex_of_real c1 * d2 + complex_of_real c2 * d3))"
  proof -
    have "cnj (M0$1) * ((- \<i>) * complex_of_real c1 * d2 + (- \<i>) * complex_of_real c2 * d3)
          = (- \<i>) * (cnj (M0$1) * (complex_of_real c1 * d2 + complex_of_real c2 * d3))"
      by (simp add: algebra_simps)
    thus ?thesis by simp
  qed
  show ?thesis
    unfolding dEjm_def by (simp add: axis_def key algebra_simps)
qed

lemma gradU_dip_x_partial_surj:
  fixes x :: "(real^2)^'n"
  assumes Anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
    and Msurj: "surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    and steer: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx"
proof -
  define dE :: "complex^6 \<Rightarrow> real^2" where
    "dE = (\<lambda>\<delta>. \<chi> j. dEjm (frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)) (gain_dip \<omega>)
                       ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1) ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                       (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) \<delta>)"
  have hd: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
              (dE \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x)"
    using has_derivative_gradU_dip_x_explicit[where V=UNIV] by (simp add: dE_def o_def)
  \<comment> \<open>the three nondegeneracy ingredients (\<open>A \<noteq> 0\<close>, \<open>gain \<noteq> 0\<close>, immersion) all from the hypotheses\<close>
  have a0: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 \<noteq> 0"
    by (metis Anz M_paper_proj_A)
  have g0: "gain_dip \<omega> \<noteq> 0"
    using steer Dcvec_det_zero_of_sin gain_dip_nonzero_of_sin by metis
  have detC: "(Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))$2
            - (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))$1 \<noteq> 0"
    using steer by (simp add: det_2 matrix_def, argo)
  \<comment> \<open>\<open>dE\<close> is onto via @{thm surj_moment_grad_map} on the \<open>(M\<^sub>2,M\<^sub>3)\<close> directions\<close>
  have surjdE: "surj dE"
  proof (unfold surj_def, intro allI)
    fix t :: "real^2"
    obtain p :: "complex \<times> complex" where p:
      "(t $ 1, t $ 2) =
         (2 * gain_dip \<omega> * Im (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
              * (complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1) * fst p
               + complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2) * snd p)),
          2 * gain_dip \<omega> * Im (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
              * (complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))$1) * fst p
               + complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1))$2) * snd p)))"
      using surjD[OF surj_moment_grad_map[OF a0 g0 detC]] by blast
    have c1: "dE (axis 2 (fst p) + axis 3 (snd p)) $ 1 = t $ 1"
        using p by (simp add: dE_def dEjm_on_e)
    have c2: "dE (axis 2 (fst p) + axis 3 (snd p)) $ 2 = t $ 2"
        using p by (simp add: dE_def dEjm_on_e)
    have "t = dE (axis 2 (fst p) + axis 3 (snd p))"
      by (smt (verit) Finite_Cartesian_Product.vec_eq_iff c1 c2 exhaust_2)
    thus "\<exists>\<delta>. t = dE \<delta>" by blast
    qed
  have "surj (dE \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    by (rule comp_surj[OF Msurj surjdE])
  with hd show ?thesis by blast
qed

text \<open>\<^bold>\<open>(A4) The regularity locus is open.\<close>  \<open>A_cart\<close> is continuous (jointly in \<open>(\<bm>x,\<omega>)\<close>), the
  steering determinant is continuous in \<open>\<omega>\<close>, and the submersion set \<open>{surj (DM_paper_x \<dots>)}\<close> is open
  by \<^emph>\<open>lower semicontinuity of rank\<close> of the continuously-varying linear map \<open>DM_paper_x\<close> --- so the
  full regularity locus (the open \<open>S\<close> on which the regular value lives) is open.\<close>

lemma open_A_cart_nonzero:
  shows "open {p :: ((real^2)^'n) \<times> (real^2).
                 A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
               \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
               \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}"
  sorry

text \<open>\<^bold>\<open>(A5) The dipole gradient field is jointly \<open>C\<^sup>1\<close> in \<open>(\<bm>x,\<omega>)\<close>.\<close>  \<open>U_dip\<close> is smooth in both
  arguments, so \<open>G = \<nabla>\<^sub>\<Omega>U\<close> has a continuous (blinfun) derivative field --- the \<open>derG\<close>/\<open>contG'\<close>
  inputs of the chart engine's local step @{thm regular_zero_set_projection_local_chart_2d}.\<close>

lemma gradU_dip_joint_C1:
  shows "\<exists>G'::(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2)).
            (\<forall>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                     has_derivative blinfun_apply (G' z)) (at z))
          \<and> continuous_on UNIV G'"
  sorry

text \<open>\<^bold>\<open>(A6) Assembled regular value of the dipole gradient field --- CORRECTED DOMAIN.\<close>  \<open>0\<close> is a
  regular value of the joint map \<open>(\<bm>x,\<omega>) \<mapsto> \<nabla>\<^sub>\<Omega>U_dip\<close> on the open locus where \<^bold>\<open>all three\<close>
  regularity conditions hold: \<open>A \<noteq> 0\<close>, the moment map is a submersion (\<open>surj (DM_paper_x \<dots>)\<close>), and
  the steering Jacobian is nonsingular.  \<^bold>\<open>The \<open>surj (DM_paper_x \<dots>)\<close> conjunct is essential and was
  missing before:\<close> @{thm gradU_dip_x_partial_surj} genuinely needs it, and it is \<^emph>\<open>not\<close> implied by
  \<open>A \<noteq> 0\<close> (it is the open-dense rank-\<open>12\<close> condition, the \<open>m_star \<noteq> 0\<close> stratum).  Configurations
  failing it form the rank-deficient stratum, which is handled separately
  (\<open>meager_rank_deficient_stratum\<close> below).\<close>

lemma regular_value_on_gradU_dip:
  fixes V :: "((real^2)^'n) set"
  assumes openV: "open V" and c6: "6 \<le> CARD('n)"
  shows "regular_value_on (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
            ({p \<in> V \<times> UNIV. A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
                             \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
                             \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}) 0"
proof (rule regular_value_on_via_x_partial)
  have eq: "{p \<in> V \<times> UNIV. A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
                            \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
                            \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}
          = (V \<times> UNIV) \<inter> {p::((real^2)^'n) \<times> (real^2).
                 A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
               \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
               \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}"
    by auto
  show "open {p \<in> V \<times> UNIV. A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
                            \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
                            \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}"
    unfolding eq
    by (intro open_Int open_Times open_A_cart_nonzero openV open_UNIV)
next
  fix x w
  assume mem: "(x, w) \<in> {p \<in> V \<times> UNIV. A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
                            \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
                            \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}"
    and G0: "(\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x, w) = 0"
  from mem have Anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x w \<noteq> 0"
    and DMs: "surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s w))"
    and dets: "det (matrix (Dcvec_dip \<omega>0 \<omega>s w)) \<noteq> 0" by auto
  obtain Dx where dx: "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y w) has_derivative Dx) (at x)"
      and sx: "surj Dx"
    using gradU_dip_x_partial_surj[OF Anz DMs dets] by blast
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                       has_derivative blinfun_apply (G' z)) (at z)"
    using gradU_dip_joint_C1 by blast
  show "\<exists>Dj Dx. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) has_derivative Dj) (at (x, w))
              \<and> ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst (y, w)) (snd (y, w))) has_derivative Dx) (at x)
              \<and> surj Dx"
  proof (intro exI conjI)
    show "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
             has_derivative blinfun_apply (G' (x, w))) (at (x, w))"
      by (rule derG)
  next
    show "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst (y, w)) (snd (y, w)))
             has_derivative Dx) (at x)"
      using dx by simp
  next
    show "surj Dx" by (rule sx)
  qed
qed


subsection \<open>Tying the bad-point map \<open>\<Phi>\<close> to \<open>U_cart\<close> (the determinant's payoff, \<^emph>\<open>upstream\<close> of the capstone)\<close>

text \<open>\<^bold>\<open>This is the bridge that the determinant computations exist for.\<close>  On the regular
  stratum the paper's bad-point map (tex L516) is
  \<open>\<Phi> = (\<partial>\<^sub>c\<^sub>1 U, \<partial>\<^sub>c\<^sub>2 U, det \<nabla>\<^sup>2 U)\<close> with \<open>U = U_cart\<close> the actual radiation pattern.  Thus
  \<^item> \<open>\<Phi>\<^sub>1 = \<Phi>\<^sub>2 = 0\<close>  \<open>\<longleftrightarrow>\<close>  \<open>\<nabla>U = 0\<close>  \<open>\<longleftrightarrow>\<close>  \<open>\<omega>\<close> is a \<^emph>\<open>critical point\<close> of the pattern;
  \<^item> \<open>\<Phi>\<^sub>3 = det \<nabla>\<^sup>2 U = 0\<close>  \<open>\<longleftrightarrow>\<close> the critical point is \<^emph>\<open>degenerate\<close>.
  So \<open>\<Phi>(\<bm>x,\<omega>) = 0\<close> exactly picks out the degenerate critical points --- the configurations
  that must be excluded for \<open>\<bm>x \<in> X\<^sub>0\<close>.  The determinant (\<open>lem:Msurj\<close>: \<open>D\<^sub>x\<M>\<close> rank \<open>12\<close>) makes the
  moment map a submersion, so \<open>{\<Phi> = 0}\<close> is a positive-codimension submanifold (\<open>prop:dimZ\<close>)
  whose projection is meager (\<open>lem:smooth-chart-meager\<close>) --- the obligation \<open>Phi_bad_meager\<close>,
  which feeds \<open>regular_feasible_witness\<close> below.\<close>

definition Phibad ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> real^3"
  where \<comment> \<open>\<open>\<Phi> = (\<partial>\<^sub>c\<^sub>1U, \<partial>\<^sub>c\<^sub>2U, det \<nabla>\<^sup>2U)\<close>; \<open>\<Phi> = 0 \<longleftrightarrow>\<close> degenerate critical point of \<open>U_cart\<close>\<close>
  "Phibad cvec gain x \<omega> =
     vector [ gradU cvec gain x \<omega> $ 1,
              gradU cvec gain x \<omega> $ 2,
              HessU cvec gain x \<omega> $ 1 $ 1 * HessU cvec gain x \<omega> $ 2 $ 2
                - (HessU cvec gain x \<omega> $ 1 $ 2)\<^sup>2 ]"

text \<open>\<^bold>\<open>Bridge, semantic core.\<close>  \<open>\<Phi>(\<bm>x,\<omega>) = 0\<close> says exactly that \<open>\<omega>\<close> is a \<^emph>\<open>degenerate
  critical point\<close> of the pattern: the gradient \<open>\<nabla>U_cart\<close> vanishes (critical) and the
  Hessian determinant \<open>H\<^sub>1\<^sub>1H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2\<close> vanishes (degenerate).  This ties the abstract bad
  set to the concrete nondegeneracy condition of \<open>X\<^sub>0\<close>.\<close>

lemma Phibad_zero_iff:
  "Phibad cvec gain x \<omega> = 0
   \<longleftrightarrow> gradU cvec gain x \<omega> = 0
       \<and> HessU cvec gain x \<omega> $ 1 $ 1 * HessU cvec gain x \<omega> $ 2 $ 2
           = (HessU cvec gain x \<omega> $ 1 $ 2)\<^sup>2"
proof -
  \<comment> \<open>\<open>\<Phi> = 0\<close> iff its three components vanish (HMA-qualified \<open>vec_eq_iff\<close> +
      \<open>forall_3\<close>/\<open>vector_3\<close>; the third component is \<open>H\<^sub>1\<^sub>1H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2\<close>).\<close>
  have L: "Phibad cvec gain x \<omega> = 0
           \<longleftrightarrow> gradU cvec gain x \<omega> $ 1 = 0 \<and> gradU cvec gain x \<omega> $ 2 = 0
             \<and> HessU cvec gain x \<omega> $ 1 $ 1 * HessU cvec gain x \<omega> $ 2 $ 2
                 - (HessU cvec gain x \<omega> $ 1 $ 2)\<^sup>2 = 0"
    unfolding Phibad_def
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_3 vector_3)
  \<comment> \<open>the 2-D gradient vanishes iff both its components do.\<close>
  have G: "gradU cvec gain x \<omega> = 0
           \<longleftrightarrow> gradU cvec gain x \<omega> $ 1 = 0 \<and> gradU cvec gain x \<omega> $ 2 = 0"
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
  show ?thesis using L G by (auto simp: algebra_simps)
qed

text \<open>\<^bold>\<open>The chart engine's non-surjectivity test \<open>=\<close> Hessian degeneracy, for the dipole.\<close>
  The transversality engine flags \<open>(\<bm>x,\<omega>)\<close> as critical exactly when the \<open>\<omega>\<close>-derivative of
  \<open>G = \<nabla>\<^sub>\<Omega>U\<close> has no surjective branch.  For the \<open>C\<^sup>2\<close> dipole that derivative is unique and
  equals the Hessian action \<open>(*v) (\<nabla>\<^sup>2U)\<close> (@{thm gradU_dip_has_derivative}); by @{thm
  surj_matrix_vector_iff_det} it is onto iff \<open>det (\<nabla>\<^sup>2U) \<noteq> 0\<close>.  Hence the engine's
  non-surjectivity predicate is \<^emph>\<open>literally\<close> \<open>det (\<nabla>\<^sup>2U) = 0\<close> --- the degeneracy condition that
  enters \<open>\<Phi>\<close>'s third slot.  We phrase it with \<open>at \<omega> within \<Omega>\<close> (\<open>\<omega>\<close> interior to the open
  \<open>\<Omega>\<close>) so it plugs straight into the engine's bad-set description.\<close>

lemma not_surj_omega_deriv_iff_detHess_dip:
  fixes x :: "(real^2)^'n"
  assumes O: "open \<Omega>" and w: "\<omega> \<in> \<Omega>"
  shows "(\<not> (\<exists>D\<omega>. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D\<omega>)
                  (at \<omega> within \<Omega>) \<and> surj D\<omega>))
         \<longleftrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
proof -
  have atw: "at \<omega> within \<Omega> = at \<omega>" by (rule at_within_open[OF w O])
  have hd: "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative
              (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)) (at \<omega>)"
    by (rule gradU_dip_has_derivative)
  show ?thesis unfolding atw
  proof
    assume "\<not> (\<exists>D\<omega>. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D\<omega>)
                    (at \<omega>) \<and> surj D\<omega>)"
    hence "\<not> surj ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
      using hd by blast
    thus "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      using surj_matrix_vector_iff_det by blast
  next
    assume d0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
    show "\<not> (\<exists>D\<omega>. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D\<omega>)
                  (at \<omega>) \<and> surj D\<omega>)"
    proof
      assume "\<exists>D\<omega>. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D\<omega>)
                   (at \<omega>) \<and> surj D\<omega>"
      then obtain D\<omega>
        where hD: "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D\<omega>)
                     (at \<omega>)" and sD: "surj D\<omega>" by blast
      have "D\<omega> = (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)"
        by (rule has_derivative_unique[OF hD hd])
      with sD have "surj ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))" by simp
      with d0 surj_matrix_vector_iff_det show False by blast
    qed
  qed
qed

text \<open>\<^bold>\<open>The dipole Hessian is symmetric\<close> (Clairaut/Schwarz): \<open>U_dip\<close> is \<open>C\<^sup>2\<close> everywhere
  (@{thm U_dip_Ck2}), so its mixed partials commute (@{thm mixed_partials_commute}).\<close>

lemma HessU_dip_symmetric:
  fixes x :: "(real^2)^'n"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ i $ j
       = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j $ i"
  unfolding HessU_def
  by (rule mixed_partials_commute[OF open_UNIV UNIV_I U_dip_Ck2])

text \<open>\<^bold>\<open>Degenerate critical point \<open>\<Longrightarrow>\<close> the gradient vanishes and \<open>det (\<nabla>\<^sup>2U) = 0\<close>.\<close>  Combining
  @{thm Phibad_zero_iff} (whose third slot is \<open>H\<^sub>1\<^sub>1H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2\<close>) with @{thm det_2} and the
  Hessian symmetry @{thm HessU_dip_symmetric}, \<open>\<Phi> = 0\<close> rewrites exactly to \<open>\<nabla>\<^sub>\<Omega>U = 0\<close> and
  \<open>det (\<nabla>\<^sup>2U) = 0\<close> --- the form the chart engine consumes (via @{thm
  not_surj_omega_deriv_iff_detHess_dip}).\<close>

lemma Phibad_dip_imp_detHess0:
  fixes x :: "(real^2)^'n"
  assumes "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
       \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
proof -
  from assms have conj:
    "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
     \<and> HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
         * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
       = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2)\<^sup>2"
    using Phibad_zero_iff by blast
  hence g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
  from conj have hh:
    "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
       * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
     = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2)\<^sup>2" by blast
  have sym: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
           = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
    by (rule HessU_dip_symmetric)
  have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
        = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
            * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
          - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
            * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
    by (rule det_2)
  also have "\<dots> = 0" using hh sym by (simp add: power2_eq_square)
  finally show ?thesis using g0 by blast
qed

text \<open>\<^bold>\<open>The dipole bad set sits inside the chart engine's critical-projection set.\<close>  Putting
  the two reductions together: at any \<open>\<omega>\<close> witnessing \<open>\<Phi> = 0\<close> the gradient \<open>G = \<nabla>\<^sub>\<Omega>U\<close>
  vanishes (@{thm Phibad_dip_imp_detHess0}) \<^emph>\<open>and\<close> its \<open>\<omega>\<close>-derivative has no surjective branch
  (@{thm not_surj_omega_deriv_iff_detHess_dip}, \<open>\<Omega> = UNIV\<close>).  Hence the degenerate-critical
  configuration set --- even with the extra \<open>A \<noteq> 0\<close> restriction --- is contained in the
  exact set whose meagerness @{thm parametric_transversality_meager_euclidean_stub} delivers
  from \<open>regular_value_on G\<close>.  This is the structural half of \<open>Phi_bad_meager\<close>; what remains is
  the transversality input \<open>regular_value_on\<close> and the \<open>(real^2)^'n \<cong> real^(2\<cdot>'n)\<close> reshape.\<close>

lemma Phibad_dip_subset_critical:
  fixes V :: "(planar^'n) set"
  shows "{x \<in> V. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0}
       \<subseteq> {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> \<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                        (at \<omega>) \<and> surj D)}"
proof
  fix x assume "x \<in> {x \<in> V. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                            \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0}"
  then obtain \<omega> where xV: "x \<in> V"
    and pb: "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
  from Phibad_dip_imp_detHess0[OF pb]
  have g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    and d0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" by blast+
  have "\<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
              (at \<omega> within UNIV) \<and> surj D)"
    using not_surj_omega_deriv_iff_detHess_dip[OF open_UNIV UNIV_I] d0 by blast
  hence nd: "\<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                   (at \<omega>) \<and> surj D)" by simp
  from xV g0 nd
  show "x \<in> {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> \<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                        (at \<omega>) \<and> surj D)}" by blast
qed

text \<open>\<^bold>\<open>OBLIGATION (the determinant's payoff).\<close>  The set of feasible configurations carrying
  a degenerate critical point with \<open>A \<noteq> 0\<close> is meager.  This is \<open>prop:dimZ\<close>(1): \<open>lem:Msurj\<close>
  (the \<open>12\<times>12\<close> \<open>bigJ_det \<noteq> 0\<close>) \<open>\<Longrightarrow>\<close> \<open>Z\<^sub>reg\<close> is codim-3 \<open>\<Longrightarrow>\<close> its projection is meager.  This is the
  exact point at which the proven determinants enter, and it is the consumer the
  appendix's \<open>Bregnonzero\<close> meagerness reduces to.\<close>

text \<open>\<^bold>\<open>(B1) Meagerness transfers across a linear homeomorphism.\<close>  Generic, reusable: under a
  linear homeomorphism \<open>f\<close> of the whole space, \<open>f ` S\<close> is meager iff \<open>S\<close> is.  This is the engine
  for moving between the dipole configuration space \<open>(\<real>\<^sup>2)^'n\<close> and the flat \<open>\<real>\<^sup>m\<close> the
  Euclidean transversality stub is typed for.\<close>

lemma nowhere_dense_homeo_image:
  fixes h :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes H: "homeomorphism UNIV UNIV h k" and nd: "nowhere_dense E"
  shows "nowhere_dense (h ` E)"
proof -
  have ch: "continuous_on UNIV h" by (rule homeomorphism_cont1[OF H])
  have hk: "\<And>x. h (k x) = x" by (rule homeomorphism_apply2[OF H UNIV_I])
  have kh: "\<And>x. k (h x) = x" by (rule homeomorphism_apply1[OF H UNIV_I])
  have sub1: "h ` closure E \<subseteq> closure (h ` E)"
    by (rule image_closure_subset[OF _ closed_closure closure_subset])
       (rule continuous_on_subset[OF ch subset_UNIV])
  have clc: "closed (h ` closure E)"
  proof -
    have "closedin (top_of_set UNIV) (h ` closure E)"
      by (rule homeomorphism_imp_closed_map[OF H])
         (simp add: closed_closedin[symmetric])
    thus ?thesis
      using closedin_closed_trans by blast
  qed
  have sub2: "closure (h ` E) \<subseteq> h ` closure E"
    by (rule closure_minimal[OF image_mono[OF closure_subset] clc])
  have cleq: "closure (h ` E) = h ` closure E" using sub1 sub2 by blast
  have intsub: "interior (h ` closure E) \<subseteq> h ` interior (closure E)"
  proof (rule subsetI)
    fix y assume y: "y \<in> interior (h ` closure E)"
    have oin: "openin (top_of_set UNIV) (interior (h ` closure E))"
      by simp
    have "openin (top_of_set UNIV) (k ` interior (h ` closure E))"
      by (meson H homeomorphism_imp_open_map homeomorphism_sym oin)
    hence kopen: "open (k ` interior (h ` closure E))"
      by simp
    have ksub: "k ` interior (h ` closure E) \<subseteq> closure E"
    proof -
      have "k ` interior (h ` closure E) \<subseteq> k ` (h ` closure E)"
        by (rule image_mono[OF interior_subset])
      also have "k ` (h ` closure E) = closure E" by (simp add: image_image kh)
      finally show ?thesis .
    qed
    have "k ` interior (h ` closure E) \<subseteq> interior (closure E)"
      by (rule interior_maximal[OF ksub kopen])
    hence "k y \<in> interior (closure E)" using y by auto
    hence "h (k y) \<in> h ` interior (closure E)" by (rule imageI)
    thus "y \<in> h ` interior (closure E)" by (simp add: hk)
  qed
  have "interior (h ` closure E) = {}"
    using intsub nd by (simp add: nowhere_dense_def)
  thus ?thesis using cleq by (simp add: nowhere_dense_def)
qed

lemma meager_homeo_image:
  fixes h :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes H: "homeomorphism UNIV UNIV h k" and mA: "meager A"
  shows "meager (h ` A)"
proof -
  from mA obtain E :: "nat \<Rightarrow> 'a set"
    where cov: "A \<subseteq> (\<Union>n. E n)" and nd: "\<forall>n. nowhere_dense (E n)"
    unfolding meager_def by blast
  have "h ` A \<subseteq> (\<Union>n. h ` E n)" using cov by force
  moreover have "\<forall>n. nowhere_dense (h ` E n)"
    using nd nowhere_dense_homeo_image[OF H] by blast
  ultimately show ?thesis unfolding meager_def by blast
qed

lemma meager_linear_homeo_iff:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "linear f" and homeo: "homeomorphism UNIV UNIV f g"
  shows "meager (f ` S) \<longleftrightarrow> meager S"
proof
  assume "meager S"
  thus "meager (f ` S)" by (rule meager_homeo_image[OF homeo])
next
  assume "meager (f ` S)"
  hence "meager (g ` (f ` S))"
    using assms(2) homeomorphism_symD meager_homeo_image by blast
  moreover have "g ` (f ` S) = S"
    using homeomorphism_apply1[OF homeo UNIV_I] by (simp add: image_image)
  ultimately show "meager S" by simp
qed

text \<open>\<^bold>\<open>(B2) The transversality engine in our ACTUAL configuration type --- with the \<open>C\<^sup>1\<close>
  hypothesis made explicit.\<close>  This is the Euclidean transversality result restated with the
  configuration space \<open>(\<real>\<^sup>2)^'n\<close> (rather than the flat \<open>\<real>\<^sup>m\<close>); its proof reshapes via @{thm
  meager_linear_homeo_iff} and the \<^emph>\<open>sound\<close> chart-assembly lemmas (\<open>regular_zero_set_projection_
  local_chart_2d\<close>, \<open>countable_chart_cover_of_levelset_2d\<close>, \<open>meager_critical_values_from_charts\<close>).
  \<^bold>\<open>SOUNDNESS FIX:\<close> it carries the \<open>C\<^sup>1\<close> hypotheses \<open>derG\<close>/\<open>contG'\<close> (a continuous blinfun derivative
  field) that the local-chart step genuinely requires --- the existing Euclidean \<^emph>\<open>stub\<close>
  (\<open>regular_value_on\<close> only) is understated and its \<open>sorry\<close> core is not provable without this.  The
  hypothesis is supplied for our \<open>G = \<nabla>\<^sub>\<Omega>U\<close> by @{thm gradU_dip_joint_C1}.\<close>

lemma parametric_transversality_meager_planar_config:
  fixes V :: "((real^2)^'n) set"
    and \<Omega> :: "(real^2) set"
    and G :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> (real^2)"
    and G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
  assumes "open V" and "V \<noteq> {}" and "open \<Omega>"
    and derG: "\<And>z. z \<in> V \<times> \<Omega> \<Longrightarrow> (G has_derivative blinfun_apply (G' z)) (at z)"
    and contG': "continuous_on (V \<times> \<Omega>) G'"
    and "regular_value_on G (V \<times> \<Omega>) 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>\<Omega>. G (x, \<omega>) = 0
            \<and> \<not> (\<exists>D. ((\<lambda>u. G (x, u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D)}"
  sorry


text \<open>\<^bold>\<open>=== The genuinely-complete dipole meagerness scaffold (statements only) ===\<close>

  The generic \<open>Phi_bad_meager\<close> above is \<^emph>\<open>not provable\<close> as stated (it has no smoothness of \<open>cvec\<close>/
  \<open>gain\<close> in \<open>\<omega>\<close>), so the capstone uses the \<^bold>\<open>dipole-specific\<close> \<open>Phi_bad_meager_dip\<close> below.  Proving
  it requires a \<^bold>\<open>three-stratum decomposition\<close> --- because the regular value @{thm
  regular_value_on_gradU_dip} only holds where the moment map is a submersion \<^bold>\<open>and\<close> the steering
  map is an immersion.  The two non-regular strata (\<open>\<not> surj (DM_paper_x \<dots>)\<close> and \<open>det (Dcvec) = 0\<close>)
  are positive-codimension and meager by their own arguments.  This mirrors the paper's
  \<open>prop:dimZ\<close>/\<open>prop_regnonzero\<close> stratification (where the strata meagerness are themselves the deep
  branch obligations).\<close>

text \<open>\<^bold>\<open>(M1) A regular configuration exists at any nonzero wavevector.\<close>  The moment-map submersion
  machinery (\<open>m_star\<close>, \<open>surj_iff_m_star\<close>) is proven only at the fixed \<open>c0_paper = (1,0)\<close>, \<open>CARD = 6\<close>.
  This generalises the ``one regular point'' to an arbitrary nonzero steered wavevector and any
  \<open>CARD('n) \<ge> 6\<close>.\<close>

lemma DM_paper_x_regular_point_exists:
  fixes c :: planar
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x0::(real^2)^'n. surj (DM_paper_x x0 c)"
  sorry

text \<open>\<^bold>\<open>(M2) Open-dense submersion at a fixed nonzero wavevector.\<close>  From one regular point (M1) plus
  lower semicontinuity of rank (\<open>rank_lower_semicont_open_dense_propagation\<close>, currently a \<open>sorry\<close> in
  \<open>Nonemptiness_Paper\<close>), the moment-map derivative is surjective on an open dense subset of any open
  \<open>V\<close>.  This is the general-wavevector analogue of \<open>DM_paper_open_dense_surjective\<close>.\<close>

lemma DM_paper_x_open_dense_surjective_gen:
  fixes V :: "((real^2)^'n) set" and c :: planar
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)" and "c \<noteq> 0"
  shows "\<exists>U. open U \<and> U \<subseteq> V \<and> V \<subseteq> closure U \<and> (\<forall>x\<in>U. surj (DM_paper_x x c))"
  sorry

text \<open>\<^bold>\<open>(M3) The steering-singular angle locus is nowhere dense.\<close>  \<open>Dcvec_dip\<close> is real-analytic in
  \<open>\<omega>\<close> and not everywhere singular, so its singular set is a proper analytic subset --- closed with
  empty interior.\<close>

lemma Dcvec_det_eq:
    fixes \<omega>0 \<omega>s \<omega> :: "real^2"
    shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
           = sin (\<omega>$1) * (cos (\<omega>$1)
               - sin (\<omega>$1) * (((kx \<omega>0 - kx
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * cos (\<omega>$2)
                            + ((ky \<omega>0 - ky \<omega>s)/(kz
  \<omega>s - kz \<omega>0)) * sin (\<omega>$2)))"
proof -
  have "cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (cos (\<omega> $h 2) * cos (\<omega> $h 2))) + 
           (cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (sin (\<omega> $h 2) * sin (\<omega> $h 2))) + 
           ((kx \<omega>0 * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2))) - 
             kx \<omega>s * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2)))) / 
            (kz \<omega>s - kz \<omega>0) + (kx \<omega>s * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2))) - 
             kx \<omega>0 * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2)))) / (kz \<omega>s - kz \<omega>0))) =
       cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (cos (\<omega> $h 2) * cos (\<omega> $h 2) + sin (\<omega> $h 2) * sin (\<omega> $h 2)))"
    by argo
  then show ?thesis
    by (simp add: det_2 matrix_def Dcvec_dip_def axis_def sin_cos_squared_add[of "\<omega>$2"]
  algebra_simps)
qed

lemma pythagorean_squared:
  fixes m :: real
  shows
    "cos m * (cos m * (cos m * cos m))
      + (sin m * (sin m * (sin m * sin m))
      + cos m * (cos m * (sin m * (sin m * 2)))) = 1"
proof -
  let ?c = "cos m"
  let ?s = "sin m"

  have cs: "?c * ?c + ?s * ?s = 1"
    using sin_cos_squared_add[of m]
    by (simp add: power2_eq_square add.commute)

  have
    "?c * (?c * (?c * ?c))
      + (?s * (?s * (?s * ?s))
      + ?c * (?c * (?s * (?s * 2))))
     = (?c * ?c + ?s * ?s) * (?c * ?c + ?s * ?s)"
    by (smt (verit, del_insts) Groups.mult_ac(2) ab_semigroup_mult_class.mult_ac(1) 
        mult_2 mult_hom.hom_add)
  also have "... = 1"
    using cs by simp
  finally show ?thesis.
qed

lemma sin_cos_lin_not_const0:
    fixes M a b :: real
    assumes ab: "a < b"
    shows "\<exists>s. a < s \<and> s < b \<and> sin s * (cos s -
  sin s * M) \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence Z: "\<And>s. a < s \<Longrightarrow> s < b
  \<Longrightarrow> sin s * (cos s - sin s * M) = 0" by auto
    define F  where "F  = (\<lambda>s::real. sin s * (cos s - sin s
  * M))"
    define F1 where "F1 = (\<lambda>s::real. (cos s * cos s - sin s
  * sin s) - M * (2 * sin s * cos s))"
    define F2 where "F2 = (\<lambda>s::real. - (4 * (sin s * cos
  s)) - M * (2 * (cos s * cos s - sin s * sin s)))"
    have FZ:  "F s = 0" if "a < s" "s < b" for s using Z[OF that]
  by (simp add: F_def)
    have dF:  "(F  has_real_derivative F1 s) (at s)" for s
      unfolding F_def F1_def by (auto intro!: derivative_eq_intros
  simp: algebra_simps)
    have dF1: "(F1 has_real_derivative F2 s) (at s)" for s
      unfolding F1_def F2_def by (auto intro!: derivative_eq_intros
  simp: algebra_simps)
    have F1Z: "F1 s = 0" if "a < s" "s < b" for s
    proof -
      have "(F has_real_derivative 0) (at s)"
      proof (rule has_field_derivative_transform_within_open[where
  f = "\<lambda>_. 0" and S = "{a<..<b}"])
        show "((\<lambda>_. 0::real) has_real_derivative 0) (at s)"
  by (rule DERIV_const)
        show "open {a<..<b}" by simp
        show "s \<in> {a<..<b}" using that by simp
        show "\<And>y. y \<in> {a<..<b} \<Longrightarrow> (0::real) = F y" 
          using FZ by simp
      qed   
      with dF[of s] show "F1 s = 0" by (metis DERIV_unique)
    qed
    define m where "m = (a + b) / 2"
    have m_mem: "m \<in> {a<..<b}" using ab by (simp add: m_def)
    have e1: "F1 m = 0" using F1Z m_mem by simp
    have "(F1 has_real_derivative 0) (at m)"
    proof (rule has_field_derivative_transform_within_open[where f
  = "\<lambda>_. 0" and S = "{a<..<b}"])
      show "((\<lambda>_. 0::real) has_real_derivative 0) (at m)"
        by (rule DERIV_const)
      show "open {a<..<b}" by simp
      show "m \<in> {a<..<b}" using m_mem by simp
      show "\<And>y. y \<in> {a<..<b} \<Longrightarrow> (0::real) =  F1 y" using F1Z by simp
    qed
    with dF1[of m] have e2: "F2 m = 0" by (metis DERIV_unique)
    define X where "X = cos m * cos m - sin m * sin m"
    define Y where "Y = 2 * sin m * cos m"
    have pyth: "X * X + Y * Y = 1" 
      using sin_cos_squared_add[of m] using pythagorean_squared
      by (simp add: X_def Y_def power2_eq_square algebra_simps)
    have eq1: "X - M * Y = 0" using e1 by (simp add: F1_def X_def
  Y_def)
    have eq2: "Y + M * X = 0" using e2 by (simp add: F2_def X_def
  Y_def algebra_simps)
    have "(1 + M * M) * X = 0" 
      using eq1 eq2 by (smt (verit, del_insts) mult_not_zero zero_le_mult_iff)
    hence "X = 0"
      by (metis more_arith_simps(6) mult_eq_0_iff sum_squares_eq_zero_iff) 
    moreover from this eq2 have "Y = 0" by simp
    ultimately show False using pyth by simp
  qed


lemma steering_singular_nowhere_dense:
    shows "nowhere_dense {\<omega>::angle. det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  proof -   
    define g where "g = (\<lambda>u::real. ((kx \<omega>0 - kx
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * cos u
                                   + ((ky \<omega>0 - ky
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * sin u)"
    define f where "f = (\<lambda>\<omega>::real^2. sin
  (\<omega>$1) * (cos (\<omega>$1) - sin (\<omega>$1) * g
  (\<omega>$2)))"
    have feq: "{\<omega>::angle. det (matrix (Dcvec_dip \<omega>0
  \<omega>s \<omega>)) = 0} = {\<omega>. f \<omega> = 0}"
      by (simp add: f_def g_def Dcvec_det_eq)
    have contf: "continuous_on UNIV f"
      unfolding f_def g_def
      by (intro continuous_intros bounded_linear.continuous_on[OF bounded_linear_vec_nth])
    have closedE: "closed {\<omega>::real^2. f \<omega> = 0}"
      by (rule closed_Collect_eq[OF contf continuous_on_const])
    have intE: "interior {\<omega>::real^2. f \<omega> = 0} = {}"
    proof (rule ccontr)
      assume "interior {\<omega>. f \<omega> = 0} \<noteq> {}"
      then obtain c where "c \<in> interior {\<omega>. f \<omega> =
  0}" by blast
      then obtain r where r: "0 < r" and bsub: "ball c r  \<subseteq> {\<omega>. f \<omega> = 0}"
        using mem_interior by blast
      have inb: "sin s * (cos s - sin s * g (c$2)) = 0" if hs:
  "\<bar>s - c$1\<bar> < r" for s
      proof -
        have "vector [s, c$2] - c = axis 1 (s - c$1)"
          by (simp add: vec_eq_iff forall_2 vector_2 axis_def,
              smt (verit, del_insts) Finite_Cartesian_Product.minus_vec_def 
              exhaust_2 vec_lambda_unique vector_2(1,2) verit_minus_simplify(1))
        hence "dist (vector [s, c$2] :: real^2) c = \<bar>s -  c$1\<bar>"
          by (simp add: dist_norm norm_eq_sqrt_inner inner_axis_axis)
        hence "vector [s, c$2] \<in> ball c r" using hs by (simp add: dist_commute)
        hence "f (vector [s, c$2]) = 0" using bsub by blast
        thus ?thesis by (simp add: f_def vector_2)
      qed
      have lt: "c$1 - r < c$1 + r" using r by simp
      obtain s where "c$1 - r < s" "s < c$1 + r" "sin s * (cos s - sin s * g (c$2)) \<noteq> 0"
        using sin_cos_lin_not_const0[where M = "g (c$2)" and a = "c$1 - r" and b = "c$1 + r"] lt 
        by blast
      moreover from this have "\<bar>s - c$1\<bar> < r" by simp
      ultimately show False using inb by blast
    qed
    show ?thesis
      using closedE intE by (simp add: feq nowhere_dense_def closure_closed)
  qed

text \<open>\<^bold>\<open>(M4) Regular stratum is meager.\<close>  On the open locus where \<open>A \<noteq> 0\<close>, \<open>surj (DM_paper_x \<dots>)\<close>,
  and \<open>det (Dcvec) \<noteq> 0\<close>, \<open>0\<close> is a regular value (@{thm regular_value_on_gradU_dip}); covering this
  open (non-product) locus by countably many product boxes and applying
  @{thm parametric_transversality_meager_planar_config} on each, the degenerate-critical projection
  over the regular stratum is meager.\<close>

lemma meager_bad_regular_stratum:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  sorry

text \<open>\<^bold>\<open>(M5) Rank-deficient stratum is meager.\<close>  The set of configurations carrying a degenerate
  critical point (with \<open>A \<noteq> 0\<close>) at an angle where the moment map \<^emph>\<open>fails\<close> to be a submersion.  This
  is the projection of a positive-codimension set; meager by the \<open>m_star = 0\<close> nowhere-density (M2)
  combined with a parametric argument over \<open>\<omega>\<close>.\<close>

lemma meager_rank_deficient_stratum:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  sorry

text \<open>\<^bold>\<open>(M6) Steering-singular stratum is meager.\<close>  Degenerate critical points (with \<open>A \<noteq> 0\<close>) at an
  angle where the steering Jacobian is singular.  Meager by (M3): the singular-\<open>\<omega>\<close> locus is
  nowhere dense, and the critical points over it form a positive-codimension set.\<close>

lemma meager_steering_singular_stratum:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  sorry

text \<open>\<^bold>\<open>(M6b) The \<open>A = 0\<close> degenerate stratum is meager --- ADDED (soundness).\<close>  The bad set in
  M4--M6 carries \<open>A \<noteq> 0\<close> (the transversality argument needs it).  But every array-factor null
  \<open>A_cart = 0\<close> is itself a critical point (\<open>\<nabla>\<^sub>\<Omega>U = g \<nabla>\<bar>A\<bar>\<^sup>2 + \<bar>A\<bar>\<^sup>2 \<nabla>g = 0\<close> at \<open>A = 0\<close>), so a
  \<^emph>\<open>degenerate\<close> null also breaks regularity and must be excluded.  The locus \<open>{A = 0 \<and> det \<nabla>\<^sup>2U = 0}\<close>
  is \<open>3\<close> real conditions on \<open>(\<bm>x,\<omega>)\<close> (codim \<open>3\<close>): its \<open>\<bm>x\<close>-projection is meager.\<close>

lemma meager_Azero_degenerate_stratum:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
  sorry

text \<open>\<^bold>\<open>(M7) The dipole-specific bad set is meager --- CORRECTED to the FULL set.\<close>  By @{thm
  Phibad_dip_imp_detHess0}, \<open>\<Phi> = 0\<close> gives \<open>\<nabla>\<^sub>\<Omega>U = 0 \<and> det (\<nabla>\<^sup>2U) = 0\<close>; then every witnessing \<open>\<omega>\<close> falls
  into exactly one of \<^bold>\<open>four\<close> strata --- regular (M4), rank-deficient (M5), steering-singular (M6),
  or array-null \<open>A = 0\<close> (M6b) --- whose union is meager.  \<^bold>\<open>SOUNDNESS FIX:\<close> the conclusion is now the
  \<^bold>\<open>full\<close> degenerate-critical set \<open>{\<exists>\<omega>. \<Phi> = 0}\<close> (no spurious \<open>A \<noteq> 0\<close>), so its complement gives a point
  with \<^emph>\<open>no\<close> degenerate critical at any \<open>\<omega>\<close> --- what the capstone actually needs.  \<^bold>\<open>This is the lemma
  the capstone consumes\<close>, in place of the unprovable generic \<open>Phi_bad_meager\<close>.\<close>

lemma Phi_bad_meager_dip:
  fixes V :: "((real^2)^'n) set"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
proof -
  let ?reg = "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  let ?def = "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  let ?steer = "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  let ?null = "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
  have meag4: "meager (?reg \<union> ?def \<union> ?steer \<union> ?null)"
    by (intro meager_Un meager_bad_regular_stratum[OF assms]
              meager_rank_deficient_stratum[OF assms]
              meager_steering_singular_stratum[OF assms]
              meager_Azero_degenerate_stratum[OF assms])
  have sub: "{x \<in> V. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}
             \<subseteq> ?reg \<union> ?def \<union> ?steer \<union> ?null"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    then obtain \<omega> where xV: "x \<in> V"
      and pb: "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    from Phibad_dip_imp_detHess0[OF pb]
    have g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and d0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" by blast+
    show "x \<in> ?reg \<union> ?def \<union> ?steer \<union> ?null"
      using xV g0 d0
      by fastforce 
  qed
  show ?thesis by (rule meager_subset[OF sub meag4])
qed


subsection \<open>The capstone: \<open>\<F>\<^sub>0\<close> is nonempty for appropriately chosen \<open>\<xi>, \<kappa>, \<epsilon>\<close>\<close>

text \<open>TeX Lemma~\eqref{F0} (D_edit_May18, the 2-D version, L1288/F0\_nonempty\_proof\_2D):
  for appropriately chosen \<open>\<xi>,\<kappa>,\<epsilon> > 0\<close>, \<open>\<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = \<F> \<inter> X\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close> is nonempty.

  \<^bold>\<open>No regularity is assumed.\<close>  The analytic input --- a feasible \<open>x\<^sub>0\<close> whose pattern is
  \<^emph>\<open>regular\<close> (\<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> on the \<open>\<epsilon>\<close>-sphere, and \<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> or \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> on \<open>\<Omega>\<^sup>~\<close>) ---
  is a \<^emph>\<open>consequence\<close> of \<open>Phi_bad_meager\<close> + Baire (the degenerate configurations are
  meager, so their complement inside the open interior of the feasible body is dense and
  in particular nonempty), packaged for the actual pattern as the obligation
  \<open>regular_feasible_point_dip\<close> below.  This is precisely what the determinant computation was
  for.  Given that point, the margins \<open>\<kappa> = min\<^bsub>\<partial>B\<^sub>\<epsilon>\<^esub>\<parallel>\<nabla>\<^sub>\<Omega>U\<parallel>\<close> and
  \<open>\<xi> = min\<^bsub>\<Omega>\<^sup>~\<^esub>(\<parallel>\<nabla>\<^sub>\<Omega>U\<parallel> + \<sigma>\<^sub>m\<^sub>i\<^sub>n(H))\<close> are positive by Weierstrass, and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.
  We split the analytic core (\<open>F0_nonempty_of_witness\<close>) from the witness, so the concrete
  dipole capstone \<open>F0_dip_nonempty\<close> discharges the \<^emph>\<open>continuity\<close> half from proven facts and
  leaves only the genuine existence-of-a-regular-feasible-point hole.\<close>

lemma mem_imp_ne_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}" by blast

text \<open>\<^bold>\<open>The capstone core, parametrised by the regular feasible witness.\<close>  Given a feasible
  \<open>x\<^sub>0\<close> and radius \<open>\<epsilon>>0\<close> whose pattern is regular --- gradient nonvanishing on the
  \<open>\<epsilon>\<close>-sphere, gradient-or-nondegenerate on the annulus, with the relevant norms continuous
  --- the positive margins \<open>\<kappa>,\<xi>\<close> exist by Weierstrass and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.  This is the
  purely analytic half of \<open>F0_nonempty\<close>; the witness itself (the determinant/Baire payoff)
  is the separate obligation.  Isolating it lets the \<^emph>\<open>concrete dipole\<close> capstone discharge
  the continuity conjuncts from the proven @{thm norm_gradU_dip_continuous_on} /
  @{thm sigma_min_HessU_dip_continuous_on}, rather than assuming them.\<close>

lemma F0_nonempty_of_witness:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real"
    and R dmin A B D \<delta>null pmin :: real and \<omega>null ctr :: planar
    and x0 :: "planar^'n" and \<epsilon> :: real
  assumes \<epsilon>0: "0 < \<epsilon>"
    and feas: "x0 \<in> Ffeas cvec g R dmin A B D \<omega>null ctr \<delta>null pmin"
    and cdN: "continuous_on (sphere ctr \<epsilon>) (\<lambda>\<omega>. norm (gradU cvec g x0 \<omega>))"
    and cdsum: "continuous_on (Omega ctr - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
    and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU cvec g x0 \<omega> \<noteq> 0"
    and rO: "\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                gradU cvec g x0 y \<noteq> 0 \<or> 0 < sigma_min (HessU cvec g x0 y)"
  shows "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
            \<and> F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>
                \<noteq> ({}::(planar^'n) set)"
proof -
  \<comment> \<open>the positive \<open>\<kappa>\<close>-margin on the \<open>\<epsilon>\<close>-sphere (Weierstrass)\<close>
  have sph_ne: "sphere ctr \<epsilon> \<noteq> {}"
  proof -
    have "dist (ctr + \<epsilon> *\<^sub>R axis (1::2) 1) ctr = \<epsilon>"
      using \<epsilon>0 by (simp add: dist_norm abs_of_pos)
    hence "ctr + \<epsilon> *\<^sub>R axis (1::2) 1 \<in> sphere ctr \<epsilon>"
      by (simp add: dist_commute)
    thus ?thesis by blast
  qed
  obtain \<omega>m where \<omega>m: "\<omega>m \<in> sphere ctr \<epsilon>"
      and \<omega>min: "\<forall>\<omega>\<in>sphere ctr \<epsilon>.
                    norm (gradU cvec g x0 \<omega>m) \<le> norm (gradU cvec g x0 \<omega>)"
    using continuous_attains_inf[OF compact_sphere sph_ne cdN] by blast
  define \<kappa> where "\<kappa> = norm (gradU cvec g x0 \<omega>m)"
  have \<kappa>pos: "0 < \<kappa>" using bspec[OF rsph \<omega>m] unfolding \<kappa>_def by simp
  have inXrob: "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>"
    using \<omega>min unfolding Xrobust_def \<kappa>_def by simp
  \<comment> \<open>the positive \<open>\<xi>\<close>-margin on \<open>\<Omega>\<^sup>~\<close> (vacuous if \<open>\<Omega>\<^sup>~ = \<emptyset>\<close>)\<close>
  show ?thesis
  proof (cases "Omega ctr - ball ctr \<epsilon> = {}")
    case True
    have "x0 \<in> X0 cvec g ctr (Omega ctr) 1 \<kappa> \<epsilon>"
      using inXrob True unfolding X0_def by blast
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin 1 \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin 1 \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    moreover have "(0::real) < 1" by simp
    ultimately show ?thesis using \<kappa>pos \<epsilon>0 by blast
  next
    case False
    obtain ym where ym: "ym \<in> Omega ctr - ball ctr \<epsilon>"
        and ymin: "\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
              norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)
              \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y)"
      using continuous_attains_inf[OF Omega_minus_ball_compact False cdsum] by blast
    define \<xi> where "\<xi> = norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)"
    have \<xi>pos: "0 < \<xi>"
    proof (cases "gradU cvec g x0 ym = 0")
      case True
      with bspec[OF rO ym] have "0 < sigma_min (HessU cvec g x0 ym)" by simp
      thus ?thesis unfolding \<xi>_def
        using norm_ge_zero[of "gradU cvec g x0 ym"] by linarith
    next
      case False
      hence "0 < norm (gradU cvec g x0 ym)" by simp
      thus ?thesis unfolding \<xi>_def
        using sigma_min_nonneg[of "HessU cvec g x0 ym"] by linarith
    qed
    have "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>
          \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                \<xi> \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
      using inXrob ymin unfolding \<xi>_def by blast
    hence "x0 \<in> X0 cvec g ctr (Omega ctr) \<xi> \<kappa> \<epsilon>" unfolding X0_def by simp
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    thus ?thesis using \<xi>pos \<kappa>pos \<epsilon>0 by blast
  qed
qed

subsection \<open>The capstone for the ACTUAL dipole pattern \<open>U_dip\<close>\<close>

text \<open>\<^bold>\<open>The genuine remaining obligation, for the actual function.\<close>  Specialised to the
  concrete steered dipole \<open>cvec = cvec\<^sub>dip \<omega>\<^sub>0 \<omega>\<^sub>s\<close>, \<open>g = gain\<^sub>dip\<close>: there is a feasible
  configuration \<open>x\<^sub>0\<close> and radius \<open>\<epsilon>>0\<close> whose pattern is regular (gradient nonvanishing on
  \<open>\<partial>B\<^sub>\<epsilon>\<close>, gradient-or-nondegenerate on \<open>\<Omega>\<^sup>~\<close>).  This is \<^emph>\<open>exactly\<close> the determinant/Baire
  payoff (degenerate configs meager, @{thm Phi_bad_meager_dip} + Baire inside the feasible
  interior); crucially the \<^emph>\<open>continuity\<close> half is no longer part of this hole --- it is
  discharged below from the proven dipole facts.\<close>

text \<open>\<^bold>\<open>The Baire scaffold for \<open>regular_feasible_point_dip\<close> (\<^bold>\<open>statements only\<close>; proofs deferred).\<close>\<close>

text \<open>\<^bold>\<open>(C0) A nonzero smallest singular value is exactly invertibility.\<close>  For a real \<open>2\<times>2\<close>
  matrix the smallest singular value @{const sigma_min} is positive iff the determinant is
  nonzero --- the bridge between the degeneracy slot \<open>det (\<nabla>\<^sup>2U) = 0\<close> and the capstone's
  \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> nondegeneracy margin.\<close>

lemma sigma_min_pos_iff_invertible:
  fixes H :: "real^2^2"
  shows "0 < sigma_min H \<longleftrightarrow> det H \<noteq> 0"
proof -
  have lin: "linear ((*v) H)" by (rule matrix_vector_mul_linear)
  have bdd: "bdd_below ((\<lambda>v. norm (H *v v)) ` sphere 0 1)"
    by (rule bdd_belowI[of _ 0]) auto
  have cont: "continuous_on (sphere (0::real^2) 1) (\<lambda>v. norm (H *v v))"
    by (rule continuous_on_norm[OF
          bounded_linear.continuous_on[OF matrix_vector_mul_bounded_linear continuous_on_id]])
  \<comment> \<open>Step 1: positivity of the smallest singular value \<open>\<longleftrightarrow>\<close> nonvanishing on the unit sphere.\<close>
  have nz_iff: "0 < sigma_min H \<longleftrightarrow> (\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0)"
  proof
    assume pos: "0 < sigma_min H"
    show "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    proof
      fix v assume v: "v \<in> sphere (0::real^2) 1"
      have "sigma_min H \<le> norm (H *v v)"
        unfolding sigma_min_def by (rule cINF_lower[OF bdd v])
      with pos show "H *v v \<noteq> 0" by auto
    qed
  next
    assume nz: "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    obtain v0 where v0: "v0 \<in> sphere (0::real^2) 1"
        and v0min: "\<forall>v\<in>sphere (0::real^2) 1. norm (H *v v0) \<le> norm (H *v v)"
      using continuous_attains_inf[OF compact_sphere sphere01_ne cont] by blast
    have "sigma_min H = norm (H *v v0)"
    proof -
      have "sigma_min H \<le> norm (H *v v0)"
        unfolding sigma_min_def by (rule cINF_lower[OF bdd v0])
      moreover have "norm (H *v v0) \<le> sigma_min H"
        unfolding sigma_min_def by (rule cINF_greatest[OF sphere01_ne]) (rule v0min[rule_format])
      ultimately show ?thesis by linarith
    qed
    moreover have "0 < norm (H *v v0)" using nz v0 by auto
    ultimately show "0 < sigma_min H" by simp
  qed
  \<comment> \<open>Step 2: nonvanishing on the unit sphere \<open>\<longleftrightarrow>\<close> injectivity (normalise an arbitrary nonzero
      kernel vector to the sphere).\<close>
  have inj_iff: "(\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0) \<longleftrightarrow> inj ((*v) H)"
  proof
    assume nz: "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    show "inj ((*v) H)"
    proof (rule injI)
      fix a b assume eq: "H *v a = H *v b"
      have z: "H *v (a - b) = 0"
        using eq by (simp add: matrix_vector_mult_diff_distrib)
      show "a = b"
      proof (rule ccontr)
        assume "a \<noteq> b"
        hence ab: "a - b \<noteq> 0" by simp
        define u where "u = inverse (norm (a - b)) *\<^sub>R (a - b)"
        have nu: "norm u = 1"
        proof -
          have "norm u = \<bar>inverse (norm (a - b))\<bar> * norm (a - b)"
            by (simp add: u_def)
          also have "\<dots> = inverse (norm (a - b)) * norm (a - b)" by simp
          also have "\<dots> = 1" using ab by simp
          finally show ?thesis .
        qed
        have "u \<in> sphere (0::real^2) 1" using nu by (simp add: dist_norm)
        moreover have "H *v u = 0"
          by (simp add: u_def matrix_vector_mult_scaleR z)
        ultimately show False using nz by auto
      qed
    qed
  next
    assume inj: "inj ((*v) H)"
    show "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    proof
      fix v assume v: "v \<in> sphere (0::real^2) 1"
      hence "v \<noteq> 0" by (auto simp: dist_norm)
      moreover have "H *v (0::real^2) = 0" by simp
      ultimately show "H *v v \<noteq> 0" using inj by (metis injD)
    qed
  qed
  \<comment> \<open>Step 3: injectivity of a square linear map \<open>\<longleftrightarrow>\<close> nonzero determinant.\<close>
  have det_iff: "inj ((*v) H) \<longleftrightarrow> det H \<noteq> 0"
    using det_nz_iff_inj[OF lin] by simp
  show ?thesis using nz_iff inj_iff det_iff by blast
qed

text \<open>\<^bold>\<open>(C1) The feasible body has nonempty interior (Slater).\<close>  If \<^emph>\<open>some\<close> configuration satisfies
  every constraint \<^emph>\<open>strictly\<close> --- all spacings exceed \<open>d\<^sub>min\<close>, the null power is below \<open>\<delta>\<^sub>null\<close>,
  the main power lies strictly between \<open>p\<^sub>min\<close> and the Cauchy--Schwarz cap, and \<open>\<parallel>\<bm>x\<parallel> < R\<close> --- then
  (each constraint function being continuous) that point is interior to @{const Ffeas}.  The
  hypothesis is the genuine strict-feasibility input; it does not mention \<open>interior\<close>.\<close>

lemma Ffeas_interior_nonempty:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes "\<exists>x::(real^2)^'n.
       (\<forall>p. fst p \<noteq> snd p \<longrightarrow> dmin < spdist A B D (x $ fst p) (x $ snd p))
     \<and> Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < \<delta>null
     \<and> pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr
     \<and> Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr < gain_dip ctr * (real CARD('n))\<^sup>2
     \<and> norm x < R"
  shows "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
proof -
  from assms obtain x :: "(real^2)^'n"
    where spac0: "\<forall>p. fst p \<noteq> snd p \<longrightarrow> dmin < spdist A B D (x $ fst p) (x $ snd p)"
      and Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < \<delta>null"
      and Pgt: "pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr"
      and nx: "norm x < R" by blast
  have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (x $ fst p) (x $ snd p)"
    using spac0 by blast
  have inR: "x \<in> ball 0 R" using nx by (simp add: dist_norm)
  obtain \<rho> where \<rho>: "0 < \<rho>"
      and sub: "ball x \<rho>
                \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
    using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
  have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
    by (rule interior_maximal[OF sub open_ball])
  moreover have "x \<in> ball x \<rho>" using \<rho> by simp
  ultimately show ?thesis by blast
qed

text \<open>\<^bold>\<open>(C2) Baire: a regular configuration exists inside the feasible interior.\<close>  The degenerate
  configurations are meager (@{thm Phi_bad_meager_dip}, the \<^bold>\<open>full\<close> bad set, including \<open>A = 0\<close>), so
  their complement is comeager, hence dense, hence meets the nonempty open feasible interior ---
  yielding a feasible \<open>x\<^sub>0\<close> carrying \<^bold>\<open>no\<close> degenerate critical point at \<^bold>\<open>any\<close> \<open>\<omega>\<close> (\<open>\<Phi> \<noteq> 0\<close> everywhere).
  \<^bold>\<open>SOUNDNESS FIX:\<close> the conclusion no longer carries the spurious \<open>A \<noteq> 0\<close> --- array-factor nulls
  (\<open>A = 0\<close>) are critical points (\<open>\<nabla>\<^sub>\<Omega>U = 0\<close>) too, and a \<^emph>\<open>degenerate\<close> null would break the
  capstone's regularity, so it must also be excluded.\<close>

lemma regular_config_exists:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
    and int_ne: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
  shows "\<exists>x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                          :: ((real^2)^'n) set).
            \<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
proof -
  define I where "I = interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: ((real^2)^'n) set)"
  have openI: "open I" unfolding I_def by (rule open_interior)
  have Ine: "I \<noteq> {}" unfolding I_def by (rule int_ne)
  have meagB: "meager {x \<in> I. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    by (rule Phi_bad_meager_dip[OF openI Ine c6])
  have "\<not> I \<subseteq> {x \<in> I. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
  proof
    assume sub: "I \<subseteq> {x \<in> I. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    have "meager I" by (rule meager_subset[OF sub meagB])
    moreover have "\<not> meager I" by (rule open_nonempty_not_meager[OF openI Ine])
    ultimately show False by simp
  qed
  then obtain x0 where x0I: "x0 \<in> I"
    and x0nB: "x0 \<notin> {x \<in> I. \<exists>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}" by blast
  have x0Iexp: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
    using x0I unfolding I_def by assumption
  have reg: "\<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
    using x0I x0nB by blast
  from x0Iexp reg
  have conjx0: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)
        \<and> (\<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)" by (rule conjI)
  \<comment> \<open>Composition fully established: \<open>x0Iexp\<close> (\<open>x0 \<in> interior\<close>) and \<open>reg\<close> (\<open>\<forall>\<omega>. \<Phi> \<noteq> 0\<close>) are the
      witness data.  Only the final \<^emph>\<open>bounded-existential introduction\<close> \<open>\<exists>x0\<in>interior. \<dots>\<close> with
      witness \<open>x0\<close> is left open --- a witness-instantiation tactic step (\<open>bexI\<close>/\<open>rule_tac x=x0\<close>)
      that needs live goal/type inspection to dispatch against the large \<open>interior (Ffeas \<dots>)\<close>
      term; it is mathematically immediate from \<open>x0Iexp\<close> and \<open>reg\<close>.\<close>
  show ?thesis
  proof (rule bexI[where x = x0])
    show "\<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0" by (rule reg)
  next
    show "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
      by (rule x0Iexp)
  qed
qed

text \<open>\<^bold>\<open>(C3) From ``no degenerate critical point'' to the sphere/annulus regularity.\<close>  If \<open>x\<^sub>0\<close> has
  no degenerate critical point in \<open>\<Omega>\<close> (at every \<open>\<omega>\<close>, either \<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> or \<open>det (\<nabla>\<^sup>2U) \<noteq> 0\<close>), then for
  a suitable radius \<open>\<epsilon> > 0\<close> the gradient is nonvanishing on the sphere \<open>\<partial>B\<^sub>\<epsilon>\<close> and
  gradient-or-nondegenerate on the annulus \<open>\<Omega> - B\<^sub>\<epsilon>\<close> --- exactly the conclusion shape of
  \<open>regular_feasible_point_dip\<close> below.  (Nondegenerate critical points are isolated, so \<open>\<epsilon>\<close> can dodge
  them; degeneracy \<open>det = 0\<close> is rephrased as \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n > 0\<close> via @{thm sigma_min_pos_iff_invertible}.)\<close>

lemma no_degenerate_to_sphere_annulus:
  fixes x0 :: "(real^2)^'n" and ctr \<omega>0 \<omega>s :: angle
  assumes "\<forall>\<omega>\<in>Omega ctr. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  shows "\<exists>\<epsilon>>0. (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
  sorry

lemma regular_feasible_point_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
    and feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: (planar^'n) set) \<noteq> {}"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
  \<comment> \<open>\<^bold>\<open>SOUNDNESS FIX:\<close> requires \<open>feasible\<close> (the feasible body has nonempty interior).  Without
      it the claim is false for infeasible parameters (e.g.\ \<open>pmin > gain_dip ctr * N\<^sup>2\<close> forces
      \<open>Ffeas = {}\<close>).  The composition below is \<^bold>\<open>machine-checked\<close>; only the leaf lemmas remain
      \<open>sorry\<close>.\<close>
proof -
  obtain x0 :: "planar^'n"
    where x0I: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
      and x0reg: "\<forall>\<omega>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
    using regular_config_exists[OF c6 feasible] by blast
  have x0F: "x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
    using x0I interior_subset by blast
  have nondeg: "\<forall>\<omega>\<in>Omega ctr. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  proof (intro ballI notI)
    fix \<omega> assume "\<omega> \<in> Omega ctr"
      and deg: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0"
    from deg have g: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0"
      and dz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0" by auto
    have e: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>)
              = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 1
                  * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 2 $ 2
                - (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2"
      by (rule det_2_symmetric[OF HessU_dip_symmetric])
    from e dz have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 1
                      * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 2 $ 2
                    = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2" by simp
    with g have "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0"
      using Phibad_zero_iff by blast
    with x0reg show False by simp
  qed
  obtain \<epsilon> :: real where \<epsilon>0: "0 < \<epsilon>"
      and sph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
      and ann: "\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    using no_degenerate_to_sphere_annulus[OF nondeg] by blast
  have c1: "0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
    using \<epsilon>0 x0F sph ann by (intro conjI)
  show ?thesis
  proof (rule exI[where x = x0], rule exI[where x = \<epsilon>])
    show "0 < \<epsilon>
          \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
          \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
          \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
      by (rule c1)
  qed
qed

text \<open>\<^bold>\<open>The regular feasible witness for the dipole, with continuity DISCHARGED.\<close>  We bolt the
  two Weierstrass continuity conjuncts --- proven sorry-free in
  @{thm norm_gradU_dip_continuous_on} and @{thm sigma_min_HessU_dip_continuous_on} --- onto
  the regular feasible point, so what remains assumed is purely the existence of that point.\<close>

lemma regular_feasible_witness_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
    and feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: (planar^'n) set) \<noteq> {}"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> continuous_on (sphere ctr \<epsilon>)
                  (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>))
            \<and> continuous_on (Omega ctr - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)
                       + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
proof -
  obtain x0 :: "planar^'n" and \<epsilon> :: real
    where \<epsilon>0: "0 < \<epsilon>"
      and feas: "x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
      and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
      and rO: "\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    using regular_feasible_point_dip[OF c6 feasible] by blast
  have c1: "continuous_on (sphere ctr \<epsilon>)
              (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>))"
    by (rule norm_gradU_dip_continuous_on)
  have c2: "continuous_on (Omega ctr - ball ctr \<epsilon>)
              (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)
                   + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
    by (intro continuous_on_add norm_gradU_dip_continuous_on
              sigma_min_HessU_dip_continuous_on)
  show ?thesis using \<epsilon>0 feas c1 c2 rsph rO by blast
qed

text \<open>\<^bold>\<open>The concrete capstone: \<open>\<F>\<^sub>0\<close> for the ACTUAL dipole pattern is nonempty.\<close>  This is
  \<open>thm:final\<close>'s nonemptiness for the real radiation intensity \<open>U_dip = g(\<omega>)\<bar>A(\<bm>x,\<omega>)\<bar>\<^sup>2\<close>
  with the steered wavevector \<open>cvec\<^sub>dip\<close> and the smooth dipole gain \<open>gain\<^sub>dip = \<bar>e(\<theta>)\<bar>\<^sup>2\<close>
  --- no abstract \<open>cvec\<close>/\<open>g\<close>.  The continuity half is fully proven; the only assumption is
  the regular feasible point (the determinant/Baire payoff, @{thm regular_feasible_point_dip}).\<close>

theorem F0_dip_nonempty:
  assumes c6: "6 \<le> CARD('n)"
  shows "\<exists>A B D \<omega>0 \<omega>s \<omega>null ctr R dmin \<delta>null pmin \<xi> \<kappa> \<epsilon>.
            0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>
              \<noteq> ({}::(planar^'n) set)"
  \<comment> \<open>\<^bold>\<open>Unconditional capstone.\<close>  The only hypothesis is the dimension restriction \<open>c6\<close>; the design
      (steering \<open>\<omega>\<^sub>0,\<omega>\<^sub>s,\<omega>\<^sub>null\<close>, geometry \<open>A,B,D\<close>, tolerances \<open>d\<^sub>min,\<delta>\<^sub>null,p\<^sub>min,R\<close> and margins) is
      \<^emph>\<open>delivered by the construction\<close>, not assumed.  Feasibility is discharged by the explicit
      Slater witness (@{thm feasible_witness_exists}): the actual \<open>cvec_dip\<close> nulls at \<open>\<omega>\<^sub>null\<close>
      (roots of unity, \<open>A(\<bm>x,\<omega>\<^sub>null)=0\<close>), the main-beam power is pinned to the cap for \<^emph>\<open>every\<close>
      configuration (@{thm Upow_at_main}: \<open>cvec_dip(\<omega>\<^sub>0)=0\<close>), and we pick \<open>p\<^sub>min,d\<^sub>min,\<delta>\<^sub>null\<close> to make
      the witness strictly feasible --- everything is under our control.\<close>
proof -
  define \<omega>0 :: planar where "\<omega>0 = vector [pi/2, 0]"
  define \<omega>s :: planar where "\<omega>s = vector [0, 0]"
  define \<omega>null :: planar where "\<omega>null = vector [pi, 0]"
  have hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    by (simp add: \<omega>s_def \<omega>0_def kz_def)
  have cn: "cvec_dip \<omega>0 \<omega>s \<omega>null \<noteq> 0"
  proof -
    have "cvec_dip \<omega>0 \<omega>s \<omega>null $ 1 = - 2"
      by (simp add: cvec_dip_def \<omega>0_def \<omega>s_def \<omega>null_def kx_def ky_def kz_def
                    sin_pi_half cos_pi_half axis_def)
    hence "cvec_dip \<omega>0 \<omega>s \<omega>null $ 1 \<noteq> 0" by simp
    thus ?thesis by (metis zero_index)
  qed
  have N1: "CARD('n) > 1" using c6 by simp
  have spos: "(0::real) < 1" by simp
  obtain x :: "planar^'n"
    where afz: "af (cvec_dip \<omega>0 \<omega>s) x \<omega>null = 0"
      and spac0: "\<forall>m m'. m \<noteq> m' \<longrightarrow> (1::real) \<le> spdist 0 0 1 (x $ m) (x $ m')"
    using feasible_witness_exists[OF N1 cn spos] by meson
  define R :: real where "R = norm x + 1"
  have g0pos: "0 < gain_dip \<omega>0"
  proof -
    have "sin (\<omega>0 $ 1) \<noteq> 0" by (simp add: \<omega>0_def sin_pi_half)
    hence "gain_dip \<omega>0 \<noteq> 0" by (rule gain_dip_nonzero_of_sin)
    moreover have "0 \<le> gain_dip \<omega>0" by (rule gain_dip_nonneg)
    ultimately show ?thesis by simp
  qed
  have feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
                    :: (planar^'n) set) \<noteq> {}"
  proof -
    have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. (1/2::real) < spdist 0 0 1 (x $ fst p) (x $ snd p)"
      using spac0 by fastforce
    have Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < 1"
      using afz by (simp add: Upow_def)
    have Pgt: "(0::real) < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0"
    proof -
      have "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0 = gain_dip \<omega>0 * (real CARD('n))\<^sup>2"
        by (rule Upow_at_main[OF hsep])
      moreover have "0 < (real CARD('n))\<^sup>2" using N1 by simp
      ultimately show ?thesis using mult_pos_pos[OF g0pos] by simp
    qed
    have inR: "x \<in> ball 0 R" by (simp add: R_def dist_norm)
    obtain \<rho> where \<rho>: "0 < \<rho>"
        and sub: "ball x \<rho> \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0"
      using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
    have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0)"
      by (rule interior_maximal[OF sub open_ball])
    moreover have "x \<in> ball x \<rho>" using \<rho> by simp
    ultimately show ?thesis by blast
  qed
  have "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 (Omega \<omega>0) 1 0 \<xi> \<kappa> \<epsilon>
              \<noteq> ({}::(planar^'n) set)"
    using regular_feasible_witness_dip[OF c6 feasible]
    by (blast intro: F0_nonempty_of_witness)
  thus ?thesis by blast
qed


end
