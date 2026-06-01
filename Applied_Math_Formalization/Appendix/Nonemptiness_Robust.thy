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

text \<open>\<^bold>\<open>OBLIGATION (the determinant's payoff).\<close>  The set of feasible configurations carrying
  a degenerate critical point with \<open>A \<noteq> 0\<close> is meager.  This is \<open>prop:dimZ\<close>(1): \<open>lem:Msurj\<close>
  (the \<open>12\<times>12\<close> \<open>bigJ_det \<noteq> 0\<close>) \<open>\<Longrightarrow>\<close> \<open>Z\<^sub>reg\<close> is codim-3 \<open>\<Longrightarrow>\<close> its projection is meager.  This is the
  exact point at which the proven determinants enter, and it is the consumer the
  appendix's \<open>Bregnonzero\<close> meagerness reduces to.\<close>

lemma Phi_bad_meager:
  fixes V :: "(planar^'n) set" and cvec :: "angle \<Rightarrow> planar" and gain :: "angle \<Rightarrow> real"
  assumes "open V" and "V \<noteq> {}" and "6 \<le> CARD('n)" and "\<forall>\<omega>. cvec \<omega> \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>. Phibad cvec gain x \<omega> = 0 \<and> A_cart cvec x \<omega> \<noteq> 0}"
  sorry


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
  payoff (degenerate configs meager, @{thm Phi_bad_meager} + Baire inside the feasible
  interior); crucially the \<^emph>\<open>continuity\<close> half is no longer part of this hole --- it is
  discharged below from the proven dipole facts.\<close>

lemma regular_feasible_point_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>Omega ctr - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
  \<comment> \<open>downstream of \<open>Phi_bad_meager\<close>: degenerate configs are meager, so the regular
      witness exists inside the feasible interior by Baire --- to be wired in\<close>
  sorry

text \<open>\<^bold>\<open>The regular feasible witness for the dipole, with continuity DISCHARGED.\<close>  We bolt the
  two Weierstrass continuity conjuncts --- proven sorry-free in
  @{thm norm_gradU_dip_continuous_on} and @{thm sigma_min_HessU_dip_continuous_on} --- onto
  the regular feasible point, so what remains assumed is purely the existence of that point.\<close>

lemma regular_feasible_witness_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
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
    using regular_feasible_point_dip[OF c6] by blast
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
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes c6: "6 \<le> CARD('n)"
  shows "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
            \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr (Omega ctr) \<delta>null pmin \<xi> \<kappa> \<epsilon>
                \<noteq> ({}::(planar^'n) set)"
  using regular_feasible_witness_dip[OF c6]
  by (blast intro: F0_nonempty_of_witness)


end
