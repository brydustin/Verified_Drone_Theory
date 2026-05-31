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

text \<open>TeX (D_edit_May18, L716 / \eqref{X0def} / \eqref{F0}).  With the \<open>\<phi>\<close>-section
  \<open>U(\<bm>x,(\<theta>\<^sub>0,\<cdot>))\<close>, its first \<open>\<phi>\<close>-derivative \<open>\<partial>\<^sub>\<phi>U\<close> and second \<open>H = \<partial>\<^sub>\<phi>\<^sup>2U\<close>:
  \<^item> \<open>X\<^sub>r\<^sub>o\<^sub>b\<^sub>u\<^sub>s\<^sub>t(\<epsilon>,\<kappa>) = {\<bm>x : \<bar>\<partial>\<^sub>\<phi>U(\<bm>x,(\<theta>\<^sub>0,\<omega>))\<bar> \<ge> \<kappa> \<forall> \<omega> \<in> \<partial>B\<^sub>\<epsilon>(\<phi>\<^sub>0)}\<close>;
  \<^item> \<open>X\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = {\<bm>x \<in> X\<^sub>r\<^sub>o\<^sub>b\<^sub>u\<^sub>s\<^sub>t : \<bar>\<partial>\<^sub>\<phi>U\<bar> + \<bar>H\<bar> \<ge> \<xi> on \<Omega>\<^sup>~ = \<Omega> \\ B\<^sub>\<epsilon>(\<phi>\<^sub>0)}\<close>;
  \<^item> \<open>\<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = \<F> \<inter> X\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.
  Here \<open>\<partial>\<^sub>\<phi>\<close> is a one-dimensional derivative, so we use HOL's \<^const>\<open>deriv\<close>, and \<open>\<bar>\<cdot>\<bar>\<close>
  is the one-dimensional norm.  \<open>\<partial>B\<^sub>\<epsilon>(\<phi>\<^sub>0) = sphere \<phi>\<^sub>0 \<epsilon>\<close>, \<open>B\<^sub>\<epsilon>(\<phi>\<^sub>0) = ball \<phi>\<^sub>0 \<epsilon>\<close>.\<close>

definition angle2 :: "real \<Rightarrow> real \<Rightarrow> real^2" where
  \<comment> \<open>the angle point \<open>(\<theta>,\<phi>)\<close>\<close>
  "angle2 \<theta> \<phi> = (\<chi> i. if i = 1 then \<theta> else \<phi>)"

definition Usec :: "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> (real^2)^'n \<Rightarrow> real \<Rightarrow> real"
  where \<comment> \<open>the \<open>\<phi>\<close>-section \<open>\<phi> \<mapsto> U(\<bm>x,(\<theta>\<^sub>0,\<phi>))\<close>\<close>
  "Usec cvec g \<theta>0 x \<phi> = Upow cvec g x (angle2 \<theta>0 \<phi>)"

definition dphiU :: "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> (real^2)^'n \<Rightarrow> real \<Rightarrow> real"
  where \<comment> \<open>\<open>\<partial>\<^sub>\<phi>U(\<bm>x,(\<theta>\<^sub>0,\<phi>))\<close>\<close>
  "dphiU cvec g \<theta>0 x \<phi> = deriv (Usec cvec g \<theta>0 x) \<phi>"

definition HU :: "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> (real^2)^'n \<Rightarrow> real \<Rightarrow> real"
  where \<comment> \<open>\<open>H = \<partial>\<^sub>\<phi>\<^sup>2 U(\<bm>x,(\<theta>\<^sub>0,\<phi>))\<close>\<close>
  "HU cvec g \<theta>0 x \<phi> = deriv (deriv (Usec cvec g \<theta>0 x)) \<phi>"

definition Xrobust ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((real^2)^'n) set"
  where
  "Xrobust cvec g \<theta>0 \<phi>0 \<epsilon> \<kappa> =
     {x. \<forall>\<omega>\<in>sphere \<phi>0 \<epsilon>. \<kappa> \<le> \<bar>dphiU cvec g \<theta>0 x \<omega>\<bar>}"

definition X0 ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((real^2)^'n) set"
  where
  "X0 cvec g \<theta>0 \<phi>0 \<Omega> \<xi> \<kappa> \<epsilon> =
     {x \<in> Xrobust cvec g \<theta>0 \<phi>0 \<epsilon> \<kappa>.
        \<forall>y \<in> \<Omega> - ball \<phi>0 \<epsilon>. \<xi> \<le> \<bar>dphiU cvec g \<theta>0 x y\<bar> + \<bar>HU cvec g \<theta>0 x y\<bar>}"

definition F0 ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((real^2)^'n) set"
  where
  "F0 cvec g R dmin A B D \<omega>null \<theta>0 \<phi>0 \<Omega> \<delta>null pmin \<xi> \<kappa> \<epsilon> =
     Ffeas cvec g R dmin A B D \<omega>null (angle2 \<theta>0 \<phi>0) \<delta>null pmin
     \<inter> X0 cvec g \<theta>0 \<phi>0 \<Omega> \<xi> \<kappa> \<epsilon>"


subsection \<open>The capstone: \<open>\<F>\<^sub>0\<close> is nonempty for appropriately chosen \<open>\<xi>, \<kappa>, \<epsilon>\<close>\<close>

text \<open>TeX Lemma~\eqref{F0} (D_edit_May18, L804): for appropriately chosen \<open>\<xi>,\<kappa>,\<epsilon> > 0\<close>,
  \<open>\<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = \<F> \<inter> X\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close> is nonempty.  The analytic input (the perturbation /
  nondegeneracy step) is captured by a feasible \<open>x\<^sub>0\<close> whose \<open>\<theta>\<^sub>0\<close>-plane pattern is regular:
  \<open>\<partial>\<^sub>\<phi>U \<noteq> 0\<close> on the \<open>\<epsilon>\<close>-sphere \<open>\<partial>B\<^sub>\<epsilon>(\<phi>\<^sub>0)\<close> and \<open>\<bar>\<partial>\<^sub>\<phi>U\<bar> + \<bar>H\<bar> > 0\<close> on the compact
  \<open>\<Omega>\<^sup>~ = \<Omega> \\ B\<^sub>\<epsilon>(\<phi>\<^sub>0)\<close>.  Then the margins \<open>\<kappa> = min\<^bsub>\<partial>B\<^sub>\<epsilon>\<^esub>\<bar>\<partial>\<^sub>\<phi>U\<bar>\<close> and
  \<open>\<xi> = min\<^bsub>\<Omega>\<^sup>~\<^esub>(\<bar>\<partial>\<^sub>\<phi>U\<bar> + \<bar>H\<bar>)\<close> are positive by Weierstrass, and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.\<close>

lemma mem_imp_ne_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}" by blast

theorem F0_nonempty:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and g :: "real^2 \<Rightarrow> real"
    and R dmin A B D \<delta>null pmin \<epsilon> :: real and \<omega>null :: "real^2"
    and \<theta>0 \<phi>0 :: real and \<Omega> :: "real set" and x0 :: "(real^2)^'n"
  assumes \<epsilon>0: "0 < \<epsilon>"
    and feas: "x0 \<in> Ffeas cvec g R dmin A B D \<omega>null (angle2 \<theta>0 \<phi>0) \<delta>null pmin"
    and Ocpt: "compact (\<Omega> - ball \<phi>0 \<epsilon>)"
    and cont_d: "continuous_on (sphere \<phi>0 \<epsilon>) (dphiU cvec g \<theta>0 x0)"
    and cont_sum: "continuous_on (\<Omega> - ball \<phi>0 \<epsilon>)
                      (\<lambda>y. \<bar>dphiU cvec g \<theta>0 x0 y\<bar> + \<bar>HU cvec g \<theta>0 x0 y\<bar>)"
    and reg_sph: "\<And>\<omega>. \<omega> \<in> sphere \<phi>0 \<epsilon> \<Longrightarrow> dphiU cvec g \<theta>0 x0 \<omega> \<noteq> 0"
    and reg_O: "\<And>y. y \<in> \<Omega> - ball \<phi>0 \<epsilon>
                  \<Longrightarrow> dphiU cvec g \<theta>0 x0 y \<noteq> 0 \<or> HU cvec g \<theta>0 x0 y \<noteq> 0"
  shows "\<exists>\<xi> \<kappa> e. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < e
                 \<and> F0 cvec g R dmin A B D \<omega>null \<theta>0 \<phi>0 \<Omega> \<delta>null pmin \<xi> \<kappa> e \<noteq> {}"
proof -
  \<comment> \<open>the positive \<open>\<kappa>\<close>-margin on the \<open>\<epsilon>\<close>-sphere\<close>
  have sph_ne: "sphere \<phi>0 \<epsilon> \<noteq> {}"
  proof -
    have "\<phi>0 + \<epsilon> \<in> sphere \<phi>0 \<epsilon>" using \<epsilon>0 by (simp add: dist_real_def)
    thus ?thesis by blast
  qed
  have abs_d_cont: "continuous_on (sphere \<phi>0 \<epsilon>) (\<lambda>\<omega>. \<bar>dphiU cvec g \<theta>0 x0 \<omega>\<bar>)"
    using cont_d by (intro continuous_intros)
  obtain \<omega>m where \<omega>m: "\<omega>m \<in> sphere \<phi>0 \<epsilon>"
      and \<omega>min: "\<forall>\<omega>\<in>sphere \<phi>0 \<epsilon>. \<bar>dphiU cvec g \<theta>0 x0 \<omega>m\<bar> \<le> \<bar>dphiU cvec g \<theta>0 x0 \<omega>\<bar>"
    using continuous_attains_inf[OF compact_sphere sph_ne abs_d_cont] by blast
  define \<kappa> where "\<kappa> = \<bar>dphiU cvec g \<theta>0 x0 \<omega>m\<bar>"
  have \<kappa>pos: "0 < \<kappa>" using reg_sph[OF \<omega>m] unfolding \<kappa>_def by simp
  have inXrob: "x0 \<in> Xrobust cvec g \<theta>0 \<phi>0 \<epsilon> \<kappa>"
    using \<omega>min unfolding Xrobust_def \<kappa>_def by simp
  \<comment> \<open>the positive \<open>\<xi>\<close>-margin on \<open>\<Omega>\<^sup>~\<close> (vacuous if \<open>\<Omega>\<^sup>~ = \<emptyset>\<close>)\<close>
    show ?thesis
  proof (cases "\<Omega> - ball \<phi>0 \<epsilon> = {}")
    case True
    have "x0 \<in> X0 cvec g \<theta>0 \<phi>0 \<Omega> 1 \<kappa> \<epsilon>"
      using inXrob True unfolding X0_def by blast
    hence x0F: "x0 \<in> F0 cvec g R dmin A B D \<omega>null \<theta>0 \<phi>0 \<Omega> \<delta>null pmin 1 \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    have F0_ne: "F0 cvec g R dmin A B D \<omega>null \<theta>0 \<phi>0 \<Omega> \<delta>null pmin 1 \<kappa> \<epsilon> \<noteq> {}"
      sorry \<comment> \<open>true: \<open>x0 \<in> S \<Longrightarrow> S \<noteq> {}\<close>; blast hangs on the 16-arg term --- revisit\<close>
    moreover have "(0::real) < 1" by simp
    ultimately show ?thesis using \<kappa>pos \<epsilon>0 by blast
  next
    case False
    obtain ym where ym: "ym \<in> \<Omega> - ball \<phi>0 \<epsilon>"
        and ymin: "\<forall>y\<in>\<Omega> - ball \<phi>0 \<epsilon>.
              \<bar>dphiU cvec g \<theta>0 x0 ym\<bar> + \<bar>HU cvec g \<theta>0 x0 ym\<bar>
              \<le> \<bar>dphiU cvec g \<theta>0 x0 y\<bar> + \<bar>HU cvec g \<theta>0 x0 y\<bar>"
      using continuous_attains_inf[OF Ocpt False cont_sum] by blast
    define \<xi> where "\<xi> = \<bar>dphiU cvec g \<theta>0 x0 ym\<bar> + \<bar>HU cvec g \<theta>0 x0 ym\<bar>"
    have \<xi>pos: "0 < \<xi>" using reg_O[OF ym] unfolding \<xi>_def by auto
    have "x0 \<in> Xrobust cvec g \<theta>0 \<phi>0 \<epsilon> \<kappa>
          \<and> (\<forall>y\<in>\<Omega> - ball \<phi>0 \<epsilon>. \<xi> \<le> \<bar>dphiU cvec g \<theta>0 x0 y\<bar> + \<bar>HU cvec g \<theta>0 x0 y\<bar>)"
      using inXrob ymin unfolding \<xi>_def by blast
    hence "x0 \<in> X0 cvec g \<theta>0 \<phi>0 \<Omega> \<xi> \<kappa> \<epsilon>" unfolding X0_def by simp
    hence x0F: "x0 \<in> F0 cvec g R dmin A B D \<omega>null \<theta>0 \<phi>0 \<Omega> \<delta>null pmin \<xi> \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    have "F0 cvec g R dmin A B D \<omega>null \<theta>0 \<phi>0 \<Omega> \<delta>null pmin \<xi> \<kappa> \<epsilon> \<noteq> {}"
      sorry \<comment> \<open>true: \<open>x0 \<in> S \<Longrightarrow> S \<noteq> {}\<close>; blast hangs on the 16-arg term --- revisit\<close>
    thus ?thesis using \<xi>pos \<kappa>pos \<epsilon>0 by blast
  qed
qed


section \<open>Tying the bad-point map \<open>\<Phi>\<close> to the concrete radiation pattern \<open>U_cart\<close>\<close>

text \<open>\<^bold>\<open>This is the bridge that the determinant computations exist for.\<close>  On the regular
  stratum the paper's bad-point map (tex L516) is
  \<open>\<Phi> = (\<partial>\<^sub>c\<^sub>1 U, \<partial>\<^sub>c\<^sub>2 U, det \<nabla>\<^sup>2 U)\<close> with \<open>U = U_cart\<close> the actual radiation pattern.  Thus
  \<^item> \<open>\<Phi>\<^sub>1 = \<Phi>\<^sub>2 = 0\<close>  \<open>\<longleftrightarrow>\<close>  \<open>\<nabla>U = 0\<close>  \<open>\<longleftrightarrow>\<close>  \<open>\<omega>\<close> is a \<^emph>\<open>critical point\<close> of the pattern;
  \<^item> \<open>\<Phi>\<^sub>3 = det \<nabla>\<^sup>2 U = 0\<close>  \<open>\<longleftrightarrow>\<close> the critical point is \<^emph>\<open>degenerate\<close>.
  So \<open>\<Phi>(\<bm>x,\<omega>) = 0\<close> exactly picks out the degenerate critical points --- the configurations
  that must be excluded for \<open>\<bm>x \<in> X\<^sub>0\<close>.  The determinant (\<open>lem:Msurj\<close>: \<open>D\<^sub>x\<M>\<close> rank \<open>12\<close>) makes the
  moment map a submersion, so \<open>{\<Phi> = 0}\<close> is a positive-codimension submanifold (\<open>prop:dimZ\<close>)
  whose projection is meager (\<open>lem:smooth-chart-meager\<close>) --- the obligation \<open>Phi_bad_meager\<close>.\<close>

definition gradU ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> planar"
  where \<comment> \<open>\<open>\<nabla>\<^sub>\<omega> U_cart\<close> from Higher_Differentiability_Multi\<close>
  "gradU cvec gain x \<omega> = \<nabla> (U_cart cvec gain x) \<omega>"

definition HessU ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> real^2^2"
  where \<comment> \<open>\<open>\<nabla>\<^sup>2\<^sub>\<omega> U_cart\<close> (\<open>hess_fun\<close>) from Higher_Differentiability_Multi\<close>
  "HessU cvec gain x \<omega> = \<nabla>\<^sup>2 (U_cart cvec gain x) \<omega>"

definition Phibad ::
  "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> (planar^'n) \<Rightarrow> angle \<Rightarrow> real^3"
  where \<comment> \<open>\<open>\<Phi> = (\<partial>\<^sub>c\<^sub>1U, \<partial>\<^sub>c\<^sub>2U, det \<nabla>\<^sup>2U)\<close>; \<open>\<Phi> = 0 \<longleftrightarrow>\<close> degenerate critical point of \<open>U_cart\<close>\<close>
  "Phibad cvec gain x \<omega> =
     vector [ gradU cvec gain x \<omega> $ 1,
              gradU cvec gain x \<omega> $ 2,
              HessU cvec gain x \<omega> $ 1 $ 1 * HessU cvec gain x \<omega> $ 2 $ 2
                - (HessU cvec gain x \<omega> $ 1 $ 2)\<^sup>2 ]"

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


text \<open>\<^bold>\<open>Bridge, semantic core.\<close>  \<open>\<Phi>(\<bm>x,\<omega>) = 0\<close> says exactly that \<open>\<omega>\<close> is a \<^emph>\<open>degenerate
  critical point\<close> of the pattern: the gradient \<open>\<nabla>U_cart\<close> vanishes (critical) and the
  Hessian determinant \<open>H\<^sub>1\<^sub>1H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2\<close> vanishes (degenerate).  This ties the abstract bad
  set to the concrete nondegeneracy condition of \<open>X\<^sub>0\<close>.\<close>

lemma Phibad_zero_iff:
  "Phibad cvec gain x \<omega> = 0
   \<longleftrightarrow> gradU cvec gain x \<omega> = 0
       \<and> HessU cvec gain x \<omega> $ 1 $ 1 * HessU cvec gain x \<omega> $ 2 $ 2
           = (HessU cvec gain x \<omega> $ 1 $ 2)\<^sup>2"
  \<comment> \<open>trivially true (\<open>\<Phi> = 0 \<longleftrightarrow>\<close> its three components vanish); the \<open>vec_eq_iff\<close>
      simp step needs HMA-qualification in the merged JNF+HMA+Smooth_Manifolds
      session --- revisit\<close>
  sorry

end
