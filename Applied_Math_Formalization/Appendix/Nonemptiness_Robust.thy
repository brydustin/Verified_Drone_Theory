theory Nonemptiness_Robust
  imports Nonemptiness_Capstone
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

end
