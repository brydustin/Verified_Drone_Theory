section \<open>The feasible set\<close>

theory Feasible_Set
  imports
    Array_Factor
begin

lemma continuous_on_A_cart_config:
  fixes \<omega> :: "real^2" and cvec :: "real^2 \<Rightarrow> real^2"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. A_cart cvec x \<omega>)"
  unfolding A_cart_def
  by (intro continuous_intros continuous_on_cis)

lemma continuous_on_U_cart_config:
  fixes \<omega> :: "real^2" and cvec :: "real^2 \<Rightarrow> real^2" and g :: "real^2 \<Rightarrow> real"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. U_cart cvec g x \<omega>)"
  unfolding U_cart_def
  by (intro continuous_intros continuous_on_A_cart_config)

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

definition Ffeas ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real \<Rightarrow> real \<Rightarrow> ((real^2)^'n) set"
  where
  "Ffeas cvec g R dmin A B D \<omega>null \<omega>0 \<delta>null pmin =
       (cpen dmin A B D) -` {0}
     \<inter> (\<lambda>x. U_cart cvec g x \<omega>null) -` {0 .. \<delta>null}
     \<inter> (\<lambda>x. U_cart cvec g x \<omega>0) -` {pmin .. g \<omega>0 * (real CARD('n))\<^sup>2}
     \<inter> cball 0 R"

lemma cmod_A_cart_le_card:
  "cmod (A_cart cvec (x::(real^2)^'n) \<omega>) \<le> real CARD('n)"
proof -
  have "cmod (A_cart cvec x \<omega>) \<le> (\<Sum>n\<in>(UNIV::'n set). cmod (cis (- (cvec \<omega> \<bullet> x $ n))))"
    unfolding A_cart_def by (rule norm_sum)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). 1)" by simp
  also have "\<dots> = real CARD('n)" by simp
  finally show ?thesis .
qed

lemma U_cart_le_max:
  assumes "0 \<le> g \<omega>"
  shows "U_cart cvec g (x::(real^2)^'n) \<omega> \<le> g \<omega> * (real CARD('n))\<^sup>2"
proof -
  have "(cmod (A_cart cvec x \<omega>))\<^sup>2 \<le> (real CARD('n))\<^sup>2"
    by (rule power_mono[OF cmod_A_cart_le_card norm_ge_zero])
  hence "g \<omega> * (cmod (A_cart cvec x \<omega>))\<^sup>2 \<le> g \<omega> * (real CARD('n))\<^sup>2"
    by (rule mult_left_mono[OF _ assms])
  thus ?thesis unfolding U_cart_def .
qed

lemma ball_inside_Ffeas:
  fixes xbar :: "(real^2)^'n"
  assumes gnull: "0 \<le> g \<omega>null" and g0: "0 \<le> g \<omega>0"
    and spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (xbar $ fst p) (xbar $ snd p)"
    and Nlt: "U_cart cvec g xbar \<omega>null < \<delta>null"
    and Pgt: "pmin < U_cart cvec g xbar \<omega>0"
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
    "U = Usp \<inter> {x. U_cart cvec g x \<omega>null < \<delta>null}
             \<inter> {x. pmin < U_cart cvec g x \<omega>0} \<inter> ball 0 R"
  have opU: "open U"
    unfolding U_def
    by (intro open_Int op_sp open_Collect_less continuous_on_U_cart_config
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
    have "0 \<le> U_cart cvec g x \<omega>null"
      unfolding U_cart_def by (intro mult_nonneg_nonneg gnull zero_le_power2)
    moreover have "U_cart cvec g x \<omega>null < \<delta>null" using xU' unfolding U_def by simp
    ultimately have cN: "x \<in> (\<lambda>x. U_cart cvec g x \<omega>null) -` {0..\<delta>null}" by simp
    have "pmin < U_cart cvec g x \<omega>0" using xU' unfolding U_def by simp
    moreover have "U_cart cvec g x \<omega>0 \<le> g \<omega>0 * (real CARD('n))\<^sup>2"
      by (rule U_cart_le_max[where g=g and \<omega>=\<omega>0, OF g0])
    ultimately have cP: "x \<in> (\<lambda>x. U_cart cvec g x \<omega>0) -` {pmin .. g \<omega>0 * (real CARD('n))\<^sup>2}"
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
