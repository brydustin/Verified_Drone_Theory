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

end
