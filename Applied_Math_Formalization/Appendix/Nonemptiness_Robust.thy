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


subsection \<open>The feasible set \<open>\<F>\<close> and its compactness\<close>

text \<open>TeX (L192): \<open>\<F> := {\<bm>x \<in> B\<^sub>R : \<bar>r\<^sub>n - r\<^sub>m\<bar> \<ge> d\<^sub>min \<forall> n \<noteq> m, U(\<bm>x,\<omega>\<^sub>N) \<le> \<delta>\<^sub>null}\<close>.
  The spacing and null constraints are closed and \<open>B\<^sub>R\<close> is a bounded ball, so \<open>\<F>\<close>
  is compact.\<close>

definition Ffeas ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2
     \<Rightarrow> ((real^2)^'n) set"
  where
  "Ffeas cvec g R dmin \<delta>null \<omega>N =
     {x. x \<in> cball 0 R
       \<and> (\<forall>n m. n \<noteq> m \<longrightarrow> dmin \<le> dist (x $ n) (x $ m))
       \<and> Upow cvec g x \<omega>N \<le> \<delta>null}"

lemma closed_spacing:
  "closed {x::(real^2)^'n. \<forall>n m. n \<noteq> m \<longrightarrow> dmin \<le> dist (x $ n) (x $ m)}"
proof -
  have "{x::(real^2)^'n. \<forall>n m. n \<noteq> m \<longrightarrow> dmin \<le> dist (x $ n) (x $ m)}
        = (\<Inter>n. \<Inter>m. (if n = m then UNIV else {x. dmin \<le> dist (x $ n) (x $ m)}))"
    by auto
  moreover have "closed \<dots>"
  proof (intro closed_INT)
    fix n m :: 'n
    show " \<forall>n\<in>UNIV. closed (\<Inter>m. if n = m then UNIV else {x. dmin \<le> dist (x $h n) (x $h m)})"
      by (cases "n = m", auto intro!: closed_Collect_le continuous_intros)
  qed
  ultimately show ?thesis by simp
qed

lemma closed_null:
  "closed {x::(real^2)^'n. Upow cvec g x \<omega>N \<le> \<delta>null}"
  by (rule closed_Collect_le[OF continuous_on_Upow_config continuous_on_const])

theorem Ffeas_compact:
  "compact (Ffeas cvec g R dmin \<delta>null \<omega>N :: ((real^2)^'n) set)"
proof -
  have eq: "Ffeas cvec g R dmin \<delta>null \<omega>N
        = cball 0 R
          \<inter> {x. \<forall>n m. n \<noteq> m \<longrightarrow> dmin \<le> dist (x $ n) (x $ m)}
          \<inter> {x. Upow cvec g x \<omega>N \<le> \<delta>null}"
    unfolding Ffeas_def by auto
  show ?thesis
    unfolding eq
    by (intro compact_Int_closed compact_cball closed_spacing closed_null)
qed

end
