theory Nonemptiness_Feasibility
  imports Nonemptiness_Array_Factor
begin

section \<open>Openness Skeleton for the Feasible Family\<close>

text \<open>
  The feasible set \<open>Fset\<close> of the paper is cut out by \<^emph>\<open>non-strict\<close> constraints
  (a closed ball, pairwise spacings \<open>\<ge> d\<^sub>min\<close>, and a null bound \<open>U(\<cdot>,\<omega>\<^sub>N) \<le> \<delta>\<^sub>null\<close>),
  so it is not open. The open feasible family \<open>U\<^sub>feas \<subseteq> Fset\<close> of
  Proposition \<open>prop:openfeas\<close> arises because the witness satisfies these constraints
  \<^emph>\<open>strictly\<close>: the strict-constraint set is open (preimage of open rays under the
  continuous spacing and power functions) and is contained in the non-strict set.

  This module proves that backbone abstractly in the continuous gap/power functions,
  so it can be instantiated once the concrete spacing distances and
  \<^const>\<open>power_pattern\<close> are plugged in. It supplies the \<open>open V\<close> and \<open>V \<subseteq> Fset\<close>
  hypotheses of the closeout lemma \<open>nonemptiness_from_meager_branches\<close>; only nonemptiness of the witness (the
  explicit nulling configuration) is left to the geometric construction.
\<close>

definition strict_feasible ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "strict_feasible I gap P d \<delta> B =
     B \<inter> {x. \<forall>k\<in>I. d < gap k x} \<inter> {x. P x < \<delta>}"

definition feasible ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "feasible I gap P d \<delta> B =
     B \<inter> {x. \<forall>k\<in>I. d \<le> gap k x} \<inter> {x. P x \<le> \<delta>}"

lemma strict_feasible_subset:
  "strict_feasible I gap P d \<delta> B \<subseteq> feasible I gap P d \<delta> B"
  unfolding strict_feasible_def feasible_def by force

lemma open_strict_feasible:
  fixes I :: "'i set" and gap :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> real"
    and P :: "'a \<Rightarrow> real" and d \<delta> :: real and B :: "'a set"
  assumes B: "open B" and finI: "finite I"
    and cg: "\<And>k. k \<in> I \<Longrightarrow> continuous_on UNIV (gap k)"
    and cP: "continuous_on UNIV P"
  shows "open (strict_feasible I gap P d \<delta> B)"
proof -
  have gopen: "\<And>k. k \<in> I \<Longrightarrow> open {x. d < gap k x}"
    by (rule open_Collect_less[OF continuous_on_const cg])
  have "open (\<Inter> ((\<lambda>k. {x. d < gap k x}) ` I))"
    by (rule open_Inter) (use finI gopen in auto)
  moreover have "(\<Inter> ((\<lambda>k. {x. d < gap k x}) ` I)) = {x. \<forall>k\<in>I. d < gap k x}"
    by auto
  ultimately have gaps_open: "open {x. \<forall>k\<in>I. d < gap k x}" by simp
  have Popen: "open {x. P x < \<delta>}"
    by (rule open_Collect_less[OF cP continuous_on_const])
  show ?thesis
    unfolding strict_feasible_def
    using B gaps_open Popen by blast
qed

text \<open>
  Consequently a strictly-feasible witness yields a nonempty open subset of
  \<open>Fset\<close>: exactly the \<open>open V\<close>, \<open>V \<noteq> {}\<close>, \<open>V \<subseteq> Fset\<close> triple that the closeout needs.
\<close>

lemma open_feasible_family:
  fixes I :: "'i set" and gap :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> real"
    and P :: "'a \<Rightarrow> real" and d \<delta> :: real and B :: "'a set"
  assumes B: "open B" and finI: "finite I"
    and cg: "\<And>k. k \<in> I \<Longrightarrow> continuous_on UNIV (gap k)"
    and cP: "continuous_on UNIV P"
    and witness: "x\<^sub>0 \<in> strict_feasible I gap P d \<delta> B"
  shows "open (strict_feasible I gap P d \<delta> B)
       \<and> strict_feasible I gap P d \<delta> B \<noteq> {}
       \<and> strict_feasible I gap P d \<delta> B \<subseteq> feasible I gap P d \<delta> B"
proof -
  have h_open: "open (strict_feasible I gap P d \<delta> B)"
    by (rule open_strict_feasible[OF B finI cg cP])
  have h_ne: "strict_feasible I gap P d \<delta> B \<noteq> {}"
    using witness by auto
  have h_sub: "strict_feasible I gap P d \<delta> B \<subseteq> feasible I gap P d \<delta> B"
    by (rule strict_feasible_subset)
  show ?thesis
    using h_open h_ne h_sub by blast
qed

end
