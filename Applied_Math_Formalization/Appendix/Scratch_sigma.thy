theory Scratch_sigma
  imports "Applied_Math_Nonemptiness.Nonemptiness_Paper"
begin

text \<open>Topology core for the sigma-compact clause of core_2d: a relatively-closed subset of an
  open set (in R^m) is sigma-compact.\<close>

lemma rel_closed_open_sigma_compact:
  fixes U T :: "(real^'m::{finite,wellorder}) set"
  assumes openU: "open U" and closedT: "closed T"
  shows "\<exists>K::nat \<Rightarrow> (real^'m::{finite,wellorder}) set. (\<forall>n. compact (K n)) \<and> U \<inter> T = (\<Union>n. K n)"
proof (cases "U = UNIV")
  case True
  define K where "K = (\<lambda>n::nat. T \<inter> cball 0 (real n))"
  have "compact (K n)" for n
  proof -
    have "K n \<subseteq> cball 0 (real n)" unfolding K_def by auto
    hence "bounded (K n)" using bounded_cball bounded_subset by blast
    moreover have "closed (K n)" unfolding K_def by (intro closed_Int closedT closed_cball)
    ultimately show ?thesis by (simp add: compact_eq_bounded_closed)
  qed
  moreover have "U \<inter> T = (\<Union>n. K n)"
  proof -
    have "T = (\<Union>n. T \<inter> cball 0 (real n))"
      by (auto simp: dist_norm) (meson real_arch_simple)
    thus ?thesis using True by (simp add: K_def)
  qed
  ultimately show ?thesis by blast
next
  case False
  then have neU: "- U \<noteq> {}" by auto
  have cU: "closed (- U)" using openU by (metis open_closed)
  have pos: "0 < setdist {x} (- U)" if "x \<in> U" for x
  proof -
    have "x \<notin> closure (- U)" using that cU by simp
    thus ?thesis using setdist_eq_0_sing_1[of x "- U"] neU setdist_pos_le[of "{x}" "- U"]
      by (metis order_le_less)
  qed
  define K where "K = (\<lambda>n::nat. T \<inter> cball 0 (real n) \<inter> {x. 1/(real n + 1) \<le> setdist {x} (- U)})"
  have "compact (K n)" for n
  proof -
    have csd: "closed {x. 1/(real n + 1) \<le> setdist {x} (- U)}"
      by (intro closed_Collect_le continuous_on_const continuous_on_setdist)
    have "K n \<subseteq> cball 0 (real n)" unfolding K_def by auto
    hence "bounded (K n)" using bounded_cball bounded_subset by blast
    moreover have "closed (K n)" unfolding K_def by (intro closed_Int closedT closed_cball csd)
    ultimately show ?thesis by (simp add: compact_eq_bounded_closed)
  qed
  moreover have "U \<inter> T = (\<Union>n. K n)"
  proof
    show "U \<inter> T \<subseteq> (\<Union>n. K n)"
    proof
      fix x assume x: "x \<in> U \<inter> T"
      hence sp: "0 < setdist {x} (- U)" using pos by blast
      obtain n where n: "max (norm x) (1 / setdist {x} (- U)) \<le> real n" using real_arch_simple by blast
      have "norm x \<le> real n" using n by simp
      moreover have "1/(real n + 1) \<le> setdist {x} (- U)"
      proof -
        have hn: "1 / setdist {x} (- U) \<le> real n" using n by simp
        from mult_right_mono[OF hn less_imp_le[OF sp]]
        have h2: "1 \<le> real n * setdist {x} (- U)" using sp by simp
        have "(real n + 1) * setdist {x} (- U) = real n * setdist {x} (- U) + setdist {x} (- U)"
          by (simp add: distrib_right)
        hence h3: "1 \<le> (real n + 1) * setdist {x} (- U)" using h2 sp by linarith
        have "(0::real) < real n + 1" by simp
        thus ?thesis using h3 by (metis pos_divide_le_eq mult.commute)
      qed
      ultimately show "x \<in> (\<Union>n. K n)" using x by (auto simp: K_def dist_norm)
    qed
  next
    show "(\<Union>n. K n) \<subseteq> U \<inter> T"
    proof
      fix x assume "x \<in> (\<Union>n. K n)"
      then obtain n where "x \<in> K n" by blast
      hence xT: "x \<in> T" and sd: "1/(real n + 1) \<le> setdist {x} (- U)" by (auto simp: K_def)
      have "(0::real) < 1/(real n + 1)" by simp
      hence "0 < setdist {x} (- U)" using sd by linarith
      hence "x \<notin> - U" using setdist_sing_in_set[of x "- U"] by force
      thus "x \<in> U \<inter> T" using xT by simp
    qed
  qed
  ultimately show ?thesis by blast
qed

end
