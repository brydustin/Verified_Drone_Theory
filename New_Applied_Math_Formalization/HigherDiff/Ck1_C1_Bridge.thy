section \<open>From \<open>C\<^sup>1\<close> to the inverse-function-theorem interface\<close>

text \<open>
  The IFT-based regular-value engine \<open>regular_value_local_chart\<close>
  (in \<open>Regular_Value_Theorem\<close>) consumes its hypotheses as a
  \<^emph>\<open>blinfun-valued, continuous\<close> derivative on an open set:

  \<^item> \<open>derG\<close>: \<open>\<And>z. z \<in> W \<Longrightarrow> (G has_derivative blinfun_apply (G' z)) (at z)\<close>,
  \<^item> \<open>contG'\<close>: \<open>continuous_on W G'\<close>.

  This is exactly the content of \<open>C\<^sup>1\<close>.  The transversality keystone, on the
  other hand, only carries \<open>regular_value_on\<close> data (pointwise surjective
  derivative, no continuity).  This theory bridges the two: from
  \<open>Ck_on (Suc 0) G W\<close> (i.e.\ \<open>C\<^sup>1\<close> on the open set \<open>W\<close>) we manufacture the
  canonical witness \<open>G' z = Blinfun (frechet_derivative G (at z))\<close> and discharge
  both hypotheses.  The continuity half is the only real work: per-direction
  continuity of the Fréchet derivative (which \<open>Ck_at\<close> supplies) is upgraded
  to operator-norm continuity via \<open>continuous_on_blinfun_componentwise\<close>.
\<close>

theory Ck1_C1_Bridge
  imports Higher_Differentiability_Multi
begin

text \<open>
  The canonical blinfun derivative of a map that is differentiable at every
  point of \<open>W\<close>.
\<close>

definition Dblinfun :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'b)"
  where "Dblinfun G z = Blinfun (frechet_derivative G (at z))"

lemma blinfun_apply_Dblinfun:
  assumes "G differentiable (at z)"
  shows "blinfun_apply (Dblinfun G z) = frechet_derivative G (at z)"
proof -
  have "bounded_linear (frechet_derivative G (at z))"
    using assms frechet_derivative_works has_derivative_bounded_linear by blast
  thus ?thesis
    unfolding Dblinfun_def by (rule bounded_linear_Blinfun_apply)
qed

text \<open>
  \<open>C\<^sup>1\<close> at a point unpacks to: differentiability at the point, and
  per-direction continuity of the Fréchet derivative at the point.
\<close>

lemma Ck1_atD:
  assumes "Ck_at (Suc 0) G x"
  shows "G differentiable (at x)"
    and "\<And>v. continuous (at x) (\<lambda>y. frechet_derivative G (at y) v)"
  using assms by auto

text \<open>
  Main bridge: from \<open>C\<^sup>1\<close> on the open set \<open>W\<close>, the canonical witness
  \<^const>\<open>Dblinfun\<close> is a blinfun-valued derivative of \<open>G\<close> at every point of \<open>W\<close>
  and is continuous on \<open>W\<close> — precisely the \<open>derG\<close>/\<open>contG'\<close> interface of the
  regular-value engine.
\<close>

lemma Ck1_on_imp_has_derivative_blinfun:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Ck_on (Suc 0) G W"
  shows "\<And>z. z \<in> W \<Longrightarrow> (G has_derivative blinfun_apply (Dblinfun G z)) (at z)"
proof -
  fix z assume z: "z \<in> W"
  have "Ck_at (Suc 0) G z"
    using assms z by (simp add: Ck_on_def)
  hence diff: "G differentiable (at z)" by (rule Ck1_atD)
  show "(G has_derivative blinfun_apply (Dblinfun G z)) (at z)"
    using diff by (simp add: blinfun_apply_Dblinfun frechet_derivative_works)
qed

lemma Ck1_on_imp_continuous_Dblinfun:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Ck_on (Suc 0) G W"
  shows "continuous_on W (Dblinfun G)"
proof (rule continuous_on_blinfun_componentwise)
  fix i :: 'a assume i: "i \<in> Basis"
  have W_open: "open W" using assms by (simp add: Ck_on_def)
  \<comment> \<open>per-direction continuity of the Fréchet derivative, on all of \<open>W\<close>\<close>
  have cont_dir: "continuous_on W (\<lambda>z. frechet_derivative G (at z) i)"
  proof (rule continuous_at_imp_continuous_on, rule ballI)
    fix z assume z: "z \<in> W"
    have "Ck_at (Suc 0) G z" using assms z by (simp add: Ck_on_def)
    thus "continuous (at z) (\<lambda>z. frechet_derivative G (at z) i)"
      by (rule Ck1_atD(2))
  qed
  \<comment> \<open>on \<open>W\<close> the blinfun component agrees with that derivative\<close>
  have eq: "\<And>z. z \<in> W \<Longrightarrow> blinfun_apply (Dblinfun G z) i = frechet_derivative G (at z) i"
  proof -
    fix z assume z: "z \<in> W"
    have "Ck_at (Suc 0) G z" using assms z by (simp add: Ck_on_def)
    hence "G differentiable (at z)" by (rule Ck1_atD)
    thus "blinfun_apply (Dblinfun G z) i = frechet_derivative G (at z) i"
      by (simp add: blinfun_apply_Dblinfun)
  qed
  show "continuous_on W (\<lambda>z. blinfun_apply (Dblinfun G z) i)"
    by (rule continuous_on_eq[OF cont_dir]) (simp add: eq)
qed

text \<open>The two halves packaged together, in the engine's exact shape.\<close>

theorem Ck1_on_imp_C1_interface:
  fixes G :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "Ck_on (Suc 0) G W"
  shows "(\<forall>z\<in>W. (G has_derivative blinfun_apply (Dblinfun G z)) (at z))
       \<and> continuous_on W (Dblinfun G)"
  using Ck1_on_imp_has_derivative_blinfun[OF assms]
        Ck1_on_imp_continuous_Dblinfun[OF assms]
  by blast

end
