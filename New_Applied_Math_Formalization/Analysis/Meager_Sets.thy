section \<open>Nowhere dense and meager sets\<close>

theory Meager_Sets
  imports
    Munkres_Baire_Bridge
begin

definition nowhere_dense :: "'a::topological_space set \<Rightarrow> bool" where
  "nowhere_dense A \<longleftrightarrow> interior (closure A) = {}"

definition meager :: "'a::topological_space set \<Rightarrow> bool" where
  "meager A \<longleftrightarrow>
     (\<exists>E :: nat \<Rightarrow> 'a set. A \<subseteq> (\<Union>n. E n) \<and> (\<forall>n. nowhere_dense (E n)))"

lemma nowhere_dense_empty [simp]: "nowhere_dense ({} :: 'a::topological_space set)"
  by (simp add: nowhere_dense_def)

lemma meager_empty [simp]: "meager ({} :: 'a::topological_space set)"
  unfolding meager_def
  by (meson empty_subsetI nowhere_dense_empty) 

lemma meager_subset:
  fixes A B :: "'a::topological_space set"
  assumes "A \<subseteq> B" and "meager B"
  shows "meager A"
  using assms unfolding meager_def by blast

lemma meager_Un:
  fixes A B :: "'a::topological_space set"
  assumes "meager A" and "meager B"
  shows "meager (A \<union> B)"
proof -
  obtain E :: "nat \<Rightarrow> 'a set"
    where hE: "A \<subseteq> (\<Union>n. E n)" and hEn: "\<forall>n. nowhere_dense (E n)"
    using assms(1) unfolding meager_def by blast
  obtain F :: "nat \<Rightarrow> 'a set"
    where hF: "B \<subseteq> (\<Union>n. F n)" and hFn: "\<forall>n. nowhere_dense (F n)"
    using assms(2) unfolding meager_def by blast
  define G :: "nat \<Rightarrow> 'a set" where
    "G n = (if even n then E (n div 2) else F (n div 2))" for n
  have "(A \<union> B) \<subseteq> (\<Union>n. G n)"
  proof
    fix x assume "x \<in> A \<union> B"
    then show "x \<in> (\<Union>n. G n)"
    proof
      assume "x \<in> A"
      then obtain n where "x \<in> E n"
        using hE by blast
      then have "x \<in> G (2 * n)"
        by (simp add: G_def)
      then show "x \<in> (\<Union>n. G n)"
        by blast
    next
      assume "x \<in> B"
      then obtain n where "x \<in> F n"
        using hF by blast
      then have "x \<in> G (Suc (2 * n))"
        by (simp add: G_def)
      then show "x \<in> (\<Union>n. G n)"
        by blast
    qed
  qed
  moreover have "\<forall>n. nowhere_dense (G n)"
    using hEn hFn by (simp add: G_def)
  ultimately show ?thesis
    unfolding meager_def by blast
qed

lemma meager_Union_nat:
  fixes A :: "nat \<Rightarrow> 'a::topological_space set"
  assumes "\<And>n. meager (A n)"
  shows "meager (\<Union>n. A n)"
proof -
  have "\<forall>n. \<exists>E :: nat \<Rightarrow> 'a set.
      A n \<subseteq> (\<Union>m. E m) \<and> (\<forall>m. nowhere_dense (E m))"
    using assms unfolding meager_def by blast
  then obtain E :: "nat \<Rightarrow> nat \<Rightarrow> 'a set"
    where hE: "\<forall>n. A n \<subseteq> (\<Union>m. E n m) \<and> (\<forall>m. nowhere_dense (E n m))"
    by metis
  define F :: "nat \<Rightarrow> 'a set" where
    "F k = (case prod_decode k of (n, m) \<Rightarrow> E n m)" for k
  have "(\<Union>n. A n) \<subseteq> (\<Union>k. F k)"
  proof
    fix x assume "x \<in> (\<Union>n. A n)"
    then obtain n where hx: "x \<in> A n"
      by blast
    then obtain m where "x \<in> E n m"
      using hE by blast
    then have "x \<in> F (prod_encode (n, m))"
      by (simp add: F_def)
    then show "x \<in> (\<Union>k. F k)"
      by blast
  qed
  moreover have "\<forall>k. nowhere_dense (F k)"
    using hE by (auto simp: F_def split: prod.splits)
  ultimately show ?thesis
    unfolding meager_def by blast
qed

lemma nowhere_dense_subset:
  fixes A B :: "'a::topological_space set"
  assumes sub: "A \<subseteq> B" and nd: "nowhere_dense B"
  shows "nowhere_dense A"
proof -
  have "interior (closure A) \<subseteq> interior (closure B)"
    by (intro interior_mono closure_mono sub)
  thus ?thesis using nd unfolding nowhere_dense_def by auto
qed

lemma meager_nowhere_dense:
  fixes A :: "'a::topological_space set"
  assumes "nowhere_dense A"
  shows "meager A"
  using assms unfolding meager_def by (intro exI[of _ "\<lambda>_. A"]) auto

lemma meager_Union_finite:
  fixes A :: "'i \<Rightarrow> 'a::topological_space set"
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> meager (A i)"
  shows "meager (\<Union>i\<in>I. A i)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case by simp
next
  case (insert i I)
  have "meager ((\<Union>j\<in>insert i I. A j)) \<longleftrightarrow> meager (A i \<union> (\<Union>j\<in>I. A j))"
    by auto
  moreover have "meager (A i \<union> (\<Union>j\<in>I. A j))"
    using insert by (intro meager_Un) auto
  ultimately show ?case
    by simp
qed

subsection \<open>A nonempty open set is not meager\<close>

lemma open_nonempty_not_meager:
  fixes U :: "'a::{real_normed_vector,heine_borel} set"
  assumes "open U" and "U \<noteq> {}"
  shows "\<not> meager U"
proof
  assume hU_meager: "meager U"
  obtain E :: "nat \<Rightarrow> 'a set"
    where hCover: "U \<subseteq> (\<Union>n. E n)" and hND: "\<forall>n. nowhere_dense (E n)"
    using hU_meager unfolding meager_def by blast

  define D :: "nat \<Rightarrow> 'a set" where
    "D n = U - closure (E n)" for n

  have hTopU: "is_topology_on U (subspace_topology UNIV top1_open_sets U)"
    by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) simp
  have hBaireU: "top1_baire_on U (subspace_topology UNIV top1_open_sets U)"
    by (rule top1_baire_on_open_subspace[OF assms(1)])

  have hD_props:
    "\<forall>n. D n \<in> subspace_topology UNIV top1_open_sets U \<and>
         D n \<subseteq> U \<and>
         top1_densein_on U (subspace_topology UNIV top1_open_sets U) (D n)"
  proof
    fix n
    have hDn_open_sub:
      "D n \<in> subspace_topology UNIV top1_open_sets U"
      unfolding D_def
      by (auto simp: subspace_topology_def top1_open_sets_def)
    have hDn_sub: "D n \<subseteq> U"
      by (simp add: D_def)
    have hDn_dense:
      "top1_densein_on U (subspace_topology UNIV top1_open_sets U) (D n)"
    proof (rule iffD2[OF top1_densein_on_iff_intersects_nonempty_open[OF hTopU hDn_sub]])
      show "\<forall>W. W \<in> subspace_topology UNIV top1_open_sets U \<and> W \<subseteq> U \<and> W \<noteq> {}
          \<longrightarrow> intersects W (D n)"
      proof (intro allI impI)
        fix W
        assume hW: "W \<in> subspace_topology UNIV top1_open_sets U \<and> W \<subseteq> U \<and> W \<noteq> {}"
        have hW_openin: "openin (top_of_set U) W"
          using hW by (simp add: munkres_subspace_open_iff)
        have hW_open: "open W"
          by (rule openin_top_of_set_imp_open[OF assms(1) hW_openin])
        have hW_nonempty: "W \<noteq> {}"
          using hW by blast
        have hW_sub: "W \<subseteq> U"
          using hW by blast
        show "intersects W (D n)"
        proof (rule ccontr)
          assume "\<not> intersects W (D n)"
          then have hDisj: "W \<inter> D n = {}"
            unfolding intersects_def by blast
          have hW_closure: "W \<subseteq> closure (E n)"
            using hDisj hW_sub by (auto simp: D_def)
          then have "W \<subseteq> interior (closure (E n))"
            by (rule interior_maximal[OF _ hW_open])
          with hND hW_nonempty show False
            by (auto simp: nowhere_dense_def)
        qed
      qed
    qed
    show "D n \<in> subspace_topology UNIV top1_open_sets U \<and>
          D n \<subseteq> U \<and>
          top1_densein_on U (subspace_topology UNIV top1_open_sets U) (D n)"
      using hDn_open_sub hDn_sub hDn_dense by blast
  qed

  have "intersects U (\<Inter>n. D n)"
  proof (rule top1_baire_dense_open_intersects_nonempty_open[OF hTopU hBaireU])
    show "U \<in> subspace_topology UNIV top1_open_sets U"
      by (simp add: munkres_subspace_open_iff)
    show "U \<subseteq> U"
      by simp
    show "U \<noteq> {}"
      by (rule assms(2))
    show "\<forall>n. D n \<in> subspace_topology UNIV top1_open_sets U \<and>
          D n \<subseteq> U \<and> top1_densein_on U (subspace_topology UNIV top1_open_sets U) (D n)"
      by (rule hD_props)
  qed
  then obtain x where hxU: "x \<in> U" and hxD: "x \<in> (\<Inter>n. D n)"
    unfolding intersects_def by blast
  obtain n where hxEn: "x \<in> E n"
    using hCover hxU by blast
  have "x \<in> D n"
    using hxD by blast
  then have "x \<notin> closure (E n)"
    by (simp add: D_def)
  then show False
    using hxEn closure_subset by blast
qed

subsection \<open>Closed negligible sets\<close>

lemma nowhere_dense_closed_negligible:
  fixes A :: "'a::euclidean_space set"
  assumes "closed A" and "negligible A"
  shows "nowhere_dense A"
proof -
  have "interior A = {}"
  proof (rule ccontr)
    assume ne: "interior A \<noteq> {}"
    have "\<not> negligible (interior A)"
      by (rule open_not_negligible[OF open_interior ne])
    moreover have "negligible (interior A)"
      by (rule negligible_subset[OF assms(2) interior_subset])
    ultimately show False by blast
  qed
  with assms(1) show ?thesis
    by (simp only: nowhere_dense_def closure_closed)
qed

lemma meager_negligible_closed_cover:
  fixes A :: "'a::euclidean_space set"
  assumes "A \<subseteq> (\<Union>n::nat. K n)"
    and "\<And>n. closed (K n)" and "\<And>n. negligible (K n)"
  shows "meager A"
proof -
  have "meager (\<Union>n. K n)"
  proof (rule meager_Union_nat)
    fix n
    show "meager (K n)"
      by (rule meager_nowhere_dense[OF nowhere_dense_closed_negligible[OF assms(2) assms(3)]])
  qed
  then show ?thesis
    using assms(1) meager_subset by blast
qed

subsection \<open>Homeomorphic images\<close>

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

end
