theory Scratch_sc2
  imports "Applied_Math_Nonemptiness.Nonemptiness_Paper"
begin

definition regular_value_on ::
  "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
where
  "regular_value_on f S y \<longleftrightarrow>
     (\<forall>x\<in>S. f x = y \<longrightarrow> (\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f'))"

lemma regular_value_onI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = y \<Longrightarrow> (\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f')"
  shows "regular_value_on f S y"
  using assms unfolding regular_value_on_def by blast

lemma rank_defect_of_not_inj:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'m::{finite,wellorder}"
  assumes lin: "linear f" and n_inj: "\<not> inj f"
  shows "rank (matrix f) < CARD('m)"
proof -
  have "rank (matrix f) \<noteq> CARD('m)"
    using n_inj lin by (auto simp: full_rank_injective)
  moreover have "rank (matrix f) \<le> CARD('m)"
    by (rule order_trans[OF rank_bound]) simp
  ultimately show ?thesis
    by linarith
qed

lemma exists_nonzero_in_kernel_with_fst0:
  fixes L :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
  assumes lin: "linear L"
    and not_surj_slice: "\<not> surj (\<lambda>w::real^2. L (0, w))"
  shows "\<exists>w::real^2. w \<noteq> 0 \<and> L (0, w) = 0"
proof -
  interpret Llin: linear L by (rule lin)
  have lin_slice: "linear (\<lambda>w::real^2. L (0, w))"
  proof (rule linearI)
    fix x y :: "real^2"
    show "L (0, x + y) = L (0, x) + L (0, y)"
    proof -
      have "L (0, x + y) = L ((0, x) + (0, y))"
        by simp
      also have "\<dots> = L (0, x) + L (0, y)"
        by (rule Llin.add)
      finally show ?thesis .
    qed
    fix r :: real and x :: "real^2"
    show "L (0, r *\<^sub>R x) = r *\<^sub>R L (0, x)"
    proof -
      have "L (0, r *\<^sub>R x) = L (r *\<^sub>R (0, x))"
        by simp
      also have "\<dots> = r *\<^sub>R L (0, x)"
        by (rule Llin.scale)
      finally show ?thesis.
    qed
  qed
  have "\<not> inj (\<lambda>w::real^2. L (0, w))"
  proof
    assume "inj (\<lambda>w::real^2. L (0, w))"
    then have "surj (\<lambda>w::real^2. L (0, w))"
      using lin_slice
      by (simp add: linear_injective_imp_surjective)
    with not_surj_slice show False by blast
  qed
  then have "\<exists>w::real^2. w \<noteq> 0 \<and> (\<lambda>w::real^2. L (0, w)) w = 0"
    using lin_slice
    unfolding linear_injective_0[OF lin_slice]
    by blast
  then show ?thesis by blast
qed

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

lemma projection_deriv_not_inj:
  fixes Gp :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2)"
    and Dphi :: "(real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2))"
  assumes slice: "\<not> surj (\<lambda>w::real^2. blinfun_apply Gp (0, w))"
    and rng: "range (blinfun_apply Dphi) = {z. blinfun_apply Gp z = 0}"
  shows "\<not> inj (\<lambda>v. fst (blinfun_apply Dphi v))"
proof -
  have linGp: "linear (blinfun_apply Gp)"
    by (simp add: blinfun.bounded_linear_right bounded_linear.linear)
  obtain w :: "real^2" where w0: "w \<noteq> 0" and wker: "blinfun_apply Gp (0, w) = 0"
    using exists_nonzero_in_kernel_with_fst0[OF linGp slice] by blast
  have "(0, w) \<in> range (blinfun_apply Dphi)" using wker rng by simp
  then obtain v where v: "blinfun_apply Dphi v = (0, w)" by (metis rangeE)
  have vneq: "v \<noteq> 0"
  proof
    assume "v = 0"
    hence "blinfun_apply Dphi v = 0" by (simp add: blinfun.zero_right)
    hence "snd (blinfun_apply Dphi v) = 0" by simp
    with v have "w = 0" by simp
    thus False using w0 by simp
  qed
  have a: "fst (blinfun_apply Dphi v) = 0" using v by simp
  have b: "fst (blinfun_apply Dphi 0) = 0" by (simp add: blinfun.zero_right)
  from a b vneq show "\<not> inj (\<lambda>v. fst (blinfun_apply Dphi v))" by (metis injD)
qed

text \<open>The countable chart cover, KEEPING the derivative Dphi and its tangent property
  (range Dphi = ker DG).  To be proven by mirroring countable_chart_cover_of_levelset_2d
  with regular_value_local_chart (which exposes Dphi) in place of the local_chart lemma.\<close>

lemma countable_chart_cover_with_Dphi:
  fixes V :: "(real^'m::{finite,wellorder}) set" and \<Omega> :: "(real^2) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
    and G' :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
  defines "M \<equiv> {q \<in> V\<times>\<Omega>. G q = 0}"
  assumes openV: "open V" and openOmega: "open \<Omega>"
    and derG: "\<And>z. z \<in> V\<times>\<Omega> \<Longrightarrow> (G has_derivative blinfun_apply (G' z)) (at z)"
    and contG': "continuous_on (V\<times>\<Omega>) G'"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "\<exists>(U::nat \<Rightarrow> (real^'m::{finite,wellorder}) set)
            (charts::nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2))))
            (Dphi::nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2))))).
           (\<forall>i. open (U i) \<and> charts i ` (U i) \<subseteq> M \<and>
                (\<forall>u\<in>U i. (charts i has_derivative blinfun_apply (Dphi i u)) (at u)
                         \<and> range (blinfun_apply (Dphi i u)) = {w. blinfun_apply (G' (charts i u)) w = 0})) \<and>
           M \<subseteq> (\<Union>i. charts i ` (U i))"
proof -
  have Wopen: "open (V\<times>\<Omega>)" using openV openOmega by (rule open_Times)
  have loc:
    "\<And>p. p \<in> M \<Longrightarrow> \<exists>(U::(real^'m::{finite,wellorder}) set) (u0::real^'m::{finite,wellorder})
            (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))
            (g::((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> real^'m::{finite,wellorder})
            (D\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2)))).
      open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and> \<phi> differentiable_on U \<and> \<phi> ` U \<subseteq> M \<and>
      openin (top_of_set M) (\<phi> ` U) \<and> homeomorphism U (\<phi> ` U) \<phi> g \<and>
      (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
      (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u)) = {w. blinfun_apply (G' (\<phi> u)) w = 0})"
  proof -
    fix p assume pM: "p \<in> M"
    have pVO: "p \<in> V\<times>\<Omega>" using pM unfolding M_def by simp
    have Gp0: "G p = 0" using pM unfolding M_def by simp
    have regp: "surj (blinfun_apply (G' p))"
    proof -
      obtain f' :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
        where hf': "(G has_derivative f') (at p within (V\<times>\<Omega>))" and sf': "surj f'"
        using reg0 pVO Gp0 unfolding regular_value_on_def by fastforce
      have "at p within (V\<times>\<Omega>) = at p" using pVO Wopen
        by (meson at_within_open) 
      with hf' have hf2: "(G has_derivative f') (at p)" by simp
      have h78: "(G has_derivative blinfun_apply (G' p)) (at p)" using derG pVO by simp
      have "blinfun_apply (G' p) = f'" by (rule has_derivative_unique[OF h78 hf2])
      with sf' show ?thesis by simp
    qed
    show "\<exists>(U::(real^'m::{finite,wellorder}) set) (u0::real^'m::{finite,wellorder})
            (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))
            (g::((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> real^'m::{finite,wellorder})
            (D\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2)))).
      open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and> \<phi> differentiable_on U \<and> \<phi> ` U \<subseteq> M \<and>
      openin (top_of_set M) (\<phi> ` U) \<and> homeomorphism U (\<phi> ` U) \<phi> g \<and>
      (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
      (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u)) = {w. blinfun_apply (G' (\<phi> u)) w = 0})"
      unfolding M_def
      by (rule regular_value_local_chart[OF Wopen pVO Gp0 derG contG' regp])
  qed

  define \<F> where
    "\<F> \<equiv> {S. \<exists>p\<in>M. \<exists>(U::(real^'m::{finite,wellorder}) set) (u0::real^'m::{finite,wellorder})
          (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))
          (g::((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> real^'m::{finite,wellorder})
          (D\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2)))).
          open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and> \<phi> differentiable_on U \<and> \<phi> ` U \<subseteq> M \<and>
          openin (top_of_set M) (\<phi> ` U) \<and> homeomorphism U (\<phi> ` U) \<phi> g \<and>
          (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
          (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u)) = {w. blinfun_apply (G' (\<phi> u)) w = 0}) \<and>
          S = \<phi> ` U}"
  have F_openin: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S" by (auto simp: \<F>_def)
  have coverF: "M \<subseteq> \<Union>\<F>"
  proof
    fix p assume pM: "p \<in> M"
    from loc[OF pM] obtain
      U :: "(real^'m::{finite,wellorder}) set" and u0 :: "real^'m::{finite,wellorder}"
      and \<phi> :: "real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2))"
      and g :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> real^'m::{finite,wellorder}"
      and D\<phi> :: "real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2)))"
    where w: "open U" "u0 \<in> U" "\<phi> u0 = p" "\<phi> differentiable_on U" "\<phi> ` U \<subseteq> M"
        "openin (top_of_set M) (\<phi> ` U)" "homeomorphism U (\<phi> ` U) \<phi> g"
        "\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)"
        "\<forall>u\<in>U. range (blinfun_apply (D\<phi> u)) = {w. blinfun_apply (G' (\<phi> u)) w = 0}"
      by blast
    have "\<phi> ` U \<in> \<F>" unfolding \<F>_def using pM w by blast
    moreover have "p \<in> \<phi> ` U" using w(2,3) by blast
    ultimately show "p \<in> \<Union>\<F>" by blast
  qed

  obtain \<F>' :: "((real^'m::{finite,wellorder}) \<times> (real^2)) set set"
    where F'sub: "\<F>' \<subseteq> \<F>" and F'cnt: "countable \<F>'" and coverF': "M \<subseteq> \<Union>\<F>'"
  proof -
    have scM: "second_countable (top_of_set M)"
      using second_countable_subtopology[OF second_countable_euclidean, of M] by simp
    have lindM: "Lindelof_space (top_of_set M)"
      using second_countable_imp_Lindelof_space[OF scM] .
    have hopen: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S" using F_openin by blast
    have hUnionF: "\<Union>\<F> = topspace (top_of_set M)"
    proof
      show "\<Union>\<F> \<subseteq> topspace (top_of_set M)" by (meson Sup_le_iff hopen openin_subset)
      show "topspace (top_of_set M) \<subseteq> \<Union>\<F>" using coverF by simp
    qed
    have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<F> \<and> \<Union>\<V> = topspace (top_of_set M)"
      using lindM hopen hUnionF unfolding Lindelof_space_def
      by (meson Top1_Ch3.countable_def countableE)
    then obtain \<V> :: "((real^'m::{finite,wellorder}) \<times> (real^2)) set set"
      where Vcnt: "countable \<V>" and Vsub: "\<V> \<subseteq> \<F>" and VU: "\<Union>\<V> = topspace (top_of_set M)" by blast
    have "M \<subseteq> \<Union>\<V>" using VU by simp
    thus ?thesis using that Vsub Vcnt by blast
  qed

  show ?thesis
  proof (cases "M = {}")
    case True
    define U0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set" where "U0 \<equiv> (\<lambda>_. {})"
    define charts0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))"
      where "charts0 \<equiv> (\<lambda>_ _. (0, 0))"
    define Dphi0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2))))"
      where "Dphi0 \<equiv> (\<lambda>_ _. 0)"
    show ?thesis
      by (intro exI[of _ U0] exI[of _ charts0] exI[of _ Dphi0]) (simp add: U0_def True)
  next
    case False
    have F'ne: "\<F>' \<noteq> {}" using coverF' False by auto
    obtain e :: "nat \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)) set"
      where eimg: "\<Union>(range e) = \<Union>\<F>'" and erng: "\<And>n. e n \<in> \<F>'"
    proof -
      let ?e = "from_nat_into \<F>'"
      have eimg: "\<Union>(range ?e) = \<Union>\<F>'"
        by (metis F'cnt F'ne range_from_nat_into top1_countable_nonempty_eq_image_nat uncountable_def)
      have erng: "\<And>n. ?e n \<in> \<F>'" using F'ne by (simp add: from_nat_into)
      show ?thesis by (rule that[of ?e]) (auto simp: eimg intro: erng)
    qed
    have ex_pick: "\<forall>i. \<exists>(U::(real^'m::{finite,wellorder}) set)
              (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))
              (D\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2)))).
              open U \<and> e i = \<phi> ` U \<and> \<phi> ` U \<subseteq> M \<and>
              (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
              (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u)) = {w. blinfun_apply (G' (\<phi> u)) w = 0})"
    proof
      fix i :: nat
      from erng[of i] F'sub have "e i \<in> \<F>" by blast
      then obtain p :: "(real^'m::{finite,wellorder}) \<times> (real^2)"
        and U :: "(real^'m::{finite,wellorder}) set" and u0 :: "real^'m::{finite,wellorder}"
        and \<phi> :: "real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2))"
        and g :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> real^'m::{finite,wellorder}"
        and D\<phi> :: "real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2)))"
        where w: "open U" "\<phi> ` U \<subseteq> M"
          "\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)"
          "\<forall>u\<in>U. range (blinfun_apply (D\<phi> u)) = {w. blinfun_apply (G' (\<phi> u)) w = 0}"
          "e i = \<phi> ` U"
        unfolding \<F>_def by blast
      show "\<exists>(U::(real^'m::{finite,wellorder}) set)
              (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))
              (D\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2)))).
              open U \<and> e i = \<phi> ` U \<and> \<phi> ` U \<subseteq> M \<and>
              (\<forall>u\<in>U. (\<phi> has_derivative blinfun_apply (D\<phi> u)) (at u)) \<and>
              (\<forall>u\<in>U. range (blinfun_apply (D\<phi> u)) = {w. blinfun_apply (G' (\<phi> u)) w = 0})"
        apply (rule_tac x=U in exI)
        apply (rule_tac x="\<phi>" in exI)
        apply (rule_tac x="D\<phi>" in exI)
        using w by simp
        
    qed
    obtain U0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set"
      and \<phi>0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))"
      and D\<phi>0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2))))"
      where pick: "\<And>i. open (U0 i) \<and> e i = \<phi>0 i ` (U0 i) \<and> \<phi>0 i ` (U0 i) \<subseteq> M \<and>
              (\<forall>u\<in>U0 i. (\<phi>0 i has_derivative blinfun_apply (D\<phi>0 i u)) (at u)) \<and>
              (\<forall>u\<in>U0 i. range (blinfun_apply (D\<phi>0 i u)) = {w. blinfun_apply (G' (\<phi>0 i u)) w = 0})"
      using ex_pick unfolding choice_iff by blast
    show ?thesis
    proof (intro exI[of _ U0] exI[of _ \<phi>0] exI[of _ D\<phi>0] conjI)
      show "\<forall>i. open (U0 i) \<and> \<phi>0 i ` (U0 i) \<subseteq> M \<and>
                (\<forall>u\<in>U0 i. (\<phi>0 i has_derivative blinfun_apply (D\<phi>0 i u)) (at u) \<and>
                          range (blinfun_apply (D\<phi>0 i u)) = {w. blinfun_apply (G' (\<phi>0 i u)) w = 0})"
        using pick by blast
      have "M \<subseteq> \<Union>\<F>'" using coverF' .
      also have "\<Union>\<F>' = (\<Union>i. \<phi>0 i ` (U0 i))" using eimg pick by auto
      finally show "M \<subseteq> (\<Union>i. \<phi>0 i ` (U0 i))" .
    qed
  qed
qed


lemma slice_linear:
  "linear (\<lambda>w::real^2. blinfun_apply F (0::real^'m::{finite,wellorder}, w))"
proof -
  have "linear (\<lambda>w::real^2. (0::real^'m::{finite,wellorder}, w))"
    by (auto simp: linear_iff plus_prod_def scaleR_prod_def)
  moreover have "linear (blinfun_apply F)"
    by (rule bounded_linear.linear[OF blinfun.bounded_linear_right])
  ultimately show ?thesis using linear_compose by (force simp: o_def)
qed

lemma crit0_sigma_compact_helper:
  fixes charts :: "real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2))"
    and G' :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    and U :: "(real^'m::{finite,wellorder}) set"
    and W :: "((real^'m::{finite,wellorder}) \<times> (real^2)) set"
  assumes openU: "open U" and cci: "continuous_on U charts"
    and sub: "charts ` U \<subseteq> W" and cgW: "continuous_on W G'"
  shows "\<exists>K::nat \<Rightarrow> (real^'m::{finite,wellorder}) set. (\<forall>n. compact (K n)) \<and>
           {u \<in> U. \<not> surj (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))} = (\<Union>n. K n)"
proof -
  have GC: "continuous_on U (\<lambda>u. G' (charts u))"
    using continuous_on_compose2[OF cgW cci sub] by (simp add: o_def)
  have ent: "continuous_on U (\<lambda>u. blinfun_apply (G' (charts u)) z)" for z
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_blinfun_apply GC continuous_on_const])
  have det_eq: "\<And>u. det (matrix (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w)))
        = blinfun_apply (G' (charts u)) (0, axis 1 1) $ 1 * blinfun_apply (G' (charts u)) (0, axis 2 1) $ 2
        - blinfun_apply (G' (charts u)) (0, axis 2 1) $ 1 * blinfun_apply (G' (charts u)) (0, axis 1 1) $ 2"
    by (simp add: det_2 matrix_def)
  have detc: "continuous_on U (\<lambda>u. det (matrix (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))))"
  proof -
    have e2: "continuous_on U (\<lambda>u. blinfun_apply (G' (charts u)) z $ i)" for z i
      by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth ent])
    show ?thesis unfolding det_eq by (intro continuous_intros e2)
  qed
  have surj_det: "surj (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))
                \<longleftrightarrow> det (matrix (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))) \<noteq> 0" for u
  proof -
    have "surj (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))
        \<longleftrightarrow> inj (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))"
      using linear_injective_imp_surjective[OF slice_linear]
            linear_surjective_imp_injective[OF slice_linear] by blast
    thus ?thesis using det_nz_iff_inj[OF slice_linear] by blast
  qed
  have crit_eq: "{u \<in> U. \<not> surj (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))}
               = {u \<in> U. det (matrix (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))) = 0}"
    by (auto simp: surj_det)
  have "closedin (top_of_set U)
          {u \<in> U. det (matrix (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))) = 0}"
    by (rule continuous_closedin_preimage_constant[OF detc])
  with crit_eq have cl: "closedin (top_of_set U)
          {u \<in> U. \<not> surj (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))}" by simp
  obtain T where T: "closed T"
      "{u \<in> U. \<not> surj (\<lambda>w::real^2. blinfun_apply (G' (charts u)) (0, w))} = U \<inter> T"
    using closedin_closed[THEN iffD1, OF cl] by blast
  show ?thesis unfolding T(2) by (rule rel_closed_open_sigma_compact[OF openU T(1)])
qed

lemma core_2d_strong:
  fixes V :: "(real^'m::{finite,wellorder}) set" and \<Omega> :: "(real^2) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
    and G' :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
  assumes openV: "open V" and openOmega: "open \<Omega>"
    and derG: "\<And>z. z \<in> V\<times>\<Omega> \<Longrightarrow> (G has_derivative blinfun_apply (G' z)) (at z)"
    and contG': "continuous_on (V\<times>\<Omega>) G'"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "\<exists>(charts::nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2))))
            (Crit0::nat \<Rightarrow> (real^'m::{finite,wellorder}) set)
            (D0::nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder})))).
           {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
               (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
             \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit0 i)) \<and>
           (\<forall>i x. x \<in> Crit0 i \<longrightarrow>
              ((fst \<circ> charts i) has_derivative (blinfun_apply (D0 i x))) (at x within Crit0 i)) \<and>
           (\<forall>i x. x \<in> Crit0 i \<longrightarrow> rank (matrix (blinfun_apply (D0 i x))) < CARD('m)) \<and>
           (\<forall>i. \<exists>K::nat \<Rightarrow> (real^'m::{finite,wellorder}) set. (\<forall>n. compact (K n)) \<and> Crit0 i = (\<Union>n. K n))"
proof -
  obtain U :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set"
     and charts :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))"
     and Dphi :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L ((real^'m::{finite,wellorder}) \<times> (real^2))))"
   where
    cov: "\<forall>i. open (U i) \<and> charts i ` (U i) \<subseteq> {q \<in> V\<times>\<Omega>. G q = 0} \<and>
              (\<forall>u\<in>U i. (charts i has_derivative blinfun_apply (Dphi i u)) (at u)
                       \<and> range (blinfun_apply (Dphi i u)) = {w. blinfun_apply (G' (charts i u)) w = 0})" and
    ccov: "{q \<in> V\<times>\<Omega>. G q = 0} \<subseteq> (\<Union>i. charts i ` (U i))"
    using countable_chart_cover_with_Dphi[OF openV openOmega derG contG' reg0] by blast
  have cder: "\<And>i u. u \<in> U i \<Longrightarrow> (charts i has_derivative blinfun_apply (Dphi i u)) (at u)" using cov by blast
  have crng: "\<And>i u. u \<in> U i \<Longrightarrow> range (blinfun_apply (Dphi i u)) = {w. blinfun_apply (G' (charts i u)) w = 0}" using cov by blast
  have openUi: "\<And>i. open (U i)" using cov by blast
  define D0 where "D0 = (\<lambda>i u. Blinfun fst o\<^sub>L Dphi i u)"
  define Crit0 where "Crit0 = (\<lambda>i. {u \<in> U i. \<not> surj (\<lambda>w::real^2. blinfun_apply (G' (charts i u)) (0, w))})"
  have Dapply: "\<And>i u. blinfun_apply (D0 i u) = (\<lambda>v. fst (blinfun_apply (Dphi i u) v))"
    by (simp add: D0_def blinfun_compose.rep_eq bounded_linear_fst bounded_linear_Blinfun_apply, auto)
  have linD0: "\<And>i u. linear (blinfun_apply (D0 i u))"
    by (simp add: blinfun.bounded_linear_right bounded_linear.linear)
  show ?thesis
  proof (intro exI[of _ charts] exI[of _ Crit0] exI[of _ D0] conjI)
    show "{x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
               (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
             \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit0 i))"
    proof
      fix x assume "x \<in> {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
               (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}"
      then obtain \<omega> where xV: "x \<in> V" and wO: "\<omega> \<in> \<Omega>" and Gxw: "G (x,\<omega>) = 0"
        and nbad: "\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>)" by blast
      have xwVO: "(x,\<omega>) \<in> V\<times>\<Omega>" using xV wO by simp
      have xwM: "(x,\<omega>) \<in> {q \<in> V\<times>\<Omega>. G q = 0}" using xwVO Gxw by simp
      then obtain i u where iu: "u \<in> U i" and cu: "charts i u = (x,\<omega>)" using ccov by auto
      have slice: "\<not> surj (\<lambda>w::real^2. blinfun_apply (G' (x,\<omega>)) (0,w))"
      proof
        assume sj: "surj (\<lambda>w::real^2. blinfun_apply (G' (x,\<omega>)) (0,w))"
        have aff: "((\<lambda>u::real^2. (x,u)) has_derivative (\<lambda>w. (0,w))) (at \<omega> within \<Omega>)"
          by (auto intro!: derivative_eq_intros)
        have "(G has_derivative blinfun_apply (G' (x,\<omega>))) (at (x,\<omega>))" using derG xwVO by simp
        hence "(G has_derivative blinfun_apply (G' (x,\<omega>))) (at (x,\<omega>) within (\<lambda>u. (x,u)) ` \<Omega>)"
          using has_derivative_at_withinI by blast
        from has_derivative_in_compose[OF aff this]
        have "((\<lambda>u. G (x,u)) has_derivative (\<lambda>w. blinfun_apply (G' (x,\<omega>)) (0,w))) (at \<omega> within \<Omega>)"
          by (simp add: o_def)
        with sj nbad show False by blast
      qed
      have uCrit: "u \<in> Crit0 i" using slice iu cu by (simp add: Crit0_def)
      have "x = (fst \<circ> charts i) u" using cu by (simp add: o_def)
      thus "x \<in> (\<Union>i. (fst \<circ> charts i) ` (Crit0 i))" using uCrit by blast
    qed
  next
    show "\<forall>i x. x \<in> Crit0 i \<longrightarrow> ((fst \<circ> charts i) has_derivative blinfun_apply (D0 i x)) (at x within Crit0 i)"
    proof (intro allI impI)
      fix i x assume "x \<in> Crit0 i"
      hence xU: "x \<in> U i" by (simp add: Crit0_def)
      have "((\<lambda>z. fst (charts i z)) has_derivative (\<lambda>v. fst (blinfun_apply (Dphi i x) v))) (at x)"
        by (rule bounded_linear.has_derivative[OF bounded_linear_fst cder[OF xU]])
      hence "((fst \<circ> charts i) has_derivative blinfun_apply (D0 i x)) (at x)"
        by (simp add: Dapply o_def)
      thus "((fst \<circ> charts i) has_derivative blinfun_apply (D0 i x)) (at x within Crit0 i)"
        by (rule has_derivative_at_withinI)
    qed
  next
    show "\<forall>i x. x \<in> Crit0 i \<longrightarrow> rank (matrix (blinfun_apply (D0 i x))) < CARD('m)"
    proof (intro allI impI)
      fix i x assume xC: "x \<in> Crit0 i"
      hence xU: "x \<in> U i" by (simp add: Crit0_def)
      have ns: "\<not> surj (\<lambda>w::real^2. blinfun_apply (G' (charts i x)) (0, w))"
        using xC by (simp add: Crit0_def)
      have "\<not> inj (\<lambda>v. fst (blinfun_apply (Dphi i x) v))"
        using crng[OF xU] by (intro projection_deriv_not_inj[where Gp="G' (charts i x)"]) (use ns in auto)
      hence "\<not> inj (blinfun_apply (D0 i x))" by (simp add: Dapply)
      thus "rank (matrix (blinfun_apply (D0 i x))) < CARD('m)"
        by (rule rank_defect_of_not_inj[OF linD0])
    qed
  next
    show "\<forall>i. \<exists>K::nat \<Rightarrow> (real^'m::{finite,wellorder}) set. (\<forall>n. compact (K n)) \<and> Crit0 i = (\<Union>n. K n)"
    proof (intro allI)
      fix i
      have cci: "continuous_on (U i) (charts i)"
      proof (rule continuous_at_imp_continuous_on, rule ballI)
        fix u assume "u \<in> U i"
        thus "continuous (at u) (charts i)" using cder has_derivative_continuous by blast
      qed
      have sub: "charts i ` (U i) \<subseteq> V\<times>\<Omega>" using cov by blast
      show "\<exists>K::nat \<Rightarrow> (real^'m::{finite,wellorder}) set. (\<forall>n. compact (K n)) \<and> Crit0 i = (\<Union>n. K n)"
        unfolding Crit0_def by (rule crit0_sigma_compact_helper[OF openUi cci sub contG'])
    qed
  qed
qed

end
