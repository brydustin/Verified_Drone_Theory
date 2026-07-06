section \<open>The formal-series local inverse of a real-analytic map (majorant method)\<close>

text \<open>
  This theory constructs, for a real-analytic self-map \<open>f\<close> of a Euclidean space with
  \<open>f 0 = 0\<close> and \<open>Df(0) = id\<close>, a \<^emph>\<open>convergent\<close> power series \<open>h\<close> with \<open>f (h y) = y\<close> near \<open>0\<close> ---
  the analytic core of the multivariate analytic inverse/implicit function theorem.

  Method (classical majorants, organized to reuse the \<open>Real_Analytic\<close> machinery):

  \<^item> Write \<open>f = id - \<phi>\<close> with \<open>\<phi>\<close> analytic, \<open>\<phi> 0 = 0\<close>, \<open>D\<phi>(0) = 0\<close> (coefficients \<open>b\<phi>\<close> vanish
    in degrees \<open>\<le> 1\<close>).  A right inverse must satisfy the fixed-point equation
    \<open>h y = y + \<phi> (h y)\<close>.
  \<^item> On coefficient families this is \<open>c = cId + comp\<^sub>b\<^sub>\<phi> c\<close> where \<open>comp\<close> is the CANONICAL
    series-composition operator (iterated Cauchy products \<open>ccauchy\<close>/\<open>cpow\<close> along a fixed
    enumeration of the basis).  Because \<open>b\<phi>\<close> starts in degree 2 and \<open>c\<close> has no constant
    term, the degree-\<open>d\<close> output depends only on input degrees \<open>< d\<close> (the locality lemmas),
    so the equation has a unique formal solution \<open>cfix\<close> built by stages.
  \<^item> Convergence: the per-degree \<open>\<ell>\<^sup>1\<close> profiles \<open>A d = \<Sum>\<^bsub>deg \<gamma> = d\<^esub> norm (cfix \<gamma>)\<close> obey the
    convolution recursion \<open>A \<le> e\<^sub>1 + \<Sum>\<^sub>k m\<^sub>k A\<^sup>\<circledast>\<^sup>k\<close>; a Gou\"ezel-style bootstrap on the partial
    weighted sums \<open>W\<^sub>N = \<Sum>\<^bsub>d\<le>N\<^esub> A d \<sigma>\<^sup>d\<close> shows \<open>W\<^sub>N \<le> 2n\<sigma>\<close> for small \<open>\<sigma>\<close>, i.e. a \<open>majle\<close>
    bound for \<open>cfix\<close>.
  \<^item> The function \<open>h = \<Sum> cfix\<close> then satisfies \<open>h y = y + \<phi> (h y)\<close> by the dominated-Fubini
    rearrangement (\<open>series_on_majdom_vec\<close>), hence \<open>f (h y) = y\<close>.
\<close>

theory Real_Analytic_Inverse
  imports "Applied_Math_Analytic.Real_Analytic"
begin

subsection \<open>A fixed enumeration of the Euclidean basis\<close>

definition basis_list :: "'a::euclidean_space list" where
  "basis_list = (SOME l. set l = (Basis::'a set) \<and> distinct l)"

lemma basis_list:
  "set (basis_list::'a::euclidean_space list) = (Basis::'a set)"
  "distinct (basis_list::'a::euclidean_space list)"
proof -
  obtain l :: "'a list" where l: "set l = (Basis::'a set) \<and> distinct l"
    using finite_distinct_list[OF finite_Basis] by blast
  have "set (basis_list::'a list) = (Basis::'a set) \<and> distinct (basis_list::'a list)"
    unfolding basis_list_def by (rule someI[of _ l]) (rule l)
  thus "set (basis_list::'a list) = (Basis::'a set)"
       "distinct (basis_list::'a list)" by simp_all
qed

subsection \<open>Unit multi-indices and the concrete identity coefficient family\<close>

definition unit_idx :: "'a::euclidean_space \<Rightarrow> ('a \<Rightarrow> nat)" where
  "unit_idx b = (\<lambda>x. if x = b then 1 else 0)"

lemma unit_idx_in_ra_idx: "b \<in> Basis \<Longrightarrow> unit_idx b \<in> ra_idx"
  by (auto simp: unit_idx_def ra_idx_def)

lemma ra_deg_unit_idx: "b \<in> Basis \<Longrightarrow> ra_deg (unit_idx b) = 1"
  by (simp add: ra_deg_def unit_idx_def sum.remove[where x = b])

lemma inj_on_unit_idx: "inj_on unit_idx (Basis :: 'a::euclidean_space set)"
proof (rule inj_onI)
  fix b c :: 'a
  assume "b \<in> Basis" "c \<in> Basis" and eq: "unit_idx b = unit_idx c"
  have h: "unit_idx b b = unit_idx c b" using eq by simp
  show "b = c"
  proof (rule ccontr)
    assume "b \<noteq> c"
    thus False using h by (simp add: unit_idx_def)
  qed
qed

lemma unit_idx_neq_czero: "unit_idx b \<noteq> czero_idx"
proof
  assume "unit_idx b = czero_idx"
  hence "unit_idx b b = czero_idx b" by simp
  thus False by (simp add: unit_idx_def czero_idx_def)
qed

lemma ra_monomial_unit_idx:
  "b \<in> Basis \<Longrightarrow> ra_monomial y (unit_idx b) = y \<bullet> b" for y :: "'a::euclidean_space"
proof -
  assume b: "b \<in> Basis"
  have "ra_monomial y (unit_idx b) =
      (y \<bullet> b) ^ (unit_idx b b) * (\<Prod>c\<in>Basis - {b}. (y \<bullet> c) ^ (unit_idx b c))"
    using b by (simp add: ra_monomial_def prod.remove)
  also have "\<dots> = y \<bullet> b"
    by (simp add: unit_idx_def)
  finally show ?thesis .
qed

text \<open>Classification of the degree-one multi-indices.\<close>

lemma ra_deg_one_unit:
  fixes \<alpha> :: "'a::euclidean_space \<Rightarrow> nat"
  assumes a: "\<alpha> \<in> ra_idx" and d1: "ra_deg \<alpha> = 1"
  obtains b where "b \<in> Basis" "\<alpha> = unit_idx b"
proof -
  have s1: "(\<Sum>b\<in>(Basis::'a set). \<alpha> b) = 1"
    using d1 by (simp add: ra_deg_def)
  have "\<exists>b\<in>(Basis::'a set). \<alpha> b \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>b\<in>(Basis::'a set). \<alpha> b \<noteq> 0)"
    hence "(\<Sum>b\<in>(Basis::'a set). \<alpha> b) = 0" by simp
    thus False using s1 by simp
  qed
  then obtain b where b: "b \<in> Basis" and nz: "\<alpha> b \<noteq> 0" by blast
  have ble: "\<alpha> b \<le> 1"
  proof -
    have "\<alpha> b \<le> (\<Sum>c\<in>(Basis::'a set). \<alpha> c)"
      using b by (intro member_le_sum) auto
    thus ?thesis using s1 by simp
  qed
  have b1: "\<alpha> b = 1"
    using nz ble by simp
  have rest0: "(\<Sum>c\<in>Basis - {b}. \<alpha> c) = 0"
    using s1 b b1 by (simp add: sum.remove[where x = b])
  have z: "\<alpha> c = 0" if "c \<in> Basis" "c \<noteq> b" for c
  proof -
    have "\<alpha> c \<le> (\<Sum>c\<in>Basis - {b}. \<alpha> c)"
      using that by (intro member_le_sum) auto
    thus ?thesis using rest0 by simp
  qed
  have "\<alpha> = unit_idx b"
  proof (rule ext)
    fix x
    show "\<alpha> x = unit_idx b x"
    proof (cases "x \<in> Basis")
      case True thus ?thesis using b1 z by (auto simp: unit_idx_def)
    next
      case False
      hence "\<alpha> x = 0" using a by (auto simp: ra_idx_def)
      moreover have "x \<noteq> b" using False b by blast
      ultimately show ?thesis by (simp add: unit_idx_def)
    qed
  qed
  thus ?thesis using b that by blast
qed

text \<open>The concrete identity coefficient family: \<open>\<Sum>\<^sub>\<alpha> y\<^sup>\<alpha> (cId \<alpha>) = y\<close>.\<close>

definition cId :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a" where
  "cId = (\<lambda>\<alpha>. \<Sum>b\<in>Basis. if \<alpha> = unit_idx b then b else 0)"

lemma cId_unit: "b \<in> Basis \<Longrightarrow> cId (unit_idx b) = b"
proof -
  assume b: "b \<in> Basis"
  have "cId (unit_idx b) = (\<Sum>c\<in>Basis. if c = b then c else 0)"
    unfolding cId_def
    by (rule sum.cong[OF refl])
       (use b inj_on_unit_idx in \<open>auto simp: inj_on_def\<close>)
  also have "\<dots> = b"
    using b by simp
  finally show ?thesis .
qed

lemma cId_off_units: "\<alpha> \<notin> unit_idx ` Basis \<Longrightarrow> cId \<alpha> = 0"
  unfolding cId_def by (rule sum.neutral) auto

lemma cId_czero: "cId czero_idx = 0"
  by (rule cId_off_units, metis image_iff unit_idx_neq_czero)

lemma cId_deg: "cId \<alpha> \<noteq> 0 \<Longrightarrow> ra_deg \<alpha> = 1"
proof -
  assume nz: "cId \<alpha> \<noteq> 0"
  have "\<alpha> \<in> unit_idx ` Basis"
    using nz cId_off_units by blast
  then obtain b where "b \<in> Basis" "\<alpha> = unit_idx b" by blast
  thus "ra_deg \<alpha> = 1" by (simp add: ra_deg_unit_idx)
qed

lemma cId_series:
  fixes y :: "'a::euclidean_space"
  shows "((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R cId \<alpha>) has_sum y) ra_idx"
proof (rule has_sum_finite_neutralI)
  show "finite (unit_idx ` (Basis :: 'a set))"
    by simp
  show "unit_idx ` (Basis :: 'a set) \<subseteq> ra_idx"
    using unit_idx_in_ra_idx by blast
  have "(\<Sum>\<alpha>\<in>unit_idx ` Basis. ra_monomial y \<alpha> *\<^sub>R cId \<alpha>) =
      (\<Sum>b\<in>Basis. ra_monomial y (unit_idx b) *\<^sub>R cId (unit_idx b))"
    by (rule sum.reindex_cong[where l = unit_idx, OF inj_on_unit_idx refl]) simp
  also have "\<dots> = (\<Sum>b\<in>Basis. (y \<bullet> b) *\<^sub>R b)"
    by (rule sum.cong[OF refl]) (simp add: ra_monomial_unit_idx cId_unit)
  also have "\<dots> = y"
    by (simp add: euclidean_representation)
  finally show "y = (\<Sum>\<alpha>\<in>unit_idx ` Basis. ra_monomial y \<alpha> *\<^sub>R cId \<alpha>)"
    by simp
  show "\<And>\<alpha>. \<alpha> \<in> ra_idx - unit_idx ` Basis \<Longrightarrow> ra_monomial y \<alpha> *\<^sub>R cId \<alpha> = 0"
    by (simp add: cId_off_units)
qed

lemma norm_cId_le: "norm (cId \<alpha>) \<le> 1"
proof (cases "\<alpha> \<in> unit_idx ` Basis")
  case True
  then obtain b where b: "b \<in> Basis" and e: "\<alpha> = unit_idx b" by blast
  show ?thesis using b by (simp add: e cId_unit)
next
  case False
  thus ?thesis by (simp add: cId_off_units)
qed

subsection \<open>Cauchy-product support helpers\<close>

lemma lowI_ra_idx: "\<alpha> \<in> lowI \<gamma> \<Longrightarrow> \<alpha> \<in> ra_idx"
  by (simp add: lowI_def)

lemma self_in_lowI: "\<gamma> \<in> ra_idx \<Longrightarrow> \<gamma> \<in> lowI \<gamma>"
  by (simp add: lowI_def leI_def)

lemma czero_in_lowI: "\<gamma> \<in> ra_idx \<Longrightarrow> czero_idx \<in> lowI \<gamma>"
  by (simp add: lowI_def leI_def czero_idx_def czero_idx_in, simp add: ra_idx_def)

lemma subI_czero: "subI \<gamma> czero_idx = \<gamma>"
  by (simp add: subI_def czero_idx_def)

lemma subI_self: "subI \<gamma> \<gamma> = czero_idx"
  by (simp add: subI_def czero_idx_def)

lemma addI_subI: "\<alpha> \<in> lowI \<gamma> \<Longrightarrow> addI \<alpha> (subI \<gamma> \<alpha>) = \<gamma>"
proof (rule ext)
  fix b
  assume "\<alpha> \<in> lowI \<gamma>"
  hence "\<alpha> b \<le> \<gamma> b" by (simp add: lowI_def leI_def)
  thus "addI \<alpha> (subI \<gamma> \<alpha>) b = \<gamma> b" by (simp add: addI_def subI_def)
qed

lemma subI_addI: "subI (addI \<alpha> \<delta>) \<alpha> = \<delta>"
  by (rule ext) (simp add: addI_def subI_def)

lemma ra_deg_addI: "ra_deg (addI \<alpha> \<delta>) = ra_deg \<alpha> + ra_deg \<delta>"
  by (simp add: ra_deg_def addI_def sum.distrib)

lemma addI_in_lowI: "\<alpha> \<in> ra_idx \<Longrightarrow> \<alpha> \<in> lowI (addI \<alpha> \<delta>)"
  by (simp add: lowI_def leI_def addI_def)

lemma subI_deg_eq:
  assumes "\<alpha> \<in> lowI \<gamma>" and "ra_deg (subI \<gamma> \<alpha>) = 0" and "\<gamma> \<in> ra_idx"
  shows "\<alpha> = \<gamma>"
proof -
  have "subI \<gamma> \<alpha> \<in> ra_idx" using assms(3) by (rule idx_sub)
  hence sz: "subI \<gamma> \<alpha> = czero_idx" using assms(2) by (simp add: ra_deg_eq0_iff)
  have le: "\<gamma> b \<le> \<alpha> b" for b
  proof -
    have "subI \<gamma> \<alpha> b = czero_idx b" using sz by simp
    thus ?thesis by (simp add: subI_def czero_idx_def)
  qed
  have ge: "\<And>b. \<alpha> b \<le> \<gamma> b" using assms(1) by (simp add: lowI_def leI_def)
  show ?thesis by (rule ext) (use le ge le_antisym in blast)
qed

text \<open>The unit \<open>cone\<close> is a two-sided identity for the Cauchy product (on \<open>ra_idx\<close>).\<close>

lemma ccauchy_cone_right: "\<gamma> \<in> ra_idx \<Longrightarrow> ccauchy u cone \<gamma> = u \<gamma>"
proof -
  assume g: "\<gamma> \<in> ra_idx"
  have fin: "finite (lowI \<gamma>)" by (rule idx_lower_fin)
  have "ccauchy u cone \<gamma> = (\<Sum>\<alpha>\<in>lowI \<gamma>. u \<alpha> * cone (subI \<gamma> \<alpha>))"
    by (simp add: ccauchy_def)
  also have "\<dots> = (\<Sum>\<alpha>\<in>{\<gamma>}. u \<alpha> * cone (subI \<gamma> \<alpha>))"
  proof (rule sum.mono_neutral_right[OF fin])
    show "{\<gamma>} \<subseteq> lowI \<gamma>" using self_in_lowI[OF g] by blast
    show "\<forall>\<alpha>\<in>lowI \<gamma> - {\<gamma>}. u \<alpha> * cone (subI \<gamma> \<alpha>) = 0"
    proof
      fix \<alpha> assume a: "\<alpha> \<in> lowI \<gamma> - {\<gamma>}"
      have "subI \<gamma> \<alpha> \<noteq> czero_idx"
      proof
        assume "subI \<gamma> \<alpha> = czero_idx"
        hence "ra_deg (subI \<gamma> \<alpha>) = 0" by (simp add: ra_deg_def czero_idx_def)
        hence "\<alpha> = \<gamma>" using a g by (intro subI_deg_eq) auto
        thus False using a by blast
      qed
      thus "u \<alpha> * cone (subI \<gamma> \<alpha>) = 0" by (simp add: cone_def)
    qed
  qed
  also have "\<dots> = u \<gamma>"
    by (simp add: subI_self cone_def)
  finally show ?thesis .
qed

lemma ccauchy_cone_left: "\<gamma> \<in> ra_idx \<Longrightarrow> ccauchy cone v \<gamma> = v \<gamma>"
proof -
  assume g: "\<gamma> \<in> ra_idx"
  have fin: "finite (lowI \<gamma>)" by (rule idx_lower_fin)
  have "ccauchy cone v \<gamma> = (\<Sum>\<alpha>\<in>lowI \<gamma>. cone \<alpha> * v (subI \<gamma> \<alpha>))"
    by (simp add: ccauchy_def)
  also have "\<dots> = (\<Sum>\<alpha>\<in>{czero_idx}. cone \<alpha> * v (subI \<gamma> \<alpha>))"
  proof (rule sum.mono_neutral_right[OF fin])
    show "{czero_idx} \<subseteq> lowI \<gamma>" using czero_in_lowI[OF g] by blast
    show "\<forall>\<alpha>\<in>lowI \<gamma> - {czero_idx}. cone \<alpha> * v (subI \<gamma> \<alpha>) = 0"
      by (simp add: cone_def)
  qed
  also have "\<dots> = v \<gamma>"
    by (simp add: subI_czero cone_def)
  finally show ?thesis .
qed

subsection \<open>Valuation (vanishing below a degree) under Cauchy products\<close>

text \<open>\<open>vanish_below u p\<close>: the scalar family \<open>u\<close> has no coefficients of degree \<open>< p\<close>.\<close>

definition vanish_below :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "vanish_below u p \<longleftrightarrow> (\<forall>\<alpha>. \<alpha> \<in> ra_idx \<longrightarrow> ra_deg \<alpha> < p \<longrightarrow> u \<alpha> = 0)"

lemma vanish_below_0: "vanish_below u 0"
  by (simp add: vanish_below_def)

lemma vanish_below_mono: "vanish_below u p \<Longrightarrow> q \<le> p \<Longrightarrow> vanish_below u q"
  by (auto simp: vanish_below_def)

lemma vanish_below_cone: "vanish_below cone 0"
  by (rule vanish_below_0)

lemma ccauchy_vanish:
  assumes u: "vanish_below u p" and v: "vanish_below v q"
  shows "vanish_below (ccauchy u v) (p + q)"
  unfolding vanish_below_def
proof (intro allI impI)
  fix \<gamma> :: "'a \<Rightarrow> nat"
  assume g: "\<gamma> \<in> ra_idx" and dg: "ra_deg \<gamma> < p + q"
  have "ccauchy u v \<gamma> = (\<Sum>\<alpha>\<in>lowI \<gamma>. u \<alpha> * v (subI \<gamma> \<alpha>))"
    by (simp add: ccauchy_def)
  also have "\<dots> = 0"
  proof (rule sum.neutral, rule ballI)
    fix \<alpha> assume a: "\<alpha> \<in> lowI \<gamma>"
    have ara: "\<alpha> \<in> ra_idx" using a by (rule lowI_ra_idx)
    have dra: "subI \<gamma> \<alpha> \<in> ra_idx" using g by (rule idx_sub)
    have split: "ra_deg \<gamma> = ra_deg \<alpha> + ra_deg (subI \<gamma> \<alpha>)"
      using a by (rule ra_deg_split)
    have "ra_deg \<alpha> < p \<or> ra_deg (subI \<gamma> \<alpha>) < q"
      using dg split by linarith
    thus "u \<alpha> * v (subI \<gamma> \<alpha>) = 0"
      using u v ara dra by (auto simp: vanish_below_def)
  qed
  finally show "ccauchy u v \<gamma> = 0" .
qed

lemma cpow_vanish:
  assumes u: "vanish_below u 1"
  shows "vanish_below (cpow u n) n"
proof (induction n)
  case 0
  show ?case by (simp add: cpow_0 vanish_below_0)
next
  case (Suc n)
  have "vanish_below (ccauchy u (cpow u n)) (1 + n)"
    by (rule ccauchy_vanish[OF u Suc.IH])
  thus ?case by (simp add: cpow_Suc)
qed

subsection \<open>Degree locality of Cauchy products and powers\<close>

text \<open>If two pairs of families agree up to certain degrees (and have the stated
  valuations), their Cauchy products agree up to the corresponding degree.\<close>

lemma ccauchy_local:
  fixes u u' v v' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes up: "vanish_below u p" and up': "vanish_below u' p"
    and vq: "vanish_below v q" and vq': "vanish_below v' q"
    and uu': "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> Du \<Longrightarrow> u \<alpha> = u' \<alpha>"
    and vv': "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> Dv \<Longrightarrow> v \<delta> = v' \<delta>"
    and g: "\<gamma> \<in> ra_idx" and dgu: "ra_deg \<gamma> \<le> Du + q" and dgv: "ra_deg \<gamma> \<le> Dv + p"
  shows "ccauchy u v \<gamma> = ccauchy u' v' \<gamma>"
proof -
  have "(\<Sum>\<alpha>\<in>lowI \<gamma>. u \<alpha> * v (subI \<gamma> \<alpha>)) = (\<Sum>\<alpha>\<in>lowI \<gamma>. u' \<alpha> * v' (subI \<gamma> \<alpha>))"
  proof (rule sum.cong[OF refl])
    fix \<alpha> assume a: "\<alpha> \<in> lowI \<gamma>"
    have ara: "\<alpha> \<in> ra_idx" using a by (rule lowI_ra_idx)
    have dra: "subI \<gamma> \<alpha> \<in> ra_idx" using g by (rule idx_sub)
    have split: "ra_deg \<gamma> = ra_deg \<alpha> + ra_deg (subI \<gamma> \<alpha>)"
      using a by (rule ra_deg_split)
    show "u \<alpha> * v (subI \<gamma> \<alpha>) = u' \<alpha> * v' (subI \<gamma> \<alpha>)"
    proof (cases "ra_deg \<alpha> < p")
      case True
      thus ?thesis
        using up up' ara by (simp add: vanish_below_def)
    next
      case False
      note ap = False
      show ?thesis
      proof (cases "ra_deg (subI \<gamma> \<alpha>) < q")
        case True
        thus ?thesis
          using vq vq' dra by (simp add: vanish_below_def)
      next
        case False
        have da: "ra_deg \<alpha> \<le> Du"
          using ap False split dgu by linarith
        have dd: "ra_deg (subI \<gamma> \<alpha>) \<le> Dv"
          using ap False split dgv by linarith
        show ?thesis
          using uu'[OF ara da] vv'[OF dra dd] by simp
      qed
    qed
  qed
  thus ?thesis by (simp add: ccauchy_def)
qed

lemma cpow_local:
  fixes u u' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes u1: "vanish_below u 1" and u1': "vanish_below u' 1"
    and uu': "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> u \<alpha> = u' \<alpha>"
    and n1: "1 \<le> n"
    and g: "\<gamma> \<in> ra_idx" and dg: "ra_deg \<gamma> \<le> D + n - 1"
  shows "cpow u n \<gamma> = cpow u' n \<gamma>"
  using n1 g dg
proof (induction n arbitrary: \<gamma>)
  case 0
  thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "n = 0")
    case True
    have "cpow u (Suc 0) \<gamma> = ccauchy u cone \<gamma>"
      by (simp add: cpow_Suc cpow_0)
    also have "\<dots> = u \<gamma>" using Suc.prems(2) by (rule ccauchy_cone_right)
    also have "\<dots> = u' \<gamma>"
      using Suc.prems(2,3) True by (intro uu') simp_all
    also have "\<dots> = ccauchy u' cone \<gamma>"
      using Suc.prems(2) by (simp add: ccauchy_cone_right)
    also have "\<dots> = cpow u' (Suc 0) \<gamma>"
      by (simp add: cpow_Suc cpow_0)
    finally show ?thesis using True by simp
  next
    case False
    hence n1': "1 \<le> n" by simp
    have IH: "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> D + n - 1 \<Longrightarrow> cpow u n \<delta> = cpow u' n \<delta>"
      using Suc.IH n1' by blast
    have "ccauchy u (cpow u n) \<gamma> = ccauchy u' (cpow u' n) \<gamma>"
    proof (rule ccauchy_local[where p = 1 and q = n and Du = D and Dv = "D + n - 1"])
      show "vanish_below u 1" by (rule u1)
      show "vanish_below u' 1" by (rule u1')
      show "vanish_below (cpow u n) n" by (rule cpow_vanish[OF u1])
      show "vanish_below (cpow u' n) n" by (rule cpow_vanish[OF u1'])
      show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> u \<alpha> = u' \<alpha>" by (rule uu')
      show "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> D + n - 1 \<Longrightarrow> cpow u n \<delta> = cpow u' n \<delta>"
        by (rule IH)
      show "\<gamma> \<in> ra_idx" by (rule Suc.prems(2))
      show "ra_deg \<gamma> \<le> D + n" using Suc.prems(3) n1' by simp
      show "ra_deg \<gamma> \<le> (D + n - 1) + 1" using Suc.prems(3) n1' by simp
    qed
    thus ?thesis by (simp add: cpow_Suc)
  qed
qed

subsection \<open>Canonical monomial-composition coefficients along the basis list\<close>

text \<open>\<open>mcl c \<beta> l\<close> is the canonical coefficient family of \<open>y \<mapsto> \<Prod>b\<leftarrow>l. (H y \<bullet> b) ^ \<beta> b\<close>
  when \<open>c\<close> is a coefficient family for \<open>H\<close>: iterated Cauchy products of the component
  powers, folded along the fixed list \<open>l\<close>.  Unlike \<open>series_on_ra_monomial_compose\<close> this is
  a \<^emph>\<open>definition\<close>, so it can appear in a recursion.\<close>

fun mcl :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a list
              \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> real)" where
  "mcl c \<beta> [] = cone"
| "mcl c \<beta> (b # bs) = ccauchy (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (mcl c \<beta> bs)"

lemma mcl_series:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a" and H :: "'a \<Rightarrow> 'a"
  assumes VC: "\<And>y. dist y (0::'a) < r \<Longrightarrow>
                 ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R c \<alpha>) has_sum H y) ra_idx"
  shows "series_on (0::'a) r (mcl c \<beta> l) (\<lambda>y. \<Prod>b\<leftarrow>l. (H y \<bullet> b) ^ \<beta> b)"
proof (induction l)
  case Nil
  show ?case using series_on_one[of "0::'a" r] by simp
next
  case (Cons b bs)
  have VC': "\<And>y. dist y (0::'a) < r \<Longrightarrow>
               ((\<lambda>\<alpha>. ra_monomial (y - 0) \<alpha> *\<^sub>R c \<alpha>) has_sum H y) ra_idx"
    using VC by simp
  have comp: "series_on (0::'a) r (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<lambda>y. H y \<bullet> b)"
    by (rule series_on_component[OF VC'])
  have pow: "series_on (0::'a) r (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (\<lambda>y. (H y \<bullet> b) ^ \<beta> b)"
    by (rule series_on_power[OF comp])
  have "series_on (0::'a) r (ccauchy (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (mcl c \<beta> bs))
          (\<lambda>y. (H y \<bullet> b) ^ \<beta> b * (\<Prod>b'\<leftarrow>bs. (H y \<bullet> b') ^ \<beta> b'))"
    by (rule series_on_mult[OF pow Cons.IH])
  thus ?case by simp
qed

lemma mcl_vanish:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c czero_idx = 0"
  shows "vanish_below (mcl c \<beta> l) (sum_list (map \<beta> l))"
proof (induction l)
  case Nil
  show ?case by (simp add: vanish_below_0)
next
  case (Cons b bs)
  have comp1: "vanish_below (\<lambda>\<alpha>. c \<alpha> \<bullet> b) 1"
    unfolding vanish_below_def
  proof (intro allI impI)
    fix \<alpha> :: "'a \<Rightarrow> nat"
    assume "\<alpha> \<in> ra_idx" "ra_deg \<alpha> < 1"
    hence "\<alpha> = czero_idx" by (simp add: ra_deg_eq0_iff)
    thus "c \<alpha> \<bullet> b = 0" by (simp add: c0)
  qed
  have "vanish_below (ccauchy (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (mcl c \<beta> bs))
          (\<beta> b + sum_list (map \<beta> bs))"
    by (rule ccauchy_vanish[OF cpow_vanish[OF comp1] Cons.IH])
  thus ?case by simp
qed

lemma mcl_indep:
  fixes c c' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes z: "sum_list (map \<beta> l) = 0" and g: "\<gamma> \<in> ra_idx"
  shows "mcl c \<beta> l \<gamma> = mcl c' \<beta> l \<gamma>"
  using z g
proof (induction l arbitrary: \<gamma>)
  case Nil
  show ?case by simp
next
  case (Cons b bs)
  have b0: "\<beta> b = 0" and bs0: "sum_list (map \<beta> bs) = 0"
    using Cons.prems(1) by simp_all
  have "mcl c \<beta> (b # bs) \<gamma> = ccauchy cone (mcl c \<beta> bs) \<gamma>"
    by (simp add: b0 cpow_0)
  also have "\<dots> = mcl c \<beta> bs \<gamma>"
    using Cons.prems(2) by (rule ccauchy_cone_left)
  also have "\<dots> = mcl c' \<beta> bs \<gamma>"
    using bs0 Cons.prems(2) by (rule Cons.IH)
  also have "\<dots> = ccauchy cone (mcl c' \<beta> bs) \<gamma>"
    using Cons.prems(2) by (simp add: ccauchy_cone_left)
  also have "\<dots> = mcl c' \<beta> (b # bs) \<gamma>"
    by (simp add: b0 cpow_0)
  finally show ?case .
qed

lemma mcl_local:
  fixes c c' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c czero_idx = 0" and c0': "c' czero_idx = 0"
    and agree: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> c \<alpha> = c' \<alpha>"
    and g: "\<gamma> \<in> ra_idx"
    and pos: "1 \<le> sum_list (map \<beta> l)"
    and dg: "ra_deg \<gamma> \<le> D + sum_list (map \<beta> l) - 1"
  shows "mcl c \<beta> l \<gamma> = mcl c' \<beta> l \<gamma>"
  using pos dg g
proof (induction l arbitrary: \<gamma>)
  case Nil
  thus ?case by simp
next
  case (Cons b bs)
  define u where "u = (\<lambda>\<alpha>. c \<alpha> \<bullet> b)"
  define u' where "u' = (\<lambda>\<alpha>. c' \<alpha> \<bullet> b)"
  have u1: "vanish_below u 1"
    unfolding vanish_below_def u_def
  proof (intro allI impI)
    fix \<alpha> :: "'a \<Rightarrow> nat"
    assume "\<alpha> \<in> ra_idx" "ra_deg \<alpha> < 1"
    hence "\<alpha> = czero_idx" by (simp add: ra_deg_eq0_iff)
    thus "c \<alpha> \<bullet> b = 0" by (simp add: c0)
  qed
  have u1': "vanish_below u' 1"
    unfolding vanish_below_def u'_def
  proof (intro allI impI)
    fix \<alpha> :: "'a \<Rightarrow> nat"
    assume "\<alpha> \<in> ra_idx" "ra_deg \<alpha> < 1"
    hence "\<alpha> = czero_idx" by (simp add: ra_deg_eq0_iff)
    thus "c' \<alpha> \<bullet> b = 0" by (simp add: c0')
  qed
  have uu': "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> u \<alpha> = u' \<alpha>"
    unfolding u_def u'_def using agree by simp
  define vbs where "vbs = sum_list (map \<beta> bs)"
  show ?case
  proof (cases "\<beta> b = 0")
    case True
    have pos_bs: "1 \<le> vbs"
      using Cons.prems(1) True by (simp add: vbs_def)
    have dg_bs: "ra_deg \<gamma> \<le> D + vbs - 1"
      using Cons.prems(2) True by (simp add: vbs_def)
    have "mcl c \<beta> (b # bs) \<gamma> = ccauchy cone (mcl c \<beta> bs) \<gamma>"
      by (simp add: True cpow_0)
    also have "\<dots> = mcl c \<beta> bs \<gamma>"
      using Cons.prems(3) by (rule ccauchy_cone_left)
    also have "\<dots> = mcl c' \<beta> bs \<gamma>"
      using pos_bs dg_bs Cons.prems(3) unfolding vbs_def by (rule Cons.IH)
    also have "\<dots> = ccauchy cone (mcl c' \<beta> bs) \<gamma>"
      using Cons.prems(3) by (simp add: ccauchy_cone_left)
    also have "\<dots> = mcl c' \<beta> (b # bs) \<gamma>"
      by (simp add: True cpow_0)
    finally show ?thesis .
  next
    case False
    hence bb1: "1 \<le> \<beta> b" by simp
    show ?thesis
    proof (cases "vbs = 0")
      case True
      \<comment> \<open>the tail is \<open>c\<close>-independent; only the head power carries locality\<close>
      have tail_eq: "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> mcl c \<beta> bs \<delta> = mcl c' \<beta> bs \<delta>"
        using True unfolding vbs_def by (intro mcl_indep)
      have "ccauchy (cpow u (\<beta> b)) (mcl c \<beta> bs) \<gamma>
              = ccauchy (cpow u' (\<beta> b)) (mcl c' \<beta> bs) \<gamma>"
      proof (rule ccauchy_local[where p = "\<beta> b" and q = 0
              and Du = "D + \<beta> b - 1" and Dv = "ra_deg \<gamma>"])
        show "vanish_below (cpow u (\<beta> b)) (\<beta> b)" by (rule cpow_vanish[OF u1])
        show "vanish_below (cpow u' (\<beta> b)) (\<beta> b)" by (rule cpow_vanish[OF u1'])
        show "vanish_below (mcl c \<beta> bs) 0" by (rule vanish_below_0)
        show "vanish_below (mcl c' \<beta> bs) 0" by (rule vanish_below_0)
        show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D + \<beta> b - 1 \<Longrightarrow>
                cpow u (\<beta> b) \<alpha> = cpow u' (\<beta> b) \<alpha>"
          by (rule cpow_local[OF u1 u1' uu' bb1])
        show "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> ra_deg \<gamma> \<Longrightarrow>
                mcl c \<beta> bs \<delta> = mcl c' \<beta> bs \<delta>"
          using tail_eq by blast
        show "\<gamma> \<in> ra_idx" by (rule Cons.prems(3))
        show "ra_deg \<gamma> \<le> (D + \<beta> b - 1) + 0"
          using Cons.prems(2) True
          using vbs_def by fastforce
        show "ra_deg \<gamma> \<le> ra_deg \<gamma> + \<beta> b" by simp
      qed
      thus ?thesis unfolding u_def u'_def by simp
    next
      case False
      hence vbs1: "1 \<le> vbs" by simp
      have "ccauchy (cpow u (\<beta> b)) (mcl c \<beta> bs) \<gamma>
              = ccauchy (cpow u' (\<beta> b)) (mcl c' \<beta> bs) \<gamma>"
      proof (rule ccauchy_local[where p = "\<beta> b" and q = vbs
              and Du = "D + \<beta> b - 1" and Dv = "D + vbs - 1"])
        show "vanish_below (cpow u (\<beta> b)) (\<beta> b)" by (rule cpow_vanish[OF u1])
        show "vanish_below (cpow u' (\<beta> b)) (\<beta> b)" by (rule cpow_vanish[OF u1'])
        show "vanish_below (mcl c \<beta> bs) vbs"
          unfolding vbs_def
          by (simp add: c0 mcl_vanish)
        show "vanish_below (mcl c' \<beta> bs) vbs"
          unfolding vbs_def
          by (simp add: c0' mcl_vanish)
        show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D + \<beta> b - 1 \<Longrightarrow>
                cpow u (\<beta> b) \<alpha> = cpow u' (\<beta> b) \<alpha>"
          by (rule cpow_local[OF u1 u1' uu' bb1])
        show "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> D + vbs - 1 \<Longrightarrow>
                mcl c \<beta> bs \<delta> = mcl c' \<beta> bs \<delta>"
          using Cons.IH vbs1 unfolding vbs_def by blast
        show "\<gamma> \<in> ra_idx" by (rule Cons.prems(3))
        show "ra_deg \<gamma> \<le> (D + \<beta> b - 1) + vbs"
          using Cons.prems(2) bb1 by (simp add: vbs_def)
        show "ra_deg \<gamma> \<le> (D + vbs - 1) + \<beta> b"
          using Cons.prems(2) vbs1 by (simp add: vbs_def)
      qed
      thus ?thesis unfolding u_def u'_def by simp
    qed
  qed
qed

text \<open>The packaged composition coefficients: canonical coefficients of
  \<open>y \<mapsto> ra_monomial (H y) \<beta>\<close>.\<close>

definition mono_co :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat)
                         \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> real)" where
  "mono_co c \<beta> = mcl c \<beta> basis_list"

lemma sum_list_basis_ra_deg:
  "sum_list (map \<beta> (basis_list::'a::euclidean_space list)) = ra_deg \<beta>"
proof -
  have "sum_list (map \<beta> (basis_list::'a list)) = (\<Sum>b\<in>set (basis_list::'a list). \<beta> b)"
    by (rule sum_list_distinct_conv_sum_set[OF basis_list(2)])
  also have "\<dots> = (\<Sum>b\<in>(Basis::'a set). \<beta> b)"
    by (simp add: basis_list(1))
  finally show ?thesis by (simp add: ra_deg_def)
qed

lemma mono_co_series:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a" and H :: "'a \<Rightarrow> 'a"
  assumes VC: "\<And>y. dist y (0::'a) < r \<Longrightarrow>
                 ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R c \<alpha>) has_sum H y) ra_idx"
  shows "series_on (0::'a) r (mono_co c \<beta>) (\<lambda>y. ra_monomial (H y) \<beta>)"
proof -
  have base: "series_on (0::'a) r (mcl c \<beta> basis_list)
                (\<lambda>y. \<Prod>b\<leftarrow>(basis_list::'a list). (H y \<bullet> b) ^ \<beta> b)"
    by (rule mcl_series[OF VC])
  have eq: "(\<Prod>b\<leftarrow>(basis_list::'a list). (H y \<bullet> b) ^ \<beta> b) = ra_monomial (H y) \<beta>" for y
  proof -
    have "ra_monomial (H y) \<beta> = (\<Prod>b\<in>set (basis_list::'a list). (H y \<bullet> b) ^ \<beta> b)"
      by (simp add: ra_monomial_def basis_list(1))
    also have "\<dots> = (\<Prod>b\<leftarrow>(basis_list::'a list). (H y \<bullet> b) ^ \<beta> b)"
      by (rule prod.distinct_set_conv_list[OF basis_list(2)])
    finally show ?thesis by simp
  qed
  show ?thesis
    using base unfolding series_on_def eq mono_co_def by simp
qed

lemma mono_co_vanish:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c czero_idx = 0"
  shows "vanish_below (mono_co c \<beta>) (ra_deg \<beta>)"
  unfolding mono_co_def
  by (metis c0 mcl_vanish sum_list_basis_ra_deg)

lemma mono_co_zero_below_degree:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c czero_idx = 0"
    and g: "\<gamma> \<in> ra_idx"
    and lt: "ra_deg \<gamma> < ra_deg \<beta>"
  shows "mono_co c \<beta> \<gamma> = 0"
  by (meson c0 g lt mono_co_vanish vanish_below_def)


lemma mono_co_local:
  fixes c c' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c czero_idx = 0" and c0': "c' czero_idx = 0"
    and agree: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> c \<alpha> = c' \<alpha>"
    and g: "\<gamma> \<in> ra_idx"
    and pos: "1 \<le> ra_deg \<beta>"
    and dg: "ra_deg \<gamma> \<le> D + ra_deg \<beta> - 1"
  shows "mono_co c \<beta> \<gamma> = mono_co c' \<beta> \<gamma>"
  unfolding mono_co_def
  by (metis agree c0 c0' dg g mcl_local pos sum_list_basis_ra_deg)


subsection \<open>Convolution algebra on scalar degree sequences\<close>

definition nconv :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real)" where
  "nconv A B = (\<lambda>d. \<Sum>i\<le>d. A i * B (d - i))"

definition ndelta :: "nat \<Rightarrow> real" where
  "ndelta = (\<lambda>d. if d = 0 then 1 else 0)"

primrec nconvpow :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real)" where
  "nconvpow A 0 = ndelta"
| "nconvpow A (Suc k) = nconv A (nconvpow A k)"

lemma nconv_delta_right: "nconv A ndelta = A"
proof (rule ext)
  fix d :: nat
  have "nconv A ndelta d = (\<Sum>i\<le>d. if i = d then A d else 0)"
    unfolding nconv_def ndelta_def
    by (rule sum.cong[OF refl]) auto
  also have "\<dots> = A d"
    by (simp add: if_distrib)
  finally show "nconv A ndelta d = A d" .
qed

lemma nconv_delta_left: "nconv ndelta B = B"
proof (rule ext)
  fix d :: nat
  have "nconv ndelta B d = (\<Sum>i\<le>d. if i = 0 then B d else 0)"
    unfolding nconv_def ndelta_def
    by (rule sum.cong[OF refl]) auto
  also have "\<dots> = B d"
    by simp
  finally show "nconv ndelta B d = B d" .
qed

lemma nconv_nonneg:
  assumes "\<And>i. 0 \<le> A i" and "\<And>i. 0 \<le> B i"
  shows "0 \<le> nconv A B d"
  unfolding nconv_def by (intro sum_nonneg mult_nonneg_nonneg assms)

lemma ndelta_nonneg: "0 \<le> ndelta d"
  by (simp add: ndelta_def)

lemma nconvpow_nonneg:
  assumes "\<And>i. 0 \<le> A i"
  shows "0 \<le> nconvpow A k d"
proof (induction k arbitrary: d)
  case 0
  show ?case by (simp add: ndelta_nonneg)
next
  case (Suc k)
  show ?case by (simp add: nconv_nonneg[OF assms Suc.IH])
qed

lemma nconv_mono:
  assumes AA': "\<And>i. A i \<le> A' i" and BB': "\<And>i. B i \<le> B' i"
    and Ann: "\<And>i. 0 \<le> A i" and Bnn': "\<And>i. 0 \<le> B' i"
  shows "nconv A B d \<le> nconv A' B' d"
  unfolding nconv_def
  by (rule sum_mono, metis AA' Ann BB' Bnn' dual_order.trans
      landau_omega.R_linear mult_le_0_iff mult_mono' mult_nonneg_nonneg)


lemma nconvpow_mono_base:
  assumes AA': "\<And>i. A i \<le> A' i" and Ann: "\<And>i. 0 \<le> A i"
  shows "nconvpow A k d \<le> nconvpow A' k d"
proof (induction k arbitrary: d)
  case 0
  show ?case by simp
next
  case (Suc k)
  have Ann': "\<And>i. 0 \<le> A' i"
    using Ann AA' order_trans by blast
  show ?case
    unfolding nconvpow.simps
    by (rule nconv_mono[OF AA' Suc.IH Ann nconvpow_nonneg[OF Ann']])
qed

text \<open>The triangular double-sum exchange, used for associativity and the key
  partial-sum estimate.\<close>

lemma sum_triangle_exchange:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'c::comm_monoid_add"
  shows "(\<Sum>d\<le>N. \<Sum>i\<le>d. f i (d - i)) = (\<Sum>i\<le>N. \<Sum>e\<le>N - i. f i e)"
proof -
  have L: "(\<Sum>d\<le>N. \<Sum>i\<le>d. f i (d - i)) =
      (\<Sum>(d, i)\<in>(SIGMA d:{..N}. {..d}). f i (d - i))"
    by (rule sum.Sigma[OF finite_atMost]) simp
  have R: "(\<Sum>i\<le>N. \<Sum>e\<le>N - i. f i e) =
      (\<Sum>(i, e)\<in>(SIGMA i:{..N}. {..N - i}). f i e)"
    by (rule sum.Sigma[OF finite_atMost]) simp
  have "(\<Sum>(d, i)\<in>(SIGMA d:{..N}. {..d}). f i (d - i)) =
      (\<Sum>(i, e)\<in>(SIGMA i:{..N}. {..N - i}). f i e)"
  proof (rule sum.reindex_bij_witness[where
        i = "\<lambda>(i, e). (i + e, i)" and j = "\<lambda>(d, i). (i, d - i)"])
    fix a assume a: "a \<in> (SIGMA d:{..N}. {..d})"
    obtain d i where di: "a = (d, i)" by (cases a)
    have dN: "d \<le> N" and idd: "i \<le> d" using a di by auto
    show "(case case a of (d, i) \<Rightarrow> (i, d - i) of (i, e) \<Rightarrow> (i + e, i)) = a"
      using di idd by simp
    show "(case a of (d, i) \<Rightarrow> (i, d - i)) \<in> (SIGMA i:{..N}. {..N - i})"
      using di dN idd by auto

  next
    fix b assume b: "b \<in> (SIGMA i:{..N}. {..N - i})"
    obtain i e where ie: "b = (i, e)" by (cases b)
    have iN: "i \<le> N" and eN: "e \<le> N - i" using b ie by auto
    show "(case case b of (i, e) \<Rightarrow> (i + e, i) of (d, i) \<Rightarrow> (i, d - i)) = b"
      using ie by simp
    show "(case b of (i, e) \<Rightarrow> (i + e, i)) \<in> (SIGMA d:{..N}. {..d})"
      using ie iN eN by auto
  next
    show "\<And>a. a \<in> Sigma {..N} atMost \<Longrightarrow>
       (case case a of (d, i) \<Rightarrow> (i, d - i) of (i, e) \<Rightarrow> f i e) = (case a of (d, i) \<Rightarrow> f i (d - i))"
      by fastforce
  qed
  thus ?thesis using L R by simp
qed

lemma nconv_assoc: "nconv (nconv A B) C = nconv A (nconv B C)"
proof (rule ext)
  fix d :: nat
  have "nconv (nconv A B) C d = (\<Sum>m\<le>d. (\<Sum>i\<le>m. A i * B (m - i)) * C (d - m))"
    by (simp add: nconv_def)
  also have "\<dots> = (\<Sum>m\<le>d. \<Sum>i\<le>m. A i * B (m - i) * C (d - m))"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>i\<le>d. \<Sum>e\<le>d - i. A i * B e * C (d - (i + e)))"
    using sum_triangle_exchange[of "\<lambda>i e. A i * B e * C (d - (i + e))" d]
    by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>i\<le>d. A i * (\<Sum>e\<le>d - i. B e * C (d - i - e)))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = nconv A (nconv B C) d"
    by (simp add: nconv_def)
  finally show "nconv (nconv A B) C d = nconv A (nconv B C) d" .
qed

lemma nconvpow_add: "nconv (nconvpow A m) (nconvpow A k) = nconvpow A (m + k)"
proof (induction m)
  case 0
  show ?case by (simp add: nconv_delta_left)
next
  case (Suc m)
  have "nconv (nconvpow A (Suc m)) (nconvpow A k)
          = nconv A (nconv (nconvpow A m) (nconvpow A k))"
    by (simp add: nconv_assoc)
  also have "\<dots> = nconv A (nconvpow A (m + k))"
    by (simp add: Suc.IH)
  also have "\<dots> = nconvpow A (Suc m + k)"
    by simp
  finally show ?case .
qed

lemma nconvpow_vanish:
  assumes A0: "A 0 = 0" and dk: "d < k"
  shows "nconvpow A k d = 0"
  using dk
proof (induction k arbitrary: d)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have "nconv A (nconvpow A k) d = (\<Sum>i\<le>d. A i * nconvpow A k (d - i))"
    by (simp add: nconv_def)
  also have "\<dots> = 0"
  proof (rule sum.neutral, rule ballI)
    fix i assume i: "i \<in> {..d}"
    show "A i * nconvpow A k (d - i) = 0"
    proof (cases "i = 0")
      case True
      thus ?thesis by (simp add: A0)
    next
      case False
      have "d - i < k" using i False Suc.prems by simp
      thus ?thesis by (simp add: Suc.IH)
    qed
  qed
  finally show ?case by simp
qed

text \<open>The key partial-sum estimate: a weighted partial sum of a convolution power is
  dominated by the corresponding power of a (shorter) weighted partial sum.\<close>

lemma nconvpow_partial_sum_le:
  fixes A :: "nat \<Rightarrow> real" and x :: real
  assumes Ann: "\<And>i. 0 \<le> A i" and A0: "A 0 = 0" and x0: "0 \<le> x" and k1: "1 \<le> k"
  shows "(\<Sum>d\<le>N. nconvpow A k d * x ^ d) \<le> (\<Sum>i=1..N + 1 - k. A i * x ^ i) ^ k"
  using k1
proof (induction k arbitrary: N)
  case 0
  thus ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "k = 0")
    case True
    have "(\<Sum>d\<le>N. nconvpow A (Suc 0) d * x ^ d) = (\<Sum>d\<le>N. A d * x ^ d)"
      by (simp add: nconv_delta_right)
    also have "\<dots> = (\<Sum>d=1..N. A d * x ^ d)"
    proof -
      have "{..N} = insert 0 {1..N}" by auto
      thus ?thesis by (simp add: A0)
    qed
    finally show ?thesis using True by simp
  next
    case False
    hence k1': "1 \<le> k" by simp
    have expand: "(\<Sum>d\<le>N. nconvpow A (Suc k) d * x ^ d)
        = (\<Sum>i\<le>N. \<Sum>e\<le>N - i. A i * x ^ i * (nconvpow A k e * x ^ e))"
    proof -
      have "(\<Sum>d\<le>N. nconvpow A (Suc k) d * x ^ d)
          = (\<Sum>d\<le>N. \<Sum>i\<le>d. A i * nconvpow A k (d - i) * x ^ d)"
        by (simp add: nconv_def sum_distrib_right)
      also have "\<dots> = (\<Sum>d\<le>N. \<Sum>i\<le>d. A i * x ^ i * (nconvpow A k (d - i) * x ^ (d - i)))"
      proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
        fix d i :: nat assume "d \<in> {..N}" "i \<in> {..d}"
        hence "i + (d - i) = d" by simp
        hence "x ^ d = x ^ i * x ^ (d - i)"
          by (simp flip: power_add)
        thus "A i * nconvpow A k (d - i) * x ^ d
                = A i * x ^ i * (nconvpow A k (d - i) * x ^ (d - i))"
          by (simp add: algebra_simps)
      qed
      also have "\<dots> = (\<Sum>i\<le>N. \<Sum>e\<le>N - i. A i * x ^ i * (nconvpow A k e * x ^ e))"
        by (rule sum_triangle_exchange)
      finally show ?thesis .
    qed
    define S where "S = (\<Sum>i=1..N + 1 - Suc k. A i * x ^ i)"
    have Snn: "0 \<le> S"
      unfolding S_def by (intro sum_nonneg mult_nonneg_nonneg Ann zero_le_power x0)
    have inner_bound: "(\<Sum>e\<le>N - i. nconvpow A k e * x ^ e) \<le> S ^ k"
      if i: "1 \<le> i" "i \<le> N" and nz: "k \<le> N - i" for i
    proof -
      have "(\<Sum>e\<le>N - i. nconvpow A k e * x ^ e) \<le> (\<Sum>j=1..(N - i) + 1 - k. A j * x ^ j) ^ k"
        by (rule Suc.IH[OF k1'])
      also have "\<dots> \<le> S ^ k"
      proof (rule power_mono)
        show "(\<Sum>j=1..(N - i) + 1 - k. A j * x ^ j) \<le> S"
          unfolding S_def
        proof (rule sum_mono2)
          show "finite {1..N + 1 - Suc k}" by simp
          show "{1..(N - i) + 1 - k} \<subseteq> {1..N + 1 - Suc k}"
            using i by auto
          show "\<And>j. j \<in> {1..N + 1 - Suc k} - {1..(N - i) + 1 - k} \<Longrightarrow> 0 \<le> A j * x ^ j"
            by (intro mult_nonneg_nonneg Ann zero_le_power x0)
        qed
        show "0 \<le> (\<Sum>j=1..(N - i) + 1 - k. A j * x ^ j)"
          by (intro sum_nonneg mult_nonneg_nonneg Ann zero_le_power x0)
      qed
      finally show ?thesis .
    qed
    have "(\<Sum>i\<le>N. \<Sum>e\<le>N - i. A i * x ^ i * (nconvpow A k e * x ^ e))
        = (\<Sum>i\<le>N. A i * x ^ i * (\<Sum>e\<le>N - i. nconvpow A k e * x ^ e))"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> (\<Sum>i\<le>N. (if 1 \<le> i \<and> i \<le> N + 1 - Suc k then A i * x ^ i * S ^ k else 0))"
    proof (rule sum_mono)
      fix i assume iN: "i \<in> {..N}"
      show "A i * x ^ i * (\<Sum>e\<le>N - i. nconvpow A k e * x ^ e)
              \<le> (if 1 \<le> i \<and> i \<le> N + 1 - Suc k then A i * x ^ i * S ^ k else 0)"
      proof (cases "i = 0")
        case True
        thus ?thesis by (simp add: A0)
      next
        case False
        hence i1: "1 \<le> i" by simp
        show ?thesis
        proof (cases "k \<le> N - i")
          case True
          have iub: "i \<le> N + 1 - Suc k"
            using True i1 iN by simp
          have "A i * x ^ i * (\<Sum>e\<le>N - i. nconvpow A k e * x ^ e)
                  \<le> A i * x ^ i * S ^ k"
            by (intro mult_left_mono inner_bound[OF i1 _ True]
                  mult_nonneg_nonneg Ann zero_le_power x0) (use iN in simp)
          thus ?thesis using i1 iub by simp
        next
          case False
          have zero_inner: "(\<Sum>e\<le>N - i. nconvpow A k e * x ^ e) = 0"
          proof (rule sum.neutral, rule ballI)
            fix e assume "e \<in> {..N - i}"
            hence "e < k" using False by simp
            thus "nconvpow A k e * x ^ e = 0"
              by (simp only: A0 nconvpow_vanish)
          qed
          show ?thesis
          proof (cases "1 \<le> i \<and> i \<le> N + 1 - Suc k")
            case True
            thus ?thesis
              using zero_inner
              by (auto intro!: mult_nonneg_nonneg Ann zero_le_power x0
                    nconvpow_nonneg simp: Snn zero_le_power)
          next
            case False
            thus ?thesis using zero_inner
              by auto
          qed
        qed
      qed
    qed
    also have "\<dots> = (\<Sum>i=1..N + 1 - Suc k. A i * x ^ i * S ^ k)"
    proof -
      have sub: "{1..N + 1 - Suc k} \<subseteq> {..N}" by auto
      show ?thesis
        by (rule sum.mono_neutral_cong_right[OF finite_atMost sub]) auto
    qed
    also have "\<dots> = S * S ^ k"
      by (simp add: S_def sum_distrib_right)
    also have "\<dots> = S ^ Suc k"
      by simp
    finally show ?thesis
      using expand by (simp add: S_def)
  qed
qed

subsection \<open>Per-degree $\ell^1$ profiles of coefficient families\<close>

definition ra_blk :: "nat \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat) set" where
  "ra_blk d = {\<alpha>. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = d}"

lemma finite_ra_blk: "finite (ra_blk d :: ('a::euclidean_space \<Rightarrow> nat) set)"
  unfolding ra_blk_def by (rule ra_deg_block_finite)

lemma ra_blk_0: "(ra_blk 0 :: ('a::euclidean_space \<Rightarrow> nat) set) = {czero_idx}"
proof
  show "(ra_blk 0 :: ('a \<Rightarrow> nat) set) \<subseteq> {czero_idx}"
    unfolding ra_blk_def using ra_deg_eq0_iff by auto
  have "ra_deg (czero_idx :: 'a \<Rightarrow> nat) = 0"
    by (simp add: ra_deg_def czero_idx_def)
  thus "{czero_idx} \<subseteq> (ra_blk 0 :: ('a \<Rightarrow> nat) set)"
    unfolding ra_blk_def using czero_idx_in by auto
qed

definition profS :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "profS u d = (\<Sum>\<alpha>\<in>ra_blk d. \<bar>u \<alpha>\<bar>)"

definition profV :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> real" where
  "profV c d = (\<Sum>\<alpha>\<in>ra_blk d. norm (c \<alpha>))"

lemma profS_nonneg: "0 \<le> profS u d"
  unfolding profS_def by (rule sum_nonneg) simp

lemma profV_nonneg: "0 \<le> profV c d"
  unfolding profV_def by (rule sum_nonneg) simp

text \<open>The core regrouping estimate: profiles are submultiplicative under the Cauchy
  product, with the scalar convolution as upper bound.\<close>

lemma profS_ccauchy:
  fixes u v :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  shows "profS (ccauchy u v) d \<le> nconv (profS u) (profS v) d"
proof -
  have step1: "profS (ccauchy u v) d
      \<le> (\<Sum>\<gamma>\<in>ra_blk d. \<Sum>\<alpha>\<in>lowI \<gamma>. \<bar>u \<alpha>\<bar> * \<bar>v (subI \<gamma> \<alpha>)\<bar>)"
    unfolding profS_def ccauchy_def
  proof (rule sum_mono)
    fix \<gamma> :: "'a \<Rightarrow> nat" assume "\<gamma> \<in> ra_blk d"
    have "\<bar>\<Sum>\<alpha>\<in>lowI \<gamma>. u \<alpha> * v (subI \<gamma> \<alpha>)\<bar> \<le> (\<Sum>\<alpha>\<in>lowI \<gamma>. \<bar>u \<alpha> * v (subI \<gamma> \<alpha>)\<bar>)"
      by (rule sum_abs)
    also have "\<dots> = (\<Sum>\<alpha>\<in>lowI \<gamma>. \<bar>u \<alpha>\<bar> * \<bar>v (subI \<gamma> \<alpha>)\<bar>)"
      by (simp add: abs_mult)
    finally show "\<bar>\<Sum>\<alpha>\<in>lowI \<gamma>. u \<alpha> * v (subI \<gamma> \<alpha>)\<bar>
        \<le> (\<Sum>\<alpha>\<in>lowI \<gamma>. \<bar>u \<alpha>\<bar> * \<bar>v (subI \<gamma> \<alpha>)\<bar>)" .
  qed
  have step2: "(\<Sum>\<gamma>\<in>ra_blk d. \<Sum>\<alpha>\<in>lowI \<gamma>. \<bar>u \<alpha>\<bar> * \<bar>v (subI \<gamma> \<alpha>)\<bar>)
      = (\<Sum>(\<gamma>, \<alpha>)\<in>(SIGMA \<gamma>:(ra_blk d :: ('a \<Rightarrow> nat) set). lowI \<gamma>).
           \<bar>u \<alpha>\<bar> * \<bar>v (subI \<gamma> \<alpha>)\<bar>)"
    by (rule sum.Sigma[OF finite_ra_blk]) (simp add: idx_lower_fin)
  define T :: "(('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)) set" where
    "T = {(\<alpha>, \<delta>). \<alpha> \<in> ra_idx \<and> \<delta> \<in> ra_idx \<and> ra_deg \<alpha> + ra_deg \<delta> = d}"
  have step3: "(\<Sum>(\<gamma>, \<alpha>)\<in>(SIGMA \<gamma>:(ra_blk d :: ('a \<Rightarrow> nat) set). lowI \<gamma>).
           \<bar>u \<alpha>\<bar> * \<bar>v (subI \<gamma> \<alpha>)\<bar>)
      = (\<Sum>(\<alpha>, \<delta>)\<in>T. \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>)"
  proof (rule sum.reindex_bij_witness[where
        i = "\<lambda>(\<alpha>, \<delta>). (addI \<alpha> \<delta>, \<alpha>)" and j = "\<lambda>(\<gamma>, \<alpha>). (\<alpha>, subI \<gamma> \<alpha>)"])
    fix a :: "('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)"
    assume a: "a \<in> (SIGMA \<gamma>:(ra_blk d :: ('a \<Rightarrow> nat) set). lowI \<gamma>)"
    obtain \<gamma> \<alpha> :: "'a \<Rightarrow> nat" where ga: "a = (\<gamma>, \<alpha>)" by (cases a)
    have gblk: "\<gamma> \<in> ra_blk d" and alow: "\<alpha> \<in> lowI \<gamma>" using a ga by auto
    have gra: "\<gamma> \<in> ra_idx" and gdeg: "ra_deg \<gamma> = d" using gblk by (auto simp: ra_blk_def)
    have ara: "\<alpha> \<in> ra_idx" using alow by (rule lowI_ra_idx)
    have dra: "subI \<gamma> \<alpha> \<in> ra_idx" using gra by (rule idx_sub)
    have degsplit: "ra_deg \<alpha> + ra_deg (subI \<gamma> \<alpha>) = d"
      using ra_deg_split[OF alow] gdeg by simp
    show "(case case a of (\<gamma>, \<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>) of (\<alpha>, \<delta>) \<Rightarrow> (addI \<alpha> \<delta>, \<alpha>)) = a"
      using ga addI_subI[OF alow] by simp
    show "(case a of (\<gamma>, \<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) \<in> T"
      using ga ara dra degsplit by (simp add: T_def)
  next
    fix b :: "('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)"
    assume b: "b \<in> T"
    obtain \<alpha> \<delta> :: "'a \<Rightarrow> nat" where ad: "b = (\<alpha>, \<delta>)" by (cases b)
    have ara: "\<alpha> \<in> ra_idx" and dra: "\<delta> \<in> ra_idx" and degs: "ra_deg \<alpha> + ra_deg \<delta> = d"
      using b ad by (auto simp: T_def)
    have gra: "addI \<alpha> \<delta> \<in> ra_idx" using ara dra by (rule idx_add)
    have gdeg: "ra_deg (addI \<alpha> \<delta>) = d" using degs by (simp add: ra_deg_addI)
    show "(case case b of (\<alpha>, \<delta>) \<Rightarrow> (addI \<alpha> \<delta>, \<alpha>) of (\<gamma>, \<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>)) = b"
      using ad subI_addI by simp
    show "(case b of (\<alpha>, \<delta>) \<Rightarrow> (addI \<alpha> \<delta>, \<alpha>))
            \<in> (SIGMA \<gamma>:(ra_blk d :: ('a \<Rightarrow> nat) set). lowI \<gamma>)"
      using ad gra gdeg ara addI_in_lowI[OF ara] by (auto simp: ra_blk_def)
  next
    show "\<And>a :: ('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat).
        a \<in> (SIGMA \<gamma>:(ra_blk d :: ('a \<Rightarrow> nat) set). lowI \<gamma>) \<Longrightarrow>
        (case case a of (\<gamma>, \<alpha>) \<Rightarrow> (\<alpha>, subI \<gamma> \<alpha>) of (\<alpha>, \<delta>) \<Rightarrow> \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>)
          = (case a of (\<gamma>, \<alpha>) \<Rightarrow> \<bar>u \<alpha>\<bar> * \<bar>v (subI \<gamma> \<alpha>)\<bar>)"
      by fastforce
  qed
  have Tsplit: "T = (\<Union>i\<in>{..d}. ra_blk i \<times> ra_blk (d - i))"
  proof
    show "T \<subseteq> (\<Union>i\<in>{..d}. ra_blk i \<times> ra_blk (d - i))"
    proof
      fix p :: "('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)"
      assume p: "p \<in> T"
      obtain \<alpha> \<delta> :: "'a \<Rightarrow> nat" where ad: "p = (\<alpha>, \<delta>)" by (cases p)
      have ara: "\<alpha> \<in> ra_idx" and dra: "\<delta> \<in> ra_idx" and degs: "ra_deg \<alpha> + ra_deg \<delta> = d"
        using p ad by (auto simp: T_def)
      have "ra_deg \<alpha> \<le> d" using degs by simp
      moreover have "\<alpha> \<in> ra_blk (ra_deg \<alpha>)" using ara by (simp add: ra_blk_def)
      moreover have "\<delta> \<in> ra_blk (d - ra_deg \<alpha>)"
        using dra degs by (simp add: ra_blk_def)
      ultimately show "p \<in> (\<Union>i\<in>{..d}. ra_blk i \<times> ra_blk (d - i))"
        using ad by auto
    qed
    show "(\<Union>i\<in>{..d}. ra_blk i \<times> ra_blk (d - i)) \<subseteq> T"
    proof
      fix p :: "('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)"
      assume "p \<in> (\<Union>i\<in>{..d}. ra_blk i \<times> ra_blk (d - i))"
      then obtain i and \<alpha> \<delta> :: "'a \<Rightarrow> nat" where i: "i \<le> d" and ad: "p = (\<alpha>, \<delta>)"
        and a: "\<alpha> \<in> ra_blk i" and dd: "\<delta> \<in> ra_blk (d - i)"
        by auto
      show "p \<in> T"
        using i ad a dd by (auto simp: T_def ra_blk_def)
    qed
  qed
  have step4: "(\<Sum>(\<alpha>, \<delta>)\<in>T. \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>) = nconv (profS u) (profS v) d"
  proof -
    have disj: "\<And>i j. i \<in> {..d} \<Longrightarrow> j \<in> {..d} \<Longrightarrow> i \<noteq> j \<Longrightarrow>
        (ra_blk i \<times> ra_blk (d - i)) \<inter> (ra_blk j \<times> ra_blk (d - j)) = {}"
      by (auto simp: ra_blk_def)
    have "(\<Sum>(\<alpha>, \<delta>)\<in>T. \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>)
        = (\<Sum>i\<le>d. \<Sum>(\<alpha>, \<delta>)\<in>ra_blk i \<times> ra_blk (d - i). \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>)"
      unfolding Tsplit
      by (rule sum.UNION_disjoint)
         (auto simp: finite_ra_blk disj intro: finite_cartesian_product)
    also have "\<dots> = (\<Sum>i\<le>d. (\<Sum>\<alpha>\<in>ra_blk i. \<bar>u \<alpha>\<bar>) * (\<Sum>\<delta>\<in>ra_blk (d - i). \<bar>v \<delta>\<bar>))"
      by (simp add: sum_product sum.cartesian_product)
    also have "\<dots> = nconv (profS u) (profS v) d"
      by (simp add: nconv_def profS_def)
    finally show ?thesis .
  qed
  show ?thesis
    using step1 step2 step3 step4 by simp
qed

lemma profS_cone: "profS (cone :: ('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real) = ndelta"
proof (rule ext)
  fix d :: nat
  show "profS (cone :: ('a \<Rightarrow> nat) \<Rightarrow> real) d = ndelta d"
  proof (cases "d = 0")
    case True
    thus ?thesis
      by (simp add: profS_def ra_blk_0 cone_def ndelta_def)
  next
    case False
    have "\<And>\<alpha>. \<alpha> \<in> (ra_blk d :: ('a \<Rightarrow> nat) set) \<Longrightarrow> cone \<alpha> = 0"
    proof -
      fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_blk d"
      hence da: "ra_deg \<alpha> = d" by (simp add: ra_blk_def)
      have "\<alpha> \<noteq> czero_idx"
      proof
        assume "\<alpha> = czero_idx"
        hence "ra_deg \<alpha> = 0" by (simp add: ra_deg_def czero_idx_def)
        thus False using da False by simp
      qed
      thus "cone \<alpha> = 0" by (simp add: cone_def)
    qed
    thus ?thesis by (simp add: profS_def ndelta_def False)
  qed
qed

lemma profS_cpow:
  fixes u :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  shows "profS (cpow u k) d \<le> nconvpow (profS u) k d"
proof (induction k arbitrary: d)
  case 0
  show ?case by (simp add: cpow_0 profS_cone)
next
  case (Suc k)
  have "profS (cpow u (Suc k)) d = profS (ccauchy u (cpow u k)) d"
    by (simp add: cpow_Suc)
  also have "\<dots> \<le> nconv (profS u) (profS (cpow u k)) d"
    by (rule profS_ccauchy)
  also have "\<dots> \<le> nconv (profS u) (nconvpow (profS u) k) d"
    by (rule nconv_mono[OF order_refl Suc.IH profS_nonneg
          nconvpow_nonneg[OF profS_nonneg]])
  finally show ?case by simp
qed

lemma profS_component:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes b: "b \<in> Basis"
  shows "profS (\<lambda>\<alpha>. c \<alpha> \<bullet> b) d \<le> profV c d"
  unfolding profS_def profV_def
  by (rule sum_mono) (simp add: Basis_le_norm[OF b])

lemma profS_mcl:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes bs: "set l \<subseteq> Basis"
  shows "profS (mcl c \<beta> l) d \<le> nconvpow (profV c) (sum_list (map \<beta> l)) d"
  using bs
proof (induction l arbitrary: d)
  case Nil
  show ?case by (simp add: profS_cone)
next
  case (Cons b bs)
  have bB: "b \<in> Basis" and rest: "set bs \<subseteq> Basis"
    using Cons.prems by auto
  have "profS (mcl c \<beta> (b # bs)) d
      = profS (ccauchy (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (mcl c \<beta> bs)) d"
    by simp
  also have "\<dots> \<le> nconv (profS (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b))) (profS (mcl c \<beta> bs)) d"
    by (rule profS_ccauchy)
  also have "\<dots> \<le> nconv (nconvpow (profV c) (\<beta> b))
                    (nconvpow (profV c) (sum_list (map \<beta> bs))) d"
  proof (rule nconv_mono)
    fix i
    have "profS (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) i \<le> nconvpow (profS (\<lambda>\<alpha>. c \<alpha> \<bullet> b)) (\<beta> b) i"
      by (rule profS_cpow)
    also have "\<dots> \<le> nconvpow (profV c) (\<beta> b) i"
      by (rule nconvpow_mono_base[OF profS_component[OF bB] profS_nonneg])
    finally show "profS (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) i \<le> nconvpow (profV c) (\<beta> b) i" .
  next
    fix i
    show "profS (mcl c \<beta> bs) i \<le> nconvpow (profV c) (sum_list (map \<beta> bs)) i"
      by (rule Cons.IH[OF rest])
  next
    fix i
    show "0 \<le> profS (cpow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) i" by (rule profS_nonneg)
  next
    fix i
    show "0 \<le> nconvpow (profV c) (sum_list (map \<beta> bs)) i"
      by (rule nconvpow_nonneg[OF profV_nonneg])
  qed
  also have "\<dots> = nconvpow (profV c) (\<beta> b + sum_list (map \<beta> bs)) d"
    by (simp add: nconvpow_add)
  finally show ?case by simp
qed

lemma profS_mono_co:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  shows "profS (mono_co c \<beta>) d \<le> nconvpow (profV c) (ra_deg \<beta>) d"
proof -
  have sub: "set (basis_list :: 'a list) \<subseteq> Basis"
    by (simp add: basis_list(1))
  have "profS (mcl c \<beta> basis_list) d
      \<le> nconvpow (profV c) (sum_list (map \<beta> (basis_list :: 'a list))) d"
    by (rule profS_mcl[OF sub])
  thus ?thesis
    unfolding mono_co_def by (simp add: sum_list_basis_ra_deg)
qed

lemma profV_cId:
  "profV (cId :: ('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) d
     \<le> (if d = 1 then real (card (Basis :: 'a set)) else 0)"
proof (cases "d = 1")
  case False
  have "\<And>\<alpha>. \<alpha> \<in> (ra_blk d :: ('a \<Rightarrow> nat) set) \<Longrightarrow> cId \<alpha> = 0"
  proof -
    fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_blk d"
    hence "ra_deg \<alpha> = d" by (simp add: ra_blk_def)
    thus "cId \<alpha> = 0" using False cId_deg by fastforce
  qed
  thus ?thesis by (simp add: profV_def False)
next
  case True
  have "profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d
      = (\<Sum>\<alpha>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set). norm (cId \<alpha>))"
    by (simp add: profV_def)
  also have "\<dots> \<le> (\<Sum>\<alpha>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set). 1)"
    by (rule sum_mono) (rule norm_cId_le)
  also have "\<dots> = real (card (ra_blk d :: ('a \<Rightarrow> nat) set))"
    by simp
  also have "\<dots> \<le> real (card (Basis :: 'a set))"
  proof -
    have sub: "(ra_blk d :: ('a \<Rightarrow> nat) set) \<subseteq> unit_idx ` (Basis :: 'a set)"
    proof
      fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_blk d"
      hence "\<alpha> \<in> ra_idx" "ra_deg \<alpha> = 1" using True by (auto simp: ra_blk_def)
      thus "\<alpha> \<in> unit_idx ` Basis"
        by (metis ra_deg_one_unit imageI)
    qed
    have "card (ra_blk d :: ('a \<Rightarrow> nat) set) \<le> card (unit_idx ` (Basis :: 'a set))"
      by (rule card_mono[OF finite_imageI[OF finite_Basis] sub])
    also have "\<dots> = card (Basis :: 'a set)"
      by (rule card_image[OF inj_on_unit_idx])
    finally show ?thesis by simp
  qed
  finally show ?thesis using True by simp
qed

subsection \<open>The composition operator \<open>Tcomp\<close> and the formal fixed point\<close>

definition ra_blk_le :: "nat \<Rightarrow> nat \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat) set" where
  "ra_blk_le j d = {\<beta>. \<beta> \<in> ra_idx \<and> j \<le> ra_deg \<beta> \<and> ra_deg \<beta> \<le> d}"

lemma finite_ra_blk_le: "finite (ra_blk_le j d :: ('a::euclidean_space \<Rightarrow> nat) set)"
proof -
  have "(ra_blk_le j d :: ('a \<Rightarrow> nat) set) \<subseteq> (\<Union>k\<in>{..d}. ra_blk k)"
    by (auto simp: ra_blk_le_def ra_blk_def)
  moreover have "finite (\<Union>k\<in>{..d}. ra_blk k :: ('a \<Rightarrow> nat) set)"
    by (intro finite_UN_I finite_atMost finite_ra_blk)
  ultimately show ?thesis by (rule finite_subset)
qed

definition Tcomp :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'a)
                       \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'a)" where
  "Tcomp bphi c =
     (\<lambda>\<gamma>. cId \<gamma> + (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))"

lemma ra_blk_le_2_empty: "ra_deg \<gamma> < 2 \<Longrightarrow> (ra_blk_le 2 (ra_deg \<gamma>)) = {}"
  by (auto simp: ra_blk_le_def)

lemma Tcomp_low_deg: "ra_deg \<gamma> < 2 \<Longrightarrow> Tcomp bphi c \<gamma> = cId \<gamma>"
  by (simp add: Tcomp_def ra_blk_le_2_empty)

lemma Tcomp_czero: "Tcomp bphi c czero_idx = 0"
proof -
  have "ra_deg (czero_idx :: 'a \<Rightarrow> nat) = 0"
    by (simp add: ra_deg_def czero_idx_def)
  thus ?thesis by (simp add: Tcomp_low_deg cId_czero)
qed

lemma Tcomp_sum_le_degree:
  fixes bphi c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
  shows "Tcomp bphi c \<gamma> =
    cId \<gamma> + (\<Sum>\<beta>\<in>ra_blk_le 0 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
proof -
  have "(\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      = (\<Sum>\<beta>\<in>ra_blk_le 0 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
  proof (rule sum.mono_neutral_cong_left)
    show "finite (ra_blk_le 0 (ra_deg \<gamma>) :: ('a \<Rightarrow> nat) set)"
      by (rule finite_ra_blk_le)
    show "ra_blk_le 2 (ra_deg \<gamma>) \<subseteq> ra_blk_le 0 (ra_deg \<gamma>)"
      by (auto simp: ra_blk_le_def)
    show "\<forall>\<beta>\<in>ra_blk_le 0 (ra_deg \<gamma>) - ra_blk_le 2 (ra_deg \<gamma>).
      mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta> = 0"
    proof
      fix \<beta> :: "'a \<Rightarrow> nat"
      assume "\<beta> \<in> ra_blk_le 0 (ra_deg \<gamma>) - ra_blk_le 2 (ra_deg \<gamma>)"
      hence "\<beta> \<in> ra_idx" "ra_deg \<beta> < 2"
        by (auto simp: ra_blk_le_def)
      hence "bphi \<beta> = 0"
        by (rule low)
      thus "mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta> = 0"
        by simp
    qed
    show "\<And>\<beta>. \<beta> \<in> ra_blk_le 2 (ra_deg \<gamma>) \<Longrightarrow>
      mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta> = mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>"
      by simp
  qed
  thus ?thesis
    by (simp add: Tcomp_def)
qed

lemma Tcomp_local:
  fixes c c' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c czero_idx = 0" and c0': "c' czero_idx = 0"
    and agree: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> c \<alpha> = c' \<alpha>"
    and g: "\<gamma> \<in> ra_idx" and dg: "ra_deg \<gamma> \<le> D + 1"
  shows "Tcomp bphi c \<gamma> = Tcomp bphi c' \<gamma>"
proof -
  have "(\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      = (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c' \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
  proof (rule sum.cong[OF refl])
    fix \<beta> :: "'a \<Rightarrow> nat" assume "\<beta> \<in> ra_blk_le 2 (ra_deg \<gamma>)"
    hence b2: "2 \<le> ra_deg \<beta>" by (simp add: ra_blk_le_def)
    have "mono_co c \<beta> \<gamma> = mono_co c' \<beta> \<gamma>"
    proof (rule mono_co_local[where D = D])
      show "c czero_idx = 0" by (rule c0)
      show "c' czero_idx = 0" by (rule c0')
      show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> c \<alpha> = c' \<alpha>" by (rule agree)
      show "\<gamma> \<in> ra_idx" by (rule g)
      show "1 \<le> ra_deg \<beta>" using b2 by simp
      show "ra_deg \<gamma> \<le> D + ra_deg \<beta> - 1" using dg b2 by simp
    qed
    thus "mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta> = mono_co c' \<beta> \<gamma> *\<^sub>R bphi \<beta>" by simp
  qed
  thus ?thesis by (simp add: Tcomp_def)
qed

lemma profV_Tcomp:
  fixes bphi c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  shows "profV (Tcomp bphi c) d
      \<le> profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d
          + (\<Sum>k=2..d. profV bphi k * nconvpow (profV c) k d)"
proof -
  have "profV (Tcomp bphi c) d
      = (\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set).
           norm (cId \<gamma> + (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)))"
    by (simp add: profV_def Tcomp_def)
  also have "\<dots> \<le> (\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set).
           norm (cId \<gamma>)
             + norm (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))"
    by (rule sum_mono) (rule norm_triangle_ineq)
  also have "\<dots> = (\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set). norm (cId \<gamma>))
        + (\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set).
             norm (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))"
    by (rule sum.distrib)
  finally have "profV (Tcomp bphi c) d
      \<le> (\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set). norm (cId \<gamma>))
        + (\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set).
             norm (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))" .
  also have "\<dots> \<le> profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d
        + (\<Sum>k=2..d. profV bphi k * nconvpow (profV c) k d)"
  proof -
    have inner: "(\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set).
             norm (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))
        \<le> (\<Sum>k=2..d. profV bphi k * nconvpow (profV c) k d)"
    proof -
      have rng_const: "\<And>\<gamma>. \<gamma> \<in> (ra_blk d :: ('a \<Rightarrow> nat) set) \<Longrightarrow>
          ra_blk_le 2 (ra_deg \<gamma>) = ra_blk_le 2 d"
        by (simp add: ra_blk_def)
      have "(\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set).
               norm (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))
          \<le> (\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set).
               \<Sum>\<beta>\<in>ra_blk_le 2 d. \<bar>mono_co c \<beta> \<gamma>\<bar> * norm (bphi \<beta>))"
      proof (rule sum_mono)
        fix \<gamma> :: "'a \<Rightarrow> nat" assume gblk: "\<gamma> \<in> ra_blk d"
        have "norm (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
            \<le> (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). norm (mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))"
          by (rule norm_sum)
        also have "\<dots> = (\<Sum>\<beta>\<in>ra_blk_le 2 d. \<bar>mono_co c \<beta> \<gamma>\<bar> * norm (bphi \<beta>))"
          by (simp add: rng_const[OF gblk])
        finally show "norm (\<Sum>\<beta>\<in>ra_blk_le 2 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
            \<le> (\<Sum>\<beta>\<in>ra_blk_le 2 d. \<bar>mono_co c \<beta> \<gamma>\<bar> * norm (bphi \<beta>))" .
      qed
      also have "\<dots> = (\<Sum>\<beta>\<in>ra_blk_le 2 d.
               norm (bphi \<beta>) * (\<Sum>\<gamma>\<in>ra_blk d. \<bar>mono_co c \<beta> \<gamma>\<bar>))"
        by (subst sum.swap) (simp add: sum_distrib_left algebra_simps)
      also have "\<dots> = (\<Sum>\<beta>\<in>(ra_blk_le 2 d :: ('a \<Rightarrow> nat) set).
               norm (bphi \<beta>) * profS (mono_co c \<beta>) d)"
        by (simp add: profS_def)
      also have "\<dots> \<le> (\<Sum>\<beta>\<in>(ra_blk_le 2 d :: ('a \<Rightarrow> nat) set).
               norm (bphi \<beta>) * nconvpow (profV c) (ra_deg \<beta>) d)"
        by (rule sum_mono) (intro mult_left_mono profS_mono_co norm_ge_zero)
      also have "\<dots> = (\<Sum>k=2..d. \<Sum>\<beta>\<in>(ra_blk k :: ('a \<Rightarrow> nat) set).
               norm (bphi \<beta>) * nconvpow (profV c) (ra_deg \<beta>) d)"
      proof -
        have split: "(ra_blk_le 2 d :: ('a \<Rightarrow> nat) set) = (\<Union>k\<in>{2..d}. ra_blk k)"
          by (auto simp: ra_blk_le_def ra_blk_def)
        show ?thesis
          unfolding split using finite_ra_blk
          apply (subst sum.UNION_disjoint)
          apply simp_all
          apply blast
          by (simp add: disjoint_iff ra_blk_def)
      qed
      also have "\<dots> = (\<Sum>k=2..d. profV bphi k * nconvpow (profV c) k d)"
      proof (rule sum.cong[OF refl])
        fix k assume "k \<in> {2..d}"
        have "(\<Sum>\<beta>\<in>(ra_blk k :: ('a \<Rightarrow> nat) set).
                 norm (bphi \<beta>) * nconvpow (profV c) (ra_deg \<beta>) d)
            = (\<Sum>\<beta>\<in>(ra_blk k :: ('a \<Rightarrow> nat) set).
                 norm (bphi \<beta>) * nconvpow (profV c) k d)"
          by (rule sum.cong[OF refl], simp add: ra_blk_def)
        also have "\<dots> = profV bphi k * nconvpow (profV c) k d"
          by (simp add: profV_def sum_distrib_right)
        finally show "(\<Sum>\<beta>\<in>(ra_blk k :: ('a \<Rightarrow> nat) set).
                 norm (bphi \<beta>) * nconvpow (profV c) (ra_deg \<beta>) d)
            = profV bphi k * nconvpow (profV c) k d" .
      qed
      finally show ?thesis .
    qed
    have cId_eq: "(\<Sum>\<gamma>\<in>(ra_blk d :: ('a \<Rightarrow> nat) set). norm (cId \<gamma>))
                    = profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d"
      by (simp add: profV_def)
    show ?thesis
      unfolding cId_eq by (rule add_left_mono[OF inner])
  qed
  finally show ?thesis .
qed

text \<open>Stage-wise construction of the formal fixed point.\<close>

primrec cstage :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'a)" where
  "cstage bphi 0 = (\<lambda>_. 0)"
| "cstage bphi (Suc d) = Tcomp bphi (cstage bphi d)"

lemma cstage_czero: "cstage bphi d czero_idx = 0"
  by (cases d) (simp_all add: Tcomp_czero)

lemma cstage_stable_succ:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes "\<gamma> \<in> ra_idx" and "ra_deg \<gamma> \<le> d"
  shows "cstage bphi (Suc d) \<gamma> = cstage bphi d \<gamma>"
  using assms
proof (induction d arbitrary: \<gamma>)
  case 0
  hence "\<gamma> = czero_idx" by (simp add: ra_deg_eq0_iff)
  thus ?case by (simp add: Tcomp_czero)
next
  case (Suc d)
  have "Tcomp bphi (cstage bphi (Suc d)) \<gamma> = Tcomp bphi (cstage bphi d) \<gamma>"
  proof (rule Tcomp_local[where D = d])
    show "cstage bphi (Suc d) czero_idx = 0" by (rule cstage_czero)
    show "cstage bphi d czero_idx = 0" by (rule cstage_czero)
    show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> d \<Longrightarrow>
            cstage bphi (Suc d) \<alpha> = cstage bphi d \<alpha>"
      by (rule Suc.IH)
    show "\<gamma> \<in> ra_idx" by (rule Suc.prems(1))
    show "ra_deg \<gamma> \<le> d + 1" using Suc.prems(2) by simp
  qed
  thus ?case by simp
qed

lemma cstage_stable:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes g: "\<gamma> \<in> ra_idx" and dd: "ra_deg \<gamma> \<le> d" and de: "d \<le> e"
  shows "cstage bphi e \<gamma> = cstage bphi d \<gamma>"
  using de
proof (induction e)
  case 0
  thus ?case by simp
next
  case (Suc e)
  show ?case
  proof (cases "d = Suc e")
    case True
    thus ?thesis by simp
  next
    case False
    hence "d \<le> e" using Suc.prems by simp
    hence IH: "cstage bphi e \<gamma> = cstage bphi d \<gamma>" by (rule Suc.IH)
    have "cstage bphi (Suc e) \<gamma> = cstage bphi e \<gamma>"
      by (rule cstage_stable_succ[OF g]) (use dd \<open>d \<le> e\<close> in simp)
    thus ?thesis using IH by simp
  qed
qed

definition cfix :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'a)" where
  "cfix bphi = (\<lambda>\<gamma>. cstage bphi (ra_deg \<gamma>) \<gamma>)"

lemma cfix_czero: "cfix bphi czero_idx = 0"
  by (simp add: cfix_def cstage_czero)

lemma cfix_agrees_cstage:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes a: "\<alpha> \<in> ra_idx" and dd: "ra_deg \<alpha> \<le> d"
  shows "cfix bphi \<alpha> = cstage bphi d \<alpha>"
  unfolding cfix_def
  by (rule cstage_stable[OF a order_refl dd, symmetric])

theorem cfix_fixed_point:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes g: "\<gamma> \<in> ra_idx"
  shows "cfix bphi \<gamma> = Tcomp bphi (cfix bphi) \<gamma>"
proof -
  define d where "d = ra_deg \<gamma>"
  have T_eq: "Tcomp bphi (cfix bphi) \<gamma> = Tcomp bphi (cstage bphi d) \<gamma>"
  proof (rule Tcomp_local[where D = d])
    show "cfix bphi czero_idx = 0" by (rule cfix_czero)
    show "cstage bphi d czero_idx = 0" by (rule cstage_czero)
    show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> d \<Longrightarrow> cfix bphi \<alpha> = cstage bphi d \<alpha>"
      by (rule cfix_agrees_cstage)
    show "\<gamma> \<in> ra_idx" by (rule g)
    show "ra_deg \<gamma> \<le> d + 1" by (simp add: d_def)
  qed
  have "Tcomp bphi (cstage bphi d) \<gamma> = cstage bphi (Suc d) \<gamma>"
    by simp
  also have "\<dots> = cstage bphi d \<gamma>"
    by (rule cstage_stable_succ[OF g]) (simp add: d_def)
  also have "\<dots> = cfix bphi \<gamma>"
    by (simp add: cfix_def d_def)
  finally show ?thesis
    using T_eq by simp
qed

corollary cfix_coeff_equation_le_degree:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes g: "\<gamma> \<in> ra_idx"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
  shows "cfix bphi \<gamma> =
    cId \<gamma> + (\<Sum>\<beta>\<in>ra_blk_le 0 (ra_deg \<gamma>). mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
  using cfix_fixed_point[OF g]
    Tcomp_sum_le_degree[where bphi=bphi and c="cfix bphi" and \<gamma>=\<gamma>, OF low]
  by simp

lemma mono_co_term_has_sum_le_degree:
  fixes c bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c czero_idx = 0"
    and g: "\<gamma> \<in> ra_idx"
  shows "((\<lambda>\<beta>. mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>ra_blk_le 0 (ra_deg \<gamma>). mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set)"
proof -
  let ?S = "ra_blk_le 0 (ra_deg \<gamma>) :: ('a \<Rightarrow> nat) set"
  have finite_sum:
    "((\<lambda>\<beta>. mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>?S. mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)) ?S"
    by (rule has_sum_finite) (rule finite_ra_blk_le)
  have neutral:
    "mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta> = 0"
    if "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set) - ?S" for \<beta>
  proof -
    have "ra_deg \<gamma> < ra_deg \<beta>"
      using that by (auto simp: ra_blk_le_def)
    hence "mono_co c \<beta> \<gamma> = 0"
      by (rule mono_co_zero_below_degree[where c=c and \<beta>=\<beta>, OF c0 g])
    thus ?thesis by simp
  qed
  have "(((\<lambda>\<beta>. mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>?S. mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set))
    = (((\<lambda>\<beta>. mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>?S. mono_co c \<beta> \<gamma> *\<^sub>R bphi \<beta>)) ?S)"
    by (rule has_sum_cong_neutral)
       (use neutral in \<open>auto simp: ra_blk_le_def\<close>)
  thus ?thesis
    using finite_sum by simp
qed

corollary cfix_coeff_equation_infsum:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes g: "\<gamma> \<in> ra_idx"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
  shows "cfix bphi \<gamma> =
    cId \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set). mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
proof -
  have hs: "((\<lambda>\<beta>. mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>ra_blk_le 0 (ra_deg \<gamma>). mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set)"
    by (rule mono_co_term_has_sum_le_degree[where c = "cfix bphi", OF cfix_czero g])
  hence inf_eq:
    "(\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set). mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      = (\<Sum>\<beta>\<in>ra_blk_le 0 (ra_deg \<gamma>). mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
    by (rule infsumI)
  show ?thesis
    using cfix_coeff_equation_le_degree[OF g low] inf_eq by simp
qed

subsection \<open>The majorant bootstrap: a \<open>majle\<close> bound for the fixed point\<close>

text \<open>Weighted partial sums of the profile of \<open>cfix\<close> stay below \<open>2n\<sigma>\<close> for small \<open>\<sigma>\<close>:
  the profile obeys the convolution recursion inherited from \<open>Tcomp\<close>, and the
  quadratic bootstrap keeps the interval \<open>[0, 2n\<sigma>]\<close> invariant.\<close>

lemma geom_tail_le:
  fixes q :: real
  assumes q0: "0 \<le> q" and qh: "q \<le> 1/2"
  shows "(\<Sum>k=2..K. q ^ k) \<le> 2 * q\<^sup>2"
proof -
  have "(\<Sum>k=2..K. q ^ k) = (\<Sum>j<K - 1. q ^ (j + 2))"
  proof (cases "2 \<le> K")
    case True
    show ?thesis
      using le_Suc_ex
      by (subst sum.reindex_bij_witness[where i = "\<lambda>j. j + 2" and j = "\<lambda>k. k - 2"], auto, fastforce)
  next
    case False
    thus ?thesis by simp
  qed
  also have "\<dots> = q\<^sup>2 * (\<Sum>j<K - 1. q ^ j)"
    by (simp only: power_add sum_distrib_left mult.assoc mult.commute power2_eq_square)
  also have "\<dots> \<le> q\<^sup>2 * 2"
  proof (rule mult_left_mono)
    have "(\<Sum>j<K - 1. q ^ j) \<le> (\<Sum>j<K - 1. (1/2) ^ j)"
      by (rule sum_mono) (rule power_mono[OF qh q0])
    also have "\<dots> \<le> 2"
    proof (cases "K - 1 = 0")
      case True
      thus ?thesis by simp
    next
      case False
      have "(\<Sum>j<K - 1. (1/2::real) ^ j) = (1 - (1/2) ^ (K - 1)) / (1 - 1/2)"
        by (subst geometric_sum, auto)
      also have "\<dots> \<le> 2"
        by simp
      finally show ?thesis.
    qed
    finally show "(\<Sum>j<K - 1. q ^ j) \<le> 2".
    show "0 \<le> q\<^sup>2" by simp
  qed
  finally show ?thesis by simp
qed

text \<open>Block sums of a \<open>majle\<close>-bounded family are geometrically bounded.\<close>

lemma profV_le_majle:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
  shows "profV bphi k \<le> M / t ^ k"
proof -
  have summ: "mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) summable_on ra_idx"
    and inf_le: "(\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>) \<le> M"
    using majb by (simp_all add: majle_def)
  have blk_le: "(\<Sum>\<beta>\<in>(ra_blk k :: ('a \<Rightarrow> nat) set). mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)
      \<le> (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)"
  proof (rule finite_sum_le_infsum[OF summ finite_ra_blk])
    show "(ra_blk k :: ('a \<Rightarrow> nat) set) \<subseteq> ra_idx" by (auto simp: ra_blk_def)
    show "\<And>\<beta>. \<beta> \<in> ra_idx - (ra_blk k :: ('a \<Rightarrow> nat) set) \<Longrightarrow>
            0 \<le> mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>"
      using t0 by (simp add: mfam_nonneg)
  qed
  have blk_eq: "(\<Sum>\<beta>\<in>(ra_blk k :: ('a \<Rightarrow> nat) set). mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)
      = profV bphi k * t ^ k"
    unfolding mfam_def profV_def
    by (simp add: ra_blk_def sum_distrib_right)
  have "profV bphi k * t ^ k \<le> M"
    using blk_le blk_eq inf_le by simp
  thus ?thesis
    using t0 by (simp add: field_simps)
qed

text \<open>Single coefficients of a \<open>majle\<close>-bounded family are geometrically bounded.\<close>

lemma coeff_le_majle:
  fixes u :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes t0: "0 < t" and majb: "majle t u M"
    and unn: "\<And>\<beta>. 0 \<le> u \<beta>" and b: "\<beta> \<in> ra_idx"
  shows "u \<beta> \<le> M / t ^ ra_deg \<beta>"
proof -
  have summ: "mfam t u summable_on ra_idx"
    and inf_le: "(\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. mfam t u \<beta>) \<le> M"
    using majb by (simp_all add: majle_def)
  have "(\<Sum>\<beta>'\<in>{\<beta>}. mfam t u \<beta>') \<le> (\<Sum>\<^sub>\<infinity>\<beta>'\<in>ra_idx. mfam t u \<beta>')"
    by (rule finite_sum_le_infsum[OF summ])
       (use b t0 in \<open>auto simp: mfam_nonneg\<close>)
  hence "u \<beta> * t ^ ra_deg \<beta> \<le> M"
    using inf_le unn by (simp add: mfam_def abs_of_nonneg)
  thus ?thesis
    using t0 by (simp add: field_simps)
qed

text \<open>The profile of the fixed point obeys the composition recursion.\<close>

lemma profV_cfix_rec:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  shows "profV (cfix bphi) d
      \<le> profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d + (\<Sum>k=2..d. profV bphi k * nconvpow (profV (cfix bphi)) k d)"
proof -
  have "profV (cfix bphi) d = profV (Tcomp bphi (cfix bphi)) d"
    unfolding profV_def
    by (rule sum.cong[OF refl])
       (simp add: ra_blk_def cfix_fixed_point)
  also have "\<dots> \<le> profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d + (\<Sum>k=2..d. profV bphi k * nconvpow (profV (cfix bphi)) k d)"
    by (rule profV_Tcomp)
  finally show ?thesis .
qed

lemma profV_cfix_0:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  shows "profV (cfix bphi) 0 = 0"
  by (simp add: profV_def ra_blk_0 cfix_czero)

text \<open>The bootstrap: the weighted partial profile sums of \<open>cfix\<close> never exceed \<open>2n\<sigma>\<close>.\<close>

lemma cfix_partial_sums_bounded:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  defines "A \<equiv> profV (cfix bphi)"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "(\<Sum>i=1..N. A i * \<sigma> ^ i) \<le> 2 * n * \<sigma>"
proof (induction N)
  case 0
  have "0 \<le> 2 * n * \<sigma>"
    using s0 by (simp add: n_def)
  thus ?case by simp
next
  case (Suc N)
  define W where "W = (\<Sum>i=1..N. A i * \<sigma> ^ i)"
  have Wnn: "0 \<le> W"
    unfolding W_def A_def
    by (intro sum_nonneg mult_nonneg_nonneg profV_nonneg zero_le_power) (use s0 in simp)
  have WB: "W \<le> 2 * n * \<sigma>"
    unfolding W_def by (rule Suc.IH)
  have n1: "1 \<le> n"
    unfolding n_def
    by simp
  have M0: "0 \<le> M"
  proof -
    have "0 \<le> (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)"
      using t0 by (intro infsum_nonneg) (simp add: mfam_nonneg)
    also have "\<dots> \<le> M" using majb by (simp add: majle_def)
    finally show ?thesis .
  qed
  have A0: "A 0 = 0" unfolding A_def by (rule profV_cfix_0)
  have Ann: "\<And>i. 0 \<le> A i" unfolding A_def by (rule profV_nonneg)
  have mknn: "\<And>k. 0 \<le> profV bphi k" by (rule profV_nonneg)
  have mkle: "\<And>k. profV bphi k \<le> M / t ^ k"
    by (rule profV_le_majle[OF t0 majb])

  \<comment> \<open>step 1: the per-degree recursion, weighted and summed\<close>
  have "(\<Sum>i=1..Suc N. A i * \<sigma> ^ i)
      \<le> (\<Sum>i=1..Suc N. (profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i
            + (\<Sum>k=2..i. profV bphi k * nconvpow A k i)) * \<sigma> ^ i)"
    unfolding A_def
    by (rule sum_mono, rule mult_right_mono)
       (rule profV_cfix_rec, use s0 in simp)
  also have "\<dots> = (\<Sum>i=1..Suc N. profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i * \<sigma> ^ i)
      + (\<Sum>i=1..Suc N. (\<Sum>k=2..i. profV bphi k * nconvpow A k i) * \<sigma> ^ i)"
    by (simp add: algebra_simps sum.distrib)
  also have "\<dots> \<le> n * \<sigma>
      + (\<Sum>i=1..Suc N. (\<Sum>k=2..i. profV bphi k * nconvpow A k i) * \<sigma> ^ i)"
  proof -
    have "(\<Sum>i=1..Suc N. profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i * \<sigma> ^ i)
        \<le> (\<Sum>i=1..Suc N. (if i = 1 then n else 0) * \<sigma> ^ i)"
    proof (rule sum_mono)
      fix i
      assume i: "i \<in> {1..Suc N}"
      have cid_le: "profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i \<le> (if i = 1 then n else 0)"
        using n_def profV_cId by blast
      have sig_nonneg: "0 \<le> \<sigma> ^ i"
        using s0 by simp
      show "profV (cId :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i * \<sigma> ^ i
          \<le> (if i = 1 then n else 0) * \<sigma> ^ i"
        by (rule mult_right_mono[OF cid_le sig_nonneg])
    qed
    also have "\<dots> = n * \<sigma>"
    proof -
      have "{1..Suc N} = insert 1 {2..Suc N}"
        by auto
      then have "(\<Sum>i=1..Suc N. (if i = 1 then n else 0) * \<sigma> ^ i)
          = n * \<sigma> + (\<Sum>i=2..Suc N. (if i = 1 then n else 0) * \<sigma> ^ i)"
        by simp
      also have "\<dots> = n * \<sigma>"
        by simp
      finally show ?thesis .
    qed
    finally show ?thesis
      by linarith
  qed
  also have "\<dots> \<le> n * \<sigma> + M * (2 * (W / t)\<^sup>2)"
  proof -
    \<comment> \<open>extend the inner \<open>k\<close>-range (vanishing above the diagonal), swap, apply the key bound\<close>
    have diag: "\<And>i. i \<in> {1..Suc N} \<Longrightarrow>
        (\<Sum>k=2..i. profV bphi k * nconvpow A k i)
          = (\<Sum>k=2..Suc N. profV bphi k * nconvpow A k i)"
    proof -
      fix i assume i: "i \<in> {1..Suc N}"
      show "(\<Sum>k=2..i. profV bphi k * nconvpow A k i)
          = (\<Sum>k=2..Suc N. profV bphi k * nconvpow A k i)"
      proof (rule sum.mono_neutral_left)
        show "finite {2..Suc N}" by simp
        show "{2..i} \<subseteq> {2..Suc N}" using i by auto
        show "\<forall>k\<in>{2..Suc N} - {2..i}. profV bphi k * nconvpow A k i = 0"
        proof
          fix k assume "k \<in> {2..Suc N} - {2..i}"
          hence "i < k" by auto
          thus "profV bphi k * nconvpow A k i = 0"
            by (simp add: A0 nconvpow_vanish)
        qed
      qed
    qed
    have "(\<Sum>i=1..Suc N. (\<Sum>k=2..i. profV bphi k * nconvpow A k i) * \<sigma> ^ i)
        = (\<Sum>i=1..Suc N. \<Sum>k=2..Suc N. profV bphi k * nconvpow A k i * \<sigma> ^ i)"
    proof (rule sum.cong[OF refl])
      fix x :: nat
      assume "x \<in> {1..Suc N}"
      then have "(\<Sum>n = 2..x. profV bphi n * nconvpow A n x) * \<sigma> ^ x = (\<Sum>n = 2..Suc N. profV bphi n * nconvpow A n x) * \<sigma> ^ x"
        using diag by moura
      then show "(\<Sum>n = 2..x. profV bphi n * nconvpow A n x) * \<sigma> ^ x = (\<Sum>n = 2..Suc N. profV bphi n * nconvpow A n x * \<sigma> ^ x)"
        by (metis (no_types) sum_distrib_right)
    qed
    also have "\<dots> = (\<Sum>k=2..Suc N. \<Sum>i=1..Suc N. profV bphi k * nconvpow A k i * \<sigma> ^ i)"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>k=2..Suc N. profV bphi k * (\<Sum>i=1..Suc N. nconvpow A k i * \<sigma> ^ i))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "\<dots> \<le> (\<Sum>k=2..Suc N. (M / t ^ k) * W ^ k)"
    proof (rule sum_mono)
      fix k assume k: "k \<in> {2..Suc N}"
      hence k2: "2 \<le> k" by simp
      have inner_le: "(\<Sum>i=1..Suc N. nconvpow A k i * \<sigma> ^ i) \<le> W ^ k"
      proof -
        have ext: "(\<Sum>i=1..Suc N. nconvpow A k i * \<sigma> ^ i)
            = (\<Sum>i\<le>Suc N. nconvpow A k i * \<sigma> ^ i)"
        proof -
          have "{..Suc N} = insert 0 {1..Suc N}" by auto
          moreover have "nconvpow A k 0 = 0"
            using A0 k2 nconvpow_vanish by force
          ultimately show ?thesis by simp
        qed
        have "(\<Sum>i\<le>Suc N. nconvpow A k i * \<sigma> ^ i)
            \<le> (\<Sum>i=1..Suc N + 1 - k. A i * \<sigma> ^ i) ^ k"
          by (metis (no_types, lifting) A0 Ann Suc_eq_plus1 add_leE k2 linorder_le_cases
              linorder_not_le nconvpow_partial_sum_le numeral_2_eq_2 s0)
        also have "\<dots> \<le> W ^ k"
        proof (rule power_mono)
          show "(\<Sum>i=1..Suc N + 1 - k. A i * \<sigma> ^ i) \<le> W"
            unfolding W_def
          proof (rule sum_mono2)
            show "finite {1..N}" by simp
            show "{1..Suc N + 1 - k} \<subseteq> {1..N}" using k2 by auto
            show "\<And>i. i \<in> {1..N} - {1..Suc N + 1 - k} \<Longrightarrow> 0 \<le> A i * \<sigma> ^ i"
              by (intro mult_nonneg_nonneg Ann zero_le_power) (use s0 in simp)
          qed
          show "0 \<le> (\<Sum>i=1..Suc N + 1 - k. A i * \<sigma> ^ i)"
            by (intro sum_nonneg mult_nonneg_nonneg Ann zero_le_power) (use s0 in simp)
        qed
        finally show ?thesis using ext by simp
      qed
      have Wknn: "0 \<le> (\<Sum>i=1..Suc N. nconvpow A k i * \<sigma> ^ i)"
        by (intro sum_nonneg mult_nonneg_nonneg nconvpow_nonneg[OF Ann] zero_le_power)
           (use s0 in simp)
      have "profV bphi k * (\<Sum>i=1..Suc N. nconvpow A k i * \<sigma> ^ i)
          \<le> (M / t ^ k) * (\<Sum>i=1..Suc N. nconvpow A k i * \<sigma> ^ i)"
        by (rule mult_right_mono[OF mkle Wknn])
      also have "\<dots> \<le> (M / t ^ k) * W ^ k"
        by (rule mult_left_mono[OF inner_le])
           (use M0 t0 in \<open>simp add: divide_nonneg_pos\<close>)
      finally show "profV bphi k * (\<Sum>i=1..Suc N. nconvpow A k i * \<sigma> ^ i)
          \<le> (M / t ^ k) * W ^ k" .
    qed
    also have "\<dots> = M * (\<Sum>k=2..Suc N. (W / t) ^ k)"
      by (simp add: power_divide sum_distrib_left algebra_simps)
       also have "\<dots> \<le> M * (2 * (W / t)\<^sup>2)"
    proof (rule mult_left_mono[OF _ M0])
      have Wt_nn: "0 \<le> W / t" using Wnn t0 by simp
      have "W / t \<le> 1/2"
      proof -
        have "W \<le> 2 * n * \<sigma>" by (rule WB)
        also have "\<dots> \<le> 2 * n * (t / (4 * n))"
          using s1 n1 by (intro mult_left_mono) simp_all
        also have "\<dots> = t / 2"
          using n1 by (simp add: field_simps)
        finally have "W \<le> t / 2" .
        thus ?thesis using t0 by (simp add: divide_le_eq)
      qed
      thus "(\<Sum>k=2..Suc N. (W / t) ^ k) \<le> 2 * (W / t)\<^sup>2"
        using geom_tail_le[OF Wt_nn] by presburger
    qed
    finally have conv_bound:
      "(\<Sum>i=1..Suc N. (\<Sum>k=2..i. profV bphi k * nconvpow A k i) * \<sigma> ^ i)
        \<le> M * (2 * (W / t)\<^sup>2)" .
    show ?thesis
      using conv_bound by linarith
  qed
  also have "\<dots> \<le> n * \<sigma> + n * \<sigma>"
  proof -
    have "M * (2 * (W / t)\<^sup>2) \<le> n * \<sigma>"
    proof -
      have "M * (2 * (W / t)\<^sup>2) = 2 * M * W\<^sup>2 / t\<^sup>2"
        by (simp add: power_divide)
      also have "\<dots> \<le> 2 * M * (2 * n * \<sigma>)\<^sup>2 / t\<^sup>2"
        using WB Wnn M0 t0
        by (intro divide_right_mono mult_left_mono power_mono) simp_all
      also have "\<dots> = 8 * M * n\<^sup>2 * \<sigma>\<^sup>2 / t\<^sup>2"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> \<le> n * \<sigma>"
      proof -
        have "8 * (M + 1) * n * \<sigma> \<le> t\<^sup>2"
        proof -
          have pos: "0 < 8 * (M + 1) * n"
            using M0 n1 by (intro mult_pos_pos) simp_all
          have "\<sigma> * (8 * (M + 1) * n)
              \<le> (t\<^sup>2 / (8 * (M + 1) * n)) * (8 * (M + 1) * n)"
            by (rule mult_right_mono[OF s2]) (use pos in simp)
          also have "\<dots> = t\<^sup>2"
            using pos by (simp add: field_simps)
          finally show ?thesis
            by (simp add: mult_ac)
        qed
        hence "8 * M * n * \<sigma> \<le> t\<^sup>2"
          by (smt (verit, ccfv_SIG) landau_o.R_mult_right_mono n1 s0)
        hence "8 * M * n * \<sigma> * (n * \<sigma>) \<le> t\<^sup>2 * (n * \<sigma>)"
          using n1 s0 by (intro mult_right_mono) simp_all
        hence "8 * M * n\<^sup>2 * \<sigma>\<^sup>2 \<le> t\<^sup>2 * (n * \<sigma>)"
          by (simp add: power2_eq_square algebra_simps)
        thus ?thesis
          using t0 by (simp add: pos_divide_le_eq, argo)

      qed
      finally show ?thesis .
    qed
    thus ?thesis by linarith
  qed
  also have "\<dots> = 2 * n * \<sigma>" by simp
  finally show ?case .
qed

text \<open>Packaging: the \<open>majle\<close> bound for \<open>cfix\<close>, and the induced bounds for the
  composed monomial families.\<close>

lemma majle_of_partial_profile_bounds:
  fixes u :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes unn: "\<And>\<gamma>. 0 \<le> u \<gamma>"
    and s0: "0 < \<sigma>"
    and bnd: "\<And>D. (\<Sum>d\<le>D. profS u d * \<sigma> ^ d) \<le> B"
  shows "majle \<sigma> u B"
proof -
  have partial: "(\<Sum>\<gamma>\<in>F. mfam \<sigma> u \<gamma>) \<le> B" if F: "finite F" "F \<subseteq> ra_idx" for F
  proof -
    define D where "D = Max (insert 0 (ra_deg ` F))"
    have degF: "\<And>\<gamma>. \<gamma> \<in> F \<Longrightarrow> ra_deg \<gamma> \<le> D"
      unfolding D_def using F(1) by (intro Max_ge) auto
    have Fsub: "F \<subseteq> (\<Union>d\<in>{..D}. ra_blk d)"
      using F(2) degF by (auto simp: ra_blk_def)
    have "(\<Sum>\<gamma>\<in>F. mfam \<sigma> u \<gamma>) \<le> (\<Sum>\<gamma>\<in>(\<Union>d\<in>{..D}. ra_blk d). mfam \<sigma> u \<gamma>)"
      by (rule sum_mono2[OF _ Fsub],
          auto intro: finite_UN_I finite_ra_blk mfam_nonneg simp: mfam_nonneg s0 less_imp_le)
    also have "\<dots> = (\<Sum>d\<le>D. \<Sum>\<gamma>\<in>ra_blk d. mfam \<sigma> u \<gamma>)"
      using finite_ra_blk by (subst sum.UNION_disjoint, auto, simp add: disjoint_iff ra_blk_def)
    also have "\<dots> = (\<Sum>d\<le>D. profS u d * \<sigma> ^ d)"
      unfolding mfam_def profS_def
      by (rule sum.cong[OF refl], simp add: ra_blk_def sum_distrib_right abs_of_nonneg unn)
    also have "\<dots> \<le> B" by (rule bnd)
    finally show ?thesis .
  qed
  have summ: "mfam \<sigma> u summable_on ra_idx"
  proof (rule nonneg_bdd_above_summable_on)
    show "\<And>\<gamma>. \<gamma> \<in> ra_idx \<Longrightarrow> 0 \<le> mfam \<sigma> u \<gamma>"
      using s0 by (simp add: mfam_nonneg)
    show "bdd_above (sum (mfam \<sigma> u) ` {F. F \<subseteq> ra_idx \<and> finite F})"
      by (rule bdd_aboveI[where M = B]) (use partial in auto)
  qed
  moreover have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>ra_idx. mfam \<sigma> u \<gamma>) \<le> B"
    by (rule infsum_le_finite_sums[OF summ]) (use partial in auto)
  ultimately show ?thesis by (simp add: majle_def)
qed

theorem cfix_majle:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "majle \<sigma> (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) (2 * n * \<sigma>)"
proof (rule majle_of_partial_profile_bounds)
  show "\<And>\<gamma>. 0 \<le> norm (cfix bphi \<gamma>)" by simp
  show "0 < \<sigma>" by (rule s0)
  fix D :: nat
  have prof_eq: "profS (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) = profV (cfix bphi)"
    by (rule ext) (simp add: profS_def profV_def)
  have "(\<Sum>d\<le>D. profV (cfix bphi) d * \<sigma> ^ d) = (\<Sum>d=1..D. profV (cfix bphi) d * \<sigma> ^ d)"
  proof -
    have "{..D} = insert 0 {1..D}" by auto
    thus ?thesis by (simp add: profV_cfix_0)
  qed
  also have "\<dots> \<le> 2 * n * \<sigma>"
    unfolding n_def
    by (rule cfix_partial_sums_bounded[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  finally show "(\<Sum>d\<le>D. profS (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) d * \<sigma> ^ d) \<le> 2 * n * \<sigma>"
    by (simp add: prof_eq)
qed

text \<open>A majle-bound on vector coefficients gives an absolutely convergent
  power series on the closed working ball.\<close>

lemma majle_vector_power_series_summable:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes s0: "0 \<le> \<sigma>"
    and maj: "majle \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) K"
    and hle: "norm h \<le> \<sigma>"
  shows "(\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R c \<gamma>) summable_on (ra_idx::('a \<Rightarrow> nat) set)"
proof (rule abs_summable_summable,
    rule summable_on_comparison_test[where f = "mfam \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>))"])
  show "mfam \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    using maj by (simp add: majle_def)
next
  fix \<gamma> :: "'a \<Rightarrow> nat"
  assume g: "\<gamma> \<in> ra_idx"
  have "norm (ra_monomial h \<gamma> *\<^sub>R c \<gamma>) = \<bar>ra_monomial h \<gamma>\<bar> * norm (c \<gamma>)"
    by simp
  also have "\<dots> \<le> \<sigma> ^ ra_deg \<gamma> * norm (c \<gamma>)"
    by (rule mult_right_mono[OF ra_monomial_abs_le_pow[OF g hle]]) simp
  also have "\<dots> = mfam \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) \<gamma>"
    by (simp add: mfam_def mult.commute)
  finally show "norm (ra_monomial h \<gamma> *\<^sub>R c \<gamma>) \<le> mfam \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) \<gamma>" .
next
  fix \<gamma> :: "'a \<Rightarrow> nat"
  assume "\<gamma> \<in> ra_idx"
  show "0 \<le> norm (ra_monomial h \<gamma> *\<^sub>R c \<gamma>)"
    by simp
qed

lemma majle_vector_power_series_has_sum:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes s0: "0 \<le> \<sigma>"
    and maj: "majle \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) K"
    and hle: "norm h \<le> \<sigma>"
  shows "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R c \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R c \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
  by (rule has_sum_infsum)
     (rule majle_vector_power_series_summable[OF s0 maj hle])

corollary cfix_power_series_has_sum:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
    and hle: "norm h \<le> \<sigma>"
  shows "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
proof (rule majle_vector_power_series_has_sum)
  show "0 \<le> \<sigma>"
    using s0 by simp
  show "majle \<sigma> (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) (2 * n * \<sigma>)"
    unfolding n_def
    by (rule cfix_majle[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  show "norm h \<le> \<sigma>"
    by (rule hle)
qed

lemma cfix_value_norm_bound_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
    and hle: "norm h \<le> \<sigma>"
  shows "norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      \<le> 2 * n * \<sigma>"
proof -
  let ?H = "\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>"
  have hs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      has_sum ?H) (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding n_def
    by (rule cfix_power_series_has_sum[OF t0 majb s0])
       (use s1 s2 hle in \<open>simp_all add: n_def\<close>)
  have maj: "majle \<sigma> (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) (2 * n * \<sigma>)"
    unfolding n_def
    by (rule cfix_majle[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  define S where "S = (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
      mfam \<sigma> (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) \<gamma>)"
  have dom_sum: "((mfam \<sigma> (\<lambda>\<gamma>. norm (cfix bphi \<gamma>))) has_sum S)
      (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding S_def using maj by (simp add: majle_def has_sum_infsum)
  have term_bound: "norm (ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      \<le> mfam \<sigma> (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) \<gamma>"
    if g: "\<gamma> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<gamma>
  proof -
    have "norm (ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        = \<bar>ra_monomial h \<gamma>\<bar> * norm (cfix bphi \<gamma>)"
      by simp
    also have "\<dots> \<le> \<sigma> ^ ra_deg \<gamma> * norm (cfix bphi \<gamma>)"
      by (rule mult_right_mono[OF ra_monomial_abs_le_pow[OF g hle]]) simp
    also have "\<dots> = mfam \<sigma> (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) \<gamma>"
      by (simp add: mfam_def mult.commute)
    finally show ?thesis .
  qed
  have "norm ?H \<le> S"
    by (rule norm_infsum_le[OF hs dom_sum]) (use term_bound in simp)
  also have "\<dots> \<le> 2 * n * \<sigma>"
    using maj by (simp add: S_def majle_def)
  finally show ?thesis .
qed

lemma majle_geometric_weight_summable:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes t0: "0 < t"
    and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and K0: "0 \<le> K"
    and Kt: "K < t"
  shows "(\<lambda>\<beta>. norm (bphi \<beta>) * K ^ ra_deg \<beta>)
    summable_on (ra_idx::('a \<Rightarrow> nat) set)"
proof (rule summable_on_comparison_test
    [where f = "\<lambda>\<beta>. M * (K / t) ^ ra_deg \<beta>"])
  have M0: "0 \<le> M"
  proof -
    have "0 \<le> (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)"
      using t0 by (intro infsum_nonneg) (simp add: mfam_nonneg)
    also have "\<dots> \<le> M"
      using majb by (simp add: majle_def)
    finally show ?thesis .
  qed
  have q0: "0 \<le> K / t"
    using K0 t0 by simp
  have q1: "K / t < 1"
    using Kt t0 by (simp add: divide_less_eq)
  have "(\<lambda>\<beta>::'a \<Rightarrow> nat. (K / t) ^ ra_deg \<beta>) summable_on ra_idx"
    by (rule geom_idx_summable[OF q0 q1])
  thus "(\<lambda>\<beta>. M * (K / t) ^ ra_deg \<beta>)
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    by (rule summable_on_cmult_right)
next
  fix \<beta> :: "'a \<Rightarrow> nat"
  assume b: "\<beta> \<in> ra_idx"
  have "norm (bphi \<beta>) * K ^ ra_deg \<beta>
      \<le> (M / t ^ ra_deg \<beta>) * K ^ ra_deg \<beta>"
    by (rule mult_right_mono[OF coeff_le_majle[OF t0 majb _ b]])
       (use K0 in simp_all)
  also have "\<dots> = M * (K / t) ^ ra_deg \<beta>"
    using t0 by (simp add: power_divide)
  finally show "norm (bphi \<beta>) * K ^ ra_deg \<beta>
      \<le> M * (K / t) ^ ra_deg \<beta>" .
next
  fix \<beta> :: "'a \<Rightarrow> nat"
  assume "\<beta> \<in> ra_idx"
  show "0 \<le> norm (bphi \<beta>) * K ^ ra_deg \<beta>"
    using K0 by simp
qed

lemma cfix_power_series_real_analytic_on_ball_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  defines "H \<equiv> (\<lambda>h::'a. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
      ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "real_analytic_on H (ball (0::'a) (\<sigma> / 2))"
proof -
  have n1: "1 \<le> n"
    unfolding n_def by simp
  have Hmaj: "majle \<sigma> (\<lambda>\<gamma>. norm (cfix bphi \<gamma>)) (2 * n * \<sigma>)"
    unfolding n_def
    by (rule cfix_majle[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open (ball (0::'a) (\<sigma> / 2))"
      by simp
  next
    fix y0 :: 'a
    assume y0: "y0 \<in> ball (0::'a) (\<sigma> / 2)"
    have y0_lt: "norm y0 < \<sigma> / 2"
      using y0 by (simp add: dist_norm)
    define r where "r = (\<sigma> - norm y0) / (2 * n)"
    have r0: "0 < r"
      using y0_lt n1 s0 by (simp add: r_def)
    have rle: "r \<le> r"
      by simp
    define K where "K = n * r + norm y0"
    have K0: "0 \<le> K"
      using n1 r0 by (simp add: K_def)
    have Klt: "K < \<sigma>"
    proof -
      have "n * r = (\<sigma> - norm y0) / 2"
        using n1 by (simp add: r_def field_simps)
      hence "K = (\<sigma> + norm y0) / 2"
        by (simp add: K_def)
      also have "\<dots> < \<sigma>"
        using y0_lt s0 by simp
      finally show ?thesis .
    qed
    obtain cid :: "('a \<Rightarrow> nat) \<Rightarrow> 'a" where
      cid_series: "\<And>y::'a. ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R cid \<alpha>) has_sum y) ra_idx"
      and cid_maj: "\<And>\<rho>::real. 0 \<le> \<rho> \<Longrightarrow>
        majle \<rho> (\<lambda>\<alpha>. norm (cid \<alpha>)) (real (card (Basis :: 'a set)) * \<rho>)"
    proof -
      show thesis
      proof (rule identity_coeff_series_majle)
        fix cid :: "('a \<Rightarrow> nat) \<Rightarrow> 'a"
        assume cid_series: "\<And>y::'a. ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R cid \<alpha>) has_sum y) ra_idx"
          and cid_maj: "\<And>\<rho>::real. 0 \<le> \<rho> \<Longrightarrow>
            majle \<rho> (\<lambda>\<alpha>. norm (cid \<alpha>)) (real (card (Basis :: 'a set)) * \<rho>)"
        show thesis
          by (rule that[OF cid_series cid_maj])
      qed
    qed
    have id_ser: "\<And>x. dist x y0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - y0) \<alpha> *\<^sub>R cid \<alpha>) has_sum (x - y0))
          (ra_idx::('a \<Rightarrow> nat) set)"
      using cid_series by simp
    have cidmaj_r: "majle r (\<lambda>\<alpha>. norm (cid \<alpha>)) (n * r)"
      using cid_maj[of r] r0 by (simp add: n_def)
    have mon_ser: "\<exists>cc. smaj y0 r r cc (\<lambda>x::'a. ra_monomial x \<beta>) (K ^ ra_deg \<beta>)"
      if b: "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<beta>
    proof -
      have raw: "\<exists>cc. smaj y0 r r cc
          (\<lambda>x::'a. ra_monomial ((x - y0) - (- y0)) \<beta>) (K ^ ra_deg \<beta>)"
      proof (rule smaj_ra_monomial_compose[where z = "- y0", OF _ id_ser cidmaj_r _ K0])
        show "0 \<le> r"
          using r0 by simp
        fix e :: 'a
        assume e: "e \<in> Basis"
        have "\<bar>(- y0) \<bullet> e\<bar> \<le> norm y0"
          using Basis_le_norm[OF e, of "- y0"] by simp
        thus "n * r + \<bar>(- y0) \<bullet> e\<bar> \<le> K"
          by (simp add: K_def)
      qed
      thus ?thesis
        by simp
    qed
    obtain CC where CC:
      "\<And>\<beta>. \<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set) \<Longrightarrow>
        smaj y0 r r (CC \<beta>) (\<lambda>x::'a. ra_monomial x \<beta>) (K ^ ra_deg \<beta>)"
      using mon_ser by metis
    have ser: "series_on y0 r (CC \<beta>) (\<lambda>x::'a. ra_monomial x \<beta>)"
      if b: "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<beta>
      using CC[OF b] by (simp add: smaj_def)
    have maj: "majle r (CC \<beta>) (K ^ ra_deg \<beta>)"
      if b: "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<beta>
      using CC[OF b] by (simp add: smaj_def)
    have gsum: "(\<lambda>\<beta>. norm (cfix bphi \<beta>) * (K ^ ra_deg \<beta>))
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule majle_geometric_weight_summable[OF s0 Hmaj K0 Klt])
    have Gval: "\<And>x::'a. dist x y0 < r \<Longrightarrow>
        ((\<lambda>\<beta>. ra_monomial x \<beta> *\<^sub>R cfix bphi \<beta>) has_sum H x)
          (ra_idx::('a \<Rightarrow> nat) set)"
    proof -
      fix x :: 'a
      assume x: "dist x y0 < r"
      have nx: "norm x \<le> \<sigma>"
      proof -
        have "norm x \<le> norm (x - y0) + norm y0"
          by (metis add.commute add_diff_cancel_left' norm_triangle_sub)
        also have "\<dots> < r + norm y0"
          using x by (simp add: dist_norm)
        also have "\<dots> \<le> n * r + norm y0"
          using n1 r0 by (intro add_right_mono mult_left_le_one_le) simp_all
        also have "\<dots> = K"
          by (simp add: K_def)
        also have "\<dots> < \<sigma>"
          by (rule Klt)
        finally show ?thesis
          by simp
      qed
      show "((\<lambda>\<beta>. ra_monomial x \<beta> *\<^sub>R cfix bphi \<beta>) has_sum H x)
          (ra_idx::('a \<Rightarrow> nat) set)"
        unfolding H_def n_def
        by (rule cfix_power_series_has_sum[OF t0 majb s0])
           (use s1 s2 nx in \<open>simp_all add: n_def\<close>)
    qed
    have recentered: "\<forall>x. dist x y0 < r \<longrightarrow>
       ((\<lambda>\<gamma>. ra_monomial (x - y0) \<gamma> *\<^sub>R
          (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set). CC \<beta> \<gamma> *\<^sub>R cfix bphi \<beta>))
        has_sum H x) (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule series_on_majdom_vec[OF r0 rle ser maj gsum Gval])
    show "\<exists>r>0. \<exists>c. \<forall>x. dist x y0 < r \<longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - y0) \<alpha> *\<^sub>R c \<alpha>) has_sum H x)
          (ra_idx::('a \<Rightarrow> nat) set)"
      by (intro exI[where x=r] conjI exI[where x="\<lambda>\<gamma>. \<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            CC \<beta> \<gamma> *\<^sub>R cfix bphi \<beta>"]) (use r0 recentered in auto)
  qed
qed

corollary cfix_power_series_converges_near_zero:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t"
    and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
  obtains \<sigma> where "0 < \<sigma>"
    and "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
proof -
  define n where "n = real (card (Basis :: 'a set))"
  have n1: "1 \<le> n"
    unfolding n_def by simp
  have M0: "0 \<le> M"
  proof -
    have "0 \<le> (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. mfam t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)"
      using t0 by (intro infsum_nonneg) (simp add: mfam_nonneg)
    also have "\<dots> \<le> M"
      using majb by (simp add: majle_def)
    finally show ?thesis .
  qed
  define \<sigma> where "\<sigma> = min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n)) / 2"
  have a_pos: "0 < t / (4 * n)"
    using t0 n1 by simp
  have b_pos: "0 < t\<^sup>2 / (8 * (M + 1) * n)"
    using t0 M0 n1 by (intro divide_pos_pos mult_pos_pos) simp_all
  have \<sigma>0: "0 < \<sigma>"
    using a_pos b_pos by (simp add: \<sigma>_def)
  have min_nonneg: "0 \<le> min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
    using a_pos b_pos by simp
  have half_min_le:
    "min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n)) / 2
      \<le> min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
  proof -
    have "min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n)) / 2
        = (1/2) * min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
      by simp
    also have "\<dots> \<le> 1 * min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
      by (rule mult_right_mono) (use min_nonneg in simp_all)
    finally show ?thesis
      by simp
  qed
  have s1: "\<sigma> \<le> t / (4 * n)"
  proof -
    have "\<sigma> \<le> min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
      unfolding \<sigma>_def by (rule half_min_le)
    also have "\<dots> \<le> t / (4 * n)"
      by simp
    finally show ?thesis .
  qed
  have s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  proof -
    have "\<sigma> \<le> min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
      unfolding \<sigma>_def by (rule half_min_le)
    also have "\<dots> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule that[OF \<sigma>0])
    fix h :: 'a
    assume h: "norm h < \<sigma>"
    have s1': "\<sigma> \<le> t / (4 * real DIM('a))"
      using s1 by (simp add: n_def)
    have s2': "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * real DIM('a))"
      using s2 by (simp add: n_def)
    show "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule cfix_power_series_has_sum[OF t0 majb \<sigma>0 s1' s2'])
         (use h in simp)
  qed
qed

theorem cfix_formal_inverse_data:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t"
    and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
  obtains \<sigma> where "0 < \<sigma>"
    and "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
    and "\<And>\<gamma>. \<gamma> \<in> ra_idx \<Longrightarrow>
      cfix bphi \<gamma> =
        cId \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
proof -
  show ?thesis
  proof (rule cfix_power_series_converges_near_zero[OF t0 majb])
    fix \<sigma>
    assume s0: "0 < \<sigma>"
      and conv: "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
    have coeff: "\<And>\<gamma>. \<gamma> \<in> ra_idx \<Longrightarrow>
        cfix bphi \<gamma> =
          cId \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
      by (rule cfix_coeff_equation_infsum[OF _ low])
    show thesis
      by (rule that[OF s0 conv coeff])
  qed
qed

corollary cfix_component_series_on_near_zero:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t"
    and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
  obtains \<sigma> where "0 < \<sigma>"
    and "\<And>b. b \<in> Basis \<Longrightarrow>
      series_on (0::'a) \<sigma> (\<lambda>\<gamma>. cfix bphi \<gamma> \<bullet> b)
        (\<lambda>h. (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<bullet> b)"
proof -
  show ?thesis
  proof (rule cfix_power_series_converges_near_zero[OF t0 majb])
    fix \<sigma>
    assume s0: "0 < \<sigma>"
      and conv: "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
    have ser: "series_on (0::'a) \<sigma> (\<lambda>\<gamma>. cfix bphi \<gamma> \<bullet> b)
        (\<lambda>h. (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<bullet> b)"
      if b: "b \<in> Basis" for b
      unfolding series_on_def
    proof (intro allI impI)
      fix h :: 'a
      assume h: "dist h (0::'a) < \<sigma>"
      have hs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
        by (rule conv) (use h in \<open>simp add: dist_norm\<close>)
      have "((\<lambda>\<gamma>. (ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<bullet> b)
          has_sum ((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<bullet> b))
          (ra_idx::('a \<Rightarrow> nat) set)"
        by (rule has_sum_bounded_linear[OF bounded_linear_inner_left hs])
      thus "((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R (cfix bphi \<gamma> \<bullet> b))
          has_sum ((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<bullet> b))
          (ra_idx::('a \<Rightarrow> nat) set)"
        by simp
    qed
    show thesis
      by (rule that[OF s0 ser])
  qed
qed

corollary cfix_mono_co_series_on_near_zero:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t"
    and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
  obtains \<sigma> where "0 < \<sigma>"
    and "\<And>\<beta>. series_on (0::'a) \<sigma> (mono_co (cfix bphi) \<beta>)
      (\<lambda>h. ra_monomial
        (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta>)"
proof -
  show ?thesis
  proof (rule cfix_power_series_converges_near_zero[OF t0 majb])
    fix \<sigma>
    assume s0: "0 < \<sigma>"
      and conv: "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
    have ser: "series_on (0::'a) \<sigma> (mono_co (cfix bphi) \<beta>)
      (\<lambda>h. ra_monomial
        (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta>)"
      for \<beta>
      by (rule mono_co_series[where c = "cfix bphi"])
         (use conv in \<open>simp add: dist_norm\<close>)
    show thesis
      by (rule that[OF s0 ser])
  qed
qed

text \<open>\<open>majle\<close> bounds for the composed monomial families of any zero-constant family
  whose weighted profile partial sums are bounded.\<close>

lemma mono_co_majle:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes s0: "0 < \<sigma>"
    and Bnn: "0 \<le> B"
    and bnd: "\<And>D. (\<Sum>i=1..D. profV c i * \<sigma> ^ i) \<le> B"
    and A0: "profV c 0 = 0"
  shows "majle \<sigma> (mono_co c \<beta>) (B ^ ra_deg \<beta>)"
proof -
  have majabs: "majle \<sigma> (\<lambda>\<gamma>. \<bar>mono_co c \<beta> \<gamma>\<bar>) (B ^ ra_deg \<beta>)"
  proof (rule majle_of_partial_profile_bounds)
    show "\<And>\<gamma>. 0 \<le> \<bar>mono_co c \<beta> \<gamma>\<bar>" by simp
    show "0 < \<sigma>" by (rule s0)
    fix D :: nat
    have prof_eq: "profS (\<lambda>\<gamma>. \<bar>mono_co c \<beta> \<gamma>\<bar>) = profS (mono_co c \<beta>)"
      by (rule ext) (simp add: profS_def)
    show "(\<Sum>d\<le>D. profS (\<lambda>\<gamma>. \<bar>mono_co c \<beta> \<gamma>\<bar>) d * \<sigma> ^ d) \<le> B ^ ra_deg \<beta>"
    proof (cases "ra_deg \<beta> = 0")
      case True
      \<comment> \<open>degree-zero monomial: the coefficients are (at most) the \<open>cone\<close> family\<close>
      have "(\<Sum>d\<le>D. profS (mono_co c \<beta>) d * \<sigma> ^ d)
          \<le> (\<Sum>d\<le>D. nconvpow (profV c) 0 d * \<sigma> ^ d)"
        by (smt (verit) True mult_right_mono profS_mono_co s0 sum_mono zero_le_power)
      also have "\<dots> = 1"
      proof -
        have "{..D} = insert 0 {1..D}" by auto
        thus ?thesis
          by (simp add: ndelta_def)
      qed
      finally show ?thesis
        using True by (simp add: prof_eq)
    next
      case False
      hence k1: "1 \<le> ra_deg \<beta>" by simp
      have "(\<Sum>d\<le>D. profS (mono_co c \<beta>) d * \<sigma> ^ d)
          \<le> (\<Sum>d\<le>D. nconvpow (profV c) (ra_deg \<beta>) d * \<sigma> ^ d)"
        by (rule sum_mono, rule mult_right_mono)
           (use profS_mono_co s0 in simp_all)
      also have "\<dots> \<le> (\<Sum>i=1..D + 1 - ra_deg \<beta>. profV c i * \<sigma> ^ i) ^ ra_deg \<beta>"
        apply (rule nconvpow_partial_sum_le)
        apply (simp add: profV_nonneg)
        apply (simp add: A0)
        using s0 apply fastforce
        using k1 by blast
      also have "\<dots> \<le> B ^ ra_deg \<beta>"
        by (rule power_mono[OF bnd])
           (intro sum_nonneg mult_nonneg_nonneg profV_nonneg zero_le_power,
            use s0 in simp)
      finally show ?thesis by (simp add: prof_eq)
    qed
  qed
  \<comment> \<open>transfer from the absolute-value family: \<open>mfam\<close> only sees absolute values\<close>
  have mfam_eq: "mfam \<sigma> (\<lambda>\<gamma>. \<bar>mono_co c \<beta> \<gamma>\<bar>) = mfam \<sigma> (mono_co c \<beta>)"
    by (rule ext) (simp add: mfam_def)
  show ?thesis
    using majabs by (simp add: majle_def mfam_eq)
qed

corollary cfix_mono_co_majle:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "majle \<sigma> (mono_co (cfix bphi) \<beta>) ((2 * n * \<sigma>) ^ ra_deg \<beta>)"
proof (rule mono_co_majle)
  show "0 < \<sigma>" by (rule s0)
  show "0 \<le> 2 * n * \<sigma>"
    using s0 by (simp add: n_def)
  show "\<And>D. (\<Sum>i=1..D. profV (cfix bphi) i * \<sigma> ^ i) \<le> 2 * n * \<sigma>"
    unfolding n_def
    by (rule cfix_partial_sums_bounded[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  show "profV (cfix bphi) 0 = 0"
    by (rule profV_cfix_0)
qed

lemma series_on_majle_value_bound:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes s0: "0 \<le> \<sigma>"
    and r\<sigma>: "r \<le> \<sigma>"
    and ser: "series_on x0 r c F"
    and maj: "majle \<sigma> c K"
    and x: "dist x x0 < r"
  shows "\<bar>F x\<bar> \<le> K"
proof -
  have hs: "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> * c \<alpha>) has_sum F x) ra_idx"
    using ser x by (simp add: series_on_def)
  define S where "S = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam \<sigma> c \<alpha>)"
  have dom_sum: "(mfam \<sigma> c has_sum S) ra_idx"
    unfolding S_def
    using maj by (simp add: majle_def has_sum_infsum)
  have hle: "norm (x - x0) \<le> \<sigma>"
    using x r\<sigma> by (simp add: dist_norm)
  have term_bound:
    "\<bar>ra_monomial (x - x0) \<alpha> * c \<alpha>\<bar> \<le> mfam \<sigma> c \<alpha>"
    if a: "\<alpha> \<in> ra_idx" for \<alpha>
  proof -
    have "\<bar>ra_monomial (x - x0) \<alpha> * c \<alpha>\<bar>
        = \<bar>ra_monomial (x - x0) \<alpha>\<bar> * \<bar>c \<alpha>\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> \<sigma> ^ ra_deg \<alpha> * \<bar>c \<alpha>\<bar>"
      by (rule mult_right_mono[OF ra_monomial_abs_le_pow[OF a hle]]) simp
    also have "\<dots> = mfam \<sigma> c \<alpha>"
      by (simp add: mfam_def mult.commute)
    finally show ?thesis .
  qed
  have norm_le: "norm (F x) \<le> S"
    by (rule norm_infsum_le[OF hs dom_sum]) (use term_bound in simp)
  hence "\<bar>F x\<bar> \<le> S"
    by simp
  also have "\<dots> \<le> K"
    using maj by (simp add: S_def majle_def)
  finally show ?thesis .
qed

lemma cfix_mono_co_fubini_inputs_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows mono_series:
    "series_on (0::'a) \<sigma> (mono_co (cfix bphi) \<beta>)
      (\<lambda>h. ra_monomial
        (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta>)"
    and mono_maj:
    "majle \<sigma> (mono_co (cfix bphi) \<beta>) ((2 * n * \<sigma>) ^ ra_deg \<beta>)"
    and outer_summable:
    "(\<lambda>\<beta>. norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>)
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
proof -
  show "series_on (0::'a) \<sigma> (mono_co (cfix bphi) \<beta>)
      (\<lambda>h. ra_monomial
        (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta>)"
  proof (rule mono_co_series[where c = "cfix bphi"])
    fix h :: 'a
    assume "dist h (0::'a) < \<sigma>"
    show "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
      unfolding n_def
      by (rule cfix_power_series_has_sum[OF t0 majb s0])
         (use s1 s2 \<open>dist h (0::'a) < \<sigma>\<close> in \<open>simp_all add: n_def dist_norm\<close>)
  qed
next
  show "majle \<sigma> (mono_co (cfix bphi) \<beta>) ((2 * n * \<sigma>) ^ ra_deg \<beta>)"
    unfolding n_def
    by (rule cfix_mono_co_majle[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
next
  have n1: "1 \<le> n"
    unfolding n_def by simp
  have K0: "0 \<le> 2 * n * \<sigma>"
    using n1 s0 by simp
  have Kt: "2 * n * \<sigma> < t"
  proof -
    have "2 * n * \<sigma> \<le> 2 * n * (t / (4 * n))"
      using s1 n1 by (intro mult_left_mono) simp_all
    also have "\<dots> = t / 2"
      using n1 by (simp add: field_simps)
    also have "\<dots> < t"
      using t0 by simp
    finally show ?thesis .
  qed
  show "(\<lambda>\<beta>. norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>)
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    by (rule majle_geometric_weight_summable[OF t0 majb K0 Kt])
qed

lemma cfix_phi_comp_series_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
    ((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      has_sum
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set)"
proof -
  define H where "H = (\<lambda>h::'a.
    \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)"
  have mono_series:
    "series_on (0::'a) \<sigma> (mono_co (cfix bphi) \<beta>)
      (\<lambda>h. ra_monomial (H h) \<beta>)" for \<beta>
    unfolding H_def n_def
    by (rule cfix_mono_co_fubini_inputs_at_scale(1)[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  have mono_maj:
    "majle \<sigma> (mono_co (cfix bphi) \<beta>) ((2 * n * \<sigma>) ^ ra_deg \<beta>)" for \<beta>
    unfolding n_def
    by (rule cfix_mono_co_fubini_inputs_at_scale(2)[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  have outer_summable:
    "(\<lambda>\<beta>. norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>)
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding n_def
    by (rule cfix_mono_co_fubini_inputs_at_scale(3)[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  have Gval:
    "((\<lambda>\<beta>. ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)
        has_sum
          (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>))
        (ra_idx::('a \<Rightarrow> nat) set)"
    if h: "dist h (0::'a) < \<sigma>" for h
  proof -
    have val_bound:
      "\<bar>ra_monomial (H h) \<beta>\<bar> \<le> (2 * n * \<sigma>) ^ ra_deg \<beta>"
      if b: "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<beta>
      by (rule series_on_majle_value_bound[OF _ _ mono_series mono_maj h])
         (use s0 in simp_all)
    have abs_summ:
      "(\<lambda>\<beta>. norm (ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>))
        summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    proof (rule summable_on_comparison_test[OF outer_summable])
      fix \<beta> :: "'a \<Rightarrow> nat"
      assume b: "\<beta> \<in> ra_idx"
      have "norm (ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)
          = \<bar>ra_monomial (H h) \<beta>\<bar> * norm (bphi \<beta>)"
        by simp
      also have "\<dots> \<le> (2 * n * \<sigma>) ^ ra_deg \<beta> * norm (bphi \<beta>)"
        by (rule mult_right_mono[OF val_bound[OF b]]) simp
      also have "\<dots> = norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>"
        by (simp add: mult.commute)
      finally show "norm (ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)
          \<le> norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>" .
    next
      fix \<beta> :: "'a \<Rightarrow> nat"
      assume "\<beta> \<in> ra_idx"
      show "0 \<le> norm (ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)"
        by simp
    qed
    have summ: "(\<lambda>\<beta>. ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)
        summable_on (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule abs_summable_summable[OF abs_summ])
    show ?thesis
      by (rule has_sum_infsum[OF summ])
  qed
  have main: "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
    ((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      has_sum
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set)"
    by (rule series_on_majdom_vec
        [where CC = "\<lambda>\<beta>. mono_co (cfix bphi) \<beta>"
           and Fn = "\<lambda>\<beta> h. ra_monomial (H h) \<beta>"
           and vg = bphi
           and Kk = "\<lambda>\<beta>. (2 * n * \<sigma>) ^ ra_deg \<beta>"
           and \<sigma> = \<sigma> and r = \<sigma>
           and G = "\<lambda>h. \<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
             ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>"])
       (use s0 mono_series mono_maj outer_summable Gval in auto)
  show ?thesis
    using main by (simp add: H_def)
qed

lemma cfix_functional_fixed_point_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
    (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      = h + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
proof (intro allI impI)
  fix h :: 'a
  assume h: "dist h (0::'a) < \<sigma>"
  define H where "H =
    (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)"
  define N where "N =
    (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
      ra_monomial H \<beta> *\<^sub>R bphi \<beta>)"
  have Hhs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) has_sum H)
      (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding H_def n_def
    by (rule cfix_power_series_has_sum[OF t0 majb s0])
       (use s1 s2 h in \<open>simp_all add: n_def dist_norm\<close>)
  have Nhs: "((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      has_sum N) (ra_idx::('a \<Rightarrow> nat) set)"
  proof -
    have comp: "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R
          (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
        has_sum
          (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial
              (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
                ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
        (ra_idx::('a \<Rightarrow> nat) set)"
      unfolding n_def
      by (rule cfix_phi_comp_series_at_scale[OF t0 majb s0])
         (use s1 s2 in \<open>simp_all add: n_def\<close>)
    show ?thesis
      using comp h by (simp add: N_def H_def)
  qed
  have rhs_hs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R
        (cId \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)))
      has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set)"
  proof -
    have "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cId \<gamma>
          + ra_monomial h \<gamma> *\<^sub>R
            (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
        has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule has_sum_add[OF cId_series Nhs[unfolded diff_zero]])
    thus ?thesis
      by (simp add: scaleR_add_right)
  qed
  have rhs_eq_cfix:
    "ra_monomial h \<gamma> *\<^sub>R
        (cId \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      = ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>"
    if g: "\<gamma> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<gamma>
    using cfix_coeff_equation_infsum[OF g low] by simp
  have rhs_cfix_hs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set)"
  proof -
    have "(((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R
          (cId \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            mono_co (cfix bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)))
        has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set))
      = (((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set))"
      by (rule has_sum_cong) (use rhs_eq_cfix in simp)
    thus ?thesis
      using rhs_hs by simp
  qed
  have "H = h + N"
    using has_sum_unique[OF Hhs rhs_cfix_hs] .
  thus "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      = h + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
    by (simp add: H_def N_def)
qed

corollary cfix_right_inverse_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "majle t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
    ((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      - (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
      = h"
proof (intro allI impI)
  fix h :: 'a
  assume h: "dist h (0::'a) < \<sigma>"
  have fp: "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      = h + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
  proof -
    have allfp: "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
      (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        = h + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial
              (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
                ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
      unfolding n_def
      by (rule cfix_functional_fixed_point_at_scale[OF t0 majb low s0])
         (use s1 s2 in \<open>simp_all add: n_def\<close>)
    show ?thesis
      using allfp h by simp
  qed
  define P where "P = (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
  have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) - P = (h + P) - P"
    using fp by (simp add: P_def)
  also have "\<dots> = h"
    by simp
  finally show "((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      - (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
      = h"
    by (simp add: P_def)
qed

lemma normalized_analytic_perturbation_coefficients:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and zero_U: "0 \<in> U"
    and f0: "f 0 = 0"
    and der0: "(f has_derivative id) (at 0)"
  obtains r t bphi M where
    "0 < r" "0 < t"
    "\<And>x. dist x (0::'a) < r \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R bphi \<alpha>) has_sum (x - f x))
        (ra_idx::('a \<Rightarrow> nat) set)"
    "majle t (\<lambda>\<alpha>. norm (bphi \<alpha>)) M"
    "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> < 2 \<Longrightarrow> bphi \<alpha> = 0"
proof -
  from ana zero_U obtain r c where r0: "0 < r"
    and fser: "\<And>x. dist x (0::'a) < r \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (x - 0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x)
        (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding real_analytic_on_def by blast
  define bphi where "bphi = (\<lambda>\<alpha>. cId \<alpha> - c \<alpha>)"
  have phiser: "((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R bphi \<alpha>) has_sum (x - f x))
      (ra_idx::('a \<Rightarrow> nat) set)"
    if x: "dist x (0::'a) < r" for x
  proof -
    have idser: "((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R cId \<alpha>) has_sum x)
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule cId_series)
    have fserx: "((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R c \<alpha>) has_sum f x)
        (ra_idx::('a \<Rightarrow> nat) set)"
      using fser[OF x] by simp
    have neg_fser: "((\<lambda>\<alpha>. - (ra_monomial x \<alpha> *\<^sub>R c \<alpha>)) has_sum (- f x))
        (ra_idx::('a \<Rightarrow> nat) set)"
      using fserx by (simp add: has_sum_uminus)
    have "((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R cId \<alpha>
          + (- (ra_monomial x \<alpha> *\<^sub>R c \<alpha>))) has_sum (x + (- f x)))
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule has_sum_add[OF idser neg_fser])
    thus ?thesis
      by (simp add: bphi_def scaleR_diff_right)
  qed

  have c0: "c czero_idx = 0"
  proof -
    have hs: "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R c \<alpha>) has_sum f 0)
        (ra_idx::('a \<Rightarrow> nat) set)"
      using fser[of 0] r0 by simp
    show ?thesis
      using ra_series_at_zero_coeff[OF hs] f0 by simp
  qed
  have fd_id: "frechet_derivative f (at 0) = id"
    using frechet_derivative_at[OF der0] by simp
  have low: "bphi \<alpha> = 0" if a: "\<alpha> \<in> ra_idx" and lt: "ra_deg \<alpha> < 2" for \<alpha>
  proof (cases "ra_deg \<alpha> = 0")
    case True
    hence "\<alpha> = czero_idx"
      using ra_deg_eq0_iff[OF a] by simp
    thus ?thesis
      by (simp add: bphi_def c0 cId_czero)
  next
    case False
    hence d1: "ra_deg \<alpha> = 1"
      using lt by simp
    obtain b where b: "b \<in> Basis" and alpha: "\<alpha> = unit_idx b"
      by (rule ra_deg_one_unit[OF a d1])
    have c_lin: "c (unit_idx b) = b"
    proof -
      have "c (\<lambda>x. if x = b then 1 else 0) = frechet_derivative f (at 0) b"
        by (rule ra_linear_coeff_eq_frechet_derivative_basis[OF b r0 fser])
      thus ?thesis
        by (simp add: unit_idx_def fd_id)
    qed
    show ?thesis
      using b by (simp add: bphi_def alpha c_lin cId_unit)
  qed

  define eB where "eB = (\<Sum>b\<in>(Basis::'a set). b)"
  have eBpos: "0 < norm eB"
  proof -
    have "eB \<noteq> 0"
    proof
      assume "eB = 0"
      then have zero_inner: "eB \<bullet> (SOME b. b \<in> (Basis::'a set)) = 0"
        by simp
      obtain b0 :: 'a where b0: "b0 \<in> Basis"
        using nonempty_Basis by blast
      have someB: "(SOME b. b \<in> (Basis::'a set)) \<in> Basis"
        using b0 by (rule someI)
      hence "eB \<bullet> (SOME b. b \<in> (Basis::'a set)) = 1"
        by (simp add: eB_def inner_sum_left inner_Basis)
      thus False
        using zero_inner by simp
    qed
    thus ?thesis by simp
  qed
  define \<rho> where "\<rho> = r / (2 * norm eB)"
  have \<rho>0: "0 < \<rho>"
    using r0 eBpos by (simp add: \<rho>_def)
  have corner: "\<rho> * norm (\<Sum>b\<in>(Basis::'a set). b) < r"
  proof -
    have "\<rho> * norm eB = r / 2"
      using eBpos by (simp add: \<rho>_def)
    also have "\<dots> < r"
      using r0 by simp
    finally show ?thesis
      by (simp add: eB_def)
  qed
  have phiser0: "\<And>z. dist z (0::'a) < r \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (z - 0) \<alpha> *\<^sub>R bphi \<alpha>) has_sum (z - f z))
        (ra_idx::('a \<Rightarrow> nat) set)"
    using phiser by simp
  obtain M0 where M0nn: "M0 \<ge> 0"
    and bnd: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> norm (bphi \<alpha>) \<le> M0 / \<rho> ^ ra_deg \<alpha>"
    using ra_coeff_bound[OF r0 phiser0 \<rho>0 corner] by blast
  define t where "t = \<rho> / 2"
  have t0: "0 < t"
    using \<rho>0 by (simp add: t_def)
  have t_lt: "t < \<rho>"
    using \<rho>0 by (simp add: t_def)
  define M where "M = M0 * (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a \<Rightarrow> nat) set). (t / \<rho>) ^ ra_deg \<alpha>)"
  have maj: "majle t (\<lambda>\<alpha>. norm (bphi \<alpha>)) M"
    unfolding M_def
    by (rule coeff_majle_of_bound[OF M0nn bnd \<rho>0])
       (use t0 t_lt in simp_all)

  show ?thesis
    by (rule that[OF r0 t0 phiser maj low])
qed

theorem normalized_analytic_formal_right_inverse:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and zero_U: "0 \<in> U"
    and f0: "f 0 = 0"
    and der0: "(f has_derivative id) (at 0)"
  obtains \<sigma> bphi where
    "0 < \<sigma>"
    "real_analytic_on
      (\<lambda>h::'a. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      (ball (0::'a) (\<sigma> / 2))"
    "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
    "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
      f (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) = h"
proof -
  show ?thesis
  proof (rule normalized_analytic_perturbation_coefficients[OF ana zero_U f0 der0])
    fix r t bphi M
    assume r0: "0 < r" and t0: "0 < t"
      and phiser: "\<And>x. dist x (0::'a) < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R bphi \<alpha>) has_sum (x - f x))
          (ra_idx::('a \<Rightarrow> nat) set)"
      and majb: "majle t (\<lambda>\<alpha>. norm (bphi \<alpha>)) M"
      and low: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> < 2 \<Longrightarrow> bphi \<alpha> = 0"
  define n where "n = real (card (Basis :: 'a set))"
  have n1: "1 \<le> n"
    unfolding n_def by simp
  have M0: "0 \<le> M"
  proof -
    have "0 \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. mfam t (\<lambda>\<alpha>. norm (bphi \<alpha>)) \<alpha>)"
      using t0 by (intro infsum_nonneg) (simp add: mfam_nonneg)
    also have "\<dots> \<le> M"
      using majb by (simp add: majle_def)
    finally show ?thesis .
  qed
  define a where "a = t / (4 * n)"
  define b where "b = t\<^sup>2 / (8 * (M + 1) * n)"
  define c where "c = r / (4 * n)"
  define \<sigma> where "\<sigma> = min (min a b) c / 2"
  have a0: "0 < a"
    using t0 n1 by (simp add: a_def)
  have b0: "0 < b"
    unfolding b_def
    using t0 M0 n1 by (intro divide_pos_pos mult_pos_pos) simp_all
  have c0: "0 < c"
    using r0 n1 by (simp add: c_def)
  have min0: "0 < min (min a b) c"
    using a0 b0 c0 by simp
  have \<sigma>0: "0 < \<sigma>"
    using min0 by (simp add: \<sigma>_def)
  have half_min_le: "min (min a b) c / 2 \<le> min (min a b) c"
  proof -
    have "min (min a b) c / 2 = (1/2) * min (min a b) c"
      by simp
    also have "\<dots> \<le> 1 * min (min a b) c"
      by (rule mult_right_mono) (use min0 in simp_all)
    finally show ?thesis by simp
  qed
  have s1: "\<sigma> \<le> t / (4 * n)"
  proof -
    have "\<sigma> \<le> min (min a b) c"
      unfolding \<sigma>_def by (rule half_min_le)
    also have "\<dots> \<le> a"
      by simp
    finally show ?thesis
      by (simp add: a_def)
  qed
  have s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  proof -
    have "\<sigma> \<le> min (min a b) c"
      unfolding \<sigma>_def by (rule half_min_le)
    also have "\<dots> \<le> b"
      by simp
    finally show ?thesis
      by (simp add: b_def)
  qed
  have s3: "2 * n * \<sigma> < r"
  proof -
    have "\<sigma> \<le> c / 2"
    proof -
      have "min (min a b) c \<le> c"
        by simp
      hence "min (min a b) c / 2 \<le> c / 2"
        by simp
      thus ?thesis
        by (simp add: \<sigma>_def)
    qed
    hence "2 * n * \<sigma> \<le> 2 * n * (c / 2)"
      using n1 by (intro mult_left_mono) simp_all
    also have "\<dots> = r / 4"
      using n1 by (simp add: c_def field_simps)
    also have "\<dots> < r"
      using r0 by simp
    finally show ?thesis .
  qed
  have Hana: "real_analytic_on
      (\<lambda>h::'a. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
      (ball (0::'a) (\<sigma> / 2))"
    unfolding n_def
    by (rule cfix_power_series_real_analytic_on_ball_at_scale[OF t0 majb \<sigma>0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  show ?thesis
  proof (rule that[OF \<sigma>0 Hana])
    fix h :: 'a
    assume h: "norm h < \<sigma>"
    show "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
      unfolding n_def
      by (rule cfix_power_series_has_sum[OF t0 majb \<sigma>0])
         (use h s1 s2 in \<open>simp_all add: n_def\<close>)
  next
    fix h :: 'a
    assume h: "norm h < \<sigma>"
    let ?H = "\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>"
    let ?P = "\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial ?H \<beta> *\<^sub>R bphi \<beta>"
    have hle: "norm h \<le> \<sigma>"
      using h by simp
    have Hle: "norm ?H \<le> 2 * n * \<sigma>"
      unfolding n_def
      by (rule cfix_value_norm_bound_at_scale[OF t0 majb \<sigma>0])
         (use s1 s2 hle in \<open>simp_all add: n_def\<close>)
    have Hr: "dist ?H (0::'a) < r"
      using Hle s3 by (simp add: dist_norm)
    have phi_hs: "((\<lambda>\<beta>. ra_monomial ?H \<beta> *\<^sub>R bphi \<beta>) has_sum (?H - f ?H))
        (ra_idx::('a \<Rightarrow> nat) set)"
      using phiser[OF Hr] by simp
    have phi_sum: "((\<lambda>\<beta>. ra_monomial ?H \<beta> *\<^sub>R bphi \<beta>) has_sum ?P)
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule has_sum_infsum) (rule has_sum_imp_summable[OF phi_hs])
    have Peq: "?P = ?H - f ?H"
      by (rule has_sum_unique[OF phi_sum phi_hs])
    have right: "?H - ?P = h"
    proof -
      have all_right: "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
        ((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>)
          - (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial
                (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
                  ra_monomial h \<gamma> *\<^sub>R cfix bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
          = h"
        unfolding n_def
        by (rule cfix_right_inverse_at_scale[OF t0 majb low \<sigma>0])
           (use s1 s2 in \<open>simp_all add: n_def\<close>)
      show ?thesis
        using all_right h by (simp add: dist_norm)
    qed
    show "f ?H = h"
      using right Peq by simp
  qed
  qed
qed

end
