theory Nonemptiness_Array_Factor
  imports "HOL-Analysis.Analysis"
begin

section \<open>The Array Factor and Power Pattern\<close>

text \<open>
  This theory develops the concrete radiation-pattern functions from
  \<open>Applied Math/nonemptiness_unified_singlefile_complete.tex\<close> and the elementary
  odd-\<open>N\<close> geometry that makes the whole nonemptiness argument work.

  No locales are used: every object is a plain definition, and every lemma is a
  genuine statement about those definitions. The mathematical heart recorded here
  is Lemma \<open>lem:Azero-surj\<close>: writing \<open>z\<^sub>n = e\<^sup>-\<^sup>i\<^sup>c\<^sup>\<cdot>\<^sup>p\<^sup>n\<close> (each of unit modulus), if the
  array factor vanishes and \<open>N\<close> is odd then the \<open>z\<^sub>n\<close> cannot all be real-collinear,
  because a real-collinear family would give \<open>z\<^sub>n = \<epsilon>\<^sub>n e\<^sup>i\<^sup>\<xi>\<close> with \<open>\<epsilon>\<^sub>n = \<plusminus>1\<close> and then
  \<open>\<Sum> \<epsilon>\<^sub>n = 0\<close>, impossible for an odd number of \<open>\<plusminus>1\<close>s.
\<close>

type_synonym planar_point = "real^2"
type_synonym angle_point = "real^2"
type_synonym raw_configuration = "planar_point list"

definition array_factor ::
  "(angle_point \<Rightarrow> planar_point) \<Rightarrow> raw_configuration \<Rightarrow> angle_point \<Rightarrow> complex"
where
  "array_factor cvec ps \<omega> =
     sum_list (map (\<lambda>p. cis (-(cvec \<omega> \<bullet> p))) ps)"

definition power_pattern ::
  "(angle_point \<Rightarrow> planar_point) \<Rightarrow> (angle_point \<Rightarrow> real) \<Rightarrow>
  raw_configuration \<Rightarrow> angle_point \<Rightarrow> real"
where
  "power_pattern cvec g ps \<omega> =
     g \<omega> * (cmod (array_factor cvec ps \<omega>))\<^sup>2"


subsection \<open>Elementary algebra of the array factor\<close>

lemma array_factor_Nil [simp]:
  "array_factor cvec [] \<omega> = 0"
  by (simp add: array_factor_def)

lemma array_factor_Cons:
  "array_factor cvec (p # ps) \<omega> =
     cis (-(cvec \<omega> \<bullet> p)) + array_factor cvec ps \<omega>"
  by (simp add: array_factor_def)

lemma array_factor_append:
  "array_factor cvec (ps @ qs) \<omega> =
     array_factor cvec ps \<omega> + array_factor cvec qs \<omega>"
  by (simp add: array_factor_def)

lemma cmod_array_factor_le:
  "cmod (array_factor cvec ps \<omega>) \<le> real (length ps)"
proof (induction ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  have "cmod (array_factor cvec (p # ps) \<omega>)
          = cmod (cis (-(cvec \<omega> \<bullet> p)) + array_factor cvec ps \<omega>)"
    by (simp add: array_factor_Cons)
  also have "\<dots> \<le> cmod (cis (-(cvec \<omega> \<bullet> p))) + cmod (array_factor cvec ps \<omega>)"
    by (rule norm_triangle_ineq)
  also have "\<dots> = 1 + cmod (array_factor cvec ps \<omega>)"
    by (simp add: norm_cis)
  also have "\<dots> \<le> 1 + real (length ps)"
    using Cons.IH by simp
  finally show ?case by simp
qed

lemma power_pattern_nonneg:
  assumes "0 \<le> g \<omega>"
  shows "0 \<le> power_pattern cvec g ps \<omega>"
  using assms by (simp add: power_pattern_def)


section \<open>Odd-\<open>N\<close> Geometry of the Zeros\<close>

text \<open>
  The combinatorial nucleus: a sum of an odd number of \<open>\<plusminus>1\<close>s is odd, hence nonzero.
\<close>

lemma sum_pm_one_parity:
  fixes \<epsilon> :: "nat \<Rightarrow> int"
  assumes "\<And>n. n < N \<Longrightarrow> \<epsilon> n \<in> {-1, 1}"
  shows "odd (\<Sum>n<N. \<epsilon> n) = odd N"
  using assms
proof (induction N)
  case 0
  show ?case by simp
next
  case (Suc N)
  have hIH: "odd (\<Sum>n<N. \<epsilon> n) = odd N"
    using Suc.IH Suc.prems by simp
  have h\<epsilon>: "odd (\<epsilon> N)"
    using Suc.prems[of N] by auto
  have "(\<Sum>n<Suc N. \<epsilon> n) = (\<Sum>n<N. \<epsilon> n) + \<epsilon> N"
    by simp
  then show ?case
    using hIH h\<epsilon> by (simp add: even_add)
qed

lemma sum_pm_one_odd_nonzero:
  fixes \<epsilon> :: "nat \<Rightarrow> int"
  assumes "odd N" and "\<And>n. n < N \<Longrightarrow> \<epsilon> n \<in> {-1, 1}"
  shows "(\<Sum>n<N. \<epsilon> n) \<noteq> 0"
proof -
  have "odd (\<Sum>n<N. \<epsilon> n)"
    using sum_pm_one_parity[OF assms(2)] assms(1) by simp
  then show ?thesis by force
qed

text \<open>
  A real-collinear family of unit-modulus terms sums to an integer multiple of the
  common direction, with that integer's parity equal to the number of terms.
\<close>

lemma sum_list_collinear_units:
  fixes ps :: "'a list" and f :: "'a \<Rightarrow> complex" and u :: complex
  assumes "u \<noteq> 0"
    and "\<And>p. p \<in> set ps \<Longrightarrow> \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> f p = of_int \<epsilon> * u"
  shows "\<exists>m::int. sum_list (map f ps) = of_int m * u \<and> odd m = odd (length ps)"
  using assms
proof (induction ps)
  case Nil
  show ?case by (intro exI[of _ 0]) simp
next
  case (Cons p ps)
  obtain \<epsilon> :: int where h\<epsilon>: "\<epsilon> \<in> {-1, 1}" "f p = of_int \<epsilon> * u"
    using Cons.prems(2)[of p] by auto
  obtain m :: int where hm: "sum_list (map f ps) = of_int m * u" "odd m = odd (length ps)"
    using Cons.IH Cons.prems by auto
  have "sum_list (map f (p # ps)) = of_int (\<epsilon> + m) * u"
    using h\<epsilon> hm by (simp add: of_int_add ring_distribs)
  moreover have "odd (\<epsilon> + m) = odd (length (p # ps))"
    using h\<epsilon> hm by (auto simp: even_add)
  ultimately show ?case by blast
qed

lemma sum_list_collinear_units_odd_nonzero:
  fixes ps :: "'a list" and f :: "'a \<Rightarrow> complex" and u :: complex
  assumes "odd (length ps)" and "u \<noteq> 0"
    and "\<And>p. p \<in> set ps \<Longrightarrow> \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> f p = of_int \<epsilon> * u"
  shows "sum_list (map f ps) \<noteq> 0"
proof -
  have "\<exists>m::int. sum_list (map f ps) = of_int m * u \<and> odd m = odd (length ps)"
    by (rule sum_list_collinear_units[OF assms(2)]) (use assms(3) in blast)
  then obtain m :: int where hm:
      "sum_list (map f ps) = of_int m * u" "odd m = odd (length ps)"
    by blast
  from hm assms(1) have "m \<noteq> 0" by auto
  with hm assms(2) show ?thesis by simp
qed

text \<open>
  Lemma \<open>lem:Azero-surj\<close> (geometric core). When \<open>N\<close> is odd and the array factor
  vanishes, the unit-modulus summands \<open>cis(-(cvec \<omega> \<cdot> p))\<close> cannot all lie on a common
  real line through the origin. Equivalently, their real span is two-dimensional, so
  the partial differential \<open>D\<^sub>x A\<close> (which equals \<open>-\<i>\<close> times that span) is onto \<open>\<complex>\<close>.
\<close>

theorem array_factor_zero_odd_not_collinear:
  assumes "odd (length ps)"
    and "array_factor cvec ps \<omega> = 0"
  shows "\<not> (\<exists>u. u \<noteq> 0 \<and>
              (\<forall>p\<in>set ps. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (-(cvec \<omega> \<bullet> p)) = of_int \<epsilon> * u))"
proof
  assume "\<exists>u. u \<noteq> 0 \<and>
            (\<forall>p\<in>set ps. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (-(cvec \<omega> \<bullet> p)) = of_int \<epsilon> * u)"
  then obtain u where hu: "u \<noteq> 0"
    and hcol: "\<And>p. p \<in> set ps \<Longrightarrow>
                 \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (-(cvec \<omega> \<bullet> p)) = of_int \<epsilon> * u"
    by blast
  have "sum_list (map (\<lambda>p. cis (-(cvec \<omega> \<bullet> p))) ps) \<noteq> 0"
    by (rule sum_list_collinear_units_odd_nonzero[OF assms(1) hu]) (use hcol in blast)
  then show False
    using assms(2) by (simp add: array_factor_def)
qed


section \<open>Real Spans in the Complex Plane\<close>

text \<open>
  The linear-algebra counterpart of the surjectivity half of \<open>lem:Azero-surj\<close>:
  two complex numbers that are \<^emph>\<open>real\<close>-linearly independent span \<open>\<complex>\<close> over \<open>\<real>\<close>.
  Real independence of \<open>a\<close>, \<open>b\<close> is exactly nonvanishing of the \<open>2 \<times> 2\<close> real
  determinant \<open>Re a \<cdot> Im b - Im a \<cdot> Re b = Im (cnj a \<cdot> b)\<close>, and the spanning
  coefficients are recovered by Cramer's rule.
\<close>

lemma Im_cnj_mult: "Im (cnj a * b) = Re a * Im b - Im a * Re b"
  by simp

lemma complex_real_span_2:
  fixes a b w :: complex
  assumes hindep: "Im (cnj a * b) \<noteq> 0"
  shows "\<exists>r s::real. w = of_real r * a + of_real s * b"
proof -
  define D where "D = Re a * Im b - Im a * Re b"
  have hD: "D \<noteq> 0"
    using hindep by (simp add: Im_cnj_mult D_def)
  define r where "r = (Re w * Im b - Im w * Re b) / D"
  define s where "s = (Re a * Im w - Im a * Re w) / D"
  have rD: "r * D = Re w * Im b - Im w * Re b"
    unfolding r_def using hD by (simp add: field_simps)
  have sD: "s * D = Re a * Im w - Im a * Re w"
    unfolding s_def using hD by (simp add: field_simps)
  have Re_eq: "r * Re a + s * Re b = Re w"
  proof -
    have "(r * Re a + s * Re b) * D = (r * D) * Re a + (s * D) * Re b"
      by (simp add: algebra_simps)
    also have "\<dots> = (Re w * Im b - Im w * Re b) * Re a + (Re a * Im w - Im a * Re w) * Re b"
      by (simp only: rD sD)
    also have "\<dots> = Re w * D"
      unfolding D_def by (simp add: algebra_simps)
    finally have "(r * Re a + s * Re b) * D = Re w * D" .
    then show ?thesis using hD by (metis mult_right_cancel)
  qed
  have Im_eq: "r * Im a + s * Im b = Im w"
  proof -
    have "(r * Im a + s * Im b) * D = (r * D) * Im a + (s * D) * Im b"
      by (simp add: algebra_simps)
    also have "\<dots> = (Re w * Im b - Im w * Re b) * Im a + (Re a * Im w - Im a * Re w) * Im b"
      by (simp only: rD sD)
    also have "\<dots> = Im w * D"
      unfolding D_def by (simp add: algebra_simps)
    finally have "(r * Im a + s * Im b) * D = Im w * D" .
    then show ?thesis using hD by (metis mult_right_cancel)
  qed
  have "of_real r * a + of_real s * b = w"
    by (rule complex_eqI) (use Re_eq Im_eq in simp)+
  then show ?thesis by blast
qed

text \<open>
  Consequently a real-collinearity failure for unit-modulus terms upgrades to genuine
  spanning: if two of the summands are real-independent, every complex value is a real
  combination of them --- the statement that \<open>D\<^sub>x A\<close> is onto \<open>\<complex>\<close>.
\<close>

corollary indep_pair_spans_complex:
  fixes z :: "'i \<Rightarrow> complex"
  assumes "Im (cnj (z i) * z j) \<noteq> 0"
  shows "\<forall>w. \<exists>r s::real. w = of_real r * z i + of_real s * z j"
  using complex_real_span_2[OF assms] by blast


text \<open>
  The reverse direction: two unit-modulus numbers whose \<open>2 \<times> 2\<close> determinant
  \<open>Im (cnj a \<cdot> b)\<close> vanishes are real-collinear, in fact equal up to sign. (If
  \<open>cnj a \<cdot> b\<close> is real with modulus \<open>1\<close>, it is \<open>\<plusminus>1\<close>, and multiplying back by \<open>a\<close>
  gives \<open>b = \<plusminus>a\<close>.)
\<close>

lemma unit_mult_real_imp_pm:
  fixes a b :: complex
  assumes "cmod a = 1" and "cmod b = 1" and "Im (cnj a * b) = 0"
  shows "b = a \<or> b = - a"
proof -
  define w where "w = cnj a * b"
  have hw1: "cmod w = 1"
    using assms(1,2) by (simp add: w_def norm_mult)
  have hwIm: "Im w = 0"
    using assms(3) by (simp add: w_def)
  have "cmod w = \<bar>Re w\<bar>"
    using hwIm by (simp add: norm_complex_def real_sqrt_abs)
  with hw1 have "\<bar>Re w\<bar> = 1" by simp
  then have hRe: "Re w = 1 \<or> Re w = -1" by auto
  have hw: "w = 1 \<or> w = -1"
    using hRe hwIm by (auto simp: complex_eq_iff)
  have hcnj: "cnj a * a = 1"
  proof -
    have "cnj a * a = of_real ((Re a)\<^sup>2 + (Im a)\<^sup>2)"
      by (simp add: complex_eq_iff power2_eq_square)
    also have "(Re a)\<^sup>2 + (Im a)\<^sup>2 = (cmod a)\<^sup>2"
      by (simp add: cmod_power2)
    finally show ?thesis using assms(1) by simp
  qed
  have wab: "w * a = b"
    using hcnj unfolding w_def
    by (metis (no_types, lifting) mult.assoc mult.commute mult.left_neutral)
  show "b = a \<or> b = - a"
    using hw wab by auto
qed

text \<open>
  Hence if every pair of a family of unit-modulus terms has vanishing determinant,
  the whole family lies on one real line (all \<open>\<plusminus>\<close> a single direction).
\<close>

lemma unit_pairwise_real_imp_collinear:
  fixes z :: "'i \<Rightarrow> complex" and i0 :: 'i
  assumes units: "\<And>n. cmod (z n) = 1"
    and pair: "\<And>i j. Im (cnj (z i) * z j) = 0"
  shows "\<exists>u. u \<noteq> 0 \<and> (\<forall>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> z n = of_int \<epsilon> * u)"
proof (intro exI[of _ "z i0"] conjI)
  show "z i0 \<noteq> 0" using units[of i0] by auto
  show "\<forall>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> z n = of_int \<epsilon> * z i0"
  proof
    fix n
    have "z n = z i0 \<or> z n = - z i0"
      using unit_mult_real_imp_pm[OF units[of i0] units[of n] pair] by blast
    then show "\<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> z n = of_int \<epsilon> * z i0"
      by (auto intro: exI[of _ "1::int"] exI[of _ "-1::int"])
  qed
qed

text \<open>
  The contrapositive used in \<open>lem:Azero-surj\<close>: a unit-modulus family that is \<^emph>\<open>not\<close>
  real-collinear has two real-independent members, whose real span is therefore all
  of \<open>\<complex>\<close> by @{thm [source] complex_real_span_2}.
\<close>


lemma not_collinear_imp_indep_pair:
  fixes z :: "'i \<Rightarrow> complex"
  assumes units: "\<And>n. cmod (z n) = 1"
    and notcol: "\<not> (\<exists>u. u \<noteq> 0 \<and> (\<forall>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> z n = of_int \<epsilon> * u))"
  shows "\<exists>i j. Im (cnj (z i) * z j) \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>i j. Im (cnj (z i) * z j) \<noteq> 0)"
  then have hpair: "\<And>i j. Im (cnj (z i) * z j) = 0"
    by simp

  from unit_pairwise_real_imp_collinear[OF units hpair]
  obtain u where hu:
    "u \<noteq> 0"
    "\<forall>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> z n = of_int \<epsilon> * u"
    by metis   
  then show False
    using notcol by blast
qed


end
