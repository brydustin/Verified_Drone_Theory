section \<open>The array factor and the radiation pattern\<close>

theory Array_Factor
  imports
    "HOL-Analysis.Analysis"
begin

text \<open>A configuration is a family \<open>x :: planar^'n\<close> of positions in the plane; an angle is the pair of polar angle and azimuth.\<close>

type_synonym planar = "real^2"

type_synonym angle = "real^2"   (* (theta, phi) as a 2-vector *)

subsection \<open>Real spans of unit complex numbers\<close>

lemma complex_real_span_2:
  fixes a b w :: complex
  assumes hindep: "Im (cnj a * b) \<noteq> 0"
  shows "\<exists>r s::real. w = of_real r * a + of_real s * b"
proof -
  define D where "D = Re a * Im b - Im a * Re b"
  have hD: "D \<noteq> 0"
    using hindep by (simp add: D_def)
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

subsection \<open>Definitions\<close>

text \<open>The array factor of the configuration \<open>x\<close> for the wavevector map \<open>cvec\<close>, and the pattern with the gain \<open>g\<close>.\<close>

definition A_cart :: "(angle \<Rightarrow> planar) \<Rightarrow> planar^'n \<Rightarrow> angle \<Rightarrow> complex" where
  "A_cart cvec x \<omega> = (\<Sum>n\<in>UNIV. cis (- (cvec \<omega> \<bullet> (x $ n))))"

definition U_cart :: "(angle \<Rightarrow> planar) \<Rightarrow> (angle \<Rightarrow> real) \<Rightarrow> planar^'n \<Rightarrow> angle \<Rightarrow> real" where
  "U_cart cvec g x \<omega> = g \<omega> * (cmod (A_cart cvec x \<omega>))\<^sup>2"

subsection \<open>For an odd number of relays the phases at a zero of the array factor are not collinear\<close>

lemma sum_collinear_units_card:
  fixes z :: "'i \<Rightarrow> complex" and u :: complex
  assumes "finite I" and "u \<noteq> 0"
    and "\<And>i. i \<in> I \<Longrightarrow> \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> z i = of_int \<epsilon> * u"
  shows "\<exists>m::int. (\<Sum>i\<in>I. z i) = of_int m * u \<and> odd m = odd (card I)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  show ?case by (intro exI[of _ 0]) simp
next
  case (insert a I)
  obtain \<epsilon> :: int where h\<epsilon>: "\<epsilon> \<in> {-1, 1}" "z a = of_int \<epsilon> * u"
    using insert.prems(2)[of a] by auto
  have hrest: "\<And>i. i \<in> I \<Longrightarrow> \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> z i = of_int \<epsilon> * u"
    using insert.prems(2) by simp
  obtain m :: int where hm: "(\<Sum>i\<in>I. z i) = of_int m * u" "odd m = odd (card I)"
    using insert.IH[OF insert.prems(1) hrest] by blast
  have "(\<Sum>i\<in>insert a I. z i) = of_int (\<epsilon> + m) * u"
    using insert.hyps h\<epsilon> hm by (simp add: ring_distribs)
  moreover have "odd (\<epsilon> + m) = odd (card (insert a I))"
    using insert.hyps h\<epsilon> hm by (auto simp:)
  ultimately show ?case by blast
qed

theorem A_cart_zero_odd_not_collinear:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes "odd CARD('n)" and "A_cart cvec x \<omega> = 0"
  shows "\<not> (\<exists>u. u \<noteq> 0 \<and>
              (\<forall>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (- (cvec \<omega> \<bullet> (x $ n))) = of_int \<epsilon> * u))"
proof
  assume "\<exists>u. u \<noteq> 0 \<and>
            (\<forall>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (- (cvec \<omega> \<bullet> (x $ n))) = of_int \<epsilon> * u)"
  then obtain u where hu: "u \<noteq> 0"
    and hcol: "\<And>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (- (cvec \<omega> \<bullet> (x $ n))) = of_int \<epsilon> * u"
    by blast
  have hfin: "finite (UNIV :: 'n set)" by simp
  obtain m :: int where hm:
      "(\<Sum>n\<in>(UNIV::'n set). cis (- (cvec \<omega> \<bullet> (x $ n)))) = of_int m * u"
      "odd m = odd (card (UNIV::'n set))"
    using sum_collinear_units_card[OF hfin hu, of "\<lambda>n. cis (- (cvec \<omega> \<bullet> (x $ n)))"] hcol
    by blast
  have "odd m" using hm(2) assms(1) by simp
  then have "m \<noteq> 0" by presburger
  with hm(1) hu have "(\<Sum>n\<in>(UNIV::'n set). cis (- (cvec \<omega> \<bullet> (x $ n)))) \<noteq> 0"
    by simp
  then show False
    using assms(2) by (simp add: A_cart_def)
qed

corollary A_cart_zero_odd_indep_pair:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes "odd CARD('n)" and "A_cart cvec x \<omega> = 0"
  shows "\<exists>i j. Im (cnj (cis (- (cvec \<omega> \<bullet> (x $ i)))) * cis (- (cvec \<omega> \<bullet> (x $ j)))) \<noteq> 0"
proof -
  have units: "\<And>n. cmod (cis (- (cvec \<omega> \<bullet> (x $ n)))) = 1"
    by simp
  have notcol:
    "\<not> (\<exists>u. u \<noteq> 0 \<and>
          (\<forall>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (- (cvec \<omega> \<bullet> (x $ n))) = of_int \<epsilon> * u))"
    by (rule A_cart_zero_odd_not_collinear[OF assms])
  show ?thesis
    by (rule not_collinear_imp_indep_pair[OF units notcol])
qed

subsection \<open>The derivative of the array factor in the configuration is onto at a zero\<close>

definition dxA ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2)^'n \<Rightarrow> real^2 \<Rightarrow> (real^2)^'n \<Rightarrow> complex" where
  "dxA cvec x \<omega> h =
     - \<i> * (\<Sum>n\<in>UNIV. of_real (cvec \<omega> \<bullet> (h $ n)) * cis (- (cvec \<omega> \<bullet> (x $ n))))"

theorem dxA_surj:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n"
    and \<omega> :: "real^2" and w :: complex
  assumes oddN: "odd CARD('n)" and czero: "cvec \<omega> \<noteq> 0" and Azero: "A_cart cvec x \<omega> = 0"
  shows "\<exists>h. dxA cvec x \<omega> h = w"
proof -
  obtain i j where hij:
      "Im (cnj (cis (- (cvec \<omega> \<bullet> (x $ i)))) * cis (- (cvec \<omega> \<bullet> (x $ j)))) \<noteq> 0"
    using A_cart_zero_odd_indep_pair[OF oddN Azero] by blast
  have hzz: "\<And>b. Im (cnj (cis b) * cis b) = 0" by simp
  have hne: "i \<noteq> j"
  proof
    assume "i = j"
    then have "Im (cnj (cis (- (cvec \<omega> \<bullet> (x $ i)))) * cis (- (cvec \<omega> \<bullet> (x $ j)))) = 0"
      using hzz by simp
    with hij show False by simp
  qed
  obtain r s :: real where hrs:
      "\<i> * w = of_real r * cis (- (cvec \<omega> \<bullet> (x $ i)))
               + of_real s * cis (- (cvec \<omega> \<bullet> (x $ j)))"
    using complex_real_span_2[OF hij] by blast
  have hcc: "cvec \<omega> \<bullet> cvec \<omega> \<noteq> 0"
    using czero by (simp add:)
  define d :: "real^2" where "d = (1 / (cvec \<omega> \<bullet> cvec \<omega>)) *\<^sub>R cvec \<omega>"
  have hd: "cvec \<omega> \<bullet> d = 1"
    using hcc by (simp add: d_def)
  define h :: "(real^2)^'n" where
    "h = (\<chi> n. if n = i then r *\<^sub>R d else if n = j then s *\<^sub>R d else 0)"
  define g :: "'n \<Rightarrow> complex" where
    "g = (\<lambda>n. of_real (cvec \<omega> \<bullet> (h $ n)) * cis (- (cvec \<omega> \<bullet> (x $ n))))"
  have van: "\<And>n. n \<notin> {i, j} \<Longrightarrow> g n = 0"
    by (simp add: g_def h_def)
  have gi: "g i = of_real r * cis (- (cvec \<omega> \<bullet> (x $ i)))"
    by (simp add: g_def h_def hd)
  have gj: "g j = of_real s * cis (- (cvec \<omega> \<bullet> (x $ j)))"
    using hne by (simp add: g_def h_def hd)
  have "(\<Sum>n\<in>(UNIV::'n set). g n) = (\<Sum>n\<in>{i, j}. g n)"
  proof (rule sum.mono_neutral_right)
    show "finite (UNIV :: 'n set)" by simp
    show "{i, j} \<subseteq> UNIV" by simp
    show "\<forall>n\<in>UNIV - {i, j}. g n = 0" using van by simp
  qed
  also have "\<dots> = g i + g j" using hne by simp
  also have "\<dots> = \<i> * w" using gi gj hrs by simp
  finally have hsum: "(\<Sum>n\<in>(UNIV::'n set). g n) = \<i> * w" .
  have hsum': "(\<Sum>n\<in>(UNIV::'n set).
                 of_real (cvec \<omega> \<bullet> (h $ n)) * cis (- (cvec \<omega> \<bullet> (x $ n)))) = \<i> * w"
    using hsum by (simp add: g_def)
  have hval: "dxA cvec x \<omega> h = - \<i> * (\<i> * w)"
    by (simp add: dxA_def hsum')
  have "- \<i> * (\<i> * w) = w" by (simp add: complex_eq_iff)
  with hval have "dxA cvec x \<omega> h = w" by simp
  then show ?thesis by blast
qed

end
