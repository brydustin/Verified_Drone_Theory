theory Nonemptiness_Spine
  imports
    Nonemptiness_Scaffold
    Nonemptiness_Array_Factor
    Nonemptiness_Feasibility
begin

section \<open>Concrete Configuration Space\<close>

text \<open>
  A configuration is a tuple of \<open>N = CARD('n)\<close> planar element positions,
  \<open>x : (real^2)^'n\<close>, with \<open>N\<close> odd and \<open>N \<ge> 7\<close>. This type is a finite-dimensional
  Euclidean space, hence \<^class>\<open>heine_borel\<close> and \<^class>\<open>real_normed_vector\<close> --- exactly
  the Baire-space setting the closeout in \<^theory>\<open>Applied_Math_Nonemptiness.Nonemptiness_Scaffold\<close>
  needs. The radiation-pattern functions are the concrete \<^const>\<open>array_factor\<close>
  specialized to this fixed-arity configuration type.
\<close>

definition af :: "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2)^'n \<Rightarrow> real^2 \<Rightarrow> complex" where
  "af cvec x \<omega> = (\<Sum>n\<in>UNIV. cis (- (cvec \<omega> \<bullet> (x $ n))))"

definition pw ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real) \<Rightarrow> (real^2)^'n \<Rightarrow> real^2 \<Rightarrow> real" where
  "pw cvec g x \<omega> = g \<omega> * (cmod (af cvec x \<omega>))\<^sup>2"

lemma pw_nonneg:
  assumes "0 \<le> g \<omega>"
  shows "0 \<le> pw cvec g x \<omega>"
  using assms by (simp add: pw_def)


section \<open>Odd-\<open>N\<close> Geometry on the Configuration Space\<close>

text \<open>
  The finite-index counterpart of the array-factor zero geometry from
  \<^theory>\<open>Applied_Math_Nonemptiness.Nonemptiness_Array_Factor\<close>: a real-collinear family
  of unit-modulus terms sums to an integer multiple of the common direction, with that
  integer's parity equal to the number of terms.
\<close>

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

text \<open>
  Lemma \<open>lem:Azero-surj\<close> on the configuration space: when \<open>N\<close> is odd and the array
  factor vanishes, the unit-modulus summands cannot all lie on one real line, so the
  partial differential \<open>D\<^sub>x A\<close> (\<open>= -\<i>\<close> times their real span) is onto \<open>\<complex>\<close>.
\<close>

theorem af_zero_odd_not_collinear:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes "odd CARD('n)" and "af cvec x \<omega> = 0"
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
    using assms(2) by (simp add: af_def)
qed

text \<open>
  Full surjectivity content of \<open>lem:Azero-surj\<close> at the level of the summands:
  when \<open>N\<close> is odd and \<open>A(x,\<omega>) = 0\<close>, two of the terms \<open>cis(-(cvec \<omega> \<cdot> p\<^sub>n))\<close> are
  real-independent, so (by @{thm [source] complex_real_span_2}) their real span is
  all of \<open>\<complex>\<close> --- equivalently the image of \<open>D\<^sub>x A\<close> is two-dimensional.
\<close>

corollary af_zero_odd_indep_pair:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes "odd CARD('n)" and "af cvec x \<omega> = 0"
  shows "\<exists>i j. Im (cnj (cis (- (cvec \<omega> \<bullet> (x $ i)))) * cis (- (cvec \<omega> \<bullet> (x $ j)))) \<noteq> 0"
proof -
  have units: "\<And>n. cmod (cis (- (cvec \<omega> \<bullet> (x $ n)))) = 1"
    by simp
  have notcol:
    "\<not> (\<exists>u. u \<noteq> 0 \<and>
          (\<forall>n. \<exists>\<epsilon>::int. \<epsilon> \<in> {-1, 1} \<and> cis (- (cvec \<omega> \<bullet> (x $ n))) = of_int \<epsilon> * u))"
    by (rule af_zero_odd_not_collinear[OF assms])
  show ?thesis
    by (rule not_collinear_imp_indep_pair[OF units notcol])
qed


subsection \<open>The Partial Differential \<open>D\<^sub>x A\<close> and its Surjectivity\<close>

text \<open>
  The partial differential of the array factor in the configuration variable, in the
  direction \<open>h\<close>, is \<open>D\<^sub>x A(\<delta>x) = -\<i> \<Sum>\<^sub>n (cvec \<omega> \<cdot> \<delta>p\<^sub>n) z\<^sub>n\<close> with \<open>z\<^sub>n = cis(-(cvec \<omega> \<cdot> p\<^sub>n))\<close>
  (differentiate \<open>cis\<close> termwise). We record it directly by this formula.
\<close>

definition dxA ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2)^'n \<Rightarrow> real^2 \<Rightarrow> (real^2)^'n \<Rightarrow> complex" where
  "dxA cvec x \<omega> h =
     - \<i> * (\<Sum>n\<in>UNIV. of_real (cvec \<omega> \<bullet> (h $ n)) * cis (- (cvec \<omega> \<bullet> (x $ n))))"

text \<open>
  Lemma \<open>lem:Azero-surj\<close>, full statement: at an odd-\<open>N\<close> zero of the array factor with
  \<open>cvec \<omega> \<noteq> 0\<close>, the partial differential \<open>D\<^sub>x A\<close> is onto \<open>\<complex>\<close>. The two real-independent
  summands span \<open>\<complex>\<close>, and \<open>cvec \<omega> \<noteq> 0\<close> lets us hit any pair of real coefficients by
  moving the two corresponding elements along the direction \<open>d\<close> with \<open>cvec \<omega> \<cdot> d = 1\<close>.
\<close>

theorem dxA_surj:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n"
    and \<omega> :: "real^2" and w :: complex
  assumes oddN: "odd CARD('n)" and czero: "cvec \<omega> \<noteq> 0" and Azero: "af cvec x \<omega> = 0"
  shows "\<exists>h. dxA cvec x \<omega> h = w"
proof -
  obtain i j where hij:
      "Im (cnj (cis (- (cvec \<omega> \<bullet> (x $ i)))) * cis (- (cvec \<omega> \<bullet> (x $ j)))) \<noteq> 0"
    using af_zero_odd_indep_pair[OF oddN Azero] by blast
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


section \<open>Closeout Lemma (Baire + Meager Branches)\<close>

text \<open>
  This is the Isabelle counterpart of Theorem \<open>thm:final\<close> (odd-\<open>N\<close> nonemptiness),
  assembled over the concrete configuration type. It is \<^emph>\<open>fully proved\<close> (no
  \<^theory_text>\<open>sorry\<close>): it derives nonemptiness of the robust feasible set
  \<open>Fzero Fset X0 = Fset \<inter> X0 \<xi>\<close> from the four meagerness facts and the soundness of
  \<open>X0\<close>, exactly as the paper's closeout does. Those hypotheses are the deep
  branch results of the paper; they are stated here as explicit assumptions, not
  hidden, and remain to be proved for the concrete bad sets (the next modules):

  \<^item> \<open>open V\<close>, \<open>V \<noteq> {}\<close>, \<open>V \<subseteq> Fset\<close> --- the feasibility construction
     (Prop \<open>prop:openfeas\<close>, Lem \<open>lem:twotriplecover\<close>);
  \<^item> the four \<open>meager (B\<^sub>i \<inter> V)\<close> --- Props \<open>prop:regzero\<close>, \<open>prop:foldzero\<close>,
     \<open>prop:foldnonzero\<close>, \<open>prop:regnonzero\<close>;
  \<^item> soundness of \<open>X0\<close> --- the nondegenerate-critical-point / finiteness argument
     in the proof of \<open>thm:final\<close>.

  The \<open>cvec = 0\<close> case (Cor \<open>cor:no_czero\<close>) is subsumed into the regular/fold
  stratification of the bad sets.
\<close>

theorem nonemptiness_from_meager_branches:
  fixes Fset V :: "((real^2)^'n) set"
    and X0 :: "real \<Rightarrow> ((real^2)^'n) set"
    and Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero :: "((real^2)^'n) set"
  assumes V_open: "open V" and V_nonempty: "V \<noteq> {}" and V_subset_Fset: "V \<subseteq> Fset"
    and meager_reg_nonzero: "meager (Breg_nonzero \<inter> V)"
    and meager_reg_zero:    "meager (Breg_zero \<inter> V)"
    and meager_fold_zero:   "meager (Bfold_zero \<inter> V)"
    and meager_fold_nonzero:"meager (Bfold_nonzero \<inter> V)"
    and X0_sound:
      "\<And>x. x \<in> V - bad_union Breg_nonzero Breg_zero Bfold_zero Bfold_nonzero
            \<Longrightarrow> \<exists>\<xi>>0. x \<in> X0 \<xi>"
  shows "\<exists>\<xi>>0. Fzero Fset X0 \<xi> \<noteq> {}"
  by (rule nonemptiness_from_branches[OF V_open V_nonempty V_subset_Fset
        meager_reg_nonzero meager_reg_zero meager_fold_zero meager_fold_nonzero X0_sound])

end
