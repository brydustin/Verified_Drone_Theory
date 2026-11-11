section \<open>A strictly feasible configuration\<close>

theory Feasibility_Witness
  imports
    Feasible_Set
    Dipole_Pattern
begin

lemma sum_cis_roots_unity:
  assumes "n > 1"
  shows "(\<Sum>k<n. cis (2 * pi * real k / real n)) = 0"
proof -
  have nn: "real n \<noteq> 0" using assms by simp
  define w where "w = cis (2 * pi / real n)"
  have wne: "w \<noteq> 1"
  proof
    assume "w = 1"
    with assms obtain k :: int where "2 * pi / real n = 2 * pi * of_int k"
      by (auto simp: w_def complex_eq_iff cos_one_2pi_int)
    with assms have "real n * of_int k = 1" by (simp add: field_simps)
    also have "real n * of_int k = of_int (int n * k)" by simp
    also have "1 = (of_int 1 :: real)" by simp
    also note of_int_eq_iff
    finally show False using assms by (auto simp: zmult_eq_1_iff)
  qed
  have wn1: "w ^ n = 1"
  proof -
    have "w ^ n = cis (real n * (2 * pi / real n))"
      using Complex.DeMoivre w_def by presburger
    also have "real n * (2 * pi / real n) = 2 * pi" using nn by simp
    finally show ?thesis by simp
  qed
  have "(\<Sum>k<n. cis (2 * pi * real k / real n)) = (\<Sum>k<n. w ^ k)"
    by (intro sum.cong refl, simp add: Complex.DeMoivre Groups.mult_ac(2) w_def)
  also have "\<dots> = (w ^ n - 1) / (w - 1)"
    using wne by (subst geometric_sum) auto
  also have "\<dots> = 0" using wn1 by simp
  finally show ?thesis .
qed

lemma sum_cis_neg_roots_unity:
  assumes "n > 1"
  shows "(\<Sum>k<n. cis (- (2 * pi * real k / real n))) = 0"
proof -
  have "(\<Sum>k<n. cis (- (2 * pi * real k / real n)))
          = cnj (\<Sum>k<n. cis (2 * pi * real k / real n))"
    by (simp add: cnj_sum cis_cnj)
  also have "\<dots> = cnj 0" by (subst sum_cis_roots_unity[OF assms]) simp
  finally show ?thesis by simp
qed

lemma cvec_dip_at_main:
  assumes "kz \<omega>s \<noteq> kz \<omega>0"
  shows "cvec_dip \<omega>0 \<omega>s \<omega>0 = 0"
proof -
  have d: "kz \<omega>s - kz \<omega>0 \<noteq> 0" using assms by simp
  have c1: "(kx \<omega>0 - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega>0 - kz \<omega>s) = 0"
    using d by (simp add: field_simps)
  have c2: "(ky \<omega>0 - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega>0 - kz \<omega>s) = 0"
    using d by (simp add: field_simps)
  show ?thesis unfolding cvec_dip_def c1 c2 by simp
qed

lemma A_cart_at_main:
  assumes "kz \<omega>s \<noteq> kz \<omega>0"
  shows "A_cart (cvec_dip \<omega>0 \<omega>s) (x::(real^2)^'n) \<omega>0 = of_nat CARD('n)"
  by (simp add: A_cart_def cvec_dip_at_main[OF assms])

lemma U_cart_at_main:
  assumes "kz \<omega>s \<noteq> kz \<omega>0"
  shows "U_cart (cvec_dip \<omega>0 \<omega>s) g (x::(real^2)^'n) \<omega>0 = g \<omega>0 * (real CARD('n))\<^sup>2"
proof -
  have "cmod (A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>0) = real CARD('n)"
    by (simp add: A_cart_at_main[OF assms])
  thus ?thesis by (simp add: U_cart_def)
qed

lemma inner_real2: "(a::real^2) \<bullet> b = a$1 * b$1 + a$2 * b$2"
  by (simp add: inner_vec_def sum_2)

lemma spdist_ge_abs1: "\<bar>p$1 - q$1\<bar> \<le> spdist A B D p q"
proof -
  have le: "(p $ 1 - q $ 1)\<^sup>2 \<le> (p $ 1 - q $ 1)\<^sup>2 + (p $ 2 - q $ 2)\<^sup>2
              + ((A * (p $ 1 - q $ 1) + B * (p $ 2 - q $ 2)) / D)\<^sup>2"
    using zero_le_power2[of "p$2-q$2"]
          zero_le_power2[of "(A*(p$1-q$1)+B*(p$2-q$2))/D"] by linarith
  have "\<bar>p$1-q$1\<bar> = sqrt ((p$1-q$1)\<^sup>2)" by simp
  also have "\<dots> \<le> spdist A B D p q"
    unfolding spdist_def by (rule real_sqrt_le_mono[OF le])
  finally show ?thesis .
qed

lemma spdist_ge_abs2: "\<bar>p$2 - q$2\<bar> \<le> spdist A B D p q"
proof -
  have le: "(p $ 2 - q $ 2)\<^sup>2 \<le> (p $ 1 - q $ 1)\<^sup>2 + (p $ 2 - q $ 2)\<^sup>2
              + ((A * (p $ 1 - q $ 1) + B * (p $ 2 - q $ 2)) / D)\<^sup>2"
    using zero_le_power2[of "p$1-q$1"]
          zero_le_power2[of "(A*(p$1-q$1)+B*(p$2-q$2))/D"] by linarith
  have "\<bar>p$2-q$2\<bar> = sqrt ((p$2-q$2)\<^sup>2)" by simp
  also have "\<dots> \<le> spdist A B D p q"
    unfolding spdist_def by (rule real_sqrt_le_mono[OF le])
  finally show ?thesis .
qed

lemma A_cart_null_zero:
  fixes x :: "(real^2)^'n" and f :: "nat \<Rightarrow> 'n"
  assumes N: "CARD('n) > 1"
    and bij: "bij_betw f {..<CARD('n)} (UNIV::'n set)"
    and phase: "\<And>k. k < CARD('n) \<Longrightarrow>
                 cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (x $ f k) = 2 * pi * real k / real CARD('n)"
  shows "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>n = 0"
proof -
  have "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>n
          = (\<Sum>m\<in>UNIV. cis (- (cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (x $ m))))"
    by (simp add: A_cart_def)
  also have "\<dots> = (\<Sum>k<CARD('n). cis (- (cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (x $ f k))))"
    by (rule sum.reindex_bij_betw[OF bij,
          where g = "\<lambda>m. cis (- (cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (x $ m)))", symmetric])
  also have "\<dots> = (\<Sum>k<CARD('n). cis (- (2 * pi * real k / real CARD('n))))"
    using phase by (intro sum.cong refl) simp
  also have "\<dots> = 0" by (rule sum_cis_neg_roots_unity[OF N])
  finally show ?thesis .
qed

lemma nat_real_abs_diff_ge1:
  fixes k j :: nat
  assumes "k \<noteq> j" shows "(1::real) \<le> \<bar>real k - real j\<bar>"
proof -
  have "k < j \<or> j < k" using assms by linarith
  thus ?thesis
  proof
    assume "k < j" hence "k + 1 \<le> j" by simp
    hence "real k + 1 \<le> real j" using of_nat_le_iff by fastforce
    thus ?thesis by simp
  next
    assume "j < k" hence "j + 1 \<le> k" by simp
    hence "real j + 1 \<le> real k" using of_nat_le_iff by fastforce
    thus ?thesis by simp
  qed
qed

lemma gain_dip_nonneg: "0 \<le> gain_dip \<omega>"
  by (simp add: gain_dip_def gdip_eq_edip_sq)

lemma feasible_witness_exists:
  fixes \<omega>0 \<omega>s \<omega>n :: angle and s A B D :: real
  assumes N: "CARD('n) > 1"
    and cn: "cvec_dip \<omega>0 \<omega>s \<omega>n \<noteq> 0"
    and spos: "0 < s"
  shows "\<exists>x::(real^2)^'n. A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega>n = 0
            \<and> (\<forall>m m'. m \<noteq> m' \<longrightarrow> s \<le> spdist A B D (x $ m) (x $ m'))
            \<and> (\<exists>v. \<forall>m. \<exists>r. x $ m = r *\<^sub>R v)"
proof -
  define c1 where "c1 = cvec_dip \<omega>0 \<omega>s \<omega>n $ 1"
  define c2 where "c2 = cvec_dip \<omega>0 \<omega>s \<omega>n $ 2"
  define t where "t = (\<lambda>k::nat. 2 * pi * real k / real CARD('n))"
  obtain f where "bij_betw f {0..<CARD('n)} (UNIV::'n set)"
    using ex_bij_betw_nat_finite[of "UNIV::'n set"] N card.infinite gr_implies_not0 by blast
  hence bijf: "bij_betw f {..<CARD('n)} (UNIV::'n set)" by (simp add: atLeast0LessThan)
  define idx where "idx = inv_into {..<CARD('n)} f"
  have idx_inj: "inj idx"
    unfolding idx_def by (metis bijf bij_betw_imp_surj_on inj_on_inv_into order_refl)
  have idx_f: "idx (f k) = k" if "k < CARD('n)" for k
    using that bijf by (simp add: idx_def bij_betw_imp_inj_on inv_into_f_f)
  have ex_p: "\<exists>p::nat \<Rightarrow> real^2.
       (\<forall>k. c1 * (p k $ 1) + c2 * (p k $ 2) = t k)
     \<and> (\<forall>k j. k \<noteq> j \<longrightarrow> s \<le> \<bar>p k $ 1 - p j $ 1\<bar> \<or> s \<le> \<bar>p k $ 2 - p j $ 2\<bar>)
     \<and> (\<exists>v. \<forall>k. p k = real k *\<^sub>R v)"
  proof (cases "c2 = 0")
    case False
    define v :: "real^2" where "v = vector [s, (2 * pi / real CARD('n) - c1 * s) / c2]"
    define p where "p = (\<lambda>k. real k *\<^sub>R v)"
    have p1: "p k $ 1 = s * real k" and p2: "p k $ 2 = (t k - c1 * (s * real k)) / c2" for k
      using False by (simp_all add: p_def v_def t_def field_simps)
    have ph: "c1 * (p k $ 1) + c2 * (p k $ 2) = t k" for k
      using False by (simp add: p1 p2)
    have sp: "s \<le> \<bar>p k $ 1 - p j $ 1\<bar>" if "k \<noteq> j" for k j
    proof -
      have "p k $ 1 - p j $ 1 = s * (real k - real j)"
        by (simp add: p1 right_diff_distrib)
      hence "\<bar>p k $ 1 - p j $ 1\<bar> = s * \<bar>real k - real j\<bar>"
        using spos by (simp add: abs_mult abs_of_pos)
      moreover have "s * 1 \<le> s * \<bar>real k - real j\<bar>"
        using spos nat_real_abs_diff_ge1[OF that] by (intro mult_left_mono) auto
      ultimately show ?thesis by simp
    qed
    have col: "\<exists>v. \<forall>k. p k = real k *\<^sub>R v"
      unfolding p_def by blast
    show ?thesis by (intro exI[of _ p] conjI allI impI col) (use ph sp in blast)+
  next
    case True
    hence c1ne: "c1 \<noteq> 0"
    proof -
      have "c1 \<noteq> 0 \<or> c2 \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> (c1 \<noteq> 0 \<or> c2 \<noteq> 0)"
        then have "cvec_dip \<omega>0 \<omega>s \<omega>n = 0"
          by (simp add: c1_def c2_def Finite_Cartesian_Product.vec_eq_iff forall_2)
        with cn show False by simp
      qed
      thus ?thesis using True by simp
    qed
    define v :: "real^2" where "v = vector [2 * pi / real CARD('n) / c1, s]"
    define p where "p = (\<lambda>k. real k *\<^sub>R v)"
    have p1: "p k $ 1 = t k / c1" and p2: "p k $ 2 = s * real k" for k
      using c1ne by (simp_all add: p_def v_def t_def field_simps)
    have ph: "c1 * (p k $ 1) + c2 * (p k $ 2) = t k" for k
      using True c1ne by (simp add: p1 p2)
    have sp: "s \<le> \<bar>p k $ 2 - p j $ 2\<bar>" if "k \<noteq> j" for k j
    proof -
      have "p k $ 2 - p j $ 2 = s * (real k - real j)"
        by (simp add: p2 right_diff_distrib)
      hence "\<bar>p k $ 2 - p j $ 2\<bar> = s * \<bar>real k - real j\<bar>"
        using spos by (simp add: abs_mult abs_of_pos)
      moreover have "s * 1 \<le> s * \<bar>real k - real j\<bar>"
        using spos nat_real_abs_diff_ge1[OF that] by (intro mult_left_mono) auto
      ultimately show ?thesis by simp
    qed
    have col: "\<exists>v. \<forall>k. p k = real k *\<^sub>R v"
      unfolding p_def by blast
    show ?thesis by (intro exI[of _ p] conjI allI impI col) (use ph sp in blast)+
  qed
  obtain p :: "nat \<Rightarrow> real^2" and v :: "real^2"
    where pphase: "\<And>k. c1 * (p k $ 1) + c2 * (p k $ 2) = t k"
      and pspace: "\<And>k j. k \<noteq> j \<Longrightarrow> s \<le> \<bar>p k $ 1 - p j $ 1\<bar> \<or> s \<le> \<bar>p k $ 2 - p j $ 2\<bar>"
      and pcol: "\<And>k. p k = real k *\<^sub>R v"
    using ex_p by blast
  define xbar where "xbar = (\<chi> m. p (idx m))"
  have xbar_m: "xbar $ m = p (idx m)" for m by (simp add: xbar_def)
  have afz: "A_cart (cvec_dip \<omega>0 \<omega>s) xbar \<omega>n = 0"
  proof (rule A_cart_null_zero[OF N bijf])
    fix k assume k: "k < CARD('n)"
    have "xbar $ f k = p k" using k by (simp add: xbar_m idx_f)
    thus "cvec_dip \<omega>0 \<omega>s \<omega>n \<bullet> (xbar $ f k) = 2 * pi * real k / real CARD('n)"
      using pphase[of k]
      by (simp add: inner_real2 c1_def[symmetric] c2_def[symmetric] t_def)
  qed
  have spac: "s \<le> spdist A B D (xbar $ m) (xbar $ m')" if mm: "m \<noteq> m'" for m m'
  proof -
    have "idx m \<noteq> idx m'" using mm idx_inj by (auto dest: injD)
    hence disj: "s \<le> \<bar>p (idx m) $ 1 - p (idx m') $ 1\<bar>
               \<or> s \<le> \<bar>p (idx m) $ 2 - p (idx m') $ 2\<bar>"
      by (rule pspace)
    have d1: "\<bar>p (idx m) $ 1 - p (idx m') $ 1\<bar> \<le> spdist A B D (xbar $ m) (xbar $ m')"
      using spdist_ge_abs1[of "xbar $ m" "xbar $ m'" A B D] by (simp add: xbar_m)
    have d2: "\<bar>p (idx m) $ 2 - p (idx m') $ 2\<bar> \<le> spdist A B D (xbar $ m) (xbar $ m')"
      using spdist_ge_abs2[of "xbar $ m" "xbar $ m'" A B D] by (simp add: xbar_m)
    from disj d1 d2 show ?thesis by auto
  qed
  have col: "\<exists>v. \<forall>m. \<exists>r. xbar $ m = r *\<^sub>R v"
    using pcol by (auto simp: xbar_m)
  from afz spac col show ?thesis by (intro exI[of _ xbar]) blast
qed

end
