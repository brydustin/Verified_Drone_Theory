theory Scratch_AlignedCover
  imports "Applied_Math_M5_Wiring.Scratch_Wiring"
begin

section \<open>A clean aligned-phase cover for reuse by D3\<close>

text \<open>
  This theory isolates the already-proved aligned-phase parametrization from
  the later D4 development.  It has no dependency on the D4 collision branch
  and is built with \<open>quick_and_dirty = false\<close>.
\<close>

definition aligned_conf :: "((real^2)^'n::finite) \<Rightarrow> (real^2) \<Rightarrow> bool" where
  "aligned_conf x c \<longleftrightarrow> (\<forall>m. Im (cnj (A_moment x c) * phase c x m) = 0)"

lemma perp2_self_inner: "perp2 c \<bullet> perp2 c = c \<bullet> c"
  unfolding perp2_def
  by (simp add: inner_vec_def sum_2 vector_2 power2_eq_square)

lemma lagrange2:
  fixes c w :: "real^2"
  shows "(c \<bullet> c) * (w \<bullet> w) = (c \<bullet> w)^2 + (perp2 c \<bullet> w)^2"
  unfolding perp2_def
  by (simp add: inner_vec_def sum_2 vector_2 power2_eq_square algebra_simps)

lemma perp2_decomp2:
  fixes c v :: "real^2"
  assumes cnz: "c \<noteq> 0"
  shows "v = ((c \<bullet> v)/(c \<bullet> c)) *\<^sub>R c + ((perp2 c \<bullet> v)/(c \<bullet> c)) *\<^sub>R perp2 c"
proof -
  have ccnz: "c \<bullet> c \<noteq> 0"
    using cnz by simp
  define w where
    "w = v - ((c \<bullet> v)/(c \<bullet> c)) *\<^sub>R c - ((perp2 c \<bullet> v)/(c \<bullet> c)) *\<^sub>R perp2 c"
  have orth1: "c \<bullet> w = 0"
    unfolding w_def
    using ccnz
    by (simp add: inner_diff_right perp2_orth)
  have orth2: "perp2 c \<bullet> w = 0"
  proof -
    have pc: "perp2 c \<bullet> c = 0"
      using perp2_orth inner_commute by metis
    show ?thesis
      unfolding w_def
      using ccnz
      by (simp add: inner_diff_right perp2_self_inner pc)
  qed
  have "(c \<bullet> c) * (w \<bullet> w) = 0"
    using lagrange2[of c w] orth1 orth2 by simp
  hence "w \<bullet> w = 0"
    using ccnz by simp
  hence "w = 0"
    by simp
  thus ?thesis
    unfolding w_def
    by (metis add.commute add.right_neutral diff_add_cancel)
qed

lemma aligned_relation:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  assumes al: "aligned_conf x c"
  shows "Re (A_moment x c) * sin (c \<bullet> vec_nth x m)
       + Im (A_moment x c) * cos (c \<bullet> vec_nth x m) = 0"
proof -
  have ph: "phase c x m = cis (- (c \<bullet> vec_nth x m))"
    by (simp add: phase_def)
  have base: "Im (cnj (A_moment x c) * phase c x m) = 0"
    using al unfolding aligned_conf_def by blast
  have "Im (cnj (A_moment x c) * cis (- (c \<bullet> vec_nth x m))) = 0"
    using base unfolding ph .
  moreover have "Im (cnj (A_moment x c) * cis (- (c \<bullet> vec_nth x m)))
      = Re (A_moment x c) * sin (- (c \<bullet> vec_nth x m))
        - Im (A_moment x c) * cos (- (c \<bullet> vec_nth x m))"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma aligned_pairwise_sin_zero:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  assumes Anz: "A_moment x c \<noteq> 0" and al: "aligned_conf x c"
  shows "sin (c \<bullet> vec_nth x m - c \<bullet> vec_nth x m') = 0"
proof -
  define rA where "rA = Re (A_moment x c)"
  define iA where "iA = Im (A_moment x c)"
  define t where "t q = c \<bullet> vec_nth x q" for q :: 'n
  have rel: "rA * sin (t q) + iA * cos (t q) = 0" for q
    unfolding rA_def iA_def t_def by (rule aligned_relation[OF al])
  have rzero: "rA * sin (t m - t m') = 0"
  proof -
    have "rA * sin (t m - t m')
        = (rA * sin (t m)) * cos (t m') - cos (t m) * (rA * sin (t m'))"
      by (simp add: sin_diff algebra_simps)
    also have "\<dots> = (- iA * cos (t m)) * cos (t m') - cos (t m) * (- iA * cos (t m'))"
      using rel[of m] rel[of m'] by (simp add: algebra_simps, 
          smt (verit) Groups.mult_ac(2) calculation mult_eq_0_iff mult_minus_left sin_diff
          vector_space_over_itself.scale_left_commute)
    also have "\<dots> = 0"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have izero: "iA * sin (t m - t m') = 0"
  proof -
    have "iA * sin (t m - t m')
        = sin (t m) * (iA * cos (t m')) - (iA * cos (t m)) * sin (t m')"
      by (simp add: sin_diff algebra_simps)
    also have "\<dots> = sin (t m) * (- rA * sin (t m')) - (- rA * sin (t m)) * sin (t m')"
      using rel[of m] rel[of m'] by (simp add: algebra_simps,
          smt (verit, ccfv_threshold) Groups.mult_ac(2) mult_eq_0_iff rzero sin_diff)
    also have "\<dots> = 0"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have "rA \<noteq> 0 \<or> iA \<noteq> 0"
    using Anz unfolding rA_def iA_def by (metis complex.expand zero_complex.simps)
  thus ?thesis
    using rzero izero unfolding t_def by auto
qed

lemma aligned_quantization:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  assumes cnz: "c \<noteq> 0" and Anz: "A_moment x c \<noteq> 0" and al: "aligned_conf x c"
  obtains k :: "'n \<Rightarrow> int" and \<alpha> :: real and s :: "real^'n"
  where "\<alpha> \<in> {0..pi}"
    and "\<And>m. vec_nth x m
        = ((\<alpha> + of_int (k m) * pi)/(c \<bullet> c)) *\<^sub>R c + (vec_nth s m) *\<^sub>R perp2 c"
proof -
  define t where "t q = c \<bullet> vec_nth x q" for q :: 'n
  define m0 where "m0 = (SOME q :: 'n. True)"
  have step: "\<exists>i::int. t q - t m0 = of_int i * pi" for q
    using aligned_pairwise_sin_zero[OF Anz al, of q m0]
    unfolding t_def by (simp add: sin_zero_iff_int2)
  define i where "i q = (SOME j::int. t q - t m0 = of_int j * pi)" for q
  have ieq: "t q - t m0 = of_int (i q) * pi" for q
    unfolding i_def by (rule someI_ex[OF step])
  define quo where "quo = floor (t m0 / pi)"
  define \<alpha> where "\<alpha> = t m0 - of_int quo * pi"
  have alo: "0 \<le> \<alpha>"
  proof -
    have "of_int quo \<le> t m0 / pi"
      unfolding quo_def by (rule of_int_floor_le)
    hence "of_int quo * pi \<le> t m0"
      using pi_gt_zero by (simp add: pos_le_divide_eq mult.commute)
    thus ?thesis unfolding \<alpha>_def by simp
  qed
  have ahi: "\<alpha> \<le> pi"
  proof -
    have "t m0 / pi < of_int quo + 1"
      unfolding quo_def by auto 
    hence "t m0 < (of_int quo + 1) * pi"
      using pi_gt_zero by (simp add: pos_divide_less_eq mult.commute)
    thus ?thesis unfolding \<alpha>_def by (simp add: algebra_simps)
  qed
  define k where "k q = i q + quo" for q
  have teq: "t q = \<alpha> + of_int (k q) * pi" for q
    using ieq[of q] unfolding \<alpha>_def k_def by (simp add: algebra_simps)
  define s where "s = (\<chi> q. (perp2 c \<bullet> vec_nth x q)/(c \<bullet> c))"
  have xeq: "vec_nth x q
      = ((\<alpha> + of_int (k q) * pi)/(c \<bullet> c)) *\<^sub>R c + (vec_nth s q) *\<^sub>R perp2 c" for q
  proof -
    have "vec_nth x q = ((c \<bullet> vec_nth x q)/(c \<bullet> c)) *\<^sub>R c
        + ((perp2 c \<bullet> vec_nth x q)/(c \<bullet> c)) *\<^sub>R perp2 c"
      by (rule perp2_decomp2[OF cnz])
    thus ?thesis
      using teq[of q] unfolding t_def s_def by simp
  qed
  show thesis
    by (rule that[of \<alpha> k s]) (use alo ahi xeq in auto)
qed

lemma A_moment_nz_of_A_cart:
  assumes "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
  shows "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0"
  using assms by (simp add: A_cart_eq_Afun Afun_eq_A_moment)

section \<open>\<section>7j stage B: the parametrization maps and their closed negligible images\<close>

definition align_param_map ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> ('n::finite \<Rightarrow> int)
    \<Rightarrow> ((real^2) \<times> real \<times> (real^'n)) \<Rightarrow> ((real^2)^'n)" where
  "align_param_map \<omega>0 \<omega>s k p =
     (\<chi> m. ((fst (snd p) + of_int (k m) * pi)
              /(cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)))
             *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst p)
           + (vec_nth (snd (snd p)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst p)))"

definition align_dom ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> nat
    \<Rightarrow> ((real^2) \<times> real \<times> (real^('n::finite))) set" where
  "align_dom \<omega>0 \<omega>s K0 j = {p. fst p \<in> K0
      \<and> 1/real (Suc j) \<le> cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)
      \<and> fst (snd p) \<in> {0..pi}
      \<and> snd (snd p) \<in> cball 0 (real j)}"

lemma bounded_linear_perp2: "bounded_linear perp2"
proof (rule bounded_linear_intro[of perp2 1])
  show "\<And>x y. perp2 (x + y) = perp2 x + perp2 y"
    unfolding perp2_def
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2)
  show "\<And>r x. perp2 (r *\<^sub>R x) = r *\<^sub>R perp2 x"
    unfolding perp2_def
    by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2 vector_2)
  show "\<And>x. norm (perp2 x) \<le> norm x * 1"
    by (simp add: norm_eq_sqrt_inner perp2_self_inner)
qed

lemma bounded_linear_axis:
  fixes m :: "'k::finite"
  shows "bounded_linear (axis m :: real^2 \<Rightarrow> (real^2)^'k)"
proof (rule bounded_linear_intro[of _ 1])
  fix x y :: "real^2"
  show "axis m (x + y) = axis m x + axis m y"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 'k
    show "vec_nth (axis m (x + y)) i = vec_nth (axis m x + axis m y) i"
    proof (cases "i = m")
      case True
      thus ?thesis by (simp add: axis_def)
    next
      case False
      have l: "vec_nth (axis m (x + y)) i = (0::real^2)"
        using False by (simp add: axis_def)
      have r: "vec_nth (axis m x + axis m y) i = (0::real^2) + (0::real^2)"
        using False by (simp add: axis_def)
      show ?thesis
        unfolding l r by simp
    qed
  qed
next
  fix r :: real and x :: "real^2"
  show "axis m (r *\<^sub>R x) = r *\<^sub>R axis m x"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 'k
    show "vec_nth (axis m (r *\<^sub>R x)) i = vec_nth (r *\<^sub>R axis m x) i"
    proof (cases "i = m")
      case True
      thus ?thesis by (simp add: axis_def)
    next
      case False
      have l: "vec_nth (axis m (r *\<^sub>R x)) i = (0::real^2)"
        using False by (simp add: axis_def)
      have r2: "vec_nth (r *\<^sub>R axis m x) i = r *\<^sub>R (0::real^2)"
        using False by (simp add: axis_def)
      show ?thesis
        unfolding l r2 by simp
    qed
  qed
next
  fix x :: "real^2"
  have "(axis m x :: (real^2)^'k) \<bullet> axis m x
      = (\<Sum>i\<in>UNIV. vec_nth (axis m x :: (real^2)^'k) i
           \<bullet> vec_nth (axis m x :: (real^2)^'k) i)"
    by (simp add: inner_vec_def)
  also have "\<dots> = (\<Sum>i\<in>(UNIV::'k set). if i = m then x \<bullet> x else 0)"
    by (rule sum.cong[OF refl]) (simp add: axis_def)
  also have "\<dots> = x \<bullet> x"
    by (simp add: sum.delta)
  finally have "(axis m x :: (real^2)^'k) \<bullet> axis m x = x \<bullet> x" .
  thus "norm (axis m x :: (real^2)^'k) \<le> norm x * 1"
    by (simp add: norm_eq_sqrt_inner)
qed

lemma vec_lambda_eq_sum_axis:
  fixes F :: "'k::finite \<Rightarrow> 'a::real_normed_vector"
  shows "(\<chi> m. F m) = (\<Sum>m\<in>UNIV. axis m (F m))"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix i :: 'k
  have "vec_nth (\<Sum>m\<in>UNIV. axis m (F m)) i = (\<Sum>m\<in>UNIV. vec_nth (axis m (F m)) i)"
    by simp
  also have "\<dots> = (\<Sum>m\<in>UNIV. if m = i then F m else 0)"
    by (rule sum.cong[OF refl]) (simp add: axis_def)
  also have "\<dots> = F i"
    by (simp add: sum.delta)
  finally show "vec_nth (\<chi> m. F m) i = vec_nth (\<Sum>m\<in>UNIV. axis m (F m)) i"
    by simp
qed

lemma align_dom_denom_pos:
  assumes "p \<in> align_dom \<omega>0 \<omega>s K0 j"
  shows "cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p) \<noteq> 0"
proof -
  have "(0::real) < 1/real (Suc j)" by simp
  moreover have "1/real (Suc j) \<le> cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)"
    using assms unfolding align_dom_def by blast
  ultimately show ?thesis by linarith
qed

lemma cvec_fst_differentiable:
  fixes S :: "((real^2) \<times> real \<times> (real^('n::finite))) set"
    and p :: "(real^2) \<times> real \<times> (real^'n)"
  shows "(\<lambda>q. cvec_dip \<omega>0 \<omega>s (fst q)) differentiable (at p within S)"
proof -
  have c: "cvec_dip \<omega>0 \<omega>s differentiable (at (fst p))"
    using has_derivative_cvec_dip differentiable_def by blast
  have f: "fst differentiable (at p within S)"
    by (simp add: bounded_linear_imp_differentiable bounded_linear_fst)
  have "(cvec_dip \<omega>0 \<omega>s \<circ> fst) differentiable (at p within S)"
    by (rule differentiable_chain_within[OF f differentiable_at_withinI[OF c]])
  thus ?thesis by (simp add: o_def)
qed

lemma align_param_map_differentiable_on:
  fixes k :: "'n::finite \<Rightarrow> int"
  shows "align_param_map \<omega>0 \<omega>s k differentiable_on
      (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^'n)) set)"
proof -
  define D where "D = (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^'n)) set)"
  have comp: "(\<lambda>p. axis m (((fst (snd p) + of_int (k m) * pi)
              /(cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)))
             *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst p)
           + (vec_nth (snd (snd p)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst p))))
      differentiable (at p within D)"
    if pin: "p \<in> D" for m and p :: "(real^2) \<times> real \<times> (real^'n)"
  proof -
    have cd: "(\<lambda>q. cvec_dip \<omega>0 \<omega>s (fst q))
        differentiable (at p within D)"
      by (rule cvec_fst_differentiable)
    have bl_alph: "bounded_linear (\<lambda>q::((real^2) \<times> real \<times> (real^'n)). fst (snd q))"
      by (rule bounded_linear_compose[OF bounded_linear_fst bounded_linear_snd])
    have alph: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)). fst (snd q))
        differentiable (at p within D)"
      by (rule bounded_linear_imp_differentiable[OF bl_alph])
    have bl_ss: "bounded_linear (\<lambda>q::((real^2) \<times> real \<times> (real^'n)). snd (snd q))"
      by (rule bounded_linear_compose[OF bounded_linear_snd bounded_linear_snd])
    have bl_sm: "bounded_linear (\<lambda>q::((real^2) \<times> real \<times> (real^'n)). vec_nth (snd (snd q)) m)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth bl_ss])
    have sm: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)). vec_nth (snd (snd q)) m)
        differentiable (at p within D)"
      by (rule bounded_linear_imp_differentiable[OF bl_sm])
    have dnz: "cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p) \<noteq> 0"
      using align_dom_denom_pos pin unfolding D_def by blast
    have inner_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)).
          cvec_dip \<omega>0 \<omega>s (fst q) \<bullet> cvec_dip \<omega>0 \<omega>s (fst q))
        differentiable (at p within D)"
      by (rule differentiable_inner[OF cd cd])
    have perp_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)). perp2 (cvec_dip \<omega>0 \<omega>s (fst q)))
        differentiable (at p within D)"
    proof -
      have "(perp2 \<circ> (\<lambda>q::((real^2) \<times> real \<times> (real^'n)). cvec_dip \<omega>0 \<omega>s (fst q)))
          differentiable (at p within D)"
        by (rule differentiable_chain_within[OF cd
              bounded_linear_imp_differentiable[OF bounded_linear_perp2]])
      thus ?thesis by (simp add: o_def)
    qed
    have numer_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)). fst (snd q) + of_int (k m) * pi)
        differentiable (at p within D)"
      by (rule differentiable_add[OF alph differentiable_const])
    have quot_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)).
          (fst (snd q) + of_int (k m) * pi)
            /(cvec_dip \<omega>0 \<omega>s (fst q) \<bullet> cvec_dip \<omega>0 \<omega>s (fst q)))
        differentiable (at p within D)"
      by (rule differentiable_divide[OF numer_d inner_d dnz])
    have sc1_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)).
          ((fst (snd q) + of_int (k m) * pi)
            /(cvec_dip \<omega>0 \<omega>s (fst q) \<bullet> cvec_dip \<omega>0 \<omega>s (fst q)))
           *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst q))
        differentiable (at p within D)"
      by (rule differentiable_scaleR[OF quot_d cd])
    have sc2_d: "(\<lambda>q::((real^2) \<times> real \<times> (real^'n)).
          (vec_nth (snd (snd q)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst q)))
        differentiable (at p within D)"
      by (rule differentiable_scaleR[OF sm perp_d])
    have core: "(\<lambda>p. ((fst (snd p) + of_int (k m) * pi)
              /(cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)))
             *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst p)
           + (vec_nth (snd (snd p)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst p)))
        differentiable (at p within D)"
      by (rule differentiable_add[OF sc1_d sc2_d])
    show ?thesis
      using differentiable_chain_within[OF core
            bounded_linear_imp_differentiable[OF bounded_linear_axis]]
      by (simp add: o_def)
  qed
  have eq: "align_param_map \<omega>0 \<omega>s k
      = (\<lambda>p. \<Sum>m\<in>UNIV. axis m (((fst (snd p) + of_int (k m) * pi)
              /(cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)))
             *\<^sub>R cvec_dip \<omega>0 \<omega>s (fst p)
           + (vec_nth (snd (snd p)) m) *\<^sub>R perp2 (cvec_dip \<omega>0 \<omega>s (fst p))))"
    unfolding align_param_map_def
    by (rule ext) (rule vec_lambda_eq_sum_axis)
  have "align_param_map \<omega>0 \<omega>s k differentiable_on D"
    unfolding eq differentiable_on_def
    by (intro ballI differentiable_sum comp, simp_all) 
  thus ?thesis
    unfolding D_def .
qed

lemma align_param_map_continuous_on:
  "continuous_on (align_dom \<omega>0 \<omega>s K0 j) (align_param_map \<omega>0 \<omega>s k)"
  by (rule differentiable_imp_continuous_on[OF align_param_map_differentiable_on])

lemma compact_align_dom:
  assumes K0c: "compact K0"
  shows "compact (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^('n::finite))) set)"
proof -
  have eq: "(align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^'n)) set)
      = (K0 \<times> {0..pi} \<times> cball 0 (real j))
        \<inter> {p. 1/real (Suc j)
            \<le> cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)}"
    unfolding align_dom_def by (auto simp: mem_Times_iff)
  have cpt: "compact ((K0 \<times> {0..pi} \<times> cball 0 (real j))
      :: ((real^2) \<times> real \<times> (real^'n)) set)"
    by (intro compact_Times K0c compact_Icc compact_cball)
  have cont: "continuous_on (UNIV :: ((real^2) \<times> real \<times> (real^'n)) set)
      (\<lambda>p. cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p))"
    by (intro continuous_on_inner
          continuous_on_compose2[OF continuous_on_cvec_dip
            continuous_on_fst[OF continuous_on_id] subset_UNIV])
  have cls: "closed {p :: ((real^2) \<times> real \<times> (real^'n)).
      1/real (Suc j) \<le> cvec_dip \<omega>0 \<omega>s (fst p) \<bullet> cvec_dip \<omega>0 \<omega>s (fst p)}"
    by (intro closed_Collect_le continuous_on_const cont)
  show ?thesis
    unfolding eq by (rule compact_Int_closed[OF cpt cls])
qed

lemma align_image_closed:
  assumes K0c: "compact K0"
  shows "closed (align_param_map \<omega>0 \<omega>s k
      ` (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^('n::finite))) set))"
  by (intro compact_imp_closed compact_continuous_image
        align_param_map_continuous_on compact_align_dom K0c)

lemma align_image_negligible:
  assumes card4: "4 \<le> CARD('n::finite)"
  shows "negligible (align_param_map \<omega>0 \<omega>s k
      ` (align_dom \<omega>0 \<omega>s K0 j :: ((real^2) \<times> real \<times> (real^'n)) set))"
proof (rule negligible_differentiable_image_lowdim)
  show "DIM((real^2) \<times> real \<times> (real^'n)) < DIM((real^2)^'n)"
    using card4 by simp
  show "align_param_map \<omega>0 \<omega>s k differentiable_on align_dom \<omega>0 \<omega>s K0 j"
    by (rule align_param_map_differentiable_on)
qed

subsection \<open>Case (ii): coincident drone positions are already negligible\<close>

text \<open>No hypothesis anywhere requires distinct drone positions, so the
  ``two drones occupy the same point'' locus must be covered regardless of
  what \<open>reg1\<close>/\<open>reg2\<close> end up needing. It costs nothing: the set sits inside
  a hyperplane, independently of \<open>\<omega>\<close> entirely.\<close>

lemma drone_coincide_negligible:
  fixes i j :: "'n::finite"
  assumes ij: "i \<noteq> j"
  shows "negligible {x :: (real^2)^'n. x $ i = x $ j}"
proof -
  define v :: "real^2" where "v = axis (1::2) (1::real)"
  define a :: "(real^2)^'n" where "a = axis i v - axis j v"
  have vnz: "v \<noteq> 0" unfolding v_def by simp
  have ai: "a $ i = v"
    unfolding a_def by (simp add: axis_def ij)
  have anz: "a \<noteq> 0"
    using ai vnz by (metis vec_eq_iff zero_index)
  have sub: "{x :: (real^2)^'n. x $ i = x $ j} \<subseteq> {x. a \<bullet> x = 0}"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x. x $ i = x $ j}"
    then have xij: "x $ i = x $ j" by simp
    have "a \<bullet> x = inner (axis i v) x - inner (axis j v) x"
      unfolding a_def by (simp add: inner_diff_left)
    also have "\<dots> = inner v (x $ i) - inner v (x $ j)"
      by (simp add: inner_axis')
    also have "\<dots> = 0"
      using xij by simp
    finally show "x \<in> {x. a \<bullet> x = 0}" by simp
  qed
  have hyp: "negligible {x :: (real^2)^'n. a \<bullet> x = 0}"
    by (rule negligible_hyperplane) (auto simp: anz)
  show ?thesis
    using negligible_subset[OF hyp sub] .
qed

lemma aligned_in_align_param_image:
  fixes x :: "(real^2)^'n::finite" and \<omega> :: "real^2"
  assumes wK0: "\<omega> \<in> K0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and Anz: "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0"
    and al: "aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)"
  shows "\<exists>(k::'n \<Rightarrow> int) (j::nat).
      x \<in> align_param_map \<omega>0 \<omega>s k ` align_dom \<omega>0 \<omega>s K0 j"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  obtain k :: "'n \<Rightarrow> int" and \<alpha> :: real and s :: "real^'n"
    where arange: "\<alpha> \<in> {0..pi}"
      and xeq: "\<And>m. vec_nth x m
        = ((\<alpha> + of_int (k m) * pi)/(c \<bullet> c)) *\<^sub>R c + (vec_nth s m) *\<^sub>R perp2 c"
    using aligned_quantization[OF cnz[folded c_def] Anz[folded c_def] al[folded c_def]]
    by metis
  have ccpos: "0 < c \<bullet> c"
    using cnz unfolding c_def by (metis inner_gt_zero_iff)
  obtain j1 :: nat where j1: "inverse (real (Suc j1)) < c \<bullet> c"
    using reals_Archimedean[OF ccpos] by blast
  obtain j2 :: nat where j2: "norm s \<le> real j2"
    using real_arch_simple by blast
  define j where "j = max j1 j2"
  have denom_ok: "1/real (Suc j) \<le> c \<bullet> c"
  proof -
    have "1/real (Suc j) \<le> 1/real (Suc j1)"
      unfolding j_def by (simp only: frac_le)
    also have "\<dots> < c \<bullet> c"
      using j1 by (simp only: inverse_eq_divide)
    finally show ?thesis by linarith
  qed
  have s_ok: "s \<in> cball 0 (real j)"
    using j2 unfolding j_def by (simp add: dist_norm)
  define p where "p = (\<omega>, \<alpha>, s)"
  have pin: "p \<in> align_dom \<omega>0 \<omega>s K0 j"
    unfolding align_dom_def p_def
    using wK0 denom_ok arange s_ok unfolding c_def by simp
  have "align_param_map \<omega>0 \<omega>s k p = x"
    unfolding align_param_map_def p_def
    by (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
      (simp add: c_def[symmetric] xeq[symmetric])
  thus ?thesis
    using pin by (metis imageI)
qed

section \<open>\<section>7j stage C: countable assembly and the conditional Branch-P core\<close>

theorem aligned_bad_closed_cover:
  fixes \<omega>0 \<omega>s :: "real^2" and K0 :: "(real^2) set"
  assumes card4: "4 \<le> CARD('n::finite)"
    and K0c: "compact K0"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
      {x. \<exists>\<omega>\<in>K0. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
            \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
            \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)} \<subseteq> (\<Union>n. K n)
    \<and> (\<forall>n. closed (K n)) \<and> (\<forall>n. negligible (K n))"
proof -
  have cnt: "Countable_Set.countable (UNIV :: (('n \<Rightarrow> int) \<times> nat) set)"
    by (rule countableI_type)
  have ne: "(UNIV :: (('n \<Rightarrow> int) \<times> nat) set) \<noteq> {}"
    by blast
  define enum where "enum = from_nat_into (UNIV :: (('n \<Rightarrow> int) \<times> nat) set)"
  have enum_surj: "range enum = (UNIV :: (('n \<Rightarrow> int) \<times> nat) set)"
    unfolding enum_def by (rule range_from_nat_into[OF ne cnt])
  define K :: "nat \<Rightarrow> ((real^2)^'n) set" where
    "K n = align_param_map \<omega>0 \<omega>s (fst (enum n))
        ` align_dom \<omega>0 \<omega>s K0 (snd (enum n))" for n
  have closedK: "closed (K n)" for n
    unfolding K_def by (rule align_image_closed[OF K0c])
  have negK: "negligible (K n)" for n
    unfolding K_def by (rule align_image_negligible[OF card4])
  have cover: "{x. \<exists>\<omega>\<in>K0. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
        \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
        \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)} \<subseteq> (\<Union>n. K n)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x. \<exists>\<omega>\<in>K0. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
        \<and> A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0
        \<and> aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)}"
    then obtain \<omega> where wK0: "\<omega> \<in> K0"
      and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
      and Anz: "A_moment x (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0"
      and al: "aligned_conf x (cvec_dip \<omega>0 \<omega>s \<omega>)"
      by blast
    obtain k :: "'n \<Rightarrow> int" and j :: nat
      where img: "x \<in> align_param_map \<omega>0 \<omega>s k ` align_dom \<omega>0 \<omega>s K0 j"
      using aligned_in_align_param_image[OF wK0 cnz Anz al] by blast
    obtain n where "enum n = (k, j)"
      using enum_surj by (metis UNIV_I imageE)
    hence "x \<in> K n"
      unfolding K_def using img by simp
    thus "x \<in> (\<Union>n. K n)" by blast
  qed
  show ?thesis
    using cover closedK negK by blast
qed

end
