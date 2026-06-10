theory Nonemptiness_Robust2
  imports "Applied_Math_Appendix_Base.Nonemptiness_Robust1"
begin

section \<open>Robust feasible set, part 2: the diagonal \<open>Sym\<^sup>2T\<close> moment transport laws\<close>

text \<open>This small theory is the second half of the original \<open>Nonemptiness_Robust\<close>:
  the two diagonal moment transport laws \<open>M11_moment_applyT\<close> / \<open>M22_moment_applyT\<close>
  ([E] brick 3, \<open>Sym\<^sup>2T\<close>).  Their original proofs carried pointwise \<open>key\<close>/\<open>sum_key\<close>
  identities with ~24 raw \<open>T $ i $ j\<close> vec-nth occurrences, which hang elaboration
  at parse time (the \<open>*\<close>-overload pathology documented at \<open>M12_moment_applyT\<close> in
  \<open>Nonemptiness_Robust3\<close>); under parallel scheduling they blew past the session
  timeout.  Here the proofs are rewritten with the matrix entries abbreviated as
  scalars (\<^theory_text>\<open>define t11 \<dots>\<close>), which parses immediately.  The expensive-but-stable
  first half lives in the \<open>Applied_Math_Appendix_Base\<close> heap (\<open>Nonemptiness_Robust1\<close>).\<close>

lemma M11_moment_applyT:
  fixes T :: "real^2^2"
  assumes "transpose T *v c = c0_paper"
  shows "M11_moment (applyT T y) c
       = of_real ((T $ 1 $ 1)\<^sup>2) * M11_moment y c0_paper
       + of_real (2 * (T $ 1 $ 1) * (T $ 1 $ 2)) * M12_moment y c0_paper
       + of_real ((T $ 1 $ 2)\<^sup>2) * M22_moment y c0_paper"
proof -
  define t11 where "t11 = T $ 1 $ 1"
  define t12 where "t12 = T $ 1 $ 2"
  have key: "\<And>n.
       phase c (applyT T y) n * (of_real ((applyT T y $ n) $ 1))\<^sup>2
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2))"
  proof -
    fix n
    have ph: "phase c (applyT T y) n = phase c0_paper y n"
      by (rule phase_applyT[OF assms])
    have lin: "(applyT T y $ n) $ 1 = t11 * (y $ n) $ 1 + t12 * (y $ n) $ 2"
      unfolding t11_def t12_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    show "phase c (applyT T y) n * (of_real ((applyT T y $ n) $ 1))\<^sup>2
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2))"
      using ph lin
      by (simp add: w_M12_def of_real_add of_real_mult power2_eq_square algebra_simps)
  qed

  have sum_key:
    "(\<Sum>n\<in>UNIV. phase c (applyT T y) n
          * (of_real ((applyT T y $ n) $ 1))\<^sup>2)
     =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2)))"
  proof -
    have "(\<Sum>n\<in>UNIV. phase c (applyT T y) n
          * (of_real ((applyT T y $ n) $ 1))\<^sup>2)
       =
      (\<Sum>n\<in>UNIV.
         phase c0_paper y n
           * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2))
       + phase c0_paper y n
           * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12))
       + phase c0_paper y n
           * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2)))"
      by (rule sum.cong, rule refl, simp add: key)
    also have "\<dots> =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11\<^sup>2)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (2 * t11 * t12)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12\<^sup>2)))"
      by (simp add: sum.distrib add.assoc)
    finally show ?thesis .
  qed

  show ?thesis
    unfolding M11_moment_def M12_moment_def M22_moment_def
    using sum_key[unfolded t11_def t12_def]
    by (simp add: sum_distrib_left algebra_simps power2_eq_square ac_simps)
qed

lemma M22_moment_applyT:
  fixes T :: "real^2^2"
  assumes "transpose T *v c = c0_paper"
  shows "M22_moment (applyT T y) c
       = of_real ((T $ 2 $ 1)\<^sup>2) * M11_moment y c0_paper
       + of_real (2 * (T $ 2 $ 1) * (T $ 2 $ 2)) * M12_moment y c0_paper
       + of_real ((T $ 2 $ 2)\<^sup>2) * M22_moment y c0_paper"
proof -
  define t21 where "t21 = T $ 2 $ 1"
  define t22 where "t22 = T $ 2 $ 2"
  have key: "\<And>n.
       phase c (applyT T y) n * (of_real ((applyT T y $ n) $ 2))\<^sup>2
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2))"
  proof -
    fix n
    have ph: "phase c (applyT T y) n = phase c0_paper y n"
      by (rule phase_applyT[OF assms])
    have lin: "(applyT T y $ n) $ 2 = t21 * (y $ n) $ 1 + t22 * (y $ n) $ 2"
      unfolding t21_def t22_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    show "phase c (applyT T y) n * (of_real ((applyT T y $ n) $ 2))\<^sup>2
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2))"
      using ph lin
      by (simp add: w_M12_def of_real_add of_real_mult power2_eq_square algebra_simps)
  qed

  have sum_key:
    "(\<Sum>n\<in>UNIV. phase c (applyT T y) n
          * (of_real ((applyT T y $ n) $ 2))\<^sup>2)
     =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2)))"
  proof -
    have "(\<Sum>n\<in>UNIV. phase c (applyT T y) n
          * (of_real ((applyT T y $ n) $ 2))\<^sup>2)
       =
      (\<Sum>n\<in>UNIV.
         phase c0_paper y n
           * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2))
       + phase c0_paper y n
           * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22))
       + phase c0_paper y n
           * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2)))"
      by (rule sum.cong, rule refl, simp add: key)
    also have "\<dots> =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t21\<^sup>2)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (2 * t21 * t22)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t22\<^sup>2)))"
      by (simp add: sum.distrib add.assoc)
    finally show ?thesis .
  qed

  show ?thesis
    unfolding M11_moment_def M12_moment_def M22_moment_def
    using sum_key[unfolded t21_def t22_def]
    by (simp add: sum_distrib_left algebra_simps power2_eq_square ac_simps)
qed

end
