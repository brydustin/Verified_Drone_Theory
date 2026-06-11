theory Nonemptiness_Robust3
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

lemma M12_moment_applyT:
  fixes T :: "real^2^2"
  assumes "transpose T *v c = c0_paper"
  shows "M12_moment (applyT T y) c
       = of_real ((T $ 1 $ 1) * (T $ 2 $ 1)) * M11_moment y c0_paper
       + of_real ((T $ 1 $ 1) * (T $ 2 $ 2) + (T $ 1 $ 2) * (T $ 2 $ 1)) * M12_moment y c0_paper
       + of_real ((T $ 1 $ 2) * (T $ 2 $ 2)) * M22_moment y c0_paper"
proof -
  \<comment> \<open>Abbreviate the four matrix entries as scalars: the pointwise \<open>key\<close>
      identity otherwise carries ~24 vec-nth occurrences and hangs elaboration
      at parse time (the *-overload graph noted at \<^const>\<open>w_M12\<close>).  With the
      entries named, it parses immediately.\<close>
  define t11 where "t11 = T $ 1 $ 1"
  define t12 where "t12 = T $ 1 $ 2"
  define t21 where "t21 = T $ 2 $ 1"
  define t22 where "t22 = T $ 2 $ 2"
  have key: "\<And>n.
       phase c (applyT T y) n * of_real (w_M12 (applyT T y $ n))
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22))"
  proof -
    fix n
    have ph: "phase c (applyT T y) n = phase c0_paper y n"
      by (rule phase_applyT[OF assms])
    have lin1: "(applyT T y $ n) $ 1 = t11 * (y $ n) $ 1 + t12 * (y $ n) $ 2"
      unfolding t11_def t12_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    have lin2: "(applyT T y $ n) $ 2 = t21 * (y $ n) $ 1 + t22 * (y $ n) $ 2"
      unfolding t21_def t22_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    show "phase c (applyT T y) n * of_real (w_M12 (applyT T y $ n))
       =
       phase c0_paper y n
         * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
         * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
         * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22))"
      using ph lin1 lin2
      by (simp add: w_M12_def of_real_add of_real_mult power2_eq_square algebra_simps)
  qed

  have sum_key:
    "(\<Sum>n\<in>UNIV. phase c (applyT T y) n * of_real (w_M12 (applyT T y $ n)))
     =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22)))"
  proof -
    have "(\<Sum>n\<in>UNIV. phase c (applyT T y) n * of_real (w_M12 (applyT T y $ n)))
       =
      (\<Sum>n\<in>UNIV.
         phase c0_paper y n
           * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
           * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
           * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22)))"
      by (rule sum.cong, rule refl, simp add: key)
    also have "\<dots> =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 1)\<^sup>2) * of_real (t11 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (y $ n)) * of_real (t11 * t22 + t12 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (((y $ n) $ 2)\<^sup>2) * of_real (t12 * t22)))"
      by (simp add: sum.distrib add.assoc)
    finally show ?thesis .
  qed

  show ?thesis
      unfolding M11_moment_def M12_moment_def M22_moment_def
      using sum_key[unfolded t11_def t12_def t21_def t22_def]
      by (simp add: sum_distrib_left algebra_simps power2_eq_square ac_simps)
qed


text \<open>\<^bold>\<open>[E] brick 4a: the vector moment law.\<close>  Bundling the six \<open>*_moment_applyT\<close>
  laws into one equation \<open>M_paper(applyT T y) c = L\<^sub>T (M_paper y c\<^sub>0)\<close>.  The four matrix
  entries are named \<open>a,b,p,q\<close> via \<^theory_text>\<open>defines\<close> so the explicit transported vector parses
  (a bare \<open>T$i$j\<close> form would carry ~16 vec-nth occurrences and hang elaboration).\<close>

lemma M_paper_applyT:
  fixes T :: "real^2^2" and a b p q :: real
  assumes Tc: "transpose T *v c = c0_paper"
  defines "a \<equiv> T $ 1 $ 1" and "b \<equiv> T $ 1 $ 2"
      and "p \<equiv> T $ 2 $ 1" and "q \<equiv> T $ 2 $ 2"
  shows "M_paper (applyT T y) c = vector
    [ A_moment y c0_paper,
      of_real a * M1_moment y c0_paper + of_real b * M2_moment y c0_paper,
      of_real p * M1_moment y c0_paper + of_real q * M2_moment y c0_paper,
      of_real (a\<^sup>2) * M11_moment y c0_paper
        + of_real (2 * a * b) * M12_moment y c0_paper
        + of_real (b\<^sup>2) * M22_moment y c0_paper,
      of_real (a * p) * M11_moment y c0_paper
        + of_real (a * q + b * p) * M12_moment y c0_paper
        + of_real (b * q) * M22_moment y c0_paper,
      of_real (p\<^sup>2) * M11_moment y c0_paper
        + of_real (2 * p * q) * M12_moment y c0_paper
        + of_real (q\<^sup>2) * M22_moment y c0_paper ]"
proof (subst Finite_Cartesian_Product.vec_eq_iff, intro allI)
  fix i :: 6
  consider "i = 1" | "i = 2" | "i = 3" | "i = 4" | "i = 5" | "i = 6"
    using exhaust_6 by metis
  then show "M_paper (applyT T y) c $ i =
      vector
        [ A_moment y c0_paper,
          of_real a * M1_moment y c0_paper + of_real b * M2_moment y c0_paper,
          of_real p * M1_moment y c0_paper + of_real q * M2_moment y c0_paper,
          of_real (a\<^sup>2) * M11_moment y c0_paper
            + of_real (2 * a * b) * M12_moment y c0_paper
            + of_real (b\<^sup>2) * M22_moment y c0_paper,
          of_real (a * p) * M11_moment y c0_paper
            + of_real (a * q + b * p) * M12_moment y c0_paper
            + of_real (b * q) * M22_moment y c0_paper,
          of_real (p\<^sup>2) * M11_moment y c0_paper
            + of_real (2 * p * q) * M12_moment y c0_paper
            + of_real (q\<^sup>2) * M22_moment y c0_paper ] $ i"
  proof cases
    case 1 then show ?thesis
      by (simp add: A_moment_applyT[OF Tc] vector_def)
  next
    case 2 then show ?thesis
      unfolding a_def b_def by (simp add: M1_moment_applyT[OF Tc] vector_def)
  next
    case 3 then show ?thesis
      unfolding p_def q_def by (simp add: M2_moment_applyT[OF Tc] vector_def)
  next
    case 4 then show ?thesis
      unfolding a_def b_def by (simp add: M11_moment_applyT[OF Tc] vector_def)
  next
    case 5 then show ?thesis
      unfolding a_def b_def p_def q_def
      by (simp add: M12_moment_applyT[OF Tc] vector_def)
  next
    case 6 then show ?thesis
      unfolding p_def q_def by (simp add: M22_moment_applyT[OF Tc] vector_def)
  qed
qed


text \<open>\<^bold>\<open>[E] brick 4b: the \<open>Sym\<^sup>2\<close> block is invertible.\<close>  The second-order transport
  block --- the \<open>3\<times>3\<close> matrix carrying \<open>(M\<^sub>1\<^sub>1, M\<^sub>1\<^sub>2, M\<^sub>2\<^sub>2)\<close> --- is the symmetric square
  of \<open>T = ((a,b),(p,q))\<close>.  Its determinant is \<open>(det T)\<^sup>3 = (aq - bp)\<^sup>3\<close>, so it is
  invertible exactly when \<open>T\<close> is.  This is the one genuinely nonlinear step of the
  steering transport.\<close>

definition Smat :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^3^3" where
  "Smat a b p q = vector
    [ vector [a\<^sup>2,    2 * a * b,      b\<^sup>2],
      vector [a * p,  a * q + b * p,  b * q],
      vector [p\<^sup>2,    2 * p * q,      q\<^sup>2] ]"

lemma det_Smat:
  "det (Smat a b p q) = (a * q - b * p) ^ 3"
  unfolding Smat_def
  by (simp add: det_3 vector_3 power2_eq_square power3_eq_cube algebra_simps)

lemma invertible_Smat:
  assumes "a * q - b * p \<noteq> 0"
  shows "invertible (Smat a b p q)"
proof -
  have "det (Smat a b p q) = (a * q - b * p) ^ 3" by (rule det_Smat)
  with assms have "det (Smat a b p q) \<noteq> 0" by simp
  thus ?thesis by (simp add: invertible_det_nz)
qed

text \<open>\<^bold>\<open>[E] brick 4b (complex block): the \<open>Sym\<^sup>2\<close> block over \<open>\<complex>\<close>.\<close>  The
  transport acts on the complex moment vector, so we need the \<open>3\<times>3\<close> symmetric-square
  block over \<open>\<complex>\<close>; its determinant is \<open>(of_real (det T))\<^sup>3\<close>, nonzero exactly when
  \<open>T\<close> is invertible.\<close>

definition Smat_c :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex^3^3" where
  "Smat_c a b p q = vector
    [ vector [of_real (a\<^sup>2),   of_real (2 * a * b),     of_real (b\<^sup>2)],
      vector [of_real (a * p), of_real (a * q + b * p), of_real (b * q)],
      vector [of_real (p\<^sup>2),   of_real (2 * p * q),     of_real (q\<^sup>2)] ]"

lemma det_Smat_c:
  "det (Smat_c a b p q) = (of_real (a * q - b * p)) ^ 3"
  unfolding Smat_c_def
  by (simp add: det_3 vector_3 of_real_power of_real_mult of_real_add of_real_diff
                power2_eq_square power3_eq_cube algebra_simps)

lemma invertible_Smat_c:
  assumes "a * q - b * p \<noteq> 0"
  shows "invertible (Smat_c a b p q)"
proof -
  have "det (Smat_c a b p q) = (of_real (a * q - b * p)) ^ 3"
    by (rule det_Smat_c)
  moreover have "(of_real (a * q - b * p) :: complex) \<noteq> 0"
    using assms by fastforce
  ultimately have "det (Smat_c a b p q) \<noteq> 0" by simp
  thus ?thesis by (simp add: invertible_det_nz)
qed


text \<open>\<^bold>\<open>[E] brick 4: the 6x6 steering-transport matrix \<open>L\<^sub>T = 1 \<oplus> T \<oplus> Sym\<^sup>2 T\<close>.\<close>
  Its explicit action (\<open>Lmat_apply\<close>) and the bridge from \<open>M_paper_applyT\<close>
  (\<open>M_paper_transport\<close>): \<open>M_paper(applyT T y) c = L\<^sub>T (M_paper y c\<^sub>0)\<close>.\<close>

definition Lmat :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex^6^6" where
  "Lmat a b p q = vector
    [ vector [1, 0, 0, 0, 0, 0],
      vector [0, of_real a, of_real b, 0, 0, 0],
      vector [0, of_real p, of_real q, 0, 0, 0],
      vector [0, 0, 0, of_real (a\<^sup>2),  of_real (2 * a * b),     of_real (b\<^sup>2)],
      vector [0, 0, 0, of_real (a * p), of_real (a * q + b * p), of_real (b * q)],
      vector [0, 0, 0, of_real (p\<^sup>2),  of_real (2 * p * q),     of_real (q\<^sup>2)] ]"

lemma Lmat_apply:
  "Lmat a b p q *v w = vector
    [ w $ 1,
      of_real a * w $ 2 + of_real b * w $ 3,
      of_real p * w $ 2 + of_real q * w $ 3,
      of_real (a\<^sup>2) * w $ 4 + of_real (2 * a * b) * w $ 5 + of_real (b\<^sup>2) * w $ 6,
      of_real (a * p) * w $ 4 + of_real (a * q + b * p) * w $ 5 + of_real (b * q) * w $ 6,
      of_real (p\<^sup>2) * w $ 4 + of_real (2 * p * q) * w $ 5 + of_real (q\<^sup>2) * w $ 6 ]"
  unfolding Finite_Cartesian_Product.vec_eq_iff
proof (intro allI)
  fix i :: 6
  show "(Lmat a b p q *v w) $ i =
    vector
    [ w $ 1,
      of_real a * w $ 2 + of_real b * w $ 3,
      of_real p * w $ 2 + of_real q * w $ 3,
      of_real (a\<^sup>2) * w $ 4 + of_real (2 * a * b) * w $ 5 + of_real (b\<^sup>2) * w $ 6,
      of_real (a * p) * w $ 4 + of_real (a * q + b * p) * w $ 5 + of_real (b * q) * w $ 6,
      of_real (p\<^sup>2) * w $ 4 + of_real (2 * p * q) * w $ 5 + of_real (q\<^sup>2) * w $ 6 ] $ i"
    using exhaust_6[of i]
    by (elim disjE; simp add: Lmat_def matrix_vector_mult_def sum_6)
qed

lemma M_paper_transport:
  fixes T :: "real^2^2"
  assumes Tc: "transpose T *v c = c0_paper"
  shows "M_paper (applyT T y) c
       = Lmat (T $ 1 $ 1) (T $ 1 $ 2) (T $ 2 $ 1) (T $ 2 $ 2) *v M_paper y c0_paper"
  by (simp add: M_paper_applyT[OF Tc] Lmat_apply)


text \<open>\<^bold>\<open>[E] brick 4b: the transport matrix is surjective.\<close>  By injectivity through
  the three blocks (1, then T via \<open>a q - b p \<noteq> 0\<close>, then \<open>Sym\<^sup>2 T\<close> via \<open>invertible_Smat_c\<close>);
  surjectivity then follows in finite dimension.  This is \<open>surj L\<^sub>T\<close>, what the transport
  of surjectivity (4d) needs.\<close>

lemma UNIV_3: "(UNIV::3 set) = {1,2,3}" using exhaust_3 by auto
lemma sum_3: "sum f (UNIV::3 set) = f 1 + f 2 + f 3" unfolding UNIV_3 by (simp add: ac_simps)

lemma surj_Lmat:
  assumes ne: "a * q - b * p \<noteq> 0"
  shows "surj ((*v) (Lmat a b p q))"
proof -
  have lin: "linear ((*v) (Lmat a b p q))" by (rule matrix_vector_mul_linear)
  have rne: "(of_real (a * q - b * p) :: complex) \<noteq> 0" using ne by fastforce
  have ker: "w = 0" if Z: "Lmat a b p q *v w = 0" for w :: "complex^6"
  proof -
    have V: "vector
      [ w $ 1, of_real a * w $ 2 + of_real b * w $ 3, of_real p * w $ 2 + of_real q * w $ 3,
        of_real (a\<^sup>2) * w $ 4 + of_real (2*a*b) * w $ 5 + of_real (b\<^sup>2) * w $ 6,
        of_real (a*p) * w $ 4 + of_real (a*q+b*p) * w $ 5 + of_real (b*q) * w $ 6,
        of_real (p\<^sup>2) * w $ 4 + of_real (2*p*q) * w $ 5 + of_real (q\<^sup>2) * w $ 6 ] = (0::complex^6)"
      using Z by (simp add: Lmat_apply)
    have e1: "w $ 1 = 0" using arg_cong[where f="\<lambda>v. v $ (1::6)", OF V] by simp
    have e2: "of_real a * w $ 2 + of_real b * w $ 3 = 0" using arg_cong[where f="\<lambda>v. v $ (2::6)", OF V] by simp
    have e3: "of_real p * w $ 2 + of_real q * w $ 3 = 0" using arg_cong[where f="\<lambda>v. v $ (3::6)", OF V] by simp
    have e4: "of_real (a\<^sup>2) * w $ 4 + of_real (2*a*b) * w $ 5 + of_real (b\<^sup>2) * w $ 6 = 0" using arg_cong[where f="\<lambda>v. v $ (4::6)", OF V] by simp
    have e5: "of_real (a*p) * w $ 4 + of_real (a*q+b*p) * w $ 5 + of_real (b*q) * w $ 6 = 0" using arg_cong[where f="\<lambda>v. v $ (5::6)", OF V] by simp
    have e6: "of_real (p\<^sup>2) * w $ 4 + of_real (2*p*q) * w $ 5 + of_real (q\<^sup>2) * w $ 6 = 0" using arg_cong[where f="\<lambda>v. v $ (6::6)", OF V] by simp
    have w2: "w $ 2 = 0"
    proof -
      have "of_real (a*q-b*p) * w $ 2 = of_real q * (of_real a * w $ 2 + of_real b * w $ 3) - of_real b * (of_real p * w $ 2 + of_real q * w $ 3)"
        by (simp add: of_real_diff of_real_mult algebra_simps)
      also have "... = 0" using e2 e3 by simp
      finally show ?thesis using rne by simp
    qed
    have w3: "w $ 3 = 0"
    proof -
      have "of_real (a*q-b*p) * w $ 3 = of_real a * (of_real p * w $ 2 + of_real q * w $ 3) - of_real p * (of_real a * w $ 2 + of_real b * w $ 3)"
        by (simp add: of_real_diff of_real_mult algebra_simps)
      also have "... = 0" using e2 e3 by simp
      finally show ?thesis using rne by simp
    qed
    have Sz: "Smat_c a b p q *v (vector [w$4, w$5, w$6] :: complex^3) = 0"
      unfolding Finite_Cartesian_Product.vec_eq_iff
    proof (intro allI)
      fix i :: 3
      show "(Smat_c a b p q *v (vector [w$4, w$5, w$6])) $ i = (0::complex^3) $ i"
        using exhaust_3[of i] e4 e5 e6
        by (elim disjE; simp add: Smat_c_def matrix_vector_mult_def sum_3 algebra_simps)
    qed
    have z3: "(vector [w$4, w$5, w$6] :: complex^3) = 0"
    proof -
      obtain B :: "complex^3^3" where B: "B ** Smat_c a b p q = mat 1"
        using invertible_Smat_c[OF ne] unfolding invertible_def by blast
      have "(vector [w$4, w$5, w$6] :: complex^3) = (B ** Smat_c a b p q) *v vector [w$4, w$5, w$6]"
        by (simp add: B matrix_vector_mul_lid)
      also have "... = B *v (Smat_c a b p q *v vector [w$4, w$5, w$6])"
        by (simp add: matrix_vector_mul_assoc[symmetric])
      also have "... = B *v 0" using Sz by simp
      also have "... = 0" by (simp add: matrix_vector_mult_0)
      finally show ?thesis .
    qed
    have w4: "w$4 = 0" using arg_cong[where f="\<lambda>v. v $ (1::3)", OF z3] by simp
    have w5: "w$5 = 0" using arg_cong[where f="\<lambda>v. v $ (2::3)", OF z3] by simp
    have w6: "w$6 = 0" using arg_cong[where f="\<lambda>v. v $ (3::3)", OF z3] by simp
    show "w = 0" using e1 w2 w3 w4 w5 w6 by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_6)
  qed
  have inj: "inj ((*v) (Lmat a b p q))" using lin ker by (simp add: linear_injective_0)
  show ?thesis using lin inj by (metis linear_injective_imp_surjective)
qed



text \<open>\<^bold>\<open>[E] brick 4c support:\<close> the per-point transport \<open>applyT T\<close> is linear, and
  surjective when \<open>T\<close> is invertible (an explicit right inverse \<open>applyT B\<close>).\<close>

lemma applyT_linear: "linear (applyT T)"
proof (rule linearI)
  have l: "linear ((*v) T)" by (rule matrix_vector_mul_linear)
  show "applyT T (x + y) = applyT T x + applyT T y" for x y :: "(real^2)^'n"
    by (simp add: applyT_def Finite_Cartesian_Product.vec_eq_iff vector_add_component linear_add[OF l])
  show "applyT T (r *\<^sub>R x) = r *\<^sub>R applyT T x" for r and x :: "(real^2)^'n"
    by (simp add: applyT_def Finite_Cartesian_Product.vec_eq_iff vector_scaleR_component linear_cmul[OF l])
qed

lemma applyT_surj:
  assumes "invertible T" shows "surj (applyT T :: (real^2)^'n \<Rightarrow> _)"
proof -
  obtain B :: "real^2^2" where B: "T ** B = mat 1"
    using assms unfolding invertible_def by blast
  have "applyT T (applyT B z) = z" for z :: "(real^2)^'n"
    by (simp add: applyT_def Finite_Cartesian_Product.vec_eq_iff matrix_vector_mul_assoc B matrix_vector_mul_lid)
  thus ?thesis by (metis surjI)
qed



text \<open>\<^bold>\<open>[E] brick 4c: transport of surjectivity\<close> from \<open>c\<^sub>0\<close> to any \<open>c \<noteq> 0\<close>.
  Differentiate \<open>M_paper_transport\<close> on both sides; \<open>has_derivative_unique\<close> gives
  \<open>DM_paper_x (applyT T y\<^sub>0) c \<circ> applyT T = L\<^sub>T \<circ> DM_paper_x y\<^sub>0 c\<^sub>0\<close>; the RHS is surjective
  (\<open>surj_Lmat\<close> \<open>\<circ>\<close> reg), and \<open>applyT T\<close> is surjective, so the first factor is surjective.\<close>

lemma DM_paper_x_surj_transport:
  fixes T :: "real^2^2" and c :: planar and y0 :: "(real^2)^'n"
  assumes Tinv: "invertible T" and Tc: "transpose T *v c = c0_paper"
      and reg: "surj (DM_paper_x y0 c0_paper)"
  shows "surj (DM_paper_x (applyT T y0) c)"
proof -
  define L where "L \<equiv> (\<lambda>v::complex^6. Lmat (T$1$1) (T$1$2) (T$2$1) (T$2$2) *v v)"
  have Llin: "linear L" unfolding L_def by (rule matrix_vector_mul_linear)
  have hd_f: "(applyT T has_derivative applyT T) (at y0)"
    by (rule linear_imp_has_derivative[OF applyT_linear])
  have hd_g: "((\<lambda>z. M_paper z c) has_derivative DM_paper_x (applyT T y0) c) (at (applyT T y0))"
    using has_derivative_M_paper_x[where x="applyT T y0" and c=c and V=UNIV] by simp
  have d1: "((\<lambda>y. M_paper (applyT T y) c) has_derivative (DM_paper_x (applyT T y0) c \<circ> applyT T)) (at y0)"
    using diff_chain_at[OF hd_f hd_g] by (simp add: o_def)
  have hd_g0: "((\<lambda>y. M_paper y c0_paper) has_derivative DM_paper_x y0 c0_paper) (at y0)"
    using has_derivative_M_paper_x[where x=y0 and c=c0_paper and V=UNIV] by simp
  have hd_L: "(L has_derivative L) (at (M_paper y0 c0_paper))"
    by (rule linear_imp_has_derivative[OF Llin])
  have d2: "((\<lambda>y. L (M_paper y c0_paper)) has_derivative (L \<circ> DM_paper_x y0 c0_paper)) (at y0)"
    using diff_chain_at[OF hd_g0 hd_L] by (simp add: o_def)
  have feq: "(\<lambda>y. M_paper (applyT T y) c) = (\<lambda>y. L (M_paper y c0_paper))"
    by (simp add: L_def fun_eq_iff M_paper_transport[OF Tc])
  have d2': "((\<lambda>y. M_paper (applyT T y) c) has_derivative (L \<circ> DM_paper_x y0 c0_paper)) (at y0)"
    unfolding feq by (rule d2)
  have Deq: "DM_paper_x (applyT T y0) c \<circ> applyT T = L \<circ> DM_paper_x y0 c0_paper"
    by (rule has_derivative_unique[OF d1 d2'])
  have sL: "surj L"
  proof -
    have ne: "T$1$1 * T$2$2 - T$1$2 * T$2$1 \<noteq> 0" using Tinv by (simp add: invertible_det_nz det_2)
    have "surj ((*v) (Lmat (T$1$1) (T$1$2) (T$2$1) (T$2$2)))" by (rule surj_Lmat[OF ne])
    thus ?thesis by (simp add: L_def)
  qed
  have "surj (L \<circ> DM_paper_x y0 c0_paper)" using reg sL by (rule comp_surj)
  hence "surj (DM_paper_x (applyT T y0) c \<circ> applyT T)" using Deq by simp
  thus "surj (DM_paper_x (applyT T y0) c)" by (metis comp_apply surjD surjI)
qed



text \<open>\<^bold>\<open>[E] brick 5 + closure.\<close>  Lift the dim-6 regular point at \<open>c\<^sub>0\<close> to any
  \<open>CARD(n) \<ge> 6\<close> (embed via an injection \<open>6 \<hookrightarrow> n\<close>, off-image points harmless since
  every summand is linear in \<open>h$n\<close>), then transport to any \<open>c \<noteq> 0\<close>.\<close>

lemma sum_reindex_embed:
  fixes \<iota> :: "6 \<Rightarrow> 'm::finite" and g :: "'m \<Rightarrow> 'a::comm_monoid_add"
  assumes inj: "inj \<iota>" and van: "\<And>n. n \<notin> range \<iota> \<Longrightarrow> g n = 0"
  shows "(\<Sum>n\<in>UNIV. g n) = (\<Sum>k\<in>UNIV. g (\<iota> k))"
proof -
  have "(\<Sum>n\<in>(UNIV::'m set). g n) = (\<Sum>n\<in>range \<iota>. g n)"
    by (rule sum.mono_neutral_right[OF finite_class.finite_UNIV subset_UNIV]) (simp add: van)
  also have "(\<Sum>n\<in>range \<iota>. g n) = (\<Sum>k\<in>(UNIV::6 set). (g \<circ> \<iota>) k)"
    by (rule sum.reindex[OF inj])
  also have "(\<Sum>k\<in>(UNIV::6 set). (g \<circ> \<iota>) k) = (\<Sum>k\<in>(UNIV::6 set). g (\<iota> k))"
    by (simp only: o_def)
  finally show ?thesis .
qed

lemma DM_paper_x_regular_point_c0_gen:
  assumes c6: "6 \<le> CARD('n)"
  shows "\<exists>y0::(real^2)^'n. surj (DM_paper_x y0 c0_paper)"
proof -
  obtain x0 :: "(real^2)^6" where reg6: "surj (DM_paper_x x0 c0_paper)"
    using DM_paper_x_regular_point_c0 by blast
  have c: "card (UNIV::6 set) \<le> card (UNIV::'n set)" using c6 by simp
  obtain \<iota> :: "6 \<Rightarrow> 'n" where inj\<iota>: "inj \<iota>"
    using card_le_inj[OF finite_class.finite_UNIV finite_class.finite_UNIV c] by (auto simp: inj_def)
  define xf :: "6 \<Rightarrow> real^2" where "xf = vec_nth x0"
  define y0 :: "(real^2)^'n" where "y0 = vec_lambda (\<lambda>n. if n \<in> range \<iota> then xf (inv_into (UNIV::6 set) \<iota> n) else (0::real^2))"
  have y0v: "\<And>k. y0 $ (\<iota> k) = x0 $ k" by (simp add: y0_def xf_def inv_f_f[OF inj\<iota>])
  have y0z: "\<And>n. n \<notin> range \<iota> \<Longrightarrow> y0 $ n = 0" by (simp add: y0_def)
  have "surj (DM_paper_x y0 c0_paper)"
    unfolding surj_def
  proof (rule allI)
    fix z :: "complex^6"
    obtain h0 :: "(real^2)^6" where h0: "z = DM_paper_x x0 c0_paper h0"
      using reg6 by (auto simp: surj_def)
    define hf :: "6 \<Rightarrow> real^2" where "hf = vec_nth h0"
    define h :: "(real^2)^'n" where "h = vec_lambda (\<lambda>n. if n \<in> range \<iota> then hf (inv_into (UNIV::6 set) \<iota> n) else (0::real^2))"
    have hv: "\<And>k. h $ (\<iota> k) = h0 $ k" by (simp add: h_def hf_def inv_f_f[OF inj\<iota>])
    have hz: "\<And>n. n \<notin> range \<iota> \<Longrightarrow> h $ n = 0" by (simp add: h_def)
    have cA: "d_A_moment_x y0 c0_paper h = d_A_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). d_phase c0_paper y0 h n) = (\<Sum>k\<in>(UNIV::6 set). d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_A_moment_x_def)
    qed
    have cM1: "d_M1_moment_x y0 c0_paper h = d_M1_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real ((h$n)$1) * phase c0_paper y0 n + of_real ((y0$n)$1) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real ((h$(\<iota> k))$1) * phase c0_paper y0 (\<iota> k) + of_real ((y0$(\<iota> k))$1) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real ((h0$k)$1) * phase c0_paper x0 k + of_real ((x0$k)$1) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M1_moment_x_def)
    qed
    have cM2: "d_M2_moment_x y0 c0_paper h = d_M2_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real ((h$n)$2) * phase c0_paper y0 n + of_real ((y0$n)$2) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real ((h$(\<iota> k))$2) * phase c0_paper y0 (\<iota> k) + of_real ((y0$(\<iota> k))$2) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real ((h0$k)$2) * phase c0_paper x0 k + of_real ((x0$k)$2) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M2_moment_x_def)
    qed
    have cM11: "d_M11_moment_x y0 c0_paper h = d_M11_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real (2 * ((y0$n)$1) * ((h$n)$1)) * phase c0_paper y0 n + of_real (((y0$n)$1)\<^sup>2) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real (2 * ((y0$(\<iota> k))$1) * ((h$(\<iota> k))$1)) * phase c0_paper y0 (\<iota> k) + of_real (((y0$(\<iota> k))$1)\<^sup>2) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real (2 * ((x0$k)$1) * ((h0$k)$1)) * phase c0_paper x0 k + of_real (((x0$k)$1)\<^sup>2) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M11_moment_x_def)
    qed
    have cM12: "d_M12_moment_x y0 c0_paper h = d_M12_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real (dw_M12 (y0$n) (h$n)) * phase c0_paper y0 n + of_real (w_M12 (y0$n)) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real (dw_M12 (y0$(\<iota> k)) (h$(\<iota> k))) * phase c0_paper y0 (\<iota> k) + of_real (w_M12 (y0$(\<iota> k))) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def dw_M12_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real (dw_M12 (x0$k) (h0$k)) * phase c0_paper x0 k + of_real (w_M12 (x0$k)) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M12_moment_x_def)
    qed
    have cM22: "d_M22_moment_x y0 c0_paper h = d_M22_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real (2 * ((y0$n)$2) * ((h$n)$2)) * phase c0_paper y0 n + of_real (((y0$n)$2)\<^sup>2) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real (2 * ((y0$(\<iota> k))$2) * ((h$(\<iota> k))$2)) * phase c0_paper y0 (\<iota> k) + of_real (((y0$(\<iota> k))$2)\<^sup>2) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real (2 * ((x0$k)$2) * ((h0$k)$2)) * phase c0_paper x0 k + of_real (((x0$k)$2)\<^sup>2) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M22_moment_x_def)
    qed
    have key: "DM_paper_x y0 c0_paper h = DM_paper_x x0 c0_paper h0"
      unfolding Finite_Cartesian_Product.vec_eq_iff
    proof (intro allI)
      fix k :: 6
      show "DM_paper_x y0 c0_paper h $ k = DM_paper_x x0 c0_paper h0 $ k"
        using exhaust_6[of k]
        by (simp add: DM_paper_x_eq_MM Moment_Map.DM_paper_x_def cA cM1 cM11 cM12 cM2 cM22)
    qed
    show "\<exists>h'. z = DM_paper_x y0 c0_paper h'" using key h0 by metis
  qed
  thus ?thesis by blast
qed


lemma DM_paper_x_regular_point_exists:
  fixes c :: planar
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x0::(real^2)^'n. surj (DM_paper_x x0 c)"
proof -
  obtain T where T: "invertible T" "transpose T *v c = c0_paper"
    using steering_transport_exists[OF assms(1)] by blast
  obtain y0 :: "(real^2)^'n" where y0: "surj (DM_paper_x y0 c0_paper)"
    using DM_paper_x_regular_point_c0_gen[OF assms(2)] by blast
  have "surj (DM_paper_x (applyT T y0) c)" using DM_paper_x_surj_transport[OF T(1) T(2) y0] .
  thus ?thesis by blast
qed

text \<open>\<^bold>\<open>(M2) Open-dense submersion at a fixed nonzero wavevector.\<close>  From one regular point (M1) plus
  lower semicontinuity of rank (the rank-semicontinuity tool was deleted as dead code; this is
  delivered sorry-free by the \<open>mstarg\<close> machinery below), the moment-map derivative is surjective on an open dense subset of any open
  \<open>V\<close>.  This is the general-wavevector analogue of \<open>DM_paper_open_dense_surjective\<close>.\<close>

text \<open>\<^bold>\<open>[E]/[F] sound open-dense machinery (in progress).\<close>  The general-n analogue of
  the dim-6 \<open>m_star\<close>: \<open>mstarg c x = det (matrix (G x c))\<close> with the codomain Gram
  \<open>G = (transC \<circ> DM_paper_x x c) \<circ> adjoint (\<dots>) :: real^12 \<Rightarrow> real^12\<close> (no flattening; \<open>transC\<close>
  is the fixed iso).  \<open>surj (DM_paper_x x c) \<longleftrightarrow> mstarg c x \<noteq> 0\<close>, continuous, and (TODO)
  entire-along-lines + nonzero \<Rightarrow> nowhere-dense zeros \<Rightarrow> a rank-semicont-free [F].\<close>

lemma surj_iff_gram_invertible:
  fixes A :: "'a::euclidean_space \<Rightarrow> (real^'m)"
  assumes lin: "linear A"
  shows "surj A \<longleftrightarrow> invertible (matrix (A \<circ> adjoint A))"
proof -
  have linAd: "linear (adjoint A)" by (rule adjoint_linear[OF lin])
  have linG: "linear (A \<circ> adjoint A)" using lin linAd by (subst linear_compose, auto)
  show ?thesis
  proof
    assume surjA: "surj A"
    have inj_adj: "inj (adjoint A)"
      unfolding linear_injective_0[OF linAd]
    proof (intro allI impI)
      fix y assume z: "adjoint A y = 0"
      obtain x where x: "A x = y" using surjA by (metis surjD)
      have "inner y y = inner (A x) y" using x by simp
      also have "\<dots> = inner x (adjoint A y)" by (simp add: adjoint_works[OF lin])
      also have "\<dots> = 0" using z by simp
      finally have "inner y y = 0" .
      thus "y = 0" by simp
    qed
    have inj_G: "inj (A \<circ> adjoint A)"
      unfolding linear_injective_0[OF linG]
    proof (intro allI impI)
      fix y assume z: "(A \<circ> adjoint A) y = 0"
      have "inner ((A \<circ> adjoint A) y) y = inner (adjoint A y) (adjoint A y)"
        by (simp add: o_def adjoint_works[OF lin])
      hence "inner (adjoint A y) (adjoint A y) = 0" using z by simp
      hence "adjoint A y = 0" by simp
      thus "y = 0" using inj_adj linAd by (metis linear_injective_0)
    qed
    thus "invertible (matrix (A \<circ> adjoint A))"
      by (metis det_nz_iff_inj[OF linG] invertible_det_nz)
  next
    assume invG: "invertible (matrix (A \<circ> adjoint A))"
    have "inj (A \<circ> adjoint A)" by (metis invG det_nz_iff_inj[OF linG] invertible_det_nz)
    hence "surj (A \<circ> adjoint A)" using linG by (metis linear_injective_imp_surjective)
    thus "surj A" by (metis comp_apply surjD surjI)
  qed
qed

definition mstarg :: "planar \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

lemma linear_DM_paper_x: "linear (DM_paper_x x c)"
  by (metis has_derivative_M_paper_x has_derivative_bounded_linear bounded_linear.linear)

lemma surj_iff_mstarg: "surj (DM_paper_x x c) \<longleftrightarrow> mstarg c x \<noteq> 0"
proof -
  have lTDF: "linear (transC \<circ> DM_paper_x x c)"
    by (intro linear_compose linear_transC linear_DM_paper_x)
  have seq: "surj (DM_paper_x x c) \<longleftrightarrow> surj (transC \<circ> DM_paper_x x c)"
  proof
    assume "surj (DM_paper_x x c)"
    thus "surj (transC \<circ> DM_paper_x x c)" using surj_transC comp_surj by blast
  next
    assume s: "surj (transC \<circ> DM_paper_x x c)"
    have "surj (transC_inv \<circ> (transC \<circ> DM_paper_x x c))"
      using s surj_transC_inv comp_surj by blast
    moreover have "transC_inv \<circ> (transC \<circ> DM_paper_x x c) = DM_paper_x x c"
      by (rule ext) (simp add: transC_inv_left)
    ultimately show "surj (DM_paper_x x c)" by simp
  qed
  show ?thesis
    unfolding mstarg_def
    using seq surj_iff_gram_invertible[OF lTDF] invertible_det_nz by blast
qed

lemma matrix_gram_entry:
  "vec_nth (vec_nth (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c))) i) j
   = (\<Sum>e\<in>Basis. vec_nth (transC (DM_paper_x x c e)) j * vec_nth (transC (DM_paper_x x c e)) i)"
proof -
  define B where "B = transC \<circ> DM_paper_x x c"
  have lB: "linear B" unfolding B_def by (intro linear_compose linear_transC linear_DM_paper_x)
  have key: "inner (adjoint B (axis k (1::real))) e = vec_nth (B e) k"
    for k :: 12 and e
  proof -
    have "inner (adjoint B (axis k (1::real))) e = inner e (adjoint B (axis k (1::real)))"
      by (rule inner_commute)
    also have "\<dots> = inner (B e) (axis k (1::real))" by (rule adjoint_works[OF lB])
    also have "\<dots> = vec_nth (B e) k" by (simp add: inner_axis)
    finally show ?thesis .
  qed
  have "vec_nth (vec_nth (matrix (B \<circ> adjoint B)) i) j = vec_nth (B (adjoint B (axis j (1::real)))) i"
    by (simp add: matrix_def o_def)
  also have "\<dots> = inner (B (adjoint B (axis j (1::real)))) (axis i (1::real))"
    by (simp add: inner_axis)
  also have "\<dots> = inner (adjoint B (axis j (1::real))) (adjoint B (axis i (1::real)))"
    by (simp add: adjoint_works[OF lB])
  also have "\<dots> = (\<Sum>e\<in>Basis. inner (adjoint B (axis j (1::real))) e * inner (adjoint B (axis i (1::real))) e)"
    by (rule euclidean_inner)
  also have "\<dots> = (\<Sum>e\<in>Basis. vec_nth (B e) j * vec_nth (B e) i)" by (simp add: key)
  finally show ?thesis by (simp add: B_def o_def)
qed

lemma cont_transC_DM_entry:
  "continuous_on UNIV (\<lambda>x. vec_nth (transC (DM_paper_x x c e)) k)"
proof -
  have "continuous_on UNIV (\<lambda>x. DM_paper_x x c e)"
   by (simp add: DM_paper_x_eq_MM continuous_on_DM_paper_x_vec)
  hence "continuous_on UNIV (\<lambda>x. transC (DM_paper_x x c e))"
    by (rule bounded_linear.continuous_on[OF bounded_linear_transC])
  thus ?thesis by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
qed

lemma cont_matrix_G_entry:
  "continuous_on UNIV
     (\<lambda>x. vec_nth (vec_nth (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c))) i) j)"
proof -
  have "continuous_on UNIV
          (\<lambda>x. \<Sum>e\<in>Basis. vec_nth (transC (DM_paper_x x c e)) j * vec_nth (transC (DM_paper_x x c e)) i)"
    by (intro continuous_on_sum continuous_on_mult cont_transC_DM_entry)
  thus ?thesis by (simp add: matrix_gram_entry)
qed

lemma cont_mstarg: "continuous_on UNIV (\<lambda>x. mstarg c x)"
  unfolding mstarg_def by (rule continuous_on_det_fun) (rule cont_matrix_G_entry)


text \<open>\<^bold>\<open>[E]/[F] cont.\<close>  Entire-along-lines + nonzero \<Rightarrow> nowhere-dense zeros of mstarg.\<close>

lemma bl_neg_inner_gen: "bounded_linear (\<lambda>x::(real^2)^'n. - (c \<bullet> (x $ n)))"
  by (intro bounded_linear_minus bounded_linear_compose[OF bounded_linear_inner_right bounded_linear_vec_nth])

lemma cline_entire_phase_gen: "cline_entire (\<lambda>x::(real^2)^'n. phase c x n)"
  unfolding phase_def by (rule cline_entire_cis_linear[OF bl_neg_inner_gen])

lemma cline_entire_dphase_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_phase c x h n)"
proof -
  have "cline_entire (\<lambda>x::(real^2)^'n.
          complex_of_real (- (c \<bullet> (h $ n))) * (\<i> * cis (- (c \<bullet> (x $ n)))))"
    by (intro cline_entire_mult cline_entire_const cline_entire_cis_linear[OF bl_neg_inner_gen])
  thus ?thesis unfolding d_phase_def by (simp add: scaleR_conv_of_real)
qed

lemmas moment_cline_intros_gen =
  cline_entire_sum cline_entire_add cline_entire_mult cline_entire_const
  cline_entire_phase_gen cline_entire_dphase_gen cline_entire_of_real_rline
  rline_entire_coord rline_entire_const rline_entire_add rline_entire_mult rline_entire_scale

lemma cline_entire_dA_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_A_moment_x x c h)"
  unfolding d_A_moment_x_def by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM1_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M1_moment_x x c h)"
  unfolding d_M1_moment_x_def by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM2_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M2_moment_x x c h)"
  unfolding d_M2_moment_x_def by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM11_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M11_moment_x x c h)"
  unfolding d_M11_moment_x_def power2_eq_square by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM12_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M12_moment_x x c h)"
  unfolding d_M12_moment_x_def w_M12_def dw_M12_def by (intro moment_cline_intros_gen) simp
lemma cline_entire_dM22_gen: "cline_entire (\<lambda>x::(real^2)^'n. d_M22_moment_x x c h)"
  unfolding d_M22_moment_x_def power2_eq_square by (intro moment_cline_intros_gen) simp

lemma cline_entire_DM_comp_gen: "cline_entire (\<lambda>x::(real^2)^'n. DM_paper_x x c h $ m)"
proof -
  from exhaust_6[of m] consider (m1) "m=(1::6)" | (m2) "m=(2::6)" | (m3) "m=(3::6)"
    | (m4) "m=(4::6)" | (m5) "m=(5::6)" | (m6) "m=(6::6)" by blast
  then show ?thesis
  proof cases
    case m1 then show ?thesis
      by (metis (no_types, lifting) ext DA_paper_x_def DM_paper_x_components(1) cline_entire_dA_gen d_A_moment_x_def)
  next
    case m2 then show ?thesis
      by (metis (no_types, lifting) ext DM1_paper_x_def DM_paper_x_components(2) cline_entire_dM1_gen d_M1_moment_x_def)
  next
    case m3 then show ?thesis
      by (metis (no_types, lifting) ext DM2_paper_x_def DM_paper_x_components(3) cline_entire_dM2_gen d_M2_moment_x_def)
  next
    case m4 then show ?thesis
      by (metis (no_types, lifting) ext DM11_paper_x_def DM_paper_x_components(4) cline_entire_dM11_gen d_M11_moment_x_def)
  next
    case m5 then show ?thesis
      by (metis (no_types, lifting) DM12_paper_x_def DM_paper_x_components(5) cline_entire_dM12_gen cline_entire_def d_M12_moment_x_def)
  next
    case m6 then show ?thesis
      by (metis (no_types, lifting) ext DM22_paper_x_def DM_paper_x_components(6) cline_entire_dM22_gen d_M22_moment_x_def)
  qed
qed

lemma rline_entire_transC_comp_gen:
  fixes w :: "(real^2)^'n \<Rightarrow> complex^6" and i :: 12
  assumes "\<And>m. cline_entire (\<lambda>x. w x $ m)"
  shows "rline_entire (\<lambda>x. vec_nth (transC (w x)) i)"
  using exhaust_12[of i]
  by (elim disjE)
     (simp_all add: transC_def rline_entire_Re[OF assms] rline_entire_Im[OF assms])

lemma rline_entire_transC_DM:
  "rline_entire (\<lambda>x::(real^2)^'n. vec_nth (transC (DM_paper_x x c e)) k)"
  by (rule rline_entire_transC_comp_gen[OF cline_entire_DM_comp_gen])

lemma rline_entire_matrix_G_entry:
  "rline_entire
     (\<lambda>x::(real^2)^'n. vec_nth (vec_nth (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c))) i) j)"
proof -
  have "rline_entire
          (\<lambda>x::(real^2)^'n. \<Sum>e\<in>Basis. vec_nth (transC (DM_paper_x x c e)) j * vec_nth (transC (DM_paper_x x c e)) i)"
    by (auto intro!: rline_entire_sum rline_entire_mult rline_entire_transC_DM)
  thus ?thesis by (simp add: matrix_gram_entry)
qed

lemma rline_entire_mstarg: "rline_entire (\<lambda>x::(real^2)^'n. mstarg c x)"
  unfolding mstarg_def by (rule rline_entire_det_fun) (rule rline_entire_matrix_G_entry)

lemma mstarg_nonzero:
  assumes "c \<noteq> 0" and "6 \<le> CARD('n)"
  shows "\<exists>x::(real^2)^'n. mstarg c x \<noteq> 0"
proof -
  obtain x0 :: "(real^2)^'n" where "surj (DM_paper_x x0 c)"
    using DM_paper_x_regular_point_exists[OF assms] by blast
  thus ?thesis using surj_iff_mstarg by blast
qed

lemma nowhere_dense_mstarg_zeros:
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. mstarg c x = 0}"
proof -
  have lines: "\<exists>F. F holomorphic_on UNIV
                  \<and> (\<forall>t. F (complex_of_real t) = complex_of_real (mstarg c (a + t *\<^sub>R v)))" for a v
    using rline_entire_mstarg unfolding rline_entire_def by blast
  have "nowhere_dense {x::(real^2)^'n \<in> UNIV. mstarg c x = 0}"
    by (rule lines_entire_slice_nowhere_dense[OF cont_mstarg lines]) (use mstarg_nonzero[OF c0 n6] in blast)
  thus ?thesis by simp
qed


lemma DM_paper_x_open_dense_surjective_gen:
  fixes V :: "((real^2)^'n) set" and c :: planar
  assumes V_open: "open V" and V_ne: "V \<noteq> {}" and N_ge_6: "6 \<le> CARD('n)" and c_ne: "c \<noteq> 0"
  shows "\<exists>U. open U \<and> U \<subseteq> V \<and> V \<subseteq> closure U \<and> (\<forall>x\<in>U. surj (DM_paper_x x c))"
proof (intro exI[of _ "V \<inter> {x::(real^2)^'n. mstarg c x \<noteq> 0}"] conjI)
  show "open (V \<inter> {x. mstarg c x \<noteq> 0})"
    using V_open open_Collect_neq[OF cont_mstarg continuous_on_const] by blast
  show "V \<inter> {x. mstarg c x \<noteq> 0} \<subseteq> V" by blast
  have cl0: "closed {x::(real^2)^'n. mstarg c x = 0}"
    by (rule closed_Collect_eq[OF cont_mstarg continuous_on_const])
  have int0: "interior {x::(real^2)^'n. mstarg c x = 0} = {}"
    using nowhere_dense_mstarg_zeros[OF c_ne N_ge_6] cl0 by (simp only: nowhere_dense_def closure_closed)
  have dense: "closure {x::(real^2)^'n. mstarg c x \<noteq> 0} = UNIV"
    by (simp add: Collect_neg_eq closure_complement int0)
  show "V \<subseteq> closure (V \<inter> {x. mstarg c x \<noteq> 0})"
    using open_Int_closure_subset[OF V_open, of "{x. mstarg c x \<noteq> 0}"] dense by simp
  show "\<forall>x\<in>V \<inter> {x. mstarg c x \<noteq> 0}. surj (DM_paper_x x c)"
    by (auto simp: surj_iff_mstarg)
qed


text \<open>\<^bold>\<open>(M3) The steering-singular angle locus is nowhere dense.\<close>  \<open>Dcvec_dip\<close> is real-analytic in
  \<open>\<omega>\<close> and not everywhere singular, so its singular set is a proper analytic subset --- closed with
  empty interior.\<close>

lemma Dcvec_det_eq:
    fixes \<omega>0 \<omega>s \<omega> :: "real^2"
    shows "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
           = sin (\<omega>$1) * (cos (\<omega>$1)
               - sin (\<omega>$1) * (((kx \<omega>0 - kx
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * cos (\<omega>$2)
                            + ((ky \<omega>0 - ky \<omega>s)/(kz
  \<omega>s - kz \<omega>0)) * sin (\<omega>$2)))"
proof -
  have "cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (cos (\<omega> $h 2) * cos (\<omega> $h 2))) + 
           (cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (sin (\<omega> $h 2) * sin (\<omega> $h 2))) + 
           ((kx \<omega>0 * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2))) - 
             kx \<omega>s * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2)))) / 
            (kz \<omega>s - kz \<omega>0) + (kx \<omega>s * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2))) - 
             kx \<omega>0 * (sin (\<omega> $h 1) * (sin (\<omega> $h 1) * cos (\<omega> $h 2)))) / (kz \<omega>s - kz \<omega>0))) =
       cos (\<omega> $h 1) * (sin (\<omega> $h 1) * (cos (\<omega> $h 2) * cos (\<omega> $h 2) + sin (\<omega> $h 2) * sin (\<omega> $h 2)))"
    by argo
  then show ?thesis
    by (simp add: det_2 matrix_def Dcvec_dip_def axis_def sin_cos_squared_add[of "\<omega>$2"]
  algebra_simps)
qed

lemma pythagorean_squared:
  fixes m :: real
  shows
    "cos m * (cos m * (cos m * cos m))
      + (sin m * (sin m * (sin m * sin m))
      + cos m * (cos m * (sin m * (sin m * 2)))) = 1"
proof -
  let ?c = "cos m"
  let ?s = "sin m"

  have cs: "?c * ?c + ?s * ?s = 1"
    using sin_cos_squared_add[of m]
    by (simp add: power2_eq_square add.commute)

  have
    "?c * (?c * (?c * ?c))
      + (?s * (?s * (?s * ?s))
      + ?c * (?c * (?s * (?s * 2))))
     = (?c * ?c + ?s * ?s) * (?c * ?c + ?s * ?s)"
    by (smt (verit, del_insts) Groups.mult_ac(2) ab_semigroup_mult_class.mult_ac(1) 
        mult_2 mult_hom.hom_add)
  also have "... = 1"
    using cs by simp
  finally show ?thesis.
qed

lemma sin_cos_lin_not_const0:
    fixes M a b :: real
    assumes ab: "a < b"
    shows "\<exists>s. a < s \<and> s < b \<and> sin s * (cos s -
  sin s * M) \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence Z: "\<And>s. a < s \<Longrightarrow> s < b
  \<Longrightarrow> sin s * (cos s - sin s * M) = 0" by auto
    define F  where "F  = (\<lambda>s::real. sin s * (cos s - sin s
  * M))"
    define F1 where "F1 = (\<lambda>s::real. (cos s * cos s - sin s
  * sin s) - M * (2 * sin s * cos s))"
    define F2 where "F2 = (\<lambda>s::real. - (4 * (sin s * cos
  s)) - M * (2 * (cos s * cos s - sin s * sin s)))"
    have FZ:  "F s = 0" if "a < s" "s < b" for s using Z[OF that]
  by (simp add: F_def)
    have dF:  "(F  has_real_derivative F1 s) (at s)" for s
      unfolding F_def F1_def by (auto intro!: derivative_eq_intros
  simp: algebra_simps)
    have dF1: "(F1 has_real_derivative F2 s) (at s)" for s
      unfolding F1_def F2_def by (auto intro!: derivative_eq_intros
  simp: algebra_simps)
    have F1Z: "F1 s = 0" if "a < s" "s < b" for s
    proof -
      have "(F has_real_derivative 0) (at s)"
      proof (rule has_field_derivative_transform_within_open[where
  f = "\<lambda>_. 0" and S = "{a<..<b}"])
        show "((\<lambda>_. 0::real) has_real_derivative 0) (at s)"
  by (rule DERIV_const)
        show "open {a<..<b}" by simp
        show "s \<in> {a<..<b}" using that by simp
        show "\<And>y. y \<in> {a<..<b} \<Longrightarrow> (0::real) = F y" 
          using FZ by simp
      qed   
      with dF[of s] show "F1 s = 0" by (metis DERIV_unique)
    qed
    define m where "m = (a + b) / 2"
    have m_mem: "m \<in> {a<..<b}" using ab by (simp add: m_def)
    have e1: "F1 m = 0" using F1Z m_mem by simp
    have "(F1 has_real_derivative 0) (at m)"
    proof (rule has_field_derivative_transform_within_open[where f
  = "\<lambda>_. 0" and S = "{a<..<b}"])
      show "((\<lambda>_. 0::real) has_real_derivative 0) (at m)"
        by (rule DERIV_const)
      show "open {a<..<b}" by simp
      show "m \<in> {a<..<b}" using m_mem by simp
      show "\<And>y. y \<in> {a<..<b} \<Longrightarrow> (0::real) =  F1 y" using F1Z by simp
    qed
    with dF1[of m] have e2: "F2 m = 0" by (metis DERIV_unique)
    define X where "X = cos m * cos m - sin m * sin m"
    define Y where "Y = 2 * sin m * cos m"
    have pyth: "X * X + Y * Y = 1" 
      using sin_cos_squared_add[of m] using pythagorean_squared
      by (simp add: X_def Y_def power2_eq_square algebra_simps)
    have eq1: "X - M * Y = 0" using e1 by (simp add: F1_def X_def
  Y_def)
    have eq2: "Y + M * X = 0" using e2 by (simp add: F2_def X_def
  Y_def algebra_simps)
    have "(1 + M * M) * X = 0" 
      using eq1 eq2 by (smt (verit, del_insts) mult_not_zero zero_le_mult_iff)
    hence "X = 0"
      by (metis more_arith_simps(6) mult_eq_0_iff sum_squares_eq_zero_iff) 
    moreover from this eq2 have "Y = 0" by simp
    ultimately show False using pyth by simp
  qed


lemma steering_singular_nowhere_dense:
    shows "nowhere_dense {\<omega>::angle. det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  proof -   
    define g where "g = (\<lambda>u::real. ((kx \<omega>0 - kx
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * cos u
                                   + ((ky \<omega>0 - ky
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * sin u)"
    define f where "f = (\<lambda>\<omega>::real^2. sin
  (\<omega>$1) * (cos (\<omega>$1) - sin (\<omega>$1) * g
  (\<omega>$2)))"
    have feq: "{\<omega>::angle. det (matrix (Dcvec_dip \<omega>0
  \<omega>s \<omega>)) = 0} = {\<omega>. f \<omega> = 0}"
      by (simp add: f_def g_def Dcvec_det_eq)
    have contf: "continuous_on UNIV f"
      unfolding f_def g_def
      by (intro continuous_intros bounded_linear.continuous_on[OF bounded_linear_vec_nth])
    have closedE: "closed {\<omega>::real^2. f \<omega> = 0}"
      by (rule closed_Collect_eq[OF contf continuous_on_const])
    have intE: "interior {\<omega>::real^2. f \<omega> = 0} = {}"
    proof (rule ccontr)
      assume "interior {\<omega>. f \<omega> = 0} \<noteq> {}"
      then obtain c where "c \<in> interior {\<omega>. f \<omega> =
  0}" by blast
      then obtain r where r: "0 < r" and bsub: "ball c r  \<subseteq> {\<omega>. f \<omega> = 0}"
        using mem_interior by blast
      have inb: "sin s * (cos s - sin s * g (c$2)) = 0" if hs:
  "\<bar>s - c$1\<bar> < r" for s
      proof -
        have "vector [s, c$2] - c = axis 1 (s - c$1)"
          by (simp add: vec_eq_iff forall_2 vector_2 axis_def,
              smt (verit, del_insts) Finite_Cartesian_Product.minus_vec_def 
              exhaust_2 vec_lambda_unique vector_2(1,2) verit_minus_simplify(1))
        hence "dist (vector [s, c$2] :: real^2) c = \<bar>s -  c$1\<bar>"
          by (simp add: dist_norm norm_eq_sqrt_inner inner_axis_axis)
        hence "vector [s, c$2] \<in> ball c r" using hs by (simp add: dist_commute)
        hence "f (vector [s, c$2]) = 0" using bsub by blast
        thus ?thesis by (simp add: f_def vector_2)
      qed
      have lt: "c$1 - r < c$1 + r" using r by simp
      obtain s where "c$1 - r < s" "s < c$1 + r" "sin s * (cos s - sin s * g (c$2)) \<noteq> 0"
        using sin_cos_lin_not_const0[where M = "g (c$2)" and a = "c$1 - r" and b = "c$1 + r"] lt 
        by blast
      moreover from this have "\<bar>s - c$1\<bar> < r" by simp
      ultimately show False using inb by blast
    qed
    show ?thesis
      using closedE intE by (simp add: feq nowhere_dense_def closure_closed)
  qed

text \<open>\<^bold>\<open>The planar-config transversality engine is DONE\<close> --- proven sorry-free as
  \<open>parametric_transversality_meager_planar_config\<close> in \<open>Nonemptiness_Robust2\<close>
  (in the \<open>Applied_Math_Appendix\<close> heap; development history in \<open>Scratch_planar\<close>).
  It is available here via the import.  CAUTION (sledgehammer): do NOT accept
  proofs citing the 7 sorried facts (capstone_feasible, branch_*_meager,
  capstone_X0_sound, odd_N_nonemptiness).\<close>

text \<open>\<^bold>\<open>(M4) Regular stratum is meager.\<close>  On the open locus where \<open>A \<noteq> 0\<close>, \<open>surj (DM_paper_x \<dots>)\<close>,
  and \<open>det (Dcvec) \<noteq> 0\<close>, \<open>0\<close> is a regular value (@{thm regular_value_on_gradU_dip}); covering this
  open (non-product) locus by countably many product boxes and applying
  {thm parametric_transversality_meager_planar_config} on each, the degenerate-critical projection
  over the regular stratum is meager.\<close>

text \<open>\<open>meager_bad_regular_stratum\<close> (M4) is DONE --- proven sorry-free in
  \<open>Nonemptiness_Robust2\<close> (in the heap), together with the reusable helpers
  \<open>regular_value_on_subset\<close>, \<open>open_prod_nat_cover\<close>, \<open>dip_slice_no_surj_deriv\<close>.
  Development history in \<open>Scratch_m4\<close>.\<close>

text \<open>\<^bold>\<open>(M5) Rank-deficient stratum is meager.\<close>  The set of configurations carrying a degenerate
  critical point (with \<open>A \<noteq> 0\<close>) at an angle where the moment map \<^emph>\<open>fails\<close> to be a submersion.  This
  is the projection of a positive-codimension set; meager by the \<open>m_star = 0\<close> nowhere-density (M2)
  combined with a parametric argument over \<open>\<omega>\<close>.\<close>

lemma meager_rank_deficient_stratum:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  sorry

text \<open>\<^bold>\<open>(M6) Steering-singular stratum is meager.\<close>  Degenerate critical points (with \<open>A \<noteq> 0\<close>) at an
  angle where the steering Jacobian is singular.  Meager by (M3): the singular-\<open>\<omega>\<close> locus is
  nowhere dense, and the critical points over it form a positive-codimension set.\<close>

lemma meager_steering_singular_stratum:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  sorry

text \<open>\<^bold>\<open>(M6b) The \<open>A = 0\<close> degenerate stratum is meager --- ADDED (soundness).\<close>  The bad set in
  M4--M6 carries \<open>A \<noteq> 0\<close> (the transversality argument needs it).  But every array-factor null
  \<open>A_cart = 0\<close> is itself a critical point (\<open>\<nabla>\<^sub>\<Omega>U = g \<nabla>\<bar>A\<bar>\<^sup>2 + \<bar>A\<bar>\<^sup>2 \<nabla>g = 0\<close> at \<open>A = 0\<close>), so a
  \<^emph>\<open>degenerate\<close> null also breaks regularity and must be excluded.  The locus \<open>{A = 0 \<and> det \<nabla>\<^sup>2U = 0}\<close>
  is \<open>3\<close> real conditions on \<open>(\<bm>x,\<omega>)\<close> (codim \<open>3\<close>): its \<open>\<bm>x\<close>-projection is meager.\<close>

text \<open>\<open>meager_Azero_degenerate_stratum\<close> (M6b) is DONE --- proven sorry-free in
  \<open>Nonemptiness_Robust2\<close> (in the heap): the planar engine on \<open>cplx_r2 \<circ> af\<close>
  with global regular value (odd \<open>N\<close>), plus the Hessian-at-null determinant
  identity.  Development history in \<open>Scratch_m6b\<close>.\<close>

text \<open>\<^bold>\<open>(M7) The dipole-specific bad set is meager --- CORRECTED to the FULL set.\<close>  By @{thm
  Phibad_dip_imp_detHess0}, \<open>\<Phi> = 0\<close> gives \<open>\<nabla>\<^sub>\<Omega>U = 0 \<and> det (\<nabla>\<^sup>2U) = 0\<close>; then every witnessing \<open>\<omega>\<close> falls
  into exactly one of \<^bold>\<open>four\<close> strata --- regular (M4), rank-deficient (M5), steering-singular (M6),
  or array-null \<open>A = 0\<close> (M6b) --- whose union is meager.  \<^bold>\<open>SOUNDNESS FIX:\<close> the conclusion is now the
  \<^bold>\<open>full\<close> degenerate-critical set \<open>{\<exists>\<omega>. \<Phi> = 0}\<close> (no spurious \<open>A \<noteq> 0\<close>), so its complement gives a point
  with \<^emph>\<open>no\<close> degenerate critical at any \<open>\<omega>\<close> --- what the capstone actually needs.  \<^bold>\<open>This is the lemma
  the capstone consumes\<close>, in place of the unprovable generic \<open>Phi_bad_meager\<close>.\<close>

lemma Phi_bad_meager_dip:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and oddN: "odd CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
proof -
  let ?reg = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  let ?def = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  let ?steer = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  let ?null = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
  have meag4: "meager (?reg \<union> ?def \<union> ?steer \<union> ?null)"
    by (intro meager_Un meager_bad_regular_stratum_on[OF openV Vne c6]
              meager_rank_deficient_stratum[OF openV Vne c6 d0 pf]
              meager_steering_singular_stratum[OF openV Vne c6 d0 pf]
              meager_Azero_degenerate_stratum[OF openV Vne c6 oddN d0 pf])
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}
             \<subseteq> ?reg \<union> ?def \<union> ?steer \<union> ?null"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    then obtain \<omega> where xV: "x \<in> V" and wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and pb: "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    from Phibad_dip_imp_detHess0[OF pb]
    have g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and d0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" by blast+
    show "x \<in> ?reg \<union> ?def \<union> ?steer \<union> ?null"
      using xV wD g0 d0
      by fastforce 
  qed
  show ?thesis by (rule meager_subset[OF sub meag4])
qed


subsection \<open>The capstone: \<open>\<F>\<^sub>0\<close> is nonempty for appropriately chosen \<open>\<xi>, \<kappa>, \<epsilon>\<close>\<close>

text \<open>TeX Lemma~\eqref{F0} (D_edit_May18, the 2-D version, L1288/F0\_nonempty\_proof\_2D):
  for appropriately chosen \<open>\<xi>,\<kappa>,\<epsilon> > 0\<close>, \<open>\<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>) = \<F> \<inter> X\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close> is nonempty.

  \<^bold>\<open>No regularity is assumed.\<close>  The analytic input --- a feasible \<open>x\<^sub>0\<close> whose pattern is
  \<^emph>\<open>regular\<close> (\<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> on the \<open>\<epsilon>\<close>-sphere, and \<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> or \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> on \<open>\<Omega>\<^sup>~\<close>) ---
  is a \<^emph>\<open>consequence\<close> of \<open>Phi_bad_meager\<close> + Baire (the degenerate configurations are
  meager, so their complement inside the open interior of the feasible body is dense and
  in particular nonempty), packaged for the actual pattern as the obligation
  \<open>regular_feasible_point_dip\<close> below.  This is precisely what the determinant computation was
  for.  Given that point, the margins \<open>\<kappa> = min\<^bsub>\<partial>B\<^sub>\<epsilon>\<^esub>\<parallel>\<nabla>\<^sub>\<Omega>U\<parallel>\<close> and
  \<open>\<xi> = min\<^bsub>\<Omega>\<^sup>~\<^esub>(\<parallel>\<nabla>\<^sub>\<Omega>U\<parallel> + \<sigma>\<^sub>m\<^sub>i\<^sub>n(H))\<close> are positive by Weierstrass, and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.
  We split the analytic core (\<open>F0_nonempty_of_witness\<close>) from the witness, so the concrete
  dipole capstone \<open>F0_dip_nonempty\<close> discharges the \<^emph>\<open>continuity\<close> half from proven facts and
  leaves only the genuine existence-of-a-regular-feasible-point hole.\<close>

lemma mem_imp_ne_empty: "x \<in> A \<Longrightarrow> A \<noteq> {}" by blast

text \<open>\<^bold>\<open>The capstone core, parametrised by the regular feasible witness.\<close>  Given a feasible
  \<open>x\<^sub>0\<close> and radius \<open>\<epsilon>>0\<close> whose pattern is regular --- gradient nonvanishing on the
  \<open>\<epsilon>\<close>-sphere, gradient-or-nondegenerate on the annulus, with the relevant norms continuous
  --- the positive margins \<open>\<kappa>,\<xi>\<close> exist by Weierstrass and \<open>x\<^sub>0 \<in> \<F>\<^sub>0(\<xi>,\<kappa>,\<epsilon>)\<close>.  This is the
  purely analytic half of \<open>F0_nonempty\<close>; the witness itself (the determinant/Baire payoff)
  is the separate obligation.  Isolating it lets the \<^emph>\<open>concrete dipole\<close> capstone discharge
  the continuity conjuncts from the proven @{thm norm_gradU_dip_continuous_on} /
  @{thm sigma_min_HessU_dip_continuous_on}, rather than assuming them.\<close>

lemma F0_nonempty_of_witness:
  fixes cvec :: "angle \<Rightarrow> planar" and g :: "angle \<Rightarrow> real"
    and R dmin A B D \<delta>null pmin :: real and \<omega>null ctr :: planar
    and x0 :: "planar^'n" and \<epsilon> :: real and \<Omega>dom :: "planar set"
  assumes \<epsilon>0: "0 < \<epsilon>" and cOm: "compact \<Omega>dom"
    and feas: "x0 \<in> Ffeas cvec g R dmin A B D \<omega>null ctr \<delta>null pmin"
    and cdN: "continuous_on (sphere ctr \<epsilon>) (\<lambda>\<omega>. norm (gradU cvec g x0 \<omega>))"
    and cdsum: "continuous_on (\<Omega>dom - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
    and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU cvec g x0 \<omega> \<noteq> 0"
    and rO: "\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
                gradU cvec g x0 y \<noteq> 0 \<or> 0 < sigma_min (HessU cvec g x0 y)"
  shows "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
            \<and> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>
                \<noteq> ({}::(planar^'n) set)"
proof -
  \<comment> \<open>the positive \<open>\<kappa>\<close>-margin on the \<open>\<epsilon>\<close>-sphere (Weierstrass)\<close>
  have sph_ne: "sphere ctr \<epsilon> \<noteq> {}"
  proof -
    have "dist (ctr + \<epsilon> *\<^sub>R axis (1::2) 1) ctr = \<epsilon>"
      using \<epsilon>0 by (simp add: dist_norm abs_of_pos)
    hence "ctr + \<epsilon> *\<^sub>R axis (1::2) 1 \<in> sphere ctr \<epsilon>"
      by (simp add: dist_commute)
    thus ?thesis by blast
  qed
  obtain \<omega>m where \<omega>m: "\<omega>m \<in> sphere ctr \<epsilon>"
      and \<omega>min: "\<forall>\<omega>\<in>sphere ctr \<epsilon>.
                    norm (gradU cvec g x0 \<omega>m) \<le> norm (gradU cvec g x0 \<omega>)"
    using continuous_attains_inf[OF compact_sphere sph_ne cdN] by blast
  define \<kappa> where "\<kappa> = norm (gradU cvec g x0 \<omega>m)"
  have \<kappa>pos: "0 < \<kappa>" using bspec[OF rsph \<omega>m] unfolding \<kappa>_def by simp
  have inXrob: "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>"
    using \<omega>min unfolding Xrobust_def \<kappa>_def by simp
  \<comment> \<open>the positive \<open>\<xi>\<close>-margin on \<open>\<Omega>\<^sup>~\<close> (vacuous if \<open>\<Omega>\<^sup>~ = \<emptyset>\<close>)\<close>
  show ?thesis
  proof (cases "\<Omega>dom - ball ctr \<epsilon> = {}")
    case True
    have "x0 \<in> X0 cvec g ctr (\<Omega>dom) 1 \<kappa> \<epsilon>"
      using inXrob True unfolding X0_def by blast
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin 1 \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin 1 \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    moreover have "(0::real) < 1" by simp
    ultimately show ?thesis using \<kappa>pos \<epsilon>0 by blast
  next
    case False
    obtain ym where ym: "ym \<in> \<Omega>dom - ball ctr \<epsilon>"
        and ymin: "\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
              norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)
              \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y)"
      using continuous_attains_inf[OF compact_minus_ball[OF cOm] False cdsum] by blast
    define \<xi> where "\<xi> = norm (gradU cvec g x0 ym) + sigma_min (HessU cvec g x0 ym)"
    have \<xi>pos: "0 < \<xi>"
    proof (cases "gradU cvec g x0 ym = 0")
      case True
      with bspec[OF rO ym] have "0 < sigma_min (HessU cvec g x0 ym)" by simp
      thus ?thesis unfolding \<xi>_def
        using norm_ge_zero[of "gradU cvec g x0 ym"] by linarith
    next
      case False
      hence "0 < norm (gradU cvec g x0 ym)" by simp
      thus ?thesis unfolding \<xi>_def
        using sigma_min_nonneg[of "HessU cvec g x0 ym"] by linarith
    qed
    have "x0 \<in> Xrobust cvec g ctr \<epsilon> \<kappa>
          \<and> (\<forall>y\<in>\<Omega>dom - ball ctr \<epsilon>.
                \<xi> \<le> norm (gradU cvec g x0 y) + sigma_min (HessU cvec g x0 y))"
      using inXrob ymin unfolding \<xi>_def by blast
    hence "x0 \<in> X0 cvec g ctr (\<Omega>dom) \<xi> \<kappa> \<epsilon>" unfolding X0_def by simp
    hence "x0 \<in> F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>"
      using feas unfolding F0_def by simp
    hence "F0 cvec g R dmin A B D \<omega>null ctr (\<Omega>dom) \<delta>null pmin \<xi> \<kappa> \<epsilon>
             \<noteq> ({}::(planar^'n) set)"
      by (rule mem_imp_ne_empty)
    thus ?thesis using \<xi>pos \<kappa>pos \<epsilon>0 by blast
  qed
qed

subsection \<open>The capstone for the ACTUAL dipole pattern \<open>U_dip\<close>\<close>

text \<open>\<^bold>\<open>The genuine remaining obligation, for the actual function.\<close>  Specialised to the
  concrete steered dipole \<open>cvec = cvec\<^sub>dip \<omega>\<^sub>0 \<omega>\<^sub>s\<close>, \<open>g = gain\<^sub>dip\<close>: there is a feasible
  configuration \<open>x\<^sub>0\<close> and radius \<open>\<epsilon>>0\<close> whose pattern is regular (gradient nonvanishing on
  \<open>\<partial>B\<^sub>\<epsilon>\<close>, gradient-or-nondegenerate on \<open>\<Omega>\<^sup>~\<close>).  This is \<^emph>\<open>exactly\<close> the determinant/Baire
  payoff (degenerate configs meager, @{thm Phi_bad_meager_dip} + Baire inside the feasible
  interior); crucially the \<^emph>\<open>continuity\<close> half is no longer part of this hole --- it is
  discharged below from the proven dipole facts.\<close>

text \<open>\<^bold>\<open>The Baire scaffold for \<open>regular_feasible_point_dip\<close> (\<^bold>\<open>statements only\<close>; proofs deferred).\<close>\<close>

text \<open>\<^bold>\<open>(C0) A nonzero smallest singular value is exactly invertibility.\<close>  For a real \<open>2\<times>2\<close>
  matrix the smallest singular value @{const sigma_min} is positive iff the determinant is
  nonzero --- the bridge between the degeneracy slot \<open>det (\<nabla>\<^sup>2U) = 0\<close> and the capstone's
  \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n(H) > 0\<close> nondegeneracy margin.\<close>

lemma sigma_min_pos_iff_invertible:
  fixes H :: "real^2^2"
  shows "0 < sigma_min H \<longleftrightarrow> det H \<noteq> 0"
proof -
  have lin: "linear ((*v) H)" by (rule matrix_vector_mul_linear)
  have bdd: "bdd_below ((\<lambda>v. norm (H *v v)) ` sphere 0 1)"
    by (rule bdd_belowI[of _ 0]) auto
  have cont: "continuous_on (sphere (0::real^2) 1) (\<lambda>v. norm (H *v v))"
    by (rule continuous_on_norm[OF
          bounded_linear.continuous_on[OF matrix_vector_mul_bounded_linear continuous_on_id]])
  \<comment> \<open>Step 1: positivity of the smallest singular value \<open>\<longleftrightarrow>\<close> nonvanishing on the unit sphere.\<close>
  have nz_iff: "0 < sigma_min H \<longleftrightarrow> (\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0)"
  proof
    assume pos: "0 < sigma_min H"
    show "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    proof
      fix v assume v: "v \<in> sphere (0::real^2) 1"
      have "sigma_min H \<le> norm (H *v v)"
        unfolding sigma_min_def by (rule cINF_lower[OF bdd v])
      with pos show "H *v v \<noteq> 0" by auto
    qed
  next
    assume nz: "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    obtain v0 where v0: "v0 \<in> sphere (0::real^2) 1"
        and v0min: "\<forall>v\<in>sphere (0::real^2) 1. norm (H *v v0) \<le> norm (H *v v)"
      using continuous_attains_inf[OF compact_sphere sphere01_ne cont] by blast
    have "sigma_min H = norm (H *v v0)"
    proof -
      have "sigma_min H \<le> norm (H *v v0)"
        unfolding sigma_min_def by (rule cINF_lower[OF bdd v0])
      moreover have "norm (H *v v0) \<le> sigma_min H"
        unfolding sigma_min_def by (rule cINF_greatest[OF sphere01_ne]) (rule v0min[rule_format])
      ultimately show ?thesis by linarith
    qed
    moreover have "0 < norm (H *v v0)" using nz v0 by auto
    ultimately show "0 < sigma_min H" by simp
  qed
  \<comment> \<open>Step 2: nonvanishing on the unit sphere \<open>\<longleftrightarrow>\<close> injectivity (normalise an arbitrary nonzero
      kernel vector to the sphere).\<close>
  have inj_iff: "(\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0) \<longleftrightarrow> inj ((*v) H)"
  proof
    assume nz: "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    show "inj ((*v) H)"
    proof (rule injI)
      fix a b assume eq: "H *v a = H *v b"
      have z: "H *v (a - b) = 0"
        using eq by (simp add: matrix_vector_mult_diff_distrib)
      show "a = b"
      proof (rule ccontr)
        assume "a \<noteq> b"
        hence ab: "a - b \<noteq> 0" by simp
        define u where "u = inverse (norm (a - b)) *\<^sub>R (a - b)"
        have nu: "norm u = 1"
        proof -
          have "norm u = \<bar>inverse (norm (a - b))\<bar> * norm (a - b)"
            by (simp add: u_def)
          also have "\<dots> = inverse (norm (a - b)) * norm (a - b)" by simp
          also have "\<dots> = 1" using ab by simp
          finally show ?thesis .
        qed
        have "u \<in> sphere (0::real^2) 1" using nu by (simp add: dist_norm)
        moreover have "H *v u = 0"
          by (simp add: u_def matrix_vector_mult_scaleR z)
        ultimately show False using nz by auto
      qed
    qed
  next
    assume inj: "inj ((*v) H)"
    show "\<forall>v\<in>sphere (0::real^2) 1. H *v v \<noteq> 0"
    proof
      fix v assume v: "v \<in> sphere (0::real^2) 1"
      hence "v \<noteq> 0" by (auto simp: dist_norm)
      moreover have "H *v (0::real^2) = 0" by simp
      ultimately show "H *v v \<noteq> 0" using inj by (metis injD)
    qed
  qed
  \<comment> \<open>Step 3: injectivity of a square linear map \<open>\<longleftrightarrow>\<close> nonzero determinant.\<close>
  have det_iff: "inj ((*v) H) \<longleftrightarrow> det H \<noteq> 0"
    using det_nz_iff_inj[OF lin] by simp
  show ?thesis using nz_iff inj_iff det_iff by blast
qed

text \<open>\<^bold>\<open>(C1) The feasible body has nonempty interior (Slater).\<close>  If \<^emph>\<open>some\<close> configuration satisfies
  every constraint \<^emph>\<open>strictly\<close> --- all spacings exceed \<open>d\<^sub>min\<close>, the null power is below \<open>\<delta>\<^sub>null\<close>,
  the main power lies strictly between \<open>p\<^sub>min\<close> and the Cauchy--Schwarz cap, and \<open>\<parallel>\<bm>x\<parallel> < R\<close> --- then
  (each constraint function being continuous) that point is interior to @{const Ffeas}.  The
  hypothesis is the genuine strict-feasibility input; it does not mention \<open>interior\<close>.\<close>

lemma Ffeas_interior_nonempty:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle
  assumes "\<exists>x::(real^2)^'n.
       (\<forall>p. fst p \<noteq> snd p \<longrightarrow> dmin < spdist A B D (x $ fst p) (x $ snd p))
     \<and> Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < \<delta>null
     \<and> pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr
     \<and> Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr < gain_dip ctr * (real CARD('n))\<^sup>2
     \<and> norm x < R"
  shows "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
proof -
  from assms obtain x :: "(real^2)^'n"
    where spac0: "\<forall>p. fst p \<noteq> snd p \<longrightarrow> dmin < spdist A B D (x $ fst p) (x $ snd p)"
      and Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < \<delta>null"
      and Pgt: "pmin < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x ctr"
      and nx: "norm x < R" by blast
  have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. dmin < spdist A B D (x $ fst p) (x $ snd p)"
    using spac0 by blast
  have inR: "x \<in> ball 0 R" using nx by (simp add: dist_norm)
  obtain \<rho> where \<rho>: "0 < \<rho>"
      and sub: "ball x \<rho>
                \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
    using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
  have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
    by (rule interior_maximal[OF sub open_ball])
  moreover have "x \<in> ball x \<rho>" using \<rho> by simp
  ultimately show ?thesis by blast
qed

text \<open>\<^bold>\<open>(C2) Baire: a regular configuration exists inside the feasible interior.\<close>  The degenerate
  configurations are meager (@{thm Phi_bad_meager_dip}, the \<^bold>\<open>full\<close> bad set, including \<open>A = 0\<close>), so
  their complement is comeager, hence dense, hence meets the nonempty open feasible interior ---
  yielding a feasible \<open>x\<^sub>0\<close> carrying \<^bold>\<open>no\<close> degenerate critical point at \<^bold>\<open>any\<close> \<open>\<omega>\<close> (\<open>\<Phi> \<noteq> 0\<close> everywhere).
  \<^bold>\<open>SOUNDNESS FIX:\<close> the conclusion no longer carries the spurious \<open>A \<noteq> 0\<close> --- array-factor nulls
  (\<open>A = 0\<close>) are critical points (\<open>\<nabla>\<^sub>\<Omega>U = 0\<close>) too, and a \<^emph>\<open>degenerate\<close> null would break the
  capstone's regularity, so it must also be excluded.\<close>

lemma regular_config_exists:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and int_ne: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                    :: ((real^2)^'n) set) \<noteq> {}"
  shows "\<exists>x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                          :: ((real^2)^'n) set).
            \<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
proof -
  define I where "I = interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: ((real^2)^'n) set)"
  have openI: "open I" unfolding I_def by (rule open_interior)
  have Ine: "I \<noteq> {}" unfolding I_def by (rule int_ne)
  have meagB: "meager {x \<in> I. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    by (rule Phi_bad_meager_dip[OF openI Ine c6 oddN d0 pf])
  have "\<not> I \<subseteq> {x \<in> I. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
  proof
    assume sub: "I \<subseteq> {x \<in> I. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    have "meager I" by (rule meager_subset[OF sub meagB])
    moreover have "\<not> meager I" by (rule open_nonempty_not_meager[OF openI Ine])
    ultimately show False by simp
  qed
  then obtain x0 where x0I: "x0 \<in> I"
    and x0nB: "x0 \<notin> {x \<in> I. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}" by blast
  have x0Iexp: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
    using x0I unfolding I_def by assumption
  have reg: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
    using x0I x0nB by blast
  from x0Iexp reg
  have conjx0: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)
        \<and> (\<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)" by (rule conjI)
  \<comment> \<open>Composition fully established: \<open>x0Iexp\<close> (\<open>x0 \<in> interior\<close>) and \<open>reg\<close> (\<open>\<forall>\<omega>. \<Phi> \<noteq> 0\<close>) are the
      witness data.  Only the final \<^emph>\<open>bounded-existential introduction\<close> \<open>\<exists>x0\<in>interior. \<dots>\<close> with
      witness \<open>x0\<close> is left open --- a witness-instantiation tactic step (\<open>bexI\<close>/\<open>rule_tac x=x0\<close>)
      that needs live goal/type inspection to dispatch against the large \<open>interior (Ffeas \<dots>)\<close>
      term; it is mathematically immediate from \<open>x0Iexp\<close> and \<open>reg\<close>.\<close>
  show ?thesis
  proof (rule bexI[where x = x0])
    show "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0" by (rule reg)
  next
    show "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
      by (rule x0Iexp)
  qed
qed

text \<open>\<^bold>\<open>(C3) From ``no degenerate critical point'' to the sphere/annulus regularity.\<close>  If \<open>x\<^sub>0\<close> has
  no degenerate critical point in \<open>\<Omega>\<close> (at every \<open>\<omega>\<close>, either \<open>\<nabla>\<^sub>\<Omega>U \<noteq> 0\<close> or \<open>det (\<nabla>\<^sup>2U) \<noteq> 0\<close>), then for
  a suitable radius \<open>\<epsilon> > 0\<close> the gradient is nonvanishing on the sphere \<open>\<partial>B\<^sub>\<epsilon>\<close> and
  gradient-or-nondegenerate on the annulus \<open>\<Omega> - B\<^sub>\<epsilon>\<close> --- exactly the conclusion shape of
  \<open>regular_feasible_point_dip\<close> below.  (Nondegenerate critical points are isolated, so \<open>\<epsilon>\<close> can dodge
  them; degeneracy \<open>det = 0\<close> is rephrased as \<open>\<sigma>\<^sub>m\<^sub>i\<^sub>n > 0\<close> via @{thm sigma_min_pos_iff_invertible}.)\<close>

lemma isolated_nondeg_zero:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes hd: "(f has_derivative L) (at c)" and injL: "inj L" and fc: "f c = 0"
  shows "\<exists>d>0. \<forall>y. dist y c < d \<longrightarrow> y \<noteq> c \<longrightarrow> f y \<noteq> 0"
proof -
  have linL: "linear L" using hd by (rule has_derivative_linear)
  obtain B where B0: "0 < B" and Bn: "\<And>v. B * norm v \<le> norm (L v)"
    using linear_inj_bounded_below_pos[OF linL injL] by blast
  have "\<forall>e>0. \<exists>d>0. \<forall>y. norm (y - c) < d \<longrightarrow> norm (f y - f c - L (y - c)) \<le> e * norm (y - c)"
    using hd by (simp add: has_derivative_at_alt)
  then obtain d where d0: "0 < d"
      and db: "\<And>y. norm (y - c) < d \<Longrightarrow> norm (f y - f c - L (y - c)) \<le> (B/2) * norm (y - c)"
    using B0 half_gt_zero by blast
  have "\<forall>y. dist y c < d \<longrightarrow> y \<noteq> c \<longrightarrow> f y \<noteq> 0"
  proof (intro allI impI)
    fix y assume yd: "dist y c < d" and yc: "y \<noteq> c"
    have nyc: "0 < norm (y - c)" using yc by simp
    have ndc: "norm (y - c) < d" using yd by (simp add: dist_norm)
    have a1: "B * norm (y - c) \<le> norm (L (y - c))" by (rule Bn)
    have a2: "norm (f y - L (y - c)) \<le> (B/2) * norm (y - c)" using db[OF ndc] fc by simp
    have "(B/2) * norm (y - c) = B * norm (y - c) - (B/2) * norm (y - c)" by simp
    also have "\<dots> \<le> norm (L (y - c)) - norm (f y - L (y - c))" using a1 a2 by linarith
    also have "\<dots> \<le> norm (f y)"
      using norm_triangle_ineq2[of "L (y - c)" "f y"] by (simp add: norm_minus_commute)
    finally have "(B/2) * norm (y - c) \<le> norm (f y)" .
    moreover have "0 < (B/2) * norm (y - c)" using nyc B0 by simp
    ultimately have "0 < norm (f y)" by linarith
    thus "f y \<noteq> 0" by auto
  qed
  thus ?thesis using d0 by blast
qed


lemma sphere_subset_Omega:
  fixes ctr :: "real^2"
  assumes "\<epsilon> \<le> pi/2"
  shows "sphere ctr \<epsilon> \<subseteq> Omega ctr"
proof
  fix y assume "y \<in> sphere ctr \<epsilon>"
  hence dy: "dist y ctr = \<epsilon>" by (simp add: dist_commute sphere_def)
  show "y \<in> Omega ctr"
    unfolding Omega_def mem_box_cart
  proof (intro allI)
    fix i :: 2
    have b: "\<bar>y$i - ctr$i\<bar> \<le> pi/2"
    proof -
      have "\<bar>y$i - ctr$i\<bar> = \<bar>(y - ctr)$i\<bar>" by simp
      also have "\<dots> \<le> norm (y - ctr)" by (rule component_le_norm_cart)
      also have "\<dots> = \<epsilon>" using dy by (simp add: dist_norm)
      finally show ?thesis using assms by simp
    qed
    have v: "pi/2 \<le> (vector [pi/2, pi] :: real^2) $ i"
      using exhaust_2[of i] by (auto simp: vector_2 pi_gt_zero)
    have lo: "(ctr - vector [pi/2, pi]) $ i = ctr $ i - vector [pi/2, pi] $ i"
      by (simp add: vector_minus_component)
    have hi: "(ctr + vector [pi/2, pi]) $ i = ctr $ i + vector [pi/2, pi] $ i"
      by (simp add: vector_add_component)
    have b1: "y$i - ctr$i \<le> pi/2" using abs_le_D1[OF b] .
    have b2: "ctr$i - y$i \<le> pi/2" using abs_le_D2[OF b] by simp
    show "(ctr - vector [pi/2, pi]) $ i \<le> y $ i \<and> y $ i \<le> (ctr + vector [pi/2, pi]) $ i"
      using lo hi v b1 b2 by linarith
  qed
qed

lemma no_degenerate_to_sphere_annulus:
  fixes x0 :: "(real^2)^'n" and ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and nd: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  shows "\<exists>\<epsilon>>0. (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
proof -
  define f where "f = gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0"
  define C where "C = {\<omega>. \<omega> \<in> OmegaPF ctr \<delta> \<and> f \<omega> = 0}"
  have fcont: "continuous_on UNIV f" unfolding f_def by (rule gradU_dip_continuous_on)
  have isol: "\<not> c islimpt C" if cC: "c \<in> C" for c
  proof -
    from cC have cO: "c \<in> OmegaPF ctr \<delta>" and fc0: "f c = 0" by (auto simp: C_def)
    have dnz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c) \<noteq> 0"
      using nd cO fc0 unfolding f_def by blast
    hence inv: "invertible (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c)" by (simp add: invertible_det_nz)
    have injL: "inj ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c))"
      using inv by (metis matrix_left_invertible_injective invertible_def)
    have hd: "(f has_derivative ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 c))) (at c)"
      unfolding f_def by (rule gradU_dip_has_derivative)
    obtain d where d0: "0 < d" and dd: "\<And>y. dist y c < d \<Longrightarrow> y \<noteq> c \<Longrightarrow> f y \<noteq> 0"
      using isolated_nondeg_zero[OF hd injL fc0] by blast
    show "\<not> c islimpt C" using dd d0 by (force simp: islimpt_approachable C_def)
  qed
  have Cint: "C = OmegaPF ctr \<delta> \<inter> {y. f y = 0}" by (auto simp: C_def)
  have Ccomp: "compact C"
    unfolding Cint by (rule compact_Int_closed[OF OmegaPF_compact closed_Collect_eq[OF fcont continuous_on_const]])
  have Cfin: "finite C" using Ccomp isol by (metis compact_eq_Bolzano_Weierstrass order_refl)
  define R where "R = (\<lambda>c. dist c ctr) ` C"
  have Rfin: "finite R" unfolding R_def using Cfin by simp
  have "infinite {0<..\<delta>::real}" using d0 by (simp add: infinite_Ioc)
  hence "infinite ({0<..\<delta>::real} - R)" using Rfin by (rule Diff_infinite_finite[rotated])
  then obtain \<epsilon> where \<epsilon>m: "\<epsilon> \<in> {0<..\<delta>::real} - R" using infinite_imp_nonempty by blast
  have \<epsilon>0: "0 < \<epsilon>" and \<epsilon>pi: "\<epsilon> \<le> \<delta>" and \<epsilon>R: "\<epsilon> \<notin> R" using \<epsilon>m by auto
  have sphere: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. f \<omega> \<noteq> 0"
  proof
    fix \<omega> assume w: "\<omega> \<in> sphere ctr \<epsilon>"
    hence wO: "\<omega> \<in> OmegaPF ctr \<delta>" using sphere_subset_OmegaPF[OF \<epsilon>pi dpi] by blast
    have dw: "dist \<omega> ctr = \<epsilon>" using w by (simp add: dist_commute sphere_def)
    show "f \<omega> \<noteq> 0"
    proof
      assume "f \<omega> = 0"
      hence "\<omega> \<in> C" using wO by (simp add: C_def)
      hence "dist \<omega> ctr \<in> R" by (simp add: R_def)
      thus False using \<epsilon>R dw by simp
    qed
  qed
  have annulus: "\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                   f y \<noteq> 0 \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
  proof
    fix y assume "y \<in> OmegaPF ctr \<delta> - ball ctr \<epsilon>"
    hence yO: "y \<in> OmegaPF ctr \<delta>" by simp
    show "f y \<noteq> 0 \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    proof (cases "f y = 0")
      case True
      hence "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y) \<noteq> 0"
        using nd yO unfolding f_def by blast
      thus ?thesis by (simp add: sigma_min_pos_iff_invertible)
    next
      case False thus ?thesis by blast
    qed
  qed
  show ?thesis using \<epsilon>0 sphere annulus unfolding f_def by blast
qed

lemma regular_feasible_point_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: (planar^'n) set) \<noteq> {}"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
  \<comment> \<open>\<^bold>\<open>SOUNDNESS FIX:\<close> requires \<open>feasible\<close> (the feasible body has nonempty interior).  Without
      it the claim is false for infeasible parameters (e.g.\ \<open>pmin > gain_dip ctr * N\<^sup>2\<close> forces
      \<open>Ffeas = {}\<close>).  The composition below is \<^bold>\<open>machine-checked\<close>; only the leaf lemmas remain
      \<open>sorry\<close>.\<close>
proof -
  obtain x0 :: "planar^'n"
    where x0I: "x0 \<in> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin)"
      and x0reg: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
    using regular_config_exists[OF c6 oddN d0 pf feasible] by blast
  have x0F: "x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
    using x0I interior_subset by blast
  have nondeg: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. \<not> (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0)"
  proof (intro ballI notI)
    fix \<omega> assume "\<omega> \<in> OmegaPF ctr \<delta>"
      and deg: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0
                \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0"
    from deg have g: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0"
      and dz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>) = 0" by auto
    have e: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>)
              = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 1
                  * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 2 $ 2
                - (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2"
      by (rule det_2_symmetric[OF HessU_dip_symmetric])
    from e dz have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 1
                      * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 2 $ 2
                    = (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> $ 1 $ 2)\<^sup>2" by simp
    with g have "Phibad (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> = 0"
      using Phibad_zero_iff by blast
    with x0reg \<open>\<omega> \<in> OmegaPF ctr \<delta>\<close> show False by auto
  qed
  obtain \<epsilon> :: real where \<epsilon>0: "0 < \<epsilon>"
      and sph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
      and ann: "\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    using no_degenerate_to_sphere_annulus[OF d0 dpi nondeg] by blast
  have c1: "0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
    using \<epsilon>0 x0F sph ann by (intro conjI)
  show ?thesis
  proof (rule exI[where x = x0], rule exI[where x = \<epsilon>])
    show "0 < \<epsilon>
          \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
          \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
          \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
      by (rule c1)
  qed
qed

text \<open>\<^bold>\<open>The regular feasible witness for the dipole, with continuity DISCHARGED.\<close>  We bolt the
  two Weierstrass continuity conjuncts --- proven sorry-free in
  @{thm norm_gradU_dip_continuous_on} and @{thm sigma_min_HessU_dip_continuous_on} --- onto
  the regular feasible point, so what remains assumed is purely the existence of that point.\<close>

lemma regular_feasible_witness_dip:
  fixes R dmin A B D \<delta>null pmin :: real and \<omega>null ctr \<omega>0 \<omega>s :: angle and \<delta> :: real
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and d0: "0 < \<delta>" and dpi: "\<delta> \<le> pi"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
                      :: (planar^'n) set) \<noteq> {}"
  shows "\<exists>(x0::planar^'n) \<epsilon>. 0 < \<epsilon>
            \<and> x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin
            \<and> continuous_on (sphere ctr \<epsilon>)
                  (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>))
            \<and> continuous_on (OmegaPF ctr \<delta> - ball ctr \<epsilon>)
                  (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)
                       + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))
            \<and> (\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0)
            \<and> (\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
proof -
  obtain x0 :: "planar^'n" and \<epsilon> :: real
    where \<epsilon>0: "0 < \<epsilon>"
      and feas: "x0 \<in> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr \<delta>null pmin"
      and rsph: "\<forall>\<omega>\<in>sphere ctr \<epsilon>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> \<noteq> 0"
      and rO: "\<forall>y\<in>OmegaPF ctr \<delta> - ball ctr \<epsilon>.
                  gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y \<noteq> 0
                  \<or> 0 < sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)"
    using regular_feasible_point_dip[OF c6 oddN d0 dpi pf feasible] by blast
  have c1: "continuous_on (sphere ctr \<epsilon>)
              (\<lambda>\<omega>. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>))"
    by (rule norm_gradU_dip_continuous_on)
  have c2: "continuous_on (OmegaPF ctr \<delta> - ball ctr \<epsilon>)
              (\<lambda>y. norm (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y)
                   + sigma_min (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 y))"
    by (intro continuous_on_add norm_gradU_dip_continuous_on
              sigma_min_HessU_dip_continuous_on)
  show ?thesis using \<epsilon>0 feas c1 c2 rsph rO by blast
qed

text \<open>\<^bold>\<open>The concrete capstone: \<open>\<F>\<^sub>0\<close> for the ACTUAL dipole pattern is nonempty.\<close>  This is
  \<open>thm:final\<close>'s nonemptiness for the real radiation intensity \<open>U_dip = g(\<omega>)\<bar>A(\<bm>x,\<omega>)\<bar>\<^sup>2\<close>
  with the steered wavevector \<open>cvec\<^sub>dip\<close> and the smooth dipole gain \<open>gain\<^sub>dip = \<bar>e(\<theta>)\<bar>\<^sup>2\<close>
  --- no abstract \<open>cvec\<close>/\<open>g\<close>.  The continuity half is fully proven; the only assumption is
  the regular feasible point (the determinant/Baire payoff, @{thm regular_feasible_point_dip}).\<close>

theorem F0_dip_nonempty:
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
  shows "\<exists>A B D \<omega>0 \<omega>s \<omega>null ctr \<delta> R dmin \<delta>null pmin \<xi> \<kappa> \<epsilon>.
            0 < \<delta> \<and> 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr (OmegaPF ctr \<delta>) \<delta>null pmin \<xi> \<kappa> \<epsilon>
              \<noteq> ({}::(planar^'n) set)"
  \<comment> \<open>\<^bold>\<open>The odd-\<open>N\<close> capstone.\<close>  The hypotheses are the dimension restriction \<open>c6\<close> and
      oddness (as in TeX \<open>thm:final\<close>; oddness powers \<open>dxA_surj\<close> in the \<open>A = 0\<close> stratum); the design
      (steering \<open>\<omega>\<^sub>0,\<omega>\<^sub>s,\<omega>\<^sub>null\<close>, geometry \<open>A,B,D\<close>, tolerances \<open>d\<^sub>min,\<delta>\<^sub>null,p\<^sub>min,R\<close> and margins) is
      \<^emph>\<open>delivered by the construction\<close>, not assumed.  Feasibility is discharged by the explicit
      Slater witness (@{thm feasible_witness_exists}): the actual \<open>cvec_dip\<close> nulls at \<open>\<omega>\<^sub>null\<close>
      (roots of unity, \<open>A(\<bm>x,\<omega>\<^sub>null)=0\<close>), the main-beam power is pinned to the cap for \<^emph>\<open>every\<close>
      configuration (@{thm Upow_at_main}: \<open>cvec_dip(\<omega>\<^sub>0)=0\<close>), and we pick \<open>p\<^sub>min,d\<^sub>min,\<delta>\<^sub>null\<close> to make
      the witness strictly feasible --- everything is under our control.\<close>
proof -
  define \<omega>0 :: planar where "\<omega>0 = vector [pi/2, 0]"
  define \<omega>s :: planar where "\<omega>s = vector [0, 0]"
  define \<omega>null :: planar where "\<omega>null = vector [pi, 0]"
  have hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    by (simp add: \<omega>s_def \<omega>0_def kz_def)
  have d0: "(0::real) < pi/4" by simp
  have dpi: "(pi::real)/4 \<le> pi" by simp
  have pf: "\<forall>\<omega>\<in>OmegaPF \<omega>0 (pi/4). sin (\<omega> $ 1) \<noteq> 0"
  proof
    fix \<omega> :: planar assume "\<omega> \<in> OmegaPF \<omega>0 (pi/4)"
    hence mb: "(\<omega>0 - vector [pi/4, pi]) $ 1 \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> (\<omega>0 + vector [pi/4, pi]) $ 1"
      unfolding OmegaPF_def mem_box_cart by blast
    have l1: "(\<omega>0 - vector [pi/4, pi]) $ 1 = pi/4"
      by (simp add: \<omega>0_def vector_minus_component vector_2)
    have l2: "(\<omega>0 + vector [pi/4, pi]) $ 1 = 3*pi/4"
      by (simp add: \<omega>0_def vector_add_component vector_2)
    have lo: "0 < \<omega> $ 1" and hi: "\<omega> $ 1 < pi" using mb l1 l2 pi_gt_zero by linarith+
    have "0 < sin (\<omega> $ 1)" by (rule sin_gt_zero[OF lo hi])
    thus "sin (\<omega> $ 1) \<noteq> 0" by simp
  qed
  have cn: "cvec_dip \<omega>0 \<omega>s \<omega>null \<noteq> 0"
  proof -
    have "cvec_dip \<omega>0 \<omega>s \<omega>null $ 1 = - 2"
      by (simp add: cvec_dip_def \<omega>0_def \<omega>s_def \<omega>null_def kx_def ky_def kz_def
                    sin_pi_half cos_pi_half axis_def)
    hence "cvec_dip \<omega>0 \<omega>s \<omega>null $ 1 \<noteq> 0" by simp
    thus ?thesis by (metis zero_index)
  qed
  have N1: "CARD('n) > 1" using c6 by simp
  have spos: "(0::real) < 1" by simp
  obtain x :: "planar^'n"
    where afz: "af (cvec_dip \<omega>0 \<omega>s) x \<omega>null = 0"
      and spac0: "\<forall>m m'. m \<noteq> m' \<longrightarrow> (1::real) \<le> spdist 0 0 1 (x $ m) (x $ m')"
    using feasible_witness_exists[OF N1 cn spos] by meson
  define R :: real where "R = norm x + 1"
  have g0pos: "0 < gain_dip \<omega>0"
  proof -
    have "sin (\<omega>0 $ 1) \<noteq> 0" by (simp add: \<omega>0_def sin_pi_half)
    hence "gain_dip \<omega>0 \<noteq> 0" by (rule gain_dip_nonzero_of_sin)
    moreover have "0 \<le> gain_dip \<omega>0" by (rule gain_dip_nonneg)
    ultimately show ?thesis by simp
  qed
  have feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
                    :: (planar^'n) set) \<noteq> {}"
  proof -
    have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}. (1/2::real) < spdist 0 0 1 (x $ fst p) (x $ snd p)"
      using spac0 by fastforce
    have Nlt: "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>null < 1"
      using afz by (simp add: Upow_def)
    have Pgt: "(0::real) < Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0"
    proof -
      have "Upow (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>0 = gain_dip \<omega>0 * (real CARD('n))\<^sup>2"
        by (rule Upow_at_main[OF hsep])
      moreover have "0 < (real CARD('n))\<^sup>2" using N1 by simp
      ultimately show ?thesis using mult_pos_pos[OF g0pos] by simp
    qed
    have inR: "x \<in> ball 0 R" by (simp add: R_def dist_norm)
    obtain \<rho> where \<rho>: "0 < \<rho>"
        and sub: "ball x \<rho> \<subseteq> Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0"
      using ball_inside_Ffeas[OF gain_dip_nonneg gain_dip_nonneg spac Nlt Pgt inR] by blast
    have "ball x \<rho> \<subseteq> interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0)"
      by (rule interior_maximal[OF sub open_ball])
    moreover have "x \<in> ball x \<rho>" using \<rho> by simp
    ultimately show ?thesis by blast
  qed
  have "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 (OmegaPF \<omega>0 (pi/4)) 1 0 \<xi> \<kappa> \<epsilon>
              \<noteq> ({}::(planar^'n) set)"
    using regular_feasible_witness_dip[OF c6 oddN d0 dpi pf feasible]
    by (blast intro: F0_nonempty_of_witness OmegaPF_compact)
  thus ?thesis using d0 by blast
qed

end