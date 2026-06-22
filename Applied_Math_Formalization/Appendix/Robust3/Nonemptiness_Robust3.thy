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
  by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_6
                Lmat_def matrix_vector_mult_def sum_6)

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


(* ============================================================================
   M5 CONSOLIDATION GRAFT (auto-assembled): D1 + D2 + D5 + D34 strata, proven
   sorry-free except the two D34 chart-branch cores (m5_D34_D3_collinear,
   m5_D34_D4_branchP).  Sources: M5_Dev_D5 / M5_Dev_D2 / M5_Dev_D34 / M5_Dev.
   The freebie fixed_c_nonsurj_nowhere_dense is discharged here in-place from the
   resident mstarg machinery (surj_iff_mstarg + nowhere_dense_mstarg_zeros).
   ============================================================================ *)

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
proof -
  have "{x::(real^2)^'n. \<not> surj (DM_paper_x x c)} = {x. mstarg c x = 0}"
    using surj_iff_mstarg by auto
  thus ?thesis using nowhere_dense_mstarg_zeros[OF c0 n6] by simp
qed

(* ---- D5: steering-singular corner: gdip-helpers + beam-center Hessian + m5_D5_steersing ---- *)

definition gsincdd :: "real \<Rightarrow> real" where
  "gsincdd x = (- (x^2) * sin x - 2 * x * cos x + 2 * sin x) / x^3"

lemma gsincd_has_deriv:
  fixes x :: real
  assumes x0: "x \<noteq> 0"
  shows "(gsincd has_real_derivative gsincdd x) (at x)"
proof -
  have num: "((\<lambda>y. y * cos y - sin y) has_real_derivative (- x * sin x)) (at x)"
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  have den: "((\<lambda>y. y^2) has_real_derivative (2 * x)) (at x)"
    by (auto intro!: derivative_eq_intros)
  have x2: "x^2 \<noteq> 0" using x0 by simp
  have raw: "((\<lambda>y. (y * cos y - sin y) / y^2) has_real_derivative
              ((- x * sin x) * x^2 - (x * cos x - sin x) * (2 * x)) / (x^2 * x^2)) (at x)"
    by (rule DERIV_divide[OF num den x2])
  have eq: "((- x * sin x) * x^2 - (x * cos x - sin x) * (2 * x)) / (x^2 * x^2) = gsincdd x"
    using x0 by (simp add: gsincdd_def power2_eq_square power3_eq_cube field_simps)
  have step: "((\<lambda>y. (y * cos y - sin y) / y^2) has_real_derivative gsincdd x) (at x)"
    using raw unfolding eq .
  show ?thesis
  proof (rule has_field_derivative_transform_within_open[OF step, where S = "- {0::real}"])
    show "open (- {0::real})" by (rule open_Compl) (rule closed_singleton)
    show "x \<in> - {0::real}" using x0 by simp
    show "\<And>y. y \<in> - {0::real} \<Longrightarrow> (y * cos y - sin y) / y^2 = gsincd y"
      by (simp add: gsincd_def)
  qed
qed

definition um :: "real \<Rightarrow> real" where "um t = (pi/2)*(1 - cos t)"
definition up :: "real \<Rightarrow> real" where "up t = (pi/2)*(1 + cos t)"

definition D1f :: "real \<Rightarrow> real" where
  "D1f t = pi^2/4 * ((pi/2) * sin t) *
             (gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))"

lemma gdip_deriv_field_eq_D1f:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0"
  shows "frechet_derivative gdip (at \<theta>) 1 = D1f \<theta>"
proof -
  have "(gdip has_real_derivative D1f \<theta>) (at \<theta>)"
    using g1_gdip_has_deriv[OF s0] unfolding D1f_def um_def up_def .
  thus ?thesis by (rule g1_frechet_eval)
qed

lemma D1f_has_deriv:
  fixes \<theta> :: real
  assumes um0: "um \<theta> \<noteq> 0" and up0: "up \<theta> \<noteq> 0"
  shows "(D1f has_real_derivative
           pi^2/4 *
           ( (pi/2) * cos \<theta>
              * (gsincd (um \<theta>) * gsinc (up \<theta>) - gsinc (um \<theta>) * gsincd (up \<theta>))
            + (pi/2) * sin \<theta>
              * ( ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                     + gsincd (um \<theta>) * (gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) )
                  - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                     + gsinc (um \<theta>) * (gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) ) )))
         (at \<theta>)"
proof -
  have dum: "(um has_real_derivative ((pi/2) * sin \<theta>)) (at \<theta>)"
    unfolding um_def by (auto intro!: derivative_eq_intros)
  have dup: "(up has_real_derivative (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    unfolding up_def by (auto intro!: derivative_eq_intros)
  have gsmum: "((\<lambda>t. gsinc (um t)) has_real_derivative
                 gsincd (um \<theta>) * ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF g1_gsinc_has_deriv[OF um0] dum])
  have gsdmum: "((\<lambda>t. gsincd (um t)) has_real_derivative
                  gsincdd (um \<theta>) * ((pi/2) * sin \<theta>)) (at \<theta>)"
    by (rule DERIV_chain2[OF gsincd_has_deriv[OF um0] dum])
  have gsmup: "((\<lambda>t. gsinc (up t)) has_real_derivative
                 gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    by (rule DERIV_chain2[OF g1_gsinc_has_deriv[OF up0] dup])
  have gsdmup: "((\<lambda>t. gsincd (up t)) has_real_derivative
                  gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) (at \<theta>)"
    by (rule DERIV_chain2[OF gsincd_has_deriv[OF up0] dup])
  have pref: "((\<lambda>t. (pi/2) * sin t) has_real_derivative ((pi/2) * cos \<theta>)) (at \<theta>)"
    by (auto intro!: derivative_eq_intros)
  have br1: "((\<lambda>t. gsincd (um t) * gsinc (up t)) has_real_derivative
               gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                + gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsincd (um \<theta>)) (at \<theta>)"
    by (rule DERIV_mult[OF gsdmum gsmup])
  have br2: "((\<lambda>t. gsinc (um t) * gsincd (up t)) has_real_derivative
               gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                + gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsinc (um \<theta>)) (at \<theta>)"
    by (rule DERIV_mult[OF gsmum gsdmup])
  have br: "((\<lambda>t. gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))
              has_real_derivative
              ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                 + gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsincd (um \<theta>) )
              - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                 + gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsinc (um \<theta>) )) (at \<theta>)"
    by (rule DERIV_diff[OF br1 br2])
  define BR where
    "BR = ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                 + gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsincd (um \<theta>) )
              - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                 + gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>)) * gsinc (um \<theta>) )"
  define BV where
    "BV = gsincd (um \<theta>) * gsinc (up \<theta>) - gsinc (um \<theta>) * gsincd (up \<theta>)"
  have brBR: "((\<lambda>t. gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))
                 has_real_derivative BR) (at \<theta>)"
    unfolding BR_def by (rule br)
  have prod: "((\<lambda>t. ((pi/2) * sin t)
                    * (gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t)))
                 has_real_derivative
                 (pi/2) * cos \<theta> * BV + BR * ((pi/2) * sin \<theta>)) (at \<theta>)"
    unfolding BV_def by (rule DERIV_mult[OF pref brBR])
  have D1f_reassoc: "D1f = (\<lambda>t. pi^2/4 * (((pi/2) * sin t)
                    * (gsincd (um t) * gsinc (up t) - gsinc (um t) * gsincd (up t))))"
    by (rule ext) (simp add: D1f_def mult.assoc)
  have raw: "(D1f has_real_derivative
                pi^2/4 * ((pi/2) * cos \<theta> * BV + BR * ((pi/2) * sin \<theta>))) (at \<theta>)"
    unfolding D1f_reassoc by (rule DERIV_cmult[OF prod])
  have eqval: "pi^2/4 * ((pi/2) * cos \<theta> * BV + BR * ((pi/2) * sin \<theta>))
       = pi^2/4 *
           ( (pi/2) * cos \<theta>
              * (gsincd (um \<theta>) * gsinc (up \<theta>) - gsinc (um \<theta>) * gsincd (up \<theta>))
            + (pi/2) * sin \<theta>
              * ( ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                     + gsincd (um \<theta>) * (gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) )
                  - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                     + gsinc (um \<theta>) * (gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) ) ))"
    unfolding BR_def BV_def by (simp add: algebra_simps)
  show ?thesis using raw unfolding eqval .
qed

lemma gdip_second_deriv_at_cos_zero:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0" and cz: "cos \<theta> = 0"
  shows "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative
            (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)) (at \<theta>)"
proof -
  have umpi: "um \<theta> = pi/2" using cz by (simp add: um_def)
  have uppi: "up \<theta> = pi/2" using cz by (simp add: up_def)
  have pih: "(pi/2::real) \<noteq> 0" using pi_gt_zero by simp
  have um0: "um \<theta> \<noteq> 0" unfolding umpi by (rule pih)
  have up0: "up \<theta> \<noteq> 0" unfolding uppi by (rule pih)
  define V where
    "V = pi^2/4 *
           ( (pi/2) * cos \<theta>
              * (gsincd (um \<theta>) * gsinc (up \<theta>) - gsinc (um \<theta>) * gsincd (up \<theta>))
            + (pi/2) * sin \<theta>
              * ( ( gsincdd (um \<theta>) * ((pi/2) * sin \<theta>) * gsinc (up \<theta>)
                     + gsincd (um \<theta>) * (gsincd (up \<theta>) * (- ((pi/2) * sin \<theta>))) )
                  - ( gsincd (um \<theta>) * ((pi/2) * sin \<theta>) * gsincd (up \<theta>)
                     + gsinc (um \<theta>) * (gsincdd (up \<theta>) * (- ((pi/2) * sin \<theta>))) ) ))"
  have d1: "(D1f has_real_derivative V) (at \<theta>)"
    unfolding V_def by (rule D1f_has_deriv[OF um0 up0])
  have openS: "open {x::real. sin x \<noteq> 0}"
    using continuous_on_id continuous_on_sin
    by (subst open_Collect_neq, auto, simp add: continuous_at_imp_continuous_on)
  have memS: "\<theta> \<in> {x::real. sin x \<noteq> 0}" using s0 by simp
  have agree: "D1f x = frechet_derivative gdip (at x) 1" if "x \<in> {x. sin x \<noteq> 0}" for x
    using that by (simp add: gdip_deriv_field_eq_D1f)
  have d2: "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative V) (at \<theta>)"
    by (rule has_field_derivative_transform_within_open[OF d1 openS memS agree])
  have sin2: "(sin \<theta>)^2 = 1" using cz sin_cos_squared_add[of \<theta>] by simp
  have Veq: "V = (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)"
  proof -
    have "V = pi^2/4 * (((pi/2) * sin \<theta>)
              * ( (gsincdd (pi/2) * ((pi/2) * sin \<theta>)) * gsinc (pi/2)
                 + gsincd (pi/2) * (gsincd (pi/2) * (- ((pi/2) * sin \<theta>)))
                 - ( (gsincd (pi/2) * ((pi/2) * sin \<theta>)) * gsincd (pi/2)
                    + gsinc (pi/2) * (gsincdd (pi/2) * (- ((pi/2) * sin \<theta>))) )))"
      unfolding V_def umpi uppi using cz by simp
    also have "\<dots> = pi^2/4 * ((pi/2) * sin \<theta>) * ((pi/2) * sin \<theta>)
                      * (2 * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2))"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = pi^2/4 * ((pi/2)^2 * (sin \<theta>)^2)
                      * (2 * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2))"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = pi^2/4 * ((pi/2)^2 * 1)
                      * (2 * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2))"
      unfolding sin2 by simp
    also have "\<dots> = (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)"
      by (simp add: power2_eq_square power4_eq_xxxx field_simps)
    finally show ?thesis .
  qed
  show ?thesis using d2 unfolding Veq .
qed

lemma gsinc_pi_half: "gsinc (pi/2) = 2/pi"
  using pi_gt_zero by (simp add: gsinc_def)

lemma gsincd_pi_half: "gsincd (pi/2) = - (4/pi^2)"
  using pi_gt_zero by (simp add: gsincd_def power2_eq_square field_simps)

lemma gsincdd_pi_half: "gsincdd (pi/2) = 16/pi^3 - 2/pi"
proof -
  have "gsincdd (pi/2) = (- ((pi/2)^2) * 1 - 2 * (pi/2) * 0 + 2 * 1) / (pi/2)^3"
    by (simp add: gsincdd_def)
  also have "\<dots> = (2 - pi^2/4) / (pi^3/8)"
    by (simp add: power2_eq_square power3_eq_cube field_simps)
  also have "\<dots> = 16/pi^3 - 2/pi"
    using pi_gt_zero by (simp add: power2_eq_square power3_eq_cube field_simps)
  finally show ?thesis .
qed

lemma gdip_secondderiv_value:
  "(pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2) = (16 - 4*pi^2)/8"
proof -
  have br: "gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2 = 16/pi^4 - 4/pi^2"
    unfolding gsinc_pi_half gsincd_pi_half gsincdd_pi_half
    using pi_gt_zero
    by (simp add: power2_eq_square power3_eq_cube power4_eq_xxxx field_simps)
  have "(pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)
      = (pi^4/8) * (16/pi^4 - 4/pi^2)"
    unfolding br by simp
  also have "\<dots> = (16 - 4*pi^2)/8"
    using pi_gt_zero by (simp add: power4_eq_xxxx power2_eq_square field_simps)
  finally show ?thesis .
qed

lemma gdip_secondderiv_value_nonzero: "(16 - 4*pi^2)/8 \<noteq> (0::real)"
proof -
  have "(2::real) < pi" using pi_gt3 by simp
  hence "(2::real)^2 < pi^2"
    by (rule power_strict_mono) auto
  hence "(16::real) < 4 * pi^2" by (simp add: power2_eq_square)
  thus ?thesis by simp
qed

text \<open>The scalar second derivative of \<open>gdip\<close> at a cos-zero is nonzero.\<close>

lemma gdip_scalar_second_deriv_nonzero:
  fixes \<theta> :: real
  assumes s0: "sin \<theta> \<noteq> 0" and cz: "cos \<theta> = 0"
  shows "frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at \<theta>) 1 \<noteq> 0"
proof -
  have hd: "((\<lambda>t. frechet_derivative gdip (at t) 1) has_real_derivative
              (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)) (at \<theta>)"
    by (rule gdip_second_deriv_at_cos_zero[OF s0 cz])
  have "frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at \<theta>) 1
       = (pi^4/8) * (gsincdd (pi/2) * gsinc (pi/2) - (gsincd (pi/2))^2)"
    by (rule g1_frechet_eval[OF hd])
  also have "\<dots> = (16 - 4*pi^2)/8" by (rule gdip_secondderiv_value)
  finally show ?thesis using gdip_secondderiv_value_nonzero by simp
qed


subsection \<open>The beam-center (\<open>c = 0\<close>) Hessian collapse and the det moment polynomial\<close>

text \<open>\<^bold>\<open>Moments at the beam center \<open>c = 0\<close> are real.\<close>  At \<open>c = 0\<close> every phase factor is \<open>1\<close>,
  so \<open>Afun x 0 = N\<close> (\<open>N = CARD('n)\<close>) and \<open>Mcfun x 0 k\<close>, \<open>M2cfun x 0 k l\<close> are real coordinate
  (second-)moment sums.\<close>

lemma Afun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "Afun x (0::real^2) = of_nat CARD('n)"
  by (simp add: Afun_def)

lemma Mcfun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "Mcfun x (0::real^2) k = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)"
  by (simp add: Mcfun_def)

lemma M2cfun_at_zero:
  fixes x :: "(real^2)^'n"
  shows "M2cfun x (0::real^2) k l
     = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)"
  by (simp add: M2cfun_def)

text \<open>The \<open>c\<close>-gradient of \<open>|A|\<^sup>2\<close> vanishes at the beam center (\<open>|A|\<^sup>2\<close> is critical at \<open>c = 0\<close>:
  the array factor is maximal there).  Real moments \<open>\<Rightarrow>\<close> the steering term \<open>Re(cnj A \<cdot> (-\<ii>)real)\<close>
  is the real part of a purely imaginary number.\<close>

lemma gradUc_at_zero:
  fixes x :: "(real^2)^'n"
  shows "gradU (\<lambda>c. c) (\<lambda>_. 1) x (0::real^2) = 0"
proof -
  have comp: "gradU (\<lambda>c. c) (\<lambda>_. 1) x (0::real^2) $ j = 0" for j
  proof -
    have A0: "M_paper x 0 $ 1 = complex_of_real (real CARD('n))"
      by (simp add: A_moment_def phase_def)
    have M20: "M_paper x 0 $ 2 = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
      by (simp add: M1_moment_def phase_def)
    have M30: "M_paper x 0 $ 3 = complex_of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
      by (simp add: M2_moment_def phase_def)
    have Ar: "M_paper x 0 $ 1 = of_real (Re (M_paper x 0 $ 1))" by (subst A0)+ simp
    have M2r: "M_paper x 0 $ 2 = of_real (Re (M_paper x 0 $ 2))" by (subst M20)+ simp
    have M3r: "M_paper x 0 $ 3 = of_real (Re (M_paper x 0 $ 3))" by (subst M30)+ simp
    have steer0: "Re (cnj (M_paper x 0 $ 1)
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * (M_paper x 0 $ 2)
             + (- \<i>) * complex_of_real ((axis j 1)$2) * (M_paper x 0 $ 3))) = 0"
    proof -
      have "cnj (M_paper x 0 $ 1)
          * ((- \<i>) * complex_of_real ((axis j 1)$1) * (M_paper x 0 $ 2)
           + (- \<i>) * complex_of_real ((axis j 1)$2) * (M_paper x 0 $ 3))
          = of_real (Re (M_paper x 0 $ 1))
            * ((- \<i>) * complex_of_real ((axis j 1)$1) * of_real (Re (M_paper x 0 $ 2))
             + (- \<i>) * complex_of_real ((axis j 1)$2) * of_real (Re (M_paper x 0 $ 3)))"
        by (subst Ar, subst M2r, subst M3r) (simp only: Complex.complex_cnj_complex_of_real)
      also have "\<dots> = complex_of_real (Re (M_paper x 0 $ 1)
                       * ((axis j 1)$1 * Re (M_paper x 0 $ 2)
                        + (axis j 1)$2 * Re (M_paper x 0 $ 3))) * (- \<i>)"
        by (simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    show ?thesis
      using gradUc_component_moments[of x 0 j] steer0 by simp
  qed
  show ?thesis by (simp add: Finite_Cartesian_Product.vec_eq_iff comp)
qed

text \<open>\<^bold>\<open>The directional second derivative of the gain field is \<open>e\<^sub>1\<close>-only.\<close>  The first-derivative
  field \<open>\<eta> \<mapsto> \<partial>gdip(\<eta>\<^sub>1) 1\<close> factors through the projection \<open>\<eta> \<mapsto> \<eta>\<^sub>1\<close>, so its Fréchet
  derivative in direction \<open>h\<close> is \<open>h\<^sub>1 \<cdot> gdip''(\<omega>\<^sub>1)\<close>.  (Re-proof of the gdip2 projection bridge,
  generalised to an arbitrary direction.)\<close>

lemma gdip_field_frechet:
  fixes \<omega> h :: "real^2"
  shows "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>) h
       = (h$1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
proof -
  have d1: "(\<lambda>t. frechet_derivative gdip (at t) 1) differentiable (at (\<omega>$1))"
    by (rule gdip_deriv_differentiable)
  obtain D where D: "((\<lambda>t. frechet_derivative gdip (at t) 1) has_derivative D) (at (\<omega>$1))"
    using d1 unfolding differentiable_def by blast
  have proj: "((\<lambda>\<eta>::real^2. \<eta>$1) has_derivative (\<lambda>h. h$1)) (at \<omega>)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_ident])
  have "((\<lambda>t. frechet_derivative gdip (at t) 1) \<circ> (\<lambda>\<eta>::real^2. \<eta>$1) has_derivative
            (D \<circ> (\<lambda>h. h$1))) (at \<omega>)"
    by (rule diff_chain_at[OF proj D])
  hence hd: "((\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) has_derivative
            (\<lambda>h. D (h$1))) (at \<omega>)"
    by (simp add: o_def)
  have Deq: "D = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1))"
    by (rule frechet_derivative_at[OF D])
  have fd: "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>)
          = (\<lambda>h. D (h$1))"
    by (rule frechet_derivative_at[symmetric, OF hd])
  have lin: "linear D" by (rule has_derivative_linear[OF D])
  have "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1) (at \<omega>) h
        = D (h$1)" by (subst fd) (rule refl)
  also have "\<dots> = (h$1) *\<^sub>R D 1" using linear_cmul[OF lin, of "h$1" 1] by simp
  also have "\<dots> = (h$1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
    using fun_cong[OF Deq, of 1] by simp
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The beam-center Hessian entry collapse.\<close>  At \<open>c = 0\<close> the \<open>c\<close>-gradient terms of
  @{thm HessU_dip_entry_moments} drop (@{thm gradUc_at_zero}), leaving the curvature quadratic
  form (\<open>Hcmat x 0\<close>) plus the gain-Hessian term, which is \<open>e\<^sub>1e\<^sub>1\<^sup>T\<close>-supported:
  \<open>HessU x \<omega> $ k $ l = gain \<cdot> Dcvec(e\<^sub>k) \<bullet> Hcmat x 0 (Dcvec(e\<^sub>l)) + (e_k)\<^sub>1 (e_l)\<^sub>1 gdip''(\<omega>\<^sub>1) N\<^sup>2\<close>.\<close>

lemma HessU_beamcenter_entry:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))
       + ((axis k 1)$1) * ((axis l 1)$1)
           * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1
           * (real CARD('n))\<^sup>2"
proof -
  have g0: "gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    unfolding c0 by (rule gradUc_at_zero)
  have U0: "U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>) = (real CARD('n))\<^sup>2"
  proof -
    have "U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>) = (cmod (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2"
      by (rule Uc_eq_moment)
    also have "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_nat CARD('n)"
      unfolding c0 by (simp add: A_moment_def phase_def)
    finally show ?thesis by (simp add: norm_of_nat)
  qed
  \<comment> \<open>the gain-Hessian field directional second derivative, in direction \<open>axis l 1\<close>,
      of the \<open>k\<close>-scaled gain derivative.  Scale the constant \<open>(axis k 1)\<^sub>1\<close> out of the
      \<open>\<eta>\<close>-field, then apply the projection bridge @{thm gdip_field_frechet}.\<close>
  have field_lin: "frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)
                 = ((axis k 1)$1) * frechet_derivative gdip (at (\<eta>$1)) 1" for \<eta> :: "real^2"
    using linear_cmul[OF has_derivative_linear[OF frechet_derivative_works[THEN iffD1,
            OF gdip_differentiable]], of "(axis k 1)$1" 1]
    by (simp add: cart_eq_inner_axis frechet_gdip_zero_arg inner_axis_axis)
  define F where "F = (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) 1)"
  have Fdiff: "F differentiable (at \<omega>)"
  proof -
    have proj: "(\<lambda>\<eta>::real^2. \<eta>$1) differentiable (at \<omega>)"
      by (simp add: bounded_linear_vec_nth bounded_linear_imp_differentiable)
    have sc: "(\<lambda>t. frechet_derivative gdip (at t) 1) differentiable (at (\<omega>$1))"
      by (rule gdip_deriv_differentiable)
    show ?thesis unfolding F_def
      using differentiable_chain_at[OF proj sc] by (simp add: o_def)
  qed
  have FD: "(F has_derivative frechet_derivative F (at \<omega>)) (at \<omega>)"
    using Fdiff frechet_derivative_works by blast
  have cF: "((\<lambda>\<eta>. F \<eta> * ((axis k 1)$1)) has_derivative
              (\<lambda>h. frechet_derivative F (at \<omega>) h * ((axis k 1)$1))) (at \<omega>)"
    by (rule has_derivative_mult_left[OF FD])
  have gainH: "frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
       = ((axis k 1)$1) * ((axis l 1)$1)
           * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
  proof -
    have e: "(\<lambda>\<eta>::real^2. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1))
        = (\<lambda>\<eta>. F \<eta> * ((axis k 1)$1))"
      unfolding F_def by (rule ext) (simp add: field_lin mult.commute)
    have "frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
         = frechet_derivative F (at \<omega>) (axis l 1) * ((axis k 1)$1)"
      unfolding e using frechet_derivative_at[OF cF] by metis 
    also have "frechet_derivative F (at \<omega>) (axis l 1)
         = ((axis l 1)$1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1"
      unfolding F_def by (rule gdip_field_frechet)
    finally show ?thesis by (simp only: mult.assoc mult.commute)
  qed
  have Hc0: "Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) = Hcmat x 0" unfolding c0 by (rule refl)
  have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = (gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x (cvec_dip \<omega>0 \<omega>s \<omega>) *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
                        + (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1))
                          \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative gdip (at (\<omega>$1)) ((axis l 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>)))
        + (frechet_derivative gdip (at (\<omega>$1)) ((axis k 1)$1)
            * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))
          + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (\<eta>$1)) ((axis k 1)$1)) (at \<omega>) (axis l 1)
            * U_cart (\<lambda>c. c) (\<lambda>_. 1) x (cvec_dip \<omega>0 \<omega>s \<omega>))"
    by (rule HessU_dip_entry_moments)
  also have "\<dots> = gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                          \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))))
       + ((axis k 1)$1) * ((axis l 1)$1)
           * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1
           * (real CARD('n))\<^sup>2"
    by (simp only: g0 U0 gainH Hc0 inner_zero_right add_0_right add_0 mult_zero_right) 
  finally show ?thesis .
qed


subsection \<open>The beam-center det-Hessian as an entire, continuous moment polynomial in \<open>x\<close>\<close>

text \<open>\<^bold>\<open>The curvature matrix entry at \<open>c = 0\<close> in real moment form.\<close>
  \<open>Hcmat x 0 $ k $ l = 2 ((\<Sum>x\<^sub>l)(\<Sum>x\<^sub>k) - N (\<Sum>x\<^sub>k x\<^sub>l))\<close> --- a real degree-2 polynomial in
  the configuration coordinates.\<close>

lemma Hcmat_at_zero_entry:
  fixes x :: "(real^2)^'n"
  shows "Hcmat x (0::real^2) $ k $ l
       = 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
proof -
  have "Hcmat x (0::real^2) $ k $ l
      = 2 * (Re (cnj (Mcfun x 0 l) * Mcfun x 0 k) - Re (cnj (Afun x 0) * M2cfun x 0 k l))"
    by (simp add: Hcmat_def)
  also have "\<dots> = 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
    by (simp add: Mcfun_at_zero M2cfun_at_zero Afun_at_zero)
  finally show ?thesis .
qed

text \<open>The curvature entry is \<open>rline_entire\<close> (entire on every line) and continuous in \<open>x\<close>.\<close>

lemma rline_entire_Hcmat_at_zero:
  shows "rline_entire (\<lambda>x::(real^2)^'n. Hcmat x (0::real^2) $ k $ l)"
proof -
  have c1: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). (x $ n) $ l)"
    by (intro rline_entire_sum) (auto intro: rline_entire_coord)
  have c2: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)"
    by (intro rline_entire_sum) (auto intro: rline_entire_coord)
  have c3: "rline_entire (\<lambda>x::(real^2)^'n. \<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)"
    by (intro rline_entire_sum) (auto intro!: rline_entire_mult rline_entire_coord)
  have prod12: "rline_entire (\<lambda>x::(real^2)^'n.
                  (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k))"
    by (rule rline_entire_mult[OF c1 c2])
  have scaled: "rline_entire (\<lambda>x::(real^2)^'n.
                  real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
    by (rule rline_entire_scale[OF c3])
  have diff: "rline_entire (\<lambda>x::(real^2)^'n.
                  (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
                - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l))"
    using rline_entire_add[OF prod12 rline_entire_scale[OF scaled, of "-1"]]
    by (simp add: field_simps)
  have eq: "(\<lambda>x::(real^2)^'n. Hcmat x (0::real^2) $ k $ l)
          = (\<lambda>x. 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)))"
    by (rule ext) (rule Hcmat_at_zero_entry)
  show ?thesis unfolding eq by (rule rline_entire_scale[OF diff])
qed

lemma continuous_Hcmat_at_zero:
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. (Hcmat x (0::real^2) $ k $ l :: real))"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. Hcmat x (0::real^2) $ k $ l)
          = (\<lambda>x. 2 * ((\<Sum>n\<in>(UNIV::'n set). (x $ n) $ l) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k)
              - real CARD('n) * (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ k * (x $ n) $ l)))"
    by (rule ext) (rule Hcmat_at_zero_entry)
  show ?thesis
    unfolding eq
    by (intro continuous_intros
          bounded_linear.continuous_on[OF bounded_linear_compose
            [OF bounded_linear_vec_nth bounded_linear_vec_nth]])
qed

text \<open>\<^bold>\<open>The beam-center Hessian entry, as a function of \<open>x\<close>, is entire on lines and continuous.\<close>
  Expand the quadratic form @{thm HessU_beamcenter_entry} over the \<open>2\<close>-dimensional inner
  product / mat-vec; each summand is a constant (the steering jet / gain / gain-curvature)
  times a curvature entry @{thm rline_entire_Hcmat_at_zero}.\<close>

lemma HessU_beamcenter_entry_expand:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l
       = gain_dip \<omega> * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ i * Hcmat x 0 $ i $ j * Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ j)
       + (axis k 1 $ 1) * (axis l 1 $ 1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
proof -
  have "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> (Hcmat x 0 *v (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ i * Hcmat x 0 $ i $ j * Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ j)"
    unfolding inner_vec_def matrix_vector_mult_def by (simp add: sum_distrib_left mult.assoc)
  thus ?thesis unfolding HessU_beamcenter_entry[OF c0] by simp
qed

lemma rline_entire_HessU_beamcenter_entry:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "rline_entire (\<lambda>x::(real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l)"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l)
      = (\<lambda>x. gain_dip \<omega> * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ i * Hcmat x 0 $ i $ j * Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ j)
       + (axis k 1 $ 1) * (axis l 1 $ 1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2)"
    by (rule ext) (rule HessU_beamcenter_entry_expand[OF c0])
  have fin: "finite (UNIV :: 2 set)" by simp
  show ?thesis unfolding eq
    by (intro rline_entire_add rline_entire_scale rline_entire_sum[OF fin] rline_entire_mult rline_entire_Hcmat_at_zero rline_entire_const)
qed

lemma continuous_HessU_beamcenter_entry:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l :: real))"
proof -
  have eq: "(\<lambda>x::(real^2)^'n. (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l :: real))
      = (\<lambda>x. gain_dip \<omega> * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) $ i * Hcmat x 0 $ i $ j * Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) $ j)
       + (axis k 1 $ 1) * (axis l 1 $ 1) * frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2)"
    by (rule ext) (rule HessU_beamcenter_entry_expand[OF c0])
  have fin: "finite (UNIV :: 2 set)" by simp
  show ?thesis
    unfolding eq by (intro continuous_intros continuous_on_sum fin continuous_Hcmat_at_zero)
qed

text \<open>\<^bold>\<open>The beam-center det-Hessian is entire-on-lines and continuous in \<open>x\<close>\<close> --- via the \<open>2\<times>2\<close>
  determinant expansion @{thm det_2} and the entry lemmas.\<close>

lemma rline_entire_det_HessU_beamcenter:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "rline_entire (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
  by (rule rline_entire_det_fun) (rule rline_entire_HessU_beamcenter_entry[OF c0])

lemma continuous_det_HessU_beamcenter:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "continuous_on UNIV (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
proof -
  have d2: "(\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))
      = (\<lambda>x. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
             * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
           - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
             * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1)"
    by (rule ext) (simp add: det_2)
  show ?thesis
    unfolding d2 by (intro continuous_intros continuous_HessU_beamcenter_entry[OF c0])
qed


subsection \<open>Nontriviality: a one-displaced-element witness with \<open>det HessU \<noteq> 0\<close>\<close>

text \<open>\<^bold>\<open>The rank-one curvature witness.\<close>  Put one element at a point \<open>p\<close> not orthogonal to the
  second steering column \<open>col2 = Dcvec(e\<^sub>2)\<close>; the others at the origin.  Then every moment is a
  single-element moment, so \<open>Hcmat xs 0 = 2(1 - N) p p\<^sup>T\<close> is rank one.  Writing \<open>u = p \<bullet> col1\<close>,
  \<open>v = p \<bullet> col2\<close>, \<open>\<alpha> = gain \<cdot> 2(1 - N)\<close>, \<open>\<gamma> = gdip''(\<omega>\<^sub>1) N\<^sup>2\<close>, the four Hessian entries are
  \<open>H\<^sub>1\<^sub>1 = \<alpha> u\<^sup>2 + \<gamma>\<close>, \<open>H\<^sub>1\<^sub>2 = H\<^sub>2\<^sub>1 = \<alpha> u v\<close>, \<open>H\<^sub>2\<^sub>2 = \<alpha> v\<^sup>2\<close>, whence
  \<open>det HessU = (\<alpha> u\<^sup>2 + \<gamma>)(\<alpha> v\<^sup>2) - (\<alpha> u v)\<^sup>2 = \<gamma> \<alpha> v\<^sup>2\<close> --- nonzero since \<open>\<gamma> \<noteq> 0\<close> (cos-zero,
  @{thm gdip_scalar_second_deriv_nonzero}), \<open>gain \<noteq> 0\<close>, \<open>1 - N \<noteq> 0\<close> (\<open>N \<ge> 6\<close>), \<open>v \<noteq> 0\<close>.\<close>

lemma det_HessU_beamcenter_witness:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" and cz: "cos (\<omega> $ 1) = 0"
  shows "\<exists>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
proof -
  define col1 where "col1 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)"
  define col2 where "col2 = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  have c2nz: "col2 \<noteq> 0" unfolding col2_def by (rule Dcvec_col2_nz[OF pfw])
  define p :: "real^2" where "p = col2"
  have vp: "p \<bullet> col2 \<noteq> 0" unfolding p_def using c2nz by simp
  define i0 :: 'n where "i0 = undefined"
  define xs :: "(real^2)^'n" where "xs = (\<chi> n. if n = i0 then p else 0)"
  \<comment> \<open>single-element moment sums\<close>
  have sumk: "(\<Sum>n\<in>(UNIV::'n set). (xs $ n) $ k) = p $ k" for k :: 2
  proof -
    have "(\<Sum>n\<in>(UNIV::'n set). (xs $ n) $ k)
        = (xs $ i0) $ k + (\<Sum>n\<in>(UNIV::'n set) - {i0}. (xs $ n) $ k)"
      by (rule sum.remove) simp_all
    also have "(\<Sum>n\<in>(UNIV::'n set) - {i0}. (xs $ n) $ k) = 0"
      by (rule sum.neutral) (simp add: xs_def)
    finally show ?thesis by (simp add: xs_def)
  qed
  have sumkl: "(\<Sum>n\<in>(UNIV::'n set). (xs $ n) $ k * (xs $ n) $ l) = p $ k * p $ l" for k l :: 2
  proof -
    have "(\<Sum>n\<in>(UNIV::'n set). (xs $ n) $ k * (xs $ n) $ l)
        = (xs $ i0) $ k * (xs $ i0) $ l + (\<Sum>n\<in>(UNIV::'n set) - {i0}. (xs $ n) $ k * (xs $ n) $ l)"
      by (rule sum.remove) simp_all
    also have "(\<Sum>n\<in>(UNIV::'n set) - {i0}. (xs $ n) $ k * (xs $ n) $ l) = 0"
      by (rule sum.neutral) (simp add: xs_def)
    finally show ?thesis by (simp add: xs_def)
  qed
  \<comment> \<open>the rank-one curvature matrix at the witness\<close>
  define N1 where "N1 = 2 * (1 - real CARD('n))"
  have Hc: "Hcmat xs 0 $ k $ l = N1 * (p $ k * p $ l)" for k l :: 2
    using Hcmat_at_zero_entry[of xs k l] unfolding sumk sumkl N1_def
    by (simp add: algebra_simps)
  \<comment> \<open>scalar abbreviations\<close>
  define g where "g = gain_dip \<omega>"
  define u where "u = col1 $ 1 * p $ 1 + col1 $ 2 * p $ 2"
  define v where "v = col2 $ 1 * p $ 1 + col2 $ 2 * p $ 2"
  define \<gamma> where "\<gamma> = frechet_derivative (\<lambda>t. frechet_derivative gdip (at t) 1) (at (\<omega>$1)) 1
                    * (real CARD('n))\<^sup>2"
  \<comment> \<open>the four Hessian entries at the witness\<close>
  have H11: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 1 $ 1 = g * (N1 * u * u) + \<gamma>"
    unfolding HessU_beamcenter_entry_expand[OF c0] Hc col1_def[symmetric] col2_def[symmetric]
              g_def[symmetric] u_def \<gamma>_def
    by (simp add: sum_2 axis_def algebra_simps)
  have H12: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 1 $ 2 = g * (N1 * u * v)"
    unfolding HessU_beamcenter_entry_expand[OF c0] Hc col1_def[symmetric] col2_def[symmetric]
              g_def[symmetric] u_def v_def
    by (simp add: sum_2 axis_def algebra_simps)
  have H21: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 2 $ 1 = g * (N1 * u * v)"
    unfolding HessU_beamcenter_entry_expand[OF c0] Hc col1_def[symmetric] col2_def[symmetric]
              g_def[symmetric] u_def v_def
    by (simp add: sum_2 axis_def algebra_simps)
  have H22: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 2 $ 2 = g * (N1 * v * v)"
    unfolding HessU_beamcenter_entry_expand[OF c0] Hc col1_def[symmetric] col2_def[symmetric]
              g_def[symmetric] v_def
    by (simp add: sum_2 axis_def algebra_simps)
  \<comment> \<open>the determinant collapses to \<open>\<gamma> g N1 v\<^sup>2\<close>\<close>
  have detval: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>) = \<gamma> * (g * (N1 * (v * v)))"
  proof -
    have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>)
        = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 1 $ 1 * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 2 $ 2
        - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 1 $ 2 * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega> $ 2 $ 1"
      by (simp add: det_2)
    also have "\<dots> = (g * (N1 * u * u) + \<gamma>) * (g * (N1 * v * v))
                  - (g * (N1 * u * v)) * (g * (N1 * u * v))"
      unfolding H11 H12 H21 H22 by (rule refl)
    also have "\<dots> = \<gamma> * (g * (N1 * (v * v)))"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>each factor is nonzero\<close>
  have \<gamma>nz: "\<gamma> \<noteq> 0"
    unfolding \<gamma>_def using gdip_scalar_second_deriv_nonzero[OF pfw cz] c6 by simp
  have gnz: "g \<noteq> 0" unfolding g_def by (rule gain_dip_nonzero_of_sin[OF pfw])
  have N1nz: "N1 \<noteq> 0" unfolding N1_def using c6 by simp
  have vnz: "v \<noteq> 0" using vp unfolding v_def by (simp add: inner_vec_def sum_2 mult.commute)
  have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip xs \<omega>) \<noteq> 0"
    unfolding detval using \<gamma>nz gnz N1nz vnz by simp
  thus ?thesis by blast
qed


subsection \<open>The genuine per-angle beam-center obligation (D2-style polynomial)\<close>

text \<open>The \<open>c = 0\<close> sub-case of a witness angle.  When \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close> the moment-map
  derivative \<open>DM_paper_x x 0\<close> is never surjective (@{thm DM_paper_x_null_not_surj}), so the
  D5 slice degenerates to the D2 beam-center slice at \<open>\<omega>\<close>:
  \<open>{x. gradU = 0 \<and> A \<noteq> 0 \<and> det HessU = 0}\<close>.  Its meagerness is the beam-center det-Hessian
  covariance-polynomial argument: \<open>det HessU\<close> is a continuous, entire-on-lines moment polynomial
  in \<open>x\<close> (@{thm continuous_det_HessU_beamcenter}, @{thm rline_entire_det_HessU_beamcenter}); when
  \<open>cos(\<omega>\<^sub>1) = 0\<close> it is not identically zero (@{thm det_HessU_beamcenter_witness}, nontrivial
  because \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close>), so its zero set is nowhere dense and the slice
  (contained in it) is meager; when \<open>cos(\<omega>\<^sub>1) \<noteq> 0\<close> the slice is EMPTY because criticality
  \<open>gradU\<^sub>1 = gdip'(\<omega>\<^sub>1) N\<^sup>2 \<noteq> 0\<close> fails (the M6-empty mirror).  Now \<^emph>\<open>discharged\<close>.\<close>

lemma m5_D5_beamcenter_angle_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
proof (cases "cos (\<omega> $ 1) = 0")
  case False
  \<comment> \<open>\<open>cos(\<omega>\<^sub>1) \<noteq> 0\<close>: criticality fails for ALL \<open>x\<close> (the M6-empty mirror), so the set is empty.\<close>
  have gd: "frechet_derivative gdip (at (\<omega>$1)) 1 \<noteq> 0"
    using gdip_deriv_zero_iff[OF pfw] False by blast
  have empty: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0} = {}"
  proof (rule equals0I)
    fix x :: "(real^2)^'n"
    assume "x \<in> {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    hence g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    \<comment> \<open>component 1 of the beam-center gradient is \<open>gdip'(\<omega>\<^sub>1) N\<^sup>2\<close>\<close>
    have a1: "((axis (1::2) 1 :: real^2) $ 1) = 1" by (simp add: axis_def)
    have NA: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_nat CARD('n)"
      unfolding c0 by (simp add: A_moment_def phase_def)
    have steer0: "Re (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
            * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1) * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
             + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2) * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))) = 0"
    proof -
      have M1r: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2 = of_real (Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2))"
        unfolding c0 by (simp add: M1_moment_def phase_def)
      have M2r: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3 = of_real (Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))"
        unfolding c0 by (simp add: M2_moment_def phase_def)
      have Ar: "M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1 = of_real (Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))"
        unfolding NA by simp
      have "cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
            * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1) * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
             + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2) * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))
          = of_real (Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
              * ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$1 * Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
               + (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))$2 * Re (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))) * (- \<i>)"
        by (subst Ar, subst M1r, subst M2r) (simp add: Complex.complex_cnj_complex_of_real algebra_simps)
      thus ?thesis by simp
    qed
    have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
        = frechet_derivative gdip (at (\<omega>$1)) ((axis (1::2) 1)$1)
            * (cmod (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2"
      using steer0 by (simp add: gradU_dip_component_moments)
    also have "\<dots> = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
      by (subst a1, subst NA) (simp add: norm_of_nat)
    finally have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2" .
    moreover have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0" using g0 by simp
    ultimately have "frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2 = 0" by simp
    moreover have "(real CARD('n))\<^sup>2 \<noteq> 0" using c6 by simp
    ultimately have "frechet_derivative gdip (at (\<omega>$1)) 1 = 0" by simp
    with gd show False by simp
  qed
  show ?thesis unfolding empty by simp
next
  case True
  \<comment> \<open>\<open>cos(\<omega>\<^sub>1) = 0\<close>: the det-Hessian moment polynomial is nontrivial, so its zero set is
       nowhere dense; the slice is contained in it, hence meager.\<close>
  have nd: "nowhere_dense {x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
  proof -
    have seq: "{x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
             = {x \<in> (UNIV::((real^2)^'n) set). det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
      by simp
    show ?thesis
      unfolding seq
    proof (rule lines_entire_slice_nowhere_dense)
      show "continuous_on UNIV (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
        by (rule continuous_det_HessU_beamcenter[OF c0])
      show "\<And>a v. \<exists>F. F holomorphic_on UNIV
              \<and> (\<forall>t::real. F (complex_of_real t)
                          = complex_of_real (det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (a + t *\<^sub>R v) \<omega>)))"
        using rline_entire_det_HessU_beamcenter[OF c0] unfolding rline_entire_def by blast
      show "\<exists>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
        by (rule det_HessU_beamcenter_witness[OF c6 pfw c0 True])
    qed
  qed
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
        \<subseteq> {x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_nowhere_dense[OF nd]])
qed


subsection \<open>Per-angle D5 slice is meager (case split on the beam center)\<close>

text \<open>For a fixed witness angle \<open>\<omega>\<close> with \<open>sin(\<omega>$1) \<noteq> 0\<close>, the D5 slice
  \<open>{x. gradU = 0 \<and> A \<noteq> 0 \<and> det HessU = 0 \<and> \<not> surj (DM_paper_x x (cvec \<omega>))}\<close> is meager.
  Case \<open>c \<noteq> 0\<close>: it injects into \<open>{x. \<not> surj (DM_paper_x x c)}\<close>, nowhere dense by the mstarg
  freebie.  Case \<open>c = 0\<close>: \<open>\<not> surj\<close> is universal, so the slice is the D2 beam-center set,
  meager by @{thm m5_D5_beamcenter_angle_meager}.\<close>

lemma m5_D5_slice_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> = 0")
  case True
  \<comment> \<open>\<open>c = 0\<close>: \<open>\<not> surj\<close> holds for all \<open>x\<close>, so the slice is the D2 beam-center set.\<close>
  have e: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
        = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    using DM_paper_x_null_not_surj[where x = _ and 'n = 'n] by (simp add: True)
  show ?thesis
    unfolding e by (rule m5_D5_beamcenter_angle_meager[OF c6 pfw True])
next
  case False
  \<comment> \<open>\<open>c \<noteq> 0\<close>: inject into the nowhere-dense moment-map set, then meager.\<close>
  have cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0" using False .
  have nd: "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    by (rule fixed_c_nonsurj_nowhere_dense[OF cnz c6])
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
        \<subseteq> {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_nowhere_dense[OF nd]])
qed


subsection \<open>D5 assembly: \<open>m5_D5_steersing\<close> (R3 confinement + finite union of slices)\<close>

text \<open>The exact target statement (verbatim from the M5 skeleton).  Proof is the M6 R3
  reduction with \<open>surj\<close> dropped: confine every bad witness angle into the finite set \<open>K\<close>
  (cos zeros \<open>\<times>\<close> phase-lattice zeros) via @{thm M6_witness_gdip_deriv_zero} and
  @{thm Dcvec_det_eq} --- neither uses surjectivity --- then take the finite union of the
  per-angle slices, each meager by @{thm m5_D5_slice_meager}.\<close>

lemma m5_D5_steersing:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
proof -
  \<comment> \<open>Phase-separation data \<open>hsep\<close>/\<open>kdiff\<close> are now lemma assumptions, supplied by the
      M5 splice (where they hold for the concrete \<open>\<omega>0 = vector[\<pi>/2,0]\<close>, \<open>\<omega>s = vector[0,0]\<close>).\<close>
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0
            \<and> Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0}"
  define slice :: "real^2 \<Rightarrow> ((real^2)^'n) set" where
    "slice \<omega> = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}" for \<omega> :: "real^2"
  text \<open>The phase coefficients are not both zero.\<close>
  have D0: "kz \<omega>s - kz \<omega>0 \<noteq> 0" using hsep by simp
  have ABnz: "Ac \<noteq> 0 \<or> Bc \<noteq> 0"
    using kdiff D0 unfolding Ac_def Bc_def by (auto simp: divide_eq_0_iff)
  text \<open>The witness-angle set \<open>K\<close> is finite.\<close>
  define S1 :: "real set" where
    "S1 = {t::real. ctr $ 1 - \<delta> \<le> t \<and> t \<le> ctr $ 1 + \<delta> \<and> cos t = 0}"
  define S2 :: "real set" where
    "S2 = {u::real. ctr $ 2 - pi \<le> u \<and> u \<le> ctr $ 2 + pi
            \<and> Ac * cos u + Bc * sin u = 0}"
  have finS1: "finite S1" unfolding S1_def by (rule finite_cos_zeros_interval)
  have finS2: "finite S2" unfolding S2_def by (rule finite_phase_zeros_interval[OF ABnz])
  have Ksub: "K \<subseteq> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
  proof
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
    have pz: "Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0" using wK by (simp add: K_def)
    have bnds: "ctr $ 1 - \<delta> \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> ctr $ 1 + \<delta>
              \<and> ctr $ 2 - pi \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> ctr $ 2 + pi"
      by (rule OmegaPF_component_bounds[OF wD])
    have mem: "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2"
      using bnds cz pz by (auto simp: S1_def S2_def)
    show "\<omega> \<in> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
    proof (rule image_eqI[where x = "(\<omega> $ 1, \<omega> $ 2)"])
      show "\<omega> = (\<lambda>(t, u). vector [t, u] :: real^2) (\<omega> $ 1, \<omega> $ 2)"
        by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
      show "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2" by (rule mem)
    qed
  qed
  have finK: "finite K"
    by (rule finite_subset[OF Ksub
          finite_imageI[OF finite_cartesian_product[OF finS1 finS2]]])
  text \<open>Witness confinement: every bad witness angle lies in \<open>K\<close>
    (R3 kernel-direction reduction --- uses NO surjectivity).\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}
             \<subseteq> (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
    then obtain \<omega> :: "real^2" where wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and hz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and ns: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      and dz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
      by blast
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    have gd0: "frechet_derivative gdip (at (\<omega> $ 1)) 1 = 0"
      by (rule M6_witness_gdip_deriv_zero[OF s1 g0 anz dz])
    have cz: "cos (\<omega> $ 1) = 0"
      by (rule iffD1[OF gdip_deriv_zero_iff[OF s1] gd0])
    have e: "sin (\<omega> $ 1) * (cos (\<omega> $ 1)
               - sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2))) = 0"
      using dz by (simp add: Dcvec_det_eq Ac_def Bc_def)
    have e2: "cos (\<omega> $ 1) - sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2)) = 0"
      using mult_eq_0_iff[THEN iffD1, OF e] s1 by blast
    have e3: "sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2)) = 0"
      using e2 cz by simp
    have q0: "Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0"
      using mult_eq_0_iff[THEN iffD1, OF e3] s1 by blast
    have wK: "\<omega> \<in> K" using wD cz q0 by (simp add: K_def)
    have xs: "x \<in> slice \<omega>" using g0 anz hz ns by (simp add: slice_def)
    show "x \<in> (\<Union>\<omega>\<in>K. slice \<omega>)"
    proof (rule UN_I)
      show "\<omega> \<in> K" by (rule wK)
      show "x \<in> slice \<omega>" by (rule xs)
    qed
  qed
  text \<open>Each slice over a fixed angle in \<open>K\<close> is meager (mstarg freebie for \<open>c \<noteq> 0\<close>,
    D2 covariance polynomial for \<open>c = 0\<close>); the finite union is meager.\<close>
  have meagU: "meager (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof (rule meager_Union_finite[OF finK])
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    show "meager (slice \<omega>)"
      unfolding slice_def
      by (rule m5_D5_slice_meager[OF c6 s1])
  qed
  show ?thesis by (rule meager_subset[OF sub meagU])
qed

(* ---- D2: beam-center stratum (consumes D5 machinery above) ---- *)

lemma M_paper_at_zero_A:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 1 = of_nat CARD('n)"
proof -
  have "A_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). cis 0)"
    by (simp add: A_moment_def phase_def)
  also have "\<dots> = of_nat CARD('n)" by simp
  finally show ?thesis by simp
qed

text \<open>At \<open>c = 0\<close> every moment is real (the phase factor is \<open>1\<close>).\<close>

lemma M_paper_at_zero_M1:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 2 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
proof -
  have "M1_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 1) * cis 0)"
    by (simp add: M1_moment_def phase_def)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 1))" by simp
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)" by simp
  finally show ?thesis by simp
qed

lemma M_paper_at_zero_M2:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 3 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
proof -
  have "M2_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 2) * cis 0)"
    by (simp add: M2_moment_def phase_def)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 2))" by simp
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)" by simp
  finally show ?thesis by simp
qed

text \<open>The first three moments are real at \<open>c = 0\<close>.\<close>

lemma M_paper_at_zero_real123:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 1 = of_real (Re (M_paper x 0 $ 1))"
    and "M_paper x 0 $ 2 = of_real (Re (M_paper x 0 $ 2))"
    and "M_paper x 0 $ 3 = of_real (Re (M_paper x 0 $ 3))"
proof -
  have e1: "M_paper x 0 $ 1 = of_real (real CARD('n))"
    using M_paper_at_zero_A[of x] by (metis of_real_of_nat_eq)
  have e2: "M_paper x 0 $ 2 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
    by (rule M_paper_at_zero_M1)
  have e3: "M_paper x 0 $ 3 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
    by (rule M_paper_at_zero_M2)
  show "M_paper x 0 $ 1 = of_real (Re (M_paper x 0 $ 1))"
    by (subst e1)+ simp
  show "M_paper x 0 $ 2 = of_real (Re (M_paper x 0 $ 2))"
    by (subst e2)+ simp
  show "M_paper x 0 $ 3 = of_real (Re (M_paper x 0 $ 3))"
    by (subst e3)+ simp
qed

section \<open>gradU at a beam center forces \<open>cos(\<omega>$1) = 0\<close>\<close>

text \<open>If \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close> then the moment-space steering term in \<open>gradU\<close>
  vanishes (real moments \<open>\<Rightarrow>\<close> the \<open>Re(cnj A \<cdot> (-\<ii>) \<cdot> real)\<close> term is \<open>0\<close>), so
  \<open>gradU $ j = gdip'(\<theta>) \<cdot> (axis j 1)$1 \<cdot> N\<^sup>2\<close>: component 2 is automatically zero,
  and component 1 vanishes iff \<open>gdip'(\<theta>) = 0\<close>.\<close>

lemma gradU_at_beamcenter_component:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
       = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
           * (cmod (M_paper x 0 $ 1))\<^sup>2"
proof -
  define A where "A = M_paper x 0 $ 1"
  define M2 where "M2 = M_paper x 0 $ 2"
  define M3 where "M3 = M_paper x 0 $ 3"
  define dj1 where "dj1 = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1"
  define dj2 where "dj2 = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2"
  have Ar: "A = of_real (Re A)" unfolding A_def by (rule M_paper_at_zero_real123(1))
  have M2r: "M2 = of_real (Re M2)" unfolding M2_def by (rule M_paper_at_zero_real123(2))
  have M3r: "M3 = of_real (Re M3)" unfolding M3_def by (rule M_paper_at_zero_real123(3))
  text \<open>The steering term: \<open>Re(cnj A \<cdot> ((-\<ii>) dj1 M2 + (-\<ii>) dj2 M3))\<close> is the real
    part of a purely-imaginary complex number, hence zero.\<close>
  have steer0: "Re (cnj A * ((- \<i>) * complex_of_real dj1 * M2
                            + (- \<i>) * complex_of_real dj2 * M3)) = 0"
  proof -
    have "cnj A * ((- \<i>) * complex_of_real dj1 * M2 + (- \<i>) * complex_of_real dj2 * M3)
        = of_real (Re A) * ((- \<i>) * complex_of_real dj1 * of_real (Re M2)
                          + (- \<i>) * complex_of_real dj2 * of_real (Re M3))"
      using Ar M2r M3r by (metis Complex.complex_cnj_complex_of_real)
    also have "\<dots> = complex_of_real (Re A * (dj1 * Re M2 + dj2 * Re M3)) * (- \<i>)"
      by (simp add: algebra_simps)
    finally have "cnj A * ((- \<i>) * complex_of_real dj1 * M2 + (- \<i>) * complex_of_real dj2 * M3)
                = complex_of_real (Re A * (dj1 * Re M2 + dj2 * Re M3)) * (- \<i>)" .
    thus ?thesis by simp
  qed
  have base: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
       = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
             * (cmod (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2
           + gain_dip \<omega> * (2 * Re (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
                * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1)
                     * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
                 + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                     * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))))"
    by (rule gradU_dip_component_moments)
  show ?thesis
    unfolding base c0
    using steer0 unfolding A_def M2_def M3_def dj1_def dj2_def by simp
qed

text \<open>The first gradient component at a beam center is \<open>gdip'(\<theta>) \<cdot> N\<^sup>2\<close>.\<close>

lemma gradU_at_beamcenter_comp1:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
       = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
proof -
  have a1: "((axis (1::2) 1 :: real^2) $ 1) = 1" by (simp add: axis_def)
  have NA: "cmod (M_paper x 0 $ 1) = real CARD('n)"
    using M_paper_at_zero_A[of x] by (simp add: norm_of_nat)
  have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
       = frechet_derivative gdip (at (\<omega>$1)) ((axis (1::2) 1)$1)
           * (cmod (M_paper x 0 $ 1))\<^sup>2"
    by (rule gradU_at_beamcenter_component[OF c0, of x 1])
  also have "\<dots> = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
    by (subst a1, subst NA, rule refl)
  finally show ?thesis .
qed

text \<open>Criticality at a beam center (off the poles) forces \<open>cos(\<omega>$1) = 0\<close>.\<close>

lemma beamcenter_critical_cos_zero:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and s1: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
    and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "cos (\<omega> $ 1) = 0"
proof -
  have Npos: "(0::real) < real CARD('n)" using c6 by simp
  have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0" using g0 by simp
  hence "frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2 = 0"
    using gradU_at_beamcenter_comp1[OF c0, of x] by simp
  hence gd0: "frechet_derivative gdip (at (\<omega>$1)) 1 = 0"
    using Npos by simp
  show ?thesis by (rule iffD1[OF gdip_deriv_zero_iff[OF s1] gd0])
qed


section \<open>Finiteness of the beam-center witness-angle set (scoped genuine-math sorry)\<close>

text \<open>\<^bold>\<open>The beam-center witness-angle set is finite.\<close>  Every witness angle \<open>\<omega>\<close> in the
  D2 bad set is \<^emph>\<open>critical\<close> (\<open>gradU = 0\<close>) at a beam center (\<open>cvec = 0\<close>) off the
  poles (\<open>sin (\<omega>\<^sub>1) \<noteq> 0\<close>), so by @{thm beamcenter_critical_cos_zero} it satisfies
  \<open>cos (\<omega>\<^sub>1) = 0\<close>.  Thus the witness angles confine to
    \<open>K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega>\<^sub>1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}\<close>.
  This set is FINITE: \<open>cos (\<omega>\<^sub>1) = 0\<close> pins \<open>\<omega>\<^sub>1\<close> to the finite cos-zero set inside the
  box (@{thm finite_cos_zeros_interval}); and at any such \<open>\<omega>\<^sub>1\<close> (where
  \<open>sin (\<omega>\<^sub>1) = \<plusminus>1\<close>, \<open>kz \<omega> = 0\<close>), the two equations \<open>cvec\<^sub>1 = cvec\<^sub>2 = 0\<close> read
  \<open>sin (\<omega>\<^sub>1) \<cdot> cos (\<omega>\<^sub>2) = P\<close>, \<open>sin (\<omega>\<^sub>1) \<cdot> sin (\<omega>\<^sub>2) = Q\<close> (constants
  \<open>P = kx \<omega>s + Ac \<cdot> kz \<omega>s\<close>, \<open>Q = ky \<omega>s + Bc \<cdot> kz \<omega>s\<close> with \<open>P\<^sup>2 + Q\<^sup>2 = sin\<^sup>2(\<omega>\<^sub>1) = 1\<close>),
  which by @{thm sin_cos_eq_iff} pin \<open>\<omega>\<^sub>2\<close> to a \<open>2\<pi>\<int>\<close>-coset --- finite inside the box
  (@{thm finite_affine_int_zeros}).  The full carve-out is the genuine remaining
  analytic step; we carry the resulting finiteness as a single scoped \<open>sorry\<close>.\<close>

lemma m5_D2_beamcenter_K_finite:
  fixes ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  shows "finite {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  \<comment> \<open>GENUINE remaining math (now discharged): at \<open>cos(\<omega>\<^sub>1)=0\<close> (so \<open>kz \<omega>=0\<close>,
      \<open>sin(\<omega>\<^sub>1)=\<plusminus>1\<close>) the two scalar equations \<open>cvec\<^sub>1=cvec\<^sub>2=0\<close> read
      \<open>sin(\<omega>\<^sub>1)\<cdot>cos(\<omega>\<^sub>2)=P\<close>, \<open>sin(\<omega>\<^sub>1)\<cdot>sin(\<omega>\<^sub>2)=Q\<close> with constants
      \<open>P=kx \<omega>s+Ac\<cdot>kz \<omega>s\<close>, \<open>Q=ky \<omega>s+Bc\<cdot>kz \<omega>s\<close> (\<open>Ac,Bc\<close> the usual ratios).
      Eliminating \<open>sin(\<omega>\<^sub>1)\<close> gives the phase relation \<open>Q\<cdot>cos(\<omega>\<^sub>2)-P\<cdot>sin(\<omega>\<^sub>2)=0\<close>;
      if \<open>P=Q=0\<close> the locus is empty (forces \<open>cos\<^sup>2+sin\<^sup>2=0\<close>), else the phase
      relation has finitely many \<open>\<omega>\<^sub>2\<close> in the box (@{thm finite_phase_zeros_interval});
      \<open>cos(\<omega>\<^sub>1)=0\<close> pins \<open>\<omega>\<^sub>1\<close> to a finite set (@{thm finite_cos_zeros_interval}).\<close>
proof -
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define P :: real where "P = kx \<omega>s + Ac * kz \<omega>s"
  define Q :: real where "Q = ky \<omega>s + Bc * kz \<omega>s"
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  \<comment> \<open>The two scalar beam-center equations at \<open>cos(\<omega>\<^sub>1)=0\<close>.\<close>
  have eqs: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P \<and> sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
    if cz: "cos (\<omega> $ 1) = 0" and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" for \<omega> :: "real^2"
  proof -
    have kzw: "kz \<omega> = 0" using cz by (simp add: kz_def)
    have c1: "cvec_dip \<omega>0 \<omega>s \<omega> $ 1 = 0" and c2: "cvec_dip \<omega>0 \<omega>s \<omega> $ 2 = 0"
      using c0 by simp_all
    have e1: "(kx \<omega> - kx \<omega>s) + Ac * (kz \<omega> - kz \<omega>s) = 0"
      using c1 unfolding cvec_dip_def Ac_def by (simp add: axis_def)
    have e2: "(ky \<omega> - ky \<omega>s) + Bc * (kz \<omega> - kz \<omega>s) = 0"
      using c2 unfolding cvec_dip_def Bc_def by (simp add: axis_def)
    have p1: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P"
      using e1 kzw unfolding P_def kx_def by (simp add: algebra_simps)
    have p2: "sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
      using e2 kzw unfolding Q_def ky_def by (simp add: algebra_simps)
    show ?thesis using p1 p2 by blast
  qed
  \<comment> \<open>The \<open>\<omega>\<^sub>1\<close> coordinate ranges over the finite cos-zero set inside the box.\<close>
  define S1 :: "real set" where
    "S1 = {t::real. ctr $ 1 - \<delta> \<le> t \<and> t \<le> ctr $ 1 + \<delta> \<and> cos t = 0}"
  have finS1: "finite S1" unfolding S1_def by (rule finite_cos_zeros_interval)
  show ?thesis
  proof (cases "P = 0 \<and> Q = 0")
    case True
    \<comment> \<open>\<open>P=Q=0\<close>: any witness forces \<open>cos(\<omega>\<^sub>2)=sin(\<omega>\<^sub>2)=0\<close>, impossible; \<open>K\<close> is empty.\<close>
    have "K = {}"
    proof (rule ccontr)
      assume "K \<noteq> {}"
      then obtain \<omega> :: "real^2" where wK: "\<omega> \<in> K" by blast
      have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
      have c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
      have s1: "sin (\<omega> $ 1) \<noteq> 0"
      proof -
        have "sin (\<omega> $ 1) ^ 2 = 1"
          using sin_cos_squared_add[of "\<omega> $ 1"] cz by simp
        thus ?thesis by (auto simp: power2_eq_square)
      qed
      have "sin (\<omega> $ 1) * cos (\<omega> $ 2) = 0" "sin (\<omega> $ 1) * sin (\<omega> $ 2) = 0"
        using eqs[OF cz c0] True by simp_all
      hence "cos (\<omega> $ 2) = 0" "sin (\<omega> $ 2) = 0" using s1 by simp_all
      thus False using sin_cos_squared_add[of "\<omega> $ 2"] by simp
    qed
    thus ?thesis by (simp flip: K_def)
  next
    case False
    hence ABnz: "Q \<noteq> 0 \<or> - P \<noteq> 0" by auto
    \<comment> \<open>\<open>\<omega>\<^sub>2\<close> ranges over the finite zero set of the phase form \<open>Q\<cdot>cos - P\<cdot>sin\<close>.\<close>
    define S2 :: "real set" where
      "S2 = {u::real. ctr $ 2 - pi \<le> u \<and> u \<le> ctr $ 2 + pi
              \<and> Q * cos u + (- P) * sin u = 0}"
    have finS2: "finite S2" unfolding S2_def by (rule finite_phase_zeros_interval[OF ABnz])
    have Ksub: "K \<subseteq> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
    proof
      fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
      have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
      have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
      have c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
      have bnds: "ctr $ 1 - \<delta> \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> ctr $ 1 + \<delta>
                \<and> ctr $ 2 - pi \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> ctr $ 2 + pi"
        by (rule OmegaPF_component_bounds[OF wD])
      have p1: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P"
        and p2: "sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
        using eqs[OF cz c0] by simp_all
      \<comment> \<open>Eliminate \<open>sin(\<omega>\<^sub>1)\<close>: \<open>Q\<cdot>cos(\<omega>\<^sub>2) - P\<cdot>sin(\<omega>\<^sub>2) = sin(\<omega>\<^sub>1)\<cdot>(Q\<cdot>cos\<cdot>... )\<close>.\<close>
      have pz: "Q * cos (\<omega> $ 2) + (- P) * sin (\<omega> $ 2) = 0"
      proof -
        have "Q * cos (\<omega> $ 2) + (- P) * sin (\<omega> $ 2)
            = (sin (\<omega> $ 1) * sin (\<omega> $ 2)) * cos (\<omega> $ 2)
            - (sin (\<omega> $ 1) * cos (\<omega> $ 2)) * sin (\<omega> $ 2)"
          by (simp add: p1[symmetric] p2[symmetric])
        also have "\<dots> = 0" by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      have mem: "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2"
        using bnds cz pz by (auto simp: S1_def S2_def)
      show "\<omega> \<in> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
      proof (rule image_eqI[where x = "(\<omega> $ 1, \<omega> $ 2)"])
        show "\<omega> = (\<lambda>(t, u). vector [t, u] :: real^2) (\<omega> $ 1, \<omega> $ 2)"
          by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
        show "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2" by (rule mem)
      qed
    qed
    have "finite K"
      by (rule finite_subset[OF Ksub
            finite_imageI[OF finite_cartesian_product[OF finS1 finS2]]])
    thus ?thesis by (simp flip: K_def)
  qed
qed


section \<open>The per-beam-center-angle slice is nowhere dense (scoped genuine-math sorry)\<close>

text \<open>For a beam-center angle \<open>\<omega>\<close> (\<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>) with \<open>sin (\<omega>\<^sub>1) \<noteq> 0\<close> and a
  nonsingular steering Jacobian, the configurations \<open>x\<close> carrying a degenerate critical
  point with nonzero array factor form a nowhere-dense set.  This is the det-Hessian
  covariance-polynomial payload: with \<open>cvec = 0\<close> the Hessian collapses to
  \<open>N\<^sup>2 gdip''(\<pi>/2) e1 e1\<^sup>T + C\<^sup>T(-2N Cov x) C\<close>, whose vanishing determinant is a
  nontrivial polynomial in the (real) moments of \<open>x\<close> --- nontrivial because
  \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close> --- so its zero set is nowhere dense.  Carried as
  a single scoped \<open>sorry\<close>.\<close>

lemma m5_D2_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "nowhere_dense {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  \<comment> \<open>Ported from the proven D5 covariance core.  \<open>cos \<omega>\<^sub>1 = 0\<close>: the slice is a subset of the
      nowhere-dense det-Hessian zero set (\<open>gdip''(\<pi>/2) \<noteq> 0\<close>).  \<open>cos \<omega>\<^sub>1 \<noteq> 0\<close>: the slice is
      empty by criticality (@{thm beamcenter_critical_cos_zero}).\<close>
proof (cases "cos (\<omega> $ 1) = 0")
  case True
  have nd: "nowhere_dense {x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
  proof -
    have seq: "{x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
             = {x \<in> (UNIV::((real^2)^'n) set). det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
      by simp
    show ?thesis
      unfolding seq
    proof (rule lines_entire_slice_nowhere_dense)
      show "continuous_on UNIV (\<lambda>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
        by (rule continuous_det_HessU_beamcenter[OF cz])
      show "\<And>a v. \<exists>F. F holomorphic_on UNIV
              \<and> (\<forall>t::real. F (complex_of_real t)
                          = complex_of_real (det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (a + t *\<^sub>R v) \<omega>)))"
        using rline_entire_det_HessU_beamcenter[OF cz] unfolding rline_entire_def by blast
      show "\<exists>x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
        by (rule det_HessU_beamcenter_witness[OF c6 pfw cz True])
    qed
  qed
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}
        \<subseteq> {x::(real^2)^'n. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    by blast
  show ?thesis by (rule nowhere_dense_subset[OF sub nd])
next
  case False
  have empty: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0} = {}"
  proof (rule equals0I)
    fix x :: "(real^2)^'n"
    assume "x \<in> {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
    hence g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" by blast
    have "cos (\<omega> $ 1) = 0" by (rule beamcenter_critical_cos_zero[OF c6 pfw cz g0])
    with False show False by simp
  qed
  show ?thesis unfolding empty by simp
qed


section \<open>Assembly: \<open>m5_D2_beamcenter\<close> from finite \<open>K\<close> + nowhere-dense slices\<close>

text \<open>The exact target statement (verbatim from the M5 skeleton), closed by witness
  confinement to the finite beam-center angle set \<open>K\<close>, a finite union of
  nowhere-dense per-angle slices (@{thm meager_Union_finite} + @{thm
  meager_nowhere_dense}), and @{thm meager_subset}.  Two facts make the confinement
  work \<^emph>\<open>x\<close>-universally at a beam center: the \<open>\<not> surj (DM_paper_x x 0)\<close> conjunct is
  automatic (@{thm DM_paper_x_null_not_surj}), so it drops out of the slice; and
  critical witnesses satisfy \<open>cos (\<omega>\<^sub>1) = 0\<close> (@{thm beamcenter_critical_cos_zero}),
  pinning the witness angle into the finite \<open>K\<close>.  Sorry-free at this assembly layer.\<close>

lemma m5_D2_beamcenter:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
proof -
  \<comment> \<open>The finite beam-center witness-angle set (\<open>cos(\<omega>\<^sub>1)=0\<close> from criticality, \<open>cvec=0\<close>).\<close>
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  have finK: "finite K"
    unfolding K_def by (rule m5_D2_beamcenter_K_finite)
  \<comment> \<open>The det-Hessian covariance slice at a fixed beam-center angle.\<close>
  define slice :: "real^2 \<Rightarrow> ((real^2)^'n) set" where
    "slice \<omega> = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}" for \<omega> :: "real^2"
  \<comment> \<open>Witness confinement: every bad witness angle lies in \<open>K\<close>, and the configuration
       lies in the corresponding slice.  The \<open>\<not> surj\<close> conjunct is dropped (automatic
       at a beam center), and \<open>cos(\<omega>\<^sub>1)=0\<close> comes from criticality.\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}
             \<subseteq> (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
    then obtain \<omega> :: "real^2" where wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and hz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and dnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      and cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
      by blast
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    have cosz: "cos (\<omega> $ 1) = 0"
      by (rule beamcenter_critical_cos_zero[OF c6 s1 cz g0])
    have wK: "\<omega> \<in> K" using wD cosz cz by (simp add: K_def)
    have xs: "x \<in> slice \<omega>"
      using g0 hz anz dnz by (simp add: slice_def)
    show "x \<in> (\<Union>\<omega>\<in>K. slice \<omega>)"
    proof (rule UN_I)
      show "\<omega> \<in> K" by (rule wK)
      show "x \<in> slice \<omega>" by (rule xs)
    qed
  qed
  \<comment> \<open>Each slice over a fixed beam-center angle is nowhere dense, hence meager; the
       finite union over \<open>K\<close> is meager; the bad set is contained in it.\<close>
  have meagU: "meager (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof (rule meager_Union_finite[OF finK])
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    show "meager (slice \<omega>)"
      unfolding slice_def
      by (rule meager_nowhere_dense[OF m5_D2_slice_nowhere_dense[OF c6 s1 cz]])
  qed
  show ?thesis by (rule meager_subset[OF sub meagU])
qed

(* ---- D34: phase_collinear predicate ---- *)

definition phase_collinear :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "phase_collinear \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<exists>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) = t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<or> (\<exists>t. cvec_dip \<omega>0 \<omega>s \<omega> = t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"

(* ---- D34: residual assembly (m5_D34_D3_collinear + m5_D34_D4_branchP = the 2 scoped sorries) ---- *)

lemma m5_D34_subset_mstarg_residual:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  shows "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}
        \<subseteq> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  by blast


subsection \<open>Proven building block: the fixed-angle slice is nowhere dense\<close>

text \<open>For a FIXED steering angle \<open>\<omega>\<close> with nonzero wavevector \<open>cvec_dip \<omega>0 \<omega>s \<omega>\<close>,
  the set of \<open>x\<close> at which the moment-map derivative \<open>DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)\<close>
  is not surjective is nowhere dense --- hence meager.  This is the per-angle
  payload of the excess engine, derived sorry-free from the abstract input
  @{text nd} (the Robust3 \<open>mstarg\<close> fact).  The genuine remaining work in D3/D4 is
  precisely the passage from this PER-ANGLE meagerness to meagerness of the
  UNCOUNTABLE \<open>x\<close>-projection \<open>\<Union>\<^bsub>\<omega>\<in>OmegaPF\<^esub>\<close> of the slices --- which needs the
  excess engine (IFT charts + lattice / dichotomy), NOT a mere countable union.\<close>

lemma fixed_omega_slice_meager:
  fixes \<omega> :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  by (rule meager_nowhere_dense[OF nd[OF c0]])


subsection \<open>D3 --- the phase-collinear branch (one scoped sorry)\<close>

text \<open>The phase-collinear branch of the residual.  Internally: the 3-equation /
  2-parameter excess engine produces \<open>(2N-1)\<close>-dim IFT graphs whose \<open>x\<close>-projections
  are negligible, unioned over the \<open>\<int>\<^sup>3\<close> phase-period lattice (window-finite by
  @{thm finite_affine_int_zeros}).  No Sard.  Here we carry the resulting
  meagerness as a single scoped \<open>sorry\<close> and feed it the abstract
  @{thm fixed_c_nonsurj_nowhere_dense} input.\<close>

lemma m5_D34_D3_collinear:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
  sorry


subsection \<open>D4 --- the Branch-P residual (one scoped sorry)\<close>

text \<open>The Branch-P residual: the complementary (non phase-collinear) part.
  Internally: the explicit rank-drop dichotomy (\<open>\<gamma> \<parallel> c\<close> or not) plus the excess
  engine on the \<open>(\<star>n)/Hess.u(w)\<close> rows.  \<open>core_3d\<close> is ruled out structurally (the
  gradU rows degenerate exactly at the residual witnesses), so a dedicated
  stratification is required.  Carried as a single scoped \<open>sorry\<close>.\<close>


(* ===== D4 Stage-B reduction: D4charts chart-route (BadXGW RETAINS gradU=0 -> sound) =====
   phase_collinear already defined above (~L2358); Sard NOT needed -- negligible_singular_image_2n
   + meager_negligible_closed_cover resolve from the Applied_Math_Nonemptiness heap. The single
   new sorry is branchP_indep_charts_Nn, the canonical D4 IFT chart core. ===== *)

definition BadXGW :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  "BadXGW \<omega>0 \<omega>s \<Gamma> = {x::(real^2)^'n. \<exists>\<omega>\<in>\<Gamma>.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
      \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
      \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"


subsection \<open>The rank-drop dichotomy predicate \<open>\<gamma> \<parallel> c\<close> (copied verbatim)\<close>

definition gamma_par_c :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow> phase_collinear \<omega>0 \<omega>s \<omega>"

lemma not_gamma_par_c_iff:
  "\<not> gamma_par_c \<omega>0 \<omega>s \<omega> \<longleftrightarrow>
     (\<forall>t. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<noteq> t *\<^sub>R cvec_dip \<omega>0 \<omega>s \<omega>)
   \<and> (\<forall>t. cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> t *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1))"
  unfolding gamma_par_c_def phase_collinear_def by blast


subsection \<open>Structural set algebra for \<open>BadXGW\<close> (sorry-free, copied verbatim)\<close>

lemma BadXGW_mono:
  fixes \<Gamma> \<Delta> :: "(real^2) set"
  assumes "\<Gamma> \<subseteq> \<Delta>"
  shows "BadXGW \<omega>0 \<omega>s \<Gamma> \<subseteq> (BadXGW \<omega>0 \<omega>s \<Delta> :: ((real^2)^'n) set)"
  using assms unfolding BadXGW_def by blast

lemma BadXGW_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "BadXGW \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)
          = (\<Union>i\<in>I. (BadXGW \<omega>0 \<omega>s (arc i) :: ((real^2)^'n) set))"
  unfolding BadXGW_def by blast

lemma BadXGW_point:
  fixes \<omega> :: "real^2"
  shows "BadXGW \<omega>0 \<omega>s {\<omega>}
          = {x :: (real^2)^'n.
                gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
              \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
              \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  unfolding BadXGW_def by blast


subsection \<open>The irreducible IFT-chart bundle (the single isolated analytic \<open>sorry\<close>)\<close>

text \<open>\<^bold>\<open>The genuine geometric-measure content, isolated as one precisely-scoped
  statement.\<close>  Over the linear-independence (\<open>\<gamma> \<not>\<parallel> c\<close>) region \<open>\<Gamma> \<subseteq> OmegaPF ctr \<delta>\<close>,
  the retained-constraint bad \<open>x\<close>-fibre \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> admits a chart bundle in
  the EXACT shape consumed by @{thm negligible_proj_charts_Nn} (the @{thm
  charts_core_Nn} output): a COUNTABLE family of charts
  \<open>charts i :: (real^2)^'n \<Rightarrow> ((real^2)^'n \<times> (real^2))\<close> with critical sets \<open>Crit i\<close>
  and blinfun derivatives \<open>D i\<close> such that
  \<^enum> the bad fibre is covered by the \<open>x\<close>-projections \<open>(fst \<circ> charts i) ` Crit i\<close>;
  \<^enum> on each \<open>Crit i\<close> the projection \<open>fst \<circ> charts i\<close> has derivative \<open>D i x\<close>;
  \<^enum> that derivative is NON-surjective on \<open>(real^2)^'n\<close> (the codimension \<open>\<ge> 1\<close>
    rank-drop from RETAINED \<open>gradU = 0\<close> + the moment rank-drop), and
  \<^enum> each \<open>x\<close>-projection piece \<open>(fst \<circ> charts i) ` Crit i\<close> is CLOSED.

  This is the implicit-function-theorem chart of the retained-constraint locus.  See
  the file header for the engine analysis showing why neither @{thm charts_core_Nn}
  (G = \<open>gradU\<close>: its \<open>\<omega>\<close>-partial rank drop is \<open>det (HessU) = 0\<close>, not the moment
  \<open>x\<close>-Jacobian rank drop) nor @{thm parametric_transversality_negligible_complex}
  (its rank drop is the \<open>\<omega>\<close>-partial of a complex map, with the variable roles
  transposed relative to the \<open>x\<close>-partial @{const DM_paper_x}) yields an inclusion of
  \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> into the engine bad set.  The codimension source is the
  conjunction \<open>gradU = 0\<close> \<open>\<and>\<close> the moment rank drop; realising the chart of that
  combined locus is the genuine multi-week IFT content and does NOT follow from
  @{text nd} alone.  NOT a splice freebie.\<close>

lemma branchP_indep_charts_Nn:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
            \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  \<comment> \<open>GENUINE geometric-measure core: the IFT chart of the retained-constraint bad
      \<open>(x,\<omega>)\<close> locus in the @{thm charts_core_Nn} output shape.  The single irreducible
      \<open>sorry\<close> of this file; it does NOT follow from @{text nd} alone (see header).
      NOT a splice freebie.\<close>
  sorry


subsection \<open>The verbatim target: the closed negligible cover (sorry-free from the bundle)\<close>

text \<open>\<^bold>\<open>The closed negligible cover, assembled sorry-free from the chart bundle.\<close>
  From the chart bundle @{thm branchP_indep_charts_Nn} the pieces
  \<open>K i = (fst \<circ> charts i) ` (Crit i)\<close> are CLOSED (chart output) and NEGLIGIBLE
  (@{thm negligible_singular_image_2n}: the projection has non-surjective derivative
  on \<open>Crit i\<close>), and they cover the bad fibre.  This turns the IFT-chart content into
  the countable closed negligible cover the reduction layer consumes.  The target
  statement is copied VERBATIM from the D4 core file.\<close>

lemma branchP_indep_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "\<exists>K :: nat \<Rightarrow> ((real^2)^'n) set.
            (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)
          \<and> (\<forall>n. closed (K n))
          \<and> (\<forall>n. negligible (K n))"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
     and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
     and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)
                    \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and rank: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and clo: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using branchP_indep_charts_Nn[OF openV Vne c6 d0 pf Gsub Gindep nd]
    by (smt (verit, best))
  define K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "K i = (fst \<circ> charts i) ` (Crit i)" for i
  have Kcover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    using cover unfolding K_def by simp
  have Kclosed: "closed (K n)" for n
    using clo unfolding K_def by blast
  have Knegligible: "negligible (K n)" for n
    unfolding K_def
    by (rule negligible_singular_image_2n
          [where f = "fst \<circ> charts n" and S = "Crit n"
             and f' = "\<lambda>x. blinfun_apply (D n x)"])
       (use der rank in blast)+
  show ?thesis
    using Kcover Kclosed Knegligible by blast
qed


subsection \<open>The downstream sorry-free layers (copied verbatim from D4Core)\<close>

text \<open>The two sorry-free layers consumed downstream (copied verbatim from the D4
  core file) confirm the cut is at the right place: the closed negligible cover
  yields meagerness without further geometric-measure work.\<close>

lemma branchP_indep_of_negligible_closed_cover:
  fixes V :: "((real^2)^'n) set" and \<Gamma> :: "(real^2) set"
    and K :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
    and clo: "\<And>n. closed (K n)"
    and neg: "\<And>n. negligible (K n)"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
  by (rule meager_negligible_closed_cover[OF cover clo neg])

lemma branchP_indep_core:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
    and \<Gamma> :: "(real^2) set"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and Gsub: "\<Gamma> \<subseteq> OmegaPF ctr \<delta>"
    and Gindep: "\<forall>\<omega>\<in>\<Gamma>. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager (V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set)"
proof -
  obtain K :: "nat \<Rightarrow> ((real^2)^'n) set"
    where cover: "(V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>n. K n)"
      and clo: "\<forall>n. closed (K n)"
      and neg: "\<forall>n. negligible (K n)"
    using branchP_indep_negligible_closed_cover[OF openV Vne c6 d0 pf Gsub Gindep nd]
    by blast
  show ?thesis
    by (rule branchP_indep_of_negligible_closed_cover[OF cover]) (use clo neg in blast)+
qed

lemma m5_D34_D4_branchP:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  \<comment> \<open>Stage-B D4 reduction: the residual = \<open>V \<inter> BadXGW \<omega>0 \<omega>s \<Gamma>\<close> over the
      \<open>\<gamma>\<not>\<parallel>c\<close> region \<open>\<Gamma>\<close>, closed by the grafted D4 chart-route \<open>branchP_indep_core\<close>
      (which bottoms out at the canonical IFT core \<open>branchP_indep_charts_Nn\<close>).\<close>
proof -
  let ?Gam = "{\<omega>\<in>OmegaPF ctr \<delta>. \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  have eq: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}
          = (V \<inter> BadXGW \<omega>0 \<omega>s ?Gam :: ((real^2)^'n) set)"
    unfolding BadXGW_def by blast
  have Gsub: "?Gam \<subseteq> OmegaPF ctr \<delta>" by blast
  have Gindep: "\<forall>\<omega>\<in>?Gam. \<not> gamma_par_c \<omega>0 \<omega>s \<omega>" by (auto simp: gamma_par_c_def)
  show ?thesis unfolding eq
    by (rule branchP_indep_core[OF openV Vne c6 d0 pf Gsub Gindep nd])
qed


subsection \<open>Assembly: \<open>m5_D34_residual\<close> from the reduction + D3 + D4\<close>

text \<open>The exact target statement (verbatim from the M5 skeleton), closed by:
  the structural reduction @{thm m5_D34_subset_mstarg_residual}, the
  excluded-middle split of the residual on the proof-internal predicate
  @{const phase_collinear} into D3 \<union> D4, the two inner meagerness lemmas, and
  @{thm meager_subset} / @{thm meager_Un}.  Sorry-free at this assembly layer.\<close>

lemma m5_D34_residual:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  \<comment> \<open>The Robust3-supplied fixed-angle nowhere-density (here a single scoped sorry).\<close>
  have nd: "\<And>c::real^2. c \<noteq> 0 \<Longrightarrow>
              nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
    by (rule fixed_c_nonsurj_nowhere_dense[OF _ c6])
  \<comment> \<open>The residual the excess engine consumes (gradU = 0, det Dcvec \<noteq> 0,
       cvec \<noteq> 0, DM not surjective).\<close>
  let ?R = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  let ?D3 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> phase_collinear \<omega>0 \<omega>s \<omega>}"
  let ?D4 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> \<not> phase_collinear \<omega>0 \<omega>s \<omega>}"
  \<comment> \<open>The residual is the D3/D4 union (excluded middle on \<open>phase_collinear\<close>).\<close>
  have RsubD: "?R \<subseteq> ?D3 \<union> ?D4" by blast
  \<comment> \<open>Each piece is meager (the two genuine obligations, sorried inside).\<close>
  have mD3: "meager ?D3" by (rule m5_D34_D3_collinear[OF openV Vne c6 d0 pf nd])
  have mD4: "meager ?D4" by (rule m5_D34_D4_branchP[OF openV Vne c6 d0 pf nd])
  have mR: "meager ?R"
    by (rule meager_subset[OF RsubD meager_Un[OF mD3 mD4]])
  \<comment> \<open>The full D34 bad set injects into the residual (structural reduction).\<close>
  show ?thesis
    by (rule meager_subset[OF m5_D34_subset_mstarg_residual mR])
qed

(* ---- D1: joint-regular part (subset of heap meager_grad_x_regular_part) ---- *)

lemma m5_D1_regular:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}
        \<subseteq> {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_grad_x_regular_part[OF openV Vne]])
qed

lemma meager_rank_deficient_stratum:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
  \<comment> \<open>(M5) assembled from the four-stratum cover D1 \<union> D2 \<union> D5 \<union> D34 (grafted above).
      D1/D2/D5 are proven sorry-free; D34 rests on the two scoped chart-branch cores
      \<open>m5_D34_D3_collinear\<close> / \<open>m5_D34_D4_branchP\<close>.\<close>
proof -
  let ?D1 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  let ?D2 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  let ?D5 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  let ?D34 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  have meag: "meager (?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34)"
    by (intro meager_Un
          m5_D1_regular[OF openV Vne]
          m5_D2_beamcenter[OF openV Vne c6 d0 pf]
          m5_D5_steersing[OF openV Vne c6 d0 pf hsep kdiff]
          m5_D34_residual[OF openV Vne c6 d0 pf])
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
             \<subseteq> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    then obtain \<omega> where xV: "x \<in> V" and wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and a0: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and ns: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      by blast
    show "x \<in> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34"
      using xV wD g0 h0 a0 ns by blast
  qed
  show ?thesis by (rule meager_subset[OF sub meag])
qed

text \<open>\<^bold>\<open>(M6) Steering-singular stratum is meager.\<close>  Degenerate critical points (with \<open>A \<noteq> 0\<close>) at an
  angle where the steering Jacobian is singular.  Meager by (M3): the singular-\<open>\<omega>\<close> locus is
  nowhere dense, and the critical points over it form a positive-codimension set.\<close>

text \<open>\<open>meager_steering_singular_stratum\<close> (M6) is DONE --- proven sorry-free in
  \<open>Nonemptiness_Robust2\<close> (in the heap): kernel-direction reduction +
  gdip-derivative zero classification + finite witness-angle set + fixed-angle
  analytic slices.  Development history: Scratch_m6 / Scratch_g1_r4 /
  Scratch_g2_r5 / Scratch_g3_asm (parallel agent wave).\<close>

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
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
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
              \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
              \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  let ?null = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
              \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
              \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> = 0}"
  have meag4: "meager (?reg \<union> ?def \<union> ?steer \<union> ?null)"
    by (intro meager_Un meager_bad_regular_stratum_on[OF openV Vne c6]
              meager_rank_deficient_stratum[OF openV Vne c6 d0 pf hsep kdiff]
              meager_steering_singular_stratum[OF openV Vne c6 d0 pf hsep kdiff]
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
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
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
    by (rule Phi_bad_meager_dip[OF openI Ine c6 oddN hsep kdiff d0 pf])
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
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
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
    using regular_config_exists[OF c6 oddN hsep kdiff d0 pf feasible] by blast
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
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
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
    using regular_feasible_point_dip[OF c6 oddN hsep kdiff d0 dpi pf feasible] by blast
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
  have kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
    by (simp add: \<omega>0_def \<omega>s_def kx_def sin_pi_half)
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
    using regular_feasible_witness_dip[OF c6 oddN hsep kdiff d0 dpi pf feasible]
    by (blast intro: F0_nonempty_of_witness OmegaPF_compact)
  thus ?thesis using d0 by blast
qed

end