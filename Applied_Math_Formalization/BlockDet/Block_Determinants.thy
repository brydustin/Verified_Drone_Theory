theory Block_Determinants
  imports
    "HOL-Analysis.Determinants"
begin

text \<open>
  Concrete 6x6 block-matrix determinant computations factored out of
  Nonemptiness_Paper.thy so they can be baked into the Applied_Math_BlockDet
  heap (the row-by-row reductions are cheap once compiled but slow to
  recompile from source). The exported facts are \<open>det_A\<close>, \<open>det_D\<close>, and the
  surrounding index/sum infrastructure (\<open>UNIV_12\<close>, \<open>forall_12\<close>, etc.) consumed
  by the \<open>bigJ_det\<close> chain.
\<close>

subsection \<open>Index/sum infrastructure for \<open>5\<close>, \<open>6\<close>, \<open>12\<close>\<close>

text \<open>
  HOL-Analysis provides \<open>exhaust_n\<close>/\<open>UNIV_n\<close>/\<open>sum_n\<close> for \<open>n \<le> 4\<close>; we extend to
  \<open>5\<close> and \<open>6\<close> (needed for the \<open>6\<times>6\<close> block determinants below).
\<close>

lemma exhaust_5:
  fixes x :: 5
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5"
proof (induct x)
  case (of_int z)
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4" by fastforce
  then show ?case by auto
qed

lemma UNIV_5: "UNIV = {1, 2, 3, 4, 5::5}"
  using exhaust_5 by auto

lemma sum_5: "sum f (UNIV::5 set) = f 1 + f 2 + f 3 + f 4 + f 5"
  unfolding UNIV_5 by (simp add: ac_simps)

lemma exhaust_6:
  fixes x :: 6
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5 \<or> x = 6"
proof (induct x)
  case (of_int z)
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4 \<or> z = 5" by fastforce
  then show ?case by auto
qed

lemma UNIV_6: "UNIV = {1, 2, 3, 4, 5, 6::6}"
  using exhaust_6 by auto

lemma sum_6: "sum f (UNIV::6 set) = f 1 + f 2 + f 3 + f 4 + f 5 + f 6"
  unfolding UNIV_6 by (simp add: ac_simps)

lemma forall_5: "(\<forall>i::5. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5"
  by (metis exhaust_5)

lemma forall_6:
  "(\<forall>i::6. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5 \<and> P 6"
  by (metis exhaust_6)

lemma vector_5 [simp]:
 "(vector [a,b,c,d,e] :: ('a::zero)^5) $ 1 = a"
 "(vector [a,b,c,d,e] :: ('a::zero)^5) $ 2 = b"
 "(vector [a,b,c,d,e] :: ('a::zero)^5) $ 3 = c"
 "(vector [a,b,c,d,e] :: ('a::zero)^5) $ 4 = d"
 "(vector [a,b,c,d,e] :: ('a::zero)^5) $ 5 = e"
  unfolding vector_def by simp_all

lemma vector_6 [simp]:
 "(vector [a,b,c,d,e,f] :: ('a::zero)^6) $ 1 = a"
 "(vector [a,b,c,d,e,f] :: ('a::zero)^6) $ 2 = b"
 "(vector [a,b,c,d,e,f] :: ('a::zero)^6) $ 3 = c"
 "(vector [a,b,c,d,e,f] :: ('a::zero)^6) $ 4 = d"
 "(vector [a,b,c,d,e,f] :: ('a::zero)^6) $ 5 = e"
 "(vector [a,b,c,d,e,f] :: ('a::zero)^6) $ 6 = f"
  unfolding vector_def by simp_all

lemma exhaust_12:
  fixes x :: 12
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5 \<or> x = 6
       \<or> x = 7 \<or> x = 8 \<or> x = 9 \<or> x = 10 \<or> x = 11 \<or> x = 12"
proof (induct x)
  case (of_int z)
  then have zbound: "0 \<le> z \<and> z < 12" by simp
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4 \<or> z = 5
           \<or> z = 6 \<or> z = 7 \<or> z = 8 \<or> z = 9 \<or> z = 10 \<or> z = 11"
    using zbound by presburger
  then show ?case by auto
qed

lemma UNIV_12: "UNIV = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12::12}"
  using exhaust_12 by auto

lemma sum_12:
  "sum f (UNIV::12 set)
     = f 1 + f 2 + f 3 + f 4 + f 5 + f 6
     + f 7 + f 8 + f 9 + f 10 + f 11 + f 12"
  unfolding UNIV_12 by (simp add: ac_simps)

lemma forall_12:
  "(\<forall>i::12. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5 \<and> P 6
                  \<and> P 7 \<and> P 8 \<and> P 9 \<and> P 10 \<and> P 11 \<and> P 12"
  by (metis exhaust_12)

lemma vector_12 [simp]:
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 1 = a"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 2 = b"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 3 = c"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 4 = d"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 5 = e"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 6 = f"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 7 = g"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 8 = h"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 9 = i"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 10 = j"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 11 = k"
 "(vector [a,b,c,d,e,f,g,h,i,j,k,l] :: ('a::zero)^12) $ 12 = l"
  unfolding vector_def by simp_all


text \<open>
  The explicit \<open>12 \<times> 12\<close> real Jacobian minor \<open>J\<close> of \<open>Dblk\<^sub>x M\<close> at the chosen
  six-element configuration (TeX Figure~\<open>fig:bigmatrix\<close>), evaluated at
  \<open>\<kappa> = 1\<close>. Rows are the twelve real moment components
  \<open>\<real>Ablk, \<I>Ablk, \<real>M\<^sub>1, \<I>M\<^sub>1, \<real>M\<^sub>2, \<I>M\<^sub>2, \<real>M\<^sub>1\<^sub>1, \<I>M\<^sub>1\<^sub>1, \<real>M\<^sub>1\<^sub>2, \<I>M\<^sub>1\<^sub>2, \<real>M\<^sub>2\<^sub>2, \<I>M\<^sub>2\<^sub>2\<close>;
  the twelve columns are \<open>\<partial>\<^sub>u\<^sub>n M, \<partial>\<^sub>v\<^sub>n M\<close> for \<open>n = 1..6\<close>. (The determinant is
  transpose-invariant, so the row/column reading is immaterial.)
\<close>

subsection \<open>The constant \<open>6\<times>6\<close> block \<open>Bblk\<close>\<close>

text \<open>
  After pulling out a factor \<open>\<pi>\<^sup>6\<close> from the \<open>Ablk\<close>-block (Determinant.md \<section>5),
  the residual constant matrix is \<open>Bblk\<close>; we will show \<open><det Bblk = -\<sqrt>3/18\<close>.
\<close>

definition Bblk :: "real^6^6" where
  "Bblk = vector
    [ vector [0,  - sqrt 3 / 2,    - sqrt 3 / 2,     0,  sqrt 3 / 2,      sqrt 3 / 2],
      vector [-1, -1/2,            1/2,              1,  1/2,             -1/2],
      vector [0,  - sqrt 3 / 6,    - sqrt 3 / 3,     0,  2 * sqrt 3 / 3,  5 * sqrt 3 / 6],
      vector [0,  -1/6,            1/3,              1,  2/3,             -5/6],
      vector [0,  - sqrt 3 / 18,   - 2 * sqrt 3 / 9, 0,  8 * sqrt 3 / 9,  25 * sqrt 3 / 18],
      vector [0,  -1/18,           2/9,              1,  8/9,             -25/18] ]"

text \<open>
  \<^bold>\<open>Row-reduction chain for \<open>det Bblk\<close>.\<close> Brute-force unfolding of the 720-term
  permutation sum is intractable; instead we transform \<open>Bblk\<close> to an upper-
  triangular \<open>Bblk\<^sub>5\<close> through five determinant-preserving (or sign-flipping)
  row operations, then read off the determinant from the diagonal.

  \begin{itemize}
  \item \<open>Bblk\<^sub>1\<close>: swap rows \<open>1\<close> and \<open>2\<close> (\<open>det\<close> negated).
  \item \<open>Bblk\<^sub>2\<close>: eliminate column \<open>2\<close> below row \<open>2\<close> (four row-adds, \<open>det\<close>
        preserved).
  \item \<open>Bblk\<^sub>3\<close>: eliminate column \<open>3\<close> below row \<open>3\<close> (three row-adds).
  \item \<open>Bblk\<^sub>4\<close>: eliminate column \<open>4\<close> below row \<open>4\<close> (one row-add).
  \item \<open>Bblk\<^sub>5\<close>: eliminate column \<open>5\<close> below row \<open>5\<close> (one row-add). Upper
        triangular; diagonal product \<open>= \<sqrt>3/18\<close>.
  \end{itemize}
\<close>

subsubsection \<open>Step 1: swap rows \<open>1\<close> and \<open>2\<close>\<close>

definition Bblk\<^sub>1 :: "real^6^6" where
  "Bblk\<^sub>1 = vector
    [ vector [-1, -1/2,            1/2,              1,  1/2,             -1/2],
      vector [0,  - sqrt 3 / 2,    - sqrt 3 / 2,     0,  sqrt 3 / 2,      sqrt 3 / 2],
      vector [0,  - sqrt 3 / 6,    - sqrt 3 / 3,     0,  2 * sqrt 3 / 3,  5 * sqrt 3 / 6],
      vector [0,  -1/6,            1/3,              1,  2/3,             -5/6],
      vector [0,  - sqrt 3 / 18,   - 2 * sqrt 3 / 9, 0,  8 * sqrt 3 / 9,  25 * sqrt 3 / 18],
      vector [0,  -1/18,           2/9,              1,  8/9,             -25/18] ]"

lemma det_B_eq_neg_det_B\<^sub>1: "det Bblk = - det Bblk\<^sub>1"
proof -
  let ?\<sigma> = "Fun.swap (1::6) 2 id"
  have perm: "?\<sigma> permutes UNIV"
    by (simp add: permutes_swap_id)
  have eq: "Bblk\<^sub>1 = (\<chi> i. Bblk $ (?\<sigma> i))"
    unfolding Bblk_def Bblk\<^sub>1_def vec_eq_iff
    by (auto simp: forall_6 Fun.swap_def vector_def)
  have "det Bblk\<^sub>1 = of_int (sign ?\<sigma>) * det Bblk"
    using det_permute_rows[OF perm, of Bblk] eq by simp
  also have "\<dots> = - det Bblk"
    by (simp add: sign_swap_id)
  finally show ?thesis by simp
qed

subsubsection \<open>Step 2: eliminate column \<open>2\<close> below the pivot at row \<open>2\<close>\<close>

text \<open>Four row-adds with pivot \<open>Bblk\<^sub>1[2,2] = -\<sqrt>3/2\<close>:
      \<open>R\<^sub>3 \<leftarrow> R\<^sub>3 - (1/3) R\<^sub>2\<close>,
      \<open>R\<^sub>4 \<leftarrow> R\<^sub>4 - (\<sqrt>3/9) R\<^sub>2\<close>,
      \<open>R\<^sub>5 \<leftarrow> R\<^sub>5 - (1/9) R\<^sub>2\<close>,
      \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 - (\<sqrt>3/27) R\<^sub>2\<close>.\<close>

definition Bblk\<^sub>2 :: "real^6^6" where
  "Bblk\<^sub>2 = vector
    [ vector [-1, -1/2,         1/2,          1,  1/2,             -1/2],
      vector [0,  - sqrt 3 / 2, - sqrt 3 / 2, 0,  sqrt 3 / 2,      sqrt 3 / 2],
      vector [0,  0,            - sqrt 3 / 6, 0,  sqrt 3 / 2,      2 * sqrt 3 / 3],
      vector [0,  0,            1/2,          1,  1/2,             -1],
      vector [0,  0,            - sqrt 3 / 6, 0,  5 * sqrt 3 / 6,  4 * sqrt 3 / 3],
      vector [0,  0,            5/18,         1,  5/6,             -13/9] ]"

lemma det_B\<^sub>1_eq_det_B\<^sub>2: "det Bblk\<^sub>1 = det Bblk\<^sub>2"
proof -
  define X\<^sub>1 :: "real^6^6"
    where "X\<^sub>1 = (\<chi> k. if k = 3 then row 3 Bblk\<^sub>1 + (-1/3) *s row 2 Bblk\<^sub>1 else row k Bblk\<^sub>1)"
  define X\<^sub>2 :: "real^6^6"
    where "X\<^sub>2 = (\<chi> k. if k = 4 then row 4 X\<^sub>1 + (- sqrt 3 / 9) *s row 2 X\<^sub>1 else row k X\<^sub>1)"
  define X\<^sub>3 :: "real^6^6"
    where "X\<^sub>3 = (\<chi> k. if k = 5 then row 5 X\<^sub>2 + (-1/9) *s row 2 X\<^sub>2 else row k X\<^sub>2)"
  define X\<^sub>4 :: "real^6^6"
    where "X\<^sub>4 = (\<chi> k. if k = 6 then row 6 X\<^sub>3 + (- sqrt 3 / 27) *s row 2 X\<^sub>3 else row k X\<^sub>3)"
  have d1: "det X\<^sub>1 = det Bblk\<^sub>1"
    unfolding X\<^sub>1_def by (rule det_row_operation) auto
  have d2: "det X\<^sub>2 = det X\<^sub>1"
    unfolding X\<^sub>2_def by (rule det_row_operation) auto
  have d3: "det X\<^sub>3 = det X\<^sub>2"
    unfolding X\<^sub>3_def by (rule det_row_operation) auto
  have d4: "det X\<^sub>4 = det X\<^sub>3"
    unfolding X\<^sub>4_def by (rule det_row_operation) auto
  have eq: "X\<^sub>4 = Bblk\<^sub>2"
    unfolding X\<^sub>4_def X\<^sub>3_def X\<^sub>2_def X\<^sub>1_def Bblk\<^sub>1_def Bblk\<^sub>2_def vec_eq_iff
    by (auto simp: forall_6 row_def vector_def field_simps power2_eq_square)
  show ?thesis using d1 d2 d3 d4 eq by simp
qed

subsubsection \<open>Step 3: eliminate column \<open>3\<close> below the pivot at row \<open>3\<close>\<close>

text \<open>Three row-adds with pivot \<open>Bblk\<^sub>2[3,3] = -\<sqrt>3/6\<close>:
      \<open>R\<^sub>4 \<leftarrow> R\<^sub>4 + \<sqrt>3 R\<^sub>3\<close>,
      \<open>R\<^sub>5 \<leftarrow> R\<^sub>5 - R\<^sub>3\<close>,
      \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 + (5 \<sqrt>3/9) R\<^sub>3\<close>.\<close>

definition Bblk\<^sub>3 :: "real^6^6" where
  "Bblk\<^sub>3 = vector
    [ vector [-1, -1/2,         1/2,          1,  1/2,         -1/2],
      vector [0,  - sqrt 3 / 2, - sqrt 3 / 2, 0,  sqrt 3 / 2,  sqrt 3 / 2],
      vector [0,  0,            - sqrt 3 / 6, 0,  sqrt 3 / 2,  2 * sqrt 3 / 3],
      vector [0,  0,            0,            1,  2,           1],
      vector [0,  0,            0,            0,  sqrt 3 / 3,  2 * sqrt 3 / 3],
      vector [0,  0,            0,            1,  5/3,         -1/3] ]"

lemma det_B\<^sub>2_eq_det_B\<^sub>3: "det Bblk\<^sub>2 = det Bblk\<^sub>3"
proof -
  define Y\<^sub>1 :: "real^6^6"
    where "Y\<^sub>1 = (\<chi> k. if k = 4 then row 4 Bblk\<^sub>2 + sqrt 3 *s row 3 Bblk\<^sub>2 else row k Bblk\<^sub>2)"
  define Y\<^sub>2 :: "real^6^6"
    where "Y\<^sub>2 = (\<chi> k. if k = 5 then row 5 Y\<^sub>1 + (-1) *s row 3 Y\<^sub>1 else row k Y\<^sub>1)"
  define Y\<^sub>3 :: "real^6^6"
    where "Y\<^sub>3 = (\<chi> k. if k = 6 then row 6 Y\<^sub>2 + (5 * sqrt 3 / 9) *s row 3 Y\<^sub>2 else row k Y\<^sub>2)"
  have d1: "det Y\<^sub>1 = det Bblk\<^sub>2"
    unfolding Y\<^sub>1_def by (rule det_row_operation) auto
  have d2: "det Y\<^sub>2 = det Y\<^sub>1"
    unfolding Y\<^sub>2_def by (rule det_row_operation) auto
  have d3: "det Y\<^sub>3 = det Y\<^sub>2"
    unfolding Y\<^sub>3_def by (rule det_row_operation) auto
  have eq: "Y\<^sub>3 = Bblk\<^sub>3"
    unfolding Y\<^sub>3_def Y\<^sub>2_def Y\<^sub>1_def Bblk\<^sub>2_def Bblk\<^sub>3_def vec_eq_iff
    by (auto simp: forall_6 row_def vector_def field_simps power2_eq_square)
  show ?thesis using d1 d2 d3 eq by simp
qed

subsubsection \<open>Step 4: eliminate column \<open>4\<close> below the pivot at row \<open>4\<close>\<close>

text \<open>One row-add with pivot \<open>Bblk\<^sub>3[4,4] = 1\<close>: \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 - R\<^sub>4\<close>.
      (\<open>Bblk\<^sub>3[5,4]\<close> is already \<open>0\<close>.)\<close>

definition Bblk\<^sub>4 :: "real^6^6" where
  "Bblk\<^sub>4 = vector
    [ vector [-1, -1/2,         1/2,          1,  1/2,         -1/2],
      vector [0,  - sqrt 3 / 2, - sqrt 3 / 2, 0,  sqrt 3 / 2,  sqrt 3 / 2],
      vector [0,  0,            - sqrt 3 / 6, 0,  sqrt 3 / 2,  2 * sqrt 3 / 3],
      vector [0,  0,            0,            1,  2,           1],
      vector [0,  0,            0,            0,  sqrt 3 / 3,  2 * sqrt 3 / 3],
      vector [0,  0,            0,            0,  -1/3,        -4/3] ]"

lemma det_B\<^sub>3_eq_det_B\<^sub>4: "det Bblk\<^sub>3 = det Bblk\<^sub>4"
proof -
  define Z :: "real^6^6"
    where "Z = (\<chi> k. if k = 6 then row 6 Bblk\<^sub>3 + (-1) *s row 4 Bblk\<^sub>3 else row k Bblk\<^sub>3)"
  have d: "det Z = det Bblk\<^sub>3"
    unfolding Z_def by (rule det_row_operation) auto
  have eq: "Z = Bblk\<^sub>4"
    unfolding Z_def Bblk\<^sub>3_def Bblk\<^sub>4_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps)
  show ?thesis using d eq by simp
qed

subsubsection \<open>Step 5: eliminate column \<open>5\<close> below the pivot at row \<open>5\<close>\<close>

text \<open>One row-add with pivot \<open>Bblk\<^sub>4[5,5] = \<sqrt>3/3\<close>: \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 + (\<sqrt>3/3) R\<^sub>5\<close>.\<close>

definition Bblk\<^sub>5 :: "real^6^6" where
  "Bblk\<^sub>5 = vector
    [ vector [-1, -1/2,         1/2,          1,  1/2,         -1/2],
      vector [0,  - sqrt 3 / 2, - sqrt 3 / 2, 0,  sqrt 3 / 2,  sqrt 3 / 2],
      vector [0,  0,            - sqrt 3 / 6, 0,  sqrt 3 / 2,  2 * sqrt 3 / 3],
      vector [0,  0,            0,            1,  2,           1],
      vector [0,  0,            0,            0,  sqrt 3 / 3,  2 * sqrt 3 / 3],
      vector [0,  0,            0,            0,  0,           -2/3] ]"

lemma det_B\<^sub>4_eq_det_B\<^sub>5: "det Bblk\<^sub>4 = det Bblk\<^sub>5"
proof -
  define W :: "real^6^6"
    where "W = (\<chi> k. if k = 6 then row 6 Bblk\<^sub>4 + (sqrt 3 / 3) *s row 5 Bblk\<^sub>4 else row k Bblk\<^sub>4)"
  have d: "det W = det Bblk\<^sub>4"
    unfolding W_def by (rule det_row_operation) auto
  have eq: "W = Bblk\<^sub>5"
    unfolding W_def Bblk\<^sub>4_def Bblk\<^sub>5_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps power2_eq_square)
  show ?thesis using d eq by simp
qed

subsubsection \<open>Step 6: read off \<open>det Bblk\<^sub>5\<close> from the diagonal\<close>

lemma det_B\<^sub>5: "det Bblk\<^sub>5 = sqrt 3 / 18"
proof -
  text \<open>\<open>Bblk\<^sub>5\<close> is upper triangular and sparse, so brute-forcing the 720-term
        permutation sum is tractable: 719 terms vanish via \<open>0 \<cdot> _ = 0\<close>, leaving
        only the identity-permutation product (the diagonal).\<close>
  have f1: "finite {2::6, 3, 4, 5, 6}" "1 \<notin> {2::6, 3, 4, 5, 6}" by auto
  have f2: "finite {3::6, 4, 5, 6}"    "2 \<notin> {3::6, 4, 5, 6}"    by auto
  have f3: "finite {4::6, 5, 6}"       "3 \<notin> {4::6, 5, 6}"       by auto
  have f4: "finite {5::6, 6}"          "4 \<notin> {5::6, 6}"          by auto
  have f5: "finite {6::6}"             "5 \<notin> {6::6}"             by auto
  show ?thesis
    unfolding Bblk\<^sub>5_def det_def UNIV_6
    unfolding sum_over_permutations_insert[OF f1]
    unfolding sum_over_permutations_insert[OF f2]
    unfolding sum_over_permutations_insert[OF f3]
    unfolding sum_over_permutations_insert[OF f4]
    unfolding sum_over_permutations_insert[OF f5]
    unfolding permutes_sing
    by (simp add: sign_swap_id permutation_swap_id sign_compose swap_id_eq
                  field_simps power2_eq_square)
qed

subsubsection \<open>Combining the chain: \<open>det Bblk = -\<sqrt>3/18\<close>\<close>

lemma det_B: "det Bblk = - sqrt 3 / 18"
  using det_B_eq_neg_det_B\<^sub>1 det_B\<^sub>1_eq_det_B\<^sub>2 det_B\<^sub>2_eq_det_B\<^sub>3
        det_B\<^sub>3_eq_det_B\<^sub>4 det_B\<^sub>4_eq_det_B\<^sub>5 det_B\<^sub>5
  by simp


subsection \<open>The \<open>6\<times>6\<close> \<open>Ablk\<close>-block: \<open>det Ablk = -\<sqrt>3 \<pi>\<^sup>6/18\<close>\<close>

text \<open>
  The original \<open>Ablk\<close>-block (Determinant.md \<section>5). Four \<open>det\<close>-preserving row-adds
  bring it to \<open>Ablk\<^sub>4\<close>, whose rows \<open>3,4,5,6\<close> are \<open>\<pi>, \<pi>, \<pi>\<^sup>2, \<pi>\<^sup>2\<close> times the
  corresponding rows of \<open>Bblk\<close>; factoring those out gives \<open>det Ablk\<^sub>4 = \<pi>\<^sup>6 \<cdot> det Bblk\<close>.
\<close>

definition Ablk :: "real^6^6" where
  "Ablk = vector
    [ vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [-1, -1/2, 1/2, 1, 1/2, -1/2],
      vector [1, 1/2 - pi * sqrt 3 / 6, -1/2 - pi * sqrt 3 / 3, -1,
              -1/2 + 2 * pi * sqrt 3 / 3, 1/2 + 5 * pi * sqrt 3 / 6],
      vector [0, - sqrt 3 / 2 - pi / 6, - sqrt 3 / 2 + pi / 3, pi,
              sqrt 3 / 2 + 2 * pi / 3, sqrt 3 / 2 - 5 * pi / 6],
      vector [0, pi / 3 - pi^2 * sqrt 3 / 18, -2 * pi / 3 - 2 * pi^2 * sqrt 3 / 9,
              -2 * pi, -4 * pi / 3 + 8 * pi^2 * sqrt 3 / 9,
              5 * pi / 3 + 25 * pi^2 * sqrt 3 / 18],
      vector [0, - pi * sqrt 3 / 3 - pi^2 / 18, -2 * pi * sqrt 3 / 3 + 2 * pi^2 / 9,
              pi^2, 4 * pi * sqrt 3 / 3 + 8 * pi^2 / 9,
              5 * pi * sqrt 3 / 3 - 25 * pi^2 / 18] ]"

definition Ablk\<^sub>4 :: "real^6^6" where
  "Ablk\<^sub>4 = vector
    [ vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [-1, -1/2, 1/2, 1, 1/2, -1/2],
      vector [0, - pi * sqrt 3 / 6, - pi * sqrt 3 / 3, 0,
              2 * pi * sqrt 3 / 3, 5 * pi * sqrt 3 / 6],
      vector [0, - pi / 6, pi / 3, pi, 2 * pi / 3, -5 * pi / 6],
      vector [0, - (pi^2) * sqrt 3 / 18, - 2 * pi^2 * sqrt 3 / 9, 0,
              8 * pi^2 * sqrt 3 / 9, 25 * pi^2 * sqrt 3 / 18],
      vector [0, - (pi^2) / 18, 2 * pi^2 / 9, pi^2, 8 * pi^2 / 9, -25 * pi^2 / 18] ]"

subsubsection \<open>Row-adds: \<open>det Ablk = det Ablk\<^sub>4\<close>\<close>

text \<open>Four \<open>det\<close>-preserving row-adds:
      \<open>R\<^sub>3 \<leftarrow> R\<^sub>3 + R\<^sub>2\<close>,
      \<open>R\<^sub>4 \<leftarrow> R\<^sub>4 - R\<^sub>1\<close>,
      \<open>R\<^sub>5 \<leftarrow> R\<^sub>5 + 2 R\<^sub>4\<close> (using the new \<open>R\<^sub>4\<close>),
      \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 - 2 R\<^sub>3\<close> (using the new \<open>R\<^sub>3\<close>).\<close>

lemma det_A_eq_det_A\<^sub>4: "det Ablk = det Ablk\<^sub>4"
proof -
  define U\<^sub>1 :: "real^6^6"
    where "U\<^sub>1 = (\<chi> k. if k = 3 then row 3 Ablk + 1 *s row 2 Ablk else row k Ablk)"
  define U\<^sub>2 :: "real^6^6"
    where "U\<^sub>2 = (\<chi> k. if k = 4 then row 4 U\<^sub>1 + (-1) *s row 1 U\<^sub>1 else row k U\<^sub>1)"
  define U\<^sub>3 :: "real^6^6"
    where "U\<^sub>3 = (\<chi> k. if k = 5 then row 5 U\<^sub>2 + 2 *s row 4 U\<^sub>2 else row k U\<^sub>2)"
  define U\<^sub>4 :: "real^6^6"
    where "U\<^sub>4 = (\<chi> k. if k = 6 then row 6 U\<^sub>3 + (-2) *s row 3 U\<^sub>3 else row k U\<^sub>3)"
  have d1: "det U\<^sub>1 = det Ablk"
    unfolding U\<^sub>1_def by (rule det_row_operation) auto
  have d2: "det U\<^sub>2 = det U\<^sub>1"
    unfolding U\<^sub>2_def by (rule det_row_operation) auto
  have d3: "det U\<^sub>3 = det U\<^sub>2"
    unfolding U\<^sub>3_def by (rule det_row_operation) auto
  have d4: "det U\<^sub>4 = det U\<^sub>3"
    unfolding U\<^sub>4_def by (rule det_row_operation) auto
  have eq: "U\<^sub>4 = Ablk\<^sub>4"
    unfolding U\<^sub>4_def U\<^sub>3_def U\<^sub>2_def U\<^sub>1_def Ablk_def Ablk\<^sub>4_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps power2_eq_square)
  show ?thesis using d1 d2 d3 d4 eq by simp
qed

subsubsection \<open>Row-mults: \<open>det Ablk\<^sub>4 = \<pi>\<^sup>6 \<cdot> det Bblk\<close>\<close>

text \<open>\<open>Ablk\<^sub>4\<close> rows \<open>3,4\<close> are \<open>\<pi>\<close> times the corresponding \<open>Bblk\<close>-rows; rows \<open>5,6\<close> are
      \<open>\<pi>\<^sup>2\<close> times. Four applications of @{thm det_row_mul} factor out the powers
      of \<open>\<pi>\<close>; total factor \<open>\<pi> \<cdot> \<pi> \<cdot> \<pi>\<^sup>2 \<cdot> \<pi>\<^sup>2 = \<pi>\<^sup>6\<close>.\<close>

lemma det_A\<^sub>4_eq_pi6_det_B: "det Ablk\<^sub>4 = pi^6 * det Bblk"
proof -
  have row1_eq: "row 1 Ablk\<^sub>4 = row 1 Bblk"
    unfolding Ablk\<^sub>4_def Bblk_def vec_eq_iff by (auto simp: forall_6 row_def)
  have row2_eq: "row 2 Ablk\<^sub>4 = row 2 Bblk"
    unfolding Ablk\<^sub>4_def Bblk_def vec_eq_iff by (auto simp: forall_6 row_def)
  have row3_eq: "row 3 Ablk\<^sub>4 = pi *s row 3 Bblk"
    unfolding Ablk\<^sub>4_def Bblk_def vec_eq_iff by (auto simp: forall_6 row_def field_simps)
  have row4_eq: "row 4 Ablk\<^sub>4 = pi *s row 4 Bblk"
    unfolding Ablk\<^sub>4_def Bblk_def vec_eq_iff by (auto simp: forall_6 row_def field_simps)
  have row5_eq: "row 5 Ablk\<^sub>4 = (pi^2) *s row 5 Bblk"
    unfolding Ablk\<^sub>4_def Bblk_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps power2_eq_square)
  have row6_eq: "row 6 Ablk\<^sub>4 = (pi^2) *s row 6 Bblk"
    unfolding Ablk\<^sub>4_def Bblk_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps power2_eq_square)

  define N\<^sub>1 :: "real^6^6"
    where "N\<^sub>1 = (\<chi> k. if k = 3 then row 3 Bblk else row k Ablk\<^sub>4)"
  define N\<^sub>2 :: "real^6^6"
    where "N\<^sub>2 = (\<chi> k. if k = 4 then row 4 Bblk else row k N\<^sub>1)"
  define N\<^sub>3 :: "real^6^6"
    where "N\<^sub>3 = (\<chi> k. if k = 5 then row 5 Bblk else row k N\<^sub>2)"
  define N\<^sub>4 :: "real^6^6"
    where "N\<^sub>4 = (\<chi> k. if k = 6 then row 6 Bblk else row k N\<^sub>3)"

  text \<open>Step: factor \<open>\<pi>\<close> from row \<open>3\<close>.\<close>
  have A4_chi3: "Ablk\<^sub>4 = (\<chi> i. if i = 3 then pi *s row 3 Bblk else row i Ablk\<^sub>4)"
    using row3_eq by (auto simp: vec_eq_iff row_def)
  have step1: "det Ablk\<^sub>4 = pi * det N\<^sub>1"
  proof -
    have "det (\<chi> i. if i = (3::6) then pi *s (\<lambda>_. row 3 Bblk) i else (\<lambda>i. row i Ablk\<^sub>4) i)
        = pi * det (\<chi> i. if i = 3 then (\<lambda>_. row 3 Bblk) i else (\<lambda>i. row i Ablk\<^sub>4) i)"
      by (rule det_row_mul)
    thus ?thesis using A4_chi3 by (simp add: N\<^sub>1_def)
  qed

  text \<open>Step: factor \<open>\<pi>\<close> from row \<open>4\<close> of \<open>N\<^sub>1\<close>.\<close>
  have N1_row4: "row 4 N\<^sub>1 = pi *s row 4 Bblk"
    using row4_eq by (simp add: N\<^sub>1_def row_def vec_eq_iff)
  have N1_chi4: "N\<^sub>1 = (\<chi> i. if i = 4 then pi *s row 4 Bblk else row i N\<^sub>1)"
    using N1_row4 by (auto simp: vec_eq_iff row_def)
  have step2: "det N\<^sub>1 = pi * det N\<^sub>2"
  proof -
    have "det (\<chi> i. if i = (4::6) then pi *s (\<lambda>_. row 4 Bblk) i else (\<lambda>i. row i N\<^sub>1) i)
        = pi * det (\<chi> i. if i = 4 then (\<lambda>_. row 4 Bblk) i else (\<lambda>i. row i N\<^sub>1) i)"
      by (rule det_row_mul)
    thus ?thesis using N1_chi4 by (simp add: N\<^sub>2_def)
  qed

  text \<open>Step: factor \<open>\<pi>\<^sup>2\<close> from row \<open>5\<close> of \<open>N\<^sub>2\<close>.\<close>
  have N2_row5: "row 5 N\<^sub>2 = (pi^2) *s row 5 Bblk"
    using row5_eq by (simp add: N\<^sub>2_def N\<^sub>1_def row_def vec_eq_iff)
  have N2_chi5: "N\<^sub>2 = (\<chi> i. if i = 5 then (pi^2) *s row 5 Bblk else row i N\<^sub>2)"
    using N2_row5 by (auto simp: vec_eq_iff row_def)
  have step3: "det N\<^sub>2 = (pi^2) * det N\<^sub>3"
  proof -
    have "det (\<chi> i. if i = (5::6) then (pi^2) *s (\<lambda>_. row 5 Bblk) i else (\<lambda>i. row i N\<^sub>2) i)
        = (pi^2) * det (\<chi> i. if i = 5 then (\<lambda>_. row 5 Bblk) i else (\<lambda>i. row i N\<^sub>2) i)"
      by (rule det_row_mul)
    thus ?thesis using N2_chi5 by (simp add: N\<^sub>3_def)
  qed

  text \<open>Step: factor \<open>\<pi>\<^sup>2\<close> from row \<open>6\<close> of \<open>N\<^sub>3\<close>.\<close>
  have N3_row6: "row 6 N\<^sub>3 = (pi^2) *s row 6 Bblk"
    using row6_eq by (simp add: N\<^sub>3_def N\<^sub>2_def N\<^sub>1_def row_def vec_eq_iff)
  have N3_chi6: "N\<^sub>3 = (\<chi> i. if i = 6 then (pi^2) *s row 6 Bblk else row i N\<^sub>3)"
    using N3_row6 by (auto simp: vec_eq_iff row_def)
  have step4: "det N\<^sub>3 = (pi^2) * det N\<^sub>4"
  proof -
    have "det (\<chi> i. if i = (6::6) then (pi^2) *s (\<lambda>_. row 6 Bblk) i else (\<lambda>i. row i N\<^sub>3) i)
        = (pi^2) * det (\<chi> i. if i = 6 then (\<lambda>_. row 6 Bblk) i else (\<lambda>i. row i N\<^sub>3) i)"
      by (rule det_row_mul)
    thus ?thesis using N3_chi6 by (simp add: N\<^sub>4_def)
  qed

  text \<open>\<open>N\<^sub>4 = Bblk\<close>: all six rows now match \<open>Bblk\<close>'s.\<close>
  have N4_eq_B: "N\<^sub>4 = Bblk"
    unfolding N\<^sub>4_def N\<^sub>3_def N\<^sub>2_def N\<^sub>1_def vec_eq_iff
    using row1_eq row2_eq
    by (auto simp: forall_6 row_def)

  have "det Ablk\<^sub>4 = pi * (pi * ((pi^2) * ((pi^2) * det N\<^sub>4)))"
    using step1 step2 step3 step4 by simp
  also have "\<dots> = pi^6 * det Bblk"
    using N4_eq_B by (simp add: field_simps power2_eq_square power_add,
        metis (no_types, lifting) numeral_Bit0_eq_double power2_eq_square power3_eq_cube power_mult
        vector_space_over_itself.scale_scale)
  finally show ?thesis .
qed

lemma det_A: "det Ablk = - sqrt 3 * pi^6 / 18"
  using det_A_eq_det_A\<^sub>4 det_A\<^sub>4_eq_pi6_det_B det_B
  by simp


subsection \<open>The \<open>6\<times>6\<close> \<open>Dblk\<close>-block: \<open>det Dblk = -10\<sqrt>3 \<pi>\<^sup>2\<close>\<close>

text \<open>
  Factor \<open>\<pi>\<^sup>2\<close> from rows \<open>3,4\<close> of \<open>Dblk\<close> to get the constant matrix \<open>Eblk\<close>;
  later we reduce \<open>Eblk\<close> to upper-triangular via row-adds.
\<close>

definition Dblk :: "real^6^6" where
  "Dblk = vector
    [ vector [1, 1/2, -1/2, -1, -1/2, 1/2],
      vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [0, pi / 6, - pi / 3, - pi, -2 * pi / 3, 5 * pi / 6],
      vector [0, - pi * sqrt 3 / 6, - pi * sqrt 3 / 3, 0,
              2 * pi * sqrt 3 / 3, 5 * pi * sqrt 3 / 6],
      vector [4, 2, 0, 0, -2, 2],
      vector [0, -2 * sqrt 3, 0, 0, 2 * sqrt 3, 2 * sqrt 3] ]"

definition Eblk :: "real^6^6" where
  "Eblk = vector
    [ vector [1, 1/2, -1/2, -1, -1/2, 1/2],
      vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [0, 1/6, -1/3, -1, -2/3, 5/6],
      vector [0, - sqrt 3 / 6, - sqrt 3 / 3, 0, 2 * sqrt 3 / 3, 5 * sqrt 3 / 6],
      vector [4, 2, 0, 0, -2, 2],
      vector [0, -2 * sqrt 3, 0, 0, 2 * sqrt 3, 2 * sqrt 3] ]"

subsubsection \<open>Factor \<open>\<pi>\<^sup>2\<close>: \<open>det Dblk = \<pi>\<^sup>2 \<cdot> det Eblk\<close>\<close>

lemma det_D_eq_pi2_det_E: "det Dblk = pi^2 * det Eblk"
proof -
  have row1_eq: "row 1 Dblk = row 1 Eblk"
    unfolding Dblk_def Eblk_def vec_eq_iff by (auto simp: forall_6 row_def)
  have row2_eq: "row 2 Dblk = row 2 Eblk"
    unfolding Dblk_def Eblk_def vec_eq_iff by (auto simp: forall_6 row_def)
  have row3_eq: "row 3 Dblk = pi *s row 3 Eblk"
    unfolding Dblk_def Eblk_def vec_eq_iff by (auto simp: forall_6 row_def field_simps)
  have row4_eq: "row 4 Dblk = pi *s row 4 Eblk"
    unfolding Dblk_def Eblk_def vec_eq_iff by (auto simp: forall_6 row_def field_simps)
  have row5_eq: "row 5 Dblk = row 5 Eblk"
    unfolding Dblk_def Eblk_def vec_eq_iff by (auto simp: forall_6 row_def)
  have row6_eq: "row 6 Dblk = row 6 Eblk"
    unfolding Dblk_def Eblk_def vec_eq_iff by (auto simp: forall_6 row_def)

  define M\<^sub>1 :: "real^6^6"
    where "M\<^sub>1 = (\<chi> k. if k = 3 then row 3 Eblk else row k Dblk)"
  define M\<^sub>2 :: "real^6^6"
    where "M\<^sub>2 = (\<chi> k. if k = 4 then row 4 Eblk else row k M\<^sub>1)"

  text \<open>Factor \<open>\<pi>\<close> from row \<open>3\<close>.\<close>
  have D_chi3: "Dblk = (\<chi> i. if i = 3 then pi *s row 3 Eblk else row i Dblk)"
    using row3_eq by (auto simp: vec_eq_iff row_def)
  have step1: "det Dblk = pi * det M\<^sub>1"
  proof -
    have "det (\<chi> i. if i = (3::6) then pi *s (\<lambda>_. row 3 Eblk) i else (\<lambda>i. row i Dblk) i)
        = pi * det (\<chi> i. if i = 3 then (\<lambda>_. row 3 Eblk) i else (\<lambda>i. row i Dblk) i)"
      by (rule det_row_mul)
    thus ?thesis using D_chi3 by (simp add: M\<^sub>1_def)
  qed

  text \<open>Factor \<open>\<pi>\<close> from row \<open>4\<close> of \<open>M\<^sub>1\<close>.\<close>
  have M1_row4: "row 4 M\<^sub>1 = pi *s row 4 Eblk"
    using row4_eq by (simp add: M\<^sub>1_def row_def vec_eq_iff)
  have M1_chi4: "M\<^sub>1 = (\<chi> i. if i = 4 then pi *s row 4 Eblk else row i M\<^sub>1)"
    using M1_row4 by (auto simp: vec_eq_iff row_def)
  have step2: "det M\<^sub>1 = pi * det M\<^sub>2"
  proof -
    have "det (\<chi> i. if i = (4::6) then pi *s (\<lambda>_. row 4 Eblk) i else (\<lambda>i. row i M\<^sub>1) i)
        = pi * det (\<chi> i. if i = 4 then (\<lambda>_. row 4 Eblk) i else (\<lambda>i. row i M\<^sub>1) i)"
      by (rule det_row_mul)
    thus ?thesis using M1_chi4 by (simp add: M\<^sub>2_def)
  qed

  text \<open>\<open>M\<^sub>2 = Eblk\<close>: rows \<open>3,4\<close> set to \<open>Eblk\<close>'s, rows \<open>1,2,5,6\<close> already match.\<close>
  have M2_eq_E: "M\<^sub>2 = Eblk"
    unfolding M\<^sub>2_def M\<^sub>1_def vec_eq_iff
    using row1_eq row2_eq row5_eq row6_eq
    by (auto simp: forall_6 row_def)

  have "det Dblk = pi * (pi * det M\<^sub>2)" using step1 step2 by simp
  also have "\<dots> = (pi * pi) * det Eblk" using M2_eq_E by (simp add: algebra_simps)
  also have "\<dots> = pi^2 * det Eblk" by (simp add: power2_eq_square)
  finally show ?thesis .
qed

subsubsection \<open>Row-reduction chain for \<open>Eblk\<close> (to upper-triangular \<open>Eblk\<^sub>5\<close>)\<close>

text \<open>\<open>Eblk\<^sub>1\<close>: \<open>R\<^sub>5 \<leftarrow> R\<^sub>5 - 4 R\<^sub>1\<close>, \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 - 4 R\<^sub>2\<close>.\<close>

definition Eblk\<^sub>1 :: "real^6^6" where
  "Eblk\<^sub>1 = vector
    [ vector [1, 1/2, -1/2, -1, -1/2, 1/2],
      vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [0, 1/6, -1/3, -1, -2/3, 5/6],
      vector [0, - sqrt 3 / 6, - sqrt 3 / 3, 0, 2 * sqrt 3 / 3, 5 * sqrt 3 / 6],
      vector [0, 0, 2, 4, 0, 0],
      vector [0, 0, 2 * sqrt 3, 0, 0, 0] ]"

lemma det_E_eq_det_E\<^sub>1: "det Eblk = det Eblk\<^sub>1"
proof -
  define V\<^sub>1 :: "real^6^6"
    where "V\<^sub>1 = (\<chi> k. if k = 5 then row 5 Eblk + (-4) *s row 1 Eblk else row k Eblk)"
  define V\<^sub>2 :: "real^6^6"
    where "V\<^sub>2 = (\<chi> k. if k = 6 then row 6 V\<^sub>1 + (-4) *s row 2 V\<^sub>1 else row k V\<^sub>1)"
  have d1: "det V\<^sub>1 = det Eblk"
    unfolding V\<^sub>1_def by (rule det_row_operation) auto
  have d2: "det V\<^sub>2 = det V\<^sub>1"
    unfolding V\<^sub>2_def by (rule det_row_operation) auto
  have eq: "V\<^sub>2 = Eblk\<^sub>1"
    unfolding V\<^sub>2_def V\<^sub>1_def Eblk_def Eblk\<^sub>1_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps)
  show ?thesis using d1 d2 eq by simp
qed

text \<open>\<open>Eblk\<^sub>2\<close>: \<open>R\<^sub>3 \<leftarrow> R\<^sub>3 + (\<sqrt>3/9) R\<^sub>2\<close>, \<open>R\<^sub>4 \<leftarrow> R\<^sub>4 - (1/3) R\<^sub>2\<close>.\<close>

definition Eblk\<^sub>2 :: "real^6^6" where
  "Eblk\<^sub>2 = vector
    [ vector [1, 1/2, -1/2, -1, -1/2, 1/2],
      vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [0, 0, -1/2, -1, -1/2, 1],
      vector [0, 0, - sqrt 3 / 6, 0, sqrt 3 / 2, 2 * sqrt 3 / 3],
      vector [0, 0, 2, 4, 0, 0],
      vector [0, 0, 2 * sqrt 3, 0, 0, 0] ]"

lemma det_E\<^sub>1_eq_det_E\<^sub>2: "det Eblk\<^sub>1 = det Eblk\<^sub>2"
proof -
  define W\<^sub>1 :: "real^6^6"
    where "W\<^sub>1 = (\<chi> k. if k = 3 then row 3 Eblk\<^sub>1 + (sqrt 3 / 9) *s row 2 Eblk\<^sub>1 else row k Eblk\<^sub>1)"
  define W\<^sub>2 :: "real^6^6"
    where "W\<^sub>2 = (\<chi> k. if k = 4 then row 4 W\<^sub>1 + (-1/3) *s row 2 W\<^sub>1 else row k W\<^sub>1)"
  have d1: "det W\<^sub>1 = det Eblk\<^sub>1"
    unfolding W\<^sub>1_def by (rule det_row_operation) auto
  have d2: "det W\<^sub>2 = det W\<^sub>1"
    unfolding W\<^sub>2_def by (rule det_row_operation) auto
  have eq: "W\<^sub>2 = Eblk\<^sub>2"
    unfolding W\<^sub>2_def W\<^sub>1_def Eblk\<^sub>1_def Eblk\<^sub>2_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps power2_eq_square)
  show ?thesis using d1 d2 eq by simp
qed

text \<open>\<open>Eblk\<^sub>3\<close>: \<open>R\<^sub>4 \<leftarrow> R\<^sub>4 - (\<sqrt>3/3) R\<^sub>3\<close>, \<open>R\<^sub>5 \<leftarrow> R\<^sub>5 + 4 R\<^sub>3\<close>, \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 + 4\<sqrt>3 R\<^sub>3\<close>.\<close>

definition Eblk\<^sub>3 :: "real^6^6" where
  "Eblk\<^sub>3 = vector
    [ vector [1, 1/2, -1/2, -1, -1/2, 1/2],
      vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [0, 0, -1/2, -1, -1/2, 1],
      vector [0, 0, 0, sqrt 3 / 3, 2 * sqrt 3 / 3, sqrt 3 / 3],
      vector [0, 0, 0, 0, -2, 4],
      vector [0, 0, 0, -4 * sqrt 3, -2 * sqrt 3, 4 * sqrt 3] ]"

lemma det_E\<^sub>2_eq_det_E\<^sub>3: "det Eblk\<^sub>2 = det Eblk\<^sub>3"
proof -
  define Y\<^sub>1 :: "real^6^6"
    where "Y\<^sub>1 = (\<chi> k. if k = 4 then row 4 Eblk\<^sub>2 + (- sqrt 3 / 3) *s row 3 Eblk\<^sub>2 else row k Eblk\<^sub>2)"
  define Y\<^sub>2 :: "real^6^6"
    where "Y\<^sub>2 = (\<chi> k. if k = 5 then row 5 Y\<^sub>1 + 4 *s row 3 Y\<^sub>1 else row k Y\<^sub>1)"
  define Y\<^sub>3 :: "real^6^6"
    where "Y\<^sub>3 = (\<chi> k. if k = 6 then row 6 Y\<^sub>2 + (4 * sqrt 3) *s row 3 Y\<^sub>2 else row k Y\<^sub>2)"
  have d1: "det Y\<^sub>1 = det Eblk\<^sub>2"
    unfolding Y\<^sub>1_def by (rule det_row_operation) auto
  have d2: "det Y\<^sub>2 = det Y\<^sub>1"
    unfolding Y\<^sub>2_def by (rule det_row_operation) auto
  have d3: "det Y\<^sub>3 = det Y\<^sub>2"
    unfolding Y\<^sub>3_def by (rule det_row_operation) auto
  have eq: "Y\<^sub>3 = Eblk\<^sub>3"
    unfolding Y\<^sub>3_def Y\<^sub>2_def Y\<^sub>1_def Eblk\<^sub>2_def Eblk\<^sub>3_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps power2_eq_square)
  show ?thesis using d1 d2 d3 eq by simp
qed

text \<open>\<open>Eblk\<^sub>4\<close>: \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 + 12 R\<^sub>4\<close>.\<close>

definition Eblk\<^sub>4 :: "real^6^6" where
  "Eblk\<^sub>4 = vector
    [ vector [1, 1/2, -1/2, -1, -1/2, 1/2],
      vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [0, 0, -1/2, -1, -1/2, 1],
      vector [0, 0, 0, sqrt 3 / 3, 2 * sqrt 3 / 3, sqrt 3 / 3],
      vector [0, 0, 0, 0, -2, 4],
      vector [0, 0, 0, 0, 6 * sqrt 3, 8 * sqrt 3] ]"

lemma det_E\<^sub>3_eq_det_E\<^sub>4: "det Eblk\<^sub>3 = det Eblk\<^sub>4"
proof -
  define Z :: "real^6^6"
    where "Z = (\<chi> k. if k = 6 then row 6 Eblk\<^sub>3 + 12 *s row 4 Eblk\<^sub>3 else row k Eblk\<^sub>3)"
  have d: "det Z = det Eblk\<^sub>3"
    unfolding Z_def by (rule det_row_operation) auto
  have eq: "Z = Eblk\<^sub>4"
    unfolding Z_def Eblk\<^sub>3_def Eblk\<^sub>4_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps)
  show ?thesis using d eq by simp
qed

text \<open>\<open>Eblk\<^sub>5\<close>: \<open>R\<^sub>6 \<leftarrow> R\<^sub>6 + 3\<sqrt>3 R\<^sub>5\<close>. Upper triangular.\<close>

definition Eblk\<^sub>5 :: "real^6^6" where
  "Eblk\<^sub>5 = vector
    [ vector [1, 1/2, -1/2, -1, -1/2, 1/2],
      vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [0, 0, -1/2, -1, -1/2, 1],
      vector [0, 0, 0, sqrt 3 / 3, 2 * sqrt 3 / 3, sqrt 3 / 3],
      vector [0, 0, 0, 0, -2, 4],
      vector [0, 0, 0, 0, 0, 20 * sqrt 3] ]"

lemma det_E\<^sub>4_eq_det_E\<^sub>5: "det Eblk\<^sub>4 = det Eblk\<^sub>5"
proof -
  define Z :: "real^6^6"
    where "Z = (\<chi> k. if k = 6 then row 6 Eblk\<^sub>4 + (3 * sqrt 3) *s row 5 Eblk\<^sub>4 else row k Eblk\<^sub>4)"
  have d: "det Z = det Eblk\<^sub>4"
    unfolding Z_def by (rule det_row_operation) auto
  have eq: "Z = Eblk\<^sub>5"
    unfolding Z_def Eblk\<^sub>4_def Eblk\<^sub>5_def vec_eq_iff
    by (auto simp: forall_6 row_def field_simps power2_eq_square)
  show ?thesis using d eq by simp
qed

subsubsection \<open>Read off \<open>det Eblk\<^sub>5\<close> from the diagonal\<close>

lemma det_E\<^sub>5: "det Eblk\<^sub>5 = -10 * sqrt 3"
proof -
  text \<open>Sparse: brute-force perm sum collapses to the diagonal product.\<close>
  have f1: "finite {2::6, 3, 4, 5, 6}" "1 \<notin> {2::6, 3, 4, 5, 6}" by auto
  have f2: "finite {3::6, 4, 5, 6}"    "2 \<notin> {3::6, 4, 5, 6}"    by auto
  have f3: "finite {4::6, 5, 6}"       "3 \<notin> {4::6, 5, 6}"       by auto
  have f4: "finite {5::6, 6}"          "4 \<notin> {5::6, 6}"          by auto
  have f5: "finite {6::6}"             "5 \<notin> {6::6}"             by auto
  show ?thesis
    unfolding Eblk\<^sub>5_def det_def UNIV_6
    unfolding sum_over_permutations_insert[OF f1]
    unfolding sum_over_permutations_insert[OF f2]
    unfolding sum_over_permutations_insert[OF f3]
    unfolding sum_over_permutations_insert[OF f4]
    unfolding sum_over_permutations_insert[OF f5]
    unfolding permutes_sing
    by (simp add: sign_swap_id permutation_swap_id sign_compose sign_id swap_id_eq
                  field_simps power2_eq_square)
qed

subsubsection \<open>Combining: \<open>det Dblk = -10\<sqrt>3 \<pi>\<^sup>2\<close>\<close>

lemma det_D: "det Dblk = -10 * sqrt 3 * pi^2"
proof -
  have "det Dblk = pi^2 * det Eblk" by (rule det_D_eq_pi2_det_E)
  also have "\<dots> = pi^2 * det Eblk\<^sub>5"
    using det_E_eq_det_E\<^sub>1 det_E\<^sub>1_eq_det_E\<^sub>2 det_E\<^sub>2_eq_det_E\<^sub>3
          det_E\<^sub>3_eq_det_E\<^sub>4 det_E\<^sub>4_eq_det_E\<^sub>5 by simp
  also have "\<dots> = pi^2 * (-10 * sqrt 3)" by (simp add: det_E\<^sub>5)
  also have "\<dots> = -10 * sqrt 3 * pi^2" by simp
  finally show ?thesis .
qed

end
