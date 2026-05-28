theory Moment_Map
  imports
    Block_Determinants
    "HOL-Analysis.Derivative"
begin

text \<open>
  The paper's six-component moment map and its Fréchet derivative
  infrastructure, factored out of \<open>Nonemptiness_Paper.thy\<close> so it can
  be baked into the \<open>Applied_Math_BlockDet\<close> heap.

  Once cached, the heavy operator-overload elaboration cost of the per-term
  derivative lemmas (\<open>has_derivative_M\<^sub>1\<^sub>2_term\<close> in particular) is paid only
  once at heap-build time; downstream theories that use these lemmas see
  them as single-fact lookups.
\<close>

type_synonym planar = "real^2"

subsection \<open>Phase factor and its differential\<close>

text \<open>
  Every moment of the paper is a sum of terms \<open>w(p\<^sub>n) \<cdot> e\<^sup>-\<imath>\<^sup>(\<^sup>c\<^sup>\<cdot>\<^sup>p\<^sup>_\<^sup>n\<^sup>)\<close> where
  \<open>w\<close> is a polynomial weight (\<open>1, p\<^sub>1, p\<^sub>2, p\<^sub>1\<^sup>2, p\<^sub>1 p\<^sub>2, p\<^sub>2\<^sup>2\<close>). To keep
  the elaborator's work bounded as we manipulate these terms, we introduce
  two concrete constants once and for all:

  \<^item> \<open>phase\<close> --- the paper's phase factor \<open>e\<^sup>-\<imath>\<^sup>(\<^sup>c\<^sup>\<cdot>\<^sup>(\<^sup>x\<^sup>$\<^sup>n\<^sup>)\<^sup>)\<close>.
  \<^item> \<open>d_phase\<close> --- its Fréchet differential at the configuration
    \<open>x\<close>, applied to a perturbation \<open>h\<close>.

  These are not abstractions over arbitrary functions; they are concrete
  definitions of the paper's actual quantities. Using them in lemma
  statements reduces each expression from a tree of polymorphic operators
  to a single constant lookup.
\<close>

definition phase :: "planar \<Rightarrow> (planar^'n) \<Rightarrow> 'n \<Rightarrow> complex"
  where "phase c y n = cis (-(c \<bullet> (y $ n)))"

definition d_phase :: "planar \<Rightarrow> (planar^'n) \<Rightarrow> (planar^'n) \<Rightarrow> 'n \<Rightarrow> complex"
  where "d_phase c x h n = -(c \<bullet> (h $ n)) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n))))"

text \<open>The mixed-coordinate weight for the \<open>M\<^sub>1\<^sub>2\<close> moment and its
  directional derivative. The inner product-of-coordinates carries an
  inner \<open>+\<close>, two products, and four polymorphic \<open>$ k\<close> applications --- in
  M12's lemma statements this expression appears multiple times and gives
  the elaborator a combinatorially expensive \<open>*\<close>-overload graph to solve.
  Wrapping it as a named constant collapses each occurrence to a single
  function call.\<close>

definition w_M12 :: "planar \<Rightarrow> real"
  where "w_M12 p = (p $ 1) * (p $ 2)"

definition dw_M12 :: "planar \<Rightarrow> planar \<Rightarrow> real"
  where "dw_M12 p dp = (dp $ 1) * (p $ 2) + (p $ 1) * (dp $ 2)"


subsection \<open>The paper's six-component moment map\<close>

text \<open>
  TeX (Section ``Moment-space form of the bad-point map'') defines, for each
  configuration \<open>x = (p\<^sub>1, \<dots>, p\<^sub>N) \<in> (\<real>\<^sup>2)\<^sup>N\<close> and each
  parameter \<open>c \<in> \<real>\<^sup>2\<close>,
  \begin{align*}
    A      &= \textstyle\sum_n e^{-\imath\, c\cdot p_n},\\
    M_k    &= \textstyle\sum_n p_{n,k}\, e^{-\imath\, c\cdot p_n},
              \quad k=1,2,\\
    M_{kl} &= \textstyle\sum_n p_{n,k} p_{n,l}\, e^{-\imath\, c\cdot p_n},
              \quad (k,l) \in \{(1,1),(1,2),(2,2)\}.
  \end{align*}
  Using \<^const>\<open>phase\<close> for the phase factor, the six moments are bundled
  into the moment map \<open>M_paper : (\<real>\<^sup>2)\<^sup>N \<times> \<real>\<^sup>2 \<rightarrow> \<complex>\<^sup>6\<close>.

  Each moment is a weighted variant of the same phase factor with a
  polynomial weight; defining each one directly via \<^const>\<open>phase\<close> lets the
  Jacobian identification \<open>D(M_paper)(x\<^sub>0) = (*v) bigJ\<close> be checked
  entry-by-entry against the column formulas of TeX Section ``Surjectivity
  of the moment map''.
\<close>

definition A_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "A_moment x c = (\<Sum>n\<in>UNIV. phase c x n)"

definition M1_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M1_moment x c = (\<Sum>n\<in>UNIV. of_real ((x $ n) $ 1) * phase c x n)"

definition M2_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M2_moment x c = (\<Sum>n\<in>UNIV. of_real ((x $ n) $ 2) * phase c x n)"

definition M11_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M11_moment x c = (\<Sum>n\<in>UNIV. of_real (((x $ n) $ 1)\<^sup>2) * phase c x n)"

definition M12_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M12_moment x c = (\<Sum>n\<in>UNIV. of_real (w_M12 (x $ n)) * phase c x n)"

definition M22_moment :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex"
  where "M22_moment x c = (\<Sum>n\<in>UNIV. of_real (((x $ n) $ 2)\<^sup>2) * phase c x n)"

text \<open>
  The moment map itself, packaged as a \<^typ>\<open>complex^6\<close>-valued function. The
  component order at indices \<open>1,2,3,4,5,6\<close> is
  \<open>(A, M\<^sub>1, M\<^sub>2, M\<^sub>1\<^sub>1, M\<^sub>1\<^sub>2, M\<^sub>2\<^sub>2)\<close>, matching the row order of \<open>bigJ\<close>
  (real parts even, imaginary parts odd, paired): \<open>\<real>A,\<I>A, \<real>M\<^sub>1,\<I>M\<^sub>1, \<dots>,
  \<real>M\<^sub>2\<^sub>2,\<I>M\<^sub>2\<^sub>2\<close>.
\<close>

definition M_paper :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> complex^6"
  where
  "M_paper x c = vector
    [ A_moment   x c,
      M1_moment  x c,
      M2_moment  x c,
      M11_moment x c,
      M12_moment x c,
      M22_moment x c ]"

text \<open>Convenience: project the \<open>k\<close>-th moment out by name.\<close>

lemma M_paper_components [simp]:
  shows "M_paper x c $ 1 = A_moment   x c"
    and "M_paper x c $ 2 = M1_moment  x c"
    and "M_paper x c $ 3 = M2_moment  x c"
    and "M_paper x c $ 4 = M11_moment x c"
    and "M_paper x c $ 5 = M12_moment x c"
    and "M_paper x c $ 6 = M22_moment x c"
  unfolding M_paper_def
  by ((simp add: vector_def)+)

subsection \<open>Derivative of \<^const>\<open>M_paper\<close> with respect to the configuration\<close>

text \<open>
  For fixed steering parameter \<open>c\<close>, every component of the moment map
  \<^const>\<open>M_paper\<close> is a sum over \<open>n\<close> of a term of the form
  \<open>w(x $ n) \<cdot> cis(-(c \<bullet> (x $ n)))\<close> where \<open>w\<close> is one of six polynomial
  weights (\<open>1\<close>, \<open>p\<^sub>1\<close>, \<open>p\<^sub>2\<close>, \<open>p\<^sub>1\<^sup>2\<close>, \<open>p\<^sub>1 p\<^sub>2\<close>, \<open>p\<^sub>2\<^sup>2\<close>). The derivative
  of each term in \<open>x\<close> follows from the chain and product rules. We assemble
  the Fréchet derivative \<open>D\<^sub>x M_paper(x,c)\<close> componentwise.
\<close>

text \<open>\<^bold>\<open>Layer 1.\<close> The fundamental building block: differentiability of
  \<open>cis(-(c \<bullet> (x $ n)))\<close> in \<open>x\<close>.\<close>

lemma has_derivative_inner_const_nth_x:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. c \<bullet> (y $ n)) has_derivative (\<lambda>h. c \<bullet> (h $ n)))
         (at x within V)"
proof -
  have lin: "linear (\<lambda>y :: planar^'n. c \<bullet> (y $ n))"
    by (intro linearI) (simp_all add: inner_right_distrib)
  show ?thesis using linear_imp_has_derivative[OF lin] .
qed

lemma has_derivative_cis_neg_inner_x:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. cis (-(c \<bullet> (y $ n)))) has_derivative
            (\<lambda>h. (-(c \<bullet> (h $ n))) *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n))))))
         (at x within V)"
proof -
  have neg_inner_deriv:
    "((\<lambda>y :: planar^'n. -(c \<bullet> (y $ n))) has_derivative (\<lambda>h. -(c \<bullet> (h $ n))))
         (at x within V)"
    using has_derivative_inner_const_nth_x[where c = c and n = n and x = x and V = V]
    by (rule has_derivative_minus)
  have cis_deriv:
    "(cis has_derivative (\<lambda>r. r *\<^sub>R (\<i> * cis (-(c \<bullet> (x $ n))))))
         (at (-(c \<bullet> (x $ n))))"
    by (auto intro!: derivative_eq_intros)
  show ?thesis
    using has_derivative_compose[OF neg_inner_deriv cis_deriv] by (simp add: o_def)
qed

text \<open>\<^bold>\<open>Layer 2.\<close> Component access: \<open>(x $ n) $ k\<close> is linear (and thus
  differentiable with itself as derivative) in \<open>x\<close> for each fixed \<open>n, k\<close>.\<close>

lemma has_derivative_nth_k_x:
  fixes n :: "'n::finite" and k :: 2
  shows "((\<lambda>y :: planar^'n. (y $ n) $ k) has_derivative (\<lambda>h. (h $ n) $ k))
         (at x within V)"
proof -
  have lin: "linear (\<lambda>y :: planar^'n. (y $ n) $ k)"
    by (intro linearI) simp_all
  show ?thesis using linear_imp_has_derivative[OF lin] .
qed

text \<open>\<^bold>\<open>Layer 3.\<close> Per-term derivatives. Each moment's \<open>n\<close>-th summand
  \<open>w(x $ n) \<cdot> cis(-(c \<bullet> (x $ n)))\<close> is differentiable by the product rule.\<close>

text \<open>Helper: lift a real-valued derivative through the embedding
  \<^const>\<open>of_real\<close> (which is real-linear from \<^typ>\<open>real\<close> to \<^typ>\<open>complex\<close>),
  yielding a \<^typ>\<open>complex\<close>-valued derivative.\<close>

lemma has_derivative_of_real_lift:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "(f has_derivative f') (at x within V)"
  shows "((\<lambda>y. of_real (f y) :: complex) has_derivative (\<lambda>h. of_real (f' h)))
         (at x within V)"
proof -
  have lin: "linear (of_real :: real \<Rightarrow> complex)"
    by (intro linearI) (simp_all add: scaleR_conv_of_real)
  have outer: "(of_real has_derivative (of_real :: real \<Rightarrow> complex))
                  (at (f x) within f ` V)"
    using linear_imp_has_derivative[OF lin] .
  show ?thesis
    using has_derivative_in_compose[OF assms outer] by (simp add: o_def)
qed

text \<open>One-line lift of \<open>has_derivative_cis_neg_inner_x\<close> into
  \<^const>\<open>phase\<close>/\<^const>\<open>d_phase\<close> notation, used by every downstream term and
  moment derivative lemma so their statements collapse to a single
  constant-lookup tree (no nested polymorphic operators).\<close>

lemma has_derivative_phase_x:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. phase c y n) has_derivative (\<lambda>h. d_phase c x h n))
         (at x within V)"
  unfolding phase_def d_phase_def
  by (rule has_derivative_cis_neg_inner_x)

lemma has_derivative_A_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. phase c y n) has_derivative (\<lambda>h. d_phase c x h n))
         (at x within V)"
  by (rule has_derivative_phase_x)

lemma has_derivative_nth_k_sq_x:
  fixes x :: "planar^'n"
    and V :: "(planar^'n) set"
    and n :: "'n::finite"
    and k :: 2
  shows "((\<lambda>y :: planar^'n. ((y $ n) $ k)\<^sup>2)
            has_derivative
            (\<lambda>h. 2 * ((x $ n) $ k) * ((h $ n) $ k)))
         (at x within V)"
proof -
  have d_nth:
    "((\<lambda>y :: planar^'n. (y $ n) $ k)
        has_derivative
        (\<lambda>h. (h $ n) $ k))
     (at x within V)"
    by (rule has_derivative_nth_k_x)

  have d_prod:
    "((\<lambda>y :: planar^'n. ((y $ n) $ k) * ((y $ n) $ k))
        has_derivative
        (\<lambda>h. ((x $ n) $ k) * ((h $ n) $ k)
           + ((h $ n) $ k) * ((x $ n) $ k)))
     (at x within V)"
    using d_nth d_nth
    by (rule has_derivative_mult)

  then show ?thesis
    by (simp add: power2_eq_square algebra_simps)
qed

lemma has_derivative_M1_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 1) * phase c y n)
            has_derivative
            (\<lambda>h. of_real ((h $ n) $ 1) * phase c x n
               + of_real ((x $ n) $ 1) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 1) :: complex) has_derivative
      (\<lambda>h. of_real ((h $ n) $ 1))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_x])

  have d_phase:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
      (\<lambda>h. d_phase c x h n)) (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 1) * phase c y n)
       has_derivative
       (\<lambda>h. of_real ((x $ n) $ 1) * d_phase c x h n
          + of_real ((h $ n) $ 1) * phase c x n))
     (at x within V)"
    using d_real d_phase
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

lemma has_derivative_M2_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 2) * phase c y n)
            has_derivative
            (\<lambda>h. of_real ((h $ n) $ 2) * phase c x n
               + of_real ((x $ n) $ 2) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 2) :: complex) has_derivative
      (\<lambda>h. of_real ((h $ n) $ 2))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_x])

  have dph:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
      (\<lambda>h. d_phase c x h n)) (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real ((y $ n) $ 2) * phase c y n)
       has_derivative
       (\<lambda>h. of_real ((x $ n) $ 2) * d_phase c x h n
          + of_real ((h $ n) $ 2) * phase c x n))
     (at x within V)"
    using d_real dph
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

lemma has_derivative_M11_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 1)\<^sup>2) * phase c y n)
            has_derivative
            (\<lambda>h. of_real (2 * ((x $ n) $ 1) * ((h $ n) $ 1)) * phase c x n
               + of_real (((x $ n) $ 1)\<^sup>2) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 1)\<^sup>2) :: complex) has_derivative
        (\<lambda>h. of_real (2 * ((x $ n) $ 1) * ((h $ n) $ 1)))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_sq_x])

  have dph:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
        (\<lambda>h. d_phase c x h n))
     (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 1)\<^sup>2) * phase c y n)
        has_derivative
        (\<lambda>h. of_real (((x $ n) $ 1)\<^sup>2) * d_phase c x h n
           + of_real (2 * ((x $ n) $ 1) * ((h $ n) $ 1)) * phase c x n))
     (at x within V)"
    using d_real dph
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

lemma has_derivative_M12_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real (w_M12 (y $ n)) * phase c y n)
            has_derivative
            (\<lambda>h. of_real (dw_M12 (x $ n) (h $ n)) * phase c x n
               + of_real (w_M12 (x $ n)) * d_phase c x h n))
         (at x within V)"
proof -
  have d1:
    "((\<lambda>y :: planar^'n. (y $ n) $ 1) has_derivative (\<lambda>h. (h $ n) $ 1))
     (at x within V)"
    by (rule has_derivative_nth_k_x)

  have d2:
    "((\<lambda>y :: planar^'n. (y $ n) $ 2) has_derivative (\<lambda>h. (h $ n) $ 2))
     (at x within V)"
    by (rule has_derivative_nth_k_x)

  have d_prod:
    "((\<lambda>y :: planar^'n. ((y $ n) $ 1) * ((y $ n) $ 2))
        has_derivative
        (\<lambda>h. ((x $ n) $ 1) * ((h $ n) $ 2)
           + ((h $ n) $ 1) * ((x $ n) $ 2)))
     (at x within V)"
    using d1 d2
    by (rule has_derivative_mult)

  have d_w:
    "((\<lambda>y :: planar^'n. w_M12 (y $ n)) has_derivative
        (\<lambda>h. dw_M12 (x $ n) (h $ n)))
     (at x within V)"
    using d_prod
    unfolding w_M12_def dw_M12_def
    by (simp add: algebra_simps)

  have d_real:
    "((\<lambda>y :: planar^'n. of_real (w_M12 (y $ n)) :: complex)
        has_derivative
        (\<lambda>h. of_real (dw_M12 (x $ n) (h $ n))))
     (at x within V)"
    by (rule has_derivative_of_real_lift[OF d_w])

  have dph:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
        (\<lambda>h. d_phase c x h n))
     (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real (w_M12 (y $ n)) * phase c y n)
        has_derivative
        (\<lambda>h. of_real (w_M12 (x $ n)) * d_phase c x h n
           + of_real (dw_M12 (x $ n) (h $ n)) * phase c x n))
     (at x within V)"
    using d_real dph
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

lemma has_derivative_M22_term:
  fixes c :: planar
  shows "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 2)\<^sup>2) * phase c y n)
            has_derivative
            (\<lambda>h. of_real (2 * ((x $ n) $ 2) * ((h $ n) $ 2)) * phase c x n
               + of_real (((x $ n) $ 2)\<^sup>2) * d_phase c x h n))
         (at x within V)"
proof -
  have d_real:
    "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 2)\<^sup>2) :: complex) has_derivative
        (\<lambda>h. of_real (2 * ((x $ n) $ 2) * ((h $ n) $ 2)))) (at x within V)"
    by (rule has_derivative_of_real_lift[OF has_derivative_nth_k_sq_x])

  have dph:
    "((\<lambda>y :: planar^'n. phase c y n) has_derivative
        (\<lambda>h. d_phase c x h n))
     (at x within V)"
    unfolding phase_def d_phase_def
    by (rule has_derivative_cis_neg_inner_x)

  have prod:
    "((\<lambda>y :: planar^'n. of_real (((y $ n) $ 2)\<^sup>2) * phase c y n)
        has_derivative
        (\<lambda>h. of_real (((x $ n) $ 2)\<^sup>2) * d_phase c x h n
           + of_real (2 * ((x $ n) $ 2) * ((h $ n) $ 2)) * phase c x n))
     (at x within V)"
    using d_real dph
    by (rule has_derivative_mult)

  show ?thesis
    using prod
    by (simp add: algebra_simps)
qed

text \<open>\<^bold>\<open>Layer 4.\<close> Sum each moment over \<open>n \<in> UNIV\<close>; the result is the
  per-moment Fréchet derivative. We define each derivative as a \<^emph>\<open>named
  constant\<close> so that downstream expressions (in particular \<open>DM_paper_x\<close>)
  do not have to carry the unfolded sum-of-products tree --- they reference
  the constant by name and the elaborator pays no per-occurrence cost.\<close>

definition d_A_moment_x :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n) \<Rightarrow> complex"
  where "d_A_moment_x x c h = (\<Sum>n\<in>UNIV. d_phase c x h n)"

definition d_M1_moment_x :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n) \<Rightarrow> complex"
  where "d_M1_moment_x x c h
           = (\<Sum>n\<in>UNIV. of_real ((h $ n) $ 1) * phase c x n
                      + of_real ((x $ n) $ 1) * d_phase c x h n)"

definition d_M2_moment_x :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n) \<Rightarrow> complex"
  where "d_M2_moment_x x c h
           = (\<Sum>n\<in>UNIV. of_real ((h $ n) $ 2) * phase c x n
                      + of_real ((x $ n) $ 2) * d_phase c x h n)"

definition d_M11_moment_x :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n) \<Rightarrow> complex"
  where "d_M11_moment_x x c h
           = (\<Sum>n\<in>UNIV.
                of_real (2 * ((x $ n) $ 1) * ((h $ n) $ 1)) * phase c x n
              + of_real (((x $ n) $ 1)\<^sup>2) * d_phase c x h n)"

definition d_M12_moment_x :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n) \<Rightarrow> complex"
  where "d_M12_moment_x x c h
           = (\<Sum>n\<in>UNIV. of_real (dw_M12 (x $ n) (h $ n)) * phase c x n
                      + of_real (w_M12 (x $ n)) * d_phase c x h n)"

definition d_M22_moment_x :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> (planar^'n) \<Rightarrow> complex"
  where "d_M22_moment_x x c h
           = (\<Sum>n\<in>UNIV.
                of_real (2 * ((x $ n) $ 2) * ((h $ n) $ 2)) * phase c x n
              + of_real (((x $ n) $ 2)\<^sup>2) * d_phase c x h n)"

lemma has_derivative_A_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. A_moment y c) has_derivative (\<lambda>h. d_A_moment_x x c h))
         (at x within V)"
  unfolding A_moment_def d_A_moment_x_def
  by (rule has_derivative_sum) (use has_derivative_A_term in blast)

lemma has_derivative_M1_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M1_moment y c) has_derivative (\<lambda>h. d_M1_moment_x x c h))
         (at x within V)"
  unfolding M1_moment_def d_M1_moment_x_def
  by (rule has_derivative_sum) (use has_derivative_M1_term in blast)

lemma has_derivative_M2_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M2_moment y c) has_derivative (\<lambda>h. d_M2_moment_x x c h))
         (at x within V)"
  unfolding M2_moment_def d_M2_moment_x_def
  by (rule has_derivative_sum) (use has_derivative_M2_term in blast)

lemma has_derivative_M11_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M11_moment y c) has_derivative (\<lambda>h. d_M11_moment_x x c h))
         (at x within V)"
  unfolding M11_moment_def d_M11_moment_x_def
  by (rule has_derivative_sum) (use has_derivative_M11_term in blast)

lemma has_derivative_M12_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M12_moment y c) has_derivative (\<lambda>h. d_M12_moment_x x c h))
         (at x within V)"
  unfolding M12_moment_def d_M12_moment_x_def
  by (rule has_derivative_sum) (use has_derivative_M12_term in blast)

lemma has_derivative_M22_moment_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M22_moment y c) has_derivative (\<lambda>h. d_M22_moment_x x c h))
         (at x within V)"
  unfolding M22_moment_def d_M22_moment_x_def
  by (rule has_derivative_sum) (use has_derivative_M22_term in blast)


text \<open>\<^bold>\<open>Layer 5.\<close> Assemble the six per-moment derivatives into the
  vector-valued Fréchet derivative \<open>D\<^sub>x M_paper\<close>.

  Because each component of the vector is now a single constant
  application (\<^const>\<open>d_A_moment_x\<close>, ...), the elaborator does only
  six lookups when typechecking this definition --- no nested
  sum-of-products tree.
\<close>

definition DM_paper_x :: "(planar^'n) \<Rightarrow> planar \<Rightarrow> ((planar^'n) \<Rightarrow> complex^6)"
  where
  "DM_paper_x x c = (\<lambda>h. vector
    [ d_A_moment_x   x c h,
      d_M1_moment_x  x c h,
      d_M2_moment_x  x c h,
      d_M11_moment_x x c h,
      d_M12_moment_x x c h,
      d_M22_moment_x x c h ])"

text \<open>Componentwise unfolding lemma so \<open>DM_paper_x x c h $ k\<close> does not
  re-elaborate the full vector at every proof step.\<close>

lemma DM_paper_x_components [simp]:
  "DM_paper_x x c h $ 1 = d_A_moment_x   x c h"
  "DM_paper_x x c h $ 2 = d_M1_moment_x  x c h"
  "DM_paper_x x c h $ 3 = d_M2_moment_x  x c h"
  "DM_paper_x x c h $ 4 = d_M11_moment_x x c h"
  "DM_paper_x x c h $ 5 = d_M12_moment_x x c h"
  "DM_paper_x x c h $ 6 = d_M22_moment_x x c h"
  unfolding DM_paper_x_def by simp_all

lemma has_derivative_M_paper_x:
  fixes c :: planar and x :: "planar^'n"
  shows "((\<lambda>y. M_paper y c) has_derivative DM_paper_x x c) (at x within V)"
proof -
  have comps:
    "\<forall>k :: 6. ((\<lambda>y. M_paper y c $ k) has_derivative (\<lambda>h. DM_paper_x x c h $ k))
              (at x within V)"
  proof (intro allI)
    fix k :: 6
    consider "k = 1" | "k = 2" | "k = 3" | "k = 4" | "k = 5" | "k = 6"
      using exhaust_6 by metis
    thus "((\<lambda>y. M_paper y c $ k) has_derivative (\<lambda>h. DM_paper_x x c h $ k))
            (at x within V)"
    proof cases
      case 1 thus ?thesis
        using has_derivative_A_moment_x[where c=c and x=x and V=V] by simp
    next
      case 2 thus ?thesis
        using has_derivative_M1_moment_x[where c=c and x=x and V=V] by simp
    next
      case 3 thus ?thesis
        using has_derivative_M2_moment_x[where c=c and x=x and V=V] by simp
    next
      case 4 thus ?thesis
        using has_derivative_M11_moment_x[where c=c and x=x and V=V] by simp
    next
      case 5 thus ?thesis
        using has_derivative_M12_moment_x[where c=c and x=x and V=V] by simp
    next
      case 6 thus ?thesis
        using has_derivative_M22_moment_x[where c=c and x=x and V=V] by simp
    qed
  qed

  have vec_der:
    "((\<lambda>y. \<chi> k. M_paper y c $ k)
        has_derivative
        (\<lambda>h. \<chi> k. DM_paper_x x c h $ k))
     (at x within V)"
  proof (subst has_derivative_componentwise_within, intro ballI)
    fix b :: "complex^6" assume bB: "b \<in> Basis"
    from bB obtain k :: 6 and e :: complex
      where b_eq: "b = axis k e" and e_basis: "e \<in> Basis"
      unfolding Basis_vec_def by auto
    have indiv:
      "((\<lambda>y. M_paper y c $ k) has_derivative (\<lambda>h. DM_paper_x x c h $ k))
       (at x within V)"
      using comps by blast
    have inner_d:
      "((\<lambda>z :: complex. z \<bullet> e) has_derivative (\<lambda>z. z \<bullet> e))
         (at (M_paper x c $ k) within (\<lambda>y. M_paper y c $ k) ` V)"
      using bounded_linear_inner_left[of e]
      by (rule bounded_linear.has_derivative, simp)
    have d_compose:
      "((\<lambda>y. (M_paper y c $ k) \<bullet> e) has_derivative
          (\<lambda>h. (DM_paper_x x c h $ k) \<bullet> e))
       (at x within V)"
      using has_derivative_in_compose[OF indiv inner_d]
      by (simp add: o_def)
    show "((\<lambda>y. (\<chi> k. M_paper y c $ k) \<bullet> b) has_derivative
           (\<lambda>y. (\<chi> k. DM_paper_x x c y $ k) \<bullet> b))
          (at x within V)"
      using d_compose by (simp add: b_eq inner_axis)
  qed

  show ?thesis
  proof -
    have lhs:
      "(\<lambda>y. \<chi> k. M_paper y c $ k) = (\<lambda>y. M_paper y c)"
      by (simp add: fun_eq_iff vec_eq_iff)
    have rhs:
      "(\<lambda>h. \<chi> k. DM_paper_x x c h $ k) = DM_paper_x x c"
      by (simp add: fun_eq_iff vec_eq_iff)
    show ?thesis
      using vec_der
      by (simp only: lhs rhs)
  qed
qed

end
