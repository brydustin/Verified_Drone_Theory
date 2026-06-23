theory Scratch_mstargc1
  imports Scratch_momentsard
begin

text \<open>\<^bold>\<open>Phase A: the joint C1 field of mstarg\<close> (toward has_derivative_mstarg_joint_C1).

  mstarg c x = det (Gram (transC o DM_paper_x x c)).  Its x-dependence flows through the
  moment Jacobian components d_*_moment_x (DM_paper_x_components), so the x-partial assembles
  from the moment x-derivative bricks in Scratch_momentsard (imported here) through transC
  (bounded-linear), the Gram entries (sum-of-products), and det.  The omega-partial flows
  through cvec_dip (smooth).  We develop on the fast Robust2 heap with this local mstarg def
  (identical to the d3eng stub / the real Robust3 def), mirroring gradU_dip_joint_C1; the
  finished lemma grafts to Robust3 at the splice.\<close>

definition mstarg :: "planar \<Rightarrow> (planar^'n) \<Rightarrow> real" where
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

text \<open>Gram foundation, ported verbatim from Scratch_gram (self-contained: only \<open>transC\<close>
  + HOL-Analysis).  \<open>matrix_gram_entry\<close> exposes each Gram entry as a sum of products of the
  moment components \<open>transC (DM_paper_x x c e)\<close> --- the form whose x-derivative my moment
  bricks supply directly.\<close>

lemma linear_DM_paper_x: "linear (DM_paper_x x c)"
  by (metis has_derivative_M_paper_x has_derivative_bounded_linear bounded_linear.linear)

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
  also have "\<dots> = (\<Sum>e\<in>Basis. vec_nth (B e) j * vec_nth (B e) i)" by (simp only: key)
  finally show ?thesis by (simp only: B_def o_def)
qed

text \<open>Scaffolding sanity: the moment x-derivative bricks are visible through the import.\<close>

lemma scaffold_brick_visible:
  fixes c :: planar and x h :: "planar^'n" and V :: "(planar^'n) set"
  shows "(\<lambda>y::planar^'n. d_M1_moment_x y c h) differentiable (at x within V)"
  by (rule differentiable_d_M1_moment_x)

text \<open>\<^bold>\<open>A1: DM_paper_x differentiable in x.\<close>  First a reusable componentwise lemma:
  a vec-valued map is differentiable when each component is (mirrors the
  \<open>has_derivative_componentwise_within\<close> step of \<open>has_derivative_M_paper_x\<close>).\<close>

lemma differentiable_vec_componentwise:
  fixes f :: "'a::real_normed_vector \<Rightarrow> (('b::euclidean_space)^'c::finite)"
  assumes "\<And>k. (\<lambda>y. f y $ k) differentiable (at x within V)"
  shows "(\<lambda>y. f y) differentiable (at x within V)"
proof -
  from assms obtain D where D: "\<And>k. ((\<lambda>y. f y $ k) has_derivative D k) (at x within V)"
    unfolding differentiable_def by metis
  have "((\<lambda>y. f y) has_derivative (\<lambda>h. \<chi> j. D j h)) (at x within V)"
  proof (subst has_derivative_componentwise_within, intro ballI)
    fix b :: "('b)^'c" assume bB: "b \<in> Basis"
    then obtain k u where b: "b = axis k u" and u: "u \<in> Basis"
      unfolding Basis_vec_def by auto
    have inner_d: "((\<lambda>z::'b. z \<bullet> u) has_derivative (\<lambda>z. z \<bullet> u))
                     (at (f x $ k) within (\<lambda>y. f y $ k) ` V)"
      using bounded_linear_inner_left[of u] by (rule bounded_linear.has_derivative, simp)
    have "((\<lambda>y. (f y $ k) \<bullet> u) has_derivative (\<lambda>h. (D k h) \<bullet> u)) (at x within V)"
      using has_derivative_in_compose[OF D inner_d] by (simp only: o_def)
    thus "((\<lambda>y. f y \<bullet> b) has_derivative (\<lambda>h. (\<chi> j. D j h) \<bullet> b)) (at x within V)"
      by (simp add: b inner_axis)
  qed
  thus ?thesis by (rule differentiableI)
qed

lemma differentiable_DM_paper_x_vec:
  fixes c :: planar and x e :: "planar^'n" and V :: "(planar^'n) set"
  shows "(\<lambda>y::planar^'n. DM_paper_x y c e) differentiable (at x within V)"
proof (rule differentiable_vec_componentwise)
  fix k :: 6
  consider "k=1"|"k=2"|"k=3"|"k=4"|"k=5"|"k=6" using exhaust_6 by metis
  thus "(\<lambda>y. DM_paper_x y c e $ k) differentiable (at x within V)"
  proof cases
    case 1
    hence eq: "(\<lambda>y::planar^'n. DM_paper_x y c e $ k) = (\<lambda>y. d_A_moment_x y c e)"
      by (simp only: DM_paper_x_components DA_paper_x_def d_A_moment_x_def)
    show ?thesis unfolding eq by (rule differentiableI[OF has_derivative_d_A_moment_x])
  next
    case 2
    hence eq: "(\<lambda>y::planar^'n. DM_paper_x y c e $ k) = (\<lambda>y. d_M1_moment_x y c e)"
      by (simp only: DM_paper_x_components DM1_paper_x_def d_M1_moment_x_def)
    show ?thesis unfolding eq by (rule differentiable_d_M1_moment_x)
  next
    case 3
    hence eq: "(\<lambda>y::planar^'n. DM_paper_x y c e $ k) = (\<lambda>y. d_M2_moment_x y c e)"
      by (simp only: DM_paper_x_components DM2_paper_x_def d_M2_moment_x_def)
    show ?thesis unfolding eq by (rule differentiable_d_M2_moment_x)
  next
    case 4
    hence eq: "(\<lambda>y::planar^'n. DM_paper_x y c e $ k) = (\<lambda>y. d_M11_moment_x y c e)"
      by (simp only: DM_paper_x_components DM11_paper_x_def d_M11_moment_x_def)
    show ?thesis unfolding eq by (rule differentiable_d_M11_moment_x)
  next
    case 5
    hence eq: "(\<lambda>y::planar^'n. DM_paper_x y c e $ k) = (\<lambda>y. d_M12_moment_x y c e)"
      by (simp only: DM_paper_x_components DM12_paper_x_def d_M12_moment_x_def)
    show ?thesis unfolding eq by (rule differentiable_d_M12_moment_x)
  next
    case 6
    hence eq: "(\<lambda>y::planar^'n. DM_paper_x y c e $ k) = (\<lambda>y. d_M22_moment_x y c e)"
      by (simp only: DM_paper_x_components DM22_paper_x_def d_M22_moment_x_def)
    show ?thesis unfolding eq by (rule differentiable_d_M22_moment_x)
  qed
qed

text \<open>\<^bold>\<open>A2-A4: mstarg differentiable in x (the FX side of the joint field).\<close>  Mirror the
  cont_transC_DM_entry / cont_matrix_G_entry / cont_mstarg chain of Scratch_gram, with
  \<open>differentiable\<close> in place of \<open>continuous_on\<close>, fed by A1.\<close>

lemma differentiable_transC_DM_entry:
  fixes c :: planar and x e :: "planar^'n" and V :: "(planar^'n) set"
  shows "(\<lambda>y::planar^'n. vec_nth (transC (DM_paper_x y c e)) k) differentiable (at x within V)"
proof -
  have "(\<lambda>y. transC (DM_paper_x y c e)) differentiable (at x within V)"
    using differentiable_DM_paper_x_vec
          bounded_linear_imp_differentiable bounded_linear_transC differentiable_compose by blast
  thus ?thesis
    using bounded_linear_vec_nth bounded_linear_imp_differentiable differentiable_compose by blast
qed

lemma differentiable_matrix_G_entry:
  fixes c :: planar and x :: "planar^'n" and V :: "(planar^'n) set"
  shows "(\<lambda>y::planar^'n. vec_nth (vec_nth
            (matrix ((transC \<circ> DM_paper_x y c) \<circ> adjoint (transC \<circ> DM_paper_x y c))) i) j)
         differentiable (at x within V)"
proof -
  have "(\<lambda>y::planar^'n. \<Sum>e\<in>Basis.
            vec_nth (transC (DM_paper_x y c e)) j * vec_nth (transC (DM_paper_x y c e)) i)
         differentiable (at x within V)"
    by (intro differentiable_sum differentiable_mult differentiable_transC_DM_entry, simp,
           simp add: differentiable_transC_DM_entry)
  thus ?thesis by (simp only: matrix_gram_entry)
qed

lemma differentiable_prod':
  fixes f :: "'i \<Rightarrow> ('a::real_normed_vector) \<Rightarrow> ('b::real_normed_field)"
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>y. f i y) differentiable (at x within V)"
  shows "(\<lambda>y. \<Prod>i\<in>I. f i y) differentiable (at x within V)"
  using assms
  by (induction I rule: finite_induct, auto intro!: differentiable_mult differentiable_const)

lemma differentiable_mstarg_x:
  fixes c :: planar and x :: "planar^'n" and V :: "(planar^'n) set"
  shows "(\<lambda>y::planar^'n. mstarg c y) differentiable (at x within V)"
  unfolding mstarg_def det_def
  by (intro differentiable_sum ballI differentiable_mult differentiable_const
            differentiable_prod' differentiable_matrix_G_entry, simp_all)

end
