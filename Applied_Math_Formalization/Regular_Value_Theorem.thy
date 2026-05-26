theory Regular_Value_Theorem
  imports "HOL-Analysis.Derivative"
begin

text \<open>
  Self-contained development of the (finite-dimensional, Euclidean) regular-value
  theorem, built on top of @{theory "HOL-Analysis.Derivative"} only. The aim is a
  reusable, AFP-submittable module: a smooth map \<open>G\<close> with \<open>0\<close> a regular value has,
  near each zero, a smooth chart of its zero set \<open>G\<^sup>-\<^sup>1(0)\<close>.

  The construction augments \<open>G\<close> to a square map \<open>F z = (\<pi> z, G z)\<close> whose derivative
  at the base point is a bijection, applies the (inverse-function-theorem based)
  local diffeomorphism, and reads off the chart. This file currently records the
  statements; proofs are being filled in.
\<close>

section \<open>Rank--nullity for Euclidean linear maps\<close>

text \<open>
  For a surjective linear map between Euclidean spaces the kernel has dimension
  \<open>DIM('a) - DIM('b)\<close>. (HOL-Analysis has the abstract rank-nullity result only in
  the algebraic hierarchy, not in this Euclidean form, so we record it here.)
\<close>

lemma dim_kernel_surj:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" and "surj f"
  shows "dim {x. f x = 0} = DIM('a) - DIM('b)"
proof -
  interpret f: linear f
    using assms(1) .

  let ?K = "{x. f x = 0}"
  have subK: "subspace ?K"
    using Real_Vector_Spaces.real_vector.linear_subspace_kernel assms(1) by blast
  have spanK[simp]: "span ?K = ?K"
    using subK by (simp add: span_eq)

  let ?H = "{y. \<forall>x\<in>?K. orthogonal x y}"
  have subH: "subspace ?H"
    by (rule subspace_orthogonal_to_vectors)

  have decomp: "\<And>x. \<exists>u v. u \<in> ?K \<and> v \<in> ?H \<and> x = u + v"
  proof -
    fix x
    obtain u v where uv:
      "x = u + v" "u \<in> span ?K" "\<And>w. w \<in> span ?K \<Longrightarrow> orthogonal v w"
      using orthogonal_subspace_decomp_exists[of ?K x] subK by blast
    have "u \<in> ?K"
      using uv(2) by simp
    moreover have "v \<in> ?H"
      using uv(3) by (auto simp: orthogonal_commute)
    ultimately show "\<exists>u v. u \<in> ?K \<and> v \<in> ?H \<and> x = u + v"
      using uv(1) by blast
  qed

  have H_surj: "f ` ?H = UNIV"
  proof (rule set_eqI)
    fix y :: 'b
    show "y \<in> f ` ?H \<longleftrightarrow> y \<in> UNIV"
    proof
      assume "y \<in> f ` ?H"
      then show "y \<in> UNIV" by simp
    next
      assume "y \<in> UNIV"
      obtain x where fx: "f x = y"
        using assms(2) unfolding surj_def by metis
      from decomp[of x] obtain u v where uv: "u \<in> ?K" "v \<in> ?H" "x = u + v"
        by blast
      have "f u = 0"
        using uv(1) by simp
      then have "f v = y"
        using fx uv(3) by (simp add: f.add)
      then show "y \<in> f ` ?H"
        using uv(2) by blast
    qed
  qed

  have H_inj: "inj_on f ?H"
  proof (rule inj_onI)
    fix x y
    assume x: "x \<in> ?H" and y: "y \<in> ?H" and eq: "f x = f y"
    have "f (x - y) = 0"
      using eq by (simp add: f.diff)
    then have xyK: "x - y \<in> ?K"
      by simp
    have "x - y \<in> ?H"
      using x y by (auto simp: orthogonal_def inner_diff_right)
    then have ortho: "\<forall>w\<in>?K. orthogonal w (x - y)"
      by simp
    have "orthogonal (x - y) (x - y)"
      using ortho xyK by (simp add: orthogonal_commute)
    then have "x - y = 0"
      by (simp add: orthogonal_self)
    then show "x = y"
      by simp
  qed

  have dimH: "dim ?H = DIM('b)"
  proof -
    have spanH: "span ?H = ?H"
      using subH by (simp add: span_eq)
    have inj_spanH: "inj_on f (span ?H)"
      using H_inj by (simp only: spanH)
    have "dim (f ` ?H) = dim ?H"
      using Euclidean_Space.eucl.dim_image_eq[OF assms(1) inj_spanH] .
    moreover have "dim (f ` ?H) = DIM('b)"
      using H_surj by simp
    ultimately show ?thesis
      by simp
  qed

  have dim_sum: "dim ?H + dim ?K = DIM('a)"
  proof -
    have "dim {y \<in> UNIV. \<forall>x\<in>?K. orthogonal x y} + dim ?K = dim (UNIV::'a set)"
      using dim_subspace_orthogonal_to_vectors[OF subK subspace_UNIV]
      by simp
    then show ?thesis
      by (simp add: dim_eq_full)
  qed

  from dim_sum dimH show ?thesis
    by linarith
qed

section \<open>Augmenting a surjection to a bijection\<close>

text \<open>
  Sub-lemma 1. A surjective linear map \<open>L : 'a \<rightarrow> 'b\<close> can be completed to a linear
  bijection \<open>z \<mapsto> (\<pi> z, L z)\<close> of \<open>'a\<close> onto \<open>'c \<times> 'b\<close>, for any complement type \<open>'c\<close>
  with \<open>DIM('c) + DIM('b) = DIM('a)\<close>: pick \<open>\<pi>\<close> linear and an isomorphism on \<open>ker L\<close>
  (which has dimension \<open>DIM('c)\<close>) onto \<open>'c\<close>; then \<open>(\<pi>, L)\<close> is injective, hence
  bijective.
\<close>

text \<open>
  For the regular-value chart we always work on a product domain \<open>'c \<times> 'b\<close>, with
  a map \<open>L : ('c\<times>'b) \<rightarrow> 'b\<close>.  Then the square augmentation
  \<open>z \<mapsto> (\<pi> z, L z)\<close> is an *endomorphism* of \<open>'c\<times>'b\<close>, so injective implies
  surjective by finite-dimensionality without any extra dimension arithmetic.
\<close>

lemma linear_surj_augment_to_bij:
  fixes L :: "('c::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b"
  assumes "linear L" and "surj L"
  shows "\<exists>\<pi>::('c\<times>'b) \<Rightarrow> 'c. linear \<pi> \<and> bij (\<lambda>z. (\<pi> z, L z))"
proof -
  let ?K = "{z. L z = 0}"
  have subK: "subspace ?K"
    using Real_Vector_Spaces.real_vector.linear_subspace_kernel assms(1) by blast

  have dimK: "dim ?K = DIM('c)"
    using dim_kernel_surj[OF assms]
    by (simp only: DIM_prod)

  have pair_ax:
      "finite_dimensional_vector_space_pair (*\<^sub>R) (Basis::('c\<times>'b) set) (*\<^sub>R) (Basis::'c set)"
    using Euclidean_Space.eucl.finite_dimensional_vector_space_pair_axioms .

  obtain \<pi> :: "('c\<times>'b) \<Rightarrow> 'c"
    where linpi: "linear \<pi>"
      and imgpi: "\<pi> ` ?K = UNIV"
      and injpi: "inj_on \<pi> ?K"
  proof -
    have "dim ?K = dim (UNIV::'c set)"
      using dimK by (simp add: dim_eq_full)
    then have "\<exists>\<pi>. Vector_Spaces.linear (*\<^sub>R) (*\<^sub>R) \<pi> \<and> \<pi> ` ?K = (UNIV::'c set) \<and> inj_on \<pi> ?K"
      using Vector_Spaces.finite_dimensional_vector_space_pair.subspace_isomorphism
      using pair_ax subK subspace_UNIV
      by (metis dim_raw_def subspace_raw_def)

    then obtain \<pi> :: "('c\<times>'b) \<Rightarrow> 'c"
      where lin\<pi>_raw: "Vector_Spaces.linear (*\<^sub>R) (*\<^sub>R) \<pi>"
        and img\<pi>: "\<pi> ` ?K = (UNIV::'c set)"
        and inj\<pi>: "inj_on \<pi> ?K"
      by blast

    have lin\<pi>: "linear \<pi>"
    proof (rule linearI)
      fix x y :: "'c \<times> 'b"
      show "\<pi> (x + y) = \<pi> x + \<pi> y"
        using lin\<pi>_raw
        by (simp add: Real_Vector_Spaces.linear.intro linear_add)
    next
      fix r :: real
      fix x :: "'c \<times> 'b"
      show "\<pi> (r *\<^sub>R x) = r *\<^sub>R \<pi> x"
        using lin\<pi>_raw
        by (simp add: Real_Vector_Spaces.linear.intro linear_cmul)
    qed

    show ?thesis
      using that[of \<pi>] lin\<pi> img\<pi> inj\<pi>
      by blast
  qed

  define F where "F = (\<lambda>z. (\<pi> z, L z))"

  have linF: "linear F"
  proof (rule linearI)
    fix x y :: "'c \<times> 'b"
    show "F (x + y) = F x + F y"
    proof -
      have "F (x + y) = (\<pi> (x + y), L (x + y))"
        by (simp add: F_def)
      also have "\<dots> = (\<pi> x + \<pi> y, L x + L y)"
        using linpi assms(1)
        by (simp add: linear_add)
      also have "\<dots> = (\<pi> x, L x) + (\<pi> y, L y)"
        by simp
      also have "\<dots> = F x + F y"
        by (simp add: F_def)
      finally show ?thesis.
    qed
  next
    fix r :: real
    fix x :: "'c \<times> 'b"
    show "F (r *\<^sub>R x) = r *\<^sub>R F x"
    proof -
      have "F (r *\<^sub>R x) = (\<pi> (r *\<^sub>R x), L (r *\<^sub>R x))"
        by (simp add: F_def)
      also have "\<dots> = (r *\<^sub>R \<pi> x, r *\<^sub>R L x)"
        using linpi assms(1)
        by (simp add: linear_cmul)
      also have "\<dots> = r *\<^sub>R (\<pi> x, L x)"
        by simp
      also have "\<dots> = r *\<^sub>R F x"
        by (simp add: F_def)
      finally show ?thesis.
    qed
  qed

  have injF: "inj F"
  proof (rule injI)
    fix x y
    assume eq: "F x = F y"
    have pi_eq: "\<pi> x = \<pi> y" and L_eq: "L x = L y"
      using eq unfolding F_def by auto
    let ?d = "x - y"
    have Ld0: "L ?d = 0"
      by (simp add: L_eq assms(1) linear_diff)
    have pid0: "\<pi> ?d = 0"
      by (simp add: linear_diff linpi pi_eq)
    have d_in_K: "?d \<in> ?K"
      using Ld0 by simp
    have "?d = 0"
      using injpi d_in_K pid0
      using linear_injective_on_subspace_0 linpi subK by blast
    then show "x = y"
      by simp
  qed

  have surjF: "surj F"
    using Euclidean_Space.eucl.linear_inj_imp_surj[OF linF injF] .

  have bijF: "bij F"
    using injF surjF by (simp add: bij_def)

  show ?thesis
    using linpi bijF unfolding F_def by blast
qed

section \<open>The regular-value local chart\<close>

text \<open>
  Keystone. If \<open>G : 'c \<times> 'b \<rightarrow> 'b\<close> is continuously differentiable on an open
  set \<open>W\<close> and \<open>p \<in> W\<close> is a regular zero (the derivative \<open>G' p\<close> is surjective),
  then the zero set \<open>M = {q \<in> W. G q = 0}\<close> is, near \<open>p\<close>, the smooth image of an
  open subset \<open>U \<subseteq> 'c\<close> under a chart \<open>\<phi>\<close> that is a homeomorphism onto an
  open-in-\<open>M\<close> neighbourhood of \<open>p\<close>.

  Construction (sub-lemma 1 + inverse function theorem): augment \<open>G\<close> to the square
  map \<open>F z = (\<pi> z, G z)\<close> with \<open>\<pi>\<close> from @{thm linear_surj_augment_to_bij} applied to
  \<open>L = G' p\<close>, so \<open>F' p\<close> is a bijection; the inverse function theorem gives a local
  diffeomorphism \<open>F : U' \<rightarrow> V'\<close> with inverse \<open>g\<close>, and the chart is
  \<open>\<phi> u = g (u, 0)\<close> on \<open>U = {u. (u,0) \<in> V'}\<close>.
\<close>

theorem regular_value_local_chart:
  fixes G :: "('c::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b"
    and G' :: "('c \<times> 'b) \<Rightarrow> (('c \<times> 'b) \<Rightarrow>\<^sub>L 'b)"
    and W :: "('c \<times> 'b) set"
    and p :: "'c \<times> 'b"
  assumes Wopen: "open W" and pW: "p \<in> W" and Gp0: "G p = 0"
    and derG: "\<And>z. z \<in> W \<Longrightarrow> (G has_derivative blinfun_apply (G' z)) (at z)"
    and contG': "continuous_on W G'"
    and regp: "surj (blinfun_apply (G' p))"
  shows "\<exists>(U::'c set) (u0::'c) (\<phi>::'c \<Rightarrow> ('c \<times> 'b)) (g::('c \<times> 'b) \<Rightarrow> 'c).
            open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and>
            \<phi> differentiable_on U \<and>
            \<phi> ` U \<subseteq> {q \<in> W. G q = 0} \<and>
            openin (top_of_set {q \<in> W. G q = 0}) (\<phi> ` U) \<and>
            homeomorphism U (\<phi> ` U) \<phi> g"
proof -
  text \<open>The derivative at \<open>p\<close>, as a (surjective) linear map.\<close>
  define L where "L = blinfun_apply (G' p)"
  have blL: "bounded_linear L"
    unfolding L_def by (rule blinfun.bounded_linear_right)
  have linL: "linear L"
    using blL by (simp add: bounded_linear.linear)
  have surjL: "surj L"
    using regp unfolding L_def .

  text \<open>Sub-lemma 1: complete \<open>L\<close> to a bijection \<open>z \<mapsto> (\<pi> z, L z)\<close>.\<close>
  obtain \<pi> :: "('c \<times> 'b) \<Rightarrow> 'c"
    where lin\<pi>: "linear \<pi>" and bijB: "bij (\<lambda>z. (\<pi> z, L z))"
    using linear_surj_augment_to_bij[OF linL surjL] by blast
  have bl\<pi>: "bounded_linear \<pi>"
    using lin\<pi> by (simp add: linear_conv_bounded_linear)

  text \<open>The augmented square map \<open>F\<close> and its (blinfun) derivative \<open>Fd\<close>.\<close>
  define F where "F = (\<lambda>z::'c\<times>'b. (\<pi> z, G z))"
  define Fd where "Fd = (\<lambda>z. Blinfun (\<lambda>v. (\<pi> v, blinfun_apply (G' z) v)))"
  have bl_pair: "bounded_linear (\<lambda>v. (\<pi> v, blinfun_apply (G' z) v))" for z
    by (intro bounded_linear_Pair bl\<pi> blinfun.bounded_linear_right)
  have Fd_eq: "blinfun_apply (Fd z) = (\<lambda>v. (\<pi> v, blinfun_apply (G' z) v))" for z
    unfolding Fd_def by (rule bounded_linear_Blinfun_apply[OF bl_pair])

  have derF: "(F has_derivative blinfun_apply (Fd z)) (at z)" if z: "z \<in> W" for z
  proof -
    have d\<pi>: "(\<pi> has_derivative \<pi>) (at z)"
      using bl\<pi> by (rule bounded_linear_imp_has_derivative)
    have dG: "(G has_derivative blinfun_apply (G' z)) (at z)"
      using z by (rule derG)
    have "((\<lambda>w. (\<pi> w, G w)) has_derivative (\<lambda>h. (\<pi> h, blinfun_apply (G' z) h))) (at z)"
      by (rule has_derivative_Pair[OF d\<pi> dG])
    then show ?thesis
      by (simp add: F_def Fd_eq)
  qed

  have bij_Fdp: "bij (blinfun_apply (Fd p))"
    using bijB by (simp add: Fd_eq L_def)

  show ?thesis
    sorry
qed

end
