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
  sorry

section \<open>Augmenting a surjection to a bijection\<close>

text \<open>
  Sub-lemma 1. A surjective linear map \<open>L : 'a \<rightarrow> 'b\<close> can be completed to a linear
  bijection \<open>z \<mapsto> (\<pi> z, L z)\<close> of \<open>'a\<close> onto \<open>'c \<times> 'b\<close>, for any complement type \<open>'c\<close>
  with \<open>DIM('c) + DIM('b) = DIM('a)\<close>: pick \<open>\<pi>\<close> linear and an isomorphism on \<open>ker L\<close>
  (which has dimension \<open>DIM('c)\<close>) onto \<open>'c\<close>; then \<open>(\<pi>, L)\<close> is injective, hence
  bijective.
\<close>

lemma linear_surj_augment_to_bij:
  fixes L :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear L" and "surj L"
    and dimc: "DIM('c::euclidean_space) + DIM('b) = DIM('a)"
  shows "\<exists>\<pi>::'a \<Rightarrow> 'c. linear \<pi> \<and> bij (\<lambda>z. (\<pi> z, L z))"
  sorry

end
