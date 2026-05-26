theory Parametric_Transversality_Euclidean_Base
  imports
    "HOL-Analysis.Change_Of_Vars"
    Nonemptiness_Scaffold
begin

text \<open>
  Reusable Euclidean infrastructure for the paper's "parametric transversality"
  steps:

  * Regular value hypothesis for a joint map \<open>G : V\<times>\<Omega> \<to> \<real>^k\<close>.
  * Regular value theorem (implicit-function-theorem based): the preimage
    \<open>{(x,\<omega>). G(x,\<omega>) = 0}\<close> admits a countable smooth chart cover.
  * Sard on the projection from that regular level set to the parameter space.

  Isabelle/HOL (as shipped) provides Sard in the form of @{thm baby_Sard}. What is
  missing is a convenient packaged regular-value / submanifold development. We
  therefore record the pipeline here as a single theorem with one central
  \<open>sorry\<close>, and we will later refine it by proving the intermediate lemmas.
\<close>

subsection \<open>Regular Value Predicate\<close>

definition regular_value_on ::
  "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
where
  "regular_value_on f S y \<longleftrightarrow>
     (\<forall>x\<in>S. f x = y \<longrightarrow> (\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f'))"

lemma regular_value_onI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = y \<Longrightarrow> (\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f')"
  shows "regular_value_on f S y"
  using assms unfolding regular_value_on_def by blast


subsection \<open>Complex as \<open>real^2\<close> (for Sard)\<close>

definition cplx_r2 :: "complex \<Rightarrow> real^2"
where
  "cplx_r2 z = (vector [Re z, Im z] :: real^2)"

lemma vector2_add:
  "(vector [a + b, c + d] :: real^2) = vector [a, c] + vector [b, d]"
  by (simp add: vec_eq_iff forall_2 algebra_simps)

lemma vector2_scaleR:
  "(vector [r * a, r * c] :: real^2) = r *\<^sub>R vector [a, c]"
  by (simp add: vec_eq_iff forall_2)

lemma cplx_r2_eq_iff [simp]: "cplx_r2 z = cplx_r2 w \<longleftrightarrow> z = w"
proof
  assume h: "cplx_r2 z = cplx_r2 w"
  have "Re z = Re w"
  proof -
    have "(cplx_r2 z) $ 1 = (cplx_r2 w) $ 1"
      using h by simp
    then show ?thesis
      by (simp add: cplx_r2_def)
  qed
  moreover have "Im z = Im w"
  proof -
    have "(cplx_r2 z) $ 2 = (cplx_r2 w) $ 2"
      using h by simp
    then show ?thesis
      by (simp add: cplx_r2_def)
  qed
  ultimately show "z = w"
    by (simp add: complex_eq_iff)
next
  assume "z = w"
  then show "cplx_r2 z = cplx_r2 w" by simp
qed

lemma cplx_r2_0_iff [simp]: "cplx_r2 z = 0 \<longleftrightarrow> z = 0"
proof
  assume "cplx_r2 z = 0"
  then have hz: "vector [Re z, Im z] = (0::real^2)"
    by (simp add: cplx_r2_def)
  have "Re z = 0"
  proof -
    have "(vector [Re z, Im z] :: real^2) $ 1 = (0::real^2) $ 1"
      by (rule arg_cong[OF hz])
    then show ?thesis by simp
  qed
  moreover have "Im z = 0"
  proof -
    have "(vector [Re z, Im z] :: real^2) $ 2 = (0::real^2) $ 2"
      by (rule arg_cong[OF hz])
    then show ?thesis by simp
  qed
  ultimately show "z = 0"
    by (simp add: complex_eq_iff)
next
  assume "z = 0"
  then show "cplx_r2 z = 0"
    by (simp add: cplx_r2_def vec_eq_iff forall_2)
qed

lemma bounded_linear_cplx_r2: "bounded_linear cplx_r2"
proof (rule bounded_linear_intro[where K=2])
  fix x y
  show "cplx_r2 (x + y) = cplx_r2 x + cplx_r2 y"
    unfolding cplx_r2_def by (simp add: vector2_add)
  fix r x
  show "cplx_r2 (r *\<^sub>R x) = r *\<^sub>R cplx_r2 x"
    unfolding cplx_r2_def by (simp add: vector2_scaleR)
  fix z
  show "norm (cplx_r2 z) \<le>  cmod z * 2"
  proof -
    have "norm (cplx_r2 z) \<le> (\<Sum>i\<in>UNIV. \<bar>(cplx_r2 z) $ i\<bar>)"
      by (rule norm_le_l1_cart)
    also have "\<dots> = norm (Re z) + norm (Im z)"
      unfolding cplx_r2_def by (simp add: sum_2)
    also have "\<dots> \<le> norm z + norm z"
      by (intro add_mono) (simp_all add: abs_Re_le_cmod abs_Im_le_cmod)
    finally show ?thesis
      by linarith
  qed
qed

lemma has_derivative_cplx_r2 [derivative_intros]:
  fixes z :: complex
  shows "(cplx_r2 has_derivative cplx_r2) (at z)"
  by (rule bounded_linear.has_derivative[OF bounded_linear_cplx_r2], simp)

lemma surj_cplx_r2: "surj cplx_r2"
proof -
  have "\<And>v::real^2. cplx_r2 (Complex (v$1) (v$2)) = v"
    unfolding cplx_r2_def by (simp add: vec_eq_iff forall_2)
  then show ?thesis
    by (intro surjI[where f = "\<lambda>v::real^2. Complex (v$1) (v$2)"], simp) 
qed


subsection \<open>Second Countability / Lindelof Convenience\<close>

lemma second_countable_euclidean:
  "second_countable (euclidean :: 'a::second_countable_topology topology)"
proof -
  obtain B :: "'a set set" where B: "countable B" "topological_basis B"
    using ex_countable_basis by (metis Top1_Ch3.countable_def countableE)
  have openB: "\<And>V. V \<in> B \<Longrightarrow> openin (euclidean :: 'a topology) V"
    using B(2) by (simp add: topological_basis_open)
  have refine:
    "\<And>U x. openin (euclidean :: 'a topology) U \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>V\<in>B. x \<in> V \<and> V \<subseteq> U"
  proof -
    fix U x
    assume "openin (euclidean :: 'a topology) U" and "x \<in> U"
    then have "open U" by simp
    from topological_basisE[OF B(2) this \<open>x \<in> U\<close>]
    show "\<exists>V\<in>B. x \<in> V \<and> V \<subseteq> U"
      by metis
  qed
  show ?thesis
    unfolding second_countable_def
    using B(1) openB refine
    by (metis ex_countable_basis istopology_open topological_basis_def 
        topological_basis_iff topology_inverse')
qed

subsection \<open>Parametric Sard/Transversality (Euclidean Pipeline)\<close>

subsection \<open>Linear Algebra Lemmas for the Critical-Value Characterization\<close>

text \<open>
  The "critical point" mechanism used in parametric transversality can be reduced
  to a simple linear observation: if a linear map \<open>F : X\<times>Y \<to> Y\<close> is surjective,
  then its kernel has the expected dimension \<open>dim X\<close>. If furthermore the
  restriction \<open>F(0,\<cdot>) : Y \<to> Y\<close> is not surjective, then there exists a
  nonzero vector in the kernel with zero \<open>X\<close>-component, forcing the projection
  from the kernel to \<open>X\<close> to fail injectivity, hence to have rank defect.
\<close>

lemma rank_defect_of_not_inj:
  fixes f :: "real^'m::{finite,wellorder} \<Rightarrow> real^'m::{finite,wellorder}"
  assumes lin: "linear f" and n_inj: "\<not> inj f"
  shows "rank (matrix f) < CARD('m)"
proof -
  have "rank (matrix f) \<noteq> CARD('m)"
    using n_inj lin by (auto simp: full_rank_injective)
  moreover have "rank (matrix f) \<le> CARD('m)"
    by (rule order_trans[OF rank_bound]) simp
  ultimately show ?thesis
    by linarith
qed

text \<open>
  Kernel/projection gadget used in the parametric transversality argument:
  if the full derivative in joint variables is surjective but the slice derivative
  in the frequency variables is not, then the projection from the tangent space
  (kernel of the derivative) to the parameter coordinates fails injectivity.
\<close>

lemma exists_nonzero_in_kernel_with_fst0:
  fixes L :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
  assumes lin: "linear L"
    and not_surj_slice: "\<not> surj (\<lambda>w::real^2. L (0, w))"
  shows "\<exists>w::real^2. w \<noteq> 0 \<and> L (0, w) = 0"
proof -
  interpret Llin: linear L by (rule lin)
  have lin_slice: "linear (\<lambda>w::real^2. L (0, w))"
  proof (rule linearI)
    fix x y :: "real^2"
    show "L (0, x + y) = L (0, x) + L (0, y)"
    proof -
      have "L (0, x + y) = L ((0, x) + (0, y))"
        by simp
      also have "\<dots> = L (0, x) + L (0, y)"
        by (rule Llin.add)
      finally show ?thesis .
    qed
    fix r :: real and x :: "real^2"
    show "L (0, r *\<^sub>R x) = r *\<^sub>R L (0, x)"
    proof -
      have "L (0, r *\<^sub>R x) = L (r *\<^sub>R (0, x))"
        by simp
      also have "\<dots> = r *\<^sub>R L (0, x)"
        by (rule Llin.scale)
      finally show ?thesis.
    qed
  qed
  have "\<not> inj (\<lambda>w::real^2. L (0, w))"
  proof
    assume "inj (\<lambda>w::real^2. L (0, w))"
    then have "surj (\<lambda>w::real^2. L (0, w))"
      using lin_slice
      by (simp add: linear_injective_imp_surjective)
    with not_surj_slice show False by blast
  qed
  then have "\<exists>w::real^2. w \<noteq> 0 \<and> (\<lambda>w::real^2. L (0, w)) w = 0"
    using lin_slice
    unfolding linear_injective_0[OF lin_slice]
    by blast
  then show ?thesis by blast
qed

lemma kernel_projection_not_inj_if_slice_not_surj:
  fixes L :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
  assumes lin: "linear L"
    and surj_full: "surj L"
    and not_surj_slice: "\<not> surj (\<lambda>w::real^2. L (0, w))"
  shows "\<exists>u v. v \<noteq> (0::real^2) \<and> L (u, v) = 0"
proof -
  obtain v0 :: "real^2" where v0nz: "v0 \<noteq> 0" and Lv0: "L (0, v0) = 0"
    using exists_nonzero_in_kernel_with_fst0[OF lin not_surj_slice] by blast
  obtain u0 :: "real^'m::{finite,wellorder}" where Lu0: "L (u0, 0) = - L (0, v0)"
    using surj_full unfolding surj_def
    by (metis Lv0 add.inverse_neutral lin linear_0 zero_prod_def)
  have "L (u0, v0) = 0"
  proof -
    interpret Llin: linear L by (rule lin)
    have "L (u0, v0) = L ((u0, 0) + (0, v0))"
      by simp
    also have "\<dots> = L (u0, 0) + L (0, v0)"
      by (rule Llin.add)
    also have "\<dots> = 0"
      using Lu0 by simp
    finally show ?thesis.
  qed
  then show ?thesis
    using v0nz by blast
qed

text \<open>
  The key dimension observation for our application (array factor):
  @{term G} has codomain dimension @{term "CARD('k) = 2"} and the joint domain is
  @{term "V \<times> \<Omega>"} with dimensions @{term "CARD('m)"} and @{term "CARD('n) = 2"}.
  A regular zero set of a map term "V\<times>\<Omega> \<to> \<real>^'k" has expected dimension
  @{term "CARD('m) + CARD('n) - CARD('k) = CARD('m)"}. Therefore the projection to
  @{term V} is between equal-dimensional Euclidean spaces, and the "baby Sard"
  theorem in Isabelle is applicable to the critical values of that projection.

  We do not yet have a packaged regular value / chart theorem in the library, so we
  separate concerns:
  1. A reusable lemma that turns a *given* countable chart cover + rank-defect
     hypothesis into negligibility of critical values (proved using @{thm baby_Sard}).
  2. A single remaining stub that provides those charts from the regular-value
     hypothesis.
\<close>


thm baby_Sard

lemma negligible_critical_values_from_charts:
  fixes charts ::
    "nat \<Rightarrow> (real ^ 'm::{finite,wellorder}) \<Rightarrow> ((real ^ 'm::{finite,wellorder}) \<times> (real ^ 'n::{finite,wellorder}))"
    and Crit :: "nat \<Rightarrow> (real ^ 'm::{finite,wellorder}) set"
    and D :: "nat \<Rightarrow> (real ^ 'm::{finite,wellorder}) \<Rightarrow> ((real ^ 'm::{finite,wellorder}) \<Rightarrow>\<^sub>L (real ^ 'm::{finite,wellorder}))"
  defines "proj \<equiv> fst"
  assumes der:
    "\<And>i x. x \<in> Crit i \<Longrightarrow>
      ((proj \<circ> charts i) has_derivative blinfun_apply (D i x))
        (at x within Crit i)"
    and rank_defect:
      "\<And>i x. x \<in> Crit i \<Longrightarrow>
        rank (matrix (blinfun_apply (D i x))) < CARD('m)"
  shows "negligible (\<Union>i. (proj \<circ> charts i) ` (Crit i))"
proof -
  have "negligible ((proj \<circ> charts i) ` (Crit i))" for i
  proof -
    have "negligible ((proj \<circ> charts i) ` (Crit i))"
    proof (rule baby_Sard[where f = "proj \<circ> charts i" and S = "Crit i" and f' = "\<lambda>x. blinfun_apply (D i x)"])
      show "CARD('m) \<le> CARD('m)"
        by simp
      show "\<And>x. x \<in> Crit i \<Longrightarrow>
          ((proj \<circ> charts i) has_derivative blinfun_apply (D i x)) (at x within Crit i)"
        using der by simp
      show "\<And>x. x \<in> Crit i \<Longrightarrow> rank (matrix (blinfun_apply (D i x))) < CARD('m)"
        using rank_defect by simp
    qed
    then show ?thesis .
  qed
  then show ?thesis
    by (simp add: image_Union negligible_Union_nat)
qed

text \<open>
  Missing geometric/analytic bridge: obtain a countable chart cover of the regular
  level set and identify bad parameters as critical values of the projection.

  Once this is available, the negligibility conclusion is immediate from
  {thm negligible_critical_values_from_charts}.
\<close>

(* bad parameters are contained in critical values of the projection *)
           (* the critical-value set is negligible by baby_Sard on each chart *)

lemma regular_zero_set_projection_charts_stub:
  fixes V :: "(real^'m::{finite,wellorder}) set"
    and \<Omega> :: "(real^'n::{finite,wellorder}) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^'n::{finite,wellorder})) \<Rightarrow> (real^'k::{finite,wellorder})"
  assumes "open V" "V \<noteq> {}" "open \<Omega>"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "\<exists>(charts :: nat \<Rightarrow> (real^'m::{finite,wellorder})
                       \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^'n::{finite,wellorder})))
            (Crit :: nat \<Rightarrow> (real^'m::{finite,wellorder}) set)
            (D :: nat \<Rightarrow> (real^'m::{finite,wellorder})
                       \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder}))).

           {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
               (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
             \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
           (\<forall>i x. x \<in> Crit i \<longrightarrow>
              ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
           (\<forall>i x. x \<in> Crit i \<longrightarrow>
              rank (matrix (blinfun_apply (D i x))) < CARD('m)) \<and>
           (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  sorry

text \<open>
  Specialized form of the missing chart lemma for the concrete situation used in
  the nonemptiness project: parameters live in \<open>real^'m\<close>, the frequency variable
  lives in \<open>real^2\<close>, and the constraint is two real equations (codomain \<open>real^2\<close>).

  This avoids a lot of type-class bookkeeping and matches the eventual
  instantiation from complex-valued maps via @{const cplx_r2}.
\<close>

text \<open>
  Work breakdown: we keep the main lemma as an assembly wrapper and factor the
  missing geometry into three intermediate lemmas.  These are the next proof
  targets (in this order).
\<close>

lemma regular_zero_set_projection_charts_core_2d:
  fixes V :: "(real^'m::{finite,wellorder}) set"
    and \<Omega> :: "(real^2) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
  assumes "open V" "V \<noteq> {}" "open \<Omega>"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "\<exists>(charts :: nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec))))
            (Crit0 :: nat \<Rightarrow> (real^'m::{finite,wellorder}) set)
            (D0 :: nat \<Rightarrow> (real^'m::{finite,wellorder})
                       \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder}))).
           {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
               (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
             \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit0 i)) \<and>
           (\<forall>i x. x \<in> Crit0 i \<longrightarrow>
              ((fst \<circ> charts i) has_derivative (blinfun_apply (D0 i x))) (at x within Crit0 i)) \<and>
           (\<forall>i x. x \<in> Crit0 i \<longrightarrow>
              rank (matrix (blinfun_apply (D0 i x))) < CARD('m))"
  sorry

text \<open>
  Local (single-point) version of the regular-value-to-chart step.
  This is the first real proof target: it should be discharged using
  @{thm inverse_function_theorem_scaled} plus a coordinate split argument.
\<close>

lemma regular_zero_set_projection_local_chart_2d:
  fixes V :: "(real^'m::{finite,wellorder}) set"
    and \<Omega> :: "(real^2) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
    and p :: "(real^'m::{finite,wellorder}) \<times> (real^2)"
  defines "M \<equiv> {q \<in> V\<times>\<Omega>. G q = 0}"
  assumes "open V" "open \<Omega>"
    and pM: "p \<in> M"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "\<exists>(U::(real^'m::{finite,wellorder}) set) (u0::real^'m::{finite,wellorder})
            (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))
            (g::((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> real^'m::{finite,wellorder}).
            open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and>
            \<phi> differentiable_on U \<and>
            \<phi> ` U \<subseteq> M \<and>
            openin (top_of_set M) (\<phi> ` U) \<and>
            homeomorphism U (\<phi> ` U) \<phi> g"
  sorry

text \<open>
  Countable chart cover of the regular level set, extracted from the local chart
  lemma via Lindelof.  This is the "topological" part of
  @{thm regular_zero_set_projection_charts_core_2d}; the remaining part is to
  identify the critical points/values and record Jacobians with rank defect.
\<close>



lemma countable_chart_cover_of_levelset_2d:
  fixes V :: "(real^'m::{finite,wellorder}) set"
    and \<Omega> :: "(real^2) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
  defines "M \<equiv> {q \<in> V\<times>\<Omega>. G q = 0}"
  assumes "open V" "open \<Omega>"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "\<exists>(U :: nat \<Rightarrow> (real^'m::{finite,wellorder}) set)
            (charts :: nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))).
           (\<forall>i. open (U i) \<and> charts i differentiable_on (U i) \<and> charts i ` (U i) \<subseteq> M \<and>
                openin (top_of_set M) (charts i ` (U i))) \<and>
           M \<subseteq> (\<Union>i. charts i ` (U i))"
proof -
  have loc:
    "\<And>p. p \<in> M \<Longrightarrow> \<exists>(U::(real^'m::{finite,wellorder}) set) (u0::real^'m::{finite,wellorder})
            (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))
            (g::((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> real^'m::{finite,wellorder}).
      open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and> \<phi> differentiable_on U \<and> \<phi> ` U \<subseteq> M \<and>
      openin (top_of_set M) (\<phi> ` U) \<and> homeomorphism U (\<phi> ` U) \<phi> g"
  proof -
    fix p
    assume pM: "p \<in> M"
    have pM': "p \<in> {q \<in> V\<times>\<Omega>. G q = 0}"
      using pM by (simp add: M_def)
    show "\<exists>(U::(real^'m::{finite,wellorder}) set) (u0::real^'m::{finite,wellorder})
            (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^2)))
            (g::((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> real^'m::{finite,wellorder}).
      open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and> \<phi> differentiable_on U \<and> \<phi> ` U \<subseteq> M \<and>
      openin (top_of_set M) (\<phi> ` U) \<and> homeomorphism U (\<phi> ` U) \<phi> g"
      using M_def assms(2,3) pM reg0 regular_zero_set_projection_local_chart_2d[of V \<Omega> p G] by blast
  qed

  define \<F> where
    "\<F> \<equiv> {S. \<exists>p\<in>M.
        \<exists>(U :: (real, 'm) vec set)
          (u0 :: (real, 'm) vec)
          (\<phi> :: (real, 'm) vec \<Rightarrow> (real, 'm) vec \<times> (real,2) vec)
          (g :: (real, 'm) vec \<times> (real,2) vec \<Rightarrow> (real, 'm) vec).
          open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and>
          \<phi> differentiable_on U \<and>
          \<phi> ` U \<subseteq> M \<and>
          openin (top_of_set M) (\<phi> ` U) \<and>
          homeomorphism U (\<phi> ` U) \<phi> g \<and>
          S = \<phi> ` U}"
  have F_openin: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S"
    by (auto simp: \<F>_def)
  have coverF: "M \<subseteq> \<Union>\<F>"
  proof
    fix p assume "p \<in> M"
    from loc[OF this] obtain
      U :: "(real^'m::{finite,wellorder}) set"
      and u0 :: "real^'m::{finite,wellorder}"
      and \<phi> :: "real^'m::{finite,wellorder}
                 \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec))"
      and g :: "((real^'m::{finite,wellorder}) \<times> ((real,2) vec))
                \<Rightarrow> real^'m::{finite,wellorder}"
    where
      "open U" "u0 \<in> U" "\<phi> u0 = p" "\<phi> differentiable_on U" "\<phi> ` U \<subseteq> M"
      "openin (top_of_set M) (\<phi> ` U)" "homeomorphism U (\<phi> ` U) \<phi> g"
      by blast
    have openU: "open U"
      and u0U: "u0 \<in> U"
      and phiu0: "\<phi> u0 = p"
      and diff: "\<phi> differentiable_on U"
      and subM: "\<phi> ` U \<subseteq> M"
      and openinM: "openin (top_of_set M) (\<phi> ` U)"
      and homeo: "homeomorphism U (\<phi> ` U) \<phi> g"
      using \<open>open U\<close> \<open>u0 \<in> U\<close> \<open>\<phi> u0 = p\<close> \<open>\<phi> differentiable_on U\<close> \<open>\<phi> ` U \<subseteq> M\<close>
            \<open>openin (top_of_set M) (\<phi> ` U)\<close> \<open>homeomorphism U (\<phi> ` U) \<phi> g\<close>
      by auto
    have image_in_F: "\<phi> ` U \<in> \<F>"
      unfolding \<F>_def
      using \<open>p \<in> M\<close> openU u0U phiu0 diff subM openinM homeo
      by blast
     
    have "p \<in> \<phi> ` U"
      using u0U phiu0 by blast
    then show "p \<in> \<Union>\<F>"
      using image_in_F by blast
  qed

  obtain \<F>' where F'sub: "\<F>' \<subseteq> \<F>" and F'cnt: "countable \<F>'" and coverF': "M \<subseteq> \<Union>\<F>'"
  proof -
    have scM: "second_countable (top_of_set M)"
      using second_countable_subtopology[OF second_countable_euclidean, of M] by simp

    have lindM: "Lindelof_space (top_of_set M)"
      using second_countable_imp_Lindelof_space[OF scM] .

    have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<F> \<and> M \<subseteq> \<Union>\<V>"
    proof -
      have hopen: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S"
        using F_openin by blast

      have hcover: "topspace (top_of_set M) \<subseteq> \<Union>\<F>"
        using coverF by simp

      obtain \<V> where Vsub: "\<V> \<subseteq> \<F>"
        and Vcnt: "countable \<V>"
        and Vcover: "topspace (top_of_set M) \<subseteq> \<Union>\<V>"
      proof -
        have hUnionF: "\<Union>\<F> = topspace (top_of_set M)"
        proof
          show "\<Union>\<F> \<subseteq> topspace (top_of_set M)"
            by (meson Sup_le_iff hopen openin_subset)
          show "topspace (top_of_set M) \<subseteq> \<Union>\<F>"
            using hcover.
        qed

        have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<F> \<and> \<Union>\<V> = topspace (top_of_set M)"
          using lindM hopen hUnionF
          unfolding Lindelof_space_def
          by (meson Top1_Ch3.countable_def countableE)


        then obtain \<V> where Vcnt: "countable \<V>" and Vsub: "\<V> \<subseteq> \<F>"
          and VU: "\<Union>\<V> = topspace (top_of_set M)"
          by blast
        have Vcover: "topspace (top_of_set M) \<subseteq> \<Union>\<V>"
          using VU by simp
        show ?thesis
          using that Vsub Vcnt Vcover by blast
      qed

        have "M \<subseteq> \<Union>\<V>"
        using Vcover by simp

      then show ?thesis
        using Vcnt Vsub by blast
    qed

    then obtain \<V> where "\<V> \<subseteq> \<F>" "countable \<V>" "M \<subseteq> \<Union>\<V>"
      by blast

    then show ?thesis
      using that by blast
  qed

  show ?thesis
  proof (cases "M = {}")
    case True
    define U0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set" where
      "U0 \<equiv> (\<lambda>_. {})"
    define charts0 ::
      "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))"
      where "charts0 \<equiv> (\<lambda>_. (\<lambda>_. (0, 0)))"

    have "\<forall>i. open (U0 i) \<and>
              charts0 i differentiable_on (U0 i) \<and>
              charts0 i ` (U0 i) \<subseteq> M \<and>
              openin (top_of_set M) (charts0 i ` (U0 i))"
      using True by (auto simp: U0_def charts0_def)
    moreover have "M \<subseteq> (\<Union>i. charts0 i ` (U0 i))"
      using True by (auto simp: U0_def charts0_def)
    ultimately show ?thesis
      by (intro exI[of _ U0] exI[of _ charts0]) auto
  next
    case False

    have F'ne: "\<F>' \<noteq> {}"
    proof
      assume "\<F>' = {}"
      with coverF' have "M = {}"
        by simp
      with False show False
        by simp
    qed

    obtain e :: "nat \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)) set"
      where eimg: "\<Union>(range e) = \<Union>\<F>'" and erng: "\<And>n. e n \<in> \<F>'"
    proof -
      let ?e = "from_nat_into \<F>'"
      have eimg: "\<Union>(range ?e) = \<Union>\<F>'"
        by (metis F'cnt F'ne range_from_nat_into top1_countable_nonempty_eq_image_nat uncountable_def)
      have erng: "\<And>n. ?e n \<in> \<F>'"
        using F'ne by (simp add: from_nat_into)
      show ?thesis
        by (rule that[of ?e]) (auto simp: eimg intro: erng)
    qed

    (* Finally pick witnesses (U i, charts i) for each member of the countable cover. *)
    have "\<forall>S\<in>\<F>'. \<exists>(U::(real^'m::{finite,wellorder}) set)
                      (u0::real^'m::{finite,wellorder})
                      (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))
                      (g::((real^'m::{finite,wellorder}) \<times> ((real,2) vec)) \<Rightarrow> real^'m::{finite,wellorder})
                      (p::(real^'m::{finite,wellorder}) \<times> ((real,2) vec)).
            S = \<phi> ` U \<and> open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and>
            \<phi> differentiable_on U \<and> \<phi> ` U \<subseteq> M \<and>
            openin (top_of_set M) (\<phi> ` U) \<and> homeomorphism U (\<phi> ` U) \<phi> g"
    proof clarify
      fix S 
      assume "S \<in> \<F>'"
      with F'sub have "S \<in> \<F>" by blast
      then show "\<exists>(U::(real^'m::{finite,wellorder}) set)
                   (u0::real^'m::{finite,wellorder})
                   (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))
                   (g::((real^'m::{finite,wellorder}) \<times> ((real,2) vec)) \<Rightarrow> real^'m::{finite,wellorder})
                   (p::(real^'m::{finite,wellorder}) \<times> ((real,2) vec)).
            S = \<phi> ` U \<and>
            open U \<and>
            u0 \<in> U \<and>
            \<phi> u0 = p \<and>
            \<phi> differentiable_on U \<and>
            \<phi> ` U \<subseteq> M \<and>
            openin (top_of_set M) (\<phi> ` U) \<and>
            homeomorphism U (\<phi> ` U) \<phi> g"
      proof -
        from \<open>S \<in> \<F>\<close> obtain
          p :: "(real^'m::{finite,wellorder}) \<times> ((real,2) vec)"
          and U :: "(real^'m::{finite,wellorder}) set"
          and u0 :: "real^'m::{finite,wellorder}"
          and \<phi> :: "real^'m::{finite,wellorder}
                     \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec))"
          and g :: "((real^'m::{finite,wellorder}) \<times> ((real,2) vec))
                    \<Rightarrow> real^'m::{finite,wellorder}"
          where w: "open U" "u0 \<in> U" "\<phi> u0 = p" "\<phi> differentiable_on U"
            "\<phi> ` U \<subseteq> M" "openin (top_of_set M) (\<phi> ` U)"
            "homeomorphism U (\<phi> ` U) \<phi> g" "S = \<phi> ` U"
          unfolding \<F>_def by blast
        show ?thesis
          by (intro exI[of _ U] exI[of _ u0] exI[of _ \<phi>] exI[of _ g] exI[of _ p])
             (use w in blast)
      qed
    qed

    then have ex_pick:
      "\<forall>i. \<exists>(U::(real^'m::{finite,wellorder}) set)
              (u0::real^'m::{finite,wellorder})
              (\<phi>::real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))
              (g::((real^'m::{finite,wellorder}) \<times> ((real,2) vec)) \<Rightarrow> real^'m::{finite,wellorder})
              (p::(real^'m::{finite,wellorder}) \<times> ((real,2) vec)).
              e i = \<phi> ` U \<and> open U \<and> u0 \<in> U \<and> \<phi> u0 = p \<and>
              \<phi> differentiable_on U \<and> \<phi> ` U \<subseteq> M \<and>
              openin (top_of_set M) (\<phi> ` U) \<and> homeomorphism U (e i) \<phi> g"
      using erng by (metis (mono_tags, opaque_lifting))
    then obtain
      U0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set"
      and u00 :: "nat \<Rightarrow> real^'m::{finite,wellorder}"
      and \<phi>0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder}
                    \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))"
      and g0 :: "nat \<Rightarrow> (((real^'m::{finite,wellorder}) \<times> ((real,2) vec))
                    \<Rightarrow> real^'m::{finite,wellorder})"
      and p0 :: "nat \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec))"
      where pick:
        "\<And>i. e i = \<phi>0 i ` (U0 i) \<and>
              open (U0 i) \<and>
              u00 i \<in> U0 i \<and>
              \<phi>0 i (u00 i) = p0 i \<and>
              \<phi>0 i differentiable_on (U0 i) \<and>
              \<phi>0 i ` (U0 i) \<subseteq> M \<and>
              openin (top_of_set M) (\<phi>0 i ` (U0 i)) \<and>
              homeomorphism (U0 i) (e i) (\<phi>0 i) (g0 i)"
      using ex_pick
    proof -
      have "\<exists>(U0::nat \<Rightarrow> (real^'m::{finite,wellorder}) set)
              (u00::nat \<Rightarrow> real^'m::{finite,wellorder})
              (\<phi>0::nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec))))
              (g0::nat \<Rightarrow> (((real^'m::{finite,wellorder}) \<times> ((real,2) vec)) \<Rightarrow> real^'m::{finite,wellorder}))
              (p0::nat \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec))).
          \<forall>i. e i = \<phi>0 i ` (U0 i) \<and> open (U0 i) \<and> u00 i \<in> U0 i \<and> \<phi>0 i (u00 i) = p0 i \<and>
              \<phi>0 i differentiable_on (U0 i) \<and> \<phi>0 i ` (U0 i) \<subseteq> M \<and>
              openin (top_of_set M) (\<phi>0 i ` (U0 i)) \<and> homeomorphism (U0 i) (e i) (\<phi>0 i) (g0 i)"
        using ex_pick
        unfolding choice_iff
        by blast
      then show ?thesis
        using that by blast
    qed

    show ?thesis
      by (smt (verit, best) Sup.SUP_cong
          \<open>\<And>thesis. (\<And>U0 u00 \<phi>0 g0 p0. (\<And>i. e i = \<phi>0 i ` U0 i \<and> open (U0 i) \<and> u00 i \<in> U0 i \<and>
           \<phi>0 i (u00 i) = p0 i \<and> \<phi>0 i differentiable_on U0 i \<and> \<phi>0 i ` U0 i \<subseteq> M \<and> 
           openin (top_of_set M) (\<phi>0 i ` U0 i) \<and> homeomorphism (U0 i) (e i) (\<phi>0 i) (g0 i)) 
            \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> coverF' eimg)
    qed
qed

lemma projection_critical_sets_closed_upgrade_2d:
  fixes charts :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))"
    and Crit0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set"
  shows "\<exists>(Crit :: nat \<Rightarrow> (real^'m::{finite,wellorder}) set).
          (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))) \<and>
          (\<Union>i. (fst \<circ> charts i) ` (Crit0 i)) \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
          (\<forall>i. Crit0 i \<subseteq> Crit i)"
  sorry

lemma projection_critical_sets_extend_derivative_rank_2d:
  fixes charts :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))"
    and Crit0 Crit :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set"
    and D0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder})
                 \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder}))"
  assumes "\<forall>i. Crit0 i \<subseteq> Crit i"
    and der0:
      "\<forall>i x. x \<in> Crit0 i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative (blinfun_apply (D0 i x))) (at x within Crit0 i)"
    and rk0:
      "\<forall>i x. x \<in> Crit0 i \<longrightarrow>
        rank (matrix (blinfun_apply (D0 i x))) < CARD('m)"
  shows "(\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D0 i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            rank (matrix (blinfun_apply (D0 i x))) < CARD('m))"
  sorry

lemma regular_zero_set_projection_charts_stub_2d:
  fixes V :: "(real^'m::{finite,wellorder}) set"
    and \<Omega> :: "(real^2) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^2)) \<Rightarrow> (real^2)"
  assumes "open V" "V \<noteq> {}" "open \<Omega>"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "\<exists>(charts :: nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec))))
            (Crit :: nat \<Rightarrow> (real^'m::{finite,wellorder}) set)
            (D :: nat \<Rightarrow> real^'m::{finite,wellorder}
                       \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder}))).
           {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
               (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
             \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
           (\<forall>i x. x \<in> Crit i \<longrightarrow>
              ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
           (\<forall>i x. x \<in> Crit i \<longrightarrow>
              rank (matrix (blinfun_apply (D i x))) < CARD('m)) \<and>
           (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  text \<open>
    We split the missing geometric step into three lemmas:

    1. Build local smooth parametrizations of the regular level set
       \<open>M = {(x,\<omega>)\<in>V\<times>\<Omega>. G(x,\<omega>)=0}\<close>.
    2. Show "bad parameters" are contained in the critical values of the
       projection \<open>\<pi>(x,\<omega>)=x\<close> in those charts, and record the rank-defect Jacobian.
    3. Extract a countable subcover and upgrade the critical images to closed sets.

    This is exactly the pipeline used later with @{thm baby_Sard}.
  \<close>

  have "\<exists>(charts :: nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec))))
            (Crit0 :: nat \<Rightarrow> (real^'m::{finite,wellorder}) set)
            (D0 :: nat \<Rightarrow> (real^'m::{finite,wellorder})
                       \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder}))).
           {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
               (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
             \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit0 i)) \<and>
           (\<forall>i x. x \<in> Crit0 i \<longrightarrow>
              ((fst \<circ> charts i) has_derivative (blinfun_apply (D0 i x))) (at x within Crit0 i)) \<and>
           (\<forall>i x. x \<in> Crit0 i \<longrightarrow>
              rank (matrix (blinfun_apply (D0 i x))) < CARD('m))"
    using regular_zero_set_projection_charts_core_2d[OF assms] by blast
  then obtain
    charts :: "nat \<Rightarrow> (real^'m::{finite,wellorder} \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> ((real,2) vec)))"
    and Crit0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set"
    and D0 :: "nat \<Rightarrow> (real^'m::{finite,wellorder})
                      \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder}))"
  where
    sub0:
      "{x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
           (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit0 i))"
    and der0:
      "\<forall>i x. x \<in> Crit0 i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative (blinfun_apply (D0 i x))) (at x within Crit0 i)"
    and rk0:
      "\<forall>i x. x \<in> Crit0 i \<longrightarrow>
        rank (matrix (blinfun_apply (D0 i x))) < CARD('m)"
    by blast

  have "\<exists>(Crit :: nat \<Rightarrow> (real^'m::{finite,wellorder}) set).
          (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))) \<and>
          (\<Union>i. (fst \<circ> charts i) ` (Crit0 i)) \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
          (\<forall>i. Crit0 i \<subseteq> Crit i)"
    using projection_critical_sets_closed_upgrade_2d[of charts Crit0] by blast
  then obtain Crit where
    cl: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    and cover: "(\<Union>i. (fst \<circ> charts i) ` (Crit0 i)) \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    and Crit_mono: "\<forall>i. Crit0 i \<subseteq> Crit i"
    by auto

  have sub: "{x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
                (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
              \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    using sub0 cover by auto

  have der_rk:
      "(\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D0 i x))) (at x within Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow>
          rank (matrix (blinfun_apply (D0 i x))) < CARD('m))"
    using Crit_mono der0 rk0 projection_critical_sets_extend_derivative_rank_2d                    
    by (metis projection_critical_sets_extend_derivative_rank_2d) 

  show ?thesis
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D0])
       (use sub der_rk cl in auto)
qed

text \<open>
  Roadmap for discharging @{thm regular_zero_set_projection_charts_stub_2d} without
  importing a full manifold library.

  We will factor the proof into three reusable pieces.

  1. **Regular value \<open>\<Rightarrow>\<close> local parametrizations of the zero set.**
     Let \<open>M = {(x,\<omega>)\<in>V\<times>\<Omega>. G(x,\<omega>) = 0}\<close>.  From
     @{term "regular_value_on G (V\<times>\<Omega>) 0"}, every \<open>p\<in>M\<close> has a neighborhood
     on which \<open>M\<close> can be parametrized by a smooth chart
     \<open>\<phi> : U \<subseteq> \<real>^'m \<to> \<real>^'m\<times>\<real>^2\<close> with image in \<open>M\<close>.
     This is a special case of the constant-rank theorem / regular level set theorem.
     We will implement this directly using the inverse function theorem
     (Isabelle: @{thm inverse_function_theorem_scaled}) plus linear algebra to pick
     suitable coordinates.

  2. **Bad parameters are critical values of the projection.**
     With \<open>\<pi>(x,\<omega>) = x\<close>, show:
     if \<open>p=(x,\<omega>)\<in>M\<close> and the slice derivative
     \<open>D\<omega> : \<real>^2\<to>\<real>^2\<close> is not surjective, while the full derivative of \<open>G\<close>
     at \<open>p\<close> is surjective, then the differential of \<open>\<pi>\<close> restricted to the tangent
     space \<open>T_p M\<close> fails to be injective, hence in charts the Jacobian of
     \<open>\<pi>\<circ>\<phi>\<close> has rank defect.  This is elementary linear algebra and will be
     expressed in terms of kernels of the derivative map.

  3. **Countable cover and closed critical images.**
     Use second countability of Euclidean space to extract a countable subcover of
     the local parametrizations.  Define \<open>Crit i\<close> as a closed subset of each chart
     domain where the rank defect holds; then \<open>(fst\<circ>charts i) ` Crit i\<close> is closed.

  Once these are in place, @{thm negligible_critical_values_from_charts} finishes
  the Sard step automatically.
\<close>

text \<open>
  Intended proof of {thm regular_zero_set_projection_charts_stub} (sketch, to be
  implemented):

  * Define the joint zero set \<open>M = {(x,\<omega>)\<in>V\<times>\<Omega>. G(x,\<omega>) = 0}\<close>.
  * Use {term reg0} (regular value at 0) to get local coordinate systems around
    each point of \<open>M\<close> in which \<open>M\<close> is described as the graph of a smooth map
    from an open subset of \<open>real^'m\<close> into \<open>real^'n\<close>. Concretely, because
    {term "CARD('n) = CARD('k)"} in our application, these charts can be chosen
    so that the parameter coordinates correspond to the first component
    (projection to \<open>V\<close>).
  * In each chart, the projection \<open>\<pi>(x,\<omega>) = x\<close> becomes a smooth map
    \<open>real^'m \<to> real^'m\<close>. The set of points where the slice map
    \<open>u \<mapsto> G(x,u)\<close> fails to be transverse to 0 corresponds to points where the
    differential of \<open>\<pi>\<close> has rank defect, hence points of a critical set
    \<open>Crit i\<close> for that chart.
  * Instantiate {thm negligible_critical_values_from_charts} with these charts.
\<close>

theorem parametric_transversality_negligible_stub:
  fixes V :: "(real^'m::{finite,wellorder}) set"
    and \<Omega> :: "(real^'n::{finite,wellorder}) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^'n::{finite,wellorder}))
                \<Rightarrow> (real^'k::{finite,wellorder})"
  assumes "open V" "V \<noteq> {}"
    and "open \<Omega>"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "negligible {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
                 (\<not> (\<exists>D. ((\<lambda>u. G (x,u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D))}"
proof -
  obtain charts :: "nat \<Rightarrow> (real^'m::{finite,wellorder})
                            \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^'n::{finite,wellorder}))"
     and Crit :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set"
     and D :: "nat \<Rightarrow> (real^'m::{finite,wellorder})
                       \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder}))"
   where
    sub: "{x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
             (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
           \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
              ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
    and rk: "\<forall>i x. x \<in> Crit i \<longrightarrow> rank (matrix (blinfun_apply (D i x))) < CARD('m)"
    using regular_zero_set_projection_charts_stub[OF assms] by blast
  have "negligible (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    by (rule negligible_critical_values_from_charts)
       (use der rk in auto)
  then show ?thesis
    using negligible_subset sub by blast
qed

text \<open>
  Bridge from Lebesgue-negligibility to the topological notion \<^const>\<open>meager\<close>
  (defined in \<^theory>\<open>Applied_Math_Nonemptiness.Nonemptiness_Scaffold\<close>). Note
  \<^const>\<open>negligible\<close> alone does \<^emph>\<open>not\<close> imply \<^const>\<open>meager\<close>; one needs the
  negligible set to be \<^emph>\<open>closed\<close> (then it is nowhere dense by
  @{thm open_not_negligible}), and a countable union of nowhere-dense sets is meager.
\<close>

lemma meager_nowhere_dense:
  fixes A :: "'a::topological_space set"
  assumes "nowhere_dense A"
  shows "meager A"
  using assms unfolding meager_def by (intro exI[of _ "\<lambda>_. A"]) auto

lemma nowhere_dense_closed_negligible:
  fixes A :: "'a::euclidean_space set"
  assumes "closed A" and "negligible A"
  shows "nowhere_dense A"
proof -
  have "interior A = {}"
  proof (rule ccontr)
    assume ne: "interior A \<noteq> {}"
    have "\<not> negligible (interior A)"
      by (rule open_not_negligible[OF open_interior ne])
    moreover have "negligible (interior A)"
      by (rule negligible_subset[OF assms(2) interior_subset])
    ultimately show False by blast
  qed
  with assms(1) show ?thesis
    by (simp only: nowhere_dense_def closure_closed)
qed

lemma meager_negligible_closed_cover:
  fixes A :: "'a::euclidean_space set"
  assumes "A \<subseteq> (\<Union>n::nat. K n)"
    and "\<And>n. closed (K n)" and "\<And>n. negligible (K n)"
  shows "meager A"
proof -
  have "meager (\<Union>n. K n)"
  proof (rule meager_Union_nat)
    fix n
    show "meager (K n)"
      by (rule meager_nowhere_dense[OF nowhere_dense_closed_negligible[OF assms(2) assms(3)]])
  qed
  then show ?thesis
    using assms(1) meager_subset by blast
qed

theorem parametric_transversality_meager_euclidean_stub:
  fixes V :: "(real^'m::{finite,wellorder}) set"
    and \<Omega> :: "(real^'n::{finite,wellorder}) set"
    and G :: "((real^'m::{finite,wellorder}) \<times> (real^'n::{finite,wellorder}))
                \<Rightarrow> (real^'k::{finite,wellorder})"
  assumes "open V" "V \<noteq> {}"
    and "open \<Omega>"
    and reg0: "regular_value_on G (V\<times>\<Omega>) 0"
  shows "meager {x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
                 (\<not> (\<exists>D. ((\<lambda>u. G (x,u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D))}"
proof -
  obtain charts :: "nat \<Rightarrow> (real^'m::{finite,wellorder})
                            \<Rightarrow> ((real^'m::{finite,wellorder}) \<times> (real^'n::{finite,wellorder}))"
     and Crit :: "nat \<Rightarrow> (real^'m::{finite,wellorder}) set"
     and D :: "nat \<Rightarrow> (real^'m::{finite,wellorder})
                       \<Rightarrow> ((real^'m::{finite,wellorder}) \<Rightarrow>\<^sub>L (real^'m::{finite,wellorder}))"
   where
    sub: "{x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
             (\<not> (\<exists>D\<omega>. ((\<lambda>u. G (x,u)) has_derivative D\<omega>) (at \<omega> within \<Omega>) \<and> surj D\<omega>))}
           \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
              ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
    and rk: "\<forall>i x. x \<in> Crit i \<longrightarrow> rank (matrix (blinfun_apply (D i x))) < CARD('m)"
    and cl: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using regular_zero_set_projection_charts_stub[OF assms] by blast
  have neg: "negligible (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    by (rule negligible_critical_values_from_charts) (use der rk in auto)
  show ?thesis
  proof (rule meager_negligible_closed_cover[where K = "\<lambda>i. (fst \<circ> charts i) ` (Crit i)"])
    show "{x\<in>V. \<exists>\<omega>\<in>\<Omega>. G (x,\<omega>) = 0 \<and>
             (\<not> (\<exists>D. ((\<lambda>u. G (x,u)) has_derivative D) (at \<omega> within \<Omega>) \<and> surj D))}
           \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      by (rule sub)
    show "\<And>i. closed ((fst \<circ> charts i) ` (Crit i))"
      using cl by simp
    show "\<And>i. negligible ((fst \<circ> charts i) ` (Crit i))"
    proof -
      fix i
      have "negligible ((fst \<circ> charts i) ` (Crit i))"
      proof (rule baby_Sard[where f = "fst \<circ> charts i" and S = "Crit i" and f' = "\<lambda>x. D i x"])
        show "CARD('m) \<le> CARD('m)"
          by simp
        show "\<And>x. x \<in> Crit i \<Longrightarrow> ((fst \<circ> charts i) has_derivative blinfun_apply (D i x)) (at x within Crit i)"
          using der by simp
        show "\<And>x. x \<in> Crit i \<Longrightarrow> rank (matrix (blinfun_apply (D i x))) < CARD('m)"
          using rk by simp
      qed
      then show "negligible ((fst \<circ> charts i) ` (Crit i))" .
    qed
  qed
qed

end
