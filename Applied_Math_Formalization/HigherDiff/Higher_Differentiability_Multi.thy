section \<open>Higher-Order Differentiability in Several Variables\<close>

text \<open>
  This theory develops \<open>k\<close>-times Fréchet differentiability and \<open>C\<^sup>k\<close> smoothness
  for maps between arbitrary real normed vector spaces.

  \<^bold>\<open>Design principles.\<close>
  \<^enum> \<open>k_times_Fr_differentiable_at\<close> captures pure differentiability (no
    continuity).  Its base case is \<open>True\<close>.
  \<^enum> \<open>Ck_at\<close> captures \<open>C\<^sup>k\<close> at a point: \<open>k\<close>-times differentiable in a
    neighbourhood and the \<open>k\<close>-th--level directional derivatives are continuous
    at the point.  Its base case is continuity.
  \<^enum> \<open>Ck_on\<close> captures \<open>C\<^sup>k\<close> on an open set.

  Both \<open>k_times_Fr_differentiable_at\<close> and \<open>Ck_at\<close> use the
  directional-derivative trick of Smooth\_Manifolds to keep the codomain type
  uniform across differentiation levels.

  We relate these to the one-dimensional definitions in
  \<open>Higher_Differentiability\<close> and to the AFP's
  \<open>higher_differentiable_on\<close> from \<open>Smooth_Manifolds.Smooth\<close>.
\<close>

theory Higher_Differentiability_Multi
  imports "HOL-Analysis.Analysis"
          Higher_Differentiability          (* 1-d theory: k_times_differentiable_at, C_k_on, etc. *)
          Smooth_Manifolds.Smooth           (* AFP: higher_differentiable_on *)
begin

(* ================================================================== *)
subsection \<open>Multi-dimensional \<open>k\<close>-times Fréchet differentiability at a point\<close>
(* ================================================================== *)

text \<open>
  This is the pure differentiability notion: no continuity assumption.
  Compare with @{const k_times_differentiable_at} which is the \<open>real \<Rightarrow> real\<close>
  specialisation.

  \<^item> \<open>0\<close>-times differentiable is trivially true (no condition).
  \<^item> \<open>(Suc k)\<close>-times differentiable at \<open>x\<close> means:
    \<^enum> \<open>f\<close> is \<open>k\<close>-times differentiable in a neighbourhood of \<open>x\<close>;
    \<^enum> \<open>f\<close> is Fréchet differentiable at \<open>x\<close>; and
    \<^enum> for every direction \<open>v\<close>, the map
      \<open>\<lambda>y. frechet_derivative f (at y) v\<close> is \<open>k\<close>-times differentiable at \<open>x\<close>.

  Clause (c) replaces the 1-d clause
  ``the \<open>k\<close>-th derivative has a derivative at \<open>x\<close>''
  and avoids the type escalation that would arise from iterating the
  Fréchet derivative directly.
\<close>

primrec k_times_Fr_differentiable_at
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "k_times_Fr_differentiable_at 0 f x \<longleftrightarrow> True"
| "k_times_Fr_differentiable_at (Suc k) f x \<longleftrightarrow>
     (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k f y))
   \<and> f differentiable (at x)
   \<and> (\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x)"

text \<open>Sanity check: \<open>1\<close>-times differentiable = Fréchet differentiable.\<close>

lemma one_times_Fr_iff:
  "k_times_Fr_differentiable_at 1 f x \<longleftrightarrow> f differentiable (at x)"
  by auto

text \<open>Monotonicity: higher differentiability implies lower.\<close>

lemma k_times_Fr_differentiable_at_mono:
  assumes "m \<le> k" and "k_times_Fr_differentiable_at k f x"
  shows   "k_times_Fr_differentiable_at m f x"
  using assms
proof (induction k arbitrary: m f x)
  case 0
  then have "m = 0" by simp
  then show ?case by simp
next
  case (Suc k)
  note IH = Suc.IH
  note asm = Suc.prems

  show ?case
  proof (cases m)
    case 0
    then show ?thesis by simp
  next
    case (Suc m')
    from asm(1) Suc have m'_le: "m' \<le> k"
      by simp

    from asm(2) obtain A where
      A: "open A"
         "x \<in> A"
         "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
      and fdiff: "f differentiable (at x)"
      and D: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
      by auto

    have A': "\<forall>y\<in>A. k_times_Fr_differentiable_at m' f y"
      using A(3) IH[OF m'_le] by blast

    have D': "\<forall>v. k_times_Fr_differentiable_at m' (\<lambda>y. frechet_derivative f (at y) v) x"
      using D IH[OF m'_le] by blast

    show ?thesis
      using Suc A fdiff D' A'
      by (metis IH asm(1,2) le_Suc_eq)
  qed
qed

text \<open>Peeling off the top layer.\<close>

lemma k_times_Fr_differentiable_at_SucD:
  assumes "k_times_Fr_differentiable_at (Suc k) f x"
  shows   "k_times_Fr_differentiable_at k f x"
    and   "f differentiable (at x)"
    and   "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
  using assms k_times_Fr_differentiable_at_mono
  by auto

text \<open>The derivative field inherits differentiability.\<close>

lemma k_times_Fr_differentiable_at_derivative:
  assumes "k_times_Fr_differentiable_at (Suc k) f x"
  shows   "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
  using assms by simp


(* ================================================================== *)
subsection \<open>Set-wise \<open>k\<close>-times Fréchet differentiability\<close>
(* ================================================================== *)

definition k_times_Fr_differentiable_on
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "k_times_Fr_differentiable_on k f S \<longleftrightarrow> (\<forall>x\<in>S. k_times_Fr_differentiable_at k f x)"

lemma k_times_Fr_differentiable_onI:
  "(\<And>x. x \<in> S \<Longrightarrow> k_times_Fr_differentiable_at k f x) \<Longrightarrow> k_times_Fr_differentiable_on k f S"
  by (simp add: k_times_Fr_differentiable_on_def)

lemma k_times_Fr_differentiable_onD:
  "k_times_Fr_differentiable_on k f S \<Longrightarrow> x \<in> S \<Longrightarrow> k_times_Fr_differentiable_at k f x"
  by (simp add: k_times_Fr_differentiable_on_def)

lemma k_times_Fr_differentiable_on_mono:
  "m \<le> k \<Longrightarrow> k_times_Fr_differentiable_on k f S \<Longrightarrow> k_times_Fr_differentiable_on m f S"
  by (simp add: k_times_Fr_differentiable_on_def k_times_Fr_differentiable_at_mono)

lemma k_times_Fr_differentiable_on_subset:
  "S \<subseteq> T \<Longrightarrow> k_times_Fr_differentiable_on k f T \<Longrightarrow> k_times_Fr_differentiable_on k f S"
  by (simp add: k_times_Fr_differentiable_on_def subset_iff)


(* ================================================================== *)
subsection \<open>\<open>C\<^sup>k\<close> at a point (with continuity)\<close>
(* ================================================================== *)

text \<open>
  \<open>Ck_at k f x\<close> says \<open>f\<close> is \<open>C\<^sup>k\<close> at \<open>x\<close>:
  \<^item> \<open>k = 0\<close>: \<open>f\<close> is continuous at \<open>x\<close>.
  \<^item> \<open>k = Suc n\<close>: \<open>f\<close> is \<open>C\<^sup>n\<close> in a neighbourhood of \<open>x\<close>,
    \<open>f\<close> is differentiable at \<open>x\<close>, and for every direction \<open>v\<close> the
    directional derivative map is \<open>C\<^sup>n\<close> at \<open>x\<close>.

  This is the pointwise version that corresponds to
  @{const higher_differentiable_on} restricted to a neighbourhood.
\<close>

primrec Ck_at
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "Ck_at 0 f x \<longleftrightarrow> continuous (at x) f"
| "Ck_at (Suc k) f x \<longleftrightarrow>
     (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k f y))
   \<and> f differentiable (at x)
   \<and> (\<forall>v. Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x)"


(* ================================================================== *)
subsection \<open>\<open>C\<^sup>k\<close> on an open set\<close>
(* ================================================================== *)

text \<open>
  We define \<open>Ck_on k f U\<close> to mean \<open>f\<close> is \<open>C\<^sup>k\<close> on the open set \<open>U\<close>.
  This is the multi-dimensional generalisation of
  @{const C_k_on} from \<open>Limits_Higher_Order_Derivatives\<close>.
\<close>

definition Ck_on
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "Ck_on k f U \<longleftrightarrow> open U \<and> (\<forall>x\<in>U. Ck_at k f x)"


(* ================================================================== *)
subsection \<open>Relationships between the three notions\<close>
(* ================================================================== *)

text \<open>\<open>C\<^sup>k\<close> implies \<open>k\<close>-times differentiable (forgetting continuity).\<close>

lemma Ck_at_imp_k_times_Fr:
  "Ck_at k f x \<Longrightarrow> k_times_Fr_differentiable_at k f x"
proof (induction k arbitrary: f x)
  case 0 then show ?case by simp
next
  case (Suc k)
  then show ?case
    by auto
qed

corollary Ck_on_imp_k_times_Fr_on:
  "Ck_on k f U \<Longrightarrow> k_times_Fr_differentiable_on k f U"
  by (simp add: Ck_on_def k_times_Fr_differentiable_on_def Ck_at_imp_k_times_Fr)


(* ================================================================== *)
subsection \<open>Equivalence with AFP's \<open>higher_differentiable_on\<close>\<close>
(* ================================================================== *)

text \<open>
  The AFP predicate @{const higher_differentiable_on} from
  \<open>Smooth_Manifolds.Smooth\<close> is a \<open>C\<^sup>k\<close> notion (continuity baked into
  the base case).  We show it agrees with our \<open>Ck_on\<close>.
\<close>

lemma Ck_on_iff_higher_differentiable_on:
  assumes "open U"
  shows "Ck_on k f U \<longleftrightarrow> higher_differentiable_on U f k"
  using assms
proof (induction k arbitrary: f U)
  case 0
  show ?case
  proof
    assume "Ck_on 0 f U"
    then have "\<forall>x\<in>U. continuous (at x) f"
      by (simp add: Ck_on_def)
    then have "\<forall>x\<in>U. continuous (at x within U) f"
      using continuous_at_imp_continuous_at_within by blast
    then show "higher_differentiable_on U f 0"
      by (simp add: continuous_on_eq_continuous_within higher_differentiable_on.simps(1))
  next
    assume "higher_differentiable_on U f 0"
    then have "continuous_on U f"
      using higher_differentiable_on.simps(1) by blast
    then have "\<forall>x\<in>U. continuous (at x within U) f"
      using continuous_on_eq_continuous_within by blast
    then have "\<forall>x\<in>U. continuous (at x) f"
      by (metis "0" at_within_open)
    then show "Ck_on 0 f U"
      using "0" by (simp add: Ck_on_def)
  qed
next
  case (Suc k)
  show ?case
  proof
    assume "Ck_on (Suc k) f U"
    then have U_open: "open U"
      and Cat: "\<forall>x\<in>U. Ck_at (Suc k) f x"
      by (auto simp: Ck_on_def)
    have diff: "\<forall>x\<in>U. f differentiable (at x)"
      using Cat by auto
    have der_Ck_on: "\<forall>v. Ck_on k (\<lambda>y. frechet_derivative f (at y) v) U"
      using Cat Ck_on_def U_open by fastforce
    have der_higher: "\<forall>v. higher_differentiable_on U (\<lambda>y. frechet_derivative f (at y) v) k"
      using Suc.IH[OF U_open] der_Ck_on by blast
    then show "higher_differentiable_on U f (Suc k)"
      using diff higher_differentiable_on.simps(2) by blast
  next
    assume H: "higher_differentiable_on U f (Suc k)"
    then have diff: "\<forall>x\<in>U. f differentiable (at x)"
      and der_higher:
        "\<forall>v. higher_differentiable_on U (\<lambda>y. frechet_derivative f (at y) v) k"
      using H higher_differentiable_on.simps(2) by blast+
    have Hk: "higher_differentiable_on U f k"
      using H by (rule higher_differentiable_on_SucD)
    have CkU: "Ck_on k f U"
      using Suc.IH[OF Suc.prems] Hk by blast
    have der_Ck_on: "\<forall>v. Ck_on k (\<lambda>y. frechet_derivative f (at y) v) U"
      using Suc.IH[OF Suc.prems] der_higher by blast
    show "Ck_on (Suc k) f U"
      by (metis CkU Ck_at.simps(2) Ck_on_def der_Ck_on diff)
  qed
qed


(* ================================================================== *)
subsection \<open>Bridge to the one-dimensional theory\<close>
(* ================================================================== *)


text \<open>Multi-d \<open>k\<close>-times differentiable = 1-d \<open>k\<close>-times differentiable for reals.\<close>


text \<open>
  The forward implication, proved by induction on \<open>k\<close>.  Being \<open>k\<close>-times
  differentiable at \<open>x\<close> is a local property: if \<open>f\<close> and \<open>g\<close> agree on an open
  neighbourhood of \<open>x\<close>, then they are \<open>k\<close>-times differentiable at \<open>x\<close> together.
\<close>

lemma k_times_differentiable_at_transfer_open:
  fixes f g :: "real \<Rightarrow> real"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
    and Hf: "k_times_differentiable_at k f x"
  shows "k_times_differentiable_at k g x"
  using U eq Hf
proof (induction k arbitrary: f g x U)
  case 0
  then show ?case by simp
next
  case (Suc k)

  text \<open>Unfold the definition at \<open>x\<close>: an \<open>\<epsilon>\<close>-ball of lower-order differentiability
        plus a derivative condition at \<open>x\<close>.\<close>
  from Suc.prems(4) obtain \<epsilon> where \<epsilon>pos: "\<epsilon> > 0"
    and ball_f: "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow> k_times_differentiable_at k f y"
    and der_f: "((deriv ^^ k) f
                   has_derivative (\<lambda>h. (deriv ^^ Suc k) f x * h)) (at x)"
    by auto

  text \<open>Shrink the ball so that it sits inside \<open>U\<close>, where \<open>f = g\<close>.\<close>
  obtain \<delta> where \<delta>pos: "\<delta> > 0" and ballU: "ball x \<delta> \<subseteq> U"
    using Suc.prems(1,2) open_contains_ball by blast
  define r where "r = min \<epsilon> \<delta>"
  have rpos: "r > 0" using \<epsilon>pos \<delta>pos by (simp add: r_def)

  define B where "B = ball x r"
  have openB: "open B" and xB: "x \<in> B" using rpos by (auto simp: B_def)
  have BsubU: "B \<subseteq> U"
    using ballU by (auto simp: B_def r_def dist_real_def abs_minus_commute)
  have eqB: "\<forall>y\<in>B. f y = g y" using BsubU Suc.prems(3) by auto

  text \<open>On \<open>B\<close> the function \<open>f\<close> is \<open>k\<close>-times differentiable.\<close>
  have f_on_B: "f k-times_differentiable_on B"
    by (rule k_times_differentiable_onI)
       (auto simp: B_def r_def dist_real_def abs_minus_commute intro!: ball_f)

  text \<open>Transfer this to \<open>g\<close> and obtain agreement of the lower derivatives.\<close>
  have g_on_B: "g k-times_differentiable_on B"
   and der_agree: "\<forall>y\<in>B. \<forall>m<k. ((deriv ^^ m) g
                       has_derivative (*) ((deriv ^^ Suc m) f y)) (at y)"
    using times_differentiable_on_transfer[OF openB f_on_B eqB] by blast+

  text \<open>Part 1: the \<open>\<epsilon>\<close>-ball condition for \<open>g\<close> (radius \<open>r\<close>).\<close>
  have ball_g: "\<forall>y. \<bar>y - x\<bar> < r \<longrightarrow> k_times_differentiable_at k g y"
    using g_on_B
    by (auto simp: k_times_differentiable_on_def B_def dist_real_def abs_minus_commute)

  text \<open>Part 2: the \<open>k\<close>-th derivatives of \<open>f\<close> and \<open>g\<close> coincide on \<open>B\<close>.\<close>
  have kth_eq: "\<forall>y\<in>B. (deriv ^^ k) f y = (deriv ^^ k) g y"
  proof (cases k)
    case 0
    then show ?thesis using eqB by simp
  next
    case (Suc n)
    show ?thesis
    proof
      fix y assume yB: "y \<in> B"
      have "((deriv ^^ n) g has_derivative (*) ((deriv ^^ Suc n) f y)) (at y)"
        using der_agree yB Suc by simp
      hence "deriv ((deriv ^^ n) g) y = (deriv ^^ Suc n) f y"
        by (rule deriv_eq)
      thus "(deriv ^^ k) f y = (deriv ^^ k) g y"
        using Suc by simp
    qed
  qed

  text \<open>Transfer the derivative condition at \<open>x\<close> from \<open>f\<close> to \<open>g\<close>.\<close>
  have der_f': "((deriv ^^ k) f has_derivative (*) ((deriv ^^ Suc k) f x)) (at x)"
    using der_f by simp
  have der_g': "((deriv ^^ k) g has_derivative (*) ((deriv ^^ Suc k) f x)) (at x)"
    using has_derivative_transfer_on_open[OF openB xB _ der_f'] kth_eq by blast
  have kSuc_eq: "(deriv ^^ Suc k) g x = (deriv ^^ Suc k) f x"
    using der_g' by (simp add: deriv_eq)

  have der_g: "((deriv ^^ k) g
                  has_derivative (\<lambda>h. (deriv ^^ Suc k) g x * h)) (at x)"
    using der_g' kSuc_eq by simp

  show "k_times_differentiable_at (Suc k) g x"
    using \<epsilon>pos rpos ball_g der_g by auto
qed

lemma eq_on_open_k_times_differentiable_at:
  fixes f g :: "real \<Rightarrow> real"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
  shows "k_times_differentiable_at k f x \<longleftrightarrow> k_times_differentiable_at k g x"
  using k_times_differentiable_at_transfer_open[OF U eq]
        k_times_differentiable_at_transfer_open[OF U(1,2), of g f k] eq
  by auto

lemma k_times_differentiable_at_cmult:
  fixes f :: "real \<Rightarrow> real"
  shows "k_times_differentiable_at k f x \<Longrightarrow>
         k_times_differentiable_at k (\<lambda>y. c * f y) x"
  by (rule kth_deriv_cmultE)



lemma k_times_Fr_real_iff:
  fixes f :: "real \<Rightarrow> real"
  shows "k_times_Fr_differentiable_at k f x \<longleftrightarrow> k_times_differentiable_at k f x"
proof (induction k arbitrary: f x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof
    assume H: "k_times_Fr_differentiable_at (Suc k) f x"

    from H obtain A where
      A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
      and df: "f differentiable (at x)"
      and D: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
      unfolding k_times_Fr_differentiable_at.simps(2)
      by blast

    have neigh: "\<forall>y\<in>A. k_times_differentiable_at k f y"
      using A(3) Suc.IH by blast

    have dk: "k_times_differentiable_at k (deriv f) x"
    proof (cases k)
      case 0
      then show ?thesis by simp
    next
      case (Suc j)

      have H1: "k_times_Fr_differentiable_at (Suc j)
                  (\<lambda>y. frechet_derivative f (at y) 1) x"
        using D Suc by simp
      then have dk1:
        "k_times_differentiable_at (Suc j)
           (\<lambda>y. frechet_derivative f (at y) 1) x"
        using Suc.IH Suc by blast

      have eq_deriv: "\<And>y. y \<in> A \<Longrightarrow> frechet_derivative f (at y) 1 = deriv f y"
        using A(3) Suc frechet_derivative_one_eq_deriv k_times_Fr_differentiable_at.simps(2) by blast


      have "k_times_differentiable_at (Suc j)
              (\<lambda>y. frechet_derivative f (at y) 1) x \<longleftrightarrow>
            k_times_differentiable_at (Suc j) (deriv f) x"
        using A(1,2) eq_deriv eq_on_open_k_times_differentiable_at by presburger
      then show ?thesis
        using Suc dk1 by blast
    qed

    show "k_times_differentiable_at (Suc k) f x"
    proof -
      obtain \<epsilon> where \<epsilon>pos: "\<epsilon> > 0" and ballA: "ball x \<epsilon> \<subseteq> A"
        using A(1,2) open_contains_ball by blast
      have part1: "\<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f y"
        using ballA neigh by (auto simp: dist_real_def abs_minus_commute,
                               simp add: dist_norm subsetD)
      have diffk: "(deriv ^^ k) f differentiable (at x)"
      proof (cases k)
        case 0
        then show ?thesis using df by simp
      next
        case (Suc j)
        from dk Suc have d: "(deriv f) (Suc j)-times_differentiable_at x" by simp
        have "((deriv ^^ j) (deriv f)
                 has_real_derivative (deriv ^^ Suc j) (deriv f) x) (at x)"
          using k_times_differentiable_at_le_deriv(2)[OF d lessI] .
        then have "(deriv ^^ j) (deriv f) differentiable (at x)"
          using real_differentiable_def by blast
        then show ?thesis
          using Suc kth_deriv_shift by metis
      qed
      have part2: "((deriv ^^ k) f
                      has_derivative (\<lambda>h. (deriv ^^ Suc k) f x * h)) (at x)"
      proof -
        from diffk have "((deriv ^^ k) f
                 has_real_derivative deriv ((deriv ^^ k) f) x) (at x)"
          using DERIV_deriv_iff_real_differentiable by blast
        then show ?thesis
          by (simp add: has_field_derivative_def)
      qed
      show ?thesis
        using \<epsilon>pos part1 part2 by auto
    qed
  next
    assume H: "k_times_differentiable_at (Suc k) f x"

    from H obtain \<epsilon> where \<epsilon>pos: "\<epsilon> > 0"
      and ball_f: "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow> k_times_differentiable_at k f y"
      by auto
    define A where "A = ball x \<epsilon>"
    have A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_differentiable_at k f y"
      using \<epsilon>pos ball_f by (auto simp: A_def dist_real_def abs_minus_commute)
    have df: "f differentiable (at x)"
    proof -
      have "f 1-times_differentiable_at x"
        using H k_times_differentiable_at_mono[of 1 "Suc k" f x] by simp
      then show ?thesis
        by (metis one_time_differentiable_at_iff real_differentiable_def)
    qed
    have dk: "k_times_differentiable_at k (deriv f) x"
      using k_times_differentiable_at_derivative[OF H] by simp

    have neigh: "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
      using A(3) Suc.IH by blast

    have D: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    proof
      fix v
      show "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
      proof (cases k)
        case 0
        then show ?thesis by simp
      next
        case (Suc j)

        have dk': "k_times_differentiable_at (Suc j) (\<lambda>y. v * deriv f y) x"
          using dk Suc k_times_differentiable_at_cmult[of "Suc j" "deriv f" x v]
          by blast
        hence dk'': "k_times_differentiable_at (Suc j) (\<lambda>y. deriv f y * v) x"
          by (simp add: mult.commute)

        have eq_deriv: "\<And>y. y \<in> A \<Longrightarrow> frechet_derivative f (at y) v = deriv f y * v"
          using Suc frechet_derivative_to_deriv neigh by auto

        have "k_times_differentiable_at (Suc j)
                (\<lambda>y. frechet_derivative f (at y) v) x \<longleftrightarrow>
              k_times_differentiable_at (Suc j) (\<lambda>y. deriv f y * v) x"
          using A(1,2) eq_deriv eq_on_open_k_times_differentiable_at by presburger
        then have "k_times_differentiable_at (Suc j)
                     (\<lambda>y. frechet_derivative f (at y) v) x"
          using dk'' by blast
        then show ?thesis
          using Suc Suc.IH by blast
      qed
    qed

    show "k_times_Fr_differentiable_at (Suc k) f x"
      unfolding k_times_Fr_differentiable_at.simps(2)
      using A(1,2) neigh df D by blast
  qed
qed

text \<open>Multi-d \<open>C\<^sup>k\<close> = 1-d \<open>C\<^sup>k\<close> for reals.\<close>

lemma Ck_on_real_iff:
  fixes f :: "real \<Rightarrow> real"
  assumes "open U"
  shows "Ck_on k f U \<longleftrightarrow> C_k_on k f U"
  using assms
  by (simp add: Ck_on_iff_higher_differentiable_on higher_differentiable_on_real_iff_Ck_on)


(* ================================================================== *)
subsection \<open>Basic closure properties\<close>
(* ================================================================== *)

text \<open>
  We state the main closure lemmas.  These generalise the 1-d results
  in \<open>Higher_Differentiability\<close>.  Detailed proofs are developed below.
\<close>

lemma k_times_Fr_const:
  "k_times_Fr_differentiable_at k (\<lambda>_. c) x"
proof (induction k arbitrary: x c)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>_. c) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto
  moreover have "(\<lambda>_. c) differentiable (at x)"
    by simp
  moreover have "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative (\<lambda>_. c) (at y) v) x"
    by (simp add: Suc)
  ultimately show ?case
    by simp
qed

lemma k_times_Fr_id:
  "k_times_Fr_differentiable_at k (\<lambda>x. x) x"
proof (induction k arbitrary: x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have nbhd:
    "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>x. x) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto
  have diff: "(\<lambda>x. x) differentiable (at x)"
    by simp
  have derivs: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative (\<lambda>x. x) (at y) v) x"
    by (simp add: k_times_Fr_const)
  show ?case
    using nbhd diff derivs
    by simp
qed

lemma Ck_at_const:
  "Ck_at k (\<lambda>_. c) x"
proof (induction k arbitrary: x c)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have nbhd: "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k (\<lambda>_. c) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto

  have diff: "(\<lambda>_. c) differentiable (at x)"
    by simp

  have derivs: "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative (\<lambda>_. c) (at y) v) x"
    by (simp add: Suc)

  show ?case
    using nbhd diff derivs
    by simp
qed

lemma Ck_on_const:
  "open U \<Longrightarrow> Ck_on k (\<lambda>_. c) U"
  by (simp add: Ck_on_def Ck_at_const)

text \<open>
  As in the one-dimensional case, the forward implication is proved by
  induction and the equivalence follows by symmetry of the hypotheses.
\<close>

lemma k_times_Fr_differentiable_at_transfer_open:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
    and Hf: "k_times_Fr_differentiable_at k f x"
  shows "k_times_Fr_differentiable_at k g x"
  using U eq Hf
proof (induction k arbitrary: f g x U)
  case 0
  then show ?case by simp
next
  case (Suc k)

  from Suc.prems(4) obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  let ?C = "A \<inter> U"
  have C: "open ?C" "x \<in> ?C"
    using A Suc.prems by auto

  have neigh: "\<forall>y\<in>?C. k_times_Fr_differentiable_at k g y"
    by (metis A(3) Int_iff Suc.IH Suc.prems(1,3))
  have evx: "eventually (\<lambda>y. y \<in> U) (nhds x)"
    using Suc.prems(1,2) by (simp add: eventually_nhds, auto)
  have evx_fg: "eventually (\<lambda>y. f y = g y) (nhds x)"
    by (rule eventually_mono[OF evx]) (use Suc.prems(3) in auto)


  have dg: "g differentiable (at x)"
    by (metis Suc.prems(1,2,3) df differentiable_eqI)

  have Dg: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis by simp
    next
      case (Suc j)

      have eqD:
        "\<And>y. y \<in> ?C \<Longrightarrow> frechet_derivative f (at y) v = frechet_derivative g (at y) v"
      proof -
        fix y
        assume yC: "y \<in> ?C"
        hence yA: "y \<in> A" and yU: "y \<in> U"
          by auto

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        hence dfy: "f differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have gy: "k_times_Fr_differentiable_at (Suc j) g y"
          using Suc neigh yC by blast

        hence dgy: "g differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" g y]
          by (simp add: one_times_Fr_iff)

        have evy: "eventually (\<lambda>z. f z = g z) (nhds y)"
          using Suc.prems(1) yU Suc.prems(3)
          by (simp add: eventually_nhds, auto)

        have "(f has_derivative frechet_derivative f (at y)) (at y)"
          by (simp add: dfy frechet_derivative_worksI)
        then have "(g has_derivative frechet_derivative f (at y)) (at y)"
          using Suc.prems(1,3) has_derivative_transfer_on_open yU by blast
        moreover have "(g has_derivative frechet_derivative g (at y)) (at y)"
          using dgy frechet_derivative_worksI by blast
        ultimately have "frechet_derivative f (at y) = frechet_derivative g (at y)"
          by (rule has_derivative_unique)
        then show "frechet_derivative f (at y) v = frechet_derivative g (at y) v"
          by simp
      qed

      have "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
        using Df by blast
      then show ?thesis
        using Suc.IH[OF C(1,2), of
            "\<lambda>y. frechet_derivative f (at y) v"
            "\<lambda>y. frechet_derivative g (at y) v"]
          eqD
        by blast
    qed
  qed

  show "k_times_Fr_differentiable_at (Suc k) g x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    using C neigh dg Dg by blast
qed

lemma eq_on_open_k_times_Fr_differentiable_at:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
  shows "k_times_Fr_differentiable_at k f x \<longleftrightarrow> k_times_Fr_differentiable_at k g x"
  using k_times_Fr_differentiable_at_transfer_open[OF U eq]
        k_times_Fr_differentiable_at_transfer_open[OF U(1,2), of g f k] eq
  by auto

lemma k_times_Fr_add:
  assumes "k_times_Fr_differentiable_at k f x"
      and "k_times_Fr_differentiable_at k g x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. f y + g y) x"
  using assms
proof (induction k arbitrary: f g x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  from Suc.prems(1) obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  from Suc.prems(2) obtain B where
    B: "open B" "x \<in> B" "\<forall>y\<in>B. k_times_Fr_differentiable_at k g y"
    and dg: "g differentiable (at x)"
    and Dg: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  let ?C = "A \<inter> B"
  have C: "open ?C" "x \<in> ?C"
    using A B by auto

  have neigh: "\<forall>y\<in>?C. k_times_Fr_differentiable_at k (\<lambda>z. f z + g z) y"
  proof
    fix y
    assume yC: "y \<in> ?C"
    then have yA: "y \<in> A" and yB: "y \<in> B"
      by auto
    show "k_times_Fr_differentiable_at k (\<lambda>z. f z + g z) y"
      using Suc.IH A(3)[rule_format, OF yA] B(3)[rule_format, OF yB] by blast
  qed

  have diff: "(\<lambda>y. f y + g y) differentiable (at x)"
    by (simp add: df dg)
  have Dsum:"\<forall>v. k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k
            (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc j)

      have ksum:
        "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative f (at y) v + frechet_derivative g (at y) v) x"
        using Suc.IH Df Dg by blast

      have eqD:
        "\<And>y. y \<in> ?C \<Longrightarrow>
          frechet_derivative (\<lambda>z. f z + g z) (at y) v =
          frechet_derivative f (at y) v + frechet_derivative g (at y) v"
      proof -
        fix y
        assume yC: "y \<in> ?C"
        then have yA: "y \<in> A" and yB: "y \<in> B"
          by auto

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        have gy: "k_times_Fr_differentiable_at (Suc j) g y"
          using B(3) Suc yB by blast


        have dfy: "f differentiable (at y)"
          using fy k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have dgy: "g differentiable (at y)"
          using gy k_times_Fr_differentiable_at_mono[of 1 "Suc j" g y]
          by (simp add: one_times_Fr_iff)

        have hder: "((\<lambda>z. f z + g z) has_derivative
             (\<lambda>h. frechet_derivative f (at y) h + frechet_derivative g (at y) h)) (at y)"
          by (simp add: dfy dgy frechet_derivative_worksI)

        then have "frechet_derivative (\<lambda>z. f z + g z) (at y) =
              (\<lambda>h. frechet_derivative f (at y) h + frechet_derivative g (at y) h)"
          using frechet_derivative_at' by blast
        then show
          "frechet_derivative (\<lambda>z. f z + g z) (at y) v =
           frechet_derivative f (at y) v + frechet_derivative g (at y) v"
          by simp
      qed

      have
        "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x \<longleftrightarrow>
         k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative f (at y) v + frechet_derivative g (at y) v) x"
        by (smt (verit) C(1,2) eqD eq_on_open_k_times_Fr_differentiable_at)
      then show ?thesis
        using ksum by blast
    qed
  qed
  show ?case
    unfolding k_times_Fr_differentiable_at.simps(2)
    using C neigh diff Dsum by blast
qed

lemma k_times_Fr_scaleR:
  assumes "k_times_Fr_differentiable_at k f x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. c *\<^sub>R f y) x"
  using assms
proof (induction k arbitrary: f x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  from Suc.prems obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  have neigh: "\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>z. c *\<^sub>R f z) y"
    using A(3) Suc.IH by blast

  have diff: "(\<lambda>y. c *\<^sub>R f y) differentiable (at x)"
    by (simp add: df)

  have Dscale: "\<forall>v. k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k
            (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc j)

      have kscaled:
        "k_times_Fr_differentiable_at k
           (\<lambda>y. c *\<^sub>R frechet_derivative f (at y) v) x"
        using Suc.IH Df by blast

      have eqD:
        "\<And>y. y \<in> A \<Longrightarrow>
          frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v =
          c *\<^sub>R frechet_derivative f (at y) v"
      proof -
        fix y
        assume yA: "y \<in> A"

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        hence dfy: "f differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have hder: "((\<lambda>z. c *\<^sub>R f z) has_derivative (\<lambda>h. c *\<^sub>R frechet_derivative f (at y) h)) (at y)"
          by (simp add: dfy frechet_derivative_worksI has_derivative_scaleR_right)

        have "frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) = (\<lambda>h. c *\<^sub>R frechet_derivative f (at y) h)"
          by (metis frechet_derivative_at hder)
        then show "frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v =  c *\<^sub>R frechet_derivative f (at y) v"
          by simp
      qed

      have  "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x \<longleftrightarrow>
         k_times_Fr_differentiable_at k
           (\<lambda>y. c *\<^sub>R frechet_derivative f (at y) v) x"
        by (smt (verit) A(1,2) eqD eq_on_open_k_times_Fr_differentiable_at)
      then show ?thesis
        using kscaled by blast
    qed
  qed

  show ?case
    unfolding k_times_Fr_differentiable_at.simps(2)
    using A(1,2) neigh diff Dscale by blast
qed

lemma Ck_on_add:
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows   "Ck_on k (\<lambda>y. f y + g y) U"
proof -
  have U: "open U"
    using assms by (auto simp: Ck_on_def)

  have hf: "higher_differentiable_on U f k"
    using assms(1) U
    by (simp add: Ck_on_iff_higher_differentiable_on)

  have hg: "higher_differentiable_on U g k"
    using assms(2) U
    by (simp add: Ck_on_iff_higher_differentiable_on)

  have hsum: "higher_differentiable_on U (\<lambda>y. f y + g y) k"
    using hf hg U
    by (rule higher_differentiable_on_add)

  show ?thesis
    using U hsum
    by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_sum:
  fixes F :: "'i \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes fin: "finite I"
      and ne: "I \<noteq> {}"
      and Ck: "\<And>i. i \<in> I \<Longrightarrow> Ck_on k (F i) U"
  shows "Ck_on k (\<lambda>y. \<Sum>i\<in>I. F i y) U"
  using fin ne Ck
proof (induction rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  have Ci: "Ck_on k (F i) U"
    using insert.prems by simp
  show ?case
  proof (cases "I = {}")
    case True
    then show ?thesis
      using Ci insert.hyps by simp
  next
    case False
    have CI: "Ck_on k (\<lambda>y. \<Sum>j\<in>I. F j y) U"
      using insert.IH[OF False] insert.prems by blast
    show ?thesis
      using Ck_on_add[OF Ci CI] insert.hyps by simp
  qed
qed

lemma Ck_on_scaleR:
  assumes "Ck_on k f U"
  shows   "Ck_on k (\<lambda>y. c *\<^sub>R f y) U"
proof -
  have U: "open U"
    using assms by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms U
    by (simp add: Ck_on_iff_higher_differentiable_on)
  have hscale: "higher_differentiable_on U (\<lambda>y. c *\<^sub>R f y) k"
    by (simp add: U hf higher_differentiable_on_const higher_differentiable_on_scaleR)
  show ?thesis
    using U hscale
    by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_id:
  "open U \<Longrightarrow> Ck_on k (\<lambda>x. x) U"
  by (simp add: Ck_on_iff_higher_differentiable_on higher_differentiable_on_id)





lemma Ck_on_neg:
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. - f y) U"
proof -
  have "Ck_on k (\<lambda>y. (-1) *\<^sub>R f y) U"
    by (rule Ck_on_scaleR[OF assms])
  thus ?thesis by simp
qed

lemma Ck_on_sub:
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y - g y) U"
proof -
  have "Ck_on k (\<lambda>y. f y + (- g y)) U"
    by (rule Ck_on_add[OF assms(1) Ck_on_neg[OF assms(2)]])
  thus ?thesis by simp
qed


lemma Ck_on_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y * g y) U"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have hg: "higher_differentiable_on U g k"
    using assms(2) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U (\<lambda>y. f y * g y) k"
    using hf hg oU by (rule higher_differentiable_on_mult)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_pow:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. (f y) ^ n) U"
proof (induction n)
  case 0
  have "open U" using assms by (simp add: Ck_on_def)
  then show ?case
    using Ck_on_const by simp
next
  case (Suc n)
  have "Ck_on k (\<lambda>y. f y * (f y) ^ n) U"
    by (rule Ck_on_mult[OF assms Suc])
  thus ?case by (simp add: power_Suc2)
qed

lemma Ck_on_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U" and "\<And>y. y \<in> U \<Longrightarrow> f y \<noteq> 0"
  shows "Ck_on k (\<lambda>y. inverse (f y)) U"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U (\<lambda>y. inverse (f y)) k"
    using hf assms(2) oU by(subst higher_differentiable_on_inverse, simp_all, simp add: image_iff)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_divide:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U" and "Ck_on k g U" and "\<And>y. y \<in> U \<Longrightarrow> g y \<noteq> 0"
  shows "Ck_on k (\<lambda>y. f y / g y) U"
proof -
  have inv_g: "Ck_on k (\<lambda>y. inverse (g y)) U"
    by (rule Ck_on_inverse[OF assms(2,3)])
  have "Ck_on k (\<lambda>y. f y * inverse (g y)) U"
    by (rule Ck_on_mult[OF assms(1) inv_g])
  thus ?thesis by (simp add: divide_inverse)
qed

lemma Ck_on_inner:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y \<bullet> g y) U"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have hg: "higher_differentiable_on U g k"
    using assms(2) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U (\<lambda>y. f y \<bullet> g y) k"
    using hf hg oU by (rule higher_differentiable_on_inner)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_norm_sq:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. (norm (f y))\<^sup>2) U"
proof -
  have "Ck_on k (\<lambda>y. f y \<bullet> f y) U"
    by (rule Ck_on_inner[OF assms assms])
  thus ?thesis by (simp add: dot_square_norm)
qed

lemma Ck_on_compose:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
    and g :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "Ck_on k g V" and "Ck_on k f U" and "\<And>y. y \<in> U \<Longrightarrow> f y \<in> V"
  shows "Ck_on k (\<lambda>y. g (f y)) U"
proof -
  have oU: "open U"
    using assms(2) by (simp add: Ck_on_def)
  have oV: "open V"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(2) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have hg: "higher_differentiable_on V g k"
    using assms(1) oV by (simp add: Ck_on_iff_higher_differentiable_on)
  have fUV: "f ` U \<subseteq> V"
    using assms(3) by blast
  have "higher_differentiable_on U (g \<circ> f) k"
    by (rule higher_differentiable_on_compose[OF hg hf fUV oU oV])
  hence "higher_differentiable_on U (\<lambda>y. g (f y)) k"
    by (simp add: o_def)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_subset:
  assumes "Ck_on k f U" and "open V" and "V \<subseteq> U"
  shows "Ck_on k f V"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on V f k"
    using hf assms(3) by (rule higher_differentiable_on_subset)
  thus ?thesis
    using assms(2) by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_mono:
  assumes "Ck_on k f U" and "m \<le> k"
  shows "Ck_on m f U"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U f m"
    using hf assms(2) by (rule higher_differentiable_on_le)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed


(* ================================================================== *)
subsection \<open>Gradient for \<open>real\<^sup>n \<Rightarrow> real\<close>\<close>
(* ================================================================== *)

definition has_gradient ::
    "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n \<Rightarrow> bool"
    ("(GRAD (_)/ (_)/ :> (_))" [1000,1000,60] 60)
  where "GRAD f x :> g \<longleftrightarrow> (f has_derivative (\<lambda>v. v \<bullet> g)) (at x)"

lemma gradient_unique:
  "GRAD f x :> g \<Longrightarrow> GRAD f x :> g' \<Longrightarrow> g = g'"
  unfolding has_gradient_def
  by (metis has_derivative_unique vector_eq_ldot)

definition grad_fun :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n"
  ("\<nabla>")
  where "\<nabla> f x = (THE g :: real^'n. GRAD f x :> g)"

lemma grad_fun_eq:
  assumes "GRAD f x :> g"
  shows "\<nabla> f x = g"
  unfolding grad_fun_def using assms gradient_unique
  by (metis the_equality)

lemma grad_fun_satisfies_GRAD:
  assumes "GRAD f x :> g"
  shows "GRAD f x :> \<nabla> f x"
  using assms grad_fun_eq by blast

lemma has_derivative_to_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "(f has_derivative L) (at x)"
  shows "GRAD f x :> (\<Sum>i\<in>UNIV. L (axis i 1) *\<^sub>R axis i 1)"
proof -
  let ?g = "(\<Sum>i\<in>UNIV. L (axis i 1) *\<^sub>R axis i 1)"

  have bl: "bounded_linear L"
    using assms by (rule has_derivative_bounded_linear)

  have L_eq: "L = (\<lambda>v. v \<bullet> ?g)"
  proof
    fix v :: "real^'n"
    have v_exp: "v = (\<Sum>i\<in>UNIV. (v $ i) *\<^sub>R axis i 1)"
      by (metis (no_types) basis_expansion scalar_mult_eq_scaleR)
    then have "L v = L (\<Sum>i\<in>UNIV. (v $ i) *\<^sub>R axis i 1)"
      by simp
    also have "... = (\<Sum>i\<in>UNIV. L ((v $ i) *\<^sub>R axis i 1))"
      using bl bounded_linear.linear linear_sum by blast
    also have "... = (\<Sum>i\<in>UNIV. (v $ i) * L (axis i 1))"
      by (simp add: bl linear_simps(5))
    also have "... = v \<bullet> ?g"
      by (smt (verit, ccfv_SIG) Finite_Cartesian_Product.sum_cong_aux inner_axis
          inner_commute inner_real_def inner_scaleR_right inner_sum_right real_inner_1_right)
    finally show "L v = v \<bullet> ?g".
  qed
  have "(f has_derivative (\<lambda>v. v \<bullet> ?g)) (at x)"
    using assms L_eq by simp
  then show ?thesis
    unfolding has_gradient_def.
qed

lemma frechet_eq_inner_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "(f has_derivative L) (at x)" and "GRAD f x :> \<nabla> f x"
  shows "L v = v \<bullet> \<nabla> f x"
  using assms has_derivative_unique has_gradient_def by blast

text \<open>
  Differentiability of \<open>f :: real\<^sup>n \<Rightarrow> real\<close> implies the gradient exists.
  This connects @{const k_times_Fr_differentiable_at} at level 1 to the
  gradient.
\<close>

lemma Fr_diff_imp_gradient_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "f differentiable (at x)"
  shows "\<exists>g. GRAD f x :> g"
  using assms unfolding differentiable_def by (blast intro: has_derivative_to_gradient)


(* ================================================================== *)
subsection \<open>Hessian for \<open>real\<^sup>n \<Rightarrow> real\<close>\<close>
(* ================================================================== *)

text \<open>
  The (1-d) second derivative predicate, retained for backward compatibility
  with the 1-d theory.
\<close>

definition has_hessian_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
    ("(HDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where "HDERIV f x :> H \<longleftrightarrow> (deriv f has_derivative (\<lambda>h. h * H)) (at x)"

text \<open>
  The multi-dimensional Hessian: the Fréchet derivative of the gradient,
  represented as a matrix.
\<close>

definition has_hessian ::
    "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n^'n \<Rightarrow> bool"
    ("(HESS (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where "HESS f x :> H \<longleftrightarrow> (\<nabla> f has_derivative (\<lambda>v. H *v v)) (at x)"

lemma hessian_unique:
  "HESS f x :> H \<Longrightarrow> HESS f x :> H' \<Longrightarrow> H = H'"
  unfolding has_hessian_def
  by (metis has_derivative_unique matrix_eq)

definition hess_fun :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  ("\<nabla>\<^sup>2")
  where "\<nabla>\<^sup>2 f x = (THE H :: real^'n^'n. HESS f x :> H)"

lemma hess_fun_eq:
  assumes "HESS f x :> H"
  shows "\<nabla>\<^sup>2 f x = H"
  unfolding hess_fun_def using assms hessian_unique
  by (metis the_equality)

lemma hessian_eq_jacobian_of_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "HESS f x :> H"
  shows "H = matrix (frechet_derivative (\<nabla> f) (at x))"
  by (metis assms frechet_derivative_at' has_hessian_def matrix_of_matrix_vector_mul)

text \<open>
  The Hessian entries are iterated partial derivatives:
  \<open>(\<nabla>\<^sup>2 f x) $ i $ j = \<partial>\<^sub>j (\<partial>\<^sub>i f) (x)\<close>.
\<close>

lemma hessian_eq_double_nabla:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "HESS f x :> \<nabla>\<^sup>2 f x"
  shows "\<forall>i j. \<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
proof (intro allI)
  fix i j
  have row_grad: "GRAD (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
  proof -
    have H: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f x)) (at x)"
      using assms unfolding has_hessian_def by simp
    have Hcomp: "((\<lambda>y. \<nabla> f y \<bullet> axis i 1) has_derivative
         (\<lambda>v. ((*v) (\<nabla>\<^sup>2 f x)) v \<bullet> axis i 1)) (at x within UNIV)"
      using H by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
                  auto simp: Basis_vec_def)
    have comp_fun:  "(\<lambda>y. \<nabla> f y \<bullet> axis i 1) = (\<lambda>y. \<nabla> f y $ i)"
      by (rule ext, simp add: cart_eq_inner_axis)
    have comp_deriv: "(\<lambda>v. ((*v) (\<nabla>\<^sup>2 f x)) v \<bullet> axis i 1) = (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x) $ i))"
      by (rule ext, simp add: inner_axis' inner_commute matrix_vector_mul_component)
    from Hcomp show ?thesis
      unfolding has_gradient_def by (simp add: comp_fun comp_deriv)
  qed
  hence "\<nabla> (\<lambda>y. \<nabla> f y $ i) x = (\<nabla>\<^sup>2 f x) $ i"
    by (rule grad_fun_eq)
  then show "\<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
    by simp
qed


(* ================================================================== *)
subsection \<open>Connecting \<open>C\<^sup>k\<close> to the Hessian\<close>
(* ================================================================== *)

text \<open>
  These bridge lemmas connect the abstract \<open>C\<^sup>k\<close> notion to the concrete
  gradient/Hessian machinery.  They are the missing link in the existing
  development.
\<close>

lemma Ck_2_imp_gradient_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U" and "x \<in> U"
  shows "\<exists>g. GRAD f x :> g"
proof -
  from assms have "Ck_at 2 f x"
    by (simp add: Ck_on_def)
  then have "f differentiable (at x)"
    by (metis Ck_at.simps(2) Suc_1)
  then show ?thesis
    by (rule Fr_diff_imp_gradient_exists)
qed

lemma Ck_2_imp_hessian_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U" and "x \<in> U"
  shows "HESS f x :> \<nabla>\<^sup>2 f x"
proof -
  from assms have C2: "Ck_at 2 f x"
    by (simp add: Ck_on_def)

  then obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at 1 f y"
    and diffx: "f differentiable (at x)"
    and D: "\<forall>v. Ck_at 1 (\<lambda>y. frechet_derivative f (at y) v) x"
    by (metis Ck_at.simps(2) Suc_1)

  let ?H = "(\<chi> i. \<nabla> (\<lambda>y. \<nabla> f y $ i) x)"

  have H_wit: "HESS f x :> ?H"
  proof (unfold has_hessian_def)
    have comp: "\<forall>i\<in>Basis. ((\<lambda>y. \<nabla> f y \<bullet> i) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> i)) (at x)"
    proof clarify
      fix b :: "real^'n"
      assume b: "b \<in> Basis"
      then obtain i where i: "b = axis i 1"
        by (auto simp: Basis_vec_def)

      let ?Fi = "(\<lambda>y. frechet_derivative f (at y) (axis i 1))"
      let ?Gi = "(\<lambda>y. \<nabla> f y $ i)"

      have Fi_C1: "Ck_at 1 ?Fi x"
        using D by blast
      hence Fi_diff: "?Fi differentiable (at x)"
        by simp

      have eqA: "\<And>y. y \<in> A \<Longrightarrow> ?Fi y = ?Gi y"
        by (metis (lifting) A(3) Ck_at.simps(2) Fr_diff_imp_gradient_exists Suc_eq_plus1 add_0
            frechet_derivative_at grad_fun_eq has_gradient_def inner_axis' inner_real_def lambda_one)


      have ev_eq: "eventually (\<lambda>y. ?Fi y = ?Gi y) (nhds x)"
      proof -
        have "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>y\<in>S. ?Fi y = ?Gi y)"
          using A eqA by blast
        then show ?thesis
          by (simp add: eventually_nhds)
      qed

      have Gi_diff: "?Gi differentiable (at x)"
        by (metis (no_types, lifting) A(1,2) Fi_diff differentiable_eqI eqA)


      from Fr_diff_imp_gradient_exists[OF Gi_diff]
      obtain gi where gi: "GRAD ?Gi x :> gi"
        by blast

      have gradGi: "GRAD ?Gi x :> \<nabla> ?Gi x"
        using gi by (rule grad_fun_satisfies_GRAD)

      have dGi: "(?Gi has_derivative (\<lambda>v. v \<bullet> (?H $ i))) (at x)"
        using gradGi unfolding has_gradient_def by simp

      have "((\<lambda>y. \<nabla> f y \<bullet> b) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> b)) (at x)"
        by (metis (no_types, lifting) ext cart_eq_inner_axis dGi i
            inner_commute matrix_vector_mul_component)
      then show "((\<lambda>y. \<nabla> f y \<bullet> b) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> b)) (at x)".
    qed

    then show "(\<nabla> f has_derivative (*v) ?H) (at x)"
      using has_derivative_componentwise_within by blast
  qed
  show ?thesis
    using H_wit hess_fun_eq by fastforce
qed

lemma Ck_2_imp_hessian_continuous:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U"
  shows "continuous_on U (\<nabla>\<^sup>2 f)"
proof -
  have openU: "open U"
    using assms by (simp add: Ck_on_def)

  have comp_cont: "\<And>x i j. x \<in> U \<Longrightarrow> continuous (at x) (\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j)"
  proof -
    fix x i j
    assume xU: "x \<in> U"

    from assms xU have C2x: "Ck_at 2 f x"
      by (simp add: Ck_on_def)

    from C2x obtain A where
      A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at 1 f y"
      and diffx: "f differentiable (at x)"
      and Dx: "\<forall>v. Ck_at 1 (\<lambda>y. frechet_derivative f (at y) v) x"
      by (metis Ck_at.simps(2) Suc_1)

    let ?Fi = "(\<lambda>y. frechet_derivative f (at y) (axis i 1))"
    let ?K  = "(\<lambda>y. frechet_derivative ?Fi (at y) (axis j 1))"
    let ?Hc = "(\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j)"

    have Fi_C1: "Ck_at 1 ?Fi x"
      using Dx by simp

    have K_cont: "continuous (at x) ?K"
      using Fi_C1 by simp

    have eq_on_U: "\<And>y. y \<in> U \<Longrightarrow> frechet_derivative ?Fi (at y) (axis j 1) = \<nabla>\<^sup>2 f y $ i $ j"
    proof -
      fix y
      assume yU: "y \<in> U"

      from assms yU have C2y: "Ck_at 2 f y"
        by (simp add: Ck_on_def)

      have dy: "f differentiable (at y)"
        by (metis C2y Ck_at.simps(2) Suc_1)

      have Fi_C1_y: "Ck_at 1 ?Fi y"
        using C2y by (metis Ck_at.simps(2) Suc_1)

      have Fi_diff_y: "?Fi differentiable (at y)"
        using Fi_C1_y by simp

      let ?Gi = "(\<lambda>z. \<nabla> f z $ i)"

      have FG_eq_on_U: "\<And>z. z \<in> U \<Longrightarrow> ?Fi z = ?Gi z"
      proof -
        fix z
        assume zU: "z \<in> U"

        from assms zU have C2z: "Ck_at 2 f z"
          by (simp add: Ck_on_def)

        have dz: "f differentiable (at z)"
          by (metis C2z Ck_at.simps(2) Suc_1)

        from Fr_diff_imp_gradient_exists[OF dz]
        obtain g where g: "GRAD f z :> g"
          by blast
        have g_eq: "\<nabla> f z = g"
          using g by (rule grad_fun_eq)
        have "(f has_derivative (\<lambda>v. v \<bullet> g)) (at z)"
          using g unfolding has_gradient_def by simp
        hence fd_eq: "frechet_derivative f (at z) = (\<lambda>v. v \<bullet> g)"
          by (metis frechet_derivative_at)
        show "?Fi z = ?Gi z"
          by (simp add: fd_eq g_eq inner_axis')
      qed

      have ev_FG: "eventually (\<lambda>z. ?Fi z = ?Gi z) (nhds y)"
        using FG_eq_on_U eventually_nhds openU yU by blast


      have Gi_diff_y: "?Gi differentiable (at y)"
        by (metis (no_types, lifting) FG_eq_on_U Fi_diff_y differentiable_eqI openU yU)


      then have fd_Fi_Gi: "frechet_derivative ?Fi (at y) = frechet_derivative ?Gi (at y)"
        by (smt (verit, best) FG_eq_on_U frechet_derivative_transform_within_open openU yU)

      from Fr_diff_imp_gradient_exists[OF Gi_diff_y]
      obtain gi where gi: "GRAD ?Gi y :> gi"
        by blast

      have gi_eq: "\<nabla> ?Gi y = gi"
        using gi by (rule grad_fun_eq)

      have "(?Gi has_derivative (\<lambda>v. v \<bullet> gi)) (at y)"
        using gi unfolding has_gradient_def by simp
      hence fd_Gi: "frechet_derivative ?Gi (at y) = (\<lambda>v. v \<bullet> gi)"
        by (metis frechet_derivative_at)

      have fd_Gi_axis: "frechet_derivative ?Gi (at y) (axis j 1) = \<nabla> ?Gi y $ j"
        by (metis cart_eq_inner_axis fd_Gi gi_eq inner_commute)
      have Hess_y: "HESS f y :> \<nabla>\<^sup>2 f y"
        using assms yU by (rule Ck_2_imp_hessian_exists)

      have hess_eq: "\<nabla>\<^sup>2 f y $ i $ j = \<nabla> ?Gi y $ j"
        using hessian_eq_double_nabla[OF Hess_y] by simp

      show "frechet_derivative ?Fi (at y) (axis j 1) = \<nabla>\<^sup>2 f y $ i $ j"
        using fd_Fi_Gi fd_Gi_axis hess_eq by simp
    qed
    have ev_eq: "eventually (\<lambda>y. ?K y = ?Hc y) (nhds x)"
      using eq_on_U eventually_nhds openU xU by blast
    show "continuous (at x) ?Hc"
      using K_cont ev_eq isCont_cong by fastforce
  qed

  show ?thesis
    unfolding continuous_on
  proof
    fix x
    assume xU: "x \<in> U"

    have isCont_H: "isCont (\<lambda>y. \<chi> i. \<chi> j. \<nabla>\<^sup>2 f y $ i $ j) x"
      unfolding isCont_def
    proof (rule tendsto_vec_lambda)
      fix i
      show "((\<lambda>y. \<chi> j. \<nabla>\<^sup>2 f y $ i $ j) \<longlongrightarrow> (\<chi> j. \<nabla>\<^sup>2 f x $ i $ j)) (at x)"
      proof (rule tendsto_vec_lambda)
        fix j
        from comp_cont[OF xU, of i j]
        show "((\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j) \<longlongrightarrow> \<nabla>\<^sup>2 f x $ i $ j) (at x)"
          unfolding isCont_def by simp
      qed
    qed
    then have "continuous (at x) (\<nabla>\<^sup>2 f)"
      by simp
    then show "(\<nabla>\<^sup>2 f \<longlongrightarrow> \<nabla>\<^sup>2 f x) (at x within U)"
      by (metis at_within_open continuous_within openU xU)
  qed
qed

text \<open>
  The ad-hoc predicate \<open>C2_on_vec\<close> from the earlier development is
  now derivable from \<open>Ck_on 2 f U\<close>.
\<close>

definition C2_on_vec ::
  "(real^'n::finite \<Rightarrow> real) \<Rightarrow> (real^'n) set \<Rightarrow> bool"
where
  "C2_on_vec f U \<longleftrightarrow> (\<forall>y\<in>U. HESS f y :> \<nabla>\<^sup>2 f y) \<and> continuous_on U (\<nabla>\<^sup>2 f)"

lemma Ck_2_imp_C2_on_vec:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U"
  shows "C2_on_vec f U"
  unfolding C2_on_vec_def
  using Ck_2_imp_hessian_exists Ck_2_imp_hessian_continuous assms
  by blast


(* ================================================================== *)
subsection \<open>Clairaut's theorem (Symmetry of mixed partials)\<close>
(* ================================================================== *)

text \<open>
  If \<open>f :: real\<^sup>n \<Rightarrow> real\<close> is \<open>C\<^sup>2\<close> on an open set \<open>U\<close>, then its Hessian
  is symmetric at every point of \<open>U\<close>.

  The hypothesis uses the general \<open>Ck_on\<close>, which subsumes both the
  1-d \<open>C_k_on\<close> and the ad-hoc \<open>C2_on_vec\<close>.
\<close>

lemma clairaut_scalar_R2:
  fixes \<Phi>  :: "real \<Rightarrow> real \<Rightarrow> real"
  fixes fx :: "real \<Rightarrow> real"
    and fy :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow>\<^sub>L real)"
  assumes fx:
    "((\<lambda>u. \<Phi> u y) has_derivative fx) (at x within X)"
  assumes fy:
    "\<And>u v. u \<in> X \<Longrightarrow> v \<in> Y \<Longrightarrow>
      ((\<lambda>v'. \<Phi> u v') has_derivative (blinfun_apply (fy u v))) (at v within Y)"
  assumes fy_cont:
    "continuous (at (x,y) within X \<times> Y) (\<lambda>(u,v). fy u v)"
  assumes yY: "y \<in> Y"
  assumes convY: "convex Y"
  shows
    "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty))
      (at (x,y) within X \<times> Y)"
proof -
  have "((\<lambda>(x,y). \<Phi> x y) has_derivative
          (\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty))
        (at (x,y) within X \<times> Y)"
    by (rule has_derivative_partialsI[OF fx fy fy_cont yY convY])
  then show ?thesis
    by (simp add: case_prod_unfold)
qed

lemma clairaut_scalar_R2_mixed_eq:
  fixes \<Phi>  :: "real \<Rightarrow> real \<Rightarrow> real"
  fixes fx :: "real \<Rightarrow> real"
    and fy :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow>\<^sub>L real)"
    and gy :: "real \<Rightarrow> real"
    and gx :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow>\<^sub>L real)"
  assumes fx:
    "((\<lambda>u. \<Phi> u y) has_derivative fx) (at x within X)"
  assumes fy:
    "\<And>u v. u \<in> X \<Longrightarrow> v \<in> Y \<Longrightarrow>
      ((\<lambda>v'. \<Phi> u v') has_derivative (blinfun_apply (fy u v))) (at v within Y)"
  assumes fy_cont:
    "continuous (at (x,y) within X \<times> Y) (\<lambda>(u,v). fy u v)"
  assumes gy:
    "((\<lambda>v. \<Phi> x v) has_derivative gy) (at y within Y)"
  assumes gx:
    "\<And>v u. v \<in> Y \<Longrightarrow> u \<in> X \<Longrightarrow>
      ((\<lambda>u'. \<Phi> u' v) has_derivative (blinfun_apply (gx v u))) (at u within X)"
  assumes gx_cont:
    "continuous (at (y,x) within Y \<times> X) (\<lambda>(v,u). gx v u)"
  assumes xX: "x \<in> X" and yY: "y \<in> Y"
  assumes openX: "open X" and openY: "open Y"
  assumes convX: "convex X" and convY: "convex Y"
  shows
    "(\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty) =
     (\<lambda>(tx,ty). blinfun_apply (gx y x) tx + gy ty)"
proof -
  have D1:
    "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty))
      (at (x,y) within X \<times> Y)"
    by (rule clairaut_scalar_R2[OF fx fy fy_cont yY convY])

  have Dswap:
    "((\<lambda>p. \<Phi> (snd p) (fst p)) has_derivative
        (\<lambda>(tv,tu). gy tv + blinfun_apply (gx y x) tu))
      (at (y,x) within Y \<times> X)"
  proof -
    have "((\<lambda>p. (\<lambda>v u. \<Phi> u v) (fst p) (snd p)) has_derivative
            (\<lambda>(tv,tu). gy tv + blinfun_apply (gx y x) tu))
          (at (y,x) within Y \<times> X)"
      by (rule clairaut_scalar_R2[
            where \<Phi> = "\<lambda>v u. \<Phi> u v"
              and fx = gy and fy = gx
              and x = y and X = Y and y = x and Y = X])
         (use gy gx gx_cont xX convX in auto)
    then show ?thesis
      by (simp add: case_prod_unfold)
  qed

  have bl_swap: "bounded_linear (\<lambda>(tx::real,ty::real). (ty,tx))"
    by (simp add: bounded_linear_Pair bounded_linear_fst bounded_linear_snd case_prod_unfold)

  have Dswap_map: "((\<lambda>(u::real,v::real). (v,u)) has_derivative (\<lambda>(tx,ty). (ty,tx)))
      (at (x,y) within X \<times> Y)"
    by (simp add: bl_swap bounded_linear_imp_has_derivative)
  have swap_image:
    "(\<lambda>(u::real,v::real). (v,u)) ` (X \<times> Y) = Y \<times> X"
    by auto

  have Dswap': "((\<lambda>p. \<Phi> (snd p) (fst p)) has_derivative
        (\<lambda>(tv,tu). gy tv + blinfun_apply (gx y x) tu))
      (at ((\<lambda>(u::real,v::real). (v,u)) (x,y))
          within ((\<lambda>(u::real,v::real). (v,u)) ` (X \<times> Y)))"
    using Dswap by (simp add: swap_image)

  have D2: "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). blinfun_apply (gx y x) tx + gy ty))
      (at (x,y) within X \<times> Y)"
  proof -
    have "(((\<lambda>p. \<Phi> (snd p) (fst p)) \<circ> (\<lambda>(u::real,v::real). (v,u)))
            has_derivative
            ((\<lambda>(tv,tu). gy tv + blinfun_apply (gx y x) tu)
              \<circ> (\<lambda>(tx,ty). (ty,tx))))
          (at (x,y) within X \<times> Y)"
      by (rule diff_chain_within[OF Dswap_map Dswap'])
    then show ?thesis
      by (simp add: o_def case_prod_unfold ac_simps)
  qed

  have D1_at: "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty)) (at (x,y))"
    by (metis (mono_tags, lifting) D1 SigmaI at_within_open openX openY open_Times xX yY)

  have D2_at: "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). blinfun_apply (gx y x) tx + gy ty))  (at (x,y))"
    by (metis (lifting) D2 Sigma_cong at_within_open mem_Sigma_iff openX openY open_Times xX yY)
  show ?thesis
    by (rule has_derivative_unique[OF D1_at D2_at])
qed


(* The rectangle argument:                                             *)
(*   \<Delta>(h,k) = f(x+h\<sqdot>eᵢ+k\<sqdot>eⱼ) - f(x+h\<sqdot>eᵢ) - f(x+k\<sqdot>eⱼ) + f(x)     *)
(*                                                                     *)
(*   By MVT in s then t:  \<Delta> = h\<sqdot>k\<sqdot>(\<nabla>²f z₁)$i$j                       *)
(*   By MVT in t then s:  \<Delta> = h\<sqdot>k\<sqdot>(\<nabla>²f z₂)$j$i                       *)
(*   where z₁,z₂ \<rightarrow> x as h,k \<rightarrow> 0.                                     *)
(*   By continuity of \<nabla>²f, both Hessian entries equal at x.           *)
(* ================================================================== *)

lemma mixed_coordinate_second_derivative_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes openU: "open U"
      and xU: "x \<in> U"
      and C2: "Ck_on 2 f U"
  shows "(\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
proof -
  (* ---------- 0.  Notation ---------- *)
  let ?ei = "axis i 1 :: real^'n"
  let ?ej = "axis j 1 :: real^'n"

  (* ---------- 1.  Work inside a ball ---------- *)
  obtain r where r_pos: "r > 0" and rU: "ball x r \<subseteq> U"
    using openU xU by (meson open_contains_ball)

  define \<delta> where "\<delta> = r / 4"
  have \<delta>_pos: "\<delta> > 0" using r_pos by (simp add: \<delta>_def)

  (* Any point x + s\<sqdot>eᵢ + t\<sqdot>eⱼ with |s|,|t| < \<delta> lies in U. *)
  have inU: "\<lbrakk> \<bar>s\<bar> < \<delta>; \<bar>t\<bar> < \<delta> \<rbrakk> \<Longrightarrow> x + s *\<^sub>R ?ei + t *\<^sub>R ?ej \<in> U" for s t
  proof -
    assume s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>"
    have "norm (s *\<^sub>R ?ei + t *\<^sub>R ?ej) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
      by (simp add: norm_triangle_le)
    also have "\<dots> < \<delta> + \<delta>" using s_bd t_bd by linarith
    also have "\<dots> = r / 2" by (simp add: \<delta>_def)
    also have "\<dots> < r" using r_pos by linarith
    finally show "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej \<in> U"
      by (metis (no_types, lifting) add.assoc basic_trans_rules(31)
          dist_0_norm dist_add_cancel group_cancel.rule0 mem_ball rU)
  qed

  (* ---------- 2.  Names for partial derivatives ---------- *)
  (* Ps(s,t) = \<partial>ᵢf at x + s\<sqdot>eᵢ + t\<sqdot>eⱼ *)
  define Ps where "Ps s t = \<nabla> f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej) $ i" for s t
  (* Qt(s,t) = \<partial>ⱼf at x + s\<sqdot>eᵢ + t\<sqdot>eⱼ *)
  define Qt where "Qt s t = \<nabla> f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej) $ j" for s t

  (* ---------- 3.  Basic differentiability facts ---------- *)
  have diff_at: "f differentiable (at z)" if "z \<in> U" for z
    by (metis Ck_at.simps(2) Ck_on_def Suc_1 C2 that)

  have grad_exists: "GRAD f z :> \<nabla> f z" if "z \<in> U" for z
    using Fr_diff_imp_gradient_exists[OF diff_at[OF that]]
      grad_fun_satisfies_GRAD by blast

  have Hess_exists: "HESS f z :> \<nabla>\<^sup>2 f z" if "z \<in> U" for z
    using C2 that by (rule Ck_2_imp_hessian_exists)

  have hcont: "continuous_on U (\<nabla>\<^sup>2 f)"
    using C2 by (rule Ck_2_imp_hessian_continuous)

  (* ---------- 4.  Row-gradient lemma ---------- *)
  (* GRAD (\<lambda>y. \<nabla> f y $ k) z :> (\<nabla>²f z) $ k  for z \<in> U *)
  have row_grad: "GRAD (\<lambda>y. \<nabla> f y $ k) z :> (\<nabla>\<^sup>2 f z) $ k"
    if zU: "z \<in> U" for z k
  proof -
    have H: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f z)) (at z)"
      using Hess_exists[OF zU] unfolding has_hessian_def .
    have "((\<lambda>y. \<nabla> f y \<bullet> axis k 1) has_derivative
         (\<lambda>v. ((*v) (\<nabla>\<^sup>2 f z)) v \<bullet> axis k 1)) (at z within UNIV)"
      using H by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
                  auto simp: Basis_vec_def)
    thus ?thesis
      unfolding has_gradient_def
      by (simp add: inner_axis' inner_commute matrix_vector_mul_component)
  qed

  (* ---------- 5.  Derivatives of the slice maps ---------- *)
  (* \<partial>/\<partial>s [Ps(s,t)] = (\<nabla>²f)$i$i  and  \<partial>/\<partial>t [Ps(s,t)] = (\<nabla>²f)$i$j *)

  have Ps_has_deriv_t:
    "((\<lambda>t'. Ps s t') has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j)
       (at t)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have rg: "GRAD (\<lambda>y. \<nabla> f y $ i) ?z :> (\<nabla>\<^sup>2 f ?z) $ i"
      by (rule row_grad[OF zU])
    have fd: "((\<lambda>y. \<nabla> f y $ i) has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))) (at ?z)"
      using rg unfolding has_gradient_def .
    have lin: "((\<lambda>t'. x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) has_derivative (\<lambda>dt. dt *\<^sub>R ?ej)) (at t)"
      by (intro derivative_eq_intros) auto
    have chain:
      "((\<lambda>t'. \<nabla> f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) $ i) has_derivative
         (\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))) (at t)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))
        = (\<lambda>dt. dt * ((\<nabla>\<^sup>2 f ?z) $ i $ j))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Ps_def has_field_derivative_def
      by (simp add: mult_commute_abs)
  qed

  have Qt_has_deriv_s:
    "((\<lambda>s'. Qt s' t) has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i)
       (at s)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have rg: "GRAD (\<lambda>y. \<nabla> f y $ j) ?z :> (\<nabla>\<^sup>2 f ?z) $ j"
      by (rule row_grad[OF zU])
    have fd: "((\<lambda>y. \<nabla> f y $ j) has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))) (at ?z)"
      using rg unfolding has_gradient_def .
    have lin: "((\<lambda>s'. x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) has_derivative (\<lambda>ds. ds *\<^sub>R ?ei)) (at s)"
      by (intro derivative_eq_intros) auto
    have chain:
      "((\<lambda>s'. \<nabla> f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) $ j) has_derivative
         (\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))) (at s)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))
        = (\<lambda>ds. ds * ((\<nabla>\<^sup>2 f ?z) $ j $ i))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Qt_def has_field_derivative_def
      by (metis (no_types, lifting) ext mult.commute)
  qed

  (* Similarly for \<partial>/\<partial>s [\<Phi>(s,t)] and \<partial>/\<partial>t [\<Phi>(s,t)] *)
  have Phi_has_deriv_s: "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej)) has_real_derivative Ps s t) (at s)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have fd: "(f has_derivative (\<lambda>v. v \<bullet> \<nabla> f ?z)) (at ?z)"
      using grad_exists[OF zU] unfolding has_gradient_def .
    have lin: "((\<lambda>s'. x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) has_derivative (\<lambda>ds. ds *\<^sub>R ?ei)) (at s)"
      by (intro derivative_eq_intros) auto
    have chain: "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej)) has_derivative
         (\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> \<nabla> f ?z)) (at s)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> \<nabla> f ?z) = (\<lambda>ds. ds * (\<nabla> f ?z $ i))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Ps_def has_field_derivative_def
      by (metis (full_types, lifting) ext mult.commute)
  qed

  have Phi_has_deriv_t: "((\<lambda>t'. f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt s t) (at t)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have fd: "(f has_derivative (\<lambda>v. v \<bullet> \<nabla> f ?z)) (at ?z)"
      using grad_exists[OF zU] unfolding has_gradient_def .
    have lin: "((\<lambda>t'. x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) has_derivative (\<lambda>dt. dt *\<^sub>R ?ej)) (at t)"
      by (intro derivative_eq_intros) auto
    have chain: "((\<lambda>t'. f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_derivative
         (\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> \<nabla> f ?z)) (at t)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> \<nabla> f ?z) = (\<lambda>dt. dt * (\<nabla> f ?z $ j))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Qt_def has_field_derivative_def
      by (metis (full_types, lifting) ext mult.commute)
  qed


  (* ---------- 6.  Continuity of the relevant Hessian entries ---------- *)


  (* For the \<epsilon>-\<delta> argument we only need: *)
  have Hij_cont_at_0:
    "\<forall>\<epsilon>>0. \<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
       \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
  proof -
    have cont_comp: "isCont (\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j) (0,0)"
    proof -
      have cont_hij: "continuous_on U (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j)"
        using hcont by (simp add: continuous_on_component)
      have isCont_hij: "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j) x"
        using cont_hij openU xU continuous_on_eq_continuous_at by blast
      have isCont_slice: "isCont (\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real)"
        by (intro continuous_intros)
      have at_zero: "(\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real) = x"
        by simp
      have "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j)
              ((\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0, 0))"
        using isCont_hij by (simp add: at_zero)
      thus ?thesis
        by (rule isCont_o2[OF isCont_slice])
    qed
    show ?thesis
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume eps: "\<epsilon> > 0"

      (* Step 1: unfold isCont to tendsto, then to eventually_at *)
      from cont_comp
      have "((\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j) \<longlongrightarrow>
              (\<nabla>\<^sup>2 f x) $ i $ j) (at (0,0))"
        unfolding isCont_def by simp

      (* Step 2: instantiate tendsto_iff at \<epsilon> *)
      from this[unfolded tendsto_iff] eps
      have "eventually (\<lambda>p. dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j)
                                  ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>) (at (0,0))"
        by simp

      (* Step 3: unfold eventually_at to get r'' with the p \<noteq> (0,0) guard *)
      then obtain r'' where r''_pos: "r'' > 0"
        and r''_bd: "\<forall>p. p \<noteq> (0::real, 0::real) \<and> dist p (0,0) < r'' \<longrightarrow>
             dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j)
                  ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>"
        unfolding eventually_at by auto

      (* Step 4: extend to ALL p by case-splitting on p = (0,0) *)
      define \<delta>' where "\<delta>' = min \<delta> (r'' / 2)"
      have "\<delta>' > 0" using \<delta>_pos r''_pos by (simp add: \<delta>'_def)
      moreover have "\<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
         (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix s t assume st: "\<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>'"
        show "\<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
               (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
        proof (cases "s = 0 \<and> t = 0")
          case True
          then show ?thesis using eps by simp
        next
          case False
          then have "(s, t) \<noteq> (0::real, 0::real)" by auto
          moreover have "dist (s,t) (0::real, 0::real) < r''"
          proof -
            have "dist (s,t) (0::real, 0::real) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
              using sqrt_sum_squares_le_sum_abs by (simp add: dist_Pair_Pair)
            also have "\<dots> < r''" using st by (simp add: \<delta>'_def)
            finally show ?thesis.
          qed
          ultimately have "dist ((\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j)
                                ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>"
            using r''_bd by auto
          thus ?thesis by (simp add: dist_real_def)
        qed
      qed
      ultimately show "\<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
         (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
        by blast
    qed
  qed

  have Hji_cont_at_0:
  "\<forall>\<epsilon>>0. \<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
     \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
  proof -
    have cont_comp: "isCont (\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i) (0,0)"
    proof -
      have cont_hji: "continuous_on U (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i)"
        using hcont by (simp add: continuous_on_component)
      have isCont_hji: "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i) x"
        using cont_hji openU xU continuous_on_eq_continuous_at by blast
      have isCont_slice: "isCont (\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real)"
        by (intro continuous_intros)
      have at_zero: "(\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real) = x"
        by simp
      have "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i)
              ((\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0, 0))"
        using isCont_hji by (simp add: at_zero)
      thus ?thesis
        by (rule isCont_o2[OF isCont_slice])
    qed
    show ?thesis
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume eps: "\<epsilon> > 0"

      from cont_comp
      have "((\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i) \<longlongrightarrow>
              (\<nabla>\<^sup>2 f x) $ j $ i) (at (0,0))"
        unfolding isCont_def by simp

      from this[unfolded tendsto_iff] eps
      have "eventually (\<lambda>p. dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i)
                                  ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>) (at (0,0))"
        by simp

      then obtain r'' where r''_pos: "r'' > 0"
        and r''_bd: "\<forall>p. p \<noteq> (0::real, 0::real) \<and> dist p (0,0) < r'' \<longrightarrow>
             dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i)
                  ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>"
        unfolding eventually_at by auto

      define \<delta>' where "\<delta>' = min \<delta> (r'' / 2)"
      have "\<delta>' > 0"
        using \<delta>_pos r''_pos by (simp add: \<delta>'_def)
      moreover have "\<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
         (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix s t
        assume st: "\<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>'"
        show "\<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
               (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
        proof (cases "s = 0 \<and> t = 0")
          case True
          then show ?thesis
            using eps by simp
        next
          case False
          then have "(s, t) \<noteq> (0::real, 0::real)"
            by auto
          moreover have "dist (s,t) (0::real, 0::real) < r''"
          proof -
            have "dist (s,t) (0::real, 0::real) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
              using sqrt_sum_squares_le_sum_abs by (simp add: dist_Pair_Pair)
            also have "\<dots> < r''"
              using st by (simp add: \<delta>'_def)
            finally show ?thesis .
          qed
          ultimately have "dist ((\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i)
                                ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>"
            using r''_bd by auto
          thus ?thesis
            by (simp add: dist_real_def)
        qed
      qed
      ultimately show "\<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
         (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
        by blast
    qed
  qed


  (* ---------- 7.  The rectangle increment ---------- *)
  define \<Delta> where
    "\<Delta> h k = f (x + h *\<^sub>R ?ei + k *\<^sub>R ?ej)
           - f (x + h *\<^sub>R ?ei)
           - f (x + k *\<^sub>R ?ej)
           + f x" for h k

  (* ---------- 8.  MVT, direction 1: differentiate in s first, then t ---------- *)
  (*
     g(s) = f(x + s\<sqdot>eᵢ + k\<sqdot>eⱼ) - f(x + s\<sqdot>eᵢ)
     g(h) - g(0) = \<Delta>(h,k)
     By MVT: \<exists> \<xi> between 0 and h.  \<Delta>(h,k) = h \<sqdot> g'(\<xi>)
     g'(s) = Ps(s,k) - Ps(s,0)
     Then p(t) = Ps(\<xi>,t), and p(k) - p(0) = g'(\<xi>) = Ps(\<xi>,k) - Ps(\<xi>,0)
     By MVT on p: \<exists> \<eta> between 0 and k.
       Ps(\<xi>,k) - Ps(\<xi>,0) = k \<sqdot> (\<nabla>²f(x + \<xi>\<sqdot>eᵢ + \<eta>\<sqdot>eⱼ))$i$j
     So \<Delta>(h,k) = h \<sqdot> k \<sqdot> (\<nabla>²f(x + \<xi>\<sqdot>eᵢ + \<eta>\<sqdot>eⱼ))$i$j
  *)
  have dir1:
    "\<exists>\<xi> \<eta>. \<bar>\<xi>\<bar> \<le> \<bar>h\<bar> \<and> \<bar>\<eta>\<bar> \<le> \<bar>k\<bar> \<and>
            \<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
    if h_pos: "h > 0" and k_pos: "k > 0"
       and h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
    for h k
  proof -
    (* g(s) = f(x + s\<sqdot>eᵢ + k\<sqdot>eⱼ) - f(x + s\<sqdot>eᵢ) *)
    define g where "g s = f (x + s *\<^sub>R ?ei + k *\<^sub>R ?ej) - f (x + s *\<^sub>R ?ei)" for s

    have g_deriv: "(g has_real_derivative (Ps s k - Ps s 0)) (at s)"
      if "\<bar>s\<bar> < \<delta>" for s
    proof -
      have "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + k *\<^sub>R ?ej)) has_real_derivative Ps s k) (at s)"
        using Phi_has_deriv_s[of s k] that k_bd k_pos by linarith
      moreover have "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + 0 *\<^sub>R ?ej)) has_real_derivative Ps s 0) (at s)"
        using Phi_has_deriv_s[of s 0] that \<delta>_pos by auto
      ultimately show ?thesis
        unfolding g_def
        by (subst derivative_eq_intros, simp_all)
    qed

    (* Apply MVT to g on [0,h] *)
    have g_deriv_on_seg: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> h \<Longrightarrow> (g has_real_derivative (Ps x k - Ps x 0)) (at x)"
    proof -
      fix x :: real
      assume x0: "0 \<le> x"
      assume xh: "x \<le> h"
      have "\<bar>x\<bar> = x"
        using x0 by simp
      also have "... \<le> h"
        using xh by simp
      also have "... < \<delta>"
        using h_bd by simp
      finally have "\<bar>x\<bar> < \<delta>" .
      thus "(g has_real_derivative (Ps x k - Ps x 0)) (at x)"
        by (rule g_deriv)
    qed

    have g_diff: "\<exists>\<xi>. 0 < \<xi> \<and> \<xi> < h \<and> \<Delta> h k = h * (Ps \<xi> k - Ps \<xi> 0)"
    proof -
      obtain \<xi> where \<xi>:
        "0 < \<xi>" "\<xi> < h"
        "g h - g 0 = (h - 0) * (Ps \<xi> k - Ps \<xi> 0)"
        using MVT2[of 0 h g "\<lambda>x. Ps x k - Ps x 0"]
          h_pos g_deriv_on_seg
        by blast
      have "g h - g 0 = \<Delta> h k"
        by (simp add: g_def \<Delta>_def)
      with \<xi> show ?thesis
        by auto
    qed
    then obtain \<xi> where \<xi>_pos: "0 < \<xi>" and \<xi>_lt: "\<xi> < h"
      and eq1: "\<Delta> h k = h * (Ps \<xi> k - Ps \<xi> 0)" by blast

    (* Now apply MVT to p(t) = Ps(\<xi>,t) on [0,k] *)
    define p where "p t = Ps \<xi> t" for t

    have p_deriv: "(p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
      if "\<bar>t\<bar> < \<delta>" for t
      using Ps_has_deriv_t[of \<xi> t] \<xi>_lt h_bd that
      unfolding p_def
      using \<xi>_pos by argo


    (* MVT application to p on [0,k] *)
    have p_deriv_on_seg: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> k \<Longrightarrow>
       (p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
    proof -
      fix t :: real
      assume t0: "0 \<le> t"
      assume tk: "t \<le> k"
      have "\<bar>t\<bar> = t"
        using t0 by simp
      also have "... \<le> k"
        using tk by simp
      also have "... < \<delta>"
        using k_bd by simp
      finally have "\<bar>t\<bar> < \<delta>".
      thus "(p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
        by (rule p_deriv)
    qed

    have p_diff: "\<exists>\<eta>. 0 < \<eta> \<and> \<eta> < k \<and>
        Ps \<xi> k - Ps \<xi> 0 = k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
    proof -
      obtain \<eta> where \<eta>:
        "0 < \<eta>"
        "\<eta> < k"
        "p k - p 0 = (k - 0) * ((\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j)"
        using MVT2[of 0 k p "\<lambda>t. (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j"] k_pos p_deriv_on_seg
        by blast
      have "p k - p 0 = Ps \<xi> k - Ps \<xi> 0"
        unfolding p_def by simp
      with \<eta> show ?thesis
        by auto
    qed
    then obtain \<eta> where \<eta>_pos: "0 < \<eta>" and \<eta>_lt: "\<eta> < k"
      and eq2: "Ps \<xi> k - Ps \<xi> 0 = k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      by blast

    have "\<Delta> h k = h * (k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j)"
      using eq1 eq2 by simp
    hence "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      by (simp add: mult.assoc)
    moreover have "\<bar>\<xi>\<bar> \<le> \<bar>h\<bar>" using \<xi>_pos \<xi>_lt h_pos by linarith
    moreover have "\<bar>\<eta>\<bar> \<le> \<bar>k\<bar>" using \<eta>_pos \<eta>_lt k_pos by linarith
    ultimately show ?thesis by blast
  qed

  (* ---------- 9.  MVT, direction 2: differentiate in t first, then s ---------- *)
  have dir2:
    "\<exists>\<xi>' \<eta>'. \<bar>\<xi>'\<bar> \<le> \<bar>h\<bar> \<and> \<bar>\<eta>'\<bar> \<le> \<bar>k\<bar> \<and>
              \<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
    if h_pos: "h > 0" and k_pos: "k > 0"
       and h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
    for h k
  proof -
    (* g̃(t) = f(x + h\<sqdot>eᵢ + t\<sqdot>eⱼ) - f(x + t\<sqdot>eⱼ) *)
    define g' where "g' t = f (x + h *\<^sub>R ?ei + t *\<^sub>R ?ej) - f (x + t *\<^sub>R ?ej)" for t

    have g'_deriv: "(g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
      if "\<bar>t\<bar> < \<delta>" for t
    proof -
      have "((\<lambda>t'. f (x + h *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt h t) (at t)"
        using Phi_has_deriv_t[of h t] h_bd that
        using h_pos by linarith
      moreover have "((\<lambda>t'. f (x + 0 *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt 0 t) (at t)"
        using Phi_has_deriv_t[of 0 t] \<delta>_pos that by auto
      ultimately show ?thesis
        unfolding g'_def by (subst derivative_eq_intros, simp_all)
    qed

    (* MVT on g̃ over [0,k] *)
    have g'_diff: "\<exists>\<eta>'. 0 < \<eta>' \<and> \<eta>' < k \<and> \<Delta> h k = k * (Qt h \<eta>' - Qt 0 \<eta>')"
    proof -
      have "g' k - g' 0 = \<Delta> h k"
        by (simp add: g'_def \<Delta>_def)
      moreover have g'_deriv_on_seg:
        "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> k \<Longrightarrow> (g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
      proof -
        fix t :: real
        assume t0: "0 \<le> t"
        assume tk: "t \<le> k"
        have "\<bar>t\<bar> = t"
          using t0 by simp
        also have "... \<le> k"
          using tk by simp
        also have "... < \<delta>"
          using k_bd by simp
        finally have "\<bar>t\<bar> < \<delta>".
        thus "(g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
          by (rule g'_deriv)
      qed
      moreover obtain \<eta>' where "0 < \<eta>'" "\<eta>' < k"
        and "g' k - g' 0 = k * (Qt h \<eta>' - Qt 0 \<eta>')"
        using MVT2[of 0 k g' "\<lambda>t. Qt h t - Qt 0 t"] k_pos g'_deriv_on_seg
        by auto
      ultimately show ?thesis
        by auto
    qed

    then obtain \<eta>' where \<eta>'_pos: "0 < \<eta>'" and \<eta>'_lt: "\<eta>' < k"
      and eq1': "\<Delta> h k = k * (Qt h \<eta>' - Qt 0 \<eta>')" by blast

    (* MVT on q(s) = Qt(s, \<eta>') over [0,h] *)
    define q where "q s = Qt s \<eta>'" for s

    have q_deriv_on_seg:
      "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> h \<Longrightarrow>
        (q has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i) (at s)"
    proof -
      fix s :: real
      assume s0: "0 \<le> s"
      assume sh: "s \<le> h"
      have "\<bar>s\<bar> = s"
        using s0 by simp
      also have "... \<le> h"
        using sh by simp
      also have "... < \<delta>"
        using h_bd by simp
      finally have "\<bar>s\<bar> < \<delta>" .
      thus "(q has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i) (at s)"
        using Qt_has_deriv_s \<eta>'_lt \<eta>'_pos \<open>q \<equiv> \<lambda>s. Qt s \<eta>'\<close> k_bd by fastforce
    qed

    have q_diff: "\<exists>\<xi>'. 0 < \<xi>' \<and> \<xi>' < h \<and>
        Qt h \<eta>' - Qt 0 \<eta>' = h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
    proof -
      obtain \<xi>' where \<xi>':
        "0 < \<xi>'"
        "\<xi>' < h"
        "q h - q 0 = (h - 0) * ((\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i)"
        using MVT2[of 0 h q "\<lambda>s. (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"] h_pos q_deriv_on_seg
        by blast
      have "q h - q 0 = Qt h \<eta>' - Qt 0 \<eta>'"
        unfolding q_def by simp
      with \<xi>' show ?thesis
        by auto
    qed
    then obtain \<xi>' where \<xi>'_pos: "0 < \<xi>'" and \<xi>'_lt: "\<xi>' < h"
      and eq2': "Qt h \<eta>' - Qt 0 \<eta>' = h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      by blast

    have "\<Delta> h k = k * (h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i)"
      using eq1' eq2' by simp
    hence "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      by (simp add: mult.commute mult.assoc)
    moreover have "\<bar>\<xi>'\<bar> \<le> \<bar>h\<bar>" using \<xi>'_pos \<xi>'_lt h_pos by linarith
    moreover have "\<bar>\<eta>'\<bar> \<le> \<bar>k\<bar>" using \<eta>'_pos \<eta>'_lt k_pos by linarith
    ultimately show ?thesis by blast
  qed

  (* ---------- 10.  Combine: equality of Hessian entries ---------- *)
  have "(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla>\<^sup>2 f x) $ j $ i"
  proof (rule ccontr)
    assume neq: "(\<nabla>\<^sup>2 f x) $ i $ j \<noteq> (\<nabla>\<^sup>2 f x) $ j $ i"

    define \<epsilon> where "\<epsilon> = \<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> / 3"
    then have \<epsilon>_pos: "\<epsilon> > 0" using neq by simp

    (* By continuity, get \<delta>\<^sub>1 for the (i,j) entry and \<delta>\<^sub>2 for the (j,i) entry *)
    obtain \<delta>\<^sub>1 where \<delta>\<^sub>1_pos: "\<delta>\<^sub>1 > 0"
      and \<delta>\<^sub>1_bd: "\<forall>s t. \<bar>s\<bar> < \<delta>\<^sub>1 \<and> \<bar>t\<bar> < \<delta>\<^sub>1 \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      using Hij_cont_at_0 \<epsilon>_pos by blast

    obtain \<delta>\<^sub>2 where \<delta>\<^sub>2_pos: "\<delta>\<^sub>2 > 0"
      and \<delta>\<^sub>2_bd: "\<forall>s t. \<bar>s\<bar> < \<delta>\<^sub>2 \<and> \<bar>t\<bar> < \<delta>\<^sub>2 \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      using Hji_cont_at_0 \<epsilon>_pos by blast

    define \<delta>\<^sub>3 where "\<delta>\<^sub>3 = min \<delta> (min \<delta>\<^sub>1 \<delta>\<^sub>2)"
    have \<delta>\<^sub>3_pos: "\<delta>\<^sub>3 > 0" using \<delta>_pos \<delta>\<^sub>1_pos \<delta>\<^sub>2_pos by (simp add: \<delta>\<^sub>3_def)

    (* Pick concrete h, k *)
    define h where "h = \<delta>\<^sub>3 / 2"
    define k where "k = \<delta>\<^sub>3 / 2"
    have h_pos: "h > 0" and k_pos: "k > 0"
      using \<delta>\<^sub>3_pos by (simp_all add: h_def k_def)
    have h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
      using \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def, auto)

    (* Apply dir1 and dir2 *)
    obtain \<xi> \<eta> where \<xi>_bd: "\<bar>\<xi>\<bar> \<le> h" and \<eta>_bd: "\<bar>\<eta>\<bar> \<le> k"
      and eq_ij: "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      using dir1[OF h_pos k_pos h_bd k_bd] h_pos k_pos by auto

    obtain \<xi>' \<eta>' where \<xi>'_bd: "\<bar>\<xi>'\<bar> \<le> h" and \<eta>'_bd: "\<bar>\<eta>'\<bar> \<le> k"
      and eq_ji: "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      using dir2[OF h_pos k_pos h_bd k_bd] h_pos k_pos by auto

    (* Both \<xi>,\<eta> and \<xi>',\<eta>' are within \<delta>\<^sub>1 and \<delta>\<^sub>2 bounds *)
    have "\<bar>\<xi>\<bar> < \<delta>\<^sub>1" and "\<bar>\<eta>\<bar> < \<delta>\<^sub>1"
      using \<xi>_bd \<eta>_bd \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def)
    hence close_ij:
      "\<bar>(\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      using \<delta>\<^sub>1_bd by blast

    have "\<bar>\<xi>'\<bar> < \<delta>\<^sub>2" and "\<bar>\<eta>'\<bar> < \<delta>\<^sub>2"
      using \<xi>'_bd \<eta>'_bd \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def)
    hence close_ji:
      "\<bar>(\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      using \<delta>\<^sub>2_bd by blast

    (* From eq_ij and eq_ji, since h*k > 0 we can cancel: *)
    have "(\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j =
          (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      using eq_ij eq_ji h_pos k_pos by simp

    (* Triangle inequality gives contradiction *)
    hence "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < 2 * \<epsilon>"
      using close_ij close_ji by linarith
    hence "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar>
            < 2 * \<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> / 3"
      by (simp add: \<epsilon>_def)
    moreover have "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> > 0"
      using neq by simp
    ultimately show False
      by (simp add: field_simps)
  qed

  (* ---------- 11.  Translate to gradient notation ---------- *)
  have Hx: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Hess_exists xU by blast

  have rowi: "(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
    using hessian_eq_double_nabla[OF Hx] by simp
  have rowj: "(\<nabla>\<^sup>2 f x) $ j $ i = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
    using hessian_eq_double_nabla[OF Hx] by simp

  show ?thesis
    using \<open>(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla>\<^sup>2 f x) $ j $ i\<close> rowi rowj by simp
qed



theorem clairaut_hessian_symmetric:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "open U"
      and "x \<in> U"
      and "Ck_on 2 f U"
  shows "transpose (\<nabla>\<^sup>2 f x) = \<nabla>\<^sup>2 f x"
proof -
  have H: "HESS f x :> \<nabla>\<^sup>2 f x"
    using assms(2,3) by (subst Ck_2_imp_hessian_exists, simp_all)

  have sym_entries: "\<forall>i j. \<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
  proof (intro allI)
    fix i j
    have ij: "\<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
      using hessian_eq_double_nabla[OF H] by simp
    have ji: "\<nabla>\<^sup>2 f x $ j $ i = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
      using hessian_eq_double_nabla[OF H] by simp
    have mix: "(\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
      by (rule mixed_coordinate_second_derivative_eq[OF assms])
    show "\<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
      using ij ji mix by simp
  qed
  then show ?thesis
    by (simp add: Finite_Cartesian_Product.transpose_def)
qed

text \<open>Equivalently, all mixed partials commute.\<close>

corollary mixed_partials_commute:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "open U" and "x \<in> U" and "Ck_on 2 f U"
  shows "\<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
  using clairaut_hessian_symmetric[OF assms]
  by (metis (no_types, lifting) Finite_Cartesian_Product.transpose_def vec_lambda_beta)

(* ================================================================== *)
subsection \<open>Basic algebra of gradients\<close>
(* ================================================================== *)

lemma GRAD_add:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> gf"
      and Gg: "GRAD g x :> gg"
  shows "GRAD (\<lambda>y. f y + g y) x :> gf + gg"
  using Gf Gg
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros simp: inner_add_right)

lemma grad_fun_add:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
      and "\<exists>gg. GRAD g x :> gg"
  shows "\<nabla> (\<lambda>y. f y + g y) x = \<nabla> f x + \<nabla> g x"
proof -
  have Gf: "GRAD f x :> \<nabla> f x"
    using assms(1) by (blast intro: grad_fun_satisfies_GRAD)
  have Gg: "GRAD g x :> \<nabla> g x"
    using assms(2) by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. f y + g y) x :> \<nabla> f x + \<nabla> g x"
    by (rule GRAD_add[OF Gf Gg])
  thus ?thesis
    by (rule grad_fun_eq)
qed

lemma GRAD_scaleR:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> gf"
  shows "GRAD (\<lambda>y. c * f y) x :> c *\<^sub>R gf"
  using Gf
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros simp: inner_commute)

lemma grad_fun_scaleR:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
  shows "\<nabla> (\<lambda>y. c * f y) x = c *\<^sub>R \<nabla> f x"
proof -
  have Gf: "GRAD f x :> \<nabla> f x"
    using assms by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. c * f y) x :> c *\<^sub>R \<nabla> f x"
    by (rule GRAD_scaleR[OF Gf])
  thus ?thesis
    by (rule grad_fun_eq)
qed

lemma GRAD_neg:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> gf"
  shows "GRAD (\<lambda>y. - f y) x :> - gf"
proof -
  have "GRAD (\<lambda>y. (-1) * f y) x :> (-1) *\<^sub>R gf"
    by (rule GRAD_scaleR[OF Gf])
  thus ?thesis by simp
qed

lemma grad_fun_neg:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
  shows "\<nabla> (\<lambda>y. - f y) x = - \<nabla> f x"
proof -
  have "\<nabla> (\<lambda>y. (-1) * f y) x = (-1) *\<^sub>R \<nabla> f x"
    by (rule grad_fun_scaleR[OF assms])
  thus ?thesis by simp
qed

lemma GRAD_sub:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> gf"
      and Gg: "GRAD g x :> gg"
  shows "GRAD (\<lambda>y. f y - g y) x :> gf - gg"
proof -
  have "GRAD (\<lambda>y. f y + (- g y)) x :> gf + (- gg)"
    by (rule GRAD_add[OF Gf GRAD_neg[OF Gg]])
  thus ?thesis by simp
qed

lemma grad_fun_sub:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
      and "\<exists>gg. GRAD g x :> gg"
  shows "\<nabla> (\<lambda>y. f y - g y) x = \<nabla> f x - \<nabla> g x"
proof -
  have "\<nabla> (\<lambda>y. f y + (- g y)) x = \<nabla> f x + \<nabla> (\<lambda>y. - g y) x"
    using assms grad_fun_add GRAD_neg by blast
  also have "\<nabla> (\<lambda>y. - g y) x = - \<nabla> g x"
    by (rule grad_fun_neg[OF assms(2)])
  finally show ?thesis by simp
qed


(* ================================================================== *)
subsection \<open>Constants and affine maps\<close>
(* ================================================================== *)

lemma GRAD_const:
  fixes c :: real
  shows "GRAD (\<lambda>_. c) x :> 0"
  unfolding has_gradient_def
  by simp

lemma grad_fun_const:
  fixes c :: real
  shows "\<nabla> (\<lambda>_. c) x = 0"
  by (rule grad_fun_eq[OF GRAD_const])

lemma GRAD_affine:
  fixes a :: real and b :: "real^'n::finite"
  shows "GRAD (\<lambda>x. a + x \<bullet> b) x :> b"
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros simp: inner_commute)

lemma grad_fun_affine:
  fixes a :: real and b :: "real^'n::finite"
  shows "\<nabla> (\<lambda>x. a + x \<bullet> b) x = b"
  by (rule grad_fun_eq[OF GRAD_affine])

lemma GRAD_sum:
  fixes F :: "'i \<Rightarrow> real^'n::finite \<Rightarrow> real"
  fixes G :: "'i \<Rightarrow> real^'n"
  assumes fin: "finite I"
      and G: "\<And>i. i \<in> I \<Longrightarrow> GRAD (F i) x :> G i"
  shows "GRAD (\<lambda>y. \<Sum>i\<in>I. F i y) x :> (\<Sum>i\<in>I. G i)"
  using fin G
proof (induction rule: finite_induct)
  case empty
  show ?case
    unfolding has_gradient_def
    by simp
next
  case (insert i I)
  have Gi: "GRAD (F i) x :> G i"
    using insert.prems by simp
  have GI: "GRAD (\<lambda>y. \<Sum>j\<in>I. F j y) x :> (\<Sum>j\<in>I. G j)"
    using insert.IH insert.prems by blast
  have "GRAD (\<lambda>y. F i y + (\<Sum>j\<in>I. F j y)) x :> G i + (\<Sum>j\<in>I. G j)"
    by (rule GRAD_add[OF Gi GI])
  then show ?case
    using insert.hyps
    by simp
qed

lemma grad_fun_sum:
  fixes F :: "'i \<Rightarrow> real^'n::finite \<Rightarrow> real"
  assumes fin: "finite I"
      and exG: "\<And>i. i \<in> I \<Longrightarrow> \<exists>g. GRAD (F i) x :> g"
  shows "\<nabla> (\<lambda>y. \<Sum>i\<in>I. F i y) x = (\<Sum>i\<in>I. \<nabla> (F i) x)"
proof -
  have G: "\<And>i. i \<in> I \<Longrightarrow> GRAD (F i) x :> \<nabla> (F i) x"
    using exG by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. \<Sum>i\<in>I. F i y) x :> (\<Sum>i\<in>I. \<nabla> (F i) x)"
    by (rule GRAD_sum[OF fin G])
  thus ?thesis
    by (rule grad_fun_eq)
qed


(* ================================================================== *)
subsection \<open>Hessian: constants and affine maps\<close>
(* ================================================================== *)

lemma HESS_const_zero:
  fixes c :: real
  shows "HESS (\<lambda>_. c) x :> 0"
  unfolding has_hessian_def
  by (metis (no_types, lifting) ext grad_fun_const has_derivative_const matrix_vector_mult_0)

lemma HESS_affine_zero:
  fixes a :: real and b :: "real^'n::finite"
  shows "HESS (\<lambda>x. a + x \<bullet> b) x :> 0"
  unfolding has_hessian_def
  by (metis (no_types, lifting) ext grad_fun_affine has_derivative_const matrix_vector_mult_0)

lemma hessian_const_zero:
  fixes c :: real
  shows "\<nabla>\<^sup>2 (\<lambda>_. c) x = 0"
  using HESS_const_zero by (metis hess_fun_eq)

lemma hessian_affine_zero:
  fixes a :: real and b :: "real^'n::finite"
  shows "\<nabla>\<^sup>2 (\<lambda>x. a + x \<bullet> b) x = 0"
  using HESS_affine_zero by (metis hess_fun_eq)


(* ================================================================== *)
subsection \<open>Coordinate formulas\<close>
(* ================================================================== *)

lemma HESS_row_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "GRAD (\<lambda>y. \<nabla> f y $ i) x :> Hx $ i"
proof -
  have Hd: "(\<nabla> f has_derivative (*v) Hx) (at x)"
    using H unfolding has_hessian_def by simp
  have Hcomp:
    "((\<lambda>y. \<nabla> f y \<bullet> axis i 1) has_derivative
       (\<lambda>v. ((*v) Hx) v \<bullet> axis i 1)) (at x within UNIV)"
    using Hd
    by (subst (asm) has_derivative_componentwise_within[where S = UNIV])
       (auto simp: Basis_vec_def)
  have comp_fun:
    "(\<lambda>y. \<nabla> f y \<bullet> axis i 1) = (\<lambda>y. \<nabla> f y $ i)"
    by (rule ext) (simp add: cart_eq_inner_axis)
  have comp_deriv:
    "(\<lambda>v. ((*v) Hx) v \<bullet> axis i 1) = (\<lambda>v. v \<bullet> (Hx $ i))"
    by (metis (no_types) cart_eq_inner_axis inner_commute matrix_vector_mul_component)
  show ?thesis
    using Hcomp
    unfolding has_gradient_def
    by (simp add: comp_fun comp_deriv)
qed

lemma HESS_row_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "\<nabla> (\<lambda>y. \<nabla> f y $ i) x = Hx $ i"
  by (rule grad_fun_eq[OF HESS_row_gradient[OF H]])

lemma HESS_component_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "Hx $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
  using HESS_row_eq[OF H, of i] by simp


(* ================================================================== *)
subsection \<open>Hessian algebra at the predicate level\<close>
(* ================================================================== *)

lemma HESS_add:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Hf: "HESS f x :> Hf'" and Hg: "HESS g x :> Hg'"
      and eq: "\<And>y. y \<in> A \<Longrightarrow> \<nabla> (\<lambda>z. f z + g z) y = \<nabla> f y + \<nabla> g y"
      and Aop: "open A" and xA: "x \<in> A"
  shows "HESS (\<lambda>y. f y + g y) x :> Hf' + Hg'"
proof -
  have dsum: "((\<lambda>y. \<nabla> f y + \<nabla> g y) has_derivative
               (\<lambda>v. Hf' *v v + Hg' *v v)) (at x)"
    using has_derivative_add
      Hf[unfolded has_hessian_def] Hg[unfolded has_hessian_def] by blast
  have dtrans: "((\<lambda>y. \<nabla> (\<lambda>z. f z + g z) y) has_derivative
                 (\<lambda>v. Hf' *v v + Hg' *v v)) (at x)"
    by (smt (verit, best) Aop dsum eq has_derivative_transfer_on_open xA)

  have "\<And>v. (Hf' + Hg') *v v = Hf' *v v + Hg' *v v"
    by (simp add: matrix_vector_mult_def vec_eq_iff sum.distrib distrib_right)
  thus ?thesis
    unfolding has_hessian_def using dtrans by presburger
qed

lemma HESS_scaleR:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Hf: "HESS f x :> Hf'"
      and eq: "\<And>y. y \<in> A \<Longrightarrow> \<nabla> (\<lambda>z. c * f z) y = c *\<^sub>R \<nabla> f y"
      and Aop: "open A" and xA: "x \<in> A"
  shows "HESS (\<lambda>y. c * f y) x :> c *\<^sub>R Hf'"
proof -
  have dscale: "((\<lambda>y. c *\<^sub>R \<nabla> f y) has_derivative
                 (\<lambda>v. c *\<^sub>R (Hf' *v v))) (at x)"
    using Hf[unfolded has_hessian_def]
    by (intro has_derivative_scaleR_right)
  have dtrans: "((\<lambda>y. \<nabla> (\<lambda>z. c * f z) y) has_derivative
                 (\<lambda>v. c *\<^sub>R (Hf' *v v))) (at x)"
    using Aop dscale eq has_derivative_transform_within_open xA by force
  have "\<And>v. (c *\<^sub>R Hf') *v v = c *\<^sub>R (Hf' *v v)"
    by (simp add: matrix_vector_mult_def vec_eq_iff scaleR_sum_right,
        simp add: sum_distrib_left vector_space_over_itself.scale_scale)
  thus ?thesis
    unfolding has_hessian_def using dtrans by presburger
qed


(* ================================================================== *)
subsection \<open>Linearity of the Hessian on C² maps\<close>
(* ================================================================== *)

lemma hessian_add_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y + g y) x = \<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i
  have openU: "open U"
    using Cf by (simp add: Ck_on_def)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g x :> \<nabla>\<^sup>2 g x"
    using Cg xU by (rule Ck_2_imp_hessian_exists)
  have Hfg: "HESS (\<lambda>y. f y + g y) x :> \<nabla>\<^sup>2 (\<lambda>y. f y + g y) x"
    using Ck_on_add[OF Cf Cg] xU by (rule Ck_2_imp_hessian_exists)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. f z + g z) y $ i"
  let ?\<psi> = "\<lambda>y. \<nabla> f y $ i + \<nabla> g y $ i"
  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have Gf: "GRAD f y :> \<nabla> f y"
      using Ck_2_imp_gradient_exists[OF Cf yU]
      by (blast intro: grad_fun_satisfies_GRAD)
    have Gg: "GRAD g y :> \<nabla> g y"
      using Ck_2_imp_gradient_exists[OF Cg yU]
      by (blast intro: grad_fun_satisfies_GRAD)
    have "GRAD (\<lambda>z. f z + g z) y :> \<nabla> f y + \<nabla> g y"
      by (rule GRAD_add[OF Gf Gg])
    hence "\<nabla> (\<lambda>z. f z + g z) y = \<nabla> f y + \<nabla> g y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed
  have Grow_f: "GRAD (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have Grow_g: "GRAD (\<lambda>y. \<nabla> g y $ i) x :> (\<nabla>\<^sup>2 g x) $ i"
    by (rule HESS_row_gradient[OF Hg])
  have G\<psi>: "GRAD ?\<psi> x :> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i)"
    using GRAD_add[OF Grow_f Grow_g] by simp
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i))) (at x)"
    using G\<psi> unfolding has_gradient_def by simp
  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i))) (at x)"
    by (smt (verit, best) D\<psi> eqU has_derivative_transform_within_open openU xU)
  have G\<phi>: "GRAD ?\<phi> x :> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i)"
    using D\<phi> unfolding has_gradient_def by simp
  show "\<nabla>\<^sup>2 (\<lambda>y. f y + g y) x $ i = (\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i"
    using G\<phi> HESS_row_eq Hfg grad_fun_eq by fastforce
qed

lemma hessian_scaleR_on_C2:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. c * f y) x = c *\<^sub>R \<nabla>\<^sup>2 f x"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i
  have openU: "open U"
    using Cf by (simp add: Ck_on_def)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hcf: "HESS (\<lambda>y. c * f y) x :> \<nabla>\<^sup>2 (\<lambda>y. c * f y) x"
    using Ck_on_scaleR[OF Cf] xU by (subst Ck_2_imp_hessian_exists, auto)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. c * f z) y $ i"
  let ?\<psi> = "\<lambda>y. c * (\<nabla> f y $ i)"
  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have Gf: "GRAD f y :> \<nabla> f y"
      using Ck_2_imp_gradient_exists[OF Cf yU]
      by (blast intro: grad_fun_satisfies_GRAD)
    have "GRAD (\<lambda>z. c * f z) y :> c *\<^sub>R \<nabla> f y"
      by (rule GRAD_scaleR[OF Gf])
    hence "\<nabla> (\<lambda>z. c * f z) y = c *\<^sub>R \<nabla> f y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed
  have Grow_f: "GRAD (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have G\<psi>: "GRAD ?\<psi> x :> c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)"
    using GRAD_scaleR[OF Grow_f] by simp
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> (c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)))) (at x)"
    using G\<psi> unfolding has_gradient_def by simp
  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> (c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)))) (at x)"
    using D\<psi> eqU has_derivative_transform_within_open openU xU by fastforce
  have G\<phi>: "GRAD ?\<phi> x :> c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)"
    using D\<phi> unfolding has_gradient_def by simp
  show "\<nabla>\<^sup>2 (\<lambda>y. c * f y) x $ i = (c *\<^sub>R \<nabla>\<^sup>2 f x) $ i"
    using G\<phi> HESS_row_eq Hcf grad_fun_eq by fastforce
qed

lemma hessian_sub_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y - g y) x = \<nabla>\<^sup>2 f x - \<nabla>\<^sup>2 g x"
proof -
  have "\<nabla>\<^sup>2 (\<lambda>y. f y + (-1) * g y) x = \<nabla>\<^sup>2 f x + (-1) *\<^sub>R \<nabla>\<^sup>2 g x"
  proof (subst hessian_add_on_C2)
    show "Ck_on 2 f U"
      by (rule Cf)
    show "Ck_on 2 (\<lambda>y. (-1) * g y) U"
      using Ck_on_scaleR[OF Cg] by (metis ext real_scaleR_def)
    show "x \<in> U"
      by (rule xU)
    show "\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 (\<lambda>y. - 1 * g y) x = \<nabla>\<^sup>2 f x + - 1 *\<^sub>R \<nabla>\<^sup>2 g x"
      by (metis Cg hessian_scaleR_on_C2 xU)
  qed
  thus ?thesis by simp
qed

lemma hessian_sum_on_C2:
  fixes F :: "'i \<Rightarrow> real^'n::finite \<Rightarrow> real"
  assumes fin: "finite I"
      and C2: "\<And>i. i \<in> I \<Longrightarrow> Ck_on 2 (F i) U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>i\<in>I. F i y) x = (\<Sum>i\<in>I. \<nabla>\<^sup>2 (F i) x)"
  using fin C2
proof (induction rule: finite_induct)
  case empty
  show ?case by (simp add: hessian_const_zero)
next
  case (insert i I)
  have Ci: "Ck_on 2 (F i) U"
    using insert.prems by simp
  have openU: "open U"
    using Ci by (simp add: Ck_on_def)
  have C2_I: "\<And>j. j \<in> I \<Longrightarrow> Ck_on 2 (F j) U"
    using insert.prems by simp
  have CI: "Ck_on 2 (\<lambda>y. \<Sum>j\<in>I. F j y) U"
  proof (cases "I = {}")
    case True
    then show ?thesis
      using Ck_on_const[OF openU] by simp
  next
    case False
    then show ?thesis
      using Ck_on_sum[OF insert.hyps(1) False C2_I]
      by presburger
  qed
  have IH: "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>I. F j y) x = (\<Sum>j\<in>I. \<nabla>\<^sup>2 (F j) x)"
    using insert.IH C2_I by blast
  have "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>insert i I. F j y) x
        = \<nabla>\<^sup>2 (\<lambda>y. F i y + (\<Sum>j\<in>I. F j y)) x"
    by (simp add: insert.hyps(1,2))
  also have "\<dots> = \<nabla>\<^sup>2 (F i) x + \<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>I. F j y) x"
    by (rule hessian_add_on_C2[OF Ci CI xU])
  also have "\<dots> = \<nabla>\<^sup>2 (F i) x + (\<Sum>j\<in>I. \<nabla>\<^sup>2 (F j) x)"
    by (simp add: IH)
  also have "\<dots> = (\<Sum>j\<in>insert i I. \<nabla>\<^sup>2 (F j) x)"
    using insert.hyps by simp
  finally show ?case.
qed

lemma second_directional_derivative_eq_hessian_quadratic_form:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes C2: "Ck_on 2 f U"
      and xU: "x \<in> U"
  shows "frechet_derivative (\<lambda>y. frechet_derivative f (at y) v) (at x) v
       = v \<bullet> ((\<nabla>\<^sup>2 f x) *v v)"
proof -
  have openU: "open U"
    using C2 by (simp add: Ck_on_def)

  have H: "HESS f x :> \<nabla>\<^sup>2 f x"
    using C2 xU by (rule Ck_2_imp_hessian_exists)

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> frechet_derivative f (at y) v = v \<bullet> \<nabla> f y"
  proof -
    fix y
    assume yU: "y \<in> U"

    from Ck_2_imp_gradient_exists[OF C2 yU]
    obtain g where g: "GRAD f y :> g"
      by blast

    have Gy: "GRAD f y :> \<nabla> f y"
      using g by (rule grad_fun_satisfies_GRAD)

    have "(f has_derivative (\<lambda>w. w \<bullet> \<nabla> f y)) (at y)"
      using Gy unfolding has_gradient_def by simp
    hence "frechet_derivative f (at y) = (\<lambda>w. w \<bullet> \<nabla> f y)"
      by (subst frechet_derivative_at, auto)

    thus "frechet_derivative f (at y) v = v \<bullet> \<nabla> f y"
      by simp
  qed
  have "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. frechet_derivative f (at y) v = v \<bullet> \<nabla> f y)"
    using openU xU eqU by blast
  then have ev_eq: "eventually (\<lambda>y. frechet_derivative f (at y) v = v \<bullet> \<nabla> f y) (nhds x)"
    by (simp add: eventually_nhds)
  have Dgrad: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f x)) (at x)"
    using H unfolding has_hessian_def by simp
  have Dcomp: "((\<lambda>y. v \<bullet> \<nabla> f y) has_derivative (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))) (at x)"
    using Dgrad by (auto intro!: derivative_eq_intros)
  have Dfd: "((\<lambda>y. frechet_derivative f (at y) v) has_derivative
       (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))) (at x)"
    by (metis (no_types, lifting) Dcomp eqU has_derivative_transform_within_open openU xU)
  have FD: "frechet_derivative (\<lambda>y. frechet_derivative f (at y) v) (at x)
    = (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))"
    by (metis Dfd frechet_derivative_at)
  show ?thesis
    by (simp add: FD)
qed

(* ================================================================== *)
subsection \<open>Outer product of vectors\<close>
(* ================================================================== *)

definition outer_prod :: "real^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" (infixl "\<otimes>" 70)
  where "a \<otimes> b = (\<chi> i j. a $ i * b $ j)"

lemma outer_prod_component [simp]:
  "(a \<otimes> b) $ i $ j = a $ i * b $ j"
  by (simp add: outer_prod_def)

lemma outer_prod_row:
  "(a \<otimes> b) $ i = (a $ i) *\<^sub>R b"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_commute:
  "transpose (a \<otimes> b) = b \<otimes> a"
  by (simp add: vec_eq_iff transpose_def outer_prod_def mult.commute)

lemma outer_prod_add_left:
  "(a + b) \<otimes> c = a \<otimes> c + b \<otimes> c"
  by (simp add: vec_eq_iff outer_prod_def distrib_right)

lemma outer_prod_add_right:
  "a \<otimes> (b + c) = a \<otimes> b + a \<otimes> c"
  by (simp add: vec_eq_iff outer_prod_def distrib_left)

lemma outer_prod_scaleR_left:
  "(c *\<^sub>R a) \<otimes> b = c *\<^sub>R (a \<otimes> b)"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_scaleR_right:
  "a \<otimes> (c *\<^sub>R b) = c *\<^sub>R (a \<otimes> b)"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_zero_left [simp]:
  "0 \<otimes> b = 0"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_zero_right [simp]:
  "a \<otimes> 0 = 0"
  by (simp add: vec_eq_iff outer_prod_def)

lemma outer_prod_mult_vec:
  "(a \<otimes> b) *v v = (b \<bullet> v) *\<^sub>R a"
  by (simp add: matrix_vector_mul_component outer_prod_row vec_eq_iff)


(* ================================================================== *)
subsection \<open>Gradient product rule\<close>
(* ================================================================== *)

lemma GRAD_mult:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> df"
      and Gg: "GRAD g x :> dg"
  shows "GRAD (\<lambda>y. f y * g y) x :> f x *\<^sub>R dg + g x *\<^sub>R df"
proof -
  have Df: "(f has_derivative (\<lambda>v. v \<bullet> df)) (at x)"
    using Gf unfolding has_gradient_def.
  have Dg: "(g has_derivative (\<lambda>v. v \<bullet> dg)) (at x)"
    using Gg unfolding has_gradient_def.
  have "((\<lambda>y. f y * g y) has_derivative
         (\<lambda>v. f x * (v \<bullet> dg) + (v \<bullet> df) * g x)) (at x)"
    using Df Dg by (auto intro!: derivative_eq_intros)
  moreover have "\<And>v. f x * (v \<bullet> dg) + (v \<bullet> df) * g x
                    = v \<bullet> (f x *\<^sub>R dg + g x *\<^sub>R df)"
    by (simp add: inner_add_right mult.commute)
  ultimately show ?thesis
    unfolding has_gradient_def by simp
qed

lemma grad_fun_mult:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
      and "\<exists>gg. GRAD g x :> gg"
  shows "\<nabla> (\<lambda>y. f y * g y) x = f x *\<^sub>R \<nabla> g x + g x *\<^sub>R \<nabla> f x"
proof -
  have Gf: "GRAD f x :> \<nabla> f x"
    using assms(1) by (blast intro: grad_fun_satisfies_GRAD)
  have Gg: "GRAD g x :> \<nabla> g x"
    using assms(2) by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. f y * g y) x :> f x *\<^sub>R \<nabla> g x + g x *\<^sub>R \<nabla> f x"
    by (rule GRAD_mult[OF Gf Gg])
  thus ?thesis
    by (rule grad_fun_eq)
qed


(* ================================================================== *)
subsection \<open>Hessian product rule\<close>
(* ================================================================== *)

text \<open>
  For scalar \<open>C²\<close> functions \<open>f, g : \<real>ⁿ \<rightarrow> \<real>\<close> on an open set \<open>U\<close>:

    \<open>\<nabla>²(fg)(x) = f(x) \<nabla>²g(x) + g(x) \<nabla>²f(x) + (\<nabla>f(x)) \<otimes> (\<nabla>g(x)) + (\<nabla>g(x)) \<otimes> (\<nabla>f(x))\<close>

  where \<open>a \<otimes> b\<close> denotes the outer product \<open>(\<chi> i j. a$i * b$j)\<close>.
\<close>

lemma hessian_mult_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x =
           f x *\<^sub>R \<nabla>\<^sup>2 g x + g x *\<^sub>R \<nabla>\<^sup>2 f x
         + (\<nabla> f x) \<otimes> (\<nabla> g x)
         + (\<nabla> g x) \<otimes> (\<nabla> f x)"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i

  have openU: "open U"
    using Cf by (simp add: Ck_on_def)

  (* ---- Hessians exist ---- *)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g x :> \<nabla>\<^sup>2 g x"
    using Cg xU by (rule Ck_2_imp_hessian_exists)

  have Cfh: "Ck_on 2 (\<lambda>y. f y * g y) U"
    by (simp add: Cf Cg Ck_on_mult)

  have Hfg: "HESS (\<lambda>y. f y * g y) x :> \<nabla>\<^sup>2 (\<lambda>y. f y * g y) x"
    using Cfh xU by (rule Ck_2_imp_hessian_exists)

  (* ---- Gradient existence on U ---- *)
  have Gf_at: "\<And>y. y \<in> U \<Longrightarrow> GRAD f y :> \<nabla> f y"
    using Ck_2_imp_gradient_exists[OF Cf]
    by (blast intro: grad_fun_satisfies_GRAD)
  have Gg_at: "\<And>y. y \<in> U \<Longrightarrow> GRAD g y :> \<nabla> g y"
    using Ck_2_imp_gradient_exists[OF Cg]
    by (blast intro: grad_fun_satisfies_GRAD)

  (* ---- Row gradients of Hessians ---- *)
  have Hf_row: "GRAD (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have Hg_row: "GRAD (\<lambda>y. \<nabla> g y $ i) x :> (\<nabla>\<^sup>2 g x) $ i"
    by (rule HESS_row_gradient[OF Hg])

  (* ---- The i-th component of \<nabla>(fg) ---- *)
  (* On U: \<nabla>(fg)(y) $ i = f(y) * \<nabla>g(y) $ i + g(y) * \<nabla>f(y) $ i *)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. f z * g z) y $ i"
  let ?\<psi> = "\<lambda>y. f y * (\<nabla> g y $ i) + g y * (\<nabla> f y $ i)"

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have "GRAD (\<lambda>z. f z * g z) y :> f y *\<^sub>R \<nabla> g y + g y *\<^sub>R \<nabla> f y"
      by (rule GRAD_mult[OF Gf_at[OF yU] Gg_at[OF yU]])
    hence "\<nabla> (\<lambda>z. f z * g z) y = f y *\<^sub>R \<nabla> g y + g y *\<^sub>R \<nabla> f y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed

  (* ---- Gradient of y \<mapsto> f(y) * \<nabla>g(y)$i ---- *)
  have Gf_x: "GRAD f x :> \<nabla> f x"
    using Gf_at[OF xU] .
  have Gg_x: "GRAD g x :> \<nabla> g x"
    using Gg_at[OF xU] .

  have G_term1: "GRAD (\<lambda>y. f y * (\<nabla> g y $ i)) x :>
                   f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x"
    by (rule GRAD_mult[OF Gf_x Hg_row])

  (* ---- Gradient of y \<mapsto> g(y) * \<nabla>f(y)$i ---- *)
  have G_term2: "GRAD (\<lambda>y. g y * (\<nabla> f y $ i)) x :>
                   g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x"
    by (rule GRAD_mult[OF Gg_x Hf_row])

  (* ---- Gradient of \<psi> by addition ---- *)
  have G\<psi>: "GRAD ?\<psi> x :>
               (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
             + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (rule GRAD_add[OF G_term1 G_term2])

  (* ---- Transfer from \<psi> to \<phi> using agreement on U ---- *)
  have D\<psi>: "(?\<psi> has_derivative
      (\<lambda>v. v \<bullet> ((f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
              + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)))) (at x)"
    using G\<psi> unfolding has_gradient_def by simp

  have D\<phi>: "(?\<phi> has_derivative
      (\<lambda>v. v \<bullet> ((f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
              + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)))) (at x)"
    using D\<psi> eqU has_derivative_transform_within_open openU xU by fastforce

  have G\<phi>: "GRAD ?\<phi> x :>
               (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
             + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    using D\<phi> unfolding has_gradient_def by simp

  (* ---- Assemble the row ---- *)
  have row_eq: "\<nabla> ?\<phi> x =
      (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
    + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (rule grad_fun_eq[OF G\<phi>])

  have lhs: "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x $ i = \<nabla> ?\<phi> x"
    using HESS_row_eq[OF Hfg] by simp

  (* ---- Express the RHS in terms of the target matrix ---- *)
  let ?M = "f x *\<^sub>R \<nabla>\<^sup>2 g x + g x *\<^sub>R \<nabla>\<^sup>2 f x
          + (\<nabla> f x) \<otimes> (\<nabla> g x)
          + (\<nabla> g x) \<otimes> (\<nabla> f x)"

  have rhs: "?M $ i =
      (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
    + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (simp add: vec_eq_iff outer_prod_row algebra_simps)

  show "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x $ i = ?M $ i"
    using lhs row_eq rhs by simp
qed

(* ================================================================== *)
subsection \<open>Matrix–inner product identity\<close>
(* ================================================================== *)

lemma transpose_mv_inner:
  fixes A :: "real^'n^'m" and v :: "real^'n" and w :: "real^'m"
  shows "(A *v v) \<bullet> w = v \<bullet> (transpose A *v w)"
proof -
  have "(A *v v) \<bullet> w = (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. A $ i $ j * v $ j) * w $ i)"
    by (simp add: matrix_vector_mult_def inner_vec_def)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (A $ i $ j * v $ j) * w $ i)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. w $ i * A $ i $ j * v $ j)"
    by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. w $ i * A $ i $ j * v $ j)"
    using sum.swap by fastforce
  also have "\<dots> = (\<Sum>j\<in>UNIV. v $ j * (\<Sum>i\<in>UNIV. A $ i $ j * w $ i))"
    by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
  also have "\<dots> = v \<bullet> (transpose A *v w)"
    by (simp add: matrix_vector_mult_def inner_vec_def transpose_def)
  finally show ?thesis.
qed


(* ================================================================== *)
subsection \<open>Jacobian\<close>
(* ================================================================== *)

definition jacobian :: "(real^'n::finite \<Rightarrow> real^'m::finite) \<Rightarrow> real^'n \<Rightarrow> real^'n^'m"
  where "jacobian F x = matrix (frechet_derivative F (at x))"

lemma jacobian_works:
  assumes "F differentiable (at x)"
  shows "frechet_derivative F (at x) v = jacobian F x *v v"
  unfolding jacobian_def
  by (simp add: assms linear_frechet_derivative)

lemma jacobian_component:
  assumes "F differentiable (at x)"
  shows "jacobian F x $ r $ i = frechet_derivative (\<lambda>y. F y $ r) (at x) (axis i 1)"
proof -
  have FD: "(F has_derivative frechet_derivative F (at x)) (at x)"
    using assms frechet_derivative_works by blast

  have coord_D:  "((\<lambda>y. F y $ r) has_derivative (\<lambda>h. frechet_derivative F (at x) h $ r)) (at x)"
  proof -
    have Hcomp: "((\<lambda>y. F y \<bullet> axis r 1) has_derivative
          (\<lambda>h. frechet_derivative F (at x) h \<bullet> axis r 1)) (at x within UNIV)"
      using FD by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
                   auto simp: Basis_vec_def)
    have comp_fun: "(\<lambda>y. F y \<bullet> axis r 1) = (\<lambda>y. F y $ r)"
      by (rule ext, simp add: cart_eq_inner_axis)
    have comp_deriv: "(\<lambda>h. frechet_derivative F (at x) h \<bullet> axis r 1)
                    = (\<lambda>h. frechet_derivative F (at x) h $ r)"
      by (rule ext, simp add: cart_eq_inner_axis)
    show ?thesis
      using Hcomp by (simp add: comp_fun comp_deriv)
  qed
  have coord_FD: "frechet_derivative (\<lambda>y. F y $ r) (at x) = (\<lambda>h. frechet_derivative F (at x) h $ r)"
    by (subst frechet_derivative_at[OF coord_D], simp)
  have "(jacobian F x *v axis i 1) $ r = jacobian F x $ r $ i"
    by (simp add: matrix_vector_mult_def,
        metis (full_types) cart_eq_inner_axis inner_real_def inner_vec_def)
  moreover have "jacobian F x *v axis i 1 = frechet_derivative F (at x) (axis i 1)"
    using assms by (subst jacobian_works, auto)
  ultimately have "jacobian F x $ r $ i = frechet_derivative F (at x) (axis i 1) $ r"
    by simp
  also have "... = frechet_derivative (\<lambda>y. F y $ r) (at x) (axis i 1)"
    by (simp add: coord_FD)
  finally show ?thesis.
qed

(* ================================================================== *)
subsection \<open>Gradient chain rule\<close>
(* ================================================================== *)

text \<open>
  If \<open>g : \<real>ᵐ \<rightarrow> \<real>\<close> has gradient \<open>\<nabla>g(F(x))\<close> at \<open>F(x)\<close> and \<open>F : \<real>ⁿ \<rightarrow> \<real>ᵐ\<close>
  is Fréchet differentiable at \<open>x\<close>, then:

    \<open>\<nabla>(g \<circ> F)(x) = Jᶠ(x)ᵀ *v \<nabla>g(F(x))\<close>

  where \<open>Jᶠ(x)\<close> is the Jacobian of \<open>F\<close> at \<open>x\<close>.
\<close>

lemma GRAD_compose:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes Gg: "GRAD g (F x) :> dg"
      and DF: "(F has_derivative J) (at x)"
  shows "GRAD (\<lambda>y. g (F y)) x :> transpose (matrix J) *v dg"
proof -
  have Dg: "(g has_derivative (\<lambda>w. w \<bullet> dg)) (at (F x))"
    using Gg unfolding has_gradient_def .

  have Dcomp: "((\<lambda>y. g (F y)) has_derivative (\<lambda>v. J v \<bullet> dg)) (at x)"
    using has_derivative_compose[OF DF Dg] by (simp add: o_def)

  have "\<And>v. J v \<bullet> dg = v \<bullet> (transpose (matrix J) *v dg)"
  proof -
    fix v
    have bl: "bounded_linear J"
      using DF by (rule has_derivative_bounded_linear)
    have "J v = matrix J *v v"
      using bl by (simp add: matrix_works)
    hence "J v \<bullet> dg = (matrix J *v v) \<bullet> dg"
      by simp
    also have "\<dots> = v \<bullet> (transpose (matrix J) *v dg)"
      by (rule transpose_mv_inner)
    finally show "J v \<bullet> dg = v \<bullet> (transpose (matrix J) *v dg)" .
  qed

  hence "((\<lambda>y. g (F y)) has_derivative (\<lambda>v. v \<bullet> (transpose (matrix J) *v dg))) (at x)"
    using Dcomp by simp

  thus ?thesis
    unfolding has_gradient_def .
qed

corollary GRAD_compose':
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes Gg: "GRAD g (F x) :> dg"
      and DF: "F differentiable (at x)"
  shows "GRAD (\<lambda>y. g (F y)) x :> transpose (jacobian F x) *v dg"
proof -
  have "(F has_derivative frechet_derivative F (at x)) (at x)"
    using DF by (simp add: frechet_derivative_worksI)
  thus ?thesis
    by (simp add: jacobian_def, metis GRAD_compose Gg transpose_matrix_vector)
qed

lemma grad_fun_compose:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes "\<exists>gg. GRAD g (F x) :> gg"
      and "F differentiable (at x)"
  shows "\<nabla> (\<lambda>y. g (F y)) x = transpose (jacobian F x) *v \<nabla> g (F x)"
proof -
  have Gg: "GRAD g (F x) :> \<nabla> g (F x)"
    using assms(1) by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. g (F y)) x :> transpose (jacobian F x) *v \<nabla> g (F x)"
    by (rule GRAD_compose'[OF Gg assms(2)])
  thus ?thesis
    by (rule grad_fun_eq)
qed


(* ================================================================== *)
subsection \<open>Component closure\<close>
(* ================================================================== *)

lemma Ck_on_component:
  fixes F :: "real^'n::finite \<Rightarrow> real^'m::finite"
  assumes "Ck_on k F U"
  shows "Ck_on k (\<lambda>x. F x $ r) U"
proof -
  have oU: "open U"
    using assms by (simp add: Ck_on_def)
  then have hF: "higher_differentiable_on U F k"
    using assms by (simp add: Ck_on_iff_higher_differentiable_on)

  have hcomp: "higher_differentiable_on U (\<lambda>x. F x $ r) k"
    using hF
  proof (induction k arbitrary: F)
    case 0
    then show ?case
      by (metis continuous_on_component higher_differentiable_on.simps(1))
  next
    case (Suc k)
    then have hdiff:
      "higher_differentiable_on U F (Suc k)"
      by simp
    have diffF: "\<forall>x\<in>U. F differentiable (at x)"
      using hdiff higher_differentiable_on.simps(2) by blast
    have diff_comp: "\<forall>x\<in>U. (\<lambda>x. F x $ r) differentiable (at x)"
    proof
      fix x
      assume xU: "x \<in> U"
      have FD: "(F has_derivative frechet_derivative F (at x)) (at x)"
        using diffF xU frechet_derivative_worksI by blast
      have Hcomp:"((\<lambda>y. F y \<bullet> axis r 1) has_derivative
            (\<lambda>h. frechet_derivative F (at x) h \<bullet> axis r 1)) (at x within UNIV)"
        using FD
        by (subst (asm) has_derivative_componentwise_within[where S=UNIV], auto simp: Basis_vec_def)
      have comp_fun: "(\<lambda>y. F y \<bullet> axis r 1) = (\<lambda>y. F y $ r)"
        by (rule ext) (simp add: cart_eq_inner_axis)
      have "((\<lambda>y. F y $ r) has_derivative (\<lambda>h. frechet_derivative F (at x) h $ r)) (at x)"
        using Hcomp by (simp add: inner_axis)
      then show "(\<lambda>x. F x $ r) differentiable (at x)"
        unfolding differentiable_def by blast
    qed
    have der_comp: "\<forall>v. higher_differentiable_on U
                   (\<lambda>x. frechet_derivative (\<lambda>x. F x $ r) (at x) v) k"
    proof
      fix v
      have eqU: "\<And>x. x \<in> U \<Longrightarrow> frechet_derivative (\<lambda>x. F x $ r) (at x) v =
                               frechet_derivative F (at x) v $ r"
      proof -
        fix x
        assume xU: "x \<in> U"
        have FD: "(F has_derivative frechet_derivative F (at x)) (at x)"
          using diffF xU frechet_derivative_worksI by blast
        have Hcomp:"((\<lambda>y. F y \<bullet> axis r 1) has_derivative
                     (\<lambda>h. frechet_derivative F (at x) h \<bullet> axis r 1)) (at x within UNIV)"
          using FD
          by (subst (asm) has_derivative_componentwise_within[where S=UNIV], auto simp: Basis_vec_def)
        have comp_fun: "(\<lambda>y. F y \<bullet> axis r 1) = (\<lambda>y. F y $ r)"
          by (rule ext) (simp add: cart_eq_inner_axis)
        have coord_D: "((\<lambda>y. F y $ r) has_derivative
                        (\<lambda>h. frechet_derivative F (at x) h $ r)) (at x)"
          using Hcomp by (simp add: cart_eq_inner_axis)
        have coord_FD: "frechet_derivative (\<lambda>y. F y $ r) (at x) =
                   (\<lambda>h. frechet_derivative F (at x) h $ r)"
          by (subst frechet_derivative_at[OF coord_D], simp)
        show "frechet_derivative (\<lambda>x. F x $ r) (at x) v = frechet_derivative F (at x) v $ r"
          by (simp add: coord_FD)
      qed
      have hderF:  "higher_differentiable_on U (\<lambda>x. frechet_derivative F (at x) v) k"
        using hdiff higher_differentiable_on.simps(2) by blast
      have "higher_differentiable_on U  (\<lambda>x. (frechet_derivative F (at x) v :: real^'m) $ r) k"
        using Suc.IH[OF hderF].
      then show "higher_differentiable_on U (\<lambda>x. frechet_derivative (\<lambda>x. F x $ r) (at x) v) k"
        using oU eqU by (subst higher_differentiable_on_cong, simp_all)
    qed
    then show ?case
      using diff_comp higher_differentiable_on.simps(2) by blast
  qed
  with oU show ?thesis
    by (simp add: Ck_on_iff_higher_differentiable_on)
qed


(* ================================================================== *)
subsection \<open>Hessian chain rule\<close>
(* ================================================================== *)


text \<open>
  Row extraction for a quadratic matrix product:
    \<open>(A\<^sup>T B A)\<^sub>i = \<Sigma>\<^sub>r A\<^sub>r\<^sub>i \<sqdot> (A\<^sup>T \<sqdot> B\<^sub>r)\<close>
  where \<open>B\<^sub>r\<close> is the \<open>r\<close>-th row of \<open>B\<close> viewed as a column vector.
\<close>

lemma row_transpose_mult_both:
  fixes A :: "real^'n^'m" and B :: "real^'m^'m"
  shows "(transpose A ** B ** A) $ i = (\<Sum>r\<in>UNIV. A $ r $ i *\<^sub>R (transpose A *v (B $ r)))"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix j :: 'n
  have "(transpose A ** B ** A) $ i $ j
      = (\<Sum>s\<in>UNIV. (transpose A ** B) $ i $ s * A $ s $ j)"
    by (simp add: matrix_matrix_mult_def)
  also have "\<dots> = (\<Sum>s\<in>UNIV. (\<Sum>r\<in>UNIV. A $ r $ i * B $ r $ s) * A $ s $ j)"
    by (simp add: matrix_matrix_mult_def transpose_def)
  also have "\<dots> = (\<Sum>s\<in>UNIV. \<Sum>r\<in>UNIV. A $ r $ i * B $ r $ s * A $ s $ j)"
    by (simp add: sum_distrib_right mult.assoc)
  also have "\<dots> = (\<Sum>r\<in>UNIV. \<Sum>s\<in>UNIV. A $ r $ i * B $ r $ s * A $ s $ j)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>r\<in>UNIV. A $ r $ i * (\<Sum>s\<in>UNIV. B $ r $ s * A $ s $ j))"
    by (simp add: sum_distrib_left mult.assoc)
  also have "\<dots> = (\<Sum>r\<in>UNIV. A $ r $ i * (\<Sum>s\<in>UNIV. A $ s $ j * B $ r $ s))"
    by (simp add: mult.commute)
  also have "\<dots> = (\<Sum>r\<in>UNIV. A $ r $ i * (transpose A *v (B $ r)) $ j)"
    by (simp add: matrix_vector_mult_def transpose_def)
  also have "\<dots> = (\<Sum>r\<in>UNIV. A $ r $ i *\<^sub>R (transpose A *v (B $ r))) $ j"
    by simp
  finally show "(Finite_Cartesian_Product.transpose A ** B ** A) $ i $ j =
          (\<Sum>r\<in>UNIV. A $ r $ i *\<^sub>R (Finite_Cartesian_Product.transpose A *v B $ r)) $ j"
    by simp
qed


text \<open>
  For \<open>g : \<real>ᵐ \<rightarrow> \<real>\<close> that is \<open>C²\<close> on \<open>V\<close> and \<open>F : \<real>ⁿ \<rightarrow> \<real>ᵐ\<close> that is
  \<open>C²\<close> on \<open>U\<close> with \<open>F(U) \<subseteq> V\<close>:

    \<open>\<nabla>²(g \<circ> F)(x) = Jᶠ(x)ᵀ \<^emph>\<^emph> \<nabla>²g(F(x)) \<^emph>\<^emph> Jᶠ(x) + \<Sigma>ᵣ (\<nabla>g(F(x)) $ r) *\<^sub>R \<nabla>²Fᵣ(x)\<close>

  where \<open>Jᶠ(x) = jacobian F x\<close> and \<open>Fᵣ(y) = F(y) $ r\<close>.
\<close>

lemma hessian_compose_on_C2:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes Cg: "Ck_on 2 g V"
      and CF: "Ck_on 2 F U"
      and FUV: "\<And>y. y \<in> U \<Longrightarrow> F y \<in> V"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. g (F y)) x =
           transpose (jacobian F x) ** \<nabla>\<^sup>2 g (F x) ** jacobian F x
         + (\<Sum>r\<in>UNIV. (\<nabla> g (F x) $ r) *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x)"
         (is "?LHS = ?RHS")
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i :: 'n

  have openU: "open U" using CF by (simp add: Ck_on_def)
  have openV: "open V" using Cg by (simp add: Ck_on_def)

  (* ---- C² closure: g \<circ> F is C² on U ---- *)
  have CgF: "Ck_on 2 (\<lambda>y. g (F y)) U"
    using Ck_on_compose[OF Cg CF FUV] .

  (* ---- Component C² ---- *)
  have CF_r: "\<And>r. Ck_on 2 (\<lambda>y. F y $ r) U"
    using CF by (rule Ck_on_component)

  (* ---- Hessians exist ---- *)
  have HgF: "HESS (\<lambda>y. g (F y)) x :> \<nabla>\<^sup>2 (\<lambda>y. g (F y)) x"
    using CgF xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g (F x) :> \<nabla>\<^sup>2 g (F x)"
    using Cg FUV[OF xU] by (rule Ck_2_imp_hessian_exists)
  have HF_r: "\<And>r. HESS (\<lambda>y. F y $ r) x :> \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x"
    using CF_r xU by (rule Ck_2_imp_hessian_exists)

  (* ---- Differentiability of F on U ---- *)
  have F_diff: "\<And>y. y \<in> U \<Longrightarrow> F differentiable (at y)"
  proof -
    fix y assume "y \<in> U"
    then have "Ck_at 2 F y"
      using CF by (simp add: Ck_on_def)
    thus "F differentiable (at y)"
      by (metis Ck_at.simps(2) Suc_1)
  qed

  (* ---- Gradient existence ---- *)
  have Gg_at: "\<And>z. z \<in> V \<Longrightarrow> GRAD g z :> \<nabla> g z"
    using Ck_2_imp_gradient_exists[OF Cg]
    by (blast intro: grad_fun_satisfies_GRAD)

  have GF_r_at: "\<And>r y. y \<in> U \<Longrightarrow> GRAD (\<lambda>y. F y $ r) y :> \<nabla> (\<lambda>y. F y $ r) y"
    using Ck_2_imp_gradient_exists[OF CF_r]
    by (blast intro: grad_fun_satisfies_GRAD)

  (* ---- Row gradients of component Hessians ---- *)
  have HF_r_row: "\<And>r. GRAD (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i) x :> (\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    by (rule HESS_row_gradient[OF HF_r])

  (* ---- Row gradient of the Hessian of g ---- *)
  have Hg_row: "\<And>r. GRAD (\<lambda>z. \<nabla> g z $ r) (F x) :> (\<nabla>\<^sup>2 g (F x)) $ r"
    by (rule HESS_row_gradient[OF Hg])

  (* ---- On U, \<nabla>(g \<circ> F)(y) $ i = \<Sigma>_r (\<nabla>(F_r)(y) $ i) * (\<nabla>g(F(y)) $ r) ---- *)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. g (F z)) y $ i"
  let ?\<psi> = "\<lambda>y. \<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r"

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y :: "real^'n"
    assume yU: "y \<in> U"

    have Fy_V: "F y \<in> V" using FUV[OF yU] .
    have Gy: "GRAD g (F y) :> \<nabla> g (F y)"
      using Gg_at[OF Fy_V] .
    have Fy_diff: "F differentiable (at y)"
      using F_diff[OF yU] .

    have grad_comp: "\<nabla> (\<lambda>z. g (F z)) y = transpose (jacobian F y) *v \<nabla> g (F y)"
      by (rule grad_fun_compose[where g=g and F=F], blast intro: Gy, rule Fy_diff)

    have "?\<phi> y = (transpose (jacobian F y) *v \<nabla> g (F y)) $ i"
      using grad_comp by simp
    also have "\<dots> = (\<Sum>r\<in>UNIV. transpose (jacobian F y) $ i $ r * \<nabla> g (F y) $ r)"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> = (\<Sum>r\<in>UNIV. jacobian F y $ r $ i * \<nabla> g (F y) $ r)"
      by (simp add: transpose_def)
    also have "\<dots> = ?\<psi> y"
    proof (rule sum.cong[OF refl])
      fix r :: 'm
      assume "r \<in> UNIV"

      have Fr_diff: "(\<lambda>z. F z $ r) differentiable (at y)"
      proof -
        have FD: "(F has_derivative frechet_derivative F (at y)) (at y)"
          using Fy_diff frechet_derivative_worksI by blast

        have Hcomp:"((\<lambda>z. F z \<bullet> axis r 1) has_derivative
                     (\<lambda>h. frechet_derivative F (at y) h \<bullet> axis r 1)) (at y within UNIV)"
          using FD
          by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
              auto simp: Basis_vec_def)

        have comp_fun: "(\<lambda>z. F z \<bullet> axis r 1) = (\<lambda>z. F z $ r)"
          by (rule ext) (simp add: cart_eq_inner_axis)
        have coord_D: "((\<lambda>z. F z $ r) has_derivative
                        (\<lambda>h. frechet_derivative F (at y) h $ r)) (at y)"
          using Hcomp by (simp add: inner_axis)
        then show ?thesis
          unfolding differentiable_def by blast
      qed

      show "jacobian F y $ r $ i * \<nabla> g (F y) $ r =  \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r"
      proof -
        have Jcomp: "jacobian F y $ r $ i = frechet_derivative (\<lambda>z. F z $ r) (at y) (axis i 1)"
          using jacobian_component[OF Fy_diff, of r i] by simp

        have GFr: "GRAD (\<lambda>z. F z $ r) y :> \<nabla> (\<lambda>z. F z $ r) y"
          using Fr_diff_imp_gradient_exists[OF Fr_diff]
          by (blast intro: grad_fun_satisfies_GRAD)

        have DFr: "((\<lambda>z. F z $ r) has_derivative (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) y)) (at y)"
          using GFr unfolding has_gradient_def by simp

        have FD_eq:  "frechet_derivative (\<lambda>z. F z $ r) (at y) = (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) y)"
          by (subst frechet_derivative_at[OF DFr], simp)

        have "frechet_derivative (\<lambda>z. F z $ r) (at y) (axis i 1)
              = axis i 1 \<bullet> \<nabla> (\<lambda>z. F z $ r) y"
          by (simp add: FD_eq)
        also have "... = \<nabla> (\<lambda>z. F z $ r) y $ i"
          using inner_commute by (simp add: cart_eq_inner_axis, auto)
        finally show ?thesis
          using Jcomp by simp
      qed
      then have "jacobian F y $ r $ i = \<nabla> (\<lambda>z. F z $ r) y $ i"
        using jacobian_component[OF Fy_diff]
        by (metis (mono_tags, lifting) Fr_diff Fr_diff_imp_gradient_exists cart_eq_inner_axis
            frechet_derivative_at grad_fun_eq has_gradient_def inner_commute)
      qed
      thus "\<nabla> (\<lambda>z. g (F z)) y $ i = (\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r)"
        using calculation by presburger
  qed

  (* ---- Differentiate \<psi> at x using GRAD_sum, GRAD_mult ---- *)
  (*
     \<psi>(y) = \<Sigma>_r  a_r(y) * b_r(y)
     where a_r(y) = \<nabla>(F_r)(y) $ i  and  b_r(y) = \<nabla>g(F(y)) $ r.

     GRAD a_r(x) = (\<nabla>²(F_r)(x)) $ i       [by HESS_row_gradient]
     GRAD b_r(x) = transpose(J_F(x)) *v (\<nabla>²g(F(x)) $ r)  [by GRAD_compose']

     By GRAD_mult:
     GRAD (a_r \<sqdot> b_r)(x) = a_r(x) *\<^sub>R GRAD b_r(x) + b_r(x) *\<^sub>R GRAD a_r(x)

     By GRAD_sum:
     GRAD \<psi>(x) = \<Sigma>_r [a_r(x) *\<^sub>R GRAD b_r(x) + b_r(x) *\<^sub>R GRAD a_r(x)]
  *)

  have Ga_r: "\<And>r. GRAD (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i) x :> (\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    using HF_r_row .

  have Gb_r: "\<And>r. GRAD (\<lambda>y. \<nabla> g (F y) $ r) x :> transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)"
  proof -
    fix r :: 'm
    have "GRAD (\<lambda>z. \<nabla> g z $ r) (F x) :> (\<nabla>\<^sup>2 g (F x)) $ r"
      using Hg_row .
    thus "GRAD (\<lambda>y. \<nabla> g (F y) $ r) x :> transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)"
      by (rule GRAD_compose'[OF _ F_diff[OF xU]])
  qed

  have G_term_r: "\<And>r. GRAD (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r) x :>
      \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r))
    + \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i)"
    by (rule GRAD_mult[OF Ga_r Gb_r])

  define G_r where "G_r r =
      \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r))
    + \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i)" for r

  have G\<psi>: "GRAD ?\<psi> x :> (\<Sum>r\<in>UNIV. G_r r)"
  proof -
    have "\<And>r. r \<in> (UNIV :: 'm set) \<Longrightarrow>
      GRAD (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r) x :> G_r r"
      using G_term_r by (simp add: G_r_def)
    thus ?thesis
      by (rule GRAD_sum[OF finite_class.finite_UNIV])
  qed

  (* ---- Transfer from \<psi> to \<phi> ---- *)
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> (\<Sum>r\<in>UNIV. G_r r))) (at x)"
    using G\<psi> unfolding has_gradient_def .

  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> (\<Sum>r\<in>UNIV. G_r r))) (at x)"
    using D\<psi> eqU has_derivative_transform_within_open openU xU by fastforce

  have G\<phi>: "GRAD ?\<phi> x :> (\<Sum>r\<in>UNIV. G_r r)"
    using D\<phi> unfolding has_gradient_def by simp

  have row_eq: "\<nabla> ?\<phi> x = (\<Sum>r\<in>UNIV. G_r r)"
    by (rule grad_fun_eq[OF G\<phi>])

  have lhs: "?LHS $ i = \<nabla> ?\<phi> x"
    using HESS_row_eq[OF HgF] by simp

  (* ---- Match the RHS row ---- *)
  (*
     ?RHS $ i = [J^T ** \<nabla>²g(F x) ** J] $ i + [\<Sigma>_r (\<nabla>g(F x)$r) *\<^sub>R \<nabla>²(F_r)(x)] $ i

     We need: \<Sigma>_r G_r(r) = ?RHS $ i

     Expand G_r(r):
       G_r r = a_r(x) *\<^sub>R [J^T *v (\<nabla>²g(F x) $ r)]  +  b_r(x) *\<^sub>R [(\<nabla>²(F_r) x) $ i]

     \<Sigma>_r b_r(x) *\<^sub>R [(\<nabla>²(F_r) x) $ i]  =  [\<Sigma>_r \<nabla>g(F x)$r *\<^sub>R \<nabla>²(F_r)(x)] $ i   \<checkmark>

     \<Sigma>_r a_r(x) *\<^sub>R [J^T *v (\<nabla>²g(F x) $ r)]  =  [J^T ** \<nabla>²g(F x) ** J] $ i
     This is the key matrix algebra step.
  *)

  have sum_second: "(\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i))
                  = (\<Sum>r\<in>UNIV. (\<nabla> g (F x) $ r) *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    by simp

  (* matrix algebra: the key identity relating the sum to J^T H J *)
  have sum_first: "(\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R
                      (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))
                 = (transpose (jacobian F x) ** \<nabla>\<^sup>2 g (F x) ** jacobian F x) $ i"
  proof -
    have grad_jac: "\<nabla> (\<lambda>z. F z $ r) x $ i = jacobian F x $ r $ i" for r
    proof -
      have Fr_diff: "(\<lambda>z. F z $ r) differentiable (at x)"
        using F_diff[OF xU] by (metis CF_r Ck_at.simps(2) Ck_on_def Suc_1 xU)
      have GFr: "GRAD (\<lambda>z. F z $ r) x :> \<nabla> (\<lambda>z. F z $ r) x"
        using Fr_diff_imp_gradient_exists[OF Fr_diff]
        by (blast intro: grad_fun_satisfies_GRAD)
      have FD_eq: "frechet_derivative (\<lambda>z. F z $ r) (at x) = (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) x)"
        using GFr unfolding has_gradient_def  by (metis frechet_derivative_at)
      have "jacobian F x $ r $ i = frechet_derivative (\<lambda>z. F z $ r) (at x) (axis i 1)"
        using jacobian_component[OF F_diff[OF xU]].
      also have "\<dots> = \<nabla> (\<lambda>z. F z $ r) x $ i"
        by (simp add: FD_eq cart_eq_inner_axis inner_commute,
            metis (no_types, lifting) ext FD_eq cart_eq_inner_axis)
      finally show ?thesis by simp
    qed
    then have "(\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R  (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))
        = (\<Sum>r\<in>UNIV. jacobian F x $ r $ i *\<^sub>R   (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))"
      by simp
    also have "\<dots> = (transpose (jacobian F x) ** \<nabla>\<^sup>2 g (F x) ** jacobian F x) $ i"
      by (rule row_transpose_mult_both[symmetric])
    finally show ?thesis.
  qed
  then have "(\<Sum>r\<in>UNIV. G_r r) = ?RHS $ i"
    unfolding G_r_def by (metis (no_types) sum.distrib sum_second vector_add_component)
  then show "?LHS $ i = ?RHS $ i"
    using lhs row_eq by simp
qed


(* ================================================================== *)
subsection \<open>Affine composition (special case)\<close>
(* ================================================================== *)

text \<open>
  If \<open>F(y) = A *v y + b\<close> is affine, then \<open>Jᶠ = A\<close> is constant and each
  \<open>\<nabla>²Fᵣ = 0\<close>, so the chain rule simplifies to:

    \<open>\<nabla>²(g \<circ> F)(x) = Aᵀ \<^emph>\<^emph> \<nabla>²g(A *v x + b) \<^emph>\<^emph> A\<close>
\<close>

lemma hessian_affine_compose_on_C2:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and A :: "real^'n^'m"
    and b :: "real^'m"
  assumes Cg: "Ck_on 2 g V"
      and sub: "\<And>y. y \<in> U \<Longrightarrow> A *v y + b \<in> V"
      and oU: "open U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. g (A *v y + b)) x = transpose A ** \<nabla>\<^sup>2 g (A *v x + b) ** A"
proof -
  define F where "F y = A *v y + b" for y
  have bl: "bounded_linear ((*v) A)"
    by simp
  then have f1: "higher_differentiable_on U ((*v) A) 2"
    using bounded_linear.higher_differentiable_on by blast
  have "higher_differentiable_on U (\<lambda>y. A *v y + b) 2"
      using oU f1 by (subst higher_differentiable_on_add, auto,
                      simp add: higher_differentiable_on_const)
  then have CF: "Ck_on 2 F U"
    unfolding F_def using oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have F_diff: "\<And>y. F differentiable (at y)"
    unfolding F_def by (simp add: bounded_linear_imp_differentiable)
  have jac_eq: "jacobian F y = A" for y
    unfolding jacobian_def F_def by (metis bl bounded_linear_imp_has_derivative
              frechet_derivative_at has_derivative_add_const matrix_of_matrix_vector_mul)
  have comp_hess_zero: "\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x = 0" for r
  proof -
    have fn_eq: "(\<lambda>y. F y $ r) = (\<lambda>y. b $ r + y \<bullet> (A $ r))"
    proof (rule ext)
      fix y :: "real^'n"
      have "F y $ r = (A *v y + b) $ r"
        by (simp add: F_def)
      also have "\<dots> = (\<Sum>j\<in>UNIV. A $ r $ j * y $ j) + b $ r"
        by (simp add: matrix_vector_mult_def)
      also have "\<dots> = b $ r + y \<bullet> (A $ r)"
        by (simp add: inner_vec_def, meson mult.commute)
      finally show "F y $ r = b $ r + y \<bullet> (A $ r)".
    qed
    have "HESS (\<lambda>y. b $ r + y \<bullet> (A $ r)) x :> 0"
      by (rule HESS_affine_zero)
    hence "HESS (\<lambda>y. F y $ r) x :> 0"
      by (simp add: fn_eq)
    thus ?thesis
      by (metis hess_fun_eq)
  qed
  then have grad_zero_sum: "(\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) = 0"
    by simp
  have "\<nabla>\<^sup>2 (\<lambda>y. g (F y)) x =
         transpose (jacobian F x) ** \<nabla>\<^sup>2 g (F x) ** jacobian F x
       + (\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x)"
    by (rule hessian_compose_on_C2[OF Cg CF _ xU], simp add: F_def sub)
  also have "\<dots> = transpose A ** \<nabla>\<^sup>2 g (F x) ** A + 0"
    by (simp add: jac_eq grad_zero_sum)
  also have "\<dots> = transpose A ** \<nabla>\<^sup>2 g (A *v x + b) ** A"
    by (simp add: F_def)
  ultimately show ?thesis by (simp add: F_def)
qed

(* ================================================================== *)
subsection \<open>Summary of the hierarchy\<close>
(* ================================================================== *)

text \<open>
  \<^bold>\<open>At a point:\<close>
  @{term "k_times_Fr_differentiable_at k f x"}
  \<open>\<Longleftarrow>\<close>  @{term "Ck_at k f x"}
  In 1-d (\<open>f :: real \<Rightarrow> real\<close>):
  @{term "k_times_Fr_differentiable_at k f x"} \<open>\<longleftrightarrow>\<close> @{term "k_times_differentiable_at k f x"}
  \<^bold>\<open>On an open set:\<close>
  @{term "k_times_Fr_differentiable_on k f U"}
  \<open>\<Longleftarrow>\<close>  @{term "Ck_on k f U"}
  \<open>\<longleftrightarrow>\<close>  @{term "higher_differentiable_on U f k"} (when \<open>U\<close> is open)
  In 1-d:
  @{term "Ck_on k f U"} \<open>\<longleftrightarrow>\<close> @{term "C_k_on k f U"}
\<close>

end
