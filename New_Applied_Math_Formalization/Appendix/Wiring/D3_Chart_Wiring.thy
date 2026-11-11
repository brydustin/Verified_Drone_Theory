theory D3_Chart_Wiring
  imports "Applied_Math_Appendix_Frontier.Nonemptiness_Robust4"
          "Applied_Math_D34_Analytic.D34_Geodesic_Branch"
begin

section \<open>Wiring the geodesic-branch rank criteria toward \<open>d3_detHess_arc_chart_core_all\<close>\<close>

text \<open>\<^bold>\<open>Architecture.\<close>  This theory is the FIRST theory that sees both heaps: the
  Robust4 frontier (which defines the honest boundary predicate
  \<open>d3_detHess_arc_chart_core_all\<close> consumed by \<open>F0_dip_nonempty\<close>) and the geodesic
  branch (which provides the rank-3 criteria \<open>Jac3_22\<close> / \<open>Jac3\<close> / \<open>Jac3_H0cub\<close> with
  generic satisfaction and concrete witnesses).  Its job is the glue:

  \<^enum> FIBRE FACTS: on the \<open>D3BadXG_H0core\<close> fibre the first two rank-criterion rows
    vanish (\<open>Phi_par = 0\<close>, \<open>gradU\<^sub>2 = 0\<close>);
  \<^enum> the BRANCH TRICHOTOMY: \<open>det HessU = 0\<close> splits into \<open>H\<^sub>2\<^sub>2 \<noteq> 0\<close> (Jac3_22 branch),
    \<open>H\<^sub>2\<^sub>2 = 0 \<and> H\<^sub>1\<^sub>1 \<noteq> 0\<close> (Jac3 branch), or --- by symmetry of the Hessian ---
    \<open>HessU = 0\<close> entirely (the Tier 6 cubic branch);
  \<^enum> the remaining engine gap, stated precisely at the end.\<close>

subsection \<open>Fibre facts\<close>

lemma H0core_fibre_Phi_par_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite"
  assumes gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "Phi_par x \<omega> \<omega>0 \<omega>s = 0"
  by (rule Phi_par_zero_of_gradU_zero[OF gz])

lemma H0core_fibre_gradU2_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite"
  assumes gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2 = 0"
  unfolding gz by simp

subsection \<open>The branch trichotomy for \<open>det HessU = 0\<close>\<close>

lemma detHess_zero_cases:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite"
  assumes dz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2 \<noteq> 0
       \<or> (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2 = 0
          \<and> HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1 \<noteq> 0)
       \<or> HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
proof (cases "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2 = 0")
  case False
  thus ?thesis by blast
next
  case H22: True
  show ?thesis
  proof (cases "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1 = 0")
    case False
    with H22 show ?thesis by blast
  next
    case H11: True
    \<comment> \<open>diagonal zero + det zero + symmetry \<Longrightarrow> the whole Hessian vanishes\<close>
    have det2: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
        = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
            * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
        - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
            * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
      by (simp add: det_2)
    have sym: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
        = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
      by (rule HessU_dip_symmetric)
    have H12: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2 = 0"
    proof -
      have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
          * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2 = 0"
        using dz det2 H11 H22 sym by simp
      thus ?thesis by simp
    qed
    have Hz: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
      fix k :: 2
      show "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k = (0::real^2^2) $ k"
      proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
        fix l :: 2
        have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l = 0"
          using exhaust_2[of k] exhaust_2[of l] H11 H22 H12 sym H12[unfolded sym]
          by (metis (full_types))
        thus "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l = (0::real^2^2) $ k $ l"
          by (simp add: zero_index)
      qed
    qed
    thus ?thesis by blast
  qed
qed

text \<open>\<^bold>\<open>The remaining engine gap, stated precisely.\<close>  For each fibre point the
  trichotomy selects a rank-3 criterion whose side conditions hold generically
  (\<open>Jac3_H12rad_nonzero_in_open_robust4_witness\<close> /
  \<open>Jac3_H0cub_nonzero_in_open_robust4_witness\<close> at the design point).  What converts
  "the fibre is locally inside a level set of a \<open>C\<^sup>1\<close> triple with rank-3 x-derivative"
  into the \<open>charts/Crit/D\<close> data of \<open>d3_detHess_arc_chart_core\<close> is a
  level-set-to-rank-deficient-closed-cover engine: locally parametrize the codim-3
  level set, compose with inclusion to get self-maps of configuration space with
  rank \<open>\<le> 2N - 3\<close> derivatives, and exhaust by closed pieces.  That engine is the
  next tier; this theory pins its interface.\<close>


section \<open>The scalar-cut engine: level-set pieces to rank-deficient chart data\<close>

text \<open>\<^bold>\<open>The decisive simplification.\<close>  The chart-core predicate demands only
  \<open>\<not> surj\<close> derivatives, and permits the chart maps to be the IDENTITY on each piece.
  If a closed piece \<open>C\<close> lies in the zero set of ONE scalar function \<open>f\<close> whose
  derivative at \<open>x \<in> C\<close> is \<open>v \<mapsto> g \<bullet> v\<close> with \<open>g \<noteq> 0\<close>, then the identity has
  within-\<open>C\<close> derivative equal to the tangential projection
  \<open>P v = v - ((g \<bullet> v)/(g \<bullet> g)) \<cdot> g\<close>: the auxiliary map
  \<open>\<psi> w = w - (f w/(g \<bullet> g)) \<cdot> g\<close> EQUALS the identity on \<open>C\<close> (where \<open>f \<equiv> 0\<close>) and has
  full-space derivative exactly \<open>P\<close>, so \<open>has_derivative_transform_within\<close> does all the
  analytic work --- no \<open>\<epsilon>\<close>-\<open>\<delta>\<close>, no IFT, no projection machinery.  \<open>P\<close> is explicitly
  non-surjective (its range is orthogonal to \<open>g\<close>).  Consequently the ENTIRE remaining
  D3 gap reduces to: produce countably many closed pieces covering the arc-fibre, each
  inside a scalar cut with nonvanishing gradient.\<close>

subsection \<open>The tangential projection: linearity and non-surjectivity\<close>

lemma tangential_projection_bounded_linear:
  fixes g :: "'a::real_inner"
  shows "bounded_linear (\<lambda>v. v - ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g)"
proof -
  have inner_bl: "bounded_linear (\<lambda>v. (g \<bullet> v) / (g \<bullet> g))"
    using bounded_linear_compose[OF bounded_linear_mult_left bounded_linear_inner_right]
    by (simp add: divide_inverse)
  have "bounded_linear (\<lambda>v. ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g)"
    by (rule bounded_linear_compose[OF bounded_linear_scaleR_left inner_bl])
  thus ?thesis
    by (intro bounded_linear_sub bounded_linear_ident)
qed

lemma tangential_projection_not_surj:
  fixes g :: "'a::real_inner"
  assumes gnz: "g \<noteq> 0"
  shows "\<not> surj (\<lambda>v. v - ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g)"
proof
  assume s: "surj (\<lambda>v. v - ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g)"
  then obtain v where veq: "v - ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g = g"
    by (metis (no_types, lifting) surjD)
  have ggnz: "g \<bullet> g \<noteq> 0"
    using gnz by simp
  have "(v - ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g) \<bullet> g = 0"
    using ggnz by (simp add: inner_diff_left inner_commute divide_inverse inner_diff_right)
  with veq have "g \<bullet> g = 0"
    by (simp only: inner_commute)
  with ggnz show False by simp
qed

subsection \<open>The within-derivative of the identity at a scalar cut\<close>

lemma scalar_cut_id_within_derivative:
  fixes C :: "'a::real_inner set" and x g :: 'a and f :: "'a \<Rightarrow> real"
  assumes xC: "x \<in> C"
    and df: "(f has_derivative (\<lambda>v. g \<bullet> v)) (at x)"
    and f0: "\<And>y. y \<in> C \<Longrightarrow> f y = 0"
  shows "((\<lambda>w. w) has_derivative (\<lambda>v. v - ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g)) (at x within C)"
proof -
  have d0: "((\<lambda>w. (f w / (g \<bullet> g)) *\<^sub>R g) has_derivative
      (\<lambda>v. ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g)) (at x)"
  proof -
    have d1: "((\<lambda>w. f w / (g \<bullet> g)) has_derivative (\<lambda>v. (g \<bullet> v) / (g \<bullet> g))) (at x)"
      using bounded_linear.has_derivative[OF bounded_linear_mult_left df]
      by (simp add: divide_inverse)
    show ?thesis
      by (rule bounded_linear.has_derivative[OF bounded_linear_scaleR_left d1])
  qed
  have hpsi: "((\<lambda>w. w - (f w / (g \<bullet> g)) *\<^sub>R g) has_derivative
      (\<lambda>v. v - ((g \<bullet> v) / (g \<bullet> g)) *\<^sub>R g)) (at x within C)"
    by (rule has_derivative_at_withinI[OF has_derivative_diff[OF has_derivative_ident d0]])
  show ?thesis
    by (metis (no_types, lifting) 
        arith_simps(57) assms(1) div_0 f0 has_derivative_transform hpsi scaleR_simps(7))  
qed

subsection \<open>Assembling the chart-core data from countable closed scalar cuts\<close>

theorem chart_core_data_of_scalar_cuts:
  fixes S :: "((real^2)^'n::finite) set"
    and C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and f :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
    and G :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (real^2)^'n"
  assumes cover: "S \<subseteq> (\<Union>i. C i)"
    and closedC: "\<And>i. closed (C i)"
    and cut0: "\<And>i y. y \<in> C i \<Longrightarrow> f i y = 0"
    and cutd: "\<And>i x. x \<in> C i \<Longrightarrow> (f i has_derivative (\<lambda>v. G i x \<bullet> v)) (at x)"
    and Gnz: "\<And>i x. x \<in> C i \<Longrightarrow> G i x \<noteq> 0"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define P where "P = (\<lambda>i x v. v - ((G i x \<bullet> v) / (G i x \<bullet> G i x)) *\<^sub>R G i x)"
  define D where "D = (\<lambda>i x. Blinfun (P i x))"
  define charts where "charts = (\<lambda>(i::nat) (w :: (real^2)^'n). (w, 0::real^2))"
  have fst_id: "(fst \<circ> charts i) = (\<lambda>w. w)" for i
    unfolding charts_def by (simp add: o_def)
  have appD: "blinfun_apply (D i x) = P i x" for i x
    unfolding D_def
    by (rule bounded_linear_Blinfun_apply)
       (simp add: P_def tangential_projection_bounded_linear)
  have cov: "S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (C i))"
    using cover unfolding fst_id by simp
  have der: "\<forall>i x. x \<in> C i \<longrightarrow>
      ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within C i)"
  proof (intro allI impI)
    fix i x assume xC: "x \<in> C i"
    have "((\<lambda>w. w) has_derivative (P i x)) (at x within C i)"
      unfolding P_def
      by (rule scalar_cut_id_within_derivative[OF xC cutd[OF xC] cut0])
    thus "((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within C i)"
      unfolding fst_id appD .
  qed
  have nsurj: "\<forall>i x. x \<in> C i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
  proof (intro allI impI)
    fix i x assume xC: "x \<in> C i"
    show "\<not> surj (blinfun_apply (D i x))"
      unfolding appD P_def
      by (rule tangential_projection_not_surj[OF Gnz[OF xC]])
  qed
  have cls: "\<forall>i. closed ((fst \<circ> charts i) ` (C i))"
    unfolding fst_id using closedC by simp
  show ?thesis
    by (intro exI[of _ charts] exI[of _ C] exI[of _ D] conjI cov der nsurj cls)
qed


section \<open>The functional-cut engine: scalar cuts with an explicit direction\<close>

lemma functional_cut_projection_bounded_linear:
  fixes L :: "'a::real_normed_vector \<Rightarrow> real" and r :: 'a
  assumes bl: "bounded_linear L"
  shows "bounded_linear (\<lambda>v. v - (L v / L r) *\<^sub>R r)"
proof -
  have "bounded_linear (\<lambda>v. L v / L r)"
    using bounded_linear_compose[OF bounded_linear_mult_left bl]
    by (simp add: divide_inverse)
  hence "bounded_linear (\<lambda>v. (L v / L r) *\<^sub>R r)"
    by (rule bounded_linear_compose[OF bounded_linear_scaleR_left])
  thus ?thesis
    by (intro bounded_linear_sub bounded_linear_ident)
qed

lemma functional_cut_projection_not_surj:
  fixes L :: "'a::real_normed_vector \<Rightarrow> real" and r :: 'a
  assumes bl: "bounded_linear L" and rnz: "L r \<noteq> 0"
  shows "\<not> surj (\<lambda>v. v - (L v / L r) *\<^sub>R r)"
proof
  assume s: "surj (\<lambda>v. v - (L v / L r) *\<^sub>R r)"
  then obtain v where veq: "v - (L v / L r) *\<^sub>R r = r"
    by (metis (no_types, lifting) surjD)
  interpret L: bounded_linear L
    by (rule bl)
  have "L (v - (L v / L r) *\<^sub>R r) = L v - (L v / L r) * L r"
    by (simp add: L.diff L.scaleR)
  also have "\<dots> = 0"
    using rnz by simp
  finally have "L r = 0"
    using veq by simp
  with rnz show False by simp
qed

lemma functional_cut_id_within_derivative:
  fixes C :: "'a::real_normed_vector set" and x r :: 'a
    and f :: "'a \<Rightarrow> real" and L :: "'a \<Rightarrow> real"
  assumes xC: "x \<in> C"
    and df: "(f has_derivative L) (at x)"
    and rnz: "L r \<noteq> 0"
    and f0: "\<And>y. y \<in> C \<Longrightarrow> f y = 0"
  shows "((\<lambda>w. w) has_derivative (\<lambda>v. v - (L v / L r) *\<^sub>R r)) (at x within C)"
proof -
  have d1: "((\<lambda>w. f w / L r) has_derivative (\<lambda>v. L v / L r)) (at x)"
    using bounded_linear.has_derivative[OF bounded_linear_mult_left df]
    by (simp add: divide_inverse)
  have d0: "((\<lambda>w. (f w / L r) *\<^sub>R r) has_derivative (\<lambda>v. (L v / L r) *\<^sub>R r)) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_scaleR_left d1])
  have hpsi: "((\<lambda>w. w - (f w / L r) *\<^sub>R r) has_derivative
      (\<lambda>v. v - (L v / L r) *\<^sub>R r)) (at x within C)"
    by (rule has_derivative_at_withinI[OF has_derivative_diff[OF has_derivative_ident d0]])
  have agree: "\<And>y. y \<in> C \<Longrightarrow> y - (f y / L r) *\<^sub>R r = y"
    by (simp add: f0)
  show ?thesis
    by (rule has_derivative_transform[OF xC _ hpsi]) (simp add: agree)
qed

theorem chart_core_data_of_functional_cuts:
  fixes S :: "((real^2)^'n::finite) set"
    and C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and f :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
    and L :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
    and r :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (real^2)^'n"
  assumes cover: "S \<subseteq> (\<Union>i. C i)"
    and closedC: "\<And>i. closed (C i)"
    and cut0: "\<And>i y. y \<in> C i \<Longrightarrow> f i y = 0"
    and cutd: "\<And>i x. x \<in> C i \<Longrightarrow> (f i has_derivative L i x) (at x)"
    and rnz: "\<And>i x. x \<in> C i \<Longrightarrow> L i x (r i x) \<noteq> 0"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define P where "P = (\<lambda>i x v. v - (L i x v / L i x (r i x)) *\<^sub>R r i x)"
  define D where "D = (\<lambda>i x. Blinfun (P i x))"
  define charts where "charts = (\<lambda>(i::nat) (w :: (real^2)^'n). (w, 0::real^2))"
  have fst_id: "(fst \<circ> charts i) = (\<lambda>w. w)" for i
    unfolding charts_def by (simp add: o_def)
  have blL: "bounded_linear (L i x)" if "x \<in> C i" for i x
    by (rule has_derivative_bounded_linear[OF cutd[OF that]])
  have appD: "blinfun_apply (D i x) = P i x" if "x \<in> C i" for i x
    unfolding D_def
    by (rule bounded_linear_Blinfun_apply)
       (simp add: P_def functional_cut_projection_bounded_linear[OF blL[OF that]])
  have cov: "S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (C i))"
    using cover unfolding fst_id by simp
  have der: "\<forall>i x. x \<in> C i \<longrightarrow>
      ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within C i)"
  proof (intro allI impI)
    fix i x assume xC: "x \<in> C i"
    have "((\<lambda>w. w) has_derivative (P i x)) (at x within C i)"
      unfolding P_def
      by (rule functional_cut_id_within_derivative[OF xC cutd[OF xC] rnz[OF xC] cut0])
    thus "((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within C i)"
      unfolding fst_id appD[OF xC] .
  qed
  have nsurj: "\<forall>i x. x \<in> C i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
  proof (intro allI impI)
    fix i x assume xC: "x \<in> C i"
    show "\<not> surj (blinfun_apply (D i x))"
      unfolding appD[OF xC] P_def
      by (rule functional_cut_projection_not_surj[OF blL[OF xC] rnz[OF xC]])
  qed
  have cls: "\<forall>i. closed ((fst \<circ> charts i) ` (C i))"
    unfolding fst_id using closedC by simp
  show ?thesis
    by (intro exI[of _ charts] exI[of _ C] exI[of _ D] conjI cov der nsurj cls)
qed


section \<open>The vector-cut engine: joint vector-valued cuts\<close>

text \<open>Generalizes @{thm chart_core_data_of_scalar_cuts} from a single
  scalar cut (corank 1) to a vector-valued cut \<open>f : 'a \<Rightarrow> 'b\<close> (corank
  \<open>DIM('b)\<close>), given a pointwise bounded-linear right inverse \<open>W\<close> of the
  cut's derivative \<open>L\<close> (i.e. \<open>L (W t) = t\<close> for all \<open>t\<close>).  The same
  \<psi>-transform trick applies: \<open>\<psi>(w) = w - W (f w)\<close> equals the identity on
  the cut (where \<open>f \<equiv> 0\<close>) and has full derivative the projection
  \<open>P(v) = v - W (L v)\<close>.  This is the corank-\<open>k\<close> chart-core engine needed
  by the remaining D3 mixed-IFT wiring.\<close>

lemma vector_cut_projection_bounded_linear:
  fixes L :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and W :: "'b \<Rightarrow> 'a"
  assumes lL: "bounded_linear L" and lW: "bounded_linear W"
  shows "bounded_linear (\<lambda>v. v - W (L v))"
  by (intro bounded_linear_sub bounded_linear_ident
        bounded_linear_compose[OF lW lL])

lemma vector_cut_projection_not_surj:
  fixes L :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
    and W :: "'b \<Rightarrow> 'a"
  assumes lin_L: "linear L"
    and right_inv: "\<And>t. L (W t) = t"
  shows "\<not> surj (\<lambda>v. v - W (L v))"
proof
  assume s: "surj (\<lambda>v. v - W (L v))"
  obtain b :: 'b where bB: "b \<in> Basis"
    using nonempty_Basis by blast
  have bnz: "b \<noteq> 0"
    using norm_Basis[OF bB] by auto
  have "\<exists>v. W b = v - W (L v)"
    using s unfolding surj_def by blast
  then obtain v where veq: "W b = v - W (L v)"
    by blast
  have chain: "L (W b) = 0"
  proof -
    have "L (W b) = L (v - W (L v))"
      using veq by simp
    also have "\<dots> = L v - L (W (L v))"
      by (rule linear_diff[OF lin_L])
    also have "\<dots> = L v - L v"
      using right_inv by simp
    also have "\<dots> = 0"
      by simp
    finally show ?thesis .
  qed
  have "b = 0"
    using chain right_inv[of b] by simp
  thus False
    using bnz by simp
qed

lemma vector_cut_id_within_derivative:
  fixes C :: "'a::real_normed_vector set" and x :: 'a
    and f :: "'a \<Rightarrow> 'b::euclidean_space" and L :: "'a \<Rightarrow> 'b" and W :: "'b \<Rightarrow> 'a"
  assumes xC: "x \<in> C"
    and df: "(f has_derivative L) (at x)"
    and blW: "bounded_linear W"
    and f0: "\<And>y. y \<in> C \<Longrightarrow> f y = 0"
  shows "((\<lambda>w. w) has_derivative (\<lambda>v. v - W (L v))) (at x within C)"
proof -
  have d0: "((\<lambda>w. W (f w)) has_derivative (\<lambda>v. W (L v))) (at x)"
    by (rule bounded_linear.has_derivative[OF blW df])
  have hpsi: "((\<lambda>w. w - W (f w)) has_derivative (\<lambda>v. v - W (L v))) (at x within C)"
    by (rule has_derivative_at_withinI[OF has_derivative_diff[OF has_derivative_ident d0]])
  have eq_on_C: "\<And>w. w \<in> C \<Longrightarrow> w = w - W (f w)"
    using f0 linear_0[OF bounded_linear.linear[OF blW]] by fastforce
  show ?thesis
    by (rule has_derivative_transform[OF xC eq_on_C hpsi])
qed

theorem chart_core_data_of_vector_cuts:
  fixes S :: "((real^2)^'n::finite) set"
    and C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and f :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b::euclidean_space"
    and L :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b"
    and W :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b \<Rightarrow> (real^2)^'n"
  assumes cover: "S \<subseteq> (\<Union>i. C i)"
    and closedC: "\<And>i. closed (C i)"
    and cut0: "\<And>i y. y \<in> C i \<Longrightarrow> f i y = 0"
    and cutd: "\<And>i x. x \<in> C i \<Longrightarrow> (f i has_derivative L i x) (at x)"
    and Wbl: "\<And>i x. x \<in> C i \<Longrightarrow> bounded_linear (W i x)"
    and Wright: "\<And>i x t. x \<in> C i \<Longrightarrow> L i x (W i x t) = t"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define P where "P = (\<lambda>i x v. v - W i x (L i x v))"
  define D where "D = (\<lambda>i x. Blinfun (P i x))"
  define charts where "charts = (\<lambda>(i::nat) (w :: (real^2)^'n). (w, 0::real^2))"
  have fst_id: "(fst \<circ> charts i) = (\<lambda>w. w)" for i
    unfolding charts_def by (simp add: o_def)
  have blL: "bounded_linear (L i x)" if "x \<in> C i" for i x
    by (rule has_derivative_bounded_linear[OF cutd[OF that]])
  have blP: "bounded_linear (P i x)" if "x \<in> C i" for i x
    unfolding P_def
    by (rule vector_cut_projection_bounded_linear[OF blL[OF that] Wbl[OF that]])
  have appD: "blinfun_apply (D i x) = P i x" if "x \<in> C i" for i x
    unfolding D_def
    by (rule bounded_linear_Blinfun_apply) (rule blP[OF that])
  have cov: "S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (C i))"
    using cover unfolding fst_id by simp
  have der: "\<forall>i x. x \<in> C i \<longrightarrow>
      ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within C i)"
  proof (intro allI impI)
    fix i x assume xC: "x \<in> C i"
    have "((\<lambda>w. w) has_derivative (P i x)) (at x within C i)"
      unfolding P_def
      by (rule vector_cut_id_within_derivative[OF xC cutd[OF xC] Wbl[OF xC] cut0])
    thus "((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within C i)"
      unfolding fst_id appD[OF xC] .
  qed
  have nsurj: "\<forall>i x. x \<in> C i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
  proof (intro allI impI)
    fix i x assume xC: "x \<in> C i"
    show "\<not> surj (blinfun_apply (D i x))"
      unfolding appD[OF xC] P_def
      by (rule vector_cut_projection_not_surj
            [OF bounded_linear.linear[OF blL[OF xC]] Wright[OF xC]])
  qed
  have cls: "\<forall>i. closed ((fst \<circ> charts i) ` (C i))"
    unfolding fst_id using closedC by simp
  show ?thesis
    by (intro exI[of _ charts] exI[of _ C] exI[of _ D] conjI cov der nsurj cls)
qed


section \<open>Reusable chart-core combinators\<close>

lemma chart_core_data_union:
  fixes S T :: "((real^2)^'n::finite) set"
  assumes Sdata: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    and Tdata: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         T \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S \<union> T \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  obtain charts0 :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit0 :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D0 :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cov0: "S \<subseteq> (\<Union>i. (fst \<circ> charts0 i) ` (Crit0 i))"
      and der0: "\<forall>i x. x \<in> Crit0 i \<longrightarrow>
        ((fst \<circ> charts0 i) has_derivative (blinfun_apply (D0 i x))) (at x within Crit0 i)"
      and ns0: "\<forall>i x. x \<in> Crit0 i \<longrightarrow> \<not> surj (blinfun_apply (D0 i x))"
      and cls0: "\<forall>i. closed ((fst \<circ> charts0 i) ` (Crit0 i))"
    using Sdata by blast
  obtain charts1 :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit1 :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D1 :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cov1: "T \<subseteq> (\<Union>i. (fst \<circ> charts1 i) ` (Crit1 i))"
      and der1: "\<forall>i x. x \<in> Crit1 i \<longrightarrow>
        ((fst \<circ> charts1 i) has_derivative (blinfun_apply (D1 i x))) (at x within Crit1 i)"
      and ns1: "\<forall>i x. x \<in> Crit1 i \<longrightarrow> \<not> surj (blinfun_apply (D1 i x))"
      and cls1: "\<forall>i. closed ((fst \<circ> charts1 i) ` (Crit1 i))"
    using Tdata by blast

  define branch where "branch = (\<lambda>n::nat. fst (prod_decode n))"
  define idx where "idx = (\<lambda>n::nat. snd (prod_decode n))"
  define charts where "charts =
    (\<lambda>n (x::(real^2)^'n). if branch n = 0 then charts0 (idx n) x else charts1 (idx n) x)"
  define Crit where "Crit =
    (\<lambda>n::nat. if branch n = 0 then Crit0 (idx n) else Crit1 (idx n))"
  define D where "D =
    (\<lambda>n (x::(real^2)^'n). if branch n = 0 then D0 (idx n) x else D1 (idx n) x)"

  have cov: "S \<union> T \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
  proof
    fix x assume xU: "x \<in> S \<union> T"
    show "x \<in> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    proof (rule UnE[OF xU])
      assume xS: "x \<in> S"
      then obtain i y where y: "y \<in> Crit0 i" and xeq: "x = (fst \<circ> charts0 i) y"
        using cov0 by blast
      define n where "n = prod_encode (0, i)"
      have "x \<in> (fst \<circ> charts n) ` (Crit n)"
        unfolding charts_def Crit_def branch_def idx_def n_def using y xeq by simp
      thus "x \<in> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
        by blast
    next
      assume xT: "x \<in> T"
      then obtain i y where y: "y \<in> Crit1 i" and xeq: "x = (fst \<circ> charts1 i) y"
        using cov1 by blast
      define n where "n = prod_encode (Suc 0, i)"
      have "x \<in> (fst \<circ> charts n) ` (Crit n)"
        unfolding charts_def Crit_def branch_def idx_def n_def using y xeq by simp
      thus "x \<in> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
        by blast
    qed
  qed

  have der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
      ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
  proof (intro allI impI)
    fix i x assume xC: "x \<in> Crit i"
    show "((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
    proof (cases "branch i = 0")
      case True
      have "x \<in> Crit0 (idx i)"
        using xC True unfolding Crit_def by simp
      thus ?thesis
        using der0 True unfolding charts_def Crit_def D_def by simp
    next
      case False
      have "x \<in> Crit1 (idx i)"
        using xC False unfolding Crit_def by simp
      thus ?thesis
        using der1 False unfolding charts_def Crit_def D_def by simp
    qed
  qed
  have nsurj: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
  proof (intro allI impI)
    fix i x assume xC: "x \<in> Crit i"
    show "\<not> surj (blinfun_apply (D i x))"
    proof (cases "branch i = 0")
      case True
      have "x \<in> Crit0 (idx i)"
        using xC True unfolding Crit_def by simp
      thus ?thesis
        using ns0 True unfolding D_def by simp
    next
      case False
      have "x \<in> Crit1 (idx i)"
        using xC False unfolding Crit_def by simp
      thus ?thesis
        using ns1 False unfolding D_def by simp
    qed
  qed
  have cls: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
  proof
    fix i
    show "closed ((fst \<circ> charts i) ` (Crit i))"
    proof (cases "branch i = 0")
      case True
      thus ?thesis
        using cls0 unfolding charts_def Crit_def by simp
    next
      case False
      thus ?thesis
        using cls1 unfolding charts_def Crit_def by simp
    qed
  qed

  show ?thesis
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D] conjI cov der nsurj cls)
qed

lemma chart_core_data_empty:
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n::finite) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         {} \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    where "charts = (\<lambda>_ x. (x, 0))"
  define Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "Crit = (\<lambda>_. {})"
  define D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where "D = (\<lambda>_ _. 0)"
  show ?thesis
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D]) (simp add: Crit_def)
qed

lemma chart_core_data_finite_UN:
  fixes S :: "'i \<Rightarrow> ((real^2)^'n::finite) set"
  assumes fin: "finite I"
    and data: "\<And>i. i \<in> I \<Longrightarrow>
      \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (\<Union>i\<in>I. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  using fin data
proof (induction I)
  case empty
  have emp: "(\<Union>i\<in>{}. S i) = ({} :: ((real^2)^'n) set)"
    by simp
  show ?case
    unfolding emp by (rule chart_core_data_empty)
next
  case (insert i I)
  have di: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    using insert.prems by blast
  have dI: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (\<Union>i\<in>I. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    by (rule insert.IH) (use insert.prems in blast)
  have eq: "(\<Union>j\<in>insert i I. S j) = S i \<union> (\<Union>j\<in>I. S j)"
    by blast
  show ?case
    unfolding eq by (rule chart_core_data_union[OF di dI])
qed

lemma d3_detHess_arc_chart_core_empty:
  fixes V :: "((real^2)^'n::finite) set"
  assumes empty: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) = {}"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  unfolding d3_detHess_arc_chart_core_def
proof (intro exI conjI)
  show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i::nat. (fst \<circ> (\<lambda>(_::nat) (x::(real^2)^'n). (x, 0::real^2)) i) ` ({} :: ((real^2)^'n) set))"
    using empty by simp
qed simp_all

lemma d3_detHess_arc_chart_core_all_empty:
  fixes V :: "((real^2)^'n::finite) set"
  assumes empty: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) = {}"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and sub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
    by (rule d3_detHess_arc_chart_core_empty[OF empty[OF arc sub]])
qed

theorem d3_chart_core_of_finite_chart_core_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and S :: "'i \<Rightarrow> ((real^2)^'n) set"
  assumes fin: "finite I"
    and cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i\<in>I. S i)"
    and data: "\<And>i. i \<in> I \<Longrightarrow>
      \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cov: "(\<Union>i\<in>I. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))"
      and der: "\<forall>j x. x \<in> Crit j \<longrightarrow>
        ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)"
      and nsurj: "\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))"
      and cls: "\<forall>j. closed ((fst \<circ> charts j) ` (Crit j))"
    using chart_core_data_finite_UN[OF fin data]
    by (smt (verit, best) assms(1,3) chart_core_data_finite_UN) 
  have cover': "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))"
    using cover cov by blast
  show ?thesis
    unfolding d3_detHess_arc_chart_core_def
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D] conjI cover' der nsurj cls)
qed

theorem d3_chart_core_all_of_finite_chart_core_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes pieces: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>(I :: nat set) (S :: nat \<Rightarrow> ((real^2)^'n) set).
        finite I
      \<and> (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i\<in>I. S i)
      \<and> (\<forall>i\<in>I.
        \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
          (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
          (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
           S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
           (\<forall>j x. x \<in> Crit j \<longrightarrow>
              ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
           (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
           (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j))))"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and sub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  obtain I :: "nat set" and S :: "nat \<Rightarrow> ((real^2)^'n) set"
    where fin: "finite I"
      and cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i\<in>I. S i)"
      and data: "\<forall>i\<in>I.
        \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
          (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
          (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
           S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
           (\<forall>j x. x \<in> Crit j \<longrightarrow>
              ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
           (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
           (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    using pieces[OF arc sub] by blast
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
    by (rule d3_chart_core_of_finite_chart_core_cover[OF fin cover])
       (use data in blast)
qed


section \<open>Arc chart cores from direct cut covers\<close>

theorem d3_chart_core_of_functional_cut_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and f :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
    and L :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
    and r :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (real^2)^'n"
  assumes cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. C i)"
    and closedC: "\<And>i. closed (C i)"
    and cut0: "\<And>i y. y \<in> C i \<Longrightarrow> f i y = 0"
    and cutd: "\<And>i x. x \<in> C i \<Longrightarrow> (f i has_derivative L i x) (at x)"
    and rnz: "\<And>i x. x \<in> C i \<Longrightarrow> L i x (r i x) \<noteq> 0"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  unfolding d3_detHess_arc_chart_core_def
  by (rule chart_core_data_of_functional_cuts[OF cover closedC cut0 cutd rnz])

theorem d3_chart_core_all_of_functional_cut_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes pieces: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>(C :: nat \<Rightarrow> ((real^2)^'n) set)
        (f :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> real)
        (L :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real)
        (r :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (real^2)^'n).
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. C i)
      \<and> (\<forall>i. closed (C i))
      \<and> (\<forall>i y. y \<in> C i \<longrightarrow> f i y = 0)
      \<and> (\<forall>i x. x \<in> C i \<longrightarrow> (f i has_derivative L i x) (at x))
      \<and> (\<forall>i x. x \<in> C i \<longrightarrow> L i x (r i x) \<noteq> 0)"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  obtain C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and f :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
    and L :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
    and r :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (real^2)^'n"
    where cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. C i)"
      and closedC: "\<forall>i. closed (C i)"
      and cut0: "\<forall>i y. y \<in> C i \<longrightarrow> f i y = 0"
      and cutd: "\<forall>i x. x \<in> C i \<longrightarrow> (f i has_derivative L i x) (at x)"
      and rnz: "\<forall>i x. x \<in> C i \<longrightarrow> L i x (r i x) \<noteq> 0"
    using pieces[OF arc gsub] by blast
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
    by (rule d3_chart_core_of_functional_cut_cover
        [where C = C and f = f and L = L and r = r, OF cover])
       (use closedC cut0 cutd rnz in blast)+
qed

theorem d3_chart_core_of_vector_cut_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and f :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b::euclidean_space"
    and L :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b"
    and W :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b \<Rightarrow> (real^2)^'n"
  assumes cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. C i)"
    and closedC: "\<And>i. closed (C i)"
    and cut0: "\<And>i y. y \<in> C i \<Longrightarrow> f i y = 0"
    and cutd: "\<And>i x. x \<in> C i \<Longrightarrow> (f i has_derivative L i x) (at x)"
    and Wbl: "\<And>i x. x \<in> C i \<Longrightarrow> bounded_linear (W i x)"
    and Wright: "\<And>i x t. x \<in> C i \<Longrightarrow> L i x (W i x t) = t"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  unfolding d3_detHess_arc_chart_core_def
  by (rule chart_core_data_of_vector_cuts[OF cover closedC cut0 cutd Wbl Wright])

theorem d3_chart_core_all_of_vector_cut_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes pieces: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>(C :: nat \<Rightarrow> ((real^2)^'n) set)
        (f :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b::euclidean_space)
        (L :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b)
        (W :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b \<Rightarrow> (real^2)^'n).
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. C i)
      \<and> (\<forall>i. closed (C i))
      \<and> (\<forall>i y. y \<in> C i \<longrightarrow> f i y = 0)
      \<and> (\<forall>i x. x \<in> C i \<longrightarrow> (f i has_derivative L i x) (at x))
      \<and> (\<forall>i x. x \<in> C i \<longrightarrow> bounded_linear (W i x))
      \<and> (\<forall>i x t. x \<in> C i \<longrightarrow> L i x (W i x t) = t)"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  obtain C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and f :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b"
    and L :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b"
    and W :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> 'b \<Rightarrow> (real^2)^'n"
    where cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. C i)"
      and closedC: "\<forall>i. closed (C i)"
      and cut0: "\<forall>i y. y \<in> C i \<longrightarrow> f i y = 0"
      and cutd: "\<forall>i x. x \<in> C i \<longrightarrow> (f i has_derivative L i x) (at x)"
      and Wbl: "\<forall>i x. x \<in> C i \<longrightarrow> bounded_linear (W i x)"
      and Wright: "\<forall>i x t. x \<in> C i \<longrightarrow> L i x (W i x t) = t"
    using pieces[OF arc gsub] by blast
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
    by (rule d3_chart_core_of_vector_cut_cover
        [where C = C and f = f and L = L and W = W, OF cover])
       (use closedC cut0 cutd Wbl Wright in blast)+
qed


section \<open>Arc chart cores from fixed-\<open>\<omega>\<close> pieces\<close>

lemma has_derivative_gradU_dip_component2_x_frechet:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) has_derivative
      frechet_derivative
        (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)) (at x)"
proof -
  have h: "((\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) has_derivative
        (dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (2::2) 1) 1)) (gain_dip \<omega>)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 1)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (2::2) 1)) 2)
             (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
         \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x)"
    by (rule has_derivative_gradU_dip_component_x)
  show ?thesis
    using h frechet_derivative_at[OF h] by simp
qed

theorem d3_chart_core_of_fixed_omega_piece_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and Cp :: "nat \<Rightarrow> ((real^2)^'n) set"
    and om :: "nat \<Rightarrow> real^2"
    and ki :: "nat \<Rightarrow> 'n"
    and \<gamma> :: "(real^2) set"
    and \<omega>0 \<omega>s :: "real^2"
  assumes cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. Cp i)"
    and closedC: "\<And>i. closed (Cp i)"
    and subcore: "\<And>i. Cp i \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s {om i}"
    and snz: "\<And>i x. x \<in> Cp i \<Longrightarrow>
        frechet_derivative
          (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (om i)) 2) (at x)
          (slot (ki i) (perp2 (cvec_dip \<omega>0 \<omega>s (om i)))) \<noteq> 0"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof -
  define f where "f = (\<lambda>i (y::(real^2)^'n).
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (om i)) 2)"
  define L where "L = (\<lambda>i (x::(real^2)^'n). frechet_derivative (f i) (at x))"
  define r where "r = (\<lambda>i (x::(real^2)^'n). slot (ki i) (perp2 (cvec_dip \<omega>0 \<omega>s (om i))))"
  have cutd: "(f i has_derivative L i x) (at x)" for i x
    unfolding f_def L_def by (rule has_derivative_gradU_dip_component2_x_frechet)
  have cut0: "f i y = 0" if "y \<in> Cp i" for i y
  proof -
    have ycore: "y \<in> D3BadXG_H0core \<omega>0 \<omega>s {om i}"
      using that subcore[of i] by blast
    have "\<exists>\<omega>'\<in>{om i}.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>' = 0
      \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>') = 0
      \<and> cvec_dip \<omega>0 \<omega>s \<omega>' \<noteq> 0
      \<and> \<not> surj (DM_paper_x y (cvec_dip \<omega>0 \<omega>s \<omega>'))
      \<and> \<not> (\<exists>Dx. ((\<lambda>z. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip z \<omega>') has_derivative Dx)
            (at y) \<and> surj Dx)"
      using ycore unfolding D3BadXG_H0core_def by simp
    then obtain \<omega>' where "\<omega>' = om i"
      and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>' = 0"
      by auto
    hence "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (om i) = 0"
      by simp
    thus ?thesis
      unfolding f_def by simp
  qed
  have rnz: "L i x (r i x) \<noteq> 0" if "x \<in> Cp i" for i x
    unfolding L_def r_def f_def using snz[OF that] .
  show ?thesis
    unfolding d3_detHess_arc_chart_core_def
  proof (rule chart_core_data_of_functional_cuts[of _ Cp f L r])
    show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. Cp i)"
      by (rule cover)
    show "\<And>i. closed (Cp i)"
      by (rule closedC)
    show "\<And>i y. y \<in> Cp i \<Longrightarrow> f i y = 0"
      by (rule cut0)
    show "\<And>i x. x \<in> Cp i \<Longrightarrow> (f i has_derivative L i x) (at x)"
      by (rule cutd)
    show "\<And>i x. x \<in> Cp i \<Longrightarrow> L i x (r i x) \<noteq> 0"
      by (rule rnz)
  qed
qed

theorem d3_chart_core_all_of_fixed_omega_piece_covers:
  fixes V :: "((real^2)^'n::finite) set"
  assumes pieces: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>(Cp :: nat \<Rightarrow> ((real^2)^'n) set) (om :: nat \<Rightarrow> real^2) (ki :: nat \<Rightarrow> 'n).
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. Cp i)
      \<and> (\<forall>i. closed (Cp i))
      \<and> (\<forall>i. Cp i \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s {om i})
      \<and> (\<forall>i x. x \<in> Cp i \<longrightarrow>
          frechet_derivative
            (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (om i)) 2) (at x)
            (slot (ki i) (perp2 (cvec_dip \<omega>0 \<omega>s (om i)))) \<noteq> 0)"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  obtain Cp :: "nat \<Rightarrow> ((real^2)^'n) set"
    and om :: "nat \<Rightarrow> real^2"
    and ki :: "nat \<Rightarrow> 'n"
    where cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. Cp i)"
      and closedC: "\<forall>i. closed (Cp i)"
      and subcore: "\<forall>i. Cp i \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s {om i}"
      and snz: "\<forall>i x. x \<in> Cp i \<longrightarrow>
          frechet_derivative
            (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (om i)) 2) (at x)
            (slot (ki i) (perp2 (cvec_dip \<omega>0 \<omega>s (om i)))) \<noteq> 0"
    using pieces[OF arc gsub] by blast
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  proof (rule d3_chart_core_of_fixed_omega_piece_cover[OF cover])
    show "\<And>i. closed (Cp i)"
      using closedC by blast
    show "\<And>i. Cp i \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s {om i}"
      using subcore by blast
    show "\<And>i x. x \<in> Cp i \<Longrightarrow>
        frechet_derivative
          (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (om i)) 2) (at x)
          (slot (ki i) (perp2 (cvec_dip \<omega>0 \<omega>s (om i)))) \<noteq> 0"
      using snz by blast
  qed
qed


section \<open>Capstone-facing Robust4 design wrappers\<close>

theorem F0_dip_nonempty_from_robust4_design_cores:
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and d3core: "\<And>V::(planar^'n) set.
      d3_detHess_arc_chart_core_all V (vector [pi / 2, 0]) (pi / 4)
        (vector [pi / 2, 0]) (vector [0, 0])"
    and branchcore: "\<And>V::(planar^'n) set.
      branchP_indep_closed_cover_core_all V (vector [pi / 2, 0]) (pi / 4)
        (vector [pi / 2, 0]) (vector [0, 0])"
  shows "\<exists>A B D \<omega>0 \<omega>s \<omega>null ctr \<delta> R dmin \<delta>null pmin \<xi> \<kappa> \<epsilon>.
            0 < \<delta> \<and> 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr
              (OmegaPF ctr \<delta>) \<delta>null pmin \<xi> \<kappa> \<epsilon> \<noteq> ({}::(planar^'n) set)"
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
  have pf: "\<forall>\<omega>\<in>OmegaPF \<omega>0 (pi/4). sin (vec_nth \<omega> 1) \<noteq> 0"
  proof
    fix \<omega> :: planar assume "\<omega> \<in> OmegaPF \<omega>0 (pi/4)"
    hence mb: "vec_nth (\<omega>0 - vector [pi/4, pi]) 1 \<le> vec_nth \<omega> 1 \<and>
        vec_nth \<omega> 1 \<le> vec_nth (\<omega>0 + vector [pi/4, pi]) 1"
      unfolding OmegaPF_def mem_box_cart by blast
    have l1: "vec_nth (\<omega>0 - vector [pi/4, pi]) 1 = pi/4"
      by (simp add: \<omega>0_def vector_minus_component vector_2)
    have l2: "vec_nth (\<omega>0 + vector [pi/4, pi]) 1 = 3*pi/4"
      by (simp add: \<omega>0_def vector_add_component vector_2)
    have lo: "0 < vec_nth \<omega> 1" and hi: "vec_nth \<omega> 1 < pi"
      using mb l1 l2 pi_gt_zero by linarith+
    have "0 < sin (vec_nth \<omega> 1)" by (rule sin_gt_zero[OF lo hi])
    thus "sin (vec_nth \<omega> 1) \<noteq> 0" by simp
  qed
  have nsing: "d3_collinear_nsing_all \<omega>0 (pi/4) \<omega>0 \<omega>s"
  proof (unfold d3_collinear_nsing_all_def, intro ballI)
    fix \<omega> :: planar
    assume wL: "\<omega> \<in> {\<omega> \<in> OmegaPF \<omega>0 (pi/4). d3_crossTheta \<omega>0 \<omega>s \<omega> = 0}"
    hence wO: "\<omega> \<in> OmegaPF \<omega>0 (pi/4)"
      and z: "d3_crossTheta \<omega>0 \<omega>s \<omega> = 0" by auto
    have mb: "vec_nth (\<omega>0 - vector [pi/4, pi]) 1 \<le> vec_nth \<omega> 1
        \<and> vec_nth \<omega> 1 \<le> vec_nth (\<omega>0 + vector [pi/4, pi]) 1"
      using wO unfolding OmegaPF_def mem_box_cart by blast
    have l1: "vec_nth (\<omega>0 - vector [pi/4, pi]) 1 = pi/4"
      by (simp only: \<omega>0_def vector_minus_component vector_2)
    have l2: "vec_nth (\<omega>0 + vector [pi/4, pi]) 1 = 3*pi/4"
      by (simp add: \<omega>0_def vector_add_component vector_2)
    have lo: "0 < vec_nth \<omega> 1" and hi: "vec_nth \<omega> 1 < pi"
      using mb l1 l2 pi_gt_zero by linarith+
    have c_lt1: "cos (vec_nth \<omega> 1) < 1"
    proof -
      have h0: "0 < vec_nth \<omega> 1 / 2" using lo by simp
      have h2: "vec_nth \<omega> 1 / 2 < 2" using hi pi_less_4 by linarith
      have "cos (2 * (vec_nth \<omega> 1 / 2)) < 1"
        by (rule cos_double_less_one[OF h0 h2])
      thus ?thesis by simp
    qed
    have cne: "cos (vec_nth \<omega> 1) - 1 \<noteq> 0" using c_lt1 by linarith
    have trig_collapse: "cos (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
        + sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
        = sin (vec_nth \<omega> 2)"
    proof -
      have "cos (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
          + sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
          = (cos (vec_nth \<omega> 1) * cos (vec_nth \<omega> 1)
              + sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1)) * sin (vec_nth \<omega> 2)"
        by (simp only: mult.assoc distrib_right)
      also have "\<dots> = sin (vec_nth \<omega> 2)"
        by (simp only: sin_cos_squared_add3)
      finally show ?thesis .
    qed
    have theta_eq: "d3_crossTheta \<omega>0 \<omega>s \<omega> = (cos (vec_nth \<omega> 1) - 1) * sin (vec_nth \<omega> 2)"
      by (simp add: d3_crossTheta_def cvec_dip_def Dcvec_dip_def
          \<omega>0_def \<omega>s_def kx_def ky_def kz_def axis_def vector_2
          sin_pi_half cos_pi_half algebra_simps trig_collapse)
    have s2z: "sin (vec_nth \<omega> 2) = 0" using z theta_eq cne by auto
    have c2nz: "cos (vec_nth \<omega> 2) \<noteq> 0"
    proof
      assume c2z: "cos (vec_nth \<omega> 2) = 0"
      have "\<bar>cos (vec_nth \<omega> 2)\<bar> = (1::real)" by (rule sin_zero_abs_cos_one[OF s2z])
      thus False using c2z by simp
    qed
    have d2eq: "d3_collinear_d2 \<omega>0 \<omega>s \<omega> =
        (cos (vec_nth \<omega> 1) - 1) * cos (vec_nth \<omega> 2)"
      by (simp add: d3_collinear_d2_def d3_crossA_def d3_crossB_def
          \<omega>0_def \<omega>s_def kx_def ky_def kz_def vector_2
          sin_pi_half cos_pi_half algebra_simps)
    have "d3_collinear_d2 \<omega>0 \<omega>s \<omega> \<noteq> 0"
      using cne c2nz d2eq by simp
    thus "d3_collinear_d2 \<omega>0 \<omega>s \<omega> \<noteq> 0
       \<or> d3_collinear_d1 \<omega>0 \<omega>s \<omega> \<noteq> 0" by blast
  qed
  have cn: "cvec_dip \<omega>0 \<omega>s \<omega>null \<noteq> 0"
  proof -
    have "vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>null) 1 = - 2"
      by (simp add: cvec_dip_def \<omega>0_def \<omega>s_def \<omega>null_def kx_def ky_def kz_def
          sin_pi_half cos_pi_half axis_def)
    hence "vec_nth (cvec_dip \<omega>0 \<omega>s \<omega>null) 1 \<noteq> 0" by simp
    thus ?thesis by (metis zero_index)
  qed
  have N1: "CARD('n) > 1" using c6 by simp
  have spos: "(0::real) < 1" by simp
  obtain x :: "planar^'n"
    where afz: "af (cvec_dip \<omega>0 \<omega>s) x \<omega>null = 0"
      and spac0: "\<forall>m m'. m \<noteq> m' \<longrightarrow>
        (1::real) \<le> spdist 0 0 1 (vec_nth x m) (vec_nth x m')"
    using feasible_witness_exists[OF N1 cn spos] by meson
  define R :: real where "R = norm x + 1"
  have g0pos: "0 < gain_dip \<omega>0"
  proof -
    have "sin (vec_nth \<omega>0 1) \<noteq> 0" by (simp add: \<omega>0_def sin_pi_half)
    hence "gain_dip \<omega>0 \<noteq> 0" by (rule gain_dip_nonzero_of_sin)
    moreover have "0 \<le> gain_dip \<omega>0" by (rule gain_dip_nonneg)
    ultimately show ?thesis by simp
  qed
  have feasible: "interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
                    :: (planar^'n) set) \<noteq> {}"
  proof -
    have spac: "\<forall>p\<in>{p. fst p \<noteq> snd p}.
        (1/2::real) < spdist 0 0 1 (vec_nth x (fst p)) (vec_nth x (snd p))"
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
  have cap: "\<exists>\<xi> \<kappa> \<epsilon>. 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0
              (OmegaPF \<omega>0 (pi/4)) 1 0 \<xi> \<kappa> \<epsilon> \<noteq> ({}::(planar^'n) set)"
  proof -
    have d3core_feas: "d3_detHess_arc_chart_core_all
        (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
           :: (planar^'n) set)) \<omega>0 (pi/4) \<omega>0 \<omega>s"
      unfolding \<omega>0_def \<omega>s_def by (rule d3core)
    have branchcore_feas: "branchP_indep_closed_cover_core_all
        (interior (Ffeas (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0 1 0
           :: (planar^'n) set)) \<omega>0 (pi/4) \<omega>0 \<omega>s"
      unfolding \<omega>0_def \<omega>s_def by (rule branchcore)
    show ?thesis
      using regular_feasible_witness_dip[
          OF c6 oddN hsep kdiff d0 dpi pf nsing feasible d3core_feas branchcore_feas]
      by (blast intro: F0_nonempty_of_witness OmegaPF_compact)
  qed
  then obtain \<xi> \<kappa> \<epsilon>
    where xipos: "0 < \<xi>"
      and kappapos: "0 < \<kappa>"
      and epspos: "0 < \<epsilon>"
      and F0nz: "F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R (1/2) 0 0 1 \<omega>null \<omega>0
          (OmegaPF \<omega>0 (pi/4)) 1 0 \<xi> \<kappa> \<epsilon> \<noteq> ({}::(planar^'n) set)"
    by blast
  show ?thesis
    apply (rule_tac x="0::real" in exI)
    apply (rule_tac x="0::real" in exI)
    apply (rule_tac x="1::real" in exI)
    apply (rule_tac x="\<omega>0" in exI)
    apply (rule_tac x="\<omega>s" in exI)
    apply (rule_tac x="\<omega>null" in exI)
    apply (rule_tac x="\<omega>0" in exI)
    apply (rule_tac x="pi/4" in exI)
    apply (rule_tac x="R" in exI)
    apply (rule_tac x="1/2::real" in exI)
    apply (rule_tac x="1::real" in exI)
    apply (rule_tac x="0::real" in exI)
    apply (rule_tac x="\<xi>" in exI)
    apply (rule_tac x="\<kappa>" in exI)
    apply (rule_tac x="\<epsilon>" in exI)
    apply (intro conjI)
       apply (rule d0)
      apply (rule xipos)
     apply (rule kappapos)
    apply (rule epspos)
    apply (rule F0nz)
    done
qed

theorem F0_dip_nonempty_from_robust4_piece_covers:
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and d3pieces: "\<And>(V::(planar^'n) set) \<gamma>.
      analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4) \<Longrightarrow>
      \<exists>(Cp :: nat \<Rightarrow> (planar^'n) set) (om :: nat \<Rightarrow> real^2) (ki :: nat \<Rightarrow> 'n).
        (V \<inter> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) \<gamma> :: (planar^'n) set)
          \<subseteq> (\<Union>i. Cp i)
      \<and> (\<forall>i. closed (Cp i))
      \<and> (\<forall>i. Cp i \<subseteq> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {om i})
      \<and> (\<forall>i x. x \<in> Cp i \<longrightarrow>
          frechet_derivative
            (\<lambda>y::planar^'n. vec_nth (gradU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip y (om i)) 2) (at x)
            (slot (ki i) (perp2 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (om i)))) \<noteq> 0)"
    and branchcore: "\<And>V::(planar^'n) set.
      branchP_indep_closed_cover_core_all V (vector [pi / 2, 0]) (pi / 4)
        (vector [pi / 2, 0]) (vector [0, 0])"
  shows "\<exists>A B D \<omega>0 \<omega>s \<omega>null ctr \<delta> R dmin \<delta>null pmin \<xi> \<kappa> \<epsilon>.
            0 < \<delta> \<and> 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr
              (OmegaPF ctr \<delta>) \<delta>null pmin \<xi> \<kappa> \<epsilon> \<noteq> ({}::(planar^'n) set)"
proof (rule F0_dip_nonempty_from_robust4_design_cores[OF c6 oddN])
  fix V :: "(planar^'n) set"
  show "d3_detHess_arc_chart_core_all V (vector [pi / 2, 0]) (pi / 4)
      (vector [pi / 2, 0]) (vector [0, 0])"
  proof (rule d3_chart_core_all_of_fixed_omega_piece_covers)
    fix \<gamma>
    assume arc: "analytic_arc \<gamma>"
      and gsub: "\<gamma> \<subseteq> OmegaPF (vector [pi / 2, 0]) (pi / 4)"
    show "\<exists>(Cp :: nat \<Rightarrow> (planar^'n) set) (om :: nat \<Rightarrow> real^2) (ki :: nat \<Rightarrow> 'n).
        (V \<inter> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) \<gamma> :: (planar^'n) set)
          \<subseteq> (\<Union>i. Cp i)
      \<and> (\<forall>i. closed (Cp i))
      \<and> (\<forall>i. Cp i \<subseteq> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {om i})
      \<and> (\<forall>i x. x \<in> Cp i \<longrightarrow>
          frechet_derivative
            (\<lambda>y::planar^'n. vec_nth (gradU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
              gain_dip y (om i)) 2) (at x)
            (slot (ki i) (perp2 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (om i)))) \<noteq> 0)"
      by (rule d3pieces[OF arc gsub])
  qed
next
  fix V :: "(planar^'n) set"
  show "branchP_indep_closed_cover_core_all V (vector [pi / 2, 0]) (pi / 4)
      (vector [pi / 2, 0]) (vector [0, 0])"
    by (rule branchcore)
qed

end
