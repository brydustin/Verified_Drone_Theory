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

end
