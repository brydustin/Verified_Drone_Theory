theory Scratch_Wiring
  imports "Applied_Math_D3_Wiring.D3_Chart_Wiring"
          "Applied_Math_D34_Analytic.D34_H0res_Branch"
begin

section \<open>The functional-cut engine for fixed-\<open>\<omega>\<close> slice pieces\<close>

text \<open>\<^bold>\<open>Scratch staging only.\<close>  The parent wiring theory is part of the
  \<open>Applied_Math_D3_Wiring\<close> heap; this child scratch theory is the right place to
  test additions before they are folded into a rebuilt heap.\<close>

subsection \<open>Reusable threshold covers for nonzero scalar cuts\<close>

lemma nonzero_threshold_cover:
  fixes s :: "'a \<Rightarrow> real"
  shows "{x. s x \<noteq> 0} \<subseteq> (\<Union>n. {x. inverse (real (Suc n)) \<le> \<bar>s x\<bar>})"
proof
  fix x assume sx: "x \<in> {x. s x \<noteq> 0}"
  hence pos: "0 < \<bar>s x\<bar>" by simp
  obtain n where "inverse (real (Suc n)) < \<bar>s x\<bar>"
    using reals_Archimedean[OF pos] by blast
  hence "x \<in> {x. inverse (real (Suc n)) \<le> \<bar>s x\<bar>}"
    by simp
  thus "x \<in> (\<Union>n. {x. inverse (real (Suc n)) \<le> \<bar>s x\<bar>})"
    by blast
qed

lemma closed_abs_ge_threshold:
  fixes s :: "'a::metric_space \<Rightarrow> real"
  assumes cont: "continuous_on UNIV s"
  shows "closed {x. a \<le> \<bar>s x\<bar>}"
proof -
  have cont_abs: "continuous_on UNIV (\<lambda>x. \<bar>s x\<bar>)"
    by (intro continuous_intros cont)
  have cont_at: "\<And>x. continuous (at x) (\<lambda>x. \<bar>s x\<bar>)"
    using continuous_on_eq_continuous_at[OF open_UNIV, THEN iffD1, OF cont_abs]
    by simp
  have "{x. a \<le> \<bar>s x\<bar>} = (\<lambda>x. \<bar>s x\<bar>) -` {a..}"
    by auto
  thus ?thesis
    by (simp add: continuous_closed_vimage[OF closed_real_atLeast cont_at])
qed

subsection \<open>The functional-cut projection\<close>

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
  interpret L: bounded_linear L by (rule bl)
  have "L (v - (L v / L r) *\<^sub>R r) = L v - (L v / L r) * L r"
    by (simp add: L.diff L.scaleR)
  also have "\<dots> = 0"
    using rnz by simp
  finally have "L r = 0"
    using veq by simp
  with rnz show False by simp
qed

subsection \<open>The within-derivative of the identity at a functional cut\<close>

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

subsection \<open>Assembling chart-core data from countable closed functional cuts\<close>

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

subsection \<open>The fixed-\<open>\<omega>\<close> slice pieces from the \<open>s\<^sub>k\<close> side condition\<close>

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

theorem slice_chart_core_data:
  fixes S :: "((real^2)^'n::finite) set"
    and Cp :: "nat \<Rightarrow> ((real^2)^'n) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2" and k :: 'n
  assumes cover: "S \<subseteq> (\<Union>i. Cp i)"
    and closedC: "\<And>i. closed (Cp i)"
    and inslice: "\<And>i y. y \<in> Cp i \<Longrightarrow>
        vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2 = 0"
    and snz: "\<And>i x. x \<in> Cp i \<Longrightarrow>
        frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
          (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) \<noteq> 0"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define f2 where "f2 = (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2)"
  define Lf where "Lf = (\<lambda>x::(real^2)^'n. frechet_derivative f2 (at x))"
  have hd2: "(f2 has_derivative Lf x) (at x)" for x :: "(real^2)^'n"
    unfolding f2_def Lf_def by (rule has_derivative_gradU_dip_component2_x_frechet)
  show ?thesis
  proof (rule chart_core_data_of_functional_cuts[of S Cp "\<lambda>i. f2" "\<lambda>i. Lf"
        "\<lambda>i x. slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))"])
    show "S \<subseteq> (\<Union>i. Cp i)" by (rule cover)
    show "\<And>i. closed (Cp i)" by (rule closedC)
    show "\<And>i y. y \<in> Cp i \<Longrightarrow> f2 y = 0"
      unfolding f2_def by (rule inslice)
    show "\<And>i x. x \<in> Cp i \<Longrightarrow> (f2 has_derivative Lf x) (at x)"
      by (rule hd2)
    show "\<And>i x. x \<in> Cp i \<Longrightarrow> Lf x (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) \<noteq> 0"
      unfolding Lf_def f2_def using snz .
  qed
qed

subsection \<open>Singleton-\<open>\<omega>\<close> D3 chart core from fixed-slice cuts\<close>

theorem fixed_omega_slice_d3_chart_core:
  fixes V :: "((real^2)^'n::finite) set"
    and Cp :: "nat \<Rightarrow> ((real^2)^'n) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2" and k :: 'n
  assumes cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. Cp i)"
    and closedC: "\<And>i. closed (Cp i)"
    and inslice: "\<And>i y. y \<in> Cp i \<Longrightarrow>
        vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2 = 0"
    and snz: "\<And>i x. x \<in> Cp i \<Longrightarrow>
        frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
          (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) \<noteq> 0"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
  unfolding d3_detHess_arc_chart_core_def
  by (rule slice_chart_core_data[OF cover closedC inslice snz])

theorem fixed_omega_core_pieces_d3_chart_core:
  fixes V :: "((real^2)^'n::finite) set"
    and Cp :: "nat \<Rightarrow> ((real^2)^'n) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2" and k :: 'n
  assumes cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. Cp i)"
    and closedC: "\<And>i. closed (Cp i)"
    and subcore: "\<And>i. Cp i \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}"
    and snz: "\<And>i x. x \<in> Cp i \<Longrightarrow>
        frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
          (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) \<noteq> 0"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
proof (rule fixed_omega_slice_d3_chart_core[OF cover closedC _ snz])
  fix i y assume yC: "y \<in> Cp i"
  then obtain \<omega>' where "\<omega>' \<in> {\<omega>}"
    and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>' = 0"
    using subcore[of i] unfolding D3BadXG_H0core_def by blast
  hence "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> = 0"
    by simp
  thus "vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2 = 0"
    by simp
qed

subsection \<open>The fixed-\<open>\<omega>\<close> slicible branch and its residual\<close>

definition d3_s2_perp_slot ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 'n::finite \<Rightarrow> ((real^2)^'n) \<Rightarrow> real" where
  "d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x =
     frechet_derivative
       (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
       (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"

definition d3_s2_global_factor :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "d3_s2_global_factor \<omega>0 \<omega>s \<omega> =
     2 * gain_dip \<omega>
       * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))"

lemma d3_s2_perp_slot_value:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x
       = d3_s2_global_factor \<omega>0 \<omega>s \<omega>
           * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
               * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k)"
  unfolding d3_s2_perp_slot_def d3_s2_global_factor_def
  by (simp only: Phi2_perp_slot_value[OF perp2_orth])

definition D3H0_slicable_branch ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_slicable_branch V \<omega>0 \<omega>s \<omega> =
     {x \<in> V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}. \<exists>k. d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x \<noteq> 0}"

definition D3H0_all_s2_zero_residual ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_all_s2_zero_residual V \<omega>0 \<omega>s \<omega> =
     {x \<in> V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}. \<forall>k. d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x = 0}"

lemma fixed_omega_H0core_slicable_residual_decomp:
  "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n::finite) set)
   = D3H0_slicable_branch V \<omega>0 \<omega>s \<omega> \<union> D3H0_all_s2_zero_residual V \<omega>0 \<omega>s \<omega>"
  unfolding D3H0_slicable_branch_def D3H0_all_s2_zero_residual_def by blast

lemma continuous_on_d3_s2_perp_slot:
  "continuous_on UNIV (\<lambda>x::(real^2)^'n::finite. d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x)"
proof (rule continuous_at_imp_continuous_on, rule ballI)
  fix x :: "(real^2)^'n"
  assume "x \<in> UNIV"
  have ana: "real_analytic_on (\<lambda>x::(real^2)^'n. d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x) UNIV"
    unfolding d3_s2_perp_slot_def by (rule real_analytic_on_gradU2_slot)
  show "continuous (at x) (\<lambda>x::(real^2)^'n. d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x)"
    by (rule real_analytic_on_imp_continuous[OF ana UNIV_I])
qed

lemma closed_gradU2_component2_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "closed {x::(real^2)^'n::finite.
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2 = 0}"
proof -
  have cont: "continuous_on UNIV
      (\<lambda>x::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2)"
  proof (rule has_derivative_continuous_on)
    fix x :: "(real^2)^'n"
    show "((\<lambda>x::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2)
        has_derivative
        frechet_derivative
          (\<lambda>x::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) (at x))
        (at x within UNIV)"
      by (rule has_derivative_at_withinI[OF has_derivative_gradU_dip_component2_x_frechet])
  qed
  show ?thesis
    by (rule closed_Collect_eq[OF cont continuous_on_const])
qed

theorem fixed_omega_slicable_branch_chart_core_data:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_slicable_branch V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define k_of :: "nat \<Rightarrow> 'n" where
    "k_of n = from_nat (fst (prod_decode n))" for n
  define m_of :: "nat \<Rightarrow> nat" where
    "m_of n = snd (prod_decode n)" for n
  define f2 where "f2 = (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2)"
  define Lf where "Lf = (\<lambda>x::(real^2)^'n. frechet_derivative f2 (at x))"
  define r where "r = (\<lambda>n (x::(real^2)^'n). slot (k_of n) (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"
  define C where "C = (\<lambda>n. {x::(real^2)^'n. f2 x = 0}
      \<inter> {x. inverse (real (Suc (m_of n))) \<le> \<bar>d3_s2_perp_slot \<omega>0 \<omega>s \<omega> (k_of n) x\<bar>})"

  have cutd: "(f2 has_derivative Lf x) (at x)" for x :: "(real^2)^'n"
    unfolding f2_def Lf_def by (rule has_derivative_gradU_dip_component2_x_frechet)

  have closedC: "closed (C n)" for n
  proof -
    have c0: "closed {x::(real^2)^'n. f2 x = 0}"
      unfolding f2_def by (rule closed_gradU2_component2_zero)
    have ct: "closed {x::(real^2)^'n.
        inverse (real (Suc (m_of n))) \<le> \<bar>d3_s2_perp_slot \<omega>0 \<omega>s \<omega> (k_of n) x\<bar>}"
      by (rule closed_abs_ge_threshold[OF continuous_on_d3_s2_perp_slot])
    show ?thesis
      unfolding C_def by (intro closed_Int c0 ct)
  qed

  have cover: "D3H0_slicable_branch V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>n. C n)"
  proof
    fix x assume xB: "x \<in> D3H0_slicable_branch V \<omega>0 \<omega>s \<omega>"
    then obtain k :: 'n where sk: "d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x \<noteq> 0"
      unfolding D3H0_slicable_branch_def by blast
    define q where "q = to_nat k"
    have q: "from_nat q = k"
      unfolding q_def by simp
    have pos: "0 < \<bar>d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x\<bar>"
      using sk by simp
    obtain m where m: "inverse (real (Suc m)) < \<bar>d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x\<bar>"
      using reals_Archimedean[OF pos] by blast
    define n where "n = prod_encode (q, m)"
    have kd: "k_of n = k"
      unfolding k_of_def n_def using q by simp
    have md: "m_of n = m"
      unfolding m_of_def n_def by simp
    have fzero: "f2 x = 0"
    proof -
      have "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}"
        using xB unfolding D3H0_slicable_branch_def by blast
      then obtain \<omega>' where "\<omega>' \<in> {\<omega>}"
        and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>' = 0"
        unfolding D3BadXG_H0core_def by blast
      hence "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
        by simp
      thus ?thesis
        unfolding f2_def by simp
    qed
    have "x \<in> C n"
      unfolding C_def kd md using fzero m sk by auto
    thus "x \<in> (\<Union>n. C n)"
      by blast
  qed

  have cut0: "f2 y = 0" if "y \<in> C n" for n y
    using that unfolding C_def by simp
  have rnz: "Lf x (r n x) \<noteq> 0" if "x \<in> C n" for n x
  proof -
    have ge: "inverse (real (Suc (m_of n))) \<le> \<bar>d3_s2_perp_slot \<omega>0 \<omega>s \<omega> (k_of n) x\<bar>"
      using that unfolding C_def by simp
    have pos: "0 < inverse (real (Suc (m_of n)))"
      by simp
    have "d3_s2_perp_slot \<omega>0 \<omega>s \<omega> (k_of n) x \<noteq> 0"
      using ge pos by fastforce
    thus ?thesis
      unfolding d3_s2_perp_slot_def f2_def Lf_def r_def by simp
  qed

  show ?thesis
    by (rule chart_core_data_of_functional_cuts[OF cover closedC cut0 cutd rnz])
qed

subsection \<open>The fixed-\<open>\<omega>\<close> residual branch cut by \<open>B_dip\<close>\<close>

definition D3H0_residual_Bzero_branch ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_residual_Bzero_branch V \<omega>0 \<omega>s \<omega> =
     {x \<in> D3H0_all_s2_zero_residual V \<omega>0 \<omega>s \<omega>. \<exists>k. B_dip k x \<omega> \<omega>0 \<omega>s = 0}"

definition D3H0_residual_Bnonzero_residual ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega> =
     {x \<in> D3H0_all_s2_zero_residual V \<omega>0 \<omega>s \<omega>. \<forall>k. B_dip k x \<omega> \<omega>0 \<omega>s \<noteq> 0}"

definition D3H0_Bnonzero_factorzero_residual ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega> =
     {x \<in> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>.
        d3_s2_global_factor \<omega>0 \<omega>s \<omega> = 0}"

definition D3H0_Bnonzero_phase_aligned_residual ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega> =
     {x \<in> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>.
        \<forall>k. Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
             * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0}"

lemma fixed_omega_all_s2_residual_Bzero_decomp:
  "D3H0_all_s2_zero_residual V \<omega>0 \<omega>s \<omega>
   = D3H0_residual_Bzero_branch V \<omega>0 \<omega>s \<omega>
     \<union> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>"
  unfolding D3H0_residual_Bzero_branch_def D3H0_residual_Bnonzero_residual_def
  by blast

lemma fixed_omega_Bnonzero_residual_factor_phase_decomp:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows
  "D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>
   = D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega>
     \<union> D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>"
proof
  show "D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>
      \<subseteq> D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega>
        \<union> D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>"
  proof
    fix x assume xres: "x \<in> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>"
    show "x \<in> D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega>
        \<union> D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>"
    proof (cases "d3_s2_global_factor \<omega>0 \<omega>s \<omega> = 0")
      case True
      thus ?thesis
        using xres unfolding D3H0_Bnonzero_factorzero_residual_def by blast
    next
      case facnz: False
      have aligned: "\<forall>k. Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
             * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0"
      proof
        fix k :: 'n
        have s0: "d3_s2_perp_slot \<omega>0 \<omega>s \<omega> k x = 0"
          using xres
          unfolding D3H0_residual_Bnonzero_residual_def D3H0_all_s2_zero_residual_def
          by blast
        have "d3_s2_global_factor \<omega>0 \<omega>s \<omega>
             * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                 * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0"
          using s0 unfolding d3_s2_perp_slot_value .
        thus "Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
             * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0"
          using facnz by simp
      qed
      thus ?thesis
        using xres unfolding D3H0_Bnonzero_phase_aligned_residual_def by blast
    qed
  qed
  show "D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega>
      \<union> D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>
      \<subseteq> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>"
    unfolding D3H0_Bnonzero_factorzero_residual_def
      D3H0_Bnonzero_phase_aligned_residual_def
    by blast
qed

lemma fixed_omega_Bnonzero_residual_phase_alignment_if_factor_nonzero:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
    and x :: "(real^2)^'n"
  assumes facnz: "d3_s2_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and xres: "x \<in> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>"
  shows "x \<in> D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>"
proof -
  have "D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega> = {}"
    using facnz unfolding D3H0_Bnonzero_factorzero_residual_def by blast
  thus ?thesis
    using xres fixed_omega_Bnonzero_residual_factor_phase_decomp[of V \<omega>0 \<omega>s \<omega>]
    by blast
qed

lemma has_derivative_B_dip_x_frechet:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>y::(real^2)^'n. B_dip k y \<omega> \<omega>0 \<omega>s) has_derivative
      frechet_derivative (\<lambda>y::(real^2)^'n. B_dip k y \<omega> \<omega>0 \<omega>s) (at x)) (at x)"
proof -
  have h: "((\<lambda>y::(real^2)^'n. B_dip k y \<omega> \<omega>0 \<omega>s) has_derivative
      (\<lambda>h. -(2 * sin (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x k))
              + (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x k))
                * cos (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x k)))
           * (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth h k)))) (at x)"
    by (rule has_derivative_B_dip_x)
  show ?thesis
    using h frechet_derivative_at[OF h] by simp
qed

lemma continuous_on_B_dip_x:
  "continuous_on UNIV (\<lambda>x::(real^2)^'n::finite. B_dip k x \<omega> \<omega>0 \<omega>s)"
proof (rule continuous_at_imp_continuous_on, rule ballI)
  fix x :: "(real^2)^'n"
  assume "x \<in> UNIV"
  show "continuous (at x) (\<lambda>x::(real^2)^'n. B_dip k x \<omega> \<omega>0 \<omega>s)"
    by (rule has_derivative_continuous[OF has_derivative_B_dip_x])
qed

lemma closed_B_dip_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "closed {x::(real^2)^'n::finite. B_dip k x \<omega> \<omega>0 \<omega>s = 0}"
  by (rule closed_Collect_eq[OF continuous_on_B_dip_x continuous_on_const])

theorem fixed_omega_residual_Bzero_branch_chart_core_data:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_residual_Bzero_branch V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define k_of :: "nat \<Rightarrow> 'n" where
    "k_of n = from_nat n" for n
  define C where "C = (\<lambda>n. {x::(real^2)^'n. B_dip (k_of n) x \<omega> \<omega>0 \<omega>s = 0})"
  define f where "f = (\<lambda>n (x::(real^2)^'n). B_dip (k_of n) x \<omega> \<omega>0 \<omega>s)"
  define L where "L = (\<lambda>n (x::(real^2)^'n).
      frechet_derivative (\<lambda>y::(real^2)^'n. B_dip (k_of n) y \<omega> \<omega>0 \<omega>s) (at x))"
  define r where "r = (\<lambda>n (x::(real^2)^'n). slot (k_of n) (cvec_dip \<omega>0 \<omega>s \<omega>))"

  have closedC: "closed (C n)" for n
    unfolding C_def by (rule closed_B_dip_zero)

  have cover: "D3H0_residual_Bzero_branch V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>n. C n)"
  proof
    fix x assume xB: "x \<in> D3H0_residual_Bzero_branch V \<omega>0 \<omega>s \<omega>"
    then obtain k :: 'n where bk: "B_dip k x \<omega> \<omega>0 \<omega>s = 0"
      unfolding D3H0_residual_Bzero_branch_def by blast
    define n where "n = to_nat k"
    have "k_of n = k"
      unfolding k_of_def n_def by simp
    hence "x \<in> C n"
      unfolding C_def using bk by simp
    thus "x \<in> (\<Union>n. C n)"
      by blast
  qed

  have cut0: "f n y = 0" if "y \<in> C n" for n y
    using that unfolding C_def f_def by simp
  have cutd: "(f n has_derivative L n x) (at x)" for n x
    unfolding f_def L_def by (rule has_derivative_B_dip_x_frechet)
  have rnz: "L n x (r n x) \<noteq> 0" if "x \<in> C n" for n x
  proof -
    have bz: "B_dip (k_of n) x \<omega> \<omega>0 \<omega>s = 0"
      using that unfolding C_def by simp
    show ?thesis
      unfolding L_def r_def
      by (rule B_dip_uslot_transversal[OF cnz bz])
  qed

  show ?thesis
    by (rule chart_core_data_of_functional_cuts[OF cover closedC cut0 cutd rnz])
qed

definition D3H0_slicable_or_Bzero_branch ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_slicable_or_Bzero_branch V \<omega>0 \<omega>s \<omega> =
     D3H0_slicable_branch V \<omega>0 \<omega>s \<omega>
     \<union> D3H0_residual_Bzero_branch V \<omega>0 \<omega>s \<omega>"

lemma fixed_omega_H0core_slicable_or_Bzero_decomp:
  "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n::finite) set)
   = D3H0_slicable_or_Bzero_branch V \<omega>0 \<omega>s \<omega>
     \<union> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>"
  unfolding D3H0_slicable_or_Bzero_branch_def
  using fixed_omega_H0core_slicable_residual_decomp[of V \<omega>0 \<omega>s \<omega>]
    fixed_omega_all_s2_residual_Bzero_decomp[of V \<omega>0 \<omega>s \<omega>]
  by blast

theorem fixed_omega_slicable_or_Bzero_branch_chart_core_data:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_slicable_or_Bzero_branch V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  have slicible: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_slicable_branch V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by (rule fixed_omega_slicable_branch_chart_core_data)
  have bzero: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_residual_Bzero_branch V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by (rule fixed_omega_residual_Bzero_branch_chart_core_data[OF cnz])
  show ?thesis
    unfolding D3H0_slicable_or_Bzero_branch_def
    by (rule chart_core_data_union[OF slicible bzero])
qed

theorem fixed_omega_H0core_chart_core_from_Bnonzero_residual:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and residual: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
proof -
  have resolved: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_slicable_or_Bzero_branch V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by (rule fixed_omega_slicable_or_Bzero_branch_chart_core_data[OF cnz])
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cov: "D3H0_slicable_or_Bzero_branch V \<omega>0 \<omega>s \<omega>
          \<union> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and nsurj: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and cls: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using chart_core_data_union[OF resolved residual] by blast
  have cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    using cov fixed_omega_H0core_slicable_or_Bzero_decomp[of V \<omega>0 \<omega>s \<omega>] by blast
  show ?thesis
    unfolding d3_detHess_arc_chart_core_def
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D] conjI cover der nsurj cls)
qed

corollary fixed_omega_H0core_chart_core_if_no_Bnonzero_residual:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and empty: "D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega> = {}"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
proof (rule fixed_omega_H0core_chart_core_from_Bnonzero_residual[OF cnz])
  show "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    using empty
    by (intro exI[of _ "\<lambda>(_::nat) (x::(real^2)^'n). (x, 0::real^2)"]
        exI[of _ "\<lambda>(_::nat). {} :: ((real^2)^'n) set"]
        exI[of _ "\<lambda>(_::nat) (_::(real^2)^'n). 0 :: (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"])
       simp
qed

theorem fixed_omega_H0core_chart_core_from_factor_phase_residuals:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and factor_data: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    and phase_data: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cov: "D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega>
          \<union> D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and nsurj: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and cls: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using chart_core_data_union[OF factor_data phase_data] by blast
  have residual_data:
    "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
        (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
        (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
         (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
       (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  proof (intro exI[of _ charts] exI[of _ Crit] exI[of _ D] conjI der nsurj cls)
    show "D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
      using cov fixed_omega_Bnonzero_residual_factor_phase_decomp[of V \<omega>0 \<omega>s \<omega>] by blast
  qed
  show ?thesis
    by (rule fixed_omega_H0core_chart_core_from_Bnonzero_residual[OF cnz residual_data])
qed

theorem fixed_omega_H0core_chart_core_from_phase_aligned_residual:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and facnz: "d3_s2_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and phase_data: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cov: "D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and nsurj: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and cls: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using phase_data by blast
  have residual_data:
    "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
        (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
        (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
         (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
       (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  proof (intro exI[of _ charts] exI[of _ Crit] exI[of _ D] conjI der nsurj cls)
    show "D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
    proof
      fix x assume xres: "x \<in> D3H0_residual_Bnonzero_residual V \<omega>0 \<omega>s \<omega>"
      have "x \<in> D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>"
        by (rule fixed_omega_Bnonzero_residual_phase_alignment_if_factor_nonzero[OF facnz xres])
      thus "x \<in> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
        using cov by blast
    qed
  qed
  show ?thesis
    by (rule fixed_omega_H0core_chart_core_from_Bnonzero_residual[OF cnz residual_data])
qed

subsection \<open>The phase-alignment cut: closing the phase-aligned residual\<close>

text \<open>The remaining fixed-\<open>\<omega>\<close> residual (all \<open>s\<^sub>k = 0\<close>, all \<open>B_dip k \<noteq> 0\<close>, factor
  \<open>\<noteq> 0\<close>) is exactly the phase-aligned locus: every \<open>cnj A \<cdot> phase\<^sub>k\<close> is real,
  where \<open>A = A_moment x c\<close>.  The decisive observation is that the alignment
  functional \<open>g\<^sub>k x = Im (cnj (A_moment x c) * phase c x k)\<close> is ITSELF a
  functional cut for its own zero locus: its \<open>x\<close>-derivative in the slot
  direction \<open>slot k u\<close> evaluates to \<open>(c \<bullet> u) \<cdot> (1 - Re (cnj A \<cdot> phase\<^sub>k))\<close>, and
  on the aligned locus not all defects \<open>1 - Re (cnj A \<cdot> phase\<^sub>k)\<close> can vanish
  when \<open>CARD('n) \<ge> 2\<close>: summing \<open>cnj A \<cdot> phase\<^sub>k = 1\<close> over \<open>k\<close> would force
  \<open>\<bar>A\<bar>\<^sup>2 = CARD('n)\<close> while each equation forces \<open>\<bar>A\<bar> = 1\<close>.\<close>

lemma has_derivative_cnjA_phase_x:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2" and k :: 'n
  shows "((\<lambda>y::(real^2)^'n. cnj (A_moment y c) * phase c y k) has_derivative
      (\<lambda>h. cnj (A_moment x c) * d_phase c x h k
         + cnj (d_A_moment_x x c h) * phase c x k)) (at x)"
proof -
  have hA: "((\<lambda>y::(real^2)^'n. A_moment y c) has_derivative
      (\<lambda>h. d_A_moment_x x c h)) (at x)"
    by (rule has_derivative_A_moment_x[where V = UNIV])
  have hcnjA: "((\<lambda>y::(real^2)^'n. cnj (A_moment y c)) has_derivative
      (\<lambda>h. cnj (d_A_moment_x x c h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_cnj hA])
  have hP: "((\<lambda>y::(real^2)^'n. phase c y k) has_derivative
      (\<lambda>h. d_phase c x h k)) (at x)"
    by (rule has_derivative_phase_x[where V = UNIV])
  show ?thesis
    by (rule has_derivative_mult[OF hcnjA hP])
qed

lemma has_derivative_phase_align_x:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2" and k :: 'n
  shows "((\<lambda>y::(real^2)^'n. Im (cnj (A_moment y c) * phase c y k)) has_derivative
      (\<lambda>h. Im (cnj (A_moment x c) * d_phase c x h k
             + cnj (d_A_moment_x x c h) * phase c x k))) (at x)"
  by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_cnjA_phase_x])

lemma phase_align_slot_self_value:
  fixes x :: "(real^2)^'n::finite" and c u :: "real^2" and k :: 'n
  shows "Im (cnj (A_moment x c) * d_phase c x (slot k u) k
           + cnj (d_A_moment_x x c (slot k u)) * phase c x k)
       = (c \<bullet> u) * (1 - Re (cnj (A_moment x c) * phase c x k))"
proof -
  have dP: "d_phase c x (slot k u) k = -(c \<bullet> u) *\<^sub>R (\<i> * phase c x k)"
    by (simp add: d_phase_slot phase_def)
  have dA: "d_A_moment_x x c (slot k u) = -(c \<bullet> u) *\<^sub>R (\<i> * phase c x k)"
    by (rule d_A_moment_x_slot)
  have unitP: "cnj (phase c x k) * phase c x k = 1"
    unfolding phase_def by (simp add: cis_cnj cis_mult)
  have term2: "cnj (d_A_moment_x x c (slot k u)) * phase c x k = (c \<bullet> u) *\<^sub>R \<i>"
  proof -
    have "cnj (d_A_moment_x x c (slot k u)) * phase c x k
        = -(c \<bullet> u) *\<^sub>R ((cnj \<i> * cnj (phase c x k)) * phase c x k)"
      by (simp add: dA)
    also have "\<dots> = -(c \<bullet> u) *\<^sub>R (cnj \<i> * (cnj (phase c x k) * phase c x k))"
      by (simp only: mult.assoc)
    also have "\<dots> = -(c \<bullet> u) *\<^sub>R (- \<i>)"
      by (simp add: unitP)
    also have "\<dots> = (c \<bullet> u) *\<^sub>R \<i>"
      by simp
    finally show ?thesis .
  qed
  have term1: "cnj (A_moment x c) * d_phase c x (slot k u) k
      = -(c \<bullet> u) *\<^sub>R (\<i> * (cnj (A_moment x c) * phase c x k))"
    by (simp add: dP mult.left_commute)
  show ?thesis
    unfolding term1 term2
    by (simp add: scaleR_conv_of_real ring_distribs)
qed

lemma continuous_on_phase_align_x:
  "continuous_on UNIV
     (\<lambda>x::(real^2)^'n::finite. Im (cnj (A_moment x c) * phase c x k))"
proof (rule continuous_at_imp_continuous_on, rule ballI)
  fix x :: "(real^2)^'n"
  assume "x \<in> UNIV"
  show "continuous (at x) (\<lambda>x::(real^2)^'n. Im (cnj (A_moment x c) * phase c x k))"
    by (rule has_derivative_continuous[OF has_derivative_phase_align_x])
qed

lemma continuous_on_phase_align_defect_x:
  "continuous_on UNIV
     (\<lambda>x::(real^2)^'n::finite. 1 - Re (cnj (A_moment x c) * phase c x k))"
proof -
  have hRe: "((\<lambda>y::(real^2)^'n. Re (cnj (A_moment y c) * phase c y k)) has_derivative
      (\<lambda>h. Re (cnj (A_moment x c) * d_phase c x h k
             + cnj (d_A_moment_x x c h) * phase c x k))) (at x)"
    for x :: "(real^2)^'n"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_cnjA_phase_x])
  have contRe: "continuous_on UNIV
      (\<lambda>x::(real^2)^'n. Re (cnj (A_moment x c) * phase c x k))"
  proof (rule continuous_at_imp_continuous_on, rule ballI)
    fix x :: "(real^2)^'n"
    assume "x \<in> UNIV"
    show "continuous (at x) (\<lambda>x::(real^2)^'n. Re (cnj (A_moment x c) * phase c x k))"
      by (rule has_derivative_continuous[OF hRe])
  qed
  show ?thesis
    by (intro continuous_intros contRe)
qed

lemma closed_phase_align_zero:
  "closed {x::(real^2)^'n::finite. Im (cnj (A_moment x c) * phase c x k) = 0}"
  by (rule closed_Collect_eq[OF continuous_on_phase_align_x continuous_on_const])

lemma phase_aligned_defect_witness:
  fixes x :: "(real^2)^'n::finite" and c :: "real^2"
  assumes card2: "2 \<le> CARD('n)"
    and aligned: "\<And>k::'n. Im (cnj (A_moment x c) * phase c x k) = 0"
  shows "\<exists>k::'n. 1 - Re (cnj (A_moment x c) * phase c x k) \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>k::'n. 1 - Re (cnj (A_moment x c) * phase c x k) \<noteq> 0)"
  hence re1: "Re (cnj (A_moment x c) * phase c x k) = 1" for k :: 'n
    by auto
  have unit: "cnj (A_moment x c) * phase c x k = 1" for k :: 'n
    using re1[of k] aligned[of k]
    by (intro complex_eqI) simp_all
  have modP: "cmod (phase c x k) = 1" for k :: 'n
    by (simp add: phase_def)
  have modA: "cmod (A_moment x c) = 1"
  proof -
    obtain k :: 'n where True by blast
    have "cmod (cnj (A_moment x c) * phase c x k) = 1"
      using unit[of k] by simp
    thus ?thesis
      using modP[of k] by (simp add: norm_mult)
  qed
  have sumA: "cnj (A_moment x c) * A_moment x c = of_nat (CARD('n))"
  proof -
    have "cnj (A_moment x c) * A_moment x c
        = (\<Sum>k\<in>(UNIV::'n set). cnj (A_moment x c) * phase c x k)"
      unfolding A_moment_def by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>k\<in>(UNIV::'n set). 1)"
      by (simp only: unit)
    also have "\<dots> = of_nat (CARD('n))"
      by simp
    finally show ?thesis.
  qed
  have "cmod (cnj (A_moment x c) * A_moment x c) = 1"
    by (simp add: norm_mult modA)
  hence "real (CARD('n)) = 1"
    using sumA by simp
  thus False
    using card2 by simp
qed

theorem fixed_omega_phase_aligned_residual_chart_core_data:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define k_of :: "nat \<Rightarrow> 'n" where
    "k_of n = from_nat (fst (prod_decode n))" for n
  define m_of :: "nat \<Rightarrow> nat" where
    "m_of n = snd (prod_decode n)" for n
  define f where "f = (\<lambda>n (x::(real^2)^'n).
      Im (cnj (A_moment x c) * phase c x (k_of n)))"
  define L where "L = (\<lambda>n (x::(real^2)^'n) (h::(real^2)^'n).
      Im (cnj (A_moment x c) * d_phase c x h (k_of n)
        + cnj (d_A_moment_x x c h) * phase c x (k_of n)))"
  define r where "r = (\<lambda>n (x::(real^2)^'n). slot (k_of n) c)"
  define C where "C = (\<lambda>n. {x::(real^2)^'n.
        Im (cnj (A_moment x c) * phase c x (k_of n)) = 0}
      \<inter> {x. inverse (real (Suc (m_of n)))
             \<le> \<bar>1 - Re (cnj (A_moment x c) * phase c x (k_of n))\<bar>})"

  have cutd: "(f n has_derivative L n x) (at x)" for n x
    unfolding f_def L_def by (rule has_derivative_phase_align_x)

  have closedC: "closed (C n)" for n
  proof -
    have c0: "closed {x::(real^2)^'n.
        Im (cnj (A_moment x c) * phase c x (k_of n)) = 0}"
      by (rule closed_phase_align_zero)
    have ct: "closed {x::(real^2)^'n.
        inverse (real (Suc (m_of n)))
          \<le> \<bar>1 - Re (cnj (A_moment x c) * phase c x (k_of n))\<bar>}"
      by (rule closed_abs_ge_threshold[OF continuous_on_phase_align_defect_x])
    show ?thesis
      unfolding C_def by (intro closed_Int c0 ct)
  qed

  have cut0: "f n y = 0" if "y \<in> C n" for n y
    using that unfolding C_def f_def by simp

  have cnz': "c \<bullet> c \<noteq> 0"
    using cnz unfolding c_def by simp

  have rnz: "L n x (r n x) \<noteq> 0" if "x \<in> C n" for n x
  proof -
    have ge: "inverse (real (Suc (m_of n)))
        \<le> \<bar>1 - Re (cnj (A_moment x c) * phase c x (k_of n))\<bar>"
      using that unfolding C_def by simp
    have "1 - Re (cnj (A_moment x c) * phase c x (k_of n)) \<noteq> 0"
      using ge by fastforce
    moreover have "L n x (r n x)
        = (c \<bullet> c) * (1 - Re (cnj (A_moment x c) * phase c x (k_of n)))"
      unfolding L_def r_def by (rule phase_align_slot_self_value)
    ultimately show ?thesis
      using cnz' by simp
  qed

  have cover: "D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>n. C n)"
  proof
    fix x assume xR: "x \<in> D3H0_Bnonzero_phase_aligned_residual V \<omega>0 \<omega>s \<omega>"
    have aligned: "Im (cnj (A_moment x c) * phase c x k) = 0" for k :: 'n
    proof -
      have "Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
          * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0"
        using xR unfolding D3H0_Bnonzero_phase_aligned_residual_def by blast
      thus ?thesis
        unfolding c_def by simp
    qed
    obtain k :: 'n where defect: "1 - Re (cnj (A_moment x c) * phase c x k) \<noteq> 0"
      using phase_aligned_defect_witness[OF card2 aligned] by blast
    have pos: "0 < \<bar>1 - Re (cnj (A_moment x c) * phase c x k)\<bar>"
      using defect by simp
    obtain m where m: "inverse (real (Suc m))
        < \<bar>1 - Re (cnj (A_moment x c) * phase c x k)\<bar>"
      using reals_Archimedean[OF pos] by blast
    define n where "n = prod_encode (to_nat k, m)"
    have kd: "k_of n = k"
      unfolding k_of_def n_def by simp
    have md: "m_of n = m"
      unfolding m_of_def n_def by simp
    have "x \<in> C n"
      unfolding C_def kd md using aligned[of k] m by auto
    thus "x \<in> (\<Union>n. C n)"
      by blast
  qed

  show ?thesis
    by (rule chart_core_data_of_functional_cuts[OF cover closedC cut0 cutd rnz])
qed

subsection \<open>The fixed-\<open>\<omega>\<close> chart core under angle-only side conditions\<close>

theorem fixed_omega_H0core_chart_core_from_factorzero_residual:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
    and factor_data: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_Bnonzero_factorzero_residual V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
  by (rule fixed_omega_H0core_chart_core_from_factor_phase_residuals[OF cnz factor_data
        fixed_omega_phase_aligned_residual_chart_core_data[OF cnz card2]])

theorem fixed_omega_H0core_chart_core_of_angle_conditions:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and facnz: "d3_s2_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
  by (rule fixed_omega_H0core_chart_core_from_phase_aligned_residual[OF cnz facnz
        fixed_omega_phase_aligned_residual_chart_core_data[OF cnz card2]])

text \<open>At the Robust4 design point \<open>\<omega>\<^sub>0 = (\<pi>/2, 0)\<close>, \<open>\<omega>\<^sub>s = 0\<close>, \<open>\<omega> = (\<pi>/2, \<pi>/3)\<close>,
  both angle conditions are literally the geodesic branch's side-condition
  facts: \<open>cvec \<noteq> 0\<close> is condition (2), and the global factor is
  \<open>2 \<cdot> gain \<cdot> (Dcvec(axis 2 1) \<bullet> perp2 c) = -2 \<cdot> (D\<^sub>1 c\<^sub>2 - D\<^sub>2 c\<^sub>1)\<close>, the negative
  of condition (3), with \<open>gain = gdip(\<pi>/2) = 1\<close>.\<close>

theorem fixed_omega_H0core_chart_core_robust4_witness:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0])
      {vector [pi / 2, pi / 3]}"
proof (rule fixed_omega_H0core_chart_core_of_angle_conditions)
  show "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 3]) \<noteq> 0"
    by (rule h12rad_robust4_omega_side_conditions(2))
  show "2 \<le> CARD('n)"
    by (rule card2)
  have gain: "gain_dip (vector [pi / 2, pi / 3]) = 1"
    unfolding gain_dip_def by (simp only: vector_2 gdip_pi_half)
  have key: "vec_nth (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
          (vector [pi / 2, pi / 3]) (axis (2::2) 1)) 1
      * vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
          (vector [pi / 2, pi / 3])) 2
      - vec_nth (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
          (vector [pi / 2, pi / 3]) (axis (2::2) 1)) 2
        * vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
          (vector [pi / 2, pi / 3])) 1
      \<noteq> 0"
    by (rule h12rad_robust4_omega_side_conditions(3))
  have expand: "Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
        (vector [pi / 2, pi / 3]) (axis (2::2) 1)
      \<bullet> perp2 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) (vector [pi / 2, pi / 3]))
      = - (vec_nth (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3]) (axis (2::2) 1)) 1
          * vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3])) 2
        - vec_nth (Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3]) (axis (2::2) 1)) 2
          * vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0])
            (vector [pi / 2, pi / 3])) 1)"
    by (simp add: perp2_def inner_vec_def sum_2 vector_2 algebra_simps)
  show "d3_s2_global_factor (vector [pi / 2, 0]) (vector [0, 0])
      (vector [pi / 2, pi / 3]) \<noteq> 0"
    unfolding d3_s2_global_factor_def expand
    using key by (simp add: gain)
qed

subsection \<open>Arc chart core from countably many fixed-\<open>\<omega>\<close> pieces\<close>

lemma chart_core_data_countable_UN:
  fixes S :: "nat \<Rightarrow> ((real^2)^'n::finite) set"
  assumes data: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
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
         (\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
proof -
    have h0:
    "\<forall>i. \<exists>(charts_i :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit_i :: nat \<Rightarrow> ((real^2)^'n) set)
            (D_i :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       S i \<subseteq> (\<Union>j. (fst \<circ> charts_i j) ` (Crit_i j)) \<and>
       (\<forall>j x. x \<in> Crit_i j \<longrightarrow>
          ((fst \<circ> charts_i j) has_derivative
            (blinfun_apply (D_i j x))) (at x within Crit_i j)) \<and>
       (\<forall>j x. x \<in> Crit_i j \<longrightarrow>
          \<not> surj (blinfun_apply (D_i j x))) \<and>
       (\<forall>j. closed ((fst \<circ> charts_i j) ` (Crit_i j)))"
    using data by blast

  obtain charts ::
      "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    where hcharts:
      "\<forall>i. \<exists>(Crit_i :: nat \<Rightarrow> ((real^2)^'n) set)
              (D_i :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
                (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit_i j)) \<and>
         (\<forall>j x. x \<in> Crit_i j \<longrightarrow>
            ((fst \<circ> charts i j) has_derivative
              (blinfun_apply (D_i j x))) (at x within Crit_i j)) \<and>
         (\<forall>j x. x \<in> Crit_i j \<longrightarrow>
            \<not> surj (blinfun_apply (D_i j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit_i j)))"
  proof -
    have "\<exists>charts ::
        nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)).
        \<forall>i. \<exists>(Crit_i :: nat \<Rightarrow> ((real^2)^'n) set)
                (D_i :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
                  (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
           S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit_i j)) \<and>
           (\<forall>j x. x \<in> Crit_i j \<longrightarrow>
              ((fst \<circ> charts i j) has_derivative
                (blinfun_apply (D_i j x))) (at x within Crit_i j)) \<and>
           (\<forall>j x. x \<in> Crit_i j \<longrightarrow>
              \<not> surj (blinfun_apply (D_i j x))) \<and>
           (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit_i j)))"
      using assms by (subst choice, auto)
      then obtain charts' ::
        "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
      where hcharts':
        "\<forall>i. \<exists>(Crit_i :: nat \<Rightarrow> ((real^2)^'n) set)
                (D_i :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
                  (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
           S i \<subseteq> (\<Union>j. (fst \<circ> charts' i j) ` (Crit_i j)) \<and>
           (\<forall>j x. x \<in> Crit_i j \<longrightarrow>
              ((fst \<circ> charts' i j) has_derivative
                (blinfun_apply (D_i j x))) (at x within Crit_i j)) \<and>
           (\<forall>j x. x \<in> Crit_i j \<longrightarrow>
              \<not> surj (blinfun_apply (D_i j x))) \<and>
           (\<forall>j. closed ((fst \<circ> charts' i j) ` (Crit_i j)))"
      by blast
    show ?thesis
      by (rule that[OF hcharts'])
  qed

  obtain Crit :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
    where hCrit:
      "\<forall>i. \<exists>(D_i :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
                (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit i j)) \<and>
         (\<forall>j x. x \<in> Crit i j \<longrightarrow>
            ((fst \<circ> charts i j) has_derivative
              (blinfun_apply (D_i j x))) (at x within Crit i j)) \<and>
         (\<forall>j x. x \<in> Crit i j \<longrightarrow>
            \<not> surj (blinfun_apply (D_i j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit i j)))"
  proof -
    have "\<exists>Crit :: nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set.
        \<forall>i. \<exists>(D_i :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
                  (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
           S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit i j)) \<and>
           (\<forall>j x. x \<in> Crit i j \<longrightarrow>
              ((fst \<circ> charts i j) has_derivative
                (blinfun_apply (D_i j x))) (at x within Crit i j)) \<and>
           (\<forall>j x. x \<in> Crit i j \<longrightarrow>
              \<not> surj (blinfun_apply (D_i j x))) \<and>
           (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit i j)))"
      using hcharts
      by (subst choice, auto)
    then obtain Crit' :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
      where hCrit':
        "\<forall>i. \<exists>(D_i :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
                  (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
           S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit' i j)) \<and>
           (\<forall>j x. x \<in> Crit' i j \<longrightarrow>
              ((fst \<circ> charts i j) has_derivative
                (blinfun_apply (D_i j x))) (at x within Crit' i j)) \<and>
           (\<forall>j x. x \<in> Crit' i j \<longrightarrow>
              \<not> surj (blinfun_apply (D_i j x))) \<and>
           (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit' i j)))"
      by blast
    show ?thesis
      by (rule that[OF hCrit'])
  qed

  obtain D ::
      "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
        (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where hall:
      "\<forall>i.
         S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit i j)) \<and>
         (\<forall>j x. x \<in> Crit i j \<longrightarrow>
            ((fst \<circ> charts i j) has_derivative
              (blinfun_apply (D i j x))) (at x within Crit i j)) \<and>
         (\<forall>j x. x \<in> Crit i j \<longrightarrow>
            \<not> surj (blinfun_apply (D i j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit i j)))"
  proof -
    have "\<exists>D ::
        nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n)).
        \<forall>i.
           S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit i j)) \<and>
           (\<forall>j x. x \<in> Crit i j \<longrightarrow>
              ((fst \<circ> charts i j) has_derivative
                (blinfun_apply (D i j x))) (at x within Crit i j)) \<and>
           (\<forall>j x. x \<in> Crit i j \<longrightarrow>
              \<not> surj (blinfun_apply (D i j x))) \<and>
           (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit i j)))"
      using hCrit
      by (subst choice, auto)
    then obtain D' ::
        "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) \<Rightarrow>
          (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      where hall':
        "\<forall>i.
           S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit i j)) \<and>
           (\<forall>j x. x \<in> Crit i j \<longrightarrow>
              ((fst \<circ> charts i j) has_derivative
                (blinfun_apply (D' i j x))) (at x within Crit i j)) \<and>
           (\<forall>j x. x \<in> Crit i j \<longrightarrow>
              \<not> surj (blinfun_apply (D' i j x))) \<and>
           (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit i j)))"
      by blast
    show ?thesis
      by (rule that[OF hall'])
  qed


  have cov: "\<And>i. S i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit i j))"
    using hall by presburger

  have der: "\<And>i. \<forall>j x. x \<in> Crit i j \<longrightarrow>
      ((fst \<circ> charts i j) has_derivative (blinfun_apply (D i j x))) (at x within Crit i j)"
    using hall by blast

  have nsurj: "\<And>i. \<forall>j x. x \<in> Crit i j \<longrightarrow> \<not> surj (blinfun_apply (D i j x))"
    using hall by blast

  have cls: "\<And>i. \<forall>j. closed ((fst \<circ> charts i j) ` (Crit i j))"
    using hall by blast
  define i_of :: "nat \<Rightarrow> nat" where "i_of n = fst (prod_decode n)" for n
  define j_of :: "nat \<Rightarrow> nat" where "j_of n = snd (prod_decode n)" for n
  define charts' where "charts' = (\<lambda>n. charts (i_of n) (j_of n))"
  define Crit' where "Crit' = (\<lambda>n. Crit (i_of n) (j_of n))"
  define D' where "D' = (\<lambda>n. D (i_of n) (j_of n))"
  have cover: "(\<Union>i. S i) \<subseteq> (\<Union>n. (fst \<circ> charts' n) ` (Crit' n))"
  proof
    fix x assume "x \<in> (\<Union>i. S i)"
    then obtain i where xS: "x \<in> S i"
      by blast
    then obtain j y where yC: "y \<in> Crit i j"
      and xeq: "x = (fst \<circ> charts i j) y"
      using cov[of i] by blast
    define n where "n = prod_encode (i, j)"
    have io: "i_of n = i"
      unfolding i_of_def n_def by simp
    have jo: "j_of n = j"
      unfolding j_of_def n_def by simp
    have "y \<in> Crit' n"
      unfolding Crit'_def io jo using yC .
    moreover have "x = (fst \<circ> charts' n) y"
      unfolding charts'_def io jo using xeq .
    ultimately show "x \<in> (\<Union>n. (fst \<circ> charts' n) ` (Crit' n))"
      by blast
  qed
  have der': "\<forall>n x. x \<in> Crit' n \<longrightarrow>
      ((fst \<circ> charts' n) has_derivative (blinfun_apply (D' n x))) (at x within Crit' n)"
    unfolding charts'_def Crit'_def D'_def using der by blast
  have nsurj': "\<forall>n x. x \<in> Crit' n \<longrightarrow> \<not> surj (blinfun_apply (D' n x))"
    unfolding Crit'_def D'_def using nsurj by blast
  have cls': "\<forall>n. closed ((fst \<circ> charts' n) ` (Crit' n))"
    unfolding charts'_def Crit'_def using cls by blast
  show ?thesis
    by (intro exI[of _ charts'] exI[of _ Crit'] exI[of _ D'] conjI cover der' nsurj' cls')
qed

theorem d3_chart_core_of_countable_fixed_omega_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and om :: "nat \<Rightarrow> real^2"
    and \<gamma> :: "(real^2) set"
    and \<omega>0 \<omega>s :: "real^2"
  assumes cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
    and core: "\<And>i. d3_detHess_arc_chart_core V \<omega>0 \<omega>s {om i}"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
proof -
  define S where "S = (\<lambda>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i} :: ((real^2)^'n) set)"
  have data: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    using core unfolding S_def d3_detHess_arc_chart_core_def by blast
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where all_data:
      "(\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
       (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
       (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
       (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  proof -
    have ex_data: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
      by (rule chart_core_data_countable_UN[OF data])
    then show ?thesis
    proof (elim exE)
      fix charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
        and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
        and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      assume all_data:
        "(\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
      show ?thesis
        by (rule that[OF all_data])
    qed
  qed
  from all_data have cov: "(\<Union>i. S i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))"
    by (rule conjunct1)
  from all_data have rest_data1: "(\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
       (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
       (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    by (rule conjunct2)
  from rest_data1 have der: "\<forall>j x. x \<in> Crit j \<longrightarrow>
        ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)"
    by (rule conjunct1)
  from rest_data1 have rest_data2:
      "(\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
       (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    by (rule conjunct2)
  from rest_data2 have nsurj: "\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))"
    by (rule conjunct1)
  from rest_data2 have cls: "\<forall>j. closed ((fst \<circ> charts j) ` (Crit j))"
    by (rule conjunct2)
  have cover': "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
      \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))"
    using cover cov unfolding S_def by blast
  show ?thesis
    unfolding d3_detHess_arc_chart_core_def
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D] conjI cover' der nsurj cls)
qed

theorem d3_chart_core_all_of_countable_fixed_omega_angle_cover:
  fixes V :: "((real^2)^'n::finite) set"
  assumes card2: "2 \<le> CARD('n)"
    and cover: "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>om :: nat \<Rightarrow> real^2.
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})
        \<and> (\<forall>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0)
        \<and> (\<forall>i. d3_s2_global_factor \<omega>0 \<omega>s (om i) \<noteq> 0)"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  obtain om :: "nat \<Rightarrow> real^2"
    where cov: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})"
      and cnz: "\<forall>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0"
      and facnz: "\<forall>i. d3_s2_global_factor \<omega>0 \<omega>s (om i) \<noteq> 0"
    using cover[OF arc gsub] by blast
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  proof (rule d3_chart_core_of_countable_fixed_omega_cover[OF cov])
    fix i
    show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {om i}"
      by (rule fixed_omega_H0core_chart_core_of_angle_conditions[OF _ _ card2])
         (use cnz facnz in auto)
  qed
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

subsection \<open>Capstone-facing D3 frontier reductions\<close>

theorem F0_dip_nonempty_from_countable_fixed_omega_angle_covers:
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and d3covers: "\<And>(V::(planar^'n) set) ctr \<delta> \<omega>0 \<omega>s \<gamma>.
      analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>om :: nat \<Rightarrow> real^2.
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: (planar^'n) set)
          \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})
        \<and> (\<forall>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0)
        \<and> (\<forall>i. d3_s2_global_factor \<omega>0 \<omega>s (om i) \<noteq> 0)"
    and branchcore: "\<And>(V::(planar^'n) set) ctr \<delta> \<omega>0 \<omega>s.
      branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "\<exists>A B D \<omega>0 \<omega>s \<omega>null ctr \<delta> R dmin \<delta>null pmin \<xi> \<kappa> \<epsilon>.
            0 < \<delta> \<and> 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr
              (OmegaPF ctr \<delta>) \<delta>null pmin \<xi> \<kappa> \<epsilon> \<noteq> ({}::(planar^'n) set)"
proof (rule F0_dip_nonempty[OF c6 oddN])
  fix V :: "(planar^'n) set" and ctr \<omega>0 \<omega>s :: planar and \<delta> :: real
  show "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  proof (rule d3_chart_core_all_of_countable_fixed_omega_angle_cover)
    show "2 \<le> CARD('n)"
      using c6 by simp
    show "\<And>\<gamma>. analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>om :: nat \<Rightarrow> real^2.
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: (planar^'n) set)
          \<subseteq> (\<Union>i. V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {om i})
        \<and> (\<forall>i. cvec_dip \<omega>0 \<omega>s (om i) \<noteq> 0)
        \<and> (\<forall>i. d3_s2_global_factor \<omega>0 \<omega>s (om i) \<noteq> 0)"
      by (rule d3covers)
  qed
next
  fix V :: "(planar^'n) set" and ctr \<omega>0 \<omega>s :: planar and \<delta> :: real
  show "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
    by (rule branchcore)
qed

theorem F0_dip_nonempty_from_fixed_omega_piece_covers:
  assumes c6: "6 \<le> CARD('n)" and oddN: "odd CARD('n)"
    and d3pieces: "\<And>(V::(planar^'n) set) ctr \<delta> \<omega>0 \<omega>s \<gamma>.
      analytic_arc \<gamma> \<Longrightarrow> \<gamma> \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      \<exists>(Cp :: nat \<Rightarrow> (planar^'n) set) (om :: nat \<Rightarrow> real^2) (ki :: nat \<Rightarrow> 'n).
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: (planar^'n) set) \<subseteq> (\<Union>i. Cp i)
      \<and> (\<forall>i. closed (Cp i))
      \<and> (\<forall>i. Cp i \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s {om i})
      \<and> (\<forall>i x. x \<in> Cp i \<longrightarrow>
          frechet_derivative
            (\<lambda>y::planar^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (om i)) 2) (at x)
            (slot (ki i) (perp2 (cvec_dip \<omega>0 \<omega>s (om i)))) \<noteq> 0)"
    and branchcore: "\<And>(V::(planar^'n) set) ctr \<delta> \<omega>0 \<omega>s.
      branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
  shows "\<exists>A B D \<omega>0 \<omega>s \<omega>null ctr \<delta> R dmin \<delta>null pmin \<xi> \<kappa> \<epsilon>.
            0 < \<delta> \<and> 0 < \<xi> \<and> 0 < \<kappa> \<and> 0 < \<epsilon>
          \<and> F0 (cvec_dip \<omega>0 \<omega>s) gain_dip R dmin A B D \<omega>null ctr
              (OmegaPF ctr \<delta>) \<delta>null pmin \<xi> \<kappa> \<epsilon> \<noteq> ({}::(planar^'n) set)"
proof (rule F0_dip_nonempty[OF c6 oddN])
  fix V :: "(planar^'n) set" and ctr \<omega>0 \<omega>s :: planar and \<delta> :: real
  show "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  proof (rule d3_chart_core_all_of_fixed_omega_piece_covers)
    fix \<gamma>
    assume arc: "analytic_arc \<gamma>" and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
    show "\<exists>(Cp :: nat \<Rightarrow> (planar^'n) set) (om :: nat \<Rightarrow> real^2) (ki :: nat \<Rightarrow> 'n).
        (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: (planar^'n) set) \<subseteq> (\<Union>i. Cp i)
      \<and> (\<forall>i. closed (Cp i))
      \<and> (\<forall>i. Cp i \<subseteq> D3BadXG_H0core \<omega>0 \<omega>s {om i})
      \<and> (\<forall>i x. x \<in> Cp i \<longrightarrow>
          frechet_derivative
            (\<lambda>y::planar^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (om i)) 2) (at x)
            (slot (ki i) (perp2 (cvec_dip \<omega>0 \<omega>s (om i)))) \<noteq> 0)"
      by (rule d3pieces[OF arc gsub])
  qed
next
  fix V :: "(planar^'n) set" and ctr \<omega>0 \<omega>s :: planar and \<delta> :: real
  show "branchP_indep_closed_cover_core_all V ctr \<delta> \<omega>0 \<omega>s"
    by (rule branchcore)
qed

subsection \<open>Robust4-design capstone reductions\<close>

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

subsection \<open>The component-1 twin factor: at most one of the two can vanish\<close>

text \<open>@{const d3_s2_global_factor} is one of two mirror invariants arising from
  @{thm gradU_dip_xderiv_perp_slot}, which gives the SAME perp-slot phase
  structure for both gradU components \<open>j = 1, 2\<close> --- only the linear
  coefficient \<open>Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> perp2 c\<close> differs.  The
  component-1 twin is defined identically with \<open>j = 1\<close>.\<close>

definition d3_s1_global_factor :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "d3_s1_global_factor \<omega>0 \<omega>s \<omega> =
     2 * gain_dip \<omega>
       * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))"

text \<open>Both factors vanishing would force \<open>perp2 c\<close> orthogonal to BOTH basis
  vectors under the linear map \<open>Dcvec_dip \<omega>0 \<omega>s \<omega>\<close>, hence (by linearity)
  orthogonal to its entire range; if that map is a bijection of \<open>real^2\<close>
  (\<open>det (matrix Dcvec) \<noteq> 0\<close>) the range is all of \<open>real^2\<close>, forcing
  \<open>perp2 c = 0\<close>, hence \<open>c = 0\<close> (@{thm perp2_nz}) --- contradicting
  \<open>cvec \<noteq> 0\<close>.  So under the non-degeneracy conditions \<open>cvec \<noteq> 0\<close>,
  \<open>det (matrix Dcvec) \<noteq> 0\<close>, \<open>gain_dip \<omega> \<noteq> 0\<close> --- all purely angle-only,
  none referring to any specific \<open>x\<close> --- at least one of the two factors is
  nonzero.  This is the frontier-push beyond the Robust4-witness result: it
  replaces the ad-hoc pointwise fact \<open>d3_s2_global_factor \<noteq> 0\<close> with a
  disjunction of two angle-only conditions that together are implied by
  ordinary non-degeneracy alone.\<close>

lemma d3_s1_or_s2_global_factor_nonzero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
  shows "d3_s1_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0 \<or> d3_s2_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0"
proof (rule ccontr)
  assume contra: "\<not> ?thesis"
  define v where "v = perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)"
  from contra have f1z: "d3_s1_global_factor \<omega>0 \<omega>s \<omega> = 0"
    and f2z: "d3_s2_global_factor \<omega>0 \<omega>s \<omega> = 0"
    by simp_all
  have d1z: "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v = 0"
    using f1z gnz unfolding d3_s1_global_factor_def v_def by (simp add: mult_eq_0_iff)
  have d2z: "Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v = 0"
    using f2z gnz unfolding d3_s2_global_factor_def v_def by (simp add: mult_eq_0_iff)
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have decomp: "\<And>h::real^2. h = vec_nth h 1 *\<^sub>R axis 1 1 + vec_nth h 2 *\<^sub>R axis 2 1"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix h :: "real^2" and i :: 2
    show "vec_nth h i = vec_nth (vec_nth h 1 *\<^sub>R axis 1 1 + vec_nth h 2 *\<^sub>R axis 2 1) i"
      using exhaust_2[of i] by (auto simp: axis_def)
  qed
  have split: "Dcvec_dip \<omega>0 \<omega>s \<omega> h
      = vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
      + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)" for h :: "real^2"
    using decomp[of h] linear_add[OF lin] linear_cmul[OF lin] by metis
  have allz: "Dcvec_dip \<omega>0 \<omega>s \<omega> h \<bullet> v = 0" for h :: "real^2"
    unfolding split[of h] by (simp add: inner_add_left d1z d2z)
  have mv: "matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v h = Dcvec_dip \<omega>0 \<omega>s \<omega> h" for h :: "real^2"
  proof -
    have expand: "matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v h
        = vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
        + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
    proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
      fix i :: 2
      show "vec_nth (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v h) i
          = vec_nth (vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
                   + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) i"
        by (simp add: matrix_def matrix_vector_mult_def sum_2 algebra_simps)
    qed
    with split[of h] show ?thesis by simp
  qed
  have bij: "bij ((*v) (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)))"
    by (rule bij_matrix_vector_mult[OF detnz])
  have surjmv: "\<forall>y. \<exists>x. y = matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v x"
    using bij_is_surj[OF bij] unfolding surj_def .
  obtain h where hv: "v = matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v h" using surjmv by blast
  hence hv': "v = Dcvec_dip \<omega>0 \<omega>s \<omega> h" using mv by simp
  have "v \<bullet> v = 0"
    using allz[of h] hv' by simp
  hence "v = 0" by simp
  hence "perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    unfolding v_def .
  moreover have "perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) \<noteq> 0"
    by (rule perp2_nz[OF cnz])
  ultimately show False by simp
qed

subsection \<open>The component-1 mirror ladder\<close>

text \<open>Everything in the fixed-\<open>\<omega>\<close> chart-core ladder above (the slicable branch,
  the \<open>B_dip\<close>-zero residual, the factor/phase split) was built from gradU's
  component 2.  @{thm gradU_dip_xderiv_perp_slot} gives the IDENTICAL perp-slot
  phase structure for component 1 --- same \<open>M_paper x c $ 1\<close> phase factor,
  only the linear coefficient \<open>Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> perp2 c\<close>
  changes with \<open>j\<close>.  So the phase-alignment-cut subsection above is reused
  UNCHANGED; only the slicable/Bzero/Bnonzero layer needs a mirror, built
  from gradU's component 1.\<close>

lemma has_derivative_gradU_dip_component1_x_frechet:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) has_derivative
      frechet_derivative
        (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) (at x)) (at x)"
proof -
  have h: "((\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) has_derivative
        (dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (1::2) 1) 1)) (gain_dip \<omega>)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1)) 1)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis (1::2) 1)) 2)
             (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
         \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x)"
    by (rule has_derivative_gradU_dip_component_x)
  show ?thesis
    using h frechet_derivative_at[OF h] by simp
qed

definition d3_s1_perp_slot ::
  "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 'n::finite \<Rightarrow> ((real^2)^'n) \<Rightarrow> real" where
  "d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x =
     frechet_derivative
       (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) (at x)
       (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"

lemma d3_s1_perp_slot_value:
  fixes x :: "(real^2)^'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x
       = d3_s1_global_factor \<omega>0 \<omega>s \<omega>
           * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
               * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k)"
proof -
  have hd1: "((\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) has_derivative
       (\<lambda>h. vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 1)) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_gradU_dip_x_explicit])
  have val: "d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x
      = vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>)
                    (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))) 1"
    unfolding d3_s1_perp_slot_def
    by (rule fun_cong[OF frechet_derivative_at[OF hd1, symmetric]])
  show ?thesis
    unfolding val d3_s1_global_factor_def
    using arg_cong[where f = "\<lambda>V. vec_nth V 1", OF gradU_dip_xderiv_perp_slot[OF perp2_orth]]
    by simp
qed

definition D3H0_slicable_branch1 ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_slicable_branch1 V \<omega>0 \<omega>s \<omega> =
     {x \<in> V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}. \<exists>k. d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x \<noteq> 0}"

definition D3H0_all_s1_zero_residual ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_all_s1_zero_residual V \<omega>0 \<omega>s \<omega> =
     {x \<in> V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}. \<forall>k. d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x = 0}"

lemma fixed_omega_H0core_slicable_residual_decomp1:
  "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n::finite) set)
   = D3H0_slicable_branch1 V \<omega>0 \<omega>s \<omega> \<union> D3H0_all_s1_zero_residual V \<omega>0 \<omega>s \<omega>"
  unfolding D3H0_slicable_branch1_def D3H0_all_s1_zero_residual_def by blast

lemma real_analytic_on_gradU1_slot:
  fixes \<omega> \<omega>0 \<omega>s v :: "real^2" and k :: "'n::finite"
  shows "real_analytic_on (\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) (at x)
        (slot k v)) UNIV"
proof -
  have fd_eq: "frechet_derivative
      (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) (at x)
      = (dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (1::2) 1) 1)) (gain_dip \<omega>)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)) 1)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)) 2)
             (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
         \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))" for x :: "(real^2)^'n"
  proof -
    have hd: "((\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) has_derivative
        (dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (1::2) 1) 1)) (gain_dip \<omega>)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)) 1)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)) 2)
             (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
         \<circ> DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))) (at x)"
      by (rule has_derivative_gradU_dip_component_x)
    show ?thesis
      by (rule frechet_derivative_at[OF hd, symmetric])
  qed
  have eq: "(\<lambda>x::(real^2)^'n.
      frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) (at x)
        (slot k v))
      = (\<lambda>x. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis (1::2) 1) 1))
             (gain_dip \<omega>)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)) 1)
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)) 2)
             (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
             (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot k v)))"
    by (metis (no_types, lifting) comp_def fd_eq)
  show ?thesis
    unfolding eq by (rule real_analytic_on_dEjm_moment)
qed

lemma continuous_on_d3_s1_perp_slot:
  "continuous_on UNIV (\<lambda>x::(real^2)^'n::finite. d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x)"
proof (rule continuous_at_imp_continuous_on, rule ballI)
  fix x :: "(real^2)^'n"
  assume "x \<in> UNIV"
  have ana: "real_analytic_on (\<lambda>x::(real^2)^'n. d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x) UNIV"
    unfolding d3_s1_perp_slot_def by (rule real_analytic_on_gradU1_slot)
  show "continuous (at x) (\<lambda>x::(real^2)^'n. d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x)"
    by (rule real_analytic_on_imp_continuous[OF ana UNIV_I])
qed

lemma closed_gradU1_component_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "closed {x::(real^2)^'n::finite.
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1 = 0}"
proof -
  have cont: "continuous_on UNIV
      (\<lambda>x::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1)"
  proof (rule has_derivative_continuous_on)
    fix x :: "(real^2)^'n"
    show "((\<lambda>x::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1)
        has_derivative
        frechet_derivative
          (\<lambda>x::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) (at x))
        (at x within UNIV)"
      by (rule has_derivative_at_withinI[OF has_derivative_gradU_dip_component1_x_frechet])
  qed
  show ?thesis
    by (rule closed_Collect_eq[OF cont continuous_on_const])
qed

theorem fixed_omega_slicable_branch_chart_core_data1:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_slicable_branch1 V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define k_of :: "nat \<Rightarrow> 'n" where
    "k_of n = from_nat (fst (prod_decode n))" for n
  define m_of :: "nat \<Rightarrow> nat" where
    "m_of n = snd (prod_decode n)" for n
  define f1 where "f1 = (\<lambda>y::(real^2)^'n. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1)"
  define Lf where "Lf = (\<lambda>x::(real^2)^'n. frechet_derivative f1 (at x))"
  define r where "r = (\<lambda>n (x::(real^2)^'n). slot (k_of n) (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"
  define C where "C = (\<lambda>n. {x::(real^2)^'n. f1 x = 0}
      \<inter> {x. inverse (real (Suc (m_of n))) \<le> \<bar>d3_s1_perp_slot \<omega>0 \<omega>s \<omega> (k_of n) x\<bar>})"

  have cutd: "(f1 has_derivative Lf x) (at x)" for x :: "(real^2)^'n"
    unfolding f1_def Lf_def by (rule has_derivative_gradU_dip_component1_x_frechet)

  have closedC: "closed (C n)" for n
  proof -
    have c0: "closed {x::(real^2)^'n. f1 x = 0}"
      unfolding f1_def by (rule closed_gradU1_component_zero)
    have ct: "closed {x::(real^2)^'n.
        inverse (real (Suc (m_of n))) \<le> \<bar>d3_s1_perp_slot \<omega>0 \<omega>s \<omega> (k_of n) x\<bar>}"
      by (rule closed_abs_ge_threshold[OF continuous_on_d3_s1_perp_slot])
    show ?thesis
      unfolding C_def by (intro closed_Int c0 ct)
  qed

  have cover: "D3H0_slicable_branch1 V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>n. C n)"
  proof
    fix x assume xB: "x \<in> D3H0_slicable_branch1 V \<omega>0 \<omega>s \<omega>"
    then obtain k :: 'n where sk: "d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x \<noteq> 0"
      unfolding D3H0_slicable_branch1_def by blast
    define q where "q = to_nat k"
    have q: "from_nat q = k"
      unfolding q_def by simp
    have pos: "0 < \<bar>d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x\<bar>"
      using sk by simp
    obtain m where m: "inverse (real (Suc m)) < \<bar>d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x\<bar>"
      using reals_Archimedean[OF pos] by blast
    define n where "n = prod_encode (q, m)"
    have kd: "k_of n = k"
      unfolding k_of_def n_def using q by simp
    have md: "m_of n = m"
      unfolding m_of_def n_def by simp
    have fzero: "f1 x = 0"
    proof -
      have "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>}"
        using xB unfolding D3H0_slicable_branch1_def by blast
      then obtain \<omega>' where "\<omega>' \<in> {\<omega>}"
        and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>' = 0"
        unfolding D3BadXG_H0core_def by blast
      hence "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
        by simp
      thus ?thesis
        unfolding f1_def by simp
    qed
    have "x \<in> C n"
      unfolding C_def kd md using fzero m sk by auto
    thus "x \<in> (\<Union>n. C n)"
      by blast
  qed

  have cut0: "f1 y = 0" if "y \<in> C n" for n y
    using that unfolding C_def by simp
  have rnz: "Lf x (r n x) \<noteq> 0" if "x \<in> C n" for n x
  proof -
    have ge: "inverse (real (Suc (m_of n))) \<le> \<bar>d3_s1_perp_slot \<omega>0 \<omega>s \<omega> (k_of n) x\<bar>"
      using that unfolding C_def by simp
    have pos: "0 < inverse (real (Suc (m_of n)))"
      by simp
    have "d3_s1_perp_slot \<omega>0 \<omega>s \<omega> (k_of n) x \<noteq> 0"
      using ge pos by fastforce
    thus ?thesis
      unfolding d3_s1_perp_slot_def f1_def Lf_def r_def by simp
  qed

  show ?thesis
    by (rule chart_core_data_of_functional_cuts[OF cover closedC cut0 cutd rnz])
qed

definition D3H0_residual_Bzero_branch1 ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_residual_Bzero_branch1 V \<omega>0 \<omega>s \<omega> =
     {x \<in> D3H0_all_s1_zero_residual V \<omega>0 \<omega>s \<omega>. \<exists>k. B_dip k x \<omega> \<omega>0 \<omega>s = 0}"

definition D3H0_residual_Bnonzero_residual1 ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega> =
     {x \<in> D3H0_all_s1_zero_residual V \<omega>0 \<omega>s \<omega>. \<forall>k. B_dip k x \<omega> \<omega>0 \<omega>s \<noteq> 0}"

lemma fixed_omega_all_s1_residual_Bzero_decomp:
  "D3H0_all_s1_zero_residual V \<omega>0 \<omega>s \<omega>
   = D3H0_residual_Bzero_branch1 V \<omega>0 \<omega>s \<omega>
     \<union> D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega>"
  unfolding D3H0_residual_Bzero_branch1_def D3H0_residual_Bnonzero_residual1_def
  by blast

theorem fixed_omega_residual_Bzero_branch_chart_core_data1:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_residual_Bzero_branch1 V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define k_of :: "nat \<Rightarrow> 'n" where
    "k_of n = from_nat n" for n
  define C where "C = (\<lambda>n. {x::(real^2)^'n. B_dip (k_of n) x \<omega> \<omega>0 \<omega>s = 0})"
  define f where "f = (\<lambda>n (x::(real^2)^'n). B_dip (k_of n) x \<omega> \<omega>0 \<omega>s)"
  define L where "L = (\<lambda>n (x::(real^2)^'n).
      frechet_derivative (\<lambda>y::(real^2)^'n. B_dip (k_of n) y \<omega> \<omega>0 \<omega>s) (at x))"
  define r where "r = (\<lambda>n (x::(real^2)^'n). slot (k_of n) (cvec_dip \<omega>0 \<omega>s \<omega>))"

  have closedC: "closed (C n)" for n
    unfolding C_def by (rule closed_B_dip_zero)

  have cover: "D3H0_residual_Bzero_branch1 V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>n. C n)"
  proof
    fix x assume xB: "x \<in> D3H0_residual_Bzero_branch1 V \<omega>0 \<omega>s \<omega>"
    then obtain k :: 'n where bk: "B_dip k x \<omega> \<omega>0 \<omega>s = 0"
      unfolding D3H0_residual_Bzero_branch1_def by blast
    define n where "n = to_nat k"
    have "k_of n = k"
      unfolding k_of_def n_def by simp
    hence "x \<in> C n"
      unfolding C_def using bk by simp
    thus "x \<in> (\<Union>n. C n)"
      by blast
  qed

  have cut0: "f n y = 0" if "y \<in> C n" for n y
    using that unfolding C_def f_def by simp
  have cutd: "(f n has_derivative L n x) (at x)" for n x
    unfolding f_def L_def by (rule has_derivative_B_dip_x_frechet)
  have rnz: "L n x (r n x) \<noteq> 0" if "x \<in> C n" for n x
  proof -
    have bz: "B_dip (k_of n) x \<omega> \<omega>0 \<omega>s = 0"
      using that unfolding C_def by simp
    show ?thesis
      unfolding L_def r_def
      by (rule B_dip_uslot_transversal[OF cnz bz])
  qed

  show ?thesis
    by (rule chart_core_data_of_functional_cuts[OF cover closedC cut0 cutd rnz])
qed

definition D3H0_slicable_or_Bzero_branch1 ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_slicable_or_Bzero_branch1 V \<omega>0 \<omega>s \<omega> =
     D3H0_slicable_branch1 V \<omega>0 \<omega>s \<omega>
     \<union> D3H0_residual_Bzero_branch1 V \<omega>0 \<omega>s \<omega>"

lemma fixed_omega_H0core_slicable_or_Bzero_decomp1:
  "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n::finite) set)
   = D3H0_slicable_or_Bzero_branch1 V \<omega>0 \<omega>s \<omega>
     \<union> D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega>"
  unfolding D3H0_slicable_or_Bzero_branch1_def
  using fixed_omega_H0core_slicable_residual_decomp1[of V \<omega>0 \<omega>s \<omega>]
    fixed_omega_all_s1_residual_Bzero_decomp[of V \<omega>0 \<omega>s \<omega>]
  by blast

theorem fixed_omega_slicable_or_Bzero_branch_chart_core_data1:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_slicable_or_Bzero_branch1 V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  have slicible: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_slicable_branch1 V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by (rule fixed_omega_slicable_branch_chart_core_data1)
  have bzero: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_residual_Bzero_branch1 V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by (rule fixed_omega_residual_Bzero_branch_chart_core_data1[OF cnz])
  show ?thesis
    unfolding D3H0_slicable_or_Bzero_branch1_def
    by (rule chart_core_data_union[OF slicible bzero])
qed

theorem fixed_omega_H0core_chart_core_from_Bnonzero_residual1:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and residual: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
proof -
  have resolved: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_slicable_or_Bzero_branch1 V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by (rule fixed_omega_slicable_or_Bzero_branch_chart_core_data1[OF cnz])
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cov: "D3H0_slicable_or_Bzero_branch1 V \<omega>0 \<omega>s \<omega>
          \<union> D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega>
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and nsurj: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and cls: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using chart_core_data_union[OF resolved residual] by blast
  have cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<omega>} :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
    using cov fixed_omega_H0core_slicable_or_Bzero_decomp1[of V \<omega>0 \<omega>s \<omega>] by blast
  show ?thesis
    unfolding d3_detHess_arc_chart_core_def
    by (intro exI[of _ charts] exI[of _ Crit] exI[of _ D] conjI cover der nsurj cls)
qed

definition D3H0_Bnonzero_phase_aligned_residual1 ::
  "((real^2)^'n::finite) set \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> ((real^2)^'n) set" where
  "D3H0_Bnonzero_phase_aligned_residual1 V \<omega>0 \<omega>s \<omega> =
     {x \<in> D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega>.
        \<forall>k. Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
             * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0}"

lemma fixed_omega_Bnonzero_residual_phase_alignment_if_factor_nonzero1:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
    and x :: "(real^2)^'n"
  assumes facnz: "d3_s1_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and xres: "x \<in> D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega>"
  shows "x \<in> D3H0_Bnonzero_phase_aligned_residual1 V \<omega>0 \<omega>s \<omega>"
proof -
  have s0: "d3_s1_perp_slot \<omega>0 \<omega>s \<omega> k x = 0" for k :: 'n
    using xres unfolding D3H0_residual_Bnonzero_residual1_def D3H0_all_s1_zero_residual_def
    by blast
  have aligned: "\<forall>k. Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
         * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0"
  proof
    fix k :: 'n
    have "d3_s1_global_factor \<omega>0 \<omega>s \<omega>
         * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
             * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0"
      using s0[of k] unfolding d3_s1_perp_slot_value .
    thus "Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
         * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0"
      using facnz by simp
  qed
  thus ?thesis
    using xres unfolding D3H0_Bnonzero_phase_aligned_residual1_def by blast
qed

theorem fixed_omega_H0core_chart_core_from_phase_aligned_residual1:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and facnz: "d3_s1_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and phase_data: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_Bnonzero_phase_aligned_residual1 V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
proof -
  obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where cov: "D3H0_Bnonzero_phase_aligned_residual1 V \<omega>0 \<omega>s \<omega>
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))"
      and der: "\<forall>i x. x \<in> Crit i \<longrightarrow>
        ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)"
      and nsurj: "\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))"
      and cls: "\<forall>i. closed ((fst \<circ> charts i) ` (Crit i))"
    using phase_data by blast
  have residual_data:
    "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
        (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
        (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega> \<subseteq>
         (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
       (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  proof (intro exI[of _ charts] exI[of _ Crit] exI[of _ D] conjI der nsurj cls)
    show "D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega>
        \<subseteq> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
    proof
      fix x assume xres: "x \<in> D3H0_residual_Bnonzero_residual1 V \<omega>0 \<omega>s \<omega>"
      have "x \<in> D3H0_Bnonzero_phase_aligned_residual1 V \<omega>0 \<omega>s \<omega>"
        by (rule fixed_omega_Bnonzero_residual_phase_alignment_if_factor_nonzero1[OF facnz xres])
      thus "x \<in> (\<Union>i. (fst \<circ> charts i) ` Crit i)"
        using cov by blast
    qed
  qed
  show ?thesis
    by (rule fixed_omega_H0core_chart_core_from_Bnonzero_residual1[OF cnz residual_data])
qed

theorem fixed_omega_phase_aligned_residual_chart_core_data1:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         D3H0_Bnonzero_phase_aligned_residual1 V \<omega>0 \<omega>s \<omega> \<subseteq>
           (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
         (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
         (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define k_of :: "nat \<Rightarrow> 'n" where
    "k_of n = from_nat (fst (prod_decode n))" for n
  define m_of :: "nat \<Rightarrow> nat" where
    "m_of n = snd (prod_decode n)" for n
  define f where "f = (\<lambda>n (x::(real^2)^'n).
      Im (cnj (A_moment x c) * phase c x (k_of n)))"
  define L where "L = (\<lambda>n (x::(real^2)^'n) (h::(real^2)^'n).
      Im (cnj (A_moment x c) * d_phase c x h (k_of n)
        + cnj (d_A_moment_x x c h) * phase c x (k_of n)))"
  define r where "r = (\<lambda>n (x::(real^2)^'n). slot (k_of n) c)"
  define C where "C = (\<lambda>n. {x::(real^2)^'n.
        Im (cnj (A_moment x c) * phase c x (k_of n)) = 0}
      \<inter> {x. inverse (real (Suc (m_of n)))
             \<le> \<bar>1 - Re (cnj (A_moment x c) * phase c x (k_of n))\<bar>})"

  have cutd: "(f n has_derivative L n x) (at x)" for n x
    unfolding f_def L_def by (rule has_derivative_phase_align_x)

  have closedC: "closed (C n)" for n
  proof -
    have c0: "closed {x::(real^2)^'n.
        Im (cnj (A_moment x c) * phase c x (k_of n)) = 0}"
      by (rule closed_phase_align_zero)
    have ct: "closed {x::(real^2)^'n.
        inverse (real (Suc (m_of n)))
          \<le> \<bar>1 - Re (cnj (A_moment x c) * phase c x (k_of n))\<bar>}"
      by (rule closed_abs_ge_threshold[OF continuous_on_phase_align_defect_x])
    show ?thesis
      unfolding C_def by (intro closed_Int c0 ct)
  qed

  have cut0: "f n y = 0" if "y \<in> C n" for n y
    using that unfolding C_def f_def by simp

  have cnz': "c \<bullet> c \<noteq> 0"
    using cnz unfolding c_def by simp

  have rnz: "L n x (r n x) \<noteq> 0" if "x \<in> C n" for n x
  proof -
    have ge: "inverse (real (Suc (m_of n)))
        \<le> \<bar>1 - Re (cnj (A_moment x c) * phase c x (k_of n))\<bar>"
      using that unfolding C_def by simp
    have "1 - Re (cnj (A_moment x c) * phase c x (k_of n)) \<noteq> 0"
      using ge by fastforce
    moreover have "L n x (r n x)
        = (c \<bullet> c) * (1 - Re (cnj (A_moment x c) * phase c x (k_of n)))"
      unfolding L_def r_def by (rule phase_align_slot_self_value)
    ultimately show ?thesis
      using cnz' by simp
  qed

  have cover: "D3H0_Bnonzero_phase_aligned_residual1 V \<omega>0 \<omega>s \<omega> \<subseteq> (\<Union>n. C n)"
  proof
    fix x assume xR: "x \<in> D3H0_Bnonzero_phase_aligned_residual1 V \<omega>0 \<omega>s \<omega>"
    have aligned: "Im (cnj (A_moment x c) * phase c x k) = 0" for k :: 'n
    proof -
      have "Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
          * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x k) = 0"
        using xR unfolding D3H0_Bnonzero_phase_aligned_residual1_def by blast
      thus ?thesis
        unfolding c_def by simp
    qed
    obtain k :: 'n where defect: "1 - Re (cnj (A_moment x c) * phase c x k) \<noteq> 0"
      using phase_aligned_defect_witness[OF card2 aligned] by blast
    have pos: "0 < \<bar>1 - Re (cnj (A_moment x c) * phase c x k)\<bar>"
      using defect by simp
    obtain m where m: "inverse (real (Suc m))
        < \<bar>1 - Re (cnj (A_moment x c) * phase c x k)\<bar>"
      using reals_Archimedean[OF pos] by blast
    define n where "n = prod_encode (to_nat k, m)"
    have kd: "k_of n = k"
      unfolding k_of_def n_def by simp
    have md: "m_of n = m"
      unfolding m_of_def n_def by simp
    have "x \<in> C n"
      unfolding C_def kd md using aligned[of k] m by auto
    thus "x \<in> (\<Union>n. C n)"
      by blast
  qed

  show ?thesis
    by (rule chart_core_data_of_functional_cuts[OF cover closedC cut0 cutd rnz])
qed

theorem fixed_omega_H0core_chart_core_of_angle_conditions1:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and facnz: "d3_s1_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
  by (rule fixed_omega_H0core_chart_core_from_phase_aligned_residual1[OF cnz facnz
        fixed_omega_phase_aligned_residual_chart_core_data1[OF cnz card2]])

subsection \<open>The generic fixed-\<open>\<omega>\<close> chart core: dropping the ad-hoc factor hypothesis\<close>

text \<open>Combining both mirror branches with @{thm d3_s1_or_s2_global_factor_nonzero}:
  the fixed-\<open>\<omega>\<close> chart core holds under PURELY generic non-degeneracy
  (\<open>cvec \<noteq> 0\<close>, \<open>det (matrix Dcvec) \<noteq> 0\<close>, \<open>gain_dip \<omega> \<noteq> 0\<close>), with no reference
  to either \<open>d3_s1_global_factor\<close> or \<open>d3_s2_global_factor\<close> individually.  This
  is the frontier-push beyond @{thm fixed_omega_H0core_chart_core_robust4_witness}:
  it replaces a pointwise-checked witness fact with a condition that plausibly
  holds throughout the whole Robust4 design box, not just at one design point.\<close>

theorem fixed_omega_H0core_chart_core_of_generic_conditions:
  fixes V :: "((real^2)^'n::finite) set"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<omega>}"
proof (cases "d3_s2_global_factor \<omega>0 \<omega>s \<omega> = 0")
  case True
  have facnz1: "d3_s1_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0"
    using d3_s1_or_s2_global_factor_nonzero[OF cnz detnz gnz] True by blast
  show ?thesis
    by (rule fixed_omega_H0core_chart_core_of_angle_conditions1[OF cnz facnz1 card2])
next
  case False
  hence facnz2: "d3_s2_global_factor \<omega>0 \<omega>s \<omega> \<noteq> 0" by simp
  show ?thesis
    by (rule fixed_omega_H0core_chart_core_of_angle_conditions[OF cnz facnz2 card2])
qed

subsection \<open>At the Robust4 design point, EVERY angle in the box is regular\<close>

text \<open>Sharper than the generic-conditions theorem: at the literal Robust4
  design values, the two factors vanishing SIMULTANEOUSLY (given the box's
  own \<open>0 < \<omega>\<^sub>1 < \<pi>\<close> constraint) forces \<open>\<omega> = \<omega>0\<close> itself, i.e. forces
  \<open>cvec_dip = 0\<close> --- which already makes the whole bad fibre empty by
  definition, needing no chart at all.  So there is NO exceptional angle:
  every \<open>\<omega>\<close> with \<open>0 < \<omega>\<^sub>1 < \<pi>\<close> (in particular every \<open>\<omega>\<close> in the design box,
  by the pre-existing \<open>pf\<close> fact) is individually regular.\<close>

lemma d3_s1_s2_both_zero_forces_cvec_zero_robust4:
  fixes \<omega> :: "real^2"
  assumes w1lo: "0 < vec_nth \<omega> 1" and w1hi: "vec_nth \<omega> 1 < pi"
    and f1z: "d3_s1_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
    and f2z: "d3_s2_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
  shows "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
proof -
  have sinw1: "0 < sin (vec_nth \<omega> 1)"
    by (rule sin_gt_zero[OF w1lo w1hi])
  have gnz: "gain_dip \<omega> \<noteq> 0"
    by (rule gain_dip_nonzero_of_sin) (use sinw1 in force)
  have trig_collapse: "cos (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
      + sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
      = sin (vec_nth \<omega> 2)"
  proof -
    have "cos (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
        + sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2))
        = ((cos (vec_nth \<omega> 1)) * (cos (vec_nth \<omega> 1))
            + (sin (vec_nth \<omega> 1)) * (sin (vec_nth \<omega> 1))) * sin (vec_nth \<omega> 2)"
      by (simp only: mult.assoc distrib_right)
    also have "\<dots> = sin (vec_nth \<omega> 2)"
      by (simp only: sin_cos_squared_add3)
    finally show ?thesis .
  qed
  have D1eq: "Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> (axis 1 1)
      \<bullet> perp2 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
      = sin (vec_nth \<omega> 2) * (1 - cos (vec_nth \<omega> 1))"
    by (simp add: Dcvec_dip_def cvec_dip_def perp2_def kx_def ky_def kz_def
        axis_def inner_vec_def sum_2 vector_2 sin_pi_half cos_pi_half algebra_simps
        trig_collapse)
  have trig_collapse2: "sin (vec_nth \<omega> 1)
      * (sin (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 2) * cos (vec_nth \<omega> 2)))
    + sin (vec_nth \<omega> 1)
      * (sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 2) * sin (vec_nth \<omega> 2)))
    = sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1)"
  proof -
    have "sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 2) * cos (vec_nth \<omega> 2)))
        + sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 2) * sin (vec_nth \<omega> 2)))
        = (sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1))
            * (cos (vec_nth \<omega> 2) * cos (vec_nth \<omega> 2) + sin (vec_nth \<omega> 2) * sin (vec_nth \<omega> 2))"
      by (simp only: mult.assoc distrib_left)
    also have "\<dots> = sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 1)"
      by (simp only: sin_cos_squared_add3)
    finally show ?thesis .
  qed
  have D2eq: "Dcvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> (axis 2 1)
      \<bullet> perp2 (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>)
      = sin (vec_nth \<omega> 1)
          * (sin (vec_nth \<omega> 1) + cos (vec_nth \<omega> 2) * (cos (vec_nth \<omega> 1) - 1))"
    using trig_collapse2
    by (simp add: Dcvec_dip_def cvec_dip_def perp2_def kx_def ky_def kz_def
        axis_def inner_vec_def sum_2 vector_2 sin_pi_half cos_pi_half algebra_simps
        trig_collapse)
  have f1z': "sin (vec_nth \<omega> 2) * (1 - cos (vec_nth \<omega> 1)) = 0"
    using f1z gnz D1eq unfolding d3_s1_global_factor_def by (simp add: mult_eq_0_iff)
  have f2z': "sin (vec_nth \<omega> 1) + cos (vec_nth \<omega> 2) * (cos (vec_nth \<omega> 1) - 1) = 0"
    using f2z gnz D2eq sinw1 unfolding d3_s2_global_factor_def by (simp add: mult_eq_0_iff)
  have c_lt1: "cos (vec_nth \<omega> 1) < 1"
  proof -
    have h0: "0 < vec_nth \<omega> 1 / 2" using w1lo by simp
    have h2: "vec_nth \<omega> 1 / 2 < 2" using w1hi pi_less_4 by linarith
    have "cos (2 * (vec_nth \<omega> 1 / 2)) < 1"
      by (rule cos_double_less_one[OF h0 h2])
    thus ?thesis by simp
  qed
  have sinw2z: "sin (vec_nth \<omega> 2) = 0"
    using f1z' c_lt1 by auto
  have cosw2pm: "\<bar>cos (vec_nth \<omega> 2)\<bar> = 1"
    by (rule sin_zero_abs_cos_one[OF sinw2z])
  have c1eq: "vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 1
      = sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2) + cos (vec_nth \<omega> 1) - 1"
    by (simp add: cvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half algebra_simps)
  have c2eq: "vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 2
      = sin (vec_nth \<omega> 1) * sin (vec_nth \<omega> 2)"
    by (simp add: cvec_dip_def kx_def ky_def kz_def axis_def vector_2
        sin_pi_half cos_pi_half algebra_simps)
  show ?thesis
  proof (cases "cos (vec_nth \<omega> 2) = 1")
    case True
    have sumeq1: "sin (vec_nth \<omega> 1) + cos (vec_nth \<omega> 1) = 1"
      using f2z' True by simp
    have sq: "sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 1) = 0"
    proof -
      have "1 = (sin (vec_nth \<omega> 1) + cos (vec_nth \<omega> 1))\<^sup>2"
        using sumeq1 by simp
      also have "\<dots> = (sin (vec_nth \<omega> 1))\<^sup>2 + (cos (vec_nth \<omega> 1))\<^sup>2
          + 2 * (sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 1))"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = 1 + 2 * (sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 1))"
        using sin_cos_squared_add[of "vec_nth \<omega> 1"] by simp
      finally show ?thesis by simp
    qed
    have cosz: "cos (vec_nth \<omega> 1) = 0"
      using sq sinw1 by simp
    have sinw1eq1: "sin (vec_nth \<omega> 1) = 1"
      using sumeq1 cosz by simp
    have "vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 1 = 0"
      unfolding c1eq using True cosz
      by (simp add: sinw1eq1)
    moreover have "vec_nth (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega>) 2 = 0"
      unfolding c2eq using sinw2z by simp
    ultimately show ?thesis
      by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
  next
    case False
    hence cosw2m1: "cos (vec_nth \<omega> 2) = - 1"
      using cosw2pm by (simp add: abs_if split: if_splits)
    have eqn: "sin (vec_nth \<omega> 1) - cos (vec_nth \<omega> 1) + 1 = 0"
      using f2z' cosw2m1 by simp
    have contra: "2 * sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) + 1) = 0"
    proof -
      have s1: "sin (vec_nth \<omega> 1) + 1 = cos (vec_nth \<omega> 1)"
        using eqn by simp
      have "(sin (vec_nth \<omega> 1) + 1)\<^sup>2 = (cos (vec_nth \<omega> 1))\<^sup>2"
        using s1 by simp
      also have "(cos (vec_nth \<omega> 1))\<^sup>2 = 1 - (sin (vec_nth \<omega> 1))\<^sup>2"
        using sin_cos_squared_add[of "vec_nth \<omega> 1"]
        using cos_squared_eq by blast
      finally have "(sin (vec_nth \<omega> 1))\<^sup>2 + 2 * sin (vec_nth \<omega> 1) + 1
          = 1 - (sin (vec_nth \<omega> 1))\<^sup>2"
        using c_lt1 s1 sinw1 by argo
      hence "2 * (sin (vec_nth \<omega> 1))\<^sup>2 + 2 * sin (vec_nth \<omega> 1) = 0"
        by argo
      thus ?thesis
        using c_lt1 s1 sinw1 by argo
    qed
    have "sin (vec_nth \<omega> 1) + 1 \<noteq> 0" using sinw1 by simp
    hence False using contra sinw1 by auto
    thus ?thesis ..
  qed
qed

theorem fixed_omega_H0core_chart_core_robust4_all_angles:
  fixes V :: "((real^2)^'n::finite) set" and \<omega> :: "real^2"
  assumes w1lo: "0 < vec_nth \<omega> 1" and w1hi: "vec_nth \<omega> 1 < pi"
    and card2: "2 \<le> CARD('n)"
  shows "d3_detHess_arc_chart_core V (vector [pi / 2, 0]) (vector [0, 0]) {\<omega>}"
proof (cases "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0")
  case True
  have empty: "(V \<inter> D3BadXG_H0core (vector [pi / 2, 0]) (vector [0, 0]) {\<omega>}
      :: ((real^2)^'n) set) = {}"
    using True unfolding D3BadXG_H0core_def by auto
  show ?thesis
    unfolding d3_detHess_arc_chart_core_def empty
    by (rule chart_core_data_of_functional_cuts
          [of "{} :: ((real^2)^'n) set" "\<lambda>i::nat. ({} :: ((real^2)^'n) set)"
              "\<lambda>(i::nat) (x::(real^2)^'n). (0::real)"
              "\<lambda>(i::nat) (x::(real^2)^'n) (v::(real^2)^'n). (0::real)"
              "\<lambda>(i::nat) (x::(real^2)^'n). x"];
        simp)
next
  case False
  hence cnz: "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0" .
  show ?thesis
  proof (cases "d3_s2_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0")
    case True
    have f1nz: "d3_s1_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega> \<noteq> 0"
    proof
      assume f1z: "d3_s1_global_factor (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
      have "cvec_dip (vector [pi / 2, 0]) (vector [0, 0]) \<omega> = 0"
        by (rule d3_s1_s2_both_zero_forces_cvec_zero_robust4[OF w1lo w1hi f1z True])
      thus False using cnz by simp
    qed
    show ?thesis
      by (rule fixed_omega_H0core_chart_core_of_angle_conditions1[OF cnz f1nz card2])
  next
    case False
    show ?thesis
      by (rule fixed_omega_H0core_chart_core_of_angle_conditions[OF cnz False card2])
  qed
qed

section \<open>The corank-k functional cut engine: joint vector-valued cuts\<close>

text \<open>Generalizes @{thm chart_core_data_of_functional_cuts} from a single
  scalar cut (corank 1) to a VECTOR-valued cut \<open>f : 'a \<Rightarrow> 'b\<close> (corank
  \<open>DIM('b)\<close>), given a pointwise bounded-linear RIGHT INVERSE \<open>W\<close> of the
  cut's derivative \<open>L\<close> (i.e. \<open>L (W t) = t\<close> for all \<open>t\<close>).  The same
  \<psi>-transform trick applies: \<open>\<psi>(w) = w - W (f w)\<close> equals the identity on
  the cut (where \<open>f \<equiv> 0\<close>, using \<open>W\<close> linear so \<open>W 0 = 0\<close>) and has full
  derivative the projection \<open>P(v) = v - W (L v)\<close> onto \<open>ker L\<close>, which is
  proper since \<open>L\<close> maps ONTO the nontrivial space \<open>'b\<close> (\<open>DIM('b) \<ge> 1\<close> for
  any @{class euclidean_space}, via @{thm nonempty_Basis}) --- so \<open>P\<close> is
  automatically non-surjective, with NO \<epsilon>-\<delta>, no IFT.  This is exactly the
  engine \<open>Appendix/Wiring/D3_Chart_Wiring.thy\<close> calls "the next tier": the
  intended eventual target is the geodesic-branch \<open>(Phi_par, Phi2, G11)\<close>
  triple with its \<open>Jac3_*\<close> rank-3 side conditions (\<open>'b\<close> a 3-dimensional
  space there), but the engine itself is fully generic in the corank.\<close>

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
  obtain b :: 'b where bB: "b \<in> Basis" using nonempty_Basis by blast
  have bnz: "b \<noteq> 0" using norm_Basis[OF bB] by auto
  have "\<exists>v. W b = v - W (L v)" using s unfolding surj_def by blast
  then obtain v where veq: "W b = v - W (L v)" by blast
  have chain: "L (W b) = 0"
  proof -
    have "L (W b) = L (v - W (L v))" using veq by simp
    also have "\<dots> = L v - L (W (L v))" by (rule linear_diff[OF lin_L])
    also have "\<dots> = L v - L v" using right_inv by simp
    also have "\<dots> = 0" by simp
    finally show ?thesis .
  qed
  have "b = 0" using chain right_inv[of b] by simp
  thus False using bnz by simp
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

section \<open>The arc-bridge: x-space rank-2 via a perp direction and a radial direction\<close>

text \<open>\<^bold>\<open>Strategy for the still-open arc-packaging problem.\<close>  Rather than
  eliminating the arc parameter \<open>t\<close> via the OMEGA-Hessian (which is exactly
  singular on the D3 locus, and whose rank-1 range direction is genuinely
  \<open>x\<close>-dependent --- a dead end), use TWO purely \<open>x\<close>-space directions:
  \<open>v\<^sub>perp = slot k (perp2 c)\<close> (already known transversal for gradU's component
  2, via @{thm d3_s2_perp_slot_value} / the "all angles regular" ladder) and
  \<open>v\<^sub>rad = slot m c\<close> (a RADIAL direction, i.e. NOT perpendicular to \<open>c\<close>).  By
  @{thm Phi_par_perp_slot_zero}, the perp column
  \<open>(\<partial>gradU\<^sub>1/\<partial>v\<^sub>perp, \<partial>gradU\<^sub>2/\<partial>v\<^sub>perp)\<close> is ALWAYS exactly parallel to
  \<open>perp2(e_par)\<close> (zero \<open>e_par\<close>-component).  The radial column has
  \<open>e_par\<close>-component EXACTLY \<open>Phi_par\<close>'s radial derivative (since
  \<open>Phi_par = gradU \<bullet> e_par\<close>).  A vector with zero \<open>e_par\<close>-component can never
  be parallel to one with nonzero \<open>e_par\<close>-component (unless both vanish), so
  \<open>v\<^sub>perp \<noteq> 0\<close>-transversality PLUS \<open>Phi_par\<close>'s radial derivative \<open>\<noteq> 0\<close> TOGETHER
  give gradU's full \<open>2 \<times> 2\<close> \<open>x\<close>-Jacobian (restricted to \<open>v\<^sub>perp, v\<^sub>rad\<close>) full
  RANK 2 --- with NO reference to \<open>\<omega>\<close>-derivatives or the arc tangent at all.
  This is the key new fact needed: \<open>Phi_par\<close>'s radial derivative is not an
  angle-only quantity (it depends on the actual antenna configuration \<open>x\<close>),
  so --- exactly as for every other transversality quantity in this
  development (@{thm gradU2_perp_slot_zeros_nowhere_dense}) --- the best
  available fact is GENERICITY (nowhere-dense zero set), established via a
  two-bump witness plus @{thm real_analytic_nowhere_dense_zeros}.  The
  two-bump computation below reuses @{thm Phi_par_uslot_radial} and the
  \<open>two_bump_row_sum_i/j\<close> machinery already built for
  @{thm Lambda_rad_two_bump_witness}, extracting just the \<open>Phi_par\<close> part (not
  the full \<open>Hrad2\<close>/\<open>Lambda_rad_ij\<close> Wronskian) --- and, mirroring the
  component-1-or-2 disjunction trick, shows that of TWO antenna indices
  \<open>i \<noteq> j\<close>, AT LEAST ONE gives a nowhere-dense zero set, UNCONDITIONALLY (no
  extra angle-side hypothesis beyond the standing \<open>gain \<noteq> 0\<close>, \<open>cvec \<noteq> 0\<close>,
  \<open>det Dcvec \<noteq> 0\<close>, \<open>CARD('n) \<ge> 4\<close>).\<close>

theorem Phi_par_uslot_radial_nowhere_dense_disjunction:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and i j :: "'n::finite"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and ij: "i \<noteq> j"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and N4: "4 \<le> CARD('n)"
  shows "interior (closure {x::(real^2)^'n.
            frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
              (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)) = 0}) = {}
       \<or> interior (closure {x::(real^2)^'n.
            frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
              (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)) = 0}) = {}"
proof -
  define c where "c = cvec_dip \<omega>0 \<omega>s \<omega>"
  define q where "q = c \<bullet> c"
  define A where "A = deriv gdip (vec_nth \<omega> 1) * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1"
  define g0 where "g0 = gain_dip \<omega>"
  define Phi' where "Phi' = (\<lambda>u. A * (- sin u) + g0 * (- (sin u + u * cos u)))"
  define w1 where "w1 = (pi / q) *\<^sub>R c"
  define w2 where "w2 = (pi / (2 * q)) *\<^sub>R c"
  define x0 where "x0 = slot i w1 + slot j w2"
  define N where "N = real (CARD('n))"
  have qnz: "q \<noteq> 0"
    unfolding q_def c_def using cnz by (simp add: dot_square_norm)
  have t1: "c \<bullet> w1 = pi"
    unfolding w1_def by (simp add: inner_scaleR_right q_def[symmetric] qnz)
  have t2: "c \<bullet> w2 = pi / 2"
    unfolding w2_def by (simp add: inner_scaleR_right q_def[symmetric] qnz)
  have Phi'0: "Phi' 0 = 0"
    unfolding Phi'_def by simp
  have Phi'odd: "Phi' (- u) = - Phi' u" for u :: real
    unfolding Phi'_def by (simp add: algebra_simps)
  have phi_val: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot m c)
      = 2 * q * (\<Sum>p\<in>UNIV. Phi' (c \<bullet> (vec_nth x0 m - vec_nth x0 p)))" for m :: 'n
    using Phi_par_uslot_radial[OF detnz, of x0 m]
    unfolding c_def[symmetric] q_def[symmetric] Phi'_def A_def g0_def by simp
  have row_Phi_i: "(\<Sum>p\<in>UNIV. Phi' (c \<bullet> (vec_nth x0 i - vec_nth x0 p)))
      = Phi' (pi / 2) + (N - 2) * Phi' pi"
    using two_bump_row_sum_i[of i j Phi' c w1 w2, OF ij Phi'0] t1 t2
    unfolding x0_def N_def by simp
  have row_Phi_j: "(\<Sum>p\<in>UNIV. Phi' (c \<bullet> (vec_nth x0 j - vec_nth x0 p)))
      = - Phi' (pi / 2) + (N - 2) * Phi' (pi / 2)"
    using two_bump_row_sum_j[of i j Phi' c w1 w2, OF ij Phi'0] t1 t2
    unfolding x0_def N_def
    by (simp add: Phi'odd[of "pi/2", symmetric])
  have phi_i: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot i c)
      = 2 * q * (Phi' (pi / 2) + (N - 2) * Phi' pi)"
    unfolding phi_val[of i] row_Phi_i ..
  have phi_j: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot j c)
      = 2 * q * (- Phi' (pi / 2) + (N - 2) * Phi' (pi / 2))"
    unfolding phi_val[of j] row_Phi_j ..
  have PhiPi: "Phi' pi = pi * g0"
    unfolding Phi'_def by simp
  have PhiHalf: "Phi' (pi / 2) = - (A + g0)"
    unfolding Phi'_def by simp
  have N3: "N - 3 \<noteq> 0" and N2: "N - 2 \<noteq> 0"
    using N4 unfolding N_def by simp_all
  have gnz': "g0 \<noteq> 0" unfolding g0_def using gnz .
  show ?thesis
  proof (cases "A + g0 = 0")
    case True
    have phi_i_val: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot i c)
        = 2 * q * ((N - 2) * (pi * g0))"
      unfolding phi_i PhiPi PhiHalf using True by simp
    have phi_i_nz: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot i c) \<noteq> 0"
      unfolding phi_i_val using qnz N2 gnz' by simp
    have ex: "\<exists>x\<in>UNIV. frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
        (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      using phi_i_nz unfolding c_def by blast
    have "interior (closure {x \<in> UNIV.
        frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
          (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)) = 0}) = {}"
      by (rule real_analytic_nowhere_dense_zeros[OF real_analytic_on_Phi_par_uslot
            connected_UNIV ex])
    hence "interior (closure {x::(real^2)^'n.
        frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
          (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)) = 0}) = {}"
      by simp
    thus ?thesis by blast
  next
    case False
    have phi_j_val: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot j c)
        = 2 * q * ((A + g0) * (3 - N))"
      unfolding phi_j PhiHalf by (simp add: algebra_simps)
    have phi_j_nz: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x0) (slot j c) \<noteq> 0"
      unfolding phi_j_val using qnz N3 False by simp
    have ex: "\<exists>x\<in>UNIV. frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
        (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      using phi_j_nz unfolding c_def by blast
    have "interior (closure {x \<in> UNIV.
        frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
          (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)) = 0}) = {}"
      by (rule real_analytic_nowhere_dense_zeros[OF real_analytic_on_Phi_par_uslot
            connected_UNIV ex])
    hence "interior (closure {x::(real^2)^'n.
        frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x)
          (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)) = 0}) = {}"
      by simp
    thus ?thesis by blast
  qed
qed

end
