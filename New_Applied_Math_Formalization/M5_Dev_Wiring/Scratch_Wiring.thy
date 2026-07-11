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
  by (simp add: Phi2_perp_slot_value[OF perp2_orth])

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
      by (simp add: mult.assoc)
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
      by (simp add: unit)
    also have "\<dots> = of_nat (CARD('n))"
      by simp
    finally show ?thesis .
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

subsection \<open>Arc chart core from countably many fixed-\<open>\<omega>\<close> pieces\<close>

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

end
