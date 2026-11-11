theory Scratch_ArcBridge
  imports "Applied_Math_Appendix_Frontier.Nonemptiness_Robust4"
begin

section \<open>Eliminating the arc parameter: a joint \<open>(x,t)\<close> implicit-function graph\<close>

text \<open>\<^bold>\<open>Scratch staging only.\<close>  Goal: close the remaining D3 arc-bridge gap
  (\<open>d3_detHess_arc_chart_core_all\<close>) by eliminating the arc parameter \<open>t\<close> via a
  joint \<open>(x,t)\<close> implicit-function graph, NOT by reusing the regular
  (\<open>det HessU \<noteq> 0\<close>) critical-graph engine -- that engine targets the wrong
  stratum (the D3 target set requires \<open>det HessU = 0\<close>).  The construction here
  uses the standard multivariate @{thm inverse_function_theorem} on
  \<open>H(x,t) = (x, gradU_1(x,\<phi> t))\<close>, whose joint continuous derivative comes from
  @{thm gradU_dip_joint_C1} (already unconditional, no \<open>det HessU\<close> hypothesis).\<close>

definition Hgrad1 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real \<Rightarrow> real^2)
      \<Rightarrow> (((real^2)^'n::finite) \<times> real) \<Rightarrow> (((real^2)^'n) \<times> real)" where
  "Hgrad1 \<omega>0 \<omega>s \<phi> q =
     (fst q, vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q))) 1)"

lemma has_derivative_phase_pair:
  fixes x :: "(real^2)^'n::finite" and t :: real
    and \<phi> :: "real \<Rightarrow> real^2" and D\<phi> :: "real^2"
  assumes phid: "(\<phi> has_vector_derivative D\<phi>) (at t)"
  shows "((\<lambda>q::(((real^2)^'n)\<times>real). (fst q, \<phi> (snd q)))
      has_derivative (\<lambda>q. (fst q, snd q *\<^sub>R D\<phi>))) (at (x,t))"
proof -
  have phid'': "(\<phi> has_derivative (\<lambda>s. s *\<^sub>R D\<phi>)) (at (snd (x,t)))"
    using phid unfolding has_vector_derivative_def by simp
  have hd_snd: "(snd has_derivative snd) (at (x,t))"
    by (rule bounded_linear.has_derivative[OF bounded_linear_snd has_derivative_ident])
  have step1: "((\<phi> \<circ> snd) has_derivative ((\<lambda>s. s *\<^sub>R D\<phi>) \<circ> snd)) (at (x,t))"
    by (rule diff_chain_at[OF hd_snd phid''])
  have step2: "((\<lambda>q. \<phi> (snd q)) has_derivative (\<lambda>q. snd q *\<^sub>R D\<phi>)) (at (x,t))"
    using step1 by (simp add: o_def)
  have hd_fst: "(fst has_derivative fst) (at (x,t))"
    by (rule bounded_linear.has_derivative[OF bounded_linear_fst has_derivative_ident])
  from has_derivative_Pair[OF hd_fst step2]
  show ?thesis by simp
qed

lemma has_derivative_Hgrad1_at:
  fixes x :: "(real^2)^'n::finite" and t :: real
    and \<phi> :: "real \<Rightarrow> real^2" and D\<phi> :: "real^2"
    and G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
  assumes G'd: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                 has_derivative blinfun_apply (G' z)) (at z)"
    and phid: "(\<phi> has_vector_derivative D\<phi>) (at t)"
  shows "(Hgrad1 \<omega>0 \<omega>s \<phi> has_derivative
      (\<lambda>q. (fst q, vec_nth (blinfun_apply (G' (x, \<phi> t)) (fst q, snd q *\<^sub>R D\<phi>)) 1)))
      (at (x,t))"
proof -
  have phase: "((\<lambda>q::(((real^2)^'n)\<times>real). (fst q, \<phi> (snd q)))
      has_derivative (\<lambda>q. (fst q, snd q *\<^sub>R D\<phi>))) (at (x,t))"
    by (rule has_derivative_phase_pair[OF phid])
  have Gat: "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                 has_derivative blinfun_apply (G' (x, \<phi> t)))
             (at (x, \<phi> t))"
    using G'd by blast
  have comp: "(((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                \<circ> (\<lambda>q. (fst q, \<phi> (snd q))))
      has_derivative
       (blinfun_apply (G' (x, \<phi> t)) \<circ> (\<lambda>q. (fst q, snd q *\<^sub>R D\<phi>))))
      (at (x,t))"
    by (rule diff_chain_at[OF phase, of "\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)"
          "blinfun_apply (G' (x, \<phi> t))"])
       (simp add: Gat)
  have eq1: "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                \<circ> (\<lambda>q. (fst q, \<phi> (snd q))))
      = (\<lambda>q. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q)))"
    by (simp add: o_def)
  have main: "((\<lambda>q. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q)))
      has_derivative
       (\<lambda>q. blinfun_apply (G' (x, \<phi> t)) (fst q, snd q *\<^sub>R D\<phi>)))
      (at (x,t))"
    using comp unfolding eq1 o_def .
  have vecnth1: "((\<lambda>q. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q))) 1)
      has_derivative
       (\<lambda>q. vec_nth (blinfun_apply (G' (x, \<phi> t)) (fst q, snd q *\<^sub>R D\<phi>)) 1))
      (at (x,t))"
    using bounded_linear.has_derivative[OF bounded_linear_vec_nth main] .
  have hd_fst: "(fst has_derivative fst) (at (x,t))"
    by (rule bounded_linear.has_derivative[OF bounded_linear_fst has_derivative_ident])
  have "(Hgrad1 \<omega>0 \<omega>s \<phi> has_derivative
      (\<lambda>q. (fst q, vec_nth (blinfun_apply (G' (x, \<phi> t)) (fst q, snd q *\<^sub>R D\<phi>)) 1)))
      (at (x,t))"
    unfolding Hgrad1_def
    by (rule has_derivative_Pair[OF hd_fst vecnth1])
  thus ?thesis .
qed

section \<open>The local implicit-function graph: eliminating the arc parameter\<close>

lemma gradU1_arc_local_graph:
  fixes x0 :: "(real^2)^'n::finite" and t0 :: real
    and \<phi> :: "real \<Rightarrow> real^2" and D\<phi> :: "real \<Rightarrow> real^2"
    and \<omega>0 \<omega>s :: "real^2" and a b :: real
  assumes phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
      and phic: "continuous_on {a<..<b} D\<phi>"
      and t0ab: "a < t0" "t0 < b"
      and crit1: "vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0)) 1 = 0"
      and trans: "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi> t0) 1 \<noteq> 0"
  obtains B \<epsilon> \<tau> where
    "open B" "x0 \<in> B" "0 < \<epsilon>" "{t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}"
    "\<tau> x0 = t0"
    "\<And>x. x \<in> B \<Longrightarrow> \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
    "\<And>x. x \<in> B \<Longrightarrow> vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
    "\<And>x. x \<in> B \<Longrightarrow> \<tau> differentiable (at x)"
    "continuous_on B \<tau>"
    "\<And>x t. x \<in> B \<Longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<Longrightarrow>
        vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<Longrightarrow> t = \<tau> x"
proof -
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))" where
    G'd: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                 has_derivative blinfun_apply (G' z)) (at z)"
    and G'c: "continuous_on UNIV G'"
    using gradU_dip_joint_C1 by blast

  define U :: "(((real^2)^'n) \<times> real) set" where "U = (UNIV::((real^2)^'n) set) \<times> {a<..<b}"
  have openU: "open U" unfolding U_def by (intro open_Times open_UNIV) simp

  define Hmap :: "(((real^2)^'n) \<times> real) \<Rightarrow> ((real^2)^'n) \<times> real \<Rightarrow> (((real^2)^'n) \<times> real)"
    where "Hmap z = (\<lambda>q. (fst q,
        vec_nth (blinfun_apply (G' (fst z, \<phi> (snd z))) (fst q, snd q *\<^sub>R D\<phi> (snd z))) 1))" for z

  define Hd :: "(((real^2)^'n) \<times> real) \<Rightarrow> ((((real^2)^'n) \<times> real) \<Rightarrow>\<^sub>L (((real^2)^'n) \<times> real))"
    where "Hd = (\<lambda>z. Blinfun (Hmap z))"

  have Hderiv: "(Hgrad1 \<omega>0 \<omega>s \<phi> has_derivative blinfun_apply (Hd z)) (at z)" if zU: "z \<in> U" for z
  proof -
    obtain x t where z: "z = (x,t)" by fastforce
    have tab: "a < t" "t < b" using zU z unfolding U_def by auto
    have main: "(Hgrad1 \<omega>0 \<omega>s \<phi> has_derivative Hmap z) (at (x,t))"
      unfolding Hmap_def z using has_derivative_Hgrad1_at[OF G'd phid[OF tab]] z by simp
    have blmap: "bounded_linear (Hmap z)"
      using has_derivative_bounded_linear[OF main[unfolded z]] unfolding z .
    have "blinfun_apply (Hd z) = Hmap z"
      unfolding Hd_def using bounded_linear_Blinfun_apply[OF blmap] by simp
    thus ?thesis using main unfolding z by simp
  qed

  have phicont: "continuous_on {a<..<b} \<phi>"
  proof (rule continuous_at_imp_continuous_on, intro ballI)
    fix t assume "t \<in> {a<..<b}"
    thus "continuous (at t) \<phi>"
      using phid[of t] has_vector_derivative_continuous by auto
  qed

  have Hdcont: "continuous_on U Hd"
  proof (rule continuous_on_blinfun_componentwise)
    fix w :: "((real^2)^'n) \<times> real" assume "w \<in> Basis"
    have eqb: "\<And>z. z \<in> U \<Longrightarrow> blinfun_apply (Hd z) w = Hmap z w"
    proof -
      fix z assume zU: "z \<in> U"
      obtain x t where z: "z = (x,t)" by fastforce
      have tab: "a < t" "t < b" using zU z unfolding U_def by auto
      have alt: "(Hgrad1 \<omega>0 \<omega>s \<phi> has_derivative Hmap z) (at z)"
        unfolding Hmap_def z using has_derivative_Hgrad1_at[OF G'd phid[OF tab]] z by simp
      show "blinfun_apply (Hd z) w = Hmap z w"
        using has_derivative_unique[OF Hderiv[OF zU] alt] by simp
    qed
    have phatU: "continuous_on U (\<lambda>z. (fst z, \<phi> (snd z)))"
      by (intro continuous_on_Pair continuous_on_fst
                continuous_on_compose2[OF phicont continuous_on_snd])
         (auto simp: U_def)
    have DphiU: "continuous_on U (\<lambda>z. D\<phi> (snd z))"
      by (rule continuous_on_compose2[OF phic continuous_on_snd]) (auto simp: U_def)
    have "continuous_on U (\<lambda>z. vec_nth
              (blinfun_apply (G' (fst z, \<phi> (snd z))) (fst w, snd w *\<^sub>R D\<phi> (snd z))) 1)"
      by (intro continuous_intros continuous_on_compose2[OF G'c phatU]
                continuous_on_compose2[OF DphiU] subset_UNIV)
         auto
    hence "continuous_on U (\<lambda>z. Hmap z w)"
      unfolding Hmap_def
      by (intro continuous_on_Pair continuous_on_const) simp
    thus "continuous_on U (\<lambda>z. blinfun_apply (Hd z) w)"
      using eqb by (simp cong: continuous_on_cong)
  qed

  \<comment> \<open>The \<open>\<omega>\<close>-only slice of the joint derivative \<open>G'\<close> agrees with \<open>HessU\<close>: compose the
      constant-\<open>x0\<close> embedding \<open>\<iota>(\<omega>)=(x0,\<omega>)\<close> (derivative \<open>v \<mapsto> (0,v)\<close>) with \<open>G'd\<close> via the
      chain rule, and match against @{thm gradU_dip_has_derivative} by uniqueness of the
      Fr\'echet derivative.\<close>
  have G'_omega_part: "blinfun_apply (G' (x0, \<omega>)) (0, v)
      = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> *v v" for \<omega> v
  proof -
    have iota_deriv: "((\<lambda>\<eta>. (x0,\<eta>)) has_derivative (\<lambda>v. (0,v))) (at \<omega>)"
      by (auto intro!: derivative_eq_intros)
    have Gz: "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                 has_derivative blinfun_apply (G' (x0,\<omega>))) (at (x0,\<omega>))"
      using G'd .
    have chain: "((\<lambda>\<eta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<eta>)
        has_derivative (\<lambda>v. blinfun_apply (G' (x0,\<omega>)) (0,v))) (at \<omega>)"
      using diff_chain_at[OF iota_deriv Gz] by (simp add: o_def)
    have direct: "((\<lambda>\<eta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<eta>)
        has_derivative (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> *v v)) (at \<omega>)"
      using gradU_dip_has_derivative .
    have "(\<lambda>v. blinfun_apply (G' (x0,\<omega>)) (0,v))
        = (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> *v v)"
      using has_derivative_unique[OF chain direct] .
    thus ?thesis by (simp add: fun_eq_iff)
  qed

  \<comment> \<open>Invertibility of \<open>Hd (x0,t0)\<close>: block-triangular with scalar corner \<open>T \<noteq> 0\<close>.\<close>
  define Dxpart :: "(real^2)^'n \<Rightarrow> real"
    where "Dxpart = (\<lambda>u. vec_nth (blinfun_apply (G' (x0, \<phi> t0)) (u, 0)) 1)"
  define T :: real
    where "T = vec_nth (blinfun_apply (G' (x0, \<phi> t0)) (0, D\<phi> t0)) 1"
  have Tnz: "T \<noteq> 0"
    unfolding T_def using G'_omega_part[of "\<phi> t0" "D\<phi> t0"] trans by simp

  have blDxpart: "bounded_linear Dxpart"
    unfolding Dxpart_def
    by (intro bounded_linear_compose[OF bounded_linear_vec_nth]
              bounded_linear_compose[OF blinfun.bounded_linear_right]
              bounded_linear_Pair bounded_linear_ident bounded_linear_zero)

  define invHmap :: "(((real^2)^'n) \<times> real) \<Rightarrow> (((real^2)^'n) \<times> real)"
    where "invHmap = (\<lambda>q. (fst q, (snd q - Dxpart (fst q)) / T))"

  have blMinusDxpart: "bounded_linear (\<lambda>q::(((real^2)^'n) \<times> real). snd q - Dxpart (fst q))"
    by (intro bounded_linear_sub bounded_linear_snd
              bounded_linear_compose[OF blDxpart bounded_linear_fst])

  have blInvHmap: "bounded_linear invHmap"
    unfolding invHmap_def
    by (intro bounded_linear_Pair bounded_linear_fst
              bounded_linear_compose[OF bounded_linear_divide blMinusDxpart])

  define invHd :: "(((real^2)^'n) \<times> real) \<Rightarrow>\<^sub>L (((real^2)^'n) \<times> real)"
    where "invHd = Blinfun invHmap"

  have invHd_apply: "blinfun_apply invHd = invHmap"
    unfolding invHd_def using bounded_linear_Blinfun_apply[OF blInvHmap] .

  have Hd_x0t0_apply: "blinfun_apply (Hd (x0,t0)) q = (fst q, Dxpart (fst q) + snd q * T)"
    for q :: "((real^2)^'n) \<times> real"
  proof -
    have x0t0U': "(x0,t0) \<in> U"
      unfolding U_def using t0ab by simp

    have altq: "(Hgrad1 \<omega>0 \<omega>s \<phi> has_derivative Hmap (x0,t0)) (at (x0,t0))"
      unfolding Hmap_def using has_derivative_Hgrad1_at[OF G'd phid[OF t0ab]] by simp

    have Hd_eq: "blinfun_apply (Hd (x0,t0)) q = Hmap (x0,t0) q"
      using has_derivative_unique[OF Hderiv[OF x0t0U'] altq] by simp

    let ?L = "blinfun_apply (G' (x0, \<phi> t0))"

    have split: "(fst q, snd q *\<^sub>R D\<phi> t0) = (fst q, 0) + snd q *\<^sub>R (0, D\<phi> t0)"
      by simp

    have Lsplit: "?L (fst q, snd q *\<^sub>R D\<phi> t0)
        = ?L (fst q, 0) + snd q *\<^sub>R ?L (0, D\<phi> t0)"
      by (subst split, metis (no_types, lifting) blinfun.add_right blinfun.scaleR_right)

    have component_split: "vec_nth (?L (fst q, snd q *\<^sub>R D\<phi> t0)) 1
        = vec_nth (?L (fst q, 0)) 1 + snd q * vec_nth (?L (0, D\<phi> t0)) 1"
      using Lsplit by simp

    have Hmap_eq: "Hmap (x0,t0) q = (fst q, Dxpart (fst q) + snd q * T)"
      unfolding Hmap_def Dxpart_def T_def using component_split by simp

    show ?thesis using Hd_eq Hmap_eq by simp
  qed

  have invHd_Hd: "invHd o\<^sub>L Hd (x0,t0) = id_blinfun"
  proof (rule blinfun_eqI)
    fix q :: "((real^2)^'n) \<times> real"
    have "blinfun_apply (invHd o\<^sub>L Hd (x0,t0)) q
        = invHmap (fst q, Dxpart (fst q) + snd q * T)"
      by (simp add: blinfun_compose.rep_eq Hd_x0t0_apply invHd_apply)
    also have "\<dots> = (fst q, snd q)"
      unfolding invHmap_def using Tnz by (simp add: field_simps)
    finally show "blinfun_apply (invHd o\<^sub>L Hd (x0,t0)) q = blinfun_apply id_blinfun q"
      by simp
  qed

  have x0t0U: "(x0,t0) \<in> U" unfolding U_def using t0ab by simp

  obtain U' V g g' where
    ifU': "open U'" and ifU'subU: "U' \<subseteq> U" and ifx0U': "(x0,t0) \<in> U'"
    and ifV: "open V" and ifHx0V: "Hgrad1 \<omega>0 \<omega>s \<phi> (x0,t0) \<in> V"
    and ifhomeo: "homeomorphism U' V (Hgrad1 \<omega>0 \<omega>s \<phi>) g"
    and ifgderiv: "\<And>y. y \<in> V \<Longrightarrow> (g has_derivative (g' y)) (at y)"
  using inverse_function_theorem[OF openU Hderiv Hdcont x0t0U invHd_Hd]
  by metis

  have Hx0t0: "Hgrad1 \<omega>0 \<omega>s \<phi> (x0,t0) = (x0, 0)"
    unfolding Hgrad1_def using crit1 by simp

  have x00V: "(x0,0) \<in> V" using ifHx0V Hx0t0 by simp

  \<comment> \<open>Two independent radii: \<open>e3\<close> keeps \<open>(x,t)\<close>-boxes inside \<open>U'\<close>, \<open>e2\<close> keeps
      \<open>(x,0)\<close>-slices inside \<open>V\<close>.\<close>
  obtain e3 :: real where e3pos: "0 < e3" and e3ball: "ball (x0,t0) e3 \<subseteq> U'"
    using ifU' ifx0U' open_contains_ball by blast
  obtain e2 :: real where e2pos: "0 < e2" and e2ball: "ball (x0,0) e2 \<subseteq> V"
    using ifV x00V open_contains_ball by blast

  define r0 :: real where "r0 = min e2 e3 / 2"
  have r0pos: "0 < r0" unfolding r0_def using e2pos e3pos by simp
  have r0e2: "r0 < e2 / sqrt 2"
  proof -
    have hle: "r0 \<le> e2 / 2"
      unfolding r0_def
      by simp

    have sqrt2pos: "0 < sqrt 2"
      by simp
    have sqrt2lt2: "sqrt 2 < 2"
      by (simp add: sqrt2_less_2)
    have "e2 / 2 < e2 / sqrt 2"
      using e2pos sqrt2pos sqrt2lt2 frac_less2 by blast
    thus ?thesis
      using hle  by linarith
  qed
  have r0e3: "r0 < e3 / sqrt 2"
  proof -
    have hle: "r0 \<le> e3 / 2"
      unfolding r0_def
      by simp

    have sqrt2pos: "0 < sqrt 2"
      by simp
    have sqrt2lt2: "sqrt 2 < 2"
      by (simp add: sqrt2_less_2)
    have "e3 / 2 < e3 / sqrt 2"
      using e3pos sqrt2pos sqrt2lt2 frac_less2 by blast
    thus ?thesis
      using hle by linarith
  qed

  define B :: "((real^2)^'n) set" where "B = ball x0 r0"
  have openB: "open B" unfolding B_def by simp
  have x0B: "x0 \<in> B" unfolding B_def using r0pos by simp

  define \<epsilon> :: real where "\<epsilon> = min r0 (min (t0 - a) (b - t0))"
  have \<epsilon>pos: "0 < \<epsilon>" unfolding \<epsilon>_def using r0pos t0ab by simp
  have \<epsilon>_sub_ab: "{t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}"
    unfolding \<epsilon>_def by auto
  have \<epsilon>_le_r0: "\<epsilon> \<le> r0" unfolding \<epsilon>_def by simp

  have B_slice_V: "\<And>x. x \<in> B \<Longrightarrow> (x,0) \<in> V"
  proof -
    fix x assume xB: "x \<in> B"
    have "dist x x0 < r0" using xB unfolding B_def by (simp only: mem_ball dist_commute)
    hence "dist (x,0) (x0,0) < e2"
      unfolding dist_Pair_Pair using r0e2
      using e2pos lemma_real_divide_sqrt_less by force
    thus "(x,0) \<in> V" using e2ball by (simp only: mem_ball dist_commute, fastforce)
  qed

  have box_sub_U': "\<And>x t. x \<in> B \<Longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<Longrightarrow> (x,t) \<in> U'"
  proof -
    fix x t assume xB: "x \<in> B" and tI: "t \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
    have dx: "dist x x0 < r0" using xB unfolding B_def by (simp only: mem_ball dist_commute)
    have dt: "dist t t0 < r0" using tI \<epsilon>_le_r0 by (auto simp: dist_real_def)
    have "dist (x,t) (x0,t0) < e3"
      unfolding dist_Pair_Pair using r0e3 dx dt real_sqrt_sum_squares_less by simp
    thus "(x,t) \<in> U'" using e3ball by (simp only: mem_ball dist_commute, fastforce)
  qed

  \<comment> \<open>Define \<open>\<tau>\<close> on \<open>B\<close> via the local inverse \<open>g\<close> restricted to the slice \<open>{(x,0)}\<close>.\<close>
  define \<tau> :: "(real^2)^'n \<Rightarrow> real" where "\<tau> = (\<lambda>x. snd (g (x,0)))"

  have g_x00: "g (x0,0) = (x0,t0)"
    using ifhomeo ifx0U' Hx0t0 unfolding homeomorphism_def by metis

  have tau_x0: "\<tau> x0 = t0" unfolding \<tau>_def using g_x00 by simp

  have g_fst: "\<And>x. x \<in> B \<Longrightarrow> fst (g (x,0)) = x"
  proof -
    fix x assume xB: "x \<in> B"
    have x0V: "(x,0) \<in> V" using B_slice_V[OF xB] .
    have "Hgrad1 \<omega>0 \<omega>s \<phi> (g (x,0)) = (x,0)"
      using ifhomeo x0V unfolding homeomorphism_def by blast
    thus "fst (g (x,0)) = x" unfolding Hgrad1_def by (metis fst_conv)
  qed

  have g_eq: "\<And>x. x \<in> B \<Longrightarrow> g (x,0) = (x, \<tau> x)"
    using g_fst unfolding \<tau>_def by (metis prod.collapse)

  have exist_clause: "\<And>x. x \<in> B \<Longrightarrow> vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
  proof -
    fix x assume xB: "x \<in> B"
    have x0V: "(x,0) \<in> V" using B_slice_V[OF xB] .
    have "Hgrad1 \<omega>0 \<omega>s \<phi> (g (x,0)) = (x,0)"
      using ifhomeo x0V unfolding homeomorphism_def by blast
    hence "Hgrad1 \<omega>0 \<omega>s \<phi> (x, \<tau> x) = (x,0)" using g_eq[OF xB] by simp
    thus "vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
      unfolding Hgrad1_def by (simp add: prod_eq_iff)
  qed

  have gU'inv: "\<And>p. p \<in> U' \<Longrightarrow> g (Hgrad1 \<omega>0 \<omega>s \<phi> p) = p"
    using ifhomeo unfolding homeomorphism_def by blast

  have gcontV: "continuous_on V g"
    using ifhomeo
    unfolding homeomorphism_def
    by blast

  have gcont0: "continuous (at (x0,0)) g"
    using gcontV ifV x00V
    by (simp add: continuous_on_eq_continuous_at)

  obtain \<delta> :: real where
      \<delta>pos: "0 < \<delta>"
    and \<delta>g: "\<And>y. dist y (x0,0) < \<delta>
        \<Longrightarrow> dist (g y) (g (x0,0)) < \<epsilon>"
    using gcont0 \<epsilon>pos
    unfolding continuous_at_eps_delta
    using Elementary_Metric_Spaces.continuous_at_eps_delta by blast


  define Bsmall :: "((real^2)^'n) set"
    where "Bsmall = B \<inter> ball x0 \<delta>"

  have openBsmall: "open Bsmall"
    unfolding Bsmall_def
    using openB
    by blast

  have x0Bsmall: "x0 \<in> Bsmall"
    unfolding Bsmall_def
    using x0B \<delta>pos
    by simp

  have Bsmall_sub_B: "Bsmall \<subseteq> B"
    unfolding Bsmall_def
    by simp

  have range_clause:
      "\<And>x. x \<in> Bsmall \<Longrightarrow> \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
  proof -
    fix x
    assume xBsmall: "x \<in> Bsmall"

    have xB: "x \<in> B"
      using xBsmall Bsmall_sub_B
      by blast

    have xdelta: "dist x x0 < \<delta>"
      using xBsmall
      unfolding Bsmall_def
      by (simp add: Met_TC.commute)

    have pair_delta: "dist (x,0) (x0,0) < \<delta>"
      using xdelta
      by (simp add: dist_Pair_Pair)

    have gclose:
        "dist (g (x,0)) (g (x0,0)) < \<epsilon>"
      by (rule \<delta>g[OF pair_delta])

    have tau_close: "dist (\<tau> x) t0 < \<epsilon>"
    proof -
      have "dist (\<tau> x) t0
          = dist (snd (g (x,0))) (snd (g (x0,0)))"
        unfolding \<tau>_def
        using g_x00
        by simp
      also have "\<dots> \<le> dist (g (x,0)) (g (x0,0))"
        by (rule dist_snd_le)
      also have "\<dots> < \<epsilon>"
        by (rule gclose)
      finally show ?thesis .
    qed

    show "\<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
      using tau_close
      by (auto simp: dist_real_def abs_less_iff)
  qed

  \<comment> \<open>Differentiability of \<open>\<tau>\<close> at EVERY \<open>x\<in>B\<close>, via \<open>g\<close>'s derivative at \<open>(x,0)\<close>
      (available for any \<open>x\<in>B\<close> since \<open>(x,0)\<in>V\<close> by @{thm B_slice_V}, exactly
      mirroring the \<open>x0\<close>-only argument) -- plus continuity of \<open>\<tau>\<close> on all of
      \<open>B\<close>, directly from \<open>g\<close>'s continuity on \<open>V\<close> (@{thm gcontV}).\<close>
  have tau_diff: "\<tau> differentiable (at x)" if xB: "x \<in> B" for x
  proof -
    have x0V: "(x,0) \<in> V" using B_slice_V[OF xB] .
    obtain gd where gd: "(g has_derivative gd) (at (x,0))"
      using ifgderiv[OF x0V] by blast
    have p0: "((\<lambda>y. (y,0::real)) has_derivative (\<lambda>u. (u,0::real))) (at x)"
      by (auto intro!: derivative_eq_intros)
    have compderiv: "((\<lambda>y. g (y,0)) has_derivative (gd o (\<lambda>u. (u,0::real)))) (at x)"
      using diff_chain_at[OF p0 gd] by (simp add: o_def)
    have "((\<lambda>y. snd (g (y,0))) has_derivative
            (snd o (gd o (\<lambda>u. (u,0::real))))) (at x)"
      using bounded_linear.has_derivative[OF bounded_linear_snd compderiv]
      by (simp add: o_def)
    hence "(\<tau> has_derivative (snd o (gd o (\<lambda>u. (u,0::real))))) (at x)"
      unfolding \<tau>_def .
    thus ?thesis by (auto simp: differentiable_def)
  qed

  have tau_cont: "continuous_on B \<tau>"
  proof -
    have pairB: "continuous_on B (\<lambda>x. (x, 0::real))"
      by (intro continuous_intros)
    have imgB: "(\<lambda>x. (x, 0::real)) ` B \<subseteq> V"
      using B_slice_V by auto
    have gxcont: "continuous_on B (\<lambda>x. g (x,0))"
      using continuous_on_compose[OF pairB continuous_on_subset[OF gcontV imgB]]
      by (simp add: o_def)
    have "continuous_on B (\<lambda>x. snd (g (x,0)))"
      by (rule continuous_on_snd[OF gxcont])
    thus ?thesis unfolding \<tau>_def .
  qed

  \<comment> \<open>Uniqueness of \<open>t = \<tau> x\<close> among solutions in the shrunk box.\<close>
  have uniq_clause: "\<And>x t. x \<in> B \<Longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<Longrightarrow>
        vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<Longrightarrow> t = \<tau> x"
  proof -
    fix x t assume xB: "x \<in> B" and tI: "t \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
      and z0: "vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0"
    have xtU': "(x,t) \<in> U'" using box_sub_U'[OF xB tI] .
    have Hxt: "Hgrad1 \<omega>0 \<omega>s \<phi> (x,t) = (x,0)"
      unfolding Hgrad1_def using z0 by simp
    have "g (Hgrad1 \<omega>0 \<omega>s \<phi> (x,t)) = (x,t)"
      using gU'inv[OF xtU'] .
    hence gxt: "g (x,0) = (x,t)" using Hxt by simp
    have "g (x,0) = (x, \<tau> x)" using g_eq[OF xB] .
    with gxt show "t = \<tau> x" by simp
  qed

  show ?thesis
  proof (rule that[of Bsmall \<epsilon> \<tau>])
    show "open Bsmall"
      by (rule openBsmall)
    show "x0 \<in> Bsmall"
      by (rule x0Bsmall)
    show "0 < \<epsilon>"
      by (rule \<epsilon>pos)
    show "{t0 - \<epsilon><..<t0 + \<epsilon>} \<subseteq> {a<..<b}"
      by (rule \<epsilon>_sub_ab)
    show "\<tau> x0 = t0"
      by (rule tau_x0)
    show "\<And>x. x \<in> Bsmall \<Longrightarrow> \<tau> x \<in> {t0 - \<epsilon><..<t0 + \<epsilon>}"
      by (rule range_clause)
    show "\<And>x. x \<in> Bsmall \<Longrightarrow>
        vec_nth
          (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
    proof -
      fix x
      assume xBsmall: "x \<in> Bsmall"
      have xB: "x \<in> B"
        using xBsmall Bsmall_sub_B
        by blast
      show "vec_nth
          (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
        by (rule exist_clause[OF xB])
    qed
    show "\<And>x. x \<in> Bsmall \<Longrightarrow> \<tau> differentiable (at x)"
      using tau_diff Bsmall_sub_B by blast
    show "continuous_on Bsmall \<tau>"
      using tau_cont Bsmall_sub_B continuous_on_subset by blast
    show "\<And>x t. x \<in> Bsmall \<Longrightarrow>
        t \<in> {t0 - \<epsilon><..<t0 + \<epsilon>} \<Longrightarrow>
        vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<Longrightarrow>
        t = \<tau> x"
    proof -
      fix x t
      assume xBsmall: "x \<in> Bsmall"
        and tI: "t \<in> {t0 - \<epsilon><..<t0 + \<epsilon>}"
        and z0:
          "vec_nth
            (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0"
      have xB: "x \<in> B"
        using xBsmall Bsmall_sub_B
        by blast
      show "t = \<tau> x"
        by (rule uniq_clause[OF xB tI z0])
    qed
  qed
qed

section \<open>The explicit closed form of \<open>\<tau>\<close>'s derivative\<close>

text \<open>\<^bold>\<open>Implicit differentiation.\<close>  Given \<open>\<tau>\<close> differentiable at \<open>x0\<close> with
  \<open>gradU_1(x,\<phi>(\<tau> x)) \<equiv> 0\<close> on an open neighborhood \<open>B\<close> of \<open>x0\<close> (exactly
  @{thm gradU1_arc_local_graph}'s output), differentiate the identity: the
  \<open>x\<close>-partial of \<open>gradU_1\<close> at fixed \<open>\<omega>=\<phi> t0\<close> plus \<open>D\<tau>\<close> times the
  transversality scalar \<open>T\<close> must vanish, giving \<open>D\<tau> = -(x\<close>-partial\<open>)/T\<close> --
  no new derivative order, just @{thm has_derivative_gradU_dip_x_explicit}
  (already-available \<open>x\<close>-side) and @{thm gradU_dip_joint_C1} (already-available
  joint side) combined via the chain rule.\<close>

lemma G'_x_part:
  fixes x0 :: "(real^2)^'n::finite" and \<omega> :: "real^2" and \<omega>0 \<omega>s :: "real^2"
    and G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
  assumes G'd: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                 has_derivative blinfun_apply (G' z)) (at z)"
  shows "blinfun_apply (G' (x0, \<omega>)) (u, 0)
      = frechet_derivative (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) (at x0) u"
proof -
  have iota_deriv: "((\<lambda>\<eta>. (\<eta>,\<omega>)) has_derivative (\<lambda>u. (u,0))) (at x0)"
    by (auto intro!: derivative_eq_intros)
  have Gz: "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
               has_derivative blinfun_apply (G' (x0,\<omega>))) (at (x0,\<omega>))"
    using G'd .
  have chain: "((\<lambda>\<eta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip \<eta> \<omega>)
      has_derivative (\<lambda>u. blinfun_apply (G' (x0,\<omega>)) (u,0))) (at x0)"
    using diff_chain_at[OF iota_deriv Gz] by (simp add: o_def)
  have direct: "((\<lambda>\<eta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip \<eta> \<omega>)
      has_derivative (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1)) (gain_dip \<omega>)
                            (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                            (M_paper x0 (cvec_dip \<omega>0 \<omega>s \<omega>))
                            (DM_paper_x x0 (cvec_dip \<omega>0 \<omega>s \<omega>) h))) (at x0)"
    using has_derivative_gradU_dip_x_explicit[where V=UNIV] by fastforce
  have "(\<lambda>u. blinfun_apply (G' (x0,\<omega>)) (u,0))
      = (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1)) (gain_dip \<omega>)
                            (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                            (M_paper x0 (cvec_dip \<omega>0 \<omega>s \<omega>))
                            (DM_paper_x x0 (cvec_dip \<omega>0 \<omega>s \<omega>) h))"
    using has_derivative_unique[OF chain direct] by (simp add: fun_eq_iff)
  hence eq1:
    "blinfun_apply (G' (x0, \<omega>)) (u, 0)
      = (\<chi> j.
          dEjm
            (frechet_derivative gdip
              (at (vec_nth \<omega> 1))
              (vec_nth (axis j 1) 1))
            (gain_dip \<omega>)
            (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
            (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
            (M_paper x0 (cvec_dip \<omega>0 \<omega>s \<omega>))
            (DM_paper_x x0 (cvec_dip \<omega>0 \<omega>s \<omega>) u))"
    by (simp add: fun_eq_iff)
  have fr: "frechet_derivative (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) (at x0) = (\<lambda>h. \<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1)) (gain_dip \<omega>)
                            (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                            (M_paper x0 (cvec_dip \<omega>0 \<omega>s \<omega>))
                            (DM_paper_x x0 (cvec_dip \<omega>0 \<omega>s \<omega>) h))"
    using frechet_derivative_at[OF direct] by argo
  show ?thesis unfolding fr using eq1 by simp
qed

text \<open>The \<open>\<omega>\<close>-only slice of \<open>G'\<close> agrees with \<open>HessU\<close> (the counterpart of
  @{thm G'_x_part} on the other side of the joint derivative) -- compose the
  constant-\<open>x0\<close> embedding \<open>\<iota>(\<omega>)=(x0,\<omega>)\<close> with \<open>G'd\<close> via the chain rule and
  match against @{thm gradU_dip_has_derivative} by uniqueness.\<close>

lemma G'_omega_part:
  fixes x0 :: "(real^2)^'n::finite" and \<omega> v :: "real^2" and \<omega>0 \<omega>s :: "real^2"
    and G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
  assumes G'd: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                 has_derivative blinfun_apply (G' z)) (at z)"
  shows "blinfun_apply (G' (x0, \<omega>)) (0, v)
      = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> *v v"
proof -
  have iota_deriv: "((\<lambda>\<eta>. (x0,\<eta>)) has_derivative (\<lambda>v. (0,v))) (at \<omega>)"
    by (auto intro!: derivative_eq_intros)
  have Gz: "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
               has_derivative blinfun_apply (G' (x0,\<omega>))) (at (x0,\<omega>))"
    using G'd .
  have chain: "((\<lambda>\<eta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<eta>)
      has_derivative (\<lambda>v. blinfun_apply (G' (x0,\<omega>)) (0,v))) (at \<omega>)"
    using diff_chain_at[OF iota_deriv Gz] by (simp add: o_def)
  have direct: "((\<lambda>\<eta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<eta>)
      has_derivative (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> *v v)) (at \<omega>)"
    using gradU_dip_has_derivative .
  have "(\<lambda>v. blinfun_apply (G' (x0,\<omega>)) (0,v))
      = (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega> *v v)"
    using has_derivative_unique[OF chain direct] .
  thus ?thesis by (simp add: fun_eq_iff)
qed

lemma tau_has_derivative:
  fixes x0 :: "(real^2)^'n::finite" and t0 :: real
    and \<phi> :: "real \<Rightarrow> real^2" and D\<phi>0 :: "real^2"
    and \<omega>0 \<omega>s :: "real^2"
    and B :: "((real^2)^'n) set" and \<tau> :: "(real^2)^'n \<Rightarrow> real"
  assumes openB: "open B" and x0B: "x0 \<in> B"
    and taux0: "\<tau> x0 = t0"
    and taudiff: "\<tau> differentiable (at x0)"
    and zero_on_B: "\<And>x. x \<in> B \<Longrightarrow> vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
    and phid_t0: "(\<phi> has_vector_derivative D\<phi>0) (at t0)"
    and trans: "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi>0) 1 \<noteq> 0"
  shows "(\<tau> has_derivative
      (\<lambda>u. - vec_nth (frechet_derivative (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> t0)) (at x0) u) 1
             / vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi>0) 1))
      (at x0)"
proof -
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))" where
    G'd: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                 has_derivative blinfun_apply (G' z)) (at z)"
    using gradU_dip_joint_C1 by blast

  obtain Dtau where Dtau: "(\<tau> has_derivative Dtau) (at x0)"
    using taudiff unfolding differentiable_def by blast

  define T :: real where "T = vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi>0) 1"
  have Tnz: "T \<noteq> 0" unfolding T_def using trans by simp

  define Dx1 :: "(real^2)^'n \<Rightarrow> real"
    where "Dx1 = (\<lambda>u. vec_nth (frechet_derivative (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> t0)) (at x0) u) 1)"

  \<comment> \<open>Chain rule: the pairing \<open>x \<mapsto> (x, \<phi>(\<tau> x))\<close> at \<open>x0\<close>.\<close>
  have phid_t0': "(\<phi> has_derivative (\<lambda>s. s *\<^sub>R D\<phi>0)) (at t0)"
    using phid_t0 unfolding has_vector_derivative_def .
  have taut0: "(\<phi> has_derivative (\<lambda>s. s *\<^sub>R D\<phi>0)) (at (\<tau> x0))" using phid_t0' taux0 by simp
  have phitau: "((\<lambda>x. \<phi> (\<tau> x)) has_derivative (\<lambda>u. Dtau u *\<^sub>R D\<phi>0)) (at x0)"
    using diff_chain_at[OF Dtau taut0] by (simp add: o_def)
  have idderiv: "((\<lambda>x. x) has_derivative (\<lambda>u. u)) (at x0)" by (rule has_derivative_ident)
  have Qpair: "((\<lambda>x. (x, \<phi> (\<tau> x))) has_derivative (\<lambda>u. (u, Dtau u *\<^sub>R D\<phi>0))) (at x0)"
    using has_derivative_Pair[OF idderiv phitau] .

  \<comment> \<open>Compose with the joint derivative of \<open>gradU\<close> at \<open>(x0,\<phi> t0)\<close>.\<close>
  have Gatx0: "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
               has_derivative blinfun_apply (G' (x0, \<phi> t0))) (at (x0, \<phi> t0))"
    using G'd .
  have compFull: "((\<lambda>x. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)))
      has_derivative (\<lambda>u. blinfun_apply (G' (x0, \<phi> t0)) (u, Dtau u *\<^sub>R D\<phi>0))) (at x0)"
  proof -
    have chain:
        "(((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
              \<circ> (\<lambda>x. (x, \<phi> (\<tau> x))))
          has_derivative
            (blinfun_apply (G' (x0, \<phi> t0))
              \<circ> (\<lambda>u. (u, Dtau u *\<^sub>R D\<phi>0))))
          (at x0)"
    proof (rule diff_chain_at[OF Qpair])
      show "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip
                    (fst p) (snd p))
          has_derivative blinfun_apply (G' (x0, \<phi> t0)))
          (at ((\<lambda>x. (x, \<phi> (\<tau> x))) x0))"
        using Gatx0 taux0
        by simp
    qed

    show ?thesis
      using chain
      by (simp add: o_def)
  qed

  have compF:
      "((\<lambda>x. vec_nth
          (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1)
        has_derivative
          (\<lambda>u. vec_nth
            (blinfun_apply (G' (x0, \<phi> t0))
              (u, Dtau u *\<^sub>R D\<phi>0)) 1))
        (at x0)"
    using bounded_linear.has_derivative[OF bounded_linear_vec_nth compFull] .

  \<comment> \<open>Split the joint action into \<open>x\<close>- and \<open>\<omega>\<close>-parts (bilinearity of \<open>blinfun_apply\<close>).\<close>
  have split: "\<And>u. (u, Dtau u *\<^sub>R D\<phi>0) = (u,0) + Dtau u *\<^sub>R (0,D\<phi>0)" by simp
  have Lsplit: "\<And>u. blinfun_apply (G' (x0,\<phi> t0)) (u, Dtau u *\<^sub>R D\<phi>0)
      = blinfun_apply (G' (x0,\<phi> t0)) (u,0) + Dtau u *\<^sub>R blinfun_apply (G' (x0,\<phi> t0)) (0,D\<phi>0)"
    by (subst split, metis (no_types, lifting) blinfun.add_right blinfun.scaleR_right)

  have xpart: "\<And>u. vec_nth (blinfun_apply (G' (x0, \<phi> t0)) (u,0)) 1 = Dx1 u"
  proof -
    fix u

    have iota_deriv: "((\<lambda>y. (y, \<phi> t0)) has_derivative (\<lambda>v. (v,0))) (at x0)"
      by (auto intro!: derivative_eq_intros)

    have joint:
        "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          has_derivative blinfun_apply (G' (x0, \<phi> t0)))
          (at (x0, \<phi> t0))"
      using G'd .

    have chain:
        "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> t0))
          has_derivative
            (\<lambda>v. blinfun_apply (G' (x0, \<phi> t0)) (v,0)))
          (at x0)"
      using diff_chain_at[OF iota_deriv joint]
      by (simp add: o_def)

    have derivative_eq:
        "frechet_derivative
            (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> t0))
            (at x0)
          = (\<lambda>v. blinfun_apply (G' (x0, \<phi> t0)) (v,0))"
      by (simp add: chain frechet_derivative_at')

    show "vec_nth (blinfun_apply (G' (x0, \<phi> t0)) (u,0)) 1 = Dx1 u"
      unfolding Dx1_def
      using derivative_eq
      by simp
  qed

  have omega_part:
      "vec_nth
        (blinfun_apply (G' (x0, \<phi> t0)) (0, D\<phi>0)) 1 = T"
  proof -
    have iota_deriv:
        "((\<lambda>\<eta>. (x0, \<eta>)) has_derivative (\<lambda>v. (0, v))) (at (\<phi> t0))"
      by (auto intro!: derivative_eq_intros)

    have joint:
        "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          has_derivative blinfun_apply (G' (x0, \<phi> t0)))
          (at (x0, \<phi> t0))"
      using G'd .

    have chain:
        "((\<lambda>\<eta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<eta>)
          has_derivative
            (\<lambda>v. blinfun_apply (G' (x0, \<phi> t0)) (0, v)))
          (at (\<phi> t0))"
      using diff_chain_at[OF iota_deriv joint]
      by (simp add: o_def)

    have direct:
        "((\<lambda>\<eta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<eta>)
          has_derivative
            (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v v))
          (at (\<phi> t0))"
      using gradU_dip_has_derivative .

    have derivative_eq:
        "(\<lambda>v. blinfun_apply (G' (x0, \<phi> t0)) (0, v))
          =
         (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v v)"
      using has_derivative_unique[OF chain direct] .

    have "blinfun_apply (G' (x0, \<phi> t0)) (0, D\<phi>0)
        = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi>0"
      using derivative_eq
      by (simp add: fun_eq_iff)

    thus ?thesis
      unfolding T_def
      by simp
  qed

  have derivative_formula:
      "\<And>u. vec_nth
          (blinfun_apply (G' (x0, \<phi> t0))
            (u, Dtau u *\<^sub>R D\<phi>0)) 1
        = Dx1 u + Dtau u * T"
  proof -
    fix u

    let ?L = "blinfun_apply (G' (x0, \<phi> t0))"

    have Llin: "bounded_linear ?L"
      by (rule blinfun.bounded_linear_right)

    have split:
        "(u, Dtau u *\<^sub>R D\<phi>0)
          = (u, 0) + Dtau u *\<^sub>R (0, D\<phi>0)"
      by simp

    have Lsplit:
        "?L (u, Dtau u *\<^sub>R D\<phi>0)
          = ?L (u, 0) + Dtau u *\<^sub>R ?L (0, D\<phi>0)"
      by (subst split, simp add: Lsplit)


    show "vec_nth (?L (u, Dtau u *\<^sub>R D\<phi>0)) 1
        = Dx1 u + Dtau u * T"
      using Lsplit xpart[of u] omega_part
      by simp
  qed

  have compF':
      "((\<lambda>x. vec_nth
          (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1)
        has_derivative (\<lambda>u. Dx1 u + Dtau u * T))
        (at x0)"
    using compF
    by (simp add: derivative_formula)


  \<comment> \<open>The composed function is identically \<open>0\<close> on the open set \<open>B\<close>.\<close>
  have zeroderiv: "((\<lambda>x. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1)
      has_derivative (\<lambda>u. 0)) (at x0)"
  proof (rule has_derivative_transform_within_open[OF has_derivative_const openB x0B])
    fix x assume "x \<in> B"
    thus "(0::real) = vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1"
      using zero_on_B by simp
  qed

  have eqderiv: "(\<lambda>u. Dx1 u + Dtau u * T) = (\<lambda>u. (0::real))"
    using has_derivative_unique[OF compF' zeroderiv] .
  have Dtau_eq: "\<And>u. Dtau u = - Dx1 u / T"
  proof -
    fix u
    have "Dx1 u + Dtau u * T = 0" using eqderiv by (simp add: fun_eq_iff)
    thus "Dtau u = - Dx1 u / T" using Tnz by (simp add: field_simps)
  qed
  have "Dtau = (\<lambda>u. - Dx1 u / T)" using Dtau_eq by (simp add: fun_eq_iff)
  thus ?thesis unfolding Dx1_def T_def using Dtau by simp
qed

section \<open>The leftover \<open>gradU_2\<close> condition composed along the \<open>\<tau>\<close>-graph\<close>

text \<open>\<^bold>\<open>The Schur-complement-style leftover cut.\<close>  Having eliminated \<open>t\<close> via
  \<open>\<tau>\<close> (using \<open>gradU_1\<close>'s transversality), the SECOND \<open>gradU\<close> component
  composed along the graph, \<open>x \<mapsto> gradU_2(x,\<phi>(\<tau> x))\<close>, is the genuine
  leftover \<open>x\<close>-space cut.  Its derivative combines BOTH components of the
  same \<open>x\<close>-partial frechet derivative (@{thm G'_x_part}, components 1 and 2)
  with \<open>D\<tau>\<close>'s closed form (@{thm tau_has_derivative}) via the chain rule --
  no new derivative order, exactly the plan's Schur-complement combination
  \<open>Dx2 - (T2/T1)\<cdot>Dx1\<close>.\<close>

lemma gradU2_along_graph_has_derivative:
  fixes x0 :: "(real^2)^'n::finite" and t0 :: real
    and \<phi> :: "real \<Rightarrow> real^2" and D\<phi>0 :: "real^2"
    and \<omega>0 \<omega>s :: "real^2"
    and B :: "((real^2)^'n) set" and \<tau> :: "(real^2)^'n \<Rightarrow> real"
  assumes openB: "open B" and x0B: "x0 \<in> B"
    and taux0: "\<tau> x0 = t0"
    and taudiff: "\<tau> differentiable (at x0)"
    and zero_on_B: "\<And>x. x \<in> B \<Longrightarrow> vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
    and phid_t0: "(\<phi> has_vector_derivative D\<phi>0) (at t0)"
    and trans: "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi>0) 1 \<noteq> 0"
  defines "Dx1 \<equiv> (\<lambda>u. vec_nth (frechet_derivative (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> t0)) (at x0) u) 1)"
    and "Dx2 \<equiv> (\<lambda>u. vec_nth (frechet_derivative (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> t0)) (at x0) u) 2)"
    and "T1 \<equiv> vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi>0) 1"
    and "T2 \<equiv> vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi>0) 2"
  shows "((\<lambda>x. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 2)
      has_derivative (\<lambda>u. Dx2 u - Dx1 u * T2 / T1))
      (at x0)"
proof -
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))" where
    G'd: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                 has_derivative blinfun_apply (G' z)) (at z)"
    using gradU_dip_joint_C1 by blast

  have Tnz: "T1 \<noteq> 0" unfolding T1_def using trans by simp

  have Dtau: "(\<tau> has_derivative (\<lambda>u. - Dx1 u / T1)) (at x0)"
    unfolding Dx1_def T1_def
    by (rule tau_has_derivative[OF openB x0B taux0 taudiff zero_on_B phid_t0 trans])

  \<comment> \<open>Chain rule: the pairing \<open>x \<mapsto> (x, \<phi>(\<tau> x))\<close> at \<open>x0\<close>.\<close>
  have phid_t0': "(\<phi> has_derivative (\<lambda>s. s *\<^sub>R D\<phi>0)) (at t0)"
    using phid_t0 unfolding has_vector_derivative_def .
  have taut0: "(\<phi> has_derivative (\<lambda>s. s *\<^sub>R D\<phi>0)) (at (\<tau> x0))" using phid_t0' taux0 by simp
  have phitau: "((\<lambda>x. \<phi> (\<tau> x)) has_derivative (\<lambda>u. (- Dx1 u / T1) *\<^sub>R D\<phi>0)) (at x0)"
    using diff_chain_at[OF Dtau taut0] by (simp add: o_def)
  have idderiv: "((\<lambda>x. x) has_derivative (\<lambda>u. u)) (at x0)" by (rule has_derivative_ident)
  have Qpair: "((\<lambda>x. (x, \<phi> (\<tau> x))) has_derivative (\<lambda>u. (u, (- Dx1 u / T1) *\<^sub>R D\<phi>0))) (at x0)"
    using has_derivative_Pair[OF idderiv phitau] .

  \<comment> \<open>Compose with the joint derivative of \<open>gradU\<close> at \<open>(x0,\<phi> t0)\<close>.\<close>
  have Gatx0: "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
               has_derivative blinfun_apply (G' (x0, \<phi> t0))) (at (x0, \<phi> t0))"
    using G'd .
  have compFull: "((\<lambda>x. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)))
      has_derivative (\<lambda>u. blinfun_apply (G' (x0, \<phi> t0)) (u, (- Dx1 u / T1) *\<^sub>R D\<phi>0))) (at x0)"
  proof -
    have chain:
        "(((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
              \<circ> (\<lambda>x. (x, \<phi> (\<tau> x))))
          has_derivative
            (blinfun_apply (G' (x0, \<phi> t0))
              \<circ> (\<lambda>u. (u, (- Dx1 u / T1) *\<^sub>R D\<phi>0))))
          (at x0)"
    proof (rule diff_chain_at[OF Qpair])
      show "((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
          has_derivative blinfun_apply (G' (x0, \<phi> t0)))
          (at ((\<lambda>x. (x, \<phi> (\<tau> x))) x0))"
        using Gatx0 taux0 by simp
    qed
    show ?thesis using chain by (simp add: o_def)
  qed

  \<comment> \<open>Extract component 2 and split via bilinearity, using @{thm G'_x_part}
      and @{thm G'_omega_part} directly (both hold for ANY component).\<close>
  have compF2: "((\<lambda>x. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 2)
      has_derivative (\<lambda>u. vec_nth (blinfun_apply (G' (x0, \<phi> t0)) (u, (- Dx1 u / T1) *\<^sub>R D\<phi>0)) 2)) (at x0)"
    using bounded_linear.has_derivative[OF bounded_linear_vec_nth compFull] .

  have split: "\<And>u. (u, (- Dx1 u / T1) *\<^sub>R D\<phi>0) = (u,0) + (- Dx1 u / T1) *\<^sub>R (0,D\<phi>0)" by simp
  have Lsplit: "\<And>u. blinfun_apply (G' (x0,\<phi> t0)) (u, (- Dx1 u / T1) *\<^sub>R D\<phi>0)
      = blinfun_apply (G' (x0,\<phi> t0)) (u,0) + (- Dx1 u / T1) *\<^sub>R blinfun_apply (G' (x0,\<phi> t0)) (0,D\<phi>0)"
    by (subst split, metis (no_types, lifting) blinfun.add_right blinfun.scaleR_right)

  have xpart2: "\<And>u. vec_nth (blinfun_apply (G' (x0,\<phi> t0)) (u,0)) 2 = Dx2 u"
    unfolding Dx2_def using G'_x_part[OF G'd] by simp
  have opart2: "vec_nth (blinfun_apply (G' (x0,\<phi> t0)) (0,D\<phi>0)) 2 = T2"
    unfolding T2_def using G'_omega_part[OF G'd] by simp

  have component_split: "\<And>u. vec_nth (blinfun_apply (G' (x0,\<phi> t0)) (u, (- Dx1 u / T1) *\<^sub>R D\<phi>0)) 2
      = Dx2 u - Dx1 u * T2 / T1"
    using Lsplit xpart2 opart2 by simp

  show ?thesis using compF2 component_split by simp
qed

definition gradU2_graph :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real \<Rightarrow> real^2)
      \<Rightarrow> (((real^2)^'n::finite) \<Rightarrow> real) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real" where
  "gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x =
     vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 2"

definition arc_schur_L :: "real^2 \<Rightarrow> real^2 \<Rightarrow> (real \<Rightarrow> real^2)
      \<Rightarrow> (real \<Rightarrow> real^2) \<Rightarrow> (((real^2)^'n::finite) \<Rightarrow> real)
      \<Rightarrow> ((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real" where
  "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x u =
     vec_nth
       (frechet_derivative
          (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> (\<tau> x))) (at x) u) 2
     - vec_nth
         (frechet_derivative
            (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> (\<tau> x))) (at x) u) 1
       * vec_nth
           (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 2
       / vec_nth
           (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1"

lemma gradU2_graph_has_derivative_schur:
  fixes B :: "((real^2)^'n::finite) set"
    and x :: "(real^2)^'n"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
  assumes openB: "open B" and xB: "x \<in> B"
    and taudiff: "\<tau> differentiable (at x)"
    and zero_on_B: "\<And>y. y \<in> B \<Longrightarrow>
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> (\<tau> y))) 1 = 0"
    and phid: "(\<phi> has_vector_derivative D\<phi> (\<tau> x)) (at (\<tau> x))"
    and trans: "vec_nth
      (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0"
  shows "(gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> has_derivative arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x) (at x)"
  unfolding gradU2_graph_def arc_schur_L_def
  by (rule gradU2_along_graph_has_derivative
      [OF openB xB refl taudiff zero_on_B phid trans])

lemma continuous_on_gradU2_graph:
  fixes B :: "((real^2)^'n::finite) set"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
  assumes openB: "open B"
    and taudiff: "\<And>x. x \<in> B \<Longrightarrow> \<tau> differentiable (at x)"
    and zero_on_B: "\<And>x. x \<in> B \<Longrightarrow>
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
    and phid: "\<And>x. x \<in> B \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> (\<tau> x)) (at (\<tau> x))"
    and trans: "\<And>x. x \<in> B \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0"
  shows "continuous_on B (gradU2_graph \<omega>0 \<omega>s \<phi> \<tau>)"
proof (rule has_derivative_continuous_on)
  fix x
  assume xB: "x \<in> B"
  show "(gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> has_derivative
      arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x) (at x within B)"
    by (metis assms(1,2,3,4,5) at_within_open gradU2_graph_has_derivative_schur xB)    
qed

lemma continuous_on_arc_schur_L_fixed:
  fixes B :: "((real^2)^'n::finite) set"
    and r :: "(real^2)^'n"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
  assumes omega_cont: "continuous_on B (\<lambda>x. \<phi> (\<tau> x))"
    and Domega_cont: "continuous_on B (\<lambda>x. D\<phi> (\<tau> x))"
    and trans: "\<And>x. x \<in> B \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0"
  shows "continuous_on B (\<lambda>x. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r)"
proof -
  have pairB: "continuous_on B (\<lambda>x. (x, \<phi> (\<tau> x)))"
    by (rule continuous_on_Pair[OF continuous_on_id omega_cont])
  have dxcont: "continuous_on B
      (\<lambda>x. frechet_derivative
        (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (\<phi> (\<tau> x))) (at x) r)"
  proof -
    have hcont:
      "continuous_on
        (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
        (\<lambda>p.
          (\<chi> j.
            dEjm
              (frechet_derivative gdip
                (at (vec_nth (snd p) 1))
                (vec_nth (axis j 1) 1))
              (gain_dip (snd p))
              (vec_nth
                (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 1)
              (vec_nth
                (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 2)
              (M_paper
                (fst p)
                (cvec_dip \<omega>0 \<omega>s (snd p)))
              (DM_paper_x
                (fst p)
                (cvec_dip \<omega>0 \<omega>s (snd p))
                r)) :: real^2)"
      using continuous_on_gradU_dip_xpartial_applied[of \<omega>0 \<omega>s r] .
	    have joint_cont:
	      "continuous_on
	        (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
	        (\<lambda>p. frechet_derivative
	          (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (snd p))
	          (at (fst p)) r)"
	    proof -
	      have fr_eq: "\<And>p :: (((real^2)^'n) \<times> (real^2)).
	        frechet_derivative
	          (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (snd p))
	          (at (fst p)) r
	        =
	        (\<chi> j.
	          dEjm
	            (frechet_derivative gdip
	              (at (vec_nth (snd p) 1))
	              (vec_nth (axis j 1) 1))
	            (gain_dip (snd p))
	            (vec_nth
	              (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 1)
	            (vec_nth
	              (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 2)
	            (M_paper
	              (fst p)
	              (cvec_dip \<omega>0 \<omega>s (snd p)))
	            (DM_paper_x
	              (fst p)
	              (cvec_dip \<omega>0 \<omega>s (snd p))
	              r))"
	      proof -
	        fix p :: "((real^2)^'n) \<times> (real^2)"
	        have direct:
	          "((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (snd p))
	            has_derivative
	              (\<lambda>h. \<chi> j.
	                dEjm
	                  (frechet_derivative gdip
	                    (at (vec_nth (snd p) 1))
	                    (vec_nth (axis j 1) 1))
	                  (gain_dip (snd p))
	                  (vec_nth
	                    (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 1)
	                  (vec_nth
	                    (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 2)
	                  (M_paper
	                    (fst p)
	                    (cvec_dip \<omega>0 \<omega>s (snd p)))
	                  (DM_paper_x
	                    (fst p)
	                    (cvec_dip \<omega>0 \<omega>s (snd p))
	                    h)))
	            (at (fst p))"
	          using has_derivative_gradU_dip_x_explicit[
	            where V = UNIV and x = "fst p" and \<omega> = "snd p" and \<omega>0 = \<omega>0
	              and \<omega>s = \<omega>s]
	          by fastforce
	        show "frechet_derivative
	          (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (snd p))
	          (at (fst p)) r
	        =
	        (\<chi> j.
	          dEjm
	            (frechet_derivative gdip
	              (at (vec_nth (snd p) 1))
	              (vec_nth (axis j 1) 1))
	            (gain_dip (snd p))
	            (vec_nth
	              (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 1)
	            (vec_nth
	              (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 2)
	            (M_paper
	              (fst p)
	              (cvec_dip \<omega>0 \<omega>s (snd p)))
	              (DM_paper_x
	                (fst p)
	                (cvec_dip \<omega>0 \<omega>s (snd p))
	                r))"
	          by (rule fun_cong[OF frechet_derivative_at[OF direct, symmetric]])
	      qed
	      show ?thesis
	        using hcont by (simp add: fr_eq cong: continuous_on_cong)
	    qed
    have comp:
        "continuous_on B
          (\<lambda>x. frechet_derivative
            (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y
              (snd (x, \<phi> (\<tau> x))))
            (at (fst (x, \<phi> (\<tau> x)))) r)"
      by (rule continuous_on_compose2[OF joint_cont pairB])
         simp

    show ?thesis
      using comp
      by simp
  qed
  have HessB: "continuous_on B
      (\<lambda>x. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)))"
    using continuous_on_compose2[OF continuous_on_HessU_dip_joint pairB subset_UNIV]
    by (simp add: o_def)
  have Tcont: "continuous_on B
      (\<lambda>x. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x))"
    by (rule continuous_on_matvec[OF HessB Domega_cont])
  show ?thesis
    unfolding arc_schur_L_def using assms(3)
    by (intro continuous_intros dxcont Tcont trans, presburger)
qed

section \<open>The functional-cut engine (verbatim copy of the reusable combinator
  from \<open>Appendix/Wiring/D3_Chart_Wiring.thy\<close>, kept local here so this scratch
  theory does not depend on the heavier \<open>Applied_Math_D3_Wiring\<close> heap during
  development; delete this copy when splicing into the real file)\<close>

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

lemma chart_core_data_of_countable_cover:
  fixes S :: "((real^2)^'n::finite) set"
    and C :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "S \<subseteq> (\<Union>i. C i)"
    and data: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         C i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
proof -
  have union_core: "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         (\<Union>i. C i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
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
    assume core:
      "(\<Union>i. C i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
       (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
       (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
       (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    have union_cover: "(\<Union>i. C i) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))"
      using core by simp
    have cover': "S \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))"
    proof
      fix x
      assume xS: "x \<in> S"
      have xUnion: "x \<in> (\<Union>i. C i)"
        using cover xS by auto
      show "x \<in> (\<Union>j. (fst \<circ> charts j) ` (Crit j))"
        by (rule subsetD[OF union_cover xUnion])
    qed
    have der: "\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)"
      using core by simp
    have nsurj: "\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))"
      using core by simp
    have cls: "\<forall>j. closed ((fst \<circ> charts j) ` (Crit j))"
      using core by simp
    show ?thesis
      apply (rule exI[where x = charts])
      apply (rule exI[where x = Crit])
      apply (rule exI[where x = D])
      using cover' der nsurj cls
      by simp
  qed
qed

lemma d3_chart_core_of_countable_chart_core_cover:
  fixes V :: "((real^2)^'n::finite) set"
    and S :: "nat \<Rightarrow> ((real^2)^'n) set"
  assumes cover: "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s \<gamma> :: ((real^2)^'n) set) \<subseteq> (\<Union>i. S i)"
    and data: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
  unfolding d3_detHess_arc_chart_core_def
  by (rule chart_core_data_of_countable_cover[OF cover data])

lemma d3_chart_core_of_countable_arc_local_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and X C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and T :: "nat \<Rightarrow> real set"
    and \<phi> :: "real \<Rightarrow> real^2"
  assumes pair_cover: "\<And>x t. x \<in> V \<Longrightarrow> t \<in> {a<..<b} \<Longrightarrow>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<Longrightarrow>
      \<exists>i. x \<in> X i \<and> t \<in> T i"
    and local_cover: "\<And>i x t. x \<in> X i \<Longrightarrow> t \<in> T i \<Longrightarrow>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<Longrightarrow> x \<in> C i"
    and data: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         C i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a<..<b})"
proof (rule d3_chart_core_of_countable_chart_core_cover)
  show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b}) :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. C i)"
  proof
    fix x
    assume xbad: "x \<in> (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b}) :: ((real^2)^'n) set)"
    have xV: "x \<in> V"
      using xbad by simp
    have "\<exists>\<omega>\<in>\<phi> ` {a<..<b}.
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      using xbad unfolding D3BadXG_H0core_def by blast
    obtain t where tint: "t \<in> {a<..<b}"
      and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0"
      using \<open>\<exists>\<omega>\<in>\<phi> ` {a<..<b}.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0\<close>
      by blast
    obtain i where xXi: "x \<in> X i" and tTi: "t \<in> T i"
      using pair_cover[OF xV tint gz] by blast
    have "x \<in> C i"
      by (rule local_cover[OF xXi tTi gz])
    thus "x \<in> (\<Union>i. C i)"
      by blast
  qed
  show "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         C i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            (fst \<circ> charts j has_derivative blinfun_apply (D j x)) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
    by (rule data)
qed

lemma d3_chart_core_of_countable_arc_cball_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and x0 :: "nat \<Rightarrow> ((real^2)^'n)"
    and \<rho> \<epsilon> t0 :: "nat \<Rightarrow> real"
    and C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and \<phi> :: "real \<Rightarrow> real^2"
  assumes pair_cover: "\<And>x t. x \<in> V \<Longrightarrow> t \<in> {a<..<b} \<Longrightarrow>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<Longrightarrow>
      \<exists>i. x \<in> cball (x0 i) (\<rho> i) \<and> t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i}"
    and local_cover: "\<And>i x t. x \<in> cball (x0 i) (\<rho> i) \<Longrightarrow>
      t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i} \<Longrightarrow>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<Longrightarrow> x \<in> C i"
    and data: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         C i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a<..<b})"
proof (rule d3_chart_core_of_countable_arc_local_patches
    [where X = "\<lambda>i. cball (x0 i) (\<rho> i)"
      and T = "\<lambda>i. {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i}"
      and C = C])
  fix x t
  assume xV: "x \<in> V"
    and tint: "t \<in> {a<..<b}"
    and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0"
  show "\<exists>i. x \<in> cball (x0 i) (\<rho> i) \<and> t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i}"
    by (rule pair_cover[OF xV tint gz])
next
  fix i x t
  assume xcb: "x \<in> cball (x0 i) (\<rho> i)"
    and tint: "t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i}"
    and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0"
  show "x \<in> C i"
    by (rule local_cover[OF xcb tint gz])
next
  show "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         C i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            (fst \<circ> charts j has_derivative blinfun_apply (D j x)) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
    by (rule data)
qed

lemma d3_chart_core_of_countable_arc_cball_patches_H0core:
  fixes V :: "((real^2)^'n::finite) set"
    and x0 :: "nat \<Rightarrow> ((real^2)^'n)"
    and \<rho> \<epsilon> t0 :: "nat \<Rightarrow> real"
    and C :: "nat \<Rightarrow> ((real^2)^'n) set"
    and \<phi> :: "real \<Rightarrow> real^2"
  assumes pair_cover: "\<And>x t. x \<in> V \<Longrightarrow> t \<in> {a<..<b} \<Longrightarrow>
      x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> t} \<Longrightarrow>
      \<exists>i. x \<in> cball (x0 i) (\<rho> i) \<and> t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i}"
    and local_cover: "\<And>i x t. x \<in> cball (x0 i) (\<rho> i) \<Longrightarrow>
      t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i} \<Longrightarrow>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<Longrightarrow> x \<in> C i"
    and data: "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         C i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a<..<b})"
proof (rule d3_chart_core_of_countable_chart_core_cover)
  show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b}) :: ((real^2)^'n) set)
      \<subseteq> (\<Union>i. C i)"
  proof
    fix x
    assume xbad: "x \<in> (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b}) :: ((real^2)^'n) set)"
    have xV: "x \<in> V"
      using xbad by simp
    obtain \<omega> where omega_img: "\<omega> \<in> \<phi> ` {a<..<b}"
      and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and det0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
      and nsurj: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      and ncrit: "\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)"
      using xbad unfolding D3BadXG_H0core_def by blast
    obtain t where tint: "t \<in> {a<..<b}" and omega_eq: "\<omega> = \<phi> t"
      using omega_img by blast
    have xsingle: "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> t}"
      unfolding D3BadXG_H0core_def
      using gz det0 cnz nsurj ncrit omega_eq by blast
    obtain i where xcb: "x \<in> cball (x0 i) (\<rho> i)"
      and tint_i: "t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i}"
      using pair_cover[OF xV tint xsingle] by blast
    have gz_t: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0"
      using gz omega_eq by simp
    have "x \<in> C i"
      by (rule local_cover[OF xcb tint_i gz_t])
    thus "x \<in> (\<Union>i. C i)"
      by blast
  qed
  show "\<And>i. \<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         C i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            (fst \<circ> charts j has_derivative blinfun_apply (D j x)) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
    by (rule data)
qed

lemma countable_subcover_of_openin_cover:
  fixes M :: "'a::second_countable_topology set"
    and \<F> :: "'a set set"
  assumes openF: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S"
    and cover: "M \<subseteq> \<Union>\<F>"
  obtains \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "M \<subseteq> \<Union>\<F>'"
proof -
  have scM: "second_countable (top_of_set M)"
    using second_countable_subtopology[OF second_countable_euclidean, of M] by simp
  have lindM: "Lindelof_space (top_of_set M)"
    using second_countable_imp_Lindelof_space[OF scM] .
  have union_top: "\<Union>\<F> = topspace (top_of_set M)"
  proof
    show "\<Union>\<F> \<subseteq> topspace (top_of_set M)"
      by (meson Sup_le_iff openF openin_subset)
    show "topspace (top_of_set M) \<subseteq> \<Union>\<F>"
      using cover by simp
  qed
  have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<F> \<and> \<Union>\<V> = topspace (top_of_set M)"
    using lindM openF union_top unfolding Lindelof_space_def
    by (meson Top1_Ch3.countable_def countableE)
  then obtain \<V> where Vprops:
      "countable \<V> \<and> \<V> \<subseteq> \<F> \<and> \<Union>\<V> = topspace (top_of_set M)"
    by (elim exE)
  have Vcnt: "countable \<V>"
    using Vprops by simp
  have Vsub: "\<V> \<subseteq> \<F>"
    using Vprops by simp
  have VU: "\<Union>\<V> = topspace (top_of_set M)"
    using Vprops by simp
  have Msub: "M \<subseteq> \<Union>\<V>"
    using VU by simp
  show ?thesis
    by (rule that[OF Vsub Vcnt Msub])
qed

lemma d3_chart_core_of_Lindelof_H0core_cball_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> :: "real \<Rightarrow> real^2"
    and M :: "(((real^2)^'n) \<times> real) set"
    and a b :: real
    and \<omega>0 \<omega>s :: "real^2"
  defines "M \<equiv> {q :: ((real^2)^'n) \<times> real.
      fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
      fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}}"
  assumes local: "\<And>q. q \<in> M \<Longrightarrow>
    \<exists>S x0 \<rho> \<epsilon> t0 C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       openin (top_of_set M) S
     \<and> q \<in> S
     \<and> (\<forall>p\<in>S. fst p \<in> cball x0 \<rho> \<and> snd p \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x t. x \<in> cball x0 \<rho> \<longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a<..<b})"
proof -
  define \<F> where "\<F> = {S. \<exists>q\<in>M. \<exists>x0 \<rho> \<epsilon> t0 C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       openin (top_of_set M) S
     \<and> q \<in> S
     \<and> (\<forall>p\<in>S. fst p \<in> cball x0 \<rho> \<and> snd p \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x t. x \<in> cball x0 \<rho> \<longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))}"
  have F_open: "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set M) S"
    unfolding \<F>_def by blast
  have F_cover: "M \<subseteq> \<Union>\<F>"
  proof
    fix q
    assume qM: "q \<in> M"
    obtain S x0 \<rho> \<epsilon> t0 C
      and charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      where w: "openin (top_of_set M) S"
        "q \<in> S"
        "\<forall>p\<in>S. fst p \<in> cball x0 \<rho> \<and> snd p \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
        "\<forall>x t. x \<in> cball x0 \<rho> \<longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C"
        "C \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))"
        "\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j)"
        "\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))"
        "\<forall>j. closed ((fst \<circ> charts j) ` (Crit j))"
      using local[OF qM] by blast
    have "S \<in> \<F>"
      unfolding \<F>_def using qM w by blast
    thus "q \<in> \<Union>\<F>"
      using w by blast
  qed
  obtain \<F>' where F'sub: "\<F>' \<subseteq> \<F>"
    and F'cnt: "countable \<F>'"
    and coverF': "M \<subseteq> \<Union>\<F>'"
    by (rule countable_subcover_of_openin_cover[OF F_open F_cover])
  show ?thesis
  proof (cases "M = {}")
    case True
    define Ce :: "nat \<Rightarrow> ((real^2)^'n) set" where "Ce = (\<lambda>_. {})"
    show ?thesis
    proof (rule d3_chart_core_of_countable_chart_core_cover[where S = Ce])
      show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b}) :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. Ce i)"
      proof
        fix x
        assume xbad: "x \<in> (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b}) :: ((real^2)^'n) set)"
        have xV: "x \<in> V"
          using xbad by simp
        obtain \<omega> where omega_img: "\<omega> \<in> \<phi> ` {a<..<b}"
          and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
          and det0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
          and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
          and nsurj: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
          and ncrit: "\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)"
          using xbad unfolding D3BadXG_H0core_def by blast
        obtain t where tint: "t \<in> {a<..<b}" and omega_eq: "\<omega> = \<phi> t"
          using omega_img by blast
        have xsingle: "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> t}"
          unfolding D3BadXG_H0core_def
          using gz det0 cnz nsurj ncrit omega_eq by blast
        have "(x, t) \<in> M"
          unfolding M_def using xV tint xsingle by simp
        with True show "x \<in> (\<Union>i. Ce i)"
          by simp
      qed
    next
      fix i
      let ?charts = "\<lambda>(_::nat) (x::((real^2)^'n)). (x, 0::real^2)"
      let ?Crit = "\<lambda>(_::nat). ({} :: ((real^2)^'n) set)"
      let ?D = "\<lambda>(_::nat) (_::((real^2)^'n)).
        (0 :: ((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      show "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         Ce i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            (fst \<circ> charts j has_derivative blinfun_apply (D j x)) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
        unfolding Ce_def
        by (intro exI[of _ ?charts] exI[of _ ?Crit] exI[of _ ?D]) simp
    qed
  next
    case False
    have F'ne: "\<F>' \<noteq> {}"
      using coverF' False by auto
    obtain e :: "nat \<Rightarrow> (((real^2)^'n) \<times> real) set"
      where eimg: "\<Union>(range e) = \<Union>\<F>'"
        and erng: "\<And>n. e n \<in> \<F>'"
    proof -
      let ?e = "from_nat_into \<F>'"
      have eimg: "\<Union>(range ?e) = \<Union>\<F>'"
        by (metis F'cnt F'ne range_from_nat_into top1_countable_nonempty_eq_image_nat uncountable_def)
      have erng: "\<And>n. ?e n \<in> \<F>'"
        using F'ne by (simp add: from_nat_into)
      show ?thesis
        by (rule that[of ?e]) (auto simp: eimg intro: erng)
    qed
    have ex_pick: "\<forall>i. \<exists>x0 \<rho> \<epsilon> t0 C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       (\<forall>p\<in>e i. fst p \<in> cball x0 \<rho> \<and> snd p \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x t. x \<in> cball x0 \<rho> \<longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    proof
      fix i :: nat
      have "e i \<in> \<F>"
        using erng[of i] F'sub by blast
      thus "\<exists>x0 \<rho> \<epsilon> t0 C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       (\<forall>p\<in>e i. fst p \<in> cball x0 \<rho> \<and> snd p \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x t. x \<in> cball x0 \<rho> \<longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
        unfolding \<F>_def by blast
    qed
    obtain x0 :: "nat \<Rightarrow> ((real^2)^'n)"
      and \<rho> :: "nat \<Rightarrow> real"
      and \<epsilon> :: "nat \<Rightarrow> real"
      and t0 :: "nat \<Rightarrow> real"
      and C :: "nat \<Rightarrow> ((real^2)^'n) set"
      and charts :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      where pick: "\<And>i.
       (\<forall>p\<in>e i. fst p \<in> cball (x0 i) (\<rho> i) \<and>
          snd p \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i})
     \<and> (\<forall>x t. x \<in> cball (x0 i) (\<rho> i) \<longrightarrow>
          t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C i)
     \<and> C i \<subseteq> (\<Union>j. (fst \<circ> charts i j) ` (Crit i j))
     \<and> (\<forall>j x. x \<in> Crit i j \<longrightarrow>
          ((fst \<circ> charts i j) has_derivative (blinfun_apply (D i j x))) (at x within Crit i j))
     \<and> (\<forall>j x. x \<in> Crit i j \<longrightarrow> \<not> surj (blinfun_apply (D i j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts i j) ` (Crit i j)))"
      using ex_pick unfolding choice_iff by blast
    show ?thesis
    proof (rule d3_chart_core_of_countable_chart_core_cover[where S = C])
      show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b}) :: ((real^2)^'n) set)
          \<subseteq> (\<Union>i. C i)"
      proof
        fix x
        assume xbad: "x \<in> (V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b}) :: ((real^2)^'n) set)"
        have xV: "x \<in> V"
          using xbad by simp
        obtain \<omega> where omega_img: "\<omega> \<in> \<phi> ` {a<..<b}"
          and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
          and det0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
          and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
          and nsurj: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
          and ncrit: "\<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)"
          using xbad unfolding D3BadXG_H0core_def by blast
        obtain t where tint: "t \<in> {a<..<b}" and omega_eq: "\<omega> = \<phi> t"
          using omega_img by blast
        have xsingle: "x \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> t}"
          unfolding D3BadXG_H0core_def
          using gz det0 cnz nsurj ncrit omega_eq by blast
        have qM: "(x, t) \<in> M"
          unfolding M_def using xV tint xsingle by simp
        have "(x, t) \<in> \<Union>\<F>'"
          using coverF' qM by blast
        hence "(x, t) \<in> \<Union>(range e)"
          using eimg by simp
        then obtain i where qi: "(x, t) \<in> e i"
          by blast
        have xcb: "x \<in> cball (x0 i) (\<rho> i)"
          and tint_i: "t \<in> {t0 i - \<epsilon> i<..<t0 i + \<epsilon> i}"
          using pick[of i] qi by force+
        have gz_t: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0"
          using gz omega_eq by simp
        have "x \<in> C i"
          using pick[of i] xcb tint_i gz_t by blast
        thus "x \<in> (\<Union>i. C i)"
          by blast
      qed
    next
      fix i
      show "\<exists>(charts' :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit' :: nat \<Rightarrow> ((real^2)^'n) set)
            (D' :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         C i \<subseteq> (\<Union>j. (fst \<circ> charts' j) ` Crit' j) \<and>
         (\<forall>j x. x \<in> Crit' j \<longrightarrow>
            (fst \<circ> charts' j has_derivative blinfun_apply (D' j x)) (at x within Crit' j)) \<and>
         (\<forall>j x. x \<in> Crit' j \<longrightarrow> \<not> surj (blinfun_apply (D' j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts' j) ` Crit' j))"
        by (intro exI[of _ "charts i"] exI[of _ "Crit i"] exI[of _ "D i"])
           (use pick[of i] in blast)
    qed
  qed
qed

lemma local_zero_cut_chart_core_data:
  fixes B :: "((real^2)^'n::finite) set"
    and x0 r :: "(real^2)^'n"
    and f :: "((real^2)^'n) \<Rightarrow> real"
    and L :: "((real^2)^'n) \<Rightarrow> ((real^2)^'n) \<Rightarrow> real"
  assumes openB: "open B" and x0B: "x0 \<in> B"
    and fcont: "continuous_on B f"
    and fx0: "f x0 = 0"
    and deriv: "\<And>x. x \<in> B \<Longrightarrow> (f has_derivative L x) (at x)"
    and Lcont: "continuous_on B (\<lambda>x. L x r)"
    and rnz0: "L x0 r \<noteq> 0"
  shows "\<exists>\<rho> C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       0 < \<rho>
     \<and> C = cball x0 \<rho> \<inter> {x. f x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball x0 \<rho> \<subseteq> B
     \<and> x0 \<in> C
     \<and> (\<forall>x\<in>C. L x r \<noteq> 0)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  define U where "U = B \<inter> {x. L x r \<noteq> 0}"
  have openU: "open U"
  proof -
    have openNZ: "open (UNIV - {0::real})"
      by (simp add: open_Diff)
    have "open (B \<inter> (\<lambda>x. L x r) -` (UNIV - {0}))"
      by (rule continuous_open_preimage[OF Lcont openB openNZ])
    also have "B \<inter> (\<lambda>x. L x r) -` (UNIV - {0}) = U"
      unfolding U_def by auto
    finally show ?thesis .
  qed
  have x0U: "x0 \<in> U"
    unfolding U_def using x0B rnz0 by simp
  obtain e where epos: "0 < e" and eball: "ball x0 e \<subseteq> U"
    using openU x0U open_contains_ball by blast
  define \<rho> where "\<rho> = e / 2"
  have rhopos: "0 < \<rho>"
    unfolding \<rho>_def using epos by simp
  have rho_lt_e: "\<rho> < e"
    unfolding \<rho>_def using epos by simp
  define C where "C = cball x0 \<rho> \<inter> {x. f x = 0}"
  have cball_sub_U: "cball x0 \<rho> \<subseteq> U"
  proof
    fix x
    assume xcb: "x \<in> cball x0 \<rho>"
    have "dist x x0 \<le> \<rho>"
      using xcb by (simp add: dist_commute)
    hence "dist x x0 < e"
      using rho_lt_e by linarith
    hence "x \<in> ball x0 e"
      by (simp add: dist_commute)
    thus "x \<in> U"
      using eball by blast
  qed
  have cball_sub_B: "cball x0 \<rho> \<subseteq> B"
    using cball_sub_U unfolding U_def by blast
  have fcont_cball: "continuous_on (cball x0 \<rho>) f"
    by (rule continuous_on_subset[OF fcont cball_sub_B])
  have closedC: "closed C"
  proof -
    have "closed (f -` {0} \<inter> cball x0 \<rho>)"
      by (rule closed_vimage_Int[OF closed_singleton fcont_cball closed_cball])
    thus ?thesis
      unfolding C_def vimage_def by (simp add: Int_commute)
  qed
  have CsubB: "C \<subseteq> B"
    using cball_sub_B unfolding C_def by blast
  have x0C: "x0 \<in> C"
    unfolding C_def using rhopos fx0 by simp
  have rnzC: "\<And>x. x \<in> C \<Longrightarrow> L x r \<noteq> 0"
    using cball_sub_U unfolding C_def U_def by blast
  have data:
    "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
       (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
       (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
       (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  proof (rule chart_core_data_of_functional_cuts
      [of C "\<lambda>_::nat. C" "\<lambda>_. f" "\<lambda>_. L" "\<lambda>_ _. r"])
    show "C \<subseteq> (\<Union>i::nat. C)"
      by blast
    show "\<And>i::nat. closed C"
      by (rule closedC)
    show "\<And>i y. y \<in> C \<Longrightarrow> f y = 0"
      unfolding C_def by simp
    show "\<And>i x. x \<in> C \<Longrightarrow> (f has_derivative L x) (at x)"
      using CsubB deriv by blast
    show "\<And>i x. x \<in> C \<Longrightarrow> L x r \<noteq> 0"
      by (rule rnzC)
  qed
  then obtain charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
    and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
    and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where core:
       "C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i)) \<and>
       (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x))) \<and>
       (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by blast
  show ?thesis
    by (intro exI[of _ \<rho>] exI[of _ C] exI[of _ charts] exI[of _ Crit] exI[of _ D])
       (use rhopos C_def closedC CsubB cball_sub_B x0C rnzC core in blast)
qed

lemma arc_schur_zero_cut_chart_core_data:
  fixes B :: "((real^2)^'n::finite) set"
    and x0 r :: "(real^2)^'n"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
  assumes openB: "open B" and x0B: "x0 \<in> B"
    and omega_cont: "continuous_on B (\<lambda>x. \<phi> (\<tau> x))"
    and Domega_cont: "continuous_on B (\<lambda>x. D\<phi> (\<tau> x))"
    and taudiff: "\<And>x. x \<in> B \<Longrightarrow> \<tau> differentiable (at x)"
    and zero1: "\<And>x. x \<in> B \<Longrightarrow>
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
    and phid: "\<And>x. x \<in> B \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> (\<tau> x)) (at (\<tau> x))"
    and trans: "\<And>x. x \<in> B \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0"
    and zero2x0: "vec_nth
      (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> (\<tau> x0))) 2 = 0"
    and rnz0: "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x0 r \<noteq> 0"
  shows "\<exists>\<rho> C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       0 < \<rho>
     \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball x0 \<rho> \<subseteq> B
     \<and> x0 \<in> C
     \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  have fcont: "continuous_on B (gradU2_graph \<omega>0 \<omega>s \<phi> \<tau>)"
    by (rule continuous_on_gradU2_graph[OF openB taudiff zero1 phid trans])
  have deriv: "\<And>x. x \<in> B \<Longrightarrow>
      (gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> has_derivative arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x) (at x)"
  proof -
    fix x assume xB: "x \<in> B"
    show "(gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> has_derivative arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x) (at x)"
      by (rule gradU2_graph_has_derivative_schur
          [where B = B and x = x and \<tau> = \<tau> and \<phi> = \<phi> and D\<phi> = D\<phi>])
         (use openB xB taudiff[OF xB] zero1 phid[OF xB] trans[OF xB] in auto)
  qed
  have Lcont: "continuous_on B (\<lambda>x. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r)"
    by (rule continuous_on_arc_schur_L_fixed[OF omega_cont Domega_cont trans])
  have fx0: "gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x0 = 0"
    unfolding gradU2_graph_def using zero2x0 by simp
  show ?thesis
    by (rule local_zero_cut_chart_core_data
        [OF openB x0B fcont fx0 deriv Lcont rnz0])
qed

section \<open>Shrinking to where the transversality persists\<close>

text \<open>The transversality scalar \<open>T1(x) := HessU(x,\<phi>(\<tau> x))\<bullet>D\<phi>(\<tau> x)\<close> is
  continuous in \<open>x\<close> (composition of @{thm continuous_on_HessU_dip_joint},
  \<open>\<tau>\<close>'s continuity, and \<open>\<phi>\<close>/\<open>D\<phi>\<close>'s continuity), so its being nonzero at \<open>x0\<close>
  (the ORIGINAL hypothesis of @{thm gradU1_arc_local_graph}) persists on a
  SHRUNK open neighborhood -- the standard continuity-shrink used throughout
  this project.\<close>

lemma transversality_shrink:
  fixes x0 :: "(real^2)^'n::finite" and t0 :: real
    and \<phi> :: "real \<Rightarrow> real^2" and D\<phi> :: "real \<Rightarrow> real^2"
    and \<omega>0 \<omega>s :: "real^2" and a b \<epsilon> :: real
    and B :: "((real^2)^'n) set" and \<tau> :: "(real^2)^'n \<Rightarrow> real"
  assumes openB: "open B" and x0B: "x0 \<in> B"
    and taux0: "\<tau> x0 = t0"
    and taucont: "continuous_on B \<tau>"
    and taurange: "\<And>x. x \<in> B \<Longrightarrow> \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
    and eps_sub_ab: "{t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}"
    and phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    and trans: "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi> t0) 1 \<noteq> 0"
  obtains B' where "open B'" "x0 \<in> B'" "B' \<subseteq> B"
    "\<And>x. x \<in> B' \<Longrightarrow> vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0"
proof -
  have phicont: "continuous_on {a<..<b} \<phi>"
  proof (rule continuous_at_imp_continuous_on, intro ballI)
    fix t assume "t \<in> {a<..<b}"
    thus "continuous (at t) \<phi>"
      using phid[of t] has_vector_derivative_continuous by auto
  qed

  define T1field :: "(real^2)^'n \<Rightarrow> real"
    where "T1field = (\<lambda>x. vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1)"

  have tauB_ab: "\<And>x. x \<in> B \<Longrightarrow> a < \<tau> x \<and> \<tau> x < b"
  proof -
    fix x assume xB: "x \<in> B"
    have "\<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}" using taurange[OF xB] .
    hence "\<tau> x \<in> {a<..<b}" using eps_sub_ab by blast
    thus "a < \<tau> x \<and> \<tau> x < b" by simp
  qed

  have phi_taucont: "continuous_on B (\<lambda>x. \<phi> (\<tau> x))"
    by (rule continuous_on_compose2[OF phicont taucont])
       (auto simp: tauB_ab)
  have Dphi_taucont: "continuous_on B (\<lambda>x. D\<phi> (\<tau> x))"
    by (rule continuous_on_compose2[OF phic taucont])
       (auto simp: tauB_ab)

  have pairB: "continuous_on B (\<lambda>x. (x, \<phi> (\<tau> x)))"
    by (rule continuous_on_Pair[OF continuous_on_id phi_taucont])

  have HessB: "continuous_on B (\<lambda>x. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)))"
    using continuous_on_compose2[OF continuous_on_HessU_dip_joint pairB subset_UNIV]
    by (simp add: o_def)

  have matvecB: "continuous_on B (\<lambda>x. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x))"
    using continuous_on_matvec[OF HessB Dphi_taucont] .

  have vec_nth_cont: "continuous_on UNIV (\<lambda>v::real^2. vec_nth v 1)"
    using bounded_linear.continuous_on[OF bounded_linear_vec_nth continuous_on_id] .
  have T1cont: "continuous_on B T1field"
    unfolding T1field_def
    using continuous_on_compose2[OF vec_nth_cont matvecB subset_UNIV] .

  have T1x0: "T1field x0 \<noteq> 0"
    unfolding T1field_def using taux0 trans by simp

  define B' where "B' = B \<inter> {x. T1field x \<noteq> 0}"

  have openB': "open B'"
  proof -
    have openUD: "open (UNIV - {0::real})"
      by (simp add: open_Diff)
    have "open (B \<inter> T1field -` (UNIV - {0}))"
      by (rule continuous_open_preimage[OF T1cont openB openUD])
    also have "B \<inter> T1field -` (UNIV - {0}) = B'"
      unfolding B'_def by auto
    finally show ?thesis .
  qed

  have x0B': "x0 \<in> B'" unfolding B'_def using x0B T1x0 by simp
  have subB: "B' \<subseteq> B" unfolding B'_def by simp
  have nz: "\<And>x. x \<in> B' \<Longrightarrow> T1field x \<noteq> 0" unfolding B'_def by simp

  show ?thesis
    using that[OF openB' x0B' subB] nz unfolding T1field_def by blast
qed

lemma arc_schur_point_zero_cut_chart_core_data:
  fixes x0 r :: "(real^2)^'n::finite"
    and t0 a b :: real
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
    and \<omega>0 \<omega>s :: "real^2"
  assumes phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    and t0ab: "a < t0" "t0 < b"
    and crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) = 0"
    and trans: "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi> t0) 1 \<noteq> 0"
    and schur_nz0: "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. t0) x0 r \<noteq> 0"
  shows "\<exists>B \<epsilon> \<tau> \<rho> C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       open B
     \<and> x0 \<in> B
     \<and> 0 < \<epsilon>
     \<and> {t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}
     \<and> \<tau> x0 = t0
     \<and> (\<forall>x\<in>B. \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x\<in>B. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0)
     \<and> (\<forall>x\<in>B. \<forall>t\<in>{t0-\<epsilon><..<t0+\<epsilon>}.
          vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<longrightarrow> t = \<tau> x)
     \<and> (\<forall>x\<in>B.
          vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0)
     \<and> 0 < \<rho>
     \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball x0 \<rho> \<subseteq> B
     \<and> x0 \<in> C
     \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  have crit1: "vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0)) 1 = 0"
    using crit by simp
  obtain B0 \<epsilon> \<tau> where openB0: "open B0"
    and x0B0: "x0 \<in> B0"
    and epspos: "0 < \<epsilon>"
    and eps_sub: "{t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}"
    and taux0: "\<tau> x0 = t0"
    and taurange0: "\<And>x. x \<in> B0 \<Longrightarrow> \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
    and zero10: "\<And>x. x \<in> B0 \<Longrightarrow>
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
    and taudiff0: "\<And>x. x \<in> B0 \<Longrightarrow> \<tau> differentiable (at x)"
    and taucont0: "continuous_on B0 \<tau>"
    and uniq0: "\<And>x t. x \<in> B0 \<Longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<Longrightarrow>
        vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<Longrightarrow> t = \<tau> x"
  proof (rule gradU1_arc_local_graph[OF phid phic t0ab crit1 trans])
    fix B0 \<epsilon> \<tau>
    assume openB0': "open B0"
      and x0B0': "x0 \<in> B0"
      and epspos': "0 < \<epsilon>"
      and eps_sub': "{t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}"
      and taux0': "\<tau> x0 = t0"
      and taurange0': "\<And>x. x \<in> B0 \<Longrightarrow> \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
      and zero10': "\<And>x. x \<in> B0 \<Longrightarrow>
        vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
      and taudiff0': "\<And>x. x \<in> B0 \<Longrightarrow> \<tau> differentiable (at x)"
      and taucont0': "continuous_on B0 \<tau>"
      and uniq0': "\<And>x t. x \<in> B0 \<Longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<Longrightarrow>
        vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<Longrightarrow> t = \<tau> x"
    show thesis
      by (rule that[OF openB0' x0B0' epspos' eps_sub' taux0' taurange0'
            zero10' taudiff0' taucont0' uniq0'])
  qed

  obtain B where openB: "open B"
    and x0B: "x0 \<in> B"
    and Bsub: "B \<subseteq> B0"
    and transB: "\<And>x. x \<in> B \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0"
  proof (rule transversality_shrink
      [OF openB0 x0B0 taux0 taucont0 taurange0 eps_sub phid phic trans])
    fix B
    assume openB': "open B"
      and x0B': "x0 \<in> B"
      and Bsub': "B \<subseteq> B0"
      and transB': "\<And>x. x \<in> B \<Longrightarrow>
        vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0"
    show thesis
      by (rule that[OF openB' x0B' Bsub' transB'])
  qed

  have taurange: "\<And>x. x \<in> B \<Longrightarrow> \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
    using Bsub taurange0 by blast
  have zero1: "\<And>x. x \<in> B \<Longrightarrow>
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0"
    using Bsub zero10 by blast
  have taudiff: "\<And>x. x \<in> B \<Longrightarrow> \<tau> differentiable (at x)"
    using Bsub taudiff0 by blast
  have uniq: "\<And>x t. x \<in> B \<Longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<Longrightarrow>
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<Longrightarrow> t = \<tau> x"
    using Bsub uniq0 by blast
  have taucont: "continuous_on B \<tau>"
    by (rule continuous_on_subset[OF taucont0 Bsub])

  have phicont: "continuous_on {a<..<b} \<phi>"
  proof (rule continuous_at_imp_continuous_on, intro ballI)
    fix t
    assume "t \<in> {a<..<b}"
    thus "continuous (at t) \<phi>"
      using phid[of t] has_vector_derivative_continuous by auto
  qed
  have tauB_ab: "\<And>x. x \<in> B \<Longrightarrow> a < \<tau> x \<and> \<tau> x < b"
  proof -
    fix x assume xB: "x \<in> B"
    have "\<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
      by (rule taurange[OF xB])
    hence "\<tau> x \<in> {a<..<b}"
      using eps_sub by blast
    thus "a < \<tau> x \<and> \<tau> x < b"
      by simp
  qed
  have omega_cont: "continuous_on B (\<lambda>x. \<phi> (\<tau> x))"
    by (rule continuous_on_compose2[OF phicont taucont])
       (auto simp: tauB_ab)
  have Domega_cont: "continuous_on B (\<lambda>x. D\<phi> (\<tau> x))"
    by (rule continuous_on_compose2[OF phic taucont])
       (auto simp: tauB_ab)
  have phidB: "\<And>x. x \<in> B \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> (\<tau> x)) (at (\<tau> x))"
    using phid tauB_ab by blast
  have zero2x0: "vec_nth
      (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> (\<tau> x0))) 2 = 0"
    using crit taux0 by simp
  have rnz0: "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x0 r \<noteq> 0"
    using schur_nz0 taux0 unfolding arc_schur_L_def by simp

  obtain \<rho> C
      and charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where core:
       "0 < \<rho>
     \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball x0 \<rho> \<subseteq> B
     \<and> x0 \<in> C
     \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  proof -
    have core_ex: "\<exists>\<rho> C
        (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
        (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
        (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         0 < \<rho>
       \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
       \<and> closed C
       \<and> C \<subseteq> B
       \<and> cball x0 \<rho> \<subseteq> B
       \<and> x0 \<in> C
       \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
       \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
       \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
       \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
       \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
      by (rule arc_schur_zero_cut_chart_core_data[
          OF openB x0B omega_cont Domega_cont taudiff zero1 phidB transB zero2x0 rnz0])
    then show thesis
    proof (elim exE)
      fix \<rho> C
        and charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
        and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
        and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      assume core': "0 < \<rho>
       \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
       \<and> closed C
       \<and> C \<subseteq> B
       \<and> cball x0 \<rho> \<subseteq> B
       \<and> x0 \<in> C
       \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
       \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
       \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
       \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
       \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
      show thesis
        by (rule that[OF core'])
    qed
  qed

  show ?thesis
  by (rule exI[where x = B,
        OF exI[where x = \<epsilon>,
        OF exI[where x = \<tau>,
        OF exI[where x = \<rho>,
        OF exI[where x = C,
        OF exI[where x = charts,
        OF exI[where x = Crit,
        OF exI[where x = D]]]]]]]];
      use openB x0B epspos eps_sub taux0 taurange zero1 uniq transB core
      in auto)
qed

lemma arc_schur_point_local_critical_cover_chart_core_data:
  fixes x0 r :: "(real^2)^'n::finite"
    and t0 a b :: real
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
    and \<omega>0 \<omega>s :: "real^2"
  assumes phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    and t0ab: "a < t0" "t0 < b"
    and crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) = 0"
    and trans: "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 (\<phi> t0) *v D\<phi> t0) 1 \<noteq> 0"
    and schur_nz0: "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. t0) x0 r \<noteq> 0"
  shows "\<exists>B \<epsilon> \<tau> \<rho> C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       open B
     \<and> x0 \<in> B
     \<and> 0 < \<epsilon>
     \<and> {t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}
     \<and> \<tau> x0 = t0
     \<and> (\<forall>x\<in>B. \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x\<in>B. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0)
     \<and> (\<forall>x\<in>B. \<forall>t\<in>{t0-\<epsilon><..<t0+\<epsilon>}.
          vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<longrightarrow> t = \<tau> x)
     \<and> (\<forall>x\<in>B.
          vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0)
     \<and> 0 < \<rho>
     \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball x0 \<rho> \<subseteq> B
     \<and> x0 \<in> C
     \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
     \<and> (\<forall>x t. x \<in> cball x0 \<rho> \<longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
proof -
  obtain B \<epsilon> \<tau> \<rho> C
      and charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where data:
       "open B
     \<and> x0 \<in> B
     \<and> 0 < \<epsilon>
     \<and> {t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}
     \<and> \<tau> x0 = t0
     \<and> (\<forall>x\<in>B. \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x\<in>B. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0)
     \<and> (\<forall>x\<in>B. \<forall>t\<in>{t0-\<epsilon><..<t0+\<epsilon>}.
          vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<longrightarrow> t = \<tau> x)
     \<and> (\<forall>x\<in>B.
          vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0)
     \<and> 0 < \<rho>
     \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball x0 \<rho> \<subseteq> B
     \<and> x0 \<in> C
     \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
  proof -
    have data_ex: "\<exists>B \<epsilon> \<tau> \<rho> C
        (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
        (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
        (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         open B
       \<and> x0 \<in> B
       \<and> 0 < \<epsilon>
       \<and> {t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}
       \<and> \<tau> x0 = t0
       \<and> (\<forall>x\<in>B. \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>})
       \<and> (\<forall>x\<in>B. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0)
       \<and> (\<forall>x\<in>B. \<forall>t\<in>{t0-\<epsilon><..<t0+\<epsilon>}.
            vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<longrightarrow> t = \<tau> x)
       \<and> (\<forall>x\<in>B.
            vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0)
       \<and> 0 < \<rho>
       \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
       \<and> closed C
       \<and> C \<subseteq> B
       \<and> cball x0 \<rho> \<subseteq> B
       \<and> x0 \<in> C
       \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
       \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
       \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
       \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
       \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
      by (rule arc_schur_point_zero_cut_chart_core_data[
          OF phid phic t0ab crit trans schur_nz0])
    then show thesis
    proof (elim exE)
      fix B \<epsilon> \<tau> \<rho> C
        and charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
        and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
        and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
      assume data': "open B
       \<and> x0 \<in> B
       \<and> 0 < \<epsilon>
       \<and> {t0-\<epsilon><..<t0+\<epsilon>} \<subseteq> {a<..<b}
       \<and> \<tau> x0 = t0
       \<and> (\<forall>x\<in>B. \<tau> x \<in> {t0-\<epsilon><..<t0+\<epsilon>})
       \<and> (\<forall>x\<in>B. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0)
       \<and> (\<forall>x\<in>B. \<forall>t\<in>{t0-\<epsilon><..<t0+\<epsilon>}.
            vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<longrightarrow> t = \<tau> x)
       \<and> (\<forall>x\<in>B.
            vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0)
       \<and> 0 < \<rho>
       \<and> C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
       \<and> closed C
       \<and> C \<subseteq> B
       \<and> cball x0 \<rho> \<subseteq> B
       \<and> x0 \<in> C
       \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
       \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
       \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
            ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
       \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
       \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
      show thesis
        by (rule that[OF data'])
    qed
  qed

  have cball_sub: "cball x0 \<rho> \<subseteq> B"
    using data by simp
  have C_def: "C = cball x0 \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}"
    using data by simp
  have uniq: "\<And>x t. x \<in> B \<Longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<Longrightarrow>
      vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<Longrightarrow> t = \<tau> x"
    using data by blast
  have local_cover: "\<And>x t. x \<in> cball x0 \<rho> \<Longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<Longrightarrow>
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<Longrightarrow> x \<in> C"
  proof -
    fix x t
    assume xcb: "x \<in> cball x0 \<rho>"
      and tint: "t \<in> {t0-\<epsilon><..<t0+\<epsilon>}"
      and gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0"
    have xB: "x \<in> B"
      using cball_sub xcb by blast
    have t_eq: "t = \<tau> x"
      by (rule uniq[OF xB tint]) (use gz in simp)
    have "gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0"
      unfolding gradU2_graph_def using gz t_eq by simp
    thus "x \<in> C"
      unfolding C_def using xcb by simp
  qed

  show ?thesis
  by (rule exI[where x = B,
        OF exI[where x = \<epsilon>,
        OF exI[where x = \<tau>,
        OF exI[where x = \<rho>,
        OF exI[where x = C,
        OF exI[where x = charts,
        OF exI[where x = Crit,
        OF exI[where x = D]]]]]]]];
      use data local_cover in auto)
qed

lemma arc_schur_point_open_H0core_cball_patch:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
    and M :: "(((real^2)^'n) \<times> real) set"
    and q :: "((real^2)^'n) \<times> real"
    and r :: "(real^2)^'n"
    and a b :: real
    and \<omega>0 \<omega>s :: "real^2"
  defines "M \<equiv> {q :: ((real^2)^'n) \<times> real.
      fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
      fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}}"
  assumes qM: "q \<in> M"
    and phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    and trans: "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    and schur_nz0: "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
  shows "\<exists>S x0 \<rho> \<epsilon> t0 C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       openin (top_of_set M) S
     \<and> q \<in> S
     \<and> (\<forall>p\<in>S. fst p \<in> cball x0 \<rho> \<and> snd p \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x t. x \<in> cball x0 \<rho> \<longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
proof -
  have t0ab: "a < snd q" "snd q < b"
    using qM unfolding M_def by auto
  have xcore: "fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}"
    using qM unfolding M_def by simp
  have crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q)) = 0"
    using xcore unfolding D3BadXG_H0core_def by blast
  have local_ex: "\<exists>B \<epsilon> \<tau> \<rho> C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       open B
     \<and> fst q \<in> B
     \<and> 0 < \<epsilon>
     \<and> {snd q-\<epsilon><..<snd q+\<epsilon>} \<subseteq> {a<..<b}
     \<and> \<tau> (fst q) = snd q
     \<and> (\<forall>x\<in>B. \<tau> x \<in> {snd q-\<epsilon><..<snd q+\<epsilon>})
     \<and> (\<forall>x\<in>B. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0)
     \<and> (\<forall>x\<in>B. \<forall>t\<in>{snd q-\<epsilon><..<snd q+\<epsilon>}.
          vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<longrightarrow> t = \<tau> x)
     \<and> (\<forall>x\<in>B.
          vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0)
     \<and> 0 < \<rho>
     \<and> C = cball (fst q) \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball (fst q) \<rho> \<subseteq> B
     \<and> fst q \<in> C
     \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
     \<and> (\<forall>x t. x \<in> cball (fst q) \<rho> \<longrightarrow> t \<in> {snd q-\<epsilon><..<snd q+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by (rule arc_schur_point_local_critical_cover_chart_core_data
        [OF phid phic t0ab crit trans schur_nz0])
  then obtain B \<epsilon> \<tau> \<rho> C
      and charts :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2))"
      and Crit :: "nat \<Rightarrow> ((real^2)^'n) set"
      and D :: "nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
    where data:
       "open B
     \<and> fst q \<in> B
     \<and> 0 < \<epsilon>
     \<and> {snd q-\<epsilon><..<snd q+\<epsilon>} \<subseteq> {a<..<b}
     \<and> \<tau> (fst q) = snd q
     \<and> (\<forall>x\<in>B. \<tau> x \<in> {snd q-\<epsilon><..<snd q+\<epsilon>})
     \<and> (\<forall>x\<in>B. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x))) 1 = 0)
     \<and> (\<forall>x\<in>B. \<forall>t\<in>{snd q-\<epsilon><..<snd q+\<epsilon>}.
          vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t)) 1 = 0 \<longrightarrow> t = \<tau> x)
     \<and> (\<forall>x\<in>B.
          vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> (\<tau> x)) *v D\<phi> (\<tau> x)) 1 \<noteq> 0)
     \<and> 0 < \<rho>
     \<and> C = cball (fst q) \<rho> \<inter> {x. gradU2_graph \<omega>0 \<omega>s \<phi> \<tau> x = 0}
     \<and> closed C
     \<and> C \<subseteq> B
     \<and> cball (fst q) \<rho> \<subseteq> B
     \<and> fst q \<in> C
     \<and> (\<forall>x\<in>C. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> \<tau> x r \<noteq> 0)
     \<and> (\<forall>x t. x \<in> cball (fst q) \<rho> \<longrightarrow> t \<in> {snd q-\<epsilon><..<snd q+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>i. (fst \<circ> charts i) ` (Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow>
          ((fst \<circ> charts i) has_derivative (blinfun_apply (D i x))) (at x within Crit i))
     \<and> (\<forall>i x. x \<in> Crit i \<longrightarrow> \<not> surj (blinfun_apply (D i x)))
     \<and> (\<forall>i. closed ((fst \<circ> charts i) ` (Crit i)))"
    by presburger
    
  define A where "A = ball (fst q) \<rho> \<times> {snd q-\<epsilon><..<snd q+\<epsilon>}"
  define S where "S = M \<inter> A"
  have openA: "open A"
    unfolding A_def by (intro open_Times) simp_all
  have openS: "openin (top_of_set M) S"
    unfolding S_def openin_open_eq
    using openA by blast
  have qS: "q \<in> S"
    unfolding S_def A_def
    using qM data by (cases q) auto
  have bounds: "\<forall>p\<in>S. fst p \<in> cball (fst q) \<rho> \<and> snd p \<in> {snd q-\<epsilon><..<snd q+\<epsilon>}"
    unfolding S_def A_def by auto
    show ?thesis
    by (rule exI[where x = S,
          OF exI[where x = "fst q",
          OF exI[where x = \<rho>,
          OF exI[where x = \<epsilon>,
          OF exI[where x = "snd q",
          OF exI[where x = C,
          OF exI[where x = charts,
          OF exI[where x = Crit,
          OF exI[where x = D]]]]]]]]];
        use openS qS bounds data in blast)
qed

lemma d3_chart_core_of_pointwise_arc_schur_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
    and M :: "(((real^2)^'n) \<times> real) set"
    and a b :: real
    and \<omega>0 \<omega>s :: "real^2"
  defines "M \<equiv> {q :: ((real^2)^'n) \<times> real.
      fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
      fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}}"
  assumes phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    and trans: "\<And>q. q \<in> M \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    and schur: "\<And>q. q \<in> M \<Longrightarrow>
      \<exists>r. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a<..<b})"
proof (rule d3_chart_core_of_Lindelof_H0core_cball_patches)
  fix q
  assume qMset: "q \<in> {q :: ((real^2)^'n) \<times> real.
      fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
      fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}}"
  have qM: "q \<in> M"
    using qMset unfolding M_def by simp
  obtain r where schurq:
      "arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
    using schur[OF qM] by blast
  show "\<exists>S x0 \<rho> \<epsilon> t0 C
      (charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       openin (top_of_set {q :: ((real^2)^'n) \<times> real.
          fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
          fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}}) S
     \<and> q \<in> S
     \<and> (\<forall>p\<in>S. fst p \<in> cball x0 \<rho> \<and> snd p \<in> {t0-\<epsilon><..<t0+\<epsilon>})
     \<and> (\<forall>x t. x \<in> cball x0 \<rho> \<longrightarrow> t \<in> {t0-\<epsilon><..<t0+\<epsilon>} \<longrightarrow>
          gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (\<phi> t) = 0 \<longrightarrow> x \<in> C)
     \<and> C \<subseteq> (\<Union>j. (fst \<circ> charts j) ` (Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` (Crit j)))"
    by (rule arc_schur_point_open_H0core_cball_patch
        [OF qMset phid phic trans[OF qM] schurq])
qed

lemma D3BadXG_H0core_UN:
  fixes arc :: "'i \<Rightarrow> (real^2) set"
  shows "D3BadXG_H0core \<omega>0 \<omega>s (\<Union>i\<in>I. arc i)
      = (\<Union>i\<in>I. (D3BadXG_H0core \<omega>0 \<omega>s (arc i) :: ((real^2)^'n::finite) set))"
  unfolding D3BadXG_H0core_def by blast

lemma D3BadXG_H0core_arc_split:
  fixes \<phi> :: "real \<Rightarrow> real^2" and a b :: real
  assumes ab: "a \<le> b"
  shows "D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a..b})
       = (D3BadXG_H0core \<omega>0 \<omega>s {\<phi> a} :: ((real^2)^'n::finite) set)
         \<union> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b})
         \<union> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> b}"
proof -
  have "\<phi> ` {a..b} = \<phi> ` ({a} \<union> {a<..<b} \<union> {b})"
    using ab by fastforce
  also have "\<dots> = {\<phi> a} \<union> \<phi> ` {a<..<b} \<union> {\<phi> b}"
    by (simp add: image_Un)
  finally have eq: "\<phi> ` {a..b} = {\<phi> a} \<union> \<phi> ` {a<..<b} \<union> {\<phi> b}" .
  show ?thesis
    unfolding eq D3BadXG_H0core_def by auto
qed

lemma chart_core_data_empty:
  shows "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n::finite) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
      (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
      (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
       ({} :: ((real^2)^'n) set) \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j)
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow>
          ((fst \<circ> charts j) has_derivative (blinfun_apply (D j x))) (at x within Crit j))
     \<and> (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x)))
     \<and> (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
proof -
  let ?charts = "\<lambda>(_::nat) (x::((real^2)^'n)). (x, 0::real^2)"
  let ?Crit = "\<lambda>(_::nat). ({} :: ((real^2)^'n) set)"
  let ?D = "\<lambda>(_::nat) (_::((real^2)^'n)).
      (0 :: ((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))"
  show ?thesis
    by (intro exI[of _ ?charts] exI[of _ ?Crit] exI[of _ ?D]) simp
qed

lemma d3_chart_core_of_closed_arc_split:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> :: "real \<Rightarrow> real^2"
  assumes ab: "a \<le> b"
    and left: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> a}"
    and middle: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a<..<b})"
    and right: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> b}"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a..b})"
proof -
  define S :: "nat \<Rightarrow> ((real^2)^'n) set" where
    "S = (\<lambda>i. if i = 0 then V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> a}
              else if i = 1 then V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b})
              else if i = 2 then V \<inter> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> b}
              else {})"
  show ?thesis
  proof (rule d3_chart_core_of_countable_chart_core_cover[where S = S])
    have arc_eq: "D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a..b})
       = (D3BadXG_H0core \<omega>0 \<omega>s {\<phi> a} :: ((real^2)^'n) set)
         \<union> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a<..<b})
         \<union> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> b}"
      by (rule D3BadXG_H0core_arc_split[OF ab])
    show "(V \<inter> D3BadXG_H0core \<omega>0 \<omega>s (\<phi> ` {a..b}) :: ((real^2)^'n) set)
        \<subseteq> (\<Union>i. S i)"
      unfolding S_def arc_eq by auto
  next
    fix i :: nat
    show "\<exists>(charts :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<times> (real^2)))
            (Crit :: nat \<Rightarrow> ((real^2)^'n) set)
            (D :: nat \<Rightarrow> ((real^2)^'n) \<Rightarrow> (((real^2)^'n) \<Rightarrow>\<^sub>L ((real^2)^'n))).
         S i \<subseteq> (\<Union>j. (fst \<circ> charts j) ` Crit j) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow>
            (fst \<circ> charts j has_derivative blinfun_apply (D j x)) (at x within Crit j)) \<and>
         (\<forall>j x. x \<in> Crit j \<longrightarrow> \<not> surj (blinfun_apply (D j x))) \<and>
         (\<forall>j. closed ((fst \<circ> charts j) ` Crit j))"
    proof (cases "i = 0")
      case True
      show ?thesis
        using left unfolding S_def True d3_detHess_arc_chart_core_def by simp
    next
      case i0: False
      show ?thesis
      proof (cases "i = 1")
        case True
        show ?thesis
          using middle i0 unfolding S_def True d3_detHess_arc_chart_core_def by simp
      next
        case i1: False
        show ?thesis
        proof (cases "i = 2")
          case True
          show ?thesis
            using right i0 i1 unfolding S_def True d3_detHess_arc_chart_core_def by simp
        next
          case i2: False
          have "S i = ({} :: ((real^2)^'n) set)"
            unfolding S_def using i0 i1 i2 by simp
          thus ?thesis
            using chart_core_data_empty by simp
        qed
      qed
    qed
  qed
qed

lemma d3_chart_core_of_closed_arc_pointwise_arc_schur_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> D\<phi> :: "real \<Rightarrow> real^2"
    and M :: "(((real^2)^'n) \<times> real) set"
    and a b :: real
    and \<omega>0 \<omega>s :: "real^2"
  defines "M \<equiv> {q :: ((real^2)^'n) \<times> real.
      fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
      fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}}"
  assumes ab: "a \<le> b"
    and left: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> a}"
    and right: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> b}"
    and phid: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    and trans: "\<And>q. q \<in> M \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    and schur: "\<And>q. q \<in> M \<Longrightarrow>
      \<exists>r. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a..b})"
proof (rule d3_chart_core_of_closed_arc_split[OF ab left _ right])
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a<..<b})"
  proof (rule d3_chart_core_of_pointwise_arc_schur_patches)
    show "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
      by (rule phid)
  next
    show "continuous_on {a<..<b} D\<phi>"
      by (rule phic)
  next
    fix q
    assume qMset: "q \<in> {q :: ((real^2)^'n) \<times> real.
      fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
      fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}}"
    have qM: "q \<in> M"
      using qMset unfolding M_def by simp
    show "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
      by (rule trans[OF qM])
    show "\<exists>r. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
      by (rule schur[OF qM])
  qed
qed

lemma C1_closed_interval_open_derivative:
  fixes \<phi> :: "real \<Rightarrow> real^2"
  assumes c1: "\<phi> C1_differentiable_on {a..b}"
  obtains D\<phi> where
    "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    "continuous_on {a<..<b} D\<phi>"
proof -
  obtain D\<phi> where d:
      "\<And>t. t \<in> {a..b} \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and cont: "continuous_on {a..b} D\<phi>"
    using c1 unfolding C1_differentiable_on_def by blast
  have dopen: "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow>
      (\<phi> has_vector_derivative D\<phi> t) (at t)"
    using d by simp
  have open_subset: "{a<..<b} \<subseteq> {a..b}"
    by auto
  have contopen: "continuous_on {a<..<b} D\<phi>"
    by (rule continuous_on_subset[OF cont open_subset])
  show thesis
    by (rule that[OF dopen contopen])
qed

lemma d3_chart_core_of_closed_C1_arc_pointwise_arc_schur_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and \<phi> :: "real \<Rightarrow> real^2"
    and a b :: real
    and \<omega>0 \<omega>s :: "real^2"
  assumes ab: "a \<le> b"
    and c1: "\<phi> C1_differentiable_on {a..b}"
    and left: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> a}"
    and right: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> b}"
    and trans: "\<And>D\<phi> q.
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}} \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    and schur: "\<And>D\<phi> q.
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}} \<Longrightarrow>
      \<exists>r. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
  shows "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a..b})"
proof -
  obtain D\<phi> where phid:
      "\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)"
    and phic: "continuous_on {a<..<b} D\<phi>"
    using C1_closed_interval_open_derivative[OF c1] by blast
  show ?thesis
  proof (rule d3_chart_core_of_closed_arc_pointwise_arc_schur_patches[
        OF ab left right phid phic])
    fix q
    assume q: "q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}}"
    show "vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
      by (rule trans[OF phid phic q])
    show "\<exists>r. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
      by (rule schur[OF phid phic q])
  qed
qed

theorem d3_chart_core_all_of_analytic_arc_pointwise_arc_schur_patches:
  fixes V :: "((real^2)^'n::finite) set"
    and ctr \<omega>0 \<omega>s :: "real^2"
    and \<delta> :: real
  assumes left: "\<And>\<phi> a b.
      a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> a}"
    and right: "\<And>\<phi> a b.
      a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> b}"
    and trans: "\<And>\<phi> D\<phi> a b q.
      a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}} \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
    and schur: "\<And>\<phi> D\<phi> a b q.
      a \<le> b \<Longrightarrow> \<phi> C1_differentiable_on {a..b} \<Longrightarrow>
      \<phi> ` {a..b} \<subseteq> OmegaPF ctr \<delta> \<Longrightarrow>
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}} \<Longrightarrow>
      \<exists>r. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
  shows "d3_detHess_arc_chart_core_all V ctr \<delta> \<omega>0 \<omega>s"
  unfolding d3_detHess_arc_chart_core_all_def
proof (intro allI impI)
  fix \<gamma>
  assume arc: "analytic_arc \<gamma>"
    and gsub: "\<gamma> \<subseteq> OmegaPF ctr \<delta>"
  obtain a b \<phi> where ab: "a \<le> b"
    and c1: "\<phi> C1_differentiable_on {a..b}"
    and geq: "\<gamma> = \<phi> ` {a..b}"
    using arc unfolding analytic_arc_def by blast
  have gsub': "\<phi> ` {a..b} \<subseteq> OmegaPF ctr \<delta>"
    using gsub geq by simp
  have core: "d3_detHess_arc_chart_core V \<omega>0 \<omega>s (\<phi> ` {a..b})"
  proof (rule d3_chart_core_of_closed_C1_arc_pointwise_arc_schur_patches[
        OF ab c1])
    show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> a}"
      by (rule left[OF ab c1 gsub'])
    show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s {\<phi> b}"
      by (rule right[OF ab c1 gsub'])
    show "\<And>D\<phi> q.
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}} \<Longrightarrow>
      vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip
        (fst q) (\<phi> (snd q)) *v D\<phi> (snd q)) 1 \<noteq> 0"
      by (rule trans[OF ab c1 gsub'])
    show "\<And>D\<phi> q.
      (\<And>t. a < t \<Longrightarrow> t < b \<Longrightarrow> (\<phi> has_vector_derivative D\<phi> t) (at t)) \<Longrightarrow>
      continuous_on {a<..<b} D\<phi> \<Longrightarrow>
      q \<in> {q :: ((real^2)^'n) \<times> real.
        fst q \<in> V \<and> snd q \<in> {a<..<b} \<and>
        fst q \<in> D3BadXG_H0core \<omega>0 \<omega>s {\<phi> (snd q)}} \<Longrightarrow>
      \<exists>r. arc_schur_L \<omega>0 \<omega>s \<phi> D\<phi> (\<lambda>_. snd q) (fst q) r \<noteq> 0"
      by (rule schur[OF ab c1 gsub'])
  qed
  show "d3_detHess_arc_chart_core V \<omega>0 \<omega>s \<gamma>"
    using core geq by simp
qed

section \<open>Joint continuity of the x-partial, applied to a fixed direction\<close>

text \<open>Bridges has_derivative_gradU_dip_x_explicit (the concrete dEjm
  formula) with frechet_derivative_at to restate the ALREADY-PROVEN
  joint continuity fact continuous_on_gradU_dip_xpartial_applied
  (from Nonemptiness_Robust1.thy) in terms of frechet_derivative, matching
  the notation used by G'_x_part above -- no new continuity
  argument, just a restatement.\<close>

lemma frechet_derivative_gradU_dip_x_eq_explicit:
  fixes x i :: "(real^2)^'n::finite"
    and \<omega> \<omega>0 \<omega>s :: "real^2"
  shows
    "frechet_derivative
        (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) (at x) i
      =
      (\<chi> j.
        dEjm
          (frechet_derivative gdip
            (at (vec_nth \<omega> 1))
            (vec_nth (axis j 1) 1))
          (gain_dip \<omega>)
          (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
          (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
          (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
          (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) i))"
  using frechet_derivative_at[
      OF has_derivative_gradU_dip_x_explicit[
        where V = UNIV and x = x and \<omega> = \<omega>]]
  by (simp only: fun_eq_iff)

lemma continuous_on_frechet_derivative_gradU_dip_x_applied:
  fixes \<omega>0 \<omega>s :: "real^2"
    and i :: "(real^2)^'n::finite"
  shows "continuous_on
      (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
      (\<lambda>p. frechet_derivative
        (\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y (snd p))
        (at (fst p)) i)"
proof -
  have hcont:
      "continuous_on
        (UNIV :: (((real^2)^'n) \<times> (real^2)) set)
        (\<lambda>p.
          (\<chi> j.
            dEjm
              (frechet_derivative gdip
                (at (vec_nth (snd p) 1))
                (vec_nth (axis j 1) 1))
              (gain_dip (snd p))
              (vec_nth
                (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 1)
              (vec_nth
                (Dcvec_dip \<omega>0 \<omega>s (snd p) (axis j 1)) 2)
              (M_paper
                (fst p)
                (cvec_dip \<omega>0 \<omega>s (snd p)))
              (DM_paper_x
                (fst p)
                (cvec_dip \<omega>0 \<omega>s (snd p))
                i)) :: real^2)"
    using continuous_on_gradU_dip_xpartial_applied[of \<omega>0 \<omega>s i] .

  show ?thesis
    using hcont
    by (simp only: frechet_derivative_gradU_dip_x_eq_explicit
        cong: continuous_on_cong)
qed

end
