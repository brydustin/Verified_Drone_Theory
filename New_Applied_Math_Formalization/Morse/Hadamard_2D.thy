theory Hadamard_2D
  imports "HOL-Analysis.Analysis"
begin

definition C1field :: "(real^2 \<Rightarrow> real) \<Rightarrow> (real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "C1field f g S \<longleftrightarrow> (\<forall>x\<in>S. (f has_derivative (\<lambda>h. inner (g x) h)) (at x)) \<and> continuous_on S g"

text \<open>Generic differentiate-under-the-integral for the Hadamard coefficients.\<close>

lemma leibniz_coeff:
  fixes Hc :: "real^2 \<Rightarrow> real" and Kc :: "real^2 \<Rightarrow> real^2"
    and p :: "real^2" and \<rho>0 :: real
  assumes \<rho>0: "\<rho>0 > 0"
    and Kder: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (Hc has_derivative (\<lambda>h. inner (Kc x) h)) (at x)"
    and cK: "continuous_on (ball p \<rho>0) Kc"
  shows "C1field (\<lambda>x. integral {0..1} (\<lambda>t. (1 - t) * Hc (p + t *\<^sub>R (x - p))))
                 (\<lambda>x. integral {0..1} (\<lambda>t. ((1 - t) * t) *\<^sub>R Kc (p + t *\<^sub>R (x - p))))
                 (ball p \<rho>0)"
proof -
  define U where "U = ball p \<rho>0"
  have convU: "convex U" and openU: "open U" by (auto simp: U_def)
  define mseg where "mseg = (\<lambda>x t::real. p + t *\<^sub>R (x - p))"
  \<comment> \<open>segment stays in U\<close>
  have segin: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> mseg x t \<in> U"
  proof -
    fix x :: "real^2" and t :: real assume xU: "x \<in> U" and tin: "t \<in> {0..1}"
    have "dist (p + t *\<^sub>R (x - p)) p = t * dist x p"
      using tin by (simp add: dist_norm)
    also have "\<dots> < \<rho>0"
    proof (cases "dist x p = 0")
      case True thus ?thesis using \<rho>0 by simp
    next
      case False
      have "dist x p < \<rho>0" using xU by (simp add: U_def dist_commute)
      moreover have "0 < dist x p" using False by simp
      ultimately show ?thesis using tin
        by (metis atLeastAtMost_iff comm_monoid_mult_class.mult_1 less_eq_real_def mult_strict_mono')
    qed
    finally show "mseg x t \<in> U" by (simp only: U_def mseg_def dist_commute mem_ball)
  qed
  \<comment> \<open>Hc is continuous on U (from differentiability)\<close>
  have cHc: "continuous_on U Hc"
  proof (rule has_derivative_continuous_on)
    fix x :: "real^2" assume "x \<in> U"
    then have "(Hc has_derivative (\<lambda>h. inner (Kc x) h)) (at x)"
      using Kder by (simp add: U_def)
    then show "(Hc has_derivative (\<lambda>h. inner (Kc x) h)) (at x within U)"
      by (rule has_derivative_at_withinI)
  qed
  \<comment> \<open>the vector field v x t = ((1-t)*t) *_R Kc(mseg x t)\<close>
  define v where "v = (\<lambda>x t::real. ((1 - t) * t) *\<^sub>R Kc (mseg x t))"
  \<comment> \<open>joint continuity of v on U x {0..1}\<close>
  have cont_mseg: "continuous_on (U \<times> {0..1}) (\<lambda>(x,t). mseg x t)"
    unfolding mseg_def by (subst case_prod_unfold, intro continuous_intros)
  have img_mseg: "(\<lambda>(x,t). mseg x t) ` (U \<times> {0..1}) \<subseteq> U"
    using segin by auto
  have cont_Kc_seg: "continuous_on (U \<times> {0..1}) (\<lambda>(x,t). Kc (mseg x t))"
    by (metis (mono_tags, lifting) U_def cK   
        cont_mseg continuous_on_compose2 continuous_on_cong img_mseg split_beta')    
  have cont_Kmseg':"continuous_on (U \<times> {0..1}) (\<lambda>z. Kc (mseg (fst z) (snd z)))"
    using cont_Kc_seg continuous_on_eq by fastforce
  have cont_v: "continuous_on (U \<times> {0..1}) (\<lambda>(x,t). v x t)"
    unfolding v_def using cont_Kmseg' by (subst case_prod_unfold, intro continuous_intros)
  \<comment> \<open>blinfun field fx x t = Blinfun (inner (v x t))\<close>
  define fx where "fx = (\<lambda>x t::real. Blinfun (\<lambda>h. inner (v x t) h))"
  have bapp: "\<And>x t. blinfun_apply (fx x t) = (\<lambda>h. inner (v x t) h)"
    unfolding fx_def by (rule bounded_linear_Blinfun_apply[OF bounded_linear_inner_right])
  \<comment> \<open>pointwise x-derivative of the integrand Fc x t = (1-t) * Hc(mseg x t)\<close>
  have Fcder: "\<And>x t. x \<in> U \<Longrightarrow> t \<in> cbox 0 1 \<Longrightarrow>
      ((\<lambda>x. (1 - t) * Hc (mseg x t)) has_derivative blinfun_apply (fx x t)) (at x within U)"
  proof -
    fix x :: "real^2" and t :: real assume xU: "x \<in> U" and tin': "t \<in> cbox 0 1"
    have tin: "t \<in> {0..1}" using tin' by (simp add: cbox_interval)
    have mU: "mseg x t \<in> U" using segin[OF xU tin] .
    have m_der: "((\<lambda>x. mseg x t) has_derivative (\<lambda>h. t *\<^sub>R h)) (at x within U)"
      unfolding mseg_def by (auto intro!: derivative_eq_intros)
    have Hc_der: "(Hc has_derivative (\<lambda>h. inner (Kc (mseg x t)) h)) (at (mseg x t))"
      using Kder[OF mU[unfolded U_def]] by (simp add: U_def)
    have "((\<lambda>x. Hc (mseg x t)) has_derivative
              (\<lambda>h. inner (Kc (mseg x t)) (t *\<^sub>R h)))
              (at x within U)"
      by (rule has_derivative_compose[OF m_der Hc_der])
    then have chain: "((\<lambda>x. Hc (mseg x t)) has_derivative
        ((\<lambda>h. inner (Kc (mseg x t)) h) \<circ> (\<lambda>h. t *\<^sub>R h)))
        (at x within U)"
      by (metis (no_types, lifting) ext comp_apply)
    have chain': "((\<lambda>x. Hc (mseg x t)) has_derivative (\<lambda>h. t * inner (Kc (mseg x t)) h)) (at x within U)"
      using chain by (simp add: o_def)
    have "((\<lambda>x. Hc (mseg x t) * (1 - t)) has_derivative
                 (\<lambda>h. (t * inner (Kc (mseg x t)) h) * (1 - t))) (at x within U)"
      by (rule has_derivative_mult_left, simp add: chain')
    then have "((\<lambda>x. (1 - t) * Hc (mseg x t)) has_derivative (\<lambda>h. inner (v x t) h)) (at x within U)"
      unfolding v_def
      by (simp add: mult.commute vector_space_over_itself.scale_scale) 
    then show "((\<lambda>x. (1 - t) * Hc (mseg x t)) has_derivative blinfun_apply (fx x t)) (at x within U)"
      by (simp add: bapp)
  qed
  \<comment> \<open>integrability of t \<mapsto> Fc x t for fixed x\<close>
  have Fc_int: "\<And>x. x \<in> U \<Longrightarrow> (\<lambda>t. (1 - t) * Hc (mseg x t)) integrable_on cbox 0 1"
  proof -
    fix x :: "real^2" assume xU: "x \<in> U"
    have cm: "continuous_on {0..1} (\<lambda>t. mseg x t)"
      unfolding mseg_def by (simp only: continuous_intros)
    have sub: "(\<lambda>t. mseg x t) ` {0..1} \<subseteq> U" using segin[OF xU] by auto
    have "continuous_on {0..1} (\<lambda>t. Hc (mseg x t))"
      using continuous_on_compose2[OF cHc cm sub] .
    then have "continuous_on {0..1} (\<lambda>t. (1 - t) * Hc (mseg x t))"
      by (simp only: continuous_intros)
    then show "(\<lambda>t. (1 - t) * Hc (mseg x t)) integrable_on cbox 0 1"
      by (simp add: integrable_continuous_real)
  qed
  \<comment> \<open>joint continuity of the blinfun field via componentwise\<close>
  have cont_fx: "continuous_on (U \<times> cbox 0 1) (\<lambda>(x,t). fx x t)"
  proof (rule continuous_on_blinfun_componentwise)
    fix i :: "real^2" assume "i \<in> Basis"
    have "continuous_on (U \<times> cbox 0 1) (\<lambda>(x,t). inner (v x t) i)"
      using cont_v
      by (simp ,
          smt (verit, best) \<open>i \<in> Basis\<close> continuous_on_componentwise continuous_on_cong split_beta')
    moreover have "\<And>x t. blinfun_apply (fx x t) i = inner (v x t) i" by (simp add: bapp)
    ultimately show "continuous_on (U \<times> cbox 0 1) (\<lambda>x. blinfun_apply (case x of (x, t) \<Rightarrow> fx x t) i)"
      by (simp only: case_prod_unfold)
  qed
  \<comment> \<open>single-variable (slice) continuity of v and fx for fixed x0\<close>
  have slice_into: "\<And>x0. x0 \<in> U \<Longrightarrow> continuous_on (cbox 0 1) (\<lambda>t. (x0, t))"
    by (simp only: continuous_intros)
  have cont_v_slice: "\<And>x0. x0 \<in> U \<Longrightarrow> continuous_on (cbox 0 1) (\<lambda>t. v x0 t)"
  proof -
    fix x0 :: "real^2" assume x0U: "x0 \<in> U"
    have "continuous_on (cbox 0 1) ((\<lambda>(x,t). v x t) \<circ> (\<lambda>t. (x0, t)))"
      by (rule continuous_on_compose[OF slice_into[OF x0U]])
         (rule continuous_on_subset[OF cont_v], use x0U in \<open>auto simp: cbox_interval\<close>)
    then show "continuous_on (cbox 0 1) (\<lambda>t. v x0 t)" by (simp add: o_def)
  qed
  have cont_fx_slice: "\<And>x0. x0 \<in> U \<Longrightarrow> continuous_on (cbox 0 1) (\<lambda>t. fx x0 t)"
  proof -
    fix x0 :: "real^2" assume x0U: "x0 \<in> U"
    have "continuous_on (cbox 0 1) ((\<lambda>(x,t). fx x t) \<circ> (\<lambda>t. (x0, t)))"
      by (rule continuous_on_compose[OF slice_into[OF x0U]])
         (rule continuous_on_subset[OF cont_fx], use x0U in \<open>auto\<close>)
    then show "continuous_on (cbox 0 1) (\<lambda>t. fx x0 t)" by (simp add: o_def)
  qed
  \<comment> \<open>Leibniz: the integral has the blinfun derivative\<close>
  have leib: "\<And>x0. x0 \<in> U \<Longrightarrow>
      ((\<lambda>x. integral (cbox 0 1) (\<lambda>t. (1 - t) * Hc (mseg x t)))
        has_derivative blinfun_apply (integral (cbox 0 1) (fx x0))) (at x0 within U)"
  proof -
    fix x0 :: "real^2" assume x0U: "x0 \<in> U"
    show "((\<lambda>x. integral (cbox 0 1) (\<lambda>t. (1 - t) * Hc (mseg x t)))
            has_derivative blinfun_apply (integral (cbox 0 1) (fx x0))) (at x0 within U)"
      by (rule leibniz_rule[OF Fcder Fc_int cont_fx x0U convU])
  qed
  \<comment> \<open>convert the blinfun derivative to inner-form, and identify it with the gradient field\<close>
  have der_inner: "\<And>x0. x0 \<in> U \<Longrightarrow>
      ((\<lambda>x. integral {0..1} (\<lambda>t. (1 - t) * Hc (mseg x t)))
        has_derivative (\<lambda>h. inner (integral {0..1} (\<lambda>t. v x0 t)) h)) (at x0 within U)"
  proof -
    fix x0 :: "real^2" assume x0U: "x0 \<in> U"
    have fxint: "fx x0 integrable_on cbox 0 1"
      using cont_fx_slice[OF x0U] integrable_continuous by blast 
    have vint: "(\<lambda>t. v x0 t) integrable_on cbox 0 1"
      using cont_v_slice[OF x0U] integrable_continuous by blast 
    have apptoh: "\<And>h. blinfun_apply (integral (cbox 0 1) (fx x0)) h = inner (integral {0..1} (\<lambda>t. v x0 t)) h"
    proof -
      fix h :: "real^2"
      have "blinfun_apply (integral (cbox 0 1) (fx x0)) h
          = integral (cbox 0 1) (\<lambda>t. blinfun_apply (fx x0 t) h)"
        by (rule blinfun_apply_integral[OF fxint])
      also have "\<dots> = integral (cbox 0 1) (\<lambda>t. inner (v x0 t) h)"
        by (simp add: bapp)
      also have "\<dots> = integral (cbox 0 1) ((\<lambda>w. inner w h) \<circ> (\<lambda>t. v x0 t))"
        by (simp add: o_def)
      also have "\<dots> = inner (integral (cbox 0 1) (\<lambda>t. v x0 t)) h"
        by (rule integral_linear[OF vint bounded_linear_inner_left])
      finally show "blinfun_apply (integral (cbox 0 1) (fx x0)) h
          = inner (integral {0..1} (\<lambda>t. v x0 t)) h" by (simp add: cbox_interval)
    qed
    have "((\<lambda>x. integral (cbox 0 1) (\<lambda>t. (1 - t) * Hc (mseg x t)))
            has_derivative blinfun_apply (integral (cbox 0 1) (fx x0))) (at x0 within U)"
      by (rule leib[OF x0U])
    then show "((\<lambda>x. integral {0..1} (\<lambda>t. (1 - t) * Hc (mseg x t)))
            has_derivative (\<lambda>h. inner (integral {0..1} (\<lambda>t. v x0 t)) h)) (at x0 within U)"
      using apptoh by (metis (lifting) ext box_real(2)) 
  qed
  \<comment> \<open>upgrade derivative-within-open to derivative-at\<close>
  have der_at: "\<And>x0. x0 \<in> U \<Longrightarrow>
      ((\<lambda>x. integral {0..1} (\<lambda>t. (1 - t) * Hc (mseg x t)))
        has_derivative (\<lambda>h. inner (integral {0..1} (\<lambda>t. v x0 t)) h)) (at x0)"
  proof -
    fix x0 :: "real^2" assume x0U: "x0 \<in> U"
    have "at x0 within U = at x0" by (rule at_within_open[OF x0U openU])
    then show "((\<lambda>x. integral {0..1} (\<lambda>t. (1 - t) * Hc (mseg x t)))
            has_derivative (\<lambda>h. inner (integral {0..1} (\<lambda>t. v x0 t)) h)) (at x0)"
      using der_inner[OF x0U] by simp
  qed
  \<comment> \<open>continuity of the gradient field via integral_continuous_on_param\<close>
  have cont_grad: "continuous_on U (\<lambda>x. integral (cbox 0 1) (\<lambda>t. v x t))"
    by (rule integral_continuous_on_param[where f=v]) (use cont_v in \<open>simp add: cbox_interval\<close>)

  \<comment> \<open>assemble C1field; note the witness equals the gradient field by definition\<close>
  have eqg: "(\<lambda>x. integral {0..1} (\<lambda>t. ((1 - t) * t) *\<^sub>R Kc (p + t *\<^sub>R (x - p))))
           = (\<lambda>x. integral {0..1} (\<lambda>t. v x t))"
    unfolding v_def mseg_def by simp
  have eqa: "(\<lambda>x. integral {0..1} (\<lambda>t. (1 - t) * Hc (p + t *\<^sub>R (x - p))))
           = (\<lambda>x. integral {0..1} (\<lambda>t. (1 - t) * Hc (mseg x t)))"
    unfolding mseg_def by simp
  show ?thesis
    unfolding C1field_def
  proof (intro conjI ballI)
    fix x assume "x \<in> ball p \<rho>0"
    then have xU: "x \<in> U" by (simp add: U_def)
    show "((\<lambda>x. integral {0..1} (\<lambda>t. (1 - t) * Hc (p + t *\<^sub>R (x - p)))) has_derivative
            (\<lambda>h. inner ((\<lambda>x. integral {0..1} (\<lambda>t. ((1 - t) * t) *\<^sub>R Kc (p + t *\<^sub>R (x - p)))) x) h)) (at x)"
      using der_at[OF xU] mseg_def v_def by fastforce 
  next
    show "continuous_on (ball p \<rho>0) (\<lambda>x. integral {0..1} (\<lambda>t. ((1 - t) * t) *\<^sub>R Kc (p + t *\<^sub>R (x - p))))"
      using cont_grad by (simp add: U_def mseg_def v_def) 
  qed
qed


text \<open>Order-3 smoothness data for a scalar field f on a set S, packaged as explicit
  gradient / Hessian-row / third-order fields. G is the gradient of f; H1, H2 are the
  gradients of the two components of G (the Hessian rows); K11, K12, K22 are the gradients
  of the three distinct second partials (the order-3 data needed for the C1 dependence of
  the Hadamard coefficients). Continuity of the K-rows supplies the joint continuity that
  the Leibniz rule needs; the symmetry (H1 x)2 = (H2 x)1 is Clairaut/Schwarz (true for C2).
  Any C-infinity function (e.g. a trigonometric polynomial) supplies all of this on any
  open set.\<close>

definition SMOOTH3 ::
  "(real^2 \<Rightarrow> real) \<Rightarrow> (real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real^2)
   \<Rightarrow> (real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> real^2)
   \<Rightarrow> (real^2) set \<Rightarrow> bool" where
  "SMOOTH3 f G H1 H2 K11 K12 K22 S \<longleftrightarrow>
     (\<forall>x\<in>S. (f has_derivative (\<lambda>h. inner (G x) h)) (at x)) \<and>
     (\<forall>x\<in>S. ((\<lambda>y. (G y)$1) has_derivative (\<lambda>h. inner (H1 x) h)) (at x)) \<and>
     (\<forall>x\<in>S. ((\<lambda>y. (G y)$2) has_derivative (\<lambda>h. inner (H2 x) h)) (at x)) \<and>
     (\<forall>x\<in>S. (H1 x)$2 = (H2 x)$1) \<and>
     (\<forall>x\<in>S. ((\<lambda>y. (H1 y)$1) has_derivative (\<lambda>h. inner (K11 x) h)) (at x)) \<and>
     (\<forall>x\<in>S. ((\<lambda>y. (H1 y)$2) has_derivative (\<lambda>h. inner (K12 x) h)) (at x)) \<and>
     (\<forall>x\<in>S. ((\<lambda>y. (H2 y)$2) has_derivative (\<lambda>h. inner (K22 x) h)) (at x)) \<and>
     continuous_on S (\<lambda>x. (H1 x)$1) \<and> continuous_on S (\<lambda>x. (H1 x)$2) \<and>
     continuous_on S (\<lambda>x. (H2 x)$2) \<and>
     continuous_on S K11 \<and> continuous_on S K12 \<and> continuous_on S K22"

subsection \<open>Chain rules for the 1D restriction along a segment\<close>

lemma chain1:
  fixes f :: "real^2 \<Rightarrow> real" and G :: "real^2 \<Rightarrow> real^2"
    and p Delta :: "real^2" and t :: real
  assumes "(f has_derivative (\<lambda>h. inner (G (p + t *\<^sub>R Delta)) h)) (at (p + t *\<^sub>R Delta))"
  shows "((\<lambda>s. f (p + s *\<^sub>R Delta)) has_vector_derivative inner (G (p + t *\<^sub>R Delta)) Delta) (at t)"
proof -
  have seg: "((\<lambda>s. p + s *\<^sub>R Delta) has_derivative (\<lambda>h. h *\<^sub>R Delta)) (at t)"
    by (auto intro!: derivative_eq_intros)
  have "((f \<circ> (\<lambda>s. p + s *\<^sub>R Delta)) has_derivative
          ((\<lambda>h. inner (G (p + t *\<^sub>R Delta)) h) \<circ> (\<lambda>h. h *\<^sub>R Delta))) (at t)"
    by (rule diff_chain_at[OF seg assms])
  then have "((\<lambda>s. f (p + s *\<^sub>R Delta)) has_derivative
          (\<lambda>h. h * inner (G (p + t *\<^sub>R Delta)) Delta)) (at t)"
    by (simp add: o_def inner_commute)
  then show ?thesis
    by (simp add: has_vector_derivative_def has_derivative_at_within mult.commute)
qed

lemma chain2:
  fixes G :: "real^2 \<Rightarrow> real^2" and H1 H2 :: "real^2 \<Rightarrow> real^2"
    and p Delta :: "real^2" and t :: real
  assumes h1: "((\<lambda>y. (G y)$1) has_derivative (\<lambda>h. inner (H1 (p + t *\<^sub>R Delta)) h)) (at (p + t *\<^sub>R Delta))"
      and h2: "((\<lambda>y. (G y)$2) has_derivative (\<lambda>h. inner (H2 (p + t *\<^sub>R Delta)) h)) (at (p + t *\<^sub>R Delta))"
  shows "((\<lambda>s. inner (G (p + s *\<^sub>R Delta)) Delta) has_vector_derivative
          (Delta$1 * inner (H1 (p + t *\<^sub>R Delta)) Delta
         + Delta$2 * inner (H2 (p + t *\<^sub>R Delta)) Delta)) (at t)"
proof -
  let ?s = "p + t *\<^sub>R Delta"
  have seg: "((\<lambda>s. p + s *\<^sub>R Delta) has_derivative (\<lambda>h. h *\<^sub>R Delta)) (at t)"
    by (auto intro!: derivative_eq_intros)
  have c1: "((\<lambda>s. (G (p + s *\<^sub>R Delta))$1) has_vector_derivative inner (H1 ?s) Delta) (at t)"
  proof -
    have "(((\<lambda>y. (G y)$1) \<circ> (\<lambda>s. p + s *\<^sub>R Delta)) has_derivative
            ((\<lambda>h. inner (H1 ?s) h) \<circ> (\<lambda>h. h *\<^sub>R Delta))) (at t)"
      by (rule diff_chain_at[OF seg h1])
    then have "((\<lambda>s. (G (p + s *\<^sub>R Delta))$1) has_derivative (\<lambda>h. h * inner (H1 ?s) Delta)) (at t)"
      by (simp add: o_def inner_commute)
    then show ?thesis
      by (simp add: has_vector_derivative_def has_derivative_at_within mult.commute)
  qed
  have c2: "((\<lambda>s. (G (p + s *\<^sub>R Delta))$2) has_vector_derivative inner (H2 ?s) Delta) (at t)"
  proof -
    have "(((\<lambda>y. (G y)$2) \<circ> (\<lambda>s. p + s *\<^sub>R Delta)) has_derivative
            ((\<lambda>h. inner (H2 ?s) h) \<circ> (\<lambda>h. h *\<^sub>R Delta))) (at t)"
      by (rule diff_chain_at[OF seg h2])
    then have "((\<lambda>s. (G (p + s *\<^sub>R Delta))$2) has_derivative (\<lambda>h. h * inner (H2 ?s) Delta)) (at t)"
      by (simp add: o_def inner_commute)
    then show ?thesis
      by (simp add: has_vector_derivative_def has_derivative_at_within mult.commute)
  qed
  have eq: "\<And>s. inner (G s) Delta = Delta$1 * (G s)$1 + Delta$2 * (G s)$2"
    by (simp add: inner_vec_def UNIV_2 mult.commute)
  have "((\<lambda>s. Delta$1 * (G (p + s *\<^sub>R Delta))$1 + Delta$2 * (G (p + s *\<^sub>R Delta))$2)
          has_vector_derivative
          (Delta$1 * inner (H1 ?s) Delta + Delta$2 * inner (H2 ?s) Delta)) (at t)"
    by (auto intro!: derivative_eq_intros c1 c2)
  then show ?thesis using eq by simp
qed

subsection \<open>1D Taylor with integral remainder (from Taylor_has_integral, p = 2)\<close>

lemma taylor_remainder:
  fixes phi phi' phi'' :: "real \<Rightarrow> real"
  assumes d0: "\<And>t. t \<in> {0..1} \<Longrightarrow> (phi has_vector_derivative phi' t) (at t within {0..1})"
      and d1: "\<And>t. t \<in> {0..1} \<Longrightarrow> (phi' has_vector_derivative phi'' t) (at t within {0..1})"
      and z0: "phi 0 = 0" and z1: "phi' 0 = 0"
  shows "((\<lambda>x. (1 - x) * phi'' x) has_integral phi 1) {0..1}"
proof -
  define Df :: "nat \<Rightarrow> real \<Rightarrow> real" where
    "Df = (\<lambda>m. if m = 0 then phi else if m = 1 then phi' else phi'')"
  have step: "\<And>m t. \<lbrakk>m < 2; 0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow>
                (Df m has_vector_derivative Df (Suc m) t) (at t within {0..1})"
  proof -
    fix m :: nat and t :: real
    assume m2: "m < 2" and tl: "0 \<le> t" and tu: "t \<le> 1"
    have tin: "t \<in> {0..1}" using tl tu by simp
    consider "m = 0" | "m = 1" using m2 by linarith
    then show "(Df m has_vector_derivative Df (Suc m) t) (at t within {0..1})"
    proof cases
      case 1 thus ?thesis using d0[OF tin] by (simp add: Df_def)
    next
      case 2 thus ?thesis using d1[OF tin] by (simp add: Df_def)
    qed
  qed
  have "((\<lambda>x. ((1 - x) ^ (2 - 1) / fact (2 - 1)) *\<^sub>R Df 2 x) has_integral
          Df 0 1 - (\<Sum>i<2. ((1 - 0) ^ i / fact i) *\<^sub>R Df i 0)) {0..1}"
    by (rule Taylor_has_integral[where p=2 and a=0 and b=1 and f="Df 0" and Df=Df])
       (use step in \<open>auto\<close>)
  also have "Df 0 1 - (\<Sum>i<2. ((1 - 0) ^ i / fact i) *\<^sub>R Df i 0) = phi 1"
    by (simp add: Df_def z0 z1 numeral_2_eq_2 lessThan_Suc)
  finally have "((\<lambda>x. ((1 - x) ^ (2 - 1) / fact (2 - 1)) *\<^sub>R Df 2 x) has_integral phi 1) {0..1}" .
  then show ?thesis by (simp add: Df_def)
qed

subsection \<open>Geometric / algebraic helpers\<close>

lemma seg_in_ball:
  fixes p x :: "real^2" and rho t :: real
  assumes "x \<in> ball p rho" and "0 \<le> t" and "t \<le> 1"
  shows "p + t *\<^sub>R (x - p) \<in> ball p rho"
proof -
  have "dist (p + t *\<^sub>R (x - p)) p = norm (t *\<^sub>R (x - p))"
    by (simp add: dist_norm)
  also have "\<dots> = t * dist x p"
    using assms(2) by (simp add: dist_norm)
  also have "\<dots> < rho"
  proof (cases "dist x p = 0")
    case True thus ?thesis using assms by (simp add: dist_norm)
  next
    case False
    have "dist x p < rho" using assms(1) by (simp add: dist_commute)
    moreover have "0 < dist x p" using False by simp
    ultimately show ?thesis using assms(2,3)
      by (meson mult_left_le_one_le order_le_less_trans zero_le_dist)
  qed
  finally show ?thesis by (simp only: dist_commute mem_ball)
qed

lemma phi2_as_form:
  fixes H1 H2 :: "real^2 \<Rightarrow> real^2" and Delta s :: "real^2"
  assumes sym: "(H1 s)$2 = (H2 s)$1"
  shows "Delta$1 * inner (H1 s) Delta + Delta$2 * inner (H2 s) Delta
       = (H1 s)$1 * (Delta$1)\<^sup>2 + 2 * ((H1 s)$2 * ((Delta$1) * (Delta$2))) + (H2 s)$2 * (Delta$2)\<^sup>2"
proof -
  have e1: "inner (H1 s) Delta = (H1 s)$1 * Delta$1 + (H1 s)$2 * Delta$2"
    by (simp add: inner_vec_def UNIV_2)
  have e2: "inner (H2 s) Delta = (H2 s)$1 * Delta$1 + (H2 s)$2 * Delta$2"
    by (simp add: inner_vec_def UNIV_2)
  show ?thesis using e1 e2 sym by (simp add: power2_eq_square algebra_simps)
qed

lemma half_int: "integral {0..1} (\<lambda>t::real. 1 - t) = 1/2"
proof -
  define F :: "real \<Rightarrow> real" where "F = (\<lambda>t. t - t\<^sup>2 / 2)"
  have "((\<lambda>t::real. 1 - t) has_integral F 1 - F 0) {0..1}"
  proof (rule fundamental_theorem_of_calculus)
    show "(0::real) \<le> 1" by simp
    show "\<And>x. x \<in> {0..1} \<Longrightarrow> (F has_vector_derivative (1 - x)) (at x within {0..1})"
      unfolding F_def by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  qed
  moreover have "F 1 - F 0 = 1/2" unfolding F_def by simp
  ultimately show ?thesis by (simp add: integral_unique)
qed

lemma gp0:
  fixes G :: "real^2 \<Rightarrow> real^2" and f :: "real^2 \<Rightarrow> real" and p :: "real^2"
  assumes a: "(f has_derivative (\<lambda>h. inner (G p) h)) (at p)"
      and b: "(f has_derivative (\<lambda>_. 0)) (at p)"
  shows "G p = 0"
proof -
  have "(\<lambda>h. inner (G p) h) = (\<lambda>_. 0)" by (rule has_derivative_unique[OF a b])
  then have allh: "\<And>h. inner (G p) h = 0" by (rule fun_cong)
  have "inner (G p) (G p) = 0" by (rule allh)
  then show ?thesis by simp
qed

lemma seg_integrand_cont:
  fixes H :: "real^2 \<Rightarrow> real" and p Delta :: "real^2" and R :: real
  assumes cH: "continuous_on (ball p R) H"
      and seg: "\<And>t. t \<in> {0..1} \<Longrightarrow> p + t *\<^sub>R Delta \<in> ball p R"
  shows "continuous_on {0..1} (\<lambda>t. (1 - t) * H (p + t *\<^sub>R Delta))"
proof -
  have s: "continuous_on {0..1} (\<lambda>t. p + t *\<^sub>R Delta)"
    by (simp only: continuous_intros)
  have sub: "(\<lambda>t. p + t *\<^sub>R Delta) ` {0..1} \<subseteq> ball p R" using seg by auto
  have "continuous_on {0..1} (\<lambda>t. H (p + t *\<^sub>R Delta))"
    by (rule continuous_on_compose2[OF cH s sub])
  then show ?thesis by (simp only: continuous_intros)
qed

lemma lin_split_cont:
  fixes g1 g2 g3 :: "real \<Rightarrow> real" and c1 c2 c3 :: real
  assumes "continuous_on {0..1::real} g1" "continuous_on {0..1::real} g2" "continuous_on {0..1::real} g3"
  shows "integral {0..1} (\<lambda>t. c1 * g1 t + 2 * c2 * g2 t + c3 * g3 t)
       = c1 * integral {0..1} g1 + 2 * c2 * integral {0..1} g2 + c3 * integral {0..1} g3"
proof -
  have i1: "(\<lambda>t. c1 * g1 t) integrable_on {0..1}"
    using assms(1) by (simp only: integrable_continuous_real continuous_intros)
  have i2: "(\<lambda>t. 2 * c2 * g2 t) integrable_on {0..1}"
    using assms(2) by (simp only: integrable_continuous_real continuous_intros)
  have i3: "(\<lambda>t. c3 * g3 t) integrable_on {0..1}"
    using assms(3) by (simp only: integrable_continuous_real continuous_intros)
  have i12: "(\<lambda>t. c1 * g1 t + 2 * c2 * g2 t) integrable_on {0..1}"
    using i1 i2 by (rule integrable_add)
  have "integral {0..1} (\<lambda>t. (c1 * g1 t + 2 * c2 * g2 t) + c3 * g3 t)
      = integral {0..1} (\<lambda>t. c1 * g1 t + 2 * c2 * g2 t) + integral {0..1} (\<lambda>t. c3 * g3 t)"
    by (rule integral_add[OF i12 i3])
  also have "integral {0..1} (\<lambda>t. c1 * g1 t + 2 * c2 * g2 t)
      = integral {0..1} (\<lambda>t. c1 * g1 t) + integral {0..1} (\<lambda>t. 2 * c2 * g2 t)"
    by (rule integral_add[OF i1 i2])
  finally have "integral {0..1} (\<lambda>t. c1 * g1 t + 2 * c2 * g2 t + c3 * g3 t)
      = integral {0..1} (\<lambda>t. c1 * g1 t) + integral {0..1} (\<lambda>t. 2 * c2 * g2 t)
      + integral {0..1} (\<lambda>t. c3 * g3 t)"
    by (simp add: add.assoc)
  also have "\<dots> = c1 * integral {0..1} g1 + 2 * c2 * integral {0..1} g2 + c3 * integral {0..1} g3"
    by (simp only: integral_mult_right mult.assoc)
  finally show ?thesis.
qed

subsection \<open>Hadamard's lemma, 2nd order\<close>

text \<open>The coefficient functions a, b, c are the parametric integrals of the (weighted)
  second partials along the segment from p to x. C1field of a, b, c is the
  differentiate-under-the-integral (Leibniz) step, discharged via @{thm leibniz_coeff}
  (witnesses ga, gb, gc supplied). The quadratic decomposition of f and the identification
  of 2 a p, 2 b p, 2 c p with the second partials are proven below. No proof hole.\<close>

lemma hadamard2:
  fixes f :: "real^2 \<Rightarrow> real" and p :: "real^2" and \<rho>0 :: real
  assumes \<rho>0: "\<rho>0 > 0"
    and smooth: "SMOOTH3 f G H1 H2 K11 K12 K22 (ball p \<rho>0)"
    and fp: "f p = 0"
    and Dfp: "(f has_derivative (\<lambda>_. 0)) (at p)"
  obtains a b c :: "real^2 \<Rightarrow> real" and ga gb gc :: "real^2 \<Rightarrow> real^2" and \<rho> :: real
    where "0 < \<rho>" "\<rho> \<le> \<rho>0"
      "C1field a ga (ball p \<rho>)" "C1field b gb (ball p \<rho>)" "C1field c gc (ball p \<rho>)"
      "\<And>x. x \<in> ball p \<rho> \<Longrightarrow>
          f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
      "2 * a p = (H1 p)$1" "2 * b p = (H1 p)$2" "2 * c p = (H2 p)$2"
proof -
  define a where "a = (\<lambda>x::real^2. integral {0..1} (\<lambda>t. (1 - t) * (H1 (p + t *\<^sub>R (x - p)))$1))"
  define b where "b = (\<lambda>x::real^2. integral {0..1} (\<lambda>t. (1 - t) * (H1 (p + t *\<^sub>R (x - p)))$2))"
  define c where "c = (\<lambda>x::real^2. integral {0..1} (\<lambda>t. (1 - t) * (H2 (p + t *\<^sub>R (x - p)))$2))"
  define ga where "ga = (\<lambda>x::real^2. integral {0..1} (\<lambda>t. ((1 - t) * t) *\<^sub>R K11 (p + t *\<^sub>R (x - p))))"
  define gb where "gb = (\<lambda>x::real^2. integral {0..1} (\<lambda>t. ((1 - t) * t) *\<^sub>R K12 (p + t *\<^sub>R (x - p))))"
  define gc where "gc = (\<lambda>x::real^2. integral {0..1} (\<lambda>t. ((1 - t) * t) *\<^sub>R K22 (p + t *\<^sub>R (x - p))))"

  have Gder: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (f has_derivative (\<lambda>h. inner (G x) h)) (at x)"
    and H1der: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> ((\<lambda>y. (G y)$1) has_derivative (\<lambda>h. inner (H1 x) h)) (at x)"
    and H2der: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> ((\<lambda>y. (G y)$2) has_derivative (\<lambda>h. inner (H2 x) h)) (at x)"
    and symm: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> (H1 x)$2 = (H2 x)$1"
    and cH11: "continuous_on (ball p \<rho>0) (\<lambda>x. (H1 x)$1)"
    and cH12: "continuous_on (ball p \<rho>0) (\<lambda>x. (H1 x)$2)"
    and cH22: "continuous_on (ball p \<rho>0) (\<lambda>x. (H2 x)$2)"
    and K11der: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> ((\<lambda>y. (H1 y)$1) has_derivative (\<lambda>h. inner (K11 x) h)) (at x)"
    and K12der: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> ((\<lambda>y. (H1 y)$2) has_derivative (\<lambda>h. inner (K12 x) h)) (at x)"
    and K22der: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow> ((\<lambda>y. (H2 y)$2) has_derivative (\<lambda>h. inner (K22 x) h)) (at x)"
    and cK11: "continuous_on (ball p \<rho>0) K11"
    and cK12: "continuous_on (ball p \<rho>0) K12"
    and cK22: "continuous_on (ball p \<rho>0) K22"
    using smooth unfolding SMOOTH3_def by blast+

  have Gp0: "G p = 0"
  proof -
    have pin: "p \<in> ball p \<rho>0" using \<rho>0 by simp
    show ?thesis
      using Dfp Gder gp0 pin by blast 
  qed

  have decomp: "\<And>x. x \<in> ball p \<rho>0 \<Longrightarrow>
      f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
  proof -
    fix x :: "real^2" assume xin: "x \<in> ball p \<rho>0"
    define Delta where "Delta = x - p"
    define phi where "phi = (\<lambda>t::real. f (p + t *\<^sub>R Delta))"
    define phi' where "phi' = (\<lambda>t::real. inner (G (p + t *\<^sub>R Delta)) Delta)"
    define phi'' where "phi'' = (\<lambda>t::real. Delta$1 * inner (H1 (p + t *\<^sub>R Delta)) Delta
                                          + Delta$2 * inner (H2 (p + t *\<^sub>R Delta)) Delta)"
    have segin: "\<And>t. t \<in> {0..1} \<Longrightarrow> p + t *\<^sub>R Delta \<in> ball p \<rho>0"
      using seg_in_ball[OF xin] unfolding Delta_def by auto
    have D0: "\<And>t. t \<in> {0..1} \<Longrightarrow> (phi has_vector_derivative phi' t) (at t within {0..1})"
    proof -
      fix t :: real assume tin: "t \<in> {0..1}"
      have "(phi has_vector_derivative phi' t) (at t)"
        unfolding phi_def phi'_def
        using Gder chain1 segin tin by blast 
      then show "(phi has_vector_derivative phi' t) (at t within {0..1})"
        using has_vector_derivative_at_within by blast
    qed
    have D1: "\<And>t. t \<in> {0..1} \<Longrightarrow> (phi' has_vector_derivative phi'' t) (at t within {0..1})"
    proof -
      fix t :: real assume tin: "t \<in> {0..1}"
      have "(phi' has_vector_derivative phi'' t) (at t)"
        unfolding phi'_def phi''_def
        using H1der H2der chain2 segin tin by blast
      then show "(phi' has_vector_derivative phi'' t) (at t within {0..1})"
        using has_vector_derivative_at_within by blast
    qed
    have phi0: "phi 0 = 0" unfolding phi_def using fp by simp
    have phi'0: "phi' 0 = 0" unfolding phi'_def using Gp0 by simp
    have FTC: "((\<lambda>t. (1 - t) * phi'' t) has_integral phi 1) {0..1}"
      by (rule taylor_remainder[OF D0 D1 phi0 phi'0])
    have phi1: "phi 1 = f x" unfolding phi_def Delta_def by simp
    define g1 where "g1 = (\<lambda>t::real. (1 - t) * (H1 (p + t *\<^sub>R Delta))$1)"
    define g2 where "g2 = (\<lambda>t::real. (1 - t) * (H1 (p + t *\<^sub>R Delta))$2)"
    define g3 where "g3 = (\<lambda>t::real. (1 - t) * (H2 (p + t *\<^sub>R Delta))$2)"
    have integrand: "\<And>t. t \<in> {0..1} \<Longrightarrow>
        (1 - t) * phi'' t
        = (Delta$1)\<^sup>2 * g1 t + 2 * ((Delta$1) * (Delta$2)) * g2 t + (Delta$2)\<^sup>2 * g3 t"
    proof -
      fix t :: real assume tin: "t \<in> {0..1}"
      have "(1 - t) * phi'' t
          = (1 - t) * ((H1 (p + t *\<^sub>R Delta))$1 * (Delta$1)\<^sup>2
              + 2 * ((H1 (p + t *\<^sub>R Delta))$2 * ((Delta$1) * (Delta$2)))
              + (H2 (p + t *\<^sub>R Delta))$2 * (Delta$2)\<^sup>2)"
        unfolding phi''_def using phi2_as_form segin symm tin by presburger 
      also have "\<dots> = (Delta$1)\<^sup>2 * g1 t + 2 * ((Delta$1) * (Delta$2)) * g2 t + (Delta$2)\<^sup>2 * g3 t"
        unfolding g1_def g2_def g3_def by (simp add: algebra_simps)
      finally show "(1 - t) * phi'' t
        = (Delta$1)\<^sup>2 * g1 t + 2 * ((Delta$1) * (Delta$2)) * g2 t + (Delta$2)\<^sup>2 * g3 t" .
    qed
    have cg1: "continuous_on {0..1} g1"
      unfolding g1_def by (rule seg_integrand_cont[OF cH11 segin])
    have cg2: "continuous_on {0..1} g2"
      unfolding g2_def by (rule seg_integrand_cont[OF cH12 segin])
    have cg3: "continuous_on {0..1} g3"
      unfolding g3_def by (rule seg_integrand_cont[OF cH22 segin])
    have "f x = phi 1" using phi1 by simp
    also have "phi 1 = integral {0..1} (\<lambda>t. (1 - t) * phi'' t)"
      using FTC by (simp add: integral_unique)
    also have "\<dots> = integral {0..1}
                    (\<lambda>t. (Delta$1)\<^sup>2 * g1 t + 2 * ((Delta$1) * (Delta$2)) * g2 t + (Delta$2)\<^sup>2 * g3 t)"
      by (rule integral_cong) (rule integrand)
    also have "\<dots> = (Delta$1)\<^sup>2 * integral {0..1} g1
                  + 2 * ((Delta$1) * (Delta$2)) * integral {0..1} g2
                  + (Delta$2)\<^sup>2 * integral {0..1} g3"
      by (rule lin_split_cont[OF cg1 cg2 cg3])
    also have "\<dots> = a x * (Delta$1)\<^sup>2 + 2 * b x * ((Delta$1) * (Delta$2)) + c x * (Delta$2)\<^sup>2"
      unfolding a_def b_def c_def g1_def g2_def g3_def Delta_def by (simp add: algebra_simps)
    finally show "f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
      unfolding Delta_def by (simp add: algebra_simps)
  qed

  have ap: "2 * a p = (H1 p)$1"
  proof -
    have "a p = integral {0..1} (\<lambda>t. (1 - t) * (H1 p)$1)" unfolding a_def by simp
    also have "\<dots> = (H1 p)$1 * integral {0..1} (\<lambda>t::real. 1 - t)"
      by simp
    also have "\<dots> = (H1 p)$1 * (1/2)" by (simp add: half_int)
    finally show ?thesis by simp
  qed
  have bp: "2 * b p = (H1 p)$2"
  proof -
    have "b p = integral {0..1} (\<lambda>t. (1 - t) * (H1 p)$2)" unfolding b_def by simp
    also have "\<dots> = (H1 p)$2 * integral {0..1} (\<lambda>t::real. 1 - t)"
      by simp
    also have "\<dots> = (H1 p)$2 * (1/2)" by (simp add: half_int)
    finally show ?thesis by simp
  qed
  have cp: "2 * c p = (H2 p)$2"
  proof -
    have "c p = integral {0..1} (\<lambda>t. (1 - t) * (H2 p)$2)" unfolding c_def by simp
    also have "\<dots> = (H2 p)$2 * integral {0..1} (\<lambda>t::real. 1 - t)"
      by simp
    also have "\<dots> = (H2 p)$2 * (1/2)" by (simp add: half_int)
    finally show ?thesis by simp
  qed

  text \<open>C1field of the coefficients: differentiate under the integral (Leibniz).
    Discharged via leibniz_coeff (one application each).\<close>
  have C1a: "C1field a ga (ball p \<rho>0)"
    unfolding a_def ga_def by (rule leibniz_coeff[OF \<rho>0 K11der cK11])
  have C1b: "C1field b gb (ball p \<rho>0)"
    unfolding b_def gb_def by (rule leibniz_coeff[OF \<rho>0 K12der cK12])
  have C1c: "C1field c gc (ball p \<rho>0)"
    unfolding c_def gc_def by (rule leibniz_coeff[OF \<rho>0 K22der cK22])

  show ?thesis
    by (rule that[of \<rho>0 a ga b gb c gc])
       (use \<rho>0 C1a C1b C1c decomp ap bp cp in auto)
qed

end
