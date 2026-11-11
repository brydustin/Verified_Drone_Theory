theory Scratch_VPair22Full
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

section \<open>cor:vpair22-full: the abstract determinant algebra (prop:vpair22-KLM)\<close>

text \<open>The paper's \<open>T_\<tau>,V_\<tau>,D_\<tau>,K,L,M,\<Theta>_1^{(22)},\<Theta>_2^{(22)}\<close> apparatus is stated in the
  paper's OWN gauge-specific c-adapted local coordinates (\<open>b=0\<close>, real/imaginary moment
  decompositions \<open>a_1,b_1,a_2,b_2,a_{12},a_{22}\<close>).  Formalized here as ABSTRACT real
  quantities satisfying the defining trig relations, NOT yet connected to this project's
  invariant \<open>x\<close>/\<open>\<omega>\<close>/\<open>HessU\<close> objects --- that connection needs a gauge-specific
  translation layer (assuming \<open>b=0\<close>, i.e. \<open>Im(A)=0\<close>, then relating \<open>H_{12},H_{22}\<close> to
  their moment-derivative formulas) that has NOT been built and is comparable in scope to
  everything already built for \<open>G22\<close>/\<open>H_par\<close> --- see the closing report for the honest
  scope assessment.\<close>

subsection \<open>The triple determinants, via the existing det3 primitive\<close>

definition Ttau :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Ttau u1 u2 u3 t1 t2 t3 = det3 1 1 1 u1 u2 u3 t1 t2 t3"

definition Vtau :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Vtau v1 v2 v3 t1 t2 t3 = det3 1 1 1 v1 v2 v3 t1 t2 t3"

definition Dtau :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Dtau v1 v2 v3 u1 u2 u3 t1 t2 t3 = det3 v1 v2 v3 u1 u2 u3 t1 t2 t3"

definition AT3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "AT3 u1 u2 u3 v1 v2 v3 = det3 1 1 1 u1 u2 u3 v1 v2 v3"

text \<open>\<open>L,M,K\<close>, the paper's "familiar cofactors" (defined earlier in the paper via
  \<open>c_j,s_j\<close> weighted rows) --- here directly via their OWN determinant definitions
  (\<open>L:=\<det>[c;s;vc]\<close>, \<open>M:=\<det>[c;s;uc]\<close>, and by the same pattern \<open>K:=\<det>[s;uc;vc]\<close>,
  matching \<open>prop:vmixed\<close>'s computation).\<close>

definition Lcof :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Lcof c1 c2 c3 s1 s2 s3 v1 v2 v3 = det3 c1 c2 c3 s1 s2 s3 (v1*c1) (v2*c2) (v3*c3)"

definition Mcof :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Mcof c1 c2 c3 s1 s2 s3 u1 u2 u3 = det3 c1 c2 c3 s1 s2 s3 (u1*c1) (u2*c2) (u3*c3)"

definition Kcof :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Kcof c1 c2 c3 s1 s2 s3 u1 u2 u3 v1 v2 v3
     = det3 s1 s2 s3 (u1*c1) (u2*c2) (u3*c3) (v1*c1) (v2*c2) (v3*c3)"

subsection \<open>prop:vpair22-KLM: L, M, K in terms of T_tau, V_tau, D_tau (c1c2c3\<noteq>0)\<close>

text \<open>Dividing the j-th column of L's/M's/K's defining determinant by \<open>c_j\<close> turns the
  \<open>s_j\<close> row into \<open>tan(\<kappa>u_j) = \<tau>_j\<close> and the \<open>u_jc_j\<close>/\<open>v_jc_j\<close> rows into \<open>u_j\<close>/\<open>v_j\<close>; the
  paper then identifies the result with \<open>V_\<tau>,T_\<tau>,D_\<tau>\<close> up to a row swap. Formalized here
  directly via \<open>det3\<close>'s explicit expansion (no row/column abstraction machinery needed for
  a fixed 3x3 case) --- each identity is pure field algebra once \<open>s_j = \<tau>_j c_j\<close> is
  substituted and \<open>c_j \<noteq> 0\<close> is used to clear denominators.\<close>

theorem Lcof_eq:
  assumes c1: "c1 \<noteq> 0" and c2: "c2 \<noteq> 0" and c3: "c3 \<noteq> 0"
    and s1: "s1 = t1 * c1" and s2: "s2 = t2 * c2" and s3: "s3 = t3 * c3"
  shows "Lcof c1 c2 c3 s1 s2 s3 v1 v2 v3 = - (c1*c2*c3) * Vtau v1 v2 v3 t1 t2 t3"
  unfolding Lcof_def Vtau_def det3_def s1 s2 s3
  by (simp add: algebra_simps)

theorem Mcof_eq:
  assumes c1: "c1 \<noteq> 0" and c2: "c2 \<noteq> 0" and c3: "c3 \<noteq> 0"
    and s1: "s1 = t1 * c1" and s2: "s2 = t2 * c2" and s3: "s3 = t3 * c3"
  shows "Mcof c1 c2 c3 s1 s2 s3 u1 u2 u3 = - (c1*c2*c3) * Ttau u1 u2 u3 t1 t2 t3"
  unfolding Mcof_def Ttau_def det3_def s1 s2 s3
  by (simp add: algebra_simps)

theorem Kcof_eq:
  assumes s1: "s1 = t1 * c1" and s2: "s2 = t2 * c2" and s3: "s3 = t3 * c3"
  shows "Kcof c1 c2 c3 s1 s2 s3 u1 u2 u3 v1 v2 v3 = - (c1*c2*c3) * Dtau v1 v2 v3 u1 u2 u3 t1 t2 t3"
  unfolding Kcof_def Dtau_def det3_def s1 s2 s3
  by (simp add: algebra_simps)

text \<open>The \<open>\<Theta>_1^{(22)},\<Theta>_2^{(22)}\<close> restatement (prop:vpair22-KLM's corollary): given
  \<open>H_{22}M - H_{12}L = 0\<close> and \<open>aK+a_1L-a_2M=0\<close> (the \<open>\<Theta>\<close>-vanishing conditions, unfolded to
  \<open>K,L,M\<close> directly per the paper's own definitions \<open>\<Theta>_1^{(22)}:=H_{12}V_\<tau>-H_{22}T_\<tau>\<close>,
  \<open>\<Theta>_2^{(22)}:=aD_\<tau>-a_2T_\<tau>+a_1V_\<tau>\<close>), the ratio identities \<open>L/M=H_{22}/H_{12}\<close> and
  \<open>K/M=(a_2H_{12}-a_1H_{22})/(aH_{12})\<close> hold PROVIDED \<open>M\<noteq>0\<close> (cor:vpair22-nonzero's own
  nonvanishing conclusion --- not re-derived here, see the closing report).\<close>

theorem KLM_ratio_from_Theta:
  fixes H12 H22 a a1 a2 K L M :: real
  assumes h12: "H12 \<noteq> 0" and a: "a \<noteq> 0" and Mnz: "M \<noteq> 0"
    and theta1: "H22 * M - H12 * L = 0"
    and theta2: "a * K + a1 * L - a2 * M = 0"
  shows "L / M = H22 / H12" and "K / M = (a2 * H12 - a1 * H22) / (a * H12)"
proof -
  have e1: "L * H12 = H22 * M"
    using theta1 by (simp add: algebra_simps eq_diff_eq)
  show "L / M = H22 / H12"
    using frac_eq_eq[OF Mnz h12] e1 by (simp add: algebra_simps)
  have e2: "K * (a * H12) = (a2 * H12 - a1 * H22) * M"
  proof -
    have step0: "K * a + L * a1 = M * a2"
      using theta2 by (simp add: algebra_simps eq_diff_eq)
    have "a * K * H12 = (a2 * M - a1 * L) * H12"
      using arg_cong[where f = "\<lambda>z. z * H12", OF step0]
      by (simp add: algebra_simps)
    also have "\<dots> = a2 * H12 * M - a1 * (L * H12)"
      by (simp add: algebra_simps)
    also have "\<dots> = a2 * H12 * M - a1 * (H22 * M)"
      by (simp add: e1)
    also have "\<dots> = (a2 * H12 - a1 * H22) * M"
      by (simp add: algebra_simps)
    finally show ?thesis by (simp add: algebra_simps)
  qed
  have aH12nz: "a * H12 \<noteq> 0" using a h12 by simp
  show "K / M = (a2 * H12 - a1 * H22) / (a * H12)"
    using frac_eq_eq[OF Mnz aH12nz] e2 by (simp add: algebra_simps)
qed

end
