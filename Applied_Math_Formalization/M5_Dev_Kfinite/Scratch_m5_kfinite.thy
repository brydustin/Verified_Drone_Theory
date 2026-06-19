theory Scratch_m5_kfinite
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>(M5) stub D2 --- finiteness of the beam-center witness-angle set.

  Target (verbatim from the D2 dev file):

    \<open>finite {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}\<close>.

  Mirrors the D5 finite-witness confinement technique (finite \<open>S1 \<times> S2\<close> via
  @{thm finite_cos_zeros_interval} and @{thm finite_phase_zeros_interval}).

  The MATH.  At a witness, \<open>cos (\<omega>$1) = 0\<close> pins \<open>\<omega>$1\<close> to the finite cos-zero set
  inside the box (@{thm finite_cos_zeros_interval}); and \<open>cos(\<omega>$1)=0 \<Longrightarrow> sin(\<omega>$1) \<noteq> 0\<close>.
  Reading the two scalar equations \<open>cvec\<^sub>1 = cvec\<^sub>2 = 0\<close> at such a \<open>\<omega>\<close>:
    \<open>sin(\<omega>$1) * cos(\<omega>$2) = P\<close>, \<open>sin(\<omega>$1) * sin(\<omega>$2) = Q\<close>,
  with constants \<open>P = kx \<omega>s + Ac * kz \<omega>s\<close>, \<open>Q = ky \<omega>s + Bc * kz \<omega>s\<close> (using \<open>kz \<omega> = 0\<close>).
  Eliminating \<open>sin(\<omega>$1)\<close> (multiply the equations crosswise and subtract) gives the
  phase equation \<open>Q * cos(\<omega>$2) - P * sin(\<omega>$2) = 0\<close>; with \<open>(P,Q) \<noteq> (0,0)\<close> this pins
  \<open>\<omega>$2\<close> to a \<open>\<pi>\<int>\<close>-coset --- finite inside the box (@{thm finite_phase_zeros_interval}).
  If \<open>(P,Q) = (0,0)\<close> the witness set is empty (would force \<open>cos(\<omega>$2)=sin(\<omega>$2)=0\<close>).\<close>


subsection \<open>Scalar components of the steering vector\<close>

text \<open>The two entries of @{const cvec_dip} as real scalars.\<close>

lemma cvec_dip_component1:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2"
  shows "cvec_dip \<omega>0 \<omega>s \<omega> $ 1
       = (kx \<omega> - kx \<omega>s) + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)"
  unfolding cvec_dip_def by (simp add: axis_def)

lemma cvec_dip_component2:
  fixes \<omega>0 \<omega>s \<omega> :: "real^2"
  shows "cvec_dip \<omega>0 \<omega>s \<omega> $ 2
       = (ky \<omega> - ky \<omega>s) + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)"
  unfolding cvec_dip_def by (simp add: axis_def)


subsection \<open>Finiteness of the beam-center witness-angle set\<close>

lemma m5_D2_beamcenter_K_finite:
  fixes ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  shows "finite {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
proof -
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  \<comment> \<open>The two fixed phase constants (the values of the components at \<open>cos(\<omega>$1)=0\<close>).\<close>
  define P :: real where "P = kx \<omega>s + Ac * kz \<omega>s"
  define Q :: real where "Q = ky \<omega>s + Bc * kz \<omega>s"
  define KK :: "(real^2) set" where
    "KK = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  text \<open>For every witness in \<open>KK\<close> the two scalar steering equations hold.\<close>
  have eqPQ: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P \<and> sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
    if wKK: "\<omega> \<in> KK" for \<omega> :: "real^2"
  proof -
    have cz: "cos (\<omega> $ 1) = 0" using wKK by (simp add: KK_def)
    have c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wKK by (simp add: KK_def)
    have kzw: "kz \<omega> = 0" using cz by (simp add: kz_def)
    \<comment> \<open>Component 1 = 0 and component 2 = 0.\<close>
    have c01: "cvec_dip \<omega>0 \<omega>s \<omega> $ 1 = 0" using c0 by simp
    have c02: "cvec_dip \<omega>0 \<omega>s \<omega> $ 2 = 0" using c0 by simp
    have e1: "(kx \<omega> - kx \<omega>s) + Ac * (kz \<omega> - kz \<omega>s) = 0"
      using c01 unfolding Ac_def by (simp add: cvec_dip_component1)
    have e2: "(ky \<omega> - ky \<omega>s) + Bc * (kz \<omega> - kz \<omega>s) = 0"
      using c02 unfolding Bc_def by (simp add: cvec_dip_component2)
    \<comment> \<open>With \<open>kz \<omega> = 0\<close> the components read \<open>kx \<omega> = P\<close>, \<open>ky \<omega> = Q\<close>.\<close>
    have kxw: "kx \<omega> = P" using e1 kzw unfolding P_def by simp
    have kyw: "ky \<omega> = Q" using e2 kzw unfolding Q_def by simp
    have "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P" using kxw by (simp add: kx_def)
    moreover have "sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q" using kyw by (simp add: ky_def)
    ultimately show ?thesis by blast
  qed
  text \<open>The phase coefficients \<open>(Q, -P)\<close> are not both zero, provided \<open>KK \<noteq> {}\<close>.\<close>
  have ABnz: "Q \<noteq> 0 \<or> - P \<noteq> 0" if wKK: "\<omega> \<in> KK" for \<omega> :: "real^2"
  proof (rule ccontr)
    assume "\<not> (Q \<noteq> 0 \<or> - P \<noteq> 0)"
    hence P0: "P = 0" and Q0: "Q = 0" by auto
    have cz: "cos (\<omega> $ 1) = 0" using wKK by (simp add: KK_def)
    have "(sin (\<omega> $ 1))\<^sup>2 = 1" using sin_cos_squared_add[of "\<omega> $ 1"] cz by simp
    hence s1: "sin (\<omega> $ 1) \<noteq> 0" by auto
    have pq: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P \<and> sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
      by (rule eqPQ[OF wKK])
    have "cos (\<omega> $ 2) = 0" using pq P0 s1 by simp
    moreover have "sin (\<omega> $ 2) = 0" using pq Q0 s1 by simp
    ultimately show False
      using sin_cos_squared_add2[of "\<omega> $ 2"] by simp
  qed
  text \<open>The phase equation \<open>Q * cos(\<omega>$2) - P * sin(\<omega>$2) = 0\<close> holds at every witness.\<close>
  have phase0: "Q * cos (\<omega> $ 2) + (- P) * sin (\<omega> $ 2) = 0"
    if wKK: "\<omega> \<in> KK" for \<omega> :: "real^2"
  proof -
    have pq: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P \<and> sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
      by (rule eqPQ[OF wKK])
    have a: "P = sin (\<omega> $ 1) * cos (\<omega> $ 2)" using pq by blast
    have b: "Q = sin (\<omega> $ 1) * sin (\<omega> $ 2)" using pq by blast
    \<comment> \<open>Substitute \<open>P, Q\<close> and cancel: \<open>sin(\<omega>1)*(sin*cos - cos*sin) = 0\<close>.\<close>
    show ?thesis unfolding a b by (simp add: algebra_simps)
  qed
  text \<open>Confine \<open>KK\<close> into the finite box-product \<open>S1 \<times> S2\<close>.\<close>
  define S1 :: "real set" where
    "S1 = {t::real. ctr $ 1 - \<delta> \<le> t \<and> t \<le> ctr $ 1 + \<delta> \<and> cos t = 0}"
  define S2 :: "real set" where
    "S2 = {u::real. ctr $ 2 - pi \<le> u \<and> u \<le> ctr $ 2 + pi
            \<and> Q * cos u + (- P) * sin u = 0}"
  have finS1: "finite S1" unfolding S1_def by (rule finite_cos_zeros_interval)
  show ?thesis
  proof (cases "KK = {}")
    case True
    show ?thesis unfolding KK_def[symmetric] using True by simp
  next
    case False
    then obtain \<omega>w :: "real^2" where wmem: "\<omega>w \<in> KK" by blast
    have ABnz': "Q \<noteq> 0 \<or> - P \<noteq> 0" by (rule ABnz[OF wmem])
    have finS2: "finite S2"
      unfolding S2_def by (rule finite_phase_zeros_interval[OF ABnz'])
    have Ksub: "KK \<subseteq> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
    proof
      fix \<omega> :: "real^2" assume wK: "\<omega> \<in> KK"
      have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: KK_def)
      have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: KK_def)
      have pz: "Q * cos (\<omega> $ 2) + (- P) * sin (\<omega> $ 2) = 0" by (rule phase0[OF wK])
      have bnds: "ctr $ 1 - \<delta> \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> ctr $ 1 + \<delta>
                \<and> ctr $ 2 - pi \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> ctr $ 2 + pi"
        by (rule OmegaPF_component_bounds[OF wD])
      have mem: "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2"
        using bnds cz pz by (auto simp: S1_def S2_def)
      show "\<omega> \<in> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
      proof (rule image_eqI[where x = "(\<omega> $ 1, \<omega> $ 2)"])
        show "\<omega> = (\<lambda>(t, u). vector [t, u] :: real^2) (\<omega> $ 1, \<omega> $ 2)"
          by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
        show "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2" by (rule mem)
      qed
    qed
    have finK: "finite KK"
      by (rule finite_subset[OF Ksub
            finite_imageI[OF finite_cartesian_product[OF finS1 finS2]]])
    show ?thesis using finK by (simp add: KK_def)
  qed
qed

end
