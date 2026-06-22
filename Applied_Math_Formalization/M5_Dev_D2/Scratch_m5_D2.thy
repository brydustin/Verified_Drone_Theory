theory Scratch_m5_D2
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>(M5) stub D2 --- the beam-center stratum \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>.

  Development scaffold.  Structural skeleton: at a beam-center witness angle the
  \<open>gradU = 0\<close> conjunct forces \<open>cos(\<omega>$1) = 0\<close> (criticality of the dipole gain),
  so the witness angle set is confined to a finite set; each fixed-angle slice
  is then handled by the slice machinery.\<close>

section \<open>Probe: structure of \<open>gradU\<close> at a beam center (cvec = 0)\<close>

text \<open>At \<open>c = cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close> the steering vector vanishes, so all moments
  are real: \<open>M_paper x 0 = (N, \<Sum>x\<^sub>n\<^sub>1, \<Sum>x\<^sub>n\<^sub>2, \<dots>)\<close> with \<open>N = CARD('n)\<close>.\<close>

lemma M_paper_at_zero_A:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 1 = of_nat CARD('n)"
proof -
  have "A_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). cis 0)"
    by (simp add: A_moment_def phase_def)
  also have "\<dots> = of_nat CARD('n)" by simp
  finally show ?thesis by simp
qed

text \<open>At \<open>c = 0\<close> every moment is real (the phase factor is \<open>1\<close>).\<close>

lemma M_paper_at_zero_M1:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 2 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
proof -
  have "M1_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 1) * cis 0)"
    by (simp add: M1_moment_def phase_def)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 1))" by simp
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)" by simp
  finally show ?thesis by simp
qed

lemma M_paper_at_zero_M2:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 3 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
proof -
  have "M2_moment x 0 = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 2) * cis 0)"
    by (simp add: M2_moment_def phase_def)
  also have "\<dots> = (\<Sum>n\<in>(UNIV::'n set). of_real ((x $ n) $ 2))" by simp
  also have "\<dots> = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)" by simp
  finally show ?thesis by simp
qed

text \<open>The first three moments are real at \<open>c = 0\<close>.\<close>

lemma M_paper_at_zero_real123:
  fixes x :: "(real^2)^'n"
  shows "M_paper x 0 $ 1 = of_real (Re (M_paper x 0 $ 1))"
    and "M_paper x 0 $ 2 = of_real (Re (M_paper x 0 $ 2))"
    and "M_paper x 0 $ 3 = of_real (Re (M_paper x 0 $ 3))"
proof -
  have e1: "M_paper x 0 $ 1 = of_real (real CARD('n))"
    using M_paper_at_zero_A[of x] by (metis of_real_of_nat_eq)
  have e2: "M_paper x 0 $ 2 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 1)"
    by (rule M_paper_at_zero_M1)
  have e3: "M_paper x 0 $ 3 = of_real (\<Sum>n\<in>(UNIV::'n set). (x $ n) $ 2)"
    by (rule M_paper_at_zero_M2)
  show "M_paper x 0 $ 1 = of_real (Re (M_paper x 0 $ 1))"
    by (subst e1)+ simp
  show "M_paper x 0 $ 2 = of_real (Re (M_paper x 0 $ 2))"
    by (subst e2)+ simp
  show "M_paper x 0 $ 3 = of_real (Re (M_paper x 0 $ 3))"
    by (subst e3)+ simp
qed

section \<open>gradU at a beam center forces \<open>cos(\<omega>$1) = 0\<close>\<close>

text \<open>If \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close> then the moment-space steering term in \<open>gradU\<close>
  vanishes (real moments \<open>\<Rightarrow>\<close> the \<open>Re(cnj A \<cdot> (-\<ii>) \<cdot> real)\<close> term is \<open>0\<close>), so
  \<open>gradU $ j = gdip'(\<theta>) \<cdot> (axis j 1)$1 \<cdot> N\<^sup>2\<close>: component 2 is automatically zero,
  and component 1 vanishes iff \<open>gdip'(\<theta>) = 0\<close>.\<close>

lemma gradU_at_beamcenter_component:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
       = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
           * (cmod (M_paper x 0 $ 1))\<^sup>2"
proof -
  define A where "A = M_paper x 0 $ 1"
  define M2 where "M2 = M_paper x 0 $ 2"
  define M3 where "M3 = M_paper x 0 $ 3"
  define dj1 where "dj1 = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1"
  define dj2 where "dj2 = (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2"
  have Ar: "A = of_real (Re A)" unfolding A_def by (rule M_paper_at_zero_real123(1))
  have M2r: "M2 = of_real (Re M2)" unfolding M2_def by (rule M_paper_at_zero_real123(2))
  have M3r: "M3 = of_real (Re M3)" unfolding M3_def by (rule M_paper_at_zero_real123(3))
  text \<open>The steering term: \<open>Re(cnj A \<cdot> ((-\<ii>) dj1 M2 + (-\<ii>) dj2 M3))\<close> is the real
    part of a purely-imaginary complex number, hence zero.\<close>
  have steer0: "Re (cnj A * ((- \<i>) * complex_of_real dj1 * M2
                            + (- \<i>) * complex_of_real dj2 * M3)) = 0"
  proof -
    have "cnj A * ((- \<i>) * complex_of_real dj1 * M2 + (- \<i>) * complex_of_real dj2 * M3)
        = of_real (Re A) * ((- \<i>) * complex_of_real dj1 * of_real (Re M2)
                          + (- \<i>) * complex_of_real dj2 * of_real (Re M3))"
      using Ar M2r M3r by (metis Complex.complex_cnj_complex_of_real)
    also have "\<dots> = complex_of_real (Re A * (dj1 * Re M2 + dj2 * Re M3)) * (- \<i>)"
      by (simp add: algebra_simps)
    finally have "cnj A * ((- \<i>) * complex_of_real dj1 * M2 + (- \<i>) * complex_of_real dj2 * M3)
                = complex_of_real (Re A * (dj1 * Re M2 + dj2 * Re M3)) * (- \<i>)" .
    thus ?thesis by simp
  qed
  have base: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ j
       = frechet_derivative gdip (at (\<omega>$1)) ((axis j 1)$1)
             * (cmod (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1))\<^sup>2
           + gain_dip \<omega> * (2 * Re (cnj (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 1)
                * ((- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$1)
                     * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 2)
                 + (- \<i>) * complex_of_real ((Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1))$2)
                     * (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>) $ 3))))"
    by (rule gradU_dip_component_moments)
  show ?thesis
    unfolding base c0
    using steer0 unfolding A_def M2_def M3_def dj1_def dj2_def by simp
qed

text \<open>The first gradient component at a beam center is \<open>gdip'(\<theta>) \<cdot> N\<^sup>2\<close>.\<close>

lemma gradU_at_beamcenter_comp1:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
       = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
proof -
  have a1: "((axis (1::2) 1 :: real^2) $ 1) = 1" by (simp add: axis_def)
  have NA: "cmod (M_paper x 0 $ 1) = real CARD('n)"
    using M_paper_at_zero_A[of x] by (simp add: norm_of_nat)
  have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1
       = frechet_derivative gdip (at (\<omega>$1)) ((axis (1::2) 1)$1)
           * (cmod (M_paper x 0 $ 1))\<^sup>2"
    by (rule gradU_at_beamcenter_component[OF c0, of x 1])
  also have "\<dots> = frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2"
    by (subst a1, subst NA, rule refl)
  finally show ?thesis .
qed

text \<open>Criticality at a beam center (off the poles) forces \<open>cos(\<omega>$1) = 0\<close>.\<close>

lemma beamcenter_critical_cos_zero:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and s1: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
    and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "cos (\<omega> $ 1) = 0"
proof -
  have Npos: "(0::real) < real CARD('n)" using c6 by simp
  have "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 = 0" using g0 by simp
  hence "frechet_derivative gdip (at (\<omega>$1)) 1 * (real CARD('n))\<^sup>2 = 0"
    using gradU_at_beamcenter_comp1[OF c0, of x] by simp
  hence gd0: "frechet_derivative gdip (at (\<omega>$1)) 1 = 0"
    using Npos by simp
  show ?thesis by (rule iffD1[OF gdip_deriv_zero_iff[OF s1] gd0])
qed


section \<open>Finiteness of the beam-center witness-angle set (scoped genuine-math sorry)\<close>

text \<open>\<^bold>\<open>The beam-center witness-angle set is finite.\<close>  Every witness angle \<open>\<omega>\<close> in the
  D2 bad set is \<^emph>\<open>critical\<close> (\<open>gradU = 0\<close>) at a beam center (\<open>cvec = 0\<close>) off the
  poles (\<open>sin (\<omega>\<^sub>1) \<noteq> 0\<close>), so by @{thm beamcenter_critical_cos_zero} it satisfies
  \<open>cos (\<omega>\<^sub>1) = 0\<close>.  Thus the witness angles confine to
    \<open>K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega>\<^sub>1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}\<close>.
  This set is FINITE: \<open>cos (\<omega>\<^sub>1) = 0\<close> pins \<open>\<omega>\<^sub>1\<close> to the finite cos-zero set inside the
  box (@{thm finite_cos_zeros_interval}); and at any such \<open>\<omega>\<^sub>1\<close> (where
  \<open>sin (\<omega>\<^sub>1) = \<plusminus>1\<close>, \<open>kz \<omega> = 0\<close>), the two equations \<open>cvec\<^sub>1 = cvec\<^sub>2 = 0\<close> read
  \<open>sin (\<omega>\<^sub>1) \<cdot> cos (\<omega>\<^sub>2) = P\<close>, \<open>sin (\<omega>\<^sub>1) \<cdot> sin (\<omega>\<^sub>2) = Q\<close> (constants
  \<open>P = kx \<omega>s + Ac \<cdot> kz \<omega>s\<close>, \<open>Q = ky \<omega>s + Bc \<cdot> kz \<omega>s\<close> with \<open>P\<^sup>2 + Q\<^sup>2 = sin\<^sup>2(\<omega>\<^sub>1) = 1\<close>),
  which by @{thm sin_cos_eq_iff} pin \<open>\<omega>\<^sub>2\<close> to a \<open>2\<pi>\<int>\<close>-coset --- finite inside the box
  (@{thm finite_affine_int_zeros}).  The full carve-out is the genuine remaining
  analytic step; we carry the resulting finiteness as a single scoped \<open>sorry\<close>.\<close>

lemma m5_D2_beamcenter_K_finite:
  fixes ctr \<omega>0 \<omega>s :: "real^2" and \<delta> :: real
  shows "finite {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  \<comment> \<open>GENUINE remaining math (now discharged): at \<open>cos(\<omega>\<^sub>1)=0\<close> (so \<open>kz \<omega>=0\<close>,
      \<open>sin(\<omega>\<^sub>1)=\<plusminus>1\<close>) the two scalar equations \<open>cvec\<^sub>1=cvec\<^sub>2=0\<close> read
      \<open>sin(\<omega>\<^sub>1)\<cdot>cos(\<omega>\<^sub>2)=P\<close>, \<open>sin(\<omega>\<^sub>1)\<cdot>sin(\<omega>\<^sub>2)=Q\<close> with constants
      \<open>P=kx \<omega>s+Ac\<cdot>kz \<omega>s\<close>, \<open>Q=ky \<omega>s+Bc\<cdot>kz \<omega>s\<close> (\<open>Ac,Bc\<close> the usual ratios).
      Eliminating \<open>sin(\<omega>\<^sub>1)\<close> gives the phase relation \<open>Q\<cdot>cos(\<omega>\<^sub>2)-P\<cdot>sin(\<omega>\<^sub>2)=0\<close>;
      if \<open>P=Q=0\<close> the locus is empty (forces \<open>cos\<^sup>2+sin\<^sup>2=0\<close>), else the phase
      relation has finitely many \<open>\<omega>\<^sub>2\<close> in the box (@{thm finite_phase_zeros_interval});
      \<open>cos(\<omega>\<^sub>1)=0\<close> pins \<open>\<omega>\<^sub>1\<close> to a finite set (@{thm finite_cos_zeros_interval}).\<close>
proof -
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define P :: real where "P = kx \<omega>s + Ac * kz \<omega>s"
  define Q :: real where "Q = ky \<omega>s + Bc * kz \<omega>s"
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  \<comment> \<open>The two scalar beam-center equations at \<open>cos(\<omega>\<^sub>1)=0\<close>.\<close>
  have eqs: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P \<and> sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
    if cz: "cos (\<omega> $ 1) = 0" and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" for \<omega> :: "real^2"
  proof -
    have kzw: "kz \<omega> = 0" using cz by (simp add: kz_def)
    have c1: "cvec_dip \<omega>0 \<omega>s \<omega> $ 1 = 0" and c2: "cvec_dip \<omega>0 \<omega>s \<omega> $ 2 = 0"
      using c0 by simp_all
    have e1: "(kx \<omega> - kx \<omega>s) + Ac * (kz \<omega> - kz \<omega>s) = 0"
      using c1 unfolding cvec_dip_def Ac_def by (simp add: axis_def)
    have e2: "(ky \<omega> - ky \<omega>s) + Bc * (kz \<omega> - kz \<omega>s) = 0"
      using c2 unfolding cvec_dip_def Bc_def by (simp add: axis_def)
    have p1: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P"
      using e1 kzw unfolding P_def kx_def by (simp add: algebra_simps)
    have p2: "sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
      using e2 kzw unfolding Q_def ky_def by (simp add: algebra_simps)
    show ?thesis using p1 p2 by blast
  qed
  \<comment> \<open>The \<open>\<omega>\<^sub>1\<close> coordinate ranges over the finite cos-zero set inside the box.\<close>
  define S1 :: "real set" where
    "S1 = {t::real. ctr $ 1 - \<delta> \<le> t \<and> t \<le> ctr $ 1 + \<delta> \<and> cos t = 0}"
  have finS1: "finite S1" unfolding S1_def by (rule finite_cos_zeros_interval)
  show ?thesis
  proof (cases "P = 0 \<and> Q = 0")
    case True
    \<comment> \<open>\<open>P=Q=0\<close>: any witness forces \<open>cos(\<omega>\<^sub>2)=sin(\<omega>\<^sub>2)=0\<close>, impossible; \<open>K\<close> is empty.\<close>
    have "K = {}"
    proof (rule ccontr)
      assume "K \<noteq> {}"
      then obtain \<omega> :: "real^2" where wK: "\<omega> \<in> K" by blast
      have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
      have c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
      have s1: "sin (\<omega> $ 1) \<noteq> 0"
      proof -
        have "sin (\<omega> $ 1) ^ 2 = 1"
          using sin_cos_squared_add[of "\<omega> $ 1"] cz by simp
        thus ?thesis by (auto simp: power2_eq_square)
      qed
      have "sin (\<omega> $ 1) * cos (\<omega> $ 2) = 0" "sin (\<omega> $ 1) * sin (\<omega> $ 2) = 0"
        using eqs[OF cz c0] True by simp_all
      hence "cos (\<omega> $ 2) = 0" "sin (\<omega> $ 2) = 0" using s1 by simp_all
      thus False using sin_cos_squared_add[of "\<omega> $ 2"] by simp
    qed
    thus ?thesis by (simp flip: K_def)
  next
    case False
    hence ABnz: "Q \<noteq> 0 \<or> - P \<noteq> 0" by auto
    \<comment> \<open>\<open>\<omega>\<^sub>2\<close> ranges over the finite zero set of the phase form \<open>Q\<cdot>cos - P\<cdot>sin\<close>.\<close>
    define S2 :: "real set" where
      "S2 = {u::real. ctr $ 2 - pi \<le> u \<and> u \<le> ctr $ 2 + pi
              \<and> Q * cos u + (- P) * sin u = 0}"
    have finS2: "finite S2" unfolding S2_def by (rule finite_phase_zeros_interval[OF ABnz])
    have Ksub: "K \<subseteq> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
    proof
      fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
      have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
      have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
      have c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
      have bnds: "ctr $ 1 - \<delta> \<le> \<omega> $ 1 \<and> \<omega> $ 1 \<le> ctr $ 1 + \<delta>
                \<and> ctr $ 2 - pi \<le> \<omega> $ 2 \<and> \<omega> $ 2 \<le> ctr $ 2 + pi"
        by (rule OmegaPF_component_bounds[OF wD])
      have p1: "sin (\<omega> $ 1) * cos (\<omega> $ 2) = P"
        and p2: "sin (\<omega> $ 1) * sin (\<omega> $ 2) = Q"
        using eqs[OF cz c0] by simp_all
      \<comment> \<open>Eliminate \<open>sin(\<omega>\<^sub>1)\<close>: \<open>Q\<cdot>cos(\<omega>\<^sub>2) - P\<cdot>sin(\<omega>\<^sub>2) = sin(\<omega>\<^sub>1)\<cdot>(Q\<cdot>cos\<cdot>... )\<close>.\<close>
      have pz: "Q * cos (\<omega> $ 2) + (- P) * sin (\<omega> $ 2) = 0"
      proof -
        have "Q * cos (\<omega> $ 2) + (- P) * sin (\<omega> $ 2)
            = (sin (\<omega> $ 1) * sin (\<omega> $ 2)) * cos (\<omega> $ 2)
            - (sin (\<omega> $ 1) * cos (\<omega> $ 2)) * sin (\<omega> $ 2)"
          by (simp add: p1[symmetric] p2[symmetric])
        also have "\<dots> = 0" by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      have mem: "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2"
        using bnds cz pz by (auto simp: S1_def S2_def)
      show "\<omega> \<in> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
      proof (rule image_eqI[where x = "(\<omega> $ 1, \<omega> $ 2)"])
        show "\<omega> = (\<lambda>(t, u). vector [t, u] :: real^2) (\<omega> $ 1, \<omega> $ 2)"
          by (simp add: Finite_Cartesian_Product.vec_eq_iff forall_2)
        show "(\<omega> $ 1, \<omega> $ 2) \<in> S1 \<times> S2" by (rule mem)
      qed
    qed
    have "finite K"
      by (rule finite_subset[OF Ksub
            finite_imageI[OF finite_cartesian_product[OF finS1 finS2]]])
    thus ?thesis by (simp flip: K_def)
  qed
qed


section \<open>The per-beam-center-angle slice is nowhere dense (scoped genuine-math sorry)\<close>

text \<open>For a beam-center angle \<open>\<omega>\<close> (\<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>) with \<open>sin (\<omega>\<^sub>1) \<noteq> 0\<close> and a
  nonsingular steering Jacobian, the configurations \<open>x\<close> carrying a degenerate critical
  point with nonzero array factor form a nowhere-dense set.  This is the det-Hessian
  covariance-polynomial payload: with \<open>cvec = 0\<close> the Hessian collapses to
  \<open>N\<^sup>2 gdip''(\<pi>/2) e1 e1\<^sup>T + C\<^sup>T(-2N Cov x) C\<close>, whose vanishing determinant is a
  nontrivial polynomial in the (real) moments of \<open>x\<close> --- nontrivial because
  \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close> --- so its zero set is nowhere dense.  Carried as
  a single scoped \<open>sorry\<close>.\<close>

lemma m5_D2_slice_nowhere_dense:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)"
    and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "nowhere_dense {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
  \<comment> \<open>GENUINE remaining math: the det-Hessian covariance polynomial at a beam center
      (\<open>gdip''(\<pi>/2) \<noteq> 0\<close>) cuts out a positive-codimension (nowhere-dense) \<open>x\<close>-set.
      NOT a Robust3 freebie.\<close>
  sorry


section \<open>Assembly: \<open>m5_D2_beamcenter\<close> from finite \<open>K\<close> + nowhere-dense slices\<close>

text \<open>The exact target statement (verbatim from the M5 skeleton), closed by witness
  confinement to the finite beam-center angle set \<open>K\<close>, a finite union of
  nowhere-dense per-angle slices (@{thm meager_Union_finite} + @{thm
  meager_nowhere_dense}), and @{thm meager_subset}.  Two facts make the confinement
  work \<^emph>\<open>x\<close>-universally at a beam center: the \<open>\<not> surj (DM_paper_x x 0)\<close> conjunct is
  automatic (@{thm DM_paper_x_null_not_surj}), so it drops out of the slice; and
  critical witnesses satisfy \<open>cos (\<omega>\<^sub>1) = 0\<close> (@{thm beamcenter_critical_cos_zero}),
  pinning the witness angle into the finite \<open>K\<close>.  Sorry-free at this assembly layer.\<close>

lemma m5_D2_beamcenter:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
proof -
  \<comment> \<open>The finite beam-center witness-angle set (\<open>cos(\<omega>\<^sub>1)=0\<close> from criticality, \<open>cvec=0\<close>).\<close>
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  have finK: "finite K"
    unfolding K_def by (rule m5_D2_beamcenter_K_finite)
  \<comment> \<open>The det-Hessian covariance slice at a fixed beam-center angle.\<close>
  define slice :: "real^2 \<Rightarrow> ((real^2)^'n) set" where
    "slice \<omega> = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}" for \<omega> :: "real^2"
  \<comment> \<open>Witness confinement: every bad witness angle lies in \<open>K\<close>, and the configuration
       lies in the corresponding slice.  The \<open>\<not> surj\<close> conjunct is dropped (automatic
       at a beam center), and \<open>cos(\<omega>\<^sub>1)=0\<close> comes from criticality.\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}
             \<subseteq> (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
    then obtain \<omega> :: "real^2" where wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and hz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and dnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      and cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
      by blast
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    have cosz: "cos (\<omega> $ 1) = 0"
      by (rule beamcenter_critical_cos_zero[OF c6 s1 cz g0])
    have wK: "\<omega> \<in> K" using wD cosz cz by (simp add: K_def)
    have xs: "x \<in> slice \<omega>"
      using g0 hz anz dnz by (simp add: slice_def)
    show "x \<in> (\<Union>\<omega>\<in>K. slice \<omega>)"
    proof (rule UN_I)
      show "\<omega> \<in> K" by (rule wK)
      show "x \<in> slice \<omega>" by (rule xs)
    qed
  qed
  \<comment> \<open>Each slice over a fixed beam-center angle is nowhere dense, hence meager; the
       finite union over \<open>K\<close> is meager; the bad set is contained in it.\<close>
  have meagU: "meager (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof (rule meager_Union_finite[OF finK])
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have cz: "cvec_dip \<omega>0 \<omega>s \<omega> = 0" using wK by (simp add: K_def)
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    show "meager (slice \<omega>)"
      unfolding slice_def
      by (rule meager_nowhere_dense[OF m5_D2_slice_nowhere_dense[OF c6 s1 cz]])
  qed
  show ?thesis by (rule meager_subset[OF sub meagU])
qed

end
