section \<open>Degenerate critical points where the steering map is singular\<close>

theory Steering_Singular_Stratum
  imports
    Main_Beam_Stratum
begin

lemma Dcvec_det_eq:
    fixes \<omega>0 \<omega>s \<omega> :: "real^2"
    shows "matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))
           = sin (\<omega>$1) * (cos (\<omega>$1)
               - sin (\<omega>$1) * (((kx \<omega>0 - kx
  \<omega>s)/(kz \<omega>s - kz \<omega>0)) * cos (\<omega>$2)
                            + ((ky \<omega>0 - ky \<omega>s)/(kz
  \<omega>s - kz \<omega>0)) * sin (\<omega>$2)))"
proof -
  have "cos (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 2) * cos (vec_nth \<omega> 2))) + 
           (cos (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 2) * sin (vec_nth \<omega> 2))) + 
           ((kx \<omega>0 * (sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2))) - 
             kx \<omega>s * (sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)))) / 
            (kz \<omega>s - kz \<omega>0) + (kx \<omega>s * (sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2))) - 
             kx \<omega>0 * (sin (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * cos (vec_nth \<omega> 2)))) / (kz \<omega>s - kz \<omega>0))) =
       cos (vec_nth \<omega> 1) * (sin (vec_nth \<omega> 1) * (cos (vec_nth \<omega> 2) * cos (vec_nth \<omega> 2) + sin (vec_nth \<omega> 2) * sin (vec_nth \<omega> 2)))"
    by argo
  then show ?thesis
    by (simp add: det_2 matrix_def Dcvec_dip_def axis_def sin_cos_squared_add[of "\<omega>$2"]
  algebra_simps)
qed

lemma steering_slice_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes card2: "2 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> = 0")
  case True
  show ?thesis
    by (rule beamcenter_angle_meager[OF card2 pfw True])
next
  case False
  have nd: "nowhere_dense {x::(real^2)^'n. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    by (rule critical_slice_nowhere_dense[OF card2 pfw False])
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}
        \<subseteq> {x::(real^2)^'n. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_nowhere_dense[OF nd]])
qed

lemma meager_steering_singular:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes card2: "2 \<le> CARD('n)"
    and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
    and hsep: "kz \<omega>s \<noteq> kz \<omega>0"
    and kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (jacobian (cvec_dip \<omega>0 \<omega>s) (at \<omega>)) = 0}"
proof -
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0
            \<and> Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0}"
  define slice :: "real^2 \<Rightarrow> ((real^2)^'n) set" where
    "slice \<omega> = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}" for \<omega> :: "real^2"
  text \<open>The phase coefficients are not both zero.\<close>
  have D0: "kz \<omega>s - kz \<omega>0 \<noteq> 0" using hsep by simp
  have ABnz: "Ac \<noteq> 0 \<or> Bc \<noteq> 0"
    using kdiff D0 unfolding Ac_def Bc_def by (auto simp: divide_eq_0_iff)
  text \<open>The witness-angle set \<open>K\<close> is finite.\<close>
  define S1 :: "real set" where
    "S1 = {t::real. ctr $ 1 - \<delta> \<le> t \<and> t \<le> ctr $ 1 + \<delta> \<and> cos t = 0}"
  define S2 :: "real set" where
    "S2 = {u::real. ctr $ 2 - pi \<le> u \<and> u \<le> ctr $ 2 + pi
            \<and> Ac * cos u + Bc * sin u = 0}"
  have finS1: "finite S1" unfolding S1_def by (rule finite_cos_zeros_interval)
  have finS2: "finite S2" unfolding S2_def by (rule finite_phase_zeros_interval[OF ABnz])
  have Ksub: "K \<subseteq> (\<lambda>(t, u). vector [t, u] :: real^2) ` (S1 \<times> S2)"
  proof
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have cz: "cos (\<omega> $ 1) = 0" using wK by (simp add: K_def)
    have pz: "Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0" using wK by (simp add: K_def)
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
  have finK: "finite K"
    by (rule finite_subset[OF Ksub
          finite_imageI[OF finite_cartesian_product[OF finS1 finS2]]])
  text \<open>Every witness angle lies in \<open>K\<close>.\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}
             \<subseteq> (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
    then obtain \<omega> :: "real^2" where wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and hz: "matrix_det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and dz: "matrix_det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
      by blast
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    have gd0: "frechet_derivative gdip (at (\<omega> $ 1)) 1 = 0"
      by (rule steering_singular_gdip_deriv_zero[OF s1 g0 anz dz])
    have cz: "cos (\<omega> $ 1) = 0"
      by (rule iffD1[OF gdip_deriv_zero_iff[OF s1] gd0])
    have e: "sin (\<omega> $ 1) * (cos (\<omega> $ 1)
               - sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2))) = 0"
      using dz by (simp add: Dcvec_det_eq Ac_def Bc_def)
    have e2: "cos (\<omega> $ 1) - sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2)) = 0"
      using mult_eq_0_iff[THEN iffD1, OF e] s1 by blast
    have e3: "sin (\<omega> $ 1) * (Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2)) = 0"
      using e2 cz by simp
    have q0: "Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0"
      using mult_eq_0_iff[THEN iffD1, OF e3] s1 by blast
    have wK: "\<omega> \<in> K" using wD cz q0 by (simp add: K_def)
    have xs: "x \<in> slice \<omega>" using g0 anz hz by (simp add: slice_def)
    show "x \<in> (\<Union>\<omega>\<in>K. slice \<omega>)"
    proof (rule UN_I)
      show "\<omega> \<in> K" by (rule wK)
      show "x \<in> slice \<omega>" by (rule xs)
    qed
  qed
  text \<open>Each slice over a fixed angle in \<open>K\<close> is meager; the finite union is meager.\<close>
  have meagU: "meager (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof (rule meager_Union_finite[OF finK])
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    show "meager (slice \<omega>)"
      unfolding slice_def
      by (rule steering_slice_meager[OF card2 s1])
  qed
  show ?thesis unfolding jacobian_cvec_dip by (rule meager_subset[OF sub meagU])
qed

end
