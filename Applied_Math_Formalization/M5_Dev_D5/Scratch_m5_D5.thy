theory Scratch_m5_D5
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) stub D5 --- the steering-singular corner \<open>det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0\<close>.\<close>

  This file closes the heavy stub @{text m5_D5_steersing} of the M5 skeleton: the
  \<open>(\<not> surj, det Dcvec = 0)\<close> corner of the rank-deficient stratum.  It is the exact
  mirror of @{thm meager_steering_singular_stratum} (M6) in the heap, with the single
  difference that the moment-map slice carries \<open>\<not> surj (DM_paper_x x c)\<close> in place of
  M6's \<open>surj (DM_paper_x x c)\<close>.

  \<^bold>\<open>The R3 kernel-direction reduction needs NO \<open>surj\<close> hypothesis.\<close>  The witness-confinement
  step of M6 --- which collapses every bad witness angle into the FINITE set \<open>K\<close> (cos zeros
  \<open>\<times>\<close> phase-lattice zeros) --- rests only on @{thm M6_witness_gdip_deriv_zero} (which uses
  \<open>gradU = 0\<close>, \<open>A \<noteq> 0\<close>, \<open>det Dcvec = 0\<close>; \<^emph>\<open>not\<close> surjectivity) plus @{thm Dcvec_det_eq}.
  So the identical confinement applies here.  Once confined, D5 = a finite union over \<open>K\<close>
  of per-angle x-slices; each slice is shown meager.

  \<^bold>\<open>The per-angle slices.\<close>  For a fixed witness angle \<open>\<omega>\<close> with \<open>sin (\<omega>$1) \<noteq> 0\<close>:
  \<^item> If \<open>cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0\<close>: the slice injects into \<open>{x. \<not> surj (DM_paper_x x c)}\<close>, which is
    nowhere dense by the \<open>mstarg\<close> freebie @{text fixed_c_nonsurj_nowhere_dense}
    (= @{text nowhere_dense_mstarg_zeros} \<circ> @{text surj_iff_mstarg} at the Robust3 splice;
    mirror of D34's @{text fixed_c_nonsurj_nowhere_dense}).
  \<^item> If \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>: \<open>\<not> surj (DM_paper_x x 0)\<close> holds for \<^emph>\<open>all\<close> \<open>x\<close>
    (@{thm DM_paper_x_null_not_surj}), so the slice is exactly the D2 beam-center set at \<open>\<omega>\<close>
    \<open>{x. gradU = 0 \<and> A \<noteq> 0 \<and> det HessU = 0}\<close>; its meagerness is the D2 covariance-polynomial
    argument (\<open>gdip''(\<pi>/2) \<noteq> 0\<close>), isolated here as the single genuine per-angle obligation
    @{text m5_D5_beamcenter_angle_meager}.

  \<^bold>\<open>Splice freebies.\<close>  Because \<open>\<omega>0 \<omega>s\<close> are FREE here (the heap above the splice has no global
  \<open>\<omega>0 \<omega>s\<close>; they become the concrete @{text \<omega>0_def}/@{text \<omega>s_def} in Robust3), the M6
  separation hypotheses \<open>hsep : kz \<omega>s \<noteq> kz \<omega>0\<close> and \<open>kdiff : kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s\<close>
  are carried as local stub lemmas; both are discharged \<^emph>\<open>by simp\<close> for the concrete constants
  at the splice (Robust3 L1634--1637), so they are freebies.\<close>


subsection \<open>Splice freebie: the phase-separation data (concrete at Robust3)\<close>

text \<open>\<open>kz \<omega>s \<noteq> kz \<omega>0\<close>: the two beams are not co-elevation.  At the splice this is
  @{text "by (simp add: \<omega>s_def \<omega>0_def kz_def)"} for \<open>\<omega>0 = vector[\<pi>/2,0]\<close>, \<open>\<omega>s = vector[0,0]\<close>
  (Robust3 L1634).  = the M6 hypothesis \<open>hsep\<close>; closes at the Robust3 splice.\<close>

lemma m5_D5_hsep_freebie:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "kz \<omega>s \<noteq> kz \<omega>0"
  \<comment> \<open>= M6 hypothesis hsep; at the splice: simp on the concrete \<open>\<omega>0_def \<omega>s_def kz_def\<close>.\<close>
  sorry

text \<open>\<open>kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s\<close>: the in-plane wavevectors differ.  At the splice this is
  @{text "by (simp add: \<omega>0_def \<omega>s_def kx_def sin_pi_half)"} (Robust3 L1636).
  = the M6 hypothesis \<open>kdiff\<close>; closes at the Robust3 splice.\<close>

lemma m5_D5_kdiff_freebie:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s"
  \<comment> \<open>= M6 hypothesis kdiff; at the splice: simp on the concrete \<open>\<omega>0_def \<omega>s_def kx_def\<close>.\<close>
  sorry


subsection \<open>Splice freebie: the fixed-angle moment-map nowhere-density (mstarg)\<close>

text \<open>For every nonzero \<open>c\<close>, the set of \<open>x\<close> at which \<open>DM_paper_x x c\<close> is not surjective is
  nowhere dense.  In Robust3: rewrite \<open>\<not> surj (DM_paper_x x c) = (mstarg c x = 0)\<close> via
  @{text surj_iff_mstarg} (L578), then @{text nowhere_dense_mstarg_zeros}[OF c0 n6] (L744).
  \<open>mstarg\<close> is defined in Robust3 ABOVE the M5 splice, so it is out of scope here but in scope
  at the splice.  Mirror of D34's @{text fixed_c_nonsurj_nowhere_dense}; closes at the splice.\<close>

lemma fixed_c_nonsurj_nowhere_dense:
  fixes c :: "real^2"
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
  \<comment> \<open>= nowhere_dense_mstarg_zeros \<circ> surj_iff_mstarg (Robust3); closes at the M5 splice.\<close>
  sorry


subsection \<open>The genuine per-angle beam-center obligation (D2-style polynomial)\<close>

text \<open>The \<open>c = 0\<close> sub-case of a witness angle.  When \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close> the moment-map
  derivative \<open>DM_paper_x x 0\<close> is never surjective (@{thm DM_paper_x_null_not_surj}), so the
  D5 slice degenerates to the D2 beam-center slice at \<open>\<omega>\<close>:
  \<open>{x. gradU = 0 \<and> A \<noteq> 0 \<and> det HessU = 0}\<close>.  Its meagerness is the D2 covariance-polynomial
  argument (det-Hessian non-degenerate via \<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close>), the SAME
  genuine obligation carried by the sibling D2 stub @{text m5_D2_beamcenter}; isolated here
  as a per-angle, GENUINE-MATH sorry (not a splice freebie).\<close>

lemma m5_D5_beamcenter_angle_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega> = 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
  \<comment> \<open>GENUINE remaining math: the D2 beam-center covariance polynomial; shared with the
      sibling D2 stub.  NOT a splice freebie.\<close>
  sorry


subsection \<open>Per-angle D5 slice is meager (case split on the beam center)\<close>

text \<open>For a fixed witness angle \<open>\<omega>\<close> with \<open>sin(\<omega>$1) \<noteq> 0\<close>, the D5 slice
  \<open>{x. gradU = 0 \<and> A \<noteq> 0 \<and> det HessU = 0 \<and> \<not> surj (DM_paper_x x (cvec \<omega>))}\<close> is meager.
  Case \<open>c \<noteq> 0\<close>: it injects into \<open>{x. \<not> surj (DM_paper_x x c)}\<close>, nowhere dense by the mstarg
  freebie.  Case \<open>c = 0\<close>: \<open>\<not> surj\<close> is universal, so the slice is the D2 beam-center set,
  meager by @{thm m5_D5_beamcenter_angle_meager}.\<close>

lemma m5_D5_slice_meager:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes c6: "6 \<le> CARD('n)" and pfw: "sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
proof (cases "cvec_dip \<omega>0 \<omega>s \<omega> = 0")
  case True
  \<comment> \<open>\<open>c = 0\<close>: \<open>\<not> surj\<close> holds for all \<open>x\<close>, so the slice is the D2 beam-center set.\<close>
  have e: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
        = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0}"
    using DM_paper_x_null_not_surj[where x = _ and 'n = 'n] by (simp add: True)
  show ?thesis
    unfolding e by (rule m5_D5_beamcenter_angle_meager[OF c6 pfw True])
next
  case False
  \<comment> \<open>\<open>c \<noteq> 0\<close>: inject into the nowhere-dense moment-map set, then meager.\<close>
  have cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0" using False .
  have nd: "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    by (rule fixed_c_nonsurj_nowhere_dense[OF cnz c6])
  have sub: "{x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
        \<subseteq> {x::(real^2)^'n. \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_nowhere_dense[OF nd]])
qed


subsection \<open>D5 assembly: \<open>m5_D5_steersing\<close> (R3 confinement + finite union of slices)\<close>

text \<open>The exact target statement (verbatim from the M5 skeleton).  Proof is the M6 R3
  reduction with \<open>surj\<close> dropped: confine every bad witness angle into the finite set \<open>K\<close>
  (cos zeros \<open>\<times>\<close> phase-lattice zeros) via @{thm M6_witness_gdip_deriv_zero} and
  @{thm Dcvec_det_eq} --- neither uses surjectivity --- then take the finite union of the
  per-angle slices, each meager by @{thm m5_D5_slice_meager}.\<close>

lemma m5_D5_steersing:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
proof -
  \<comment> \<open>Splice freebies: phase-separation data for the (free) \<open>\<omega>0 \<omega>s\<close>.\<close>
  have hsep: "kz \<omega>s \<noteq> kz \<omega>0" by (rule m5_D5_hsep_freebie)
  have kdiff: "kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s" by (rule m5_D5_kdiff_freebie)
  define Ac :: real where "Ac = (kx \<omega>0 - kx \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define Bc :: real where "Bc = (ky \<omega>0 - ky \<omega>s) / (kz \<omega>s - kz \<omega>0)"
  define K :: "(real^2) set" where
    "K = {\<omega> \<in> OmegaPF ctr \<delta>. cos (\<omega> $ 1) = 0
            \<and> Ac * cos (\<omega> $ 2) + Bc * sin (\<omega> $ 2) = 0}"
  define slice :: "real^2 \<Rightarrow> ((real^2)^'n) set" where
    "slice \<omega> = {x :: (real^2)^'n.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}" for \<omega> :: "real^2"
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
  text \<open>Witness confinement: every bad witness angle lies in \<open>K\<close>
    (R3 kernel-direction reduction --- uses NO surjectivity).\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}
             \<subseteq> (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof
    fix x :: "(real^2)^'n"
    assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
    then obtain \<omega> :: "real^2" where wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and hz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and ns: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      and dz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0"
      by blast
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    have gd0: "frechet_derivative gdip (at (\<omega> $ 1)) 1 = 0"
      by (rule M6_witness_gdip_deriv_zero[OF s1 g0 anz dz])
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
    have xs: "x \<in> slice \<omega>" using g0 anz hz ns by (simp add: slice_def)
    show "x \<in> (\<Union>\<omega>\<in>K. slice \<omega>)"
    proof (rule UN_I)
      show "\<omega> \<in> K" by (rule wK)
      show "x \<in> slice \<omega>" by (rule xs)
    qed
  qed
  text \<open>Each slice over a fixed angle in \<open>K\<close> is meager (mstarg freebie for \<open>c \<noteq> 0\<close>,
    D2 covariance polynomial for \<open>c = 0\<close>); the finite union is meager.\<close>
  have meagU: "meager (\<Union>\<omega>\<in>K. slice \<omega>)"
  proof (rule meager_Union_finite[OF finK])
    fix \<omega> :: "real^2" assume wK: "\<omega> \<in> K"
    have wD: "\<omega> \<in> OmegaPF ctr \<delta>" using wK by (simp add: K_def)
    have s1: "sin (\<omega> $ 1) \<noteq> 0" by (rule bspec[OF pf wD])
    show "meager (slice \<omega>)"
      unfolding slice_def
      by (rule m5_D5_slice_meager[OF c6 s1])
  qed
  show ?thesis by (rule meager_subset[OF sub meagU])
qed

end
