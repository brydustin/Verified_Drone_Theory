theory Scratch_m5_skeleton
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>\<^bold>\<open>(M5) Rank-deficient stratum --- D1--D5 skeleton.\<close>

  This file restates \<open>meager_rank_deficient_stratum\<close> (the lone live \<open>sorry\<close> on the
  flagship path) as an \<^emph>\<open>assembly\<close> over an exhaustive cover of its bad set \<open>?def\<close>
  (= the \<open>?def\<close> stratum of \<open>Phi_bad_meager_dip\<close> in Robust3).  The witness angle \<open>\<omega>\<close> of every
  \<open>?def\<close> point falls into exactly one case:

  \<^item> \<open>det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0\<close>                       \<rightarrow> \<^bold>\<open>D5\<close> (steering det\<open>=0\<close> corner)
  \<^item> \<open>det \<noteq> 0 \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close>                          \<rightarrow> \<^bold>\<open>D2\<close> (beam-center \<open>c=0\<close>)
  \<^item> \<open>det \<noteq> 0 \<and> cvec \<noteq> 0 \<and> x-partial of \<nabla>U regular\<close>          \<rightarrow> \<^bold>\<open>D1\<close> (joint-regular; = M5a)
  \<^item> \<open>det \<noteq> 0 \<and> cvec \<noteq> 0 \<and> \<not> regular\<close>                        \<rightarrow> \<^bold>\<open>D34\<close> (residual = D3 collinear \<union> D4 Branch-P)

  The cover is exhaustive by excluded middle (det\<open>=0\<close>?, cvec\<open>=0\<close>?, regular?), so the
  assembly closes regardless of the (hard) internal structure of each piece, which is
  isolated into the four sub-lemmas.

  \<^bold>\<open>Status:\<close> D1 is PROVEN here (it is a subset of the heap's @{thm meager_grad_x_regular_part},
  M5a, since restricting \<open>\<omega>\<close> to \<open>OmegaPF\<close> and adding conjuncts only shrinks the set).
  D2, D5, D34 are \<open>sorry\<close> stubs for the parallel prover wave.  Diary design: D2 = countable
  beam-center angles + det-Hessian covariance-polynomial slices; D5 = M6 machinery (R3 kernel
  reduction sans \<open>surj\<close>) at the finite witness-angle set; D34 splits internally into D3
  (phase-collinear, excess engine + \<open>\<int>\<^sup>3\<close> lattice) and D4 (Branch-P, rank-drop dichotomy).\<close>


subsection \<open>D1 --- joint-regular part (PROVEN from M5a in the heap)\<close>

text \<open>The slice where the \<open>x\<close>-partial of \<open>\<nabla>\<^sub>\<Omega>U\<close> is surjective.  This is a subset of the
  already-proven @{thm meager_grad_x_regular_part} (which quantifies \<open>\<omega>\<close> over all of \<open>real^2\<close>
  and omits the \<open>A \<noteq> 0\<close> / \<open>\<not> surj\<close> / det / cvec conjuncts), so it is meager by monotonicity.\<close>

lemma m5_D1_regular:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
proof -
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}
        \<subseteq> {x \<in> V. \<exists>\<omega> :: real^2. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
            \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
            \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
    by blast
  show ?thesis
    by (rule meager_subset[OF sub meager_grad_x_regular_part[OF openV Vne]])
qed


subsection \<open>D2 --- beam-center angles \<open>cvec_dip \<omega>0 \<omega>s \<omega> = 0\<close> (STUB)\<close>

text \<open>The countable set of beam-center angles where the steering vector vanishes
  identically.  Three of M5's four conjuncts hold \<open>x\<close>-universally there; meagerness comes
  from the nontrivial det-Hessian covariance polynomial
  (\<open>gdip''(\<pi>/2) = (16 - 4\<pi>\<^sup>2)/8 \<noteq> 0\<close>).  Design piece D2.\<close>

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
  sorry


subsection \<open>D5 --- steering-singular corner \<open>det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0\<close> (STUB)\<close>

text \<open>The \<open>(\<not> surj, det Dcvec = 0)\<close> corner.  M6's R3 kernel-direction reduction needs NO
  \<open>surj\<close> hypothesis, so it collapses witnesses to the same finite angle set as M6; R5-variant
  slices (\<open>c \<noteq> 0\<close>) and D2-polynomial slices (\<open>c = 0\<close>) finish.  Design piece D5 (reuses the
  proven M6 machinery in the heap).\<close>

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
  sorry


subsection \<open>D34 --- residual: D3 (phase-collinear) \<union> D4 (Branch-P) (STUB)\<close>

text \<open>The non-beam-center, det-nonsingular, \<^emph>\<open>non-regular\<close> residual.  Internally split per the
  diary into D3 (phase-collinear branch: 3-equation/2-parameter excess engine -> \<open>(2N-1)\<close>-dim
  IFT graphs with negligible \<open>x\<close>-projections + \<open>\<int>\<^sup>3\<close> lattice union, no Sard) and D4 (Branch-P
  residual: \<open>\<gamma> \<parallel> c\<close> rank-drop dichotomy + excess engine).  Kept as one statement here because
  the D3/D4 separating predicate is a proof-internal design choice, not a statement-level one.\<close>

lemma m5_D34_residual:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  sorry


subsection \<open>Assembly: \<open>meager_rank_deficient_stratum\<close> (M5) from D1, D2, D5, D34\<close>

lemma meager_rank_deficient_stratum:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
proof -
  let ?D1 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  let ?D2 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> = 0}"
  let ?D5 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) = 0}"
  let ?D34 = "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>.
            gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
          \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
          \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
          \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
          \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0
          \<and> cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0
          \<and> \<not> (\<exists>Dx. ((\<lambda>y. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative Dx) (at x) \<and> surj Dx)}"
  have meag: "meager (?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34)"
    by (intro meager_Un
          m5_D1_regular[OF openV Vne]
          m5_D2_beamcenter[OF openV Vne c6 d0 pf]
          m5_D5_steersing[OF openV Vne c6 d0 pf]
          m5_D34_residual[OF openV Vne c6 d0 pf])
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}
             \<subseteq> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34"
  proof (rule subsetI)
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
    then obtain \<omega> where xV: "x \<in> V" and wD: "\<omega> \<in> OmegaPF ctr \<delta>"
      and g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      and h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
      and a0: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0"
      and ns: "\<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))"
      by blast
    show "x \<in> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34"
      using xV wD g0 h0 a0 ns by blast
  qed
  show ?thesis by (rule meager_subset[OF sub meag])
qed

end
