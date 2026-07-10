theory D3_Chart_Wiring
  imports "Applied_Math_Appendix_Frontier.Nonemptiness_Robust4"
          "Applied_Math_D34_Analytic.D34_Geodesic_Branch"
begin

section \<open>Wiring the geodesic-branch rank criteria toward \<open>d3_detHess_arc_chart_core_all\<close>\<close>

text \<open>\<^bold>\<open>Architecture.\<close>  This theory is the FIRST theory that sees both heaps: the
  Robust4 frontier (which defines the honest boundary predicate
  \<open>d3_detHess_arc_chart_core_all\<close> consumed by \<open>F0_dip_nonempty\<close>) and the geodesic
  branch (which provides the rank-3 criteria \<open>Jac3_22\<close> / \<open>Jac3\<close> / \<open>Jac3_H0cub\<close> with
  generic satisfaction and concrete witnesses).  Its job is the glue:

  \<^enum> FIBRE FACTS: on the \<open>D3BadXG_H0core\<close> fibre the first two rank-criterion rows
    vanish (\<open>Phi_par = 0\<close>, \<open>gradU\<^sub>2 = 0\<close>);
  \<^enum> the BRANCH TRICHOTOMY: \<open>det HessU = 0\<close> splits into \<open>H\<^sub>2\<^sub>2 \<noteq> 0\<close> (Jac3_22 branch),
    \<open>H\<^sub>2\<^sub>2 = 0 \<and> H\<^sub>1\<^sub>1 \<noteq> 0\<close> (Jac3 branch), or --- by symmetry of the Hessian ---
    \<open>HessU = 0\<close> entirely (the Tier 6 cubic branch);
  \<^enum> the remaining engine gap, stated precisely at the end.\<close>

subsection \<open>Fibre facts\<close>

lemma H0core_fibre_Phi_par_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite"
  assumes gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "Phi_par x \<omega> \<omega>0 \<omega>s = 0"
  by (rule Phi_par_zero_of_gradU_zero[OF gz])

lemma H0core_fibre_gradU2_zero:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite"
  assumes gz: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
  shows "vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2 = 0"
  unfolding gz by simp

subsection \<open>The branch trichotomy for \<open>det HessU = 0\<close>\<close>

lemma detHess_zero_cases:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite"
  assumes dz: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
  shows "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2 \<noteq> 0
       \<or> (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2 = 0
          \<and> HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1 \<noteq> 0)
       \<or> HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
proof (cases "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2 = 0")
  case False
  thus ?thesis by blast
next
  case H22: True
  show ?thesis
  proof (cases "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1 = 0")
    case False
    with H22 show ?thesis by blast
  next
    case H11: True
    \<comment> \<open>diagonal zero + det zero + symmetry \<Longrightarrow> the whole Hessian vanishes\<close>
    have det2: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>)
        = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 1
            * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 2
        - HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
            * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
      by (simp add: det_2)
    have sym: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
        = HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 2 $ 1"
      by (rule HessU_dip_symmetric)
    have H12: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2 = 0"
    proof -
      have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2
          * HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ 1 $ 2 = 0"
        using dz det2 H11 H22 sym by simp
      thus ?thesis by simp
    qed
    have Hz: "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
    proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
      fix k :: 2
      show "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k = (0::real^2^2) $ k"
      proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
        fix l :: 2
        have "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l = 0"
          using exhaust_2[of k] exhaust_2[of l] H11 H22 H12 sym H12[unfolded sym]
          by (metis (full_types))
        thus "HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> $ k $ l = (0::real^2^2) $ k $ l"
          by (simp add: zero_index)
      qed
    qed
    thus ?thesis by blast
  qed
qed

text \<open>\<^bold>\<open>The remaining engine gap, stated precisely.\<close>  For each fibre point the
  trichotomy selects a rank-3 criterion whose side conditions hold generically
  (\<open>Jac3_H12rad_nonzero_in_open_robust4_witness\<close> /
  \<open>Jac3_H0cub_nonzero_in_open_robust4_witness\<close> at the design point).  What converts
  "the fibre is locally inside a level set of a \<open>C\<^sup>1\<close> triple with rank-3 x-derivative"
  into the \<open>charts/Crit/D\<close> data of \<open>d3_detHess_arc_chart_core\<close> is a
  level-set-to-rank-deficient-closed-cover engine: locally parametrize the codim-3
  level set, compose with inclusion to get self-maps of configuration space with
  rank \<open>\<le> 2N - 3\<close> derivatives, and exhaust by closed pieces.  That engine is the
  next tier; this theory pins its interface.\<close>

end
