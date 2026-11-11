section \<open>The dipole gain is real-analytic\<close>

theory Dipole_Gain_Analytic
  imports
    Dipole_Pattern
    "HOL-Complex_Analysis.Complex_Analytic"
begin

text \<open>The gain @{const gdip} is the restriction to the real line of an entire function.  Hence it
  is real-analytic, and in particular \<open>C\<^sup>\<infinity>\<close>, on the whole line, the poles included.\<close>

definition csinc :: "complex \<Rightarrow> complex" where
  "csinc z = (if z = 0 then 1 else sin z / z)"

lemma csinc_holomorphic: "csinc holomorphic_on UNIV"
proof (rule no_isolated_singularity'[where K = "{0}"])
  show "csinc holomorphic_on UNIV - {0}"
  proof (rule holomorphic_transform)
    show "(\<lambda>z. sin z / z) holomorphic_on UNIV - {0}"
      by (intro holomorphic_intros) auto
    show "sin z / z = csinc z" if "z \<in> UNIV - {0}" for z
      using that by (simp add: csinc_def)
  qed
  show "open (UNIV :: complex set)"
    by simp
  show "finite {0::complex}"
    by simp
  show "(csinc \<longlongrightarrow> csinc z) (at z within UNIV)" if "z \<in> {0}" for z
  proof -
    have z: "z = 0"
      using that by simp
    have "((\<lambda>h. (sin (0 + h) - sin 0) / h) \<longlongrightarrow> cos (0::complex)) (at 0)"
      using DERIV_sin[of "0::complex"] unfolding DERIV_def .
    then have "((\<lambda>h::complex. sin h / h) \<longlongrightarrow> 1) (at 0)"
      by simp
    moreover have "eventually (\<lambda>h. sin h / h = csinc h) (at 0)"
      by (simp add: eventually_at_filter csinc_def)
    ultimately have "(csinc \<longlongrightarrow> 1) (at 0)"
      by (rule Lim_transform_eventually)
    then show ?thesis
      by (simp add: z csinc_def)
  qed
qed

lemma csinc_of_real: "csinc (complex_of_real t) = complex_of_real (gsinc t)"
  by (simp add: csinc_def gsinc_def sin_of_real)

text \<open>The entire function that restricts to @{const gdip}.\<close>

definition gdip_ext :: "complex \<Rightarrow> complex" where
  "gdip_ext z = of_real (pi^2/4)
      * (csinc (of_real (pi/2) * (1 - cos z)) * csinc (of_real (pi/2) * (1 + cos z)))"

lemma gdip_ext_holomorphic: "gdip_ext holomorphic_on UNIV"
proof -
  have m: "(\<lambda>z. of_real (pi/2) * (1 - cos z)) holomorphic_on UNIV"
    by (intro holomorphic_intros)
  have p: "(\<lambda>z. of_real (pi/2) * (1 + cos z)) holomorphic_on UNIV"
    by (intro holomorphic_intros)
  have a: "(csinc o (\<lambda>z. of_real (pi/2) * (1 - cos z))) holomorphic_on UNIV"
    by (rule holomorphic_on_compose_gen[OF m csinc_holomorphic]) simp
  have b: "(csinc o (\<lambda>z. of_real (pi/2) * (1 + cos z))) holomorphic_on UNIV"
    by (rule holomorphic_on_compose_gen[OF p csinc_holomorphic]) simp
  have "(\<lambda>z. of_real (pi^2/4)
          * ((csinc o (\<lambda>z. of_real (pi/2) * (1 - cos z))) z
             * (csinc o (\<lambda>z. of_real (pi/2) * (1 + cos z))) z)) holomorphic_on UNIV"
    by (rule holomorphic_on_mult[OF holomorphic_on_const holomorphic_on_mult[OF a b]])
  then show ?thesis
    unfolding gdip_ext_def[abs_def] o_def .
qed

lemma gdip_ext_of_real: "gdip_ext (complex_of_real x) = complex_of_real (gdip x)"
proof -
  have m: "of_real (pi/2) * (1 - cos (complex_of_real x)) = complex_of_real ((pi/2) * (1 - cos x))"
    by (simp add: cos_of_real)
  have p: "of_real (pi/2) * (1 + cos (complex_of_real x)) = complex_of_real ((pi/2) * (1 + cos x))"
    by (simp add: cos_of_real)
  show ?thesis
    unfolding gdip_ext_def gdip_def m p csinc_of_real by simp
qed

theorem gdip_real_analytic: "real_analytic_on gdip UNIV"
proof -
  have "real_analytic_at_1d gdip c" for c
  proof (rule holo_extension_imp_real_analytic_at_1d)
    show "has_holo_extension_at gdip c"
      unfolding has_holo_extension_at_def
    proof (intro exI[of _ "1::real"] exI[of _ gdip_ext] conjI allI impI)
      show "(0::real) < 1"
        by simp
      show "gdip_ext holomorphic_on ball (complex_of_real c) 1"
        by (rule holomorphic_on_subset[OF gdip_ext_holomorphic]) simp
      show "gdip_ext (complex_of_real x) = complex_of_real (gdip x)" for x
        by (rule gdip_ext_of_real)
    qed
  qed
  then show ?thesis
    by (simp add: real_analytic_on_1d_iff)
qed

corollary gdip_Cinfinity: "Cinfinity_on gdip UNIV"
  by (rule real_analytic_imp_Cinfinity[OF gdip_real_analytic])

text \<open>The same for the gain as a function of the angle.\<close>

theorem gain_dip_real_analytic: "real_analytic_on gain_dip UNIV"
proof -
  have proj: "real_analytic_on (\<lambda>\<omega>::real^2. \<omega> $ 1) UNIV"
    by (rule real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_vec_nth])
  have "real_analytic_on (\<lambda>\<omega>::real^2. gdip (\<omega> $ 1)) UNIV"
    by (rule real_analytic_on_compose[OF proj gdip_real_analytic]) simp
  then show ?thesis
    by (simp add: gain_dip_def[abs_def])
qed

corollary gain_dip_Cinfinity: "Cinfinity_on gain_dip UNIV"
  by (rule real_analytic_imp_Cinfinity[OF gain_dip_real_analytic])

end
