theory Scratch_D3Generic
  imports "Applied_Math_M5_D3Assembly.Scratch_D3Assembly"
begin

section \<open>Making the Xi witness a genericity theorem\<close>

text \<open>
  @{thm Xi_nonzero_witness_exists} supplies the nontriviality input for the
  real-analytic zero-set theorem, but until this leaf it had no downstream
  consumer.  The first bridge is to prove that, at frozen steering data and
  frozen arc velocity, \<open>x \<mapsto> Xi x omega0 omegas omega w\<close> is real
  analytic on configuration space.
\<close>

lemma real_analytic_on_HessU_dip_entry_fixed_angle:
  fixes k l :: 2
  shows "real_analytic_on
      (\<lambda>x::(real^2)^'n::finite.
        vec_nth (vec_nth
          (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) k) l)
      UNIV"
proof -
  have con: "real_analytic_on (\<lambda>_::(real^2)^'n. \<omega>) UNIV"
    by (rule real_analytic_on_const[OF open_UNIV])
  have "real_analytic_on
      (\<lambda>x::(real^2)^'n.
        vec_nth (vec_nth
          (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x
            ((\<lambda>_::(real^2)^'n. \<omega>) x)) k) l)
      UNIV"
    by (rule real_analytic_on_HessU_entry_chart[OF open_UNIV con])
  then show ?thesis
    by simp
qed

theorem real_analytic_on_Xi_config:
  "real_analytic_on
      (\<lambda>x::(real^2)^'n::finite. Xi x \<omega>0 \<omega>s \<omega> w)
      UNIV"
proof -
  have row: "real_analytic_on
      (\<lambda>x::(real^2)^'n.
        vec_nth
          (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v w) i)
      UNIV" for i
  proof -
    have eq: "(\<lambda>x::(real^2)^'n.
        vec_nth
          (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v w) i)
      = (\<lambda>x. \<Sum>j\<in>UNIV.
          vec_nth (vec_nth
            (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) i) j
          * vec_nth w j)"
      by (rule ext) (simp add: matrix_vector_mult_def)
    show ?thesis
      unfolding eq
      by (intro real_analytic_on_sum[OF open_UNIV finite]
            real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
            real_analytic_on_HessU_dip_entry_fixed_angle)
  qed
  have Term: "real_analytic_on
      (\<lambda>x::(real^2)^'n.
        vec_nth
          (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v w) i
        * vec_nth (e_par \<omega>0 \<omega>s \<omega>) i)
      UNIV" for i
    by (simp add: real_analytic_on_const real_analytic_on_mult row)
    
  then show ?thesis
    unfolding Xi_def inner_vec_def
    by (subst real_analytic_on_sum, auto)
qed

text \<open>
  Consequently the exceptional configurations on which the frozen arc
  velocity lies in the Hessian kernel form a nowhere-dense analytic zero
  set.  This is the first theorem that actually consumes
  @{thm Xi_nonzero_witness_exists}.
\<close>

theorem Xi_zeros_nowhere_dense:
  fixes \<omega>0 \<omega>s \<omega> w :: "real^2"
  assumes card2: "2 \<le> CARD('n)"
    and detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and e1nz: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0"
    and gnz: "gain_dip \<omega> \<noteq> 0"
    and w1nz: "vec_nth w 1 \<noteq> 0"
  shows "interior
      (closure {x::(real^2)^'n. Xi x \<omega>0 \<omega>s \<omega> w = 0}) = {}"
proof -
  obtain x :: "(real^2)^'n"
    where "Xi x \<omega>0 \<omega>s \<omega> w \<noteq> 0"
    using Xi_nonzero_witness_exists[OF card2 detnz cnz e1nz gnz w1nz]
    by blast
  then have ex: "\<exists>x\<in>(UNIV::((real^2)^'n) set).
      Xi x \<omega>0 \<omega>s \<omega> w \<noteq> 0"
    by blast
  have "interior
      (closure {x\<in>(UNIV::((real^2)^'n) set).
        Xi x \<omega>0 \<omega>s \<omega> w = 0}) = {}"
    by (rule real_analytic_nowhere_dense_zeros
          [OF real_analytic_on_Xi_config connected_UNIV ex])
  then show ?thesis
    by simp
qed

end
