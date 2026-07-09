theory D34_H0res_Branch
  imports D34_Analytic_Bridge
begin

section \<open>app:H0res: the B1=B2=B3=0 branch, connected to the D34 configuration type\<close>

text \<open>IMPORTANT PRIOR-WORK NOTE (found during investigation, before writing anything
  here): the elementary trig fact this branch needs
  (\<open>\<beta>(t):=cos t - t sin t\<close>, \<open>\<beta>(t)=0 \<Longrightarrow> \<beta>'(t)\<noteq>0\<close>) is ALREADY fully proven,
  with zero \<open>proof hole\<close>, in \<open>Appendix/Nonemptiness_Regnonzero_Appendix.thy\<close>
  (\<open>lem_h0res_Bcuts\<close>), together with the residue rank-2 argument
  (\<open>lem_h0res_a1a2\<close>) and generic nowhere-dense wrappers
  (\<open>prop_h0res_Bbranch\<close>, \<open>prop_h0res_Sbranch\<close>, \<open>prop_h0res_twocos\<close>,
  \<open>lem_h0res_residue_exc\<close>, \<open>lem_h0res_baseSK\<close>, \<open>prop_h0res_meager\<close>).  HOWEVER:
  \<^enum> that file (and \<open>Nonemptiness_Capstone.thy\<close>, which imports it) is NOT imported
    by \<open>Appendix/Robust3/Nonemptiness_Robust3.thy\<close> --- i.e. it is disconnected from
    the actual causal chain to \<open>F0_dip_nonempty\<close>, the same situation as the
    earlier \<open>m5_D34_subset_mstarg_residual\<close> enlargement;
  \<^enum> its H0res lemmas are GENERIC wrappers over an abstract \<open>cert :: 'w \<Rightarrow> real\<close>
    function --- they are true but not yet connected to any concrete D34 object
    (no \<open>B_j\<close> defined in terms of \<open>cvec_dip\<close>/the triple type anywhere);
  \<^enum> more importantly, \<open>prop_h0res_meager\<close> TAKES \<open>meager (Bbranch \<inter> Vset)\<close> etc.
    as HYPOTHESES rather than deriving them from the nowhere-dense facts --- the
    file's own "Correction" comment (search \<open>analytic_cut_nowhere_dense\<close>) flags
    that a single codim-1 cut being nowhere-dense in \<open>W\<close> does NOT by itself give
    meager PROJECTION to \<open>V\<close> (needs an actual codim-\<ge>3 dimension drop); that
    bridging step is not completed anywhere in the file for this branch.
  So: reusable elementary facts exist, but "app:H0res is done" would be
  significantly overclaiming the current state.  This file connects the
  ELEMENTARY transversality fact (re-derived fresh here, not by cross-session
  import, to avoid coupling to a theory outside this project's live chain) to
  the ACTUAL D34 configuration type, landing a genuinely new, connected result:
  the u-slot derivative of the D34-specific \<open>B_dip j\<close> is nonzero whenever
  \<open>B_dip j = 0\<close>.  The codim-3-implies-meager-projection step remains open (see
  the closing remark).\<close>

subsection \<open>The elementary trig fact (re-derived; matches Regnonzero\_Appendix's
  lem\_h0res\_Bcuts exactly, kept independent of that theory's session)\<close>

definition beta_h0 :: "real \<Rightarrow> real" where
  "beta_h0 t = cos t - t * sin t"

theorem beta_h0_deriv_nonzero_at_zero:
  fixes t :: real
  assumes b: "beta_h0 t = 0"
  shows "-(2 * sin t + t * cos t) \<noteq> 0"
proof
  assume "-(2 * sin t + t * cos t) = 0"
  hence d: "2 * sin t + t * cos t = 0" by simp
  from b have c: "cos t = t * sin t" unfolding beta_h0_def by simp
  have "sin t * (2 + t\<^sup>2) = 2 * sin t + t * cos t"
    by (simp add: c algebra_simps power2_eq_square)
  also have "\<dots> = 0" using d by simp
  finally have prod0: "sin t * (2 + t\<^sup>2) = 0" .
  have pos: "2 + t\<^sup>2 > 0" using zero_le_power2[of t] by linarith
  with prod0 have s0: "sin t = 0" by simp
  hence c0: "cos t = 0" using c by simp
  with s0 sin_cos_squared_add[of t] show False by simp
qed

theorem has_derivative_beta_h0: "(beta_h0 has_derivative (\<lambda>h. -(2 * sin t + t * cos t) * h)) (at t)"
  unfolding beta_h0_def
  by (auto intro!: derivative_eq_intros ext) (simp add: algebra_simps fun_eq_iff)

subsection \<open>ucoord: the c-projected parallel coordinate of a single element\<close>

text \<open>Kept as a local, self-contained definition (rather than importing
  \<open>D34_UPhi_Branch.thy\<close>, an actively-developed sibling file) to avoid coupling
  this branch's build to concurrent work; matches Codex's \<open>ucoord\<close> convention in
  \<open>D34_UPhi_Branch.thy\<close> exactly (\<open>ucoord c p = (c \<bullet> p) / norm c\<close>).\<close>

definition ucoord_h0 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "ucoord_h0 c p = (c \<bullet> p) / norm c"

theorem has_derivative_ucoord_h0_x:
  fixes j :: "'n::finite" and c :: "real^2" and x :: "(real^2)^'n"
  shows "((\<lambda>y. ucoord_h0 c (vec_nth y j)) has_derivative (\<lambda>h. ucoord_h0 c (vec_nth h j))) (at x)"
proof -
  have lin: "linear (\<lambda>y. ucoord_h0 c (vec_nth y j))"
    unfolding ucoord_h0_def linear_iff
    by (simp add: inner_add_right algebra_simps add_divide_distrib)
  show ?thesis
    by (rule linear_imp_has_derivative[OF lin])
qed

theorem ucoord_h0_slot_self:
  fixes c :: "real^2"
  assumes cnz: "c \<noteq> 0"
  shows "ucoord_h0 c c = norm c"
  unfolding ucoord_h0_def
  by (simp add: dot_square_norm power2_eq_square cnz)

theorem ucoord_h0_uslot_deriv:
  fixes j :: "'n::finite" and c :: "real^2" and x :: "(real^2)^'n"
  assumes cnz: "c \<noteq> 0"
  shows "frechet_derivative (\<lambda>y. ucoord_h0 c (vec_nth y j)) (at x) (slot j c) = norm c"
proof -
  have hd: "((\<lambda>y. ucoord_h0 c (vec_nth y j)) has_derivative (\<lambda>h. ucoord_h0 c (vec_nth h j))) (at x)"
    by (rule has_derivative_ucoord_h0_x)
  have val: "frechet_derivative (\<lambda>y. ucoord_h0 c (vec_nth y j)) (at x) (slot j c)
           = ucoord_h0 c (vec_nth (slot j c) j)"
    by (rule fun_cong[OF frechet_derivative_at[OF hd, symmetric]])
  show ?thesis
    unfolding val slot_nth by (simp add: ucoord_h0_slot_self[OF cnz])
qed

subsection \<open>B\_dip: the D34-connected version of the paper's B\_j, and its u-slot transversality\<close>

definition B_dip :: "'n::finite \<Rightarrow> (real^2)^'n \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "B_dip j x \<omega> \<omega>0 \<omega>s
     = beta_h0 (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))"

theorem has_derivative_B_dip_x:
  fixes j :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  shows "((\<lambda>y. B_dip j y \<omega> \<omega>0 \<omega>s) has_derivative
      (\<lambda>h. -(2 * sin (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))
              + (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))
                * cos (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j)))
           * (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth h j)))) (at x)"
proof -
  have inner: "((\<lambda>y. norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth y j)) has_derivative
       (\<lambda>h. norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth h j))) (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const has_derivative_ucoord_h0_x]])
       (simp add: fun_eq_iff algebra_simps)
  have outer: "(beta_h0 has_derivative
       (\<lambda>h. -(2 * sin (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))
              + (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))
                * cos (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))) * h))
       (at (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j)))"
    by (rule has_derivative_beta_h0)
  show ?thesis
    unfolding B_dip_def
    by (rule has_derivative_compose[OF inner outer])
qed

theorem B_dip_uslot_transversal:
  fixes j :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes cnz: "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
    and bz: "B_dip j x \<omega> \<omega>0 \<omega>s = 0"
  shows "frechet_derivative (\<lambda>y. B_dip j y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
proof -
  have val: "frechet_derivative (\<lambda>y. B_dip j y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>))
      = -(2 * sin (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))
          + (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))
            * cos (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j)))
        * (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)) j))"
    by (rule fun_cong[OF frechet_derivative_at[OF has_derivative_B_dip_x, symmetric]])
  have selfval: "ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)) j) = norm (cvec_dip \<omega>0 \<omega>s \<omega>)"
    unfolding slot_nth by (simp add: ucoord_h0_slot_self[OF cnz])
  have bz': "beta_h0 (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j)) = 0"
    using bz unfolding B_dip_def .
  have nz: "-(2 * sin (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))
             + (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))
               * cos (norm (cvec_dip \<omega>0 \<omega>s \<omega>) * ucoord_h0 (cvec_dip \<omega>0 \<omega>s \<omega>) (vec_nth x j))) \<noteq> 0"
    by (rule beta_h0_deriv_nonzero_at_zero[OF bz'])
  show ?thesis
    unfolding val selfval
    using nz cnz by simp
qed

text \<open>REMAINING for this branch (not attempted here, genuinely separate work): lifting
  \<open>B_dip_uslot_transversal\<close> (transversality of ONE cut, for ONE triple element \<open>j\<close>) to
  the full \<open>prop:h0res-Bbranch\<close> conclusion (codimension \<ge>3 from THREE independent
  cuts \<open>j=1,2,3\<close>, hence MEAGER PROJECTION to the configuration space \<open>V\<close> --- this
  needs a genuine \<open>proj_lowdim_meager\<close>-style rank/dimension argument using the has_derivative
  machinery for all three \<open>u_1,u_2,u_3\<close> slots jointly, analogous in spirit to the
  \<open>det3\<close>/\<open>Jac3\<close> block-triangular arguments built for the H11/H22/H12=0 branches
  elsewhere in this bridge, but for a THREE-FOLD (not 3x3-single-point) codimension
  count).  Not attempted in this pass.\<close>

end
