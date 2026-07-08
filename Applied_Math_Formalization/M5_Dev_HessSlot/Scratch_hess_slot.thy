theory Scratch_hess_slot
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-08).  The perp-slot x-derivatives of the three Hessian
  blocks --- verified here and spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>:
  \<^item> glue \<open>Mcfun_eq_M1/M2_moment\<close>, \<open>M2cfun_eq_M11/M12/M12'/M22_moment\<close>;
  \<^item> uniform derivative entries \<open>dMcfun_x\<close> / \<open>dM2cfun_x\<close> with their
    \<open>has_derivative_Afun/Mcfun/M2cfun_x\<close> laws (at fixed c, in x) and perp-slot
    collapses \<open>dMcfun_x_perp\<close> / \<open>dM2cfun_x_perp\<close>;
  \<^item> the three block x-derivatives \<open>has_derivative_Uc_x\<close> (pattern value V=|A|^2),
    \<open>has_derivative_gradUc_comp_x\<close> (c-gradient components), \<open>has_derivative_Hcmat_entry_x\<close>
    (Hcmat entries), each with its perp-slot value:
      Uc_perp_slot_deriv       : partial_{slot m v} V = 0
      gradUc_comp_perp_slot_deriv : = 2 v_i Im(cnj A phi_m)
      Hcmat_entry_perp_slot_deriv : = 2[v_l Re(cnj phi_m M_k) + v_k Re(cnj M_l phi_m)
                                        - (v_k x_l + x_k v_l) Re(cnj A phi_m)]
  These are the gauge/frame-free generators of the paper's d_vj H12/H22 formulas
  (prop:vpair11 / prop:vblock).  Checks below guard the interface.\<close>

thm Mcfun_eq_M1_moment M2cfun_eq_M12_moment
thm has_derivative_Afun_x has_derivative_Mcfun_x has_derivative_M2cfun_x
thm dMcfun_x_perp dM2cfun_x_perp
thm has_derivative_Uc_x has_derivative_gradUc_comp_x has_derivative_Hcmat_entry_x
thm Uc_perp_slot_deriv gradUc_comp_perp_slot_deriv Hcmat_entry_perp_slot_deriv

end
