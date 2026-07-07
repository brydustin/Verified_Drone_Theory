theory Scratch_cofactors
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  Layer 4b step 3 --- division closure + the Case-B
  cofactor primitives --- verified here and spliced verbatim into
  \<open>D34_Analytic_Bridge.thy\<close>:
  \<^enum> \<open>has_holo_extension_at_inverse\<close>, \<open>real_analytic_on_inverse_1d\<close> (on \<open>- {0}\<close>),
    \<open>real_analytic_on_inverse_comp\<close>, \<open>real_analytic_on_divide\<close> --- the missing
    division closure (needed for the branch gauge quantities, e.g.
    \<open>G\<^sub>2\<^sub>2 = H\<^sub>1\<^sub>1 - H\<^sub>1\<^sub>2\<^sup>2/H\<^sub>2\<^sub>2\<close>);
  \<^enum> \<open>det3\<close> + closure; \<open>tcoord c p = c \<bullet> p\<close> (\<open>= \<kappa> u_j\<close>) and
    \<open>wcoord c p = edge_det2 c p\<close> (\<open>= \<kappa> v_j\<close>) + closure;
  \<^enum> the three familiar cofactors \<open>cofK\<close>/\<open>cofL\<close>/\<open>cofM\<close> (tex 3650) in \<kappa>-SCALED
    polynomial-trigonometric form (\<open>cofK = \<kappa>\<^sup>2 K\<close>, \<open>cofL = \<kappa> L\<close>, \<open>cofM = \<kappa> M\<close> ---
    nonvanishing certificates transfer; exact \<kappa>-bookkeeping deferred to the
    \<open>prop:vblock\<close> derivation in step 4), with joint analyticity AND the
    chart-composed forms \<open>real_analytic_on_cof[KLM]_chart\<close> along a critical graph.
  NOTE: the paper's \<open>lem:block\<close>/\<open>lem:3x3\<close> (J5, rank-3 minor) are NOT in the heap
  and are NOT needed: they belong to \<open>prop:dimZ\<close>'s surjective piece, which the
  formalization already covers via the D1/mstarg route.
  Checks below guard the interface.\<close>

thm real_analytic_on_inverse_comp real_analytic_on_divide
thm det3_def real_analytic_on_det3
thm tcoord_def wcoord_def real_analytic_on_tcoord real_analytic_on_wcoord
thm cofK_def cofL_def cofM_def
thm real_analytic_on_cofK real_analytic_on_cofL real_analytic_on_cofM
thm real_analytic_on_cofK_chart real_analytic_on_cofL_chart real_analytic_on_cofM_chart

end
