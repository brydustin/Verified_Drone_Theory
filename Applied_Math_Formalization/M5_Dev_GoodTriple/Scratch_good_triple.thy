theory Scratch_good_triple
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  Layer 4b step 2 --- the good-triple layer --- was
  drafted and verified here, then spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>:
  \<open>triple_good\<close> (+ \<open>_t_distinct\<close>, \<open>_distinct\<close>), \<open>edge_det2\<close> +
  \<open>common_perp_edge_det2\<close> (a common perpendicular to two edges in \<open>\<real>\<^sup>2\<close> kills their
  determinant), \<open>triples_transverse\<close> + \<open>two_triple_cover_pointwise\<close> (nine nonzero
  cross-edge determinants \<Longrightarrow> every \<open>c \<noteq> 0\<close> is good for one of the two triples ---
  the pointwise \<open>lem:twotriplecover\<close>), and \<open>triple_good_chart_persist\<close> (goodness at a
  chart basepoint survives on a shrunk ball).  GOTCHAS: in the merged heap, plain
  \<open>vec_eq_iff\<close> can resolve against JNF's \<open>Matrix.vec\<close> --- qualify as
  \<open>Finite_Cartesian_Product.vec_eq_iff\<close>; and \<open>open (A \<inter> V\<^sub>1 \<inter> V\<^sub>2)\<close> from pieces
  \<open>open (A \<inter> V\<^sub>i)\<close> needs the explicit re-association.  Checks below guard the interface.\<close>

thm triple_good_def triple_good_t_distinct triple_good_distinct
thm edge_det2_def common_perp_edge_det2
thm triples_transverse_def two_triple_cover_pointwise
thm triple_good_chart_persist

end
