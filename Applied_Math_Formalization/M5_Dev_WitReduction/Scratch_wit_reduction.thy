theory Scratch_wit_reduction
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-06).  The 4b close-out reduction --- verified here and
  spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>:
  \<^enum> \<open>triples_transverse_witness\<close>: an EXPLICIT transverse configuration
    ((0,0),(1,0),(0,1) / (0,0),(1,2),(3,1)) for any six distinct indices;
  \<^enum> \<open>edet\<close>/\<open>ttprod\<close> (the nine-factor transversality product --- index-based, a
    polynomial in \<open>x\<close> alone) + \<open>ttprod_nz_iff\<close> + \<open>real_analytic_on_ttprod\<close> +
    \<open>transverse_point_in_open\<close>: every nonempty open set of configurations contains
    a transverse point (workhorse on the product certificate; REPLACES the paper's
    globally perturbed two-triple neighbourhood \<open>V\<close> --- no perturbation lemma needed);
  \<^enum> \<^bold>\<open>dip_wit_reduction\<close>: the interface obligation \<open>wit\<close> of
    @{thm dip_critical_chart_nowhere_dense} follows from the SINGLE remaining
    hypothesis \<open>wit_core\<close> (a witness on any connected analytic critical chart with
    nonvanishing wavevector and a FIXED good triple) --- the exact statement the four
    Case-B branch corollaries prove.  4b is hereby reduced to \<open>wit_core\<close> alone.
  GOTCHAS: a ⋀-hypothesis quantifying sets over the theorem's index type must PIN
  the type (\<open>B'::((real^2)^'n) set\<close>) or its type variables float free; OF into the
  higher-order slots needs the explicit \<open>[of B' g i j k]\<close> instantiation first.
  Checks below guard the interface.\<close>

thm triples_transverse_witness
thm edet_def ttprod_def ttprod_nz_iff real_analytic_on_ttprod
thm transverse_point_in_open
thm dip_wit_reduction

end
