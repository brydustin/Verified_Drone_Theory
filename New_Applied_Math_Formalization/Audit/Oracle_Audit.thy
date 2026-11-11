theory Oracle_Audit
  imports "Applied_Math_Final.Nonemptiness_Final"
begin

text \<open>The session fails if the final theorem, or any theorem on the way to it, depends on an oracle.  Only
  meaningful because every session below it is built with \<open>quick_and_dirty = false\<close>.\<close>

ML \<open>
  fun audit name thms =
    (case Thm_Deps.all_oracles thms of
      [] => ()
    | os => error ("Oracles in " ^ name ^ ": " ^ commas (map (fn ((n, _), _) => n) os)));
  val _ = audit "F0_dip_nonempty_final" [@{thm F0_dip_nonempty_final}];
  val _ = audit "F0_dip_nonempty_final_explicit" [@{thm F0_dip_nonempty_final_explicit}];
  val _ = audit "regular_feasible_configuration_exists" [@{thm regular_feasible_configuration_exists}];
  val _ = audit "F0_dip_nonempty_example" [@{thm F0_dip_nonempty_example}];
  val _ = audit "negligible_of_countable_line_slices" [@{thm negligible_of_countable_line_slices}];
  val _ = audit "negligible_res_f_zeros" [@{thm negligible_res_f_zeros}];
  val _ = audit "residual_point_equations" @{thms residual_point_equations};
  val _ = audit "BadXGW_point_equations" @{thms BadXGW_point_equations};
  val _ = audit "design_radial_equation" [@{thm design_radial_equation}];
  val _ = audit "design_radial_degenerate" [@{thm design_radial_degenerate}];
  val _ = audit "design_perp_equation" [@{thm design_perp_equation}];
  val _ = audit "chart_image_cover" [@{thm chart_image_cover}];
  val _ = audit "nonaligned_point_in_chart_image" [@{thm nonaligned_point_in_chart_image}];
  val _ = audit "nonaligned_residual_cover" [@{thm nonaligned_residual_cover}];
  val _ = audit "aligned_bad_closed_cover" [@{thm aligned_bad_closed_cover}];
  val _ = audit "BadXGW_design_cover" [@{thm BadXGW_design_cover}];
  val _ = audit "residual_meager_design" [@{thm residual_meager_design}];
\<close>

end
