theory Oracle_Audit
  imports "Applied_Math_Main.Poles_And_Fixed_Margins" "Applied_Math_Pattern.Dipole_Gain_Analytic"
begin

text \<open>The session fails if one of the final theorems, or a theorem on the way to them, depends on an oracle.  Only
  meaningful because every session below it is built with \<open>quick_and_dirty = false\<close>.\<close>

ML \<open>
  fun audit name thms =
    (case Thm_Deps.all_oracles thms of
      [] => ()
    | os => error ("Oracles in " ^ name ^ ": " ^ commas (map (fn ((n, _), _) => n) os)));
  val _ = audit "degenerate_configurations_meager" [@{thm degenerate_configurations_meager}];
  val _ = audit "degenerate_configurations_nowhere_dense" @{thms degenerate_configurations_nowhere_dense};
  val _ = audit "nondegenerate_open_dense" @{thms nondegenerate_open_dense};
  val _ = audit "nondegenerate_dense_in_open" [@{thm nondegenerate_dense_in_open}];
  val _ = audit "nondegenerate_in_X0" [@{thm nondegenerate_in_X0}];
  val _ = audit "F0_dip_interior_nonempty" [@{thm F0_dip_interior_nonempty}];
  val _ = audit "F0_dip_nonempty_final" [@{thm F0_dip_nonempty_final}];
  val _ = audit "pole_degenerate" @{thms pole_degenerate};
  val _ = audit "X0_empty_on_box_with_pole" [@{thm X0_empty_on_box_with_pole}];
  val _ = audit "feasible_ball_outside_X0" [@{thm feasible_ball_outside_X0}];
  val _ = audit "design_cvec_eq_0_iff" [@{thm design_cvec_eq_0_iff}];
  val _ = audit "F0_dip_nonempty_final_explicit" [@{thm F0_dip_nonempty_final_explicit}];
  val _ = audit "regular_feasible_configuration_exists" [@{thm regular_feasible_configuration_exists}];
  val _ = audit "F0_dip_nonempty_example" [@{thm F0_dip_nonempty_example}];
  val _ = audit "negligible_of_countable_line_slices" [@{thm negligible_of_countable_line_slices}];
  val _ = audit "negligible_res_f_zeros" [@{thm negligible_res_f_zeros}];
  val _ = audit "residual_point_equations" @{thms residual_point_equations};
  val _ = audit "residual_set_point_equations" @{thms residual_set_point_equations};
  val _ = audit "design_radial_equation" [@{thm design_radial_equation}];
  val _ = audit "design_radial_degenerate" [@{thm design_radial_degenerate}];
  val _ = audit "design_perp_equation" [@{thm design_perp_equation}];
  val _ = audit "chart_image_cover" [@{thm chart_image_cover}];
  val _ = audit "nonaligned_point_in_chart_image" [@{thm nonaligned_point_in_chart_image}];
  val _ = audit "nonaligned_residual_cover" [@{thm nonaligned_residual_cover}];
  val _ = audit "aligned_bad_closed_cover" [@{thm aligned_bad_closed_cover}];
  val _ = audit "residual_set_design_cover" [@{thm residual_set_design_cover}];
  val _ = audit "residual_meager_design" [@{thm residual_meager_design}];
  val _ = audit "gdip_real_analytic" [@{thm gdip_real_analytic}];
  val _ = audit "gain_dip_real_analytic" [@{thm gain_dip_real_analytic}];
\<close>

end
