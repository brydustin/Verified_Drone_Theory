theory Unused_Facts
  imports "Applied_Math_Main.Poles_And_Fixed_Margins" "Applied_Math_Pattern.Dipole_Gain_Analytic"
begin

text \<open>Lists the named lemmas of the proof chain on which none of the theorems below depends, and fails
  if there is one.  The roots are the theorems of \<open>Audit/Oracle_Audit.thy\<close> and the statements cited in the
  write-up.  Run from the formalization directory:
  \<open>isabelle process_theories -O -d . -l Applied_Math_Main -D tools/unused_facts Unused_Facts\<close>.\<close>

ML \<open>
  val thy = \<^theory>;
  val chain =
    ["Munkres_Baire_Bridge", "Meager_Sets", "Regular_Value_Theorem", "Parametric_Transversality_Euclidean",
     "Parametric_Transversality_Planar", "Line_Entire_Functions", "Negligible_Line_Slices", "Array_Factor",
     "Moment_Map", "Pattern_Derivatives", "Feasible_Set", "Dipole_Pattern",
     "Dipole_Gain_Derivatives", "Dipole_Gain_Analytic", "Robust_Sets", "Feasibility_Witness",
     "Pattern_Moments", "Gradient_Field_C1", "Null_Stratum", "Regular_Stratum",
     "Critical_Slices", "Main_Beam_Stratum", "Steering_Singular_Stratum", "Residual_Phase_Equation",
     "Residual_Equations", "Residual_Design", "Residual_Charts", "Residual_Chart_Cover",
     "Residual_Aligned", "Residual_Meager", "Degenerate_Configurations", "Poles_And_Fixed_Margins"];
  val roots =
    ["F0_dip_interior_nonempty", "F0_dip_nonempty_example", "F0_dip_nonempty_final",
     "F0_dip_nonempty_final_explicit", "HessU_beamcenter_entry", "X0_closed",
     "X0_empty_of_pole", "X0_empty_on_box_with_pole", "X0_lower_margins_ball",
     "aligned_bad_closed_cover", "aligned_quantization", "chart_image_cover",
     "closed_exists_compact", "collinear_null_degenerate", "degenerate_configurations",
     "degenerate_configurations_meager", "degenerate_configurations_nowhere_dense", "degenerate_set_closed",
     "design_cvec_eq_0_iff", "design_perp_equation", "design_radial_degenerate",
     "design_radial_equation", "design_strictly_feasible_collinear", "det_HessU_at_null",
     "dxA_surj", "feasible_ball_outside_X0", "gain_dip_Cinfinity",
     "gain_dip_real_analytic", "gdip_Cinfinity", "gdip_Ck_on",
     "gdip_deriv_zero_iff", "gdip_eq_edip_sq", "gdip_real_analytic",
     "gdip_scalar_second_deriv_nonzero", "gradU_combination", "gradU_x_derivative_slot_combination",
     "isolated_nondeg_zero", "lines_entire_slice_nowhere_dense", "meager_Azero_degenerate_stratum",
     "meager_grad_x_regular_part", "meager_main_beam", "meager_negligible_closed_cover",
     "meager_steering_singular", "negligible_of_countable_line_slices", "negligible_res_f_zeros",
     "nonaligned_point_in_chart_image", "nonaligned_residual_cover", "nondegenerate_dense_in_open",
     "nondegenerate_in_X0", "nondegenerate_open_dense", "parametric_transversality_meager_planar_config",
     "pole_degenerate", "regular_feasible_configuration_exists", "regular_value_local_chart",
     "residual_meager_design", "residual_point_equations", "residual_set_design_cover",
     "residual_set_point_equations", "sigma_min_pos_iff_invertible", "steering_singular_gdip_deriv_zero"];

  fun lookup ((name, i): Thm_Name.T) =
    (let val ths = Global_Theory.get_thms thy name
     in if i = 0 then ths else [nth ths (i - 1)] end) handle ERROR _ => [] | General.Subscript => [];
  fun closure seen [] = seen
    | closure seen (n :: rest) =
        if Thm_Name.Set.member seen n then closure seen rest
        else closure (Thm_Name.Set.insert n seen) (map #2 (Thm_Deps.thm_deps thy (lookup n)) @ rest);

  val theories = filter (fn t => member (op =) chain (Context.theory_base_name t)) (Theory.ancestors_of thy);
  fun own t = map #1 (Facts.dest_static false (map Global_Theory.facts_of (Theory.parents_of t)) (Global_Theory.facts_of t));
  val facts = maps own theories;
  fun base s = List.last (space_explode "." s);
  fun is_root s = member (op =) roots (base s) orelse member (op =) roots (perhaps (try (unsuffix "_def")) (base s));
  val root_names = filter is_root facts;
  val _ = app (fn r => if exists (fn s => base s = r orelse base s = r ^ "_def") facts then ()
    else error ("no such fact: " ^ r)) roots;
  val used = closure Thm_Name.Set.empty (map (fn s => (s, 0)) root_names);
  val used_names = Symtab.make_set (map #1 (Thm_Name.Set.dest used));
  (* lemmas only: a definition gives a fact named ..._def, a recursive function gives facts with a further dot *)
  fun is_lemma s = length (space_explode "." s) = 2 andalso not (String.isSuffix "_def" s);
  val unused = sort_strings (filter (fn s => is_lemma s andalso not (Symtab.defined used_names s)) facts);
  val _ = writeln ("lemmas in the chain: " ^ string_of_int (length (filter is_lemma facts)) ^
    ", roots: " ^ string_of_int (length roots) ^ ", unused: " ^ string_of_int (length unused));
  val _ = app (fn s => writeln ("UNUSED " ^ s)) unused;
  val _ = if null unused then () else error (string_of_int (length unused) ^ " unused lemma(s)");
\<close>

end
