theory Final_Deps
  imports "Applied_Math_Final.Nonemptiness_Final"
begin

text \<open>Named facts on which the final theorems depend (transitive closure of \<open>Thm_Deps.thm_deps\<close>).
  Run from the formalization directory:
  \<open>isabelle process_theories -O -d . -d <AFP>/thys -l Applied_Math_Final -D tools/final_deps Final_Deps\<close>.
  Prints, for each listed fact, whether it is in the closure.\<close>

ML \<open>
  val thy = \<^theory>;

  fun lookup ((name, i): Thm_Name.T) =
    (let val ths = Global_Theory.get_thms thy name
     in if i = 0 then ths else [nth ths (i - 1)] end) handle ERROR _ => [] | General.Subscript => [];

  fun closure seen [] = seen
    | closure seen (n :: rest) =
        if Thm_Name.Set.member seen n then closure seen rest
        else closure (Thm_Name.Set.insert n seen) (map #2 (Thm_Deps.thm_deps thy (lookup n)) @ rest);

  val roots =
    [("Nonemptiness_Final.F0_dip_nonempty_final", 0),
     ("Nonemptiness_Final.F0_dip_nonempty_final_explicit", 0),
     ("Nonemptiness_Final.regular_feasible_configuration_exists", 0),
     ("Nonemptiness_Final.Phi_bad_meager_design", 0)];
  val _ = app (fn r => if null (lookup r) then error ("no such fact: " ^ Thm_Name.print r) else ()) roots;

  val names = sort_strings (map Thm_Name.print (Thm_Name.Set.dest (closure Thm_Name.Set.empty roots)));
  val _ = writeln ("DEPS facts in the closure: " ^ string_of_int (length names));

  fun base s = List.last (space_explode "." (hd (space_explode "(" s)));
  fun report b =
    let val hits = filter (fn s => base s = b) names
    in writeln ("DEPS " ^ (if null hits then "not used  " else "USED      ") ^ b ^
         (if null hits then "" else "   [" ^ commas hits ^ "]")) end;
  val _ = app report
    ["fixed_c_nonsurj_nowhere_dense", "nowhere_dense_mstarg_zeros", "mstarg_nonzero",
     "DM_paper_x_regular_point_exists", "DM_paper_x_regular_point_c0_gen",
     "DM_paper_x_open_dense_surjective_gen", "bigJ_det", "bigJ_surj", "bigJ_full_rank",
     "surj_iff_mstarg", "m5_D5_steersing", "m5_D5_slice_meager", "M6_slice_nowhere_dense",
     "meager_steering_singular_stratum", "meager_bad_regular_stratum_on",
     "meager_steering_singular", "steering_slice_meager", "critical_slice_nowhere_dense",
     "m5_D2_beamcenter", "meager_Azero_degenerate_stratum", "meager_grad_x_regular_part",
     "residual_meager_design", "gradU_dip_x_partial_surj", "DM_paper_x_null_not_surj"];
  val thys = sort_strings (distinct (op =) (map (fn s => hd (space_explode "." s)) names));
  val _ = writeln ("DEPS theories: " ^ commas thys);
\<close>

end
