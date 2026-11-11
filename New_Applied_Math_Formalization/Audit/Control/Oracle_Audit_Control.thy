theory Oracle_Audit_Control
  imports Main
begin

text \<open>Negative control for the oracle audit: the same test must report the oracle of a
  \<open>sorry\<close>.  This is the only session with \<open>quick_and_dirty = true\<close>.\<close>

lemma control: "(1::nat) = 1"
  sorry

ML \<open>
  val _ =
    (case Thm_Deps.all_oracles [@{thm control}] of
      [] => error "Oracle audit control: the sorry was not detected"
    | _ => ());
\<close>

end
