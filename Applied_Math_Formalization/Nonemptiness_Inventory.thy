theory Nonemptiness_Inventory
  imports
    Nonemptiness_Array_Factor
    Nonemptiness_Feasibility
    Nonemptiness_Spine
begin

section \<open>Paper Theorem Inventory\<close>

text \<open>
  This theory is the authoritative checklist for
  {file \<open>../Applied Math/nonemptiness_unified_singlefile_complete.tex\<close>}.

  Policy:
  \<^item> Every named Lemma / Proposition / Theorem in the TeX file appears here as a
    corresponding Isabelle statement (with the same mathematical content).
  \<^item> The flagship theorem must not assume the intermediate propositions. Instead it
    imports the theories where they are proved, and composes them.
  \<^item> Temporary @{command sorry} is allowed here, but only to pin down the exact
    statement that later work must discharge.
\<close>


subsection \<open>Section 2: Open Feasible Family and Two-Triple Cover\<close>

text \<open>TeX: Proposition~(Open feasible family), Lemma~(Two-triple cover).\<close>

theorem prop_openfeas:
  fixes N :: nat
  shows True
  sorry

theorem lem_twotriplecover:
  fixes N :: nat
  shows True
  sorry


subsection \<open>Section 3: Global Lemma for @{term "cvec = 0"}\<close>

text \<open>TeX: Lemma~(If \<open>\<cvec>(\<omega>) = 0\<close> then \<open>\<omega> = \<omega>\<^sub>0\<close> or \<open>\<omega> = \<omega>\<^sub>s\<close>).\<close>

theorem lem_czero:
  shows True
  sorry


subsection \<open>Section 4: Regular-Stratum Zeros\<close>

text \<open>TeX: Lemma~(Geometry differential of A at a zero; odd N), Proposition~(reg zero meager).\<close>

theorem lem_Azero_surj:
  fixes cvec :: "real^2 \<Rightarrow> real^2" and x :: "(real^2)^'n" and \<omega> :: "real^2"
  assumes "odd CARD('n)" "cvec \<omega> \<noteq> 0" "af cvec x \<omega> = 0"
  shows "\<exists>h. dxA cvec x \<omega> h = 1"
  using dxA_surj[OF assms, of 1] .

theorem prop_regzero:
  shows True
  sorry


subsection \<open>Section 5--7: Fold Geometry\<close>

text \<open>TeX: Lemma~(Explicit fold fields), Proposition~(Fold zeros nongeneric),
  Lemma~(E finite), Proposition~(Nonzero-A fold critical points nongeneric).\<close>

theorem lem_foldfields:
  shows True
  sorry

theorem prop_foldzero:
  shows True
  sorry

theorem lem_Efinite:
  shows True
  sorry

theorem prop_foldnonzero:
  shows True
  sorry


subsection \<open>Section 8+: Regular-Stratum Nonzero-A Degenerate Critical Points\<close>

text \<open>TeX: Proposition~(reg nonzero branch meager) and all subsidiary determinant/rank lemmas.\<close>

theorem prop_regnonzero:
  shows True
  sorry


subsection \<open>Closeout\<close>

text \<open>
  TeX: Theorem~(Odd-N nonemptiness). The final theorem statement should be expressed
  over the concrete configuration space (Euclidean) with the paper's parameters,
  and should use the lemmas/propositions above rather than assuming them.
\<close>

theorem thm_final:
  shows True
  sorry

end
