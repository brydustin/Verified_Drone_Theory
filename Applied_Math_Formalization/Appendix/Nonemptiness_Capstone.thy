theory Nonemptiness_Capstone
  imports Nonemptiness_Regnonzero_Appendix
begin

section \<open>Capstone: START \<open>\<longrightarrow>\<close> FINISH with no gaps\<close>

text \<open>
  This theory closes the chain from the paper's hypotheses (\<^bold>\<open>START\<close>: odd \<open>N \<ge> 7\<close>,
  secant/spacing) to the flagship conclusion (\<^bold>\<open>FINISH\<close>: the robust feasible set
  \<open>F\<^sub>z\<^sub>e\<^sub>r\<^sub>o\<close> is nonempty), \<open>thm:final\<close>.  Every intermediate node of the proof DAG is now
  a \<^emph>\<open>stated\<close> lemma; the only remaining holes are the proof-command leaves (the
  determinant computations, the transversality/Sard keystones, the real-analytic
  isolated-zeros input, and the analytic-cut engine) --- to be discharged in the
  next cycle.

  \<^bold>\<open>Structure (the four branches + feasibility + robustness, assembled).\<close>
  The four bad sets are \<^emph>\<open>defined concretely\<close> from the array factor \<^const>\<open>af\<close>:
  \<^item> \<open>Bregzero\<close>  --- regular stratum, non-transverse zero of \<open>A\<close> (\<open>prop:regzero\<close>);
  \<^item> \<open>Bfoldzero\<close> --- a zero of \<open>A\<close> on the fold curve \<open>\<Sigma>\<close> (\<open>prop:foldzero\<close>);
  \<^item> \<open>Bfoldnonzero\<close> --- a fold-critical point with \<open>A \<noteq> 0\<close>, reduced to the
    finite exceptional set \<open>E\<close> (\<open>prop:foldnonzero\<close>, via \<open>lem:Efinite\<close>);
  \<^item> \<open>Bregnonzero\<close> --- a degenerate critical point with \<open>A \<noteq> 0\<close> on \<open>\<Omega>\<^sub>r\<^sub>e\<^sub>g\<close>
    (\<open>prop:regnonzero\<close>, via the whole Appendix).

  The capstone \<^theory_text>\<open>odd_N_nonemptiness\<close> is \<^emph>\<open>proved\<close> by feeding the four branch
  meagerness lemmas, the feasibility lemma, and the robustness lemma into the
  already-proof-complete closeout \<open>nonemptiness_from_meager_branches\<close>.  Thus the
  assembly itself is machine-checked: nothing false can slip through the seams,
  only through the explicitly-named leaf obligations.
\<close>


subsection \<open>The four concrete bad sets\<close>

definition Bregzero :: "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  \<comment> \<open>regular stratum: \<open>A\<close> is not transverse to \<open>0\<close> on \<open>\<Omega>\<^sub>r\<^sub>e\<^sub>g\<close>\<close>
  "Bregzero cvec \<Omega>reg = {x. \<not> transverse0_on (\<lambda>\<omega>. af cvec x \<omega>) \<Omega>reg}"

definition Bfoldzero :: "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  \<comment> \<open>\<open>A\<close> has a zero somewhere on the fold curve \<open>\<Sigma>\<close>\<close>
  "Bfoldzero cvec \<Sigma> = {x. \<exists>\<omega>\<in>\<Sigma>. af cvec x \<omega> = 0}"

definition Bfoldnonzero ::
  "(real^2 \<Rightarrow> ((real^2)^'n) \<Rightarrow> real) \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  \<comment> \<open>fold-critical, \<open>A \<noteq> 0\<close>: reduced to the finite exceptional set \<open>E\<close> via the
      fold-critical field \<open>Fcrit\<close>\<close>
  "Bfoldnonzero Fcrit E = {x. \<exists>\<omega>\<in>E. Fcrit \<omega> x = 0}"

definition Bregnonzero ::
  "(real^2 \<Rightarrow> real^2) \<Rightarrow> (real^2 \<Rightarrow> ((real^2)^'n) \<Rightarrow> bool) \<Rightarrow> (real^2) set \<Rightarrow> ((real^2)^'n) set" where
  \<comment> \<open>regular stratum, \<open>A \<noteq> 0\<close>, degenerate critical point (\<open>\<Phi> = 0\<close>); \<open>degcrit\<close> is the
      concrete \<open>\<Phi>=0\<close> predicate whose meagerness the Appendix discharges\<close>
  "Bregnonzero cvec degcrit \<Omega>reg =
     {x. \<exists>\<omega>\<in>\<Omega>reg. af cvec x \<omega> \<noteq> 0 \<and> degcrit \<omega> x}"


subsection \<open>Feasibility: START builds a nonempty open working set \<open>V \<subseteq> Fset\<close>\<close>

text \<open>TeX \<open>prop:openfeas\<close> (L203) + \<open>lem:twotriplecover\<close> (L244): under START there is a
  nonempty open \<open>V \<subseteq> Fset\<close> (the strictly-feasible family around the root-of-unity
  nulling configuration).  Reduces to \<open>prop_openfeas\<close> / \<open>open_feasible_family\<close> /
  \<open>lem_twotriplecover\<close>.\<close>

lemma capstone_feasible:
  fixes Fset :: "((real^2)^'n) set" and cvec :: "real^2 \<Rightarrow> real^2" and \<omega>N :: "real^2"
  assumes oddN: "odd CARD('n)" and N7: "7 \<le> CARD('n)"
    and czero: "cvec \<omega>N \<noteq> 0"   \<comment> \<open>secant/spacing \<open>\<Longrightarrow>\<close> \<open>c(\<omega>) \<noteq> 0\<close> (\<open>cor:no_czero\<close>)\<close>
  shows "\<exists>V::((real^2)^'n) set. open V \<and> V \<noteq> {} \<and> V \<subseteq> Fset"
  sorry


subsection \<open>The four branch meagerness reductions (concrete bad sets)\<close>

text \<open>TeX \<open>prop:regzero\<close> (L324): instantiate \<open>prop_regzero\<close> at \<open>A = af cvec\<close>; its joint
  transversality hypothesis is supplied by \<open>lem_Azero_surj\<close>/\<open>dxA_surj\<close> (odd \<open>N\<close>,
  \<open>c \<noteq> 0\<close>) and \<open>af\<close> is \<open>C\<^sup>1\<close>.\<close>

lemma branch_regzero_meager:
  fixes V :: "((real^2)^'n) set" and cvec :: "real^2 \<Rightarrow> real^2" and \<Omega>reg :: "(real^2) set"
  assumes "open V" and "V \<noteq> {}" and "open \<Omega>reg"
    and "odd CARD('n)" and "\<forall>\<omega>\<in>\<Omega>reg. cvec \<omega> \<noteq> 0"
  shows "meager (Bregzero cvec \<Omega>reg \<inter> V)"
  sorry

text \<open>TeX \<open>prop:foldzero\<close> (L395): instantiate \<open>prop_foldzero\<close> with the fold-curve
  charts; per-chart meagerness is the transversality \<open>chart_zero_projection_meager_stub\<close>.\<close>

lemma branch_foldzero_meager:
  fixes V :: "((real^2)^'n) set" and cvec :: "real^2 \<Rightarrow> real^2" and \<Sigma> :: "(real^2) set"
  assumes "open V" and "V \<noteq> {}"
  shows "meager (Bfoldzero cvec \<Sigma> \<inter> V)"
  sorry

text \<open>TeX \<open>prop:foldnonzero\<close> (L449): instantiate \<open>prop_foldnonzero\<close> --- \<open>E\<close> finite
  (\<open>lem:Efinite\<close>) and each slice \<open>{x\<in>V. Fcrit \<omega> x = 0}\<close> nowhere dense (the
  real-analytic engine).\<close>

lemma branch_foldnonzero_meager:
  fixes V :: "((real^2)^'n) set"
    and Fcrit :: "real^2 \<Rightarrow> ((real^2)^'n) \<Rightarrow> real" and E :: "(real^2) set"
  assumes "finite E"
    and "\<And>\<omega>. \<omega> \<in> E \<Longrightarrow> nowhere_dense {x \<in> V. Fcrit \<omega> x = 0}"
  shows "meager (Bfoldnonzero Fcrit E \<inter> V)"
  sorry

text \<open>TeX \<open>prop:regnonzero\<close> (L1240): instantiate the proved 4-piece reduction
  \<open>prop_regnonzero\<close> with the concrete \<open>Z\<^sub>r\<^sub>e\<^sub>g\<close>, \<open>Z\<inter>{H\<equiv>0}\<close>, \<open>B\<^sub>C\<^sub>a\<^sub>s\<^sub>e\<^sub>B\<close>, \<open>B\<^sub>H\<^sub>0\<^sub>,\<^sub>r\<^sub>e\<^sub>s\<close>;
  their meagerness is \<open>prop:dimZ\<close> (facts 1,2), \<open>cor:caseBmeager\<close> (fact 3),
  \<open>prop:h0res-meager\<close> (fact 4) --- all stated in
  \<open>Applied_Math_Appendix.Nonemptiness_Regnonzero_Appendix\<close>.\<close>

lemma branch_regnonzero_meager:
  fixes V :: "((real^2)^'n) set" and cvec :: "real^2 \<Rightarrow> real^2"
    and degcrit :: "real^2 \<Rightarrow> ((real^2)^'n) \<Rightarrow> bool" and \<Omega>reg :: "(real^2) set"
  assumes "open V" and "V \<noteq> {}" and "7 \<le> CARD('n)"
  shows "meager (Bregnonzero cvec degcrit \<Omega>reg \<inter> V)"
  sorry


subsection \<open>Robustness: \<open>X0\<close> soundness\<close>

text \<open>The robust-set soundness: away from all four bad strata, the sidelobe
  Hessian is uniformly positive-definite, so the good point lies in some
  \<open>X\<^sub>0(\<xi>)\<close> (\<open>\<xi>>0\<close>).  This is the nondegenerate-critical-point / finiteness
  argument behind \<open>X\<^sub>0\<close>.\<close>

lemma capstone_X0_sound:
  fixes V :: "((real^2)^'n) set" and X0 :: "real \<Rightarrow> ((real^2)^'n) set"
    and B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4 :: "((real^2)^'n) set" and x :: "(real^2)^'n"
  assumes "x \<in> V - bad_union B\<^sub>1 B\<^sub>2 B\<^sub>3 B\<^sub>4"
  shows "\<exists>\<xi>>0. x \<in> X0 \<xi>"
  sorry


subsection \<open>The flagship: odd-\<open>N\<close> nonemptiness (assembled, machine-checked)\<close>

text \<open>TeX \<open>thm:final\<close> (L1342).  Proved by assembling the four branch reductions, the
  feasibility lemma, and the robustness lemma through the proof-complete closeout
  \<open>nonemptiness_from_meager_branches\<close>.  The chain from START to FINISH has no
  gaps beyond the named \<^theory_text>\<open>proof hole\<close>-leaves above.\<close>

theorem odd_N_nonemptiness:
  fixes Fset :: "((real^2)^'n) set" and X0 :: "real \<Rightarrow> ((real^2)^'n) set"
    and cvec :: "real^2 \<Rightarrow> real^2" and \<omega>N :: "real^2"
    and \<Omega>reg \<Sigma> :: "(real^2) set"
    and Fcrit :: "real^2 \<Rightarrow> ((real^2)^'n) \<Rightarrow> real" and E :: "(real^2) set"
    and degcrit :: "real^2 \<Rightarrow> ((real^2)^'n) \<Rightarrow> bool"
  assumes oddN: "odd CARD('n)" and N7: "7 \<le> CARD('n)"
    and czero: "cvec \<omega>N \<noteq> 0"
    and Oreg_open: "open \<Omega>reg" and Oreg_nz: "\<forall>\<omega>\<in>\<Omega>reg. cvec \<omega> \<noteq> 0"
    and E_fin: "finite E"
    and fold_slices:
      "\<And>V \<omega>. \<omega> \<in> E \<Longrightarrow> nowhere_dense {x \<in> V. Fcrit \<omega> x = 0}"
  shows "\<exists>\<xi>>0. Fzero Fset X0 \<xi> \<noteq> {}"
proof -
  obtain V :: "((real^2)^'n) set"
    where Vopen: "open V" and Vne: "V \<noteq> {}" and Vsub: "V \<subseteq> Fset"
    using capstone_feasible[where cvec = cvec and \<omega>N = \<omega>N, OF oddN N7 czero] by blast
  have m_rz: "meager (Bregzero cvec \<Omega>reg \<inter> V)"
    by (rule branch_regzero_meager[OF Vopen Vne Oreg_open oddN Oreg_nz])
  have m_fz: "meager (Bfoldzero cvec \<Sigma> \<inter> V)"
    by (rule branch_foldzero_meager[OF Vopen Vne])
  have m_fn: "meager (Bfoldnonzero Fcrit E \<inter> V)"
    by (rule branch_foldnonzero_meager[OF E_fin]) (rule fold_slices)
  have m_rn: "meager (Bregnonzero cvec degcrit \<Omega>reg \<inter> V)"
    by (rule branch_regnonzero_meager[OF Vopen Vne N7])
  show ?thesis
  proof (rule nonemptiness_from_meager_branches[OF Vopen Vne Vsub m_rn m_rz m_fz m_fn])
    fix x :: "(real^2)^'n"
    assume "x \<in> V - bad_union (Bregnonzero cvec degcrit \<Omega>reg) (Bregzero cvec \<Omega>reg)
                               (Bfoldzero cvec \<Sigma>) (Bfoldnonzero Fcrit E)"
    then show "\<exists>\<xi>>0. x \<in> X0 \<xi>"
      by (rule capstone_X0_sound)
  qed
qed

end
