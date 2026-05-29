theory Moment_Jacobian
  imports
    Moment_Map
    Block_Determinants_BigJ
begin

text \<open>
  Real-linear transports between the moment map's natural domain/codomain
  \<open>(\<real>\<^sup>2)\<^sup>6\<close>, \<open>\<complex>\<^sup>6\<close> and the \<open>\<real>\<^sup>1\<^sup>2\<close> used by \<^const>\<open>bigJ\<close>, plus the
  Jacobian identification \<open>D\<^sub>x M_paper(x0, c0) = (*v) bigJ\<close>.

  \<^bold>\<open>Why this lives here\<close> (and not in \<open>Nonemptiness_Paper\<close>): the nested
  vec-projection \<open>(c$i)$j\<close> in \<^term>\<open>transD_inv\<close> elaborates in milliseconds in
  this \<open>HMA_Connect\<close>/\<open>Conformal_Mappings\<close>-free context, but \<^emph>\<open>hangs / runs out of
  store\<close> when those theories are in scope (as they are in \<open>Nonemptiness_Paper\<close>).
  Baking the definitions into the \<open>Applied_Math_BlockDet\<close> heap means downstream
  theories merely \<^emph>\<open>use\<close> the constants (no re-elaboration of the definition).

  \<^bold>\<open>Proof engineering\<close>: each vec equality is reduced to per-component facts
  discharged by a \<^emph>\<open>bounded\<close> \<open>exhaust_N\<close> case split; a blanket
  \<open>forall_12\<close>/\<open>vec_eq_iff\<close> simp over the nested \<open>vector[\<dots>]\<close> exhausts memory.
\<close>

definition transC :: "complex^6 \<Rightarrow> real^12" where
  "transC z = vector
     [ Re (z$1), Im (z$1), Re (z$2), Im (z$2), Re (z$3), Im (z$3),
       Re (z$4), Im (z$4), Re (z$5), Im (z$5), Re (z$6), Im (z$6) ]"

definition transC_inv :: "real^12 \<Rightarrow> complex^6" where
  "transC_inv y = vector
     [ Complex (y$1)  (y$2),  Complex (y$3)  (y$4),  Complex (y$5)  (y$6),
       Complex (y$7)  (y$8),  Complex (y$9)  (y$10), Complex (y$11) (y$12) ]"

definition transD :: "real^12 \<Rightarrow> (real^2)^6" where
  "transD y = vector
     [ vector [y$1,  y$2],  vector [y$3,  y$4],  vector [y$5,  y$6],
       vector [y$7,  y$8],  vector [y$9,  y$10], vector [y$11, y$12] ]"

definition transD_inv :: "(real^2)^6 \<Rightarrow> real^12" where
  "transD_inv c = vector
     [ (c$1)$1, (c$1)$2, (c$2)$1, (c$2)$2, (c$3)$1, (c$3)$2,
       (c$4)$1, (c$4)$2, (c$5)$1, (c$5)$2, (c$6)$1, (c$6)$2 ]"

lemma linear_transC: "linear transC"
proof (rule linearI)
  fix z w :: "complex^6"
  have "transC (z + w) $ i = (transC z + transC w) $ i" for i :: 12
    using exhaust_12[of i] by (elim disjE; simp add: transC_def)
  thus "transC (z + w) = transC z + transC w" by (simp add: vec_eq_iff)
next
  fix r :: real and z :: "complex^6"
  have "transC (r *\<^sub>R z) $ i = (r *\<^sub>R transC z) $ i" for i :: 12
    using exhaust_12[of i] by (elim disjE; simp add: transC_def)
  thus "transC (r *\<^sub>R z) = r *\<^sub>R transC z" by (simp add: vec_eq_iff)
qed

lemma linear_transD: "linear transD"
proof (rule linearI)
  fix y w :: "real^12"
  have "transD (y + w) $ i = (transD y + transD w) $ i" for i :: 6
    using exhaust_6[of i] by (elim disjE; simp add: transD_def vec_eq_iff forall_2)
  thus "transD (y + w) = transD y + transD w" by (simp add: vec_eq_iff)
next
  fix r :: real and y :: "real^12"
  have "transD (r *\<^sub>R y) $ i = (r *\<^sub>R transD y) $ i" for i :: 6
    using exhaust_6[of i] by (elim disjE; simp add: transD_def vec_eq_iff forall_2)
  thus "transD (r *\<^sub>R y) = r *\<^sub>R transD y" by (simp add: vec_eq_iff)
qed

lemma transC_inv_left: "transC_inv (transC z) = z"
proof -
  have "transC_inv (transC z) $ i = z $ i" for i :: 6
    using exhaust_6[of i] by (elim disjE; simp add: transC_def transC_inv_def)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma transC_inv_right: "transC (transC_inv y) = y"
proof -
  have "transC (transC_inv y) $ i = y $ i" for i :: 12
    using exhaust_12[of i] by (elim disjE; simp add: transC_def transC_inv_def)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma transD_inv_left: "transD_inv (transD y) = y"
proof -
  have "transD_inv (transD y) $ i = y $ i" for i :: 12
    using exhaust_12[of i] by (elim disjE; simp add: transD_def transD_inv_def)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma transD_inv_right: "transD (transD_inv c) = c"
proof -
  have "transD (transD_inv c) $ i = c $ i" for i :: 6
    using exhaust_6[of i] by (elim disjE; simp add: transD_def transD_inv_def vec_eq_iff forall_2)
  thus ?thesis by (simp add: vec_eq_iff)
qed

lemma bij_transC: "bij transC"
  by (rule o_bij[of transC_inv transC])
     (simp_all add: fun_eq_iff transC_inv_left transC_inv_right)

lemma bij_transD: "bij transD"
  by (rule o_bij[of transD_inv transD])
     (simp_all add: fun_eq_iff transD_inv_left transD_inv_right)

end
