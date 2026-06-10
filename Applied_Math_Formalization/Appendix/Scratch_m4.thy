theory Scratch_m4
  imports "Applied_Math_Appendix.Nonemptiness_Robust2"
begin

text \<open>Development scratch for (M4) \<open>meager_bad_regular_stratum\<close>: cover the open
  triple-regularity locus by countably many product boxes, run
  \<open>parametric_transversality_meager_planar_config\<close> on each, and inject the
  degenerate-critical set via det-Hessian = 0 \<open>\<Longrightarrow>\<close> no surjective slice
  derivative.\<close>

subsection \<open>Helper 1: \<open>regular_value_on\<close> restricts to subsets\<close>

lemma regular_value_on_subset:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes reg: "regular_value_on f S y" and sub: "T \<subseteq> S"
  shows "regular_value_on f T y"
proof (rule regular_value_onI)
  fix x assume xT: "x \<in> T" and fx: "f x = y"
  have xS: "x \<in> S" using xT sub by blast
  have ex: "\<exists>f'. (f has_derivative f') (at x within S) \<and> surj f'"
    by (rule mp[OF bspec[OF reg[unfolded regular_value_on_def] xS] fx])
  then obtain f' where d: "(f has_derivative f') (at x within S)" and s: "surj f'"
    by (elim exE conjE)
  have "(f has_derivative f') (at x within T)"
    by (rule has_derivative_subset[OF d sub])
  then show "\<exists>f'. (f has_derivative f') (at x within T) \<and> surj f'"
    using s by blast
qed

subsection \<open>Helper 2: countable product-box cover of an open set in a product space\<close>

lemma open_prod_nat_cover:
  fixes W :: "(('a::second_countable_topology) \<times> ('b::second_countable_topology)) set"
  assumes oW: "open W"
  shows "\<exists>A :: nat \<Rightarrow> 'a set. \<exists>B :: nat \<Rightarrow> 'b set.
           (\<forall>n. open (A n)) \<and> (\<forall>n. open (B n)) \<and> (\<forall>n. A n \<times> B n \<subseteq> W)
         \<and> (\<Union>n. A n \<times> B n) = W"
proof -
  obtain BA :: "'a set set" where cA: "Countable_Set.countable BA" and tA: "topological_basis BA"
    using ex_countable_basis by blast
  obtain BB :: "'b set set" where cB: "Countable_Set.countable BB" and tB: "topological_basis BB"
    using ex_countable_basis by blast
  define P :: "('a set \<times> 'b set) set"
    where "P = {q \<in> BA \<times> BB. fst q \<times> snd q \<subseteq> W}"
  have cAB: "Countable_Set.countable (BA \<times> BB)"
    by (intro countable_SIGMA cA cB)
  have Psub: "P \<subseteq> BA \<times> BB" unfolding P_def by auto
  have cP: "Countable_Set.countable P" by (rule countable_subset[OF Psub cAB])
  have cover: "(\<Union>q\<in>P. fst q \<times> snd q) = W"
  proof
    show "(\<Union>q\<in>P. fst q \<times> snd q) \<subseteq> W" unfolding P_def by auto
    show "W \<subseteq> (\<Union>q\<in>P. fst q \<times> snd q)"
    proof
      fix p assume pW: "p \<in> W"
      obtain a b where pab: "p = (a, b)" by fastforce
      have exAB: "\<exists>Ao Bo. open Ao \<and> open Bo \<and> (a, b) \<in> Ao \<times> Bo \<and> Ao \<times> Bo \<subseteq> W"
        by (rule bspec[OF oW[unfolded open_prod_def] pW[unfolded pab]])
      then obtain Ao Bo where ABo0: "open Ao" "open Bo" "(a, b) \<in> Ao \<times> Bo" "Ao \<times> Bo \<subseteq> W"
        by (elim exE conjE)
      have ABo: "open Ao" "open Bo" "a \<in> Ao" "b \<in> Bo" "Ao \<times> Bo \<subseteq> W"
        using ABo0 by auto
      obtain UA where UA: "UA \<in> BA" "a \<in> UA" "UA \<subseteq> Ao"
        using topological_basisE[OF tA ABo(1) ABo(3)] by blast
      obtain UB where UB: "UB \<in> BB" "b \<in> UB" "UB \<subseteq> Bo"
        using topological_basisE[OF tB ABo(2) ABo(4)] by blast
      have UTsub: "UA \<times> UB \<subseteq> W" using UA(3) UB(3) ABo(5) by blast
      have qP: "(UA, UB) \<in> P" unfolding P_def using UA(1) UB(1) UTsub by auto
      show "p \<in> (\<Union>q\<in>P. fst q \<times> snd q)"
        using qP UA(2) UB(2) unfolding pab by force
    qed
  qed
  show ?thesis
  proof (cases "P = {}")
    case True
    then have Wempty: "W = {}" using cover by simp
    show ?thesis
      by (intro exI[of _ "\<lambda>n. ({} :: 'a set)"] exI[of _ "\<lambda>n. ({} :: 'b set)"])
         (simp add: Wempty)
  next
    case False
    define F where "F = from_nat_into P"
    have FP: "\<And>n. F n \<in> P" unfolding F_def by (rule from_nat_into[OF False])
    have rF: "range F = P" unfolding F_def by (rule range_from_nat_into[OF False cP])
    have uF: "(\<Union>n. fst (F n) \<times> snd (F n)) = (\<Union>q\<in>P. fst q \<times> snd q)"
    proof -
      have "(\<Union>n. fst (F n) \<times> snd (F n)) = (\<Union>q\<in>range F. fst q \<times> snd q)" by blast
      also have "\<dots> = (\<Union>q\<in>P. fst q \<times> snd q)" unfolding rF by (rule refl)
      finally show ?thesis .
    qed
    have FAB: "\<And>n. F n \<in> BA \<times> BB" using FP Psub by blast
    have openA: "\<And>n. open (fst (F n))"
    proof -
      fix n :: nat
      have "fst (F n) \<in> BA" using FAB[of n] by (simp add: mem_Times_iff)
      then show "open (fst (F n))" by (rule topological_basis_open[OF tA])
    qed
    have openB: "\<And>n. open (snd (F n))"
    proof -
      fix n :: nat
      have "snd (F n) \<in> BB" using FAB[of n] by (simp add: mem_Times_iff)
      then show "open (snd (F n))" by (rule topological_basis_open[OF tB])
    qed
    have subW: "\<And>n. fst (F n) \<times> snd (F n) \<subseteq> W"
      using FP unfolding P_def by auto
    show ?thesis
      by (intro exI[of _ "\<lambda>n. fst (F n)"] exI[of _ "\<lambda>n. snd (F n)"] conjI)
         (use openA openB subW uF cover in auto)
  qed
qed

subsection \<open>Helper 3: degenerate Hessian forbids a surjective slice derivative\<close>

lemma dip_slice_no_surj_deriv:
  fixes x :: "(real^2)^'n" and \<omega> \<omega>0 \<omega>s :: "real^2" and C :: "(real^2) set"
  assumes oC: "open C" and wC: "\<omega> \<in> C"
    and hess0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0"
  shows "\<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                  (at \<omega> within C) \<and> surj D)"
proof
  assume "\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                (at \<omega> within C) \<and> surj D"
  then obtain D where
    dD: "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D) (at \<omega> within C)"
    and sD: "surj D" by (elim exE conjE)
  have dD': "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D) (at \<omega>)"
    using dD by (simp add: at_within_open[OF wC oC])
  have dH: "((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative
              (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)) (at \<omega>)"
    by (rule gradU_dip_has_derivative)
  have DH: "D = (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> *v v)"
    by (rule has_derivative_unique[OF dD' dH])
  have "surj ((*v) (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>))"
    using sD unfolding DH by simp
  then have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) \<noteq> 0"
    by (simp add: surj_matrix_vector_iff_det)
  with hess0 show False by simp
qed

subsection \<open>(M4) The regular stratum is meager\<close>

lemma meager_bad_regular_stratum:
  fixes V :: "((real^2)^'n) set" and \<omega>0 \<omega>s :: "real^2"
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
  shows "meager {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
proof -
  \<comment> \<open>The open triple-regularity locus over \<open>V\<close>.\<close>
  define WV :: "(((real^2)^'n) \<times> (real^2)) set"
    where "WV = {p \<in> V \<times> UNIV. A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
                             \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
                             \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}"
  have WVeq: "WV = (V \<times> UNIV) \<inter> {p :: ((real^2)^'n) \<times> (real^2).
                 A_cart (cvec_dip \<omega>0 \<omega>s) (fst p) (snd p) \<noteq> 0
               \<and> surj (DM_paper_x (fst p) (cvec_dip \<omega>0 \<omega>s (snd p)))
               \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s (snd p))) \<noteq> 0}"
    unfolding WV_def by auto
  have oWV: "open WV"
    unfolding WVeq
    by (intro open_Int open_Times openV open_UNIV open_A_cart_nonzero)
  have regWV: "regular_value_on
      (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) WV 0"
    unfolding WV_def by (rule regular_value_on_gradU_dip[OF openV c6])
  \<comment> \<open>Global \<open>C\<^sup>1\<close> data for the joint gradient field.\<close>
  obtain G' :: "(((real^2)^'n) \<times> (real^2)) \<Rightarrow> ((((real^2)^'n) \<times> (real^2)) \<Rightarrow>\<^sub>L (real^2))"
    where derG: "\<And>z. ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
                       has_derivative blinfun_apply (G' z)) (at z)"
      and contG': "continuous_on UNIV G'"
    using gradU_dip_joint_C1 by blast
  \<comment> \<open>Countable product-box cover of the locus.\<close>
  obtain A :: "nat \<Rightarrow> ((real^2)^'n) set" and B :: "nat \<Rightarrow> (real^2) set"
    where boxA: "\<And>n. open (A n)" and boxB: "\<And>n. open (B n)"
      and boxsub: "\<And>n. A n \<times> B n \<subseteq> WV"
      and boxun: "(\<Union>n. A n \<times> B n) = WV"
    using open_prod_nat_cover[OF oWV] by blast
  \<comment> \<open>The engine's bad set over each box.\<close>
  define bad :: "nat \<Rightarrow> ((real^2)^'n) set"
    where "bad n = {x \<in> A n. \<exists>\<omega>\<in>B n.
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and>
        \<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                 (at \<omega> within B n) \<and> surj D)}" for n
  have mbad: "\<And>n. meager (bad n)"
  proof -
    fix n :: nat
    show "meager (bad n)"
    proof (cases "A n = {}")
      case True
      then have "bad n = {}" unfolding bad_def by simp
      then show ?thesis by simp
    next
      case False
      have derGn: "\<And>z. z \<in> A n \<times> B n \<Longrightarrow>
          ((\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
             has_derivative blinfun_apply (G' z)) (at z)"
        by (rule derG)
      have contGn: "continuous_on (A n \<times> B n) G'"
        by (rule continuous_on_subset[OF contG' subset_UNIV])
      have regn: "regular_value_on
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (A n \<times> B n) 0"
        by (rule regular_value_on_subset[OF regWV boxsub])
      have "meager {x \<in> A n. \<exists>\<omega>\<in>B n.
          (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x, \<omega>) = 0 \<and>
          \<not> (\<exists>D. ((\<lambda>u. (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p)) (x, u))
                   has_derivative D) (at \<omega> within B n) \<and> surj D)}"
        using parametric_transversality_meager_planar_config[OF boxA False boxB
                derGn contGn regn] by blast
      then show ?thesis unfolding bad_def by simp
    qed
  qed
  have un_meager: "meager (\<Union>n. bad n)"
    by (rule meager_Union_nat) (rule mbad)
  \<comment> \<open>The M4 bad set injects into the union of engine bad sets.\<close>
  have inj_sub: "{x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0} \<subseteq> (\<Union>n. bad n)"
  proof
    fix x assume "x \<in> {x \<in> V. \<exists>\<omega>. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0
                  \<and> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0
                  \<and> A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0
                  \<and> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))
                  \<and> det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0}"
    then obtain \<omega> :: "real^2" where
      xV: "x \<in> V" and
      g0: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0" and
      h0: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) = 0" and
      anz: "A_cart (cvec_dip \<omega>0 \<omega>s) x \<omega> \<noteq> 0" and
      dms: "surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))" and
      dcz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
      by blast
    have inWV: "(x, \<omega>) \<in> WV"
      unfolding WV_def using xV anz dms dcz by simp
    then obtain n where "(x, \<omega>) \<in> A n \<times> B n"
      using boxun by blast
    then have xA: "x \<in> A n" and wB: "\<omega> \<in> B n" by auto
    have nos: "\<not> (\<exists>D. ((\<lambda>u. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x u) has_derivative D)
                       (at \<omega> within B n) \<and> surj D)"
      by (rule dip_slice_no_surj_deriv[OF boxB wB h0])
    have "x \<in> bad n"
      unfolding bad_def using xA wB g0 nos by blast
    then show "x \<in> (\<Union>n. bad n)" by blast
  qed
  show ?thesis by (rule meager_subset[OF inj_sub un_meager])
qed

end
