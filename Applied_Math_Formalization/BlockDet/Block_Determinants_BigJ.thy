theory Block_Determinants_BigJ
  imports
    Block_Determinants
begin

text \<open>
  The full bigJ determinant chain: the 12x12 configuration matrix, the row /
  column permutation reducing it to block-lower-triangular form, the block
  decomposition step, and the final value \<open>det bigJ = -5\<pi>\<^sup>8/3\<close> plus the
  corollaries (\<open>bigJ_full_rank\<close>, \<open>bigJ_surj\<close>). Factored out of
  \<open>Nonemptiness_Paper.thy\<close> so it can be baked into the
  \<open>Applied_Math_BlockDet\<close> heap; once cached, leaf rebuilds of the paper
  theory stay seconds-fast.
\<close>

definition bigJ :: "real^12^12" where
  "bigJ = vector
    [ vector [0, 0, - sqrt 3 / 2, 0, - sqrt 3 / 2, 0, 0, 0, sqrt 3 / 2, 0, sqrt 3 / 2, 0],
      vector [- 1, 0, - 1/2, 0, 1/2, 0, 1, 0, 1/2, 0, - 1/2, 0],
      vector [1, 0, 1/2 - pi * sqrt 3 / 6, 0, - 1/2 - pi * sqrt 3 / 3, 0,
              - 1, 0, - 1/2 + 2 * pi * sqrt 3 / 3, 0, 1/2 + 5 * pi * sqrt 3 / 6, 0],
      vector [0, 0, - sqrt 3 / 2 - pi / 6, 0, - sqrt 3 / 2 + pi / 3, 0,
              pi, 0, sqrt 3 / 2 + 2 * pi / 3, 0, sqrt 3 / 2 - 5 * pi / 6, 0],
      vector [0, 1, - sqrt 3, 1/2, 0, - 1/2, 0, - 1, sqrt 3, - 1/2, sqrt 3, 1/2],
      vector [- 2, 0, - 1, - sqrt 3 / 2, 0, - sqrt 3 / 2, 0, 0, 1, sqrt 3 / 2, - 1, sqrt 3 / 2],
      vector [0, 0, pi / 3 - pi^2 * sqrt 3 / 18, 0, - 2 * pi / 3 - 2 * pi^2 * sqrt 3 / 9, 0,
              - 2 * pi, 0, - 4 * pi / 3 + 8 * pi^2 * sqrt 3 / 9, 0,
              5 * pi / 3 + 25 * pi^2 * sqrt 3 / 18, 0],
      vector [0, 0, - pi * sqrt 3 / 3 - pi^2 / 18, 0, - 2 * pi * sqrt 3 / 3 + 2 * pi^2 / 9, 0,
              pi^2, 0, 4 * pi * sqrt 3 / 3 + 8 * pi^2 / 9, 0,
              5 * pi * sqrt 3 / 3 - 25 * pi^2 / 18, 0],
      vector [2, 0, 1 - pi * sqrt 3 / 3, pi / 6, 0, - pi / 3, 0, - pi,
              - 1 + 4 * pi * sqrt 3 / 3, - 2 * pi / 3, 1 + 5 * pi * sqrt 3 / 3, 5 * pi / 6],
      vector [0, 0, - sqrt 3 - pi / 3, - pi * sqrt 3 / 6, 0, - pi * sqrt 3 / 3, 0, 0,
              sqrt 3 + 4 * pi / 3, 2 * pi * sqrt 3 / 3, sqrt 3 - 5 * pi / 3, 5 * pi * sqrt 3 / 6],
      vector [0, 4, - 2 * sqrt 3, 2, 0, 0, 0, 0, 2 * sqrt 3, - 2, 2 * sqrt 3, 2],
      vector [- 4, 0, - 2, - 2 * sqrt 3, 0, 0, 0, 0, 2, 2 * sqrt 3, - 2, 2 * sqrt 3] ]"

text \<open>
  TeX Lemma~\<open>lem:Msurj\<close>, determinant core (\<open>det J = -5\<pi>\<^sup>8/3\<close> at \<open>\<kappa> = 1\<close>;
  the general value is \<open>-5\<pi>\<^sup>8/(3\<kappa>\<^sup>2)\<close>). The explicit symbolic determinant of
  the configuration matrix \<^const>\<open>bigJ\<close>. Strategy (Determinant.md): reorder
  the rows by \<open>1,2,3,4,7,8,5,6,9,10,11,12\<close> and the columns by
  \<open>1,3,5,7,9,11,2,4,6,8,10,12\<close> to expose a block-lower-triangular form
  \<open>[Ablk | 0; C | Dblk]\<close>; row permutation has sign \<open>+1\<close> (two disjoint swaps),
  column permutation has sign \<open>-1\<close> (15 inversions / 10-cycle); the block
  determinant is \<open>det Ablk \<cdot> det Dblk\<close>; combining gives
  \<open>det bigJ = -det Ablk \<cdot> det Dblk = -(-\<sqrt>3 \<pi>\<^sup>6/18)(-10\<sqrt>3 \<pi>\<^sup>2) = -5\<pi>\<^sup>8/3\<close>.
\<close>

subsubsection \<open>Row and column permutations exposing the block-lower-triangular form\<close>

definition \<sigma>row :: "12 \<Rightarrow> 12" where
  "\<sigma>row = Fun.swap 5 7 (Fun.swap 6 8 id)"

definition \<sigma>col :: "12 \<Rightarrow> 12" where
  "\<sigma>col = Fun.swap 2 3
            (Fun.swap 2 5
              (Fun.swap 2 9
                (Fun.swap 2 6
                  (Fun.swap 2 11
                    (Fun.swap 2 10
                      (Fun.swap 2 8
                        (Fun.swap 2 4
                          (Fun.swap 2 7 id)))))))) "

lemma \<sigma>row_as_comp:
  "\<sigma>row = Fun.swap (6::12) 8 id \<circ> Fun.swap (5::12) 7 id"
  unfolding \<sigma>row_def by (auto simp: comp_def Fun.swap_def fun_eq_iff)

lemma \<sigma>col_as_comp:
  "\<sigma>col = Fun.swap (2::12) 7 id \<circ> Fun.swap (2::12) 4 id \<circ> Fun.swap (2::12) 8 id
        \<circ> Fun.swap (2::12) 10 id \<circ> Fun.swap (2::12) 11 id \<circ> Fun.swap (2::12) 6 id
        \<circ> Fun.swap (2::12) 9 id \<circ> Fun.swap (2::12) 5 id \<circ> Fun.swap (2::12) 3 id"
  unfolding \<sigma>col_def by (auto simp: comp_def Fun.swap_def fun_eq_iff)

lemma \<sigma>row_permutes: "\<sigma>row permutes UNIV"
  by (simp add: \<sigma>row_as_comp permutes_compose permutes_swap_id)

lemma \<sigma>col_permutes: "\<sigma>col permutes UNIV"
  by (simp add: \<sigma>col_as_comp permutes_compose permutes_swap_id)

lemma sign_\<sigma>row: "sign \<sigma>row = 1"
proof -
  have "sign \<sigma>row = sign (Fun.swap (6::12) 8 id) * sign (Fun.swap (5::12) 7 id)"
    by (simp add: \<sigma>row_as_comp sign_compose permutation_swap_id)
  thus ?thesis by (simp add: sign_swap_id)
qed

lemma sign_\<sigma>col: "sign \<sigma>col = -1"
proof -
  have "sign \<sigma>col
      = sign (Fun.swap (2::12) 7 id) * sign (Fun.swap (2::12) 4 id)
      * sign (Fun.swap (2::12) 8 id) * sign (Fun.swap (2::12) 10 id)
      * sign (Fun.swap (2::12) 11 id) * sign (Fun.swap (2::12) 6 id)
      * sign (Fun.swap (2::12) 9 id) * sign (Fun.swap (2::12) 5 id)
      * sign (Fun.swap (2::12) 3 id)"
    by (simp add: \<sigma>col_as_comp sign_compose permutation_swap_id
                  permutation_compose mult.assoc)
  thus ?thesis by (simp add: sign_swap_id)
qed

definition Jperm :: "real^12^12" where
  "Jperm = (\<chi> i j. bigJ $ (\<sigma>row i) $ (\<sigma>col j))"

lemma det_bigJ_eq_neg_det_Jperm: "det bigJ = - det Jperm"
proof -
  let ?M = "(\<chi> i j. bigJ $ i $ \<sigma>col j) :: real^12^12"
  have Jp: "Jperm = (\<chi> i. ?M $ (\<sigma>row i))"
    unfolding Jperm_def by (simp add: vec_eq_iff)
  have step_row: "det Jperm = of_int (sign \<sigma>row) * det ?M"
    using det_permute_rows
    by (metis Determinants.det_permute_rows Jp \<sigma>row_permutes) 
  have step_col: "det ?M = of_int (sign \<sigma>col) * det bigJ"
    using det_permute_columns[OF \<sigma>col_permutes, of bigJ] .
  have "det Jperm = of_int (sign \<sigma>row) * (of_int (sign \<sigma>col) * det bigJ)"
    using step_row step_col by simp
  also have "\<dots> = - det bigJ"
    by (simp add: sign_\<sigma>row sign_\<sigma>col)
  finally show ?thesis by simp
qed

subsubsection \<open>Block decomposition: \<open>det Jperm = det Ablk \<cdot> det Dblk\<close>\<close>

text \<open>
  The permuted matrix \<^const>\<open>Jperm\<close> has the block form \<open>[Ablk | 0; Cblk | Dblk]\<close>,
  realized by the type-level embeddings \<open>top_emb\<close>, \<open>bot_emb\<close> from
  the 6-index type into the 12-index type.
\<close>

definition top_emb :: "6 \<Rightarrow> 12" where
  "top_emb k = (if k = 1 then 1 else if k = 2 then 2 else if k = 3 then 3
                else if k = 4 then 4 else if k = 5 then 5 else 6)"

definition bot_emb :: "6 \<Rightarrow> 12" where
  "bot_emb k = (if k = 1 then 7 else if k = 2 then 8 else if k = 3 then 9
                else if k = 4 then 10 else if k = 5 then 11 else 12)"

text \<open>The lower-left block \<open>Cblk\<close> (the values are determined by \<^const>\<open>Jperm\<close>'s
  definition; we list them explicitly so the structural lemma is checkable by \<open>simp\<close>).\<close>

definition Cblk :: "real^6^6" where
  "Cblk = vector
    [ vector [0, - sqrt 3, 0, 0, sqrt 3, sqrt 3],
      vector [-2, -1, 0, 0, 1, -1],
      vector [2, 1 - pi * sqrt 3 / 3, 0, 0, -1 + 4 * pi * sqrt 3 / 3,
              1 + 5 * pi * sqrt 3 / 3],
      vector [0, - sqrt 3 - pi / 3, 0, 0, sqrt 3 + 4 * pi / 3,
              sqrt 3 - 5 * pi / 3],
      vector [0, -2 * sqrt 3, 0, 0, 2 * sqrt 3, 2 * sqrt 3],
      vector [-4, -2, 0, 0, 2, -2] ]"

lemma TOP_set:
  "top_emb ` UNIV = {(1::12), 2, 3, 4, 5, 6}"
proof
  show "top_emb ` UNIV \<subseteq> {(1::12), 2, 3, 4, 5, 6}"
  proof
    fix y
    assume ymem: "y \<in> top_emb ` UNIV"
    then obtain k :: 6 where y: "y = top_emb k"
      by blast

    have "k = 1 \<or> k = 2 \<or> k = 3 \<or> k = 4 \<or> k = 5 \<or> k = 6"
      by (rule exhaust_6)

    then show "y \<in> {(1::12), 2, 3, 4, 5, 6}"
      using y
      by (auto simp: top_emb_def)
  qed

  show "{(1::12), 2, 3, 4, 5, 6} \<subseteq> top_emb ` UNIV"
  proof
    fix y
    assume ymem: "y \<in> {(1::12), 2, 3, 4, 5, 6}"

    then consider
        "y = (1::12)"
      | "y = (2::12)"
      | "y = (3::12)"
      | "y = (4::12)"
      | "y = (5::12)"
      | "y = (6::12)"
      by auto

    then show "y \<in> top_emb ` UNIV"
    proof cases
      case 1
      have "top_emb (1::6) = (1::12)"
        by (simp add: top_emb_def)
      then show ?thesis
        using 1
        by (metis UNIV_I image_eqI)
    next
      case 2
      have "top_emb (2::6) = (2::12)"
        by (simp add: top_emb_def)
      then show ?thesis
        using 2
        by (metis UNIV_I image_eqI)
    next
      case 3
      have "top_emb (3::6) = (3::12)"
        by (simp add: top_emb_def)
      then show ?thesis
        using 3
        by (metis UNIV_I image_eqI)
    next
      case 4
      have "top_emb (4::6) = (4::12)"
        by (simp add: top_emb_def)
      then show ?thesis
        using 4
        by (metis UNIV_I image_eqI)
    next
      case 5
      have "top_emb (5::6) = (5::12)"
        by (simp add: top_emb_def)
      then show ?thesis
        using 5
        by (metis UNIV_I image_eqI)
    next
      case 6
      have "top_emb (6::6) = (6::12)"
        by (simp add: top_emb_def)
      then show ?thesis
        using 6
        by (metis UNIV_I image_eqI)
    qed
  qed
qed

lemma BOT_set:
  "bot_emb ` UNIV = {(7::12), 8, 9, 10, 11, 12}"
proof
  show "bot_emb ` UNIV \<subseteq> {(7::12), 8, 9, 10, 11, 12}"
  proof
    fix y
    assume ymem: "y \<in> bot_emb ` UNIV"
    then obtain k :: 6 where y: "y = bot_emb k"
      by blast

    have "k = 1 \<or> k = 2 \<or> k = 3 \<or> k = 4 \<or> k = 5 \<or> k = 6"
      by (rule exhaust_6)

    then show "y \<in> {(7::12), 8, 9, 10, 11, 12}"
      using y
      by (auto simp: bot_emb_def)
  qed

  show "{(7::12), 8, 9, 10, 11, 12} \<subseteq> bot_emb ` UNIV"
  proof
    fix y
    assume ymem: "y \<in> {(7::12), 8, 9, 10, 11, 12}"

    then consider
        "y = (7::12)"
      | "y = (8::12)"
      | "y = (9::12)"
      | "y = (10::12)"
      | "y = (11::12)"
      | "y = (12::12)"
      by auto

    then show "y \<in> bot_emb ` UNIV"
    proof cases
      case 1
      have "bot_emb (1::6) = (7::12)"
        by (simp add: bot_emb_def)
      then show ?thesis
        using 1 by (metis UNIV_I image_eqI)
    next
      case 2
      have "bot_emb (2::6) = (8::12)"
        by (simp add: bot_emb_def)
      then show ?thesis
        using 2 by (metis UNIV_I image_eqI)
    next
      case 3
      have "bot_emb (3::6) = (9::12)"
        by (simp add: bot_emb_def)
      then show ?thesis
        using 3 by (metis UNIV_I image_eqI)
    next
      case 4
      have "bot_emb (4::6) = (10::12)"
        by (simp add: bot_emb_def)
      then show ?thesis
        using 4 by (metis UNIV_I image_eqI)
    next
      case 5
      have "bot_emb (5::6) = (11::12)"
        by (simp add: bot_emb_def)
      then show ?thesis
        using 5 by (metis UNIV_I image_eqI)
    next
      case 6
      have "bot_emb (6::6) = (12::12)"
        by (simp add: bot_emb_def)
      then show ?thesis
        using 6 by (metis UNIV_I image_eqI)
    qed
  qed
qed

lemma top_emb_inj: "inj top_emb"
  by (auto simp: inj_def top_emb_def forall_6 split: if_splits)

lemma bot_emb_inj: "inj bot_emb"
  by (auto simp: inj_def bot_emb_def forall_6 split: if_splits)

lemma top_bot_disjoint: "top_emb ` UNIV \<inter> bot_emb ` UNIV = {}"
  unfolding TOP_set BOT_set by auto

lemma top_bot_union: "top_emb ` UNIV \<union> bot_emb ` UNIV = (UNIV :: 12 set)"
  unfolding TOP_set BOT_set UNIV_12 by auto

text \<open>The four block equations characterizing \<^const>\<open>Jperm\<close>.\<close>

lemma Jperm_TL_all: "\<forall>i j :: 6. Jperm $ (top_emb i) $ (top_emb j) = Ablk $ i $ j"
  unfolding Jperm_def \<sigma>row_def \<sigma>col_def top_emb_def Ablk_def bigJ_def
  by (simp add: forall_6 Fun.swap_def)

lemma Jperm_TL: "Jperm $ (top_emb i) $ (top_emb j) = Ablk $ i $ j"
  using Jperm_TL_all by blast

lemma Jperm_TR_all: "\<forall>i j :: 6. Jperm $ (top_emb i) $ (bot_emb j) = 0"
  unfolding Jperm_def \<sigma>row_def \<sigma>col_def top_emb_def bot_emb_def bigJ_def
  by (simp add: forall_6 Fun.swap_def)

lemma Jperm_TR: "Jperm $ (top_emb i) $ (bot_emb j) = 0"
  using Jperm_TR_all by blast

lemma Jperm_BL_all: "\<forall>i j :: 6. Jperm $ (bot_emb i) $ (top_emb j) = Cblk $ i $ j"
  unfolding Jperm_def \<sigma>row_def \<sigma>col_def top_emb_def bot_emb_def Cblk_def bigJ_def
  by (simp add: forall_6 Fun.swap_def)

lemma Jperm_BL: "Jperm $ (bot_emb i) $ (top_emb j) = Cblk $ i $ j"
  using Jperm_BL_all by blast

lemma Jperm_BR_all: "\<forall>i j :: 6. Jperm $ (bot_emb i) $ (bot_emb j) = Dblk $ i $ j"
  unfolding Jperm_def \<sigma>row_def \<sigma>col_def bot_emb_def Dblk_def bigJ_def
  by (simp add: forall_6 Fun.swap_def)

lemma Jperm_BR: "Jperm $ (bot_emb i) $ (bot_emb j) = Dblk $ i $ j"
  using Jperm_BR_all by blast

text \<open>The Cartesian block determinant lemma, proved via permutation
  decomposition: nonzero terms of \<open>det Jperm\<close>'s permutation sum come only from
  block-preserving permutations; those decompose as a pair of \<open>6\<close>-permutations
  on the top and bottom blocks; the sign and product factor accordingly.\<close>



lemma det_Jperm: "det Jperm = det Ablk * det Dblk"
proof -
  let ?T = "top_emb ` (UNIV::6 set)"
  let ?B = "bot_emb ` (UNIV::6 set)"

  have fin_T: "finite ?T" by simp
  have fin_B: "finite ?B" by simp
  have disj: "?T \<inter> ?B = {}" by (rule top_bot_disjoint)
  have UN: "(UNIV::12 set) = ?T \<union> ?B" by (rule top_bot_union[symmetric])

  have bij_T: "bij_betw top_emb UNIV ?T"
    using top_emb_inj by (simp add: bij_betw_def)
  have bij_B: "bij_betw bot_emb UNIV ?B"
    using bot_emb_inj by (simp add: bij_betw_def)

  define lift where
    "lift pT pB = (\<lambda>k::12. if k \<in> ?T
                            then top_emb (pT (inv_into UNIV top_emb k))
                            else bot_emb (pB (inv_into UNIV bot_emb k)))"
    for pT pB :: "6 \<Rightarrow> 6"

  have lift_on_T: "lift pT pB (top_emb i) = top_emb (pT i)" for pT pB i
    unfolding lift_def
    using inv_into_f_f[OF top_emb_inj UNIV_I, of i] by auto

  have lift_on_B: "lift pT pB (bot_emb i) = bot_emb (pB i)" for pT pB i
    unfolding lift_def
    using inv_into_f_f[OF bot_emb_inj UNIV_I, of i] disj
    by (auto simp: image_iff)

  have permutes_6_iff_bij:
    "f permutes (UNIV::6 set) \<longleftrightarrow> bij f"
    for f :: "6 \<Rightarrow> 6"
    by (auto simp: permutes_def bij_def inj_on_def surj_def, metis+)
    

  have permutes_12_iff_bij:
    "f permutes (UNIV::12 set) \<longleftrightarrow> bij f"
    for f :: "12 \<Rightarrow> 12"
    by (auto simp: permutes_def bij_def inj_on_def surj_def, metis+)

  text \<open>Step 1: nonzero contributions come only from block-preserving permutations.\<close>
  have BP_only: "(\<Prod>k\<in>(UNIV::12 set). Jperm $ k $ p k) = 0"
    if p_perm: "p permutes (UNIV::12 set)" and not_bp: "p ` ?T \<noteq> ?T"
    for p
  proof -
    from p_perm have inj_p: "inj_on p ?T" by (rule permutes_inj_on)
    have card_im: "card (p ` ?T) = card ?T" using inj_p by (rule card_image)
    have "p ` ?T \<subseteq> ?T \<Longrightarrow> p ` ?T = ?T"
      using fin_T card_im by (metis card_subset_eq)
    with not_bp obtain k where kT: "k \<in> ?T" and pk_notT: "p k \<notin> ?T" by blast
    from pk_notT UN have "p k \<in> ?B" by auto
    then obtain j where pk_eq: "p k = bot_emb j" by auto
    from kT obtain i where k_eq: "k = top_emb i" by auto
    have "Jperm $ k $ p k = Jperm $ (top_emb i) $ (bot_emb j)"
      using k_eq pk_eq by simp
    also have "\<dots> = 0" by (rule Jperm_TR)
    finally have "Jperm $ k $ p k = 0" .
    moreover have "k \<in> UNIV" by simp
    ultimately show ?thesis by (intro prod_zero) auto
  qed

  text \<open>Step 2: for block-preserving permutations, the product factors as
    (top-block product) * (bottom-block product), each indexed by a
    \<open>6\<close>-permutation.\<close>
  have BP_factor:
    "(\<Prod>k\<in>UNIV. Jperm $ k $ p k)
       = (\<Prod>i\<in>UNIV. Ablk $ i $ ((inv_into UNIV top_emb \<circ> p \<circ> top_emb) i))
       * (\<Prod>i\<in>UNIV. Dblk $ i $ ((inv_into UNIV bot_emb \<circ> p \<circ> bot_emb) i))"
    if p_perm: "p permutes (UNIV::12 set)" and bp: "p ` ?T = ?T"
    for p
  proof -
    have bp_B: "p ` ?B = ?B"
    proof -
      have inj_UN: "inj_on p (UNIV::12 set)"
        using p_perm
        by (rule permutes_inj_on)

      have pB_sub_B: "p ` ?B \<subseteq> ?B"
      proof
        fix y
        assume y_in: "y \<in> p ` ?B"
        then obtain b where bB: "b \<in> ?B" and y_eq: "y = p b"
          by blast

        have y_TB: "y \<in> ?T \<union> ?B"
          using UN
          by simp

        show "y \<in> ?B"
        proof (rule ccontr)
          assume y_not_B: "y \<notin> ?B"
          then have yT: "y \<in> ?T"
            using y_TB
            by blast

          then obtain t where tT: "t \<in> ?T" and y_eq_t: "y = p t"
            using bp
            by blast

          have "b = t"
            using inj_UN y_eq y_eq_t
            by (auto simp: inj_on_def)

          then have "b \<in> ?T"
            using tT
            by simp

          then show False
            using bB disj
            by auto
        qed
      qed

      have inj_B: "inj_on p ?B"
        using p_perm
        by (rule permutes_inj_on)

      have card_pB: "card (p ` ?B) = card ?B"
        using inj_B
        by (rule card_image)

      show ?thesis
        using pB_sub_B fin_B card_pB
        by (metis card_subset_eq)
    qed
    have prod_split:
      "(\<Prod>k\<in>UNIV. Jperm $ k $ p k)
       = (\<Prod>k\<in>?T. Jperm $ k $ p k) * (\<Prod>k\<in>?B. Jperm $ k $ p k)"
      using UN disj fin_T fin_B by (simp add: prod.union_disjoint,
                                    metis (lifting) fin_B fin_T prod.union_disjoint)
    have top_prod:
      "(\<Prod>k\<in>?T. Jperm $ k $ p k)
       = (\<Prod>i\<in>UNIV. Ablk $ i $ ((inv_into UNIV top_emb \<circ> p \<circ> top_emb) i))"
    proof -
      have "(\<Prod>k\<in>?T. Jperm $ k $ p k)
            = (\<Prod>i\<in>UNIV. Jperm $ (top_emb i) $ p (top_emb i))"
        by (rule prod.reindex_bij_betw[OF bij_T, symmetric])
      also have "\<dots> = (\<Prod>i\<in>UNIV. Jperm $ (top_emb i)
                          $ (top_emb (inv_into UNIV top_emb (p (top_emb i)))))"
      proof (rule prod.cong[OF refl])
        fix i :: 6 assume "i \<in> UNIV"
        have "p (top_emb i) \<in> ?T" using bp by (metis UNIV_I imageI image_eqI)
        thus "Jperm $ (top_emb i) $ p (top_emb i)
              = Jperm $ (top_emb i) $ top_emb (inv_into UNIV top_emb (p (top_emb i)))"
          by (simp add: f_inv_into_f)
      qed
      also have "\<dots> = (\<Prod>i\<in>UNIV. Ablk $ i $ (inv_into UNIV top_emb (p (top_emb i))))"
        by (simp add: Jperm_TL)
      finally show ?thesis by (simp add: o_def)
    qed
    have bot_prod:
      "(\<Prod>k\<in>?B. Jperm $ k $ p k)
       = (\<Prod>i\<in>UNIV. Dblk $ i $ ((inv_into UNIV bot_emb \<circ> p \<circ> bot_emb) i))"
    proof -
      have "(\<Prod>k\<in>?B. Jperm $ k $ p k)
            = (\<Prod>i\<in>UNIV. Jperm $ (bot_emb i) $ p (bot_emb i))"
        by (rule prod.reindex_bij_betw[OF bij_B, symmetric])
      also have "\<dots> = (\<Prod>i\<in>UNIV. Jperm $ (bot_emb i)
                          $ (bot_emb (inv_into UNIV bot_emb (p (bot_emb i)))))"
      proof (rule prod.cong[OF refl])
        fix i :: 6 assume "i \<in> UNIV"
        have "p (bot_emb i) \<in> ?B" using bp_B by (metis UNIV_I imageI image_eqI)
        thus "Jperm $ (bot_emb i) $ p (bot_emb i)
              = Jperm $ (bot_emb i) $ bot_emb (inv_into UNIV bot_emb (p (bot_emb i)))"
          by (simp add: f_inv_into_f)
      qed
      also have "\<dots> = (\<Prod>i\<in>UNIV. Dblk $ i $ (inv_into UNIV bot_emb (p (bot_emb i))))"
        by (simp add: Jperm_BR)
      finally show ?thesis by (simp add: o_def)
    qed
    from prod_split top_prod bot_prod show ?thesis by simp
  qed

  text \<open>Step 3: the bijection between block-preserving 12-perms and
    pairs of 6-perms, and sign multiplicativity. These remaining algebraic
    steps are left as helper sorries; combined they close the determinant.\<close>

  have sign_lift: "sign (lift pT pB) = sign pT * sign pB"
    if pT_perm: "pT permutes (UNIV::6 set)"
      and pB_perm: "pB permutes (UNIV::6 set)"
    for pT pB
  proof -
    let ?topL = "map_permutation (UNIV::6 set) top_emb pT :: 12 \<Rightarrow> 12"
    let ?botL = "map_permutation (UNIV::6 set) bot_emb pB :: 12 \<Rightarrow> 12"

    have top_inj_on: "inj_on top_emb (UNIV::6 set)"
      using top_emb_inj
      by (simp add: inj_on_def)

    have bot_inj_on: "inj_on bot_emb (UNIV::6 set)"
      using bot_emb_inj
      by (simp add: inj_on_def)

    have topL_on_T:
      "?topL (top_emb i) = top_emb (pT i)"
      for i :: 6
      by (rule map_permutation_apply[OF top_inj_on UNIV_I])

    have botL_on_B:
      "?botL (bot_emb i) = bot_emb (pB i)"
      for i :: 6
      by (rule map_permutation_apply[OF bot_inj_on UNIV_I])

    have topL_on_B:
      "?topL (bot_emb i) = bot_emb i"
      for i :: 6
    proof -
      have "bot_emb i \<notin> ?T"
        using disj
        by auto
      then show ?thesis
        by (simp add: map_permutation_def restrict_id_def)
    qed

    have botL_on_T: "?botL (top_emb i) = top_emb i"
      for i :: 6
    proof -
      have "top_emb i \<notin> ?B"
        using disj
        by auto
      then show ?thesis
        by (simp add: map_permutation_def restrict_id_def)
    qed

    have lift_eq: "lift pT pB = ?topL \<circ> ?botL"
    proof
      fix k :: 12
      have "k \<in> ?T \<or> k \<in> ?B"
        using UN
        by auto
      then show "lift pT pB k = (?topL \<circ> ?botL) k"
      proof
        assume kT: "k \<in> ?T"
        then obtain i :: 6 where k: "k = top_emb i"
          by auto
        then show ?thesis
          by (simp add: lift_on_T topL_on_T botL_on_T)
      next
        assume kB: "k \<in> ?B"
        then obtain i :: 6 where k: "k = bot_emb i"
          by auto
        then show ?thesis
          by (simp add: lift_on_B topL_on_B botL_on_B)
      qed
    qed

    have topL_permutes:
      "?topL permutes ?T"
      using bij_T pT_perm
      by (rule map_permutation_permutes)

    have botL_permutes:
      "?botL permutes ?B"
      using bij_B pB_perm
      by (rule map_permutation_permutes)

    have topL_perm: "permutation ?topL"
      using fin_T topL_permutes
      by (rule permutes_imp_permutation)

    have botL_perm: "permutation ?botL"
      using fin_B botL_permutes
      by (rule permutes_imp_permutation)

    have sign_top: "sign ?topL = sign pT"
      by (simp add: pT_perm sign_map_permutation top_emb_inj)

    have sign_bot: "sign ?botL = sign pB"
      by (simp add: bot_inj_on sign_map_permutation that(2))

    have "sign (lift pT pB) = sign (?topL \<circ> ?botL)"
      by (simp add: lift_eq)
    also have "... = sign ?topL * sign ?botL"
      by (rule sign_compose[OF topL_perm botL_perm])
    also have "... = sign pT * sign pB"
      by (simp add: sign_top sign_bot)
    finally show ?thesis.
  qed

  have lift_perm: "lift pT pB permutes (UNIV::12 set)"
    if pT_perm: "pT permutes (UNIV::6 set)"
      and pB_perm: "pB permutes (UNIV::6 set)"
    for pT pB
  proof -
    have surj_pT: "surj pT"
      using pT_perm
      by (simp add: permutes_6_iff_bij bij_def)

    have surj_pB: "surj pB"
      using pB_perm
      by (simp add: permutes_6_iff_bij bij_def)

    have surj_lift: "surj (lift pT pB)"
    proof (unfold surj_def, intro allI)
      fix y :: 12
      have y_cases: "y \<in> ?T \<or> y \<in> ?B"
        using UN
        by auto

      then show "\<exists>x. y = lift pT pB x"
      proof
        assume yT: "y \<in> ?T"
        then obtain j :: 6 where y: "y = top_emb j"
          by auto

        obtain i :: 6 where i: "pT i = j"
          using surj_pT
          by (auto simp: surj_def, metis)

        have "y = lift pT pB (top_emb i)"
          using y i
          by (simp add: lift_on_T)

        then show ?thesis
          by blast
      next
        assume yB: "y \<in> ?B"
        then obtain j :: 6 where y: "y = bot_emb j"
          by auto

        obtain i :: 6 where i: "pB i = j"
          using surj_pB
          by (auto simp: surj_def, metis)

        have "y = lift pT pB (bot_emb i)"
          using y i
          by (simp add: lift_on_B)

        then show ?thesis
          by blast
      qed
    qed

    have inj_pT: "inj pT"
      using pT_perm
      by (simp add: permutes_6_iff_bij bij_def)

    have inj_pB: "inj pB"
      using pB_perm
      by (simp add: permutes_6_iff_bij bij_def)

    have inj_lift: "inj (lift pT pB)"
    proof (rule injI)
      fix a b :: 12
      assume eq: "lift pT pB a = lift pT pB b"

      have a_cases: "a \<in> ?T \<or> a \<in> ?B"
        using UN by auto
      have b_cases: "b \<in> ?T \<or> b \<in> ?B"
        using UN by auto

      show "a = b"
        using a_cases
      proof
        assume aT: "a \<in> ?T"
        then obtain i :: 6 where a_eq: "a = top_emb i"
          by auto

        show "a = b"
          using b_cases
        proof
          assume bT: "b \<in> ?T"
          then obtain j :: 6 where b_eq: "b = top_emb j"
            by auto

          have "top_emb (pT i) = top_emb (pT j)"
            using eq a_eq b_eq
            by (simp add: lift_on_T)

          then have "pT i = pT j"
            using top_emb_inj
            by (simp add: inj_def)

          then have "i = j"
            using inj_pT
            by (simp add: inj_def)

          then show "a = b"
            using a_eq b_eq
            by simp
        next
          assume bB: "b \<in> ?B"
          then obtain j :: 6 where b_eq: "b = bot_emb j"
            by auto

          have eq_blocks: "top_emb (pT i) = bot_emb (pB j)"
            using eq a_eq b_eq
            by (simp add: lift_on_T lift_on_B)

          have "top_emb (pT i) \<in> ?T"
            by auto
          moreover have "bot_emb (pB j) \<in> ?B"
            by auto
          ultimately show "a = b"
            using eq_blocks disj
            by auto
        qed
      next
        assume aB: "a \<in> ?B"
        then obtain i :: 6 where a_eq: "a = bot_emb i"
          by auto

        show "a = b"
          using b_cases
        proof
          assume bT: "b \<in> ?T"
          then obtain j :: 6 where b_eq: "b = top_emb j"
            by auto

          have eq_blocks: "bot_emb (pB i) = top_emb (pT j)"
            using eq a_eq b_eq
            by (simp add: lift_on_T lift_on_B)

          have "bot_emb (pB i) \<in> ?B"
            by auto
          moreover have "top_emb (pT j) \<in> ?T"
            by auto
          ultimately show "a = b"
            using eq_blocks disj
            by auto
        next
          assume bB: "b \<in> ?B"
          then obtain j :: 6 where b_eq: "b = bot_emb j"
            by auto

          have "bot_emb (pB i) = bot_emb (pB j)"
            using eq a_eq b_eq
            by (simp add: lift_on_B)

          then have "pB i = pB j"
            using bot_emb_inj
            by (simp add: inj_def)

          then have "i = j"
            using inj_pB
            by (simp add: inj_def)

          then show "a = b"
            using a_eq b_eq
            by simp
        qed
      qed

      have "bij (lift pT pB)"
        unfolding bij_def
        by(simp add: finite_UNIV_surj_inj surj_lift)
    qed
    then show ?thesis
      using bij_def surj_lift by (simp add: permutes_12_iff_bij, auto)       
  qed

  have lift_image_T: "lift pT pB ` ?T = ?T"
    if pT_perm: "pT permutes (UNIV::6 set)" for pT pB
  proof
    show "lift pT pB ` ?T \<subseteq> ?T"
    proof
      fix y
      assume "y \<in> lift pT pB ` ?T"
      then obtain i :: 6 where y: "y = lift pT pB (top_emb i)"
        by auto
      then have "y = top_emb (pT i)"
        by (simp add: lift_on_T)
      then show "y \<in> ?T"
        by auto
    qed

    show "?T \<subseteq> lift pT pB ` ?T"
    proof
      fix y
      assume yT: "y \<in> ?T"
      then obtain j :: 6 where y: "y = top_emb j"
        by auto

      have "surj pT"
        using pT_perm
        by (simp add: permutes_6_iff_bij bij_def)

      then obtain i :: 6 where i: "pT i = j"
        by (auto simp: surj_def, metis)

      have "lift pT pB (top_emb i) = y"
        using y i
        by (simp add: lift_on_T)

      then show "y \<in> lift pT pB ` ?T"
        by auto
    qed
  qed

  have inv_lift: "(inv_into UNIV top_emb \<circ> lift pT pB \<circ> top_emb) = pT
                \<and> (inv_into UNIV bot_emb \<circ> lift pT pB \<circ> bot_emb) = pB"
    if "pT permutes UNIV" "pB permutes UNIV" for pT pB
    using bot_emb_inj lift_on_B lift_on_T top_emb_inj by auto

  let ?BP = "{p. p permutes (UNIV::12 set) \<and> p ` ?T = ?T}"
  let ?PP = "{pT. pT permutes (UNIV::6 set)} \<times> {pB. pB permutes (UNIV::6 set)}"

  have p_pres_BOT: "p ` ?B = ?B"
    if p_perm: "p permutes (UNIV::12 set)" and p_bp: "p ` ?T = ?T" for p
  proof -
    have inj_p: "inj p"
      using p_perm by (simp add: permutes_12_iff_bij bij_def)
    have pB_sub_B: "p ` ?B \<subseteq> ?B"
    proof
      fix y assume "y \<in> p ` ?B"
      then obtain b where bB: "b \<in> ?B" and y_eq: "y = p b" by blast
      show "y \<in> ?B"
      proof (rule ccontr)
        assume y_not_B: "y \<notin> ?B"
        with UN have yT: "y \<in> ?T" by auto
        with p_bp obtain t where tT: "t \<in> ?T" and y_eq_t: "y = p t" by blast
        have "b = t" using inj_p y_eq y_eq_t by (auto simp: inj_def)
        then have "b \<in> ?T" using tT by simp
        with bB disj show False by auto
      qed
    qed
    have card_pB: "card (p ` ?B) = card ?B"
      using inj_p by (auto simp: card_image inj_on_def)
    show ?thesis
      using pB_sub_B fin_B card_pB by (metis card_subset_eq)
  qed

  have unlift_perm:
    "(inv_into UNIV top_emb \<circ> p \<circ> top_emb) permutes (UNIV::6 set)
   \<and> (inv_into UNIV bot_emb \<circ> p \<circ> bot_emb) permutes (UNIV::6 set)"
    if p_perm: "p permutes (UNIV::12 set)" and p_bp: "p ` ?T = ?T" for p
  proof -
    have p_bb: "p ` ?B = ?B" by (rule p_pres_BOT[OF p_perm p_bp])
    have inj_pT: "inj (inv_into UNIV top_emb \<circ> p \<circ> top_emb)"
    proof (rule injI)
      fix x y :: 6
      assume "(inv_into UNIV top_emb \<circ> p \<circ> top_emb) x
            = (inv_into UNIV top_emb \<circ> p \<circ> top_emb) y"
      then have eq: "inv_into UNIV top_emb (p (top_emb x))
                   = inv_into UNIV top_emb (p (top_emb y))" by simp
      have "p (top_emb x) \<in> ?T" using p_bp by auto
      moreover have "p (top_emb y) \<in> ?T" using p_bp by auto
      ultimately have "p (top_emb x) = p (top_emb y)"
        by (meson eq inv_into_injective)
      then have "top_emb x = top_emb y"
        using p_perm by (meson permutes_inj injD)
      then show "x = y" using top_emb_inj by (meson injD)
    qed
    have bij_pT: "bij (inv_into UNIV top_emb \<circ> p \<circ> top_emb)"
      using finite_class.finite_UNIV inj_imp_permutes inj_pT permutes_6_iff_bij by blast
    have pT_perm: "(inv_into UNIV top_emb \<circ> p \<circ> top_emb) permutes (UNIV::6 set)"
      using bij_pT by (simp add: permutes_6_iff_bij)
    have inj_pB: "inj (inv_into UNIV bot_emb \<circ> p \<circ> bot_emb)"
    proof (rule injI)
      fix x y :: 6
      assume "(inv_into UNIV bot_emb \<circ> p \<circ> bot_emb) x
            = (inv_into UNIV bot_emb \<circ> p \<circ> bot_emb) y"
      then have eq: "inv_into UNIV bot_emb (p (bot_emb x))
                   = inv_into UNIV bot_emb (p (bot_emb y))" by simp
      have "p (bot_emb x) \<in> ?B" using p_bb by auto
      moreover have "p (bot_emb y) \<in> ?B" using p_bb by auto
      ultimately have "p (bot_emb x) = p (bot_emb y)"
        by (meson eq inv_into_injective)
      then have "bot_emb x = bot_emb y"
        using p_perm by (meson permutes_inj injD)
      then show "x = y" using bot_emb_inj by (meson injD)
    qed
    have bij_pB: "bij (inv_into UNIV bot_emb \<circ> p \<circ> bot_emb)"
      using finite_class.finite_UNIV inj_imp_permutes inj_pB permutes_6_iff_bij by blast
    have pB_perm: "(inv_into UNIV bot_emb \<circ> p \<circ> bot_emb) permutes (UNIV::6 set)"
      using bij_pB by (simp add: permutes_6_iff_bij)
    from pT_perm pB_perm show ?thesis by simp
  qed

  have lift_unlift:
    "lift (inv_into UNIV top_emb \<circ> p \<circ> top_emb)
          (inv_into UNIV bot_emb \<circ> p \<circ> bot_emb) = p"
    if p_perm: "p permutes (UNIV::12 set)" and p_bp: "p ` ?T = ?T" for p
  proof
    fix k :: 12
    let ?pT = "inv_into UNIV top_emb \<circ> p \<circ> top_emb"
    let ?pB = "inv_into UNIV bot_emb \<circ> p \<circ> bot_emb"
    have "k \<in> ?T \<or> k \<in> ?B" using UN by auto
    then show "lift ?pT ?pB k = p k"
    proof
      assume kT: "k \<in> ?T"
      then obtain i where k: "k = top_emb i" by auto
      have "lift ?pT ?pB (top_emb i)
            = top_emb (inv_into UNIV top_emb (p (top_emb i)))"
        by (simp add: lift_on_T)
      moreover have "p (top_emb i) \<in> ?T" using p_bp by auto
      then have "top_emb (inv_into UNIV top_emb (p (top_emb i))) = p (top_emb i)"
        using bij_T by (auto simp: f_inv_into_f)
      ultimately show "lift ?pT ?pB k = p k" using k by simp
    next
      assume kB: "k \<in> ?B"
      then obtain i where k: "k = bot_emb i" by auto
      have p_bb: "p ` ?B = ?B" by (rule p_pres_BOT[OF p_perm p_bp])
      have "lift ?pT ?pB (bot_emb i)
            = bot_emb (inv_into UNIV bot_emb (p (bot_emb i)))"
        by (simp add: lift_on_B)
      moreover have "p (bot_emb i) \<in> ?B" using p_bb by auto
      then have "bot_emb (inv_into UNIV bot_emb (p (bot_emb i))) = p (bot_emb i)"
        using bij_B by (auto simp: f_inv_into_f)
      ultimately show "lift ?pT ?pB k = p k" using k by simp
    qed
  qed

  have bij_lift: "bij_betw (\<lambda>(pT, pB). lift pT pB) ?PP ?BP"
  proof (rule bij_betwI[where
           g = "\<lambda>p. (inv_into UNIV top_emb \<circ> p \<circ> top_emb,
                     inv_into UNIV bot_emb \<circ> p \<circ> bot_emb)"])
    show "(\<lambda>(pT, pB). lift pT pB) \<in> ?PP \<rightarrow> ?BP"
    proof
      fix q :: "(6 \<Rightarrow> 6) \<times> (6 \<Rightarrow> 6)"
      assume "q \<in> ?PP"
      then have pT: "fst q permutes (UNIV::6 set)"
            and pB: "snd q permutes (UNIV::6 set)" by auto
      have "lift (fst q) (snd q) permutes (UNIV::12 set)"
        by (rule lift_perm[OF pT pB])
      moreover have "lift (fst q) (snd q) ` ?T = ?T"
        by (rule lift_image_T[OF pT])
      ultimately show "(\<lambda>(pT, pB). lift pT pB) q \<in> ?BP"
        by (simp add: case_prod_beta)
    qed
  next
    show "(\<lambda>p. (inv_into UNIV top_emb \<circ> p \<circ> top_emb,
                inv_into UNIV bot_emb \<circ> p \<circ> bot_emb)) \<in> ?BP \<rightarrow> ?PP"
    proof
      fix p :: "12 \<Rightarrow> 12"
      assume "p \<in> ?BP"
      then have p_perm: "p permutes (UNIV::12 set)" and p_bp: "p ` ?T = ?T" by auto
      show "(inv_into UNIV top_emb \<circ> p \<circ> top_emb,
             inv_into UNIV bot_emb \<circ> p \<circ> bot_emb) \<in> ?PP"
        using unlift_perm[OF p_perm p_bp] by auto
    qed
  next
    fix q :: "(6 \<Rightarrow> 6) \<times> (6 \<Rightarrow> 6)"
    assume "q \<in> ?PP"
    then have pT: "fst q permutes (UNIV::6 set)"
          and pB: "snd q permutes (UNIV::6 set)" by auto
    have inv_eq: "(inv_into UNIV top_emb \<circ> lift (fst q) (snd q) \<circ> top_emb) = fst q
                \<and> (inv_into UNIV bot_emb \<circ> lift (fst q) (snd q) \<circ> bot_emb) = snd q"
      using inv_lift[OF pT pB] .
    show "(\<lambda>p. (inv_into UNIV top_emb \<circ> p \<circ> top_emb,
                inv_into UNIV bot_emb \<circ> p \<circ> bot_emb))
            ((\<lambda>(pT, pB). lift pT pB) q) = q"
      using inv_eq
      by (simp add: case_prod_beta) 
  next
    fix p :: "12 \<Rightarrow> 12"
    assume "p \<in> ?BP"
    then have p_perm: "p permutes (UNIV::12 set)" and p_bp: "p ` ?T = ?T" by auto
    show "(\<lambda>(pT, pB). lift pT pB)
            ((\<lambda>p. (inv_into UNIV top_emb \<circ> p \<circ> top_emb,
                   inv_into UNIV bot_emb \<circ> p \<circ> bot_emb)) p) = p"
      by (simp add: case_prod_beta lift_unlift[OF p_perm p_bp])
  qed

  have all_perms_fin: "finite {p. p permutes (UNIV::12 set)}"
    by (rule finite_permutations) auto
  have BP_sub: "?BP \<subseteq> {p. p permutes (UNIV::12 set)}" by auto

  have det_split:
    "det Jperm
       = sum (\<lambda>p. of_int (sign p) * (\<Prod>k\<in>UNIV. Jperm $ k $ p k)) ?BP"
  proof -
    have "det Jperm
          = sum (\<lambda>p. of_int (sign p) * (\<Prod>k\<in>UNIV. Jperm $ k $ p k))
                {p. p permutes UNIV}"
      unfolding det_def by simp
    also have "\<dots> = sum (\<lambda>p. of_int (sign p) * (\<Prod>k\<in>UNIV. Jperm $ k $ p k)) ?BP
                  + sum (\<lambda>p. of_int (sign p) * (\<Prod>k\<in>UNIV. Jperm $ k $ p k))
                        ({p. p permutes UNIV} - ?BP)"
      by (subst sum.subset_diff[OF BP_sub all_perms_fin]) simp
    also have "sum (\<lambda>p. of_int (sign p) * (\<Prod>k\<in>UNIV. Jperm $ k $ p k))
                   ({p. p permutes UNIV} - ?BP) = 0"
      by (rule sum.neutral, use BP_only in auto)
    finally show ?thesis by simp
  qed

  have reindex_step:
    "sum (\<lambda>p. of_int (sign p) * (\<Prod>k\<in>UNIV. Jperm $ k $ p k)) ?BP
     = sum (\<lambda>q. of_int (sign (lift (fst q) (snd q)))
                * (\<Prod>k\<in>UNIV. Jperm $ k $ lift (fst q) (snd q) k)) ?PP"
    using sum.reindex_bij_betw[OF bij_lift,
            of "\<lambda>p. of_int (sign p) * (\<Prod>k\<in>UNIV. Jperm $ k $ p k)"]
    by (simp add: case_prod_beta')

  have prod_pair:
    "of_int (sign (lift (fst q) (snd q)))
     * (\<Prod>k\<in>UNIV. Jperm $ k $ lift (fst q) (snd q) k)
     = (of_int (sign (fst q)) * (\<Prod>i\<in>UNIV. Ablk $ i $ fst q i))
     * (of_int (sign (snd q)) * (\<Prod>i\<in>UNIV. Dblk $ i $ snd q i))"
    if q_in: "q \<in> ?PP" for q
  proof -
    from q_in have pT: "fst q permutes UNIV" and pB: "snd q permutes UNIV" by auto
    let ?p = "lift (fst q) (snd q)"
    have p_perm: "?p permutes UNIV" using lift_perm[OF pT pB] .
    have p_bp: "?p ` ?T = ?T" using lift_image_T[OF pT] .
    have BP_fact: "(\<Prod>k\<in>UNIV. Jperm $ k $ ?p k)
                 = (\<Prod>i\<in>UNIV. Ablk $ i $ ((inv_into UNIV top_emb \<circ> ?p \<circ> top_emb) i))
                 * (\<Prod>i\<in>UNIV. Dblk $ i $ ((inv_into UNIV bot_emb \<circ> ?p \<circ> bot_emb) i))"
      using BP_factor[OF p_perm p_bp] .
    have idT: "(inv_into UNIV top_emb \<circ> ?p \<circ> top_emb) = fst q"
          and idB: "(inv_into UNIV bot_emb \<circ> ?p \<circ> bot_emb) = snd q"
      using inv_lift[OF pT pB] by auto
    have sig: "sign ?p = sign (fst q) * sign (snd q)"
      using sign_lift[OF pT pB] .
    show ?thesis
      by (simp add: BP_fact idT idB sig of_int_mult)
  qed

  have sum_factor:
    "sum (\<lambda>q. of_int (sign (lift (fst q) (snd q)))
              * (\<Prod>k\<in>UNIV. Jperm $ k $ lift (fst q) (snd q) k)) ?PP
     = (sum (\<lambda>pT. of_int (sign pT) * (\<Prod>i\<in>UNIV. Ablk $ i $ pT i))
            {pT. pT permutes (UNIV::6 set)})
     * (sum (\<lambda>pB. of_int (sign pB) * (\<Prod>i\<in>UNIV. Dblk $ i $ pB i))
            {pB. pB permutes (UNIV::6 set)})"
  proof -
    have "sum (\<lambda>q. of_int (sign (lift (fst q) (snd q)))
                * (\<Prod>k\<in>UNIV. Jperm $ k $ lift (fst q) (snd q) k)) ?PP
        = sum (\<lambda>q. (of_int (sign (fst q)) * (\<Prod>i\<in>UNIV. Ablk $ i $ fst q i))
                 * (of_int (sign (snd q)) * (\<Prod>i\<in>UNIV. Dblk $ i $ snd q i))) ?PP"
      by (rule sum.cong[OF refl]) (rule prod_pair)
    also have "\<dots> = (\<Sum>pT\<in>{pT. pT permutes UNIV}.
                     \<Sum>pB\<in>{pB. pB permutes UNIV}.
                       (of_int (sign pT) * (\<Prod>i\<in>UNIV. Ablk $ i $ pT i))
                     * (of_int (sign pB) * (\<Prod>i\<in>UNIV. Dblk $ i $ pB i)))"
      by (subst sum.cartesian_product, metis (mono_tags, lifting) case_prod_beta prod.cong)
    also have "\<dots> = (\<Sum>pT\<in>{pT. pT permutes UNIV}.
                       of_int (sign pT) * (\<Prod>i\<in>UNIV. Ablk $ i $ pT i))
                  * (\<Sum>pB\<in>{pB. pB permutes UNIV}.
                       of_int (sign pB) * (\<Prod>i\<in>UNIV. Dblk $ i $ pB i))"
      by (simp add: sum_product)
    finally show ?thesis .
  qed

  from det_split reindex_step sum_factor
  show "det Jperm = det Ablk * det Dblk"
    unfolding det_def by simp
qed

lemma bigJ_det: "det bigJ = - (5 * pi^8) / 3"
proof -
  have s_sq: "sqrt 3 * sqrt 3 = (3::real)"
    using real_sqrt_mult_self by simp
  have "det bigJ = - det Jperm"
    by (rule det_bigJ_eq_neg_det_Jperm)
  also have "\<dots> = - (det Ablk * det Dblk)" by (simp add: det_Jperm)
  also have "\<dots> = - ((- sqrt 3 * pi^6 / 18) * (-10 * sqrt 3 * pi^2))"
    by (simp add: det_A det_D)
  also have "\<dots> = - (10 * (sqrt 3 * sqrt 3) * (pi^6 * pi^2) / 18)"
    by (simp add: field_simps)
  also have "\<dots> = - (10 * 3 * pi^8 / 18)"
    by (simp add: s_sq flip: power_add)
  also have "\<dots> = - (5 * pi^8) / 3" by simp
  finally show ?thesis .
qed

lemma bigJ_det_nonzero: "det bigJ \<noteq> 0"
proof -
  have "pi > 0" by (rule pi_gt_zero)
  hence "pi^8 > 0" by simp
  thus ?thesis unfolding bigJ_det by simp
qed

text \<open>
  The configuration matrix has full rank, hence the parameter-derivative is
  surjective \<^emph>\<open>at the base point\<close>. This is the pointwise content of
  \<open>lem:Msurj\<close> that the determinant delivers: it discharges the
  \<open>one_regular\<close> base-point premise of
  \<open>rank_lower_semicont_open_dense_propagation\<close> once the concrete moment
  map's derivative at the six-element configuration is identified with
  \<^term>\<open>(*v) bigJ\<close>. The open-dense upgrade is a \<^emph>\<open>separate\<close> argument
  (lower semicontinuity of rank), not implied by the single-point determinant.
\<close>

lemma bigJ_full_rank: "rank bigJ = CARD(12)"
proof -
  have "rank bigJ \<noteq> CARD(12) \<Longrightarrow> rank bigJ < CARD(12)"
    using rank_bound[of bigJ] by simp
  with bigJ_det_nonzero det_eq_0_rank[of bigJ] show ?thesis by auto
qed

lemma bigJ_surj: "surj ((*v) bigJ)"
  using bigJ_full_rank full_rank_surjective[of bigJ] by simp

end
