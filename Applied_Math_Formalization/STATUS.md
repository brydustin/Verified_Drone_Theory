# Formalization Status — Odd-N Nonemptiness Paper

Cross-reference between the paper
`nonemptiness_unified_singlefile_complete.tex` (6285 lines, 102 theorem-like
environments) and the Isabelle/HOL development in this directory.

Companion to [ROADMAP.md](ROADMAP.md) (the plan). This file is the **catalogue +
status** (the map). Line numbers refer to the `.tex`.

## What is being verified

The flagship result is **`thm:final`** (§Closeout): for odd `N ≥ 7` under the
secant/spacing hypotheses (`ω_s ∈ B_ε(ω₀)`, `cos θ_s ≠ cos θ₀`), the robust
feasible set `F_zero = F ∩ X₀(ξ)` is nonempty for some `ξ > 0`.

The proof is a **Baire-category argument**: four "bad" parameter sets are each
*meager*, so their union cannot cover the nonempty open feasible family — hence a
good parameter exists. The four branches:

| Branch | meagerness result | engine |
| --- | --- | --- |
| regular stratum, `A = 0`   | `prop:regzero`    | parametric transversality + Sard |
| fold zeros, `A = 0`        | `prop:foldzero`   | chart-projection meager |
| fold critical, `A ≠ 0`     | `prop:foldnonzero` (+`lem:Efinite`) | real-analytic zero sets |
| regular stratum, `A ≠ 0`   | `prop:regnonzero` | the **entire appendix** (moment-map + H≡0 + Case B) |

## The iceberg

The first nine sections (the **spine**, ~17 results) are mostly formalized. The
appendix (lines **1462–6285**, ~85 results) proves the single branch
`prop:regnonzero` and is **essentially unformalized**.

```
SPINE  (≈17 results, §1–9)        ████████████████░░   mostly done
APPENDIX (≈85 results, L1462+)    ░░░░░░░░░░░░░░░░░░   no Isabelle counterpart
```

Status legend: ✅ proven · ◐ proven modulo a `sorry` stub · ⬚ placeholder
(`shows True`) · ✗ absent (no Isabelle counterpart yet).

## Isabelle name map (the 11 top-level obligations)

The names live in `Nonemptiness_Paper.thy` (working) and `Nonemptiness_Inventory.thy`
(skeleton, all `shows True` stubs). `thm:final`'s real logic is separately **proven**
as `nonemptiness_from_meager_branches` in `Nonemptiness_Spine.thy` — not yet wired.

| Isabelle name | TeX label | Status | Notes |
| --- | --- | --- | --- |
| `prop_openfeas`      | `prop:openfeas`      | ◐ | nulling half proven; openness/spacing half not yet |
| `lem_twotriplecover` | `lem:twotriplecover` | ◐ | combinatorial avoidance core proven; geometric packaging pending |
| `lem_czero`          | `lem:czero`          | ✅ | full (via `secant_sphere`) |
| `lem_Azero_surj`     | `lem:Azero-surj`     | ✅ | full (via `dxA_surj`, Spine) |
| `prop_regzero`       | `prop:regzero`       | ◐ | meagerness reduced to `parametric_transversality_meager_stub` (sorry) |
| `lem_foldfields`     | `lem:foldfields`     | ✅ | full (φ/θ derivatives + `det Jcvec`) |
| `prop_foldzero`      | `prop:foldzero`      | ◐ | finite-union meagerness proven; per-chart `chart_zero_projection_meager_stub` (sorry) |
| `lem_Efinite`        | `lem:Efinite`        | ◐ | **stated truly** (`E` finite); real-analyticity modeled as the real restriction of an entire function; the isolated-zeros step is the remaining `sorry` |
| `prop_foldnonzero`   | `prop:foldnonzero`   | ✅ | **stated + proved** as the finite-union reduction (the TeX proof); nowhere-density of each slice-zero set (the real-analytic input) is a hypothesis |
| `prop_regnonzero`    | `prop:regnonzero`    | ✅ | **stated + proved** as the 4-piece decomposition reduction; the four sub-meagerness facts are hypotheses (the unformalized appendix obligations `prop:dimZ` / `cor:caseBmeager` / `prop:h0res-meager`) |
| `thm_final`          | `thm:final`          | ◐ | **wired (proven, conditional)**: the Baire closeout, conditional on the four branch meagerness facts + feasibility + `X0` soundness, via `nonemptiness_from_meager_branches`. Becomes unconditional once the four branches are proved for the concrete array-factor sets. |

Proven supporting infrastructure (not in the 11): negligible→meager engine
(`meager_nowhere_dense`, `nowhere_dense_closed_negligible`,
`meager_negligible_closed_cover`, `meager_Union_finite`), the Baire glue topology
(`meager_Un`, `meager_Union_nat`, `open_nonempty_not_meager` in `Nonemptiness_Scaffold.thy`),
`Topology_Bridge.thy` (0 sorry), and the array-factor core (`af_zero_odd_not_collinear`,
`af_zero_odd_indep_pair`, `dxA_surj` in `Nonemptiness_Spine.thy`).

The Euclidean transversality pipeline lives in
`Parametric_Transversality_Euclidean_Base.thy`: `countable_chart_cover_of_levelset_2d`
✅ and `negligible_critical_values_from_charts` ✅ are proven; the keystone
`regular_zero_set_projection_local_chart_2d` (regular value ⇒ local smooth chart) and
the Sard/critical-set plumbing remain `sorry`.

Note on the keystone: its `shows` existential is now **type-pinned to `real^'m`**
(chart domain), as is `loc` inside `countable_chart_cover` — without this the
chart-domain type generalizes to a schematic variable and the lemma is unprovable
(invariance of domain). Proving it is the genuine **regular-value theorem**: HOL-Analysis
has no implicit-function / submanifold theorem, so it must be built from
`inverse_function_theorem` (Derivative.thy) by augmenting `G` to a square map
`F z = (π z, G z)` with `π : (real^'m × real^2) →L real^'m` chosen so `(π, DG p)` is
bijective (`π` an iso on `ker (DG p)`, via `subspace_isomorphism` /
`orthogonal_subspace_decomp_exists`), then extracting the chart `φ u = g (u, 0)` from
the local diffeomorphism. This is a substantial multi-step proof, not a type fix.

---

## Full statement catalogue (all 102 environments)

Descriptions are one-line paraphrases of the `.tex` statements. Isabelle column:
status per the legend; "—" means no counterpart and none planned as a named obligation.

### Spine — §Setup … §Closeout (L86–1461)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 203  | `prop:openfeas`      | A nonempty open `U_feas ⊂ ℝ^{2N}` lies in the feasible set `F` (root-of-unity nulling + openness). | ◐ `prop_openfeas` |
| 244  | `lem:twotriplecover` | After a small perturbation, a connected open `V ⊂ U_feas` has two disjoint noncollinear triples covering every direction. | ◐ `lem_twotriplecover` |
| 279  | `lem:czero`          | `c(ω) = 0 ⟹ ω = ω₀ or ω = ω_s` (secant-on-sphere). | ✅ `lem_czero` |
| 290  | `cor:no_czero`       | Under `ω_s ∈ B_ε(ω₀)`, `Ω°` contains no point with `c(ω)=0`. | — (via `lem_czero`) |
| 300  | `lem:Azero-surj`     | Odd `N`: at a zero of `A` with `c≠0`, `D_x A : ℝ^{2N}→ℂ` is surjective. | ✅ `lem_Azero_surj` |
| 323  | `prop:regzero`       | `{x∈V : A_x not transverse to 0 on Ω_reg}` is meager. | ◐ `prop_regzero` |
| 364  | `lem:foldfields`     | Explicit kernel field `K` and tangent field `T` on the fold curve `Σ`; every point of `Σ` is a fold point. | ✅ `lem_foldfields` |
| 395  | `prop:foldzero`      | `{x∈V : A has a zero on the fold curve Σ}` is meager. | ◐ `prop_foldzero` |
| 435  | `lem:Efinite`        | `E = {ω∈Σ : g_θ(ω)=0}` is finite (real-analytic zero set, ≤2 φ-solutions each). | ◐ `lem_Efinite` (stated truly; isolated-zeros `sorry`) |
| 448  | `prop:foldnonzero`   | `{x∈V : nonzero-A critical point of U on Σ}` is meager. | ✅ `prop_foldnonzero` (proved finite-union reduction) |
| 527  | `lem:Hzero`          | Where `H₁₁=H₁₂=H₂₂=0`, `DΦ₃=0`, so `rank DΦ ≤ 2`. | ✗ |
| 547  | `cor:Hyp3false`      | Existence of such a point falsifies the old Hypothesis 3. | ✗ |
| 602  | `lem:block`          | The 5×5 Jacobian `J₅` is block-triangular with `det J₅ = −32 g⁵ a⁵` (dual `±32 g⁵ b⁵`). | ✗ |
| 637  | `lem:3x3`            | Three explicit 3×3 rank-3 minors of `D_M F` equal `−8g³a³H₂₂`, `−8g³a³H₁₁`, `16g³a³H₁₂` (+ duals). | ✗ |
| 670  | `lem:Msurj`          | For `N≥6`, `c≠0`, `D_x M : ℝ^{2N}→ℂ⁶≅ℝ¹²` has rank 12 on an open dense subset of `V` — the **explicit 12×12 determinant** at a six-element configuration. | ✅ `bigJ_det_nonzero`/`bigJ_surj` + `DM_paper_open_dense_surjective` (`W_surj` = the open-dense surjective locus) |
| 1144 | `prop:dimZ`          | On `W_surj`: `Z_reg` (H≢0 piece) is a smooth codim-3 submanifold (dim ≤ 2N−1); the H≡0 stratum has dim ≤ 2N−3. | ✗ |
| 1197 | `lem:smooth-chart-meager` | A smooth map from open `U⊂ℝ^m` to `ℝ^n` with `m<n` has meager image (measure-zero cube cover). | ✗ (negligible→meager half proven separately) |
| 1239 | `prop:regnonzero`    | `B_{reg,≠0} ⊆ π_V(Z_reg) ∪ π_V(H≡0 stratum) ∪ B_{CaseB,≠0} ∪ B_{H0,res}`. | ✅ `prop_regnonzero` (proved 4-piece decomposition reduction) |
| 1342 | `thm:final`          | **Flagship.** Odd `N≥7` + secant/spacing hyps ⟹ ∃`ξ>0`, `F_zero` nonempty (Baire over the 4 meager branches). | ◐ `thm_final` (closeout proven, conditional on the 4 branch facts; via `nonemptiness_from_meager_branches`) |

### Appendix A — Moment coordinates / triple-side minors (L1462–1770)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 1521 | `prop:upair`  | The u-pair 2×2 minor for `(b₁,a₁₁)` is always nonzero. | ✗ |
| 1582 | `prop:vcos`   | Pure-cosine v-block determinant formula. | ✗ |
| 1604 | `prop:vsin`   | Pure-sine v-block determinant formula. | ✗ |
| 1620 | `prop:vmixed` | Mixed v-block determinant formula. | ✗ |
| 1667 | `prop:KLM`    | Reduction of the `K=0` branch via `K,L,M` cofactors. | ✗ |

### Appendix B — Gauge-fixed moment-space minors (L1771–1872)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 1793 | `prop:moment3`    | Gauge-fixed 3×3 moment-space minors (explicit). | ✗ |
| 1827 | `prop:moment5`    | Gauge-fixed 5×5 moment-space minor. | ✗ |
| 1848 | `prop:moment5alt` | Two alternative 5×5 minors. | ✗ |

### Appendix C — Common-cofactor theorem, H≡0 branch (L1873–2014)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 1886 | `prop:direct5`       | Common-cofactor factorization of the 5×5 determinant. | ✗ |
| 1941 | `cor:pairambiguity`  | The pair ambiguity is removed. | ✗ |
| 1954 | `prop:direct5alt`    | Alternative common-cofactor factorizations. | ✗ |
| 1995 | `cor:H0subcase`      | A closed H≡0 subcase. | ✗ |

### Appendix D — Further closed H≡0 subcase (L2015–2215)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 2027 | `prop:direct5szero` | Direct restricted determinants on the all-sine-zero branch. | ✗ |
| 2082 | `lem:Fij`           | Not all `F_ij` vanish. | ✗ |
| 2130 | `cor:szeroH0`       | Closed all-sine-zero H≡0 subcase. | ✗ |
| 2163 | `prop:szero-small`  | The all-sine-zero branch is high codimension. | ✗ |
| 2201 | `cor:szero-meager`  | Coefficient-degenerate all-sine-zero branch is meager. | ✗ |

### Appendix E — First residual one-cosine-zero subcase (L2216–2553)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 2224 | `prop:onecos-codim3`   | A codim-3 residual subcase. | ✗ |
| 2305 | `cor:onecos-codim3`    | Meager (first one-cosine branch). | ✗ |
| 2321 | `prop:onecos-lam`      | A second codim-3 residual subcase. | ✗ |
| 2415 | `cor:onecos-lam`       | Meager (second). | ✗ |
| 2435 | `prop:onecos-terminal` | Terminal one-cosine slice is codim 3. | ✗ |
| 2507 | `cor:onecos-terminal`  | Meager (terminal). | ✗ |
| 2530 | `cor:onecos-exhausted` | `c₁=0` one-cosine residual exhausted. | ✗ |

### Appendix F — Fully nonzero-cosine coefficient-degenerate branches (L2554–2883)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 2566 | `prop:allcos-La2`  | All-cosine `K=L=a₂=0` branch is high codimension. | ✗ |
| 2677 | `cor:allcos-La2`   | Meager. | ✗ |
| 2732 | `prop:quarterturn` | Quarter-turn symmetry of adapted coordinates. | ✗ |
| 2861 | `cor:allcos-Ma1`   | All-cosine `K=M=a₁=0` branch meager. | ✗ |

### Appendix G — First simultaneous coefficient-zero all-cosine subcase (L2884–3085)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 2897 | `prop:allcos-a1a2` | A rank-3 subcase of `K=a₁=a₂=0`. | ✗ |
| 2988 | `cor:allcos-a1a2`  | Meager subcase. | ✗ |

### Appendix H — Residual Hessian-Zero Closure `app:H0res` (L3086–3578)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 3142 | `lem:h0res-Bcuts`      | Triple B-cuts are transversal. | ✗ |
| 3174 | `prop:h0res-Bbranch`   | `B₁=B₂=B₃=0` branch meager. | ✗ |
| 3195 | `lem:h0res-residue-exc`| Residue exceptional sets. | ✗ |
| 3233 | `lem:h0res-a1a2`       | Rank 2 of the residue map. | ✗ |
| 3268 | `lem:h0res-baseSK`     | Base slice `{c₁c₂c₃≠0, S=0, K=0}` codim ≥ 2. | ✗ |
| 3348 | `prop:h0res-Sbranch`   | `S=0` branch meager. | ✗ |
| 3395 | `prop:h0res-threecos`  | Three-cosine branch meager. | ✗ |
| 3416 | `prop:h0res-twocos`    | Two-cosine branches meager. | ✗ |
| 3543 | `prop:h0res-meager`    | Residual Hessian-zero projection is meager (closes `app:H0res`). | ✗ |

### Appendix I — Direct Configuration-Space Closure of Case B `app:caseB` (L3579–6254)

| Line | Label | Statement | Isabelle |
| --- | --- | --- | --- |
| 3682 | `prop:vblock`            | Direct v-block factorization. | ✗ |
| 3712 | `prop:branch`            | Direct rank-3 branch theorem. | ✗ |
| 3811 | `cor:repair`             | What this directly repairs. | ✗ |
| 3848 | `prop:uphi-reduce`       | Reduction of the u-slice differential. | ✗ |
| 3918 | `prop:uphi-codim3`       | Vanishing u-slice branch locally codim 3. | ✗ |
| 3979 | `cor:uphi-exhausted`     | Vanishing u-slice branch exhausted. | ✗ |
| 4031 | `prop:vpair11`           | Direct `H₁₁` v-slice factorization. | ✗ |
| 4076 | `cor:vpair11`            | Rank-3 criterion on `H₁₁` branch. | ✗ |
| 4116 | `prop:szero-local`       | All-sine-zero slice codim 3. | ✗ |
| 4140 | `prop:vpair11-graph`     | Graph lift on `H₁₁` pair-minor residue. | ✗ |
| 4258 | `cor:vpair11-graph`      | `H₁₁` pair-minor residue codim 4. | ✗ |
| 4315 | `cor:H11-closed`         | Closure of the `H₁₁` branch. | ✗ |
| 4397 | `prop:vpair22`           | Direct 2×2 v-slice factorization. | ✗ |
| 4509 | `cor:vpair22`            | Sharper rank-3 criterion. | ✗ |
| 4566 | `cor:vpair22-common`     | Common-parameter residue on v-slice. | ✗ |
| 4632 | `prop:vpair22-graph`     | Three-parameter graph reduction. | ✗ |
| 4760 | `cor:vpair22-graph`      | Lifted graph envelope. | ✗ |
| 4855 | `prop:vpair22-KLM`       | Relation with `K,L,M` cofactors. | ✗ |
| 4927 | `cor:vpair22-nonzero`    | First nonvanishing consequences. | ✗ |
| 5015 | `prop:vpair22-elim`      | Elimination of the graph parameters. | ✗ |
| 5204 | `prop:vpair22-onezero`   | One-sine-zero slice codim 4 after three eliminations. | ✗ |
| 5277 | `cor:vpair22-onezero`    | Any one-sine-zero slice exhausted. | ✗ |
| 5305 | `prop:vpair22-full`      | Full scalar residue codim 4. | ✗ |
| 5390 | `cor:vpair22-full`       | Scalar residue exhausted. | ✗ |
| 5446 | `prop:H12zero`           | Direct `H₁₂=0` block factorization. | ✗ |
| 5528 | `cor:H12zero`            | Rank-3 criterion on `H₁₂=0` branch. | ✗ |
| 5655 | `prop:Lambda-common`     | Common-parameter reduction of the `Λ^{(11)}` residue. | ✗ |
| 5754 | `prop:double-param`      | Explicit double-root parameterization. | ✗ |
| 5815 | `cor:double-impossible`  | Multiple degeneracy impossible. | ✗ |
| 5834 | `prop:Lambda-simple`     | Simple-critical subcase codim 3. | ✗ |
| 5875 | `cor:Lambda-remains`     | What remains of the `Λ^{(11)}` residue. | ✗ |
| 5904 | `prop:Lambda-high`       | One higher-order degenerate critical point is high codim. | ✗ |
| 5971 | `prop:Lambda-onefold`    | One simple degenerate critical point high codim. | ✗ |
| 6046 | `cor:Lambda-refined`     | Refined residual form. | ✗ |
| 6074 | `prop:Lambda-twofold`    | Two simple degenerate critical points high codim. | ✗ |
| 6160 | `cor:Lambda-twofold`     | Refined multiple-degeneracy residue. | ✗ |
| 6184 | `cor:Lambda-closed`      | Closure of common-parameter residue. | ✗ |
| 6205 | `cor:caseBmeager`        | **Case B projection is meager on the `H≢0` side** (closes `app:caseB`; feeds `prop:regnonzero`). | ✗ |

Six unlabeled `\definition` blocks (gauge-fixing setups) at L3828, L4006, L4376,
L4804, L5188, L5431 complete the 102 count.

---

## Difficulty ranking (hardest first)

1. **`lem:Msurj`** — the explicit **12×12 symbolic determinant** at a six-element
   configuration (V-block / U-block factorization + κ-scaling). Single longest
   explicit-algebra piece. Self-contained symbolic computation.
2. **Case B `app:caseB`** — the `Λ^{(11)}` double-root elimination chain (~40
   chained results, L3579–6254). Largest single block of explicit-algebra closure.
3. **Parametric transversality / Sard** — blocks `prop:regzero` and `prop:foldzero`.
   Keystone: `regular_zero_set_projection_local_chart_2d` (IFT local chart) + `baby_Sard`.
4. **H≡0 residual closure `app:H0res`** — a finite tree of codimension closures.
5. **Real-analytic zero sets** — `lem:Efinite` / `prop:foldnonzero`
   (nontrivial real-analytic functions vanish nowhere-densely).

## Recommended sequencing (cheap → deep)

1. ~~Wire `thm_final` to `nonemptiness_from_meager_branches`~~ **DONE** — `thm_final`
   is now the proven Baire closeout, conditional on the 4 branch facts. (The Baire
   glue `final_nonemptiness_from_bad_union` / `bad_union_meagerness` /
   `nonemptiness_from_branches` was already sorry-free.)
2. ~~Transcribe the `shows True` placeholders~~ **DONE** — `lem_Efinite`,
   `prop_foldnonzero`, `prop_regnonzero` now have real statements. The two
   reductions are proved; `lem_Efinite` carries the real-analytic isolated-zeros
   `sorry`. The four `shows True` placeholders are gone; Paper.thy is down to 3
   real sorries (the two transversality stubs + `lem_Efinite`).
3. Finish the transversality pipeline (IFT chart + Sard) → closes `prop_regzero`,
   `prop_foldzero` end-to-end.
4. Real-analytic zero sets + smooth-image-meager → `lem_Efinite`, `prop_foldnonzero`.
5. The appendix (`prop_regnonzero`): start with `lem:Msurj` (12×12 determinant),
   then `prop:dimZ`, then `app:H0res` and `app:caseB`.
