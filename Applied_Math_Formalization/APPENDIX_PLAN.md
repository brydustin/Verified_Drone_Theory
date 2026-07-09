# Unconditional `thm:final` — Full Appendix Execution Plan

**Decision (2026-05-29):** commit to the complete unconditional theorem — discharge
*every* hypothesis of `thm_final`, transcribing the full appendix. The honest path.

## Ground-truth source
The paper with the complete appendix proofs (the only place the detailed arguments
live) is:

    /home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Applied Math/nonemptiness_unified_singlefile_complete.tex   (6285 lines, + .pdf)

`STATUS.md`'s `L####` numbers index *this* file (±1–2). `\label{...}` names match the
STATUS "Label" column. Transcribe from here; do not reverse-engineer from one-liners.

## What is already DONE (foundations — do not redo)
- **Architecture:** `thm_final` = Baire closeout over 4 meager branches
  (`nonemptiness_from_meager_branches`); `prop_regnonzero` = proved 4-piece
  decomposition reduction. Both proof-complete, branch facts are hypotheses.
- **`lem:Msurj` (THE #1-hardest item, the explicit 12×12 determinant):** DONE as
  `bigJ_det_nonzero` + `bigJ_surj` + `DM_paper_open_dense_surjective`
  (`= W_surj` is open dense). The tex partials (∂_uA, ∂_uM₁,…) = `DM_paper_x_components`.
- **Engines built & reusable:** transversality keystone
  `regular_zero_set_projection_local_chart_2d` (IFT chart); real-analytic
  nowhere-density engine (`rline_entire`/`cline_entire`/`lines_entire_slice_nowhere_dense`,
  `analytic_continuation`); Sard negligible→meager half (`Applied_Math_Sard`).

## `prop:regnonzero` decomposition (tex L1240) — the exact 4 facts to discharge
`B_{reg,≠0} ⊆ π_V(Z_reg) ∪ π_V(Z∩{H≡0}∩W_surj) ∪ B_{CaseB,≠0} ∪ B_{H0,res}`, need first three meager:
1. `π_V(Z_reg)` meager        ← `prop:dimZ` (codim-3, dim ≤ 2N−1) + `lem:smooth-chart-meager`
2. `π_V(Z∩{H≡0}∩W_surj)` meager ← `prop:dimZ` (dim ≤ 2N−3) + `lem:smooth-chart-meager`   [the "ZH0surj" piece]
3. `B_{CaseB,≠0}` meager       ← `cor:caseBmeager` (Appendix I)
4. `B_{H0,res}` meager         ← `prop:h0res-meager` (Appendix H)

## Dependency-ordered execution tiers

### Tier 0 — close the *non*-appendix branches (shrinks thm_final's hypotheses fastest)
- [ ] `lem_Efinite` isolated-zeros `proof hole` → closes `prop_foldnonzero`.
      (Reuse the real-analytic engine: nontrivial real-analytic g has isolated zeros.)
- [ ] Transversality pipeline `proof hole`s in `Parametric_Transversality_Euclidean_Base.thy`
      (L369 `charts_core_2d`, L1015 meager-stub) → closes `prop_regzero`, `prop_foldzero`.
- [ ] `prop_openfeas` (◐ feasibility half), `lem_twotriplecover` (◐ geometric packaging).

### Tier 1 — appendix foundations
- [x] `lem:smooth-chart-meager` (tex L1198): smooth U⊂ℝ^m→ℝ^n, m<n ⟹ meager image.
      DONE as `smooth_chart_meager` in `Parametric_Transversality_Euclidean_Base`, via
      general `rank_deficient_C1_image_meager` (open `U`, C¹, rank `<n` ⟹ meager image:
      `open_sigma_compact_exhaustion` + `baby_Sard` per piece + `meager_negligible_closed_cover`).
      Also serves transversality stub 2 (rank-deficient, not just m<n).
- [ ] Appendix A minors (L1462): `prop:upair`, `prop:vcos`, `prop:vsin`, `prop:vmixed`, `prop:KLM`.
- [ ] Appendix B minors (L1771): `prop:moment3`, `prop:moment5`, `prop:moment5alt`.
      (All self-contained symbolic determinants — reuse the `bigJ_det` pattern.)

### Tier 2 — codimension of `Z_reg` and the H≡0 stratum
- [ ] `prop:dimZ` (L1145): `Z_reg` codim-3 smooth submanifold; `{H≡0}` stratum dim ≤ 2N−3.
      Uses the regular-value keystone (done) + Tier-1 minors for the rank inputs.
      → discharges facts 1 & 2.
- [ ] Appendices C–G (L1873–3085): the closed `H≡0` subcase reductions feeding dimZ /
      h0res (direct5, szero, onecos, allcos chains).

### Tier 3 — the two big meagerness grinds
- [ ] Appendix H `app:H0res` (L3086, 9 lemmas) → `prop:h0res-meager` → fact 4.
- [ ] Appendix I `app:caseB` (L3579, ~40 lemmas, the Λ^{(11)} double-root chain) →
      `cor:caseBmeager` → fact 3.  Largest single block.

### Tier 4 — top-level instantiation → UNCONDITIONAL
- [ ] Define the concrete bad sets; prove each of the 4 branches meager for them;
      instantiate `thm_final` to remove every hypothesis.

## Working rules (autonomous mode)
Build→verify(BUILD_EXIT=0)→commit→push per verified checkpoint. Transcribe one
`\label` at a time; keep STATUS.md's Isabelle column current; newest-first diary entry
each session. Use `isabelle eval_at`+sledgehammer, not blind tactics. Respect the
HMA-free / bounded-exhaust / pin-binder-types traps (see autoformalization memory).
