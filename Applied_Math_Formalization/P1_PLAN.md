# P1 — Moment-map / `prop_regnonzero` branch plan

Tracked plan for the moment-map (regular stratum, `A ≠ 0`) branch of the odd-`N`
nonemptiness theorem. Previously this roadmap lived only in commit-message labels
(`P1.1`–`P1.3`) and was never written down; this file is the source of truth.
Status mirrored in [FORMALIZATION_DIARY.md](FORMALIZATION_DIARY.md).

## Goal

Make `meager (ZH0surj ∩ V)` (the H≡0-on-the-regular-stratum bad set) unconditional
for the concrete moment map, feeding the `ZH0surj` hypothesis of `prop_regnonzero`
(`Nonemptiness_Paper.thy`), itself one of the four branches of `thm:final`.

The engine for `ZH0surj` is: on the **open dense** stratum where the moment-map
derivative `DM_paper_x` is surjective, parametric transversality / Sard gives
meagerness. So we must show that surjective stratum is open **and dense** in `V`.

## Steps and status

| Step | Result | Status |
|---|---|---|
| P1.1 | `M_paper` (six-component moment map) defined | ✅ `28846a2` |
| P1.2 | base config `x0_paper`, `c0_paper` | ✅ `20c7035` |
| P1.3 | moment-map + Fréchet derivatives factored into `Moment_Map.thy` heap | ✅ `1b77582` |
| P1.4 | `M_paper` is **C¹** — `continuous_on V (λx. Blinfun (DM_paper_x x c))` (`C1_M_paper_x`) | ✅ (this arc) |
| — | `bigJ_det` = `-(5·π⁸)/3`, `bigJ_det_nonzero`, `bigJ_surj` | ✅ (BlockDet, 0 sorry) |
| P1.5 | **Jacobian identification**: `DM_paper_x x0_paper c0_paper = (*v) bigJ` ⟹ `surj` at the base point (the regular-point input) | ❌ |
| P1.6 | `rank_lower_semicont_open_dense_propagation` (`Nonemptiness_Paper.thy:3650`): surjective stratum is open **and dense** | ❌ (sorry) |
| P1.7 | assemble `DM_paper_open_dense_surjective` (C¹ + regular point + P1.6) → `ZH0surj` meager → `prop_regnonzero` unconditional | ❌ |

## Key finding (2026-05-29): density needs real-analyticity, **not** C¹

The conclusion of `rank_lower_semicont_open_dense_propagation` forces the
surjective stratum to be **dense** in `V` (`V ⊆ closure U`). Its docstring claimed
this follows from "openness + one regular point + connectedness." **That is false.**
Counterexample: on connected open `V = ℝ`, a C¹ `ℱ` with `Dℱ ≠ 0` at `0` but
`Dℱ ≡ 0` on `[1,2]` has a non-dense surjective stratum. So:

- **C¹ ⟹ the surjective stratum is *open*** (genuine rank lower-semicontinuity).
- **Density needs real-analyticity** of the Jacobian (its minors are trig
  polynomials ⟹ a non-trivial minor's zero set is nowhere dense).

Decision (user, 2026-05-29): **build the real-analytic density unconditionally.**

## Revised P1.6 route — the real-analytic engine ALREADY EXISTS

The hard analytic infrastructure is already built and proven in
`Nonemptiness_Paper.thy` (for the array-factor / `prop_foldnonzero` branch):

- `lines_entire_identity` / `lines_entire_slice_nowhere_dense` — the 1‑D
  line-restriction identity theorem (via `analytic_continuation`): continuous +
  entire line restrictions + nontrivial ⟹ **nowhere-dense zero set**.
- closure algebra `cline_entire` / `rline_entire`: `const`, `add`, `mult`, `sum`,
  `cis_linear`, `Re`, `Im`, `scale`, `cmod_sq`.
- newly added base cases for the moment map: `rline_entire_coord`,
  `cline_entire_phase`, `rline_entire_cos_inner`, `rline_entire_sin_inner`.

So P1.6 reduces to **instantiation**, not foundational building:

1. Define the minor `m*(x)` = `det` of the 12×12 real-Jacobian submatrix of
   `DM_paper_x x c` on the 6 base points' coordinate columns (the `bigJ` block).
2. `m*` is `rline_entire` — `det` = sum of products of entries; each entry is a
   coordinate-polynomial × `cos`/`sin (c · (x$n))`; closure lemmas finish it.
3. `m*` is continuous (from P1.4 / `DM_paper_x` continuity).
4. **Nontrivial**: `m*(x0_paper) = det bigJ = -(5·π⁸)/3 ≠ 0` (this is P1.5's
   Jacobian identification).
5. `lines_entire_slice_nowhere_dense` ⟹ `{x∈V. m* x = 0}` nowhere dense.
6. `{m* ≠ 0} ⊆ {x. surj (DM_paper_x x c)}` (a non-zero 12×12 minor ⟹ full row
   rank ⟹ surjective) — gives an open dense subset of the surjective stratum.
7. Assemble the `open U ∧ U ⊆ V ∧ V ⊆ closure U ∧ (∀x∈U. surj …)` conclusion.

P1.5 (the `bigJ`↔`DM_paper_x` identification) is the prerequisite for step 4 and
is the next concrete task.
