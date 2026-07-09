# New_Applied_Math_Formalization

Streamlined, audited copy of the legacy `Applied_Math_Formalization` tree
(2026-07-09).  It contains **only** the theories on the import path of the
capstone theorem, plus the real-analytic bridge stack that is the active plan
for finishing it.  The legacy directory is kept untouched for history; all
new work should happen here.

## Honest status of the capstone

The capstone is `F0_dip_nonempty` in `Appendix/Robust4/Nonemptiness_Robust4.thy`
(session `Applied_Math_Appendix_Frontier`).

- **Every theory in this tree is free of `sorry`.**  (Verified by audit and by
  a full clean build; the legacy tree's on-path sorries lived in
  `Nonemptiness_Capstone.thy`, whose sorried lemmas were *used by nothing* —
  that file has been dropped and `Nonemptiness_Robust1` now imports
  `Nonemptiness_Regnonzero_Appendix` directly.)
- **The theorem is NOT assumption-free.**  `F0_dip_nonempty` carries two
  explicit analytic hypotheses, threaded honestly through the whole D3/D4
  reduction chain:
  1. `d3_detHess_arc_chart_core_all` — the D3 det-HessU/NSx degenerate-critical
     chart theorem over one C1 arc (degenerate criticality with non-surjective
     configuration derivative);
  2. `branchP_indep_closed_cover_core_all` — the Branch-P (D4) countable closed
     negligible cover of the 2-parameter moment-rank-drop continuum
     (per-fixed-angle nowhere-density is not enough; a genuine joint
     codimension-3 argument is needed).

  Everything else — feasibility/Slater witness, continuity half, D1/D2/D5
  strata, the D3 finite C1 arc cover, all reduction plumbing — is proved.
  Discharging these two hypotheses is the remaining mathematical work.

## Directory map (build order)

| Session | Dir | Contents |
|---|---|---|
| `Applied_Math_Base` | `Base/` | external platform (Munkres, Jordan, Perron-Frobenius, HOL-Complex_Analysis) |
| `Applied_Math_BlockDet` | `BlockDet/` | block determinants, big-J, the moment map `M_paper` |
| `Applied_Math_MomentJac` | `MomentJac/` | `D_x M_paper = bigJ` Jacobian identification |
| `Applied_Math_Nonemptiness` | `.` (root) | `Nonemptiness_Paper` + support: `Topology_Bridge`, `Nonemptiness_Scaffold/Array_Factor/Feasibility/Spine`, `Regular_Value_Theorem`, `Parametric_Transversality_Euclidean(_Base)` |
| `Applied_Math_HigherDiff` | `HigherDiff/` | k-times Fréchet differentiability, Taylor-Peano, Ck1/C1 bridge |
| `Applied_Math_Appendix_Base` | `Appendix/` | `Nonemptiness_Regnonzero_Appendix` (paper's regnonzero appendix, used by the curve cover) + `Nonemptiness_Robust1` (long stable first half) |
| `Applied_Math_Appendix` | `Appendix/Robust2/` | `Nonemptiness_Robust2` (Sym² T diagonal moment laws, planar transversality engine) |
| `Applied_Math_Appendix_Full` | `Appendix/Robust3/` | `Nonemptiness_Robust3` (M5 scaffold through the D3 cover set-algebra bridge) |
| `Applied_Math_Morse` | `Morse/` | 2D Morse/saddle/Hadamard/arc-clip helpers for the curve cover |
| `Applied_Math_D3_Curve_Cover` | `Appendix/Robust4Cover/` | `D3_Curve_Cover` (finite C1 arc cover of the phase-collinear locus, proved) |
| `Applied_Math_Appendix_Frontier` | `Appendix/Robust4/` | `Nonemptiness_Robust4` — **the live frontier + `F0_dip_nonempty`** |
| `Applied_Math_Analytic` | `Analytic/` | real-analytic (C^ω) function theory + bump functions |
| `Applied_Math_Analytic_Inverse` | `Analytic/Inverse/` | majorant-method formal-series local inverse |
| `Applied_Math_Analytic_Complex` | `Analytic/Complex/` | complexification bridge + analytic IFT + nowhere-dense-zeros workhorse |
| `Applied_Math_D34_Analytic` | `Appendix/AnalyticBridge/` | `D34_Analytic_Bridge` + `D34_H0res_Branch`: verified Case-B/H0 machinery aimed at the two open hypotheses |

## Building

From this directory:

```
../../Isabelle2025-2/bin/isabelle build -b -d . \
  -d /home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology \
  -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys \
  Applied_Math_Appendix_Frontier Applied_Math_D34_Analytic
```

For interactive Robust4 work, load the frontier against the curve-cover heap
(never bake the buffer you are editing into its own heap):

```
../../Isabelle2025-2/bin/isabelle jedit -l Applied_Math_D3_Curve_Cover -d . \
  -d /home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology \
  -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys \
  Appendix/Robust4/Nonemptiness_Robust4.thy
```

## What was dropped from the legacy tree, and why

- **All 55 `M5_Dev_*` scratch sessions** and the 18 `Appendix/Scratch_*.thy`
  files: dev-scratch history, already spliced or superseded.  (The six Morse
  helper theories were rescued from `M5_Dev_Morse/` into `Morse/` — they are a
  real dependency of `D3_Curve_Cover`.)
- **`Nonemptiness_Capstone.thy`** (6 active sorries): its sorried lemmas and
  flagship `odd_N_nonemptiness` were cited by nothing downstream; it only sat
  in the import chain.  Removing it makes the whole tree sorry-free.
- (`Nonemptiness_Regnonzero_Appendix.thy` was initially slated for removal but
  is **kept**: the full build revealed `D3_Curve_Cover` genuinely uses its
  `lem_h0res_Bcuts`.  It is sorry-free, so the zero-sorry guarantee stands.)
- **`D34_UPhi_Branch.thy`** (1 sorry): the remaining sorry
  (`Phi_par_parallel_slot_F_eta_identification`) was found by Codex to be
  **unsound as stated** (the `F_eta` target matches the real-part moment
  derivative, not the imaginary-part one the repo's phase convention
  produces).  Its proven Tier 1 pieces live on in legacy for salvage after a
  restatement.
- **`Analytic/Real_Analytic_Complex.thy`** (root-level copy, 7 sorries): dead
  duplicate; the live, sorry-free version is `Analytic/Complex/Real_Analytic_Complex.thy`.
- **`SardNegligible/`**, `Nonemptiness_Work_Session.thy`: standalone/unused.
- Coordination docs (`PARALLEL_WITH_CODEX.md`, `INSTRUCTIONS_FOR_CODEX.md`,
  `NOTES_FOR_CLAUDE.md`, plans): legacy history; `FORMALIZATION_DIARY.md` was
  copied here and remains the append-only log going forward.

## Known dead ends (do not retry)

- The `H_par` / `e_par` double-contraction approach to the H12=0 branch:
  its load-bearing hypothesis `h_par_vslot_zero` was machine-verified **false**
  (exact witness, interval arithmetic).  A geodesic/normal-coordinate approach
  would be needed instead.
- Proving `Phi_par_parallel_slot_F_eta_identification` as stated (see above).
