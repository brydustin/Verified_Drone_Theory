# New_Applied_Math_Formalization

Isabelle/HOL proof that the robust feasible set `F0` of the paper
(`../Paper/Geometry_Driven_Optimization_of_Passive_UAV_Relay_Arrays.pdf`,
Eq. 22; Conjecture 5 there) is nonempty.  Target: Isabelle2026 with AFP
`afp-2026-10-29`.  The legacy directory `../Applied_Math_Formalization` is kept
untouched for history.

## Status

The end-to-end theorem is `F0_dip_nonempty_final` in
`Residual/Final/Nonemptiness_Final.thy` (session `Applied_Math_Final`), proved
2026-11-11.  For an odd number `N ≥ 6` of antennas, source overhead and main
beam horizontal, it states that the robust feasible set `F0` of the paper is
nonempty for every minimum spacing, every null threshold above zero, every
minimum main-beam power below the maximum, every null direction other than
the main beam, the paper's plane coefficients, all large radii, and suitable
margins.  It has no other hypotheses, every session is built with
`quick_and_dirty = false`, and `Applied_Math_Oracle_Audit` fails the build if
the theorem depends on an oracle.  See `END_TO_END_PLAN.md` for the statement,
its relation to the paper, and the route.

The earlier conditional theorem `F0_dip_nonempty` and its two assumed chart-core
predicates were removed from `Appendix/Robust4/Nonemptiness_Robust4.thy` on
2026-11-11; the tag `pre-isabelle2026` still has them.

Documents: `END_TO_END_PLAN.md` (statement, relation to the paper, route,
verification protocol), `Sketch.md` §8 (the proof in plain mathematics and the
table of formal names), `FORMALIZATION_DIARY.md` (log).

## Directory map (build order)

| Session | Dir | Contents |
|---|---|---|
| `Applied_Math_Base` | `Base/` | external platform (Munkres, Jordan, Perron-Frobenius, HOL-Complex_Analysis) |
| `Applied_Math_BlockDet` | `BlockDet/` | block determinants, big-J, the moment map `M_paper` |
| `Applied_Math_MomentJac` | `MomentJac/` | `D_x M_paper = bigJ` Jacobian identification |
| `Applied_Math_Nonemptiness` | `.` (root) | `Nonemptiness_Paper` + support: `Topology_Bridge`, `Nonemptiness_Scaffold/Array_Factor/Feasibility/Spine`, `Regular_Value_Theorem`, `Parametric_Transversality_Euclidean(_Base)` |
| `Applied_Math_Appendix_Base` | `Appendix/` | `Nonemptiness_Regnonzero_Appendix` (paper's regnonzero appendix, used by the curve cover) + `Nonemptiness_Robust1` (long stable first half) |
| `Applied_Math_Appendix` | `Appendix/Robust2/` | `Nonemptiness_Robust2` (Sym² T diagonal moment laws, planar transversality engine) |
| `Applied_Math_Appendix_Full` | `Appendix/Robust3/` | `Nonemptiness_Robust3` (M5 scaffold through the D3 cover set-algebra bridge) |
| `Applied_Math_Morse` | `Morse/` | 2D Morse/saddle/Hadamard/arc-clip helpers for the curve cover |
| `Applied_Math_D3_Curve_Cover` | `Appendix/Robust4Cover/` | `D3_Curve_Cover` (finite C1 arc cover of the phase-collinear locus, proved) |
| `Applied_Math_Appendix_Frontier` | `Appendix/Robust4/` | `Nonemptiness_Robust4`: the retained bad set `BadXGW`, the regular stratum, the lemmas from a regular feasible configuration to a point of `F0` |
| `Applied_Math_Residual_Analysis` | `Residual/` | `Residual_Measure` (Fubini with countable slices), `Residual_Null_Set` (the phase functions; the zero set of `res_f` is negligible) |
| `Applied_Math_Residual` | `Residual/Stratum/` | the three equations at a point of `BadXGW`, the design geometry, the charts and their cover, the aligned cover, `residual_meager_design` |
| `Applied_Math_Final` | `Residual/Final/` | `Nonemptiness_Final`: `F0_dip_nonempty_final`, its explicit form, a numeric example |
| `Applied_Math_Oracle_Audit` | `Audit/` | fails the build if the final theorem, or a theorem on the way to it, uses an oracle; `Audit/Control` checks that the test detects a `sorry` |

`Munkres/` is the vendored Munkres topology library (session
`Munkres_Topology_Local`, two lemma names updated for Isabelle2026).
`tools/` holds the build script and the numeric checks of the residual
equations.

### Archive (not built)

Superseded work, kept in place for history.  It targets Isabelle2025-2, is
commented out in `ROOT`, and parts of it contain `sorry` or refer to lemmas
since removed:

- theories: `HigherDiff/`, `Analytic/`, `Appendix/AnalyticBridge/`,
  `Appendix/Wiring/`, all `M5_Dev_*`;
- material of the superseded D3/D4 route: `d4_*.py` and §1–§7 of `Sketch.md`.

The last Isabelle2025-2 state of the tree is the git tag `pre-isabelle2026`.

## Building (Isabelle2026)

Every session is strict (`quick_and_dirty = false`).  From this directory:

```
~/Desktop/Isabelle/Isabelle2026/bin/isabelle build -b -d . \
  -d ~/Desktop/Isabelle/afp-2026-10-29/thys Applied_Math_Oracle_Audit
```

This builds the whole chain (about 16 minutes from scratch) and fails if the
final theorem depends on an oracle.  `tools/build_session.sh SESSION [SECONDS]`
does the same for one session with a hard time limit.  To read the final
theory in Isabelle/jEdit:

```
~/Desktop/Isabelle/Isabelle2026/bin/isabelle jedit -d . \
  -d ~/Desktop/Isabelle/afp-2026-10-29/thys -l Applied_Math_Residual \
  Residual/Final/Nonemptiness_Final.thy
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
