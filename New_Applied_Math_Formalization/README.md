# New_Applied_Math_Formalization

Isabelle/HOL proof that the robust feasible set `F0` of the paper
(`../Paper/Geometry_Driven_Optimization_of_Passive_UAV_Relay_Arrays.pdf`,
Eq. 22; Conjecture 5 there) is nonempty.  Target: Isabelle2026; nothing beyond
its distribution is needed.  The legacy directory `../Applied_Math_Formalization`
is kept untouched for history.

## The theorems

`Main/Degenerate_Configurations.thy` (session `Applied_Math_Main`), for an odd
number `N ≥ 5` of relays, source overhead and main beam horizontal:

- `degenerate_configurations_nowhere_dense`: the configurations whose pattern
  has a degenerate critical point in the angular box form a closed nowhere
  dense set;
- `nondegenerate_in_X0`: every other configuration is robust for suitable
  margins;
- `F0_dip_interior_nonempty`: for suitable margins the robust feasible set `F0`
  contains a ball;
- `F0_dip_nonempty_final`: `F0` is nonempty for every minimum spacing, every
  null threshold above zero, every minimum main-beam power below the maximum,
  every null direction other than the main beam, the paper's plane
  coefficients, all large radii, and suitable margins.

`Main/Poles_And_Fixed_Margins.thy` has two facts behind the form of these
statements: at a pole of the dipole pattern every configuration has a
degenerate critical point, and the margins have to depend on the configuration.

The theorems have no other hypotheses.  Every session is built with
`quick_and_dirty = false`, and `Applied_Math_Oracle_Audit` fails the build if
one of them depends on an oracle.

## Theories (build order)

| Session | Dir | Theories |
|---|---|---|
| `Applied_Math_Base` | `Base/` | none of its own: the Munkres formalization on top of `HOL-Complex_Analysis` |
| `Applied_Math_Analysis` | `Analysis/` | `Munkres_Baire_Bridge` (the Baire category theorem), `Meager_Sets`, `Regular_Value_Theorem`, `Parametric_Transversality_Euclidean`, `Parametric_Transversality_Planar`, `Line_Entire_Functions` (functions whose restrictions to lines are entire), `Negligible_Line_Slices` |
| `Applied_Math_Pattern` | `Pattern/` | `Array_Factor` (array factor `A_cart`, pattern `U_cart`), `Moment_Map` (`A_moment`, `first_moment`, `second_moment`), `Pattern_Derivatives` (gradient `gradU`, Hessian `HessU`), `Feasible_Set`, `Dipole_Pattern` (gain, steering wavevector, smoothness), `Dipole_Gain_Derivatives`, `Dipole_Gain_Analytic`, `Robust_Sets` (`Xrobust`, `X0`, `F0`, the box `OmegaPF`), `Feasibility_Witness`, `Pattern_Moments`, `Gradient_Field_C1` |
| `Applied_Math_Strata` | `Strata/` | four of the five classes of degenerate configurations are meager: `Null_Stratum`, `Regular_Stratum`, `Critical_Slices`, `Main_Beam_Stratum`, `Steering_Singular_Stratum` |
| `Applied_Math_Residual` | `Residual/` | the fifth class: `Residual_Phase_Equation`, `Residual_Equations` (the set `residual_set`), `Residual_Design`, `Residual_Charts`, `Residual_Chart_Cover`, `Residual_Aligned`, `Residual_Meager` |
| `Applied_Math_Main` | `Main/` | `Degenerate_Configurations`, `Poles_And_Fixed_Margins` |
| `Applied_Math_Oracle_Audit` | `Audit/` | fails the build if one of the theorems uses an oracle; `Audit/Control` checks that the test detects a `sorry` |

`Munkres/` is a copy of the Munkres topology library (session
`Munkres_Topology_Local`, two lemma names updated for Isabelle2026): the
formalization of Bryant, Huerta y Munive, Kaliszyk and Urban (LNCS 16870,
arXiv:2604.07455).  The Baire category theorem is taken from it.

Derivatives are those of HOL-Analysis in Isabelle2026: the gradient and the
Hessian of the pattern are `∇` and `∇²` of `Higher_Differentiability_Multi`,
the Jacobian of the wavevector map is `jacobian`, smoothness is `Ck_on`
(library of Bryant, Huerta y Munive and Foster, *Verifying Numerical Methods
with Isabelle/HOL*, SEFM 2026, arXiv:2511.20550).  Matrices and determinants
are those of HOL-Analysis as well.  No entry of the Archive of Formal Proofs is
used.

The tree contains only what the theorems use.
`tools/unused_facts/Unused_Facts.thy` lists the named lemmas on which none of
them depends and fails if there is one; `tools/build_session.sh` builds one
session with a hard time limit; the two Python scripts in `tools/` are numeric
checks of the residual equations.

## Building (Isabelle2026)

From this directory:

```
~/Desktop/Isabelle/Isabelle2026/bin/isabelle build -b -d . Applied_Math_Oracle_Audit
```

This builds the whole chain and fails if a theorem depends on an oracle.  To
read the final theory in Isabelle/jEdit:

```
~/Desktop/Isabelle/Isabelle2026/bin/isabelle jedit -d . -l Applied_Math_Residual \
  Main/Degenerate_Configurations.thy
```

## History

- `FORMALIZATION_DIARY.md` is the log; its entry of 2026-11-11 on the removal
  of unused material lists the old and new names of theories, definitions and
  lemmas.
- Commit `fd07a54` is the last state before that removal.  It contains the
  theories that the theorems stopped using: the six-moment determinant
  (`BlockDet/`, `MomentJac/`), the curve cover of the phase-collinear locus
  (`Morse/`, `Appendix/Robust4Cover/`) and others, and the archive of earlier
  attempts that was never built on Isabelle2026 (`HigherDiff/`, `Analytic/`,
  `Appendix/`, `M5_Dev_*`, `d4_*.py`; git tag `pre-isabelle2026` has them in
  their Isabelle2025-2 form).
- `END_TO_END_PLAN.md` and `Sketch.md` are the plan and the informal proof
  from which the end-to-end theorem was reached; they use the names of that
  state.
