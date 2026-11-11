# Verified Drone Theory

Machine-checked **Isabelle/HOL** formalizations underpinning this project's
applied-mathematics results.

## Main result

`F0_dip_nonempty_final` in
`New_Applied_Math_Formalization/Residual/Final/Nonemptiness_Final.thy`: the
robust feasible set `F0` of the paper (`Paper/`, Eq. 22; Conjecture 5 there) is
nonempty.  It holds for an odd number `N ≥ 5` of antennas, source overhead and
main beam horizontal, every minimum spacing, every null threshold above zero,
every minimum main-beam power below the maximum, every null direction other
than the main beam, the paper's plane coefficients, all large radii, and
suitable margins.  No other hypotheses, no oracles (checked at build time).

The same theory proves more: the configurations whose pattern has a degenerate
critical point in the angular box form a closed nowhere dense set
(`degenerate_configurations_nowhere_dense`), every other configuration is
robust for suitable margins (`nondegenerate_in_X0`), and for suitable margins
`F0` contains a ball (`F0_dip_interior_nonempty`).

## Contents

- **`New_Applied_Math_Formalization/`** — the proof of the main result, for
  **Isabelle2026**.  Its `README.md` has the directory map and the build
  command; `END_TO_END_PLAN.md` relates the theorem to the paper.
- **`Paper/`** — the paper.
- **`Applied_Math_Formalization/`** — the legacy tree (Isabelle2025-2), kept
  for history: the Euclidean "parametric transversality" pipeline and the
  earlier nonemptiness development.
  - `Parametric_Transversality_Euclidean_Base.thy` — regular-value / submanifold
    infrastructure for a joint map `G : V × Ω → ℝ²`, including
    **`countable_chart_cover_of_levelset_2d`**: the regular zero-set
    `{q ∈ V × Ω. G q = 0}` admits a *countable* smooth chart cover.
  - `Nonemptiness_*.thy` — the nonemptiness/feasibility development.
  - `Topology_Bridge.thy` — Lebesgue-negligible ↔ topological-meager bridge.
  - `ROADMAP.md` — development roadmap.

## Building

The main result (Isabelle2026, AFP `afp-2026-10-29`; about 16 minutes from
scratch):

```
cd New_Applied_Math_Formalization
isabelle build -b -d . -d <AFP>/thys Applied_Math_Oracle_Audit
```

The legacy tree is built with **Isabelle2025-2**.  Its session definitions live in
`Applied_Math_Formalization/ROOT`:

- `Applied_Math_Base` — stable base heap (HOL-Analysis + local Munkres topology).
- `Applied_Math_Nonemptiness` — minimal heap on top of the base.

The base heap depends on a local Munkres topology session. Evolving development
theories are intended to be checked interactively in Isabelle/jEdit rather than
pre-built into the heap.
