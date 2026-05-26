# Verified Drone Theory

Machine-checked **Isabelle/HOL** formalizations underpinning this project's
applied-mathematics results.

## Contents

- **`Applied_Math_Formalization/`** — the Euclidean "parametric transversality"
  pipeline and the antenna *nonemptiness* development.
  - `Parametric_Transversality_Euclidean_Base.thy` — regular-value / submanifold
    infrastructure for a joint map `G : V × Ω → ℝ²`. Notably includes the proven
    lemma **`countable_chart_cover_of_levelset_2d`**: the regular zero-set
    `{q ∈ V × Ω. G q = 0}` admits a *countable* smooth chart cover (each chart
    open, differentiable, with image open in the level set).
  - `Nonemptiness_*.thy` — the nonemptiness/feasibility development.
  - `Topology_Bridge.thy` — Lebesgue-negligible ↔ topological-meager bridge.
  - `ROADMAP.md` — development roadmap.

## Building

Built with **Isabelle2025-2**. Session definitions live in
`Applied_Math_Formalization/ROOT`:

- `Applied_Math_Base` — stable base heap (HOL-Analysis + local Munkres topology).
- `Applied_Math_Nonemptiness` — minimal heap on top of the base.

The base heap depends on a local Munkres topology session. Evolving development
theories are intended to be checked interactively in Isabelle/jEdit rather than
pre-built into the heap.
