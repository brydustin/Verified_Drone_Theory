# Instructions for Codex — continuing this formalization

Claude is handing off active work here due to running low on budget in its
session. This document is the roadmap. It was written after directly
re-checking the current repo state (git log, actual `proof hole` locations via
grep, actual file contents) — not from memory of what should be true. Where
something below is unverified or a fork's self-report rather than something
Claude directly confirmed, it says so.

Read this whole file before doing anything. Then read `PARALLEL_WITH_CODEX.md`
(the existing coordination doc — still accurate for house style and gotchas,
just not for "what's next", which this file supersedes) and the tail of
`FORMALIZATION_DIARY.md`.

## 0. THE MOST IMPORTANT THING — read this before continuing any Case-B work

The goal is `theorem F0_dip_nonempty` in `Appendix/Robust3/Nonemptiness_Robust3.thy`
(currently at line 3450). As of this writing there are exactly **two** real
`proof hole`s left in that file (verified via `grep -n "^\s*proof hole\s*$\|by proof hole\| proof hole$"`,
not by trusting comments that merely mention the word "proof hole"):

1. **`m5_D34_D3_collinear`** (statement at line 2412, `proof hole` at line 2424).
2. **`branchP_indep_charts_Nn`** (deep inside the D4 chain — `m5_D34_D4_branchP`
   itself, line 2625, is *already proven*, built on `branchP_indep_core` →
   `branchP_indep_negligible_closed_cover` → ... → `branchP_indep_charts_Nn`,
   which carries the actual `proof hole` and is explicitly commented as "The single
   irreducible `proof hole` of this file").

**Neither of these two proof hole statements mentions `det(HessU)`, `G11`, `G22`,
`Phi_par`, or anything from the Case-B analytic route.** Read their exact
statements yourself (lines 2412–2421 and ~2508–2534) — both are phrased purely
in terms of `gradU(...) = 0`, `det(matrix(Dcvec_dip...))≠0`, `cvec_dip≠0`, and
`¬ surj (DM_paper_x x c)` (moment-map non-surjectivity). This is the *older*,
relaxed formulation, reached via `m5_D34_subset_mstarg_residual` (line ~2365),
which is a **pure-set-inclusion enlargement**: it proves the true D34 bad set
(which retains `det(HessU)=0 ∧ A_cart≠0 ∧ ¬(∃Dx. gradU-deriv surj)` — see
`meager_rank_deficient_stratum`, line ~2743, for the tighter target) is a
*subset* of this looser, `¬surj(DM_paper_x)`-driven set, then asks you to prove
meagerness of the *looser* superset directly. That's strictly harder than
necessary, and it's also **not what any of the Case-B / analytic-bridge work
built this session targets**.

**What this means concretely:** `Appendix/AnalyticBridge/D34_Analytic_Bridge.thy`
(4504 lines) + `D34_UPhi_Branch.thy` (220 lines, Codex's own u-slice work) +
`D34_H0res_Branch.thy` (171 lines) — all verified, all real, ~4900 lines total
— are currently **imported by nothing that `Nonemptiness_Robust3.thy` uses**.
Confirmed directly: `Nonemptiness_Robust3.thy`'s only import is
`"Applied_Math_Appendix.Nonemptiness_Robust2"` (line 2 of that file). None of
the AnalyticBridge files are in that import chain at all.

**"Layer 5" — restating `m5_D34_D3_collinear`/`m5_D34_D4_branchP` to retain the
Hessian conjuncts (so their targets are the actual Case-B set, not the
enlarged one) and rewiring `m5_D34_residual`'s proof to use a *tight* inclusion
instead of `m5_D34_subset_mstarg_residual`'s loose one — has not been started.**
This is not a detail to get to eventually; it determines the *exact shape*
every Case-B sub-lemma needs to have to be useful at all. Recommendation:
**investigate this rewiring before sinking more effort into new Case-B
sub-branches** (`Lambda-closed`, finishing `vpair22-full`, more of `H0res`).
It's entirely possible that once the true target is written out precisely,
some of what's already built doesn't fit the exact shape needed and needs
adjusting — better to find that out now than after building more on the
current shape.

If, after investigating, restating D3'/D4' with the retained conjuncts turns
out to be its own hard problem (plausible — it needs the tight direction of
`m5_D34_subset_mstarg_residual`'s argument, which nobody has attempted), that
is itself the right thing to report back and scope carefully, the same way
Claude did for `cor:H12zero` and `cor:vpair22-full`, rather than guessed at.

## 1. What's actually proven and verified (regardless of the wiring gap above)

All of the below is genuinely proven in Isabelle (checked via `isabelle build`,
`BUILD_EXIT=0`), even though — per §0 — none of it is wired into
`F0_dip_nonempty` yet. It's real, reusable infrastructure once the wiring
question is resolved. Everything lives in
`Appendix/AnalyticBridge/D34_Analytic_Bridge.thy` unless noted.

**The `H11≠0` branch (`prop:vpair11`/`cor:vpair11`), commit `b2e0601`, `2394769`:**
`e_par`, `Phi_par` (the invariant fix for `Φ1`'s v-slot independence — see the
gotcha in §3), `G11`, `Delta_ij`, `det3`, `Jac3`, `Jac3_identity`,
`Jac3_nonzero_criterion` — the rank-3 criterion for this branch, fully proven.

**The `H12≠0,H22≠0` branch bare rank-3 criterion (`prop:vpair22`/`cor:vpair22`),
commit `bd45b71`:** `G22`, `Delta_ij_22`, `Jac3_22`, `Jac3_22_identity`,
`Jac3_22_nonzero_criterion` — built by direct reuse of the H11 pattern (same
`Phi_par`/`det3`), verified on the first attempt.

**`cor:vpair22-full` (the deeper closure of the H12≠0,H22≠0 branch) — IN
PROGRESS, NOT LANDED.** A background fork built early scaffolding
(`M5_Dev_VPair22Full/Scratch_VPair22Full.thy`, 94 lines: `Ttau`, `Vtau`,
`Dtau`, `AT3`, `Lcof`, `Mcof`, `Kcof`, and lemmas `Lcof_eq`/`Mcof_eq`/`Kcof_eq`/
`KLM_ratio_from_Theta`) but had not reached the actual codimension-4
IFT-lifting argument or created a permanent branch file as of this writing.
**This has not been independently verified by Claude** — check whether it
still builds before relying on it. Paper scope: lines ~4560–5460 of
`../Applied Math/nonemptiness_unified_singlefile_complete.tex`, chain
`cor:vpair22-common` → `prop:vpair22-graph` → `prop:vpair22-elim` (~5016) →
`prop:vpair22-onezero` (~5206) → `prop:vpair22-full` (~5307) →
`cor:vpair22-full`.

**`app:H0res`'s `B1=B2=B3=0` branch — PARTIALLY landed, commit `3bf33f5`.**
`Appendix/AnalyticBridge/D34_H0res_Branch.thy`: `beta_h0`,
`beta_h0_deriv_nonzero_at_zero`, `has_derivative_beta_h0`, `ucoord_h0` +
slot-value lemmas, `B_dip`, `has_derivative_B_dip_x`,
`B_dip_uslot_transversal` — transversality for ONE cut (one triple element
`j`). Independently re-verified by Claude (re-ran the build, hand-checked the
key algebra). **Remaining**: lift this to the joint three-cut (`j=1,2,3`)
codimension-≥3 argument actually needed for `prop:h0res-Bbranch`'s conclusion
— not attempted, needs a `det3`/`Jac3`-style but three-fold rank argument.
The other four `app:H0res` pieces (residue-control for `(a1,a2)`, the `S=0`
branch, two/three-vanishing-cosine branches, lines ~3193–3541 of the paper)
are read/scoped but untouched.

**IMPORTANT — a pre-existing, DISCONNECTED, INCOMPLETE H0res scaffold already
exists**: `Appendix/Nonemptiness_Regnonzero_Appendix.thy` has fully-proven
(zero `proof hole`) generic lemmas (`lem_h0res_Bcuts`, `lem_h0res_a1a2`,
`prop_h0res_meager`, etc.) but (a) that file, and `Nonemptiness_Capstone.thy`
which imports it, are not imported by `Nonemptiness_Robust3.thy` either — a
second instance of the same disconnection pattern as §0 — and (b) its
`prop_h0res_meager` *takes* the meager conclusion as a hypothesis rather than
deriving it, so even if it were wired in, it wouldn't close this branch. Do
not treat that file as evidence this branch is more done than it is.

**The u-slice branch (`prop:uphi-reduce`/`prop:uphi-codim3`/
`cor:uphi-exhausted`) — Codex's own prior work, `D34_UPhi_Branch.thy`:**
Tier 1 (`F_eta`, `real_analytic_on_F_eta`, `F_eta_at_0`,
`F_eta_zeros_nowhere_dense`) is fully proven. Tier 2 has substrate
(`DM_paper_x_slot_1/2/3`, `Phi_par_slot_value`, `Phi_par_parallel_slot_value`,
`ucoord`, `eta_par`, `uphi_E1_deriv_F_eta`, `uphi_scalar_zero_iff`,
`uphi_reduce_pointwise`) with exactly one remaining `proof hole`:
`Phi_par_parallel_slot_F_eta_identification`. Claude reviewed the "soundness
warning" note Codex left about this proof hole (see `NOTES_FOR_CLAUDE.md` and the
diary entry "TO CODEX: reviewed NOTES_FOR_CLAUDE.md's soundness warning") and
believes — **as a considered hypothesis, not a verified fact** — that the
warning is a false alarm caused by the informal side-check conflating
`M1_moment`'s ambient coordinate weight `(x$n)$1` with the c-projected
`ucoord` coordinate. Recommend attempting the proof hole directly via the existing
invariant machinery before treating it as broken.

## 2. Dead end — do not repeat this

**`cor:H12zero`** (the `H12=0,H22≠0` branch's entry corollary, which
`cor:Lambda-closed` depends on) was attempted via `H_par` — contracting both
Hessian indices with `e_par`, mirroring the `Phi_par` fix. This is
**definitively, machine-verifiedly false in general**, not just unresolved.
Full derivation in the diary ("h_par_vslot_zero: DEFINITIVELY RESOLVED
FALSE"), commit `e264093`. Summary: the residual term
`Q := D2cvec_dip(ω)[e_par,e_par]·perp2(c)` was computed in closed form at an
explicit witness (`ω0=(π/4,0)`, `ωs=(3π/4,0)`, `ω=(π/3,π/6)`) and confirmed
nonzero via Isabelle's `approximation` method (rigorous interval arithmetic,
not hand arithmetic): `Q = 23√6/24 − 5√3/4 ∈ (0.18, 0.19)`. Because `Q` is
real-analytic and nonzero at a generic point, it's nonzero on a dense open
set — the hypothesis fails generically, not just at one witness. **Do not
retry the `H_par` (contract-both-indices-with-`e_par`) construction.** A real
fix needs geodesic/Riemannian-normal-coordinate machinery on the sphere,
which doesn't exist anywhere in this project — that's a large, separate
undertaking, not a patch. `cor:Lambda-closed` is on hold pending that or a
different invariant characterization of `H11` entirely.
`Jac3_H12zero_identity`/`Jac3_H12zero_nonzero_criterion` remain in the bridge
(logically valid implications, just practically inapplicable) — don't build
further on them.

## 3. House style / gotchas (still accurate, see `PARALLEL_WITH_CODEX.md` for more)

- **Dev-scratch-then-splice.** New work goes in its own `M5_Dev_<Name>/`
  (session parented on `Applied_Math_D34_Analytic`, `quick_and_dirty=true`),
  tested via `isabelle eval_at` before full builds, then integrated into a
  **permanent branch file** — never edit `D34_Analytic_Bridge.thy` directly if
  someone else might be working in parallel; register new theories as extra
  entries in the existing `Applied_Math_D34_Analytic` session block in `ROOT`
  (a second session rooted at the same directory fails to build — Isabelle
  rejects duplicate session directories).
- **`vec_eq_iff` doesn't auto-apply as a simp rule** in this heap. Use
  `proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix i :: 2 show ...` instead of `simp add: vec_eq_iff`.
- **`has_derivative_mult`/similar composed rules need `has_derivative_eq_rhs`
  wrapping** when the natural RHS (e.g. a product rule's full expansion)
  doesn't syntactically match a simplified target — wrap with
  `has_derivative_eq_rhs[OF ...]` then `(simp add: fun_eq_iff algebra_simps)`.
  Hit repeatedly (G11 session, H12zero session, H0res fork).
- **A tangent direction like `U` in a theorem about x-space derivatives has
  type `(real^2)^'n`, not `real^2`** — don't confuse it with an omega-space
  vector like `ω`/`ω0`/`ωs`. Caught via type-clash error before, but check
  proactively.
- **jEdit**: never open `jedit`/`build` with `-l Applied_Math_D34_Analytic`
  while editing a file that session itself bakes in (`D34_Analytic_Bridge.thy`
  or any of its registered branch theories) — load against the *parent*
  session (`-l Applied_Math_Appendix`) to view/edit live from source.
- **`inv` is algebra-structure syntax** in this merged heap — spell
  `inv_into UNIV` instead.
- **Before assuming existing "complete-looking" infrastructure is load-bearing,
  check what actually imports it.** This has bitten the project twice now
  (`m5_D34_subset_mstarg_residual`'s enlargement, and
  `Nonemptiness_Regnonzero_Appendix.thy`'s disconnected H0res scaffold) — a
  quick `grep -rn "theory_name\|specific_lemma_name"` across the repo to see
  what actually imports/uses a file, rather than assuming a `zero-proof hole` file
  is wired into the real proof, would have caught both faster.

## 4. Coordination

- Don't commit/push work you haven't built and verified yourself
  (`isabelle build`, `BUILD_EXIT=0`) — this project's whole discipline is
  "verify before committing," not "trust a summary."
- `FORMALIZATION_DIARY.md` and `D34_WITNESS_PLAN.md` are append-only logs —
  add dated entries at the end, don't edit others' entries.
- If a Claude session resumes this project later, it will read this file,
  `PARALLEL_WITH_CODEX.md`, and the diary tail to get oriented — keep them
  updated the same way as you go, so the next handoff (in either direction)
  is as accurate as this one tried to be.
