# M5 D3/D4 Close-Out Roadmap

_Status as of 2026-06-22. The single source of truth for finishing `F0_dip_nonempty`._

## 1. F0 status (oracle-verified)

`F0_dip_nonempty` (`Appendix/Robust3/Nonemptiness_Robust3.thy:3450`) is proven under exactly
`6 ≤ CARD('n)` ∧ `odd CARD('n)`, modulo **exactly two `sorry`s**. Confirmed two ways:
- clean grep: Robust1/Robust2/base/Regnonzero = 0 live sorries; `Nonemptiness_Capstone`'s 6 are
  OFF-path (F0 cites none);
- Isabelle kernel: `thm_oracles F0_dip_nonempty` = `{skip_proof, cooper}` (full chain replays
  `EVAL_EXIT=0`). `cooper` = the sound Presburger decision procedure, not a gap.

The two live sorries:
- **D3**: `m5_D34_D3_collinear` (`Robust3:2412`)
- **D4**: `branchP_indep_charts_Nn` (`Robust3:2512`)

Everything else is sorry-free: D1 (`meager_grad_x_regular_part`, Robust2:2373), D2, D5, the Sard
reduction (`branchP_indep_negligible_closed_cover`, Robust3:2547), the meager capstone
(`meager_rank_deficient_stratum` → `Phi_bad_meager_dip`), feasibility (Slater witness), and
`DM_paper_x_regular_point_exists` (proven at Robust3:495).

## 2. The frontier reduces to ~ONE genuine new lemma

Both remaining cores bottom out at the SAME new mathematics — the **moment-determinant
transversality**:

> Along an IFT critical graph `ω = ω*(x)` (where `gradU = 0`), the moment rank-drop locus
> `{x : mstarg(cvec(ω*(x)), x) = 0}` has positive codimension — equivalently, its x-projection
> chart has a non-surjective derivative, so it is negligible / nowhere-dense.

Prove this once and it feeds **both D3-B and D4**. The only other genuine residual is the
degenerate-critical stratum **D3-A-NSx**.

**Why there is no shortcut (the Gram-det kill):** `mstarg c x = det((transC∘DM_paper_x x c)∘
adjoint(…))` is a Gram determinant, so by Cauchy–Binet `mstarg ≥ 0` everywhere; hence `∇mstarg = 0`
identically on `{mstarg=0}`. So 0 is never a regular value of mstarg — the rank-drop CANNOT come
from a moment/mstarg submersion (the dead "Bug-4"). It must come from the manifold-dimension count
of the bad fibre (the `gradU=0` + moment-rank-drop conjunction, codim ≥ 3 in (x,ω)).

## 3. D3 close-out structure

Sound chain (all `BadXWG` = `gradU = 0` RETAINED; all proven sorry-free in the dev sessions):

```
m5_D34_D3_collinear  (Robust3:2412 — the live opaque sorry)
  ⟸ m5_D34_D3_collinear_fixed        (M5_Dev_D3fix, connector, sorry-free)
  ⟸ collinear_locus_finite_arc_cover (M5_Dev_curvecover, ~3700 lines sorry-free given nsing_all)
  ⟸ excess_arc_projection_meager / excess_arc_negligible_closed_cover / excess_arc_charts_Nn
                                     (M5_Dev_D3proof/Scratch_m5_d3sound_detHess.thy, sorry-free)
       ⟸ RESIDUAL A  (BadXWG_H0_charts_Nn, detHess.thy:233)   — det HessU = 0
       ⟸ RESIDUAL B  (BadXWG_Hn_charts_Nn, detHess.thy:281)   — det HessU ≠ 0
```

Agent decompositions (UNVERIFIED static reasoning — must be re-derived/verified in main checkout):
- **RESIDUAL A** splits into `Sx` (x-partial of the moment map surjective ⟹ chartable by the
  proven `charts_core_Nn`) **+** `NSx` (det HessU=0 ∧ x-partial non-surjective — the smaller
  degenerate-critical residual). Only `NSx` remains genuinely open.
- **RESIDUAL B** = the bridge `gradU_joint_surj_of_detHess` (det HessU≠0 ⟹ joint gradU derivative
  surjective, sound via the ω-Hessian) **+** `BadXWG_Hn_reg_charts_Nn` = the moment-transversality
  core (§2).

### TODO — land the sound reduction in Robust3 (achievable, days)
This replaces the opaque `m5_D34_D3_collinear` sorry with the two precise cores, everything else
machine-checked. Net: D3's 1 opaque sorry → 2 precise sorries + verified scaffold (a trust gain).
1. Port the sound dev layers (detHess det-split + `excess_arc_*`; curvecover arc-cover; d3fix
   connector) into Robust3 (or a new heap theory imported by it). **NEVER** import the UNSOUND
   `BadXW` (gradU-dropped) files: `M5_Dev_CurveEngine`, `M5_Dev_Excess`, `M5_Dev_D3charts`,
   `M5_Dev_D3Sound`, `M5_Dev_D3proof/Scratch_m5_d3proof.thy` (old), `M5_Dev_D3/Scratch_m5_D3.thy`.
2. Discharge `nsing_all` / `hsep` / `kdiff` from the F0 config (ω0 = vector[pi/2,0],
   ωs = vector[0,0]; hsep/kdiff are derived inside F0's proof ~L3468-3471).
3. Replace the bare sorry with the connector proof; keep RESIDUAL A + B (verbatim) as the only new
   sorries.

## 4. D4

`branchP_indep_charts_Nn` (Robust3:2512) — the non-collinear moment-transversality chart, the SAME
moment-determinant transversality as D3-B, over Γ with `¬gamma_par_c`. The only sorry-free dev
"proof" (`M5_Dev_D4eng/Scratch_m5_d4eng.thy:536`) is the dead Bug-4 joint `(gradU,mstarg)→ℝ³`
submersion (vacuous `regular_value_on_Gjoint_off_Sigma`, real content hidden in `Sigma0_bad_charts`)
— **DO NOT consolidate it**. Keep only its sorry-free helpers.

## 5. Reusable asset

`gradU_joint_surj_of_detHess` — det HessU ≠ 0 ⟹ the joint gradU derivative is C¹ + surjective
(SOUND via the ω-Hessian, NOT mstarg). Source: `M5_Dev_MomentSard/Scratch_bridge_check.thy`.
Verification: **PENDING** (eval_at running). Feeds the IFT-applicability of both D3-B and D4's
det-HessU≠0 parts.

## 6. Phase-A asset (proven & committed 2026-06-22)

`differentiable_mstarg_x` (`Scratch_mstargc1.thy:163`) + the six moment 2nd-derivatives
(`Scratch_momentsard.thy`) — the FX half of the joint-C¹ field; a real input to the
moment-transversality lemma.

## 7. Effort

| Item | Effort | Notes |
|------|--------|-------|
| Consolidate the sound D3 reduction into Robust3 | days | mechanical port; arc-cover already proven |
| **moment-determinant transversality** lemma | multi-week | the genuine core; unlocks **D3-B + D4** |
| D3-A-NSx degenerate-critical stratum | multi-week | needs 2-jet/Morse stratification |
| **Total to zero-sorry F0** | **~5–10 weeks** | concentrated in 1–2 genuine new lemmas |

Bottom line: the formalization is complete except for one (reused) piece of genuine
geometric-measure mathematics plus one degenerate stratum. F0 is honestly proven modulo exactly two
precisely-scoped, oracle-verified sorries.
