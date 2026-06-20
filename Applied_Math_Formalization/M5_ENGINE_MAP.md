# M5 Engine Map & Frontier (2026-06-19)

Exact inventory of the heap "engine" lemmas available for closing the remaining
M5 cores, plus the precise structural findings about each core. Built to let the
next focused session start without re-discovery. **Verify file:line against
current source before composing — these are point-in-time.**

## Status of the flagship

`F0_dip_nonempty` (`Appendix/Nonemptiness_Robust3.thy`) is sorry-free except the
single stub `meager_rank_deficient_stratum` (M5). M5 assembly is proven in
`M5_Dev/Scratch_m5_skeleton.thy` (green) as an exhaustive excluded-middle cover:

    M5  =  D1 (proven, = heap meager_grad_x_regular_part / M5a)
         ∪ D2 (m5_D2_beamcenter,  STUB)
         ∪ D5 (m5_D5_steersing,   STUB)
         ∪ D34 (m5_D34_residual,  STUB)  =  D3 (phase-collinear) ∪ D4 (Branch-P)

All dev files import `Applied_Math_Appendix.Nonemptiness_Robust2` and build in
~5–20 s on the warm Appendix heap (BUILD_EXIT=0). Build invocation (repo root
`…/Vern_Paulsen_QC`):

    timeout -s KILL 420 Isabelle2025-2/bin/isabelle build -o threads=4 \
      -d Imported_Munkres_Topology \
      -d Verified_Drone_Theory/Applied_Math_Formalization \
      -d Verified_Drone_Theory/Applied_Math_Formalization/M5_Dev_<X> \
      Applied_Math_M5_<X>

## Verified dev files (BUILD_EXIT=0)

| File | Session | Genuine residual sorry |
|------|---------|------------------------|
| `M5_Dev_curvecover` | `Applied_Math_M5_curvecover` | `locus_locally_C1_arc` (core iii) — committed e68046a |
| `M5_Dev_D3fix` | `Applied_Math_M5_D3fix` | `excess_arc_charts_Nn` (+3 mstarg freebies) |
| `M5_Dev_D4fix` | `Applied_Math_M5_D4fix` | `branchP_indep_charts_Nn` (+4 mstarg freebies) |
| `M5_Dev/skeleton` | (no session) | D2, D5, D34 stubs |
| `M5_Dev_gdip2`, `M5_Dev_Kfinite` | — | sorry-free (D2 sub-pieces) |

"mstarg freebies" = `surj_iff_mstarg`, `mstarg_nonzero`, `nowhere_dense_mstarg_zeros`,
`rline_entire_mstarg`: stubbed in dev files (local `mstarg` def), but PROVEN in
Robust3 where the real `mstarg` lives. Sound to consolidate against the real ones.

## Engine inventory (verbatim, decoded)

### regular_value_local_chart — Regular_Value_Theorem.thy:279  ★ GENERAL IFT
The implicit-function/chart keystone. **Codomain `'b` is ARBITRARY euclidean_space**
(the dev-file headers wrongly claimed "HOL-Analysis has no IFT").
```
fixes G :: "('c::euclidean_space × 'b::euclidean_space) ⇒ 'b"  and G' W p
assumes open W,  p∈W,  G p = 0,
  ⋀z. z∈W ⟹ (G has_derivative blinfun_apply (G' z)) (at z),  continuous_on W G',
  surj (blinfun_apply (G' p))
shows ∃U u0 φ g Dφ. open U ∧ u0∈U ∧ φ u0 = p ∧ φ differentiable_on U ∧
  φ`U ⊆ {q∈W. G q = 0} ∧ openin (top_of_set {q∈W. G q=0}) (φ`U) ∧
  homeomorphism U (φ`U) φ g ∧ (∀u∈U. (φ has_derivative blinfun_apply (Dφ u)) (at u)) ∧
  (∀u∈U. range (blinfun_apply (Dφ u)) = {w. blinfun_apply (G' (φ u)) w = 0})
```
NOTE: domain is a PRODUCT `'c × 'b`, not a `vec`. crossTheta:real^2→real needs
real^2 ↔ real×real transport to use this for the curve-cover residual.

### bad_zero_chart — Nonemptiness_Paper.thy:1316  ★ GENERAL (codomain 'b)
The per-zero local chart used inside charts_core_Nn. Fully generic:
`G :: ('c::euclidean_space × 'b::euclidean_space) ⇒ 'b`. Gives the cball-chart
bundle (φ, Dφ, r) at any regular zero q. => the chart-EXTRACTION half of the
"real^3 engine generalization" is mechanical.

### charts_core_Nn — Nonemptiness_Paper.thy:1557  (HARD-TYPED real^2)
```
fixes V::((real^2)^'n) set,  Ω::(real^2) set,  G::(((real^2)^'n) × real^2) ⇒ real^2
assumes open V, V≠{}, open Ω,  regular_value_on G (V×Ω) 0,
  ∃G'. (∀z∈V×Ω. (G has_derivative blinfun_apply (G' z)) (at z)) ∧ continuous_on (V×Ω) G'
shows ∃charts Crit D.
  {x∈V. ∃ω∈Ω. G(x,ω)=0 ∧ ¬(∃Dω. ((λu. G(x,u)) has_derivative Dω) (at ω within Ω) ∧ surj Dω)}
    ⊆ (⋃i. (fst∘charts i)`(Crit i)) ∧
  (∀i x. x∈Crit i ⟶ ((fst∘charts i) has_derivative blinfun_apply (D i x)) (at x within Crit i)) ∧
  (∀i x. x∈Crit i ⟶ ¬ surj (blinfun_apply (D i x))) ∧ (∀i. closed ((fst∘charts i)`(Crit i)))
```
Proof body uses bad_zero_chart (general) + exists_surj_deriv_iff_partial + Lindelof_openin
+ from_nat_into. The real^2 enters via types, exists_surj_deriv_iff_partial, and the
DIMENSION COUNT for "¬ surj x-projection" (lines 1726+, not audited).

### parametric_transversality_meager_planar_config — Appendix/Scratch_planar.thy:10 (also in Nonemptiness_Paper.thy)  ★ PROVEN real^2 transversality→meager
```
fixes V::((real^2)^'n::finite) set, Ω::(real^2) set, G::(((real^2)^'n)×real^2)⇒real^2, G'
assumes open V, V≠{}, open Ω,  ⋀z. z∈V×Ω ⟹ (G has_derivative blinfun_apply (G' z)) (at z),
  continuous_on (V×Ω) G',  regular_value_on G (V×Ω) 0
shows meager {x∈V. ∃ω∈Ω. G(x,ω)=0 ∧ ¬(∃D. ((λu. G(x,u)) has_derivative D) (at ω within Ω) ∧ surj D)}
```

### regular_value_on (DEFINITION) — Parametric_Transversality_Euclidean_Base.thy:25
```
regular_value_on f S y ⟷ (∀x∈S. f x = y ⟶ (∃f'. (f has_derivative f') (at x within S) ∧ surj f'))
```

### regular_value_on_via_x_partial — Appendix/Nonemptiness_Robust1.thy:3204
```
fixes G :: "('a::real_normed_vector × 'b::real_normed_vector) ⇒ 'c::real_normed_vector"
assumes open S,
  ⋀x w. (x,w)∈S ⟹ G(x,w)=0 ⟹ (∃Dj Dx. (G has_derivative Dj) (at (x,w)) ∧
                                 ((λy. G(y,w)) has_derivative Dx) (at x) ∧ surj Dx)
shows regular_value_on G S 0
```
NOTE: gives regularity from a surjective X-PARTIAL. Does NOT apply to the chart
cores directly — on the bad locus the x-partial of gradU is exactly NON-surjective
(the defining bad condition). The Gjoint submersion must mix x- and ω-partials.

### negligible_singular_image_2n — SardNegligible/Sard_Negligible.thy:20
```
fixes f::"(real^2)^'n ⇒ (real^2)^'n",  f'::"(real^2)^'n ⇒ ((real^2)^'n ⇒ (real^2)^'n)"
assumes ⋀x. x∈S ⟹ (f has_derivative f' x) (at x within S),  ⋀x. x∈S ⟹ ¬ surj (f' x)
shows negligible (f`S)
```

### meager_negligible_closed_cover — Parametric_Transversality_Euclidean_Base.thy:1435
```
fixes A::"'a::euclidean_space set"
assumes A ⊆ (⋃n::nat. K n),  ⋀n. closed (K n),  ⋀n. negligible (K n)
shows meager A
```

### has_derivative_gradU_dip_x — Appendix/Nonemptiness_Robust1.thy:3231
x-partial of gradU factors through the moment x-Jacobian:
`∃F::complex^6⇒real^2. bounded_linear F ∧ ((λy. gradU (cvec_dip ω0 ωs) gain_dip y ω)
   has_derivative (F ∘ DM_paper_x x (cvec_dip ω0 ωs ω))) (at x within V)`

### has_derivative_M_paper_x — BlockDet/Moment_Map.thy:565
`((λy. M_paper y c) has_derivative DM_paper_x x c) (at x within V)`

### Finite-zeros lemmas — Appendix/Scratch_g3_asm.thy (also Robust2:2125/2156/2166)
- `finite_affine_int_zeros` (:159): {t∈[lo,hi]. ∃i::int. t = i·c + d} finite for c>0.
- `finite_cos_zeros_interval` (:190): {t∈[lo,hi]. cos t = 0} finite.
- `finite_phase_zeros_interval` (:200): {u∈[lo,hi]. a·cos u + b·sin u = 0} finite for (a,b)≠0.
  (Curve-cover slices are a·cos+b·sin+c=0 — INHOMOGENEOUS; needs a c≠0 extension.)

### implicit_function_theorem — DOES NOT EXIST (project or distribution).
### inverse_function_theorem — Isabelle2025-2 HOL/Analysis/Derivative.thy:3031 (f:'a→'a same space, obtains local homeo + deriv).

## The four remaining cores — difficulty / risk / leverage

1. **locus_locally_C1_arc** (curve-cover, core iii). Local finite C¹-arc cover of
   {crossTheta=0}, crossTheta = crossA(ω1)cos ω2 + crossB(ω1)sin ω2 + crossG(ω1).
   - REGULAR points (∂1 or ∂2 ≠ 0): ONE graph arc via regular_value_local_chart.
     Needs real^2↔real×real transport. Tractable, SOUND.
   - SINGULAR points (∂1=∂2=crossTheta=0): the wall. Needs analytic local-branch
     structure (finitely many branches) — NOT in HOL-Analysis. Or prove this
     specific curve has finite/empty singular set (parameter-dependent; singular
     ⟹ A²+B²=G², A,B affine in cos ω1, G linear in sin ω1). Risk: HIGH non-closure.
   - Leverage: closes core iii only. Soundness risk: LOW (true statement).

2. **excess_arc_charts_Nn (D3)** + **branchP_indep_charts_Nn (D4)** — the SHARED crux.
   Both = codim-3 chart bundle of {Gjoint=(gradU,mstarg)=0} in charts_core_Nn output shape.
   - Part (a) engine→real^3: chart EXTRACTION is mechanical (bad_zero_chart,
     regular_value_local_chart general). BUT the "¬ surj x-projection" conclusion is
     a DIMENSION argument (manifold dim 2N-1 < 2N) that must be re-derived for codom 3
     — audit charts_core_Nn:1726+ before trusting. SOUND if done carefully.
   - Part (b) **regular_value_on Gjoint** — THE crux. D(Gjoint) surjective onto real^3
     at bad zeros, mixing x- and ω-partials (x-partial alone NON-surjective there).
     D4 DROPS det HessU=0, so surjectivity must come from steering nondeg det(Dcvec)≠0
     / γ∦c. SOUNDNESS-SUBTLE (codim bookkeeping = where the 3 prior bugs lived).
   - Leverage: HIGHEST (closes D3+D4). Soundness risk: HIGH if freelanced.

3. **D2 (m5_D2_beamcenter)** — beam-center c=0 meagerness. Deep: M5_Dev_BeamHess is
   871 lines of beam-Hessian machinery (det HessU covariance polynomial, nowhere-dense
   slices). gdip2 (gdip''(π/2)=(16-4π²)/8≠0) + Kfinite proven; the assembly + slice
   nowhere-density (m5_D2_slice_nowhere_dense) still open. Medium risk.

4. **D5 (m5_D5_steersing)** — det(Dcvec)=0 corner via M6 R3/R5 machinery reuse. Medium.

## Recommended sequencing (for a focused next session)

- HIGHEST VALUE but RISKIEST: the shared chart crux (2). Do part (a) first as a
  SOUND, verifiable `charts_core_Nn_gen` (arbitrary 'b) — audit the dim argument —
  then attack part (b) `regular_value_on Gjoint` with the design §7 transversality
  (carefully, with codim truth-gates; this is where soundness bugs hide).
- LOWEST soundness risk, self-contained: core iii (1). Prove the regular case via
  the general IFT (+ real^2↔real×real transport); confront the singular set
  finiteness for THIS curve. Either closes iii or sharpens its residual.
- D2/D5 are independent and can be done in any order.

NONE is a one-liner. Build serially (heap lock). Subagents CANNOT run `isabelle build`
(permission is main-loop only) — the main loop must drive every verification.

## SOUNDNESS FINDINGS (2026-06-19 parallel audit) — READ BEFORE TOUCHING THE CORES

Two latent over-general stubs caught by parallel read-only audit (the project's recurring
failure mode — 3 prior bugs from codim miscounts). Both cores' stated sorries had gaps.

### Core iii (curve-cover) — REGULAR CASES PROVEN (2026-06-20; commits dc12da7, 0e1dc7b)
`crossTheta_local_C1_graph` (φ-graph over ω₁ where ∂₂Θ≠0) PROVEN sorry-free; the symmetric
`crossTheta_local_C1_graph_vert` (χ-graph over ω₂ where ∂₁Θ≠0) + 4 foundation lemmas PROVEN
(built by 2 parallel agents). `locus_locally_C1_arc` now proves BOTH regular orientations at an
interior locus point (CASE A φ, CASE B1 χ). Single residual `sorry` = **∇Θ=0 singular points
(finite — see below) ∪ box boundary**. Next: boundary (clipped/component box-containment, tractable)
+ singular local cover. Detail below was the original (e750e1f) plan; the singular analysis is now the live lead.

### Core iii (curve-cover) — FIXED (e750e1f)
`locus_locally_C1_arc` was FALSE without `kdiff`. If `Ac=Bc=0` (i.e. `kx ω0=kx ωs ∧ ky ω0=ky ωs`)
then `crossTheta ≡ crossG(ω1) ≡ 0`, locus = whole 2-D box, NOT finitely arc-coverable. Added
`hsep: kz ωs ≠ kz ω0` + `kdiff: kx ω0 ≠ kx ωs ∨ ky ω0 ≠ ky ωs` (free downstream; M5 assembly +
Robust3:1001-1002 carry them). WITH `kdiff`: singular set `{crossTheta=0 ∧ ∂1=∂2=0}` ⟹ `A²+B²=G²`,
a degree-≤2 poly in `cos ω1` (leading coeff = `(Ac·kyωs−Bc·kxωs)²+(Ac·kzωs+kxωs)²+(Bc·kzωs+kyωs)²`,
a sum of 3 squares; ≡0 iff `Ac=Bc=0` = ¬kdiff) ⟹ FINITE. NOW CLOSEABLE, ~150-300 lines, NO WALL:
- Build `has_derivative_crossTheta` (∂1,∂2 from crossTheta_separable + bounded_linear_vec_nth + derivative_intros; mirror continuous_on_crossTheta).
- 2 helpers: `finite_cos_eq_zeros_interval` (cos t=κ, |κ|≤1; model finite_cos_zeros_interval) + `finite_inhom_phase_zeros_interval` (a·cos+b·sin=k, |k|≤√(a²+b²); model finite_phase_zeros_interval). The inhomogeneous c≠0 extension.
- Regular case: EXPLICIT graph arc `(λt. t*R axis 1 1 + ψ t *R axis 2 1)`[a,b]`, ψ from arcsin/arccos branch, C¹ via axis-scaleR pasting (mirror cvec_dip smoothness Robust1:742). Do NOT use regular_value_local_chart — its open-U/differentiable_on output doesn't meet the closed-interval/C¹ analytic_arc contract.
- Singular case: r < dist(ω', Ssing\{ω'}); cover by analytic_arc_singleton + ≤2 arcsin-branch graphs per orientation + point-arcs at finitely many turning points.

### Chart crux (D3/D4) — NOT closeable as stated; needs re-architecture
The `Gjoint=(gradU,mstarg)→real^3` regular value is **FALSE unconditionally**: at a bad point with
`det HessU=0 ∧ ¬surj(DM_paper_x)`, the joint Jacobian has rank ≤ 2 < 3 (x-block rank ≤1: moment
drop + `∇ₓmstarg=0` at the Gram-det min; ω-block is 3×2, collapses to rank ≤1 in rows 1-2 when
`det HessU=0`). `M5_Dev_D4charts:41` states outright "nothing forces ¬surj DM ⟹ det HessU=0", so
the degenerate stratum is non-empty. Proving `excess_arc_charts_Nn`/`branchP_indep_charts_Nn`
(D3fix/D4fix) via an unconditional Gjoint submersion = a 4th soundness bug. D4eng quarantines via
`Sigma0` excision but `Sigma0_bad_charts` (D4eng:328) is UNPROVEN, has NO nondeg hypotheses, and
is "not credibly true."
SOUND ROUTE — split the bad set on `det HessU`:
- `det HessU = 0` part: charts via HEAP `charts_core_Nn[G=gradU]` DIRECTLY. Verified bridge
  `not_surj_omega_deriv_iff_detHess_dip` (Robust1:4245): `¬surj(ω-partial gradU) ⟺ det HessU=0`,
  so `{gradU=0 ∧ det HessU=0}` IS charts_core_Nn[gradU]'s bad set. NO generic-codomain engine,
  NO Sigma0. (param=codom=real^2, fits the heap engine as-is. Paper's Phibad=(gradU,det HessU),
  Robust1:4201, is this codim-3 map.)
- `det HessU ≠ 0` part: `{gradU=0 ∧ ¬surj DM ∧ det HessU≠0}` = moment-rank-drop content (gradU
  ω-regular, moment x-irregular). The genuine remaining D-work; relate to D1 = meager_grad_x_regular_part.
NOTE on the engine: `charts_core_Nn_gen` to arbitrary codomain 'b is mechanical EXCEPT (i) re-prove
crit_piece_compact for non-square ω-partial (rank/minor route, or trivial cball-collapse when
DIM(param)<DIM(codom) since ω-partial then never surjective), AND (ii) bad_zero_chart needs
domain=('c×'b)→'b with codom='b=2nd factor, so a real^3 codomain with real^2 param needs a domain
RE-SPLIT (abstract (2N-1)-dim 'c ⊕ real^3) — not free. The det-HessU split AVOIDS all this (uses
the real^2 heap engine directly), so it is the preferred path.
