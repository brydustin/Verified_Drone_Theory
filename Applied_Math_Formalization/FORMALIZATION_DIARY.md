# Formalization Diary — Antenna Feasibility Nonemptiness

A running, dated log of the Isabelle/HOL formalization of the antenna-feasibility
*nonemptiness* theorem. Kept partly as a development record and partly as raw
material for the paper's "formalization notes." Entries are newest-first within a
day; commit hashes refer to the working repo (`antenna-nonemptiness`), mirrored
into the monorepo `Verified_Drone_Theory` under `Applied_Math_Formalization/`.

---

## 2026-05-29 — Diary catch-up + importing higher-order differentiability

### Mea culpa: the diary lapsed

This entry catches up three sessions' worth of work (commits `28846a2`..`a6f5316`)
that landed after the `charts_core_Nn` entry but were never logged here. Going
forward the diary is updated at the end of *every* session, not retroactively.

### What happened since the last entry (reconstructed from git)

- **Moment-map heap (`28846a2` P1.1, `20c7035` P1.2, `1b77582` P1.3).** The
  six-component moment map `M_paper`, its base configuration `x0_paper`/`c0_paper`,
  and the per-term Fréchet-derivative lemmas were factored out of
  `Nonemptiness_Paper.thy` into `BlockDet/Moment_Map.thy` so the expensive
  operator-overload elaboration is paid once at heap-build time.
- **`bigJ` determinant chain (`82baa57`, `66c0e7b`, `ad8e16f`, `f469397`,
  `d01ffdf`, `4192198`).** The `det_A/B/D` row-reduction pieces of the `12×12`
  Jacobian determinant were baked into `Applied_Math_BlockDet`.
- **Sard port (`f9d1110`, `087004b`, `a6f5316`).** `negligible_singular_image_2n`
  — the `(real^2)^'n ≅ real^('n bit0)` transport feeding `baby_Sard` — is now a
  **sorry-free** build theory `SardNegligible/Sard_Negligible.thy`, registered as
  session `Applied_Math_Sard`. Note: this branch needs only **C¹** (a single
  `has_derivative` + non-surjectivity), *not* higher-order differentiability.
- **`chart_zero_projection_meager_stub` (`9a9cc95`)** proved unconditionally —
  closing the fold-zero branch.

### Current `sorry` ledger (verified by grep this session)

- `Nonemptiness_Paper.thy:3650` — `rank_lower_semicont_open_dense_propagation`
  (the C¹ rank-lower-semicontinuity tool feeding `DM_paper_open_dense_surjective`
  → `ZH0surj` → `prop_regnonzero`). **Only C¹.**
- `Parametric_Transversality_Euclidean_Base.thy` — three:
  - `regular_zero_set_projection_local_chart_2d` (line ~373) — **the keystone**:
    regular value ⇒ local smooth chart of the level set.
  - `regular_zero_set_projection_charts_core_2d` (line ~352) — the countable-cover
    assembly built on the keystone.
  - `parametric_transversality_meager_euclidean_stub` (line ~972) — the meager
    conclusion built on the assembly.
- `Regular_Value_Theorem.thy` — **sorry-free**, but **not registered in any
  session/ROOT**. Its theorem `regular_value_local_chart` is the IFT-based engine
  for the keystone: it returns `U, u0, φ, g, Dφ` with `φ differentiable_on U`,
  `φ ` U ⊆ {G=0}`, `openin … (φ ` U)`, `homeomorphism U (φ ` U) φ g`,
  `range(Dφ u) = ker(G'(φ u))`. **Hypotheses: `derG` (Fréchet derivative `G'` as a
  blinfun on `W`) + `contG'` (`continuous_on W G'`, i.e. C¹) + `regp` (`surj G'` at
  `p`).**

### Why we just imported `Higher_Differentiability_Multi`

The keystone is currently stated with only `regular_value_on G (V×Ω) 0`, which
gives a *pointwise* surjective derivative at the zeros but **no continuity of the
derivative**. The IFT engine needs **C¹** (`contG'`). That is precisely the gap
`Higher_Differentiability_Multi` fills:

- `Ck_on 1 G W` (its `Ck_on`/`Ck_at` C¹ notion) ⟹ a continuous blinfun-valued
  derivative on `W` ⟹ discharges `derG` + `contG'`.
- Bridges: `Ck_on_imp_k_times_Fr_on`, `Ck_on_iff_higher_differentiable_on`
  (agreement with the AFP `Smooth_Manifolds.higher_differentiable_on`).

Copied into `HigherDiff/` with its three local deps (`Limits_Higher_Order_Derivatives`,
`Auxiliary_Facts`, `Higher_Differentiability`); registered as session
`Applied_Math_HigherDiff = HOL-Analysis + Smooth_Manifolds`. Builds clean
(`BUILD_EXIT=[0]`). One pre-existing `sorry` in `Higher_Differentiability` ⇒
session kept `quick_and_dirty`.

#### Dependencies imported this session (for the record)

Source: `…/Academic/Isabelle_Stuff/Verified_Numerical_Algorithms_ITP2026/`.
Copied verbatim into `Applied_Math_Formalization/HigherDiff/`:

| File | Imports (after copy) |
| --- | --- |
| `Limits_Higher_Order_Derivatives.thy` | `HOL-Analysis.Analysis` |
| `Auxiliary_Facts.thy`                 | `Limits_Higher_Order_Derivatives` |
| `Higher_Differentiability.thy`        | `Auxiliary_Facts`, `Smooth_Manifolds.Smooth`, `HOL-Analysis.Analysis` (carries 1 `sorry`) |
| `Higher_Differentiability_Multi.thy`  | `Higher_Differentiability`, `Smooth_Manifolds.Smooth`, `HOL-Analysis.Analysis` |

Non-local deps **not** copied (already available): `HOL-Analysis` (Isabelle
dist), `Smooth_Manifolds` (AFP `afp-2026-04-09`, globally registered). UTP /
`ITree_Numeric_VCG` machinery from the source project was deliberately **not**
imported — it is only for imperative program verification, irrelevant here.
New session in `ROOT`: `Applied_Math_HigherDiff in "HigherDiff" = HOL-Analysis +
sessions Smooth_Manifolds`.

### Done this session — the C¹ bridge (`Ck1_C1_Bridge.thy`, sorry-free)

New theory `HigherDiff/Ck1_C1_Bridge.thy` (imports `Higher_Differentiability_Multi`,
added to `Applied_Math_HigherDiff`; whole session `BUILD_EXIT=[0]`). It converts
the higher-diff C¹ notion into the regular-value engine's interface:

- `Dblinfun G z ≡ Blinfun (frechet_derivative G (at z))` — the canonical blinfun
  derivative; `blinfun_apply_Dblinfun` proves the rep is faithful where `G` is
  differentiable (finite-dim ⇒ Fréchet derivative is bounded-linear).
- `Ck1_on_imp_has_derivative_blinfun`: `Ck_on (Suc 0) G W` ⇒
  `(G has_derivative blinfun_apply (Dblinfun G z)) (at z)` for `z∈W`  (= `derG`).
- `Ck1_on_imp_continuous_Dblinfun`: `Ck_on (Suc 0) G W` ⇒
  `continuous_on W (Dblinfun G)`  (= `contG'`). Crux: per-direction continuity of
  `frechet_derivative` (from `Ck_at 1`) ⇒ operator-norm continuity, via
  `continuous_on_blinfun_componentwise` (finite-dim) + `continuous_on_eq`.
- `Ck1_on_imp_C1_interface`: the two packaged in the engine's exact shape.

Lesson (logged): header `text` blocks **before** `theory … begin` cannot resolve
`\<^const>`/`@{thm}` antiquotations — keep the pre-`theory` header plain prose.

**Next:** instantiate `regular_value_local_chart` at `'c := real^'m`, `'b := real^2`,
feed it `Dblinfun` via `Ck1_on_imp_C1_interface` (after adding a `Ck_on 1 G (V×Ω)`
hypothesis to the keystone), and repackage into
`regular_zero_set_projection_local_chart_2d`'s `differentiable_on`/`homeomorphism`
conclusion.

### Done this session — the keystone `regular_zero_set_projection_local_chart_2d`

Discharged the keystone sorry in `Parametric_Transversality_Euclidean_Base.thy`.
Verified: `Applied_Math_Nonemptiness` `BUILD_EXIT=[0]` (14s, reusing the
Base/BlockDet heaps — Munkres/JNF/Perron untouched in the heap).

Design decision: rather than import the higher-diff theory into the (heavy,
Munkres-rooted) Nonemptiness session graph, the keystone now takes the C¹ data in
the engine's **native language** — `fixes G'` + `assumes derG` (blinfun-valued
derivative on `V×Ω`) + `contG'` (`continuous_on (V×Ω) G'`). This keeps
`Smooth_Manifolds` out of the main graph; `Ck1_C1_Bridge.Ck1_on_imp_C1_interface`
is applied later, at the *concrete* call site, to manufacture exactly `derG`+`contG'`.

Proof: `W = V×Ω` open (`open_Times`); `p∈W`, `G p = 0` from `p∈M`; `regp`
(surjectivity of `G' p`) recovered from `regular_value_on` + `derG` via
`has_derivative_unique` (on open `W`, `at p within W = at p`); then a single
`regular_value_local_chart[OF …]` and `blast` (dropping the engine's extra `Dφ`
conjuncts; `unfolding M_def` to match the level set). The lemma as *originally*
stated (only `regular_value_on`, no C¹) was **not provable** — `regular_value_on`
gives a pointwise surjective derivative but no continuity, and the IFT needs C¹;
this is the same gap that forced the C¹ hypothesis onto `charts_core_Nn` (05-27).

Threaded the same `G'`/`derG`/`contG'` through the keystone's only caller,
`countable_chart_cover_of_levelset_2d` (which has no callers of its own, so
propagation stops). Remaining sorries in the file: `charts_core_2d` (369) and
`parametric_transversality_meager_euclidean_stub` (1015).

### Finding: the moment map M_paper *will* need C¹ — but for Paper:3650, not the keystone

Checked whether `Moment_Map.thy`'s base-function derivatives need a C¹ upgrade for
the work just done. **They do not** — the keystone is generic and its concrete `G`
is the *array factor* (`(real^2)^N × real^2 → real^2`), whose C¹-ness comes from
analyticity (`C1_cplx_r2_comp`), not from the moment map.

However, `rank_lower_semicont_open_dense_propagation` (`Nonemptiness_Paper.thy:3650`,
the one open sorry there) is about the moment map `M_paper`. Its current
hypotheses (`deriv` = pointwise `has_derivative` within `V`, `one_regular`) are
**insufficient**: open-density of the surjective stratum rests on lower
semicontinuity of `rank`, which requires `DℱF` to vary *continuously* — i.e. C¹.
So that lemma must gain a continuity-of-derivative hypothesis, and instantiating
it with the concrete `M_paper` then requires `M_paper` to be C¹. Since
`Moment_Map.thy` already computes every per-term Fréchet derivative, proving
`Ck_on 1 M_paper …` there (via `Ck1_C1_Bridge`) is the right next step — necessary
for Paper:3650, and the natural concrete use of the higher-diff theory.

### Done this session — `M_paper` is C¹ (`Moment_Map.thy`, Layer 6, sorry-free)

Added a "Layer 6" to `BlockDet/Moment_Map.thy` proving continuity of the
configuration-derivative. Verified: `Applied_Math_BlockDet` + downstream
`Applied_Math_Nonemptiness` `BUILD_EXIT=[0]`.

Decision (same as the keystone): prove it in **native** `has_derivative`/
`continuous_on` language, *not* via `Ck_on`/`Ck1_C1_Bridge` — because the
derivative `DM_paper_x` is already explicit (Layer 5), so C¹ here is a pure
*continuity* obligation, not a differentiability one, and going through
`frechet_derivative`/`Ck_on` would needlessly drag `Smooth_Manifolds` into the
`Applied_Math_BlockDet` heap. (The higher-diff theory is the right tool when we
must *establish* differentiability; here we already have the derivative.)

Chain: `continuous_on_phase_x` / `continuous_on_d_phase_x` (the phase factor and
its differential are continuous in the base point — `cis ∘ (linear)`); a shared
`moment_cont_intros` intro-set discharges all six per-moment derivative
continuities (`continuous_on_d_{A,M1,M2,M11,M12,M22}_moment_x`) as finite sums of
products of `of_real`-lifted polynomials and the phase; `continuous_on_DM_paper_x_vec`
assembles the `complex^6` vector (via `continuous_on_vec_lambda` + `exhaust_6`);
`continuous_on_Blinfun_DM_paper_x` upgrades to operator-norm continuity
(`continuous_on_blinfun_componentwise`, using `bounded_linear_DM_paper_x` from
`has_derivative_M_paper_x` to make the `Blinfun` rep faithful). Final bundle
`C1_M_paper_x`: `(∀x∈V. (M_paper(·,c) has_derivative blinfun_apply(Blinfun(DM_paper_x x c))) (at x within V)) ∧ continuous_on V (λx. Blinfun (DM_paper_x x c))`
— the `derG`+`contG'` pair for the rank argument.

Needed two extra imports (`HOL-Analysis.Bounded_Linear_Function`,
`HOL-Analysis.Cartesian_Euclidean_Space`). Trap re-logged: a bare `C\<^sup>1` in
prose text (outside a `\<open>…\<close>` cartouche) is parsed as an undefined `\<^sup>`
antiquotation — keep superscripts inside cartouches.

**Next:** prove `rank_lower_semicont_open_dense_propagation` (`Nonemptiness_Paper.thy:3650`),
adding a continuity-of-derivative (C¹) hypothesis and discharging it for the
concrete moment map via `C1_M_paper_x`; that yields `DM_paper_open_dense_surjective`
→ `ZH0surj` → `prop_regnonzero`.

### Plan written down + the density-needs-analyticity finding (P1 arc)

Wrote [P1_PLAN.md](P1_PLAN.md): the moment-map branch P1.1–P1.7 with status, since
the `P1.x` labels previously lived only in commit messages (no tracked plan, no
"P1.4"). What we did this arc (keystone + `M_paper` C¹) is the natural P1.4.
Also confirmed: `bigJ_det = -(5·π⁸)/3`, `bigJ_surj` are **already proven**
(BlockDet, 0 sorry — the 05‑27 "deferred to last" item is done).

**Critical finding (ultrathink).** `rank_lower_semicont_open_dense_propagation`
(P1.6) is **not** provable from C¹: its conclusion forces the surjective stratum
to be *dense* (`V ⊆ closure U`), and the docstring's "openness + one regular point
+ connectedness ⟹ density" is **false** — counterexample: a C¹ map on connected
`ℝ` with derivative non-zero at `0` but `≡ 0` on `[1,2]` has a non-dense surjective
stratum. C¹ gives only *openness*; **density needs real-analyticity** of the
Jacobian. User chose to build the analytic density unconditionally.

**Good news:** the analytic engine is **already built and proven** for the
array-factor branch — `lines_entire_identity` / `lines_entire_slice_nowhere_dense`
(1‑D line-restriction identity theorem via `analytic_continuation`) plus the
`cline_entire`/`rline_entire` closure algebra. So P1.6 is *instantiation*, not
from-scratch building.

### Done this session — moment-map base cases for the entire-line-restriction algebra

Added to `Nonemptiness_Paper.thy` (sorry-free; `Applied_Math_Nonemptiness`
`BUILD_EXIT=[0]`): the closure base cases the moment-map minor needs but the array
factor didn't — `rline_entire_coord` (a single coordinate `(x$n)$k` is affine in
the line parameter ⟹ entire), `cline_entire_phase`, `rline_entire_cos_inner`,
`rline_entire_sin_inner` (`cos`/`sin (c · (x$n))` are `Re`/`Im` of the `cis`-phase).
With `det` = sum-of-products of entries and the existing `rline_entire_add/_mult/_sum`,
the 12×12 Jacobian minor `m*` will be `rline_entire`.

**Next (P1.5, the prerequisite):** the Jacobian identification
`DM_paper_x x0_paper c0_paper = (*v) bigJ`, giving `m*(x0_paper) = det bigJ ≠ 0`
(nontriviality) and `surj` at the base point. Then P1.6 instantiation (steps 1–7
in `P1_PLAN.md`), then P1.7 assembly.

### Done this session — P1.5 arithmetic foundation (base-point phase values)

Began P1.5 (the Jacobian identification `D_x M_paper(x0_paper, c0_paper) = (*v) bigJ`,
`Nonemptiness_Paper.thy`). Established the arithmetic substrate, sorry-free,
`Applied_Math_Nonemptiness` `BUILD_EXIT=[0]`.

Precise statement of the reduction (for the paper): the canonical base
configuration `x0_paper` has six points whose first ("`u`") coordinates are the
equally-spaced angles `u_n ∈ {0, π/3, 2π/3, π, 4π/3, 5π/3}`, and the steering
vector is `c0_paper = (1,0)`. Hence the steering form at point `n` is
`c0_paper · (x0_paper$n) = u_n`, and the phase factor is
`phase c0_paper x0_paper n = cis(-u_n) = cos u_n − 𝚤·sin u_n`. Every entry of the
12×12 Jacobian `D_x M_paper(x0_paper, c0_paper)` is therefore a polynomial in the
base coordinates and in `cos u_n`, `sin u_n` — i.e. expressible through `cos`/`sin`
at these six angles, which are the sixth roots of unity.

Lemmas added (`Nonemptiness_Paper.thy`, after the `x0_paper`/`c0_paper` block):
- `sqrt3_sq`: `sqrt 3 * sqrt 3 = 3` (via `real_sqrt_pow2`).
- `base_trig_values`: the twelve closed forms
  `cos/sin` of `0, π/3, 2π/3, π, 4π/3, 5π/3`
  (`= 1,0; 1/2,√3/2; −1/2,√3/2; −1,0; −1/2,−√3/2; 1/2,−√3/2`). Proved by explicit
  calculational Isar from `cos_add`/`sin_add` and the `π/3` values (`cos_60`,
  `sin_60`), isolating the single `sqrt3_sq` step where `cos(2π/3)` needs
  `(√3/2)² = 3/4`; `5π/3` reuses the `2π/3` values. (Replaced the initial
  one-line `simp` attempts, which were fragile around `√3·√3`.)

### Performance pathology + fix: nested vec-projection under `HMA_Connect`/`Conformal_Mappings`

Building the real-linear transports between `(real^2)^6`/`complex^6` and the
`real^12` of `bigJ` exposed a sharp performance trap, worth recording for the
paper's formalization notes.

- The transports: `transC : complex^6 → real^12`, `transD : real^12 → (real^2)^6`,
  and their inverses, defined by explicit `vector [...]`. `transD_inv` is the only
  one with a **nested** projection `(c$i)$j` (flattening `(real^2)^6` into 12 reals).
- **Symptom:** in `Nonemptiness_Paper` (which imports `Perron_Frobenius.HMA_Connect`
  and `HOL-Complex_Analysis.Conformal_Mappings`) the *definition* of `transD_inv`
  never finishes elaborating — in batch it ran 24 min then died "Run out of store";
  in jEdit it sits purple forever. The single-projection transports are fine.
- **Isolated reproduction:** the identical definitions build in **4 s** when the
  theory imports only `Block_Determinants`; adding `HMA_Connect` +
  `Conformal_Mappings` makes the same `transD_inv` time out. So the cost is the
  *import context* interacting with nested vec-projection elaboration (pinning the
  index types `(c$(i::6))$(j::2)` did **not** help — it is not numeral inference).
- **Fix (architectural):** define the transports (and, next, the Jacobian
  identification) in `BlockDet/Moment_Jacobian.thy`, which imports only the
  `HMA_Connect`/`Conformal_Mappings`-free moment-map theories (`Moment_Map`,
  `Block_Determinants_BigJ`). There the nested projection elaborates in
  milliseconds; the definitions are baked into the `Applied_Math_BlockDet` heap,
  and `Nonemptiness_Paper` merely *uses* the constants (using a constant never
  re-runs its definition's elaboration). Verified: `Applied_Math_BlockDet` +
  `Applied_Math_Nonemptiness` `BUILD_EXIT=[0]`.
- **Proof engineering (separate point):** the transport lemmas reduce each vec
  equality to per-component facts via a *bounded* `exhaust_N` case split
  (`exhaust_12[of i]` + `elim disjE; simp`); a blanket `forall_12`/`vec_eq_iff`
  simp over the nested `vector[...]` also exhausts memory and must be avoided.

`Moment_Jacobian.thy` now contains `transC`/`transC_inv`/`transD`/`transD_inv`
with `linear_*`, `*_inv_left/right`, and `bij_transC`/`bij_transD` (all sorry-free).

**Next within P1.5:** compute `D_x M_paper(x0_paper, c0_paper)` column by column
— for each base point `n` and coordinate `k`, the directional derivative
collapses the moment sums to the single `n`-th term, giving an explicit
`complex^6` vector whose `Re`/`Im` parts (via `base_trig_values`) must match the
corresponding column of `bigJ` — then assemble the 12×12 identification and read
off `surj (DM_paper_x x0_paper c0_paper)` (from `bigJ_surj`) and
`det = det bigJ ≠ 0`.

### Next target (where this resumes)

Discharge `regular_zero_set_projection_local_chart_2d` from
`regular_value_local_chart` by instantiating `'c := real^'m`, `'b := real^2`, and
supplying the missing **C¹** hypothesis via `Ck_on 1 G (V×Ω)`. Concretely:
1. register `Regular_Value_Theorem` (and then `Parametric_Transversality_*`) in a
   session whose base sees both HOL-Analysis and `Applied_Math_HigherDiff`;
2. add a `Ck_on 1 G (V×Ω)` hypothesis to the keystone (mirroring how the C¹
   hypothesis was threaded through `charts_core_Nn` on 05-27);
3. extract `G'` + `continuous_on (V×Ω) G'` + the point-`p` surjectivity from
   `regular_value_on` + C¹, then apply the engine and repackage its conclusion
   into the keystone's `differentiable_on`/`homeomorphism` shape.

---

## 2026-05-27 — The regular-value branch: `charts_core_Nn` from sorry to QED

### Where this fits

The nonemptiness theorem reduces (via Baire category) to showing four "bad" sets
are meager in a nonempty open working set `V`. Two of the four branches are
*regular-value* branches: the bad set is contained in a countable union of
lower-dimensional smooth images, hence Lebesgue-negligible, hence (being closed)
nowhere dense, hence meager. The combinatorial heart of that argument is a single
lemma, `charts_core_Nn`: at a regular value `0` of the parameter map `G`, the set
of base points `x` over which the ω-fibre derivative degenerates is covered by
countably many *closed* chart images on which a projection has everywhere-singular
derivative. Feeding this to a Sard-type negligibility lemma closes the branch.

At the start of the day `charts_core_Nn` was a single `sorry`. By the end it was
proved with no `sorry`, on the back of seven supporting lemmas built and verified
in sequence. This is the spine of the regular-value branches and the most
differential-topology-heavy part of the development.

### What was built, in order

- **`d880ba3` — chart derivative exposed.** The self-contained regular-value
  theorem (`Regular_Value_Theorem.thy`, IFT-based, AFP-targetable) produced a
  chart `φ` of the zero set but did not expose its derivative. We strengthened
  `regular_value_local_chart` to also return `Dφ` as a bounded linear map
  (`blinfun`), together with the key identity `range(Dφ u) = ker(DG_{φ u})`. The
  chart derivative is `h ↦ inv(DF)(h,0)` for the augmented square map `F`; its
  range is exactly the tangent space of the zero set.

- **`cf82b5d`, `5520534` — the C¹ hypothesis.** A subtle but real gap: the chart
  comes from the inverse function theorem, which needs `G` to be **C¹** (a
  *continuous* blinfun-valued derivative), not merely to have a surjective
  derivative at the zeros (which is all `regular_value_on` provides). We added an
  explicit C¹ hypothesis to `charts_core_Nn` and threaded it through the two
  `parametric_transversality_*_complex` lemmas and `prop_regzero`, discharging it
  at the top from the analyticity of the array factor via the reusable
  `C1_cplx_r2_comp` (composition with the bounded-linear `cplx_r2`). The
  redundant differentiability hypothesis `A_smooth` was removed — C¹ subsumes it.
  *Getting the hypotheses exactly right, and no stronger, was a deliberate design
  choice.*

- **`81c359b` — `chart_proj_surj_iff`.** Pure linear algebra: if `range(Dφ) =
  ker(L)` for a surjective `L = DG`, then the `x`-factor projection `fst∘Dφ` is
  surjective **iff** the ω-partial `b ↦ L(0,b)` is. This is the bridge from
  "chart point is regular for the projection" to "ω-derivative is non-degenerate."

- **`21762a0` — `partial_omega_deriv`, `exists_surj_deriv_iff_partial`.** Identify
  the ω-slice derivative of `G` as `h ↦ DG(0,h)` (chain rule on the affine slice
  `u ↦ (x,u)`), and show on an open `Ω` that the abstract "no surjective slice
  derivative exists" condition is equivalent to concrete non-surjectivity of that
  unique partial. This lets the bad set be written cleanly as `fst ` BadZeros`.

- **`a9be237` — `bad_zero_chart`.** Package, per bad zero `q`, the chart together
  with a closed ball `cball u0 r ⊆ U`: on it `φ` is continuous, lands in the zero
  set, carries `Dφ` with `range = ker(DG)`, and `φ`(ball)` is an openin-`M`
  neighbourhood of `q` (the input to Lindelöf).

- **`c1bd9f4` — `crit_piece_compact`.** Each critical piece is compact: on the
  closed ball, the set where the ω-partial (a self-map of `ℝ²`) is non-surjective
  is the zero set of `x ↦ det` of a continuous `2×2` matrix field, hence
  closed-in-the-compact-ball, hence compact. This is what makes the chart images
  *closed* (continuous image of a compact set), which the meager conclusion needs.

- **`581f6b2` — `charts_core_Nn`.** The assembly. Recover the continuous `G'`;
  show the bad set equals `fst ` BadZeros`; obtain a chart bundle at every bad
  zero; skolemise the four chart-data functions through a single tuple-valued
  choice; take a countable subcover of the openin-`M` chart neighbourhoods with
  `Lindelof_openin`; reindex by `from_nat_into`; and discharge the four conjuncts
  — cover, projected-chart derivative as a blinfun, everywhere-singular derivative
  on the critical set, and closedness.

### Two lessons worth recording (and arguably worth a footnote in the paper)

1. **Type-annotate existential and `obtain` binders, always.** An existential
   `∃u0 r φ Dφ. … φ u0 = q … φ u ∈ W …` looks fully determined, but nothing in the
   body forces `type(u0)` to be the chart-domain type `'c`: `φ`'s *domain* is
   unconstrained, because the predicate only ever applies `φ`. Isabelle therefore
   generalizes `u0` to a fresh rigid type variable, and then **no** tactic —
   `blast`, explicit `exI`-witnesses, structured `intro` — can unify a genuine
   `'c`-typed witness against a foreign type variable. The fix is one line:
   `∃(u0::'c) (r::real) (φ::'c⇒'c×'b) (Dφ::…). …`. This cost the better part of an
   afternoon across `bad_zero_chart` and the `exch` step of `charts_core_Nn`. Rule
   of thumb: *if a binder's type is pinned only through a function applied to it,
   annotate it explicitly — function domains do not propagate the constraint.*

2. **Multi-function choice needs an explicit `SOME`, not automation.** Going from
   `∀q∈BZ. ∃u0 r φ Dφ. P q u0 r φ Dφ` to four skolem functions
   `u0f, rf, φf, Dφf` is the axiom of choice with a four-fold codomain. `blast`
   and `metis` cannot perform this higher-order, multi-function skolemization. The
   clean route is a single tuple-valued choice function
   `sk q = (SOME t. P q (fst t) (fst(snd t)) (fst(snd(snd t))) (snd(snd(snd t))))`,
   justified by `someI_ex`, with the four projections defined off it. (As a bonus
   trap: when annotating the tuple's type, `(real^2)^'n × real × …` parses as
   `(real^2) ^ ('n × real × …)` — the vec exponent greedily grabs the whole tuple
   — so the first factor needs its own parentheses, `((real^2)^'n) × real × …`.)

### Status at end of day

`charts_core_Nn` is `sorry`-free, so the regular-value branch
(`parametric_transversality_negligible_complex`,
`parametric_transversality_meager_complex`, `prop_regzero`) is proved modulo
nothing in the chart cover. Three `sorry`s remain in `Nonemptiness_Paper.thy`:

- `chart_zero_projection_meager_stub` — the fold-zero branch (1-D transversality →
  meager), still open;
- `bigJ_det` — the explicit `12×12` Jacobian determinant `det bigJ = -(5·π⁸)/3`,
  deliberately deferred to last;
- `Dx_moment_map_surjective` — surjectivity wrapper that consumes `bigJ_det`.

The fold-*nonzero* branch's analytic input (`dU_cart` nowhere-density via the
entire-line-restriction identity theorem and `lem_Efinite`) was completed in
earlier sessions; what remains there is the non-analytic nontriviality input.
