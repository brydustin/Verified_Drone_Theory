# D3 closure: mathematical sketch (semi-formal, Isabelle-free)

Written 2026-07-12 after a full survey of the current tree, in response to
losing track of "today's dead end" when context was cleared. Purpose: pin
down the *actual* remaining mathematics before writing one more line of
Isabelle. Everything below is plain math; Isabelle constant names are given
in `code font` only as pointers back to the formalization.

## Current status (2026-07-12, end of session 4 -- read this first)

This file has grown to 2000+ lines across many numbered sub-sections
(`§6a`-`§6q`) written by three different contributors (Claude, Codex, the
user) working concurrently. If you are resuming cold, start here, not at
`§1`.

**DONE, verified (0 `sorry`, forced-clean `isabelle build -b -c` rebuild
independently re-checked by Claude 2026-07-12):**

- **D3's rank-1 (`det HessU` has rank exactly 1) residual is CLOSED.**
  `M5_Dev_D3Assembly/Scratch_D3Assembly.thy`
  (`Applied_Math_M5_D3Assembly`)'s `Xi_nonzero_witness_exists` is a fully
  unconditional existence theorem: for any admissible design data (nonzero
  steering determinant, nonzero `cvec_dip`, nonzero `e_par$1`/`gain_dip`,
  `2\<le>CARD('n)`) and any arc tangent `w` with `w$1\<neq>0`, there exists a
  genuinely critical `x` (`gradU=0`) with `\<Xi> x \<omega>0 \<omega>s \<omega> w \<neq> 0` -- i.e. the
  arc's own velocity is NOT in `ker HessU` there. This closes the
  `trans`/`schur` degenerate-residual argument's mathematical content
  (\<section>4's original question). Chain: `R_dip`/`Q_dip` (\<section>6k, general linear
  algebra) + `Xi_single_bump_raw` (\<section>6o, unconditional value formula) +
  Codex's `single_bump_phase_point`/radial-point construction
  (`M5_Dev_D3Xi/Scratch_D3Xi.thy`) + the reconciliation bridge (\<section>6p) +
  `Xi_at_phase_point_closed`/residual bound (\<section>6o/\<section>6q) + a sin-free radial
  variant and Archimedean large-window argument (landed live in jEdit,
  authorship split between the user and Codex, \<section>6q's "Superseded by the
  user continuation" note).

**IN PROGRESS, honestly scoped, NOT yet done:**

- **D3's `HessU\<equiv>0` residual.** \<section>6a showed this stratum is nonempty-but-
  thin. \<section>6j proposed using `Jac3_H0cub` as a rank-3 IFT/vector-cut
  witness; \<section>6m (Codex) found this FAILS by a clean phase-degree argument
  (`T3rad`'s cubic row cannot be manufactured from `H_par`/`Phi_par`/
  `gradU_2`'s own x-derivative rows). Per \<section>6m's own conclusion, the two
  live routes are: (a) a genuinely different third vanishing cut, or
  (b) a countability/isolation argument on the "bad-angle set" (for each
  fixed `t0`, is `{\<omega> : \<exists>x\<in>V. x\<in>D3BadXG_H0core{\<omega>}, HessU(x,\<omega>)\<equiv>0}` countable/
  isolated along the arc?), reusing the ALREADY-unconditional
  `fixed_omega_H0core_chart_core_robust4_all_angles` per-angle result once
  countability is established. `M5_Dev_H0coreArc/Scratch_H0coreArc.thy` has
  the capstone-facing wrapper shape already written; the actual
  countability proof is the open piece. Not touched this session beyond
  Codex's \<section>6m negative result.

- **D4's Branch-P closed-cover core.** Completely separate obligation
  (`branchP_indep_closed_cover_core_all`), untouched before this session.
  Codex's new `M5_Dev_D4Branch/Scratch_D4Branch.thy`
  (`Applied_Math_M5_D4Branch`), verified 0 `sorry`, is a SOUND REDUCTION
  (not a finished proof, and the file says so) of the target down to:
  produce, for every admissible steering set `\<Gamma>`, a countable family of
  local product patches `W_i\<times>\<Omega>_i` covering the retained bad fibre
  `V\<inter>BadXGW(\<Gamma>)`, on each of which `gradU` (jointly in `(x,\<omega>)`) is a
  regular value at `0`. The reduction chain itself (`charts_core_Nn`,
  `negligible_singular_image_2n`, `not_surj_omega_deriv_iff_detHess_dip`)
  is complete and reusable; producing the actual patches on the rank-
  deficient stratum is the new hard target, see Sketch.md \<section>7 below for
  Codex's own detailed writeup.

**Division of labor going forward** (no file conflicts if respected):
`M5_Dev_D3Hess`/`M5_Dev_D3Xi`/`M5_Dev_D3Assembly` are DONE for the rank-1
residual -- do not reopen unless a genuine bug is found. `M5_Dev_H0coreArc`
is the live `HessU\<equiv>0` front. `M5_Dev_D4Branch` is the live D4 front. New
assembly work belongs in fresh leaves per this project's own established
convention (\<section>6j/\<section>6n/\<section>6p), not edits to already-verified upstream
scratch theories.

## 0. Where this sits in the whole proof

`F0_dip_nonempty` (the "feasible configuration set is nonempty" capstone)
is, at the concrete Robust4 design point (`ω0=(π/2,0)`, `ωs=(0,0)`,
`δ=π/4`), reduced to exactly two independent obligations:

- **D3**: `d3_detHess_arc_chart_core_all` — a chart-core property of the
  "degenerate critical" locus (`det HessU = 0`).
- **D4**: `branchP_indep_closed_cover_core_all` — completely untouched,
  separate problem, not discussed further here.

This sketch is only about D3. D3 is **not** a transcription of the paper's
"Case B" appendix — Case B was for `det HessU ≠ 0` and was later found
*unnecessary* for F0 (see `[[verified-drone-nonemptiness]]`). The `det
HessU = 0` stratum handled here is genuinely new mathematics invented by
this formalization effort, not present in the LaTeX source.

## 1. The object being covered

For fixed steering-frame parameters `ω0, ωs` and a set of angles `Γ ⊆
R²`, define the **bad-x set**

    D3BadXG_H0core(Γ) = { x : ∃ω∈Γ.  ∇_ω U(x,ω) = 0
                                    ∧ det Hess_ω U(x,ω) = 0
                                    ∧ c(ω) ≠ 0
                                    ∧ DM_x(x,c(ω)) not surjective
                                    ∧ ∇_x[∇_ω U(·,ω)] not surjective at x }

where `U(x,ω) = gain(ω)·Wc(x, c(ω))` is the array power in direction
`ω`, `c(ω) = cvec_dip(ω0,ωs,ω)` is the wavevector map, and

    Wc(x,c) = Σ_n Σ_p cos(c·(x_n − x_p))              (= |array factor|²)

is a finite trigonometric-polynomial in `x` for **every fixed `c`** — this
fact is the single most useful structural feature of the whole problem and
is used repeatedly below.

`x` ranges over `n`-antenna configurations, i.e. `x ∈ (R²)ⁿ`; `ω ∈ R²` is
the two steering angles (`ω$1` = "theta", `ω$2` = "phi").

**Chart-core** for a set `Γ`, `d3_detHess_arc_chart_core(V, ω0, ωs, Γ)`,
means: `V ∩ D3BadXG_H0core(Γ)` can be covered by **countably many** pieces,
each the image of a closed critical set under a chart whose derivative is
*non-surjective* everywhere on it — the standard "this piece is
topologically small (negligible/meager)" packaging used throughout this
project. `d3_detHess_arc_chart_core_all` demands this for `Γ = γ`, **for
every** C1 arc `γ` (i.e. every `γ = φ([a,b])` with `φ` merely
`C1_differentiable_on`, not real-analytic) contained in the design box.

## 2. Why "for every arc" — and what's already free

`D3BadXG_H0core(γ) = ⋃_{t∈[a,b]} D3BadXG_H0core({φ(t)})`. Every single
fixed-angle slice `D3BadXG_H0core({ω})` **already has an unconditional
chart-core**, proved for literally every angle in the box with **zero**
side conditions:

    fixed_omega_H0core_chart_core_robust4_all_angles:
      0 < ω$1 < π  ⟹  d3_detHess_arc_chart_core(V, ω0, ωs, {ω})

(elementary trig case-split: the two "global factor" scalars
`d3_s1_global_factor`, `d3_s2_global_factor` can't both vanish without
forcing `c(ω)=0`, which is excluded). This is real, finished mathematics —
just not yet *wired* into anything (grep confirms it is never cited
downstream; the diary flags this explicitly as "wiring not yet done").

**The problem is not any single angle. It is assembling a continuum of
already-solved single-angle pieces into countably many pieces.** Since
"bad at angle ω" (`∇_ωU(x,ω)=0`) is generically an isolated condition in
`ω` for fixed `x` (`∇_ωU : R²→R²`, so its zero set is generically
0-dimensional), you cannot just sample countably many angles from `[a,b]`
and hope their fixed-angle bad-sets union to the whole thing — you would
miss any `x` whose *unique* bad angle wasn't sampled. You genuinely need
**local openness in x, uniformly as t varies**, which needs continuity/
differentiability of the bad-locus in `t`, which is where the real content
lives. This is a Lindelöf/compactness argument, and it's already built
(`d3_chart_core_of_Lindelof_H0core_cball_patches` etc.) — but it consumes,
as its raw input, a **local graph of the joint critical set over x**, valid
on an open x-ball, which is where the two live scalar hypotheses come from:

    trans(x,t):  (HessU(x,φ(t)) · Dφ(t))$1 ≠ 0
    schur(x,t):  ∃r. arc_schur_L(...)(x)(r) ≠ 0

`trans` is exactly the condition needed to run the implicit function
theorem on `∇_ωU(x,φ(t))$1 = 0`, solving `t = τ(x)` locally; `schur` is
then the leftover Schur-complement condition needed to cut the *other*
component `∇_ωU(x,φ(τ(x)))$2` transversally in `x`. **At the two arc
endpoints these reduce to the free fixed-angle result above** — no
continuity-in-t is needed there, so `left`/`right` are (mathematically)
already done, only unwired. **On the open interior, `trans`/`schur` are the
entire remaining content of D3.**

*(Aside: there is a second, less-developed candidate architecture,
`d3_chart_core_of_fixed_omega_piece_cover` in `Scratch_Wiring.thy`, phrased
via "functional cuts" instead of a `(x,t)`-graph. I checked whether it
sidesteps the whole `trans`/`schur` difficulty — it doesn't: its own
antecedent `d3pieces` is exactly as unproven, and needs the same local
"openness in x, uniform in t" content. It is a different *packaging*, not
an easier *proof*. Not pursued further here.)*

## 3. What `trans` actually says

`HessU(x,ω) = Hess_ω U(x,ω)` is a 2×2 **symmetric** matrix (Hessian in the
*steering angle*, at fixed antenna position). On the D3 stratum `det
HessU = 0`, so — provided `HessU ≠ 0` (the fully-degenerate `HessU≡0` case
is a separate, excluded branch, presumably handled elsewhere; see open
question in §6) — `HessU` has **rank exactly 1**: `HessU = λ v⊗v` for some
nonzero `v ∈ R²` (its "range direction") and scalar `λ≠0`.

`(HessU·h)$1 = λ v$1 (v·h)`, so:

    trans(x,t) fails  ⟺  v$1 = 0   OR   Dφ(t) ⊥ v  (i.e. Dφ(t) ∈ ker HessU)

The `v$1=0` case is a codimension-1 condition purely in `(x,ω)`, independent
of the arc; it should be handled the same way the `H12=0`/`H0cub`
branches were handled elsewhere in this project (rank-3/Wronskian
witnesses) — **not yet checked whether it's vacuous or genuinely occurs
here**, flagged as open below. The interesting case is the second: **does
the arc's own ω-velocity `Dφ(t)` lie in `ker HessU(x,φ(t))`?**

### The kernel direction is already computed

Work in the orthogonal basis `(e_par(ω), perp2(e_par(ω)))` of ω-space,
where `e_par` is *defined* by `Dc(e_par) = c(ω)` (the ω-direction whose
pushforward under the wavevector map is the wavevector itself — well
defined whenever `det(Dc) ≠ 0`, closed form `e_par = (s2/D, −s1/D)` with
`D = 2·gain(ω)·det(Dc)`, `s1,s2` the "global factor" trig scalars from §2).
In this basis `Scratch_D3Hess.thy` has already, unconditionally, proved:

    H_par(x,ω)  := (HessU·e_par)·e_par
    H_cross(x,ω):= (HessU·e_par)·perp2(e_par)   =  ∂_ω[Φ_par](perp2 e_par)   (a first-derivative identity, free)
    H_perp(x,ω) := (HessU·perp2 e_par)·perp2(e_par)
    H_par · H_perp = H_cross²                     (exactly the det=0 condition, rewritten in this basis)

so `v` (the rank-1 range direction), in `(e_par, perp2 e_par)`-coordinates,
is `(H_par, H_cross)` (up to scale — proportional to `(H_cross,H_perp)`
too, consistent by the identity above), and therefore

    **ker HessU  =  span{ H_cross · e_par  −  H_par · perp2(e_par) }**       (★)

`(★)` is the single load-bearing fact this whole branch is trying to make
usable. `H_par` already has a genuinely closed "radial" form (no leftover
ω-Jacobian second-derivative term):

    H_par = gain(ω)·Wc_dd(x,c;c,c) + [g''(ω$1) − 2g'(ω$1)²/gain(ω)]·(e_par$1)²·Wc(x,c) + gain(ω)·Wc_d1(x,c; D²c(e_par,e_par))

(the last term is the one `Hrad2` strips out; it is the one piece that
does *not* have an obviously-closed radial form, because `D²c(e_par,e_par)`
needs `e_par`'s own closed ratio-of-trig-factors form substituted into the
bilinear `D²c` map — this substitution is exactly the "$-notation
elaboration cost" landmine flagged in `[[isabelle-collab-hygiene]]`, and is
a *formalization* cost, not a *mathematical* obstruction: the algebra is
finite and mechanical, it just must be staged behind `define`s).

`H_cross` similarly decomposes via the general moment formula (derived by
hand in §5 below, using `HessU_dip_entry_moments`):

    HessU(k,l)|_crit = gain·Wc_dd(x,c; Dc(e_k), Dc(e_l))
                      + gain·Wc_d1(x,c; D²c(e_k,e_l))
                      + [g'' − 2g'²/gain]·e_k$1·e_l$1·Wc(x,c)

valid **at any critical point** (`∇_ωU(x,ω)=0` was used to eliminate the
`Dc(e_k)·∇_cWc` cross terms — this is a genuine simplification, not yet
landed in Isabelle, see §5). Setting `k=par,l=perp` gives `H_cross`'s own
closed form the same way.

## 4. The real question, reframed

The literature/diary framing ("does the arc's tangent generically avoid a
moving target as t varies") is the wrong shape to attack, because `φ` is
only C1 — nothing prevents an adversarial `φ` from tracking a smoothly
varying target exactly over a whole subinterval, so no "isolated zeros in
t" argument is available for free, and this is (I believe) the wall the
previous session hit and could not get past.

**But the target — `ker HessU(x,ω)` via `(★)` — depends on `x` as well as
`ω`, and dependence on `x` is *real-analytic*, not merely C1**, because
`Wc`, `Wc_d1`, `Wc_dd` are finite sums of `cos`/`sin` of *linear* functions
of `x` (entire functions of `x`, for each fixed `c`). `H_par(x,ω)` and
`H_cross(x,ω)`, hence the kernel direction `(★)`, are therefore
**real-analytic in `x`, for each fixed `ω`.**

This suggests the right question is not "generic in t" but **"generic in
x, at each fixed t"**:

> Fix `t0`, hence `ω0 := φ(t0)`. Consider the scalar

>     Ξ(x) := (H_cross(x,ω0)·(Dφ(t0)·e_par-component)  −  H_par(x,ω0)·(Dφ(t0)·perp2-e_par-component))

>   i.e. the signed component of `Dφ(t0)` transverse to `ker HessU(x,ω0)`
>   (equivalently: `Dφ(t0)` is *not* in the kernel `⟺ Ξ(x) ≠ 0`; this is a
>   basis-independent, cleaner replacement for testing "component 1" of
>   `HessU·Dφ`, and sidesteps the `v$1=0` degenerate case from §3 for free
>   — `Ξ=0` captures *exactly* "`Dφ(t0)` ∈ ker", nothing more).
>
> Is `Ξ(·)` (a fixed, single real-analytic function of `x`, `t0` frozen)
> **identically zero on the relevant critical-x-set, or does it have
> isolated zeros there?**

If `Ξ(·)` is not identically zero (as a function on the ambient x-space —
or, better, restricted to the D3-critical-x-variety at this `ω0`, which is
itself presumably a real-analytic variety), its zero set is nowhere dense
*by the same `real_analytic_nowhere_dense_zeros` machinery already used
six times over in `D34_Geodesic_Branch.thy`* (Tiers 4–6, `Jac3_*`
witnesses) — meaning: **for a fixed t0, only a topologically negligible
set of x's can have their arc-tangent land exactly in the kernel.** That is
a *much* weaker, and much more plausible, claim than "the whole arc avoids
the kernel" — and it is exactly the shape of claim this codebase already
knows how to prove (build a two-point/Wronskian-style witness showing
`Ξ ≢ 0`, then invoke the standard nowhere-dense-zeros lemma).

**Why this could be enough**: the x's where `trans` genuinely fails (for a
fixed t0) are then isolated points, not an open set — but "isolated" isn't
automatically "harmless" for a *chart-core* argument (which needs local
openness). The natural fallback for those isolated bad points is the
"cubic/isolated-zero" idea already under construction in
`Scratch_D3Hess.thy`: at a bad `(x0,t0)` where `Ξ(x0)=0` but `Ξ` is not
identically zero nearby, a **higher t-derivative** of the same quantity
(the third-order jet along the *straight line* `ω0 + s·w` direction, `w =
Dφ(t0)`, which is what `Wc_cvec_dip_line_third_deriv` +
`gain_dip_line_third_deriv` compute) may still certify a genuine isolated
critical structure good enough to build a (possibly weaker, e.g.
finite-to-one rather than a graph) chart at that single point — this is
plausible but **not yet worked out precisely**; see open question in §6.

This reframing does **not** contradict or discard the honest-remaining-scope
plan already staged in `Scratch_D3Hess.thy` (steps a–e); it *relocates*
where the payoff (Ξ, item d/e) should be aimed: not at "third derivative
saves us when the first-order arc-tangent test fails identically along a
whole sub-arc" (the reading in the diary), but at "third derivative saves
us at the isolated points, fixed t, where the first-order x-analytic test
Ξ(x) has a zero" — a narrower, more tractable target. **This is why I do
not believe today's (lost) dead end was in `Scratch_D3Hess.thy` itself —
its third-derivative jet machinery is reusable either way; what needed
rethinking was the outer logical shape of the argument it feeds into.**

## 5. Concrete next formalization step (recommended)

In priority order:

1. ~~Derive the critical-point-simplified `HessU(k,l)` moment formula~~
   **DONE (2026-07-12): `HessU_dip_entry_moments_crit` + `K_gdip` landed in
   `Scratch_D3Hess.thy` (0 `sorry`, verified via `isabelle eval_at` for the
   whole file), matching §6's hand derivation exactly** — for `k,l::2` and
   critical `x`, `HessU$k$l = gain·[Dc(e_k)·Hc·Dc(e_l) + D²c(e_k,e_l)·∇_cV]
   + K_gdip(ω$1, gain)·e_k$1·e_l$1·V` with `K_gdip θ g = deriv(deriv gdip)
   θ − 2·(deriv gdip θ)²/g`. Two reusable side lemmas landed too:
   `frechet_derivative_gdip_linear` (`frechet_derivative gdip (at t) c = c *
   deriv gdip t`) and `frechet_derivative_gdip_k_omega` (the ω-space 2nd
   derivative of `gdip`'s ω-lift, closing the moment formula's last
   `frechet_derivative`-wrapped term into `deriv(deriv gdip)`). One
   correctness gotcha hit and fixed: `has_field_derivative_imp_has_derivative`
   gives `(*) D` (i.e. `λh. D*h`, **D on the left**) — stating the target
   chain-rule lemma with `λh. h*D` (D on the right) makes `rule` fail to
   unify even though the two are equal by `mult.commute`; match the
   library fact's literal term shape first, commute afterward in `simp`.
   Also: an unquoted `fixes ω :: real^2` (vs `:: "real^2"`) silently breaks
   *all* outer-syntax parsing from that point on with a wildly
   misleading downstream error ("proposition expected, but keyword fixes
   was found" reported at the *next* lemma) — always quote non-atomic
   types in `fixes`. This immediately gives `H_cross` a genuinely closed
   form (mod the `D²c(e_par,perp2 e_par)` term, same residual status as
   `Hrad2`'s own).
2. **Define `Ξ` (§4) and attempt a two-point/Wronskian-style witness that
   it is not identically zero** on a design-point slice — mirroring
   exactly the technique already used for `Jac3_H12rad`/`Jac3_H0cub`
   (`Lambda_rad_ij`/`Lambda_cub_ij` two-bump evaluations). This is new
   computation but a *known recipe*, not new mathematics.
3. ~~Decide whether the isolated-zero fallback needs the cubic jet at all,
   or whether `schur` alone already covers the residual~~ **CHECKED
   (2026-07-12), answer: NO, definitively — see §6c.** `schur` cannot
   substitute for `trans` at points where `trans` fails; the two are
   strictly conjunctive in this architecture, both mathematically and in
   the Isabelle hypothesis structure. **This means the `Ξ`-witness /ansatz
   in step 2 (or the cubic-jet fallback from §4) is not optional — it is
   the only route past isolated `trans`-failures.**
4. ~~Wire `fixed_omega_H0core_chart_core_robust4_all_angles` into
   `left`/`right`~~ **DONE (2026-07-12).** New session
   `Applied_Math_M5_ArcWiring` (`M5_Dev_ArcWiring/Scratch_ArcWiring.thy`,
   parented on `Applied_Math_M5_Wiring` with `Applied_Math_M5_ArcBridge`
   as an extra `sessions` dependency — the previously-deferred heap merge,
   done safely since it's a *new leaf* session, not a rebuild of either
   parent) proves `d3_detHess_arc_chart_core_all_robust4_left_right_free`:
   the arc-bridge capstone at the concrete Robust4 design values
   (`ctr=ω0=(π/2,0)`, `ωs=(0,0)`, `δ=π/4`) with `left`/`right`
   *unconditionally* discharged — only `trans`/`schur` remain as genuine
   hypotheses. 0 `sorry`, `isabelle build -b` clean (`Finished
   Applied_Math_M5_ArcWiring`, 17s). Build command (needed flags are
   non-obvious — two extra `-d` for the vendored AFP/Munkres components,
   plus one `-d` per nested `M5_Dev_*` ROOT dir):
   ```
   isabelle build -b -d . \
     -d <path>/Imported_Munkres_Topology -d <path>/afp-2026-04-09/thys \
     -d M5_Dev_Wiring -d M5_Dev_ArcBridge -d M5_Dev_ArcWiring \
     Applied_Math_M5_ArcWiring
   ```
   Gotcha hit twice while writing the two small `OmegaPF` bound lemmas: (i)
   `blast`/`unfolding` failed silently on a manually-restated conjunction
   using a *fresh* `vector [pi/2,0::real]` term — Isabelle gave its two
   occurrences (component 1 vs 2) unrelated fresh index-type variables
   since nothing pinned them to `real^2`, so the "same" term wasn't
   actually the same term; (ii) `linarith` doesn't know `pi > 0`
   automatically — must feed `pi_gt_zero` explicitly. Fixed by stating the
   bound directly in already-simplified form (`pi/2 - pi/4 ≤ ...`, via
   `simp add: vector_2` applied straight to
   `OmegaPF_component_bounds[OF assms]`) rather than restating the raw
   `vector [...] $ i` term and unfolding afterward.

## 6. Detailed analysis: is `HessU≡0` excluded, and does `Ξ≢0` actually hold?

These two questions are significant enough that deferring them was a
mistake — a hole in either one would silently invalidate §4's whole
reframing. Worked through by hand below (no Isabelle), each to the point
of either a clean resolution or a precisely-scoped remaining computation.

### 6a. Is `HessU ≡ 0` excluded on `D3BadXG_H0core`?

**It is not excluded by the stated hypotheses**, but a direct computation
shows it can only happen on a strictly higher-codimension sub-locus than
`det HessU=0` alone — i.e. it is a genuine but *small* residual case, not
a hole that invalidates the rank-1 picture in §3.

First, confirm the mechanism. `Wc(x,c) = |A(x,c)|²` exactly, where `A(x,c)
= Σ_n cis(−c·x_n)` is the (complex) array factor (`A_cart_def`,
`Wc_eq_cmod_sq`, `U_cart_Wc`) — so `V := Wc(x,c) = 0 ⟺ A(x,c) = 0`, and
`D3BadXG_H0core` (unlike the original `D3BadXG`) does **not** exclude this
(`A_cart ≠ 0` was dropped when the set was enlarged for
`D3BadXG ⊆ D3BadXG_H0core`).

**Step 1 — `V=0 ⟹ ∇_cV=0` automatically.** `V = A·Ā`, so `∇V = (∇A)·Ā +
A·(∇Ā)`; if `A=0` both terms vanish. (Elementary; matches §3's use of
`V=0 ⟹ ∇_cV=0` when simplifying `HessU`'s formula at such a point — no
new machinery, just note it as a corollary of `Wc_d1`'s definition.)

**Step 2 — but `Hc` (the `c`-Hessian of `Wc`) generically does *not*
vanish at a zero of `A`.** By the product rule twice on `f = A·Ā`:

    ∂_i∂_j(AĀ) = (∂_i∂_jA)Ā + A(∂_i∂_jĀ) + (∂_iA)(∂_jĀ) + (∂_jA)(∂_iĀ)
               = 2Re[(∂_i∂_jA)·Ā] + 2Re[(∂_iA)·conj(∂_jA)]

At `A=0` the first term drops, leaving `Hc(i,j) = 2Re[g_i·conj(g_j)]`
where `g := ∇_cA = (∂_1A,∂_2A) ∈ C²`. Writing `g = Re(g) + i·Im(g)`,

    Hc = 2[Re(g)⊗Re(g) + Im(g)⊗Im(g)]

— a sum of (up to) two rank-1 PSD outer products, hence **`Hc ⪰ 0` with
rank ≤ 2, rank exactly 2 unless `Re(g) ∥ Im(g)`** (i.e. `∂_1A/∂_2A ∈ R`, a
codimension-1 condition on `x` in addition to `A=0` itself — `g=0`
identically, a "double zero" of `A`, is the only way to force `Hc=0`
outright, an even more special condition). Since `∂_iA(x,c) = −i·Σ_n
x_n$i·cis(−c·x_n)`, generic `x` (perturbed off any special symmetric
configuration) makes `∂_1A/∂_2A` non-real, so `Hc` generically has full
rank 2 at points where `A=0`.

**Step 3 — assemble.** At a critical point with `V=0` (hence `∇_cV=0` by
Step 1), `HessU`'s moment formula (§3/§5) collapses to just the pure
pullback term:

    HessU(x,ω)|_{crit, V=0} = gain(ω) · Dc(ω)ᵀ · Hc(x,c) · Dc(ω)

(`D²c·∇_cV` and the `V`-proportional term both vanish since `∇_cV=V=0`).
This is the pullback of the (generically rank-2, PSD) quadratic form `Hc`
through the linear map `Dc(ω): R²→R²`. It is the **zero matrix** iff
`range(Dc(ω)) ⊆ ker(Hc(x,c))`. Since `Hc` generically has `ker = {0}`
(full rank 2), this forces `Dc(ω) = 0` as a linear map outright — but
`Dc`'s explicit closed form (`Dcvec_dip_def`, built from `cos/sin` of
`ω$1,ω$2` and the fixed `kx/ky/kz` steering constants) is not the zero map
anywhere in the design box that I can see by inspection (its four entries
don't share a common vanishing locus). **So generically, `HessU≡0` at
`V=0` would additionally require `Hc` itself to be rank-deficient — a
codimension-1 condition on top of `A(x,c)=0`'s own codimension-2 (`A`
complex) — i.e. `HessU≡0` sits on a codimension-≥3 sub-locus of the
already-thin `det HessU=0, V=0` stratum**, not a generic occurrence.

The `V≠0` case is similar or better: forcing `H_par=H_cross=H_perp=0`
simultaneously (3 real conditions, since `det=0` is only 1 of the 3 needed
once `H_par·H_perp=H_cross²` is already assumed) against the "generic"
3-real-parameter family `(Hc, ∇_cV, V)` (subject to only the 2 real
criticality constraints) is again a high-codimension coincidence, not a
generic feature of the stratum.

**Conclusion**: `HessU≡0` is a real but small (positive-codimension, likely
≥3 beyond `det=0`) residual sub-locus of `D3BadXG_H0core`, not excluded by
the stated hypotheses and **not shown empty here** — but the mechanism is
now precise enough to either (i) show it's actually empty at the concrete
Robust4 design point via the same kind of explicit trig computation used
for `d3_s1_or_s2_global_factor_nonzero`, or (ii) if nonempty, peel it off
as its own thin closed sub-case (it would need its own, presumably easy,
chart argument, since `Hc`-rank-deficiency-at-a-zero-of-`A` is itself a
codimension-1 condition with its own transversality). **I looked for, but
could not confirm, that the existing `D34_H0res_Branch.thy`
(`B_dip j x ω ω0 ωs = β(c·x_j)`, a *per-antenna* invariant) already covers
this — its structure (one scalar per antenna index, no visible relation to
`Hc`'s rank) doesn't obviously match the `A=0`-driven mechanism derived
here, so this should be treated as a genuinely open connection, not
assumed.** This is the single item from this section most worth a
dedicated follow-up before deep formalization: pin down at the design
point whether `{HessU≡0} ∩ D3BadXG_H0core` is empty, and if not, whether
it coincides with (or is contained in) whatever `app:H0res` actually is.

### 6a-addendum: the actual architecture, found by re-reading the diary (2026-07-12)

Checked both open connections above against `FORMALIZATION_DIARY.md`
(2026-07-10/11 entries) and `D34_H0res_Branch.thy`'s own header — both
resolve, and the picture is quite different (better, but not free) from
what the hand-derivation above assumed.

**`B_dip`/`D34_H0res_Branch.thy` is confirmed UNRELATED.** Its own header
says it implements *"app:H0res: the B1=B2=B3=0 branch"* — a per-antenna,
Case-B-flavored residual (`beta_h0(t) := cos t − t sin t`, `B_dip j =
beta_h0(c·x_j)`) from a *different* part of the source paper, structurally
unconnected to `Hc`'s rank or `A=0`. Worse: the file's own comment says
this theory is **not even imported by `Nonemptiness_Robust3.thy`** — it is
disconnected from the live `F0_dip_nonempty` causal chain entirely, same
as the abandoned `Nonemptiness_Regnonzero_Appendix.thy`/`Nonemptiness_
Capstone.thy` layer. So: not the right tool, and not live regardless.

**A fixed-angle criterion for `HessU≡0` DOES already exist — `Jac3_H0cub`
(`D34_Geodesic_Branch.thy`, "Tier 6", 2026-07-10)** — proven generically
satisfied (`Jac3_H0cub_nonzero_in_open`) with a concrete Robust4-design-
point witness (`Jac3_H0cub_nonzero_in_open_robust4_witness`, side
condition literally `1/4≠0` since `gdip'(π/2)=0` at that design point —
"hypothesis-free" per the diary). This is real, finished, verified math
for exactly the fixed-`ω` version of the `HessU≡0` sub-case.

**But it was explicitly abandoned for the arc-cover target, and for the
same reason the whole `trans`/`schur` machinery had to be invented.** The
2026-07-11 diary entry "the x-space-only rank-2 reframing... and its
price" states this directly: `Jac3`/`Jac3_H0cub`/the whole geodesic branch
differentiates only in `x`, treating `ω` as an entirely fixed parameter —
just like `fixed_omega_H0core_chart_core_robust4_all_angles` (§2 above),
it proves single-angle regularity, not a chart over a continuum of angles
along a C1 arc. Wiring it up "would have reproven something the simpler
[fixed-angle] ladder already fully closes, not touched the actual
arc-packaging gap" (diary, verbatim). So `Jac3_H0cub` cannot simply be
dropped in as a fix for the `HessU≡0` residual in the arc-bridge target —
it needs its **own** arc-elimination construction, structurally parallel
to `trans`/`schur`, not a reuse of the existing fixed-angle result as-is.

**Net effect on the open question.** This sharpens, rather than resolves,
§6a: `{HessU≡0}∩D3BadXG_H0core` is not shown empty, and there is no
existing shortcut past it in the current architecture — but the raw
fixed-angle building block (`Jac3_H0cub`, with a genericity condition
already proven "hypothesis-free" at the design point) is *stronger* and
*more finished* than the analogous input `trans`/`schur` had to start from
(`fixed_omega_H0core_chart_core_robust4_all_angles` also had zero side
conditions, but `trans`/`schur` themselves — the arc-elimination layer —
needed the whole `Ξ`-witness apparatus in §6d–f to become usable). So the
honest scope of "close the `HessU≡0` residual" is: build a `trans`/`schur`-
style arc-elimination pair for the `HessU≡0` stratum, using `Jac3_H0cub`
as the fixed-angle input the way §5 step 4 used the fixed-angle H0core
result — a real, scoped, but not-yet-started unit of work, comparable in
size to the `Ξ`-witness effort, not a "cheap check."

### 6a-addendum-2: correcting the shape of the fix — it can't literally be `trans`/`schur`-style (2026-07-12)

Worked through what "a `trans`/`schur`-style arc-elimination pair for
`HessU≡0`" would actually have to look like, before committing to build
it — and it can't be literally that shape. Important correction to the
addendum above.

**Why `trans`/`schur` structurally cannot apply to `HessU≡0`.**
`trans(x,t): (HessU(x,φ(t))·Dφ(t))$1 ≠ 0` — if `HessU(x,φ(t))` is the
**zero matrix**, `HessU·Dφ(t) = 0` identically, so `trans` is **always
false**, for every `t`, every arc. Likewise `arc_schur_L`'s formula
divides by exactly this same (now-zero) quantity. So on the `HessU≡0`
sub-locus, `trans` doesn't "fail generically" the way it does on the
rank-1 locus — it fails **unconditionally, by construction**. The whole
`d3_chart_core_all_of_analytic_arc_pointwise_arc_schur_patches` machinery
requires `trans` to hold at *every* interior bad point (§6c already
established this is non-negotiable, no meager-exception carve-out exists
in the current capstone) — so if `{HessU≡0}∩D3BadXG_H0core` meets the
interior of *any* admissible arc, the capstone as stated is simply
**unprovable** via this route, full stop, regardless of any cleverness in
choosing the witness. §5 step 4's fixed-angle building block worked
because `left`/`right` only needed chart-core *at the two isolated arc
endpoints* (no continuity-in-`t` needed there — §2). `HessU≡0` has no
such luxury: it can in principle occur anywhere in the arc's interior.

**So the fix must be a genuinely different chart-core mechanism for this
sub-locus — not an IFT/implicit-function graph in `(x,t)` at all.** The
right model is the *other* pattern already used successfully in this
sketch: fix `t0` (hence `ω0=φ(t0)`), note `Jac3_H0cub`'s target quantity
is **real-analytic in `x`** (same reason `Ξ` was, §4 — it's built from
`Wc`/`Wc_d1`/`Wc_dd`-type trig-polynomial sums), so *for each fixed `t0`*,
`{x : HessU(x,ω0)=0}` is either everything (ruled out generically by
`Jac3_H0cub`'s witness) or **nowhere dense** in `x`, by
`real_analytic_nowhere_dense_zeros` — exactly the `Ξ`-witness's own
mechanism (§6d's opening move), *not* `trans`/`schur`'s IFT-graph
mechanism.

**Correction (checked directly against `Scratch_ArcBridge.thy`): the
Lindelöf-assembly step is NOT missing machinery — it already exists,
generically, and needs no new work.** `d3_chart_core_of_Lindelof_H0core_
cball_patches` (`Scratch_ArcBridge.thy:1797`) is already written
abstractly: it takes, as its *only* hypothesis, a per-bad-point `local`
existential ("some open `(x,t)`-neighbourhood `S`, inside some
`cball x0 ρ × (t0-ε,t0+ε)`, such that the criticality-locus `C` inside
that cball×interval is covered by countably many closed,
non-surjective-derivative charts") and, via the standard
second-countable-space Lindelöf argument (`countable_subcover_of_openin_
cover`, already proven, no side conditions), assembles it into the full
`d3_detHess_arc_chart_core` — with **no reference to `trans`/`schur`, the
IFT graph, or `HessU`'s rank anywhere in its own statement.** `trans`/
`schur` are simply *one* way of discharging that `local` hypothesis (via
`arc_schur_point_open_H0core_cball_patch`); they are not part of the
assembly lemma itself. So what's actually needed for `HessU≡0` is not new
Lindelöf machinery — it's a **new proof of the same `local` existential**,
built from `Jac3_H0cub` + `real_analytic_nowhere_dense_zeros` instead of
the IFT graph. This also corrects the parenthetical claim above that this
is literally the same missing piece as the `Ξ`-witness's own isolated-`x`
fallback (§4's end) — it's the same *reusable assembly step*, but each
needs its *own* `local`-hypothesis proof, since the underlying
real-analytic quantity (`HessU`'s rank-0 zero-set vs. `Ξ`'s zero-set) and
the geometry of "what a good chart looks like near a bad point" differ
between the two cases.

**Revised net effect.** "Close the `HessU≡0` residual" is: prove the
`local` per-bad-point existential that `d3_chart_core_of_Lindelof_H0core_
cball_patches` (already built, generic, reusable) needs — via
`Jac3_H0cub` + `real_analytic_nowhere_dense_zeros`, in the same spirit as
(but not the same lemma as) whatever the `Ξ`-witness's own residual
isolated-`x` fallback (§4's end) will eventually need. Both are genuinely
new, comparably-sized proof obligations that *feed into* the same
existing assembly lemma — not one shared piece of missing infrastructure.
This narrows, rather than merges, the two remaining open items: the
Lindelöf/countable-cover machinery itself needs **no** new work; all the
remaining effort is in producing `local`-style witnesses (via
real-analytic-nowhere-dense-zeros) for each of the two strata.

### 6b. Does `Ξ ≢ 0` actually hold?

Recall (§4, cleaned up): `Ξ(x) := (HessU(x,ω0)·w) · e_par(ω0)`, where
`ω0 = φ(t0)` is the frozen arc angle and `w = Dφ(t0)` is the frozen arc
tangent — a single fixed real-analytic function of `x` alone. By
`HessU_radial_row_decomp`'s bilinear-form shape (equivalently, directly
from the moment formula with `k=par`, `l="w"`, using bilinearity in the
second slot):

    Ξ(x) = gain(ω0)·Wc_dd(x,c0; c0, Dc(w)) + gain(ω0)·Wc_d1(x,c0; D²c(e_par,w))
           + K(θ0)·e_par$1·w$1·Wc(x,c0)

where `c0=c(ω0)`, `θ0=ω0$1`, `K(θ) := g''(θ) − 2g'(θ)²/gain(θ)` (derived
by hand in §5's substitution, re-checked here). This holds **at any
critical `x`** (the substitution used `∇_ωU(x,ω0)=0`).

**A concrete partial computation.** Take the (unconstrained, likely
infeasible w.r.t. antenna separation, but perfectly well-defined)
configuration `x⁰` with **all `n` antennas coincident at the origin**.
Then every pairwise difference `x_n−x_p=0`, so directly from the
definitions: `Wc(x⁰,c)=n²` for all `c`, and `Wc_d1(x⁰,c;·)=Wc_dd(x⁰,c;·,·)
= 0` identically (every term in the defining sums carries a factor of the
vanishing pairwise difference). Substituting:

    **Ξ(x⁰) = K(θ0) · e_par$1(ω0) · w$1 · n²**

This is a strikingly clean answer: at the totally-degenerate baseline, `Ξ`
collapses to a pure scalar depending only on the frozen angle data — no
antenna configuration dependence survives at all. This immediately shows
`Ξ`, as an abstract function on *all* of x-space (forgetting feasibility/
criticality), is **not the identically-zero function**, provided
`K(θ0)·e_par$1(ω0)·w$1 ≠ 0`; each factor is an explicit, checkable
closed-form scalar (`e_par$1`, `w$1` from the arc data; `K(θ)` from
`gdip`'s known closed form) rather than anything x-dependent.

**But this is not yet a valid in-stratum witness**, for two reasons that
must be resolved before this becomes a real proof:

1. **`x⁰` is generally not critical.** Direct computation:
   `∇_ωU(x⁰,ω0)$1 = gain(θ0)·(Dc(e_1)·0) + g'(θ0)·n² = g'(θ0)·n²` and
   `∇_ωU(x⁰,ω0)$2 = gain·(Dc(e_2)·0) = 0`. So `x⁰` is critical at `ω0`
   **iff `g'(θ0)=0`** — plausible at symmetry points (e.g. broadside,
   `θ=π/2`, is a natural candidate for `g'=0` given `gdip`'s presumed
   even symmetry about broadside — not yet checked from `gdip`'s actual
   `gsinc`-based closed form) but **not true for a generic `θ0` ranging
   over the whole arc**, and the arc's `θ0=φ(t0)$1` ranges over the *whole*
   `(0,π)` interval (via `pf`), not just `π/2`. So `x⁰` only witnesses `Ξ`
   at isolated angles at best, not generically along the arc.
2. Even granting (1) at special angles, `x⁰` fails antenna-separation
   constraints, so at best it certifies `Ξ≠0` in a formal, unconstrained
   sense; the actual theorem needs a witness (or nowhere-dense argument)
   over **feasible, separated** configurations.

**What this computation *does* establish, honestly:** `Ξ`'s "leading
behavior" — the part surviving as the antenna configuration degenerates
toward total coincidence — is governed purely by the scalar `K(θ)·e_par$1
·w$1`, with **no cancellation mechanism visible from the array geometry
itself**. This is evidence *for* `Ξ≢0` being the typical case, in the same
spirit as (though weaker than) the two/three-bump Wronskian witnesses
already used for `Λ_rad_ij`/`Λ_cub_ij` elsewhere in this project — but it
is not yet a proof, because it doesn't sit on the critical variety.

**The precise remaining computation** (concrete, bounded, not yet done):
construct a *genuinely critical*, feasible configuration near `x⁰` — e.g.
a symmetric 2-or-3-bump perturbation of the kind already used for
`feasible_witness_exists`/`Upow_at_main` and the `Jac3_*_robust4_witness`
family elsewhere in this project — and check whether `Ξ` evaluated there
still reduces to (or stays close to, by continuity in the perturbation
size) the same `K(θ)·e_par$1·w$1`-dominated leading term, or whether the
*specific* perturbation needed to force criticality (which necessarily
breaks the `x⁰` degeneracy in a `θ`-dependent way) exactly cancels it.
Because criticality is only 2 real constraints and the antenna
configuration space is `2n`-dimensional, there is *a priori* plenty of
room for both to hold simultaneously — but "plenty of room in principle"
is not the same as an exhibited witness, and this is the one honestly
open computation this whole strategy now rests on.

**Net assessment**: neither (6a) nor (6b) invalidates the §4 reframing —
both come out "plausibly fine, small-residual-or-provable" under direct
hand computation rather than "structurally broken." But (6b) in
particular is not yet a proof, and un-doing that is the correct next unit
of work (ahead of any further Isabelle writing), per the recommendation in
§5 — with the added, concrete target: **evaluate `K(θ) = g''(θ) −
2g'(θ)²/gain(θ)` from `gdip`'s actual closed form**, and **build one
explicit critical, separated 2-bump witness and evaluate `Ξ` on it exactly**,
mirroring the `Λ_cub_ij` two-bump recipe.

### 6c. Does `schur` alone cover `trans`'s residual? (checked, 2026-07-12)

**No.** This was checked directly against `Scratch_ArcBridge.thy` — cheap,
as anticipated, and the answer is clean and negative:

- `arc_schur_L`'s own *definition* (`Scratch_ArcBridge.thy:993-1006`) is

      arc_schur_L ... x u
        = (frechet_derivative (gradU-component-1-map) (at x) u)$2
          - (frechet_derivative (...) (at x) u)$1
            * (HessU · Dφ)$2 / (HessU · Dφ)$1

  — it divides *by the `trans` quantity itself*, `(HessU·Dφ)$1`. At a point
  where `trans` fails, this is division by zero; Isabelle's real-division
  convention silently sets that term to `0`, so the formula collapses to
  just the bare `frechet_derivative(...)$2` term — a value with no relation
  to the actual second-order transversality condition. A "nonzero" reading
  of `arc_schur_L` at such a point carries **no proof content**.
- Confirmed at the theorem level: `gradU2_graph_has_derivative_schur`
  (line 1008), the lemma that proves `arc_schur_L` really *is* the
  derivative of `gradU2_graph`, takes `trans` as an explicit, unremovable
  hypothesis (line 1018) — the implicit-function-theorem step
  (`tau_has_derivative`, used inside its proof) needs `trans` just to know
  `τ` is differentiable at all.
- Confirmed at the wiring level: every capstone that consumes `schur`
  (`d3_chart_core_of_pointwise_arc_schur_patches` line 2793,
  `d3_chart_core_of_closed_C1_arc_pointwise_arc_schur_patches` line 3007,
  `d3_chart_core_all_of_analytic_arc_pointwise_arc_schur_patches` line
  3052) requires `trans` **and** `schur` as two separate hypotheses,
  universally quantified over the *same* bad point `q`, and passed
  together into the single local-chart builder
  `arc_schur_point_open_H0core_cball_patch` (line 2835:
  `OF qMset phid phic trans[OF qM] schurq`). There is no case-split
  anywhere in this chain that tries `schur` only where `trans` is absent —
  the architecture is strictly conjunctive, not "trans, else schur."

**Consequence**: the isolated points (fixed `t0`) where `trans` genuinely
fails cannot be patched by `schur` under the current formalization. The
only routes past them are the ones already on the table: (i) show they
don't occur at the design point (rule out `v$1=0` and `Dφ(t0)∈ker HessU`
outright — unlikely to hold arc-wide), or (ii) the `Ξ`-nonvanishing /
nowhere-dense-zeros argument of §4/§6b (isolated-in-x, not isolated-in-t,
so it changes the *shape* of the fallback needed), or (iii) the
cubic/third-derivative jet fallback sketched at the end of §4, which was
proposed precisely because `schur` cannot do this job. **This closes the
last open bullet of §7 with a firm "no shortcut here" — the `Ξ`-witness
computation (§5 step 2 / §6b) is not moot and remains the next real unit
of work.**

### 6d. A concrete single-bump critical witness for `Ξ`, at a generic frozen angle (2026-07-12)

Worked by hand (no Isabelle) in response to "build the critical 2-bump `Ξ`
witness." Result: a genuinely critical, single-bump (not even needing two
bumps!) witness family works at **any** frozen angle `θ0` (not just
`θ0=π/2`), via an asymptotic/IVT argument rather than a closed form — this
is new, and resolves the "not yet a valid in-stratum witness" gap flagged
in §6b, modulo two flagged (not yet checked) genericity side-conditions.

**Setup.** Freeze `t0`, hence `ω0=φ(t0)`, `θ0=ω0$1`, `c0=c(ω0)`,
`w=Dφ(t0)`. Write `g0=gain(θ0)`, `g0'=g'(θ0)`, `g0''=g''(θ0)`,
`K0=K(θ0)`. Let `d_w := Dc(w)`, `e2 := D²c(e_par,w)`, `d_perp := Dc(perp2
e_par)` — all fixed c-space vectors determined by the frozen arc data.
`perp2(v) := (-v$2, v$1)` (`perp2_def`, confirmed against the codebase).

**Single-bump closed forms.** Take `x` with ONE antenna at position `p ∈
R²` and `n1 := N-1` antennas at the origin (simpler than the two-bump
recipe used elsewhere — Ξ is not a row-indexed determinant like
`Lambda_rad_ij`/`Lambda_cub_ij`, so it doesn't need the asymmetry a second
bump provides). Direct enumeration of the `n1²` zero-zero pairs (each
contributing `1`/`0`/`0` to `Wc`/`Wc_d1`/`Wc_dd`), the `2n1` bump-zero
pairs, and the 1 bump self-pair gives, for **any** covectors `d,u`:

    Wc(x,c0)        = n1² + 1 + 2n1·cos φ,        φ := c0·p
    Wc_d1(x,c0,d)   = -2n1·(d·p)·sin φ
    Wc_dd(x,c0,d,u) = -2n1·(d·p)·(u·p)·cos φ

(Sanity check: `p=0` gives `φ=0`, `Wc=n1²+1+2n1=(n1+1)²=N²`, matching §6b's
all-coincident baseline exactly.) Note these hold for **arbitrary** `p`,
unlike the existing two-bump machinery which needed bump displacements
`∝ c` — here `Wc_dd` needs two genuinely different c-space directions
(`c0` and `d_w`, generically independent since `w` need not be `∥ e_par`),
so that constraint would have been fatal; the single-bump sums avoid it
because they only ever multiply two *linear-in-p* factors together, valid
for any `p`.

**Parametrize `p` by `(φ,r)`:** `p = (φ/(c0·c0))·c0 + r·perp2(c0)` — a
valid reparametrization of all of `R²` since `{c0,perp2(c0)}` is an
orthogonal basis (`c0≠0` always, standing hypothesis).

**Criticality, `k=e_par`:** `∇_ωU(x,ω0)·e_par = g0·Wc_d1(x,c0,Dc(e_par)) +
g0'·e_par$1·Wc(x,c0)`, and `Dc(e_par)=c0`, so criticality along `e_par`
is the single scalar equation

    (C1)   F1(φ) := -2n1·g0·φ·sin φ + g0'·e_par$1·(n1²+1+2n1 cos φ) = 0

— depends on `p` **only through `φ`**, since `Wc_d1(x,c0,c0)=-2n1φ sinφ`
and `Wc` also only sees `φ`.

**Criticality, `k=perp2(e_par)`:** `Dc(perp2 e_par)=d_perp`, giving

    (C2)   -2n1·g0·sin φ·[φ/(c0·c0)·(d_perp·c0) + r·(d_perp·perp2 c0)]
            + g0'·(perp2 e_par)$1·(n1²+1+2n1 cos φ) = 0

which is **linear in `r`** once `φ` is fixed, with pivot coefficient
`d_perp·perp2(c0)`.

**The pivot is automatically nonzero.** In the basis `(e_par, perp2
e_par)`, `Dc` sends `(e_par,perp2 e_par) ↦ (c0,d_perp)`; changing back to
the standard basis, `d_perp·perp2(c0) = det([c0|d_perp]) = det(Dc)·
det([e_par|perp2 e_par]) = det(Dc)·|e_par|²` (using `perp2`'s explicit
`(-v$2,v$1)` form for the second determinant). Since `det(Dc)≠0` is
already a standing hypothesis (needed for `e_par` itself to be
well-defined) and `e_par≠0` (as `Dc(e_par)=c0≠0` and `Dc` is then
invertible), **`d_perp·perp2(c0) ≠ 0` always** — so (C2) always has a
unique solution `r=r(φ)` once `φ` is fixed. No new hypothesis needed here.

**Existence of a critical `φ*` with `sin φ*≠0` (IVT argument).** Write
`F1(φ) = -2n1 g0·[φ sin φ - B(φ)]` where `B(φ) := g0'e_par$1/(2n1 g0)·
(n1²+1+2n1 cos φ)` is **bounded** (`|B(φ)|≤C` for a fixed `C` depending
only on the frozen data). Since `φ sin φ` is unbounded and oscillates with
growing amplitude, `h(φ):=φ sin φ - B(φ)` takes arbitrarily large positive
values at `φ=π/2+2kπ` (`sin=1`) and arbitrarily large negative values at
`φ=3π/2+2kπ` (`sin=-1`) as `k→∞`; by IVT `h` (hence `F1`) has a root
`φ*_k` in `(π/2+2kπ, 3π/2+2kπ)` for every sufficiently large `k`, and by
choosing a narrower quarter-period sub-window inside that interval (a
routine refinement of the same pigeonhole/IVT argument — not spelled out
symbol-by-symbol here) one can always find such a root with **both**
`sin φ*_k` and `cos φ*_k` bounded away from `0` by a fixed amount,
independent of `k`. (Honest caveat: ruling out the knife-edge coincidence
where the IVT root lands exactly on a `sin`-zero for *every* `k`
simultaneously is a genuine but non-generic degeneracy in the design
parameters — not fully closed here, flagged in §7.)

**Asymptotic evaluation of `Ξ`.** By the same bilinearity used in §6b,

    Ξ(p) = -2n1 g0 φ cos φ·(d_w·p) - 2n1 g0 sin φ·(e2·p) + K0·w$1·e_par$1·Wc(x,c0)

Substituting `p=(φ/(c0·c0))c0+r·perp2(c0)` and using that, from (C2),
`r(φ) ~ -φ·(d_perp·c0)/((c0·c0)·(d_perp·perp2 c0)) + O(1)` as `φ→∞`
(the bounded `V(φ)`-term in (C2) doesn't grow with `φ`, so `r` is
asymptotically **linear** in `φ` whenever `d_perp·c0 ≠ 0`), the
`φ·cos φ·(d_w·p)` term of `Ξ` picks up a factor `φ·r ~ φ²`, which
**dominates** every other term in `Ξ` (all of which are `O(φ)` or
`O(1)`). Concretely, along the `φ*_k` family with `cos φ*_k` bounded away
from `0`:

    Ξ(p*_k)  ~  2·n1·g0·(d_perp·c0)/((c0·c0))·(d_w·perp2 c0)/(d_perp·perp2 c0) · (φ*_k)² · cos(φ*_k)   as k→∞

a quantity that **grows without bound** and is eventually nonzero for all
large `k`, **provided the three scalar factors `g0`, `d_perp·c0`, and
`d_w·perp2(c0)` are all nonzero.** `g0≠0` is a standing hypothesis
(`gnz`). The other two are genuine open side-conditions:

- `d_perp·c0 ≠ 0`: asks whether `Dc` maps the orthogonal pair
  `(e_par,perp2 e_par)` to another (not-necessarily-orthogonal) pair
  `(c0,d_perp)` that happens to stay orthogonal — no structural reason it
  should, but not yet checked at the design point.
- `d_w·perp2(c0) ≠ 0`: this is exactly "`w = Dφ(t0)` is not parallel to
  `e_par(ω0)`" pushed through `Dc` (if `w ∥ e_par` then `d_w=Dc(w) ∥
  Dc(e_par)=c0`, killing this term) — a genuinely meaningful degenerate
  case (the arc is instantaneously moving exactly along the wavevector
  direction), plausibly non-generic along a C1 arc but not excluded by
  anything proved so far.

**Net assessment.** This is real, new progress on the open question from
§6b: a **generic-angle** (not just `θ0=π/2`), genuinely **critical**
witness family for `Ξ ≠ 0` now exists, via an asymptotic/oscillation
argument rather than a closed-form evaluation — qualitatively different
from (and stronger than) the all-coincident baseline of §6b, which only
worked at the symmetric angle. It is **not yet a complete proof**: two
scalar side-conditions (`d_perp·c0≠0`, `d_w·perp2(c0)≠0`) and one
technical existence refinement (avoiding the `sin`-zero coincidence for
*all* `k`, not just showing infinitely many candidate roots) remain to be
checked or closed off. Formalizing this in Isabelle is a substantially
bigger lift than the moment-formula work in §5 step 1 (it needs a genuine
IVT/oscillation lemma plus careful asymptotic bookkeeping) — recommend
resolving the two side-conditions by hand first (cheap, same style of
computation as `d3_s1_or_s2_global_factor_nonzero`) before committing to
formalizing the IVT argument.

### 6e. Checking the two `§6d` side-conditions by hand (2026-07-12)

Per "check the cheap side-conditions before formalizing the IVT argument."
Explicit formulas at the Robust4 steering constants `Ω0=(π/2,0)`,
`Ωs=(0,0)` (note: distinct from `ω0:=φ(t0)`, the *arc's* frozen angle,
which ranges over the whole design box — this is the same notational
overload already flagged as unavoidable in §6b/§6d, since Sketch reuses
"`ω0`" for the arc angle while the codebase's `cvec_dip ω0 ωs ω` uses it
for the steering reference; I write `Ω0,Ωs` here for the steering
constants to keep the two apart).

**`Dc`'s explicit matrix.** From `Dcvec_dip_def`, writing
`κ=(kx Ω0 - kx Ωs)/(kz Ωs - kz Ω0)`, `λ=(ky Ω0-ky Ωs)/(kz Ωs-kz Ω0)`
(fixed constants), `kx=sinθcosψ,ky=sinθsinψ,kz=cosθ` (`Nonemptiness_Paper.
thy`), at `Ω0=(π/2,0), Ωs=(0,0)`: **`κ=1, λ=0`** exactly (direct
substitution: `kx Ω0=1,ky Ω0=0,kz Ω0=0,kx Ωs=ky Ωs=0,kz Ωs=1`). So at an
arc angle `ω0=(θ,ψ)`, writing `M:=Dc(ω0)`'s matrix:

    M = [ cosθcosψ-sinθ    -sinθsinψ  ]        c0 = ( sinθcosψ+cosθ-1 )
        [ cosθsinψ          sinθcosψ  ]             ( sinθsinψ         )

    det M = sinθ(cosθ - sinθcosψ)   (matches the `s1/s2`-factor flavor of §2/§3)

**Side-condition 1, `d_perp·c0 ≠ 0`: FALSE exactly on `ψ=0`, TRUE
(checked numerically, 2000+ random samples plus explicit algebra) away
from it.** At `ψ=0`: `M12=M21=0` (matrix is **diagonal**), `c0=(sinθ+cosθ
-1, 0)` lies purely along the first axis, hence `e_par=M⁻¹c0` does too,
hence `perp2(e_par)` lies purely along the second axis, hence
`d_perp=Dc(perp2 e_par)` does too — **`c0` and `d_perp` are exactly
orthogonal by this axis-alignment, not by coincidence.** This is a
genuine structural fact at `ψ=0` for these steering constants, not a
generic-vs-isolated coincidence — it holds for **every** `θ` along the
whole line `ψ=0`, confirmed both by the algebra above and by direct
symbolic cancellation (the numerator `s1·P1+s2·P2` computed in §6d
vanishes identically in `θ` when `ψ=0`, verified numerically to double
precision for `θ∈{0.3,...,2.5}`). Away from `ψ=0`, a sweep of 2000 random
`(θ,ψ)` pairs with `θ∈(0.05,π-0.05)`, `ψ∈(0.05,π/4)` (matching the
Robust4 design-box shape) gives **zero** near-zero hits — strong evidence
`d_perp·c0`'s zero set is *exactly* `{ψ=0}`, nothing more.

**This does not kill the witness — it splits into two cases, both still
closeable by the same asymptotic mechanism:**

- **`ψ0 ≠ 0`:** §6d's argument applies unchanged; `d_perp·c0≠0` is now a
  *proven* (not just hoped-for) fact away from the single line `ψ0=0`.
- **`ψ0 = 0`:** the whole problem decouples exactly (`M` diagonal), and
  redoing the criticality solve *directly* in this decoupled frame shows
  `(perp2 e_par)$1=0` *also* holds exactly there, which forces the
  particular part of `r(φ)` to vanish too — so **`r*(φ)=0` exactly** (not
  just bounded/subdominant), a cleaner fact than the generic case, not a
  worse one. Redoing the `Ξ` asymptotics with `r*≡0` gives a *different*
  dominant term, `~ -(2n1g0/C1)·d_w$1·φ²cos φ` (`C1:=sinθ+cosθ-1`,
  `d_w$1` = the **first**, not second, component of `Dc(w)`) — still
  order `φ²`, still unboundedly growing, just gated by a *different*
  scalar condition (`d_w$1≠0`, i.e. `w` not parallel to `perp2(e_par)`,
  which at `ψ0=0` is the direction with `Dc`-image purely along the
  second axis) rather than side-condition 2 below.

So **side-condition 1 is now fully resolved**: nonzero everywhere except
one structural line, which is separately (and comparably easily) covered
by the same mechanism with a swapped genericity condition.

**Side-condition 2, `d_w·perp2(c0) ≠ 0` (`ψ0≠0` case) / `d_w$1 ≠ 0`
(`ψ0=0` case): NOT checked, and structurally different from
side-condition 1 — it is a condition on the *arc data* `w=Dφ(t0)`, not on
the design-point angle alone, so it can't be resolved by a single sweep
over `(θ,ψ)`.** Both forms say the same thing in different coordinates:
"the arc's velocity `w`, pushed through `Dc`, is not parallel to `c0`" —
equivalently (since `Dc(e_par)=c0`) **`w` is not parallel to `e_par(ω0)`
at `ψ0≠0`**, or **`w` is not parallel to `perp2(e_par(ω0))`** at `ψ0=0`.
This is a condition that must hold *for the specific arc and time `t0`
under consideration* — it cannot be "checked at the design point" the way
side-condition 1 was. Two honest options, neither pursued yet: (a) argue
it's non-generic for *any* C1 arc to have its tangent hit exactly one of
these two directions except at isolated `t`'s (plausible but not proved —
same open-ended flavor as the "adversarial C1 arc" worry §4 already
flagged), or (b) note that when it *does* fail, that's precisely the
`v$1=0`-type degenerate case already carried as an open item in §7 (`w ∥
e_par` forces `trans` to reduce to testing `H_par=0` directly, a
genuinely different, not-yet-analyzed sub-case).

**Net assessment.** One of the two `§6d` side-conditions is now fully
closed (with an unexpected but fully-explained and still-tractable
wrinkle at `ψ0=0`). The other reduces to, and does not add new content
beyond, the pre-existing open "is `v$1=0` vacuous" question from §3/§7 —
so no new fundamentally-open question was created by this check, just a
sharper understanding of where the existing open question actually bites.
Recommend formalizing side-condition 1's `ψ0≠0`/`ψ0=0` case split next
(it's now a clean, closed, hand-verified statement — no IVT needed for
*this* part, just the explicit `Dc`-matrix algebra above), and treat the
`v$1=0`/`w ∥ e_par` question as its own dedicated unit of work before
attempting the full IVT witness formalization.

### 6f. Closing the `w ∥ e_par` degenerate case for free (2026-07-12)

The last open item from §6e ("is `v$1=0`/`w∥e_par` vacuous") turns out to
be **mostly free**, not a new hard question — checked by hand just now.

**Key observation.** `Ξ(x) := HessU(x,ω0)[w,e_par]` is *bilinear* in `w`.
If `w ∥ e_par` exactly (the `ψ0≠0` bad case from §6e), then
`Ξ = HessU[e_par,e_par] = H_par(x,ω0)` — **exactly** the radial quantity
already singled out in §3 as having "a genuinely closed radial form."
Recompute its leading asymptotic term directly: setting `w=e_par` in §6d's
`Ξ` formula gives `d_w = Dc(e_par) = c0` — so the first term becomes
`-2n1g0·φcosφ·(c0·p) = -2n1g0·φ²cosφ` (using `c0·p=φ` by *definition* of
`φ`, no dependence on `r` at all!). This is **already** the dominant,
unconditionally-nonzero term identified in §6d/§6e (nonzero whenever
`g0≠0`, `n1>0`, `cos φ*≠0` — all already secured by construction, no new
side-condition). **So `w ∥ e_par` is not a failure case for the witness at
all — it makes the witness computation strictly easier** (the messy
`r`-dependent terms drop out entirely).

**The mirror case, `w ∥ perp2(e_par)` (relevant only at `ψ0=0`, per
§6e).** Here `Ξ = HessU[perp2(e_par),e_par] = H_cross(x,ω0)`, and
`d_w = Dc(perp2 e_par) = d_perp`. Unlike the `H_par` case, `d_perp·p` is
NOT free to grow with `φ` — it's exactly *pinned* by (C2) to the bounded
quantity `g0'·(perp2 e_par)$1·V(φ)/(2n1g0 sinφ)` (that is literally what
(C2) says). So `H_cross`'s leading term is only `O(φ)`, not `O(φ²)` —
this sub-case is **not** closed by the same clean argument and needs its
own (not yet done) check of whether its `O(φ)` coefficient is nonzero.

**Net effect: the residual open case has shrunk to a single, doubly-thin
locus.** The only configuration §6d–§6f's witness does not yet cover is
**`ψ0=0` (the arc angle's second component is exactly `0`) *and*
simultaneously `w ∥ perp2(e_par(ω0))` at that same `t0`** — a
codimension-2-flavored coincidence (one condition on the frozen angle,
one on the frozen tangent, at the *same* instant) rather than the
original, much broader-looking "`w∥e_par` somewhere along the arc" worry.
Recommend treating this sliver as low priority — either bound it away
directly (check `H_cross`'s `O(φ)` coefficient by the same style of
computation), or simply note it as a residual thin case requiring its own
short argument later, and proceed to formalizing the now much more solid
`§6d`–`§6f` picture.

### 6g. The residual sliver: the single-bump witness is EXACTLY zero there, not just unclear (2026-07-12)

Checked the `O(φ)` coefficient flagged in §6f as "not yet done." Result:
**the single-bump witness family gives `H_cross(p)=0 identically** (not
approximately, not just to leading order — every term vanishes exactly)
throughout the doubly-degenerate residual case. This *rules out* the
single-bump construction for this sliver rather than leaving it open, and
identifies exactly why.

**The computation.** At `ψ0=0`, direct substitution into `D2cvec_dip`'s
explicit formula (`Nonemptiness_Robust1.thy:859-872`, with `κ=1,λ=0`) at
`h=perp2(e_par)=(0,C1/M11)`, `h'=e_par=(C1/M11,0)` gives

    D²c(perp2 e_par, e_par)$1 = -h$1(sinθ+cosθ)h'$1 - h$2 sinθ h'$1 = 0

(both terms vanish: the first because `h$1=0`, the second because
`h'$2=0` — cleanly, not by cancellation). Combined with the two facts
already established in §6f (`d_perp·p=0` exactly since `p2=0`, and
`(perp2 e_par)$1=0` exactly), **all three terms of `H_cross`'s moment
formula vanish exactly**, for *every* `φ`, not just asymptotically.

**Why, conceptually (not just algebraically).** At `ψ0=0`, a single bump
on the `c0`-axis (`p=(p1,0)`, forced by criticality — §6e already showed
`r*≡0` there) is a configuration with an exact **mirror symmetry**
(reflection across the axis: every antenna, including the bump, has
second coordinate `0`, hence is fixed by `x$2 ↦ -x$2`). `H_cross` mixes
the `e_par` (even, axis-aligned) and `perp2(e_par)` (odd, off-axis)
directions — it is *parity-odd* under exactly this reflection, so it
**must** vanish on any mirror-symmetric configuration, by symmetry alone,
with no need for the detailed algebra above (which merely confirms it).
This is the *same* phenomenon already documented at the top of §6d for
the *original* two-bump machinery elsewhere in the codebase ("on a single
bump all non-bump rows coincide and `Λ` vanishes identically by that
symmetry... minimal asymmetric family is the two-bump") — it is not a
coincidence, it's the generic reason single-bump/on-axis families fail to
witness "cross" quantities.

**Consequence.** The residual sliver genuinely needs a symmetry-breaking
(at least two-bump, off-axis) witness — mirroring the *existing*
`Lambda_rad_two_bump_witness`/`Lambda_cub_two_bump_witness` recipe
(§6d's opening reference), not a refinement of the single-bump family.
Still assessed as low priority (doubly-degenerate locus: needs `ψ0=0`
*and* `w∥perp2(e_par)` at the same instant) — recorded here mainly so a
future pass doesn't waste time trying to rescue the single-bump
construction for this specific case; the fix, when someone wants it, is
"add a second, off-axis bump," not "look harder at the same family."

### 6h. Formalization progress on the `Ξ`-witness, and a correction to §6d's root family (2026-07-12, session 3)

**Landed in Isabelle (`M5_Dev_D3Hess/Scratch_D3Hess.thy`, `Applied_Math_M5_D3Hess`
session, 0 `sorry`, clean `isabelle build -b`):** the entire "cheap algebraic
layer" §6d recommended resolving before attempting the IVT argument.

- `Xi x ω0 ωs ω w := (HessU(...) *v w) • e_par ω0 ωs ω`, plus
  `Xi_eq_par_cross_combo` (the `H_par`/`H_cross` linear-combination decomposition,
  free from the pre-existing `HessU_radial_row_decomp`), `Xi_at_e_par`
  (`Xi(e_par) = H_par`) and `Xi_at_perp2_e_par` (`Xi(perp2 e_par) = H_cross`) —
  formalizing §4's definition and §6f's two collapse cases exactly.
- `single_bump_double_sum`: the general engine (any raw-vector-even `h`, single
  bump `slot i p`) collapsing a double pair-sum to
  `(1+(N-1)²)·h(0) + 2(N-1)·h(p)`. Instantiated to give `Wc_single_bump`,
  `Wc_d1_single_bump`, `Wc_dd_single_bump` — the three closed forms §6d derived
  by hand, now proven for literally *any* `p` (not just `p ∝ c`), matching the
  hand derivation term-for-term including the `p=0` sanity check.
- `gradU_dip_dot`: the missing bridge between the abstract `gradU` (a `grad_fun`
  THE-value) and the concrete `Wc`/`Wc_d1` closed forms, built from the
  already-proven `has_derivative_U_dip_omega_factored` plus the
  `has_gradient`/`grad_fun` dictionary in `Higher_Differentiability_Multi.thy`
  (`frechet_eq_inner_gradient`, `Fr_diff_imp_gradient_exists`). This was *not*
  needed by any previously-landed lemma (`HessU_dip_entry_moments_crit` and
  friends work entirely with the abstract c-space `Hcmat`/`gradU_c`, never
  descending to `Wc_d1` itself) — genuinely new infrastructure.
- `gradU_dip_dot_e_par_single_bump` and `gradU_dip_dot_perp2_e_par_single_bump`:
  (C1) and (C2) as literal scalar equations on the single-bump family, matching
  Sketch's hand derivation exactly (mod notation).
- `matrix_perp2_pivot_identity` (a hypothesis-free 2×2 linear-algebra identity:
  `(M·perp2 e)•perp2(M·e) = det(M)·(e•e)`, same mechanical-algebra style as
  `HessU_det_via_par_cross_perp`) and `pivot_nonzero` (its instantiation at
  `M = matrix(Dc)`, `e = e_par`, using the existing `Dcvec_dip_e_par`) — proving
  the pivot-nonvanishing fact **unconditionally**, no numerical sweep needed,
  contra §6e's framing of it as merely "checked."

**A genuine error found in §6d's asymptotic argument, while attempting to
formalize the IVT step (Task 4).** Re-derived the large-`φ` root structure of
(C1) directly rather than trusting the hand-wave, and it does not do what §6d
claimed.

(C1) reads `φ sinφ = B(φ)` where `B(φ) := g0'e_par$1/(2n1g0)·(n1²+1+2n1cosφ)`
is *bounded* (§6d's own framing — `|cosφ|≤1`). This is not a minor technical
gap: it is a **hard constraint** on every unbounded root sequence. If
`φ_k → ∞` solves `φ_k sinφ_k = B(φ_k)` with `B` bounded, then `sinφ_k =
B(φ_k)/φ_k → 0` **necessarily** — there is no window-choice or refinement that
avoids this, since it follows directly from boundedness of the right-hand
side. §6d's claim that a root family exists with "both `sinφ*_k` and
`cosφ*_k` bounded away from 0" is **false** for large `φ`, not merely
under-justified.

**Locating the actual root family precisely.** Every large root sits near a
zero of `sin`, i.e. near `φ = Nπ`. Writing `φ = Nπ + t`: `sin(Nπ+t) =
(-1)^N sin t`, so for small `t`, `sin(Nπ+t) ≈ (-1)^N t`, and (C1) becomes
`(Nπ+t)·(-1)^N t ≈ B(Nπ+t)`, giving `t* ≈ (-1)^N B(φ*)/φ*` — so `t*_N =
O(1/N)`, i.e. `φ*_N = Nπ + O(1/N)`. Consequently:

- `cos(φ*_N) = (-1)^N cos(t*_N) → (-1)^N` — genuinely bounded away from 0
  (this part of §6d's claim was directionally right, just for the wrong
  reason: it's forced, not chosen).
- `sin(φ*_N) ≈ (-1)^N t*_N ~ B(φ*_N)/φ*_N = O(1/N) → 0` — genuinely **not**
  bounded away from 0; it vanishes like `1/N`.

**Why this breaks (not just weakens) §6d's `r(φ)` asymptotic.** (C2)'s exact
solution is `r(φ) = [g0'(perp2 e_par)$1·V(φ)/(2n1g0·sinφ) - φ(d_perp·c0)/(c0·c0)]
/ (d_perp·perp2c0)`. §6d dropped the first (`V(φ)/sinφ`) term as "the bounded
`V(φ)`-term [doesn't] grow with `φ`" — but `V(φ)` bounded and `sinφ*_N =
O(1/N)` together give `V(φ*_N)/sin(φ*_N) = O(N) = O(φ*_N)` — **the same
order as the second term**, not negligible. The dropped term was wrong to
drop: `r(φ*_N)` is still `Θ(φ*_N)` (still linear order, so the *shape* of the
downstream `Ξ ~ φ²cosφ` conclusion may well survive), but its **coefficient**
is the sum of *two* `O(φ)` contributions, not the single one §6d computed —
so the genericity side-condition at the end of §6d (`d_w·perp2(c0)≠0`) is
almost certainly not the right nonvanishing condition to check anymore; the
correct one is "the *combined* coefficient (both terms) is nonzero," a
different and not-yet-derived scalar expression.

**Status: §6d/§6e/§6f's qualitative shape (single-bump witness, criticality
reduction, `w∥e_par` collapse) all still stand — only the last step (turning
"`Ξ` grows without bound along *some* root family" into a fully certified
nonvanishing statement) needs to be redone.** Concretely, before writing any
more IVT/asymptotic Isabelle code, someone needs to: (1) solve (C2) for `r(φ*_N)`
*keeping both* `O(φ)` terms (using the precise `t*_N ~ (-1)^N B(φ*_N)/φ*_N`
asymptotic above to evaluate `sin(φ*_N)` to leading order, not just call it
"bounded away from 0"), (2) substitute into `Ξ`'s formula to get the *true*
combined leading coefficient of `φ²cosφ*_N`, and (3) check *that* scalar is
generically nonzero. This is real, self-contained follow-up math, not a
formalization technicality — do it by hand in a `§6i` before touching
Isabelle again, per the standing sketch-before-formalize workflow.

### 6i. Redoing §6d/§6h's asymptotic correctly — an EXACT (not asymptotic) result (2026-07-12, session 3)

Did the follow-up §6h flagged as needed. Result: better than expected — (C1)
being *exact* (`φ sinφ = B(φ)`, not approximate) makes `1/sinφ` substitutable
*exactly* wherever `sinφ≠0`, which collapses `r(φ)` to an **exact** linear
function of `φ` (no `O(1)` residual at all), and the whole computation reduces
cleanly to checking a single fixed scalar `R≠0`. This supersedes §6d's
asymptotic argument entirely — no asymptotic bookkeeping is needed at all,
only an exact algebraic substitution plus one root-existence fact.

**Step 1 — `r(φ)` is exactly linear in `φ`, at any root of (C1) with `sinφ≠0`.**
From (C2), `r = [N_r1 - N_r2]/D_r` with `N_r2 = φ(d_perp·c0)/(c0·c0)` (exact),
`D_r = d_perp·perp2(c0)` (the pivot — **exactly** `det(Dc)·(e_par·e_par)` by
`pivot_nonzero`, §6d/now formalized, unconditionally nonzero), and
`N_r1 = g0'(perp2 e_par)$1·V(φ)/(2n1g0·sinφ)`. Since `B(φ) = g0'e_par$1·V(φ)/(2n1g0)`
*by definition* and (C1) says `φ sinφ = B(φ)` **exactly**, `1/sinφ = φ/B(φ)`
exactly (wherever `sinφ≠0`), so

    N_r1 = φ · (perp2 e_par)$1 · V(φ) · g0' / (g0' e_par$1 · V(φ))
         = φ · (perp2 e_par)$1 / e_par$1          (V(φ), g0' cancel EXACTLY)

provided `e_par$1≠0` and `V(φ)≠0`. So `r(φ) = φ·Q` **exactly**, where

    Q := [ (perp2 e_par)$1/e_par$1 - (d_perp·c0)/(c0·c0) ] / (det(Dc)·(e_par·e_par))

is a **fixed scalar** (depends only on the frozen angle `ω0`, not on `φ` at
all — no `+O(1)` term, unlike §6d's version).

**Step 2 — `Ξ(p)`'s three terms, evaluated exactly along any root of (C1).**
`d_w·p = φ·[(d_w·c0)/(c0·c0) + Q·(d_w·perp2c0)] =: φR` (exactly linear, same
mechanism). Substituting into §6d's `Ξ(p) = -2n1g0φcosφ(d_w·p) -
2n1g0 sinφ(e2·p) + K0w$1e_par$1V(φ)`:

- Term 1: `-2n1g0φcosφ·(φR) = -2n1g0R·φ²cosφ` — exact, no approximation.
- Term 2: `e2·p = φS` similarly (`S` another fixed scalar), so term 2
  `= -2n1g0·Sφ·sinφ = -2n1g0S·B(φ)` (using `φsinφ=B(φ)` exactly again) — this
  is **bounded** (§6d's own point that `B` is bounded, correctly used this
  time on a term where it actually applies), hence genuinely negligible
  against `φ²`.
- Term 3: `K0w$1e_par$1V(φ)` — bounded (`V=Wc` is bounded), negligible.

So **`Ξ(p) = -2n1g0R·φ²cosφ + O(1)` exactly** (not `+O(φ)` as one might fear
from §6h's worry — the `1/sinφ` blowup exactly cancels against the
`sinφ→0` factor multiplying it in term 2, leaving only a bounded residual).
`R` is a single fixed scalar:

    R := (d_w·c0)/(c0·c0) + Q·(d_w·perp2c0)

**Step 3 — what's left.** Two independent things, both strictly easier than
what §6d/§6h were staring at:

1. **Root existence**: a sequence `φ*_N → ∞` solving (C1) exactly, with
   `cos(φ*_N)` bounded away from 0. This is now a clean, self-contained IVT
   claim with NO side-condition on `sinφ*_N` needed (§6h's worry about
   needing `sinφ*_N` bounded away from 0 was based on the *wrong* — now
   corrected — `r(φ)` formula; the exact formula has no such requirement).
   Sketch: for the window `φ ∈ [Nπ-π/4, Nπ+π/4]`, `h(φ):=φsinφ-B(φ)`
   satisfies `h(Nπ-π/4) → -∞·sign` / `h(Nπ+π/4)→+∞·sign` (opposite signs,
   `B` bounded) for `N` large, hence IVT gives a root `φ*_N` in the open
   interval, where `|cos(φ*_N)| = cos(t*_N) ≥ cos(π/4) = √2/2` throughout the
   whole window (shown in §6h) — no need to locate `t*_N` more precisely
   than "somewhere in the window."
2. **`R ≠ 0`**: a single fixed-scalar genericity check, same style/cost as
   `d3_s1_or_s2_global_factor_nonzero` or §6e's `d_perp·c0` sweep — not yet
   done, but cheap and mechanical (substitute the Robust4 `Dc`/`e_par` closed
   forms from §6e, evaluate `Q` then `R`). Recommend doing this numeric/
   algebraic check next, by hand, before any further Isabelle IVT work — it
   could in principle vanish on a sub-locus the same way `d_perp·c0` did at
   `ψ0=0`, and it's far cheaper to find that out by hand than mid-proof.

**Net effect**: §6d's original "asymptotic bookkeeping" fear is now moot —
the corrected computation is exact, not asymptotic, so there is no error
term to bound and no `O(1)` vs `O(φ)` ambiguity left anywhere. The remaining
work is exactly two independent, well-scoped pieces: an IVT existence lemma
(root family, cos bounded away from 0 — genuinely simpler than §6d's version
since it drops the sin-bounded-away requirement entirely) and one scalar
nonvanishing check (`R≠0`, not yet done). Recommend checking `R≠0` by hand
first (cheap), then formalizing the IVT existence lemma.

### 6j. HessU≡0 arc-elimination: the local rank-3 witness (2026-07-12, Codex)

This is the hand derivation for the `HessU≡0` residual before touching
Isabelle. It corrects one tempting but wrong simplification: the
`Jac3_H0cub` row involving `T3rad` is a derivative row, not a third
level-set equation. The level-set equation that vanishes on the
`HessU = 0` fibre is a Hessian scalar, naturally `H_par = 0` (or a
row-equivalent corrected Hessian scalar). `T3rad` enters only after
row-reducing the derivative of that Hessian scalar using the already
proved stratum dictionaries.

**Local data and the three x-directions.** Fix a bad point
`q = (x*,t*)`, set `ω* = φ t*` and `c* = cvec_dip ω0 ωs ω*`. Before any
rank argument, shrink the t-neighborhood so the steering determinant,
`gain_dip`, and `cvec_dip` stay nonzero there. This is the same local
nonzero-gain/nonzero-steering-determinant move used elsewhere: the
quantities are continuous, and at a D3 point the bad-set assumptions plus
the Robust4 box side conditions give the needed nonzero values.

The three coordinate directions are exactly the columns appearing in
`Jac3_H0cub`:

    u1 = slot i c*
    u2 = slot j c*
    u3 = slot k (perp2 c*)

with `i ≠ j`. These are not arbitrary coordinates. The `u1,u2` columns
are radial c-slot motions in two antenna indices, and `u3` is the
perp-slot motion that supplies the nonzero `gradU_2` row while the
`Phi_par` and cubic radial rows have zero perp-slot entries
(`Phi_par_perp_slot_zero`, `T3rad_slot_perp_zero`).

**The cut map.** The correct arc-level map is joint in `(x,t)`, not a
fixed-angle map:

    F(x,t) =
      ( Phi_par x (φ t) ω0 ωs,
        vec_nth (gradU (cvec_dip ω0 ωs) gain_dip x (φ t)) 2,
        H_par x (φ t) ω0 ωs )

or the same third row after subtracting fixed, t-dependent multiples of
the first two rows. For a `HessU = 0` bad point, `F(x,t)=0`: the first
row is `Phi_par_zero_of_gradU_zero`, the second is the second component
of `gradU = 0`, and the third is `H_par_zero_of_HessU_zero`.

The fixed-angle-only map `x ↦ (Phi_par, gradU_2, H_par)` is insufficient
for the arc lemma, because the local object is the projection of a
zero-set in `(x,t)`. Treating `t` as a free parameter is the essential
move.

**What still has to be proved before `Jac3_H0cub ≠ 0` gives the needed
rank.** At `(x*,t*)`, restrict `D_x F` to the three columns
`(u1,u2,u3)`. The first two rows are already the first two rows of
`Jac3_H0cub`. The third row is the derivative of `H_par`, not literally
the derivative of `T3rad`; the intended row reduction is:

    D_x H_par  ≡  gain_dip(ω*) · D_x(T3rad · c*)        modulo
                  span{D_x Phi_par, D_x gradU_2}

on the `gradU = 0 ∧ HessU = 0` stratum, after using
`Phi_par_radial_dictionary`, `radial_level1_of_gradU_zero`, and
`radial_level2_of_HessU_zero`.

Do not treat that equivalence as established yet. Expanding
`H_par_radial_dictionary` gives, with
`A = gdip'(ω$1)·e_par$1`, `B = gdip''(ω$1)·(e_par$1)^2`,
`g = gain_dip ω`, and `d2 = D2cvec_dip(e_par,e_par)`,

    H_par = B·Wc + 2A·Wc_d1(c) + g·Wc_d1(d2) + g·Wc_d2(c,c).

Differentiating in x clearly produces the desired cubic row from
`g·D_x Wc_d2(c,c)`, but it also produces lower-order rows
`D_x Wc`, `D_x Wc_d1(c)`, and `D_x Wc_d1(d2)`. The last one should be
reducible using the local basis `{c, Dcvec_dip(axis 2)}` (this is exactly
where the nonzero steering determinant/`Knz` side condition enters), and
`D_x Wc_d1(c)` is removed by the `Phi_par` row. The remaining check is
whether the `D_x Wc` coefficient cancels after this decomposition; if it
does not, the third row must be a corrected Hessian scalar rather than
raw `H_par`.

So the first concrete formal/mathematical lemma in the new leaf is the
exact row-reduction statement, including the coefficients. Once that
lemma is in place, `gain_dip(ω*) ≠ 0` converts
`Jac3_H0cub x* ω* ω0 ωs i j k ≠ 0` into invertibility of the 3-by-3 matrix

    D_(a,b,d) F(x* + a u1 + b u2 + d u3, t*) |_(0,0,0).

Equivalently, `D_x F(x*,t*)` is surjective onto `R^3` with an explicit
right inverse supported on the three selected slot directions.

**IFT shape.** Decompose x-space as

    X = P ⊕ span{u1,u2,u3}

where `P` is any fixed linear complement (formally, choose the three
slot-coordinate functionals dual to `u1,u2,u3` and set them to zero).
The implicit-function theorem then solves

    F(z + a u1 + b u2 + d u3, t) = 0

for `(a,b,d)` as a C1 function `α(z,t)` near `(z*,t*)`, with `(z,t)` in
`P × R`. Thus the local HessU-zero bad locus is contained in the image

    Θ(z,t) = z + α1(z,t) u1 + α2(z,t) u2 + α3(z,t) u3.

The parameter space has dimension `(2 CARD('n) - 3) + 1 = 2 CARD('n)-2`.
After embedding `(z,t)` into the ambient x-space as a closed affine
parameter plane, the derivative of `Θ` has rank at most `2 CARD('n)-2`,
so the derivative of the first component of the resulting chart is not
surjective onto x-space. To satisfy the closed-image requirement, exhaust
the local parameter neighborhood by countably many compact boxes; each
compact box maps continuously to a compact, hence closed, x-set.

This is the promised "rank-3 criterion to `charts/Crit/D`" construction:
not the rank-1 `trans`/`schur` graph, but a codim-3 cut in x with t left
free, followed by projection to x.

**Important interface warning.** The raw
`d3_chart_core_of_Lindelof_H0core_cball_patches` hypothesis is stronger
than the HessU-zero residual alone: its local `C` must contain every
nearby critical x for all t in the cball/interval, not merely the
`HessU = 0` bad points. The map above only cuts the `H_par = 0` part of
the critical locus. Therefore do not try to discharge that exact local
hypothesis with the cubic witness alone.

**2026-07-12 leaf inspection correction.** There is an even sharper
interface issue: `Jac3_H0cub` is a determinant of derivative rows
`(Phi_par, gradU_2, T3rad)`, but `T3rad` is not currently known to be a
level-set equation vanishing on `D3BadXG_H0core` or on the
`gradU = 0 ∧ HessU = 0` fibre. The honest vanishing Hessian scalar
`H_par` differentiates to the second radial profile row, not directly to
the `T3rad` row. Thus a rank statement for `Jac3_H0cub` is not yet an
IFT/chart witness by itself; one still needs either a proved third
vanishing cut whose x-derivative is row-equivalent to `T3rad`, or a
different arc-localization route.

The already-proved fixed-angle theorem
`fixed_omega_H0core_chart_core_of_generic_conditions` is therefore an
important fallback: for a singleton `{ω}` it covers the whole H0core
fibre under the angle-only assumptions `cvec_dip ω ≠ 0`,
`det(matrix Dcvec_dip ω) ≠ 0`, `gain_dip ω ≠ 0`, and `2 ≤ CARD('n)`.
In the new leaf this is exposed as
`H0coreArc_fixed_omega_chart_core_of_regular_angle`, with
`H0coreArc_regular_angle_open` /
`H0coreArc_regular_arc_interval` recording the local nonzero-gain and
nonzero-steering-determinant shrink. This does not by itself close the
arc residual, because a pointwise singleton chart core does not cover an
uncountable arc without a countable localization or isolation argument.
But it gives the correct formal target for the next step: convert the
local regular-angle interval into countably many closed x-pieces, or
prove that the relevant H0 bad times are locally isolated so the
singleton engine can be used countably.

There are two viable formal routes:

1. Prove a residual chart-core lemma for the `HessU = 0` sublocus using
   the joint rank-3 construction above and combine it with the rank-1
   cover by the existing countable/union chart-core lemmas.
2. Or strengthen the local witness fed to
   `d3_chart_core_of_Lindelof_H0core_cball_patches` by making `C` a union:
   the existing rank-1 local critical cover for nearby `HessU ≠ 0`
   criticals plus the new rank-3 projected cover for nearby `HessU = 0`
   criticals.

Route 1 is the cleaner first formal target. Route 2 is the wrapper needed
only if the final capstone insists on the already-existing Lindelöf lemma
with its all-critical local-cover hypothesis.

**Concrete next Isabelle targets in the new leaf session.**

1. Done in `M5_Dev_H0coreArc/Scratch_H0coreArc.thy`: create the leaf
   session and expose the fixed-angle H0core theorem through
   `H0coreArc_fixed_omega_chart_core_of_regular_angle`.
2. Done in the same leaf, modulo machine verification blocked by heap
   permissions: prove the local regular-angle shrink
   `H0coreArc_regular_angle_open` / `H0coreArc_regular_arc_interval`, so
   nonzero `gain_dip`, nonzero steering determinant, and nonzero `cvec`
   persist on a small arc interval.
3. Next formal target, now sharpened: expose the exact wrapper saying
   that if an arc's H0core bad set is contained in a countable union of
   singleton fixed-angle H0core fibres, and each listed angle satisfies
   `cvec ≠ 0`, `det Dcvec ≠ 0`, and `gain_dip ≠ 0`, then
   `d3_detHess_arc_chart_core` follows immediately from
   `d3_chart_core_of_countable_fixed_omega_cover` plus
   `fixed_omega_H0core_chart_core_of_generic_conditions`. This does not
   prove the needed countable localization/isolation theorem, but it
   packages the residual obligation in the exact capstone-facing form.
   A cleaner caller-facing variant is to define the bad-angle set
   `{ω∈γ. ∃x∈V. x∈D3BadXG_H0core {ω}}`; countability/regularity of this
   angle set implies the raw singleton-fibre cover by unfolding
   `D3BadXG_H0core`. The empty bad-angle case is a separate immediate
   empty-chart-core case, so the countable theorem does not need an
   arbitrary dummy regular angle.
   For the actual Robust4 design point there is an even sharper wrapper:
   `fixed_omega_H0core_chart_core_robust4_all_angles` already handles
   every angle with `0 < ω$1 < pi`. Since
   `OmegaPF [pi/2,0] (pi/4)` lies in that strip, the capstone-facing
   residual becomes exactly: for every analytic arc in this box, its
   H0core bad-angle set is countable.
4. In parallel as a risk check, keep the row-reduction question open:
   only if a genuine vanishing third cut is identified should
   `Jac3_H0cub` be packaged as an IFT/vector-cut witness. Do not use
   `T3rad` itself as a cut until that missing vanishing statement exists.
5. Only after one of the two routes above is real, wire the residual cover
   into the existing D3 union or Lindelöf assembly.

## 7. Remaining open questions after this pass

- Whether `{HessU≡0} ∩ D3BadXG_H0core` is actually empty at the design
  point, or genuinely needs its own (thin) chart argument (§6a). **Scoped
  (§6a-addendum), then CORRECTED TWICE (§6a-addendum-2, 2026-07-12): (i)
  the fix can't literally be `trans`/`schur`-style, since `trans` is
  identically false wherever `HessU≡0` (dividing by/testing the zero
  matrix) — the IFT-graph mechanism cannot apply there at all; (ii) the
  Lindelöf/countable-cover assembly step it would feed into is **already
  built and fully generic** (`d3_chart_core_of_Lindelof_H0core_cball_
  patches`, no reference to `trans`/`schur`/`HessU` in its own statement)
  — no new assembly machinery is needed. What remains is a genuinely new
  (but now precisely scoped) proof: a per-bad-point `local` witness for
  that existing assembly lemma, built from `Jac3_H0cub` +
  `real_analytic_nowhere_dense_zeros` in the same *spirit* as (but not
  literally shared with) whatever the `Ξ`-witness's own residual
  isolated-`x` fallback will eventually need. **Further checked
  (2026-07-12): `Appendix/Wiring/D3_Chart_Wiring.thy` (1259 lines, 0
  `sorry`) already confirms this is genuinely open — it has a whole
  "scalar/functional/vector-cut engine" and honestly documents, in its
  own header, "the remaining engine gap": converting a fixed-`ω` rank-3
  criterion (`Jac3_H0cub`/`Jac3_H12rad`) into `charts/Crit/D` data is
  built, but *assembling across a continuum of angles* is explicitly
  flagged as the next, unbuilt tier. Its `d3_chart_core_of_fixed_omega_
  piece_cover` route (§2's aside) does NOT sidestep this either — its
  `pieces` antecedent still demands a countable cover of the arc-fibre by
  closed pieces each pinned to a *single* fixed angle, i.e. the same
  continuum-assembly problem in different packaging, confirming the
  earlier (2026-07-11) session's finding still stands. `Jac3_H0cub` is a
  **rank-3** (not rank-1) criterion, so its arc-extension is likely a
  bigger lift than `trans`/`schur`'s own rank-1 IFT graph was, not a
  smaller one — revise "comparable in size" above to "at least as big."**
- ~~Whether `D34_H0res_Branch.thy`'s `B_dip` machinery is or isn't the
  right tool for whatever residual `HessU≡0` leaves behind~~ **RESOLVED
  (2026-07-12, §6a-addendum): no. `B_dip`/`D34_H0res_Branch.thy` implements
  an unrelated Case-B-flavored per-antenna residual ("app:H0res"), and by
  its own header is not even imported by `Nonemptiness_Robust3.thy` —
  disconnected from the live `F0_dip_nonempty` chain entirely.**
- ~~The concrete critical 2-bump `Ξ`-witness computation (§6b)~~ **PROGRESS
  (2026-07-12, §6d): a generic-angle single-bump asymptotic/IVT witness
  family is worked out by hand, reducing the remaining gap to two scalar
  genericity side-conditions (`d_perp·c0≠0`, `d_w·perp2(c0)≠0`) plus one
  IVT existence-refinement technicality — not yet closed, not yet
  formalized.**
- ~~Is `d_perp·c0 ≠ 0` at the design point~~ **RESOLVED (2026-07-12, §6e):
  false exactly on the line `ψ0=0` (a genuine structural fact — `Dc` is
  diagonal there), true everywhere else in the design box (hand-checked
  algebraically + 2000-sample numeric sweep, zero near-zero hits off the
  line). The `ψ0=0` case is separately closeable by the same asymptotic
  mechanism with a swapped condition (`d_w$1≠0` instead) — see §6e.**
- ~~Is `d_w·perp2(c0) ≠ 0` (`ψ0≠0`) / `d_w$1 ≠ 0` (`ψ0=0`), i.e. `v$1=0`
  vacuity / `w∥e_par`~~ **MOSTLY RESOLVED (2026-07-12, §6f): the `ψ0≠0`
  bad case (`w∥e_par`) is not actually bad — `Ξ` reduces to `H_par`, whose
  leading term is unconditionally nonzero, no side-condition needed.**
  Residual: **only** at `ψ0=0` *and* `w∥perp2(e_par(ω0))` simultaneously
  (a thin, doubly-special locus) does the witness still need a check.
- ~~Whether `H_cross`'s leading `O(φ)` coefficient (§6f's residual sliver,
  `ψ0=0 ∧ w∥perp2(e_par)`) is nonzero~~ **CHECKED (2026-07-12, §6g): it's
  not just small, it's exactly ZERO on the whole single-bump family — a
  mirror-symmetry obstruction, not a computational accident.** The
  single-bump construction cannot resolve this sliver at all; needs a
  symmetry-breaking two-bump witness instead (recipe identified, not
  built). Still low priority (doubly-degenerate locus).
- ~~Whether `schur` alone (without needing `Ξ`/cubic machinery at all)
  already suffices whenever `trans` fails only at isolated x's~~ **CHECKED
  (2026-07-12): no — see §6c. `schur` and `trans` are strictly conjunctive
  in this architecture (`arc_schur_L` literally divides by the `trans`
  quantity), so §6b's `Ξ`-witness work is NOT moot and is the next real
  unit of work.**
- ~~The precise large-`φ` asymptotic coefficient of `Ξ(p*_N)` along the
  root family `φ*_N = Nπ + O(1/N)`~~ **RESOLVED EXACTLY (2026-07-12, §6i):
  turns out `r(φ)=φQ` and `Ξ(p)=-2n1g0R·φ²cosφ+O(1)` **exactly** (not
  asymptotically — the `1/sinφ` term substitutes exactly via (C1)'s own
  identity `φsinφ=B(φ)`, no error term). Reduces to two independent,
  well-scoped remaining pieces: (1) an IVT root-existence lemma (simpler
  than originally thought — no `sinφ*_N` side-condition needed at all, only
  `cosφ*_N` bounded away from 0, which §6h already showed is automatic for
  the `φ=Nπ+t*` window), and (2) checking the single fixed scalar `R≠0`
  (`R := (d_w·c0)/(c0·c0) + Q·(d_w·perp2c0)`) — cheap, not yet done. The
  algebraic layer (Ξ definition, single-bump `Wc`/`Wc_d1`/`Wc_dd`, (C1)/(C2),
  pivot fact) is fully formalized and landed (0 `sorry`,
  `M5_Dev_D3Hess/Scratch_D3Hess.thy`, `Applied_Math_M5_D3Hess`).**

### 6k. `R \<noteq> 0` resolved completely: `R \<cdot> e_par$1 = w$1`, a FULLY GENERAL
identity (2026-07-12, session 4, after a machine restart)

The IVT root-existence lemma (`phi_sin_eq_B_root_exists_even`) landed (0
`sorry`) in a session I have no direct memory of (the user's machine
crashed; picked this up cold from the file + diary). The one item §6i left
open -- "check `R \<noteq> 0` by hand" -- is now **fully and exactly resolved**,
and the resolution is sharper and more general than anything in §6d-§6j
anticipated.

**Method**: rather than hand-deriving `R`'s formula in the Robust4 trig
variables (the route that produced two hand-derivation errors already,
§6h correcting §6d), I computed it with a computer algebra system (sympy)
first, both at the Robust4 design point AND -- crucially -- in FULL
GENERALITY (an arbitrary invertible `2x2` matrix `M` in place of `Dc`, an
arbitrary `e` with `e$1\<noteq>0` in place of `e_par`, `c := M\<cdot>e`). The general
computation confirms:

    R(w) \<cdot> e$1 = w$1                                        (exactly, always)

as a literal polynomial identity -- `sympy.together(R*e1 - w1)` has
numerator `0` after expansion, no factoring or trig needed at all. This
holds for ANY invertible `M`, not just Robust4's steering matrix -- **`R`'s
nonvanishing has nothing to do with the design point's trig specifics; it
is pure `2x2` linear algebra.**

**Consequence**: `R = 0 \<longleftrightarrow> w$1 = 0` whenever `e_par$1\<noteq>0` (itself
needed just for `Q`/`R` to be *defined* -- see below). The single-bump
witness's leading coefficient is nonzero **exactly when the arc's angular
velocity has a nonzero `\<theta>`-component** -- independent of where on the arc
you are, independent of `\<psi>`, independent of everything except that one
component of `w`. This is a dramatically cleaner answer than the
case-by-case analysis in §6d-§6g (which separately handled `w\<parallel>e_par`
"free," `w\<parallel>perp2(e_par)` at `\<psi>0=0` "exactly zero, needs 2-bump") --
those are now understood as special instances of one linear fact:
`w$1=0` describes a single line of "bad" tangent directions in `\<omega>`-space
at each `\<omega>0`, not a family of unrelated special cases.

**Why this is believable, structurally** (found by decomposing `w` in the
`(e_par, perp2 e_par)` orthogonal basis: `w = \<alpha>\<cdot>e_par + \<beta>\<cdot>perp2(e_par)`,
`\<alpha>=(w\<bullet>e_par)/(e_par\<bullet>e_par)`, `\<beta>=(w\<bullet>perp2 e_par)/(e_par\<bullet>e_par)`):
linearity pushes this through `Dc`, giving `Dc(w) = \<alpha>\<cdot>c + \<beta>\<cdot>d_perp`. Then:

  - `Dc(w)\<bullet>perp2(c) = \<beta>\<cdot>(d_perp\<bullet>perp2(c)) = \<beta>\<cdot>det(Dc)\<cdot>(e_par\<bullet>e_par)`, using
    `c\<bullet>perp2(c)=0` (any vector, trivially) and the ALREADY-PROVEN pivot fact
    `d_perp\<bullet>perp2(c)=det(Dc)\<cdot>(e_par\<bullet>e_par)` (`pivot_nonzero`).
  - `Dc(w)\<bullet>c = \<alpha>\<cdot>(c\<bullet>c) + \<beta>\<cdot>(d_perp\<bullet>c)` -- this `d_perp\<bullet>c` term is the
    genuinely messy quantity §6e had to compute by hand via explicit trig
    (found zero exactly on `\<psi>=0`, nonzero elsewhere).
  - Substituting both into `R`'s formula, the messy `d_perp\<bullet>c` term
    appears TWICE -- once directly, once inside `Q` -- with opposite signs,
    and **cancels exactly**, leaving `R = \<alpha> - \<beta>\<cdot>e_par$2/e_par$1`.
  - `w$1 = \<alpha>\<cdot>e_par$1 - \<beta>\<cdot>e_par$2` (component 1 of the decomposition, using
    `perp2(e_par)$1 = -e_par$2`).
  - So `R\<cdot>e_par$1 = \<alpha>\<cdot>e_par$1 - \<beta>\<cdot>e_par$2 = w$1` exactly. QED, and none of
    §6e's hard-won `d_perp\<bullet>c` computation was even needed for THIS fact
    (it cancels out identically) -- it's still needed elsewhere (e.g. to
    evaluate `Q` itself explicitly), just not for the `R\<noteq>0` question.

**The one remaining side-condition, now isolated and singular**: `R`/`Q`
are only *defined* where `e_par$1\<noteq>0`. Numerically scanning `e_par$1`
across the actual (box-shaped, not disk-shaped -- see correction below)
design region shows it has a genuine zero curve inside the box (crosses
zero near `\<theta>\<approx>1.6-1.7` at `\<psi>=0.394`, confirmed as a true sign change /
pole of `1/e_par$1`, not a numerical artifact). This is very likely
IDENTICAL to the pre-existing, already-anticipated `d3_s2_global_factor=0`
locus (`e_par = (s2/D, -s1/D)` per §3, so `e_par$1=0 \<Leftrightarrow> s2=0`) -- **not a
new problem**, but a known angle-only condition the codebase already has
machinery for (the `d3_s1_or_s2_global_factor_nonzero` case-split: `s1,s2`
can't both vanish). This link is a strong hypothesis, not yet checked
line-by-line against `d3_s2_global_factor`'s actual Isabelle definition.

**Important correction to §6e's own numeric sweep**: `OmegaPF ctr \<delta>` is
`cbox (ctr - [\<delta>,\<pi>]) (ctr + [\<delta>,\<pi>])` (`Nonemptiness_Robust2.thy:670`) --
a BOX, restricting only `\<theta>` to `[ctr$1-\<delta>, ctr$1+\<delta>]`; `\<psi>` ranges over
essentially the FULL `[-\<pi>,\<pi>]`, not `(0,\<pi>/4)` as §6e's sweep assumed. This
doesn't affect §6e's own `d_perp\<bullet>c0` finding (re-verified: still exactly
`\<psi>=0`, a fact independent of the sweep window), but it means any future
numeric sweep in this project claiming to cover "the design box" must use
the true box `\<theta>\<in>[\<pi>/4,3\<pi>/4]`, `\<psi>\<in>[-\<pi>,\<pi>]`, not a narrow `\<psi>` guess.

**Formalization status**: `R_dip`/`Q_dip` (matching `Q`/`R` above exactly)
and the theorem `R_dip_times_e_par1_eq_w1` (plus corollary
`R_dip_eq_zero_iff`) are being landed in `M5_Dev_D3Hess/Scratch_D3Hess.thy`
now, via the orthogonal-decomposition proof sketched above (NOT a
brute-force `m11..m22` component bash, even though sympy confirmed that
route also works -- the structural proof is far shorter and reuses
`pivot_nonzero`/`perp2_orth` already in the file). Verification in
progress as this entry is written.

**Net effect on the D3 story**: modulo (i) formalizing the short proof
above (in progress) and (ii) confirming `e_par$1\<noteq>0 \<Leftrightarrow> d3_s2_global_factor
\<noteq>0`, the single-bump witness for `\<Xi>\<neq>0` is COMPLETE for every arc whose
tangent has nonzero `\<theta>`-component wherever it crosses the `det HessU=0`
stratum -- which, combined with the IVT root lemma now also landed,
finishes the ENTIRE algebraic + analytic core of the arc-bridge's
`trans`/`schur` degenerate-residual argument, modulo: (a) assembling these
pieces into the actual `local` chart-core witness `d3_chart_core_of_
Lindelof_H0core_cball_patches` needs (not yet done -- these lemmas prove
`\<Xi>\<neq>0` at a point, not yet packaged as a chart), and (b) the thin residual
`w$1=0` sub-case (needs its own, not-yet-built argument, though now a
single clean codimension-1 condition on the arc's tangent rather than an
open-ended family of cases).

**CONFIRMED (2026-07-12, user, jEdit all-green): `R_dip_times_e_par1_eq_w1`
and `R_dip_eq_zero_iff` compile, 0 `sorry`.** `R\<noteq>0` is genuinely closed.

### 6l. What's honestly still missing before "\<Xi>\<neq>0 exists" is an actual
theorem, not just a formula (2026-07-12, session 4)

Important scope correction before anyone assumes `\<section>6k` finished the
`\<Xi>`-witness: it did NOT. `R_dip` only says what happens IF you're already
sitting at a critical single-bump point with phase `\<phi>` solving (C1) -- it
does not yet:

1. **Construct the critical point itself.** (C2) (`gradU_dip_dot_perp2_e_par_
   single_bump`) is currently just an EQUATION (`... = 0` after choosing the
   right `r`), not yet solved for `r` as an explicit function of `\<phi>`. Doing
   so needs `pivot_nonzero` (already have -- gives the nonzero pivot
   coefficient) plus a genuine "solve the linear equation for the unique
   root" step -- short, but not yet written.
2. **Get `\<Xi>`'s actual VALUE at that point.** `Xi_eq_par_cross_combo` only
   reduces `\<Xi>` to `H_par`/`H_cross`; getting `\<Xi>`'s closed FORM in terms of
   `Wc`/`Wc_d1`/`Wc_dd` single-bump values needs `HessU_dip_entry_moments_crit`
   + `K_gdip` (already landed, per \<section>5 step 1) chained through `H_par_eq_
   quadform`/`H_cross_def`'s own radial dictionaries -- this chain exists in
   pieces but has not been assembled into one closed `\<Xi>(p)` formula lemma.
3. **Bound the `O(1)` residual EXPLICITLY.** \<section>6i's `term 2`/`term 3` are
   easy to bound (term 2 uses `B` bounded, already a hypothesis of
   `phi_sin_eq_B_root_exists_even`; term 3 uses `Wc` trivially bounded via
   `Wc_single_bump`'s own closed form, `|Wc|\<le>(n1+1)\<^sup>2`) -- but "easy" still
   means writing down two more `have` blocks with actual numeric bounds,
   not yet done.
4. **Combine (1)-(3) with `R_dip_eq_zero_iff` and `phi_sin_eq_B_root_exists_
   even`** into one final existence theorem, roughly:

   ```
   theorem Xi_nonzero_witness_exists:
     assumes "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0" "cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0"
       "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 \<noteq> 0" "vec_nth w 1 \<noteq> 0" "2 \<le> CARD('n)"
     shows "\<exists>x. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<and> Xi x \<omega>0 \<omega>s \<omega> w \<noteq> 0"
   ```

   This is the actual formal statement of "the arc avoids `ker HessU` at
   isolated critical `x`'s, not on an open set" -- i.e. the real mathematical
   content this whole `\<Xi>` sub-project has been aiming at since \<section>4. NOT YET
   WRITTEN. Estimated comparable in size to \<section>6k's own `R_dip` work (a
   half-day-scale unit, not a quick finish) -- recommend this as the next
   session's first concrete target, in the order (1)-(4) above, each step
   independently checkable before moving to the next (mirroring how \<section>6k
   itself was built: general fact first, verified, THEN wired to the
   specific application).

**Do not claim `\<Xi>\<neq>0` is "solved" until `Xi_nonzero_witness_exists` (or an
equivalent) is landed and build-verified.** \<section>6k resolved a real and
previously-open sub-question (is the single-bump family's leading
coefficient ever identically zero) but is infrastructure for this theorem,
not a substitute for it.

### 6m. The `H_par` row-reduction to `T3rad` fails (2026-07-12, Codex)

This is the hand check requested by §6j before writing further Isabelle for
the HessU=0 arc residual. Result: the tempting row-reduction

    D_x H_par  ==  scalar * D_x(T3rad)    modulo {D_x Phi_par, D_x gradU_2}

is false for the honest vanishing cut `H_par`.

Freeze `omega`, and abbreviate

    c  := cvec_dip omega0 omegas omega
    e  := e_par omega0 omegas omega
    q  := Dcvec_dip omega0 omegas omega (axis 2 1)
    d2 := D2cvec_dip omega0 omegas omega e e
    g  := gain_dip omega
    A  := deriv gdip (omega$1) * e$1
    B  := deriv (deriv gdip) (omega$1) * (e$1)^2.

The existing dictionaries say

    Phi_par = A * W + g * W1(c)
    gradU_2 = g * W1(q)
    H_par   = 2*A*W1(c) + B*W + g*W1(d2) + g*W2(c,c).

Because `det Dc != 0`, `{c,q}` is a basis locally, so write

    d2 = alpha * c + beta * q.

Differentiating only in the x-slots, with omega fixed, gives

    D H_par =
      (2*A + g*alpha) * D W1(c)
      + B * D W
      + g*beta * D W1(q)
      + g * D W2(c,c).

Modulo `D gradU_2 = g * D W1(q)` and
`D Phi_par = A * D W + g * D W1(c)`, this reduces to

    D H_par ==
      (B - A*(2*A + g*alpha)/g) * D W
      + g * D W2(c,c).

So after the legitimate row operations the third row still lives in the
second radial x-jet span generated by `D W` and `D W2(c,c)`. It has no
`D T3rad` component.

The phase-degree check makes the obstruction concrete. On a radial slot
`slot m c`, with `r_p = c dot (x_m - x_p)`,

    D W              only contains sin(r_p),
    D W1(c)          only contains sin(r_p) and r_p*cos(r_p),
    D W2(c,c)        only contains r_p*cos(r_p) and r_p^2*sin(r_p),
    D T3rad          contains 3*r_p^2*sin(r_p) + r_p^3*cos(r_p).

The `r_p^3*cos(r_p)` term in `D T3rad` cannot be manufactured from the
rows available in `D H_par`, `D Phi_par`, and `D gradU_2` by fixed scalar
row operations. Thus `Jac3_H0cub` is not an IFT/vector-cut witness for the
level set `(Phi_par, gradU_2, H_par)=0`.

There is also a structural reason this could not have worked by changing
only row operations. If a proposed third cut is a smooth expression that
vanishes for every point with `Phi_par = gradU_2 = H_par = 0`, while
`T3rad` remains a free next invariant on that fibre, then its derivative
cannot have a `D T3rad` component: any expression `F(Phi_par, gradU_2,
H_par, T3rad)` that vanishes for all values of `T3rad` when the first
three arguments are zero has `partial F / partial T3rad = 0` there. The
Tier-6 `Jac3_H0cub` theorem is therefore a fixed-angle nonflatness /
nowhere-dense-zero witness, not directly a codim-3 level-set chart.

**Consequence for the next target.** Do not formalize the §6j row-reduction
as stated. The viable H0coreArc leaf work remains the capstone-facing
countability wrapper already written in `Scratch_H0coreArc.thy`, plus a
new analytic localization argument that proves countability/isolation of
the relevant bad-angle set, or a genuinely different third vanishing cut.
`T3rad` itself cannot be used as that third cut unless a new theorem first
proves it is constrained on the fibre, which would contradict the way Tier
6 treats it as the free next invariant.

### 6n. First resumed Xi target: solve the C2 single-bump equation (2026-07-12, Codex)

The row-reduction failure in §6m means the HessU=0 residual cannot move
through `Jac3_H0cub` as a direct IFT cut. The remaining productive D3 line
that is already formalized far enough to extend is the `Xi` single-bump
track in `M5_Dev_D3Hess/Scratch_D3Hess.thy`. Per §6l, the first missing
piece there is not the IVT root lemma or the `R_dip` identity, which are
landed, but the explicit solution of the second criticality equation (C2).

The required algebra is small and independent enough to formalize in a
new leaf rather than editing `Scratch_D3Hess.thy` directly.

Freeze `omega`, and abbreviate

    c := cvec_dip omega0 omegas omega
    e := e_par omega0 omegas omega
    d := Dcvec_dip omega0 omegas omega (perp2 e)
    n1 := CARD('n) - 1
    W(phi) := n1^2 + 1 + 2*n1*cos(phi).

The existing single-bump formula says

    gradU(slot i p, omega) dot perp2(e)
      = -2*n1*gain(omega)*(d dot p)*sin(phi)
        + gdip'(omega_1)*(perp2 e)_1*W(phi),

provided `phi = c dot p`.

So if `n1 != 0`, `gain(omega) != 0`, and `sin(phi) != 0`, C2 is solved by
choosing

    d dot p = y(phi)
      := gdip'(omega_1)*(perp2 e)_1*W(phi)
         / (2*n1*gain(omega)*sin(phi)).

The vector-level solve is pure two-dimensional linear algebra. If `c != 0`
and `d dot perp2(c) != 0`, then for any target `y`

    p(phi,y)
      := (phi / (c dot c)) * c
         + ((y - phi*(d dot c)/(c dot c)) / (d dot perp2(c))) * perp2(c)

satisfies

    c dot p(phi,y) = phi
    d dot p(phi,y) = y.

In the D3 application, the pivot lemma already gives

    d dot perp2(c) = det(Dc) * (e dot e),

so this denominator is nonzero from `det(Dc) != 0` and `c != 0`
(`Dc(e)=c`, hence `e != 0`). This produces a concrete single-bump
configuration satisfying C2 once the IVT-picked phase satisfies C1 and
`sin(phi) != 0` or is handled by a later zero-sine subcase.

This should be the next Isabelle unit:

1. In a fresh leaf importing `Applied_Math_M5_D3Hess.Scratch_D3Hess`, define
   the pure point solver `single_bump_phase_point c d phi y`.
2. Prove its two dot-product equations.
3. Specialize it to `d = Dcvec_dip(...)(perp2 e_par)` using `pivot_nonzero`.
4. Use `gradU_dip_dot_perp2_e_par_single_bump` to prove the C2-zero theorem
   under the explicit nonzero assumptions above.

This does not yet finish `Xi_nonzero_witness_exists`; it closes item 1's
C2 construction part from §6l and leaves C1 root selection, the closed
`Xi(slot i p)` value, and the final nonzero argument as the subsequent
checkable steps.

**Formalization status (Codex, 2026-07-12): done and verified.** Added the
fresh leaf `M5_Dev_D3Xi/Scratch_D3Xi.thy` (`Applied_Math_M5_D3Xi`) with
`single_bump_phase_point`, the two dot-product solver lemmas, scalar C1/C2
cancellation lemmas, and
`single_bump_gradU_zero_of_phase_root_and_C2_target`. The final theorem says
that under `2 <= CARD('n)`, nonzero steering determinant, `cvec_dip != 0`,
`gain_dip != 0`, `sin phi != 0`, and the C1 root equation, the explicit
C2-target point has `gradU (...) (slot i p) omega = 0`. Verification command
used a no-heap-save build because `-b` was killed while saving the large
D3Hess heap:

    isabelle build -o threads=2 ... Applied_Math_M5_D3Xi

Result: `Finished Applied_Math_M5_D3Hess` and
`Finished Applied_Math_M5_D3Xi`. This closes the critical-point construction
part of §6l item 1 for the `sin phi != 0` branch.

### 6o. The corrected exact `Xi(slot i p)` formula, re-derived from the
unconditional `HessU_quad_dictionary` and numerically cross-checked
(2026-07-12, Claude, session 4)

Went back to first principles rather than trust §6d/§6i's original
`Xi(p)` formula (which implicitly assumed a "K0-folded" simplification that
turns out to need its OWN justification -- see below). The actually-proven,
completely unconditional dictionary in this codebase is
`HessU_quad_dictionary` (`D34_Geodesic_Branch.thy:702`, no criticality
hypothesis, arbitrary `e`,`w`):

    (HessU *v w) . e = (g' e$1) Wc_d1(x,c;Dc w) + g'' w$1 e$1 Wc(x,c)
      + g (Wc_d1(x,c;D2c(e,w)) + Wc_dd(x,c;Dc e,Dc w)) + g' w$1 Wc_d1(x,c;Dc e)

Setting `e := e_par` (so `Dc e = c`), this has FOUR raw terms, not the
three-term `K0`-folded shape `\<section>6d/\<section>6i` assumed -- there are two separate
`g'`-weighted cross terms (`g'e_par$1*Wc_d1(...;Dc w)` and
`g'w$1*Wc_d1(...;c)`) that don't obviously combine into a single `K0`
coefficient the way the DIAGONAL case (`H_par`, `w=e_par`) does.

**Re-derived by hand, substituting the single-bump `Wc`/`Wc_d1`/`Wc_dd`
closed forms and eliminating `g'` via (C1)'s own exact identity
`g'*e_par$1*V(\<phi>) = 2n1*g0*\<phi>*sin\<phi>`** (not asymptotically -- an exact
algebraic substitution, same trick as \<section>6i's `1/sin\<phi> = \<phi>/B(\<phi>)`).
**Result: EVERY extra term besides the `-2n1g0\<phi>cos\<phi>*A_w` leading piece
turns out to be exactly \<phi>-independent (bounded, not just asymptotically
negligible) once `A_w = \<phi>*R_dip(w)` and `A_{e2} := D2c(e_par,w)\<bullet>p = \<phi>*S`
(same linear-in-\<phi> structure as `A_w`, for a second fixed scalar `S`) are
substituted:**

    Xi(slot i p_\<phi>) = -2n1*g0*R*\<phi>\<^sup>2*cos\<phi>
      - 4n1\<^sup>2*g0*B(\<phi>)\<^sup>2*R/V(\<phi>)
      - 2n1*g0*B(\<phi>)*S
      - 4n1\<^sup>2*g0*w$1*B(\<phi>)\<^sup>2/(e_par$1*V(\<phi>))
      + g0''*w$1*e_par$1*V(\<phi>)

i.e. Sketch's original leading-order claim (`\<section>6i`) is CONFIRMED CORRECT, but
the "residual is O(1)" claim now has an honest, complete justification (all
four residual terms, not just the two `\<section>6i` originally considered) rather
than an assumption. **Numerically cross-checked** (random invertible `2x2`
`M`, random `e,w,e2vec`, `g0,g0'',n1`, `\<phi>`, solving `g0'` from (C1) and `r`
from (C2) exactly): raw `HessU_quad_dictionary`-based `Xi` value and the
formula above agree to `1e-12` (floating-point noise only). All four
residual terms are honestly bounded (`|B|\<le>Cbound`, `V(\<phi>)\<in>[(n1-1)\<^sup>2,(n1+1)\<^sup>2]`
both positive given `n1\<ge>1`, everything else `\<phi>`-independent) -- so:

    |Xi(slot i p_\<phi>) - (-2n1g0R\<phi>\<^sup>2cos\<phi>)|
      \<le> 4n1\<^sup>2|g0|Cbound\<^sup>2|R|/(n1-1)\<^sup>2 + 2n1|g0|Cbound|S|
          + 4n1\<^sup>2|g0||w$1|Cbound\<^sup>2/(|e_par$1|(n1-1)\<^sup>2) + |g0''||w$1||e_par$1|(n1+1)\<^sup>2
      =: C_res     (a FIXED constant, independent of \<phi>)

Combined with `phi_sin_eq_B_root_exists_even` (gives `\<phi>*_M` with
`|cos\<phi>*_M|\<ge>\<surd>2/2`, `M` as large as needed) and `R_dip_eq_zero_iff`
(`R\<noteq>0 \<longleftrightarrow> w$1\<noteq>0`): choosing `M` large enough that
`2n1|g0||R|(\<surd>2/2)(\<phi>*_M)\<^sup>2 > C_res`, `Xi(slot i p_{\<phi>*_M}) \<noteq> 0` is now a
FULLY closed, checked (mod formalization) argument -- this is
`Xi_nonzero_witness_exists` (\<section>6l), modulo (i) formalizing this bound chain
and (ii) `S`'s own definition (`D2cvec_dip(e_par,w)\<bullet>perp2(c0) / (c0\<bullet>c0)`-style,
analogous to `R`'s own `Q`-based formula but for the `D2c` vector instead of
`Dc(w)`) -- `S` needs NO nonvanishing property, only boundedness, which is
free once it's shown to not depend on \<phi>.

**Division of labor note**: Codex is independently building the explicit
critical-point CONSTRUCTION (\<section>6n, `single_bump_phase_point`, new leaf
`M5_Dev_D3Xi`) -- that and this \<section>6o value-formula work are independent and
compose: \<section>6n gives the existence of a critical `p` for given `(\<phi>,y)`; \<section>6o
(once formalized) gives `Xi`'s value there. Recommend `Xi_nonzero_witness_
exists`'s eventual proof cite both.

**CONFIRMED (2026-07-12, session 4): `Xi_single_bump_raw` lands, 0 `sorry`,
clean batch reload (`RELOAD_OK`).** The working proof avoided manual
`[of ...]`/`[where ...]` instantiation of `HessU_quad_dictionary` entirely
(a first attempt with positional `[of ...]` silently mis-ordered the
`fixes` list `x e w \<omega> \<omega>0 \<omega>s` and unfolded nothing; a second attempt with
explicit `[where x=... e=... ...]` hit a real type-unification error before
being superseded) -- the robust fix was a two-step `have raw: ... unfolding
Xi_def by (rule HessU_quad_dictionary)` (letting higher-order unification
find the instantiation automatically against the goal) followed by `show
?thesis unfolding raw Wc_single_bump Wc_d1_single_bump Wc_dd_single_bump
Dcvec_dip_e_par[OF detnz] by (simp add: power2_eq_square algebra_simps)`.
Lesson for next time: prefer `by (rule LEMMA)` / `unfolding ... by (rule
LEMMA)` over manual positional or named instantiation of a multi-variable
dictionary lemma when the goal already pins the instantiation uniquely.

### 6p. Next formal bridge: the constructed point has `Dc(w) dot p = phi*R_dip(w)` (2026-07-12, Codex)

Section 6n constructs the critical single-bump point by solving C2 in the
`{c, perp2 c}` basis. Section 6o's leading-term extraction needs the
projection of that same point against `Dc(w)` and `D2c(e,w)`.

The algebra is a direct consequence of the C1 equation. With

    W(phi) = n1^2 + 1 + 2*n1*cos(phi),
    y = gp*(perp2 e)_1*W(phi)/(2*n1*g*sin(phi)),
    phi*sin(phi) = gp*e_1*W(phi)/(2*n1*g),

and `e_1 != 0`, `sin(phi) != 0`, the C2 target simplifies to

    y = phi * (perp2 e)_1 / e_1.

For the point

    p = (phi/(c dot c))*c
        + ((y - phi*(d dot c)/(c dot c))/(d dot perp2 c))*perp2 c,

where `d = Dc(perp2 e)`, the pivot identity gives

    d dot perp2 c = det(Dc)*(e dot e).

So the coefficient of `perp2 c` is exactly

    phi * ((perp2 e)_1/e_1 - (d dot c)/(c dot c)) / (det(Dc)*(e dot e))
      = phi * Q_dip.

Therefore for any probe vector `a`,

    a dot p = phi * ((a dot c)/(c dot c) + Q_dip*(a dot perp2 c)).

Taking `a = Dc(w)` gives

    Dc(w) dot p = phi * R_dip(w),

and taking `a = D2c(e,w)` gives the analogous scalar

    D2c(e,w) dot p = phi * S_dip(w),

where `S_dip(w)` is the same projection functional with `D2c(e,w)` in place
of `Dc(w)`. `S_dip` needs only boundedness/finiteness in the final Xi
argument, not nonvanishing.

### 6p. Reconciling Codex's `single_bump_phase_point` with `R_dip`'s
`r=\<phi>Q` (2026-07-12, Claude, session 4)

Codex's `M5_Dev_D3Xi/Scratch_D3Xi.thy` landed a COMPLETE, general critical-
point construction: `single_bump_gradU_zero_of_phase_root_and_C2_target`
gives, from a root `\<phi>` of (C1) with `sin \<phi>\<noteq>0`, an explicit `p :=
single_bump_phase_point c d \<phi> (single_bump_C2_target ... \<phi>)` with
`gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (slot i p) \<omega> = 0` -- i.e. genuine
criticality, via a DIFFERENT (more general, C1-independent) parametrization
than \<section>6i/\<section>6k's own `r=\<phi>Q_dip`.

**Checked by hand: these are the SAME point, given (C1) holds.** Codex's
target `y(\<phi>) := gp\<cdot>pe1\<cdot>W(\<phi>) / (2n1\<cdot>g\<cdot>sin\<phi>)` -- substituting (C1)'s own
identity `gp\<cdot>W(\<phi>)/(2n1g) = \<phi>sin\<phi>/e1` (rearranged from `\<phi>sin\<phi>=B(\<phi>)`,
`B(\<phi>):=gp\<cdot>e1\<cdot>W(\<phi>)/(2n1g)`) -- gives `y(\<phi>) = pe1\<cdot>\<phi>sin\<phi>/(e1\<cdot>sin\<phi>) =
\<phi>\<cdot>pe1/e1` EXACTLY. Plugging this into `single_bump_phase_point`'s own
`perp2(c)`-coefficient `[y-\<phi>(d\<bullet>c)/(c\<bullet>c)]/(d\<bullet>perp2c)` gives
`\<phi>\<cdot>[pe1/e1-(d\<bullet>c)/(c\<bullet>c)]/(d\<bullet>perp2c) = \<phi>\<cdot>Q_dip(...)` EXACTLY (matching
`Q_dip`'s own definition verbatim). **So Codex's `p` and \<section>6i's
`(\<phi>/(c\<bullet>c))c + \<phi>Q\<cdot>perp2(c)` coincide identically whenever \<phi> solves (C1)**
-- not a coincidence, both solve the same 2-equation linear system with a
unique solution (pivot nonzero). Consequence: `Dc(w)\<bullet>p = \<phi>\<cdot>R_dip(...,w)`
EXACTLY at Codex's `p` too (substituting the same identity into `R_dip`'s
own formula) -- so the \<section>6o leading-term/residual analysis applies
UNCHANGED to Codex's construction; no adaptation needed, just a short
connecting lemma (`Dc(w)\<bullet>(single_bump_phase_point c d \<phi> (single_bump_C2_
target ...)) = \<phi>\<cdot>R_dip \<omega>0 \<omega>s \<omega> w`, given the root condition) rather than
a full re-derivation.

**Division of labor, now concrete**: Codex owns `M5_Dev_D3Xi` (point
construction + criticality, DONE). Claude owns `M5_Dev_D3Hess` (`\<Xi>`'s
value formula, `Xi_single_bump_raw` DONE; the connecting lemma above and
the final `Xi_nonzero_witness_exists` assembly are next). No file
conflicts: the assembly theorem should live in a THIRD leaf importing both
`Applied_Math_M5_D3Hess.Scratch_D3Hess` and `Applied_Math_M5_D3Xi.
Scratch_D3Xi`, per this project's established "assembly in a fresh leaf,
don't edit either upstream scratch" convention (\<section>6j, \<section>6n).

### 6q. Assembly leaf: good-phase Xi witness bridge (2026-07-12, Codex)

Implemented the third leaf `M5_Dev_D3Assembly/Scratch_D3Assembly.thy`
(`Applied_Math_M5_D3Assembly`). It now formalizes the section 6p bridge:

* `single_bump_phase_point_closed_form`: under C1, Codex's C2-solver point is
  exactly `(phi/(c dot c))*c + (phi*Q_dip)*perp2 c`.
* `single_bump_phase_point_dot_eq_phi_R`: the constructed point satisfies
  `Dc(w) dot p = phi * R_dip omega0 omegas omega w`.
* `single_bump_phase_point_dot_eq_phi_S`: the analogous
  `D2c(e_par,w) dot p = phi * S` projection used by the residual.
* `Xi_at_phase_point_closed`: at the constructed point,
  `Xi = -2*n1*gain*R*phi^2*cos phi + residual`.
* `single_bump_residual_le_bound`: the residual is bounded by a fixed
  `single_bump_residual_bound`, independent of `phi`.
* `Xi_nonzero_witness_of_good_phase`: if a C1 phase root also satisfies the
  explicit domination inequality
  `residual_bound < abs(-2*n1*gain*R*phi^2*cos phi)`, then there exists a
  single-bump configuration `x` with both `gradU x omega = 0` and
  `Xi x omega0 omegas omega w != 0`.

Verification: an external focused build rebuilt and saved
`Applied_Math_M5_D3Assembly` at 2026-07-12 16:52. The first failure was an
`OF` mismatch caused by passing the root equation in the local `n1` form to a
theorem exported in the expanded `real CARD('n)-1` form; the second was the
explicit `n1 != 0` side condition. Both are fixed. `git diff --check` is clean
for the assembly leaf.

**Superseded by the user continuation later on 2026-07-12:** the full
root-selection/bounds argument is now formalized in the same assembly leaf.
The completed layer adds the sin-free radial point
`single_bump_radial_point`, its closed form/dot projection lemmas, the radial
criticality theorem `single_bump_gradU_zero_of_phase_root_radial`, the value
formula `Xi_at_radial_point_closed`, and the bridge
`Xi_nonzero_witness_of_good_phase_radial`.  The final theorem
`Xi_nonzero_witness_exists` discharges the former domination hypothesis using
`phi_sin_eq_B_root_exists_even`, `R_dip_eq_zero_iff`, and an Archimedean choice
of a large even root window.

Verification note: the user reported that, after substantial edits,
`M5_Dev_D3Assembly/Scratch_D3Assembly.thy` compiles in jEdit. Codex did not run a
separate batch build at this point because the jEdit/PIDE worker was still
active.

## 7. Hardest remaining target: D4/Branch-P closed-cover core

Written 2026-07-12, Codex iteration.  The single hardest remaining theorem is
not another Xi witness lemma.  It is the D4 closed-cover obligation

    branchP_indep_closed_cover_core_all

because this is the first place where the proof must control a two-dimensional
steering family on the moment-rank-deficient stratum.  The current permanent
target is the retained bad fibre

    BadXGW(Γ) = {x : ∃ω∈Γ.
        gradU(x,ω)=0
      ∧ det HessU(x,ω)=0
      ∧ A_cart(x,ω)≠0
      ∧ det Dcvec(ω)≠0
      ∧ cvec(ω)≠0
      ∧ DM_paper_x(x,cvec(ω)) is not surjective
      ∧ the x-derivative of gradU(·,ω) has no surjective branch }.

Two tempting shortcuts are wrong:

* The regular-Hessian critical graph lemmas (`dip_critical_graph_*`) do not
  directly apply here, because the permanent `BadXGW` already has
  `det HessU = 0`.
* The existing `regular_value_on_gradU_dip` theorem also does not apply, because
  it assumes `surj DM_paper_x`, while `BadXGW` lives exactly on
  `¬ surj DM_paper_x`.

The clean formal reduction is instead:

1.  For any open steering neighbourhood `Ω` with `Γ ⊆ Ω`, every point of
    `V ∩ BadXGW(Γ)` lies in the standard `charts_core_Nn` bad set for
    `G(x,ω)=gradU(x,ω)` over `V×Ω`.  The proof uses the verified bridge
    `not_surj_omega_deriv_iff_detHess_dip`: the `det HessU = 0` conjunct is
    exactly the failure of the omega-partial derivative of `gradU` to be
    surjective.
2.  Therefore a `charts_core_Nn`-shaped chart bundle for that `gradU` bad set
    immediately yields the exposed D4 `branchP_indep_closed_cover_core`: take
    the chart images as the closed sets `K n`, and use
    `negligible_singular_image_2n` for negligibility.

This does not finish D4, but it puts the remaining hard mathematics in the
right form.  What is still missing is a sound way to obtain those chart bundles
on the rank-deficient Branch-P stratum.  Proving regularity over the full
product `V×Ω` is too strong in general; the eventual proof likely needs a
local product/open-cover version adapted to the Branch-P hypotheses
`A_cart≠0`, `det Dcvec≠0`, `¬gamma_par_c`, and `¬surj DM_paper_x`, or an
equivalent chart engine that works over the corresponding open regular
envelopes and then restricts back to `BadXGW`.

Formal iteration started in `M5_Dev_D4Branch/Scratch_D4Branch.thy`:

* `BadXGW_subset_gradU_engine_bad` proves item 1.
* `branchP_indep_closed_cover_core_of_gradU_engine_charts` proves item 2.
* `branchP_indep_closed_cover_core_of_gradU_regular_value` records the
  sufficient but probably over-strong specialization through `charts_core_Nn`.
* `branchP_indep_closed_cover_core_of_countable_closed_covers` reindexes a
  two-level countable family of closed negligible sets into the single
  `K : nat ⇒ set` expected by the permanent D4 core.
* `branchP_indep_closed_cover_core_of_countable_gradU_regular_value_patches`
  is the better target shape: if the D4 bad set is covered by countably many
  local product patches `W_i×Ω_i`, and `gradU` has the regular-value property
  on each patch, then the permanent D4 closed-cover core follows.
* `branchP_indep_closed_cover_core_all_of_countable_gradU_regular_value_patches`
  lifts that patchwise interface to the exact permanent `..._core_all`
  obligation, uniformly for every admissible `Γ`.
* `branchP_indep_closed_cover_core_of_countable_steering_regular_value_cover`
  is a simpler intermediate: if an admissible steering set `Γ` is covered by
  countably many open steering patches `Ω_i` and `gradU` is regular on
  `V×Ω_i`, then the D4 core follows.
* `branchP_indep_closed_cover_core_all_of_countable_steering_regular_value_covers`
  lifts the steering-cover version to the exact permanent `..._core_all`
  target.

The 2026-07-12 continuation added a second, sharper interface that matches
Claude's section 6s recommendation to prefer a countability/isolation fallback
over another `H_par`/`Hrad2` rank-3 shortcut.  The new definition is the actual
D4 witness-angle set

    branchP_bad_angles(V,ω0,ωs,Γ)
      = {ω∈Γ : ∃x∈V. x∈BadXGW(ω0,ωs,{ω})}.

The checked bridge is:

* `BadXGW_subset_D3BadXG_H0core`: D4's retained bad set is a stricter
  D3 H0core fibre, so any H0core chart cover also covers D4.
* `branchP_indep_closed_cover_core_of_d3_H0core_chart_core`: a D3 H0core
  chart core immediately gives the D4 closed-cover core.
* `branchP_fixed_omega_cover_of_bad_angle_range_cover`: if the actual D4
  witness angles are enumerated by `om : nat ⇒ real^2`, then
  `V ∩ BadXGW(Γ)` is covered by the corresponding countable fixed-angle
  H0core fibres.
* `branchP_indep_closed_cover_core_of_countable_regular_bad_angles`: if
  `branchP_bad_angles` is countable and each such angle is regular
  (`cvec≠0`, `det Dcvec≠0`, `gain≠0`; the first two are already conjuncts
  of `BadXGW`), then the D4 core follows from the existing fixed-angle
  theorem `fixed_omega_H0core_chart_core_of_generic_conditions`.
* `branchP_indep_closed_cover_core_all_of_countable_bad_angles`: the exact
  permanent `..._core_all` obligation follows if every admissible
  non-collinear `Γ⊆OmegaPF` has countable `branchP_bad_angles`.

So the hardest remaining D4 theorem is now much more concrete:

    ∀Γ⊆OmegaPF ctr δ.
      (∀ω∈Γ. ¬ gamma_par_c ω0 ωs ω)
      ⟹ countable (branchP_bad_angles V ω0 ωs Γ).

This theorem would close D4 completely in the scratch layer.  Semiformally,
one must show that Branch-P's non-collinearity plus the retained constraints
`gradU=0`, `det HessU=0`, `A_cart≠0`, `det Dcvec≠0`, `¬surj DM_paper_x`, and
failed x-partial regularity cannot persist over a two-dimensional continuum of
angles after projecting away `x`; equivalently, the actual witness-angle locus
is isolated/countable.  This is now the preferred hard target.  The older
regular-value patch theorem remains useful, but it asks for stronger local
product regularity than the countable-angle route.

Verification: `Applied_Math_M5_D4Branch` builds cleanly with the project roots:

    isabelle build -d . \
      -d /home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology \
      -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys \
      -d M5_Dev_Wiring -d M5_Dev_D4Branch Applied_Math_M5_D4Branch

The D4 scratch session now imports `Applied_Math_M5_Wiring.Scratch_Wiring`,
because the countable-angle reducer reuses the already-checked fixed-angle
H0core theorem `fixed_omega_H0core_chart_core_of_generic_conditions`.

The first check caught a brittle explicit instantiation of
`not_surj_omega_deriv_iff_detHess_dip`; removing the manual `of ...` fixed it.
The second check initially hung on an over-automated `metis` choice over local
covers; replacing it with an explicit `SOME` construction made the batch build
finish in the normal focused-check time.  There are no new `sorry`/`oops` holes
in the scratch leaf.

Follow-up note: a more ambitious pointwise-local/Lindelöf reducer was attempted
but not kept, because the representative-choice proof made the batch build
hang.  The checked file stays at the countable-patch and countable-steering
interfaces, which are stable and already sufficient targets for the next
Branch-P transversality step.

### 7a. Semi-formal strategy for `countable_bad` (2026-07-12, Claude, for
Codex, in response to the user's request)

Worked through the remaining target by hand:

    \<forall>\<Gamma>\<subseteq>OmegaPF ctr \<delta>. (\<forall>\<omega>\<in>\<Gamma>. \<not>gamma_par_c \<omega>0 \<omega>s \<omega>) \<Longrightarrow>
      countable (branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>)

**One important correction first, that simplifies the target**: `DM_paper_x
x c :: (planar^'n) \<Rightarrow> complex^6` (checked directly, `Nonemptiness_Paper.thy`)
-- a map from `R^{2n}` (2n real dims) to `C^6 \<cong> R^{12}`. **For any array
with fewer than 6 antennas (`CARD('n)<6`), `surj (DM_paper_x x c)` is
IMPOSSIBLE by dimension count alone (`2n<12`), so `\<not>surj DM_paper_x` is
VACUOUSLY TRUE for every `x`.** This conjunct of `BadXGW` contributes
NOTHING to narrowing the bad locus for realistic (small) antenna arrays --
recommend NOT trying to use it in any codimension/genericity argument;
treat it as a free side-condition that's automatically satisfied whenever
`CARD('n)<6`, and simply carry it through unused. (For `CARD('n)\<ge>6` it
would start to bite, but that's not the case this project's Robust4 design
point/witnesses use as far as I've seen.)

**The dimension-counting heuristic that makes countability plausible.**
`branchP_bad_angles`'s defining condition, per antenna-configuration `x`,
combines THREE genuinely rank-reducing conditions on the JOINT `(x,\<omega>)`
space (dimension `2n+2`):

1. `gradU(x,\<omega>)=0` -- 2 real equations.
2. `det HessU(x,\<omega>)=0` -- 1 real equation (already known, via the checked
   bridge `not_surj_omega_deriv_iff_detHess_dip`, to be EXACTLY
   "`D_\<omega>[gradU](x,\<cdot>)` is not surjective onto `R\<^sup>2`").
3. `D_x[gradU(\<cdot>,\<omega>)]` at `x` is not surjective onto `R\<^sup>2` -- BadXGW's OWN
   last conjunct, structurally the SAME KIND of condition as (2) but for
   the OTHER half of the joint Jacobian (the `x`-partial block, not the
   `\<omega>`-partial block). For a "generic" `2\<times>(2n)` matrix, failing to have
   full rank 2 is a codimension-`(2n-1)` condition (standard determinantal-
   variety count: `(m-r)(k-r)` for an `m\<times>k` matrix dropping to rank `r`,
   here `m=2,k=2n,r=1`).

**Adding these up: `2 + 1 + (2n-1) = 2n+2`, EXACTLY the ambient dimension
of the joint `(x,\<omega>)` space.** This is a strong (though heuristic, not
rigorous -- see caveats below) suggestion that the joint bad-locus
`{(x,\<omega>) : (1)\<and>(2)\<and>(3)}` is GENERICALLY 0-DIMENSIONAL (isolated points),
which would make its `\<omega>`-projection (hence `branchP_bad_angles`, for ANY
`\<Gamma>`, even the full 2-dimensional `OmegaPF` box) automatically LOCALLY
FINITE, hence countable, for free -- no separate argument about `\<Gamma>` being
an arc is even needed. **This is genuinely encouraging: the numbers work
out exactly, not approximately -- (1)+(2)+(3)'s codimensions sum to
precisely the ambient dimension, the signature of a genuine "isolated
solutions" (regular-value / IFT) situation, not a coincidence worth
dismissing.**

**Caveats -- why this is a heuristic, not a proof, and what to actually
check:**

- The `(2n-1)` codimension count for condition (3) assumes the map
  `x \<mapsto> D_x[gradU(\<cdot>,\<omega>)]` behaves "generically" as `x` (and `\<omega>`) vary --
  i.e. that this SPECIFIC, structured Jacobian (not an arbitrary matrix)
  actually achieves the determinantal-variety codimension bound rather
  than degenerating further (which would make the true dimension LOWER,
  fine) or failing to achieve it at all (which would make the true
  dimension HIGHER, breaking the argument). This needs to be checked, not
  assumed.
- "0-dimensional" (in the informal dimension-counting sense) does NOT
  automatically mean "countable" or even "locally finite" in a rigorous
  sense -- `real_analytic_nowhere_dense_zeros` (the tool used everywhere
  else in this project) only gives NOWHERE DENSE, which is a strictly
  WEAKER conclusion than countable (a nowhere-dense set can still be
  uncountable, e.g. a fat Cantor set). **Do not reach for
  `real_analytic_nowhere_dense_zeros` here expecting it to give
  countability -- it won't.** The right tool is a genuine REGULAR VALUE /
  IMPLICIT FUNCTION THEOREM argument: if a map `F : R^{2n+2} \<to> R^{2n+2}`
  (built from finitely many of the scalar/vector cuts above) is shown to
  be a LOCAL DIFFEOMORPHISM (full-rank derivative) at every zero of `F` in
  the relevant region, THEN `F\<inverse>(0)` is automatically discrete (isolated
  points, by the inverse function theorem), hence countable via
  second-countability of Euclidean space -- a genuinely different (and
  available in this project's library, since `HOL-Analysis` has the
  inverse/implicit function theorem) argument shape from the nowhere-
  dense-zeros one.

**Concretely, the recommended NEXT STEP (semi-formal, not yet Isabelle):**
construct the cleanest possible characterization of condition (3) as
EXPLICIT scalar equations (mirroring how `det HessU=0` already cleanly
captures condition (2)). Since `D_x[gradU(\<cdot>,\<omega>)]` is a `2\<times>(2n)` matrix
with 2n columns (one 2-vector per antenna, `\<partial>gradU/\<partial>x_k` for each `k`),
"rank `\<le>1`" means ALL these column 2-vectors are proportional to a common
direction -- equivalently, there exists a nonzero covector `\<lambda>=(\<lambda>_1,\<lambda>_2)`
(unique up to scale, an ANGLE `\<alpha>` really) with `\<lambda>\<cdot>\<partial>_x_k[gradU]=0` for
EVERY antenna `k` simultaneously -- i.e. the SCALAR combination
`\<lambda>_1\<cdot>gradU_1(\<cdot>,\<omega>)+\<lambda>_2\<cdot>gradU_2(\<cdot>,\<omega>)` (a single real-analytic scalar
function of `x`, for `\<lambda>,\<omega>` fixed) has a CRITICAL point in `x` at the SAME
`x` where `gradU(x,\<omega>)=0` itself. This is structurally very close to the
`Phi_par`/`Phi2`-style "linear combination of `gradU`'s components" pattern
ALREADY used throughout `D34_Geodesic_Branch.thy` for OTHER rank
conditions (e.g. `Phi_par := gradU\<bullet>e_par`) -- strongly suggests reusing
(or closely mimicking) that existing machinery, parametrized by a NEW
free angle `\<lambda>` (not `e_par`, which is `\<omega>`-derived, not independently
free) rather than inventing a new formalism from scratch. Recommend:

1. Write out `\<partial>_x_k[gradU_1]` and `\<partial>_x_k[gradU_2]` in closed `Wc`-moment
   form (this project already has the general `x`-derivative-of-`gradU`
   machinery from `HessU_dip_entry_moments`-adjacent work, and from THIS
   session's own `D_x[Wc_d1(\<cdot>,c,v)](slot k u)` closed formula in \<section>6s --
   reusable almost verbatim, since `gradU`'s own `x`-derivative is exactly
   this same kind of moment-sum object one order down).
2. State "condition (3) with a free `\<lambda>`" as a genuinely NEW scalar
   equation family, and check by hand (NOT yet Isabelle) whether the
   COMBINED 5-equation system (`gradU_1=0, gradU_2=0, det HessU=0`, plus
   the two real+imaginary -- or `\<lambda>`-parametrized -- equations capturing
   condition (3)) is a regular value of SOME natural map, at least at an
   explicit witness point (matching this project's standard "exhibit a
   witness, invoke a nowhere-dense/regular-value theorem" recipe).
3. Only once (2) is checked by hand should this be formalized -- per this
   project's own repeatedly-learned lesson (\<section>6h, \<section>6m, \<section>6s all correct an
   over-eager formalization attempt).

**Division of labor recommendation**: this is squarely in Codex's current
file/session (`M5_Dev_D4Branch`); the `Wc`-moment `x`-derivative machinery
Claude built this session (\<section>6s, `M5_Dev_D3Hess`) is a reusable INPUT but
lives in a different, already-finished leaf -- Codex should cite it (once
it's confirmed to be the right closed form for `gradU`'s own `x`-Jacobian,
not just `H_par`'s) rather than re-derive it.

**Codex follow-up formal interface (same day).** In `Scratch_D4Branch.thy`,
the last `BadXGW` conjunct has now been split out into an explicit
`x`-partial derivative field:

    gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> :
      ((real^2)^'n) \<Rightarrow> real^2

with a uniqueness bridge

    (\<exists>Dx. D_x[gradU(\<cdot>,\<omega>)] = Dx \<and> surj Dx)
      \<longleftrightarrow> surj (gradU_x_partial_dip \<omega>0 \<omega>s x \<omega>).

The rank-defect condition is also now equivalent to a genuine cokernel
covector:

    gradU_x_rank_defect_dip \<omega>0 \<omega>s x \<omega>
      \<longleftrightarrow>
    (\<exists>\<lambda>\<noteq>0. \<forall>h. \<lambda> \<bullet> gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> h = 0).

The bad-angle set has been re-expressed as a projection of an explicit joint
locus:

    branchP_bad_angles V \<omega>0 \<omega>s \<Gamma>
      = snd ` branchP_joint_rank_bad V \<omega>0 \<omega>s \<Gamma>
      = snd ` (fst ` branchP_joint_cokernel_bad V \<omega>0 \<omega>s \<Gamma>).

This is exactly Claude's free-covector strategy turned into an Isabelle
interface.  The next formal unit should not try to prove countability directly
from the unquotiented covector set, because a cokernel covector is scale-free.
Instead, projectivize it into two affine covector charts, e.g. `\<lambda>=(1,a)` and
`\<lambda>=(a,1)`, prove every nonzero covector is represented in one of these
charts, and state the two corresponding `(x,\<omega>,a)` zero systems.  Those are
the right finite-dimensional systems for the hand witness / regular-value
check.

### 6r. A promising, UNEXPLORED alternative to the failed `T3rad` route for
`HessU\<equiv>0` (2026-07-12, Claude, session 4)

While reading `D34_Geodesic_Branch.thy` closely to understand \<section>6m's
negative result, found a structural fact worth flagging precisely -- NOT
yet checked to completion, but a genuinely different and possibly much
simpler route than `Jac3_H0cub`/`T3rad`.

**The key observation.** `Jac3_H0cub_identity` (already proven,
hypothesis-free) shows the FULL 3x3 rank-3 determinant collapses cleanly:

    Jac3_H0cub x \<omega> \<omega>0 \<omega>s i j k
      = -(D_x[gradU_2](slot k (perp2 c))) * Lambda_cub_ij x \<omega> \<omega>0 \<omega>s i j

where `Lambda_cub_ij` is just a 2x2 determinant of `(Phi_par, T3rad)`
x-derivatives along slots `i,j`. The proof needs exactly TWO ingredients:
`Phi_par_perp_slot_zero` (already have, general) and `T3rad_slot_perp_zero`
(already have, specific to `T3rad`). \<section>6m's finding was that `T3rad`'s OWN
level set doesn't match `HessU\<equiv>0`'s fibre (the row-reduction from `H_par`
to `T3rad` fails) -- but this is a fact about `T3rad` SPECIFICALLY, not
about the Jac3-factorization TECHNIQUE itself.

**The alternative**: build the analogous determinant using `H_par` (which
DOES literally vanish on the fibre, `H_par_zero_of_HessU_zero`, already
proven) as the third row INSTEAD of `T3rad` -- i.e. differentiate `H_par`
in `x`, not `T3rad`. If an analogous `H_par_slot_perp_zero`-type fact holds
(need: `D_x[H_par](slot k (perp2 c)) = 0`), the identical factorization
argument goes through mechanically (the `Jac3_H0cub_identity` proof is
short and would transfer almost verbatim), reducing the whole question to
a 2x2 `Lambda_par_ij` (determinant of `Phi_par`/`H_par` x-derivative rows)
being nonzero somewhere -- avoiding `T3rad`/§6m's obstruction ENTIRELY,
since we would never need to relate `H_par` to `T3rad` at all.

**What's NOT yet checked (genuinely open, not just unformalized)**:

1. **Does `H_par` (not the already-defined `Hrad2 := H_par - gain*Wc_d1(x,c;
   D\<^sup>2c(e_par,e_par))`) actually have the needed perp-slot-zero property?**
   Searched: no `H_par_slot_perp_zero`-shaped fact exists anywhere in the
   codebase. `Hrad2` DOES have this property (`Hrad2_slot_perp_zero`,
   already proven) -- but `Hrad2` is a DIFFERENT quantity from `H_par`
   (subtracting one specific term), and it is NOT yet checked whether
   `Hrad2=0` follows from `HessU\<equiv>0` the way `H_par=0` does
   (`H_par_zero_of_HessU_zero` is about `H_par`, not `Hrad2` -- the
   subtracted term `gain*Wc_d1(x,c;D\<^sup>2c(e_par,e_par))` is NOT obviously
   forced to vanish just because `HessU\<equiv>0`, unlike the special `V=0`
   sub-case in \<section>6a where an extra `\<nabla>_cV=0` fact killed it for a
   different reason). Two sub-cases to actually check by hand:
   (a) does `H_par` itself have a perp-slot-zero property (if yes, use
   `H_par` directly, simplest); (b) if not, does `Hrad2=0` genuinely
   follow from `HessU\<equiv>0` (if yes, use `Hrad2` instead, reusing the
   ALREADY-PROVEN `Hrad2_slot_perp_zero`).
2. **Even granting either (a) or (b), is `Lambda_par_ij` (or `Lambda_
   Hrad2_ij`) actually nonzero somewhere** -- a genericity computation of
   comparable scope to `Jac3_H0cub`'s own `Lambda_cub_ij_nonzero`-style
   result (not yet located/checked whether an analogous fact for a
   QUADRATIC, not cubic, invariant is easier or harder to establish).

**Why this is worth prioritizing over re-deriving a T3rad-compatible row
reduction**: `H_par`/`Hrad2` are SECOND-order (quadratic-in-`c`) objects
with an ALREADY-CLOSED radial form (`H_par_radial_dictionary`), one order
simpler than `T3rad`'s cubic jet -- if either (1) checks out, the whole
`HessU\<equiv>0` residual's remaining work shrinks from "new cubic-jet
infrastructure + a new row-reduction" (§6m's now-abandoned estimate) down
to "one genericity computation on an object we already have a closed form
for." Recommend (1) as literally the next hand-computation, before writing
any Isabelle: does `D_x[H_par](slot k (perp2 c)) = 0` hold in general
(check via `H_par_radial_dictionary`'s own closed form + the general
`Wc_d1`/`Wc_dd` x-derivative machinery already used throughout this
session), or does it need the `Hrad2` correction?

### 6s. §6r resolved (negatively, with a new positive structural finding):
neither `H_par` nor `Hrad2` gives a clean rank-3 witness in general -- but
an exact closed formula for the obstruction, plus a genuine sub-case where
it disappears (2026-07-12, Claude, session 4)

Worked through both open items from \<section>6r by hand.

**(1) Does `H_par` have the perp-slot-zero property?** Computed directly
from `H_par_radial_dictionary`'s own four terms. Three of the four
(`Wc(x,c)`, `Wc_d1(x,c;c)`, `Wc_dd(x,c;c,c)`) depend on `x` ONLY through
inner products against `c` itself, hence are exactly invariant under moving
any single antenna by `perp2(c)` (since `c\<bullet>perp2(c)=0`) -- their
`x`-derivative along `slot k (perp2 c)` is 0, by the SAME mechanism as
`Phi_par_perp_slot_zero`. The FOURTH term, `g\<cdot>Wc_d1(x,c;D\<^sup>2c(e_par,e_par))`,
is the odd one out: its "outer" linear factor is `D\<^sup>2c(e_par,e_par)`, a
DIFFERENT vector from `c` in general, so it is NOT perp2(c)-invariant.
Derived the exact general formula (elementary product-rule expansion of
the double pair-sum defining `Wc_d1`):

    D_x[Wc_d1(\<cdot>,c,v)](slot k u) = -2(v\<bullet>u)\<cdot>\<Sigma>_{j\<neq>k} sin(c\<bullet>(x_k-x_j))     when c\<bullet>u=0

(the `cos(...)\<cdot>(c\<bullet>u)` half of the product rule drops identically when
`u\<bullet>c=0`, e.g. `u=perp2(c)`). Hence, exactly:

    D_x[H_par](slot k (perp2 c)) = -2g\<cdot>(D\<^sup>2c(e_par,e_par)\<bullet>perp2(c))\<cdot>\<Sigma>_{j\<neq>k}sin(c\<bullet>(x_k-x_j))

**Answer: NO, not in general.** `D\<^sup>2c(e_par,e_par)\<bullet>perp2(c)` (a pure
angle-only quantity, computed explicitly from `D2cvec_dip_def` at the
Robust4 steering constants) is GENERICALLY NONZERO -- numerically checked,
15 random `(\<theta>,\<psi>)` samples in the design box, zero hits: 0/15, values
ranging `\<approx>` -3.4 to 8.6.

**(2) Does `Hrad2=0` follow from `HessU\<equiv>0`?** NO. Worked through the full
critical-point moment formula (`HessU_dip_entry_moments_crit`, all THREE
independent entries `HessU$1$1,$1$2,$2$2` in the standard `axis(1)/axis(2)`
basis, using bilinearity of `D\<^sup>2c` and `Hc` to relate them to `H_par` via
`e_par = e_par$1\<cdot>axis(1)+e_par$2\<cdot>axis(2)`). The three `HessU\<equiv>0` equations
determine `Dc(axis_i)\<bullet>Hc\<bullet>Dc(axis_j)` (the c-space-pullback quantities) in
terms of the `D\<^sup>2c(axis_i,axis_j)\<bullet>\<nabla>_cWc` quantities and `K\<cdot>V` -- but this
is 3 equations relating (effectively) 7 unknowns; `Wc_d1(x,c;D\<^sup>2c(e_par,
e_par))` itself is NOT pinned to any specific value, in particular not
forced to 0. Concretely: `Hrad2 = -g\<cdot>Wc_d1(x,c;D\<^sup>2c(e_par,e_par))`
EXACTLY, given `HessU\<equiv>0` (using `H_par=0` to eliminate the `c\<bullet>Hc\<bullet>c`
piece) -- i.e. `Hrad2` on the `HessU\<equiv>0` fibre is EXACTLY the same free,
generically-nonzero quantity that broke `H_par`'s own perp-slot property
in (1). `Hrad2` was very likely built for a DIFFERENT purpose in this
codebase (plausibly the rank-1, not rank-0, stratum), not for `HessU\<equiv>0`.

**Net: this is a genuine structural obstruction, parallel in spirit to
\<section>6m's `T3rad` finding but with a different shape** -- the quantity that
provably vanishes on the fibre (`H_par`) lacks the clean derivative
structure needed for the Jac3-style cofactor trick; the quantity WITH
clean derivative structure (`Hrad2`) does not vanish on the fibre. No
single existing scalar invariant in this codebase has both properties
simultaneously.

**One genuine positive finding: at `\<psi>0=0` exactly, the obstruction
vanishes.** Checked both numerically (values `\<approx>1e-10`, floating-point
noise) AND symbolically (`sympy.simplify` at `\<psi>=0` gives literally `0`):
`D\<^sup>2c(e_par,e_par)\<bullet>perp2(c) \<equiv> 0` at `\<psi>0=0`. This means `H_par` GENUINELY
has the perp-slot-zero property there, and the ENTIRE
`Jac3_H0cub_identity`-style factorization argument (with `H_par` replacing
`T3rad`) would go through cleanly -- but only on this thin (codimension-1)
sub-locus, matching the SAME `\<psi>0=0` special case already flagged as
structurally distinguished in \<section>6e/\<section>6f/\<section>6g (`Dc` diagonal there, mirror
symmetry). On its own this covers a measure-zero slice of the arc, not
the general case -- low standalone value unless combined with a resolution
of the `\<psi>\<neq>0` case.

**Honest assessment of what's left, for whoever continues:** the `\<psi>\<neq>0`
case genuinely needs one of: (a) a FULL (non-factored) 3x3 rank-3
genericity computation directly on `(Phi_par, gradU_2, H_par)`'s Jacobian
(no clean cofactor-expansion shortcut available, since `H_par`'s own
perp-slot entry is nonzero) -- comparable in scope to the ORIGINAL
`Jac3_H12rad`/`Jac3_H0cub` Tier-6 work, i.e. a genuine new "Tier," not a
quick finish; or (b) abandoning the `Jac3`-factorization TECHNIQUE
entirely and pursuing the OTHER fallback already on record (\<section>7's own:
prove countability/isolation of the bad-angle set directly, reusing the
UNCONDITIONAL `fixed_omega_H0core_chart_core_robust4_all_angles` per-angle
result, without needing an x-space rank-3 witness at all). Given (a)'s
now-confirmed lack of a shortcut, (b) looks relatively more attractive
than it did before this check -- worth a dedicated look next, rather than
continuing to invest in the `Jac3`-style route.

Not formalized this pass (deliberately -- this was hand-analysis, per this
project's own "sketch before formalize" discipline, specifically because
\<section>6h/\<section>6m both already demonstrate the cost of formalizing a plausible-
looking but ultimately-wrong construction). The `D2c(e_par,e_par)\<bullet>perp2(c)`
closed-form computation (\<section>6e-style: explicit at Robust4, `\<psi>0=0` special
case) is ready to formalize as-is if the `\<psi>0=0` sub-case turns out to be
needed later; the general-`\<psi>` rank-3 computation is not yet even sketched
in enough detail to start writing Isabelle.

### 7b. Concrete recipe for the two projective covector charts (2026-07-12,
Claude, session 4/5): what `\<Psi>_a` should BE, and a dimension count that
predicts the target is achievable

Following up on Codex's \<section>7a follow-up (line ~2312): the next formal unit
is to projectivize `gradU_x_rank_defect_dip`'s free covector `\<lambda>\<noteq>0` into the
two affine charts `\<lambda>=(1,a)` and `\<lambda>=(a,1)`. Here is the concrete scalar
object each chart reduces to, plus a dimension count that says this SHOULD
work (i.e. is worth the formalization cost), before any Isabelle is written.

**What `\<Psi>_a` is.** In chart A (`\<lambda>=(1,a)`), unwinding
`gradU_x_rank_defect_dip`'s defining condition
`\<forall>h. \<lambda>\<bullet>gradU_x_partial_dip \<omega>0 \<omega>s x \<omega> h = 0` antenna-by-antenna: for every
antenna `k`, `\<partial>_{x_k}[gradU_1](x,\<omega>) + a\<cdot>\<partial>_{x_k}[gradU_2](x,\<omega>) = 0` (a
`real^2`-valued equation per antenna, since `x_k` is a `real^2` slot). This
is EXACTLY saying: the full `x`-gradient of the single new scalar function

    \<Psi>_a(x,\<omega>) := gradU_1(x,\<omega>) + a \<cdot> gradU_2(x,\<omega>)

vanishes at `x` -- i.e. `x` is a critical point (in the FULL `2n`-dim `x`
variable, not a per-antenna or per-slot statement) of `\<Psi>_a(\<cdot>,\<omega>)`. This is
structurally identical to how `Phi_par := gradU\<bullet>e_par` is already built and
used throughout `D34_Geodesic_Branch.thy`, except the direction `e_par`
(`\<omega>`-derived) is replaced by the FREE direction `(1,a)`. Chart B
(`\<lambda>=(a,1)`) is the same construction with `\<Psi>'_a := a\<cdot>gradU_1 + gradU_2`.
Recommend defining `Psi_a_dip` (or similar) exactly this way, and reusing
`Phi_par`'s existing `x`-derivative machinery as a template (same shape of
argument, different direction vector).

**The full chart-A system to check for a regular value.** The joint locus
(matching `branchP_joint_cokernel_bad`, chart-A slice) in `(x,\<omega>,a)` is

    gradU_1(x,\<omega>) = 0  \<and>  gradU_2(x,\<omega>) = 0  \<and>  \<nabla>_x[\<Psi>_a(\<cdot>,\<omega>)](x) = 0

where the last conjunct is `2n` scalar equations (one real equation per
`x`-coordinate, `n` antennas `\<times>` 2 coordinates each). So: `2 + 2n` equations
total, in `(x,\<omega>,a) \<in> (real^2)^n \<times> real^2 \<times> real`, i.e. `2n + 3` unknowns.
Generic (regular-value) expectation: a `((2n+3)-(2n+2))=1`-dimensional
solution set in `(x,\<omega>,a)`-space. Projecting away `a` and intersecting `\<omega>`
with the 1-dimensional arc `OmegaPF ctr \<delta>` generically leaves an ISOLATED
(0-dimensional) set of bad `\<omega>`'s -- i.e. exactly what `countable_bad` needs,
and it matches the earlier back-of-envelope count already on record
(\<section>7a: `2+1+(2n-1)=2n+2`). Two independent dimension counts agreeing is a
good sign this is the right formal target, not just a plausible one.

**Concrete next steps for Codex, in order:**

1. Derive closed `Wc`-moment forms for `D_x[gradU_1](slot k u)` and
   `D_x[gradU_2](slot k u)` (general `u`, not just `perp2 c`) -- this is the
   `x`-derivative of `gradU` ONE order down from `HessU`, so it should reuse
   the SAME product-rule expansion technique as \<section>6s's
   `D_x[Wc_d1(\<cdot>,c,v)](slot k u)` formula (that computation is a template,
   not a dead end -- \<section>6s's negative result was specifically about
   `H_par`/`Hrad2`'s perp-slot property, not about this expansion technique
   itself).
2. Define `Psi_a_dip` and `Psi'_a_dip` (chart A / chart B) as above, and
   state the `2n+2`-equation joint system in each chart as an explicit
   Isabelle predicate (mirroring `branchP_joint_cokernel_bad`'s existing
   shape, specialized to each chart).
3. BEFORE formalizing a genericity/regular-value proof: hand/sympy-check
   the Jacobian of the full `(2n+2)`-equation system (w.r.t. `(x,\<omega>,a)`) at
   an EXPLICIT witness point at the Robust4 design constants (same recipe
   as `Jac3_H0cub_nonzero_in_open_robust4_witness`), for the smallest
   nontrivial `n` (`n=2` or `3`) first. Only formalize once this hand-check
   is positive -- per \<section>6h/\<section>6m/\<section>6s's repeated lesson about the cost of
   formalizing an unverified construction.
4. If the Jacobian check is positive: the countability conclusion follows
   from a regular-value/IFT-style local-discreteness argument (each
   solution is isolated in `(x,\<omega>,a)`, hence the projection to `\<omega>` on any
   compact piece of the arc is finite, hence the full countable union over
   compact exhaustion of the arc is countable) -- structurally the SAME
   kind of argument already used for `charts_core_Nn`/regular-value chart
   covers elsewhere in this codebase, not a new proof technique.

**Division of labor**: this whole section is Codex's file/session
(`M5_Dev_D4Branch`); nothing here needs touching `M5_Dev_D3Hess` or
`M5_Dev_D3Assembly` (both finished, do not edit).

### 7c. D4 ownership transferred to Claude alone; §7b's perp-slot brick landed
sorry-free; the GENERAL (non-perp) slot formula, sympy-verified (2026-07-12,
Claude, session 5)

Per the user's explicit instruction, D4 (`M5_Dev_D4Branch/Scratch_D4Branch.thy`)
is now Claude's alone -- no more Codex handoffs on this file. Codex's two
remaining sorries (`branchP_bad_angles_eq_snd_image_joint_rank_bad`,
`branchP_joint_rank_bad_eq_fst_image_joint_cokernel_bad`) are CLOSED (see
diary 2026-07-12). `\<section>7b`'s plan is now under direct formalization.

**Landed (sorry-free, forced rebuild BUILD_EXIT=0):** `Psi_a_dip`,
`Psi_a_x_partial_dip`, `Psi_a_dip_has_derivative`, and the perp-slot value
theorem `Psi_a_dip_xderiv_perp_slot` -- for `v` with `c\<bullet>v=0`:

    \<partial>\<^bsub>slot m v\<^esub> \<Psi>\<^sub>a = 2g\<cdot>((\<gamma>\<^sub>1+a\<gamma>\<^sub>2)\<bullet>v)\<cdot>Im(cnj A\<cdot>\<phi>\<^sub>m)

reusing the ALREADY-PROVEN `gradU_dip_xderiv_perp_slot` from
`D34_Analytic_Bridge.thy` (reachable via `Scratch_Wiring`'s existing
`imports "Applied_Math_D34_Analytic.D34_H0res_Branch"`). This is only HALF
the picture (perp `v` only); the rank-defect condition `\<forall>h. ...=0` needs
EVERY `v`, not just perp ones.

**The general (unrestricted `v`) formula, sympy-verified against the raw
`dEjm` definition (script: `psi_a_parallel.py`, all three components matched
exactly, `sp.simplify(...) == 0`).** Writing `A=M_paper x c$1`,
`M\<^sub>1=M_paper x c$2`, `M\<^sub>2=M_paper x c$3`, `\<phi>\<^sub>m=phase c x m`,
`\<kappa>\<^sub>v := c\<bullet>v` (NOT restricted to 0 this time), `x\<^sub>m := x$m`:

    dEjm p g c\<^sub>1 c\<^sub>2 (M_paper x c) (DM_paper_x x c (slot m v)) = p\<cdot>T\<^sub>1 + g\<cdot>(c\<^sub>1\<cdot>T\<^sub>2+c\<^sub>2\<cdot>T\<^sub>3)

    T\<^sub>1 = 2\<kappa>\<^sub>v\<cdot>Im(cnj A\<cdot>\<phi>\<^sub>m)
    T\<^sub>2 = 2\<kappa>\<^sub>v\<cdot>Re(cnj \<phi>\<^sub>m\<cdot>M\<^sub>1) + 2v\<^sub>1\<cdot>Im(cnj A\<cdot>\<phi>\<^sub>m) - 2\<kappa>\<^sub>v\<cdot>(x\<^sub>m)\<^sub>1\<cdot>Re(cnj A\<cdot>\<phi>\<^sub>m)
    T\<^sub>3 = 2\<kappa>\<^sub>v\<cdot>Re(cnj \<phi>\<^sub>m\<cdot>M\<^sub>2) + 2v\<^sub>2\<cdot>Im(cnj A\<cdot>\<phi>\<^sub>m) - 2\<kappa>\<^sub>v\<cdot>(x\<^sub>m)\<^sub>2\<cdot>Re(cnj A\<cdot>\<phi>\<^sub>m)

At `\<kappa>\<^sub>v=0` (perp case) this collapses to `T\<^sub>1=0`, `T\<^sub>2=2v\<^sub>1 Im(cnj A\<phi>\<^sub>m)`,
`T\<^sub>3=2v\<^sub>2 Im(cnj A\<phi>\<^sub>m)`, recovering the already-proven perp result exactly
(good consistency check). `gradU`'s own `j`-component slot value is
`p\<^sub>j\<cdot>T\<^sub>1 + g\<cdot>((\<gamma>\<^sub>j)\<^sub>1 T\<^sub>2 + (\<gamma>\<^sub>j)\<^sub>2 T\<^sub>3)` (`p\<^sub>1=gdip'(\<theta>)`, `p\<^sub>2=0`, `\<gamma>\<^sub>j=Dcvec_dip(axis j)`
as before), and `\<Psi>_a`'s slot value is the `(1,a)`-combination of the two
`j`-rows, exactly as in the perp case.

**Formalization plan (not yet attempted -- the RHS is large: three `Re`/`Im`
cross-terms per component, and the earlier perp-slot proof already showed
that a blanket `simp`/`auto` mixing complex-number expansion with real
`algebra_simps` produces spurious asymmetric partial expansions).**
Recommended proof shape, learned from that near-miss: unfold `dEjm_def` and
substitute `d_A_moment_x_slot`/`d_M1_moment_x_slot`/`d_M2_moment_x_slot`
(the GENERAL, already-proven, non-perp slot lemmas -- no need for
`dEjm_zero1`'s shortcut here) via a targeted `simp only:`, get to a raw
`Re`/`Im`/`cnj`/`phase` expression, and ONLY THEN do one clean
`simp add: algebra_simps` (or, if that reflows unevenly again, an explicit
`Re`/`Im`-component `have`-chain matching the sympy derivation term-by-term)
-- never mix the "substitute definitions" step and the "regroup terms" step
in one call.

**Division of labor**: none needed now -- Claude owns this file solely per
the user's instruction. This entry is itself the semi-formal half of the
cycle for the NEXT formal step (the general slot theorem); formalize next.

### 7d. NEGATIVE finding: the chart-A `(2n+2)`-equation system is NEVER a
regular value -- the §7a/§7b dimension count was wrong, a genuine structural
rank defect of (at least) 3 (2026-07-12, Claude, session 5)

Per the user's request, did the §7b step-3 hand-check (numerically/high-
precision, scripts in the scratchpad dir: `d4_witness.py`, `d4_witness2.py`,
`d4_witness_exact.py`/`_exact2.py`, `d4_probe_n2.py`, `d4_multi_seed.py`)
BEFORE writing any more Isabelle. Built the exact chart-A system
`F(x,\<omega>,a) = (gradU_1, gradU_2, D_x[\<Psi>_a])` (the `2n+2`-equation system from
\<section>7b/\<section>7c, using `gradU_dip_component_moments`'s own closed form directly,
cross-checked against the just-formalized `Psi_a_dip_xderiv_slot`) at the
Robust4 design constants (`\<omega>0=(\<pi>/2,0), \<omega>s=(0,0)`).

**Method**: numerically solved `F=0` from many random starts (`scipy.
least_squares`), for `n=2,3,4` antennas, filtering out solutions at/near the
steering center `\<omega>0` (where `c=0` identically -- a genuinely degenerate
corner, not a useful witness) and near `sin\<theta>=0` (a pole of `edip`, also
degenerate). For EVERY converged, non-degenerate witness found (60 random
trials each, `n=2,3,4`), computed the FULL `(2n+2)\<times>(2n+3)` Jacobian of `F`
and its rank via SVD. One `n=3` witness was independently re-verified at
50-digit precision (sympy-exact `F`, `mpmath` Newton refinement to residual
`\<approx>1.5e-50`, then a 50-digit finite-difference Jacobian) to rule out any
finite-difference noise artifact -- the smallest 4 of 8 singular values sat
at `\<approx>1e-26`--`1e-51` (18 to 43 orders of magnitude below the top 4, which
were `\<approx>2.6`--`14.4`): a genuine, unambiguous rank of 4, not 8.

**The pattern is consistent, not a fluke of one witness.** Across ALL
non-degenerate witnesses found for `n=2,3,4` (rank histograms: `n=2\<rightarrow>`max 3
of 6 needed; `n=3\<rightarrow>`max 5 of 8 needed; `n=4\<rightarrow>`max 7 of 10 needed), the
MAXIMUM rank ever achieved was exactly `2n-1` -- i.e. a rank defect of
EXACTLY 3 below the needed `2n+2`, for every `n` tried. This is far too
regular to be a search-coverage artifact; it is a genuine ALGEBRAIC
identity relating the `2n+2` equations, present for every `n`.

**A structural clue, not yet a full explanation.** At the high-precision
`n=3` witness, the LEFT singular vectors (the near-null row-combinations)
all have their `gradU_1` and `gradU_2` weights EXACTLY opposite (`c` and
`-c`), and the RIGHT singular vectors (near-null directions in the domain)
all have ESSENTIALLY ZERO `\<theta>,\<phi>,a` component -- the rank defect lives
entirely in a 4-dimensional subspace of pure `x`-perturbations that leaves
`F` unchanged to high order. The witness itself had `a=-1` EXACTLY (not a
coincidence of rounding -- the Newton solve converged there from an
unconstrained start), meaning `\<Psi>_{-1} = gradU_1 - gradU_2` at this witness;
worth investigating whether `a=-1` specifically (or some other clean value)
is itself forced by a Schwarz-symmetry-type identity among the mixed
`x`,`\<omega>`-partials of `U`, which could explain both the `a=-1` attractor AND
the rank-3 defect via one shared mechanism. NOT yet worked out.

**Conclusion: the naive "stack `gradU=0` and `D_x[\<Psi>_a]=0`, hope for a
regular value" plan from \<section>7a/\<section>7b does NOT work as stated** -- this is a
genuine negative finding, of the same character as \<section>6m (`T3rad` row
reduction) and \<section>6s (`H_par`/`Hrad2` perp-slot obstruction): a plausible-
looking dimension count that does not survive an actual hand/numerical
check. Per this project's own repeated discipline, NOT formalized (would
have wasted real Isabelle effort chasing a system that structurally cannot
be a regular value).

**What's still salvageable.** The `Psi_a_dip_xderiv_slot`/`gradU_dip_xderiv_
slot`/`dEjm_slot_value` closed-form machinery landed this session is
CORRECT and reusable regardless -- it is exact, sympy-verified, and
sorry-free; the negative finding is about the SPECIFIC equation system built
from it, not about the closed forms themselves. Two live options for the
next semi-formal pass, both worth exploring before picking one:
  1. Chase the rank-3 identity to understand it exactly (likely a genuine,
     provable algebraic fact, e.g. via Euler-homogeneity or Schwarz symmetry
     of `U`'s mixed partials) and use it to build a CORRECTED, smaller
     equation system with the redundant 3 rows already removed -- if the
     resulting `(2n-1)`-equation system (matching the observed max rank) IS
     a regular value, the SAME countability conclusion follows, just via a
     smaller/cleaner map.
  2. Fall back to \<section>6s's own recommendation (already on record, made
     BEFORE this chart-A detour): prove countability/isolation of the bad-
     angle set directly by reusing the UNCONDITIONAL
     `fixed_omega_H0core_chart_core_robust4_all_angles` per-angle result,
     without needing an `x`-space rank-3 (or rank-`(2n+2)`) witness at all.
     Given the chart-A route's now-confirmed structural obstruction, this
     looks more attractive again.

### 7e. Correction to \<section>7d's fallback, and a genuinely promising POSITIVE
result: Codex's round-1 `gradU_regular_value` reduction (already proven,
unused) needs a MUCH weaker condition than the dead chart-A system
(2026-07-12, Claude, session 5)

Went to start on option (2) above and discovered it was based on a
misreading: `fixed_omega_H0core_chart_core_robust4_all_angles`
(`M5_Dev_Wiring/Scratch_Wiring.thy:2881`) is D3's OWN arc-ENDPOINT lemma
(used in `M5_Dev_ArcWiring/Scratch_ArcWiring.thy` to discharge the `left`/
`right` obligations of `d3_chart_core_all_of_analytic_arc_pointwise_arc_
schur_patches`, D3's separate arc-cover-seam problem) -- it does NOT
directly bootstrap D4's `countable_bad`/`branchP_bad_angles` machinery.
Correcting the record here so this isn't re-attempted the same way twice.

**What IS already sitting proven and unused in `Scratch_D4Branch.thy`,
lines 560-607 and 1020-1043 (Codex's ORIGINAL round-1 work, from before the
`gradU_x_partial_dip`/cokernel detour):**
`branchP_indep_closed_cover_core_of_gradU_regular_value` reduces
`branchP_indep_closed_cover_core V \<omega>0 \<omega>s \<Gamma>` to a SINGLE hypothesis:
`regular_value_on (\<lambda>p. gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))
(V \<times> \<Omega>) 0` for some open `\<Omega>\<supseteq>\<Gamma>` -- i.e. `0` is a regular value of `gradU`
treated as a map on the JOINT `(x,\<omega>)`-space, `V\<times>\<Omega> \<subseteq> (real^2)^n \<times> real^2`.
Concretely: wherever `gradU(x,\<omega>)=0`, the FULL `2\<times>(2n+2)` Jacobian
`D_{(x,\<omega>)}[gradU]` (BOTH the `x`-block AND the `\<omega>`-block, i.e. `HessU`,
together) must have rank 2 (be surjective onto `real^2`).

**Why this is a MUCH weaker, more tractable condition than \<section>7d's dead
system**: \<section>7d needed the `x`-ONLY block to have rank `2n` essentially
(the full `2n+2` system including `\<Psi>_a`'s Hessian). HERE we only need the
COMBINED `x`-block (`2\<times>2n`) and `\<omega>`-block (`HessU`, `2\<times>2`) to jointly span
`real^2` -- i.e. even if EITHER block alone is degenerate (e.g. `det
HessU=0`, `BadXGW`'s own defining condition), the OTHER block's leftover
rank-1 direction just needs to not coincide with the first's. This is a
completely different, much easier kind of genericity claim, and it does
NOT conflict with `BadXGW` containing points where `det HessU=0` and the
`x`-block ALSO has rank `\<le>1` -- those two rank-1 pieces can still jointly
span `real^2` unless their single directions happen to EXACTLY coincide.

**How the reduction actually works (worth having explicit, since it wasn't
obvious on first read): this is a classical Sard argument, not a direct
attack on `BadXGW`.** `charts_core_Nn` (used internally,
lines 599-604) does NOT need the map to avoid `BadXGW`-type points at all.
Given `regular_value_on gradU (V\<times>\<Omega>) 0`, the zero set `{(x,\<omega>):gradU=0}`
is (by the ordinary implicit function theorem) a smooth `2n`-dimensional
submanifold of `V\<times>\<Omega>`. `charts_core_Nn` then applies SARD'S THEOREM to the
coordinate PROJECTION of this submanifold onto `x`-space: the critical
points of THAT projection are EXACTLY where the submanifold's tangent space
fails to project isomorphically, i.e. exactly where `det HessU=0` (i.e.
`gradU_engine_bad`, `BadXGW`'s natural superset) -- and Sard's theorem says
the projection's critical VALUES (i.e. the bad `x`'s themselves) are
negligible in `x`-space, regardless of what the `x`-block's OWN rank is at
those points. This is the SAME "exhibit a regular value, invoke Sard" recipe
used everywhere else in this codebase, just one level removed from
`BadXGW` itself.

**Numerical check (Robust4 design, `d4_joint_regvalue.py` in scratchpad):**
solved `gradU(x,\<omega>)=0` from random starts for `n=2,3,4` antennas (a MUCH
less constrained search than \<section>7d's dead system -- just 2 equations),
filtered degenerate witnesses (`\<omega>` near `\<omega>0` where `c=0`, `sin\<theta>` near 0),
and checked the `2\<times>(2n+2)` joint Jacobian's rank via SVD. Result: `n=3,4`
achieved rank 2 (full) at EVERY one of ~20-22 non-degenerate witnesses
found; `n=2` achieved rank 2 at 13/19 (rank 1 the rest, plausibly just
`n=2`'s smaller configuration space being more special, not a structural
obstruction). This is the OPPOSITE pattern from \<section>7d -- genericity here
looks real, not illusory.

**What's actually still needed (the honest remaining scope, not yet
started).** `regular_value_on gradU (V\<times>\<Omega>) 0` needs to be proven
ANALYTICALLY (not just numerically spot-checked) for the Robust4 design, on
some `V,\<Omega>` covering every independent `\<Gamma>`. Natural case split at a zero
`(x,\<omega>)`:
  (a) `det HessU(x,\<omega>) \<noteq> 0`: the `\<omega>`-block alone is already invertible, so
      the joint Jacobian is trivially surjective (a sub-block of a matrix
      being surjective onto the codomain, using only a subset of input
      coordinates, forces the full matrix to be surjective too) -- this
      should be a short, easy lemma, essentially free given `HessU_explicit`
      and the existing `not_surj_omega_deriv_iff_detHess_dip` bridge.
  (b) `det HessU(x,\<omega>) = 0` (i.e. `x \<in> D3BadXG_H0core`-type locus): need the
      `x`-block to supply a rank-1 direction NOT collinear with `HessU`'s
      own rank-1 leftover direction. This is the genuinely open part --
      structurally similar in spirit to (but a different claim from) D3's
      own `Jac3_H0cub`-style rank-3 genericity work, so likely comparable
      effort, NOT a quick finish. Not yet attempted; the RIGHT next semi-
      formal step is a hand/sympy genericity check of JUST this sub-case
      (fix `det HessU=0`, ask whether the `x`-block's leftover direction can
      degenerate to exactly `HessU`'s leftover direction) before writing any
      Isabelle for it.

**Division of labor / status**: Claude owns this file solely. This
supersedes \<section>7a-\<section>7d's chart-A route entirely as the active plan; the
`Psi_a_dip`/`gradU_dip_xderiv_slot` machinery from \<section>7c stays in the file
(correct, reusable if ever needed) but is no longer on the critical path.

### 7f. Case (a) landed (sorry-free, batch-verified); case (b) numerics point
to a striking, unresolved structural finding: `gradU=0 \<and> det HessU=0`
appears to FORCE phase-alignment (2026-07-12, Claude, session 5)

**Case (a) DONE.** `joint_regular_of_detHessU_nonzero` is in
`Scratch_D4Branch.thy`, sorry-free, independently batch-verified
(`BUILD_EXIT=0`). Built the joint `(x,\<omega>)` derivative explicitly via
`has_derivative_partialsI` (same construction as `gradU_dip_joint_C1`, but
keeping the formula local/visible), then surjectivity follows directly
from `det HessU\<noteq>0` via `surj_matrix_vector_iff_det` plus the elementary
"a linear map on a product space is surjective if its restriction to one
factor already is" fact.

**Case (b) investigation (`d4_caseb.py`, `d4_caseb_diag.py`,
`d4_caseb_fast.py`, `d4_caseb_nonaligned.py`, scratchpad).** Searched for
witnesses with `gradU(x,\<omega>)=0 \<and> det HessU(x,\<omega>)=0` (the `D3BadXG_H0core`
locus) at the Robust4 design, for `n=2,3,4`, and checked BOTH the `x`-block
rank AND the joint `2\<times>(2n+2)` rank there. First pass (unconstrained random
search): every non-degenerate witness found (10/10 for `n=2`, 1/1 for
`n=4`) had `rank_x=1` AND `rank_joint=1` -- i.e. the joint map is NOT
regular at these points, and moreover the `x`-block's leftover direction
coincides EXACTLY with `HessU`'s own leftover direction (not just both
individually rank-deficient, but COLLINEAR).

Diagnosed WHY before treating this as structural (matching the earlier
lesson from the dead-end `\<theta>=\<phi>=\<pi>/2` solver attractor): checked
`Im(cnj A\<cdot>\<phi>_m)` (the phase-alignment quantity from \<section>7c/\<section>7e) at every
witness -- ALL were phase-aligned to `\<approx>1e-10`--`1e-13` for every antenna.
Tried explicitly PUSHING the solver away from phase-alignment (an extra
penalty term targeting a random nonzero misalignment pattern, `scale=1.0`
to `5.0`, up to 60 trials at `n=3`): either the solver failed to converge
at all (residual stayed large -- suggesting no nearby non-aligned solution
to `gradU=0\<and>det HessU=0` exists), or it snapped back to a degenerate
`\<theta>=\<pi>` point (a genuine pole of `edip`, filtered out) or to phase-alignment
anyway. Zero non-aligned, non-degenerate witnesses found across all
attempts.

**This is now a striking (not yet explained) finding, not obviously a
search artifact**: `gradU=0 \<and> det HessU=0` at the Robust4 design may
UNCONDITIONALLY force phase-alignment (`Im(cnj A\<cdot>\<phi>_m)=0` for every
antenna `m`) -- and if so, the joint-regular-value route (Codex's round-1
plan, \<section>7e) is ALSO structurally blocked, exactly on `D3BadXG_H0core`
(`BadXGW`'s superset), for the SAME reason the chart-A route (\<section>7d) died:
another hidden algebraic identity, this time linking `HessU`'s degeneracy
directly to phase-alignment.

**A plausible mechanism, not yet checked**: this project already has
`H_par_zero_of_HessU_zero` (cited in \<section>6s, unconditional: `HessU\<equiv>0`
implies `H_par=0` -- though note that's the STRONGER `HessU\<equiv>0` condition,
not just `det HessU=0`; may need a weaker version). If `det HessU=0` (not
full vanishing) ALSO forces some related quantity to zero, and THAT
quantity's vanishing is equivalent to (or implies) phase-alignment, this
would explain the numerics without being a coincidence. Worth checking by
hand: does `det HessU=0` (as opposed to `HessU\<equiv>0`) already pin down enough
of the `HessU_dip_entry_moments` structure to force
`Im(cnj A\<cdot>\<phi>_m)=0` for every `m`? NOT yet attempted -- this is the honest
next semi-formal step, and it is a genuine hand-derivation task, not a
quick numerical spot-check (the numerics have already been pushed hard).

**Status / open decision**: two live paths, neither started:
  1. Chase the mechanism above analytically (comparable effort to D3's own
     `H_par`/`Hrad2`/`Jac3_H0cub` investigations, \<section>6r/\<section>6s) -- if it
     resolves cleanly, it may hand back BOTH case (b) AND a cleaner
     understanding of `D3BadXG_H0core`'s own structure for free.
  2. Reconsider whether `charts_core_Nn`'s joint-(x,\<omega>) route can be
     RESCUED despite this -- e.g. by choosing `V,\<Omega>` to exclude a thin
     neighborhood of the phase-aligned locus and handling THAT locus with a
     separate, smaller argument (if phase-alignment is itself a
     lower-dimensional/negligible condition on `x` for fixed `\<omega>`, which
     is plausible given it is `n` real equations on a `2n`-dim `x`-space).
Recommend (1) first, since it may be short and gives real understanding;
if the hand-derivation drags, (2) is the fallback.

### 7g. Case (b) RESOLVED into a clean three-way split; the "(phase-alignment
forced" reading of \<section>7f retracted as another solver-attractor artifact; the
full analytical mechanism derived (2026-07-12, Claude, session 5,
"ultrathink" pass)

**Correction to \<section>7f first (important).** Re-ran the case (b) search with
`\<omega>` HELD FIXED at a generic point (`\<omega>=(1.9,-1.3)`, `sin\<theta>=0.946`,
`|c|=1.4`): found 26/26 genuinely NON-phase-aligned witnesses of
`gradU=0 \<and> det HessU=0` (max`|Im(cnj A\<cdot>\<phi>_m)|` ranging 0.04-2.2), and ALL
26 had `rank_x=2` -- the `x`-block alone already surjective. So \<section>7f's
"det HessU=0 forces phase-alignment" reading is RETRACTED: it was the same
class of solver-attractor artifact as the `\<theta>=\<phi>=\<pi>/2` finding, one level
deeper (letting `\<omega>` float lets the solver slide down to the aligned
critical manifold; pinning `\<omega>` removes the slide). Case (b1) -- `x`-block
surjective \<Rightarrow> joint regular -- was formalized on the strength of this
(`joint_regular_of_x_partial_surj`, sorry-free, user-confirmed compile).

**The analytical mechanism (hand-derived, explains ALL the session's
attractor behavior in one stroke).** Differentiating
`U = g(\<theta>)\<cdot>|A(x,c(\<omega>))|\<^sup>2` in one antenna position:

    \<partial>U/\<partial>x_m = 2g\<cdot>Im(cnj(A)\<phi>_m)\<cdot>c        (always a multiple of the FIXED vector c)

so `\<nabla>_xU=0 \<longleftrightarrow>` full phase-alignment -- alignment IS the critical locus of
`U(\<cdot>,\<omega>)`, a genuine low-codimension attractor for any gradient-based
solver. Differentiating again in `\<omega>` and assembling the `x`-block's
rank-\<le>1 condition (`\<exists>(\<lambda>,\<mu>)\<noteq>0` killing `\<lambda>Row\<^sub>1+\<mu>Row\<^sub>2`) gives, per antenna:

    A_m\<cdot>c + Im_m\<cdot>B = 0,   B := g(\<lambda>\<gamma>\<^sub>1+\<mu>\<gamma>\<^sub>2),
    A_m := \<lambda>(p\<^sub>1 Im_m + g\<partial>\<^sub>\<theta>Im_m) + \<mu>g\<partial>\<^sub>\<phi>Im_m,   Im_m := Im(cnj(A)\<phi>_m)

Since `\<gamma>\<^sub>1,\<gamma>\<^sub>2` independent (`det Dcvec\<noteq>0` retained in BadXGW), `B\<noteq>0` always,
and there is a UNIQUE-up-to-scale special `(\<lambda>\<^sub>0,\<mu>\<^sub>0)` with `B\<parallel>c`. Dichotomy:

  1. **Generic branch** (witness `(\<lambda>,\<mu>)` has `B\<nparallel>c`): forces `Im_m=0` AND
     `A_m=0` for every antenna = full alignment + a collinearity condition.
     Full alignment \<Rightarrow> `\<nabla>_cV=0` \<Rightarrow> `gradU\<^sub>1=p\<^sub>1\<cdot>V`; then `gradU\<^sub>1=0` forces
     `V=|A|\<^sup>2=0` UNLESS `gdip'(\<theta>)=0` (discrete \<theta>-set, by analyticity).
     **This is exactly why every unconstrained search drove `A\<rightarrow>0`.** So on
     this branch, genuine BadXGW (`A\<noteq>0`) lives only over the countable
     `gdip'(\<theta>)=0` angle set -- negligible/harmless by this project's usual
     isolated-zeros machinery.
  2. **Special branch** (`(\<lambda>\<^sub>0,\<mu>\<^sub>0)`, `B=g\<cdot>c` after normalizing
     `\<lambda>\<^sub>0\<gamma>\<^sub>1+\<mu>\<^sub>0\<gamma>\<^sub>2=c`): per-antenna scalar equation `A_m + g\<cdot>Im_m = 0`
     (NOTE: coefficient `g`, an earlier scripted check mistakenly used `1`).
     Does NOT force alignment. Genuine `A\<noteq>0` BadXGW witnesses, if any,
     live here. Dimension count at fixed \<omega>: `gradU` (2) + branch-2 (n) +
     `det H=0` (1) = n+3 equations in 2n unknowns \<Rightarrow> expect solutions for
     n\<ge>4 generically (n=3 exactly determined, n\<le>2 overdetermined).

**Status**: branch-2 existence + joint-regularity check (the correctly-
scoped case (b2) question) running numerically (`d4_branch2_v3.py`, with
the corrected `g` coefficient and a properly-determined system). If
branch-2 witnesses exist and are joint-regular, `regular_value_on gradU`
holds everywhere relevant and D4 closes via Codex's round-1 reduction; if
they exist and are NOT joint-regular, they are at least now confined to an
explicitly parametrized, thin locus that can be handled separately; if
they don't exist, case (b2) is vacuous outside the discrete-\<theta> set.

### 7h. Synthesis: where case (b2) actually stands after the branch-2 hunt,
and the two concrete paths to close D4 (2026-07-12, Claude, session 5)

**Branch-2 emptiness (numerical, strong).** The decisive experiment
(`d4_branch2_seeded.py`): took 8 GENUINE non-aligned witnesses of
`{gradU=0, det H=0}` (stage 1, the \<section>7g fixed-\<omega> recipe, `|A|\<ge>0.3`,
`max|Im_m|\<ge>0.1`) and least-squared the full branch-2 system from each
(n=5, 9 equations in 10 unknowns -- solutions would form CURVES if the
system were consistent). Result: 0/8 converged; three seeds independently
stalled at the SAME nonzero residual (9.31e-2), the signature of a locally
inconsistent system rather than solver laziness. Together with \<section>7g's
analytical split this says: **the special-branch (`B\<parallel>c`) rank-collapse
locus appears EMPTY off the aligned manifold** -- i.e. genuinely-`A\<noteq>0`,
non-aligned `BadXGW` points seem not to exist, at least at generic \<omega>.

**Where the A=0 zeros fit (new sub-observation, (b3)).** For the
regular-value hypothesis, the huge zero manifold `{A=0}` (on which
`gradU\<equiv>0` identically) is NOT a problem: at `A=0`, `D_x[gradU_j] =
2g\<cdot>Re((-\<i>)\<cdot>cnj(D_xA)\<cdot>\<gamma>_j\<cdot>M)` (the `p_j|A|\<^sup>2` and `cnj A` terms die), which is
generically rank 2 in `x` alone -- so `A=0` points are generically covered
by case (b1) (`joint_regular_of_x_partial_surj`, already formalized). The
degenerate sub-locus where even this fails is where `\<gamma>_1\<cdot>M` and `\<gamma>_2\<cdot>M`
fail real-independence -- thin, and worth its own small check later.

**The one structurally unavoidable residual: `gdip'(\<theta>)=0`.** Branch-1 with
`A\<noteq>0` forces `gdip'(\<theta>)=0`. For the Robust4 design (`ctr=(\<pi>/2,0)`,
`\<delta>=\<pi>/4`), `\<theta>` ranges over `(\<pi>/4,3\<pi>/4)` and `gdip` has its MAXIMUM at
`\<theta>=\<pi>/2` -- so `gdip'(\<pi>/2)=0` and the line `{(\<pi>/2,\<phi>)}` lies INSIDE the
design box. On that 1-dim \<omega>-line, aligned `A\<noteq>0` configurations with the
branch-1 collinearity conditions are candidate genuine `BadXGW` points
that no case so far covers. This locus is thin (codim 1 in \<omega>, codim \<approx>n in
`x`) but the GLOBAL `regular_value_on gradU (V\<times>\<Omega>) 0` hypothesis quantifies
over every zero, so it cannot just be waved through -- the global-\<Omega> form
of Codex's reduction is NOT directly usable if these points are genuinely
irregular.

**Two concrete paths to close D4 from here (both use machinery ALREADY
proven in `Scratch_D4Branch.thy`):**

  1. **Patch route** (`branchP_indep_closed_cover_core_of_countable_gradU_
     regular_value_patches`, proven): apply the regular-value engine only
     on patches `\<Omega>_i` AVOIDING `\<theta>=\<pi>/2` (and any other `gdip'` zeros), where
     cases (a)+(b1)+(b3) plausibly give regularity everywhere; handle the
     excluded `\<theta>=\<pi>/2` angles by the SINGLETON route: `branchP_indep_closed_
     cover_core_of_d3_H0core_chart_core` (proven) + `fixed_omega_H0core_
     chart_core_robust4_all_angles` (proven, unconditional, covers EVERY
     angle in range including `\<pi>/2`) + `branchP_fixed_omega_cover_of_bad_
     angle_range_cover` (proven) + the countable-union assembler (proven).
     The bad angles on the `\<theta>=\<pi>/2` line form a 1-dim family, but the
     SINGLETON machinery needs only COUNTABLY many bad angles total --
     which is exactly `countable_bad` again, but now needed ONLY for the
     `\<theta>=\<pi>/2` line (1-dim), a much smaller target than before: bad angles
     on that line are `\<phi>`-values where an aligned `A\<noteq>0` critical
     configuration exists, and countability there may follow from analytic
     finiteness in the single variable `\<phi>` -- a 1-VARIABLE analyticity
     argument, the kind this project already does well (isolated zeros of
     non-vanishing real-analytic functions).
  2. **Regularity-at-the-residual route**: check (numerically first)
     whether at `\<theta>=\<pi>/2` aligned `A\<noteq>0` points the JOINT Jacobian is
     nevertheless rank 2 (the \<omega>-block/HessU could still supply the missing
     directions even though the `x`-block collapses to \<parallel>c). If yes at
     generic such points, a `\<theta>=\<pi>/2`-specific case (b4) lemma covers them
     and the GLOBAL regular-value route survives after excising only a
     genuinely-irregular sub-sub-locus (possibly empty).

Recommend: numerically check route 2's question first (cheap, one fixed-\<omega>
experiment at `\<omega>=(\<pi>/2,\<phi>_0)` with alignment imposed); if it fails, route 1
is the fallback with a clear 1-variable countability endgame.

### 7i. DECISIVE numerics: the global regular-value hypothesis appears TRUE
-- the joint Jacobian is rank 2 at every category of gradU-zero, including
the deepest degeneracy locus (2026-07-12, Claude, session 5)

Completed the \<section>7h route-2 check, in two steps, both at `\<theta>=\<pi>/2` (the
`gdip'=0` line inside the design box), multiple `\<phi>` values, `n=4`:

**Step 1 -- aligned `A\<noteq>0` points WITHOUT the collinearity degeneracy**
(`d4_route2_pi2.py`; NOTE the quantization fact discovered en route: under
exact alignment `|A|` is QUANTIZED to `{n, n-2, ...}` -- for `n=4` only
`{0,2,4}` -- because all phases equal `arg A` mod `\<pi>`; an `|A|=1.5` target
is unsatisfiable and gave a false "no witnesses" first pass). Result:
19/19 witnesses have `rank_x=2` -- generic aligned points at `gdip'=0`
angles are ALREADY covered by the formalized case (b1). Analytical reason:
at alignment the `x`-block's columns are `c_k\<cdot>v_m` with
`v_m := 2g\<cdot>\<nabla>_\<omega>Im_m \<in> \<real>\<^sup>2`, so `rank_x = dim span{v_m} = 2` unless ALL the
`\<nabla>_\<omega>Im_m` are collinear -- `n-1` further equations that alignment alone
does not impose. \<section>7h's fear that the `\<theta>=\<pi>/2` line is a structural
obstruction was overblown.

**Step 2 -- the TRUE deepest locus: aligned + `A\<noteq>0` + all `\<nabla>_\<omega>Im_m`
collinear** (`d4_collinear_pi2.py`, imposing the `n-1` cross-product
equations explicitly): 14/14 witnesses found (so this locus is NONEMPTY --
the residual is real), every one with `rank_x=1` EXACTLY (second singular
value 0.0 to solver precision) -- and **`rank_joint=2` in every single
case**, second joint singular value 5.3-11.7, far from zero: the \<omega>-block
(`HessU`) supplies exactly the direction the collapsed `x`-block loses.
Plausible clean mechanism for the eventual proof: at `\<theta>=\<pi>/2` aligned
points, `H\<^sub>1\<^sub>1 \<supset> gdip''(\<pi>/2)\<cdot>V \<noteq> 0` (`gdip` has a genuine max at `\<pi>/2`, so
`gdip''<0`, and `V=|A|\<^sup>2>0`) -- not yet a complete argument (need the
H-image to be jointly independent from the `x`-block's leftover direction
`span{v}`), but a concrete starting point.

**Net status of the D4 campaign after today:**
  - `regular_value_on gradU (V\<times>\<Omega>) 0` appears TRUE globally at the Robust4
    design (every zero category checked: case (a) det H\<noteq>0 [formalized],
    case (b1) rank_x=2 [formalized], A=0 zeros [generically (b1)],
    branch-2 [empirically empty], deepest collinear-aligned locus
    [rank_joint=2, 14/14]).
  - The remaining FORMALIZATION gap is exactly one genuine lemma -- call
    it case (b4): at zeros where `det HessU=0` AND the `x`-block is
    rank-deficient, the joint derivative is still surjective. Everything
    else (the reduction from `branchP_indep_closed_cover_core_all` to the
    regular-value hypothesis, the case-split assembly, the chart engine)
    is ALREADY proven in `Scratch_D4Branch.thy`.
  - Honest difficulty estimate for (b4): the numerics + the `H\<^sub>1\<^sub>1` seed
    suggest a genuine analytical proof exists, but it must handle the
    classification of WHICH zeros can reach this locus (the \<section>7g branch
    analysis: alignment + `gdip'(\<theta>)=0` + collinearity, or the empirically-
    empty branch-2, whose emptiness would ALSO need proof if relied upon)
    -- this is real work, comparable to one of D3's mid-size bricks, but
    it is now ONE concrete, well-scoped target instead of an amorphous
    "countability of bad angles."

### 7j. (b4) semi-formal pass: the claim as stated is FALSE (explicit
counterexample constructed) -- but the same exact algebra yields the
correct, fully explicit replacement plan (2026-07-12/13, Claude, session 5)

**Retraction of \<section>7i's optimism, with proof.** Working the collinear-
aligned locus EXACTLY (no numerics): under alignment write
`\<phi>_m = \<sigma>_m e^{i\<alpha>}`, `\<sigma>_m\<in>{\<pm>1}`. Then everything is real:
`A = S\<^sub>0e^{i\<alpha>}` (`S\<^sub>0=\<Sigma>\<sigma>_m` -- whence the `|A|` quantization of \<section>7i),
`M_k = S_ke^{i\<alpha>}`, and with all antennas on a line `x_m = P + t_m d`
through `P = S/S\<^sub>0` (which is EXACTLY the \<section>7g collinearity condition,
`\<Sigma>\<sigma>_mt_m=0` forced):

    Hc = -2S\<^sub>0Q\<cdot>dd\<^sup>T          (Q := \<Sigma>\<sigma>_mt_m\<^sup>2; rank \<le>1, direction d!)
    H  = a\<cdot>uu\<^sup>T + b\<cdot>e\<^sub>1e\<^sub>1\<^sup>T     (u := \<Gamma>\<^sup>Td, a := -2gS\<^sub>0Q, b := gdip''(\<theta>)V)
    col(J_x) = \<real>\<cdot>u          (x-block image)

Joint rank 2 \<longleftrightarrow> `b\<noteq>0 \<and> u \<nparallel> e\<^sub>1`, i.e. `\<gamma>\<^sub>2\<cdot>d \<noteq> 0`. **If the antenna line
direction `d` is perpendicular to `\<gamma>\<^sub>2`, then `col(J_x) = col(H) = \<real>e\<^sub>1` and
the joint Jacobian has rank 1.** Constructed such a point explicitly
(`d4_irregular_construct.py`, n=6, \<omega>=(\<pi>/2,0.4), \<sigma>=(+,+,+,+,-,-),
quantized `t_m`, `\<Sigma>\<sigma>_mt_m=0`): verified `|A|=2`, `max|Im_m|=8e-15`,
`|gradU|\<approx>2e-10`, rank_x=1, **rank_joint=1** (the apparent
`det H\<approx>2.5e-2` is exactly FD noise: sv\<^sub>1\<cdot>(relative FD error) --- the closed
form gives `H\<^sub>1\<^sub>2=H\<^sub>2\<^sub>2=0` exactly). These points satisfy every BadXGW conjunct
(A\<noteq>0, det Dcvec\<noteq>0 generic, etc.), so: **the global `regular_value_on
gradU (V\<times>\<Omega>) 0` is FALSE, and no patch containing such points can satisfy
it either.** \<section>7i's 14/14 missed this because `\<gamma>\<^sub>2\<cdot>d=0` is one more
codimension than the random search imposed. (Also explains why the
formalized cases (a)/(b1) are still fine -- these points genuinely have
`det H=0` and rank_x\<le>1.)

**The silver lining -- the SAME algebra gives the correct plan.** The
entire branch-1/aligned residual (which contains ALL such irregular
points) is EXPLICITLY PARAMETRIZED, no genericity needed:

    aligned w.r.t. \<omega>=(\<theta>\<^sup>*,\<phi>) with gdip'(\<theta>\<^sup>*)=0
    \<longleftrightarrow> every c(\<theta>\<^sup>*,\<phi>)\<cdot>x_m \<in> \<alpha> + \<pi>\<int>
    \<longleftrightarrow> x \<in> image of F_k : (\<phi>, \<alpha>, s\<^sub>1..s_n) \<mapsto>
         (x_m = ((\<alpha>+k_m\<pi>)/|c|\<^sup>2)c + s_m c\<^sup>\<bottom>)_m,   k \<in> \<int>\<^sup>n (countable)

Each `F_k` is a smooth map `\<real>\<^sup>{n+2} \<rightarrow> \<real>\<^sup>{2n}`; since `n+2 < 2n` for `n\<ge>3`
(we have `CARD('n)\<ge>6`), its derivative is NOWHERE surjective, so
`negligible_singular_image_2n` applies with `Crit` = (a compact exhaustion
of) the whole domain: countably many closed negligible images covering the
aligned residual. **This slots DIRECTLY into
`branchP_indep_closed_cover_core`'s definition** -- no IFT, no Sard, no
regular-value hypotheses. This is the new main formalization target,
replacing the false (b4).

**Honest remaining gap: the non-aligned part.** Non-aligned BadXGW points
\<subseteq> branch-2 locus (\<section>7g), empirically empty. Algebraic notes toward an
emptiness/thinness proof: `\<Sigma>_mIm_m = Im(cnj A\<cdot>A) = 0` identically, so the
plain sum of the branch-2 equations gives nothing; the `x_{m,k}`-weighted
sum gives `\<lambda>\<^sub>0(p\<^sub>1I_k + g\<partial>_\<theta>I_k) + \<mu>\<^sub>0g\<partial>_\<phi>I_k + gI_k = 0` (`I_k :=
Im(cnj A\<cdot>M_k)`, `\<nabla>_cV = 2I`), to be combined with `gradU=0 \<longleftrightarrow>
{p\<^sub>1V + 2g\<gamma>\<^sub>1\<cdot>I = 0, \<gamma>\<^sub>2\<cdot>I = 0}` -- not yet conclusive. Options remain:
(i) prove branch-2 \<inter> {gradU=0} forces alignment (the dream identity);
(ii) cover the branch-2 locus by its own chart family (needs an
independence/thinness argument for the n+2 cut equations); (iii) a
different decomposition of the non-aligned part. NOT resolved this pass.

**Revised D4 status:** cases (a)+(b1) formalized \<checkmark>; aligned residual has a
fully explicit, genericity-free cover plan (formalize next); non-aligned
residual (branch-2) is the one genuinely open piece.

### 7k. Task-14 semi-formal pass: branch-2 is a CRITICAL-POINT system in
the phase coordinates; the dream identity is FALSE, but gradU=0 makes the
t-sector overdetermined (2026-07-13, Claude, session 5)

**The (t,u) frame.** For fixed \<omega> with `c\<noteq>0`, write each antenna as
`x_m = (t_m c + u_m c\<^sup>\<bottom>)/|c|\<^sup>2` (`t_m = c\<bullet>x_m`, `u_m = c\<^sup>\<bottom>\<bullet>x_m`). Everything
phase-dependent (`\<phi>_m, A, Im_m, Re_m, W := c\<^sub>1M\<^sub>1+c\<^sub>2M\<^sub>2 = \<Sigma>t_m\<phi>_m`) is a
function of `t` ALONE.

**Discovery 1: branch-2 is `\<nabla>_t\<Phi> = 0` for one scalar potential.** Two
exact identities: `Im_m = \<half>\<cdot>\<partial>V/\<partial>t_m` (`V=|A|\<^sup>2`), and the \<section>7g branch-2
equation `A_m + g\<cdot>Im_m = 0` collapses (using `\<lambda>\<^sub>0\<gamma>\<^sub>1+\<mu>\<^sub>0\<gamma>\<^sub>2 = c`, so
`\<lambda>\<^sub>0\<partial>_\<theta>+\<mu>\<^sub>0\<partial>_\<phi> = c\<cdot>\<nabla>_c`) to

    \<partial>/\<partial>t_m [ (\<lambda>\<^sub>0p\<^sub>1/2)\<cdot>V + g\<cdot>G ] = 0  for every m,   G := Im(cnj A\<cdot>W)

-- i.e. `t` is a critical point of `\<Phi> := (\<lambda>\<^sub>0p\<^sub>1/2)V + gG`. The same
critical-point mechanism as \<section>7c's `\<Psi>_a` and \<section>7g's alignment -- one
family, three appearances.

**Discovery 2: the dream identity is FALSE.** Numerically (`d4_branch2_
tspace.py`, n=5, \<omega>=(1.9,-1.3)): `\<nabla>_t\<Phi>=0` has MANY non-aligned solutions
(17/23 converged trials, `max|Im|` up to 3.0, `|A|` up to 3.4). Branch-2
alone does NOT force alignment; task-14 cannot be closed by an emptiness
identity at that level.

**Discovery 3: `gradU=0` adds exactly ONE more t-equation.** In the (t,u)
frame `I = \<Sigma>Im_m x_m = (S_t c + S_u c\<^sup>\<bottom>)/|c|\<^sup>2` with `S_t = \<Sigma>Im_m t_m`
(t-only) and `S_u = \<Sigma>Im_m u_m` (the ONLY u-dependence). `gradU=0` \<equiv>
`{\<gamma>\<^sub>2\<cdot>I = 0, p\<^sub>1V + 2g\<gamma>\<^sub>1\<cdot>I = 0}`: the first solves for `S_u` (one LINEAR
u-equation, always satisfiable for non-aligned t since some `Im_m\<noteq>0`);
substituting into the second leaves ONE scalar equation in `t` alone. So
the non-aligned `branch-2 \<and> gradU=0` locus needs `t` to satisfy an
OVERDETERMINED system: `n+1` equations (`\<nabla>_t\<Phi>=0` and the reduced gradU
scalar) in `n` unknowns -- generically EMPTY, which would explain the
\<section>7h seeded-search emptiness exactly. Numerical confirmation running
(`d4_branch2_tu_full.py`).

**Consequence for the task-14 architecture (either way, now sharply
scoped).** If the (n+1)-in-n overdetermination holds generically in \<omega>:
consistency is a codim-1 condition on the \<omega>-dependent coefficients, so
bad \<omega>'s form a \<le>1-dim subfamily of the 2-dim `OmegaPF` box, and at those
\<omega> the t-solutions are (generically) isolated with `u` constrained by the
`S_u` line -- total dimension of the non-aligned BadXGW locus \<le>
1 + 0 + (n-1) = n < 2n even before using `det H=0` and `\<not>surj DM`. The
cover formalization would mirror \<section>7j's: parametrize `(\<omega>, t\<^sup>*(\<omega>), u)` --
BUT unlike \<section>7j the t-slices are IMPLICIT (solutions of \<nabla>_t\<Phi>=0), so a
naive chart needs IFT-regularity of \<Phi>'s Hessian -- the genericity problem
again. Honest options: (i) find MORE structure in \<Phi> (it is an explicit
trig polynomial -- its critical set may admit an explicit description like
the aligned case); (ii) use `\<not>surj DM_paper_x` (also retained in BadXGW,
unused so far) as the covering condition instead -- for FIXED c it is
`{x : all 12\<times>12 minors of DM vanish}`, a real-analytic variety; with the
right analytic-stratification lemma (NOT yet in the codebase) it covers;
(iii) prove the reduced-gradU scalar is NOT identically zero on \<Phi>'s
critical set as a function of \<omega> along every analytic arc, and countability
in \<omega> follows by isolated zeros -- the 1-variable analyticity pattern this
project already does well, but now the object is an implicit function of
\<omega> (needs the analytic IFT that Analytic/ is building!). Option (iii)
connects to the EXISTING Real_Analytic/analytic-IFT program (memory:
analytic-ift-route-and-foundation-sync) -- possibly the intended
convergence point of the two efforts.

### 7m. Codex formalization step: put the branch-2 residual into `(t,u)`
coordinates

The current Isabelle endpoint is stronger than the older countable-angle
route: D4 is reduced to a cover of the explicit residual

    branch2_bad(V,\<Gamma>) =
      {x\<in>V. \<exists>\<omega>\<in>\<Gamma>. x\<in>BadXGW(\<omega>0,\<omega>s,{\<omega>})
          \<and> x\<in>branch2_locus(\<omega>0,\<omega>s,\<omega>)}.

The next formal move is not to prove the cover yet, but to move this set into
the `(t,u)` frame used in §7k.  For fixed nonzero `c`, define

    T_c(\<omega>,t,u)_m =
      ((t_m / (c\<bullet>c)) * c) + ((u_m / (c\<bullet>c)) * perp2 c)

where `t_m = c\<bullet>x_m` and `u_m = perp2 c\<bullet>x_m`.  The already-proven
`perp2_decomp2` gives the reconstruction lemma

    c \<noteq> 0 \<Longrightarrow> T_c((\<chi>m. c\<bullet>x_m),(\<chi>m. perp2 c\<bullet>x_m)) = x.

Since every `BadXGW` point carries `cvec_dip \<omega>0 \<omega>s \<omega> \<noteq> 0`, the residual
is contained in the image of the corresponding `(t,u)` system:

    branch2_bad V \<omega>0 \<omega>s \<Gamma>
      \<subseteq> (\<lambda>(\<omega>,t,u). T_{c(\<omega>)}(t,u)) ` branch2_tu_system V \<omega>0 \<omega>s \<Gamma>.

This is deliberately a first, conservative formal interface.  The next cycle
should strengthen `branch2_tu_system` by replacing its pulled-back
`BadXGW`/`branch2_locus` predicates with the explicit §7k scalar equations
in `t` and the one linear `u` constraint.

### 7n. Next formal bridge: radial slots are coordinate axes in `t`

The first scalarization step should avoid expanding the full trigonometric
potential immediately.  In the `(t,u)` frame, the radial slot direction
`slot m c` is exactly the image of the `m`-th coordinate axis in `t`, scaled
by `c·c`:

    T_c((c·c)e_m,0) = slot m c,        c ≠ 0.

Similarly `T_c(0,(c·c)e_m) = slot m (perp2 c)`.  Therefore the defining
branch-2 equations

    ell · D_x gradU(x,ω)[slot m c] = 0       for all m

can be restated, without changing the mathematics, as vanishing of the
radial `t_m` coordinate derivatives of the pulled-back system.  This is the
right next Isabelle interface:

    branch2_tu_system p
      ⟹ branch2_tu_radial_locus ω t u.

After this bridge is formalized, the following cycle can replace those
radial derivative equations by the closed §7k trigonometric formulas
(`∇_t Φ = 0`) and then add the `gradU=0` reduced scalar plus the one linear
`u` constraint.

### 7o. Next formal bridge: expose the radial derivative formula

The next Isabelle layer should name the closed radial-slot vector obtained
from the already-proven general slot formula `gradU_dip_xderiv_slot`, with
`v = c(ω)`:

    R_m(x,ω) := D_x[gradU(x,ω)](slot m c(ω)).

Formally this is just a vector-valued abbreviation for the theorem
`gradU_dip_xderiv_slot` specialized to the radial slot.  The important
interface is:

    branch2_tu_radial_locus ω t u
      ⟹ ∃ell. special(ell,ω) ∧ ∀m. ell · R_m(T_c(t,u),ω) = 0.

This still has `M_paper` and `phase` in it, but all occurrences of `x` are
now through `T_c(t,u)`.  The following cycle can use the coordinate identity

    w · T_c(t,u)_m =
      (t_m/(c·c))(w·c) + (u_m/(c·c))(w·perp2 c)

to replace the remaining `γ_j·x_m` terms by explicit linear expressions in
`t_m,u_m`; after that the only nonlinear part is the expected trigonometric
dependence on `t`.

### 7p. Formal substitution of the remaining `γ_j·x_m` radial term

The next bridge is purely definitional: specialize §7o's radial-slot closed
form to `x = T_c(t,u)` and replace the only visible affine-in-`x` term

    γ_j(ω) · x_m

by

    (t_m/(c·c))(γ_j·c) + (u_m/(c·c))(γ_j·perp2 c).

This yields a `gradU_radial_tu_slot_rhs` formula.  It still deliberately
leaves `M_paper(T_c(t,u),c)` and `phase(c,T_c(t,u),m)` unexpanded, because
those are the next, more trigonometric, substitutions.  The important
interface is:

    branch2_tu_system p
      ⟹ branch2_tu_radial_tu_formula_locus ω t u.

The following step should simplify `phase(c,T_c(t,u),m)` to `exp(-i*t_m)`
and rewrite the moment terms as sums over `t` only; only then is the
`∇_t Φ = 0` shape fully visible.

### 7q. Phase and first-moment collapse after `(t,u)` substitution

For `c ≠ 0`, the coordinate map was chosen so that

    c · T_c(t,u)_m = t_m,          perp2(c) · T_c(t,u)_m = u_m.

Therefore the paper phase has the exact pulled-back form

    phase(c,T_c(t,u),m) = cis(-t_m).

The first moment `A` consequently depends only on `t`:

    A(T_c(t,u),c) = Σ_m cis(-t_m).

The two coordinate moments used by the radial-slot formula are not
`u`-free, because `M1` and `M2` are written in the fixed ambient coordinate
axes rather than in the `(c,perp2 c)` frame.  But they are now explicit
affine-weighted phase sums:

    M_j(T_c(t,u),c)
      = Σ_m ((t_m/(c·c)) c_j + (u_m/(c·c)) perp2(c)_j) cis(-t_m),
        j = 1,2.

The next formal interface should replace the first three `M_paper` entries
and every visible `phase(c,T_c(t,u),m)` in `gradU_radial_tu_slot_rhs` by
these named pulled-back sums.  This is still not the final scalar
`∇_t Φ = 0` statement, but it removes the opaque moment map from the
branch-2 radial equations and leaves an explicit trigonometric-polynomial
system in `(ω,t,u,ell)`.

### 7r. Bundle the branch-2 equations as one finite scalar residual

After §7q, the branch-2 radial equations have the form

    ∃ell ≠ 0.
      (ell_1 γ_1(ω) + ell_2 γ_2(ω)) · perp2(c(ω)) = 0
      ∧ ∀m. ell · R_m(ω,t,u) = 0.

The first side condition is itself just one scalar equation.  Define the
coefficient vector

    B(ω)_j = γ_j(ω) · perp2(c(ω)).

Then

    (ell_1 γ_1 + ell_2 γ_2) · perp2(c) = ell · B(ω).

So the whole branch-2 residue can be written as a single finite residual
map

    F(ω,t,u,ell) =
      ( ell · B(ω),
        (ell · R_m(ω,t,u))_m )
      ∈ R × R^n.

The formal target for this cycle is only the exact interface

    branch2_tu_system p
      ⟹ ∃ell ≠ 0. F(ω,t,u,ell) = 0.

This is intentionally still existential in `ell`.  The next cycle can choose
a covector chart (`ell_1 ≠ 0` or `ell_2 ≠ 0`) and turn that projective
unknown into one real parameter, matching the earlier `Psi_a` chart pattern.

### 7s. Projectivize the covector residual

The residual `F(ω,t,u,ell)` from §7r is linear in `ell`.  Since `ell ≠ 0`,
either `ell_1 ≠ 0` or `ell_2 ≠ 0`.  Scaling a zero of `F` by any nonzero
real scalar is again a zero, so the existential covector can be covered by
two one-parameter charts:

    ell = (1,a)     if ell_1 ≠ 0,
    ell = (a,1)     if ell_2 ≠ 0.

Thus

    ∃ell ≠ 0. F(ω,t,u,ell)=0

is equivalent to the union of two chart systems

    ∃a. F(ω,t,u,(1,a))=0
      ∨ ∃a. F(ω,t,u,(a,1))=0.

This is the first point where the branch-2 residue has the right dimension
profile for the cover argument: the variables are `(ω,t,u,a)`, and the
equations are one special-covector equation plus the `n` radial equations.
The remaining `BadXGW` conjuncts still supply `gradU=0`, `det HessU=0`,
`A≠0`, and the harmless `¬surj DM_paper_x` condition.

### 7t. Feed the chart split back into the D4 cover capstone

The existing D4 capstone already knows how to finish from a countable
closed negligible cover of

    branch2_bad(V,Γ)
      = {x∈V. ∃ω∈Γ. x∈BadXGW(ω) ∧ x∈branch2_locus(ω)}.

Sections §7m-§7s now give the exact containment

    branch2_bad(V,Γ)
      ⊆ X_1(V,Γ) ∪ X_2(V,Γ),

where `X_i` is the image in x-space of the `(ω,t,u)` systems satisfying the
i-th projective covector chart residual:

    X_i(V,Γ) =
      { T_{c(ω)}(t,u) :
          (ω,t,u)∈branch2_tu_system(V,Γ)
          and chart_i_residual(ω,t,u)=0 }.

Therefore the next formal capstone should be:

    cover(X_1) ∧ cover(X_2)
      ⟹ cover(branch2_bad)
      ⟹ branchP_indep_closed_cover_core_all.

This does not yet prove the two chart-image covers analytically, but it
removes another layer of glue: the only remaining mathematical work is now
to prove closed/negligible covers for two explicit chart-image residual
systems.  That is the correct final target for the analytic/IFT or
finite-dimensional parametrization argument.

### 7u. Make the chart parameter `a` part of the parameter domain

The chart-image sets `X_i(V,Γ)` from §7t still hide the chart parameter by
writing the chart condition as `∃a`.  For the final covering argument, it is
better to expose `a` as an ordinary parameter and map from

    q = ((ω,t,u),a).

Define residual functions

    F_1(q) = F(ω,t,u,(1,a)),
    F_2(q) = F(ω,t,u,(a,1)),

and parameter systems

    Q_i(V,Γ) =
      { ((ω,t,u),a) :
          (ω,t,u)∈branch2_tu_system(V,Γ) and F_i((ω,t,u),a)=0 }.

The x-map ignores `a`:

    X(q) = T_{c(ω)}(t,u).

Then formally

    X_i(V,Γ) = X ` Q_i(V,Γ).

This is mainly bookkeeping, but it is important bookkeeping: the remaining
D4 obligation can now be stated directly as closed/negligible covers of two
explicit residual-zero images, with no hidden existential covector and no
abstract `branch2_locus`.

### 7v. Countable bounded slices of the chart parameter images

The chart parameter images are still images of unbounded parameter domains:
`t`, `u`, and the projective chart coordinate `a` range over Euclidean
spaces, and the coordinate map divides by `c(ω)·c(ω)`.  But every actual
point in the chart systems already has `c(ω) ≠ 0`, because it came from
`BadXGW`.  Hence every parameter point belongs to some bounded slice

    1/(j+1) ≤ c(ω)·c(ω),
    ||t|| ≤ j,    ||u|| ≤ j,    |a| ≤ j.

Therefore each chart image is contained in the countable union of its
bounded-slice images:

    branch2_charti_param_image(V,Γ)
      ⊆ ⋃_j branch2_charti_param_slice_image(V,Γ,j).

The next formal capstone should say:

    (∀j. cover(slice_1(j))) ∧ (∀j. cover(slice_2(j)))
      ⟹ branchP_indep_closed_cover_core_all.

This is still a reduction, not the final analytic proof, but it removes the
last global unboundedness issue.  The remaining proof units are now local:
closed/negligible covers for bounded residual-zero images in each chart.

Status note, 2026-07-13: Codex tried to add this bounded-slice layer directly
to `Scratch_D4Branch.thy`, but PIDE stalled at the end of the theory.  The
formal file has therefore been rolled back to the verified §7u capstone
interface, where the remaining hypotheses are covers of the two explicit
chart-parameter images.  Keep §7v as the next semi-formal target, but
reintroduce it only as smaller lemmas or in a separate scratch theory so that
each boundedness/covering component can be checked independently.

Informal proof plan for the smaller §7v formalization.

Write a chart parameter as

    q = ((ω,t,u),a),

and put

    c = c(ω),    X(q) = T_c(t,u).

For a natural number j, define the bounded predicate B_j(q) by

    1 / (j+1) ≤ c·c,
    ||t|| ≤ j+1,
    ||u|| ≤ j+1,
    |a|  ≤ j+1.

Let Q_i be the already-formal chart parameter system from §7u, and let

    Q_i(j) = { q ∈ Q_i : B_j(q) }.

The slice image is

    X_i(j) = X ` Q_i(j).

Now take any x ∈ X ` Q_i.  By definition, x = X(q) for some q ∈ Q_i.
Since q ∈ Q_i, its first component p = (ω,t,u) lies in
`branch2_tu_system`.  That system was built from `BadXGW`, so
`c(ω) ≠ 0`; hence `0 < c(ω)·c(ω)`.  By Archimedeanness, choose j0 with
`1/(j0+1) < c·c`.  Choose j1,j2,j3 bounding `||t||`, `||u||`, and `|a|`.
With j the maximum of those four indices, all four inequalities defining
B_j(q) hold.  Hence q ∈ Q_i(j), and x ∈ X_i(j).  This proves

    X ` Q_i ⊆ ⋃_j X ` Q_i(j).

Therefore, if each bounded slice image X_1(j) and X_2(j) has a countable
closed/negligible cover, the whole chart images X_1 and X_2 have countable
closed/negligible covers by diagonal enumeration of `(j,n)`.  Feeding those
two chart-image covers into the §7u capstone proves
`branchP_indep_closed_cover_core_all`.

### 7w. The special covector cancels the `u`-dependence

The bounded-slice reduction leaves a local problem in parameters

    q = ((ω,t,u),a).

A naive dimension count on all parameters is too large:

    dim(ω,t,u,a) = 2 + n + n + 1 = 2n+3,

while the image lives in `2n` real dimensions.  The residual equations must
be used before applying a thin-image argument.

The key simplification is that the projective covector chart equation contains
the special scalar constraint

    ell · B(ω) = 0.

Equivalently, for

    L = ell_1 D_1 c(ω) + ell_2 D_2 c(ω),

we have

    L · perp(c(ω)) = 0.

Since `c(ω) ≠ 0` on the bad locus, this means `L` is parallel to `c(ω)`:

    L = ((L·c)/(c·c)) c.

Now each antenna position in `(t,u)` coordinates is

    x_m = (t_m/(c·c)) c + (u_m/(c·c)) perp(c).

Therefore

    L · x_m
      = (t_m/(c·c)) (L·c)
        + (u_m/(c·c)) (L·perp(c))
      = (t_m/(c·c)) (L·c).

So the `u_m` term vanishes.  Summing against the phases gives the moment
combination cancellation:

    ell_1 M_1(c,t,u) + ell_2 M_2(c,t,u)
      = Σ_m ((t_m/(c·c)) (L·c)) phase_t(t,m),

which depends only on `(ω,t,ell)`, not on `u`.

This is the next formal target.  It does not yet prove the slice images are
negligible, but it removes the misleading `u`-dependence from the residual.
After this, the chart residual should be rewritten as equations in
`(ω,t,a)` only, with `u` remaining as a free `n`-dimensional fibre in the
x-map.  The expected dimension then becomes:

    dim(solution base in (ω,t,a)) = 2,
    dim(free u fibre) = n,
    total image dimension ≤ n+2 < 2n     for CARD('n) ≥ 4.

### 7x. Reduced radial scalar equations in `(ω,t,a)`

After §7w, the next formal object should be a reduced scalar residual with no
`u` argument.  For a chart covector `ell`, set

    L(ω,ell) = ell_1 D_1 c(ω) + ell_2 D_2 c(ω),

and define the `u`-free combined moment

    M_L(ω,t,ell)
      = Σ_i ((t_i/(c·c)) (L·c)) phase_t(t,i).

The radial scalar equation

    ell · gradU_radial_tu_moment_rhs(ω,t,u,m) = 0

then rewrites, under the special equation `L·perp(c)=0`, to

    G_ell(ω) · 2(c·c) Im(conj(A_t(t)) phase_m)
      + gain(ω) [
          2(c·c) Re(conj(phase_m) M_L(ω,t,ell))
          + 2(L·c) Im(conj(A_t(t)) phase_m)
          - 2(c·c) ((t_m/(c·c))(L·c))
              Re(conj(A_t(t)) phase_m)
        ] = 0,

where

    G_ell(ω) = ell · (j ↦ D gain(ω)[axis_j]).

This is the real residual system that should drive the final local proof.
For chart 1, `ell = (1,a)`; for chart 2, `ell = (a,1)`.  The base variables
are now only `(ω,t,a)` with `n+1` scalar equations: one special equation plus
the `n` reduced radial equations.  The expected regular rank is `n+1`, leaving
a two-dimensional base solution set; adding the free bounded `u` fibre gives
dimension `n+2`, safely below the `2n` target dimension for `n ≥ 4`.

### 7y. Reduced-base slice images as the final D4 interface

The no-`u` rewrite should now be made into the last global D4 reduction.
Write a chart parameter as

    q = ((ω,t,u),a).

Separate it into a base parameter and a free fibre:

    r = ((ω,t),a),     u = u(q).

For chart 1 put `ell = ell_chart1(a)`, and for chart 2 put
`ell = ell_chart2(a)`.  Define the reduced base residual by

    R_i(r) =
      ( ell · branch2_special_coeffs(ω),
        χm. branch2_radial_scalar_reduced_eq(ω,t,ell,m) ).

The bounded base condition remembers all bounds except the free `u` bound:

    1/(j+1) ≤ c(ω)·c(ω),
    ||t|| ≤ j+1,
    |a| ≤ j+1.

The fibre condition is just

    ||u|| ≤ j+1.

The reduced base system is

    B_i(Γ,j) =
      { r : ω ∈ Γ, base_bound_j(r), R_i(r)=0 }.

The reduced slice image is

    X_i^red(Γ,j) =
      { T_c(ω)(t,u) : r ∈ B_i(Γ,j), ||u|| ≤ j+1 }.

Now take any point in the old bounded chart slice image.  It comes from some
`q = ((ω,t,u),a)` in the old slice system.  Its residual is zero, so the
special scalar equation gives the first component of `R_i(r)=0`, and §7x
rewrites every old radial equation to the reduced radial equation.  The old
bounded predicate splits into the new base bound plus the free fibre bound.
Finally the old `x`-map and the new base/fibre `x`-map are definitionally the
same.  Hence

    old_slice_image_i(V,Γ,j) ⊆ X_i^red(Γ,j).

This is the final global D4 capstone:

    covers of X_1^red(Γ,j) and X_2^red(Γ,j), for all Γ,j,
      imply branchP_indep_closed_cover_core_all.

After this reduction, nothing global remains.  The final unfinished theorem is
local and analytic: prove each reduced base/fibre image has a countable closed
negligible cover.  Dimensionally this is now the right target: the equations
live on `(ω,t,a)`, leave an expected two-dimensional base solution set, and
the free bounded `u` fibre adds `n` more dimensions, so the image dimension is
at most `n+2 < 2n` when `CARD('n) ≥ 4`.

### 7z. Local analytic proof shape for the reduced images

Fix a steering patch `Γ`, a bounded slice index `j`, and one projective chart.
The reduced base variables are

    r = ((ω,t),a) ∈ real^2 × real^n × real,

and the reduced residual is

    R_i(r) ∈ real × real^n.

The reduced base system is `R_i(r)=0`, together with the patch and boundedness
conditions.  The real analytic/rank theorem we need is:

    rank D R_i(r) = n+1

on each local regular piece of the reduced base system.  Since the base
ambient dimension is `n+3`, the implicit-function theorem gives local
two-dimensional charts

    ψα : Uα ⊆ real^2 → real^2 × real^n × real

whose images cover the reduced base system on the bounded slice.

The free fibre variable is still

    u ∈ real^n,    ||u|| ≤ j+1.

For each local base chart, define the configuration parametrization

    Fα(s,u) =
      T_{c(ω(s))}(t(s),u),

where `ψα(s)=((ω(s),t(s)),a(s))`.  Its source has dimension

    dim(real^2 × real^n) = n+2.

The target configuration space has dimension `2n`.  For `n ≥ 4`,

    n+2 < 2n.

Thus each `Fα` image is negligible by the low-dimensional differentiable image
theorem.  On bounded closed subpieces, the source is compact and `Fα` is
continuous, so the image is closed.  Countably many such pieces cover the
bounded reduced slice, giving a countable closed negligible cover.

The formal bridge should therefore not restate the whole IFT at once.  It
should first prove:

    if a reduced slice image is contained in the union of countably many
    images of differentiable maps

        Fk : real^2 × real^n → (real^2)^n,

    and each image is closed, then that slice image has a closed negligible
    cover.

Then a D4 capstone should say: if every reduced chart slice admits such
countable low-dimensional parametrizations, then

    branchP_indep_closed_cover_core_all.

After that, the only missing theorem is the rank/IFT construction of the
local parametrizations `ψα`.

### 7aa. The exact IFT output to feed §7z

The §7z capstone wants configuration-space maps

    Fk : real^2 × real^n → (real^2)^n.

The implicit-function theorem naturally produces only base charts

    ψk : real^2 → real^2 × real^n × real,

where the codomain is the reduced base parameter `r = ((ω,t),a)`.  The free
`u` fibre is then attached afterwards.  For a fixed bounded slice `j`, define

    U_j = { u : ||u|| ≤ j+1 }.

Given a base chart `ψk` with domain `Ck ⊆ real^2`, the lifted configuration
map is

    Fk(s,u) =
      branch2_base_fibre_x_map(ψk(s), u)

on the product domain

    Ck × U_j ⊆ real^2 × real^n.

Therefore the precise remaining local theorem for chart `i` is:

1. the reduced base system `B_i(Γ,j)` is contained in
   `⋃k ψk(Ck)`;
2. each lifted map `Fk` is differentiable on `Ck × U_j`;
3. each lifted image `Fk(Ck × U_j)` is closed.

Those three facts imply the §7z countable low-dimensional parametrization
hypothesis, and therefore imply D4.  The still-open mathematical content is
only the construction of the `ψk` from the rank condition

    rank D R_i = n+1.

Equivalently, prove a local IFT theorem for `R_i` on the bounded independent
patch, then exhaust each local chart domain by closed bounded subpieces so
the lifted images are closed.

### 7ab. What is still missing to finish D4

D4 is reduced to one hard local analytic theorem.  For every independent
steering patch `Gamma`, every bounded slice `j`, and each of the two
projective covector charts, prove the predicate now named formally as

    branch2_chart*_reduced_base_regular_rank

and then derive

    branch2_chart*_reduced_base_IFT_parametrizations.

The regular-rank predicate says that at each point of the reduced base zero
set, the derivative of

    branch2_chart*_reduced_base_residual

is onto `real x real^n`.  Since the domain is `real^2 x real^n x real`, this
is the formal version of the rank `n+1` statement.

The IFT-parametrization predicate then means producing countably many sets
`Ck subset real^2` and
maps

    psik : real^2 -> real^2 x real^n x real

such that the reduced base zero set is contained in `union_k psik(Ck)`, and
such that the lifted maps

    Fk(s,u) = branch2_base_fibre_x_map(psik(s),u)

are differentiable on `Ck x U_j` and have closed images there.

The informal proof should run as follows.

1. In each projective chart, write the reduced residual map as

       R_i : real^(n+3) -> real^(n+1).

   The domain variables are `(omega,t,a)`: two steering variables, one scalar
   `t`, and the `n` normalized fibre coefficients `a`.  The residual equations
   are the branch-2 equations after the `u`-moment cancellation from Section
   7w, so the base system no longer contains the free `u` fibre.

2. Prove the rank statement on the independent patch:

       rank D R_i(omega,t,a) = n+1

   at every point of the reduced base system.  This is the only genuinely new
   analytic calculation left.  The earlier dimension count predicts exactly a
   two-dimensional zero set, and the two free parameters are the two steering
   coordinates left after solving the remaining `n+1` variables.

3. Apply the implicit-function theorem locally.  At each solution point,
   choose an invertible `(n+1) x (n+1)` minor of `D R_i`; solve those `n+1`
   variables as a C1, in fact analytic, function of the two remaining
   variables.  This gives a local base chart

       psi_alpha : real^2 -> real^2 x real^n x real

   whose image contains the nearby reduced base solutions.

4. Make the local cover countable.  Use rational boxes/balls inside the IFT
   neighborhoods and then a closed bounded exhaustion of each local domain.
   On each closed bounded piece, `psi_alpha` is continuous and the bounded
   fibre domain `U_j` is compact, so the lifted image `Fk(C x U_j)` is closed.

5. Feed the resulting countable family to

       branchP_indep_closed_cover_core_all_of_reduced_base_IFT_parametrizations.

The formal endpoint is split accordingly:

    branch2_reduced_base_regular_rank_all
      ==> branch2_reduced_base_IFT_parametrizations_all
      ==> branchP_indep_closed_cover_core_all.

The first implication is the hard calculation plus IFT/countable-chart
exhaustion.  The second implication is now formalized in
`branchP_indep_closed_cover_core_all_of_reduced_base_IFT_parametrizations`.

### 7ac. IFT-ready coordinates are now the right formal target

The reduced base parameter was originally represented as

    ((omega,t),a) : (real^2 x real^n) x real.

The regular-value theorem in `Regular_Value_Theorem.thy` wants the domain split
as

    omega : real^2
    y     : real^n x real,

so the IFT-ready parameter is

    (omega,(t,a)) : real^2 x (real^n x real).

The formalization now has the reassociation maps

    branch2_base_assoc
    branch2_base_unassoc

and the two IFT-ready residuals

    branch2_chart1_reduced_base_IFT_residual
    branch2_chart2_reduced_base_IFT_residual.

These residuals have exactly the shape

    real^2 x (real^n x real) -> real^n x real,

so `regular_value_local_chart` applies directly.  The local chart lemmas now
say: if the IFT-ready residual is C1 on `UNIV`, vanishes at `z0`, and its
derivative at `z0` is onto, then there is a local chart

    phi : real^2 -> real^2 x (real^n x real)

through `z0` whose image lies in the residual zero set.

The D4 capstone still wants unassociated base charts

    psi : real^2 -> (real^2 x real^n) x real.

This is now bridged formally: a countable cover by associated-coordinate
charts `phi` implies the old `psi`-chart predicate by taking

    psi(s) = branch2_base_unassoc (phi(s)).

Therefore the exact remaining theorem is now:

    branch2_reduced_base_regular_rank_all
      ==> branch2_reduced_base_assoc_IFT_parametrizations_all.

To prove it, finish three pieces:

1. build the C1 derivative fields `G'` for the two IFT-ready residuals;
2. prove the `n+1` surjectivity/rank calculation on the reduced base zero set;
3. use `regular_value_local_chart`, Lindelof, and closed bounded exhaustion to
   produce `branch2_reduced_base_assoc_IFT_parametrizations_all`.

### 7m. The user's solo formalization of the full branch-2 cover pipeline
(2026-07-13; written up by Claude, architecture and Isabelle by the user)

While the assistant was blocked by tool outages, the user independently
built and verified (~2900 lines, `Scratch_D4Branch.thy` now 5161 lines,
BUILD_EXIT=0, 0 sorry) the complete "cover, not emptiness" pipeline for
the non-aligned residual sketched in \<section>7k:

**The pipeline** (each stage a verified subset/equivalence chain from
`branch2_bad` down to the final covers):
  1. `tu_param_map` + `branch2_bad_subset_tu_system_image`: the (t,u)
     frame of \<section>7k made formal -- every non-aligned BadXGW point is the
     image of a (t,u)-system solution.
  2. Moment pullbacks `phase_t`, `A_t_moment`, `M1/M2_tu_moment` and the
     radial slot formula chain (`gradU_radial_slot_rhs` \<rightarrow> \<dots> \<rightarrow>
     `branch2_tu_radial_moment_formula_locus`): the branch-2 residuals as
     EXPLICIT trig-polynomial expressions in (t,u).
  3. Projective covector charts `ell_chart1`/`ell_chart2` (\<lambda>=(1,a) and
     \<lambda>=(a,1)) -- \<section>7b's idea, landed at the correct level of the problem.
  4. **The key structural discovery (the piece \<section>7k was missing): the
     u-elimination lemmas** (`tu_coord_combo_special_no_u`,
     `M12_tu_moment_combo_special_no_u`): on the SPECIAL covector
     combination, all u-dependence cancels from the residuals.
     Consequence: the branch-2 system descends to a "reduced base" system
     on (\<omega>, t, a) alone, with the u's an EXPLICIT free fibre -- branch-2
     becomes exactly as explicitly parametrizable as the aligned locus
     was in \<section>7j (where the assistant had assumed t would remain
     implicit-only and the architecture would need Hessian-regularity of
     the potential \<Phi>).
  5. Reduced-base charts \<times> u-slices (`branch2_lifted_base_chart_x_map`,
     `branch2_u_slice_domain`), bounded/slice exhaustion, and the reused
     lowdim engine (`closed_negligible_cover_of_lowdim_image`, source
     dimension n+2 < 2n): closed negligible covers from ANY countable
     differentiable parametrization of the reduced base.
  6. assoc/unassoc plumbing into IFT-range form, and two final capstones
     (`branchP_indep_closed_cover_core_all_of_reduced_base_regular_rank_
     and_(assoc_)IFT_chart_theorem`) that isolate D4's ENTIRE remaining
     mathematical content to two inputs:
       (a) `branch2_reduced_base_regular_rank_all` -- transversality of
           the reduced base system (the honest open math; numerically
           true per \<section>7k's overdetermination analysis);
       (b) the bridge `regular_rank \<Longrightarrow> (assoc_)IFT_parametrizations_all`
           -- an instance of the C\<^sup>1 IFT chart theorem; the heap's
           `regular_value_local_chart` engine is the natural discharger,
           and `branch2_chart*_reduced_base_IFT_residual_local_chart` are
           already shaped to receive it.

The assistant's contribution to this round: two fixes for the
implicit-type-variable trap (phantom `V` in the `_of_assoc` lemmas -- a
terminal `.` failing on identically-PRINTED fact/goal because the
statement's inferred type variable differed from the body's explicit 'n;
fixed with explicit `fixes V`), and independent batch verification.

**Honest status of D4 after \<section>7j+\<section>7m**: aligned residual closed
UNCONDITIONALLY; non-aligned residual closed CONDITIONALLY on (a)+(b).
(b) is machinery. (a) is the one genuine open mathematical claim left in
all of D4. Standard caveat per the verify-stub-statements discipline: the
capstones' CONCLUSION is the heap-pinned `branchP_indep_closed_cover_core_
all` (cannot be accidentally weakened), so the residual risk sits only in
the two hypotheses being harder to discharge than intended -- (a)'s
definition should be sanity-checked against a numerical rank evaluation
at a reduced-base solution before proof investment.

### 7n. Semi-formal audit of `branch2_reduced_base_regular_rank_all`: the
hypothesis is UNSATISFIABLE as stated (an exact sum identity), and the
concrete repair (2026-07-13, Claude, session 5)

Before investing in the rank proof, ran the discipline-mandated numerical
audit of the EXACT `branch2_chart1_reduced_base_residual` at genuine
system points (\<omega> free so the solver can find the consistency locus).
Findings, in order of discovery:

1. **First pass (unconstrained)**: ranks 2-6 of the needed 7, never 7.
   Classification traced the worst families to `L := \<gamma>\<^sub>1+a\<gamma>\<^sub>2 = 0` -- which
   forces `det(Dcvec) = 0`, EXCLUDED by BadXGW but never threaded into the
   base system. Repair candidate #1: add `1/Suc j \<le> \<bar>det (matrix (Dcvec_dip
   \<omega>0 \<omega>s \<omega>))\<bar>` to the bounded pieces (bad points satisfy it; the whole
   subset chain survives).
2. **Second pass (in-box, det-bounded, non-collinear)**: rank UNIFORMLY
   exactly 6/7 at every clean system point -- pointing to an exact
   identity, confirmed by hand and numerically (2.3e-15 relative, at NON-
   solution points): **\<Sigma>\<^sub>m F\<^sub>m \<equiv> 0 identically** (from \<Sigma>Im\<^sub>m = 0 and
   \<Sigma>\<^sub>m Re(cnj \<phi>\<^sub>m W) = \<Sigma>\<^sub>m t\<^sub>m Re\<^sub>m = Re(cnj A W)). The radial residuals map
   into the hyperplane {\<Sigma> components = 0}, so surjectivity onto
   `real \<times> real^'n` is IMPOSSIBLE: **`branch2_reduced_base_regular_rank_
   all` as currently defined can never hold** -- it would have been an
   unprovable frontier. (Third statement-level catch of the semi-formal
   cycle, after (b4) and the L=0 family.)
3. **The repair that preserves the entire downstream architecture**:
   repurpose ONE distinguished codomain slot `m\<^sub>0` of the radial part with
   the reduced-gradU scalar `R` (\<section>7k discovery 3):
       R = p\<^sub>1V + (2g/(c\<bullet>c))\<cdot>(S\<^sub>t\<cdot>(\<gamma>\<^sub>1\<bullet>c) + S\<^sub>u\<^sup>*\<cdot>(\<gamma>\<^sub>1\<bullet>perp2 c)),
       S\<^sub>u\<^sup>* = -S\<^sub>t(\<gamma>\<^sub>2\<bullet>c)/(\<gamma>\<^sub>2\<bullet>perp2 c),  S\<^sub>t = \<Sigma>t\<^sub>mIm\<^sub>m, V = |A|\<^sup>2
   (defined on the base -- u eliminated via \<gamma>\<^sub>2\<bullet>I = 0). Bad-point images DO
   satisfy R = 0 (gradU=0 descends), so the subset chain survives WITH new
   S\<^sub>u-elimination lemmas; the F\<^sub>m equation dropped at m\<^sub>0 is implied by the
   others via the sum identity, so nothing is lost. Codomain, base
   dimension, and the 2-dim IFT charts all unchanged.
4. **Repaired-system numerics**: the sum-degeneracy is gone; full-rank 7/7
   points exist; the system is much smaller (2 in-box points in 200
   trials); ONE in-box rank-5/7 point remains (\<theta>-\<pi>/2 = +0.37) whose
   degeneracy class is not yet mapped -- more sampling + classification
   needed before finalizing the repaired rank claim (candidates: another
   excludable BadXGW conjunct such as `det HessU = 0`'s descended form, an
   `S\<^sub>t = 0`/aligned-t structure, or \<gamma>\<^sub>2\<bullet>perp2c-related; ALSO note the
   \<gamma>\<^sub>2\<bullet>perp2c \<noteq> 0 side condition of R's S\<^sub>u-elimination needs a case split
   or its own thin-locus handling).

**Concrete formal work list for the repair** (owner's call on naming):
  (i) define `branch2_reduced_gradU_scalar` (R) on the base; (ii) redefine
  the two reduced-base residuals with the m\<^sub>0-slot swap (m\<^sub>0 := SOME fixed
  index); (iii) new lemmas: gradU=0 at a bad point \<Longrightarrow> R = 0 at its base
  image (the S\<^sub>u-elimination, with the \<gamma>\<^sub>2\<bullet>perp2c case split); (iv) re-prove
  the two `*_residual_zero_imp_reduced_base_residual_zero` subset lemmas;
  (v) thread `1/Suc j \<le> \<bar>det Dcvec\<bar>` through the bounded definitions
  (chart-param + base-param + the `_exists` lemmas); (vi) keep everything
  downstream verbatim (IFT lemmas/capstones unchanged in shape).

### 7o. Codex repair pass: determinant-free slot swap is now formalized

The repaired branch-2 target in `Scratch_D4Branch.thy` now follows the
strategy of §7n, but with a slightly cleaner scalar than the first
semi-formal formula.  Instead of solving for an eliminated `u` scalar by
division, the formal proof uses the cross-combination

    L = (γ₂ · perp2 c) γ₁ - (γ₁ · perp2 c) γ₂.

This has `L · perp2 c = 0` identically, so the already-formal
`M12_tu_moment_combo_special_no_u` lemma applies directly.  The repaired
base scalar is the determinant-free expression

    R* =
      ((γ₂ · perp2 c) p₁ - (γ₁ · perp2 c) p₂) |A|²
      + g · 2 Re(cnj A · (-i) · M12_special(c,t,L)).

The key formal bridge is now proved:

    branch2_reduced_gradU_scalar_eq_gradU_cross

which says, after pulling back through the `(t,u)` chart,

    R* =
      (γ₂ · perp2 c) · gradU₁
      - (γ₁ · perp2 c) · gradU₂.

Therefore every genuine bad point, where `gradU = 0`, satisfies `R* = 0`.
This is formalized as

    branch2_reduced_gradU_scalar_zero_of_gradU_zero.

The repaired residuals

    branch2_chart1_repaired_reduced_base_residual
    branch2_chart2_repaired_reduced_base_residual

replace one fixed radial slot, `branch2_repair_slot`, by `R*` and keep all
other slots unchanged.  The old chart residual plus the bad-point
`gradU=0` condition now implies the repaired reduced residual:

    branch2_chart1_residual_zero_imp_repaired_reduced_base_residual_zero
    branch2_chart2_residual_zero_imp_repaired_reduced_base_residual_zero.

The determinant repair is also threaded into the bounded pieces:

    branch2_base_param_bounded_det
    branch2_chart_param_bounded_det.

The follow-up formal pass added determinant-bounded chart slices and proved
that every old chart image is exhausted by those slices because `BadXGW`
already contains `det Dcvec != 0`.  The repaired slice images

    branch2_chart1_repaired_reduced_slice_image
    branch2_chart2_repaired_reduced_slice_image

then cover the determinant-bounded chart slices.  The resulting capstone is

    branchP_indep_closed_cover_core_all_of_repaired_reduced_slice_covers.

This is the important logical repair: the D4 pipeline no longer needs the
unsatisfiable old residual map whose radial components always sum to zero.
It now reaches the final cover theorem from covers of the repaired reduced
slices.

What remains to completely finish D4 is now narrower and correctly stated:

1. Prove the repaired low-dimensional/IFT chart endpoint:

       branch2_repaired_reduced_base_regular_rank_all
         ==> branch2_repaired_reduced_base_assoc_IFT_parametrizations_all

   or its non-associated equivalent.

2. Prove the genuine repaired rank claim, i.e. surjectivity of the derivative
   of the slot-swapped residual on the determinant-threaded repaired base
   zero set.

3. Before investing heavily in the rank proof, classify the one numerical
   rank-5/7 repaired point from §7n.  The likely outcomes are either another
   excludable thin locus or an additional necessary residual-side condition.

### 7p. Compact IFT endpoint for the repaired system

The formal endpoint has been tightened once more.  The low-dimensional cover
engine requires closed lifted images.  Rather than carrying this as an
independent analytic burden, the repaired IFT target now has a compact-chart
variant:

    branch2_repaired_reduced_base_compact_IFT_parametrizations_all.

Here each base chart domain `C i` is compact.  The `u`-slice is compact
formally:

    compact_branch2_u_slice_domain.

Therefore

    compact (C i × branch2_u_slice_domain j),

and if the lifted map is differentiable on that product then its image is
closed by compactness:

    closed_branch2_lifted_base_chart_image_of_differentiable.

This gives a sharper D4 capstone:

    branchP_indep_closed_cover_core_all_of_repaired_reduced_base_regular_rank_and_compact_IFT_chart_theorem

with remaining bridge

    branch2_repaired_reduced_base_regular_rank_all
      ==> branch2_repaired_reduced_base_compact_IFT_parametrizations_all.

This is the correct target for the local IFT proof: apply the repaired
regular-value local chart, restrict each open chart to a small closed ball,
use Lindelof on the images of the corresponding open balls, and keep the
closed balls as the compact domains in the final parametrization.  The closed
lifted images are then automatic from compactness plus differentiability.

### 7q. C1 regular-rank interface and the first local bridge

The next formal refinement separates two assertions that were previously
compressed into the phrase "regular rank".

The old repaired predicate

```isabelle
branch2_repaired_reduced_base_regular_rank_all
```

only says: at each repaired zero, there exists some derivative of the
unassociated residual and that derivative is surjective.  That is not the
right direct input for `regular_value_local_chart`.  The IFT theorem needs a
single derivative field for the associated residual, differentiability at all
points, continuity of that derivative field, and surjectivity at the zero in
question.

The new interface is:

```isabelle
branch2_repaired_reduced_base_C1_regular_rank_all
```

with chart-level pieces

```isabelle
branch2_chart1_repaired_reduced_base_C1_regular_rank
branch2_chart2_repaired_reduced_base_C1_regular_rank.
```

For each chart this packages a field `G'` such that

```isabelle
((branch2_chart*_repaired_reduced_base_IFT_residual omega0 omegas)
  has_derivative blinfun_apply (G' z)) (at z)
continuous_on UNIV G'
surj (blinfun_apply (G' (branch2_base_assoc r)))
```

for every repaired base-system zero `r`.

This is the exact formal shape of the local analytic proof.  From this
stronger C1 predicate, the file now proves two pointwise bridges for each
repaired chart:

```isabelle
branch2_chart*_repaired_reduced_base_C1_regular_rank_local_chart
branch2_chart*_repaired_reduced_base_C1_regular_rank_cball_chart
```

The first gives the open `regular_value_local_chart` package through
`branch2_base_assoc r`.  The second shrinks it to a closed ball: there are
`u0`, `rho > 0`, `phi`, and `Dphi` such that `phi u0` is the associated
repaired zero, `phi` maps the closed ball into the zero set, `phi` has the
exposed derivative on that closed ball, `phi` is continuous there, and the
image of the open ball is an open relative zero-set neighbourhood of the
point.

The remaining compact bridge is now precise:

1. Use the open-ball images from the cball chart lemma as an open relative
   cover of the repaired associated zero set.
2. Extract a countable subcover by `countable_subcover_of_openin_cover`.
3. Keep the corresponding closed balls as compact domains.
4. Prove the lifted maps

       branch2_lifted_base_chart_x_map omega0 omegas
         (lambda s. branch2_base_unassoc (phi i s))

   are differentiable on each closed-ball times `branch2_u_slice_domain j`.
5. Conclude

       branch2_repaired_reduced_base_C1_regular_rank_all
         ==> branch2_repaired_reduced_base_compact_IFT_parametrizations_all.

After that bridge is closed, the final hard analytic task is to prove the C1
derivative fields and surjectivity for the repaired slot-swapped residuals
themselves.
