# End-to-end plan for `F0_dip_nonempty`

Written 2026-11-10.  Scope: finish the proof that the robust feasible set is
nonempty, with no hypotheses beyond `5 ≤ N` (`6 ≤ N` until 2026-11-11, see §8), `N` odd, no oracles, and a
concretely defined set.

## 1. The theorem to end on

The paper is `Paper/Geometry_Driven_Optimization_of_Passive_UAV_Relay_Arrays.pdf`
(the Applied Mathematical Modelling submission).  It does not fix numbers for
the feasible set.  Eq. (22) defines it for free parameters `d_min`,
`δ_null > 0`, `p_min < |e(θ0)|² N²`, a null direction and a large radius `R`;
the plane coefficients are fixed by the angles (Eqs. 12–14):
`A = sin θs cos φs − sin θ0 cos φ0`, `B = sin θs sin φs − sin θ0 sin φ0`,
`D = cos θ0 − cos θs`.  Nonemptiness of `F0` is **Conjecture 5** there, and
Corollary 6 assumes it.  The final theorem therefore quantifies over the
paper's parameters under the paper's conditions:

```isabelle
theorem F0_dip_nonempty_final:      (* Residual/Final/Nonemptiness_Final.thy, PROVED 2026-11-11 *)
  fixes dmin δnull pmin :: real and ωnull :: "real^2"
  assumes "5 ≤ CARD('n)" and "odd CARD('n)"
    and "0 < δnull"
    and "pmin < gain_dip design_beam * (real CARD('n))²"
    and "cvec_dip design_beam design_source ωnull ≠ 0"
  shows "∃R0. ∀R≥R0. ∃ξ κ ε. 0 < ξ ∧ 0 < κ ∧ 0 < ε ∧ ε ≤ pi / 4 ∧
     F0 (cvec_dip design_beam design_source) gain_dip R dmin
        (kx design_source - kx design_beam) (ky design_source - ky design_beam)
        (kz design_beam - kz design_source)
        ωnull design_beam (OmegaPF design_beam (pi / 4)) δnull pmin ξ κ ε
     ≠ ({} :: ((real^2)^'n) set)"
```

with `design_beam = vector [pi / 2, 0]` and `design_source = vector [0, 0]`.
`F0_dip_nonempty_final_explicit` is the same with these constants written out
and `A = −1`, `B = 0`, `D = −1`.  `F0_dip_nonempty_example` is the instance
`dmin = 1/4`, `δnull = 1/100`, `pmin = 1`, null direction `(π/2, π/2)`, where the
element gain is 1 in both directions, so no constraint is vacuous.
`regular_feasible_configuration_exists` is the statement without margins.

Every object is a definition: `F0 = Ffeas ∩ X0`
(`Nonemptiness_Robust1.thy:1559`), `cvec_dip` (`:735`), `gain_dip` (`:635`),
`gradU`/`HessU` (`:222`, `:227`), `OmegaPF` (`Robust2:670`).  `ξ, κ, ε` are the
robustness margins of the paper's `X0(ξ, κ)` and are existential there too.

Where this differs from the paper, and why:

| Paper | Final theorem | Reason |
|---|---|---|
| any angles with `0 ≤ θs < π/2 ≤ θ0 ≤ π` | `θs = 0`, `(θ0, φ0) = (π/2, 0)` | the whole chain, and the residual argument, are worked out for this steering geometry; other angles are a separate extension |
| `Ω = [θ0−π/2, θ0+π/2] × [φ0−π, φ0+π]` | `[π/4, 3π/4] × [−π, π]` | the theorem is proved on a pole-free box; the poles `θ ∈ {0, π}`, where the dipole gain vanishes to second order, are not covered (`Nonemptiness_Robust2.thy`, section on `OmegaPF`) |
| experiment: `N = 9`, `(θ0, φ0) = (90°, 120°)`, `(θs, φs) = (85°, 120°)`, null `(90°, 60°)`, `d_min = λ0/4`, `δ_null = (10⁻² e(θ0) N)²` | all `d_min`, all `δ_null > 0`, all `p_min < N²`, any null direction with `cvec ≠ 0` | covers the experiment's `d_min`, `δ_null`, `N` and a null at `θ = 90°`; not its steering angles |

What the retired conditional capstone picked instead, all of which the final
theorem replaces: `pmin = 0` (main-beam constraint vacuous); null direction `(π, 0)`,
where `gdip π = 0`, so the null constraint is vacuous as well; and
`A = B = 0`, `D = 1` (planar spacing), where the paper's formulas give
`A = −1`, `B = 0`, `D = −1` for these angles.  `feasible_witness_exists` and
`ball_inside_Ffeas` are already general in all of these, so this costs little.

"Done" means: this theorem is in a session built with
`quick_and_dirty = false` from `Applied_Math_Base` up, and the oracle check of
§5 passes on it.

### Concreteness rules (added 2026-11-10 after the user's question)

Oracle-free is not the same as meaningful.  Several results in this project
are schemas about arbitrary sets or functions with assumed properties
(`thm_final`, `prop_h0res_meager`, `parametric_transversality_negligible_stub`,
the `…_from_…`/`…_of_…` wrappers), and the present capstone assumes its two
core predicates for every `V ctr δ ω0 ωs`, where they may be false.  So:

1. The final statement has no set-valued or function-valued variable.  Its only
   variables are the index type `'n` and the paper's real parameters, under
   the paper's conditions (§1).
2. No lemma counts as progress until its hypotheses are discharged, in the same
   development, for the actual objects (`BadXGW`, `gradU`, `HessU`,
   `cvec_dip`, `gain_dip`).  WP3 must start from `BadXGW` itself.
3. Every set-valued or function-valued hypothesis that remains in a lemma is
   listed in the diary with the theorem that discharges it.
4. The final theory also states the margin-free fact the proof already has:

   ```isabelle
   theorem regular_feasible_configuration_exists:
     assumes "5 ≤ CARD('n)" and "odd CARD('n)"
     shows "∃x ∈ interior (Ffeas …concrete constants…).
              ∀ω ∈ OmegaPF (vector [pi/2, 0]) (pi/4).
                ¬ (gradU … x ω = 0 ∧ matrix_det (HessU … x ω) = 0)"
   ```

   and gives `ε` an explicit upper bound in the `F0` form, so the excluded ball
   cannot swallow the box.
5. Resolved 2026-11-10 from the paper: the final theorem is stated for all
   admissible `d_min`, `δ_null`, `p_min` and null directions, with the paper's
   `A`, `B`, `D` (§1).

## 2. Audit of the existing work

| Item | Finding | Evidence |
|---|---|---|
| Capstone today | `F0_dip_nonempty` (`Nonemptiness_Robust4.thy:1363`) is proved from `6 ≤ N`, odd `N` and two assumed predicates, `d3_detHess_arc_chart_core_all` and `branchP_indep_closed_cover_core_all`, each quantified over all `V ctr δ ω0 ωs`. | read |
| What the two predicates are for | Only `m5_D34_residual` (`:535`) uses them.  It needs one fact: the set `{x∈V. ∃ω∈Ω. gradU = 0 ∧ det HessU = 0 ∧ A ≠ 0 ∧ ¬surj DM ∧ det Dc ≠ 0 ∧ c ≠ 0 ∧ D_x gradU not onto}` is meager.  D3 and D4 are this one set split by `phase_collinear`. | read |
| Other strata | Regular part, beam centre (`c = 0`), steering-singular (`det Dc = 0`), array null (`A = 0`), Slater witness, continuity half: proved, no hypotheses. | read; strict rebuild (below) |
| D3 line (July) | Reduced to three residuals `D3ActualXiZeroNonphaseIncidence V y`.  Open: the "flat fold" `h11 = h11' = 0`, which needs new mathematics; the "simple fold" is a large unbuilt engine. | diary 2026-07-24 |
| D4 line (July–Aug) | The submersion hypothesis `reg1/reg2` is false at phase collisions.  Two repairs were refuted numerically.  Two `sorry`s remain (`Scratch_D4Branch.thy:9395`, `:9437`).  The last hypothesis ("drop R*") was never tested. | diary 2026-07-14, 2026-08-06 |
| `sorry` / axioms | No `sorry`, `oops`, `axiomatization` or `oracle` command in any theory on the capstone path, including the vendored Munkres library (its eight hits are comments). | grep |
| Strictness | Every session in `ROOT` has `quick_and_dirty = true`.  In that mode `fun`/`record` internals may be cheated, so "no `sorry`" does not yet mean "no oracle". | `ROOT` |
| Heaps | The whole chain from `Applied_Math_Base` up is stale (parents rebuilt in October).  Nothing can be checked without a full rebuild. | `isabelle build -n` |
| Strict rebuild + oracle check | **Passed (2026-11-10, Isabelle2025-2).** A copy of the tree with every session set to `quick_and_dirty = false` built from `Base` to `Robust4` with exit 0 and no errors (about 16 minutes). `Thm_Deps.all_oracles [F0_dip_nonempty]` is empty; the negative control reports `Pure.skip_proof`. So today's conditional capstone is oracle-free: its only gaps are the two stated hypotheses. The copy had renamed sessions (`AMStrict_*`), so the project tree and its heaps were not touched. | scratchpad build log |
| Statement shape | The current capstone quantifies existentially over all design constants.  The proof fixes them, so the concrete statement of §1 costs nothing. | read |
| Working tree | Four tracked files modified and about twenty untracked files and scratch folders, uncommitted since August. | `git status` |

Conclusion of the audit: the foundation is one meagerness statement short.
Both July lines attack that statement through rank conditions on a large
system, and both stall there.

## 2a. Platform: Isabelle2026 (in place since 2026-11-10)

The tree now targets Isabelle2026 (`~/Desktop/Isabelle/Isabelle2026`, AFP
`afp-2026-10-29`), on branch `isabelle2026`.  The last Isabelle2025-2 state is
the tag `pre-isabelle2026`; `main` is untouched.  Every session is strict.

| Isabelle2026 change | Fix |
|---|---|
| `real_arch_pow`, `real_arch_pow_inv` renamed to `arch_pow`, `arch_pow_inv` | 9 replacements in the Munkres files, now vendored in `Munkres/` (the external copy was under no version control) |
| HOL-Analysis ships `Higher_Differentiability_Multi`; a second theory of that name is rejected | the tree's copy leaves the chain: `GRAD` → `GDERIV` in `Nonemptiness_Robust1` (4 lines), one `ROOT` line; at first a bridge lemma to the AFP predicate `higher_differentiable_on`, since 2026-11-11 `Ck_on` throughout and no bridge (§8) |
| unqualified `det` is the determinant of a linear map | `det` → `matrix_det` (290 occurrences in 8 theories), `det_def` → `matrix_det_def` |
| `baby_Sard` is stated for Euclidean spaces | wrapper `baby_Sard_cart` in the old form; 5 call sites |
| `verit_minus_simplify` no longer exists | `diff_self` in one `smt` proof in `Nonemptiness_Robust3` |

Of the tree's `HigherDiff/` theories the chain used 13 facts; 10 are in
Isabelle2026 under the same name with identical `Ck_on`/`Ck_at` definitions.
`HigherDiff/`, `Analytic/`, `Appendix/AnalyticBridge/`, `Appendix/Wiring/` and
the `M5_Dev_*` scratch sessions are not ported (Isabelle2025-2 archive; their
session entries are commented out at the end of `ROOT`).  WP3 must therefore
re-derive or port the few slot-calculus lemmas it needs from
`Scratch_D4Branch.thy` and the aligned cover from `Scratch_AlignedCover.thy`.

## 3. The route to the end

The residual can be closed by one elementary argument that uses no rank
condition on the large system.  The full semi-formal proof is `Sketch.md` §8;
the two scripts in `tools/` check each formula numerically.

In `(t,u)` coordinates along and across `c(ω)`, a non-aligned residual point
satisfies three equations, each involving a variable the others do not:

1. one radial equation, linear in `cos φ`, so `ω` lies on an explicit curve;
2. one equation `f_m(t) = 0` in `t` alone, whose zero set is negligible;
3. one equation linear in `u_m`, so `u_m` is an explicit function of the rest.

So the residual is the image, under an explicit differentiable map between
spaces of equal dimension `2N`, of a negligible set.  That image is negligible
(`negligible_differentiable_image_negligible`), and compact exhaustion makes
the pieces closed.  Aligned points are already covered
(`aligned_bad_closed_cover`).

Why this has an end where the old routes did not: it never asks whether the
`N+1` equations are independent.  Phase collisions, the corank-2 points and
the flat fold are all inside the negligible set and need no separate case.

## 4. Work packages

Each package is one theory with one named result.  Sizes are estimates of new
Isabelle text.

| WP | Theory | Result | Depends on | Size |
|---|---|---|---|---|
| 0 | `ROOT` | **done**: Isabelle2026, all sessions strict, `Applied_Math_Oracle_Audit` in `ROOT` | — | config |
| 1 | `Residual_Measure` | `negligible_of_countable_line_slices` (Sketch L5a) | HOL-Analysis | ~100 lines |
| 2 | `Residual_Null_Set` | `negligible {t. s_m t ≠ 0 ∧ f_m t = 0}` (L4) | WP1, HOL-Complex_Analysis | ~200 |
| 3 | `Residual_Equations` | L1–L3: the three equations and the six-way case split at a non-aligned residual point | Robust4; slot calculus ported from `Scratch_D4Branch` | ~450, half ported |
| 4 | `Residual_Charts` | each chart map differentiable on its open domain; compact pieces closed and negligible | WP2, WP3 | ~400 |
| 5 | `Residual_Cover` | `m5_D34_residual_design`: the residual is meager at the design point, no hypotheses | WP4; aligned cover ported from `Scratch_AlignedCover` | ~150 new, ~570 ported |
| 6 | `Nonemptiness_Final` | `F0_dip_nonempty_final` (§1) | WP5; hypothesis-free copies of five Robust4 lemmas | ~300, mostly copied |
| 7 | close-out | §5 passes; `README`, `ROOT`, diary updated; `d3core`/`branchcore` and the D3/D4 scratch sessions retired | all | — |

Status (2026-11-10), all on Isabelle2026 in `Residual/` (session
`Applied_Math_Residual_Analysis`, strict, oracle check empty):

* **WP1 done.** `Residual_Measure.thy`: `emeasure_lborel_countable_slices`,
  `negligible_of_countable_line_slices`, and the open-and-closed corollary.
* **WP2 done.** `Residual_Null_Set.thy`: definitions `res_s`, `res_q`, `res_W`,
  `res_P`, `res_f`; `res_on_line`; `countable_slice_zeros`;
  `negligible_res_f_zeros`.  These are concrete functions of the phase vector,
  but by concreteness rule 2 they count only once WP3 ties them to `BadXGW`.
* **WP3 done.** `Residual/Stratum/Residual_Equations.thy` (session
  `Applied_Math_Residual`, on top of `Nonemptiness_Robust4`):
  `BadXGW_point_equations` — for `x ∈ BadXGW ω0 ωs {ω}`, `sin θ ≠ 0` and an
  antenna `m` with `res_s m t ≠ 0`, where `t = phase_coords c x` and
  `u = perp_coords c x`:
  (E2) `res_f m t = 0`;
  (E1) `gd · res_s m t · cross2 c γ2 + gain_dip ω · (res_s m t + res_q m t) · cross2 γ1 γ2 = 0`;
  (E3) `2 · gain_dip ω · cross2 γ1 γ2 · Σ_b u_b · res_s b t = gd · cross2 (perp2 c) γ2 · res_W t`.
  This holds for every `ω0`, `ωs`: it starts from `BadXGW` itself and uses no
  steering-specific formula (concreteness rule 2).
  `Residual/Stratum/Residual_Design.thy`: for `design_beam = (π/2, 0)`,
  `design_source = (0, 0)` the three determinants are explicit
  (`design_cross2`), (E1) becomes `K · cos φ = Num` (`design_radial_equation`),
  and `K = 0` forces `cos θ = 0` (`design_radial_degenerate`).
* **WP4 done.** `Residual/Stratum/Residual_Charts.thy`: `tu_param_map` and its
  reconstruction lemma; the chart map `chart_map th ph m` on the source
  `(real^'n) × (real^'n)`; `chart_map_differentiable`; and the engine
  `chart_image_cover` (for angle functions differentiable on an open set, the
  image of `{res_f m t = 0}` lies in countably many compact negligible sets;
  uses `negligible_res_f_zeros`, `negligible_Times_UNIV` and
  `negligible_differentiable_image_negligible`).
  `Residual/Stratum/Residual_Chart_Cover.thy`: six charts per antenna
  (`chart_th`, `chart_ph`, `chart_Dom`), `nonaligned_point_in_chart_image`
  (every non-aligned point of `BadXGW` over the box is in a chart image), and

  ```isabelle
  theorem nonaligned_residual_cover:
    "∃K :: nat ⇒ ((real^2)^'n) set.
       {x. ∃ω∈OmegaPF design_beam (pi / 4). x ∈ BadXGW design_beam design_source {ω}
             ∧ (∃m. res_s m (phase_coords (cvec_dip design_beam design_source ω) x) ≠ 0)}
         ⊆ (⋃n. K n)
       ∧ (∀n. closed (K n)) ∧ (∀n. negligible (K n))"
  ```

  It has no hypotheses.  Added on the way: `design_perp_equation` and
  `BadXGW_design_nondegenerate` (`Residual_Design`), `negligible_Times_UNIV`
  (`Residual_Measure`), `res_f_zeros_borel` (`Residual_Null_Set`).
* **WP5 done.** `Residual/Stratum/Residual_Aligned.thy`: the aligned cover
  `aligned_bad_closed_cover` (needs `4 ≤ CARD('n)`), ported from the
  Isabelle2025-2 scratch theory; it built unchanged.
  `Residual/Stratum/Residual_Meager.thy`: `aligned_conf_iff_res_s`,
  `BadXGW_design_cover` (the whole of `BadXGW` over the design box has a
  countable closed negligible cover), and `residual_meager_design`: for every
  `V` and `4 ≤ CARD('n)`, the set in the conclusion of `m5_D34_residual` —
  with `ω0 = design_beam`, `ωs = design_source`, centre `design_beam`, half-width
  `π/4` — is meager.  **Neither `d3core` nor `branchcore` is assumed.**
* **WP6 done.** `Residual/Final/Nonemptiness_Final.thy` (session
  `Applied_Math_Final`): `design_feasible_interior` (the feasible body has
  nonempty interior for every `dmin`, every `δnull > 0`, every
  `pmin < gain_dip design_beam · N²`, every null direction with `cvec ≠ 0`,
  arbitrary `A B D`, all large `R`); the re-threaded lemmas
  `Phi_bad_meager_design`, `regular_config_exists_design`,
  `no_degenerate_to_sphere_annulus_bounded` (exports `ε ≤ δ`),
  `F0_nonempty_of_witness_radius` (keeps `ε`) — the first, second and fourth
  were replaced on 2026-11-11 by `degenerate_configurations_meager`, a direct
  proof of `regular_feasible_configuration_exists`, and `X0_of_witness_radius`
  (§8);
  `regular_feasible_configuration_exists`; `F0_dip_nonempty_final`,
  `F0_dip_nonempty_final_explicit`, `F0_dip_nonempty_example`.
  The oracle audit now checks the final theorem.
* **WP7 done (2026-11-11).** The conditional `F0_dip_nonempty`, the predicates
  `d3_detHess_arc_chart_core(_all)`, `branchP_indep_closed_cover_core(_all)`,
  `branchP_indep_chart_core`, `D3BadXG_H0core` and every lemma assuming them
  are removed from `Nonemptiness_Robust4` (1524 → 517 lines; the unconditional
  lemmas stay).  `tools/make_final_blocks.py` is removed with them.  The
  Isabelle2025-2 directories stay in place as an archive, not built (README,
  "Archive").  `README.md`, `ROOT` and the repository `README.md` describe the
  final state.
* Build everything and audit: the command in `ROOT` (target
  `Applied_Math_Oracle_Audit`, which sits on `Applied_Math_Final`).  The two analysis theories alone:
  `cd Residual && ~/Desktop/Isabelle/Isabelle2026/bin/isabelle build -b -d . Applied_Math_Residual_Analysis` (about 20 seconds).

Notes on the packages.

* **WP0** comes first because every later check needs fresh heaps anyway.  The
  strict audit already showed the existing chain builds unchanged with
  `quick_and_dirty = false`, so this is a `ROOT` edit and one rebuild.
* **WP1 and WP2** are the only new mathematics, and both are small.  WP2 uses
  `holomorphic_countable_zeros` on the entire extension of one slice function.
* **WP3** starts from `gradU_dip_xderiv_slot` (`Scratch_D4Branch.thy:1194`),
  which already gives every slot derivative of `gradU`.  A dependency scan
  decides what to port (`slot`, `perp2`, `tu_param_map`, `dEjm_slot_value`).
* **WP4** follows the pattern of `align_param_map_differentiable_on`,
  `compact_align_dom`, `align_image_closed` in `Scratch_AlignedCover`.
* **WP6** copies `meager_rank_deficient_stratum`, `Phi_bad_meager_dip`,
  `regular_feasible_point_dip`, `regular_feasible_witness_dip` and the capstone
  with the two hypotheses deleted and the constants fixed.  The assumed
  predicates cannot be proved as stated (the D3 one is about an enlarged set),
  so they are bypassed, not discharged.

## 5. Verification protocol (the "no oracles" requirement)

1. `quick_and_dirty = false` in every session of `ROOT` (done); build
   `Applied_Math_Oracle_Audit` from `Applied_Math_Base` up with `-b`.
2. `Audit/Oracle_Audit.thy` fails the build if `Thm_Deps.all_oracles` of the
   audited theorems is not empty.  It checks `F0_dip_nonempty_final`, its
   explicit form, the example and the WP1–WP5 theorems.
3. Negative control: `Audit/Control/Oracle_Audit_Control.thy` (the only
   `quick_and_dirty` session) fails if the same test misses a `sorry`.
4. `grep` for `axiomatization`, `oracle`, `sorry`, `oops` over every theory in
   the import closure that is not part of the Isabelle distribution or the AFP.
5. Record the commit hash and the build log line in the diary.

**Carried out 2026-11-11 for commit `3876566`:** all five steps pass, from
scratch, in an isolated copy with renamed sessions (13 sessions, 15 minutes,
exit 0; details in the diary entry of that date).

## 6. Superseded work (stop, keep as archive)

* D3: `M5_Dev_ActualD3*`, `M5_Dev_D3ResidualSplit`, the simple-fold engine and
  the flat-fold question.
* D4: the reduced-base IFT route in `Scratch_D4Branch` after line ~2450, the
  `reg1'/reg2'` hypotheses, both `sorry`s, the collision numerics.
* The real-analytic stack (`Analytic/`, `D34_*`) leaves the capstone path.  It
  stays valid as a library.

## 7. Risks

| Risk | Effect | Handling |
|---|---|---|
| A formal definition differs from the formula used in `Sketch.md` §8 | L2 fails to prove | L1 is already a formal lemma; WP3 derives the equations from it, so a mismatch shows there at once |
| Ported lemmas pull in the analytic bridge | larger strict chain | dependency scan before porting; fallback is to parent the new session on `Applied_Math_D3_Wiring` |
| Chart differentiability is slow to elaborate in the big heap | time | `vec_nth` not `$`; small lemmas; `eval_at -t` |

## 8. Next step

None for the theorem: WP0–WP7 are done.

2026-11-11, after WP7: the hypothesis `6 ≤ N` was lowered to `5 ≤ N`.  It had
entered through one stratum only, the steering-singular one (`det Dc = 0`),
which used the six-moment submersion `fixed_c_nonsurj_nowhere_dense`.  That
stratum is now `meager_steering_singular` (`Nonemptiness_Robust3.thy`): at a
fixed angle with `c ≠ 0`, criticality alone is a nowhere dense condition
(`critical_slice_nowhere_dense`, `Nonemptiness_Robust2.thy`, `2 ≤ N`).
`Phi_bad_meager_design` now splits the degenerate set into five strata (array
null, steering-singular, beam centre, regular, residual).  The bound 5 is
`4 ≤ N` of `residual_meager_design` together with oddness.  The six-moment
theorems are kept; the final theorem does not depend on them
(`tools/final_deps/Final_Deps.thy`).

2026-11-11, second change: the theorems are stated as in the write-up.
`Nonemptiness_Final.thy` defines `degenerate_configurations` and proves
`degenerate_configurations_meager` (the five strata),
`degenerate_configurations_nowhere_dense` (closed and nowhere dense),
`nondegenerate_in_X0` (margins for a configuration outside the set),
`X0_lower_margins_ball`, `F0_dip_interior_nonempty` (for suitable margins `F0`
contains a ball) and, as a corollary, `F0_dip_nonempty_final` (statement
unchanged).  The condition `¬ surj (DM_paper_x …)` was removed from `BadXGW`
and from the main-beam stratum (`meager_main_beam`), where it was not used.
`Poles_And_Fixed_Margins.thy`: `pole_degenerate`, `X0_empty_on_box_with_pole`,
`feasible_ball_outside_X0`, `design_cvec_eq_0_iff`.

2026-11-11, third change: derivatives use the Isabelle2026 library only.
Smoothness is `Ck_on` (the AFP entry Smooth_Manifolds and the bridge theory are
no longer needed), and the Jacobian condition in `BadXGW` and in the stratum
lemmas is `jacobian (cvec_dip ω0 ωs) (at ω)` (`jacobian_cvec_dip` relates it to
the explicit formula `Dcvec_dip`).
  Possible extensions, not needed for
it: other steering angles (the residual equations of WP3 already hold for all
angles; the charts and the other strata would need the design facts for them),
and an explicit `R0`.
