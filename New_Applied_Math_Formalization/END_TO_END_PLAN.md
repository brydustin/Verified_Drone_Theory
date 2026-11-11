# End-to-end plan for `F0_dip_nonempty`

Written 2026-11-10.  Scope: finish the proof that the robust feasible set is
nonempty, with no hypotheses beyond `6 ≤ N`, `N` odd, no oracles, and a
concretely defined set.

## 1. The theorem to end on

```isabelle
theorem F0_dip_nonempty_final:
  assumes "6 ≤ CARD('n)" and "odd CARD('n)"
  shows "∃R ξ κ ε. 0 < ξ ∧ 0 < κ ∧ 0 < ε ∧
     F0 (cvec_dip (vector [pi/2, 0]) (vector [0, 0])) gain_dip
        R (1/2) 0 0 1 (vector [pi, 0]) (vector [pi/2, 0])
        (OmegaPF (vector [pi/2, 0]) (pi/4)) 1 0 ξ κ ε
     ≠ ({} :: ((real^2)^'n) set)"
```

Every object is a definition, not a parameter: `F0 = Ffeas ∩ X0`
(`Nonemptiness_Robust1.thy:1559`), `cvec_dip` (`:735`), `gain_dip` (`:635`),
`gradU`/`HessU` (`:222`, `:227`), `OmegaPF` (`Robust2:670`).  The design
constants are the ones the current proof already picks.  `ξ, κ, ε` are
robustness margins and are existential by nature.  `R` is the radius of the
Slater witness plus one; making it a closed-form number is optional (WP6).

"Done" means: this theorem is in a session built with
`quick_and_dirty = false` from `Applied_Math_Base` up, and the oracle check of
§5 passes on it.

### Concreteness rules (added 2026-11-10 after the user's question)

Oracle-free is not the same as meaningful.  Several results in this project
are schemas about arbitrary sets or functions with assumed properties
(`thm_final`, `prop_h0res_meager`, `parametric_transversality_negligible_stub`,
the `…_from_…`/`…_of_…` wrappers), and the present capstone assumes its two
core predicates for every `V ctr δ ω0 ωs`, where they may be false.  So:

1. The final statement has no free variable other than the index type `'n`,
   and no hypothesis other than `6 ≤ CARD('n)` and `odd CARD('n)`.
2. No lemma counts as progress until its hypotheses are discharged, in the same
   development, for the actual objects (`BadXGW`, `gradU`, `HessU`,
   `cvec_dip`, `gain_dip`).  WP3 must start from `BadXGW` itself.
3. Every set-valued or function-valued hypothesis that remains in a lemma is
   listed in the diary with the theorem that discharges it.
4. The final theory also states the margin-free fact the proof already has:

   ```isabelle
   theorem regular_feasible_configuration_exists:
     assumes "6 ≤ CARD('n)" and "odd CARD('n)"
     shows "∃x ∈ interior (Ffeas …concrete constants…).
              ∀ω ∈ OmegaPF (vector [pi/2, 0]) (pi/4).
                ¬ (gradU … x ω = 0 ∧ matrix_det (HessU … x ω) = 0)"
   ```

   and gives `ε` an explicit upper bound in the `F0` form, so the excluded ball
   cannot swallow the box.
5. Open decision for the user: the constants the current proof picks are
   `pmin = 0`, `δnull = 1`, `dmin = 1/2`, `A = B = 0`, `D = 1`.  With `pmin = 0`
   the main-beam constraint is vacuous.  The residual argument holds for any
   open `V`; only the feasibility witness depends on these values.

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

## 2a. Platform: Isabelle2026 (decided 2026-11-10)

New work is done on Isabelle2026 (`~/Desktop/Isabelle/Isabelle2026`, AFP
`afp-2026-10-29`).  The whole capstone chain builds there in strict mode after
six small changes, and `Thm_Deps.all_oracles [F0_dip_nonempty]` is empty there
too.  `tools/isabelle2026_port/make_copy.sh TARGET` reproduces the ported copy
from the tree; the tree itself is still the Isabelle2025-2 version.

| Isabelle2026 change | Fix |
|---|---|
| `real_arch_pow`, `real_arch_pow_inv` renamed to `arch_pow`, `arch_pow_inv` | 9 replacements in the vendored Munkres files |
| HOL-Analysis ships `Higher_Differentiability_Multi`; a second theory of that name is rejected | drop the tree's copy from the chain: bridge lemma `Ck_on_iff_higher_differentiable_on` in `Higher_Diff_Bridge_2026.thy`, `GRAD` → `GDERIV` in `Nonemptiness_Robust1` (4 lines), one `ROOT` line |
| unqualified `det` is the determinant of a linear map | `det` → `matrix_det` (290 occurrences in 8 theories), `det_def` → `matrix_det_def` |
| `baby_Sard` is stated for Euclidean spaces | wrapper `baby_Sard_cart` in the old form; 5 call sites |
| `verit_minus_simplify` no longer exists | `diff_self` in one `smt` proof in `Nonemptiness_Robust3` |

Of the tree's `HigherDiff/` theories the chain used 13 facts; 10 are in
Isabelle2026 under the same name with identical `Ck_on`/`Ck_at` definitions.
The `Analytic/` and `D34_*` theories are not ported; they are off the capstone
path (§6).

**Open step (needs the user's choice):** make the port canonical, either in
place (the tree then no longer builds on Isabelle2025-2) or as a generated
sibling tree.  WP3 onwards needs `Nonemptiness_Robust4` on Isabelle2026.

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
| 0 | `ROOT` | all sessions `quick_and_dirty = false`; chain rebuilt; oracle check on today's conditional capstone is empty | strict audit result | config |
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
* Build: `cd Residual && ~/Desktop/Isabelle/Isabelle2026/bin/isabelle build -b -d . Applied_Math_Residual_Analysis` (about 20 seconds).

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

1. `quick_and_dirty = false` in every session of `ROOT`; build
   `Nonemptiness_Final`'s session from `Applied_Math_Base` up with `-b`.
2. At the end of `Nonemptiness_Final`:
   `ML ‹case Thm_Deps.all_oracles [@{thm F0_dip_nonempty_final}] of [] => () | os => error …›`.
3. Negative control: a `sorry` lemma in a `quick_and_dirty` session must make
   the same check report `Pure.skip_proof`.  (Verified working today.)
4. `grep` for `axiomatization`, `oracle`, `sorry`, `oops` over every theory in
   the import closure that is not part of the Isabelle distribution or the AFP.
5. Record the commit hash and the build log line in the diary.

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

Choose how to make the Isabelle2026 port canonical (§2a), then WP3.
