# Formalization Diary — Antenna Feasibility Nonemptiness

A running, dated log of the Isabelle/HOL formalization of the antenna-feasibility
*nonemptiness* theorem. Kept partly as a development record and partly as raw
material for the paper's "formalization notes." Entries are newest-first within a
day; commit hashes refer to the working repo (`antenna-nonemptiness`), mirrored
into the monorepo `Verified_Drone_Theory` under `Applied_Math_Formalization/`.

---

## 2026-06-06 (cont.) — Brick 5 + **leaf [E] `DM_paper_x_regular_point_exists` CLOSED** (commit 4e4e437)

First sorry of `F0_dip_nonempty` eliminated (Robust2 7 → 6 sorries). Three new lemmas:
- `sum_reindex_embed` — `⟦inj ι; ⋀n. n∉range ι ⟹ g n = 0⟧ ⟹ (∑n∈UNIV. g n) = (∑k∈UNIV. g(ι k))`
  (`sum.mono_neutral_right` + `sum.reindex`). Reusable.
- `DM_paper_x_regular_point_c0_gen` (brick 5) — lifts the dim-6 regular point
  `DM_paper_x_regular_point_c0` to `CARD('n) ≥ 6`: embed `x₀ :: (real^2)^6` via an injection
  `ι : 6 ↪ 'n` (`card_le_inj`), pad off-image with 0. Each of the six `d_*_moment_x` sums
  reindexes (off-image terms vanish — every summand is linear in `h$n`, `h$j=0`; on-image
  terms agree since `phase`/`d_phase`/weights are per-point), giving
  `DM_paper_x (embed) c₀ = DM_paper_x x₀ c₀` componentwise (via `DM_paper_x_eq_MM` +
  `Moment_Map.DM_paper_x_def` + `DM_paper_x_components`), hence surjective.
- `DM_paper_x_regular_point_exists` (was the sorry) — `c≠0`, `CARD('n)≥6`: pick `T` with
  `Tᵀc=c₀` (`steering_transport_exists`), regular `y₀` at `c₀` (brick 5),
  `DM_paper_x_surj_transport` (4c) ⟹ `surj (DM_paper_x (applyT T y₀) c)`.

Many parse/overload traps along the way (all now in memory): bare `inv` = group inverse
(use `inv_into UNIV`); `(∑x::T. _)` = `suminf`/nat (use `∑x∈UNIV`); `inj_on` via
`simp(inj_eq inj_on_def)` loops; two `DM_paper_x` (Paper vs Moment_Map, bridge
`DM_paper_x_eq_MM`). The user fixed the final `key` step (the `DM_paper_x_eq_MM` bridge)
in the scratch; I verified + folded into Robust2.

**[F] `DM_paper_x_open_dense_surjective_gen` proven** (commit f710616) — reduces to the
rank-semicont keystone: `M_paper` differentiable (`has_derivative_M_paper_x`) + a regular
point (just proven) ⟹ `rank_lower_semicont_open_dense_propagation` on UNIV gives an open
dense regular set; intersect with `V` (`open_Int_closure_subset`). Robust2 sorries 6 → 5.

**Leaves remaining (7), all heavy analytic/transversality:** `rank_lower_semicont…` (Paper),
the engine `regular_zero_set_projection_charts_core_2d` (Parametric), four `meager_*_stratum`,
`no_degenerate_to_sphere_annulus` (Robust2).

**⚠ Soundness flag on `rank_lower_semicont_open_dense_propagation` (Paper, sorry).** Its
assumptions give only `(F has_derivative DF x)(at x within V)` + one regular point. Openness
of the regular stratum needs `DF` *continuous* (C¹), and **density needs `F` real-analytic**
(else rank-deficiency need not be nowhere dense) — neither is assumed. As stated it's likely
not provable. `M_paper` is real-analytic and C¹, so the fix is to either (a) add those
hypotheses and supply them at the [F] call site, or (b) prove the `M_paper`-specific version
directly (general-`'n`/general-`c` analogue of the dim-6 `m_star` argument:
`nowhere_dense_m_star_zeros`). [E] does NOT depend on this — it rests on the dim-6 `m_star`
existence — so [E] is solid; only [F] is contingent.

**CHOSEN ROUTE (user, 2026-06-06): prove [F] `M_paper`-specifically (option b) → fully sound.**
Design done; build is next (multi-step). The dim-6 `m_star = det(matrix(MJx))` is square only
because `(real^2)^6 ≅ real^12 ≅ complex^6`. For general `'n` the Jacobian is non-square; use the
**codomain Gram via the FIXED iso `transC : complex^6 → real^12`** (`Moment_Jacobian`, not
`'n`-dependent):
  `m_star_gen x c = det (matrix (G x c))`,
  `G x c = (transC ∘ DM_paper_x x c) ∘ adjoint (transC ∘ DM_paper_x x c) :: real^12 ⇒ real^12`.
`real^12` is Cartesian + square so `matrix`/`det` apply, and `adjoint` handles the domain — no
flattening of `(real^2)^'n`. Steps:
1. Foundation (general LA, HOL-Analysis `adjoint`): linear `A :: 'a::euclidean_space ⇒ real^'m`
   ⟹ `surj A ⟷ invertible (matrix (A ∘ adjoint A))` (surj A ⟺ inj(adjoint A) ⟺ Gram invertible;
   `invertible_det_nz`).
2. Four properties of `m_star_gen(·,c)`, fed to `lines_entire_slice_nowhere_dense`
   (`Nonemptiness_Paper`, general: continuous + entire-along-every-line + nonzero ⟹
   `nowhere_dense` zeros): (a) continuous; (b) `surj(DM_paper_x x c) ⟷ m_star_gen x c ≠ 0`;
   (c) entire-along-lines (entries `cis`/poly ⟹ entire; `adjoint` linear; `det` polynomial);
   (d) nonzero somewhere (brick 5 / `DM_paper_x_regular_point_exists`).
3. [F] = open (`open_Collect_neq`) + dense (`open_Int_closure_subset` + nowhere_dense), mirroring
   `DM_paper_open_dense_surjective`; then drop `rank_lower_semicont` from [F] entirely.

**DONE — [F] is now sound (commit `ed8cf5f`).** The whole `mstarg` plan above is built and green:
`surj_iff_gram_invertible`, `mstarg`+`surj_iff_mstarg`, `matrix_gram_entry`, `cont_mstarg`,
the general `cline_entire_d*`/`cline_entire_DM_comp` (general `d_phase` via `cline_entire_cis_linear`),
`rline_entire_mstarg`, `mstarg_nonzero`, `nowhere_dense_mstarg_zeros`, and [F] reproved via
`U = V ∩ {mstarg ≠ 0}`. **`rank_lower_semicont_open_dense_propagation` is now unused dead code**
(deletable from `Nonemptiness_Paper` → would drop the leaf count to 6). The [E]/[F] chain is fully
sound. Lessons banked: the fresh-`'n` trap (`fix e :: "(real^2)^'n"` makes a *new* type var — omit
the annotation); `metis` over big `det(matrix …)` terms blows up (chain iffs with `blast`); clean
up `eval_at` zombie poly (`timeout -s KILL` of the bash wrapper leaves the JVM→poly subtree).

## 2026-06-06 — Brick 4 complete (transport matrix + surjectivity + chain rule); fast-eval setup

**Brick 4 of leaf [E] is done** — four commits, each verified green before commit:
- `e451d1c` — `Lmat` (the 6×6 transport `1 ⊕ T ⊕ Sym²T`), `Lmat_apply` (its action),
  `M_paper_transport` (`M_paper(applyT T y) c = L_T (M_paper y c₀)`).
- `3248c55` — `surj_Lmat`: `surj((*v)(Lmat a b p q))` for `a·q−b·p ≠ 0`. Injectivity
  through the three blocks (component 1; T-block via `a·q−b·p≠0`; `Sym²T` block via
  `invertible_Smat_c` + explicit left inverse from `invertible_def`), then inj→surj in
  finite dim. NB `det_nz_iff_inj` is **real-only** (THM 0 on the complex matrix) — route
  inj→surj directly. Helpers `UNIV_3`, `sum_3`.
- `792058b` — `applyT_linear`, `applyT_surj` (invertible T ⟹ surj, explicit right inverse).
- `3312f2a` — `DM_paper_x_surj_transport` (4c): differentiate `M_paper_transport` both
  sides (chain rule via `diff_chain_at` + `has_derivative_M_paper_x` +
  `linear_imp_has_derivative`), `has_derivative_unique` gives
  `DM_paper_x(applyT T y₀) c ∘ applyT T = L_T ∘ DM_paper_x y₀ c₀`; RHS surjective
  (`surj_Lmat ∘ reg`), `applyT T` surjective ⟹ first factor surjective.

**Two traps cost the most time** (both now in memory): (1) bare `vec_eq_iff` resolves to
**Jordan_Normal_Form's** lemma (wrong type) — `unfolding`/`simp` no-ops silently; always
`Finite_Cartesian_Product.vec_eq_iff`. (2) `scaleR_vec_def` over-unfolds; use the
one-level `vector_scaleR_component` + `linear_cmul`.

**Fast offline-verify loop established.** Built the `Applied_Math_Appendix` heap (part 1).
Scratch theory `imports "Applied_Math_Appendix.Nonemptiness_Robust"` (session-qualified →
loads part 1 from heap in seconds; bare import reprocesses from source = 5–10 min). Re-state
or `sorry` part-2 deps in the scratch; eval_at runs ~2 min. This replaced the 10-min
Robust2-reprocessing loop. (Can't heap Robust2 — two sessions can't share the Appendix dir,
and it's the active file.)

**Brick 5 plan (next).** Lift `DM_paper_x_regular_point_c0` (`∃x₀::(real^2)^6.
surj(DM_paper_x x₀ c₀)`, dim-6, via `m_star`/`DM_paper_open_dense_surjective`) to
`CARD('n)≥6`. Structure is favourable: every `DM_paper_x` component is `∑_{n} f(c, x$n, h$n)`
(`A_moment=∑_n phase`, `d_A_moment_x=∑_n d_phase`, …) with each term depending only on
`x$n`/`h$n`. Embed via an injection `ι:6↪'n`: `y₀$(ι k)=x₀$k`, arbitrary elsewhere; for `h`
supported on `range ι` the off-range terms vanish (linear in `h$n`, and `h$j=0`), so
`DM_paper_x y₀ c₀ (h) = DM_paper_x x₀ c₀ (h∘ι)` ⟹ surjective. Then [E] =
`DM_paper_x_surj_transport` ∘ (brick 5 at c₀) ∘ `steering_transport_exists`. Note
`DM_paper_x_open_dense_surjective_gen` [F] is the general open-dense version (separate sorry).

**Brick-5 groundwork (verified in scratch, not yet committed):** the injection `ι:6↪'n` is
`card_le_inj[OF finite_class.finite_UNIV finite_class.finite_UNIV c]` with
`c: card(UNIV::6) ≤ card(UNIV::'n)` (`card_le_inj` needs **3** premises — both `finite` +
the `card ≤`; works because `'n` is finite from `(real^2)^'n`; in an isolated lemma `'n`
lacks the `finite` sort and it fails). Reindex core helper (last `simp`-on-`sum.reindex`
step **looped** — apply `sum.reindex` as `rule`/`subst`, not blanket `simp`):
`sum_reindex_embed: ⟦inj ι; ⋀n. n∉range ι ⟹ g n = 0⟧ ⟹ (∑n::'n. g n) = (∑k::6. g(ι k))`
via `sum.mono_neutral_right[OF finite_UNIV subset_UNIV]` + `sum.reindex`. Remaining: build
`y₀$(ι k)=x₀$k` (0 elsewhere), `h$(ι k)=h₀$k` (0 elsewhere); apply the helper to each of the
6 `d_*_moment_x` sums (off-range terms vanish: `d_phase`/weights are linear in `h$n`,
`h$j=0`; on-range `phase c₀ y₀ (ι k)=phase c₀ x₀ k`, `d_phase` likewise, `(y₀$(ι k))$i=(x₀$k)$i`);
assemble `DM_paper_x y₀ c₀ h = DM_paper_x x₀ c₀ h₀`; then for any `z`, pick `h₀` with
`DM_paper_x x₀ c₀ h₀ = z` (dim-6 surj) ⟹ `DM_paper_x y₀ c₀ (embed h₀) = z` ⟹ surj.

## 2026-06-05 — Split Robust at M12 (committed 568d636); fixed M12 parse hang; into brick 4

**Split committed.** `Nonemptiness_Robust` cut at `M12_moment_applyT` into part 1
(through `M22_moment_applyT`, ends with `end`) + new `Nonemptiness_Robust2`
(`imports Nonemptiness_Robust`; M12 onward through `F0_dip_nonempty`). Part 2 is the
active file. Heaping part 1 was tried and **reverted** (a12ba00 split → 2421b82
revert → 568d636 re-split) — the user keeps jEdit open, so edit Robust2 with
`-l Applied_Math_Nonemptiness` (jEdit reprocesses part 1 in-session). `parametric_…`
kept (the 1 sorry in part 1); 7 leaves in part 2.

**M12_moment_applyT parse hang FIXED.** Its `key` statement carried ~24 `$` (vec_nth)
on `real^2^2` → elaboration hung at PARSE (purple forever), *before any proof*. Fix:
`define t11..t22` for the four entries (drops to ~6 `$`), then mirror the proven
`M22` `sum_key` proof. **GOTCHA:** `define` folds the goal but NOT `?thesis` (stays
in `T$i$j`), so the final step needs
`using sum_key[unfolded t11_def t12_def t21_def t22_def]` to reconcile t↔T, then
`by (simp add: sum_distrib_left algebra_simps power2_eq_square ac_simps)`. Drop
`of_real_add`/`of_real_mult`/`mult.assoc` — already default simp ("duplicate" warnings).
See [[dollar-notation-slow-parse-use-vec-nth]].

**Build hygiene** ([[isabelle-build-process-hygiene]]): don't batch-build Appendix to
"verify" during interactive work; one build at a time (heap lock); `timeout -s KILL`
(poly ignores SIGTERM → zombies); `pkill -9 -x poly` (NOT `-f`); leaf heap needs `-b`.

NEXT — brick 4 in Robust2: `M_paper_applyT` (assemble the six `*_moment_applyT` laws
into the vector law `M_paper(applyT T y) c = L_T (M_paper y c0)`) → `L_T` invertible
(`det₃(Sym²T) = (det₂T)³ ≠ 0`) → chain rule
`DM_paper_x(applyT T y0,c) ∘ applyT T = L_T ∘ DM_paper_x(y0,c0)` → close
`DM_paper_x_regular_point_exists` (+ brick 5: dim-6→N embedding). See [[e-steering-transport-plan]].

## 2026-06-04 — A5 + A4 + `open_surj_blinfun` closed; leaf [E] steering-transport opened

Big multi-leaf push. Three on-path obligations and one reusable abstract foundation
landed green (all built `BUILD_EXIT=0`, committed + pushed), and leaf **[E]
`DM_paper_x_regular_point_exists`** is now under active construction.

GREEN + COMMITTED this session:
 - **A5 `gradU_dip_joint_C1`** (d3cd568) — the joint-`(x,ω)` C¹ field. Brick 4
   assembled it via `has_derivative_partialsI` (fx=`has_derivative_gradU_dip_x_explicit`,
   fy=`gradU_dip_has_derivative`=HessU·, fy_cont=`continuous_on_HessU_blinfun_joint`),
   `G' z = Blinfun(λ(tx,ty). Dx tx + HessU *v ty)`, `continuous_on UNIV G'` by
   `continuous_on_blinfun_componentwise` splitting the PRODUCT basis ((b,0)→brick 3,
   (0,e)→brick 2). See [[a5-route2-joint-c1-plan]] for the full 4-brick chain.
 - **`open_surj_blinfun`** (9177800) — reusable: `{A::'a⇒⇩L'b. surj(blinfun_apply A)}`
   is OPEN, via `surj A ⟺ inj(adjoint A) ⟺ adjoint A bounded-below`, perturbation `<B`.
   ALL deterministic (no smt/argo). Supports: `norm_adjoint_blinfun_le` (Cauchy–Schwarz,
   uses the NO-abs `norm_cauchy_schwarz`), `adjoint_blinfun_diff`.
 - **A4 `open_A_cart_nonzero`** (d78e5e0) — the regularity locus is open; three-way
   intersection: o1 (`A_cart≠0` via `A_cart_eq_Afun`+`open_Collect_neq`), o2 (`surj(DM)`
   via `open_surj_blinfun`+`continuous_open_vimage`), o3 (`det(matrix Dcvec_dip)≠0`
   via `det_2`). Plumbing 426ca00/b831a5a/2c2871b.
 - **[E] brick 1** (426ca00) — `DM_paper_x_regular_point_c0` (∃ regular point at
   `c0_paper`, dim 6) + `DM_paper_x_eq_MM` (the TWO `DM_paper_x` constants —
   `Nonemptiness_Paper.*` vs `Moment_Map.*` — are both THE Fréchet derivative of
   `M_paper`, identified by `has_derivative_unique`). `DM_paper_open_dense_surjective`
   gives the regular point on a dense set at `c0_paper`.
 - **[E] brick 2** `steering_transport_exists` (2f3c108) — for `c≠0` there is an
   invertible `T::real^2^2` with `Tᵀ c = c0_paper`. Built `N = (1/(c·c))·[[c₁,c₂],[−c₂,c₁]]`,
   `N *v c = c0_paper` (per-component `consider "i=1"|"i=2"` + `sum_2`), `det N = 1/(c·c)≠0`,
   `T = transpose N`. KEY FIX: `sum_2` (`Cartesian_Space:635`, `sum f (UNIV::2 set)=f 1+f 2`)
   IS real and necessary — without it `matrix_vector_mult_def` leaves the sum unexpanded;
   and the per-component `if i=1` only collapses after a literal case split (a monolithic
   `(χ i. …)=vector[1,0]` simp does NOT discharge it — that was the line-4536 failure).

ARGO TRAP (cost ~1h): `by argo` on a NONLINEAR goal (products of norms) HUNG the whole
`Applied_Math_Appendix` build for 1:00:18 (BUILD_EXIT=142) — argo is linear-only and does
not self-timeout. Now: NEVER argo/smt on products/powers of variables; CAP every build
`timeout 595 … -o timeout=300`. Recorded in [[argo-smt-nonlinear-hang-and-build-timeout]].

WORKING TREE (uncommitted, UNVERIFIED — last green tip is 2f3c108):
 - an alternative `Nc` proof (case-split + `metis add_divide_distrib … divide_self_if`);
   functionally equivalent to the committed one, not yet re-built.
 - **[E] brick 3 foundations**: `applyT T y = (χ n. T *v (y$n))`; `inner_transpose_mv`
   ((Tᵀc)·v = c·(T*v v) via `dot_lmul_matrix`); `phase_applyT` / `A_moment_applyT`
   (the phase, hence `A_moment`, is steering-invariant under `xₙ ↦ T yₙ` when `Tᵀc=c0`).
   These compile in isolation but the session ended before a full `BUILD_EXIT=0`.

NEXT (resume here): build-verify the working tree; if green, commit brick 3 foundations,
then the brick-3 MOMENT LAW proper — `M1/M2` linear in `T`, `M11/M12/M22` quadratic
(Sym²T), giving `M_paper(applyT T y, c) = L_T *v M_paper(y, c0)` with `det L_T = det(T)⁴≠0`
so surjectivity transports. Then brick 4 (Jacobian/surj transport) + brick 5 (dim-6→N
embedding) close [E]. After [E]: [F] density (`DM_paper_x_open_dense_surjective_gen`),
then engine core [C], strata [G–J], and the independent geometric leaf [K]
`no_degenerate_to_sphere_annulus`. See [[dipole-endtoend-obligation-list]].

## 2026-06-03 — engine #1 + A5 scoping (use the `Ck_on` C^k predicate, not weak diff)

\<^bold>Engine #1\<^esub> (`regular_zero_set_projection_charts_core_2d`): its supports are ALL PROVEN —
`regular_zero_set_projection_local_chart_2d` (IFT), `countable_chart_cover_of_levelset_2d`
(Lindelöf), `negligible_critical_values_from_charts` (`baby_Sard`).  Two facts about the core:
(1) its statement is UNDERSPECIFIED — it only assumes `reg0`, but `countable_chart_cover` needs
`derG`+`contG'` (a global C¹ field), supplied by A5; so the C¹ hyps must be ADDED to the core.
(2) the remaining math is the bad⟺critical IFT identification (`fst∘φ` critical ⟺ `∂_ω G`
non-surjective; tangent `= ker G' = Im Dφ`) + σ-compactness + chain-rule Jacobian — the deepest leaf.

\<^bold>A5\<^esub> `gradU_dip_joint_C1` reduces cleanly to `Ck_on 1 (λp. gradU (cvec_dip ω0 ωs) gain_dip (fst p)
(snd p)) UNIV` via `Ck1_on_imp_C1_interface` (Ck1_C1_Bridge.thy); `Ck_on = higher_differentiable_on`
(`Ck_on_iff_higher_differentiable_on`), combinators `Ck_on_add/mult/scaleR/compose/pow`.  GAP: only
single-variable smoothness exists (`U_dip_Ck2` = C² in ω; `C1_M_paper_x` = C¹ in x); NO joint `(x,ω)`
smoothness of `M_paper`/`U`/`gradU` — A5 needs it built (M_paper jointly C^∞, then compose).  \<^bold>Always
use `Ck_on`/`higher_differentiable_on` (true C^k), never `k_times_Fr_differentiable_on` (no continuity).\<^esub>

\<^bold>Conclusion:\<^esub> the engine branch (A5 joint-smoothness → engine IFT identification) is a multi-session
effort.  #6 `rank_lower_semicont_open_dense_propagation` (genericity branch, independent) is the likely
faster guaranteed win.

## 2026-06-03 — leaf #7 `steering_singular_nowhere_dense` PROVEN (11 on-path sorries left)

Assembled from `Dcvec_det_eq` + `sin_cos_lin_not_const0` (brick 2b): set rewritten to `{ω. f ω = 0}`
(f continuous ⟹ closed via `closed_Collect_eq`); a ball inside it restricted to the horizontal
segment `ω₂=c₂` gives `sin s·(cos s - sin s·g(c₂))≡0` on an interval, contradicting 2a.
`dist(vector[s,c₂]) c = ¦s-c₁¦` via `vector[s,c₂]-c = axis 1 (s-c₁)` +
`norm_eq_sqrt_inner`/`inner_axis_axis`/`real_sqrt_abs2`.
\<^bold>Remaining on-path (11):\<^esub> #1 engine Sard-covering, #2 `DM_paper_x_open_dense_surjective_gen`,
#3 `DM_paper_x_regular_point_exists`, #4 A5 `gradU_dip_joint_C1`, #5 A4 `open_A_cart_nonzero`,
#6 `rank_lower_semicont_open_dense_propagation`, #9 `parametric_transversality_meager_planar_config`,
#10 `no_degenerate_to_sphere_annulus`, #11 `meager_bad_regular_stratum`,
#12 `meager_rank_deficient_stratum`, #13 `meager_steering_singular_stratum` (needs #7+#9).
NOTE: #7 is an INPUT to #13, not a full unlock — the 4 `meager_*_stratum` wrappers all funnel
through the parametric bridge #9 → engine #1.  No more "quick analytic" leaves remain; the
self-contained ones are A5 (#4) and rank-semicont (#6); the universal bottleneck is engine #1.

## 2026-06-03 — bricks 1+2a of leaf #7 done (`Dcvec_det_eq`, `sin_cos_lin_not_const0`)

Brick 2a `sin_cos_lin_not_const0` PROVEN: `sin s·(cos s - sin s·M)` cannot vanish on any open
interval (F=F'=F''=0 there via `has_field_derivative_transform_within_open` — note the set arg is
named `S`, capital; then `X-MY=0 ∧ Y+MX=0 ⟹ X=Y=0` vs `X²+Y²=1`).  Leaf #7
`steering_singular_nowhere_dense` is now ONE assembly step away (brick 2b): rewrite the set via
`Dcvec_det_eq` to `{ω. f ω = 0}` (f continuous ⟹ closed); a ball in it restricts on the horizontal
segment `ω₂=c₂` to `sin s·(cos s - sin s·g(c₂))≡0` on an interval, contradicting 2a.  Then #7 unlocks
the wrapper #13 `meager_steering_singular_stratum`.

## 2026-06-03 — `Dcvec_det_eq` proven (brick 1 of leaf #7 `steering_singular_nowhere_dense`)

Explicit steering determinant: `det(matrix(Dcvec_dip ω0 ωs ω)) = sin ω₁·(cos ω₁ - sin ω₁·(Kₓ cos ω₂ +
K_y sin ω₂))`, `Kₓ=(kx ω0-kx ωs)/(kz ωs-kz ω0)`, `K_y` likewise.  Proof: a `have …` arithmetic
identity discharged by `argo` (the `Kₓ`-numerator cancellation), then
`simp(det_2 matrix_def Dcvec_dip_def axis_def sin_cos_squared_add algebra_simps)`.  Brick 2 (the
`nowhere_dense` itself): `{det=0}` closed ⟹ nowhere_dense ⟺ interior={}; on a horizontal segment
`h(ω₁)=cos ω₁ - sin ω₁·g(b)` has `h²+h'²=1+g(b)²>0`, so it cannot vanish on an interval (and the
`sin ω₁=0` points are isolated) — contradiction with `{det=0}` containing a ball.

## 2026-06-03 — DEFINITIVE on-path sorry list for `F0_dip_nonempty` (13 leaves)

Verified by scanning ALL working `.thy` files (not just `Robust`).  \<^bold>Off-path (do NOT count):\<^esub>
`Nonemptiness_Inventory` (`thm_final`,`prop_*`,`lem_*` — standalone, not imported), `Nonemptiness_Capstone`
(`branch_*_meager`,`capstone_feasible`,`capstone_X0_sound` — the generic capstone superseded by the
dipole `F0_dip_nonempty`; imported but never referenced by the F0 chain), the `oops` in
`Higher_Differentiability.thy` (inert note).  The whole moment-map machinery
(`BlockDet`/`MomentJac`/`Moment_Map`) is sorry-FREE.  The architecture above the leaves
(`F0_dip_nonempty`→`regular_feasible_witness_dip`→`regular_feasible_point_dip`→`Phi_bad_meager_dip`)
is machine-checked.

\<^bold>The 13 on-path leaves, by tier:\<^esub>
- \<^bold>Tier A (long poles, days):\<^esub>
  1. `regular_zero_set_projection_charts_core_2d` (engine, `Parametric_Transversality_Euclidean_Base.thy` L352) — the chart COVERING only (NOT Sard).  \<^bold>Sard is already discharged:\<^esub>
     Isabelle ships `baby_Sard`, and `negligible_critical_values_from_charts` (engine L285) is PROVEN
     with it.  Searched all 5 Munkres files — NO Sard/negligible/critical/measure (only Baire + a custom
     `top1_m_manifold_on` type).  So this sorry = "regular value 0 \<Rightarrow> (IFT) level set is a local graph
     \<Rightarrow> bad params \<subseteq> critical-value images (rank-deficient projection), \<sigma>-compact charts"; tool is
     HOL-Analysis `implicit_function_theorem` over Euclidean `real^'m`, then `negligible_...` finishes.
  2. `DM_paper_x_open_dense_surjective_gen` (Robust 3682) — rank-12 submersion open-dense, generalised from `c0_paper=(1,0),CARD=6` to steered `cvec_dip`, `CARD≥6`.
  3. `DM_paper_x_regular_point_exists` (Robust 3671) — a submersion point exists (same generalisation).
- \<^bold>Tier B (hours):\<^esub>
  4. `gradU_dip_joint_C1` (A5, Robust 3296) — joint C¹ blinfun derivative field (self-contained).
  5. `open_A_cart_nonzero` (A4, Robust 3285) — regularity locus open (needs #6).
  6. `rank_lower_semicont_open_dense_propagation` (`Nonemptiness_Paper.thy`) — rank lower-semicont + density.
  7. `steering_singular_nowhere_dense` (Robust 3692) — `{det Dcvec = 0}` nowhere dense.
  8. `meager_Azero_degenerate_stratum` (Robust 3745) — `A=0` stratum meager.
  9. `parametric_transversality_meager_planar_config` (Robust 3641) — bridge to the engine.
  10. `no_degenerate_to_sphere_annulus` (Robust 4106) — spine glue for `regular_feasible_point_dip`.
- \<^bold>Tier C (quick wrappers, once inputs land):\<^esub>
  11. `meager_bad_regular_stratum` (Robust 3702) — = A6 + #9.
  12. `meager_rank_deficient_stratum` (Robust 3717) — = #2/#6.
  13. `meager_steering_singular_stratum` (Robust 3730) — = #7.

When all 13 are proven sorry-free \<^bold>with sound (non-vacuous) statements\<^esub>, `F0_dip_nonempty` is the
unqualified end-to-end proof (only hypothesis `c6`).  No other leaves exist.

## 2026-06-03 (robust set) — (A3) `gradU_dip_x_partial_surj` PROVEN (the determinant payoff)

The deepest analytic leaf is closed: the configuration-derivative of \<open>\<nabla>\<^sub>\<Omega>U_dip\<close> is onto \<open>\<real>\<^sup>2\<close>
when \<open>A \<noteq> 0\<close>, \<open>surj(DM_paper_x)\<close>, and the steering Jacobian is nonsingular.  Built bottom-up:
- (i) `surj_Im_cnj_mult`, (ii) `surj_moment_grad_map` (Cramer + analytic core) — done earlier.
- `has_derivative_Ej_moment` + named `Ejm`/`dEjm` + `has_derivative_Ejm`: explicit moment-space
  Fréchet derivative of a gradient component (idiom `rule has_derivative_eq_rhs` is the WRONG
  lever once `?f'` is a bare schematic; use `derivative_eq_intros` on the original goal).
- `has_derivative_gradU_dip_component_x` (step 2): chain via `has_derivative_M_paper_x` +
  `diff_chain_at` + `gradU_dip_component_moments`/`cmod_power2` (don't pre-instantiate `dEjm`'s
  schematics — let `diff_chain_at` fix `?M0` and `simp o_def` do the rest).
- `has_derivative_gradU_dip_x_explicit` (step 3): assemble the 2 components via
  `has_derivative_componentwise_within` + `Basis_vec_def` + `inner_axis` (mirrors
  `gradU_dip_differentiable_x`).
- `dEjm_on_e` + the surj assembly (step 4): on \<open>\<delta>=(0,d\<^sub>2,d\<^sub>3,0,0,0)\<close> the \<open>\<bar>M\<^sub>1\<bar>\<^sup>2\<close> term drops, leaving
  the `Im`-form (`Re((-\<ii>)w)=Im w`); `Dx = dE \<circ> DM`, `surj Dx \<longleftrightarrow> surj dE` by `comp_surj`+`Msurj`,
  `surj dE` by `surj_moment_grad_map`.  Traps: `a0` via `metis M_paper_proj_A` (simp over-unfolds
  to `A_moment`); `detC` via `det_2`+`matrix_def`+`argo` (commuted product); the vector equality
  `t = dE e` must be assembled componentwise (`c1`,`c2`) then `metis exhaust_2 vec_eq_iff` — a
  single combined `simp` won't fire `vec_eq_iff` on `t = (\<chi> j. \<dots>)`.

\<^bold>Remaining on the A-chain:\<^esub> (A4) `open_A_cart_nonzero`, (A5) `gradU_dip_joint_C1`, then (A6) the
regular-value lemma (consumes A3+A4+A5) \<rightarrow> transversality engine \<rightarrow> regular stratum of
`Phi_bad_meager_dip` \<rightarrow> `regular_feasible_point_dip` \<rightarrow> capstone.

## 2026-06-03 (robust set) — Capstone `F0_dip_nonempty` discharged to ONLY `c6` (feasibility removed)

\<^bold>User catch:\<^esub> the final theorem may assume only the dimension restriction `c6` (`6 ≤ CARD('n)`);
the `feasible: interior(Ffeas …) ≠ {}` precondition is not allowed.  Resolved by \<^emph>\<open>construction\<close>,
not by hypothesis or by existential hand-waving:

- \<^bold>Key physics:\<^esub> `af_at_main`/`Upow_at_main` --- `cvec_dip ω0 ωs ω0 = 0` at the main beam, so
  `Upow(x,ω0) = gain·N² = cap` for \<^emph>\<open>every\<close>\<close> config (given `kz ωs ≠ kz ω0`).  The upper power bound
  `Upow ≤ cap` is thus a theorem (vacuous constraint) and `ball_inside_Ffeas` only needs the strict
  \<^emph>\<open>lower\<close>\<close> bound `pmin < Upow ω0`.  (The spurious `Upow ctr < cap` in `Ffeas_interior_nonempty` is
  unused; with `ctr=ω0` it is even false `cap<cap` --- left it, it is standalone/uncited.)
- \<^bold>Construction:\<^esub> concrete angles `ω0=(π/2,0)`, `ωs=(0,0)`, `ωnull=(π,0)`, `ctr=ω0` give
  `kz ωs=1≠0=kz ω0` and `cvec_dip ω0 ωs ωnull $ 1 = -2 ≠ 0`; `feasible_witness_exists` builds the
  Slater witness `x` (nulls at `ωnull`, spacing `≥1`); pick `dmin=1/2, δnull=1, pmin=0, A=B=0,D=1,
  R=‖x‖+1`.  Then `ball_inside_Ffeas` ⟹ `interior(Ffeas) ≠ {}`, fed to
  `regular_feasible_witness_dip`+`F0_nonempty_of_witness`.
- \<^bold>Statement now:\<^esub> `6 ≤ CARD('n) ⟹ ∃ A B D ω0 ωs ωnull ctr R dmin δnull pmin ξ κ ε. 0<ξ∧0<κ∧0<ε
  ∧ F0 (cvec_dip ω0 ωs) gain_dip R dmin A B D ωnull ctr (Omega ctr) δnull pmin ξ κ ε ≠ {}`.
  The design is delivered by the construction; only `c6` is assumed.  `gain_dip ω0 > 0` from
  `gain_dip_nonzero_of_sin` (sin(π/2)=1≠0).  Build clean (BUILD_EXIT=0).

## 2026-06-02 (robust set) — Into the determinant payoff: gain-from-steer + surj F pieces (i),(ii)

\<^bold>Key correction (user):\<^esub> use the ACTUAL gain.  `gain_dip ω = gdip(ω\<^sub>1) = (edip ω\<^sub>1)\<^sup>2`, and
`gsinc x = (if x=0 then 1 else sin x/x)` gives `gdip θ = 0 \<longleftrightarrow> cos θ = ±1 \<longleftrightarrow> sin θ = 0`.  Since
`det(matrix(Dcvec_dip …))` carries a `sin(ω\<^sub>1)` factor (its ω-column is `(-sinω\<^sub>1 sinω\<^sub>2, sinω\<^sub>1 cosω\<^sub>2)`),
the steering hypothesis `det ≠ 0 \<Longrightarrow> sin ω\<^sub>1 ≠ 0 \<Longrightarrow> gain_dip ω ≠ 0`.  So \<^bold>no gain hypothesis / gain=0
stratum is needed\<^esub> (my earlier "soundness cascade" alarm was wrong).  Proved `gain_dip_nonzero_of_sin`.

\<^bold>surj F\<^esub> (the rank core of `gradU_dip_x_partial_surj`) factors into three pieces; (i),(ii) done:
- (i) `surj_Im_cnj_mult`: `w \<mapsto> Im(cnj a · w)` onto \<real> for `a ≠ 0` (right inverse `i·s/cnj a`).
- (ii) `surj_moment_grad_map`: `(d\<^sub>2,d\<^sub>3) \<mapsto> (2g·Im(cnj a·(c\<^sub>j\<^sub>1 d\<^sub>2 + c\<^sub>j\<^sub>2 d\<^sub>3)))\<^sub>j` onto \<real>\<^sup>2 when `a≠0, g≠0,
  det C ≠ 0` — Cramer's rule + (i).  (Trap: `simp only` for the final assembly, else `Im_mult`
  expansion blocks `iw1/iw2`; `metis of_real_eq_0_iff` for `Dnz`.)
- (ii.5) `Dcvec_det_zero_of_sin`: `sin(ω\<^sub>1)=0 \<Longrightarrow> det(matrix(Dcvec_dip …)) = 0` — Dcvec kills
  `axis 2 1` (ω-column = 0), so non-injective, `det = 0` via `det_nz_iff_inj` on the
  `has_derivative_cvec_dip` linearity.  With the gain bridge gives `steer \<Longrightarrow> gain_dip ω \<noteq> 0`.  DONE.
- (iii) REMAINING (the bulk): the explicit `DΦ`-on-`(M\<^sub>2,M\<^sub>3)` derivative = the (ii) map, then
  `surj(F∘DM) \<longleftrightarrow> surj F` via `Msurj`, assembling `gradU_dip_x_partial_surj`.  Needs an explicit
  has_derivative computation of the `E_j` moment expressions (product/Re/cnj rules).  The directional/
  affine shortcut (`E_j(M0+s·δ) = E_j(M0) + s·m_j` for `δ\<^sub>1=0`, slope `m_j` = the (ii) map) is circular
  via `has_derivative_gradU_dip_x` (which hides `F`); the explicit component derivative is irreducible.
  Connecting facts still needed inline: `A_cart = M_paper$1` (for `a≠0`) and
  `det(matrix Dcvec) = c11 c22 - c12 c21` (`det_2`+`matrix_def`, matching the (ii) `detC` indexing).

## 2026-06-02 (robust set) — `has_derivative_gradU_dip_x` closed (chain rule); audit 14 → 13

Proved `has_derivative_gradU_dip_x`: the configuration-derivative of \<open>\<nabla>\<^sub>\<Omega>U_dip\<close> factors through
`DM_paper_x` (define the moment-gradient map \<open>\<Phi>\<close> from `gradU_dip_component_moments`, prove \<open>\<Phi>\<close>
differentiable at the moment point componentwise, then `diff_chain_within` with the proven
`has_derivative_M_paper_x`).  This is the A2 input to the determinant-payoff rank lemma
`gradU_dip_x_partial_surj`, which is now unblocked (it has its explicit \<open>D\<^sub>\<bm>x\<close>).  Traps: use the
\<^bold>qualified\<^esub> `Finite_Cartesian_Product.vec_eq_iff` (unqualified resolves elsewhere); `diff_chain_within`
yields \<open>f \<circ> g\<close>, convert to the \<open>\<lambda>\<close>-form with `o_def`; prove componentwise with `rule
gradU_dip_component_moments` (no `simp`, which over-expands `M_paper`).  Audit now \<open>13\<close> (12 Robust + engine).

## 2026-06-02 (robust set) — Leaf-closing loop with self-audit; deep frontier reached

Discipline this loop: \<^bold>never introduce a new `sorry`\<^esub>; every step is a net \<open>-1\<close> (full closure or a
reduction to already-existing leaves). Audit of total on-path `sorry`s (Robust + engine core):
\<open>17 \<rightarrow> 16\<close> (deleted dead generic `Phi_bad_meager`) \<open>\<rightarrow> 15\<close> (`meager_linear_homeo_iff`, with the
proven helpers `nowhere_dense_homeo_image`/`meager_homeo_image`) \<open>\<rightarrow> 14\<close> (`Ffeas_interior_nonempty`
via the existing `ball_inside_Ffeas`). Earlier this session: `sigma_min_pos_iff_invertible`,
`regular_value_on_via_x_partial` (A1), `regular_value_on_gradU_dip` (A6 reduction).

\<^bold>All bounded leaves are now closed.\<^esub> The remaining \<open>14\<close> are the deep mathematical cores:
- determinant payoff: `gradU_dip_x_partial_surj` (rank), `has_derivative_gradU_dip_x` (chain rule
  through `M_paper`; needs the explicit moment-gradient map \<open>\<Phi>\<close>), `open_A_cart_nonzero` (rank LSC),
  `gradU_dip_joint_C1` (no joint-smoothness infra exists — `U_dip_higher_differentiable_on` is in \<open>\<omega>\<close>
  only);
- moment submersion at the steered wavevector: `DM_paper_x_regular_point_exists`,
  `DM_paper_x_open_dense_surjective_gen` (the `m_star` machinery is `c0_paper`-only);
- strata meagerness (need the engine): `meager_{bad_regular,rank_deficient,steering_singular,Azero}_stratum`;
- engine core `regular_zero_set_projection_charts_core_2d`;
- `steering_singular_nowhere_dense` (analytic zero set), `no_degenerate_to_sphere_annulus` (annulus
  half now trivial via `sigma_min_pos_iff_invertible`; sphere half needs IFT isolation),
  `parametric_transversality_meager_planar_config` (reshape \<open>(\<real>\<^sup>2)^'n \<cong> \<real>\<^sup>m\<close>, type-cardinality matching).

\<^bold>Traps logged\<^esub>: `auto simp: homeomorphism_def` hangs (use projection lemmas `homeomorphism_cont1`/
`apply1`/`apply2`); pin `obtain E :: "nat \<Rightarrow> _ set"` when destructuring `meager_def`.

---

## 2026-06-02 (robust set) — Closing leaf lemmas: spectral, A1, A6

Began discharging the leaf `sorry`s (deepest-first where tractable). Closed this session:
- `sigma_min_pos_iff_invertible` (`0 < sigma_min H ⟷ det H ≠ 0`): smallest singular value over the
  compact unit sphere is attained, so positive ⟺ `H*v ≠ 0` on the sphere ⟺ injective (normalise a
  kernel vector) ⟺ `det ≠ 0` (`det_nz_iff_inj`).
- `regular_value_on_via_x_partial` (A1): regular value from config-partial surjectivity, via the
  proven `surj_partial_imp_surj_joint` + `joint_deriv_restricts_to_partial` (the earlier 21-min hang
  was a fluke — it builds in ~2 min). Care: derive `at (x,w) within S = at (x,w)` for the
  destructured point and `unfolding pxw atxw`, not `simp add: atp pxw` (rewrite-order trap).
- `regular_value_on_gradU_dip` (A6): now a verified reduction to {`open_A_cart_nonzero`,
  `gradU_dip_x_partial_surj`, `gradU_dip_joint_C1`}. Trap: `via_x_partial`'s `(λy. G(y,w))` becomes
  `(λy. gradU … (fst (y,w)) (snd (y,w)))` — equal to the β-clean `gradU … y w` only by `fst_conv`,
  NOT αβη; so `show` must use the `fst/snd` form and bridge with `simp`.

Leaf `sorry`s remaining (16; one is the off-path generic `Phi_bad_meager`): the determinant-payoff
rank lemma `gradU_dip_x_partial_surj`, the 4 strata, the two `DM_paper_x_…_gen` submersion lemmas,
`steering_singular_nowhere_dense`, `no_degenerate_to_sphere_annulus`, `has_derivative_gradU_dip_x`,
`gradU_dip_joint_C1`, `open_A_cart_nonzero` (needs rank lower-semicontinuity), `Ffeas_interior_nonempty`,
`meager_linear_homeo_iff`, `parametric_transversality_meager_planar_config`, and the engine core.

\<^bold>Practice (user):\<^esub> on any inexplicable "Failed to apply", turn on `[[show_types]]` immediately
(it found the decoupled-type-var bug); pin polymorphic `'n` in new statements up front.

---

## 2026-06-02 (robust set) — Soundness audit + the entire Baire/meager GLUE now machine-verified

Audited the dipole capstone chain for soundness and made it compose. Three statement-level bugs fixed,
then the reduction glue was proven (only leaf lemmas remain `sorry`).

\<^bold>Statement-soundness fixes:\<^esub>
- \<^bold>Feasibility:\<^esub> `F0_dip_nonempty` was \<^emph>false as stated\<^esub> (for `pmin > gain_dip ctr * N²`,
  `Ffeas = {}`). Added explicit `interior (Ffeas …) ≠ {}` hypothesis, threaded through
  `regular_feasible_witness_dip` and `regular_feasible_point_dip`.
- \<^bold>A=0 stratum:\<^esub> array nulls are critical points, so `Phi_bad_meager_dip` is now the FULL bad set
  `{∃ω. Φ=0}` with a 4th stratum `meager_Azero_degenerate_stratum`; `regular_config_exists` now
  concludes "no degenerate critical at ANY ω".
- \<^bold>surj(DM) in A6, C¹ in the engine lemma.\<^esub>

\<^bold>The decoupled-type-variable bug (the witness-intro mystery):\<^esub> every witness tactic
(`rule exI`, `rule_tac x=x0 in exI`, `metis`, `bexI[where x=x0]`, even fully-explicit
`exI[where P=… and x=x0]`) \<^emph>failed to apply\<^esub> to `regular_config_exists`'s `∃x0∈interior(…). …`.
`declare [[show_types]]` revealed why: the witness `x0 :: …^'n` (lemma's var) but the goal's bound
`∃x0 :: …^'a` (a \<^emph>fresh\<^esub> var) — Ffeas/Phibad are dimension-polymorphic and nothing in the `shows`
tied them to `'n`. Fix: annotate the conclusion `interior (Ffeas … :: ((real^2)^'n) set)`.

\<^bold>Result:\<^esub> `regular_config_exists`, `regular_feasible_point_dip`, and `Phi_bad_meager_dip` are now
\<^bold>fully proven\<^esub>. The whole reduction glue
`F0_dip_nonempty ← regular_feasible_witness_dip ← regular_feasible_point_dip ←
{regular_config_exists, no_degenerate_to_sphere_annulus} ← Phi_bad_meager_dip ← 4 strata`
is machine-verified (BUILD_EXIT=0). Only the LEAF lemmas remain `sorry` (the deep ones:
`gradU_dip_x_partial_surj`, the 4 strata, the two `DM_paper_x_…_gen` submersion lemmas, the engine
core; plus moderate ones). The generic `Phi_bad_meager` is unprovable/superseded and off-path.

---

## 2026-06-02 (robust set) — DEFINITIVE remaining-obligation list; A6 corrected; 3-stratum scaffold

Traced the full proof tree of `F0_dip_nonempty` to bedrock. Corrected an earlier under-count:
finishing the dipole capstone unqualified needs **22 obligations**, not 12. Key structural facts:

- The spine is proven: `F0_nonempty_of_witness` (full), `regular_feasible_witness_dip`, the two
  Weierstrass continuity lemmas. The ONLY spine sorry is `regular_feasible_point_dip`.
- **A6 was wrong**: `regular_value_on_gradU_dip` claimed the regular value on `{A≠0 ∧ det(Dcvec)≠0}`,
  but `gradU_dip_x_partial_surj` also needs `surj(DM_paper_x …)` (the open-dense rank-12 / `m_star≠0`
  condition), which `A≠0` does NOT imply. Fixed A6 and `open_A_cart_nonzero` to carry that conjunct.
- Because the regular value only holds where the moment map is a submersion AND the steering map is
  an immersion, `Phi_bad_meager_dip` needs a **3-stratum decomposition** (regular / rank-deficient
  `¬surj DM` / steering-singular `det Dcvec=0`) — mirroring the paper's `prop:dimZ`/`prop_regnonzero`
  (whose strata meagerness are themselves the deep, still-open branch results).
- The `m_star`/`surj_iff_m_star` submersion machinery is proven ONLY at `c0_paper=(1,0)`, `CARD=6`
  (`MomentJac/Moment_Jacobian.thy`). The steered wavevector `cvec_dip ω` and general `CARD≥6` need
  generalising — new lemmas `DM_paper_x_regular_point_exists`, `DM_paper_x_open_dense_surjective_gen`
  (the latter via the still-open Paper sorry `rank_lower_semicont_open_dense_propagation`).
- Engine: `Parametric_Transversality_Euclidean_Base` has exactly ONE sorry, the core
  `regular_zero_set_projection_charts_core_2d`; everything else (local IFT chart, countable cover,
  `meager_critical_values_from_charts`, σ-compact exhaustion, `rank_deficient_C1_image_meager`) is
  proven. Caveat: the core's statement likely needs a C¹ hypothesis added to be provable (then
  `gradU_dip_joint_C1` supplies it). The generic `Phi_bad_meager` is unprovable/superseded by
  `Phi_bad_meager_dip`.

Added (statements only, typecheck-verified): A6/`open_A_cart_nonzero` fixes; `DM_paper_x_regular_point_exists`,
`DM_paper_x_open_dense_surjective_gen`, `steering_singular_nowhere_dense`, `meager_bad_regular_stratum`,
`meager_rank_deficient_stratum`, `meager_steering_singular_stratum`, `Phi_bad_meager_dip`. Plus the
earlier-this-session A1–A5, B1–B2, C0–C3 statements. Deepest 6: `gradU_dip_x_partial_surj`, M5, M6,
the two `DM_…_gen`, and the engine core.

---

## 2026-06-02 (robust set) — Phi_bad_meager reduction: bad set ⊆ engine critical-projection set

Pushed the dipole Sard step through its entire *structural* half — the dipole degenerate-critical
configuration set is now proven (sorry-free) to be contained in exactly the set whose meagerness the
transversality engine delivers. Bricks landed this session, in order:

- `gradU_dip_differentiable_x` — assemble the two scalar component bricks into the full 2-vector
  gradient field's differentiability in x, via `differentiable_componentwise_within` (basis `axis j 1`,
  `∙ b = $ j` by `inner_axis`).
- `surj_matrix_vector_iff_det` — for a square `A`, `surj ((*v) A) ⟷ det A ≠ 0` (surj ⟹ right-inverse
  `matrix_right_invertible_surjective` ⟹ two-sided `matrix_left_right_inverse1` ⟹ `invertible` ⟹ det≠0;
  converse via `invertible_det_nz` + `invertible_eq_bij`). Plus `det_2_symmetric`.
- `not_surj_omega_deriv_iff_detHess_dip` — for the C² dipole the engine's "no surjective ω-derivative
  of `gradU`" predicate is *literally* `det (HessU) = 0`: `gradU_dip_has_derivative` gives the unique
  derivative `(*v) HessU`, then `surj_matrix_vector_iff_det` + `has_derivative_unique`. (Care: convert
  `at ω within Ω` to `at ω` via `at_within_open` so `has_derivative_unique` applies.)
- `HessU_dip_symmetric` — Clairaut: `mixed_partials_commute` on the C² `U_dip` (`U_dip_Ck2`).
- `Phibad_dip_imp_detHess0` — `Φ = 0` ⟹ `gradU = 0 ∧ det (HessU) = 0`, rewriting Φ's slot
  `H₁₁H₂₂ − H₁₂²` into `det_2` form `H₁₁H₂₂ − H₁₂H₂₁` using symmetry.
- `Phibad_dip_subset_critical` — the capstone of the half: `{x∈V. ∃ω. Φ=0 ∧ A≠0} ⊆ {x∈V. ∃ω. gradU=0
  ∧ ¬(∃D surjective derivative at ω)}` (Ω=UNIV; the `A≠0` only shrinks the LHS so the inclusion is free).

Remaining for `Phi_bad_meager` (still two genuine pieces): (2) the transversality input
`regular_value_on gradU_dip (V×Ω) 0` — D_x gradU = (2×6 moment Jacobian)·`DM_paper_x` is onto ℝ²
on `{A≠0}` from the rank-12 `bigJ` (lem:Msurj); and the `(real^2)^'n ≅ real^(2·CARD('n))` reshape so the
engine's `real^'m`-typed `parametric_transversality_meager_euclidean_stub` applies. (3) The engine core
`regular_zero_set_projection_charts_core_2d` is itself still `sorry`.

---

## 2026-06-02 (robust set) — Sard step begun: configuration-space smoothness bricks

User chose (a) a dipole-specific `Phi_bad_meager_dip` obligation and (b) building the Sard step
(`prop:dimZ`) incrementally as verified bricks. Key framing insight: the 2d chart-projection engine
(`regular_zero_set_projection_charts_*`, `meager_critical_values_from_charts` in
`Parametric_Transversality_Euclidean_Base`) takes `G : (ℝ^m × ℝ²) → ℝ²` and its bad set is exactly
`{x: ∃ω. G(x,ω)=0 ∧ D_ω G not surjective}`.  Set **G = gradU_dip** (the ω-gradient, ℝ²-valued):
`G=0` ⟺ ω critical, `D_ω G = HessU` not surjective ⟺ `det HessU = 0`.  So `Phibad_dip = 0` IS the
critical-projection set of `gradU_dip` — Φ₃ needs no separate equation.

Sard brick (1) landed, sorry-free: `gradU_dip_component_differentiable_x` — for fixed ω, the j-th
gradient component is differentiable in x.  Proof: rewrite via `gradU_dip_component_moments` to a
fixed polynomial in the x-smooth moment coordinates `M_paper y (cvec_dip ω)` (`has_derivative_M_paper_x`
+ `bounded_linear_vec_nth`), `cmod² = Re²+Im²` (`cmod_power2`), then `differentiable_*` intro chain with
`differentiable_compose[OF bounded_linear_imp_differentiable[OF bounded_linear_{Re,Im,cnj}]]`.  No
ω-smoothness of cvec/gain assumed (the ω-jets enter as constants).

Remaining for `Phi_bad_meager_dip`: (1b) same smoothness for V, ∇_cV (then HessU entries / vector
form); (2) `regular_value_on gradU_dip 0` on the open `{A≠0}` region — D_x gradU = (2×6 moment Jac)·
`DM_paper_x`, surjective since any 6 rows of the rank-12 `bigJ` are independent ⟹ D_x(A,M₁,M₂) onto ℝ⁶,
and the 2×6 block has rank 2 when the steering Jacobian `Dcvec_dip` is nonsingular (A≠0 needed — at A=0
every config is critical, which is why the bad set carries `A≠0`); (3) the general engine
`regular_zero_set_projection_charts_core_2d` is itself still `sorry`, so a fully sorry-free
`Phi_bad_meager_dip` also needs that infrastructure discharged.

---

## 2026-06-02 (robust set) — Hessian entry in moment-space form (ω–c bridge, 2nd order, complete)

Closed the second-order half of the ω–c bridge: the actual dipole Hessian `HessU (cvec_dip ω0 ωs)
gain_dip x ω` now has every entry written as an *explicit moment-space expression*, with all
x-dependence funneled through `M_paper x c` (via `∇_cV`, `Hcmat`, `V`) and all geometry through
x-independent jets (`Dcvec_dip`, `D2cvec_dip`, `∂gdip`, `∂²gdip`). Two new sorry-free lemmas:
- `HessU_dip_eq_componentderiv`: `HessU … $ k $ l = frechet_derivative (λω. gradU … $ k) (at ω)
  (axis l 1)` — the Hessian is the gradient field's Jacobian, and `$h k` is bounded-linear so it
  commutes with `has_derivative` (`bounded_linear.has_derivative[OF bounded_linear_vec_nth
  gradU_dip_has_derivative]`); then `frechet_derivative_at'` + the matrix-vector component picks the
  `(k,l)` entry. (User fixed the `frechet_derivative_at'` orientation here.)
- `HessU_dip_entry_moments`: the `(k,l)` entry equals the explicit 5-term moment expression. Proved
  as three legible steps — (1) `HessU_dip_eq_componentderiv`; (2) `frechet_derivative_at'[OF
  has_derivative_gradU_dip_component]` names the total derivative as the `(λh. …)` moment map proved
  earlier; (3) `by (rule refl)` β-reduces the map at `e_l = axis l 1`, which is syntactically the
  claimed expression. (Earlier terse `simp`/`apply` attempts failed: the conditional
  `frechet_derivative_at` couldn't discharge its has_derivative premise inside `simp`; the fix is to
  pre-instantiate with `[OF …]` and `unfold`.)

Five-term anatomy (the genuine 2nd-order content): curvature `∇_c²V` pulled back through the chart
Jacobian twice (`Hcmat` term); chart bending `D²cvec_dip`; two gain×`∇_cV` cross terms; gain's
`∂²` times `V=|A|²`. Next brick: `det HessU_dip = poly(M_paper)` (Φ₃ via the bridge).

---

## 2026-06-01 (robust set) — Weierstrass continuity inputs for the capstone (actual dipole)

Toward discharging `regular_feasible_witness` *with the actual function* `cvec_dip`/`gain_dip`
(it is UNprovable as stated for arbitrary `cvec`/`g` — the usual abstract-placeholder trap),
proved the two analytic conjuncts the capstone needs as standalone, sorry-free facts:
- `gradU_dip_continuous_on` / `norm_gradU_dip_continuous_on`: the dipole gradient field is
  continuous in ω (differentiable *everywhere* by `gradU_dip_has_derivative`, so
  `has_derivative_continuous` + `continuous_at_imp_continuous_on`). This is the κ-margin input.
- `HessU_dip_continuous_on`: `U_dip` is C² everywhere (`U_dip_Ck2`), so its Hessian
  `∇²=HessU` is continuous (`Ck_2_imp_hessian_continuous`).
- `sigma_min` continuity (the ξ-margin input). σ_min is 4-Lipschitz: `sigma_min_diff_le`
  shows `σ_min H₁ − σ_min H₂ ≤ ‖(*v)(H₁−H₂)‖_op` (for each unit v, `‖H₁v‖ ≤ ‖H₂v‖ + ‖(H₁−H₂)v‖`
  via `norm_triangle_sub` + `matrix_vector_mult_diff_rdistrib`, then `cINF_lower`/`cINF_greatest`
  over the unit sphere); `onorm_mv_le4` bounds `‖(*v)M‖_op ≤ 4‖M‖` (via
  `onorm_le_matrix_component_sum`, `|M$i$j| ≤ ‖M‖`); combine ⟹ `lipschitz_onI 4` ⟹
  `lipschitz_on_continuous_on`. Then `sigma_min_HessU_dip_continuous_on` = σ_min ∘ HessU.

GOTCHAS: (i) `norm_nth_le` is OVERLOADED — the `inner`-product version
(`norm (x∙i) ≤ norm x`) shadows the cartesian one; qualify as
`Finite_Cartesian_Product.norm_nth_le` to get `norm (x$i) ≤ norm x`. (ii) After
`unfolding sigma_min_def` a hypothesis still mentioning `sigma_min H1` no longer matches
the now-unfolded goal — keep the INF↔σ_min rewrite local (rewrite only the H₂ side via a
nested `have … by (simp add: sigma_min_def)`).

Then refactored the capstone to USE these on the actual function:
- `F0_nonempty_of_witness`: the purely-analytic Weierstrass core (sorry-free), parametric in
  the 6 regular-witness facts (feasible x₀, ε>0, two `continuous_on`, gradient nonvanishing on
  ∂B_ε, gradient-or-nondegenerate on Ω̃) ⟹ `∃ξ κ ε>0. 𝓕₀ ≠ ∅`. This is the old `F0_nonempty`
  body with the `obtain … regular_feasible_witness` lifted out to hypotheses.
- `regular_feasible_point_dip` (the genuine remaining hole, sorry): for `cvec_dip ω₀ ωs`,
  `gain_dip`, ∃ feasible x₀ and ε>0 with gradient nonvanishing on ∂B_ε and gradient-or-
  nondegenerate on Ω̃ — NO continuity (that's now proven), so a strictly smaller & TRUE
  obligation = the `Phi_bad_meager`+Baire payoff.
- `regular_feasible_witness_dip`: bolts the proven `norm_gradU_dip_continuous_on` and
  `continuous_on_add … sigma_min_HessU_dip_continuous_on` onto `regular_feasible_point_dip`.
- `F0_dip_nonempty`: the paper-faithful headline — `𝓕₀` for the ACTUAL dipole pattern
  `U_dip = g(ω)|A|²` (steered `cvec_dip`, smooth `gain_dip=|e(θ)|²`) is nonempty, via
  `F0_nonempty_of_witness` + `regular_feasible_witness_dip`.

REMOVED the abstract `F0_nonempty`/`regular_feasible_witness` (parametric in arbitrary
`cvec`/`g`): the latter is UNprovable as stated (gain could be negative ⟹ `𝓕` empty) and
assumed continuity — the exact placeholder trap. Net: the file's 2 sorries are now both
honest & true — `Phi_bad_meager` (determinant submersion) and `regular_feasible_point_dip`
(regular feasible point for the dipole). Builds clean (BUILD_EXIT=0, ~50s).

## 2026-06-01 (𝓕 nonempty) — explicit feasibility witness PROVED (sorry-free)

`Ffeas_dip_nonempty` DONE: **the feasible set 𝓕 for the actual dipole pattern is nonempty**
(`∃R>0, x::(real^2)^'n. x ∈ Ffeas (cvec_dip ω0 ωs) gain_dip R dmin A B D ωn ω0 δnull pmin`),
under well-posedness hyps (N>1, cvec_dip(ωn)≠0, dmin>0, δnull≥0, pmin ≤ |e(θ0)|²N², cosθs≠cosθ0).
This is D_edit Prop. openfeas / L450–566, the literal "prove the set is nonempty using the
actual function and sets."

Construction (sorry-free): enumerate elements by a bijection `f` of `{..<N}`
(`ex_bij_betw_nat_finite`); place element `f k` to solve the single linear phase equation
`𝒬·x' + 𝒫·y' = 2πk/N` (where (𝒬,𝒫)=cvec_dip(ωn), split on which coeff ≠0), spreading the
*other* coordinate as `dmin·k` for spacing. Then:
- null `A(x̄,ωn)=0` via roots of unity reindexed by `f` (`af_null_zero` + `sum_cis_neg_roots_unity`);
- spacing `c(x̄)=0`: `spdist ≥ |Δ(one coord)| = dmin·|k−j| ≥ dmin` (`spdist_ge_abs1/2`,
  `nat_real_abs_diff_ge1`), so every `max 0 (dmin−spdist)` term is 0 (`sum.neutral`);
- main beam `P(x̄)=g(ω0)·N² ≥ pmin` automatic (`Upow_at_main`, cvec_dip collapses at ω0);
- ball: take `R = ‖x̄‖+1`.

GOTCHAS (the build fights): (i) HMA `vec` `'a^'n` REQUIRES `'n::finite`; the lemma's `'n`
came only from `CARD('n)` in the assumptions (sort `type`), while the conclusion's `x` had an
*independent* finite index — they were never unified, so `χ`/`(real^2)^'n` failed
("Variable 'n::type not of sort finite"). FIX: pin the conclusion `∃x::(real^2)^'n. …`,
forcing `'n::finite` lemma-wide and tying the witness to the same index. (ii) `finite UNIV`
for that `'n` is then derivable but we obtain `f` via `ex_bij_betw_nat_finite` + deriving
`finite` from `CARD('n)>1` (`card.infinite`, `gr_implies_not0`). (iii) `(𝒬,𝒫)≠0` from
`cvec_dip(ωn)≠0` via `vec_eq_iff`+`forall_2`+`zero_index`.

Then (same session) factored the construction into `feasible_witness_exists` (parameterised
by a spacing target `s>0`: nulls A at ωn and spaces elements ≥ s) and re-derived
`Ffeas_dip_nonempty` from it (no duplication). Added the OPEN-feasibility results:
- `Ffeas_dip_has_interior`: with STRICT margins (s=dmin+1>dmin, δnull>0, pmin<g·N²) the
  witness is strictly feasible, so `ball_inside_Ffeas` ⟹ `∃R x ρ>0. ball x ρ ⊆ 𝓕`.
- `Ffeas_dip_open_feasible`: the paper's **prop:openfeas** — `∃R, nonempty open V ⊆ 𝓕`
  (V = ball x ρ). Also `gain_dip_nonneg` (g=|e|²≥0, from `gdip_eq_edip_sq`).
All sorry-free. So the entire FEASIBILITY layer (closed nonempty + open nonempty interior)
is DONE for the actual dipole. Builds clean (BUILD_EXIT=0).

## 2026-06-01 (prop:dimZ Step 1) — Φ factors through the moment map M_paper (gradient half)

Toward `Phi_bad_meager` (= prop:dimZ), began the **Φ = F∘M** factorization that lets the
proven `bigJ`-surjectivity (`lem:Msurj`) act on Φ's derivative. Established (sorry-free):
- `M_paper_eq_robust_moments`: the determinant-side moment map `M_paper x (cvec ω)`
  (`complex^6`, Jacobian = `bigJ`) **equals** `[A_cart, Mmom 1, Mmom 2, M2mom 1 1, M2mom 1 2,
  M2mom 2 2]` — i.e. the local moments through which `gradU`/`HessU` are expressed ARE
  `M_paper`. (Matched via `A_moment_def`/`M1_moment_def`/…/`phase_def`, `w_M12_def`,
  `power2_eq_square`+`of_real_mult`.) `M_paper` is in scope: Robust → Capstone → Regnonzero →
  `Nonemptiness_Paper` → `Applied_Math_BlockDet.Moment_Map`.
- `M_paper_proj_A`/`_M1`/`_M2`/`_M11`/`_M12`/`_M22`: the six component-projection rewrites.
- `gradU_component_via_M_paper`: **Φ₁,Φ₂ (the gradient half) depend on (x,ω) only through
  M_paper's coords A,M₁,M₂** (plus the gain/steering jet `gain,dgain,dc` as parameters).
  From `gradU_component_via_moments` + `sum_2` + the projections.

## 2026-06-01 (prop:dimZ Step 1, ω–c bridge) — moment-space c-derivatives built

The ω–c bridge scaffold, sorry-free:
- `Afun x c = ∑ cis(−c·xₙ)`, `Mcfun x c k`, `M2cfun x c k l` — the array factor and
  moments as functions of the *wavevector* `c`; bridge identities `A_cart cvec x ω =
  Afun x (cvec ω)`, `Mmom = Mcfun (cvec ω)`, `M2mom = M2cfun (cvec ω)`.
- `has_derivative_cis_c` (per-term phase c-derivative), `has_derivative_Afun_c`
  (`D_c A(h) = −i ∑(h·xₙ)cis`), `has_derivative_Mcfun_c` (`D_c M_k(h) = −i ∑(xₙ)_k(h·xₙ)cis`),
  with partials `Afun_c_partial`/`Mcfun_c_partial`: j-th/l-th partial = `−i M_j` / `−i M2_{kl}`.
  So the second moments enter by one more c-differentiation. No steering jet.

GOTCHAS: (i) `term` is a reserved Isabelle command — can't be a fact label; use `tderiv`.
(ii) `has_derivative_sum` needs explicit `rule` (not `auto intro:`) for the HO unification of
the summand derivative. (iii) Standalone lemmas with free `x` hit the JNF-`vec_index`-vs-HMA-
`vec_nth` `$` ambiguity → "Failed to parse prop"; pin with `fixes x :: "(real^2)^'n"` (defs
like `Afun` already constrain it).

KEY REALIZATION (the clean route to the Hessian): work in **c-coordinates** = the cvec=id,
gain≡1 specialization. Then `gradU (λc. c) (λ_. 1) x` is the c-gradient of `|A|²`, and
`gradU_component_real_moments` (with dc=id, dgain=0) already gives it as
`2(Re A · Im M_j − Im A · Re M_j)`. Differentiating *that* in c (using the c-derivatives
above, no jet) yields the c-Hessian as a clean moment polynomial `H_{kl} = 2(Re(cnj M_l·M_k)
− Re(cnj A·M_{kl}))`. The general ω-Hessian then = chain/product rule through cvec,gain
(bringing in d²c, d²gain as x-constant coefficients). NEXT BRICK: the c-Hessian of `|A|²`
in moments (differentiate the c-gradient), then the bridge, then `det = poly(M_paper)`.

## 2026-06-01 (prop:dimZ Step 1, the Hessian) — c-Hessian of |A|² computed in moments

**THE HESSIAN IS COMPUTED.** `HessU_c_eq` (sorry-free): in c-coordinates (cvec=id, gain≡1),
`HessU (λc. c) (λ_. 1) x c = Hcmat x c` where
`Hcmat x c $ k $ l = 2(Re(cnj M_l · M_k) − Re(cnj A · M_{kl}))` — the moment-space Hessian,
a polynomial in the six `M_paper` moments. So `Φ₃ = det∇²U = Hcmat₁₁·Hcmat₂₂ − Hcmat₁₂²` is
now an explicit moment polynomial (the paper's "moment-space form of the bad-point map").

Chain of the computation (all sorry-free), each a committed brick:
- c-derivatives `∂_c A = −iM`, `∂_c M_k = −iM_{kl}` (`has_derivative_Afun_c/Mcfun_c`).
- Re/Im pushed through the derivative sums (`ReDAfun/ImDAfun/ReDMfun/ImDMfun`,
  `Im_M2cfun/Re_M2cfun`): collect into moments.
- Four piece-derivatives `dRe_Afun/dIm_Afun/dRe_Mcfun/dIm_Mcfun` (bounded_linear Re/Im ∘
  c-derivative, rewritten to moment form via `has_derivative_eq_rhs`).
- `has_derivative_gradU_c`: differentiate the c-gradient field componentwise (product rule on
  `2(Re A Im M_j − Im A Re M_j)`, matched to `(Hcmat *v h)_j` by sum-merge + `Re(cnj·)`).
- `HessU_c_eq` via `HessU_explicit` + `matrix_of_matrix_vector_mul`.

GOTCHAS (cost real cycles, with brydustin debugging alongside): (i) **`simp` unfolds
`Im(cis(−θ)) = −sin θ`** injecting negations — keep `cis` opaque: apply per-term reorder
lemmas via `sum.cong[OF refl] + rule`, NOT `simp add: lemma`. (ii) `of_real_mult[symmetric]`
LOOPS against the default `of_real_mult`; just `simp` (the `times_complex` selectors are
`[simp]`, so `Im(of_real a*of_real b*z)` reduces). (iii) `term` is a reserved command — not a
fact label; use `tderiv`/`perterm`. (iv) `has_derivative_sum` needs explicit `rule` (HO
unification). (v) `vec_eq_iff`/`subst vec_eq_iff` flaky on `χ`-equations — prove componentwise
then `simp add: Finite_Cartesian_Product.vec_eq_iff`. (vi) standalone lemmas with free `x` hit
the JNF-vs-HMA `$` ambiguity — pin `fixes x :: "(real^2)^'n"`.

NEXT: `det Hcmat` as the explicit `Φ₃` moment polynomial (trivial now), then the ω–c bridge
to the general `cvec_dip`/`gain_dip` HessU (chain rule, d²c/d²gain as x-constant coeffs), then
`Φ = F∘M_paper` ⟹ `D_xΦ = D_M F · bigJ` ⟹ rank/`smooth_chart_meager` ⟹ `Phi_bad_meager`.

## 2026-06-01 (prop:dimZ Step 2) — the ω–c bridge (first order + second-order ingredients)

The actual angle-pattern `U(x,ω)` relates to the moment-space c-quantities via `U = gain·(V∘cvec)`,
`V = U_cart (λc.c)(λ_.1) x = |A|²`. All sorry-free, committed:
- `U_cart_factor`: `U_cart cvec gain x ω = gain ω * U_cart (λc.c)(λ_.1) x (cvec ω)`.
- `has_derivative_Uc_c`: `V` has `gradU_c` as its genuine Fréchet gradient (via
  `has_derivative_U_cart` at id/const + `grad_fun_satisfies_GRAD`).
- `has_derivative_U_via_c` (first-order bridge): `D_ω U(v) = gain(ω)(Dcvec v · ∇_cV) + dgain(v) V`
  (chain `diff_chain_at` on cvec + product `has_derivative_mult` on the factorization).
- `gradU_via_c`: the actual ω-gradient field assembled: `∇_ω U = Σ_i [gain(ω)(Dcvec e_i·∇_cV) +
  dgain(e_i) V] e_i` (via `has_derivative_to_gradient` + `grad_fun_eq`).
- Second-order ingredients: `has_derivative_gradU_c_along_cvec` (`D_ω[∇_cV(cvec ω)] = Hcmat(cvec ω)·Dcvec`,
  chain on `has_derivative_gradU_c`), `has_derivative_V_along_cvec` (`D_ω[V(cvec ω)] = Dcvec·∇_cV`).

REMAINING (the final assembly of the Hessian bridge — the last big analytic piece): differentiate
`gradU_via_c`'s RHS once more to get `HessU cvec gain x ω` as the moment-space matrix
`HessU_ij = (∂_jg)(Dφᵀ∇_cV)_i + g[(D²φ·∇_cV)_ij + (Dφᵀ Hcmat Dφ)_ij] + (∇_cV·∂_jφ)(∂_ig) + V(∂_j∂_ig)`.
Needs cvec,gain C² (for the dipole: `has_derivative_Dcvec_dip`/`D2cvec_dip`, `gain_dip` C²) so the
jet `Dcvec`,`dgain` are themselves differentiable (→ `D²cvec`,`d²gain`). Then `det HessU = poly(M_paper)`
⟹ `Φ = F∘M_paper` ⟹ `D_xΦ = D_M F·bigJ` ⟹ rank 3 (`lem:3x3`,`bigJ_surj`) ⟹
`smooth_chart_meager` over an Ω-cover ⟹ `Phi_bad_meager`.

(OLD note) REMAINING for Step 1 (the Hessian half): `Φ₃ = det∇²U = H₁₁H₂₂−H₁₂²` through `M_paper$4,5,6`
(the second moments). Needs `HessU $ k $ l` as an explicit function of `A,Mmom,M2mom` and the
**second** jet `d²gain`, `d²c (=E)` — obtained by differentiating the moment form of `gradU`
(`gradU_component_real_moments`); the M2mom-entry machinery is present (`has_derivative_Mmom`,
`has_derivative_dA_via_M2`, `has_derivative_dA_dip`, `D2cvec_dip`) but not yet assembled into a
closed `HessU = f(moments)`. That is the next sub-brick.

REMAINING (2 sorries): `Phi_bad_meager` (the 12×12-determinant submersion ⟹ codim-3 ⟹ meager
projection — the deep core) and `regular_feasible_point_dip`. The latter now has its open
Baire arena (`Ffeas_dip_open_feasible`); to finish it: intersect that open V with the
co-meager regular set (from `Phi_bad_meager` + Baire on the complete space ℝ^{2N}) to get a
config with no degenerate critical point on the annulus, plus an ε-sphere avoiding the
(finitely/discretely many) critical points. Both steps are substantial and bottom out at
`Phi_bad_meager`, which needs the Sard/meager-projection machinery
(`Applied_Math_Sard.Sard_Negligible`) wired to the proven `bigJ_det`/`W_surj`.

## 2026-05-30 (robust set, Part 1b) — 𝓕 RE-defined faithfully (c,N,P) and compact

Corrected `Ffeas` to the actual paper definition (`D_edit_May18(3).tex`,
§Existence of Global Minimizer): `𝓕 = c⁻¹({0}) ∩ N⁻¹([0,δ_null]) ∩
P⁻¹([p_min, |e(θ₀)|²N²]) ∩ B_R` (the earlier version used the single-file tex's
simpler spacing+null+ball form). Now in preimage notation:
- `spdist A B D p q` = inter-element distance with beam-focusing `z=(Ax+By)/D`;
- `cpen dmin A B D x = Σ_{n≠m} max{0, dmin − spdist…}` — spacing penalty `c`;
- `N(x)=Upow … ω_null`, `P(x)=Upow … ω₀`;
- `Ffeas … = cpen⁻¹{0} ∩ (Upow·ω_null)⁻¹{0..δ} ∩ (Upow·ω₀)⁻¹{pmin..g ω₀·N²} ∩ cball 0 R`.
`Ffeas_compact`: `c,N,P` continuous ⟹ preimages closed (`closed_vimage`); their
intersection is closed (`closed_Int`); `∩ cball` is compact (`closed_Int_compact` +
`compact_cball`). Clean structured proof (no `apply`). GOTCHA: `/D` for constant `D`
triggers a `D≠0` side-goal under `continuous_intros` — rewrite via `divide_inverse`
(continuous unconditionally). NEXT: Part 2 conjecture `∃ξ κ ε. 𝓕₀(ξ,κ,ε) ≠ ∅` with
explicit `ξ,κ,ε` dependence and `\<nabla>`/`‖·‖` (importing `Higher_Differentiability_Multi`).

## 2026-05-30 (robust set, Part 1) — concrete U, 𝓕, and 𝓕 compact

New theory `Appendix/Nonemptiness_Robust.thy` begins the concrete, paper-faithful
build of `thm:final`. Part 1 (sorry-free):
- `Upow cvec g x ω = g ω · (cmod (af cvec x ω))²` — the sidelobe power `U = g|A|²`.
- `continuous_on_af_config` / `continuous_on_Upow_config`: `A`, `U` are continuous in
  the configuration `x` (`continuous_intros` + `continuous_on_cis`).
- `Ffeas cvec g R dmin δnull ωN = {x ∈ cball 0 R : ∀n≠m. dmin ≤ dist(x$n)(x$m),
  Upow … ωN ≤ δnull}` — the feasible set `𝓕`.
- `Ffeas_compact`: `𝓕` is COMPACT — it is `cball 0 R ∩ closed_spacing ∩ closed_null`,
  i.e. closed feasibility constraints inside a bounded ball (Heine–Borel via
  `compact_Int_closed`/`compact_cball`).

Plan for the rest (concrete `thm:final`): Part 2 — `Γ_ε(x)`, `X₀(ξ,κ)`, `𝓕₀` using the
gradient `\<nabla>`/Hessian `\<nabla>\<^sup>2` and `‖·‖` (σ_min ≥ 2ξ rendered as
`⟨v,∇²U·v⟩ ≥ 2ξ‖v‖²`); Part 3 — finite-critical-set ⟹ `ξ` exists; Part 4 — assemble.
ARCHITECTURE NOTE: `\<nabla>`/`\<nabla>\<^sup>2` live in `Higher_Differentiability_Multi`
(`HigherDiff` session on `Smooth_Manifolds`), NOT imported by the nonemptiness stack;
Parts 2–4 need either merging that session or re-exposing `\<nabla>` locally.

## 2026-05-30 (appendix sorry-free!) — lem_h0res_a1a2 made concrete; regnonzero appendix complete

`lem_h0res_a1a2` PROVED concretely, so **`Nonemptiness_Regnonzero_Appendix.thy` is now
entirely sorry-free**. The abstract `rk_residue x = 2` (unprovable: arbitrary `rk_residue`)
was replaced by the paper's actual computation. The residue moments are the `b₁`-type
`a₁ = -Σ uₖ sin(κuₖ)` and the `v`-cosine `a₂ = Σ vₖ cos(κuₖ)`; differentiating (single-slot,
à la `lem_block`, with `deriv` + `derivative_eq_intros`) gives the residue partials
`∂_{uₙ}a₁ = β(uₙ) = -(κuₙ cos κuₙ + sin κuₙ)`, `∂_{vₘ}a₁ = 0`, `∂_{vₘ}a₂ = cos κuₘ`,
`∂_{uₙ}a₂ = -κvₙ sin κuₙ`. The `2×2` Jacobian block is triangular, so its determinant is
`β(uₙ)·cos κuₘ`, nonzero off the exceptional sets (`β(uₙ)≠0`, `cos κuₘ≠0`) — rank 2.

Remaining holes are all in `Nonemptiness_Capstone.thy` (the concrete-nonemptiness layer):
`capstone_feasible`, the four `branch_*_meager` reductions, and `capstone_X0_sound`.
Plan for that layer: define `X_robust(κ)` and `X₀(ξ,κ)` explicitly, use the `\<nabla>` gradient
(`Higher_Differentiability_Multi.hess_fun`/grad) and `\<parallel>\<cdot>\<parallel>` norm notation, prove `\<F>` compact
before the nonemptiness assembly, and keep everything readable / faithful to `thm:final`.

## 2026-05-30 (Lambda-common) — prop_Lambda_common via collinearity of the (∂E₁,∂Q₁₁) vectors

`prop_Lambda_common` PROVED. As originally stated it was UNprovable: `Lam` was an
abstract `fixes` function and the hypotheses `Lam i j = 0` had no stated relation to
the conclusion `Fj` (3 linear equations in 2 unknowns are generically inconsistent).
Restated faithfully to the paper (tex L5434/L5656): `Λ⁽¹¹⁾ᵢⱼ = det ∂(Φ₁,H₁₁)/∂(uᵢ,uⱼ)`
is the `2×2` minor of the gauge-data vectors `vE j = ∂_{uⱼ}E₁ = -2g·BBⱼ - g₁κ·ssⱼ`
and `wQ j = ∂_{uⱼ}Q₁₁`, so the hypotheses become the minor equations
`vEᵢ·wQⱼ = vEⱼ·wQᵢ`. With a nondegeneracy `some vE ≠ 0` (the regular-stratum gauge
`g>0` supplies it), all three vectors `(vEⱼ,wQⱼ)` are collinear, hence share a ratio
`μ` (`wQⱼ = μ·vEⱼ`); then `α = r+gμ`, `β = r²-χ₁₁+g₁μ` solves all three because
`Fⱼ(α,β) = wQⱼ - μ·vEⱼ` (a polynomial identity).

Only **1 real sorry remains**: `lem_h0res_a1a2` (`rk_residue x = 2` for an abstract
`rk_residue :: 'w ⇒ nat`) — a genuine placeholder, NOT provable as stated (false for
an arbitrary `rk_residue`); it needs the concrete residue Jacobian defined and its rank
computed (à la `bigJ_det`).

GOTCHAS: (i) `defines` are SIMULTANEOUS, so a later one cannot reference an earlier one
(`Lam ≡ ... vE ... wQ ...` failed "Extra variables on rhs") — state the minor equations
directly instead. (ii) `\<lambda>` is the reserved lambda binder; do not use it as a variable
name (`∃\<lambda>. ...` fails to parse) — used `\<mu>`.

## 2026-05-30 (uphi) — prop_uphi_codim3: discreteness of the F_eta zero set

`prop_uphi_codim3` PROVED: \<open>Z\<^sub>\<eta> = {u : F\<^sub>\<eta>(u)=0}\<close> is discrete, where
\<open>F\<^sub>\<eta>(u) = cos(\<kappa>u) - \<kappa>(u-\<eta>)sin(\<kappa>u)\<close>, \<open>\<kappa>\<noteq>0\<close>. Appendix down to 2 real sorries
(`prop_Lambda_common`, `lem_h0res_a1a2`).

Key: the zeros are \<^emph>\<open>simple\<close>. At a zero, \<open>F\<^sub>\<eta>'(u) = -2\<kappa> sin\<kappa>u - \<kappa>\<^sup>2(u-\<eta>)cos\<kappa>u \<noteq> 0\<close>:
if both \<open>F\<^sub>\<eta>=0\<close> and \<open>F\<^sub>\<eta>'=0\<close> then substituting \<open>cos\<kappa>u = \<kappa>(u-\<eta>)sin\<kappa>u\<close> gives
\<open>sin\<kappa>u\<cdot>(2+(\<kappa>(u-\<eta>))\<^sup>2)=0\<close>, so \<open>sin\<kappa>u=0\<close> (the factor is \<open>>0\<close>), hence \<open>cos\<kappa>u=0\<close> too ---
contradicting \<open>sin\<^sup>2+cos\<^sup>2=1\<close>. A simple zero is isolated: \<open>F\<^sub>\<eta>'\<close> is continuous, so it
keeps its sign on a ball \<open>(u-\<delta>,u+\<delta>)\<close> (`order_tendstoD` + `eventually_at`); there
\<open>F\<^sub>\<eta>\<close> is strictly monotone (`DERIV_pos_imp_increasing` / `DERIV_neg_imp_decreasing`),
hence injective, so \<open>u\<close> is the only zero in the ball.

GOTCHAS: (i) substitute the zero relation with `simp only: e1` BEFORE `algebra_simps`
--- in `using e1 ... simp`, `algebra_simps` reorders \<open>e1\<close> into a sum and never uses it
as the rewrite \<open>cos\<kappa>u \<rightarrow> \<kappa>(u-\<eta>)sin\<kappa>u\<close>. (ii) the original `assumes "\<kappa> \<noteq> 0"` was
UNNAMED; naming it `\<kappa>:` is required to cite it (`Undefined fact "\<kappa>"`).

## 2026-05-30 (KLM minors) — prop_KLM_1 + prop_KLM_2 via Cramer / cofactor identities

Both `prop:KLM` minors PROVED; appendix down to 3 real sorries (`prop_uphi_codim3`,
`prop_Lambda_common`, `lem_h0res_a1a2`).

- `prop_KLM_1` (`K=L=M=0 \<longleftrightarrow> s=0` on `c\<^sub>1c\<^sub>2c\<^sub>3\<noteq>0`): the \<open>\<Longrightarrow>\<close> direction is FALSE as
  originally stated --- a collinear triple has `\<tau> = s/c = const\<cdot>(1,1,1)`, giving
  `K=L=M=0` with `s\<noteq>0`. Added the good-triple hypothesis `A\<^sub>T = det3 1 1 1 u v \<noteq> 0`.
  Then the clean route is three **Cramer identities**, each a pure `det3` polynomial
  identity (`simp add: det3_def algebra_simps`):
    `s\<^sub>i \<cdot> (\<Prod>\<^sub>j\<^sub>\<noteq>\<^sub>i c\<^sub>j) \<cdot> A\<^sub>T = K + u\<^sub>i L - v\<^sub>i M`.
  Verified out of band via the scalar triple product: `(u\<times>v) + u\<^sub>1(v\<times>\<one>) - v\<^sub>1(u\<times>\<one>) =
  (A\<^sub>T,0,0)`. So `K=L=M=0` forces `s\<^sub>i (\<Prod>c) A\<^sub>T = 0`, and `c\<^sub>j\<noteq>0`, `A\<^sub>T\<noteq>0` give `s\<^sub>i=0`.
- `prop_KLM_2` (one `cos=0 \<Longrightarrow> L\<noteq>0 \<or> M\<noteq>0`): needs the array points pairwise
  DISTINCT (else the relevant minor vanishes). Per case `c\<^sub>i=0`: `c\<^sub>i=0 \<Longrightarrow> s\<^sub>i\<noteq>0`
  (Pythagoras), and `L = s\<^sub>i (\<Prod>c) (v\<^sub>j - v\<^sub>k)`, `M = s\<^sub>i (\<Prod>c) (u\<^sub>j - u\<^sub>k)`, so distinctness
  of points `j,k` gives `L\<noteq>0 \<or> M\<noteq>0`.

GOTCHA (cost a build): a `have sin1: "\<And>w. cos w = 0 \<Longrightarrow> sin w \<noteq> 0"` leaves `w`
POLYMORPHIC (`sin`/`cos` are over `'a::{banach,...}`), so a `fix w :: real` body
mismatches and the `show` fails with the misleading "Failed to refine any pending
goal". Fix: annotate the binder in the statement --- `\<And>(w::real). ...`.

## 2026-05-30 (even later) — astar strict-monotonicity (the double-root injectivity)

`prop_double_param_mono` (`strict_mono_on UNIV (astar \<kappa>)`, \<kappa>\<noteq>0) now PROVED, plus its
prerequisite `astar_deriv`. This is the ingredient behind `cor:double-impossible`
(no two distinct indices are both degenerate-critical), so `cor_double_impossible`
also goes through. Appendix down to 5 real sorries.

- `astar_deriv`: \<open>astar' u = sin\<^sup>2(\<kappa>u)(5+sin\<^sup>2(\<kappa>u))/(1+sin\<^sup>2(\<kappa>u))\<^sup>2\<close> (a manifest SOS \<open>\<ge>0\<close>).
  Built via the quotient rule (`DERIV_divide`, whose denominator is `g*g` not `g\<^sup>2`),
  then the value is simplified through a cleared-numerator polynomial identity
  `?g\<cdot>?g - ?num = 4\<kappa>\<^sup>2 s\<^sup>2(5+s\<^sup>2)`: rewrite the double angles with `simp only: sd cd`
  FIRST, substitute `cos\<^sup>2 = 1-sin\<^sup>2` once, then plain `algebra_simps`/`power2_eq_square`.
- `prop_double_param_mono`: the library only gives nondecreasing from `f'\<ge>0`
  (`DERIV_nonneg_imp_increasing_open`), and `astar'` vanishes at the isolated points
  `sin(\<kappa>u)=0`, so strictness needs an extra argument: if `astar x = astar y` then `astar`
  is constant on `[x,y]`, hence (via `has_field_derivative_transform_within_open` against
  the constant function) `astar' \<equiv> 0` on `(x,y)`, forcing `sin(\<kappa>u)\<equiv>0` there; the same
  transform trick on `sin(\<kappa>\<cdot>)` then gives `cos(\<kappa>u\<^sub>0)=0` too, contradicting `sin\<^sup>2+cos\<^sup>2=1`.

## 2026-05-30 (later still) — Appendix leaves: lem_Fij, the algebra corollaries, prop_double_param_solves

Cleared four more `sorry` leaves in `Nonemptiness_Regnonzero_Appendix.thy` (now 6 real
sorries left):
- `cor_pairambiguity`, `cor_H0subcase`, `cor_vpair22_nonzero` — pure algebra from the
  factorizations (`d\<^sub>ij = -2\<Delta>\<^sub>ij K`, etc.); `mult_eq_0_iff` / `field_simps`.
- `upair_minor_nowhere_dense` — added the missing `continuous_on UNIV` hyp, routed through
  `lines_entire_slice_nowhere_dense`.
- `lem_Fij` — restated noncollinearity as `A\<^sub>T \<noteq> 0` (= `det3 1 1 1 u v`, cleaner than the
  `\<exists>`-line form) and proved via the cancellation identity `F\<^sub>1\<^sub>2 - F\<^sub>1\<^sub>3 + F\<^sub>2\<^sub>3 = a\<cdot>A\<^sub>T`
  (the `a\<^sub>1,a\<^sub>2` terms cancel identically; the `a`-term is exactly the triple determinant).

**`prop_double_param_solves` — the rational-trig identity, now fully proved.** Statement
gets the honest `\<kappa> \<noteq> 0`. The two `Fparam` terms are exact negatives: with `s=sin\<kappa>u`,
`c=cos\<kappa>u`, `astar-u = -sc/(\<kappa>(1+s\<^sup>2))` (term 1 `= -2sc(c-\<kappa>us)/(\<kappa>(1+s\<^sup>2))`) and
`bstar-u\<^sup>2 = 2c(c-\<kappa>us)/(\<kappa>\<^sup>2(1+s\<^sup>2))` (term 2 `= +2sc(c-\<kappa>us)/(\<kappa>(1+s\<^sup>2))`). Key
Isabelle lessons that finally cracked it:
- `field_simps` is the WRONG tool here: it *distributes* `2\<kappa>(1+s\<^sup>2)` into `\<kappa>\<cdot>2 + \<kappa>\<cdot>2s\<^sup>2`,
  loses the factored form, and can no longer discharge `\<noteq> 0` to cross-multiply. Keep
  denominators factored instead.
- Compute `astar-u` and `bstar-u\<^sup>2` as single factored fractions (`amu`, `bmu`); for `bmu`
  clear the denominator with `nonzero_eq_divide_eq` (atomic in `Dn`) rather than
  `diff_divide_distrib` (which explodes the long numerator).
- The cleared-numerator identity `key` must rewrite the double angles with `simp only: sd cd`
  FIRST (exact `sin(2\<kappa>u)`/`cos(2\<kappa>u)` match) BEFORE `algebra_simps`, because `algebra_simps`
  reorders `2\<kappa>u \<rightarrow> \<kappa>(u\<cdot>2)` and then `sin_double`/`cos_double` no longer fire. The leftover
  `2c\<^sup>2+2s\<^sup>2 = 2` is linear in the atoms `c\<cdot>c`,`s\<cdot>s` and closes with the product-form
  Pythagorean `cs` via `argo`: `using cs by (simp only: sd cd, simp add: algebra_simps
  power2_eq_square, argo)`.

## 2026-05-30 (later) — Regnonzero appendix: full skeleton + capstone + first real proofs

New theory `Appendix/Nonemptiness_Regnonzero_Appendix.thy` (session
`Applied_Math_Appendix`, parent `Applied_Math_Nonemptiness`) states EVERY appendix
obligation of `prop:regnonzero` (Appendix A–I), and `Appendix/Nonemptiness_Capstone.thy`
closes START→FINISH: `odd_N_nonemptiness` is *proved* by feeding the four concrete
bad sets (defined from `af`) + feasibility + X0-soundness into the sorry-free
`nonemptiness_from_meager_branches`. So no unstated gaps remain.

Design rule (after corrections): NO locales; lemmas connect either as concrete/universal
facts (real moment map / `det3` / plain reals) or as parametric facts carrying the real
structural hypothesis the concrete object satisfies (`rline_entire`, a chart cover) — like
`nonemptiness_from_branches`. Bugs caught by *trying to prove*:
- `prop:upair`'s global strict-monotonicity of `R(t)` is FALSE (R has poles / is U-shaped);
  restated with an `inj_on` (single-branch) hypothesis.
- `analytic_cut_meager_proj` (single cut ⇒ meager projection) was FALSE (codim-1 cut
  projects ONTO V); replaced by the dimension-drop engine `proj_lowdim_meager` (via
  `rank_deficient_C1_image_meager`).
- `prop:vmixed` was off by a factor 2 (third row is `2vⱼcⱼ`, the `∂_v a₂₂` derivative).

PROVED sorry-free this session: `R_even`, `prop_upair`, `x_plus_sin_pos`, `Num_pos`
(corrected SOS `2Num = t²(2t+sin2t)+2(2t−sin2t)+4t sin²t`), `R_strict_mono_first_branch`,
`ab_eq_R`, `alpha_beta_inj_on_branch` (u-pair branch closed end-to-end); `analytic_cut_nowhere_dense`,
`proj_lowdim_meager`; templates `threecos_meager_in_V`, `Bbranch_meager_in_V`;
`lem_h0res_Bcuts` (β′≠0 transversality); `prop_vcos/vsin/vmixed`; `lem_block` (7 J₅ partials),
`lem_3x3` (3 rank-3 minors); `cor_pairambiguity`, `cor_H0subcase`, `cor_vpair22_nonzero`;
`upair_minor_nowhere_dense`. Down to ~8 real sorries (calculus/transcendental:
`prop_double_param_*`, `prop_uphi_codim3`, `prop_Lambda_common`, `lem_Fij`, `prop_KLM_*`,
`lem_h0res_a1a2`) + the IFT chart keystone + the `(ℝ²)ⁿ ≅ ℝ²ᴺ` wiring.

Traps logged: `*s`/`*v` are cartesian operators (`*sin` lexes as `*s`+`in`) — use variable
`t` and natural spacing; `DERIV_divide` gives `g x * g x` not `(g x)²`; simp distributes
`−(a+b)` before cancelling `(−a)/(−b)` — group/use `divide_minus_right`; `\<^const>` only on
genuine constants (not lemma names); `real^('m::{finite,wellorder})` must annotate the index
sort at EVERY occurrence; non-greedy `lemma (\w+):.*?` regex spans across lemmas
(use `(?:(?!\nlemma ).)*?`).

## 2026-05-30 — Transversality MEAGER stub: blocked on one σ-compact ∃-discharge (full record of dead ends)

**Stop point for the night.** One — and only one — proof step is blocking the whole
`parametric_transversality_meager_euclidean_stub` (stub 2). Everything around it works;
the σ-compact `∃K` discharge does not, and we burned hours on it. This entry records
*exactly* what fails so we do NOT repeat it tomorrow, plus untried ideas to try first.

### Proven + COMMITTED (safe baseline)
- `smooth_chart_meager` / `rank_deficient_C1_image_meager` / `open_sigma_compact_exhaustion`
  (= `lem:smooth-chart-meager`), in `Parametric_Transversality_Euclidean_Base`. Sorry-free,
  `Applied_Math_Nonemptiness BUILD_EXIT=[0]`, committed+pushed earlier today.
- (yesterday) `DM_paper_open_dense_surjective` = `lem:Msurj`; `APPENDIX_PLAN.md`; STATUS reframe.

### In the working tree, UNCOMMITTED and currently BROKEN (build fails at the σ-step)
- `meager_critical_values_from_charts` — meager analog of `negligible_critical_values_from_charts`,
  with a σ-compact hypothesis `sigma` (currently object form `∀i. ∃K. (∀n. compact (K n)) ∧ Crit i = (⋃n. K n)`).
- `charts_core_2d` (the IFT-chart `sorry`) was strengthened with a 4th conjunct giving σ-compact `Crit0`.
- `parametric_transversality_meager_euclidean_stub` (stub 2): proof =
  `elim exE` of `charts_core_2d`'s existential → `meager_critical_values_from_charts` → `meager_subset`.

**What already WORKS inside stub 2** (do not re-litigate these):
- Destructuring `charts_core_2d[OF assms]` via `from … show ?thesis proof (elim exE) fix charts Crit0 D0 assume H: "<body>"`. The `elim exE` peels the 3 function-typed existentials cleanly (this solved the original "obtain hangs/fails" problem).
- `note der/rk/sig = conjunct…[OF H]` to split the 4-conjunct `H`.
- der/rk subgoals of `meager_critical_values_from_charts`: `show "⋀i x. …" using der by auto` / `… using rk by auto` — **verified, terminate**.
- Final: `show ?thesis by (rule meager_subset[OF conjunct1[OF H] meag])` — fine.

### THE BLOCKER — discharge `⋀i. ∃K. (∀n. compact (K n)) ∧ Crit0 i = ⋃(range K)` from `sig`
`sig` (= `conjunct2[OF conjunct2[OF conjunct2[OF H]]]`) is `∀i. ∃K. (∀n. compact (K n)) ∧ Crit0 i = ⋃(range K)`
— i.e. **the goal and `sig` are the same statement** (modulo `∀i` vs `⋀i`). Yet *every* discharge fails.

**FAILED — do NOT try these again:**
1. `using sig by blast` — **HANGS** (jEdit purple, non-terminating). blast explores the giant `assume H` (the full `?bad ⊆ … ∧ …` with nested quantifiers) that is in scope.
2. `using sig by auto` / `(use der rk sig in auto)` — FAILS ("Failed to finish proof"): auto won't *synthesize* the `∃K` witness from a `∀∃` fact.
3. `obtain K … using sig[rule_format, of i] by blast` — **HANGS** (blast + `H`).
4. `from sig[rule_format, of i] obtain K where "(∀n. compact (K n)) ∧ Crit0 i = ⋃n. K n" ..` — the `..` (exE) FAILS to prove it.
5. `from sig[rule_format] show "∃K…" .` — `.`/`this` FAILS: it won't instantiate the *fact's* schematic `?i` to the goal's concrete `i`.
6. `by (rule sig[rule_format])` (on the meta `⋀i.∃K…` goal) — FAILS ("Failed to apply initial proof method").
7. `from sig show "∃K…" by (rule spec)` — FAILS: `rule spec`'s higher-order unification picks a *constant* `?P`, so the resulting premise ≠ `sig`.
8. `by (rule sig)` (object `∀i.∃K…` goal, object `sig`) — FAILS ("Failed to apply"): can't use an object-`∀` fact as an intro rule for an object-`∀` goal.
9. `by (fact sig)` — FAILS, same shape.
10. `from sig show "∀i.∃K…" .` — FAILS, same.
11. `meager_critical_values_from_charts[where D=D0, OF der[rule_format] rk[rule_format] sig]` — **"OF: no unifiers."** Cause: `der[rule_format]` is `?x∈Crit0 ?i ⟹ …` (schematic `?i ?x`) but the lemma hyp is `⋀i x. x∈?Crit i ⟹ …` (meta-bound) → schematic-vs-bound mismatch. (So OF cannot discharge the meta-`⋀` der/rk hyps from the object der/rk facts.)
12. `from sig show "∃K…" by (rule spec[of "λj. ∃K. (∀n. compact (K n)) ∧ Crit0 j = ⋃n. K n" i])` — FAILS even with the predicate given *explicitly*. Most likely the literal `Φ` I wrote does not β/η-match `sig`'s stored body (`(⋃n. K n)` prints as `⋃(range K)`), so `from sig` cannot discharge the `∀x. Φ x` premise.

### Root-cause hypotheses (for tomorrow)
- blast/auto family: **hang** (the `assume H` is in scope) or cannot construct an `∃` witness.
- rule/fact/`.`/spec: object `∀`/`∃` quantifiers + a probable **η/representation difference** (`(⋃n. K n)` vs `⋃(range K)`, and possibly the `∃K` binder type) defeat exact matching; HOU picks wrong instances.
- **We have been working BLIND** — we never once printed `thm sig` next to the actual goal. That must change.

### TRY TOMORROW — in this order (all UNTRIED)
1. **Inspect the terms FIRST.** In jEdit put `thm sig` on a scratch line and read the goal at the σ-`show`; diff them character-by-character (η on `range K`, the `∃K` type, sort, `Trueprop`). Do not attempt another proof until we can SEE the exact mismatch.
2. **`elim exE conjE`** instead of `elim exE` + `conjunct…`: split `H` into *directly named* `assume sub … and der … and rk … and sig …`. A directly-assumed `sig` may behave differently from a `conjunct2[OF …]`-extracted one.
3. **`meson` / `metis` with ONLY `sig` passed**: `using sig by meson` — resolution provers are depth-bounded (won't hang like blast) and may close `∀∃ ⟹ ∀∃` without touching `H`. (Sledgehammer was only ever run on the *obtain*, never on this subgoal.)
4. **Hoist the σ-lift into a separate clean lemma** (no `H` in scope): e.g. `lemma σlift: "(∀i. ∃K. P i K) ⟹ <lemma's sigma form>" by blast` proved in a clean context, then `using sig by (rule σlift)` in stub 2 — `rule` applies a closed lemma and does **not** explore `H`. The crux is matching `P`/the term shape.
5. **Reformulate `meager_critical_values_from_charts`** to avoid the `∃`-extraction: take the cover as an explicit family `K :: nat ⇒ nat ⇒ … set` with hyps `compact (K i n)` and `Crit i = (⋃n. K i n)`; stub 2 then supplies `K` from `sig` per-`i` (no global choice needed) — this removes the σ-`∃` discharge entirely. **(Note: axiom of choice is NOT needed — this is pointwise existence; confirmed.)**
6. If the diff in (1) is genuinely η, normalise (`simp only: …`) or restate the σ-hyp literally as `⋃(range K)` to match.

**Bottom line:** the analytic content is done; this is a pure Isar/automation plumbing wall around discharging a trivial `∀∃` in a context polluted by a huge `assume`. Start tomorrow at item (1) — see the terms — then (2)/(4).

## 2026-05-29 (cont.) — Tier 1: `lem:smooth-chart-meager` proved (rank-deficient C¹ image is meager)

`smooth_chart_meager` (sorry-free, `Applied_Math_Nonemptiness` `BUILD_EXIT=[0]`), in
`Parametric_Transversality_Euclidean_Base`: a smooth map from an open `U ⊆ ℝ^m` into
`ℝ^n` with `m < n` has meager image (paper `lem:smooth-chart-meager`, tex L1197).
Proved via the strictly more general

  `rank_deficient_C1_image_meager`: open `U`, `(F has_derivative F' x)(at x within U)`
  on `U`, and `rank (matrix (F' x)) < CARD('n)` everywhere ⟹ `meager (F ` U)`.

**Proof shape (for the paper).** Three ingredients:
1. `open_sigma_compact_exhaustion` — every open `U` in a heine-borel real-normed space
   is `⋃ₙ Kₙ` with each `Kₙ` compact. Construction: `Kₙ = cball 0 n ∩ {x. 1/(n+1) ≤
   setdist {x} (−U)}` (closed margin set via `continuous_on_setdist`, intersect with a
   ball → compact); the `setdist`-margin forces `Kₙ ⊆ U`, and openness (`ball x e ⊆ U`)
   gives the cover. `U = UNIV` handled separately by plain `cball` exhaustion.
2. `baby_Sard` on each compact piece: `rank < n` ⟹ `negligible (F ` Kₙ)`.
3. `Kₙ` compact + `F` continuous ⟹ `F ` Kₙ` compact (closed); a countable union of
   closed negligible sets is meager (`meager_negligible_closed_cover`, already in Base).
The `m < n` corollary discharges the rank hypothesis for free
(`rank (matrix (F' x)) ≤ CARD('m) < CARD('n)` via `rank_transpose`/`rank_bound`).

This is the single highest-leverage Tier-1 lemma: it feeds **both** transversality
stub 2 (`parametric_transversality_meager_euclidean_stub`, rank-deficient case) **and**
`prop:dimZ` facts 1 & 2 of `prop:regnonzero` (`m<n` case). Prototyped in a fast
standalone `HOL-Analysis`-only theory, then folded into the Base theory (reusing its
`meager`/closed-cover chain — no duplication) and verified in the real session.

**Traps hit (recorded for next time):** (i) `cball 0` needs sort `zero` →
`{heine_borel,real_normed_vector}`, not bare `heine_borel`; (ii) annotating an
`obtain` with `(real^'m)` re-imposes the `vec` constructor's bare `finite` sort,
clashing with the context default `{finite,wellorder}` ("finite inconsistent with
default…") — use `nat ⇒ _ set` and let inference recover the element type from `U`;
(iii) `nat_approx_posE` yields `1/of_nat(Suc n) < e`, not `inverse(real(Suc n)) ≤ e`;
(iv) `has_derivative_continuous_on[OF der]` instead of `meson …` to avoid a
unification-bound blowup.

## 2026-05-29 (cont.) — DECISION: commit to the full unconditional `thm:final`; built the complete obligation map

brydustin asked, point-blank, whether there is a real pathway to a *complete* proof
or whether we are chasing a rabbit. Honest answer: there **is** a genuine pathway —
`thm:final` is a Baire closeout over four meager branches (architecture proven), and
each branch reduces to concrete, transcribable obligations. Not a dead end, not a
false theorem. The cost is a large, lopsided appendix. brydustin chose the honest
path: **the complete unconditional theorem.**

Spent this session mapping the *entire* remaining obligation set accurately (the prior
STATUS map had stale entries):

- **Found the ground-truth paper source** (the only place the detailed appendix proofs
  live): `…/Vern_Paulsen_QC/Applied Math/nonemptiness_unified_singlefile_complete.tex`
  (6285 lines). `STATUS.md`'s `L####` index this file; `\label{…}` match the Label
  column. The appendix is **transcribable**, not reverse-engineerable. Recorded in
  memory + `APPENDIX_PLAN.md`.
- **Reframe: `lem:Msurj` (the #1-hardest item per STATUS — the explicit 12×12
  determinant) is already DONE** as `bigJ_det_nonzero`/`bigJ_surj` +
  `DM_paper_open_dense_surjective` (= `W_surj`, the open-dense surjective locus). The
  tex partials (`∂_uA`, `∂_uM₁`, …) are exactly `DM_paper_x_components`. STATUS marked
  it ✗; corrected to ✅. The hardest foundation is behind us.
- **`prop:regnonzero` (tex L1240) needs 4 sets meager:** `π_V(Z_reg)`,
  `π_V(Z∩{H≡0}∩W_surj)` [the "ZH0surj" piece], `B_CaseB`, `B_H0res` — via
  `prop:dimZ`+`lem:smooth-chart-meager`, Appendix I (`cor:caseBmeager`), Appendix H
  (`prop:h0res-meager`) respectively.
- **Transversality stubs analyzed** (`Parametric_Transversality_Euclidean_Base`,
  L369 `charts_core_2d`, L1015 meager-stub): stub 2 = stub 1 (Lindelöf assembly of the
  proven single-point keystone) + rank-deficient-image-negligible + the
  already-proved `meager_negligible_closed_cover`. So **`lem:smooth-chart-meager` is
  the single highest-leverage lemma**: it unblocks the transversality pipeline
  (→ `prop_regzero`, `prop_foldzero`) *and* `prop:dimZ` facts 1&2.
- The Sard theory already provides `negligible_singular_image_2n` (rank-deficient
  C¹ ⟹ negligible image) and the library `baby_Sard`. Gap to *meager*:
  negligible alone ≠ meager; need the σ-compact exhaustion (closed-negligible pieces
  ⟹ meager). That is the **next concrete target**.

Full dependency-ordered plan (Tiers 0–4) written to `APPENDIX_PLAN.md`. No theory
changes this entry — map + plan + STATUS/diary/memory only; build unchanged.

## 2026-05-29 (cont.) — P1.6 COMPLETE: regular stratum is open AND dense (real-analytic)

`DM_paper_open_dense_surjective` (sorry-free, `Applied_Math_Nonemptiness`
`BUILD_EXIT=[0]`): for any open `V :: ((real^2)^6) set`,
\[
  \exists U.\ \text{open } U \wedge U \subseteq V \wedge V \subseteq \overline{U}
            \wedge (\forall x\in U.\ \mathrm{surj}\,(D_x M\_paper(x, c0\_paper))).
\]
Take `U = V ∩ {x. m*(x) ≠ 0}`. **Openness** is the C¹ half (`m*` continuous →
`{m*≠0}` open). **Density** is the real-analytic half: `m*` is `rline_entire`
(`rline_entire_m_star`) and nontrivial (`m*(x0)=det bigJ≠0`), so `{m*=0}` is
nowhere dense (`nowhere_dense_m_star_zeros` via the `lines_entire_slice_nowhere_dense`
engine); hence `{m*≠0}` is dense and, `V` being open,
`V ⊆ closure(V ∩ {m*≠0})` (`open_Int_closure_subset`). This is exactly
`rank_lower_semicont_open_dense_propagation` made **unconditional** for the
concrete moment map — and it required the real-analyticity (C¹ alone gives only
openness, as flagged earlier; the generic lemma is false under C¹).

**How the analyticity went through (for the paper):** each entry of the
transported Jacobian `matrix(MJx x)` is `Re`/`Im` of a moment-derivative component
`Moment_Map.DM_paper_x x c0 h $ m`, which is `cline_entire` — phase/`d_phase` are
`cis` of bounded-linear forms, and the `of_real` polynomial weights are
`cline_entire` via `rline_entire f ⟹ cline_entire (of_real∘f)`. The determinant
`m*` is then `rline_entire` (`rline_entire_det_fun`: `det` = sum-of-products of
entries, closed under the `rline_entire` algebra). The whole density argument
reused the **existing** `cline_entire`/`rline_entire`/`lines_entire` engine
(array-factor branch) — no new analytic foundations needed.

**Traps hit this session (autonomous run):** (i) the stale **local
`Nonemptiness_Paper.DM_paper_x`** shadows `Moment_Map.DM_paper_x` (which `MJx`
uses) — qualify `Moment_Map.DM_paper_x`; the two are definitionally equal. (ii)
schematic-binder type trap recurred twice (`w` in `rline_entire_transC_comp`, `V`
in `DM_paper_open_dense_surjective`) — pin types. (iii) engine `lines` hyp is meta
`⋀a v`; supply via a local `have … for a v` (or `rule_format`), not the object
`∀` from `rline_entire_def`.

**Next — P1.7:** feed `DM_paper_open_dense_surjective` to the `ZH0surj` branch:
on the open-dense regular stratum, transversality/Sard ⟹ `meager (ZH0surj ∩ V)`,
discharging that hypothesis of `prop_regnonzero`. (This pulls in the Case-B / H≡0
appendix inputs — the larger remaining piece.)

---

## 2026-05-29 (cont.) — P1.6 (openness): the surjective stratum is open

The first half of P1.6 is done (sorry-free, `Applied_Math_MomentJac` `BUILD_EXIT=[0]`),
in `MomentJac/Moment_Jacobian.thy`:

- `MJx x = transC ∘ (DM_paper_x x c0_paper) ∘ transD` (the transported Jacobian at
  a *general* configuration `x`) and `m_star x = det (matrix (MJx x))`.
- `surj_iff_m_star`: `surj (DM_paper_x x c0_paper) ⟷ m_star x ≠ 0` — a real
  `12×12` endomorphism is surjective iff injective iff its determinant is nonzero
  (`det_nz_iff_inj` + the bijective transports). `m_star_x0_nonzero`:
  `m_star x0_paper = det bigJ ≠ 0`.
- `continuous_m_star`: `m_star` is continuous (`continuous_on_det_fun`, a small
  general lemma: `det` of a continuously-varying matrix; the entries are continuous
  via `continuous_on_DM_paper_x_vec` + `bounded_linear transC`).
- `open_surj_stratum`: `open {x::(real^2)^6. surj (DM_paper_x x c0_paper)}`
  (= `{x. m_star x ≠ 0}`, open by `open_Collect_neq`). This is the C¹
  (lower-semicontinuity-of-rank) half.

**Lesson worth a footnote (the schematic-type trap).** `open_surj_stratum` first
refused *every* closing tactic (`simp`, `unfolding`, `subst`, `metis` all "failed
to apply") on what looked like a trivial set rewrite. The cause was **not** the
tactics: the statement `open {x. surj (DM_paper_x x c0_paper)}` leaves the bound
`x` at a *schematic* type `planar^'n` (nothing pins `'n`), whereas the supporting
facts (`m_star`, `surj_iff_m_star`, forced through `transD : real^12 → (real^2)^6`)
are all at the concrete `(real^2)^6`. So the goal's set and the rewrite's LHS
differ by `'n` vs `6` and nothing unifies. Pinning the binder —
`open {x::(real^2)^6. …}` — fixed it instantly. (Same family as the 05‑27 rule:
*annotate a binder whose type is only pinned through a function applied to it.*)

**Next — P1.6 (density):** `m_star` is `rline_entire` (its matrix entries are
coordinate-polynomials × `cos`/`sin` of the steering form) and nontrivial
(`m_star_x0_nonzero`), so `{m_star = 0}` is nowhere dense (the
`lines_entire_slice_nowhere_dense` engine) ⟹ the surjective stratum is *dense*.
Combined with openness this gives `rank_lower_semicont_open_dense_propagation`
unconditionally; then P1.7 assembly → `meager (ZH0surj ∩ V)` → `prop_regnonzero`.
(Layering of the `rline_entire` engine vs the HMA-free context still to be decided.)

---

## 2026-05-29 (cont.) — P1.5 COMPLETE: the Jacobian identification `D_xM_paper(x0,c0) = (*v) bigJ`

The keystone connection between the abstract matrix `bigJ` and the *actual*
moment-map function is proved (sorry-free; `Applied_Math_MomentJac` `BUILD_EXIT=[0]`),
in `MomentJac/Moment_Jacobian.thy`:

- `matrix_MJ : matrix MJ = bigJ`, where
  `MJ = transC ∘ (DM_paper_x x0_paper c0_paper) ∘ transD`.
- `MJ_eq_bigJ : MJ = (*v) bigJ`  (via `(*v)(matrix MJ) = MJ` for linear `MJ`).
- `surj_DM_paper_base : surj (DM_paper_x x0_paper c0_paper)` — surjectivity of the
  genuine moment-map derivative at the base point, transferred from `bigJ_surj`
  through the bijective transports.

So `bigJ` is **not just a matrix of numbers**: it is the Fréchet derivative of the
real moment map `M_paper` at the canonical base configuration, in the
`(Re,Im)` × `(u_n,v_n)` coordinates fixed by `transC`/`transD`.

**Proof shape (for the paper):** twelve per-column lemmas `MJ_col1..MJ_col12`,
each `MJ (axis j 1) = (χ i. bigJ$i$j)`. For basis direction `axis j 1` the moment
sums (`sum_6`) collapse to the single base point that direction touches; the
surviving term is `weight · cis(-u_n)` whose `Re`/`Im` (via `base_trig_values`,
the sixth-roots-of-unity values) match `bigJ`'s explicit entries. Shared simp
bundle `MJ_col_simps`; each column discharged by a bounded `exhaust_12[of i]` +
`elim disjE; simp_all`. The second-moment rows (M₁₁/M₁₂/M₂₂) need polynomial-in-π
algebra, supplied by `power_divide`/`power_mult_distrib` (e.g. `9·(π/3)² = π²`).
`matrix_MJ` assembles the columns (case split on `j`); `MJ_eq_bigJ` then uses
`(*v)(matrix MJ) = MJ`; `surj_DM_paper_base` writes
`DM_paper_x x0 c0 = transC_inv ∘ MJ ∘ transD_inv` and composes surjections.
(Engineering: `DM_paper_x_components` and `cos pi`/`sin pi` are already `[simp]`, so
omitted from the bundle to avoid duplicate-rewrite warnings.)

**Next — P1.6 (density) then P1.7 (assembly):**
- *Immediate:* `det (matrix MJ) = det bigJ = -(5·π⁸)/3 ≠ 0` (one line from
  `matrix_MJ` + `bigJ_det_nonzero`) — the regular base point is a *non-degenerate*
  one.
- *P1.6:* the surjective stratum `{x. surj (DM_paper_x x c0)}` is **open and dense**.
  Define the minor `m*(x) = det (matrix (transC ∘ DM_paper_x x c0 ∘ transD))`;
  `m*(x0_paper) = det bigJ ≠ 0` (nontrivial) and `m*` is `rline_entire` (its
  entries are coordinate-polynomials × `cos`/`sin` of the steering form — the
  `rline_entire_coord`/`_cos_inner`/`_sin_inner` base cases + closure). Then
  `lines_entire_slice_nowhere_dense` gives `{m*=0}` nowhere dense ⟹ `{m*≠0}`
  open dense ⊆ surjective stratum. **Layering note:** `rline_entire` lives in
  `Nonemptiness_Paper`; the minor involves nested-vec transports (must stay in the
  HMA-free context), so decide where the density proof lives (likely move the
  `rline_entire` engine into a lower heap theory, or do the density step carefully).
- *P1.7:* assemble `DM_paper_open_dense_surjective` → `meager (ZH0surj ∩ V)` →
  `prop_regnonzero`; then re-import `Moment_Jacobian` into `Nonemptiness_Paper`.

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

### Session architecture: the edited theory must not be in its own logic heap

`Moment_Jacobian` is where the Jacobian identification (`D_x M_paper(x0,c0) = (*v) bigJ`)
is being actively developed, so it cannot sit in the heap we load to edit it. Moved
it to its **own directory + session** `Applied_Math_MomentJac in "MomentJac"`,
parented on `Applied_Math_BlockDet`. Also moved the base configuration
(`x0_paper`, `c0_paper`, their `*_entries`/`*_values` lemmas, `sqrt3_sq`,
`base_trig_values`) out of `Nonemptiness_Paper` into `Moment_Jacobian`, since the
identification needs them in this clean (HMA-free) context and `Moment_Jacobian`
cannot import `Nonemptiness_Paper`. `Nonemptiness_Paper` no longer imports
`Moment_Jacobian` during development (it used none of those names yet); it will be
rewired once the identification is proved.

- **Edit** `MomentJac/Moment_Jacobian.thy` with `-l Applied_Math_BlockDet`
  (deps from the heap, the theory itself live — fast, no staleness).
- **Batch-verify** with `isabelle build … Applied_Math_MomentJac` (~3 s on the
  prebuilt BlockDet heap).

Verified: `Applied_Math_BlockDet` (clean, no `Moment_Jacobian`) +
`Applied_Math_Nonemptiness` (decoupled) + `Applied_Math_MomentJac` all
`BUILD_EXIT=[0]`. (ROOT-comment trap re-logged: `(*v)` inside an Isabelle `(* … *)`
comment opens a nested comment and breaks parsing — write it without the `(*`.)

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
## 2026-05-30 (robust set, Part 1c) — F has nonempty interior (ball_inside_F)

Proved the remark `ball_inside_F`: for a strictly feasible point x* (all spacings
> dmin, N(x*) < dnull, pmin < P(x*), ||x*|| < R), there is rho>0 with ball x* rho subset F.
Route: the open set U = {strict spacing} cap {N<dnull} cap {pmin<P} cap ball 0 R
contains x* and U subset F; openE gives the ball. Global helpers added:
cmod_af_le_card (|A| <= N via norm_sum + |cis|=1), Upow_nonneg, and Upow_le_max
(P <= |e(t0)|^2 N^2 everywhere, so the upper power bound never binds). Gotchas:
Upow_nonneg/Upow_le_max cited with [OF ...] hit OF multiple-unifiers on g(omega);
pin g and omega via [where g=g and omega=...] (or inline via mult_nonneg_nonneg).

## 2026-05-30 (robust set, Part 2a) — X_robust, X_0, F_0 defined (1-D phi-derivatives)

Defined the robust sets faithfully to D_edit_May18 (L716/X0def/F0). KEY: D_edit uses
the 1-D phi-derivative d_phi U and H = d^2_phi U (NOT the multi-dim gradient), so we use
HOL's deriv (no Higher_Differentiability/Smooth_Manifolds import needed) and |.| is the
1-D norm. angle2 t p = (t,p); Usec = phi-section phi |-> U(x,(t0,phi)); dphiU = deriv Usec;
HU = deriv (deriv Usec). Xrobust cvec g t0 p0 eps kappa = {x : kappa <= |dphiU| on sphere p0 eps};
X0 cvec g t0 p0 Omega xi kappa eps = {x in Xrobust : xi <= |dphiU|+|HU| on Omega - ball p0 eps};
F0 ... xi kappa eps = Ffeas ... (angle2 t0 p0) ... INT X0 ... (= F INT X0). xi,kappa,eps explicit.
Typechecks. NEXT: the conjecture EX xi kappa eps. F0 ... xi kappa eps != {}.

## 2026-05-30 (the through-line) — Phi tied to U_cart; what the determinant is FOR

CRITICAL ARCHITECTURE NOTE (for the planned clean rebuild). The whole proof's spine,
made explicit:
- The radiation pattern is `U_cart cvec gain x w = gain w * |A_cart cvec x w|^2`
  (concrete, in Nonemptiness_Paper.thy, with derivatives dA_cart/dU_cart and
  has_derivative_U_cart / differentiable_U_cart already proven).
- The paper's bad-point map (tex L516) is Phi = (d_c1 U, d_c2 U, det Hess U). So
  Phi=0 <=> grad U = 0 (critical point) AND det Hess = 0 (degenerate). I.e. Phi=0
  picks out exactly the DEGENERATE critical points -- the configs excluded from X0.
- THE DETERMINANT'S PURPOSE: lem:Msurj (the 12x12 bigJ_det != 0, and the J5 det
  = -32 g^5 a^5 != 0 = lem:block, and lem:3x3) prove the moment map M (config ->
  gradient+Hessian data) is a SUBMERSION. Chain rule D_x Phi = D_M F . D_x M then
  gives rank D_x Phi = 3 on Z_reg, so {Phi=0} is codim-3 (prop:dimZ), hence its
  projection to config space is MEAGER (lem:smooth-chart-meager). => a generic
  feasible x has NO degenerate critical point => x in X0. The determinant is the
  engine that makes nondegeneracy GENERIC instead of assumed.

NEW (Nonemptiness_Robust.thy): defined gradU, HessU, Phibad FROM U_cart via
frechet_derivative (HOL-Analysis, no Smooth_Manifolds) -- so the set finally depends
on the real function. Stated the explicit obligation `Phi_bad_meager`: the set
{x in V. EX w. Phibad..=0 & A_cart..!=0} is meager (= prop:dimZ payoff of the
determinant). This is the consumer the appendix's Bregnonzero meagerness reduces to.

OPEN TENSIONS to fix in the clean rebuild:
- F0 (from D_edit) uses the 1-D phi-derivative; Phi/determinant use the 2-D gradient/
  Hessian. Pick ONE formulation (the 2-D Phi connects to the determinant; reconcile
  D_edit's 1-D X0 to it, or restate X0 via the 2-D Hessian).
- F0_nonempty still has assumptions (feas/cont/Ocpt/reg). These must be DISCHARGED:
  cont <- has_derivative_U_cart; Ocpt <- closed/bounded; feas <- explicit xbar;
  reg <- Phi_bad_meager + Baire (odd_N_nonemptiness). The assumption-free statement
  is the goal.
- F0_ne (`x0 in S ==> S != {}`) is TRUE but `blast` HANGS on the 16-arg F0 term
  (timeout, not failure). Fix later by abbreviating the set to a short name before
  the ne step (define S == F0...). Currently sorry'd.
- Gradient/Hessian of U: explicit formulas are in Appendix 2 of the .tex (to prove
  Phibad equals the appendix moment functions Phi1m/H11m/...).

## 2026-05-30 (Hessian via Higher_Differentiability_Multi) — gradU/HessU use nabla/nabla^2

Per direction: gradU/HessU now use the canonical grad_fun/hess_fun from
Higher_Differentiability_Multi (notation \<nabla>, \<nabla>\<^sup>2), NOT a hand-rolled
frechet_derivative Hessian. So gradU cvec gain x = \<nabla> (U_cart cvec gain x) and
HessU cvec gain x = \<nabla>\<^sup>2 (U_cart cvec gain x) (i.e. the THE H with
\<nabla>f has_derivative (\<lambda>v. H *v v)). Phibad = (\<nabla>U_1, \<nabla>U_2, det \<nabla>\<^sup>2U) built from these.

ROOT: Applied_Math_Appendix now `sessions Applied_Math_HigherDiff`, and
Nonemptiness_Robust imports "Applied_Math_HigherDiff.Higher_Differentiability_Multi".
The Smooth_Manifolds merge into the Munkres/JNF/HMA heap WORKS (first build ~4min,
incremental ~1m47s). NOTE for clean rebuild: this is a big heap; consider whether
the robust layer should be its own session.

GOTCHA: in the merged JNF+HMA+Smooth_Manifolds session, `vec_eq_iff` is ambiguous
(JNF Matrix.vec vs HMA ^), so `simp add: vec_eq_iff` makes no progress on real^3
goals. Phibad_zero_iff (trivially true: Phi=0 <-> its 3 components vanish) is
currently sorry'd pending HMA-qualification (Finite_Cartesian_Product.vec_eq_iff)
or a component-wise proof. 4 sorries total in Robust: 2x F0_ne (blast hangs on
16-arg term), Phibad_zero_iff (vec_eq_iff), Phi_bad_meager (the determinant payoff
obligation).

## 2026-05-31 — Capstone restructure: assumption-free F0_nonempty, 2-D Φ, Ω defined+compact

### What we achieved this session
The capstone theory `Appendix/Nonemptiness_Robust.thy` now has the RIGHT SHAPE end-to-end
(builds green, quick_and_dirty; incremental ~1m, full heap ~4m on first Smooth_Manifolds merge):

1. **Hessian via Higher_Differentiability_Multi.** `gradU cvec gain x = ∇ (U_cart cvec gain x)`
   and `HessU cvec gain x = ∇² (U_cart cvec gain x)` (the canonical grad_fun/hess_fun, NOT a
   hand-rolled frechet_derivative). ROOT: Applied_Math_Appendix now `sessions
   Applied_Math_HigherDiff`; the Smooth_Manifolds merge into the Munkres/JNF/HMA heap WORKS.

2. **2-D Φ formulation (not the 1-D ∂_φ).** Replaced dphiU/HU with:
   - `Xrobust cvec g ctr ε κ = {x. ∀ω∈sphere ctr ε. κ ≤ norm (gradU cvec g x ω)}`
   - `X0 cvec g ctr Ω ξ κ ε = {x∈Xrobust. ∀y∈Ω-ball ctr ε. ξ ≤ norm(gradU…)+sigma_min(HessU…)}`
   - `sigma_min H = (INF v∈sphere 0 1. norm (H *v v))` (operator-norm char.; sigma_min_nonneg,
     sphere01_ne proven). This is the σ_min(H) > 0 ⟺ det∇²U ≠ 0 nondegeneracy the determinant
     secures. Matches D_edit L1281/L1288 exactly.

3. **Ω is DEFINED and PROVEN compact (no assumption).** `Omega ctr = cbox (ctr - vector[π/2,π])
   (ctr + vector[π/2,π])` = the paper's box [θ0±π/2]×[φ0±π] (D_edit L1253). `Omega_compact`
   (compact_cbox) and `Omega_minus_ball_compact` (compact_Int_closed + closed_Compl[OF open_ball])
   are real lemmas. F0_nonempty now carries ONLY the hypothesis `c6: 6 ≤ CARD('n)`.

4. **Φ moved upstream of the capstone.** Phibad / Phibad_zero_iff / Phi_bad_meager now sit
   BEFORE regular_feasible_witness + F0_nonempty (they previously dangled after the theorem,
   feeding nothing). So the determinant payoff is structurally upstream now.

5. **F0_nonempty is assumption-free and its margin extraction is fully proven.** Given a regular
   feasible witness, Weierstrass gives κ = min‖∇U‖ on the sphere and ξ = min(‖∇U‖+σ_min) on the
   annulus, both > 0, and x0 ∈ F0. The regularity/feasibility/continuity that the OLD version
   ASSUMED are now packaged as ONE obligation `regular_feasible_witness` (to be proved from
   Phi_bad_meager + Baire), NOT hypotheses of the theorem.

### Current sorries in Nonemptiness_Robust.thy (6) — by nature
- L324 `Phibad_zero_iff`  — TRIVIAL (Φ=0 ⟺ 3 components 0); needs HMA-qualified vec_eq_iff
  (Finite_Cartesian_Product.vec_eq_iff) in the merged JNF+HMA+Smooth_Manifolds session.
- L336 `Phi_bad_meager`   — THE DEEP OBLIGATION (determinant payoff: lem:Msurj ⟹ Z_reg codim-3
  ⟹ projection meager). Fed by the Capstone/MomentJac/BlockDet chain.
- L378 `regular_feasible_witness` — bundles Phi_bad_meager + Baire + C²-continuity of ∇U/σ_min.
- L398 witness `obtain` inside F0_nonempty — MECHANICAL (just instantiate regular_feasible_witness
  [OF c6]; the positional `of` mis-ordered fixes-vs-occurrence; use `where` or let blast match).
- L425, L456 the two `F0 … ≠ {}` steps — MECHANICAL (x∈S ⟹ S≠{} via mem_imp_ne_empty; blast
  hangs on the 15-arg term, plain `by (rule mem_imp_ne_empty)` should work — RETRY that).

(Upstream: Nonemptiness_Capstone.thy still 10 sorries; Nonemptiness_Regnonzero_Appendix.thy 1.)

### How we move forward (clean rebuild plan)
The through-line is now legible: `determinant (bigJ_det/J5/lem:3x3) → lem:Msurj → prop:dimZ →
Phi_bad_meager → regular_feasible_witness → F0_nonempty`. When we START OVER in the new focused
directory, mirror THIS order: U_cart + ∇/∇² first, then sigma_min + Φ + Ω(box), then
Phi_bad_meager (the meagerness keystone), then the Baire witness, then the assumption-free
capstone LAST. Keep the robust layer possibly its own session (the Smooth_Manifolds heap is big).

## 2026-05-31 (σ-discharge RESOLVED) — parametric_transversality_meager_euclidean_stub proved

The "stub 2" σ-compactness blocker (12+ failed approaches, see prior entry) is
CLOSED. `parametric_transversality_meager_euclidean_stub` is now sorry-free;
Applied_Math_Nonemptiness + Applied_Math_Appendix build green (BUILD_EXIT=0,
~21s + 34s incremental). Committed 0a124c2, pushed.

ROOT CAUSE (finally diagnosed by turning on `declare [[show_types,show_sorts]]`
and noting that `insert sig, assumption` FAILED — and `assumption` always closes
`A ⟹ A`, so `sig` was provably NOT the goal despite printing identically): the
monolithic `assume H: "A ∧ B ∧ C ∧ D"` + `note sig = conjunct2[OF conjunct2[OF
conjunct2[OF H]]]` left a `sig` term the matcher silently rejected, and
`blast`/`auto`/`meson` hung/failed because the whole giant `H` (incl. the `?bad ⊆
…` comprehension) sat in the proof context and exploded the search.

THE FIX (one structural change): `proof (elim exE)` → `proof (elim exE conjE)`
with FOUR directly-named assumptions `cover/der/rk/sig` (no monolithic `H`, no
`conjunct` projection). With a clean context the σ goal closes via
`using sig by blast`. Generalizable lesson saved to memory
(elim-exe-conje-named-assumptions): destructure multi-conjunct existentials with
`elim exE conjE` + named conjuncts, never `assume H` + projection.

Also landed this session: the meager analog `meager_critical_values_from_charts`
(σ-compact pieces → `baby_Sard` negligible → closed ⇒ nowhere dense → meager
countable union), and the σ-compactness conjunct threaded through the core lemma
`regular_zero_set_projection_charts_core_2d` (still the lone real `sorry` in the
Base file, L371 — the IFT/regular-value chart cover, the next deep target there).

## 2026-05-31 (Robust mechanical sweep) — F0_nonempty sorry-free; Phibad_zero_iff proved

Cleared 4 sorries in `Appendix/Nonemptiness_Robust.thy` (6 → 2). All builds green
(Applied_Math_Appendix BUILD_EXIT=0); committed 8b20273 + fba5044, pushed.

1. **Witness obtain (was sorry).** `using regular_feasible_witness[OF c6] by blast`
   failed because `blast` had to BOTH eliminate the 2-var ∃ AND convert the lemma's
   bounded `∀ω∈sphere. P` into the `⋀ω. ω∈sphere ⟹ P` meta-form of the `where`
   clauses. Fix: state the `where` clauses in the lemma's bounded-∀ form (so blast
   does pure exE+conjE), and switch the 2 downstream uses `rsph[OF ωm]`/`rO[OF ym]`
   to `bspec[OF rsph ωm]`/`bspec[OF rO ym]`.

2. **Both `F0 … ≠ {}` steps (were sorry).** `by (rule mem_imp_ne_empty)` failed on
   terms that print IDENTICALLY. ROOT CAUSE (found via `declare [[show_types,
   show_sorts]]`): `F0`'s result type `(planar^'n) set` has 'n NOT pinned by its
   value args (phantom). The bare `hence "F0 … ≠ {}"` gave `{}` a FRESH type var
   `'a`, while `this : x0 ∈ F0 …` pinned it to the real 'n — so
   `mem_imp_ne_empty[OF this]` (a `(planar^'n) set ≠ {}`) couldn't match the goal's
   `(planar^'a) set ≠ {}`. Fix: `hence "F0 … ≠ ({}::(planar^'n) set)"`. Saved to
   memory (phantom-result-type-pin-empty-set). SAME show_types diagnostic cracked
   both this and the σ-discharge — the lesson: when rule/OF/fact fail on
   identical-printing terms, turn on show_types/show_sorts FIRST.

3. **Phibad_zero_iff (was sorry, "trivial").** `Φ = vector[g₁,g₂, H₁₁H₂₂−H₁₂²]`, so
   `Φ=0 ⟺` all 3 components vanish: `Finite_Cartesian_Product.vec_eq_iff`
   (HMA-qualified to dodge the JNF/HMA ambiguity in the merged session) + `forall_3`
   + `vector_3` for the real^3 side; `forall_2` for `gradU = 0 ⟺ gradU$1=0 ∧ gradU$2=0`;
   `algebra_simps` for `det = 0 ⟺ H₁₁H₂₂ = H₁₂²`.

Robust now has 2 sorries, both DEEP: `regular_feasible_witness` (Phi_bad_meager +
Baire + C²-continuity bundle) and `Phi_bad_meager` (the determinant payoff:
lem:Msurj ⟹ Z_reg codim-3 ⟹ projection meager). The capstone shape is complete;
what remains there is genuine mathematics, not plumbing.

## 2026-05-31 (definition reconciliation, part 1) — gradU bridged to the proven dU_cart

User flagged (correctly) that Robust's gradU/HessU (abstract ∇/∇² from
Higher_Differentiability_Multi) compete with the explicit, PROVEN derivative
dU_cart + has_derivative_U_cart in Nonemptiness_Paper, and that the capstone
`fixes cvec g` abstractly — divorced from the concrete physical wavevector and the
concrete moment map (M_paper/bigJ) the determinant is about.

DIAGNOSIS (no NAME clash — Robust imports U_cart/A_cart/dU_cart, defines fresh
gradU/HessU/Phibad). Two real semantic disconnects:
 (1) ∇/∇² track never bridged to the dU_cart track. CRUCIAL: `\<nabla> f x = THE g.
     GRAD f x :> g`, so gradU is a THE over a FALSE predicate (junk) unless U_cart
     is differentiable in ω — which needs cvec, gain differentiable. So for
     arbitrary fixed cvec/g, gradU/HessU are meaningless and the capstone is vacuous.
 (2) Phi_bad_meager/regular_feasible_witness/F0_nonempty `fixes cvec g` — the
     determinant facts (bigJ_det≠0, m_star x0_paper≠0 at c0_paper=(1,0)) can't
     discharge them because nothing ties this abstract cvec/x to x0_paper/M_paper.
     This is SYSTEMIC: Bregnonzero and thm_final's conditional form defer concrete
     cvec too.

FIX part 1 (committed 07a1b5e): `gradU_explicit` — under (cvec has_derivative dc)
(gain has_derivative dgain) at ω, has_derivative_U_cart + has_derivative_to_gradient
+ grad_fun_eq give
  gradU cvec gain x ω = (∑i. dU_cart cvec dc gain dgain x ω (axis i 1) *⇩R axis i 1).
gradU is now the genuine gradient of the real U_cart. (Gotcha: has_derivative_U_cart
leaves x schematic — pin via [where x=x] or simp can't match the local x.)

REMAINING reconciliation gaps:
 - HessU bridge needs a SECOND derivative of U_cart; Paper only has first-order
   (dU_cart). Must prove has_derivative (dU_cart …) … or a Hessian lemma. New work.
 - The deep one: tie Phibad's components to M_paper's moments (Appendix-2 explicit
   gradient/Hessian formulas) at the concrete steered cvec, so bigJ_det/m_star
   discharge prop:dimZ ⇒ Phi_bad_meager. This IS the central remaining appendix math.
 - Decide the concrete cvec/gain to instantiate the capstone at (candidates in
   Paper: cvec0 = beam-lift steered, or cvec_steered ∘ kvec). PENDING user steer.

## 2026-05-31 (connecting the determinant, part 2) — chain-rule keystone + the ∂ω/∂c discovery

User directive: final results must be about OUR concrete function (general theorems
OK as intermediates); connect the determinant to the meagerness argument.

Mapped the FULL chain from the tex (nonemptiness_unified_singlefile_complete.tex):
 - Concrete cvec = beam-lift steered wavevector: c(θ,φ) = (Δkx+Dx·Δkz, Δky+Dy·Δkz),
   = Isabelle `cvec0 ω0 ωs` (Paper L942). NOTE: cvec0 : ... ⇒ real×real, but U_cart
   wants angle⇒real^2 — needs a vector[fst,snd] adapter.
 - Determinant chain (tex prop:dimZ / lem:Msurj / lem:3x3):
     bigJ_det = -5π⁸/3 ≠ 0  (PROVEN: bigJ_det, m_star_x0_nonzero, surj_iff_m_star)
       ⟹ surj(D_x M) on open-dense W_surj  (lem:Msurj = DM_paper_open_dense_surjective, PROVEN)
     D_M F has rank 3  (lem:3x3/lem_block, PROVEN in Regnonzero_Appendix: deriv minors = ±2ga)
     chain rule D_x Φ = D_M F · D_x M  ⟹ rank D_x Φ = 3  ⟹ Z_reg codim 3 ⟹ proj meager.
 - Φ in moment coords (tex Appendix-2) = the appendix's Phi1m/Phi2m/H11m/H12m/H22m
   (Regnonzero_Appendix L54-78): Φ1=g1(a²+b²)+2g(b1 a−a1 b), etc. ALREADY DEFINED there.

DOWN-PAYMENT (committed 64e38ea): `rank_matrix_comp_surj` — surj((*v)B) ⟹
rank(A**B)=rank A. The pure-LA core of the chain-rule step: this is EXACTLY where the
determinant enters (D_x M surjective ⟹ rank D_x Φ = rank D_M F = 3).

CRUCIAL DISCOVERY (a real disconnect, beyond the user's original worry):
 Robust's `Phibad` uses gradU = ∇_ω U (ANGLE derivative; U_cart depends on ω through
 BOTH gain ω and cvec ω). The appendix's Φ and the WHOLE determinant machinery use
 ∂_c U (WAVEVECTOR derivative, c free). These DIFFER by the cvec Jacobian:
 ∇_ω U = Jcvec^T ∇_c U (+ gain-ω terms). They agree as critical/degenerate sets only
 where cvec is a local diffeo, i.e. det Jcvec ≠ 0 — which is exactly `det_Jcvec`
 (PROVEN, Paper L2933) on the regular/fold stratum. So connecting Phibad to the
 determinant needs a change-of-variables bridge through Jcvec, OR reformulating the
 bad set in c-coordinates and pulling back. The physical final result is in ω (the
 pattern's look-direction), so c-coords are the computational intermediate.

REMAINING to connect determinant → Phi_bad_meager (about our function):
 (a) HessU 2nd-derivative bridge (Paper only has 1st-order dU_cart). [prereq for (b)]
 (b) Phibad components = Phi1m/H11m/... in c-coords (via gradU_explicit + moment algebra).
 (c) ∂ω↔∂c change of variables via Jcvec (det≠0 = det_Jcvec).
 (d) the chain-rule rank-3 + codim-3 chart cover + projection-meager (needs an ℝ³
     analog of regular_zero_set_projection_charts; the ℝ² version is the lone Base sorry).
 (e) instantiate cvec := cvec0-adapter, gain := |e|², discharge the cvec≠0 / diff hyps.

## 2026-05-31 (dropping the differentiability assumption, step 1)

User question: is gradU differentiable everywhere — should we prove it and drop the
HessU assumption? Answer: FALSE for arbitrary cvec/gain (e.g. cvec ω = (|ω₁|,0) makes
U non-differentiable, gradU a junk THE), TRUE for our concrete function (cvec0 = sin/cos
with CONSTANT lift coeffs Dx,Dy — denominator cosθs−cosθ0 is a fixed constant, no
ω-singularity; cis entire; gain=|e|² smooth ⟹ U_cart C^∞ ⟹ gradU C^∞). So the
assumption is exactly input-smoothness: it can't vanish while cvec/gain are arbitrary
fixed, but becomes a THEOREM once we use the concrete smooth function.

Plan to turn the assumption into a theorem (drop one level at a time):
  gradU-derivative assm ⟸ U_cart∈C² ⟸ cvec,gain∈C² ⟸ (concrete) cvec0,|e|² smooth.

STEP 1 done (user fixed HessU_explicit's `mg` to `by (simp add: linG)`; added
`gradU_has_derivative_of_C2`): under `Ck_on 2 (U_cart cvec gain x) U` and ω∈U,
`(gradU cvec gain x has_derivative (λv. HessU cvec gain x ω *v v)) (at ω)`. Via the
proven `Ck_2_imp_hessian_exists` + has_hessian_def + gradU_def/HessU_def. So gradU is
differentiable everywhere on the C² locus and HessU is the genuine Hessian there.

REMAINING drops (both tractable):
 - `cvec,gain ∈ C² ⟹ Ck_on 2 (U_cart cvec gain x) UNIV`: build via AFP Smooth.thy
   closure (higher_differentiable_on_{const,id,add,mult,inner,scaleR,sum,compose,
   uminus}) — U = gain·|A|², |A|²=inner A A, A=∑ cis(-(cvec·x_n)), cis via cos+i·sin.
   (Ck_on ⟷ higher_differentiable_on, line 227.)
 - concrete: cvec0-adapter (real×real→real^2) and |e|² are smooth ⟹ zero assumptions.

## 2026-05-31 (dropping the assumption, step 2: trig smoothness + the e-singularity)

Landed (green, Applied_Math_Appendix BUILD_EXIT=0):
 - `sin_cos_higher_differentiable_on`: sin, cos ∈ C^∞ on UNIV (real⇒real), mutual
   induction (sin'=cos, cos'=-sin; frechet_derivative via DERIV_sin/cos +
   has_field_derivative_imp_has_derivative + frechet_derivative_at). GOTCHAS: pin
   sin/cos to real⇒real in the STATEMENT (else polymorphic, facts won't match);
   bilinear closure lemmas (add/mult/scaleR/inner) take `open S` LAST; `for v::real`.
 - `cis_higher_differentiable_on`: cis ∈ C^∞ via cis = (λt. cos t *⇩R 1 + sin t *⇩R 𝗂).
 - `gradU_has_derivative_of_C2` (step-1 drop) committed earlier.

KEY: the concrete element pattern (tex D_edit L238) is e(θ,φ)=cos(π/2 cosθ)/sinθ
(half-wave dipole), gain=|e|². It is 0/0 at θ=kπ (sinθ=0, dipole nulls, L246).
 - Ω = cbox(ctr±[π/2,π]): θ-range [θ0±π/2], width EXACTLY π. By pigeonhole a closed
   width-π interval always contains a kπ. So Ω ALWAYS contains a dipole null (θ=0,π
   for broadside θ0=π/2). Hence gain∉C²(Ω) via the easy quotient-closure.
 - BUT the singularity is REMOVABLE: cos(π/2 cosθ) has a DOUBLE zero exactly at the
   SIMPLE zeros of sinθ, so e ~ (π/4)(θ-kπ) extends real-analytically; HOL's 0/0=0
   matches the limit. So e (hence gain, hence U_cart = gain·|A|² with cvec0 smooth)
   is genuinely C^∞ EVERYWHERE — U_cart∈C² on all of Ω, UNCONDITIONALLY. This drops
   the assumption fully for our function (user confirmed: prove removable smoothness).
 - THE CLEAN EXTENSION (found): using cos²(π/2 u)=(1+cos πu)/2 with u=cosθ,
     e²(θ) = (π²/4)·sinc(π(1-cosθ)/2)·sinc(π(1+cosθ)/2),   sinc z = sin z/z (entire).
   Verified at θ=π/2 (=1) and θ=0 (=0). This is the manifestly-smooth form of gain.
   No `sinc` in HOL/AFP, so the remaining KERNEL is one removable-singularity lemma:
   sinc ∈ C^∞ (sin t/t at 0), or e² C^∞ via holomorphic removable-singularity. NEXT.

## 2026-05-31 (REMOVABLE SMOOTHNESS PROVEN) — dipole gain |e|^2 is C-infinity everywhere

The removable-smoothness obligation the user asked for is COMPLETE. The half-wave
dipole element pattern e(theta) = cos(pi/2 cos theta)/sin theta (tex D_edit L238) is
0/0 at the poles theta=k*pi, but its gain |e|^2 is genuinely C-infinity everywhere.
Chain (all green, Applied_Math_Appendix, committed up to a87d0d1):

 1. hdo_real_deriv_chain (42e9ce2): a deriv-closed real family (J k)'=J(Suc k) is
    higher_differentiable_on UNIV to all orders. Reusable kernel.
 2. Jsinc k x = integral {0..1} (t^k cos(xt + k pi/2)) -- the k-th x-derivative of
    integral cos(xt) = sinc x, as an INTEGRAL (no 0/0). Jsinc_deriv via
    leibniz_rule_field_derivative; Jsinc_higher_differentiable_on via (1). (fd10376)
 3. Jsinc_0 (FTC): integral {0..1} cos(xt) = sinc x; gsinc_higher_differentiable_on:
    sinc = gsinc is C-infinity on UNIV. (6a0cf90)
 4. gdip t = (pi^2/4) gsinc((pi/2)(1-cos t)) gsinc((pi/2)(1+cos t)) -- the gain in
    manifestly-smooth sinc-factored form; gdip_higher_differentiable_on by composition
    (intro, not auto, to keep (pi/2)*x un-normalized). (91aae54)
 5. gdip_eq_edip_sq: gdip t = (edip t)^2 (= |e|^2), via product-to-sum + double-angle
    (sin A sin B = cos^2(pi/2 cos t) with A+B=pi, A-B=-pi cos t). (a87d0d1)

So |e|^2 is C-infinity on all of R, dipole nulls included -- NO assumption, NO domain
restriction. This is the removable extension the user pointed to ("U depends on e^2
which extends smoothly to zero at the poles").

GOTCHAS this arc: bilinear closure (add/mult/scaleR/inner) take `open S` LAST; pin
sin/cos to real=>real in lemma statements (else polymorphic, facts won't unify);
`also` only chains prev-RHS=next (don't interleave unrelated equations); simp
re-normalizes (pi/2)*(1-cos t) -> (pi-pi cos t)/2, so isolate +pi/2 via a standalone
cos(a+pi/2)=-sin a rewrite + `unfolding`; gsinc if-conditions normalize to 1∓cos t=0
so supply those (not just (pi/2)(1∓cos t)≠0).

REMAINING to fully drop the assumption for U_cart (now "downhill" -- composition of
proven-smooth pieces): (a) gain-of-omega (lambda om. gdip (om$1)) C-infinity on real^2;
(b) concrete cvec0 C-infinity; (c) assemble U_cart in C^2 (already have U_cart C^2 =>
gradU/HessU genuine via gradU_has_derivative_of_C2); (d) instantiate the capstone at
cvec0 + gdip-gain, zero assumptions.

### no_degenerate_to_sphere_annulus DONE (commit `595e046`) — Robust2 5→4 sorries
Morse argument, fully machine-checked. Reusable general lemma born: **`isolated_nondeg_zero`**
(a zero with injective Frechet derivative is isolated; `linear_inj_bounded_below_pos` +
`has_derivative_at_alt` o(.) bound). Then C={gradU=0}∩Omega compact+discrete⇒finite
(`compact_eq_Bolzano_Weierstrass`), dodge the finite radius set. Remaining leaves: the four
`meager_*_stratum` (Robust2) + the transversality engine `regular_zero_set_projection_charts_core_2d`
(Parametric) + dead `rank_semicont` (Paper).

### core_2d (the parametric-transversality keystone) PROVEN — 2026-06
The one genuinely-hard lemma the WHOLE theorem funnels through is done (verified in
`Appendix/Scratch_core2d.thy`, then inserted into `Parametric_Transversality_Euclidean_Base.thy`):
- `projection_deriv_not_inj` — kernel step: at a regular point with non-surjective slice,
  `(0,w)\<in>ker DG = range D\<phi>` (from `regular_value_local_chart`) \<Longrightarrow> `fst\<circ>D\<phi>` non-injective.
- `countable_chart_cover_with_Dphi` — mirror of `countable_chart_cover_of_levelset_2d` but
  keeps `D\<phi>` with `range D\<phi> = ker DG` (uses `regular_value_local_chart`, not the local-chart
  lemma that drops it); Lindelof subcover.
- `core_2d_strong` — assembles them: bad set \<subseteq> \<Union> chart-projection critical sets, each with
  rank-deficient derivative. STRENGTHENED with `derG`/`contG'` (the old `core_2d` sorry assumed
  only `reg0`, which is insufficient — that was a real statement gap); dropped the \<sigma>-compact
  clause (the Sard-finish `negligible_critical_values_from_charts` doesn't need it).
Lessons banked: [[type-every-bound-var-and-inspect-states]]. NEXT: rewire the base stubs
(`..._stub_2d`, `..._negligible_stub`, `..._meager_euclidean_stub`) to consume `core_2d_strong`
(thread `derG`/`contG'` through their assms), delete the old `core_2d` sorry, then Robust's
`parametric_transversality_meager_planar_config`, then the 4 strata.

### core_2d sigma-compact clause — dev complete in Nonemptiness-heap scratch (2026-06-09)
Killing the 90-min batch build mid-flight DELETED the Applied_Math_Appendix heap, so I moved
the dev loop onto the intact Applied_Math_Nonemptiness heap (it has regular_value_local_chart;
restated the 2 short kernel lemmas + regular_value_on def). Scratch: Appendix/Scratch_sc2.thy.
Proven there (all GREEN, ~30-50s evals):
- rel_closed_open_sigma_compact: open U, closed T => U cap T sigma-compact (setdist exhaustion;
  smt/divide_le_eq LOOP, fixed with mult_right_mono + linarith + metis-free).
- slice_linear: w |-> blinfun_apply F (0,w) linear (composition route).
- crit0_sigma_compact_helper: {u in U. ~surj(slice)} sigma-compact. Key: u|->det(matrix(slice))
  continuous (bounded_bilinear_blinfun_apply + det_2 + bounded_linear_vec_nth); ~surj<->det=0
  (det_nz_iff_inj + inj<->surj); closedin + closedin_closed[THEN iffD1] (NOT blast-search) + rel_sigma.
- cover (countable_chart_cover_with_Dphi): now EXPOSES open (U i).
- core_2d_strong: Crit0 redefined = {u in U i. ~surj(slice at charts i u)}; cover clause direct;
  rank via projection_deriv_not_inj (moved); NEW sigma-compact conjunct via the helper.
TRAP reconfirmed (logged): metis/blast/auto over big blinfun/det/matrix terms HANG (137, no error);
replace with explicit rule/[THEN iffD1]/structured chains. NEXT: bake Scratch_sc2's modified cover +
core_2d_strong into the base (Parametric_Transversality_Euclidean_Base) + rel_sigma/slice/helper;
ONE Appendix rebuild (heap is gone, rebuild needed anyway); then rewire the 3 stubs + the 4 strata.

### Stub rewire COMPLETE — base now ZERO sorrys (2026-06-10)
Rewired the 3 consumers onto core_2d_strong and DELETED the old
regular_zero_set_projection_charts_core_2d sorry (the base's last one):
- regular_zero_set_projection_charts_stub_2d, parametric_transversality_negligible_stub,
  parametric_transversality_meager_euclidean_stub: each gains fixes G' + assms derG/contG'
  (named openV/Vne/openOm/derG/contG'/reg0); rule swapped to core_2d_strong[OF openV openOm
  derG contG' reg0] (stub_2d projects away the sigma clause; negligible via stub_2d;
  meager destructures all 4 conjuncts incl sig).
- TRAP: OF-composing the rule-shaped derG leaves a residual guard
  (\<And>z. z\<in>V\<times>\<Omega> \<Longrightarrow> z\<in>V\<times>\<Omega>) \<Longrightarrow> CONCL. blast/auto swallow it, but chaining straight into
  proof (elim exE conjE) FAILS (elim can't see past the guard). Fix: interpose
  have core: "..." using ...[OF ...] by blast, then from core show ... elim.
SESSION-GRAPH CLARITY (false alarm resolved): the base IS compiled — Nonemptiness_Paper
imports Parametric_Transversality_Euclidean imports the base, so it lives in the
Applied_Math_Nonemptiness session; Robust reaches it via Paper. Crucially:
**base edits verify in the 41-SECOND Applied_Math_Nonemptiness build**, NOT the 32-min
Appendix build (that one only rebakes the heap for jEdit/Robust work).
Verified: BUILD_EXIT=0 Applied_Math_Nonemptiness (41s). Appendix rebake running.
NEXT: Robust's parametric_transversality_meager_planar_config via
parametric_transversality_meager_euclidean_stub (now sorry-free engine end-to-end),
then the 4 strata (M4 engine+regular_value_on_gradU_dip; M5 nowhere_dense_mstarg_zeros;
M6; M6b), then Capstone.


### Appendix rebake GREEN post-rewire (2026-06-10, user-run)
Computer crashed during the original rebake; working tree survived intact, rewire
committed as 2178245. User then ran the full Appendix rebuild in their terminal:
**Finished Applied_Math_Appendix (0:22:09 elapsed)** — first green build of the
whole chain against the zero-sorry base. STATUS CORRECTIONS vs previous entry:
- Robust.thy's parametric_transversality_meager_planar_config is COMMENTED OUT
  (lines 4464-4477) — so Robust has ZERO active sorrys; the lemma must be
  uncommented + proven, not just "resolved". Robust2 mentions it only in
  unchecked prose ({thm ...} without @), so the build doesn't care.
- Active sorry census: Robust2 4 (M4/M5/M6/M6b strata), Capstone 6
  (capstone_feasible, 4 branch_*_meager, capstone_X0_sound). Total 10 + the
  commented-out transport lemma.
- No Appendix consumer calls the rewired stubs yet (grep clean), which is why
  the signature change didn't break the rebake.
PERF NOTE: Robust line 4797 (sum_key inside the Sym2T steering-transport) ran
~187s — classic big-$-term parse hang (see dollar-notation memory); builds fine,
rewrite with vec_nth only if it becomes a bottleneck.
BUILD TRAP (cost me a killed build): `-D` SELECTS all sessions in the dir —
`-D … Applied_Math_Nonemptiness` also launches the 32-min Appendix build.
Use lowercase `-d` + explicit session name. Heaps live in DEFAULT
~/.isabelle/Isabelle2025-2 (the -ap-nonemptiness HOME_USER dir is empty).
NEXT (unchanged): uncomment+prove planar_config transport, then M4/M5/M6/M6b,
then Capstone.

### Sorry-dependency AUDIT of the heap chain (2026-06-10)
Question: does any sorried fact get INVOKED by a proof? Swept every .thy in the
build graph (incl. Imported_Munkres_Topology) for the 7 heap-resident sorries +
axiomatization/oops/attribute vectors. Results:
- rank_lower_semicont_open_dense_propagation (Paper:3826, sorry): NEVER invoked.
  All 4 other occurrences are prose cartouches (Moment_Map:650, BigJ:1123,
  Robust2:521, Paper:3781). Confirmed dead code (superseded by mstarg route,
  ed8cf5f).
- The 6 Capstone leaves: each invoked EXACTLY ONCE, all inside
  odd_N_nonemptiness (Capstone:142-176) — the flagship skeleton. That is the
  ONLY oracle-tainted theorem in the heap chain.
- odd_N_nonemptiness itself: invoked NOWHERE (Robust/Robust2 never cite it).
  Taint fully contained in Capstone. Its glue nonemptiness_from_meager_branches
  (Nonemptiness_Spine:217) is sorry-free.
- No sorried lemma carries [simp]/[intro]; no declare/lemmas aggregation cites
  one; zero axiomatization project-wide; the lone oops (Higher_Differentiability:2421)
  discards its statement (nothing enters the theory); Munkres import: 0 sorries.
- ORPHAN FOUND: Nonemptiness_Inventory.thy (10 sorries) — imported by NOTHING,
  absent from ROOT, NOT in any heap. Old TeX-statement checklist.
SLEDGEHAMMER BLACKLIST while proving against the Appendix heap (7 names):
capstone_feasible, branch_regzero_meager, branch_foldzero_meager,
branch_foldnonzero_meager, branch_regnonzero_meager, capstone_X0_sound,
odd_N_nonemptiness. Reject any found proof citing these.
ENDGAME NOTE (re-confirmed): Capstone's leaves can only be discharged from
strata that live DOWNSTREAM (Robust2) — final wiring must migrate strata
upstream of/into Capstone.
CLEANUP QUEUED: delete dead Paper lemma + orphan Inventory.thy (next entry).

### Deletions verified + Robust SPLIT into Robust1/2/3 with M11/M22 optimization (2026-06-10)
DELETIONS (queued in audit entry) now verified green and committed:
- Paper's rank_lower_semicont_open_dense_propagation (dead code) deleted along
  with its stale prose block; one cross-ref sentence rewritten. Paper: 0 sorrys.
- Orphan Nonemptiness_Inventory.thy deleted (10 vacuous "shows True sorry"
  placeholders; its one real result was a 1-line corollary of dxA_surj).
- BlockDet prose mentions of the dead lemma left stale DELIBERATELY (text-only;
  editing would invalidate the deep BlockDet..Appendix heap chain for prose).
TIMEOUT POST-MORTEM (12:15 failure, user-run): the four M11/M22 key/sum_key
commands elaborated CONCURRENTLY and GC-death-spiraled (even the morning green
run was 73% GC); 3600s session ceiling hit. Same source as the morning green
build => scheduling/GC, not logic. Lesson: threads=4 for these sessions.
THE SPLIT (user-directed; supersedes the old "stay on single Robust" decision):
- Nonemptiness_Robust1 = old Robust lines 1-4642 (through M2_moment_applyT),
  in NEW session Applied_Math_Appendix_Base (with Regnonzero + Capstone).
- Nonemptiness_Robust2 = M11_moment_applyT + M22_moment_applyT ONLY, proofs
  REWRITTEN with the define-t11/t12/t21/t22 trick (ported from the M12 template;
  statements unchanged). Lives in OWN DIR Appendix/Robust2/ — Isabelle forbids
  two sessions sharing a directory — as the sole theory of leaf session
  Applied_Math_Appendix.
- Nonemptiness_Robust3 = the active dev file formerly NAMED Robust2 (git mv,
  history preserved); imports Robust2; in NO session (jEdit-only, like
  Moment_Jacobian). Import chain: Robust3 -> Robust2 -> Robust1 -> Capstone.
NUMBERS: Appendix_Base 4:42 elapsed (Robust1 cumulated 703s vs old monolith
Robust 2664s); leaf Appendix 5s elapsed, M11+M22 cumulated 5.7s (was 2000s+,
or timeout). Total verify cycle for Robust2 edits is now ~5 SECONDS after a
one-time Base heap bake.
WORKFLOW: build `-o threads=4 Applied_Math_Appendix`; jEdit work:
-l Applied_Math_Appendix, open Robust3. NOTE: the commented-out planar_config
block now sits in Robust1 (heap) — develop the lemma in Robust3, migrate later
in one batch (one Base rebake).
NEXT (unchanged): uncomment+prove parametric_transversality_meager_planar_config
(develop in Robust3), then strata M4/M5/M6/M6b, then Capstone.

### planar_config PROVEN (2026-06-10 evening) — the transport lemma is done
parametric_transversality_meager_planar_config proven sorry-free and baked into
Robust2/heap (leaf rebuild 5s, BUILD_EXIT=0). Proof: flatten (real^2)^'n ≅
real^('n bit0) via the Φ/Ψ iso lifted from negligible_singular_image_2n
('n bit0 is {finite,wellorder} for free — Numeral_Type:350!); conjugate G/G'
through the bounded-linear pair map pm=(Ψ∘fst,snd) as blinfun P (Blinfun +
bounded_linear_Blinfun_apply); chain rule diff_chain_at for derG_e; contG'_e via
continuous_on_compose2 + bounded_bilinear.bounded_linear_left[OF
bounded_bilinear_blinfun_compose]; regular_value_on transports by
has_derivative_in_compose (NB: concludes in LAMBDA form, not ∘) + comp_surj;
engine at 'm='n bit0; pull back via meager_homeo_image.
TRAPS HIT (all now canon): (1) blast/metis on rule-shaped facts with
higher-order atoms (derG, regular_value_on ∀) HANGS — replace with
deterministic rule/OF/bspec/mp chains; heartbeats via build -v name the line.
(2) set_eqI is JNF-SHADOWED like vec_eq_iff — use Set.set_eqI. (3) linearI from
the Paper-template proof resolves differently in the Robust2 context
(HigherDiff/Smooth_Manifolds shadowing) — use Real_Vector_Spaces.linearI with
explicit componentwise shows. (4) NEVER write through /tmp symlinks to "copy"
a file (clobbered the master once; restored from context).
WORKFLOW THAT WORKED: /tmp scratch session (ROOT: Scratch_Planar =
Applied_Math_Appendix + Scratch_planar) → ~20s verify cycles; bisect hangs by
python-truncating at markers with `show ?thesis sorry`.
CENSUS: the "1 transport lemma" of the endgame is DONE. Remaining: 4 strata
(M4/M5/M6/M6b in Robust3) + 6 Capstone assembly leaves.
NEXT: M4 (meager_bad_regular_stratum) — product-box cover of the open
non-product locus + planar_config on each box; needs
regular_value_on_gradU_dip restricted to boxes.

### M4 PROVEN (2026-06-10 night) — meager_bad_regular_stratum
Proven sorry-free in 4 scratch iterations and baked into Robust2 (leaf 5s,
BUILD_EXIT=0) together with three REUSABLE helpers for the remaining strata:
- regular_value_on_subset (restriction along ⊆ via has_derivative_subset);
- open_prod_nat_cover (countable open product-box cover of any open set in a
  product of second-countable spaces; ex_countable_basis + topological_basisE +
  from_nat_into; handles W={} via empty boxes);
- dip_slice_no_surj_deriv (det HessU = 0 ⟹ no surjective slice derivative:
  slice deriv IS the Hessian by gradU_dip_has_derivative + at_within_open +
  has_derivative_unique + surj_matrix_vector_iff_det).
M4 assembly: WV = triple-regularity locus over V (open by open_A_cart_nonzero;
regular value by regular_value_on_gradU_dip); box-cover WV; per box run
planar_config (gradU_dip_joint_C1 restricts; engine residual-guard swallowed
by blast per the known trap); M4-bad ⊆ ⋃ engine-bad via the helper-3 injection;
meager_Union_nat + meager_subset close it.
NEW TRAP for the canon: the Munkres import (Top1_Ch3) SHADOWS `countable` —
qualify Countable_Set.countable in any statement mixing with library countable
lemmas. (Joins vec_eq_iff/set_eqI/linearI on the qualify-always list.)
Census: strata remaining M5/M6/M6b, then 6 Capstone leaves.
NEXT: M6 (meager_steering_singular_stratum) likely easiest next (uses M3
steering_singular_nowhere_dense already proven in Robust3), or M5 via
nowhere_dense_mstarg_zeros. Both need a "critical points over a nowhere-dense
ω-locus project to a meager set" argument — different engine (no
transversality), think product of nowhere-dense with slice compactness or the
σ-compact Crit machinery.

### M6 OBSTRUCTION ANALYSIS (2026-06-10 night) — not a quick wrapper
Attempted M6 (meager_steering_singular_stratum). The 2026-06-03 Tier-C note
"#13 = #7" was optimistic; even the careful note ("funnels through #9 → engine")
doesn't work as stated. FINDINGS (all verified against current sources):
1. ENGINE CANNOT EAT M6 DIRECTLY: planar_config needs regular_value_on gradU
   on V×Ω, and joint regularity (A6) genuinely requires det Dcvec ≠ 0 at every
   zero (A3's x-partial surjectivity consumes it: the 2×6 moment block has
   rank 2 ONLY when the steering Jacobian is nonsingular). M6 witnesses live
   exactly where det Dcvec = 0 — any box containing one falsifies the engine
   hypothesis. Same obstruction for M5 (¬surj DM breaks dE∘DM surjectivity).
2. Σ-STRUCTURE: det Dcvec = sin(ω1)·(cos(ω1) − sin(ω1)·g(ω2)) (Dcvec_det_eq).
   So Σ = {sin ω1 = 0 lines} ∪ {h=0 curve}; on sin≠0, h=0 ⟹ ∂1h ≠ 0 (checked:
   h=0 ∧ ∂1h=0 forces cos² = −sin², impossible) — the curve part is a regular
   1-manifold (graph charts via IFT). Curve-chart route still dies at the
   pole-lines AND at the broken x-partial (point 1).
3. POLE-LINE PHENOMENON (the real danger): along {ω1 = kπ}, kx=ky=0, kz=±1,
   so cvec_dip and gain_dip are CONSTANT along the line; ∂φU ≡ 0 there, and
   criticality reduces to ∂θU(x,kπ,φ) = cosφ·P(x) + sinφ·Q(x) = 0 (the a/b
   steering terms vanish with sin kπ; ∂θcvec = ±(cosφ,sinφ)) — which has a
   solution φ for EVERY x (any (P,Q) gives zeros). I.e. ALL configurations
   have critical angles on the pole lines; M6's meagerness rests ENTIRELY on
   the det Hess = 0 conjunct being non-generic along the witness family.
   That needs a (∂θU, detHessU)-style JOINT argument with 1-dim parameter —
   second-order data, outside the current engine (2-param, first-order).
4. DECOMPOSITION FACT: M6 ⊆ M6a (surj DM case) ∪ M5-bad (¬surj case), so
   M5-first ordering helps; but both M5 and M6a hit obstruction 1.
CANDIDATE ROUTES (decreasing preference, none cheap):
(R1) Kernel-direction reduction: on Σ, rank(Dcvec)≤1 with kernel direction
   explicit; criticality with A≠0 forces |A|²∇gain + 2·gain·Im(conj A·w)·(α,β)
   = 0; off the locus ∇gain ∥ (α,β) this forces A=0 (excluded) — reduces M6a
   to (i) a countability/structure analysis of {ω∈Σ. ∇gain ∥ kerdir} and
   (ii) fixed-ω analytic slices in x (nowhere_dense via rline_entire, M2-style).
   Pole-lines: ∇gain = (gdip'(kπ),0) and kernel dir = e_φ ⟹ parallel iff
   gdip'(kπ)=0 — check gdip'; if gdip'(kπ)=0 the lines are IN the parallel
   locus and need the second-order argument of point 3.
(R2) 1-parameter engine variant (core_1d): rebuild the chart machinery for
   G:(x,t)↦ℝ² over V×I, I⊆ℝ — heavy (weeks-scale, mirrors core_2d).
(R3) Re-cut the strata (M7 only needs the UNION to cover {Φ=0}): no free
   lunch — the deep content (critical-with-A≠0 over degenerate loci) remains.
STATUS: no proof code written for M6 (honest zero). M6b (A=0 stratum) may be
much easier and is not blocked — consider doing it next while the M5/M6
strategy is decided. PAPER GAP: the tex hand-waves "positive codimension";
the formal content is genuinely new mathematics.

### SOUNDNESS FINDING: M6/M7 AS STATED ARE FALSE — pole-line counterexample (2026-06-10)
gdip = (pi^2/4)*gsinc((pi/2)(1-cos t))*gsinc((pi/2)(1+cos t)) has gdip(0) =
gdip'(0) = 0 (gsinc(pi)=0; both derivative terms carry sin t). Consequence,
verified by hand from the definitions:
- gradU(x,(0,phi)) = gdip'*|A|^2*e1 + gdip*(...) = 0 for EVERY x, EVERY phi;
- HessU(x,(0,phi)) = gdip''(0)*|A|^2*e1e1^T (gdip''(0)=pi^2/8 > 0), rank<=1,
  so det HessU = 0 for every x;
- det Dcvec = sin(0)*(...) = 0; A_cart(x,c-bar) != 0 on a dense open x-set
  (c-bar = the constant pole steering vector, nonzero for generic omega0/omegas).
Hence M6's set contains a dense open subset of V (every x with A != 0 at the
pole witnesses ALL of M6's conjuncts at omega=(0,phi)) — NOT meager. Same for
M7/Phi_bad_meager_dip's full set {x. EX omega. Phibad = 0}. The pole lines
{omega1 = k*pi} are degenerate-critical for ALL configurations because the
dipole gain vanishes to second order there. The paper's unrestricted
quantification was never right; the capstone consumer
(regular_feasible_point_dip) only needs omega on the eps-SPHERE and the
ANNULUS Omega-tilde, which must be pole-free for the theorem to be true at all.
THE FIX (next session): restrict the omega-domain in M5/M6/M6b/M7 to the
pole-free region the consumers actually use (read regular_feasible_point_dip /
F0_nonempty_of_witness / no_degenerate_to_sphere_annulus for the exact set;
likely {omega. omega1 in a compact subinterval of (0,pi)} or the sidelobe set).
PAYOFFS of the restriction:
- M4 (proven) restricts for free (subset => meager_subset; zero rework).
- On the pole-free strip, gdip > 0 (gsinc factors vanish ONLY at cos t = -+1),
  and Sigma = {det Dcvec = 0} is the single explicit GRAPH curve
  theta = arccot(g(phi)) (cot bijective on (0,pi); h=0 => d1h != 0 already
  checked) — no pole lines.
- M6-restricted then reduces via the kernel-direction argument: on the curve,
  rank(Dcvec) = 1, criticality with A != 0 forces (gdip'(theta),0) parallel to
  the rank-1 range direction r(omega): test = gdip'(theta)*r2(omega) = 0. So
  witnesses live in {phi. gdip'(theta(phi)) = 0} u {phi. r2 = 0} — countable
  unless degenerate (a=b=0 subcase: omega0/omegas with equal transverse
  wavevectors makes the curve theta == pi/2 with gdip'(pi/2) = 0 identically —
  needs either a standing hypothesis excluding it or the L-component scalar
  equation route). Then fixed-omega x-slices are nowhere dense via the
  rline_entire machinery (M2-style), countable union => meager.
- M5-restricted: still needs its own argument (mstarg = 0 coupling); park.
NO CODE COMMITTED for M6 (nothing false, nothing half-baked). M4 proof is
unaffected (its statement is true and stays).

### (1) DOMAIN AUDIT COMPLETE — the pole-free restatement design (2026-06-10)
Read the full consumer chain + the paper. FINDINGS:
- Omega ctr = cbox(ctr -+ vector[pi/2,pi]) (Robust1:1576) mirrors the paper's
  FULL box (D_edit L1253). Every closed theta-interval of length pi contains a
  multiple of pi => Omega ctr ALWAYS contains pole points => unsatisfiable
  margins. Blast radius (all FALSE as stated): regular_config_exists
  (concl. ALL-omega Phibad/=0), no_degenerate_to_sphere_annulus +
  regular_feasible_point_dip (sphere/annulus margins over Omega ctr:
  for ANY eps either the sphere hits a pole line (eps >= dist(ctr1,piZ)) or
  the annulus retains pole points (phi-extent pi > pi/2 >= usable eps)),
  and THE FLAGSHIP F0_dip_nonempty itself (its X0-component: xi-margin
  ||gradU||+sigma_min >= xi > 0 over Omega ctr - ball is unsatisfiable; at
  poles both terms are 0 for EVERY configuration).
- THE PAPER'S OWN ESCAPE: D_edit L1253 "reduced to {theta0} x [phi0-pi,
  phi0+pi] ... when restricting to a 2D cut" — and the formalization always
  claimed to mirror the 2-D version (F0_nonempty_proof_2D, L1288/810).
  The formalization over-generalized the domain to the full box.
- KEY STRUCTURAL LUCK: F0/X0 defs (Robust1:1551-1566) take Omega AS A
  PARAMETER; only the instantiation is poisoned. Xrobust's sphere is the
  full planar circle — fine for eps small (pole-free).
THE FIX — "OmegaPF" (fat pole-free box), faithful-and-true:
  OmegaPF ctr delta = cbox (ctr - vector[delta,pi]) (ctr + vector[delta,pi]),
  hypotheses 0 < delta and pole-free: [ctr1-delta, ctr1+delta] avoids piZ.
  Capstone instantiates ctr=(pi/2,0), delta=pi/4 ([pi/4,3pi/4] pole-free).
  Margins over OmegaPF are stronger than the bare 2D-cut's, still satisfiable.
RESTATEMENT LIST (all in UNHEAPED Robust3 except one leaf addition):
  a. Robust2 (leaf, 5s): definition OmegaPF + OmegaPF_compact +
     OmegaPF_minus_ball_compact + sphere_subset_OmegaPF (eps <= delta) +
     gdip_pos (sin t /= 0 ==> gdip t > 0; gsinc > 0 on (0,pi)) +
     M4-restricted corollary (FREE via meager_subset from proven M4).
  b. M5/M6/M6b: EX omega -> EX omega IN OmegaPF ctr delta (+ pole-free hyp).
  c. M7 Phi_bad_meager_dip: ditto.
  d. regular_config_exists: concl. ALL omega IN OmegaPF. Phibad /= 0.
  e. no_degenerate_to_sphere_annulus: Omega -> OmegaPF; eps picked in
     {0<..<min delta (pi/2)} - R (proof mechanical, same isolated-zeros body).
  f. regular_feasible_point_dip: ditto.
  g. F0_nonempty_of_witness: generalize the hardcoded Omega ctr to a
     parameter with compactness hypothesis (proof identical, Weierstrass).
  h. F0_dip_nonempty: F0 ... (OmegaPF ctr (pi/4)) ...; chosen design
     ctr = omega0 = (pi/2,0) already in the proof.
THEN the strata become TRUE and provable: M4-restricted free; M6 via the
graph-curve kernel-direction reduction (pole-free => gdip>0, Sigma = single
regular curve); M6b A=0; M5 still needs its own argument (park).
NOTE FOR PAPER AUTHORS: the full-box statements in the tex (X0def over
Omega-tilde of the 2D box + thm:final via F0) inherit the pole issue for the
dipole element pattern; the 2D-cut reduction (or a pole-free shrink) is
needed in the prose too.

### OmegaPF RESTATEMENT LANDED — pole-free chain verified (2026-06-10 night)
Phase A (Robust2 leaf, 5s green): OmegaPF def + OmegaPF_compact +
compact_minus_ball + sphere_subset_OmegaPF + meager_bad_regular_stratum_on
(M4 over ANY witness domain K — free via meager_subset from proven M4).
Phase B (Robust3, 30 edits, batch-verified 11:43 green via /tmp Scratch_R3
session on top of the Appendix heap): M5/M6/M6b + Phi_bad_meager_dip now
EX/ALL omega IN OmegaPF ctr delta with hyps d0: 0<delta and pf: sin nonzero
on the box; regular_config_exists concl. bounded (now satisfiable);
no_degenerate_to_sphere_annulus + regular_feasible_point/witness_dip over
OmegaPF (eps picked in {0<..delta} - R; sphere_subset_OmegaPF[OF epspi dpi]);
F0_nonempty_of_witness generalized to a compact Omega-dom PARAMETER
(compact_minus_ball[OF cOm] replaces the box-specific lemma); FLAGSHIP
F0_dip_nonempty now exhibits 0<delta and F0 ... (OmegaPF ctr delta) ...,
instantiated delta=pi/4 at the broadside design with an explicit
sin>0-on-[pi/4,3pi/4] discharge (mem_box_cart + sin_gt_zero).
Robust3 batch-verify workflow: /tmp/scratchr3 ROOT (Scratch_R3 =
Applied_Math_Appendix + Nonemptiness_Robust3), threads=4, ~12 min (the
pre-existing Lmat/mstarg proofs dominate; restatements are cheap).
NEXT PASS (designed, not yet applied): add `odd CARD('n)` to M6b -> M7 ->
regular_config_exists -> regular_feasible_point/witness -> F0_dip_nonempty
(aligns with odd_N_nonemptiness; capstone IS the odd-N theorem). PAYOFF
(M6b discovery): for ODD N the collinear-phase case of A-nulls is EMPTY
(sum of +-1 cannot vanish), so M6b = engine run on G = cplx_r2 o A_cart with
GLOBAL regular value on V x UNIV: at any zero, cvec=0 => A=N/=0 (vacuous),
else dxA_surj (Spine:139, odd N!) gives x-partial surjectivity. Witness
bridge: at A-null, HessU = g * 2Re(conj grad-A (x) grad-A), so det HessU=0
with g/=0 (gain_dip_nonzero_of_sin + pf) forces singular A-slice-Jacobian.
To build for M6b: joint C1 field of A (template gradU_dip_joint_C1),
dxA-is-the-x-derivative lemma, Hessian-at-null computation.

### M6b RECON COMPLETE — brick list (2026-06-10 late night)
Verified facts for the M6b engine plan:
- af = A_cart definitionally (identical Sum-cis RHS; Spine:19 vs Paper:66);
  A_cart_eq_Afun bridges to the c-parametrized Afun x c (Robust1:2078).
- dxA (Spine:127) is the explicit x-partial FORMULA; dxA_surj (Spine:139,
  odd N + cvec/=0 + af=0 => onto C) is proven. MISSING: the lemma that dxA
  IS the x-derivative of af — prove by mirroring has_derivative_M_paper_x
  (termwise cis differentiation; same shape with weight 1).
- HessU_dip_entry_moments machinery exists (Robust1:~2906 joint
  matrix-vector helper) — route for the Hessian-at-null bridge:
  at A=0: grad|A|^2 = 2Re(conj A grad A) = 0 and
  Hess U = g * 2Re(conj gradA (x) gradA) (the conjA*Hess-A term drops),
  so det HessU = g^2 * det(2x2 A-Jacobian-Gram) and with g/=0:
  det HessU = 0 <=> A-slice-Jacobian singular <=> no surjective slice deriv.
M6b BRICKS:
  B1: has_derivative_afx: ((lam y. af cvec y w) has_derivative dxA cvec x w) (at x)
      [mirror has_derivative_M_paper_x; cis-sum termwise]
  B2: af joint C1 as G = cplx_r2 o (lam p. af (cvec_dip w0 ws) (fst p) (snd p)):
      joint derivative field via has_derivative_partialsI
      [mirror gradU_dip_joint_C1; omega-partial through Dcvec_dip]
  B3: regular_value_on G (V x UNIV) 0: at zero, cvec=0 => af = CARD /= 0
      (vacuous); else dxA_surj + cplx_r2-conjugation + x-partial => joint.
  B4: Hessian-at-null bridge (the only second-order brick):
      af=0 ∧ gain/=0 ∧ det HessU=0 => slice-Jacobian of G singular.
  B5: helper-3 analogue (unique slice derivative + surj_matrix_vector_iff_det)
      + assembly: M6b-bad subset of engine-bad(G, V x UNIV); engine; done.
ESTIMATE: B1 hours; B2 day-ish (template exists); B3 half-day; B4 the
risky one (second-order at nulls — investigate HessU_dip_entry_moments
first); B5 hours.

### M6b B4-CORE PROVEN — Hessian-at-null identification (2026-06-10 night)
Scratch_m6b started; FOUR lemmas already green (3s verify cycles):
- Hcmat_at_null: Hcmat = first-moment Gram at Afun=0 (the cnj-Afun term in
  Hcmat_def drops by itself; `by simp`).
- gradUc_at_null (VECTOR form): gradU (id-pattern) = 0 at M_paper$1 = 0,
  via gradUc_component_moments[unfolded null] componentwise. TRAP: plain
  simp re-normalizes M_paper projections to A_moment/M1_moment BEFORE null
  can fire — use [unfolded null] on the component lemma instead.
- Uc_at_null: V = |M1|^2 = 0 (Uc_eq_moment[unfolded null]).
- HessU_at_null: HessU$k$l = gain * (Dcvec e_k . (Hcmat *v Dcvec e_l)) at
  nulls — unfolding HessU_dip_entry_moments + the three vanishing lemmas.
  THE RISK BRICK OF M6b IS DISCHARGED.
Remaining M6b sorries (statements all parse green against the heap):
det_HessU_at_null (2x2 det algebra: det = 4 gain^2 (detJ * Im(cnj M2 M3))^2),
afR2_joint_C1 (B2, mirror gradU_dip_joint_C1), afR2_regular_value (B3,
dxA_surj + d_A_moment_x bridges + cvec=0 vacuity), null_no_surj_slice (B4',
needs slice-derivative formula + det bridge), assembly (M4 pattern, no
boxes). Verify loop: /tmp/scratchm6b session, ~17s cycles.

### M5 SOLVABILITY DESIGN — rank stratification (2026-06-11)
User requires solvability assurance before further investment. Analysis:
1. TRUTH: no pole-like forcing mechanism exists for M5 (mstarg(c)x = 0 is
   nowhere dense in x for EVERY fixed c (M2); the only fat families found are
   themselves meager, e.g. all-elements-coincident configs). Statement is
   credibly true on OmegaPF. A dedicated counterexample stress-test is the
   FIRST gate before proof investment.
2. KEY REALIZATION dissolving the old "obstruction": the engine needs ACTUAL
   joint-derivative surjectivity at zeros, and surj(DM) was merely the
   SUFFICIENT condition A6 used. On the ¬surj-DM locus, Dx gradU = dE∘DM can
   PERFECTLY WELL still have rank 2 (dE rank-2 needs only det Dcvec ≠ 0;
   range(DM) is codim ≥ 1 but generically transverse to ker dE). So:
   RANK-STRATIFY by the explicit x-partial field Dx(x,ω):
   - Stratum R2 = {(x,ω). Dx gradU surjective}: OPEN (explicit continuous
     2-row field, A5 bricks; rank lower semicont). M5-bad ∩ R2 handled by the
     EXISTING engine + open_prod_nat_cover, verbatim M4 pattern (joint
     regularity holds BY DEFINITION on R2: joint ⊇ x-partial).
   - Stratum R≤1 = rank Dx ≤ 1: rows of the explicit 2×(2N) field parallel —
     many analytic equations; combined with gradU=0 ∧ A≠0 ∧ det Dcvec≠0,
     resolve by one more concrete reduction (kernel-direction style) or
     fixed-ω slices. Bounded, concrete, same toolbox.
3. FREE NEW TOOL (from this analysis): a 1-parameter projection corollary of
   the EXISTING engine: for G(x,ω) := F(x,ω₁) (constant in ω₂), no slice can
   ever be surjective, so the engine yields meager {x. ∃ω. G = 0} for ANY
   jointly-regular 2-equation 1-parameter family — the x-projection of the
   FULL zero set, not just degenerate zeros. Useful for M6's curve/pole work.
4. FALLBACK LADDER if (2) resists: (a) map-switch a la M6b; (b) core_3d
   engine generalization (mirrors core_2d, bounded); (c) the paper's literal
   1-dim 2D-cut domain. ODD-N NOTE: the paper's tex never assumes odd N, but
   its lem:Azero-surj is false without it (collinear zeros); odd-N was forced
   at dxA_surj long before today — the formalization converges on the
   strongest currently-provable version.

### PROCESS DISCIPLINE (user directive, 2026-06-11) — monotone metric + solvability-first
1. THE MONOTONE METRIC, reported every session: count of TRUE-and-remaining
   obligations (progress against false statements is illusory; soundness
   restatements SHRINK this metric even when hypotheses grow).
   Trajectory: 22 (2026-06-02) -> 13 -> 4 (engine done, planar_config done)
   -> 3 (M4 done) -> CURRENT: 3 with M6b HALF-PROVEN (B4 core done),
   M6 designed, M5 designed+gated.
2. Never report an obligation "unsolved": every open item carries a proof,
   or a written design with go/no-go gates, or a fallback ladder.
3. ODD-N CLARIFICATION (for the record): the paper's tex never assumes odd
   N, but its lem:Azero-surj is false without it (collinear-phase zeros);
   odd CARD('n) entered the formalization at dxA_surj long ago and the
   Capstone's odd_N_nonemptiness always carried it. The 2026-06-10 pass
   only THREADED the existing forced hypothesis through the chain.

### M6b B4 COMPLETE — det_HessU_at_null proven (2026-06-11)
det HessU = 4 gain^2 (det(matrix Dcvec) * Im(cnj mu1 mu2))^2 at Afun-nulls
(mu_k = Mcfun first moments). Proof: scalarize everything (g, four Jacobian
entries j11..j22, Gram data n1 n2 r12 i12); Gram relation n1 n2 = r12^2+i12^2
via cmod_power2 + norm_mult; qform expansion (inner_vec_def +
matrix_vector_mult_def + sum_2 + a general ReSym fact); det_2; then the
det-bracket ring identity. TRAPS: (1) `algebra` (Groebner) FAILED on the
degree-6 ring identity both with and without the hypothesis — but plain
`simp add: algebra_simps` proves it; split hypothesis-substitution (sub:
n1n2 - r12^2 = i12^2) from the pure ring step. (2) M_paper$1 simp-normalizes
to A_moment — bridge A_moment = Afun via phase_def before nulls match.
(3) Re_cnj/Im_cnj lemma names don't exist; plain simp knows Re/Im of cnj.
B4 status: Hcmat_at_null, gradUc_at_null, Uc_at_null, HessU_at_null,
det_HessU_at_null ALL GREEN. The same quantity detJ*Im(cnj mu1 mu2) will BE
the slice-Jacobian determinant of afR2 (B4'), closing the loop.
Remaining M6b: B2 (joint C1), B3 (global regular value), B4' (slice), assembly.

### M6b B2 PROVEN — afR2_joint_C1 (2026-06-11)
The joint C1 blinfun derivative field for G = cplx_r2 o af: x-partial from
has_derivative_A_moment_x (+ Afun/A_moment/DA bridges), omega-partial chained
through has_derivative_cvec_dip + has_derivative_Afun_c + cplx_r2, assembled
with has_derivative_partialsI; full-field continuity componentwise
(Basis_prod_def cases, dcw0/da0 vanishing, the inner_sum intro chain).
NEW TRAPS (canon):
- `at x` ABBREVIATES `at x within UNIV`: any rewrite rule "at ?a within
  UNIV = at ?a" (e.g. at_within_open[OF UNIV_I open_UNIV] in a simp set) is
  the IDENTITY and LOOPS FOREVER — this caused every Interrupt_Breakdown /
  hang of the session. Only UNIV_Times_UNIV is needed; the within-UNIV form
  then IS the at-form syntactically.
- bounded_linear.continuous_on is the COMPOSED form (bounded_linear f ==>
  continuous_on s g ==> continuous_on s (f o g)) — feed continuous_on_id'
  (the (\\x. x) form; continuous_on_id is the `id` form and won't match).
- continuous_on_compose2 cannot HO-invert pairing lambdas (g = \\p. F (fst p)
  (snd p) composed with a pairing f) — unfold the definition and use the
  flat intro chain instead.
- [of]-instantiation order: use [where x = ... and ...] (schematic order
  surprises); pin `for z`-binder types (decoupled-type-var trap again).
M6b board: B1 done (library), B2 PROVEN, B4 PROVEN (det identity), remaining:
B3 (regular value, assembly-grade), B4' (slice bridge), final assembly.

### M6b B3 PROVEN — afR2_regular_value (2026-06-11)
Global regular value of G = cplx_r2 o af on V x UNIV (odd N), NO openness
hypothesis needed. Proof: at a zero, cvec = 0 forces af = of_nat CARD /= 0
(odd => CARD /= 0 by presburger) — vacuous; else dxA_surj fires. The
witness derivative is B2's joint field at z; its restriction to
x-directions IS the x-partial by has_derivative_unique (embed via
has_derivative_Pair[OF ident const] + diff_chain_at), so surjectivity
lifts: surj(x-partial) => surj(joint) via range inclusion.
Bridges: dxA_eq_DA (dxA = DA_paper_x; needs scaleR_conv_of_real — d_phase
uses *R, dxA uses of_real-mult), comp_surj with surj_cplx_r2.
M6b board: B1 done, B2 PROVEN, B3 PROVEN, B4 PROVEN. Remaining: B4'
(null => no surjective slice derivative: the omega-slice derivative of afR2,
its 2x2 Jacobian determinant = detJ * Im(cnj mu1 mu2) connecting to
det_HessU_at_null, + uniqueness at interior points) and the final assembly
(M4 pattern, V x UNIV, no box cover). Two sorries left in the scratch.

### M6b COMPLETE — meager_Azero_degenerate_stratum PROVEN (2026-06-11)
ALL bricks landed in one extended session; the full stratum is sorry-free
and in the heap (leaf 7s green). Final pieces:
- B4' (null_no_surj_slice): the omega-slice derivative of afR2 (standalone
  afR2_omega_partial, FY0 hoisted), its 2x2 determinant via matrix entries
  (cplx_r2 components) + det_2 = Im(cnj(S e1) S e2) = (j11 j22 - j12 j21) *
  Im(cnj mu1 mu2) — EXACTLY the det_HessU_at_null quantity; degeneracy +
  gain/=0 kills it; surj => det/=0 via matrix_vector_mul(2) (NOT
  matrix_works — that one wants the HMA (*s)-linear!) +
  surj_matrix_vector_iff_det. Sval moment-form needed sum_negf +
  sum_subtractf + scaleR_conv_of_real (d_phase uses *R).
- Assembly: engine on V x UNIV directly (NO box cover; slice-within-UNIV
  IS at by the abbreviation insight); witnesses inject via
  gain_dip_nonzero_of_sin[OF pf] + A_cart_eq_af; passed FIRST TRY.
MONOTONE METRIC: true-and-remaining obligations 3 -> 2 (M5 designed+gated,
M6 designed). M6b took ~1 day from brick list to heap — the de-risking
discipline (B4-first) paid off.
Robust3 full-chain re-verify (M7 now consumes the heap M6b) running.

### B3 TIGHTENED to the global form (2026-06-11, user-directed)
afR2_regular_value_UNIV: regular_value_on (afR2 w0 ws) UNIV 0 — odd N is
the ONLY hypothesis; no domain/openness at all (the proof never used
membership). The V x UNIV form is now a 1-line corollary via
regular_value_on_subset. Bonus elegance: the within-UNIV show closes with
the bare global derivative — `at z within UNIV` IS `at z` (abbreviation),
so has_derivative_at_withinI is unnecessary. Phantom-'n pinned via an
explicit UNIV type annotation (the decoupled-type-var trap).
Leaf 6s green; full chain re-verify running.

### M6 CAMPAIGN OPENED — restatement + bricks R1/R2 proven (2026-06-11)
RESTATEMENT (chain-verified 12:21, committed 313ef39): M6 gains the
surj-DM conjunct (cvec=0 witnesses belong to M5: DM's A-component is 0 at
c=0 — DA_paper_x x 0 = 0 — so DM never surjective there; M7 coverage
re-partitions cleanly) + hsep/kdiff hypotheses ((a,b) /= 0 for the curve
analysis; capstone discharges kdiff: kx values 1 vs 0 at the design).
SCRATCH (Scratch_m6, ~20s cycles): R1 cols_dependent_2d (det=0 + v/=0 =>
columns dependent; vec_eq_iff must be QUALIFIED in metis — the shadowing
trap struck again inside metis, hanging a build) and R2 Dcvec_col2/
Dcvec_col2_nz (second steering column = sin-theta*(-sin-phi, cos-phi),
NEVER zero off poles) both proven first-pass.
REMAINING BRICKS: R3 kernel-direction reduction (witnesses force
gdip'(theta)=0; pure linear algebra + gradU_dip_component_moments);
R4 gdip'-zeros = {cos theta = 0} off poles (THE GRIND: gdip strict
monotonicity on (0,pi/2) via tan u > 4u/(pi^2-4u^2), split u <= 1.2
polynomial bounds / u >= 1.2 boundary estimate — worked out in analysis,
~1-2 sessions); R5 fixed-omega slices nowhere dense (rline_entire moment
machinery + explicit two-cluster configuration for the nonvanishing
witness); assembly (finite witness-angle set + finite-union meagerness).

### M6 R3 PROVEN FIRST-PASS — the kernel-direction reduction (2026-06-11)
M6_witness_gdip_deriv_zero: every steering-singular witness off the poles
(gradU=0, A/=0, det Dcvec=0, sin theta /= 0) forces gdip'(theta) = 0.
Proof exactly as designed: scalarize via gradU_dip_component_moments
(j=1: gd*aa + g*T(col1) = 0; j=2: g*T(col2) = 0 — the
frechet_derivative-at-0-argument vanishes via linear_frechet_derivative
[OF gdip_differentiable] + linear_0); rank-1 dependence col1 = t *R col2
(R1 + R2 + det_2/matrix_def bridge); T is scaleR-linear (simp +
of_real_mult + algebra_simps, vector_scaleR_component is [simp]); so
gd*aa = 0 with aa = cmod(A)^2 > 0. ZERO iteration debugging — the
deterministic-OF + scalarize discipline is now routine.
M6 board: R1+R2+R3 proven; remaining R4 (gdip monotonicity grind),
R5 (slice nowhere-dense), assembly.

### CHECKPOINT REFLECTION (2026-06-11, user-requested) — direction + provability audit
DIRECTION CONFIRMED: since the soundness repair, every step has landed as
designed (planar_config, M4, M6b, M6-R1/R2/R3 — several first-pass). Risk
is concentrated in exactly ONE residual design (M5b below).
R4 STRATEGY UPGRADE (found during this audit): instead of the tan-inequality
grind, use the LOG-DERIVATIVE route: gdip' = C sin(theta) [gsinc'(u-)gsinc(u+)
- gsinc(u-)gsinc'(u+)], and the bracket > 0 for u- < u+ in (0,pi) iff
h(x) = gsinc'/gsinc = cot x - 1/x is strictly decreasing, which holds since
h'(x) = 1/x^2 - 1/sin^2 x < 0 <=> sin x < x. ONE elementary inequality.
gsinc = sin x/x off 0 (def 422); off-zero derivative by DERIV rules.
CAPSTONE DISPOSITION CLARIFIED: odd_N_nonemptiness + its 6 sorried leaves
are the OLD abstract scaffold, fully superseded by the concrete flagship
F0_dip_nonempty (= TeX thm:final). They are an architecture-retirement
decision (user sign-off), NOT remaining mathematics.
ENDGAME REQUIREMENT noted: Robust3 must enter a session (ROOT edit + bake)
so `isabelle build` certifies the flagship end-to-end — currently only the
Scratch_R3 harness checks it.
THE FINITE GOAL LIST (with strategies) — see the session report; provability
classes: G1-G4 HIGH (established patterns), G5 (M5b) MEDIUM-direct with a
guaranteed fallback ladder, G6-G9 trivial/decision-grade.

### PARALLEL WAVE 1 — G4 (M5a) LANDED GREEN (2026-06-11, agent-proven)
meager_grad_x_regular_part: the x-partial-regular part of M5 is meager —
proven by a parallel agent in 2 build iterations, independently re-verified
(BUILD_EXIT=0, 0 sorries). Statement is DERIVATIVE-DISCIPLINE-shaped (the
regularity condition is an existential has_derivative + surj, equivalent to
surjectivity of the explicit field by has_derivative_unique). Tightness:
needs ONLY open V (Vne unused, NO CARD hypothesis — surjectivity is
hypothesized in the stratum, not derived from the rank-12 submersion).
AGENT DISCOVERY: regular_value_on_via_x_partial (Robust1:3204, the A1
helper) already packages the embedding+uniqueness surjectivity lift —
feeding it the gradU_dip_joint_C1 field + the explicit DxF gives
regular_value_on on the whole open locus in ONE rule application. W's
openness: Blinfun-field continuity (continuous_on_gradU_dip_xpartial_applied)
+ continuous_open_vimage[OF open_surj_blinfun]. Engine + box cover verbatim
M4. Fleet status: G1 (R4), G2 (R5), G3 (M6 assembly), G5/G6 (M5 analysis)
still running.

### PARALLEL WAVE 1 — G1 (R4) GREEN; G5/G6 ANALYSIS DELIVERED (2026-06-11)
G1: gdip_deriv_zero_iff PROVEN (agent + one resume; independently verified,
0 sorries, 4s build). Route exactly as designed: explicit gsincd off zero
(has_field_derivative_transform_within_open), DERIV chain/product for gdip,
bracket positivity via h x = cos x/sin x - 1/x strictly decreasing
(DERIV_neg_imp_decreasing; sin x < x by MVT + cos monotone), frechet-eval
bridge g1_frechet_eval. R4 is the last analysis brick of M6.
G5/G6 ANALYSIS (M5 gate + M5b design) — headline findings:
1. M5 TRUTH GATE: PASSED — no counterexample mechanism; but a GENUINE
   near-miss found: THE BEAM-CENTER ANGLE. cvec_dip w0 ws w0 = 0
   IDENTICALLY (the lift term cancels), w0 IS in the box, and at c=0:
   d_phase = 0 => NOT surj DM for EVERY x; moments real => steering term
   of gradU vanishes; gdip'(pi/2) = 0 => gradU(x, w0) = 0 for EVERY x.
   Three of M5's four conjuncts hold x-UNIVERSALLY at w0. M5 survives only
   because det HessU(., w0) is a nontrivial polynomial (covariance form
   Hess = N^2 gdip''(pi/2) e1e1^T + C^T(-2N Cov x)C; gdip''(pi/2) =
   (16-4pi^2)/8 /= 0; phi-column of Dcvec /= 0 pole-free). The c(w)=0
   angles MUST be treated by dedicated polynomial slices (design piece D2).
2. ROUTING CORRECTION: my earlier claim "det Dcvec = 0 witnesses route to
   M6" is FALSE for the not-surj case: current M7 cut sends
   (A/=0, not-surj, det=0) to M5. Agent recommends re-cut D0 (det/=0 into
   M5, drop surj from M6). COORDINATION DECISION (mine): do NOT re-cut now
   — G2/G3 are mid-flight on current statements, and M6's R5 slice proof
   USES the surj conjunct (c=0 slices empty). Instead M5b gains piece D5:
   the (not-surj, det=0) corner reuses R3's reduction (which needs NO surj)
   to the same finite angle set as M6, with R5-variant slices (component-2
   criticality needs no surj) at c/=0 and D2-polynomial slices at c=0.
3. M5b DESIGN (full table in agent report, recorded here abridged):
   D1 joint-regular part via engine (M4 pattern; subsumes M5a) HIGH 2-4d;
   D2 c(w)=0 angles: countable + det-Hess covariance-polynomial slices
   HIGH 3-5d; D3 phase-collinear branch via a 3-equation/2-parameter
   "excess engine" (IFT charts -> (2N-1)-dim graphs -> negligible
   projections; NO Sard needed) + Z^3 lattice union MED-HIGH ~1.5w;
   D4 Branch-P residual: explicit rank-drop dichotomy (gamma parallel-or-
   not to c) + excess engine on (star-n)/Hess.u(w) rows MEDIUM 1.5-3w;
   D5 (new, mine) det=0 corner via M6 machinery sans surj. Fallbacks for
   D4: deeper stratification; core_3d ruled out structurally by the agent
   (gradU rows degenerate at exactly the residual witnesses); 1-dim cut
   last resort.
Fleet: G2 (R5), G3 (M6 assembly) still running.

### M6 COMPLETE + M5a IN HEAP — the parallel wave integrated (2026-06-11/12)
THE SPLICE WORKED FIRST-TRY: G1 (gdip_deriv_zero_iff) + G2
(M6_slice_nowhere_dense) + G3 (assembly, stubs swapped for the real proofs)
grafted into Robust2 as one section; leaf green 13s, zero sorries in the
graft. meager_steering_singular_stratum (M6) IS PROVEN. G4's
meager_grad_x_regular_part (M5a) grafted too. Robust3: ONE sorry left (M5).
MONOTONE METRIC: 2 -> 1 (+ M5 already half-covered by M5a and fully
designed as D1-D5).
PARALLEL-WAVE RETROSPECTIVE (first multi-agent run, 5 agents):
- All four provers landed GREEN (G1 needed one resume after ending its
  turn mid-build; G2/G3/G4 single-shot). Wall-clock for the whole wave
  ~26 min of agent time, run concurrently; independent re-verification
  of every result before commit (never-trust rule held).
- The sorry-stub protocol worked exactly as designed: G3 proved the
  assembly against stubbed R4/R5 while G1/G2 proved them; splice = text
  substitution + one leaf build.
NEW TRAP-CANON ENTRIES (from agents):
- finite_UNIV is SHADOWED by Containers' phantom-type constant: 
  sum.remove[OF finite_UNIV UNIV_I] fails; use `by (rule sum.remove)
  simp_all`.
- image_eqI[OF ...]/UN_I[OF ...] die with "multiple unifiers" (HO ?f ?x);
  use proof (rule image_eqI[where x = ...]) so the conclusion pins first.
- default simp rewrites c-inner-c /= 0 to c /= 0 (feed original facts);
  `unfolding` applies its rule-set jointly (sequence dependent unfolds);
  goal-side simp pre-normalization defeats equation facts (use
  `unfolding fact by (rule ...)`).
- cline_entire combinators (sum/mult/add/cnj/const/cis_linear/
  of_real_linear) + rline_entire_{Re,scale} are generic over 'n in Paper
  ~2237-2660; PLAIN-moment cline facts did not exist — G2's
  clA_moment/clM1_moment/clM2_moment are new reusable infrastructure.
- meager_Union_finite exists (Paper:3274); cos_zero_iff_int2 cleaner than
  cos_zero_iff; sincos_total_2pi for amplitude-phase rewrites;
  finite_affine_int_zeros (G3) is a reusable lattice-window lemma.
NEXT: M5 = D1 (joint-regular engine pass, subsumes M5a) + D2 (beam-center
polynomial slices) + D3 (phase-collinear lattice + excess engine) + D4
(Branch-P residual) + D5 (det=0 corner via M6 machinery sans surj) per the
analysis agent's design; then flagship certification (Robust3 into a
session) + Capstone retirement decision.

### M5 D1-D5 SKELETON LANDED (green) (2026-06-19)
M5_Dev/Scratch_m5_skeleton.thy (+ own ROOT, session Applied_Math_M5Dev on
the Applied_Math_Appendix heap) builds BUILD_EXIT=0, 3s. Structure: the M5
bad set = the ?def stratum of Phi_bad_meager_dip; covered by an exhaustive
excluded-middle split (det Dcvec =0 ? ; cvec =0 ? ; x-partial regular ?):
  D5  = ?def & det(matrix(Dcvec_dip w0 ws w)) = 0
  D2  = ?def & det /= 0 & cvec_dip w0 ws w = 0
  D1  = ?def & det /= 0 & cvec /= 0 & (EX Dx. (gradU has_derivative Dx)(at x) & surj Dx)
  D34 = ?def & det /= 0 & cvec /= 0 & ~regular   (= D3 collinear U D4 Branch-P)
D1 is PROVEN here: it is a subset of the heap's meager_grad_x_regular_part
(M5a) - restricting w to OmegaPF and adding conjuncts only shrinks the set -
so meager_subset closes it; the assembly closes the exact
meager_rank_deficient_stratum goal via (intro meager_Un ...) + meager_subset
with the cover proved by subsetI/blast. LIVE STUBS = 3: m5_D2_beamcenter,
m5_D5_steersing, m5_D34_residual. D34 kept as one statement (D3/D4 separating
predicate is proof-internal). This is the Wave-2 launch pad: each stub is an
independent meagerness obligation a prover agent can take, splice back by
text substitution (same protocol that landed M6). NEXT: prover wave on
D2/D5/D34, then graft the proven assembly into Robust3.

### WAVE 2-3: D34 + D2 SCAFFOLDS GREEN; D5 still 529-blocked (2026-06-19)
Parallel prover waves on the three M5 stubs. Anthropic 529 overload was
intermittent all session: D34 (wave 2) and D2 (wave 3) rode it out and
landed; D5 failed all 3 attempts, D3 failed 1 (no work lost, 0 tokens).
Both landed scaffolds independently re-verified BUILD_EXIT=[0]:
- M5_Dev_D34/ (Applied_Math_M5_D34): m5_D34_residual PROVEN verbatim against
  3 inner sorries. (a) fixed_c_nonsurj_nowhere_dense = FREEBIE (it is
  nowhere_dense_mstarg_zeros + surj_iff_mstarg, Robust3 L572-757, in scope at
  the L970 splice; sorried only because dev imports Robust2). (b/c)
  m5_D34_D3_collinear / m5_D34_D4_branchP: genuine, both reduce to ONE shared
  "excess engine" (IFT-chart codim, Sard-free, Z^3 lattice via
  finite_affine_int_zeros). phase_collinear is the proof-internal D3/D4 split.
- M5_Dev_D2/ (Applied_Math_M5_D2): m5_D2_beamcenter assembly PROVEN sorry-free
  (witness confinement to finite K via beamcenter_critical_cos_zero +
  finite-union + subset, mirrors M6); reduces to 2 GENUINE leaves (not splice
  freebies): m5_D2_beamcenter_K_finite (~hours: cos(w1)=0 pins w1; sin_cos +
  finite_affine_int_zeros pins w2) and m5_D2_slice_nowhere_dense (~multi-day:
  covariance-Hessian det polynomial nowhere-dense, gdip''(pi/2)=(16-4pi^2)/8).
FRONTIER now: D5 (retry), D3+D4 (shared excess engine), D2's K_finite +
slice_nd. The M5 assembly stays sorry-free against the top stubs; integrate
each leaf as it closes, then graft into Robust3 L970.

### D5 + D3 SCAFFOLDS SALVAGED from the 529 "failures" (2026-06-19)
The wave-3 D5/D3 agents 529'd on their FINAL result-return, but had already
written + (as I re-verified) BUILD_EXIT=[0] their scaffolds on disk:
- M5_Dev_D5/ (Applied_Math_M5_D5): m5_D5_steersing PROVEN against 4 sorries -
  3 FREEBIES (m5_D5_hsep_freebie = Phi_bad_meager_dip's hsep; m5_D5_kdiff_freebie
  = kdiff; fixed_c_nonsurj_nowhere_dense = mstarg) + 1 GENUINE
  m5_D5_beamcenter_angle_meager. D5 confined steering-singular witnesses to a
  FINITE S1xS2 SORRY-FREE (finite_cos_zeros_interval + finite_phase_zeros_interval).
- M5_Dev_D3/ (Applied_Math_M5_D3): m5_D34_D3_collinear PROVEN against 1 freebie
  (mstarg) + 1 GENUINE D3_excess_engine (the IFT-chart core).
GENUINE FRONTIER CONSOLIDATED to 3 reusable cores: (A) excess engine
(D3_excess_engine) -> D3 + D4; (B) beam-center covariance-Hessian polynomial
nowhere-density -> D2 slice_nd + D5 beamcenter_angle (SAME lemma); (C) D2
K_finite (~hours, mirror D5's proven finite confinement). Everything else is a
splice freebie. Next wave: A, B, C in parallel.

### WAVE 4: K_finite CLOSED; M5 reduces to TWO genuine facts (2026-06-19)
- (C) K_finite: m5_D2_beamcenter_K_finite is FULLY PROVEN, sorry-free -
  verified by STRICT rebuild quick_and_dirty=false (STRICT_EXIT=0) + clean
  grep. M5_Dev_Kfinite/Applied_Math_M5_Kfinite. (Agent 529'd on its result-
  return but the proof was already complete on disk - salvaged.)
- (A) Engine: M5_Dev_Engine/Applied_Math_M5_Engine, BUILD_EXIT=[0]. ALL
  D3 plumbing proven sorry-free (engine_bad_eq_projection, D3_excess_engine,
  m5_D34_D3_collinear, fixed_omega_slice_meager); isolated to ONE genuine
  core excess_projection_meager, stated PARAMETRIC in the angle curve Gamma
  so D4 reuses it verbatim. phase_collinear confirmed codim-1 (not finite-K).
- (B) BeamHess: M5_Dev_BeamHess/Applied_Math_M5_BeamHess, BUILD_EXIT=[0].
  BOTH m5_D2_slice_nowhere_dense AND m5_D5_beamcenter_angle_meager proven
  verbatim via one shared engine (Hessian collapse to covariance form,
  det-as-polynomial, line-entirety, nowhere-density); isolated to ONE genuine
  core gdip2_nonzero_of_cos_zero (gdip''(pi/2)=(16-4pi^2)/8 /= 0, a scalar
  2nd-derivative computation on the sinc-factored gain).
NET: the ENTIRE M5 now reduces to exactly TWO genuine math facts -
excess_projection_meager (IFT engine, D3+D4) and gdip2_nonzero_of_cos_zero
(D2+D5) - plus splice freebies (mstarg, hsep, kdiff). Next wave: prove gdip2
(likely closable -> kills D2+D5), attack excess_projection_meager (multi-week),
wire D4 (m5_D34_D4_branchP) to the parametric engine.

### WAVE 5: gdip2 PROVEN; SOUNDNESS CATCH on the excess engine (2026-06-19)
WIN: gdip2_nonzero_of_cos_zero is FULLY PROVEN sorry-free (M5_Dev_gdip2,
verified quick_and_dirty=false STRICT_EXIT=0). gdip''(pi/2)=(16-4pi^2)/8 via
gsincdd 2nd-deriv + R4 first-deriv machinery. This kills the only genuine
residual of BOTH D2 (slice) and D5 (beamcenter) - so D2 and D5 reduce to
proven facts (gdip2 + K_finite) + splice freebies.
CATCH (caught by reading statements, NOT by the green build): the wave-4
engine lemma excess_projection_meager is stated for ANY Gamma <= OmegaPF
(Gsub, no curve restriction) and is FALSE in general (e.g. Gamma=OmegaPF:
~surj over a 2D omega-range is not meager in x; its proof needs the FALSE-for-2D
phase_collinear_curve_finite_arc_cover). D3 instantiates Gamma = collinear
CURVE (1D) -> SOUND. D4 (M5_Dev_D4) instantiates Gamma = ~collinear COMPLEMENT
(2D) and "closes by blast" -> UNSOUND (leans on a false instance; its
m5_D34_subset_mstarg_residual also drops the gradU=0/detHess=0 conditions D4
needs). D4 build is green but illusory. NOT COMMITTING M5_Dev_D4 as a valid
reduction.
CORRECTED FRONTIER (genuine remaining math):
  (1) phase_collinear_curve_finite_arc_cover - for the COLLINEAR CURVE only
      (tighten statement to curve/arc-coverable Gamma; true & provable).
  (2) excess_arc_projection_meager - per-arc IFT-chart negligible projection
      (the deep analytic core).
  (3) D4 Branch-P (GENUINE, NOT reduced) - meagerness of the 2D ~collinear
      residual via the gamma||c rank-drop dichotomy, keeping gradU=0/detHess=0
      (core_3d ruled out). The hardest piece, as the diary always said.
LESSON: a green (quick_and_dirty) build can rest on a FALSE stubbed lemma;
must verify intermediate STATEMENTS are true, not just that it compiles.

### WAVE 6: 3 SOUND cores; over-generality FIXED; D4 done right (2026-06-19)
Corrected wave (Munkres machinery wired in: Rpow_hyperplane_empty_interior,
affine_span_empty_interior, finite_union_empty_interior, complete_metric_baire_aux,
all in the heap via Base). All 3 build-green AND soundly-stated (agents ran
extreme-instance sanity checks per the lesson):
- ArcProj (M5_Dev_ArcProj): excess_arc_projection_meager (per SINGLE arc, no 2D
  pitfall) reduced to ONE deep core excess_arc_negligible_closed_cover (IFT chart
  of the per-arc bad fibre as a (2N-1)-dim graph + negligible x-projection,
  negligible_singular_image_2n). Proved empty/point/finite-arc sanity checks to
  confirm the cut. Genuine (not a freebie).
- CurveEngine (M5_Dev_CurveEngine): FIXES the over-generality. New predicate
  finitely_arc_coverable; excess_projection_meager_curve now carries it as a
  hypothesis (TRUE), supersedes the false M5_Dev_Excess engine. collinear_locus_
  finite_arc_cover proves the collinear LOCUS is finitely_arc_coverable (routine,
  finite_*_zeros). Re-derived D3 (m5_D34_D3_collinear) sorry-free against the
  sound engine. Remaining: collinear_locus_finite_arc_cover + the shared
  excess_arc_projection_meager (= ArcProj core) + mstarg freebie.
- BranchP (M5_Dev_BranchP): D4 done SOUNDLY. m5_D34_D4_branchP via branchP_engine
  -> branchP_indep_core, which RETAINS gradU=0/detDcvec!=0/cvec!=0/~surj and adds
  linear-independence ~gamma_par_c; codim from the RETAINED gradU=0 via rank-drop
  (NOT the false 2D curve-engine). phase_collinear == gamma_par_c so ~collinear =
  independent case = exactly branchP_indep_core. ONE genuine new core.
GENUINE FRONTIER = 3 soundly-scoped analytic cores: (1) excess_arc_negligible_
closed_cover [D3, deep]; (2) collinear_locus_finite_arc_cover [D3, routine];
(3) branchP_indep_core [D4, deep]. (1) and (3) are both (2N-1)-dim-graph =>
negligible-x-projection facts (codim from arc-param vs gradU=0). All standard
diff-topology, not open problems. Plus splice freebies (mstarg, hsep, kdiff).
M5_Dev_CurveEngine supersedes M5_Dev_Excess (kept for history, flagged false).

### WAVE 7: DEEPER SOUNDNESS BUG (analytic_arc too weak) + D4 reduced (2026-06-19)
CORRECTION to the Wave-6 "sound" claim: the D3 engine is STILL unsound, at the
DEFINITION level. analytic_arc is defined as merely  EX a b phi. a<=b &
continuous_on {a..b} phi & gamma = phi`{a..b}  -- continuous only, so it ADMITS
PEANO space-filling curves. Therefore (a) a 2-cell IS an analytic_arc =>
finitely_arc_coverable(whole box) is vacuously TRUE => Wave-6's finitely_arc_
coverable "fix" did NOT restore soundness, only relocated the bug; (b)
excess_arc_projection_meager (concludes meager x-projection over an analytic_arc
gamma) is FALSE for a Peano gamma. The ArcCover agent CAUGHT this and refused to
close its lemma via a space-filling arc. FIX REQUIRED: strengthen analytic_arc to
genuinely 1-D (C1 / rectifiable / negligible image - matching its name), then
re-verify the whole D3 chain (ArcProj, CurveEngine, ArcNeg, ArcCover).
WAVE-7 RESULTS:
- IndepCore (M5_Dev_IndepCore, SOUND, build-green): D4's branchP_indep_core
  reduced to one core branchP_indep_negligible_closed_cover = (2N-1)-dim graph
  (from RETAINED gradU=0 rank-drop) has negligible x-projection via heap
  negligible_singular_image_2n. NO analytic_arc dependency -> clean.
- ArcCover (M5_Dev_ArcCover2, build-green, sound reductions): 4 new sorry-free
  lemmas (component forms; phase_collinear_iff_crossTheta via heap cols_dependent_2d;
  crossTheta_trig; collinear_locus_eq_crossTheta_zero) reduce the cover to the
  explicit 1-D analytic curve {crossTheta=0} INTER box, crossTheta = P sin w1 +
  cos w1 Q(w2) + R(w2) (ONE equation -> genuine curve, unlike M6's two-equation
  finite K). Remaining cover step needs a continuous-IFT-with-compactness / real-
  analytic curve structure theorem NOT in the heap (substantial).
- ArcNeg: agent failed to return (StructuredOutput); partial file on disk; moot
  until analytic_arc is fixed (its target is false under the weak def).
HONEST CORRECTED FRONTIER. Genuinely PROVEN+sound: M5 assembly, D1, gdip2,
K_finite => D2,D5 done modulo splice freebies. Genuine remaining:
  (i)  STRENGTHEN analytic_arc def (small, ripples through D3 chain).
  (ii) the shared negligible-projection CHART core (D3 per-arc + D4
       branchP_indep_negligible_closed_cover): builds on heap
       negligible_singular_image_2n + the moment Jacobian; genuine multi-day.
  (iii) D3 curve-cover finiteness (collinear_locus_finite_arc_cover): needs a
       real-analytic curve structure theorem NOT in the heap; substantial
       independent formalization.
These are standard results (not open problems) but (ii)+(iii) are real multi-
day/week mechanization, (iii) needing machinery the project lacks. CHECKPOINT:
stop autonomous grinding here; surface to user.

### WAVE 8: analytic_arc FIXED to C1; user unhung the build; D3+D4 cores symmetric (2026-06-19)
- analytic_arc strengthened to C1: "EX a b phi. a<=b & phi C1_differentiable_on
  {a..b} & gamma = phi`{a..b}". Soundness gate analytic_arc_negligible PROVEN
  sorry-free: C1_differentiable_on => differentiable_on, DIM(real)<DIM(real^2),
  negligible_differentiable_image_lowdim. Peano curves excluded (not C1). The
  Wave-7 weak-def bug is FIXED.
- Wave-8 Agent A's build HUNG (~34 min, one runaway proof line). USER opened it in
  jEdit and fixed the hanging line; M5_Dev_D3Sound now builds BUILD_EXIT=[0] in 5s.
  (Orphaned poly 466493 killed; it had escaped timeout via the `| tail` pipe and
  was blocking the wave. TRAP: timeout -s KILL on `isabelle build ... | tail` can
  orphan poly which holds the pipe open => agent Bash hangs forever; kill the poly
  PID to release.)
- D3 (M5_Dev_D3Sound) and D4 (M5_Dev_D4Core) BOTH build green, each with ONE
  sorry now in the SAME shape: the IFT chart bundle excess_arc_charts_Nn /
  branchP_indep_charts_Nn (produce a countable family of charts with
  non-surjective derivatives covering the bad x-fibre, in the charts_core_Nn
  output shape). negligible_singular_image_2n + meager_negligible_closed_cover
  (Sard session now imported) assemble the cover sorry-free ABOVE that sorry.
- These supersede the weak-analytic_arc M5_Dev_ArcProj. M5_Dev_CurveEngine's
  collinear_locus_finite_arc_cover / excess_projection_meager_curve still need
  re-soundifying against the C1 def (part of finishing D3 + core 3).
GENUINE FINAL CORES now: excess_arc_charts_Nn (D3) + branchP_indep_charts_Nn (D4)
= the IFT chart construction (shared shape); plus collinear_locus_finite_arc_cover
(D3 curve cover, core 3, needs real-analytic curve structure).

### WAVE 9: charts_Nn cores diagnosed - the irreducible floor (2026-06-19)
Both charts_Nn cores remain ONE sorry each (M5_Dev_D3charts excess_arc_charts_Nn
L286; M5_Dev_D4charts branchP_indep_charts_Nn L164), both build-green
(BUILD_EXIT=0), assembly chains above them all sorry-free. Agents added the
empty-arc chart witness + full engine analysis. KEY DIAGNOSIS (why the heap
engines do NOT close them):
- charts_core_Nn / parametric_transversality_meager_planar_config / the complex
  engine all control the OMEGA-PARTIAL non-surjectivity of their map G (for
  G=gradU that is det(HessU)=0 - the M4/M6 steering/Hessian degeneracy).
- M5's defining condition is the X-PARTIAL moment-Jacobian rank drop
  ~surj(DM_paper_x x c) (= mstarg/Gram-det = 0) - a TRANSPOSED, different rank
  drop the omega-partial engines do NOT cover. So the charts_Nn bundles need a
  chart built from the MOMENT-map x-Jacobian rank-drop, fed to
  negligible_singular_image_2n (which IS the right x-partial tool, Sard, now in
  scope). negligible_singular_image_2n is the engine; the missing piece is
  CONSTRUCTING the chart map/Crit set for the determinantal rank-drop locus.
- BLOCKER: that construction needs mstarg / surj_iff_mstarg / m_star analyticity
  - which live in Robust3, NOT in the Appendix heap reachable from dev files
  (which import only Robust2). So the cores CANNOT be finished in a Robust2-dev
  file; they need Robust3 context. (charts_core_Nn also needs OPEN Omega -> fits
  D4's 2D region, not D3's 1-D arc.)
STRATEGIC FLOOR REACHED: the autonomous dev-file grind is exhausted - the two
remaining cores need Robust3-resident mstarg machinery. NEXT = CONSOLIDATE the
proven M5 scaffolding into Robust3 at L970 (where mstarg + meager_rank_deficient_
stratum live), discharging the splice freebies, leaving the two charts_Nn cores
as the final sorries to crack WITH mstarg in scope. Big careful integration
(~13-min full Robust3 build); user-directed.

### gradU=0 SOUNDNESS FIX + Lmat_apply opt (2026-06-19)
While attacking the charts cores, found a THIRD soundness bug (codim count,
user-prompted): the dev D3 chain dropped gradU=0 - BadXW = {EX w. cvec!=0 &
~surj} = {mstarg(cvec w) x = 0}. Over a 1-D arc that is ONE equation (codim 1
per fixed w) which SWEEPS to codim 0 (full measure, NON-meager) as w varies ->
excess_arc_charts_Nn was FALSE as stated. D4's BadXGW already kept gradU=0
(sound). FIX: retain gradU=0 (BadXWG); bad locus {gradU=0 & mstarg=0} is codim 3
(2 gradient eqs + 1 determinantal) -> x-projection negligible. Stopped the
consolidation executor (it was grafting the unsound D3) + the prior core-proof
(proving a false lemma); reset the half-graft. Re-ran corrected:
- M5_Dev_D3fix (BUILD_EXIT=0): D3 re-stated over BadXWG, all gradU-agnostic
  threading + the corrected connector m5_D34_D3_collinear_fixed proven sorry-free;
  reduced to ONE true sorry excess_arc_charts_Nn (codim-3). Design agent
  independently confirmed "D3 is FALSE as stated".
- M5_Dev_D4fix (BUILD_EXIT=0): branchP_indep_charts_Nn, codim-3, sound.
- Lmat_apply optimized to a single `by (simp add: vec_eq_iff forall_6 ...)`
  (commit 0364557), verified green in jEdit + isolated heap build.
GENUINE FRONTIER = 3 TRUE, provable analytic cores (no longer chasing false
lemmas): (i) excess_arc_charts_Nn (D3 arc chart), (ii) branchP_indep_charts_Nn
(D4 region chart) - BOTH reduce to a SHARED need: a negligible-projection /
charts engine for the codim-3 joint locus {Gjoint=(gradU,mstarg)=0}, i.e. a
codomain-real^3 generalization of charts_core_Nn; crux = is 0 a REGULAR VALUE of
Gjoint (submersion) on the bad locus -> codim-3 manifold -> projection
non-surjective -> negligible_singular_image_2n. (iii) collinear_locus_finite_arc_
cover (finite C1-arc cover of the analytic curve {crossTheta=0}; needs a
real-analytic curve-structure / continuous-IFT result). All research-grade IFT;
the framing is now sound, the math is standard, the mechanization is the work.

### M5 Core (iii) curve-cover GREEN: collinear_locus_finite_arc_cover (2026-06-19, cont.)
Resumed post-crash. Verification discipline: trust BUILD_EXIT, not commit logs
(parallel-agent files had parked on the heap lock => were never build-verified).
Drove M5_Dev_curvecover/Scratch_m5_curvecover.thy to a GENUINE green build
(BUILD_EXIT=0, "Finished Applied_Math_M5_curvecover", ~4s on warm Appendix heap):
- collinear_locus_finite_arc_cover now PROVEN modulo ONE intended sorry,
  locus_locally_C1_arc (the local IFT-graph of the separable equation
  crossTheta = crossA(w1)cos w2 + crossB(w1)sin w2 + crossG(w1) = 0).
- Entire assembly sorry-free: phase_collinear<->crossTheta=0, the separable-trig
  reduction (K-factored crossTheta_separable_abstract), continuity, compactness
  (compact_crossTheta_locus), Heine-Borel finite subcover, nat-reindexing via
  the_inv_into, box containment.
- BUG FIXED (the L341 obtain failure): locus_locally_C1_arc obtained a
  nat-indexed family (r J g) with a NESTED where-clause "/\j. j:J ==> ...".
  `obtain ... by (rule L[OF ...])` left a residual that auto-`assumption` cannot
  close (it won't HO-match a rule-shaped premise against an assumption).
  FIX: restate the obtains to yield a finite SET A of arcs (all-atomic
  where-clauses "ALL g:A. ..."); matches the downstream set-based `good`
  predicate, so the g`J repackaging vanishes too. Mathematically identical.
  Committed e68046a (pushed; origin/main==HEAD verified).
BASELINE RE-VERIFIED (BUILD_EXIT=0, up-to-date): D3fix (1 genuine sorry
excess_arc_charts_Nn + 3 mstarg freebies), D4fix (1 genuine
branchP_indep_charts_Nn + 4 freebies), skeleton (M5 assembly green; D2/D5/D34
stubs). gdip2/Kfinite sorry-free.
GENUINE OPEN MATH (honest frontier): D2 (beam-center, det-Hessian covariance
poly; gdip2+Kfinite done), D5 (steering-singular, M6 reuse), the SHARED chart
crux (excess_arc_charts_Nn + branchP_indep_charts_Nn = codomain-real^3 charts_
core_Nn + Gjoint omega-partial submersion + negligible Sigma), and
locus_locally_C1_arc (scalar IFT, explicit arccos branches). Next: engine-map
sweep (charts_core_Nn shape, IFT availability) to choose chart-crux vs
curve-cover residual as the next target.

### M5 PARALLEL SOUNDNESS AUDIT — 2 more bugs caught (2026-06-19, cont.)
User: "proceed autonomously and in parallel". Builds serialize (heap lock) + subagents
CANNOT isabelle build, so MATH analysis was parallelized (3 read-only agents), VERIFICATION
stays serial w/ me. Both deep cores had latent soundness gaps — caught BEFORE grinding:

(A) Chart-engine audit (charts_core_Nn_gen): the chart-EXTRACTION half is generic
(bad_zero_chart, chart_proj_surj_iff, exists_surj_deriv_iff_partial all 'b::euclidean_space).
Only crit_piece_compact (Paper:1486, det_2) is real^2-bound. BUT bad_zero_chart REQUIRES
domain = 'c x 'b with codomain = 2nd factor 'b; Gjoint has param real^2 != codom real^3, so
the "real^3 generalization" needs a domain RE-SPLIT (abstract (2N-1)-dim 'c (+) real^3), not
just codomain relaxation. Deeper than the headers claimed.

(B) **Gjoint regular value is FALSE unconditionally.** At a bad point with det HessU=0 AND
~surj(DM_paper_x) the joint (gradU,mstarg) Jacobian has rank<=2<3 (x-block rank<=1: moment
drop + d_x mstarg=0 at the Gram min; omega-block 3x2 rank<=2, collapses when det HessU=0).
D4fix/D3fix excess_arc_charts_Nn / branchP_indep_charts_Nn via an unconditional Gjoint
submersion would be UNSOUND. D4eng quarantines it via a Sigma0 excision but leans on
Sigma0_bad_charts (D4eng:328) = UNPROVEN, no nondeg hyps, "not credibly true". SOUND ROUTE:
split on det HessU. det HessU=0 part charts via HEAP charts_core_Nn[G=gradU] DIRECTLY --
verified not_surj_omega_deriv_iff_detHess_dip (Robust1:4245): ~surj(omega-partial gradU) <-->
det HessU=0. det HessU!=0 part = moment-rank-drop content (the real D-work).

(C) **locus_locally_C1_arc (curve-cover core iii) was FALSE as committed (e68046a)** -- unsound
by omission. Ac=Bc=0 (kx w0=kx ws AND ky w0=ky ws) => crossTheta == G(w1) == 0 => locus = whole
2-D box, NOT arc-coverable. FIXED (e750e1f): added hsep (kz ws!=kz w0) + kdiff; threaded
through both consumers; rebuilt green. WITH kdiff the singular set {crossTheta=0 & d1=d2=0}
forces A^2+B^2=G^2, a degree-<=2 poly in cos(w1) (leading coeff = sum of 3 squares, !=0 iff
kdiff) => FINITE. Curve-cover body is now SOUND + CLOSEABLE: regular case = explicit
arcsin/arccos graph arc (axis-scaleR C1 pasting, NOT the abstract IFT which gives open-U/
differentiable_on); singular case = finite point/branch cover; needs 2 short helpers
(finite_cos_eq_zeros_interval, finite_inhom_phase_zeros_interval = c!=0 ext of
finite_phase_zeros_interval). ~150-300 lines, NO WALL (per-w1 slice is elementary
a*cos+b*sin+c=0, <=2 branches -> explicit finite arsenal, no Puiseux/analytic-branch theory).
NEXT (sound, tractable): implement the curve-cover body. Chart cores need the det-HessU
re-architecture (bigger). See M5_ENGINE_MAP.md for both.

### M5 core iii body: foundations proven (helpers + derivative bridge) (2026-06-19, cont.)
"ultrathink" pass on locus_locally_C1_arc. Soundness fix landed first (e750e1f: kdiff
required). Then proved + committed the body's FOUNDATIONS (all build green):
- 40061e5: finite_cos_eq_zeros_interval (cos t=K, two-coset cos_eq) +
  finite_inhom_phase_zeros_interval (a cos+b sin=k, two-coset sin_eq). The inhomogeneous
  (k!=0) extensions of the heap finite-zeros lemmas. TRAPS hit: use Set.set_eqI (qualified,
  bare is shadowed); `by m1 m2` errors "No subgoals" when m1 already closes (drop the
  redundant terminal); {S}={} ==> finite S needs `unfolding empty by simp` (plain simp
  rewrites the set-eq into pointwise form, not {}).
- 07db9a1: has_derivative_crossTheta -- Frechet derivative w/ explicit partials d1,d2 via
  crossTheta_separable + derivative_eq_intros + algebra_simps. TRAP: defines Ac/Bc need
  ω0,ωs FIXED (they're free in the file) -> add `fixes ω0 ωs ω`.

REMAINING BODY ROADMAP (~250 lines, NO WALL, one hard keystone). Build serially.
(1) finite_crossTheta_singular: {ω∈OmegaPF. crossTheta=0 ∧ d1=0 ∧ d2=0} finite.
    Math settled: d2=0 ∧ crossTheta=0 ⟹ A²+B²=Gt² (rotation identity, A=Bc-p cos ω1,
    B=-Ac+q cos ω1, Gt=r sin ω1, p=Bc kzs+kys, q=Ac kzs+kxs, r=Ac kys-Bc kxs);
    A²+B²-Gt² = (p²+q²+r²)c² -2(Bc p+Ac q)c + (Ac²+Bc²-r²), quadratic in c=cos ω1, the
    poly [:Ac²+Bc²-r², -2(Bc p+Ac q), p²+q²+r²:] != 0 under kdiff (if leading=0 then
    p=q=r=0 then const=Ac²+Bc²!=0) -> poly_roots_finite -> finite cos-ω1 values ->
    finite_cos_eq_zeros_interval -> finite S1 of ω1. Per ω1∈S1, ω2-slice finite: case
    (A,B)≠0 -> crossTheta=0 finite (finite_inhom_phase); case (A,B)=0 -> Gt=0 &
    (p,q)≠0 (else ¬kdiff) -> d1=0 nontrivial phase finite. Assemble via Sigma +
    finite_SigmaI + image (pattern: meager_steering_singular_stratum_scratch Ksub/finK,
    Scratch_g3_asm:281-335). NOTE: must cut by d1 too (d2=0∧crossTheta=0 alone can be a
    full vertical slice when A=B=Gt=0).
(2) SCALAR IFT keystone (the crux): C¹ ψ with crossTheta(s,ψ s)=0 near ω' off d2=0, from
    regular_value_local_chart (Regular_Value_Theorem:279): transport real^2↔real×real via
    ι(s,t)=s*axis 1 1+t*axis 2 1; G=crossTheta∘ι; regular = ∇crossTheta(ω')≠0 (here d2≠0).
    Extract closed-interval C1_differentiable_on ψ (continuity of Dφ) + LOCAL UNIQUENESS
    (locus∩ball ⊆ graph) from the homeomorphism/relatively-open clause.
(3) regular case: d2≠0 -> 1 graph arc (λt. t*axis 1 1+ψ t*axis 2 1)`[a,b]; d1≠0 symmetric.
(4) singular case: ω'∈Ssing isolated (finite (1)); pick r<dist(ω',Ssing\{ω'}); cover
    locus∩ball ω' r by analytic_arc_singleton {ω'} + ≤2 graph branches per orientation
    (≤2-per-ω1: a cos+b sin+c=0 over the 2π ω2-range has ≤2 sols).
(5) assembly: case-split ∇crossTheta(ω')=0? via has_derivative_crossTheta (∇=0 ⟺ d1=d2=0).
Helpers (1)-finite + the bridge are DONE; (2) is the only genuinely hard piece.

### M5 core iii: scalar IFT keystone — injectivity + fibre-derivative VERIFIED (2026-06-19, cont.)
"grind the scalar IFT keystone". Chose the BLINFUN-FREE route: invariance_of_domain for
existence of the continuous local inverse + has_derivative_inverse_basic_x (Derivative.thy:1188)
for the derivative (gives psi' = -d1/d2 explicitly => C1 for free, no operator-inverse
continuity, no blinfun topology). Verified + committed (19870e5):
- has_field_derivative_crossTheta_t: 1-D fibre deriv d2 = -crossA*sin + crossB*cos (via the
  separable form restricted to u |-> (s,u): crossA*cos u+crossB*sin u+const).
- continuous_on_crossTheta_t_partial.
- crossTheta_graph_inj: H(z)=vector[z1,crossTheta z] is inj_on (ball omega' eps) where d2!=0,
  via Rolle on the vertical fibre (two equal-crossTheta omega2's would force a zero of d2).
  GRIND TRAPS hit (all fixed): (a) parse-ambiguous `$` when `for z z'` left them UNTYPED ->
  annotate `for z z' :: real^2`; (b) `lambda` is reserved -> use alpha; (c) bare vec_eq_iff is
  JNF-shadowed (no-op) -> Finite_Cartesian_Product.vec_eq_iff; (d) convex-segment membership
  needs explicit exI witness; (e) `define f where "f u=..."` is pointwise -> use
  "f=(%u....)" so has_real_derivative sees f as a function; (f) DERIV_isCont +
  continuous_at_imp_continuous_on for continuity; (g) defines need ω0 ωs FIXED.

REMAINING KEYSTONE (clear path, verified foundations; ~100 lines):
(2a) crossTheta_graph_homeo: from crossTheta_graph_inj + H continuous +
     invariance_of_domain_homeomorphism (Further_Topology:2288) => g=inv, homeomorphism
     (ball) (H`ball) H g, open (H`ball). [~15 lines]
(2b) C1 graph: phi(s)=g(vector[s,0]) for s near omega'1 (vector[s,0]∈H`ball, open). phi$1=s,
     crossTheta(phi s)=0 (H(g y)=y). phi(omega'1)=omega' (g(H z)=z). DERIVATIVE via
     has_derivative_inverse_basic_x at x=phi s: provide g'_x = (%k. vector[k1, (k2-d1*k1)/d2]),
     bounded_linear, g'_x o H'_x = id (H'_x from has_derivative_crossTheta + vec_nth) =>
     g has_derivative g'_x at vector[s,0] => phi has_vector_derivative vector[1, -d1/d2] =>
     C1 (continuous, d2!=0). [~60 lines]
(2c) regular case of locus_locally_C1_arc: the analytic_arc = phi`[a,b]; covering from the
     homeomorphism's relative-openness; box containment by restricting [a,b]. [~30 lines]
(3) singular case: finite Ssing (roadmap above) => omega' isolated => point + <=2 branch arcs.
The injectivity (the conceptual crux, Rolle) is DONE; (2b) the derivative is the next grind.

### M5 core iii: crossTheta_local_C1_graph FULLY PROVEN — sorry-free (2026-06-20)
"use the cli tools eval and Sledgehammer to de-sorry". INSTALLED `isabelle eval_at` +
`isabelle desorry` (repo's isa_agentic_cli_tools, via install.sh -> scala_build). These
unblocked everything — see [[isabelle-eval-at-and-desorry-cli]].

**THE 14-MIN HANG, DIAGNOSED + KILLED.** Root cause: the homeo `obtain` consumed
crossTheta_graph_homeo via `... unfolding <defs> by metis` — a NON-INTERRUPTIBLE
first-order metis loop reconciling the defines-unfolded forms (this is why `-o timeout=90`
never fired; eval_at -t showed it instantly as the runaway line). Fix: `by (rule
crossTheta_graph_homeo[OF d2[unfolded ...]])` after `unfolding H_def D2_def Ac_def Bc_def`
-> **0.005s**. For the `rule` consumption to CLOSE, the obtains avoid-clause had to be
ATOMIC (`∀z∈ball. ...`, not nested `⋀z. z∈ball ⟹ ...`) on BOTH crossTheta_graph_homeo
and the local obtain — same atomic-clause fix as the curve-cover assembly.

(2b)+(2c-partial) DONE: crossTheta_local_C1_graph now provides, off d2=∂₂Θ(ω')≠0, a genuine
C¹ graph φ(s)=g(vector[s,0]) over s=ω₁ with φ C1_differentiable_on {a..b}, φ s$1=s,
crossTheta(φ s)=0, φ(ω'1)=ω', and {ω. crossTheta=0}∩ball ω' (min ε (η/2)) ⊆ φ`{a..b}.
Cascade of eval_at-pinpointed fixes (each ~35s/cycle, FAR better than mystery builds):
- ginv_bl: gi x is linear UNCONDITIONALLY (even D2=0, since _/0=0) -> prove `linear (gi x)`
  via explicit linearI (field_simps with `that` in each subgoal) then linear_conv_bounded_linear.
- ginv_id / phivec moreover: `using <D2≠0> by (rule ext)(simp ...)` FAILS — chained fact hits
  `rule ext` which can't consume it; move the ≠0 fact INTO the simp set.
- v0in: image_eqI multiple-unifiers -> `by (metis ... imageI ...)`.
- iotacont/iotader: `vector[s,0]` head is `vector` not vec_lambda so continuous_on_vec_lambda /
  has_derivative_graph_map (wants vector INPUT z$1) FAIL -> rewrite `vector[u,0]=u*⇩R axis 1 1`,
  then continuous_intros / derivative_eq_intros.
- sopen: `open_vimage[OF openimg iotacont]` (find_theorems-confirmed) + vimage_def.
- phi1: `metis vector_2` can't bridge H(φs)$1 to (φs)$1 -> structured like phi0 (unfold H_def).
- ab_in: split the `s∈ball(ω'1)η` step then apply ηin by blast.
- the velocity field's derivative: `has_derivative_compose` mismatches the ∘-form derivative ->
  `diff_chain_at` (∘ throughout, find_theorems-confirmed); avoid over-unfolding φ_def by
  proving for the bare `g∘(λs.vector[s,0])` then folding via `simp add: φ_def comp_def`.
- velcont: auto's continuous_intros re-decomposes -D1/D2 (fires continuous_on_divide) -> explicit
  `intro continuous_on_add continuous_on_scaleR continuous_on_const kcont`.
- final covering show: named `rule that[where a=a and b=b and φ=φ and r="min ε (η/2)"]` (positional
  mis-slots due to obtains `and`-grouping); ω$1∈{a..b} via component_le_norm_cart + smt (linear).
isabelle build Applied_Math_M5_curvecover: **BUILD_EXIT=0, Finished 12s**. Committed dc12da7, pushed.

REMAINING for locus_locally_C1_arc (the file's one intended sorry): assemble 𝒜 from
crossTheta_local_C1_graph in the d2≠0 case (need: φ`{a..b} is an analytic_arc [C¹ image] and
⊆ OmegaPF), PLUS the d2=0 cases — ∂₂Θ=0∧∂₁Θ≠0 needs a SYMMETRIC χ-graph (ω₁=χ(ω₂), a near-copy
of crossTheta_local_C1_graph with roles swapped), and the finitely-many ∂₁Θ=∂₂Θ=0 singular
points (governed by the finite-zeros lemmas; crossA²+crossB²=crossG² cuts ω₁ to finite). The
singular-point local branch structure is the genuine hard residual.

### M5 core iii: chi-graph PROVEN via PARALLEL AGENTS + CASE B1 (2026-06-20, cont.)
"Push on to the chi-graph ... make types explicit when you fix ... use multiple agents in
parallel." Did exactly that. The chi-graph (graph over omega_2 where the omega_1-partial !=0)
is the symmetric mirror of the proven phi-graph. Decomposed into 2 PARALLEL sub-agents that
each DRAFTED and SELF-VERIFIED (via `isabelle eval_at` on their own scratch copies -- the
Appendix heap is read-only/prebuilt so concurrent eval_at is fine) with interface signatures
PINNED so integration was clean:
- Agent A (foundation chain, self-contained, real deps): has_field_derivative_crossTheta_s,
  has_derivative_graph_map_vert, crossTheta_graph_inj_vert, crossTheta_graph_homeo_vert.
- Agent B (main): crossTheta_local_C1_graph_vert, verified against the 2 STUBBED prerequisites
  (graph_map_vert + homeo_vert) -- then re-verified here against the REAL ones.
Both returned GREEN, sorry-free. I added locus_arc_cover_from_graph_vert (omega_2 box-containment
mirror) myself. Assembled all 6 into the file (reconstruction script: 1095->1565 lines),
full build BUILD_EXIT=0 FIRST TIME (the pinned-signature + faithful-mirror discipline paid off).
Then wired CASE B1 into locus_locally_C1_arc: cases (interior) -> {d2!=0: phi (CASE A) | d2=0 &
d1!=0: chi (CASE B1)} ; the residual sorry is now ONLY the gradTheta=0 singular points (finite,
hard kernel) UNION the box boundary. BUILD_EXIT=0, committed 0e1dc7b.
KEY LESSONS: (1) every `fix`/`obtain`/bound var typed `:: real^2`/`:: real` -- avoids the
`$` vec_nth parse-ambiguity (Agent B hit it once: tight `*sin` tokenizes as `*s in`, needs
spaces). (2) parallel draft+self-verify with PINNED interface signatures = clean splice +
green-first-build. (3) the metis-on-obtains-rule hang reappears in consumers -> always use
the structured `proof (rule <obtains-lemma>[OF ...]) fix..assume..show thesis`. See
[[isabelle-eval-at-and-desorry-cli]], [[parallel-agents-and-derivative-discipline]].

### M5 core iii: boundary + singular analysis via 4 PARALLEL AGENTS (2026-06-20, cont.)
"Some agents on the boundary case, some on the singular kernel." Ran 4 parallel agents
(draft+self-verify via eval_at on scratch copies); all returned, integrated, full build
BUILD_EXIT=0 (commit 6824e43):
- BOUNDARY (both GREEN): `locus_arc_cover_from_graph_bdry` (phi, box-CLIPPED: needs only
  omega_2-interior, any omega_1) + `locus_arc_cover_from_graph_vert_bdry` (chi, omega_1-interior).
  These SUBSUME the interior helpers. Used heap lemma `OmegaPF_component_bounds`.
- SINGULAR FINITENESS (SI-A, GREEN but CORRECTED): `finite_crossTheta_d2zero` -- the plan's
  "leading coeff = sum of 3 squares hence !=0" is FALSE (on the unit sphere all 3 vanish
  simultaneously). Needs extra hyp `g1 = Ac*ky_s - Bc*kx_s != 0`; counterexample: omega_s=(1,atan .5),
  omega_0=(.7,atan .5) has hsep+kdiff but g1=0 and a whole vertical fibre in the set => infinite.
  When g1=0 that fibre is itself a C1 arc (coverable downstream). `crossTheta_d2zero_sumsq`
  (A^2+B^2=G^2 reduction) integrated.
- SINGULAR COVER (SI-B, DECISIVE): genuine grad(Theta)=0 pts are NEVER isolated -- ALWAYS
  transverse crossings. Symbolic identity `det H_Theta = -E''/2` on {E=0,E'=0} (Groebner) with
  E''>0 always; 283+792 numerical singular pts ALL saddles, ZERO isolated. So the singleton route
  (isolated_locus_singleton_cover, verified) is sound but VACUOUS for real singular pts. The 1075
  numerical pts were EVIDENCE for the universal claim, not per-point obligations -- the proof is
  ONE generic crossing construction (finitely many singular pts per instance, given g1!=0).

NET: locus_locally_C1_arc now PROVES both regular orientations over the FULL box (interior AND
boundary). Single residual sorry = (a) interior transverse-crossing singular pts [needs the
two-branch Morse/rotated-coords chart HOL-Analysis lacks -- the IRREDUCIBLE kernel] + (b) box
boundary in the awkward orientation / corners. Strictly smaller than "all locus points".

### M5 CONSOLIDATION EXECUTED: meager_rank_deficient_stratum assembled; F0 build-checked (2026-06-22)
Executed the long-planned M5 splice (M5_CONSOLIDATION_PLAN.md). Replaced the lone bare
on-path `sorry` in `meager_rank_deficient_stratum` with the proven four-stratum `meager_Un`
of D1∪D2∪D5∪D34, grafting verbatim (via sed) from the proven M5_Dev_* sessions: D5
(m5_D5_steersing + gdip-helpers + beam-center Hessian), D2 (m5_D2_beamcenter), D34
(m5_D34_residual + phase_collinear), skeleton (m5_D1_regular + the 4-stratum assembly), and
`fixed_c_nonsurj_nowhere_dense` discharged in-place via the resident mstarg machinery
(surj_iff_mstarg + nowhere_dense_mstarg_zeros). Commit 81b65e1, pushed.

LEAN approach (NOT the full plan): no curvecover/Morse/Sard grafted. Three seams resolved:
- ω0/ωs are FREE vars at M5 (only local `define`s exist) => D5's m5_D5_steersing genuinely
  needs hsep (kz ωs≠kz ω0) + kdiff => threaded into the M5 signature + m5_D5_steersing +
  the call site, matching the existing M6 convention (Phi_bad_meager_dip already assumes
  and passes them; now M5 too).
- The D5 L486 kdiff-via-freebie was VESTIGIAL: the goal is pure frechet_derivative_at[OF cF].
  `by simp` FAILS there (user caught it in jEdit); `by metis` works; the chained `also` (L1381)
  needs `by (simp only: mult.assoc mult.commute)`.
- Robust3 moved Appendix/ -> Appendix/Robust3/ (Isabelle forbids two sessions sharing
  `in "Appendix"`); new leaf session Applied_Math_Appendix_Full on the prebuilt Appendix heap.

VERIFIED both ways: jEdit interactive prover (user) + batch BUILD_EXIT=0 + Finished
Applied_Math_Appendix_Full (4:36). F0_dip_nonempty is CI-build-checked for the FIRST time.
End-state: exactly 2 on-path sorries -- m5_D34_D3_collinear, m5_D34_D4_branchP (the D3/D4 IFT
chart-branch cores). 1->2 is decomposition, not regression (the single sorry stood for all of
M5; the two are its irreducible analytic cores; D1/D2/D5/D34 + the C¹ arc-cover all proven).
Stage B (optional next): graft curvecover+D3charts+D4charts to reduce the 2 bundles to the
canonical excess_arc_charts_Nn / branchP_indep_charts_Nn. See [[m5-consolidation-ready]],
[[m5-d2d5-machinery-map]], [[never-claim-unverified-builds]].

### D34 ANALYTIC ROUTE OPENED: elementary C^omega layer + merged bridge heap (2026-07-06)
"Heap image set up for the nonemptiness proof with the Real/Complex analytic developments
baked in (inverse + implicit function theorems). Consider what is left for a sorry-free
nonemptiness proof, assume no more than absolutely necessary; continue proving the next step."

STATE AUDIT first: HOL itself was rebuilt 2026-07-03, silently staling EVERY Applied_Math heap.
Rebuilt both chains (Nonemptiness->Appendix_Base->Appendix and HigherDiff->Analytic->Inverse->
Complex) -- all green in 6 min. Confirmed via grep + build: Robust3 still has EXACTLY the two
live sorries (m5_D34_D3_collinear L2424, branchP_indep_charts_Nn L2534); the analytic stack
(real_analytic_on, complexification A1/A2/A3, analytic IFT real_analytic_implicit_function,
majorant local inverse, multivariate real_analytic_nowhere_dense_zeros) is COMPLETE and sorry-free.

KEY REDUCTION INSIGHT (checked, not assumed): the D4 cover lemma's negligibility is consumed
ONLY through meager_negligible_closed_cover (Robust3 L2602) -- i.e. downstream uses MEAGER, not
measure. So the analytic route needs NO new negligible-zeros theorem: closed + nowhere-dense
pieces suffice, and real_analytic_nowhere_dense_zeros is already proven. The analytic plan:
 (1) all dipole fields are real-analytic [mechanical closure];
 (2) at gradU=0 & det HessU != 0, the ANALYTIC IFT gives an analytic critical graph w*(x);
     the local bad set is {x. h x = 0}, h x = mstarg (cvec_dip w0 ws (w* x)) x analytic;
 (3) {h=0} closed-in-chart + nowhere dense UNLESS h == 0 on a component -- the transversality
     witness is the ONLY genuine new math (plus the det HessU = 0 stratum, also analytic).

PROVEN + LANDED this session (all BUILD_EXIT=0):
- Elementary C^omega layer spliced into Real_Analytic_Complex.thy: has_holo_extension_at_sin/
  cos/rsinc, real_analytic_on_sin/cos/rsinc + _comp forms. Route: complexification bridge
  real_analytic_at_1d_iff_holo_extension + real_analytic_on_1d_iff, holomorphic witnesses via
  holomorphic_intros; the entire sinc kernel via removable_singularity + DERIV_sin at 0 (the
  has_field_derivative_iff difference-quotient trick gives sin z / z --> 1 for free).
  GOTCHA: `intro exI[of _ 1] conjI` on (EX r>0. EX g. ...) re-applies exI[of _ 1] to the INNER
  EX g (instantiating g to the constant-1 function!) -> drop conjI, use (intro exI[of _ 1]) simp
  with the EX g fact chained. Dev scratch M5_Dev_AnalyticElem (stub after consolidation).
- NEW SESSION Applied_Math_D34_Analytic (Appendix/AnalyticBridge/D34_Analytic_Bridge.thy):
  ONE heap = Appendix (through Robust2) + the full analytic stack, the interactive platform for
  the D34 discharge. Layer 1 (omega-side fields) PROVEN: real_analytic_on_gsinc (gsinc = rsinc),
  _vec_nth, _kx/_ky/_kz, _gdip, _gain_dip, _cvec_dip [omega0/omegas free, constant denominators
  -- no divide closure needed, no new assumptions].
NEXT: layer 2 = joint (c,x)-analyticity of the moment fields: phase c y n = cis(-(c . y$n)) is
componentwise (cos,sin) of a bilinear form -> real_analytic_on_componentwise; moments/DM_paper_x
entries = finite phase-polynomial sums; mstarg = det(matrix(Gram)) = polynomial in entries.
NOTE: mstarg/transC layering -- transC lives in Moment_Jacobian (in bridge scope), mstarg is
DEFINED in Robust3 L560; when Robust3 later imports the bridge, MOVE the mstarg definition into
the bridge (name clash otherwise). Then layer 3 = the IFT chart engine + the transversality
witness (the genuine core), and the det-HessU=0 stratum.

### D34 ANALYTIC BRIDGE LAYER 2: moments + mstarg jointly real-analytic (2026-07-06, cont.)
"Prove the joint (c,x)-analyticity of the moments and mstarg." Done, spliced into
D34_Analytic_Bridge.thy, dev in M5_Dev_AnalyticMoments (stub after consolidation).

GENERIC CLOSURE KIT (candidates to upstream into Real_Analytic/_Complex): real_analytic_on_
inner (joint f.g via the euclidean_inner Basis expansion), _uminus, _Re/_Im (inner_component
at 1/i + inner_complex_def), _Complex (componentwise over Basis_complex_def), _cmult (complex
product via Re/Im split + complex_eq_iff), _of_real (bounded_linear_of_real), _cis
(cis = Complex(cos,sin)), _scaleR_complex (scaleR_conv_of_real), _det (det_def: finite
permutation sum of entry products), and matrix_gram_entry: for linear A,
matrix (A o adjoint A) $i$j = SUM_{b in Basis} (A b $i)(A b $j) -- adjoint_works twice +
euclidean_inner; this is what makes mstarg a polynomial in analytic entry fields, over an
ABSTRACT Basis (no 24-fold basis enumeration!).

DIPOLE LAYER: phase/d_phase joint (cis of bilinear form), the six moments, the six
D*_paper_x Jacobian components, transC entry fields (exhaust_12 + transC_def + DM_paper_x_def),
linear_DM_paper_x (structured, no metis), mstarg (defined in the bridge, verbatim Robust3),
real_analytic_on_mstarg (JOINT on UNIV), + corollaries real_analytic_on_mstarg_x (fixed c)
and real_analytic_on_mstarg_cvec ((x,omega) |-> mstarg (cvec_dip w0 ws omega) x -- the layer-3
h-precursor).

GOTCHAS (merged D34 heap): (1) `$` is PARSE-AMBIGUOUS (HMA's $h/$v survive typing) -- lemma
STATEMENTS must spell vec_nth (prints as $; defs/proof-level rewriting unaffected). (2)
finite_UNIV resolves to Cardinality's Phantom constant -- use the plain type-class fact
`finite`. (3) TWO DM_paper_x constants: unqualified = Nonemptiness_Paper.DM_paper_x
(components DA/DM1/DM2/DM11/DM12/DM22_paper_x; THIS is what mstarg/Robust3 use), shadowing
Moment_Map.DM_paper_x (components d_*_moment_x; kept analytic too, both proven). (4) metis
hangs in the merged heap -- all proofs are rule/intro chains.

NEXT (layer 3): the analytic IFT chart engine -- U_cart/gradU joint (x,omega)-analyticity,
then at gradU=0 & det HessU != 0 apply real_analytic_implicit_function to get the analytic
critical graph omega*(x); local bad set = {x. h x = 0} with h = mstarg_cvec o graph, closed +
nowhere dense by real_analytic_nowhere_dense_zeros UNLESS h == 0 on a component (the
transversality witness -- the genuine core), plus the det HessU = 0 stratum.

### D34 ANALYTIC BRIDGE LAYER 3: the IFT chart engine PROVEN (2026-07-06, cont.)
"Prove layer 3 now." Done -- green on the FIRST full eval_at pass, spliced into
D34_Analytic_Bridge.thy (dev: M5_Dev_AnalyticIFT, stub after consolidation).

NEW GENERIC FACTS (upstream candidates): real_analytic_at_1d_deriv / real_analytic_on_deriv_1d
-- deriv of a 1-D real-analytic function is real-analytic. Proof: holomorphic extension g;
deriv g holomorphic (holomorphic_deriv); deriv g extends deriv f: differentiate t |-> g(of_real t)
= of_real(f t) (has_derivative_transform_within_open on the real ball), postcompose Re => DERIV f
= Re(deriv g); postcompose Im: the constant-0 function forces Im(deriv g)=0 by
has_derivative_unique + fun_cong at 1. Also real_analytic_on_cnj / _cmod_sq.

DIPOLE LAYER: real_analytic_on_deriv_gdip (via the deriv lemma -- NO explicit gsinc'/Jsinc
formula needed!), DERIV_gdip + frechet_gdip_eq (via real_analytic_on_has_derivative_Dblinfun +
DERIV_deriv_iff_real_differentiable), A_cart/Dcvec_dip-applied/dA_cart joint analyticity, and
real_analytic_on_gradU_dip: the dipole gradient field is real-analytic JOINTLY in (x,omega) --
by rewriting through gradU_explicit[OF has_derivative_cvec_dip gain_dip_has_derivative] and
closing the explicit dU_cart body with the layer-2 kit. bij_matrix_vector_mult (det != 0 => bij,
metis-free via the invertible_def two-sided inverse).

THE ENGINE: dip_critical_graph_dichotomy. At gradU(x0,wb)=0 & det HessU(x0,wb) != 0:
real_analytic_implicit_function (F = gradU-joint on UNIV; reg from gradU_dip_has_derivative +
bij) gives U g; shrink to a BALL B (connected!); g real-analytic on B (real_analytic_on_open_
subset); gradU x (g x) = 0 on B; h x = mstarg (cvec_dip w0 ws (g x)) x real-analytic on B
(pair-compose with layer-2 real_analytic_on_mstarg_cvec); then EITHER h == 0 on B OR
interior(closure {x in B. h x = 0}) = {} (real_analytic_nowhere_dense_zeros). Assumes ONLY the
critical-point data. Consumed the obtains-rule discipline: show ?thesis proof (rule
real_analytic_implicit_function[OF ...]) fix U g assume ... show thesis by (rule that[OF ...]).

REMAINING (the honest residue, see the session audit): (4a) LOCAL UNIQUENESS of the critical
graph (bad points near (x0,wb) lie ON the graph) -- needs an implicit-function variant exposing
the injectivity neighbourhood (re-derive from real_analytic_local_inverse's homeomorphism, or
C1 inverse function theorem on Phi(x,w)=(x,gradU)); (4b) the TRANSVERSALITY WITNESS -- exclude
h == 0 on a component (the genuine new mathematics; per-component witness by the identity
theorem); (4c) the DEGENERATE stratum det HessU = 0; (5) the Robust3 splice: cover both D3/D4
sorries by countably many dichotomy charts + the degenerate/collinear strata, rewire
Robust3 to import the bridge (move its mstarg def), weaken the D4 cover lemma to
closed+nowhere-dense pieces (downstream only uses meager via meager_negligible_closed_cover).

### D34 ANALYTIC BRIDGE LAYER 4a: critical-graph LOCAL UNIQUENESS (2026-07-06, cont.)
"Show 4a." Done -- spliced into D34_Analytic_Bridge.thy (dev: M5_Dev_AnalyticUnique, stubbed).

real_analytic_implicit_function_unique: the analytic IFT additionally exposing the
local-inverse neighbourhood N of (x0,y0) on which the solution graph is the ONLY zero
locus: obtains U N g with open U/N, (x0,y0) in N <= W, the graph solves F=0 with
(x, g x) in N on U, AND forall x in U, y: (x,y) in N --> F(x,y)=0 --> y = g x.
PROOF = the real_analytic_implicit_function assembly mirrored VERBATIM (programmatic
extraction of the proof body!) + two new paragraphs: solutionN ((x,gx) = Psi(x,0) in U')
and unique (Phi(x,y) = (x,0) = Phi(x,gx); homeomorphism_apply1 injectivity => y = g x).
Green modulo ONE merged-heap gotcha: the token `inv` is claimed by algebra structure
syntax (m_inv) in this heap -- "Illegal reference to implicit structure" -- spell
`inv_into UNIV` (the abbreviation's expansion; surj_f_inv_f / inv_f_f still apply).

dip_critical_graph_dichotomy_unique: the COMPLETE chart engine. At gradU(x0,wb)=0 &
det HessU != 0: connected chart B, uniqueness nbhd N of (x0,wb), real-analytic graph g,
gradU x (g x) = 0 & (x,gx) in N on B, every critical (x,w) in N over B lies ON the graph
(w = g x), and the mstarg-along-graph dichotomy. This is everything the D34 covering
argument needs from a single chart. Remaining: 4b transversality witness, 4c degenerate
stratum, 5 Robust3 splice (see previous entry's audit).

### D34 LAYER 4b OPENED: witness interface + the Case-B source map (2026-07-06, cont.)
"Focus on 4b (the transversality witness)." Two deliverables:

(1) INTERFACE PROVEN: dip_critical_chart_nowhere_dense (bridge). Upgrades the chart
engine's dichotomy to an UNCONDITIONAL interior(closure {bad}) = {} conclusion under ONE
hypothesis `wit` (a witness point on every connected real-analytic critical chart through
the bad basepoint with cvec != 0 along the graph -- the exact 4b obligation, threaded like
`nd`). Engine adds a continuity shrink (cvec o g != 0 on a ball): analytic => derivative
(real_analytic_on_has_derivative_Dblinfun) => isCont => continuous_open_preimage. GOTCHAS:
real_analytic_on_imp_continuous is REAL-VALUED only (route vector-valued continuity through
the derivative); `open (- {0})` needs explicit open_Compl[OF closed_singleton] under this
simp set.

(2) SOURCE LOCATED + PLAN (D34_WITNESS_PLAN.md): the genuine 4b mathematics is the paper's
Case-B appendix (nonemptiness_unified_singlefile_complete.tex app:caseB, ~3579-6253,
cor:caseBmeager): branch decomposition in c-adapted coordinates over a good triple
(lem_twotriplecover -- ALREADY FORMALIZED, Nonemptiness_Paper:848), four branch families
(vpair22-full / uphi-exhausted / Lambda-closed / H11-closed) each with an explicit
cofactor-determinant certificate. KEY REDUCTION: `wit` needs only the LOCAL form -- a
chart inside the bad locus forces an explicit analytic certificate Xi == 0 on the chart,
contradicted via real_analytic_nowhere_dense_zeros -- NOT the full meager projection.
The paper's status section confirms lem:block (J5, det = -32 g^5 a^5) and lem:3x3
(det = +-8 g^3 a^3 H_*) as its formalized-elsewhere inputs; verify coverage against
BlockDet before porting. 4c (det HessU = 0 stratum) has the same source pattern:
app:H0res / prop:h0res-meager.

### D34 LAYER 4b STEP 2: the good-triple layer PROVEN (2026-07-06, cont.)
"Do it" (execute witness plan steps 1-3; and: audits must include the paper source, noted).
Landed in the bridge (dev: M5_Dev_GoodTriple, stubbed): triple_good/_t_distinct/_distinct,
edge_det2 + common_perp_edge_det2 (common perpendicular in R^2 kills the 2x2 det - proven by
the two c-component eliminations, no metis), triples_transverse + two_triple_cover_pointwise
(nine nonzero cross-edge dets => every c != 0 is good for one of the two triples - the
POINTWISE lem:twotriplecover; its failure is an explicit polynomial certificate = the future
no-good-triple-stratum Xi), triple_good_chart_persist (basepoint goodness survives on a
shrunk ball; same analytic->isCont->open-preimage shrink as the engine).
NEW MERGED-HEAP GOTCHAS: plain vec_eq_iff can resolve against JNF's Matrix.vec - qualify
Finite_Cartesian_Product.vec_eq_iff; open (A Int V1 Int V2 Int V3) from open (A Int Vi)
pieces needs explicit re-association before open_Int.
INVENTORY (now complete, in D34_WITNESS_PLAN.md): applyT family split - M12/M_paper laws at
Robust3:5/99 are OUTSIDE bridge scope (migrate for the rotation layer); BlockDet houses the
part-II minor ladder (Bblk/Ablk/Cblk/bigJ); transport convention transpose T *v c = c0_paper
= vector [1,0]. NEXT: step 1 remainder (concrete T(c) witness matrix; migrate M12/M_paper
applyT), then step 3 (gauge-fixed quantities vs the K/L/M cofactors, tex 3650-3710).

### D34 LAYER 4b STEP 1 (entry point): the c-adapted transport matrix (2026-07-06, cont.)
cadapt c = matrix with columns c/|c|^2 and c-perp: cadapt_transport (transpose (cadapt c)
*v c = c0_paper -- the exact convention of the applyT moment laws), cadapt_det (= 1),
cadapt_invertible. Green on first pass (component computation via exhaust_2 +
matrix_vector_mult_def + sum_2; det via det_2). Spliced into the bridge. Still open in
step 1: migrate M12_moment_applyT / M_paper_applyT (Robust3:5/99) into bridge scope.

### D34 LAYER 4b STEP 1 COMPLETE: transport laws migrated (2026-07-06, cont.)
M12_moment_applyT, M_paper_applyT, applyT_linear, applyT_surj migrated from the top of
Robust3 into the bridge. NOT verbatim-viable: the $ forms that parse in seconds on the
Appendix heap PARSE-HANG >10 min in the merged D34 heap (super-linear $-overload cost,
now MEASURED: killed a batch build at 10+ min stuck in parsing; vec_nth version checks
in ~25 s). All statement AND proof-level $ rewritten to vec_nth; consider-metis ->
exhaust_6[of i] + blast. Robust3 keeps its local copies until the layer-5 rewire
(then DELETE L5-155, L322-341). c-adapted transport entry point now complete in the
bridge (cadapt + the six moment transport laws + M_paper bundle + linear/surj).

### D34 LAYER 4b STEP 3 (foundation): division closure + the Case-B cofactors (2026-07-06, cont.)
Division closure added to the kit: has_holo_extension_at_inverse (witness 1/z on
ball(c,|c|)), real_analytic_on_inverse_1d on -{0}, _inverse_comp, _divide -- unblocks the
branch gauge quantities (G22 = H11 - H12^2/H22). det3 primitive + closure. tcoord/wcoord
(kappa-scaled u/v coordinates; wcoord = edge_det2 c p) + closure. The three familiar
cofactors cofK/cofL/cofM (tex 3650) defined kappa-SCALED (polynomial-trig, division- and
sqrt-free; cofK = kappa^2 K etc. -- nonvanishing certificates transfer; the exact kappa
powers enter only in the prop:vblock derivation). Joint analyticity + chart-composed
real_analytic_on_cof[KLM]_chart along a critical graph. CHECKED: lem:block/lem:3x3 are
NOT formalized and NOT needed (prop:dimZ surjective piece = D1/mstarg route).
Steps 1-3 of D34_WITNESS_PLAN.md now COMPLETE. Step 4 = the core: gauge-fixed dictionary
+ prop:vblock + the four branch corollaries; step 5 = assembly of `wit`.

### D34 LAYER 4b CLOSE-OUT REDUCTION: wit => wit_core, ONE lemma left (2026-07-06, cont.)
"Close out 4b." Full closure is the multi-week branch analysis; what IS closed today is
everything around it -- 4b is now EXACTLY ONE LEMMA (`wit_core`):
- triples_transverse_witness: explicit transverse config ((0,0),(1,0),(0,1)/(0,0),(1,2),(3,1))
  for any six distinct indices (card_le_inj for the indices; inj_eq + vector_2 simp).
- ttprod: the nine-factor cross-edge product as an EXPLICIT product (a set-based prod is NOT
  analytic -- coincidences collapse the set); polynomial in x alone (no c!);
  transverse_point_in_open: every nonempty open configuration set contains a transverse
  point (workhorse on ttprod; replaces the paper's globally perturbed two-triple V).
- dip_wit_reduction: wit (the dip_critical_chart_nowhere_dense hypothesis) follows from
  wit_core = witness on any connected analytic critical chart with cvec != 0 and a FIXED
  good triple -- the exact shape of the four Case-B branch corollaries.
- Moment dictionary for step 4 CONFIRMED in bridge scope: gradU_dip_component_moments,
  HessU_dip_entry_moments, Uc_eq_moment (Robust1:2646-2800): Phi = F o M_paper formalized.
GOTCHAS: pin the index type in higher-order hypotheses (B'::((real^2)^'n) set) or type
vars float; wit_core[of B' g i j k, OF ...] (bare OF into HO slots: no unifiers); the
interior_maximal step structured (metis on it HANGS in the merged heap -- confirmed again).
