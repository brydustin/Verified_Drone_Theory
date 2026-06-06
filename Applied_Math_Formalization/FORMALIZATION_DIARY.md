# Formalization Diary — Antenna Feasibility Nonemptiness

A running, dated log of the Isabelle/HOL formalization of the antenna-feasibility
*nonemptiness* theorem. Kept partly as a development record and partly as raw
material for the paper's "formalization notes." Entries are newest-first within a
day; commit hashes refer to the working repo (`antenna-nonemptiness`), mirrored
into the monorepo `Verified_Drone_Theory` under `Applied_Math_Formalization/`.

---

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
