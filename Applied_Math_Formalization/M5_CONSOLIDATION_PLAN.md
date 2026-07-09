All line numbers from R1–R4 are confirmed against the live files. The plan follows.

---

# M5 Consolidation Plan — Graft Proven Scaffolding into `Nonemptiness_Robust3.thy`

> **STATUS: ✅ EXECUTED (Stage A) — commit 81b65e1, 2026-06-22.** M5 assembled from
> D1∪D2∪D5∪D34; `F0_dip_nonempty` build-checked (new leaf `Applied_Math_Appendix_Full`;
> Robust3 moved to `Appendix/Robust3/`). **Lean graft: D5+D2+D34+skeleton+fixed_c only —
> NO curvecover/Morse/Sard.** Two proof holes remain: `m5_D34_D3_collinear`, `m5_D34_D4_branchP`.
> Stage B (graft curvecover/charts → canonical IFT cores) NOT done. See the diary entry of
> the same date + the `m5-consolidation-ready` memory for the seam fixes (hsep/kdiff, L1377 metis).

---

## ⟳ UPDATE (2026-06-22, post-D2/D5/curvecover completion) — overrides §3/§8 sources

Since this plan was written, the D2/D5/arc-cover work was COMPLETED + committed. Three corrections:

- **BLOCKER-A is RESOLVED.** The arc-cover chain is now PROVEN proof-complete with the **C¹** `analytic_arc` in **`M5_Dev_curvecover/Scratch_m5_curvecover.thy`** (commit b024a1b): `locus_locally_C1_arc` (~L2961), `collinear_locus_crossTheta_finite_arc_cover` (~L3573), `collinear_locus_finite_arc_cover` (~L3685). **Graft the arc-cover from `M5_Dev_curvecover`, NOT the stale weak/proof hole `M5_Dev_ArcCover2`.** These curvecover lemmas carry a `nsing_all` hypothesis (`∀ω∈{ω∈OmegaPF ctr δ. crossTheta ω0 ωs ω = 0}. ?d2≠0 ∨ ?d1≠0`); DISCHARGE it at the config: `crossTheta ω0 ωs ω = (cos(ω$1)−1)·sin(ω$2)` (Ac=1,Bc=0) so the locus is the 3 lines ω$2∈{−π,0,π}, and `?d2 = (cos(ω$1)−1)·cos(ω$2) ≠ 0` there (cos(ω$1)<1 on [π/4,3π/4]; cos(ω$2)=±1 on the locus). → end-state **2 proof holes**, not 3.
- **D2/D5 PROVEN as self-contained sessions** (supersedes §3 #11–#14's BeamHess/Kfinite split): graft **`m5_D2_beamcenter`** from `M5_Dev_D2` (commit 5563c72, proof-complete; D2 `imports Applied_Math_M5_D5`, and its `m5_D2_slice_nowhere_dense` ports the D5 covariance core via `nowhere_dense_subset`) and **`m5_D5_steersing`** from `M5_Dev_D5` (commit b8e1bfd; the covariance lemma `m5_D5_beamcenter_angle_meager` is proven via the **∑-form** `HessU_beamcenter_entry_expand` — a folded double-sum that fixed a 19-`$` coercion-parse hang). Source the beam-center/Hessian/gdip2 machinery from `M5_Dev_D5` (the ∑-form), not BeamHess. D5 still has 3 in-file freebie stubs (hsep/kdiff/fixed_c_nonsurj) discharged per §4.
- **Unchanged terminal proof holes:** `excess_arc_charts_Nn` (D3charts) + `branchP_indep_charts_Nn` (D4charts).

---

## ⚠ TOP-OF-PLAN BLOCKERS / INCONSISTENCIES (read first)

Two findings from R1–R4 materially change the naive task framing. Both are load-bearing and must be acknowledged before execution.

**BLOCKER-A — The arc-cover seam is NOT sound-compatible with the C¹ gate (from R2, Flag #1).**
The chain that bridges the D3 collinear locus to the per-arc engine — `collinear_locus_finite_arc_cover`, `crossTheta_trig`, `phase_collinear_iff_crossTheta`, `finitely_arc_coverable`, `collinear_locus_eq_crossTheta_zero` — lives **only in `M5_Dev_ArcCover2`**, which defines `analytic_arc` with the **weak `continuous_on`** version. The sound negligibility gate `analytic_arc_negligible` (in D3charts) requires the **C¹** `analytic_arc`. These two definitions are incompatible: the arcs produced by the cover step are stated `continuous_on`, but the gate consumes C¹ arcs.
→ **Consequence:** grafting the arc-cover reductions as-is will NOT typecheck against the C¹ gate. There is real work at the seam: either (i) re-state the cover's output arcs as `C1_differentiable_on` (re-prove `collinear_locus_finite_arc_cover` with C¹ arcs — itself currently a `proof hole` at `M5_Dev_ArcCover2:169`), or (ii) keep the arc-cover proof hole as a *third* open obligation. **The "exactly 2 proof holes remain" end-state is only achievable if `collinear_locus_finite_arc_cover` is either proven C¹ or absorbed into the `excess_arc_charts_Nn` core.** See §3 Layer-3D and §6.

**BLOCKER-B — `excess_arc_charts_Nn` and `branchP_indep_charts_Nn` are NOT proven anywhere (from R3).**
These are the genuine open IFT-chart cores, carried as `proof hole` in *every* file including the canonical D3charts (L286) / D4charts (L164). The plan **does not close them** — it grafts everything *around* them so they become the only two remaining proof holes. This is the intended end-state, but it must be stated plainly: **this consolidation does not finish M5's mathematics; it isolates the two irreducible obligations.**

**Non-blocker correction (from R4):** The premise that `negligible_singular_image_2n` is Sard-only is **false** — it is duplicated verbatim in `Nonemptiness_Paper.thy:1851` (identical signature) and is already in the Appendix heap. **Do NOT import `Applied_Math_Sard` into Robust3** (it creates a name clash). See §1.

---

## 0. Goal & end-state

**Goal:** Replace the single `proof hole` in `meager_rank_deficient_stratum` (`Nonemptiness_Robust3.thy:978`) with the real M5 proof, grafting the sound dev scaffolding so `mstarg`-based machinery discharges the freebies in-place, leaving **exactly two** genuine `proof hole` tokens in the consolidated Robust3.

**End-state (what builds):** A new leaf session `Applied_Math_Appendix_Full` (base `Applied_Math_Appendix`, no Sard import) builds green with `BUILD_EXIT=0` and `Finished Applied_Math_Appendix_Full`.

**The exactly-2 remaining proof holes (target):**
1. `excess_arc_charts_Nn` — the D3 per-arc IFT chart of the moment-Jacobian bad fibre (source: `M5_Dev_D3charts/Scratch_m5_d3charts.thy:286`).
2. `branchP_indep_charts_Nn` — the D4 IFT chart of the retained-constraint (`gradU=0 ∧ ¬surj`) bad locus (source: `M5_Dev_D4charts/Scratch_m5_d4charts.thy:164`).

**Caveat (BLOCKER-A):** achieving *exactly* 2 (not 3) requires resolving the arc-cover/C¹ seam. If unresolved, the honest end-state is **3 proof holes** (the two above + `collinear_locus_finite_arc_cover`). The plan flags the decision point in §3/§6.

---

## 1. Import / ROOT changes

**Imports of `Nonemptiness_Robust3.thy`:** **NO CHANGE.** Keep the single import `"Applied_Math_Appendix.Nonemptiness_Robust2"`.

- Do **NOT** add `"Applied_Math_Sard.Sard_Negligible"`. Per R4, `negligible_singular_image_2n` (+ helpers `card_n2_bit0`, `exists_index_bij`) is already exported by the heap via `Nonemptiness_Paper.thy:1838/1842/1851` with identical signature. Importing Sard would create a duplicate-name ambiguity forcing qualification everywhere.

**ROOT change — add one leaf session.** Move `Appendix/Nonemptiness_Robust3.thy` → `Appendix/Robust3/Nonemptiness_Robust3.thy` (mirroring the `Robust2/` layout so the dev copy and heaped copy don't collide), then add to `Applied_Math_Formalization/ROOT`:

```
session Applied_Math_Appendix_Full in "Appendix/Robust3" = Applied_Math_Appendix +
  options [document = false, quick_and_dirty = true, timeout = 3600]
  theories
    Nonemptiness_Robust3
```

**Why `quick_and_dirty = true`:** allows the two terminal `proof hole`s to remain while still building green. The remaining lemmas are checked for real (proof hole-freeness verified separately, §6).

**Interim verify recipe (before baking into ROOT)** — the throwaway temp session used today:
```
session Scratch_R3 = Applied_Math_Appendix + theories Nonemptiness_Robust3
```
written to a `/tmp` ROOT, built at `threads=4` (~12–13 min). Use this during graft iteration; bake the named leaf only once green.

---

## 2. New definitions to add to Robust3

**Insertion point:** between **L968** (end of the `(M5)` commentary text block) and **L970** (`lemma meager_rank_deficient_stratum`). This is after the entire mstarg/steering machinery (L572–775: `mstarg`, `surj_iff_mstarg`, `nowhere_dense_mstarg_zeros`, `cont_mstarg`) and after the M3 `Dcvec` block (L782–945), and before the M5 consumer `Phi_bad_meager_dip` (L1009). All are in scope.

Add, in this order (def dependencies respected):

| # | Definition | Type | Canonical source | Notes |
|---|---|---|---|---|
| D-1 | `gsincdd :: real⇒real` | helper | `M5_Dev_gdip2` (L20) | 2nd deriv of `gsincd` |
| D-2 | `um`, `up`, `D1f :: real⇒real` | helpers | `M5_Dev_gdip2` (L58) | first-deriv field on `{sin≠0}` |
| D-3 | `gdip2 :: real⇒real` (scalar route) | def | `M5_Dev_gdip2` | base `gdip`/`cvec_dip`/`Dcvec_dip` are already in heap (`Robust1`) — do NOT re-add |
| D-4 | `qf`, `gdip2` (vector `real^2→real`, Hessian route) | def | `M5_Dev_BeamHess` | **distinct** from D-3's scalar route; keep both names disambiguated (BeamHess uses its own `gdip2` for the Hessian — verify no name collision; if both are literally `gdip2`, rename one at graft, e.g. `gdip2_qf`) |
| D-5 | `analytic_arc :: (real^2)set⇒bool` | def | `M5_Dev_D3charts` (= D3Sound) | **C¹ version ONLY**: `∃a b φ. a≤b ∧ φ C1_differentiable_on {a..b} ∧ γ = φ`{a..b}`. NEVER the `continuous_on` version. |
| D-6 | `BadXW :: real^2⇒real^2⇒(real^2)set⇒((real^2)^'n)set` | def | `M5_Dev_D3charts` | D3 bad-x-set (drops `gradU=0`) |
| D-7 | `phase_collinear :: real^2⇒real^2⇒real^2⇒bool` | def | `M5_Dev_D34` | D3/D4 separating predicate |
| D-8 | `gamma_par_c :: real^2⇒real^2⇒real^2⇒bool` | def | `M5_Dev_D4charts` | D4 rank-drop dichotomy (γ∥c) |
| D-9 | `BadXGW :: real^2⇒real^2⇒(real^2)set⇒((real^2)^'n)set` | def | `M5_Dev_D4charts` | D4 bad-x-set, `gradU=0` **RETAINED** (the soundness fix) |
| D-10 | `crossTheta` + `finitely_arc_coverable` | defs | `M5_Dev_ArcCover2` | **CONDITIONAL** — only if pursuing BLOCKER-A resolution (i). `finitely_arc_coverable` is off the canonical chain otherwise. Re-source with `analytic_arc` upgraded to C¹. |

All confirmed absent from heap and Robust3 (R3 grep: count 0). No collisions except the potential `gdip2` double-definition (D-3 vs D-4) — disambiguate at graft.

---

## 3. Dependency-ordered graft list

Graft into the L968–970 gap (defs first per §2, then lemmas in this numbered order). All sources are the **canonical** files identified in R2; never graft from superseded files (§8).

**Layer 1 — gdip2 helpers (all proof-complete), from `M5_Dev_gdip2`:**
1. `gsincd_has_deriv`, `gdip_deriv_field_eq_D1f`, `D1f_has_deriv`
2. `gdip_second_deriv_at_cos_zero`, `gsinc_pi_half`, `gsincd_pi_half`, `gsincdd_pi_half`
3. `gdip_secondderiv_value`, `gdip_secondderiv_value_nonzero`
4. `gdip2_eq_scalar_second_deriv`
5. **`gdip2_nonzero_of_cos_zero`** ← the key residual that BeamHess carries as a proof hole (L564) but gdip2 proves proof-complete (ends in `qed`).

**Layer 2 — structural set algebra (proof-complete):**
6. `analytic_arc_negligible` (the C¹ soundness gate; proven from heap `negligible`/`C1_differentiable` machinery) — `M5_Dev_D3charts`
7. `BadXW_empty/mono/UN/point` — `M5_Dev_D3charts`
8. `not_gamma_par_c_iff`, `BadXGW_mono/UN/point` — `M5_Dev_D4charts`
9. `cvec_dip_component1/2` — `M5_Dev_Kfinite`

**Layer 2D — D1 / D2 / D5 leaf strata:**
10. **D1:** `m5_D1_regular` — `M5_Dev/Scratch_m5_skeleton` (uses heap `meager_grad_x_regular_part`, M5a)
11. **D2 BeamHess chain** (proof-complete *given* Layer-1 `gdip2_nonzero_of_cos_zero`): `M_paper_at_zero_*`, `Afun/Mcfun/M2cfun_at_zero_real`, `gradUc_at_beamcenter`, `Uc_at_beamcenter`, `HessU_at_beamcenter_entry`, `Re_*_at_zero`, `Hcmat_at_zero_entry`, `rline_entire_*`, `Hcmat_qform_at_zero`, `continuous_on_*`, `Gterm_*`, `HessU_entry_qf`, `det_HessU_at_beamcenter`, `Hcmat_one_point`, `qf_one_point`, `det_HessU_nontrivial_witness`, `gradU_at_beamcenter_component`, `gradU_beamcenter_comp1`, `beamcenter_bad_empty_of_cos_ne`, `det_HessU_zero_nowhere_dense_cos0`, **`m5_D2_slice_nowhere_dense`**, **`m5_D5_beamcenter_angle_meager`** — `M5_Dev_BeamHess` (replace its internal `gdip2_nonzero_of_cos_zero` proof hole with the Layer-1 lemma)
12. **D2 K-finite:** **`m5_D2_beamcenter_K_finite`** — `M5_Dev_Kfinite` (proof-complete; the D2-file copy is a STUB — do not use it)
13. **D2 assembly:** `m5_D2_beamcenter` — `M5_Dev_D2` (consumes #11 BeamHess + #12 Kfinite)
14. **D5:** `m5_D5_slice_meager`, `m5_D5_steersing` — `M5_Dev_D5` (consume #11 `m5_D5_beamcenter_angle_meager`; freebie split handled in §4)

**Layer 3D — D3/D4 chart cores + arc machinery:**
15. **D3 chart route** (proof-complete above the one `charts_Nn`): `fixed_omega_slice_nowhere_dense`, `fixed_omega_slice_meager`, `fixed_omega_proj_meager`, `excess_empty_arc_meager`, `excess_point_arc_meager`, `excess_finite_arc_meager`, **`excess_empty_arc_charts_Nn`**, `excess_arc_charts_Nn_of_closed_negligible_cover` (reduction), `excess_arc_negligible_closed_cover`, `excess_arc_projection_of_negligible_closed_cover`, `excess_arc_projection_meager` — `M5_Dev_D3charts`
16. **`excess_arc_charts_Nn`** — `M5_Dev_D3charts:264/286` → **TERMINAL proof hole #1** (graft as-is, keeps `proof hole`)
17. **D3 collinear-locus arc reductions** (proof-complete, def-independent of weak `analytic_arc`): `crossTheta` def, `phase_collinear_iff_crossTheta`, `crossTheta_trig`, `collinear_locus_eq_crossTheta_zero`, `c1_eq/c2_eq/Dc1_eq/Dc2_eq` — re-sourced from `M5_Dev_ArcCover2` ⚠ **BLOCKER-A applies here.**
18. **`collinear_locus_finite_arc_cover`** — `M5_Dev_ArcCover2:169` ⚠ **DECISION POINT (BLOCKER-A):** this is a `proof hole` *and* states `continuous_on` arcs. Either re-prove with C¹ arcs (preferred; keeps end-state at 2) or leave as a 3rd terminal proof hole.
19. **D4 chart route** (proof-complete above the one `charts_Nn`): `branchP_indep_negligible_closed_cover`, `branchP_indep_of_negligible_closed_cover`, `branchP_indep_core` — `M5_Dev_D4charts`
20. **`branchP_indep_charts_Nn`** — `M5_Dev_D4charts:142/164` → **TERMINAL proof hole #2** (graft as-is, keeps `proof hole`)

**Layer 4 — D34 assembly (proof-complete), from `M5_Dev_D34`:**
21. `m5_D34_subset_mstarg_residual` (structural reduction)
22. `m5_D34_D3_collinear` — the proof-complete subset-reduction (D3's version; D34's own copy is a STUB → use D3's). Bridges to #15/#16 via the arc cover (#17/#18).
23. `m5_D34_D4_branchP` — proof-complete subset-reduction (BranchP's version; D34's copy is a STUB → use the sound one). Bridges to #19/#20.
24. `m5_D34_residual` — `M5_Dev_D34` (consumes #21–#23)

**Layer 5 — top interface:**
25. The body of `meager_rank_deficient_stratum` — assembly from `M5_Dev/Scratch_m5_skeleton` (see §5), consuming D1 (#10), D2 (#13), D5 (#14), D34 (#24).

---

## 4. Freebie discharges

Three freebies are dev-only stubs that close *in-place at the splice* because the referenced fact is already resident above L970 (or is a context assumption). Replace each stub's `proof hole`/stub body with the proof below.

**(a) `fixed_c_nonsurj_nowhere_dense`** — stub statement `c≠0 ⟹ 6≤CARD('n) ⟹ nowhere_dense {x::(real^2)^'n. ¬ surj (DM_paper_x x c)}` (8 identical dev copies). Discharge via `surj_iff_mstarg` (L578) ∘ `nowhere_dense_mstarg_zeros` (L744), both in scope:
```isabelle
lemma fixed_c_nonsurj_nowhere_dense:
  assumes c0: "c \<noteq> 0" and n6: "6 \<le> CARD('n)"
  shows "nowhere_dense {x::(real^2)^'n. \<not> surj (DM_paper_x x c)}"
proof -
  have "{x::(real^2)^'n. \<not> surj (DM_paper_x x c)} = {x. mstarg c x = 0}"
    using surj_iff_mstarg by auto
  thus ?thesis using nowhere_dense_mstarg_zeros[OF c0 n6] by simp
qed
```

**(b) `m5_D5_hsep_freebie`** — `kz \<omega>s \<noteq> kz \<omega>0`. In `Phi_bad_meager_dip` this is the named assumption `hsep` (L1013), so M5's own proof does not need it directly (M5 takes only the 5 assumptions `openV Vne c6 d0 pf`). Where the concrete `\<omega>0 = vector[\<pi>/2,0]`, `\<omega>s = vector[0,0]` are in play (Robust3 L1634–1635), discharge by:
```isabelle
by (simp add: \<omega>s_def \<omega>0_def kz_def)
```

**(c) `m5_D5_kdiff_freebie`** — `kx \<omega>0 \<noteq> kx \<omega>s \<or> ky \<omega>0 \<noteq> ky \<omega>s`. The named assumption `kdiff` (L1014). At the concrete site (L1636–1637):
```isabelle
by (simp add: \<omega>0_def \<omega>s_def kx_def sin_pi_half)
```

**Routing note (from R1):** M5 (`meager_rank_deficient_stratum`) is invoked as `meager_rank_deficient_stratum[OF openV Vne c6 d0 pf]` — exactly 5 OF-args, NO `hsep`/`kdiff`/`oddN`. Those are routed to M6 (`meager_steering_singular_stratum[... hsep kdiff]`) and M6b (`oddN`). So freebies (b)/(c) must be discharged inside the **D5 sub-proof of M5 from M5's own context** if D5 needs them — verify during graft whether the D5 chain actually consumes `hsep`/`kdiff`; per R3 the D5 slice split only needs `fixed_c_nonsurj_nowhere_dense` (c≠0) and `m5_D5_beamcenter_angle_meager` (c=0). If `hsep`/`kdiff` appear in the D5 chain they must be derivable from M5's 5 assumptions or the kernel reduction — **flag for verification at graft**, as M5 does not receive them as hypotheses.

---

## 5. Final M5 assembly (replacing L978 `proof hole`)

Keep the lemma signature (L970–977) **untouched** so the call site `meager_rank_deficient_stratum[OF openV Vne c6 d0 pf]` at L1037 stays valid. Replace only the `proof hole` at L978.

The conclusion set (gradU=0 ∧ det HessU=0 ∧ A_cart≠0 ∧ ¬surj DM_paper_x) is decomposed (per `M5_Dev/Scratch_m5_skeleton`) into the union of four strata:
- **D1** (regular part) — `m5_D1_regular` (#10)
- **D2** (beamcenter) — `m5_D2_beamcenter` (#13)
- **D5** (steering-singular sub-stratum within M5's residual) — `m5_D5_steersing` (#14)
- **D34** (collinear D3 ∪ branch-P D4) — `m5_D34_residual` (#24)

Assembly shape:
```isabelle
lemma meager_rank_deficient_stratum:
  fixes V :: "((real^2)^'n) set" and ctr :: "real^2" and \<delta> :: real
  assumes openV: "open V" and Vne: "V \<noteq> {}" and c6: "6 \<le> CARD('n)"
    and d0: "0 < \<delta>" and pf: "\<forall>\<omega>\<in>OmegaPF ctr \<delta>. sin (\<omega> $ 1) \<noteq> 0"
  shows "meager {x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. ... \<and> \<not> surj (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>))}"
proof -
  \<comment> \<open>the bad set is contained in the union of the four strata\<close>
  have sub: "{x \<in> V. \<exists>\<omega>\<in>OmegaPF ctr \<delta>. ...} \<subseteq> ?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34" by ...
  have "meager (?D1 \<union> ?D2 \<union> ?D5 \<union> ?D34)"
    by (intro meager_Un
              m5_D1_regular[OF openV Vne c6 ...]
              m5_D2_beamcenter[OF openV Vne c6 d0 pf]
              m5_D5_steersing[OF openV Vne c6 d0 pf]
              m5_D34_residual[OF openV Vne c6 d0 pf])
  thus ?thesis using sub by (rule meager_subset)  \<comment> \<open>or meager_mono\<close>
qed
```
(Exact strata definitions `?D1..?D34` and the `sub` subset proof come verbatim from `M5_Dev/Scratch_m5_skeleton`. The skeleton's three leaf-stubs `m5_D2_beamcenter` L82, `m5_D5_steersing` L102, `m5_D34_residual` L125 are replaced by the grafted #13/#14/#24 bodies.)

---

## 6. Expected final proof hole inventory + verification

**Target: exactly 2** (subject to BLOCKER-A):
1. `excess_arc_charts_Nn` (D3 IFT chart core)
2. `branchP_indep_charts_Nn` (D4 IFT chart core)

**If BLOCKER-A unresolved: 3** (add `collinear_locus_finite_arc_cover`). Decide at graft step #18.

**Everything else must be proof-complete.** Verify by:
```bash
grep -n "\bsorry\b\|\boops\b" Appendix/Robust3/Nonemptiness_Robust3.thy
```
Expect exactly the 2 (or 3) lines, each on the grafted chart-core lemma. Cross-check with the build log: with `quick_and_dirty=true`, Isabelle still emits an `oracle`/`proof hole` count — confirm it matches. Additionally run a `quick_and_dirty=false` build to *prove* every non-terminal lemma is genuinely closed: it should fail **only** on the 2 (or 3) `proof hole`s and nowhere else.

**Pre-graft sanity:** before grafting, confirm none of the new names already exist in the heap (R3 verified count 0 for `BadXW`, `BadXGW`, `analytic_arc`, `phase_collinear`, `gamma_par_c`, `gdip2`):
```bash
grep -rn "definition \(BadXW\|BadXGW\|analytic_arc\|phase_collinear\|gamma_par_c\|gdip2\)\b" Appendix/ *.thy Robust2/ SardNegligible/
```

---

## 7. Build & verification steps

1. **Move file:** `Appendix/Nonemptiness_Robust3.thy` → `Appendix/Robust3/Nonemptiness_Robust3.thy`.
2. **Edit ROOT:** add the `Applied_Math_Appendix_Full` leaf (§1).
3. **Graft** defs (§2) + lemmas (§3) into the L968–970 gap; discharge freebies (§4); replace L978 proof hole (§5).
4. **Interim builds** during iteration via the `/tmp` `Scratch_R3` session (`threads=4`, ~12–13 min).
5. **Final build** (per `isabelle-build-invocation` memory — lowercase `-d`, run from repo root `…/Vern_Paulsen_QC`):
```bash
timeout -s KILL 1500 ./Isabelle2025-2/bin/isabelle build \
  -d Imported_Munkres_Topology \
  -d Applied_Math_Formalization \
  -o threads=4 \
  Applied_Math_Appendix_Full
echo "BUILD_EXIT=$?"
```
6. **Acceptance:** require `BUILD_EXIT=0` AND a `Finished Applied_Math_Appendix_Full` line (per `never-claim-unverified-builds`). Then run §6 proof hole-grep + the `quick_and_dirty=false` confirmation.

**Expected time:** ~13–15 min wall (heap base prebuilt; M5 graft is "cheap restatements" per R4's diary accounting). The Lmat/mstarg proofs dominate, not the graft.

**Process hygiene (from `isabelle-build-process-hygiene`):** `timeout -s KILL` only (plain `timeout` orphans a 4 GB `poly` holding the heap lock ~1h); never SIGKILL mid-flight (deletes the target heap); kill strays with `pkill -9 -x poly` (never `-f`); one session build at a time (heap lock); do not run while a jEdit `-l Applied_Math_Appendix_Full` session is open.

**Rollback if it breaks:**
- All work is git-tracked. To revert: `git checkout Appendix/ ROOT` (and restore the original file location), rebuild the prior green target to confirm clean state.
- Do NOT commit until BUILD_EXIT=0 + Finished + proof hole count = 2 (or the explicitly-accepted 3). Never commit broken state (CLAUDE.md rule).
- If a single grafted lemma fails, graft is incremental — bisect by re-introducing lemmas in the §3 numbered order; the dependency order guarantees each lemma's prerequisites precede it.

---

## 8. Risks & mitigations

| Risk | Severity | Mitigation |
|---|---|---|
| **Arc-cover C¹ seam (BLOCKER-A)** | HIGH | The `continuous_on` arcs from `M5_Dev_ArcCover2` don't feed the C¹ gate `analytic_arc_negligible`. Decide at #18: re-prove `collinear_locus_finite_arc_cover` with C¹ arcs (target 2 proof holes) OR accept it as a 3rd proof hole. Do NOT silently graft the weak-def version — it would make `analytic_arc_negligible` UNSOUND (admits Peano curves). |
| **`gdip2` double-definition** (scalar gdip2 file vs vector BeamHess `gdip2`) | MED | Disambiguate at graft: rename the BeamHess Hessian-route to e.g. `gdip2_qf`. Verify with the §6 pre-graft grep. |
| **Grafting from a superseded file** | MED | Use ONLY canonical sources (R2): `gdip2, BeamHess, Kfinite, D2, D5, D3charts, D4charts, D34, skeleton`. NEVER graft `D3_excess_engine` (D3/Engine/CurveEngine/Excess), `branchP_engine` (BranchP), the weak `analytic_arc` (ArcProj/ArcNeg/CurveEngine/Excess/ArcCover2), or the UNSOUND `M5_Dev_D4` wave (drops `gradU=0`). Use D3's/BranchP's sound subset-reductions for `m5_D34_D3_collinear`/`m5_D34_D4_branchP`, not D34's stubs. |
| **Stub-vs-canonical confusion** (Kfinite-in-D2 is a STUB; D34's own `m5_D34_D3/D4` are STUBS) | MED | Per R2/R3: take `m5_D2_beamcenter_K_finite` from Kfinite (not D2), the D34 connectors from D3charts/BranchP (not D34). |
| **Sard/Munkres merge** | LOW | Already proven coexistent: green dual-import dev files + green Appendix heap (`Nonemptiness_Paper` hosts HOL-Analysis `negligible_singular_image_2n` alongside Munkres/JNF/HMA). Mitigation = do NOT import Sard (use the heap's Paper copy); avoids the only real issue (duplicate-name ambiguity). |
| **hsep/kdiff not in M5's context** | MED | M5 receives only 5 assumptions (no hsep/kdiff). Verify the D5 chain inside M5 doesn't actually need them (R3: D5 split needs only `fixed_c_nonsurj_nowhere_dense` + `m5_D5_beamcenter_angle_meager`). If it does, that's a real gap — flag before claiming green. |
| **~13-min build × iteration cost** | LOW | Use the `/tmp Scratch_R3` interim session; bake the ROOT leaf only once green. Hand the final long verify to the user with `-v` if needed (per `user-runs-long-builds-verbose`). |
| **Ordering pitfalls** | LOW | Follow §3's numbered sequence exactly: gdip2 helpers → set algebra → D1/D2/D5 → D3/D4 cores → D34 assembly → M5 top. `gdip2_nonzero_of_cos_zero` (#5) MUST precede BeamHess (#11), which it un-proof holes. |

---

**Bottom line:** No import/ROOT root-change for the Sard engine (it's already in the heap). One new leaf session. Defs + ~50 lemmas grafted from 9 canonical dev files into the L968–970 gap, in the §3 order, with 3 freebies discharged in-place. The L978 proof hole becomes a 4-stratum `meager_Un` assembly. End-state is **2 proof holes** (`excess_arc_charts_Nn`, `branchP_indep_charts_Nn`) **IF** BLOCKER-A (arc-cover C¹ seam) is resolved at step #18 — otherwise **3**. This consolidation isolates the two irreducible IFT-chart obligations; it does not close them.