# D34 layer 4b: the transversality witness — work plan

_As of 2026-07-06. The single remaining GENUINE-MATHEMATICS obligation of the analytic
route to a sorry-free `F0_dip_nonempty` (besides the degenerate stratum 4c)._


## 0. ARCHITECTURE CORRECTION (2026-07-07) — READ FIRST

`m5_D34_subset_mstarg_residual` (Robust3:2365) is a pure `blast` ENLARGEMENT: the true
D34 target (`m5_D34_residual`, Robust3:2665) RETAINS `det HessU = 0`, `A_cart != 0`,
and `not (EX Dx. gradU-x-derivative surjective)`. The two sorries were stated for the
enlarged residual (those conjuncts dropped) — STRICTLY STRONGER than F0 needs.

Consequences:
- The NEEDED bad set = the paper's Case-B set verbatim (degenerate critical
  `Phi3 = det H = 0` + rank drop + regular stratum `A != 0`). The paper's branch
  certificates (built on `G11 = Phi3/H11` etc.) apply DIRECTLY — at FIXED omega,
  via rank-3 x-charts (the original charts_Nn shape), NO omega-graph.
- `wit_core` as stated (det H != 0 charts) is the roadmap's "genuinely new
  mathematics" (moment-determinant transversality along nondegenerate critical
  graphs) and is NOT needed for F0. The omega-graph engine
  (dip_critical_graph_dichotomy_unique / dip_critical_chart_nowhere_dense /
  dip_wit_reduction / dip_wit_core_scaffold) remains sound and reusable, but the
  LAYER-5 covering of D34 should NOT route through it; it routes through
  rank-3-in-x charts on the det-H=0 set.
- Layer-5 restatement: replace the two sorried lemmas by versions RETAINING
  `det HessU = 0 /\ A_cart != 0 /\ ...` (adapt m5_D34_residual to consume them
  directly, dropping the subset step). Then prove them via the paper's Case-B
  branches over the landed substrate.
- What carries over unchanged to the corrected path: ALL of layers 1-3 + 4a
  (analytic kit, moments/mstarg, gradU/HessU analyticity, IFT-unique), the
  good-triple layer, cadapt/applyT transport, cofactors, division closure, the
  slot calculus, the entry-shrink pattern (re-aim the scaffold's package at the
  det-H=0 set), and the June heap machinery charts_core_Nn /
  negligible_proj_charts_Nn / regular_value_local_chart (the rank-3 chart
  consumers the paper's route needs).

## 1. The interface (DONE, in the bridge heap) — see §0: engine retained, layer-5 re-aimed

`dip_critical_chart_nowhere_dense` (`Appendix/AnalyticBridge/D34_Analytic_Bridge.thy`)
delivers the final chart the D3/D4 covering argument consumes — connected chart `B`,
uniqueness neighbourhood `N`, real-analytic critical graph `g`, `cvec ≠ 0` along the
graph, and `interior (closure {x ∈ B. mstarg (cvec_dip ω0 ωs (g x)) x = 0}) = {}` —
under ONE hypothesis:

    wit: ⋀B g. open B ⟹ connected B ⟹ x0 ∈ B ⟹
           real_analytic_on g B ⟹ g x0 = ωb ⟹
           (⋀x. x ∈ B ⟹ gradU (cvec_dip ω0 ωs) gain_dip x (g x) = 0) ⟹
           (⋀x. x ∈ B ⟹ cvec_dip ω0 ωs (g x) ≠ 0) ⟹
           ∃x∈B. mstarg (cvec_dip ω0 ωs (g x)) x ≠ 0

`wit` = "no connected critical chart lies wholly inside the moment-rank-drop locus".
It plays the role for 4b that `nd` plays in the two Robust3 sorries. If the witness
mathematics needs more side conditions along the chart (e.g. `det HessU ≠ 0`, `A ≠ 0`,
`g x` in the OmegaPF window), they are ALL shrinkable by continuity from the basepoint
facts — extend the engine's shrink step (the `cvec ≠ 0` shrink in
`dip_critical_chart_nowhere_dense` is the template).

## 2. The mathematics (the paper's Case-B appendix)

Source of truth: `Vern_Paulsen_QC/Applied Math/nonemptiness_unified_singlefile_complete.tex`,
`app:caseB` (lines ~3579–6253), culminating in `cor:caseBmeager` (line 6205): the
x-projection of `(Z \ W_surj) ∩ {H ≢ 0}` — EXACTLY our `BadXGW` — is meager. Structure:

- Setup (3579): c-adapted coordinates over a GOOD TRIPLE `T = {1,2,3}`
  (`p_j = u_j e∥ + v_j e⊥`, `c = κ e∥`, `t_j = κ u_j`); translation-invariance
  normalisation `b = 0, a > 0`; on `H22 ≠ 0`:
  `rank D(Φ1,Φ2,Φ3) = rank D(Φ1,Φ2,G22)`, `G22 = H11 − H12²/H22`.
- The three familiar cofactors (3650); the direct v-block determinant (3680);
  a direct branch theorem (3710).
- Branches, each with an explicit rank/containment certificate:
  * `H12 ≠ 0, H22 ≠ 0`: scalar residue exhausted by `cor:vpair22-full` (4365–5186);
  * vanishing u-slice differential of Φ1: `cor:uphi-exhausted` (3826–4004);
  * `H12 = 0, H22 ≠ 0`: `cor:Lambda-closed` (5417–5587) + the common-parameter
    reduction of the Λ^(11) residue (5587–6205);
  * symmetric `H11 ≠ 0`: `cor:H11-closed` (4004–4365).
- Assembly (6205): two-triple cover ⟹ finitely many branch types; each piece is
  contained in codim-≥3 coordinate slices or images of codim-4 analytic lifts ⟹
  nowhere dense; countable chart cover ⟹ meager.

## 3. Formalization strategy for `wit` (LOCAL form — less than full caseBmeager)

For `wit` we do NOT need the full meager projection: a chart `B` with `h ≡ 0` embeds an
OPEN set of x into the Case-B locus; it suffices to derive a contradiction from that.
Per branch, the paper's certificate is an explicit REAL-ANALYTIC function `Ξ_branch`
(built from the cofactor determinants of the moment coordinates) such that the branch's
bad locus is contained in `{Ξ_branch = 0}` while `Ξ_branch ≢ 0` there. Formal shape:

    chart B inside bad locus ⟹ Ξ ∘ (graph data) ≡ 0 on B
      ⟹ (identity theorem / real_analytic_nowhere_dense_zeros) Ξ-witness contradiction.

This matches the analytic toolkit exactly (layer-2 closure kit + the workhorse).
Steps, in dependency order:

1. **c-adapted coordinates layer**: rotation to `c = κ e∥`; the rotated moment
   transport is ALREADY formalized (the Robust3 `M12_moment_applyT`-style `applyT`
   laws + Robust2 Sym²T diagonal transport) — verify coverage, port what's missing.
2. **Good-triple layer**: `lem_twotriplecover` is formalized (`Nonemptiness_Paper:848`).
   Bridge it to the chart setting (a good triple exists for `c = cvec_dip (g x0)` ≠ 0,
   and by continuity stays good on a shrunk chart).
3. **Cofactor certificates**: the 3650–3710 determinants (check against
   `BlockDet/Block_Determinants(_BigJ)` — the u-pair/v-triple minor propositions of
   the tex part II may already be there; `lem:block`'s J5 with `det = −32 g⁵ a⁵` and
   `lem:3x3`'s `det = ±8 g³ a³ H_*` are listed as formalized in the paper's status).
4. **Branch lemmas**: one Isabelle lemma per tex corollary (`vpair22-full`,
   `uphi-exhausted`, `Lambda-closed`, `H11-closed`), each in the local Ξ-certificate
   form above.
5. **Assembly**: `wit` by case split over the finitely many branches at the basepoint
   (H-entry signs + good-triple choice), each closed by its certificate.

Estimated effort: steps 1–3 days-scale (mostly porting/verification), step 4 the
multi-week core (four branch families of explicit analytic linear algebra), step 5 days.

### Progress log

- 2026-07-06: **step 2 LANDED** (good-triple layer, in the bridge): `triple_good`
  (+ t-separation, distinctness), `edge_det2` + `common_perp_edge_det2`,
  `triples_transverse` + `two_triple_cover_pointwise` (nine nonzero cross-edge
  determinants => every c /= 0 good for one triple - the pointwise
  lem:twotriplecover; its failure set is the explicit polynomial certificate for
  the no-good-triple stratum), `triple_good_chart_persist` (chart shrink).
  INVENTORY VERIFIED: applyT transport family = phase/A/M1/M2 (Robust1:4567-4640),
  M11/M22 (Robust2:17/98), M12/M_paper (Robust3:5/99 - OUTSIDE bridge scope, must
  migrate into the bridge or be re-proven there for the rotation layer);
  `lem_twotriplecover` (Nonemptiness_Paper:848) is the abstract finite-avoidance
  core only - the geometric content is now the pointwise criterion above;
  BlockDet = the Bblk/Ablk/Cblk/bigJ determinant chain (the paper's part-II minor
  ladder), c0_paper = vector [1,0] with transport convention
  `transpose T *v c = c0_paper` (Moment_Jacobian:36).
  Remaining in step 1: the concrete T(c) witness matrix for c /= 0 (rotation+scale
  with transpose T *v c = c0_paper) + migration of the M12/M_paper applyT laws.
  Then step 3: connect gauge-fixed a,b,a_k,b_k,H-entries to the K/L/M cofactors
  (tex 3650-3710) and check them against the BlockDet ladder.
- 2026-07-06 (cont.): **step 1 transport entry point LANDED**: `cadapt c` (columns
  c/|c|^2 and c-perp) with `cadapt_transport` (transpose (cadapt c) *v c = c0_paper),
  `cadapt_det` (= 1), `cadapt_invertible` - the witness matrix for the applyT laws.
- 2026-07-06 (cont.): **step 1 COMPLETE**: M12_moment_applyT / M_paper_applyT /
  applyT_linear / applyT_surj migrated into the bridge (statements+proofs rewritten
  to vec_nth: the verbatim $ forms PARSE-HANG >10 min in the merged heap; metis
  consider replaced by exhaust_6+blast). Robust3's local copies (L5-155, L322-341)
  to be DELETED at the layer-5 rewire. Still available in Robust3 only (migrate on
  demand for the certificates): Smat/Smat_c/Lmat/Lmat_apply (L158-320),
  DM_paper_x_surj_transport + regular-point lifts (L343-495).
  NEXT = step 3: the K/L/M cofactors (tex 3650-3710) and the gauge-fixed
  a,b,a_k,b_k,H-entry dictionary, checked against the BlockDet ladder.
- 2026-07-06 (cont.): **step 3 foundation LANDED**: division closure for the kit
  (real_analytic_on_inverse_1d/_inverse_comp/_divide - needed for G22 etc.); det3;
  tcoord (= kappa u_j) / wcoord (= kappa v_j, via edge_det2); the three familiar
  cofactors cofK/cofL/cofM (tex 3650) in kappa-SCALED polynomial-trig form
  (cofK = kappa^2 K, cofL = kappa L, cofM = kappa M; nonvanishing transfers,
  exact kappa-bookkeeping deferred to the prop:vblock derivation), with joint
  analyticity and the chart-composed real_analytic_on_cof[KLM]_chart forms.
  CHECKED: the paper's lem:block/lem:3x3 (J5, rank-3 minor) are NOT in the heap
  and NOT needed - they serve prop:dimZ's surjective piece, already covered by
  the formalization's D1/mstarg route.
  NEXT = step 4 (THE CORE): the gauge-fixed dictionary (a,b,a_k,b_k,H-entries as
  functions of the configuration in the c0-frame; translation gauge b=0, a>0) and
  prop:vblock: det d(Phi2,H12,H22)/d(v1,v2,v3) = -16 a^2 g^3 (aK + a1 L - a2 M)
  in the scaled variables, then the four branch corollaries.
- 2026-07-06 (cont.): **4b REDUCED TO ONE LEMMA** (`dip_wit_reduction` in the bridge):
  the interface obligation `wit` follows from the single hypothesis `wit_core` -- a
  witness on any connected analytic critical chart with nonvanishing wavevector and
  a FIXED good triple. Machinery: explicit transverse configuration witness
  (triples_transverse_witness), the nine-factor transversality product ttprod
  (polynomial in x alone!) with transverse_point_in_open (every open chart contains
  a transverse point -- REPLACES the paper's globally perturbed two-triple V; no
  perturbation argument needed), triple selection via two_triple_cover_pointwise +
  persistence. ALSO VERIFIED: the moment-space dictionary needed by step 4 already
  exists in bridge scope: gradU_dip_component_moments, HessU_dip_entry_moments,
  Uc_eq_moment etc. (Robust1:2646-2800) -- the Phi = F o M_paper factorisation is
  formalized; the gauge b=0/a>0 normalisation rides on the applyT/cadapt transport.
  **REMAINING FOR 4b = prove `wit_core`** = the four Case-B branch corollaries
  (vpair22-full, uphi-exhausted, Lambda-closed, H11-closed; tex 3826-6205) over the
  landed substrate. If the certificates need A /= 0 or det HessU /= 0 along the
  chart, add the corresponding analytic-dichotomy sub-cases inside wit_core's proof
  (A o graph == 0 is itself an analytic certificate; same pattern).
- 2026-07-07: **wit_core substrate: Hessian fields analytic** (in the bridge):
  real_analytic_on_HessU_dip_entry (each (k,l) entry of HessU jointly analytic in
  (x,omega), assembled through HessU_dip_entry_moments), real_analytic_on_detHessU_dip
  + _chart. Supporting: Afun/Mcfun/M2cfun joint (c,x); Hcmat entries; c-pattern
  gradient components (gradU_c_field); deriv^2 gdip analytic + frechet_gdip2_eq;
  D2cvec_dip applied; helpers field_nth / inner_expand_vec / inner_mv_expand.
  NEXT: (a) thread det HessU != 0 along the chart into wit / wit_core (continuity
  shrink via real_analytic_on_detHessU_chart - interface upgrade of
  dip_critical_chart_nowhere_dense + dip_wit_reduction); (b) then the branch
  case-split scaffold on H-entry vanishing patterns (identity theorem per entry
  field), then the four certificates.
- 2026-07-07 (cont.): **(a) DONE - det HessU != 0 threaded**: wit (in
  dip_critical_chart_nowhere_dense) and wit_core (in dip_wit_reduction) now carry
  `det (HessU ... x (g x)) != 0` along the chart; the engine shrinks on it by the
  detHessU_chart continuity (same preimage pattern as cvec != 0); the HessAna
  section moved before the interface section (forward reference). wit_core's
  hypothesis package is now: open/connected/nonempty chart, analytic graph,
  gradU = 0, cvec != 0, det HessU != 0, FIXED good triple -- Case B's exact
  standing hypotheses (H != 0 pointwise follows from det H != 0).
  NEXT = the branch case scaffold (H11 != 0 / H11 == 0 & H22 != 0 / both == 0
  forces H12 != 0 by det H != 0) + the four certificates (the remaining core).
- 2026-07-07 (cont.): **branch scaffold + slot calculus LANDED**:
  (i) dip_wit_core_scaffold - wit_core's conclusion from THREE branch hypotheses
  brH11/brH22/brH12 (full chart package + one Hessian entry nonvanishing along the
  chart), via the pointwise det_2 entry dichotomy + HessU_entry_chart_shrink
  (+ real_analytic_on_HessU_entry_chart);
  (ii) the H11-certificate ground layer: slot j v / perp2 c, the master d_phase_slot
  law, the six collapsed d_*_moment_x_slot laws, the six perpendicular corollaries
  (c . v = 0: phase derivative dies, weight survives - the source of prop:vpair11's
  d_vj formulas), and the D*_paper_eq_d_moment glue.
  REMAINING for the H11 branch (cor:H11-closed, tex 4004-4365): (1) the gauge
  dictionary layer: Phi2/H-entries' v_j-derivatives assembled from the slot laws
  through gradU_dip_component_moments / HessU_dip_entry_moments (chain rule along
  slot directions - needs the x-derivative of the HessU entry fields in slot
  directions, i.e. differentiating the moment dictionary once in x);
  (2) prop:vpair11's determinant identity Delta_ij^(11) = -8ag^2/H11 (s_i c_j R_j -
  s_j c_i R_i); (3) cor:vpair11's rank-3 criterion; (4) prop:szero-local +
  the uphi/residual sub-branches; (5) the branch conclusion in wit_core form
  (mstarg-witness from rank-3: rank D_x Phi = 3 on the triple's six variables
  CONTRADICTS mstarg == 0? NO - connect via: if mstarg == 0 on the chart then the
  IFT-graph argument pins x locally to a codim-3 set vs openness. The precise
  bridge from 'rank-3 on the bad set' to the wit-witness is the step-5-style
  assembly of the H11 branch - spell it out when (1)-(3) are in).
- 2026-07-07 (cont.): **ARCHITECTURE CORRECTION recorded (see §0)** + first
  corrected-path brick: dEjm_zero1, DM_paper_x_perp_slot_1/2/3,
  dEjm_perp_slot_value, gradU_dip_xderiv_perp_slot — the x-derivative of the
  gradient field AT FIXED omega in a perpendicular slot direction, invariant form
  d_{slot m v} Phi_j = 2 g (gamma_j . v) Im(cnj A phi_m) (the paper's
  d_vj Phi2 = -2ag s_j), matching has_derivative_gradU_dip_x_explicit's map.
  NEXT on the corrected path: (i) the HessU-entry perp-slot derivatives (chain
  rule through HessU_dip_entry_moments — the Hcmat/gradc/Uc x-derivatives in slot
  directions via the same collapse); (ii) prop:vpair11's Delta identity;
  (iii) the rank-3 criterion feeding regular_value_local_chart /
  charts_core_Nn-shaped bundles on the det-H=0 set; (iv) restate D3'/D4' with the
  retained conjuncts and adapt m5_D34_residual (drop the subset step).

## 4. What is already banked (2026-07-06, commits 07b21bc..)

Elementary C^ω layer; joint (c,x)-analyticity of moments/mstarg + closure kit +
`matrix_gram_entry`; joint (x,ω)-analyticity of `gradU`; `deriv`-of-analytic (1-D);
analytic IFT with uniqueness neighbourhood; the chart engine
(`dip_critical_graph_dichotomy(_unique)`); the 4b interface
(`dip_critical_chart_nowhere_dense`). Remaining besides `wit`: 4c (degenerate stratum
`det HessU = 0` — the paper closes its `H ≡ 0` residue in `app:H0res`,
`prop:h0res-meager`; same interface pattern applies) and layer 5 (the Lindelöf
covering splice into Robust3).
