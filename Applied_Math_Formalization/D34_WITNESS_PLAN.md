# D34 layer 4b: the transversality witness — work plan

_As of 2026-07-06. The single remaining GENUINE-MATHEMATICS obligation of the analytic
route to a proof-complete `F0_dip_nonempty` (besides the degenerate stratum 4c)._


## 0. ARCHITECTURE CORRECTION (2026-07-07) — READ FIRST

`m5_D34_subset_mstarg_residual` (Robust3:2365) is a pure `blast` ENLARGEMENT: the true
D34 target (`m5_D34_residual`, Robust3:2665) RETAINS `det HessU = 0`, `A_cart != 0`,
and `not (EX Dx. gradU-x-derivative surjective)`. The two proof holes were stated for the
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
- Layer-5 restatement: replace the two stubbed lemmas by versions RETAINING
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
It plays the role for 4b that `nd` plays in the two Robust3 proof holes. If the witness
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
- 2026-07-08: **step i.5 DONE: the Hessian-entry x-derivative assembled** (in the
  bridge): `has_derivative_HessU_dip_entry_x` - the x-derivative (at FIXED omega) of
  a single Hessian entry HessU(.,omega)$k$l, assembled from the three block
  derivatives (V, gradcV, Hcmat) through HessU_dip_entry_moments's linear
  combination (Dcvec_dip/D2cvec_dip/gain_dip/the gdip jets are all constant in x).
  Machinery: dV_x/dgradcV_x/dHcmat_x named block-derivative abbreviations (+ their
  already-proven perp-slot values repackaged); has_derivative_gradcV_inner_x /
  has_derivative_Hcmat_bilinear_x (a fixed vector, resp. pair of vectors, paired
  against the gradcV/Hcmat block via bounded-linearity + has_derivative_eq_rhs).
  `HessU_dip_entry_perp_slot_value`: the VALUE of that derivative at a
  perpendicular slot direction (frechet_derivative_at + fun_cong) - this is what
  the branch certificates differentiate directly, giving H11/H12/H22's v-slot
  derivatives as a corollary (k=l=1 / k=1,l=2 / k=l=2).
  GOTCHAS (new): `define X where "X = ..."` introduces a genuine LOCAL CONSTANT,
  so a fact proven using the abbreviated name does NOT syntactically match a goal
  stated in unabbreviated form even though propositionally equal (unfolding the
  _def on the goal vs on the fact diverge) - avoid `define` for this kind of
  "prove in short form, restate in long form" pattern; write everything out in
  full instead (verbose but safe), or use `let ?x = "..."` carefully (still
  fragile under bulk regex editing - a manual full-rewrite was ultimately safer
  than patching). Bare `HessU (...) $ k $ l` inside a `frechet_derivative (\y. ...)`
  argument can hit the fps_nth/vec_nth $-ambiguity even where the identical
  pattern parsed fine as a has_derivative LHS - spell vec_nth explicitly there.
  `fixes m :: 'n` used with `slot` needs the explicit `'n::finite` sort annotated
  at the SPECIFIC lemma (not inherited from context).
- 2026-07-08 (cont.): **step (ii) DONE - G11 quotient-rule derivative + Delta_ij
  determinant identity** (in the bridge): `Phi2_perp_slot_value` (Phi_2's perp-slot
  value in clean closed form, via bounded_linear.has_derivative composed with
  has_derivative_gradU_dip_x_explicit + frechet_derivative_at + fun_cong, matched
  against gradU_dip_xderiv_perp_slot via arg_cong on the j=2 component); `G11`
  (=H22-H12^2/H11) + `has_derivative_G11_x` (quotient-rule x-derivative, fixed
  omega, assuming H11 != 0, built from has_derivative_HessU_dip_entry_x at
  (2,2)/(1,2)/(1,1) via has_derivative_mult/has_derivative_divide'/has_derivative_diff
  -- kept in frechet_derivative notation for the three Hessian entries rather than
  hand-flattened); `G11_perp_slot_value` (the value at a perpendicular slot, via
  frechet_derivative_at + fun_cong); `Delta_ij` (the rank-3 Jacobian determinant,
  invariantly: v_i = slot i (perp2 c)) + `Delta_ij_identity` (Phi_2-factors collapse
  to closed form; G11-factors stay packaged via G11_perp_slot_value, available on
  demand).
  CAUGHT BEFORE RUNNING: an early draft of G11_perp_slot_value's RHS mistakenly
  copied Phi_2's closed-form formula for the H22 term -- H22 (a Hessian entry) and
  Phi_2 (a gradU component) are UNRELATED quantities; the fix is to state such
  "value" lemmas in frechet_derivative notation (mechanical, zero algebra) rather
  than hand-inventing a collapsed closed form whenever the collapse is genuinely
  nontrivial (H22's own perp-slot value is itself a 7-term dHcmat_x/dgradcV_x
  expression, not reducible to anything as simple as Phi_2's).
  GOTCHA: subscripted Unicode in a `section`/`subsection` title (e.g.
  \<Delta>\<^sub>i\<^sub>j) can trigger a spurious "Undefined document antiquotation: sub"
  parse error -- use plain ASCII (Delta_ij) in section/subsection headers; body
  text \<open>...\<close> tolerates the subscripts fine.
- 2026-07-08 (cont. 2): **step (iii) DONE - the rank-3 criterion (cor:vpair11)
  itself**, in fully invariant form (in the bridge): the paper's block-triangular
  argument needs Phi_1 independent of every v-slot, a fact of their SPECIFIC
  omega-parametrization -- NOT automatic for our (sin-theta-cos-phi,...) angular
  coordinates (gradU_dip_xderiv_perp_slot gives BOTH components j=1,2 the SAME
  nonzero shape 2*g0*(gamma_j.v)*W_m). Resolved via an invariant fix, not glossed
  over: `e_par` (the omega direction pushing forward to c under Dcvec_dip, via
  bij_matrix_vector_mult + inv_into UNIV) + `Dcvec_dip_e_par` (its defining
  property, proven via ELEMENTARY matrix_def/basis-decomposition rather than
  matrix_works/matrix_vector_mul, which resolve to the Vector_Spaces.linear (*s)
  (*s) typeclass variant in this heap, not the standard `linear` from
  bounded_linear.linear, with no bridging fact findable -- the elementary route
  sidesteps this); `Phi_par := gradU . e_par` (playing Phi_1's role) +
  `Phi_par_perp_slot_zero` (its perpendicular-slot x-derivative vanishes BY
  CONSTRUCTION: D Phi_par(slot m v) = 2g0 W_m (Dcvec_dip(e_par).v) = 2g0 W_m
  (c.v) = 0 -- the invariant analogue of the paper's own omega-gauge choice).
  Then the criterion itself: `Jac3` (the 3x3 Jacobian determinant of
  (Phi_par,Phi2,G11) restricted to (U, slot_i(perp2 c), slot_j(perp2 c)), via the
  existing det3 primitive) + `Jac3_identity` (Jac3 = D Phi_par(U) * Delta_ij(i,j),
  the block-triangular cofactor-expansion collapse) + `Jac3_nonzero_criterion`
  (given D Phi_par(U) != 0 for some x-direction U and Delta_ij(i,j) != 0 -- the
  paper's own two hypotheses -- Jac3 != 0, i.e. the restriction of
  D(Phi_par,Phi2,G11) to (U,slot_i,slot_j) has full rank 3). This IS cor:vpair11
  in fully invariant (gauge-free) form.
  GOTCHA: another vec_eq_iff-as-simp-member failure (twice) -- plain
  `simp add: vec_eq_iff ...` does NOT auto-apply the iff as a splitting rule;
  use `proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix i :: 2 show ...` instead.
  GOTCHA: mistyped U's fixes-clause as real^2 instead of (real^2)^'n (U is an
  x-space tangent direction matching x's type, not an omega-space vector like
  omega/omega0/omegas) -- caught immediately via the resulting type-clash error.
  REMAINING for the H11 branch (cor:H11-closed): (iv) prop:szero-local + the
  uphi/residual sub-branches; (v) layer 5 (Robust3 splice).
- 2026-07-08 (cont. 3): **the symmetric H22 branch (prop:vpair22/cor:vpair22)
  DONE** (in the bridge) via DIRECT REUSE of the H11-branch pattern: `G22`
  (:= H11 - H12^2/H22) + `has_derivative_G22_x` (quotient-rule x-derivative,
  H22 != 0) + `G22_perp_slot_value`; `Delta_ij_22` (:= det d(Phi2,G22)/d(v_i,v_j)
  -- SAME Phi2 as prop:vpair11, paired with G22 instead of G11) +
  `Delta_ij_22_identity`; `Jac3_22` + `Jac3_22_identity` (= D Phi_par(U) *
  Delta_ij_22(i,j)) + `Jac3_22_nonzero_criterion` -- cor:vpair22's rank-3
  criterion, fully invariant. Crucially, `Phi_par`/`Phi_par_perp_slot_zero`
  (the H11-branch's invariant fix for Phi_1's v-independence) and `det3` were
  REUSED VERBATIM with zero changes, since Phi_par doesn't depend on the
  H11/H22 choice at all -- checked the paper's prop:vpair22/cor:vpair22 proofs
  first and confirmed they are STRUCTURALLY IDENTICAL to vpair11/cor:vpair11
  (same Phi2 factor, same block-triangular argument), just G11->G22. All five
  theorems checked cleanly on the FIRST eval_at attempt.
  NOTE: this is the BARE rank-3 criterion (cor:vpair22), not the deeper
  cor:vpair22-full (needs a real-analytic lifting argument with auxiliary
  variables, codimension counting in an EXTENDED space -- a genuinely
  different, larger piece of work, not yet attempted).
  REMAINING for Case B (cor:caseBmeager, the full H-not-identically-0 closure):
  (iv-a) cor:vpair22-full's auxiliary-variable lifting (needs new machinery,
  Hausdorff-dimension/codimension-in-extended-space arguments -- NOT the
  has_derivative toolkit used so far); (iv-b) cor:uphi-exhausted (the u-slice
  D Phi_1|_{E_u}=0 residue is nowhere dense -- needs prop:uphi-codim3's
  REAL-ANALYTIC isolated-zero argument, a different flavor of proof entirely,
  likely drawing on Applied_Math_Analytic_Complex/Real_Analytic_IFT); (iv-c)
  cor:Lambda-closed (the H12=0,H22!=0 branch -- needs FOUR more sub-
  propositions: Lambda-simple, Lambda-onefold, Lambda-high, double-impossible,
  a substantial standalone piece); (iv-d) app:H0res/prop:h0res-meager (the
  H-identically-0 degenerate stratum, a whole separate appendix); (v) layer 5
  (Robust3 splice) once the above close.
  NEXT: (ii) prop:vpair11's G11 (=H22-H12^2/H11) perp-slot derivative via
  has_derivative_divide'/quotient rule from the H11/H12/H22 corollaries above,
  then the Delta_ij determinant identity; (iii) rank-3 criterion; layer 5.
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
- 2026-07-08: **(i) DONE — HessU-entry perp-slot derivatives** (bridge): the three
  block x-derivatives at fixed c (has_derivative_Uc_x, has_derivative_gradUc_comp_x,
  has_derivative_Hcmat_entry_x) plus perp-slot values (Uc = 0; gradUc_i = 2 v_i
  Im(cnj A phi_m); Hcmat_kl = 2[v_l Re(cnj phi_m M_k)+v_k Re(cnj M_l phi_m)
  -(v_k x_l + x_k v_l)Re(cnj A phi_m)]). Supporting: Mcfun/M2cfun = paper moments
  glue; uniform dMcfun_x/dM2cfun_x with has_derivative laws (reuse the six heap
  has_derivative_*_moment_x) and perp collapses. These are the gauge/frame-free
  generators of the paper's d_vj H12/H22.
  NOTE the M5 x-derivative of a Hessian ENTRY along a v-slot combines all three
  blocks via HessU_dip_entry_moments's chain-rule structure (D2cvec/Dcvec jets are
  omega-side, constant in x; only V, gradcV, Hcmat carry x). Assemble that entry
  x-derivative next, then:
  (ii) prop:vpair11's Delta_ij^(11) = -8ag^2/H11 (s_i c_j R_j - s_j c_i R_i);
  (iii) rank-3 criterion -> regular_value_local_chart bundles on det-H=0;
  (iv) restate D3'/D4' with retained conjuncts, adapt m5_D34_residual.

## 4. What is already banked (2026-07-06, commits 07b21bc..)

Elementary C^ω layer; joint (c,x)-analyticity of moments/mstarg + closure kit +
`matrix_gram_entry`; joint (x,ω)-analyticity of `gradU`; `deriv`-of-analytic (1-D);
analytic IFT with uniqueness neighbourhood; the chart engine
(`dip_critical_graph_dichotomy(_unique)`); the 4b interface
(`dip_critical_chart_nowhere_dense`). Remaining besides `wit`: 4c (degenerate stratum
`det HessU = 0` — the paper closes its `H ≡ 0` residue in `app:H0res`,
`prop:h0res-meager`; same interface pattern applies) and layer 5 (the Lindelöf
covering splice into Robust3).

- 2026-07-08 (Codex): **u-slice Tier 1 LANDED** in a separate branch theory:
  `Appendix/AnalyticBridge/D34_UPhi_Branch.thy` plus dev scratch
  `M5_Dev_UPhi/`.  Added `F_eta`, `real_analytic_on_F_eta`, `F_eta_at_0`,
  and `F_eta_zeros_nowhere_dense`, using the existing
  `real_analytic_1d_nowhere_dense_zeros` workhorse with witness `u=0`.
  Verified:
  `Applied_Math_M5_UPhi` BUILD_EXIT=0 and `Applied_Math_D34_Analytic`
  BUILD_EXIT=0 after registering the new UPhi theory.  Note: Isabelle rejects a
  second session rooted at `Appendix/AnalyticBridge`, so the permanent branch is
  a separate theory in the existing D34 analytic session rather than a second
  session in the same directory; the shared bridge file itself was not edited.
  Tier 2 (`prop:uphi-reduce`, the parallel-slot derivative of `Phi_par`) remains
  open.

- 2026-07-08 (Codex, cont.): **u-slice Tier 2 derivative substrate LANDED** in
  the UPhi branch file, still without touching the shared bridge.  Added
  `DM_paper_x_slot_1`, `DM_paper_x_slot_2`, `DM_paper_x_slot_3`,
  `Phi_par_slot_value`, and `Phi_par_parallel_slot_value`.  These expose the
  Fréchet derivative of `Phi_par` on a general slot and on the parallel slot
  `slot m (cvec_dip omega0 omegas omega)`.  The remaining `prop:uphi-reduce`
  gap is now explicitly documented in `D34_UPhi_Branch.thy`: the c-adapted
  gauge dictionary (`a,b,b1`, `E1`, `eta`) and the final scalar trigonometric
  rewrite to `F_eta` are still needed.

- 2026-07-08 (Codex, cont.): **u-slice Tier 2 pointwise reduction LANDED with
  one precise upstream proof hole**.  Added `ucoord`, `eta_par`,
  `uphi_E1_deriv_F_eta`, `uphi_scalar_zero_iff`,
  `Phi_par_parallel_slot_F_eta_identification`, and `uphi_reduce_pointwise`.
  The new theorem `uphi_reduce_pointwise` proves the branch's pointwise
  zero-equivalence from the isolated gauge-dictionary identity:
  the parallel-slot derivative of `Phi_par` vanishes iff
  `F_eta eta kappa u = 0`, assuming `det Dcvec != 0`, `c != 0`, the slice
  equation `Im (M_1)=0`, `Phi_par=0`, `a>0`, and `gain_dip>0`.
  The sole `proof hole` is `Phi_par_parallel_slot_F_eta_identification`, which
  exactly states the missing c-adapted gauge/algebra bridge from
  `Phi_par_parallel_slot_value` to `-2*a*gain*kappa*F_eta eta kappa u`.
  This follows the documented proof hole-upstream escape hatch: Tier 1 and the
  downstream Tier 2 scalar cancellation are shipped, while the remaining
  upstream bridge is precision-scoped.

- 2026-07-08 (Claude, cont.): **cor:H12zero investigation + conditional landing.**
  Started on cor:H12zero (the entry point to cor:Lambda-closed) expecting it to
  reuse Phi_par/det3 the same clean way H11/H22 did. Found a genuine obstacle
  before writing anything: prop:H12zero needs H11 independent of every v-slot
  (mirroring the Phi_1 v-independence issue already found and fixed via
  Phi_par/e_par). Tried the same e_par-contraction fix for H11 (call it H_par)
  -- most terms collapse cleanly, but a residual D2cvec_dip(e_par)(e_par).v term
  does not obviously vanish (a differential-geometry argument about cvec_dip's
  structure as a shifted linear projection of the unit sphere suggests this is
  a real obstruction, not just an unsimplified artifact -- not formally settled
  either way). Retracted the earlier "high confidence, same pattern" claim in
  PARALLEL_WITH_CODEX.md.
  Rather than block on this, landed everything that IS honestly provable:
  H_par + has_derivative_H_par_x + H_par_slot_value (fully proven, unconditional);
  Phi_par_uslot_value + Phi2_uslot_value (fully proven, unconditional -- turned out
  the existing has_derivative_gradU_inner_x/has_derivative_gradU_dip_x_explicit were
  ALREADY general-direction, no new "u-slot" derivation needed, contrary to what I
  expected); Lambda_ij + Jac3_H12zero + Jac3_H12zero_identity +
  Jac3_H12zero_nonzero_criterion -- the last two carry `h_par_vslot_zero` as an
  EXPLICIT NAMED HYPOTHESIS (not proven, not hidden), matching the project's
  existing pattern of carrying genuine nondegeneracy conditions.
  Applied_Math_D34_Analytic + dev session BUILD_EXIT=0 (both splices).
  NEXT: (a) attempt the D2cvec_dip(e_par)(e_par).perp2(c) computation directly to
  settle h_par_vslot_zero, or (b) leave it carried and move to scoping
  cor:vpair22-full or app:H0res, or layer-5 assembly progress.

- 2026-07-08 (Claude, cont. 2): **h_par_vslot_zero definitively resolved FALSE**
  (not just unresolved). Isolated the residual precisely: H_par's v-slot value
  = 2*gain_dip(omega)*Im(cnj(A)*phi_m)*Q, Q := D2cvec_dip(omega)[e_par,e_par].perp2(c)
  (omega-only). Built explicit witness (omega0=(pi/4,0), omegas=(3pi/4,0),
  omega=(pi/3,pi/6)), solved Dc(e_par)=c exactly (e_par=(sqrt3-sqrt6/2,sqrt6/6)),
  closed form Q=23*sqrt6/24-5*sqrt3/4. Machine-verified via
  HOL-Decision_Procs.Approximation's `approximation` method: 0.18<Q<0.19, definitely
  nonzero -- BUILD_EXIT=0 on the standalone check. Since Q is real-analytic and
  nonzero at a generic point, its zero set is nowhere dense (same logic as
  real_analytic_1d_nowhere_dense_zeros) -- h_par_vslot_zero fails GENERICALLY, not
  just at this witness. The H_par (contract-both-indices-with-e_par) approach for
  cor:H12zero is a DEAD END, not a gap to patch -- see diary for the full
  derivation and why the first-derivative fix (Phi_par) doesn't generalize to
  second derivatives (needs geodesic/normal-coordinate machinery, not present in
  this project).
  cor:Lambda-closed is ON HOLD pending either that new infrastructure or a
  different invariant characterization of H11 entirely.

- 2026-07-08 (Claude fork, cont. 3): **app:H0res B_dip transversality landed** +
  an architectural finding: a fully-proven H0res scaffold already exists in
  Appendix/Nonemptiness_Regnonzero_Appendix.thy but is disconnected from
  Nonemptiness_Robust3.thy (same situation as the earlier
  m5_D34_subset_mstarg_residual enlargement) and its lemmas are generic/
  uninstantiated, with prop_h0res_meager taking the meager conclusion as a
  HYPOTHESIS rather than deriving it (a codim-1-to-meager-projection gap the
  file itself flags but doesn't close). Landed the D34-connected version
  instead: beta_h0/B_dip/B_dip_uslot_transversal in
  Appendix/AnalyticBridge/D34_H0res_Branch.thy (registered in ROOT alongside
  D34_UPhi_Branch), BUILD_EXIT=0, independently re-verified.
  REMAINING: lift the one-cut transversality (single j) to the joint
  three-cut codimension->=3 argument (needs a det3/Jac3-style but three-fold
  rank argument, not attempted); the other four H0res pieces (residue-control,
  S=0 branch, two/three-cosine branches) scoped but untouched.

- 2026-07-08 (Codex, layer-5 wiring correction): **D34 residual obligations
  restated to the tight Case-B target** in `Appendix/Robust3/Nonemptiness_Robust3.thy`.
  The legacy `m5_D34_subset_mstarg_residual` loose enlargement is still present
  for reference but no longer used by `m5_D34_residual`.  The two remaining
  D34 obligations now retain the important conjuncts:
  `det HessU = 0`, `A_cart != 0`, `not surj(DM_paper_x ...)`, `det Dcvec != 0`,
  `cvec != 0`, and failure of the `x`-derivative of `gradU` to be surjective.
  Concretely, `m5_D34_D3_collinear`, `BadXGW`, `branchP_indep_charts_Nn`
  through `m5_D34_D4_branchP`, and the D34 assembly split now target the actual
  retained residual rather than the older `gradU + detDc + cvec + not-surj-DM`
  superset.  `Applied_Math_Appendix_Full` rebuilt with `BUILD_EXIT=0`.

- 2026-07-08 (Codex, D3 next target): **`m5_D34_D3_collinear` is no longer an
  opaque `proof hole`**.  Added a retained D3 fibre `D3BadXG` and proved the D3 branch
  by checked assembly from two precise residuals:
  `d3_retained_arc_charts_Nn` (per-C1-arc chart bundle for the exact retained
  fibre) and `d3_active_collinear_finite_arc_cover` (finite active
  phase-collinear witness-arc cover).  `m5_D34_residual` now passes the existing
  `hsep`/`kdiff` assumptions into D3; `meager_rank_deficient_stratum` already had
  those assumptions, so no capstone API change was needed.  Current Robust3
  on-path proof holes are exactly the two new D3 residuals plus the existing D4
  `branchP_indep_charts_Nn`.  Verified `Applied_Math_Appendix_Full`
  `BUILD_EXIT=0`.

- 2026-07-08 (Codex, D3 cover factoring): **the active D3 cover theorem is now
  checked glue, not an open mathematical obligation**.  Added
  `d3_finitely_arc_coverable` and proved `d3_active_cover_from_angle_cover`,
  then changed the open cover theorem to the pure angle-locus statement
  `d3_collinear_locus_finite_arc_cover`.  The on-path Robust3 proof holes are now:
  `d3_retained_arc_charts_Nn`, `d3_collinear_locus_finite_arc_cover`, and
  `branchP_indep_charts_Nn`.  This is the intended shape for grafting the
  `M5_Dev_curvecover` C1 phase-collinear cover.  Verified
  `Applied_Math_Appendix_Full` with `BUILD_EXIT=0`.

- 2026-07-08 (Codex, D3 nonsing side condition): **the D3 curve-cover target now
  carries the required `nsing_all` hypothesis and F0 proves it concretely**.
  Added `d3_crossTheta`, `phase_collinear_iff_d3_crossTheta`,
  `d3_collinear_d1`, `d3_collinear_d2`, and `d3_collinear_nsing_all`; threaded
  the predicate through the D3/D34 meagerness and feasible-witness chain; and
  discharged it in `F0_dip_nonempty` for `ω0 = vector [pi/2,0]`,
  `ωs = vector [0,0]`, `δ = pi/4`.  This preserves the current three Robust3
  open obligations but fixes the statement shape for grafting
  `M5_Dev_curvecover`.  Verified `Applied_Math_Appendix_Full` with
  `BUILD_EXIT=0`.

- 2026-07-09 (Codex, heap/frontier split): **moved the active M5/F0 frontier
  into `Appendix/Robust4/Nonemptiness_Robust4.thy`**.  Robust3 is now the stable
  heap theory ending after `d3_active_cover_from_angle_cover`; Robust4 imports
  `Applied_Math_Appendix_Full.Nonemptiness_Robust3` and contains the three open
  frontier obligations plus `F0_dip_nonempty`.  `ROOT` now has
  `Applied_Math_Appendix_Full` for Robust3 and
  `Applied_Math_Appendix_Frontier` for Robust4.  Verified both sessions with
  `BUILD_EXIT=0`.
