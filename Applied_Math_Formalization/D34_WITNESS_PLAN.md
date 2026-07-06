# D34 layer 4b: the transversality witness — work plan

_As of 2026-07-06. The single remaining GENUINE-MATHEMATICS obligation of the analytic
route to a sorry-free `F0_dip_nonempty` (besides the degenerate stratum 4c)._

## 1. The interface (DONE, in the bridge heap)

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

## 4. What is already banked (2026-07-06, commits 07b21bc..)

Elementary C^ω layer; joint (c,x)-analyticity of moments/mstarg + closure kit +
`matrix_gram_entry`; joint (x,ω)-analyticity of `gradU`; `deriv`-of-analytic (1-D);
analytic IFT with uniqueness neighbourhood; the chart engine
(`dip_critical_graph_dichotomy(_unique)`); the 4b interface
(`dip_critical_chart_nowhere_dense`). Remaining besides `wit`: 4c (degenerate stratum
`det HessU = 0` — the paper closes its `H ≡ 0` residue in `app:H0res`,
`prop:h0res-meager`; same interface pattern applies) and layer 5 (the Lindelöf
covering splice into Robust3).
