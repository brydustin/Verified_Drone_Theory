# Working in parallel with Claude on this repo

This file is instructions for **Codex/ChatGPT** (or any other agent) working on
this Isabelle formalization *at the same time* as Claude, in the same
checkout. Claude wrote it after finishing the `H11`/`H22` rank-3 branches, to
avoid the two of us burning tokens re-deriving each other's context or
clobbering each other's files. Read this whole file before touching anything.

Read `D34_WITNESS_PLAN.md` and `FORMALIZATION_DIARY.md` next — they are the
living project log (dated entries, most recent at the bottom of each). They
tell you what's actually been proved vs. what's still `sorry`, which matters
more than anything in this file.

## 1. The project, in one paragraph

We're formalizing a nonemptiness proof (`F0_dip_nonempty`) for a drone/antenna
configuration problem. The overarching strategy is the "analytic route": build
real-analytic machinery to discharge sorries in
`Appendix/Robust3/Nonemptiness_Robust3.thy` by porting the paper's Case-B
branch certificates. The paper source is
`../Applied Math/nonemptiness_unified_singlefile_complete.tex` (also readable
as the compiled `.pdf` next to it) — **always check the paper's exact
statement and proof before writing any Isabelle**, don't guess the math from
variable names.

## 2. Architecture rules (read before running `isabelle build` or `jedit`)

- **Dev-scratch-then-splice pattern.** Never write new theorems directly into
  a big shared bridge file. Instead:
  1. Create your own directory `M5_Dev_<Name>/` with a `ROOT` file:
     ```
     session Applied_Math_M5_<Name> in "." = Applied_Math_D34_Analytic +
       options [document = false, quick_and_dirty = true, timeout = 3600]
       theories
         Scratch_<name>
     ```
  2. Write and verify `Scratch_<name>.thy` there (imports
     `"Applied_Math_D34_Analytic.D34_Analytic_Bridge"`), testing incrementally
     with `isabelle eval_at` (fast, no full rebuild) before doing a full
     session build.
  3. Only once every theorem is green, integrate it into a permanent file
     (see §3 — **not** the shared bridge file).

- **`isabelle eval_at` for fast iteration:**
  ```
  isabelle eval_at -d . -d <Munkres-dir> -d <afp-dir> <file>.thy <line> 'thm <name>'
  ```
  This type-checks up to `<line>` and evaluates the given command against the
  running theory — much faster than a full session build while drafting.

- **Full session build once a dev scratch is done:**
  ```
  isabelle build -b -d . -d <Munkres-dir> -d <afp-dir> -d M5_Dev_<Name> Applied_Math_M5_<Name>
  ```
  Check `BUILD_EXIT=0` before moving on.

- **CRITICAL gotcha (Claude hit this and the user caught it):** never open
  `jedit`/`build` with `-l Applied_Math_D34_Analytic` while the file you're
  editing is `D34_Analytic_Bridge.thy` itself — that file *is* that session's
  own baked-in theory. jEdit will treat an already-compiled heap member as a
  live editable buffer, which is broken. If you need to view/edit that file
  interactively, load jEdit against its *parent* session
  (`-l Applied_Math_Appendix`) instead, so it's processed live from source.

- Isabelle/AFP directory paths you'll need (adjust if your checkout differs):
  `-d /home/dusty/Desktop/Isabelle/Vern_Paulsen_QC/Imported_Munkres_Topology`
  and `-d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys`.

## 3. Conflict-avoidance protocol (the important new part)

Both of us will be editing this repo at once. The single biggest risk is two
agents both appending to the tail of the same big file
(`Appendix/AnalyticBridge/D34_Analytic_Bridge.thy`, currently ~4266 lines and
growing) — that produces constant git merge conflicts on the same few lines.

**Rule: do not append to `D34_Analytic_Bridge.thy`.** Instead:

- Create your own permanent theory file, e.g.
  `Appendix/AnalyticBridge/D34_UPhi_Branch.thy`, that
  `imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"` and holds *your*
  theorems. Give it its own session (`Applied_Math_D34_UPhi`, parented on
  `Applied_Math_D34_Analytic`, same pattern as the dev-scratch `ROOT` above,
  but this one is **permanent**, not stubbed away afterward).
- This file coexists with the main bridge rather than being merged into it.
  Final integration (deciding whether/how to fold branch-files together, and
  wiring things into `Nonemptiness_Robust3.thy`) happens later, explicitly,
  once both threads are stable — don't try to pre-empt that now.
- `D34_WITNESS_PLAN.md` and `FORMALIZATION_DIARY.md` are both append-only
  logs. Append your own dated entries at the very end of each. Before
  pushing, always `git pull --rebase origin main` first. If rebase produces a
  conflict in these two files, it will be a trivial "both sides added text at
  the end" conflict — resolve by **keeping both blocks** (concatenate, order
  doesn't matter), never delete or edit the other party's entry.
- Never edit or delete a theorem, comment, or diary/plan entry the other
  party wrote. If something looks wrong, say so in your own diary entry
  (`TO CLAUDE: ...`) rather than silently changing it.
- Commit in small verified units, same discipline as the rest of this
  project: dev-scratch green → session build green → integrate into your own
  branch file → rebuild → commit + push. Don't batch unrelated work into one
  commit.
- Use `git add <specific files>`, never `-A`/`.` — this repo accumulates
  stray scratch directories from past sessions; don't sweep them into your
  commits.

## 4. The "sorry upstream" protocol

If your assigned piece needs a fact that depends on something Claude is
actively building (or hasn't finished yet), **do not block waiting for it.**
Instead:

1. State the missing fact as an explicit placeholder in *your own* file:
   ```isabelle
   (* NEEDS FROM MAIN BRANCH: <one-line description of what this should say
      and why you need it — e.g. "Delta_ij nonzero at this configuration,
      currently being built in D34_Analytic_Bridge.thy's H11 branch"> *)
   lemma needed_fact_name:
     assumes ...
     shows ...
     sorry
   ```
2. Keep building on top of it as if it were proved. This lets you verify your
   own downstream reasoning is sound modulo that one gap, without waiting on
   anyone.
3. Keep a running list of every such `sorry` at the top of your file (a
   `NEEDS:` comment block) so re-integration later is just "replace this
   sorry with the real theorem name" — assuming the statement shape matches;
   flag it in the diary if you're not sure it will.
4. Symmetrically, Claude will do the same for anything needed from your work
   that isn't ready yet.

This is standard practice in large multi-author Isabelle developments
(quick_and_dirty sorries as a synchronization primitive) — it's not cheating,
it's how the two threads stay decoupled.

## 5. Task assignment

**Your target is the u-slice branch: `prop:uphi-reduce` / `prop:uphi-codim3`
/ `cor:uphi-exhausted`.** Not `app:H0res`. This section explains the decision
and then gives an exact, tiered build plan — read it in full before writing
any Isabelle, since it fixes names and types you should reuse rather than
invent your own.

### Why this one, and not `app:H0res`

I compared the two candidates by actually reading both in the paper source
(`../Applied Math/nonemptiness_unified_singlefile_complete.tex`):

- **The u-slice branch** is 3 environments (one definition, two
  propositions, one corollary) across paper lines 3826–4000 — small, and
  I confirmed the core analytic lemma it needs is *already proved* in this
  repo (see Tier 1 below).
- **`app:H0res`** (lines 3086–3578) is a *whole appendix*: 6 subsections,
  roughly 20 propositions/lemmas/corollaries, covering many distinct residual
  sub-branches (`B_1=B_2=B_3=0`, residue control for `(a_1,a_2)`, the `S=0`
  branch, branches with two/three vanishing cosines, a closeout section).
  It is not a single well-scoped task — it would itself need to be split
  into several pieces before being handed to one agent for one sitting, and
  attempting the whole thing risks a shallow pass over everything rather
  than a finished piece of anything.

So: u-slice branch, definitely. If you finish it and want `app:H0res` next,
say so in the diary first (`TO CLAUDE: ...`) so we can split it the same way
`cor:caseBmeager` was split, rather than you picking a sub-piece unilaterally.

### The math, precisely

Read the paper section right after `cor:vpair11`'s corollary, titled "The
vanishing $u$-slice branch" (lines ~3826–4000). In brief:

- `\eta := g_1/(2g)`, `F_\eta(u) := \cos(\kappa u) - \kappa(u-\eta)\sin(\kappa u)`.
- `prop:uphi-reduce`: on gauge `b=0`, `D\Phi_1|_{E_u}=0` (where
  `E_u := span{\partial_{u_1},\partial_{u_2},\partial_{u_3}}`, i.e. moving
  each triple element *parallel* to `c`) is equivalent to
  `F_\eta(u_j)=0` for `j=1,2,3`.
- `prop:uphi-codim3`: `F_\eta` is real-analytic, not identically zero
  (`F_\eta(0)=1`), hence has a discrete zero set, hence the branch is
  locally a finite union of codimension-3 coordinate slices.
- `cor:uphi-exhausted`: hence the branch is locally nowhere dense.

### Exact correspondence to existing Isabelle terms (do not rename these)

| Paper | Isabelle (already exists in the bridge / `Appendix/Nonemptiness_Robust1.thy`) |
|---|---|
| `g(\omega)` | `gain_dip \<omega>` (`= gdip (\<omega> $ 1)`) |
| `g_1 = \partial_{\omega_1} g` | `frechet_derivative gdip (at (vec_nth \<omega> 1)) 1` |
| `\kappa = |c|` | `norm (cvec_dip \<omega>0 \<omega>s \<omega>)` |
| `\Phi_1` | `Phi_par` (see `Appendix/AnalyticBridge/D34_Analytic_Bridge.thy` — proven independent of every *perpendicular* slot; you are now differentiating it in the *parallel* direction instead) |
| perpendicular slot for element `j` (`v_j`) | `slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))` |
| **parallel slot for element `j` (`u_j`) — new, build by direct analogy** | `slot j (cvec_dip \<omega>0 \<omega>s \<omega>)` |

### Tier 1 (fully specified, low risk — do this first, it stands alone)

Everything below is assembly from lemmas that already exist; I checked each
one is actually in the repo before writing this (not guessing from memory):

- `real_analytic_on_sin_comp`, `real_analytic_on_cos_comp`
  (`Analytic/Complex/Real_Analytic_Complex.thy:604,610` — given
  `real_analytic_on f U`, these give `real_analytic_on (\<lambda>x. sin (f x)) U`
  / `cos` respectively);
- `real_analytic_on_const`, `real_analytic_on_add`, `real_analytic_on_diff`,
  `real_analytic_on_mult`, `real_analytic_on_scaleR`,
  `real_analytic_on_compose` (`Analytic/Real_Analytic.thy`) — the
  composition algebra;
- the identity function's analyticity and a `connected UNIV` fact are small
  lookups I did *not* verify by name — search `Analytic/Real_Analytic.thy`
  for something like `real_analytic_on_id`, and HOL-Analysis's `Connected.thy`
  /`Abstract_Topology.thy` for `connected_UNIV`; if neither exists, both are
  one-line derivations (`convex_connected[OF convex_UNIV]` for the latter);
- **the key workhorse, already proved**, `Analytic/Real_Analytic.thy`,
  subsection "(1.6) Workhorse: a non-vanishing analytic function has
  nowhere-dense zeros":
  ```isabelle
  theorem real_analytic_1d_nowhere_dense_zeros:
    fixes f :: "real \<Rightarrow> real"
    assumes ana: "real_analytic_on f U" and conn: "connected U"
      and ex: "\<exists>x\<in>U. f x \<noteq> 0"
    shows "interior (closure {x \<in> U. f x = 0}) = {}"
  ```
  This *is* `prop:uphi-codim3`'s analytic content. Apply with `U := UNIV`.

Build exactly these, in this order, in your dev scratch:

```isabelle
definition F_eta :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "F_eta \<eta> \<kappa> u = cos (\<kappa> * u) - \<kappa> * (u - \<eta>) * sin (\<kappa> * u)"

theorem real_analytic_on_F_eta: "real_analytic_on (F_eta \<eta> \<kappa>) UNIV"
  (* compose sin_comp/cos_comp/mult/diff/const/scaleR as above *)

theorem F_eta_at_0: "F_eta \<eta> \<kappa> 0 = 1"
  unfolding F_eta_def by simp

theorem F_eta_zeros_nowhere_dense:
  "interior (closure {u. F_eta \<eta> \<kappa> u = 0}) = {}"
  (* real_analytic_1d_nowhere_dense_zeros[OF real_analytic_on_F_eta conn]
     with the witness from F_eta_at_0 *)
```

This tier is unambiguous and self-contained: land it, verify it, commit it,
even if Tier 2 below turns out to need more time.

### Tier 2 (needs real derivation work — the actual `prop:uphi-reduce`)

This is where you connect `F_eta`'s zero condition to the *actual*
`D\Phi_1|_{E_u}=0` statement, i.e. to `Phi_par`'s derivative in the
*parallel*-slot direction `slot j (cvec_dip \<omega>0 \<omega>s \<omega>)`.

Good news: the general (non-perpendicular-restricted) foundational fact you
need already exists —
```isabelle
lemma d_A_moment_x_slot:
  "d_A_moment_x x c (slot j v) = -(c \<bullet> v) *\<^sub>R (\<i> * phase c x j)"
```
(`Appendix/AnalyticBridge/D34_Analytic_Bridge.thy:2807-2808`). Note
`d_A_moment_x_perp` (line 2920) is just this specialized to `c \<bullet> v = 0`
— for the parallel slot you want `v := cvec_dip \<omega>0 \<omega>s \<omega>` instead,
which makes `c \<bullet> v = \<kappa>^2 \<noteq> 0`, i.e. genuinely nonzero, matching the
paper's claim that `\Phi_1`'s u-slice derivative is generically nonzero.
Redo the *same* derivation chain Claude used for
`gradU_dip_xderiv_perp_slot` (`Appendix/AnalyticBridge/D34_Analytic_Bridge.thy`
— search for it and read the proof) but starting from `d_A_moment_x_slot`
(general) instead of `d_A_moment_x_perp`, with `v := c` instead of
`v := perp2 c`. That gives you `D\Phi_1`'s value at a parallel slot in
closed form; matching it against `F_\eta(u_j)=0` is then the algebra in the
paper's own proof of `prop:uphi-reduce` (gauge `b=0`, `E_1 := g_1 a + 2g b_1`,
`\Phi_1 = a E_1`).

**If this doesn't come together cleanly:** use the sorry-upstream protocol
from §4. State `prop:uphi-reduce`'s conclusion as a `sorry`'d lemma with a
`NEEDS:` comment explaining exactly what's missing, and still land
`prop:uphi-codim3` + `cor:uphi-exhausted` built on top of it (marking their
own dependence on the sorry clearly). A Tier 1 + honestly-flagged Tier 2 gap
is a real, valuable, mergeable contribution — don't let Tier 2 block Tier 1
from shipping.

### Tier 3 (only after Tier 2, and only if you have room)

Lifting the single-variable "nowhere dense in `\<real>`" fact to the full
6-real-variable coordinate space (`cor:uphi-exhausted`'s actual conclusion):
the set `{F_\eta(u_1)=0 \wedge F_\eta(u_2)=0 \wedge F_\eta(u_3)=0}` is
nowhere dense in the ambient triple-configuration type. Check
`Appendix/AnalyticBridge/D34_Analytic_Bridge.thy` and
`Appendix/Robust3/Nonemptiness_Robust3.thy` for an existing nowhere-dense /
closed-cover combinator (`dip_critical_chart_nowhere_dense`,
`meager_negligible_closed_cover`) before building a product-space lemma from
scratch — and use the project's actual triple-configuration type (grep
`HessU`'s signature in the bridge), don't invent a new one.

**Deliverable:** `F_eta`/`real_analytic_on_F_eta`/`F_eta_zeros_nowhere_dense`
(Tier 1, must-have) plus as much of `prop:uphi-reduce`/`prop:uphi-codim3`/
`cor:uphi-exhausted` (Tiers 2–3) as comes together cleanly, landed in your
own `Appendix/AnalyticBridge/D34_UPhi_Branch.thy` + `M5_Dev_UPhi/` dev
session, verified, committed, pushed, with a diary entry stating exactly
which tier you reached and what (if anything) is `sorry`'d.

### Reserved for Claude — precise plan (mirrors the tiering above)

I read all three remaining pieces in the paper source before writing this, the
same way I scoped the u-slice branch vs. `app:H0res` above. Here's the exact
shape of each, my priority order, and why.

**Scope comparison** (paper line ranges in
`nonemptiness_unified_singlefile_complete.tex`):

| Branch | Paper labels + lines | Size | Flavor |
|---|---|---|---|
| `H12=0,H22\neq0`, entry corollary | `prop:H12zero`/`cor:H12zero` (5447–5556) | small — 1 prop + 1 cor | block-triangular rank-3, **same pattern as H11/H22** |
| `H12=0,H22\neq0`, full closure | `cor:Lambda-closed` + `prop:Lambda-simple`/`Lambda-onefold`/`Lambda-high`/`cor:double-impossible`/`prop:double-param` (5755–6202, ~450 lines) | large | monotonicity argument + auxiliary-variable lifting, several sub-lemmas |
| `H12\neq0,H22\neq0`, full closure | `cor:vpair22-full` chain: `cor:vpair22-common`→`prop:vpair22-graph`→`prop:vpair22-elim`(5016)→`prop:vpair22-onezero`(5206)→`prop:vpair22-full`(5307)→`cor:vpair22-full` (4560–5460, ~900 lines) | largest | real-analytic IFT lifting with 3 auxiliary variables `(\delta,\mu,\rho)`, uniqueness via a Vandermonde-shaped 3×3 system, several sub-cases |
| `H \equiv 0` residual | `app:H0res`/`prop:h0res-meager` (3086–3578, ~500 lines, 6 subsections, ~20 environments) | large, and **structurally separate** — its own `(q,r)` coordinate chart, doesn't reuse `HessU`/`Phi_par`/`det3` at all | transversality of hypersurfaces, residue-coordinate reduction |

**My priority order: `cor:H12zero` first, then reassess.**
`prop:H12zero`/`cor:H12zero` is the *entry point* to `cor:Lambda-closed`
(`rem:H12zero`, right after it, explicitly says this corollary reduces the
`H12=0` branch down to two residues — the rest of Lambda-closed *is* those
two residues). It is also, structurally, the exact same block-triangular
rank-3 argument I've now built twice (`cor:vpair11`, `cor:vpair22`) — just
with a different pairing: `\Lambda^{(11)}_{ij} := \det \partial(\Phi_1,H_{11})
/\partial(u_i,u_j)` (u-slot, not v-slot), and `s_k` (a v-slot quantity for
the *third*, excluded index). High confidence, high reuse, same as before.

**⚠ Cross-dependency with Codex's Tier 2 — read before starting either
side.** `cor:H12zero` needs `\Phi_1`'s derivative in the *u-slot* (parallel)
direction — exactly what Codex's u-slice Tier 2 is building
(`Appendix/AnalyticBridge/D34_Analytic_Bridge.thy`'s `Phi_par` differentiated
via `slot j (cvec_dip \<omega>0 \<omega>s \<omega>))` instead of `perp2 (...)`, using
`d_A_moment_x_slot` in place of `d_A_moment_x_perp`). Check the diary before
duplicating this: if Codex has already landed the general u-slot derivative
of `Phi_par`/`gradU`, reuse it directly rather than re-deriving it. What I
need *beyond* that (which is genuinely my own, since it's Hessian- not
gradient-level) is the **general (non-perpendicular) u-slot analogues of the
Hessian-entry block derivatives** — `dV_x`, `dgradcV_x`, `dHcmat_x` currently
only have `_perp` siblings (`dV_x_perp`, `dgradcV_x_perp`, `dHcmat_x_perp`,
`Appendix/AnalyticBridge/D34_Analytic_Bridge.thy:3450-3468`), built from
`Uc_perp_slot_deriv`/`gradUc_comp_perp_slot_deriv`/`Hcmat_entry_perp_slot_deriv`.
Those need general (`_slot`) siblings, mirroring `d_A_moment_x_slot` vs.
`d_A_moment_x_perp` exactly, to get `H_{11}`'s u-slot derivative. If Codex
gets to Tier 2 first and needs to touch any of these Hessian-level names,
that's a signal to post a diary note rather than both of us extending the
same lemma family independently.

**Tier A for `cor:H12zero`** (my first concrete step, once I start this):

1. Build the general (`_slot`, not `_perp`) versions of `dV_x`, `dgradcV_x`,
   `dHcmat_x` — same derivation as `dV_x_perp`/`dgradcV_x_perp`/`dHcmat_x_perp`
   (`D34_Analytic_Bridge.thy:3450-3468`) but from the general
   `d_A_moment_x_slot` (not the perp-specialized `d_A_moment_x_perp`), with
   `v := cvec_dip \<omega>0 \<omega>s \<omega>` for the u-slot case.
2. Reuse `HessU_dip_entry_moments`'s assembly (same as sessions (i)/(i.5)) to
   get `H_{11}`'s u-slot derivative in closed(ish) form — expect this to
   mirror `HessU_dip_entry_perp_slot_value`'s shape closely.
3. Define `Lambda_ij := det ∂(Φ1,H11)/∂(u_i,u_j)` (invariantly: `u_i = slot i
   (cvec_dip \<omega>0 \<omega>s \<omega>)`), analogous to `Delta_ij`.
4. Build the block-triangular `Jac3`-style determinant identity — this part
   should be near-verbatim reuse of `Jac3`/`Jac3_identity`'s proof shape
   (`det3`, cofactor expansion), just with `Phi_par`/`H11`/`s_k`'s v-slot
   value (`Phi2_perp_slot_value`'s pattern, but for the *third* excluded
   index `k` rather than the pair `i,j`) as the three rows.
5. `cor:H12zero`'s nonzero criterion: given `s_k \neq 0` and
   `Lambda_ij \neq 0`, rank 3 — same shape as `Jac3_nonzero_criterion`.

Land this in its own file (`Appendix/AnalyticBridge/D34_H12zero_Branch.thy` +
`M5_Dev_H12zero/`), same discipline as everything else in this project.

**After `cor:H12zero`:** reassess based on what `rem:H12zero` says is left
(the all-sine-zero slice `s_1=s_2=s_3=0`, said to already be closed
elsewhere as codimension-3 — check `nonemptiness_restricted_minors.tex` if
it exists in this checkout — and the `Lambda_ij` all-zero residue, which is
where `Lambda-simple`/`Lambda-onefold`/`Lambda-high`/`double-impossible`
actually come in). I have not scoped those four sub-propositions down to
theorem-level precision yet — they involve a genuinely different technique
(an explicit strictly-monotone auxiliary function `\alpha_\ast(u)`, proved
increasing via a manifestly-positive derivative, `prop:double-param` around
line 5755) — that's real, separate work for a later session, not something
to improvise mid-flight.

**`cor:vpair22-full` and `app:H0res` are lower priority than both of the
above** — larger, more novel (IFT-lifting with auxiliary variables; a wholly
separate coordinate chart, respectively), and neither is blocking anything
else. I'll scope each to this level of precision in its own turn, when I get
to it, rather than commit to an implementation plan now based on a
structural skim.

## 6. Communication

There's no live channel between us. Use `FORMALIZATION_DIARY.md` as the
shared log: prefix a note with `TO CLAUDE:` or `TO CODEX:` if it needs the
other party's attention (a discovered gotcha, a naming decision that affects
shared types, a completed piece ready for someone else to build on). Read the
tail of the diary before starting a session, in case the other party left you
something.
