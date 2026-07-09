# Working in parallel with Claude on this repo

This file is instructions for **Codex/ChatGPT** (or any other agent) working on
this Isabelle formalization *at the same time* as Claude, in the same
checkout. Claude wrote it after finishing the `H11`/`H22` rank-3 branches, to
avoid the two of us burning tokens re-deriving each other's context or
clobbering each other's files. Read this whole file before touching anything.

Read `D34_WITNESS_PLAN.md` and `FORMALIZATION_DIARY.md` next — they are the
living project log (dated entries, most recent at the bottom of each). They
tell you what's actually been proved vs. what's still `proof hole`, which matters
more than anything in this file.

## 1. The project, in one paragraph

We're formalizing a nonemptiness proof (`F0_dip_nonempty`) for a drone/antenna
configuration problem. The overarching strategy is the "analytic route": build
real-analytic machinery to discharge proof holes in
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

## 4. The "proof hole upstream" protocol

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
     proof hole
   ```
2. Keep building on top of it as if it were proved. This lets you verify your
   own downstream reasoning is sound modulo that one gap, without waiting on
   anyone.
3. Keep a running list of every such `proof hole` at the top of your file (a
   `NEEDS:` comment block) so re-integration later is just "replace this
   proof hole with the real theorem name" — assuming the statement shape matches;
   flag it in the diary if you're not sure it will.
4. Symmetrically, Claude will do the same for anything needed from your work
   that isn't ready yet.

This is standard practice in large multi-author Isabelle developments
(quick_and_dirty proof holes as a synchronization primitive) — it's not cheating,
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

**If this doesn't come together cleanly:** use the proof hole-upstream protocol
from §4. State `prop:uphi-reduce`'s conclusion as a `proof hole`'d lemma with a
`NEEDS:` comment explaining exactly what's missing, and still land
`prop:uphi-codim3` + `cor:uphi-exhausted` built on top of it (marking their
own dependence on the proof hole clearly). A Tier 1 + honestly-flagged Tier 2 gap
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
which tier you reached and what (if anything) is `proof hole`'d.

### Reserved for Claude — precise plan (mirrors the tiering above)

I read all three remaining pieces in the paper source before writing this, the
same way I scoped the u-slice branch vs. `app:H0res` above. Here's the exact
shape of each, my priority order, and why.

**Scope comparison** (paper line ranges in
`nonemptiness_unified_singlefile_complete.tex`):

| Branch | Paper labels + lines | Size | Flavor |
|---|---|---|---|
| `H12=0,H22\neq0`, entry corollary | `prop:H12zero`/`cor:H12zero` (5447–5556) | small statement, **but BLOCKED — see below, not a safe reuse** | block-triangular rank-3, looked like H11/H22 at first, turned out not to be |
| `H12=0,H22\neq0`, full closure | `cor:Lambda-closed` + `prop:Lambda-simple`/`Lambda-onefold`/`Lambda-high`/`cor:double-impossible`/`prop:double-param` (5755–6202, ~450 lines) | large | monotonicity argument + auxiliary-variable lifting, several sub-lemmas |
| `H12\neq0,H22\neq0`, full closure | `cor:vpair22-full` chain: `cor:vpair22-common`→`prop:vpair22-graph`→`prop:vpair22-elim`(5016)→`prop:vpair22-onezero`(5206)→`prop:vpair22-full`(5307)→`cor:vpair22-full` (4560–5460, ~900 lines) | largest | real-analytic IFT lifting with 3 auxiliary variables `(\delta,\mu,\rho)`, uniqueness via a Vandermonde-shaped 3×3 system, several sub-cases |
| `H \equiv 0` residual | `app:H0res`/`prop:h0res-meager` (3086–3578, ~500 lines, 6 subsections, ~20 environments) | large, and **structurally separate** — its own `(q,r)` coordinate chart, doesn't reuse `HessU`/`Phi_par`/`det3` at all | transversality of hypersurfaces, residue-coordinate reduction |

**Correction (2026-07-08, after actually tracing the math): `cor:H12zero` is
NOT a safe high-confidence reuse — I was wrong to say so.** I started
building it and found a genuine obstacle before writing any Isabelle. Full
details are in the diary entry "cor:H12zero investigation: a genuine
obstacle, not a quick brick" — summary here since it changes the plan:

`prop:H12zero`'s determinant needs `H_{11}` independent of every v-slot,
mirroring the `\Phi_1` independence claim from `cor:vpair11` — which does
NOT hold automatically in our angular omega coordinates (that's exactly what
`Phi_par`/`e_par` fixed, for the *first*-derivative case). I tried the same
fix for `H_{11}` (contract both Hessian indices with `e_par` instead of
`axis(1,1)`, call it `H_par`). Tracing `HessU_dip_entry_perp_slot_value`'s
already-proven general formula, most terms *do* collapse the same clean way
— but there's an extra term from `D2cvec_dip(e_par)(e_par) \<bullet> v`
(the *second*-derivative analogue) that does not obviously vanish.
Reasoning about `cvec_dip`'s structure (a fixed linear projection, with a
constant beam-steering shift, of a point moving on the unit sphere) via the
classical Gauss equation for a sphere's embedding Hessian suggests this
residual is genuinely nonzero in general, not just an unsimplified
artifact — though I have NOT formally verified this in Isabelle either way,
and want to flag that distinction honestly: this is a differential-geometry
plausibility argument, not a checked proof of non-vanishing.

**Update (2026-07-08, cont. 2): SETTLED — the `H_par` approach is a dead
end, not an open question.** Did the full computation: isolated the
residual to `H_par`'s v-slot value `= 2*gain_dip(ω)*Im(cnj(A)*φ_m)*Q` where
`Q := D2cvec_dip(ω)[e_par,e_par] · perp2(c)` (an ω-only quantity). Built an
explicit witness (`ω0=(π/4,0)`, `ωs=(3π/4,0)`, `ω=(π/3,π/6)`, chosen so
`Dx=Dy=0`), solved `Dc(e_par)=c` exactly to get `e_par=(√3−√6/2, √6/6)`, and
got the closed form `Q = 23√6/24 − 5√3/4`. Machine-verified (not hand
arithmetic) via `HOL-Decision_Procs.Approximation`'s `approximation` method:
`0.18 < Q < 0.19`, definitively nonzero. Since `Q` is a real-analytic
function of `(ω0,ωs,ω)` nonzero at a generic point, by the same
identity-theorem logic this project already uses elsewhere
(`real_analytic_1d_nowhere_dense_zeros`), its zero set is nowhere dense —
`h_par_vslot_zero` fails **generically**, not just at this witness. Full
derivation in the diary entry "h_par_vslot_zero: DEFINITIVELY RESOLVED
FALSE, not just unresolved."

**Do not pursue `H_par` (contract-both-indices-with-`e_par`) for
`cor:H12zero` — it cannot work, not even after more effort.** The
`Jac3_H12zero_identity`/`Jac3_H12zero_nonzero_criterion` theorems already in
the bridge remain logically valid (true implications) but are practically
inapplicable and should not be built on further. A real fix needs a
genuinely different construction — most plausibly geodesic/Riemannian-
normal-coordinate reparametrization on the sphere at each point (so the
ambient Hessian's tangential/Christoffel part vanishes too, not just the
first-order direction) — which is substantial new differential-geometry
infrastructure this project doesn't have, not a quick brick. Treat
`cor:Lambda-closed` (which depends on `cor:H12zero`) as **on hold** pending
that infrastructure, or someone finding a different invariant
characterization entirely.

**After `cor:H12zero` is actually resolved:** reassess based on what `rem:H12zero` says is left
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

**Update (2026-07-08, cont. 3): `app:H0res` — started, one piece landed, one
important finding.** Before writing anything: a fully-proven (zero `proof hole`)
H0res scaffold already exists in
`Appendix/Nonemptiness_Regnonzero_Appendix.thy` (`lem_h0res_Bcuts`,
`prop_h0res_meager`, etc.) — but it's disconnected from the actual proof
chain (not imported by `Nonemptiness_Robust3.thy`, same situation as the
earlier `m5_D34_subset_mstarg_residual` enlargement), its lemmas are generic
over an abstract `cert :: 'w ⇒ real` never instantiated with a concrete D34
object, and its `prop_h0res_meager` *takes* the meager conclusion as a
hypothesis rather than deriving it (the file's own comment flags the
codim-1-to-meager-projection gap as unclosed). So don't treat that file as
"H0res is basically done" — it isn't wired in and has a real gap of its own.

Landed instead, connected to the actual D34 configuration type:
`beta_h0`/`B_dip`/`B_dip_uslot_transversal` in
`Appendix/AnalyticBridge/D34_H0res_Branch.thy` (registered in `ROOT`
alongside `D34_UPhi_Branch`, same pattern) — `lem:h0res-Bcuts`'s
transversality conclusion for one cut (one triple element `j`), genuinely
verified (`BUILD_EXIT=0`, independently re-checked). **Remaining**: lifting
this one-cut result to the joint three-cut (`j=1,2,3`) codimension-≥3
argument needed for `prop:h0res-Bbranch`'s actual meager-projection
conclusion — not attempted, needs a `det3`/`Jac3`-style but three-fold rank
argument. The other four `app:H0res` pieces (residue-control for `(a1,a2)`,
the `S=0` branch, two/three-vanishing-cosine branches) are read and scoped
but untouched.

**`cor:vpair22-full` is lower priority, in progress** — larger, more novel
(IFT-lifting with auxiliary variables `δ,μ,ρ`), not blocking anything else.
Early scaffolding (`Ttau`,`Vtau`,`Dtau`,`AT3`,`Lcof`,`Mcof`,`Kcof` and a few
`_eq` lemmas) exists in `M5_Dev_VPair22Full/` as of this writing but hasn't
reached a landed/spliced state yet — check the diary for current status
before assuming this is further along than it is.

## 6. Communication

There's no live channel between us. Use `FORMALIZATION_DIARY.md` as the
shared log: prefix a note with `TO CLAUDE:` or `TO CODEX:` if it needs the
other party's attention (a discovered gotcha, a naming decision that affects
shared types, a completed piece ready for someone else to build on). Read the
tail of the diary before starting a session, in case the other party left you
something.
