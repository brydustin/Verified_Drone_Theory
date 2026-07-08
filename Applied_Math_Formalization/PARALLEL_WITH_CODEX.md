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

Four sub-branches remain for the paper's `cor:caseBmeager` (Case B is meager
on the `H \not\equiv 0` side), covering the two possible "good triples" per
point:

| Branch | Paper labels | Status | Flavor |
|---|---|---|---|
| `H11 \neq 0` | `prop:vpair11`/`cor:vpair11` | **DONE** (Claude, commit `b2e0601`) | Fréchet-derivative rank-3 argument |
| `H12\neq0,H22\neq0` | `prop:vpair22`/`cor:vpair22` (bare) | **DONE** (Claude, commit `bd45b71`); `cor:vpair22-full`'s auxiliary-variable lifting NOT done | same, plus a lifting argument |
| **u-slice vanishing** | `prop:uphi-reduce`/`prop:uphi-codim3`/`cor:uphi-exhausted` | **not started — recommended for Codex** | real-analytic isolated-zeros |
| `H12=0,H22\neq0` | `cor:Lambda-closed` (+ 4 sub-props: `Lambda-simple`, `Lambda-onefold`, `Lambda-high`, `double-impossible`) | not started | mixed, large |
| `H \equiv 0` residual | `app:H0res`/`prop:h0res-meager` | not started | separate appendix entirely |

### Recommended for Codex: the u-slice branch (`cor:uphi-exhausted`)

**Why this one:** it's the smallest self-contained piece (one definition, two
propositions, one corollary — paper lines 3826–4000 of
`nonemptiness_unified_singlefile_complete.tex`), it is mathematically
*distinct* from the rank-3/Jacobian work above (real-analytic zero-counting,
not differentiation), so there's essentially zero file/lemma overlap with
what Claude has been building — and **the hard analytic machinery already
exists in this repo**, so this is mostly an assembly job, not new research.

**The math (read the paper section first — section right after
`cor:vpair11`'s corollary, titled "The vanishing u-slice branch"):**

- Definitions (paper, ~line 3826): `\eta := g_1/(2g)`,
  `F_\eta(u) := \cos(\kappa u) - \kappa(u-\eta)\sin(\kappa u)`, where `\kappa`
  is the (already-defined-elsewhere) constant `|c|>0`.
- `prop:uphi-reduce`: on gauge `b=0`, `D\Phi_1|_{E_u}=0` (the "u-slice
  differential of Φ1 vanishes", where `E_u := span{∂_{u_1},∂_{u_2},∂_{u_3}}`)
  is *equivalent* to `F_\eta(u_j)=0` for `j=1,2,3`.
- `prop:uphi-codim3`: `F_\eta` is real-analytic and not identically zero
  (witness: `F_\eta(0) = \cos(0) - \kappa(0-\eta)\sin(0) = 1 \neq 0` — the
  paper uses a fancier witness `F_\eta(m\pi/\kappa)=(-1)^m` for all integers
  `m`, but you only need one nonzero value, and `u=0` is the simplest).
  Hence `F_\eta`'s zero set is discrete, so the branch
  `{D\Phi_1|_{E_u}=0}` is locally a finite union of codimension-3 coordinate
  slices `u_1=\xi_1, u_2=\xi_2, u_3=\xi_3`.
- `cor:uphi-exhausted`: hence the branch is locally nowhere dense.

**What already exists in this repo that you should use, not reprove**
(all in `Analytic/Real_Analytic.thy` unless noted):
- `real_analytic_on_sin` / `real_analytic_on_cos` — proved in
  `Analytic/Complex/Real_Analytic_Complex.thy:544,548` via a
  complex-holomorphic-extension bridge. Also `real_analytic_on_sin_comp` /
  `real_analytic_on_cos_comp` (composed forms: given
  `real_analytic_on f U`, get `real_analytic_on (\<lambda>x. sin (f x)) U`,
  and likewise for `cos`) — these are exactly the shape you need for
  `sin(\<kappa>u)`/`cos(\<kappa>u)`.
- `real_analytic_on_const`, `real_analytic_on_add`, `real_analytic_on_diff`,
  `real_analytic_on_mult`, `real_analytic_on_scaleR`,
  `real_analytic_on_compose` — the composition algebra you'll chain together
  to get `F_\eta`'s analyticity from its constituent pieces.
- **The key workhorse, already proved** —
  `theorem real_analytic_1d_nowhere_dense_zeros` (`Analytic/Real_Analytic.thy`,
  subsection "(1.6) Workhorse: a non-vanishing analytic function has
  nowhere-dense zeros"):
  ```isabelle
  theorem real_analytic_1d_nowhere_dense_zeros:
    fixes f :: "real \<Rightarrow> real"
    assumes ana: "real_analytic_on f U" and conn: "connected U"
      and ex: "\<exists>x\<in>U. f x \<noteq> 0"
    shows "interior (closure {x \<in> U. f x = 0}) = {}"
  ```
  This is *exactly* `prop:uphi-codim3`'s core analytic step. Apply it with
  `U := UNIV`, and the witness from `F_\eta(0) = 1`.

**What you'll likely have to build yourself** (not found in the repo as of
this writing — search first, in case Claude or a prior session added it):
- Lifting the single-variable "F_η's zero set is nowhere dense in ℝ" fact to
  the 3-coordinate statement: the set
  `{(u_1,u_2,u_3,v_1,v_2,v_3) : F_\eta(u_1)=0 \wedge F_\eta(u_2)=0 \wedge
  F_\eta(u_3)=0}` is nowhere dense in `\<real>^6` (or whatever the project's
  actual triple-coordinate type is — check `Nonemptiness_Robust3.thy` / the
  `HessU`/triple-configuration types used elsewhere in the bridge for the
  right ambient type, don't invent a new one). This is a general
  product-space fact (a proper subset depending on only one of several
  independent coordinates, when that subset is nowhere dense in its own
  factor, gives a nowhere-dense set in the product) — check
  `Appendix/AnalyticBridge/D34_Analytic_Bridge.thy` and
  `Appendix/Robust3/Nonemptiness_Robust3.thy` for existing nowhere-dense /
  closed-cover lemmas (e.g. `dip_critical_chart_nowhere_dense`,
  `meager_negligible_closed_cover`) before building this from scratch — there
  may already be a reusable combinator.
- Connecting this to the actual `D\Phi_1|_{E_u}` object as it's represented
  in the bridge (i.e. via `slot`/Fréchet-derivative machinery, matching the
  invariant style Claude has used throughout — grep the bridge for
  `Phi_par`, `slot`, `frechet_derivative` to see the house style before
  introducing a different representation).

**Deliverable:** theorems corresponding to `prop:uphi-reduce`,
`prop:uphi-codim3`, and `cor:uphi-exhausted`, landed in your own
`Appendix/AnalyticBridge/D34_UPhi_Branch.thy` + `M5_Dev_UPhi/` dev session,
verified, committed, pushed, with a diary entry.

### Reserved for Claude — please don't start these without checking first

- `cor:vpair22-full`'s auxiliary-variable lifting (extends the `H22` branch).
- `cor:Lambda-closed` and its four sub-propositions.
- `app:H0res`/`prop:h0res-meager` (the separate appendix for `H \equiv 0`).

If you finish the u-slice branch and want more work, leave a note in the
diary (`TO CLAUDE: u-slice branch done, what's next?`) rather than picking
one of these unilaterally — they're bigger, and coordinating first avoids
two agents duplicating a multi-day effort.

## 6. Communication

There's no live channel between us. Use `FORMALIZATION_DIARY.md` as the
shared log: prefix a note with `TO CLAUDE:` or `TO CODEX:` if it needs the
other party's attention (a discovered gotcha, a naming decision that affects
shared types, a completed piece ready for someone else to build on). Read the
tail of the diary before starting a session, in case the other party left you
something.
