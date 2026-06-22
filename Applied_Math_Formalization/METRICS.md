# Formalization Metrics — Odd-N / Dipole Nonemptiness

A living record of the development metrics for this Isabelle/HOL formalization,
designed to mirror the "Project statistics" reported in the reference paper

> V. Ilin, *Semi-Autonomous Formalization of the Vlasov-Maxwell-Landau
> Equilibrium*, arXiv:2603.15929v2 (Tables 1–3).

so that when the formalization is complete we can report a directly comparable
set of numbers.

**Scope.** These metrics cover **only the Isabelle nonemptiness formalization**
(the `.thy` development). The separate Quantum-Computing / Vern-Paulsen
`QC_Notes*.tex` LaTeX reconstruction is **deliberately excluded** — the code
collector counts only `.thy` files, and the transcript collector classifies and
drops any LaTeX-dominant session.

**Status: IN PROGRESS** (sorry's remain). The numbers below are an "as-of"
snapshot and will keep growing until the last on-path `sorry` is closed.

**Milestone 2026-06-22 — M5 assembled, `F0_dip_nonempty` build-checked.**
`meager_rank_deficient_stratum` (M5), formerly the lone bare on-path `sorry`, is now the
proven four-stratum `meager_Un` of D1∪D2∪D5∪D34, and `F0_dip_nonempty` builds for the
first time on a CI leaf (`Applied_Math_Appendix_Full`, `BUILD_EXIT=0`, commit `81b65e1`).
The on-path obligation is decomposed from one black-box stratum into **two precise IFT
chart-branch cores** — `m5_D34_D3_collinear`, `m5_D34_D4_branchP` — with D1/D2/D5/D34 and
the C¹ arc-cover all proven. (On-path count 1→2 is *decomposition, not regression*: the
single sorry stood for all of M5; the two are its irreducible analytic cores.)

---

## 1. Project statistics — snapshot (as of 2026-06-12)

Mirror of the paper's Table 3. Code/git rows are recomputable any time with
`metrics/code_metrics.sh`; session rows with `metrics/transcript_metrics.py`.

| Metric | Value | Status |
|---|---:|---|
| **Theory (.thy) files** | 45 | grows |
| **Lines of code (total / non-blank)** | 33,585 / 30,307 | grows |
| **Theorems** | 34 | grows |
| **Lemmas** | 1,131 | grows |
| **Corollaries / Propositions** | 53 | grows |
| **Definitions** | 179 | grows |
| **sorry's remaining (total, incl. scratch files)** | 13 | → 0 at completion |
| &nbsp;&nbsp;of which on the `F0_dip_nonempty` path (build-checked 2026-06-22) | 2 (D3/D4 IFT chart cores) | → 0 at completion |
| &nbsp;&nbsp;of which Capstone assembly leaves (superseded scaffold) | 6 | retirement decision |
| **Git commits touching .thy** (monorepo mirror) | 188 | grows |
| **Development span** (mirror: 05-25→06-04) | 11 days | grows |
| **Development span** (incl. pre-mirror sessions) | 2026-05-05 → 06-05 | grows |
| **Author (human)** | 1 (Dustin Bryant) | — |
| — | — | — |
| **AI sessions** (formalization transcripts) | 13 | grows |
| **Human prompts** (paper defn; excl. slash + system) | 938 | grows |
| &nbsp;&nbsp;excluded as slash commands / system-noise | 14 / 405 | — |
| **Assistant turns** | 24,045 | grows |
| **Tool calls** | 12,753 | grows |
| **Tokens — input-side total** | 11.04 B | grows |
| &nbsp;&nbsp;cache read / cache creation / fresh | 10.91 B / 129.0 M / 1.8 M | grows |
| **Tokens — output** | 56.4 M | grows |
| **Input : output ratio** | 196 : 1 | — |
| **API-equivalent cost** (Opus rates, w/ caching) | ≈ \$23,000 | grows |
| — | — | — |
| **Active supervision hours** | _TODO — human estimate_ | ❗ capture |
| **Actual subscription cost paid** | _TODO — human_ | ❗ capture |
| Top tools | Bash 7,614 · Edit 2,304 · Read 1,958 · ScheduleWakeup 258 · Monitor 139 | — |

Cost basis (for comparability with the paper): \$1.50/M cache-read,
\$18.75/M cache-creation, \$75/M output, \$15/M fresh input. This is the
*API-equivalent* of the token traffic, **not** the subscription price actually
paid (which the human must report separately, as the paper does: they paid \$200
on a Max subscription against a ≈\$6,300 API-equivalent).

---

## 2. Provenance & reconstructability

The central question — *can past metrics be recovered, or must we start logging
now?* — resolves as follows. **Almost everything is reconstructable**; only two
human-judgement numbers must be captured live.

| Metric group | Source | Retroactive? |
|---|---|---|
| Files, LOC, thms, lemmas, defs, sorry's | current `.thy` tree (`code_metrics.sh`) | ✅ full + time-series via git |
| Commits, dev span, per-day line churn | `git log -- '*.thy'` | ✅ full |
| Milestone timeline (§4) | `FORMALIZATION_DIARY.md` (52 dated entries) + git | ✅ full |
| Sessions, human prompts, assistant turns, tool calls | `~/.claude/projects/*/*.jsonl` transcripts | ✅ — 125 MB on disk |
| Tokens (input/cache/output), I:O ratio, API-equiv cost | transcript `usage` fields | ✅ |
| **Active supervision hours** | human only | ❌ start estimating per session |
| **Subscription \$ actually paid** | human only | ❌ record the plan/price |
| External-prover (their "Aristotle") analog | n/a — we have none; `sledgehammer` ≈ | N/A |

**Bottom line:** the diary alone gives the milestone timeline and the qualitative
narrative; but combined with git and the on-disk Claude Code transcripts, the
full quantitative Table-3 set is recoverable from the past. The only things that
were *not* logged and cannot be reconstructed are the human's **active
supervision hours** and the **price actually paid** — start recording those now.

---

## 3. Comparison-table row (mirror of Table 1)

| Project | Prover | LOC | New thm | New defs | Team | AI role | Logs | Domain |
|---|---|---:|:--:|:--:|:--:|---|:--:|---|
| **This work** | Isabelle/HOL | 25K | ✓ | ✓ | 1 | all code | ✓ | Applied math / antenna-array feasibility |

(Logs ✓ = public diary + git history + archived session transcripts.)

---

## 4. Milestone timeline (mirror of Table 2)

Seeded from the diary; `sorry`-on-path counts are approximate at each date.
The "Sorry (on-path)" column tracks the leaves of `F0_dip_nonempty`.

| Date | Event | Sorry (on-path) |
|---|---|---:|
| 2026-05-05 | Earliest recorded AI session activity (pre-mirror) | – |
| 2026-05-25 | First `.thy` committed into the monorepo mirror | – |
| 2026-05-27 | Regular-value branch `charts_core_Nn`: sorry → QED | – |
| 2026-05-29 | DECISION: commit to unconditional `thm:final`; `smooth-chart-meager` proved; Jacobian id `D_xM(x0,c0)=bigJ` | – |
| 2026-05-30 | `Regnonzero` appendix **complete, sorry-free**; `F` redefined & compact | – |
| 2026-05-31 | σ-compact discharge resolved; dipole gain `|e|²` proved C∞; `F0_nonempty` assembled sorry-free | – |
| 2026-06-01 | Explicit feasibility witness proved sorry-free; Weierstrass continuity inputs | – |
| 2026-06-02 | Baire/meager **glue fully machine-verified**; `Phi_bad_meager` reduction to engine critical-projection | ~14 |
| 2026-06-03 | `F0_dip_nonempty` reduced to only hypothesis `c6`; A3 determinant payoff; definitive 13-leaf list; leaf #7 proved | 13 → 11 |
| 2026-06-04 | A4, A5, `open_surj_blinfun` closed; leaf [E] steering-transport opened (bricks 1–3) | 10 |
| 2026-06-22 | **M5 assembled** from D1∪D2∪D5∪D34 (proven `meager_Un`); `F0_dip_nonempty` **build-checked** for the first time (leaf `Applied_Math_Appendix_Full`, commit `81b65e1`); the single M5 black-box `sorry` → 2 precise D3/D4 IFT chart-core sorries | 1 → 2 |
| _target_ | last on-path `sorry` closed → `F0_dip_nonempty` unconditional | 0 |

---

## 5. How to regenerate

```bash
# Code + git metrics (Isabelle .thy only; QC LaTeX excluded by construction)
bash metrics/code_metrics.sh

# AI-session metrics (auto-classifies, keeps formalization sessions only)
python3 metrics/transcript_metrics.py          # defaults to all Vern-Paulsen dirs
python3 metrics/transcript_metrics.py DIR ...   # or specify transcript dirs
```

Re-run at completion and paste the final snapshot into §1.

---

## 6. Caveats

- **Human-prompt count matches the paper's definition.** `classify_user()` in
  `transcript_metrics.py` counts genuine human-typed turns and excludes bare
  slash commands (e.g. `/compact`) and all harness/system content (interrupt
  notices, compaction summaries, local-command output, system-reminder-only
  turns). Short confirmations ("continue", "go on") are intentionally kept, as
  the paper does ("most were short directives or confirmations"). The excluded
  tallies are reported alongside the count for transparency. Spot-checked
  against a manual category breakdown (genuine 937 ± 1).
- **Git history is the monorepo mirror.** It begins 2026-05-25, but session
  transcripts show activity from 2026-05-05 — the development predates the mirror
  (the diary refers to an upstream `antenna-nonemptiness` repo). For a true
  commit count, use that upstream repo's log.
- **Tokens reflect this machine's transcripts.** If development also ran on a
  second machine (as the reference project did), point the collector at those
  transcript dirs too and the aggregate will include them.
- **`sorry` total (26) vs on-path (10).** The 26 includes the abstract
  `Capstone` twin and the `Inventory` skeleton, which are off the
  `F0_dip_nonempty` critical path. Report both, clearly labelled.
