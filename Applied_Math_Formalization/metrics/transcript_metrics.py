#!/usr/bin/env python3
"""Reconstruct AI-session metrics (prompts, turns, tool calls, tokens, cost)
from Claude Code .jsonl transcripts.

Mirrors the "Project statistics" reported in the reference paper
(Ilin, "Semi-Autonomous Formalization of the Vlasov-Maxwell-Landau Equilibrium",
arXiv:2603.15929v2): sessions, human prompts, assistant turns, tool calls,
token consumption, input:output ratio, and an API-equivalent cost estimate.

Usage:
    python3 transcript_metrics.py DIR [DIR ...]

Each DIR is a Claude Code project transcript directory under ~/.claude/projects.
Reports per-directory and aggregate. Pure stdlib; streams line-by-line.
"""
import sys, os, json, glob, collections, datetime, re

# API-equivalent pricing ($ per 1e6 tokens). These match the reference paper's
# Opus rates so the cost figure is directly comparable; the actual subscription
# cost paid is a separate, human-supplied number.
PRICE = {
    "fresh_input":    15.00,
    "cache_creation": 18.75,
    "cache_read":      1.50,
    "output":         75.00,
}

# Markers of harness-injected user turns that are NOT human prompts.
_SLASH_RE = re.compile(r'^/[A-Za-z][\w-]*$')          # bare slash command, e.g. /compact
_SYSREM_RE = re.compile(r'<system-reminder>.*?</system-reminder>', re.DOTALL)
_NONPROMPT_PREFIXES = (
    "<command-name>", "<command-message>", "<command-args>",
    "<local-command-stdout>", "<local-command-stderr>",
    "<bash-input>", "<bash-stdout>", "<bash-stderr>",
    "Caveat:", "[Request interrupted",
)

def classify_user(rec):
    """Classify a user record. Returns one of:
      'human'      - a genuine human-typed prompt (paper's definition)
      'slash'      - a bare slash command (e.g. /compact) -> excluded per paper
      'tool_result'- a tool result carrier (not a prompt)
      'noise'      - interrupt notice, compaction summary, local-cmd output,
                     system-reminder-only, or other harness injection
    Mirrors arXiv:2603.15929v2: human prompts exclude bare slash commands and
    all system/harness content."""
    if rec.get("type") != "user" or rec.get("isSidechain") or rec.get("isMeta") \
       or rec.get("isCompactSummary"):
        return "noise"
    msg = rec.get("message") or {}
    c = msg.get("content")
    if isinstance(c, str):
        txt = c
    elif isinstance(c, list):
        kinds = {b.get("type") for b in c if isinstance(b, dict)}
        if "tool_result" in kinds:
            return "tool_result"
        if "text" not in kinds:
            return "noise"
        txt = "\n".join(b.get("text", "") for b in c
                        if isinstance(b, dict) and b.get("type") == "text")
    else:
        return "noise"
    # strip injected system-reminder blocks before judging the human content
    core = _SYSREM_RE.sub("", txt).strip()
    if not core:
        return "noise"
    if core.startswith(_NONPROMPT_PREFIXES):
        # slash commands are recorded as <command-name>/foo</command-name>
        return "slash" if core.startswith(("<command-name>", "<command-message>")) else "noise"
    if "This session is being continued from a previous conversation" in core[:200]:
        return "noise"
    first = core.split(None, 1)[0]
    if _SLASH_RE.match(first):                          # bare /command, not a pasted path
        return "slash"
    return "human"

def parse_ts(s):
    try:
        return datetime.datetime.fromisoformat(s.replace("Z", "+00:00"))
    except Exception:
        return None

def classify(rawtext):
    """Heuristic: is this transcript formalization (.thy/Isabelle) or LaTeX work?"""
    thy = rawtext.count(".thy") + rawtext.count("isabelle") + rawtext.count("Nonemptiness")
    tex = rawtext.count("QC_Notes") + rawtext.count("pdflatex")
    return thy, tex

def scan_file(f, formalization_only=False, min_lines=50):
    """Returns (metrics, tools, timestamps, included:bool, reason:str)."""
    m = collections.Counter(); tools = collections.Counter(); timestamps = []
    with open(f, errors="replace") as fh:
        raw = fh.read()
    nlines = raw.count("\n")
    thy, tex = classify(raw)
    if nlines < min_lines:
        return m, tools, timestamps, False, "empty/stub session"
    if formalization_only and tex > thy:
        return m, tools, timestamps, False, "LaTeX session"
    for line in raw.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            o = json.loads(line)
        except Exception:
            continue
        ts = parse_ts(o.get("timestamp", "")) if o.get("timestamp") else None
        if ts:
            timestamps.append(ts)
        typ = o.get("type")
        if typ == "assistant":
            m["assistant_turns"] += 1
            if o.get("isSidechain"):
                m["assistant_turns_sidechain"] += 1
            msg = o.get("message") or {}
            for b in (msg.get("content") or []):
                if isinstance(b, dict) and b.get("type") == "tool_use":
                    m["tool_calls"] += 1
                    tools[b.get("name", "?")] += 1
            u = msg.get("usage") or {}
            m["fresh_input"]    += u.get("input_tokens", 0) or 0
            m["cache_creation"] += u.get("cache_creation_input_tokens", 0) or 0
            m["cache_read"]     += u.get("cache_read_input_tokens", 0) or 0
            m["output"]         += u.get("output_tokens", 0) or 0
        elif typ == "user":
            m["user_records"] += 1
            kind = classify_user(o)
            if kind == "human":
                m["human_prompts"] += 1
            elif kind == "slash":
                m["excluded_slash"] += 1
            elif kind == "noise":
                m["excluded_noise"] += 1
    m["sessions"] = 1
    return m, tools, timestamps, True, "ok"

def scan_dir(d, formalization_only=False):
    m = collections.Counter(); tools = collections.Counter(); timestamps = []
    files = sorted(glob.glob(os.path.join(d, "*.jsonl")))
    for f in files:
        fm, ft, fts, inc, why = scan_file(f, formalization_only)
        if inc:
            m.update(fm); tools.update(ft); timestamps += fts
        else:
            m["excluded_sessions"] += 1
    return m, tools, timestamps

def fmt_tokens(n):
    if n >= 1e9: return f"{n/1e9:.2f}B"
    if n >= 1e6: return f"{n/1e6:.1f}M"
    if n >= 1e3: return f"{n/1e3:.1f}K"
    return str(n)

def cost(m):
    return (m["fresh_input"]/1e6*PRICE["fresh_input"]
          + m["cache_creation"]/1e6*PRICE["cache_creation"]
          + m["cache_read"]/1e6*PRICE["cache_read"]
          + m["output"]/1e6*PRICE["output"])

def report(label, m, tools, ts):
    total_in = m["fresh_input"] + m["cache_creation"] + m["cache_read"]
    ratio = total_in / m["output"] if m["output"] else 0
    print(f"\n===== {label} =====")
    print(f"  Sessions (transcript files) : {m['sessions']}")
    print(f"  Human prompts (paper defn)  : {m['human_prompts']}  "
          f"(excluded: {m['excluded_slash']} slash, {m['excluded_noise']} system/noise)")
    print(f"  Assistant turns             : {m['assistant_turns']}  "
          f"(sidechain/sub-agent: {m['assistant_turns_sidechain']})")
    print(f"  Tool calls                  : {m['tool_calls']}")
    print(f"  Tokens — fresh input        : {fmt_tokens(m['fresh_input'])}")
    print(f"  Tokens — cache creation     : {fmt_tokens(m['cache_creation'])}")
    print(f"  Tokens — cache read         : {fmt_tokens(m['cache_read'])}")
    print(f"  Tokens — TOTAL input-side   : {fmt_tokens(total_in)}")
    print(f"  Tokens — output             : {fmt_tokens(m['output'])}")
    print(f"  Input:output ratio          : {ratio:.0f}:1")
    print(f"  API-equiv cost (Opus rates) : ${cost(m):,.0f}")
    if ts:
        print(f"  Activity span               : {min(ts).date()} -> {max(ts).date()}")
    if tools:
        top = ", ".join(f"{k}:{v}" for k, v in tools.most_common(8))
        print(f"  Top tools                   : {top}")

def main(dirs, formalization_only=False):
    agg = collections.Counter(); aggtools = collections.Counter(); aggts = []
    for d in dirs:
        if not os.path.isdir(d):
            print(f"  (skip, not a dir) {d}", file=sys.stderr); continue
        m, tools, ts = scan_dir(d, formalization_only)
        report(os.path.basename(d.rstrip('/')) or d, m, tools, ts)
        agg.update(m); aggtools.update(tools); aggts += ts
    if len(dirs) > 1:
        report("AGGREGATE", agg, aggtools, aggts)
        print(f"  (excluded {agg['excluded_sessions']} empty/LaTeX sessions)")

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a != "--formalization-only"]
    fo = "--formalization-only" in sys.argv
    if not args:
        # default: all Vern-Paulsen project dirs, formalization sessions only
        args = glob.glob(os.path.expanduser("~/.claude/projects/*Isabelle-Vern-Paulsen-QC*"))
        fo = True
    main(args, fo)
