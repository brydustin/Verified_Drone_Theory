#!/bin/bash
# Build one session of this tree with Isabelle2026, with a hard time limit.
# usage: tools/build_session.sh SESSION [SECONDS] [LOGFILE]
# On timeout the whole process tree of this build is killed (the prover runs in
# its own process session, so a plain `timeout` would leave it behind).
cd "$(dirname "$0")/.." || exit 2
S="${1:?session}"; T="${2:-240}"; L="${3:-/tmp/isabelle_${S}.log}"
~/Desktop/Isabelle/Isabelle2026/bin/isabelle build -b -v -d . "$S" > "$L" 2>&1 &
PID=$!
tree() { local p; for p in $(pgrep -P "$1"); do tree "$p"; done; echo "$1"; }
SECS=0
while kill -0 $PID 2>/dev/null; do
  sleep 2; SECS=$((SECS+2))
  if [ $SECS -ge "$T" ]; then
    echo "TIMEOUT after ${T}s" >> "$L"
    kill -TERM $(tree $PID) 2>/dev/null; sleep 1; kill -KILL $(tree $PID) 2>/dev/null
    break
  fi
done
wait $PID 2>/dev/null; RC=$?
echo "EXIT=$RC"
grep -E "^Finished|TIMEOUT" "$L" | cut -c1-120
grep -n "^\*\*\*" "$L" | cut -c1-230 | head -${4:-60}
grep "running for" "$L" | tail -3 | cut -c1-200
