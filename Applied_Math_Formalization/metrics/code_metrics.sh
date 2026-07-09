#!/usr/bin/env bash
# Code- and git-derivable metrics for the Isabelle nonemptiness formalization,
# mirroring the "Project statistics" table of arXiv:2603.15929v2.
# Scoped to Isabelle .thy files only -> the Quantum-Computing LaTeX work
# (QC_Notes*.tex) is excluded by construction.
#
# Run from the formalization root (the dir containing the .thy tree).
set -u
cd "$(dirname "$0")/.."

# --- own theory files (exclude vendored AFP/Isabelle heaps) -----------------
mapfile -t THYS < <(find . -name "*.thy" -not -path "*/Isabelle*" \
    -not -path "*/Jordan_Normal_Form/*" -not -path "*/Munkres*/*" \
    -not -path "*/Perron_Frobenius/*" -not -path "*/Matrix/*" | sort)

count() { grep -hcE "$1" "${THYS[@]}" 2>/dev/null | paste -sd+ | bc; }

FILES=${#THYS[@]}
LOC=$(cat "${THYS[@]}" | wc -l | tr -d ' ')
LOC_NB=$(grep -hvE '^\s*$' "${THYS[@]}" | wc -l | tr -d ' ')
THMS=$(count '^[[:space:]]*theorem\b')
LEMS=$(count '^[[:space:]]*lemma\b')
CORS=$(count '^[[:space:]]*(corollary|proposition)\b')
DEFS=$(count '^[[:space:]]*(definition|abbreviation|fun|primrec)\b')
proof hole=$(count '^[[:space:]]*proof hole[[:space:]]*$')

echo "############  CODE METRICS (Isabelle .thy, QC/LaTeX excluded)  ############"
printf "%-34s %s\n" "Theory (.thy) files"      "$FILES"
printf "%-34s %s\n" "Lines of code (total)"    "$LOC"
printf "%-34s %s\n" "Lines of code (non-blank)" "$LOC_NB"
printf "%-34s %s\n" "Theorems"                 "$THMS"
printf "%-34s %s\n" "Lemmas"                   "$LEMS"
printf "%-34s %s\n" "Corollaries/Propositions" "$CORS"
printf "%-34s %s\n" "Definitions"              "$DEFS"
printf "%-34s %s\n" "proof holes (remaining)"      "$proof hole"

echo
echo "############  GIT METRICS (commits touching .thy files)  ############"
# Formalization commits = commits that touch at least one .thy file anywhere
# in the repo (captures the development across directory relocations);
# QC_Notes*.tex-only commits are NOT counted here.
COMMITS=$(git log --oneline -- '*.thy' | wc -l | tr -d ' ')
FIRST=$(git log --reverse --date=short --pretty='%ad' -- '*.thy' | head -1)
LAST=$(git log -1 --date=short --pretty='%ad' -- '*.thy')
DAYS=$(( ( $(date -d "$LAST" +%s) - $(date -d "$FIRST" +%s) ) / 86400 + 1 ))
AUTHORS=$(git log --pretty='%an' -- '*.thy' | sort -u | paste -sd', ')
printf "%-34s %s\n" "Commits touching .thy"    "$COMMITS"
printf "%-34s %s\n" "First .thy commit"         "$FIRST"
printf "%-34s %s\n" "Last  .thy commit"         "$LAST"
printf "%-34s %s\n" "Development span (days)"    "$DAYS"
printf "%-34s %s\n" "Authors"                    "$AUTHORS"

echo
echo "----  per-day .thy line churn (added / deleted), last 14 active days ----"
git log --date=short --pretty='C%ad' --numstat -- '*.thy' | awk '
  /^C/ { d=substr($0,2); next }
  $3 ~ /\.thy$/ { add[d]+=$1; del[d]+=$2 }
  END { for (k in add) printf "%s  +%-7d -%-7d\n", k, add[k], del[k] }' \
  | sort | tail -14
