#!/bin/bash
# Make a strict (quick_and_dirty = false) copy of the capstone chain that builds on Isabelle2026.
# Usage: make_copy.sh TARGET_DIR [SESSION_PREFIX]      (default prefix: AM26_)
# The project tree and the vendored Munkres directory are only read.
# Build:  ~/Desktop/Isabelle/Isabelle2026/bin/isabelle build -b -d TARGET_DIR -d TARGET_DIR/Munkres \
#           -d ~/Desktop/Isabelle/afp-2026-10-29/thys <PREFIX>Appendix_Frontier
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
SRC="$(cd "$HERE/../.." && pwd)"
MUNKRES="$(cd "$SRC/../../Imported_Munkres_Topology" && pwd)"
A="$1"; PFX="${2:-AM26_}"
[ -n "$A" ] || { echo "usage: $0 TARGET_DIR [SESSION_PREFIX]"; exit 2; }
[ -e "$A" ] && { echo "$A exists"; exit 2; }
mkdir -p "$A"
rsync -a --exclude 'M5_Dev_*' --exclude 'Residual' --exclude 'tools' --exclude '*.pdf' --exclude '*.aux' \
  --exclude '*.log' --exclude '*.out' --exclude '__pycache__' --exclude '.git' --exclude '.claude' \
  --exclude '.codex' --exclude '.agents' --exclude '*.thy~' --exclude '*.py' --exclude '*.md' --exclude '*.tex' "$SRC/" "$A/"
cd "$A"

# 1. session names and strict mode
grep -rl "Applied_Math_" --include=*.thy --include=ROOT . | xargs sed -i "s/Applied_Math_/${PFX}/g"
sed -i 's/quick_and_dirty = true/quick_and_dirty = false/g' ROOT

# 2. Munkres: real_arch_pow(_inv) were generalised and renamed in Isabelle2026
cp -r "$MUNKRES" Munkres
sed -i 's/\breal_arch_pow_inv\b/arch_pow_inv/g; s/\breal_arch_pow\b/arch_pow/g' Munkres/Top1_*.thy

# 3. HOL-Analysis now ships Higher_Differentiability_Multi: drop the tree's copy from the chain
cp "$HERE/Higher_Diff_Bridge_2026.thy" Appendix/Higher_Diff_Bridge_2026.thy
R=Appendix/Nonemptiness_Robust1.thy
sed -i "s|imports Nonemptiness_Regnonzero_Appendix \"${PFX}HigherDiff.Higher_Differentiability_Multi\"|imports Nonemptiness_Regnonzero_Appendix Higher_Diff_Bridge_2026|" "$R"
sed -i 's|have "GRAD (U_cart|have "GDERIV (U_cart|; s|grad_fun_satisfies_GRAD|grad_fun_satisfies_GDERIV|; s|simp add: has_gradient_def gradU_def|simp add: gderiv_def gradU_def|' "$R"

python3 - "$PFX" <<'PY'
import re, sys
pfx = sys.argv[1]
# ROOT: Appendix_Base needs Smooth_Manifolds directly and the bridge theory
s = open("ROOT").read()
old = f'''session {pfx}Appendix_Base in "Appendix" = {pfx}Nonemptiness +
  options [document = false, quick_and_dirty = false, timeout = 3600]
  sessions
    {pfx}HigherDiff
  theories
'''
assert old in s
s = s.replace(old, old.replace(f"    {pfx}HigherDiff\n", "    Smooth_Manifolds\n") + "    Higher_Diff_Bridge_2026\n")
open("ROOT", "w").write(s)

# 4. unqualified det is now the determinant of a linear map; matrices use matrix_det
for p in ["Nonemptiness_Paper.thy", "Parametric_Transversality_Euclidean_Base.thy",
          "Appendix/Nonemptiness_Regnonzero_Appendix.thy", "Appendix/Nonemptiness_Robust1.thy",
          "Appendix/Robust2/Nonemptiness_Robust2.thy", "Appendix/Robust3/Nonemptiness_Robust3.thy",
          "Appendix/Robust4Cover/D3_Curve_Cover.thy", "Appendix/Robust4/Nonemptiness_Robust4.thy"]:
    s = open(p).read()
    s = re.sub(r"(?<![A-Za-z0-9_'.\\])det(?![A-Za-z0-9_'])", "matrix_det", s)
    s = re.sub(r"(?<![A-Za-z0-9_'.])det_def(?![A-Za-z0-9_'])", "matrix_det_def", s)
    open(p, "w").write(s)

# 5. baby_Sard is now stated for Euclidean spaces; keep the Cartesian form as a wrapper
wrapper = r"""text \<open>Isabelle2026 states \<open>baby_Sard\<close> for Euclidean spaces with \<open>dim (range f')\<close>.  This is the
  Cartesian form with \<open>rank (matrix f')\<close> used below.\<close>

lemma baby_Sard_cart:
  fixes f :: "real^'m::finite \<Rightarrow> real^'n::finite"
  assumes mlen: "CARD('m) \<le> CARD('n)"
    and der: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
    and rank: "\<And>x. x \<in> S \<Longrightarrow> rank (matrix (f' x)) < CARD('n)"
  shows "negligible (f ` S)"
proof -
  have 1: "DIM(real^'m) \<le> DIM(real^'n)"
    using mlen by simp
  have 3: "dim (f' x ` UNIV) < DIM(real^'n)" if x: "x \<in> S" for x
  proof -
    have lin: "linear (f' x)"
      using der[OF x] has_derivative_linear by blast
    have "range (f' x) = range (\<lambda>v. matrix (f' x) *v v)"
      using lin by (simp add: matrix_works)
    then have "dim (range (f' x)) = rank (matrix (f' x))"
      by (simp add: rank_dim_range)
    then show ?thesis
      using rank[OF x] by simp
  qed
  show ?thesis
    by (rule baby_Sard[OF 1 der 3])
qed

"""
p = "Parametric_Transversality_Euclidean_Base.thy"; s = open(p).read()
assert s.count("thm baby_Sard\n") == 1
s = s.replace("(rule baby_Sard[", "(rule baby_Sard_cart[")
s = s.replace("thm baby_Sard\n", wrapper + "thm baby_Sard_cart\n")
open(p, "w").write(s)
p = "Nonemptiness_Paper.thy"; s = open(p).read()
open(p, "w").write(s.replace("(rule baby_Sard[", "(rule baby_Sard_cart["))
PY
# 6. an smt proof in Robust3 cites verit_minus_simplify(1) (a - a = 0), which Isabelle2026 no longer has
sed -i 's/ verit_minus_simplify(1))/ diff_self)/' Appendix/Robust3/Nonemptiness_Robust3.thy

echo "made $A (prefix $PFX)"
