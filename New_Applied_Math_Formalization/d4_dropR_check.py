#!/usr/bin/env python3
# =============================================================================
# d4_dropR_check.py  --  pursue the R*-degeneracy (FORMALIZATION_DIARY 2026-08-06).
#
# The de-risk localized the collision rank-drop to the R* (reduced-gradU / slot)
# equation.  This script tests the resulting hypothesis:
#
#   HYPOTHESIS.  Dropping the R* row leaves the remaining n equations
#   {scalar, radial_k (k != slot)} SUBMERSIVE (rank n) at the zeros
#   (cvec != 0, det(Dcvec) != 0), including at collisions.  If so, the bad set
#   sits in a dim-3 reduced solution set, its x-image has dim <= 3 + n, and
#   3 + n < 2n for n >= 4  ==>  negligible, WITHOUT R*.
#
# For each genuine zero it reports, split by collision multiplicity (# of
# coincidence relations = n - #blocks):
#   * corank of the FULL (n+1)-eq Jacobian,
#   * whether {scalar, radials} (drop R*) has full rank n,
#   * for multi-collisions where it does not, whether ALSO dropping duplicated
#     radial rows (dedup) restores rank.
#
# Reuses the validated residual in d4_collision_derisk.py.
# Usage:  python3 d4_dropR_check.py [n] [restarts]
# =============================================================================
import sys
import numpy as np
import d4_collision_derisk as H

np.set_printoptions(precision=4, suppress=True, linewidth=160)

def row_rank(M, rtol=1e-7):
    if M.shape[0] == 0:
        return 0, np.array([])
    s = np.linalg.svd(M, compute_uv=False)
    return int(np.sum(s > rtol * s[0])), s

def study(n, restarts, chart=1, slot=0, seed=0):
    f = lambda zz: H.residual(zz, n, slot, chart)
    zeros = H.find_zeros(n, restarts, slot, chart, seed=seed)
    # keep only very clean zeros
    zeros = [z for z in zeros if np.linalg.norm(f(z)) < 1e-10]
    print(f"\n===== n={n}: {len(zeros)} clean zeros (resid<1e-10);  3+n={3+n} < 2n={2*n}? {3+n < 2*n} =====")

    buckets = {}  # ncoinc -> [total, dropR_full, dropR_dedup_full]
    for z in zeros:
        Jf = H.jacobian_fd(f, z, n + 1)
        rk_full, s_full = row_rank(Jf)
        corank = (n + 1) - rk_full
        blocks = H.clusters_exact_t(z[2:2+n])
        ncoinc = n - len(blocks)

        # drop the R* row (output index 1+slot)
        keep = [i for i in range(n + 1) if i != 1 + slot]
        JnoR = Jf[keep, :]                     # n rows
        rk_noR, s_noR = row_rank(JnoR)
        dropR_full = (rk_noR == n)

        # additionally dedup radial rows: keep one radial per non-slot block
        blk_of = {}
        for ci, blk in enumerate(blocks):
            for m in blk:
                blk_of[m] = ci
        seen = set(); keep2 = [0]               # always keep scalar (output 0)
        for m in range(n):
            if m == slot:                       # R* dropped
                continue
            ci = blk_of[m]
            if ci not in seen:
                seen.add(ci); keep2.append(1 + m)
        Jdd = Jf[keep2, :]
        rk_dd, _ = row_rank(Jdd)
        dedup_full = (rk_dd == Jdd.shape[0])

        b = buckets.setdefault(ncoinc, [0, 0, 0, []])
        b[0] += 1; b[1] += dropR_full; b[2] += dedup_full
        if ncoinc >= 1 and not dropR_full and len(b[3]) < 4:
            b[3].append((blocks, corank, rk_noR, s_noR[:6]))

    print(f"  {'ncoinc':>6} {'zeros':>6} {'dropR->rank n':>14} {'dropR+dedup full':>17}")
    for k in sorted(buckets):
        tot, dr, dd, _ = buckets[k]
        tag = "(distinct)" if k == 0 else ("(single)" if k == 1 else "(multi)")
        print(f"  {k:>6} {tot:>6} {dr:>10}/{tot:<3} {dd:>13}/{tot:<3}  {tag}")
    # detail on failures
    for k in sorted(buckets):
        for (blocks, corank, rk_noR, sv) in buckets[k][3]:
            print(f"    FAIL ncoinc={k} blocks={blocks} full_corank={corank} "
                  f"dropR_rank={rk_noR}/{n}  sv(noR)={np.round(sv,4)}")

    # verdict
    single = buckets.get(1, [0,0,0,[]])
    multi = [buckets[k] for k in buckets if k >= 2]
    print("\n  ---")
    if single[0]:
        print(f"  single collisions: dropR restores rank n in {single[1]}/{single[0]}")
    if multi:
        mt = sum(b[0] for b in multi); md = sum(b[1] for b in multi); mdd = sum(b[2] for b in multi)
        print(f"  multi  collisions: dropR restores rank n in {md}/{mt};  dropR+dedup in {mdd}/{mt}")
    return buckets

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    study(n, restarts, seed=11)
