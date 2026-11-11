#!/usr/bin/env python3
# =============================================================================
# d4_collision_derisk.py
#
# De-risk the "stratify-and-deduplicate" approach to the D4 transient
# t-collision (see FORMALIZATION_DIARY.md, 2026-08-06).
#
# It reconstructs the EXACT branch-2 repaired reduced-base residual
#   F : R^{n+3} -> R^{n+1},   input z = (w1, w2, t_0..t_{n-1}, a)
# at the Robust4 design point  w0 = (pi/2, 0),  ws = (0, 0),  from the real
# Isabelle definitions in M5_Dev_D4Branch/Scratch_D4Branch.thy and
# Appendix/Nonemptiness_Robust1.thy:
#
#   phase_t t m               = exp(-i t_m)                         (l.2684)
#   A_t_moment t              = sum_m exp(-i t_m)                   (l.2687)
#   A_t_weighted_moment t     = sum_m t_m exp(-i t_m)               (l.~=)
#   cvec_dip                  (l.735, Robust1)  -> c(w)  in R^2
#   Dcvec_dip                 = Jacobian of cvec_dip                (l.813)
#   gdip / gain_dip           (l.508 / 635, Robust1)
#   perp2 c                   = (-c2, c1)
#   branch2_ell_combo         = J(w) . ell            = L           (l.3728)
#   branch2_ell_gain_deriv    = ell_1 * gdip'(w1)     = egd         (l.3891)
#   branch2_radial_scalar_reduced_eq                                (l.3916)
#   branch2_special_coeffs -> scalar eq = L . perp2(c)              (l.2850)
#   branch2_reduced_gradU_scalar -> slot eq R*                      (l.5831)
#   repaired residual: vec component m is R* if m==slot else radial (l.6410/6475)
#
# The three tests, evaluated at genuine COLLISION zeros (residual ~ 0, some
# t_i == t_j mod 2pi, with cvec != 0 and det(Dcvec) != 0):
#
#   (A) corank of DF equals the number of coincidence relations (n - r);
#   (B) the cokernel of DF is spanned by coincidence-antisymmetric RADIAL
#       output directions {e_i - e_j : t_i=t_j, i,j non-slot}
#       ("unexplained cokernel" ~ 0);
#   (C) the DEDUPLICATED reduced Jacobian (merge coincident phases in the
#       domain, keep one radial per non-slot block in the codomain) has
#       FULL row rank -> the weighted distinct-phase system is a submersion.
#
# If (A)-(C) hold across all collision zeros, the approach is de-risked.
# A non-symmetric cokernel direction (B fails) or a rank-deficient reduced
# Jacobian (C fails) would refute it *before* any Isabelle work.
#
# Requires: numpy, scipy.  Usage:  python3 d4_collision_derisk.py [n] [restarts]
# =============================================================================

import sys
import numpy as np
from scipy.optimize import least_squares

np.set_printoptions(precision=4, suppress=True, linewidth=140)

# ---- design point ----------------------------------------------------------
W0 = np.array([np.pi / 2.0, 0.0])
WS = np.array([0.0, 0.0])

def kx(w): return np.sin(w[0]) * np.cos(w[1])
def ky(w): return np.sin(w[0]) * np.sin(w[1])
def kz(w): return np.cos(w[0])

# cvec_dip constants at the design point:  Kx = 1, Ky = 0  (Kz-denominator = 1)
_KX = (kx(W0) - kx(WS)) / (kz(WS) - kz(W0))   # = 1
_KY = (ky(W0) - ky(WS)) / (kz(WS) - kz(W0))   # = 0

def cvec(w):
    """cvec_dip w0 ws w  in R^2."""
    c1 = (kx(w) - kx(WS)) + _KX * (kz(w) - kz(WS))
    c2 = (ky(w) - ky(WS)) + _KY * (kz(w) - kz(WS))
    return np.array([c1, c2])

def dcvec_jac(w):
    """Dcvec_dip = Jacobian of cvec at w (2x2). Columns = Dcvec(axis1), Dcvec(axis2)."""
    eps = 1e-7
    J = np.zeros((2, 2))
    for j in range(2):
        wp = w.copy(); wp[j] += eps
        wm = w.copy(); wm[j] -= eps
        J[:, j] = (cvec(wp) - cvec(wm)) / (2 * eps)
    return J

def perp2(c):
    return np.array([-c[1], c[0]])

def gsinc(x):
    return np.where(np.abs(x) < 1e-12, 1.0, np.sin(x) / np.where(x == 0, 1.0, x))

def gdip(theta):
    return (np.pi**2 / 4.0) * gsinc((np.pi/2.0)*(1 - np.cos(theta))) \
                            * gsinc((np.pi/2.0)*(1 + np.cos(theta)))

def gdip_prime(theta):
    eps = 1e-7
    return (gdip(theta + eps) - gdip(theta - eps)) / (2 * eps)

# ---- moments (symmetric in t) ----------------------------------------------
def phase_t(t):                 # exp(-i t_m), vector
    return np.exp(-1j * t)

def A_moment(t):                # sum_m exp(-i t_m)
    return np.sum(phase_t(t))

def AW_moment(t):               # sum_m t_m exp(-i t_m)
    return np.sum(t * phase_t(t))

# ---- the residual ----------------------------------------------------------
def ell_of(a, chart):
    return np.array([1.0, a]) if chart == 1 else np.array([a, 1.0])

def residual(z, n, slot, chart):
    """F(z) in R^{n+1};  z = [w1, w2, t_0..t_{n-1}, a]. Output [scalar, vec_0..vec_{n-1}]."""
    w = z[0:2]
    t = z[2:2+n]
    a = z[2+n]
    ell = ell_of(a, chart)

    c = cvec(w)
    cc = float(c @ c)
    J = dcvec_jac(w)
    g1 = J[:, 0]; g2 = J[:, 1]         # Dcvec(axis1), Dcvec(axis2)
    L = ell[0] * g1 + ell[1] * g2      # branch2_ell_combo
    Lc = float(L @ c)
    p2c = perp2(c)

    g = gdip(w[0])                     # gain_dip
    gp = gdip_prime(w[0])
    egd = ell[0] * gp                  # branch2_ell_gain_deriv

    A = A_moment(t)
    AW = AW_moment(t)
    ph = phase_t(t)
    ML = (Lc / cc) * AW                # M12_tu_special_moment = (Lc/cc) AW

    # scalar equation:  ell . special_coeffs = L . perp2(c)
    scalar = float(L @ p2c)

    # radial(m):
    radial = (egd * (2 * cc * np.imag(np.conj(A) * ph))
              + g * (2 * cc * np.real(np.conj(ph) * ML)
                     + 2 * Lc * np.imag(np.conj(A) * ph)
                     - 2 * cc * (t / cc) * Lc * np.real(np.conj(A) * ph)))

    # slot R*  (branch2_reduced_gradU_scalar), with p2 = 0:
    d = np.linalg.det(J)
    p1 = gp
    Rstar = ((g2 @ p2c) * p1) * (abs(A)**2) \
            + g * (2 * d * np.real(np.conj(A) * ((-1j) * AW)))

    vec = radial.copy()
    vec[slot] = Rstar
    return np.concatenate([[scalar], vec])

def jacobian_fd(f, z, m_out, eps=1e-6):
    """central-difference Jacobian of f: R^k -> R^{m_out}."""
    k = z.size
    Jf = np.zeros((m_out, k))
    for j in range(k):
        zp = z.copy(); zp[j] += eps
        zm = z.copy(); zm[j] -= eps
        Jf[:, j] = (f(zp) - f(zm)) / (2 * eps)
    return Jf

# ---- collision / rank analysis ---------------------------------------------
def clusters_exact_t(t, tol=1e-5):
    """partition indices 0..n-1 by EXACT t-value coincidence t_i == t_j.

    The residual's index symmetry (radial(i)=radial(j)) needs *exact* t_i=t_j,
    not merely equal phases mod 2pi, because branch2_radial_scalar_reduced_eq
    carries an explicit t_m term (not only the phase e^{-i t_m}). So the
    deduplication of the approach is on exact t-blocks."""
    n = t.size
    assigned = [-1] * n
    reps = []
    for m in range(n):
        placed = False
        for ci, r in enumerate(reps):
            if abs(t[m] - t[r]) < tol:
                assigned[m] = ci; placed = True; break
        if not placed:
            reps.append(m); assigned[m] = len(reps) - 1
    return [[m for m in range(n) if assigned[m] == ci] for ci in range(len(reps))]

def rank_corank(Jf, rtol=1e-6):
    s = np.linalg.svd(Jf, compute_uv=False)
    smax = s[0] if s.size else 0.0
    rank = int(np.sum(s > rtol * max(smax, 1e-300)))
    return rank, Jf.shape[0] - rank, s

def analyze_zero(z, n, slot, chart):
    f = lambda zz: residual(zz, n, slot, chart)
    Jf = jacobian_fd(f, z, n + 1)
    rank, corank, s = rank_corank(Jf)
    blocks = clusters_exact_t(z[2:2+n])
    r = len(blocks)

    # (A) coincidence count = n - r
    ncoinc = n - r

    # cokernel: left-singular vectors for ~0 singular values
    U, sv, _ = np.linalg.svd(Jf)
    smax = sv[0]
    coker = U[:, [i for i in range(n + 1) if (i >= sv.size or sv[i] <= 1e-6 * smax)]]
    # output layout: index 0 = scalar; index 1+m = vec_m (radial unless m==slot)
    # (B) coincidence-antisymmetric RADIAL directions e_{1+i} - e_{1+j}
    sym_dirs = []
    for blk in blocks:
        nonslot = [m for m in blk if m != slot]
        for a_, b_ in zip(nonslot[:-1], nonslot[1:]):
            d = np.zeros(n + 1); d[1 + a_] = 1.0; d[1 + b_] = -1.0
            sym_dirs.append(d)
    if sym_dirs:
        S = np.array(sym_dirs).T
        Q, _ = np.linalg.qr(S)          # orthonormal basis of the symmetry span
        proj = Q @ (Q.T @ coker)
        unexplained = np.linalg.norm(coker - proj)  # part of cokernel outside sym span
    else:
        unexplained = np.linalg.norm(coker) if coker.shape[1] else 0.0

    # (C) deduplicated reduced Jacobian: merge coincident phases in domain,
    #     keep [scalar] + [R*(slot)] + one radial per non-slot-containing block.
    #     reduced input: (w1, w2, tau_0..tau_{r-1}, a);  full t = tau[block(m)].
    blk_of = np.zeros(n, dtype=int)
    for ci, blk in enumerate(blocks):
        for m in blk:
            blk_of[m] = ci
    nonslot_blocks = [ci for ci, blk in enumerate(blocks) if any(m != slot for m in blk)]

    def f_reduced(zr):
        w = zr[0:2]; tau = zr[2:2+r]; a = zr[2+r]
        t_full = tau[blk_of]
        full = residual(np.concatenate([w, t_full, [a]]), n, slot, chart)
        out = [full[0], full[1 + slot]]        # scalar, R*
        for ci in nonslot_blocks:
            rep = next(m for m in blocks[ci] if m != slot)
            out.append(full[1 + rep])
        return np.array(out)

    tau0 = np.array([z[2 + blocks[ci][0]] for ci in range(r)])
    zr0 = np.concatenate([z[0:2], tau0, [z[2 + n]]])
    m_red = 2 + len(nonslot_blocks)
    Jr = jacobian_fd(f_reduced, zr0, m_red)
    rrank, rcorank, rs = rank_corank(Jr)

    return dict(rank=rank, corank=corank, ncoinc=ncoinc, blocks=blocks,
                unexplained=unexplained, red_shape=Jr.shape,
                red_rank=rrank, red_full=(rcorank == 0), s=s)

# ---- root finding ----------------------------------------------------------
def find_zeros(n, restarts, slot, chart, seed=0):
    rng = np.random.default_rng(seed)
    f = lambda zz: residual(zz, n, slot, chart)
    zeros = []
    best_rn = np.inf
    for _ in range(restarts):
        w = np.array([rng.uniform(0.3, np.pi - 0.3), rng.uniform(-np.pi, np.pi)])
        t = rng.uniform(0, 2 * np.pi, size=n)
        a = rng.uniform(-3, 3)
        z0 = np.concatenate([w, t, [a]])
        try:
            # 'trf' handles underdetermined systems (n+1 residuals < n+3 variables)
            sol = least_squares(f, z0, method="trf", max_nfev=4000, xtol=1e-15, ftol=1e-15, gtol=1e-15)
        except Exception:
            continue
        z = sol.x
        rn = np.linalg.norm(f(z))
        best_rn = min(best_rn, rn)
        c = cvec(z[0:2]); cc = float(c @ c)
        d = abs(np.linalg.det(dcvec_jac(z[0:2])))
        if rn < 1e-9 and cc > 5e-2 and d > 5e-2:
            # keep RAW z (residual is NOT 2pi-periodic in t: explicit t_m term)
            if all(np.linalg.norm(z - zz) > 1e-4 for zz in zeros):
                zeros.append(z.copy())
    print(f"  (best residual norm achieved over restarts: {best_rn:.2e})")
    return zeros

# ---- driver ----------------------------------------------------------------
def run(n, restarts, chart=1):
    slot = 0  # branch2_repair_slot = SOME m; index 0 is a valid representative
    print(f"\n===== n={n}, chart={chart}, slot={slot}, restarts={restarts} =====")
    zeros = find_zeros(n, restarts, slot, chart)
    print(f"genuine zeros found: {len(zeros)}")
    if not zeros:
        print("  (no zeros; increase restarts)"); return

    stats = {"distinct_full": 0, "distinct_total": 0,
             "coll_total": 0, "coll_A_ok": 0, "coll_B_ok": 0, "coll_C_ok": 0,
             "anomalies": []}
    for z in zeros:
        info = analyze_zero(z, n, slot, chart)
        r = len(info["blocks"])
        collision = (r < n)
        tag = "COLLISION" if collision else "distinct  "
        if not collision:
            stats["distinct_total"] += 1
            if info["corank"] == 0:
                stats["distinct_full"] += 1
        else:
            stats["coll_total"] += 1
            A_ok = (info["corank"] == info["ncoinc"])
            B_ok = (info["unexplained"] < 1e-4)
            C_ok = info["red_full"]
            stats["coll_A_ok"] += A_ok
            stats["coll_B_ok"] += B_ok
            stats["coll_C_ok"] += C_ok
            flag = "" if (A_ok and B_ok and C_ok) else "   <<< CHECK"
            if flag:
                stats["anomalies"].append((info, z))
            print(f"  {tag} blocks={info['blocks']} corank={info['corank']} "
                  f"(pred {info['ncoinc']}) A={A_ok} B={B_ok}[{info['unexplained']:.1e}] "
                  f"C={C_ok}[{info['red_shape']}->rank {info['red_rank']}]{flag}")

    print("\n--- summary ---")
    print(f"  distinct-t zeros full rank : {stats['distinct_full']}/{stats['distinct_total']}")
    print(f"  collision zeros            : {stats['coll_total']}")
    if stats["coll_total"]:
        print(f"    (A) corank = #coincidences : {stats['coll_A_ok']}/{stats['coll_total']}")
        print(f"    (B) cokernel = sym span    : {stats['coll_B_ok']}/{stats['coll_total']}")
        print(f"    (C) dedup Jacobian full-rk : {stats['coll_C_ok']}/{stats['coll_total']}")
        verdict = (stats["coll_A_ok"] == stats["coll_total"]
                   and stats["coll_B_ok"] == stats["coll_total"]
                   and stats["coll_C_ok"] == stats["coll_total"])
        print(f"\n  VERDICT: {'APPROACH DE-RISKED (all tests pass)' if verdict else 'ANOMALIES -- revise approach'}")
    else:
        print("    (no collision zeros hit; try more restarts / smaller n)")

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    run(n, restarts, chart=1)
