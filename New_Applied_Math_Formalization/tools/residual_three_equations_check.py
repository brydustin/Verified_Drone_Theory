"""Sanity check of the 'three-equation' description of the non-submersive stratum.
Design: omega0=(pi/2,0), omegas=(0,0).  U(x,w)=g(theta)*|sum_n exp(-i c(w).x_n)|^2.
Checks, at random (x,w):
  (A) Dc^{-T} D_x Phi [slot_m cperp] = -2 g s_m cperp
  (B) c-component of Dc^{-T} D_x Phi [slot_m c] = -2|c|^2 g (lam s_m + q_m)
  (C) Dc^{-T} Phi . c     = g*( W (lam-1) - P )
  (D) Dc^{-T} Phi . cperp = W nu.cperp - 2 g sum s_n u_n
Then solves the system and checks Phi=0, rank D_x Phi = 1, f_m(t)=0, cos(phi) formula.
"""
import numpy as np
from scipy.optimize import least_squares
rng = np.random.default_rng(0)
pi = np.pi

def cvec(w):
    th, ph = w
    return np.array([np.sin(th)*np.cos(ph) + np.cos(th) - 1.0, np.sin(th)*np.sin(ph)])
def Dc(w):
    th, ph = w
    return np.array([[np.cos(th)*np.cos(ph) - np.sin(th), -np.sin(th)*np.sin(ph)],
                     [np.cos(th)*np.sin(ph),               np.sin(th)*np.cos(ph)]])
def g(th):
    return np.cos(pi/2*np.cos(th))**2/np.sin(th)**2
def gp(th, h=1e-6):
    return (g(th+h)-g(th-h))/(2*h)
def perp(c): return np.array([-c[1], c[0]])

def U(x, w):
    c = cvec(w); ph = x @ c
    A = np.exp(-1j*ph).sum()
    return g(w[0])*abs(A)**2
def Phi(x, w):
    """grad_omega U, analytic."""
    c = cvec(w); J = Dc(w); t = x @ c
    d = t[:, None] - t[None, :]
    W = np.cos(d).sum()
    # grad_c W = -sum_{n,p} sin(c.d_np) d_np
    X = x[:, None, :] - x[None, :, :]
    gradcW = -(np.sin(d)[:, :, None]*X).sum(axis=(0, 1))
    return np.array([gp(w[0])*W, 0.0]) + g(w[0])*(J.T @ gradcW)
def DxPhi(x, w, h=1e-6):
    N = x.shape[0]; M = np.zeros((2, 2*N))
    for n in range(N):
        for k in range(2):
            e = np.zeros_like(x); e[n, k] = h
            M[:, 2*n+k] = (Phi(x+e, w) - Phi(x-e, w))/(2*h)
    return M
def quantities(x, w):
    c = cvec(w); t = x @ c; u = x @ perp(c)
    d = t[:, None] - t[None, :]
    s = np.sin(d).sum(axis=1); q = (d*np.cos(d)).sum(axis=1)
    W = np.cos(d).sum(); P = (d*np.sin(d)).sum()
    J = Dc(w)
    nu = np.linalg.solve(J.T, np.array([gp(w[0]), 0.0]))
    lam = 1 + (nu @ c)/g(w[0])
    return c, t, u, s, q, W, P, nu, lam

def slot(N, m, v):
    e = np.zeros((N, 2)); e[m] = v; return e.reshape(-1)

print("=== identities at random points ===")
for N in (4, 5, 7):
    worst = np.zeros(4)
    for trial in range(20):
        x = rng.normal(size=(N, 2))*2
        w = np.array([rng.uniform(pi/4, 3*pi/4), rng.uniform(-pi, pi)])
        c, t, u, s, q, W, P, nu, lam = quantities(x, w)
        J = Dc(w); gg = g(w[0]); cp = perp(c)
        M = DxPhi(x, w); JT = np.linalg.inv(J.T)
        for m in range(N):
            vA = JT @ (M @ slot(N, m, cp))
            worst[0] = max(worst[0], np.abs(vA - (-2*gg*s[m]*cp)).max())
            vB = JT @ (M @ slot(N, m, c))
            worst[1] = max(worst[1], abs(vB @ c - (-2*(c@c)*gg*(lam*s[m]+q[m]))*1.0))
        ph = JT @ Phi(x, w)
        worst[2] = max(worst[2], abs(ph @ c - gg*(W*(lam-1) - P)))
        worst[3] = max(worst[3], abs(ph @ cp - (W*(nu@cp) - 2*gg*(s@u))))
    print(f"N={N}: max abs errors (A,B,C,D) = {worst}")

print("=== solve the system, test membership in the stratum ===")
def solve(N, seed):
    r = np.random.default_rng(seed)
    def F(z):
        w = z[:2]; t = np.concatenate([[0.0], z[2:]])
        d = t[:, None] - t[None, :]
        s = np.sin(d).sum(axis=1); q = (d*np.cos(d)).sum(axis=1)
        W = np.cos(d).sum(); P = (d*np.sin(d)).sum()
        c = cvec(w); nu = np.linalg.solve(Dc(w).T, np.array([gp(w[0]), 0.0]))
        lam = 1 + (nu@c)/g(w[0])
        return np.concatenate([lam*s + q, [W*(lam-1) - P]])
    z0 = np.concatenate([[r.uniform(pi/4+.1, 3*pi/4-.1), r.uniform(-3, 3)], r.uniform(-4, 4, size=N-1)])
    lo = np.concatenate([[pi/4, -pi], -np.inf*np.ones(N-1)]); hi = np.concatenate([[3*pi/4, pi], np.inf*np.ones(N-1)])
    sol = least_squares(F, z0, bounds=(lo, hi), xtol=1e-15, ftol=1e-15, gtol=1e-15)
    return sol, r
found = 0
for N in (4, 5, 6, 7):
    for seed in range(400):
        sol, r = solve(N, seed)
        if np.abs(sol.fun).max() > 1e-10: continue
        w = sol.x[:2]; t = np.concatenate([[0.0], sol.x[2:]])
        c = cvec(w); J = Dc(w)
        if c@c < 1e-3 or abs(np.linalg.det(J)) < 1e-2: continue
        d = t[:, None] - t[None, :]
        s = np.sin(d).sum(axis=1); q = (d*np.cos(d)).sum(axis=1)
        W = np.cos(d).sum(); P = (d*np.sin(d)).sum()
        if np.abs(s).max() < 1e-2 or W < 1e-2: continue
        m = int(np.argmax(np.abs(s)))
        nu = np.linalg.solve(J.T, np.array([gp(w[0]), 0.0])); cp = perp(c)
        u = r.normal(size=N)
        u[m] = (W*(nu@cp)/(2*g(w[0])) - (np.delete(s, m) @ np.delete(u, m)))/s[m]
        x = (t[:, None]*c[None, :] + u[:, None]*cp[None, :])/(c@c)
        sv = np.linalg.svd(DxPhi(x, w), compute_uv=False)
        fm = s[m]*(P+W) + q[m]*W
        th, ph = w; gg, gd = g(th), gp(th)
        K = gg*(s[m]+q[m])*np.sin(th) + gd*s[m]*(1-np.cos(th))
        Num = gg*(s[m]+q[m])*np.cos(th) + gd*s[m]*np.sin(th)
        mind = np.abs(d + np.eye(N)*9).min()
        print(f"N={N} seed={seed}: |Phi|={np.abs(Phi(x,w)).max():.1e} sing.vals={sv[0]:.3f},{sv[1]:.1e} "
              f"f_m={fm:.1e} cosphi-Num/K={np.cos(ph)-Num/K:.1e} min|t_i-t_j|={mind:.2f} w=({th:.3f},{ph:.3f})")
        found += 1
        if found % 6 == 0: break
print("found", found)
