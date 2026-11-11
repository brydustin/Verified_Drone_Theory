import numpy as np
rng=np.random.default_rng(1); pi=np.pi
def parts(t,m):
    d=t[:,None]-t[None,:]
    s=np.sin(d).sum(1); q=(d*np.cos(d)).sum(1); W=np.cos(d).sum(); P=(d*np.sin(d)).sum()
    return s[m],q[m],W,P
def f(t,m):
    s,q,W,P=parts(t,m); return s*(P+W)+q*W
worst=0; worst2=0
for N in (2,3,4,6,9):
    for _ in range(200):
        t=rng.uniform(-6,6,N); m=rng.integers(N)
        t2=t.copy(); t2[m]+=2*pi
        s,q,W,P=parts(t,m)
        Cm=sum(np.cos(t[m]-t[p]) for p in range(N) if p!=m)
        worst=max(worst,abs((f(t2,m)-f(t,m))-2*pi*(2*s*s+Cm*W)))
        B=sum(np.exp(1j*t[p]) for p in range(N) if p!=m)
        # tau* with e^{i tau*} conj(B) = |B|
        ts=t.copy(); ts[m]=np.angle(B)
        s,q,W,P=parts(ts,m); Cm=sum(np.cos(ts[m]-ts[p]) for p in range(N) if p!=m)
        worst2=max(worst2,abs((2*s*s+Cm*W)-abs(B)*(1+abs(B))**2))
print("periodicity-difference identity max err:",worst)
print("a(tau*) = |B|(1+|B|)^2 max err:",worst2)
# witness f_1 != 0 at t=(pi/2,0,...,0)
for N in (2,4,7,11):
    t=np.zeros(N); t[0]=pi/2
    print(N, f(t,0), (N-1)*((N-1)*pi+(N-1)**2+1))
