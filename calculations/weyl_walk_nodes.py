#!/usr/bin/env python3
# Requires numpy, scipy.
import numpy as np, itertools
sx=np.array([[0,1],[1,0]],complex); sy=np.array([[0,-1j],[1j,0]]); sz=np.diag([1,-1]).astype(complex); I=np.eye(2)
def C(t): return np.array([[np.cos(t),-np.sin(t)],[np.sin(t),np.cos(t)]],complex)
def Wp(a,b,k): return C(b)@np.diag([1,np.exp(1j*k)])@C(a)@np.diag([np.exp(-1j*k),1])
def rotY(t): return np.cos(t/2)*I-1j*np.sin(t/2)*sy   # Bloch rotation by t about y
def eigbasis(s):
    w,v=np.linalg.eigh(s); return v[:,::-1]
R=[eigbasis(sx),eigbasis(sy),eigbasis(sz)]
def unit(j,k,r):
    V=rotY(-r)  # align linear term to sigma_z
    return R[j]@V@Wp(-r,r,k)@V.conj().T@R[j].conj().T
def W(k,r):
    M=I
    for j in range(3): M=M@unit(j,k[j],r)
    return M
def ph(M): return np.angle(np.linalg.eigvals(M))
# Split-step Weyl walk with per-axis twin gapping: speeds, corner gaps and extra nodes.
for r in [0.3,0.5,np.pi/4,1.0]:
    H1=[1j*(unit(j,1e-6,r)-I)/1e-6 for j in range(3)]
    print('r',round(r,3),'linear terms ~', [np.round(np.real(np.trace(H@s))/2,4) for H,s in zip(H1,[sx,sy,sz])])
    # speeds
    sp=[]
    for d in [(1,0,0),(1,1,0),(1,1,1),(0.3,-0.7,0.2)]:
        d=np.array(d,float); d/=np.linalg.norm(d); sp.append(round(np.abs(ph(W(1e-4*d,r))).max()/1e-4,4))
    # corners and grid gap
    corners={c: round(min(min(abs(x),np.pi-abs(x)) for x in ph(W(np.array(c)*np.pi,r))),4) for c in itertools.product([0,1],repeat=3) if any(c)}
    n=24; g=9; arg=None
    for p in itertools.product(np.linspace(-np.pi,np.pi,n,endpoint=False),repeat=3):
        p=np.array(p)
        if np.linalg.norm(p)<0.5: continue
        v=min(min(abs(x),np.pi-abs(x)) for x in ph(W(p,r)))
        if v<g: g=v; arg=p
    print('  speeds',sp,' corner gaps',corners,' grid min gap',round(g,4),'at',np.round(arg,2))
from scipy.optimize import minimize
r=0.5
f=lambda p: min(min(abs(x),np.pi-abs(x)) for x in ph(W(p,r)))
best=[]
rng=np.random.default_rng(1)
for _ in range(60):
    p0=rng.uniform(-np.pi,np.pi,3)
    if np.linalg.norm(p0)<0.5: continue
    res=minimize(f,p0,method='Nelder-Mead',options={'xatol':1e-10,'fatol':1e-12,'maxiter':4000})
    if res.fun<1e-6 and np.linalg.norm(((res.x+np.pi)%(2*np.pi))-np.pi)>0.3: best.append(np.round(((res.x+np.pi)%(2*np.pi))-np.pi,4))
print('extra nodes found:', len(best)); 
import collections
print(collections.Counter(tuple(b) for b in best).most_common(8))
