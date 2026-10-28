#!/usr/bin/env python3
# Two-slice (two D4 sector) domain-wall Wilson-Dirac Hamiltonian: zero modes, chirality per
# slice, speed, and twin gaps. Requires numpy.
import numpy as np, itertools
s0=np.eye(2); sx=np.array([[0,1],[1,0]],complex); sy=np.array([[0,-1j],[1j,0]]); sz=np.diag([1.,-1]).astype(complex)
k2=np.kron
# 5 anticommuting Hermitian 4x4: alpha1..3, beta, alpha4 (=gamma5-like)
a=[k2(sx,sx),k2(sx,sy),k2(sx,sz)]; beta=k2(sz,s0); a4=k2(sy,s0)
G5=a4  # chirality on the walls is measured by the extra-dimension matrix
def H(k,Ls,M,r=1.0):
    n=4*Ls; Hm=np.zeros((n,n),complex)
    W=r*sum(1-np.cos(kj) for kj in k)
    onsite=sum(np.sin(kj)*a[j] for j,kj in enumerate(k))+beta*(W-M+r)   # r from s-direction Wilson diag
    for s in range(Ls):
        Hm[4*s:4*s+4,4*s:4*s+4]=onsite
        if s+1<Ls:
            hop=0.5*(-1j*a4) - 0.5*r*beta     # forward hop in s
            Hm[4*s:4*s+4,4*(s+1):4*(s+1)+4]=hop
            Hm[4*(s+1):4*(s+1)+4,4*s:4*s+4]=hop.conj().T
    return Hm
def low(k,Ls,M):
    w,v=np.linalg.eigh(H(k,Ls,M)); i=np.argsort(abs(w))[:2]
    loc=[]
    for j in i:
        x=v[:,j]; wts=[np.linalg.norm(x[4*s:4*s+4])**2 for s in range(Ls)]
        ch=np.real(sum(x[4*s:4*s+4].conj()@G5@x[4*s:4*s+4] for s in range(Ls)))
        loc.append((round(w[j],5),[round(t,3) for t in wts],round(ch,3)))
    return loc
for Ls,M in [(2,1.0),(2,0.8),(8,1.0)]:
    print(f"Ls={Ls} M={M}")
    for k in [(0,0,0),(0.01,0,0),(0.05,0.02,0),(0.2,0,0)]:
        print("  k",k,low(np.array(k),Ls,M))
    # doublers: lowest |E| at corners
    cg={c: round(min(abs(np.linalg.eigvalsh(H(np.array(c)*np.pi,Ls,M)))),3) for c in itertools.product([0,1],repeat=3) if any(c)}
    print("  corner gaps",cg)
    # global min gap away from origin
    g=min(min(abs(np.linalg.eigvalsh(H(np.array(p),Ls,M)))) for p in itertools.product(np.linspace(-np.pi,np.pi,20,endpoint=False),repeat=3) if np.linalg.norm(p)>0.5)
    print("  min |E| away from k=0:",round(g,4))
Gam=1j*beta@a4
print("Gamma hermitian:",np.allclose(Gam,Gam.conj().T), "sq=1:",np.allclose(Gam@Gam,np.eye(4)))
for k in [(0.01,0,0),(0.03,0.04,-0.02),(0.2,0.1,0)]:
    w,v=np.linalg.eigh(H(np.array(k),2,1.0)); idx=np.argsort(abs(w))[:2]
    for j in idx:
        x=v[:,j]; out=[]
        for s in range(2):
            y=x[4*s:4*s+4]; nrm=np.linalg.norm(y)**2
            out.append((round(nrm,3), round(np.real(y.conj()@Gam@y)/max(nrm,1e-12),3)))
        print("  k",k,"E",round(w[j],4),"(weight, chirality) per slice",out)
# speed check
for d in [(1,0,0),(1,1,1),(0.3,-0.7,0.2)]:
    d=np.array(d,float); d/=np.linalg.norm(d)
    print(" speed",np.round(sorted(abs(np.linalg.eigvalsh(H(1e-4*d,2,1.0))))[0]/1e-4,5))
