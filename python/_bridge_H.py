from red_model import *
import sys
sys.setrecursionlimit(10000)

def build_closure(depth_max=5, ubound=3, vbound=6, maxlen=16):
    bases=[]
    for u in range(0,ubound+1):
        for v in range(u,vbound+1):
            bases.append(tuple(diagSeq(u,v)))
    seen=set(bases); frontier=list(bases); allM=set(bases)
    # remember oper parents:  map tuple(N) -> (tuple(M), n)
    parentof={}
    for d in range(depth_max):
        newf=[]
        for M in frontier:
            Ml=list(M)
            for n in range(1,4):
                try: Nn=oper(Ml,n)
                except Exception: continue
                if len(Nn)<1 or len(Nn)>maxlen: continue
                t=tuple(Nn)
                if t not in seen:
                    seen.add(t); allM.add(t); newf.append(t)
                    parentof.setdefault(t,(M,n))
        frontier=newf
    return [list(M) for M in allM], parentof

def gated_interior(N):
    """yield z that are gated interior: j0<z<j1, hasParent N 1 z, parent>j0."""
    L=Lng(N)
    if L<=1: return
    j1=L-1
    if not hasParent(N,1,j1): return
    j0=parent(N,1,j1)
    if j0 is None or not (j0<j1): return
    for z in range(0,j1):
        if not hasParent(N,1,z): continue
        pz=parent(N,1,z)
        if pz is None: continue
        if pz>j0 and z>j0:
            yield (j0,j1,z)

def Ez_at(N,z):
    j1=Lng(N)-1
    return entry(N,0,j1)==entry(N,0,z)+(j1-z)

Ms,parentof=build_closure()
print("closure",len(Ms))

# only consider oper-produced N (those with a recorded parent)
tot_in=0; fail_in=0; tot_pre=0; fail_pre=0
ex_in=[]; ex_pre=[]
for tN,(M,n) in parentof.items():
    N=list(tN); M=list(M)
    L=Lng(M); 
    if L<=1: continue
    j1M=L-1
    if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
    i1=idx1(M,j1M)
    if i1!=1: continue
    if not hasParent(M,1,j1M): continue
    j0M=parent(M,1,j1M)
    if not (j0M<j1M): continue
    w=j1M-j0M
    for (j0N,j1N,z) in gated_interior(N):
        # j0N should equal parent N 1 (Lng N -1)
        # classify z
        if z< j0M:
            # PREFIX case
            tot_pre+=1
            S=seg(M,0,j0M)  # take j0M+1
            # z gated interior of S?  S endpoint = j0M
            ok=True
            if S not in []:
                LS=Lng(S)
                if LS<=1: ok=False
                else:
                    jS=LS-1  # = j0M
                    # z should be interior gated of S, with Ez_S(z)
                    if not (z<jS): ok=False
                    elif not Ez_at(S,z): ok=False
            if not ok:
                fail_pre+=1
                if len(ex_pre)<6: ex_pre.append((fmt(M),n,z,j0M))
        else:
            # IN-BLOCK case: z = j0N + q*w + s ; recover s
            # by readback structure z-j0N = q*w+s ; s in (0,w)
            off = z - j0N
            q,s = divmod(off,w)
            tot_in+=1
            if s==0:
                # block start - vacuous for gated z? skip but note
                continue
            z0 = j0M+s
            # claim: N-gated <=> M-gated z0 (parent M 1 z0 = j0M? actually >j0M-1)
            okM = hasParent(M,1,z0)
            if okM:
                pz0=parent(M,1,z0)
                # M-gated interior: pz0 >= j0M  (the readback says N-gated <=> z0 M-gated)
                okM = (z0< j1M) and (pz0>=j0M)
            # and Ez_M(z0) should hold (M-side IH)
            okE = Ez_at(M,z0) if z0<Lng(M) else False
            if not (okM and okE):
                fail_in+=1
                if len(ex_in)<6: ex_in.append((fmt(M),n,z,off,q,s,z0,okM,okE))

print("IN-BLOCK gated z (s>0): tot",tot_in,"fail",fail_in)
for e in ex_in: print("  INFAIL",e)
print("PREFIX gated z: tot",tot_pre,"fail",fail_pre)
for e in ex_pre: print("  PREFAIL",e)
