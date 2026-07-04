#!/usr/bin/env python3
# r31 fast targeted probe: JGE single-branch/parent + M0RUN, memoized Red.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
import red_model as rm
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm,
                       Br, FirstNodes, Joints, hasParent, fmt, TrMax, Pred,
                       nextrel1, is_standard)

# memoize Red on tuple-of-tuples
_redcache={}
def Red(M):
    key=tuple(M)
    if key in _redcache: return _redcache[key]
    r=rm.Red(list(M)); _redcache[key]=r; return r
def is_reduced(M): return Red(M)==list(M)

def transJ0(M): return parent(M,0,Lng(M)-1)
def condIII(M):
    n=Lng(M)
    if n<3: return False
    if not hasParent(M,0,n-1): return False
    if not hasParent(M,1,n-1): return False
    j0=transJ0(M)
    return (entry(M,1,n-1)>0 and entry(M,1,j0)>=entry(M,1,n-1) and adm(M,j0))
def genuineIII(M):
    if Lng(M)-1<=1: return False
    if not monoT(M): return False
    if not is_reduced(M): return False
    if not hasParent(M,1,Lng(M)-1): return False
    return condIII(M)

def main():
    t0=time.time()
    Lmax=int(sys.argv[1]) if len(sys.argv)>1 else 7
    vmax=int(sys.argv[2]) if len(sys.argv)>2 else 5
    std=(len(sys.argv)>3 and sys.argv[3]=='std')
    cells=[(a,b) for a in range(vmax) for b in range(vmax)]
    hosts=0
    jge_ok=jge_bad=0; sb1=sbm=0; par_ok=par_bad=0
    m0_ok=m0_bad=0; m0h=0
    jge_ex=[]; m0_ex=[]; sb_ex=[]
    budget=1400
    for L in range(3,Lmax+1):
        cnt=0
        for tup in itertools.product(cells,repeat=L-1):
            if time.time()-t0>budget: break
            M=[(0,0)]+list(tup)
            if not genuineIII(M): continue
            if std and not is_standard(M): continue
            hosts+=1; cnt+=1
            jm2=parent(M,1,Lng(M)-1); jm3=Adm(M,jm2)
            if jm3<jm2:
                N=seg(M,jm3,Lng(M)-1); RN=Red(N)
                bR=Br(RN); tr=TrMax(RN)
                if len(bR)==1: sb1+=1
                else:
                    sbm+=1
                    if len(sb_ex)<8: sb_ex.append((fmt(M),fmt(RN),len(bR)))
                if tr+1<Lng(RN):
                    p=parent(RN,0,tr+1)
                    if p==tr: par_ok+=1
                    else: par_bad+=1
                jl=Joints(RN)
                if bR and jl and jl[-1] is not None:
                    if tr<=jl[-1]: jge_ok+=1
                    else:
                        jge_bad+=1
                        if len(jge_ex)<8: jge_ex.append((fmt(M),fmt(RN),tr,jl[-1]))
            else:
                m0h+=1
                if nextrel1(M,jm2,jm2+1): m0_ok+=1
                else:
                    m0_bad+=1
                    if len(m0_ex)<8: m0_ex.append((fmt(M),jm2,adm(M,jm2)))
        print(f"[L={L}] +{cnt} hosts={hosts} t={time.time()-t0:.0f}s", flush=True)
        if time.time()-t0>budget: print("[budget stop]"); break
    print("="*60)
    print(f"HOSTS={hosts}  std={std}")
    print(f"[JGE] TrMax<=Joints!last ok={jge_ok} bad={jge_bad}; single-branch one={sb1} multi={sbm}; parent==TrMax ok={par_ok} bad={par_bad}")
    for e in sb_ex: print("  MULTI-BR:",e)
    for e in jge_ex: print("  JGE BAD:",e)
    print(f"[M0RUN] ok={m0_ok} bad={m0_bad} (m0-hosts={m0h})")
    for e in m0_ex: print("  M0 BAD:",e)

if __name__=='__main__': main()
