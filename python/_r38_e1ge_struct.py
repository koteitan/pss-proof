#!/usr/bin/env python3
# r38 E1GE structural probe: for non-anc hosts, dump the local geometry that
# should drive the proof:
#   ramp1: entry1 j1 == entry1 jm2 + 1  (RedCondA row1)
#   nr0:   nextrel0 M jm2 (jm2+1)       (jm2+1 is a row-0 child of jm2)
#   p0:    parent0(jm2+1)==jm2, hasParent0(jm2+1)
#   rampA0: entry0(jm2+1)==entry0 jm2 + 1
#   e1eq:  entry1(jm2+1)==entry1 j1
#   hasP1(jm2+1), parent1(jm2+1), and entry1 of that parent
# Collect DEEP non-anc hosts; report fractions of each sub-fact; any violation.
import sys, time, random
sys.path.insert(0,'python')
from fast_pss import (Lng, entry, le0, nextrel0, nextrel1, hasParent1, parent1,
                      hasParent0, parent0, oper, reduced, diagSeq, fmt)

def zeroT(M): return Lng(M)==1 and entry(M,1,0)==0
def monoT(M): return (not zeroT(M)) and le0(M,0,Lng(M)-1)
def condIIIorIV(M):
    j1=Lng(M)-1
    if not hasParent0(M,j1): return False
    j0=parent0(M,j1)
    return entry(M,1,j1)>0 and entry(M,1,j0)>=entry(M,1,j1)
def host(M):
    L=Lng(M); j1=L-1
    if L<3 or not monoT(M): return None
    if not hasParent1(M,j1) or not hasParent0(M,j1): return None
    if not condIIIorIV(M): return None
    jm2=parent1(M,j1); j0=parent0(M,j1)
    if not (jm2<j0) or jm2+1>=L: return None
    return (jm2,j0,j1)

random.seed(7)
seed_cap=5; maxlen=30; maxdepth=24; ncap=5; frontcap=15000
seen=set(); frontier=[]
for u in range(seed_cap):
    for v in range(u,seed_cap):
        M=tuple(diagSeq(u,v))
        if 1<Lng(M)<=maxlen: seen.add(M); frontier.append(M)
st={k:0 for k in ['nonanc','ramp1','nr0','p0eq','rampA0','e1eq','hasP1p1','p1eq_jm2','viol']}
viol=[]; samples=[]
for depth in range(maxdepth+1):
    for M in frontier:
        r=host(list(M))
        if r is None: continue
        jm2,j0,j1=r; Ml=list(M)
        if le0(Ml,jm2+1,j1): continue  # anc branch: skip
        st['nonanc']+=1
        r1 = entry(Ml,1,j1)==entry(Ml,1,jm2)+1
        nr0 = nextrel0(Ml,jm2,jm2+1)
        p0 = hasParent0(Ml,jm2+1) and parent0(Ml,jm2+1)==jm2
        rA0 = entry(Ml,0,jm2+1)==entry(Ml,0,jm2)+1
        e1eq = entry(Ml,1,jm2+1)==entry(Ml,1,j1)
        hp1 = hasParent1(Ml,jm2+1)
        p1jm2 = hp1 and parent1(Ml,jm2+1)==jm2
        if r1: st['ramp1']+=1
        if nr0: st['nr0']+=1
        if p0: st['p0eq']+=1
        if rA0: st['rampA0']+=1
        if e1eq: st['e1eq']+=1
        if hp1: st['hasP1p1']+=1
        if p1jm2: st['p1eq_jm2']+=1
        if not (r1 and nr0 and p0 and rA0 and e1eq):
            st['viol']+=1
            if len(viol)<30: viol.append((fmt(Ml),'d',depth,'jm2',jm2,'j0',j0,'j1',j1,
                'r1',r1,'nr0',nr0,'p0',p0,'rA0',rA0,'e1eq',e1eq,'hp1',hp1,
                'e0',[entry(Ml,0,k) for k in range(Lng(Ml))],
                'e1',[entry(Ml,1,k) for k in range(Lng(Ml))]))
        if len(samples)<8 and depth>=14:
            samples.append((fmt(Ml),'d',depth,'jm2',jm2,'j1',j1,'e1jm2',entry(Ml,1,jm2),
                'e1jm2+1',entry(Ml,1,jm2+1),'e1j1',entry(Ml,1,j1),'p1(jm2+1)',
                parent1(Ml,jm2+1) if hp1 else None))
    # expand
    nxt=[]; fr=list(frontier); random.shuffle(fr)
    for M in fr:
        Ml=list(M)
        for n in range(1,ncap+1):
            try: Mn=oper(Ml,n)
            except Exception: continue
            if 1<len(Mn)<=maxlen:
                t=tuple(Mn)
                if t not in seen: seen.add(t); nxt.append(t)
        if len(nxt)>=frontcap: break
    if len(nxt)>frontcap: nxt=random.sample(nxt,frontcap)
    frontier=nxt
    if not frontier: break
print("nonanc",st['nonanc'],flush=True)
print("subfacts (of nonanc):",{k:st[k] for k in ['ramp1','nr0','p0eq','rampA0','e1eq','hasP1p1','p1eq_jm2']},flush=True)
print("violations",st['viol'],flush=True)
for v in viol: print("VIOL",v,flush=True)
for s in samples: print("SAMPLE",s,flush=True)
