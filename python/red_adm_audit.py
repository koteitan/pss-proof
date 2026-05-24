#!/usr/bin/env python3
"""Audit the admissibility/basepoint propositions:
  Red_adm    : AdmSet M = AdmSet(Red M)              (§6.5, content.md 992)
  admof_Red  : Adm M j  = Adm(Red M) j               (§6.5, content.md 1000)
  Red_marked : (M,m)∈Marked ⟹ (Red M,m)∈Marked       (§6.5, content.md 1008 / use 6461)
on (1) all of T_PS, and (2) ancestor-anchored slices of standard / reduced+mono.

Result (Lng≤3..4, e≤2): all three are FALSE on T_PS (e.g. Red_adm at (0,0)(0,1)(0,2),
Red_marked at (0,0)(0,1)(1,2)) but SOUND on ancestor-anchored slices — same pattern
as the other five §6.5 corollaries (correction A4)."""
import itertools, os
from red_model import (Red, fmt, Lng, monoT, le0, oper, diagSeq, seg, AdmSet, Adm, marked)

_cache={}
def Rd(M):                                  # memoized Red
    t=tuple(M)
    if t not in _cache: _cache[t]=Red(M)
    return _cache[t]

def adm_ok(M):    R=Rd(M); return AdmSet(M)==AdmSet(R)
def admof_ok(M):  R=Rd(M); return all(Adm(M,j)==Adm(R,j) for j in range(Lng(M)+1))
def marked_ok(M): R=Rd(M); return all((not marked(M,m)) or marked(R,m) for m in range(Lng(M)+1))
PROPS={"Red_adm":adm_ok,"admof_Red":admof_ok,"Red_marked":marked_ok}

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)

def gen_standard(maxv=2, steps=3, ns=(1,2,3), maxlen=8):
    seen=set(); fr=[]
    for v in range(maxv+1):
        M=diagSeq(0,v); fr.append(M); seen.add(tuple(M))
    out=list(fr)
    for _ in range(steps):
        nf=[]
        for M in fr:
            for n in ns:
                M2=oper(M,n); t=tuple(M2)
                if t not in seen and 0<len(M2)<=maxlen: seen.add(t); nf.append(M2); out.append(M2)
        fr=nf
    return out

def run(name, items, anchored):
    counts={k:[0,0,None] for k in PROPS}; seen=set()
    for S in items:
        n=Lng(S)
        slices=[seg(S,a,b) for a in range(n) for b in range(a,n) if le0(S,a,b)] if anchored else [S]
        for N in slices:
            t=tuple(N)
            if t in seen: continue
            seen.add(t)
            for k,f in PROPS.items():
                counts[k][0]+=1
                try: ok=f(N)
                except Exception: ok=False
                if not ok:
                    counts[k][1]+=1
                    if counts[k][2] is None: counts[k][2]=fmt(N)
    print(f"== {name}: {len(seen)} sequences ==")
    for k,(t,fl,ex) in counts.items():
        print(f"  {k:10s} tested={t:5d} FAIL={fl:4d} sound={fl==0}  {('ex='+ex) if ex else ''}")

def main():
    os.chdir(os.path.dirname(__file__))
    run("ALL T_PS (Lng<=3, e<=2)", list(enum(3,2)), anchored=False)
    run("anchored slices of REDUCED+MONO", [M for M in enum(4,2) if monoT(M) and Rd(M)==M], anchored=True)
    run("anchored slices of STANDARD", gen_standard(), anchored=True)

if __name__=="__main__": main()
