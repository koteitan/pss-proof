#!/usr/bin/env python3
"""Probe the d==jl equality (diag) case mechanism for MCOND."""
import sys
sys.path.insert(0, 'python')
import red_model as R

def condIII(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and R.adm(M,j0)
def condIV(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and (not R.adm(M,j0))

def analyze(RN, tag, examples, d):
    """for reduced RN, at equality d==jl: examine last-branch first node f."""
    b=R.Br(RN)
    if len(b)==0: return
    last=len(b)-1; jl=R.Joints(RN)[last]; fn=R.FirstNodes(RN)[last]
    if d!=jl: return
    # equality case
    diag=(R.entry(RN,0,fn)==R.entry(RN,1,fn))
    # is last branch a singleton?
    singleton = (fn==R.Lng(RN)-1)
    # does f have a row-1 parent?
    hasP1 = R.hasParent(RN,1,fn)
    # row-1 parent value / RedCondA style
    if len(examples)<10:
        examples.append(dict(RN=R.fmt(RN),d=d,jl=jl,fn=fn,LngRN=R.Lng(RN),
            diag=diag,singleton=singleton,hasP1=hasP1,
            e0f=R.entry(RN,0,fn),e1f=R.entry(RN,1,fn),tag=tag))

def test_host(M, exREGS, exREGSP):
    j1=R.Lng(M)-1
    if not (1<j1): return
    if not R.hasParent(M,1,j1): return
    if not (condIII(M) or condIV(M)): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    if d>0:
        try: RN=R.Red(R.seg(M,jm3,j1))
        except Exception: RN=None
        if RN is not None: analyze(RN,'REGS',exREGS,d)
    if d>0 and j1-1>jm3:
        try: RNp=R.Red(R.seg(M,jm3,j1-1))
        except Exception: RNp=None
        if RNp is not None: analyze(RNp,'REGSP',exREGSP,d)

def oper_orbit(cap, maxlen):
    seen=set(); frontier=[]
    for u in range(0,4):
        for v in range(u,u+5):
            dd=tuple(R.diagSeq(u,v)); seen.add(dd); frontier.append(list(dd))
    out=[]
    while frontier and len(out)<cap:
        M=frontier.pop(0); out.append(M)
        if R.Lng(M)>=maxlen: continue
        for n in range(1,4):
            try: Mn=R.oper(M,n)
            except Exception: continue
            t=tuple(Mn)
            if t not in seen and R.Lng(Mn)<=maxlen:
                seen.add(t); frontier.append(Mn)
    return out

def main():
    exREGS=[]; exREGSP=[]
    for M in oper_orbit(8000, 13):
        try:
            if R.is_standard(M): test_host(M, exREGS, exREGSP)
        except Exception: pass
    print("=== REGS equality (d==jl) examples ===")
    for e in exREGS: print(e)
    print("=== REGSP equality (d==jl) examples ===")
    for e in exREGSP: print(e)
    # aggregate: in equality cases, is it ALWAYS diag? singleton? hasP1?
    for name,ex in [('REGS',exREGS),('REGSP',exREGSP)]:
        if ex:
            print(f"{name}: all diag?", all(e['diag'] for e in ex),
                  "all singleton?", all(e['singleton'] for e in ex),
                  "any hasP1?", any(e['hasP1'] for e in ex),
                  "all NOT hasP1?", all(not e['hasP1'] for e in ex))

if __name__=='__main__': main()
