#!/usr/bin/env python3
"""r33 MCOND / M0RUN empirical validation (verify-rank-depth: deep + straddle).

Targets:
 (1) MCOND on RN = Red(s84x_N M) under guard d>0 (condIII REGS).
 (2) MCOND on RN' = Red(Pred(s84x_N M)) under Br(RN')<>[] (shared REGSP).
 (3) M0RUN single ineq: under guard d==0 (jm2 admissible),
       entry M 1 jm2 < entry M 1 (jm2+1).
Genuine regime = standard host (yaBMS oracle) with hasParent M 1 (Lng-1),
1<Lng-1, transCondIII or transCondIV.
"""
import sys, itertools
sys.path.insert(0, 'python')
import red_model as R

def parent0(M,j): return R.parent(M,0,j)
def condIII(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=parent0(M,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and R.adm(M,j0)
def condIV(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=parent0(M,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and (not R.adm(M,j0))

def s84(M):
    j1=R.Lng(M)-1
    jm2=R.parent(M,1,j1)
    if jm2 is None: return None
    jm3=R.Adm(M,jm2)
    return jm2,jm3

def mcond_on(RN,d):
    """returns (well_defined, holds, kind) for cfbx-style MCOND on reduced RN."""
    b=R.Br(RN)
    if len(b)==0: return (False,None,'Br=[]')
    last=len(b)-1
    jl=R.Joints(RN)[last]
    fn=R.FirstNodes(RN)[last]
    if fn>=R.Lng(RN): return (False,None,'fn oob')
    diag = R.entry(RN,0,fn)==R.entry(RN,1,fn)
    if d<jl: return (True,True,'d<jl')
    if d==jl and diag: return (True,True,'d=jl&diag')
    if d==jl and not diag: return (True,False,'d=jl&NOTdiag')
    return (True,False,'d>jl')  # violation

def test_host(M, stats):
    if R.Lng(M)<3: return
    j1=R.Lng(M)-1
    if not (1 < j1): return
    if not R.hasParent(M,1,j1): return
    isIII=condIII(M); isIV=condIV(M)
    if not (isIII or isIV): return
    sp=s84(M)
    if sp is None: return
    jm2,jm3=sp
    d=jm2-jm3
    N=R.seg(M,jm3,j1)
    try:
        RN=R.Red(N)
    except Exception:
        return
    reg='III' if isIII else 'IV'
    stats['hosts']+=1
    # (1) REGS: guard d>0
    if d>0:
        wd,hold,kind=mcond_on(RN,d)
        stats['regs_total']+=1
        if not wd:
            stats['regs_Bremp']+=1
            stats['regs_Bremp_ex'].append((R.fmt(M),kind))
        elif hold:
            stats['regs_ok']+=1
            stats['regs_kind'][kind]=stats['regs_kind'].get(kind,0)+1
        else:
            stats['regs_fail']+=1
            stats['regs_fail_ex'].append((R.fmt(M),d,kind,reg))
    # (3) M0RUN: guard d==0 (jm2 admissible)
    if d==0:
        stats['m0_total']+=1
        e_jm2=R.entry(M,1,jm2)
        if jm2+1<R.Lng(M):
            e_next=R.entry(M,1,jm2+1)
            if e_jm2<e_next: stats['m0_ok']+=1
            else:
                stats['m0_fail']+=1
                stats['m0_fail_ex'].append((R.fmt(M),jm2,e_jm2,e_next,reg))
        else:
            stats['m0_oob']+=1
    # (2) REGSP on RN' = Red(Pred N) = Red(seg M jm3 (Lng-2))
    if j1-1>=jm3:
        Np=R.seg(M,jm3,j1-1)
        try:
            RNp=R.Red(Np)
        except Exception:
            RNp=None
        if RNp is not None and len(R.Br(RNp))>0:
            stats['regsp_total']+=1
            wd,hold,kind=mcond_on(RNp,d)
            if hold:
                stats['regsp_ok']+=1
                stats['regsp_kind'][kind]=stats['regsp_kind'].get(kind,0)+1
            else:
                stats['regsp_fail']+=1
                stats['regsp_fail_ex'].append((R.fmt(M),d,kind,reg))

def oper_orbit(cap, maxlen):
    """BFS oper-orbit from diagSeqs (ST_PS by construction)."""
    seen=set(); frontier=[]
    for u in range(0,3):
        for v in range(u,u+4):
            d=tuple(R.diagSeq(u,v))
            if d not in seen: seen.add(d); frontier.append(list(d))
    out=[]
    while frontier and len(seen)<cap:
        M=frontier.pop(0)
        out.append(M)
        if R.Lng(M)>=maxlen: continue
        for n in range(1,4):
            try:
                Mn=R.oper(M,n)
            except Exception:
                continue
            t=tuple(Mn)
            if t not in seen and R.Lng(Mn)<=maxlen:
                seen.add(t); frontier.append(Mn)
    return out

def brute_straddle(maxlen, vcap):
    """brute-force short pairseqs filtered by yaBMS standardness."""
    out=[]
    for L in range(3,maxlen+1):
        # columns (a,b) with 0<=b<=a<=vcap, plus first col (0,0)
        cols=[(a,b) for a in range(0,vcap+1) for b in range(0,a+1)]
        # too big to enumerate fully; sample diag-ramp-ish prefixes
        # build sequences starting from diagonal then perturb tail
        base=R.diagSeq(0,L-2)
        for tail in cols:
            M=base+[tail]
            if R.is_standard(M): out.append(M)
    return out

def main():
    stats=dict(hosts=0,
        regs_total=0,regs_ok=0,regs_fail=0,regs_Bremp=0,
        regs_kind={},regs_fail_ex=[],regs_Bremp_ex=[],
        m0_total=0,m0_ok=0,m0_fail=0,m0_oob=0,m0_fail_ex=[],
        regsp_total=0,regsp_ok=0,regsp_fail=0,regsp_kind={},regsp_fail_ex=[])
    print("=== oper-orbit corpus (cap 30000, maxlen 13) ===", flush=True)
    orbit=oper_orbit(30000, 13)
    print("orbit size", len(orbit), flush=True)
    std=0
    for M in orbit:
        try:
            if R.is_standard(M):
                std+=1; test_host(M, stats)
        except Exception:
            pass
    print("standard in orbit:", std, flush=True)
    print("=== brute straddle (maxlen 11, vcap 6) ===", flush=True)
    for M in brute_straddle(11,6):
        test_host(M, stats)
    print("\n--- RESULTS ---")
    print("hosts (genuine III/IV):", stats['hosts'])
    print("REGS(d>0): total",stats['regs_total'],"ok",stats['regs_ok'],
          "fail",stats['regs_fail'],"Br=[]",stats['regs_Bremp'])
    print("  REGS kinds:", stats['regs_kind'])
    if stats['regs_fail_ex']: print("  REGS FAIL ex:", stats['regs_fail_ex'][:8])
    if stats['regs_Bremp_ex']: print("  REGS Br=[] ex:", stats['regs_Bremp_ex'][:8])
    print("REGSP(Br<>[]): total",stats['regsp_total'],"ok",stats['regsp_ok'],
          "fail",stats['regsp_fail'])
    print("  REGSP kinds:", stats['regsp_kind'])
    if stats['regsp_fail_ex']: print("  REGSP FAIL ex:", stats['regsp_fail_ex'][:8])
    print("M0RUN(d=0): total",stats['m0_total'],"ok",stats['m0_ok'],
          "fail",stats['m0_fail'],"oob",stats['m0_oob'])
    if stats['m0_fail_ex']: print("  M0RUN FAIL ex:", stats['m0_fail_ex'][:8])

if __name__=='__main__':
    main()
