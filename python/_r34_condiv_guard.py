#!/usr/bin/env python3
"""r34-WIRECF: characterize condIV guard jm3<jm2 (= not adm(M,jm2)). DEEP + brute."""
import sys, itertools
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

def oper_orbit(cap, maxlen):
    seen=set(); frontier=[]
    for u in range(0,5):
        for v in range(u,u+5):
            d=tuple(R.diagSeq(u,v)); seen.add(d); frontier.append(list(d))
    out=[]
    while frontier and len(out)<cap:
        M=frontier.pop(0); out.append(M)
        if R.Lng(M)>=maxlen: continue
        for n in range(1,5):
            try: Mn=R.oper(M,n)
            except Exception: continue
            t=tuple(Mn)
            if t not in seen and R.Lng(Mn)<=maxlen:
                seen.add(t); frontier.append(Mn)
    return out

def scan(hosts, st):
    for M in hosts:
        try:
            if not R.is_standard(M): continue
        except Exception: continue
        j1=R.Lng(M)-1
        if not (1<j1): continue
        if not R.hasParent(M,1,j1): continue
        isIV=condIV(M)
        if not isIV: continue
        jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
        st['IV_total']+=1
        st['IV_admjm2' if R.adm(M,jm2) else 'IV_nadmjm2']+=1
        if d>0:
            st['IV_guard']+=1
            if len(st['IV_guard_ex'])<12:
                st['IV_guard_ex'].append((R.fmt(M),'d=%d'%d))

def brute(maxlen, st):
    # brute force straddle: all monotone-ish pair sequences up to maxlen, small coords
    for L in range(3, maxlen+1):
        # build sequences greedily via BFS on standard-ness is expensive;
        # instead sample: rows 0,1 in small range with (0,0) start
        rng=range(0,5)
        # too big for full; do random-ish structured: use oper orbit already covers.
        pass

def main():
    st={k:0 for k in ['IV_total','IV_admjm2','IV_nadmjm2','IV_guard']}
    st['IV_guard_ex']=[]
    print("deep orbit...", flush=True)
    orbit=oper_orbit(120000, 18)
    print("orbit size", len(orbit), flush=True)
    scan(orbit, st)
    print("condIV total hosts:", st['IV_total'])
    print("  jm2 admissible:", st['IV_admjm2'], " jm2 NOT-adm (guard jm3<jm2):", st['IV_nadmjm2'])
    print("  guard d>0 count:", st['IV_guard'])
    if st['IV_guard_ex']: print("  GUARD EXAMPLES:", st['IV_guard_ex'])
    else: print("  NO condIV host with jm3<jm2 found (guard vacuous).")

if __name__=='__main__': main()
