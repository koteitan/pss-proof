#!/usr/bin/env python3
"""r34-WIRECF: Task1 raw=Red on condIV regime; also condIII for comparison."""
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

def oper_orbit(cap, maxlen):
    seen=set(); frontier=[]
    for u in range(0,4):
        for v in range(u,u+4):
            d=tuple(R.diagSeq(u,v)); seen.add(d); frontier.append(list(d))
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

def test_host(M, st):
    j1=R.Lng(M)-1
    if not (1<j1): return
    if not R.hasParent(M,1,j1): return
    isIII=condIII(M); isIV=condIV(M)
    if not (isIII or isIV): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    if d<=0: return   # guard jm3<jm2
    reg='III' if isIII else 'IV'
    N=R.seg(M,jm3,j1)          # s84x_N M = seg M jm3 (Lng M -1)
    try: RN=R.Red(N)
    except Exception: return
    st[reg+'_guard']+=1
    # dd = entry M 0 jm3 - entry M 1 jm3 ; raw=Red iff dd==0 iff RN==N
    dd=R.entry(M,0,jm3)-R.entry(M,1,jm3)
    rawEQred = (RN==N)
    st[reg+'_dd0' if dd==0 else reg+'_ddpos']+=1
    if rawEQred: st[reg+'_rawEQred']+=1
    else:
        st[reg+'_rawNEred']+=1
        if len(st[reg+'_ne_ex'])<8:
            st[reg+'_ne_ex'].append((R.fmt(M),'dd=%d'%dd,'jm3=%d'%jm3,'jm2=%d'%jm2,reg))
    # consistency: dd==0 <=> raw==Red ?
    if (dd==0)!=rawEQred:
        st['dd_mismatch']+=1
        if len(st['dd_ex'])<8: st['dd_ex'].append((R.fmt(M),dd,rawEQred))

def main():
    keys=[]
    for reg in ['III','IV']:
        keys+= [reg+'_guard',reg+'_dd0',reg+'_ddpos',reg+'_rawEQred',reg+'_rawNEred']
    keys+=['dd_mismatch']
    st={k:0 for k in keys}
    st['III_ne_ex']=[]; st['IV_ne_ex']=[]; st['dd_ex']=[]
    print("building orbit...", flush=True)
    orbit=oper_orbit(30000, 14)
    print("orbit size", len(orbit), flush=True)
    std=0
    for M in orbit:
        try:
            if R.is_standard(M): std+=1; test_host(M,st)
        except Exception: pass
    print("standard hosts scanned:", std)
    for reg in ['III','IV']:
        print("--- cond%s (guard jm3<jm2) ---"%reg)
        print("  guarded hosts:", st[reg+'_guard'])
        print("  dd==0:",st[reg+'_dd0']," dd>0:",st[reg+'_ddpos'])
        print("  raw==Red:",st[reg+'_rawEQred']," raw!=Red:",st[reg+'_rawNEred'])
        if st[reg+'_ne_ex']: print("  raw!=Red ex:", st[reg+'_ne_ex'])
    print("dd==0 <=> raw==Red mismatch:", st['dd_mismatch'], st['dd_ex'])

if __name__=='__main__': main()
