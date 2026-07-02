import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, entry, parent, oper, fmt, monoT, reduced
from trans_model import (Trans, Mark, Pred, ZB, Dpt, addBT, bpHeadV, bpHeadT,
                         flatBT, unflatBT, scb_decomps, Adm, condV)

def funpow(f,k,x):
    for _ in range(k): x=f(x)
    return x

def gen_condV(maxlen=5, maxval=3, cap=25):
    out=[]
    # build sequences columnwise with row0 nondecreasing diag-ish
    cols=[(a,b) for a in range(0,maxval+1) for b in range(0,maxval+1)]
    # seed with prefixes that look like standard ST_PS: start (0,0)
    import random
    random.seed(1)
    seen=set()
    # random search
    for _ in range(8000):
        L=random.randint(3,maxlen)
        M=[(0,0)]
        ok=True
        for j in range(1,L):
            a=random.randint(0,maxval); b=random.randint(0,maxval)
            M.append((a,b))
        key=tuple(M)
        if key in seen: continue
        seen.add(key)
        try:
            if not reduced(M): continue
            if not monoT(M): continue
            if not condV(M): continue
            if Trans(Pred(M))==ZB: continue
            out.append(M)
        except Exception:
            continue
        if len(out)>=cap: break
    return out

def check(M):
    j1=Lng(M)-1; P=Pred(M); t1=Trans(P)
    if t1==ZB: return None
    jp=parent(M,0,j1); jm1=Adm(M,jp); c1=Mark(P,jm1)
    v=entry(M,1,j1); t2=bpHeadT(c1); u=entry(M,1,jm1)
    ds1=scb_decomps(t1,flatBT(c1)); body=addBT(t2,Dpt(v,ZB))
    ds0=scb_decomps(body,flatBT(Dpt(v,ZB)))
    if not ds1 or not ds0: return None
    s1,b1=ds1[0]; s0,b0=ds0[-1]   # trailing leaf
    OW=lambda x: unflatBT(s1+[('D',u)]+flatBT(x)+b1)
    C=lambda x: unflatBT(s0+[('D',v-1)]+flatBT(x)+b0)
    n1=(Trans(oper(M,1))==OW(t2))
    T2=Trans(oper(M,2)); k=None
    for kk in (1,2,3,4):
        try:
            if OW(funpow(C,kk,t2))==T2: k=kk; break
        except Exception: pass
    steps=True; sc=0
    if k is not None:
        for p in range(2,4):
            try:
                b=funpow(C,k+(p-2),t2)
                if OW(b)!=Trans(oper(M,p)): steps=False; break
                if OW(C(b))!=Trans(oper(M,p+1)): steps=False; break
                sc+=1
            except Exception: steps=False; break
    return dict(M=fmt(M),n1=n1,k=k,steps=steps,sc=sc)

if __name__=='__main__':
    Ms=gen_condV()
    res=[r for M in Ms if (r:=check(M))]
    print('condV case-A hosts:',len(res))
    print('n1 fail:',sum(1 for r in res if not r['n1']))
    print('k-none:',sum(1 for r in res if r['k'] is None))
    print('step fail (k found):',sum(1 for r in res if r['k'] is not None and not r['steps']))
    from collections import Counter
    print('k dist:',Counter(r['k'] for r in res))
    for r in res:
        if (r['k'] is None) or (not r['n1']) or (r['k'] is not None and not r['steps']):
            print('  BAD',r)
