import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import Lng, entry, parent, oper, fmt
from trans_model import (Trans, Mark, Pred, ZB, Dpt, addBT, PB, bpHeadV, bpHeadT,
                         flatBT, unflatBT, scb_decomps, Adm, condI, condIII, condV, condVI,
                         monoT, reduced)
from _ez_A_fast import build_closure

def trans_accessors(M):
    j1 = Lng(M)-1
    if j1 <= 0: return None
    if not monoT(M): return None
    P = Pred(M)
    t1 = Trans(P)
    if t1 == ZB: return None
    jp = parent(M,0,j1)
    jm1 = Adm(M, jp)
    c1 = Mark(P, jm1)
    v = entry(M,1,j1); t2 = bpHeadT(c1)
    u = entry(M,1,jm1)
    return dict(j1=j1,jp=jp,jm1=jm1,t1=t1,c1=c1,v=v,t2=t2,u=u)

def OWmaker(s1,u,b1):
    return lambda x: unflatBT(s1 + [('D',u)] + flatBT(x) + b1)
def Cmaker(s0,vm1,b0):
    return lambda x: unflatBT(s0 + [('D',vm1)] + flatBT(x) + b0)

def funpow(f,k,x):
    for _ in range(k): x=f(x)
    return x

def check(M):
    # only condV/condIII case-A monotone hosts with t1!=0
    if Lng(M)<2: return None
    a = trans_accessors(M)
    if a is None: return None
    if not condV(M): return None
    u=a['u']; v=a['v']; t2=a['t2']; t1=a['t1']; c1=a['c1']
    # scb of t1 at c1
    ds1 = scb_decomps(t1, flatBT(c1))
    if not ds1: return None
    s1,b1 = ds1[0]
    body = addBT(t2, Dpt(v, ZB))
    ds0 = scb_decomps(body, flatBT(Dpt(v,ZB)))
    if not ds0: return None
    s0,b0 = ds0[0]
    OW = OWmaker(s1,u,b1)
    C = Cmaker(s0,v-1,b0)
    # n=1 base: Trans(M[1]) == OW(t2)
    n1 = (Trans(oper(M,1)) == OW(t2))
    # find k in {1,2} for base2: Trans(M[2]) == OW(C^k(t2))
    T2 = Trans(oper(M,2))
    kfound = None
    for k in (1,2,3):
        if OW(funpow(C,k,t2)) == T2:
            kfound = k; break
    # step2: for p>=2 up to 5: Trans(M[p+1]) == OW(C(b)) where Trans(M[p])==OW(b)
    step_ok = True; step_cnt=0
    for p in range(2,4):
        Tp = Trans(oper(M,p))
        Tp1 = Trans(oper(M,p+1))
        # invert OW: Tp should be OW(b). Derive b from closed form: b = C^(kfound+(p-2))(t2)
        if kfound is None: break
        b = funpow(C, kfound+(p-2), t2)
        if OW(b) != Tp:
            step_ok=False; break
        if OW(C(b)) != Tp1:
            step_ok=False; break
        step_cnt+=1
    cond = 'V' if condV(M) else 'III'
    return dict(M=fmt(M),cond=cond,n1=n1,k=kfound,step_ok=step_ok,step_cnt=step_cnt)

if __name__=='__main__':
    Ms = build_closure(depth_max=3, ubound=2, vbound=4, maxlen=8)
    res=[]
    for M in Ms:
        try:
            r = check(M)
        except Exception as e:
            r = None
        if r: res.append(r)
    n1f=[r for r in res if not r['n1']]
    kbad=[r for r in res if r['k'] is None]
    stepbad=[r for r in res if not r['step_ok']]
    kvals={}
    for r in res:
        kvals.setdefault((r['cond'],r['k']),0); kvals[(r['cond'],r['k'])]+=1
    print('total condIII/V case-A hosts:', len(res))
    print('n1 base fail:', len(n1f))
    print('k-not-found:', len(kbad))
    print('step2 fail:', len(stepbad))
    print('k distribution (cond,k):', kvals)
    for r in stepbad[:6]: print('  STEPBAD', r)
    for r in n1f[:6]: print('  N1BAD', r)
    for r in kbad[:6]: print('  KBAD', r)
