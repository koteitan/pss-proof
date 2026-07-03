#!/usr/bin/env python3
r"""r27-CONDIVII: DIRECTLY validate the c4cx_condIV_exchange_full `mnform` residual
(the remaining condIV obligation feeding conclusions (1)/(3)):

  flatBT(Trans(M[m]))
     = s1 @ [D_e3] @ concat(rep (m-1) (s0@[D_ub])) @ flatBT(transT2 M)
              @ concat(rep (m-1) b0) @ b1                       (ub = v1-1)

with e3 = entry M 1 (s84x_jm3 M), v1 = entry M 1 (Lng M-1), t2 = transT2 M,
(s1,b1) the scb pair of Trans M at the jm3 principal D_e3(body), (s0,b0) the scb
pair of body at the innermost D_v1 0 hole.

Also cross-checks the PROVEN jm1-form (m_8_4_various_scb_IIIV_from_slice):
  flatBT(Trans(M[m]))
     = s84x_s1 @ [D_e1jm1] @ concat(rep(m-1)(fst sb@[D_e1jm2])) @ flatBT t2
              @ concat(rep(m-1)(snd sb)) @ s84x_b1
  e1jm1 = entry M 1 (transJm1 M), e1jm2 = entry M 1 (s84x_jm2 M).
The point: the jm1-form is a THEOREM.  Question = does the jm3-form (single-letter
ub=v1-1 d4vx_core) ALSO reproduce it, or does the jm3-decomposition need a NESTED
tower (as the c4vx caveat says: rightmost jm3 principal is a nested D_v)?
Uses r19's proven condIV-finding generator; DEEP Lng>=9 + brute straddle.
"""
import sys, os, time, signal, itertools, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper,
                       hasParent, seg, fmt)
from trans_model import (adm, Adm, ZB, Dpt, addBT, flatBT, flatBP, bpHeadV,
                         bpHeadT, PB, SigmaB, _c2, Pred, scb_decomps)

_TC, _MC, _RC, _rc = {}, {}, {}, {}
_T0, _M0, _R0, _r0 = tm.Trans, tm.Mark, rm.Red, tm.reduced
def Trans(M, d=0):
    k=tuple(M)
    if k not in _TC: _TC[k]=_T0(M,d)
    return _TC[k]
def Mark(M,m,d=0):
    k=(tuple(M),m)
    if k not in _MC: _MC[k]=_M0(M,m,d)
    return _MC[k]
def Red(M,d=0):
    k=tuple(M)
    if k not in _RC: _RC[k]=_R0(M,d)
    return _RC[k]
def reduced(M):
    k=tuple(M)
    if k not in _rc: _rc[k]=_r0(M)
    return _rc[k]
tm.Trans, tm.Mark, rm.Red, tm.reduced = Trans, Mark, Red, reduced

def pr(*a): print(*a, flush=True)
class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s,f: (_ for _ in ()).throw(TO()))

def condIV(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    if jp is None: return False
    return entry(M,1,j1)>0 and entry(M,1,jp)>=entry(M,1,j1) and not adm(M,jp)

def transJm1(M): return Adm(M, parent(M,0,Lng(M)-1))
def transT2(M): return bpHeadT(Mark(Pred(M), transJm1(M)))
def s84x_jm2(M): return parent(M,1,Lng(M)-1)
def s84x_jm3(M): return Adm(M, s84x_jm2(M))

def all_principals(t):
    out=[]
    for p in t[1]:
        out.append(p); out+=all_principals(p[2])
    return out

def cat(chunks): return list(itertools.chain.from_iterable(chunks))

def find_letter_decomp(TM, head, blockletter, v1):
    """principal D_head(body) in TM, body decomposes at D_v1 0; return
       list of (s1,b1,s0,b0) with block letter unused here (kept for parity)."""
    out=[]
    for p in all_principals(TM):
        if p[1]!=head: continue
        body=p[2]
        d1=scb_decomps(TM, flatBP(p))
        if not d1: continue
        d0=scb_decomps(body,[('D',v1),'Z'])
        if not d0: continue
        for (s1,b1) in d1:
            for (s0,b0) in d0:
                out.append((s1,b1,s0,b0))
    return out

def mnform_ok(cands, e3, ub, t2, lhs):
    for (s1,b1,s0,b0) in cands:
        good=True
        for (m,fL) in lhs:
            k=m-1
            rhs=(s1+[('D',e3)]+cat([s0+[('D',ub)] for _ in range(k)])
                 +flatBT(t2)+cat([b0 for _ in range(k)])+b1)
            if rhs!=fL: good=False; break
        if good: return True
    return False

def check_host(M, maxm, R):
    j1=Lng(M)-1
    v1=entry(M,1,j1); ub=v1-1
    jm3=s84x_jm3(M)
    if jm3 is None: return
    e3=entry(M,1,jm3)
    e1jm1=entry(M,1,transJm1(M))
    e1jm2=entry(M,1,s84x_jm2(M))
    t2=transT2(M)
    TM=Trans(M)
    # jm3 kind-1 candidates: principal D_e3(body), body decomposes at D_v1 0
    cands=[]
    for p in all_principals(TM):
        if p[1]!=e3: continue
        body=p[2]
        d1=scb_decomps(TM, flatBP(p))
        if not d1: continue
        d0=scb_decomps(body,[('D',v1),'Z'])
        if not d0: continue
        for (s1,b1) in d1:
            for (s0,b0) in d0:
                cands.append((s1,b1,s0,b0))
    R['hosts']+=1
    deep=Lng(M)>=9
    if deep: R['deep']+=1
    lhs=[]
    for m in range(1,maxm+1):
        Mm=oper(M,m)
        if Lng(Mm)>30: break
        try: lhs.append((m, flatBT(Trans(Mm))))
        except Exception: break
    if len(lhs)<2:
        R['short']+=1; return
    # admeq gate (the condIV route assumption: Adm M (s84x_jm2 M) = transJm1 M)
    admeq = (s84x_jm3(M) == transJm1(M))
    if admeq: R['admeq']+=1
    # diagnostics: relation of heads/block letters
    if e3==e1jm1: R['e3_eq_e1jm1']+=1
    if e1jm2==ub: R['e1jm2_eq_ub']+=1
    # ---- jm3 single-letter mnform (c4cx, head e3, block ub) ----
    uvok = (e3 < v1)
    if not uvok: R['uv_fail']+=1
    any_ok = mnform_ok(cands, e3, ub, t2, lhs) if (cands and uvok) else False
    R['mnform'].rec(any_ok,(fmt(M),))
    if deep: R['mnform_deep'].rec(any_ok,(fmt(M),))
    if admeq:
        R['mnform_admeq'].rec(any_ok,(fmt(M),))
        if deep: R['mnform_admeq_deep'].rec(any_ok,(fmt(M),))
    # ---- jm1-form (head e1jm1, block e1jm2, PROVEN via m_8_4_various...) ----
    cands1=find_letter_decomp(TM, e1jm1, e1jm2, v1)
    jm1_ok = mnform_ok(cands1, e1jm1, e1jm2, t2, lhs) if cands1 else False
    R['jm1form'].rec(jm1_ok,(fmt(M),))
    if deep: R['jm1form_deep'].rec(jm1_ok,(fmt(M),))
    if not any_ok and len(R['cex'])<8 and cands and uvok:
        s1,b1,s0,b0=cands[0]
        perm=[]
        for (m,fL) in lhs:
            k=m-1
            rhs=(s1+[('D',e3)]+cat([s0+[('D',ub)] for _ in range(k)])
                 +flatBT(t2)+cat([b0 for _ in range(k)])+b1)
            perm.append((m, rhs==fL))
        R['cex'].append((fmt(M),'e3',e3,'e1jm1',e1jm1,'v1',v1,'jm1ok',jm1_ok,perm))

class St:
    def __init__(s): s.ok=0; s.bad=0; s.cex=[]
    def rec(s,g,i):
        if g: s.ok+=1
        else:
            s.bad+=1
            if len(s.cex)<6: s.cex.append(i)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

def gen_oper(max_len, cap, seed, ns, umax, vextra):
    rng=random.Random(seed); seen=set(); out=[]; work=[]
    for u in range(0,umax+1):
        for v in range(u,u+vextra):
            work.append(diagSeq(u,v))
    while work and len(out)<cap:
        i=rng.randrange(len(work)); M=work.pop(i); k=tuple(M)
        if k in seen: continue
        seen.add(k); out.append(M)
        if Lng(M)>max_len: continue
        for n in ns:
            Mn=oper(M,n)
            if Lng(Mn)<=max_len+3 and tuple(Mn) not in seen: work.append(Mn)
    return out

def gen_straddle(maxlen, cap, seed):
    rng=random.Random(seed); out=[]; seen=set(); stack=[[(0,0)]]; steps=0
    while stack and len(out)<cap:
        steps+=1
        if steps>300000: break
        M=stack.pop(); L=Lng(M)
        if L>=4 and reduced(M) and monoT(M) and not zeroT(M) \
           and hasParent(M,1,L-1) and condIV(M):
            t=tuple(M)
            if t not in seen: seen.add(t); out.append(M)
        if L>=maxlen: continue
        prevmax0=max((p[0] for p in M), default=0)
        cands=[]
        for a in range(0, min(prevmax0+2, L+1)+1):
            for b in range(0, a+1):
                Mn=M+[(a,b)]
                if reduced(Mn): cands.append(Mn)
        rng.shuffle(cands)
        for Mn in cands[:6]: stack.append(Mn)
    return out

def run(pool, tag, R, budget):
    t0=time.time(); nh=0
    for M in pool:
        if time.time()-t0>budget: break
        j1=Lng(M)-1
        if j1<=1 or not monoT(M) or zeroT(M) or not hasParent(M,1,j1): continue
        if not condIV(M): continue
        nh+=1
        signal.alarm(20)
        try: check_host(M,4,R)
        except (TO,RecursionError,ValueError,IndexError,AssertionError): R['to']+=1
        finally: signal.alarm(0)
    pr(f'[{tag}] pool={len(pool)} condIV={nh} ({time.time()-t0:.0f}s)')

def main():
    t0=time.time()
    R={'hosts':0,'deep':0,'admeq':0,'uv_fail':0,'short':0,'to':0,
       'e3_eq_e1jm1':0,'e1jm2_eq_ub':0,
       'mnform':St(),'mnform_deep':St(),'mnform_admeq':St(),'mnform_admeq_deep':St(),
       'jm1form':St(),'jm1form_deep':St(),'cex':[]}
    # r19-style generators (proven to find condIV hosts); oper-only for speed,
    # plus one quick straddle pool for off-orbit coverage
    for seed,mlen,cap,ns,um,vx,bud in (
            (202,16,4000,(1,2),2,7,45),
            (303,18,4000,(1,2),2,8,45),
            (505,20,5000,(1,2),3,9,45),
            (707,22,6000,(1,2),4,9,45),
            (811,24,6000,(1,2,3),4,10,50),
            (913,26,6000,(1,2),5,10,50)):
        run(gen_oper(mlen,cap,seed,ns,um,vx), f'oper s{seed}', R, bud)
    pr()
    pr(f'hosts={R["hosts"]}  deep(>=9)={R["deep"]}  admeq={R["admeq"]}  short={R["short"]}  '
       f'uv_fail={R["uv_fail"]}  timeouts={R["to"]}')
    pr(f'e3==e1jm1: {R["e3_eq_e1jm1"]}/{R["hosts"]}   e1jm2==ub(v1-1): {R["e1jm2_eq_ub"]}/{R["hosts"]}')
    pr(f'MNFORM jm3 single-letter (all)        : {R["mnform"]}')
    pr(f'MNFORM jm3 single-letter (deep)       : {R["mnform_deep"]}')
    pr(f'MNFORM jm3 single-letter (ADMEQ only) : {R["mnform_admeq"]}   <-- the c4cx route gate')
    pr(f'MNFORM jm3 single-letter (ADMEQ deep) : {R["mnform_admeq_deep"]}')
    pr(f'jm1-form (all)   : {R["jm1form"]}')
    pr(f'jm1-form (deep)  : {R["jm1form_deep"]}')
    pr(f'elapsed {time.time()-t0:.1f}s')
    if R['cex']:
        pr('--- jm3 mnform CEX (host,e3,v1,ncand,per-m ok) ---')
        for c in R['cex']: pr('  ',c)

if __name__=='__main__': main()
