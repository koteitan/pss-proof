#!/usr/bin/env python3
r"""r19-CONDIV: validate the §8.4 condition-(IV) exchange DESCENT (conclusion 2)
and the shared jm1-decomposition core shapes, on GENUINE deep (Lng>=9) condIV
hosts.  condIV: v1>0, M_{1,j0} >= M_{1,j1}, NOT adm(M,j0).  (condIII is the same
with adm(M,j0).)

Claims validated (per condIV host M, n in 1..2):
  (A) M[n] closed form (shared with condIII):
        flatBT(Trans(M[n])) = s1 @ flatBP(DB v_hd (e3x_H jm2 t2 (n-1))) @ b1
      where (s1,b1) = the scb pair of Trans M at transC2 M, v_hd=bpHeadV(transC2 M),
      t2 = transT2 M = bpHeadT(transC1 M), jm2 = entry M 1 (parent M 1 (Lng M-1)),
      e3x_H tower: H_0=t2, H_{k+1}=t2 + D_{jm2}(H_k).
  (B) Trans M reads   flatBT(Trans M) = s1 @ flatBP(DB v_hd c2body) @ b1,
      c2body = bpHeadT(transC2 M)   [the condIV nested body].
  (C) tower descent:   lessBT (e3x_H jm2 t2 (n-1)) c2body.
  (D) overall descent: lessBT (Trans(M[n])) (Trans M).
  (E) order facts: jm2 < v1 <= u'   (u' = M_{1,j0}),  hence jm2 < u'.
  (F) c2body first-differ structure (the proof case split):
      t2==0  -> c2body = D_{u'}(D_{v1} 0);
      t2!=0 & leftDj0 -> shares prefix q1..q_{m-1}; pos m: (u',t4) vs (u',t4+D_v0);
      t2!=0 & !leftDj0-> shares prefix q1..q_m;  pos m: (jm2,..) vs (u', t2+D_v0).
"""
import sys, os, time, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import (Lng, entry, monoT, zeroT, diagSeq, parent, oper,
                       hasParent, seg, fmt)
from trans_model import (adm, Adm, ZB, Dpt, addBT, flatBT, flatBP, bpHeadV,
                         bpHeadT, PB, SigmaB, _c2, Pred)

# memoized model
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

# BT order (matches lessBT/lessBP of the model / Isabelle)
def lessBP(p,q): return p[1] < q[1] or (p[1]==q[1] and lessBT(p[2],q[2]))
def lessBT(a,b):
    ps,qs=a[1],b[1]
    if not ps: return bool(qs)
    if not qs: return False
    return lessBP(ps[0],qs[0]) or (ps[0]==qs[0] and lessBT(('T',ps[1:]),('T',qs[1:])))

def condIV(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return entry(M,1,j1)>0 and entry(M,1,jp)>=entry(M,1,j1) and not adm(M,jp)

def e3x_H(jm2, t2, k):
    if k==0: return t2
    return addBT(t2, Dpt(jm2, e3x_H(jm2,t2,k-1)))

def gen_pool(max_len, cap, seed, ns, umax, vextra):
    import random
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

def check(M, R):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    jm2col=parent(M,1,j1)
    jm2=entry(M,1,jm2col)
    v1=entry(M,1,j1); up=entry(M,1,jp)
    jm1=Adm(M,jp)
    c1=Mark(Pred(M), jm1)
    vhd=bpHeadV(c1); t2=bpHeadT(c1)
    c2=_c2(M,j1,jp,vhd,t2)
    c2body=bpHeadT(c2)
    TM=Trans(M)
    R['n']+=1
    # (E) order facts
    okE = (jm2 < v1) and (v1 <= up) and (jm2 < up)
    R['E'] = R['E'] and okE
    if not okE and len(R['cexE'])<4: R['cexE'].append((fmt(M), jm2, v1, up))
    # (B) Trans M wrapper: get (s1,b1) at transC2 M
    fc2 = flatBT(c2)
    fTM = flatBT(TM)
    # find s1,b1 s.t. fTM = s1 + fc2 + b1
    ds = tm.scb_decomps(TM, fc2)
    if not ds:
        R['noscb']+=1; return
    s1,b1 = ds[0]
    # (B) check Trans M reads as s1 @ flatBP(DB vhd c2body) @ b1
    okB = (fTM == s1 + flatBP(('D',vhd,c2body)) + b1)
    R['B'] = R['B'] and okB
    for n in (1,2):
        Mn=oper(M,n)
        if Lng(Mn) > 26: continue
        fMn=flatBT(Trans(Mn))
        H=e3x_H(jm2, t2, n-1)
        # (A) M[n] closed form in the shared wrapper
        okA = (fMn == s1 + flatBP(('D',vhd,H)) + b1)
        R['A'].rec(okA,(fmt(M),n))
        # (C) tower descent
        okC = lessBT(H, c2body)
        R['C'].rec(okC,(fmt(M),n,'H',H,'body',c2body))
        # (D) overall descent
        okD = lessBT(Trans(Mn), TM)
        R['D'].rec(okD,(fmt(M),n))
    # (F) c2body structure class
    if t2==ZB:
        R['F_t2z']+=1
    else:
        Pt2=PB(t2); J1b=len(Pt2)-1; pj=Pt2[J1b]
        leftDj0=(bpHeadV(pj)==up)
        R['F_left' if leftDj0 else 'F_noleft']+=1

class St:
    def __init__(s): s.ok=0; s.bad=0; s.cex=[]
    def rec(s,g,i):
        if g: s.ok+=1
        else:
            s.bad+=1
            if len(s.cex)<5: s.cex.append(i)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

def main():
    t0=time.time()
    R={'n':0,'A':St(),'C':St(),'D':St(),'B':True,'E':True,'cexE':[],
       'noscb':0,'F_t2z':0,'F_left':0,'F_noleft':0}
    nIV=nDeep=timeouts=0
    for seed,mlen,cap,ns,um,vx,bud in (
            (202,16,12000,(1,2),2,7,300),
            (303,18,12000,(1,2),2,8,300),
            (404,17,15000,(1,2,3),3,7,300),
            (505,20,15000,(1,2),3,9,300)):
        pool=gen_pool(mlen,cap,seed,ns,um,vx)
        tseg=time.time()
        for M in pool:
            if time.time()-tseg>bud: break
            j1=Lng(M)-1
            if j1<=1 or not monoT(M) or zeroT(M) or not hasParent(M,1,j1): continue
            if not condIV(M): continue
            nIV+=1
            deep = Lng(M)>=9
            if deep: nDeep+=1
            signal.alarm(20)
            try:
                check(M,R)
            except (TO,RecursionError): timeouts+=1
            except (ValueError,IndexError): timeouts+=1
            finally: signal.alarm(0)
        pr(f'[seed {seed}] pool {len(pool)} condIV {nIV} deep {nDeep} '
           f'timeouts {timeouts} ({time.time()-tseg:.0f}s)')
    pr()
    pr(f'condIV hosts checked (checks n): {R["n"]}   noscb={R["noscb"]}  timeouts={timeouts}')
    pr(f'(A) M[n] closed form  : {R["A"]}   cex={R["A"].cex[:2]}')
    pr(f'(B) Trans M wrapper   : {R["B"]}')
    pr(f'(C) tower descent H<b : {R["C"]}   cex={R["C"].cex[:2]}')
    pr(f'(D) overall descent   : {R["D"]}   cex={R["D"].cex[:2]}')
    pr(f'(E) order jm2<v<=u    : {R["E"]}   cex={R["cexE"][:3]}')
    pr(f'(F) c2body class      : t2==0:{R["F_t2z"]}  leftDj0:{R["F_left"]}  '
       f'!leftDj0:{R["F_noleft"]}')
    pr(f'elapsed {time.time()-t0:.1f}s')

if __name__=='__main__': main()
