import sys, os, itertools, functools, subprocess, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
from trans_model import (Trans,Mark,ZB,PB,bpHeadT,bpHeadV,addBT,Dpt,flatBT,
                          reduced as treduced,condV,condI,condIII,condVI,scb_decomps)
import trans_model as tm

"""§8.5 keystone ROUND 5 -- targeted characterization of the two remaining
m_8_5_anchor_col_trunkstuck hypotheses (R2b' = mJpcut, pcutle), restricted to
the keystone's OWN regime (transCondV(Mq) + hp1/parR/coin/jm1pos of
m_8_5_basepoint), at every trunk-stuck multiT fold column (n0 < Pcut(Nprev)).

Records, per trunk-stuck instance:
  - pcut = Pcut(Nprev)
  - jm1cur = transJm1(Ncur)  (None if no row-0 parent at all -- fresh branch reset)
  - pcutle = pcut <= jm1cur
  - R2bprime = marked(drop(pcut,Nprev), jm1cur-pcut)
  - structural diagnostics: m (column index within B), w=len(B), col=B[m],
    entry0(col), whether col opens ANOTHER reset (entry0(col)==0), Pcut(Nprev)
    vs the index m_open where the CURRENT branch opened (tracked separately).
"""

BMS='/home/koteitan/proofs/pss-proof/wt2/tmp/yaBMS/c/bms'
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"

def transJm1(M):
    p = parent(M,0,Lng(M)-1)
    if p is None: return None
    return tm.Adm(M, p)

def gen(maxlen=6,maxv=2):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(3,maxlen+1):
        for s in itertools.product(pairs,repeat=L):
            M=list(s)
            if M[0]!=(0,0): continue
            yield M

def main_sweep(timelimit=240, maxlen=6, maxv=2, qs=(2,3,4)):
    t0=time.time(); cnt=0; checked=0
    rows=[]
    for M in gen(maxlen,maxv):
        if time.time()-t0>timelimit: break
        try:
            if not (reduced(M) and is_std(tuple(M))): continue
        except Exception: continue
        cnt+=1
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>16: continue
                if not condV(Mq): continue
                if not hasParent(Mq,1,j1): continue
                p1=parent(Mq,1,j1); parR=nextrel0(Mq,p1,j1); p0=parent(Mq,0,j1)
                if not (parR and p1==p0): continue
                jm1=Adm(Mq,p0)
                if not (jm1>0): continue
                checked+=1
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]; w=len(B)
                if w<1: continue
                host=list(Mq)
                pcut_prev_seen = None
                for m in range(w):
                    Nprev = list(host)
                    col = B[m]
                    host=host+[col]
                    Ncur=list(host)
                    if not reduced(Ncur) or not reduced(Nprev): continue
                    if not multiT(Nprev): continue
                    pcut = Pcut(Nprev)
                    stuck = jm1 < pcut
                    if not stuck: continue
                    jm1cur = transJm1(Ncur)
                    PJ = Nprev[pcut:]
                    pcutle = None if jm1cur is None else (pcut <= jm1cur)
                    R2bprime = None
                    if jm1cur is not None and pcutle:
                        try:
                            R2bprime = marked(PJ, jm1cur-pcut)
                        except Exception:
                            R2bprime = None
                    rows.append(dict(M=tuple(M),q=q,m=m,w=w,col=col,
                                      pcut=pcut, jm1=jm1, jm1cur=jm1cur,
                                      pcutle=pcutle, R2bprime=R2bprime,
                                      entry0col=col[0], pcut_changed=(pcut!=pcut_prev_seen)))
                    pcut_prev_seen = pcut
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(360, 6, 2, (2,3,4))
    print(f"std&reduced scanned={cnt}, regime-checked={checked}, trunk-stuck rows={len(rows)}")
    from collections import Counter
    none_jm1cur = [r for r in rows if r['jm1cur'] is None]
    print(f"jm1cur is None (no row-0 parent at Ncur's new last index): {len(none_jm1cur)}/{len(rows)}")
    have = [r for r in rows if r['jm1cur'] is not None]
    pcutle_ok = [r for r in have if r['pcutle']]
    print(f"pcutle (pcut<=jm1cur) among jm1cur-defined: {len(pcutle_ok)}/{len(have)}")
    pcutle_bad = [r for r in have if not r['pcutle']]
    for r in pcutle_bad[:10]:
        print("  PCUTLE FAIL:", r['M'],'q=',r['q'],'m=',r['m'],'pcut=',r['pcut'],'jm1cur=',r['jm1cur'])
    r2b_among_pcutle = [r for r in pcutle_ok]
    r2b_ok = [r for r in r2b_among_pcutle if r['R2bprime']]
    print(f"R2bprime among pcutle-ok: {len(r2b_ok)}/{len(r2b_among_pcutle)}")
    r2b_bad = [r for r in r2b_among_pcutle if not r['R2bprime']]
    for r in r2b_bad[:10]:
        print("  R2BPRIME FAIL:", r['M'],'q=',r['q'],'m=',r['m'],'pcut=',r['pcut'],'jm1cur=',r['jm1cur'])
    print("entry0(col) for jm1cur=None cases:", Counter(r['entry0col'] for r in none_jm1cur))
    print("entry0(col) for jm1cur defined cases:", Counter(r['entry0col']>0 for r in have))
    # does jm1cur==None correlate with entry0(col)==0 (a fresh reset column)?
    bad_reset = [r for r in none_jm1cur if r['entry0col']!=0]
    print(f"jm1cur=None but entry0(col)!=0 (should be empty if reset<=>entry0=0): {len(bad_reset)}")
    ok_reset = [r for r in have if r['entry0col']==0]
    print(f"jm1cur DEFINED despite entry0(col)==0 (should be empty if reset<=>entry0=0): {len(ok_reset)}")
