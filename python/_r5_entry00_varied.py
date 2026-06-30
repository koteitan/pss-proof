import sys, os, itertools, functools, subprocess, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
from trans_model import (Trans,Mark,ZB,PB,bpHeadT,bpHeadV,addBT,Dpt,flatBT,
                          reduced as treduced,condV,condI,condIII,condVI,scb_decomps)
import trans_model as tm

"""§8.5 keystone ROUND 6 -- test whether `entry N 0 0 < fst col` is a genuine
regime fact or an artifact of the harness's M[0]=(0,0) generation convention
(flagged at the end of Round 5).  Re-run WITHOUT requiring M[0]=(0,0) -- allow
any first pair (subject to M still being std+reduced, which the yaBMS oracle
checks independently)."""

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
            yield M   # NOTE: no M[0]==(0,0) restriction this time

def main_sweep(timelimit=300, maxlen=6, maxv=2, qs=(2,3,4)):
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
                    e00 = entry(Nprev,0,0)
                    fcol = col[0]
                    rows.append(dict(M=tuple(M),q=q,m=m, M0=M[0],
                                      e00=e00, fcol=fcol, ok=(e00<fcol),
                                      jm1cur_def=(jm1cur is not None)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(300, 6, 2, (2,3,4))
    print(f"std&reduced scanned={cnt}, regime-checked={checked}, trunk-stuck rows={len(rows)}")
    from collections import Counter
    print("M0 value distribution among trunk-stuck rows:", Counter(r['M0'] for r in rows))
    bad = [r for r in rows if not r['ok']]
    print(f"entry(N,0,0) < fst(col): {len(rows)-len(bad)}/{len(rows)}")
    for r in bad[:15]:
        print("  COUNTEREXAMPLE:", r['M'], 'q=',r['q'],'m=',r['m'],'M0=',r['M0'],'e00=',r['e00'],'fcol=',r['fcol'])
    nonzero_e00 = [r for r in rows if r['e00']!=0]
    print(f"e00 != 0 among trunk-stuck rows: {len(nonzero_e00)}/{len(rows)}")
    for r in nonzero_e00[:10]:
        print("  e00!=0 example:", r['M'], 'q=',r['q'],'m=',r['m'],'e00=',r['e00'],'fcol=',r['fcol'],'ok=',r['ok'])
