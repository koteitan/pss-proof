import sys, itertools, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,diagSeq)
import red_model as rm
from trans_model import (Trans,Mark,ZB,PB,bpHeadT,bpHeadV,addBT,Dpt,flatBT,
                          reduced as treduced,condV,condI,condIII,condVI,scb_decomps)
import trans_model as tm

"""ROUND 6 -- direct test of round 5's caveat: is `entry N 0 0 < fst col`
(trunk-stuck anchor's residual hypothesis) free, even when the BASE seed M
is a genuine ST_PS member with entry M 0 0 = u > 0 (M = diagSeq(u,v), u>0;
NOT filtered through the yaBMS `is_std` oracle, which we now understand
tests a DIFFERENT/narrower notion than ST_PS membership -- diagSeq(u,v) for
u>0 IS a literal ST_PS member by the `diag` rule but is REJECTED by yaBMS
`is_std`, which only recognizes (0,0)-rooted standard forms).  This script
builds GENUINE towers oper(M,q) directly from such bases (bypassing is_std
filtering entirely) and re-runs the keystone's own regime filter.
"""

def transJm1(M):
    p = parent(M,0,Lng(M)-1)
    if p is None: return None
    return tm.Adm(M, p)

def gen_diag_bases(umax=4, vspan=4):
    for u in range(0, umax+1):
        for v in range(u, u+vspan+1):
            yield diagSeq(u,v)

def main_sweep(timelimit=240, qs=(2,3,4,5)):
    t0=time.time(); cnt=0; checked=0
    rows=[]
    nonzero_entryN_rows = []
    for M in gen_diag_bases(4,4):
        if time.time()-t0>timelimit: break
        if not reduced(M): continue
        cnt += 1
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>20: continue
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
                    entryN00 = entry(Nprev,0,0)
                    fstcol = col[0]
                    ok = entryN00 < fstcol
                    rows.append(dict(M=tuple(M),u=M[0][0],q=q,m=m,w=w,col=col,
                                      entryN00=entryN00, fstcol=fstcol, ok=ok))
                    if entryN00 != 0:
                        nonzero_entryN_rows.append(rows[-1])
            except Exception as e:
                continue
    return cnt, checked, rows, nonzero_entryN_rows

if __name__ == '__main__':
    cnt, checked, rows, nz = main_sweep(240, (2,3,4,5))
    print(f"diag bases scanned={cnt}, regime-checked={checked}, trunk-stuck rows={len(rows)}")
    ok = [r for r in rows if r['ok']]
    print(f"entry N 0 0 < fst col: {len(ok)}/{len(rows)}")
    bad = [r for r in rows if not r['ok']]
    for r in bad[:15]:
        print("  FAIL:", r)
    print(f"\nrows with entry N 0 0 != 0: {len(nz)}/{len(rows)}")
    for r in nz[:15]:
        print("  NONZERO entryN00:", r)
    # breakdown by base u
    from collections import Counter
    print("\nby base u: (checked count)", Counter(r['u'] for r in rows))
    for u in sorted(set(r['u'] for r in rows)):
        sub=[r for r in rows if r['u']==u]
        okc=sum(1 for r in sub if r['ok'])
        print(f"  u={u}: trunk-stuck rows={len(sub)} ok={okc}")
