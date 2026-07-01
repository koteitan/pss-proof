import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""§8.5 keystone ROUND 7 -- ROUTE 2 investigation.  Tests whether
`Pcut(Nprev) - Lng(Mq)` (the position of N's open last P-component, RELATIVE
to the start of the just-appended deepen-period block) is Q-INDEPENDENT for
fixed base M and fixed within-period column m -- i.e. whether the trunk-stuck
anchor witness `entry N 0 (Pcut N) < fst col` can be rewritten as a q-FREE
statement purely about M's own segment [j0,j1) via the explicit deepen-block
formula (m_8_5_deepen_block_explicit / m_8_5_deepen_block_row0).

Uses the SAME regime filter as Round 6 (transCondV(Mq)+hp1+parR+coin+jm1pos),
the SAME bug-fixed trans_model.py Mark, and tests BOTH u=0 and u>0 seeds."""

class TimeoutErr(Exception): pass
def handler(signum,frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)

def safe_reduced(M, budget=1):
    signal.alarm(budget)
    try:
        r = reduced(M)
        signal.alarm(0)
        return r
    except Exception:
        signal.alarm(0)
        return None

def transJm1(M):
    p = parent(M,0,Lng(M)-1)
    if p is None: return None
    return tm.Adm(M, p)

def gen(maxlen=7, maxv=2, u_vals=(0,1,2,3)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for u in u_vals:
        for L in range(2,maxlen+1):
            for s in itertools.product(pairs, repeat=L-1):
                M=[(u,u)]+list(s)
                yield M

def regime_rows_for_M(M, qs):
    """For fixed M, collect (q, m, pcut_rel, fst_col, entry_N0_pcut) for every
    trunk-stuck column across the given q's, where pcut_rel = Pcut(Nprev) - Lng(Mq)."""
    out = []
    for q in qs:
        try:
            Mq=oper(M,q); j1=Lng(Mq)-1
            if j1<=0 or Lng(Mq)>18: continue
            if not condV(Mq): continue
            if not hasParent(Mq,1,j1): continue
            p1=parent(Mq,1,j1); parR=nextrel0(Mq,p1,j1); p0=parent(Mq,0,j1)
            if not (parR and p1==p0): continue
            jm1=Adm(Mq,p0)
            if not (jm1>0): continue
            Msq=oper(M,q+1)
            if Msq[:len(Mq)]!=Mq: continue
            B=Msq[len(Mq):]; w=len(B)
            if w<1: continue
            LMq = len(Mq)
            host=list(Mq)
            for m in range(w):
                Nprev = list(host)
                col = B[m]
                host=host+[col]
                Ncur=list(host)
                if safe_reduced(Ncur,1) is not True: continue
                if safe_reduced(Nprev,1) is not True: continue
                if not multiT(Nprev): continue
                pcut = Pcut(Nprev)
                stuck = jm1 < pcut
                if not stuck: continue
                fcol = col[0]
                if fcol == 0: continue
                epcut = entry(Nprev,0,pcut)
                out.append(dict(q=q, m=m, w=w, LMq=LMq,
                                 pcut=pcut, pcut_rel=pcut-LMq,
                                 fcol=fcol, epcut=epcut,
                                 ok_pcut=(epcut<fcol)))
        except Exception:
            continue
    return out

def main_sweep(timelimit=300, maxlen=7, maxv=2, qs=(1,2,3,4), u_vals=(0,1,2,3)):
    t0=time.time(); cnt=0
    all_rows=[]
    qindep_total=0; qindep_match=0; qindep_examples=[]
    for M in gen(maxlen,maxv,u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
        cnt+=1
        rows = regime_rows_for_M(M, qs)
        if not rows: continue
        all_rows.extend([dict(M=tuple(M), **row) for row in rows])
        # group by m, compare pcut_rel across distinct q for SAME M, SAME m
        by_m = {}
        for row in rows:
            by_m.setdefault(row['m'], []).append(row)
        for m, group in by_m.items():
            if len(group) < 2: continue
            rels = set(g['pcut_rel'] for g in group)
            qindep_total += 1
            if len(rels) == 1:
                qindep_match += 1
            else:
                if len(qindep_examples) < 8:
                    qindep_examples.append((tuple(M), m, group))
    return cnt, all_rows, qindep_total, qindep_match, qindep_examples

if __name__ == '__main__':
    cnt, rows, qtot, qmatch, qex = main_sweep(300, 7, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, total trunk-stuck rows={len(rows)}")
    okp = [r for r in rows if r['ok_pcut']]
    print(f"entry(N,0,Pcut(N)) < fst(col): {len(okp)}/{len(rows)}  (sanity re-check of Round 6)")
    print(f"\nQ-INDEPENDENCE of pcut_rel=Pcut(Nprev)-Lng(Mq), grouped by (M,m) with >=2 distinct q's:")
    print(f"  groups tested={qtot}, all-q-agree={qmatch}, DISAGREE={qtot-qmatch}")
    for M, m, group in qex:
        print(f"  COUNTEREXAMPLE M={M} m={m}:")
        for g in group:
            print(f"    q={g['q']} w={g['w']} LMq={g['LMq']} pcut={g['pcut']} pcut_rel={g['pcut_rel']} fcol={g['fcol']} epcut={g['epcut']} ok={g['ok_pcut']}")
