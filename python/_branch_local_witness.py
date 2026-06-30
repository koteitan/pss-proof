import sys, os, itertools, functools, subprocess, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P)
import red_model as rm
from trans_model import (Trans,Mark,ZB,PB,bpHeadT,bpHeadV,addBT,Dpt,flatBT,
                          reduced as treduced,condV,condI,condIII,condVI,scb_decomps)
import trans_model as tm

"""§8.5 keystone R2a/anchor -- ROUND 4 drill-down: empirically test the
'branch-local addBT/Mark witness' hypothesis flagged at the end of ROUND 3
(_keystone_residual_summary.py, _r2a_branch_routing.py): when a fold column
opens a fresh branch (host becomes multiT), is the REAL recursive `Mark`
value at that column something simple/tractable (NOT the scbSubst-step
formula, which structurally requires monoT), and does the `anchor`
(scb_decomp existence) requirement of m_8_5_fold_C_commute still hold via a
DIFFERENT, branch-local witness?

KEY STRUCTURAL FACT (from pss_paper.thy 1175-1210, mirrored in trans_model.py
Mark()): unlike Trans (whose multi/non-monoT case IS addBT(trunk,branch)),
Mark's multi/non-monoT case is NOT addBT -- it is purely
    Mark M m = (Dpt 0 ZB)                    if PJ = [(0,0)]
              = Mark PJ (m - j0)              otherwise
i.e. it recurses ENTIRELY into the last P-component PJ, dropping the trunk
part, with NAT SUBTRACTION m-j0 (underflows to 0 if m<j0, i.e. if the
tracked mark n0 lies in the TRUNK, before PJ starts).
"""

BMS='/home/koteitan/proofs/pss-proof/wt2/tmp/yaBMS/c/bms'
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"

def transJm1(M):
    p = parent(M,0,Lng(M)-1)
    if p is None: return None
    return tm.Adm(M, p)

def gen(maxlen=5,maxv=2):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(3,maxlen+1):
        for s in itertools.product(pairs,repeat=L):
            M=list(s)
            if M[0]!=(0,0): continue
            yield M

def col_label(host):
    if not reduced(host): return "NOTRED"
    if multiT(host):
        Pc = P(host)
        PJ = Pc[-1]
        j0 = Lng(host) - Lng(PJ)
        return ("MULTI", tuple(PJ), j0)
    if monoT(host): return ("MONO",)
    return ("ZERO",)

def main_sweep(timelimit=250):
    t0=time.time(); cnt=0; checked=0
    rows=[]   # one row per (m, label info)
    for M in gen(5,2):
        if time.time()-t0>timelimit: break
        try:
            if not (reduced(M) and is_std(tuple(M))): continue
        except Exception: continue
        cnt+=1
        for q in (2,3):
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>15: continue
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
                    host=host+[B[m]]
                    Ncur=list(host)
                    if not reduced(Ncur): continue
                    lbl = col_label(Ncur)
                    lblP = col_label(Nprev)
                    # real Mark values
                    try:
                        markPrev = Mark(Nprev, jm1)
                    except Exception as e:
                        markPrev = ('ERR', str(e))
                    try:
                        markCur = Mark(Ncur, jm1)
                    except Exception as e:
                        markCur = ('ERR', str(e))
                    # transC1 of Ncur (next column's own marked principal w.r.t Nprev)
                    j0c = Lng(Nprev)-1  # parent's own Lng-1, but transJ0 defined at Ncur:
                    jp_cur = parent(Ncur, 0, Lng(Ncur)-1)
                    jm1_cur = None
                    if jp_cur is not None:
                        jm1_cur = tm.Adm(Ncur, jp_cur)
                    c1_cur = None
                    if jm1_cur is not None:
                        try:
                            c1_cur = Mark(Nprev, jm1_cur)
                        except Exception as e:
                            c1_cur = ('ERR', str(e))
                    anchor_ok = None
                    if isinstance(c1_cur, tuple) and c1_cur and c1_cur[0]=='T':
                        ds = scb_decomps(markPrev, flatBT(c1_cur))
                        anchor_ok = len(ds) > 0
                    rows.append(dict(m=m, lblP=lblP, lbl=lbl, markPrev=markPrev, markCur=markCur,
                                      jm1_cur=jm1_cur, c1_cur=c1_cur, anchor_ok=anchor_ok,
                                      j0c=j0c, jm1=jm1, M=tuple(M), q=q))
            except Exception:
                continue
    return cnt, checked, rows

def summarize(rows):
    print(f"total rows={len(rows)}")
    multi_cur = [r for r in rows if r['lbl'][0]=='MULTI']
    multi_prev = [r for r in rows if r['lblP'][0]=='MULTI']
    print(f"rows where Ncur is MULTI: {len(multi_cur)}/{len(rows)}")
    print(f"rows where Nprev is MULTI: {len(multi_prev)}/{len(rows)}")
    # among Ncur MULTI: how often is PJ == [(0,0)] (trivial reset)?
    trivial = [r for r in multi_cur if r['lbl'][1]==((0,0),)]
    print(f"  of which PJ==[(0,0)] (trivial reset, Mark forced to Dpt 0 ZB): {len(trivial)}/{len(multi_cur)}")
    for r in trivial[:5]:
        print("   trivial example:", r['M'], 'q=',r['q'],'m=',r['m'], 'markCur=', r['markCur'])
    nontrivial = [r for r in multi_cur if r['lbl'][1]!=((0,0),)]
    print(f"  of which PJ!=[(0,0)] (nontrivial branch): {len(nontrivial)}/{len(multi_cur)}")
    for r in nontrivial[:8]:
        print("   nontrivial example:", r['M'], 'q=',r['q'],'m=',r['m'], 'PJ=',r['lbl'][1],'j0=',r['lbl'][2],
              'jm1=',r['jm1'], 'markCur=', r['markCur'])
    # anchor success rate, split by whether Nprev (the host BEFORE this column,
    # whose Mark-value is the scb_decomp target) is multi or mono
    def rate(sub):
        ok=[r for r in sub if r['anchor_ok'] is True]
        tot=[r for r in sub if r['anchor_ok'] is not None]
        return f"{len(ok)}/{len(tot)}"
    print("anchor rate overall:", rate(rows))
    print("anchor rate | Nprev MONO:", rate([r for r in rows if r['lblP'][0]=='MONO']))
    print("anchor rate | Nprev MULTI:", rate([r for r in rows if r['lblP'][0]=='MULTI']))
    # for Nprev MULTI rows: is markPrev constant Dpt(0,ZB)?
    mp = [r for r in rows if r['lblP'][0]=='MULTI']
    constzero = [r for r in mp if r['markPrev']==Dpt(0,ZB)]
    print(f"Nprev MULTI & markPrev==Dpt(0,ZB): {len(constzero)}/{len(mp)}")
    print("  anchor rate | Nprev MULTI & markPrev==Dpt(0,ZB):", rate(constzero))
    notconstzero = [r for r in mp if r['markPrev']!=Dpt(0,ZB)]
    print("  anchor rate | Nprev MULTI & markPrev!=Dpt(0,ZB):", rate(notconstzero))
    # within notconstzero: split by whether n0 (jm1) < j0 of Nprev's own PJ (trunk case)
    # vs n0 falls WITHIN Nprev's own last branch (branch-local case)
    trunk_n0 = [r for r in notconstzero if r['jm1'] < r['lblP'][2]]
    local_n0 = [r for r in notconstzero if r['jm1'] >= r['lblP'][2]]
    print(f"  of notconstzero: n0<j0(Nprev) [TRUNK, junk-collapse] = {len(trunk_n0)}, "
          f"n0>=j0(Nprev) [WITHIN last branch] = {len(local_n0)}")
    print("    anchor rate | TRUNK case:", rate(trunk_n0))
    print("    anchor rate | WITHIN-branch case:", rate(local_n0))
    for r in notconstzero[:10]:
        print("   Nprev MULTI, markPrev!=Dpt(0,ZB):", r['M'],'q=',r['q'],'m=',r['m'],
              'PJprev=', r['lblP'], 'markPrev=', r['markPrev'], 'anchor_ok=', r['anchor_ok'])

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(250)
    print(f"std&reduced scanned={cnt}, regime-checked={checked}, rows={len(rows)}")
    summarize(rows)
