import sys, itertools, functools, subprocess, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,diagSeq)
import red_model as rm
from trans_model import (Trans,Mark,ZB,PB,bpHeadT,bpHeadV,addBT,Dpt,flatBT,
                          reduced as treduced,condV,condI,condIII,condVI,scb_decomps)
import trans_model as tm

"""ROUND 6 -- test the SHIFT-INVARIANCE hypothesis for round 5's caveat.

Shift_u(M) = [(a+u,b+u) for (a,b) in M]  (shift BOTH rows uniformly by u).

Claim: diagSeq(u,v) = Shift_u(diagSeq(0,v-u)), and `oper` COMMUTES with
Shift_u (oper(Shift_u(M),n) == Shift_u(oper(M,n))), and all the RELATIONAL
predicates used in the keystone regime (reduced, condV, adm, Adm, parent,
multiT, Pcut, Marked, hasParent) are Shift_u-INVARIANT (same truth value /
same index for M and Shift_u(M)).  If so, `entry N 0 0 < fst col` is
shift-invariant too (both sides shift by u, the comparison is preserved),
so the GENERAL non-(0,0)-rooted base case (M=diagSeq(u,v), u>0) reduces
EXACTLY to the (0,0)-rooted case already checked 79/79 in round 5 -- i.e.
round 5's caveat is resolved: entry N 0 0 < fst col remains exactly as
free/non-free as in the u=0 case, for ANY u, via this shift symmetry.
"""

BMS='/home/koteitan/proofs/pss-proof/wt2/tmp/yaBMS/c/bms'
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"

def Shift(M,u): return [(a+u,b+u) for (a,b) in M]

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

# PART 1: verify oper commutes with Shift_u, on raw (possibly non-ST_PS) tuples too
def test_oper_commute(trials=2000, umax=5):
    t0=time.time(); fails=0; checked=0
    for M in gen(5,2):
        if time.time()-t0>60: break
        for u in range(1,umax+1):
            for n in (1,2,3):
                try:
                    lhs = oper(Shift(M,u), n)
                    rhs = Shift(oper(M,n), u)
                except Exception:
                    continue
                checked+=1
                if lhs != rhs:
                    fails+=1
                    if fails<=5: print("  OPER-COMMUTE FAIL:", rm.fmt(M), "u=",u,"n=",n, lhs, rhs)
    print(f"oper-commutes-with-Shift: checked={checked} fails={fails}")

# PART 2: verify reduced/condV/adm/Adm/parent/multiT/Pcut/Marked invariance under Shift_u
def test_predicate_invariance(umax=5):
    t0=time.time(); checked=0
    mismatches = dict(reduced=0, condV=0, multiT=0, Pcut=0, adm=0, Adm=0, parent=0, marked=0)
    for M in gen(5,2):
        if time.time()-t0>60: break
        if not reduced(M): continue
        for u in range(1,umax+1):
            Ms = Shift(M,u)
            checked += 1
            if reduced(Ms) != reduced(M): mismatches['reduced']+=1
            try:
                cv0=condV(M)
            except Exception:
                cv0=None
            try:
                cvs=condV(Ms)
            except Exception:
                cvs=None
            if cv0!=cvs: mismatches['condV']+=1
            if multiT(Ms)!=multiT(M): mismatches['multiT']+=1
            try:
                p0=Pcut(M); ps=Pcut(Ms)
                if p0!=ps: mismatches['Pcut']+=1
            except Exception:
                pass
            for j in range(Lng(M)):
                if adm(M,j)!=adm(Ms,j): mismatches['adm']+=1; break
            for j in range(Lng(M)+1):
                if Adm(M,j)!=Adm(Ms,j): mismatches['Adm']+=1; break
            for j1 in range(Lng(M)):
                if parent(M,0,j1)!=parent(Ms,0,j1): mismatches['parent']+=1; break
                if parent(M,1,j1)!=parent(Ms,1,j1): mismatches['parent']+=1; break
            for m in range(Lng(M)):
                if marked(M,m)!=marked(Ms,m): mismatches['marked']+=1; break
    print(f"predicate-invariance: checked={checked} mismatches={mismatches}")

# PART 3: full keystone-regime sweep, shifted -- direct re-run of the round5/round4
# trunk-stuck harness but on Shift_u(M) for u in 1..4, confirming entry N 0 0 < fst col
# (now = u + (unshifted value), generally NONZERO) still holds.
def test_shifted_trunkstuck(timelimit=200, umax=4, qs=(2,3,4)):
    t0=time.time(); cnt=0; checked=0
    rows=[]
    for M0 in gen(5,2):
        if time.time()-t0>timelimit: break
        try:
            if not (reduced(M0) and is_std(tuple(M0))): continue
        except Exception: continue
        cnt+=1
        for u in range(0,umax+1):
            M=Shift(M0,u)
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
                        entryN00 = entry(Nprev,0,0)
                        fstcol = col[0]
                        ok = entryN00 < fstcol
                        rows.append(dict(u=u, ok=ok, entryN00=entryN00, fstcol=fstcol, M0=rm.fmt(M0), q=q, m=m))
                except Exception:
                    continue
    return cnt, checked, rows

if __name__ == '__main__':
    print("=== PART 1: oper commutes with Shift_u ===")
    test_oper_commute()
    print("\n=== PART 2: predicate invariance under Shift_u ===")
    test_predicate_invariance()
    print("\n=== PART 3: shifted trunk-stuck entry0<fstcol sweep ===")
    cnt, checked, rows = test_shifted_trunkstuck(200, 4, (2,3,4))
    print(f"std&reduced(0,0)-bases scanned={cnt}, regime-checked(all u)={checked}, trunk-stuck rows={len(rows)}")
    ok = [r for r in rows if r['ok']]
    print(f"entry N 0 0 < fst col: {len(ok)}/{len(rows)}")
    bad = [r for r in rows if not r['ok']]
    for r in bad[:10]: print("  FAIL:", r)
    from collections import Counter
    print("by u:", Counter((r['u'], r['ok']) for r in rows))
    nz = [r for r in rows if r['entryN00']!=0]
    print(f"entryN00 != 0 rows: {len(nz)}/{len(rows)}  (these are the GENUINE non-(0,0)-base instances)")
    for r in nz[:10]: print("  ", r)
