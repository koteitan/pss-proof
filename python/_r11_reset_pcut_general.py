import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)

"""ROUND 11, Route 2, MAJOR SIMPLIFICATION, part 3: is
    fst col == 0  ==>  Pcut (N @ [col]) == Lng N
a GENERAL fact (any N with Lng N > 0, ANY appended column col with fst col=0),
with NO deepen-block / trunk-stuck / condV regime needed at all?  If so, this
is a clean, small, general structural lemma (about Pcut/leR alone) that
directly supplies the missing base case for the Route 2 witness derivation
(combined with the ALREADY-PROVEN m_8_5_Pcut_freezes to propagate it forward
through the rest of the period)."""

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

def gen(maxlen=6, maxv=2, u_vals=(0,1,2,3)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for u in u_vals:
        for L in range(1,maxlen+1):
            for s in itertools.product(pairs, repeat=L-1):
                M=[(u,u)]+list(s)
                yield M

def main_sweep(timelimit=240, maxlen=6, maxv=2, u_vals=(0,1,2,3), vvals=(0,1,2,3)):
    t0=time.time(); cnt=0
    rows=[]
    for N in gen(maxlen,maxv,u_vals):
        if time.time()-t0>timelimit: break
        cnt+=1
        LngN = Lng(N)
        if LngN==0: continue
        for v in vvals:
            col = (0,v)
            X = list(N)+[col]
            try:
                if not multiT(X): continue
                pc = Pcut(X)
            except Exception:
                continue
            rows.append(dict(N=tuple(N), v=v, LngN=LngN, pcut=pc, ok=(pc==LngN)))
    return cnt, rows

if __name__ == '__main__':
    cnt, rows = main_sweep(240, 6, 2, (0,1,2,3), (0,1,2,3))
    print(f"N scanned={cnt}, multiT(N@[(0,v)]) rows={len(rows)}")
    ok = [r for r in rows if r['ok']]
    print(f"Pcut(N@[(0,v)])==Lng(N): {len(ok)}/{len(rows)}")
    for r in [r for r in rows if not r['ok']][:15]: print("  BAD", r)
