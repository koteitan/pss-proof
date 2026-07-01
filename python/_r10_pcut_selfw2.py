import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,le0)

"""§8.5 ROUND 10, Route 1 item (3) sub-point (1), take 2: same candidate as
_r10_pcut_selfw.py (w = Lng X - Pcut X for X=M[q], no drop/j0 offset) but with
the SAME growth-verification filter Round 9's _r9_item3_selfref.py used (checks
the actual appended block really has length w before trusting the "M[q] is q
period-copies past M" picture) -- the previous script's failures were mostly
degenerate seeds where oper(M,q) does not even grow as m_8_5_deepen_block_explicit
assumes (Lng(X) unexpectedly equal to Lng(M)), not genuine counterexamples to the
Pcut candidate itself."""

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
        for L in range(2,maxlen+1):
            for s in itertools.product(pairs, repeat=L-1):
                M=[(u,u)]+list(s)
                yield M

def main_sweep(timelimit=180, maxlen=6, maxv=2, qs=(1,2,3,4,5), u_vals=(0,1,2,3)):
    t0=time.time(); cnt=0; checked=0
    n_test=0; n_pcut_eq_j0=0; n_w_eq=0
    bad_j0=[]; bad_w=[]
    for M in gen(maxlen,maxv,u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
        cnt+=1
        try:
            j1 = Lng(M)-1
            if j1<=0: continue
            if not hasParent(M,1,j1): continue
            j0 = parent(M,1,j1)
            if not (j0 < j1): continue
            d0 = entry(M,0,j1)-entry(M,0,j0)
            w = j1-j0
            if w<1: continue
        except Exception:
            continue
        checked+=1
        for q in qs:
            try:
                Mq = oper(M,q); Msq = oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                Bq = Msq[len(Mq):]
                if len(Bq)!=w: continue
                X = Mq
                if q<2: continue   # need >=2 periods appended past M itself
                if Lng(X) > 24: continue
                if not multiT(X):
                    continue
                pc = Pcut(X)
            except Exception:
                continue
            n_test += 1
            pj0 = (pc == j0)
            wj = (Lng(X) - pc == w)
            if pj0: n_pcut_eq_j0 += 1
            else: bad_j0.append((tuple(M), q, j0, w, pc, Lng(X)))
            if wj: n_w_eq += 1
            else: bad_w.append((tuple(M), q, j0, w, pc, Lng(X)))
    return cnt, checked, n_test, n_pcut_eq_j0, n_w_eq, bad_j0, bad_w

if __name__ == '__main__':
    cnt, checked, n_test, n_peq, n_weq, bad_j0, bad_w = main_sweep()
    print(f"reduced seeds scanned={cnt}, with-hasParent1={checked}")
    print(f"growth-verified multiT(X) cases tested: {n_test}")
    print(f"Pcut(X)==j0 (original): {n_peq}/{n_test}")
    print(f"Lng(X)-Pcut(X)==w: {n_weq}/{n_test}")
    for b in bad_j0[:8]:
        print("  BAD-j0:", b)
    for b in bad_w[:8]:
        print("  BAD-w:", b)
