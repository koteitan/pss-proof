import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import trans_model as tm
from trans_model import condV

"""§8.5 ROUND 9, Route 1 item (3) investigation -- testing candidate resolution
(i) from the Round 8 writeup: a SELF-REFERENTIAL period-block law that would let
F be built purely from a pairseq X's OWN trailing block (not from the original
M/q), which -- IF it holds -- would supply the literal q-INDEPENDENT F that
m_8_5_keystone_allq needs.

m_8_5_deepen_block_explicit (already proven, green) gives the EXPLICIT period
block appended going M[q]->M[Suc q]:
    B(q)[i] = (entry M 0 (j0+i) + q*d0, entry M 1 (j0+i)),  i in [0,w)
(j0 = parent M 1 (Lng M-1), w = (Lng M-1)-j0, d0 = entry M 0 j1 - entry M 0 j0).

CLAIM under test: B(q) = Shift d0 (B(q-1)) for q>=1 -- i.e. consecutive deepen
blocks are the SAME list with row-0 shifted by the constant d0.  If genuinely
true (it follows almost by inspection from the explicit formula: B(q)[i] and
B(q-1)[i] differ ONLY in the q*d0 vs (q-1)*d0 term), then a self-referential
F could be defined as:
    F(X) := X @ Shift d0X (lastblock X)
where d0X/lastblock X are recovered from X's OWN two trailing periods (not
referencing M or q), and F(M[q]) = M[Suc q] by this SAME law -- literally
q-independent.

This script empirically verifies (a) B(q)=Shift d0 (B(q-1)) directly from the
oper/deepen-block construction, and (b) that d0 and the block boundary (period
length w) are RECOVERABLE from X=M[q] alone (q>=2) by comparing X's own last
TWO blocks -- i.e. testing d0 = entry X 0 (Lng X-1) - entry X 0 (Lng X-1-w) and
that this matches the "real" d0 from the deepen-block formula, INDEPENDENT of
knowing the original seed M."""

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

def shift(u, B):
    return [(a+u, b) for (a,b) in B]

def main_sweep(timelimit=180, maxlen=6, maxv=2, qs=(1,2,3,4,5), u_vals=(0,1,2,3)):
    t0=time.time(); cnt=0; checked=0
    n_shiftlaw=0; n_shiftlaw_ok=0
    n_selfd0=0; n_selfd0_ok=0
    bad_shift=[]; bad_selfd0=[]
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
                if Lng(Msq)>20: continue
                # (a) shift law: B(q) == Shift d0 (B(q-1))
                Mqm1 = oper(M,q-1) if q>=1 else M
                Bqm1 = Mq[len(Mqm1):] if q>=1 else None
                if q>=1 and Bqm1 is not None and len(Bqm1)==w:
                    n_shiftlaw += 1
                    predicted = shift(d0, Bqm1)
                    ok = (predicted == Bq)
                    if ok: n_shiftlaw_ok += 1
                    else: bad_shift.append((tuple(M),q,Bqm1,Bq,predicted))
                # (b) self-recoverable d0: from Mq alone (q>=2), compare last two
                # blocks purely via Mq's own entries (no reference to M/j0/d0 above)
                if q>=2 and Lng(Mq) >= 2*w:
                    n_selfd0 += 1
                    LqX = Lng(Mq)
                    d0_self = entry(Mq,0,LqX-1) - entry(Mq,0,LqX-1-w)
                    ok2 = (d0_self == d0)
                    if ok2: n_selfd0_ok += 1
                    else: bad_selfd0.append((tuple(M),q,d0,d0_self))
            except Exception:
                continue
    return cnt, checked, n_shiftlaw, n_shiftlaw_ok, bad_shift, n_selfd0, n_selfd0_ok, bad_selfd0

if __name__ == '__main__':
    cnt, checked, n_sl, n_sl_ok, bad_sl, n_sd, n_sd_ok, bad_sd = main_sweep()
    print(f"reduced seeds scanned={cnt}, with-hasParent1={checked}")
    print(f"(a) shift law B(q)=Shift d0 (B(q-1)): {n_sl_ok}/{n_sl}")
    for b in bad_sl[:5]:
        print("  SHIFT-LAW COUNTEREXAMPLE:", b)
    print(f"(b) self-recoverable d0 from Mq alone: {n_sd_ok}/{n_sd}")
    for b in bad_sd[:5]:
        print("  SELF-D0 COUNTEREXAMPLE:", b)
