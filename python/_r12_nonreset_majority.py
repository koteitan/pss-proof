import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 12, Route 2: Round 11's m_8_5_Pcut_reset_witness only covers deepen
blocks B whose OWN FIRST column B[0] is a reset column (fst(B!0)=0) -- the
parent independently verified this holds in only ~20% of genuine trunk-stuck
deepen-block cases (274/1337), FALSE in ~66% (879/1337).  This script targets
the MAJORITY case: blocks where fst(B!0) != 0 (the deepen block's own first
appended column does NOT reset row 0).

Candidate mechanism (mirrors the reset case's proof shape, but WITHOUT the
jump): if entry(Mq,0,Pcut(Mq)) < fst(B!0) holds at column 0, then
m_8_5_Pcut_freezes (ALREADY PROVEN) gives Pcut(Mq@[B!0]) = Pcut(Mq) UNCHANGED
(no jump).  If this same strict inequality holds again at column 1 (now with
the SAME frozen Pcut value), Pcut freezes again, etc.  So the conjecture is:
in the non-reset-first-column regime, Pcut STAYS AT Pcut(Mq) (fixed, from
BEFORE the block even starts) throughout the ENTIRE block, and the single
witness needed reduces to

    epcut0 := entry(Mq,0,Pcut(Mq))   [a SINGLE value, computed once at Mq]
    epcut0 < fst(B!m)   for EVERY column m of the block (0..w-1)

First measure the base partition (fst(B!0)==0 vs !=0) to reproduce the
~20/~80 split, THEN restrict entirely to the non-reset-first-column (majority)
sub-population and test:
  (F1) Pcut(Mq@take m B) == Pcut(Mq) for ALL 0<=m<Lng(B)  [freeze persists]
  (F2) epcut0 < fst(B!m) for ALL 0<=m<Lng(B)  [the witness, block-uniform]
  (F3) same as F2 but restricted to genuinely TRUNK-STUCK columns only
       (jm1 < Pcut(Nprev)), i.e. the actual proof obligation
"""

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

def main_sweep(timelimit=240, maxlen=6, maxv=2, qs=(1,2,3,4), u_vals=(0,1,2,3)):
    t0=time.time(); cnt=0; checked=0
    blocks=[]   # one row per genuine (Mq,B) trunk-stuck-eligible block
    for M in gen(maxlen,maxv,u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
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
                if safe_reduced(Mq,1) is not True: continue
                if not multiT(Mq): continue
                # Is ANY column of this block genuinely trunk-stuck?  Walk the
                # fold and record per-column stuck/witness data (same shape as
                # _r11_twocase_v3.py's per-column loop).
                host=list(Mq)
                percol=[]
                any_stuck=False
                PcutMq = Pcut(Mq)
                epcut0 = entry(Mq,0,PcutMq)
                for m in range(w):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: percol.append(None); continue
                    if safe_reduced(Nprev,1) is not True: percol.append(None); continue
                    if not multiT(Nprev): percol.append(None); continue
                    pcutN = Pcut(Nprev)
                    stuck = jm1 < pcutN
                    fcol = col[0]
                    epcut = entry(Nprev,0,pcutN)
                    if stuck: any_stuck=True
                    percol.append(dict(m=m, pcutN=pcutN, stuck=stuck, fcol=fcol,
                                        epcut=epcut,
                                        pcut_frozen=(pcutN==PcutMq),
                                        witness=(epcut<fcol) if fcol!=0 else None,
                                        witness0=(epcut0<fcol)))
                if not any_stuck: continue
                fcol0 = B[0][0]
                blocks.append(dict(M=tuple(M),q=q,jm1=jm1,PcutMq=PcutMq,
                                    epcut0=epcut0, w=w, fcol0=fcol0,
                                    reset_first=(fcol0==0), percol=percol))
            except Exception:
                continue
    return cnt, checked, blocks

if __name__ == '__main__':
    cnt, checked, blocks = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, "
          f"genuine trunk-stuck-eligible BLOCKS={len(blocks)}")
    reset = [b for b in blocks if b['reset_first']]
    nonreset = [b for b in blocks if not b['reset_first']]
    print(f"blocks with reset first column (fst(B[0])==0): {len(reset)}/{len(blocks)} "
          f"({100.0*len(reset)/max(1,len(blocks)):.1f}%)")
    print(f"blocks with NON-reset first column (fst(B[0])!=0): {len(nonreset)}/{len(blocks)} "
          f"({100.0*len(nonreset)/max(1,len(blocks)):.1f}%)")

    print("\n=== MAJORITY (non-reset-first-column) sub-population ===")
    # F1: Pcut freeze persists at Pcut(Mq) throughout the ENTIRE block
    f1_rows = []
    for b in nonreset:
        for pc in b['percol']:
            f1_rows.append(pc['pcut_frozen'])
    if f1_rows:
        print(f"F1 Pcut(Nprev)==Pcut(Mq) for ALL columns: "
              f"{sum(f1_rows)}/{len(f1_rows)}")

    # F2: epcut0 < fcol for EVERY column (including reset-valued fcol==0, where
    # it's automatically false unless epcut0==0 too -- but we exclude fcol==0
    # columns here since those are a separate/trivial case per the existing
    # reset-witness route)
    f2_rows = []
    for b in nonreset:
        for pc in b['percol']:
            if pc['fcol']==0: continue
            f2_rows.append(pc['witness0'])
    if f2_rows:
        print(f"F2 epcut0<fcol for ALL non-reset columns (block-uniform): "
              f"{sum(f2_rows)}/{len(f2_rows)}")

    # F3: same restricted to genuinely trunk-stuck columns only (the real
    # proof obligation)
    f3_rows = []
    f3_detail = []
    for b in nonreset:
        for pc in b['percol']:
            if not pc['stuck']: continue
            if pc['fcol']==0: continue  # separate case (reset column mid-block)
            f3_rows.append(pc['witness0'])
            f3_detail.append((b,pc))
    if f3_rows:
        print(f"F3 epcut0<fcol for TRUNK-STUCK non-reset columns only: "
              f"{sum(f3_rows)}/{len(f3_rows)}")
        bad = [(b,pc) for (b,pc) in f3_detail if not pc['witness0']]
        for b,pc in bad[:10]:
            print("  BAD F3:", dict(M=b['M'],q=b['q'],jm1=b['jm1'],PcutMq=b['PcutMq'],
                                     epcut0=b['epcut0'],m=pc['m'],fcol=pc['fcol'],
                                     epcut=pc['epcut'],pcutN=pc['pcutN']))

    # F3b: the actual per-column witness (epcut<fcol using the LIVE epcut, not
    # epcut0) for trunk-stuck non-reset columns in the majority sub-population
    f3b_rows = []
    for b in nonreset:
        for pc in b['percol']:
            if not pc['stuck']: continue
            if pc['fcol']==0: continue
            f3b_rows.append(pc['witness'])
    if f3b_rows:
        print(f"F3b (live epcut)<fcol for TRUNK-STUCK non-reset columns: "
              f"{sum(f3b_rows)}/{len(f3b_rows)}")

    # F0: does the block even have any mid-block reset column (fcol==0 for
    # some 0<m<w)?  If so the two-case split isn't even block-uniform.
    midreset = 0
    for b in nonreset:
        if any(pc['fcol']==0 for pc in b['percol'][1:]):
            midreset += 1
    print(f"\nblocks (majority pop) with a MID-block reset column (0<m, fcol==0): "
          f"{midreset}/{len(nonreset)}")
