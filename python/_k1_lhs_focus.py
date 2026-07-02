#!/usr/bin/env python3
"""Focused check: for condIII/condV standard M,
   (a) EX j. leBT(Trans(M[m]), operB(Trans M)(numBT j)) and which j;
   (b) crux: Trans(M[m]) == demote_rightmost_leaf(operB(Trans M)(numBT j))
       i.e. Trans(M[m]) is the operB image with the deepest D_{v-1}0 leaf -> 0_B.
"""
import sys
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/python")
import trans_model as tm
import red_model as rm
import buchholz as B

def conv(t): return [conv_bp(p) for p in t[1]]
def conv_bp(p): _, v, body = p; return ('D', v, conv(body))

def demote(a):
    # a is buchholz BT (list of principals). Demote rightmost-deepest leaf D_w 0 -> 0.
    if not a: return a
    last = a[-1]; _, w, body = last
    if body == []:           # last = D_w 0, the bottom leaf
        return a[:-1]        # remove it -> at its level becomes 0
    return a[:-1] + [('D', w, demote(body))]

def find_condhosts(maxlen=5, maxval=3):
    pairs = [(x,y) for x in range(maxval+1) for y in range(x+1)]
    hosts = {'III':[], 'V':[]}
    def rec(M):
        if len(M) >= 3 and rm.monoT(M) and tm.reduced(M):
            for c,cond in [('III',tm.condIII),('V',tm.condV)]:
                if cond(M): hosts[c].append(list(M))
        if len(M) >= maxlen: return
        for p in pairs:
            M.append(p)
            if not rm.zeroT(M): rec(M)
            M.pop()
    rec([(0,0)])
    return hosts

def main():
    hosts = find_condhosts()
    for c in ('III','V'):
        print(f"=== cond{c}: {len(hosts[c])} hosts ===")
        shown=0; demote_ok=0; demote_tot=0; bound_ok=0; bound_tot=0
        for M in hosts[c]:
            try: TM = tm.Trans(M)
            except Exception: continue
            TMb = conv(TM)
            if TMb == []: continue
            if not (B.in_TB(TMb) and B.in_OT(TMb)): continue
            rows=[]
            for m in range(2,5):
                try:
                    Mm = rm.oper(M, m); TMm = conv(tm.Trans(Mm))
                except Exception:
                    rows.append((m,'err',None)); continue
                jmatch=None; dematch=None
                for j in range(0,12):
                    rhs = B.bracket(TMb, B.nat(j))
                    if jmatch is None and B.le_term(TMm, rhs): jmatch=j
                    if demote(rhs) == TMm: dematch=j
                bound_tot+=1; demote_tot+=1
                if jmatch is not None: bound_ok+=1
                if dematch is not None: demote_ok+=1
                rows.append((m,jmatch,dematch))
            if shown<8:
                print(f"  M={M}  (m, j_leBT, j_demote_eq): {rows}")
                shown+=1
        print(f"  cond{c}: leBT-bound {bound_ok}/{bound_tot}  demote-eq {demote_ok}/{demote_tot}")

if __name__=='__main__': main()
