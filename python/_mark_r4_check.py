#!/usr/bin/env python3
"""round-4 mark crux: validate the CORRECTED D_v 0 recurrence for condIII/condV.

Target (corrected):  flatBT(Trans(M[m])) = S_{m-1} @ flatBP(D_v 0) @ B_{m-1}
  i.e. Trans(M[m]) equals operB(Trans M)(numBT (m-1)) EXCEPT the deepest
  rightmost leaf D_{v-1} 0 is promoted to D_v 0, where v = entry M 1 (Lng M -1).
Also: which j gives leBT(Trans(M[m]), operB(Trans M)(numBT j))?
"""
import sys
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/python")
import trans_model as tm
import red_model as rm
import buchholz as B

ZB = tm.ZB

def conv(t):                 # BT (trans_model) -> buchholz term (list of princ)
    return [('D', p[1], conv(p[2])) for p in t[1]]

def deepest_leaf_idx(bt):
    # follow last principal's body to the bottom; return its index, or None if empty
    ps = bt[1]
    if not ps: return None
    _, w, body = ps[-1]
    if body[1] == []:        # body == ZB -> this is the bottom leaf D_w 0
        return w
    return deepest_leaf_idx(body)

def promote_leaf(bt, newv):
    # return a copy with the deepest rightmost leaf index replaced by newv
    ps = bt[1]
    _, w, body = ps[-1]
    if body[1] == []:
        return ('T', ps[:-1] + [('D', newv, ZB)])
    return ('T', ps[:-1] + [('D', w, promote_leaf(body, newv))])

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
    hosts = find_condhosts(maxlen=4, maxval=3)
    for c in ('III','V'):
        print(f"=== cond{c}: {len(hosts[c])} hosts ===")
        rec_ok=rec_tot=0; shown=0; bound_ok=bound_tot=0
        for M in hosts[c]:
            try:
                if not rm.is_standard(M): continue
            except Exception:
                continue
            try:
                TM = tm.Trans(M); TMb = conv(TM)
            except Exception: continue
            if TMb == [] or not (B.in_TB(TMb) and B.in_OT(TMb)): continue
            v = rm.entry(M,1,rm.Lng(M)-1)
            rows=[]
            for m in range(2,4):
                try:
                    Mm = rm.oper(M,m); TMm = tm.Trans(Mm); TMmb = conv(TMm)
                except Exception:
                    rows.append((m,'err')); continue
                # leaf check
                leaf = deepest_leaf_idx(TMm)
                # corrected recurrence: promote_leaf(operB(numBT m-1), v) == Trans(M[m])
                R = B.bracket(TMb, B.nat(m-1))          # operB(Trans M)(numBT (m-1))
                # promote R's deepest leaf v-1 -> v and compare to TMmb
                Rt = ('T', [bp_to_tm(p) for p in R])
                if Rt[1]:
                    Rprom = promote_leaf(Rt, v)
                    Rpromb = conv(Rprom)
                else:
                    Rpromb = None
                eq = (Rpromb == TMmb)
                # which j gives leBT
                jb=None
                for j in range(0,m+4):
                    if B.le_term(TMmb, B.bracket(TMb, B.nat(j))): jb=j; break
                rec_tot+=1; rec_ok+= (1 if eq else 0)
                bound_tot+=1; bound_ok+= (1 if jb is not None else 0)
                rows.append((m, 'eqRec' if eq else 'NO', 'leaf=%s/v=%s'%(leaf,v), 'jLEbt=%s'%jb))
            if shown<12:
                print(f"  M={M} v={v}: {rows}")
                shown+=1
        print(f"  cond{c}: corrected-recurrence {rec_ok}/{rec_tot}   leBT-bound {bound_ok}/{bound_tot}")

def bp_to_tm(p):
    return ('D', p[1], ('T', [bp_to_tm(q) for q in p[2]]))

if __name__=='__main__': main()
