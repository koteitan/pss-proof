#!/usr/bin/env python3
# r36 BRIDGES: validate brN and brMp (article 8.2 parts (1),(3)) EXACTLY on the
# genuine vg4x_reg4 base regime (cfbx_j1p N = Lng N-1, condII/IV Adm0 host).
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm, oper,
                       diagSeq, Br, FirstNodes, Joints, Red, hasParent, fmt,
                       TrMax, Pred)
import trans_model as tm
from trans_model import (Dpt, ZB, bpHeadT, bpHeadV, addBT, PB, SigmaB, Trans)

def pr(*a): print(*a, flush=True)
def is_reduced(M): return Red(list(M)) == list(M)

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]; a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def LastStep(M):
    b = Br(M)
    if not b: return 0
    J1 = len(b)-1; lastb = b[J1]
    if entry(lastb,0,0) == entry(lastb,1,0): return J1
    cands = [J for J in range(len(b))
             if entry(lastb,0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0)]
    return min(cands)

def transJ0(M): return parent(M, 0, Lng(M)-1)
def transJm1(M): return Adm(M, transJ0(M))

def transCondI(M):
    jp = parent(M,0,Lng(M)-1)
    return entry(M,1,Lng(M)-1)==0 and adm(M,jp)
def transCondIII(M):
    jp = parent(M,0,Lng(M)-1)
    return entry(M,1,Lng(M)-1)>0 and entry(M,1,jp)>=entry(M,1,Lng(M)-1) and adm(M,jp)
def transCondV(M):
    jp = parent(M,0,Lng(M)-1)
    return (entry(M,1,Lng(M)-1)>0 and entry(M,1,jp)+1==entry(M,1,Lng(M)-1)
            and jp+1 < Lng(M)-1)

def in_reg4_base(M):
    # vg2x_reg2: reduced & monoT(=PT_PS with T_PS) & Br != []
    if not is_reduced(M): return False
    if not monoT(M): return False
    b = Br(M)
    if not b: return False
    J1 = len(b)-1
    if Lng(M)-1 <= 1: return False
    # base: cfbx_j1p = FirstNodes!(J1) = Lng-1
    fn = FirstNodes(M)
    if fn[J1] != Lng(M)-1: return False
    # vg3x_reg3 guard: entry 1 j1' < entry 0 j1'
    j1p = fn[J1]
    if not (entry(M,1,j1p) < entry(M,0,j1p)): return False
    # vg4x: 0 < j0' < TrMax
    jt = Joints(M)
    j0p = jt[J1]
    if j0p is None: return False
    if not (0 < j0p and j0p < TrMax(M)): return False
    # Adm0
    if transJm1(M) != 0: return False
    # notCondA
    if transCondI(M) or transCondIII(M) or transCondV(M): return False
    return True

def check_bridges(M):
    # form: Trans M = D_{e10}(t1 + D_{e1j0'} tau)
    b = Br(M); J1 = len(b)-1
    j0p = Joints(M)[J1]
    j1  = Lng(M)-1
    e10 = entry(M,1,0); e1j0 = entry(M,1,j0p)
    TM = Trans(M)
    # outer head must be e10, single principal
    if len(TM[1]) != 1 or TM[1][0][1] != e10:
        return ('formfail-outer', fmt(M))
    inner = TM[1][0][2]           # = t1 + D_{e1j0'} tau
    Pin = PB(inner)
    if not Pin: return ('formfail-inner-empty', fmt(M))
    last = Pin[-1]
    if bpHeadV(last) != e1j0:
        return ('formfail-lasthead', fmt(M), bpHeadV(last), e1j0)
    t1  = SigmaB(Pin[:-1])
    tau = bpHeadT(last)           # body of last principal = tau
    # brN: Trans(seg M 0 (FirstNodes!LastStep - 1)) = D_{e10} t1
    m1 = FirstNodes(M)[LastStep(M)] - 1
    Nsl = seg(M, 0, m1)
    TN = Trans(Nsl)
    okN = (TN == Dpt(e10, t1))
    # brMp: tau = t1 + t2, t2 != 0, Trans(seg M j0' j1) = D_{e1j0'} tau
    Msl = seg(M, j0p, j1)
    TMp = Trans(Msl)
    okMp_slice = (TMp == Dpt(e1j0, tau))
    # split tau = t1 + t2
    ptau = tau[1]; pt1 = t1[1]
    if ptau[:len(pt1)] == pt1:
        t2 = ('T', ptau[len(pt1):])
        ok_split = (t2 != ZB)
    else:
        t2 = None; ok_split = False
    if okN and okMp_slice and ok_split:
        return ('ok', fmt(M))
    tag = 'FAIL'
    return (tag, fmt(M), 'okN=%s okMpSlice=%s okSplit=%s' % (okN, okMp_slice, ok_split),
            'TN=%r want=%r' % (TN, Dpt(e10,t1)) if not okN else '',
            'TMp=%r want=%r' % (TMp, Dpt(e1j0,tau)) if not okMp_slice else '')

# oper-BFS generation of genuine standard hosts from diagSeq seeds
def gen_hosts(Lmax, pool_cap, seeds):
    seen = set(); out = []
    frontier = [tuple(map(tuple, s)) for s in seeds]
    seen.update(frontier)
    while frontier and len(out) < pool_cap:
        nxt = []
        for st in frontier:
            M = [list(p) for p in st]
            if Lng(M) <= Lmax and in_reg4_base(M):
                out.append(M)
            for n in range(2, 6):
                try: M2 = oper(M, n)
                except Exception: continue
                if Lng(M2) > Lmax: continue
                key = tuple(map(tuple, M2))
                if key not in seen:
                    seen.add(key); nxt.append(key)
                    if len(seen) > 200000: break
        frontier = nxt
    return out

def main():
    t0=time.time()
    Lmax = int(sys.argv[1]) if len(sys.argv)>1 else 9
    cap  = int(sys.argv[2]) if len(sys.argv)>2 else 40000
    # (A) exhaustive enumeration small
    ok=fail=0; fails=[]
    cells = [(a,b) for a in range(5) for b in range(5)]
    for L in range(3, min(Lmax,7)+1):
        if time.time()-t0>900: pr("[budget-enum]"); break
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t0>900: break
            M=[(0,0)]+list(tup)
            if not in_reg4_base(M): continue
            r=check_bridges(M)
            if r[0]=='ok': ok+=1
            else:
                fail+=1
                if len(fails)<12: fails.append(r)
        pr(f"[enum L={L}] ok={ok} fail={fail} t={time.time()-t0:.0f}s")
    # (B) deep oper-BFS
    seeds=[diagSeq(0,k) for k in range(1,6)]
    hosts=gen_hosts(Lmax, cap, seeds)
    dok=dfail=0; dmax=0
    for M in hosts:
        r=check_bridges(M)
        dmax=max(dmax,Lng(M))
        if r[0]=='ok': dok+=1
        else:
            dfail+=1
            if len(fails)<20: fails.append(r)
    pr("="*60)
    pr(f"[ENUM] brN&brMp ok={ok} fail={fail}")
    pr(f"[DEEP oper-BFS] hosts={len(hosts)} ok={dok} fail={dfail} maxLng={dmax}")
    for f in fails: pr("  ", f)

if __name__=='__main__':
    main()
