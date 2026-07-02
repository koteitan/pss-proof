#!/usr/bin/env python3
"""r14-B1: empirical validation of the [Buc1] Lemma 3.2/3.3 citation lemmas for
THIS repo's operB (pss_paper.thy 737-780, A23-fixed ([].4)(ii) xseq tower),
plus every intermediate lemma of the planned Isabelle proof:

  (b) DESC   a in OT_B, a<>0, z=numBT n         ==> operB a z < a   (Lemma 3.2a)
  (a) CLOS   same hyps                          ==> operB a z in OT_B (Lemma 3.3)
  MONO       dom(a)=T_w, z1<z2 in T_w           ==> a[z1] < a[z2]   (Lemma 3.2b; no OT needed)
  LB         a in OT, dom(a)=T_w, z in T_w      ==> z <= a[z]
  DW0LT      b in OT, dom(b)=T_w                ==> D_w 0 < b
  TOWER      kind-1 tower x_i strictly increasing; x_i < b; x_i in OT; G_v x_i < x_i
  TRI (3.6)  a in OT, z in dom(a) => forall u, forall c with a[z]<=c<=a:
             G_u(a[z]) setle G_u(c) u G_u(z) u {0}
  NONZERO    dom(a)=N ==> a[z] <> 0

The model is python/buchholz.py (already A23-validated against the Isabelle
definition; branch-by-branch correspondence rechecked in this file's header
comment).  Genuine regime = ALL terms within the size bounds passing the real
in_OT/in_TB filters (there is no oper-generation for Buchholz terms; OT_B
membership IS the filter).
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from buchholz import (ZERO, D, nat, is_zero, add, mul, lt_term, le_term, G,
                      in_OT, in_Tv, in_TB, dom, bracket, nat_value, fmt, INF)

MAX_SYM = 5          # total number of D symbols per term
MAX_IDX = 3          # indices 0..MAX_IDX (all finite => everything is in T_B)
NS = range(0, 4)     # numerals n for the top-level checks

def freeze(t):
    return tuple(('D', p[1], freeze(p[2])) for p in t)

def gen_pool(max_sym, max_idx):
    idxs = list(range(max_idx + 1))
    terms = {0: [[]]}
    princ = {}
    for s in range(1, max_sym + 1):
        princ[s] = [D(v, t) for v in idxs for t in terms_upto(terms, s - 1, exact=s - 1)]
        # terms of exact size s: first principal of size j, rest of size s-j
        out = []
        for j in range(1, s + 1):
            for p in princ[j]:
                if j == s:
                    out.append([p])
                else:
                    for rest in terms[s - j]:
                        if rest:      # rest is a term of exact size s-j >= 1
                            out.append([p] + rest)
        terms[s] = out
    pool = []
    for s in range(1, max_sym + 1):
        pool += terms[s]
    return pool

def terms_upto(terms, s, exact):
    return terms[exact]

def setle(M, N):
    """M setle N  :<=>  forall x in M. exists y in N. x <= y"""
    return all(any(le_term(x, y) for y in N) for x in M)

def main():
    pool = gen_pool(MAX_SYM, MAX_IDX)
    print(f"pool: {len(pool)} nonzero terms (sym<={MAX_SYM}, idx<={MAX_IDX})")
    otb = [a for a in pool if in_OT(a)]     # all are in T_B (finite idxs)
    print(f"OT_B pool: {len(otb)}")

    # ---------- (b) DESC + (a) CLOS on the genuine OT_B regime ----------
    n_desc = n_clos = 0
    bad = []
    for a in otb:
        for n in NS:
            az = bracket(a, nat(n))
            if lt_term(az, a):
                n_desc += 1
            else:
                bad.append(('DESC', a, n, az))
            if in_OT(az) and in_TB(az):
                n_clos += 1
            else:
                bad.append(('CLOS', a, n, az))
    tot = len(otb) * len(NS)
    print(f"DESC (3.2a, target b): {n_desc}/{tot}")
    print(f"CLOS (3.3,  target a): {n_clos}/{tot}")

    # ---------- domain classification ----------
    domTv = [(a, dom(a)[1]) for a in pool if isinstance(dom(a), tuple)]
    domTv_ot = [(a, w) for (a, w) in domTv if in_OT(a)]
    domN = [a for a in pool if dom(a) == 'N']
    print(f"dom=T_w terms: {len(domTv)} (OT: {len(domTv_ot)}), dom=N terms: {len(domN)}")

    # small z-pools per w
    zpool_raw = [t for t in pool if sym_count(t) <= 3] + [[]]
    def zpool(w):
        return [z for z in zpool_raw if in_Tv(z, w)]

    # ---------- MONO (3.2b) - NO OT filter on a ----------
    n_mono = 0
    for (a, w) in domTv:
        if sym_count(a) > 4:
            continue
        zs = zpool(w)[:40]
        for z1 in zs:
            for z2 in zs:
                if lt_term(z1, z2):
                    if lt_term(bracket(a, z1), bracket(a, z2)):
                        n_mono += 1
                    else:
                        bad.append(('MONO', a, (z1, z2), None))
    print(f"MONO (3.2b, no OT):    {n_mono}/{n_mono + sum(1 for x in bad if x[0]=='MONO')}")

    # ---------- LB ----------
    n_lb = 0
    for (a, w) in domTv_ot:
        for z in zpool(w)[:60]:
            if le_term(z, bracket(a, z)):
                n_lb += 1
            else:
                bad.append(('LB', a, z, None))
    print(f"LB   (z <= a[z], OT):  {n_lb}/{n_lb + sum(1 for x in bad if x[0]=='LB')}")

    # ---------- DW0LT ----------
    n_dw = 0
    for (b, w) in domTv_ot:
        if lt_term([D(w, ZERO)], b):
            n_dw += 1
        else:
            bad.append(('DW0LT', b, w, None))
    print(f"DW0LT (D_w 0 < b, OT): {n_dw}/{n_dw + sum(1 for x in bad if x[0]=='DW0LT')}")

    # ---------- TOWER (kind-1 internals) ----------
    n_tow = n_tow_tot = 0
    for a in otb:
        if len(a) != 1 or is_zero(a[0][2]):
            continue
        _, v, b = a[0]
        db = dom(b)
        if not (isinstance(db, tuple) and v <= db[1]):
            continue
        w = db[1]
        xs = [[D(w, ZERO)]]
        for i in range(4):
            xs.append(bracket(b, [D(w, xs[-1])]))
        ok = True
        for i in range(len(xs) - 1):
            ok &= lt_term(xs[i], xs[i + 1])
        for x in xs:
            ok &= lt_term(x, b) and in_OT(x) and in_TB(x)
            ok &= all(lt_term(g, x) for g in G(v, x))          # CL: G_v x_i < x_i
            ok &= in_OT([D(w, x)])                              # z_i in OT
        n_tow_tot += 1
        if ok:
            n_tow += 1
        else:
            bad.append(('TOWER', a, None, None))
    print(f"TOWER (incr/OT/G_v):   {n_tow}/{n_tow_tot}")

    # ---------- TRI (3.6) with general z in dom(a) ----------
    cpool = [c for c in pool if sym_count(c) <= 4] + [[]]
    ot_small = [a for a in otb if sym_count(a) <= 4]
    n_tri = n_tri_tot = 0
    for a in ot_small:
        d = dom(a)
        if d == 'empty':
            continue
        if d == 'zero':
            zs = [[]]
        elif d == 'N':
            zs = [nat(n) for n in range(3)]
        else:
            zs = zpool(d[1])[:8]
        for z in zs:
            az = bracket(a, z)
            cands = [c for c in cpool if le_term(az, c) and le_term(c, a)]
            G0z = {0}  # placeholder; use list
            ok = True
            for u in range(MAX_IDX + 2):
                Gaz = G(u, az)
                Gz = G(u, z)
                for c in cands:
                    tgt = G(u, c) + Gz + [ZERO]
                    if not setle(Gaz, tgt):
                        ok = False
                        bad.append(('TRI', a, (z, u, c), az))
                        break
                if not ok:
                    break
            n_tri_tot += 1
            if ok:
                n_tri += 1
    print(f"TRI  (3.6 sandwich):   {n_tri}/{n_tri_tot}")

    # ---------- NONZERO ----------
    n_nz = 0
    for a in domN:
        for n in range(3):
            if not is_zero(bracket(a, nat(n))):
                n_nz += 1
            else:
                bad.append(('NONZERO', a, n, None))
    print(f"NONZERO (dom=N):       {n_nz}/{n_nz + sum(1 for x in bad if x[0]=='NONZERO')}")

    # ---------- report ----------
    if bad:
        print(f"\n*** {len(bad)} FAILURES ***")
        for tag, a, extra, az in bad[:20]:
            print(f"  [{tag}] a={fmt(a)} extra={extra if not isinstance(extra, tuple) else tuple(fmt(e) if isinstance(e, list) else e for e in extra)} a[z]={fmt(az) if az is not None else '-'}")
        sys.exit(1)
    print("\nALL CHECKS PASS")

def sym_count(t):
    return sum(1 + sym_count(p[2]) for p in t)

if __name__ == "__main__":
    main()
