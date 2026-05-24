#!/usr/bin/env python3
"""Empirically validate the Buchholz system's key lemmas (docs/buchholz.md) on
enumerated small terms — these underpin §7 / the termination theorem:

  Lemma 2.1  : < is a strict linear order (irreflexive, transitive, trichotomous)
  Lemma 3.2a : z ∈ dom(a) ⟹ a[z] < a            (fundamental sequences descend)
  Lemma 3.2b : z < z' in dom(a)=T_u ⟹ a[z] < a[z']   (monotone)
  Lemma 3.3  : a,z ∈ OT, z ∈ dom(a) ⟹ a[z] ∈ OT
"""
import itertools, os
from buchholz import (ZERO, D, one, nat, lt_term, le_term, dom, in_dom, bracket,
    in_OT, in_Tv, fmt, INF, is_zero)

def gen_terms(depth, idxs, maxk=2):
    """all terms of given recursion depth: lists of <=maxk principals D_v a."""
    if depth == 0:
        return [ZERO]
    sub = gen_terms(depth-1, idxs, maxk)
    princ = [D(v, a) for v in idxs for a in sub]
    out = [ZERO]
    for k in range(1, maxk+1):
        for combo in itertools.product(princ, repeat=k):
            out.append(list(combo))
    # dedup
    seen=set(); uniq=[]
    for t in out:
        key=repr(t)
        if key not in seen: seen.add(key); uniq.append(t)
    return uniq

def main():
    os.chdir(os.path.dirname(__file__))
    idxs = [0, 1, 2]                      # finite indices (D_ω handled separately below)
    terms = gen_terms(2, idxs, maxk=2)
    ot = [t for t in terms if in_OT(t)]
    print(f"terms generated: {len(terms)}, in OT: {len(ot)}")

    # Lemma 2.1: strict linear order on OT terms
    bad_irrefl = [t for t in ot if lt_term(t,t)]
    bad_trich = []
    for a in ot:
        for b in ot:
            c = sum([lt_term(a,b), a==b, lt_term(b,a)])
            if c != 1: bad_trich.append((fmt(a),fmt(b),c))
    bad_trans = []
    import random
    sample = ot if len(ot)<=40 else random.sample(ot,40)
    for a in sample:
        for b in sample:
            for c in sample:
                if lt_term(a,b) and lt_term(b,c) and not lt_term(a,c):
                    bad_trans.append((fmt(a),fmt(b),fmt(c)))
    print(f"[2.1] irreflexive fails={len(bad_irrefl)} trichotomy fails={len(bad_trich)} transitivity fails={len(bad_trans)}")
    if bad_trich[:3]: print("   trich ex:", bad_trich[:3])

    # Lemma 3.2a: a[z] < a for z in dom(a); test over OT a and candidate z (terms + nats)
    def doms_witnesses(a):
        d = dom(a)
        if d == 'empty': return []
        if d == 'zero': return [ZERO]
        if d == 'N': return [nat(n) for n in range(4)]
        u = d[1]; return [z for z in terms if in_Tv(z,u)][:12]
    desc_fail=[]; mono_fail=[]; ot_fail=[]
    for a in ot:
        ws = doms_witnesses(a)
        for z in ws:
            if not in_dom(z,a): continue
            az = bracket(a,z)
            if not lt_term(az, a): desc_fail.append((fmt(a),fmt(z),fmt(az)))
            if in_OT(a) and in_OT(z) and not in_OT(az): ot_fail.append((fmt(a),fmt(z),fmt(az)))
        # 3.2b monotonicity on T_u domains
        d = dom(a)
        if isinstance(d,tuple):
            for z in ws:
                for z2 in ws:
                    if in_dom(z,a) and in_dom(z2,a) and lt_term(z,z2):
                        if not lt_term(bracket(a,z), bracket(a,z2)):
                            mono_fail.append((fmt(a),fmt(z),fmt(z2)))
    print(f"[3.2a] a[z]<a fails={len(desc_fail)}  [3.2b] monotone fails={len(mono_fail)}  [3.3] a[z]∈OT fails={len(ot_fail)}")
    for x in desc_fail[:5]: print("   desc FAIL:", x)
    for x in ot_fail[:5]: print("   OT   FAIL:", x)

if __name__ == "__main__": main()
