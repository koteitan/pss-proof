#!/usr/bin/env python3
"""Audit for the scb image-existence lemma (§7.3 value-invariant prerequisite):
  scb_decomp t s (flat c) b  with c principal, c' principal
  ==> s @ flat c' @ b  is in the image of flatBT.
Result 2026-06-11: 0/7,224 failures (BT terms depth<=3, indices {0,1}).
Intuition: b all-RP + balanced principal c pin the occurrence to a real
subterm position (paren balance)."""
from trans_model import flatBT, unflatBT, isPTB_str, ZB

def terms(d):
    if d == 0: return [ZB]
    sub = terms(d-1)
    out = [ZB]
    ps = []
    for v in (0, 1):
        for t in sub: ps.append(('D', v, t))
    for p in ps: out.append(('T', [p]))
    for p1 in ps[:8]:
        for p2 in ps[:8]: out.append(('T', [p1, p2]))
    seen = set(); res = []
    for t in out:
        k = str(t)
        if k not in seen: seen.add(k); res.append(t)
    return res

def main():
    TS = terms(3)
    PR = [t for t in TS if len(t[1]) == 1]
    bad = tot = 0
    for t in TS[:400]:
        f = flatBT(t)
        for c in PR:
            fc = flatBT(c); m = len(fc)
            for i in range(len(f) - m + 1):
                if f[i:i+m] != fc: continue
                s, b = f[:i], f[i+m:]
                if t != ZB and not isPTB_str(fc): continue
                if not all(x == ')' for x in b): continue
                for c2 in PR[:12]:
                    tot += 1
                    try: unflatBT(s + flatBT(c2) + b)
                    except Exception:
                        bad += 1
                        print('IMAGE FAIL', t, s, b, c2)
    print('replacements tested:', tot, 'image failures:', bad)

if __name__ == '__main__':
    main()
