#!/usr/bin/env python3
"""Corrected-operB overlay on _r15_vx_lib.

_r15_vx_lib's operB/xseq encode the OLD (wrong) reading of footnote [30]
(a[n] = D_v x_n, x_i = b[D_u x_{i-1}]).  The CORRECT Buchholz rule, now in
pss_paper.thy 761-780 and python/buchholz.py, is

    x_0 = D_u 0,   x_i = D_u b[x_{i-1}],   a[n] = D_v b[x_n].

This module redefines operB/xseq accordingly and monkey-patches them back into
_r15_vx_lib so vx.operB_iter0 (and anything else in the lib) uses them.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _r15_vx_lib as vx
from trans_model import Dpt, addBT, ZB
from _r15_vx_lib import domB, multBT, numNat, numBT

INF = float('inf')


def operB(a, z):
    ps = a[1]
    if not ps:
        return ZB
    if len(ps) == 1:
        _, v, b = ps[0]
        if b == ZB:
            if v == 0: return ZB
            if v == INF: return Dpt(numNat(z) + 1, ZB)
            return z
        db = domB(b)
        if db == 'ZERO':
            return multBT(Dpt(v, operB(b, ZB)), numNat(z) + 1)
        if isinstance(db, tuple) and db[0] == 'TB' and v <= db[1]:
            # ([].4)(ii), [Buc2] form:  a[n] = D_v b[x_n]
            return Dpt(v, operB(b, xseq(b, db[1], numNat(z))))
        return Dpt(v, operB(b, z))
    return addBT(('T', ps[:-1]), operB(('T', [ps[-1]]), z))


def xseq(b, u, i):
    if i == 0:
        return Dpt(u, ZB)                      # x_0 = D_u 0
    return Dpt(u, operB(b, xseq(b, u, i - 1)))  # x_i = D_u b[x_{i-1}]


def operB_iter0(t, k):
    for _ in range(k):
        t = operB(t, numBT(0))
    return t


vx.operB, vx.xseq, vx.operB_iter0 = operB, xseq, operB_iter0
