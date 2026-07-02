#!/usr/bin/env python3
"""Verify: for any single-principal body b with domB b = TBv u, evaluating
operB b z recurses ONLY via else/(iii) branch (and base [].2), never xseq, never mult.
And operB b z is independent of z's recursion structure (terminates by size b)."""
import sys; sys.path.insert(0,'.')
from _xseq_measure import D, ZERO, is_zero, domB, numNat
import math
INF=math.inf

def branch_trace(a, z, trace):
    """Record which branch operB a z takes at each recursion step."""
    if is_zero(a): trace.append('zero-base'); return
    if len(a)>=2: trace.append('multi'); branch_trace([a[-1]], z, trace); return
    _,v,b = a[0]
    if is_zero(b):
        if v==0: trace.append('base-v0')
        elif v==INF: trace.append('base-inf')
        else: trace.append('base-Tv([].2)')
        return
    db = domB(b)
    if db==('zero',): trace.append('MULT'); branch_trace(b, ZERO, trace); return
    if db[0]=='Tv' and v<=db[1]: trace.append('XSEQ'); return
    trace.append('else-iii'); branch_trace(b, z, trace)

def spines(depth, maxv=4):
    if depth==0: yield ZERO; return
    for v in range(maxv+1):
        for sub in spines(depth-1, maxv): yield [D(v,sub)]

violations=0; checked=0
for b in spines(5, 4):
    if is_zero(b): continue
    db = domB(b)
    if not (db[0]=='Tv'): continue
    # operB b z for some z; check trace contains no XSEQ, no MULT
    tr=[]
    branch_trace(b, [D(0,ZERO)]*3, tr)
    checked += 1
    if 'XSEQ' in tr or 'MULT' in tr:
        violations += 1
        if violations<=5:
            from _xseq_measure import fmt
            print("VIOLATION b=",fmt(b)," dom=",db," trace=",tr)
print(f"checked={checked} TBv-bodies, violations(XSEQ/MULT inside operB b)={violations}")

# Also: confirm operB b z trace is the SAME regardless of z (else-iii ignores z until base)
diffz=0
for b in spines(5,4):
    if is_zero(b): continue
    if domB(b)[0]!='Tv': continue
    t1=[]; branch_trace(b,[D(0,ZERO)]*0,t1)
    t2=[]; branch_trace(b,[D(0,ZERO)]*7,t2)
    # branch structure identical (base-Tv returns z but branch sequence same)
    if [x for x in t1] != [x for x in t2]: diffz+=1
print(f"branch trace z-independent for all TBv bodies: {diffz==0} (diffs={diffz})")
