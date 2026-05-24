#!/usr/bin/env python3
import itertools, os
from red_model import Red, red_le_holds, fmt, Lng, entry, P, Pcut, multiT, monoT, zeroT, le0, leR, nextR

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L):
            yield list(M)

def main():
    os.chdir(os.path.dirname(__file__))
    mono_fail=[]; multi_fail=[]; zero_fail=[]
    mono_n=multi_n=zero_n=0
    for M in enum(4,2):
        r,info=red_le_holds(M)
        ok=(r is True)
        if zeroT(M):
            zero_n+=1
            if not ok: zero_fail.append((M,info))
        elif monoT(M):
            mono_n+=1
            if not ok: mono_fail.append((M,info))
        else:
            multi_n+=1
            if not ok: multi_fail.append((M,info))
    print(f"zero:  n={zero_n} fail={len(zero_fail)}")
    print(f"mono:  n={mono_n} fail={len(mono_fail)}")
    print(f"multi: n={multi_n} fail={len(multi_fail)}")
    print("mono failures (first 30):")
    for (M,info) in mono_fail[:30]:
        print("  ",fmt(M),"Red=",fmt(info[3]),"at",info[:3])

if __name__=="__main__": main()
