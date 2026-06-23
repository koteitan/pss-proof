import itertools
from red_model import (Red, Lng, entry, multiT, monoT, zeroT, TrMax, Br, seg, diagSeq)
from red_charac import RedCondA, RedCondB
def enum(ml,me):
    cols=[(a,b) for a in range(me+1) for b in range(me+1)]
    for L in range(1,ml+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
fail=0; tot=0
for M in enum(4,3):
    if not monoT(M): continue
    if entry(M,0,0)!=0 or entry(M,1,0)!=0: continue
    if not (RedCondA(M) and RedCondB(M)): continue
    if TrMax(M)==Lng(M)-1: continue
    tot+=1
    t=TrMax(M)
    if diagSeq(0,t)!=seg(M,0,t): fail+=1
print(f"core-nontrunk A&B M tot={tot}, diagSeq 0 TrMax != seg M 0 TrMax: {fail}")
fail2=0
for M in enum(4,3):
    if not monoT(M): continue
    if entry(M,0,0)!=0 or entry(M,1,0)!=0: continue
    if not (RedCondA(M) and RedCondB(M)): continue
    if TrMax(M)==Lng(M)-1: continue
    t=TrMax(M)
    S=seg(M,0,t)
    if not (TrMax(S)==Lng(S)-1 and monoT(S) and RedCondA(S)): fail2+=1
print(f"slice S=seg M 0 t fails (trunk/mono/condA): {fail2}")
