import itertools
from red_model import Red, Lng, entry, multiT, monoT, zeroT
from red_charac import RedCondA, RedCondB

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L):
            yield list(M)

# monoT-core: M in T_PS, monoT M, entry00=0, entry10=0
maxlen=4; maxe=3
total=0; cnt=0; fails=0
for M in enum(maxlen,maxe):
    if not monoT(M): continue
    if entry(M,0,0)!=0 or entry(M,1,0)!=0: continue
    total+=1
    a=RedCondA(M); b=RedCondB(M)
    if a and b:
        cnt+=1
        r=Red(M)
        if r!=M:
            fails+=1
            print("COUNTEREXAMPLE",M,"Red=",r)
print(f"monoT-core total={total}, A&B={cnt}, Red!=M fails={fails}")
