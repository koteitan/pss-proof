import sys, itertools
sys.path.insert(0,'python')
import red_model as R

def transCondIII(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0) < R.entry(M,1,j1): return False   # need >=
    return R.adm(M,j0)

def transCondIV(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0) < R.entry(M,1,j1): return False
    return not R.adm(M,j0)

# stats
n_regime=0        # M in condIII regime with guard
n_brne_ok=0       # Br(Red(Pred(s84x_N M))) != []
cex=[]            # guard holds but Br == []
# also secondary: condIV regime (shared)
n_regime4=0; n_brne4_ok=0; cex4=[]

def check(M, branch=3):
    global n_regime,n_brne_ok,n_regime4,n_brne4_ok
    j1=R.Lng(M)-1
    if not (1 < j1): return
    if not R.reduced(M): return
    if not R.monoT(M): return
    if not R.hasParent(M,1,j1): return
    if branch==3:
        if not transCondIII(M): return
    else:
        if not transCondIV(M): return
    jm2=R.parent(M,1,j1)
    jm3=R.Adm(M,jm2)
    if not (jm3 < jm2): return          # guard
    # Pred(s84x_N M) = seg M jm3 (j1-1)
    if j1-1 < jm3: return
    try:
        RNp=R.Red(R.seg(M,jm3,j1-1))
    except Exception:
        return
    brne = len(R.Br(RNp))>0
    if branch==3:
        n_regime+=1
        if brne: n_brne_ok+=1
        elif len(cex)<12: cex.append((R.fmt(M),jm2,jm3,R.fmt(R.seg(M,jm3,j1-1)),R.fmt(RNp)))
    else:
        n_regime4+=1
        if brne: n_brne4_ok+=1
        elif len(cex4)<12: cex4.append((R.fmt(M),jm2,jm3,R.fmt(R.seg(M,jm3,j1-1)),R.fmt(RNp)))

# ---- Corpus 1: constructive base + tails ----
V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
seen=set()
def try_M(M):
    key=tuple(M)
    if key in seen: return
    seen.add(key)
    try:
        if not R.is_standard(M): return
    except Exception:
        return
    check(M,3); check(M,4)

n_constr=0
for base_len in range(2,7):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,5):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>12: continue
            try_M(M); n_constr+=1

print("== Corpus 1 (constructive) done ==")
print("condIII: regime(guard)=",n_regime,"Br!=[] ok=",n_brne_ok, "CEX(guard&Br=[])=",len(cex))
print("condIV : regime(guard)=",n_regime4,"Br!=[] ok=",n_brne4_ok,"CEX=",len(cex4))

# ---- Corpus 2: oper-orbit BFS ----
# seeds: small standard mono reduced sequences; repeatedly apply oper(.,n) for n in 1..4,
# collect all intermediate standard sequences up to length 14; also Pred-images.
from collections import deque
seeds=[]
for base_len in range(2,5):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>7: continue
            try:
                if R.is_standard(M) and R.reduced(M): seeds.append(tuple(M))
            except Exception: pass
seeds=list(dict.fromkeys(seeds))
visited=set()
q=deque(seeds)
bfs_checked=0
while q and len(visited)<200000:
    M=list(q.popleft())
    key=tuple(M)
    if key in visited: continue
    visited.add(key)
    if 2 <= R.Lng(M) <= 16:
        try:
            if R.is_standard(M):
                check(M,3); check(M,4); bfs_checked+=1
        except Exception:
            pass
    if R.Lng(M) > 16: continue
    for n in range(1,5):
        try:
            Mn=R.oper(M,n)
        except Exception:
            continue
        if 1 < R.Lng(Mn) <= 16 and tuple(Mn) not in visited:
            q.append(tuple(Mn))
    # also Pred image
    if R.Lng(M)>1:
        Mp=R.Pred(M)
        if tuple(Mp) not in visited:
            q.append(tuple(Mp))

print("== Corpus 2 (oper-orbit BFS) done ==  visited=",len(visited)," checked-standard=",bfs_checked)
print("condIII: regime(guard)=",n_regime,"Br!=[] ok=",n_brne_ok, "CEX(guard&Br=[])=",len(cex))
print("condIV : regime(guard)=",n_regime4,"Br!=[] ok=",n_brne4_ok,"CEX=",len(cex4))
if cex:
    print("--- condIII CEX (guard holds but Br(Red(Pred(s84x_N)))=[]): (M,jm2,jm3,Pred(s84x_N),RNp) ---")
    for e in cex: print("   ",e)
if cex4:
    print("--- condIV CEX ---")
    for e in cex4: print("   ",e)
