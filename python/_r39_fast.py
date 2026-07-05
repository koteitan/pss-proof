import sys, itertools
sys.path.insert(0,'python')
import red_model as R
from collections import deque

# ---- memoize hot functions (key on tuple-of-tuples) ----
def _memo(fn):
    cache={}
    def w(M,*a):
        if a: return fn(M,*a)
        k=tuple(map(tuple,M))
        if k in cache: return cache[k]
        v=fn(M); cache[k]=v; return v
    return w
_origRed=R.Red
_redc={}
def Red_memo(M,depth=0):
    k=tuple(map(tuple,M))
    if k in _redc: return _redc[k]
    v=_origRed(M,depth); _redc[k]=v; return v
R.Red=Red_memo
R.TrMax=_memo(R.TrMax)
R.Br=_memo(R.Br)
R.P=_memo(R.P)
R.monoT=_memo(R.monoT)

def transCond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return (False,False)
    if not R.hasParent(M,0,j1): return (False,False)
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0) < R.entry(M,1,j1): return (False,False)
    a=R.adm(M,j0)
    return (a, not a)

def descending_brs(Q):
    n=len(Q)
    for J0 in range(n):
        for J1 in range(J0,n):
            if R.entry(Q[J0],0,0) < R.entry(Q[J1],0,0): return False
            if R.entry(Q[J0],0,0)==R.entry(Q[J1],0,0) and R.entry(Q[J0],1,0) < R.entry(Q[J1],1,0):
                return False
    return True

def cfbx_reg(m,N):
    if R.Red(N)!=N: return False
    if not R.monoT(N): return False
    b=R.Br(N)
    if len(b)==0: return False
    last=len(b)-1
    jl=R.Joints(N)[last]; fn=R.FirstNodes(N)[last]
    if m < jl: return True
    if m==jl and R.entry(N,0,fn)==R.entry(N,1,fn) and descending_brs(b): return True
    return False

st={3:dict(reg=0,g=0,ng=0,brne=0,cfx=0,B2=[],B4=[]),
    4:dict(reg=0,g=0,ng=0,brne=0,cfx=0,B2=[],B4=[])}

def check(M):
    j1=R.Lng(M)-1
    if not(1<j1): return
    if R.Red(M)!=M: return
    if not R.monoT(M): return
    if not R.hasParent(M,1,j1): return
    c3,c4=transCond34(M)
    if not(c3 or c4): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
    if j1-1<jm3: return
    RNp=R.Red(R.seg(M,jm3,j1-1))
    d=jm2-jm3; g=jm3<jm2; bne=len(R.Br(RNp))>0; cf=cfbx_reg(d,RNp)
    for br in ([3] if c3 else [])+([4] if c4 else []):
        s=st[br]; s['reg']+=1
        if g:s['g']+=1
        else:s['ng']+=1
        if bne:s['brne']+=1
        if cf:s['cfx']+=1
        if bne and not g and len(s['B2'])<25:
            s['B2'].append((R.fmt(M),jm2,jm3,d,R.fmt(RNp),cf))
        if bne and not cf and len(s['B4'])<25:
            s['B4'].append((R.fmt(M),jm2,jm3,d,R.fmt(RNp),g,R.Joints(RNp)))

def report(tag):
    print("==",tag,"==",flush=True)
    for br in (3,4):
        s=st[br]
        print(f" cond{br}: reg={s['reg']} g={s['g']} !g={s['ng']} Br!=[]={s['brne']} "
              f"cfbx={s['cfx']} B2fail={len(s['B2'])} B4fail={len(s['B4'])}",flush=True)

# ---- seeds (verified standard once) ----
V=4
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
seeds=[]
for bl in range(2,4):
    base=R.diagSeq(0,bl-1)
    for t in range(1,3):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>5: continue
            if R.Red(M)==M and R.monoT(M):
                try:
                    if R.is_standard(M): seeds.append(tuple(M))
                except Exception: pass
seeds=list(dict.fromkeys(seeds))
print("seeds",len(seeds),flush=True)
for s in seeds: check(list(s))
report("seeds")

# ---- oper-orbit BFS (ST_PS closure => no per-node is_standard) ----
visited=set(); q=deque(seeds); MAXLEN=16
while q and len(visited)<300000:
    M=list(q.popleft()); k=tuple(M)
    if k in visited: continue
    visited.add(k)
    if len(visited)%25000==0: report(f"bfs{len(visited)}")
    if 2<=R.Lng(M)<=MAXLEN: check(M)
    if R.Lng(M)>MAXLEN: continue
    for n in range(1,5):
        try: Mn=R.oper(M,n)
        except Exception: continue
        if 1<R.Lng(Mn)<=MAXLEN and tuple(Mn) not in visited: q.append(tuple(Mn))
    if R.Lng(M)>1:
        Mp=R.Pred(M)
        if tuple(Mp) not in visited: q.append(tuple(Mp))
report(f"FINAL visited={len(visited)}")
for br in (3,4):
    s=st[br]
    if s['B2']:
        print(f"-- cond{br} B2fail (Br!=[]&!guard) (M,jm2,jm3,d,RNp,cfbx) --",flush=True)
        for e in s['B2']: print("  ",e,flush=True)
    if s['B4']:
        print(f"-- cond{br} B4fail (Br!=[]&!cfbx) (M,jm2,jm3,d,RNp,guard,Joints) --",flush=True)
        for e in s['B4']: print("  ",e,flush=True)
print("DONE",flush=True)
