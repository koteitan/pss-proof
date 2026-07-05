import sys, itertools
sys.path.insert(0,'python')
import red_model as R
from collections import deque

def transCondIII(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0) < R.entry(M,1,j1): return False
    return R.adm(M,j0)

def transCondIV(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    if R.entry(M,1,j0) < R.entry(M,1,j1): return False
    return not R.adm(M,j0)

def descending_brs(Q):
    n=len(Q)
    for J0 in range(n):
        for J1 in range(J0,n):
            if R.entry(Q[J0],0,0) < R.entry(Q[J1],0,0): return False
            if R.entry(Q[J0],0,0)==R.entry(Q[J1],0,0) and R.entry(Q[J0],1,0) < R.entry(Q[J1],1,0):
                return False
    return True

def cfbx_reg(m,N):
    if not R.reduced(N): return False
    if not R.monoT(N): return False
    b=R.Br(N)
    if len(b)==0: return False
    last=len(b)-1
    jl=R.Joints(N)[last]; fn=R.FirstNodes(N)[last]
    if m < jl: return True
    if m==jl and R.entry(N,0,fn)==R.entry(N,1,fn) and descending_brs(b): return True
    return False

# counters, per branch
stat={3:dict(regime=0, guard=0, nguard=0,
             B1_fail=[],      # guard & Br==[]  (Route1 REGSP false)
             B2_fail=[],      # Br!=[] & !guard (crg REGSP would need d=0 cfbx_reg)
             B4_fail=[],      # Br!=[] & !cfbx_reg (crg REGSP TRUE-target fails)
             n_brne=0, n_cfbx=0),
      4:dict(regime=0, guard=0, nguard=0, B1_fail=[], B2_fail=[], B4_fail=[],
             n_brne=0, n_cfbx=0)}

def check(M,branch):
    j1=R.Lng(M)-1
    if not (1<j1): return
    if not R.reduced(M): return
    if not R.monoT(M): return
    if not R.hasParent(M,1,j1): return
    if branch==3:
        if not transCondIII(M): return
    else:
        if not transCondIV(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
    if j1-1 < jm3: return
    try: RNp=R.Red(R.seg(M,jm3,j1-1))
    except Exception: return
    d=jm2-jm3
    brne=len(R.Br(RNp))>0
    guard=jm3<jm2
    s=stat[branch]
    s['regime']+=1
    if guard: s['guard']+=1
    else: s['nguard']+=1
    if brne: s['n_brne']+=1
    cf=cfbx_reg(d,RNp)
    if cf: s['n_cfbx']+=1
    # B1: guard => Br!=[]
    if guard and not brne and len(s['B1_fail'])<15:
        s['B1_fail'].append((R.fmt(M),jm2,jm3,R.fmt(RNp)))
    # B2: Br!=[] => guard  (equiv !guard => Br==[])
    if brne and not guard and len(s['B2_fail'])<15:
        s['B2_fail'].append((R.fmt(M),jm2,jm3,d,R.fmt(RNp)))
    # B4: Br!=[] => cfbx_reg
    if brne and not cf and len(s['B4_fail'])<15:
        s['B4_fail'].append((R.fmt(M),jm2,jm3,d,R.fmt(RNp),R.Joints(RNp),R.FirstNodes(RNp)))

# ---- seeds: standard reduced mono, verified once (SMALL; depth via oper closure) ----
V=4
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
seeds=[]
for base_len in range(2,4):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,3):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>5: continue
            try:
                if R.reduced(M) and R.monoT(M) and R.is_standard(M):
                    seeds.append(tuple(M))
            except Exception: pass
seeds=list(dict.fromkeys(seeds))
print("seeds:",len(seeds), flush=True)

# constructive check on seeds directly
for s in seeds:
    check(list(s),3); check(list(s),4)
print("== after seeds (constructive) ==")
for br in (3,4):
    s=stat[br]
    print(f" cond{br}: regime={s['regime']} guard={s['guard']} !guard={s['nguard']} "
          f"Br!=[]={s['n_brne']} cfbx_ok={s['n_cfbx']} "
          f"B1fail={len(s['B1_fail'])} B2fail={len(s['B2_fail'])} B4fail={len(s['B4_fail'])}")

# ---- oper-orbit BFS: closure of standardness => skip per-node is_standard ----
visited=set()
q=deque(seeds)
MAXLEN=16
while q and len(visited)<250000:
    M=list(q.popleft())
    key=tuple(M)
    if key in visited: continue
    visited.add(key)
    if len(visited)%20000==0:
        print("  bfs visited",len(visited),"cIII regime",stat[3]['regime'],flush=True)
    if 2<=R.Lng(M)<=MAXLEN:
        # M standard (closure); need reduced for regime -> check() filters reduced
        check(M,3); check(M,4)
    if R.Lng(M)>MAXLEN: continue
    for n in range(1,5):
        try: Mn=R.oper(M,n)
        except Exception: continue
        if 1<R.Lng(Mn)<=MAXLEN and tuple(Mn) not in visited:
            q.append(tuple(Mn))
    if R.Lng(M)>1:
        Mp=R.Pred(M)
        if tuple(Mp) not in visited: q.append(tuple(Mp))

print("== after oper-orbit BFS == visited=",len(visited))
for br in (3,4):
    s=stat[br]
    print(f" cond{br}: regime={s['regime']} guard={s['guard']} !guard={s['nguard']} "
          f"Br!=[]={s['n_brne']} cfbx_ok={s['n_cfbx']} "
          f"B1fail={len(s['B1_fail'])} B2fail={len(s['B2_fail'])} B4fail={len(s['B4_fail'])}")
for br in (3,4):
    s=stat[br]
    if s['B2_fail']:
        print(f"--- cond{br} B2_fail (Br!=[] & !guard): (M,jm2,jm3,d,RNp) ---")
        for e in s['B2_fail']: print("   ",e)
    if s['B4_fail']:
        print(f"--- cond{br} B4_fail (Br!=[] & !cfbx_reg): (M,jm2,jm3,d,RNp,Joints,FN) ---")
        for e in s['B4_fail']: print("   ",e)
