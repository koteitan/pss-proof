import sys
sys.path.insert(0,'python')
import red_model as R

def gen_STPS(maxlen=16, vcap=6, steps=6, cap=8000):
    seen=set(); frontier=[]
    for u in range(vcap):
        for v in range(u,vcap):
            M=tuple(R.diagSeq(u,v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    allM=list(frontier)
    for _ in range(steps):
        nf=[]
        for M in frontier:
            for n in range(1,6):
                try: Mn=R.oper(M,n)
                except Exception: continue
                if 1<len(Mn)<=maxlen:
                    t=tuple(Mn)
                    if t not in seen and len(seen)<cap:
                        seen.add(t); nf.append(Mn); allM.append(Mn)
        frontier=nf
        if len(seen)>=cap: break
    return allM

def condIII(M):
    j1=R.Lng(M)-1
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    return R.entry(M,1,j1)>0 and R.entry(M,1,j0)>=R.entry(M,1,j1) and R.adm(M,j0)
def condIV(M):
    j1=R.Lng(M)-1
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    return R.entry(M,1,j1)>0 and R.entry(M,1,j0)>=R.entry(M,1,j1) and (not R.adm(M,j0))

# Additional structural checks over whole corpus:
#  (A) for k in (jm2, j0]: is nadm M k? (non-admissible run?)
#  (B) parent M 0 (k+1) == k for k in [jm2, j0)?  (backward-unique row0 chain)
#  (C) is [jm2+1, j0] contained in the nadm-run (Adm M j0' ... )?
st={'host':0,'III':0,'IV':0,
    'win_nadm':0,'win_par0':0,'jm2_nadm':0,'j0_adm':0,
    'run_covers':0}
examples=[]
for M in gen_STPS():
    L=R.Lng(M)
    if L<3: continue
    j1=L-1
    if not R.hasParent(M,1,j1): continue
    if not R.hasParent(M,0,j1): continue
    if not (1<j1): continue
    ciii=condIII(M); civ=condIV(M)
    if not (ciii or civ): continue
    jm2=R.parent(M,1,j1); j0=R.parent(M,0,j1)
    if jm2+1>=L: continue
    st['host']+=1
    if ciii: st['III']+=1
    if civ: st['IV']+=1
    # (A) nadm on (jm2, j0]
    win_nadm = all(R.nadm(M,k) for k in range(jm2+1,j0+1))
    if win_nadm: st['win_nadm']+=1
    # (B) parent0
    win_par0 = all(R.hasParent(M,0,k+1) and R.parent(M,0,k+1)==k for k in range(jm2,j0))
    if win_par0: st['win_par0']+=1
    if R.nadm(M,jm2): st['jm2_nadm']+=1
    if R.adm(M,j0): st['j0_adm']+=1
    # (C) does the nadm-run of some anchor cover [jm2+1,j0]? Check Adm M j0-run
    # Adm-run of position p: (Adm M p, p]. Take p=j0 if nadm else skip.
    if len(examples)<6 and L>=11:
        rows=[]
        for k in range(max(0,jm2-1), min(L,j0+2)):
            rows.append((k,R.entry(M,0,k),R.entry(M,1,k),'adm' if R.adm(M,k) else 'nadm'))
        examples.append((R.fmt(M),'jm2',jm2,'j0',j0,'III' if ciii else 'IV',rows))
print(st)
for e in examples:
    print("EX",e[0])
    print("   jm2",e[2],"j0",e[4],e[5])
    for r in e[6]: print("   k=%d row0=%d row1=%d %s"%r)
