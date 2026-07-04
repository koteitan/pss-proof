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

def reach0(M):
    n=R.Lng(M)
    Rm=[[i==j for j in range(n)] for i in range(n)]
    edges=[(a,b) for a in range(n) for b in range(n) if R.nextrel0(M,a,b)]
    changed=True
    while changed:
        changed=False
        for (c,d) in edges:
            for a in range(n):
                if Rm[a][c] and not Rm[a][d]:
                    Rm[a][d]=True; changed=True
    return Rm

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

st={'host':0,'ANC0_true':0,'consec_window':0,'row0_consec':0,'deep':0,'deep_ANC0':0}
cex=[]
maxL=0
for M in gen_STPS():
    L=R.Lng(M)
    if L<3: continue
    j1=L-1
    if not R.hasParent(M,1,j1): continue
    if not R.hasParent(M,0,j1): continue
    if not (1<j1): continue
    if not (condIII(M) or condIV(M)): continue
    jm2=R.parent(M,1,j1)
    j0=R.parent(M,0,j1)
    if jm2+1>=L: continue
    Rm=reach0(M)
    st['host']+=1
    maxL=max(maxL,L)
    deep = L>=10
    if deep: st['deep']+=1
    anc0 = Rm[jm2+1][j0]
    if anc0:
        st['ANC0_true']+=1
        if deep: st['deep_ANC0']+=1
    else:
        if len(cex)<8: cex.append(("ANC0_FALSE",R.fmt(M),'jm2',jm2,'j0',j0))
    win_ok = all(R.nextrel0(M,k,k+1) for k in range(jm2,j0))
    if win_ok: st['consec_window']+=1
    row0_ok = all(R.entry(M,0,k+1)==R.entry(M,0,k)+1 for k in range(jm2,j0))
    if row0_ok: st['row0_consec']+=1
    if anc0 and not win_ok and len(cex)<14:
        cex.append(("ANC0_but_notconsec",R.fmt(M),'jm2',jm2,'j0',j0,
                    'row0win',[R.entry(M,0,k) for k in range(jm2,j0+1)]))

print("maxL",maxL)
print(st)
for c in cex: print("CEX",c)
