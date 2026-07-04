import sys
sys.path.insert(0,'python')
import red_model as R

def gen_STPS(maxlen=15, vcap=6, steps=6, cap=6000):
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

def condIIIorIV(M):
    j1=R.Lng(M)-1
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    return R.entry(M,1,j1)>0 and R.entry(M,1,j0)>=R.entry(M,1,j1)

st={'host':0,'d0_eq_w':0,'lastblock_consec':0,'win_consec':0}
cex=[]
for M in gen_STPS():
    L=R.Lng(M)
    if L<3: continue
    j1=L-1
    if not R.hasParent(M,1,j1): continue
    if not R.hasParent(M,0,j1): continue
    if not (1<j1): continue
    if not condIIIorIV(M): continue
    jm2=R.parent(M,1,j1); j0=R.parent(M,0,j1)
    if jm2+1>=L: continue
    st['host']+=1
    d0 = R.entry(M,0,j1)-R.entry(M,0,jm2)
    w = j1 - jm2
    if d0==w: st['d0_eq_w']+=1
    else:
        if len(cex)<8: cex.append(("d0!=w",R.fmt(M),'d0',d0,'w',w,'jm2',jm2))
    # full last block [jm2, j1] consecutive row-0
    lbc = all(R.entry(M,0,jm2+i)==R.entry(M,0,jm2)+i for i in range(0,j1-jm2+1))
    if lbc: st['lastblock_consec']+=1
    winc = all(R.entry(M,0,k+1)==R.entry(M,0,k)+1 for k in range(jm2,j0))
    if winc: st['win_consec']+=1
print(st)
for c in cex: print("CEX",c)
