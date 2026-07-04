import sys, itertools
sys.path.insert(0,'python')
import red_model as R
# M0RUN: for M in ST_PS with hasParent M 1 (Lng-1) and adm M jm2 (jm2=parent M 1 (Lng-1)),
#  entry M 1 jm2 < entry M 1 (jm2+1).
# Build ST_PS by oper closure from diagSeqs.
def gen_STPS(maxlen=16, vcap=7, steps=5):
    seen=set(); frontier=[]
    for u in range(vcap):
        for v in range(u,vcap):
            M=tuple(R.diagSeq(u,v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    allM=list(frontier)
    for _ in range(steps):
        nf=[]
        for M in frontier:
            for n in range(1,5):
                try: Mn=R.oper(M,n)
                except Exception: continue
                if 1<len(Mn)<=maxlen:
                    t=tuple(Mn)
                    if t not in seen: seen.add(t); nf.append(Mn); allM.append(Mn)
        frontier=nf
    return allM
st={'tot':0,'admedge':0,'M0RUN':0,'hard_notle0':0,'hard_M0RUN':0,
    'diag_step':0,'jm2par1_jm2p1':0}
cex=[]
for M in gen_STPS():
    if R.Lng(M)<2: continue
    j1=R.Lng(M)-1
    if not R.hasParent(M,1,j1): continue
    jm2=R.parent(M,1,j1)
    if R.Adm(M,jm2)!=jm2: continue  # adm M jm2 (admissible)
    st['admedge']+=1
    if jm2+1>=R.Lng(M): continue
    st['tot']+=1
    e1jm2=R.entry(M,1,jm2); e1jm2p1=R.entry(M,1,jm2+1)
    ok = e1jm2<e1jm2p1
    if ok: st['M0RUN']+=1
    notle0 = not R.le0(M,jm2+1,j1)
    if notle0:
        st['hard_notle0']+=1
        if ok: st['hard_M0RUN']+=1
    # diagonal step jm2->jm2+1?
    if R.entry(M,0,jm2+1)==R.entry(M,0,jm2)+1 and e1jm2p1==e1jm2+1: st['diag_step']+=1
    if R.hasParent(M,1,jm2+1) and R.parent(M,1,jm2+1)==jm2: st['jm2par1_jm2p1']+=1
    if not ok and len(cex)<6: cex.append((R.fmt(M),jm2,e1jm2,e1jm2p1))
print(st)
for c in cex: print("CEX",c)
