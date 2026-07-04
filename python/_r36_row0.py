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

st={'tot':0,'reduced_mono':0,'row0_identity':0,'row0_strict_incr':0,
    'nextrel0_all_adjacent':0,'e00_is_0':0}
cex=[]
for M in gen_STPS():
    L=R.Lng(M)
    if L<2: continue
    st['tot']+=1
    red = R.reduced(M)
    mono = R.monoT(M)
    if not (red and mono): continue
    st['reduced_mono']+=1
    if R.entry(M,0,0)==0: st['e00_is_0']+=1
    ident = all(R.entry(M,0,j)==j for j in range(L))
    if ident: st['row0_identity']+=1
    else:
        if len(cex)<6: cex.append(("NOT_IDENT",R.fmt(M),[R.entry(M,0,j) for j in range(L)]))
    sincr = all(R.entry(M,0,j)<R.entry(M,0,j+1) for j in range(L-1))
    if sincr: st['row0_strict_incr']+=1
    else:
        if len(cex)<12: cex.append(("NOT_SINCR",R.fmt(M),[R.entry(M,0,j) for j in range(L)]))
    nr0all = all(R.nextrel0(M,k,k+1) for k in range(L-1))
    if nr0all: st['nextrel0_all_adjacent']+=1
print(st)
for c in cex: print("CEX",c)
