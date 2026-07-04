import sys
sys.path.insert(0,'python')
import red_model as R

def gen_STPS(maxlen=13, vcap=5, steps=5, cap=1500):
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
                    if t not in seen and len(seen)<cap:
                        seen.add(t); nf.append(Mn); allM.append(Mn)
        frontier=nf
        if len(seen)>=cap: break
    return allM

st={'red_mono':0,'row0_ident':0,'row0_strict_incr':0,'has_branch':0,
    'branch_strict_incr':0}
cex=[]
for M in gen_STPS():
    L=R.Lng(M)
    if L<3: continue
    if not (R.reduced(M) and R.monoT(M)): continue
    st['red_mono']+=1
    br = R.Br(M)
    if len(br)>0: st['has_branch']+=1
    ident = all(R.entry(M,0,j)==j for j in range(L))
    if ident: st['row0_ident']+=1
    sincr = all(R.entry(M,0,j)<R.entry(M,0,j+1) for j in range(L-1))
    if sincr:
        st['row0_strict_incr']+=1
        if len(br)>0: st['branch_strict_incr']+=1
    else:
        if len(cex)<8: cex.append((R.fmt(M),[R.entry(M,0,j) for j in range(L)],'nbr',len(br)))
print(st)
for c in cex: print("CEX_notstrict",c)
