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

st={'host':0,'WGAP':0,'c_win_le_TrMaxX':0,'recon_ok':0,'XmonoT':0}
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
    if not (jm2<j0): continue          # condIII/IV => jm2<j0
    if j0>=L-1: continue
    st['host']+=1
    # WGAP directly
    wgap = R.entry(M,0,j0)==R.entry(M,0,jm2)+(j0-jm2)
    if wgap: st['WGAP']+=1
    else:
        if len(cex)<6: cex.append(("WGAP_FALSE",R.fmt(M),jm2,j0)); continue
    # slice S = seg M jm2 (L-2); X = Red S
    S=R.seg(M,jm2,L-2)
    try: X=R.Red(S)
    except Exception: continue
    if not R.monoT(X):
        if len(cex)<12: cex.append(("XnotMono",R.fmt(M))); continue
    st['XmonoT']+=1
    TrMaxX=R.TrMax(X)
    win=j0-jm2
    if win<=TrMaxX: st['c_win_le_TrMaxX']+=1
    else:
        if len(cex)<12: cex.append(("win>TrMaxX",R.fmt(M),'win',win,'TrMaxX',TrMaxX,'X',R.fmt(X))); continue
    # reconstruction: entry M 0 (jm2+k) = entry X 0 k + dd ; entry X 0 d = entry X 0 0 + d (trunk)
    dd=R.entry(M,0,jm2)-R.entry(M,1,jm2)
    ok = (R.entry(M,0,jm2)==R.entry(X,0,0)+dd
          and R.entry(M,0,j0)==R.entry(X,0,win)+dd
          and R.entry(X,0,win)==R.entry(X,0,0)+win)
    if ok: st['recon_ok']+=1
    else:
        if len(cex)<14: cex.append(("recon_fail",R.fmt(M),'dd',dd,'e0Mjm2',R.entry(M,0,jm2),'e0X0',R.entry(X,0,0),'e0Xwin',R.entry(X,0,win),'win',win))
print(st)
for c in cex: print("CEX",c)
