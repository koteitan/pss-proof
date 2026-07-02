import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,idx1,diagSeq)
import trans_model as tm
from trans_model import condV

"""ROUND 14 front K, STEP 0: broaden the empirical base for the residual
    entry Mq 0 (Pcut Mq) < fst (B!m)      [trunk-stuck non-reset columns]
AND record the BASE-M-level explicit structure of the genuine deepen block.

KEY STRUCTURAL FACT (read off oper's definition, both i1 branches):
  oper(M,q+1) = oper(M,q) @ copy_q,   copy_q = [(entry(M,0,j)+q*d0M, entry(M,1,j))
                                                 for j in [j0M, j1M)]
  with j1M=Lng M-1, i1M=idx1(M,j1M), j0M=parent(M,i1M,j1M),
       d0M = entry(M,0,j1M)-entry(M,0,j0M) if i1M==1 else 0.
So B IS explicit at the base level -- round 13 only checked the i1=1 form
(m_8_5_deepen_block_explicit) and concluded "no explicit form governs".

Per genuine block, record:
  i1M, d0M, sanity B==copy_q, pcMq=Pcut(Mq), V=entry(Mq,0,pcMq),
  fst(B!0), V==fst(B!0)?, V<=fst(B!0)?, pcMq==j0M?, pcMq==j0M+k*wM some k?
Per trunk-stuck non-reset column: V<fc (the residual), min fc, m==0 stuck?
Populations: (A) random reduced M (maxv/u broadened); (B) genuine ST_PS-style
M = iterated oper of diagSeq(u,v)."""

class TimeoutErr(Exception): pass
def handler(s,f): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)
def safe_reduced(M,b=1):
    signal.alarm(b)
    try: r=reduced(M); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None

def gen_random(rng,maxlen=6,maxv=3,u_vals=(0,1,2,3,4)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]; npair=len(pairs)
    combos=[(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            idx=rng.randrange(npair**(L-1)); s=[]; t=idx
            for _ in range(L-1): s.append(pairs[t%npair]); t//=npair
            yield [(u,u)]+s

def gen_stps(rng,maxu=3,maxv=4,maxsteps=3,maxidx=3):
    """genuine ST_PS-style: start diagSeq(u,v), apply a few random oper."""
    while True:
        u=rng.randint(0,maxu); v=rng.randint(u,u+maxv)
        M=diagSeq(u,v)
        for _ in range(rng.randint(0,maxsteps)):
            n=rng.randint(1,maxidx)
            M2=oper(M,n)
            if Lng(M2)>14: break
            M=M2
        yield M

def sweep(genf,tl,qs,seed,tag):
    rng=random.Random(seed); t0=time.time(); cnt=0
    from collections import Counter
    Vdist=Counter(); fcmin=None; rows=0; res=0
    blocks=0; i1c=Counter(); d0c=Counter(); sane=0
    VeqB0=0; VleB0=0; pcj0=0; pcbound=0; stuck0=0
    key2=0; key2b=0; key2c=0; key3=0; key4=0
    fails=[]
    seen=set()
    for M in genf(rng):
        if time.time()-t0>tl: break
        key=tuple(M)
        if key in seen: continue
        seen.add(key)
        if safe_reduced(M,1) is not True: continue
        cnt+=1
        j1M=Lng(M)-1
        if j1M<=0: continue
        if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
        i1M=idx1(M,j1M)
        if not hasParent(M,i1M,j1M): continue
        j0M=parent(M,i1M,j1M)
        d0M=(entry(M,0,j1M)-entry(M,0,j0M)) if i1M>0 else 0
        wM=j1M-j0M
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>16: continue
                if not condV(Mq): continue
                if not hasParent(Mq,1,j1): continue
                p1=parent(Mq,1,j1)
                if not (nextrel0(Mq,p1,j1) and p1==parent(Mq,0,j1)): continue
                jm1=Adm(Mq,parent(Mq,0,j1))
                if not (jm1>0): continue
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]; wB=len(B)
                if wB<1 or B[0][0]==0: continue
                if safe_reduced(Mq,1) is not True or not multiT(Mq): continue
                # block-level structure records
                blocks+=1; i1c[i1M]+=1; d0c[d0M]+=1
                copyq=[(entry(M,0,j)+q*d0M, entry(M,1,j)) for j in range(j0M,j1M)]
                if B==copyq: sane+=1
                pcMq=Pcut(Mq); V=entry(Mq,0,pcMq)
                fB0=B[0][0]
                if V==fB0: VeqB0+=1
                if V<=fB0: VleB0+=1
                if pcMq==j0M: pcj0+=1
                # pcMq at a copy boundary j0M + k*wM ?
                if pcMq>=j0M and (pcMq-j0M)%wM==0: pcbound+=1
                # KEY2: m=0 never trunk-stuck, direct fact Pcut(Mq) <= jm1
                if pcMq<=jm1: key2+=1
                # KEY2b: adm(Mq, Pcut Mq) (mechanism candidate for KEY2)
                if adm(Mq,pcMq): key2b+=1
                # KEY2c: Pcut(Mq) <= p0 = parent(Mq,0,last)  (Pcut minimality; sanity)
                if pcMq<=parent(Mq,0,j1): key2c+=1
                host=list(Mq)
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    if not (jm1<Pcut(Nprev)): continue
                    fc=col[0]
                    if fc==0: continue
                    if m==0: stuck0+=1
                    rows+=1; Vdist[V]+=1
                    fcmin=fc if fcmin is None else min(fcmin,fc)
                    # KEY3 (per stuck col m>0): strict jump over the copy boundary value
                    if m>0 and fc>fB0: key3+=1
                    # KEY4: the c=j0M route feeding smaller_at
                    if j0M<Lng(Nprev) and entry(Nprev,0,j0M)<fc: key4+=1
                    if V<fc: res+=1
                    else:
                        if len(fails)<10:
                            fails.append(dict(M=tuple(M),q=q,m=m,V=V,fc=fc,
                                              pcMq=pcMq,j0M=j0M,i1M=i1M,d0M=d0M,B=tuple(B)))
            except Exception: continue
    return dict(tag=tag,seed=seed,cnt=cnt,blocks=blocks,sane=sane,i1c=dict(i1c),
                d0c=dict(d0c),VeqB0=VeqB0,VleB0=VleB0,pcj0=pcj0,pcbound=pcbound,
                rows=rows,res=res,Vdist=dict(Vdist),fcmin=fcmin,stuck0=stuck0,
                key2=key2,key2b=key2b,key2c=key2c,key3=key3,key4=key4,
                fails=fails)

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 60
    seeds=[int(x) for x in sys.argv[2:]] or [555,321,7,99,2024,13,42,1234,777]
    from collections import Counter
    tot=Counter(); TV=Counter(); TI=Counter(); TD=Counter(); FCM=None; allfails=[]
    for sd in seeds:
        for genf,tag in ((gen_random,'rand'),(gen_stps,'stps')):
            r=sweep(genf,tl,(1,2,3,4,5),sd,tag)
            print(f"[{tag} s{r['seed']}] scan={r['cnt']} blocks={r['blocks']} "
                  f"sane(B==copy_q)={r['sane']}/{r['blocks']} i1c={r['i1c']} d0c={r['d0c']} "
                  f"V==fB0:{r['VeqB0']}/{r['blocks']} V<=fB0:{r['VleB0']}/{r['blocks']} "
                  f"pc==j0M:{r['pcj0']}/{r['blocks']} pc@bound:{r['pcbound']}/{r['blocks']}")
            print(f"    stuck rows={r['rows']} residual V<fc: {r['res']}/{r['rows']} "
                  f"Vdist={r['Vdist']} fcmin={r['fcmin']} m0stuck={r['stuck0']} "
                  f"K2 pc<=jm1:{r['key2']}/{r['blocks']} K2b adm(pc):{r['key2b']}/{r['blocks']} "
                  f"K2c pc<=p0:{r['key2c']}/{r['blocks']} K3 fc>fB0(m>0):{r['key3']}/{r['rows']-r['stuck0']} "
                  f"K4 c=j0M:{r['key4']}/{r['rows']}")
            for k in ('blocks','sane','VeqB0','VleB0','pcj0','pcbound','rows','res','stuck0',
                      'key2','key2b','key2c','key3','key4'):
                tot[k]+=r[k]
            TV+=Counter(r['Vdist']); TI+=Counter(r['i1c']); TD+=Counter(r['d0c'])
            if r['fcmin'] is not None: FCM=r['fcmin'] if FCM is None else min(FCM,r['fcmin'])
            allfails+=r['fails']
    print("\n==== TOTALS ====")
    print(f"blocks={tot['blocks']} sane={tot['sane']}/{tot['blocks']} i1c={dict(TI)} d0c={dict(TD)}")
    print(f"V==fst(B!0): {tot['VeqB0']}/{tot['blocks']}   V<=fst(B!0): {tot['VleB0']}/{tot['blocks']}")
    print(f"Pcut(Mq)==j0M: {tot['pcj0']}/{tot['blocks']}  Pcut(Mq) at copy boundary: {tot['pcbound']}/{tot['blocks']}")
    print(f"RESIDUAL entry Mq 0 (Pcut Mq) < fst(B!m) on stuck non-reset cols: {tot['res']}/{tot['rows']}")
    print(f"V distribution: {dict(TV)}   min fst(B!m): {FCM}   m==0 ever stuck: {tot['stuck0']}")
    print(f"KEY2 Pcut(Mq)<=jm1 (m=0 unstuck): {tot['key2']}/{tot['blocks']}"
          f"   KEY2b adm(Mq,Pcut Mq): {tot['key2b']}/{tot['blocks']}"
          f"   KEY2c Pcut(Mq)<=p0: {tot['key2c']}/{tot['blocks']}")
    print(f"KEY3 fst(B!m)>fst(B!0) on stuck m>0: {tot['key3']}/{tot['rows']-tot['stuck0']}"
          f"   KEY4 entry(Nprev,0,j0M)<fc: {tot['key4']}/{tot['rows']}")
    for f in allfails[:10]: print("FAIL:",f)
