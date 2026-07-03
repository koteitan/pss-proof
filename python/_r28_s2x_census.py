#!/usr/bin/env python3
# r28-SHARP2 census: full-shape dump + structural characterization candidates for
# genuine ST_PS non-adm condV hosts (the {len2, redB} domain).
import sys, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, entry, monoT, seg, adm, oper, diagSeq, parent, Adm, Pred, fmt, nextrel1, hasParent
from trans_model import reduced, condV, Trans, Mark, bpHeadT, ZB

def transJ1(M): return Lng(M)-1
def RN(t):
    xs=t[1]
    return [] if not xs else [xs[-1][1]]+RN(xs[-1][2])

def gen(ml,mn,ms,cap):
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+3):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M);fr.append(list(M));pool.append(list(M))
    while fr and len(pool)<cap:
        nx=[]
        for M in fr:
            if Lng(M)<=1: continue
            for n in range(1,mn+1):
                N=oper(M,n)
                if Lng(N)>ml: continue
                t=tuple(N)
                if t not in seen: seen.add(t);nx.append(N);pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        fr=nx
    return pool

def run(ml,cap,budget,mn):
    pool=gen(ml,mn,4,cap)
    print("pool",len(pool),"mn",mn,"maxLng",ml,flush=True)
    t0=time.time(); tot=0
    stats={'len2':0,'redB':0,'j0gap1':0,'j0_is_Lm3':0,'noadm_mid':0,
           'ramp_flat':0,'row0_diag':0,'flat_from_j0p1':0,'jm1_adm_all_before':0,
           'peak_at_j0p1':0,'deep9':0}
    fails={k:[] for k in stats}
    hosts=[]
    for M in pool:
        if time.time()-t0>budget:
            print("BUDGET HIT",flush=True); break
        if not (reduced(M) and monoT(M)): continue
        if Lng(M)<3: continue
        j1=transJ1(M); jp=parent(M,0,j1)
        if jp is None: continue
        if not condV(M): continue
        if adm(M,jp): continue
        if Trans(Pred(M))==ZB: continue
        jm1=Adm(M,jp)
        c1=Mark(Pred(M),jm1)
        if bpHeadT(c1)==ZB: continue
        tot+=1
        L=Lng(M)
        if L>=9: stats['deep9']+=1
        rn=RN(c1)
        def chk(k,b,info):
            if b: stats[k]+=1
            else: fails[k].append((fmt(M),info))
        chk('len2', len(rn)==2, rn)
        chk('redB', entry(M,1,L-2)==entry(M,1,jp+1), (entry(M,1,L-2),entry(M,1,jp+1),jp))
        chk('j0gap1', jp-jm1==1, (jm1,jp))
        chk('j0_is_Lm3', jp==L-3, (jp,L))
        # no admissible column strictly in (jm1, L-2]
        noadm = all(not adm(M,j) for j in range(jm1+1,L-1))
        chk('noadm_mid', noadm, [j for j in range(jm1+1,L-1) if adm(M,j)])
        # ramp+flat: row1 strictly +1 ramp up to some peak p, then flat to L-2
        r1=[entry(M,1,j) for j in range(L)]
        p=0
        while p+1<L-1 and r1[p+1]==r1[p]+1: p+=1
        rampflat = all(r1[j]==r1[p] for j in range(p,L-1))
        chk('ramp_flat', rampflat, r1)
        chk('peak_at_j0p1', p==jp+1, (p,jp,r1))
        # flat exactly from j0+1: r1[j]==r1[jp+1] for jp+1<=j<=L-2
        chk('flat_from_j0p1', all(r1[j]==r1[jp+1] for j in range(jp+1,L-1)), r1)
        # row0 pure diagonal? entry M 0 j = entry M 0 0 + j
        r0=[entry(M,0,j) for j in range(L)]
        chk('row0_diag', all(r0[j]==r0[0]+j for j in range(L)), r0)
        # all columns <= jm1 admissible?
        chk('jm1_adm_all_before', all(adm(M,j) for j in range(jm1+1)), [j for j in range(jm1+1) if not adm(M,j)])
        if len(hosts)<40:
            hosts.append((fmt(M),L,jm1,jp,j1,r0,r1,len(rn)))
    print(f"tot={tot} (deep Lng>=9: {stats['deep9']})")
    for k in stats:
        if k=='deep9': continue
        print(f"  {k}: {stats[k]}/{tot}  fails={len(fails[k])}")
        for f in fails[k][:4]: print("     CEX", f)
    print("hosts (up to 40):")
    for h in hosts: print("   ",h)

if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 12,
        int(sys.argv[2]) if len(sys.argv)>2 else 8000,
        int(sys.argv[3]) if len(sys.argv)>3 else 240,
        int(sys.argv[4]) if len(sys.argv)>4 else 8)
