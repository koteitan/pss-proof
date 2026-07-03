#!/usr/bin/env python3
# r28-SHARP2: generate the deep ST_PS pool ONCE and pickle it (with reduced/mono flags).
import sys, time, pickle
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import Lng, monoT, oper, diagSeq
from trans_model import reduced

def gen(ml,mn,ms,cap):
    seen=set();fr=[];pool=[]
    for u in range(ms):
        for v in range(u,u+ms+4):
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

if __name__=='__main__':
    ml=int(sys.argv[1]) if len(sys.argv)>1 else 13
    cap=int(sys.argv[2]) if len(sys.argv)>2 else 30000
    mn=int(sys.argv[3]) if len(sys.argv)>3 else 9
    t0=time.time()
    pool=gen(ml,mn,4,cap)
    print("pool",len(pool),"gen time",round(time.time()-t0,1),flush=True)
    # annotate mono+reduced once (reduced is the expensive bit)
    ann=[]
    for i,M in enumerate(pool):
        mo=monoT(M)
        red=reduced(M) if mo else None
        ann.append((M,mo,red))
        if i%2000==0: print(i,round(time.time()-t0,1),flush=True)
    with open('/tmp/claude-1000/-home-koteitan-proofs-pss-proof/8b6b910e-60c9-4662-aff1-4806ad270a61/scratchpad/r28pool.pkl','wb') as f:
        pickle.dump(ann,f)
    print("done",round(time.time()-t0,1))
