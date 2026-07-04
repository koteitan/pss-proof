import sys, time, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, entry, parent, oper, diagSeq, monoT
from trans_model import Trans, Pred, adm, Adm, condV, condIII, condVI, Dpt, addBT, bpHeadT, flatBT, ZB
INF=float('inf')
def numBT(n): return ('T',[('D',0,ZB)]*n)
def numNat(z): return len(z[1])
def multBT(a,n):
    out=ZB
    for _ in range(n): out=addBT(out,a)
    return out
def domB(a):
    ps=a[1]
    if not ps: return 'EMPTY'
    if len(ps)==1:
        _,v,b=ps[0]
        if b==ZB:
            if v==0: return 'ZERO'
            if v==INF: return 'NAT'
            return ('TB',v-1)
        db=domB(b)
        if db=='ZERO': return 'NAT'
        if isinstance(db,tuple) and db[0]=='TB' and v<=db[1]: return 'NAT'
        return db
    return domB(('T',[ps[-1]]))
def operB(a,z):
    ps=a[1]
    if not ps: return ZB
    if len(ps)==1:
        _,v,b=ps[0]
        if b==ZB:
            if v==0: return ZB
            if v==INF: return Dpt(numNat(z)+1,ZB)
            return z
        db=domB(b)
        if db=='ZERO': return multBT(Dpt(v,operB(b,ZB)),numNat(z)+1)
        if isinstance(db,tuple) and db[0]=='TB' and v<=db[1]: return Dpt(v,xseq(b,db[1],numNat(z)))
        return Dpt(v,operB(b,z))
    return addBT(('T',ps[:-1]),operB(('T',[ps[-1]]),z))
def xseq(b,u,i):
    if i==0: return Dpt(u,ZB)
    return operB(b,Dpt(u,xseq(b,u,i-1)))
def op0(a): return operB(a,numBT(0))
def transJ0(M): return parent(M,0,Lng(M)-1)
def is_std(M):
    try: return __import__('red_model').is_standard(M)
    except Exception: return False
def gen(tmax,seeds,maxlen=15):
    t0=time.time();seen=set();rng=random.Random(sum(seeds))
    while time.time()-t0<tmax:
        u=rng.randrange(0,5);vv=u+rng.randrange(1,6)
        M=diagSeq(u,vv)
        for _ in range(9):
            k=tuple(M)
            if k not in seen and 2<Lng(M)<=maxlen: seen.add(k); yield M
            n=rng.randrange(1,4)
            try: M2=oper(M,n)
            except Exception: break
            if M2==M or Lng(M2)>maxlen*2: break
            M=M2
st={'condVadm':0,'k2_ok':0,'k2_bad':0,'core_ok':0}
badex=[];idxs={}
for M in gen(int(sys.argv[1]) if len(sys.argv)>1 else 300, [11,222,3333,99]):
    if not is_std(M): continue
    j1=Lng(M)-1
    if not(1<j1): continue
    if not condV(M): continue
    j0=transJ0(M)
    if j0 is None or not adm(M,j0): continue
    st['condVadm']+=1
    e=entry(M,1,j0)
    for m in range(2,5):
        try:
            W=operB(Trans(M),numBT(m))
            Tm=Trans(oper(M,m))
        except Exception: continue
        # k=2 tower
        got=op0(op0(W))
        if got==Tm:
            st['k2_ok']+=1
            # find minimal k that works, record (m,k)
            for k in range(0,5):
                x=W
                for _ in range(k): x=op0(x)
                if x==Tm:
                    idxs[(m,k)]=idxs.get((m,k),0)+1; break
        else:
            st['k2_bad']+=1
            if len(badex)<6:
                # find any working k
                kk=None
                for k in range(0,7):
                    x=W
                    for _ in range(k): x=op0(x)
                    if x==Tm: kk=k;break
                badex.append((''.join('(%d,%d)'%p for p in M),'m=%d'%m,'kworks=%s'%kk))
print("condV-adm hosts:",st['condVadm'])
print("k=2 tower Trans(N[m])==[0]^2(operB(Trans N)(numBT m)): ok",st['k2_ok']," BAD",st['k2_bad'])
print("minimal (m,k) distribution:",dict(sorted(idxs.items())))
if badex: print("BAD examples (k that works):",badex)
