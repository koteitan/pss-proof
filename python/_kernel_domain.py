import sys,os,functools,subprocess,itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,monoT,parent,TrMax,Br,oper,seg,leR,adm
import red_model as rm
from trans_model import Trans,Mark,Adm,ZB,PB,bpHeadT,reduced,condV
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def isMarked(M,m): return adm(M,m) and leR(M,0,m,Lng(M)-1)
def gpar(M): return parent(M,0,Lng(M)-1) > TrMax(M)

def gen(maxlen=5,maxv=2):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(3,maxlen+1):
        for s in itertools.product(pairs,repeat=L):
            M=list(s)
            if M[0]!=(0,0): continue
            yield M

rows=[]
cnt=0
for M in gen(5,2):
    try:
        if not (reduced(M) and is_std(tuple(M))): continue
    except Exception: continue
    cnt+=1
    if cnt>4000: break
    for q in (2,3):
        try:
            Mq=oper(M,q); Msq=oper(M,q+1)
            if Lng(Msq)>13: continue
            jm=transJm1(Mq); Lq=Lng(Mq)
            if not (0<jm<Lq-1): continue
            Y=seg(Mq,jm,Lq-1); YB=seg(Msq,jm,Lng(Msq)-1)
            if YB[:len(Y)]!=Y: continue
            B=YB[len(Y):]
            if not B: continue
            # filter conditions
            cV=condV(M); gp=gpar(Mq); mk=isMarked(Mq,jm); stq=is_std(tuple(Mq)); redq=reduced(Mq)
            # per-column g*: each host reduced & monoT
            hosts_ok=True
            for m in range(len(B)):
                host=Y+B[:m+1]
                if not (reduced(host) and monoT(host)): hosts_ok=False;break
            # endpoint
            ep = (spineLeaf(Trans(YB))==bpHeadT(Trans(Y)))
            # entry1 predicate
            pred_ok=True
            for m in range(len(B)):
                changed = spineLeaf(Trans(Y+B[:m+1]))!=spineLeaf(Trans(Y+B[:m]))
                if changed != (B[m][1]!=0): pred_ok=False;break
            rows.append(dict(cV=cV,gp=gp,mk=mk,stq=stq,redq=redq,hosts=hosts_ok,ep=ep,pred=pred_ok,M=rm.fmt(M),q=q))
        except Exception:
            continue

print(f"std&reduced bases scanned={cnt}, kernel-candidate slices={len(rows)}")
def rate(sub,key):
    return f"{sum(1 for r in sub if r[key])}/{len(sub)}" if sub else "0/0"
print("\nALL slices: endpoint", rate(rows,'ep'), " predicate", rate(rows,'pred'))
# progressively tighten the filter; which condition recovers endpoint=all?
for conds in [['cV'],['gp'],['mk'],['stq'],['hosts'],['cV','gp'],['cV','gp','mk'],['cV','gp','mk','hosts'],['cV','gp','mk','hosts','redq']]:
    sub=[r for r in rows if all(r[c] for c in conds)]
    print(f"  filter {'+'.join(conds):28s} n={len(sub):4d}  endpoint={rate(sub,'ep'):8s}  predicate={rate(sub,'pred')}")
# among endpoint-TRUE slices, predicate rate
epT=[r for r in rows if r['ep']]
print(f"\nendpoint-TRUE slices: n={len(epT)}  predicate={rate(epT,'pred')}")
# show a few endpoint-FALSE with full condV&gpar&mk&hosts (genuine-looking but fails)
bad=[r for r in rows if r['cV'] and r['gp'] and r['mk'] and r['hosts'] and not r['ep']]
print(f"\nendpoint-FALSE despite cV&gp&mk&hosts: n={len(bad)}")
for r in bad[:6]: print("   ",r['M'],"q=",r['q'])
