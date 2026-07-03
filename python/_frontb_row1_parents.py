from red_model import *
def tile_cond(N):
    j1=Lng(N)-1
    if j1==0: return False
    if entry(N,0,j1)==0 and entry(N,1,j1)==0: return False
    i1=idx1(N,j1)
    if not hasParent(N,i1,j1): return False
    return True
def RedCondA(M):
    for i in (0,1):
        for j1 in range(Lng(M)):
            if hasParent(M,i,j1):
                if entry(M,i,parent(M,i,j1))+1 != entry(M,i,j1): return False
    return True
def RedCondB(M):
    for j1 in range(Lng(M)):
        if not hasParent(M,0,j1):
            if entry(M,0,j1)!=entry(M,1,j1): return False
    return True

# enumerate forms
seeds=[diagSeq(a,b) for a in range(0,3) for b in range(a,a+4)]
seen=set(); forms=[]
frontier=[tuple(s) for s in seeds]
while frontier and len(seen)<3000:
    new=[]
    for k in frontier:
        if k in seen: continue
        seen.add(k); forms.append(k); M=list(k)
        if Lng(M)<=7:
            for n in range(1,3):
                Mn=oper(M,n)
                if 1<Lng(Mn)<=9: new.append(tuple(Mn))
    frontier=new

# For each valid N, n: examine row-1 parents in Nn. Classify parent position
# relative to period structure.
within=0; boundary=0; prefix=0; other=0; total=0
for k in forms:
    N=list(k)
    if not tile_cond(N): continue
    if not RedCondA(N): continue
    if not RedCondB(N): continue
    j1=Lng(N)-1; i1=idx1(N,j1); j0=parent(N,i1,j1); w=j1-j0
    for n in range(1,5):
        Nn=oper(N,n)
        for x in range(Lng(Nn)):
            if not hasParent(Nn,1,x): continue
            p=parent(Nn,1,x); total+=1
            # classify x and p
            def region(z):
                if z<j0: return ('pref',z)
                q=(z-j0)//w; s=(z-j0)%w
                return ('blk',q,s)
            rx=region(x); rp=region(p)
            if rx[0]=='pref' and rp[0]=='pref': prefix+=1
            elif rx[0]=='blk' and rp[0]=='blk' and rx[1]==rp[1]: within+=1
            elif rp[0]=='pref' and rx[0]=='blk': boundary+=1
            elif rx[0]=='blk' and rp[0]=='blk' and rx[1]!=rp[1]: boundary+=1
            else: other+=1
print("total row1 parents",total,"prefix",prefix,"within",within,"boundary(crossblk/toprefix)",boundary,"other",other)

print("=== boundary detail ===")
bd_xs0=0; bd_other=0; samples=[]
for k in forms:
    N=list(k)
    if not tile_cond(N): continue
    if not RedCondA(N): continue
    if not RedCondB(N): continue
    j1=Lng(N)-1; i1=idx1(N,j1); j0=parent(N,i1,j1); w=j1-j0
    for n in range(1,5):
        Nn=oper(N,n)
        for x in range(Lng(Nn)):
            if not hasParent(Nn,1,x): continue
            p=parent(Nn,1,x)
            def region(z):
                if z<j0: return ('pref',z)
                return ('blk',(z-j0)//w,(z-j0)%w)
            rx=region(x); rp=region(p)
            is_bd = (rp[0]=='pref' and rx[0]=='blk') or (rx[0]=='blk' and rp[0]=='blk' and rx[1]!=rp[1])
            if not is_bd: continue
            # does x sit at block start s==0?
            if rx[0]=='blk' and rx[2]==0:
                bd_xs0+=1
            else:
                bd_other+=1
                if len(samples)<8: samples.append((fmt(N),n,x,p,rx,rp))
print("boundary with x at block-start(s=0):",bd_xs0,"  boundary with x interior(s>0):",bd_other)
for s in samples: print("  interior-boundary:",s)

print("=== boundary parent location (x=j0+q*w, q>=?) ===")
from collections import Counter
cnt=Counter()
for k in forms:
    N=list(k)
    if not tile_cond(N): continue
    if not RedCondA(N): continue
    if not RedCondB(N): continue
    j1=Lng(N)-1; i1=idx1(N,j1); j0=parent(N,i1,j1); w=j1-j0
    for n in range(1,5):
        Nn=oper(N,n)
        for x in range(Lng(Nn)):
            if not hasParent(Nn,1,x): continue
            p=parent(Nn,1,x)
            if x<j0: continue
            qx=(x-j0)//w; sx=(x-j0)%w
            if sx!=0: continue  # only block-start x
            # is this a boundary case (parent not in block qx)?
            if p>=j0 and (p-j0)//w==qx and (p-j0)%w>=0 and not(p<j0):
                # within-block: skip unless cross
                pq=(p-j0)//w
                if pq==qx: continue
            # boundary: record where parent sits
            if p<j0:
                cnt[('prefix',qx)]+=1
            else:
                pq=(p-j0)//w; ps=(p-j0)%w
                cnt[('blk',qx-pq,ps)]+=1   # delta block, offset of parent
print(cnt)
