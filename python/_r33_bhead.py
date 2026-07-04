import sys, itertools
sys.path.insert(0,'python')
import red_model as R
# For a reduced mono RN (any Red output), check the GENERAL branch-head fact:
#   for every branch J: entry RN 1 (FirstNodes RN!J) >= entry RN 1 (Joints RN!J) + 1
# and the strengthening at the LAST branch when its joint is a trunk node.
nbr=0; fail_ge=0; ex=[]
def check_reduced(RN):
    global nbr,fail_ge
    b=R.Br(RN)
    if len(b)==0: return
    fn=R.FirstNodes(RN); jn=R.Joints(RN)
    for J in range(len(b)):
        nbr+=1
        e1h=R.entry(RN,1,fn[J]); e1j=R.entry(RN,1,jn[J])
        if not (e1h>=e1j+1):
            fail_ge+=1
            if len(ex)<12: ex.append((R.fmt(RN),J,fn[J],jn[J],e1h,e1j))
# generate reduced slices from standard hosts (like the REGS/REGSP setting)
def cond34(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1)
V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
cnt=0
seen=set()
for base_len in range(2,6):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>9: continue
            cnt+=1
            try:
                if not R.is_standard(M): continue
            except Exception: continue
            if not cond34(M): continue
            j1=R.Lng(M)-1
            if not R.hasParent(M,1,j1): continue
            jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
            for bend in (j1, j1-1):
                if bend<=jm3: continue
                try: RN=R.Red(R.seg(M,jm3,bend))
                except Exception: continue
                key=tuple(map(tuple,RN))
                if key in seen: continue
                seen.add(key)
                check_reduced(RN)
print("branches checked",nbr,"fail(entry1 head >= entry1 joint+1):",fail_ge)
for e in ex: print("  ",e)
