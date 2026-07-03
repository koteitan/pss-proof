import sys; sys.path.insert(0,'.')
from _xseq_measure import D, ZERO, is_zero, domB
import math
INF=math.inf
def spines(depth, maxv=4):
    if depth==0: yield ZERO; return
    for v in range(maxv+1):
        for sub in spines(depth-1, maxv): yield [D(v,sub)]
# Claim: for single principal D_w c with c!=0 and domB(D_w c)=TBv u:
#   domB c = TBv u AND w>u.
bad=0
for c_depth in range(1,5):
  for c in spines(c_depth,4):
    if is_zero(c): continue
    for w in range(5):
        b=[D(w,c)]
        db=domB(b)
        if db[0]!='Tv': continue
        u=db[1]
        dc=domB(c)
        if not (dc[0]=='Tv' and dc[1]==u and w>u):
            bad+=1
            if bad<=5: print("STRUCT-FAIL w=",w,"c-dom=",dc,"b-dom=",db)
print("c!=0 single-principal TBv struct check, fails=",bad)
# c=0 case: domB(D_w 0)=TBv u iff w=u+1 (w finite, w>=1)
bad2=0
for w in range(1,6):
    db=domB([D(w,ZERO)])
    # expect ('Tv', w-1)
    if db!=('Tv',w-1): bad2+=1; print("c=0 FAIL w=",w,db)
print("c=0 case check fails=",bad2)
