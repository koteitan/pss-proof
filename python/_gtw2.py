from red_model import *
import sys; sys.setrecursionlimit(20000)
def closure(depth,ub,vb,ml):
    bases=[tuple(diagSeq(u,v)) for u in range(ub+1) for v in range(u,vb+1)]
    seen=set(bases); allM=set(bases); fr=list(bases)
    for _ in range(depth):
        nf=[]
        for M in fr:
            Ml=list(M)
            for n in range(1,4):
                try: Nn=oper(Ml,n)
                except: continue
                if not(1<=len(Nn)<=ml): continue
                t=tuple(Nn)
                if t not in seen: seen.add(t); allM.add(t); nf.append(t)
        fr=nf
    return [list(M) for M in allM]
def gtw(M):
    L=Lng(M)
    for y in range(0,L):
        if not hasParent(M,1,y): continue
        p=parent(M,1,y)
        for z in range(p+1,y):
            if not (hasParent(M,1,z) and parent(M,1,z)>=p): return False
    return True
Ms=closure(4,3,7,15)
print("closure",len(Ms))
# diag base
db=dbf=0
for u in range(0,5):
    for v in range(u,9):
        db+=1
        if not gtw(diagSeq(u,v)): dbf+=1
# step: gtw(K) => gtw(K[n])
st=sf=0; ex=[]
for K in Ms:
    if not gtw(K): continue
    for n in range(1,4):
        try: N=oper(K,n)
        except: continue
        if not(1<=Lng(N)<=40): continue
        st+=1
        if not gtw(N):
            sf+=1
            if len(ex)<5: ex.append((fmt(K),n))
# all hold?
at=af=0
for M in Ms:
    at+=1
    if not gtw(M): af+=1
print('GlobalTreeWF diag base:',db,'fail',dbf)
print('GlobalTreeWF step gtw(K)=>gtw(K[n]):',st,'fail',sf)
for e in ex: print('  ',e)
print('GlobalTreeWF holds for all in closure:',at,'fail',af)
