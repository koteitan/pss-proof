import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import oper,Lng,entry,parent,TrMax,monoT
from trans_model import Trans,Mark,Adm,ZB,PB,bpHeadT,bpHeadV
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
M=[(0,0),(1,1),(2,0),(3,1),(3,1)]
print("M=",''.join('(%d,%d)'%c for c in M))
T={}
for q in range(1,5):
    Mq=oper(M,q)
    if Lng(Mq)>12: print(" q",q,"too long",Lng(Mq)); continue
    t=Trans(Mq); T[q]=t
    print(" q=%d M[q]=%s"%(q,''.join('(%d,%d)'%c for c in Mq)))
    print("      Trans(M[q]) = %s"%sf(t))
    print("      bpHeadT=%s  spineLeaf=%s"%(sf(bpHeadT(t)),sf(spineLeaf(t)) if spineLeaf(t) else None))
# recurrence: relate Trans(M[q]) to Trans(M[q-1])
print("\n--- recurrence check ---")
for q in range(2,5):
    if q not in T or q-1 not in T: continue
    tq=T[q]; tp=T[q-1]
    # candidate: Trans(M[q]) = Dpt e10 (body) ; how does body relate to Trans(M[q-1])?
    e10=tq[1][0][1]; body=bpHeadT(tq)
    print(" q=%d: Trans(M[q])=Dpt %d (%s)"%(q,e10,sf(body)))
    print("       bpHeadT(Trans(M[q-1]))=%s"%sf(bpHeadT(tp)))
    print("       Trans(M[q-1])=%s"%sf(tp))
    # is body = (something) +B Dpt vm1 (bpHeadT(Trans(M[q-1])))? or = wrap of Trans(M[q-1])?
    print("       body == Trans(M[q-1])-with-leaf-wrapped?  spineLeaf(tq)=%s spineLeaf(tp)=%s"%(sf(spineLeaf(tq)) if spineLeaf(tq) else None, sf(spineLeaf(tp)) if spineLeaf(tp) else None))
