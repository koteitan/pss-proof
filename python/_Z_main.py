import sys
from red_model import oper, entry, Lng
from _Z_fast import le0_matrix, parent1, idx1_
from _Z_closure import build_closure

POOL=build_closure(depth=5, maxlen=16)

def setup(M,n):
    j1=Lng(M)-1
    if j1<1: return None
    if M[j1][0]==0 and M[j1][1]==0: return None
    if idx1_(M,j1)!=1: return None
    le0M=le0_matrix(M)
    j0=parent1(M,le0M,j1)
    if j0 is None: return None
    if not (j0<j1): return None
    w=j1-j0
    if w<=0: return None
    N=oper(M,n)
    le0N=le0_matrix(N)
    return j0,j1,w,N,le0M,le0N

def main():
    NMAX=4
    # TASK 2 boundary s=0
    t2_tot=0; t2_prefix=0; t2_q0=0; t2_q0_tot=0; t2_q0_rows=[]
    t2_qge1_rows=[]
    # interior readback formula (the lemma conclusion), valley check
    rb_tot=0; rb_ok=0; rb_fail=[]
    valley_tot=0; valley_ok=0; valley_fail=[]
    # Ez check
    ez_tot=0; ez_ok=0; ez_fail=[]
    nm_refl_tot=0; nm_refl_ok=0; nm_refl_fail=[]

    for M in POOL:
        for n in range(2,NMAX+1):
            s=setup(M,n)
            if s is None: continue
            j0,j1,w,N,le0M,le0N=s
            Ln=Lng(N)
            # M-side parent of u=j0+s
            for q in range(0,n):
                # ---- TASK 2: s=0, z=j0+q*w ----
                z=j0+q*w
                if z<Ln:
                    pz=parent1(N,le0N,z)
                    if pz is not None:
                        t2_tot+=1
                        if pz<j0: t2_prefix+=1
                        if q==0:
                            t2_q0_tot+=1
                            pMj0=parent1(M,le0M,j0)
                            if pMj0 is not None and pz==pMj0: t2_q0+=1
                            if len(t2_q0_rows)<8: t2_q0_rows.append((pz,pMj0))
                        else:
                            if len(t2_qge1_rows)<20: t2_qge1_rows.append((q,z,pz,j0))
                # ---- interior s>0 ----
                for s in range(1,w):
                    u=j0+s
                    if u>=Lng(M): continue
                    pM=parent1(M,le0M,u)
                    if pM is None: continue
                    if pM < j0: continue  # need pMge: pM>=j0
                    y=j0+q*w+s
                    if y>=Ln: continue
                    c=pM+q*w
                    # lemma conclusion: parent N 1 y == pM + q*w
                    py=parent1(N,le0N,y)
                    rb_tot+=1
                    if py is not None and py==c:
                        rb_ok+=1
                    else:
                        if len(rb_fail)<8: rb_fail.append((tuple(M),n,q,s,y,py,c))
                    # valley: any j' with c<j' and le0 N j' y => entry N 1 j' >= entry N 1 y
                    for jp in range(c+1,Ln):
                        if le0N[jp][y]:
                            valley_tot+=1
                            if entry(N,1,jp)>=entry(N,1,y): valley_ok+=1
                            else:
                                if len(valley_fail)<8: valley_fail.append((tuple(M),n,q,s,y,jp))
                    # N->M le0 reflection: for j' in prefix or earlier block, le0 N j' y reflects to M
                    # check: le0 N j' y  with j' = base + qp*w (qp<q) implies le0 M (basecol) u? we test a simpler invariant:
                    # entry N 1 j' for j' in block qp equals entry M 1 (j0 + (j'-j0-qp*w))   (periodicity, unshifted d1=0)
                    # ---- Ez at interior z = j0+q*w+s (the row-1 node) ----
                    # Ez : entry N 0 (Ln-1) = entry N 0 z + ((Ln-1)-z)  where z=y here (interior row-1 node)
                    znode=y
                    if znode < Ln-1:
                        ez_tot+=1
                        lhs=entry(N,0,Ln-1); rhs=entry(N,0,znode)+((Ln-1)-znode)
                        if lhs==rhs: ez_ok+=1
                        else:
                            if len(ez_fail)<8: ez_fail.append((tuple(M),n,q,s,znode,lhs,rhs))

    print("=== TASK2 boundary s=0 ===")
    print("total", t2_tot, "parent<j0 (prefix):", t2_prefix)
    print("q=0: parent N 1 j0 == parent M 1 j0 :", t2_q0, "/", t2_q0_tot, "rows", t2_q0_rows)
    print("q>=1 sample (q,z,parentN,j0):", t2_qge1_rows[:15])
    print()
    print("=== interior readback conclusion (parent N 1 y == pM+q*w) ===")
    print("ok", rb_ok, "/", rb_tot, "fails:", rb_fail[:5])
    print()
    print("=== valley clause ===")
    print("ok", valley_ok, "/", valley_tot, "fails:", valley_fail[:5])
    print()
    print("=== Ez at interior row-1 node ===")
    print("ok", ez_ok, "/", ez_tot, "fails:", ez_fail[:5])

if __name__=="__main__":
    main()
