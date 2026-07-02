from red_model import oper, fmt
from _ez_A_fast import Lng,entry,nextrel1,le0reach,hasParent1,parent1,idx1

M=[(0,0),(1,1),(1,1),(1,0),(2,1),(2,1),(2,0),(3,1),(3,1)]
n=3
N=oper(M,n)
print("M=",fmt(M),"Lng",Lng(M))
print("N=oper(M,3) Lng",Lng(N))
print("N=",fmt(N))
LM=Lng(M); j1M=LM-1
print("j1M",j1M,"entry0 j1M",entry(M,0,j1M),"entry1 j1M",entry(M,1,j1M),"idx1",idx1(M,j1M))
print("hasParent1 M j1M",hasParent1(M,j1M),"parent1",parent1(M,j1M))
j1N=Lng(N)-1
print("j1N",j1N,"hasParent1 N j1N",hasParent1(N,j1N),"j0N",parent1(N,j1N))
z=9
print("z",z,"hasParent1 N z",hasParent1(N,z),"pz",parent1(N,z))
print("entry0 N j1N",entry(N,0,j1N),"entry0 N z",entry(N,0,z),"j1N-z",j1N-z)
print("Ez lhs",entry(N,0,j1N),"rhs",entry(N,0,z)+(j1N-z))
# is M in ST_PS? M not is_standard necessarily. Check whether M arises in the broad closure
# Key question: is the gating (z interior strict ancestor in N) actually satisfied for THIS N as a standalone ST_PS member?
# print row0 of N
print("row0 N:",[entry(N,0,j) for j in range(Lng(N))])
print("row1 N:",[entry(N,1,j) for j in range(Lng(N))])
