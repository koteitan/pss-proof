#!/usr/bin/env python3
exec(open('python/_wf6_addscb_c3.py').read().split('# CONSTRUCTIVE')[0])
# The candidate counterexample to conjunct (3):
t=Trm([]); v=0
c =Trm([DB(0,Trm([]))])                       # D_0 0
c2=Trm([DB(0,Trm([DB(0,Trm([]))]))])          # D_0 (D_0 0)
tc=addBT(t,c); ftc=flatBT(tc)
u1=Trm([DB(0,Trm([DB(0,Trm([]))])), DB(0,Trm([]))])  # ( D_0(D_0 0) , D_0 0 )
fu1=flatBT(u1)
print("u1 in T_B:", in_TB(u1))
print("flatBT u1 =", fu1)
# premise: s1 D_v(t+c) b1 = flatBT u1 ?
tgt=[Dsym(v)]+ftc
print("D_v(t+c) flat =", tgt)
# find s1,b1
import sys
found=False
for i in range(len(fu1)-len(tgt)+1):
    if fu1[i:i+len(tgt)]==tgt:
        s1=fu1[:i]; b1=fu1[i+len(tgt):]
        print("  s1=",s1,"b1=",b1)
        found=True
# scb_decomp u1 s0 (flatBT c) b0
fc=flatBT(c); m=len(fc)
print("flatBT c=",fc)
for j in range(len(fu1)-m+1):
    s0=fu1[:j]; b0=fu1[j+m:]
    if fu1[j:j+m]==fc and scb_decomp(u1,s0,fc,b0):
        print("  scb: s0=",s0,"b0=",b0)
# now: does ANY u1' in T_B exist with flatBT u1' = s1 (Dsym v # flatBT(t+c')) b1
#      AND scb_decomp u1' s0 (flatBT c') b0  (for the s0,b0 found above)?
fc2=flatBT(c2); ftc2=flatBT(addBT(t,c2))
# use the s1,b1 and s0,b0 found
s1=[fu1[0]]; b1=fu1[1+len(tgt):]   # s1=[LP], b1=[CM,Dsym0,Zsym,RP]
s0=fu1[:5]; b0=[fu1[-1]]
want = s1 + ([Dsym(v)]+ftc2) + b1
print("WANT flat =", want)
print("require scb at s0=",s0," fc2=",fc2," b0=",b0)
# Is want a valid flatBT image at all, and does scb hold?
# Search deep image
import itertools
DEEP=enum_terms(4,IDXS,3)
hit=[u for u in DEEP if flatBT(u)==want]
print("#terms with flat=want:", len(hit))
for u in hit:
    print("  u1'=",u,"in_TB",in_TB(u),"scb_decomp u1' s0 fc2 b0:", scb_decomp(u,s0,fc2,b0))
# Also: is it even possible that want = s0 + fc2 + b0 ? (necessary for scb)
print("want == s0+fc2+b0 ?", want == s0+fc2+b0)
print("  s0+fc2+b0 =", s0+fc2+b0)
