#!/usr/bin/env python3
import itertools
LP, CM, RP, Zsym = 'LP', 'CM', 'RP', 'Zsym'
def Dsym(u): return ('Dsym', u)
def Trm(ps): return ('Trm', tuple(ps))
def DB(v, a): return ('D', v, a)
def flatBP(p):
    _, u, a = p; return [Dsym(u)] + flatBT(a)
def flatBT(t):
    _, ps = t
    if len(ps)==0: return [Zsym]
    if len(ps)==1: return flatBP(ps[0])
    head=ps[0]; rest=ps[1:]; mid=[]
    for r in rest: mid += [CM]+flatBP(r)
    return [LP]+(flatBP(head)+mid)+[RP]
def dfree_BT(t):
    _,ps=t; return all(dfree_BP(p) for p in ps)
def dfree_BP(p):
    _,v,a=p; return v!='INF' and dfree_BT(a)
def in_TB(t): return dfree_BT(t)
def addBT(t,c):
    _,a=t; _,bs=c; return Trm(list(a)+list(bs))

# isPTB: a string is a principal flat iff it starts with Dsym and rest is a valid BT flat.
# For this concrete check we just test membership against the relevant principal strings.
def isPTB_str_concrete(cstr):
    # flatBP p starts with Dsym; here all our c-strings are genuine principals.
    return len(cstr)>0 and isinstance(cstr[0],tuple) and cstr[0][0]=='Dsym'

def scb_decomp(t,s,cstr,b):
    if flatBT(t)!=s+cstr+b: return False
    if t!=Trm([]) and not isPTB_str_concrete(cstr): return False
    if not all(x==RP for x in b): return False
    return True

t=Trm([]); v=0
c =Trm([DB(0,Trm([]))])
c2=Trm([DB(0,Trm([DB(0,Trm([]))]))])
tc=addBT(t,c); ftc=flatBT(tc)
u1=Trm([DB(0,Trm([DB(0,Trm([]))])), DB(0,Trm([]))])
fu1=flatBT(u1)
print("flatBT u1 =", fu1, "in_TB:",in_TB(u1))
tgt=[Dsym(v)]+ftc
i=1; s1=fu1[:i]; b1=fu1[i+len(tgt):]
print("s1=",s1,"b1=",b1," (s1 D_v(t+c) b1 == flatBT u1:",s1+tgt+b1==fu1,")")
fc=flatBT(c); m=len(fc)
print("\nAll valid scb-decomps of u1 with c-string", fc, ":")
for j in range(len(fu1)-m+1):
    s0=fu1[:j]; b0=fu1[j+m:]
    if fu1[j:j+m]==fc and scb_decomp(u1,s0,fc,b0):
        print("  s0=",s0,"b0=",b0)
s0=fu1[:5]; b0=[fu1[-1]]
fc2=flatBT(c2); ftc2=flatBT(addBT(t,c2))
want = s1 + ([Dsym(v)]+ftc2) + b1
need = s0 + fc2 + b0
print("\nChosen scb: s0=",s0," b0=",b0)
print("Conclusion: u1' must have flatBT u1' =", want)
print("scb_decomp u1' s0 fc2 b0 also requires flatBT u1' = s0+fc2+b0 =", need)
print("want == need ?", want==need)
