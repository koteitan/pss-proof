#!/usr/bin/env python3
"""Re-check conjunct (3) but build the witness u1' constructively by structural
   surgery rather than searching a fixed enumeration (which is too shallow)."""
import importlib.util, itertools
spec = importlib.util.spec_from_file_location("chk", "python/_wf6_addscb_check.py")
# we cannot import directly (it runs checks). Re-define minimal pieces here.
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

def enum_terms(depth, idxs, maxp):
    if depth==0: return [Trm([])]
    sub=enum_terms(depth-1,idxs,maxp)
    princ=[DB(v,a) for v in idxs for a in sub]
    terms=[Trm([])]
    for k in range(1,maxp+1):
        for combo in itertools.product(princ,repeat=k):
            terms.append(Trm(list(combo)))
    return terms

IDXS=[0,1]; DEPTH=2; MAXP=2
ALL_TERMS=enum_terms(DEPTH,IDXS,MAXP)
ALL_PRINC=[]
for t in ALL_TERMS:
    _,ps=t
    for p in ps:
        if p not in ALL_PRINC: ALL_PRINC.append(p)
def isPTB_str(c): return any(dfree_BP(p) and c==flatBP(p) for p in ALL_PRINC)
def scb_decomp(t,s,c,b):
    if flatBT(t)!=s+c+b: return False
    if t!=Trm([]) and not isPTB_str(c): return False
    if not all(x==RP for x in b): return False
    return True
TB_TERMS=[t for t in ALL_TERMS if in_TB(t)]
PRINC_TERMS=[Trm([p]) for p in ALL_PRINC if in_TB(Trm([p]))]

# CONSTRUCTIVE witness approach:
# Hypothesis: flatBT u1 = s1 @ (Dsym v # flatBT(t+c)) @ b1.
# Since flatBT is injective and u1 corresponds to a tree, the substring
# (Dsym v # flatBT(t+c)) is the flat of a principal DB v (t+c) sitting somewhere.
# Claim: replacing that principal by DB v (t+c') in u1's tree gives u1'.
# We test: does there EXIST u1' (built by replacing the occurrence) such that
#   flatBT u1' = s1 @ (Dsym v # flatBT(t+c')) @ b1  AND scb_decomp u1' s0 (flatBT c') b0.
# To find u1' we search a DEEPER enumeration.
DEEP=enum_terms(3,IDXS,2)
DEEP_set={}
for u in DEEP:
    DEEP_set.setdefault(tuple(flatBT(u)),u)

fail=0; tot=0
for t in TB_TERMS:
    for c in PRINC_TERMS:
        tc=addBT(t,c); ftc=flatBT(tc)
        for v in IDXS:
            tgt=[Dsym(v)]+ftc
            for u1 in TB_TERMS:
                fu1=flatBT(u1); L=len(tgt)
                for i in range(len(fu1)-L+1):
                    if fu1[i:i+L]!=tgt: continue
                    s1=fu1[:i]; b1=fu1[i+L:]
                    fc=flatBT(c); m=len(fc)
                    for j in range(len(fu1)-m+1):
                        s0=fu1[:j]; b0=fu1[j+m:]
                        if fu1[j:j+m]==fc and scb_decomp(u1,s0,fc,b0):
                            for c2 in PRINC_TERMS:
                                tc2=addBT(t,c2); fc2=flatBT(c2); ftc2=flatBT(tc2)
                                want=s1+([Dsym(v)]+ftc2)+b1
                                tot+=1
                                u1p=DEEP_set.get(tuple(want))
                                ok = (u1p is not None and in_TB(u1p) and scb_decomp(u1p,s0,fc2,b0))
                                if not ok:
                                    fail+=1
                                    if fail<=10:
                                        print("STILLFAIL want_in_img=",u1p is not None,"t=",t,"c'=",c2,"v=",v)
print(f"Conjunct(3) constructive/deeper: {fail}/{tot} failures")

print("\n=== DEBUG one STILLFAIL ===")
t=Trm([]); c=Trm([DB(0,Trm([]))]); v=0
c2=Trm([DB(0,Trm([DB(0,Trm([]))]))])
tc=addBT(t,c); ftc=flatBT(tc)
u1=Trm([DB(0,Trm([DB(0,Trm([]))]))])
fu1=flatBT(u1)
print("u1=",u1,"flat=",fu1)
print("tgt=",[Dsym(v)]+ftc)
# the decomposition found: s0=[Dsym 0], b0=[]
s0=[Dsym(0)]; b0=[]
fc=flatBT(c)
print("flatBT c=",fc,"u1[len(s0):]=",fu1[len(s0):len(s0)+len(fc)])
print("scb_decomp u1 s0 fc b0:", scb_decomp(u1,s0,fc,b0))
tc2=addBT(t,c2); fc2=flatBT(c2); ftc2=flatBT(tc2)
want=[Dsym(v)]+ftc2
u1p=DEEP_set.get(tuple(want))
print("u1'=",u1p,"flat=",flatBT(u1p) if u1p else None)
print("want=",want)
print("isPTB_str fc2:",isPTB_str(fc2),"fc2=",fc2)
print("scb_decomp u1' s0 fc2 b0:", scb_decomp(u1p,s0,fc2,b0))
print("flatBT u1' == s0+fc2+b0:", flatBT(u1p)==s0+fc2+b0)
