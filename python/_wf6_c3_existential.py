#!/usr/bin/env python3
# Literal existential check of conjunct (3): for each premise instance,
# does THERE EXIST any u1' in T_B with the required flat AND scb_decomp?
# Witness search: surgery-construct candidate + also try all deep terms with matching flat.
exec(open('python/_wf6_addscb_c3.py').read().split('# CONSTRUCTIVE')[0])

def replace_princ(t, old, new):
    _, ps = t; ps=list(ps)
    for i,p in enumerate(ps):
        if p==old: return Trm(ps[:i]+[new]+ps[i+1:]), True
        _,pv,pa=p; na,f=replace_princ(pa,old,new)
        if f: return Trm(ps[:i]+[('D',pv,na)]+ps[i+1:]), True
    return t, False

# Build image map up to depth 3 maxp 2 (enough: want strings are bounded)
DEEP=enum_terms(3,IDXS,2)
IMG={}
for u in DEEP: IMG.setdefault(tuple(flatBT(u)),u)

fail=0; tot=0
fails=[]
for t in TB_TERMS:
 for c in PRINC_TERMS:
  tc=addBT(t,c); ftc=flatBT(tc)
  for v in IDXS:
   tgt=[Dsym(v)]+ftc; old=('D',v,tc)
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
        # candidate by surgery:
        cand=[]
        u1p,f=replace_princ(u1,old,('D',v,tc2))
        if f and flatBT(u1p)==want: cand.append(u1p)
        # candidate from image (the unique term with that flat)
        ii=IMG.get(tuple(want))
        if ii is not None: cand.append(ii)
        ok=any(in_TB(u) and scb_decomp(u,s0,fc2,b0) for u in cand)
        if not ok:
            fail+=1
            if len(fails)<6:
                fails.append((t,c,c2,v,u1,s0,b0,want, tuple(want) in IMG))
print(f"Conjunct(3) EXISTENTIAL: tot={tot} fail={fail}")
for fr in fails:
    print("FAIL:",fr)
