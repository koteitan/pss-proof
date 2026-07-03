#!/usr/bin/env python3
exec(open('python/_wf6_addscb_c3.py').read().split('# CONSTRUCTIVE')[0])

# Tree-surgery construction of u1':
# Hypothesis: flatBT u1 = s1 @ (Dsym v # flatBT(t+c)) @ b1.
# By flatBT injectivity & grammar, (Dsym v # flatBT(t+c)) is the flat of the
# principal DB v (t+c) sitting at a unique position in u1's tree. Replace that
# principal subtree's argument (t+c) -> (t+c') to get u1'.
# We implement: find_and_replace(u1, oldprinc=DB(v, t+c), newprinc=DB(v, t+c'))
# by recursively scanning principal lists.

def replace_princ(t, old, new):
    """Replace first occurrence (DFS, left-to-right, outermost) of principal `old`
       in BT tree `t` by `new`. Returns (newtree, found)."""
    _, ps = t
    ps = list(ps)
    for i,p in enumerate(ps):
        if p == old:
            ps2 = ps[:i] + [new] + ps[i+1:]
            return Trm(ps2), True
        # recurse into p's argument
        _, pv, pa = p
        na, found = replace_princ(pa, old, new)
        if found:
            ps2 = ps[:i] + [('D', pv, na)] + ps[i+1:]
            return Trm(ps2), True
    return t, False

fail=0; tot=0; subst_fail=0; scb_fail=0
for t in TB_TERMS:
 for c in PRINC_TERMS:
  tc=addBT(t,c); ftc=flatBT(tc)
  for v in IDXS:
   tgt=[Dsym(v)]+ftc
   old=('D', v, tc)
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
        new=('D', v, tc2)
        want=s1+([Dsym(v)]+ftc2)+b1
        tot+=1
        u1p, found = replace_princ(u1, old, new)
        if not found or flatBT(u1p)!=want or not in_TB(u1p):
            subst_fail+=1; fail+=1
            if subst_fail<=5: print("SUBSTFAIL found=",found,"flatok=",flatBT(u1p)==want if found else None)
            continue
        if not scb_decomp(u1p,s0,fc2,b0):
            scb_fail+=1; fail+=1
            if scb_fail<=5: print("SCBFAIL u1=",u1,"c'=",c2,"s0=",s0,"b0=",b0)
print(f"Conjunct(3) SURGERY: tot={tot} fail={fail} subst_fail={subst_fail} scb_fail={scb_fail}")
