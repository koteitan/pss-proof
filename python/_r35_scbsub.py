#!/usr/bin/env python3
"""r35-OTDEEP: is 'rightmost-spine scb-substitution with a SMALLER OT principal
preserves OT' true?  This is the candidate GENERAL lemma that would close all
four deep-insertion legs (each exchange NF exhibits Trans(N[m]) as t_old with the
marked core replaced by a smaller OT principal at the SAME (s,b), b all-RP).

We test on RANDOM OT terms:
  (A) GENERAL: pick a rightmost-spine principal c, replace with ANY smaller OT
      principal c' (random), check isOT of the result.
  (B) SAME-HEAD: c=D_u(body), c'=D_u(body') with body' < body and c' OT
      (mimics the exchange NF: same outer head, body shrinks).
Report pass fractions and print the FIRST counterexample of each.
"""
import sys, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
import buchholz as bu

ZERO = []
def D(v,a): return ('D', v, a)

def in_OT(a): return bu.in_OT(a)
def lt(a,b): return bu.lt_term(a,b)
def le(a,b): return bu.le_term(a,b)
def ltp(p,q): return bu.lt_princ(p,q)

def gen_OT(rng, maxv=3, depth=3):
    """random small OT term (list of principals, weakly decreasing)."""
    if depth==0: return ZERO
    n = rng.randrange(0,3)
    ps = []
    prev = None
    for _ in range(n):
        v = rng.randrange(0, maxv+1)
        b = gen_OT(rng, maxv, depth-1)
        p = D(v,b)
        if not in_OT([p]): continue
        if prev is not None and not le([p],[prev]):
            # enforce weakly decreasing: skip if bigger than prev
            continue
        ps.append(p); prev=p
    # ensure OT
    if not in_OT(ps):
        # trim to prefix that is OT
        out=[]
        for p in ps:
            if in_OT(out+[p]): out.append(p)
        ps=out
    return ps

def rightmost_positions(a):
    """yield 'paths' to rightmost-spine principals: a path is list of indices,
    always taking the LAST principal then descending into its body."""
    paths=[]
    cur=a; path=[]
    while cur:
        i=len(cur)-1
        path=path+[i]
        paths.append(list(path))
        cur=cur[i][2]  # body of last principal
    return paths

def get_at(a, path):
    cur=a
    for i in path[:-1]:
        cur=cur[i][2]
    return cur[path[-1]]

def set_at(a, path, newp):
    if len(path)==1:
        return a[:path[0]]+[newp]+a[path[0]+1:]
    i=path[0]
    p=a[i]
    newbody=set_at(p[2], path[1:], newp)
    return a[:i]+[D(p[1],newbody)]+a[i+1:]

def smaller_OT_principals(c, rng, maxv=3, tries=40):
    """random OT principals c' with c' < c."""
    out=[]
    for _ in range(tries):
        v=rng.randrange(0,maxv+1)
        b=gen_OT(rng,maxv,2)
        cp=D(v,b)
        if in_OT([cp]) and ltp(cp,c):
            out.append(cp)
    return out

def samehead_smaller(c, rng, maxv=3, tries=40):
    """c=D_u(body); c'=D_u(body') with body'<body, c' OT (same head)."""
    u,body=c[1],c[2]
    out=[]
    for _ in range(tries):
        bp=gen_OT(rng,maxv,2)
        cp=D(u,bp)
        if in_OT([cp]) and lt(bp,body):
            out.append(cp)
    return out

def main():
    seeds=range(1,40)
    genA=[0,0,0]  # tot, pass, cexprinted
    genB=[0,0,0]
    cexA=None; cexB=None
    for sd in seeds:
        rng=random.Random(sd)
        for _ in range(400):
            t=gen_OT(rng,3,3)
            if len(t)<1 or not in_OT(t): continue
            paths=rightmost_positions(t)
            if not paths: continue
            path=rng.choice(paths)
            c=get_at(t,path)
            # (A) general
            for cp in smaller_OT_principals(c,rng)[:4]:
                tnew=set_at(t,path,cp)
                genA[0]+=1
                ok=in_OT(tnew)
                if ok: genA[1]+=1
                elif cexA is None:
                    cexA=(t,path,c,cp,tnew)
            # (B) same-head
            for cp in samehead_smaller(c,rng)[:4]:
                tnew=set_at(t,path,cp)
                genB[0]+=1
                ok=in_OT(tnew)
                if ok: genB[1]+=1
                elif cexB is None:
                    cexB=(t,path,c,cp,tnew)
    print('(A) GENERAL smaller-OT rightmost subst:   %d/%d pass (%.3f)'
          %(genA[1],genA[0], genA[1]/genA[0] if genA[0] else 0))
    if cexA:
        t,path,c,cp,tn=cexA
        print('   CEX-A t=%s path=%s c=%s -> c\'=%s  result=%s (NOT OT)'
              %(bu.fmt(t),path,bu.fmt([c]),bu.fmt([cp]),bu.fmt(tn)))
    print('(B) SAME-HEAD body-shrink rightmost subst: %d/%d pass (%.3f)'
          %(genB[1],genB[0], genB[1]/genB[0] if genB[0] else 0))
    if cexB:
        t,path,c,cp,tn=cexB
        print('   CEX-B t=%s path=%s c=%s -> c\'=%s  result=%s (NOT OT)'
              %(bu.fmt(t),path,bu.fmt([c]),bu.fmt([cp]),bu.fmt(tn)))

if __name__=='__main__':
    main()
