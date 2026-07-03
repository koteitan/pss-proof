#!/usr/bin/env python3
"""Refined §8 use-site analysis.

KEY FIX vs v1: the §8.6 lemma claims (s, D_u t', b) is an scb-decomp of t[0]^k
for SOME 0<k<=w+1 (ITERATED [0]), not a single peel.  So at 6028/6038 we must
check whether iterating [0] up to w+1 times turns D_u(t'+D_w 0) into D_u t'
(as a SUB-term, but here it's top-level / isolated so equality of the principal).

We test BOTH:
  (a) does some 1<=k<=w+1 give  (D_u(t'+D_w 0))[0]^k == D_u t'   (isolated §8.6),
  (b) the A25 'clean one-step' predicate w==0 or u>=w or t'==0.

We separate by whether t' is a LEAF (t'=0), a NON-NESTING body (clean), or a
genuinely NESTED principal body that would trigger A26.
"""
import sys
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/python")
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/git/python")
import trans_model as TM
import red_model as rm
from red_model import Lng, entry, P, monoT, parent
import buchholz as B

def tm_to_buc(t):
    return [('D', p[1], tm_to_buc(p[2])) for p in t[1]]
def fmtbuc(a): return B.fmt(a)

def iter_peel_86(u, tprime_buc, w, maxk=60):
    """Return smallest k with (D_u(t'+D_w 0))[0]^k == D_u t', or None."""
    body = tprime_buc + [('D', w, [])]
    host = [('D', u, body)]
    if not B.in_TB(host): return ('not_TB', None)
    want = [('D', u, tprime_buc)]
    cur = host
    for k in range(1, maxk+1):
        cur = B.bracket(cur, B.ZERO)
        if cur == want: return ('ok', k)
        if cur == []: return ('hit0', None)
    return ('nofix', None)

def iter_anni_87(u, tprime_buc, maxk=60):
    """smallest k with (D_u t')[0]^k == D_u 0, or None."""
    host = [('D', u, tprime_buc)]
    if not B.in_TB(host): return ('not_TB', None)
    want = [('D', u, [])]
    cur = host
    for k in range(1, maxk+1):
        cur = B.bracket(cur, B.ZERO)
        if cur == want: return ('ok', k)
        if cur == []: return ('hit0', None)
    return ('nofix', None)

def gen_pairseqs(maxlen, maxval):
    seqs=[]
    def rec(cur):
        if len(cur)>=2: seqs.append(list(cur))
        if len(cur)>=maxlen: return
        for a in range(0,maxval+1):
            for b in range(0,a+1):
                cur.append((a,b)); rec(cur); cur.pop()
    rec([(0,0)])
    return seqs

def main():
    seqs = gen_pairseqs(maxlen=6, maxval=3)
    buckets = {'I/III/V (6028)':[], 'II/IV-left (6038)':[], 'II/IV-noleft 8.7 (6052)':[], 'VI (5747)':[]}
    seen=0; err=0
    for M in seqs:
        try:
            if Lng(M)<2 or not TM.reduced(M) or not monoT(M): continue
            j1=Lng(M)-1; jp=parent(M,0,j1)
            t1=TM.Trans(TM.Pred(M))
            if t1==TM.ZB: continue
            c1=TM.Mark(TM.Pred(M), TM.Adm(M,jp))
            v=TM.bpHeadV(c1); t2=TM.bpHeadT(c1)
            cI=TM.condI(M); cIII=TM.condIII(M); cV=TM.condV(M); cVI=TM.condVI(M)
            cIIIV = not (cI or cIII or cV or cVI)
            seen+=1
            m1j1=entry(M,1,j1); m1jp=entry(M,1,jp)
            t2b=tm_to_buc(t2)
            if cI or cIII or cV:
                tag,k = iter_peel_86(v, t2b, m1j1)
                is_leaf=(t2b==[]); clean=is_leaf or m1j1==0 or v>=m1j1
                buckets['I/III/V (6028)'].append((M,v,t2b,m1j1,is_leaf,clean,tag,k))
            elif cVI:
                tag,k = iter_peel_86(v, [], m1j1)
                buckets['VI (5747)'].append((M,v,[],m1j1,True,True,tag,k))
            elif cIIIV and t2!=TM.ZB:
                Pt2=TM.PB(t2); J1b=len(Pt2)-1; pj=Pt2[J1b]
                leftDj0=(TM.bpHeadV(pj)==m1jp)
                if leftDj0:
                    t4b=tm_to_buc(TM.bpHeadT(pj))
                    tag,k=iter_peel_86(m1jp,t4b,m1j1)
                    is_leaf=(t4b==[]); clean=is_leaf or m1j1==0 or m1jp>=m1j1
                    buckets['II/IV-left (6038)'].append((M,m1jp,t4b,m1j1,is_leaf,clean,tag,k))
                else:
                    body=t2b+[('D',m1j1,[])]
                    tag,k=iter_anni_87(m1jp,body)
                    is_leaf=(body==[])
                    # nested? body has >1 principal OR its last principal is itself nested
                    nested=(len(body)>1) or (len(body)==1 and body[0][2]!=[])
                    buckets['II/IV-noleft 8.7 (6052)'].append((M,m1jp,body,m1j1,is_leaf,not nested,tag,k))
            elif cIIIV and t2==TM.ZB:
                # c2 = D_v D_{m1jp} D_{m1j1} 0 ; the 8.7 applies to D_{m1jp} D_{m1j1} 0 (leaf chain)
                tag,k=iter_anni_87(m1jp,[('D',m1j1,[])])
                buckets['II/IV-noleft 8.7 (6052)'].append((M,m1jp,[('D',m1j1,[])],m1j1,False,True,tag,k))
        except Exception as e:
            err+=1
            if err<=5: print("ERR",M,repr(e))
    print(f"scanned {seen} Trans-recursion hosts; errors {err}\n")
    for name,rs in buckets.items():
        if not rs:
            print(f"[{name}] none"); continue
        nleaf=sum(1 for r in rs if r[4])
        nclean=sum(1 for r in rs if r[5])
        nok=sum(1 for r in rs if r[6]=='ok')
        nbad=[r for r in rs if r[6]!='ok']
        print(f"[{name}] n={len(rs)}  leaf={nleaf}  clean_pred={nclean}  empirically_annihilates(ok)={nok}  FAIL={len(nbad)}")
        for r in nbad[:10]:
            M,u,tb,w,isl,cl,tag,k=r
            print(f"   FAIL M={M} u={u} t'={fmtbuc(tb)} w={w} leaf={isl} clean={cl} -> {tag}")
        # show non-leaf successes to see what 'clean non-leaf' looks like
        nlsucc=[r for r in rs if r[6]=='ok' and not r[4]]
        for r in nlsucc[:3]:
            M,u,tb,w,isl,cl,tag,k=r
            print(f"   ok(non-leaf) M={M} u={u} t'={fmtbuc(tb)} w={w} clean={cl} k={k}")

if __name__=="__main__":
    main()
