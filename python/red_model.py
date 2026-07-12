#!/usr/bin/env python3
"""Faithful executable model of pss_defs.thy (the pair-sequence system).

Implements, 1:1 from pss_defs.thy: entry/Lng, nextrel0/1, le0/le1/leR, zeroT/
monoT/multiT, Pcut/P, TrMax/Br/FirstNodes/Joints, diagSeq/IncrFirst, oper (M[n]),
Pred, and Red.  A pairseq is a list of (a,b) tuples (a=row0, b=row1); equivalently
a 2-row Bashicu matrix whose columns are the pairs.

Use it to empirically test article propositions (find counterexamples, gauge the
domain on which a claim holds) before committing to an Isabelle proof.  See
README.md.  Standardness (`is_standard`) is delegated to the external yaBMS C tool
(set $BMS_BIN; default tmp/yaBMS/c/bms) so it is independent of this model."""
import sys, os, subprocess
from functools import lru_cache
sys.setrecursionlimit(100000)

def Lng(M): return len(M)
def entry(M,i,j): return M[j][i]

def nextrel0(M,j0,j1):
    n=Lng(M)
    if not(j0<n and j1<n and j0<j1): return False
    if not(entry(M,0,j0)<entry(M,0,j1)): return False
    return all(entry(M,0,j)>=entry(M,0,j1) for j in range(j0+1,j1))

def reach(M,nextf):
    # transitive-reflexive closure reachability matrix
    n=Lng(M)
    R=[[i==j for j in range(n)] for i in range(n)]
    edges=[(a,b) for a in range(n) for b in range(n) if nextf(M,a,b)]
    changed=True
    while changed:
        changed=False
        for a in range(n):
            for b in range(n):
                if R[a][b]:
                    for (c,d) in edges:
                        if b==c and not R[a][d]:
                            R[a][d]=True; changed=True
    return R

def le0(M,j0,j1):
    n=Lng(M)
    if not(j0<n and j1<n): return False
    return reach(M,nextrel0)[j0][j1]

def nextrel1(M,j0,j1):
    n=Lng(M)
    if not(j0<n and j1<n and j0<j1): return False
    if not(entry(M,1,j0)<entry(M,1,j1)): return False
    if not le0(M,j0,j1): return False
    return all(entry(M,1,j)>=entry(M,1,j1) for j in range(j0+1,n) if le0(M,j,j1))

def le1(M,j0,j1):
    n=Lng(M)
    if not(j0<n and j1<n): return False
    return reach(M,nextrel1)[j0][j1]

def nextR(M,i,j0,j1): return nextrel0(M,j0,j1) if i==0 else nextrel1(M,j0,j1)
def leR(M,i,j0,j1): return le0(M,j0,j1) if i==0 else le1(M,j0,j1)

def zeroT(M): return Lng(M)==1 and entry(M,1,0)==0
def monoT(M): return (not zeroT(M)) and le0(M,0,Lng(M)-1)
def multiT(M): return (not zeroT(M)) and (not monoT(M))

def Pcut(M):
    n=Lng(M)
    for j in range(1,n):     # 0<j<=Lng-1
        if le0(M,j,n-1): return j
    raise ValueError("no Pcut")

def P(M):
    if multiT(M) and Lng(M)>1:
        c=Pcut(M)
        return P(M[:c])+[M[c:]]
    return [M]

def TrMax(M):
    n=Lng(M); k=0
    while k< n and all(nextrel1(M,jp,jp+1) for jp in range(k)):
        if k+1<= n-1 and all(nextrel1(M,jp,jp+1) for jp in range(k+1)):
            k+=1
        else:
            break
    # robust: largest k with nextrel1 for all j'<k
    k=0
    while all(nextrel1(M,jp,jp+1) for jp in range(k+1)) and k< n-1:
        k+=1
    # but if even k=0 set... {j: forall j'<j ...} contains 0 always; find max
    best=0
    for cand in range(0,n):
        if all(nextrel1(M,jp,jp+1) for jp in range(cand)):
            best=cand
    return best

def seg(M,a,b): return M[a:b+1]
def diagSeq(a,b): return [(j,j) for j in range(a,b+1)]
def IncrFirst(M): return [(a+1,b) for (a,b) in M]
def funpow(f,n,x):
    for _ in range(n): x=f(x)
    return x

def IdxSum(Q):
    return [sum(len(Q[k]) for k in range(J)) for J in range(len(Q)+1)]

def Br(M):
    if TrMax(M)==Lng(M)-1: return []
    return P(seg(M,TrMax(M)+1,Lng(M)-1))

def FirstNodes(M):
    t=TrMax(M)
    return [t+1+x for x in IdxSum(Br(M))]

def THE_nextR(M,i,j1):
    cands=[j for j in range(Lng(M)) if nextR(M,i,j,j1)]
    if len(cands)!=1: return None
    return cands[0]

def Joints(M):
    fn=FirstNodes(M); b=Br(M)
    res=[]
    for J in range(len(b)):
        j=THE_nextR(M,0,fn[J])
        res.append(j)
    return res

def Red(M,depth=0):
    if depth>200: raise RuntimeError("Red too deep "+str(M))
    if zeroT(M): return [(0,0)]
    if multiT(M):
        out=[]
        for blk in P(M): out+=Red(blk,depth+1)
        return out
    # mono
    j1=Lng(M)-1; j1p=TrMax(M); m00=entry(M,0,0); m10=entry(M,1,0)
    if m00==0 and m10==0:
        if j1p==j1:
            return diagSeq(m10,m10+j1)
        else:
            out=diagSeq(0,j1p)
            b=Br(M); fn=FirstNodes(M); jn=Joints(M)
            for J in range(len(b)):
                br10=entry(b[J],1,0)
                if br10==0:
                    np=0
                else:
                    par=THE_nextR(M,1,fn[J])
                    np=par+1
                eJ=jn[J]+1-np
                NJ=[(m00+jn[J]+1, m10+np)]+b[J][1:]
                out+=funpow(IncrFirst,eJ,Red(NJ,depth+1))
            return out
    else:
        if m10==0:
            core=[(entry(M,0,j)-m00, entry(M,1,j)) for j in range(j1+1)]
            return Red(core,depth+1)
        else:
            N=Red(diagSeq(0,m10-1)+funpow(IncrFirst,m10,M),depth+1)
            jN=Lng(N)-1
            sg=seg(N,m10,jN)
            if m10<=jN and len(sg)>0 and monoT(sg):
                return [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
            else:
                return M

def idx1(M,j1): return 1 if entry(M,1,j1)>0 else 0
def hasParent(M,i,j1):
    return sum(1 for j0 in range(Lng(M)) if nextR(M,i,j0,j1))==1
def parent(M,i,j1):
    for j0 in range(Lng(M)):
        if nextR(M,i,j0,j1): return j0
    return None
def oper(M,n):
    j1=Lng(M)-1
    if j1==0: return M
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return M[:-1] if Lng(M)>1 else M  # Pred
    i1=idx1(M,j1)
    if not hasParent(M,i1,j1): return M[:-1] if Lng(M)>1 else M
    j0=parent(M,i1,j1)
    d0=(entry(M,0,j1)-entry(M,0,j0)) if i1>0 else 0
    d1=(entry(M,1,j1)-entry(M,1,j0)) if i1>1 else 0
    out=M[:j0]
    for k in range(n):
        for j in range(j0,j1):
            out=out+[(entry(M,0,j)+k*d0, entry(M,1,j)+k*d1)]
    return out

def Red_trace(M,calls,depth=0):
    """Like Red but appends every recursive Red-argument (the smaller calls) to `calls`."""
    if depth>200: raise RuntimeError("deep")
    if zeroT(M): return [(0,0)]
    if multiT(M):
        out=[]
        for blk in P(M):
            calls.append(("Pblock",blk)); out+=Red_trace(blk,calls,depth+1)
        return out
    j1=Lng(M)-1; j1p=TrMax(M); m00=entry(M,0,0); m10=entry(M,1,0)
    if m00==0 and m10==0:
        if j1p==j1: return diagSeq(m10,m10+j1)
        out=diagSeq(0,j1p); b=Br(M); fn=FirstNodes(M); jn=Joints(M)
        for J in range(len(b)):
            br10=entry(b[J],1,0)
            np=0 if br10==0 else nextR_THE(M,1,fn[J])+1
            eJ=jn[J]+1-np
            NJ=[(m00+jn[J]+1, m10+np)]+b[J][1:]
            calls.append(("NJ",NJ)); out+=funpow(IncrFirst,eJ,Red_trace(NJ,calls,depth+1))
        return out
    else:
        if m10==0:
            core=[(entry(M,0,j)-m00, entry(M,1,j)) for j in range(j1+1)]
            calls.append(("core",core)); return Red_trace(core,calls,depth+1)
        else:
            Narg=diagSeq(0,m10-1)+funpow(IncrFirst,m10,M)
            calls.append(("Narg",Narg)); N=Red_trace(Narg,calls,depth+1)
            jN=Lng(N)-1; sg=seg(N,m10,jN)
            if m10<=jN and len(sg)>0 and monoT(sg):
                return [(entry(N,0,j)-entry(N,0,m10)+entry(N,1,m10), entry(N,1,j)) for j in range(m10,jN+1)]
            return M

def nextR_THE(M,i,j1):
    cs=[j for j in range(Lng(M)) if nextR(M,i,j,j1)]
    return cs[0] if len(cs)==1 else (_ for _ in ()).throw(ValueError("nonunique"))

def red_le_holds(M):
    R=Red(M)
    if Lng(R)!=Lng(M): return ("LNG_MISMATCH",R)
    n=Lng(M)
    for i in (0,1):
        for j0 in range(n):
            for j1 in range(n):
                if leR(M,i,j0,j1)!=leR(R,i,j0,j1):
                    return (False,(i,j0,j1,R))
    return (True,R)

def fmt(M): return "".join(f"({a},{b})" for (a,b) in M)

# ---- convenience predicates ----
def Pred(M): return M[:-1] if Lng(M)>1 else M       # §5.2 Pred
def reduced(M): return Red(M)==M                     # RT_PS membership (Red M = M)

# ---- §6.3 admissibility ----
def nadm(M,j):                                       # 非M許容
    if j>Lng(M): return True
    jm1 = j-1 if j>=1 else 0                          # nat subtraction: 0-1=0
    return nextR(M,1,jm1,j) and nextR(M,1,j,j+1)
def adm(M,j): return not nadm(M,j)                   # M許容
def AdmSet(M): return frozenset(j for j in range(Lng(M)+1) if adm(M,j))   # ℕ_M
def Adm(M,j):                                        # 許容化 Adm_M(j)
    if adm(M,j): return j
    return max(jp for jp in range(j) if adm(M,jp))
def marked(M,m):                                     # (M,m) ∈ Marked
    return Lng(M)>=1 and adm(M,m) and leR(M,0,m,Lng(M)-1)

# ---- standardness via the external yaBMS C tool (independent oracle) ----
_BMS_BIN = os.environ.get(
    "BMS_BIN",
    os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                 "tmp", "yaBMS", "c", "bms"))

def is_standard(M):
    """True iff M is a standard-form pair sequence IN THE USUAL (u = 0) SENSE, per yaBMS `bms -s`.

    🚨 THIS IS **NOT** THE ARTICLE'S ST_PS. DO NOT USE ITS NEGATION. 🚨

    The article (content.md 1340-1346) takes ST_PS to be the least set containing the diagonal
    ((j,j))_{j=u}^{v} for EVERY u <= v, closed under M[n] — and says so explicitly: "通常は標準形
    ペア数列と言ったら 3 行バシク行列 ((0,0,0)(1,1,1)) の展開で現れるものを指すが、それは上の条件に
    おいて u = 0 としたものに対応するため、ここでの流儀では標準形が通常より広い対象を指す".
    `pss_defs.thy`'s `inductive_set ST_PS` is faithful to that.

    yaBMS's isstd() seeds from column (0,0) only, so it decides the u = 0 orbit ALONE.  Measured on a
    3000-element wide ST_PS orbit (diagSeq u v for u = 0..3, closed under oper): 2634 accepted, 366
    REJECTED — every one of them a genuine ST_PS member with u > 0.  Witnesses: (1,1), (2,2),
    (1,1)(2,2), (1,1)(2,2)(3,3).

        is_standard(M) == True   ==>  M in ST_PS          SOUND
        is_standard(M) == False  ==>  M not in ST_PS      **FALSE**

    So filtering a corpus with `if not is_standard(M): continue` silently deletes the whole u > 0
    region, and the inference "the counterexample is non-standard, therefore the claim holds on ST_PS"
    is UNSOUND.  Use `is_standard_wide` below, or build the orbit directly from diagSeq(u, v).
    """
    if not os.path.exists(_BMS_BIN):
        raise FileNotFoundError(
            f"yaBMS binary not found at {_BMS_BIN}; set $BMS_BIN to the `bms` tool.")
    out = subprocess.run([_BMS_BIN, "-s", fmt(M)], capture_output=True, text=True).stdout.strip()
    return out == "1"


def is_standard_wide(M):
    """True iff M is a standard form in the ARTICLE's (wider) sense — i.e. M in ST_PS.

    ST_PS is the DIAGONAL-TRANSLATE family of the usual u = 0 orbit.  `oper` is equivariant under
    adding (u, u) to every entry, and the first column of a diagSeq(u, v) orbit stays (u, u), so

        M in orbit(diagSeq(u, ·))   iff   M - (u,u) in orbit(diagSeq(0, ·)),   u = M_{0,0}.

    Verified: orbit(diagSeq 1 4) == (1,1)-translate of orbit(diagSeq 0 3), 26/26 elements, no
    exceptions.  NOTE the translate is on BOTH coordinates — shifting row 0 alone is WRONG
    (it maps (1,1)(2,2) to (0,1)(1,2), which is not even reduced).
    """
    if not M:
        return False
    u = M[0][0]
    if M[0][1] != u:                      # a standard form always starts on the diagonal
        return False
    if u == 0:
        return is_standard(M)
    if any(a < u or b < u for (a, b) in M):
        return False
    return is_standard([(a - u, b - u) for (a, b) in M])

if __name__=="__main__":
    # quick self-test: the §6.5 Red_le counterexample (article claims T_PS-wide; false)
    M=[(0,0),(0,1)]
    print("Red", fmt(M), "=", fmt(Red(M)), "(expect (0,0)(1,1))")
    print("red_le_holds:", red_le_holds(M), "(expect False)")
