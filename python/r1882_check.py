import itertools, sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Red, Lng, entry, P, monoT, zeroT, TrMax, Br, seg,
                       parent, FirstNodes, Joints)
import red_model as rm
from trans_model import (Trans, Mark, Pred, reduced, adm, Adm, ZB, Dpt, addBT, PB,
                         bpHeadV, bpHeadT)

def enum(ml, me):
    cols = [(a,b) for a in range(me+1) for b in range(me+1)]
    for L in range(2, ml+1):
        for M in itertools.product(cols, repeat=L):
            yield list(M)

def transJ0(M):
    return parent(M, 0, Lng(M)-1)
def transJm1(M):
    return Adm(M, transJ0(M))

# clause checkers given M (RT_PS, PT_PS, Br!=[], j1>1)
def check_clauses(M):
    j1 = Lng(M)-1
    J1 = Lng(Br(M))-1
    j0p = Joints(M)[J1]
    j1p = FirstNodes(M)[J1]
    e10 = entry(M,1,0)
    tP = Trans(Pred(M))
    tM = Trans(M)
    e1j1p = entry(M,1,j1p)
    e1j0p = entry(M,1,j0p)
    # clause (1): exists unique t1 with tP = D_e10 t1 and tM = D_e10 (t1 + D_e1j1p 0)
    c1 = False
    if tP[1] and tP[1][0][0]=='D' and tP[1][0][1]==e10 and len(tP[1])==1:
        t1 = tP[1][0][2]
        rhs = Dpt(e10, addBT(t1, Dpt(e1j1p, ZB)))
        c1 = (tM == rhs) and (j1p==j1) and (TrMax(M)==0 or j0p<TrMax(M)) \
             and (entry(M,0,j1p)==entry(M,1,j1p) or adm(M,j0p))
    # clause (2): tP = D_e10 (fst t12), tM = D_e10 (fst + D_e1j0p (snd))
    c2 = False
    if tP[1] and tP[1][0][0]=='D' and tP[1][0][1]==e10 and len(tP[1])==1:
        inner = tP[1][0][2]   # = fst t12
        # tM = D_e10 (inner + D_e1j0p snd)  for some snd
        if tM[1] and tM[1][0][0]=='D' and tM[1][0][1]==e10 and len(tM[1])==1:
            body = tM[1][0][2]  # should be inner + D_e1j0p snd
            ip = inner[1]
            if body[1][:len(ip)] == ip and len(body[1])==len(ip)+1:
                last = body[1][len(ip)]
                if last[0]=='D' and last[1]==e1j0p:
                    c2 = (j1p==j1) and (entry(M,0,j1p)>entry(M,1,j1p)) and (not adm(M,j0p))
    # clause (3): tP = D_e10 (A + D_e1j1p B), tM = D_e10 (A + D_e1j1p C)
    c3 = clause34(tP, tM, e10, e1j1p)
    # clause (4): same with e1j0p
    c4 = clause34(tP, tM, e10, e1j0p)
    return c1, c2, c3, c4

def clause34(tP, tM, e10, ev):
    # tP = D_e10 (A + D_ev B); tM = D_e10 (A + D_ev C). exists unique (A,B,C).
    def split(t):
        if not (t[1] and t[1][0][0]=='D' and t[1][0][1]==e10 and len(t[1])==1):
            return None
        body = t[1][0][2][1]  # list of BPs = A ++ [D_ev rest] ?
        # find last BP with head v==ev? The form is A + D_ev X where A's last need not be ev.
        # structurally: body = A_bps + [('D', ev, X)] with that being exactly one principal.
        if not body: return None
        # try: the principal at some position k is ('D',ev,X) and A = body[:k], and len(body)=k+1
        k = len(body)-1
        if body[k][0]=='D' and body[k][1]==ev:
            return tuple(body[:k]), body[k][2]
        return None
    sp = split(tP); sm = split(tM)
    if sp is None or sm is None: return False
    A1, B = sp; A2, C = sm
    return A1 == A2

cnt = {'tot':0,'base':0,'adm0':0,'admpos':0}
fails = []
basefails=[]; admposfails=[]
for M in enum(5, 3):
    if not (entry(M,0,0)==0 and entry(M,1,0)==0): continue
    if not monoT(M): continue
    if not reduced(M): continue   # RT_PS
    # PT_PS = T_PS and monoT; T_PS = nonempty. monoT already. ok
    if Br(M)==[]: continue
    j1 = Lng(M)-1
    if not (j1>1): continue
    cnt['tot']+=1
    try:
        cs = check_clauses(M)
    except Exception as e:
        fails.append((M,'EXC',str(e))); continue
    disj = any(cs)
    n = j1 - TrMax(M)   # induction measure
    base = (n==1)
    adm0 = (transJm1(M)==0)
    if base: cnt['base']+=1
    if adm0: cnt['adm0']+=1
    if (not adm0): cnt['admpos']+=1
    if not disj:
        fails.append((M, cs, (n, TrMax(M), j1, transJm1(M))))
    if base and not disj: basefails.append(M)
    if (not adm0) and not disj: admposfails.append((M, cs))

print("total RT_PS∩PT_PS, Br≠[], j1>1 (len≤5, e≤3):", cnt['tot'])
print("  base (n=1):", cnt['base'], " adm0:", cnt['adm0'], " admpos:", cnt['admpos'])
print("disjunction FAILS:", len(fails))
for f in fails[:8]: print("  FAIL", f)
print("base fails:", len(basefails))
for m in basefails[:8]: print("  BASEFAIL", m)
print("admpos fails:", len(admposfails))
for m in admposfails[:8]: print("  ADMPOSFAIL", m)

print("\n=== detailed: which clause per regime ===")
import collections
base_clause = collections.Counter()
admpos_clause = collections.Counter()
adm0_clause = collections.Counter()
base_j1eq = collections.Counter()
admpos_j1eq = collections.Counter()
for M in enum(5, 3):
    if not (entry(M,0,0)==0 and entry(M,1,0)==0): continue
    if not monoT(M): continue
    if not reduced(M): continue
    if Br(M)==[]: continue
    j1 = Lng(M)-1
    if not (j1>1): continue
    cs = check_clauses(M)
    n = j1 - TrMax(M)
    adm0 = (transJm1(M)==0)
    J1 = Lng(Br(M))-1
    j1p = FirstNodes(M)[J1]
    j0p = Joints(M)[J1]
    which = tuple(i+1 for i,c in enumerate(cs) if c)
    if n==1:
        base_clause[which]+=1
        base_j1eq[(j1p==j1, j0p==TrMax(M), TrMax(M)==j1-1)]+=1
    if not adm0:
        admpos_clause[which]+=1
        admpos_j1eq[(j1p==j1,)]+=1
print("BASE (n=1) clauses satisfied:", dict(base_clause))
print("BASE (j1p==j1, j0p==TrMax, TrMax==j1-1):", dict(base_j1eq))
print("ADMPOS clauses satisfied:", dict(admpos_clause))
print("ADMPOS (j1p==j1):", dict(admpos_j1eq))
