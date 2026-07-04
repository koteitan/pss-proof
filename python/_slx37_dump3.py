import sys, itertools, random
sys.path.insert(0,'python')
import red_model as R
def condIIIorIV(M):
    j1=R.Lng(M)-1
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    return R.entry(M,1,j1)>0 and R.entry(M,1,j0)>=R.entry(M,1,j1)
def info(M):
    L=R.Lng(M); j1=L-1
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    N=R.seg(M,jm3,j1); Np=R.Pred(N); RNp=R.Red(Np)
    br=R.Br(RNp); last=len(br)-1
    fnp=R.FirstNodes(RNp)[last]; jlp=R.Joints(RNp)[last]
    hp1=R.hasParent(RNp,1,fnp); p1=R.parent(RNp,1,fnp) if hp1 else None
    return dict(M=M,L=L,jm2=jm2,jm3=jm3,d=d,RNp=RNp,fnp=fnp,jlp=jlp,hp1=hp1,p1=p1,
                e0d=R.entry(RNp,0,d),e1d=R.entry(RNp,1,d),
                e0fnp=R.entry(RNp,0,fnp),e1fnp=R.entry(RNp,1,fnp),
                TrMax=R.TrMax(RNp))
random.seed(5)
V2=9
cols2=[(a,b) for a in range(0,V2+1) for b in range(0,a+1)]
seen=[]; stats={'n':0,'p1_eq_d':0,'diag_fnp':0,'jm3pos':0,'dgt1':0,'e1p1_eq_e1d':0}
for _ in range(400000):
    bl=random.randint(2,7); base=R.diagSeq(0,bl-1)
    t=random.randint(1,7)
    M=base+[random.choice(cols2) for _ in range(t)]
    if R.Lng(M)<5 or R.Lng(M)>12: continue
    L=R.Lng(M); j1=L-1
    if not(1<j1): continue
    if not R.hasParent(M,1,j1): continue
    if not R.hasParent(M,0,j1): continue
    if not condIIIorIV(M): continue
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
    if not(jm3<jm2): continue
    d=jm2-jm3; N=R.seg(M,jm3,j1)
    try: RNp=R.Red(R.Pred(N))
    except Exception: continue
    br=R.Br(RNp)
    if len(br)==0: continue
    last=len(br)-1; jlp=R.Joints(RNp)[last]
    if d!=jlp: continue
    try:
        if not R.is_standard(M): continue
    except Exception: continue
    d2=info(M); stats['n']+=1
    if d2['p1']==d: stats['p1_eq_d']+=1
    if d2['e0fnp']==d2['e1fnp']: stats['diag_fnp']+=1
    if jm3>0: stats['jm3pos']+=1
    if d>1: stats['dgt1']+=1
    if d2['hp1'] and R.entry(RNp,1,d2['p1'])==d2['e1d']: stats['e1p1_eq_e1d']+=1
    # collect interesting: jm3>0 or d>1
    if (jm3>0 or d>1) and len(seen)<12:
        seen.append(d2)
print("STATS",stats)
for s in seen:
    print("M=",R.fmt(s['M']),"jm2",s['jm2'],"jm3",s['jm3'],"d",s['d'],
          "RNp=",R.fmt(s['RNp']),"TrMax",s['TrMax'],"fnp",s['fnp'],"jlp",s['jlp'],
          "p1",s['p1'],"e1d",s['e1d'],"e1fnp",s['e1fnp'],"e0fnp",s['e0fnp'])
