#!/usr/bin/env python3
"""r34: WHY is condIV jm2 always admissible? probe jm2 vs j0, adm structure."""
import sys
sys.path.insert(0, 'python')
import red_model as R

def condIV(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and (not R.adm(M,j0))
def condIII(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and R.adm(M,j0)

def orbit(cap, maxlen, width):
    seen=set(); frontier=[]
    for u in range(0,4):
        for v in range(u,u+4):
            d=tuple(R.diagSeq(u,v)); seen.add(d); frontier.append(list(d))
    out=[]
    while frontier and len(out)<cap:
        M=frontier.pop(0); out.append(M)
        if R.Lng(M)>=maxlen: continue
        for n in range(1,width):
            try: Mn=R.oper(M,n)
            except Exception: continue
            t=tuple(Mn)
            if t not in seen and R.Lng(Mn)<=maxlen:
                seen.add(t); frontier.append(Mn)
    return out

def main():
    st={k:0 for k in ['IV','IV_jm2eqj0','IV_jm2adm','IV_j1adm',
                      'III','III_jm2eqj0','III_jm2adm']}
    exs=[]
    for M in orbit(45000,16,4):
        try:
            if not R.is_standard(M): continue
        except Exception: continue
        j1=R.Lng(M)-1
        if not (1<j1 and R.hasParent(M,1,j1)): continue
        j0=R.parent(M,0,j1); jm2=R.parent(M,1,j1)
        if condIV(M):
            st['IV']+=1
            if jm2==j0: st['IV_jm2eqj0']+=1
            if R.adm(M,jm2): st['IV_jm2adm']+=1
            # is j1 itself admissible? (condIV has entry1(j1)>0)
            if len(exs)<10:
                exs.append((R.fmt(M),'j0=%d'%j0,'jm2=%d'%jm2,
                            'admjm2=%s'%R.adm(M,jm2),'e1j0=%d'%R.entry(M,1,j0),
                            'e1jm2=%d'%R.entry(M,1,jm2),'e1j1=%d'%R.entry(M,1,j1)))
        elif condIII(M):
            st['III']+=1
            if jm2==j0: st['III_jm2eqj0']+=1
            if R.adm(M,jm2): st['III_jm2adm']+=1
    print("condIV:",st['IV']," jm2==j0:",st['IV_jm2eqj0']," adm(jm2):",st['IV_jm2adm'])
    print("condIII:",st['III']," jm2==j0:",st['III_jm2eqj0']," adm(jm2):",st['III_jm2adm'])
    print("condIV examples:")
    for e in exs: print("  ",e)

if __name__=='__main__': main()
