#!/usr/bin/env python3
"""r34: find condIV hosts, characterize guard jm3<jm2 and dd. Lean + progress."""
import sys, random
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
    st={k:0 for k in ['IV_tot','IV_guard','IV_guard_dd0','IV_guard_ddpos',
                      'III_tot','III_guard']}
    st['ex']=[]
    total=0
    ob=orbit(45000,16,4)
    print("orbit",len(ob),flush=True)
    for i,M in enumerate(ob):
        if i%10000==0: print("  ..",i,flush=True)
        try:
            if not R.is_standard(M): continue
        except Exception: continue
        j1=R.Lng(M)-1
        if not (1<j1 and R.hasParent(M,1,j1)): continue
        if condIV(M):
            st['IV_tot']+=1
            jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
            if d>0:
                st['IV_guard']+=1
                dd=R.entry(M,0,jm3)-R.entry(M,1,jm3)
                st['IV_guard_dd0' if dd==0 else 'IV_guard_ddpos']+=1
                if len(st['ex'])<12: st['ex'].append((R.fmt(M),'d=%d'%d,'dd=%d'%dd))
        elif condIII(M):
            st['III_tot']+=1
            jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
            if jm2-jm3>0: st['III_guard']+=1
    print("condIV total:",st['IV_tot']," guard(jm3<jm2):",st['IV_guard'],
          " [dd=0:",st['IV_guard_dd0']," dd>0:",st['IV_guard_ddpos'],"]")
    print("condIII total:",st['III_tot']," guard:",st['III_guard'])
    if st['ex']: print("condIV guard EXAMPLES:",st['ex'])
    else: print("NO condIV guard host found.")

if __name__=='__main__': main()
