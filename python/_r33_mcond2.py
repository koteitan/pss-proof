#!/usr/bin/env python3
"""r33 MCOND / M0RUN validation + proof sub-fact probes (faster)."""
import sys
sys.path.insert(0, 'python')
import red_model as R

def condIII(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and R.adm(M,j0)
def condIV(M):
    j1=R.Lng(M)-1
    if R.entry(M,1,j1)<=0: return False
    j0=R.parent(M,0,j1)
    if j0 is None: return False
    return R.entry(M,1,j0)>=R.entry(M,1,j1) and (not R.adm(M,j0))

def test_host(M, st):
    j1=R.Lng(M)-1
    if not (1<j1): return
    if not R.hasParent(M,1,j1): return
    isIII=condIII(M); isIV=condIV(M)
    if not (isIII or isIV): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2); d=jm2-jm3
    N=R.seg(M,jm3,j1)
    try: RN=R.Red(N)
    except Exception: return
    st['hosts']+=1
    reg='III' if isIII else 'IV'
    # trunk-diagonal probe (for ALL hosts)
    tr=R.TrMax(RN)
    tdiag=all(R.entry(RN,0,j)==R.entry(RN,1,j) for j in range(0,tr+1))
    if not tdiag:
        st['tdiag_fail']+=1
        if len(st['tdiag_ex'])<6: st['tdiag_ex'].append((R.fmt(M),R.fmt(RN),tr))
    else: st['tdiag_ok']+=1
    # dd and offset alignment
    dd=R.entry(M,0,jm3)-R.entry(M,1,jm3)
    if d>0:  # REGS
        st['regs_total']+=1
        b=R.Br(RN)
        if len(b)==0:
            st['regs_Bremp']+=1
            if len(st['regs_Bremp_ex'])<6: st['regs_Bremp_ex'].append((R.fmt(M),reg,d))
            return
        last=len(b)-1; jl=R.Joints(RN)[last]; fn=R.FirstNodes(RN)[last]
        g=jm3+fn  # M-node of last-branch first node
        # KEY probes
        k_jm2ltg = (jm2<g)
        k_le0 = R.le0(M,jm2,g)
        pg = R.parent(M,0,g)
        k_jm2le = (pg is not None and jm2<=pg)
        if not k_jm2ltg: st['k_jm2ltg_fail']+=1
        if not k_le0: st['k_le0_fail']+=1
        if not k_jm2le:
            st['k_jm2le_fail']+=1
            if len(st['k_jm2le_ex'])<6: st['k_jm2le_ex'].append((R.fmt(M),jm2,g,pg,reg))
        # joint offset check: jl == pg - jm3 ?
        if pg is not None and jl != pg-jm3:
            st['jl_offset_fail']+=1
            if len(st['jl_ex'])<6: st['jl_ex'].append((R.fmt(M),jl,pg-jm3,reg))
        diag = (R.entry(RN,0,fn)==R.entry(RN,1,fn))
        if d<jl: st['d_lt']+=1
        elif d==jl and diag: st['d_eq_diag']+=1
        elif d==jl and not diag:
            st['d_eq_nodiag']+=1
            if len(st['deqnd_ex'])<6: st['deqnd_ex'].append((R.fmt(M),d,reg))
        else:
            st['d_gt']+=1
            if len(st['dgt_ex'])<6: st['dgt_ex'].append((R.fmt(M),d,jl,reg))
    if d==0:  # M0RUN
        st['m0_total']+=1
        e=R.entry(M,1,jm2)
        if jm2+1<R.Lng(M):
            en=R.entry(M,1,jm2+1)
            if e<en: st['m0_ok']+=1
            else:
                st['m0_fail']+=1
                if len(st['m0_ex'])<6: st['m0_ex'].append((R.fmt(M),jm2,e,en,reg))
    # REGSP on RN' = Red(seg M jm3 (j1-1))
    if j1-1>jm3:
        try: RNp=R.Red(R.seg(M,jm3,j1-1))
        except Exception: RNp=None
        if RNp is not None and len(R.Br(RNp))>0:
            st['regsp_total']+=1
            b=R.Br(RNp); last=len(b)-1; jl=R.Joints(RNp)[last]; fn=R.FirstNodes(RNp)[last]
            diag=(R.entry(RNp,0,fn)==R.entry(RNp,1,fn))
            if d<jl: st['rp_lt']+=1
            elif d==jl and diag: st['rp_eq_diag']+=1
            elif d==jl and not diag:
                st['rp_eq_nodiag']+=1
                if len(st['rp_ex'])<6: st['rp_ex'].append((R.fmt(M),d,'ND'))
            else:
                st['rp_gt']+=1
                if len(st['rp_ex'])<6: st['rp_ex'].append((R.fmt(M),d,jl,'GT'))

def oper_orbit(cap, maxlen):
    seen=set(); frontier=[]
    for u in range(0,3):
        for v in range(u,u+4):
            d=tuple(R.diagSeq(u,v)); seen.add(d); frontier.append(list(d))
    out=[]
    while frontier and len(out)<cap:
        M=frontier.pop(0); out.append(M)
        if R.Lng(M)>=maxlen: continue
        for n in range(1,4):
            try: Mn=R.oper(M,n)
            except Exception: continue
            t=tuple(Mn)
            if t not in seen and R.Lng(Mn)<=maxlen:
                seen.add(t); frontier.append(Mn)
    return out

def main():
    st={k:0 for k in ['hosts','tdiag_ok','tdiag_fail','regs_total','regs_Bremp',
        'k_jm2ltg_fail','k_le0_fail','k_jm2le_fail','jl_offset_fail',
        'd_lt','d_eq_diag','d_eq_nodiag','d_gt','m0_total','m0_ok','m0_fail',
        'regsp_total','rp_lt','rp_eq_diag','rp_eq_nodiag','rp_gt']}
    for k in ['tdiag_ex','regs_Bremp_ex','k_jm2le_ex','jl_ex','deqnd_ex','dgt_ex','m0_ex','rp_ex']:
        st[k]=[]
    print("building orbit...", flush=True)
    orbit=oper_orbit(5000, 12)
    print("orbit size", len(orbit), flush=True)
    std=0
    for M in orbit:
        try:
            if R.is_standard(M): std+=1; test_host(M,st)
        except Exception: pass
    print("standard hosts tested:", std, flush=True)
    print("\n--- RESULTS (oper-orbit) ---")
    print("genuine III/IV hosts:", st['hosts'])
    print("trunk-diagonal: ok",st['tdiag_ok'],"FAIL",st['tdiag_fail'])
    if st['tdiag_ex']: print("  tdiag FAIL ex:", st['tdiag_ex'])
    print("REGS(d>0): total",st['regs_total'],"Br=[]",st['regs_Bremp'])
    print("  MCOND-RN: d<jl",st['d_lt'],"d=jl&diag",st['d_eq_diag'],
          "d=jl&NODIAG",st['d_eq_nodiag'],"d>jl",st['d_gt'])
    print("  KEY fails: jm2<g",st['k_jm2ltg_fail'],"le0(jm2,g)",st['k_le0_fail'],
          "jm2<=pg",st['k_jm2le_fail'],"jl!=pg-jm3",st['jl_offset_fail'])
    if st['k_jm2le_ex']: print("  jm2<=pg FAIL ex:", st['k_jm2le_ex'])
    if st['jl_ex']: print("  jl offset ex:", st['jl_ex'])
    if st['deqnd_ex']: print("  d=jl NODIAG ex:", st['deqnd_ex'])
    if st['dgt_ex']: print("  d>jl ex:", st['dgt_ex'])
    print("REGSP(Br<>[]): total",st['regsp_total'],"d<jl",st['rp_lt'],
          "d=jl&diag",st['rp_eq_diag'],"d=jl&NODIAG",st['rp_eq_nodiag'],"d>jl",st['rp_gt'])
    if st['rp_ex']: print("  REGSP ex:", st['rp_ex'])
    print("M0RUN(d=0): total",st['m0_total'],"ok",st['m0_ok'],"FAIL",st['m0_fail'])
    if st['m0_ex']: print("  M0RUN FAIL ex:", st['m0_ex'])

if __name__=='__main__': main()
