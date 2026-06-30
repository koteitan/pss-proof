import sys, os, itertools, functools, subprocess
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,monoT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,reduced
import red_model as rm
from trans_model import Trans,Mark,ZB,PB,bpHeadT,reduced as treduced,condV
import trans_model as tm

BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"

def transJm1(M): return tm.Adm(M, parent(M,0,Lng(M)-1))

def gen(maxlen=4,maxv=2):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(3,maxlen+1):
        for s in itertools.product(pairs,repeat=L):
            M=list(s)
            if M[0]!=(0,0): continue
            yield M

total_cols = 0
anchor_true = 0
nest_conds_true = 0
nest_but_not_anchor = []
anchor_fail_examples = []
monotone_fail = []

cnt = 0
TARGET_COLS = 400
import time
t0=time.time()
for M in gen(4,2):
    if total_cols >= TARGET_COLS: break
    if time.time()-t0 > 480: print("TIME BUDGET HIT", flush=True); break
    try:
        if not (reduced(M) and is_std(tuple(M))): continue
    except Exception:
        continue
    cnt += 1
    for q in (2,3):
        if total_cols >= TARGET_COLS: break
        try:
            Mq=oper(M,q); Msq=oper(M,q+1)
            if Lng(Msq)>14: continue
            if Msq[:len(Mq)]!=Mq: continue
            jm=transJm1(Mq); Lq=Lng(Mq)
            if not (0<jm<Lq-1): continue
            n0 = jm
            Bcols = Msq[len(Mq):]
            w = len(Bcols)
            if not Bcols: continue
            hosts = [Mq + Bcols[:m] for m in range(w+1)]
            for m in range(w):
                if total_cols >= TARGET_COLS: break
                hostm = hosts[m]; hostm1 = hosts[m+1]
                if not (reduced(hostm) and reduced(hostm1)): continue
                if Lng(hostm1) < 2: continue
                try:
                    jmid = transJm1(hostm1)
                except Exception:
                    continue
                total_cols += 1
                try:
                    c_n0 = marked(hostm, n0)
                    c_jm = marked(hostm, jmid)
                    c_le = (n0 <= jmid)
                except Exception:
                    c_n0=c_jm=c_le=False
                conds = c_n0 and c_jm and c_le and reduced(hostm)
                if conds: nest_conds_true += 1
                if not c_le and len(monotone_fail) < 8:
                    monotone_fail.append((rm.fmt(M), q, m, n0, jmid))
                try:
                    acc = Mark(hostm, n0)
                    c1m = Mark(hostm, jmid)
                    ds = tm.scb_decomps(acc, tm.flatBT(c1m))
                    anchor_ok = len(ds) > 0
                except Exception:
                    anchor_ok = False
                if anchor_ok: anchor_true += 1
                else:
                    if len(anchor_fail_examples) < 10:
                        anchor_fail_examples.append((rm.fmt(M), q, m, c_n0, c_jm, c_le, reduced(hostm)))
                if conds and not anchor_ok:
                    nest_but_not_anchor.append((rm.fmt(M), q, m))
                if total_cols % 50 == 0:
                    print(f"...progress total_cols={total_cols} anchor_true={anchor_true} nest_conds_true={nest_conds_true}", flush=True)
        except Exception:
            continue

print(f"std&reduced bases scanned={cnt}")
print(f"total per-column anchor checks = {total_cols}")
print(f"anchor TRUE = {anchor_true}/{total_cols}")
print(f"nest reduction conditions TRUE = {nest_conds_true}/{total_cols}")
print(f"monotonicity (n0<=j_m) FAILS = {len(monotone_fail)} (showing up to 8)")
for ex in monotone_fail: print("   MONO-FAIL:", ex)
print(f"\ncases nest-conds true but anchor FALSE (would refute the reduction) = {len(nest_but_not_anchor)}")
for ex in nest_but_not_anchor[:8]: print("   NEST-BUT-NOT-ANCHOR:", ex)
print("\nanchor FAIL examples (M,q,m,marked(host,n0),marked(host,jmid),n0<=jmid,reduced(host)):")
for ex in anchor_fail_examples: print("  ", ex)
