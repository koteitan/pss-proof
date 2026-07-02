import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/python')
from buchholz import ZERO, D, bracket, fmt
def op0(a): return bracket(a, ZERO)
# verify: iterating [0] on D_u(D_w 0) reaches D_u 0 with 0<k<=w+1, exhaustively
bad=0
for u in range(8):
  for w in range(8):
    c=[D(u,[D(w,ZERO)])]
    target=[D(u,ZERO)]
    cur=c; found=None
    for k in range(1,w+2):
        cur=op0(cur)
        if cur==target: found=k; break
    if found is None or not (0<found<=w+1):
        bad+=1; print(f"BAD u={u} w={w} found={found}")
    # also verify per-step laws
    c=[D(u,[D(w,ZERO)])]
    if u<w:
        assert op0(c)==[D(u,[D(w-1,ZERO)])], f"kind1 fail u={u} w={w}: {fmt(op0(c))}"
    else:  # w<=u
        assert op0(c)==[D(u,ZERO)], f"base fail u={u} w={w}: {fmt(op0(c))}"
print("descent/base laws + iteration: all OK" if bad==0 else f"{bad} bad")
