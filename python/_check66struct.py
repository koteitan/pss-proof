import itertools
from red_model import Red, fmt, Lng, entry

def row0ge(M):
    return all(entry(M,0,j)>=entry(M,1,j) for j in range(Lng(M)))

def enum(maxlen,maxe):
    cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
    for L in range(1,maxlen+1):
        for M in itertools.product(cols,repeat=L): yield list(M)

# STRUCTURAL: every Red M output has row0>=row1 everywhere (M in T_PS = nonempty)
struct_pass=0; struct_fail=0; total=0
# REDUCED: M with Red M = M  => row0>=row1
red_pass=0; red_fail=0; red_count=0
for M in enum(4,3):
    total+=1
    try: R=Red(M)
    except Exception: continue
    if row0ge(R): struct_pass+=1
    else:
        struct_fail+=1
        if struct_fail<=5: print("STRUCT FAIL: M=",fmt(M)," Red=",fmt(R))
    if R==M:
        red_count+=1
        if row0ge(M): red_pass+=1
        else:
            red_fail+=1
            if red_fail<=5: print("REDUCED FAIL:",fmt(M))
print("=== structural: Red M has row0>=row1 ===")
print("total M tried:",total,"struct pass:",struct_pass,"struct fail:",struct_fail)
print("=== reduced (Red M = M): row0>=row1 ===")
print("reduced witnesses:",red_count,"pass:",red_pass,"fail:",red_fail)
