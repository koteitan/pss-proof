from fast_pss import Lng, entry, le0, nextrel1, reduced, enum_reduced_tiling

def nadm(M, j):
    n = Lng(M)
    if j > n: return True   # j > Lng M
    # nextR M 1 (j-1) j and nextR M 1 j (j+1)
    if j-1 < 0: return False
    return nextrel1(M, j-1, j) and nextrel1(M, j, j+1)

def adm(M, j):
    return not nadm(M, j)

def nextAdm0(M, j0, j1):
    if not (le0(M, j0, j1) and j0 < j1 and adm(M, j0)): return False
    return all((not le0(M, j, j1)) or (not adm(M, j)) for j in range(j0+1, j1))

cnt=0; uniq=0; viol=[]
for M in enum_reduced_tiling(maxlen=5, maxe=3):
    n = Lng(M)
    if n < 2: continue
    cnt += 1
    j1 = n-1
    parents = [j0 for j0 in range(j1) if nextAdm0(M, j0, j1)]
    if len(parents) != 1: continue
    uniq += 1
    j0 = parents[0]
    # ancestors j with le0(M, j, j0)
    for j in range(j0+1):
        if le0(M, j, j0) and not adm(M, j):
            viol.append((M, j0, j))
            break
print(f"reduced(len>=2)={cnt}, unique-nextAdm-parent={uniq}, adm-violations={len(viol)}")
for v in viol[:8]:
    print("  CEX M=",v[0]," j0=",v[1]," nonadm-ancestor j=",v[2])
