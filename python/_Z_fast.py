from red_model import entry, Lng

# Fast per-sequence le0 / reach caches.
def le0_matrix(M):
    n=Lng(M)
    # nextrel0 edges
    R=[[i==j for j in range(n)] for i in range(n)]
    e0=entry
    edges=[]
    for a in range(n):
        ea=M[a][0]
        for b in range(a+1,n):
            if M[b][0]>ea and all(M[j][0]>=M[b][0] for j in range(a+1,b)):
                edges.append((a,b)); R[a][b]=True
    # transitive closure (Floyd-ish on edges)
    changed=True
    while changed:
        changed=False
        for a in range(n):
            Ra=R[a]
            for (c,d) in edges:
                if Ra[c] and not Ra[d]:
                    Ra[d]=True; changed=True
    return R

def parent1(M, le0M, j1):
    # row-1 parent: unique j0 with nextrel1
    n=Lng(M)
    cands=[]
    for j0 in range(j1):
        if M[j0][1] < M[j1][1] and le0M[j0][j1]:
            # maximality: all j in (j0,n) with le0 j j1 have entry1 j >= entry1 j1
            if all(M[j][1] >= M[j1][1] for j in range(j0+1,n) if le0M[j][j1]):
                cands.append(j0)
    if len(cands)==1: return cands[0]
    return None  # no unique parent

def idx1_(M,j1): return 1 if M[j1][1]>0 else 0
