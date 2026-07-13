import sys,itertools
sys.setrecursionlimit(10000); sys.path.insert(0,'.')
from red_model import *
def mk(M,m): return adm(M,m) and le0(M,m,Lng(M)-1)
def sweep(E,L):
  pairs=[(a,b) for a in range(E) for b in range(E)]
  c={'le0f':0,'le0f_bad':0,'C4':0,'C4bad':0,'C5':0,'C5bad':0}
  for Ln in range(1,L+1):
    for M in itertools.product(pairs,repeat=Ln):
      M=list(M); R=Red(Red(M)); n=Lng(M)
      if Lng(R)!=n: print("LENBAD"); continue
      for a in range(n):
        for b in range(n):
          if le0(M,a,b):
            c['le0f']+=1
            if not le0(R,a,b): c['le0f_bad']+=1
      for m in range(n):
        if not mk(M,m): continue
        c['C5']+=1
        if not adm(R,m): c['C5bad']+=1
        if any(j<m and le0(M,j,m) for j in range(m)):
          c['C4']+=1
          if not adm(R,m): c['C4bad']+=1
  print(f"entries<{E} Lng<={L}:",c)
sweep(4,4); sweep(3,5)
