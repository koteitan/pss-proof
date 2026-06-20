"""A20/A21 empirical: counterexamples to p_8_1_condI_III_c1_around as transcribed."""
from trans_model import Trans, Mark, Adm
from red_model import Lng, entry, seg, Red, parent, Pred
import red_model as rm
def check():
    # A20 (part 1): singleton non-reduced slice -> Trans(slice) != c1
    M=[(0,0),(1,0),(2,0)]; j1=Lng(M)-1; j0=parent(M,0,j1); jm1=Adm(M,j0)
    sl=seg(M,j0,j1-1); c1=Mark(Pred(M),jm1)
    print("A20 part(1) M=",M,"condI(e1j1=%d)"%entry(M,1,j1),
          "Trans(seg j0..j1-1)=",Trans(sl),"c1=",c1,"equal?",Trans(sl)==c1)
    # A21 (part 5): condIII -> parent N != j0'
    M2=[(0,0),(1,1),(2,1)]; j1=Lng(M2)-1; j0=parent(M2,0,j1)
    Mn=rm.oper(M2,2); n=2; idx=j0+(n-1)*(j1-j0); N=seg(Mn,0,idx)
    print("A21 part(5) M=",M2,"condIII(e1j1=%d)"%entry(M2,1,j1),
          "parent N=",parent(N,0,Lng(N)-1),"claimed j0'=0")
if __name__=='__main__': check()
