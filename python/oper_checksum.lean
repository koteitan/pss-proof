import PSS.Defs
open PSS

def pairsUpto (k : Nat) : List (Nat × Nat) :=
  (List.range k).flatMap (fun a => (List.range k).map (fun b => (a, b)))

def seqsOfLen (k : Nat) : Nat → List PS
  | 0 => [[]]
  | n + 1 => (seqsOfLen k n).flatMap (fun M => (pairsUpto k).map (fun p => M ++ [p]))

def allSeqs (k maxL : Nat) : List PS :=
  (List.range maxL).flatMap (fun L => seqsOfLen k (L + 1))

/-- 列の多項式ハッシュ（python 側と同じ式）。 -/
def hashPS (M : PS) : Nat :=
  M.foldl (fun h p => (h * 1000003 + p.1 * 1009 + p.2 + 7) % 1000000007) 1

def checksum (k maxL nMax : Nat) : Nat :=
  ((allSeqs k maxL).flatMap (fun M =>
      (List.range nMax).map (fun n => hashPS (oper M n)))).foldl
    (fun acc h => (acc * 31 + h) % 1000000007) 0

#eval (allSeqs 4 4).length
#eval checksum 4 4 4
