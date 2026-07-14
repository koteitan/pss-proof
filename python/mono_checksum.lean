import PSS.Mono
import PSS.Adm
open PSS

def pairsUpto (k : Nat) : List (Nat × Nat) :=
  (List.range k).flatMap (fun a => (List.range k).map (fun b => (a, b)))

def seqsOfLen (k : Nat) : Nat → List PS
  | 0 => [[]]
  | n + 1 => (seqsOfLen k n).flatMap (fun M => (pairsUpto k).map (fun p => M ++ [p]))

def allSeqs (k maxL : Nat) : List PS :=
  (List.range maxL).flatMap (fun L => seqsOfLen k (L + 1))

def hashPS (M : PS) : Nat :=
  M.foldl (fun h p => (h * 1000003 + p.1 * 1009 + p.2 + 7) % 1000000007) 1

def hashNats (l : List Nat) : Nat :=
  l.foldl (fun h x => (h * 1000003 + x + 7) % 1000000007) 1

def mix (acc x : Nat) : Nat := (acc * 31 + x) % 1000000007

def ck (f : PS → Nat) (k maxL : Nat) : Nat := ((allSeqs k maxL).map f).foldl mix 0

#eval ck (fun M => if monoT M then 1 else 0) 4 4
#eval ck (fun M => if multiT M then 1 else 0) 4 4
#eval ck (fun M => hashNats ((P M).map hashPS)) 4 4
#eval ck (fun M => TrMax M) 4 4
#eval ck (fun M => hashNats ((Br M).map hashPS)) 4 4
#eval ck (fun M => hashNats (FirstNodes M)) 4 4
#eval ck (fun M => hashNats (Joints M)) 4 4
#eval ck (fun M => hashNats ((List.range (Lng M + 2)).map (fun j => if adm M j then 1 else 0))) 4 4
#eval ck (fun M => hashNats ((List.range (Lng M + 2)).map (fun j => Adm M j))) 4 4
