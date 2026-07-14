import PSS.Red

/-!
`python/red_model.py` と Lean の `PSS.Red` の忠実性監査。

成分 `< k`、長さ `1..maxL` の全ペア数列について `Red` の出力を同じ多項式ハッシュへ
畳み込む。`k = maxL = 4` では 69,904 列を検査し、Python/Lean ともに
チェックサム `505375848` となる（2026-07-15 検証済み）。
-/

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

def checksum (k maxL : Nat) : Nat :=
  ((allSeqs k maxL).map (fun M => hashPS (Red M))).foldl
    (fun acc h => (acc * 31 + h) % 1000000007) 0

#eval (allSeqs 4 4).length
#eval checksum 4 4
