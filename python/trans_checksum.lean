import PSS.Trans

/-!
`python/trans_model.py` と Lean の `PSS.Trans` の忠実性監査。

成分 `< 3`、長さ `1..3` の全 819 ペア数列について `Trans`、全添字の `Mark`、
条件 (I)–(VI) を共通ハッシュへ畳み込む。期待値は `trans_checksum.py` で計算する。
-/

open PSS

def transPairsUpto (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun a => (List.range k).map fun b => (a, b)

def transSeqsOfLen (k : ℕ) : ℕ → List PS
  | 0 => [[]]
  | n + 1 => (transSeqsOfLen k n).flatMap fun M =>
      (transPairsUpto k).map fun p => M ++ [p]

def transAllSeqs (k maxL : ℕ) : List PS :=
  (List.range maxL).flatMap fun n => transSeqsOfLen k (n + 1)

def transModulus : ℕ := 1000000007
def transMix (a b : ℕ) : ℕ := (a * 31 + b) % transModulus

def transHashSym : Sym → ℕ
  | .zero => 1
  | .lp => 2
  | .cm => 3
  | .rp => 4
  | .dsym v => v.toNat + 100

def transHashTerm (t : BT) : ℕ :=
  (flatBT t).foldl (fun a x => transMix a (transHashSym x)) 1

def transChecksum (k maxL : ℕ) : ℕ :=
  (transAllSeqs k maxL).foldl (fun acc M =>
    let acc := transMix acc (transHashTerm (Trans M))
    let acc := (List.range (Lng M)).foldl
      (fun a m => transMix a (transHashTerm (Mark M m))) acc
    [transCondI M, transCondII M, transCondIII M,
      transCondIV M, transCondV M, transCondVI M].foldl
      (fun a c => transMix a (if c then 1 else 0)) acc) 0

#eval (transAllSeqs 3 3).length
#eval transChecksum 3 3
