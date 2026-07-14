import PSS.Buchholz

/-!
`python/buchholz.py` と Lean の `PSS.Buchholz` の忠実性監査。

有限指標 `0,1,2`、深さ 2、各項の最上位 principal 数 2 以下の全 1,561 項について、
`dfree`, `OT`, `G`, `dom`, `operB` と全項対の `<` を共通ハッシュへ畳み込む。
2026-07-15 検証値は定義群 `177483501`、順序 `877667618`（Python/Lean 一致）。
-/

open PSS

def bpSeqsOfLen (ps : List BP) : ℕ → List (List BP)
  | 0 => [[]]
  | n + 1 => (bpSeqsOfLen ps n).flatMap (fun xs => ps.map (fun p => xs ++ [p]))

def genBTerms : ℕ → List ℕ∞ → ℕ → List BT
  | 0, _, _ => [BZero]
  | depth + 1, idxs, maxComponents =>
      let sub := genBTerms depth idxs maxComponents
      let principals := idxs.flatMap (fun v => sub.map (fun b => BP.db v b))
      BZero :: (List.range maxComponents).flatMap (fun k =>
        (bpSeqsOfLen principals (k + 1)).map BT.trm)

def modulus : ℕ := 1000000007

def mix (acc x : ℕ) : ℕ := (acc * 31 + x) % modulus

def hashIndex (v : ℕ∞) : ℕ := if v == ⊤ then 100000 else v.toNat + 1

mutual
  def hashBT : BT → ℕ
    | .trm ps => (hashBPList ps * 37 + ps.length) % modulus
  def hashBP : BP → ℕ
    | .db v b => (hashIndex v * 1009 + hashBT b * 9176 + 7) % modulus
  def hashBPList : List BP → ℕ
    | [] => 1
    | p :: ps => (hashBP p * 1000003 + hashBPList ps + 7) % modulus
end

def hashBTList (ts : List BT) : ℕ := ts.foldl (fun acc t => mix acc (hashBT t)) 0

def hashDom : BDom → ℕ
  | .empty => 1
  | .zeroOnly => 2
  | .naturals => 3
  | .below u => u + 4

def termFingerprint (t : BT) : ℕ :=
  let acc := mix 0 (hashBT t)
  let acc := mix acc (if dfree_BT t then 1 else 0)
  let acc := mix acc (if isOT_BT t then 1 else 0)
  let acc := mix acc (hashBTList (gatherBT 0 t))
  let acc := mix acc (hashDom (domTag t))
  (List.range 4).foldl (fun a n => mix a (hashBT (operB t (numBT n)))) acc

def termChecksum (ts : List BT) : ℕ :=
  ts.foldl (fun acc t => mix acc (termFingerprint t)) 0

def orderChecksum (ts : List BT) : ℕ :=
  ts.foldl (fun acc a =>
    ts.foldl (fun acc b => mix acc (if lessBT a b then 1 else 0)) acc) 0

def auditTerms : List BT := genBTerms 2 [0, 1, 2] 2

#eval auditTerms.length
#eval termChecksum auditTerms
#eval orderChecksum auditTerms
