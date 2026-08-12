import «Buchholz-1986».«Buchholz-1986-2.1»

/-!
# Buchholz (1986) §2.2 — 係数集合と順序数項

出典: W. Buchholz, “A new system of proof-theoretic ordinal functions”,
Annals of Pure and Applied Logic 32 (1986), §2, Lemma 2.2 の前提となる
`Gᵤ` および `OT` の帰納的定義。

旧配置 `PSS/Buchholz.lean` の `Gᵤ`、`T_B`、`OT_B` を収録する。
-/

namespace PSS

/-! ## `Gᵤ` と項クラス -/

/- `G_u` の有限リスト表現（重複は意味に影響しない）。 -/
mutual
  def gatherBT : ℕ∞ → BT → List BT
    | u, .trm ps => gatherBPList u ps
  def gatherBP : ℕ∞ → BP → List BT
    | u, .db v b => if decide (u ≤ v) then b :: gatherBT u b else []
  def gatherBPList : ℕ∞ → List BP → List BT
    | _, [] => []
    | u, p :: ps => gatherBP u p ++ gatherBPList u ps
end

/-- [Buc1] の集合 `G_u a`。 -/
def GBT (u : ℕ∞) (a : BT) : Set BT := {x | (gatherBT u a).contains x = true}

/-- principal 項版の `G_u`。 -/
def GBP (u : ℕ∞) (p : BP) : Set BT := {x | (gatherBP u p).contains x = true}

/- `D_ω` をどの深さにも含まないことの判定。 -/
mutual
  def dfree_BT : BT → Bool
    | .trm ps => dfree_BPList ps
  def dfree_BP : BP → Bool
    | .db v b => v != ⊤ && dfree_BT b
  def dfree_BPList : List BP → Bool
    | [] => true
    | p :: ps => dfree_BP p && dfree_BPList ps
end

/-- `T_B`: `D_ω`-free な Buchholz 項。 -/
def T_B : Set BT := {t | dfree_BT t = true}

/-! ## `OT_B` -/

/-- principal リストが広義降順であること。 -/
def descP : List BP → Bool
  | [] => true
  | [_] => true
  | p :: q :: ps => leBT (.trm [q]) (.trm [p]) && descP (q :: ps)

/- [Buc1] (OT1)–(OT3) の構造的判定。 -/
mutual
  def isOT_BT : BT → Bool
    | .trm ps => isOT_BPList ps && descP ps
  def isOT_BP : BP → Bool
    | .db v b => isOT_BT b && (gatherBT v b).all (fun x => lessBT x b)
  def isOT_BPList : List BP → Bool
    | [] => true
    | p :: ps => isOT_BP p && isOT_BPList ps
end

/-- 全 Buchholz 順序数項。 -/
def OT : Set BT := {t | isOT_BT t = true}

/-- `OT_B = OT ∩ T_B`。 -/
def OT_B : Set BT := OT ∩ T_B

end PSS
