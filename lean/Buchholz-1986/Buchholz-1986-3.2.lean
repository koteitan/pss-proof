import «Buchholz-1986».«Buchholz-1986-2.2»

/-!
# Buchholz (1986) §3.2 — 加法と基本列の定義域

出典: W. Buchholz, “A new system of proof-theoretic ordinal functions”,
Annals of Pure and Applied Logic 32 (1986), §3, Lemma 3.2 の直前に置かれた
加法、`Tᵥ`、基本列の定義域 `dom(a)` の定義。

移植元: `isabelle/pss_paper.thy` §7.1、および外部文献 [Buc1] §3。

`domB` の値は常に `∅`, `{0}`, `ℕ`, `Tᵤ` のいずれかなので有限タグ
`BDom` で計算し、公開定義 `domB` で元の集合へ戻す。
([].4)(ii) の [Buc2] 差し替えを含む基本列本体は
`Buchholz-rel-ord/Buchholz-rel-ord-6.lean` に置く。
-/

namespace PSS

/-! ## 加法と `Tᵥ` -/

/-- Buchholz 項の加法（principal リストの連結）。 -/
def addBT : BT → BT → BT
  | .trm as, .trm bs => .trm (as ++ bs)

/-- 自然数倍。 -/
def multBT (a : BT) : ℕ → BT
  | 0 => BZero
  | n + 1 => addBT (multBT a n) a

/-- `T_v`: 最上位の全 principal 指標が `v` 以下の項。 -/
def TBv (v : ℕ∞) : Set BT :=
  {t | match t with
       | .trm ps => ps.all (fun p => match p with | .db u _ => decide (u ≤ v)) = true}

/-! ## 数項と `dom` -/

/-- 自然数 `n` を `n` 個の `D_0 0` の和として表す。 -/
def numBT (n : ℕ) : BT := .trm (List.replicate n (.db 0 BZero))

/-- 項の最上位 principal 個数。自然数項上では `numBT` の逆。 -/
def numNat : BT → ℕ
  | .trm ps => ps.length

/-- Buchholz 自然数項全体。 -/
def NatSet : Set BT := Set.range numBT

/-- `dom` が取り得る四種類の値。 -/
inductive BDom where
  | empty
  | zeroOnly
  | naturals
  | below (u : ℕ)
  deriving BEq, DecidableEq, Repr

/-- `BDom` を [Buc1] の実際の添字集合へ戻す。 -/
def BDom.toSet : BDom → Set BT
  | .empty => ∅
  | .zeroOnly => {BZero}
  | .naturals => NatSet
  | .below u => TBv (u : ℕ∞)

/- `dom` のタグ版。multi 項では末尾 principal の `dom` を返す。 -/
mutual
  def domTag : BT → BDom
    | .trm ps => domTagList ps
  def domTagBP : BP → BDom
    | .db v b =>
        if b == BZero then
          if v == 0 then .zeroOnly
          else if v == ⊤ then .naturals
          else .below (v.toNat - 1)
        else
          match domTag b with
          | .zeroOnly => .naturals
          | .below u => if decide (v ≤ (u : ℕ∞)) then .naturals else .below u
          | d => d
  def domTagList : List BP → BDom
    | [] => .empty
    | [p] => domTagBP p
    | _ :: ps => domTagList ps
end

/-- [Buc1] の `dom(a)`。 -/
def domB (a : BT) : Set BT := (domTag a).toSet

/-- `D = T_u` のときの `u`。該当しない集合では既定値 `0`。 -/
noncomputable def tbvIdx (D : Set BT) : ℕ := by
  classical
  exact if h : ∃ u : ℕ, D = TBv (u : ℕ∞) then Classical.choose h else 0

end PSS
