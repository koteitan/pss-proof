import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

/-!
# PSS.Buchholz — §7.1 Buchholz の順序数表記系

移植元: `isabelle/pss_paper.thy` §7.1、および外部文献 [Buc1] §2–§3。

項、辞書式順序、`Gᵤ`、`OT_B`、基本列 `operB` と `domB` を実行可能な形で定義する。
`domB` の値は常に `∅`, `{0}`, `ℕ`, `Tᵤ` のいずれかなので、基本列の内部では有限タグ
`BDom` を使い、公開定義 `domB` で元の集合へ戻す。基本列 ([].4)(ii) は訂正 A23 後の
`x₀ = Dᵤ0`, `xᵢ₊₁ = Dᵤ(b[xᵢ])`, `(Dᵥb)[n] = Dᵥ(b[xₙ])` を採用する。
-/

namespace PSS

/-! ## 項と順序 -/

/- Buchholz 項と principal 項。`Trm []` が `0`、`Trm [DB v b]` が `D_v b`。 -/
mutual
  inductive BT where
    | trm : List BP → BT
  inductive BP where
    | db : ℕ∞ → BT → BP
end

deriving instance BEq for BT, BP

/-- Buchholz の零項。 -/
def BZero : BT := .trm []

/-- principal 項 `D_v a` を通常の項として包む。 -/
def Dprin (v : ℕ∞) (a : BT) : BT := .trm [.db v a]

/- principal リストの辞書式順序と principal 項の順序。 -/
mutual
  def lessBT : BT → BT → Bool
    | .trm as, .trm bs => lessBPList as bs
  def lessBP : BP → BP → Bool
    | .db u a, .db v b => decide (u < v) || (u == v && lessBT a b)
  def lessBPList : List BP → List BP → Bool
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | a :: as, b :: bs => lessBP a b || (a == b && lessBPList as bs)
end

/-- Buchholz 項の広義順序。 -/
def leBT (a b : BT) : Bool := lessBT a b || a == b

/-! ## `Gᵤ`, 加法、項クラス -/

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

/-! ## 基本列 -/

/- 再帰の第 1 測度。項・principal・リストの真部分へ進むたび減少する。 -/
mutual
  def btWeight : BT → ℕ
    | .trm ps => bpListWeight ps + 1
  def bpWeight : BP → ℕ
    | .db _ b => btWeight b + 1
  def bpListWeight : List BP → ℕ
    | [] => 0
    | p :: ps => bpWeight p + bpListWeight ps + 1
end

private inductive BOperState where
  | term (a z : BT)
  | princ (p : BP) (z : BT)
  | list (ps : List BP) (z : BT)
  | xseq (b : BT) (u : ℕ∞) (i : ℕ)

private def bOperMeasure : BOperState → ℕ × ℕ × ℕ
  | .term a _ => (btWeight a, 0, 0)
  | .princ p _ => (bpWeight p, 0, 0)
  | .list ps _ => (bpListWeight ps, 0, 0)
  | .xseq b _ i => (btWeight b, 1, i)

/- `operB` と `xseq` の共通再帰本体。

`xseq b u (i+1)` から同じ `b` の `operB` へ移るときは測度の第 2 成分が `1 → 0`、
反復自身では第 3 成分 `i` が減る。`operB` からの全呼出しは真部分項へ進む。 -/
set_option linter.unnecessarySeqFocus false in
private def bOperCore (s : BOperState) : BT :=
  match s with
  | .term (.trm ps) z => bOperCore (.list ps z)
  | .list [] _ => BZero
  | .list [p] z => bOperCore (.princ p z)
  | .list (p :: q :: ps) z =>
      addBT (.trm [p]) (bOperCore (.list (q :: ps) z))
  | .princ (.db v b) z =>
      if b == BZero then
        if v == 0 then BZero
        else if v == ⊤ then Dprin ((numNat z + 1 : ℕ) : ℕ∞) BZero
        else z
      else
        match domTag b with
        | .zeroOnly =>
            multBT (Dprin v (bOperCore (.term b BZero))) (numNat z + 1)
        | .below u =>
            if decide (v ≤ (u : ℕ∞)) then
              Dprin v (bOperCore (.term b (bOperCore (.xseq b (u : ℕ∞) (numNat z)))))
            else
              Dprin v (bOperCore (.term b z))
        | _ => Dprin v (bOperCore (.term b z))
  | .xseq _ u 0 => Dprin u BZero
  | .xseq b u (i + 1) =>
      Dprin u (bOperCore (.term b (bOperCore (.xseq b u i))))
  termination_by bOperMeasure s
  decreasing_by
    all_goals simp [bOperMeasure, btWeight, bpWeight, bpListWeight]
    all_goals first
      | apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.right <;> omega

/-- Buchholz の基本列 `a[z]`。 -/
def operB (a z : BT) : BT := bOperCore (.term a z)

/-- 訂正 A23 後の補助列 `x_i`。 -/
def xseq (b : BT) (u : ℕ∞) (i : ℕ) : BT := bOperCore (.xseq b u i)

/-! ## principal 成分分解 -/

/-- `Trm` の principal リストを取り出す。 -/
def untrm : BT → List BP
  | .trm ps => ps

/-- 項を principal 項のリストへ分解する。 -/
def PB (t : BT) : List BT := (untrm t).map (fun p => .trm [p])

/-- principal 成分リストを再合成する。 -/
def SigmaB (ts : List BT) : BT := .trm (ts.flatMap untrm)

/-! 基本例と A23 分岐を壊さないための回帰テスト。 -/

#guard lessBT BZero (Dprin 0 BZero)
#guard domTag BZero == .empty
#guard domTag (Dprin 0 BZero) == .zeroOnly
#guard domTag (Dprin ⊤ BZero) == .naturals
#guard operB (Dprin 0 BZero) BZero == BZero
#guard operB (Dprin ⊤ BZero) (numBT 3) == Dprin (4 : ℕ∞) BZero

end PSS
