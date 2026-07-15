import PSS.Adm
import PSS.Red
import PSS.Scb

/-!
# PSS.Trans — §7.3 翻訳写像

移植元: `isabelle/pss_paper.thy` §7.3（定義 `Trans` / `Mark`）。

`flatBT` の逆写像は、Isabelle の Hilbert choice (`THE`) を実行可能な構文解析器として
実装する。`Trans` と `Mark` は相互再帰を有限燃料で全域化し、原定義の各再帰呼出しで
燃料を一つ減らす。簡約形上で燃料が尽きないことは §7.3 の well-defined 性で示す。
原文 `LastStep` の添字欠落は訂正 A9 後の形を採用する。
-/

namespace PSS

/-! ## `flatBT` の逆写像 -/

mutual
  /-- 項の文字列を一つ読み、残りの文字列も返す。 -/
  def parseBTAux : ℕ → List Sym → Option (BT × List Sym)
    | 0, _ => none
    | _ + 1, [] => none
    | _ + 1, .zero :: xs => some (BZero, xs)
    | fuel + 1, .dsym u :: xs =>
        match parseBTAux fuel xs with
        | some (t, rest) => some (Dprin u t, rest)
        | none => none
    | fuel + 1, .lp :: xs => parseBPSeqAux fuel xs []
    | _ + 1, _ => none

  /-- principal 項の文字列を一つ読む。 -/
  def parseBPAux : ℕ → List Sym → Option (BP × List Sym)
    | 0, _ => none
    | fuel + 1, .dsym u :: xs =>
        match parseBTAux fuel xs with
        | some (t, rest) => some (.db u t, rest)
        | none => none
    | _ + 1, _ => none

  /-- 左括弧の後にある、コンマ区切りの principal 項列を読む。 -/
  def parseBPSeqAux : ℕ → List Sym → List BP → Option (BT × List Sym)
    | 0, _, _ => none
    | fuel + 1, xs, acc =>
        match parseBPAux fuel xs with
        | none => none
        | some (p, .rp :: rest) => some (.trm (acc ++ [p]), rest)
        | some (p, .cm :: rest) => parseBPSeqAux fuel rest (acc ++ [p])
        | some _ => none
end

/-- `flatBT` の実行可能な部分逆写像。像の外では既定値 `0` を返す。 -/
def unflatBT (xs : List Sym) : BT :=
  match parseBTAux (xs.length + 1) xs with
  | some (t, []) => t
  | _ => BZero

/-- principal 項文字列であることの実行可能な判定。 -/
def isPTBStr (xs : List Sym) : Bool :=
  match parseBPAux (xs.length + 1) xs with
  | some (p, []) => dfree_BP p
  | _ => false

/-! ## scb 文脈の実行可能な選択 -/

/-- 固定した中央文字列 `c` に対する全 scb 文脈 `(s,b)`（左から出現順）。 -/
def scbContexts (t : BT) (c : List Sym) : List (List Sym × List Sym) :=
  let f := flatBT t
  (List.range (f.length - c.length + 1)).filterMap fun i =>
    let s := f.take i
    let b := f.drop (i + c.length)
    if (f.drop i).take c.length == c &&
        (t == BZero || isPTBStr c) &&
        b.all (· == .rp) then
      some (s, b)
    else none

/-- `c₁` を `c₂` に置換した項。文脈は Isabelle の `SOME` と同じく最初の候補を選ぶ。 -/
def replaceScb (t c₁ c₂ : BT) : BT :=
  match (scbContexts t (flatBT c₁)).head? with
  | some (s, b) => unflatBT (s ++ flatBT c₂ ++ b)
  | none => BZero

/-! ## 条件 (I)–(VI) -/

/-- Index of the final column.  Public because proofs about the recursive
equations of `TransAux` and `MarkAux` need to normalize this guard. -/
def lastIdx (M : PS) : ℕ := Lng M - 1

/-- Row-zero parent of the final column. -/
def lastParent (M : PS) : ℕ := parent M 0 (lastIdx M)

/-- 条件 (I)。 -/
def transCondI (M : PS) : Bool :=
  entry M 1 (lastIdx M) == 0 && adm M (lastParent M)

/-- 条件 (II)。 -/
def transCondII (M : PS) : Bool :=
  entry M 1 (lastIdx M) == 0 && !adm M (lastParent M)

/-- 条件 (III)。 -/
def transCondIII (M : PS) : Bool :=
  0 < entry M 1 (lastIdx M) &&
    entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M) &&
    adm M (lastParent M)

/-- 条件 (IV)。 -/
def transCondIV (M : PS) : Bool :=
  0 < entry M 1 (lastIdx M) &&
    entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M) &&
    !adm M (lastParent M)

/-- 条件 (V)。 -/
def transCondV (M : PS) : Bool :=
  0 < entry M 1 (lastIdx M) &&
    entry M 1 (lastParent M) + 1 == entry M 1 (lastIdx M) &&
    lastParent M + 1 < lastIdx M

/-- 条件 (VI)。 -/
def transCondVI (M : PS) : Bool :=
  0 < entry M 1 (lastIdx M) &&
    entry M 1 (lastParent M) + 1 == entry M 1 (lastIdx M) &&
    lastParent M + 1 == lastIdx M

/-! ## `Trans` / `Mark` -/

/-- principal 項の先頭指標（零項では既定値 `0`）。 -/
def bpHeadV : BT → ℕ∞
  | .trm (.db v _ :: _) => v
  | _ => 0

/-- principal 項の先頭内部項（零項では既定値 `0`）。 -/
def bpHeadT : BT → BT
  | .trm (.db _ t :: _) => t
  | _ => BZero

/-- 原定義の `c₂`。 -/
def transC2Core (M : PS) (v : ℕ∞) (t₂ : BT) : BT :=
  let j₁ := lastIdx M
  let j' := lastParent M
  if transCondI M || transCondIII M || transCondV M then
    Dprin v (addBT t₂ (Dprin (entry M 1 j₁ : ℕ∞) BZero))
  else if transCondVI M then
    Dprin v (Dprin (entry M 1 j₁ : ℕ∞) BZero)
  else if t₂ == BZero then
    Dprin v (Dprin (entry M 1 j' : ℕ∞)
      (Dprin (entry M 1 j₁ : ℕ∞) BZero))
  else
    let pt₂ := PB t₂
    let J₁ := pt₂.length - 1
    let pJ := pt₂.getD J₁ BZero
    let leftDj₀ := bpHeadV pJ == (entry M 1 j' : ℕ∞)
    let t₃ := if leftDj₀ then SigmaB (pt₂.take J₁) else t₂
    let t₄ := if leftDj₀ then bpHeadT pJ else t₂
    Dprin v (addBT t₃ (Dprin (entry M 1 j' : ℕ∞)
      (addBT t₄ (Dprin (entry M 1 j₁ : ℕ∞) BZero))))

/-- 相互再帰の燃料。簡約形では長さに線形な再帰深さしか使わない。非簡約入力についても
`Red` の反復を十分に収容できるよう `ν` を含む保守的な上界を採る。 -/
def transFuel (M : PS) : ℕ := 8 * (nu M + 1) * (Lng M + 1) + 8

mutual
  /-- `Trans` の燃料付き本体。 -/
  def TransAux : ℕ → PS → BT
    | 0, _ => BZero
    | fuel + 1, M =>
        if !reduced M then
          TransAux fuel (Red M)
        else
          let j₁ := lastIdx M
          if j₁ == 0 then
            if M.getD 0 (0, 0) == (0, 0) then BZero
            else Dprin (entry M 1 0 : ℕ∞) BZero
          else if monoT M then
            let t₁ := TransAux fuel (Pred M)
            if t₁ == BZero then
              Dprin 0 (Dprin (entry M 1 j₁ : ℕ∞) BZero)
            else
              let j' := lastParent M
              let c₁ := MarkAux fuel (Pred M) (Adm M j')
              let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
              replaceScb t₁ c₁ c₂
          else
            let ps := P M
            let J₁ := ps.length - 1
            let pJ := ps.getD J₁ []
            let j₀ := j₁ - Lng pJ + 1
            if pJ == [(0, 0)] then
              addBT (TransAux fuel (seg M 0 (j₀ - 1))) (Dprin 0 BZero)
            else
              addBT (TransAux fuel (seg M 0 (j₀ - 1))) (TransAux fuel pJ)

  /-- `Mark` の燃料付き本体。 -/
  def MarkAux : ℕ → PS → ℕ → BT
    | 0, _, _ => BZero
    | fuel + 1, M, m =>
        if !reduced M then
          MarkAux fuel (Red M) m
        else
          let j₁ := lastIdx M
          if j₁ == 0 then
            if M.getD 0 (0, 0) == (0, 0) then BZero
            else Dprin (entry M 1 0 : ℕ∞) BZero
          else if monoT M then
            let t₁ := TransAux fuel (Pred M)
            if t₁ == BZero then
              if m == 0 then Dprin 0 (Dprin (entry M 1 j₁ : ℕ∞) BZero)
              else Dprin (entry M 1 j₁ : ℕ∞) BZero
            else
              let j' := lastParent M
              let c₁ := MarkAux fuel (Pred M) (Adm M j')
              let c₂ := transC2Core M (bpHeadV c₁) (bpHeadT c₁)
              if m < j₁ then
                let c₀ := MarkAux fuel (Pred M) m
                match (scbContexts c₀ (flatBT c₁)).head? with
                | some (s, b) => unflatBT (s ++ flatBT c₂ ++ b)
                | none => Dprin (entry M 1 j₁ : ℕ∞) BZero
              else
                Dprin (entry M 1 j₁ : ℕ∞) BZero
          else
            let ps := P M
            let J₁ := ps.length - 1
            let pJ := ps.getD J₁ []
            let j₀ := j₁ - Lng pJ + 1
            if pJ == [(0, 0)] then Dprin 0 BZero
            else MarkAux fuel pJ (m - j₀)
end

/-- ペア数列から Buchholz 項への翻訳。 -/
def Trans (M : PS) : BT := TransAux (transFuel M) M

/-- 基点付きペア数列の翻訳。 -/
def Mark (M : PS) (m : ℕ) : BT := MarkAux (transFuel M) M m

/- 原文で後続命題から参照する中間量。 -/
def transJ1 (M : PS) : ℕ := lastIdx M
def transJ0 (M : PS) : ℕ := lastParent M
def transJm1 (M : PS) : ℕ := Adm M (transJ0 M)
def transT1 (M : PS) : BT := Trans (Pred M)
def transC1 (M : PS) : BT := Mark (Pred M) (transJm1 M)
def transV (M : PS) : ℕ∞ := bpHeadV (transC1 M)
def transT2 (M : PS) : BT := bpHeadT (transC1 M)
def transC2 (M : PS) : BT := transC2Core M (transV M) (transT2 M)

/-! 構文解析器と原文の基本例を固定する回帰テスト。 -/

#guard unflatBT (flatBT BZero) == BZero
#guard unflatBT (flatBT (Dprin 2 (Dprin 1 BZero))) == Dprin 2 (Dprin 1 BZero)
#guard unflatBT (flatBT (.trm [.db 0 BZero, .db 1 BZero])) ==
  .trm [.db 0 BZero, .db 1 BZero]
#guard Trans [(1, 1), (2, 2)] == Dprin 1 (Dprin 2 BZero)
#guard Mark [(1, 1), (2, 2)] 0 == Dprin 1 (Dprin 2 BZero)
#guard Mark [(1, 1), (2, 2)] 1 == Dprin 2 BZero

end PSS
