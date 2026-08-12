import «Buchholz-1986».«Buchholz-1986-3.2»

/-!
# Buchholz, “Relating ordinals to proofs in a prespicious way”, p.6 Definition 6

未刊行原稿 [Buc2] 自体は入手不能である。記事 §7.1 脚注30が明記した
Buchholz (1986) ([].4)(ii) の差し替えを実装する。

基本列は訂正 A23 後の
`x₀ = Dᵤ0`, `xᵢ₊₁ = Dᵤ(b[xᵢ])`, `(Dᵥb)[n] = Dᵥ(b[xₙ])` を採用する。
その他の分岐は Buchholz (1986) ([].0)–([].5) である。
-/

namespace PSS

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

/-- Internal call states of the shared `operB`/`xseq` recursion. -/
inductive BOperState where
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
/-- Shared well-founded recursion core for `operB` and `xseq`.
Exposed so proposition files can use its definitional reduction equations. -/
def bOperCore (s : BOperState) : BT :=
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

/-! 基本例と A23 分岐を壊さないための回帰テスト。 -/

#guard lessBT BZero (Dprin 0 BZero)
#guard domTag BZero == .empty
#guard domTag (Dprin 0 BZero) == .zeroOnly
#guard domTag (Dprin ⊤ BZero) == .naturals
#guard operB (Dprin 0 BZero) BZero == BZero
#guard operB (Dprin ⊤ BZero) (numBT 3) == Dprin (4 : ℕ∞) BZero

end PSS
