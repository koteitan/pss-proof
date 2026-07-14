import PSS.Mono

/-!
# PSS.Red — §6.5 簡約化 / §6.6 簡約性

移植元: `isabelle/pss_defs.thy` §6.5–§6.6。

Isabelle 版は `function (domintros)` で `Red` の停止性を後回しにできるが、Lean の定義は
その場で停止性を必要とする。そのため、ここでは `RedAux` を燃料付きで定義し、Isabelle 側の
停止性証明で使った測度 `nu` より 1 大きい燃料から開始する。`T_PS` 上でこの燃料が尽きない
ことは §6.5「Red の well-defined 性」で証明する。

燃料が尽きた場合の値は入力自身とする。この分岐は `T_PS` 上の本来の計算には現れず、空列を
含む型 `PS` 全体で定義を全域化するためだけにある。
-/

namespace PSS

/-- `diagSeq a b = ((j,j))_(j=a)^b`。`b < a` なら空列。 -/
def diagSeq (a b : ℕ) : PS :=
  (List.range' a (b + 1 - a)).map (fun j => (j, j))

/-- `IncrFirst` の `n` 回反復。 -/
def IncrFirstN : ℕ → PS → PS
  | 0,     M => M
  | n + 1, M => IncrFirstN n (IncrFirst M)

/-! ## 停止性測度

以下の 4 定義は `isabelle/pss_mechanized.thy` の `betaM`, `coreReduce`, `muMono`, `nu`
からの移植である。`Red` の各再帰呼出しでは `nu` が真に減少する。
-/

/-- 幹より右に残る位置の個数を測る核測度。 -/
def betaM (M : PS) : ℕ := Lng M - TrMax M

/-- 非核単項列を、`Red` が次に呼び出す核列へ 1 段だけ移す。 -/
def coreReduce (M : PS) : PS :=
  if entry M 1 0 = 0 then
    (List.range (Lng M)).map (fun j =>
      (entry M 0 j - entry M 0 0, entry M 1 j))
  else
    diagSeq 0 (entry M 1 0 - 1) ++ IncrFirstN (entry M 1 0) M

/-- 零項または単項に対する停止性測度。 -/
def muMono (M : PS) : ℕ :=
  if entry M 0 0 = 0 ∧ entry M 1 0 = 0 then
    2 * betaM M
  else
    2 * betaM (coreReduce M) + 1

/-- `Red` 全体の停止性測度。複項では `P` 成分の測度の和を使う。 -/
def nu (M : PS) : ℕ :=
  if multiT M then 1 + ((P M).map muMono).sum else muMono M

/-! ## 簡約化 -/

/-- `Red` の燃料付き本体。

`fuel = 0` は全域化のための打切り値。`Red M` は `nu M + 1` から始まり、`TPS M` の下では
全再帰呼出しが打切り前に完了する。 -/
def RedAux : ℕ → PS → PS
  | 0, M => M
  | fuel + 1, M =>
      if zeroT M then [(0, 0)]
      else if multiT M then
        (P M).flatMap (fun Q => RedAux fuel Q)
      else
        let j1 := Lng M - 1
        let j1' := TrMax M
        let m00 := entry M 0 0
        let m10 := entry M 1 0
        if m00 = 0 ∧ m10 = 0 then
          if j1' = j1 then
            diagSeq m10 (m10 + j1)
          else
            diagSeq 0 j1' ++
              (List.range (Br M).length).flatMap (fun J =>
                let block := (Br M).getD J []
                let firstNode := (FirstNodes M).getD J 0
                let joint := (Joints M).getD J 0
                let np :=
                  if entry block 1 0 = 0 then 0
                  else parent M 1 firstNode + 1
                let eJ := joint + 1 - np
                let NJ := (m00 + joint + 1, m10 + np) :: block.tail
                IncrFirstN eJ (RedAux fuel NJ))
        else if m10 = 0 then
          RedAux fuel (coreReduce M)
        else
          let N := RedAux fuel (coreReduce M)
          let jN := Lng N - 1
          let S := seg N m10 jN
          if decide (m10 ≤ jN) && monoT S then
            (List.range' m10 (jN + 1 - m10)).map (fun j =>
              (entry N 0 j - entry N 0 m10 + entry N 1 m10, entry N 1 j))
          else M

/-- `Red M`（簡約化）。 -/
def Red (M : PS) : PS := RedAux (nu M + 1) M

/-! ## 簡約性と係数条件 -/

/-- `M` が簡約形であることの計算可能な判定。 -/
def reduced (M : PS) : Bool := !M.isEmpty && (Red M == M)

/-- `RT_PS`: 空でない簡約形ペア数列。 -/
def RTPS (M : PS) : Prop := reduced M = true

instance (M : PS) : Decidable (RTPS M) := by
  unfold RTPS
  infer_instance

/-- 条件 (A): 一意な親を持つ各係数は、その親の係数より 1 大きい。 -/
def RedCondA (M : PS) : Bool :=
  (List.range 2).all (fun i =>
    (List.range (Lng M)).all (fun j =>
      !hasParent M i j ||
        decide (entry M i (parent M i j) + 1 = entry M i j)))

/-- 条件 (B): 上段に一意な親を持たない各位置では上下の係数が等しい。 -/
def RedCondB (M : PS) : Bool :=
  (List.range (Lng M - 1 + 1)).all (fun j =>
    hasParent M 0 j || decide (entry M 0 j = entry M 1 j))

/-! `Red` が `T_PS` 上で冪等でないこと（訂正 A4）の最小回帰テスト。 -/

#guard Red [(0, 0), (0, 2)] == [(0, 0), (2, 2)]
#guard Red [(0, 0), (2, 2)] == [(0, 0), (1, 1)]
#guard Red (Red [(0, 0), (0, 2)]) != Red [(0, 0), (0, 2)]

end PSS
