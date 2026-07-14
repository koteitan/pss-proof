import PSS.Defs

/-!
# PSS.Mono — §6.2 単項性 / 単項成分 `P`, §6.4 幹と枝

移植元: `isabelle/pss_defs.thy` §6.2, §6.4。

`P` の再帰は Isabelle では `Pcut M < Lng M` を示して停止性を証明しているが、
ここでは **燃料 `Lng M`** で回す（1 段ごとに長さが真に減るので `Lng M` 段で足りる）。
`Defs.lean` の `le0Aux` と同じ方針＝計算可能性を優先する。
-/

namespace PSS

/-! ## §6.2 零項 / 単項 / 複項 -/

/-- `zeroT M`（零項）: `Lng M = 1` かつ `M_{1,0} = 0`。 -/
def zeroT (M : PS) : Bool := (Lng M == 1) && (entry M 1 0 == 0)

/-- `monoT M`（単項）: 零項でなく、`(0,0) ≤_M (0, Lng M - 1)`。 -/
def monoT (M : PS) : Bool := !zeroT M && leR M 0 0 (Lng M - 1)

/-- `multiT M`（複項）: 零項でも単項でもない。 -/
def multiT (M : PS) : Bool := !zeroT M && !monoT M

/-- `Pcut M`: `0 < j ≤ Lng M - 1` かつ `(0,j) ≤_M (0, Lng M - 1)` を満たす最小の `j`。 -/
def Pcut (M : PS) : ℕ :=
  ((List.range (Lng M)).find?
      (fun j => (0 < j) && (j ≤ Lng M - 1) && leR M 0 j (Lng M - 1))).getD (Lng M - 1)

/-- `P` の本体（燃料付き）。 -/
def PAux : ℕ → PS → List PS
  | 0,        M => [M]
  | fuel + 1, M =>
      if multiT M && (1 < Lng M) then
        PAux fuel (M.take (Pcut M)) ++ [M.drop (Pcut M)]
      else [M]

/-- `P M`（§6.2）: `M` を非複項（零項/単項）成分に分解する。 -/
def P (M : PS) : List PS := PAux (Lng M) M

/-! ## §6.4 幹と枝 -/

/-- `IdxSum Q`: 各成分の長さの累積和（長さ `Lng Q + 1`）。 -/
def IdxSum (Q : List PS) : List ℕ :=
  (List.range (Q.length + 1)).map (fun J => ((Q.take J).map Lng).sum)

/-- `TrMax M`（幹の右端）: `∀ j' < j` で `(1,j') <^Next_M (1,j'+1)` が成り立つ最大の `j`。

`nextR M 1 j (j+1)` が偽になる最小の `j` に等しい（`j+1` が範囲外なら必ず偽なので
`Lng M - 1` で頭打ちになる）。 -/
def TrMax (M : PS) : ℕ :=
  ((List.range (Lng M)).find? (fun j => !nextR M 1 j (j + 1))).getD (Lng M - 1)

/-- `Br M`（枝）: 幹の右側の切片の `P` 分解。 -/
def Br (M : PS) : List PS :=
  if TrMax M = Lng M - 1 then [] else P (seg M (TrMax M + 1) (Lng M - 1))

/-- `FirstNodes M`: 各枝成分の（`M` における）左端。 -/
def FirstNodes (M : PS) : List ℕ :=
  (IdxSum (Br M)).map (fun x => TrMax M + 1 + x)

/-- `Joints M`: 各枝成分の左端の、上段における親。 -/
def Joints (M : PS) : List ℕ :=
  (List.range (Br M).length).map (fun J =>
    parent M 0 ((FirstNodes M).getD J 0))

end PSS
