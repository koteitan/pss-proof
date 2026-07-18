import «8».«8.4-exch84-nest-scb»

/-!
# §8.4 交換パッケージ `d4a` 転送残差の discharge（`NestScbD4aTransport_ns`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 対象: `NestScbD4aTransport_ns`（«8».«8.4-exch84-nest-scb»:80 で def・narrowing 済の残差）
  = Isabelle `cpx_d4a_all` (layerB/pss_wip.thy:98511)。共通 `(u1, v1)` を持つ
  `dP`（`Trans (Pred (s84x_N M))` の scb 分解、頭 `Dsym(M₁,ⱼ₋₃)`）から
  `d4a`（`Trans (Pred (s84x_Np M))` の scb 分解、頭 `Dsym(M₁,ⱼ₋₂)`）を作る。

## 移植構造（Isabelle `cpx_d4a_all` → `crg_d4a_trunk`/`crx_d4a_of_redreg` 共通骨格）

Isabelle の `cpx_d4a_all` は `Br (Red (Pred (s84x_N M)))` の空判定で trunk 枝
（`crg_d4a_trunk`）と regime 枝（`crx_d4a_of_redreg`、`cfbx_reg` = VEReg を消費）に
分岐するが、**両枝の scb 部分は完全に同一**であり、次の 2 つの値事実に集約される
（`WP := bpHeadT (Trans (Pred (s84x_N M)))`）:

* `princSP`: `Trans (Pred (s84x_N M)) = D_{M₁,ⱼ₋₃} WP`（源 slice が principal・頭 = `entry M 1 jm3`）。
* `valPNp'`: `Trans (Pred (s84x_Np M)) = D_{M₁,ⱼ₋₂} WP`（標的 slice が principal・**同一 tail** `WP`・頭 = `entry M 1 jm2`）。

これらが得られれば残りは純粋な scb 操作: `dP` を principal 形に書き換え（`princSP`）、
principal 頭を剥がし（`scb_dprin_unlift_d4` = Isabelle `w84x_scb_unlift`）、
新しい頭 `Dsym(M₁,ⱼ₋₂)` を被せ直す（`scb_dprin_lift_d4` = Isabelle `scb_Dpt_lift`
(layerB/pss_wip.thy:1663)）、そして `valPNp'` で結論の値へ書き換えるだけ。

### 源 principal `princSP` は `dP` から無条件に取れる

`dP` の flatten 等式は `flatBT (Trans (Pred (s84x_N M)))` が `Sym.dsym (entry M 1 jm3)`
で始まることを主張する。`flatBT` の場合分けより、`Sym.dsym _` で始まる BT は必ず単一
principal `.trm [.db _ _]` = `Dprin _ _` である（`.trm []` は `[.zero]`、multi は `[.lp,…]`
で始まる）。従って `flatBT_head_dsym_principal_d4` により `princSP` は `dP` から直接得られ、
trunk/regime の値エンジン（`crx_slice_red_head` / `crg_slice_red_value_trunk`）は不要になる。

## 残差（named Prop + needs）

深い値エンジンが供給する **標的 slice の principal 値** `valPNp'` のみを 1 本の named
Prop `NestScbD4aTargetValue` として残す（trunk 枝 = `crg_slice_red_value_trunk` の対角閉形式、
regime 枝 = `crx_slice_red_value` の `cfbx_reg` = VEReg 消費、いずれも Lean 未移植・
単一ファイルの範囲外）。源 principal と scb 操作の骨格は本ファイルで完全証明。

- 依存（ビルド済み）: «8».«8.4-exch84-nest-scb»（`NestScbD4aTransport_ns` def・
  `s84x_N`/`s84x_Np`/`s84x_jm2`/`s84x_jm3`・`transC1`・`Trans`/`Pred`/`bpHeadT`/
  `Dprin`/`flatBT`/`scb_decomp`/`isPTB_str`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `NestScbD4aTransport_ns` を **1 残差** `NestScbD4aTargetValue`（標的 slice 値）へ narrowing。
- 訂正: なし。
- Private helper suffix: `_d4`。
-/

namespace PSS

/-! ## 1. scb 操作の骨格（Isabelle `scb_Dpt_lift` / `w84x_scb_unlift` の Lean 語彙移植） -/

/-- Isabelle `w84x_scb_unlift` (layerB/pss_wip.thy:78906): principal 頭 `Dprin v` と
先頭記号 `Dsym v` を同時に剥がす。 -/
private theorem scb_dprin_unlift_d4 {W : BT} {v : ℕ∞} {s c b : List Sym}
    (d : scb_decomp (Dprin v W) (Sym.dsym v :: s) c b) : scb_decomp W s c b := by
  obtain ⟨hflat, hipt, hb⟩ := d
  refine ⟨?_, ?_, hb⟩
  · have h1 : flatBT (Dprin v W) = Sym.dsym v :: flatBT W := by
      simp [Dprin, flatBT, flatBP]
    rw [h1] at hflat
    simpa [List.cons_append] using hflat
  · intro _
    exact hipt (by simp [Dprin, BZero])

/-- Isabelle `scb_Dpt_lift` (layerB/pss_wip.thy:1663): principal 頭 `Dprin v` と
先頭記号 `Dsym v` を被せると scb 分解の中辺・末尾は保存される。 -/
private theorem scb_dprin_lift_d4 {W : BT} {v : ℕ∞} {s c b : List Sym}
    (d : scb_decomp W s c b) (ipt : isPTB_str c) :
    scb_decomp (Dprin v W) (Sym.dsym v :: s) c b := by
  obtain ⟨hflat, _, hb⟩ := d
  refine ⟨?_, ?_, hb⟩
  · have h1 : flatBT (Dprin v W) = Sym.dsym v :: flatBT W := by
      simp [Dprin, flatBT, flatBP]
    rw [h1, hflat]
    simp [List.cons_append]
  · intro _; exact ipt

/-- 頭が `Sym.dsym v` の flatten を持つ BT は単一 principal `Dprin v (bpHeadT t)`。 -/
private theorem flatBT_head_dsym_principal_d4 {t : BT} {v : ℕ∞} {rest : List Sym}
    (h : flatBT t = Sym.dsym v :: rest) : t = Dprin v (bpHeadT t) := by
  cases t with
  | trm ps =>
    rcases ps with _ | ⟨p, ps'⟩
    · simp [flatBT] at h
    · rcases p with ⟨u, a⟩
      rcases ps' with _ | ⟨q, qs⟩
      · simp only [flatBT, flatBP] at h
        injection h with hhead _
        injection hhead with hu
        subst hu
        rfl
      · simp [flatBT, flatBP] at h

/-! ## 2. 残差 named Prop（標的 slice の principal 値、Isabelle `valPNp'`） -/

/-- 残差: 標的 slice `Pred (s84x_Np M)` の principal 値。`WP = bpHeadT (Trans (Pred (s84x_N M)))`
を共通 tail として `Trans (Pred (s84x_Np M)) = D_{entry M 1 jm2} WP`。
Isabelle 値エンジン `crx_slice_red_value` (regime, `cfbx_reg`=VEReg 消費) /
`crg_slice_red_value_trunk` (trunk 対角閉形式) の出力。両者とも Lean 未移植のため named Prop。 -/
def NestScbD4aTargetValue : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    Trans (Pred (s84x_Np M))
      = Dprin ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) (bpHeadT (Trans (Pred (s84x_N M))))

/-! ## 3. house pattern による `NestScbD4aTransport_ns` の discharge -/

/-- house-pattern discharge: `NestScbD4aTransport_ns`（«8».«8.4-exch84-nest-scb»:80、
= Isabelle `cpx_d4a_all`）を 1 残差 `NestScbD4aTargetValue` へ narrowing。
源 principal は `dP` から無条件に取り、scb 骨格（unlift/lift）を完全証明する。 -/
theorem nestScbD4aTransport_holds (hVal : NestScbD4aTargetValue) :
    NestScbD4aTransport_ns := by
  intro M u1 v1 hST hmono hp hj1 hcond dP
  have valNp := hVal M hST hmono hp hj1 hcond
  -- 源 principal（`dP` から無条件に）
  have hf : flatBT (Trans (Pred (s84x_N M)))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          :: (u1 ++ flatBT (transC1 M) ++ v1) := by
    have h := dP.1
    simpa [List.cons_append] using h
  have princN : Trans (Pred (s84x_N M))
      = Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
          (bpHeadT (Trans (Pred (s84x_N M)))) :=
    flatBT_head_dsym_principal_d4 hf
  -- `flatBT (transC1 M)` の principal 性（`dP` の scb 条件から）
  have iptP : isPTB_str (flatBT (transC1 M)) := by
    apply dP.2.1
    rw [princN]; simp [Dprin, BZero]
  -- `dP` を principal 形へ書き換えて頭を剥がす
  rw [princN] at dP
  have innerP : scb_decomp (bpHeadT (Trans (Pred (s84x_N M)))) u1
      (flatBT (transC1 M)) v1 :=
    scb_dprin_unlift_d4 dP
  -- 新しい頭 `Dsym(M₁,ⱼ₋₂)` を被せ直す
  have lifted := scb_dprin_lift_d4
    (v := ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞)) innerP iptP
  rw [valNp]
  exact lifted

#print axioms nestScbD4aTransport_holds

end PSS
