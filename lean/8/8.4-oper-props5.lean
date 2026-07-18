import «8».«8.4-s84x-vocab-run»
import «7».«7.4-Trans-Mark-seg»
import «7».«7.3-Trans-preserves-zeroT»
import «6».«6.7-standard-reduced»

/-!
# §8.4 `oper` 基本性質 (5) — `s84x_L` 塔上の `Trans`-`Mark`-切片の一意対

- 原文: `tmp/content.md` 4389（命題「条件(III)〜(VI)の下での展開規則の基本性質」
  parts (5-1)/(5-2)/(5-3)）。原文では §8.4 の scb 分解クラスタは `pss_paper.thy` 上
  DEFERRED（`8.4-scb-decompositions`）。
- Isabelle（設計図）: `m_8_4_oper_props_5`（`isabelle/layerB/pss_wip.thy`:54005、~203 行）。
  * `s84x_L`  (wip:52636) = `M[n] @ [(M_{0,j₋₂} + n·(M_{0,j₁}−M_{0,j₋₂}), M_{1,j₋₂})]`
  * `s84x_Lp` (wip:52632) = `seg M j₋₂ (Lng M − 2) @ [(M_{0,j₁}, M_{1,j₋₂})]`
  * `s84x_w`/`s84x_ms` = Isabelle の `?w = Lng M − 1 − j₋₂`, `?ms = j₋₂ + (n−1)·?w`。
- 消費側: `CondVIres_nadm_Ltower_v6p`（`8.6-condVI-props`:421）が要求する非許容枝の
  L 塔閉形式（Isabelle `c6nx_condVI_exch_nadm_uncond` / `c6zx_L_tower` (:72166)）の
  **帰納エンジン**が本補題。許容枝 `CondVIres_adm_Ltower_v6p` も同じエンジンに乗る。

## 移植方針（house green-modulo）

`m_8_4_oper_props_5` の **組み立て構造**（ex1 = `m_7_4_Trans_Mark_seg` を `s84x_L M n`
に適用 → `L_n` 上の seg/entry/Mark の 3 書き換え → part (5-3) の内部/境界の場合分け →
`scb` 一意性による対の輸送 → `ex1I` 梱包）を Lean で完全証明した。

Isabelle の `m_7_2_scb_unique_sb`（`tne` を要する）は Lean では**無条件**版
`scb_unique_decomp_unconditional`（`7.2-scb-unique`:614）に置き換わるので、
Isabelle 版が経由する `Trans (L_{n−1}) ≠ 0_B`（tne）の段は Lean では不要。

エンジンより下の **§8.4 局所の値事実（`s84c1_*` クラスタ、wip:52660–54005 の ~1350 行、
Lean 未移植）** は名前付き Prop `Oper5Support` に束ねて入力とした（10 葉）。これは
Isabelle の `s84c1_jm2_basic` / `s84c1_Lng_oper` / `s84c1_Lng_L` / `s84c1_marked_L` /
`m_8_4_oper_props_2(1)` / `s84c1_L_prefix` / `s84c1_Mn_entry_mstar` / `s84c1_Mark_L_mstar` /
`s84c1_Mark_Mn_mstar` / `s84c1_oper_Suc_eq_L_app` / `s84c1_Pred_Np` に対応。`needs` 参照。

- 依存（すべてビルド済み・committed 04e06e1）: «8».«8.4-s84x-vocab-run»
  (`s84x_jm2`/`s84x_Np`/`STPS`/`RTPS`/`oper`/`seg`/`entry`)、«7».«7.4-Trans-Mark-seg»
  (`m_7_4_Trans_Mark_seg`/`Trans`/`Mark`/`Marked`/`scb_decomp`/`flatBT`/`Dprin`/
  `scb_unique_decomp_unconditional`/`RTPS_TPS`)、«7».«7.3-Trans-preserves-zeroT»、
  «6».«6.7-standard-reduced» (`STPS.oper`/`STPS_RTPS`)。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  組み立ては無条件に閉じ、残差は `Oper5Support`（§8.4 `s84c1_*` 値クラスタ）1 束のみ。
- Private helper suffix: `_op5`。
-/

namespace PSS

/-! ## 1. §8.4 scb 分解クラスタの語彙（`isabelle/layerB/pss_wip.thy`:52632–52636） -/

/-- Isabelle `s84x_Lp` (wip:52632): `L` 塔の底となる 1 段短い列。 -/
def s84x_Lp (M : PS) : PS :=
  seg M (s84x_jm2 M) (Lng M - 2)
    ++ [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))]

/-- Isabelle `s84x_L` (wip:52636): 基本列 `M[n]` に行1で `j₋₂` を複製した最終列を足した
`L` 塔の第 `n` 段。 -/
def s84x_L (M : PS) (n : ℕ) : PS :=
  oper M n
    ++ [(entry M 0 (s84x_jm2 M)
          + n * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
        entry M 1 (s84x_jm2 M))]

/-- Isabelle 証明中の `?w = Lng M − 1 − j₋₂`（`L` 塔の周期幅）。 -/
def s84x_w (M : PS) : ℕ := Lng M - 1 - s84x_jm2 M

/-- Isabelle 証明中の `?ms = j₋₂ + (n−1)·?w`（第 `n` 段の共通基点位置）。 -/
def s84x_ms (M : PS) (n : ℕ) : ℕ := s84x_jm2 M + (n - 1) * s84x_w M

/-! ## 2. §8.4 局所の値事実の束（`s84c1_*` クラスタ、Lean 未移植分の入力） -/

/-- `m_8_4_oper_props_5` の組み立てが消費する §8.4 局所の値事実（Isabelle `s84c1_*` 群）。
分解エンジン `m_7_4_Trans_Mark_seg` より下の葉のみ。 -/
def Oper5Support (M : PS) (n : ℕ) : Prop :=
  -- `s84c1_jm2_basic(1)`: 行1の親 `j₋₂` は最終列より真に左。
  s84x_jm2 M < Lng M - 1
  -- `s84c1_Lng_oper` ＋ `s84c1_mult_pred`: `Lng (M[n]) = ?ms + ?w`。
  ∧ Lng (oper M n) = s84x_ms M n + s84x_w M
  -- `s84c1_Lng_L`: `Lng (L_n) = Lng (M[n]) + 1`。
  ∧ Lng (s84x_L M n) = Lng (oper M n) + 1
  -- `s84c1_marked_L`: `(L_n, ?ms) ∈ Marked`。
  ∧ Marked (s84x_L M n) (s84x_ms M n)
  -- `m_8_4_oper_props_2(1)`: `L_n ∈ RT_PS`。
  ∧ RTPS (s84x_L M n)
  -- `s84c1_L_prefix(2)`: `seg (L_n) 0 ?ms = L_{n−1}`。
  ∧ seg (s84x_L M n) 0 (s84x_ms M n) = s84x_L M (n - 1)
  -- `s84c1_Mn_entry_mstar` 経由: `entry (L_n) 1 ?ms = M_{1,j₋₂}`。
  ∧ entry (s84x_L M n) 1 (s84x_ms M n) = entry M 1 (s84x_jm2 M)
  -- `s84c1_Mark_L_mstar`: `Mark (L_n) ?ms = Trans (L')`。
  ∧ Mark (s84x_L M n) (s84x_ms M n) = Trans (s84x_Lp M)
  -- 内部レジーム `j₋₂ + 1 < j₁`: `s84c1_Mark_Mn_mstar(2)`/`(1)`/`s84c1_L_prefix(1)`。
  ∧ (s84x_jm2 M + 1 < Lng M - 1 →
        Marked (oper M n) (s84x_ms M n)
      ∧ Mark (oper M n) (s84x_ms M n) = Trans (Pred (s84x_Np M))
      ∧ seg (oper M n) 0 (s84x_ms M n) = s84x_L M (n - 1)
      ∧ entry (oper M n) 1 (s84x_ms M n) = entry M 1 (s84x_jm2 M))
  -- 境界レジーム `j₋₂ + 1 = j₁`: `s84c1_oper_Suc_eq_L_app`（`M[n] = L_{n−1}`）＋
  -- `s84c1_Pred_Np` から得る `Trans (Pred N') = D_{M_{1,j₋₂}} 0`。
  ∧ (¬ (s84x_jm2 M + 1 < Lng M - 1) →
        oper M n = s84x_L M (n - 1)
      ∧ (¬ (zeroT (Pred (s84x_Np M)) = true) →
            Trans (Pred (s84x_Np M))
              = Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero))

/-! ## 3. 組み立て（Isabelle `m_8_4_oper_props_5`, wip:54005） -/

/-- Isabelle `m_8_4_oper_props_5`（wip:54005）。`s84x_L` 塔の第 `n` 段について、
`Trans (L_{n−1})` と `Trans (L_n)` を共有 `scb` 位置 `(s,b)` で結ぶ一意対が存在し、
`Pred N'` が非零項ならその位置で `Trans (M[n])` も分解される。

Isabelle の 5 仮定（`M ∈ ST_PS`/`M ∈ PT_PS`/`hasParent M 1 (Lng M − 1)`/`1 < Lng M − 1`/
`n > 1`）に加えて、§8.4 局所の値事実 `Oper5Support M n`（`s84c1_*` クラスタ、`needs`）を
入力とする green-modulo 形。 -/
theorem m_8_4_oper_props_5 (M : PS) (n : ℕ)
    (hST : STPS M) (_hmono : monoT M = true)
    (_hp : hasParent M 1 (Lng M - 1) = true) (_hj1 : 1 < Lng M - 1) (hn : 1 < n)
    (hsupp : Oper5Support M n) :
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_L M (n - 1))) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2
        ∧ scb_decomp (Trans (s84x_L M n)) sb.1 (flatBT (Trans (s84x_Lp M))) sb.2
        ∧ (¬ (zeroT (Pred (s84x_Np M)) = true) →
             scb_decomp (Trans (oper M n)) sb.1
               (flatBT (Trans (Pred (s84x_Np M)))) sb.2) := by
  obtain ⟨hjm2lt, hLngMn, hLngLn, hmk, hLnRT, hsegpfx, he1ms, hmarkL,
          hInterior, hBoundary⟩ := hsupp
  -- 算術下ごしらえ（Isabelle の j1gt/w1/mspos/mslt）
  have hwdef : s84x_w M = Lng M - 1 - s84x_jm2 M := rfl
  have hwpos : 0 < s84x_w M := by rw [hwdef]; omega
  have hmsdef : s84x_ms M n = s84x_jm2 M + (n - 1) * s84x_w M := rfl
  have hprod : 0 < (n - 1) * s84x_w M := Nat.mul_pos (by omega) hwpos
  have mspos : 0 < s84x_ms M n := by rw [hmsdef]; omega
  have mslt : s84x_ms M n < Lng (s84x_L M n) - 1 := by
    rw [hLngLn, hLngMn]; omega
  -- parts (5-1)+(5-2): `L_n` 上の Trans-Mark-seg 一意対（Isabelle `ex1`）
  have hseg := m_7_4_Trans_Mark_seg (s84x_L M n) (s84x_ms M n) hmk hLnRT mspos mslt
  simp only [hsegpfx, he1ms, hmarkL] at hseg
  obtain ⟨sb, ⟨hA1, hA2⟩, hU⟩ := hseg
  -- part (5-3): `¬ zeroT (Pred N')` 下での `M[n]` 側の分解（Isabelle `C3`）
  have hC3 : ¬ (zeroT (Pred (s84x_Np M)) = true) →
      scb_decomp (Trans (oper M n)) sb.1
        (flatBT (Trans (Pred (s84x_Np M)))) sb.2 := by
    intro hgz
    by_cases hint : s84x_jm2 M + 1 < Lng M - 1
    · -- 内部レジーム: `M[n]` に Trans-Mark-seg を再適用し `scb` 一意性で対を輸送
      obtain ⟨hmkMn, hmarkMn, hsegpfxM, he1msM⟩ := hInterior hint
      have hMnRT : RTPS (oper M n) := STPS_RTPS _ (STPS.oper hST n (by omega))
      have msltMn1 : s84x_ms M n < Lng (oper M n) - 1 := by
        rw [hLngMn]
        have hw2 : 2 ≤ s84x_w M := by rw [hwdef]; omega
        omega
      have hInt :=
        m_7_4_Trans_Mark_seg (oper M n) (s84x_ms M n) hmkMn hMnRT mspos msltMn1
      simp only [hsegpfxM, he1msM, hmarkMn] at hInt
      obtain ⟨sb', ⟨hC1', hC3'⟩, _⟩ := hInt
      have huniq := scb_unique_decomp_unconditional
        (Trans (s84x_L M (n - 1))) sb'.1 sb.1
        (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb'.2 sb.2 hC1' hA1
      rw [huniq.1, huniq.2] at hC3'
      exact hC3'
    · -- 境界レジーム: `M[n] = L_{n−1}` かつ `Trans (Pred N') = D_{M_{1,j₋₂}} 0`
      obtain ⟨hMnL, hTransPn⟩ := hBoundary hint
      rw [hMnL, hTransPn hgz]
      exact hA1
  -- ex1I 梱包（一意性は最初の 2 連言で決まる）
  refine ⟨sb, ⟨hA1, hA2, hC3⟩, ?_⟩
  intro y hy
  exact hU y ⟨hy.1, hy.2.1⟩

#print axioms m_8_4_oper_props_5

end PSS
