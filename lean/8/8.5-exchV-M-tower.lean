import «8».«8.5-exchV-props2»
import «8».«8.4-oper5-support»

/-!
# §8.5 exchV 最終残差 `ExchV_M_tower` の討伐（`m_8_4_oper_props_5` 塔帰納）

- 原文: `tmp/content.md` §8.5「命題（条件(V)の下での Trans と基本列の交換関係）」。
- 対象: ビルド済み «8».«8.5-exchV-props2»:110 が定義した唯一の残差 named Prop
  `ExchV_M_tower`。これを閉じると exchV の残差 2 本
  (`ExchVres_adm_M_tower` / `ExchVres_nadm_M_tower`) がともに消え、条件(V) の
  停止性フィールド (`exchVresAdmTowers` / `exchVnf3x`) が落ちる。
  (props2 の `exchVres_adm_M_tower_of_M_tower` / `exchVres_nadm_M_tower_of_M_tower`
   がともに `ExchV_M_tower` に還元済み。)

- Isabelle（設計図）:
  * adm 枝の塔閉形式 = `m_8_5_scbdec_adm_forms` 結論 (5) (isabelle/layerB/pss_wip.thy:57556)
  * 非 adm 枝の塔閉形式 = `nfx_M_tower` (同 :64348)
  * 両者の共有エンジン = `m_8_4_oper_props_5` (同 :54005) ＋ `s84x_L` 塔帰納。
  **重要な観察**: adm 枝と非 adm 枝は**帰納段が完全に同一**であり、相違は
  (a) 外側頭 `u = M_{1,j₋₁}`（adm では `= e = M_{1,j₀}`、非 adm では `≠`）と
  (b) `L₁` の底の塔段数 `baseL`（adm=1／非 adm=2）だけ。
  この 2 点はどちらも `exchV_tail M 1` と `entry M 1 (transJm1 M)` に吸収される。
  そこで本ファイルは **adm/非 adm を場合分けせず**、`L`-塔・`M`-塔の joint 帰納を
  **単一**で回す（block 数 = `exchV_tail M (k+1)`／`exchV_tail M k`、両枝一様）。

## 移植方針（house green-modulo）

engine `m_8_4_oper_props_5` は **移植済み**（«8».«8.4-oper-props5»、`Oper5Support`
modulo）。`oper5Support_holds`（«8».«8.4-oper5-support»）は `Oper5Support` を
`Oper5Residual`（§7.4 Mark 依存、並行 agent が閉包中）に還元する。よって塔帰納を
`Oper5Residual` の各段 ＋ **3 つの底スライス値**（`PredNp`/`Lpv`/`L1v`、Isabelle
`m_8_5_scbdec_PredNp_condV` / `_Lp_condV` / `s85b_L1_decomp_adm` = adm 枝 proven、
非 adm 枝は §8.2 VE 残差）＋ 条件(V) 構造事実（`s85b_condV_bridge(3)(4)`）に還元する。

これらをまとめた named Prop `ExchVMTowerResidual` を定義し、
`exchV_M_tower_of_residual (h : ExchVMTowerResidual) : ExchV_M_tower` を **無条件に**
証明する（house pattern：定理の型が `ExchV_M_tower` そのもの）。残差 1 本のみ。

- 依存（すべてビルド済み・main 670d2ee）: «8».«8.5-exchV-props2»
  (`ExchV_M_tower` / `exchV_tail` / 推移的に `condV_setup_holds` / `c1_shape_holds`)、
  «8».«8.4-oper5-support» (`oper5Support_holds` / `Oper5Residual` /
  推移的に «8».«8.4-oper-props5» = `m_8_4_oper_props_5` / `s84x_L` / `s84x_Lp` /
  `s84x_Np` / `s84x_jm2`)、«7».«7.2-scb-unique» (`scb_unique_decomp_unconditional`)、
  «7».«7.2-add-scb» (`add_scb_replace_last`)。
- 訂正: なし（A28 は取り下げ済み、`corrections-old.md`:95）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 `ExchVMTowerResidual`（`needs` 参照）1 本。塔帰納・文字列代数は無条件に閉じる。
- Private helper suffix: `_mt`。
-/

namespace PSS

/-! ## 文字列代数の generic 補題（props2 の同名 private を `_mt` で複製） -/

private theorem flatten_replicate_comm_mt {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = b ++ (List.replicate j b).flatten := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

private theorem flatten_replicate_snoc_mt {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = (List.replicate (j + 1) b).flatten := by
  rw [flatten_replicate_comm_mt, List.replicate_succ, List.flatten_cons]

/-! ## 残差 named Prop -/

/-- **`ExchV_M_tower` を閉じるための残差**。条件(V) ホスト `M` について、
`ExchV_M_tower` の底仮定 (`hd₀`/`hd₁`) の下で、以下の 6 事実を要求する:
* (a) `hasParent M 1 (Lng M − 1)`（Isabelle `s85b_condV_bridge(3)`）、
* (b) `s84x_jm2 M = transJ0 M`（同 `(4)`）、
* (c) `∀ n>1, Oper5Residual M n`（engine `m_8_4_oper_props_5` の各段の §7.4 支持束、
  並行 agent が閉包中）、
* (d) `Trans (Pred (s84x_Np M)) = D_e t₂`（`PredNp`；adm 枝 `m_8_5_scbdec_PredNp_condV`、
  非 adm 枝 §8.2 VE 残差）、
* (e) `Trans (s84x_Lp M) = D_e(t₂ +_B D_e 0)`（`Lpv`；同上 `_Lp_condV`）、
* (f) `L₁` の底 scb 分解の平坦形（`L1v`；`baseL = exchV_tail M 1` block、
  adm 枝 `s85b_L1_decomp_adm`、非 adm 枝は 1 段深い core）。

(d)(e)(f) は adm 枝では §7.4/§8.4 の Mark 表示から proven、非 adm 枝では §8.2
front-peel/VE 残差（`isabelle/layerB/pss_wip.thy` の `nfx_M_tower` の `PredNp`/`Lpv`/
`L1v` assumes に対応）。塔帰納段そのものは両枝一様で、本ファイルが無条件に閉じる。 -/
def ExchVMTowerResidual : Prop :=
  ∀ (M : PS) (s₀ s₁ b₀ b₁ : List Sym), STPS M → monoT M = true → transCondV M = true →
    scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
      s₀ (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b₀ →
    scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ →
    hasParent M 1 (Lng M - 1) = true ∧
    s84x_jm2 M = transJ0 M ∧
    (∀ n, 1 < n → Oper5Residual M n) ∧
    Trans (Pred (s84x_Np M)) = Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) ∧
    Trans (s84x_Lp M) = Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) ∧
    flatBT (Trans (s84x_L M 1))
      = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
          :: (List.replicate (exchV_tail M 1)
                (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ [Sym.zero]
          ++ (List.replicate (exchV_tail M 1) b₀).flatten ++ b₁

/-! ## 本体 -/

/-- **`ExchV_M_tower` の drop-in**（house pattern）。残差 `ExchVMTowerResidual` から
条件(V) の `Trans(M[k+1])` 塔閉形式を、`m_8_4_oper_props_5` engine ＋ `L`/`M` joint
帰納で無条件に得る。adm/非 adm 一様。 -/
theorem exchV_M_tower_of_residual (hres : ExchVMTowerResidual) : ExchV_M_tower := by
  intro M s₀ s₁ b₀ b₁ hST hmono hcond hd₀ hd₁ _hk₁
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, _hc₁eq, ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁ ht₁
  obtain ⟨hp, hjm2, hOper5, hPredNp, hLpv, hL1⟩ :=
    hres M s₀ s₁ b₀ b₁ hST hmono hcond hd₀ hd₁
  -- 条件(V) の算術
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  have hj1v : 1 < Lng M - 1 := by omega
  -- 名前の短縮（ℕ 値と文字列）
  set t₂ := transT2 M with ht2def
  set e := entry M 1 (transJ0 M) with hedef
  set u := entry M 1 (transJm1 M) with hudef
  set X := s₀ ++ [Sym.dsym (e : ℕ∞)] with hXdef
  -- `b₀`/`b₁` は全 `RP`
  have hb0rp : ∀ x ∈ b₀, x = Sym.rp := hd₀.2.2
  have hb1rp : ∀ x ∈ b₁, x = Sym.rp := hd₁.2.2
  have hBkrp : ∀ m : ℕ, ∀ x ∈ (List.replicate m b₀).flatten ++ b₁, x = Sym.rp := by
    intro m x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp h
      rw [List.eq_of_mem_replicate hl] at hxl
      exact hb0rp x hxl
    · exact hb1rp x h
  -- 底の平坦形の値（`flatBT (D_e 0)` / `f0` / `fLp` / `fPN`）
  have hDe0 : flatBT (Dprin (e : ℕ∞) BZero) = [Sym.dsym (e : ℕ∞), Sym.zero] := rfl
  have isPTB_De0 : isPTB_str (flatBT (Dprin (e : ℕ∞) BZero)) :=
    ⟨.db (e : ℕ∞) BZero, by simp [dfree_BP, dfree_BT, dfree_BPList, BZero], rfl⟩
  -- `hd₀` の core `D_{v₁} 0` を `D_e 0` に差し替え（`add_scb_replace_last`）
  have hv₁TB : Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero ∈ T_B := by
    apply Dprin_mem_T_B (by simp)
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hDe0TB : Dprin (e : ℕ∞) BZero ∈ T_B := by
    apply Dprin_mem_T_B (by simp)
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hsub0 : scb_decomp (addBT t₂ (Dprin (e : ℕ∞) BZero)) s₀
      (flatBT (Dprin (e : ℕ∞) BZero)) b₀ :=
    add_scb_replace_last t₂ (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
      (Dprin (e : ℕ∞) BZero) s₀ b₀ ht₂TB hv₁TB ⟨_, rfl⟩ hDe0TB ⟨_, rfl⟩ hd₀
  have hf0 : flatBT (addBT t₂ (Dprin (e : ℕ∞) BZero))
      = s₀ ++ [Sym.dsym (e : ℕ∞), Sym.zero] ++ b₀ := by
    have h := hsub0.1; rw [h, hDe0]
  have hfLp : flatBT (Trans (s84x_Lp M))
      = Sym.dsym (e : ℕ∞) :: (s₀ ++ [Sym.dsym (e : ℕ∞), Sym.zero] ++ b₀) := by
    rw [hLpv]
    show Sym.dsym (e : ℕ∞) :: flatBT (addBT t₂ (Dprin (e : ℕ∞) BZero)) = _
    rw [hf0]
  have hfPN : flatBT (Trans (Pred (s84x_Np M))) = Sym.dsym (e : ℕ∞) :: flatBT t₂ := by
    have hdp : flatBT (Dprin (e : ℕ∞) t₂) = Sym.dsym (e : ℕ∞) :: flatBT t₂ := rfl
    rw [hPredNp, hdp]
  have hM0 : flatBT (Trans (oper M 1)) = s₁ ++ Sym.dsym (u : ℕ∞) :: flatBT t₂ ++ b₁ := by
    have hdp : flatBT (Dprin (u : ℕ∞) t₂) = Sym.dsym (u : ℕ∞) :: flatBT t₂ := rfl
    rw [hd₁.1, hdp]
  -- `zeroT (Pred (s84x_Np M)) = false`
  have hNpLen : Lng (s84x_Np M) = Lng M - transJ0 M := by
    unfold s84x_Np; rw [length_seg, hjm2]; omega
  have hPredNpLen : Lng (Pred (s84x_Np M)) = Lng (s84x_Np M) - 1 :=
    length_Pred _ (by rw [hNpLen]; omega)
  have nzPredNp : ¬ (zeroT (Pred (s84x_Np M)) = true) := by
    have hge2 : 2 ≤ Lng (Pred (s84x_Np M)) := by rw [hPredNpLen, hNpLen]; omega
    intro h
    simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at h
    omega
  -- `exchV_tail` の算術
  have hMc0 : exchV_tail M 0 = 0 := by
    unfold exchV_tail
    by_cases hA : adm M (transJ0 M) = true
    · rw [if_pos hA]
    · rw [if_neg hA]; simp
  have hposE : ∀ k, 1 ≤ exchV_tail M (k + 1) := by
    intro k; unfold exchV_tail
    by_cases hA : adm M (transJ0 M) = true
    · rw [if_pos hA]; omega
    · rw [if_neg hA, if_neg (show ¬(k + 1 = 0) by omega)]; omega
  have hsuccE : ∀ k, exchV_tail M (k + 2) = exchV_tail M (k + 1) + 1 := by
    intro k; unfold exchV_tail
    by_cases hA : adm M (transJ0 M) = true
    · rw [if_pos hA, if_pos hA]
    · rw [if_neg hA, if_neg hA, if_neg (show ¬(k + 2 = 0) by omega),
          if_neg (show ¬(k + 1 = 0) by omega)]
  -- 文字列 combine 補題
  have snocX' : ∀ (m : ℕ) (rest : List Sym),
      (List.replicate m X).flatten ++ (s₀ ++ (Sym.dsym (e : ℕ∞) :: rest))
        = (List.replicate (m + 1) X).flatten ++ rest := by
    intro m rest
    have h1 : s₀ ++ (Sym.dsym (e : ℕ∞) :: rest) = X ++ rest := by
      rw [hXdef]; simp
    rw [h1, ← List.append_assoc, flatten_replicate_snoc_mt]
  have consB' : ∀ (m : ℕ) (rest : List Sym),
      b₀ ++ ((List.replicate m b₀).flatten ++ rest)
        = (List.replicate (m + 1) b₀).flatten ++ rest := by
    intro m rest
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
  -- pure 文字列代数（`L` step / `M` step / flat split）
  have Lstr : ∀ q : ℕ,
      (s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate q X).flatten ++ s₀)
        ++ (Sym.dsym (e : ℕ∞) :: (s₀ ++ [Sym.dsym (e : ℕ∞), Sym.zero] ++ b₀))
        ++ ((List.replicate (q + 1) b₀).flatten ++ b₁)
      = s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate (q + 2) X).flatten
          ++ [Sym.zero] ++ (List.replicate (q + 2) b₀).flatten ++ b₁ := by
    intro q
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [snocX', snocX', consB']
  have Mstr : ∀ q : ℕ,
      (s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate q X).flatten ++ s₀)
        ++ (Sym.dsym (e : ℕ∞) :: flatBT t₂)
        ++ ((List.replicate (q + 1) b₀).flatten ++ b₁)
      = s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate (q + 1) X).flatten
          ++ flatBT t₂ ++ (List.replicate (q + 1) b₀).flatten ++ b₁ := by
    intro q
    simp only [List.append_assoc, List.cons_append]
    rw [snocX']
  have splitL : ∀ q : ℕ,
      (s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate q X).flatten ++ s₀)
        ++ [Sym.dsym (e : ℕ∞), Sym.zero]
        ++ ((List.replicate (q + 1) b₀).flatten ++ b₁)
      = s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate (q + 1) X).flatten
          ++ [Sym.zero] ++ (List.replicate (q + 1) b₀).flatten ++ b₁ := by
    intro q
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [snocX']
  -- engine（`m_8_4_oper_props_5`）を各段で呼ぶ
  have engine : ∀ n, 1 < n → ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_L M (n - 1))) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2
        ∧ scb_decomp (Trans (s84x_L M n)) sb.1 (flatBT (Trans (s84x_Lp M))) sb.2
        ∧ (¬ (zeroT (Pred (s84x_Np M)) = true) →
             scb_decomp (Trans (oper M n)) sb.1
               (flatBT (Trans (Pred (s84x_Np M)))) sb.2) := by
    intro n hn
    exact m_8_4_oper_props_5 M n hST hmono hp hj1v hn
      (oper5Support_holds M n hST hmono hp hj1v hn (hOper5 n hn))
  -- joint 帰納
  have main : ∀ k,
      flatBT (Trans (s84x_L M (k + 1)))
        = s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate (exchV_tail M (k + 1)) X).flatten
            ++ [Sym.zero] ++ (List.replicate (exchV_tail M (k + 1)) b₀).flatten ++ b₁
      ∧ flatBT (Trans (oper M (k + 1)))
        = s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate (exchV_tail M k) X).flatten
            ++ flatBT t₂ ++ (List.replicate (exchV_tail M k) b₀).flatten ++ b₁ := by
    intro k
    induction k with
    | zero =>
        refine ⟨hL1, ?_⟩
        rw [hMc0]
        simpa using hM0
    | succ k ih =>
        obtain ⟨ihL, _ihM⟩ := ih
        obtain ⟨q, hq⟩ : ∃ q, exchV_tail M (k + 1) = q + 1 :=
          ⟨exchV_tail M (k + 1) - 1, by have := hposE k; omega⟩
        rw [hq] at ihL
        -- flatk: `L(k)` を `(Sk, Bk)` の scb 分解へ
        have flatk : flatBT (Trans (s84x_L M (k + 1)))
            = (s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate q X).flatten ++ s₀)
              ++ flatBT (Dprin (e : ℕ∞) BZero)
              ++ ((List.replicate (q + 1) b₀).flatten ++ b₁) := by
          rw [ihL, hDe0]; exact (splitL q).symm
        have wk : scb_decomp (Trans (s84x_L M (k + 1)))
            (s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate q X).flatten ++ s₀)
            (flatBT (Dprin (e : ℕ∞) BZero))
            ((List.replicate (q + 1) b₀).flatten ++ b₁) :=
          ⟨flatk, fun _ => isPTB_De0, hBkrp (q + 1)⟩
        -- engine at `n = k+2`
        obtain ⟨sb, ⟨hP1, hP2, hP3⟩, _hU⟩ := engine (k + 2) (by omega)
        have hP1' : scb_decomp (Trans (s84x_L M (k + 1))) sb.1
            (flatBT (Dprin (e : ℕ∞) BZero)) sb.2 := by
          rw [hjm2] at hP1; exact hP1
        obtain ⟨hpinS, hpinB⟩ := scb_unique_decomp_unconditional
          (Trans (s84x_L M (k + 1))) sb.1
          (s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate q X).flatten ++ s₀)
          (flatBT (Dprin (e : ℕ∞) BZero))
          sb.2 ((List.replicate (q + 1) b₀).flatten ++ b₁) hP1' wk
        rw [hpinS, hpinB] at hP2
        have hM2 := hP3 nzPredNp
        rw [hpinS, hpinB] at hM2
        refine ⟨?_, ?_⟩
        · -- L-part(k+1)
          show flatBT (Trans (s84x_L M (k + 2)))
              = s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate (exchV_tail M (k + 2)) X).flatten
                  ++ [Sym.zero] ++ (List.replicate (exchV_tail M (k + 2)) b₀).flatten ++ b₁
          rw [hP2.1, hfLp, show exchV_tail M (k + 2) = q + 2 from by rw [hsuccE k, hq]]
          exact Lstr q
        · -- M-part(k+1)
          show flatBT (Trans (oper M (k + 2)))
              = s₁ ++ Sym.dsym (u : ℕ∞) :: (List.replicate (exchV_tail M (k + 1)) X).flatten
                  ++ flatBT t₂ ++ (List.replicate (exchV_tail M (k + 1)) b₀).flatten ++ b₁
          rw [hM2.1, hfPN, hq]
          exact Mstr q
  intro k
  exact (main k).2

#print axioms exchV_M_tower_of_residual

end PSS
