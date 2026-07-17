import «8».«8.5-exchV-props»

/-!
# §8.5 exchV 残差の統合（`ExchVres_adm_M_tower` ＋ `ExchVres_nadm_M_tower` → 1 本）

- 原文: `tmp/content.md` §8.5「命題（条件(V)の下での Trans と基本列の交換関係）」
  および「補題（条件(V)の下での各種scb分解）」(5213)。
- 対象: ビルド済み «8».«8.5-exchV-props» が残した **2 本**の named Prop
  `ExchVres_adm_M_tower` / `ExchVres_nadm_M_tower`（どちらも
  `Trans(M[k+1])` の塔の閉形式）。本ファイルはこの 2 本を、**単一の**
  named Prop `ExchV_M_tower` に統合する（house pattern: 定理の型が Prop
  そのもの＝drop-in が elaborator により保証される）。

  | Prop | 本ファイル | 状態 |
  |---|---|---|
  | `ExchVres_adm_M_tower` | `exchVres_adm_M_tower_of_M_tower` | ⚠️ `ExchV_M_tower` 上 |
  | `ExchVres_nadm_M_tower` | `exchVres_nadm_M_tower_of_M_tower` | ⚠️ `ExchV_M_tower` 上 |
  | `ExchV_scbdec_adm_forms` | `adm_forms_holds_xv2` | ⚠️ `ExchV_M_tower` 上 |
  | `ExchV_nf3x` | `nf3x_holds_xv2` | ⚠️ `ExchV_M_tower` 上 |

  ＝**exchV の 6 本の named Prop は、これで残差 `ExchV_M_tower` ただ 1 本**
  （4 本は «8».«8.5-exchV-props» が無条件に閉じ済み）。

- Isabelle（設計図）:
  - adm 枝の塔 = `m_8_5_scbdec_adm_forms` 結論 (5) (isabelle/layerB/pss_wip.thy:57556)
  - 非 adm 枝の塔 = `nfx_M_tower` (同 :64348)（`atx_nf3x` (:86273) の結論 (1)）
  - 両者の共有エンジン = `m_8_4_oper_props_5` (同 :54005) ＋ `s84x_L` 塔帰納
  - 文字列代数 = `s85b_W_flat` (同 :58014) / `nfx_rot_s0` (同 :64198) /
    `nfx_bodyM_flat` (同 :64228)

## ⚠️ 中核の発見: adm 枝と非 adm 枝の塔は **添字が 1 ずれる**（統合は「仮定の弱化」ではできない）

`ExchVres_nadm_M_tower` は `ExchVres_adm_M_tower` から `adm = false` の仮定を
落としたものでは **ない**。両者の結論は別の文字列である。実際、
`X = s₀ ++ [D_{M₁,j₀}]` として

* adm 枝  (`m_8_5_scbdec_adm_forms`(5)): `Trans(M[k+1])` の core 内部 = `X^k t₂ b₀^k`
* 非 adm 枝 (`nfx_M_tower`):             同 = `flatBT (e5x_bodyM t₂ e k)`

であり、本ファイルの `bodyM_flat_succ_xv2` が示すとおり
`flatBT (e5x_bodyM t₂ e (j+1)) = X^{j+2} t₂ b₀^{j+2}`（`k = 0` では `t₂`）。
すなわち **非 adm 枝の指数は adm 枝より 1 大きい**（原文の `mₙ = n-1` / `n` の
ずれ、`isabelle/memo.md`:130 と整合）。Isabelle 側でも `nfx_M_tower` の仮定 `L1v`
（core `D_u(t₂ +_B D_e(t₂ +_B D_e 0))`）は adm 枝の `s85b_L1_decomp_adm`
（core `D_e(t₂ +_B D_e 0)`）と 1 段違い＝adm 枝では `L1v` は偽である。

**数値検証**（`python/audit_85_exchV_towers.py`、`diagSeq` を `oper` で閉じた
本物の標準形プール）。独立に組んだ 2 つのプールが一致した:
(A) 本スクリプトの既定値（＋行 0 祖先スライスの `Red` ＋ `Pred` 閉包）= 8094 形 →
adm 条件(V) ホスト 28 件、(B) より深い `oper` 閉包（gens=5, lenCap=16）= 5780 形 →
同 80 件。

* `ExchVres_adm_M_tower` の結論: **28/28（A）・80/80（B）で成立、反例 0**
  （`k = 0..3`）＝この残差は **真かつ非空虚**。
* 同じホストで **非 adm 枝の式は 28/28・80/80 で偽** ＝ 上記の 1 ずれは実在する。
* 非 adm ホストはどちらのプールにも現れない（`isabelle/memo.md` の
  「r16-E1 が `Lng ≥ 9` の実例を確認」と整合）。すなわち
  **`ExchVres_nadm_M_tower` は経験的に未検証**（本ファイルの非 adm 側の統合は
  Isabelle `nfx_M_tower` の逐語移植としてのみ担保されている）。

そこで本ファイルは、両枝を **指数関数 `exchV_tail` で切り替える単一の塔**として
述べ直す。`exchV_tail M k = k`（adm）/ `= if k = 0 then 0 else k+1`（非 adm）。
これは仮定の弱化ではなく、両枝の結論を 1 つの文字列式にまとめる正当な統合であり、
非 adm 側の橋渡し（`e5x_bodyM` 言語 ⟷ `replicate` 言語）が本ファイルの実質である。

## 構造

- `s85b_W_flat_xv2` … `s85b_W` 塔の flat 形（Isabelle `s85b_W_flat` :58014）。
  «8».«8.5-exchV-props» の同名 private 補題の再証明（private ゆえ再利用不可）。
- `bodyM_flat_succ_xv2` … `nfx_bodyM_flat` (:64228)。回転 `rot_s0_xv2`
  （= `nfx_rot_s0` :64198）＋ `replicate` の snoc。
- 非 adm 側の `(s₀,b₀)` の生成は `add_scb_marked`（= Isabelle
  `m_7_2_add_scb_conj1`）＋ `MarkedB` の展開で無条件に得る
  （`ExchVres_nadm_M_tower` は `(s₀,b₀)` を仮定に持たないため、ここが必要）。
  Isabelle は `m_8_5_TransCondV_producer` (:38761) を使うが、Lean 側では
  `add_scb_marked` 一発で足りる（core が principal なので producer 不要）。

- 依存（すべてビルド済み）: «8».«8.5-exchV-props»（`ExchVres_*` の Prop 本体・
  `condV_setup_holds` / `c1_shape_holds` / `adm_forms_holds` / `nf3x_holds`、
  推移的に «8».«8.5-Trans-fseq-condV» = `s85b_W` / `e5x_bodyM`、
  «7».«7.2-add-scb» = `add_scb_marked` / `add_scb_replace_last` / `addBT_mem_T_B`、
  «7».«7.3-Trans-welldefined» = `Dprin_mem_T_B`、«6».«6.7-standard-reduced»
  = `STPS_RTPS`、«6».«6.7-standard-prefix» = `STPS_TPS`）。
  ⚠️«8».«8.5-scb-decompositions»（本ラウンドで別エージェントが執筆中）は
  **import しない**。
- 訂正: なし（A28 は取り下げ済み、`corrections-old.md`:95）。
- 状態: GREEN（sorry 0）。exchV の残差 **2 本 → 1 本**。
  残る `ExchV_M_tower` は **§8.4 の `s84x_L` 塔クラスタ**
  （`m_8_4_oper_props_5` :54005 ＋ `s84x_L`/`s84x_Np`/`s84x_Lp` ＋
  adm/非 adm それぞれの 3 スライス値）の Lean 未移植分そのもので、
  «8».«8.6-Trans-fseq-condVI» の `CondVIAdmTowerScb`（Isabelle `c6zx_L_tower`
  :72166 経由）と **同じ単一の欠落**である（`needs` 参照）。
-/

namespace PSS

/-! ## 塔の指数（adm 枝と非 adm 枝の 1 ずれ） -/

/-- `Trans(M[k+1])` の core 内部に現れる `X = s₀ ++ [D_{M₁,j₀}]` の反復回数。
adm 枝では `k`、非 adm 枝では `k = 0` を除いて `k + 1`（原文の `mₙ` のずれ）。 -/
def exchV_tail (M : PS) (k : ℕ) : ℕ :=
  if adm M (transJ0 M) = true then k else (if k = 0 then 0 else k + 1)

/-- **exchV の唯一の残差**: 条件(V) ホストにおける `Trans(M[k+1])` の塔の閉形式。

Isabelle では adm 枝 = `m_8_5_scbdec_adm_forms` 結論 (5) (pss_wip.thy:57556)、
非 adm 枝 = `nfx_M_tower` (同 :64348) の 2 本に分かれるが、どちらも
`m_8_4_oper_props_5` (同 :54005) ＋ `s84x_L` 塔帰納という**同一のエンジン**に
乗っており、結論の差は指数の 1 ずれ（`exchV_tail`）だけである。 -/
def ExchV_M_tower : Prop :=
  ∀ (M : PS) (s₀ s₁ b₀ b₁ : List Sym), STPS M → monoT M = true →
    transCondV M = true →
    scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
      s₀ (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b₀ →
    scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ →
    scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ →
    (∀ k : ℕ, flatBT (Trans (oper M (k + 1)))
        = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
            :: (List.replicate (exchV_tail M k)
                  (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
            ++ flatBT (transT2 M)
            ++ (List.replicate (exchV_tail M k) b₀).flatten ++ b₁)

/-! ## 文字列代数（Isabelle `s85b_W_flat` :58014 / `nfx_rot_s0` :64198 の再証明）

«8».«8.5-exchV-props» の同内容の補題はすべて `private` なので再利用できない。
証明は同一（サフィックス `_xv2`）。 -/

private theorem s85b_W_principal_xv2 (u : ℕ) (t c : BT) (k : ℕ) :
    ∃ b, s85b_W u t c k = Dprin (u : ℕ∞) b := by
  cases k with
  | zero => exact ⟨c, rfl⟩
  | succ j => exact ⟨addBT t (s85b_W u t c j), rfl⟩

private theorem s85b_W_mem_T_B_xv2 {u : ℕ} {t c : BT} (ht : t ∈ T_B) (hc : c ∈ T_B)
    (k : ℕ) : s85b_W u t c k ∈ T_B := by
  induction k with
  | zero => exact Dprin_mem_T_B (by simp) hc
  | succ j ih => exact Dprin_mem_T_B (by simp) (addBT_mem_T_B ht ih)

private theorem flatten_replicate_comm_xv2 {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = b ++ (List.replicate j b).flatten := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

private theorem flatten_replicate_snoc_xv2 {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = (List.replicate (j + 1) b).flatten := by
  rw [flatten_replicate_comm_xv2, List.replicate_succ, List.flatten_cons]

/-- Isabelle `nfx_rot_s0` (pss_wip.thy:64198)。 -/
private theorem rot_s0_xv2 (s₀ : List Sym) (d : Sym) (j : ℕ) :
    s₀ ++ (List.replicate j (d :: s₀)).flatten
      = (List.replicate j (s₀ ++ [d])).flatten ++ s₀ := by
  induction j with
  | zero => simp
  | succ i ih =>
      calc s₀ ++ (List.replicate (i + 1) (d :: s₀)).flatten
          = (s₀ ++ [d]) ++ (s₀ ++ (List.replicate i (d :: s₀)).flatten) := by
            simp [List.replicate_succ, List.append_assoc]
        _ = (s₀ ++ [d]) ++ ((List.replicate i (s₀ ++ [d])).flatten ++ s₀) := by
            rw [ih]
        _ = (List.replicate (i + 1) (s₀ ++ [d])).flatten ++ s₀ := by
            simp [List.replicate_succ, List.append_assoc]

/-- Isabelle `s85b_W_flat` (pss_wip.thy:58014)。 -/
private theorem s85b_W_flat_xv2 {u : ℕ} {t c0 c : BT} {s₀ b₀ : List Sym}
    (htTB : t ∈ T_B) (hc0TB : c0 ∈ T_B) (hc0p : ∃ p, c0 = .trm [p])
    (hinner : scb_decomp (addBT t c0) s₀ (flatBT c0) b₀)
    (hcTB : c ∈ T_B) (k : ℕ) :
    flatBT (s85b_W u t c k)
      = (List.replicate k (Sym.dsym (u : ℕ∞) :: s₀)).flatten
        ++ flatBT (Dprin (u : ℕ∞) c) ++ (List.replicate k b₀).flatten := by
  induction k with
  | zero => simp [s85b_W]
  | succ j ih =>
      have hWTB : s85b_W u t c j ∈ T_B := s85b_W_mem_T_B_xv2 htTB hcTB j
      have hWp : ∃ p, s85b_W u t c j = BT.trm [p] := by
        obtain ⟨b, hb⟩ := s85b_W_principal_xv2 u t c j
        exact ⟨.db (u : ℕ∞) b, by simpa [Dprin] using hb⟩
      have hsub : scb_decomp (addBT t (s85b_W u t c j)) s₀
          (flatBT (s85b_W u t c j)) b₀ :=
        add_scb_replace_last t c0 (s85b_W u t c j) s₀ b₀ htTB hc0TB hc0p hWTB hWp hinner
      have hfsub : flatBT (addBT t (s85b_W u t c j))
          = s₀ ++ flatBT (s85b_W u t c j) ++ b₀ := hsub.1
      have hstep : flatBT (s85b_W u t c (j + 1))
          = Sym.dsym (u : ℕ∞) :: flatBT (addBT t (s85b_W u t c j)) := by
        simp [s85b_W, Dprin, flatBT, flatBP]
      rw [hstep, hfsub, ih]
      simp only [List.replicate_succ, List.flatten_cons, List.append_assoc,
        List.cons_append]
      rw [flatten_replicate_comm_xv2 b₀ j]

/-! ## `e5x_bodyM` 言語 ⟷ `replicate` 言語（Isabelle `nfx_bodyM_flat` :64228） -/

/-- **非 adm 枝の core 内部の flat 形**。`k = j+1` では `X = s₀ ++ [D_e]` の
反復回数が **`j + 2`**（＝`k + 1`）になる — これが adm 枝との 1 ずれの正体。 -/
private theorem bodyM_flat_succ_xv2 {t₂ : BT} {e v₁ : ℕ} {s₀ b₀ : List Sym}
    (ht₂ : t₂ ∈ T_B)
    (hinner : scb_decomp (addBT t₂ (Dprin (v₁ : ℕ∞) BZero)) s₀
      (flatBT (Dprin (v₁ : ℕ∞) BZero)) b₀) (j : ℕ) :
    flatBT (e5x_bodyM t₂ e (j + 1))
      = (List.replicate (j + 2) (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten
        ++ flatBT t₂ ++ (List.replicate (j + 2) b₀).flatten := by
  have hc0TB : Dprin (v₁ : ℕ∞) BZero ∈ T_B := by
    apply Dprin_mem_T_B (by simp)
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  -- `W = s85b_W e t₂ t₂ (j+1)` の flat 形（種 `t₂`）
  have hWflat := s85b_W_flat_xv2 (u := e) (t := t₂) (c0 := Dprin (v₁ : ℕ∞) BZero)
    (c := t₂) (s₀ := s₀) (b₀ := b₀) ht₂ hc0TB ⟨_, rfl⟩ hinner ht₂ (j + 1)
  -- 外側の `t₂ +_B W` を `add_scb_replace_last` で剥がす
  have hWTB : s85b_W e t₂ t₂ (j + 1) ∈ T_B := s85b_W_mem_T_B_xv2 ht₂ ht₂ (j + 1)
  have hWp : ∃ p, s85b_W e t₂ t₂ (j + 1) = BT.trm [p] := by
    obtain ⟨b, hb⟩ := s85b_W_principal_xv2 e t₂ t₂ (j + 1)
    exact ⟨.db (e : ℕ∞) b, by simpa [Dprin] using hb⟩
  have haddf : scb_decomp (addBT t₂ (s85b_W e t₂ t₂ (j + 1))) s₀
      (flatBT (s85b_W e t₂ t₂ (j + 1))) b₀ :=
    add_scb_replace_last t₂ (Dprin (v₁ : ℕ∞) BZero) (s85b_W e t₂ t₂ (j + 1)) s₀ b₀
      ht₂ hc0TB ⟨_, rfl⟩ hWTB hWp hinner
  have hbody : flatBT (e5x_bodyM t₂ e (j + 1))
      = s₀ ++ flatBT (s85b_W e t₂ t₂ (j + 1)) ++ b₀ := by
    have : e5x_bodyM t₂ e (j + 1) = addBT t₂ (s85b_W e t₂ t₂ (j + 1)) := rfl
    rw [this]
    exact haddf.1
  rw [hbody, hWflat]
  have hDe : flatBT (Dprin (e : ℕ∞) t₂) = Sym.dsym (e : ℕ∞) :: flatBT t₂ := by
    simp [Dprin, flatBT, flatBP]
  rw [hDe]
  -- 文字列代数: 回転 ＋ replicate の snoc
  have hrot : s₀ ++ (List.replicate (j + 1) (Sym.dsym (e : ℕ∞) :: s₀)).flatten
      = (List.replicate (j + 1) (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten ++ s₀ :=
    rot_s0_xv2 s₀ (Sym.dsym (e : ℕ∞)) (j + 1)
  calc s₀ ++ ((List.replicate (j + 1) (Sym.dsym (e : ℕ∞) :: s₀)).flatten
          ++ (Sym.dsym (e : ℕ∞) :: flatBT t₂)
          ++ (List.replicate (j + 1) b₀).flatten) ++ b₀
      = (s₀ ++ (List.replicate (j + 1) (Sym.dsym (e : ℕ∞) :: s₀)).flatten)
          ++ [Sym.dsym (e : ℕ∞)] ++ flatBT t₂
          ++ ((List.replicate (j + 1) b₀).flatten ++ b₀) := by
        simp [List.append_assoc]
    _ = ((List.replicate (j + 1) (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten ++ s₀)
          ++ [Sym.dsym (e : ℕ∞)] ++ flatBT t₂
          ++ ((List.replicate (j + 1) b₀).flatten ++ b₀) := by rw [hrot]
    _ = ((List.replicate (j + 1) (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten
          ++ (s₀ ++ [Sym.dsym (e : ℕ∞)])) ++ flatBT t₂
          ++ ((List.replicate (j + 1) b₀).flatten ++ b₀) := by
        simp [List.append_assoc]
    _ = (List.replicate (j + 2) (s₀ ++ [Sym.dsym (e : ℕ∞)])).flatten
          ++ flatBT t₂ ++ (List.replicate (j + 2) b₀).flatten := by
        rw [flatten_replicate_snoc_xv2, flatten_replicate_snoc_xv2]

/-! ## `ExchVres_adm_M_tower` の統合（`exchV_tail = k`） -/

/-- 許容枝では第 2 基点が潰れる（Isabelle `s85b_jm1_adm`, pss_wip.thy:57138）。 -/
private theorem jm1_adm_xv2 {M : PS} (h : adm M (transJ0 M) = true) :
    transJm1 M = transJ0 M := by
  simp [transJm1, Adm, h]

theorem exchVres_adm_M_tower_of_M_tower (h : ExchV_M_tower) : ExchVres_adm_M_tower := by
  intro M s₀ s₁ b₀ b₁ hST hmono hcond hadm hd₀ hd₁ hk₁ k
  have hjm1 : transJm1 M = transJ0 M := jm1_adm_xv2 hadm
  have hd₁' : scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ := by
    rw [hjm1]; exact hd₁
  have htower := h M s₀ s₁ b₀ b₁ hST hmono hcond hd₀ hd₁' hk₁ k
  have htail : exchV_tail M k = k := by simp [exchV_tail, hadm]
  rw [htower, htail, hjm1]

/-! ## `ExchVres_nadm_M_tower` の統合（`exchV_tail = k+1`、`k = 0` は `0`） -/

theorem exchVres_nadm_M_tower_of_M_tower (h : ExchV_M_tower) :
    ExchVres_nadm_M_tower := by
  intro M s₁ b₁ hST hmono hcond hnadm hd1h hk1h
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨_hV, _hc₁eq, ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁ ht₁
  -- `transJ0 M = parent M 0 (Lng M - 1)` なので非 adm 仮定は `exchV_tail` の枝を決める
  have hnadm' : adm M (transJ0 M) = false := by
    simpa [transJ0, lastParent, lastIdx] using hnadm
  -- 内側の対 `(s₀,b₀)` を `add_scb_marked` から無条件に生成する
  have hDv₁ : Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero ∈ T_B := by
    apply Dprin_mem_T_B (by simp)
    simp [T_B, BZero, dfree_BT, dfree_BPList]
  obtain ⟨s₀, b₀, hd₀⟩ :=
    add_scb_marked (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)
      ht₂TB hDv₁ ⟨_, rfl⟩
  have htower := h M s₀ s₁ b₀ b₁ hST hmono hcond hd₀ hd1h hk1h
  intro k
  rw [htower]
  cases k with
  | zero =>
      have htail : exchV_tail M 0 = 0 := by simp [exchV_tail, hnadm']
      rw [htail]
      simp [e5x_bodyM, flatBP]
  | succ j =>
      have htail : exchV_tail M (j + 1) = j + 2 := by
        simp [exchV_tail, hnadm']
      rw [htail]
      rw [show flatBP (BP.db (entry M 1 (transJm1 M) : ℕ∞)
              (e5x_bodyM (transT2 M) (entry M 1 (transJ0 M)) (j + 1)))
            = Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
              :: flatBT (e5x_bodyM (transT2 M) (entry M 1 (transJ0 M)) (j + 1)) from
          by simp [flatBP]]
      rw [bodyM_flat_succ_xv2 (t₂ := transT2 M) (e := entry M 1 (transJ0 M))
        (v₁ := entry M 1 (transJ1 M)) (s₀ := s₀) (b₀ := b₀) ht₂TB hd₀ j]
      simp [List.append_assoc]

/-! ## `ExchV_*` の drop-in（house pattern） -/

theorem adm_forms_holds_xv2 (h : ExchV_M_tower) : ExchV_scbdec_adm_forms :=
  adm_forms_holds (exchVres_adm_M_tower_of_M_tower h)

theorem nf3x_holds_xv2 (h : ExchV_M_tower) : ExchV_nf3x :=
  nf3x_holds (exchVres_nadm_M_tower_of_M_tower h)

#print axioms exchVres_adm_M_tower_of_M_tower
#print axioms exchVres_nadm_M_tower_of_M_tower
#print axioms adm_forms_holds_xv2
#print axioms nf3x_holds_xv2

end PSS
