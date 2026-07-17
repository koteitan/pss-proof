import «6».«6.7-standard-reduced»
import «6».«6.7-standard-prefix»
import «7».«7.1-lessBT-linear-order»
import «7».«7.1-buchholz-fseq-lt»
import «7».«7.2-add-scb»
import «7».«7.3-c1-c2-order»
import «7».«7.3-Pred-Trans-descend»

/-!
# §8.5 命題（条件 (V) の下での `Trans` と基本列の交換関係）

- 原文: `tmp/content.md` §8.5「命題（条件(V)の下での Trans と基本列の交換関係）」。
- 逐語: `p_8_5_Trans_oper_exchange` (isabelle/pss_paper.thy:2070)。
- 訂正: **なし（A28 は取り下げ済み、`corrections-old.md`:95）**。訂正 A23 後の
  正しい Buchholz 基本列の下では、**adm 枝では原文の添字 `mₙ = n - 1` のまま
  (1)(2)(3) の三結論がすべて成立する**（しかも `≤` ではなく `<` で厳密）。
  塔は `Trans(M[n]) < Trans(M)[n-1] < Trans(M[n+1])` と厳密に交互配置される
  （core は `s85b_W e t₂ t₂ (n-1)` / `s85b_W e t₂ 0_B n` / `s85b_W e t₂ t₂ n`、
  比較は順に `e5x_W_seed_shift` / `s85b_W_mono_seed`）。
  ⚠️Isabelle の `m_8_5_Trans_oper_exchange_condV_adm_uncond` は (1) を添字 `n`
  で述べる（＝原文添字 `n-1` 版の弱系）。本ファイルは両方を出す
  （`Trans_oper_exchange_condV_adm_uncond` の conj (1) が原文添字、conj (2) が
  Isabelle 添字）。
  **非 adm 枝**（`ST_PS` で到達可能、Isabelle r16-E1 が `Lng ≥ 9` の実例を確認）
  については、Isabelle が証明したのは添字 `n + 1` の形
  （`atx_Trans_oper_exchange_condV_nonadm_uncond`）であり、原文の添字 `mₙ = n`
  の形は**移植していない**。したがって忠実版 `Trans_oper_exchange_condV` は
  **adm 枝限定**で述べる（非 adm 枝の原文添字の真偽判定は本ファイルの scope 外
  ——`needs` 参照）。`FseqDesc_exchV` 形（`∃ k`）は**全 host 無条件**。
- Isabelle（設計図）:
  - `m_8_5_Trans_oper_exchange_condV_adm` (layerB/pss_wip.thy:58346)
  - `m_8_5_Trans_oper_exchange_condV_adm_uncond` (同 60884)
  - `m_8_5_Trans_oper_exchange_condV_nonadm` (同 61656)
  - `atx_Trans_oper_exchange_condV_nonadm_uncond` (同 86315)
  - 部品: `s85b_W` (58002) / `e5x_bodyM` (61534) / `e5x_bodyO` (61541) /
    `s85b_W_flat` (58014) / `s85b_W_mono_seed` (58050) / `s85b_W_lt_top` (58062) /
    `e5x_W_lt_Dpt` (61547) / `e5x_W_seed_shift` (61562) / `e5x_W_height_mono0` (61580) /
    `e5x_bodyM_lt_c2` (61597) / `e5x_bodyM_lt_bodyO` (61615) /
    `m_8_5_scbdec_exchange1_condV_adm` (57964) / `m_8_5_scbdec_exchange2_condV_adm` (58086) /
    `m_8_5_scbdec_prev_lt_M_condV_adm` (58168) / `m_8_5_scbdec_exchange3_strict_condV_adm` (58322)
  - green-modulo に残した brick（5 本）: `m_8_5_scbdec_adm_forms` (57556) /
    `m_8_5_scbdec_fseq_condV` (51466、(2)(3) 連言のみ) /
    `m_8_5_scbdec_c1_shape` (51286) / `s85b_condV_setup` (57120) /
    `m_8_5_scbdec_t2_nonzero_condV` (57150) / `atx_nf3x` (86273)
  - `m_8_5_condV_uv` (38509) は不要になった（`e < v₁` は `transCondV` の直読み
    `condV_ev_e5` で足りる）。`m_8_5_condV_adm_t2_components` (60690) /
    `s85b_complb_lessBT` も不要（Isabelle の HB 残差は
    `m_8_5_scbdec_prev_lt_M_condV_adm` により既に消えている）。
  - ⚰️`bpHeadT(Trans(slice@B)) = C(bpHeadT(Trans slice))` の surgery-spine keystone
    subtree は **SUPERSEDED**（isabelle/memo.md:132）。原典 route (scbdec) が
    交換命題を閉じたため obsolete。13 の死路（spinelaw-universal / leaf-fold /
    entry1 / d_M=1 / standalone-endpoint / re-deposit …）も同様に再走禁止。
- 依存: `7.3-Pred-Trans-descend` (`scbext_lessBT`)、`7.3-c1-c2-order`
  (`lessBT_addBT_self`)、`7.1-buchholz-fseq-lt` (`addBT_lt_right_bf`)、
  `7.1-lessBT-linear-order` (`lessBT_linear_trans`)、`7.2-add-scb`
  (`add_scb_replace_last` ＝ Isabelle `m_7_2_add_scb_conj2`、`addBT_mem_T_B`)、
  `7.3-Trans-welldefined` (`Dprin_mem_T_B`)、`6.7-standard-reduced` (`STPS_RTPS`)。
- ツリー項目: **交換則 1/7**。`8.7-fseq-descend.lean` の `FseqDesc_exchV` を
  `exchV_holds` が**そのままの形で**満たす（drop-in）。
- 状態: GREEN（sorry 0）、下記 6 本の named Prop 上の green-modulo。
  塔の閉形式（Isabelle の `m_8_5_scbdec_adm_forms` / `atx_nf3x`）だけを仮定し、
  そこから先の順序論法（`s85b_W` 塔の 5 つの比較 ＋ 部分表現の不等式の延長性
  `scbext_lessBT`）と、adm 塔形の `s85b_W` 言語への読み替え（Isabelle の
  `s85b_W_flat` ＋ 回転）は**すべて本ファイルで証明**している。
-/

namespace PSS

/-! ## 塔 `s85b_W` と内部 body（Isabelle 58002 / 61534 / 61541 の逐語） -/

/-- Isabelle `s85b_W`: `W₀ = D_u c`、`W_{k+1} = D_u(t +_B W_k)`。 -/
def s85b_W (u : ℕ) (t c : BT) : ℕ → BT
  | 0 => Dprin (u : ℕ∞) c
  | k + 1 => Dprin (u : ℕ∞) (addBT t (s85b_W u t c k))

/-- Isabelle `e5x_bodyM`: `Trans (M[k+1])` の core `D_u(·)` の内側。 -/
def e5x_bodyM (t : BT) (e : ℕ) : ℕ → BT
  | 0 => t
  | j + 1 => addBT t (s85b_W e t t (j + 1))

/-- Isabelle `e5x_bodyO`: `operB (Trans M) (numBT n)` の core `D_u(·)` の内側。 -/
def e5x_bodyO (t : BT) (e n : ℕ) : BT := addBT t (s85b_W e t BZero n)

/-! ## 未移植 brick（Isabelle 名 1:1、GREEN-MODULO の仮定） -/

/-- Isabelle `m_8_5_scbdec_c1_shape` (pss_wip.thy:51286)。 -/
def ExchV_scbdec_c1_shape : Prop :=
  ∀ M : PS, RTPS M → TPS M → monoT M = true → 0 < transJ1 M → transT1 M ≠ BZero →
    transV M = (entry M 1 (transJm1 M) : ℕ∞) ∧
      transC1 M = Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M) ∧
      transT2 M ∈ T_B ∧
      transJm1 M < Lng M - 1

/-- Isabelle `s85b_condV_setup` (pss_wip.thy:57120)。 -/
def ExchV_condV_setup : Prop :=
  ∀ M : PS, RTPS M → TPS M → monoT M = true → transCondV M = true →
    0 < transJ1 M ∧ transT1 M ≠ BZero

/-- Isabelle `m_8_5_scbdec_t2_nonzero_condV` (pss_wip.thy:57150)。 -/
def ExchV_t2_nonzero_condV : Prop :=
  ∀ M : PS, RTPS M → TPS M → monoT M = true → transCondV M = true →
    transT2 M ≠ BZero

/-- Isabelle `m_8_5_scbdec_adm_forms` (pss_wip.thy:57556)。adm 枝の塔の閉形式
（flat 文字列レベル、`concat (replicate …)` 形の逐語）。 -/
def ExchV_scbdec_adm_forms : Prop :=
  ∀ M : PS, STPS M → monoT M = true → transCondV M = true →
    adm M (transJ0 M) = true →
    ∃ s₀ s₁ b₀ b₁ : List Sym,
      scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
        s₀ (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b₀ ∧
      scb_decomp (Trans (oper M 1)) s₁
        (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) (transT2 M))) b₁ ∧
      scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ ∧
      (∀ n : ℕ, flatBT (operB (Trans M) (numBT n)) =
        s₁ ++ Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
          (List.replicate (n + 1)
              (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ [Sym.zero]
          ++ (List.replicate (n + 1) b₀).flatten ++ b₁) ∧
      (∀ k : ℕ, flatBT (Trans (oper M (k + 1))) =
        s₁ ++ Sym.dsym (entry M 1 (transJ0 M) : ℕ∞) ::
          (List.replicate k (s₀ ++ [Sym.dsym (entry M 1 (transJ0 M) : ℕ∞)])).flatten
          ++ flatBT (transT2 M)
          ++ (List.replicate k b₀).flatten ++ b₁)

/-- Isabelle `m_8_5_scbdec_fseq_condV` (pss_wip.thy:51466) の (2)(3) 連言
（共有 surgery 対 `(s₁,b₁)` の生成）。 -/
def ExchV_scbdec_fseq_condV : Prop :=
  ∀ M : PS, RTPS M → TPS M → monoT M = true → 0 < transJ1 M → transT1 M ≠ BZero →
    transCondV M = true →
    ∃ s₁ b₁ : List Sym,
      scb_decomp (Trans (oper M 1)) s₁
        (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ ∧
      scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁

/-- Isabelle `atx_nf3x` (pss_wip.thy:86273)。非 adm 枝の塔の閉形式。 -/
def ExchV_nf3x : Prop :=
  ∀ (M : PS) (s₁ b₁ : List Sym), STPS M → monoT M = true → transCondV M = true →
    adm M (parent M 0 (Lng M - 1)) = false →
    scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ →
    scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ →
    (∀ k : ℕ, flatBT (Trans (oper M (k + 1)))
        = s₁ ++ flatBP (.db (entry M 1 (transJm1 M) : ℕ∞)
            (e5x_bodyM (transT2 M) (entry M 1 (transJ0 M)) k)) ++ b₁) ∧
    (∀ m : ℕ, 1 ≤ m → flatBT (operB (Trans M) (numBT m))
        = s₁ ++ flatBP (.db (entry M 1 (transJm1 M) : ℕ∞)
            (e5x_bodyO (transT2 M) (entry M 1 (transJ0 M)) m)) ++ b₁)

/-! ## 純 `BT` 順序の比較（Isabelle 58006–58080 / 61547–61640 の逐語移植） -/

/-- Isabelle `s85b_W_principal`。 -/
private theorem s85b_W_principal_e5 (u : ℕ) (t c : BT) (k : ℕ) :
    ∃ b, s85b_W u t c k = Dprin (u : ℕ∞) b := by
  cases k with
  | zero => exact ⟨c, rfl⟩
  | succ j => exact ⟨addBT t (s85b_W u t c j), rfl⟩

/-- `Dprin` の同一 head 下での狭義単調性（7.3-c1-c2-order の私的複製）。 -/
private theorem lessBT_Dprin_same_e5 (v : ℕ∞) {a b : BT}
    (h : lessBT a b = true) : lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

/-- 同一 head の `lessBP`。 -/
private theorem lessBP_same_e5 (v : ℕ∞) {a b : BT}
    (h : lessBT a b = true) : lessBP (.db v a) (.db v b) = true := by
  simp [lessBP, h]

/-- Isabelle `e5x_W_lt_Dpt`: head が真に大きい principal は塔を上回る。 -/
private theorem e5x_W_lt_Dpt_e5 {u v : ℕ} (huv : u < v) (t c d : BT) (k : ℕ) :
    lessBT (s85b_W u t c k) (Dprin (v : ℕ∞) d) = true := by
  obtain ⟨b, hb⟩ := s85b_W_principal_e5 u t c k
  rw [hb]
  have : ((u : ℕ∞) < (v : ℕ∞)) := by exact_mod_cast huv
  simp [Dprin, lessBT, lessBPList, lessBP, this]

/-- Isabelle `e5x_W_seed_shift`: 高さを 1 上げると種を `t` から `0_B` に縮めた
損失を超えて取り返す。 -/
private theorem e5x_W_seed_shift_e5 (u : ℕ) (t : BT) (k : ℕ) :
    lessBT (s85b_W u t t k) (s85b_W u t BZero (k + 1)) = true := by
  induction k with
  | zero =>
      have hne : s85b_W u t BZero 0 ≠ BZero := by
        simp [s85b_W, Dprin, BZero]
      exact lessBT_Dprin_same_e5 _ (lessBT_addBT_self t _ hne)
  | succ j ih =>
      exact lessBT_Dprin_same_e5 _ (addBT_lt_right_bf t _ _ ih)

/-- Isabelle `e5x_W_height_mono0`: `0_B` 種の塔は高さで狭義単調。 -/
private theorem e5x_W_height_mono0_e5 (u : ℕ) (t : BT) (k : ℕ) :
    lessBT (s85b_W u t BZero k) (s85b_W u t BZero (k + 1)) = true := by
  induction k with
  | zero =>
      refine lessBT_Dprin_same_e5 _ ?_
      rcases t with ⟨ts⟩
      cases ts with
      | nil => simp [BZero, addBT, lessBT, lessBPList, s85b_W, Dprin]
      | cons p ps => simp [BZero, addBT, lessBT, lessBPList, s85b_W, Dprin]
  | succ j ih =>
      exact lessBT_Dprin_same_e5 _ (addBT_lt_right_bf t _ _ ih)

/-- Isabelle `s85b_W_mono_seed`: 種について狭義単調。 -/
private theorem s85b_W_mono_seed_e5 (u : ℕ) (t : BT) {c c' : BT}
    (h : lessBT c c' = true) (k : ℕ) :
    lessBT (s85b_W u t c k) (s85b_W u t c' k) = true := by
  induction k with
  | zero => exact lessBT_Dprin_same_e5 _ h
  | succ j ih => exact lessBT_Dprin_same_e5 _ (addBT_lt_right_bf t _ _ ih)

/-- Isabelle `s85b_W_lt_top`: `u < v` なら塔は `D_u(t +_B D_v 0)` を全高さで下回る。 -/
private theorem s85b_W_lt_top_e5 {u v : ℕ} (huv : u < v) (t : BT) (k : ℕ) :
    lessBT (s85b_W u t t k) (Dprin (u : ℕ∞) (addBT t (Dprin (v : ℕ∞) BZero)))
      = true := by
  cases k with
  | zero =>
      refine lessBT_Dprin_same_e5 _ ?_
      exact lessBT_addBT_self t _ (by simp [Dprin, BZero])
  | succ j =>
      refine lessBT_Dprin_same_e5 _ ?_
      exact addBT_lt_right_bf t _ _ (e5x_W_lt_Dpt_e5 huv t t BZero j)

/-- Isabelle `e5x_bodyM_lt_c2`。 -/
private theorem e5x_bodyM_lt_c2_e5 {e v : ℕ} (hev : e < v) (u : ℕ∞) (t : BT)
    (k : ℕ) :
    lessBP (.db u (e5x_bodyM t e k))
      (.db u (addBT t (Dprin (v : ℕ∞) BZero))) = true := by
  refine lessBP_same_e5 _ ?_
  cases k with
  | zero =>
      simpa [e5x_bodyM] using lessBT_addBT_self t _ (by simp [Dprin, BZero])
  | succ j =>
      simpa [e5x_bodyM] using
        addBT_lt_right_bf t _ _ (e5x_W_lt_Dpt_e5 hev t t BZero (j + 1))

/-- Isabelle `e5x_bodyM_lt_bodyO`。 -/
private theorem e5x_bodyM_lt_bodyO_e5 (u : ℕ∞) (t : BT) (e k : ℕ) :
    lessBP (.db u (e5x_bodyM t e k))
      (.db u (e5x_bodyO t e (k + 2))) = true := by
  refine lessBP_same_e5 _ ?_
  cases k with
  | zero =>
      have hne : s85b_W e t BZero 2 ≠ BZero := by simp [s85b_W, Dprin, BZero]
      simpa [e5x_bodyM, e5x_bodyO] using lessBT_addBT_self t (s85b_W e t BZero 2) hne
  | succ j =>
      have h1 : lessBT (s85b_W e t t (j + 1)) (s85b_W e t BZero (j + 2)) = true :=
        e5x_W_seed_shift_e5 e t (j + 1)
      have h2 : lessBT (s85b_W e t BZero (j + 2)) (s85b_W e t BZero (j + 3)) = true :=
        e5x_W_height_mono0_e5 e t (j + 2)
      have h3 : lessBT (s85b_W e t t (j + 1)) (s85b_W e t BZero (j + 3)) = true :=
        lessBT_linear_trans _ _ _ h1 h2
      simpa [e5x_bodyM, e5x_bodyO] using addBT_lt_right_bf t _ _ h3

/-! ## 塔の flat 文字列（Isabelle `s85b_W_flat` 58014 の逐語移植） -/

private theorem s85b_W_mem_T_B_e5 {u : ℕ} {t c : BT} (ht : t ∈ T_B) (hc : c ∈ T_B)
    (k : ℕ) : s85b_W u t c k ∈ T_B := by
  induction k with
  | zero => exact Dprin_mem_T_B (by simp) hc
  | succ j ih => exact Dprin_mem_T_B (by simp) (addBT_mem_T_B ht ih)

private theorem flatten_replicate_comm_e5 {α : Type} (b : List α) (j : ℕ) :
    (List.replicate j b).flatten ++ b = b ++ (List.replicate j b).flatten := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]

/-- 回転補題（Isabelle の `s85b_rot_cons` に相当）。 -/
private theorem rot_cons_e5 (x : Sym) (s : List Sym) (k : ℕ) :
    x :: (List.replicate k (s ++ [x])).flatten
      = (List.replicate k (x :: s)).flatten ++ [x] := by
  induction k with
  | zero => simp
  | succ j ih =>
      have : x :: (List.replicate (j + 1) (s ++ [x])).flatten
          = (x :: s) ++ (x :: (List.replicate j (s ++ [x])).flatten) := by
        simp [List.replicate_succ, List.append_assoc]
      rw [this, ih]
      simp [List.replicate_succ, List.append_assoc]

/-- Isabelle `s85b_W_flat`。 -/
private theorem s85b_W_flat_e5 {u : ℕ} {t c0 c : BT} {s₀ b₀ : List Sym}
    (htTB : t ∈ T_B) (hc0TB : c0 ∈ T_B) (hc0p : ∃ p, c0 = .trm [p])
    (hinner : scb_decomp (addBT t c0) s₀ (flatBT c0) b₀)
    (hcTB : c ∈ T_B) (k : ℕ) :
    flatBT (s85b_W u t c k)
      = (List.replicate k (Sym.dsym (u : ℕ∞) :: s₀)).flatten
        ++ flatBT (Dprin (u : ℕ∞) c) ++ (List.replicate k b₀).flatten := by
  induction k with
  | zero => simp [s85b_W]
  | succ j ih =>
      have hWTB : s85b_W u t c j ∈ T_B := s85b_W_mem_T_B_e5 htTB hcTB j
      have hWp : ∃ p, s85b_W u t c j = BT.trm [p] := by
        obtain ⟨b, hb⟩ := s85b_W_principal_e5 u t c j
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
      rw [flatten_replicate_comm_e5 b₀ j]

/-! ## 条件 (V) 下の小補題（自前） -/

/-- Isabelle `s85b_jm1_adm` (pss_wip.thy:57138)。 -/
private theorem jm1_adm_e5 {M : PS} (h : adm M (transJ0 M) = true) :
    transJm1 M = transJ0 M := by
  simp [transJm1, Adm, h]

/-- 条件 (V) は `M₁,j₀ + 1 = M₁,j₁`、特に `M₁,j₀ < M₁,j₁`（Isabelle は
`m_8_5_condV_uv` を経由するが、`j₋₁ = j₀` の adm 枝でも非 adm 枝でも
必要なのはこの直読みだけ）。 -/
private theorem condV_ev_e5 {M : PS} (h : transCondV M = true) :
    entry M 1 (transJ0 M) < entry M 1 (transJ1 M) := by
  simp only [transCondV, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  simp only [transJ0, transJ1]
  omega

/-- Isabelle `m_8_5_transC2_condV` (pss_wip.thy:43023)。 -/
private theorem transC2_condV_e5 (M : PS) (h : transCondV M = true) :
    transC2 M
      = Dprin (transV M)
          (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
  simp [transC2, transC2Core, transJ1, h]

private theorem flatBT_Dprin_e5 (v : ℕ∞) (a : BT) :
    flatBT (Dprin v a) = Sym.dsym v :: flatBT a := rfl

private theorem BZero_mem_T_B_e5 : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem rot_cons_app_e5 (x : Sym) (s X : List Sym) (k : ℕ) :
    (List.replicate k (x :: s)).flatten ++ (x :: X)
      = x :: ((List.replicate k (s ++ [x])).flatten ++ X) := by
  have h := rot_cons_e5 x s k
  calc (List.replicate k (x :: s)).flatten ++ (x :: X)
      = ((List.replicate k (x :: s)).flatten ++ [x]) ++ X := by
        simp [List.append_assoc]
    _ = (x :: (List.replicate k (s ++ [x])).flatten) ++ X := by rw [← h]
    _ = x :: ((List.replicate k (s ++ [x])).flatten ++ X) := by simp

/-! ## adm 枝の塔形（Isabelle `m_8_5_scbdec_adm_forms` を `s85b_W` 言語へ読み替え） -/

/-- Isabelle の `m_8_5_scbdec_adm_forms` ＋ `s85b_W_flat` ＋ 回転。adm 枝では
`Trans (M[k+1])` の core が `s85b_W e t₂ t₂ k`、`operB (Trans M) (numBT n)` の
core が `s85b_W e t₂ 0_B (n+1)` であり、共有 surgery 対 `(s₁,b₁)` は共通。 -/
private theorem adm_tower_forms_e5
    (hAF : ExchV_scbdec_adm_forms) (hshape : ExchV_scbdec_c1_shape)
    (hsetup : ExchV_condV_setup)
    (M : PS) (hST : STPS M) (hmono : monoT M = true) (hcond : transCondV M = true)
    (hadm : adm M (transJ0 M) = true) :
    ∃ s₁ b₁ : List Sym,
      (∀ x ∈ b₁, x = Sym.rp) ∧
      scb_decomp (Trans M) s₁ (flatBT (transC2 M)) b₁ ∧
      (∀ k : ℕ, flatBT (Trans (oper M (k + 1)))
        = s₁ ++ flatBT (s85b_W (entry M 1 (transJ0 M)) (transT2 M) (transT2 M) k)
            ++ b₁) ∧
      (∀ n : ℕ, flatBT (operB (Trans M) (numBT n))
        = s₁ ++ flatBT (s85b_W (entry M 1 (transJ0 M)) (transT2 M) BZero (n + 1))
            ++ b₁) := by
  have hR : RTPS M := STPS_RTPS M hST
  have hT : TPS M := STPS_TPS M hST
  obtain ⟨hJ1, hT1⟩ := hsetup M hR hT hmono hcond
  obtain ⟨-, -, ht2TB, -⟩ := hshape M hR hT hmono hJ1 hT1
  obtain ⟨s₀, s₁, b₀, b₁, hinner, hd1, hk1, hfseq, hmM⟩ := hAF M hST hmono hcond hadm
  have hc0TB : Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero ∈ T_B :=
    Dprin_mem_T_B (by simp) BZero_mem_T_B_e5
  have hc0p : ∃ p, Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero = BT.trm [p] := ⟨_, rfl⟩
  refine ⟨s₁, b₁, hd1.2.2, hk1.1, ?_, ?_⟩
  · intro k
    have hW := s85b_W_flat_e5 (u := entry M 1 (transJ0 M)) (t := transT2 M)
      (c0 := Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero) (c := transT2 M)
      ht2TB hc0TB hc0p hinner ht2TB k
    rw [hmM k, hW, flatBT_Dprin_e5]
    simp only [List.append_assoc, List.cons_append]
    rw [rot_cons_app_e5]
  · intro n
    have hW := s85b_W_flat_e5 (u := entry M 1 (transJ0 M)) (t := transT2 M)
      (c0 := Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero) (c := BZero)
      ht2TB hc0TB hc0p hinner BZero_mem_T_B_e5 (n + 1)
    rw [hfseq n, hW, flatBT_Dprin_e5]
    simp only [List.append_assoc, List.cons_append, BZero, flatBT]
    rw [rot_cons_app_e5]

/-! ## surgery 位置での持ち上げ -/

private theorem flatBP_db_e5 (v : ℕ∞) (a : BT) :
    flatBP (.db v a) = Sym.dsym v :: flatBT a := rfl

/-- 部分表現の不等式の延長性（`scbext_lessBT`）を `Dprin` core 形で使う。 -/
private theorem lt_of_scb_Dprin_e5 {t t' : BT} {s b : List Sym} {v : ℕ∞} {X Y : BT}
    (ht : flatBT t = s ++ flatBT (Dprin v X) ++ b)
    (ht' : flatBT t' = s ++ flatBT (Dprin v Y) ++ b)
    (hrp : ∀ x ∈ b, x = Sym.rp)
    (hlt : lessBT X Y = true) : lessBT t t' = true := by
  refine scbext_lessBT (s := s) (b := b) (cp := .db v X) (cp' := .db v Y) ?_ ?_ hrp
    (lessBP_same_e5 v hlt)
  · rw [ht, flatBT_Dprin_e5, flatBP_db_e5]
  · rw [ht', flatBT_Dprin_e5, flatBP_db_e5]

/-- `s85b_W` の core（外側 `D_u` の内側）。 -/
private def Wbody_e5 (u : ℕ) (t c : BT) : ℕ → BT
  | 0 => c
  | k + 1 => addBT t (s85b_W u t c k)

private theorem s85b_W_eq_Dprin_e5 (u : ℕ) (t c : BT) (k : ℕ) :
    s85b_W u t c k = Dprin (u : ℕ∞) (Wbody_e5 u t c k) := by
  cases k <;> rfl

private theorem lessBT_BZero_e5 {t : BT} (h : t ≠ BZero) :
    lessBT BZero t = true := by
  rcases t with ⟨ts⟩
  cases ts with
  | nil => exact absurd rfl h
  | cons p ps => simp [BZero, lessBT, lessBPList]

/-! ## adm 枝の三つの結論（Isabelle 57964 / 58086 / 58168 / 58322） -/

private theorem adm_core_lt_c2_e5 {e v : ℕ} (hev : e < v) (t : BT) (k : ℕ) :
    lessBT (Wbody_e5 e t t k) (addBT t (Dprin (v : ℕ∞) BZero)) = true := by
  cases k with
  | zero => exact lessBT_addBT_self t _ (by simp [Dprin, BZero])
  | succ j =>
      exact addBT_lt_right_bf t _ _ (e5x_W_lt_Dpt_e5 hev t t BZero j)

private theorem adm_core_lt_oper_e5 (e : ℕ) (t : BT) (k : ℕ) :
    lessBT (Wbody_e5 e t t k) (Wbody_e5 e t BZero (k + 1)) = true := by
  cases k with
  | zero =>
      exact lessBT_addBT_self t _ (by simp [s85b_W, Dprin, BZero])
  | succ j =>
      exact addBT_lt_right_bf t _ _ (e5x_W_seed_shift_e5 e t j)

private theorem adm_core_lt_oper_weak_e5 (e : ℕ) (t : BT) (k : ℕ) :
    lessBT (Wbody_e5 e t t k) (Wbody_e5 e t BZero (k + 2)) = true := by
  cases k with
  | zero => exact lessBT_addBT_self t _ (by simp [s85b_W, Dprin, BZero])
  | succ j =>
      refine addBT_lt_right_bf t _ _ ?_
      exact lessBT_linear_trans _ _ _ (e5x_W_seed_shift_e5 e t j)
        (e5x_W_height_mono0_e5 e t (j + 1))

private theorem adm_oper_lt_core_e5 {t : BT} (ht : t ≠ BZero) (e k : ℕ) :
    lessBT (Wbody_e5 e t BZero (k + 1)) (Wbody_e5 e t t (k + 1)) = true :=
  addBT_lt_right_bf t _ _ (s85b_W_mono_seed_e5 e t (lessBT_BZero_e5 ht) k)

/-- Isabelle `m_8_5_Trans_oper_exchange_condV_adm_uncond` (pss_wip.thy:60884)
＋ 原文添字版。adm 枝では塔が
`Trans(M[n]) < Trans(M)[n-1] < Trans(M[n+1])` と厳密に交互配置される。
conj (1) が**原文の添字 `mₙ = n-1`**、conj (2) が Isabelle の述べる添字 `n`
（(1) の弱系）、conj (3) が降下性、conj (4) が原文の結論 (3)。 -/
theorem Trans_oper_exchange_condV_adm_uncond
    (hAF : ExchV_scbdec_adm_forms) (hshape : ExchV_scbdec_c1_shape)
    (hsetup : ExchV_condV_setup) (ht2ne : ExchV_t2_nonzero_condV)
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hcond : transCondV M = true)
    (hadm : adm M (parent M 0 (Lng M - 1)) = true) :
    lessBT (Trans (oper M n)) (operB (Trans M) (numBT (n - 1))) = true ∧
      lessBT (Trans (oper M n)) (operB (Trans M) (numBT n)) = true ∧
      lessBT (Trans (oper M n)) (Trans M) = true ∧
      lessBT (operB (Trans M) (numBT (n - 1))) (Trans (oper M (n + 1))) = true := by
  have hadm' : adm M (transJ0 M) = true := by
    simpa [transJ0, lastParent, lastIdx] using hadm
  have hR : RTPS M := STPS_RTPS M hST
  have hT : TPS M := STPS_TPS M hST
  obtain ⟨hJ1, hT1⟩ := hsetup M hR hT hmono hcond
  obtain ⟨hV, -, -, -⟩ := hshape M hR hT hmono hJ1 hT1
  have hjm1 : transJm1 M = transJ0 M := jm1_adm_e5 hadm'
  have hev : entry M 1 (transJ0 M) < entry M 1 (transJ1 M) := condV_ev_e5 hcond
  have ht2 : transT2 M ≠ BZero := ht2ne M hR hT hmono hcond
  obtain ⟨s₁, b₁, hrp, hTM, hMt, hOt⟩ :=
    adm_tower_forms_e5 hAF hshape hsetup M hST hmono hcond hadm'
  have hMflat : ∀ k : ℕ, flatBT (Trans (oper M (k + 1)))
      = s₁ ++ flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (Wbody_e5 (entry M 1 (transJ0 M)) (transT2 M) (transT2 M) k)) ++ b₁ := by
    intro k; rw [hMt k, s85b_W_eq_Dprin_e5]
  have hOflat : ∀ m : ℕ, flatBT (operB (Trans M) (numBT m))
      = s₁ ++ flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (Wbody_e5 (entry M 1 (transJ0 M)) (transT2 M) BZero (m + 1))) ++ b₁ := by
    intro m; rw [hOt m, s85b_W_eq_Dprin_e5]
  have hc2 : transC2 M = Dprin (entry M 1 (transJ0 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
    rw [transC2_condV_e5 M hcond, hV, hjm1]
  have hTMflat : flatBT (Trans M)
      = s₁ ++ flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))) ++ b₁ := by
    have h := hTM.1
    rwa [hc2] at h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using lt_of_scb_Dprin_e5 (hMflat k) (hOflat k) hrp
      (adm_core_lt_oper_e5 _ _ k)
  · exact lt_of_scb_Dprin_e5 (hMflat k) (hOflat (k + 1)) hrp
      (adm_core_lt_oper_weak_e5 _ _ k)
  · exact lt_of_scb_Dprin_e5 (hMflat k) hTMflat hrp (adm_core_lt_c2_e5 hev _ k)
  · simpa using lt_of_scb_Dprin_e5 (hOflat k) (hMflat (k + 1)) hrp
      (adm_oper_lt_core_e5 ht2 _ k)

/-! ## 非 adm 枝（Isabelle 61656 / 86315） -/

/-- Isabelle `m_8_5_Trans_oper_exchange_condV_nonadm` (pss_wip.thy:61656) ＋
`atx_Trans_oper_exchange_condV_nonadm_uncond` (同 86315)。非 adm 枝では
交換関係 (1) の正しい Buchholz 添字は `n + 1`（Isabelle が証明した形）。 -/
theorem Trans_oper_exchange_condV_nonadm_uncond
    (hNF : ExchV_nf3x) (hfseq : ExchV_scbdec_fseq_condV)
    (hshape : ExchV_scbdec_c1_shape) (hsetup : ExchV_condV_setup)
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true)
    (hnadm : adm M (parent M 0 (Lng M - 1)) = false) (hn : 1 ≤ n) :
    lessBT (Trans (oper M n)) (operB (Trans M) (numBT (n + 1))) = true ∧
      lessBT (Trans (oper M n)) (Trans M) = true := by
  have hR : RTPS M := STPS_RTPS M hST
  have hT : TPS M := STPS_TPS M hST
  obtain ⟨hJ1, hT1⟩ := hsetup M hR hT hmono hcond
  obtain ⟨hV, -, -, -⟩ := hshape M hR hT hmono hJ1 hT1
  obtain ⟨s₁, b₁, hd1, hk1⟩ := hfseq M hR hT hmono hJ1 hT1 hcond
  obtain ⟨hMform, hOform⟩ := hNF M s₁ b₁ hST hmono hcond hnadm hd1 hk1
  have hrp : ∀ x ∈ b₁, x = Sym.rp := hd1.2.2
  have hev : entry M 1 (transJ0 M) < entry M 1 (transJ1 M) := condV_ev_e5 hcond
  have hc2 : transC2 M = Dprin (entry M 1 (transJm1 M) : ℕ∞)
      (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) := by
    rw [transC2_condV_e5 M hcond, hV]
  have hTMflat : flatBT (Trans M)
      = s₁ ++ flatBP (.db (entry M 1 (transJm1 M) : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))) ++ b₁ := by
    have h := hk1.1.1
    rw [hc2] at h
    rw [h, flatBT_Dprin_e5, flatBP_db_e5]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · exact scbext_lessBT (hMform k) (hOform (k + 2) (by omega)) hrp
      (e5x_bodyM_lt_bodyO_e5 _ _ _ k)
  · exact scbext_lessBT (hMform k) hTMflat hrp (e5x_bodyM_lt_c2_e5 hev _ _ k)

/-! ## パッケージ -/

/-- 原文命題（条件 (V) の下での `Trans` と基本列の交換関係）の忠実版
（`p_8_5_Trans_oper_exchange`, isabelle/pss_paper.thy:2070）、**adm 枝**。
原文の添字 `mₙ = n - 1` のままで (1)(2)(3) の三結論がすべて成立する
（しかも `≤` ではなく `<` で厳密）。訂正は不要。 -/
theorem Trans_oper_exchange_condV
    (hAF : ExchV_scbdec_adm_forms) (hshape : ExchV_scbdec_c1_shape)
    (hsetup : ExchV_condV_setup) (ht2ne : ExchV_t2_nonzero_condV)
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (_hj₁ : 1 < Lng M - 1) (hcond : transCondV M = true)
    (hadm : adm M (parent M 0 (Lng M - 1)) = true) :
    leBT (Trans (oper M n))
        (operB (Trans M)
          (numBT (if adm M (parent M 0 (Lng M - 1)) then n - 1 else n))) = true ∧
      leBT (Trans (oper M n)) (Trans M) = true ∧
      leBT (operB (Trans M)
          (numBT (if adm M (parent M 0 (Lng M - 1)) then n - 1 else n)))
        (Trans (oper M (n + 1))) = true := by
  obtain ⟨h1, -, h2, h3⟩ :=
    Trans_oper_exchange_condV_adm_uncond hAF hshape hsetup ht2ne M n hST hmono hn
      hcond hadm
  refine ⟨?_, ?_, ?_⟩ <;> simp [hadm, leBT, h1, h2, h3]

/-- `8.7-fseq-descend` の `FseqDesc_exchV` と同形（drop-in）。全 host 無条件
（adm 枝は `numBT (m-1)`、非 adm 枝は `numBT (m+1)` が witness）。 -/
theorem exchV_holds
    (hAF : ExchV_scbdec_adm_forms) (hshape : ExchV_scbdec_c1_shape)
    (hsetup : ExchV_condV_setup) (ht2ne : ExchV_t2_nonzero_condV)
    (hNF : ExchV_nf3x) (hfseq : ExchV_scbdec_fseq_condV) :
    ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
      transCondV N = true → 1 < m →
      ∃ k, leBT (Trans (oper N m)) (operB (Trans N) (numBT k)) = true := by
  intro N m hST hmono _hL hcond hm
  have hm1 : 1 ≤ m := by omega
  cases hb : adm N (parent N 0 (Lng N - 1)) with
  | true =>
      obtain ⟨h1, -, -, -⟩ :=
        Trans_oper_exchange_condV_adm_uncond hAF hshape hsetup ht2ne N m hST hmono
          hm1 hcond hb
      exact ⟨m - 1, by simp [leBT, h1]⟩
  | false =>
      obtain ⟨h1, -⟩ :=
        Trans_oper_exchange_condV_nonadm_uncond hNF hfseq hshape hsetup N m hST
          hmono hcond hb hm1
      exact ⟨m + 1, by simp [leBT, h1]⟩

/-- 降下性（原文の結論 (2)）、全 host 無条件。 -/
theorem Trans_oper_descend_condV
    (hAF : ExchV_scbdec_adm_forms) (hshape : ExchV_scbdec_c1_shape)
    (hsetup : ExchV_condV_setup) (ht2ne : ExchV_t2_nonzero_condV)
    (hNF : ExchV_nf3x) (hfseq : ExchV_scbdec_fseq_condV)
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hcond : transCondV M = true) :
    lessBT (Trans (oper M n)) (Trans M) = true := by
  cases hb : adm M (parent M 0 (Lng M - 1)) with
  | true =>
      exact (Trans_oper_exchange_condV_adm_uncond hAF hshape hsetup ht2ne M n hST
        hmono hn hcond hb).2.2.1
  | false =>
      exact (Trans_oper_exchange_condV_nonadm_uncond hNF hfseq hshape hsetup M n
        hST hmono hcond hb hn).2

#print axioms Trans_oper_exchange_condV_adm_uncond
#print axioms Trans_oper_exchange_condV_nonadm_uncond
#print axioms Trans_oper_exchange_condV
#print axioms exchV_holds
#print axioms Trans_oper_descend_condV

end PSS
