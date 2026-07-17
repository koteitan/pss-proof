import «8».«8.6-Trans-fseq-condVI»
import «8».«8.7-Trans-preserves-OT»
import «8».«8.7-fseq-descend»
import «6».«6.7-standard-reduced»

/-!
# §8.6 命題（条件 (VI) の下での `Trans` と基本列の交換関係）— 残差の削減

- 原文: `tmp/content.md` 5484（証明 5670–5760）＝
  命題（条件(VI)の下での Trans と基本列の交換関係）
- 訂正: **なし**（A34/A37 は取り下げ済＝`corrections-old.md`:123/154。A23 は `operB` の
  *定義* にかかるだけで本命題の主張にはかからない）。
- Isabelle:
  * 逐語転記 = `p_8_6_Trans_fseq_condVI`（`isabelle/pss_paper.thy`:2218、`sorry`）
  * 一般ホスト交換（許容 `j₀`）= `c613x_condVI_exch_adm`（`layerB/pss_wip.thy`:73312）
  * 汎用エンジン = `c613x_Dtower_mono`（同 :73203）、`c613x_operB_fseq_value`（同 :73220）、
    `c613x_tower_operB_eq`（同 :73266）、`c613x_tower_operB_lt`（同 :73284）
  * `TransPreservesOT` = `p_8_7_Trans_preserves_OT`（`pss_paper.thy`:2317）
    ＝ `y5_Trans_OT_B`（`layerC/pss_scratch.thy`）
- 依存: `8.6-Trans-fseq-condVI`（`CondVIAdmTowerScb` / `CondVIExchNadm` /
  `TransPreservesOT` の 3 named Prop と `p_8_6_Trans_fseq_condVI`）、
  `8.7-Trans-preserves-OT`（`Trans_preserves_OT`）、`8.7-fseq-descend`
  （`FseqDesc_exchVI`）、`7.2-scb-fseq`（`scb_fseq_kind1_general`、上記経由）、
  `7.3-Pred-Trans-descend`（`scbext_lessBT`、上記経由）。
- 状態: 🚧 GREEN（sorry 0）。**達成**:
  * `TransPreservesOT` を **`8.7-Trans-preserves-OT` の 12 本の `OTdisp_*` へ委譲**
    （`transPreservesOT_of_OTdisp_v6`）＝ 8.6 固有の残差ではなくなった（既出 Prop への
    合流なのでプロジェクト全体の残差は増えない）。
  * `CondVIAdmTowerScb` を **`CondVI_scbdec_adm_forms_v6` 1 本へ削減**
    （`condVIAdmTowerScb_of_scbforms_v6`）。削減で落ちたのは Isabelle の
    `c613x_operB_fseq_value` ＋ `flat_Dtower` ＝ **Buchholz 側の内容全部**。
    残った `CondVI_scbdec_adm_forms_v6` は純粋にペア数列側の
    `flatMn`（`c6zx_L_tower` 由来の閉形式）＋ `c₂` の kind-1 手術
    （`s84c2_Trans_c2_decomp` ＋ `scb_kind1_of_suffix`）である。
  * `CondVIExchNadm` を **`CondVI_scbdec_nadm_forms_v6` 1 本へ削減**
    （`condVIExchNadm_of_scbforms_v6`）。同様に Buchholz 側は本ファイルで閉じた。
  * `FseqDesc_exchVI` の drop-in `exchVI_holds_v6`（(A)/(B) modulo、`TransPreservesOT`
    **不要**＝`1 < m` なので原文 (1) の例外脚が立たない）。
- **未達（正直な報告）**: `CondVI_scbdec_adm_forms_v6` /
  `CondVI_scbdec_nadm_forms_v6` は**閉じていない**。Isabelle 側の当該証明は
  `trans_surgery_localized` / `s84c2_Trans_c2_decomp`（`pss_wip.thy`:54605）と
  `m_8_4_oper_props_5` / `s84x_L` / `c6zx_L_tower`（同 :72166）に乗るが、
  これらは **Lean 未移植の §8.4 scb 分解クラスタ**（`8.5-Trans-fseq-condV` の
  `ExchV_scbdec_c1_shape` / `ExchV_scbdec_adm_forms` / `ExchV_scbdec_fseq_condV`
  が同じ理由で露出している共有基盤）であり、単一ファイルの射程を超える。
  詳細は各 `def` の docstring を参照。
- 経験的確認（`python/_c6_condvi_scbforms.py`、真正 ST_PS プール = diagSeq 種の
  `oper` 閉包 2000、単項ホスト 1674、A23 訂正後の `operB`、`n ≤ 4`）:
  * (A') `CondVI_scbdec_adm_forms_v6`: 許容 `j₀` の条件 (VI) ホスト **206/206**（非空虚）
  * (B') `CondVI_scbdec_nadm_forms_v6`: 非許容 `j₀` の条件 (VI) ホスト **24/24**（非空虚）。
    観測された `(U, u)` は `(0,1) (0,2) (1,2) (1,3) (2,3) (2,4)`＝**常に `U = u-1`** で、
    Isabelle の注記どおり非許容側には真の外側の頭 `D_U` が立つ（`U < u+1` を満たす
    ＝kind-1）。塔の添字が `n`（許容側の `n-1` ではない）であることも確認済。
  ＝削減後の残差は**空虚ではなく、かつ真**（A34/A37 の取り下げ＝
  `corrections-old.md`:123/154 も再確認済）。

## 設計

Isabelle の `c613x_condVI_exch_adm` は、その内部で
```
flatMn : 1 ≤ n ⟹ flatBT (Trans (M[n]))            = s₁ @ flatBP (DB u (Dtower u (n-1))) @ b₁
ov     :          flatBT (operB (Trans M) (numBT m)) = s₁ @ flatBP (DB u (Dtower u (m+1))) @ b₁
```
の 2 式を作り、塔の添字を突き合わせて (1)(2)(3) を出す。このうち **`ov` は
`flatMn` から独立**であり、`Trans M` の `c₂ = D_u(D_{u+1} 0)` における kind-1 手術
だけから `scb_fseq_kind1_general`（＝Isabelle `m_7_2_scb_fseq_kind1_general`）で
機械的に出る。本ファイルはその `ov` を証明し、残差から Buchholz 側を除去する。
-/

namespace PSS

/-! ## 塔 `Dtower`（Isabelle `Dtower u k = (Dpt u)^k 0`） -/

/-- Isabelle `Dtower`: `D_u^k 0`。`8.6-Trans-fseq-condVI` の `CondVIAdmTowerScb` は
これを `(Dprin u)^[k] BZero` の形で直接書いているので、`abbrev` ではなく `def` にして
展開補題を用意する。 -/
private def Dtower_v6 (u : ℕ) (k : ℕ) : BT := (Dprin (u : ℕ∞))^[k] BZero

private theorem Dtower_zero_v6 (u : ℕ) : Dtower_v6 u 0 = BZero := rfl

private theorem Dtower_succ_v6 (u k : ℕ) :
    Dtower_v6 u (k + 1) = Dprin (u : ℕ∞) (Dtower_v6 u k) := by
  simp [Dtower_v6, Function.iterate_succ_apply']

/-! ## 純 `BT` 側の補助（`8.4`/`8.5` の私的複製、suffix `_v6`） -/

private theorem lessBT_Dprin_same_v6 (v : ℕ∞) {a b : BT}
    (h : lessBT a b = true) : lessBT (Dprin v a) (Dprin v b) = true := by
  simp [Dprin, lessBT, lessBPList, lessBP, h]

private theorem lessBP_same_v6 (v : ℕ∞) {a b : BT}
    (h : lessBT a b = true) : lessBP (.db v a) (.db v b) = true := by
  simp [lessBP, h]

private theorem lessBT_zero_Dprin_v6 (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

private theorem flatBT_Dprin_v6 (v : ℕ∞) (a : BT) :
    flatBT (Dprin v a) = flatBP (.db v a) := rfl

private theorem BZero_mem_T_B_v6 : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem Dprin_ne_BZero_v6 (v : ℕ∞) (a : BT) : Dprin v a ≠ BZero := by
  simp [Dprin, BZero]

/-- Isabelle `c613x_Dtower_mono`（`layerB/pss_wip.thy`:73203）。
`D_u^k 0 < D_u^{k+1} 0`（頭文字がひとつ増える）。 -/
private theorem Dtower_mono_v6 (u k : ℕ) :
    lessBT (Dtower_v6 u k) (Dtower_v6 u (k + 1)) = true := by
  induction k with
  | zero =>
      rw [Dtower_zero_v6, Dtower_succ_v6, Dtower_zero_v6]
      exact lessBT_zero_Dprin_v6 _ _
  | succ k ih =>
      -- `rw [Dtower_succ_v6 u k]` は両辺の `Dtower u (k+1)` を書き換えるので、
      -- 先に `ih` 側を同じ形へ寄せてから使う（memo.md §3 の RHS 書換の罠）。
      have h1 : Dtower_v6 u (k + 1) = Dprin (u : ℕ∞) (Dtower_v6 u k) :=
        Dtower_succ_v6 u k
      rw [h1] at ih
      rw [Dtower_succ_v6 u (k + 1), h1]
      exact lessBT_Dprin_same_v6 _ ih

/-! ## `Dtower` の平坦形（Isabelle `flat_Dtower`） -/

/-- `flatBT (D_u^k 0) = (D_u)^k 0`。 -/
private theorem flat_Dtower_v6 (u k : ℕ) :
    flatBT (Dtower_v6 u k) = List.replicate k (Sym.dsym (u : ℕ∞)) ++ [Sym.zero] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Dtower_succ_v6, flatBT_Dprin_v6]
      show Sym.dsym (u : ℕ∞) :: flatBT (Dtower_v6 u k) = _
      rw [ih, List.replicate_succ]
      simp

/-- `flatBP (D_U (D_u^k 0))`。 -/
private theorem flatBP_db_Dtower_v6 (U u k : ℕ) :
    flatBP (.db (U : ℕ∞) (Dtower_v6 u k))
      = Sym.dsym (U : ℕ∞) :: List.replicate k (Sym.dsym (u : ℕ∞)) ++ [Sym.zero] := by
  show Sym.dsym (U : ℕ∞) :: flatBT (Dtower_v6 u k) = _
  rw [flat_Dtower_v6]
  simp

/-- Isabelle `c6gx_concat_rep_single`（`layerB/pss_wip.thy`:70086）。 -/
private theorem flatten_replicate_single_v6 {α : Type} (x : α) (k : ℕ) :
    (List.replicate k [x]).flatten = List.replicate k x := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- Isabelle `c6gx_concat_rep_nil`（同 :70089）。 -/
private theorem flatten_replicate_nil_v6 {α : Type} (k : ℕ) :
    (List.replicate k ([] : List α)).flatten = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-! ## `ov`: 条件 (VI) 型 marked principal の `operB` 値（Buchholz 側、無条件） -/

/-- Isabelle `domTag_Dv0` 相当（`8.6-Trans-fseq-condVI` の `domTag_Dv0_c6` は
`private` なので同じ証明を複製）。 -/
private theorem domTag_Dv0_v6 (v : ℕ) (hv : 0 < v) :
    domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := by
  simp [domTag, domTagList, domTagBP, Dprin, BZero,
    show (v : ℕ∞) ≠ 0 by simpa using (Nat.ne_of_gt hv), ENat.coe_ne_top]

private theorem Dv0_mem_T_B_v6 (v : ℕ) : Dprin (v : ℕ∞) BZero ∈ T_B := by
  simp [T_B, Dprin, BZero, dfree_BT, dfree_BPList, dfree_BP]

private theorem isPTB_str_Dv0_v6 (v : ℕ) :
    isPTB_str (flatBT (Dprin (v : ℕ∞) BZero)) :=
  ⟨.db (v : ℕ∞) BZero, by simp [dfree_BP, BZero, dfree_BT, dfree_BPList], rfl⟩

private theorem scb_decomp_Dv0_self_v6 (v : ℕ) :
    scb_decomp (Dprin (v : ℕ∞) BZero) [] (flatBT (Dprin (v : ℕ∞) BZero)) [] :=
  ⟨by simp, fun _ => isPTB_str_Dv0_v6 v, by simp⟩

/-- **Isabelle `c613x_operB_fseq_value`**（`layerB/pss_wip.thy`:73220）。

条件 (VI) 型の marked principal `c₂ = D_U(D_{u+1} 0)`（`U < u+1`）を持つ `t` の
基本列 `operB t (numBT n)` は、同じ手術 `(s₁,b₁)` の内側で `D_U(D_u^{n+1} 0)` になる。
Isabelle と同様、`scb_fseq_kind1_general`（＝`m_7_2_scb_fseq_kind1_general`）を
`body = D_{u+1} 0`、`s₀ = b₀ = []` に特殊化してから文字列を潰すだけ。

**これが `CondVIAdmTowerScb` / `CondVIExchNadm` の残差から Buchholz 側を除去する鍵。** -/
private theorem operB_fseq_value_v6 {t : BT} {s₁ b₁ : List Sym} {U u : ℕ}
    (htT : t ∈ T_B) (hUlt : U < u + 1)
    (hk1 : scb_kind1 t s₁
      (flatBT (Dprin (U : ℕ∞) (Dprin ((u + 1 : ℕ) : ℕ∞) BZero))) b₁) (n : ℕ) :
    flatBT (operB t (numBT n))
      = s₁ ++ flatBP (.db (U : ℕ∞) (Dtower_v6 u (n + 1))) ++ b₁ := by
  have htag : domTag (Dprin ((u + 1 : ℕ) : ℕ∞) BZero) = .below (u + 1 - 1) :=
    domTag_Dv0_v6 (u + 1) (by omega)
  have h :=
    (scb_fseq_kind1_general (t := t) (body := Dprin ((u + 1 : ℕ) : ℕ∞) BZero)
      (u := U) (v := u + 1) (n := n) (s₀ := []) (s₁ := s₁) (b₀ := []) (b₁ := b₁)
      htT hUlt (Dv0_mem_T_B_v6 (u + 1)) htag (Dprin_ne_BZero_v6 _ _)
      (scb_decomp_Dv0_self_v6 (u + 1)) hk1).2
  rw [h, flatBP_db_Dtower_v6]
  have hsub : (u + 1 - 1 : ℕ) = u := by omega
  rw [hsub]
  simp

/-! ## `CondVIAdmTowerScb` の削減 -/

private theorem Dtower_mem_T_B_v6 (u k : ℕ) : Dtower_v6 u k ∈ T_B := by
  induction k with
  | zero => rw [Dtower_zero_v6]; exact BZero_mem_T_B_v6
  | succ k ih =>
      rw [Dtower_succ_v6]
      have : dfree_BT (Dtower_v6 u k) = true := ih
      simp [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP, this]

private theorem isPTB_str_Dprin_Dtower_v6 (U u k : ℕ) :
    isPTB_str (flatBT (Dprin (U : ℕ∞) (Dtower_v6 u k))) := by
  refine ⟨.db (U : ℕ∞) (Dtower_v6 u k), ?_, rfl⟩
  have : dfree_BT (Dtower_v6 u k) = true := Dtower_mem_T_B_v6 u k
  simp [dfree_BP, this]

/-- **削減後の残差 (A)** — 許容 `j₀` の条件 (VI) ホストにおける、**ペア数列側だけ**の
2 事実（`u := M_{1,j₀}`）:

* `flatMn`: `n ≥ 1` について `Trans (M[n])` は共通手術 `(s₁,b₁)` の内側で
  `D_u(D_u^{n-1} 0)` である（Isabelle `c6zx_L_tower`（`layerB/pss_wip.thy`:72166）
  ＋ 境界同定 `c6zx_condVI_oper_L`（同 :72257）＋ `n=1` 脚の
  `m_8_4_oper1_eq_Pred` ＋ `c6gx_condVI_transC1_adm`（同 :69904）が出す形）;
* `k1`: `Trans M` は同じ `(s₁,b₁)` で marked principal `c₂ = D_u(D_{u+1} 0)` の
  kind-1 scb 分解を持つ（Isabelle `s84c2_Trans_c2_decomp`（同 :54605）
  ＝`trans_surgery_localized` ＋ `c6gx_condVI_transC2`（同 :69884）
  ＋ `scb_kind1_of_suffix`（RightNodes `[u, u+1]`）が出す形）。

`8.6-Trans-fseq-condVI`:220 の `CondVIAdmTowerScb` との差＝**`ov`（`operB` 側の
塔閉形式）が消えていること**。`ov` は `k1` から `operB_fseq_value_v6` で機械的に
出るので、残差から Buchholz 側の内容は除去済み。

**未閉の理由（正直な報告）**: Isabelle の `c6zx_L_tower` は `m_8_4_oper_props_5`
（§8.4 の scb 分解クラスタ）に、`s84c2_Trans_c2_decomp` は
`trans_surgery_localized` に乗る。どちらも **Lean 未移植の共有基盤**であり
（`8.5-Trans-fseq-condV` の `ExchV_scbdec_c1_shape` / `ExchV_scbdec_adm_forms` /
`ExchV_scbdec_fseq_condV` が同じ基盤の欠落として露出しているものと同一）、
本ファイル単独では閉じられない。 -/
def CondVI_scbdec_adm_forms_v6 : Prop :=
  ∀ (M : PS), STPS M → RTPS M → monoT M = true → transCondVI M = true →
    1 < Lng M - 1 → adm M (transJ0 M) = true →
    ∃ s₁ b₁ : List Sym,
      (∀ n, 1 ≤ n →
        scb_decomp (Trans (oper M n)) s₁
          (flatBT (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
            (Dtower_v6 (entry M 1 (transJ0 M)) (n - 1)))) b₁) ∧
      scb_kind1 (Trans M) s₁
        (flatBT (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
          (Dprin ((entry M 1 (transJ0 M) + 1 : ℕ) : ℕ∞) BZero))) b₁

/-- **`CondVIAdmTowerScb`（`8.6-Trans-fseq-condVI`:220）の削減**。

`ov`（`operB (Trans M) (numBT m)` の塔閉形式）を `k1` から
`operB_fseq_value_v6`（＝Isabelle `c613x_operB_fseq_value`）で導出する。 -/
theorem condVIAdmTowerScb_of_scbforms_v6
    (h : CondVI_scbdec_adm_forms_v6) : CondVIAdmTowerScb := by
  intro M hST hR hmono hcond hj₁ hadm
  obtain ⟨s₁, b₁, hMn, hk1⟩ := h M hST hR hmono hcond hj₁ hadm
  refine ⟨s₁, b₁, ?_, ?_⟩
  · intro n hn
    have := hMn n hn
    simpa [Dtower_v6] using this
  · intro m
    set u := entry M 1 (transJ0 M) with hu
    have hov := operB_fseq_value_v6 (t := Trans M) (s₁ := s₁) (b₁ := b₁)
      (U := u) (u := u) (Trans_mem_T_B M hR) (by omega) hk1 m
    refine ⟨?_, ?_, hk1.1.2.2⟩
    · rw [hov]
      show _ = s₁ ++ flatBT (Dprin (u : ℕ∞) ((Dprin (u : ℕ∞))^[m + 1] BZero)) ++ b₁
      rfl
    · intro _
      have := isPTB_str_Dprin_Dtower_v6 u u (m + 1)
      simpa [Dtower_v6] using this

/-! ## 塔のマッチャ（Isabelle `c613x_tower_operB_eq` / `c613x_tower_operB_lt`） -/

/-- Isabelle `c613x_tower_operB_eq`（`layerB/pss_wip.thy`:73266）。同じ手術の内側で
同じ塔になれば項として等しい（`flatBT` の単射性）。 -/
private theorem tower_eq_v6 {w w' : BT} {s₁ b₁ : List Sym} {U u k : ℕ}
    (hw : flatBT w = s₁ ++ flatBP (.db (U : ℕ∞) (Dtower_v6 u k)) ++ b₁)
    (hw' : flatBT w' = s₁ ++ flatBP (.db (U : ℕ∞) (Dtower_v6 u k)) ++ b₁) :
    w = w' :=
  flatBT_injective (hw.trans hw'.symm)

/-- Isabelle `c613x_tower_operB_lt`（同 :73284）。塔の添字がひとつ小さければ狭義に
小さい（`scbext_lessBT` ＋ `c613x_Dtower_mono`）。 -/
private theorem tower_lt_v6 {w w' : BT} {s₁ b₁ : List Sym} {U u k : ℕ}
    (hw : flatBT w = s₁ ++ flatBP (.db (U : ℕ∞) (Dtower_v6 u k)) ++ b₁)
    (hw' : flatBT w' = s₁ ++ flatBP (.db (U : ℕ∞) (Dtower_v6 u (k + 1))) ++ b₁)
    (hrp : ∀ x ∈ b₁, x = Sym.rp) :
    lessBT w w' = true :=
  scbext_lessBT hw hw' hrp (lessBP_same_v6 _ (Dtower_mono_v6 u k))

/-! ## `CondVIExchNadm` の削減 -/

/-- **削減後の残差 (B)** — 非許容 `j₀` の条件 (VI) ホストにおける、**ペア数列側だけ**の
2 事実（`u := M_{1,j₀}`、`U := transV M`）。

Isabelle `c613x_condVI_exch_nadm`（`layerB/pss_wip.thy`:73514）の setup そのもの:
非許容側は `c₁ = D_U(D_u 0)` に**真の外側の頭** `U`（`U < u+1`、経験的 141/141）が
立つので、`Trans(M[n])` の塔の添字は `n`（許容側の `n-1` ではない）＝外側の `D_U` が
L 塔をひとつずらす。`t2eq`（`transT2 M = D_u 0`）と `vU`（`transV M = U`）は
Isabelle 側で `c6nx_t2eq`（同 :76619）/ `c6nx_condVI_uv`（同 :76352）が無条件化して
おり（→`c6nx_condVI_exch_nadm_uncond`、同 :76705）、ここではその帰結だけを束ねる。

`8.6-Trans-fseq-condVI`:236 の `CondVIExchNadm` との差＝**3 結論すべて（`operB` 側の
塔閉形式・等式マッチ・狭義不等式）が消えていること**。それらは本ファイルの
`operB_fseq_value_v6` / `tower_eq_v6` / `tower_lt_v6` で導出する。

**未閉の理由**: (A) と同じ（`m_8_5_scbdec_c1_shape` / `trans_surgery_localized` /
`c6zx_L_tower` の Lean 未移植）。 -/
def CondVI_scbdec_nadm_forms_v6 : Prop :=
  ∀ (M : PS), STPS M → RTPS M → monoT M = true → transCondVI M = true →
    1 < Lng M - 1 → ¬ (adm M (transJ0 M) = true) →
    ∃ (U : ℕ) (s₁ b₁ : List Sym),
      U < entry M 1 (transJ0 M) + 1 ∧
      (∀ n, 1 ≤ n →
        flatBT (Trans (oper M n))
          = s₁ ++ flatBP (.db (U : ℕ∞) (Dtower_v6 (entry M 1 (transJ0 M)) n)) ++ b₁) ∧
      scb_kind1 (Trans M) s₁
        (flatBT (Dprin (U : ℕ∞)
          (Dprin ((entry M 1 (transJ0 M) + 1 : ℕ) : ℕ∞) BZero))) b₁

/-- **`CondVIExchNadm`（`8.6-Trans-fseq-condVI`:236）の削減**。

Isabelle `c613x_condVI_exch_nadm` の結論部の逐語: 塔の添字は
`Trans(M[n])` ↦ `n`、`operB (Trans M) (numBT m)` ↦ `m+1` なので
(2) は `m = n-1` で等式、(1) は `m = n`、(3) は `m = n-1` で狭義になる。 -/
theorem condVIExchNadm_of_scbforms_v6
    (h : CondVI_scbdec_nadm_forms_v6) : CondVIExchNadm := by
  intro M hST hR hmono hcond hj₁ hadm
  obtain ⟨U, s₁, b₁, hUlt, hMn, hk1⟩ := h M hST hR hmono hcond hj₁ hadm
  set u := entry M 1 (transJ0 M) with hu
  have hrp : ∀ x ∈ b₁, x = Sym.rp := hk1.1.2.2
  have hov : ∀ m : ℕ, flatBT (operB (Trans M) (numBT m))
      = s₁ ++ flatBP (.db (U : ℕ∞) (Dtower_v6 u (m + 1))) ++ b₁ :=
    operB_fseq_value_v6 (t := Trans M) (s₁ := s₁) (b₁ := b₁) (U := U) (u := u)
      (Trans_mem_T_B M hR) hUlt hk1
  refine ⟨?_, ?_, ?_⟩
  · -- (1) `Trans (M[n]) < Trans(M)[n]`（塔 `n` 対 `n+1`）
    intro n hn
    exact tower_lt_v6 (hMn n hn) (hov n) hrp
  · -- (2) `Trans (M[n]) = Trans(M)[n-1]`（塔はともに `n`）
    intro n hn
    have h2 := hov (n - 1)
    rw [show n - 1 + 1 = n by omega] at h2
    exact tower_eq_v6 (hMn n hn) h2
  · -- (3) `Trans(M)[n-1] < Trans (M[n+1])`（塔 `n` 対 `n+1`）
    intro n hn
    have h2 := hov (n - 1)
    rw [show n - 1 + 1 = n by omega] at h2
    exact tower_lt_v6 h2 (hMn (n + 1) (by omega)) hrp

/-! ## `TransPreservesOT` の委譲（§8.7 へ） -/

/-- **`TransPreservesOT`（`8.6-Trans-fseq-condVI`:247）の討伐**。

`8.7-Trans-preserves-OT` の `Trans_preserves_OT` は形が**完全に一致**しており
（当該ファイル:487 の docstring が「drop-in」と明言）、そのまま外れる。§8.7 側の
12 本の `OTdisp_*` は**既に §8.7 が露出している Prop** なので、これは 8.6 固有の
残差を消す（プロジェクト全体の残差集合は増えない）合流である。

Isabelle 側では `y5_Trans_OT_B`（`layerC/pss_scratch.thy`、**証明済・仮定ゼロ**）＝
`p_8_7_Trans_preserves_OT`（`pss_paper.thy`:2317）。 -/
theorem transPreservesOT_of_OTdisp_v6
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq) :
    TransPreservesOT :=
  Trans_preserves_OT hI hII hOTint hOTpred hOTmulti hZC hCIn1 hCIj0 hCIj1
    hCVIj1 hCVIa hCVIn

/-! ## `8.7-fseq-descend` の `FseqDesc_exchVI` への drop-in -/

/-- **`FseqDesc_exchVI`（`8.7-fseq-descend`:101）の drop-in**（(A)/(B) modulo）。

降下柱が要求するのは `1 < m` における `∃ k, Trans(N[m]) ≤ Trans(N)[k]` だけなので、

* 原文 (1) の例外脚（`m_n = -1` ＝ `n = 1` かつ `j₀` 許容）は **`1 < m` で立たない**;
* したがって **`TransPreservesOT` は不要**（`p_8_6_Trans_fseq_condVI` は結論 (3) の
  降下のために [Buc1] Lemma 3.2(a) を呼ぶので `Trans M ∈ OT_B` を要するが、
  交換則 `exchVI` 自体は順序を主張しないので要らない）。

witness は許容 `j₀` で `k = m-2`、非許容 `j₀` で `k = m-1`（原文の `m_n` そのもの）。
どちらの枝も**等式**で出るので `leBT` は反射律で閉じる。 -/
theorem exchVI_holds_v6 (hA : CondVIAdmTowerScb) (hB : CondVIExchNadm) :
    FseqDesc_exchVI := by
  intro N m hST hmono hj₁ hcond hm
  have hR : RTPS N := STPS_RTPS N hST
  by_cases hadm : adm N (transJ0 N) = true
  · -- 許容 `j₀`: `m ≥ 2` なので原文の `m_n = m-2` が立つ
    obtain ⟨s₁, b₁, hMn, hop⟩ := hA N hST hR hmono hcond hj₁ hadm
    have h1 := hMn m (by omega)
    have h2 := hop (m - 2)
    rw [show m - 2 + 1 = m - 1 by omega] at h2
    have he : Trans (oper N m) = operB (Trans N) (numBT (m - 2)) :=
      flatBT_injective (h1.1.trans h2.1.symm)
    exact ⟨m - 2, by rw [he]; simp [leBT]⟩
  · -- 非許容 `j₀`: `m_n = m-1`、例外脚なし
    have he := (hB N hST hR hmono hcond hj₁ hadm).2.1 m (by omega)
    exact ⟨m - 1, by rw [he]; simp [leBT]⟩

/-! ## §8.6 の残差パッケージ -/

/-- **§8.6 命題の逐語形**（原文 `tmp/content.md` 5484 ＝ `p_8_6_Trans_fseq_condVI`、
`isabelle/pss_paper.thy`:2218）を、**削減後の残差だけの上で**述べ直したもの。

`8.6-Trans-fseq-condVI`:295 の `p_8_6_Trans_fseq_condVI` が要求していた 3 本の
名前付き仮定のうち

* `TransPreservesOT` は §8.7 の `OTdisp_*` へ委譲（＝8.6 固有の残差から消えた）、
* `CondVIAdmTowerScb` / `CondVIExchNadm` は Buchholz 側を剥がした
  `CondVI_scbdec_adm_forms_v6` / `CondVI_scbdec_nadm_forms_v6` へ削減

されている。**残差は §8.4 scb 分解クラスタ（`trans_surgery_localized` /
`m_8_4_oper_props_5` / `c6zx_L_tower`）の Lean 未移植分のみ**であり、これは
§8.5（`ExchV_scbdec_*`）と共有の基盤である。 -/
theorem p_8_6_Trans_fseq_condVI_v6
    (hA : CondVI_scbdec_adm_forms_v6) (hB : CondVI_scbdec_nadm_forms_v6)
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq)
    (M : PS) (n : ℕ)
    (hST : STPS M) (hR : RTPS M) (hmono : monoT M = true) (hn : 0 < n)
    (hj₁ : 1 < Lng M - 1) (hcond : transCondVI M = true) :
    (n = 1 ∧ adm M (parent M 0 (Lng M - 1)) = true →
        ∃ k, 1 < k ∧ k ≤ entry M 1 (Lng M - 1) + 1 ∧
          Trans (oper M n) = ((fun a => operB a (numBT 0))^[k]) (Trans M))
      ∧ (¬ (n = 1 ∧ adm M (parent M 0 (Lng M - 1)) = true) →
        Trans (oper M n) =
          operB (Trans M)
            (numBT (if adm M (parent M 0 (Lng M - 1)) then n - 2 else n - 1)))
      ∧ lessBT (Trans (oper M n)) (Trans M) = true :=
  p_8_6_Trans_fseq_condVI M n
    (condVIAdmTowerScb_of_scbforms_v6 hA)
    (condVIExchNadm_of_scbforms_v6 hB)
    (transPreservesOT_of_OTdisp_v6 hI hII hOTint hOTpred hOTmulti hZC hCIn1
      hCIj0 hCIj1 hCVIj1 hCVIa hCVIn)
    hST hR hmono hn hj₁ hcond

/-- `FseqDesc_exchVI` の drop-in を、削減後の残差だけの上で述べ直したもの。 -/
theorem exchVI_holds_of_scbforms_v6
    (hA : CondVI_scbdec_adm_forms_v6) (hB : CondVI_scbdec_nadm_forms_v6) :
    FseqDesc_exchVI :=
  exchVI_holds_v6 (condVIAdmTowerScb_of_scbforms_v6 hA)
    (condVIExchNadm_of_scbforms_v6 hB)

#print axioms condVIAdmTowerScb_of_scbforms_v6
#print axioms condVIExchNadm_of_scbforms_v6
#print axioms transPreservesOT_of_OTdisp_v6
#print axioms exchVI_holds_v6
#print axioms exchVI_holds_of_scbforms_v6
#print axioms p_8_6_Trans_fseq_condVI_v6

end PSS
