import «8».«8.1-Trans-fseq-condI»
import «8».«8.3-TransCondII-engine»
import «8».«8.5-Trans-fseq-condV»
import «8».«8.6-const2nd-Trans»
import «8».«8.7-fseq-descend»

/-!
# §8.7 降下柱 — `FseqDesc_*` の掃討 (2)

- 原文: `tmp/content.md` 5869（§8.7）。**本ファイルは新しい記事命題を主張しない**。
  `«8».«8.7-fseq-descend»` が露出した 16 本の名前付き `Prop`（`FseqDesc_*`、
  同 :67–167）のうち、`«8».«8.7-fseq-descend-props»`（Wave H、7 本）が残した
  9 本を、ビルド済みツリーの既存定理へ配線する掃討ファイル第 2 弾。
  訂正: なし（A 番号の該当なし）。
- **本ファイルで配線した 6 本**（→ 16 本中 13 本が配線済みになる）:
  | `FseqDesc_*` | 出典 | Isabelle | modulo |
  |---|---|---|---|
  | `exchV` | `8.5-Trans-fseq-condV`:568 `exchV_holds` | `m_8_5_Trans_oper_exchange_condV_adm_uncond` (pss_wip.thy:60884) ＋ `atx_..._nonadm_uncond` (同 86315) | `ExchV_*` 6 本 |
  | `m_8_5_TransCondV_oper_descend_engine` | 同:596 `Trans_oper_descend_condV` | `m_8_5_TransCondV_oper_descend_engine` (同 37496) | 同上 6 本 |
  | `m_8_6_rcseq_Trans` | `8.6-const2nd-Trans`:625 `const2nd_Trans` | `m_8_6_rcseq_Trans` (同 14299) | **無条件** |
  | `exchI` | `8.1-Trans-fseq-condI`:568 `exchI_holds` | `scx_condI_j0pos_masterCF` (同 83639) | `CondI_masterCF` 1 本 |
  | `exchII` | `8.3-TransCondII-engine`:223 `exchII_of_masterCF` | `c2sx_condII_masterCF` (同 87430) | `CondII_masterCF` 1 本 |
  | `m_8_3_TransCondII_oper_descend_engine` | 同:149 `..._fseqdesc_form` | `m_8_3_TransCondII_oper_descend_engine` (同 28563) | **無条件** |
- 🚨 **本ファイルの存在理由 = 名前衝突の解消**。Wave H は
  `PSS.Trans_oper_exchange` が `8.4-Trans-fseq-condIII-IV`(229) と
  `8.5-Trans-fseq-condV`(548) で**別主張として二重宣言**されていたため `exchV` を
  配線できなかった（co-import で**エラーを出さずヘッダが汚染**される）。
  親が 8.5 側を `Trans_oper_exchange_condV` に改名して解消済み。本ファイルは
  `8.1`＋`8.3`＋`8.5`＋`8.6`＋`8.7` の**5 ファイル同時 import が通ること**を
  実証する（dispatcher は 16 本を同時に要求するので、これが降下柱の前提）。
- 🚨 **`m_8_6_rcseq_Trans` は移植ではなく特殊化**（rcseq 基盤の新設は不要だった）:
  `const2ndSeq m u j₁ = (range (j₁+1)).map (fun j => (m+j, u))` に `m := u` を
  代入すると Isabelle の `rcseq u j₁ = map (λj. (u+j, u)) [0..<j₁+1]` と
  **構文的に一致**する（`diagSeq` は rcseq ではない）。
- **未配線の残り 3 本**（ビルド済みツリーに twin 無し＝実移植が要る。content-grep 済）:
  `operI_j0zero_trans_mult`（Isa `operI_j0zero_trans_mult` 36977。
  ⚠️`8.1-Trans-fseq-condI` は**これを仮定として消費する側**であって供給しない）／
  `f7x_Trans_append_Pblocks`（Isa 51888）／`m_7_3_Trans_leftmost_2`
  （Isa `m_7_3_Trans_leftmost` 16569 の (2)、要 `_pc` 16067 ~400 行）。
- 依存（ビルド済みのみ import）: `8.1-Trans-fseq-condI`（`exchI_holds` /
  `CondI_masterCF`）、`8.3-TransCondII-engine`（`exchII_of_masterCF` /
  `CondII_masterCF` / `TransCondII_oper_descend_engine_fseqdesc_form`）、
  `8.5-Trans-fseq-condV`（`exchV_holds` / `Trans_oper_descend_condV` /
  `ExchV_*` 6 本）、`8.6-const2nd-Trans`（`const2nd_Trans` / `const2ndSeq`）、
  `8.7-fseq-descend`（`FseqDesc_*` の定義）。
  **`8.7-fseq-descend-props`（Wave H）は import しない**（配線は素集合）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  無条件 2 本 ＋ 仮定 modulo 4 本（`_of_*` と命名して `_holds` と区別）。
-/

namespace PSS

/-! ## (1) `FseqDesc_exchV` — 名前衝突解消後の配線（PRIORITY 1）

Wave H が入れられなかったのは `PSS.Trans_oper_exchange` が
`8.4-Trans-fseq-condIII-IV` と `8.5-Trans-fseq-condV` で二重宣言だったため。
親が 8.5 側を `Trans_oper_exchange_condV` に改名して解消済み。 -/
theorem FseqDesc_exchV_of_ExchV
    (hAF : ExchV_scbdec_adm_forms) (hshape : ExchV_scbdec_c1_shape)
    (hsetup : ExchV_condV_setup) (ht2ne : ExchV_t2_nonzero_condV)
    (hNF : ExchV_nf3x) (hfseq : ExchV_scbdec_fseq_condV) :
    FseqDesc_exchV :=
  exchV_holds hAF hshape hsetup ht2ne hNF hfseq

/-! ## (2) `FseqDesc_m_8_6_rcseq_Trans`（PRIORITY 2）

移植ではなく**特殊化**。`8.6-const2nd-Trans` の
`const2ndSeq m u j₁ = (range (j₁+1)).map (fun j => (m+j, u))` に `m := u` を代入すると
Isabelle の `rcseq u j₁ = map (λj. (u+j, u)) [0..<j₁+1]` と**構文的に一致**する。 -/
theorem FseqDesc_m_8_6_rcseq_Trans_holds : FseqDesc_m_8_6_rcseq_Trans := by
  intro u j₁
  have hTPS : TPS (const2ndSeq u u j₁) := by
    simp [TPS, const2ndSeq]
  obtain ⟨h0, hp⟩ := const2nd_Trans (const2ndSeq u u j₁) u u j₁ rfl hTPS
  by_cases hz : j₁ = 0 ∧ u = 0
  · rw [if_pos hz]
    exact h0 hz
  · rw [if_neg hz]
    exact hp (by omega)

/-! ## (3) `FseqDesc_m_8_5_TransCondV_oper_descend_engine`（PRIORITY 3）

`8.5-Trans-fseq-condV`:596 の `Trans_oper_descend_condV` が結論をそのまま与える
（`Prop` 側の `1 < Lng M - 1` / `Trans M ∈ OT_B` / 交換則入力 `hexch` は**不要**——
条件 (V) の降下は adm/非 adm 両枝とも交換則の帰結として既に閉じているため）。
同じ 6 本の `ExchV_*` modulo。 -/
theorem FseqDesc_m_8_5_TransCondV_oper_descend_engine_of_ExchV
    (hAF : ExchV_scbdec_adm_forms) (hshape : ExchV_scbdec_c1_shape)
    (hsetup : ExchV_condV_setup) (ht2ne : ExchV_t2_nonzero_condV)
    (hNF : ExchV_nf3x) (hfseq : ExchV_scbdec_fseq_condV) :
    FseqDesc_m_8_5_TransCondV_oper_descend_engine := by
  intro M n hST hmono _hj1 hcond hn _hOT _hexch
  exact Trans_oper_descend_condV hAF hshape hsetup ht2ne hNF hfseq M n hST hmono
    (by omega) hcond

/-! ## (4) `FseqDesc_exchI` — `8.1-Trans-fseq-condI`:568 の `exchI_holds` -/
theorem FseqDesc_exchI_of_CondI (hCF : CondI_masterCF) : FseqDesc_exchI :=
  exchI_holds hCF

/-! ## (5) `FseqDesc_exchII` — `8.3-TransCondII-engine`:223 の `exchII_of_masterCF` -/
theorem FseqDesc_exchII_of_CondII (hCF : CondII_masterCF) : FseqDesc_exchII :=
  exchII_of_masterCF hCF

/-! ## (6) `FseqDesc_m_8_3_TransCondII_oper_descend_engine` — **無条件**

`8.3-TransCondII-engine`:149 の `TransCondII_oper_descend_engine_fseqdesc_form`。 -/
theorem FseqDesc_m_8_3_TransCondII_oper_descend_engine_holds :
    FseqDesc_m_8_3_TransCondII_oper_descend_engine :=
  TransCondII_oper_descend_engine_fseqdesc_form

#print axioms FseqDesc_exchV_of_ExchV
#print axioms FseqDesc_m_8_6_rcseq_Trans_holds
#print axioms FseqDesc_m_8_5_TransCondV_oper_descend_engine_of_ExchV
#print axioms FseqDesc_exchI_of_CondI
#print axioms FseqDesc_exchII_of_CondII
#print axioms FseqDesc_m_8_3_TransCondII_oper_descend_engine_holds

end PSS
