import «6».«6.2-P-fseq»
import «6».«6.7-standard-reduced»
import «8».«8.2-subexpr-setup»
import «8».«8.4-Trans-fseq-condIII-IV»
import «8».«8.6-Trans-fseq-condVI»
import «8».«8.7-Trans-preserves-OT»
import «8».«8.7-fseq-descend»

/-!
# §8.7 降下柱 — `FseqDesc_*` の掃討

- 原文: `tmp/content.md` 5869（§8.7）。本ファイルは新しい記事命題を主張しない。
  `«8».«8.7-fseq-descend»` が露出した 16 本の名前付き `Prop`（`FseqDesc_*`、
  同 :67–167）を、ビルド済みツリーの既存定理へ配線するだけの掃討ファイル。
  訂正: なし（A 番号の該当なし）。
- **無条件に外れた 3 本**（`_holds`。Isabelle 対応は 1:1）:
  * `FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1`
    ← `m_8_2_subexpr_component_Pred_Adm0_clause1` (layerB/pss_wip.thy:19436)
    ＝ Lean `subexpr_component_Pred_Adm0_clause1`（`8.2-subexpr-setup`:121）。
  * `FseqDesc_m_8_6_TransCondVI_oper_descend_engine`
    ← `m_8_6_TransCondVI_oper_descend_engine` (同 :40250)
    ＝ Lean 同名（`8.6-Trans-fseq-condVI`:73）。
  * `FseqDesc_m_6_2_P_oper_2` ← `m_6_2_P_oper_2` (pss_mechanized.thy:2539)
    ＝ Lean `P_fseq_2`（`6.2-P-fseq`:884）。
- **仮定 modulo で還元した 4 本**（`_of_*`。無条件ではない）:
  `FseqDesc_Trans_preserves_OT`（12 本）/ `_exchIII` / `_exchIV`（2 本）/
  `_exchVI`（3 本）。詳細は各定理の docstring。
- **`FseqDesc_exchV` は本ファイルに入れられない**（`8.4` と `8.5` の
  `PSS.Trans_oper_exchange` 名前衝突。下の 🚨 節を参照）。残り 8 本は未移植。
- 依存（ビルド済みのみ import）: `6.2-P-fseq`（`P_fseq_2`）、
  `6.7-standard-reduced`（`STPS_RTPS`）、`8.2-subexpr-setup`
  （`subexpr_component_Pred_Adm0_clause1`）、`8.4-Trans-fseq-condIII-IV`
  （`exch_condIII`/`exch_condIV`）、`8.6-Trans-fseq-condVI`
  （`m_8_6_TransCondVI_oper_descend_engine`/`p_8_6_Trans_fseq_condVI`）、
  `8.7-Trans-preserves-OT`（`Trans_preserves_OT_fseqdesc_form`）、
  `8.7-fseq-descend`（`FseqDesc_*` の定義）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
-/

namespace PSS

/-! ## (1) §8.2 clause (1)（Adm-零枝の値核）

`8.2-subexpr-setup`:121 の `subexpr_component_Pred_Adm0_clause1` と本体は同一。
差は条件の綴りだけ——`Prop` 側が `Prop` の `∨`、ビルド済み側が `Bool` の `||`
（`8.7-fseq-descend`:115 vs `8.2-subexpr-setup`:126）。 -/
theorem FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1_holds :
    FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1 := by
  intro M hR hmono hj1 hAdm0 hcond
  refine subexpr_component_Pred_Adm0_clause1 M hR hmono hj1 hAdm0 ?_
  rcases hcond with h | h | h <;> simp [h]

/-! ## (2) §8.6 条件 (VI) の降下エンジン

`8.6-Trans-fseq-condVI`:73 の `m_8_6_TransCondVI_oper_descend_engine` は
`hR : RTPS M` を余分に取る。`Prop` 側にそれが無いのは `STPS M` から
`STPS_RTPS`（`6.7-standard-reduced`:59、＝ §6.7 の `ST_PS ⊆ RT_PS`）で出るため。 -/
theorem FseqDesc_m_8_6_TransCondVI_oper_descend_engine_holds :
    FseqDesc_m_8_6_TransCondVI_oper_descend_engine := by
  intro M n hST hmono hj₁ hcond hn hTOT hexch
  exact m_8_6_TransCondVI_oper_descend_engine M n hST (STPS_RTPS M hST) hmono hj₁
    hcond hn hTOT hexch

/-! ## (3) §6.2 基本列と P 分解の可換性（最終成分が複項の場合）

`6.2-P-fseq`:884 の `P_fseq_2` と結論・仮定ともに同一（`getLastD` の綴りまで一致）。 -/
theorem FseqDesc_m_6_2_P_oper_2_holds : FseqDesc_m_6_2_P_oper_2 := by
  intro M n hM hn hlast
  exact P_fseq_2 M n hM hn hlast

/-! ## 仮定付きの外し（`_of_*`。無条件ではない＝名前で区別する）

以下の 5 本は **`FseqDesc_*` をより小さい名前付き仮定の集合に還元する**もので、
`_holds` とは呼べない（呼べば嘘になる）。dispatcher を仮定 modulo で
instantiate するために親が使う配線。各仮定は引用元ファイルが公開している `Prop`。 -/

private theorem leBT_refl_dp (a : BT) : leBT a a = true := by
  simp [leBT]

/-- `FseqDesc_Trans_preserves_OT` ← `8.7-Trans-preserves-OT`:504
（`Trans_preserves_OT_fseqdesc_form`、OT 柱の 12 本 modulo）。 -/
theorem FseqDesc_Trans_preserves_OT_of_OTdisp
    (hI : OTdisp_exchI) (hII : OTdisp_exchII)
    (hOTint : OTdisp_OTint) (hOTpred : OTdisp_OTpred) (hOTmulti : OTdisp_OTmulti)
    (hZC : OTdisp_zerocol_predval) (hCIn1 : OTdisp_Trans_fseq_condI_n1)
    (hCIj0 : OTdisp_condI_j0z_eq) (hCIj1 : OTdisp_condI_j1eq1_eq)
    (hCVIj1 : OTdisp_condVI_j1eq1_eq) (hCVIa : OTdisp_condVI_adm_eq)
    (hCVIn : OTdisp_condVI_nadm_eq) :
    FseqDesc_Trans_preserves_OT :=
  Trans_preserves_OT_fseqdesc_form hI hII hOTint hOTpred hOTmulti hZC hCIn1 hCIj0
    hCIj1 hCVIj1 hCVIa hCVIn

/-- `FseqDesc_exchIII` ← `8.4-Trans-fseq-condIII-IV`:243（`exch_condIII`、2 本 modulo）。 -/
theorem FseqDesc_exchIII_of_Exch84 (h : Exch84_condIIIIV_producer)
    (hnp : Exch84_condIIIIV_noParent) : FseqDesc_exchIII :=
  fun N m hST hmono hj1 hc hm => exch_condIII h hnp N m hST hmono hj1 hc hm

/-- `FseqDesc_exchIV` ← `8.4-Trans-fseq-condIII-IV`:254（`exch_condIV`、同じ 2 本 modulo）。 -/
theorem FseqDesc_exchIV_of_Exch84 (h : Exch84_condIIIIV_producer)
    (hnp : Exch84_condIIIIV_noParent) : FseqDesc_exchIV :=
  fun N m hST hmono hj1 hc hm => exch_condIV h hnp N m hST hmono hj1 hc hm

/-! ### 🚨 `FseqDesc_exchV` を本ファイルに入れられない理由（名前衝突）

`8.5-Trans-fseq-condV`:568 の `exchV_holds` は `FseqDesc_exchV` を
（6 本 modulo で）そのまま与えるが、**`8.4-Trans-fseq-condIII-IV` と
`8.5-Trans-fseq-condV` は同時に import できない**。両者が同一名
`PSS.Trans_oper_exchange` を**別の主張で**宣言しているため
（`8.4`:229 ＝ 条件 (III)/(IV) の交換、`8.5`:548 ＝ 条件 (V) の交換）。
両方 import すると宣言重複で環境が壊れ、kimina では**エラーを出さずに
ヘッダが毒される**（`trivial` すら Unknown identifier になる）。

dispatcher は exchIII/IV と exchV を**両方**要求するので、これは降下柱全体の
ブロッカーである。**どちらかを改名する必要がある**（本ファイルの守備範囲外＝
親に報告）。ここでは Prop 2 本 ＋ 仮定 2 本と手数の少ない `8.4` 側を採った。 -/

/-- `FseqDesc_exchVI` ← `8.6-Trans-fseq-condVI`:295（`p_8_6_Trans_fseq_condVI`、3 本 modulo）。

`m > 1` なので原文の例外脚 `(n = 1 ∧ adm j₀)` は起きず、結論 (2) の**等式**が
そのまま使える（witness `k = if adm j₀ then m-2 else m-1`）。`RTPS` は
`STPS_RTPS` で供給。 -/
theorem FseqDesc_exchVI_of_CondVI
    (hA : CondVIAdmTowerScb) (hB : CondVIExchNadm) (hC : TransPreservesOT) :
    FseqDesc_exchVI := by
  intro N m hST hmono hj₁ hcond hm
  have hkey :=
    (p_8_6_Trans_fseq_condVI N m hA hB hC hST (STPS_RTPS N hST) hmono (by omega)
      hj₁ hcond).2.1 (by rintro ⟨h, -⟩; omega)
  exact ⟨_, by rw [hkey]; exact leBT_refl_dp _⟩

#print axioms FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1_holds
#print axioms FseqDesc_m_8_6_TransCondVI_oper_descend_engine_holds
#print axioms FseqDesc_m_6_2_P_oper_2_holds
#print axioms FseqDesc_Trans_preserves_OT_of_OTdisp
#print axioms FseqDesc_exchIII_of_Exch84
#print axioms FseqDesc_exchIV_of_Exch84
#print axioms FseqDesc_exchVI_of_CondVI

end PSS
