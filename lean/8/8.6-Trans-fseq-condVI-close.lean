import «8».«8.6-Trans-fseq-condVI»
import «8».«8.6-condVI-close»
import «8».«8.6-condVI-adm-forms»
import «8».«8.6-condVI-props»
import «8».«8.6-condVI-nadm-close»
import «8».«8.7-termination»

/-!
# §8.6 命題（条件 (VI) の下での `Trans` と基本列の交換関係）— **無条件クローズ**

- 原文: `tmp/content.md` 5484（証明 5670–5760）＝
  命題（条件 (VI) の下での `Trans` と基本列の交換関係）
- 訂正: **なし**（原文は印字どおり真）。
  * **A23**（§7.1 脚注 [30]）は `operB`（基本列）の *定義* にかかるだけで本命題の
    *主張* にはかからない（Lean 側は `Buchholz-1986/ および Buchholz-rel-ord/` で訂正後規則を採用済み）。
  * **A34/A37**（「(1) の `m_n = -1` の脚が偽」）は **取り下げ済**
    （`corrections-old.md`:123/154）。正しい基本列の下では 445/445 で原文は真。
- Isabelle:
  * 逐語転記 = `p_8_6_Trans_fseq_condVI`（`isabelle/pss_paper.thy`:2218、`sorry`）
  * 一般ホスト交換（許容 `j₀`）= `c613x_condVI_exch_adm`（`layerB/pss_wip.thy`:73312）
  * 一般ホスト交換（非許容 `j₀`）= `c6nx_condVI_exch_nadm_uncond`（同 :76705）
  * `TransPreservesOT` = `p_8_7_Trans_preserves_OT`（`pss_paper.thy`:2317）
    ＝ `y5_Trans_OT_B`（`layerC/pss_scratch.thy`）

## 目的

`8.6-Trans-fseq-condVI` の `p_8_6_Trans_fseq_condVI` は名前付き命題 3 本
（`CondVIAdmTowerScb` / `CondVIExchNadm` / `TransPreservesOT`）modulo の
green-modulo だった。この 3 本は **すべて無条件に供給可能** になっている
（Wave AW で `p_8_7_termination` が無条件化した副産物）ので、本ファイルで
その 3 本を無条件に組み、`p_8_6_Trans_fseq_condVI` を丸ごと無条件化した
双子 `p_8_6_Trans_fseq_condVI_uncond` を公開する。

## 供給（3 本とも無条件・仮定ゼロ）

* `CondVIAdmTowerScb`（許容 `j₀` の塔閉形式、原文 5735 の道）
    = `condVIAdmTowerScb_of_scbforms_v6 CondVI_scbdec_adm_forms_v6_holds`
    （`8.6-condVI-close` ＋ `8.6-condVI-adm-forms`）。
* `CondVIExchNadm`（非許容 `j₀` の交換、原文 5720）
    = `condVIExchNadm_holds_v6p CondVIres_nadm_Ltower_holds_nc`
    （`8.6-condVI-props` ＋ `8.6-condVI-nadm-close`）。
* `TransPreservesOT`（`Trans(ST_PS) ⊆ OT_B`、§8.7 の OT 柱）
    = `Trans_STPS_OT_B`（`8.7-termination`、Wave AW で仮定ゼロ）。

これらは `8.7-termination` の private `condVIadmTower_term` /
`condVInadm_term` / `transPreservesOT_term` と同じ合成である（あちらは private
なので本ファイルで再合成する）。「一般ホスト: 未移植ブリック 3 本」＝この
3 named Prop であり、`p_8_6_Trans_fseq_condVI_uncond` に残る仮定はゼロ。

- 状態: ✅ GREEN（sorry 0）。axioms = propext/Classical.choice/Quot.sound。
-/

namespace PSS

/-! ## 3 named Prop の無条件供給（`8.7-termination` と同じ合成） -/

/-- **`CondVIAdmTowerScb`（`8.6-Trans-fseq-condVI`:220）の無条件供給**。
`8.6-condVI-adm-forms` が閉じた `CondVI_scbdec_adm_forms_v6` を
`8.6-condVI-close` の削減 `condVIAdmTowerScb_of_scbforms_v6` に通す。 -/
private theorem condVIAdmTowerScb_v6c : CondVIAdmTowerScb :=
  condVIAdmTowerScb_of_scbforms_v6 CondVI_scbdec_adm_forms_v6_holds

/-- **`CondVIExchNadm`（`8.6-Trans-fseq-condVI`:236）の無条件供給**。
`8.6-condVI-nadm-close` が閉じた `CondVIres_nadm_Ltower_v6p` を
`8.6-condVI-props` の `condVIExchNadm_holds_v6p` に通す。 -/
private theorem condVIExchNadm_v6c : CondVIExchNadm :=
  condVIExchNadm_holds_v6p CondVIres_nadm_Ltower_holds_nc

/-- **`TransPreservesOT`（`8.6-Trans-fseq-condVI`:247）の無条件供給**。
§8.7 の OT 柱 `Trans_STPS_OT_B`（`8.7-termination`、Wave AW で仮定ゼロ）と同一形。 -/
private theorem transPreservesOT_v6c : TransPreservesOT :=
  fun M hM => Trans_STPS_OT_B M hM

/-! ## 原文の命題（無条件） -/

/-- **§8.6 命題（条件 (VI) の下での `Trans` と基本列の交換関係）— 無条件版**
（原文 `tmp/content.md` 5484、Isabelle 逐語 `p_8_6_Trans_fseq_condVI`
＝ `isabelle/pss_paper.thy`:2218）。

`8.6-Trans-fseq-condVI` の `p_8_6_Trans_fseq_condVI` から 3 つの名前付き仮定
（`CondVIAdmTowerScb` / `CondVIExchNadm` / `TransPreservesOT`）を落とした双子。
3 本とも上の `_v6c` 供給で無条件に埋まるので、残る仮定は
`M ∈ ST_PS ∩ RT_PS`・`monoT M`・`n ∈ ℕ₊`・`j₁ > 1`・条件 (VI) の
原文どおりの前提のみ。

`M ∈ ST_PS ∩ PT_PS`、`n ∈ ℕ₊`、`j₀ = parent M 0 (Lng M - 1)`、`j₁ > 1`、
条件 (VI) の下で、`j₀` が `M` 許容なら `m_n := n-2`、非許容なら `m_n := n-1` と置くと:

* (1) `m_n = -1`（＝ `n = 1` かつ `j₀` 許容）なら、ある `k` が存在して
  `1 < k ≤ M_{1,j₁}+1` かつ `Trans(M[n]) = Trans(M)[0]^k`;
* (2) `m_n ≥ 0` なら `Trans(M[n]) = Trans(M)[m_n]`;
* (3) `Trans(M[n]) < Trans(M)`。

**訂正**: なし（A34/A37 は取り下げ済＝原文は真。A23 は `operB` の定義側のみ）。 -/
theorem p_8_6_Trans_fseq_condVI_uncond (M : PS) (n : ℕ)
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
  p_8_6_Trans_fseq_condVI M n condVIAdmTowerScb_v6c condVIExchNadm_v6c
    transPreservesOT_v6c hST hR hmono hn hj₁ hcond

#print axioms condVIAdmTowerScb_v6c
#print axioms condVIExchNadm_v6c
#print axioms transPreservesOT_v6c
#print axioms p_8_6_Trans_fseq_condVI_uncond

end PSS
