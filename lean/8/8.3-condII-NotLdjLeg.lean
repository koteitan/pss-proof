import «8».«8.3-condII-masterCF-port»
import «8».«8.3-condII-step»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.2-condV-rightmost-parent»
import «8».«8.2-condV-VE-base»

/-!
# §8.3 条件(II) — `TV_NotLdjLeg`（`cdx_tailval_notldj`）: `¬ ldj` 分岐の `tailval`

## Isabelle 対応（名前＋行番号）

* `cdx_tailval_notldj` (layerB/pss_wip.thy:90415, ~94 行) → 本ファイルの
  `TV_NotLdjLeg_of_legs`（`TV_NotLdjLeg` Prop は «8».«8.3-condII-masterCF-port»:140 で
  既定義。house pattern でその Prop を結論の型として drop-in する）。
* `c2sx_tailval_of_reg` (layerB/pss_wip.thy:87838) → 本ファイルの新 Prop `TV_NotLdjReg`
  （`M ∈ RT_PS` ＋ `¬ ldj` ＋ `cfbx_reg`＝`VEReg` から `tailval`）。
* `cfbx_reg` (layerB/pss_wip.thy:63208) = `VEReg`（«8».«8.2-condV-VE-base»:74、逐語移植）。
* `c2sx_reach` の到達性脚 `leab` (layerB/pss_wip.thy:87666) → 私的 `condII_reach_nl`
  （«8».«8.3-condII-R3LE» の `condII_reach_r3` の複製。private は module 跨ぎ不可）。

## 🚨 依存構造の所見（`props_closed` が空である理由）

Isabelle `cdx_tailval_notldj` の証明は、**同じ束の他の残差**を内部で呼ぶ:

1. `cdx_d_le_joints` (90230) = **`TV_Dichotomy`**（未閉の残差）で trunk / branched に二分。
2. trunk ⇒ `c2sx_tailval_trunk` (87720) = **`TV_TrunkLeg`**（未閉の残差）。
3. branched + `¬ ldj` ⇒ `c2sx_tailval_of_reg` (87838)（未移植の §8.2 backpeel 脚
   ＝本ファイルの `TV_NotLdjReg`。`VE` 本体 `vcx_VE_all`/`a0x_base_VE` は
   «8».«8.2-condV-VE-base» でも未達＝残差 {BASE, STEP, RPERS}）。

すなわち `TV_NotLdjLeg` は独立な葉ではなく、`TV_Dichotomy` ＋ `TV_TrunkLeg` ＋
新脚 `TV_NotLdjReg` を**包摂**する。よって 1 ファイルでは**無条件には閉じられない**。
そこで本ファイルは Isabelle の証明骨格を忠実に移植した**還元定理**
`TV_NotLdjLeg_of_legs : TV_Dichotomy → TV_TrunkLeg → TV_NotLdjReg → TV_NotLdjLeg`
を green で bank する。これは masterCF-port の残差束から `TV_NotLdjLeg` を
`TV_NotLdjReg` に**置換可能**であること（`TV_Dichotomy`/`TV_TrunkLeg` は束に既存）を示す。

## 移植した実質内容（骨格の glue）
* `DIAG → disj → cfbx_reg`(`VEReg`) の組み立て（Isabelle 90455-90467 の branched 分岐）。
* 簡約祖先切片 `tvx_Rc M` の `DT_PS` 導出（`condII_reach_nl` + `standard_slice_Red_strongmono`
  → `DTPS_iff` で `RTPS`/`monoT`/`descendingB`）。«8».«8.3-condII-R3LE» の機構と同型。

## 依存（すべて COMMITTED 緑）
* 既存公開: `STPS_RTPS` / `RTPS_TPS` / `condII_host_basic_holds` / `Marked_Pred_Adm` /
  `standard_slice_Red_strongmono` / `DTPS_iff` / `VEReg`（`cfbx_reg`）/
  `length_Pred` / `entry_Pred` / `ancestor_basic_1` / `parent_exists_3`。
* 私的移植（`_nl`、親が昇格すべき cross-scope は "needs" 参照）: `condII_reach_nl`。
* 新 Prop（親が masterCF-port の束へ昇格・配線すべき）: `TV_NotLdjReg`。

## 状態
* ⚠️ `TV_NotLdjLeg` は**無条件には未閉**（`TV_Dichotomy`/`TV_TrunkLeg`/`TV_NotLdjReg`
  の 3 脚に還元）。`TV_NotLdjReg` は §8.2 の VE backpeel 本体で別途要移植。
* ✅ `TV_NotLdjLeg_of_legs`（sorry 0, 公理 3 個）＝Isabelle `cdx_tailval_notldj` の
  proof-skeleton を忠実に移植した還元。
-/

namespace PSS

/-- Isabelle `c2sx_reach` (layerB/pss_wip.thy:87666) の到達性脚 `leab`:
`(Pred K, a) ∈ Marked` から `leR K 0 a (Lng K - 2)`。
«8».«8.3-condII-R3LE» の `condII_reach_r3` の複製（private は module 跨ぎ不可）。
Isabelle は `Pred_RT_PS` + `le0_prefix_agree` を rtrancl 帰納で回すが、ここでは値特徴付け
`ancestor_basic_1` + `parent_exists_3` + `entry_Pred`（前者切片との接尾一致）で迂回する。 -/
private theorem condII_reach_nl (K : PS) (a : ℕ) (hKR : RTPS K) (hL : 1 < Lng K)
    (hmk : Marked (Pred K) a) (hab : a < Lng K - 2) :
    leR K 0 a (Lng K - 2) = true := by
  have hKT : TPS K := RTPS_TPS K hKR
  have hpredT : TPS (Pred K) := hmk.1
  have hpl : Lng (Pred K) = Lng K - 1 := length_Pred K hL
  have hle0P : leR (Pred K) 0 a (Lng (Pred K) - 1) = true := hmk.2.2
  have hidx : Lng (Pred K) - 1 = Lng K - 2 := by omega
  rw [hidx] at hle0P
  have hLK2 : Lng K - 2 < Lng K := by omega
  apply parent_exists_3 K a (Lng K - 2) hKT hab hLK2
  intro j hlo hhi
  have hgrowPred : entry (Pred K) 0 a < entry (Pred K) 0 j :=
    ancestor_basic_1 (Pred K) a j (Lng K - 2) hpredT hlo hhi hle0P
  have haLt : a < Lng K - 1 := by omega
  have hjLt : j < Lng K - 1 := by omega
  rw [entry_Pred K 0 a haLt, entry_Pred K 0 j hjLt] at hgrowPred
  exact hgrowPred

/-- Isabelle `c2sx_tailval_of_reg` (layerB/pss_wip.thy:87838) の Lean 形。
branched かつ `¬ ldj` の分岐で `cfbx_reg`(`VEReg`) から `tailval` を出す**未移植の
§8.2 backpeel 脚**。`MR : M ∈ RT_PS` ＋ `MP : M ∈ PT_PS`（`= T_PS ∧ monoT`。`RT_PS ⟹ T_PS`
なので `RTPS M ∧ monoT M` で両者を捕捉）。 -/
def TV_NotLdjReg : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    condII_ldj M = false →
    VEReg (tvx_d M) (tvx_Rc M) →
    CondII_tailval M

/-- Isabelle `cdx_tailval_notldj` (layerB/pss_wip.thy:90415) の proof-skeleton を
忠実に移植した**還元**。`TV_NotLdjLeg`（«8».«8.3-condII-masterCF-port»:140）を
結論の型として drop-in（house pattern）するが、Isabelle 側が内部で `cdx_d_le_joints`
(=`TV_Dichotomy`) と `c2sx_tailval_trunk` (=`TV_TrunkLeg`) を呼ぶため、それら 2 本と
未移植脚 `TV_NotLdjReg` を仮定に取る。DIAG は branched の `d = jL` 分岐で消費する。 -/
theorem TV_NotLdjLeg_of_legs
    (hDich : TV_Dichotomy) (hTrunk : TV_TrunkLeg) (hReg : TV_NotLdjReg) :
    TV_NotLdjLeg := by
  intro M hST hmono hj1 hcond hnotldj hDIAG
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hL : 1 < Lng M := by omega
  obtain ⟨hp0, hE1, hNadm, hParPos, hAdmLt, hParLt, hCond, hVI, hT2⟩ :=
    condII_host_basic_holds M hMR hmono hj1 hcond
  -- 簡約祖先切片 `tvx_Rc M` は `DT_PS`（到達性 `leab` + `standard_slice_Red_strongmono`）
  have hab : Adm M (parent M 0 (Lng M - 1)) < Lng M - 2 := by omega
  have hmk : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hMT hL hp0
  have leab : leR M 0 (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2) = true :=
    condII_reach_nl M (Adm M (parent M 0 (Lng M - 1))) hMR hL hmk hab
  have hbL2 : Lng M - 2 ≤ Lng M - 1 := by omega
  have hRcDT : DTPS (tvx_Rc M) :=
    standard_slice_Red_strongmono M (Adm M (parent M 0 (Lng M - 1))) (Lng M - 2)
      hST hab hbL2 leab
  have hRcRT : RTPS (tvx_Rc M) := ((DTPS_iff (tvx_Rc M)).mp hRcDT).1
  have hmonoRc : monoT (tvx_Rc M) = true := ((DTPS_iff (tvx_Rc M)).mp hRcDT).2.1
  have hdesc : descendingB (Br (tvx_Rc M)) = true := ((DTPS_iff (tvx_Rc M)).mp hRcDT).2.2
  -- Isabelle `cdx_d_le_joints` (=`TV_Dichotomy`) による二分岐
  rcases hDich M hST hmono hj1 hcond with htrunk | ⟨hBrne, hdle⟩
  · -- 幹: Isabelle `c2sx_tailval_trunk` (=`TV_TrunkLeg`)
    exact hTrunk M hMR hmono hj1 hcond htrunk
  · -- 枝: DIAG → disj → cfbx_reg(`VEReg`) → `c2sx_tailval_of_reg` (=`TV_NotLdjReg`)
    have hREG : VEReg (tvx_d M) (tvx_Rc M) := by
      refine ⟨hRcRT, hmonoRc, hBrne, ?_⟩
      rcases eq_or_lt_of_le hdle with hd | hd
      · exact Or.inr ⟨hd, hDIAG hBrne hd, hdesc⟩
      · exact Or.inl hd
    exact hReg M hMR hmono hj1 hcond hnotldj hREG

#print axioms TV_NotLdjLeg_of_legs

end PSS
