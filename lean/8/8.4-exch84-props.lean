import «8».«8.4-Trans-fseq-condIII-IV»
import «8».«8.5-exchV-props»
import «8».«8.6-trailing-principal-annihilable»
import «7».«7.2-scb-fseq»
import «7».«7.2-add-scb»
import «7».«7.2-scb-compose»

/-!
# §8.4 `Exch84_*` の named Prop の解消（drop-in）

- 原文: `tmp/content.md` §8.4（条件(III)か(IV)の下での `Trans` と基本列の交換関係）と
  §5.3 第3項（右端に行1の親が無いときの `oper`）。
- 対象: ビルド済み «8».«8.4-Trans-fseq-condIII-IV» が green-modulo に残した 2 本の
  named Prop（`«8».«8.7-fseq-descend»` の `FseqDesc_exchIII` / `FseqDesc_exchIV` は
  «8».«8.7-fseq-descend-props» がこの 2 本から作っている）。

  | Prop | 本ファイル | 状態 |
  |---|---|---|
  | `Exch84_condIIIIV_producer` | `Exch84_condIIIIV_producer_holds` | ⚠️ `Exch84_condIIIIV_pkg` 上 |
  | `Exch84_condIIIIV_noParent` | `Exch84_condIIIIV_noParent_holds` | ⚠️ `Exch84_noParent_domTag` 上 |

  no-parent 脚（条件(III)/(IV) 両方）は **`domTag` の 1 事実まで完全に落ちた**。
  producer は Isabelle の最終ルート（layerC）の束 `oi5_IIIIV_pkg` に落ちる。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- 訂正: なし。A32 は取り下げ済（`corrections-old.md`:101）。`d13x_*`
  (pss_wip.thy:62328/62514/62656) は仮定束が空虚で **RETRACTED**（同 :78648）＝
  本ファイルは移植先ファイルと同じく `d4vx_core`/`w84x_` ルートのみを使う。

## Isabelle 設計図と本ファイルの分担

### (1) producer

エンジン `w84x_exchange13_core` (layerB/pss_wip.thy:79789) は移植先ファイルで
`exchange13_core_e34` として済んでいる。その producer は Isabelle では
`oi5_IIIIV_pkg` (layerC/pss_scratch.thy:1213)＝REGS (`mcx_regS`) / REGSP
(`slx37_regSP_uncond`) / RUN (`wgx37_m0run_of_e1ge`＋`e1x_e1ge_uncond`) を
discharge 済みの束で、`ltJ` (`s84x_jm3 M < transJm1 M`) の下で `inner`/`k1`/
`mnform` と 2 本の底事実 base0 `D_{ub} 0_B <_B A₀`、base1' `A₀ <_B ins 0_B`
(`crx_base0_of_run`/`crx_base1_of_nest`、condIV は `cnv_*`) を出す。
`Exch84_condIIIIV_pkg` はその出力を Lean の語彙に写したもの（`ins` は `d4vx_ins`
の flat 則で抽象化。`fO` は `d13x_fseq_condIII`＋`d4vx_core_flat` で
`oi5_IIIIV_pkg` の使用側が組む形。`ltJ` の分岐（condIII は `jm1eq`＋
`m_8_4_oper_props_1(1)`、非 admeq condIV は `cnv_condIV_ltJ`）は pkg の内側）。

**本ファイルの差分**は、Isabelle 側で engine 呼び出し側
(`w84x_condIII_exchange13_of_sliceregs` wip:80238 / `y3h_LbaseH_uncond`
scratch:15342) が担う底事実の変換である:
- producer の `base1` `A₀ <_B ins (D_{ub} 0_B)` ← base1' ＋ `ins` 単調性、
- producer の `Lbase` `D_{ub} 0_B ≤_B ins 0_B` ← base0 ＋ base1' の推移律。
すなわち `Lbase`（Isabelle が最後まで名前付き残差 `LbaseH` として引きずり、
`y3h_LbaseH_uncond` で初めて閉じたもの）は **pkg の底 2 事実から無条件に従う**。

### (2) no-parent 脚

Isabelle `npx_noParentPred` (wip:101595, condIII) / `dpx_exchIV_noParent`
(同 :106063, condIV)。両者は同一構造で、本ファイルは **両方を完全移植**した:

1. `N[m] = Pred N`（全ての `m`）＝ `npx_oper_noParent_Pred` (同 :101281)。
   条件(III)/(IV) は `N_{1,j₁} > 0` を含むので `i₁ = 1`、`oper` の ¬hasParent
   分岐が発火する ⟹ `oper_noParent_Pred_x84`。
2. `k = 0` の読み戻し。condIII は等式 `npx_operB_numBT0_Pred_condIII` (同 :101500)
   ⟹ `operB_numBT0_Pred_condIII_x84`、condIV は不等式
   `dpx_condIV_noParent_operB0` (同 :105911) ⟹ `noParent_operB0_condIV_x84`。
   **¬hasParent はこの 2 本では `domB (Trans N) = T_{e-1}` を作るためだけに使われる**
   ので（Isabelle も同じ構造。`npx_domB_Trans_TBv` 同 :101419 が両脚共通の
   "no-parent payload"）、本ファイルはそこだけを `Exch84_noParent_domTag` として
   露出し、残り（`c₁`/`c₂` の形、剥がし、spine 輸送、読み戻し）を全部証明する。

移植で使った Lean 資産（Isabelle 名 → Lean 名）:
* `operB_TBv_body_spine` (wip:25712) → `operB_scb_spine_below`
  («7».«7.2-scb-fseq»)。Lean 版は `domB (Trm [cp]) = TBv m` と
  `domB_operB_xseq_dom` を要求しない分だけ強い。
* `m_8_6_trailing_principal_peel` → `trailing_principal_peel`
  («8».«8.6-trailing-principal-annihilable»)。
* `m_8_5_scbdec_c1_shape` (wip:51286) → `c1_shape_holds`（«8».«8.5-exchV-props»
  が `ExchV_scbdec_c1_shape` を無条件 discharge 済み）。
* `s84c2_Trans_c2_decomp` / `trans_surgery_localized` (wip:23635) →
  `trans_surgery_x84`（`replaceScb_spec` が 1 つの対 `(s,b)` で `Trans (Pred M)`
  側と `Trans M` 側を同時に出すので Isabelle の uniqueness 段は不要）。
* `c4dx_condIV_c2body_shape` / `cnv_c2_shape_condIV` (wip:101719) →
  `c2_shape_condIV_x84`（Lean の `transC2Core` の定義から直接。`leftDj₀` 枝の
  分解は `SigmaB (PB t) = t` の末尾 1 個剥がし）。
* `m_7_2_add_scb_conj1/2` → `add_scb_marked` / `add_scb_replace_last`
  («7».«7.2-add-scb»)、`scb_Dpt_lift` → `scb_compose_dprin`、
  `scx_scb_compose` → `scb_compose`（«7».«7.2-scb-compose»）、
  `m_7_flatBT_inj` → `flatBT_injective`、`lessBT_addBT_self` は同名。

`Exch84_noParent_domTag` を残した理由: Isabelle `npx_domB_Trans_TBv` は
`domB_classify_RN` ＋ `s84c3_RightAnces_chain` ＋ `npx_le0_last_entry_ge` で
証明されるが、Lean 側の `domTag` 分類器（`rnDom_classify`、
«7».«7.2-scb-unique»）は `private` で、`RightAnces` の chain 不変量
（各元が `j₁` の `le0` 祖先の行1値であること）も未整備。
«7».«7.4-RightAnces-RightNodes» の `RightAnces_RightNodes` は在る。

- 依存（すべてビルド済み）: «8».«8.4-Trans-fseq-condIII-IV»（`Exch84_*` の Prop
  本体・`coreTower_e34`・推移的に `lessBT_linear_trans` / `scbext_lessBT`）、
  «8».«8.5-exchV-props»（`c1_shape_holds`、推移的に «7».«7.3-Trans-welldefined»
  ＝ `replaceScb_spec` / `Trans_Mark_invariant` / `Trans_Mark_mono_equations` /
  `transC2Core_properties`、«7».«7.3-c1-c2-order» ＝ `transC1_single_principal` /
  `principal_reconstruct`）、«8».«8.6-trailing-principal-annihilable»
  （`trailing_principal_peel`）、«7».«7.2-scb-fseq»（`operB_scb_spine_below`）、
  «7».«7.2-add-scb»、«7».«7.2-scb-compose»。
-/

namespace PSS

/-! ## 1. `<_B` / `≤_B` の小補題（移植先ファイルの private 版の再掲） -/

/-- Isabelle `b1x_less_le_trans`。 -/
private theorem lessBT_leBT_trans_x84 {a b c : BT}
    (h1 : lessBT a b = true) (h2 : leBT b c = true) : lessBT a c = true := by
  rcases Bool.or_eq_true _ _ |>.mp h2 with h | h
  · exact lessBT_linear_trans a b c h1 h
  · rw [eq_of_beq h] at h1; exact h1

/-- `0_B <_B D_v a`。 -/
private theorem lessBT_zero_Dprin_x84 (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-- Isabelle `c4cx_d4vx_ins_mono`。 -/
private theorem ins_mono_x84 {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) {X Y : BT} (h : lessBT X Y = true) :
    lessBT (ins X) (ins Y) = true := by
  refine scbext_lessBT (s := s0) (b := b0) (cp := .db ub X) (cp' := .db ub Y) ?_ ?_ hb0 ?_
  · rw [hflat X]; rfl
  · rw [hflat Y]; rfl
  · simp [lessBP, h]

/-! ## 2. producer の残差（Isabelle `oi5_IIIIV_pkg` の出力そのもの） -/

/-- Isabelle `oi5_IIIIV_pkg` (layerC/pss_scratch.thy:1213) ＋ `ltJ` の分岐 ＋
`d13x_fseq_condIII`／`d4vx_core_flat` による `operB` 閉形式。

`Exch84_condIIIIV_producer` との差は最後の 2 本だけ: producer の `base1`
`A₀ <_B ins (D_{ub} 0_B)` と `Lbase` `D_{ub} 0_B ≤_B ins 0_B` の代わりに、
Isabelle の pkg が実際に出す base1' `A₀ <_B ins 0_B` を持つ。 -/
def Exch84_condIIIIV_pkg : Prop :=
  ∀ M : PS, STPS M → monoT M = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    hasParent M 1 (Lng M - 1) = true →
    ∃ (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞) (s0 b0 s1 b1 : List Sym),
      -- `d4vx_ins_flat`: 挿入段の flat 則（`b0` は全 `RP`）
      (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) ∧
      (∀ x ∈ b0, x = Sym.rp) ∧
      (∀ x ∈ b1, x = Sym.rp) ∧
      -- `operB` 閉形式（`0_B` 種の塔、一段深い）
      (∀ k, flatBT (operB (Trans M) (numBT k))
        = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1) ∧
      -- `mnform`: `M[m]` の閉形式（`A0` 種の塔）
      (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
        = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1) ∧
      -- `base0` / `base1'`
      lessBT (Dprin ub BZero) A0 = true ∧
      lessBT A0 (ins BZero) = true

/-- `Exch84_condIIIIV_producer` の drop-in（house pattern）。
Isabelle の底 2 事実 base0/base1' から、engine が要る `base1`/`Lbase` を作る。 -/
theorem Exch84_condIIIIV_producer_holds (h : Exch84_condIIIIV_pkg) :
    Exch84_condIIIIV_producer := by
  intro M hST hmono hj1 hcond hp
  obtain ⟨ins, A0, e3, ub, s0, b0, s1, b1, hflat, hb0, hb1, fO, fM, base0, base1'⟩ :=
    h M hST hmono hj1 hcond hp
  refine ⟨ins, A0, e3, ub, s0, b0, s1, b1, hflat, hb0, hb1, fO, fM, base0, ?_, ?_⟩
  · -- `base1`: `A₀ <_B ins 0_B <_B ins (D_{ub} 0_B)`
    exact lessBT_linear_trans _ _ _ base1'
      (ins_mono_x84 hflat hb0 (lessBT_zero_Dprin_x84 ub BZero))
  · -- `Lbase`: `D_{ub} 0_B <_B A₀ <_B ins 0_B`
    have hlt : lessBT (Dprin ub BZero) (ins BZero) = true :=
      lessBT_linear_trans _ _ _ base0 base1'
    simp [leBT, hlt]

/-! ## 3. no-parent 脚: `oper` の崩落 -/

/-- Isabelle `npx_oper_noParent_Pred` (layerB/pss_wip.thy:101281)。
`j₁ > 0`、行1の右端成分が非零（したがって `i₁ = 1`）、行1の親なし ⟹ `oper` は
全ての `m` で `Pred N` を返す（原文 §5.3 第3項）。 -/
private theorem oper_noParent_Pred_x84 {N : PS} {m : ℕ}
    (j1gt : 0 < Lng N - 1)
    (epos : 0 < entry N 1 (Lng N - 1))
    (nhp : hasParent N 1 (Lng N - 1) = false) :
    oper N m = Pred N := by
  have hj1 : ¬ (Lng N - 1 = 0) := by omega
  have he : ¬ (entry N 1 (Lng N - 1) = 0) := by omega
  have hi1 : idx1 N (Lng N - 1) = 1 := by simp [idx1, epos]
  simp [oper, hj1, he, hi1, nhp]

/-- 条件(III)/(IV) はいずれも `N_{1,j₁} > 0` を含む。 -/
private theorem condIIIIV_entry1_pos_x84 {N : PS}
    (hc : transCondIII N = true ∨ transCondIV N = true) :
    0 < entry N 1 (Lng N - 1) := by
  rcases hc with h | h
  · simp [transCondIII, lastIdx] at h; omega
  · simp [transCondIV, lastIdx] at h; omega

/-! ## 4. no-parent 脚: 共通の setup と手術対 -/

/-- setup: `0 < transJ1 N` と `transT1 N ≠ 0_B`（Isabelle は
`Trans_Mark_invariant_aux` ＋ `Lng (Pred N) ≠ 1`）。 -/
private theorem setup_x84 {N : PS} (hR : RTPS N) (hj1 : 1 < Lng N - 1) :
    0 < transJ1 N ∧ transT1 N ≠ BZero := by
  have hlen : 1 < Lng N := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := by
    simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred N) = false := by
    simp [zeroT, hLP]; omega
  have T1' : Trans (Pred N) ≠ BZero :=
    (Trans_Mark_invariant (Pred N) (RTPS_Pred N hR)).2.1 nzP
  exact ⟨by simp [transJ1, lastIdx]; omega, by simpa [transT1] using T1'⟩

/-- Isabelle `s84c2_Trans_c2_decomp` / `trans_surgery_localized` (wip:23635)。
`replaceScb_spec` が 1 つの対 `(s,b)` で両側の scb 分解を同時に出す。 -/
private theorem trans_surgery_x84 (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hj₁ : 0 < transJ1 M) (ht₁ : transT1 M ≠ BZero) :
    transC2 M ∈ T_B ∧ ∃ s b, scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (transC2 M)) b := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj₁; omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (transJm1 M) := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using Marked_Pred_Adm M hM hlen hp
  have hinv := (Trans_Mark_invariant (Pred M) hpredR).2.2 _ hmarked
  have ht₁TB : Trans (Pred M) ∈ T_B := (Trans_Mark_invariant (Pred M) hpredR).1
  have hc₁TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent, lastIdx] using hinv.1
  have hmb : (Trans (Pred M), transC1 M) ∈ MarkedB := by
    simpa [transT1, transC1, transJm1, transJ0, lastParent] using hinv.2
  have hc₁P : ∃ p, transC1 M = .trm [p] := by
    have h := principal_reconstruct (transC1_single_principal M hR hmono hj₁ ht₁)
    exact ⟨.db (transV M) (transT2 M), by simpa [Dprin] using h⟩
  have hprops := transC2Core_properties M (transC1 M) hc₁TB hc₁P
  have hc₂TB : transC2 M ∈ T_B := by
    simpa [transC2, transV, transT2] using hprops.1
  have hc₂P : ∃ p, transC2 M = .trm [p] := by
    simpa [transC2, transV, transT2] using hprops.2
  obtain ⟨s, b, hd₁, _hflat, hd₂⟩ :=
    replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P hmb
  refine ⟨hc₂TB, s, b, hd₁, ?_⟩
  have hTM : Trans M = replaceScb (Trans (Pred M)) (transC1 M) (transC2 M) := by
    have heq := (Trans_Mark_mono_equations M hR hlen hmono).1
    have ht₁b : (Trans (Pred M) == BZero) = false := by
      simpa [beq_iff_eq, transT1] using ht₁
    simpa [transT1, transC1, transC2, transV, transT2, transJm1, transJ0,
      lastParent, ht₁b] using heq
  rw [hTM]
  exact hd₂

/-! ## 5. no-parent 脚の残差（Isabelle `npx_domB_Trans_TBv`, wip:101419） -/

/-- Isabelle `npx_domB_Trans_TBv` (layerB/pss_wip.thy:101419) の `domTag` 版
（Lean の spine 輸送 `operB_scb_spine_below` が `domTag` で述べられているため）。
**両脚（condIII/condIV）で `¬hasParent` が使われる唯一の場所**。

Isabelle の証明: `¬hasParent N 1 j₁` は「`j₁` の全 `le0` 祖先 `j` が
`N_{1,j} ≥ N_{1,j₁}`」と同値（`npx_le0_last_entry_ge`。さもなくば極大の低祖先が
行1の親になる）。`RightAnces` の chain 不変量 (`s84c3_RightAnces_chain`) と
`m_7_4_RightAnces_RightNodes` により `Trans N` の右端 spine 値は全てその祖先鎖上に
乗るので、全て `≥ e` かつ末尾 `= e ≠ 0` ⟹ `rnNatShape` が偽 ⟹ 分類器
`domB_classify_RN` が `T_{e-1}` を返す。 -/
def Exch84_noParent_domTag : Prop :=
  ∀ N : PS, RTPS N → monoT N = true → 0 < Lng N - 1 →
    0 < entry N 1 (Lng N - 1) →
    hasParent N 1 (Lng N - 1) = false →
    domTag (Trans N) = .below (entry N 1 (Lng N - 1) - 1)

/-! ## 6. `k = 0` 読み戻し — 条件(III)（Isabelle `npx_operB_numBT0_Pred_condIII`） -/

/-- Isabelle `npx_operB_numBT0_Pred_condIII` (layerB/pss_wip.thy:101500)。
`¬hasParent` は `hdt` に吸収済み（Isabelle の証明でもそこにしか効かない）。

`c₂ = D_w(t₂ + D_e 0)` は clean-descent の `[0]` 一歩で `c₁ = D_w t₂` に剥がれ
（`w ≥ e` は条件(III) の不等式そのもの、`j₋₁ = j₀` 経由）、`T_{e-1}` 定義域の
spine 輸送が `flat (operB (Trans N) [0])` を `s₁ (c₂) b₁` から `s₁ (c₁) b₁`
＝ `flat (Trans (Pred N))` に書き換える。 -/
private theorem operB_numBT0_Pred_condIII_x84 {N : PS} (hR : RTPS N)
    (hmono : monoT N = true) (hj1 : 1 < Lng N - 1) (cIII : transCondIII N = true)
    (hdt : domTag (Trans N) = .below (entry N 1 (Lng N - 1) - 1)) :
    operB (Trans N) (numBT 0) = Trans (Pred N) := by
  obtain ⟨J1pos, T1⟩ := setup_x84 hR hj1
  obtain ⟨vw, c1eq, -, -⟩ := c1_shape_holds N hR (RTPS_TPS N hR) hmono J1pos T1
  obtain ⟨hc₂TB, s, b, d1, d2⟩ := trans_surgery_x84 N hR hmono J1pos T1
  set w := entry N 1 (transJm1 N) with hw
  set e := entry N 1 (Lng N - 1) with he
  -- `w ≥ e`（条件(III) の不等式 ＋ `j₋₁ = j₀`）
  have hIII := cIII
  simp [transCondIII, lastIdx] at hIII
  have jm1eq : transJm1 N = lastParent N := by
    simp [transJm1, transJ0, Adm, hIII.2]
  have wge : e ≤ w := by rw [hw, jm1eq]; omega
  -- `c₂` の形
  have c2eq : transC2 N = Dprin (w : ℕ∞) (addBT (transT2 N) (Dprin (e : ℕ∞) BZero)) := by
    rw [← vw]; simp [transC2, transC2Core, cIII, lastIdx, he]
  -- 剥がし
  have peel : operB (BT.trm [BP.db (w : ℕ∞) (addBT (transT2 N) (Dprin (e : ℕ∞) BZero))])
      (numBT 0) = BT.trm [BP.db (w : ℕ∞) (transT2 N)] := by
    simpa [Dprin] using trailing_principal_peel (transT2 N) w e (Or.inr wge)
  -- 出現と `dfree`
  have hocc : flatBT (Trans N)
      = s ++ flatBP (BP.db (w : ℕ∞) (addBT (transT2 N) (Dprin (e : ℕ∞) BZero))) ++ b := by
    have h := d2.1
    rw [c2eq] at h
    simpa [Dprin, flatBT] using h
  have hdfp : dfree_BP (BP.db (w : ℕ∞) (addBT (transT2 N) (Dprin (e : ℕ∞) BZero))) = true := by
    have h := hc₂TB
    rw [c2eq] at h
    simpa [T_B, Dprin, dfree_BT, dfree_BPList] using h
  -- spine 輸送 ＋ 読み戻し
  have htr := operB_scb_spine_below hocc d2.2.2 hdfp hdt peel
  have hP : flatBT (Trans (Pred N)) = s ++ flatBP (BP.db (w : ℕ∞) (transT2 N)) ++ b := by
    have h := d1.1
    rw [c1eq] at h
    simpa [Dprin, flatBT] using h
  exact flatBT_injective (by rw [htr, hP])

/-! ## 7. `k = 0` 読み戻し — 条件(IV)（Isabelle `dpx_condIV_noParent_operB0`） -/

private theorem condIV_others_false_x84 {N : PS} (cIV : transCondIV N = true) :
    transCondI N = false ∧ transCondIII N = false ∧ transCondV N = false ∧
      transCondVI N = false := by
  simp [transCondIV] at cIV
  obtain ⟨⟨hpos, hle⟩, hadm⟩ := cIV
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [transCondI]; omega
  · simp [transCondIII, hadm]
  · simp [transCondV]; omega
  · simp [transCondVI]; omega

private theorem SigmaB_single_x84 (t : BT) : SigmaB [t] = t := by
  cases t; simp [SigmaB, untrm]

private theorem SigmaB_append_x84 (xs ys : List BT) :
    SigmaB (xs ++ ys) = addBT (SigmaB xs) (SigmaB ys) := by
  simp [SigmaB, addBT, List.flatMap_append]

private theorem SigmaB_PB_x84 (t : BT) : SigmaB (PB t) = t := by
  cases t with
  | trm ps => simp [SigmaB, PB, untrm, List.flatMap_map]

private theorem take_getD_last_x84 {α : Type _} (l : List α) (d : α)
    (h : l ≠ []) : l.take (l.length - 1) ++ [l.getD (l.length - 1) d] = l := by
  rcases List.eq_nil_or_concat l with rfl | ⟨xs, x, rfl⟩
  · exact absurd rfl h
  · simp [List.getD_eq_getElem?_getD]

private theorem PB_mem_principal_x84 {t c : BT} (h : c ∈ PB t) :
    c = Dprin (bpHeadV c) (bpHeadT c) := by
  simp [PB] at h
  obtain ⟨p, -, rfl⟩ := h
  cases p with
  | db v a => simp [Dprin, bpHeadV, bpHeadT]

private theorem PB_ne_nil_x84 {t : BT} (h : t ≠ BZero) : PB t ≠ [] := by
  cases t with
  | trm ps =>
      cases ps with
      | nil => exact absurd rfl h
      | cons q qs => simp [PB, untrm]

private theorem dfree_BPList_append_x84 (as bs : List BP) :
    dfree_BPList (as ++ bs) = (dfree_BPList as && dfree_BPList bs) := by
  induction as with
  | nil => simp [dfree_BPList]
  | cons p ps ih => simp [dfree_BPList, ih, Bool.and_assoc]

private theorem dfree_addBT_x84 (a b : BT) :
    dfree_BT (addBT a b) = (dfree_BT a && dfree_BT b) := by
  cases a; cases b; simp [addBT, dfree_BT, dfree_BPList_append_x84]

/-- Isabelle `c4dx_condIV_c2body_shape` / `cnv_c2_shape_condIV` (wip:101719)。
条件(IV) では `c₂` の body は一段深い `t₃ + D_{u}(t₄ + D_e 0)`。 -/
private theorem c2_shape_condIV_x84 {N : PS} (cIV : transCondIV N = true) :
    ∃ t3 t4 : BT,
      transC2 N = Dprin (transV N)
        (addBT t3 (Dprin (entry N 1 (lastParent N) : ℕ∞)
          (addBT t4 (Dprin (entry N 1 (Lng N - 1) : ℕ∞) BZero)))) ∧
      ((t3 = transT2 N ∧ t4 = transT2 N) ∨
        transT2 N = addBT t3 (Dprin (entry N 1 (lastParent N) : ℕ∞) t4)) := by
  obtain ⟨hI, hIII, hV, hVI⟩ := condIV_others_false_x84 cIV
  by_cases hz : transT2 N = BZero
  · refine ⟨BZero, BZero, ?_, Or.inl ⟨hz.symm, hz.symm⟩⟩
    simp [transC2, transC2Core, hI, hIII, hV, hVI, hz, lastIdx, addBT, BZero, Dprin]
  · by_cases hlft : (bpHeadV ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero)
        == (entry N 1 (lastParent N) : ℕ∞)) = true
    · refine ⟨SigmaB ((PB (transT2 N)).take ((PB (transT2 N)).length - 1)),
        bpHeadT ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero), ?_, Or.inr ?_⟩
      · show transC2Core N (transV N) (transT2 N) = _
        simp only [transC2Core, hI, hIII, hV, hVI, Bool.or_self, lastIdx, if_false,
          Bool.false_eq_true, hlft, beq_iff_eq, if_true]
        rw [if_neg (by simp [hz] : ¬((transT2 N == BZero) = true))]
      · -- 末尾 principal を 1 個剥がす: `t₂ = Σ(take J) +_B D_u t₄`
        have hne : PB (transT2 N) ≠ [] := PB_ne_nil_x84 hz
        have hlen : (PB (transT2 N)).length - 1 < (PB (transT2 N)).length := by
          have := List.length_pos_of_ne_nil hne; omega
        have hmem : (PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero
            ∈ PB (transT2 N) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
            Option.getD_some]
          exact List.getElem_mem hlen
        have hprin := PB_mem_principal_x84 hmem
        have hsplit := take_getD_last_x84 (PB (transT2 N)) BZero hne
        have huv : bpHeadV ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero)
            = (entry N 1 (lastParent N) : ℕ∞) := by simpa using hlft
        calc transT2 N
            = SigmaB (PB (transT2 N)) := (SigmaB_PB_x84 _).symm
          _ = SigmaB ((PB (transT2 N)).take ((PB (transT2 N)).length - 1)
                ++ [(PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero]) := by
                rw [hsplit]
          _ = addBT (SigmaB ((PB (transT2 N)).take ((PB (transT2 N)).length - 1)))
                (SigmaB [(PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero]) :=
                SigmaB_append_x84 _ _
          _ = addBT (SigmaB ((PB (transT2 N)).take ((PB (transT2 N)).length - 1)))
                ((PB (transT2 N)).getD ((PB (transT2 N)).length - 1) BZero) := by
                rw [SigmaB_single_x84]
          _ = _ := by rw [← huv]; exact congrArg _ hprin
    · refine ⟨transT2 N, transT2 N, ?_, Or.inl ⟨rfl, rfl⟩⟩
      show transC2Core N (transV N) (transT2 N) = _
      simp only [transC2Core, hI, hIII, hV, hVI, Bool.or_self, lastIdx, if_false,
        Bool.false_eq_true, hlft, beq_iff_eq]
      rw [if_neg (by simp [hz] : ¬((transT2 N == BZero) = true))]

/-- Isabelle `dpx_condIV_noParent_operB0` (layerB/pss_wip.thy:105911)。
条件(IV) の入れ子 `c₂` では剥がしの対象が一段内側の `D_u(t₄ + D_e 0)` になるので、
`(sI,bI)` は `add_scb_marked` ＋ `add_scb_replace_last`（＝ Isabelle
`m_7_2_add_scb_conj1/2`）で作り、`scb_compose_dprin`（`scb_Dpt_lift`）と
`scb_compose`（`scx_scb_compose`）で深い対に合成する。形の二分岐（fold / grow）が
両方向を閉じる。 -/
private theorem noParent_operB0_condIV_x84 {N : PS} (hR : RTPS N)
    (hmono : monoT N = true) (hj1 : 1 < Lng N - 1) (cIV : transCondIV N = true)
    (hdt : domTag (Trans N) = .below (entry N 1 (Lng N - 1) - 1)) :
    leBT (Trans (Pred N)) (operB (Trans N) (numBT 0)) = true := by
  obtain ⟨J1pos, T1⟩ := setup_x84 hR hj1
  obtain ⟨vw, c1eq, -, -⟩ := c1_shape_holds N hR (RTPS_TPS N hR) hmono J1pos T1
  obtain ⟨hc₂TB, s, b, d1, d2⟩ := trans_surgery_x84 N hR hmono J1pos T1
  obtain ⟨t3, t4, c2eq, dich⟩ := c2_shape_condIV_x84 cIV
  set u := entry N 1 (lastParent N) with hu
  set e := entry N 1 (Lng N - 1) with he
  -- `u ≥ e`（条件(IV) の不等式）
  have hIV := cIV
  simp [transCondIV, lastIdx] at hIV
  have uge : e ≤ u := by rw [he, hu]; omega
  -- `T_B` / `dfree` を `c₂ ∈ T_B` から読み出す
  have hdf := hc₂TB
  rw [c2eq] at hdf
  simp only [T_B, Set.mem_setOf_eq, Dprin, dfree_BT, dfree_BPList, dfree_BP,
    dfree_addBT_x84, Bool.and_eq_true, and_true] at hdf
  obtain ⟨-, ht3df, -, ht4df, -⟩ := hdf
  have ht3TB : t3 ∈ T_B := by simpa [T_B] using ht3df
  have hcpdf : dfree_BP (BP.db (u : ℕ∞) (addBT t4 (Dprin (e : ℕ∞) BZero))) = true := by
    simp [dfree_BP, dfree_addBT_x84, ht4df, Dprin, BZero, dfree_BT, dfree_BPList]
  have hcpTB : (BT.trm [BP.db (u : ℕ∞) (addBT t4 (Dprin (e : ℕ∞) BZero))]) ∈ T_B := by
    simpa [T_B, dfree_BT, dfree_BPList] using hcpdf
  have hDut4TB : Dprin (u : ℕ∞) t4 ∈ T_B := by
    simpa [T_B, Dprin, dfree_BT, dfree_BPList, dfree_BP] using ht4df
  -- 内側の一様な穴の対 `(sI, bI)`
  obtain ⟨sI, bI, hdI⟩ :=
    add_scb_marked t3 (BT.trm [BP.db (u : ℕ∞) (addBT t4 (Dprin (e : ℕ∞) BZero))])
      ht3TB hcpTB ⟨_, rfl⟩
  have hdI' : scb_decomp (addBT t3 (Dprin (u : ℕ∞) t4)) sI
      (flatBT (Dprin (u : ℕ∞) t4)) bI :=
    add_scb_replace_last t3 _ (Dprin (u : ℕ∞) t4) sI bI ht3TB hcpTB ⟨_, rfl⟩
      hDut4TB ⟨_, rfl⟩ hdI
  -- `D_v(·)` 持ち上げ
  have hptb : isPTB_str (flatBT (BT.trm [BP.db (u : ℕ∞) (addBT t4 (Dprin (e : ℕ∞) BZero))])) :=
    ⟨_, hcpdf, by simp [flatBT]⟩
  have hptb' : isPTB_str (flatBT (Dprin (u : ℕ∞) t4)) := by
    refine ⟨.db (u : ℕ∞) t4, ?_, by simp [Dprin, flatBT]⟩
    simpa [T_B, Dprin, dfree_BT, dfree_BPList] using hDut4TB
  have dL : scb_decomp (transC2 N) (Sym.dsym (transV N) :: sI)
      (flatBT (BT.trm [BP.db (u : ℕ∞) (addBT t4 (Dprin (e : ℕ∞) BZero))])) bI := by
    rw [c2eq]
    exact scb_compose_dprin _ _ _ _ _ (by simpa [Dprin] using hdI) hptb
  have dL' : scb_decomp (Dprin (transV N) (addBT t3 (Dprin (u : ℕ∞) t4)))
      (Sym.dsym (transV N) :: sI) (flatBT (Dprin (u : ℕ∞) t4)) bI :=
    scb_compose_dprin _ _ _ _ _ hdI' hptb'
  -- 深い対
  have hc₂P : ∃ p, transC2 N = BT.trm [p] := ⟨_, by rw [c2eq]; rfl⟩
  have dDeep := scb_compose (Trans N) (transC2 N) s (Sym.dsym (transV N) :: sI)
    (flatBT (BT.trm [BP.db (u : ℕ∞) (addBT t4 (Dprin (e : ℕ∞) BZero))])) bI b hc₂P d2 dL
  -- 剥がし ＋ spine 輸送
  have peel : operB (BT.trm [BP.db (u : ℕ∞) (addBT t4 (Dprin (e : ℕ∞) BZero))])
      (numBT 0) = BT.trm [BP.db (u : ℕ∞) t4] := by
    simpa [Dprin] using trailing_principal_peel t4 u e (Or.inr uge)
  have hocc : flatBT (Trans N) = (s ++ (Sym.dsym (transV N) :: sI))
      ++ flatBP (BP.db (u : ℕ∞) (addBT t4 (Dprin (e : ℕ∞) BZero))) ++ (bI ++ b) := by
    simpa [flatBT] using dDeep.1
  have htr := operB_scb_spine_below hocc dDeep.2.2 hcpdf hdt peel
  -- `flat (operB (Trans N) [0]) = s ++ flat (D_v(t₃ + D_u t₄)) ++ b`
  have fc2' : flatBT (Dprin (transV N) (addBT t3 (Dprin (u : ℕ∞) t4)))
      = (Sym.dsym (transV N) :: sI) ++ flatBT (Dprin (u : ℕ∞) t4) ++ bI := dL'.1
  have flat2 : flatBT (operB (Trans N) (numBT 0))
      = s ++ flatBT (Dprin (transV N) (addBT t3 (Dprin (u : ℕ∞) t4))) ++ b := by
    rw [htr, fc2']
    simp [Dprin, flatBT, List.append_assoc]
  have flatP : flatBT (Trans (Pred N)) = s ++ flatBT (transC1 N) ++ b := d1.1
  -- 形の二分岐
  rcases dich with ⟨h3, h4⟩ | hfold
  · -- grow: `t₃ = t₄ = t₂` ⟹ 真に増える
    have hne : Dprin (u : ℕ∞) t4 ≠ BZero := by simp [Dprin, BZero]
    have coreLt : lessBT (transT2 N) (addBT t3 (Dprin (u : ℕ∞) t4)) = true := by
      rw [h3]; exact lessBT_addBT_self _ _ hne
    have fP : flatBT (Trans (Pred N))
        = s ++ flatBP (BP.db (transV N) (transT2 N)) ++ b := by
      rw [flatP, c1eq, ← vw]; simp [Dprin, flatBT]
    have fO : flatBT (operB (Trans N) (numBT 0))
        = s ++ flatBP (BP.db (transV N) (addBT t3 (Dprin (u : ℕ∞) t4))) ++ b := by
      rw [flat2]; simp [Dprin, flatBT]
    have := scbext_lessBT fP fO d1.2.2 (by simp [lessBP, coreLt])
    simp [leBT, this]
  · -- fold: `t₂ = t₃ +_B D_u t₄` ⟹ 等式
    have : Dprin (transV N) (addBT t3 (Dprin (u : ℕ∞) t4)) = transC1 N := by
      rw [c1eq, ← vw, ← hfold]
    rw [this] at flat2
    have : operB (Trans N) (numBT 0) = Trans (Pred N) :=
      flatBT_injective (by rw [flat2, flatP])
    simp [leBT, this]

/-! ## 8. `Exch84_condIIIIV_noParent` の drop-in -/

/-- Isabelle `npx_noParentPred` (wip:101595) ＋ `dpx_exchIV_noParent` (同 :106063)
の `k = 0` 読み戻し部分を、両条件で統一した形。 -/
private theorem noParent_operB0_x84 (h : Exch84_noParent_domTag) {N : PS}
    (hR : RTPS N) (hmono : monoT N = true) (hj1 : 1 < Lng N - 1)
    (hcond : transCondIII N = true ∨ transCondIV N = true)
    (hp : hasParent N 1 (Lng N - 1) = false) :
    leBT (Trans (Pred N)) (operB (Trans N) (numBT 0)) = true := by
  have epos := condIIIIV_entry1_pos_x84 hcond
  have hdt := h N hR hmono (by omega) epos hp
  rcases hcond with cIII | cIV
  · simp [leBT, operB_numBT0_Pred_condIII_x84 hR hmono hj1 cIII hdt]
  · exact noParent_operB0_condIV_x84 hR hmono hj1 cIV hdt

/-- `Exch84_condIIIIV_noParent` の drop-in（house pattern）。
Isabelle `npx_noParentPred` / `dpx_exchIV_noParent` そのもの: `N[m] = Pred N` と
`k = 0` の読み戻しを合わせるだけ。 -/
theorem Exch84_condIIIIV_noParent_holds (h : Exch84_noParent_domTag) :
    Exch84_condIIIIV_noParent := by
  intro N m hST hmono hj1 hcond hp _hm
  refine ⟨0, ?_⟩
  rw [oper_noParent_Pred_x84 (by omega) (condIIIIV_entry1_pos_x84 hcond) hp]
  exact noParent_operB0_x84 h (STPS_RTPS N hST) hmono hj1 hcond hp

#print axioms Exch84_condIIIIV_producer_holds
#print axioms Exch84_condIIIIV_noParent_holds

end PSS
