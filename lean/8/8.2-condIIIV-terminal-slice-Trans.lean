import «8».«8.2-condV-terminal-slice-Trans»
import «8».«8.2-standard-slice-Red-strongmono»
import «6».«6.4-mono-slice»
import «6».«6.5-Red-welldefined»

/-!
# §8.2 命題（条件(II)か(IV)の下での終切片と `Trans` の関係）

- 原文: `tmp/content.md` L3314 付近（`LastStep` の定義 L3304、命題本体 L3316）
- 訂正: **A9**（軽微、`LastStep` の添字）。原文は `J₁ := Lng(Br M)` と置きながら
  `Br(M)_{J₁}` を参照する（範囲外）ので `J₁ := Lng(Br M) - 1` が意図。さらに A9 の
  fin 形（r69）で `min` の内包に添字上界 `J < Lng(Br M)` を付す。本ファイルの
  `LastStep` は A9 訂正後の形を採用する。
- Isabelle:
  - 逐語: `p_8_2_condIIIV_terminal_slice_Trans` (isabelle/pss_paper.thy:1627)
  - `LastStep` の定義: `isabelle/pss_defs.thy:533`（A9 訂正後、上界付き）
  - 本体: `vgx_condIIIV_of_VE` (isabelle/layerB/pss_wip.thy:91228)
    ＝ 純 BT の足場 `cdx_condIIIV_scaffold` (同 90145) ＋ 切片幾何
    （`vgx_LastStep_lt_of_guard` 同 91032 / `vgx_m1_bounds` 同 91077）＋
    切片の単項性（`vgx_slice_{N,Np,Mp}_mono` 同 91136/91120/91098）＋
    切片の principal 表示（`vgx_slice_princ` 同 91167）
  - 未移植: `VE2`/`VE3`/`VE4`（値方程式の三つ組）。Isabelle 側は
    `vg7x_condIIIV_of_DT` (同 97539) / `hqx_condIIIV_of_DT` へ続く back-peel 連鎖
    （`vg2x_VE34` 系、約 14000 行）。単一ファイルの射程外のため、本ファイルは
    条件(V) 双子（`condV_terminal_slice_Trans_modVE`）と同じ扱いで、
    `VE2`/`VE3`/`VE4` を名前付き仮定に持つ `_modVE` 形までを緑で提供する。
- 依存: `8.2-condV-terminal-slice-Trans`（`Trans_principal_head`）、
  `8.2-condV-rightmost-parent`（`le0_monoT_seg_into_list`）、
  `8.2-standard-slice-Red-strongmono`（`DTPS`/`DTPS_iff`）、
  `6.4-mono-slice`（`mono_slice`）、
  `6.4-FirstNodes-TrMax-Joints`（`FirstNodes_TrMax_Joints`/`TrMax_bound`）、
  `6.5-Red-welldefined`（`Joints_nextR_FirstNodes`）、
  `6.6-ancestor-slice-Red-IncrFirst`（`ancestor_slice_Red_IncrFirst`）、
  `7.3-Trans-IncrFirst-Red`（`Trans_Red`）

## `fin` について（Isabelle からの改善）

Isabelle の `vgx_condIIIV_of_VE` は名前付き仮定
`fin : finite {J. J < Lng (Br M) ∧ …}` を持つが、**これは A9 fin 形以前の
（上界の無い）`LastStep` 定義の遺物であり、現在の Isabelle 定義の下では
その集合は `{..< Lng (Br M)}` の部分集合ゆえ常に有限＝`fin` は自明に真**である
（`fin` は `vgx_LastStep_lt_Lng_Br` 内の `Min_le` にしか使われない）。
Lean では `LastStep` を `List.find?`＋`getD` で全域関数として定義するため
`min` の well-defined 性という問題自体が生じず、`fin` は**不要**になる。
実際 `LastStep_lt_Lng_Br`（下記）は `Br M ≠ []` のみから**無条件に**従う
（Isabelle 版は `gt`＋`fin` を要した）。したがって本ファイルの公開定理に
`fin` は現れない。

## `LastStep` の忠実性（本ファイルが定義を新設する点に注意）

`LastStep` は Lean 側に**まだ存在しなかった**（既存ファイルでの言及はすべて
コメントのみ）ので本ファイルで新設する。全域化（`min` の集合が空のときの
既定値を `J₁` とする）が Isabelle の `Min` と食い違わないことを数値検証した
（`python/audit_82_condIIIV.py`）:
- 集合が非空の 19453 host すべてで Isabelle の `Min` と**完全一致**（不一致 0）。
- 集合が空＝Isabelle の `Min` が junk になる host は 42961 件あるが、**そのうち
  本命題の幾何的仮定を満たすものは 0 件**（原文脚注[61]「`J = J₁` が条件を満たす
  ため `min` が存在する」を裏づける）。
- `LastStep M < Lng(Br M)` の反例は 62414 host 中 **0**。

## 状態

⚠️ 部分（sorry 0、rc=0）。公開定理はすべて無条件または `VE2`/`VE3`/`VE4` 仮定付き。
原文の主張そのもの（`VE` 三つ組込み）は `vg7x_condIIIV_of_DT` の移植待ち。
-/

namespace PSS

/-! ## 私的補助（suffix `_c24`） -/

/-- `Dprin` は第 2 引数について単射（第 1 引数固定）。
Isabelle `cdx_Dpt_inj` (layerB 90136)。 -/
private theorem Dprin_inj_c24 {v : ℕ∞} {a b : BT}
    (h : Dprin v a = Dprin v b) : a = b := by
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true] at h
  exact h.2

/-- `+_B` の左簡約律。Isabelle `cdx_addBT_left_cancel` (layerB 90127)。 -/
private theorem addBT_left_cancel_c24 {a b c : BT}
    (h : addBT a b = addBT a c) : b = c := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  rcases c with ⟨cs⟩
  simp only [addBT, BT.trm.injEq] at h
  simp only [BT.trm.injEq]
  exact List.append_cancel_left h

/-! ## 純 BT の一意存在足場（無条件）

Isabelle `cdx_condIIIV_scaffold` (layerB 90145)。条件(V) 双子の
`terminal_slice_Trans_scaffold` の 4 切片版。 -/

/-- **Isabelle `cdx_condIIIV_scaffold` (layerB 90145)** の逐語移植。

四つの `Trans` 値がそれぞれ所定の頭指標を持つ principal 項であり
（`princN`/`princN'`/`princM'`/`princM`）、残差の三つ組 `VE2`/`VE3`/`VE4` と
`t₂ ≠ 0_B` が成り立つなら、一意の `(t₁,t₂)` が存在し、それは
`(bpHeadT TN, t₂)` である。純 BT の代数のみを使う（ペア数列に触れない）。 -/
theorem condIIIV_Trans_scaffold (TN TN' TM' TM t₂ : BT) (u₀ u₁ : ℕ∞)
    (princN : TN = Dprin u₀ (bpHeadT TN))
    (princN' : TN' = Dprin u₁ (bpHeadT TN'))
    (princM' : TM' = Dprin u₁ (bpHeadT TM'))
    (princM : TM = Dprin u₀ (bpHeadT TM))
    (VE2 : bpHeadT TN' = bpHeadT TN)
    (VE3 : bpHeadT TM' = addBT (bpHeadT TN) t₂)
    (t2ne : t₂ ≠ BZero)
    (VE4 : bpHeadT TM = addBT (bpHeadT TN) (Dprin u₁ (bpHeadT TM'))) :
    ∃! t12 : BT × BT,
      TN = Dprin u₀ t12.1 ∧
      TN' = Dprin u₁ t12.1 ∧
      TM' = Dprin u₁ (addBT t12.1 t12.2) ∧ t12.2 ≠ BZero ∧
      TM = Dprin u₀ (addBT t12.1 (Dprin u₁ (addBT t12.1 t12.2))) := by
  -- Isabelle の `g2`/`g3`/`g4`
  have g2 : TN' = Dprin u₁ (bpHeadT TN) := by rw [princN', VE2]
  have g3 : TM' = Dprin u₁ (addBT (bpHeadT TN) t₂) := by rw [princM', VE3]
  have g4 : TM = Dprin u₀ (addBT (bpHeadT TN)
      (Dprin u₁ (addBT (bpHeadT TN) t₂))) := by
    conv_lhs => rw [princM]
    rw [VE4, VE3]
  refine ⟨(bpHeadT TN, t₂), ⟨princN, g2, g3, t2ne, g4⟩, ?_⟩
  rintro ⟨t₁, t₂'⟩ ⟨c1, -, c3, -, -⟩
  -- `fst t12 = bpHeadT TN`
  have fst12 : t₁ = bpHeadT TN := Dprin_inj_c24 (c1.symm.trans princN)
  -- `snd t12 = t₂`
  have e3 : addBT t₁ t₂' = addBT (bpHeadT TN) t₂ := Dprin_inj_c24 (c3.symm.trans g3)
  rw [fst12] at e3
  have snd12 : t₂' = t₂ := addBT_left_cancel_c24 e3
  simp [fst12, snd12]

/-! ## `LastStep`（訂正 A9 後の形）

Isabelle `LastStep` (pss_defs.thy:533)。原文 L3304。 -/

/-- `LastStep : DT_PS → ℕ`（原文 §8.2, L3304、**訂正 A9 後**の形）。

`Br M = ()` なら `0`；`J₁ := Lng(Br M) - 1` として最終枝の頭が対角
（行 0 ＝行 1）なら `J₁`；さもなくば
`min {J | J < Lng(Br M) ∧ (Br(M)_{J₁})₀,₀ = (Br(M)_J)₀,₀ > (Br(M)_J)₁,₀}`。

Isabelle の `Min`（集合）に対し Lean では `List.find?` で最小元を取る：
`List.range n` は昇順なので `find?` は条件を満たす**最小の** `J` を返す
（＝上界付き内包の `Min`）。集合が空のときの既定値は `J₁`（Isabelle の
`Min {}` は junk。原文脚注[61] は「`J = J₁` が条件を満たすため `min` が存在する」
と述べており、意図された定義域では空にならない。下記
`LastStep_eq_find_of_guard` がその一致を保証する）。

この全域化のおかげで `min` の well-defined 性（Isabelle の `fin` 仮定）が
不要になる。 -/
def LastStep (M : PS) : ℕ :=
  if (Br M).length = 0 then 0
  else
    let J₁ := (Br M).length - 1
    if entry ((Br M).getD J₁ []) 0 0 = entry ((Br M).getD J₁ []) 1 0 then J₁
    else
      ((List.range (Br M).length).find? (fun J =>
        decide (entry ((Br M).getD J₁ []) 0 0 = entry ((Br M).getD J []) 0 0) &&
        decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0))).getD J₁

/-- Isabelle `vgx_LastStep_eqcase` (layerB 90986): 対角分岐。 -/
theorem LastStep_eqcase (M : PS) (hBrne : Br M ≠ [])
    (heq : entry ((Br M).getD ((Br M).length - 1) []) 0 0
         = entry ((Br M).getD ((Br M).length - 1) []) 1 0) :
    LastStep M = (Br M).length - 1 := by
  have hLpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br M).length ≠ 0 := by omega
  unfold LastStep
  simp only [hL, if_false]
  split
  · rfl
  · next hne => exact absurd heq hne

/-- **Isabelle `vgx_LastStep_lt_Lng_Br` (layerB 91009) の無条件版。**

Isabelle 版は最終枝頭の狭義不等式 `gt` と有限性 `fin` を仮定するが、Lean の
全域的な `LastStep`（`find?`＋既定値 `J₁`）では `Br M ≠ []` のみから従う：
対角分岐なら値は `J₁ < Lng(Br M)`、`find?` が `some J` を返せば
`J ∈ List.range (Lng (Br M))` ゆえ `J < Lng(Br M)`、`none` なら既定値
`J₁ < Lng(Br M)`。いずれの枝も範囲内。 -/
theorem LastStep_lt_Lng_Br (M : PS) (hBrne : Br M ≠ []) :
    LastStep M < (Br M).length := by
  have hLpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br M).length ≠ 0 := by omega
  unfold LastStep
  simp only [hL, if_false]
  split
  · omega
  · cases hfind : (List.range (Br M).length).find? (fun J =>
        decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0
              = entry ((Br M).getD J []) 0 0) &&
        decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) with
    | none => simpa using (by omega : (Br M).length - 1 < (Br M).length)
    | some J =>
        have hJmem := List.mem_of_find?_eq_some hfind
        have : J < (Br M).length := by simpa using hJmem
        simpa using this

/-! ## 単項切片の principal 表示（無条件）

Isabelle `vgx_slice_princ` (layerB 91167)。条件(V) 双子の
`condV_terminal_slice_principal` を任意の切片端 `a < b` に一般化したもの。 -/

/-- `IncrFirstN` は行 1 の entry を動かさない（Isabelle `repr_entry1_shift_gen`
の核）。 -/
private theorem entry_IncrFirstN_one_c24 (n : ℕ) (M : PS) (j : ℕ)
    (hj : j < Lng M) : entry (IncrFirstN n M) 1 j = entry M 1 j := by
  rw [IncrFirstN_eq_map]
  simp [entry, List.getElem?_eq_getElem hj]

/-- **Isabelle `vgx_slice_princ` (layerB 91167)** の移植。

`M ∈ RT_PS` の先祖切片 `seg M a b`（`a < b ≤ Lng M - 1`）が単項なら、その
`Trans` は頭指標 `M₁,ₐ` の principal 項である：
`Trans (seg M a b) = D_{M₁,ₐ} (bpHeadT (Trans (seg M a b)))`。

証明は Isabelle と同じ経路：切片の到達性 `leR M 0 a b` を単項性から取り出し
（`le0_monoT_seg_into_list`）、簡約形 `N = Red (seg M a b)` へ落として
（`ancestor_slice_Red_IncrFirst` が `RTPS N`・`monoT N`・`seg = IncrFirstN _ N`
を一括で与える）、`Trans (seg M a b) = Trans N`（`Trans_Red`）の上で
`Trans_principal_head` を適用し、`entry N 1 0 = M₁,ₐ`（`IncrFirstN` は行 1 を
動かさない）で頭指標を読み替える。 -/
theorem slice_Trans_principal_head (M : PS) (a b : ℕ)
    (hR : RTPS M) (hab : a < b) (hbL : b ≤ Lng M - 1)
    (hmonoSeg : monoT (seg M a b) = true) :
    Trans (seg M a b) = Dprin (entry M 1 a : ℕ∞) (bpHeadT (Trans (seg M a b))) := by
  have hM : TPS M := RTPS_TPS M hR
  have hLpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hbLM : b < Lng M := by omega
  -- 到達性を単項性から取り出す
  have hle0 : le0 M a b = true :=
    le0_monoT_seg_into_list M a b b hM hmonoSeg hab.le (le_refl _) hbLM
  have hleM : leR M 0 a b = true := by simpa [leR] using hle0
  -- 簡約形の基本性質
  have hfacts := ancestor_slice_Red_IncrFirst M a b hR hab hbL hleM
  have hRedN : Red (Red (seg M a b)) = Red (seg M a b) := hfacts.1
  have hmonoN : monoT (Red (seg M a b)) = true := hfacts.2.1
  have hIF : seg M a b
      = IncrFirstN (entry M 0 a - entry M 1 a) (Red (seg M a b)) := hfacts.2.2
  -- 長さ
  have hLS : Lng (seg M a b) = b + 1 - a := length_seg M a b
  have hLN : Lng (Red (seg M a b)) = b + 1 - a := by
    have h1 : Lng (IncrFirstN (entry M 0 a - entry M 1 a) (Red (seg M a b)))
        = Lng (Red (seg M a b)) := by simp [IncrFirstN_eq_map]
    have h2 := congrArg Lng hIF
    rw [h1] at h2
    rw [← h2, hLS]
  have hNT : TPS (Red (seg M a b)) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (Red (seg M a b))
    omega
  have hST : TPS (seg M a b) := by
    apply List.ne_nil_of_length_pos
    change 0 < Lng (seg M a b)
    omega
  have hNR : RTPS (Red (seg M a b)) := by
    show reduced (Red (seg M a b)) = true
    have hne : Red (seg M a b) ≠ [] := hNT
    simp [reduced, hne, hRedN]
  -- `Trans` は簡約で不変
  have hTS : Trans (seg M a b) = Trans (Red (seg M a b)) := Trans_Red _ hST
  -- 頭指標の読み替え: `entry N 1 0 = M₁,ₐ`
  have hNpos : (0 : ℕ) < Lng (Red (seg M a b)) := by omega
  have hhead : entry (Red (seg M a b)) 1 0 = entry M 1 a := by
    have h1 : entry (seg M a b) 1 0 = entry (Red (seg M a b)) 1 0 := by
      conv_lhs => rw [hIF]
      exact entry_IncrFirstN_one_c24 _ _ 0 hNpos
    have h2 : entry (seg M a b) 1 0 = entry M 1 a := by
      have hSpos : (0 : ℕ) < Lng (seg M a b) := by omega
      rw [entry_seg M a b 1 0 hSpos, Nat.add_zero]
    rw [← h1, h2]
  have princN := Trans_principal_head _ hNR hmonoN
  rw [hhead] at princN
  rw [hTS]
  exact princN

/-! ## 切片幾何: `0 < j'₀ < TrMax M ≤ m₁ < j₁`

Isabelle `vgx_m1_bounds` (layerB 91077)。 -/

/-- 枝 `J` の左端は範囲内: `FirstNodes(M)_J < Lng M`（Isabelle `a1_FN_lt`）。
`Joints(M)_J <^Next_M FirstNodes(M)_J` の行 0 辺から読み出す。 -/
private theorem FN_lt_Lng_c24 (M : PS) (J : ℕ) (hM : TPS M)
    (hmono : monoT M = true) (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 < Lng M := by
  have hnxJ := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn0 : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using hnxJ
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hn0
  exact hn0.1.1.1.2

/-- `Br M ≠ []` なら幹の右端は右端列より真に左。 -/
private theorem TrMax_lt_last_c24 (M : PS) (hM : TPS M) (hBrne : Br M ≠ []) :
    TrMax M < Lng M - 1 := by
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    exact hBrne (by simp [Br, heq])
  have := TrMax_bound M hM
  omega

/-- **Isabelle `vgx_m1_bounds` (layerB 91077)** の移植：
`m₁ = FirstNodes(M)_{J₀} - 1`（`J₀ = LastStep M`）は幹の右端以降で、かつ
右端列より真に左：`TrMax M ≤ m₁ < Lng M - 1`。

Isabelle 版は `J₀` の範囲性を `fin` 経由で受け取るが、Lean では
`LastStep_lt_Lng_Br` が無条件に与えるので `Br M ≠ []` だけでよい。 -/
theorem m1_bounds (M : PS) (hM : TPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) :
    TrMax M ≤ (FirstNodes M).getD (LastStep M) 0 - 1 ∧
      (FirstNodes M).getD (LastStep M) 0 - 1 < Lng M - 1 := by
  have hJ0 : LastStep M < (Br M).length := LastStep_lt_Lng_Br M hBrne
  have ha := FirstNodes_TrMax_Joints M (LastStep M) hM hmono hJ0
  have hfnlt := FN_lt_Lng_c24 M (LastStep M) hM hmono hJ0
  omega

/-! ## 主張（`VE2`/`VE3`/`VE4` 仮定付き）: Isabelle `vgx_condIIIV_of_VE` -/

/-- **§8.2 命題（条件(II)か(IV)の下での終切片と `Trans` の関係）**（原文 L3314）、
Isabelle `p_8_2_condIIIV_terminal_slice_Trans` (pss_paper.thy:1627) の逐語形。

記号は原文どおり（訂正 A9 後）:
`j₁ = Lng M - 1`, `J₁ = Lng(Br M) - 1`, `j'₀ = Joints(M)_{J₁}`,
`j'₁ = FirstNodes(M)_{J₁}`, `J₀ = LastStep M`, `m₁ = FirstNodes(M)_{J₀} - 1`,
`N = seg M 0 m₁`, `N' = seg M j'₀ m₁`, `M' = seg M j'₀ j₁`。

ただし値方程式の三つ組
- `VE2 : bpHeadT (Trans N') = bpHeadT (Trans N)`
- `VE3 : bpHeadT (Trans M') = bpHeadT (Trans N) +_B t₂`（`t₂ ≠ 0_B`）
- `VE4 : bpHeadT (Trans M) = bpHeadT (Trans N) +_B D_{M₁,ⱼ'₀} (bpHeadT (Trans M'))`

を仮定として持つ（Isabelle `vgx_condIIIV_of_VE`, layerB 91228 に対応）。
`VE2`/`VE3`/`VE4` は Isabelle では `vg7x_condIIIV_of_DT` (layerB 97539) へ続く
back-peel 連鎖が与えるが、約 14000 行あり本ファイルの射程外。条件(V) 双子
（`condV_terminal_slice_Trans_modVE`）が `hVE` を仮定に持つのと同じ扱いである。

**Isabelle からの改善**: Isabelle 版が持つ `fin`（`min` の有限性側条件）は
本移植では不要（ヘッダの「`fin` について」を参照）。また原文の guard
`M₀,ⱼ'₁ > M₁,ⱼ'₁` は逐語性のため仮定に残すが、本証明では使わない
（Isabelle では `LastStep` の範囲性を出すためだけに使われていた）。 -/
theorem condIIIV_terminal_slice_Trans_modVE (M : PS) (t₂ : BT)
    (hMD : DTPS M) (hBrne : Br M ≠ [])
    (hj0pos : 0 < (Joints M).getD ((Br M).length - 1) 0)
    (hj0lt : (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
    (_hguard : entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
             < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0))
    (VE2 : bpHeadT (Trans (seg M ((Joints M).getD ((Br M).length - 1) 0)
                                 ((FirstNodes M).getD (LastStep M) 0 - 1)))
         = bpHeadT (Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))))
    (VE3 : bpHeadT (Trans (seg M ((Joints M).getD ((Br M).length - 1) 0) (Lng M - 1)))
         = addBT (bpHeadT (Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)))) t₂)
    (t2ne : t₂ ≠ BZero)
    (VE4 : bpHeadT (Trans M)
         = addBT (bpHeadT (Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))))
             (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
               (bpHeadT (Trans (seg M ((Joints M).getD ((Br M).length - 1) 0)
                                      (Lng M - 1)))))) :
    ∃! t12 : BT × BT,
      Trans (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1))
        = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
      Trans (seg M ((Joints M).getD ((Br M).length - 1) 0)
                   ((FirstNodes M).getD (LastStep M) 0 - 1))
        = Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞) t12.1 ∧
      Trans (seg M ((Joints M).getD ((Br M).length - 1) 0) (Lng M - 1))
        = Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            (addBT t12.1 t12.2) ∧
      t12.2 ≠ BZero ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t12.1 (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
          (addBT t12.1 t12.2))) := by
  obtain ⟨hR, hmono, -⟩ := (DTPS_iff M).mp hMD
  have hM : TPS M := RTPS_TPS M hR
  -- 幾何
  have hmb := m1_bounds M hM hmono hBrne
  have htrlt := TrMax_lt_last_c24 M hM hBrne
  have hj0m1 : (Joints M).getD ((Br M).length - 1) 0
      < (FirstNodes M).getD (LastStep M) 0 - 1 := by omega
  have hm1L : (FirstNodes M).getD (LastStep M) 0 - 1 ≤ Lng M - 1 := by omega
  have hzm1 : 0 < (FirstNodes M).getD (LastStep M) 0 - 1 := by omega
  have hj0j1 : (Joints M).getD ((Br M).length - 1) 0 < Lng M - 1 := by omega
  -- 三つの切片の単項性（Isabelle `vgx_slice_{N,Np,Mp}_mono`）
  have monoN : monoT (seg M 0 ((FirstNodes M).getD (LastStep M) 0 - 1)) = true :=
    mono_slice M 0 _ hM hmono hzm1 hm1L (Nat.zero_le _)
  have monoN' : monoT (seg M ((Joints M).getD ((Br M).length - 1) 0)
      ((FirstNodes M).getD (LastStep M) 0 - 1)) = true :=
    mono_slice M _ _ hM hmono hj0m1 hm1L (le_refl _)
  have monoM' : monoT (seg M ((Joints M).getD ((Br M).length - 1) 0)
      (Lng M - 1)) = true :=
    mono_slice M _ _ hM hmono hj0j1 (le_refl _) (le_refl _)
  -- 四つの principal 表示
  have princN := slice_Trans_principal_head M 0 _ hR hzm1 hm1L monoN
  have princN' := slice_Trans_principal_head M _ _ hR hj0m1 hm1L monoN'
  have princM' := slice_Trans_principal_head M _ _ hR hj0j1 (le_refl _) monoM'
  have princM := Trans_principal_head M hR hmono
  -- 純 BT の足場へ
  exact condIIIV_Trans_scaffold _ _ _ _ t₂ _ _ princN princN' princM' princM
    VE2 VE3 t2ne VE4

/-! ## 非空虚性の機械的証拠

上の定理は仮定が空虚なら無意味なので、幾何的仮定の束
（`DTPS`・`Br M ≠ []`・`0 < j'₀ < TrMax M`・guard）が**充足可能**であることを
`decide` で機械証明しておく。証人は `M = (0,0)(1,1)(2,2)(2,0)`
（`TrMax M = 2`, `j'₀ = 1`, `j'₁ = 3`, `LastStep M = 0`, `m₁ = 2`）。

残差 `VE2`/`VE3`/`VE4`/`t₂ ≠ 0_B` の充足可能性は数値検証による
（`python/audit_82_condIIIV.py`）。実測値:
- `L ≤ 5`, 成分 `< 3`: 幾何的仮定を満たす host 7 件、**7/7** で `VE` 三つ組・
  `t₂ ≠ 0_B`・結論のすべてが成立、反例 0。
- `L ≤ 6`, 成分 `< 5`（62613 host まで部分走査）: 同じく **2/2**、反例 0。
- 上記は Isabelle 側の r30 検証（`python/_r30_condIIIV.py`, 23/23）と整合。 -/

private def witness_c24 : PS := [(0,0),(1,1),(2,2),(2,0)]

#guard TrMax witness_c24 == 2
#guard (Joints witness_c24).getD ((Br witness_c24).length - 1) 0 == 1
#guard (FirstNodes witness_c24).getD ((Br witness_c24).length - 1) 0 == 3
#guard LastStep witness_c24 == 0

/-- 本ファイルの主定理の幾何的仮定は充足可能（＝主定理は空虚でない）。 -/
private theorem witness_hyps_c24 :
    DTPS witness_c24 ∧ Br witness_c24 ≠ [] ∧
    0 < (Joints witness_c24).getD ((Br witness_c24).length - 1) 0 ∧
    (Joints witness_c24).getD ((Br witness_c24).length - 1) 0 < TrMax witness_c24 ∧
    entry witness_c24 1 ((FirstNodes witness_c24).getD ((Br witness_c24).length - 1) 0)
      < entry witness_c24 0
          ((FirstNodes witness_c24).getD ((Br witness_c24).length - 1) 0) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

#print axioms witness_hyps_c24
#print axioms condIIIV_Trans_scaffold
#print axioms LastStep_eqcase
#print axioms LastStep_lt_Lng_Br
#print axioms slice_Trans_principal_head
#print axioms m1_bounds
#print axioms condIIIV_terminal_slice_Trans_modVE

end PSS
