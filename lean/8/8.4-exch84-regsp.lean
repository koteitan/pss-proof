import «8».«8.4-exch84-props»
import «8».«8.4-exch84-producer»
import «8».«8.4-exch84-regs»

/-!
# §8.4 交換パッケージの `REGSP` / `base0` / `base1'` / `mnform` 脚

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
  逐語形 = `p_8_4_Trans_oper_exchange` (isabelle/pss_paper.thy:1909)。
- 対象: ビルド済みの `Exch84_condIIIIV_pkg`（«8».«8.4-exch84-props»、6 葉残差 bundle
  `TerminationResidual` の 1 つ）を、Isabelle の最終ルート `oi5_IIIIV_pkg`
  (`isabelle/layerC/pss_scratch.thy:1213`) が discharge する 5 束
  `REGS`/`REGSP`/`RUN`/`mnform`/`base0`/`base1'` へ向けて縮約する。
  `REGS` (`mcx_regS`) は Wave-O で «8».«8.4-exch84-regs» が着地済み。本ファイルは
  残りの 3 束（`REGSP`/base 事実/`mnform`）を担当する。

## 本ファイルの分担

1. **`Exch84_condIIIIV_pkg_holds`（house pattern、完全証明）**: ビルド済みの
   `Exch84_condIIIIV_slicepkg`（«8».«8.4-exch84-producer»、`oi5_IIIIV_pkg` の出力を
   1:1 で写した Prop）から `Exch84_condIIIIV_pkg` を出す。両者の差は `operB` 閉形式
   `fO` のみで、`fO` は `slicepkg` の `inner`＋`k1` から `scb_fseq_kind1`
   （«7».«7.2-scb-fseq»、原文 §7.2(2) 一般形）で組む（«8».«8.4-exch84-producer» の
   `Exch84_condIIIIV_producer_of_slicepkg` と同一技法）。**これで `pkg` 葉は
   `slicepkg` 葉へ縮約される。**

2. **`Regsp_slx37_regSP`（REGSP、named Prop 露出）**: Isabelle
   `slx37_regSP_uncond` (layerB/pss_wip.thy:97329) を Lean 語彙で述べたもの
   （`cfbx_reg` = `VEReg`）。`Red (Pred (s84x_N M))` に対する regime membership。
   Isabelle の証明は `lb2x_regSP_of_lt_eqd` (:96435) →
   `mcx_regSP_of_diag` (:94051) ＋ 尖った `slx37_strictlt_eqd` (:97052) で、後者は
   `wid_*_Pred` / `trunk_entries_offset` / `crx_trmax_run` / `TrMax_Pred` /
   `mcx_d_le_last_joint` など未移植機構を多数使うため named 残差として露出する。

3. **`Base0_condIIIIV` / `Base1p_condIIIIV`（base0 / base1'、named Prop 露出）**:
   Isabelle `crx_base0_of_run` (:88555) / `cnv_base0_of_run` (:102029)（base0）と
   `oy1_base1Y_condIII` / `oy1_base1Y_condIV` (layerC:979/1086)（base1'）を Lean
   語彙で述べたもの。base1' は挿入段 `ins` を `d4vx_ins_flat` の結論（`hflat`）で
   抽象化し、oy1 の `inner` scb 分解を仮定に取る形（原型に忠実）。

4. **`Mnform_condIIIIV`（mnform、named Prop 露出）**: Isabelle
   `cpx_condIII_mnform` (layerB/pss_wip.thy:98605) を Lean 語彙で述べたもの。
   `oi5_IIIIV_pkg` の `obtain`（`inner`/`k1`/`MNall`）に 1:1 対応する構造束。
   `M[m]` 閉形式は `d4vx_core … A₀` = `coreTower_e34 ins A₀`（A₀ 種の塔）。

これら 4 本の named Prop（＋ 既出 `Regs_*` ＋ RUN ＋ condIV-admeq 角）から
`slicepkg` を組むのが Isabelle の `oi5_IIIIV_pkg` ＋ ltJ 二分岐であり、それは
1000 補題規模の corpus なので本ファイルでは触れない（次 wave の担当）。

- 依存（すべてビルド済み・committed）:
  «8».«8.4-exch84-props»（`Exch84_condIIIIV_pkg`・`coreTower_e34`）、
  «8».«8.4-exch84-producer»（`Exch84_condIIIIV_slicepkg`）、
  «8».«8.4-exch84-regs»（`VEReg`・`s84x_*` 語彙・`Regs_*`・推移的に
  `scb_fseq_kind1`/`Trans_mem_T_B`/`STPS_RTPS`/`scb_decomp`/`scb_kind1`/`Dprin`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `Exch84_condIIIIV_pkg_holds` は完全証明（`slicepkg` 上）。残差 = 上記 4 named Prop。
- 訂正: なし。A32 は取り下げ済（`corrections-old.md`:101）。
- Private helper suffix: `_rp`。
-/

namespace PSS

/-! ## 1. `operB` 閉形式 `fO` を組むための private 補助（suffix `_rp`）

«8».«8.4-exch84-producer» の private 版（suffix `_ep`）の再掲。 -/

/-- «7».«7.2-scb-fseq» の private `flatten_replicate_snoc` の再掲。 -/
private theorem flatten_replicate_snoc_rp {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate (n + 1) xs) =
      List.flatten (List.replicate n xs) ++ xs := by
  rw [List.replicate_add, List.flatten_append]
  simp

/-- `coreTower_e34 ins 0_B j` の flat 形。`hflat`（＝`d4vx_ins_flat`）だけから帰納で出る。
Isabelle `d4vx_core_flat` の `0_B` 底の場合。 -/
private theorem coreTower_zero_flat_rp {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) :
    ∀ j, flatBT (coreTower_e34 ins BZero j)
      = List.flatten (List.replicate j (s0 ++ [Sym.dsym ub]))
        ++ [Sym.zero] ++ List.flatten (List.replicate j b0)
  | 0 => by simp [coreTower_e34, BZero, flatBT]
  | j + 1 => by
      show flatBT (ins (coreTower_e34 ins BZero j)) = _
      rw [hflat (coreTower_e34 ins BZero j), coreTower_zero_flat_rp hflat j,
        flatten_replicate_snoc_rp b0 j, List.replicate_succ, List.flatten_cons]
      simp [List.append_assoc]

/-! ## 2. `Exch84_condIIIIV_pkg` を `Exch84_condIIIIV_slicepkg` へ縮約（house pattern） -/

/-- `Exch84_condIIIIV_pkg`（«8».«8.4-exch84-props»）の drop-in。

`Exch84_condIIIIV_slicepkg`（«8».«8.4-exch84-producer»、`oi5_IIIIV_pkg` の出力）の
`inner`＋`k1` から `operB` 閉形式 `fO` を組む。それ以外の項
（`hflat`/`hb0`/`hb1`/`mnform`/`base0`/`base1'`）は両 Prop で同形なのでそのまま渡す
（`ub = ((v₁-1 : ℕ) : ℕ∞)`、`e₃ = ((e₃ : ℕ) : ℕ∞)`）。

`fO` = `scb_fseq_kind1`（原文 §7.2(2) 一般形）を `c₂ = D_{e₃} body` に適用し、
`coreTower_zero_flat_rp` で `d4vx_core` の flat 形へ書き換える。Isabelle 側で
`d13x_fseq_condIII` ＋ `d4vx_core_flat` が担う段。 -/
theorem Exch84_condIIIIV_pkg_holds (h : Exch84_condIIIIV_slicepkg) :
    Exch84_condIIIIV_pkg := by
  intro M hST hmono hj1 hcond hp
  obtain ⟨ins, A0, body, e3, v1, s0, b0, s1, b1,
    hflat, hb0, hb1, hinner, hk1, hmn, base0, base1'⟩ := h M hST hmono hj1 hcond hp
  refine ⟨ins, A0, (e3 : ℕ∞), ((v1 - 1 : ℕ) : ℕ∞), s0, b0, s1, b1,
    hflat, hb0, hb1, ?_, hmn, base0, base1'⟩
  -- `fO`: `scb_fseq_kind1` を `c₂ = D_{e₃} body` に適用する
  intro k
  have hTB : Trans M ∈ T_B := Trans_mem_T_B M (STPS_RTPS M hST)
  have hinner' : scb_decomp (Dprin (e3 : ℕ∞) body) (Sym.dsym (e3 : ℕ∞) :: s0)
      (flatBT (Dprin (v1 : ℕ∞) BZero)) b0 := by
    refine ⟨?_, ?_, hinner.2.2⟩
    · have hd : flatBT (Dprin (e3 : ℕ∞) body) = Sym.dsym (e3 : ℕ∞) :: flatBT body := by
        simp [Dprin, flatBT, flatBP]
      rw [hd, hinner.1]
      simp
    · intro _
      exact ⟨.db (v1 : ℕ∞) BZero, by
        simp [dfree_BP, BZero, dfree_BT, dfree_BPList], rfl⟩
  have hfseq := (scb_fseq_kind1 (n := k) hTB hk1 hinner').2
  rw [hfseq]
  simp only [flatBP]
  rw [coreTower_zero_flat_rp hflat (k + 1)]
  simp [List.append_assoc]

#print axioms Exch84_condIIIIV_pkg_holds

/-! ## 3. `REGSP` 脚（named Prop、Isabelle `slx37_regSP_uncond`） -/

/-- Isabelle `slx37_regSP_uncond` (layerB/pss_wip.thy:97329) を Lean 語彙で述べたもの
（`cfbx_reg` = `VEReg`、«8».«8.2-condV-VE-base»）。

`s84x_jm3 M < s84x_jm2 M`（guard）と `Br (Red (Pred (s84x_N M))) ≠ []`（Brne'）の下で、
簡約された前スライス `Red (Pred (s84x_N M))` は `VEReg (s84x_jm2 M - s84x_jm3 M)`
の regime に属する。`Regs_mcx_regS`（«8».«8.4-exch84-regs»）の「前スライス版」。

Isabelle の証明: `lb2x_regSP_of_lt_eqd` (:96435) が `mcx_regSP_of_diag` (:94051) と
尖った `slx37_strictlt_eqd` (:97052) から組む。membership 部（`RTPS`/`monoT`/
`descendingB`）は `Red (Pred (s84x_N M)) = Red (seg M jm3 (Lng M - 2))`
（`Red_Pred` ＋ `Pred_Red_slice`）＋ `standard_slice_Red_strongmono` で従うが、
regime 選言の尖った枝（`d = jlp → diag`）は `mcx_MCOND_RN`（= `Regs_MCOND`）と
`wid_*_Pred` / `trunk_entries_offset` / `crx_trmax_run` / `TrMax_Pred` /
`mcx_d_le_last_joint` を要するため named 残差として露出する。 -/
def Regsp_slx37_regSP : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm3 M < s84x_jm2 M →
    Br (Red (Pred (s84x_N M))) ≠ [] →
    VEReg (s84x_jm2 M - s84x_jm3 M) (Red (Pred (s84x_N M)))

/-- Isabelle `mcx_regSP_of_diag` (layerB/pss_wip.thy:94051) の regime 選言のうち、
`slx37_strictlt_eqd` (:97052) が実際に供給する尖った部分だけを抜き出した残差:
`d < jlp`、または（`d = jlp` の角で）最終枝先頭が対角。ここで
`d = s84x_jm2 M - s84x_jm3 M`、`jlp = Joints (Red (Pred (s84x_N M))) ! last`。
`Regs_MCOND`（«8».«8.4-exch84-regs»）の前スライス版。 -/
def Regsp_disj_sharp : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm3 M < s84x_jm2 M →
    Br (Red (Pred (s84x_N M))) ≠ [] →
    (s84x_jm2 M - s84x_jm3 M
        < (Joints (Red (Pred (s84x_N M)))).getD
            ((Br (Red (Pred (s84x_N M)))).length - 1) 0
      ∨ (s84x_jm2 M - s84x_jm3 M
           = (Joints (Red (Pred (s84x_N M)))).getD
               ((Br (Red (Pred (s84x_N M)))).length - 1) 0
         ∧ entry (Red (Pred (s84x_N M))) 0 (VEj1p (Red (Pred (s84x_N M))))
           = entry (Red (Pred (s84x_N M))) 1 (VEj1p (Red (Pred (s84x_N M))))))

/-- `REGSP` の membership 骨格を無条件に証明し、`Regsp_slx37_regSP` を
`Regs_jm3Marked`（既出の脚、«8».«8.4-exch84-regs»）と尖った `Regsp_disj_sharp` に
縮約する（house pattern）。

Isabelle `mcx_regSP_of_diag` の membership 段の移植:
`Red (Pred (s84x_N M)) = Red (seg M j₋₃ (Lng M - 2))`（`Red_Pred`＋
`Pred_Red_terminal_slice`）に書き換え、前スライスの `DTPS`
（`standard_slice_Red_strongmono`）から `RTPS`/`monoT`/`descendingB` を得る。
`Lng M - 2` 域は `guard`（`j₋₃ < j₋₂`）と `j₋₂ < Lng M - 1` だけで足り、
`transJ0` を経由しない（`jm2 ≤ Lng M - 2` から `jm3 < Lng M - 2`）。 -/
theorem Regsp_of_disj_sharp (hMarked : Regs_jm3Marked) (hsharp : Regsp_disj_sharp) :
    Regsp_slx37_regSP := by
  intro M hST hmono hp hj1 hcond guard Brne'
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  obtain ⟨mMarked, jm3le, jm2lt⟩ := hMarked M hMR hMT hp
  have leR3 : leR M 0 (s84x_jm3 M) (Lng M - 1) = true := mMarked.2.2
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have jm3ltLm2 : s84x_jm3 M < Lng M - 2 := by omega
  have jm3leLm2 : s84x_jm3 M ≤ Lng M - 2 := le_of_lt jm3ltLm2
  -- 前スライス `Red (Pred (s84x_N M))` = `Red (seg M j₋₃ (Lng M - 2))`
  have hlenN : Lng (s84x_N M) = Lng M - s84x_jm3 M := by
    show Lng (seg M (s84x_jm3 M) (Lng M - 1)) = Lng M - s84x_jm3 M
    rw [length_seg]; omega
  have NT : TPS (s84x_N M) := by
    have hpos : 0 < Lng (s84x_N M) := by rw [hlenN]; omega
    intro hnil; rw [hnil] at hpos; simp [Lng] at hpos
  have hNeq : Red (Pred (s84x_N M)) = Red (seg M (s84x_jm3 M) (Lng M - 2)) := by
    have h1 : Red (Pred (s84x_N M)) = Pred (Red (s84x_N M)) := Red_Pred (s84x_N M) NT
    have h2 : Pred (Red (s84x_N M)) = Red (seg M (s84x_jm3 M) (Lng M - 1 - 1)) :=
      Pred_Red_terminal_slice M (s84x_jm3 M) (Lng M - 1) jm3lt
    have he : Lng M - 1 - 1 = Lng M - 2 := by omega
    rw [h1, h2, he]
  -- 前スライスの `DTPS`
  have leR3Lm2 : leR M 0 (s84x_jm3 M) (Lng M - 2) = true :=
    ancestor_tree_1 M (s84x_jm3 M) (Lng M - 2) (Lng M - 1) hMT leR3 jm3leLm2 (by omega)
  have hDT : DTPS (Red (seg M (s84x_jm3 M) (Lng M - 2))) :=
    standard_slice_Red_strongmono M (s84x_jm3 M) (Lng M - 2) hST jm3ltLm2 (by omega) leR3Lm2
  have hDT' : DTPS (Red (Pred (s84x_N M))) := by rw [hNeq]; exact hDT
  obtain ⟨RNRT, monoRN, descRN⟩ := (DTPS_iff _).mp hDT'
  -- membership ＋ 尖った選言
  refine ⟨RNRT, monoRN, Brne', ?_⟩
  rcases hsharp M hST hmono hp hj1 hcond guard Brne' with hlt' | ⟨heq, hdiag⟩
  · exact Or.inl hlt'
  · exact Or.inr ⟨heq, hdiag, descRN⟩

#print axioms Regsp_of_disj_sharp

/-! ## 4. `base0` / `base1'` 脚（named Prop） -/

/-- Isabelle の `base0`: `oi5_IIIIV_pkg` (layerC:1213) が `crx_base0_of_run`
(layerB/pss_wip.thy:88555, condIII) / `cnv_base0_of_run` (:102029, condIV) で出す
底事実 `D_{ub} 0_B <_B A₀`。`ub = M_{1,Lng M-1} - 1`、`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`。

`RUN`（`nextR M 1 j₋₂ (j₋₂+1)`、`wgx37_m0run_of_e1ge` ＋ `e1x_e1ge_uncond`）を
消費するため named 残差。 -/
def Base0_condIIIIV : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    lessBT (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero)
           (bpHeadT (Trans (Pred (s84x_N M)))) = true

/-- Isabelle の `base1'`: `oy1_base1Y_condIII` (layerC:979) / `oy1_base1Y_condIV`
(:1086) が出す `A₀ <_B ins 0_B`。挿入段 `ins` を `d4vx_ins_flat` の結論（`hflat`）で
抽象化し、oy1 の `inner` scb 分解（穴 = `D_{v₁} 0_B`）を仮定に取る。
`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`、`body = bpHeadT (Trans (s84x_N M))`、
`v₁ = M_{1,Lng M-1}`、`ub = v₁ - 1`。

Isabelle の証明は純 `T_B`/`scb` 代数（`c1_shape`/`c2_shape`/`m_7_2_add_scb`/
`scb_Dpt_lift`/`m_7_2_scb_unique_sb`/`scbext_lessBT`/`lessBT_addBT_self`）だが、
未移植の補助（`crx_c2_shape_condIII`/`cnv_c2_shape_condIV`/`vf2x_flat_head_bpHeadT`）が
あるため named 残差として露出する。 -/
def Base1p_condIIIIV : Prop :=
  ∀ (M : PS) (ins : BT → BT) (s0 b0 : List Sym),
    STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    (∀ X, flatBT (ins X)
        = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) →
    scb_decomp (bpHeadT (Trans (s84x_N M))) s0
      (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 →
    lessBT (bpHeadT (Trans (Pred (s84x_N M)))) (ins BZero) = true

/-! ## 5. `mnform` 脚（named Prop、Isabelle `cpx_condIII_mnform`） -/

/-- Isabelle `cpx_condIII_mnform` (layerB/pss_wip.thy:98605) を Lean 語彙で述べたもの。

`oi5_IIIIV_pkg` (layerC:1213) の `obtain … using cpx_condIII_mnform` に 1:1 対応する
構造束: 挿入段 `ins`（`hflat`）、`inner` scb 分解（穴 = `D_{v₁} 0_B`）、`Trans M` の
第 1 種 scb 分解 `k1`（穴 = `D_{e₃} body`）、および `M[m]` の閉形式 `mnform`
（`A₀` 種の塔 `coreTower_e34 ins A₀`）。`REGS`/`REGSP` を消費する（`ltJ` 分岐下で）ため
named 残差。`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`、`body = bpHeadT (Trans (s84x_N M))`、
`e₃ = M_{1,j₋₃}`、`v₁ = M_{1,Lng M-1}`、`ub = v₁ - 1`。 -/
def Mnform_condIIIIV : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm3 M < transJm1 M →
    ∃ (ins : BT → BT) (s0 b0 s1 b1 : List Sym),
      (∀ X, flatBT (ins X)
          = s0 ++ Sym.dsym ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) ∧
      (∀ x ∈ b0, x = Sym.rp) ∧
      (∀ x ∈ b1, x = Sym.rp) ∧
      scb_decomp (bpHeadT (Trans (s84x_N M))) s0
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) b0 ∧
      scb_kind1 (Trans M) s1
        (flatBT (Dprin ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
                       (bpHeadT (Trans (s84x_N M))))) b1 ∧
      (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
        = s1 ++ flatBP (.db ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞)
            (coreTower_e34 ins (bpHeadT (Trans (Pred (s84x_N M)))) (m - 1))) ++ b1)

end PSS
