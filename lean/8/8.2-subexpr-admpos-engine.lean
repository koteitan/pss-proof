import «6».«6.5-Red-Pred-commute»
import «6».«6.6-reduced-slice»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.4-RightAnces-zeroT»
import «7».«7.3-c1-c2-order»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.4-RightNodes-Mark»
import «7».«7.4-Trans-Mark-Pred»
import «7».«7.4-RightAnces-RightNodes»
import «8».«8.2-condV-terminal-slice-Trans»
import «8».«8.2-subexpr-wid»

/-!
# §8.2 部分表現の単項成分と `Pred` — `Admpos` body-split 機構と `wid` 連鎖

`Adm0` regime（`transJm1 M = 0`）を扱う既存の §8.2 群に対し、本ファイルはその補
regime である **`Admpos`**（`transJm1 M > 0`）の機構を担う。wave-C-2 の `wid`
エージェントが「`wid` 連鎖全体の唯一のブロッカー」と報告した engine
`trans_admpos_body_split` と、その上に載る `wid` 三本を収録する。

- 原文: `tmp/content.md` 3432–3435 付近（§8.2 補題の `j₁ - TrMax(M)` に関する
  帰納法が使う「`RightNodes (Trans M)` の第 2 成分の同定」）。
- Isabelle (`isabelle/layerB/pss_wip.thy`) との対応:
  - `trans_admpos_body_split` ← 同名 (26573)  ※STEP 1、engine
  - `wid_step`               ← `m_8_2_wid_step` (28837)
  - `wid_of_predRN`          ← `m_8_2_wid_of_predRN` (28893)
  - `wid_of_predwid`         ← `m_8_2_wid_of_predwid` (29038)
  - private (いずれも Isabelle からの完全移植、sorry 0):
    - `trans_admpos_outer_principal_ape` ← `trans_admpos_outer_principal` (25320)
    - `trans_surgery_localized_ape`      ← `trans_surgery_localized` (23635)
    - `Trans_mono_RN_ge2_ape`            ← `Trans_mono_RN_ge2` (9011)
    - `Mark0_ne_Mark_ape`                ← `Mark0_ne_Mark` (9636)
  - Isabelle の `defines`（`J1`/`j0'`/`j1'`/`JN`）は文に展開した。
    `M ∈ RT_PS ∩ PT_PS` は `(hR : RTPS M) (hmono : monoT M = true)` に展開。

## 状態: 本ファイル単独で green（sorry 0、axioms 3 種のみ）。ただし **green-modulo 1 本**

未移植の外科機構を名前付き仮定 1 本（`def ... : Prop`）として切り出し、組み立ては
それを引数に取る条件付き定理として証明した。親エージェントが後段で discharge する。

- `ScbOuterSurgerySplit` ← Isabelle `scb_outer_surgery_split` (26412, 161 行)。
  純粋な `BT`/`Sym` 組合せ論（`PS` を含まない）。未移植の下位依存:
  `scb_to_last_component` / `scbimg_image_BT` (913) / `flatBT_multi_last` (22796) /
  `flatinj_flatBP_cancel`。これが `Admpos` 系に残る唯一の穴。

**wave-C-2 報告の訂正（重要）**: 同エージェントは `trans_surgery_localized` /
`scb_outer_surgery_split` / `trans_admpos_outer_principal` の 3 本すべてを
「Lean 未移植の外科機構」と報告したが、実際に未移植なのは
`scb_outer_surgery_split` のみである。
- `trans_surgery_localized` は既存の `Trans_Mark_Pred`（§7.4, A46 形）＋
  `Mark_transJm1_eq_transC2`（§7.4）から直接得られる（`c₁ = Mark (Pred M) j₋₁`
  は定義そのもの、`c₂ = Mark M j₋₁` は後者）。
- `trans_admpos_outer_principal` は `Trans_principal_head`
  （8.2-condV-terminal-slice）から無条件に出る（`t1ne` すら不要）。
- `Mark0_ne_Mark` の唯一の壁だった `Trans_mono_RN_ge2` は、Isabelle では
  `Trans.psimps` 手展開を使うが、Lean では `RightAncesAux_RTPS_equation` ＋
  `RightAncesAux_eq_RightNodes_Trans` で再帰式を一段ほどくだけで済む
  （＝ mission の「TransAux 手展開を避けよ」の指針どおり）。

## 依存（主要）
- `Trans_principal_head`（8.2-condV-terminal-slice-Trans）
- `Trans_Mark_Pred`（7.4-Trans-Mark-Pred）, `Mark_transJm1_eq_transC2`（7.4-Mark-Trans-repr）
- `RightNodes_Dprin` / `RightNodes_addBT_Dprin`（7.4-RightAnces-RightNodes）
- `wid` / `wid_iff`（8.2-subexpr-wid — 再定義せず import）
- `transC1_single_principal` / `principal_reconstruct`（7.3-c1-c2-order）
- `Mark_mem_T_B` / `Marked_Pred` / `Marked_Pred_Adm`（7.3-Trans-welldefined）
- `RTPS_Pred` / `monoT_Pred_long` / `entry_Pred_zero`（6.5-Red-Pred-commute）
- `Adm_adm` / `Adm_le` / `Adm_max`（6.3-admof-slice）, `row0_transitive`（5.1-ancestor-tree）
- `flatBT_injective`（PSS/Flat）

private 補助は接尾辞 `_ape`。`le1Aux_chain_ape` / `adm_row1_ancestry_ape` /
`row1_row0_ape` 等は `8.1-part4-setup.lean` の private `_ps` 群と同内容の再掲
（import 不可のため）。共有層 `PSS/Adm.lean` への昇格候補（needs 参照）。
-/

namespace PSS

/-- Isabelle `trans_admpos_outer_principal` (layerB 25320). -/
private theorem trans_admpos_outer_principal_ape (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hj1gt : 1 < Lng M - 1)
    (ht1ne : Trans (Pred M) ≠ BZero) :
    Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) (bpHeadT (Trans (Pred M))) ∧
      Trans M = Dprin (entry M 1 0 : ℕ∞) (bpHeadT (Trans M)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredMono : monoT (Pred M) = true := monoT_Pred_long M hM hmono (by omega)
  have hP := Trans_principal_head (Pred M) hpredR hpredMono
  have he10 : entry (Pred M) 1 0 = entry M 1 0 := entry_Pred_zero M 1 hlen
  rw [he10] at hP
  exact ⟨hP, Trans_principal_head M hR hmono⟩

/-! ## 行 1 許容化祖先関係（Isabelle `adm_row1_ancestry` の私的再証明）

`8.1-part4-setup.lean` に同内容の private 補題 (`_ps`) があるが import できない
ため、ここに `_ape` 接尾辞で再掲する。共有層への昇格候補（needs 参照）。 -/

private theorem le1Aux_chain_ape (M : PS) (a : ℕ) (b fuel : ℕ)
    (hab : a ≤ b)
    (hstep : ∀ j, a < j → j ≤ b → nextrel1 M (j - 1) j = true)
    (hfuel : b - a ≤ fuel) : le1Aux M fuel a b = true := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by omega
      subst b
      simp [le1Aux]
  | succ fuel ih =>
      by_cases heq : a = b
      · subst b
        simp [le1Aux]
      · have hablt : a < b := lt_of_le_of_ne hab heq
        rw [le1Aux]
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
          Bool.and_eq_true, List.mem_range]
        right
        refine ⟨b - 1, by omega, hstep b hablt (le_refl _), ?_⟩
        apply ih (b := b - 1)
        · omega
        · intro j haj hjb
          exact hstep j haj (by omega)
        · omega

private theorem adm_row1_ancestry_ape (M : PS) (j : ℕ)
    (hM : TPS M) (hj : j ≤ Lng M - 1) :
    leR M 1 (Adm M j) j = true := by
  have hL : 0 < Lng M := List.length_pos_of_ne_nil hM
  have hjL : j < Lng M := by omega
  have haLe : Adm M j ≤ j := Adm_le M j
  have haL : Adm M j < Lng M := haLe.trans_lt hjL
  have hstep : ∀ k, Adm M j < k → k ≤ j →
      nextrel1 M (k - 1) k = true := by
    intro k hak hkj
    have hkadm : adm M k = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hk
      have hmax := Adm_max M k j hk hkj
      omega
    have hnadm : nadm M k = true := by
      simpa [adm] using hkadm
    have hpair : nextR M 1 (k - 1) k = true ∧
        nextR M 1 k (k + 1) = true := by
      have hn := hnadm
      simp only [nadm, Bool.or_eq_true, decide_eq_true_eq,
        Bool.and_eq_true] at hn
      rcases hn with hn | hn
      · omega
      · exact hn
    simpa [nextR] using hpair.1
  have haux : le1Aux M (Lng M) (Adm M j) j = true :=
    le1Aux_chain_ape M (Adm M j) j (Lng M) haLe hstep (by omega)
  simp [leR, le1, haL, hjL, haux]

private theorem le0Aux_refl_ape (M : PS) (fuel a : ℕ) :
    le0Aux M fuel a a = true := by
  cases fuel <;> simp [le0Aux]

private theorem le1Aux_row0_ape (M : PS) (fuel : ℕ) (a b : ℕ)
    (hM : TPS M) (hb : b < Lng M)
    (h : le1Aux M fuel a b = true) : leR M 0 a b = true := by
  induction fuel generalizing b with
  | zero =>
      have hab : a = b := by simpa [le1Aux] using h
      subst b
      simp [leR, le0, hb, le0Aux_refl_ape]
  | succ fuel ih =>
      simp only [le1Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, hpnext, hap⟩
      · subst b
        simp [leR, le0, hb, le0Aux_refl_ape]
      · have hpL : p < Lng M := hpb.trans hb
        have hap₀ := ih p hpL hap
        have hpb₀ : leR M 0 p b = true := by
          have hn := hpnext
          simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn
          simpa [leR] using hn.1.2
        exact row0_transitive M a p b hM hap₀ hpb₀

private theorem row1_row0_ape (M : PS) (a b : ℕ)
    (hM : TPS M) (h : leR M 1 a b = true) :
    leR M 0 a b = true := by
  have h₁ : le1 M a b = true := by simpa [leR] using h
  have hh := h₁
  simp only [le1, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact le1Aux_row0_ape M (Lng M) a b hM hh.1.2 hh.2

/-! ## `Admpos` 文脈: 第 2 基点 `j₋₁ = transJm1 M` は `M` 側でも marked -/

/-- Isabelle `trans_admpos_body_split` 内の `mkd'`/`hmLt` 相当（ただし `M` 側）:
`j₋₁ = transJm1 M` は `M` の marked 列であり、最終列より真に左にある。 -/
private theorem marked_transJm1_ape (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hj1gt : 1 < Lng M - 1) :
    Marked M (transJm1 M) ∧ transJm1 M < Lng M - 1 := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hj0lt : transJ0 M < Lng M - 1 := by
    simpa [transJ0, lastParent, lastIdx] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hnpar : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    simpa [transJ0, lastParent, lastIdx] using
      hasParent_next_fseq M 0 (Lng M - 1) hp
  have hleJ0 : leR M 0 (transJ0 M) (Lng M - 1) = true := nextR0_leR M _ _ hnpar
  have haAdm : adm M (Adm M (transJ0 M)) = true := Adm_adm M (transJ0 M)
  have hle1a : leR M 1 (Adm M (transJ0 M)) (transJ0 M) = true :=
    adm_row1_ancestry_ape M (transJ0 M) hM (by omega)
  have hle0a : leR M 0 (Adm M (transJ0 M)) (transJ0 M) = true :=
    row1_row0_ape M _ _ hM hle1a
  have hchain : leR M 0 (Adm M (transJ0 M)) (Lng M - 1) = true :=
    row0_transitive M _ _ _ hM hle0a hleJ0
  have haLe : Adm M (transJ0 M) ≤ transJ0 M := Adm_le M (transJ0 M)
  exact ⟨⟨hM, haAdm, hchain⟩, by simp only [transJm1]; omega⟩

/-! ## 外科機構の局所化（Isabelle `trans_surgery_localized`, layerB 23635）

Isabelle は `trans_surgery_value` ＋ `transC2_single_principal_head` 経由だが、
Lean には既に `Trans_Mark_Pred`（§7.4, A46 形）と `Mark_transJm1_eq_transC2`
（§7.4）があるので、`c₁ = Mark (Pred M) j₋₁`（定義）・`c₂ = Mark M j₋₁`
（`Mark_transJm1_eq_transC2`）を代入するだけで共有 scb 文脈が得られる。 -/

private theorem trans_surgery_localized_ape (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hj1gt : 1 < Lng M - 1)
    (ht1ne : Trans (Pred M) ≠ BZero) :
    ∃ s1 b1, scb_decomp (Trans (Pred M)) s1 (flatBT (transC1 M)) b1 ∧
      (∀ x ∈ b1, x = .rp) ∧
      scb_decomp (Trans M) s1 (flatBT (transC2 M)) b1 := by
  have hlen : 1 < Lng M := by omega
  obtain ⟨hmk, hmlt⟩ := marked_transJm1_ape M hR hmono hj1gt
  obtain ⟨sb, hsb, _⟩ := Trans_Mark_Pred M (transJm1 M) hmk hR hmlt
  refine ⟨sb.1, sb.2, hsb.1, hsb.1.2.2, ?_⟩
  rw [← Mark_transJm1_eq_transC2 M hR hmono hlen ht1ne]
  exact hsb.2

/-! ## 未移植ブリック（green-modulo）— 残り 1 本

下記 1 本のみ Isabelle 側に完全証明があるが Lean へ未移植。名前付き仮定
（`def ... : Prop`）として切り出し、本ファイルの組み立てはそれを引数に取る
条件付き定理として証明する。親エージェントが後段で discharge する。 -/

/-- 未移植ブリック ← Isabelle `scb_outer_surgery_split`
(layerB/pss_wip.thy:26412, 161 行、純粋な `BT`/`Sym` 組合せ論)。
外側 principal `D_e10 BP` の scb 分解を `D_v t2 → D_v body2` に置換すると、
`BP` と像 `Y` の本体は共通接頭辞 `pre` と共通の末尾 principal 頭 `w` を持つ。
依存（いずれも Lean 未移植）: `scb_to_last_component` / `scbimg_image_BT` /
`flatBT_multi_last` / `flatinj_flatBP_cancel`。 -/
def ScbOuterSurgerySplit : Prop :=
  ∀ (e10 v : ℕ∞) (BP body2 t2 Y : BT) (s1 b1 : List Sym),
    BP ≠ BZero →
    scb_decomp (Dprin e10 BP) s1 (flatBT (Dprin v t2)) b1 →
    dfree_BP (.db v body2) = true →
    Dprin e10 BP ≠ Dprin v t2 →
    flatBT Y = s1 ++ flatBT (Dprin v body2) ++ b1 →
    ∃ pre w u2 u3,
      BP = addBT pre (Dprin w u2) ∧ Y = Dprin e10 (addBT pre (Dprin w u3))

/-! ## 組み立てに要る小補題 -/

private theorem flatBT_length_pos_ape (t : BT) : 0 < (flatBT t).length := by
  rcases t with ⟨ps⟩
  match ps with
  | [] => simp [flatBT]
  | [p] => rcases p with ⟨u, a⟩; simp [flatBT, flatBP]
  | p :: q :: ps => simp [flatBT]

private theorem transC2_outer_ape (M : PS) :
    transC2 M = Dprin (transV M) (bpHeadT (transC2 M)) := by
  have h : ∃ a, transC2 M = Dprin (transV M) a := by
    unfold transC2 transC2Core
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split <;> exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := h
  rw [ha]
  rfl

private theorem marked_zero_ape (N : PS) (hN : TPS N) (hmono : monoT N = true) :
    Marked N 0 := by
  refine ⟨hN, by simp [adm, nadm, nextR, nextrel1], ?_⟩
  have := hmono
  simp only [monoT, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this.2

/-! ## `Trans_mono_RN_ge2`（Isabelle layerB 9011）— `Trans.psimps` 展開なしの移植

Isabelle は `Trans.psimps` を手展開して `c₂` の全分岐を再構成するが、Lean には
`RightAncesAux_RTPS_equation`（`RightAnces` の再帰式）と
`RightAncesAux_eq_RightNodes_Trans`（`RightAnces = RightNodes ∘ Trans`）があるので、
再帰式を一段ほどくだけで済む。単項簡約列（長さ > 1）の `RightNodes (Trans M)` は
「祖先ブロック `a`（非空）＋ 末尾 1〜2 成分」なので長さ ≥ 2。 -/
private theorem Trans_mono_RN_ge2_ape (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M) :
    2 ≤ (RightNodes (Trans M)).length := by
  have hM : TPS M := RTPS_TPS M hR
  have hEq : RightAncesAux (Lng M) M = RightNodes (Trans M) :=
    RightAncesAux_eq_RightNodes_Trans M (Lng M) hR (le_refl _)
  have hf : Lng M = (Lng M - 1) + 1 := by omega
  -- 祖先ブロック `a` の非空性（`if` の分解より先に用意する）
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hjplt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have := parent_lt_of_hasParent M 0 (Lng M - 1) hp
    omega
  have hjmlt : Adm M (parent M 0 (Lng M - 1)) < Lng M - 1 := by
    have := Adm_le M (parent M 0 (Lng M - 1))
    omega
  have ha : 1 ≤ (if zeroT (seg M 0 (Adm M (parent M 0 (Lng M - 1)))) = true then [0]
      else RightAncesAux (Lng M - 1)
        (seg M 0 (Adm M (parent M 0 (Lng M - 1))))).length := by
    by_cases hza : zeroT (seg M 0 (Adm M (parent M 0 (Lng M - 1)))) = true
    · rw [if_pos hza]; simp
    · rw [if_neg hza]
      have hsR : RTPS (seg M 0 (Adm M (parent M 0 (Lng M - 1)))) :=
        RTPS_initial_slice M _ hR (by omega)
      have hsT : TPS (seg M 0 (Adm M (parent M 0 (Lng M - 1)))) := RTPS_TPS _ hsR
      rw [RightAncesAux_eq_RightNodes_Trans _ (Lng M - 1) hsR (by simp; omega)]
      have hne : RightNodes (Trans (seg M 0 (Adm M (parent M 0 (Lng M - 1))))) ≠ [] := by
        rw [Ne, RightNodes_eq_nil_iff]
        intro hzz
        exact hza ((Trans_preserves_zeroT _ hsT).2 hzz)
      exact List.length_pos_of_ne_nil hne
  rw [← hEq, hf, RightAncesAux_RTPS_equation (Lng M - 1) M hR]
  simp only [hmono, if_true]
  rw [if_neg (show ¬((Lng M - 1 == 0) = true) from by
    simp only [beq_iff_eq]; omega)]
  by_cases hz : zeroT (Pred M) = true
  · rw [if_pos hz]; simp
  · rw [if_neg hz]
    split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

/-! ## `Mark0_ne_Mark`（Isabelle layerB 9636）

簡約列の marked 列 `m > 0` について `Mark M m ≠ Trans M`。内部 (`m < Lng M - 1`) は
`RightNodes_Mark`（A47 形）の 3 分割 ＋ 始切片側の `Trans_mono_RN_ge2_ape` で
`a₀ ≠ []` を出し、長さ比較で矛盾。右端 (`m = Lng M - 1`) は
`Mark_rightmost1_forward` で `Mark M m = D_{M₁,ₘ} 0` となり `RightNodes` 長 1 < 2。 -/
private theorem Mark0_ne_Mark_ape (M : PS) (m : ℕ) (hR : RTPS M)
    (hmk0 : Marked M 0) (hmk : Marked M m) (hpos : 0 < m) :
    Mark M m ≠ Trans M := by
  have hM : TPS M := RTPS_TPS M hR
  have hmlt : m < Lng M := by
    have h : le0 M m (Lng M - 1) = true := hmk.2.2
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hlen : 1 < Lng M := by omega
  have hnz : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    left; omega
  have hmono : monoT M = true := by
    simp only [monoT, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hnz, hmk0.2.2⟩
  have hRN2 : 2 ≤ (RightNodes (Trans M)).length :=
    Trans_mono_RN_ge2_ape M hR hmono hlen
  intro heq
  by_cases hint : m < Lng M - 1
  · obtain ⟨a₀, a₁, hRT, hSseg, hRMark⟩ := RightNodes_Mark M m hmk hR hpos hint
    -- 始切片 `seg M 0 m` は長さ `m+1 ≥ 2` の単項簡約列
    have hsR : RTPS (seg M 0 m) := RTPS_initial_slice M m hR (by omega)
    have hsLen : Lng (seg M 0 m) = m + 1 := by simp
    have hsmk0 : Marked (seg M 0 m) 0 := by
      have := marked_slice M 0 0 m hmk0 (le_refl _) (by omega) (by omega)
      simpa using this
    have hsnz : zeroT (seg M 0 m) = false := by
      simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      left; omega
    have hsmono : monoT (seg M 0 m) = true := by
      simp only [monoT, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨hsnz, hsmk0.2.2⟩
    have hsRN2 : 2 ≤ (RightNodes (Trans (seg M 0 m))).length :=
      Trans_mono_RN_ge2_ape _ hsR hsmono (by omega)
    rw [hSseg] at hsRN2
    simp only [List.length_append, List.length_cons, List.length_nil] at hsRN2
    -- `Mark M m = Trans M` は `a₀ = []` を強いる
    have hlenEq : (RightNodes (Mark M m)).length = (RightNodes (Trans M)).length := by
      rw [heq]
    rw [hRT, hRMark] at hlenEq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlenEq
    omega
  · -- 右端: `m = Lng M - 1`
    have hmeq : m = Lng M - 1 := by omega
    have hmk1 : Mark M m = Dprin (entry M 1 m : ℕ∞) BZero := by
      rw [hmeq]; exact Mark_rightmost1_forward M hR hnz
    rw [heq] at hmk1
    rw [hmk1] at hRN2
    simp at hRN2

/-! ## STEP 1: `Admpos` 分岐の body-split（Isabelle `trans_admpos_body_split` 26573）

`M ∈ RT_PS ∩ PT_PS`, `j₁ = Lng M - 1 > 1`, `transJm1 M > 0`,
`Trans (Pred M) ≠ 0_B` の下で、`Trans (Pred M)` と `Trans M` は同一の外側 principal
`D_{M₁,₀}(…)` であり、その本体は共通接頭辞 `pre` と共通の末尾 principal 頭 `w` を
共有する。幾何自由（`w ∈ {M₁,ⱼ′₁, M₁,ⱼ′₀}` の同定は §7.4 の別ステップ）。 -/
theorem trans_admpos_body_split (hsplit : ScbOuterSurgerySplit)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (ht1ne : Trans (Pred M) ≠ BZero) :
    ∃ pre w u2 u3,
      Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) (addBT pre (Dprin w u2)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞) (addBT pre (Dprin w u3)) := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hpredMono : monoT (Pred M) = true := monoT_Pred_long M hM hmono (by omega)
  -- 外側 principal
  obtain ⟨outP, outM⟩ := trans_admpos_outer_principal_ape M hR hmono hj1gt ht1ne
  -- `Admpos` では `c₁ ≠ Trans (Pred M)`（左端第 1 基点）
  obtain ⟨hmk, hmlt⟩ := marked_transJm1_ape M hR hmono hj1gt
  have hmkP : Marked (Pred M) (transJm1 M) :=
    Marked_Pred M (transJm1 M) hM hlen hmk (by omega)
  have hmk0P : Marked (Pred M) 0 :=
    marked_zero_ape (Pred M) (RTPS_TPS _ hpredR) hpredMono
  have hc1ne : transC1 M ≠ Trans (Pred M) :=
    Mark0_ne_Mark_ape (Pred M) (transJm1 M) hpredR hmk0P hmkP hAdmpos
  -- 外科機構の局所化
  obtain ⟨s1, b1, dsd, bRP, dM⟩ := trans_surgery_localized_ape M hR hmono hj1gt ht1ne
  -- `c₁ = D_v t₂`, `c₂ = D_v body2`
  have hc1pc : (PB (transC1 M)).length = 1 :=
    transC1_single_principal M hR hmono (by simpa [transJ1, lastIdx] using hlen)
      (by simpa [transT1] using ht1ne)
  have c1eq : transC1 M = Dprin (transV M) (transT2 M) := principal_reconstruct hc1pc
  have c2eq : transC2 M = Dprin (transV M) (bpHeadT (transC2 M)) := transC2_outer_ape M
  set e10 : ℕ∞ := (entry M 1 0 : ℕ∞) with he10
  set BP : BT := bpHeadT (Trans (Pred M)) with hBPdef
  set v : ℕ∞ := transV M with hv
  set t2 : BT := transT2 M with ht2
  set body2 : BT := bpHeadT (transC2 M) with hbody2
  -- `X = D_e10 BP` の scb 分解
  have ddX : scb_decomp (Dprin e10 BP) s1 (flatBT (Dprin v t2)) b1 := by
    rw [← outP, ← c1eq]; exact dsd
  -- `D_v body2` は d-free（`c₂ = Mark M j₋₁ ∈ T_B`）
  have hc2TB : transC2 M ∈ T_B := by
    rw [← Mark_transJm1_eq_transC2 M hR hmono hlen ht1ne]
    exact Mark_mem_T_B M (transJm1 M) hR hmk
  have dfv : dfree_BP (.db v body2) = true := by
    have hh := hc2TB
    rw [c2eq] at hh
    simpa [T_B, Dprin, dfree_BT, dfree_BPList] using hh
  -- `D_e10 BP ≠ D_v t₂`
  have hneD : Dprin e10 BP ≠ Dprin v t2 := by
    rw [← outP, ← c1eq]
    exact fun h => hc1ne h.symm
  -- `BP ≠ 0_B`（長さ勘定）
  have hXfl : flatBT (Dprin e10 BP) = s1 ++ flatBT (Dprin v t2) ++ b1 := ddX.1
  have hBPne : BP ≠ BZero := by
    intro hBP0
    have hXfl0 : flatBT (Dprin e10 BZero) = s1 ++ flatBT (Dprin v t2) ++ b1 := by
      rw [← hBP0]; exact hXfl
    have hge2 := flatBT_length_pos_ape t2
    have hsum := congrArg List.length hXfl0
    simp only [List.length_append, Dprin, flatBT, flatBP, BZero,
      List.length_cons, List.length_nil] at hsum
    have hs0 : s1 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hb0 : b1 = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hs0, hb0, List.nil_append, List.append_nil] at hXfl0
    exact hneD (by rw [hBP0]; exact flatBT_injective hXfl0)
  -- 像側の平坦形
  have hYflat : flatBT (Trans M) = s1 ++ flatBT (Dprin v body2) ++ b1 := by
    have hh := dM.1
    rw [c2eq] at hh
    exact hh
  obtain ⟨pre, w, u2, u3, hsp1, hsp2⟩ :=
    hsplit e10 v BP body2 t2 (Trans M) s1 b1 hBPne ddX dfv hneD hYflat
  exact ⟨pre, w, u2, u3, by rw [outP, hsp1], hsp2⟩

/-! ## `wid` の帰納降下ステップ（Isabelle `m_8_2_wid_step` 28837）

`Admpos` regime では body-split が共通の末尾 principal 頭 `w` を出すので、
`RightNodes`（末尾 principal を辿る）は両変換の添字 `1` で同じ `w` を読む。
すなわち第 2 `RightNodes` 成分は `Pred` 不変。 -/
theorem wid_step (hsplit : ScbOuterSurgerySplit)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (ht1ne : Trans (Pred M) ≠ BZero) :
    (RightNodes (Trans M)).getD 1 0 = (RightNodes (Trans (Pred M))).getD 1 0 := by
  obtain ⟨pre, w, u2, u3, hsp1, hsp2⟩ :=
    trans_admpos_body_split hsplit M hR hmono hj1gt hAdmpos ht1ne
  rw [hsp1, hsp2]
  simp

/-! ## `wid` の還元形（Isabelle `m_8_2_wid_of_predRN` 28893）

`M` 自身の最終枝ノード `j′₁ = FirstNodes(M)_{J₁}`, `j′₀ = Joints(M)_{J₁}` に対して
測った `Pred` 側の事実（`predRN`）から、キーストーン残差 `wid M` が直ちに従う。
（結論 `wid M` は Isabelle の生の選言と定義的に等しい: `wid_iff` は `Iff.rfl`。） -/
theorem wid_of_predRN (hsplit : ScbOuterSurgerySplit)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (ht1ne : Trans (Pred M) ≠ BZero)
    (predRN :
      (RightNodes (Trans (Pred M))).getD 1 0 =
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
        (RightNodes (Trans (Pred M))).getD 1 0 =
          entry M 1 ((Joints M).getD ((Br M).length - 1) 0)) :
    wid M := by
  rw [wid_iff, wid_step hsplit M hR hmono hj1gt hAdmpos ht1ne]
  exact predRN

/-! ## `wid` の `Pred`-`wid` 還元形（Isabelle `m_8_2_wid_of_predwid` 29038）

`Pred M` 側の `wid`（`JN = Lng (Br (Pred M)) - 1` で測ったもの）と、§6.4 の
`Pred` ブロック値転送 `jt` / `ft`、および `j′₁ = j₁` 崩壊時の補正 `cp` から
`wid M` を得る。Isabelle の `defines`（`J1`/`j0'`/`j1'`/`JN`）は文に展開した。 -/
theorem wid_of_predwid (hsplit : ScbOuterSurgerySplit)
    (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (ht1ne : Trans (Pred M) ≠ BZero)
    (predwid :
      (RightNodes (Trans (Pred M))).getD 1 0 =
          entry (Pred M) 1
            ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) ∨
        (RightNodes (Trans (Pred M))).getD 1 0 =
          entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0))
    (jt : entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
        entry M 1 ((Joints M).getD ((Br M).length - 1) 0))
    (ft : (FirstNodes M).getD ((Br M).length - 1) 0 ≠ Lng M - 1 →
        entry (Pred M) 1 ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0))
    (cp : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 →
        (RightNodes (Trans (Pred M))).getD 1 0 =
          entry (Pred M) 1
            ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0)) :
    wid M := by
  have step := wid_step hsplit M hR hmono hj1gt hAdmpos ht1ne
  rw [wid_iff]
  by_cases hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
  · exact Or.inr (by rw [step, cp hj1eq, jt])
  · rcases predwid with h | h
    · exact Or.inl (by rw [step, h, ft hj1eq])
    · exact Or.inr (by rw [step, h, jt])

#print axioms trans_admpos_outer_principal_ape
#print axioms marked_transJm1_ape
#print axioms trans_surgery_localized_ape
#print axioms Trans_mono_RN_ge2_ape
#print axioms Mark0_ne_Mark_ape
#print axioms trans_admpos_body_split
#print axioms wid_step
#print axioms wid_of_predRN
#print axioms wid_of_predwid

end PSS
