import «8».«8.4-exch84-regsp»
import «8».«8.4-exch84-e1ge-run»
import «8».«8.4-exch84-mcond»
import «7».«7.3-Pred-Trans-descend»
import «7».«7.3-two-column»
import «7».«7.3-Trans-IncrFirst-Red»
import «7».«7.1-lessBT-linear-order»
import «8».«8.2-condV-terminal-slice-Trans»
import «8».«8.1-condI-masterCF»
import «8».«8.2-strongmono-slice»

/-!
# §8.4 交換パッケージの `base0` 脚（`Base0_condIIIIV` の discharge へ向けて）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
- 移植元（Isabelle）:
  * `Trans_take_lessBT` (`isabelle/layerB/pss_wip.thy:23943`): 簡約列の真の始切片は
    `Trans` を厳密に下げる（`Pred_Trans_descend` の d-一般化）。**Lean tree に未移植**
    だったので本ファイルで公開移植する（base0 の take-2 比較に必須）。
  * `crx_base0_of_run` (:88555, condIII) / `cnv_base0_of_run` (:102029, condIV):
    RUN 辺 `nextR M 1 j₋₂ (j₋₂+1)` から、`j₋₂` 錨の簡約 Pred スライス `X` の
    2 列頭 `(ub, ub+1)`（`ub = M_{1,Lng M-1} - 1`）を使って
    `D_{ub} 0_B <_B bpHeadT (Trans (Pred (s84x_Np M)))` を出す。
  * 錨橋 `A0eq` (`cpx_condIII_mnform` 内, wip:98787): `oi5_IIIIV_pkg` (layerC:1213) が
    `crx_base0_of_run`（`s84x_Np` 錨）を declared Prop（`s84x_N` 錨）へ移すのに使う
    `bpHeadT (Trans (Pred (s84x_N M))) = bpHeadT (Trans (Pred (s84x_Np M)))`。
    これは `crx_slice_red_value`（wip:88799, REGSP 消費）の bpHeadT で、
    `crx_slice_red_value` / REGSP 正則性が未移植なので named 残差として露出する。

## 本ファイルの分担・状態

1. `Trans_take_lessBT`（公開・完全証明）— 未移植の take-descent 資産。
2. `base0_core_b0`（private・完全証明）— 2 列頭の簡約スライス `X` に対する base0 核
   `lessBT (Dprin ub 0_B) (bpHeadT (Trans X))`（Isabelle 88686–88736 の逐語）。
3. `Base0Np_condIIIIV`（`s84x_Np` 錨版、完全証明）— `crx_base0_of_run` の Lean 版。
4. `Base0_A0bridge`（named Prop, 残差）＋ `Base0_condIIIIV_holds`（house pattern）。

- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 = `Base0_A0bridge`（= `crx_slice_red_value`(REGSP) の bpHeadT）。
- 訂正: なし。
- Private helper suffix: `_b0`。
-/

namespace PSS

/-! ## 1. `Trans_take_lessBT`（公開移植） -/

/-- `Pred (M.take (k+1)) = M.take k`（`k+1 ≤ Lng M`, `k+1 > 1`）。純リスト事実。 -/
private theorem Pred_take_succ_b0 (M : PS) (k : ℕ)
    (hk : 1 ≤ k) (hle : k + 1 ≤ Lng M) :
    Pred (M.take (k + 1)) = M.take k := by
  have hLM : Lng M = M.length := rfl
  have hlen : (M.take (k + 1)).length = k + 1 := by
    rw [List.length_take]; omega
  have hnle : ¬ Lng (M.take (k + 1)) ≤ 1 := by
    show ¬ (M.take (k + 1)).length ≤ 1; rw [hlen]; omega
  rw [Pred, if_neg hnle, List.dropLast_eq_take, hlen, List.take_take]
  congr 1
  omega

/-- Isabelle `Trans_take_lessBT` (layerB/pss_wip.thy:23943)。
簡約とは限らない `TPS M` の真の始切片 `M.take n`（`0 < n < Lng M`）は `Trans` を
厳密に下げる。`Pred_Trans_descend`（§7.3, `TPS` 版）の `d`-一般化。 -/
theorem Trans_take_lessBT (M : PS) (n : ℕ) (npos : 0 < n) (nlt : n < Lng M) :
    lessBT (Trans (M.take n)) (Trans M) = true := by
  have hLM : Lng M = M.length := rfl
  have gen : ∀ d, n + d ≤ Lng M → 0 < d →
      lessBT (Trans (M.take n)) (Trans (M.take (n + d))) = true := by
    intro d
    induction d with
    | zero => intro _ h; exact absurd h (by omega)
    | succ d ih =>
        intro hle _
        have hkpos : 1 ≤ n + d := by omega
        have hlenU : Lng (M.take (n + (d + 1))) = n + (d + 1) := by
          show (M.take (n + (d + 1))).length = n + (d + 1)
          rw [List.length_take]; omega
        have UT : TPS (M.take (n + (d + 1))) := by
          have : 0 < Lng (M.take (n + (d + 1))) := by rw [hlenU]; omega
          exact List.ne_nil_of_length_pos this
        have ULt1 : 1 < Lng (M.take (n + (d + 1))) := by rw [hlenU]; omega
        have predeq : Pred (M.take (n + (d + 1))) = M.take (n + d) := by
          have := Pred_take_succ_b0 M (n + d) hkpos (by omega)
          rwa [show n + d + 1 = n + (d + 1) from by omega] at this
        have step : lessBT (Trans (M.take (n + d))) (Trans (M.take (n + (d + 1)))) = true := by
          have h := Pred_Trans_descend (M.take (n + (d + 1))) UT ULt1
          rwa [predeq] at h
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · subst hd0; simpa using step
        · have IH := ih (by omega) hdpos
          exact lessBT_linear_trans _ _ _ IH step
  have hsum : n + (Lng M - n) = Lng M := by omega
  have hfin := gen (Lng M - n) (by omega) (by omega)
  rw [hsum] at hfin
  have hMfull : M.take (Lng M) = M := by
    show M.take M.length = M; exact List.take_length
  rwa [hMfull] at hfin

#print axioms Trans_take_lessBT

/-! ## 2. `base0` の核（2 列頭の簡約スライス）— private -/

/-- 頭が異なる principal 項の順序: `u < v ⟹ D_u c <_B D_v c'`。 -/
private theorem lessBT_Dprin_lt_head_b0 (c c' : BT) {u v : ℕ∞} (h : u < v) :
    lessBT (Dprin u c) (Dprin v c') = true := by
  simp only [Dprin, lessBT, lessBPList, lessBP]
  rw [decide_eq_true h]; simp

/-- 頭が同じ principal 項の順序は本体の順序に一致（前向き）。 -/
private theorem lessBT_Dprin_body_b0 (v : ℕ∞) {a b : BT}
    (h : lessBT (Dprin v a) (Dprin v b) = true) : lessBT a b = true := by
  have e : lessBT (Dprin v a) (Dprin v b) = lessBT a b := by
    simp only [Dprin, lessBT, lessBPList, lessBP, lt_self_iff_false, decide_false,
      beq_self_eq_true, Bool.true_and, Bool.false_or, Bool.and_false, Bool.or_false]
  rw [e] at h; exact h

/-- `Dprin` は本体に単射。 -/
private theorem Dprin_body_inj_b0 (v : ℕ∞) {a b : BT} (h : Dprin v a = Dprin v b) : a = b := by
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true, true_and] at h
  exact h

/-- Isabelle `crx_base0_of_run` の核 (wip:88686–88736): 簡約スライス `X`（`DT_PS`）の
先頭 2 列が `(ub, ub+1)` なら `D_{ub} 0_B <_B bpHeadT (Trans X)`。
take-2 の厳密下降（`Trans_take_lessBT`）と 2 列 `Trans`（`two_column_Trans`）＋
principal 頭（`Trans_principal_head`）の消去で出る。 -/
private theorem base0_core_b0 (X : PS) (ub : ℕ)
    (hXD : DTPS X) (hL2 : 2 ≤ Lng X)
    (hub0 : entry X 1 0 = ub) (hub1 : entry X 1 1 = ub + 1) :
    lessBT (Dprin (ub : ℕ∞) BZero) (bpHeadT (Trans X)) = true := by
  obtain ⟨XR, monoX, _descX⟩ := (DTPS_iff X).mp hXD
  -- T2 = seg X 0 1（2 列スライス）
  have T2D : DTPS (seg X 0 1) :=
    strongmono_slice X 0 1 hXD (by norm_num) (by omega) (by exact Nat.zero_le _)
  obtain ⟨T2R, monoT2, _⟩ := (DTPS_iff (seg X 0 1)).mp T2D
  have LT2 : Lng (seg X 0 1) = 2 := by simp [length_seg]
  have hL2pos : (0 : ℕ) < Lng (seg X 0 1) := by rw [LT2]; norm_num
  have hL2pos1 : (1 : ℕ) < Lng (seg X 0 1) := by rw [LT2]; norm_num
  have eT20 : entry (seg X 0 1) 1 0 = ub := by
    have h := entry_seg X 0 1 1 0 hL2pos; rw [h]; simpa using hub0
  have eT21 : entry (seg X 0 1) 1 1 = ub + 1 := by
    have h := entry_seg X 0 1 1 1 hL2pos1; rw [h]; simpa using hub1
  have TT2 : Trans (seg X 0 1)
      = Dprin (ub : ℕ∞) (Dprin ((ub + 1 : ℕ) : ℕ∞) BZero) := by
    have h := two_column_Trans (seg X 0 1) T2R monoT2 LT2
    rw [eT20, eT21] at h; exact h
  have TXhead : Trans X = Dprin (ub : ℕ∞) (bpHeadT (Trans X)) := by
    have h := Trans_principal_head X XR monoX; rw [hub0] at h; exact h
  have step1 : lessBT (Dprin (ub : ℕ∞) BZero) (Dprin ((ub + 1 : ℕ) : ℕ∞) BZero) = true :=
    lessBT_Dprin_lt_head_b0 BZero BZero (by exact_mod_cast Nat.lt_succ_self ub)
  by_cases hLXgt : 2 < Lng X
  · have htake : X.take 2 = seg X 0 1 := take_eq_seg X 2 (by norm_num) (by omega)
    have hdesc := Trans_take_lessBT X 2 (by norm_num) hLXgt
    rw [htake, TT2, TXhead] at hdesc
    have hbody : lessBT (Dprin ((ub + 1 : ℕ) : ℕ∞) BZero) (bpHeadT (Trans X)) = true :=
      lessBT_Dprin_body_b0 (ub : ℕ∞) hdesc
    exact lessBT_linear_trans _ _ _ step1 hbody
  · have hsegwhole : seg X 0 (Lng X - 1) = X := by
      rw [seg_eq_take_drop_adm X 0 (Lng X - 1) (Nat.zero_le _) (by omega)]
      have hlast : Lng X - 1 + 1 = Lng X := by omega
      simp [hlast]
    have hsegX : seg X 0 1 = X := by
      rw [show (1 : ℕ) = Lng X - 1 from by omega]; exact hsegwhole
    rw [hsegX] at TT2
    have heq : Dprin ((ub + 1 : ℕ) : ℕ∞) BZero = bpHeadT (Trans X) := by
      have h : Dprin (ub : ℕ∞) (Dprin ((ub + 1 : ℕ) : ℕ∞) BZero)
             = Dprin (ub : ℕ∞) (bpHeadT (Trans X)) := by rw [← TT2]; exact TXhead
      exact Dprin_body_inj_b0 (ub : ℕ∞) h
    rw [← heq]; exact step1

#print axioms base0_core_b0

/-! ## 3. `s84x_Np` 錨版の base0（`crx_base0_of_run` の Lean 版、完全証明） -/

/-- Isabelle `m_8_4_oper_props_1(1)` (wip:52810) の内訳（`8.4-exch84-mcond` の private
`jm2_lt_transJ0_mc` の再掲）: 条件(III)/(IV) 下で `j₋₂ < transJ0`。 -/
private theorem jm2_lt_transJ0_b0 (M : PS)
    (hMT : TPS M) (hmono : monoT M = true) (hp : hasParent M 1 (Lng M - 1) = true)
    (j1gt : 1 < Lng M - 1) (branch : transCondIII M = true ∨ transCondIV M = true) :
    s84x_jm2 M < transJ0 M := by
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hnext0 : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    show nextR M 0 (parent M 0 (Lng M - 1)) (Lng M - 1) = true
    exact hasParent_next_fseq M 0 (Lng M - 1) hp0
  have le0jm2 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    have h := (s84c1_jm2_basic M hp).2.2
    simpa [leR] using h
  have hent0 : entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M (s84x_jm2 M) (Lng M - 1) (Lng M - 1) hMT jm2lt (le_refl _) le0jm2
  have jm2le : s84x_jm2 M ≤ transJ0 M :=
    nextR0_largest_below M (transJ0 M) (s84x_jm2 M) (Lng M - 1) hnext0 jm2lt hent0
  have hge : entry M 1 (Lng M - 1) ≤ entry M 1 (transJ0 M) := by
    rcases branch with h | h
    · have h' := h
      simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq] at h'
      show entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)
      exact h'.1.2
    · have h' := h
      simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq] at h'
      show entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)
      exact h'.1.2
  have hlt1 : entry M 1 (s84x_jm2 M) < entry M 1 (Lng M - 1) := (s84c1_jm2_basic M hp).2.1
  have hne : s84x_jm2 M ≠ transJ0 M := by
    intro heq; rw [heq] at hlt1; omega
  omega

/-- `s84x_Np` 錨版 base0（named Prop）。Isabelle `crx_base0_of_run`
(wip:88555) / `cnv_base0_of_run` (:102029) の結論。 -/
def Base0Np_condIIIIV : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    lessBT (Dprin ((entry M 1 (Lng M - 1) - 1 : ℕ) : ℕ∞) BZero)
           (bpHeadT (Trans (Pred (s84x_Np M)))) = true

/-- Isabelle `crx_base0_of_run` (wip:88555) の Lean 完全証明。
RUN 辺（`wgx37_m0run_of_e1ge` ＋ `e1x_e1ge_uncond`）で `j₋₂` 錨簡約 Pred スライス
`X = Red (seg M j₋₂ (Lng M - 2))` の 2 列頭 `(ub, ub+1)`（`ub = M_{1,Lng M-1} - 1`）を組み、
`base0_core_b0` で `D_{ub} 0_B <_B bpHeadT (Trans X)`、`Pred (s84x_Np M)` に読み戻す
（`Trans_Red` ＋ `Red_Pred` ＋ `Pred_Red_terminal_slice`）。 -/
theorem Base0Np_condIIIIV_holds : Base0Np_condIIIIV := by
  intro M hST hmono hp j1gt branch
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have jm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have jm2ltj0 : s84x_jm2 M < transJ0 M := jm2_lt_transJ0_b0 M hMT hmono hp j1gt branch
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have j0lt : transJ0 M < Lng M - 1 := by
    show lastParent M < Lng M - 1
    show parent M 0 (lastIdx M) < Lng M - 1
    exact parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  have jm2ltLm2 : s84x_jm2 M < Lng M - 2 := by omega
  -- RUN 辺
  have E1GE : entry M 1 (Lng M - 1) ≤ entry M 1 (s84x_jm2 M + 1) :=
    e1x_e1ge_uncond M hST hmono hp j1gt
  have RUN : nextR M 1 (s84x_jm2 M) (s84x_jm2 M + 1) = true := wgx37_m0run_of_e1ge M hp E1GE
  obtain ⟨condA, _condB⟩ := RTPS_condAB M hMR
  -- `ub = v1 - 1`
  have ubeq : entry M 1 (s84x_jm2 M) + 1 = entry M 1 (Lng M - 1) := by
    have h := RedCondA_apply M condA 1 (Lng M - 1) (by norm_num) (by omega) hp
    change entry M 1 (s84x_jm2 M) + 1 = entry M 1 (Lng M - 1) at h
    exact h
  -- run 値 `M_{1,j₋₂+1} = ub + 1`
  have huniqP : ∀ y, nextR M 1 y (s84x_jm2 M + 1) = true → y = s84x_jm2 M :=
    fun y hy => nextR1_unique_mr M y (s84x_jm2 M) (s84x_jm2 M + 1) hy RUN
  have hpP : hasParent M 1 (s84x_jm2 M + 1) = true :=
    (hasParent_iff_unique_fseq M 1 (s84x_jm2 M + 1)).mpr ⟨s84x_jm2 M, RUN, huniqP⟩
  have parP : parent M 1 (s84x_jm2 M + 1) = s84x_jm2 M :=
    parent_eq_of_unique_fseq M 1 (s84x_jm2 M + 1) (s84x_jm2 M) RUN huniqP
  have wval : entry M 1 (s84x_jm2 M + 1) = entry M 1 (s84x_jm2 M) + 1 := by
    have h := RedCondA_apply M condA 1 (s84x_jm2 M + 1) (by norm_num) (by omega) hpP
    rw [parP] at h; omega
  -- `leR M 0 j₋₂ (Lng M - 2)`（ancestor_tree_1 で降下、le0 climb 不要）
  have leRjm2 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    simpa [leR] using (s84c1_jm2_basic M hp).2.2
  have leRLm2 : leR M 0 (s84x_jm2 M) (Lng M - 2) = true :=
    ancestor_tree_1 M (s84x_jm2 M) (Lng M - 2) (Lng M - 1) hMT leRjm2 (by omega) (by omega)
  -- 簡約スライス `X`
  have hXD : DTPS (Red (seg M (s84x_jm2 M) (Lng M - 2))) :=
    standard_slice_Red_strongmono M (s84x_jm2 M) (Lng M - 2) hST jm2ltLm2 (by omega) leRLm2
  have hLseg : Lng (seg M (s84x_jm2 M) (Lng M - 2)) = Lng M - 1 - s84x_jm2 M := by
    rw [length_seg]; omega
  have hSegT : TPS (seg M (s84x_jm2 M) (Lng M - 2)) := by
    have h0 : 0 < Lng (seg M (s84x_jm2 M) (Lng M - 2)) := by rw [hLseg]; omega
    exact List.ne_nil_of_length_pos h0
  have hLX : Lng (Red (seg M (s84x_jm2 M) (Lng M - 2))) = Lng M - 1 - s84x_jm2 M := by
    rw [Lng_Red_invariance _ hSegT, hLseg]
  have hLX2 : 2 ≤ Lng (Red (seg M (s84x_jm2 M) (Lng M - 2))) := by rw [hLX]; omega
  -- `X = IncrFirstN dd (Red X)` で行1エントリ転送
  have segIF : seg M (s84x_jm2 M) (Lng M - 2)
      = IncrFirstN (entry M 0 (s84x_jm2 M) - entry M 1 (s84x_jm2 M))
          (Red (seg M (s84x_jm2 M) (Lng M - 2))) :=
    (ancestor_slice_Red_IncrFirst M (s84x_jm2 M) (Lng M - 2) hMR jm2ltLm2 (by omega) leRLm2).2.2
  have entX : ∀ k, k < Lng (seg M (s84x_jm2 M) (Lng M - 2)) →
      entry (Red (seg M (s84x_jm2 M) (Lng M - 2))) 1 k = entry M 1 (s84x_jm2 M + k) := by
    intro k hk
    have hseg := entry_seg M (s84x_jm2 M) (Lng M - 2) 1 k hk
    have hif : entry (seg M (s84x_jm2 M) (Lng M - 2)) 1 k
        = entry (Red (seg M (s84x_jm2 M) (Lng M - 2))) 1 k := by
      conv_lhs => rw [segIF]
      rw [entry_IncrFirstN_one]
    rw [← hif]; exact hseg
  have hk0 : (0 : ℕ) < Lng (seg M (s84x_jm2 M) (Lng M - 2)) := by rw [hLseg]; omega
  have hk1 : (1 : ℕ) < Lng (seg M (s84x_jm2 M) (Lng M - 2)) := by rw [hLseg]; omega
  have e0X : entry (Red (seg M (s84x_jm2 M) (Lng M - 2))) 1 0
      = entry M 1 (Lng M - 1) - 1 := by
    have h := entX 0 hk0
    simp only [Nat.add_zero] at h
    omega
  have e1X : entry (Red (seg M (s84x_jm2 M) (Lng M - 2))) 1 1
      = (entry M 1 (Lng M - 1) - 1) + 1 := by
    have h := entX 1 hk1
    rw [h, wval]; omega
  have hcore := base0_core_b0 (Red (seg M (s84x_jm2 M) (Lng M - 2)))
    (entry M 1 (Lng M - 1) - 1) hXD hLX2 e0X e1X
  -- 読み戻し `Trans (Pred (s84x_Np M)) = Trans X`
  have hNpL : Lng (s84x_Np M) = Lng M - s84x_jm2 M := by
    show Lng (seg M (s84x_jm2 M) (Lng M - 1)) = Lng M - s84x_jm2 M
    rw [length_seg]; omega
  have hNpT : TPS (s84x_Np M) := by
    have h0 : 0 < Lng (s84x_Np M) := by rw [hNpL]; omega
    exact List.ne_nil_of_length_pos h0
  have hNpL2 : 1 < Lng (s84x_Np M) := by rw [hNpL]; omega
  have hPredT : TPS (Pred (s84x_Np M)) := by
    have hL := length_Pred (s84x_Np M) hNpL2
    have h0 : 0 < Lng (Pred (s84x_Np M)) := by rw [hL, hNpL]; omega
    exact List.ne_nil_of_length_pos h0
  have hpr : Pred (Red (s84x_Np M)) = Red (seg M (s84x_jm2 M) (Lng M - 2)) := by
    have h := Pred_Red_terminal_slice M (s84x_jm2 M) (Lng M - 1) jm2lt
    rw [show Lng M - 1 - 1 = Lng M - 2 from by omega] at h
    exact h
  have hread : Trans (Pred (s84x_Np M)) = Trans (Red (seg M (s84x_jm2 M) (Lng M - 2))) := by
    rw [Trans_Red (Pred (s84x_Np M)) hPredT, Red_Pred (s84x_Np M) hNpT, hpr]
  rw [hread]; exact hcore

#print axioms Base0Np_condIIIIV_holds

/-! ## 4. 錨橋（named 残差）＋ `Base0_condIIIIV`（house pattern） -/

/-- 錨橋（named 残差）: Isabelle `A0eq`（`cpx_condIII_mnform` 内, wip:98787）。
`bpHeadT (Trans (Pred (s84x_N M))) = bpHeadT (Trans (Pred (s84x_Np M)))`。
`s84x_N`（`j₋₃` 錨）と `s84x_Np`（`j₋₂` 錨）の Pred スライスの principal 本体の一致。
Isabelle では `crx_slice_red_value` (wip:88799, REGSP 正則性を消費) の bpHeadT で出るが、
`crx_slice_red_value` / REGSP は未移植なので named 残差として露出する。 -/
def Base0_A0bridge : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    bpHeadT (Trans (Pred (s84x_N M))) = bpHeadT (Trans (Pred (s84x_Np M)))

/-- `Base0_condIIIIV`（«8».«8.4-exch84-regsp»）の house-pattern drop-in、
錨橋 `Base0_A0bridge` を消費（green-modulo）。`Base0Np_condIIIIV_holds`
（`s84x_Np` 錨版, 完全証明）＋ 橋で `s84x_N` 錨へ移す。 -/
theorem Base0_condIIIIV_holds (hbr : Base0_A0bridge) : Base0_condIIIIV := by
  intro M hST hmono hp j1gt branch
  rw [hbr M hST hmono hp j1gt branch]
  exact Base0Np_condIIIIV_holds M hST hmono hp j1gt branch

#print axioms Base0_condIIIIV_holds

end PSS
