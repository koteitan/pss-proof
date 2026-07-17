import «8».«8.7-fseq-descend»
import «8».«8.3-kind0-base-basepoint»
import «6».«6.6-reduced-fseq»
import «6».«6.8-standard-slice-Br-descending»
import «6».«6.2-P-fseq»
import «6».«6.2-P-additivity»
import «6».«6.2-P-components-nonmulti»
import «7».«7.3-Trans-welldefined»

/-!
# §8.7 補題（基本列の降下性）の未配線 brick 2 本

`«8».«8.7-fseq-descend»` が露出する 16 本の `FseqDesc_*` のうち、
他 agent が扱わない最後の 2 本を Isabelle から移植して落とす。

- 原文: `tmp/content.md` 5869（§8.7）。本ファイルの 2 本はいずれも原文の命題ではなく、
  §8.7 dispatcher を支える機構補題（Isabelle 側で `f7x_`/`operI_` 接頭辞のもの）。
  訂正: なし（A 番号の該当なし）。
- Isabelle:
  - `operI_j0zero_trans_mult` (isabelle/layerB/pss_wip.thy:36977)
    ＝ 条件(I)・`j₀ = 0` の基本列の copy-additivity
    `Trans (M[k+1]) = Trans (Pred M) ×_B (k+1)`。
    一歩分 `operI_j0zero_trans_step` (同 :36809) の `k` に関する帰納。
    その step が使う下請け: `oper_d0zero_expand` (同 :17095 系)、
    `operI_Suc_append` (同 :17621)、`Lng_operI`、`m_6_6_reduced_oper`、
    `oper_d0zero_le0_confined` (同 :16800 系)、
    `oper_d0zero_lastblock_to_end` (同 :17188)、`trans_multi_split` (同 :45489)。
  - `f7x_Trans_append_Pblocks` (同 :51888)
    ＝ `P` ブロック境界で切れる連接の `Trans` 加法性。`(P N).length` に関する
    measure 帰納。下請け: `m_6_2_P_components_2`、`multiT_imp_Lng_gt1`、
    `poper_last_P_multi`、`idxsum_concat_P`、`Pcut_le`、`Trans_singleton`、
    `trans_multi_split_full`、`trans_multiT_prefix_RT_PS`、`f7x_addBT_assoc`。
- 依存（ビルド済みのみ import）: `8.7-fseq-descend`（`FseqDesc_operI_j0zero_trans_mult`
  /`FseqDesc_f7x_Trans_append_Pblocks` の 2 つの `Prop`。drop-in 先）、
  `8.3-kind0-base-basepoint`（`kind0_base_basepoint` ＝ Isabelle
  `oper_d0zero_lastblock_to_end` の役割。最終ブロック開始が `M[n]` の基点＝
  `Marked` の `leR` 成分がそのまま `le_last` になる）、`6.6-reduced-fseq`
  （`RTPS_oper` ＝ `m_6_6_reduced_oper`、`length_oper_tiling` ＝ `Lng_operI`、
  `oper_TPS`）、`6.8-standard-slice-Br-descending`（`oper_d0zero_expand_68`
  ＝ `oper_d0zero_expand`、`oper_d0zero_le0_confined_68`
  ＝ `oper_d0zero_le0_confined`）、`6.2-P-fseq`（`P_nonempty`/`P_concat`
  ＝ `idxsum_concat_P`/`P_last_multi` ＝ `poper_last_P_multi`/`multi_length_fseq`
  ＝ `multiT_imp_Lng_gt1`）、`6.2-P-additivity`（`Pcut_props` ＝ `Pcut_le`、
  `Pcut_not_candidate` ＝ `Pcut` の最小性）、`6.2-P-components-nonmulti`
  （`P_components_multi_iff` ＝ `m_6_2_P_components_2`）、`7.3-Trans-welldefined`
  （`Trans_Mark_multi_equations` ＝ `trans_multi_split_full`、
  `trans_multi_prefix_RTPS` ＝ `trans_multiT_prefix_RT_PS`）。
- 状態: ✅ 証明済（sorry 0、仮定 0、axioms = propext/Classical.choice/Quot.sound）。
  露出する `Prop` は無い。private 接尾辞は `_dl2`。

## Isabelle からの差分

- `oper_d0zero_lastblock_to_end` は移植せず、既存の `kind0_base_basepoint`
  (`8.3-kind0-base-basepoint`) の (1) から `Marked` の `leR` 成分を取る。
  `j₀ = 0` では `j₀ + (n-1)*w = n*j₁` なので、そのまま `le_last` になる。
- `m_8_1_condI_oper_pow_j0zero`（`M[n] = concat (replicate n (Pred M))`）は不要。
  基底 `k = 0` は `oper_d0zero_expand_68 M 1` を直接計算して `oper M 1 = Pred M`
  を出す（`concat`/`replicate` を経由しない）。
- Isabelle の `Pcut` は `Least`、Lean の `Pcut` は `List.range` 上の `find?`。
  最小性は `Pcut_not_candidate`、候補性は `Pcut_props` で置き換える。
-/

namespace PSS

/-! ## 小さな Buchholz 補題 -/

/-- Isabelle `f7x_addBT_assoc`。 -/
private theorem addBT_assoc_dl2 (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  cases a; cases b; cases c; simp [addBT]

/-- Isabelle `f7x_addBT_zero_right`。 -/
private theorem addBT_zero_right_dl2 (a : BT) : addBT a BZero = a := by
  cases a; simp [addBT, BZero]

/-! ## `Trans [(0,0)] = 0_B`（Isabelle `Trans_singleton` の `v = 0` 特殊化） -/

private theorem Trans_zero_pair_dl2 : Trans [((0 : ℕ), (0 : ℕ))] = BZero := by
  have hT : TPS ([((0 : ℕ), (0 : ℕ))]) := by simp [TPS]
  have hz : zeroT [((0 : ℕ), (0 : ℕ))] = true := by simp [zeroT, Lng, entry]
  simpa using (Trans_preserves_zeroT _ hT).mp hz

/-! ## 小さなリスト補題 -/

private theorem getLastD_append_dl2 {α : Type _} (l m : List α) (d : α) (h : m ≠ []) :
    (l ++ m).getLastD d = m.getLastD d := by
  cases m with
  | nil => simp at h
  | cons a as =>
    obtain ⟨x, hx⟩ : ∃ x, (a :: as).getLast? = some x :=
      ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
    simp [List.getLastD_eq_getLast?, List.getLast?_append, hx]

private theorem head_dropLast_dl2 (l : List PS) (hl : 1 < l.length) :
    l.dropLast.getD 0 [] = l.getD 0 [] := by
  match l, hl with
  | _ :: _ :: _, _ => simp [List.dropLast]

/-! ## `f7x_Trans_append_Pblocks` (pss_wip.thy:51888) -/

/-- `A ++ N` の `P` 分解が `P A ++ P N` に一致するなら、`Trans` は連接で加法的
（`P N` の先頭ブロックが `[(0,0)]` のときだけ `D_0 0` が挟まる）。
Isabelle `f7x_Trans_append_Pblocks` の逐語移植（`(P N).length` の measure 帰納）。 -/
private theorem Trans_append_Pblocks_dl2 (A : PS) :
    ∀ N : PS, RTPS (A ++ N) → RTPS N → P (A ++ N) = P A ++ P N →
      Trans (A ++ N) = addBT (Trans A)
        (if (P N).getD 0 [] = [(0, 0)] then addBT (Dprin 0 BZero) (Trans N)
         else Trans N) := by
  intro N
  induction hwf : (P N).length using Nat.strong_induction_on generalizing N with
  | _ n IH =>
  intro KR NR Peq
  subst hwf
  have KT : TPS (A ++ N) := RTPS_TPS _ KR
  have NT : TPS N := RTPS_TPS _ NR
  have PAne : P A ≠ [] := P_nonempty A
  have PNne : P N ≠ [] := P_nonempty N
  -- `A ++ N` は multi（`P` の長さが 2 以上）
  have lenK : (P (A ++ N)).length = (P A).length + (P N).length := by
    rw [Peq]; simp
  have hPApos : 0 < (P A).length := List.length_pos_of_ne_nil PAne
  have hPNpos : 0 < (P N).length := List.length_pos_of_ne_nil PNne
  have lenK2 : 1 < (P (A ++ N)).length := by omega
  have muK : multiT (A ++ N) = true :=
    (P_components_multi_iff (A ++ N) KT).mpr lenK2
  have LK : 1 < Lng (A ++ N) := multi_length_fseq _ KT muK
  obtain ⟨lastK, butK⟩ := P_last_multi (A ++ N) muK LK
  have hcutK := Pcut_props (A ++ N) LK
  have LKe : Lng (A ++ N) = Lng A + Lng N := by simp [Lng]
  have LNpos : 0 < Lng N := List.length_pos_of_ne_nil NT
  by_cases hlen1 : (P N).length = 1
  · -- `P N = [N]`: 最終ブロックが `N` そのもの
    have PN : P N = [N] := by
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen1
      have hcat := P_concat N
      rw [hx] at hcat
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hcat
      rw [hx, hcat]
    have lastK2 : (P (A ++ N)).getLastD [] = N := by
      rw [Peq, PN, getLastD_append_dl2 _ _ _ (by simp)]
      simp
    have dropN : (A ++ N).drop (Pcut (A ++ N)) = N := by
      rw [← lastK]; exact lastK2
    have hlenD : Lng (A ++ N) - Pcut (A ++ N) = Lng N := by
      have := congrArg Lng dropN
      simpa [Lng] using this
    have hPcut : Pcut (A ++ N) = Lng A := by omega
    have takeA : (A ++ N).take (Pcut (A ++ N)) = A := by
      rw [hPcut]; simp [Lng]
    have hsplit := (Trans_Mark_multi_equations (A ++ N) KR muK).1
    simp only [dropN, takeA] at hsplit
    by_cases hz : N = [((0 : ℕ), (0 : ℕ))]
    · have hTN : Trans N = BZero := by rw [hz]; exact Trans_zero_pair_dl2
      have hhead : (P N).getD 0 [] = [((0 : ℕ), (0 : ℕ))] := by
        rw [PN]; simpa using hz
      have hbeq : (N == [((0 : ℕ), (0 : ℕ))]) = true := by simpa using hz
      rw [hsplit, if_pos hbeq, if_pos hhead, hTN, addBT_zero_right_dl2]
    · have hhead : ¬ ((P N).getD 0 [] = [((0 : ℕ), (0 : ℕ))]) := by
        rw [PN]; simpa using hz
      have hbeq : ¬ ((N == [((0 : ℕ), (0 : ℕ))]) = true) := by simpa using hz
      rw [hsplit, if_neg hbeq, if_neg hhead]
  · -- `1 < (P N).length`: 最後の `P` ブロックを剥がして帰納
    have lenN2 : 1 < (P N).length := by omega
    have muN : multiT N = true := (P_components_multi_iff N NT).mpr lenN2
    have LN : 1 < Lng N := multi_length_fseq _ NT muN
    obtain ⟨lastN, butN⟩ := P_last_multi N muN LN
    have hcutN := Pcut_props N LN
    set N' : PS := N.take (Pcut N) with hN'
    set c : PS := N.drop (Pcut N) with hc
    have lastKN : (P (A ++ N)).getLastD [] = c := by
      rw [Peq, getLastD_append_dl2 _ _ _ PNne]; exact lastN
    have dropc : (A ++ N).drop (Pcut (A ++ N)) = c := by
      rw [← lastK]; exact lastKN
    have hlenD : Lng (A ++ N) - Pcut (A ++ N) = Lng N - Pcut N := by
      have h1 := congrArg Lng dropc
      have h2 : Lng c = Lng N - Pcut N := by simp [hc, Lng]
      simpa [Lng, h2] using h1
    have hPcut : Pcut (A ++ N) = Lng A + Pcut N := by omega
    have takeK : (A ++ N).take (Pcut (A ++ N)) = A ++ N' := by
      rw [hPcut, hN']
      simp [List.take_append, Lng]
    have PeqK' : P (A ++ N') = P A ++ P N' := by
      have h1 : P (A ++ N') = (P (A ++ N)).dropLast := by rw [butK, takeK]
      rw [h1, Peq, List.dropLast_append_of_ne_nil PNne, butN]
    have KR' : RTPS (A ++ N') := by
      have := trans_multi_prefix_RTPS (A ++ N) KR muK
      rwa [takeK] at this
    have NR' : RTPS N' := trans_multi_prefix_RTPS N NR muN
    have lenN' : (P N').length = (P N).length - 1 := by
      rw [← butN]; simp
    have lenless : (P N').length < (P N).length := by omega
    have IHapp := IH (P N').length lenless N' rfl KR' NR' PeqK'
    have headeq : (P N').getD 0 [] = (P N).getD 0 [] := by
      rw [← butN]; exact head_dropLast_dl2 (P N) lenN2
    -- `A ++ N` と `N` の multi split（同じ最終ブロック `c`）
    have splitK : Trans (A ++ N)
        = addBT (Trans (A ++ N')) (if c = [((0 : ℕ), (0 : ℕ))]
            then Dprin 0 BZero else Trans c) := by
      have h := (Trans_Mark_multi_equations (A ++ N) KR muK).1
      simp only [dropc, takeK] at h
      by_cases hcz : c = [((0 : ℕ), (0 : ℕ))]
      · rw [h]; simp [hcz]
      · have hb : (c == [((0 : ℕ), (0 : ℕ))]) = false := by simpa using hcz
        rw [h]; simp [hb, hcz]
    have splitN : Trans N
        = addBT (Trans N') (if c = [((0 : ℕ), (0 : ℕ))]
            then Dprin 0 BZero else Trans c) := by
      have h := (Trans_Mark_multi_equations N NR muN).1
      simp only [← hN', ← hc] at h
      by_cases hcz : c = [((0 : ℕ), (0 : ℕ))]
      · rw [h]; simp [hcz]
      · have hb : (c == [((0 : ℕ), (0 : ℕ))]) = false := by simpa using hcz
        rw [h]; simp [hb, hcz]
    by_cases hz : (P N).getD 0 [] = [((0 : ℕ), (0 : ℕ))]
    · have hz' : (P N').getD 0 [] = [((0 : ℕ), (0 : ℕ))] := by rw [headeq]; exact hz
      rw [splitK, IHapp, if_pos hz', if_pos hz, addBT_assoc_dl2,
        addBT_assoc_dl2, ← splitN]
    · have hz' : ¬ ((P N').getD 0 [] = [((0 : ℕ), (0 : ℕ))]) := by
        rw [headeq]; exact hz
      rw [splitK, IHapp, if_neg hz', if_neg hz, addBT_assoc_dl2, ← splitN]

/-- Isabelle `f7x_Trans_append_Pblocks` (pss_wip.thy:51888) の drop-in。 -/
theorem f7x_Trans_append_Pblocks_holds : FseqDesc_f7x_Trans_append_Pblocks := by
  intro A N hKR hNR hPeq
  exact Trans_append_Pblocks_dl2 A N hKR hNR hPeq

#print axioms f7x_Trans_append_Pblocks_holds

/-! ## `operI_j0zero_trans_mult` (pss_wip.thy:36977)

Isabelle `operI_j0zero_trans_step` (同 :36809) の `k` に関する帰納。
-/

/-! ### Isabelle `kind0_parent_facts` (pss_wip.thy:13671) -/

private theorem nextR_parent_dl2 (M : PS) (i j₁ : ℕ)
    (hp : hasParent M i j₁ = true) : nextR M i (parent M i j₁) j₁ = true := by
  unfold hasParent at hp
  unfold parent
  have hlen : (parents M i j₁).length = 1 := by simpa using hp
  match hm : parents M i j₁ with
  | [] => rw [hm] at hlen; simp at hlen
  | x :: xs =>
      have hx : x ∈ parents M i j₁ := by rw [hm]; simp
      have := List.of_mem_filter (l := List.range (Lng M))
        (p := fun j₀ => nextR M i j₀ j₁) (by simpa [parents] using hx)
      simpa [hm] using this

/-- Isabelle `kind0_parent_facts` の (2)(3)(4)(5)(6)。 -/
private theorem kind0_parent_facts_dl2 (M : PS)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    parent M 0 (Lng M - 1) < Lng M - 1 ∧
    ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∧
    hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true ∧
    1 < Lng M := by
  have hpar := nextR_parent_dl2 M 0 (Lng M - 1) hp0
  have h0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hpar
  have hfacts := h0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hfacts
  have hlt : parent M 0 (Lng M - 1) < Lng M - 1 := hfacts.1.1.2
  have he0 : entry M 0 (parent M 0 (Lng M - 1)) < entry M 0 (Lng M - 1) := hfacts.1.2
  refine ⟨hlt, by omega, ?_, by omega⟩
  have hi : idx1 M (Lng M - 1) = 0 := by simp [idx1, e1z]
  rw [hi]; exact hp0

/-! ### ブロック `B` は `Pred M`（Isabelle `m_8_1_condI_B_eq_Pred_j0zero`） -/

private theorem B_eq_Pred_dl2 (M : PS)
    (j0z : parent M 0 (Lng M - 1) = 0) (j1gt : 1 < Lng M - 1) :
    (List.range' (parent M 0 (Lng M - 1))
        (Lng M - 1 - parent M 0 (Lng M - 1))).map
        (fun j => (entry M 0 j, entry M 1 j)) = Pred M := by
  have hPred : Pred M = M.take (Lng M - 1) := by
    rw [Pred, if_neg (by omega)]
    exact List.dropLast_eq_take
  have hseg : M.take (Lng M - 1) = seg M 0 (Lng M - 1 - 1) :=
    take_eq_seg M (Lng M - 1) (by omega) (by omega)
  rw [hPred, hseg, seg, j0z]
  have harith : Lng M - 1 - 1 + 1 - 0 = Lng M - 1 - 0 := by omega
  rw [harith]

/-! ### Isabelle `operI_Suc_append` (pss_wip.thy:17621) -/

private theorem operI_Suc_append_dl2 (M : PS) (n : ℕ)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0) :
    oper M (n + 1) = oper M n ++
      (List.range' (parent M 0 (Lng M - 1))
        (Lng M - 1 - parent M 0 (Lng M - 1))).map
        (fun j => (entry M 0 j, entry M 1 j)) := by
  obtain ⟨_, hnz, hp, hL⟩ := kind0_parent_facts_dl2 M hp0 e1z
  have hn := oper_d0zero_expand_68 M n hL hnz hp e1z
  have hsn := oper_d0zero_expand_68 M (n + 1) hL hnz hp e1z
  simp only at hn hsn
  rw [hn, hsn, List.range_succ, List.flatMap_append]
  simp [List.append_assoc]

/-- `M[1] = Pred M`（Isabelle `m_8_1_condI_oper_pow_j0zero` の `n = 1` 相当。
`concat`/`replicate` を経由せず `oper_d0zero_expand_68` を直接計算する）。 -/
private theorem oper_one_eq_Pred_dl2 (M : PS)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0)
    (j0z : parent M 0 (Lng M - 1) = 0)
    (j1gt : 1 < Lng M - 1) :
    oper M 1 = Pred M := by
  obtain ⟨_, hnz, hp, hL⟩ := kind0_parent_facts_dl2 M hp0 e1z
  have h1 := oper_d0zero_expand_68 M 1 hL hnz hp e1z
  simp only at h1
  rw [h1, j0z]
  simp only [List.take_zero, List.nil_append, List.range_one, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  have := B_eq_Pred_dl2 M j0z j1gt
  rw [j0z] at this
  exact this

/-! ### Isabelle `operI_j0zero_trans_step` (pss_wip.thy:36809) -/

private theorem operI_j0zero_trans_step_dl2 (M : PS) (n : ℕ)
    (hMR : RTPS M)
    (hp0 : hasParent M 0 (Lng M - 1) = true)
    (e1z : entry M 1 (Lng M - 1) = 0)
    (j0z : parent M 0 (Lng M - 1) = 0)
    (j1gt : 1 < Lng M - 1) (hn : 1 ≤ n) :
    Trans (oper M (n + 1)) = addBT (Trans (oper M n)) (Trans (Pred M)) := by
  obtain ⟨hj0lt, hnz, hp, hL⟩ := kind0_parent_facts_dl2 M hp0 e1z
  have hMT : TPS M := RTPS_TPS M hMR
  have hi : idx1 M (Lng M - 1) = 0 := by simp [idx1, e1z]
  -- `M[n+1] = M[n] ++ Pred M`
  have hNsplit : oper M (n + 1) = oper M n ++ Pred M := by
    rw [operI_Suc_append_dl2 M n hp0 e1z, B_eq_Pred_dl2 M j0z j1gt]
  -- 長さ
  have hLngn : Lng (oper M n) = n * (Lng M - 1) := by
    have h := length_oper_tiling M n hL hnz hp
    simp only [hi, j0z, Nat.sub_zero, Nat.zero_add] at h
    exact h
  have hPredLng : Lng (Pred M) = Lng M - 1 := by
    rw [Pred, if_neg (by omega)]; simp [Lng]
  have hLngN : Lng (oper M (n + 1)) = (n + 1) * (Lng M - 1) := by
    rw [hNsplit]
    simp only [Lng, List.length_append]
    rw [show (oper M n).length = Lng (oper M n) from rfl,
      show (Pred M).length = Lng (Pred M) from rfl, hLngn, hPredLng]
    ring
  have hLN1 : 1 < Lng (oper M (n + 1)) := by
    rw [hLngN]; nlinarith
  have hNR : RTPS (oper M (n + 1)) := RTPS_oper M (n + 1) hMR (by omega)
  -- ブロック閉じ込め: `n·j₁` 未満の列は右端に届かない
  have hnoreach : ∀ j, j < n * (Lng M - 1) →
      leR (oper M (n + 1)) 0 j (Lng (oper M (n + 1)) - 1) = false := by
    intro j hj
    by_contra hcon
    have hle : leR (oper M (n + 1)) 0 j (Lng (oper M (n + 1)) - 1) = true := by
      simpa using hcon
    have hconf := oper_d0zero_le0_confined_68 M (n + 1) j
      (Lng (oper M (n + 1)) - 1) hMT hL hnz hp hi (by rw [j0z]; omega) hle
    rw [j0z] at hconf
    simp only [Nat.sub_zero, Nat.zero_add] at hconf
    have hdiv : j / (Lng M - 1) < n :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
    have hmul : (j / (Lng M - 1) + 1) * (Lng M - 1) ≤ n * (Lng M - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hLngN] at hconf
    have hexp : (n + 1) * (Lng M - 1) = n * (Lng M - 1) + (Lng M - 1) := by ring
    omega
  -- `M[n+1]` は multi
  have hnzT : zeroT (oper M (n + 1)) = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; omega
  have hnmono : monoT (oper M (n + 1)) = false := by
    have h0 := hnoreach 0 (by nlinarith)
    simp [monoT, h0]
  have muN : multiT (oper M (n + 1)) = true := by
    simp [multiT, hnzT, hnmono]
  -- 最終ブロック開始 `n·j₁` は `M[n+1]` の基点（`leR` 成分だけ使う）
  have hle_last : leR (oper M (n + 1)) 0 (n * (Lng M - 1))
      (Lng (oper M (n + 1)) - 1) = true := by
    have hbp := (kind0_base_basepoint M (n + 1) hMR (by omega) hp0 e1z).1 (by omega)
    have hmk := hbp.1
    rw [j0z] at hmk
    simp only [Nat.sub_zero, Nat.zero_add, Nat.add_sub_cancel] at hmk
    exact hmk.2.2
  -- `Pcut (M[n+1]) = n·j₁`
  have hcut := Pcut_props (oper M (n + 1)) hLN1
  have hPcut : Pcut (oper M (n + 1)) = n * (Lng M - 1) := by
    by_contra hne
    rcases Nat.lt_or_ge (Pcut (oper M (n + 1))) (n * (Lng M - 1)) with hlt | hge
    · rw [hnoreach _ hlt] at hcut; simp at hcut
    · have hgt : n * (Lng M - 1) < Pcut (oper M (n + 1)) := by omega
      have hnc := Pcut_not_candidate (oper M (n + 1)) hLN1 (n * (Lng M - 1)) hgt
      rw [hle_last] at hnc
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.true_eq_false,
        or_false] at hnc
      rcases hnc with h | h
      · exact h (by nlinarith)
      · exact h (by rw [hLngN]; nlinarith)
  -- take/drop で `M[n]` と `Pred M` が戻る
  have htakeN : (oper M (n + 1)).take (Pcut (oper M (n + 1))) = oper M n := by
    rw [hPcut, hNsplit, ← hLngn]
    simp [Lng]
  have hdropN : (oper M (n + 1)).drop (Pcut (oper M (n + 1))) = Pred M := by
    rw [hPcut, hNsplit, ← hLngn]
    simp [Lng]
  have hPrednz : Pred M ≠ [((0 : ℕ), (0 : ℕ))] := by
    intro hc
    have h2 : Lng (Pred M) = 1 := by rw [hc]; simp [Lng]
    rw [hPredLng] at h2
    omega
  have hsplit := (Trans_Mark_multi_equations (oper M (n + 1)) hNR muN).1
  simp only [htakeN, hdropN] at hsplit
  rw [hsplit, if_neg (by simpa using hPrednz)]

/-- Isabelle `operI_j0zero_trans_mult` (pss_wip.thy:36977) の drop-in。 -/
theorem operI_j0zero_trans_mult_holds : FseqDesc_operI_j0zero_trans_mult := by
  intro M k hMR hp0 e1z j0z j1gt
  induction k with
  | zero =>
      rw [oper_one_eq_Pred_dl2 M hp0 e1z j0z j1gt]
      cases hT : Trans (Pred M) with
      | trm ps => simp [multBT, addBT, BZero]
  | succ k ih =>
      rw [operI_j0zero_trans_step_dl2 M (k + 1) hMR hp0 e1z j0z j1gt (by omega), ih]
      rfl

#print axioms operI_j0zero_trans_mult_holds

end PSS
