import «6».«6.3-admof-slice»
import «6».«6.4-mono-slice»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.5-Red-Pred-commute»
import «6».«6.6-reduced-leftend»
import «7».«7.4-RightAnces-RightNodes»
import «8».«8.2-subexpr-setup»
import «8».«8.2-condV-rightmost-parent»

/-!
# §8.2 部分表現の単項成分と `Pred` — w-identification (wid) 機構

- 原文: `tmp/content.md` 3432–3435 付近（§8.2 補題の `j₁ - TrMax(M)` に関する
  帰納法が使う「`RightNodes (Trans M)` の第 2 成分の同定」）。
- Isabelle (`isabelle/layerB/pss_wip.thy`) との対応:
  - `wid`（定義）: Isabelle には `definition` は無く、`m_8_2_wid` (29605) の結論式
    そのものが `wid`。本ファイルではその式を `def wid` として転記し、`wid_iff` で
    生の選言形に接続する。
  - `keystone_imp_wid` ← `m_8_2_keystone_imp_wid` (28936)
  - `ft_transport`     ← `m_8_2_ft_transport` (29392)
  - `jt_transport`     ← `m_8_2_jt_transport` (29460)
  - **未移植**: `wid_step` (28837) / `wid_of_predRN` (28893) / `wid_of_predwid`
    (29038)。三者はいずれも Isabelle `trans_admpos_body_split`
    (`layerB/pss_wip.thy:26573` — `trans_surgery_localized` /
    `scb_outer_surgery_split` / `trans_admpos_outer_principal` の外科機構) を
    経由する。この機構は Lean 側に未移植のため、本ファイルからは全面的に除外した
    （sorry を置かない方針）。詳細は本 wave の報告 "needs" を参照。
- 公開: `wid`（def）, `wid_iff`, `keystone_imp_wid`, `ft_transport`, `jt_transport`。
- 依存（主要）:
  - `RightNodes_Dprin` / `RightNodes_addBT_Dprin`（7.4-RightAnces-RightNodes）
  - `subexpr_component_Pred_setup`（8.2-subexpr-setup — `j′₁ < Lng M`,
    `j′₀ ≤ TrMax M < j′₁`, `TrMax M < Lng M - 1`）
  - `wf21_Br_eq_seg`（8.2-condV-rightmost-parent — 最終枝 = 接尾切片）
  - `Br_Pred_core_nontrunk` / `FirstNodes_Pred_core` / `Joints_Pred_core` /
    `entry_Pred` / `length_Pred` / `Pred_TPS`（6.5-Red-Pred-commute）
    ＝ Isabelle の `wid_Br_Pred` / `wid_FirstNodes_Pred` / `wid_Joints_Pred` /
    `wid_entry1_Pred_agree` に相当（Lean 側は既に vestigial 仮定なしの形で存在）
  - `FirstNodes_TrMax_Joints` / `FirstNodes_Joints_mono` / `Joints_getD` /
    `TrMax_bound`（6.4）, `TrMax_trunk_step`（6.4-mono-slice）,
    `Adm_adm` / `Adm_le`（6.3-admof-slice）, `RTPS_TPS`（6.6-reduced-leftend）
- 方針: Isabelle `wid_Br_Pred` / `wid_FirstNodes_Pred` / `wid_Joints_Pred` の再導出は
  不要（Lean の `*_Pred_core` 群が既に vestigial 仮定を持たない）。
  `wid_adm_trunk_interior_False` / `wid_transJ0_eq_TrMax` / `wid_JBr_Pred_imp` は
  private (`_sw`) として移植した。
- 状態: 本ファイル単独で green（sorry 0）。ただしスコープは部分的
  （`wid_step` 系 3 本は上記理由で未収録）。
-/

namespace PSS

/-! ## 定義: w-identification 残差 `wid`

Isabelle `m_8_2_wid` (29605) の結論形。`J₁ = Lng (Br M) - 1` として
`RightNodes (Trans M)` の第 2 成分は、最終枝の first node `j′₁ = FirstNodes(M)_{J₁}`
の行 1 成分か、最終 joint `j′₀ = Joints(M)_{J₁}` の行 1 成分のいずれかである。 -/
def wid (M : PS) : Prop :=
  (RightNodes (Trans M)).getD 1 0 =
      entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
    (RightNodes (Trans M)).getD 1 0 =
      entry M 1 ((Joints M).getD ((Br M).length - 1) 0)

/-- `wid` の定義展開（生の選言形との接続）。 -/
theorem wid_iff (M : PS) :
    wid M ↔
      ((RightNodes (Trans M)).getD 1 0 =
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
        (RightNodes (Trans M)).getD 1 0 =
          entry M 1 ((Joints M).getD ((Br M).length - 1) 0)) :=
  Iff.rfl

/-! ## 私的補助層（suffix `_sw`） -/

private theorem getD_default_sw {α : Type} (l : List α) (n : ℕ) (d d' : α)
    (h : n < l.length) : l.getD n d = l.getD n d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

private theorem getLastD_cons_eq_sw {α : Type} :
    ∀ (l : List α) (a d : α), (a :: l).getLastD d = (a :: l).getD l.length d := by
  intro l
  induction l with
  | nil => intro a d; rfl
  | cons b bs ih =>
      intro a d
      have hstep : (a :: b :: bs).getLastD d = (b :: bs).getLastD a := rfl
      rw [hstep, ih b a]
      simp only [List.length_cons, List.getD_cons_succ]
      exact getD_default_sw (b :: bs) bs.length a d (by simp)

private theorem getLastD_eq_getD_sw {α : Type} (l : List α) (d : α) (hl : l ≠ []) :
    l.getLastD d = l.getD (l.length - 1) d := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a as => simpa using getLastD_cons_eq_sw as a d

/-- Isabelle `rn1_outer_inner_trailing` (28912): 本体の末尾が principal
`D_b s` である外側 principal `D_a (pre + D_b s)` の `RightNodes` 第 2 成分は `b`。 -/
private theorem rn1_outer_inner_trailing_sw (a b : ℕ) (pre s : BT) :
    (RightNodes (Dprin (a : ℕ∞) (addBT pre (Dprin (b : ℕ∞) s)))).getD 1 0 = b := by
  rw [RightNodes_Dprin, RightNodes_addBT_Dprin]
  simp

/-- Isabelle `wid_adm_trunk_interior_False` (29340): 幹の内部添字
`1 ≤ k < TrMax M` は `M` 非許容。 -/
private theorem adm_trunk_interior_False_sw (M : PS) (k : ℕ) (hM : TPS M)
    (hk1 : 1 ≤ k) (hkT : k < TrMax M) : adm M k = false := by
  have hs1 : nextR M 1 k (k + 1) = true := TrMax_trunk_step M k hM hkT
  have hs2 : nextR M 1 (k - 1) (k - 1 + 1) = true :=
    TrMax_trunk_step M (k - 1) hM (by omega)
  have hkeq : k - 1 + 1 = k := by omega
  rw [hkeq] at hs2
  simp [adm, nadm, hs1, hs2]

/-- Isabelle `wid_transJ0_eq_TrMax` (29359): `Admpos` 下で最終列の行 0 の親が
幹に入るなら、それは丁度 `TrMax M`。 -/
private theorem transJ0_eq_TrMax_sw (M : PS) (hM : TPS M)
    (hjple : transJ0 M ≤ TrMax M) (hAdmpos : 0 < transJm1 M) :
    transJ0 M = TrMax M := by
  have hadmA : adm M (Adm M (transJ0 M)) = true := Adm_adm M (transJ0 M)
  have hleA : Adm M (transJ0 M) ≤ transJ0 M := Adm_le M (transJ0 M)
  have hposA : 0 < Adm M (transJ0 M) := hAdmpos
  by_contra hne
  have hjplt : transJ0 M < TrMax M := lt_of_le_of_ne hjple hne
  have hkT : Adm M (transJ0 M) < TrMax M := by omega
  have hfalse := adm_trunk_interior_False_sw M (Adm M (transJ0 M)) hM (by omega) hkT
  rw [hfalse] at hadmA
  exact Bool.false_ne_true hadmA

/-- `Br M ≠ []` は `TrMax M ≠ Lng M - 1` と同値な向きの一方。 -/
private theorem trmax_ne_of_Brne_sw (M : PS) (hBrne : Br M ≠ []) :
    TrMax M ≠ Lng M - 1 := by
  intro heq
  exact hBrne (by simp [Br, heq])

/-- 最終枝ブロックの長さ（`wf21_Br_eq_seg` の読み出し）。 -/
private theorem lastBr_len_sw (M : PS) (hM : TPS M) (hBrne : Br M ≠ []) :
    Lng ((Br M).getLastD []) =
      Lng M - (FirstNodes M).getD ((Br M).length - 1) 0 := by
  have hbl := getLastD_eq_getD_sw (Br M) ([] : PS) hBrne
  have hseg := wf21_Br_eq_seg M hM hBrne
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  rw [hbl, hseg, length_seg]
  omega

/-- Isabelle `wid_JBr_Pred_imp` (29168) 相当（本ファイルでは長さ等式を直接使う）:
`Br (Pred M)` の長さは `Br M` の長さか、それより 1 小さい。 -/
private theorem Br_Pred_length_sw (M : PS) (hM : TPS M) (hlen : 1 < Lng M)
    (hBrne : Br M ≠ []) :
    (Br (Pred M)).length =
      (if Lng ((Br M).getLastD []) ≤ 1 then (Br M).length - 1 else (Br M).length) := by
  have hne := trmax_ne_of_Brne_sw M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  rw [Br_Pred_core_nontrunk M hM hlen hne]
  by_cases hcase : Lng ((Br M).getLastD []) ≤ 1
  · rw [if_pos hcase, if_pos hcase]
    have hl : ((Br M).dropLast ++ ([] : List PS)).length = (Br M).length - 1 := by simp
    rw [hl]
  · rw [if_neg hcase, if_neg hcase]
    have hl : ((Br M).dropLast ++ [((Br M).getLastD []).dropLast]).length
        = (Br M).length - 1 + 1 := by simp
    rw [hl]
    omega

/-! ## `keystone_imp_wid`（Isabelle `m_8_2_keystone_imp_wid` 28936）

キーストーン結論（`m_8_2_subexpr_component_Pred_of_wid` の 4 分岐選言）は
どの分岐でも `Trans M = D_{M_{1,0}}(… + D_{M_{1,b}} …)`（`b ∈ {j′₁, j′₀}`）を
確定させるので、`RightNodes` の第 2 成分＝残差 `wid` はそのまま読み出せる。 -/
theorem keystone_imp_wid (M : PS)
    (key :
      ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M) ∧
          (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) =
              entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) ∨
            adm M ((Joints M).getD ((Br M).length - 1) 0) = true) ∧
          (∃! t₁ : BT, Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t₁
                (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                  BZero)))) ∨
      ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 ∧
          entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) <
            entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0) ∧
          adm M ((Joints M).getD ((Br M).length - 1) 0) = false ∧
          (∃! t12 : BT × BT,
            Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
            Trans M = Dprin (entry M 1 0 : ℕ∞)
              (addBT t12.1
                (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                  t12.2)))) ∨
      (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2))) ∨
      (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t123.1
              (Dprin (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
                t123.2.2)))) :
    wid M := by
  rcases key with ⟨_, _, _, t₁, ht₁, _⟩ | ⟨_, _, _, t12, ht12, _⟩ |
      ⟨t123, ht123, _⟩ | ⟨t123, ht123, _⟩
  · left
    rw [ht₁.2]
    exact rn1_outer_inner_trailing_sw _ _ t₁ BZero
  · right
    rw [ht12.2]
    exact rn1_outer_inner_trailing_sw _ _ t12.1 t12.2
  · left
    rw [ht123.2]
    exact rn1_outer_inner_trailing_sw _ _ t123.1 t123.2.2
  · right
    rw [ht123.2]
    exact rn1_outer_inner_trailing_sw _ _ t123.1 t123.2.2

/-! ## `ft_transport`（Isabelle `m_8_2_ft_transport` 29392）

`j′₁ ≠ j₁`（最終枝の長さ > 1）の regime では `Lng (Br (Pred M)) = Lng (Br M)`、
すなわち `JN = J₁` であり、`FirstNodes_Pred_core` が二つの first node を同定し、
`j′₁ < Lng M - 1` なので行 1 成分は `entry_Pred` で一致する。 -/
theorem ft_transport (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1)
    (hbrP : Br (Pred M) ≠ [])
    (hj1ne : (FirstNodes M).getD ((Br M).length - 1) 0 ≠ Lng M - 1) :
    entry (Pred M) 1 ((FirstNodes (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
      entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) := by
  have hMT : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hne := trmax_ne_of_Brne_sw M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hset := subexpr_component_Pred_setup M hR hmono hBrne hj1gt
  -- `j′₁ < Lng M - 1`
  have hj1lt : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M - 1 := by
    have := hset.2.1
    omega
  -- 最終枝の長さ > 1、従って `Br (Pred M)` は `Br M` と同じ長さ
  have hlast := lastBr_len_sw M hMT hBrne
  have hnotle : ¬ Lng ((Br M).getLastD []) ≤ 1 := by
    rw [hlast]; omega
  have hlenP := Br_Pred_length_sw M hMT hlen hBrne
  rw [if_neg hnotle] at hlenP
  have hJNeq : (Br (Pred M)).length - 1 = (Br M).length - 1 := by rw [hlenP]
  have hJBrP : (Br (Pred M)).length - 1 < (Br (Pred M)).length := by
    have := List.length_pos_of_ne_nil hbrP
    omega
  -- first node の同定と行 1 成分の転送
  have hfn := FirstNodes_Pred_core M hMT hlen hne ((Br (Pred M)).length - 1) hJBrP
  rw [hfn, hJNeq]
  exact entry_Pred M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) hj1lt

/-! ## `jt_transport`（Isabelle `m_8_2_jt_transport` 29460）

無条件（`Admpos` 下）。`j′₁ ≠ j₁`（case A）は `Joints_Pred_core` を `JN = J₁` で
使うだけ。`j′₁ = j₁`（case B）は `Admpos` の潰れ `transJ0 M = TrMax M`
（`transJ0_eq_TrMax_sw`）と joint の単調性から `Joints(M)_{J₁-1} = Joints(M)_{J₁}
= TrMax M` を出す。どちらの joint も幹にあるので行 1 成分は `entry_Pred` で転送。 -/
theorem jt_transport (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdmpos : 0 < transJm1 M)
    (hbrP : Br (Pred M) ≠ []) :
    entry (Pred M) 1 ((Joints (Pred M)).getD ((Br (Pred M)).length - 1) 0) =
      entry M 1 ((Joints M).getD ((Br M).length - 1) 0) := by
  have hMT : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hne := trmax_ne_of_Brne_sw M hBrne
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJ1 : (Br M).length - 1 < (Br M).length := by omega
  have hset := subexpr_component_Pred_setup M hR hmono hBrne hj1gt
  have htrlt : TrMax M < Lng M - 1 := hset.2.2.2.2.2.2.2.2.2
  have hj0tr : (Joints M).getD ((Br M).length - 1) 0 ≤ TrMax M := hset.2.2.1
  have hJBrP : (Br (Pred M)).length - 1 < (Br (Pred M)).length := by
    have := List.length_pos_of_ne_nil hbrP
    omega
  have hjPN := Joints_Pred_core M hMT hmono hlen hne ((Br (Pred M)).length - 1) hJBrP
  have hlast := lastBr_len_sw M hMT hBrne
  have hlenP := Br_Pred_length_sw M hMT hlen hBrne
  by_cases hj1eq : (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
  · -- case B: 最終枝は単項、`Br (Pred M) = (Br M).dropLast`
    have hle1 : Lng ((Br M).getLastD []) ≤ 1 := by rw [hlast, hj1eq]; omega
    rw [if_pos hle1] at hlenP
    have hBrL2 : 2 ≤ (Br M).length := by
      have := List.length_pos_of_ne_nil hbrP
      omega
    have hJNeq : (Br (Pred M)).length - 1 = (Br M).length - 1 - 1 := by
      rw [hlenP]
    -- `j′₀ = transJ0 M = TrMax M`
    have hj0parent : (Joints M).getD ((Br M).length - 1) 0 = transJ0 M := by
      rw [Joints_getD M ((Br M).length - 1) hJ1, hj1eq]
      rfl
    have hj0Tr : transJ0 M = TrMax M :=
      transJ0_eq_TrMax_sw M hMT (by omega) hAdmpos
    have hj0eq : (Joints M).getD ((Br M).length - 1) 0 = TrMax M := by
      rw [hj0parent, hj0Tr]
    -- 一つ手前の joint も `TrMax M` に潰れる
    have hlt : (Br M).length - 1 - 1 < (Br M).length - 1 := by omega
    have hmono2 := FirstNodes_Joints_mono M ((Br M).length - 1 - 1)
      ((Br M).length - 1) hMT hmono hlt hJ1
    have hJ1m : (Br M).length - 1 - 1 < (Br M).length := by omega
    have hle2 := (FirstNodes_TrMax_Joints M ((Br M).length - 1 - 1) hMT hmono hJ1m).1
    have hjJN : (Joints M).getD ((Br M).length - 1 - 1) 0 = TrMax M := by
      have := hmono2.2.1
      omega
    rw [hjPN, hJNeq, hjJN, hj0eq]
    exact entry_Pred M 1 (TrMax M) htrlt
  · -- case A: 最終枝の長さ > 1、`JN = J₁`
    have hnotle : ¬ Lng ((Br M).getLastD []) ≤ 1 := by
      have hj1lt : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M - 1 := by
        have := hset.2.1
        omega
      rw [hlast]; omega
    rw [if_neg hnotle] at hlenP
    have hJNeq : (Br (Pred M)).length - 1 = (Br M).length - 1 := by rw [hlenP]
    rw [hjPN, hJNeq]
    exact entry_Pred M 1 ((Joints M).getD ((Br M).length - 1) 0) (by omega)

#print axioms wid_iff
#print axioms keystone_imp_wid
#print axioms ft_transport
#print axioms jt_transport

end PSS
