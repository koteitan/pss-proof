import «8».«8.1-part4-setup»
import «8».«8.1-part4-mid»
import «8».«8.1-part4-trans»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.3-Mark-rightmost1»
import «7».«7.3-Trans-welldefined»
import «7».«7.2-scb-unique»
import «7».«7.2-scb-compose»
import «6».«6.3-marked-slice»
import «6».«6.5-Red-Pred-commute»
import «6».«6.2-P-additivity»
import «6».«6.6-P-condAB»
import «6».«6.2-P-fseq»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.6-reduced-leftend»
import «5».«5.1-ancestor-tree»

/-!
# §8.1 part (4-1) capstone — `c1_around_part4_1`

- 原文: `tmp/content.md` L3021–3036（part (4) の (4-1) 主張）
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  `m_8_1_c1_around_part4_1` (32085–32277) → `c1_around_part4_1`
- 依存（wave B-1 の公開定理を消費）:
  `c1_around_part4_setup`（8.1-part4-setup）,
  `c1_around_part4_Nred`（8.1-part4-mid）,
  `c1_around_part4_TransN_41` / `c1_around_part4_segpos`（8.1-part4-trans）,
  `Mark_Trans_repr` / `seg_Pred_eq`（7.4-Mark-Trans-repr）,
  `Mark_leftend_form_proper`（7.4-RightNodes-Mark, 推移 import）,
  `Mark_rightmost1_forward`（7.3-Mark-rightmost1）,
  `principal_flat_properties` / `Dprin_mem_T_B`（7.3-Trans-welldefined）,
  `scb_unique_decomp_unconditional`（7.2-scb-unique）,
  `scb_compose_dprin`（7.2-scb-compose）,
  `marked_slice`（6.3-marked-slice）,
  `ancestor_tree_1` / `row0_transitive`（5.1-ancestor-tree）,
  `flatBT_injective`（PSS/Flat）。
  Isabelle 側の part1/part2 引用は Lean では `Mark_Trans_repr`＋`seg_Pred_eq`
  （`c₁` の切片値）, `Mark_leftend_form_proper`（`c₁` の単項性）,
  `marked_slice`（切片 Marked）で私的に再導出（part1/part2 の主張全体は不要）。
- 私的補助（接尾辞 `_p1`）: `Dprin_trm_p1` / `flatBT_singleton_p1` /
  `flatBT_Dprin_p1`（flatten 変形）, `flatBPTail_append_singleton_p1`＋
  `addBT_principal_split_p1`（Isabelle `addBT_trailing_align`; 7.2-add-scb の
  private 補題の再証明）, `addBT_right_cancel_p1`＋`ex1_Dprin_addBT_p1`
  （Isabelle `ex1_Dpt_addBT`）。
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

/-! ## 私的補助: flatten 変形（Isabelle では `flatBT.simps` 直裁） -/

private theorem Dprin_trm_p1 (v : ℕ∞) (a : BT) :
    Dprin v a = .trm [.db v a] := rfl

private theorem flatBT_singleton_p1 (p : BP) :
    flatBT (.trm [p]) = flatBP p := by
  simp [flatBT]

private theorem flatBT_Dprin_p1 (v : ℕ∞) (a : BT) :
    flatBT (Dprin v a) = .dsym v :: flatBT a := by
  simp [Dprin, flatBT, flatBP]

/-! ## 私的補助: 末尾整列（Isabelle `addBT_trailing_align`, layerB 31857。
7.2-add-scb の private `addBT_principal_split` の再証明） -/

private theorem flatBPTail_append_singleton_p1 (xs : List BP) (p : BP) :
    flatBPTail (xs ++ [p]) = flatBPTail xs ++ (.cm :: flatBP p) := by
  induction xs with
  | nil => simp [flatBPTail]
  | cons q qs ih => simp [flatBPTail, ih, List.append_assoc]

private theorem addBT_principal_split_p1 (t : BT) :
    ∃ pre post : List Sym,
      (∀ x ∈ post, x = .rp) ∧
      ∀ p : BP,
        flatBT (addBT t (.trm [p])) = pre ++ flatBP p ++ post := by
  rcases t with ⟨xs⟩
  cases xs with
  | nil =>
      exact ⟨[], [], by simp, by intro p; simp [addBT, flatBT]⟩
  | cons q qs =>
      refine ⟨.lp :: (flatBP q ++ flatBPTail qs) ++ [.cm], [.rp], by simp, ?_⟩
      intro p
      cases qs with
      | nil => simp [addBT, flatBT, flatBPTail]
      | cons r rs =>
          change
            (.lp :: (flatBP q ++ flatBPTail ((r :: rs) ++ [p])) ++ [.rp]) =
              (.lp :: (flatBP q ++ flatBPTail (r :: rs)) ++ [.cm]) ++
                flatBP p ++ [.rp]
          rw [flatBPTail_append_singleton_p1]
          simp [List.append_assoc]

/-! ## 私的補助: 一意性の包装（Isabelle `ex1_Dpt_addBT`, layerB 18750） -/

private theorem addBT_right_cancel_p1 {a b c : BT}
    (h : addBT a c = addBT b c) : a = b := by
  rcases a with ⟨as⟩
  rcases b with ⟨bs⟩
  rcases c with ⟨cs⟩
  simp only [addBT, BT.trm.injEq] at h
  exact congrArg BT.trm (List.append_cancel_right h)

private theorem ex1_Dprin_addBT_p1 {X c : BT} (v : ℕ∞) (t₀ : BT)
    (h : X = Dprin v (addBT t₀ c)) :
    ∃! t : BT, X = Dprin v (addBT t c) := by
  refine ⟨t₀, h, ?_⟩
  intro t ht
  have heq : Dprin v (addBT t c) = Dprin v (addBT t₀ c) := ht.symm.trans h
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true,
    true_and] at heq
  exact addBT_right_cancel_p1 heq

/-! ## part (4-1) capstone（Isabelle `m_8_1_c1_around_part4_1`, 32085）

(4-1) ガード `j′₋₁ = j′₀ ∨ M_{1,j′₀}+1 = M_{1,j₀}` の下で、一意な `t′₂` が存在して
`Mark(Pred M, j′₋₁) = D_{M_{1,j′₋₁}}(t′₂ + c₁)`。

経路: back-slice 表示 `Mark (Pred M) j′₋₁ = Trans((M_j)_{j=j′₋₁}^{j₁-1})`
（`Mark_Trans_repr`＋`seg_Pred_eq`）、TransN_41 の depth-1 頭
`Trans((M_j)_{j=j′₋₁}^{j₀}) = D_{M_{1,j′₋₁}}(t₂ + D_{M_{1,j₀}}0)`、
segpos の共通 scb 位置で葉 `D_{M_{1,j₀}}0` を `c₁` に貼り替える（interior 枝）。
`j₀ = j₁ - 1` の boundary 枝では `c₁` 自身が右端値 `D_{M_{1,j₀}}0`。 -/

theorem c1_around_part4_1 (M : PS) (j₀' : ℕ) (hR : RTPS M)
    (hmono : monoT M = true)
    (hadm : adm M (transJ0 M) = true) (hj1 : 1 < transJ1 M)
    (hge : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M))
    (np : nextR M 0 j₀' (transJ0 M) = true)
    (hadj : j₀' + 1 < transJ0 M)
    (hguard : Adm M j₀' = j₀' ∨ entry M 1 j₀' + 1 = entry M 1 (transJ0 M)) :
    ∃! t₂' : BT, Mark (Pred M) (Adm M j₀')
      = Dprin (entry M 1 (Adm M j₀') : ℕ∞) (addBT t₂' (transC1 M)) := by
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨_hjm1, hc1, _haLe, hj0'lt, hj0j1, hj1L, haj0, hj0ub, hpredA, hpredJ0⟩ :=
    c1_around_part4_setup M j₀' hR hmono hadm hj1 hge np
  have htJ1 : transJ1 M = Lng M - 1 := rfl
  have htJ0 : transJ0 M = parent M 0 (Lng M - 1) := rfl
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hPredL : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hLP : Lng (Pred M) - 1 = transJ1 M - 1 := by omega
  -- back-slice 表示: `Mark (Pred M) j′₋₁ = Trans((M_j)_{j=j′₋₁}^{j₁-1})`
  have hlt : Adm M j₀' < Lng (Pred M) - 1 := by omega
  have hrepr : Mark (Pred M) (Adm M j₀') =
      Trans (seg (Pred M) (Adm M j₀') (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) (Adm M j₀') hpredA hpredR hlt
  have hsegeq : seg (Pred M) (Adm M j₀') (transJ1 M - 1) =
      seg M (Adm M j₀') (transJ1 M - 1) :=
    seg_Pred_eq M (Adm M j₀') (transJ1 M - 1) hlen (by omega) (by omega)
  have hreprM : Mark (Pred M) (Adm M j₀') =
      Trans (seg M (Adm M j₀') (transJ1 M - 1)) := by
    rw [hrepr, hLP, hsegeq]
  -- TransN_41: depth-1 頭と末尾葉 `D_{M_{1,j₀}} 0`
  obtain ⟨t₂, ht₂⟩ :=
    c1_around_part4_TransN_41 M j₀' hR hmono hadm hj1 np hadj hguard
  -- Nred: back-slice 祖先 `leR M 0 j′₋₁ j₀`
  obtain ⟨hleMaj0, _, _, _, _, _⟩ :=
    c1_around_part4_Nred M j₀' hR hmono hadm hj1 np
  -- `j₀` の最終列への行 0 祖先性
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnpar : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    rw [htJ0]
    exact hasParent_next_fseq M 0 (Lng M - 1) hp
  have hleJ0 : leR M 0 (transJ0 M) (Lng M - 1) = true :=
    nextR0_leR M _ _ hnpar
  -- 切片の貼り替え: `∃ t₀, Trans((M_j)_{j=j′₋₁}^{j₁-1}) = D_{M_{1,j′₋₁}}(t₀ + c₁)`
  have hslice : ∃ t₀ : BT, Trans (seg M (Adm M j₀') (transJ1 M - 1)) =
      Dprin (entry M 1 (Adm M j₀') : ℕ∞) (addBT t₀ (transC1 M)) := by
    by_cases hjlt : transJ0 M < transJ1 M - 1
    · -- interior 枝: `j₀ < j₁ - 1`
      have hlt0 : transJ0 M < Lng (Pred M) - 1 := by omega
      -- `c₁` の切片値（Isabelle part1 第 3 主張の私的再導出）
      have hreprJ0 : Mark (Pred M) (transJ0 M) =
          Trans (seg (Pred M) (transJ0 M) (Lng (Pred M) - 1)) :=
        Mark_Trans_repr (Pred M) (transJ0 M) hpredJ0 hpredR hlt0
      have hsegeqJ0 : seg (Pred M) (transJ0 M) (transJ1 M - 1) =
          seg M (transJ0 M) (transJ1 M - 1) :=
        seg_Pred_eq M (transJ0 M) (transJ1 M - 1) hlen (by omega) (by omega)
      have hc1part1 : Trans (seg M (transJ0 M) (transJ1 M - 1)) = transC1 M := by
        rw [hc1, hreprJ0, hLP, hsegeqJ0]
      -- `c₁` の単項性（Isabelle part1 第 5 主張の私的再導出）
      obtain ⟨tc, htc⟩ :=
        Mark_leftend_form_proper (Pred M) (transJ0 M) hpredJ0 hpredR hlt0
      have hc1P : transC1 M =
          Dprin (entry (Pred M) 1 (transJ0 M) : ℕ∞) tc := by
        rw [hc1, htc]
      -- 切片 Marked（Isabelle part2 第 3 主張の私的再導出）
      have hmarkedJ0M : Marked M (transJ0 M) := ⟨hM, hadm, hleJ0⟩
      have hSmMk : Marked (seg M (Adm M j₀') (transJ1 M - 1))
          (transJ0 M - Adm M j₀') :=
        marked_slice M (transJ0 M) (Adm M j₀') (transJ1 M - 1) hmarkedJ0M
          (by omega) (by omega) (by omega)
      -- 祖先連鎖
      have hlej0j1m1 : leR M 0 (transJ0 M) (transJ1 M - 1) = true :=
        ancestor_tree_1 M (transJ0 M) (transJ1 M - 1) (Lng M - 1) hM hleJ0
          (by omega) (by omega)
      have hleMaj1m1 : leR M 0 (Adm M j₀') (transJ1 M - 1) = true :=
        row0_transitive M _ _ _ hM hleMaj0 hlej0j1m1
      -- 共通 scb 位置
      obtain ⟨s, b, P1, P2⟩ := c1_around_part4_segpos M (Adm M j₀')
        (transJ0 M) (transJ1 M) (transC1 M) hR hmono haj0 hjlt hj1L hj1
        hleMaj0 hleMaj1m1 hSmMk hc1part1
      -- 末尾整列: 共通の `pre`/`post`
      obtain ⟨pre, post, hpost, hflat⟩ := addBT_principal_split_p1 t₂
      have halc : flatBT (addBT t₂ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) =
          pre ++ flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero) ++ post := by
        rw [Dprin_trm_p1, flatBT_singleton_p1]
        exact hflat _
      have halc' : flatBT (addBT t₂ (transC1 M)) =
          pre ++ flatBT (transC1 M) ++ post := by
        rw [hc1P, Dprin_trm_p1, flatBT_singleton_p1]
        exact hflat _
      -- 葉は principal 文字列
      have hiptc : isPTB_str
          (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) :=
        (principal_flat_properties
          (Dprin_mem_T_B (by simp)
            (by simp [T_B, BZero, dfree_BT, dfree_BPList]))
          ⟨_, rfl⟩).1
      -- 葉の位置の scb 分解を `D_{M_{1,j′₋₁}}` 越しに持ち上げ、一意性で `s`/`b` を同定
      have hdinner : scb_decomp
          (addBT t₂ (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) pre
          (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) post :=
        ⟨halc, fun _ => hiptc, hpost⟩
      have hdlift := scb_compose_dprin (entry M 1 (Adm M j₀') : ℕ∞) _
        pre _ post hdinner hiptc
      have hDleaf : scb_decomp (Trans (seg M (Adm M j₀') (transJ0 M)))
          (.dsym (entry M 1 (Adm M j₀') : ℕ∞) :: pre)
          (flatBT (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)) post := by
        rw [ht₂]
        exact hdlift
      obtain ⟨hs, hb⟩ :=
        scb_unique_decomp_unconditional _ _ _ _ _ _ P1 hDleaf
      -- 長い切片の flatten を `pre`/`post` で読み出して貼り替え
      have hflatlong : flatBT (Trans (seg M (Adm M j₀') (transJ1 M - 1))) =
          (.dsym (entry M 1 (Adm M j₀') : ℕ∞) :: pre) ++
            flatBT (transC1 M) ++ post := by
        have hP2 := P2.1
        rw [hs, hb] at hP2
        exact hP2
      refine ⟨t₂, ?_⟩
      apply flatBT_injective
      rw [hflatlong, flatBT_Dprin_p1, halc']
      simp
    · -- boundary 枝: `j₀ = j₁ - 1`、`c₁` は右端値 `D_{M_{1,j₀}} 0`
      have hjeq : transJ0 M = transJ1 M - 1 := by omega
      have hj0Pm1 : transJ0 M = Lng (Pred M) - 1 := by omega
      have hnzP : zeroT (Pred M) = false := by
        cases hzq : zeroT (Pred M) with
        | false => rfl
        | true =>
            exfalso
            simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at hzq
            omega
      have hmarkrm : Mark (Pred M) (Lng (Pred M) - 1) =
          Dprin (entry (Pred M) 1 (Lng (Pred M) - 1) : ℕ∞) BZero :=
        Mark_rightmost1_forward (Pred M) hpredR hnzP
      have he1P : entry (Pred M) 1 (transJ0 M) = entry M 1 (transJ0 M) := by
        rw [Pred_eq_take M hlen]
        exact entry_take M (Lng M - 1) 1 (transJ0 M) (by omega)
      have hc1leaf : transC1 M =
          Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero := by
        rw [hc1, hj0Pm1, hmarkrm, ← hj0Pm1, he1P]
      refine ⟨t₂, ?_⟩
      have hsegB : seg M (Adm M j₀') (transJ1 M - 1) =
          seg M (Adm M j₀') (transJ0 M) := by
        rw [hjeq]
      rw [hsegB, ht₂, hc1leaf]
  -- 組み立て: 表示＋貼り替え → 一意存在
  obtain ⟨t₀, ht₀⟩ := hslice
  have hMark : Mark (Pred M) (Adm M j₀') =
      Dprin (entry M 1 (Adm M j₀') : ℕ∞) (addBT t₀ (transC1 M)) := by
    rw [hreprM, ht₀]
  exact ex1_Dprin_addBT_p1 _ t₀ hMark

#print axioms c1_around_part4_1

end PSS
