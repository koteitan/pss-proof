import «8».«8.1-condI-masterCF»
import «8».«8.1-condI-III-c1-around»

/-!
# §8.1 条件(I)・`j₀ > 0` の marking-nesting 閉形式 — `CondI_masterCF` の討伐（chunk 5）

- 原文: `tmp/content.md` 3160–3260（§8.1 条件(I) 交換関係の証明本体、`j₀ > 0` regime）。
  本ファイルは**新しい記事命題を主張しない**。ビルド済み `«8».«8.1-Trans-fseq-condI»`
  が露出した唯一の `Prop` `CondI_masterCF`（同 :417）を討伐する組み立てファイル。
- Isabelle: `scx_condI_j0pos_masterCF`（`isabelle/layerB/pss_wip.thy` :83639–84092、
  r28-STEPCORE ブロックの最終 chunk 5 = 組み立て）。
  * setup / host = `scx_host_basic` (:82322)
  * `c1 = D_{v0} t2`、`t2 ∈ T_B` = §8.5 `c1_shape` を Lean では `transC1_single_principal`
    + `principal_reconstruct`（7.3-c1-c2-order）で再構成（`Mark_leftend_form` 迂回）
  * host scb 対 = `s84c2_Trans_c2_decomp`（Lean 私的複製 `Trans_c1_c2_decomp_cm5`）
  * case A/B の初期形 = `m_8_1_c1_around_part3_1`/`_3_2`/`_part4_1`/`_part4_2`
    （Lean `c1_around_3`/`c1_around_3_2`/`c1_around_part4_1`/`c1_around_part4_2`）
  * INV 帰納 = `scx_stepA`/`scx_stepB`（Lean 移植済、`«8».«8.1-condI-masterCF»` が公開）
  * `dM`（`c₁ ↦ c₂` の置換）= `add_scb_marked`/`add_scb_replace_last`/`scb_compose_dprin`
    /`scb_unique_decomp_unconditional`（7.2 系）
- 訂正: 本ブロックに掛かる訂正は無い（A20 は `c1_around_1` が内部で処理済）。
- 依存（ビルド済みのみ import）: `«8».«8.1-condI-masterCF»`（`scx_host_basic`/`scx_stepA`/
  `scx_stepB`、および CondI_masterCF の定義を推移的に露出）、`«8».«8.1-condI-III-c1-around»`
  （`c1_around_1`/`_2`/`_3`/`_3_2`、推移的に `c1_around_part4_1`/`_part4_2`）。
  推移的に 7.2-add-scb/7.2-scb-compose/7.2-scb-unique/7.3-Trans-welldefined/
  7.3-c1-c2-order/5.3-pred-is-oper1/6.5-6.6/6.8。
- 状態: 🤖 GREEN。`CondI_masterCF` を無仮定で討伐（`scx_condI_j0pos_masterCF`）。
- 私的補助（Isabelle 対応、suffix `_cm5`）: `addBT_zero_left_cm5`/`BZero_mem_T_B_cm5`/
  `multBT_mem_T_B_cm5`/`T_B_Dprin_body_cm5`/`T_B_addBT_split_cm5`/`scb_compose_str_cm5`/
  `scb_peel_cm5`/`host_transport_cm5`/`principal_flat_isPTB_cm5`/`Trans_c1_c2_decomp_cm5`。
-/

namespace PSS

/-! ## 私的補助（Isabelle `scx_*` 基盤の複製、suffix `_cm5`） -/

/-- Isabelle `scx_addBT_0left`。 -/
private theorem addBT_zero_left_cm5 (t : BT) : addBT BZero t = t := by
  cases t; simp [addBT, BZero]

/-- Isabelle `scx_TB_zero`。 -/
private theorem BZero_mem_T_B_cm5 : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

/-- Isabelle `scx_TB_multBT`。 -/
private theorem multBT_mem_T_B_cm5 {a : BT} (ha : a ∈ T_B) (n : ℕ) :
    multBT a n ∈ T_B := by
  induction n with
  | zero => simpa [multBT] using BZero_mem_T_B_cm5
  | succ k ih => exact addBT_mem_T_B ih ha

/-- Isabelle `scx_TB_Dpt_body`。 -/
private theorem T_B_Dprin_body_cm5 {v : ℕ∞} {t : BT} (h : Dprin v t ∈ T_B) :
    t ∈ T_B := by
  simp only [T_B, Set.mem_setOf_eq, Dprin, dfree_BT, dfree_BPList, dfree_BP,
    Bool.and_eq_true, bne_iff_ne, ne_eq, and_true] at h ⊢
  exact h.2

/-- Isabelle `scx_TB_addBT_left` / `scx_TB_addBT_right`。 -/
private theorem T_B_addBT_split_cm5 {a b : BT} (h : addBT a b ∈ T_B) :
    a ∈ T_B ∧ b ∈ T_B := by
  cases a with
  | trm as =>
    cases b with
    | trm bs =>
      simp only [T_B, Set.mem_setOf_eq, addBT, dfree_BT] at h ⊢
      induction as with
      | nil => simpa [dfree_BPList] using h
      | cons p ps ih =>
          simp only [List.cons_append, dfree_BPList, Bool.and_eq_true] at h ⊢
          exact ⟨⟨h.1, (ih h.2).1⟩, (ih h.2).2⟩

/-- Isabelle `scx_scb_compose`（scb 分解の合成則）。 -/
private theorem scb_compose_str_cm5 {T X : BT} {s₁ s₂ c b₁ b₂ : List Sym}
    (d1 : scb_decomp T s₁ (flatBT X) b₁)
    (d2 : scb_decomp X s₂ c b₂)
    (hXne : X ≠ BZero) :
    scb_decomp T (s₁ ++ s₂) c (b₂ ++ b₁) := by
  obtain ⟨fT, _, rb1⟩ := d1
  obtain ⟨fX, pc, rb2⟩ := d2
  refine ⟨?_, ?_, ?_⟩
  · rw [fT, fX]; simp [List.append_assoc]
  · intro _; exact pc hXne
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact rb2 x h
    · exact rb1 x h

/-- 合成の逆（peel）: 外側の文脈 `S`/`B` が `flatBT X` を包むことを取り出す。 -/
private theorem scb_peel_cm5 {T X : BT} {S sIn C bIn B : List Sym}
    (d1 : scb_decomp T (S ++ sIn) C (bIn ++ B))
    (d2 : scb_decomp X sIn C bIn)
    (hX : isPTB_str (flatBT X)) :
    scb_decomp T S (flatBT X) B := by
  obtain ⟨fT, _, rbT⟩ := d1
  obtain ⟨fX, _, _⟩ := d2
  refine ⟨?_, fun _ => hX, ?_⟩
  · rw [fT, fX]; simp only [List.append_assoc]
  · intro x hx
    exact rbT x (List.mem_append.mpr (Or.inr hx))

/-- host scb 対を使った `c₁ ↦ c₂` の文脈遺伝。 -/
private theorem host_transport_cm5 {M : PS} {s1 b1 S B : List Sym}
    (dPM : scb_decomp (Trans (Pred M)) s1 (flatBT (transC1 M)) b1)
    (dWM : scb_decomp (Trans M) s1 (flatBT (transC2 M)) b1)
    (dC : scb_decomp (Trans (Pred M)) S (flatBT (transC1 M)) B) :
    scb_decomp (Trans M) S (flatBT (transC2 M)) B := by
  obtain ⟨hs, hb⟩ := scb_unique_decomp_unconditional (Trans (Pred M)) s1 S
    (flatBT (transC1 M)) b1 B dPM dC
  rw [hs, hb] at dWM
  exact dWM

/-- Isabelle `addscb_princ_isPTB` / `isPTB_str_Dpt`。 -/
private theorem principal_flat_isPTB_cm5 {c : BT} (hc : c ∈ T_B)
    (hcP : ∃ p, c = .trm [p]) : isPTB_str (flatBT c) := by
  obtain ⟨p, rfl⟩ := hcP
  refine ⟨p, ?_, by simp [flatBT]⟩
  simpa [T_B, dfree_BT, dfree_BPList] using hc

/-- Isabelle `s84c2_Trans_c2_decomp`。`Trans (Pred M)` 内の `c₁` の scb 文脈は
`Trans M` では `c₂` の scb 文脈になる。 -/
private theorem Trans_c1_c2_decomp_cm5 (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M) (ht₁ : Trans (Pred M) ≠ BZero) :
    ∃ s b : List Sym,
      scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (transC2 M)) b := by
  have hM : TPS M := RTPS_TPS M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hmarked : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
    Marked_Pred_Adm M hM hlen hp
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have ht₁TB : Trans (Pred M) ∈ T_B := Trans_mem_T_B (Pred M) hpredR
  have hc₁TB : transC1 M ∈ T_B := by
    simpa [transC1, transJm1, transJ0, lastParent] using
      Mark_mem_T_B (Pred M) _ hpredR hmarked
  have ht₁c₁ : (Trans (Pred M), transC1 M) ∈ MarkedB := by
    simpa [transC1, transJm1, transJ0, lastParent] using
      Trans_Mark_mem_MarkedB (Pred M) _ hpredR hmarked
  have hc₁P : ∃ p, transC1 M = .trm [p] :=
    marked_component_principal ht₁ ht₁c₁
  have hc₂facts := transC2Core_properties M (transC1 M) hc₁TB hc₁P
  have hc₂TB : transC2 M ∈ T_B := by
    simpa [transC2, transV, transT2] using hc₂facts.1
  have hc₂P : ∃ p, transC2 M = .trm [p] := by
    simpa [transC2, transV, transT2] using hc₂facts.2
  have hTrans : Trans M = replaceScb (Trans (Pred M)) (transC1 M) (transC2 M) := by
    simpa [ht₁, transC1, transC2, transV, transT2, transJm1, transJ0,
      lastParent] using (Trans_Mark_mono_equations M hR hlen hmono).1
  obtain ⟨s, b, hd, _hout, hd2⟩ :=
    replaceScb_spec ht₁TB hc₁TB hc₁P hc₂TB hc₂P ht₁c₁
  exact ⟨s, b, hd, by rw [hTrans]; exact hd2⟩

/-! ## 組み立て — Isabelle `scx_condI_j0pos_masterCF` (pss_wip.thy:83639) -/

theorem scx_condI_j0pos_masterCF : CondI_masterCF := by
  intro M hR hmono hj1 hI hj0pos
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  obtain ⟨hp0, e1z, hadmHB, _hle0j0, _hpj0, hnp, hgeHB, hj0'lt⟩ :=
    scx_host_basic M hR hmono hj1 hI hj0pos
  -- transJ 形の仮定（`c1_around_*`/`scx_step*` 用）
  have hj1J : 1 < transJ1 M := hj1
  have hj1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  have hadmJ0 : adm M (transJ0 M) = true := hadmHB
  have hgeJ : entry M 1 (transJ1 M) ≤ entry M 1 (transJ0 M) := hgeHB
  have hnpJ : nextR M 0 (parent M 0 (parent M 0 (Lng M - 1))) (transJ0 M) = true :=
    hnp
  have hc1eq : transC1 M = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))) := rfl
  -- `c₁` の形: `c₁ = D_{v0} t2`、`t2 ∈ T_B`
  have part1 := c1_around_1 M hR hmono hadmJ0 hj1J hgeJ
  have T1ne : Trans (Pred M) ≠ BZero := part1.1
  have c1TB : transC1 M ∈ T_B := part1.2.2.2.1
  have c1p : ∃ p, transC1 M = .trm [p] := part1.2.2.2.2
  have hc1len := transC1_single_principal M hR hmono hj1pos T1ne
  have hc1eqTV : transC1 M = Dprin (transV M) (transT2 M) := by
    simpa [transV, transT2] using principal_reconstruct hc1len
  have hsplit : transV M ≠ ⊤ ∧ transT2 M ∈ T_B := by
    have h := c1TB
    rw [hc1eqTV] at h
    change dfree_BT (.trm [.db (transV M) (transT2 M)]) = true at h
    simp only [dfree_BT, dfree_BPList, dfree_BP, Bool.and_eq_true, bne_iff_ne] at h
    exact ⟨h.1.1, h.1.2⟩
  obtain ⟨v0, hv0⟩ := ENat.ne_top_iff_exists.mp hsplit.1
  have ht2TB : transT2 M ∈ T_B := hsplit.2
  have c1E : transC1 M = Dprin (v0 : ℕ∞) (transT2 M) := by rw [hc1eqTV, ← hv0]
  -- `c₂` の形（条件(I)）
  have hcls : (transCondI M || transCondIII M || transCondV M) = true := by simp [hI]
  have hE : (entry M 1 (lastIdx M) : ℕ∞) = 0 := by
    rw [show entry M 1 (lastIdx M) = 0 from e1z]; simp
  have c2ME : transC2 M = Dprin (v0 : ℕ∞) (addBT (transT2 M) (Dprin 0 BZero)) := by
    rw [transC2, transC2Core]
    simp only [hcls, if_true]
    rw [← hv0, hE]
  have hc2TB : transC2 M ∈ T_B := by
    rw [c2ME]
    exact Dprin_mem_T_B (by simp) (addBT_mem_T_B ht2TB
      (Dprin_mem_T_B (by simp) BZero_mem_T_B_cm5))
  have hc2p : ∃ p, transC2 M = .trm [p] := ⟨_, by rw [c2ME]; rfl⟩
  have iptc1 : isPTB_str (flatBT (transC1 M)) := principal_flat_isPTB_cm5 c1TB c1p
  have iptc2 : isPTB_str (flatBT (transC2 M)) := principal_flat_isPTB_cm5 hc2TB hc2p
  -- host scb 対
  obtain ⟨s1, b1, dPM, dWM⟩ := Trans_c1_c2_decomp_cm5 M hR hmono hlen T1ne
  -- 基点 `(Pred M, j₋₁')`
  have mkP : Marked (Pred M) (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) :=
    (c1_around_2 M (parent M 0 (parent M 0 (Lng M - 1))) hR hmono hadmJ0 hj1J
      hgeJ hnpJ).2.1
  obtain ⟨s', b', dInit⟩ :=
    Trans_Mark_mem_MarkedB (Pred M)
      (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) hpredR mkP
  -- 反復の下準備
  have hoper1 : oper M 1 = Pred M := (pred_is_oper1 M hM hlen).symm
  have hmult1 : multBT (transC1 M) 1 = transC1 M := by
    have h : multBT (transC1 M) 1 = addBT BZero (transC1 M) := rfl
    rw [h, addBT_zero_left_cm5]
  by_cases hcase :
      Adm M (parent M 0 (parent M 0 (Lng M - 1)))
          = parent M 0 (parent M 0 (Lng M - 1))
        ∨ entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) + 1
          = entry M 1 (parent M 0 (Lng M - 1))
  · -- ## case A
    obtain ⟨tau, tauT, mpjE⟩ : ∃ tau : BT, tau ∈ T_B ∧
        Mark (Pred M) (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
          = Dprin (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
              (addBT tau (transC1 M)) := by
      rcases Nat.lt_or_ge (parent M 0 (parent M 0 (Lng M - 1)) + 1)
        (parent M 0 (Lng M - 1)) with hlt | hge2
      · -- 非隣接: part4_1
        obtain ⟨tau, htau⟩ :=
          (c1_around_part4_1 M (parent M 0 (parent M 0 (Lng M - 1))) hR hmono
            hadmJ0 hj1J hgeJ hnpJ hlt hcase).exists
        have hmarkTB : Mark (Pred M)
            (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) ∈ T_B :=
          Mark_mem_T_B (Pred M) _ hpredR mkP
        rw [htau] at hmarkTB
        have hbodyTB := T_B_Dprin_body_cm5 hmarkTB
        exact ⟨tau, (T_B_addBT_split_cm5 hbodyTB).1, htau⟩
      · -- 隣接: part3_1
        have hadj : parent M 0 (parent M 0 (Lng M - 1)) + 1
            = parent M 0 (Lng M - 1) := by omega
        have h31 := (c1_around_3 M (parent M 0 (parent M 0 (Lng M - 1))) hR hmono
          hadmJ0 hj1J hgeJ hnpJ hadj).1 hcase
        exact ⟨BZero, BZero_mem_T_B_cm5, by rw [h31, addBT_zero_left_cm5]⟩
    -- 不変量
    have INV : ∀ n, 1 ≤ n →
        Mark (oper M n) (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
            = Dprin (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
                (addBT tau (multBT (transC1 M) n)) ∧
          scb_decomp (Trans (oper M n)) s'
            (flatBT (Dprin
              (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
              (addBT tau (multBT (transC1 M) n)))) b' := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
          refine ⟨?_, ?_⟩
          · rw [hoper1, hmult1]; exact mpjE
          · rw [hoper1, hmult1, ← mpjE]; exact dInit
      | succ n _ ih =>
          exact scx_stepA M (n + 1)
            (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))))
            tau (transC1 M) s' b' hR hmono hj1 hI hj0pos (by omega) hc1eq hcase rfl
            tauT dInit ih.1 ih.2
    -- `dM`: `c₁ ↦ c₂` の置換
    obtain ⟨sc, bc, iR0⟩ := add_scb_marked tau (transC1 M) tauT c1TB c1p
    have iR := scb_compose_dprin
      (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
      (addBT tau (transC1 M)) sc (flatBT (transC1 M)) bc iR0 iptc1
    have dInit' : scb_decomp (Trans (Pred M)) s'
        (flatBT (Dprin
          (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
          (addBT tau (transC1 M)))) b' := by rw [← mpjE]; exact dInit
    have dC := scb_compose_str_cm5 dInit' iR (by simp [Dprin, BZero])
    have dWM' := host_transport_cm5 dPM dWM dC
    have iR2_0 := add_scb_replace_last tau (transC1 M) (transC2 M) sc bc tauT c1TB
      c1p hc2TB hc2p iR0
    have iR2 := scb_compose_dprin
      (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
      (addBT tau (transC2 M)) sc (flatBT (transC2 M)) bc iR2_0 iptc2
    have iptOut : isPTB_str (flatBT (Dprin
        (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
        (addBT tau (transC2 M)))) :=
      principal_flat_isPTB_cm5 (Dprin_mem_T_B (by simp) (addBT_mem_T_B tauT hc2TB))
        ⟨_, rfl⟩
    have dMA := scb_peel_cm5 dWM' iR2 iptOut
    -- 組み立て
    refine ⟨s', b', entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))), v0,
      tau, transT2 M, tauT, ht2TB, ?_, ?_⟩
    · rw [← c2ME]; exact dMA
    · intro k hk
      obtain ⟨_, hd⟩ := INV (k + 1) (by omega)
      have hflat := hd.1
      rw [c1E] at hflat
      rw [← unflatBT_flat (Trans (oper M (k + 1))), hflat]
  · -- ## case B
    rw [not_or] at hcase
    obtain ⟨hne, hnv⟩ := hcase
    have blt : Adm M (parent M 0 (parent M 0 (Lng M - 1)))
        < parent M 0 (parent M 0 (Lng M - 1)) := by
      have := Adm_le M (parent M 0 (parent M 0 (Lng M - 1))); omega
    have bge : entry M 1 (parent M 0 (Lng M - 1))
        ≤ entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) := by
      have := scx_row1_bound M (parent M 0 (parent M 0 (Lng M - 1)))
        (parent M 0 (Lng M - 1)) hR hnp
      omega
    obtain ⟨t3, t4, t3T, t4T, mpjE⟩ : ∃ t3 t4 : BT, t3 ∈ T_B ∧ t4 ∈ T_B ∧
        Mark (Pred M) (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
          = Dprin (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
              (addBT t3 (Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
                (addBT t4 (transC1 M)))) := by
      rcases Nat.lt_or_ge (parent M 0 (parent M 0 (Lng M - 1)) + 1)
        (parent M 0 (Lng M - 1)) with hlt | hge2
      · -- 非隣接: part4_2
        obtain ⟨t34, htp⟩ :=
          (c1_around_part4_2 M (parent M 0 (parent M 0 (Lng M - 1))) hR hmono
            hadmJ0 hj1J hgeJ hnpJ hlt ⟨blt, bge⟩).exists
        have hmarkTB : Mark (Pred M)
            (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) ∈ T_B :=
          Mark_mem_T_B (Pred M) _ hpredR mkP
        rw [htp] at hmarkTB
        have hb1 := T_B_Dprin_body_cm5 hmarkTB
        have ht3T := (T_B_addBT_split_cm5 hb1).1
        have hmid := (T_B_addBT_split_cm5 hb1).2
        have hb2 := T_B_Dprin_body_cm5 hmid
        have ht4T := (T_B_addBT_split_cm5 hb2).1
        exact ⟨t34.1, t34.2, ht3T, ht4T, htp⟩
      · -- 隣接: part3_2（前件が空虚に偽、`c1_around_3_2` 経由で t3=t4=0）
        have hadj : parent M 0 (parent M 0 (Lng M - 1)) + 1
            = parent M 0 (Lng M - 1) := by omega
        have m32 := c1_around_3_2 M (parent M 0 (parent M 0 (Lng M - 1))) hR hnpJ
          hadj ⟨blt, bge⟩
        exact ⟨BZero, BZero, BZero_mem_T_B_cm5, BZero_mem_T_B_cm5, by
          rw [addBT_zero_left_cm5, addBT_zero_left_cm5]; exact m32⟩
    -- 不変量
    have INV : ∀ n, 1 ≤ n →
        Mark (oper M n) (Adm M (parent M 0 (parent M 0 (Lng M - 1))))
            = Dprin (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
                (addBT t3 (Dprin
                  (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
                  (addBT t4 (multBT (transC1 M) n)))) ∧
          scb_decomp (Trans (oper M n)) s'
            (flatBT (Dprin
              (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
              (addBT t3 (Dprin
                (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
                (addBT t4 (multBT (transC1 M) n)))))) b' := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
          refine ⟨?_, ?_⟩
          · rw [hoper1, hmult1]; exact mpjE
          · rw [hoper1, hmult1, ← mpjE]; exact dInit
      | succ n _ ih =>
          exact scx_stepB M (n + 1)
            (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))))
            (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))))
            t3 t4 (transC1 M) s' b' hR hmono hj1 hI hj0pos (by omega) hc1eq blt bge
            rfl rfl t3T t4T dInit ih.1 ih.2
    -- `dM`: 2 段の `c₁ ↦ c₂`
    obtain ⟨si, bi, iI0⟩ := add_scb_marked t4 (transC1 M) t4T c1TB c1p
    have iI := scb_compose_dprin
      (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
      (addBT t4 (transC1 M)) si (flatBT (transC1 M)) bi iI0 iptc1
    have hmid0TB : Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
        (addBT t4 (transC1 M)) ∈ T_B :=
      Dprin_mem_T_B (by simp) (addBT_mem_T_B t4T c1TB)
    have hmid0p : ∃ p, Dprin
        (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
        (addBT t4 (transC1 M)) = .trm [p] := ⟨_, rfl⟩
    obtain ⟨so, bo, iO0⟩ := add_scb_marked t3
      (Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
        (addBT t4 (transC1 M))) t3T hmid0TB hmid0p
    have iOc := scb_compose_str_cm5 iO0 iI (by simp [Dprin, BZero])
    have iOcl := scb_compose_dprin
      (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
      (addBT t3 (Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
        (addBT t4 (transC1 M))))
      (so ++ (.dsym (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞) :: si))
      (flatBT (transC1 M)) (bi ++ bo) iOc iptc1
    have dInit' : scb_decomp (Trans (Pred M)) s'
        (flatBT (Dprin
          (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
          (addBT t3 (Dprin
            (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
            (addBT t4 (transC1 M)))))) b' := by rw [← mpjE]; exact dInit
    have dC := scb_compose_str_cm5 dInit' iOcl (by simp [Dprin, BZero])
    have dWM' := host_transport_cm5 dPM dWM dC
    -- 内側の `c₁ ↦ c₂`
    have iI2_0 := add_scb_replace_last t4 (transC1 M) (transC2 M) si bi t4T c1TB
      c1p hc2TB hc2p iI0
    have iI2 := scb_compose_dprin
      (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
      (addBT t4 (transC2 M)) si (flatBT (transC2 M)) bi iI2_0 iptc2
    have hmidMTB : Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
        (addBT t4 (transC2 M)) ∈ T_B :=
      Dprin_mem_T_B (by simp) (addBT_mem_T_B t4T hc2TB)
    have hmidMp : ∃ p, Dprin
        (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
        (addBT t4 (transC2 M)) = .trm [p] := ⟨_, rfl⟩
    have iptmidM : isPTB_str (flatBT (Dprin
        (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
        (addBT t4 (transC2 M)))) :=
      principal_flat_isPTB_cm5 hmidMTB hmidMp
    have dWM'' : scb_decomp (Trans M)
        ((s' ++ (.dsym (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
            :: so))
          ++ (.dsym (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞) :: si))
        (flatBT (transC2 M)) (bi ++ (bo ++ b')) := by
      have e1 : (s' ++ (.dsym
            (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞) :: so))
            ++ (.dsym (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞) :: si)
          = s' ++ (.dsym
            (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
            :: (so ++ (.dsym (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
              :: si))) := by simp [List.append_assoc]
      have e2 : bi ++ (bo ++ b') = (bi ++ bo) ++ b' := by rw [List.append_assoc]
      rw [e1, e2]; exact dWM'
    have dMB := scb_peel_cm5 dWM'' iI2 iptmidM
    -- 組み立て
    refine ⟨s' ++ (.dsym
        (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞) :: so),
      bo ++ b', entry M 1 (parent M 0 (parent M 0 (Lng M - 1))), v0, t4,
      transT2 M, t4T, ht2TB, ?_, ?_⟩
    · rw [← c2ME]; exact dMB
    · intro k hk
      obtain ⟨_, hd⟩ := INV (k + 1) (by omega)
      have midkTB : Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
          (addBT t4 (multBT (transC1 M) (k + 1))) ∈ T_B :=
        Dprin_mem_T_B (by simp) (addBT_mem_T_B t4T (multBT_mem_T_B_cm5 c1TB _))
      have midkp : ∃ p, Dprin
          (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
          (addBT t4 (multBT (transC1 M) (k + 1))) = .trm [p] := ⟨_, rfl⟩
      have iptmidk : isPTB_str (flatBT (Dprin
          (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
          (addBT t4 (multBT (transC1 M) (k + 1))))) :=
        principal_flat_isPTB_cm5 midkTB midkp
      have iOk0 := add_scb_replace_last t3
        (Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
          (addBT t4 (transC1 M)))
        (Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
          (addBT t4 (multBT (transC1 M) (k + 1))))
        so bo t3T hmid0TB hmid0p midkTB midkp iO0
      have iOk := scb_compose_dprin
        (entry M 1 (Adm M (parent M 0 (parent M 0 (Lng M - 1)))) : ℕ∞)
        (addBT t3 (Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
          (addBT t4 (multBT (transC1 M) (k + 1)))))
        so
        (flatBT (Dprin (entry M 1 (parent M 0 (parent M 0 (Lng M - 1))) : ℕ∞)
          (addBT t4 (multBT (transC1 M) (k + 1)))))
        bo iOk0 iptmidk
      have dk := scb_compose_str_cm5 hd iOk (by simp [Dprin, BZero])
      have hflat := dk.1
      rw [c1E] at hflat
      rw [← unflatBT_flat (Trans (oper M (k + 1))), hflat]

#print axioms scx_condI_j0pos_masterCF

end PSS
