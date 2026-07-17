import «8».«8.6-condVI-close»
import «8».«8.6-condVI-props»
import «8».«8.6-condVI-Ltower-facta»
import «8».«8.6-Trans-Red-funpow-IncrFirst»
import «8».«8.5-exchV-props»

/-!
# §8.6 条件 (VI) 非許容 `j₀` の残差 `CondVI_scbdec_nadm_forms_v6` へ向けた公開ブリック

原文: 停止性定理 §8.6 条件 (VI) の `Trans`/基本列交換則（`tmp/content.md` 5484）の
**非許容 `j₀`** 枝。目標の残差 `CondVI_scbdec_nadm_forms_v6`
（`8.6-condVI-close`:317）は `condVI_scbdec_nadm_forms_holds_v6p`
（`8.6-condVI-props`:459）により **`CondVIres_nadm_Ltower_v6p`（L 塔閉形式）1 本**に
削減済み。本ファイルはその L 塔へ向けた公開ブリックを積む。

Isabelle 対応（`isabelle/layerB/pss_wip.thy`）:
- `c6nx_condVI_uv`（:76352, 44L）… fact (d) `M_{1,j₋₁} < M_{1,j₁}`。**本ファイルで完全証明**。
  下流 `condVI_scbdec_nadm_forms_holds_v6p` は `U < u+1` を `condVI_U_le_u_v6p`
  （`≤`）から出しているが、Isabelle の名前付き事実は狭義 `< M_{1,j₁}` なので公開する。
- fact (b) `s84c1_Mark_L_mstar`（:53883）の条件 (VI) 崩壊形
  `Mark (oper M (n+1)) (Lng (oper M n) - 1) = D_u(D_u 0)`。**本ファイルで完全証明**
  （`c6nx_Mark_L_mstar_condVI`）。崩壊の要点: 条件 (VI)＋簡約性で `d₀ = 1`
  （`RedCondA`）なので基点尾切片が `const2ndSeq` そのもの＝`IncrFirst` 反復不要、
  `const2nd_Trans`（`8.6-const2nd-Trans`）で `D_u(D_u 0)` に落ちる。

依存（すべて公開・移植済）:
- `s84c1_marked_L`（`8.6-condVI-Ltower-facta`:256, fact (a)）、
- `Mark_Trans_repr`（`7.4-Mark-Trans-repr`:984）、`const2nd_Trans`（`8.6-const2nd-Trans`:625）、
- `RTPS_oper`（`6.6-reduced-fseq`:4179）、`STPS_RTPS`（`6.7-standard-reduced`:59）、
- タイル読み出し `entry_oper_tiling_block_zero`/`_one`・`length_oper_tiling`（§6.6）、
- `RTPS_condAB`/`RedCondA_apply`（§6.6/§6.5、`d₀ = 1`）、
- `Adm_max`/`Adm_le`（§6.3、fact (d) の行 1 単調性）。

残差（本ファイルで**閉じていない**、`needs` で親へ地図化）:
- fact (c) `transC1 M = D_v(D_u 0)`（`c6nx_t2eq`:76619）… de-adm 橋が
  `m_7_3_Mark_rightmost2`（**Lean 未移植**）を要する。
- 組み立て `CondVIres_nadm_Ltower_v6p`（L 塔帰納）… `m_8_4_oper_props_5`
  （scb 分解一意性クラスタ、**Lean 未移植**）＋ `c6zx_L_tower` ＋ `c6zx_condVI_baseL_gen`。

状態: 🟡 部分（fact (b)/(d) 公開、fact (c)＋組み立ては残差）。private 補助は `_nf` 接尾辞。
-/

namespace PSS

/-! ## 条件 (VI) の指標事実（Isabelle `c6gx_condVI_j0`, pss_wip.thy:69818） -/

private theorem condVI_j0_nf {M : PS} (hcond : transCondVI M = true) :
    transJ0 M + 1 = Lng M - 1 ∧
      entry M 1 (transJ0 M) + 1 = entry M 1 (Lng M - 1) ∧
      0 < entry M 1 (Lng M - 1) := by
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    lastIdx, lastParent] at hcond
  exact ⟨hcond.2, hcond.1.2, hcond.1.1⟩

/-! ## fact (d): 行 1 の許容化単調性（Isabelle `viB_suffix_max` の破片）

`8.5-exchV-props`:270 の `entry1_step_xv` / `entry1_Adm_le_xv` は `private` なので、
同じ証明を本ファイルに複製する（suffix `_nf`）。 -/

private theorem entry1_step_nf (M : PS) (j₀ j : ℕ) (hna : adm M j₀ = false)
    (hj₀ : j₀ < Lng M) (hge : Adm M j₀ ≤ j) (hlt : j < j₀) :
    entry M 1 j < entry M 1 (j + 1) := by
  have hnaS : adm M (j + 1) = false := by
    by_contra hcon
    have hadm : adm M (j + 1) = true := by simpa using hcon
    rcases Nat.lt_or_ge (j + 1) j₀ with h | h
    · have := Adm_max M (j + 1) j₀ hadm (by omega)
      omega
    · have hEq : j + 1 = j₀ := by omega
      rw [hEq] at hadm
      rw [hadm] at hna
      exact absurd hna (by simp)
  have hnadm : nadm M (j + 1) = true := by
    simpa [adm] using hnaS
  simp only [nadm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hnadm
  have hlen : ¬ (Lng M < j + 1) := by omega
  rcases hnadm with h | h
  · exact absurd h hlen
  · have hn1 : nextrel1 M j (j + 1) = true := by
      simpa [nextR] using h.1
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at hn1
    exact hn1.1.1.2

private theorem entry1_Adm_le_nf (M : PS) (j₀ : ℕ) (hj₀ : j₀ < Lng M) :
    entry M 1 (Adm M j₀) ≤ entry M 1 j₀ := by
  by_cases hadm : adm M j₀ = true
  · simp [Adm, hadm]
  · have hna : adm M j₀ = false := by simpa using hadm
    have hmono : ∀ d a, d = j₀ - a → Adm M j₀ ≤ a → a ≤ j₀ →
        entry M 1 a ≤ entry M 1 j₀ := by
      intro d
      induction d with
      | zero => intro a hd _ hle; have : a = j₀ := by omega
                rw [this]
      | succ d ih =>
          intro a hd hge hle
          have hlt : a < j₀ := by omega
          have hstep := entry1_step_nf M j₀ a hna hj₀ hge hlt
          have hnext : entry M 1 (a + 1) ≤ entry M 1 j₀ :=
            ih (a + 1) (by omega) (by omega) (by omega)
          omega
    exact hmono (j₀ - Adm M j₀) (Adm M j₀) rfl (le_refl _) (Adm_le M j₀)

/-- **fact (d)**（Isabelle `c6nx_condVI_uv`, pss_wip.thy:76352）。
非許容枝の外側の頭 `U = M_{1,j₋₁}` は最終列の行 1 値 `M_{1,j₁}` より**狭義に**小さい。
`M_{1,j₋₁} ≤ M_{1,j₀}`（許容化単調性）＋ 条件 (VI) の隣接 `M_{1,j₀}+1 = M_{1,j₁}`。 -/
theorem c6nx_condVI_uv (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 0 < transJ1 M) (hcond : transCondVI M = true) :
    entry M 1 (transJm1 M) < entry M 1 (transJ1 M) := by
  obtain ⟨hj0eq, hsucc, _hpos⟩ := condVI_j0_nf hcond
  have hL : 1 < Lng M := by
    simp only [transJ1, lastIdx] at hj₁; omega
  have hj0lt : transJ0 M < Lng M := by omega
  have hle : entry M 1 (transJm1 M) ≤ entry M 1 (transJ0 M) := by
    simpa [transJm1] using entry1_Adm_le_nf M (transJ0 M) hj0lt
  have hj1eq : transJ1 M = Lng M - 1 := rfl
  rw [hj1eq]
  omega

#print axioms c6nx_condVI_uv

/-! ## fact (b) 用の崩壊構造（`8.6-condVI-Ltower-facta` の private 補助を複製、`_nf`） -/

private theorem condVI_idx_nf {M : PS} (hcond : transCondVI M = true) :
    parent M 0 (Lng M - 1) = Lng M - 2 ∧
    entry M 1 (Lng M - 2) + 1 = entry M 1 (Lng M - 1) ∧
    0 < entry M 1 (Lng M - 1) := by
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    lastIdx, lastParent] at hcond
  obtain ⟨⟨hpos, heq⟩, hadj⟩ := hcond
  have hp0 : parent M 0 (Lng M - 1) = Lng M - 2 := by omega
  refine ⟨hp0, ?_, hpos⟩
  rw [hp0] at heq; exact heq

private theorem nextR_of_parent_pos_nf (M : PS) (i k : ℕ)
    (hpos : 0 < parent M i k) : nextR M i (parent M i k) k = true := by
  have hmem : parent M i k ∈ parents M i k := by
    have hdef : parent M i k = (parents M i k).headD 0 := rfl
    cases hl : parents M i k with
    | nil => rw [hdef, hl] at hpos; simp at hpos
    | cons x xs => rw [hdef, hl]; simp
  simp only [parents, List.mem_filter] at hmem
  exact hmem.2

private theorem condVI_bridge_nf (M : PS) (hM : TPS M)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    hasParent M 1 (Lng M - 1) = true ∧ parent M 1 (Lng M - 1) = Lng M - 2 := by
  obtain ⟨hp0, he1, hpos1⟩ := condVI_idx_nf hcond
  have hpar0pos : 0 < parent M 0 (Lng M - 1) := by rw [hp0]; omega
  have hnext0 : nextR M 0 (Lng M - 2) (Lng M - 1) = true := by
    have h := nextR_of_parent_pos_nf M 0 (Lng M - 1) hpar0pos
    rwa [hp0] at h
  have hle0 : leR M 0 (Lng M - 2) (Lng M - 1) = true := nextR0_leR M _ _ hnext0
  have hle0' : le0 M (Lng M - 2) (Lng M - 1) = true := by simpa [leR] using hle0
  have hnr1 : nextrel1 M (Lng M - 2) (Lng M - 1) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, hle0'⟩, ?_⟩
    intro u _
    by_cases hpu : Lng M - 2 < u
    · by_cases hux : le0 M u (Lng M - 1) = true
      · have hule : u ≤ Lng M - 1 := le0_index_fseq hux
        have hueq : u = Lng M - 1 := by omega
        subst hueq
        simp [hpu, hux]
      · simp [hpu, hux]
    · simp [hpu]
  have hnextR1 : nextR M 1 (Lng M - 2) (Lng M - 1) = true := by simpa [nextR] using hnr1
  have huniq : ∀ y, nextR M 1 y (Lng M - 1) = true → y = Lng M - 2 := by
    intro y hy; exact nextR1_unique_mr M y (Lng M - 2) (Lng M - 1) hy hnextR1
  exact ⟨(hasParent_iff_unique_fseq M 1 (Lng M - 1)).mpr ⟨Lng M - 2, hnextR1, huniq⟩,
    parent_eq_of_unique_fseq M 1 (Lng M - 1) (Lng M - 2) hnextR1 huniq⟩

private theorem oper_len_nf (M : PS) (N : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    Lng (oper M N) = Lng M - 2 + N := by
  obtain ⟨_, _, hpos1⟩ := condVI_idx_nf hcond
  obtain ⟨hhp, hjp⟩ := condVI_bridge_nf M hM hcond hj₁
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hi1]; exact hhp
  have h := length_oper_tiling M N hlast hzero hp
  simp only [hi1] at h
  rw [hjp] at h
  rw [show Lng M - 1 - (Lng M - 2) = 1 by omega] at h
  simpa using h

private theorem oper_block1_nf (M : PS) (N q : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1)
    (hq : q < N) :
    entry (oper M N) 1 (Lng M - 2 + q) = entry M 1 (Lng M - 2) := by
  obtain ⟨_, _, hpos1⟩ := condVI_idx_nf hcond
  obtain ⟨hhp, hjp⟩ := condVI_bridge_nf M hM hcond hj₁
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hi1]; exact hhp
  have hjq : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = Lng M - 2 := by rw [hi1]; exact hjp
  have hw : Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) = 1 := by rw [hjq]; omega
  have hs : (0 : ℕ) < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by rw [hw]; omega
  have hb := entry_oper_tiling_block_one M N q 0 hlast hzero hp hq hs
  rw [hw] at hb
  rw [hjq] at hb
  simpa using hb

private theorem oper_block0_nf (M : PS) (N q : ℕ)
    (hM : TPS M) (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1)
    (hq : q < N) :
    entry (oper M N) 0 (Lng M - 2 + q) =
      entry M 0 (Lng M - 2) + q * (entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2)) := by
  obtain ⟨_, _, hpos1⟩ := condVI_idx_nf hcond
  obtain ⟨hhp, hjp⟩ := condVI_bridge_nf M hM hcond hj₁
  have hi1 : idx1 M (Lng M - 1) = 1 := by simp [idx1, hpos1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hi1]; exact hhp
  have hjq : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = Lng M - 2 := by rw [hi1]; exact hjp
  have hw : Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) = 1 := by rw [hjq]; omega
  have hs : (0 : ℕ) < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by rw [hw]; omega
  have hif : (if 0 < idx1 M (Lng M - 1) then
      entry M 0 (Lng M - 1) - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) else 0)
      = entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2) := by
    rw [if_pos (by rw [hi1]; exact Nat.zero_lt_one), hjq]
  have hb := entry_oper_tiling_block_zero M N q 0 hlast hzero hp hq hs
  rw [hif] at hb
  rw [hw] at hb
  rw [hjq] at hb
  simpa using hb

/-! ## `d₀ = 1`（条件 (VI)＋簡約性、Isabelle `c6gx_condVI_row0_step`, pss_wip.thy:69962） -/

private theorem condVI_row0_step_nf (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hcond : transCondVI M = true) (hj₁ : 1 < Lng M - 1) :
    entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2) = 1 := by
  have hM : TPS M := RTPS_TPS M hR
  obtain ⟨hpar, _, _⟩ := condVI_idx_nf hcond
  obtain ⟨hA, _⟩ := RTPS_condAB M hR
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hstep := RedCondA_apply M hA 0 (Lng M - 1) (by omega) (by omega) hp0
  rw [hpar] at hstep
  omega

/-! ## 基点尾切片は 2 列（`seg P a (a+1)`） -/

private theorem seg_two_nf (P : PS) (a : ℕ) :
    seg P a (a + 1) =
      [(entry P 0 a, entry P 1 a), (entry P 0 (a + 1), entry P 1 (a + 1))] := by
  simp only [seg, show a + 1 + 1 - a = 2 by omega]
  rfl

/-- **fact (b)**（Isabelle `s84c1_Mark_L_mstar`, pss_wip.thy:53883 の条件 (VI) 崩壊形）。
`Mark (oper M (n+1)) (Lng (oper M n) - 1) = D_u(D_u 0)`（`u = M_{1,j₀}`）。
崩壊: 条件 (VI)＋簡約性で `d₀ = 1` なので基点尾切片は `const2ndSeq` そのもの、
`const2nd_Trans` で `(D_u)^2 0` に落ちる（`IncrFirst` 反復不要）。 -/
theorem c6nx_Mark_L_mstar_condVI (M : PS) (n : ℕ)
    (hR : RTPS M) (hmono : monoT M = true) (hcond : transCondVI M = true)
    (hj₁ : 1 < Lng M - 1) (hn : 2 ≤ n) :
    Mark (oper M (n + 1)) (Lng (oper M n) - 1)
      = Dprin (entry M 1 (transJ0 M) : ℕ∞)
          (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero) := by
  have hM : TPS M := RTPS_TPS M hR
  -- `u` と `a`
  have htj0 : transJ0 M = Lng M - 2 := by
    simp only [transJ0, lastParent, lastIdx]; exact (condVI_idx_nf hcond).1
  set u := entry M 1 (Lng M - 2) with hu_def
  set a := entry M 0 (Lng M - 2) + (n - 1) with ha_def
  have hd0 : entry M 0 (Lng M - 1) - entry M 0 (Lng M - 2) = 1 :=
    condVI_row0_step_nf M hR hmono hcond hj₁
  -- 長さ
  have hlen_n : Lng (oper M n) = Lng M - 2 + n := oper_len_nf M n hM hcond hj₁
  have hlen_sn : Lng (oper M (n + 1)) = Lng M - 2 + (n + 1) := oper_len_nf M (n + 1) hM hcond hj₁
  set Q := oper M (n + 1) with hQ_def
  set ms := Lng (oper M n) - 1 with hms_def
  have hms : ms = Lng M - 2 + (n - 1) := by rw [hms_def, hlen_n]; omega
  have hQlast : Lng Q - 1 = ms + 1 := by rw [hQ_def, hlen_sn, hms]; omega
  -- fact (a): 基点は Marked
  have hmk : Marked Q ms := s84c1_marked_L M n hM hcond hj₁ hn
  have hRQ : RTPS Q := RTPS_oper M (n + 1) hR (by omega)
  have hmslt : ms < Lng Q - 1 := by rw [hQlast]; omega
  -- Mark = Trans (尾切片)
  have hrepr : Mark Q ms = Trans (seg Q ms (Lng Q - 1)) :=
    Mark_Trans_repr Q ms hmk hRQ hmslt
  -- 尾切片の 4 成分
  have e1ms : entry Q 1 ms = u := by
    rw [hQ_def, hms]; exact oper_block1_nf M (n + 1) (n - 1) hM hcond hj₁ (by omega)
  have e1ms1 : entry Q 1 (ms + 1) = u := by
    have hpos : ms + 1 = Lng M - 2 + n := by rw [hms]; omega
    rw [hQ_def, hpos]; exact oper_block1_nf M (n + 1) n hM hcond hj₁ (by omega)
  have e0ms : entry Q 0 ms = a := by
    rw [hQ_def, hms]
    have := oper_block0_nf M (n + 1) (n - 1) hM hcond hj₁ (by omega)
    rw [this, hd0, ha_def]; ring
  have e0ms1 : entry Q 0 (ms + 1) = a + 1 := by
    have hpos : ms + 1 = Lng M - 2 + n := by rw [hms]; omega
    rw [hQ_def, hpos]
    have := oper_block0_nf M (n + 1) n hM hcond hj₁ (by omega)
    rw [this, hd0, ha_def]
    simp only [Nat.mul_one]; omega
  -- 尾切片 = `const2ndSeq a u 1`
  have hslice : seg Q ms (Lng Q - 1) = const2ndSeq a u 1 := by
    rw [hQlast, seg_two_nf Q ms, e0ms, e1ms, e0ms1, e1ms1]
    rfl
  -- `Trans (const2ndSeq a u 1) = (D_u)^[2] 0`
  have hTPSc : TPS (const2ndSeq a u 1) := by simp [TPS, const2ndSeq]
  have hTrans : Trans (const2ndSeq a u 1) = (Dprin (u : ℕ∞))^[1 + 1] BZero :=
    (const2nd_Trans (const2ndSeq a u 1) a u 1 rfl hTPSc).2 (Or.inl (by norm_num))
  rw [hrepr, hslice, hTrans, htj0, ← hu_def]
  show (Dprin (u : ℕ∞))^[1 + 1] BZero = Dprin (u : ℕ∞) (Dprin (u : ℕ∞) BZero)
  rfl

#print axioms c6nx_Mark_L_mstar_condVI

end PSS
