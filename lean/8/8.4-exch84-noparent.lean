import «8».«8.4-exch84-props»
import «7».«7.4-RightAnces-RightNodes»
import «7».«7.4-Adm-nextAdm»
import «6».«6.2-P-fseq»
import «6».«6.2-mono-ancestor-slice»
import «6».«6.3-adm-slice»
import «6».«6.3-admof-slice»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.5-monoT-Red»
import «6».«6.5-Red-Pred-commute»
import «6».«6.6-P-condAB»
import «6».«6.6-reduced-slice»
import «6».«6.8-standard-slice-Br-descending»
import «5».«5.1-ancestor-tree»

/-!
# §8.4 no-parent 脚の完全無条件化（`Exch84_condIIIIV_noParent`）

- 対象 Prop（«8».«8.4-Trans-fseq-condIII-IV» で定義）: `Exch84_condIIIIV_noParent`。
  §8.4 の命題は `j₋₂` の存在（`hasParent M 1 (Lng M - 1)`）を仮定するが、
  `8.7-fseq-descend` の `FseqDesc_exch{III,IV}` はそれを仮定しない。真正 ST_PS
  プールの単項ホスト 250 個中 58 個は `hasParent` を満たさない（反例
  `(1,1)(2,1)(3,1)`、`(2,2)(3,2)(4,2)`）。この脚では原文の結論 (3) は偽
  （`python/_e34_audit.py` で 0/27）なので、Prop は下流が実際に要る `∃ k` 形だけを
  主張する（`k = 0` で足りる）。

- 状況: «8».«8.4-exch84-props»（ビルド済み）が既に
  `Exch84_condIIIIV_noParent_holds : Exch84_noParent_domTag → Exch84_condIIIIV_noParent`
  を証明済み（`N[m] = Pred N` の崩壊 ＋ `k = 0` 読み戻し）。残差は `domTag` の 1 事実
  `Exch84_noParent_domTag` のみ。本ファイルはそれを**無条件に**証明し、合成して
  `Exch84_condIIIIV_noParent` を無条件で閉じる。

- Isabelle 設計図: `npx_domB_Trans_TBv` (layerB/pss_wip.thy:101419)。
  * 中核 `domB_classify_RN` の使用枝（`rnNatShape` 偽 ＋ 末尾 `≠ 0` ⟹ `T_{e-1}`）
    → `domTag_below_of_spine_enp`（`BT` の相互再帰で直接分類。`dfree` 不要）。
  * `npx_le0_last_entry_ge` (同 :101304、`¬hasParent` を使う唯一の場所)
    → `le0_last_entry_ge_enp`（`Max ?S` 論法を `Finset.max'` で写す）。
  * `s84c3_RightAnces_chain` (layerB/pss_wip.thy:55372) の弱形（`hd`/`sorted`/
    `winOK` を落とし `jpwin`＝`row1_last_bound` 段を丸ごと除去）
    → `RightAncesAux_chain_enp`（`RightAncesAux` の fuel 帰納法）。
  * `m_7_4_RightAnces_RightNodes` → `RightAnces_RightNodes`（«7».«7.4»）。

- 依存（すべてビルド済み）: «8».«8.4-exch84-props»（`Exch84_condIIIIV_noParent_holds`・
  `Exch84_noParent_domTag`・`Exch84_condIIIIV_noParent`）、
  «7».«7.4-RightAnces-RightNodes»/«7».«7.4-Adm-nextAdm»、
  «6».«6.2-P-fseq»/«6».«6.2-mono-ancestor-slice»/«6».«6.3-adm-slice»/
  «6».«6.3-admof-slice»/«6».«6.4-FirstNodes-Joints-mono»/«6».«6.5-monoT-Red»/
  «6».«6.5-Red-Pred-commute»/«6».«6.6-P-condAB»/«6».«6.6-reduced-slice»
  （`RTPS_initial_slice`）/«6».«6.8-standard-slice-Br-descending»、
  «5».«5.1-ancestor-tree»。

- 私的補助の suffix: `_enp`。
- 状態: ✅ 証明済（sorry 0、仮定 0、公理 `[propext, Classical.choice, Quot.sound]`）。
-/

namespace PSS

private theorem rightNodesList_ne_nil_enp (ps : List BP) (hps : ps ≠ []) :
    rightNodesList ps ≠ [] := by
  induction ps with
  | nil => exact (hps rfl).elim
  | cons p ps ih =>
      cases ps with
      | nil => cases p with | db v a => simp [rightNodesList, rightNodesBP]
      | cons q qs => simpa [rightNodesList] using ih (by simp)

private theorem RightNodes_ne_nil_enp {t : BT} (ht : t ≠ BZero) :
    RightNodes t ≠ [] := by
  rcases t with ⟨ps⟩
  have hps : ps ≠ [] := by
    intro h; subst h; exact ht rfl
  simpa [RightNodes] using rightNodesList_ne_nil_enp ps hps

/-! ## 分類器 -/

/-- `ℕ∞` の切り捨て減算。`0 < e ≤ n` なら `e - 1 < n`。 -/
private theorem enat_sub_one_lt_enp {e n : ℕ} (he : 0 < e) (hen : e ≤ n) :
    ((e : ℕ∞) - 1) < (n : ℕ∞) := by
  rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) by simp, ← ENat.coe_sub]
  exact_mod_cast (by omega : e - 1 < n)

private def SpineBT_enp (e : ℕ) (t : BT) : Prop :=
  t ≠ BZero → (∀ x ∈ RightNodes t, e ≤ x) →
    (RightNodes t).getLastD 0 = e → domTag t = .below (e - 1)

private def SpineBP_enp (e : ℕ) (p : BP) : Prop :=
  (∀ x ∈ rightNodesBP p, e ≤ x) →
    (rightNodesBP p).getLastD 0 = e → domTagBP p = .below (e - 1)

private def SpineList_enp (e : ℕ) (ps : List BP) : Prop :=
  ps ≠ [] → (∀ x ∈ rightNodesList ps, e ≤ x) →
    (rightNodesList ps).getLastD 0 = e → domTagList ps = .below (e - 1)

/-- 右端 spine が全て `≥ e` で末尾がちょうど `e > 0` なら、定義域タグは `T_{e-1}`。
Isabelle `domB_classify_RN` の、本証明が使う枝だけを直接取り出した形
（`rnNatShape` が偽 ＋ 末尾 `≠ 0`）。`dfree` 不要: `v = ⊤` は `v.toNat = 0 < e`
で弾かれる。 -/
private theorem domTag_below_of_spine_enp {e : ℕ} (he : 0 < e) (t : BT)
    (ht : t ≠ BZero) (hge : ∀ x ∈ RightNodes t, e ≤ x)
    (hlast : (RightNodes t).getLastD 0 = e) :
    domTag t = .below (e - 1) := by
  revert ht hge hlast
  exact BT.rec
    (motive_1 := SpineBT_enp e)
    (motive_2 := SpineBP_enp e)
    (motive_3 := SpineList_enp e)
    (fun ps ih hne hge hlast => by
      have hps : ps ≠ [] := by
        intro h; subst h; exact hne rfl
      simpa [domTag, RightNodes] using
        ih hps (by simpa [RightNodes] using hge) (by simpa [RightNodes] using hlast))
    (fun v a ih hge hlast => by
      -- `rightNodesBP (.db v a) = v.toNat :: RightNodes a`
      have hvmem : v.toNat ∈ rightNodesBP (.db v a) := by simp [rightNodesBP]
      have hvge : e ≤ v.toNat := hge _ hvmem
      have hvtop : v ≠ ⊤ := by
        intro h; subst h; simp [ENat.toNat_top] at hvge; omega
      have hvcoe : (v.toNat : ℕ∞) = v := ENat.coe_toNat hvtop
      by_cases ha0 : a = BZero
      · subst a
        have hv : v.toNat = e := by
          simpa [rightNodesBP, RightNodes, rightNodesList] using hlast
        have hv0 : v ≠ 0 := by
          intro h; subst h; simp at hv; omega
        simp [SpineBP_enp, domTagBP, BZero, hv0, hvtop, hv]
      · have hRne : RightNodes a ≠ [] := RightNodes_ne_nil_enp ha0
        have hgea : ∀ x ∈ RightNodes a, e ≤ x := by
          intro x hx; exact hge x (by simp [rightNodesBP, hx])
        have hlasta : (RightNodes a).getLastD 0 = e := by
          rw [← hlast]
          cases hR : RightNodes a with
          | nil => exact (hRne hR).elim
          | cons w ws => simp [rightNodesBP, hR]
        have hiha : domTag a = .below (e - 1) := ih ha0 hgea hlasta
        have ha0b : (a == BZero) = false := by simpa [beq_iff_eq] using ha0
        simp [domTagBP, ha0b, hiha]
        rw [← hvcoe]
        exact enat_sub_one_lt_enp he hvge)
    (by simp [SpineList_enp])
    (fun p ps ihp ihps => by
      cases ps with
      | nil =>
          intro _ hge hlast
          simpa [domTagList, rightNodesList] using
            ihp (by simpa [rightNodesList] using hge)
              (by simpa [rightNodesList] using hlast)
      | cons q qs =>
          intro _ hge hlast
          simpa [domTagList, rightNodesList] using
            ihps (by simp) (by simpa [rightNodesList] using hge)
              (by simpa [rightNodesList] using hlast))
    t

/-! ## `¬hasParent` の値的特徴づけ（Isabelle `npx_le0_last_entry_ge`, wip:101304） -/

/-- 行 1 に親を持たない右端は、その全ての `le0` 祖先の行 1 値以下。
対偶: より低い行 1 値を持つ祖先があれば、その中の**極大**なものが行 1 の親になる
（Isabelle の `Max ?S` 論法をそのまま `Finset.max'` で写した）。 -/
private theorem le0_last_entry_ge_enp {N : PS} {j : ℕ}
    (nhp : hasParent N 1 (Lng N - 1) = false)
    (hle0 : leR N 0 j (Lng N - 1) = true) :
    entry N 1 (Lng N - 1) ≤ entry N 1 j := by
  classical
  set j₁ := Lng N - 1 with hj₁
  by_contra hcon
  have hjlt : entry N 1 j < entry N 1 j₁ := by omega
  have hle0' : le0 N j j₁ = true := by simpa [leR] using hle0
  have hbounds := hle0'
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hbounds
  have hj₁L : j₁ < Lng N := hbounds.1.2
  have hjle : j ≤ j₁ := le0_index_fseq hle0'
  have hjne : j ≠ j₁ := by intro h; rw [h] at hjlt; omega
  have hjlt' : j < j₁ := by omega
  -- 極大の「低い」祖先
  set S : Finset ℕ :=
    (Finset.range j₁).filter (fun i => le0 N i j₁ = true ∧ entry N 1 i < entry N 1 j₁)
    with hS
  have hjS : j ∈ S := by
    simp [hS, Finset.mem_filter, Finset.mem_range, hjlt', hle0', hjlt]
  have hne : S.Nonempty := ⟨j, hjS⟩
  set jm := S.max' hne with hjm
  have hjmS : jm ∈ S := S.max'_mem hne
  have hjmmax : ∀ i ∈ S, i ≤ jm := fun i hi => S.le_max' i hi
  have hjmfacts : jm < j₁ ∧ le0 N jm j₁ = true ∧ entry N 1 jm < entry N 1 j₁ := by
    have := hjmS
    simp only [hS, Finset.mem_filter, Finset.mem_range] at this
    exact ⟨this.1, this.2.1, this.2.2⟩
  obtain ⟨hjmlt, hjmle0, hjment⟩ := hjmfacts
  have hjmL : jm < Lng N := by omega
  -- `jm` の上にある祖先は全て行 1 値が `≥ entry N 1 j₁`
  have huniv : ∀ i, jm < i → le0 N i j₁ = true → entry N 1 j₁ ≤ entry N 1 i := by
    intro i hi hile0
    have hile : i ≤ j₁ := le0_index_fseq hile0
    by_cases hieq : i = j₁
    · rw [hieq]
    · have hilt : i < j₁ := by omega
      by_contra hc
      have hient : entry N 1 i < entry N 1 j₁ := by omega
      have hiS : i ∈ S := by
        simp [hS, Finset.mem_filter, Finset.mem_range, hilt, hile0, hient]
      exact absurd (hjmmax i hiS) (by omega)
  -- `jm` は行 1 の親
  have hnext1 : nextrel1 N jm j₁ = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨hjmL, hj₁L⟩, hjmlt⟩, hjment⟩, hjmle0⟩, ?_⟩
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true,
      decide_eq_false_iff_not]
    by_cases hjmi : jm < i
    · by_cases hile0 : le0 N i j₁ = true
      · exact Or.inr (huniv i hjmi hile0)
      · exact Or.inl (Or.inr (by simpa using hile0))
    · exact Or.inl (Or.inl hjmi)
  have hnextR : nextR N 1 jm j₁ = true := by simpa [nextR] using hnext1
  have hhp : hasParent N 1 j₁ = true := by
    rw [hasParent_iff_unique_fseq]
    exact ⟨jm, hnextR, fun y hy => nextR1_unique_mr N y jm j₁ hy hnextR⟩
  rw [hhp] at nhp
  exact Bool.noConfusion nhp

/-! ## `RightAnces` の鎖不変量（Isabelle `s84c3_RightAnces_chain`, wip:55372 の弱形） -/

/-- Isabelle `s84c3_chainOK` のうち、本証明が使う 3 項のみ
（`hd = 0` / `sorted_wrt (<)` / `s84c3_winOK` は不要なので落とした。
その結果 Isabelle が `jpwin`＝`row1_last_bound` の二分法に費やす段が丸ごと消える）。 -/
private def ChainOK_enp (Q : PS) (ks : List ℕ) : Prop :=
  ks ≠ [] ∧ ks.getLastD 0 = Lng Q - 1 ∧ ∀ k ∈ ks, leR Q 0 k (Lng Q - 1) = true

private theorem Lng_seg0_enp (Q : PS) (j : ℕ) : Lng (seg Q 0 j) = j + 1 := by
  simp [seg, Lng]

private theorem getLastD_append_enp {α : Type} (as bs : List α) (d : α)
    (hbs : bs ≠ []) : (as ++ bs).getLastD d = bs.getLastD d := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
    List.getLast?_append_of_ne_nil _ hbs]

private theorem getLastD_map_enp {α β : Type} (f : α → β) (l : List α) (d : α) (e : β)
    (hl : l ≠ []) : (l.map f).getLastD e = f (l.getLastD d) := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_map]
  cases hg : l.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hl
  | some a => simp

/-- `RightAnces Q` の各項は `Q` の行 1 の値であり、その添字は全て右端の `le0` 祖先。
Isabelle `s84c3_RightAnces_chain` の弱形を、Lean の fuel 版 `RightAncesAux` に対する
fuel 帰納法で写したもの。 -/
private theorem RightAncesAux_chain_enp (fuel : ℕ) :
    ∀ Q : PS, RTPS Q → monoT Q = true → Lng Q ≤ fuel →
      ∃ ks, RightAncesAux fuel Q = ks.map (entry Q 1) ∧ ChainOK_enp Q ks := by
  induction fuel with
  | zero =>
      intro Q hR hmono hfuel
      have : TPS Q := RTPS_TPS Q hR
      have : 0 < Lng Q := List.length_pos_of_ne_nil this
      omega
  | succ fuel ih =>
      intro Q hR hmono hfuel
      have hQT : TPS Q := RTPS_TPS Q hR
      have hLpos : 0 < Lng Q := List.length_pos_of_ne_nil hQT
      have hnz : zeroT Q = false := by
        have := hmono
        simp only [monoT, Bool.and_eq_true, Bool.not_eq_true'] at this
        exact this.1
      have hmono0 : leR Q 0 0 (Lng Q - 1) = true := by
        have := hmono
        simp only [monoT, Bool.and_eq_true] at this
        exact this.2
      have heq := RightAncesAux_RTPS_equation fuel Q hR
      set j₁ := Lng Q - 1 with hj₁
      have hj₁L : j₁ < Lng Q := by omega
      by_cases hone : Lng Q = 1
      · -- `j₁ = 0`: 単一列。単項性から行 1 の値は非零。
        have hj₁z : j₁ = 0 := by omega
        have he10 : entry Q 1 0 ≠ 0 := by
          intro h
          have : zeroT Q = true := by simp [zeroT, hone, h]
          rw [this] at hnz; exact Bool.noConfusion hnz
        have hQ0 : (Q.getD 0 (0, 0) == (0, 0)) = false := by
          rcases hq : Q[0]? with _ | p
          · exact absurd (he10 (by simp [entry, hq])) (by simp)
          · have hp2 : p.2 ≠ 0 := by
              intro h; exact he10 (by simp [entry, hq, h])
            simp only [List.getD_eq_getElem?_getD, hq, Option.getD_some]
            simp only [beq_eq_false_iff_ne, ne_eq, Prod.ext_iff, not_and]
            intro _
            exact hp2
        refine ⟨[0], ?_, ?_, ?_, ?_⟩
        · rw [heq]
          simp only [hj₁z, beq_self_eq_true, if_true, hQ0, if_false,
            List.map_cons, List.map_nil]
          simp
        · simp
        · rw [show Lng Q - 1 = 0 from by omega]; rfl
        · intro k hk
          simp only [List.mem_singleton] at hk
          subst hk
          rw [← hj₁, hj₁z]
          exact leR0_refl_68 Q 0 hLpos
      · have hL2 : 1 < Lng Q := by omega
        have hj₁ne : j₁ ≠ 0 := by omega
        by_cases hpz : zeroT (Pred Q) = true
        · -- `Pred Q` が零項 ⟹ `Lng Q = 2` かつ `entry Q 1 0 = 0`
          have hLP : Lng (Pred Q) = 1 := by
            have := hpz; simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at this
            exact this.1
          have he10 : entry Q 1 0 = 0 := by
            have hp0 : entry (Pred Q) 1 0 = 0 := by
              have := hpz; simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at this
              exact this.2
            rwa [entry_Pred Q 1 0 (by
              have : Lng (Pred Q) = Lng Q - 1 := by
                unfold Pred; rw [if_neg (by omega)]; simp
              omega)] at hp0
          refine ⟨[0, j₁], ?_, ?_, ?_, ?_⟩
          · rw [heq]
            simp only [beq_iff_eq, hj₁ne, if_false, hmono, if_true, hpz, if_true,
              List.map_cons, List.map_nil, he10, ← hj₁]
          · simp
          · simp [← hj₁]
          · intro k hk
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl
            · exact hmono0
            · exact leR0_refl_68 Q j₁ hj₁L
        · -- 主枝: `jp = parent Q 0 j₁`, `jm = Adm Q jp`
          have hpzf : zeroT (Pred Q) = false := by simpa using hpz
          set jp := parent Q 0 j₁ with hjp
          set jm := Adm Q jp with hjm
          have hhp : hasParent Q 0 j₁ = true :=
            mono_hasParent_row0 Q hQT hmono j₁ (by omega) hj₁L
          have hparR : nextR Q 0 jp j₁ = true := nextR_parent0_of_hasParent Q j₁ hhp
          have hnr0 : nextrel0 Q jp j₁ = true := by simpa [nextR] using hparR
          have hjplt : jp < j₁ := by
            have := hnr0
            simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at this
            exact this.1.1.2
          have hle0jpj1 : leR Q 0 jp j₁ = true := nextR0_leR Q jp j₁ hparR
          have hjmle : jm ≤ jp := Adm_le Q jp
          have hjmadm : adm Q jm = true := Adm_adm Q jp
          have hjmlt : jm < j₁ := by omega
          have hjmL : jm < Lng Q := by omega
          have hle0jmjp : leR Q 0 jm jp :=
            row1_implies_row0 Q jm jp hQT (adm_row1_ancestry Q jp hQT (by omega))
          have hle0jmj1 : leR Q 0 jm j₁ = true :=
            row0_transitive Q jm jp j₁ hQT hle0jmjp hle0jpj1
          have hle00jm : leR Q 0 0 jm = true :=
            ancestor_tree_1 Q 0 jm j₁ hQT hmono0 (by omega) (by omega)
          -- `a` の部分
          have apart : ∃ aks : List ℕ,
              (if zeroT (seg Q 0 jm) then [0] else RightAncesAux fuel (seg Q 0 jm))
                = aks.map (entry Q 1) ∧ ∀ k ∈ aks, leR Q 0 k jm = true := by
            by_cases hsz : zeroT (seg Q 0 jm) = true
            · have hjmz : jm = 0 := by
                have hLs : Lng (seg Q 0 jm) = 1 := by
                  have := hsz; simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at this
                  exact this.1
                rw [Lng_seg0_enp] at hLs; omega
              have he10 : entry Q 1 0 = 0 := by
                have hs0 : entry (seg Q 0 jm) 1 0 = 0 := by
                  have := hsz; simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at this
                  exact this.2
                rwa [entry_seg Q 0 jm 1 0 (by rw [Lng_seg0_enp]; omega)] at hs0
              refine ⟨[0], ?_, ?_⟩
              · simp [hsz, he10]
              · intro k hk
                simp only [List.mem_singleton] at hk
                subst hk
                rw [hjmz]
                exact leR0_refl_68 Q 0 hLpos
            · have hszf : zeroT (seg Q 0 jm) = false := by simpa using hsz
              have hSR : RTPS (seg Q 0 jm) := RTPS_initial_slice Q jm hR (by omega)
              have hLs : Lng (seg Q 0 jm) = jm + 1 := Lng_seg0_enp Q jm
              have hSmono : monoT (seg Q 0 jm) = true := by
                have htr : leR (seg Q 0 jm) 0 0 jm = leR Q 0 (0 + 0) (0 + jm) :=
                  leR0_seg_adm Q 0 jm 0 jm (by omega) hjmL
                  (by rw [hLs]; omega) (by rw [hLs]; omega)
                simp only [monoT, Bool.and_eq_true, Bool.not_eq_true', hszf, hLs,
                  Nat.add_sub_cancel, true_and]
                simpa using htr.trans (by simpa using hle00jm)
              obtain ⟨ks0, hks0map, hks0ne, hks0last, hks0le⟩ :=
                ih (seg Q 0 jm) hSR hSmono (by rw [hLs]; omega)
              rw [hLs] at hks0le hks0last
              simp only [Nat.add_sub_cancel] at hks0le hks0last
              have hbound : ∀ k ∈ ks0, k ≤ jm := by
                intro k hk
                exact le0_index_fseq (by simpa [leR] using hks0le k hk)
              refine ⟨ks0, ?_, ?_⟩
              · rw [if_neg hsz, hks0map]
                apply List.map_congr_left
                intro k hk
                have := entry_seg Q 0 jm 1 k
                  (by rw [Lng_seg0_enp]; exact Nat.lt_succ_of_le (hbound k hk))
                simpa using this
              · intro k hk
                have htr : leR (seg Q 0 jm) 0 k jm = leR Q 0 (0 + k) (0 + jm) :=
                  leR0_seg_adm Q 0 jm k jm (by omega) hjmL
                  (by rw [Lng_seg0_enp]; exact Nat.lt_succ_of_le (hbound k hk))
                  (by rw [Lng_seg0_enp]; omega)
                have h := hks0le k hk
                rw [htr] at h
                simpa using h
          obtain ⟨aks, haksmap, haksle⟩ := apart
          -- `tail` の部分
          set tailks : List ℕ :=
            if transCondI Q || transCondIII Q || transCondV Q || transCondVI Q
            then [j₁] else [jp, j₁] with htailks
          have htailmap :
              (if transCondI Q || transCondIII Q || transCondV Q || transCondVI Q
               then [entry Q 1 j₁] else [entry Q 1 jp, entry Q 1 j₁])
                = tailks.map (entry Q 1) := by
            rw [htailks]; split <;> simp
          have htailne : tailks ≠ [] := by rw [htailks]; split <;> simp
          have htaillast : tailks.getLastD 0 = j₁ := by rw [htailks]; split <;> simp
          have htaille : ∀ k ∈ tailks, leR Q 0 k j₁ = true := by
            intro k hk
            rw [htailks] at hk
            split at hk
            · simp only [List.mem_singleton] at hk
              subst hk; exact leR0_refl_68 Q j₁ hj₁L
            · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hk
              rcases hk with rfl | rfl
              · exact hle0jpj1
              · exact leR0_refl_68 Q j₁ hj₁L
          have hraw : RightAncesAux (fuel + 1) Q =
              (if zeroT (seg Q 0 jm) then [0] else RightAncesAux fuel (seg Q 0 jm))
                ++ (if transCondI Q || transCondIII Q || transCondV Q || transCondVI Q
                    then [entry Q 1 j₁] else [entry Q 1 jp, entry Q 1 j₁]) := by
            rw [heq]
            simp only [beq_iff_eq, hj₁ne, hmono, hpzf, if_false, if_true,
              Bool.false_eq_true, ← hjp, ← hjm]
            split <;> simp
          refine ⟨aks ++ tailks, ?_, ?_, ?_, ?_⟩
          · rw [hraw, List.map_append, ← haksmap, ← htailmap]
          · simp [htailne]
          · rw [← hj₁, ← htaillast]
            exact getLastD_append_enp aks tailks 0 htailne
          · intro k hk
            rw [List.mem_append] at hk
            rcases hk with hk | hk
            · exact row0_transitive Q k jm j₁ hQT (haksle k hk) hle0jmj1
            · exact htaille k hk

/-- `RightAnces` の鎖不変量（弱形）を `Trans N` の `RightNodes` に翻訳した最終形。 -/
private theorem RightNodes_Trans_chain_enp (N : PS) (hR : RTPS N)
    (hmono : monoT N = true) :
    ∃ ks, RightNodes (Trans N) = ks.map (entry N 1) ∧ ChainOK_enp N ks := by
  obtain ⟨ks, hmap, hchain⟩ :=
    RightAncesAux_chain_enp (transFuel N) N hR hmono (transFuel_ge_length N)
  refine ⟨ks, ?_, hchain⟩
  rw [← RightAnces_RightNodes N hR, RightAnces, hmap]

/-! ## `Exch84_noParent_domTag` の drop-in（house pattern） -/

/-- `Exch84_noParent_domTag` の drop-in。
Isabelle `npx_domB_Trans_TBv` (layerB/pss_wip.thy:101419) の `domTag` 版。
`¬hasParent` は `le0_last_entry_ge_enp` の 1 箇所でのみ使う。 -/
theorem Exch84_noParent_domTag_holds : Exch84_noParent_domTag := by
  intro N hR hmono hj1 epos nhp
  set e := entry N 1 (Lng N - 1) with he
  obtain ⟨ks, hmap, hne, hlast, hle⟩ := RightNodes_Trans_chain_enp N hR hmono
  have hknil : ks ≠ [] := hne
  -- `Trans N ≠ BZero`
  have hnz : zeroT N = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hz
    have := hz; simp only [zeroT, Bool.and_eq_true, beq_iff_eq] at this
    omega
  have hTne : Trans N ≠ BZero := by
    intro h
    have := (Trans_preserves_zeroT N (RTPS_TPS N hR)).2 h
    rw [this] at hnz; exact Bool.noConfusion hnz
  -- 全 spine 値 `≥ e`
  have hge : ∀ x ∈ RightNodes (Trans N), e ≤ x := by
    intro x hx
    rw [hmap, List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkle : leR N 0 k (Lng N - 1) = true := hle k hk
    exact le0_last_entry_ge_enp nhp hkle
  -- 末尾 spine 値 `= e`
  have hlastR : (RightNodes (Trans N)).getLastD 0 = e := by
    rw [hmap, getLastD_map_enp (entry N 1) ks 0 0 hknil, hlast, he]
  exact domTag_below_of_spine_enp epos (Trans N) hTne hge hlastR

#print axioms Exch84_noParent_domTag_holds

/-! ## 合成: `Exch84_condIIIIV_noParent` の無条件 drop-in（house pattern） -/

/-- ミッションの対象 Prop `Exch84_condIIIIV_noParent`（«8».«8.4-Trans-fseq-condIII-IV»
で定義）の**無条件**証明。ビルド済み «8».«8.4-exch84-props» の
`Exch84_condIIIIV_noParent_holds`（`domTag` の 1 事実を仮定に取る）に、本ファイルで
無条件証明した `Exch84_noParent_domTag_holds` を与えて合成しただけ。
Prop 自身を型に取っているので、drop-in の忠実性はエラボレータが保証する。 -/
theorem Exch84_condIIIIV_noParent_holds_enp : Exch84_condIIIIV_noParent :=
  Exch84_condIIIIV_noParent_holds Exch84_noParent_domTag_holds

#print axioms Exch84_condIIIIV_noParent_holds_enp

end PSS
