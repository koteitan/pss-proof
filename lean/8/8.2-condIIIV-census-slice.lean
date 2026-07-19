import «8».«8.2-condIIIV-base-forms»
import «8».«8.2-condIIIV-peel-values»

/-!
# §8.2 条件(II)/(IV) VE34 — **census / slice geometry** の討伐
（`BgxNotleftRun0_bf` / `BgxMpSliceData_bf`）

親 `8.2-condIIIV-base-forms` が最小残差として放出した 2 つの `Prop` を無条件討伐する:

- **`BgxMpSliceData_bf`**（Isabelle `bgx_Mp_form` 106407 の geometry core）: BASE ホストの
  終切片 `Mp = seg N j₀' (Lng N - 1)` が `Adm0`（`transJm1 Mp = 0`）かつ条件(I)/(III)/(V)
  ホストであること。`Adm0` は `nextR`-seg 転送（`nextR_seg_adm`）で終列の直近祖先が列 0
  （joint）であることを読み、条件ホスト性は row-1 valley 境界（`row1_last_bound`、私的再証明）
  と `VE34_base_notCondA` の条件(V)排除で得る。

- **`BgxNotleftRun0_bf`**（Isabelle `bgx_notleft_run0` 106972 = strong-monomiality census）:
  run-base BASE ホストで `isleft` selector が発火しないこと。`Trans (Pred N)` の body の
  最終 principal の頭値が `> N₁,j₀'`。trunk corner（`bgx_trunk_Trans`）と branching の
  3-clause dispatch（census `subexpr_component_strongmono` + head-edge 比較 + `LastStep`
  最小性）を移植。

- 訂正: なし（Isabelle 済補題の逐語移植）。
- Private suffix: `_cs2`。
-/

namespace PSS

open Classical

/-! ## 行 1 の最終列バウンド（Isabelle `row1_last_bound` 21016 の私的再証明）

`8.2-subexpr-adm0-ctx` の private `row1_last_bound_sx` を、その private 依存
（`le0Aux_index_mono_sx` / `le0Aux_last_step_sx` / `row0_valley_last_sx`）ごと `_cs2`
suffix で再導出する。基礎補題（`le0Aux_mono_fseq` / `mono_hasParent_row0` /
`nextR_parent0_of_hasParent` / `nextR0_leR` / `hasParent_iff_unique_fseq` /
`parent_eq_of_unique_fseq` / `parent_eq_of_nextR0` / `RTPS_condAB` / `RedCondA_apply`）は
すべて public。 -/

/-- `le0Aux` の添字単調性（5.1 の私的補題の再証明）。 -/
private theorem le0Aux_index_mono_cs2 {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by simpa [le0Aux] using h
      omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, _, hap⟩
      · omega
      · have := ih hap
        omega

/-- `le0Aux` の最終ステップ剥がし: `a ≠ b` なら `b` の直前点 `p` がある。 -/
private theorem le0Aux_last_step_cs2 {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) (hne : a ≠ b) :
    ∃ p, nextrel0 M p b = true ∧ le0Aux M fuel a p = true := by
  cases fuel with
  | zero =>
      have : a = b := by simpa [le0Aux] using h
      exact absurd this hne
  | succ fuel =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, _, hnext, hap⟩
      · exact absurd h hne
      · exact ⟨p, hnext,
          le0Aux_mono_fseq M fuel (fuel + 1) a p (by omega) hap⟩

/-- 行 0 の谷（Isabelle `row0_valley_last` 20973 の私的再証明）。 -/
private theorem row0_valley_last_cs2 (M : PS) (_hM : TPS M)
    (_hmono : monoT M = true) (_hL : 1 < Lng M) (j : ℕ)
    (hj : parent M 0 (Lng M - 1) < j)
    (hle : le0 M j (Lng M - 1) = true) : j = Lng M - 1 := by
  by_contra hne
  have hh := hle
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨p, hnext, hap⟩ := le0Aux_last_step_cs2 hh.2 hne
  have hpR : nextR M 0 p (Lng M - 1) = true := by simpa [nextR] using hnext
  have hpar : parent M 0 (Lng M - 1) = p := parent_eq_of_nextR0 M p _ hpR
  have hjp : j ≤ p := le0Aux_index_mono_cs2 hap
  omega

/-- 行 1 の最終列バウンド（Isabelle `row1_last_bound` 21016 の私的再証明）。 -/
private theorem row1_last_bound_cs2 (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hL : 1 < Lng M) :
    entry M 1 (Lng M - 1) ≤ entry M 1 (parent M 0 (Lng M - 1)) ∨
      entry M 1 (parent M 0 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1) := by
  by_cases hge : entry M 1 (Lng M - 1) ≤ entry M 1 (parent M 0 (Lng M - 1))
  · exact Or.inl hge
  right
  have hM : TPS M := RTPS_TPS M hR
  have he1lt : entry M 1 (parent M 0 (Lng M - 1)) < entry M 1 (Lng M - 1) := by
    omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hparR := nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hn0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hparR
  have hjplt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have hh := hn0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hjpL : parent M 0 (Lng M - 1) < Lng M := by omega
  have hle0jp : le0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    have := nextR0_leR M (parent M 0 (Lng M - 1)) (Lng M - 1) hparR
    simpa [leR] using this
  have hn1 : nextrel1 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
    refine ⟨⟨⟨⟨⟨hjpL, by omega⟩, hjplt⟩, he1lt⟩, hle0jp⟩, ?_⟩
    intro x _hx
    by_cases hxgt : parent M 0 (Lng M - 1) < x
    · by_cases hxle : le0 M x (Lng M - 1) = true
      · have hxeq : x = Lng M - 1 :=
          row0_valley_last_cs2 M hM hmono hL x hxgt hxle
        subst hxeq
        simp
      · simp [hxle]
    · simp [hxgt]
  have hn1R : nextR M 1 (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hn1
  have huniq1 : ∀ k, nextR M 1 k (Lng M - 1) = true
      → k = parent M 0 (Lng M - 1) := by
    intro k hk
    have hnk : nextrel1 M k (Lng M - 1) = true := by simpa [nextR] using hk
    have hh := hnk
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at hh
    obtain ⟨⟨⟨⟨⟨_hkL, _⟩, hklt⟩, _hke1⟩, hkle0⟩, hall⟩ := hh
    by_contra hkne
    rcases Nat.lt_or_ge k (parent M 0 (Lng M - 1)) with hklt2 | hge2
    · have h := hall (parent M 0 (Lng M - 1)) hjpL
      rw [hle0jp] at h
      simp only [hklt2, decide_true, Bool.and_true, Bool.not_true,
        Bool.false_or, decide_eq_true_eq] at h
      omega
    · have hkgt : parent M 0 (Lng M - 1) < k := by omega
      have := row0_valley_last_cs2 M hM hmono hL k hkgt hkle0
      omega
  have hp1 : hasParent M 1 (Lng M - 1) = true :=
    (hasParent_iff_unique_fseq M 1 (Lng M - 1)).mpr ⟨_, hn1R, huniq1⟩
  have hpar1 : parent M 1 (Lng M - 1) = parent M 0 (Lng M - 1) :=
    parent_eq_of_unique_fseq M 1 (Lng M - 1) _ hn1R huniq1
  have hA := (RTPS_condAB M hR).1
  have hstep := RedCondA_apply M hA 1 (Lng M - 1) (by omega) (by omega) hp1
  rw [hpar1] at hstep
  exact hstep

/-! ## `BgxMpSliceData_bf`（終切片 `Mp` の Adm0 + 条件(I)/(III)/(V) ホスト性） -/

/-- **`BgxMpSliceData_cs2`**: `BgxMpSliceData_bf` を無条件討伐。 -/
theorem BgxMpSliceData_cs2 : BgxMpSliceData_bf := by
  intro N hRegD hbase hdeep
  obtain ⟨hReg4, hdesc⟩ := hRegD
  have hReg4' := hReg4
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩ := hReg4
  have hM : TPS N := RTPS_TPS N hR
  set j0 := (Joints N).getD ((Br N).length - 1) 0 with hj0def
  have hL : 1 < Lng N := by omega
  -- `parent N 0 (Lng N-1) = j0`（最終 joint）
  have hpar_j0 : parent N 0 (Lng N - 1) = j0 := by
    have h : transJ0 N = j0 := by rw [hj0def]; exact VE34_base_transJ0 N hReg4' hbase
    simpa [transJ0, lastParent, lastIdx] using h
  have hLPN : lastParent N = j0 := by simpa [lastParent, lastIdx] using hpar_j0
  -- 終切片 `Mp` の所属と長さ
  have hj0ltL : j0 < Lng N - 1 := by omega
  have hND : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
  have hMpDT0 : DTPS (seg N j0 (Lng N - 1)) :=
    strongmono_slice N j0 (Lng N - 1) hND hj0ltL (le_refl _) (le_of_eq hj0def)
  set Mp := seg N j0 (Lng N - 1) with hMpdef
  obtain ⟨hMpR, hMpmono, _hMpdesc⟩ := (DTPS_iff Mp).mp hMpDT0
  have hMpT : TPS Mp := RTPS_TPS Mp hMpR
  have hLngMp : Lng Mp = Lng N - j0 := by rw [hMpdef, length_seg]; omega
  have hMpL : 0 < Lng Mp := by omega
  have hMpLm1 : Lng Mp - 1 < Lng Mp := by omega
  have hidx1 : j0 + (Lng Mp - 1) = Lng N - 1 := by omega
  -- 終列 `Lng N-1` の行0直近祖先は列 `j0`
  have hpN : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N hM hmono (Lng N - 1) (by omega) (by omega)
  have hnextN : nextR N 0 j0 (Lng N - 1) = true := by
    have h := nextR_parent0_of_hasParent N (Lng N - 1) hpN
    rwa [hpar_j0] at h
  -- 切片へ転送: `nextR Mp 0 0 (Lng Mp-1)`
  have hnextMp : nextR Mp 0 0 (Lng Mp - 1) = true := by
    have ht := nextR_seg_adm N j0 (Lng N - 1) 0 0 (Lng Mp - 1)
      (by omega) (by omega)
      (by rw [← hMpdef]; exact hMpL)
      (by rw [← hMpdef]; exact hMpLm1)
    rw [← hMpdef, Nat.add_zero, hidx1] at ht
    rw [ht]; exact hnextN
  -- `parent Mp 0 (Lng Mp-1) = 0`
  have hpMp : hasParent Mp 0 (Lng Mp - 1) = true :=
    mono_hasParent_row0 Mp hMpT hMpmono (Lng Mp - 1) (by omega) (by omega)
  have hparMp : parent Mp 0 (Lng Mp - 1) = 0 := by
    obtain ⟨w, _hw, huw⟩ := (hasParent_iff_unique_fseq Mp 0 (Lng Mp - 1)).mp hpMp
    have huniq : ∀ y, nextR Mp 0 y (Lng Mp - 1) = true → y = 0 := by
      intro y hy
      have h1 := huw y hy
      have h2 := huw 0 hnextMp
      omega
    exact parent_eq_of_unique_fseq Mp 0 (Lng Mp - 1) 0 hnextMp huniq
  have hLPMp : lastParent Mp = 0 := by simpa [lastParent, lastIdx] using hparMp
  -- entry 転送
  have he0 : entry Mp 1 0 = entry N 1 j0 := by
    have hh := entry_seg N j0 (Lng N - 1) 1 0 (by rw [← hMpdef]; exact hMpL)
    rw [← hMpdef] at hh; rw [hh, Nat.add_zero]
  have he1 : entry Mp 1 (Lng Mp - 1) = entry N 1 (Lng N - 1) := by
    have hh := entry_seg N j0 (Lng N - 1) 1 (Lng Mp - 1) (by rw [← hMpdef]; exact hMpLm1)
    rw [← hMpdef] at hh; rw [hh, hidx1]
  -- 目標 (1): `transJm1 Mp = 0`
  refine ⟨?_, ?_⟩
  · have htj0 : transJ0 Mp = 0 := by simpa [transJ0, lastParent, lastIdx] using hparMp
    unfold transJm1
    rw [htj0]
    simp [Adm, adm_zero Mp]
  -- 目標 (2): 条件(I)/(III)/(V) ホスト
  · have hnotA := VE34_base_notCondA N hReg4' hbase
    have hnotV : transCondV N ≠ true := fun h => hnotA (Or.inr (Or.inr h))
    have hbound := row1_last_bound_cs2 N hR hmono hL
    rw [hpar_j0] at hbound
    by_cases hz : entry N 1 (Lng N - 1) = 0
    · -- 条件(I)
      have hI : transCondI Mp = true := by
        simp only [transCondI, lastIdx, hLPMp, Bool.and_eq_true, beq_iff_eq]
        exact ⟨by rw [he1]; exact hz, adm_zero Mp⟩
      rw [hI]; simp
    · -- 条件(III)
      have hpos : 0 < entry N 1 (Lng N - 1) := Nat.pos_of_ne_zero hz
      have hge : entry N 1 (Lng N - 1) ≤ entry N 1 j0 := by
        rcases hbound with hle | heq
        · exact hle
        · exfalso; apply hnotV
          have hV : transCondV N = true := by
            simp only [transCondV, hLPN, lastIdx, Bool.and_eq_true, beq_iff_eq,
              decide_eq_true_eq]
            exact ⟨⟨hpos, heq⟩, by omega⟩
          exact hV
      have hIII : transCondIII Mp = true := by
        simp only [transCondIII, lastIdx, hLPMp, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by rw [he1]; exact hpos, by rw [he1, he0]; exact hge⟩, adm_zero Mp⟩
      rw [hIII]; simp

/-! ## census 用の小補助（Isabelle `bgx_leBT_headV` / `bgx_lastPB` / BT 反射律） -/

/-- `bpHeadT (Dprin v a) = a`。 -/
private theorem bpHeadT_Dprin_cs2 (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

/-- `PB (Dprin v t) = [Dprin v t]`（Isabelle `PB_Dpt_single`）。 -/
private theorem PB_Dprin_single_cs2 (v : ℕ∞) (t : BT) : PB (Dprin v t) = [Dprin v t] := by
  simp [PB, Dprin, untrm]

/-- `leBT` の反射律。 -/
private theorem leBT_refl_cs2 (a : BT) : leBT a a = true := by
  simp only [leBT, beq_self_eq_true, Bool.or_true]

/-- **`leBT_headV_cs2`**（Isabelle `bgx_leBT_headV`）: `D_u 0 ≤_B D_v c ⟹ u ≤ v`。 -/
private theorem leBT_headV_cs2 (u v : ℕ∞) (c : BT)
    (h : leBT (Dprin u BZero) (Dprin v c) = true) : u ≤ v := by
  rw [leBT] at h
  simp only [Dprin, lessBT, lessBPList, lessBP, Bool.or_eq_true, Bool.and_eq_true,
    Bool.false_eq_true, and_false, or_false, decide_eq_true_eq, beq_iff_eq,
    BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true] at h
  rcases h with (hlt | ⟨heq, -⟩) | ⟨heq, -⟩
  · exact le_of_lt hlt
  · exact le_of_eq heq
  · exact le_of_eq heq

/-- **`lastPB_cs2`**（Isabelle `bgx_lastPB`）: 非零 `BT` の body の最終 principal は単一
`Dprin u a` の形で、その頭値は `u`、かつ集合の元。 -/
private theorem lastPB_cs2 (t : BT) (htne : t ≠ BZero) :
    ∃ u a, (PB t).getD ((PB t).length - 1) BZero = Dprin u a ∧
      (PB t).getD ((PB t).length - 1) BZero ∈ PB t ∧
      bpHeadV ((PB t).getD ((PB t).length - 1) BZero) = u := by
  cases t with
  | trm ps =>
    have hpsne : ps ≠ [] := by
      intro h; exact htne (by rw [h]; rfl)
    have hlen : 0 < ps.length := List.length_pos_of_ne_nil hpsne
    have hnlt : ps.length - 1 < ps.length := by omega
    have hPBlen : (PB (BT.trm ps)).length = ps.length := by simp [PB, untrm]
    have hmaplen : ps.length - 1 < (ps.map (fun p => (BT.trm [p]))).length := by
      simp [hnlt]
    obtain ⟨u, a, hpn⟩ : ∃ u a, ps[ps.length - 1] = BP.db u a := by
      rcases hps : ps[ps.length - 1] with ⟨u, a⟩; exact ⟨u, a, rfl⟩
    have hget : (PB (BT.trm ps)).getD ((PB (BT.trm ps)).length - 1) BZero = Dprin u a := by
      rw [hPBlen]
      simp only [PB, untrm]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmaplen, Option.getD_some,
        List.getElem_map, hpn]
      rfl
    refine ⟨u, a, hget, ?_, ?_⟩
    · rw [hget]
      have hmem : ps[ps.length - 1] ∈ ps := List.getElem_mem hnlt
      rw [hpn] at hmem
      simp only [PB, untrm, List.mem_map]
      exact ⟨BP.db u a, hmem, rfl⟩
    · rw [hget]; rfl

/-! ## trunk-host closed form（Isabelle `bgx_trunk_Trans`、`baseU_alltrunk_Trans_RN1` 内の閉形式） -/

/-- **`trunk_Trans_cs2`**（Isabelle `bgx_trunk_Trans`）: 全幹（`TrMax Q = Lng Q - 1`）の簡約単項
ホストは `Trans Q = D_{Q₁,₀}(D_{Q₁,Lng-1} 0)`。`baseU_alltrunk_Trans_RN1` 内部の閉形式の
自己完結コピー。 -/
private theorem trunk_Trans_cs2 (Q : PS) (hR : RTPS Q) (hmono : monoT Q = true)
    (htr : TrMax Q = Lng Q - 1) (hL : 1 < Lng Q) :
    Trans Q = Dprin (entry Q 1 0 : ℕ∞) (Dprin (entry Q 1 (Lng Q - 1) : ℕ∞) BZero) := by
  have hub : entry Q 1 0 < entry Q 1 0 + (Lng Q - 1) := by omega
  have heq : Q = diagSeq (entry Q 1 0) (entry Q 1 0 + (Lng Q - 1)) := by
    apply List.ext_getElem
    · have hbridge : List.length Q = Lng Q := rfl
      simp [diagSeq]
      omega
    · intro i hiQ _
      have hiL : i < Lng Q := hiQ
      obtain ⟨hd0, hd1⟩ := baseU_alltrunk_diag_entry Q i hR hmono htr hiL
      have hQi : Q[i] = (entry Q 0 i, entry Q 1 i) := by
        have h0 : entry Q 0 i = Q[i].1 := by
          simp [entry, List.getElem?_eq_getElem hiL]
        have h1 : entry Q 1 i = Q[i].2 := by
          simp [entry, List.getElem?_eq_getElem hiL]
        rw [h0, h1]
      rw [hQi, hd0, hd1]
      simp [diagSeq, List.getElem_map, List.getElem_range']
  have hlast : entry Q 1 (Lng Q - 1) = entry Q 1 0 + (Lng Q - 1) :=
    (baseU_alltrunk_diag_entry Q (Lng Q - 1) hR hmono htr (by omega)).2
  rw [hlast]
  conv_lhs => rw [heq]
  exact diagSeq_Trans (entry Q 1 0) (entry Q 1 0 + (Lng Q - 1)) hub

/-! ## head edge / gtN / LastStep 最小性（Isabelle `bgx_headedge` / `bfx_gtN` /
`vgx_LastStep_elsecase`；`8.2-condIIIV-headeq0-close` の private 双子を `_cs2` で再導出） -/

/-- Isabelle `a1_FN_hasParent`: 枝 first node は row-0 に親を持つ。 -/
private theorem a1_FN_hasParent_cs2 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    hasParent M 0 ((FirstNodes M).getD J 0) = true := by
  have htb := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have hbr : Br M = [] := by simp [Br, heq]
    rw [hbr] at hJ; simp at hJ
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by simp [Br, hne]
  have hJQ : J ≤ (P (seg M (TrMax M + 1) (Lng M - 1))).length - 1 := by
    rw [← hBr]; omega
  have hn := mono_slice_next M (TrMax M + 1) J hM hmono (by omega) (by omega) hJQ
  have hfn := FirstNodes_getD M J hJ
  rw [hfn, hBr]
  exact hn.1

/-- Isabelle `a1_FN_lt`: 枝 first node は範囲内 `< Lng M`。 -/
private theorem a1_FN_lt_cs2 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 < Lng M := by
  have hnx := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn0 : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using hnx
  have h := hn0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- **`headEdge_cs2`**（Isabelle `bgx_headedge`）: 各枝 `J` で頭 joint の row-0 値 + 1 =
first node の row-0 値。 -/
private theorem headEdge_cs2 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (J : ℕ) (hJ : J < (Br M).length) :
    entry M 0 ((Joints M).getD J 0) + 1 = entry M 0 ((FirstNodes M).getD J 0) := by
  have hM : TPS M := RTPS_TPS M hR
  have hcondA : RedCondA M = true := (RTPS_condAB M hR).1
  have hhas : hasParent M 0 ((FirstNodes M).getD J 0) = true :=
    a1_FN_hasParent_cs2 M J hM hmono hJ
  have hlt : (FirstNodes M).getD J 0 < Lng M := a1_FN_lt_cs2 M J hM hmono hJ
  have hedge := RedCondA_apply M hcondA 0 ((FirstNodes M).getD J 0) (by omega) hlt hhas
  rw [Joints_getD M J hJ]
  exact hedge

/-- **`gtN_cs2`**（Isabelle `bfx_gtN`）: BASE run ホストで最終枝頭は狭義ガード
（row-1 < row-0）。 -/
private theorem gtN_cs2 (N : PS) (hR : RTPS N) (hBrne : Br N ≠ [])
    (hguard : entry N 1 (VEj1p N) < entry N 0 (VEj1p N)) :
    entry ((Br N).getD ((Br N).length - 1) []) 1 0
      < entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
  have hM : TPS N := RTPS_TPS N hR
  have hJ1lt : (Br N).length - 1 < (Br N).length := by
    have := List.length_pos_of_ne_nil hBrne; omega
  have h0 : entry N 0 ((FirstNodes N).getD ((Br N).length - 1) 0)
      = entry ((Br N).getD ((Br N).length - 1) []) 0 0 :=
    entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1lt
  have h1 : entry N 1 ((FirstNodes N).getD ((Br N).length - 1) 0)
      = entry ((Br N).getD ((Br N).length - 1) []) 1 0 :=
    entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 1 hM hJ1lt
  rw [← h0, ← h1]
  simpa only [VEj1p] using hguard

/-- **`LastStep_find_min_cs2`**（Isabelle `vgx_LastStep_elsecase` の全域版最小性）: 非対角
ガード下で `k < LastStep N` の枝 `k` は `S`-述語を満たさない。 -/
private theorem LastStep_find_min_cs2 (M : PS) (hBrne : Br M ≠ [])
    (hnd : entry ((Br M).getD ((Br M).length - 1) []) 0 0
         ≠ entry ((Br M).getD ((Br M).length - 1) []) 1 0)
    (k : ℕ) (hk : k < LastStep M) :
    ¬ (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0
       ∧ entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0) := by
  have hLpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br M).length ≠ 0 := by omega
  rintro ⟨heq0, hlt0⟩
  have hpk : (decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0)
             && decide (entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨heq0, hlt0⟩
  have hLSval : LastStep M
      = ((List.range (Br M).length).find? (fun J =>
          decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
          decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0))).getD
            ((Br M).length - 1) := by
    unfold LastStep
    simp only [hL, if_false]
    split
    · next heq => exact absurd heq hnd
    · rfl
  rw [hLSval] at hk
  cases hfind : (List.range (Br M).length).find? (fun J =>
      decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
      decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) with
  | none =>
      simp only [hfind, Option.getD_none] at hk
      have hkmem : k ∈ List.range (Br M).length := List.mem_range.mpr (by omega)
      exact (List.find?_eq_none.mp hfind) k hkmem hpk
  | some c =>
      simp only [hfind, Option.getD_some] at hk
      have hf' : (List.range' 0 (Br M).length).find? (fun J =>
          decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
          decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) = some c := by
        simpa using hfind
      have hmin := (List.find?_range'_eq_some.mp hf').2.2 k (Nat.zero_le k) hk
      rw [hpk] at hmin
      simp at hmin

/-! ## `BgxNotleftRun0_bf` の census core（Isabelle `bgx_notleft_run0` の `main`） -/

/-- **`notleft_main_cs2`**（Isabelle `bgx_notleft_run0` の `main`）: run-base BASE ホストで、
`transT2 N` の全 principal 成分の頭値に狭義下界 `> N₁,j₀'` がある。trunk corner
（`trunk_Trans_cs2`）と branching の 3-clause dispatch（census `subexpr_component_strongmono`
＋ head-edge 比較 ＋ `LastStep` 最小性）で証明する。 -/
private theorem notleft_main_cs2 (N : PS) (hReg4 : VE34Reg4 N)
    (hdesc : descendingB (Br N) = true) (hbase : VEj1p N = Lng N - 1)
    (hdeep : TrMax N + 2 < Lng N) (hr0 : LastStep N = (Br N).length - 1) :
    ∃ e : ℕ, entry N 1 (transJ0 N) < e ∧
      ∀ p ∈ PB (transT2 N), leBT (Dprin (e : ℕ∞) BZero) p = true := by
  have hR4 := hReg4
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, hj0pos, hj0lt⟩ := hR4
  have hM : TPS N := RTPS_TPS N hR
  set j0 := (Joints N).getD ((Br N).length - 1) 0 with hj0def
  have hj0eq : transJ0 N = j0 := by rw [hj0def]; exact VE34_base_transJ0 N hReg4 hbase
  have htrbd : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have htrne : TrMax N ≠ Lng N - 1 := fun h => hBrne (by simp [Br, h])
  have htrlt : TrMax N < Lng N - 1 := by omega
  have hL : 1 < Lng N := by omega
  have hcondA : RedCondA N = true := (RTPS_condAB N hR).1
  have hdiag : entry N 0 0 = entry N 1 0 := RTPS_mono_head_eq N hR hmono
  have hoffs : ∀ j, j ≤ TrMax N →
      entry N 0 j = entry N 0 0 + j ∧ entry N 1 j = entry N 1 0 + j :=
    fun j hj => trunk_entries_offset N hM hcondA j hj
  have he1j0 : entry N 1 j0 = entry N 1 0 + j0 := (hoffs j0 (le_of_lt hj0lt)).2
  -- Q = Pred N の共通データ
  have hLQ : Lng (Pred N) = Lng N - 1 := length_Pred N hL
  have hLpN : 1 < Lng (Pred N) := by omega
  have hQR : RTPS (Pred N) := RTPS_Pred N hR
  have hQT : TPS (Pred N) := RTPS_TPS (Pred N) hQR
  have hND : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
  have hQD : DTPS (Pred N) := descending_Br_Pred N hND hBrne hLpN
  obtain ⟨_, hmonoQ, _⟩ := (DTPS_iff (Pred N)).mp hQD
  have hTrQ : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL htrne
  have hentryQ : ∀ i j, j < Lng N - 1 → entry (Pred N) i j = entry N i j :=
    fun i j hj => entry_Pred N i j hj
  -- t2Q : transT2 N = bpHeadT (Trans (Pred N))
  have hAdm0 : transJm1 N = 0 := VE34_base_Adm0 N hReg4 hbase
  have hleR00 : leR N 0 0 (Lng N - 1) = true := by
    have hh := hmono; simp only [monoT, Bool.and_eq_true] at hh; exact hh.2
  have hMk0 : Marked N 0 := ⟨hM, adm_zero N, hleR00⟩
  have hMkP0 : Marked (Pred N) 0 := Marked_Pred N 0 hM hL hMk0 (by omega)
  have hc1 : transC1 N = Trans (Pred N) := by
    show Mark (Pred N) (transJm1 N) = Trans (Pred N)
    rw [hAdm0]; exact Mark_zero_eq_Trans (Pred N) hQR hMkP0
  have ht2Q : transT2 N = bpHeadT (Trans (Pred N)) := by
    show bpHeadT (transC1 N) = _; rw [hc1]
  -- MAIN: Br (Pred N) の有無で分岐
  by_cases hBrQ : Br (Pred N) = []
  · -- trunk corner
    have htrunkQ : TrMax (Pred N) = Lng (Pred N) - 1 := by
      by_contra hcontra
      have hBrform : Br (Pred N)
          = P (seg (Pred N) (TrMax (Pred N) + 1) (Lng (Pred N) - 1)) := by
        simp only [Br, if_neg hcontra]
      rw [hBrform] at hBrQ
      exact P_nonempty _ hBrQ
    have hLQ3 : 3 ≤ Lng (Pred N) := by rw [hLQ]; omega
    have hLQgt1 : 1 < Lng (Pred N) := by omega
    have hTF : Trans (Pred N) = Dprin (entry (Pred N) 1 0 : ℕ∞)
        (Dprin (entry (Pred N) 1 (Lng (Pred N) - 1) : ℕ∞) BZero) :=
      trunk_Trans_cs2 (Pred N) hQR hmonoQ htrunkQ hLQgt1
    have ht2form : transT2 N = Dprin (entry (Pred N) 1 (Lng (Pred N) - 1) : ℕ∞) BZero := by
      rw [ht2Q, hTF, bpHeadT_Dprin_cs2]
    have hcondAQ : RedCondA (Pred N) = true := (RTPS_condAB (Pred N) hQR).1
    have he1lastQ : entry (Pred N) 1 (Lng (Pred N) - 1)
        = entry (Pred N) 1 0 + (Lng (Pred N) - 1) :=
      (trunk_entries_offset (Pred N) hQT hcondAQ (Lng (Pred N) - 1) (le_of_eq htrunkQ.symm)).2
    have he10Q : entry (Pred N) 1 0 = entry N 1 0 := entry_Pred_zero N 1 hL
    have hLQm1_eq : Lng (Pred N) - 1 = TrMax N := by rw [← htrunkQ, hTrQ]
    have helt : entry N 1 j0 < entry (Pred N) 1 (Lng (Pred N) - 1) := by
      rw [he1lastQ, he10Q, hLQm1_eq, he1j0]; omega
    refine ⟨entry (Pred N) 1 (Lng (Pred N) - 1), ?_, ?_⟩
    · rw [hj0eq]; exact helt
    · intro p hp
      rw [ht2form, PB_Dprin_single_cs2, List.mem_singleton] at hp
      subst hp
      exact leBT_refl_cs2 _
  · -- branching Q : strong-monomiality census
    have hBrLenP : (Br (Pred N)).length = (Br N).length - 1 :=
      BrLen_Pred_base_pv N hM hBrne hL htrne hbase
    have hBrNpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
    have hBrQpos : 0 < (Br (Pred N)).length := List.length_pos_of_ne_nil hBrQ
    have hBrN2 : 2 ≤ (Br N).length := by omega
    set Jp := (Br (Pred N)).length - 1 with hJpdef
    have hJmBr : Jp < (Br (Pred N)).length := by omega
    have hJpN : Jp = (Br N).length - 2 := by omega
    have hJpltBrN : Jp < (Br N).length := by omega
    have hjqQ : (Joints (Pred N)).getD Jp 0 = (Joints N).getD Jp 0 :=
      Joints_Pred_core N hM hmono hL htrne Jp hJmBr
    have hfqQ : (FirstNodes (Pred N)).getD Jp 0 = (FirstNodes N).getD Jp 0 :=
      FirstNodes_Pred_core N hM hL htrne Jp hJmBr
    have hgeomp := FirstNodes_TrMax_Joints N Jp hM hmono hJpltBrN
    set jq := (Joints N).getD Jp 0 with hjqdef
    set fq := (FirstNodes N).getD Jp 0 with hfqdef
    -- fq < Lng N - 1
    have hfqlt : fq < Lng N - 1 := by
      have h1 : (FirstNodes (Pred N)).getD Jp 0 < Lng (Pred N) :=
        a1_FN_lt_cs2 (Pred N) Jp hQT hmonoQ hJmBr
      rw [hfqQ, hLQ] at h1; exact h1
    have hjqlt : jq < Lng N - 1 := by have := hgeomp.1; omega
    -- head edges
    have hhe_p : entry N 0 jq + 1 = entry N 0 fq := by
      have h := headEdge_cs2 N hR hmono Jp hJpltBrN
      rw [← hjqdef, ← hfqdef] at h; exact h
    have hJ1Br : (Br N).length - 1 < (Br N).length := by omega
    have hfn1 : (FirstNodes N).getD ((Br N).length - 1) 0 = Lng N - 1 := by
      simpa only [VEj1p] using hbase
    have hhe_1 : entry N 0 j0 + 1 = entry N 0 (Lng N - 1) := by
      have h := headEdge_cs2 N hR hmono ((Br N).length - 1) hJ1Br
      rw [hfn1] at h; rwa [← hj0def] at h
    -- branch-head transports
    have hbrhd_p0 : entry N 0 fq = entry ((Br N).getD Jp []) 0 0 := by
      have h := entry_FirstNodes_eq_component_mr N Jp 0 hM hJpltBrN
      rw [← hfqdef] at h; exact h
    have hbrhd_p1 : entry N 1 fq = entry ((Br N).getD Jp []) 1 0 := by
      have h := entry_FirstNodes_eq_component_mr N Jp 1 hM hJpltBrN
      rw [← hfqdef] at h; exact h
    have hbrhd_10 : entry N 0 (Lng N - 1)
        = entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
      have h := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1Br
      rw [hfn1] at h; exact h
    have hdeschd : entry ((Br N).getD ((Br N).length - 1) []) 0 0
        ≤ entry ((Br N).getD Jp []) 0 0 := by
      have hcd := (descendingB_iff (Br N)).mp hdesc Jp ((Br N).length - 1) (by omega) hJ1Br
      exact ((cdomB_iff _ _).mp hcd).1
    have hjqge : j0 ≤ jq := by
      have hh1 : entry N 0 (Lng N - 1) ≤ entry N 0 fq := by
        rw [hbrhd_10, hbrhd_p0]; exact hdeschd
      have hh2 : entry N 0 j0 ≤ entry N 0 jq := by
        have := hhe_p; have := hhe_1; omega
      have hoj0 := (hoffs j0 (le_of_lt hj0lt)).1
      have hojq := (hoffs jq hgeomp.1).1
      omega
    have hjqpos : 0 < jq := by omega
    -- census on Q
    have hcen := subexpr_component_strongmono sxsm_factA_uncond_holds sxsm_factB_holds
        (Pred N) hQD hBrQ
    obtain ⟨t', hprops, -⟩ := hcen
    obtain ⟨hcenA, hcen2, hcen3, hcen4⟩ := hprops
    rw [← hJpdef] at hcen2 hcen3 hcen4
    have ht'eq : transT2 N = t' := by rw [ht2Q, hcenA, bpHeadT_Dprin_cs2]
    have heQfq0 : entry (Pred N) 0 fq = entry N 0 fq := hentryQ 0 fq (by omega)
    have heQfq1 : entry (Pred N) 1 fq = entry N 1 fq := hentryQ 1 fq (by omega)
    have heQjq1 : entry (Pred N) 1 jq = entry N 1 jq := hentryQ 1 jq (by omega)
    have heQtr1 : entry (Pred N) 1 (TrMax N) = entry N 1 (TrMax N) :=
      hentryQ 1 (TrMax N) (by omega)
    by_cases hjqTr : jq = TrMax N
    · -- clause (4)
      have hfire : 0 < (Joints (Pred N)).getD Jp 0
          ∧ (Joints (Pred N)).getD Jp 0 = TrMax (Pred N) := by
        rw [hjqQ, hTrQ]; exact ⟨hjqpos, hjqTr⟩
      have hbnd := hcen4 hfire
      refine ⟨entry N 1 (TrMax N), ?_, ?_⟩
      · rw [hj0eq, he1j0, (hoffs (TrMax N) (le_refl _)).2]; omega
      · intro p hp
        rw [ht'eq] at hp
        have hb := hbnd p hp
        rw [hTrQ, heQtr1] at hb; exact hb
    · have hjqTr' : jq < TrMax N := lt_of_le_of_ne hgeomp.1 hjqTr
      have hcoeff : entry N 1 fq ≤ entry N 0 fq := reduced_coeff N hR fq (by omega)
      by_cases hheq : entry N 0 fq = entry N 1 fq
      · -- clause (2), head-equal
        have hfire : (Joints (Pred N)).getD Jp 0 = 0
            ∨ entry (Pred N) 0 ((FirstNodes (Pred N)).getD Jp 0)
                = entry (Pred N) 1 ((FirstNodes (Pred N)).getD Jp 0) := by
          right; rw [hfqQ, heQfq0, heQfq1]; exact hheq
        have hbnd := hcen2 hfire
        refine ⟨entry N 1 fq, ?_, ?_⟩
        · rw [hj0eq]
          have h1 : entry N 1 fq = entry N 0 jq + 1 := by omega
          have h2 : entry N 0 jq = entry N 0 0 + jq := (hoffs jq hgeomp.1).1
          have h3 : entry N 1 j0 = entry N 1 0 + j0 := he1j0
          rw [h1, h2]; omega
        · intro p hp
          rw [ht'eq] at hp
          have hb := hbnd p hp
          rw [hfqQ, heQfq1] at hb; exact hb
      · -- clause (3)
        have hgt : entry N 1 fq < entry N 0 fq :=
          lt_of_le_of_ne hcoeff (fun h => hheq h.symm)
        have hjqgt : j0 < jq := by
          rcases lt_or_eq_of_le hjqge with h | h
          · exact h
          · exfalso
            have hjqeq : jq = j0 := h.symm
            have hnd : entry ((Br N).getD ((Br N).length - 1) []) 0 0
                ≠ entry ((Br N).getD ((Br N).length - 1) []) 1 0 := by
              have hg := gtN_cs2 N hR hBrne hguard; omega
            have hdeq : entry ((Br N).getD ((Br N).length - 1) []) 0 0
                = entry ((Br N).getD Jp []) 0 0 := by
              rw [← hbrhd_10, ← hbrhd_p0]
              have hp' : entry N 0 j0 + 1 = entry N 0 fq := by rw [← hjqeq]; exact hhe_p
              omega
            have hgrd : entry ((Br N).getD Jp []) 1 0 < entry ((Br N).getD Jp []) 0 0 := by
              rw [← hbrhd_p0, ← hbrhd_p1]; exact hgt
            have hJpLS : Jp < LastStep N := by rw [hr0]; omega
            exact LastStep_find_min_cs2 N hBrne hnd Jp hJpLS ⟨hdeq, hgrd⟩
        have hfire : 0 < (Joints (Pred N)).getD Jp 0
            ∧ (Joints (Pred N)).getD Jp 0 < TrMax (Pred N)
            ∧ entry (Pred N) 1 ((FirstNodes (Pred N)).getD Jp 0)
                < entry (Pred N) 0 ((FirstNodes (Pred N)).getD Jp 0) := by
          rw [hjqQ, hfqQ, hTrQ, heQfq0, heQfq1]
          exact ⟨hjqpos, hjqTr', hgt⟩
        have hbnd := hcen3 hfire
        refine ⟨entry N 1 jq, ?_, ?_⟩
        · rw [hj0eq, he1j0, (hoffs jq hgeomp.1).2]; omega
        · intro p hp
          rw [ht'eq] at hp
          have hb := hbnd p hp
          rw [hjqQ, heQjq1] at hb; exact hb

/-- **`BgxNotleftRun0_cs2`**: `BgxNotleftRun0_bf` を無条件討伐。census core
`notleft_main_cs2` の存在量化から最終 principal の頭値抽出（`lastPB_cs2` /
`leBT_headV_cs2`）で結論する。 -/
theorem BgxNotleftRun0_cs2 : BgxNotleftRun0_bf := by
  intro N hRegD hbase hdeep hr0
  obtain ⟨hReg4, hdesc⟩ := hRegD
  have hR4 := hReg4
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0lt⟩ := hR4
  have hAdm0 : transJm1 N = 0 := VE34_base_Adm0 N hReg4 hbase
  have hj1gt : 1 < Lng N - 1 := VE34_base_j1gt N hReg4 hbase
  have hL : 1 < Lng N := by omega
  have hnotA := VE34_base_notCondA N hReg4 hbase
  have hnotVI : transCondVI N = false := notVI_Adm0 N hR hmono hBrne hj1gt hAdm0
  have ht2ne : transT2 N ≠ BZero := t2ne_notAVI N hR hmono hL hj1gt hnotA hnotVI
  obtain ⟨e, helt, hebnd⟩ := notleft_main_cs2 N hReg4 hdesc hbase hdeep hr0
  obtain ⟨u, a, hlast, hmem, hhead⟩ := lastPB_cs2 (transT2 N) ht2ne
  have hble := hebnd _ hmem
  rw [hlast] at hble
  have hle := leBT_headV_cs2 (e : ℕ∞) u a hble
  rw [hhead]
  intro hcontra
  have hlt : (entry N 1 (transJ0 N) : ℕ∞) < (e : ℕ∞) := by exact_mod_cast helt
  have hcmp : (entry N 1 (transJ0 N) : ℕ∞) < u := lt_of_lt_of_le hlt hle
  rw [hcontra] at hcmp
  exact lt_irrefl _ hcmp

#print axioms BgxMpSliceData_cs2
#print axioms BgxNotleftRun0_cs2

end PSS
