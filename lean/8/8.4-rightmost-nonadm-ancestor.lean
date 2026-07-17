import «5».«5.1-ancestor-tree»
import «6».«6.2-P-fseq»
import «6».«6.2-mono-ancestor-slice»
import «6».«6.3-adm-slice»
import «6».«6.3-admof-slice»
import «6».«6.4-mono-slice»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.4-P-IdxSum-characterization»
import «6».«6.4-mono-slice-next»
import «6».«6.5-Red-le-core»
import «6».«6.5-Red-IncrFirst-invariance»
import «6».«6.5-Lng-Red-invariance»
import «6».«6.5-Red-welldefined»
import «6».«6.6-ancestor-slice-Red-IncrFirst»
import «6».«6.6-reduced-leftend»
import «6».«6.7-standard-reduced»
import «6».«6.8-standard-slice-Br-descending»
import «7».«7.4-Adm-nextAdm»
import PSS.Adm

/-!
# §8.4 補題（右端の非許容直系先祖の基本性質）

- 原文: `tmp/content.md` L4247（補題本体 L4249、証明 L4251–L4261）
- 訂正: なし。（同節の A30 は「条件(III)～(V)の下での右端の置き換えと `Trans` の
  関係」part (3) の scb 分解、A31 は「条件(III)～(VI)の下での展開規則の基本性質」
  part (5-3) のガード欠落についてで、いずれも本補題とは別命題。本補題は `Trans`
  を一切含まず、原文の主張をそのまま証明できる。）
- Isabelle: `p_8_4_rightmost_nonadm_ancestor` (isabelle/pss_paper.thy:1931) の証明は
  `m_8_4_rightmost_nonadm_ancestor` (isabelle/layerB/pss_wip.thy:40628、約 256 行)。
  引用する補助補題（Isabelle 名 → Lean 名）:
  - `slice_Red_in_RT_PS` → `ancestor_slice_Red_IncrFirst` (6.6)
  - `m_6_5_Lng_Red` → `Lng_Red_invariance` (6.5)
  - `m_6_6_ancestor_slice_Red_IncrFirst` → `ancestor_slice_Red_IncrFirst` (6.6)
  - `m_6_3_admof_slice` → `admof_slice` (6.3)
  - `rcpb_nextR_seg` → `nextR_seg_adm` (6.3)、`adm_le0_seg` → `leR0_seg_adm` (6.3)
  - `adm_Adm_max` → `Adm_max` (6.3)、`adm_TrMax(_succ)`/`nadm_Adm_lt` → 私的再証明
  - `anchor_ge_of_leftmin` → `last_anchor_ge_of_leftmin_68` (6.8)
  - `idxsum_leftend_lmin` → `P_leftend_lmin` (6.4-P-IdxSum-characterization)
  - `idxsum_parent0_unique` → `parent_eq_of_nextR0` (6.4-mono-slice-next) で直接消化
  - `FirstNodes_nth`/`Joints_nth` → `FirstNodes_getD`/`Joints_getD` (6.4)
  - `poper_nextR_imp_le0` → `nextR0_leR` (6.4-FirstNodes-Joints-mono)
  - `le0_leftmin_ancestor_ge` (pss_mechanized.thy:27144) → 私的再証明（`_rna`）
- 依存: `6.6-ancestor-slice-Red-IncrFirst`、`6.8-standard-slice-Br-descending`
  （左端最小 pincer）、`6.4-FirstNodes-TrMax-Joints`、`6.3-adm-slice`/`6.3-admof-slice`、
  `7.4-Adm-nextAdm`（`adm_row1_ancestry`/`row1_implies_row0`）、`5.1-ancestor-tree`
- 状態: ✅ 証明済（sorry 0、仮定 0、公理 `[propext, Classical.choice, Quot.sound]`）

仮定について: 原文の `M ∈ ST_PS ∩ PT_PS` は `hst : STPS M` と
`hmono : monoT M = true` に写す（`PT_PS = T_PS ∩ monoT` で、`T_PS` は
`STPS → RTPS → TPS` から回収されるので新たな内容は `monoT` のみ）。
**`hmono` は実際には使わない**（unused variable 警告はそのため）。Isabelle 版は
`monoT (Red N)` を `m_8_2_standard_slice_Red_strongmono` 経由で取るが、Lean では
`ancestor_slice_Red_IncrFirst` が `monoT (Red N)` を無条件で同時に返すので
§8.2 を経由せず、`monoT M` が不要になった。原文への忠実性のため仮定は残してある
（結果として原文よりわずかに強い主張になっている）。

証明の骨格（Isabelle 版の構造をそのまま移植）:
`N := (M_j)_{j=m₋₁}^{j₁}`（`m₋₁ = Adm_M(m₀)`）と置き `RN := Red N` とする。
`ancestor_slice_Red_IncrFirst` で `N = IncrFirstN k RN` を得て、`nextR`/`le0`/`Adm`/
`TrMax` の `IncrFirstN` 不変性と切片転送を合成した **bridge** で `M` の関係を `RN` に
落とす。`Adm_RN(m₀-m₋₁) = 0`（許容化の切片遺伝性）から `m₀-m₋₁ ≤ TrMax(RN)`、
`Adm(TrMax) = TrMax` から狭義化。`TrMax(RN) < m₁-m₋₁` は幹ステップが
`¬ (1,m₁-1) <^Next_M (1,m₁)` に矛盾することから。最後の枝成分の同定
`FirstNodes(RN)_{J₁} = m₁-m₋₁` は **左端最小 / 最終ブロック開始の pincer**
(`last_anchor_ge_of_leftmin_68` で `≤`、`le0_leftmin_ancestor_ge_rna` で `≥`) による。

`le0_leftmin_ancestor_ge` は Isabelle では converse-rtrancl 帰納だが、Lean の
`le0Aux` は**最後の一歩を剥がす**燃料再帰なので、単段補題
（`nextrel0 M x j`, `a ≤ j`, `a` が左端最小 ⟹ `a ≤ x`）を先に立ててから
燃料帰納で連鎖に持ち上げる。
-/

namespace PSS

/-! ## 支援私的補題 1: 幹の右端の許容性（wip 20575–20714 の再証明） -/

/-- 行 1 の幹ステップは `TrMax M` で必ず破れる。 -/
private theorem nextR1_TrMax_fail_rna (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  cases hst : nextR M 1 (TrMax M) (TrMax M + 1) with
  | false => rfl
  | true =>
      exfalso
      have hall : ∀ j, j < TrMax M + 1 → nextR M 1 j (j + 1) = true := by
        intro j hj
        rcases Nat.lt_or_ge j (TrMax M) with h | h
        · exact TrMax_trunk_step M j hM h
        · have hje : j = TrMax M := by omega
          rw [hje]
          exact hst
      have := le_TrMax_intro_wd M (TrMax M + 1) hM hall
      omega

/-- `TrMax M + 1` は `M` 許容（Isabelle `adm_TrMax_succ`）。 -/
private theorem adm_TrMax_succ_rna (M : PS) (hM : TPS M) :
    adm M (TrMax M + 1) = true := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have htb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hnostep := nextR1_TrMax_fail_rna M hM
  have hno : ¬ Lng M < TrMax M + 1 := by omega
  simp [adm, nadm, hnostep, hno]

/-- `TrMax M` 自身も `M` 許容（Isabelle `adm_TrMax`）。 -/
private theorem adm_TrMax_rna (M : PS) (hM : TPS M) :
    adm M (TrMax M) = true := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have htb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hnostep := nextR1_TrMax_fail_rna M hM
  have hno : ¬ Lng M < TrMax M := by omega
  simp [adm, nadm, hnostep, hno]

/-- 非許容点の許容化は真に下がる（Isabelle `nadm_Adm_lt`）。 -/
private theorem nadm_Adm_lt_rna (M : PS) (j : ℕ) (hna : adm M j = false) :
    Adm M j < j := by
  have hle := Adm_le M j
  have hadm := Adm_adm M j
  rcases Nat.lt_or_ge (Adm M j) j with h | h
  · exact h
  · exfalso
    have heq : Adm M j = j := by omega
    rw [heq] at hadm
    rw [hadm] at hna
    exact absurd hna (by simp)

/-! ## 支援私的補題 2: `IncrFirstN` による `adm`/`Adm` 不変性 -/

private theorem Lng_IncrFirstN_rna (n : ℕ) (M : PS) :
    Lng (IncrFirstN n M) = Lng M := by
  rw [IncrFirstN_eq_map]; simp

private theorem adm_IncrFirstN_rna (n : ℕ) (M : PS) (j : ℕ) :
    adm (IncrFirstN n M) j = adm M j := by
  simp [adm, nadm, nextR_IncrFirstN_ri]

private theorem Adm_IncrFirstN_rna (n : ℕ) (M : PS) (j : ℕ) :
    Adm (IncrFirstN n M) j = Adm M j := by
  simp [Adm, adm_IncrFirstN_rna]

/-! ## 支援私的補題 3: `nextR`/`leR` を `nextrel0`/`le0` に降ろすブリッジ -/

/-- `nextR M 0` を `nextrel0` に降ろす（`nextR` の `if` を先に潰しておかないと
続く `simp only [nextrel0, …]` が `&&` の match を展開できない）。 -/
private theorem nextR0_nextrel0_rna (M : PS) (a k : ℕ) :
    nextR M 0 a k = nextrel0 M a k := by
  simp [nextR]

/-- 同様に `leR M 0` を `le0` に降ろす。 -/
private theorem leR0_le0_rna (M : PS) (a b : ℕ) :
    leR M 0 a b = le0 M a b := by
  simp [leR]

/-! ## 支援私的補題 4: 左端最小点は行 0 の祖先鎖に飛び越されない
（Isabelle `le0_leftmin_ancestor_ge`、pss_mechanized.thy:27144） -/

/-- 単段版。`a` が（狭義に左で）行 0 最小なら、`j ≥ a` への親辺は `a` を跨げない。 -/
private theorem nextrel0_leftmin_step_rna (M : PS) (a x j : ℕ)
    (hmin : ∀ z, z < a → entry M 0 a ≤ entry M 0 z)
    (hstep : nextrel0 M x j = true) (haj : a ≤ j) : a ≤ x := by
  by_contra hlt
  have hlt : x < a := by omega
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hstep
  obtain ⟨⟨⟨⟨-, -⟩, hxj⟩, hex⟩, hmid⟩ := hstep
  have hxa : entry M 0 a ≤ entry M 0 x := hmin x hlt
  rcases Nat.eq_or_lt_of_le haj with heq | hlt2
  · -- `a = j`: `entry M 0 x < entry M 0 j = entry M 0 a ≤ entry M 0 x`
    rw [← heq] at hex
    omega
  · -- `a < j`: `a` は `x` と `j` の中間なので `entry M 0 j ≤ entry M 0 a`
    have hc := hmid a (List.mem_range.mpr hlt2)
    have hja : entry M 0 j ≤ entry M 0 a := by simpa [hlt] using hc
    omega

private theorem le0Aux_leftmin_ancestor_ge_rna (M : PS) (a : ℕ)
    (hmin : ∀ z, z < a → entry M 0 a ≤ entry M 0 z) :
    ∀ (fuel p j : ℕ), le0Aux M fuel p j = true → a ≤ j → a ≤ p := by
  intro fuel
  induction fuel with
  | zero =>
      intro p j h haj
      simp only [le0Aux, beq_iff_eq] at h
      omega
  | succ f ih =>
      intro p j h haj
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        List.mem_range, Bool.and_eq_true] at h
      rcases h with heq | ⟨x, hxj, hstep, hrest⟩
      · omega
      · -- 最後の一歩 `x → j` を剥がす。単段補題で `a ≤ x`、帰納法で `a ≤ p`。
        have hax : a ≤ x := nextrel0_leftmin_step_rna M a x j hmin hstep haj
        exact ih p x hrest hax

/-- `a` が行 0 の左端最小で `a ≤ j` かつ `(0,p) ≤_M (0,j)` ならば `a ≤ p`。 -/
private theorem le0_leftmin_ancestor_ge_rna (M : PS) (a p j : ℕ)
    (hmin : ∀ z, z < a → entry M 0 a ≤ entry M 0 z)
    (hchain : le0 M p j = true) (haj : a ≤ j) : a ≤ p := by
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hchain
  exact le0Aux_leftmin_ancestor_ge_rna M a hmin (Lng M) p j hchain.2 haj

/-! ## 主定理 -/

/-- §8.4 補題（右端の非許容直系先祖の基本性質）（原文 L4247）:

任意の `M ∈ ST_PS ∩ PT_PS` と `m₀, m₁ ∈ ℕ` に対し、`j₁ := Lng(M)-1`、
`m₋₁ := Adm_M(m₀)`、`N := (M_j)_{j=m₋₁}^{j₁}`、`J₁ := Lng(Br(Red(N)))-1` と置くと、
`(0,m₀) <^Next_M (0,m₁) ≤_M (0,j₁)` のもとで `(1,m₁-1) <^Next_M (1,m₁)` でなく
かつ `m₀` が非 `M` 許容ならば、`J₁ ≥ 0` かつ `0 < m₀-m₋₁ < TrMax(Red(N))` かつ
`m₀-m₋₁ = Joints(Red(N))_{J₁}` かつ `FirstNodes(Red(N))_{J₁} = m₁-m₋₁` である。 -/
theorem rightmost_nonadm_ancestor (M : PS) (m0 m1 : ℕ)
    (hst : STPS M) (hmono : monoT M = true)
    (hnx : nextR M 0 m0 m1 = true)
    (hle : leR M 0 m1 (Lng M - 1) = true)
    (hnotnx1 : nextR M 1 (m1 - 1) m1 = false)
    (hnadm : adm M m0 = false) :
    1 ≤ (Br (Red (seg M (Adm M m0) (Lng M - 1)))).length ∧
      (0 < m0 - Adm M m0 ∧
        m0 - Adm M m0 < TrMax (Red (seg M (Adm M m0) (Lng M - 1)))) ∧
      m0 - Adm M m0 =
        (Joints (Red (seg M (Adm M m0) (Lng M - 1)))).getD
          ((Br (Red (seg M (Adm M m0) (Lng M - 1)))).length - 1) 0 ∧
      (FirstNodes (Red (seg M (Adm M m0) (Lng M - 1)))).getD
          ((Br (Red (seg M (Adm M m0) (Lng M - 1)))).length - 1) 0 = m1 - Adm M m0 := by
  have hR : RTPS M := STPS_RTPS M hst
  have hM : TPS M := RTPS_TPS M hR
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  -- `j₁`/`m₋₁` を**不透明な** fvar にする（`set` の let 値は omega が zeta 展開して
  -- 原子がぶれるため、`obtain` で本物の局所変数を作ってから goal を畳む）。
  obtain ⟨j1, hj1def⟩ : ∃ x, x = Lng M - 1 := ⟨_, rfl⟩
  obtain ⟨mm1, hmm1def⟩ : ∃ x, x = Adm M m0 := ⟨_, rfl⟩
  rw [← hj1def] at hle
  rw [← hj1def, ← hmm1def]
  -- 順序の事実
  have hnx0 : nextrel0 M m0 m1 = true := by rw [← nextR0_nextrel0_rna]; exact hnx
  have hm0m1 : m0 < m1 := by
    have h := hnx0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact h.1.1.2
  have hle0m0m1 : leR M 0 m0 m1 = true := nextR0_leR M m0 m1 hnx
  have hm1LM : m1 < Lng M := by
    have h := hle
    rw [leR0_le0_rna] at h
    simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hm1j1 : m1 ≤ j1 := by omega
  have hm0j1 : m0 < j1 := by omega
  -- `m₋₁ = Adm_M(m₀) < m₀`
  have hmm1m0 : mm1 < m0 := by rw [hmm1def]; exact nadm_Adm_lt_rna M m0 hnadm
  have hadmmm1 : adm M mm1 = true := by rw [hmm1def]; exact Adm_adm M m0
  have hmm1j1 : mm1 < j1 := by omega
  -- `(0,m₋₁) ≤_M (0,j₁)`
  have hle1a : leR M 1 mm1 m0 = true := by
    rw [hmm1def]; exact adm_row1_ancestry M m0 hM (by omega)
  have hle0a : leR M 0 mm1 m0 = true := row1_implies_row0 M mm1 m0 hM hle1a
  have hle0mm1m1 : leR M 0 mm1 m1 = true := row0_transitive M mm1 m0 m1 hM hle0a hle0m0m1
  have hleM : leR M 0 mm1 j1 = true := row0_transitive M mm1 m1 j1 hM hle0mm1m1 hle
  -- 切片 `N` とその簡約化 `RN`（`ancestor_slice_Red_IncrFirst` の三点セット）
  have hslice := ancestor_slice_Red_IncrFirst M mm1 j1 hR hmm1j1 (by omega) hleM
  simp only [] at hslice
  obtain ⟨hRedRN, hmonoRN, hsegeq⟩ := hslice
  set N := seg M mm1 j1 with hNdef
  set RN := Red N with hRNdef
  -- `hsegeq : N = IncrFirstN (entry M 0 m₋₁ - entry M 1 m₋₁) RN`
  have hLN : Lng N = j1 + 1 - mm1 := by rw [hNdef]; simp [seg]
  have hNT : TPS N := List.ne_nil_of_length_pos (show 0 < Lng N by omega)
  have hLRN : Lng RN = j1 + 1 - mm1 := by
    rw [hRNdef, Lng_Red_invariance N hNT]; exact hLN
  have hRNT : TPS RN := List.ne_nil_of_length_pos (show 0 < Lng RN by omega)
  -- bridge: `nextR RN i p q = nextR M i (m₋₁+p) (m₋₁+q)`
  have bridge : ∀ i p q : ℕ, p < Lng N → q < Lng N →
      nextR RN i p q = nextR M i (mm1 + p) (mm1 + q) := by
    intro i p q hp hq
    have h1 : nextR RN i p q = nextR N i p q := by
      conv_rhs => rw [hsegeq]
      rw [nextR_IncrFirstN_ri]
    rw [h1, hNdef]
    exact nextR_seg_adm M mm1 j1 i p q (by omega) (by omega)
      (by rw [← hNdef]; exact hp) (by rw [← hNdef]; exact hq)
  have hplt0 : m0 - mm1 < Lng N := by omega
  have hqlt1 : m1 - mm1 < Lng N := by omega
  -- `(0,m₀-m₋₁) <^Next_RN (0,m₁-m₋₁)`
  have hB0 : nextR RN 0 (m0 - mm1) (m1 - mm1) = true := by
    rw [bridge 0 (m0 - mm1) (m1 - mm1) hplt0 hqlt1,
      show mm1 + (m0 - mm1) = m0 by omega, show mm1 + (m1 - mm1) = m1 by omega]
    exact hnx
  -- `(0,m₁-m₋₁) ≤_RN (0,j₁-m₋₁)`
  have hle0RN : leR RN 0 (m1 - mm1) (j1 - mm1) = true := by
    have h1 : leR RN 0 (m1 - mm1) (j1 - mm1) = leR N 0 (m1 - mm1) (j1 - mm1) := by
      conv_rhs => rw [hsegeq]
      rw [leR_IncrFirstN]
    rw [h1, hNdef, leR0_seg_adm M mm1 j1 (m1 - mm1) (j1 - mm1) (by omega) (by omega)
      (by rw [← hNdef]; omega) (by rw [← hNdef]; omega),
      show mm1 + (m1 - mm1) = m1 by omega, show mm1 + (j1 - mm1) = j1 by omega]
    exact hle
  -- `Adm_RN(m₀-m₋₁) = 0`（許容化の切片遺伝性 + `IncrFirstN` 不変性）
  have hAdm0 : Adm RN (m0 - mm1) = 0 := by
    have hAdmN : Adm N (m0 - mm1) = 0 := by
      rw [hNdef, admof_slice M mm1 m0 j1 hM (by omega) hm0j1 (by omega)]
      omega
    have heq : Adm N (m0 - mm1) = Adm RN (m0 - mm1) := by
      rw [hsegeq, Adm_IncrFirstN_rna]
    omega
  -- `0 < m₀-m₋₁ ≤ TrMax(RN)`、そして `Adm(TrMax)=TrMax` から狭義化
  have hjppos : 0 < m0 - mm1 := by omega
  have hjpTr : m0 - mm1 ≤ TrMax RN := by
    by_contra hcon
    have ha : adm RN (TrMax RN + 1) = true := adm_TrMax_succ_rna RN hRNT
    have := Adm_max RN (TrMax RN + 1) (m0 - mm1) ha (by omega)
    omega
  have hjpstrict : m0 - mm1 < TrMax RN := by
    rcases Nat.lt_or_ge (m0 - mm1) (TrMax RN) with h | h
    · exact h
    · exfalso
      have heq : m0 - mm1 = TrMax RN := by omega
      have hadmT : adm RN (TrMax RN) = true := adm_TrMax_rna RN hRNT
      have hAdmT : Adm RN (TrMax RN) = TrMax RN := by simp [Adm, hadmT]
      rw [heq] at hAdm0
      omega
  -- `TrMax(RN) < m₁-m₋₁`: さもなくば幹ステップが `¬ (1,m₁-1) <^Next_M (1,m₁)` に矛盾
  have htlt : TrMax RN < m1 - mm1 := by
    by_contra hcon
    have hstep : nextR RN 1 (m1 - mm1 - 1) (m1 - mm1 - 1 + 1) = true :=
      TrMax_trunk_step RN (m1 - mm1 - 1) hRNT (by omega)
    rw [show m1 - mm1 - 1 + 1 = m1 - mm1 by omega,
      bridge 1 (m1 - mm1 - 1) (m1 - mm1) (by omega) hqlt1,
      show mm1 + (m1 - mm1 - 1) = m1 - 1 by omega,
      show mm1 + (m1 - mm1) = m1 by omega] at hstep
    rw [hstep] at hnotnx1
    exact absurd hnotnx1 (by simp)
  -- (1a) `Br(RN) ≠ []`
  have hm1mm1le : m1 - mm1 ≤ Lng RN - 1 := by omega
  have htrlt : TrMax RN < Lng RN - 1 := by omega
  have hBrPS : Br RN = P (seg RN (TrMax RN + 1) (Lng RN - 1)) := by
    unfold Br
    rw [if_neg (show TrMax RN ≠ Lng RN - 1 by omega)]
  set S := seg RN (TrMax RN + 1) (Lng RN - 1) with hSdef
  have hG1 : 1 ≤ (Br RN).length := by
    rw [hBrPS]; exact List.length_pos_of_ne_nil (P_nonempty S)
  have hJBr : (Br RN).length - 1 < (Br RN).length := by omega
  -- (1c) 最後の枝成分の同定: 左端最小 / 最終ブロック開始の pincer
  have hLS : Lng S = Lng RN - 1 + 1 - (TrMax RN + 1) := by rw [hSdef]; simp [seg]
  have hST : TPS S := List.ne_nil_of_length_pos (show 0 < Lng S by omega)
  obtain ⟨kk, hkkdef⟩ : ∃ x, x = m1 - mm1 - (TrMax RN + 1) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ x, x = (IdxSum (P S)).getD ((P S).length - 1) 0 := ⟨_, rfl⟩
  have htk : TrMax RN + 1 + kk = m1 - mm1 := by omega
  have hkle : kk ≤ Lng S - 1 := by omega
  have hklt : kk < Lng S := by omega
  -- `hB0` の中間条件（`nextrel0` の第 5 成分）
  have hmid : ∀ z, m0 - mm1 < z → z < m1 - mm1 →
      entry RN 0 (m1 - mm1) ≤ entry RN 0 z := by
    have h := hB0
    rw [nextR0_nextrel0_rna] at h
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    intro z hz1 hz2
    have hc := h.2 z (List.mem_range.mpr hz2)
    simpa [hz1] using hc
  -- `kk`（= `m₁-m₋₁` の `S`-局所座標）は `S` の左端最小
  have hlminK : ∀ j, j < kk → entry S 0 kk ≤ entry S 0 j := by
    intro j hj
    have e1 : entry S 0 kk = entry RN 0 (m1 - mm1) := by
      rw [hSdef, entry_seg RN (TrMax RN + 1) (Lng RN - 1) 0 kk
        (by rw [← hSdef]; exact hklt), htk]
    have e2 : entry S 0 j = entry RN 0 (TrMax RN + 1 + j) := by
      rw [hSdef, entry_seg RN (TrMax RN + 1) (Lng RN - 1) 0 j
        (by rw [← hSdef]; omega)]
    rw [e1, e2]
    exact hmid (TrMax RN + 1 + j) (by omega) (by omega)
  have hanchorK : kk ≤ c := by
    rw [hcdef]; exact last_anchor_ge_of_leftmin_68 S kk hST hkle hlminK
  -- `c` 自身も左端最小（`P_leftend_lmin` = Isabelle `idxsum_leftend_lmin`）
  have hPSlen : 0 < (P S).length := List.length_pos_of_ne_nil (P_nonempty S)
  obtain ⟨hcle, hcmin⟩ := P_leftend_lmin S ((P S).length - 1) hST (by omega)
  rw [← hcdef] at hcle hcmin
  -- `kk → Lng S - 1` の行 0 の鎖は `c` を跨げない
  have hle0S : leR S 0 kk (Lng S - 1) = true := by
    rw [hSdef, leR0_seg_adm RN (TrMax RN + 1) (Lng RN - 1) kk (Lng S - 1)
      (by omega) (by omega) (by rw [← hSdef]; exact hklt) (by rw [← hSdef]; omega),
      htk, show TrMax RN + 1 + (Lng S - 1) = j1 - mm1 by omega]
    exact hle0RN
  have hck : c ≤ kk := by
    refine le0_leftmin_ancestor_ge_rna S c kk (Lng S - 1) hcmin ?_ hcle
    rw [← leR0_le0_rna]; exact hle0S
  have hckeq : c = kk := by omega
  have hG4 : (FirstNodes RN).getD ((Br RN).length - 1) 0 = m1 - mm1 := by
    rw [FirstNodes_getD RN ((Br RN).length - 1) hJBr, hBrPS, ← hcdef, hckeq]
    omega
  -- (1b) `Joints(RN)_{J₁} = m₀-m₋₁`（行 0 の親の一意性）
  have hparRN : parent RN 0 (m1 - mm1) = m0 - mm1 :=
    parent_eq_of_nextR0 RN (m0 - mm1) (m1 - mm1) hB0
  have hG2 : m0 - mm1 = (Joints RN).getD ((Br RN).length - 1) 0 := by
    rw [Joints_getD RN ((Br RN).length - 1) hJBr, hG4, hparRN]
  exact ⟨hG1, ⟨hjppos, hjpstrict⟩, hG2, hG4⟩

#print axioms rightmost_nonadm_ancestor

end PSS
