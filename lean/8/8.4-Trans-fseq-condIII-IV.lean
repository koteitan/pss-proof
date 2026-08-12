import «Buchholz-1986».«Buchholz-1986-2.1-order»
import «7».«7.3-Pred-Trans-descend»

/-!
# §8.4 命題（条件(III)か(IV)の下での `Trans` と基本列の交換関係）

- 原文: `tmp/content.md` §8.4。逐語形は `p_8_4_Trans_oper_exchange`
  (isabelle/pss_paper.thy:1909)。原文の主張は、`M ∈ ST_PS ∩ PT_PS`、`n ≥ 1`、
  `j₋₂` の存在（`hasParent M 1 (Lng M - 1)`）、`j₁ > 1`、条件 (III) か (IV) の下で
  (1) `Trans(M[n]) ≤ Trans(M)[n-1]`、(2) `Trans(M[n]) < Trans(M)`、
  (3) `Trans(M)[n-1] < Trans(M[n+1])`。

- 訂正: **A32（§8.4 命題 (1)）は取り下げ済み**（`corrections-old.md:101`）。
  A23（operB 誤読）由来の我々の誤りであり、原文の添字 `n-1` は正確で、
  印字どおり真（真正 ST_PS プールで 579/579）。したがって本ファイルは
  「A32 訂正」を適用しない。Isabelle 側の補題名に残る `_corrected` は
  取り下げ前の名残である（下記参照）。

- Isabelle:
  * 記事逐語形 = `p_8_4_Trans_oper_exchange` (pss_paper.thy:1909, `sorry`)。
  * ミッション指定の雛形 `m_8_4_Trans_oper_exchange_corrected_condIII`
    (layerB/pss_wip.thy:62656) とその中核 `d13x_exchange13_condIII` (同 :62514) は
    **採用しない**。これらは単文字塔 `d13x_T` (同 :62328) に基づくが、後続ラウンドが
    「`d13x_T` の形は誤り（r21b-CONDIV-M refutation 4/57）。base を `transT2 M` に
    した `d4vx_core` の形が正しい」と判定している (同 :78648)。
    実際 `d13x_exchange13_condIII` の付記が主張する `Trans(M)[n-1] < Trans(M[n])` は
    本ファイルの数値監査で **0/39**（偽）＝ 仮定束が空虚。
  * 採用した雛形 = `w84x_exchange13_core` (layerB/pss_wip.thy:79789)。
    `c4cx_condIV_exchange13` の base を一般化した条件非依存エンジンで、
    結論 (1) は `Trans(M[n]) < Trans(M)[n]`、結論 (3) は原文どおり
    `Trans(M)[n-1] < Trans(M[n+1])`。条件 (III)/(IV) 双方に効く
    （エンジンは `transCondIII` を一切使わない。pss_wip.thy:62650 の付記と同旨）。
    補助 = `d4vx_ins`/`d4vx_core` (同 :63756/:63759)、`d4vx_ins_flat` (同 :63767)、
    `d4vx_core_flat` (同 :63783)、`c4cx_d4vx_ins_mono` / `c4cx_d4vx_core_compose` /
    `c4cx_d4vx_core_mono_base`。

- 依存（ビルド済みのみ import）: `Buchholz-1986-2.1-order`（`lessBT_linear_trans`）、
  `7.3-Pred-Trans-descend`（`scbext_lessBT` ＝ 部分表現の不等式の延長性）。

- 数値監査: `python/_e34_audit.py`（A23 訂正後の operB）。真正 ST_PS プールで
  * 原文 (1) `Trans(M[n]) ≤ Trans(M)[n-1]` = 39/39（＝A32 取り下げが正しい）、
  * `d13x_exchange13_condIII` の付記が主張する逆 `Trans(M)[n-1] < Trans(M[n])`
    = **0/39**（＝ d13x 経路の仮定束は空虚）、
  * 移植した (1') `Trans(M[n]) < Trans(M)[n]` = 39/39、原文 (3) = 39/39、
  * `hasParent` 不成立の脚では原文 (3) は **0/27**（＝ `hasParent` は本質的仮定）
    だが `∃k` 形は 18/18。

- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  未移植 brick を 2 本の名前付き `Prop`（`Exch84_*`）として露出し、そこから
  記事逐語形と、`8.7-fseq-descend` の `FseqDesc_exchIII` / `FseqDesc_exchIV` の
  drop-in を証明する。挿入段 `ins` は `d4vx_ins` を「その flat 則」で抽象化して
  あるので、`unflatBT` / `scbimg_image_BT` を移植せずに済んでいる。
-/

namespace PSS

/-! ## 挿入塔（Isabelle `d4vx_core`、挿入段を抽象化した形） -/

/-- Isabelle `d4vx_core s0 ub b0 t k`。挿入段 `d4vx_ins s0 ub b0` を関数 `ins` に
抽象化してある（`d4vx_ins_flat` の結論だけが使われるため）。 -/
def coreTower_e34 (ins : BT → BT) (t : BT) : ℕ → BT
  | 0 => t
  | k + 1 => ins (coreTower_e34 ins t k)

/-- Isabelle `c4cx_d4vx_core_compose`。 -/
private theorem coreTower_compose_e34 (ins : BT → BT) (t : BT) (i : ℕ) :
    ∀ k, coreTower_e34 ins (coreTower_e34 ins t i) k = coreTower_e34 ins t (k + i)
  | 0 => by simp [coreTower_e34]
  | k + 1 => by
      show ins (coreTower_e34 ins (coreTower_e34 ins t i) k) = _
      rw [coreTower_compose_e34 ins t i k]
      have e : k + 1 + i = (k + i) + 1 := by omega
      rw [e]
      rfl

/-! ## `ins` の単調性（`d4vx_ins_flat` ＋ 部分表現の不等式の延長性） -/

/-- Isabelle `c4cx_d4vx_ins_mono`。`ins` の flat 則から `scbext_lessBT` 一発。 -/
private theorem ins_mono_e34 {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) {X Y : BT} (h : lessBT X Y = true) :
    lessBT (ins X) (ins Y) = true := by
  refine scbext_lessBT (s := s0) (b := b0) (cp := .db ub X) (cp' := .db ub Y) ?_ ?_ hb0 ?_
  · rw [hflat X]; rfl
  · rw [hflat Y]; rfl
  · simp [lessBP, h]

/-- Isabelle `c4cx_d4vx_core_mono_base`。 -/
private theorem coreTower_mono_base_e34 {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) {b b' : BT} (h : lessBT b b' = true) :
    ∀ k, lessBT (coreTower_e34 ins b k) (coreTower_e34 ins b' k) = true
  | 0 => h
  | k + 1 => ins_mono_e34 hflat hb0 (coreTower_mono_base_e34 hflat hb0 h k)

/-! ## `<_B` / `≤_B` の小補題 -/

/-- Isabelle `b1x_less_le_trans`。 -/
private theorem lessBT_leBT_trans_e34 {a b c : BT}
    (h1 : lessBT a b = true) (h2 : leBT b c = true) : lessBT a c = true := by
  rcases Bool.or_eq_true _ _ |>.mp h2 with h | h
  · exact lessBT_linear_trans a b c h1 h
  · rw [eq_of_beq h] at h1; exact h1

/-- `0_B <_B D_v a`。 -/
private theorem lessBT_zero_Dprin_e34 (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-! ## 未移植 brick（Isabelle 名 1:1、GREEN-MODULO の仮定） -/

/-- 条件 (III)/(IV) の producer データ。Isabelle `w84x_exchange13_core`
(layerB/pss_wip.thy:79789) の構造仮定 `uv`/`bodyT`/`bodyne`/`dbbody`/`inner`/`k1`/
`mnform`/`base0`/`base1`/`Lbase` を、当の補題が実際に使う形（`d4vx_ins_flat` の
結論＝挿入段の flat 則、`d13x_fseq_condIII` の結論＝`operB` 閉形式、`mnform`、
塔の底 2 事実、`Lbase`）だけに絞って存在量化で束ねたもの。

Isabelle 側では r28 の `w84x_condIII_exchange13_of_sliceregs`
(同 :80238) / `c4cx2_condIV_mnform_of_slice` (同 :78664) が、これを
`regS`/`regSP`/`dbbodyH`/`base0H`/`base1H`/`LbaseH` まで落としている（経験的に 426/426）。 -/
def Exch84_condIIIIV_producer : Prop :=
  ∀ M : PS, STPS M → monoT M = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    hasParent M 1 (Lng M - 1) = true →
    ∃ (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞) (s0 b0 s1 b1 : List Sym),
      -- `d4vx_ins_flat`: 挿入段の flat 則（`b0` は全 `RP`）
      (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) ∧
      (∀ x ∈ b0, x = Sym.rp) ∧
      (∀ x ∈ b1, x = Sym.rp) ∧
      -- `d13x_fseq_condIII` ＋ `d4vx_core_flat`: `operB` 閉形式（`0_B` 種の塔、一段深い）
      (∀ k, flatBT (operB (Trans M) (numBT k))
        = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1) ∧
      -- `mnform`: `M[m]` の閉形式（`A0` 種の塔）
      (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
        = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1) ∧
      -- `base0` / `base1` / `Lbase`
      lessBT (Dprin ub BZero) A0 = true ∧
      lessBT A0 (ins (Dprin ub BZero)) = true ∧
      leBT (Dprin ub BZero) (ins BZero) = true

/-- `hasParent M 1 (Lng M - 1)` が成り立たない条件 (III)/(IV) ホストの脚。

§8.4 の命題は `j₋₂` の存在（`hasParent M 1 (Lng M - 1)`）を仮定するが、
`8.7-fseq-descend` の `FseqDesc_exchIII` / `FseqDesc_exchIV` はそれを仮定しない。
真正 ST_PS プールで条件 (III)/(IV) の単項ホスト 250 個のうち **58 個**は
`hasParent M 1 (Lng M - 1)` を満たさない（反例 `(1,1)(2,1)(3,1)`、`(2,2)(3,2)(4,2)` 等）
ので、この脚は §8.4 の命題では覆えない。原文 §8 では別経路で処理される部分。

この脚では原文の結論 (3) は **偽**（`python/_e34_audit.py` で 0/27）なので、
本 `Prop` は下流が実際に要る `∃ k` 形だけを主張する（`k = m` で 18/18）。
Isabelle 側にも対応補題は無い（§8.4 の命題自体が `hasParent` を仮定するため）。 -/
def Exch84_condIIIIV_noParent : Prop :=
  ∀ (M : PS) (m : ℕ), STPS M → monoT M = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    hasParent M 1 (Lng M - 1) = false → 1 < m →
    ∃ k, leBT (Trans (oper M m)) (operB (Trans M) (numBT k)) = true

/-! ## エンジン（Isabelle `w84x_exchange13_core`) -/

/-- Isabelle `w84x_exchange13_core` (layerB/pss_wip.thy:79789)。条件非依存。
結論 (1) `Trans(M[n]) <_B Trans(M)[n]` と 結論 (3) `Trans(M)[n-1] <_B Trans(M[n+1])`。 -/
private theorem exchange13_core_e34 {M : PS} {n : ℕ} {ins : BT → BT} {A0 : BT}
    {e3 ub : ℕ∞} {s0 b0 s1 b1 : List Sym}
    (n1 : 1 ≤ n)
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp)
    (hb1 : ∀ x ∈ b1, x = Sym.rp)
    (fO : ∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1)
    (fM : ∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1)
    (base0 : lessBT (Dprin ub BZero) A0 = true)
    (base1 : lessBT A0 (ins (Dprin ub BZero)) = true)
    (Lbase : leBT (Dprin ub BZero) (ins BZero) = true) :
    lessBT (Trans (oper M n)) (operB (Trans M) (numBT n)) = true
      ∧ lessBT (operB (Trans M) (numBT (n - 1))) (Trans (oper M (n + 1))) = true := by
  -- `0_B <_B A0`
  have zA0 : lessBT BZero A0 = true :=
    lessBT_linear_trans _ _ _ (lessBT_zero_Dprin_e34 ub BZero) base0
  -- `A0 <_B X₂ = ins (ins 0_B)`
  have A0lt2 : lessBT A0 (coreTower_e34 ins BZero 2) = true := by
    have step : leBT (ins (Dprin ub BZero)) (ins (ins BZero)) = true := by
      rcases Bool.or_eq_true _ _ |>.mp Lbase with h | h
      · simp [leBT, ins_mono_e34 hflat hb0 h]
      · rw [eq_of_beq h]; simp [leBT]
    exact lessBT_leBT_trans_e34 base1 step
  -- 結論 (1)
  have comp1 : coreTower_e34 ins (coreTower_e34 ins BZero 2) (n - 1)
      = coreTower_e34 ins BZero (n + 1) := by
    rw [coreTower_compose_e34]
    congr 1
    omega
  have AXn : lessBT (coreTower_e34 ins A0 (n - 1))
      (coreTower_e34 ins BZero (n + 1)) = true := by
    have := coreTower_mono_base_e34 hflat hb0 A0lt2 (n - 1)
    rwa [comp1] at this
  have concl1 : lessBT (Trans (oper M n)) (operB (Trans M) (numBT n)) = true := by
    refine scbext_lessBT (s := s1) (b := b1) (cp := .db e3 (coreTower_e34 ins A0 (n - 1)))
      (cp' := .db e3 (coreTower_e34 ins BZero (n + 1))) (fM n n1) (fO n) hb1 ?_
    simp [lessBP, AXn]
  -- 結論 (3)
  have XAn : lessBT (coreTower_e34 ins BZero n) (coreTower_e34 ins A0 n) = true :=
    coreTower_mono_base_e34 hflat hb0 zA0 n
  have concl3 : lessBT (operB (Trans M) (numBT (n - 1)))
      (Trans (oper M (n + 1))) = true := by
    refine scbext_lessBT (s := s1) (b := b1) (cp := .db e3 (coreTower_e34 ins BZero n))
      (cp' := .db e3 (coreTower_e34 ins A0 n)) ?_ ?_ hb1 ?_
    · have h := fO (n - 1)
      have e : n - 1 + 1 = n := by omega
      rwa [e] at h
    · have h := fM (n + 1) (by omega)
      have e : n + 1 - 1 = n := by omega
      rwa [e] at h
    · simp [lessBP, XAn]
  exact ⟨concl1, concl3⟩

/-! ## 記事逐語形 -/

/-- 命題（条件(III)か(IV)の下での `Trans` と基本列の交換関係）(§8.4)。
Isabelle `p_8_4_Trans_oper_exchange` (pss_paper.thy:1909) の結論 (1)/(3)。

原文の (1) は `Trans(M[n]) ≤ Trans(M)[n-1]`（A32 は取り下げ済＝原文どおり真）だが、
採用した Isabelle エンジン `w84x_exchange13_core` が与えるのは
`Trans(M[n]) <_B Trans(M)[n]` である。両者は `Trans(M)[n-1] <_B Trans(M)[n]`
（基本列の狭義増大）を介して前者 ⟹ 後者の関係にあり、原文 (1) の方が強い。
原文 (1) そのものは Isabelle 側でも未証明のため、ここでは移植しない
（下流の `FseqDesc_exch{III,IV}` は `∃ k` 形なので (1)' で足りる）。
結論 (3) は原文どおり。 -/
theorem Trans_oper_exchange (h : Exch84_condIIIIV_producer)
    {M : PS} {n : ℕ} (hST : STPS M) (hmono : monoT M = true)
    (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (n1 : 1 ≤ n) :
    lessBT (Trans (oper M n)) (operB (Trans M) (numBT n)) = true
      ∧ lessBT (operB (Trans M) (numBT (n - 1))) (Trans (oper M (n + 1))) = true := by
  obtain ⟨ins, A0, e3, ub, s0, b0, s1, b1,
    hflat, hb0, hb1, fO, fM, base0, base1, Lbase⟩ := h M hST hmono hj1 hcond hp
  exact exchange13_core_e34 n1 hflat hb0 hb1 fO fM base0 base1 Lbase

/-! ## `8.7-fseq-descend` への drop-in -/

/-- `«8».«8.7-fseq-descend»` の `FseqDesc_exchIII` の本体そのもの。 -/
theorem exch_condIII (h : Exch84_condIIIIV_producer) (hnp : Exch84_condIIIIV_noParent)
    (N : PS) (m : ℕ) (hST : STPS N) (hmono : monoT N = true) (hj1 : 1 < Lng N - 1)
    (hc : transCondIII N = true) (hm : 1 < m) :
    ∃ k, leBT (Trans (oper N m)) (operB (Trans N) (numBT k)) = true := by
  cases hp : hasParent N 1 (Lng N - 1) with
  | false => exact hnp N m hST hmono hj1 (Or.inl hc) hp hm
  | true =>
      refine ⟨m, ?_⟩
      simp [leBT, (Trans_oper_exchange h hST hmono hj1 (Or.inl hc) hp (by omega : 1 ≤ m)).1]

/-- `«8».«8.7-fseq-descend»` の `FseqDesc_exchIV` の本体そのもの。 -/
theorem exch_condIV (h : Exch84_condIIIIV_producer) (hnp : Exch84_condIIIIV_noParent)
    (N : PS) (m : ℕ) (hST : STPS N) (hmono : monoT N = true) (hj1 : 1 < Lng N - 1)
    (hc : transCondIV N = true) (hm : 1 < m) :
    ∃ k, leBT (Trans (oper N m)) (operB (Trans N) (numBT k)) = true := by
  cases hp : hasParent N 1 (Lng N - 1) with
  | false => exact hnp N m hST hmono hj1 (Or.inr hc) hp hm
  | true =>
      refine ⟨m, ?_⟩
      simp [leBT, (Trans_oper_exchange h hST hmono hj1 (Or.inr hc) hp (by omega : 1 ≤ m)).1]

#print axioms Trans_oper_exchange
#print axioms exch_condIII
#print axioms exch_condIV

end PSS
