import «8».«8.4-Trans-fseq-condIII-IV»
import «7».«7.2-scb-fseq»
import «7».«7.3-Trans-welldefined»
import «6».«6.7-standard-reduced»

/-!
# §8.4 `Exch84_condIIIIV_producer` の残差縮約（`fO` 消去）

- 原文: `tmp/content.md` §8.4（条件(III)か(IV)の下での `Trans` と基本列の交換関係）。
  逐語形 = `p_8_4_Trans_oper_exchange` (isabelle/pss_paper.thy:1909)。

- Isabelle:
  * producer の唯一の供給元 = `oi5_IIIIV_pkg` (layerC/pss_scratch.thy:1213)。
    `REGS` (`mcx_regS` layerB/pss_wip.thy:94021) / `REGSP`
    (`slx37_regSP_uncond` 同 :97329) / `RUN` (`wgx37_m0run_of_e1ge` 同 :96930 ＋
    `e1x_e1ge_uncond` 同 :97869) を discharge した上で `cpx_condIII_mnform`
    (同 :98605) を呼び、底 2 事実を `crx_base0_of_run` (同 :88555) /
    `crx_base1_of_nest` (同 :88419)（condIV は `cnv_base0_of_run` 同 :102029 /
    `cnv_base1_of_nest` 同 :101903）で出す。
  * ミッションが挙げた `w84x_condIII_exchange13_of_sliceregs` (同 :80238) /
    `c4cx2_condIV_mnform_of_slice` (同 :78664) は **同じ束の別ルート**（前者は
    `regS`/`regSP`/`dbbodyH`/`base0H`/`base1H`/`LbaseH` を名前付き残差として
    引きずる版、後者は `oi5` が使えない **admeq 付き condIV** 脚の記事ルート）。
  * `d13x_*` (同 :62328/:62514/:62656) は仮定束が空虚で **RETRACTED**（同 :78648）。
    本ファイルは経由しない。

- 本ファイルの内容: `Exch84_condIIIIV_producer`
  («8».«8.4-Trans-fseq-condIII-IV») を、**`oi5_IIIIV_pkg` の出力そのもの**に
  1:1 対応する `Exch84_condIIIIV_slicepkg` へ縮約する。既存の
  «8».«8.4-exch84-props» の `Exch84_condIIIIV_pkg` との差は 2 点:
  1. **`fO`（`operB (Trans M) (numBT k)` の閉形式、`∀k`）を残差から除去**した。
     Isabelle 側で `fO` を組むのは `oi5_IIIIV_pkg` の**使用側**（`d13x_fseq_condIII`
     ＋`d4vx_core_flat`）であって pkg 自身ではない。Lean では
     `scb_fseq_kind1` («7».«7.2-scb-fseq»、原文 §7.2(2) 一般形) が
     `k1`＋`inner` から直接 `fO` を出すので、残差に持つ必要が無い。
     残差は `oi5` が実際に出す `k1` (`scb_kind1`) ＋ `inner` (`scb_decomp`) になる。
  2. **`Trans M ∈ T_B` を残差から除去**した（`Trans_mem_T_B` ＋ `STPS_RTPS`）。
  底 2 事実は `oi5` どおり base0 `D_{v₁-1} 0_B <_B A₀` / base1' `A₀ <_B ins 0_B`
  のみ（producer 側の `base1`/`Lbase` は本ファイルが `ins` 単調性と推移律で作る＝
  Isabelle の `y3h_LbaseH_uncond` scratch:15342 に相当）。
  挿入段 `ins` は移植先ファイルと同じく `d4vx_ins` (同 :63756) を
  「その flat 則」(`d4vx_ins_flat` 同 :63767) で抽象化してあるので、
  `unflatBT` を移植せずに済む。塔の flat 則 (`d4vx_core_flat` 同 :63783) は
  `coreTower_zero_flat_ep` として hflat から帰納で出す。

- 依存（すべてビルド済み・committed）: «8».«8.4-Trans-fseq-condIII-IV»
  （`Exch84_condIIIIV_producer` の Prop 本体・`coreTower_e34`・推移的に
  `lessBT_linear_trans`）、«7».«7.2-scb-fseq»（`scb_fseq_kind1`）、
  «7».«7.3-Trans-welldefined»（`Trans_mem_T_B`）、
  «6».«6.7-standard-reduced»（`STPS_RTPS`）。

- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  **`Exch84_condIIIIV_producer` は無条件には閉じていない**（`props_closed` は空）。
  `Exch84_condIIIIV_slicepkg` の中身（＝`cpx_condIII_mnform` 系）は Isabelle 側で
  1000 補題規模の corpus であり、1 wave では移植不能。本ファイルはその境界を
  Isabelle の `oi5_IIIIV_pkg` に正確に合わせるところまでを担当する。
-/

namespace PSS

/-! ## 1. 小補題（移植先ファイルの private 版の再掲、suffix `_ep`） -/

/-- Isabelle `b1x_less_le_trans`。 -/
private theorem lessBT_leBT_trans_ep {a b c : BT}
    (h1 : lessBT a b = true) (h2 : leBT b c = true) : lessBT a c = true := by
  rcases Bool.or_eq_true _ _ |>.mp h2 with h | h
  · exact lessBT_linear_trans a b c h1 h
  · rw [eq_of_beq h] at h1; exact h1

/-- `0_B <_B D_v a`。 -/
private theorem lessBT_zero_Dprin_ep (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-- Isabelle `c4cx_d4vx_ins_mono`。`ins` の flat 則から `scbext_lessBT` 一発。 -/
private theorem ins_mono_ep {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) {X Y : BT} (h : lessBT X Y = true) :
    lessBT (ins X) (ins Y) = true := by
  refine scbext_lessBT (s := s0) (b := b0) (cp := .db ub X) (cp' := .db ub Y) ?_ ?_ hb0 ?_
  · rw [hflat X]; rfl
  · rw [hflat Y]; rfl
  · simp [lessBP, h]

/-- «7».«7.2-scb-fseq» の private `flatten_replicate_snoc` の再掲。 -/
private theorem flatten_replicate_snoc_ep {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate (n + 1) xs) =
      List.flatten (List.replicate n xs) ++ xs := by
  rw [List.replicate_add, List.flatten_append]
  simp

/-! ## 2. `0_B` 種の塔の flat 則（Isabelle `d4vx_core_flat` の `0_B` 底の場合） -/

/-- `coreTower_e34 ins 0_B j` の flat 形。`hflat`（＝`d4vx_ins_flat`）だけから帰納で出る。 -/
private theorem coreTower_zero_flat_ep {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) :
    ∀ j, flatBT (coreTower_e34 ins BZero j)
      = List.flatten (List.replicate j (s0 ++ [Sym.dsym ub]))
        ++ [Sym.zero] ++ List.flatten (List.replicate j b0)
  | 0 => by simp [coreTower_e34, BZero, flatBT]
  | j + 1 => by
      show flatBT (ins (coreTower_e34 ins BZero j)) = _
      rw [hflat (coreTower_e34 ins BZero j), coreTower_zero_flat_ep hflat j,
        flatten_replicate_snoc_ep b0 j, List.replicate_succ, List.flatten_cons]
      simp [List.append_assoc]

/-! ## 3. 残差（Isabelle `oi5_IIIIV_pkg` の出力そのもの） -/

/-- Isabelle `oi5_IIIIV_pkg` (layerC/pss_scratch.thy:1213) の `obtains` 節を
Lean の語彙に 1:1 で写したもの。

Isabelle の記号との対応（`?v1 = entry M 1 (Lng M - 1)`、`?ub = ?v1 - 1`、
`?e3 = entry M 1 (s84x_jm3 M)`、`?body = bpHeadT (Trans (s84x_N M))`、
`?A0 = bpHeadT (Trans (Pred (s84x_N M)))`、`s0 = u1 @ u2`、`b0 = v2 @ w1`）:

| Isabelle | 本 Prop |
|---|---|
| `\<forall>x \<in> set b0. x = RP` | `hb0` |
| `\<forall>x \<in> set b1. x = RP` | `hb1` |
| `scb_decomp ?body s0 (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0` | `hinner` |
| `scb_kind1 (Trans M) s1 (flatBT (Dpt (enat ?e3) ?body)) b1` | `hk1` |
| `MNall` (`cpx_condIII_mnform` の `mnform`) | `hmn` |
| `lessBT (Dpt (enat ?ub) 0\<^sub>B) ?A0` | `base0` |
| `lessBT ?A0 (d4vx_ins s0 ?ub b0 0\<^sub>B)` | `base1'` |

`ins` は `d4vx_ins s0 ?ub b0` を `d4vx_ins_flat` (pss_wip.thy:63767) の結論で
抽象化したもの（`hflat`）。Isabelle の `?A0 \<in> T_B` は producer 側が使わないので落とした。 -/
def Exch84_condIIIIV_slicepkg : Prop :=
  ∀ M : PS, STPS M → monoT M = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    hasParent M 1 (Lng M - 1) = true →
    ∃ (ins : BT → BT) (A0 body : BT) (e3 v1 : ℕ) (s0 b0 s1 b1 : List Sym),
      -- `d4vx_ins_flat`: 挿入段の flat 則（`b0` は全 `RP`）
      (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ((v1 - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) ∧
      (∀ x ∈ b0, x = Sym.rp) ∧
      (∀ x ∈ b1, x = Sym.rp) ∧
      -- `inner`: 挿入位置の scb 分解（穴 = `D_{v₁} 0_B`）
      scb_decomp body s0 (flatBT (Dprin (v1 : ℕ∞) BZero)) b0 ∧
      -- `k1`: `Trans M` の第 1 種 scb 分解（穴 = `D_{e₃} body`）
      scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1 ∧
      -- `mnform`: `M[m]` の閉形式（`A0` 種の塔）
      (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
        = s1 ++ flatBP (.db (e3 : ℕ∞) (coreTower_e34 ins A0 (m - 1))) ++ b1) ∧
      -- `base0` / `base1'`
      lessBT (Dprin ((v1 - 1 : ℕ) : ℕ∞) BZero) A0 = true ∧
      lessBT A0 (ins BZero) = true

/-! ## 4. drop-in（house pattern） -/

/-- `Exch84_condIIIIV_producer` の drop-in。

`oi5_IIIIV_pkg` の出力から producer の 8 本の連言を作る:
* `fO` ← `scb_fseq_kind1`（原文 §7.2(2) 一般形）＋ `coreTower_zero_flat_ep`。
  Isabelle 側で `d13x_fseq_condIII` ＋ `d4vx_core_flat` が担う段。
* `base1` `A₀ <_B ins (D_{ub} 0_B)` ← base1' ＋ `ins` 単調性。
* `Lbase` `D_{ub} 0_B ≤_B ins 0_B` ← base0 ＋ base1' の推移律
  （Isabelle が `LbaseH` として最後まで引きずり `y3h_LbaseH_uncond`
  scratch:15342 で閉じたもの）。 -/
theorem Exch84_condIIIIV_producer_of_slicepkg (h : Exch84_condIIIIV_slicepkg) :
    Exch84_condIIIIV_producer := by
  intro M hST hmono hj1 hcond hp
  obtain ⟨ins, A0, body, e3, v1, s0, b0, s1, b1,
    hflat, hb0, hb1, hinner, hk1, hmn, base0, base1'⟩ := h M hST hmono hj1 hcond hp
  refine ⟨ins, A0, (e3 : ℕ∞), ((v1 - 1 : ℕ) : ℕ∞), s0, b0, s1, b1,
    hflat, hb0, hb1, ?_, hmn, base0, ?_, ?_⟩
  · -- `fO`: `scb_fseq_kind1` を `c₂ = D_{e₃} body` に適用する
    intro k
    have hTB : Trans M ∈ T_B := Trans_mem_T_B M (STPS_RTPS M hST)
    have hinner' : scb_decomp (Dprin (e3 : ℕ∞) body) (Sym.dsym (e3 : ℕ∞) :: s0)
        (flatBT (Dprin (v1 : ℕ∞) BZero)) b0 := by
      refine ⟨?_, ?_, hinner.2.2⟩
      · have hd : flatBT (Dprin (e3 : ℕ∞) body) = Sym.dsym (e3 : ℕ∞) :: flatBT body := by
          simp [Dprin, flatBT, flatBP]
        rw [hd, hinner.1]
        simp
      · intro _
        exact ⟨.db (v1 : ℕ∞) BZero, by
          simp [dfree_BP, BZero, dfree_BT, dfree_BPList], rfl⟩
    have hfseq := (scb_fseq_kind1 (n := k) hTB hk1 hinner').2
    rw [hfseq]
    simp only [flatBP]
    rw [coreTower_zero_flat_ep hflat (k + 1)]
    simp [List.append_assoc]
  · -- `base1`: `A₀ <_B ins 0_B <_B ins (D_{ub} 0_B)`
    exact lessBT_linear_trans _ _ _ base1'
      (ins_mono_ep hflat hb0 (lessBT_zero_Dprin_ep _ BZero))
  · -- `Lbase`: `D_{ub} 0_B <_B A₀ <_B ins 0_B`
    have hlt : lessBT (Dprin ((v1 - 1 : ℕ) : ℕ∞) BZero) (ins BZero) = true :=
      lessBT_linear_trans _ _ _ base0 base1'
    simp only [leBT, hlt, Bool.true_or]

#print axioms Exch84_condIIIIV_producer_of_slicepkg

end PSS
