import «8».«8.1-Trans-fseq-condI»
import «8».«8.3-TransCondII-engine»
import «8».«8.6-Trans-fseq-condVI»
import «8».«8.6-condVI-close»
import «8».«8.7-Trans-preserves-OT»

/-!
# §8.7 OT 柱 — `OTdisp_*` の掃討

- 原文: `tmp/content.md` 6122（§8.7）。**本ファイルは新しい記事命題を主張しない**。
  `«8».«8.7-Trans-preserves-OT»` が露出した 12 本の名前付き `Prop`（`OTdisp_*`、
  同 :81–157）を、ビルド済みツリーの既存定理へ配線する掃討ファイル。
  訂正: なし（A 番号の該当なし）。
- 位置づけ: 停止性の 2 本柱のうち **OT 柱**（もう 1 本は降下柱
  `8.7-fseq-descend` ＝ `FseqDesc_*` 16 本）。降下柱側の掃討
  `«8».«8.7-fseq-descend-props2»` と同じ役目・同じ `_of_*` 命名規約。

## 本ファイルで配線した 7 本（12 本中）

| `OTdisp_*` | 出典（ビルド済み） | Isabelle | modulo |
|---|---|---|---|
| `exchI` | `8.1-Trans-fseq-condI`:568 `exchI_holds` | `scx_condI_j0pos_masterCF` (`layerB/pss_wip.thy`:83639) | `CondI_masterCF` 1 本 |
| `exchII` | `8.3-TransCondII-engine`:223 `exchII_of_masterCF` | `c2sx_condII_masterCF` (同 :87430) | `CondII_masterCF` 1 本 |
| `zerocol_predval` | `7.3-Trans-welldefined`:1282 `Trans_Mark_multi_equations` ＋ `6.2-P-additivity`:24 `Pcut_props` | `otx_zerocol_predval` (同 :85474) | **無条件** |
| `Trans_fseq_condI_n1` | `8.1-Trans-fseq-condI`:433 `condI_exchange1`（`n := 1`） | `m_8_1_Trans_fseq_condI_n1` (同 :33271) | `CondI_masterCF` ＋ `FseqDesc_operI_j0zero_trans_mult` ＋ `FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1` |
| `condI_j0z_eq` | 同 `condI_exchange1`（`j₀ = 0` 仮定は**不要**） | `otx_condI_j0z_eq` (同 :85292) | 同上 3 本 |
| `condVI_adm_eq` | `8.6-Trans-fseq-condVI`:220 `CondVIAdmTowerScb` | `otx_condVI_adm_eq` (同 :85236)／`c613x_condVI_exch_adm` | `CondVIAdmTowerScb` 1 本（→ `CondVI_scbdec_adm_forms_v6`） |
| `condVI_nadm_eq` | `8.6-Trans-fseq-condVI`:236 `CondVIExchNadm` (2) | `otx_condVI_nadm_eq` (同 :85260)／`c6nx_condVI_exch_nadm_uncond` | `CondVIExchNadm` 1 本（→ `CondVI_scbdec_nadm_forms_v6`） |

- 🚨 **`exchI`/`exchII` は降下柱の `FseqDesc_exchI`/`FseqDesc_exchII` と本文が
  バイト単位で同一**（`8.7-fseq-descend`:67–95 と照合済み）。したがって
  `8.7-fseq-descend-props2`:95/99 の drop-in がそのまま `OTdisp_*` 側にも落ちる
  （`def` は semireducible なので両者は defeq）。**再導出はしない**。
- 🚨 **`condVI_adm_eq` は `exchVI_holds_v6`（`8.6-condVI-close`:394）の許容枝と
  同一の証明**（塔の添字が `Trans(M[n]) ↦ n-1`、`operB (Trans M) (numBT (n-2)) ↦
  (n-2)+1 = n-1` で一致 → `flatBT_injective`）。`2 ≤ n` は `OTdisp_` 側の仮定にある。
- ⚠️ **`condVI_adm_eq`/`condVI_nadm_eq` の modulo は循環ではない**:
  `CondVIAdmTowerScb`/`CondVIExchNadm` は `8.6-Trans-fseq-condVI` が露出する
  **独立の名前付き仮定**であって `OTdisp_*` から導かれるものではない
  （`8.6-condVI-close`:370 `transPreservesOT_of_OTdisp_v6` は逆向き＝
  `OTdisp_*` → `TransPreservesOT` の委譲で、本ファイルとは合流しない）。
  両者は `8.5`（`ExchV_scbdec_*`）と共有の §8.4 scb 分解クラスタに乗る。

## 未配線の残り 5 本（実移植が要る。**name-grep でなく content-grep 済**）

### (a) `OTint` / `OTpred` / `OTmulti` — `OT_B` 帰納の本体

`OTdisp_OTint`（Isa `oi8_OTint_condIII`/`oi8_OTint_condIV` ＋ condV 脚）／
`OTdisp_OTpred`（Isa `opx_OTpred_of_residuals`、残差 `{DEEPOT, NOBR}`）／
`OTdisp_OTmulti`（Isa `opx_OTmulti`）: ビルド済みツリーに twin 無し。

🚨 **安易な道は塞がっている（確認済み）**: 条件 (III)/(IV)/(V) の交換則は
**等式ではなく狭義不等式**でしか出ない——
`8.4-Trans-fseq-condIII-IV`:229 `Trans_oper_exchange` は
`lessBT (Trans (oper M n)) (operB (Trans M) (numBT n))`、
`8.5-Trans-fseq-condV`:459/511 の adm/非 adm 両枝も `lessBT`
（`8.5`:568 `exchV_holds` が `leBT` に緩めているのは `leBT = (== || lessBT)` だから）。
したがって `7.1-buchholz-fseq-closed`:1358 `buchholz_fseq_closed`
（`a ∈ OT_B → a ≠ 0_B → operB a (numBT n) ∈ OT_B`）を当てても
`operB (Trans M) (numBT k) ∈ OT_B` までしか行かず、**`OT_B` は `lessBT` で
下方閉ではない**（`OT_B` は正規形の集合であって始切片ではない）ので
`Trans (oper M n) ∈ OT_B` は出ない。`8.7-OT-dom-hereditary`:181
`OT_dom_hereditary` 経由の実移植が要る。

### (b) `condI_j1eq1_eq` / `condVI_j1eq1_eq` — `Lng M = 2` 境界 regime

`1 < Lng M - 1` が偽なので `condI_exchange1`/`CondVIAdmTowerScb` は
**どちらも適用不可**（全て `hj1 : 1 < Lng M - 1` を要求する）。

**道は特定済み・算術も照合済み**（`condI_j1eq1_eq`、Isa `otx_condI_j1eq1_eq` 同 :85516）:
`M = ((v,v),(c,0))`（`RTPS_mono_head_eq` で `M_{0,0} = M_{1,0} = v`、条件(I) で
`M_{1,1} = 0`）とすると `idx1 M 1 = 0` なので `oper` の増分は `d₀ = d₁ = 0`、
すなわち **`M[n] = replicate n (v,v)`**。よって

* `Trans (M[n])` ＝ `8.7-const00-Trans`:195 `const00_Trans` で
  `if v = 0 then (D_v 0) ×_B (n-1) else (D_v 0) ×_B n`;
* `Trans M` ＝ `7.3-two-column`:482 `two_column_Trans` で `D_v (D_0 0)`、
  その基本列は `operB (D_v (D_0 0)) (numBT k) = (D_v 0) ×_B (k+1)`
  （`8.1-Trans-fseq-condI`:204 `operB_succ_body_ci` の `t₂ := 0_B` 特殊化）。

`2 ≤ n` で `(n-2)+1 = n-1` / `(n-1)+1 = n` なので **`Prop` の `if` 分岐と完全一致**する
（＝この `Prop` は真であり転記ミスではない）。**未配線の理由は再移植コストのみ**:
`M[n]` の閉形式 `8.7-fseq-descend`:362 `oper_len2_fd` と、それが呼ぶ
同 :249 `parent_one_zero_fd`、および `operB_succ_body_ci` が**すべて `private`**。
`condVI_j1eq1_eq`（同 :85582）も同じ `Lng M = 2` 基盤に乗る。

## 🔑 親への申し送り: `private` を外すだけで改善する 2 件

1. **`OTdisp_Trans_fseq_condI_n1` は modulo 0 にできる**。Isabelle では無条件
   （`m_8_1_Trans_fseq_condI_n1`）で、Lean 側にも**無条件の証明が既にある**——
   `8.1-Trans-fseq-condI`:303 `Trans_fseq_condI_n1_ci`（仮定は
   `RTPS`/`monoT`/`1 < Lng M - 1`/条件(I) のみ）。**`private` なので参照できず**、
   本ファイルは已む無く `condI_exchange1` 経由（3 本 modulo）で配線している。
   `private` を 1 語外せば `OTdisp_Trans_fseq_condI_n1_of_CondI` は無仮定版に置換可。
2. **`Lng M = 2` の 2 本（(b) 参照）の障壁も `private` のみ**:
   `8.7-fseq-descend`:249/362 の `parent_one_zero_fd` / `oper_len2_fd` と
   `8.1-Trans-fseq-condI`:204 `operB_succ_body_ci`。この 3 本を公開すれば
   `condI_j1eq1_eq` は上記 (b) の算術で閉じる（新しい数学は不要）。

- 依存（ビルド済みのみ import）: `8.1-Trans-fseq-condI`（`exchI_holds` /
  `CondI_masterCF` / `condI_exchange1`）、`8.3-TransCondII-engine`
  （`exchII_of_masterCF` / `CondII_masterCF`）、`8.6-Trans-fseq-condVI`
  （`CondVIAdmTowerScb` / `CondVIExchNadm`）、`8.6-condVI-close`
  （`condVIAdmTowerScb_of_scbforms_v6` / `condVIExchNadm_of_scbforms_v6` /
  `CondVI_scbdec_adm_forms_v6` / `CondVI_scbdec_nadm_forms_v6`）、
  `8.7-Trans-preserves-OT`（`OTdisp_*` の定義）。`7.3-Trans-welldefined`
  （`Trans_Mark_multi_equations`）／`6.2-P-additivity`（`Pcut_props`）は
  上記経由で推移的に入る。
  **`8.7-fseq-descend-props`/`-props2` は import しない**（配線は素集合）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  12 本中 **7 本配線**（うち `zerocol_predval` は**無条件**、残り 6 本は
  `CondI_masterCF` / `CondII_masterCF` / `CondVIAdmTowerScb` / `CondVIExchNadm`
  ＋ `FseqDesc_*` 2 本 modulo ＝ **いずれも既存の名前付き仮定で、本ファイルは
  プロジェクト全体の残差集合を増やさない**）。
-/

namespace PSS

/-! ## (1) `OTdisp_exchI` — `8.1-Trans-fseq-condI`:568 の `exchI_holds`

`OTdisp_exchI`（`8.7-Trans-preserves-OT`:81）は `FseqDesc_exchI`
（`8.7-fseq-descend`:67）と**本文がバイト単位で同一**なので、降下柱の drop-in
（`8.7-fseq-descend-props2`:95）がそのまま落ちる。 -/
theorem OTdisp_exchI_of_CondI (hCF : CondI_masterCF) : OTdisp_exchI :=
  exchI_holds hCF

/-! ## (2) `OTdisp_exchII` — `8.3-TransCondII-engine`:223 の `exchII_of_masterCF`

同じく `OTdisp_exchII`（同 :88）＝ `FseqDesc_exchII`（`8.7-fseq-descend`:88）。 -/
theorem OTdisp_exchII_of_CondII (hCF : CondII_masterCF) : OTdisp_exchII :=
  exchII_of_masterCF hCF

/-! ## (3) `OTdisp_Trans_fseq_condI_n1` — `condI_exchange1` の `n = 1` 特殊化

Isabelle `m_8_1_Trans_fseq_condI_n1` は無条件だが、その Lean twin
（`8.1-Trans-fseq-condI`:303 `Trans_fseq_condI_n1_ci`）が `private` なので、
公開されている `condI_exchange1` の `n := 1` 脚で配線する（`1 - 1 = 0`）。 -/
theorem OTdisp_Trans_fseq_condI_n1_of_CondI (hCF : CondI_masterCF)
    (hMul : FseqDesc_operI_j0zero_trans_mult)
    (hA : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1) :
    OTdisp_Trans_fseq_condI_n1 := by
  intro M hR hmono hj1 hI
  simpa using condI_exchange1 hCF hMul hA M 1 hR hmono hj1 hI (le_refl 1)

/-! ## (4) `OTdisp_condI_j0z_eq` — `condI_exchange1` そのもの

`condI_exchange1` は `j₀` の値に依らず（`stepT` の内部で `j₀ = 0` / `j₀ > 0` の
両枝を潰して）交換等式を出すので、`OTdisp_condI_j0z_eq` の
`parent M 0 (Lng M - 1) = 0` は**使わない**。 -/
theorem OTdisp_condI_j0z_eq_of_CondI (hCF : CondI_masterCF)
    (hMul : FseqDesc_operI_j0zero_trans_mult)
    (hA : FseqDesc_m_8_2_subexpr_component_Pred_Adm0_clause1) :
    OTdisp_condI_j0z_eq := by
  intro M n hR hmono hj1 hI _hj0z hn
  exact condI_exchange1 hCF hMul hA M n hR hmono hj1 hI hn

/-! ## (5) `OTdisp_condVI_adm_eq` — `CondVIAdmTowerScb` の塔マッチ

`8.6-condVI-close`:394 `exchVI_holds_v6` の許容枝と同一の議論:
`CondVIAdmTowerScb` は同じ `(s₁, b₁)` の中で

* `Trans (M[n])` ↦ 塔の添字 `n - 1`,
* `operB (Trans M) (numBT m)` ↦ 塔の添字 `m + 1`

を与えるので、`m := n - 2`（`2 ≤ n` より `(n-2)+1 = n-1`）で中身が一致し、
`flatBT` の単射性で項として等しい。 -/
theorem OTdisp_condVI_adm_eq_of_CondVIAdmTowerScb (hA : CondVIAdmTowerScb) :
    OTdisp_condVI_adm_eq := by
  intro M n hST hmono hcond hj₁ hadm hn
  have hR : RTPS M := STPS_RTPS M hST
  obtain ⟨s₁, b₁, hMn, hop⟩ := hA M hST hR hmono hcond hj₁ hadm
  have h1 := hMn n (by omega)
  have h2 := hop (n - 2)
  rw [show n - 2 + 1 = n - 1 by omega] at h2
  exact flatBT_injective (h1.1.trans h2.1.symm)

/-! ## (6) `OTdisp_condVI_nadm_eq` — `CondVIExchNadm` の結論 (2) そのもの

`8.6-Trans-fseq-condVI`:236 の `CondVIExchNadm` の第 2 結論
（`∀ n, 1 ≤ n → Trans (oper M n) = operB (Trans M) (numBT (n - 1))`）と
**結論が同一**。仮定側の差は `RTPS M` のみで、`STPS_RTPS` で埋まる。 -/
theorem OTdisp_condVI_nadm_eq_of_CondVIExchNadm (hB : CondVIExchNadm) :
    OTdisp_condVI_nadm_eq := by
  intro M n hST hmono hcond hj₁ hadm hn
  have hR : RTPS M := STPS_RTPS M hST
  exact (hB M hST hR hmono hcond hj₁ hadm).2.1 n hn

/-! ## (7) `OTdisp_zerocol_predval` — **無条件**

Isabelle `otx_zerocol_predval`（`layerB/pss_wip.thy`:85474）。

末尾列が `(0,0)` なら `Trans M` は**後続数項** `Trans(Pred M) +_B D₀0` であり、
後続数項の基本列は添字 `m` に依らず前者そのもの。3 段で閉じる:

1. `entry M 0 j₁ = 0` なら `(0,j) ≤_M (0,j₁)` は `j = j₁` のときだけ
   （`nextrel0 M k j₁` は `M_{0,k} < M_{0,j₁} = 0` を要求するので恒偽）
   → `Pcut M = j₁`（`6.2-P-additivity`:24 `Pcut_props` の 3 番目の結論に当てる）
   かつ `monoT M = false` → `multiT M = true`;
2. よって `7.3-Trans-welldefined`:1282 `Trans_Mark_multi_equations` の
   `J == [(0,0)]` 枝が発火し `Trans M = Trans(Pred M) +_B D₀0`;
3. `operB (t +_B D₀0) z = t`（`bOperCore` の `.princ (.db 0 0_B) z` 脚が `0_B`）。
-/

/-- 末尾列の上段が `0` なら上段の親子 1 段は張れない。 -/
private theorem nextrel0_zerocol_otp (M : PS) (j₁ k : ℕ)
    (hz : entry M 0 j₁ = 0) : nextrel0 M k j₁ = false := by
  simp [nextrel0, hz]

/-- したがって上段の先祖関係は反射脚だけ。 -/
private theorem le0Aux_zerocol_otp (M : PS) (fuel j j₁ : ℕ)
    (hz : entry M 0 j₁ = 0) : le0Aux M fuel j j₁ = (j == j₁) := by
  cases fuel with
  | zero => rfl
  | succ f =>
      have hn : ∀ k, nextrel0 M k j₁ = false := fun k =>
        nextrel0_zerocol_otp M j₁ k hz
      simp [le0Aux, hn]

/-- `(0,j) ≤_M (0,j₁)` かつ `M_{0,j₁} = 0` なら `j = j₁`。 -/
private theorem leR0_zerocol_eq_otp (M : PS) (j j₁ : ℕ) (hz : entry M 0 j₁ = 0)
    (h : leR M 0 j j₁ = true) : j = j₁ := by
  unfold leR at h
  rw [if_pos rfl] at h
  unfold le0 at h
  rw [le0Aux_zerocol_otp M (Lng M) j j₁ hz] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem Pcut_zerocol_otp (M : PS) (hlen : 1 < Lng M)
    (hz : entry M 0 (Lng M - 1) = 0) : Pcut M = Lng M - 1 := by
  obtain ⟨-, -, hle⟩ := Pcut_props M hlen
  exact leR0_zerocol_eq_otp M (Pcut M) (Lng M - 1) hz hle

private theorem multiT_zerocol_otp (M : PS) (hlen : 1 < Lng M)
    (hz : entry M 0 (Lng M - 1) = 0) : multiT M = true := by
  have hzero : zeroT M = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl (by omega)
  have hmono : monoT M = false := by
    simp only [monoT, hzero, Bool.not_false, Bool.true_and,
      Bool.eq_false_iff, ne_eq]
    intro h
    have := leR0_zerocol_eq_otp M 0 (Lng M - 1) hz h
    omega
  simp [multiT, hzero, hmono]

/-- `bOperCore` の snoc 分解（`8.1-Trans-fseq-condI`:181 `bOperCore_list_snoc_ci`
が `private` なので同じ証明を再掲）。 -/
private theorem bOperCore_list_snoc_otp (ps : List BP) (p : BP) (z : BT) :
    bOperCore (.list (ps ++ [p]) z) =
      addBT (.trm ps) (bOperCore (.princ p z)) := by
  induction ps with
  | nil =>
      rw [bOperCore.eq_def]
      change bOperCore (.princ p z) = addBT BZero (bOperCore (.princ p z))
      rcases hb : bOperCore (.princ p z) with ⟨cs⟩
      simp [addBT, BZero]
  | cons q qs ih =>
      cases qs with
      | nil => simp [bOperCore, addBT]
      | cons r rs =>
          rw [bOperCore.eq_def]
          change addBT (.trm [q])
              (bOperCore (.list ((r :: rs) ++ [p]) z)) =
            addBT (.trm (q :: r :: rs)) (bOperCore (.princ p z))
          rw [ih]
          rcases hb : bOperCore (.princ p z) with ⟨cs⟩
          simp [addBT]

/-- 後続数項の基本列は添字に依らず前者。 -/
private theorem operB_succ_zero_otp (t z : BT) :
    operB (addBT t (Dprin 0 BZero)) z = t := by
  rcases t with ⟨ps⟩
  rw [operB, show addBT (BT.trm ps) (Dprin 0 BZero)
      = BT.trm (ps ++ [BP.db 0 BZero]) from rfl, bOperCore.eq_def]
  change bOperCore (.list (ps ++ [BP.db 0 BZero]) z) = _
  rw [bOperCore_list_snoc_otp]
  have hp : bOperCore (.princ (BP.db 0 BZero) z) = BZero := by
    rw [bOperCore.eq_def]; simp
  rw [hp]
  simp [addBT, BZero]

theorem OTdisp_zerocol_predval_holds : OTdisp_zerocol_predval := by
  intro M m hR hlen h0 h1
  have hmulti : multiT M = true := multiT_zerocol_otp M hlen h0
  have hcut : Pcut M = Lng M - 1 := Pcut_zerocol_otp M hlen h0
  -- 末尾列は `(0,0)`
  have hdlen : (M.drop (Pcut M)).length = 1 := by
    rw [hcut]; simp only [List.length_drop]; simp only [Lng] at hlen ⊢; omega
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hdlen
  have hget : M[Lng M - 1]? = some p := by
    have h := congrArg (fun l => l[0]?) hp
    simpa [List.getElem?_drop, hcut] using h
  have hJ : M.drop (Pcut M) = [(0, 0)] := by
    rw [hp]
    have e0 : p.1 = 0 := by simpa [entry, hget] using h0
    have e1 : p.2 = 0 := by simpa [entry, hget] using h1
    rw [show p = (p.1, p.2) from rfl, e0, e1]
  have hApred : M.take (Pcut M) = Pred M := by
    rw [hcut, Pred, if_neg (Nat.not_le_of_lt hlen), List.dropLast_eq_take]
  -- `Trans M` は後続数項
  have hTrans : Trans M = addBT (Trans (Pred M)) (Dprin 0 BZero) := by
    have heq := (Trans_Mark_multi_equations M hR hmulti).1
    simp only [hJ, hApred, beq_self_eq_true, if_true] at heq
    exact heq
  rw [hTrans, operB_succ_zero_otp]

/-! ## (5')(6') §8.4 scb 分解クラスタまで下ろした形

`8.6-condVI-close` の削減（`condVIAdmTowerScb_of_scbforms_v6` /
`condVIExchNadm_of_scbforms_v6`）と合成して、残差を §8.5 と共有の
`CondVI_scbdec_*_forms_v6` に揃えたもの。 -/
theorem OTdisp_condVI_adm_eq_of_scbforms_v6 (hA : CondVI_scbdec_adm_forms_v6) :
    OTdisp_condVI_adm_eq :=
  OTdisp_condVI_adm_eq_of_CondVIAdmTowerScb (condVIAdmTowerScb_of_scbforms_v6 hA)

theorem OTdisp_condVI_nadm_eq_of_scbforms_v6 (hB : CondVI_scbdec_nadm_forms_v6) :
    OTdisp_condVI_nadm_eq :=
  OTdisp_condVI_nadm_eq_of_CondVIExchNadm (condVIExchNadm_of_scbforms_v6 hB)

#print axioms OTdisp_exchI_of_CondI
#print axioms OTdisp_exchII_of_CondII
#print axioms OTdisp_Trans_fseq_condI_n1_of_CondI
#print axioms OTdisp_condI_j0z_eq_of_CondI
#print axioms OTdisp_zerocol_predval_holds
#print axioms OTdisp_condVI_adm_eq_of_CondVIAdmTowerScb
#print axioms OTdisp_condVI_nadm_eq_of_CondVIExchNadm
#print axioms OTdisp_condVI_adm_eq_of_scbforms_v6
#print axioms OTdisp_condVI_nadm_eq_of_scbforms_v6

end PSS
