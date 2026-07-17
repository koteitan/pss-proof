import «8».«8.7-Trans-preserves-OT»
import «8».«8.7-fseq-descend»
import «8».«8.6-const2nd-Trans»
import «7».«7.2-scb-fseq»
import «7».«7.3-two-column»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.6-P-condAB»

/-!
# §8.7 OT 柱 — 条件 (VI) の交換等式（`Lng M = 2` 境界）

- 原文: `tmp/content.md` 6122（§8.7）。**新しい記事命題は主張しない**。
  `«8».«8.7-Trans-preserves-OT»`:140 が露出した名前付き `Prop`
  `OTdisp_condVI_j1eq1_eq` を**無条件**で閉じる掃討ファイル。訂正: なし。
- Isabelle: `otx_condVI_j1eq1_eq`（`layerB/pss_wip.thy`:85582）。
  仮定束（`M ∈ RT_PS` / `M ∈ PT_PS` / `Lng M = 2` / `transCondVI M` /
  `hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)` / `2 ≤ n`）は Lean の `Prop`
  と 1:1 で照合済み（差分なし）。
  Isabelle 側が呼ぶ 3 本の Lean twin:
  * `m_8_6_rcseq_Trans` (:14299) → `8.6-const2nd-Trans`:625 `const2nd_Trans`
    （`rcseq u j₁ = cseq u u j₁` なので `m := u` 特殊化）
  * `m_7_3_twoColumn_Trans` → `7.3-two-column`:482 `two_column_Trans`
  * `operB_Du_Dv0_kind1_eval` (:25124) → 本ファイルの `operB_Du_Dv0_kind1_ocv`
    （`8.6-Trans-fseq-condVI`:146 の `..._c6` が `private` なので、同じ
    `operB_dprin_kind1`（`7.2-scb-fseq`:586）から privately に再導出）
- 議論: 条件 (VI) の二列ホストは reducedness で `M = ((u,u),(u+1,u+1))` に固定される
  （`u = M_{1,0}`）。`idx1 M 1 = 1`・`parent = 0` より `oper` の増分は `(d₀,d₁) = (1,0)`
  なので `M[n] = ((u+k, u))_{k<n} = const2ndSeq u u (n-1)`、
  `Trans (M[n]) = (D_u)^n 0`。Buchholz 側は `Trans M = D_u(D_{u+1} 0)` が第 1 種
  （`u < u+1`）なので `operB (Trans M) (numBT (n-2)) = D_u((D_u)^{n-1} 0) = (D_u)^n 0`。
- 依存（ビルド済みのみ import）: `8.7-fseq-descend`（`oper_len2_fd` /
  `parent_one_zero_fd`）、`8.6-const2nd-Trans`（`const2nd_Trans`）、
  `7.2-scb-fseq`（`operB_dprin_kind1`）、`7.3-two-column`（`two_column_Trans`）、
  `6.6-reduced-iff-condAB`（`RTPS_condAB`）、`6.6-P-condAB`（`mono_hasParent_row0`）、
  `8.7-Trans-preserves-OT`（`OTdisp_*` の定義）。
- 状態: ✅ `OTdisp_condVI_j1eq1_eq` を**無条件**で証明（sorry 0、
  axioms = propext/Classical.choice/Quot.sound）。
  非空虚性: `python/audit_8_7_trans_preserves_OT.py` で標準形プール上
  **6/6 発火・反例 0**（`otx_condVI_j1eq1_eq` 行）。
  ⚠️ `OTdisp_condVI_adm_eq`（一般ホスト、`1 < Lng M - 1`）は**本ファイルに無い**
  ＝ 未移植の §8.4 scb 分解クラスタ待ち。理由は末尾の注記を参照（偽ではない）。
-/

namespace PSS

/-! ## `operB` の第 1 種評価（Isabelle `operB_Du_Dv0_kind1_eval`:25124 の再導出）

`8.6-Trans-fseq-condVI`:111–157 の `private` 群と同じ論法。`b = D_v 0`（`v > 0`）は
`operB` に対して恒等なので、補助列 `x_i` は純粋な `D_w` の塔になる。 -/

private theorem numNat_numBT_ocv (m : ℕ) : numNat (numBT m) = m := by
  simp [numNat, numBT]

private theorem domTag_Dv0_ocv (v : ℕ) (hv : 0 < v) :
    domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := by
  simp [domTag, domTagList, domTagBP, Dprin, BZero,
    show (v : ℕ∞) ≠ 0 by simpa using (Nat.ne_of_gt hv), ENat.coe_ne_top]

private theorem operB_Dv0_id_ocv (v : ℕ) (z : BT) (hv : 0 < v) :
    operB (Dprin (v : ℕ∞) BZero) z = z := by
  have hv0 : (v : ℕ∞) ≠ 0 := by simpa using (Nat.ne_of_gt hv)
  simp [operB, bOperCore, Dprin, BZero, hv0]

private theorem xseq_zero_ocv (b : BT) (w : ℕ∞) : xseq b w 0 = Dprin w BZero := by
  simp [xseq, bOperCore]

private theorem xseq_succ_ocv (b : BT) (w : ℕ∞) (i : ℕ) :
    xseq b w (i + 1) = Dprin w (operB b (xseq b w i)) := by
  show bOperCore (.xseq b w (i + 1)) =
    Dprin w (bOperCore (.term b (bOperCore (.xseq b w i))))
  rw [bOperCore.eq_def]

private theorem xseq_Dv0_tower_ocv (v : ℕ) (hv : 0 < v) (w : ℕ∞) :
    ∀ i, xseq (Dprin (v : ℕ∞) BZero) w i = (Dprin w)^[i + 1] BZero := by
  intro i
  induction i with
  | zero => simpa using xseq_zero_ocv (Dprin (v : ℕ∞) BZero) w
  | succ i ih =>
      rw [xseq_succ_ocv, operB_Dv0_id_ocv v _ hv, ih,
        Function.iterate_succ_apply' (Dprin w) (i + 1) BZero]

/-- Isabelle `operB_Du_Dv0_kind1_eval`（`layerB/pss_wip.thy`:25124）。`u < v` なら
`D_u(D_v 0)` は第 1 種で、その基本列は内側の塔をひとつずつ伸ばす。 -/
private theorem operB_Du_Dv0_kind1_ocv (u v m : ℕ) (huv : u < v) :
    operB (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) (numBT m)
      = Dprin (u : ℕ∞) ((Dprin ((v - 1 : ℕ) : ℕ∞))^[m + 1] BZero) := by
  have hv : 0 < v := by omega
  have hne : Dprin (v : ℕ∞) BZero ≠ BZero := by simp [Dprin, BZero]
  have htag : domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := domTag_Dv0_ocv v hv
  have hle : (u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := by
    norm_cast
    omega
  rw [operB_dprin_kind1 hne htag hle, numNat_numBT_ocv,
    xseq_Dv0_tower_ocv v hv _ m, operB_Dv0_id_ocv v _ hv]

/-! ## 条件 (VI) の二列ホストの形（reducedness で `((u,u),(u+1,u+1))` に固定） -/

/-- `Lng M = 2` の条件 (VI) ホストの 4 成分。Isabelle `otx_condVI_j1eq1_eq` の
`diagu` / `e11` / `e01` / `i1` / `pv` / `p0` 段に対応する。 -/
private theorem condVI_len2_shape_ocv (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : Lng M = 2) (hcond : transCondVI M = true) :
    entry M 0 0 = entry M 1 0 ∧ entry M 1 1 = entry M 1 0 + 1 ∧
      entry M 0 1 = entry M 1 0 + 1 ∧ idx1 M 1 = 1 ∧ 0 < entry M 1 1 := by
  have hTPS : TPS M := RTPS_TPS M hR
  have hlast : lastIdx M = 1 := by simp [lastIdx, hL]
  -- 条件 (VI) の 2 つの成分
  have hc := hcond
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    hlast] at hc
  have he1pos : 0 < entry M 1 1 := hc.1.1
  -- `idx1 M 1 = 1`
  have hi1 : idx1 M 1 = 1 := by simp [idx1, he1pos]
  -- 行 0 の親は 0（`Lng M = 2` なので唯一の候補）
  have hp0 : hasParent M 0 1 = true :=
    mono_hasParent_row0 M hTPS hmono 1 (by omega) (by omega)
  have hpar0 : parent M 0 1 = 0 := parent_one_zero_fd M 0 hp0
  -- `lastParent M = parent M 0 (lastIdx M) = 0`
  have hlp : lastParent M = 0 := by
    show parent M 0 (lastIdx M) = 0
    rw [hlast]; exact hpar0
  have he11 : entry M 1 1 = entry M 1 0 + 1 := by
    have h := hc.1.2
    rw [hlp] at h
    omega
  -- `RedCondA` を `(i,j) = (0,1)` で使う
  have hA := (RTPS_condAB M hR).1
  have hA01 : entry M 0 (parent M 0 1) + 1 = entry M 0 1 := by
    simp only [RedCondA, List.all_eq_true, List.mem_range, decide_eq_true_eq,
      Bool.or_eq_true, Bool.not_eq_true'] at hA
    have h := hA 0 (by omega) 1 (by omega)
    rcases h with h | h
    · rw [h] at hp0; exact absurd hp0 (by simp)
    · exact h
  have hhead : entry M 0 0 = entry M 1 0 := RTPS_mono_head_eq M hR hmono
  have he01 : entry M 0 1 = entry M 1 0 + 1 := by
    rw [hpar0] at hA01
    omega
  exact ⟨hhead, he11, he01, hi1, he1pos⟩

/-! ## `OTdisp_condVI_j1eq1_eq` — 無条件 -/

/-- Isabelle `otx_condVI_j1eq1_eq`（`layerB/pss_wip.thy`:85582）。

House pattern: `Prop` は `«8».«8.7-Trans-preserves-OT»`:140 の定義そのものを型に取る
（restate しない）。 -/
theorem OTdisp_condVI_j1eq1_eq_holds : OTdisp_condVI_j1eq1_eq := by
  intro M n hR hmono hL hcond hp hn
  have hTPS : TPS M := RTPS_TPS M hR
  obtain ⟨hhead, he11, he01, hi1, he1pos⟩ :=
    condVI_len2_shape_ocv M hR hmono hL hcond
  set u := entry M 1 0 with hu
  -- 仮定の `hasParent` を `Lng M - 1 = 1` に正規化
  have hj1 : Lng M - 1 = 1 := by omega
  have hp' : hasParent M (idx1 M 1) 1 = true := by
    rw [hj1] at hp; exact hp
  have hpar1 : parent M (idx1 M 1) 1 = 0 := parent_one_zero_fd M (idx1 M 1) hp'
  have hnz : ¬(entry M 0 1 = 0 ∧ entry M 1 1 = 0) := by omega
  -- `M[n]` の閉形式: 増分は `(d₀,d₁) = (1,0)`
  have hd0 : (if 0 < idx1 M 1 then
      entry M 0 1 - entry M 0 (parent M (idx1 M 1) 1) else 0) = 1 := by
    rw [hpar1, hi1]
    simp only [if_true, Nat.zero_lt_one]
    omega
  have hd1 : (if 1 < idx1 M 1 then
      entry M 1 1 - entry M 1 (parent M (idx1 M 1) 1) else 0) = 0 := by
    rw [hi1]; simp
  have hoper := oper_len2_fd M hL hnz hp' 1 0 hd0 hd1 n
  -- `M[n] = const2ndSeq u u (n-1)`
  have hconst : oper M n = const2ndSeq u u (n - 1) := by
    rw [hoper, const2ndSeq, show n - 1 + 1 = n by omega, hhead]
    apply List.map_congr_left
    intro k _
    simp [← hu]
  -- 左辺: `Trans (M[n]) = (D_u)^n 0`
  have hTPSn : TPS (oper M n) := by
    rw [hconst]
    exact List.ne_nil_of_length_pos (by simp [const2ndSeq])
  have hLHS : Trans (oper M n) = (Dprin (u : ℕ∞))^[n] BZero := by
    have h := (const2nd_Trans (oper M n) u u (n - 1) hconst hTPSn).2
      (Or.inl (by omega))
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  -- 右辺: `Trans M = D_u(D_{u+1} 0)` は第 1 種
  have hTM : Trans M = Dprin (u : ℕ∞) (Dprin ((u + 1 : ℕ) : ℕ∞) BZero) := by
    rw [two_column_Trans M hR hmono hL, he11]
  rw [hLHS, hTM, operB_Du_Dv0_kind1_ocv u (u + 1) (n - 2) (by omega),
    show u + 1 - 1 = u by omega, show n - 2 + 1 = n - 1 by omega,
    ← Function.iterate_succ_apply' (Dprin (u : ℕ∞)) (n - 1) BZero]
  congr 1
  omega

#print axioms OTdisp_condVI_j1eq1_eq_holds

/-! ## `OTdisp_condVI_adm_eq` を**閉じなかった**理由（正直な報告）

`OTdisp_condVI_adm_eq`（`8.7-Trans-preserves-OT`:147、一般ホスト `1 < Lng M - 1`）は
**偽ではない**。Isabelle は `otx_condVI_adm_eq`（`layerB/pss_wip.thy`:85236）で
無条件に証明しており、仮定束も Lean の `Prop` と 1:1 で一致する（照合済み）。
`python/audit_8_7_trans_preserves_OT.py` でも標準形プール上 **60/60 発火・反例 0**。

閉じられないのは `private` の壁ではなく**未移植の基盤**が理由:

* Lean 側の配線は既に最小化されている——
  `OTdisp_condVI_adm_eq_of_scbforms_v6`（`8.7-Trans-preserves-OT-props`:313）が
  `CondVI_scbdec_adm_forms_v6`（`8.6-condVI-close`:222）**1 本**まで削減済で、
  Buchholz 側（`c613x_operB_fseq_value` ＋ `flat_Dtower`）は既に閉じている。
* 残った `CondVI_scbdec_adm_forms_v6` は**ペア数列側の scb 手術**であり、
  Isabelle では `c613x_condVI_exch_adm`（同 :73312、209 行）が
  `s84c2_Trans_c2_decomp`（:54605）／`c6zx_L_tower`（:72166）／
  `c6zx_condVI_baseL_free`（:72286）／`c6gx_condVI_Lp`（:70020）／
  `c6gx_condVI_setup`（:69867）／`c6gx_condVI_bridge`（:69828）／
  `c6gx_condVI_transC1_adm`（:69904）／`m_8_4_oper_props_5`（:54005）／
  `trans_surgery_localized`（:23635）＋ `s84x_L`/`s84x_Lp`/`s84x_jm2`（:52620–52636）
  に乗る。これは **Lean 未移植の §8.4 scb 分解クラスタ**（:52620–:72286 の帯域）
  であって、`8.5-Trans-fseq-condV` の `ExchV_scbdec_*` が同じ理由で露出している
  **共有基盤**である。単一ファイル・単一 wave の射程を超えるので、
  中途半端に `sorry` を残さず**まるごと除外**した。

したがって本ファイルが無条件に閉じた残差は `OTdisp_condVI_j1eq1_eq` の 1 本のみ。
`8.7-termination`:216 の `otCondVIj1` 葉に `OTdisp_condVI_j1eq1_eq_holds` を
drop-in できる（型は `Prop` の定義そのものなので elaborator が保証済み）。 -/

end PSS
