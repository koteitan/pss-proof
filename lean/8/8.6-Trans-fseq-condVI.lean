import «8».«8.6-diagSeq-Trans-fseq»
import «8».«8.6-trailing-principal-annihilable»
import «8».«8.7-OT-examples»
import «Buchholz-1986».«Buchholz-1986-3.2-descent»
import «Buchholz-1986».«Buchholz-1986-3.3»
import «7».«7.3-Pred-Trans-descend»
import «7».«7.3-Trans-preserves-zeroT»
import «5».«5.3-pred-is-oper1»

/-!
# §8.6 命題（条件 (VI) の下での `Trans` と基本列の交換関係）

- 原文: `tmp/content.md` 5484（証明 5670–5760）
- 訂正: **なし（原文は印字どおり真）**。A-番号監査:
  * **A23**（§7.1 脚注 [30] の `x_i` の `D_u` と `b[·]` の転置）は本命題の *主張* には
    かからない。かかるのは `operB`（基本列）の *定義* であり、Lean 側は
    `Buchholz-1986/ および Buchholz-rel-ord/` の `bOperCore`/`xseq` で既に A23 訂正後の規則を採用済み。
    むしろ原文 §8.6 の証明が挙げる 2 ケース（`(D_v 0)[0] = 0` と
    `(D_v 0)[D_{v-1} 0] = D_{v-1} 0`）が A23 訂正の読みの裏づけになっている
    （`corrections.md` A23 の根拠 2）。
  * **A34/A37**（「(1) の `m_n = -1` の脚が偽」と主張していた）は **取り下げ済**
    （`corrections-old.md`:123/154）。正しい基本列の下では 445/445 で原文が真。
    `isabelle/memo.md`:152 が本命題 (1) を「偽命題の sorry 残置」に数えているのは
    この取り下げを反映していない stale 行である。
- Isabelle:
  * 逐語転記 = `p_8_6_Trans_fseq_condVI`（`isabelle/pss_paper.thy`:2218、`sorry`）
  * 降下エンジン = `m_8_6_TransCondVI_oper_descend_engine`（`layerB/pss_wip.thy`:40250）
  * 対角ホストの交換 = `m_8_6_diagSeq_condVI_commute`（同 :40305）、
    降下 = `m_8_6_diagSeq_condVI_descent`（同 :40331）
  * 一般ホストの交換 = `c613x_condVI_exch_adm`（同 :73312、許容 `j₀`）と
    `c6nx_condVI_exch_nadm_uncond`（同 :76705、非許容 `j₀`）。
    境界同定 `c6zx_condVI_oper_L`（同 :72257）＋ L 塔 `c6zx_L_tower`（同 :72181）で
    `Trans(M[n])` の平坦閉形式を出し、`c613x_operB_fseq_value` で `operB` 側と
    添字を合わせる、というのが両者に共通の骨格。
- 依存: `8.6-diagSeq-Trans-fseq`（`diagSeq_Trans_fseq`）、`8.1-diagSeq-Trans`
  （`diagSeq_Trans`、上記経由）、`8.6-trailing-principal-annihilable`
  （`trailing_principal_annihilable` ＝ A23 訂正後の零化上界）、`8.7-OT-examples`
  （`OT_examples_2`）、`Buchholz-1986-3.2-descent`（[Buc1] Lemma 3.2(a)
  ＝ `buchholz_fseq_lt`）、`7.3-Pred-Trans-descend`、`7.3-Trans-preserves-zeroT`、
  `5.3-pred-is-oper1`、`7.2-scb-fseq`（`operB_dprin_kind1`、上記経由）。
- 状態: 🚧 GREEN（sorry 0）。エンジン・対角ホスト実例は**無条件**。原文の完全形
  `p_8_6_Trans_fseq_condVI` は名前付き命題 3 本
  （`CondVIAdmTowerScb` / `CondVIExchNadm` / `TransPreservesOT`）modulo。
  詳細は各 `def` の docstring を参照。
- 経験的確認（`python/_c6_condvi_propA.py`、真正 ST_PS プール = diagSeq 種の
  `oper` 閉包 2000、単項ホスト 1674、A23 訂正後の `operB`、`n,m ≤ 4`）:
  * (A) `CondVIAdmTowerScb`: 許容 `j₀` の条件 (VI) ホスト **206/206**（非空虚）
  * (B) `CondVIExchNadm`: 非許容 `j₀` の条件 (VI) ホスト **24/24**（非空虚）
  * (C) 本ファイルが (A) から**導出**する原文 (1)（`n=1`・`j₀` 許容の脚）:
    **206/206**、witness `k ∈ {2,3}`、常に上界 `1 < k ≤ M_{1,j₁}+1` 内。
    ＝ A34/A37 の取り下げ（原文は真）の再確認。

## 設計

原文の結論 (3) は「(1)(2) と [Buc1] Lemma 3.2 より即座に従う」（原文 5670）。
これを Isabelle と同じ形でエンジン化したのが `m_8_6_TransCondVI_oper_descend_engine`
であり、`n = 1` の脚は条件 (VI) を使わない純 `Pred` 降下、`n > 1` は Buchholz 側の
基本列 1 歩なので Lemma 3.2(a) で真に降下する。つまり §8.6 の降下は
`{exch, Trans M ∈ OT_B}` の 2 つだけに乗る（`Trans M ≠ 0` は `j₁ > 1` から
`Trans_preserves_zeroT` でここで潰れる＝残差ではない）。
-/

namespace PSS

/-! ## §8.6 結論 (3) の降下エンジン -/

/-- Isabelle `m_8_6_TransCondVI_oper_descend_engine`（`layerB/pss_wip.thy`:40250）。

原文の結論 (3)（`Trans(M[n]) < Trans(M)`）を、交換 `exch`（結論 (1)/(2) の
`operB` 露出形）と `Trans M ∈ OT_B` の 2 つに還元する。`M ∈ PT_PS`（`hmono`）と
条件 (VI)（`hcond`）は原文の主張に合わせて残してあるが、Isabelle 版と同じく
この還元自身は使わない（`n = 1` の脚は `M[1] = Pred M` の純 `Pred` 降下）。 -/
theorem m_8_6_TransCondVI_oper_descend_engine (M : PS) (n : ℕ)
    (hST : STPS M) (hR : RTPS M) (hmono : monoT M = true)
    (hj₁ : 1 < Lng M - 1) (hcond : transCondVI M = true) (hn : 0 < n)
    (hTOT : Trans M ∈ OT_B)
    (hexch : 1 < n →
      ∃ k, leBT (Trans (oper M n)) (operB (Trans M) (numBT k)) = true) :
    lessBT (Trans (oper M n)) (Trans M) = true := by
  have hlen' : 1 < M.length := by
    have h : 1 < Lng M := by omega
    exact h
  have hM : TPS M := List.ne_nil_of_length_pos (by omega)
  have hlen : 1 < Lng M := hlen'
  -- `Trans M ≠ 0`: `j₁ > 1` なので `M` は零項でない（原文 5670 の一行）
  have hz : zeroT M = false := by
    have h1 : ¬ (M.length = 1) := by omega
    have h1' : ¬ (Lng M = 1) := h1
    simp [zeroT, h1']
  have hTne : Trans M ≠ BZero := by
    intro h
    have hzz := (Trans_preserves_zeroT M hM).mpr h
    rw [hz] at hzz
    exact Bool.noConfusion hzz
  by_cases h1 : n = 1
  · -- `n = 1` の脚: `M[1] = Pred M`、純 `Pred` 降下（条件 (VI) 不要）
    subst h1
    rw [← pred_is_oper1 M hM hlen]
    exact Pred_Trans_descend M hM hlen
  · -- `n > 1`: Buchholz 側の基本列 1 歩なので [Buc1] Lemma 3.2(a) で降下
    have hn1 : 1 < n := by omega
    obtain ⟨k, hk⟩ := hexch hn1
    have hlt := buchholz_fseq_lt (Trans M) k hTOT hTne
    simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hk
    rcases hk with hk | hk
    · exact lessBT_linear_trans _ _ _ hk hlt
    · rw [hk]; exact hlt

/-! ## `operB` の第 1 種評価（`D_u(D_v 0)[m] = D_u(D_{v-1}^{m+1} 0)`、`u < v`） -/

private theorem numNat_numBT_c6 (m : ℕ) : numNat (numBT m) = m := by
  simp [numNat, numBT]

private theorem domTag_Dv0_c6 (v : ℕ) (hv : 0 < v) :
    domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := by
  simp [domTag, domTagList, domTagBP, Dprin, BZero,
    show (v : ℕ∞) ≠ 0 by simpa using (Nat.ne_of_gt hv), ENat.coe_ne_top]

private theorem operB_Dv0_id_c6 (v : ℕ) (z : BT) (hv : 0 < v) :
    operB (Dprin (v : ℕ∞) BZero) z = z := by
  have hv0 : (v : ℕ∞) ≠ 0 := by simpa using (Nat.ne_of_gt hv)
  simp [operB, bOperCore, Dprin, BZero, hv0]

private theorem xseq_zero_c6 (b : BT) (w : ℕ∞) : xseq b w 0 = Dprin w BZero := by
  simp [xseq, bOperCore]

private theorem xseq_succ_c6 (b : BT) (w : ℕ∞) (i : ℕ) :
    xseq b w (i + 1) = Dprin w (operB b (xseq b w i)) := by
  show bOperCore (.xseq b w (i + 1)) =
    Dprin w (bOperCore (.term b (bOperCore (.xseq b w i))))
  rw [bOperCore.eq_def]

/-- `b = D_v 0` (`v > 0`) は `operB` に対して恒等なので、A23 訂正後の補助列 `x_i` は
純粋な `D_w` の塔になる。 -/
private theorem xseq_Dv0_tower_c6 (v : ℕ) (hv : 0 < v) (w : ℕ∞) :
    ∀ i, xseq (Dprin (v : ℕ∞) BZero) w i = (Dprin w)^[i + 1] BZero := by
  intro i
  induction i with
  | zero => simpa using xseq_zero_c6 (Dprin (v : ℕ∞) BZero) w
  | succ i ih =>
      rw [xseq_succ_c6, operB_Dv0_id_c6 v _ hv, ih,
        Function.iterate_succ_apply' (Dprin w) (i + 1) BZero]

/-- Isabelle `operB_Du_Dv0_kind1_eval`: `u < v` なら `D_u(D_v 0)` は第 1 種で、
その基本列は内側の塔をひとつずつ伸ばす。 -/
private theorem operB_Du_Dv0_kind1_eval_c6 (u v m : ℕ) (huv : u < v) :
    operB (Dprin (u : ℕ∞) (Dprin (v : ℕ∞) BZero)) (numBT m)
      = Dprin (u : ℕ∞) ((Dprin ((v - 1 : ℕ) : ℕ∞))^[m + 1] BZero) := by
  have hv : 0 < v := by omega
  have hne : Dprin (v : ℕ∞) BZero ≠ BZero := by simp [Dprin, BZero]
  have htag : domTag (Dprin (v : ℕ∞) BZero) = .below (v - 1) := domTag_Dv0_c6 v hv
  have hle : (u : ℕ∞) ≤ ((v - 1 : ℕ) : ℕ∞) := by
    norm_cast
    omega
  rw [operB_dprin_kind1 hne htag hle, numNat_numBT_c6,
    xseq_Dv0_tower_c6 v hv _ m, operB_Dv0_id_c6 v _ hv]

/-! ## `(1,1)` 対角ホストにおける交換と降下（無条件） -/

private theorem TPS_diagSeq_c6 (a b : ℕ) (hab : a ≤ b) : TPS (diagSeq a b) := by
  have h : (diagSeq a b).length = b + 1 - a := by simp [diagSeq]
  exact List.ne_nil_of_length_pos (by omega)

private theorem coe_sub_one_c6 (u j₁ : ℕ) (hj₁ : 1 < j₁) :
    ((u + j₁ - 1 : ℕ) : ℕ∞) = (u : ℕ∞) + (j₁ : ℕ∞) - 1 := by
  simp [ENat.coe_sub]

/-- Isabelle `m_8_6_diagSeq_condVI_commute`（`layerB/pss_wip.thy`:40305）。

`M = diagSeq u (u+j₁)`（`j₁ > 1`）は条件 (VI) の `(1,1)` 対角ホストであり、
`Trans M = D_u(D_{u+j₁} 0)` は二段の塔なので、`operator[]` の交換は
（一般ホストで条件 III/V/VI を塞ぐ marking-nesting 手術を一切使わずに）
**直接計算**で出る。原文の結論 (2) が `m_n = n-1` の**等式**として成立する形。 -/
theorem m_8_6_diagSeq_condVI_commute (u j₁ n : ℕ) (hj₁ : 1 < j₁) (hn : 0 < n) :
    Trans (oper (diagSeq u (u + j₁)) n)
      = operB (Trans (diagSeq u (u + j₁))) (numBT (n - 1)) := by
  have huv : u < u + j₁ := by omega
  have hTPS : TPS (diagSeq u (u + j₁)) := TPS_diagSeq_c6 u (u + j₁) (by omega)
  rw [diagSeq_Trans_fseq (diagSeq u (u + j₁)) u j₁ n rfl hTPS hn hj₁,
    diagSeq_Trans u (u + j₁) huv,
    operB_Du_Dv0_kind1_eval_c6 u (u + j₁) (n - 1) huv,
    coe_sub_one_c6 u j₁ hj₁]
  congr 2
  omega

/-- Isabelle `m_8_6_diagSeq_condVI_descent`（`layerB/pss_wip.thy`:40331）。
降下エンジンの非空虚な payoff: `(1,1)` 対角ホストでの `Trans(M[n]) < Trans(M)`。
`n = 1` の脚も `operB (Trans M) (numBT 0)` として同じ 1 歩なので、`Pred` 分岐も
条件 (VI) の述語も要らない。 -/
theorem m_8_6_diagSeq_condVI_descent (u j₁ n : ℕ) (hj₁ : 1 < j₁) (hn : 0 < n) :
    lessBT (Trans (oper (diagSeq u (u + j₁)) n)) (Trans (diagSeq u (u + j₁))) = true := by
  have hTM : Trans (diagSeq u (u + j₁)) =
      Dprin (u : ℕ∞) (Dprin ((u + j₁ : ℕ) : ℕ∞) BZero) :=
    diagSeq_Trans u (u + j₁) (by omega)
  have hOT : Trans (diagSeq u (u + j₁)) ∈ OT_B := by
    rw [hTM]; exact OT_examples_2 u (u + j₁)
  have hTne : Trans (diagSeq u (u + j₁)) ≠ BZero := by
    rw [hTM]; simp [Dprin, BZero]
  rw [m_8_6_diagSeq_condVI_commute u j₁ n hj₁ hn]
  exact buchholz_fseq_lt _ _ hOT hTne

/-! ## 一般ホスト: 未移植ブリック 3 本（green-modulo） -/

/-- **名前付き仮定 (A)** — 許容 `j₀` の条件 (VI) ホストにおける `Trans(M[n])` と
`Trans(M)[m]` の塔閉形式。

Isabelle `c613x_condVI_exch_adm`（`layerB/pss_wip.thy`:73312、**証明済・無条件**）の
内部で確立される 2 つの平坦閉形式
```
flatMn : 1 ≤ n ⟹ flatBT (Trans (M[n]))              = s₁ @ flatBP (DB u (Dtower u (n-1))) @ b₁
ov     :          flatBT (operB (Trans M) (numBT m)) = s₁ @ flatBP (DB u (Dtower u (Suc m))) @ b₁
```
（`u = M_{1,j₀}`、`b₁` は全て `)`）を、Lean 側で扱いやすい `scb_decomp` の形に
束ねたもの。`Dtower u k` は `(Dprin u)^[k] BZero`。

この 2 式に至る Isabelle の道は、条件 (VI) が常に境界 regime `j₋₂+1 = j₁` であること
（`c6zx_condVI_oper_L`:72257 で `M[Suc n] = L_n`）＋ L 塔 `c6zx_L_tower`:72181 ＋
`c613x_operB_fseq_value`（第 1 種 scb の `operB` 値）であり、Lean 未移植の
`s84x_L`/`m_8_4_oper_props_5` 系（§8.4 の scb 分解クラスタ）に乗る。 -/
def CondVIAdmTowerScb : Prop :=
  ∀ (M : PS), STPS M → RTPS M → monoT M = true → transCondVI M = true →
    1 < Lng M - 1 → adm M (transJ0 M) = true →
    ∃ s₁ b₁ : List Sym,
      (∀ n, 1 ≤ n →
        scb_decomp (Trans (oper M n)) s₁
          (flatBT (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
            ((Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞))^[n - 1] BZero))) b₁) ∧
      (∀ m : ℕ,
        scb_decomp (operB (Trans M) (numBT m)) s₁
          (flatBT (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
            ((Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞))^[m + 1] BZero))) b₁)

/-- **名前付き仮定 (B)** — 非許容 `j₀` の条件 (VI) 交換。Isabelle
`c6nx_condVI_exch_nadm_uncond`（`layerB/pss_wip.thy`:76705、**証明済・無条件**）の
逐語転記（3 結論そのまま）。非許容側には `m_n = -1` の例外脚が無い。 -/
def CondVIExchNadm : Prop :=
  ∀ (M : PS), STPS M → RTPS M → monoT M = true → transCondVI M = true →
    1 < Lng M - 1 → ¬ (adm M (transJ0 M) = true) →
    (∀ n, 1 ≤ n → lessBT (Trans (oper M n)) (operB (Trans M) (numBT n)) = true) ∧
    (∀ n, 1 ≤ n → Trans (oper M n) = operB (Trans M) (numBT (n - 1))) ∧
    (∀ n, 1 ≤ n →
      lessBT (operB (Trans M) (numBT (n - 1))) (Trans (oper M (n + 1))) = true)

/-- **名前付き仮定 (C)** — §8.7 の `OT_B` 所属。Isabelle `p_8_7_Trans_preserves_OT`
（`pss_paper.thy`:2317）＝ `y5_Trans_OT_B`（`layerC/pss_scratch.thy`、**証明済・仮定ゼロ**）
の逐語転記。エンジンが [Buc1] Lemma 3.2(a) を呼ぶために要る唯一の外部事実。 -/
def TransPreservesOT : Prop := ∀ (M : PS), STPS M → Trans M ∈ OT_B

/-! ## 補助（(1) の零化脚で使う `T_B` 事実） -/

private theorem zero_addBT_c6 (t : BT) : addBT BZero t = t := by
  rcases t with ⟨ps⟩
  rfl

private theorem BZero_mem_T_B_c6 : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem leBT_refl_c6 (a : BT) : leBT a a = true := by
  simp [leBT]

/-- 条件 (VI) の第 2 成分: `M_{1,j₀} + 1 = M_{1,j₁}`。 -/
private theorem condVI_entry_succ_c6 (M : PS) (hcond : transCondVI M = true) :
    entry M 1 (transJ0 M) + 1 = entry M 1 (Lng M - 1) := by
  simp only [transCondVI, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    lastIdx, lastParent] at hcond
  exact hcond.1.2

/-! ## 原文の命題（green-modulo (A)/(B)/(C)） -/

/-- **§8.6 命題（条件 (VI) の下での `Trans` と基本列の交換関係）**
（原文 `tmp/content.md` 5484、Isabelle 逐語 `p_8_6_Trans_fseq_condVI`
＝ `isabelle/pss_paper.thy`:2218）。

`M ∈ ST_PS ∩ PT_PS`、`n ∈ ℕ₊`、`j₀ = parent M 0 (Lng M - 1)`、`j₁ > 1`、
条件 (VI) の下で、`j₀` が `M` 許容なら `m_n := n-2`、非許容なら `m_n := n-1` と置くと:

* (1) `m_n = -1`（＝ `n = 1` かつ `j₀` 許容）なら、ある `k` が存在して
  `1 < k ≤ M_{1,j₁}+1` かつ `Trans(M[n]) = Trans(M)[0]^k`;
* (2) `m_n ≥ 0` なら `Trans(M[n]) = Trans(M)[m_n]`;
* (3) `Trans(M[n]) < Trans(M)`。

Isabelle 版の modelling note どおり、整数値の添字 `m_n ∈ ℕ ∪ {-1}` は `n` と
`adm M j₀` で完全に決まるので `Trans` 再帰の内部記号を露出せずに転記できる。

**訂正**: なし。A34/A37（「(1) が偽」）は取り下げ済で、原文は印字どおり真
（`corrections-old.md`:123/154。A23 訂正後の `operB` で 445/445）。

(1) は Isabelle 側にも逐語の証明が無い（`c613x_condVI_exch_adm` が出すのは
`n=1` 脚では狭義不等式 `Trans(M[1]) < Trans(M)[0]` だけ）。ここでは原文 5735 の道
——`Trans(M[1]) = s₁ D_u 0 b₁`、`Trans(M)[0] = s₁ D_u(D_u 0) b₁` に
**順序数項の末尾単項の零化可能性**（`trailing_principal_annihilable`、A23 訂正後の
上界 `0 < k' ≤ M_{1,j₁}`）を当て、`k := k'+1`——を Lean で実行して閉じている。
(3) は原文どおり (1)(2) と [Buc1] Lemma 3.2 から
（`m_8_6_TransCondVI_oper_descend_engine`）。 -/
theorem p_8_6_Trans_fseq_condVI (M : PS) (n : ℕ)
    (hA : CondVIAdmTowerScb) (hB : CondVIExchNadm) (hC : TransPreservesOT)
    (hST : STPS M) (hR : RTPS M) (hmono : monoT M = true) (hn : 0 < n)
    (hj₁ : 1 < Lng M - 1) (hcond : transCondVI M = true) :
    (n = 1 ∧ adm M (parent M 0 (Lng M - 1)) = true →
        ∃ k, 1 < k ∧ k ≤ entry M 1 (Lng M - 1) + 1 ∧
          Trans (oper M n) = ((fun a => operB a (numBT 0))^[k]) (Trans M))
      ∧ (¬ (n = 1 ∧ adm M (parent M 0 (Lng M - 1)) = true) →
        Trans (oper M n) =
          operB (Trans M)
            (numBT (if adm M (parent M 0 (Lng M - 1)) then n - 2 else n - 1)))
      ∧ lessBT (Trans (oper M n)) (Trans M) = true := by
  have hj0 : parent M 0 (Lng M - 1) = transJ0 M := rfl
  rw [hj0]
  have hTOT : Trans M ∈ OT_B := hC M hST
  -- `Trans M ≠ 0`（`j₁ > 1` から。原文 5670 の一行）
  have hM : TPS M := List.ne_nil_of_length_pos (by
    have h : 1 < Lng M := by omega
    have h' : 1 < M.length := h
    omega)
  have hz : zeroT M = false := by
    have h1 : ¬ (M.length = 1) := by
      have h : 1 < Lng M := by omega
      have h' : 1 < M.length := h
      omega
    have h1' : ¬ (Lng M = 1) := h1
    simp [zeroT, h1']
  have hTne : Trans M ≠ BZero := by
    intro h
    have hzz := (Trans_preserves_zeroT M hM).mpr h
    rw [hz] at hzz
    exact Bool.noConfusion hzz
  -- 結論 (2)
  have key2 : ¬ (n = 1 ∧ adm M (transJ0 M) = true) →
      Trans (oper M n) =
        operB (Trans M) (numBT (if adm M (transJ0 M) then n - 2 else n - 1)) := by
    intro hnot
    by_cases hadm : adm M (transJ0 M) = true
    · -- 許容 `j₀`: `n ≥ 2`（`n = 1` は (1) の脚として除外済）
      have hn2 : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · exact absurd ⟨by omega, hadm⟩ hnot
        · exact h
      obtain ⟨s₁, b₁, hMn, hop⟩ := hA M hST hR hmono hcond hj₁ hadm
      have h1 := hMn n (by omega)
      have h2 := hop (n - 2)
      have hidx : n - 2 + 1 = n - 1 := by omega
      rw [hidx] at h2
      simp only [hadm, if_true]
      exact flatBT_injective (h1.1.trans h2.1.symm)
    · -- 非許容 `j₀`: `m_n = n-1`、例外脚なし
      have hf : adm M (transJ0 M) = false := Bool.eq_false_of_not_eq_true hadm
      have hBn := (hB M hST hR hmono hcond hj₁ hadm).2.1 n (by omega)
      simp only [hf, Bool.false_eq_true, if_false]
      exact hBn
  -- 結論 (3): 原文どおり (1)(2) と [Buc1] Lemma 3.2 から（エンジン）
  have key3 : lessBT (Trans (oper M n)) (Trans M) = true := by
    refine m_8_6_TransCondVI_oper_descend_engine M n hST hR hmono hj₁ hcond hn hTOT ?_
    intro hn1
    refine ⟨if adm M (transJ0 M) then n - 2 else n - 1, ?_⟩
    rw [key2 (by rintro ⟨h, -⟩; omega)]
    exact leBT_refl_c6 _
  refine ⟨?_, key2, key3⟩
  -- 結論 (1): `n = 1` かつ `j₀` 許容（`m_n = -1`）の脚
  rintro ⟨rfl, hadm⟩
  obtain ⟨s₁, b₁, hMn, hop⟩ := hA M hST hR hmono hcond hj₁ hadm
  have h1 : scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) BZero)) b₁ := by
    have := hMn 1 (le_refl 1)
    simpa using this
  have h0 : scb_decomp (operB (Trans M) (numBT 0)) s₁
      (flatBT (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
        (addBT BZero (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) BZero)))) b₁ := by
    have := hop 0
    rw [zero_addBT_c6]
    simpa using this
  have hTB : operB (Trans M) (numBT 0) ∈ T_B :=
    (buchholz_fseq_closed (Trans M) 0 hTOT hTne).2
  obtain ⟨k, hkpos, hkle, hk⟩ :=
    trailing_principal_annihilable (operB (Trans M) (numBT 0)) BZero s₁ b₁
      (entry M 1 (transJ0 M)) (entry M 1 (transJ0 M)) hTB BZero_mem_T_B_c6 h0
  have hval : Trans (oper M 1) =
      ((fun a => operB a (numBT 0))^[k]) (operB (Trans M) (numBT 0)) :=
    flatBT_injective (h1.1.trans hk.1.symm)
  refine ⟨k + 1, by omega, ?_, ?_⟩
  · have := condVI_entry_succ_c6 M hcond
    omega
  · rw [hval, Function.iterate_succ_apply]

#print axioms m_8_6_TransCondVI_oper_descend_engine
#print axioms m_8_6_diagSeq_condVI_commute
#print axioms m_8_6_diagSeq_condVI_descent
#print axioms p_8_6_Trans_fseq_condVI

end PSS
