import «8».«8.4-oper5-residual»
import «8».«8.4-parent-max»

/-!
# §8.4 補題（条件(III)〜(VI)の下での展開規則の基本性質）

原文: `tmp/content.md` 4389「補題（条件(III)〜(VI)の下での展開規則の基本性質）」。

## ⚠️ 名前クロスオーバー

`isabelle/pss_paper.thy:2017` の `p_8_4_oper_basic` は **別**補題（条件(III)か(IV)
の下での**基本列**の基本性質、Lean では `8.4-fseq-basic`）である。本ファイルの
対象はそれではなく、§8.4 の「**展開規則**の基本性質」（`pss_paper.thy:1955` で
partially DEFERRED と注記される補題）である。Isabelle の逐語形は設計図
`isabelle/layerB/pss_wip.thy` の `m_8_4_oper_props_1`〜`m_8_4_oper_props_5`
(wip:52810 / 52946 / 53230 / 53257 / 54005) に分割されている。

## 原文の主張（setup ＋ parts (1)–(5)）

任意の \(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\) に対し、`Trans` の再帰的
定義中に導入した記号（\(j_1 = \textrm{Lng}\,M - 1\)、\(j_0 = \) 行0親、
\(j_{-2} = \) 行1親 `s84x_jm2 M = parent M 1 j₁`）を用い、
\((1,j_{-2}) <_M^{\textrm{Next}} (1,j_1)\) を満たす一意な \(j_{-2}\) が存在する
（`hasParent M 1 (Lng M - 1)`）とし、
\(N' := (M_j)_{j=j_{-2}}^{j_1}\) = `s84x_Np M`、
\(L' := (M'_j)_{j=j_{-2}}^{j_1}\) = `s84x_Lp M`、
\(L_n := M[n] \oplus ((M_{0,j_{-2}}+n(M_{0,j_1}-M_{0,j_{-2}}),M_{1,j_{-2}}))\)
= `s84x_L M n` と置くと、\(j_1 > 1\)（`1 < Lng M - 1`）ならば：

- (1) \(M\) が (III)/(IV) を満たすならば \(j_{-2} < j_0\)、\(M\) が (V)/(VI) を
  満たすならば \(j_{-2} = j_0\)。
- (2) 任意の \(n \in \mathbb{N}_{+}\) に対し \(L_n\) は簡約かつ単項。
- (3) \(\leq_M\) と \(\leq_{L_1}\) の \((\{0,1\}\times\mathbb{N})\setminus\{(1,j_1)\}\)
  への制限は一致する。
- (4) 「(VI) を満たすかまたは \(j_0\) が \(M\) 許容」ならば \(L_1\) は (I)/(III)、
  「(VI) を満たさずかつ \(j_0\) が非 \(M\) 許容」ならば \(L_1\) は (II)/(IV)。
- (5) 任意の \(n \in \mathbb{N}_{+}\) に対し \(n > 1\) ならば一意な \((s',b')\) が
  存在して (5-1)〜(5-3) を満たす。

## 訂正

- **A31**（`corrections.md:967`）: part (5-3) は \(\textrm{Pred}(N')\) が零項の
  とき偽（ガード欠落）。原文
  「\((s',\textrm{Trans}(\textrm{Pred}(N')),b')\) は \(\textrm{Trans}(M[n])\) の
  scb 分解」を、訂正案「\(\textrm{Pred}(N')\) が**零項でないならば** …」の形で
  述べる（反例 \(M=((0,0),(1,1),(2,0),(3,1))\)、\(n=2\)：`Trans (M[2]) ≠ 0` だが
  中心 `Trans (Pred N') = 0` は単項でない）。本ファイルの part (5) は
  `oper_props_5_unconditional`（`8.4-oper5-residual`）へ委譲し、この形の (5-3)
  ガードを既に内包する。

## `PT_PS` の展開

`M ∈ PT_PS` は `PT_PS = {M. M ∈ T_PS ∧ monoT M}`（`pss_defs.thy:240`）で展開する
（Lean 側に `PTPS` は無い。`STPS M` ＋ `monoT M = true` で表す。`TPS` は `STPS`
から従う）。

## 供給（本ファイルで証明する公開定理）

- **part (1)** 完全（両枝）:
  - `oper_rule_basic_part1_IIIIV`（(III)/(IV) → \(j_{-2} < j_0\)）=
    `regs_jm2_lt_transJ0_holds`（`8.4-parent-max`、Isabelle `m_8_4_oper_props_1(1)`）。
  - `oper_rule_basic_part1_VVI`（(V)/(VI) → \(j_{-2} = j_0\)）= Isabelle
    `m_8_4_oper_props_1(2)` の中核 `s84c1_e1lt_imp_jm2_eq_j0` (wip:52773) を移植
    （行1親の一意性）。
- **part (2)** 簡約性のみ: `oper_rule_basic_part2_reduced` = `RTPS_s84x_L`
  （`8.4-oper5-residual`、Isabelle `m_8_4_oper_props_2(1)`）。
- **part (5)** 完全（A31 ガード内包）: `oper_rule_basic_part5` =
  `oper_props_5_unconditional`（`8.4-oper5-residual`、Isabelle
  `m_8_4_oper_props_5` を残差無しに閉じたもの）。§8.4 注記どおり本補題の
  load-bearing な内容は (5)。

## 未転記（largest green prefix、`sorry` を残さないための省略）

以下は原文の主張だが、本ファイルでは公開しない。理由は Isabelle 設計図
（`pss_paper.thy:1955`）が「(1)–(4) は transcribable だが article-internal な
列 \(L'\)/\(L_n\) を明示構築する必要があり、load-bearing な (5) と 1 本の補題に
織り込まれている」と注記するとおり、Lean 側の対応する補助群が private のまま
公開入口を持たないため：

- **part (2) 単項性** = Isabelle `m_8_4_oper_props_2(2)`（`monoT (s84x_L M n)`）。
  基本列の単項性保存（非複項性と基本列の関係(2)）＋単項性の始切片への遺伝性の
  連鎖が要り、`monoT (oper M (n+1))` の一般形（cond III–VI 共通）が Lean で
  公開されていない。
- **part (3)** = Isabelle `m_8_4_oper_props_3`（\(\leq_M\)/\(\leq_{L_1}\) の
  \((\{0,1\}\times\mathbb{N})\setminus\{(1,j_1)\}\) 上一致）。`8.4-l1-slice-data`
  の private `_l1` 合同群が対応するが未公開。
- **part (4)** = Isabelle `m_8_4_oper_props_4`（\(L_1\) の条件レジーム）。同上
  （`8.4-l1-slice-data` の private レジーム解析）。

- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  公開 4 定理 = part (1) 両枝 ＋ part (2) 簡約性 ＋ part (5)。
- Private helper suffix: `_ob`。
-/

namespace PSS

/-! ## part (1)（条件(III)/(IV)枝） — Isabelle `m_8_4_oper_props_1(1)` (wip:52810)

条件 (III) か (IV) を満たすならば、行1の親 \(j_{-2}\) は行0の親 \(j_0\) より真に
手前にある。 -/
theorem oper_rule_basic_part1_IIIIV (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    s84x_jm2 M < transJ0 M :=
  regs_jm2_lt_transJ0_holds M hST hmono hp hj1 hcond

/-! ## part (1)（条件(V)/(VI)枝） — Isabelle `m_8_4_oper_props_1(2)` (wip:52810)

条件 (V) か (VI) を満たすならば、行1の親 \(j_{-2}\) は行0の親 \(j_0\) に一致する。
Isabelle の `s84c1_e1lt_imp_jm2_eq_j0` (wip:52773) を移植する（行1親の一意性で
\(j_0\) が行1親であることを示す）。 -/

/-- Isabelle `s84c1_anc_le_j0` (wip:52735) の行0版（`8.4-parent-max` の private
`s84c1_anc_le_j0_pm` の複製）。`le0 M j (Lng M-1)` かつ `j < Lng M-1` なら
`j ≤ transJ0 M`。 -/
private theorem anc_le_j0_ob (M : PS) (hMT : TPS M) (hmono : monoT M = true)
    (j1gt : 0 < Lng M - 1) {j : ℕ}
    (jle : le0 M j (Lng M - 1) = true) (jlt : j < Lng M - 1) :
    j ≤ transJ0 M := by
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hnextR0 : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hleR : leR M 0 j (Lng M - 1) = true := by simpa [leR] using jle
  have hgrow : entry M 0 j < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M j (Lng M - 1) (Lng M - 1) hMT jlt (le_refl _) hleR
  exact nextR0_largest_below M (transJ0 M) j (Lng M - 1) hnextR0 jlt hgrow

/-- `nextrel0 M a b` から `le0 M a b`（`8.3-kind0-branch-rule` の private
`le0_of_nextrel0_83` の複製）。 -/
private theorem le0_of_nextrel0_ob (M : PS) (a b : ℕ)
    (h : nextrel0 M a b = true) : le0 M a b = true := by
  have hh := (nextR_implies_row0 M 0 a b (by simpa [nextR] using h)).2
  simpa [leR] using hh

/-- Isabelle `m_8_4_oper_props_1(2)` (wip:52810) の中核 `s84c1_e1lt_imp_jm2_eq_j0`
(wip:52773)。行1の親 `j₋₂` に対し `entry M 1 (transJ0 M) < entry M 1 (Lng M-1)`
ならば `j₋₂ = transJ0 M`。 -/
private theorem e1lt_imp_jm2_eq_j0_ob (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hlt : entry M 1 (transJ0 M) < entry M 1 (Lng M - 1)) :
    s84x_jm2 M = transJ0 M := by
  have hMT : TPS M := RTPS_TPS M (STPS_RTPS M hST)
  have j1gt : 0 < Lng M - 1 := by omega
  -- `nextR M 0 (transJ0 M) (Lng M-1)`（行0親）
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hnextR0 : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hnr0 : nextrel0 M (transJ0 M) (Lng M - 1) = true := by
    simpa [nextR] using hnextR0
  have hj0lt : transJ0 M < Lng M - 1 := by
    have hh := hnr0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hle0j0 : le0 M (transJ0 M) (Lng M - 1) = true := le0_of_nextrel0_ob M _ _ hnr0
  have hj1L : Lng M - 1 < Lng M := by omega
  have hj0L : transJ0 M < Lng M := by omega
  -- `nextrel1 M (transJ0 M) (Lng M-1)`
  have hnr1 : nextrel1 M (transJ0 M) (Lng M - 1) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨hj0L, hj1L⟩, hj0lt⟩, hlt⟩, hle0j0⟩, ?_⟩
    intro k hk
    by_cases hak : transJ0 M < k
    · by_cases hkle : le0 M k (Lng M - 1) = true
      · -- 内容: `entry M 1 (Lng M-1) ≤ entry M 1 k`
        have hle_k : entry M 1 (Lng M - 1) ≤ entry M 1 k := by
          rcases Nat.lt_trichotomy k (Lng M - 1) with hkc | hkc | hkc
          · exact absurd (anc_le_j0_ob M hMT hmono j1gt hkle hkc) (by omega)
          · subst hkc; exact le_refl _
          · exact absurd (le0_index_fseq hkle) (by omega)
        simp [hak, hkle, hle_k]
      · simp [hak, hkle]
    · simp [hak]
  have hnextR1 : nextR M 1 (transJ0 M) (Lng M - 1) = true := by
    simpa [nextR] using hnr1
  -- 行1親の一意性で `j₋₂ = transJ0 M`
  obtain ⟨_, _, huniq⟩ := (hasParent_iff_unique_fseq M 1 (Lng M - 1)).mp hp
  rw [huniq (s84x_jm2 M) (s84c1_nextR1_jm2 M hp), huniq (transJ0 M) hnextR1]

theorem oper_rule_basic_part1_VVI (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondV M = true ∨ transCondVI M = true) :
    s84x_jm2 M = transJ0 M := by
  -- 条件(V)/(VI): `M_{1,j₀} + 1 = M_{1,j₁}`、特に `M_{1,j₀} < M_{1,j₁}`
  have hlt : entry M 1 (transJ0 M) < entry M 1 (Lng M - 1) := by
    simp only [transJ0]
    rcases hcond with h | h
    · unfold transCondV at h
      simp only [lastIdx, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      omega
    · unfold transCondVI at h
      simp only [lastIdx, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      omega
  exact e1lt_imp_jm2_eq_j0_ob M hST hmono hp hj1 hlt

/-! ## part (2)（簡約性） — Isabelle `m_8_4_oper_props_2(1)` (wip:52946)

各 \(n \ge 1\) に対し \(L_n\) は簡約ペア数列。 -/
theorem oper_rule_basic_part2_reduced (M : PS) (n : ℕ)
    (hST : STPS M) (hp : hasParent M 1 (Lng M - 1) = true)
    (hj1 : 1 < Lng M - 1) (hn : 1 ≤ n) :
    RTPS (s84x_L M n) :=
  RTPS_s84x_L M n hST hp hj1 hn

/-! ## part (5) — Isabelle `m_8_4_oper_props_5` (wip:54005) ＋ 訂正 A31

各 \(n > 1\) に対し一意な \((s',b')\) が存在して、
- (5-1) \((s', D_{M_{1,j_{-2}}} 0, b')\) は \(\textrm{Trans}(L_{n-1})\) の scb 分解、
- (5-2) \((s', \textrm{Trans}(L'), b')\) は \(\textrm{Trans}(L_n)\) の scb 分解、
- (5-3) [A31 ガード] \(\textrm{Pred}(N')\) が非零項ならば
  \((s', \textrm{Trans}(\textrm{Pred}(N')), b')\) は \(\textrm{Trans}(M[n])\) の
  scb 分解。 -/
theorem oper_rule_basic_part5 (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 < n) :
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_L M (n - 1))) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2
        ∧ scb_decomp (Trans (s84x_L M n)) sb.1 (flatBT (Trans (s84x_Lp M))) sb.2
        ∧ (¬ (zeroT (Pred (s84x_Np M)) = true) →
             scb_decomp (Trans (oper M n)) sb.1
               (flatBT (Trans (Pred (s84x_Np M)))) sb.2) :=
  oper_props_5_unconditional M n hST hmono hp hj1 hn

#print axioms oper_rule_basic_part1_IIIIV
#print axioms oper_rule_basic_part1_VVI
#print axioms oper_rule_basic_part2_reduced
#print axioms oper_rule_basic_part5

end PSS
