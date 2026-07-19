import «8».«8.4-kind1-shape»
import «8».«8.4-np-c2decomp»
import «8».«8.4-exch84-scbdecomp»

/-!
# §8.4 補題群（条件(III)～(VI)の下での各種 scb 分解）

原文 `tmp/content.md` の §8.4「条件(III)か(IV)の下での展開規則」に含まれる
scb 分解補題群を集約する p ファイル。対応する原文行と Isabelle 逐語文は以下：

| 原文行 | 補題名 | Isabelle |
|---|---|---|
| 4507 | 補題（条件(III)～(VI)の下での `Trans` と scb 分解の関係） | `pss_paper.thy:1968` (DEFERRED) |
| 4605 | 補題（条件(III)～(V)の下での切片の scb 分解） | `pss_paper.thy:1980` (DEFERRED) |
| 4702 / 4726 | 補題（条件(III)～(V)の下での各種 scb 分解） | `pss_paper.thy:1986` (DEFERRED) |
| 4802 | 補題（条件(III)か(IV)の下での各種 scb 分解） | `pss_paper.thy:1994` (DEFERRED) |

## Isabelle 側が DEFERRED である理由と Lean 側の露出

Isabelle 藍図はこのクラスタ全体を **DEFERRED**（`text` 注記のみ）としている。原文の
補題はいずれも `Trans` 再帰の**内部局所記号** \(c_1, c_2, t_2\) と scb 文字列
\(s_1, b_1, s'_1, b'_1, s'_0, b'_0, s'_2, b'_2\) を通じて述べられており、これらは
Isabelle 側では別関数として露出していない（§7.3 の deferred な命題（\(c_1\) と
\(c_2\) の大小関係）と同じ事情）。

Lean 側はこの内部記号を関数として**露出済み**である
(`lean/PSS/Trans.lean`)：`transC1`(=\(c_1\)), `transC2`(=\(c_2\)),
`transT2`(=\(t_2\)), `transV`(=\(v\)), `transJ0`(=\(j_0\)),
`transJ1`(=\(j_1\)), `transJm1`(=\(j_{-1}\))。さらに §8.4 固有の切片語彙
`s84x_jm2`(=\(j_{-2}=\textrm{parent } M\ 1\ j_1\)),
`s84x_jm3`(=\(j_{-3}=\textrm{Adm}_M(j_{-2})\)),
`s84x_N`(=\(N=(M_j)_{j=j_{-3}}^{j_1}\)),
`s84x_Np`(=\(N'=(M_j)_{j=j_{-2}}^{j_1}\)) も定義済み
(`lean/8/8.4-s84x-vocab-run.lean`)。したがって本クラスタは Lean 側では statable で
あり、原文の scb 分解内容を忠実に述べる公開定理として本ファイルに集約する。ただし
scb **文字列** \(s_1, b_1, \dots\) 自身は依然として存在束縛量（関数ではない）であ
るため、\(\textrm{Trans}(L_n)\) / \(\textrm{Trans}(M[n])\) の閉形式（原文 (4)/(5)）は
文字列の連結・冪として与えられ、単一自己完結定理としては未組立（下記 RESIDUAL）。

## 本ファイルが供給する公開定理（既存資産の再露出）

原文 §8.4 の scb 分解「内容」を忠実に実現する、既に無条件・公理クリーンに証明済みの
資産を再露出する。いずれも `#print axioms` = `[propext, Classical.choice, Quot.sound]`。

- `p_8_4_scbdecomp_c1c2_base_sd4` — `Trans M` の基底 c1/c2 scb 分解（原文 §7.3/§8.4
  で全補題が土台にする「\((s_1,c_2,b_1)\) が \(\textrm{Trans}(M)\) の scb 分解、
  \((s_1,c_1,b_1)\) が \(\textrm{Trans}(\textrm{Pred}(M))\) の scb 分解」）。
  再露出元 `Trans_c1_c2_decomp` (`8.3-condII-masterCF`)。
- `p_8_4_scbdecomp_TransN_kind1_exists_sd4` — 原文 4507 補題（`Trans` と scb 分解の
  関係）の条件(III)/(IV) 具体化の**存在形（無条件）**：`Trans M` の穴
  `Trans (s84x_N M)`（＝ \(\textrm{Trans}(N)\)）による [Buc1] 第 1 種 scb 分解
  （`scb_kind1`）が存在する。基底 scb 分解の存在
  `scbBaseDecompExists_sd4_holds`（`Regs_jm3Marked_holds` ＋ `Mark_Trans_repr` ＋
  `Trans_Mark_mem_MarkedB` の dec1 エンジン）＋ 第 1 種昇格核 `kind1Shape_holds`
  (`8.4-kind1-shape`, Wave AF) の合成。付随して昇格核単体
  `p_8_4_scbdecomp_TransN_kind1_shape_sd4` も露出。
- `p_8_4_scbdecomp_Np_transport_sd4` — 原文 4605/4702 補題（切片の scb 分解）の
  中核：`Trans (s84x_N M)` の transC2 中心分解を `Trans (s84x_Np M)`
  （＝ \(N'\) 側）へ移送。核 `np_c2decomp_holds` (`8.4-np-c2decomp`)。
- `p_8_4_scbdecomp_c2shape_condIV_sd4` — 原文 4802 補題（各種 scb 分解, 条件(IV) 枝）
  の `c_2` 本体入れ子形状 `transC2 M = D_v(t₃ + D_{w}(t₄ + D_{v₁} 0_B))`。
  核 `Cnv_c2_shape_condIV_holds` (`8.4-exch84-scbdecomp`)。
- `p_8_4_scbdecomp_nested_hole_sd4` — 同補題の一様入れ子穴 surgery 対
  `(sB, bB)`。核 `Cnv_nested_hole_pair_holds` (`8.4-exch84-scbdecomp`)。

## 残差（precise）

- 原文 (4)/(5) の \(\textrm{Trans}(L_n)\) / \(\textrm{Trans}(M[n])\) 閉形式、および
  原文 4802 の 6 タプル `(s'_0,\dots,b'_0)` は、露出されない scb **文字列**の連結・
  冪による表示のため、単一自己完結定理としては未組立（Isabelle DEFERRED と同状態）。
  corpus 側では exch84 機構（`8.4-exch84-*`, `8.4-slice-ext-*`, `8.4-corner-*`）が
  条件付き Prop として分散所持しており、本ファイルはその葉を再露出する方針。

## 位置づけ

本クラスタは主定理 `p_8_7_termination`（無条件・sorry 0）を**gate しない**原文カバ
レッジである。

## 訂正

- **A5**（§6.6 命題（簡約性の切片への遺伝性）の前提強化）は本 §8.4 の証明中でも
  \(j'_0 \le \textrm{Joints}(M)_{J_1} \le \textrm{TrMax}(M)\) が満たされることを根拠に
  している（`corrections.md:270`）。
- **A11 / A12**（§7.2 scb 分解の合成則 (2) / 置換可能性）は本クラスタが用いる
  scb 分解の定義自体への訂正（`corrections.md:470`, `:505`）。
-/

namespace PSS

/-! ## 0. 基底 scb 分解の存在（原文 4507 証明の dec1 エンジン） -/

/-- `Trans M` の穴 `Trans (s84x_N M)`（＝ \(\textrm{Trans}(N)\),
\(N=(M_j)_{j=j_{-3}}^{j_1}\)）による scb 分解の**存在**を述べる述語。原文 4507 の証明
「\((M,j_{-3}) \in T_{\textrm{PS}}^{\textrm{Marked}}\) より一意な \((s',b')\) が存在し
\((s',\textrm{Mark}(M,j'_{-2}),b')\) が \(\textrm{Trans}(M)\) の scb 分解、Mark の Trans
表示より \((s',\textrm{Trans}(N),b')\)」に対応。 -/
def ScbBaseDecompExists_sd4 : Prop :=
  ∀ (M : PS), STPS M → hasParent M 1 (Lng M - 1) = true →
    ∃ s b : List Sym, scb_decomp (Trans M) s (flatBT (Trans (s84x_N M))) b

/-- **基底 scb 分解の存在（無条件）**。dec1 エンジン: \((M,j_{-3}) \in\) `Marked`
（`Regs_jm3Marked_holds`）＋ `Mark M j₋₃ = Trans N`（`Mark_Trans_repr`, §7.4）＋
`(Trans M, Mark M j₋₃) ∈ MarkedB`（`Trans_Mark_mem_MarkedB`）。Isabelle
`s84d_jm3_Marked` 系。 -/
theorem scbBaseDecompExists_sd4_holds : ScbBaseDecompExists_sd4 := by
  intro M hST hp
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  obtain ⟨mM3, jm3le, jm2lt⟩ := Regs_jm3Marked_holds M hMR hMT hp
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_of_le_of_lt jm3le jm2lt
  have reprM : Mark M (s84x_jm3 M) = Trans (s84x_N M) :=
    Mark_Trans_repr M (s84x_jm3 M) mM3 hMR jm3lt
  obtain ⟨u0, v0, hd0⟩ := Trans_Mark_mem_MarkedB M (s84x_jm3 M) hMR mM3
  rw [reprM] at hd0
  exact ⟨u0, v0, hd0⟩

#print axioms scbBaseDecompExists_sd4_holds

/-! ## 1. 基底 c1/c2 scb 分解（原文 §7.3/§8.4 の土台） -/

/-- **基底 c1/c2 scb 分解**（§8.4 の全 scb 分解補題が土台にする）。単項ホスト
`M \in RT_{PS}`（`monoT`, `Lng M > 1`, `Trans(Pred M) ≠ 0_B`）に対し、共通の
scb 対 `(s,b)` が存在し `(s,c_1,b)` は `Trans(Pred M)` の、`(s,c_2,b)` は
`Trans(M)` の scb 分解になる。ここで `c_1 = transC1 M`, `c_2 = transC2 M`。
再露出元 `Trans_c1_c2_decomp` (`8.3-condII-masterCF`, 無仮定 `replaceScb_spec` 経由)。 -/
theorem p_8_4_scbdecomp_c1c2_base_sd4 (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hlen : 1 < Lng M) (ht₁ : Trans (Pred M) ≠ BZero) :
    ∃ s b : List Sym,
      scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b ∧
      scb_decomp (Trans M) s (flatBT (transC2 M)) b :=
  Trans_c1_c2_decomp M hR hmono hlen ht₁

#print axioms p_8_4_scbdecomp_c1c2_base_sd4

/-! ## 2. 原文 4507 補題（`Trans` と scb 分解の関係, 条件(III)/(IV) 具体化） -/

/-- **原文 4507「補題（条件(III)～(VI)の下での `Trans` と scb 分解の関係）」の
条件(III)/(IV) 昇格核**。`Trans M` の穴 `Trans (s84x_N M)`（＝ \(\textrm{Trans}(N)\),
\(N=(M_j)_{j=j_{-3}}^{j_1}\)）による scb 分解 `hd` が与えられたとき、それは [Buc1]
**第 1 種** scb 分解（`scb_kind1`）である。再露出元 `kind1Shape_holds`
(`8.4-kind1-shape`, Wave AF)。 -/
theorem p_8_4_scbdecomp_TransN_kind1_shape_sd4
    (M : PS) (u0 v0 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hp : hasParent M 1 (Lng M - 1) = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondIII M = true ∨ transCondIV M = true)
    (hd : scb_decomp (Trans M) u0 (flatBT (Trans (s84x_N M))) v0) :
    scb_kind1 (Trans M) u0 (flatBT (Trans (s84x_N M))) v0 :=
  kind1Shape_holds M u0 v0 hST hmono hp hj1 hcond hd

#print axioms p_8_4_scbdecomp_TransN_kind1_shape_sd4

/-- **原文 4507 補題の存在形（条件(III)/(IV) 具体化, 無条件）**。`Trans M` の穴
`Trans (s84x_N M)`（＝ \(\textrm{Trans}(N)\)）による [Buc1] **第 1 種** scb 分解が
存在する。原文の「一意な \((s',b')\) が存在して \((s',\textrm{Trans}(N),b')\) は
\(\textrm{Trans}(M)\) の第 1 種 scb 分解」に対応（本定理は**存在部分**のみ主張。
一意性は scb 分解の一意性 `scb_unique_decomp_unconditional` から従うが未主張）。基底
存在 `scbBaseDecompExists_sd4_holds` ＋ 昇格核 `kind1Shape_holds` の合成。 -/
theorem p_8_4_scbdecomp_TransN_kind1_exists_sd4
    (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    ∃ s b : List Sym, scb_kind1 (Trans M) s (flatBT (Trans (s84x_N M))) b := by
  obtain ⟨s, b, hd⟩ := scbBaseDecompExists_sd4_holds M hST hp
  exact ⟨s, b, kind1Shape_holds M s b hST hmono hp hj1 hcond hd⟩

#print axioms p_8_4_scbdecomp_TransN_kind1_exists_sd4

/-! ## 3. 原文 4605/4702 補題（切片の scb 分解, transC2 移送核） -/

/-- **原文 4605/4702「切片の scb 分解」の transC2 移送核**。`Trans (s84x_N M)`
（＝ \(N\) 側）の transC2 中心 scb 分解を `Trans (s84x_Np M)`（＝ \(N'\) 側）へ移送
する。原文 (2)「\((D_{M_{1,j_{-2}}} s'_1, D_{M_{1,j_1}} 0, b'_1)\) は
\(\textrm{Trans}(N')\) の scb 分解」の中核（穴は共通の `transC2 M`）。
再露出元 `np_c2decomp_holds` (`8.4-np-c2decomp`)。 -/
theorem p_8_4_scbdecomp_Np_transport_sd4
    (M : PS) (s1 b1 : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hp : hasParent M 1 (Lng M - 1) = true)
    (hj1 : 1 < Lng M - 1) (hcond : transCondIII M = true ∨ transCondIV M = true)
    (hd : scb_decomp (Trans (s84x_N M))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: s1) (flatBT (transC2 M)) b1) :
    scb_decomp (Trans (s84x_Np M))
      (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: s1) (flatBT (transC2 M)) b1 :=
  np_c2decomp_holds M s1 b1 hST hmono hp hj1 hcond hd

#print axioms p_8_4_scbdecomp_Np_transport_sd4

/-! ## 4. 原文 4802 補題（各種 scb 分解, 条件(IV) 枝）の c2 本体形状と穴 surgery -/

/-- **原文 4802 補題の条件(IV) 枝: `c_2` 本体入れ子形状**。条件(IV) の下で
`transC2 M = D_v(t₃ + D_{w}(t₄ + D_{v₁} 0_B))`（形状二分付き）。原文の各種 scb
分解 (3)/(4) が用いる `c_2` の入れ子構造を与える。再露出元
`Cnv_c2_shape_condIV_holds` (`8.4-exch84-scbdecomp`)。 -/
theorem p_8_4_scbdecomp_c2shape_condIV_sd4
    (M : PS) (hST : STPS M) (hmono : monoT M = true) (hj1 : 1 < Lng M - 1)
    (hT1 : transT1 M ≠ BZero) (hcIV : transCondIV M = true) :
    ∃ t3 t4 : BT, t3 ∈ T_B ∧ t4 ∈ T_B ∧
      transC2 M = Dprin (transV M)
        (addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞)
          (addBT t4 (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)))) ∧
      ((t3 = transT2 M ∧ t4 = transT2 M)
       ∨ transT2 M = addBT t3 (Dprin ((entry M 1 (transJ0 M) : ℕ) : ℕ∞) t4)) :=
  Cnv_c2_shape_condIV_holds M hST hmono hj1 hT1 hcIV

#print axioms p_8_4_scbdecomp_c2shape_condIV_sd4

/-- **原文 4802 補題の条件(IV) 枝: 一様入れ子穴 surgery 対**。入れ子形状
`t₃ + D_w(t₄ + ·)` の穴 `·` に対し、穴内容 `c'` に依らない単一の surgery 対
`(sB, bB)` が存在して `(sB, c', bB)` が全体の scb 分解になる。原文 (4) の
`(D_{M_{1,j_{-2}}} s'_1 s'_2, D_{M_{1,j_{-2}}} 0, b'_2 b'_1)` 合成 surgery の一様版。
再露出元 `Cnv_nested_hole_pair_holds` (`8.4-exch84-scbdecomp`)。 -/
theorem p_8_4_scbdecomp_nested_hole_sd4
    (t3 t4 : BT) (w : ℕ∞) (ht4 : t4 ∈ T_B) :
    ∃ sB bB : List Sym, ∀ c' : BT, c' ∈ T_B → (∃ p, c' = BT.trm [p]) →
      scb_decomp (addBT t3 (Dprin w (addBT t4 c'))) sB (flatBT c') bB :=
  Cnv_nested_hole_pair_holds t3 t4 w ht4

#print axioms p_8_4_scbdecomp_nested_hole_sd4

end PSS
