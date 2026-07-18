import «8».«8.4-oper-props5»

/-!
# §8.4 補題（条件(III)～(V)の下での右端の置き換えと `Trans` の関係）＋ 訂正 A30 / A31

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと
  `Trans` の関係）」(4265)。本体は parts (1)/(2)/(3) (4269–4273)、証明 4275–4387。
  同節の「補題（条件(III)～(VI)の下での展開規則の基本性質）」(4389) の part (5-3)
  が訂正 A31 の対象。
- 逐語: **なし**。`isabelle/pss_paper.thy`:1945 は本補題を **DEFERRED**（text-only
  note）とする。理由は原文が `Trans` の再帰的定義中の内部記号 `t₂` と条件付き
  `c`-形 `D_{M₁,j₀}(t₂ +_B D_{M₁,j₀} 0)` を露出せずに述べているため
  （"BLOCKING SYMBOLS: `t₂`, the conditional `c`-shape"）。Lean/Isabelle はこの
  露出を `transT2` / `transC2` と存在量化された `(s,b)` で行う。
- 訂正:
  * **A30**（`corrections.md`:936）: part (3) の scb 分解の中心 `D_{M₁,j₀}(t₂ +_B
    D_{M₁,j₀} 0)` は**長さ勘定で偽**。原文証明自身の結語（4371 / 4387）が両場合と
    もに part (2) と同一の中心 `D_{M₁,j₋₂} 0` を導いている。訂正形は
    (3) `⟹ (s, D_{M₁,j₋₂} 0, b)` は `Trans(L')` の scb 分解（part (2) と同一・無条件）。
    part (1) と `(s,b)` を共有する以上、`Trans(L')` の文字列長から中心の長さは
    part (2) の `D_{M₁,j₋₂} 0`（長さ 2）に一意に決まり、原文の `D_{M₁,j₀}(t₂ + …)`
    （長さ ≥ 3）にはなりえない。
  * **A31**（`corrections.md`:967）: 隣の補題「条件(III)～(VI)の下での展開規則の
    基本性質」part (5-3) は `Pred(N')` が零項のときガード欠落で偽。訂正形
    「`Pred(N')` が零項でないならば …」は既に `8.4-oper-props5` の
    `Oper5Result` (hC3 枝) にガード付きで移植済み。本ファイルは**原文形（ガード
    無し）の反例**のみ機械証明する。
- 設計図（house green-modulo, 8.5-scb-decompositions と同型）:
  DEFERRED 補題なので Isabelle 側にも `m_` 証明は無い。**Lean の勝ち筋**として
  訂正形を named Prop `Rightmost84ReplaceCorrected` で露出（green-modulo 残差、
  §8 停止性の臨界パス外）し、原文形の反例を有限 host 上で**完全機械証明**する。
  `_str`（host 非依存の長さ論法）＝ `8.5-scb-decompositions` の
  `scbdec_condV_part5_original_false_str` と同じ骨格。
- 依存（すべてビルド済み・committed）: «8».«8.4-oper-props5»（`s84x_jm2`/`s84x_Np`/
  `seg`/`entry`/`oper`/`Pred`/`Trans`/`STPS`/`STPS.diag`/`STPS.oper`/`diagSeq`/
  `monoT`/`hasParent`/`adm`/`parent`/`scb_decomp`/`isPTB_str`/`flatBT`/`flatBP`/
  `Dprin`/`BZero`/`addBT`/`Sym`/`dfree_BP`）。
- 数値検証: `python/red_model.py`（`oper`/`parent`/`seg`）＋`python/trans_model.py`
  （`Trans`/`scb_decomps`）。A30 host `M = (0,0)(1,1)(2,2)(2,1)`（`j₁=3, j₋₂=0,
  j₀=1`、`j₀` 非許容、標準形かつ単項）で part (1) 中心 `D_1 0` と part (2) 中心
  `D_0 0` が同一 `(s,b)` を共有（`scb_decomps` で確認）。A31 host `M =
  (0,0)(1,1)(2,0)(3,1)`, `n=2`: `Trans(Pred N') = 0`、`Trans(M[2]) ≠ 0`。
- ツリー項目: 補題（条件(III)～(V)の下での右端の置き換えと `Trans` の関係）(§8.4)。
- 状態: GREEN（sorry 0）。訂正形 `Rightmost84ReplaceCorrected` 上の green-modulo
  （named Prop、新規残差 1 本）。原文形の反例（A30/A31）と非空虚性は無条件。
-/

namespace PSS

/-! ## `L'` の定義（右端置き換え列）

`L' := (M_j)_{j=j₋₂}^{j₁-1} ⊕ ((M_{0,j₁}, M_{1,j₋₂}))`（原文 4267）。
ここで `j₁ = Lng M - 1`, `j₋₂ = s84x_jm2 M = parent M 1 j₁`。 -/
def rrLp (M : PS) : PS :=
  seg M (s84x_jm2 M) (Lng M - 2)
    ++ [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))]

/-! ## flatBT の長さ補題（長さ勘定＝A30 の核） -/

/-- 補正形の中心 `D_v 0` の文字列は常に長さ 2（`[D_v, Z]`）。 -/
private theorem two_flat_Dprin_BZero_rr (u : ℕ∞) :
    (flatBT (Dprin u BZero)).length = 2 := by
  simp [Dprin, flatBT, flatBP, BZero]

/-- `t₂ +_B D_v 0` の文字列は常に長さ ≥ 2（末尾 principal `D_v 0` を含むため）。 -/
private theorem two_le_flat_add_rr (u : ℕ∞) (t : BT) :
    2 ≤ (flatBT (addBT t (Dprin u BZero))).length := by
  obtain ⟨ps⟩ := t
  cases ps with
  | nil => simp [addBT, Dprin, BZero, flatBT, flatBP]
  | cons p rest =>
    have haddeq : addBT (BT.trm (p :: rest)) (Dprin u BZero)
        = BT.trm (p :: (rest ++ [BP.db u BZero])) := by
      simp [addBT, Dprin, BZero]
    rw [haddeq]
    cases rest with
    | nil =>
      simp only [List.nil_append, flatBT, List.length_append, List.length_cons]
      omega
    | cons q qs =>
      simp only [List.cons_append, flatBT, List.length_append, List.length_cons]
      omega

/-- **A30 の核**: 原文 part (3) の中心 `D_{M₁,j₀}(t₂ +_B D_{M₁,j₀} 0)` の文字列は、
`t₂` が何であれ長さ ≥ 3（補正形の中心 `D_{M₁,j₋₂} 0` の長さ 2 を超える）。 -/
private theorem three_le_orig_center_rr (u : ℕ∞) (t : BT) :
    3 ≤ (flatBT (Dprin u (addBT t (Dprin u BZero)))).length := by
  have hflat : flatBT (Dprin u (addBT t (Dprin u BZero)))
      = Sym.dsym u :: flatBT (addBT t (Dprin u BZero)) := by
    simp [Dprin, flatBT, flatBP]
  rw [hflat, List.length_cons]
  have := two_le_flat_add_rr u t
  omega

/-- 零項の文字列 `[Z]` は principal 項の文字列ではない（scb 分解の中心になれない）。 -/
private theorem not_isPTB_zero_rr : ¬ isPTB_str [Sym.zero] := by
  rintro ⟨p, _, hp⟩
  cases p with | db u a => simp [flatBP] at hp

/-! ## 訂正 A30 形（named Prop, green-modulo 残差）

原文 part (3) を訂正した形。part (2) と part (3) の条件は排他的かつ網羅的で、両場合
とも `Trans(L')` の scb 分解の中心が `D_{M₁,j₋₂} 0` になる（訂正 A30）。よって
part (2)/(3) は無条件の 1 本に統合される。`M ∈ PT_PS`（単項ペア数列）は `monoT M`。 -/
def Rightmost84ReplaceCorrected : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
    ∃! sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_Np M)) sb.1
          (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) sb.2 ∧
      scb_decomp (Trans (rrLp M)) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2

/-! ## A30 一般形の反証（host 非依存・長さ論法）

補正形 part (2) `(s, D_{M₁,j₋₂} 0, b)` が `Trans(L')` の scb 分解であるとき、同じ
`(s,b)` に対して原文形 part (3) の中心 `D_{M₁,j₀}(t₂ +_B D_{M₁,j₀} 0)` は scb 分解に
なりえない。中心の長さが 2（補正）と ≥ 3（原文）で食い違うため。 -/
theorem rr84_original_false_str (T : BT) (s b : List Sym) (u₂ u₀ : ℕ∞) (t₂ : BT)
    (hcorr : scb_decomp T s (flatBT (Dprin u₂ BZero)) b) :
    ¬ scb_decomp T s (flatBT (Dprin u₀ (addBT t₂ (Dprin u₀ BZero)))) b := by
  intro horig
  have l1 := congrArg List.length hcorr.1
  have l2 := congrArg List.length horig.1
  rw [List.length_append, List.length_append, two_flat_Dprin_BZero_rr] at l1
  rw [List.length_append, List.length_append] at l2
  have h3 := three_le_orig_center_rr u₀ t₂
  omega

/-! ## A30 具体 host（訂正形の充足性＋原文形の反証）

`M = (0,0)(1,1)(2,2)(2,1)`（標準形かつ単項、`python/red_model.py`）。
`j₁ = 3`, `j₋₂ = parent M 1 3 = 0`（＝ `N' = M`）, `j₀ = parent M 0 3 = 1`（非許容）。
`L' = (0,0)(1,1)(2,2)(2,0)`。共有手術対は `(s_rr, b_rr)`（`python/trans_model.py` の
`scb_decomps` で part (1) 中心 `D_1 0` と part (2) 中心 `D_0 0` が同一と確認）。 -/

def hostM30_rr : PS := [(0,0),(1,1),(2,2),(2,1)]

/-- 共有手術対の左文字列 `s`。`Trans(N') = s (D_1 0) b`, `Trans(L') = s (D_0 0) b`。 -/
def s_rr : List Sym :=
  [Sym.dsym (0:ℕ∞), Sym.lp, Sym.dsym (2:ℕ∞), Sym.zero, Sym.cm,
   Sym.dsym (1:ℕ∞), Sym.lp, Sym.dsym (2:ℕ∞), Sym.zero, Sym.cm]

/-- 共有手術対の右文字列 `b`（`)` の並び）。 -/
def b_rr : List Sym := [Sym.rp, Sym.rp]

/-- `M = (0,0)(1,1)(2,2)(2,1)` は標準形（`diagSeq 0 3` から `oper` 9 段）。 -/
theorem hostM30_STPS_rr : STPS hostM30_rr := by
  have h0 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,3)] := by
    have h := STPS.diag 0 3 (by norm_num)
    rwa [show diagSeq 0 3 = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,3)] from by decide] at h
  have h1 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,2)] := by
    have h := STPS.oper h0 2 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,3)] 2
      = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,2)] from by decide] at h
  have h2 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,1),(4,2)] := by
    have h := STPS.oper h1 2 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,2)] 2
      = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,1),(4,2)] from by decide] at h
  have h3 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,1)] := by
    have h := STPS.oper h2 1 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,1),(4,2)] 1
      = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,1)] from by decide] at h
  have h4 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0),(4,1),(5,2)] := by
    have h := STPS.oper h3 2 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,1)] 2
      = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0),(4,1),(5,2)] from by decide] at h
  have h5 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0),(4,1)] := by
    have h := STPS.oper h4 1 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0),(4,1),(5,2)] 1
      = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0),(4,1)] from by decide] at h
  have h6 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0)] := by
    have h := STPS.oper h5 1 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0),(4,1)] 1
      = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0)] from by decide] at h
  have h7 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,2)] := by
    have h := STPS.oper h6 2 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0)] 2
      = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,2)] from by decide] at h
  have h8 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,1),(3,2)] := by
    have h := STPS.oper h7 2 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,2)] 2
      = [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,1),(3,2)] from by decide] at h
  have h9 := STPS.oper h8 1 (by norm_num)
  rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,1),(3,2)] 1
    = hostM30_rr from by decide] at h9

/-- **part (1)**: `(s, D_{M₁,j₁} 0, b)` は `Trans(N')` の scb 分解。 -/
theorem rr84_part1_rr :
    scb_decomp (Trans (s84x_Np hostM30_rr)) s_rr
      (flatBT (Dprin (entry hostM30_rr 1 (Lng hostM30_rr - 1) : ℕ∞) BZero)) b_rr := by
  refine ⟨by decide, ?_, ?_⟩
  · intro _
    exact ⟨BP.db (entry hostM30_rr 1 (Lng hostM30_rr - 1) : ℕ∞) BZero, by decide, by decide⟩
  · intro x hx; fin_cases hx <;> rfl

/-- **part (2)（訂正 A30 形）**: `(s, D_{M₁,j₋₂} 0, b)` は `Trans(L')` の scb 分解。
part (1) と同じ `(s,b)` を共有する。 -/
theorem rr84_corrected_part2_rr :
    scb_decomp (Trans (rrLp hostM30_rr)) s_rr
      (flatBT (Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) BZero)) b_rr := by
  refine ⟨by decide, ?_, ?_⟩
  · intro _
    exact ⟨BP.db (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) BZero, by decide, by decide⟩
  · intro x hx; fin_cases hx <;> rfl

/-- 訂正 A30 形の充足性: 共有手術対 `(s_rr, b_rr)` が part (1) と part (2) を同時に
満たす（＝ `Rightmost84ReplaceCorrected` の存在部分の具体証拠）。 -/
theorem rr84_corrected_holds_rr :
    ∃ sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_Np hostM30_rr)) sb.1
          (flatBT (Dprin (entry hostM30_rr 1 (Lng hostM30_rr - 1) : ℕ∞) BZero)) sb.2 ∧
      scb_decomp (Trans (rrLp hostM30_rr)) sb.1
          (flatBT (Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) BZero)) sb.2 :=
  ⟨(s_rr, b_rr), rr84_part1_rr, rr84_corrected_part2_rr⟩

/-- **原文 part (3) は偽（訂正 A30、具体 host）**: 共有手術対 `(s_rr, b_rr)` に対し、
原文形の中心 `D_{M₁,j₀}(t₂ +_B D_{M₁,j₀} 0)` は `t₂` が何であれ `Trans(L')` の scb
分解にならない。part (1)/(2) が確定させた `(s,b)` から中心の長さは 2 に決まるが、
原文形の中心は長さ ≥ 3。 -/
theorem rr84_original_false_rr (t₂ : BT) :
    ¬ scb_decomp (Trans (rrLp hostM30_rr)) s_rr
        (flatBT (Dprin (entry hostM30_rr 1 (parent hostM30_rr 0 (Lng hostM30_rr - 1)) : ℕ∞)
          (addBT t₂ (Dprin (entry hostM30_rr 1 (parent hostM30_rr 0 (Lng hostM30_rr - 1)) : ℕ∞)
            BZero)))) b_rr :=
  rr84_original_false_str _ _ _ _ _ t₂ rr84_corrected_part2_rr

/-! ## A31 具体 host（隣接補題 part (5-3) 原文形の反証）

`M = (0,0)(1,1)(2,0)(3,1)`, `n = 2`（標準形かつ単項）。`j₁ = 3`, `j₋₂ = 2`,
`N' = (2,0)(3,1)`, `Pred(N') = (2,0)` は**零項**なので `Trans(Pred N') = 0`。一方
`M[2] = (0,0)(1,1)(2,0)(3,0)`, `Trans(M[2]) = D_0 D_1 D_0 D_0 0 ≠ 0`。原文 part (5-3)
`(s', Trans(Pred N'), b')` は `Trans(M[n])` の scb 分解と主張するが、中心
`Trans(Pred N')` の文字列は `[Z]` で、対象が零項でない以上 scb 分解の中心は単項で
なければならない（`[Z]` は単項でない）。訂正形（`Pred(N')` 非零項ガード）は
`8.4-oper-props5` に移植済み。 -/

def hostA31_rr : PS := [(0,0),(1,1),(2,0),(3,1)]

/-- `M = (0,0)(1,1)(2,0)(3,1)` は標準形（`diagSeq 0 2` から `oper` 2 段）。 -/
theorem hostA31_STPS_rr : STPS hostA31_rr := by
  have h0 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,2)] := by
    have h := STPS.diag 0 2 (by norm_num)
    rwa [show diagSeq 0 2 = [((0:ℕ),(0:ℕ)),(1,1),(2,2)] from by decide] at h
  have h1 : STPS [((0:ℕ),(0:ℕ)),(1,1),(2,1)] := by
    have h := STPS.oper h0 2 (by norm_num)
    rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2)] 2
      = [((0:ℕ),(0:ℕ)),(1,1),(2,1)] from by decide] at h
  have h2 := STPS.oper h1 2 (by norm_num)
  rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,1)] 2 = hostA31_rr from by decide] at h2

/-- **原文 part (5-3) は偽（訂正 A31、具体 host）**: `Pred(N')` が零項なので
`Trans(Pred N') = 0`、その文字列 `[Z]` を中心とする scb 分解は存在しない
（`Trans(M[2]) ≠ 0` かつ中心は単項でなければならない）。 -/
theorem oper5_part5_3_original_false_rr :
    ¬ ∃ s b, scb_decomp (Trans (oper hostA31_rr 2)) s
        (flatBT (Trans (Pred (s84x_Np hostA31_rr)))) b := by
  rintro ⟨s, b, hsd⟩
  have hnz : Trans (oper hostA31_rr 2) ≠ BZero := by
    intro h
    have hf : flatBT (Trans (oper hostA31_rr 2)) = flatBT BZero := by rw [h]
    exact absurd hf (by decide)
  have hptb := hsd.2.1 hnz
  have hcenter : flatBT (Trans (Pred (s84x_Np hostA31_rr))) = [Sym.zero] := by decide
  rw [hcenter] at hptb
  exact not_isPTB_zero_rr hptb

/-! ## 非空虚性（仮定が充足可能であることの機械確認）

`Rightmost84ReplaceCorrected` および原文形反証の仮定（標準形＋単項＋
`hasParent M 1 j₁`＋`j₋₂ < j₁-1`＋`j₀` 非許容）が実際に充足可能であることを、
標準形の導出ごと機械確認する。 -/

/-- A30 host の仮定は充足可能。 -/
theorem nonvacuous_a30_rr :
    STPS hostM30_rr ∧ monoT hostM30_rr = true ∧
      hasParent hostM30_rr 1 (Lng hostM30_rr - 1) = true ∧
      s84x_jm2 hostM30_rr + 1 < Lng hostM30_rr - 1 ∧
      adm hostM30_rr (parent hostM30_rr 0 (Lng hostM30_rr - 1)) = false :=
  ⟨hostM30_STPS_rr, by decide, by decide, by decide, by decide⟩

/-- A31 host の仮定は充足可能。 -/
theorem nonvacuous_a31_rr :
    STPS hostA31_rr ∧ monoT hostA31_rr = true ∧
      hasParent hostA31_rr 1 (Lng hostA31_rr - 1) = true :=
  ⟨hostA31_STPS_rr, by decide, by decide⟩

/-! ## 回帰ベクトル（`python/red_model.py` / `python/trans_model.py` と一致） -/

#guard s84x_jm2 hostM30_rr == 0
#guard parent hostM30_rr 0 (Lng hostM30_rr - 1) == 1
#guard entry hostM30_rr 1 (Lng hostM30_rr - 1) == 1
#guard entry hostM30_rr 1 (s84x_jm2 hostM30_rr) == 0
#guard s84x_Np hostM30_rr == hostM30_rr
#guard rrLp hostM30_rr == [(0,0),(1,1),(2,2),(2,0)]
#guard !adm hostM30_rr (parent hostM30_rr 0 (Lng hostM30_rr - 1))
#guard flatBT (Trans (s84x_Np hostM30_rr))
  == s_rr ++ [Sym.dsym (1:ℕ∞), Sym.zero] ++ b_rr
#guard flatBT (Trans (rrLp hostM30_rr))
  == s_rr ++ [Sym.dsym (0:ℕ∞), Sym.zero] ++ b_rr
#guard s84x_jm2 hostA31_rr == 2
#guard Pred (s84x_Np hostA31_rr) == [(2,0)]
#guard oper hostA31_rr 2 == [(0,0),(1,1),(2,0),(3,0)]
#guard flatBT (Trans (Pred (s84x_Np hostA31_rr))) == [Sym.zero]

#print axioms rr84_original_false_str
#print axioms rr84_part1_rr
#print axioms rr84_corrected_part2_rr
#print axioms rr84_corrected_holds_rr
#print axioms rr84_original_false_rr
#print axioms hostM30_STPS_rr
#print axioms oper5_part5_3_original_false_rr
#print axioms hostA31_STPS_rr
#print axioms nonvacuous_a30_rr
#print axioms nonvacuous_a31_rr

end PSS
