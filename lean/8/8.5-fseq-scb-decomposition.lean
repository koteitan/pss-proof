import «8».«8.5-exchV-props»
import «8».«8.5-scb-decompositions»
import «8».«8.5-exchV-M-tower-close»
import «8».«8.5-exchV-values-close»
import «8».«8.5-exchV-nadm-w2nostr»
import «8».«8.5-exchV-nadm-c2l1»
import «8».«8.5-exchV-notld»
import «8».«8.4-rightmost-replace-close»
import «8».«8.4-rm84-rfacts-close»

/-!
# §8.5 補題（条件(V)の下での基本列の scb 分解）

- 原文: `tmp/content.md` §8.5「補題（条件(V)の下での基本列のscb分解）」(5352)、
  その証明 5364–5445。§8.5「条件(V)の下での展開規則」内、命題（条件(V)の下での
  `Trans` と基本列の交換関係）(5153) を証明するための最後の補題。
- 逐語: **なし**。`isabelle/pss_paper.thy`:2128 は本補題を **DEFERRED**
  （text-only note）としている。理由は原文が `Trans` の再帰定義の内部記号
  `t₂ / s'₀ / b'₀` を露出せずに述べているため
  （"BLOCKING SYMBOLS: `t₂`, `s'₀`, `b'₀`"）。Lean/Isabelle 側はこの露出を
  `transT2 M`（= `t₂`）と存在量化された `(s'₀,b'₀)`（scb 文字列対）で行う。
  本ファイルも同じ。原文の記号との対応:
  * `u`（外側 `D_u` の指標） = 存在量化された `ℕ`（本証明では `M₁,j₀`）
  * `t₂` = `transT2 M`
  * `M₁,j₀` = `entry M 1 (transJ0 M)`、`M₁,j₋₁` = `entry M 1 (transJm1 M)`
  * `t'` = 存在量化された `T_B` の元（本証明では `t₂`、下記 ⚠️ 参照）
- 主張（原文 5352）: `M ∈ ST_PS ∩ PT_PS`、`n ∈ ℕ₊`、`j₁ > 1`、条件(V) のとき、
  一意な `u ∈ ℕ`、`(s'₀,b'₀) ∈ (Σ^<ω)²`、`t' ∈ T_B` が存在して
  * (1) `(s'₀, D_u t₂, b'₀)` は `Trans(M[n])` の scb 分解、
  * (2) `(s'₀, D_u(t₂ +_B D_{M₁,j₀} 0), b'₀)` は `Trans(M)[m_n]` の scb 分解、
  * (3) `(s'₀, D_u(t₂ +_B D_{M₁,j₀} t'), b'₀)` は `Trans(M[n+1])` の scb 分解、
  ここで `j₀` が `M` 許容なら `m_n := n-1`、非許容なら `m_n := n`。
- **本ファイルの scope＝`j₀` 非 `M` 許容（`m_n = n`）かつ `n > 1` の枝**。
  この枝が原文 (5) `Trans(M[n]) = s₁ D_{M₁,j₋₁} (s'₁ D_{M₁,j₀})^n t₂ (b'₁)^n b₁`
  に依拠しており、これは **訂正 A29**（`8.5-scb-decompositions.lean` 参照、
  `corrections.md`:889）により `n = 1` で偽（指数 0）。したがって非許容枝の本補題は
  **原文の証明が `n > 1` でのみ意味を持つ**。`j₀` 許容枝（`m_n = n-1`）は
  `j₋₁ = j₀`（許容ゆえ `Adm M j₀ = j₀`）で外側・内側の指標が一致し `n = 1` の
  破綻がない別枝（`ExchV_scbdec_adm_forms` を用いる）で、本ファイルの scope 外。
- ⚠️**原文の `t'` の誤り**: 原文の非許容枝は `t'₀ := t₂ +_B D_{M₁,j₀} t₂` と置き
  (3) を `Trans(M[n+1]) = …(s'₁ D_{M₁,j₀})^{n+2}…` と主張するが、原文自身の
  (5)' は `Trans(M[n+1]) = …^{n+1}…`（指数 `n+1`）であり **内部矛盾**。機械化した塔
  （`e5x_bodyM`）は指数 `n+1` の（正しい）形なので、本証明は **`t' := t₂`**
  （指数 `n+1`）を採り、(3) を機械的に成立させる。＝原文の `t'₀` は誤り。
- Isabelle（設計図）: `m_8_5_scbdec_fseq_condV` (`isabelle/layerB/pss_wip.thy`:51466)
  ＋ 非許容塔 `atx_nf3x` (同 :86273) → `nfx_NFall` (:64558)。Lean では前者が
  `fseq_condV_holds`（`8.5-exchV-props`、無条件）、後者が named Prop `ExchV_nf3x`
  （`8.5-Trans-fseq-condV`）。塔の core は `e5x_bodyM t₂ e k`（`M`側）と
  `e5x_bodyO t₂ e m`（`operB`側）。
- 依存（すべてビルド済み）: «8».«8.5-exchV-props»
  （`fseq_condV_holds` / `condV_setup_holds` / `transC2_condV_eq`）、
  «8».«8.5-scb-decompositions»（`scb5Pow`）、推移的に «8».«8.5-Trans-fseq-condV»
  （named Prop `ExchV_nf3x`、`e5x_bodyM` / `e5x_bodyO` / `s85b_W`、
  `transT2` / `transJ0` / `transJm1`）、`PSS.Scb`（`flatBT` / `flatBP` /
  `scb_decomp`）、`PSS.Buchholz`（`addBT` / `Dprin` / `BZero`）。
- 訂正: **A29**（`corrections.md`:889、[軽微]、非許容枝 (5) の `n=1` 指数）
  ＋ 本ファイルで顕在化した **`t'` の内部矛盾**（上記 ⚠️）。
- 状態: GREEN（sorry 0）。named Prop `ExchV_nf3x`（既存、新規残差ではない）上の
  green-modulo。許容枝と一意性は scope 外（`needs` 参照）。
-/

namespace PSS

/-! ## scb 分解のための文字列分割（`8.5-scb-decompositions` の `_sd5` の私的複製） -/

/-- `t₂ +_B D_v (·)` の左側の文字列。 -/
private def sSplit_fsd : BT → List Sym
  | .trm [] => []
  | .trm (p :: ps) => Sym.lp :: (flatBP p ++ flatBPTail ps) ++ [Sym.cm]

/-- `t₂ +_B D_v (·)` の右側の文字列。 -/
private def bSplit_fsd : BT → List Sym
  | .trm [] => []
  | .trm (_ :: _) => [Sym.rp]

private theorem flatBPTail_append_one_fsd (ps : List BP) (d : BP) :
    flatBPTail (ps ++ [d]) = flatBPTail ps ++ (Sym.cm :: flatBP d) := by
  induction ps with
  | nil => simp [flatBPTail]
  | cons p ps ih => simp [flatBPTail, ih]

/-- **鍵**: `t +_B D_v Y` の文字列は `Y` を `D_v Y` の位置にだけ含み、
その左右 `(sSplit,bSplit)` は `Y` にも `v` にも依存しない。 -/
private theorem flat_addBT_Dprin_fsd (t : BT) (v : ℕ∞) (Y : BT) :
    flatBT (addBT t (Dprin v Y))
      = sSplit_fsd t ++ (Sym.dsym v :: flatBT Y) ++ bSplit_fsd t := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simp [addBT, Dprin, flatBT, flatBP, sSplit_fsd, bSplit_fsd]
  | cons p rest =>
      cases rest with
      | nil =>
          simp [addBT, Dprin, flatBT, flatBP, flatBPTail, sSplit_fsd, bSplit_fsd]
      | cons q qs =>
          show flatBT (.trm (p :: q :: (qs ++ [BP.db v Y]))) = _
          simp [flatBT, flatBPTail, flatBPTail_append_one_fsd, flatBP,
            sSplit_fsd, bSplit_fsd]

/-! ## `scb5Pow`（`8.5-scb-decompositions`、公開）の補助 -/

private theorem replicate_flatten_comm_fsd (b' : List Sym) (n : ℕ) :
    b' ++ (List.replicate n b').flatten = (List.replicate n b').flatten ++ b' := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, ← List.append_assoc, ih]

/-- 外側から 1 段剥がす（`scb5Pow_succ_sd5` の複製、seed 非依存）。 -/
private theorem scb5Pow_succ_fsd (s' b' : List Sym) (e : ℕ∞) (t : BT) (n : ℕ) :
    scb5Pow s' b' e t (n + 1)
      = (s' ++ [Sym.dsym e]) ++ scb5Pow s' b' e t n ++ b' := by
  simp only [scb5Pow, List.replicate_succ, List.flatten_cons, List.append_assoc,
    replicate_flatten_comm_fsd]

/-! ## 塔 `s85b_W` の flat 形（種 `t` と種 `0_B` の両方） -/

/-- 種 `t` の塔（`M` 側）: `flat(t +_B W_m^{seed=t}) = scb5Pow … t (m+1)`。 -/
private theorem flat_addBT_s85b_W_seedT_fsd (t : BT) (e : ℕ) (m : ℕ) :
    flatBT (addBT t (s85b_W e t t m))
      = scb5Pow (sSplit_fsd t) (bSplit_fsd t) (e : ℕ∞) t (m + 1) := by
  induction m with
  | zero =>
      rw [s85b_W, flat_addBT_Dprin_fsd]
      simp [scb5Pow, List.append_assoc]
  | succ m ih =>
      rw [s85b_W, flat_addBT_Dprin_fsd, ih,
        scb5Pow_succ_fsd (sSplit_fsd t) (bSplit_fsd t) (e : ℕ∞) t (m + 1)]
      simp [List.append_assoc]

/-- 種 `0_B` の塔（`operB` 側）: `flat(t +_B W_m^{seed=0}) = scb5Pow … 0_B (m+1)`。 -/
private theorem flat_addBT_s85b_W_seedZ_fsd (t : BT) (e : ℕ) (m : ℕ) :
    flatBT (addBT t (s85b_W e t BZero m))
      = scb5Pow (sSplit_fsd t) (bSplit_fsd t) (e : ℕ∞) BZero (m + 1) := by
  induction m with
  | zero =>
      rw [s85b_W, flat_addBT_Dprin_fsd]
      simp [scb5Pow, List.append_assoc]
  | succ m ih =>
      rw [s85b_W, flat_addBT_Dprin_fsd, ih,
        scb5Pow_succ_fsd (sSplit_fsd t) (bSplit_fsd t) (e : ℕ∞) BZero (m + 1)]
      simp [List.append_assoc]

/-- `Trans(M[k+1])` の core `D_{M₁,j₋₁}(·)` の内側の flat 形（`k ≥ 1`）。 -/
private theorem flat_e5x_bodyM_succ_fsd (t : BT) (e : ℕ) (j : ℕ) :
    flatBT (e5x_bodyM t e (j + 1))
      = scb5Pow (sSplit_fsd t) (bSplit_fsd t) (e : ℕ∞) t (j + 2) := by
  rw [e5x_bodyM, flat_addBT_s85b_W_seedT_fsd]

/-- `operB(Trans M)(numBT m)` の core `D_{M₁,j₋₁}(·)` の内側の flat 形。 -/
private theorem flat_e5x_bodyO_fsd (t : BT) (e : ℕ) (m : ℕ) :
    flatBT (e5x_bodyO t e m)
      = scb5Pow (sSplit_fsd t) (bSplit_fsd t) (e : ℕ∞) BZero (m + 1) := by
  rw [e5x_bodyO, flat_addBT_s85b_W_seedZ_fsd]

/-! ## `replicate` の flatten 併合補題 -/

private theorem rep_snoc_fsd (X : List Sym) (k : ℕ) :
    (List.replicate k X).flatten ++ X = (List.replicate (k + 1) X).flatten := by
  rw [List.replicate_succ']
  simp [List.flatten_append]

private theorem rep_cons_fsd (X : List Sym) (k : ℕ) :
    X ++ (List.replicate k X).flatten = (List.replicate (k + 1) X).flatten := by
  rw [List.replicate_succ, List.flatten_cons]

/-! ## `bSplit` / scb `b` 部が全て `RP` であること -/

private theorem bSplit_all_rp_fsd (t : BT) : ∀ x ∈ bSplit_fsd t, x = Sym.rp := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => intro x hx; simp [bSplit_fsd] at hx
  | cons p ps => intro x hx; simp [bSplit_fsd] at hx; exact hx

private theorem replicate_flatten_all_rp_fsd {L : List Sym}
    (hL : ∀ x ∈ L, x = Sym.rp) (k : ℕ) :
    ∀ x ∈ (List.replicate k L).flatten, x = Sym.rp := by
  intro x hx
  rw [List.mem_flatten] at hx
  obtain ⟨l, hlmem, hxl⟩ := hx
  rw [List.eq_of_mem_replicate hlmem] at hxl
  exact hL x hxl

/-! ## 中央 principal が `D_ω`-free であること（`isPTB_str`） -/

/-- 中央 `D_v X`（`X ∈ T_B`）が `D_ω`-free principal 文字列であること。 -/
private theorem isPTB_Dprin_fsd (v : ℕ) (X : BT) (hX : X ∈ T_B) :
    isPTB_str (flatBT (Dprin (v : ℕ∞) X)) := by
  have hXd : dfree_BT X = true := hX
  refine ⟨.db (v : ℕ∞) X, ?_, ?_⟩
  · simp [dfree_BP, hXd, ENat.coe_ne_top]
  · simp [Dprin, flatBT]

/-! ## 中央 principal の flat と塔の peel（scb 枠の露出） -/

private theorem flat_Dprin_fsd (v : ℕ∞) (X : BT) :
    flatBT (Dprin v X) = Sym.dsym v :: flatBT X := by
  simp [Dprin, flatBT, flatBP]

/-- `M` 側（種 `t`）の塔から末尾 1 ブロックを剥がし `D_e t` を露出。 -/
private theorem scb5Pow_peel_fsd (sc bc : List Sym) (e : ℕ∞) (t : BT) (k : ℕ) :
    scb5Pow sc bc e t (k + 2)
      = ((List.replicate (k + 1) (sc ++ [Sym.dsym e])).flatten ++ sc)
          ++ (Sym.dsym e :: flatBT t)
          ++ (List.replicate (k + 2) bc).flatten := by
  simp only [scb5Pow]
  rw [← rep_snoc_fsd (sc ++ [Sym.dsym e]) (k + 1)]
  simp [List.append_assoc]

/-- 末尾 2 ブロックを剥がし `D_e(sc D_e t bc)` を露出（`operB`側は `t := 0_B`）。 -/
private theorem scb5Pow_peel2_fsd (sc bc : List Sym) (e : ℕ∞) (t : BT) (k : ℕ) :
    scb5Pow sc bc e t (k + 3)
      = ((List.replicate (k + 1) (sc ++ [Sym.dsym e])).flatten ++ sc)
          ++ (Sym.dsym e :: (sc ++ (Sym.dsym e :: flatBT t) ++ bc))
          ++ (List.replicate (k + 2) bc).flatten := by
  simp only [scb5Pow]
  rw [← rep_snoc_fsd (sc ++ [Sym.dsym e]) (k + 2),
      ← rep_snoc_fsd (sc ++ [Sym.dsym e]) (k + 1),
      ← rep_cons_fsd bc (k + 2)]
  simp [List.append_assoc]

/-! ## 本体（非許容枝、`n > 1`） -/

/-- **補題（条件(V)の下での基本列の scb 分解）、非許容枝・`n > 1`**
（原文 `tmp/content.md`:5352、`isabelle/pss_paper.thy`:2128 は DEFERRED）。

`M ∈ ST_PS`、`monoT M`、条件(V)、`j₀` が非 `M` 許容（`m_n = n`）、`n > 1` のとき、
`u := M₁,j₀`、`t' := t₂`（原文の `t'₀ := t₂ +_B D_{M₁,j₀} t₂` は内部矛盾＝誤り、
本証明は正しい指数 `n+1` を与える `t' = t₂` を採る）、および明示的な
`(s'₀,b'₀)` に対し、原文 (1)(2)(3) が成り立つ:
* (1) `(s'₀, D_u t₂, b'₀)` は `Trans(M[n])` の scb 分解、
* (2) `(s'₀, D_u(t₂ +_B D_{M₁,j₀} 0), b'₀)` は `Trans(M)[n]` の scb 分解、
* (3) `(s'₀, D_u(t₂ +_B D_{M₁,j₀} t'), b'₀)` は `Trans(M[n+1])` の scb 分解。

`ExchV_nf3x`（`8.5-Trans-fseq-condV` の named Prop、既存）上の green-modulo。 -/
theorem p_8_5_fseq_scb_decomp_nadm (hNF : ExchV_nf3x) (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hcond : transCondV M = true)
    (hnadm : adm M (transJ0 M) = false) (hn : 1 < n) :
    ∃ (u : ℕ) (s' b' : List Sym) (t' : BT),
      scb_decomp (Trans (oper M n)) s'
        (flatBT (Dprin (u : ℕ∞) (transT2 M))) b' ∧
      scb_decomp (operB (Trans M) (numBT n)) s'
        (flatBT (Dprin (u : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)))) b' ∧
      scb_decomp (Trans (oper M (n + 1))) s'
        (flatBT (Dprin (u : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) t')))) b' := by
  have hR : RTPS M := STPS_RTPS M hST
  have hT : TPS M := RTPS_TPS M hR
  obtain ⟨hj₁, ht₁⟩ := condV_setup_holds M hR hT hmono hcond
  obtain ⟨s₁, b₁, hd₁, hk₁⟩ := fseq_condV_holds M hR hT hmono hj₁ ht₁ hcond
  obtain ⟨_hV, _hc₁eq, ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hT hmono hj₁ ht₁
  have hnadm' : adm M (parent M 0 (Lng M - 1)) = false := by
    simpa [transJ0, lastParent, lastIdx] using hnadm
  obtain ⟨hMtower, hOtower⟩ := hNF M s₁ b₁ hST hmono hcond hnadm' hd₁ hk₁
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  set e : ℕ := entry M 1 (transJ0 M) with he
  set um1 : ℕ := entry M 1 (transJm1 M) with hum1
  set t : BT := transT2 M with ht
  -- `b'` は常に全 `RP`
  have hbrp : ∀ x ∈ (List.replicate (k + 2) (bSplit_fsd t)).flatten ++ b₁, x = Sym.rp := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact replicate_flatten_all_rp_fsd (bSplit_all_rp_fsd t) (k + 2) x hx
    · exact hd₁.2.2 x hx
  -- 内側 `t₂ +_B D_e 0_B ∈ T_B`、`t₂ +_B D_e t₂ ∈ T_B`
  have hBZ : BZero ∈ T_B := by simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hDe0 : addBT t (Dprin (e : ℕ∞) BZero) ∈ T_B :=
    addBT_mem_T_B ht₂TB (Dprin_mem_T_B (by simp) hBZ)
  have hDet : addBT t (Dprin (e : ℕ∞) t) ∈ T_B :=
    addBT_mem_T_B ht₂TB (Dprin_mem_T_B (by simp) ht₂TB)
  refine ⟨e,
    s₁ ++ Sym.dsym (um1 : ℕ∞)
      :: (List.replicate (k + 1) (sSplit_fsd t ++ [Sym.dsym (e : ℕ∞)])).flatten ++ sSplit_fsd t,
    (List.replicate (k + 2) (bSplit_fsd t)).flatten ++ b₁, t, ?_, ?_, ?_⟩
  · -- (1) `Trans(M[k+2])`
    refine ⟨?_, fun _ => isPTB_Dprin_fsd e t ht₂TB, hbrp⟩
    have hM : flatBT (Trans (oper M (k + 2)))
        = s₁ ++ flatBP (BP.db (um1 : ℕ∞) (e5x_bodyM t e (k + 1))) ++ b₁ :=
      hMtower (k + 1)
    rw [flatBP, flat_e5x_bodyM_succ_fsd, scb5Pow_peel_fsd] at hM
    rw [hM, flat_Dprin_fsd]
    simp [List.append_assoc]
  · -- (2) `Trans(M)[k+2]`（`operB` 側）
    refine ⟨?_, fun _ => isPTB_Dprin_fsd e _ hDe0, hbrp⟩
    have hO : flatBT (operB (Trans M) (numBT (k + 2)))
        = s₁ ++ flatBP (BP.db (um1 : ℕ∞) (e5x_bodyO t e (k + 2))) ++ b₁ :=
      hOtower (k + 2) (by omega)
    rw [flatBP, flat_e5x_bodyO_fsd] at hO
    rw [hO, show k + 2 + 1 = k + 3 from rfl, scb5Pow_peel2_fsd,
      flat_Dprin_fsd, flat_addBT_Dprin_fsd]
    simp [List.append_assoc]
  · -- (3) `Trans(M[k+3])`
    refine ⟨?_, fun _ => isPTB_Dprin_fsd e _ hDet, hbrp⟩
    have hM3 : flatBT (Trans (oper M (k + 2 + 1)))
        = s₁ ++ flatBP (BP.db (um1 : ℕ∞) (e5x_bodyM t e (k + 2))) ++ b₁ :=
      hMtower (k + 2)
    rw [flatBP, flat_e5x_bodyM_succ_fsd] at hM3
    rw [hM3, show k + 2 + 1 = k + 3 from rfl, scb5Pow_peel2_fsd,
      flat_Dprin_fsd, flat_addBT_Dprin_fsd]
    simp [List.append_assoc]

/-! ## 非空虚性（仮定が充足可能であることの機械確認）

`M = (0,0)(1,1)(2,2)(2,2)`（`Lng = 4`）は `8.5-scb-decompositions.lean` /
`python/audit_85_scbdec5.py` が真正 `ST_PS` プールから見つけた最小の該当 host。
`n = 2 (> 1)` を採れば本補題の仮定はすべて充足される。 -/

private def hostM_fsd : PS := [(0,0),(1,1),(2,2),(2,2)]

private theorem hostM_STPS_fsd : STPS hostM_fsd := by
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
  have h7 := STPS.oper h6 2 (by norm_num)
  rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0)] 2 = hostM_fsd from by decide] at h7

/-- 本補題の仮定は**充足可能**（＝空虚ではない）。`n := 2` が `1 < n` を満たす。 -/
theorem nonvacuous_fsd :
    STPS hostM_fsd ∧ monoT hostM_fsd = true ∧ transCondV hostM_fsd = true ∧
      adm hostM_fsd (transJ0 hostM_fsd) = false ∧ 1 < transJ1 hostM_fsd ∧ (1 : ℕ) < 2 :=
  ⟨hostM_STPS_fsd, by decide, by decide, by decide, by decide, by decide⟩

/-! ## 回帰ベクトル -/

#guard monoT hostM_fsd
#guard transCondV hostM_fsd
#guard !adm hostM_fsd (transJ0 hostM_fsd)
#guard transJ1 hostM_fsd == 3
#guard transJ0 hostM_fsd == 1

#print axioms p_8_5_fseq_scb_decomp_nadm
#print axioms nonvacuous_fsd


/-- `ExchV_nf3x` の公開無条件供給（`8.7-termination`／`8.5-Trans-fseq-condV-close` と同一連鎖）。 -/
private theorem nf3x_fsdu : ExchV_nf3x :=
  nf3x_holds_xv2 (exchV_M_tower_of_residual (exchVMres_of_values
    (exchVMvalues_of_nadm_package (exchVMNadmAtomicPackage_of_parts
      (rightmost84ReplaceCorrected_of_exists rightmost84ReplaceExists_rc2)
      nadmW2nostr_holds (nadmC2L1_of_notLD nadmC2L1NotLD_holds)))))

/-- **本補題（非許容枝）の無条件形**。 -/
theorem p_8_5_fseq_scb_decomp_nadm_uncond (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hcond : transCondV M = true)
    (hnadm : adm M (transJ0 M) = false) (hn : 1 < n) :
    ∃ (u : ℕ) (s' b' : List Sym) (t' : BT),
      scb_decomp (Trans (oper M n)) s'
        (flatBT (Dprin (u : ℕ∞) (transT2 M))) b' ∧
      scb_decomp (operB (Trans M) (numBT n)) s'
        (flatBT (Dprin (u : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) BZero)))) b' ∧
      scb_decomp (Trans (oper M (n + 1))) s'
        (flatBT (Dprin (u : ℕ∞)
          (addBT (transT2 M) (Dprin (entry M 1 (transJ0 M) : ℕ∞) t')))) b' :=
  p_8_5_fseq_scb_decomp_nadm nf3x_fsdu M n hST hmono hcond hnadm hn

#print axioms p_8_5_fseq_scb_decomp_nadm_uncond

end PSS
