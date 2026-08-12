import «8».«8.5-Trans-fseq-condV»
import «8».«8.5-exchV-props»
import «8».«8.5-exchV-props2»
import «8».«8.5-exchV-M-tower»
import «8».«8.5-exchV-M-tower-close»
import «8».«8.5-exchV-values-close»
import «8».«8.5-exchV-nadm-atomics»
import «8».«8.5-exchV-nadm-w2nostr»
import «8».«8.5-exchV-nadm-c2l1»
import «8».«8.5-exchV-notld»
import «8».«8.4-rightmost-replace-close»
import «8».«8.4-rm84-rfacts-close»

/-!
# §8.5 補題（条件(V)の下での各種scb分解）part (5) ＋ 訂正 A29

- 原文: `tmp/content.md` §8.5「補題（条件(V)の下での各種scb分解）」(5213)。
  本ファイルの対象は **part (5)** (5225)、その証明は 5267 / 5329。
- 逐語: **なし**。`isabelle/pss_paper.thy:2117` は本補題を **DEFERRED**
  （text-only note）としている。理由は原文が `Trans` の再帰定義の内部記号
  `s₁ / b₁ / s'₁ / b'₁ / t₂ / c₂` を露出せずに述べているため
  （"BLOCKING SYMBOLS: `s₁`, `b₁`, `s'₁`, `b'₁`, `t₂`, `c₂`"）。
  Isabelle/Lean はこの露出を `transT2` / `transC2` / `transJ1` / `transJ0` /
  `transJm1` と存在量化された `(s₁,b₁)`／`(s₀,b₀)` で行う。本ファイルも同じ。
- 訂正: **A29**（`corrections.md`:889、[軽微]）。
  原文 (5) `Trans(M[n]) = s₁ D_{M₁,j₋₁} (s'₁ D_{M₁,j₀})^n t₂ (b'₁)^n b₁` は
  **n = 1 で偽**（原文自身の n=1 の基底 5329 は指数 **0** を導いており、主張と
  その証明の基底が食い違う）。訂正形は
  * `n = 1` → `Trans(M[1]) = s₁ D_{M₁,j₋₁} t₂ b₁`（指数 0）
  * `n > 1` → `Trans(M[n]) = s₁ D_{M₁,j₋₁} (s'₁ D_{M₁,j₀})^n t₂ (b'₁)^n b₁`
  ⚠️A29 は `corrections-old.md`:34 に登場するが **取り下げではない**。当初の
  訂正案「指数 `n-1`」が誤った `operB` に基づき `n ≥ 2` で偽だったため
  **訂正案のみ差し替え**られた（欠陥は `n=1` の境界のみ）。現行 A29 が本補題を
  指すことは `corrections.md`:889 の「位置」で確認済み（8.5-Joints-FirstNodes-basic
  ではない）。
- Isabelle（設計図）: `m_8_5_scbdec_fseq_condV` (`isabelle/layerB/pss_wip.thy`:51466)
  の conjunct (2) が訂正形の `n=1` そのもの
  （`scb_decomp (Trans (M[1])) s₁ (flatBT (D_{M₁,j₋₁} t₂)) b₁`）。
  `n ≥ 2` 側は `atx_nf3x` (同 :86273) → `nfx_NFall` (:64558) の
  `Trans(M[k+1])` 塔閉形式（core は `e5x_bodyM t₂ e k`）。
- 依存（すべてビルド済み）: «8».«8.5-Trans-fseq-condV»
  （named Prop `ExchV_nf3x` ＝ `atx_nf3x`、および `e5x_bodyM` / `s85b_W` /
  `transT2` / `transJ0` / `transJm1`）。推移的に `PSS.Scb`（`flatBT` / `flatBP` /
  `flatBPTail` / `scb_decomp`）、`Buchholz-1986 および Buchholz-rel-ord`（`addBT` / `Dprin` / `BZero`）。
  **`7.2-scb-unique` は不要**: 本ファイルの反証は `(s'₁,b'₁)` の一意性を使わず
  **任意の** `(s'₁,b'₁)` に対して原文形を否定する（一意性より強い）。
  無条件版 `scbdec_condV_part5_corrected_uncond` のために exchV discharge 連鎖
  （`8.5-exchV-props`/`props2`/`M-tower`/`M-tower-close`/`values-close`/
  `nadm-atomics`/`nadm-w2nostr`/`nadm-c2l1`/`notld`、`8.4-rightmost-replace-close`/
  `8.4-rm84-rfacts-close`＝`8.5-Trans-fseq-condV-close` と同一の import 集合）も追加。
  これらは公開 discharger `condV_setup_holds` / `fseq_condV_holds` /
  `nf3x_holds_xv2 (exchVMtower_sd5)` を供給し、3 named Prop を無条件化する。
- 数値検証: `python/audit_85_scbdec5.py`。真正 `ST_PS` プール（diagSeq 種＋oper 閉包、
  pool=1500 / mono host=1188）で、条件(V)＋`j₀` 非許容＋`j₁>1` を満たす host は
  **21 個**（＝仮定は非空虚。A29 本文の 32 個はプール設定違い）。そのうえで
  * 原文 LITERAL（指数 `n`）: `n=1` **0/21（偽）**、`n=2,3,4` 63/63（真）
  * A29 訂正形: 84/84（全 `n` で真）
  * Lean の `e5x_bodyM` 経由の body 恒等式: 84/84
  最小 host は `M = (0,0)(1,1)(2,2)(2,2)`（`Lng=4`）。Lean 側でも
  `nonvacuous_sd5` で `STPS` 導出（`diagSeq 0 3` から `oper` 7 段）ごと機械確認。
- ツリー項目: 補題（条件(V)の下での各種scb分解）(§8.5, content.md 5213) の part (5)。
- 状態: GREEN（sorry 0）。part (5) は **無条件**
  （`scbdec_condV_part5_corrected_uncond`＝3 named Prop を公開 discharger で供給）。
  `_corrected` / `_corrected_full` は Prop 仮定を保持した green-modulo 版として併存。
  part (1)–(4) は本ファイルの scope 外（`needs` 参照）。
-/

namespace PSS

/-! ## 原文 (5) の右辺の body `(s'₁ D_{M₁,j₀})^n t₂ (b'₁)^n` -/

/-- 原文 §8.5 (5) の `D_{M₁,j₋₁}` の内側の文字列
`(s'₁ D_e)^n t₂ (b'₁)^n`（`s' = s'₁`, `b' = b'₁`）。 -/
def scb5Pow (s' b' : List Sym) (e : ℕ∞) (t : BT) (n : ℕ) : List Sym :=
  (List.replicate n (s' ++ [Sym.dsym e])).flatten ++ flatBT t
    ++ (List.replicate n b').flatten

private theorem replicate_flatten_comm_sd5 (b' : List Sym) (n : ℕ) :
    b' ++ (List.replicate n b').flatten = (List.replicate n b').flatten ++ b' := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, ← List.append_assoc, ih]

/-- 外側から 1 段剥がす。 -/
private theorem scb5Pow_succ_sd5 (s' b' : List Sym) (e : ℕ∞) (t : BT) (n : ℕ) :
    scb5Pow s' b' e t (n + 1) = (s' ++ [Sym.dsym e]) ++ scb5Pow s' b' e t n ++ b' := by
  simp only [scb5Pow, List.replicate_succ, List.flatten_cons, List.append_assoc,
    replicate_flatten_comm_sd5]

/-! ## 内側の scb 対 `(s'₁, b'₁)` の明示形 -/

/-- `t₂ +_B D_v (·)` の左側の文字列。 -/
private def sSplit_sd5 : BT → List Sym
  | .trm [] => []
  | .trm (p :: ps) => Sym.lp :: (flatBP p ++ flatBPTail ps) ++ [Sym.cm]

/-- `t₂ +_B D_v (·)` の右側の文字列。 -/
private def bSplit_sd5 : BT → List Sym
  | .trm [] => []
  | .trm (_ :: _) => [Sym.rp]

private theorem flatBPTail_append_one_sd5 (ps : List BP) (d : BP) :
    flatBPTail (ps ++ [d]) = flatBPTail ps ++ (Sym.cm :: flatBP d) := by
  induction ps with
  | nil => simp [flatBPTail]
  | cons p ps ih => simp [flatBPTail, ih]

/-- **鍵**: `t₂ +_B D_v Y` の文字列は `Y` を `D_v Y` の位置にだけ含み、
その左右 `(s₀,b₀)` は `Y` にも `v` にも依存しない。 -/
private theorem flat_addBT_Dprin_sd5 (t : BT) (v : ℕ∞) (Y : BT) :
    flatBT (addBT t (Dprin v Y))
      = sSplit_sd5 t ++ (Sym.dsym v :: flatBT Y) ++ bSplit_sd5 t := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simp [addBT, Dprin, flatBT, flatBP, sSplit_sd5, bSplit_sd5]
  | cons p rest =>
      cases rest with
      | nil =>
          simp [addBT, Dprin, flatBT, flatBP, flatBPTail, sSplit_sd5, bSplit_sd5]
      | cons q qs =>
          show flatBT (.trm (p :: q :: (qs ++ [BP.db v Y]))) = _
          simp [flatBT, flatBPTail, flatBPTail_append_one_sd5, flatBP,
            sSplit_sd5, bSplit_sd5]

/-! ## 塔 `s85b_W` の flat 形＝原文の `(s'₁ D_{M₁,j₀})^n t₂ (b'₁)^n` -/

/-- `t +_B W_m` の文字列は指数 `m+1` の原文形。 -/
private theorem flat_addBT_s85b_W_sd5 (t : BT) (e : ℕ) (m : ℕ) :
    flatBT (addBT t (s85b_W e t t m))
      = scb5Pow (sSplit_sd5 t) (bSplit_sd5 t) (e : ℕ∞) t (m + 1) := by
  induction m with
  | zero =>
      rw [s85b_W, flat_addBT_Dprin_sd5]
      simp [scb5Pow, List.append_assoc]
  | succ m ih =>
      rw [s85b_W, flat_addBT_Dprin_sd5, ih,
        scb5Pow_succ_sd5 (sSplit_sd5 t) (bSplit_sd5 t) (e : ℕ∞) t (m + 1)]
      simp [List.append_assoc]

/-- **訂正 A29 の核**: `Trans(M[k+1])` の core `D_{M₁,j₋₁}(·)` の内側は、
`k = 0`（＝ `n = 1`）では `t₂` そのもの（**指数 0**）であり、`k ≥ 1`
（＝ `n = k+1 ≥ 2`）でのみ指数 `n` の原文形になる。 -/
private theorem flat_e5x_bodyM_zero_sd5 (t : BT) (e : ℕ) :
    flatBT (e5x_bodyM t e 0) = flatBT t := by
  rw [e5x_bodyM]

private theorem flat_e5x_bodyM_succ_sd5 (t : BT) (e : ℕ) (j : ℕ) :
    flatBT (e5x_bodyM t e (j + 1))
      = scb5Pow (sSplit_sd5 t) (bSplit_sd5 t) (e : ℕ∞) t (j + 2) := by
  rw [e5x_bodyM, flat_addBT_s85b_W_sd5]

/-! ## `(sSplit_sd5 t₂, bSplit_sd5 t₂)` が原文の `(s'₁, b'₁)` であることの証明書

原文 part (1) は「`(D_{M₁,j₋₁} s'₁, D_{M₁,j₁} 0, b'₁)` が `c₂` の scb 分解」と
述べる。条件(V) の下では `c₂ = D_{M₁,j₋₁}(t₂ +_B D_{M₁,j₁} 0)`
（Isabelle `m_8_5_transC2_condV`）なので、これは
`(s'₁, D_{M₁,j₁} 0, b'₁)` が `t₂ +_B D_{M₁,j₁} 0` の scb 分解であることと同値。
以下はその形で `(s'₁,b'₁)` を確定させる。 -/

private theorem inner_scb_decomp_sd5 (t : BT) (v : ℕ) :
    scb_decomp (addBT t (Dprin (v : ℕ∞) BZero)) (sSplit_sd5 t)
      (flatBT (Dprin (v : ℕ∞) BZero)) (bSplit_sd5 t) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [flat_addBT_Dprin_sd5]
    simp [Dprin, flatBT, flatBP]
  · intro _
    exact ⟨.db (v : ℕ∞) BZero, by
      simp [dfree_BP, dfree_BT, dfree_BPList, BZero, ENat.coe_ne_top], by
      simp [Dprin, flatBT]⟩
  · intro x hx
    rcases t with ⟨ps⟩
    cases ps with
    | nil => simp [bSplit_sd5] at hx
    | cons p ps => simp [bSplit_sd5] at hx; exact hx

/-! ## 訂正 A29 形の part (5) -/

/-- **補題（条件(V)の下での各種scb分解）part (5)、訂正 A29 形**
（原文 `tmp/content.md`:5225、`isabelle/pss_paper.thy`:2117 は DEFERRED）。

`M ∈ ST_PS`、`monoT M`、条件(V)、`j₀` が非 `M` 許容のとき、共有手術対
`(s₁,b₁)`（Isabelle `m_8_5_scbdec_fseq_condV` の (2)(3) ＝ Lean の named Prop
`ExchV_scbdec_fseq_condV` が供給する）に対し、原文の `(s'₁,b'₁)` が存在して

* `n = 1` → `Trans(M[1]) = s₁ D_{M₁,j₋₁} t₂ b₁`（**指数 0**）
* `n > 1` → `Trans(M[n]) = s₁ D_{M₁,j₋₁} (s'₁ D_{M₁,j₀})^n t₂ (b'₁)^n b₁`

が成り立つ。原文は `n = 1` でも指数 `n` を主張しており、そこが偽
（`scbdec_condV_part5_original_false` 参照）。 -/
theorem scbdec_condV_part5_corrected (hNF : ExchV_nf3x) (M : PS) (s₁ b₁ : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hcond : transCondV M = true)
    (hnadm : adm M (transJ0 M) = false)
    (hd₁ : scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁)
    (hk₁ : scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁) :
    ∃ s' b' : List Sym,
      scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
        s' (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b' ∧
      flatBT (Trans (oper M 1))
        = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞) :: flatBT (transT2 M) ++ b₁ ∧
      (∀ n : ℕ, 1 < n → flatBT (Trans (oper M n))
        = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
            :: scb5Pow s' b' (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) n ++ b₁) := by
  have hnadm' : adm M (parent M 0 (Lng M - 1)) = false := by
    simpa [transJ0, lastParent, lastIdx] using hnadm
  obtain ⟨hMtower, _hOtower⟩ := hNF M s₁ b₁ hST hmono hcond hnadm' hd₁ hk₁
  refine ⟨sSplit_sd5 (transT2 M), bSplit_sd5 (transT2 M),
    inner_scb_decomp_sd5 _ _, ?_, ?_⟩
  · have h0 := hMtower 0
    rw [flatBP, flat_e5x_bodyM_zero_sd5] at h0
    simpa using h0
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    have hj := hMtower (j + 1)
    rw [flatBP, flat_e5x_bodyM_succ_sd5] at hj
    simpa using hj

/-- `(s₁,b₁)` を bare な仮定ではなく既存の named Prop から供給した完全形。
`ExchV_condV_setup` / `ExchV_scbdec_fseq_condV` はいずれも
`8.5-exchV-props.lean` で**無条件に discharge 済み**（`condV_setup_holds` /
`fseq_condV_holds`）なので、本定理の実質的な残差は `ExchV_nf3x` 一本。 -/
theorem scbdec_condV_part5_corrected_full (hsetup : ExchV_condV_setup)
    (hfseq : ExchV_scbdec_fseq_condV) (hNF : ExchV_nf3x) (M : PS)
    (hST : STPS M) (hmono : monoT M = true) (hcond : transCondV M = true)
    (hnadm : adm M (transJ0 M) = false) :
    ∃ s₁ b₁ s' b' : List Sym,
      scb_decomp (Trans (oper M 1)) s₁
        (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ ∧
      scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ ∧
      scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
        s' (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b' ∧
      flatBT (Trans (oper M 1))
        = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞) :: flatBT (transT2 M) ++ b₁ ∧
      (∀ n : ℕ, 1 < n → flatBT (Trans (oper M n))
        = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
            :: scb5Pow s' b' (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) n ++ b₁) := by
  have hR : RTPS M := STPS_RTPS M hST
  have hT : TPS M := RTPS_TPS M hR
  obtain ⟨hj₁, ht₁⟩ := hsetup M hR hT hmono hcond
  obtain ⟨s₁, b₁, hd₁, hk₁⟩ := hfseq M hR hT hmono hj₁ ht₁ hcond
  obtain ⟨s', b', hinner, hbase, htower⟩ :=
    scbdec_condV_part5_corrected hNF M s₁ b₁ hST hmono hcond hnadm hd₁ hk₁
  exact ⟨s₁, b₁, s', b', hd₁, hk₁, hinner, hbase, htower⟩

/-! ## 無条件版（3 named Prop をすべて公開 discharger で供給）

`scbdec_condV_part5_corrected_full` の 3 仮定
（`ExchV_condV_setup` / `ExchV_scbdec_fseq_condV` / `ExchV_nf3x`）は、いずれも
exchV corpus で**無条件に discharge 済み**:
* `condV_setup_holds : ExchV_condV_setup`（`8.5-exchV-props`）
* `fseq_condV_holds : ExchV_scbdec_fseq_condV`（`8.5-exchV-props`）
* `nf3x_holds_xv2 (h : ExchV_M_tower) : ExchV_nf3x`（`8.5-exchV-props2`）、
  `ExchV_M_tower` は下記 `exchVMtower_sd5` で無条件供給。

したがって残差 Prop 0 の無条件定理が得られる。 -/

/-- `ExchV_M_tower` の無条件供給。`8.5-Trans-fseq-condV-close`:60 の private
`exchVMtower_vc`（＝`8.7-termination`:260 `exchVMtower_term`）の逐語再構成。 -/
private theorem exchVMtower_sd5 : ExchV_M_tower :=
  exchV_M_tower_of_residual
    (exchVMres_of_values (exchVMvalues_of_nadm_package
      (exchVMNadmAtomicPackage_of_parts
        (rightmost84ReplaceCorrected_of_exists rightmost84ReplaceExists_rc2)
        nadmW2nostr_holds (nadmC2L1_of_notLD nadmC2L1NotLD_holds))))

/-- **補題（条件(V)の下での各種scb分解）part (5)、訂正 A29 形、無条件版**
（原文 `tmp/content.md`:5225、`isabelle/pss_paper.thy`:2117 は DEFERRED）。

`scbdec_condV_part5_corrected_full` の 3 named Prop 仮定を、無条件公開 discharger
`condV_setup_holds` / `fseq_condV_holds` / `nf3x_holds_xv2 exchVMtower_sd5` で
供給して消去した。よって仮定は `STPS`＋`monoT`＋条件(V)＋`j₀` 非許容のみ。

`M ∈ ST_PS`、`monoT M`、条件(V)、`j₀` が非 `M` 許容のとき、原文の共有手術対
`(s₁,b₁)` と内側 scb 対 `(s'₁,b'₁)` が存在して

* `n = 1` → `Trans(M[1]) = s₁ D_{M₁,j₋₁} t₂ b₁`（**指数 0**、訂正 A29）
* `n > 1` → `Trans(M[n]) = s₁ D_{M₁,j₋₁} (s'₁ D_{M₁,j₀})^n t₂ (b'₁)^n b₁`

が成り立つ。原文 (5) が `n = 1` でも指数 `n` を主張して偽である点は
`scbdec_condV_part5_original_false` を参照。 -/
theorem scbdec_condV_part5_corrected_uncond (M : PS)
    (hST : STPS M) (hmono : monoT M = true) (hcond : transCondV M = true)
    (hnadm : adm M (transJ0 M) = false) :
    ∃ s₁ b₁ s' b' : List Sym,
      scb_decomp (Trans (oper M 1)) s₁
        (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁ ∧
      scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁ ∧
      scb_decomp (addBT (transT2 M) (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero))
        s' (flatBT (Dprin (entry M 1 (transJ1 M) : ℕ∞) BZero)) b' ∧
      flatBT (Trans (oper M 1))
        = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞) :: flatBT (transT2 M) ++ b₁ ∧
      (∀ n : ℕ, 1 < n → flatBT (Trans (oper M n))
        = s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
            :: scb5Pow s' b' (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) n ++ b₁) :=
  scbdec_condV_part5_corrected_full condV_setup_holds fseq_condV_holds
    (nf3x_holds_xv2 exchVMtower_sd5) M hST hmono hcond hnadm

/-! ## 原文形の反証（訂正 A29） -/

/-- **原文 (5) は `n = 1` で偽**（文字列レベルの不可能性）。

`(s'₁,b'₁)` の**一意性を一切使わない**: 訂正形の `n=1`
（`Trans(M[1]) = s₁ D_u t₂ b₁`）が成り立つ限り、**どんな** `(s'₁,b'₁)` を
取っても原文形 `s₁ D_u (s'₁ D_e)^1 t₂ (b'₁)^1 b₁` にはならない。
長さ勘定: 原文形は訂正形より `|s'₁| + 1 + |b'₁| ≥ 1` だけ長い。 -/
theorem scbdec_condV_part5_original_false_str (s₁ b₁ s' b' : List Sym) (u e : ℕ∞)
    (t T : BT) (hcorr : flatBT T = s₁ ++ Sym.dsym u :: flatBT t ++ b₁) :
    flatBT T ≠ s₁ ++ Sym.dsym u :: scb5Pow s' b' e t 1 ++ b₁ := by
  intro h
  have e1 := hcorr.symm.trans h
  have hlen := congrArg List.length e1
  simp [scb5Pow, List.length_append] at hlen
  omega

/-- **原文 (5) は条件(V)＋`j₀` 非許容の host すべてで `n = 1` において偽**
（訂正 A29、`corrections.md`:889）。

原文 (5) は「一意な `(s'₁,b'₁)` が存在して (1)–(5) を満たす」と述べるが、
ここでは一意性より強く、**任意の** `(s'₁,b'₁)` に対して `n = 1` の等式が
破れることを示す。したがって原文の主張はどう `(s'₁,b'₁)` を選んでも救えない。
仮定の非空虚性は `nonvacuous_sd5`（および `python/audit_85_scbdec5.py` の 21 host、
原文 LITERAL は `n=1` で 0/21）を参照。 -/
theorem scbdec_condV_part5_original_false (hNF : ExchV_nf3x) (M : PS) (s₁ b₁ : List Sym)
    (hST : STPS M) (hmono : monoT M = true) (hcond : transCondV M = true)
    (hnadm : adm M (transJ0 M) = false)
    (hd₁ : scb_decomp (Trans (oper M 1)) s₁
      (flatBT (Dprin (entry M 1 (transJm1 M) : ℕ∞) (transT2 M))) b₁)
    (hk₁ : scb_kind1 (Trans M) s₁ (flatBT (transC2 M)) b₁) :
    ∀ s' b' : List Sym, flatBT (Trans (oper M 1))
      ≠ s₁ ++ Sym.dsym (entry M 1 (transJm1 M) : ℕ∞)
          :: scb5Pow s' b' (entry M 1 (transJ0 M) : ℕ∞) (transT2 M) 1 ++ b₁ := by
  intro s' b'
  obtain ⟨_, _, _, hbase, _⟩ :=
    scbdec_condV_part5_corrected hNF M s₁ b₁ hST hmono hcond hnadm hd₁ hk₁
  exact scbdec_condV_part5_original_false_str s₁ b₁ s' b' _ _ _ _ hbase

/-! ## 非空虚性（仮定が充足可能であることの機械確認）

⚠️ 本 repo は「blueprint が空虚だった」事故を経験している。上の 2 定理の仮定
（`STPS` ＋ `monoT` ＋ 条件(V) ＋ `j₀` 非許容 ＋ `j₁ > 1`）が実際に充足可能である
ことを、`STPS` の導出ごと機械確認する。

`M = (0,0)(1,1)(2,2)(2,2)` は `python/audit_85_scbdec5.py` が真正 `ST_PS` プールから
見つけた**最小**の該当 host（`Lng = 4`）。導出は `diagSeq 0 3` から `oper` 7 段:
`diagSeq 0 3 →[2] →[2] →[1] →[2] →[1] →[1] →[2] M`。 -/

private def hostM_sd5 : PS := [(0,0),(1,1),(2,2),(2,2)]

private theorem hostM_STPS_sd5 : STPS hostM_sd5 := by
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
  rwa [show oper [((0:ℕ),(0:ℕ)),(1,1),(2,2),(3,0)] 2 = hostM_sd5 from by decide] at h7

/-- 上の 2 定理の仮定は**充足可能**（＝空虚ではない）。 -/
theorem nonvacuous_sd5 :
    STPS hostM_sd5 ∧ monoT hostM_sd5 = true ∧ transCondV hostM_sd5 = true ∧
      adm hostM_sd5 (transJ0 hostM_sd5) = false ∧ 1 < transJ1 hostM_sd5 :=
  ⟨hostM_STPS_sd5, by decide, by decide, by decide, by decide⟩

/-! ## 回帰ベクトル -/

#guard monoT hostM_sd5
#guard transCondV hostM_sd5
#guard reduced hostM_sd5
#guard !adm hostM_sd5 (transJ0 hostM_sd5)
#guard transJ1 hostM_sd5 == 3
#guard transJ0 hostM_sd5 == 1

#print axioms scbdec_condV_part5_corrected
#print axioms scbdec_condV_part5_corrected_full
#print axioms scbdec_condV_part5_corrected_uncond
#print axioms scbdec_condV_part5_original_false_str
#print axioms scbdec_condV_part5_original_false
#print axioms nonvacuous_sd5

end PSS
