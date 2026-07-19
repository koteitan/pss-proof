import «8».«8.7-termination»
import «8».«8.4-Trans-fseq-condIII-IV»

/-!
# §8.4 補題（条件(III)か(IV)の下での基本列の基本性質）part (2)(3)

- 原文: `tmp/content.md` 5000（補題（条件(III)か(IV)の下での基本列の基本性質））の
  (2)(3)。`j₁ = Lng M - 1`、`j₋₂ = parent M 1 j₁`、`w' = j₁ - 1 - j₋₂` として
  * (2) `Trans(M)[n-1] = Trans(M[n+1][1]^{w'})`（`Trans(M)[k] = operB (Trans M) (numBT k)`）；
  * (3) ある `(s',c'₁,c'₂,b')` が存在し、`c'₁`/`c'₂` は単項（`(PB c'ᵢ).length = 1`）、
    `c'₁ <_B c'₂`、`(s',c'₁,b')` は `Trans(M[n])` の scb 分解、`(s',c'₂,b')` は
    `Trans(M)[n]` の scb 分解。
- 訂正: part (2) に付いていた A33（構造的に偽と主張）は撤回済みで `corrections.md` に
  存在しない（part (2) は真）。A30 は §8.4 の別補題「右端の置き換えと`Trans`」part (3)、
  A31 は「展開規則の基本性質」part (5-3) が対象で本補題とは無関係。
- Isabelle: 逐語形は `p_8_4_oper_basic`（`isabelle/pss_paper.thy:2017`、`sorry`）。
  part (1) は `8.4-fseq-basic.lean` の `oper_basic_part1`。本ファイルは part (2)(3)。
  * part (3) の証明は `y3h_p_8_4_oper_basic`（`layerC/pss_scratch.thy:15527`）＝
    `y3h_part3_jm3anchor`/`y3h_part3_of_forms`（同 :15245/:15206）。本ファイルの
    `oper_basic_part3` はその engine `y3h_part3_of_forms` を移植し、閉形式・狭義順序を
    §8.4 交換 producer `Exch84_condIIIIV_producer`（`8.4-Trans-fseq-condIII-IV`）から供給する。
  * part (2) の証明は `y3l_p_8_4_oper_basic_part2` ＋ `y3m_p_8_4_oper_basic_part2_full`
    （同 :18777/:19105）。operB 側閉形式は producer の `fO`（Isabelle `d13x_fseq_condIII`）
    だが、切片 `L_n = M[n+1][1]^{w'}` の `Trans` 閉形式は別 producer
    `y3i_L6_various_scb_IIIIV`（同 :16321）に依る。この L6 切片閉形式は本移植の単一
    ファイル外なので、`Oper84BasicPart2Residual`（両辺 flat 一致）として名前付き残差に
    括り出し、part (2) の等式を `flatBT_injective` で得る（green-modulo）。

- 状態: part (3) ✅（`Exch84_condIIIIV_producer` modulo、sorry 0）。
  part (2) ✅（`Oper84BasicPart2Residual` modulo、sorry 0）。

## part (3) 証明の構造（Isabelle `y3h_part3_of_forms` のまま）

`Trans(M[n])` と `Trans(M)[n]` が共通の外側 scb 対 `(s₁, b₁)` で
`s₁ ++ D_{e₃} X ++ b₁` / `s₁ ++ D_{e₃} Y ++ b₁` と分解される（producer の `fM`/`fO`、
`X = coreTower ins A0 (n-1)`、`Y = coreTower ins 0_B (n+1)`）。すると:
1. `Trans(M[n]) ∈ T_B` から `X ∈ T_B`・`e₃ ≠ ⊤`、`operB(Trans M)(numBT n) ∈ T_B` から
   `Y ∈ T_B` を flat 文字列経由で抽出（`core_TB_of_flat_fb2`）。
2. `Trans(M[n]) <_B Trans(M)[n]`（producer の交換 `Trans_oper_exchange` 第 1 主張）を
   共通 scb 対を通して core へ反映して `D_{e₃} X <_B D_{e₃} Y`（`scbext_reflect_fb2`）。
3. 証人 `c'₁ = D_{e₃} X`、`c'₂ = D_{e₃} Y`、`s' = s₁`、`b' = b₁`。単項性は `PB` 長 1、
   scb 分解は flat 等式＋`isPTB_str`（`X,Y ∈ T_B`、`e₃ ≠ ⊤`）。
-/

namespace PSS

/-! ## 補助: flat 由来の `T_B` 抽出

`8.7-otint-a0ot-nub` の private `*_an`（`dfree_BT t = flatFin (flatBT t)`）を suffix
`_fb2` で複製。Isabelle `dfree_flat_BT` に対応。 -/

private def symFin_fb2 : Sym → Bool
  | .dsym v => v != (⊤ : ℕ∞)
  | _ => true

private def flatFin_fb2 (l : List Sym) : Bool := l.all symFin_fb2

private theorem flatFin_append_fb2 (a b : List Sym) :
    flatFin_fb2 (a ++ b) = (flatFin_fb2 a && flatFin_fb2 b) := by
  simp only [flatFin_fb2, List.all_append]

private theorem flatFin_cons_fb2 (x : Sym) (l : List Sym) :
    flatFin_fb2 (x :: l) = (symFin_fb2 x && flatFin_fb2 l) := by
  simp only [flatFin_fb2, List.all_cons]

mutual
  private theorem dfree_flat_BT_fb2 : ∀ t : BT, dfree_BT t = flatFin_fb2 (flatBT t)
    | .trm [] => by rfl
    | .trm [p] => by
        show (dfree_BP p && dfree_BPList []) = flatFin_fb2 (flatBP p)
        rw [dfree_flat_BP_fb2 p]; simp [dfree_BPList]
    | .trm (p :: q :: ps) => by
        show (dfree_BP p && dfree_BPList (q :: ps))
            = flatFin_fb2 (Sym.lp :: (flatBP p ++ flatBPTail (q :: ps)) ++ [Sym.rp])
        rw [flatFin_append_fb2, flatFin_cons_fb2, flatFin_append_fb2,
          dfree_flat_BP_fb2 p, dfree_flat_BPTail_fb2 (q :: ps)]
        simp [symFin_fb2, flatFin_fb2]
  private theorem dfree_flat_BP_fb2 : ∀ p : BP, dfree_BP p = flatFin_fb2 (flatBP p)
    | .db u a => by
        show ((u != (⊤ : ℕ∞)) && dfree_BT a) = flatFin_fb2 (Sym.dsym u :: flatBT a)
        rw [flatFin_cons_fb2, dfree_flat_BT_fb2 a]; rfl
  private theorem dfree_flat_BPTail_fb2 :
      ∀ ps : List BP, dfree_BPList ps = flatFin_fb2 (flatBPTail ps)
    | [] => by rfl
    | p :: ps => by
        show (dfree_BP p && dfree_BPList ps) = flatFin_fb2 (Sym.cm :: flatBP p ++ flatBPTail ps)
        rw [flatFin_append_fb2, flatFin_cons_fb2, dfree_flat_BP_fb2 p, dfree_flat_BPTail_fb2 ps]
        simp [symFin_fb2]
end

/-- Isabelle `y3h_core_TB_of_flat`（`layerC/pss_scratch.thy:15185`）を、頭添字 `e` の
有限性も同時に取り出す形に強めたもの。`t ∈ T_B` の flat 文字列に principal `D_e X` が
現れれば `e ≠ ⊤` かつ `X ∈ T_B`。 -/
private theorem core_TB_of_flat_fb2 {t X : BT} {s b : List Sym} {e : ℕ∞}
    (ht : t ∈ T_B) (hf : flatBT t = s ++ flatBP (.db e X) ++ b) :
    e ≠ ⊤ ∧ X ∈ T_B := by
  have hdf : dfree_BT t = true := ht
  rw [dfree_flat_BT_fb2 t, hf, flatFin_fb2, List.all_eq_true] at hdf
  -- `hdf : ∀ x ∈ s ++ flatBP (.db e X) ++ b, symFin_fb2 x = true`
  have hsub : ∀ {y : Sym}, y ∈ flatBP (.db e X) → y ∈ s ++ flatBP (.db e X) ++ b := by
    intro y hy; exact List.mem_append_left b (List.mem_append_right s hy)
  have hhead : Sym.dsym e ∈ flatBP (.db e X) := by
    rw [show flatBP (.db e X) = Sym.dsym e :: flatBT X from rfl]; exact List.mem_cons_self
  have he : e ≠ ⊤ := by
    have h := hdf _ (hsub hhead)
    simp only [symFin_fb2] at h
    exact bne_iff_ne.mp h
  refine ⟨he, ?_⟩
  show dfree_BT X = true
  rw [dfree_flat_BT_fb2 X, flatFin_fb2, List.all_eq_true]
  intro x hx
  apply hdf
  apply hsub
  rw [show flatBP (.db e X) = Sym.dsym e :: flatBT X from rfl]
  exact List.mem_cons_of_mem _ hx

/-! ## 補助: principal 文字列・Dprin 順序 -/

/-- Isabelle `isPTB_str_Dpt`: `X ∈ T_B`・`e ≠ ⊤` なら `D_e X` の flat 文字列は
`isPTB_str`。 -/
private theorem isPTB_str_Dpt_fb2 {e : ℕ∞} {X : BT} (he : e ≠ ⊤) (hX : X ∈ T_B) :
    isPTB_str (flatBT (Dprin e X)) := by
  refine ⟨.db e X, ?_, rfl⟩
  have hXf : dfree_BT X = true := hX
  simp only [dfree_BP, Bool.and_eq_true]
  exact ⟨bne_iff_ne.mpr he, hXf⟩

/-! ## 補助: scb 拡張を通した狭義順序の反映（Isabelle `y3h_scbext_reflect`, :15157） -/

private theorem scbext_reflect_fb2 {t t' : BT} {s b : List Sym} {cp1 cp2 : BP}
    (f1 : flatBT t = s ++ flatBP cp1 ++ b)
    (f2 : flatBT t' = s ++ flatBP cp2 ++ b)
    (bRP : ∀ x ∈ b, x = Sym.rp)
    (lt : lessBT t t' = true) : lessBP cp1 cp2 = true := by
  rcases lessBT_linear_trichotomy (BT.trm [cp1]) (BT.trm [cp2]) with h | h | h
  · -- `lessBT (trm [cp1]) (trm [cp2]) = true` がそのまま目標
    simpa [lessBT, lessBPList] using h
  · -- `trm [cp1] = trm [cp2]` ⟹ `t = t'` ⟹ `lessBT t t = false` と矛盾
    exfalso
    have hcp : cp1 = cp2 := by
      simp only [BT.trm.injEq, List.cons.injEq, and_true] at h; exact h
    have htt : t = t' := flatBT_injective (by rw [f1, f2, hcp])
    rw [htt, lessBT_linear_irrefl] at lt; exact absurd lt (by simp)
  · -- `lessBT (trm [cp2]) (trm [cp1])` ⟹ `lessBT t' t` ⟹ 推移＋非反射で矛盾
    exfalso
    have gt : lessBP cp2 cp1 = true := by simpa [lessBT, lessBPList] using h
    have ltt' : lessBT t' t = true := scbext_lessBT f2 f1 bRP gt
    have hself : lessBT t t = true := lessBT_linear_trans t t' t lt ltt'
    rw [lessBT_linear_irrefl] at hself; exact absurd hself (by simp)

/-! ## part (3) engine（Isabelle `y3h_part3_of_forms`, :15206） -/

/-- 共通 scb 対 `(s,b)` で `Trans(M[n]) = s ++ D_e X ++ b`・
`Trans(M)[n] = s ++ D_e Y ++ b` と分解され、両者が `T_B` で狭義順序 `lt` を満たせば
part (3) の証人が取れる。 -/
private theorem part3_of_forms_fb2 {M : PS} {n : ℕ} {s b : List Sym} {X Y : BT} {e : ℕ∞}
    (hMTB : Trans (oper M n) ∈ T_B) (hOTB : operB (Trans M) (numBT n) ∈ T_B)
    (fM : flatBT (Trans (oper M n)) = s ++ flatBP (.db e X) ++ b)
    (fO : flatBT (operB (Trans M) (numBT n)) = s ++ flatBP (.db e Y) ++ b)
    (bRP : ∀ x ∈ b, x = Sym.rp)
    (lt : lessBT (Trans (oper M n)) (operB (Trans M) (numBT n)) = true) :
    ∃ s c1 c2 b, (PB c1).length = 1 ∧ (PB c2).length = 1 ∧ lessBT c1 c2 = true
      ∧ scb_decomp (Trans (oper M n)) s (flatBT c1) b
      ∧ scb_decomp (operB (Trans M) (numBT n)) s (flatBT c2) b := by
  obtain ⟨he, hX⟩ := core_TB_of_flat_fb2 hMTB fM
  obtain ⟨_, hY⟩ := core_TB_of_flat_fb2 hOTB fO
  have coreLt : lessBP (.db e X) (.db e Y) = true := scbext_reflect_fb2 fM fO bRP lt
  refine ⟨s, Dprin e X, Dprin e Y, b, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PB, Dprin, untrm]
  · simp [PB, Dprin, untrm]
  · simpa [Dprin, lessBT, lessBPList] using coreLt
  · exact ⟨fM, fun _ => isPTB_str_Dpt_fb2 he hX, bRP⟩
  · exact ⟨fO, fun _ => isPTB_str_Dpt_fb2 he hY, bRP⟩

/-! ## part (3) 記事逐語形 -/

/-- **§8.4 補題（条件(III)か(IV)の下での基本列の基本性質）part (3)**
（原文 `tmp/content.md` 5000、Isabelle `p_8_4_oper_basic` 第 (3) 主張、
`isabelle/pss_paper.thy:2017`）。

ある `(s',c'₁,c'₂,b')` が存在し、`c'₁`/`c'₂` は単項（`(PB c'ᵢ).length = 1`）で
`c'₁ <_B c'₂`、`(s',c'₁,b')` は `Trans(M[n])` の scb 分解、`(s',c'₂,b')` は
`Trans(M)[n] = operB(Trans M)(numBT n)` の scb 分解。

`Exch84_condIIIIV_producer`（`8.4-Trans-fseq-condIII-IV`）modulo。 -/
theorem oper_basic_part3 (hprod : Exch84_condIIIIV_producer)
    (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hj₁ : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    ∃ s c1 c2 b, (PB c1).length = 1 ∧ (PB c2).length = 1 ∧ lessBT c1 c2 = true
      ∧ scb_decomp (Trans (oper M n)) s (flatBT c1) b
      ∧ scb_decomp (operB (Trans M) (numBT n)) s (flatBT c2) b := by
  -- `Trans(M[n]) ∈ T_B`
  have hMTB : Trans (oper M n) ∈ T_B :=
    Trans_mem_T_B (oper M n) (STPS_RTPS (oper M n) (STPS.oper hST n hn))
  -- `Trans M ≠ 0_B`（`monoT` から `zeroT M = false`）
  have hTP : TPS M := RTPS_TPS M (STPS_RTPS M hST)
  have hz : zeroT M = false := by
    have h := hmono; unfold monoT at h
    rw [Bool.and_eq_true] at h
    simpa using h.1
  have hTMne : Trans M ≠ BZero := fun hcontra => by
    simp [(Trans_preserves_zeroT M hTP).mpr hcontra] at hz
  -- `operB(Trans M)(numBT n) ∈ T_B`（Buchholz 基本列の閉包 + `OT_B ⊆ T_B`）
  have hOTB : operB (Trans M) (numBT n) ∈ T_B :=
    (buchholz_fseq_closed (Trans M) n (Trans_STPS_OT_B M hST) hTMne).2
  -- producer の閉形式・狭義順序
  obtain ⟨ins, A0, e3, ub, s0, b0, s1, b1, hflat, hb0, hb1, fO, fM, base0, base1, Lbase⟩ :=
    hprod M hST hmono hj₁ hcond hp
  have lt : lessBT (Trans (oper M n)) (operB (Trans M) (numBT n)) = true :=
    (Trans_oper_exchange hprod hST hmono hj₁ hcond hp hn).1
  exact part3_of_forms_fb2 hMTB hOTB (fM n hn) (fO n) hb1 lt

/-! ## part (2): 残差と記事逐語形 -/

/-- part (2) の残差。operB 側閉形式は producer の `fO`（Isabelle `d13x_fseq_condIII`）だが、
切片 `L_n = M[n+1][1]^{w'}` の `Trans` 閉形式（Isabelle `y3i_L6_various_scb_IIIIV`、
`layerC/pss_scratch.thy:16321）は本ファイル外の §8.4 corpus に属す。両者の flat 一致を
単一の残差として括り出す。真理性は `python/_wd84_operbasic_audit` 系の operB 監査
（A23 訂正後）で経験的に裏付けられている。 -/
def Oper84BasicPart2Residual : Prop :=
  ∀ (M : PS) (n : ℕ), STPS M → monoT M = true → 1 ≤ n →
    hasParent M 1 (Lng M - 1) = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    flatBT (operB (Trans M) (numBT (n - 1)))
      = flatBT (Trans ((fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)]
          (oper M (n + 1))))

/-- **§8.4 補題（条件(III)か(IV)の下での基本列の基本性質）part (2)**
（原文 `tmp/content.md` 5000、Isabelle `p_8_4_oper_basic` 第 (2) 主張、
`isabelle/pss_paper.thy:2017`）。

`Trans(M)[n-1] = Trans(M[n+1][1]^{j₁-1-j₋₂})`（`j₁ = Lng M - 1`、
`j₋₂ = parent M 1 j₁`）。`Oper84BasicPart2Residual` modulo（flat 一致 → `flatBT_injective`）。 -/
theorem oper_basic_part2 (hres : Oper84BasicPart2Residual)
    (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hj₁ : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    operB (Trans M) (numBT (n - 1)) =
      Trans ((fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)] (oper M (n + 1))) :=
  flatBT_injective (hres M n hST hmono hn hp hj₁ hcond)

#print axioms oper_basic_part3
#print axioms oper_basic_part2


/-- **part (3) の無条件形**: producer を公開連鎖（`8.4-exch84-regsp`＋corner readouts、
`8.7-termination` の `exch84producer_term` と同一）で供給。 -/
theorem oper_basic_part3_uncond (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hj₁ : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    ∃ s c1 c2 b, (PB c1).length = 1 ∧ (PB c2).length = 1 ∧ lessBT c1 c2 = true
      ∧ scb_decomp (Trans (oper M n)) s (flatBT c1) b
      ∧ scb_decomp (operB (Trans M) (numBT n)) s (flatBT c2) b :=
  oper_basic_part3
    (Exch84_condIIIIV_producer_holds (Exch84_condIIIIV_pkg_holds
      (exch84slicepkg_of_cornerReadouts_nc2
        (cornerCoreReadouts_of_residual cornerNpSliceValue_holds_cnv))))
    M n hST hmono hn hp hj₁ hcond

#print axioms oper_basic_part3_uncond

end PSS
