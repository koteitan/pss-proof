import «8».«8.7-pred-oper0-corners»

/-!
# §8.7 補題 — 共有 scb 文脈での**一般末尾零化**（原文 `p_8_7_OT_tail_annihilable` の scb 逐語形）

- 原文: `tmp/content.md` article 6018–6058（簡約性→条件(A)(B)→scb 置換可能性→
  条件(I)–(VI) 分析）の hard core。姉妹ファイル `8.7-pred-oper0-corners.lean` が
  枝 (II)/(IV) を単一残差 `PredOper0_scbCtx_residual_pc`（共有 scb 文脈での
  `transC2 M → transC1 M` の `[0]`-降下）へ尖鋭化済み。本ファイルはその残差を、
  一般 **body-annihilation エンジン** で討伐する。
- Isabelle: `p_8_7_OT_tail_annihilable`（`sorry` のまま）。本ファイルは Isabelle corpus を
  **超える**（beyond-Isabelle）。数値監査は 806/806（枝 II/IV の 129 ホスト全通過、
  観測最大カスケード長 `k = 13`）。

## 構成

1. **エンジン `scb_body_annihilable_ta`**：任意の body `t' ∈ T_B` について、共有 scb 文脈
   `(s, b)` の中で単項 `D_u t'` は `[0]` 反復で `D_u 0` へ降下する。`btWeight t'` に関する
   強帰納法。既存 `trailing_principal_annihilable`（`8.6`, 末尾 `D_v 0` の除去）を
   末尾 principal ごとに再帰適用する。
2. **末尾 principal 除去 `scb_remove_trailing_principal_ta`**：`D_u(t' +ᴮ D_w body)` から
   末尾 principal `D_w body`（body 任意）を丸ごと落として `D_u t'` へ。エンジンの系。
3. 残差 `PredOper0_scbCtx_residual_pc` の討伐（枝 (II)/(IV) の 4th-branch カスケード）。

## private helper suffix: `_ta`
（`8.6-trailing-principal-annihilable` の private 補題の証明を改名して再利用。）
-/

namespace PSS

/-! ## 0. 補助補題（`8.6` からの改名再利用 + 重み補題） -/

@[simp] private theorem zero_addBT_ta (t : BT) : addBT BZero t = t := by
  rcases t with ⟨ps⟩; rfl

@[simp] private theorem addBT_zero_ta (t : BT) : addBT t BZero = t := by
  rcases t with ⟨ps⟩; simp [addBT, BZero]

private theorem BZero_mem_T_B_ta : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem dfree_BP_of_mem_ta {p : BP} {ps : List BP}
    (hdf : dfree_BPList ps = true) (hp : p ∈ ps) : dfree_BP p = true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp [dfree_BPList] at hdf
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hdf.1
      · exact ih hdf.2 hp

private theorem dfree_BPList_prefix_ta {as : List BP} {q : BP}
    (h : dfree_BPList (as ++ [q]) = true) : dfree_BPList as = true := by
  induction as with
  | nil => simp [dfree_BPList]
  | cons p ps ih =>
      simp only [List.cons_append, dfree_BPList, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih h.2⟩

private theorem scbOfFlat_ta {t : BT} {p : BP} {s b : List Sym}
    (hflat : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp) (hdf : dfree_BP p = true) :
    scb_decomp t s (flatBP p) b := by
  refine ⟨hflat, ?_, hb⟩
  intro _; exact ⟨p, hdf, rfl⟩

/-- multi 項の末尾 principal より前の前置文字列。 -/
private def scbLastPre_ta : List BP → List Sym
  | [] => []
  | p :: ps => .lp :: flatComponentRun (p :: ps)

/-- multi 項の末尾 principal より後の後置文字列。 -/
private def scbLastPost_ta : List BP → List Sym
  | [] => []
  | _ :: _ => [.rp]

private theorem flatBT_snoc_shape_ta (initPs : List BP) (q : BP) :
    flatBT (.trm (initPs ++ [q])) =
      scbLastPre_ta initPs ++ flatBP q ++ scbLastPost_ta initPs := by
  cases hi : initPs with
  | nil => simp [scbLastPre_ta, scbLastPost_ta, flatBT]
  | cons r rs =>
      simpa [scbLastPre_ta, scbLastPost_ta] using flatBT_multi_snoc r rs q

private theorem scbLastPost_all_rp_ta (initPs : List BP) :
    ∀ x ∈ scbLastPost_ta initPs, x = .rp := by
  cases initPs <;> simp [scbLastPost_ta]

/-! ### 重み補題（強帰納法の測度） -/

private theorem bpListWeight_snoc_ta (as : List BP) (q : BP) :
    bpListWeight (as ++ [q]) = bpListWeight as + bpWeight q + 1 := by
  induction as with
  | nil => simp [bpListWeight]
  | cons p ps ih => simp only [List.cons_append, bpListWeight, ih]; omega

private theorem flatBT_Dprin_cons_ta (u : ℕ∞) (X : BT) :
    flatBT (Dprin u X) = Sym.dsym u :: flatBT X := rfl

private theorem flatBP_db_eq_ta (u : ℕ∞) (X : BT) :
    flatBP (.db u X) = flatBT (Dprin u X) := rfl

/-! ## 1. 一般 body-annihilation エンジン

`t' ∈ T_B` の任意の body について、共有 scb 文脈 `(s,b)` の中で `D_u t'` は `[0]` 反復で
`D_u 0` へ降下する。`btWeight t'` に関する強帰納法。末尾 principal `D_w body` を、
その body を再帰で 0 化 → `trailing_principal_annihilable` で除去、を繰り返す。 -/

private theorem scb_body_annihilable_aux_ta :
    ∀ (n : ℕ) (t' : BT), btWeight t' = n → t' ∈ T_B →
      ∀ (t : BT) (s b : List Sym) (u : ℕ), t ∈ T_B →
        scb_decomp t s (flatBT (Dprin (u : ℕ∞) t')) b →
        ∃ k, scb_decomp (((fun a => operB a (numBT 0))^[k]) t) s
              (flatBT (Dprin (u : ℕ∞) BZero)) b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t' hn ht' t s b u ht hd
    rcases t' with ⟨ps⟩
    cases ps with
    | nil =>
        exact ⟨0, by simpa using hd⟩
    | cons y ys =>
        -- 末尾 principal を分離： y::ys = initPs ++ [.db w body]
        obtain ⟨initPs, q, hsn⟩ :
            ∃ initPs q, y :: ys = initPs ++ [q] :=
          ⟨(y :: ys).dropLast, (y :: ys).getLast (by simp),
            (List.dropLast_append_getLast (by simp)).symm⟩
        rcases q with ⟨w, body⟩
        rw [hsn] at hd ht' hn
        set pre := scbLastPre_ta initPs with hpre
        set post := scbLastPost_ta initPs with hpost
        -- `t'` の平坦形
        have ht'flat : flatBT (.trm (initPs ++ [.db w body])) =
            pre ++ flatBP (.db w body) ++ post :=
          flatBT_snoc_shape_ta initPs (.db w body)
        -- dfree / T_B 抽出
        have hdfList : dfree_BPList (initPs ++ [.db w body]) = true := ht'
        have hdfq : dfree_BP (.db w body) = true :=
          dfree_BP_of_mem_ta hdfList (by simp)
        have hdfInit : dfree_BPList initPs = true :=
          dfree_BPList_prefix_ta hdfList
        have hwtop : w ≠ ⊤ := by
          have := hdfq; simp [dfree_BP] at this; exact this.1
        have hbodyTB : body ∈ T_B := by
          have := hdfq; simp [dfree_BP] at this; exact this.2
        have hinitTB : (BT.trm initPs) ∈ T_B := hdfInit
        set wN : ℕ := w.toNat with hwNdef
        have hwN : (wN : ℕ∞) = w := ENat.coe_toNat hwtop
        -- s2, b2（body を囲む scb 文脈）
        set s2 : List Sym := s ++ Sym.dsym (u : ℕ∞) :: pre with hs2
        set b2 : List Sym := post ++ b with hb2
        have hb : ∀ x ∈ b, x = .rp := hd.2.2
        have hb2rp : ∀ x ∈ b2, x = .rp := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact scbLastPost_all_rp_ta initPs x hx
          · exact hb x hx
        -- 元 occurrence（外側 principal `.db u t'`）
        have hdocc0 : flatBT t = s ++ flatBP (.db (u : ℕ∞) (.trm (initPs ++ [.db w body]))) ++ b := by
          have := hd.1
          rw [flatBP_db_eq_ta]; exact this
        -- body の occurrence at (s2, b2)
        have hoccBody : flatBT t = s2 ++ flatBP (.db w body) ++ b2 := by
          rw [hd.1, flatBT_Dprin_cons_ta, ht'flat, hs2, hb2]
          simp [List.append_assoc]
        have hdBody : scb_decomp t s2 (flatBT (Dprin (wN : ℕ∞) body)) b2 := by
          have h := scbOfFlat_ta hoccBody hb2rp hdfq
          rw [flatBP_db_eq_ta, ← hwN] at h; exact h
        -- IH on body
        have hlt_body : btWeight body < n := by
          rw [← hn]; simp only [btWeight, bpListWeight_snoc_ta, bpWeight]; omega
        obtain ⟨k1, hk1⟩ :=
          ih (btWeight body) hlt_body body rfl hbodyTB t s2 b2 wN ht hdBody
        -- 変換： s2..b2 で D_wN 0 ⟹ s..b で D_u(init +ᴮ D_wN 0)
        set init : BT := BT.trm initPs with hinitdef
        set bodyNew : BT := addBT init (Dprin (wN : ℕ∞) BZero) with hbodyNew
        have hbodyNewTB : bodyNew ∈ T_B :=
          addBT_mem_T_B hinitTB (Dprin_mem_T_B (by simp) BZero_mem_T_B_ta)
        have hdfNew : dfree_BP (.db (u : ℕ∞) bodyNew) = true := by
          simp only [dfree_BP, Bool.and_eq_true, bne_iff_ne]
          exact ⟨by simp, hbodyNewTB⟩
        have hbodyNewflat : flatBT bodyNew = pre ++ flatBT (Dprin (wN : ℕ∞) BZero) ++ post := by
          rw [hbodyNew, hinitdef]
          change flatBT (BT.trm (initPs ++ [.db (wN : ℕ∞) BZero])) = _
          rw [flatBT_snoc_shape_ta initPs (.db (wN : ℕ∞) BZero), flatBP_db_eq_ta]
        have hFk1flat : flatBT (((fun a => operB a (numBT 0))^[k1]) t) =
            s ++ flatBT (Dprin (u : ℕ∞) bodyNew) ++ b := by
          rw [flatBT_Dprin_cons_ta (u : ℕ∞) bodyNew, hbodyNewflat, hk1.1, hs2, hb2]
          simp [List.append_assoc]
        have hFk1occ : flatBT (((fun a => operB a (numBT 0))^[k1]) t) =
            s ++ flatBP (.db (u : ℕ∞) bodyNew) ++ b := by
          rw [hFk1flat, flatBP_db_eq_ta]
        have hFk1TB : ((fun a => operB a (numBT 0))^[k1]) t ∈ T_B := by
          obtain ⟨t1, ht1TB, ht1flat⟩ :=
            principal_replacement_image ht hdfNew hdocc0
          have : ((fun a => operB a (numBT 0))^[k1]) t = t1 :=
            flatBT_injective (hFk1occ.trans ht1flat.symm)
          rw [this]; exact ht1TB
        have hdConv : scb_decomp (((fun a => operB a (numBT 0))^[k1]) t) s
            (flatBT (Dprin (u : ℕ∞) bodyNew)) b := by
          have h := scbOfFlat_ta hFk1occ hb hdfNew
          rw [flatBP_db_eq_ta] at h; exact h
        -- trailing_principal_annihilable： D_u(init +ᴮ D_wN 0) ⟹ D_u init
        obtain ⟨k2, _, _, hc2⟩ :=
          trailing_principal_annihilable
            (((fun a => operB a (numBT 0))^[k1]) t) init s b u wN
            hFk1TB hinitTB hdConv
        -- F^[k2] (F^[k1] t) ∈ T_B
        have hF21flat : flatBT (((fun a => operB a (numBT 0))^[k2])
            (((fun a => operB a (numBT 0))^[k1]) t)) =
            s ++ flatBP (.db (u : ℕ∞) init) ++ b := by
          rw [hc2.1, flatBP_db_eq_ta]
        have hdfInitP : dfree_BP (.db (u : ℕ∞) init) = true := by
          simp only [dfree_BP, Bool.and_eq_true, bne_iff_ne]
          exact ⟨by simp, hinitTB⟩
        have hF21TB : ((fun a => operB a (numBT 0))^[k2])
            (((fun a => operB a (numBT 0))^[k1]) t) ∈ T_B := by
          obtain ⟨t2, ht2TB, ht2flat⟩ :=
            principal_replacement_image ht hdfInitP hdocc0
          have : ((fun a => operB a (numBT 0))^[k2])
              (((fun a => operB a (numBT 0))^[k1]) t) = t2 :=
            flatBT_injective (hF21flat.trans ht2flat.symm)
          rw [this]; exact ht2TB
        -- IH on init
        have hlt_init : btWeight init < n := by
          rw [← hn, hinitdef]
          simp only [btWeight, bpListWeight_snoc_ta, bpWeight]; omega
        obtain ⟨k3, hc3⟩ :=
          ih (btWeight init) hlt_init init rfl hinitTB
            (((fun a => operB a (numBT 0))^[k2])
              (((fun a => operB a (numBT 0))^[k1]) t)) s b u hF21TB hc2
        refine ⟨k3 + (k2 + k1), ?_⟩
        rw [Function.iterate_add_apply _ k3 (k2 + k1),
            Function.iterate_add_apply _ k2 k1]
        exact hc3

/-- **一般 body-annihilation エンジン**（原文 `p_8_7_OT_tail_annihilable` の scb 逐語形）。
`t'` が共有 scb 文脈 `(s,b)` の中で `D_u` の body として現れるとき、`[0]` 反復で
`D_u t' ⟹ D_u 0` へ降下する。 -/
theorem scb_body_annihilable_ta (t' : BT) (ht' : t' ∈ T_B)
    (t : BT) (s b : List Sym) (u : ℕ) (ht : t ∈ T_B)
    (hd : scb_decomp t s (flatBT (Dprin (u : ℕ∞) t')) b) :
    ∃ k, scb_decomp (((fun a => operB a (numBT 0))^[k]) t) s
          (flatBT (Dprin (u : ℕ∞) BZero)) b :=
  scb_body_annihilable_aux_ta _ t' rfl ht' t s b u ht hd

#print axioms scb_body_annihilable_ta

/-! ## 2. 末尾 principal への降下・再構成（汎用ナビゲーション）

`t` が共有 scb 文脈 `(s,b)` の中で `D_v(Y +ᴮ D_w innerbody)` を占めるとき、末尾 principal
`D_w innerbody` を deeper 文脈で reduce（引数 `hred`）して単項 `D_{w'} ib'` に置換した
`D_v(Y +ᴮ D_{w'} ib')` へ、`[0]` 反復で到達する。エンジンと Brick 2/case-B の共通ナビ。 -/

private theorem scb_reduce_last_gen_ta (t : BT) (s b : List Sym) (v : ℕ) (Y : BT)
    (w : ℕ∞) (innerbody : BT) (w' : ℕ∞) (ib' : BT)
    (ht : t ∈ T_B) (hY : Y ∈ T_B) (hw : w ≠ ⊤) (hinner : innerbody ∈ T_B)
    (hw' : w' ≠ ⊤) (hib' : ib' ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (v : ℕ∞) (addBT Y (Dprin w innerbody)))) b)
    (hred : ∀ (t0 : BT) (s0 b0 : List Sym), t0 ∈ T_B →
       scb_decomp t0 s0 (flatBT (Dprin w innerbody)) b0 →
       ∃ k, scb_decomp (((fun a => operB a (numBT 0))^[k]) t0) s0
             (flatBT (Dprin w' ib')) b0) :
    ∃ k, scb_decomp (((fun a => operB a (numBT 0))^[k]) t) s
          (flatBT (Dprin (v : ℕ∞) (addBT Y (Dprin w' ib')))) b := by
  rcases Y with ⟨YPs⟩
  set pre := scbLastPre_ta YPs with hpre
  set post := scbLastPost_ta YPs with hpost
  have hq_shape : flatBT (BT.trm (YPs ++ [.db w innerbody])) =
      pre ++ flatBP (.db w innerbody) ++ post :=
    flatBT_snoc_shape_ta YPs (.db w innerbody)
  have hq'_shape : flatBT (BT.trm (YPs ++ [.db w' ib'])) =
      pre ++ flatBP (.db w' ib') ++ post :=
    flatBT_snoc_shape_ta YPs (.db w' ib')
  have haddq : addBT (BT.trm YPs) (Dprin w innerbody) =
      BT.trm (YPs ++ [.db w innerbody]) := rfl
  have hb : ∀ x ∈ b, x = .rp := hd.2.2
  set s2 : List Sym := s ++ Sym.dsym (v : ℕ∞) :: pre with hs2
  set b2 : List Sym := post ++ b with hb2
  have hb2rp : ∀ x ∈ b2, x = .rp := by
    intro x hx; rcases List.mem_append.mp hx with hx | hx
    · exact scbLastPost_all_rp_ta YPs x hx
    · exact hb x hx
  have hdfq : dfree_BP (.db w innerbody) = true := by
    simp only [dfree_BP, Bool.and_eq_true, bne_iff_ne]; exact ⟨hw, hinner⟩
  have hdmark : flatBT t =
      s ++ flatBT (Dprin (v : ℕ∞) (BT.trm (YPs ++ [.db w innerbody]))) ++ b := by
    have := hd.1; rw [haddq] at this; exact this
  have hoccInner : flatBT t = s2 ++ flatBP (.db w innerbody) ++ b2 := by
    rw [hdmark, flatBT_Dprin_cons_ta, hq_shape, hs2, hb2]; simp [List.append_assoc]
  have hdInner : scb_decomp t s2 (flatBT (Dprin w innerbody)) b2 := by
    have h := scbOfFlat_ta hoccInner hb2rp hdfq; rw [flatBP_db_eq_ta] at h; exact h
  obtain ⟨k, hk⟩ := hred t s2 b2 ht hdInner
  set P'add : BT := addBT (BT.trm YPs) (Dprin w' ib') with hP'add
  have hP'addTB : P'add ∈ T_B := addBT_mem_T_B hY (Dprin_mem_T_B hw' hib')
  have hdfMark' : dfree_BP (.db (v : ℕ∞) P'add) = true := by
    simp only [dfree_BP, Bool.and_eq_true, bne_iff_ne]; exact ⟨by simp, hP'addTB⟩
  have hP'addflat : flatBT P'add = pre ++ flatBT (Dprin w' ib') ++ post := by
    rw [hP'add]
    change flatBT (BT.trm (YPs ++ [.db w' ib'])) = _
    rw [hq'_shape, flatBP_db_eq_ta]
  have hFkflat : flatBT (((fun a => operB a (numBT 0))^[k]) t) =
      s ++ flatBT (Dprin (v : ℕ∞) P'add) ++ b := by
    rw [flatBT_Dprin_cons_ta (v : ℕ∞) P'add, hP'addflat, hk.1, hs2, hb2]
    simp [List.append_assoc]
  have hFkocc : flatBT (((fun a => operB a (numBT 0))^[k]) t) =
      s ++ flatBP (.db (v : ℕ∞) P'add) ++ b := by rw [hFkflat, flatBP_db_eq_ta]
  refine ⟨k, ?_⟩
  have h := scbOfFlat_ta hFkocc hb hdfMark'
  rw [flatBP_db_eq_ta] at h
  exact h

/-- **Brick 2**：共有 scb 文脈で末尾 principal `D_w innerbody`（body 任意）を丸ごと
除去し `D_u t'` へ。エンジン（body 零化）＋ `trailing_principal_annihilable`。 -/
theorem scb_remove_trailing_principal_ta (t : BT) (s b : List Sym) (u w : ℕ)
    (t' innerbody : BT) (ht : t ∈ T_B) (ht' : t' ∈ T_B) (hbody : innerbody ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞) (addBT t' (Dprin (w : ℕ∞) innerbody)))) b) :
    ∃ k, scb_decomp (((fun a => operB a (numBT 0))^[k]) t) s
          (flatBT (Dprin (u : ℕ∞) t')) b := by
  -- step 1: 末尾 principal を `D_w 0` へ（エンジンで body を零化）
  obtain ⟨k1, hk1⟩ :=
    scb_reduce_last_gen_ta t s b u t' (w : ℕ∞) innerbody (w : ℕ∞) BZero
      ht ht' (by simp) hbody (by simp) BZero_mem_T_B_ta hd
      (fun t0 s0 b0 ht0 hd0 =>
        scb_body_annihilable_ta innerbody hbody t0 s0 b0 w ht0 hd0)
  -- hk1 : scb_decomp (F^[k1] t) s (flatBT (Dprin u (addBT t' (Dprin w 0)))) b
  have hdocc0 : flatBT t =
      s ++ flatBP (.db (u : ℕ∞) (addBT t' (Dprin (w : ℕ∞) innerbody))) ++ b := by
    rw [flatBP_db_eq_ta]; exact hd.1
  have hdfNew : dfree_BP (.db (u : ℕ∞) (addBT t' (Dprin (w : ℕ∞) BZero))) = true := by
    simp only [dfree_BP, Bool.and_eq_true, bne_iff_ne]
    exact ⟨by simp, addBT_mem_T_B ht' (Dprin_mem_T_B (by simp) BZero_mem_T_B_ta)⟩
  have hFk1occ : flatBT (((fun a => operB a (numBT 0))^[k1]) t) =
      s ++ flatBP (.db (u : ℕ∞) (addBT t' (Dprin (w : ℕ∞) BZero))) ++ b := by
    rw [hk1.1, flatBP_db_eq_ta]
  have hFk1TB : ((fun a => operB a (numBT 0))^[k1]) t ∈ T_B := by
    obtain ⟨t1, ht1TB, ht1flat⟩ :=
      principal_replacement_image ht hdfNew hdocc0
    have : ((fun a => operB a (numBT 0))^[k1]) t = t1 :=
      flatBT_injective (hFk1occ.trans ht1flat.symm)
    rw [this]; exact ht1TB
  obtain ⟨k2, _, _, hc2⟩ :=
    trailing_principal_annihilable (((fun a => operB a (numBT 0))^[k1]) t) t' s b u w
      hFk1TB ht' hk1
  refine ⟨k2 + k1, ?_⟩
  rw [Function.iterate_add_apply _ k2 k1]; exact hc2

#print axioms scb_remove_trailing_principal_ta

/-- **case-B peeler**：`D_v(Y +ᴮ D_w(Z +ᴮ D_j 0))` の末尾 principal から内側の
末尾零項 `D_j 0` を落とし `D_v(Y +ᴮ D_w Z)` へ（`trailing_principal_annihilable`）。 -/
theorem scb_peel_inner_zero_ta (t : BT) (s b : List Sym) (v w j : ℕ) (Y Z : BT)
    (ht : t ∈ T_B) (hY : Y ∈ T_B) (hZ : Z ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (v : ℕ∞)
        (addBT Y (Dprin (w : ℕ∞) (addBT Z (Dprin (j : ℕ∞) BZero)))))) b) :
    ∃ k, scb_decomp (((fun a => operB a (numBT 0))^[k]) t) s
          (flatBT (Dprin (v : ℕ∞) (addBT Y (Dprin (w : ℕ∞) Z)))) b := by
  refine scb_reduce_last_gen_ta t s b v Y (w : ℕ∞)
    (addBT Z (Dprin (j : ℕ∞) BZero)) (w : ℕ∞) Z ht hY (by simp)
    (addBT_mem_T_B hZ (Dprin_mem_T_B (by simp) BZero_mem_T_B_ta))
    (by simp) hZ hd ?_
  intro t0 s0 b0 ht0 hd0
  obtain ⟨k, _, _, h⟩ :=
    trailing_principal_annihilable t0 Z s0 b0 w j ht0 hZ hd0
  exact ⟨k, h⟩

#print axioms scb_peel_inner_zero_ta

/-! ## 3. 具体形からの降下（条件非依存の合成器）

`transC2 M = D_v(t₃ +ᴮ D_{j'}(t₄ +ᴮ D_{j₁} 0))`、`transC1 M = D_v t₂` の共有 scb 文脈で、
`t₂` と `(t₃,t₄)` の関係（case A: `t₂ = t₃` / case B: `t₂ = t₃ +ᴮ D_{j'} t₄`）に応じて
Brick 2（case A）／case-B peeler で `Trans M → Trans (Pred M)` を閉じる。 -/

theorem scbCtx_descent_ta (Big Pred : BT) (s b : List Sym) (v j' j1 : ℕ)
    (t2 t3 t4 : BT)
    (hBig : Big ∈ T_B) (ht3 : t3 ∈ T_B) (ht4 : t4 ∈ T_B)
    (hd1 : scb_decomp Pred s (flatBT (Dprin (v : ℕ∞) t2)) b)
    (hd2 : scb_decomp Big s
      (flatBT (Dprin (v : ℕ∞)
        (addBT t3 (Dprin (j' : ℕ∞) (addBT t4 (Dprin (j1 : ℕ∞) BZero)))))) b)
    (hcase : t2 = t3 ∨ t2 = addBT t3 (Dprin (j' : ℕ∞) t4)) :
    ∃ k, ((fun a => operB a (numBT 0))^[k]) Big = Pred := by
  have hfinish : ∀ k, scb_decomp (((fun a => operB a (numBT 0))^[k]) Big) s
      (flatBT (Dprin (v : ℕ∞) t2)) b →
      ((fun a => operB a (numBT 0))^[k]) Big = Pred := by
    intro k hk
    exact flatBT_injective (by rw [hk.1, hd1.1])
  rcases hcase with hA | hB
  · -- case A: 末尾 principal `D_{j'}(t₄ +ᴮ D_{j₁} 0)` を丸ごと除去 → `D_v t₃ = D_v t₂`
    obtain ⟨k, hk⟩ :=
      scb_remove_trailing_principal_ta Big s b v j' t3
        (addBT t4 (Dprin (j1 : ℕ∞) BZero)) hBig ht3
        (addBT_mem_T_B ht4 (Dprin_mem_T_B (by simp) BZero_mem_T_B_ta)) hd2
    refine ⟨k, hfinish k ?_⟩
    rw [hA]; exact hk
  · -- case B: 内側末尾零項 `D_{j₁} 0` を落として `D_v(t₃ +ᴮ D_{j'} t₄) = D_v t₂`
    obtain ⟨k, hk⟩ :=
      scb_peel_inner_zero_ta Big s b v j' j1 t3 t4 hBig ht3 ht4 hd2
    refine ⟨k, hfinish k ?_⟩
    rw [hB]; exact hk

#print axioms scbCtx_descent_ta

/-! ## 4. 条件 (II) の具体形からの充足 -/

private theorem dfree_BPList_append_ta (as bs : List BP) :
    dfree_BPList (as ++ bs) = (dfree_BPList as && dfree_BPList bs) := by
  induction as with
  | nil => simp [dfree_BPList]
  | cons p ps ih =>
      simp only [List.cons_append, dfree_BPList, ih, Bool.and_assoc]

private theorem addBT_left_mem_ta {a c : BT} (h : addBT a c ∈ T_B) : a ∈ T_B := by
  rcases a with ⟨as⟩; rcases c with ⟨cs⟩
  have hh : dfree_BPList (as ++ cs) = true := h
  rw [dfree_BPList_append_ta] at hh
  simp only [Bool.and_eq_true] at hh; exact hh.1

private theorem addBT_right_mem_ta {a c : BT} (h : addBT a c ∈ T_B) : c ∈ T_B := by
  rcases a with ⟨as⟩; rcases c with ⟨cs⟩
  have hh : dfree_BPList (as ++ cs) = true := h
  rw [dfree_BPList_append_ta] at hh
  simp only [Bool.and_eq_true] at hh; exact hh.2

private theorem Dprin_body_mem_ta {v : ℕ∞} {a : BT} (h : Dprin v a ∈ T_B) :
    a ∈ T_B := by
  have h' : (v != ⊤) = true ∧ dfree_BT a = true := by
    simpa [T_B, Dprin, dfree_BT, dfree_BP, dfree_BPList] using h
  simpa [T_B] using h'.2

private theorem SigmaB_map_singleton_ta (l : List BP) :
    SigmaB (l.map (fun p => BT.trm [p])) = BT.trm l := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
      have ihl : ((ps.map (fun p => BT.trm [p])).flatMap untrm) = ps := by
        simpa [SigmaB, BT.trm.injEq] using ih
      simp [SigmaB, untrm, ihl]

/-- 末尾 principal の切出し（`PB_split_last_sc`/`_rp` の改名コピー）。 -/
private theorem PB_split_last_ta (t : BT) (ht : t ≠ BZero) :
    ∃ (v : ℕ∞) (u : BT),
      (PB t).getD ((PB t).length - 1) BZero = Dprin v u ∧
      t = addBT (SigmaB ((PB t).take ((PB t).length - 1))) (Dprin v u) := by
  rcases t with ⟨ps⟩
  have hne : ps ≠ [] := by
    intro h; exact ht (by simp [h, BZero])
  have hpos : 0 < ps.length := List.length_pos_of_ne_nil hne
  have hidx : ps.length - 1 < ps.length := by omega
  have hPB : PB (BT.trm ps) = ps.map (fun p => BT.trm [p]) := rfl
  have hlenPB : (PB (BT.trm ps)).length = ps.length := by simp [hPB]
  rcases hlast : ps[ps.length - 1] with ⟨v, u⟩
  refine ⟨v, u, ?_, ?_⟩
  · have h1 : (PB (BT.trm ps)).getD ((PB (BT.trm ps)).length - 1) BZero
        = (ps.map (fun p => BT.trm [p]))[ps.length - 1]'(by simpa using hidx) := by
      rw [hlenPB, hPB]
      exact getD_eq_getElem_idx _ BZero (by simpa using hidx)
    rw [h1]
    simp [List.getElem_map, hlast, Dprin]
  · have htake : (PB (BT.trm ps)).take ((PB (BT.trm ps)).length - 1)
        = (ps.take (ps.length - 1)).map (fun p => BT.trm [p]) := by
      rw [hlenPB, hPB, ← List.map_take]
    rw [htake, SigmaB_map_singleton_ta]
    show BT.trm ps = addBT (BT.trm (ps.take (ps.length - 1))) (BT.trm [BP.db v u])
    have hsplit : ps.take (ps.length - 1) ++ [ps[ps.length - 1]] = ps := by
      conv_rhs => rw [← List.take_append_drop (ps.length - 1) ps]
      congr 1
      rw [List.drop_eq_getElem_cons hidx]
      have hsucc : ps.length - 1 + 1 = ps.length := by omega
      rw [hsucc, List.drop_length]
    rw [hlast] at hsplit
    simp only [addBT, BT.trm.injEq]
    exact hsplit.symm

private theorem bpHeadV_Dprin_ta (v : ℕ∞) (a : BT) : bpHeadV (Dprin v a) = v := rfl
private theorem bpHeadT_Dprin_ta (v : ℕ∞) (a : BT) : bpHeadT (Dprin v a) = a := rfl

#print axioms PB_split_last_ta

/-- 条件非依存の共通末尾：`transC1 M = D_{v₀} t₂`・`transC2 M = D_{v₀}(t₃ +ᴮ D_{j'}(t₄ +ᴮ
D_{jᵢ} 0))`（`t₃=condII_t3 M`, `t₄=condII_t4 M`）の scb 分解と `t₂≠0`・`t₂∈T_B` から、
`condII_ldj` の case 分岐（PB 分割）で `t₃,t₄∈T_B` と `hcase` を作り
`scbCtx_descent_ta` を呼ぶ。 -/
private theorem scbCtx_finish_ta (M : PS) (s b : List Sym) (v0 j'0 jinner : ℕ)
    (hR : RTPS M) (ht2ne : transT2 M ≠ BZero) (ht2TB : transT2 M ∈ T_B)
    (hj'0 : (j'0 : ℕ∞) = (entry M 1 (transJ0 M) : ℕ∞))
    (hd1 : scb_decomp (Trans (Pred M)) s (flatBT (Dprin (v0 : ℕ∞) (transT2 M))) b)
    (hd2 : scb_decomp (Trans M) s
      (flatBT (Dprin (v0 : ℕ∞)
        (addBT (condII_t3 M) (Dprin (j'0 : ℕ∞)
          (addBT (condII_t4 M) (Dprin (jinner : ℕ∞) BZero)))))) b) :
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M) := by
  have ht3TB : condII_t3 M ∈ T_B := by
    by_cases hldj : condII_ldj M = true
    · simp only [condII_t3, hldj, if_true]
      obtain ⟨vpj, upj, _, hsplit⟩ := PB_split_last_ta (transT2 M) ht2ne
      exact addBT_left_mem_ta (hsplit ▸ ht2TB)
    · simp only [condII_t3, hldj]; exact ht2TB
  have ht4TB : condII_t4 M ∈ T_B := by
    by_cases hldj : condII_ldj M = true
    · simp only [condII_t4, hldj, if_true]
      obtain ⟨vpj, upj, hpjeq, hsplit⟩ := PB_split_last_ta (transT2 M) ht2ne
      have hpj : condII_pj M = Dprin vpj upj := hpjeq
      rw [hpj, bpHeadT_Dprin_ta]
      exact Dprin_body_mem_ta (addBT_right_mem_ta (hsplit ▸ ht2TB))
    · simp only [condII_t4, hldj]; exact ht2TB
  have hcase : transT2 M = condII_t3 M ∨
      transT2 M = addBT (condII_t3 M) (Dprin (j'0 : ℕ∞) (condII_t4 M)) := by
    by_cases hldj : condII_ldj M = true
    · right
      obtain ⟨vpj, upj, hpjeq, hsplit⟩ := PB_split_last_ta (transT2 M) ht2ne
      have hpj : condII_pj M = Dprin vpj upj := hpjeq
      have ht3v : condII_t3 M
          = SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1)) := by
        simp only [condII_t3, hldj, if_true]
      have ht4v : condII_t4 M = upj := by
        simp only [condII_t4, hldj, if_true, hpj, bpHeadT_Dprin_ta]
      have hvpj : (j'0 : ℕ∞) = vpj := by
        have hh : bpHeadV (condII_pj M) = (entry M 1 (transJ0 M) : ℕ∞) := by
          have := hldj; simp only [condII_ldj, beq_iff_eq] at this; exact this
        rw [hpj, bpHeadV_Dprin_ta] at hh
        rw [hj'0]; exact hh.symm
      rw [ht3v, ht4v, hvpj]; exact hsplit
    · left; unfold condII_t3; rw [if_neg hldj]
  exact scbCtx_descent_ta (Trans M) (Trans (Pred M)) s b v0 j'0 jinner
    (transT2 M) (condII_t3 M) (condII_t4 M) (Trans_mem_T_B M hR) ht3TB ht4TB
    hd1 hd2 hcase

/-- 条件非依存の準備：`transC1 M = Dprin (transV M) (transT2 M)`（単一 principal）と
`transV M ≠ ⊤`・`transT2 M ∈ T_B`。RTPS の下で `transC1_single_principal` から。 -/
private theorem transC1_reconstruct_ta (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (ht1 : Trans (Pred M) ≠ BZero) :
    transC1 M = Dprin (transV M) (transT2 M) ∧ transV M ≠ ⊤ ∧ transT2 M ∈ T_B := by
  have hj1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  have hc1len := transC1_single_principal M hR hmono hj1pos ht1
  have hc1eqTV : transC1 M = Dprin (transV M) (transT2 M) := by
    simpa [transV, transT2] using principal_reconstruct hc1len
  have c1TB : transC1 M ∈ T_B := by
    have hp : hasParent M 0 (Lng M - 1) = true :=
      mono_hasParent_row0 M (RTPS_TPS M hR) hmono (Lng M - 1) (by omega) (by omega)
    have hmk : Marked (Pred M) (Adm M (parent M 0 (Lng M - 1))) :=
      Marked_Pred_Adm M (RTPS_TPS M hR) hlen hp
    have hh : Mark (Pred M) (Adm M (parent M 0 (Lng M - 1))) ∈ T_B :=
      Mark_mem_T_B (Pred M) _ (RTPS_Pred M hR) hmk
    simpa [transC1, transJm1, transJ0, lastParent, lastIdx] using hh
  have hmem : Dprin (transV M) (transT2 M) ∈ T_B := hc1eqTV ▸ c1TB
  have h' : (transV M != ⊤) = true ∧ dfree_BT (transT2 M) = true := by
    simpa [T_B, Dprin, dfree_BT, dfree_BP, dfree_BPList] using hmem
  exact ⟨hc1eqTV, by simpa [bne_iff_ne] using h'.1, h'.2⟩

/-- `1 < Lng M - 1`：`adm M (lastParent M) = false`（II/IV いずれも成立）と `1 < Lng M` から。 -/
private theorem Lng_gt_two_of_nadm_ta (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (hnadm : adm M (lastParent M) = false) : 1 < Lng M - 1 := by
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M (RTPS_TPS M hR) hmono (Lng M - 1) (by omega) (by omega)
  have hjplt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have hparR := nextR_parent0_of_hasParent M (Lng M - 1) hp
    have hh : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
      simpa [nextR] using hparR
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hlp : lastParent M = parent M 0 (Lng M - 1) := by simp [lastParent, lastIdx]
  have hpne0 : parent M 0 (Lng M - 1) ≠ 0 := by
    intro h; rw [hlp, h, adm_zero M] at hnadm; exact absurd hnadm (by simp)
  omega

private theorem j'0_eq_transJ0_ta (M : PS) :
    (entry M 1 (lastParent M) : ℕ∞) = (entry M 1 (transJ0 M) : ℕ∞) := by
  simp [transJ0]

/-- 条件 (II) の host での残差充足。 -/
theorem predOper0_scbCtx_condII_ta (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (ht1 : Trans (Pred M) ≠ BZero) (hcondII : transCondII M = true)
    (s b : List Sym)
    (hd1 : scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b)
    (hd2 : scb_decomp (Trans M) s (flatBT (transC2 M)) b) :
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M) := by
  have hcond' : entry M 1 (lastIdx M) = 0 ∧ adm M (lastParent M) = false := by
    simpa [transCondII, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] using hcondII
  have hLm1 : 1 < Lng M - 1 := Lng_gt_two_of_nadm_ta M hR hmono hlen hcond'.2
  obtain ⟨hc1eqTV, hvtop, ht2TB⟩ := transC1_reconstruct_ta M hR hmono hlen ht1
  have hc2 := condII_c2_val_holds M hR hmono hLm1 hcondII
  have hV2 : transV M = (entry M 1 (Adm M (parent M 0 (Lng M - 1))) : ℕ∞) :=
    (condII_c1_shape_holds M hR hmono hLm1 hcondII).2.1
  have ht2ne : transT2 M ≠ BZero :=
    (condII_host_basic_holds M hR hmono hLm1 hcondII).2.2.2.2.2.2.2.2
  set v0 : ℕ := (transV M).toNat with hv0def
  have hv0 : (v0 : ℕ∞) = transV M := ENat.coe_toNat hvtop
  set j'0 : ℕ := entry M 1 (parent M 0 (Lng M - 1)) with hj'0def
  have hC1form : transC1 M = Dprin (v0 : ℕ∞) (transT2 M) := by rw [hc1eqTV, hv0]
  have hC2form : transC2 M = Dprin (v0 : ℕ∞)
      (addBT (condII_t3 M) (Dprin (j'0 : ℕ∞)
        (addBT (condII_t4 M) (Dprin ((0 : ℕ) : ℕ∞) BZero)))) := by
    rw [hc2, ← hV2, ← hv0]; simp only [Nat.cast_zero]
  rw [hC1form] at hd1
  rw [hC2form] at hd2
  refine scbCtx_finish_ta M s b v0 j'0 0 hR ht2ne ht2TB ?_ hd1 hd2
  rw [hj'0def]
  have hlp : parent M 0 (Lng M - 1) = lastParent M := by simp [lastParent, lastIdx]
  rw [hlp]; exact j'0_eq_transJ0_ta M

/-- 条件 (IV) の host での残差充足。RTPS 版の `transC2Core` 4th-branch 直接展開。 -/
theorem predOper0_scbCtx_condIV_ta (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hlen : 1 < Lng M) (ht1 : Trans (Pred M) ≠ BZero) (hcondIV : transCondIV M = true)
    (s b : List Sym)
    (hd1 : scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b)
    (hd2 : scb_decomp (Trans M) s (flatBT (transC2 M)) b) :
    ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M) := by
  have hcond' : (0 < entry M 1 (lastIdx M) ∧
      entry M 1 (lastIdx M) ≤ entry M 1 (lastParent M)) ∧
      adm M (lastParent M) = false := by
    simpa [transCondIV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      using hcondIV
  obtain ⟨⟨he0, hle⟩, hnadm⟩ := hcond'
  have hLm1 : 1 < Lng M - 1 := Lng_gt_two_of_nadm_ta M hR hmono hlen hnadm
  obtain ⟨hc1eqTV, hvtop, ht2TB⟩ := transC1_reconstruct_ta M hR hmono hlen ht1
  -- 枝 (I)/(III)/(V)/(VI) を潰す
  have hbe : (entry M 1 (lastParent M) + 1 == entry M 1 (lastIdx M)) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  have hI : transCondI M = false := by
    simp only [transCondI, Bool.and_eq_false_iff, beq_eq_false_iff_ne]; left; omega
  have hIII : transCondIII M = false := by
    simp only [transCondIII, hnadm, Bool.and_false]
  have hV : transCondV M = false := by
    simp only [transCondV, hbe, Bool.and_false, Bool.false_and]
  have hVI : transCondVI M = false := by
    simp only [transCondVI, hbe, Bool.and_false, Bool.false_and]
  have hnotA : ¬(transCondI M = true ∨ transCondIII M = true ∨ transCondV M = true) := by
    simp [hI, hIII, hV]
  have ht2ne : transT2 M ≠ BZero := t2ne_notAVI M hR hmono hlen hLm1 hnotA hVI
  have ht2b : (transT2 M == BZero) = false := by simpa [beq_eq_false_iff_ne] using ht2ne
  -- 4th-branch 展開
  have hC2form0 : transC2 M = Dprin (transV M)
      (addBT (condII_t3 M) (Dprin (entry M 1 (lastParent M) : ℕ∞)
        (addBT (condII_t4 M) (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero)))) := by
    rw [transC2, transC2Core]
    simp only [hI, hIII, hV, hVI, ht2b, Bool.or_self, Bool.false_eq_true, if_false]
    rfl
  set v0 : ℕ := (transV M).toNat with hv0def
  have hv0 : (v0 : ℕ∞) = transV M := ENat.coe_toNat hvtop
  have hC1form : transC1 M = Dprin (v0 : ℕ∞) (transT2 M) := by rw [hc1eqTV, hv0]
  have hC2form : transC2 M = Dprin (v0 : ℕ∞)
      (addBT (condII_t3 M) (Dprin ((entry M 1 (lastParent M) : ℕ) : ℕ∞)
        (addBT (condII_t4 M) (Dprin ((entry M 1 (lastIdx M) : ℕ) : ℕ∞) BZero)))) := by
    rw [hC2form0, hv0]
  rw [hC1form] at hd1
  rw [hC2form] at hd2
  refine scbCtx_finish_ta M s b v0 (entry M 1 (lastParent M)) (entry M 1 (lastIdx M))
    hR ht2ne ht2TB ?_ hd1 hd2
  exact j'0_eq_transJ0_ta M

#print axioms predOper0_scbCtx_condII_ta
#print axioms predOper0_scbCtx_condIV_ta

/-! ## 5. 残差 `PredOper0_scbCtx_residual_pc` の討伐 ＋ 一般形の無条件化 -/

/-- **本ミッションの主結果**：`8.7-pred-oper0-corners` の唯一残差
`PredOper0_scbCtx_residual_pc`（共有 scb 文脈での `transC2 → transC1` の `[0]`-降下、
原文 `p_8_7_OT_tail_annihilable` の scb 逐語形＝Isabelle も `sorry`）を、
条件 (II)/(IV) いずれでも一般 body-annihilation エンジンで討伐する。 -/
theorem predOper0_scbCtx_residual_holds_pc : PredOper0_scbCtx_residual_pc := by
  intro M hR hmono hlen ht1 hcond s b hd1 hd2
  rcases hcond with hII | hIV
  · exact predOper0_scbCtx_condII_ta M hR hmono hlen ht1 hII s b hd1 hd2
  · exact predOper0_scbCtx_condIV_ta M hR hmono hlen ht1 hIV s b hd1 hd2

#print axioms predOper0_scbCtx_residual_holds_pc

/-- **BONUS**：残差が討伐できたので、原文 §8.7「補題（`Pred` と `[0]` の関係）」の
一般忠実形 `PredOper0_pg`（`8.7-Pred-oper0-general`）が**無条件**に成立する。
（`p_8_7_Pred_oper0_of_scbCtx_pc`（`8.7-pred-oper0-corners`）へ本残差を流し込む。） -/
theorem p_8_7_Pred_oper0_pg_uncond : PredOper0_pg :=
  p_8_7_Pred_oper0_of_scbCtx_pc predOper0_scbCtx_residual_holds_pc

#print axioms p_8_7_Pred_oper0_pg_uncond

end PSS
