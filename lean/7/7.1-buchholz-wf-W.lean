import «7».«7.3-Trans-welldefined»
import PSS.Buchholz

/-!
# §7.1 [Buc1] 2.2 キャンペーン — `W` 階層の土台 (foundation 1/2)

- 原文: `tmp/content.md` 5978 / 6331（`(OT_B, <)` の整礎性を [Buc1] 補題 2.2 で引用）
- [Buc1]: §2 p.137–138 の反復帰納的定義 `W_v = lfp(A_v)`（(W1)(W2)(W3)）と
  p.137 命題 `u ≤ v ⟹ W_u ⊆ W_v`
- 訂正: なし
- Isabelle: `isabelle/layerC/pss_scratch.thy`
  - `bwl_Aop` (8695), `bwl_Aset` (8701), `bwl_Aop_mono_nv` (8719),
    `bwl_Wf` / `bwl_W` (8750), `bwl_A2` (8807), `bwl_A1_intro` (8818),
    `bwl_A2'` (8835), `bwl_W_zero` (8846)
  - `y3_W_mono` (11280), `y3_TBv_dfree_W_aux` (11295), `y3_TBv_dfree_W` (11320),
    `y3_dfree_ex_lev_aux` (11333), `y3_dfree_ex_lev` (11370),
    `y3_Trans_dfree` (11390), `y3_one_in_TBv` (11403),
    `y3_D0one_not_NatSet` (11406), `y3_TBv_ne_zeroset` (11416),
    `y3_TBv_ne_NatSet` (11424), `y3_TBv_inj` (11432)
- 依存: `PSS.Buchholz`（`BT`/`BP`/`TBv`/`NatSet`/`numBT`/`domB`/`operB`/`addBT`/
  `dfree_BT`）、`7.3-Trans-welldefined`（`Trans_mem_T_B`）
- 状態: ✅ green（sorry 0）。`Bwl28Principal` / `Bwl24bAdd` の 2 つの名前付き仮定
  （[Buc1] 2.8 / 2.4(b)、foundation 2/2 の担当）に modulo。

引用する [Buc1] 2.2 は**意味論的**（順序数への評価写像 `o` と正則基数 `Ω_u` を使う）で
定義的 HOL / Lean では表現できない。原文が実際に使うのは構文的な帰結だけであり、
Isabelle 版はそれを Buchholz–Schütte の distinguished sets 法（基数不要）で証明した。
本キャンペーンはそちらを移植する。**順序数・`ψ`・`Ω` は一切導入しない。**

`W_v` は**反復**帰納的定義である: (W3) の `W_u` (`u < v`) は生成中の集合に対して
単調でないパラメータ位置に現れるので、単一の `lfp` では作れない。Isabelle 同様、
段階族 `bwl_Wf` を `v` についての構造的再帰で定義し、各段を（単調作用素の）正直な
最小不動点として取る。
-/

namespace PSS

/-! ## 補助: 最小不動点（Knaster–Tarski の必要な 2 面のみ） -/

/-- `Set BT` 上の最小不動点。Isabelle の `lfp` に対応。 -/
private def lfpS_w3 (f : Set BT → Set BT) : Set BT := ⋂₀ {Y | f Y ⊆ Y}

/-- `lfp_lowerbound`: 前不動点は `lfp` を上から抑える（単調性不要）。 -/
private theorem lfpS_lowerbound_w3 {f : Set BT → Set BT} {Y : Set BT}
    (h : f Y ⊆ Y) : lfpS_w3 f ⊆ Y := fun _ hx => hx Y h

private theorem lfpS_unfold_le_w3 {f : Set BT → Set BT} (hm : Monotone f) :
    f (lfpS_w3 f) ⊆ lfpS_w3 f := by
  intro x hx Y hY
  exact hY (hm (lfpS_lowerbound_w3 hY) hx)

private theorem lfpS_unfold_ge_w3 {f : Set BT → Set BT} (hm : Monotone f) :
    lfpS_w3 f ⊆ f (lfpS_w3 f) :=
  lfpS_lowerbound_w3 (hm (lfpS_unfold_le_w3 hm))

/-- `lfp_unfold`: `f (lfp f) = lfp f`。 -/
private theorem lfpS_unfold_w3 {f : Set BT → Set BT} (hm : Monotone f) :
    f (lfpS_w3 f) = lfpS_w3 f :=
  Set.Subset.antisymm (lfpS_unfold_le_w3 hm) (lfpS_unfold_ge_w3 hm)

/-! ## (1) 作用素 `A_ν` — 下位の族をパラメータとして受け取る -/

/-- [Buc1] p.138 (1)(2)。下位の階層 `Wf` はパラメータ。
    Isabelle: `bwl_Aop` (pss_scratch.thy:8695)。 -/
def bwl_Aop (Wf : ℕ → Set BT) (nv : ℕ∞) (X : Set BT) (a : BT) : Prop :=
  a = BZero ∨
  ((domB a = {BZero} ∨ domB a = NatSet) ∧ (∀ n : ℕ, operB a (numBT n) ∈ X)) ∨
  (∃ u : ℕ, (u : ℕ∞) < nv ∧ domB a = TBv (u : ℕ∞) ∧ (∀ z ∈ Wf u, operB a z ∈ X))

/-- Isabelle: `bwl_Aset` (pss_scratch.thy:8701)。 -/
def bwl_Aset (Wf : ℕ → Set BT) (nv : ℕ∞) (X : Set BT) : Set BT :=
  {a | bwl_Aop Wf nv X a}

/-- Isabelle: `bwl_Aop_mono_X` (pss_scratch.thy:8705)。 -/
theorem bwl_Aop_mono_X {Wf : ℕ → Set BT} {nv : ℕ∞} {X Y : Set BT} {a : BT}
    (h : bwl_Aop Wf nv X a) (hXY : X ⊆ Y) : bwl_Aop Wf nv Y a := by
  unfold bwl_Aop at h ⊢
  rcases h with h | ⟨hd, hop⟩ | ⟨u, hu, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hd, fun n => hXY (hop n)⟩)
  · exact Or.inr (Or.inr ⟨u, hu, hd, fun z hz => hXY (hop z hz)⟩)

/-- Isabelle: `bwl_Aset_mono` (pss_scratch.thy:8710)。 -/
theorem bwl_Aset_mono (Wf : ℕ → Set BT) (nv : ℕ∞) : Monotone (bwl_Aset Wf nv) := by
  intro X Y hXY a ha
  exact bwl_Aop_mono_X (Wf := Wf) (nv := nv) ha hXY

/-- [Buc1] は 2.5(1) の証明で `A_u(X) ⊆ A_ν(X)` (`u ≤ ν`) を使う。
    Isabelle: `bwl_Aop_mono_nv` (pss_scratch.thy:8719)。 -/
theorem bwl_Aop_mono_nv {Wf : ℕ → Set BT} {nv nv' : ℕ∞} {X : Set BT} {a : BT}
    (le : nv ≤ nv') (h : bwl_Aop Wf nv X a) : bwl_Aop Wf nv' X a := by
  unfold bwl_Aop at h ⊢
  rcases h with h | h | ⟨u, hu, hd, hop⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨u, lt_of_lt_of_le hu le, hd, hop⟩)

/-- `A_ν` は族パラメータの `u < ν` の段しか読まない。
    Isabelle: `bwl_Aop_cong` (pss_scratch.thy:8726)。 -/
theorem bwl_Aop_cong {Wf Wg : ℕ → Set BT} {nv : ℕ∞} {X : Set BT} {a : BT}
    (W : ∀ u : ℕ, (u : ℕ∞) < nv → Wf u = Wg u) :
    bwl_Aop Wf nv X a ↔ bwl_Aop Wg nv X a := by
  unfold bwl_Aop
  constructor
  · rintro (h | h | ⟨u, hu, hd, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨u, hu, hd, fun z hz => hop z ((W u hu) ▸ hz)⟩)
  · rintro (h | h | ⟨u, hu, hd, hop⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨u, hu, hd, fun z hz => hop z ((W u hu).symm ▸ hz)⟩)

/-! ## (2) 反復帰納的定義 `W_v = lfp A_v` -/

/-- `bwl_Wf n` は `n` 未満の段の族（`n` 以上の段はゴミ `∅`）。
    Isabelle: `bwl_Wf` (pss_scratch.thy:8746)。 -/
def bwl_Wf : ℕ → ℕ → Set BT
  | 0 => fun _ => ∅
  | v + 1 => fun u =>
      if u = v then lfpS_w3 (bwl_Aset (bwl_Wf v) (v : ℕ∞)) else bwl_Wf v u

/-- Isabelle: `bwl_W` (pss_scratch.thy:8750)。 -/
def bwl_W (u : ℕ) : Set BT := bwl_Wf (u + 1) u

/-- Isabelle: `bwl_Wf_coh` (pss_scratch.thy:8753)。 -/
theorem bwl_Wf_coh {u n : ℕ} (h : u < n) : bwl_Wf n u = bwl_Wf (u + 1) u := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero u)
  | succ v ih =>
      by_cases huv : u = v
      · subst huv; rfl
      · have ulv : u < v := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h) huv
        show (if u = v then _ else bwl_Wf v u) = _
        rw [if_neg huv]
        exact ih ulv

/-- Isabelle: `bwl_Wf_eq_W` (pss_scratch.thy:8769)。 -/
theorem bwl_Wf_eq_W {u n : ℕ} (h : u < n) : bwl_Wf n u = bwl_W u := bwl_Wf_coh h

/-- 定義方程式: `W_v` は族 `W` そのものに対する `A_v` の最小不動点
    （段の切り詰めは `A_v` が `u < v` しか読まないので不可視）。
    Isabelle: `bwl_W_unfold` (pss_scratch.thy:8775)。 -/
theorem bwl_W_unfold (v : ℕ) : bwl_W v = lfpS_w3 (bwl_Aset bwl_W (v : ℕ∞)) := by
  have stage : bwl_W v = lfpS_w3 (bwl_Aset (bwl_Wf v) (v : ℕ∞)) := by
    show bwl_Wf (v + 1) v = _
    show (if v = v then _ else bwl_Wf v v) = _
    rw [if_pos rfl]
  have cong : ∀ u : ℕ, (u : ℕ∞) < (v : ℕ∞) → bwl_Wf v u = bwl_W u := by
    intro u hu
    exact bwl_Wf_eq_W (by exact_mod_cast hu)
  have ptw : ∀ X : Set BT, bwl_Aset (bwl_Wf v) (v : ℕ∞) X = bwl_Aset bwl_W (v : ℕ∞) X := by
    intro X
    ext a
    exact bwl_Aop_cong (Wf := bwl_Wf v) (Wg := bwl_W) (nv := (v : ℕ∞)) (X := X) cong
  rw [stage, funext ptw]

/-- **(A1)** [Buc1] p.138: `A_v(W_v) = W_v` — 不動点方程式。
    Isabelle: `bwl_A1` (pss_scratch.thy:8800)。 -/
theorem bwl_A1 (v : ℕ) : bwl_Aset bwl_W (v : ℕ∞) (bwl_W v) = bwl_W v := by
  rw [bwl_W_unfold v]
  exact lfpS_unfold_w3 (bwl_Aset_mono bwl_W (v : ℕ∞))

/-- **(A2)** [Buc1] p.138: `A_v(Y) ⊆ Y ⟹ W_v ⊆ Y` — 帰納法規則。
    Isabelle: `bwl_A2` (pss_scratch.thy:8807)。 -/
theorem bwl_A2 {v : ℕ} {Y : Set BT} (A : bwl_Aset bwl_W (v : ℕ∞) Y ⊆ Y) :
    bwl_W v ⊆ Y := by
  rw [bwl_W_unfold v]
  exact lfpS_lowerbound_w3 A

/-- Isabelle: `bwl_A1_intro` (pss_scratch.thy:8818)。 -/
theorem bwl_A1_intro {v : ℕ} {a : BT} (h : bwl_Aop bwl_W (v : ℕ∞) (bwl_W v) a) :
    a ∈ bwl_W v := by
  have : a ∈ bwl_Aset bwl_W (v : ℕ∞) (bwl_W v) := h
  rwa [bwl_A1 v] at this

/-- Isabelle: `bwl_A1_dest` (pss_scratch.thy:8826)。 -/
theorem bwl_A1_dest {v : ℕ} {a : BT} (h : a ∈ bwl_W v) :
    bwl_Aop bwl_W (v : ℕ∞) (bwl_W v) a := by
  have : a ∈ bwl_Aset bwl_W (v : ℕ∞) (bwl_W v) := by rw [bwl_A1 v]; exact h
  exact this

/-- Isabelle: `bwl_A2'` (pss_scratch.thy:8835)。 -/
theorem bwl_A2' {v : ℕ} {Y : Set BT}
    (hY : ∀ c : BT, bwl_Aop bwl_W (v : ℕ∞) Y c → c ∈ Y) : bwl_W v ⊆ Y :=
  bwl_A2 (fun x hx => hY x hx)

/-- (W1): `0 ∈ W_v`。Isabelle: `bwl_W_zero` (pss_scratch.thy:8846)。 -/
theorem bwl_W_zero (v : ℕ) : BZero ∈ bwl_W v :=
  bwl_A1_intro (Or.inl rfl)

/-! ## 名前付き仮定（green-modulo。foundation 2/2 = [Buc1] §2 本体の担当）

以下の 2 命題は [Buc1] §2 の本体であり、Isabelle では証明済み。本ファイルはこれらを
仮定として受け取る（`bwl_W` は本ファイルの定義なので、命題は本ファイルで述べられる）。 -/

/-- [Buc1] 2.8 の系。Isabelle: `bwl_2_8_principal` (pss_scratch.thy:9733)
    `dfree_BT t ⟹ Trm [DB (enat u) t] ∈ bwl_W u`。 -/
def Bwl28Principal : Prop :=
  ∀ (u : ℕ) (t : BT), dfree_BT t = true → Dprin (u : ℕ∞) t ∈ bwl_W u

/-- [Buc1] 2.4(b)。Isabelle: `bwl_2_4b_add` (pss_scratch.thy:8965)
    `a ∈ bwl_W v ⟹ b ∈ bwl_W v ⟹ a +⇩B b ∈ bwl_W v`。 -/
def Bwl24bAdd : Prop :=
  ∀ (v : ℕ) (a b : BT), a ∈ bwl_W v → b ∈ bwl_W v → addBT a b ∈ bwl_W v

/-! ## (1) `W` は水準について単調、`D_ω`-free な `T_m`-項は `W_m` にいる -/

/-- [Buc1] p.137 命題: `u ≤ v ⟹ W_u ⊆ W_v`。
    Isabelle: `y3_W_mono` (pss_scratch.thy:11280)。 -/
theorem y3_W_mono {u v : ℕ} (uv : u ≤ v) : bwl_W u ⊆ bwl_W v := by
  refine bwl_A2' (fun c A => ?_)
  have le : (u : ℕ∞) ≤ (v : ℕ∞) := by exact_mod_cast uv
  exact bwl_A1_intro (bwl_Aop_mono_nv le A)

private theorem dfree_BPList_forall_w3 :
    ∀ {ps : List BP}, dfree_BPList ps = true → ∀ p ∈ ps, dfree_BP p = true
  | [], _ => by simp
  | q :: qs, h => by
      simp only [dfree_BPList, Bool.and_eq_true] at h
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact h.1
      · exact dfree_BPList_forall_w3 h.2 p hp'

/-- 鍵となる閉包性: `D_ω`-free で最上位の principal 指標がすべて `≤ m` の項は `W_m`
    にいる。各 principal は `bwl_2_8_principal` で自身の指標の `W` に入り、`y3_W_mono`
    で `W_m` に持ち上がり、加法閉包 `bwl_2_4b_add` で組み立てる。
    Isabelle: `y3_TBv_dfree_W_aux` (pss_scratch.thy:11295)。 -/
theorem y3_TBv_dfree_W_aux (Hprin : Bwl28Principal) (Hadd : Bwl24bAdd) (m : ℕ) :
    ∀ ps : List BP, (∀ p ∈ ps, dfree_BP p = true) →
      (∀ p ∈ ps, (match p with | .db w _ => w ≤ (m : ℕ∞))) →
      BT.trm ps ∈ bwl_W m := by
  intro ps
  induction ps with
  | nil => intro _ _; exact bwl_W_zero m
  | cons p ps ih =>
      intro df bd
      obtain ⟨w, b⟩ := p
      have dfp : dfree_BP (BP.db w b) = true := df _ List.mem_cons_self
      have dfp' : w ≠ ⊤ ∧ dfree_BT b = true := by
        simpa [dfree_BP, Bool.and_eq_true, bne_iff_ne] using dfp
      obtain ⟨wne, dfb⟩ := dfp'
      lift w to ℕ using wne with k
      have kle : (k : ℕ∞) ≤ (m : ℕ∞) := bd _ List.mem_cons_self
      have km : k ≤ m := by exact_mod_cast kle
      have pW : Dprin (k : ℕ∞) b ∈ bwl_W k := Hprin k b dfb
      have pWm : BT.trm [BP.db (k : ℕ∞) b] ∈ bwl_W m := y3_W_mono km pW
      have d1 : ∀ q ∈ ps, dfree_BP q = true := fun q hq => df q (List.mem_cons_of_mem _ hq)
      have d2 : ∀ q ∈ ps, (match q with | .db w' _ => w' ≤ (m : ℕ∞)) :=
        fun q hq => bd q (List.mem_cons_of_mem _ hq)
      have rest : BT.trm ps ∈ bwl_W m := ih d1 d2
      have := Hadd m _ _ pWm rest
      simpa [addBT] using this

/-- Isabelle: `y3_TBv_dfree_W` (pss_scratch.thy:11320)。 -/
theorem y3_TBv_dfree_W (Hprin : Bwl28Principal) (Hadd : Bwl24bAdd) {z : BT} {m : ℕ}
    (df : dfree_BT z = true) (tb : z ∈ TBv (m : ℕ∞)) : z ∈ bwl_W m := by
  obtain ⟨ps⟩ := z
  have d1 : ∀ p ∈ ps, dfree_BP p = true :=
    dfree_BPList_forall_w3 (by simpa [dfree_BT] using df)
  have d2 : ∀ p ∈ ps, (match p with | .db w _ => w ≤ (m : ℕ∞)) := by
    have h : ps.all (fun p => match p with | .db u _ => decide (u ≤ (m : ℕ∞))) = true := by
      simpa [TBv] using tb
    intro p hp
    have := (List.all_eq_true.mp h) p hp
    obtain ⟨w, b⟩ := p
    simpa using this
  exact y3_TBv_dfree_W_aux Hprin Hadd m ps d1 d2

/-- `D_ω`-free な項は有限水準を持つ、したがって**どれかの** `W_m` にいる。
    Isabelle: `y3_dfree_ex_lev_aux` (pss_scratch.thy:11333)。 -/
theorem y3_dfree_ex_lev_aux :
    ∀ ps : List BP, (∀ p ∈ ps, dfree_BP p = true) →
      ∃ m : ℕ, ∀ p ∈ ps, (match p with | .db w _ => w ≤ (m : ℕ∞)) := by
  intro ps
  induction ps with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons p ps ih =>
      intro df
      obtain ⟨w, b⟩ := p
      have dfp : dfree_BP (BP.db w b) = true := df _ List.mem_cons_self
      have wne : w ≠ ⊤ :=
        (by simpa [dfree_BP, Bool.and_eq_true, bne_iff_ne] using dfp :
          w ≠ ⊤ ∧ dfree_BT b = true).1
      lift w to ℕ using wne with k
      have d1 : ∀ q ∈ ps, dfree_BP q = true := fun q hq => df q (List.mem_cons_of_mem _ hq)
      obtain ⟨m, hm⟩ := ih d1
      refine ⟨max k m, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · show (k : ℕ∞) ≤ ((max k m : ℕ) : ℕ∞)
        exact_mod_cast Nat.le_max_left k m
      · have hq2 := hm q hq'
        obtain ⟨w', b'⟩ := q
        show w' ≤ ((max k m : ℕ) : ℕ∞)
        refine le_trans hq2 ?_
        exact_mod_cast Nat.le_max_right k m

/-- Isabelle: `y3_dfree_ex_lev` (pss_scratch.thy:11370)。 -/
theorem y3_dfree_ex_lev {z : BT} (df : dfree_BT z = true) : ∃ m : ℕ, z ∈ TBv (m : ℕ∞) := by
  obtain ⟨ps⟩ := z
  have d1 : ∀ p ∈ ps, dfree_BP p = true :=
    dfree_BPList_forall_w3 (by simpa [dfree_BT] using df)
  obtain ⟨m, hm⟩ := y3_dfree_ex_lev_aux ps d1
  refine ⟨m, ?_⟩
  show (List.all ps fun p => match p with | .db u _ => decide (u ≤ (m : ℕ∞))) = true
  refine List.all_eq_true.mpr (fun p hp => ?_)
  have := hm p hp
  obtain ⟨w, b⟩ := p
  simpa using this

/-- Isabelle: `y3_dfree_W_ex` (pss_scratch.thy:11382)。 -/
theorem y3_dfree_W_ex (Hprin : Bwl28Principal) (Hadd : Bwl24bAdd) {z : BT}
    (df : dfree_BT z = true) : ∃ m : ℕ, z ∈ bwl_W m := by
  obtain ⟨m, hm⟩ := y3_dfree_ex_lev df
  exact ⟨m, y3_TBv_dfree_W Hprin Hadd df hm⟩

/-- `Trans` の像は `D_ω`-free（`m_7_3_Trans_in_T_B` により `T_B` に属する）。
    Isabelle: `y3_Trans_dfree` (pss_scratch.thy:11390)。 -/
theorem y3_Trans_dfree {M : PS} (MR : RTPS M) : dfree_BT (Trans M) = true :=
  Trans_mem_T_B M MR

/-- Isabelle: `y3_Trans_W` (pss_scratch.thy:11395)。 -/
theorem y3_Trans_W (Hprin : Bwl28Principal) (Hadd : Bwl24bAdd) {M : PS} (MR : RTPS M) :
    ∃ m : ℕ, Trans M ∈ bwl_W m :=
  y3_dfree_W_ex Hprin Hadd (y3_Trans_dfree MR)

/-! ## (2) 三種類の `dom` 形は互いに相異なる -/

/-- Isabelle: `y3_one_in_TBv` (pss_scratch.thy:11403)。 -/
theorem y3_one_in_TBv (m : ℕ) :
    BT.trm [BP.db 0 (BT.trm [BP.db 0 (BT.trm [])])] ∈ TBv (m : ℕ∞) := by
  simp [TBv]

/-- Isabelle: `y3_D0one_not_NatSet` (pss_scratch.thy:11406)。 -/
theorem y3_D0one_not_NatSet :
    BT.trm [BP.db 0 (BT.trm [BP.db 0 (BT.trm [])])] ∉ NatSet := by
  rintro ⟨n, hn⟩
  have l : List.replicate n (BP.db 0 BZero) = [BP.db 0 (BT.trm [BP.db 0 (BT.trm [])])] := by
    simpa [numBT] using hn
  cases n with
  | zero => simp at l
  | succ k => simp [List.replicate_succ, BZero] at l

/-- Isabelle: `y3_TBv_ne_zeroset` (pss_scratch.thy:11416)。 -/
theorem y3_TBv_ne_zeroset (m : ℕ) : TBv (m : ℕ∞) ≠ ({BZero} : Set BT) := by
  intro e
  have h1 := y3_one_in_TBv m
  rw [e] at h1
  simp [BZero] at h1

/-- Isabelle: `y3_TBv_ne_NatSet` (pss_scratch.thy:11424)。 -/
theorem y3_TBv_ne_NatSet (m : ℕ) : TBv (m : ℕ∞) ≠ NatSet := by
  intro e
  have h1 := y3_one_in_TBv m
  rw [e] at h1
  exact y3_D0one_not_NatSet h1

/-- Isabelle: `y3_TBv_inj` (pss_scratch.thy:11432)。 -/
theorem y3_TBv_inj {m m' : ℕ} (e : TBv (m : ℕ∞) = TBv (m' : ℕ∞)) : m = m' := by
  have le : ∀ i j : ℕ, TBv (i : ℕ∞) = TBv (j : ℕ∞) → i ≤ j := by
    intro i j ij
    have h : BT.trm [BP.db (i : ℕ∞) (BT.trm [])] ∈ TBv (i : ℕ∞) := by simp [TBv]
    rw [ij] at h
    have hij : (i : ℕ∞) ≤ (j : ℕ∞) := by simpa [TBv] using h
    exact_mod_cast hij
  exact Nat.le_antisymm (le m m' e) (le m' m e.symm)

#print axioms bwl_Aop_mono_X
#print axioms bwl_Aset_mono
#print axioms bwl_Aop_mono_nv
#print axioms bwl_Aop_cong
#print axioms bwl_Wf_coh
#print axioms bwl_Wf_eq_W
#print axioms bwl_W_unfold
#print axioms bwl_A1
#print axioms bwl_A2
#print axioms bwl_A1_intro
#print axioms bwl_A1_dest
#print axioms bwl_A2'
#print axioms bwl_W_zero
#print axioms y3_W_mono
#print axioms y3_TBv_dfree_W_aux
#print axioms y3_TBv_dfree_W
#print axioms y3_dfree_ex_lev_aux
#print axioms y3_dfree_ex_lev
#print axioms y3_dfree_W_ex
#print axioms y3_Trans_dfree
#print axioms y3_Trans_W
#print axioms y3_one_in_TBv
#print axioms y3_D0one_not_NatSet
#print axioms y3_TBv_ne_zeroset
#print axioms y3_TBv_ne_NatSet
#print axioms y3_TBv_inj

end PSS
