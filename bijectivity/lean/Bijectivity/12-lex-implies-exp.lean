import Bijectivity.«12c-big-step»

/-!
# 命題（基本列的順序が辞書式的順序を含意すること）

原文: 任意の \(M,N\in CT_{\textrm{PS}}\) に対して、\(M<_{\textrm{PS}}N\) ならば
\(M<_{\textrm{PS}[]}N\) である。

原文の証明（構成）:

> \(\textrm{Lng}(M)\) に関する帰納法。
> \(j_1^M=0\) なら \(M=((0,0))=(N_j)_{j=0}^0\) で 標準形の始切片への経路 より従う。
> \(f=\min(\{\min(j_1^M,j_1^N)+1\}\cup\{j\mid j\leq\min(j_1^M,j_1^N)\land M_j\neq N_j\})\)
> で場合分けする。
> \(f=j_1^M+1\) なら \(M=(N_j)_{j=0}^{j_1^M}\) で 標準形の始切片への経路 より従う。
> \(f\leq j_1^M\) のときは \(f=j_1^N\) の場合に、\(\textrm{Lng}(M')=\textrm{Lng}(N)\) かつ
> \((M'_j)_{j=0}^{j_1^N-1}=(N_j)_{j=0}^{j_1^N-1}\) なる \(M'\in CT_{\textrm{PS}}\) が
> 高々 \((j_1^N)^2\) 個であることを使い、内側の帰納を回す。
> 一般の \(f\leq j_1^N\) は \(N\) を \((N_j)_{j=0}^f\) に置き換えて帰着する。□

形式化は原文の構成をそのまま辿る。

* \(f\) による場合分け … `12a-lex-toolkit.lean` の `ltPS_dest_idx`
* 有限性 … `12b-ctps-finite.lean` の `ctps_finite`（原文の「高々 \((j_1^N)^2\) 個」）
* \(f=j_1^N\) の場合の主要部 … `12c-big-step.lean` の `big_step`
* 「\(N\) を \((N_j)_{j=0}^f\) に置き換える」帰着 … 本ファイルの `reduce_to_bounded`
* 内側の帰納 … 本ファイルの `ltPS_ltExpPS_bounded`

## 原文との差異（訂正候補ではなく、証明の穴の補い）

原文の内側の帰納は「\(\textrm{Lng}(N)\) と \((N_j)_{j=0}^{j_1^N-1}\) を固定した集合」
の上での下降帰納だが、その集合の \(<_{\textrm{PS}}\)-最大元における基底段階が原文では
扱われていない（最大元では帰納法の仮定が使えないのに、結論は自明ではない）。
ここでは代わりに「長さ \(L\) 以下の \(CT_{\textrm{PS}}\) の元全体」の上で下降帰納する。
この集合で取ると、最大元では相手 \(N\) が存在しないので主張が空虚に成り立ち、
基底段階が自動的に閉じる。有限性の根拠は原文と同じ係数評価
\(M'_{1,j}\leq M'_{0,j}\leq j\) である。
-/

namespace Bijectivity

open PSS

/-! ## 小道具 -/

/-- \(\leq_{\textrm{PS}[]}\) を右から合成しても狭義は保たれる。 -/
theorem ltExpPS_leExpPS_trans {X Y Z : PS} (h1 : X <ₚ[] Y) (h2 : Y ≤ₚ[] Z) : X <ₚ[] Z := by
  obtain ⟨a, hane, ha, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := h2
  refine ⟨b ++ a, ?_, ?_, ?_⟩
  · exact List.append_ne_nil_of_right_ne_nil b hane
  · intro n hn
    rcases List.mem_append.mp hn with h | h
    · exact hb n h
    · exact ha n h
  · exact (expand_append Z b a).symm ▸ rfl

/-- 始切片は再び \(CT_{\textrm{PS}}\) の元（[1] の標準形の始切片への遺伝性）。 -/
theorem ctps_take {N : PS} (hN : CTPS N) {f : ℕ} (hf : f < Lng N) :
    CTPS (N.take (f + 1)) := by
  have hst : STPS (seg N 0 f) :=
    STPS_prefix N f hN.1 (by simp only [Lng] at hf ⊢; omega)
  rw [seg_zero_eq_take N (by simp only [Lng] at hf ⊢; omega)] at hst
  refine ⟨hst, ?_⟩
  cases N with
  | nil => simp only [Lng, List.length_nil] at hf; omega
  | cons p Q => simpa using hN.2

/-- 標準形の始切片への経路 の `take` 形。 -/
theorem take_leExpPS_of_lt {N : PS} (hN : CTPS N) {f : ℕ} (hf : f < Lng N) :
    N.take (f + 1) ≤ₚ[] N := by
  have h := seg_leExpPS (STPS_TPS N hN.1) (j1' := f)
    (by simp only [Lng] at hf ⊢; omega)
  rwa [seg_zero_eq_take N (by simp only [Lng] at hf ⊢; omega)] at h

/-- 原文の「\(f=j_1^M+1\)」の場合: \(M\) が \(N\) の真の始切片。 -/
theorem ltExpPS_of_take {X N : PS} (hX : CTPS X) (hN : CTPS N)
    (hlen : Lng X < Lng N) (hpre : X = N.take (Lng X)) : X <ₚ[] N := by
  have hpos : 0 < Lng X := List.length_pos_of_ne_nil (STPS_TPS X hX.1)
  have hf : Lng X - 1 < Lng N := by simp only [Lng] at hlen hpos ⊢; omega
  have hseg : N.take (Lng X - 1 + 1) = X := by
    have : Lng X - 1 + 1 = Lng X := by simp only [Lng] at hpos ⊢; omega
    rw [this, ← hpre]
  have hle := take_leExpPS_of_lt hN hf
  rw [hseg] at hle
  obtain ⟨a, ha, hXa⟩ := hle
  refine ⟨a, ?_, ha, hXa⟩
  rintro rfl
  simp only [expand] at hXa
  subst hXa
  exact Nat.lt_irrefl _ hlen

/-! ## 原文の「\(N\) を \((N_j)_{j=0}^f\) に置き換える」帰着 -/

/-- 相手の長さが \(\textrm{Lng}(X)\) 以下の場合だけ分かっていれば、一般の相手にも従う。 -/
theorem reduce_to_bounded {X : PS} (hX : CTPS X)
    (hb : ∀ N : PS, CTPS N → Lng N ≤ Lng X → X <ₚ N → X <ₚ[] N) :
    ∀ N : PS, CTPS N → X <ₚ N → X <ₚ[] N := by
  intro N hN hlt
  rcases ltPS_dest_idx hlt with ⟨hlen, hpre⟩ | ⟨f, hfX, hfN, hfpre, hflt⟩
  · exact ltExpPS_of_take hX hN hlen hpre
  · have hN2ct : CTPS (N.take (f + 1)) := ctps_take hN hfN
    have hN2len : Lng (N.take (f + 1)) = f + 1 := by
      simp only [Lng, List.length_take] at hfN ⊢
      omega
    have hpre2 : X.take f = (N.take (f + 1)).take f := by
      rw [List.take_take]
      have hmin : min f (f + 1) = f := by omega
      rw [hmin]
      exact hfpre
    have hXN2 : X <ₚ N.take (f + 1) := by
      refine ltPS_of_agree hfX (by omega) hpre2 ?_
      rw [pairAt_take N (Nat.lt_succ_self f)]
      exact hflt
    have hstep : X <ₚ[] N.take (f + 1) := by
      refine hb _ hN2ct ?_ hXN2
      simp only [Lng] at hN2len hfX ⊢
      omega
    exact ltExpPS_leExpPS_trans hstep (take_leExpPS_of_lt hN hfN)

/-! ## 内側の帰納（長さ `L` 以下の `CT_PS` 上の下降帰納） -/

theorem ltPS_ltExpPS_bounded (L : ℕ) (X : PS) : CTPS X → Lng X ≤ L →
    ∀ N : PS, CTPS N → Lng N ≤ L → X <ₚ N → X <ₚ[] N := by
  refine (ctps_wf L).induction (C := fun X => CTPS X → Lng X ≤ L →
    ∀ N : PS, CTPS N → Lng N ≤ L → X <ₚ N → X <ₚ[] N) X ?_
  clear X
  intro X ih hX hXL N hN hNL hlt
  rcases ltPS_dest_idx hlt with ⟨hlen, hpre⟩ | ⟨f, hfX, hfN, hfpre, hflt⟩
  · -- 原文「\(f=j_1^M+1\)」: 標準形の始切片への経路 で終わり
    exact ltExpPS_of_take hX hN hlen hpre
  · -- 原文「\(N\) を \((N_j)_{j=0}^f\) に置き換える」
    have hN2ct : CTPS (N.take (f + 1)) := ctps_take hN hfN
    have hN2len : Lng (N.take (f + 1)) = f + 1 := by
      simp only [Lng, List.length_take] at hfN ⊢
      omega
    have hpre2 : X.take f = (N.take (f + 1)).take f := by
      rw [List.take_take]
      have hmin : min f (f + 1) = f := by omega
      rw [hmin]
      exact hfpre
    have hXN2 : X <ₚ N.take (f + 1) := by
      refine ltPS_of_agree hfX (by omega) hpre2 ?_
      rw [pairAt_take N (Nat.lt_succ_self f)]
      exact hflt
    have hN2X : Lng (N.take (f + 1)) ≤ Lng X := by
      simp only [Lng] at hN2len hfX ⊢
      omega
    -- 帰納法の仮定は \(X\) より上の元に対して使える
    have hPhi : ∀ N3 : PS, CTPS N3 → N.take (f + 1) <ₚ N3 → N.take (f + 1) <ₚ[] N3 := by
      refine reduce_to_bounded hN2ct ?_
      intro N3 hN3 hN3len hlt3
      refine ih (N.take (f + 1))
        ⟨hXN2, ⟨hN2ct, by simp only [Lng] at hN2X hXL ⊢; omega⟩, ⟨hX, hXL⟩⟩
        hN2ct (by simp only [Lng] at hN2X hXL ⊢; omega) N3 hN3 ?_ hlt3
      simp only [Lng] at hN3len hN2X hXL ⊢
      omega
    -- 原文の \(f=j_1^N\) の場合の主要部
    have hagree : X.take (Lng (N.take (f + 1)) - 1)
        = (N.take (f + 1)).take (Lng (N.take (f + 1)) - 1) := by
      rw [hN2len, Nat.add_sub_cancel]
      exact hpre2
    have hbig : X <ₚ[] N.take (f + 1) :=
      big_step hX hN2ct hXN2 hN2X hagree hPhi
    exact ltExpPS_leExpPS_trans hbig (take_leExpPS_of_lt hN hfN)

/-- 原文の命題（基本列的順序が辞書式的順序を含意すること）。 -/
theorem ltPS_ltExpPS {M N : PS} (hM : CTPS M) (hN : CTPS N) (h : M <ₚ N) : M <ₚ[] N := by
  refine reduce_to_bounded hM ?_ N hN h
  intro N' hN' hlen hlt'
  exact ltPS_ltExpPS_bounded (Lng M) M hM (le_refl _) N' hN' hlen hlt'

end Bijectivity
