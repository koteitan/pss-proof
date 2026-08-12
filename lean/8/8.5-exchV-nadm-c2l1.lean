import «8».«8.5-exchV-nadm-atomics»

/-!
# §8.5 ExchV 非許容枝 `c₂(L₁)` の値（`NadmC2L1`）

## 目的

`8.5-exchV-nadm-atomics` の残差 `NadmC2L1`（Isabelle `atx_c2L1`）を
`transC2Core` の直接評価で閉じる。`NadmC2L1` は non-admissible 条件(V) ホスト `M`
について

    transC2 (s84x_L M 1)
      = D_{M₁,ⱼ₋₁}(t₂ +_B D_{M₁,ⱼ₀}(t₂ +_B D_{M₁,ⱼ₀} 0))   (t₂ = transT2 M)

を主張する。

## 原文 / Isabelle 対応

- Isabelle blueprint（`isabelle/layerB/pss_wip.thy`）:
  * `atx_c2L1`(86248) = `dax_c2L1_of_notLD`(71081) ＋ `atx_notLD`(86198)。
  * `dax_c2L1_of_notLD` は `transC2 (s84x_L M 1)` を `s84d_c2hole ?L (·)`(58420)
    で表し、`L₁` が条件(II)/(IV) レジーム（`m_8_4_oper_props_4`(53257)）である
    ことと `notLD`（`atx_notLD` = 前線 `t₂` の末尾 principal 頭が `M₁,ⱼ₀` でない）
    から `else`枝を評価し、`t₂ = 0`/`t₂ ≠ 0` の両場合を同一 3 段 `D` 形へ潰す。
  * Lean では `s84d_c2hole` に相当する engine が **既に定義**の `transC2Core`
    （`PSS/Trans.lean`:139）そのものなので、別途 `s84d_c2hole` を移植せず
    `transC2 (s84x_L M 1) = transC2Core (s84x_L M 1) (transV (s84x_L M 1))
    (transT2 (s84x_L M 1))` を直接評価する。

## 構造（house green-modulo）

`NadmC2L1` を次の 3 段で **単一の深い残差** `NadmC2L1NotLD`（Isabelle `atx_notLD`）
へ縮約する:

1. `nadmC2L1_of_support` — `dax_c2L1_of_notLD` の **値の組み立て**（`transC2Core` の
   `else`枝評価と `t₂ = 0` / `t₂ ≠ 0` の 2 場合の潰し）を無条件に完全証明。入力は
   `s84x_L M 1` の構造束 `NadmC2L1Support`（7 場）。`shape(1)`（`c1_shape_holds`）と
   `jm2eq`（`condV_bridge_hp_jm2`）を使用。
2. `l1_geom_cl` / `l1_congr_cl` — `NadmC2L1Support` のうち **構造 6 場**（`s84d_L1_data`
   の `Lng`/`Pred`/`transJ0`/`transJm1`/`transV`/`transT2` 合同群、entry 合同、
   および (II)/(IV) レジーム＝`m_8_4_oper_props_4(2)` 相当の I/III/V/VI 全偽）を
   **無条件に完全証明**。`8.5-exchV-values-close` の `exchV_L1_structure_adm` の
   幾何導出を非許容枝向けに再導出し、`Adm` 合同（`find?_congr_cl`）で `transJm1` へ、
   `Pred` 合同と合わせて `transV`/`transT2` へ持ち上げる。条件(V) では
   `s84x_jm2 M = j₀` なので `e1_jm2_le_j0` は不要、レジームは entry 合同のみで閉じる。
3. `nadmC2L1_of_notLD` — 1 と 2 を合成。残るは第7場 `notLD` のみ。

よって `NadmC2L1` は **`NadmC2L1NotLD` ただ 1 本**へ縮約された。`atx_notLD` は
Red 切片の強単項性（`atx_condV_nadm_t2_components`(86068) 経由。Lean では
`m_8_5_Joints_FirstNodes_basic_condV` 未移植、`subexpr_component_strongmono` は
witness/factAB gated）に依存する深い leaf なので本ファイルでは据え置く。

## 依存（すべて committed 緑, main 19dc5fd）

«8».«8.5-exchV-nadm-atomics»（`NadmC2L1`/`condV_setup_holds`/`c1_shape_holds`/
`condV_bridge_hp_jm2`/`s84x_L`/`s84x_jm2`/`s84c1_jm2_basic`/`s84x_L_eq_append`/
`RTPS_s84x_L`/`nextrel0_row0_congr`/`nextR_prefix_agree_68`/`pred_is_oper1`/
`ancestor_basic_1`/`mono_hasParent_row0`/`STPS_RTPS`/`STPS_TPS` を推移的に供給）,
`PSS/Trans.lean`（`transC2`/`transC2Core`/`transV`/`transT2`/`transJ0`/`transJm1`/
`lastIdx`/`lastParent`/`bpHeadV`/`transCondI…VI`）, `PSS/Adm.lean`（`adm`/`Adm`）,
`Buchholz-1986/ および Buchholz-rel-ord/`（`addBT`/`BZero`/`Dprin`/`PB`）.

## 状態

GREEN-MODULO（sorry 0, axioms = [propext, Classical.choice, Quot.sound]）。
`NadmC2L1` を **単一残差 `NadmC2L1NotLD`**（Isabelle `atx_notLD`）へ縮約。
構造合同・レジーム・値組み立ては無条件。

## private 接尾辞: `_cl`
-/

namespace PSS

/-- `addBT 0_B X = X`（`addBT`/`BZero` の定義計算）。 -/
private theorem addBT_zero_left_cl (X : BT) : addBT BZero X = X := by
  rcases X with ⟨bs⟩; simp [addBT, BZero]

/-- `s84x_L M 1` の構造的事実の束（Isabelle `s84d_L1_data` の合同群 ＋
`m_8_4_oper_props_4` のレジーム ＋ `atx_notLD` の `notLD`）。`NadmC2L1` を
`transC2Core` の値組み立てから閉じるために必要な入力のみ。すべて Lean 未移植。 -/
def NadmC2L1Support : Prop :=
  ∀ M : PS, STPS M → monoT M = true → transCondV M = true →
    adm M (transJ0 M) = false →
    -- `m_8_4_oper_props_4(2)`: `L₁` は (II)/(IV) レジーム（(I)/(III)/(V)/(VI) でない）
    (transCondI (s84x_L M 1) || transCondIII (s84x_L M 1)
        || transCondV (s84x_L M 1)) = false
    ∧ transCondVI (s84x_L M 1) = false
    -- `s84d_L1_data(8)`: `transV (L₁) = transV M`
    ∧ transV (s84x_L M 1) = transV M
    -- `s84d_L1_data(9)`: `transT2 (L₁) = transT2 M`
    ∧ transT2 (s84x_L M 1) = transT2 M
    -- `s84d_L1_data(5)` ＋ `s84c1_L1_entry1_lt`: 行1 `j₀` 列は不変
    ∧ entry (s84x_L M 1) 1 (lastParent (s84x_L M 1)) = entry M 1 (transJ0 M)
    -- `s84c1_L1_entry1_j1`: `L₁` の最終列（行1）は `M₁,ⱼ₋₂`
    ∧ entry (s84x_L M 1) 1 (lastIdx (s84x_L M 1)) = entry M 1 (s84x_jm2 M)
    -- `atx_notLD`: 前線 `t₂` の末尾 principal 頭は `M₁,ⱼ₀` でない
    ∧ (transT2 M ≠ BZero →
        (bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
          == (entry M 1 (transJ0 M) : ℕ∞)) = false)

/-- Isabelle `dax_c2L1_of_notLD`（pss_wip.thy:71081）の **値の組み立て**。
`s84x_L M 1` の構造事実 `NadmC2L1Support` の下で `transC2Core` の `else`枝を評価し、
`t₂ = 0`/`t₂ ≠ 0` の両場合を同一 3 段 `D` 形へ潰す。 -/
theorem nadmC2L1_of_support (hsupp : NadmC2L1Support) : NadmC2L1 := by
  intro M hST hmono hcond hnadm
  obtain ⟨hreg, hregVI, hVcong, hT2cong, hEj0, hEj1, hnotLD⟩ :=
    hsupp M hST hmono hcond hnadm
  have hR : RTPS M := STPS_RTPS M hST
  have hM : TPS M := STPS_TPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  obtain ⟨hVshape, _, _, _⟩ := c1_shape_holds M hR hM hmono hj1pos ht1ne
  have hjm2eq : s84x_jm2 M = transJ0 M := (condV_bridge_hp_jm2 M hM hmono hcond).2
  -- transV (L₁) = M₁,ⱼ₋₁
  have hVfull : transV (s84x_L M 1) = (entry M 1 (transJm1 M) : ℕ∞) := by
    rw [hVcong, hVshape]
  -- entry (L₁) 1 (lastIdx L₁) = M₁,ⱼ₀
  have hEj1' : entry (s84x_L M 1) 1 (lastIdx (s84x_L M 1)) = entry M 1 (transJ0 M) := by
    rw [hEj1, hjm2eq]
  -- transC2 (L₁) = transC2Core (L₁) (transV L₁) (transT2 L₁)  (定義)
  show transC2Core (s84x_L M 1) (transV (s84x_L M 1)) (transT2 (s84x_L M 1)) = _
  rw [hT2cong, hVfull]
  -- transC2Core を展開しレジームの if を潰す
  simp only [transC2Core, hreg, hregVI, if_false, Bool.false_eq_true, hEj0, hEj1']
  by_cases ht2 : transT2 M = BZero
  · -- t₂ = 0: 2 段 D 形。target 側の addBT 0 を消して一致
    rw [ht2]
    simp only [beq_self_eq_true, if_true, addBT_zero_left_cl]
  · -- t₂ ≠ 0: notLD で leftDj₀ = false、t₃ = t₄ = t₂
    have hbeq : (transT2 M == BZero) = false := by
      simp only [beq_eq_false_iff_ne]; exact ht2
    simp only [hbeq, hnotLD ht2, Bool.false_eq_true, if_false]

#print axioms nadmC2L1_of_support

/-! ## `L₁` 構造合同の移植（Isabelle `s84d_L1_data` の幾何部） -/

/-- `L₁ = s84x_L M 1` の幾何合同（`8.5-exchV-values-close` の `exchV_L1_structure_adm`
の adm 非依存部を非許容枝向けに再導出）。 -/
private theorem l1_geom_cl (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) :
    Lng (s84x_L M 1) = Lng M
    ∧ Pred (s84x_L M 1) = Pred M
    ∧ transJ0 (s84x_L M 1) = transJ0 M
    ∧ (∀ j, j < Lng M - 1 → (s84x_L M 1).getD j (0, 0) = M.getD j (0, 0))
    ∧ entry (s84x_L M 1) 1 (Lng M - 1) = entry M 1 (s84x_jm2 M)
    ∧ (∀ j, j < Lng M → entry (s84x_L M 1) 0 j = entry M 0 j) := by
  have hM : TPS M := STPS_TPS M hST
  have hR : RTPS M := STPS_RTPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  have hlen : 1 < Lng M := by simp only [transJ1, lastIdx] at hj1pos; omega
  have hp1 : hasParent M 1 (Lng M - 1) = true := (condV_bridge_hp_jm2 M hM hmono hcond).1
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp1).1
  have hlejm2 : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by
    simpa [leR] using (s84c1_jm2_basic M hp1).2.2
  have he0lt : entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) :=
    ancestor_basic_1 M (s84x_jm2 M) (Lng M - 1) (Lng M - 1) hM hjm2lt (le_refl _) hlejm2
  have hsum : entry M 0 (s84x_jm2 M)
        + (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)) = entry M 0 (Lng M - 1) := by omega
  have hL1form : s84x_L M 1
      = Pred M ++ [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))] := by
    rw [s84x_L_eq_append, ← pred_is_oper1 M hM hlen]
    simp [hsum]
  have hPredLen : Lng (Pred M) = Lng M - 1 := length_Pred M hlen
  have hLngL1 : Lng (s84x_L M 1) = Lng M := by
    rw [hL1form]
    simp only [List.length_append, List.length_cons, List.length_nil, hPredLen]
    omega
  have hPredL1 : Pred (s84x_L M 1) = Pred M := by
    rw [Pred_eq_take (s84x_L M 1) (by rw [hLngL1]; omega), hL1form]
    have htake : (Pred M ++ [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))]).take (Lng M - 1)
        = Pred M := by
      rw [← hPredLen]; exact List.take_left' rfl
    simpa [hLngL1] using htake
  have hpairPrefix : ∀ j, j < Lng M - 1 → (s84x_L M 1).getD j (0, 0) = M.getD j (0, 0) := by
    intro j hj
    have hjTake : j < (M.take (Lng M - 1)).length := by simp; omega
    rw [hL1form, Pred_eq_take M hlen]
    change ((M.take (Lng M - 1) ++
      [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))])[j]?).getD (0, 0) = (M[j]?).getD (0, 0)
    rw [List.getElem?_append_left hjTake, List.getElem?_take]
    simp [hj]
  have hentry1j1 : entry (s84x_L M 1) 1 (Lng M - 1) = entry M 1 (s84x_jm2 M) := by
    rw [hL1form, entry_append_right_mr (Pred M) _ 1 (Lng M - 1) (by rw [hPredLen]), hPredLen]
    simp [entry]
  have hentry0 : ∀ j, j < Lng M → entry (s84x_L M 1) 0 j = entry M 0 j := by
    intro j hj
    by_cases hjp : j < Lng M - 1
    · rw [hL1form, entry_append_left_mr (Pred M) _ 0 j (by rw [hPredLen]; exact hjp),
        Pred_eq_take M hlen, entry_take M (Lng M - 1) 0 j hjp]
    · have hjlast : j = Lng M - 1 := by omega
      subst j
      rw [hL1form, entry_append_right_mr (Pred M) _ 0 (Lng M - 1) (by rw [hPredLen]), hPredLen]
      simp [entry]
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnextM : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    have h := nextR_parent0_of_hasParent M (Lng M - 1) hp0
    simpa [transJ0, lastParent, lastIdx] using h
  have hnext0eq : ∀ a b, nextR (s84x_L M 1) 0 a b = nextR M 0 a b := by
    intro a b
    simp only [nextR]
    exact nextrel0_row0_congr M (s84x_L M 1) id hLngL1.symm strictMono_id
      (by intro j hj; simpa using hentry0 j hj) a b
  have hnextL : nextR (s84x_L M 1) 0 (transJ0 M) (Lng (s84x_L M 1) - 1) = true := by
    rw [hLngL1, hnext0eq]; exact hnextM
  obtain ⟨p, hp, huniq⟩ := (hasParent_iff_unique_fseq M 0 (Lng M - 1)).mp hp0
  have hpj0 : p = transJ0 M := (huniq (transJ0 M) hnextM).symm
  subst p
  have huniqL : ∀ y, nextR (s84x_L M 1) 0 y (Lng (s84x_L M 1) - 1) = true → y = transJ0 M := by
    intro y hy
    apply huniq
    have hy' : nextR (s84x_L M 1) 0 y (Lng M - 1) = true := by simpa [hLngL1] using hy
    rw [hnext0eq] at hy'; exact hy'
  have hparentL : parent (s84x_L M 1) 0 (Lng (s84x_L M 1) - 1) = transJ0 M :=
    parent_eq_of_unique_fseq (s84x_L M 1) 0 (Lng (s84x_L M 1) - 1) (transJ0 M) hnextL huniqL
  have hj0L : transJ0 (s84x_L M 1) = transJ0 M := by
    simpa [transJ0, lastParent, lastIdx] using hparentL
  exact ⟨hLngL1, hPredL1, hj0L, hpairPrefix, hentry1j1, hentry0⟩

/-- 行1エントリの `getD` 表示（`entry`/`List.getD` の定義計算）。 -/
private theorem entry1_eq_getD_cl (X : PS) (j : ℕ) :
    entry X 1 j = (X.getD j (0, 0)).2 := by
  simp only [entry, List.getD_eq_getElem?_getD]
  cases X[j]? <;> simp

/-- 述語がリスト要素上で一致すれば `List.find?` は一致する。 -/
private theorem find?_congr_cl {α : Type _} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = q x) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha : p a = q a := h a (by simp)
    have iht : t.find? p = t.find? q := ih (fun x hx => h x (by simp [hx]))
    simp only [List.find?_cons, ha, iht]

/-- `L₁ = s84x_L M 1` の `trans`-値合同（Isabelle `s84d_L1_data(8)(9)`）と (II)/(IV)
レジーム（`m_8_4_oper_props_4(2)` 相当）を非許容枝で導出する。 -/
private theorem l1_congr_cl (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true) (hnadm : adm M (transJ0 M) = false) :
    (transCondI (s84x_L M 1) || transCondIII (s84x_L M 1)
        || transCondV (s84x_L M 1)) = false
    ∧ transCondVI (s84x_L M 1) = false
    ∧ transV (s84x_L M 1) = transV M
    ∧ transT2 (s84x_L M 1) = transT2 M
    ∧ entry (s84x_L M 1) 1 (lastParent (s84x_L M 1)) = entry M 1 (transJ0 M)
    ∧ entry (s84x_L M 1) 1 (lastIdx (s84x_L M 1)) = entry M 1 (s84x_jm2 M) := by
  have hM : TPS M := STPS_TPS M hST
  have hR : RTPS M := STPS_RTPS M hST
  obtain ⟨hj1pos, ht1ne⟩ := condV_setup_holds M hR hM hmono hcond
  have hlen : 1 < Lng M := by simp only [transJ1, lastIdx] at hj1pos; omega
  have hjm2eq : s84x_jm2 M = transJ0 M := (condV_bridge_hp_jm2 M hM hmono hcond).2
  have hrng : transJ0 M + 1 < Lng M - 1 := by
    have h := hcond
    simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simpa [transJ0, lastParent, lastIdx] using h.2
  obtain ⟨hLng, hPred, hj0, hpair, hentry1j1, _hentry0⟩ := l1_geom_cl M hST hmono hcond
  -- 行1エントリの prefix 合同
  have hentry1 : ∀ j, j < Lng M - 1 → entry (s84x_L M 1) 1 j = entry M 1 j := by
    intro j hj
    rw [entry1_eq_getD_cl, entry1_eq_getD_cl, hpair j hj]
  -- lastParent / lastIdx の値
  have hlp : lastParent (s84x_L M 1) = transJ0 M := hj0
  have hli : lastIdx (s84x_L M 1) = Lng M - 1 := by simp only [lastIdx, hLng]
  -- adm 合同（内部レジーム）
  have hadm_cong : ∀ j', j' + 1 < Lng M - 1 → adm (s84x_L M 1) j' = adm M j' := by
    intro j' hj'
    have hbound : Lng M - 2 < Lng M := by omega
    have hboundL : Lng M - 2 < Lng (s84x_L M 1) := by rw [hLng]; omega
    have hagree : ∀ j, j ≤ Lng M - 2 → (s84x_L M 1).getD j (0, 0) = M.getD j (0, 0) := by
      intro j hj; exact hpair j (by omega)
    have h1 : nextR (s84x_L M 1) 1 (j' - 1) j' = nextR M 1 (j' - 1) j' :=
      nextR_prefix_agree_68 (s84x_L M 1) M (Lng M - 2) 1 (j' - 1) j'
        hagree hboundL hbound (by omega) (by omega)
    have h2 : nextR (s84x_L M 1) 1 j' (j' + 1) = nextR M 1 j' (j' + 1) :=
      nextR_prefix_agree_68 (s84x_L M 1) M (Lng M - 2) 1 j' (j' + 1)
        hagree hboundL hbound (by omega) (by omega)
    simp only [adm, nadm, hLng, h1, h2]
  have hadm_j0 : adm (s84x_L M 1) (transJ0 M) = adm M (transJ0 M) :=
    hadm_cong (transJ0 M) hrng
  -- Adm 合同 → transJm1 合同 → transV/transT2 合同
  have hfindcong : ((List.range (transJ0 M)).reverse.find? (fun j' => adm (s84x_L M 1) j'))
      = ((List.range (transJ0 M)).reverse.find? (fun j' => adm M j')) := by
    apply find?_congr_cl
    intro x hx
    have hxlt : x < transJ0 M := List.mem_range.mp (List.mem_reverse.mp hx)
    exact hadm_cong x (by omega)
  have hAdmcong : Adm (s84x_L M 1) (transJ0 M) = Adm M (transJ0 M) := by
    simp only [Adm, hadm_j0, hfindcong]
  have htransJm1 : transJm1 (s84x_L M 1) = transJm1 M := by
    show Adm (s84x_L M 1) (transJ0 (s84x_L M 1)) = Adm M (transJ0 M)
    rw [hj0, hAdmcong]
  have htransC1 : transC1 (s84x_L M 1) = transC1 M := by
    show Mark (Pred (s84x_L M 1)) (transJm1 (s84x_L M 1)) = Mark (Pred M) (transJm1 M)
    rw [hPred, htransJm1]
  have htransV : transV (s84x_L M 1) = transV M := by
    show bpHeadV (transC1 (s84x_L M 1)) = bpHeadV (transC1 M); rw [htransC1]
  have htransT2 : transT2 (s84x_L M 1) = transT2 M := by
    show bpHeadT (transC1 (s84x_L M 1)) = bpHeadT (transC1 M); rw [htransC1]
  -- entry 場（lastParent / lastIdx）
  have hEj0field : entry (s84x_L M 1) 1 (lastParent (s84x_L M 1)) = entry M 1 (transJ0 M) := by
    rw [hlp]; exact hentry1 (transJ0 M) (by omega)
  have hEj1field : entry (s84x_L M 1) 1 (lastIdx (s84x_L M 1)) = entry M 1 (s84x_jm2 M) := by
    rw [hli]; exact hentry1j1
  -- 非許容: adm L₁ (lastParent) = false
  have hadmL_false : adm (s84x_L M 1) (lastParent (s84x_L M 1)) = false := by
    rw [hlp, hadm_j0, hnadm]
  -- 中間の後継比較は偽（s84x_jm2 = j₀ より）
  have hmidfalse : (entry (s84x_L M 1) 1 (lastParent (s84x_L M 1)) + 1
      == entry (s84x_L M 1) 1 (lastIdx (s84x_L M 1))) = false := by
    rw [hEj0field, hEj1field, hjm2eq]
    simp only [beq_eq_false_iff_ne]; omega
  -- レジーム: I/III/V/VI がすべて偽
  have hI : transCondI (s84x_L M 1) = false := by
    simp only [transCondI, hadmL_false, Bool.and_false]
  have hIII : transCondIII (s84x_L M 1) = false := by
    simp only [transCondIII, hadmL_false, Bool.and_false]
  have hV : transCondV (s84x_L M 1) = false := by
    simp only [transCondV, hmidfalse, Bool.and_false, Bool.false_and]
  have hVI : transCondVI (s84x_L M 1) = false := by
    simp only [transCondVI, hmidfalse, Bool.and_false, Bool.false_and]
  have hreg : (transCondI (s84x_L M 1) || transCondIII (s84x_L M 1)
      || transCondV (s84x_L M 1)) = false := by rw [hI, hIII, hV]; rfl
  exact ⟨hreg, hVI, htransV, htransT2, hEj0field, hEj1field⟩

/-! ## `notLD` 残差への縮約 -/

/-- Isabelle `atx_notLD`（pss_wip.thy:86198）。non-admissible 条件(V) 前線 `t₂` の
末尾 principal 頭は `M₁,ⱼ₀` でない。深い Red 切片・強単項性・IncrFirst の塔
（`atx_condV_nadm_t2_components`(86068) 経由）で閉じる。Lean 未移植。 -/
def NadmC2L1NotLD : Prop :=
  ∀ M : PS, STPS M → monoT M = true → transCondV M = true →
    adm M (transJ0 M) = false →
    transT2 M ≠ BZero →
      (bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
        == (entry M 1 (transJ0 M) : ℕ∞)) = false

/-- `notLD` 残差から `NadmC2L1Support`（7 場）を復元する。構造 6 場は無条件に
（`l1_congr_cl`）、第7場 `notLD` のみ入力から。 -/
private theorem nadmC2L1Support_of_notLD_cl (hn : NadmC2L1NotLD) : NadmC2L1Support := by
  intro M hST hmono hcond hnadm
  obtain ⟨hreg, hVI, hV, hT2, hEj0, hEj1⟩ := l1_congr_cl M hST hmono hcond hnadm
  exact ⟨hreg, hVI, hV, hT2, hEj0, hEj1, hn M hST hmono hcond hnadm⟩

/-- `NadmC2L1` を単一残差 `NadmC2L1NotLD`（Isabelle `atx_notLD`）へ縮約。 -/
theorem nadmC2L1_of_notLD (hn : NadmC2L1NotLD) : NadmC2L1 :=
  nadmC2L1_of_support (nadmC2L1Support_of_notLD_cl hn)

#print axioms nadmC2L1_of_notLD

end PSS
