import «8».«8.4-l6-slice-close»

/-!
# §8.4 補題 part (2) の L 塔底読み出し `L6TowerResidual` の討伐

- 原文: `tmp/content.md` 5008（補題（条件(III)か(IV)の下での基本列の基本性質）part (2)）。
  `j₁ = Lng M - 1`、`j₋₂ = parent M 1 j₁`、`w' = j₁ - 1 - j₋₂` として、L 切片塔の底読み出し
  4 葉（`«8».«8.4-l6-slice-close»` の `L6TowerResidual`）を扱う。
- Isabelle（設計図）: `y3l_p_8_4_oper_basic_part2`（`isabelle/layerC/pss_scratch.thy:18777`）
  の底読み出し部。

## 本ファイルの内容

`L6TowerResidual`（`«8».«8.4-l6-slice-close»:103`）は塔帰納の底読み出し 4 葉:
* (1) `op1pow`: `op1^{w'}(M[n+1]) = s84x_L M n`（Isabelle `y3l_L_eq_op1pow`）。
* (2) `ub_eq`: `(entry M 1 (s84x_jm2 M) : ℕ∞) = ub`。
* (3) `base`: 底段 `L₁` の `Trans` 平坦形（Isabelle `base5`）。
* (4) `lpv`: 単一段の中心値 `Trans(L')` 平坦形（Isabelle `s84d_dec*` Lp 読み出し）。

**(1) op1pow は本ファイルが無条件に討伐する**（純ペア数列組合せ論、`op1` 反復 = `take`）。
Isabelle `y3l_op1pow_take`（`op1^{k} Z = take (Lng Z − k) Z`）＋ `y3l_L_eq_op1pow`
（`op1^{w−1}(M[n+1]) = s84x_L M n`）の忠実移植。土台の tiling 補題
（`length_oper_tiling`/`oper_tiling_expand`、`«6».«6.6-reduced-fseq»`、公開）から底を組む。
数値監査 164/164（`python/_l6_part2_audit.py`）。

**(2)(3)(4) は producer 座標での底読み出し残差 `L6BaseReadoutsResidual` に括り出す**。
これらは L₁/L' 切片の `Trans` 平坦値であり、§8.4 の L1 切片幾何（`base5`/`s84d_dec`、
`cfbx_reg` 正則性エンジン消費、Lean 未移植の frontier）に属す。producer の全出力
（`hflat`/`hb0`/`hb1`/`fO`/`fM`/`base0`/`base1`/`Lbase`）を仮定として持つ named Prop
として残す（`«8».«8.4-mnform-corner-dispatch»` の `MnformResidual` と同じ残差境界）。

- 依存（すべてビルド済み・main caf2a82）: «8».«8.4-l6-slice-close»
  (`L6TowerResidual` def・`l6TransSliceClosed_holds`・`L6TransSliceClosed_p2`・
  `oper84BasicPart2_holds`・`Oper84BasicPart2Residual`・`oper_basic_part2`・
  `s84x_L`/`s84x_Lp`/`s84x_jm2`・`coreTower_e34`・`operB`/`numBT`・`Trans`/`oper`/`entry`/`Lng`)、
  推移的に «6».«6.6-reduced-fseq» (`length_oper_tiling`/`oper_tiling_expand`)、
  «6».«6.6-reduced-slice» (`RTPS_initial_slice`)、«6».«6.3-adm-slice» (`seg_eq_take_drop_adm`)、
  «5».«5.3-pred-is-oper1» (`pred_is_oper1`)、«8».«8.4-oper5-residual» (`s84x_L_eq_append`)。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  (1) 無条件討伐、残差 = producer 座標の底読み出し `L6BaseReadoutsResidual`（(2)(3)(4)）。
- 停止性連鎖には不要（`p_8_7_termination` は無条件・独立）。原文カバレッジのための逐語形。
- Private helper suffix: `_br`。
-/

namespace PSS

/-! ## 0. tiling 補助（`«8».«8.4-oper5-residual»` private の `_br` 複製） -/

/-- `«8».«8.4-oper5-residual»` private `setup_o5r` の複製。 -/
private theorem setup_br (M : PS) (hM : TPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    idx1 M (Lng M - 1) = 1 ∧ 1 < Lng M ∧
      ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) ∧
      hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true ∧
      parent M (idx1 M (Lng M - 1)) (Lng M - 1) = s84x_jm2 M ∧
      s84x_jm2 M < Lng M - 1 ∧
      entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) := by
  obtain ⟨hjm2lt, he1, hle0⟩ := s84c1_jm2_basic M hp
  have he1pos : 0 < entry M 1 (Lng M - 1) := by omega
  have hidx : idx1 M (Lng M - 1) = 1 := by unfold idx1; rw [if_pos he1pos]
  have hlast : 1 < Lng M := by omega
  have hnz : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨_, h2⟩; omega
  have hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by rw [hidx]; exact hp
  have hj0 : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = s84x_jm2 M := by
    unfold s84x_jm2; rw [hidx]
  have he0lt : entry M 0 (s84x_jm2 M) < entry M 0 (Lng M - 1) := by
    have hleR : leR M 0 (s84x_jm2 M) (Lng M - 1) = true := by simpa [leR] using hle0
    exact ancestor_basic_1 M (s84x_jm2 M) (Lng M - 1) (Lng M - 1) hM hjm2lt (le_refl _) hleR
  exact ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩

/-- `«8».«8.4-oper5-residual»` private `Lng_oper_o5r` の複製: `Lng (M[k]) = j₋₂ + k·w`。 -/
private theorem Lng_oper_br (M : PS) (k : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    Lng (oper M k) = s84x_jm2 M + k * (Lng M - 1 - s84x_jm2 M) := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_br M hM hp hj1
  have h : Lng (oper M k)
      = parent M (idx1 M (Lng M - 1)) (Lng M - 1)
          + k * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) :=
    length_oper_tiling M k hlast hnz hp'
  rw [hj0] at h; exact h

/-- `«8».«8.4-oper5-residual»` private `oper_succ_append_o5r` の複製。 -/
private theorem oper_succ_append_br (M : PS) (m : ℕ)
    (hlast : 1 < Lng M)
    (hnz : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true) :
    oper M (m + 1) = oper M m ++
      (List.range' (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
                   (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1))).map
        (fun j => (entry M 0 j
                     + m * (if 0 < idx1 M (Lng M - 1)
                            then entry M 0 (Lng M - 1)
                                   - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
                            else 0),
                   entry M 1 j
                     + m * (if 1 < idx1 M (Lng M - 1)
                            then entry M 1 (Lng M - 1)
                                   - entry M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
                            else 0))) := by
  have e1 := oper_tiling_expand M (m + 1) hlast hnz hp'
  have e0 := oper_tiling_expand M m hlast hnz hp'
  dsimp only at e1 e0
  rw [e1, e0, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.append_assoc]

/-- `range'` の先頭剥がし（`«8».«8.4-oper5-residual»` private `range'_eq_cons_o5r` の複製）。 -/
private theorem range'_eq_cons_br (s n : ℕ) (hn : 0 < n) :
    List.range' s n = s :: List.range' (s + 1) (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

/-- `«8».«8.4-oper5-residual»` private `oper_succ_L_o5r` の複製:
`M[m+1] = L_m ++ 残り`。 -/
private theorem oper_succ_L_br (M : PS) (m : ℕ)
    (hlast : 1 < Lng M)
    (hnz : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true)
    (hidx : idx1 M (Lng M - 1) = 1)
    (hjm2lt : s84x_jm2 M < Lng M - 1) :
    oper M (m + 1) = s84x_L M m ++
      (List.range' (s84x_jm2 M + 1) (Lng M - 1 - s84x_jm2 M - 1)).map
        (fun j => (entry M 0 j
                     + m * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
                   entry M 1 j)) := by
  have hj0 : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = s84x_jm2 M := by
    unfold s84x_jm2; rw [hidx]
  have hd1 : (if 1 < idx1 M (Lng M - 1)
             then entry M 1 (Lng M - 1) - entry M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
             else 0) = 0 := by rw [hidx]; simp
  have hd0 : (if 0 < idx1 M (Lng M - 1)
             then entry M 0 (Lng M - 1) - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
             else 0) = entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M) := by
    rw [hidx]; simp [s84x_jm2]
  have happ := oper_succ_append_br M m hlast hnz hp'
  simp only [hd0, hd1, Nat.mul_zero, Nat.add_zero] at happ
  simp only [hj0] at happ
  rw [happ, range'_eq_cons_br (s84x_jm2 M) (Lng M - 1 - s84x_jm2 M) (by omega),
    List.map_cons, s84x_L_eq_append]
  rw [List.append_assoc]
  rfl

/-- Isabelle `s84c1_L_take`: `take (Lng (M[n]) + 1) (M[n+1]) = L_n`。 -/
private theorem s84c1_L_take_br (M : PS) (n : ℕ)
    (hM : TPS M) (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) :
    (oper M (n + 1)).take (Lng (oper M n) + 1) = s84x_L M n := by
  obtain ⟨hidx, hlast, hnz, hp', hj0, hjm2lt, he0lt⟩ := setup_br M hM hp hj1
  have hsucc := oper_succ_L_br M n hlast hnz hp' hidx hjm2lt
  have hLngL : (s84x_L M n).length = Lng (oper M n) + 1 := by rw [s84x_L_eq_append]; simp
  rw [hsucc]
  exact List.take_left' hLngL

/-! ## 1. `op1` 反復 = `take`（Isabelle `y3l_op1pow_take`） -/

/-- `take m` の `dropLast`（`m ≤ length` なら `take (m-1)`）。 -/
private theorem dropLast_take_br (l : PS) (m : ℕ) (hm : m ≤ l.length) :
    (l.take m).dropLast = l.take (m - 1) := by
  apply List.ext_getElem
  · simp only [List.length_dropLast, List.length_take]
    omega
  · intro i h1 h2
    simp only [List.getElem_dropLast, List.getElem_take]

/-- Isabelle `y3l_op1pow_take`: `Z ∈ RT_PS`・`1 ≤ Lng Z − k` なら
`op1^{k} Z = take (Lng Z − k) Z`。 -/
private theorem op1pow_take_br (Z : PS) (hZ : RTPS Z) :
    ∀ k, 1 ≤ Lng Z - k → ((fun N => oper N 1)^[k] Z) = Z.take (Lng Z - k) := by
  have hlenZ : Z.length = Lng Z := rfl
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : 1 ≤ Lng Z - k := by omega
      have hih := ih hk'
      have hle : Lng Z - k ≤ Lng Z := by omega
      have hWlen : (Z.take (Lng Z - k)).length = Lng Z - k := by
        rw [List.length_take]; omega
      have hWR : RTPS (Z.take (Lng Z - k)) := by
        have h := RTPS_initial_slice Z (Lng Z - k - 1) hZ (by omega)
        rwa [seg_eq_take_drop_adm Z 0 (Lng Z - k - 1) (Nat.zero_le _) (by omega),
             List.drop_zero, show Lng Z - k - 1 + 1 - 0 = Lng Z - k from by omega] at h
      have hWT : TPS (Z.take (Lng Z - k)) := RTPS_TPS _ hWR
      have hWgt : 1 < Lng (Z.take (Lng Z - k)) := by
        show 1 < (Z.take (Lng Z - k)).length
        rw [hWlen]; omega
      have hPred : Pred (Z.take (Lng Z - k)) = (Z.take (Lng Z - k)).dropLast := by
        unfold Pred; rw [if_neg (by omega)]
      rw [Function.iterate_succ_apply', hih]
      show oper (Z.take (Lng Z - k)) 1 = Z.take (Lng Z - (k + 1))
      rw [← pred_is_oper1 _ hWT hWgt, hPred, dropLast_take_br Z (Lng Z - k) hle,
          show Lng Z - k - 1 = Lng Z - (k + 1) from by omega]

/-! ## 2. (1) op1pow 橋（Isabelle `y3l_L_eq_op1pow`、無条件） -/

/-- **`L6TowerResidual` 底読み出し (1)**（Isabelle `y3l_L_eq_op1pow`,
`isabelle/layerC/pss_scratch.thy:18706`）。`op1^{j₁−1−j₋₂}(M[n+1]) = L_n`。
純ペア数列組合せ論（`op1` 反復 = `take`）で無条件討伐。 -/
theorem l6_op1pow_bridge_br (M : PS) (n : ℕ)
    (hST : STPS M)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1) (hn : 1 ≤ n) :
    (fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)] (oper M (n + 1))
      = s84x_L M n := by
  have hMT : TPS M := RTPS_TPS M (STPS_RTPS M hST)
  have hj2 : parent M 1 (Lng M - 1) = s84x_jm2 M := rfl
  have hjm2lt : s84x_jm2 M < Lng M - 1 := (s84c1_jm2_basic M hp).1
  have hZR : RTPS (oper M (n + 1)) := STPS_RTPS _ (STPS.oper hST (n + 1) (by omega))
  have hLngZ : Lng (oper M (n + 1)) = s84x_jm2 M + (n + 1) * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_br M (n + 1) hMT hp hj1
  have hLngn : Lng (oper M n) = s84x_jm2 M + n * (Lng M - 1 - s84x_jm2 M) :=
    Lng_oper_br M n hMT hp hj1
  have hexp : (Lng M - 1) - 1 - parent M 1 (Lng M - 1)
      = (Lng M - 1 - s84x_jm2 M) - 1 := by rw [hj2]; omega
  have hsub : Lng (oper M (n + 1)) - ((Lng M - 1 - s84x_jm2 M) - 1)
      = Lng (oper M n) + 1 := by
    rw [hLngZ, hLngn]
    have hmul : (n + 1) * (Lng M - 1 - s84x_jm2 M)
        = n * (Lng M - 1 - s84x_jm2 M) + (Lng M - 1 - s84x_jm2 M) := by ring
    omega
  have hge1 : 1 ≤ Lng (oper M (n + 1)) - ((Lng M - 1 - s84x_jm2 M) - 1) := by omega
  rw [hexp, op1pow_take_br (oper M (n + 1)) hZR ((Lng M - 1 - s84x_jm2 M) - 1) hge1, hsub]
  exact s84c1_L_take_br M n hMT hp hj1

/-! ## 3. (2)(3)(4) 底読み出し残差（producer 座標） -/

/-- **producer 座標での底読み出し残差**（`L6TowerResidual` の (2)(3)(4)）。
L₁/L' 切片の `Trans` 平坦値であり、§8.4 L1 切片幾何（Isabelle `base5`/`s84d_dec*`、
`cfbx_reg` 正則性エンジン消費、Lean 未移植 frontier）に属す。producer の全出力を
仮定として持つ。 -/
def L6BaseReadoutsResidual : Prop :=
  ∀ (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym),
    STPS M → monoT M = true → 1 ≤ n →
    hasParent M 1 (Lng M - 1) = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) →
    (∀ x ∈ b1, x = Sym.rp) →
    (∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1) →
    (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1) →
    lessBT (Dprin ub BZero) A0 = true →
    lessBT A0 (ins (Dprin ub BZero)) = true →
    leBT (Dprin ub BZero) (ins BZero) = true →
    ((entry M 1 (s84x_jm2 M) : ℕ∞) = ub)
    ∧ (flatBT (Trans (s84x_L M 1))
        = s1 ++ Sym.dsym e3 :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0) ++ b1)
    ∧ (flatBT (Trans (s84x_Lp M))
        = Sym.dsym ub :: (s0 ++ [Sym.dsym ub, Sym.zero] ++ b0))

/-! ## 4. `L6TowerResidual` の討伐（(1) 無条件 ＋ (2)(3)(4) residual） -/

/-- **`L6TowerResidual`（`«8».«8.4-l6-slice-close»:103`）の drop-in**（house pattern）。
底読み出し (1) op1pow を無条件に組み、(2)(3)(4) を producer 座標残差
`L6BaseReadoutsResidual` から取る。 -/
theorem l6TowerResidual_holds (hbr : L6BaseReadoutsResidual) : L6TowerResidual := by
  intro M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
    hflat hb0 hb1 fO fM base0 base1 Lbase
  refine ⟨l6_op1pow_bridge_br M n hST hp hj1 hn, ?_⟩
  exact hbr M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj1 hcond
    hflat hb0 hb1 fO fM base0 base1 Lbase

/-! ## 5. §8.4 part (2) の合成（`L6BaseReadoutsResidual` modulo） -/

/-- **§8.4 補題 part (2)**（原文 `tmp/content.md` 5008、Isabelle
`y3m_p_8_4_oper_basic_part2_full`）を `L6BaseReadoutsResidual` modulo で供給。
親連鎖 `oper_basic_part2 ∘ oper84BasicPart2_holds ∘ l6TransSliceClosed_holds ∘
l6TowerResidual_holds` を合成。 -/
theorem oper_basic_part2_br (hbr : L6BaseReadoutsResidual)
    (M : PS) (n : ℕ)
    (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hj₁ : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    operB (Trans M) (numBT (n - 1)) =
      Trans ((fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)] (oper M (n + 1))) :=
  oper_basic_part2 (oper84BasicPart2_holds (l6TransSliceClosed_holds (l6TowerResidual_holds hbr)))
    M n hST hmono hn hp hj₁ hcond

#print axioms l6_op1pow_bridge_br
#print axioms l6TowerResidual_holds
#print axioms oper_basic_part2_br

end PSS
