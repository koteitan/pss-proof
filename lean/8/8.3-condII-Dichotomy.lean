import «8».«8.3-condII-masterCF-port»
import «8».«8.4-rightmost-nonadm-ancestor»
import «8».«8.2-standard-slice-Red-strongmono»
import «8».«8.2-condV-rightmost-parent»
import «6».«6.5-Red-Pred-commute»

/-!
# §8.3 条件(II) — `TV_Dichotomy`（`cdx_d_le_joints`）: 幹 ∨ `d ≤ Joints!last` の二分岐

## 目的

ビルド済み «8».«8.3-condII-masterCF-port»:114 の名前付き `Prop` `TV_Dichotomy` を
house pattern で充足する。これは Isabelle `cdx_d_le_joints`
(layerB/pss_wip.thy:90230, ~150 行) の 1:1 移植で、条件(II) ホスト `K` の簡約祖先切片
`R_c = tvx_Rc K = Red (seg K (Adm K (parent K 0 (Lng K-1))) (Lng K-2))` について、
**`R_c` が純粋な幹（`TrMax = 最終添字`）であるか、さもなくば枝を持ち
`d = parent-Adm ≤ Joints R_c ! last`** の二分岐を主張する。

## Isabelle 証明骨格（`cdx_d_le_joints`）

`R84 := Red (seg K jm1 (Lng K-1))`（`jm1 = Adm K j0`, `j0 = parent K 0 (Lng K-1)`）を
`m_8_2_standard_slice_Red_strongmono` で `DT_PS` に落とし、
`m_8_4_rightmost_nonadm_ancestor` から
* `Br R84 ≠ []`（`Br84ge1`）
* `d = Joints R84 ! last`（`dJ84`）
* `FirstNodes R84 ! last = j1 - jm1`（`FN84`）
を得る。`FN84` と `Lng R84 = j1+1-jm1` から `R84` の最終枝は単項切片（長さ 1）。
`R_c = Pred R84`（`m_7_4_Pred_Red_slice`）なので `wid_Br_Pred` により
`Br R_c = butlast (Br R84)`。あとは `Br R84` の長さで場合分け:
* 長さ 1 → `Br R_c = []` → `TrMax R_c = Lng R_c - 1`（左）
* 長さ ≥ 2 → `Br R_c ≠ []` ＋ `wid_Joints_Pred` と `Joints` の単調性
  (`m_6_4_FirstNodes_Joints_mono_aux`) で `d = Joints R84 ! last ≤ Joints R84 ! (last-1)
   = Joints R_c ! last`（右）

## Isabelle 側の対応（名前＋行番号）

| Isabelle | 位置 | 本ファイル |
|---|---|---|
| `cdx_d_le_joints` | layerB/pss_wip.thy:90230 | `TV_Dichotomy_holds`（`TV_Dichotomy` を drop-in） |
| `c2sx_host_basic` | layerB/pss_wip.thy:86474 | `condII_host_basic_holds` |
| `m_8_4_rightmost_nonadm_ancestor` | — | `rightmost_nonadm_ancestor` |
| `m_8_2_standard_slice_Red_strongmono` | — | `standard_slice_Red_strongmono` |
| `m_7_4_Pred_Red_slice` | layerB/pss_wip.thy:11676 | `Pred_Red_terminal_slice` |
| `wid_Br_Pred` | layerB/pss_wip.thy:29093 | `Br_Pred_core_nontrunk` |
| `wid_Joints_Pred` | layerB/pss_wip.thy:29260 | `Joints_Pred_core` |
| `m_6_4_FirstNodes_Joints_mono_aux` | — | `FirstNodes_Joints_mono` |
| `wf21_Br_eq_seg` | — | `wf21_Br_eq_seg` |
| `m_6_5_Lng_Red` | — | `Lng_Red_invariance` |

## 依存（すべて COMMITTED 緑）

* «8».«8.3-condII-masterCF-port» — `TV_Dichotomy` / `tvx_Rc` / `tvx_d` / `tvx_jL` の定義。
  推移的に «8».«8.3-condII-masterCF»（`condII_host_basic_holds` / `CondII_host_basic`）、
  «7».«7.4-Mark-Trans-repr»（`Pred_Red_terminal_slice`）。
* «8».«8.4-rightmost-nonadm-ancestor» — `rightmost_nonadm_ancestor`。推移的に
  `row0_transitive` / `nextR0_leR` / `nextR_parent0_of_hasParent` /
  `FirstNodes_Joints_mono` / `Lng_Red_invariance` / `length_seg` / `P_nonempty` /
  `adm_row1_ancestry` / `row1_implies_row0` / `STPS_RTPS` / `RTPS_TPS`。
* «8».«8.2-standard-slice-Red-strongmono» — `standard_slice_Red_strongmono` /
  `DTPS_iff` / `DTPS_TPS`。
* «8».«8.2-condV-rightmost-parent» — `wf21_Br_eq_seg`。
* «6».«6.5-Red-Pred-commute» — `Br_Pred_core_nontrunk` / `Joints_Pred_core`。

## 状態

* ✅ `TV_Dichotomy_holds : TV_Dichotomy`（sorry 0, 無条件, 公理 3 個）。
  `CondII_masterCF` の tailval 連鎖 4 残差の 1 本を閉じる。
-/

namespace PSS

/-- `getLastD` を末尾添字の `getD` に橋渡し（`getLast?`/`getElem?` 経由、仮定不要）。 -/
private theorem getLastD_eq_getD_dch {α : Type} (l : List α) (d : α) :
    l.getLastD d = l.getD (l.length - 1) d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- `leR` の反射性（`6.4-mono-slice` の私的 `leR0_refl_ms` の再証明）。 -/
private theorem leR0_refl_dch (M : PS) (j : ℕ) (hj : j < Lng M) :
    leR M 0 j j = true := by
  have haux : le0Aux M (Lng M) j j = true := by
    cases hL : Lng M <;> simp [le0Aux]
  simp [leR, le0, hj, haux]

/-- Isabelle `cdx_d_le_joints` の**組合せ核**（`R84`/`Rc` を不透明 fvar として抽象化）。

`Rc = Pred R84` かつ `R84` の最終枝が単項（`hlast1`）であるとき、`R84` の枝の長さで
場合分けして二分岐を出す。`R84` は `DT_PS` 切片（`hR84mono`）、`Rc` はその前者。 -/
private theorem cdx_peel_dch (j0 jm1 : ℕ) (R84 Rc : PS)
    (hRcPred : Rc = Pred R84)
    (hBr84ge1 : 1 ≤ (Br R84).length)
    (hdJ84 : j0 - jm1 = (Joints R84).getD ((Br R84).length - 1) 0)
    (hlast1 : Lng ((Br R84).getLastD []) = 1)
    (hR84T : TPS R84) (hR84mono : monoT R84 = true)
    (hLR84gt : 1 < Lng R84) (hne84 : TrMax R84 ≠ Lng R84 - 1) :
    TrMax Rc = Lng Rc - 1 ∨
      (Br Rc ≠ [] ∧ j0 - jm1 ≤ (Joints Rc).getD ((Br Rc).length - 1) 0) := by
  -- `wid_Br_Pred` で `Br Rc = butlast (Br R84)`（最終枝は単項なので `if` の枝が消える）
  have hshape := Br_Pred_core_nontrunk R84 hR84T hLR84gt hne84
  rw [hlast1, if_pos (le_refl 1), List.append_nil, ← hRcPred] at hshape
  -- `hshape : Br Rc = (Br R84).dropLast`
  by_cases hcase : (Br R84).length = 1
  · -- 単項枝: `Br Rc = []`、幹（左）
    left
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hcase
    have hBrRcNil : Br Rc = [] := by rw [hshape, ha]; simp
    by_contra hcon
    rw [Br, if_neg hcon] at hBrRcNil
    exact P_nonempty _ hBrRcNil
  · -- 枝 ≥ 2: 右
    right
    have hlen2 : 2 ≤ (Br R84).length := by omega
    have hBrRcLen : (Br Rc).length = (Br R84).length - 1 := by
      rw [hshape, List.length_dropLast]
    have hidx : (Br Rc).length - 1 = (Br R84).length - 2 := by rw [hBrRcLen]; omega
    refine ⟨?_, ?_⟩
    · -- `Br Rc ≠ []`
      rw [hshape]
      intro h
      have hl : (Br R84).dropLast.length = (Br R84).length - 1 := List.length_dropLast
      rw [h, List.length_nil] at hl
      omega
    · -- `d ≤ Joints Rc ! last`
      have hJlt : (Br R84).length - 2 < (Br (Pred R84)).length := by
        rw [← hRcPred, hBrRcLen]; omega
      have hjointeq :=
        Joints_Pred_core R84 hR84T hR84mono hLR84gt hne84 ((Br R84).length - 2) hJlt
      rw [← hRcPred] at hjointeq
      -- `hjointeq : (Joints Rc).getD (last-2) 0 = (Joints R84).getD (last-2) 0`
      have hmono2 :=
        FirstNodes_Joints_mono R84 ((Br R84).length - 2) ((Br R84).length - 1)
          hR84T hR84mono (by omega) (by omega)
      calc
        j0 - jm1 = (Joints R84).getD ((Br R84).length - 1) 0 := hdJ84
        _ ≤ (Joints R84).getD ((Br R84).length - 2) 0 := hmono2.2.1
        _ = (Joints Rc).getD ((Br Rc).length - 1) 0 := by rw [hidx]; exact hjointeq.symm

/-- Isabelle `cdx_d_le_joints` (layerB/pss_wip.thy:90230) の **1:1** 移植。
`TV_Dichotomy`（«8».«8.3-condII-masterCF-port»:114）を house pattern で drop-in する。 -/
theorem TV_Dichotomy_holds : TV_Dichotomy := by
  intro K hK hmono hj1gt hcond
  have hR : RTPS K := STPS_RTPS K hK
  have hM : TPS K := RTPS_TPS K hR
  -- 条件(II) ホストの基本諸性質
  obtain ⟨hp0, e1z, nadmj, hj0pos, hjm1ltj0, hw2, -⟩ :=
    condII_host_basic_holds K hR hmono hj1gt hcond
  -- ゴールを `tvx_*` 展開
  simp only [tvx_Rc, tvx_d, tvx_jL]
  -- `j0`/`jm1` を不透明 fvar 化してゴール・仮定を畳む
  obtain ⟨j0, hj0def⟩ : ∃ x, x = parent K 0 (Lng K - 1) := ⟨_, rfl⟩
  rw [← hj0def] at nadmj hj0pos hjm1ltj0 hw2 ⊢
  obtain ⟨jm1, hjm1def⟩ : ∃ x, x = Adm K j0 := ⟨_, rfl⟩
  rw [← hjm1def] at hjm1ltj0 ⊢
  -- 基本的な順序の事実
  have hj0lt : j0 < Lng K - 1 := by omega
  have hj1L : Lng K - 1 < Lng K := by omega
  have hjm1ltj1 : jm1 < Lng K - 1 := by omega
  -- 親辺・反射・行1非親
  have hnx : nextR K 0 j0 (Lng K - 1) = true := by
    have h := nextR_parent0_of_hasParent K (Lng K - 1) hp0
    rwa [← hj0def] at h
  have hle : leR K 0 (Lng K - 1) (Lng K - 1) = true := leR0_refl_dch K (Lng K - 1) hj1L
  have hnotnx1 : nextR K 1 ((Lng K - 1) - 1) (Lng K - 1) = false := by
    have hif : nextR K 1 ((Lng K - 1) - 1) (Lng K - 1)
        = nextrel1 K ((Lng K - 1) - 1) (Lng K - 1) := by simp [nextR]
    rw [hif, nextrel1, e1z]
    simp
  -- `(0,jm1) ≤_K (0,j1)`
  have hle1a : leR K 1 jm1 j0 = true := by
    have h := adm_row1_ancestry K j0 hM (by omega)
    rwa [← hjm1def] at h
  have hle0a : leR K 0 jm1 j0 = true := row1_implies_row0 K jm1 j0 hM hle1a
  have hle0j0j1 : leR K 0 j0 (Lng K - 1) = true := nextR0_leR K j0 (Lng K - 1) hnx
  have leRjm1j1 : leR K 0 jm1 (Lng K - 1) = true :=
    row0_transitive K jm1 j0 (Lng K - 1) hM hle0a hle0j0j1
  -- `rightmost_nonadm_ancestor` の三点セット
  have RN := rightmost_nonadm_ancestor K j0 (Lng K - 1) hK hmono hnx hle hnotnx1 nadmj
  rw [← hjm1def] at RN
  obtain ⟨hBr84ge1, -, hdJ84, hFN84⟩ := RN
  -- `R84 = Red (seg K jm1 (Lng K-1))` は `DT_PS`
  have R84DT : DTPS (Red (seg K jm1 (Lng K - 1))) :=
    standard_slice_Red_strongmono K jm1 (Lng K - 1) hK hjm1ltj1 (le_refl _) leRjm1j1
  have R84T : TPS (Red (seg K jm1 (Lng K - 1))) := DTPS_TPS _ R84DT
  have R84mono : monoT (Red (seg K jm1 (Lng K - 1))) = true := ((DTPS_iff _).mp R84DT).2.1
  have hBr84ne : Br (Red (seg K jm1 (Lng K - 1))) ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  -- 長さ
  have hsegpos : 0 < Lng (seg K jm1 (Lng K - 1)) := by rw [length_seg]; omega
  have hsegT : TPS (seg K jm1 (Lng K - 1)) := List.ne_nil_of_length_pos hsegpos
  have hLR84 : Lng (Red (seg K jm1 (Lng K - 1))) = (Lng K - 1) + 1 - jm1 := by
    rw [Lng_Red_invariance _ hsegT, length_seg]
  have hLR84gt : 1 < Lng (Red (seg K jm1 (Lng K - 1))) := by rw [hLR84]; omega
  have hne84 : TrMax (Red (seg K jm1 (Lng K - 1)))
      ≠ Lng (Red (seg K jm1 (Lng K - 1))) - 1 := fun h => hBr84ne (by simp [Br, h])
  -- 最終枝は単項（長さ 1）
  have hlast1 : Lng ((Br (Red (seg K jm1 (Lng K - 1)))).getLastD []) = 1 := by
    rw [getLastD_eq_getD_dch, wf21_Br_eq_seg _ R84T hBr84ne, length_seg, hFN84]
    omega
  -- `Rc = Pred R84`
  have hRcPred : Red (seg K jm1 (Lng K - 2)) = Pred (Red (seg K jm1 (Lng K - 1))) := by
    have h := Pred_Red_terminal_slice K jm1 (Lng K - 1) hjm1ltj1
    rw [show (Lng K - 1) - 1 = Lng K - 2 from by omega] at h
    exact h.symm
  -- 組合せ核に投入
  exact cdx_peel_dch j0 jm1 (Red (seg K jm1 (Lng K - 1))) (Red (seg K jm1 (Lng K - 2)))
    hRcPred hBr84ge1 hdJ84 hlast1 R84T R84mono hLR84gt hne84

#print axioms TV_Dichotomy_holds

end PSS
