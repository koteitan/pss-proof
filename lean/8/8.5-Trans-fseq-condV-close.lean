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
# §8.5 命題（条件 (V) の下での `Trans` と基本列の交換関係）— instantiation close

- 原文: `tmp/content.md` §8.5「命題（条件(V)の下での Trans と基本列の交換関係）」
  (content.md:5153)。逐語: `p_8_5_Trans_oper_exchange` (isabelle/pss_paper.thy:2070)。
- 訂正: **なし**（A28 は取り下げ済み、`corrections-old.md`:95）。
- 目的: `8.5-Trans-fseq-condV.lean` の公開定理はいずれも 6 本の named Prop
  {`ExchV_scbdec_adm_forms`, `ExchV_scbdec_c1_shape`, `ExchV_condV_setup`,
  `ExchV_t2_nonzero_condV`, `ExchV_nf3x`, `ExchV_scbdec_fseq_condV`} を仮定に取る
  green-modulo 版だった。本ファイルはこの 6 本を **すべて無条件に供給**し、
  各公開定理の **無条件双子**（接尾辞 `_vc`）を出す。これで task 項目
  `8.5-Trans-fseq-condV` が done になる。
- 6 本の無条件供給元（すべて `#print axioms` clean、Wave AW 統合済み）:
  | Prop | supplier | 供給元ファイル |
  |---|---|---|
  | `ExchV_condV_setup` | `condV_setup_holds` | `8.5-exchV-props` |
  | `ExchV_scbdec_c1_shape` | `c1_shape_holds` | `8.5-exchV-props` |
  | `ExchV_t2_nonzero_condV` | `t2_nonzero_condV_holds` | `8.5-exchV-props` |
  | `ExchV_scbdec_fseq_condV` | `fseq_condV_holds` | `8.5-exchV-props` |
  | `ExchV_scbdec_adm_forms` | `adm_forms_holds exchVresAdm_vc` | `8.5-exchV-props(2)` |
  | `ExchV_nf3x` | `nf3x_holds_xv2 exchVMtower_vc` | `8.5-exchV-props2` |
  最後の 2 本は `ExchV_M_tower` 塔から来る（`8.7-termination` の
  `exchVMtower_term` / `exchVresAdm_term` / `exchVnf3x_term` と同一合成、ただし
  あちらは private なので本ファイルで同じ term を再構成する）。
- 塔の合成（`8.7-termination`:260 の逐語再構成）:
  `exchV_M_tower_of_residual` (`8.5-exchV-M-tower`) ∘
  `exchVMres_of_values` (`8.5-exchV-M-tower-close`) ∘
  `exchVMvalues_of_nadm_package` (`8.5-exchV-values-close`) ∘
  `exchVMNadmAtomicPackage_of_parts` (`8.5-exchV-nadm-atomics`) の 3 引数
  {`rightmost84ReplaceCorrected_of_exists rightmost84ReplaceExists_rc2`
   (`8.4-rightmost-replace-close` / `8.4-rm84-rfacts-close`),
   `nadmW2nostr_holds` (`8.5-exchV-nadm-w2nostr`),
   `nadmC2L1_of_notLD nadmC2L1NotLD_holds` (`8.5-exchV-nadm-c2l1` / `8.5-exchV-notld`)}。
- 忠実性: 公開双子の**論理式は p ファイルと 1 文字も変えていない**（仮定から
  6 Prop を除いただけ）。よって p ファイルが原文に対して確立した忠実性
  （原文添字 `mₙ = n-1` の adm 枝 (1)(2)(3)、`≤` ではなく `<` で厳密、訂正不要）が
  そのまま無条件版に受け継がれる。非 adm 枝の原文添字 `mₙ = n` の真偽は
  p ファイル同様 scope 外（Isabelle が証明した添字は `n+1`）。
- 状態: GREEN（sorry 0）、無条件（axioms = propext / Classical.choice / Quot.sound）。
-/

namespace PSS

/-! ## 6 本の named Prop の無条件供給（`8.7-termination`:260 の private 合成を再構成） -/

/-- `8.7-termination`:260 `exchVMtower_term` の逐語再構成。 -/
private theorem exchVMtower_vc : ExchV_M_tower :=
  exchV_M_tower_of_residual
    (exchVMres_of_values (exchVMvalues_of_nadm_package
      (exchVMNadmAtomicPackage_of_parts
        (rightmost84ReplaceCorrected_of_exists rightmost84ReplaceExists_rc2)
        nadmW2nostr_holds (nadmC2L1_of_notLD nadmC2L1NotLD_holds))))

/-- `8.7-termination`:267 `exchVresAdm_term` の逐語再構成。 -/
private theorem exchVresAdm_vc : ExchVres_adm_M_tower :=
  exchVres_adm_M_tower_of_M_tower exchVMtower_vc

/-- `ExchV_scbdec_adm_forms` の無条件供給（`8.7-termination`:337）。 -/
private theorem admForms_vc : ExchV_scbdec_adm_forms :=
  adm_forms_holds exchVresAdm_vc

/-- `ExchV_nf3x` の無条件供給（`8.7-termination`:270 `exchVnf3x_term`）。
非 adm 枝の閉形式は `bijectivity` の 補題（基本列の関係）でも要るので公開する。 -/
theorem nf3x_vc : ExchV_nf3x :=
  nf3x_holds_xv2 exchVMtower_vc

/-! ## 公開定理の無条件双子（p ファイルの論理式と同一、6 Prop 仮定を除去） -/

/-- 無条件版（`Trans_oper_exchange_condV_adm_uncond`）。adm 枝の 4 連言:
`Trans(M[n]) < Trans(M)[n-1]`（原文添字）/`< Trans(M)[n]`（Isabelle 添字）/
`< Trans(M)`（降下）/`Trans(M)[n-1] < Trans(M[n+1])`。 -/
theorem Trans_oper_exchange_condV_adm_uncond_vc
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hcond : transCondV M = true)
    (hadm : adm M (parent M 0 (Lng M - 1)) = true) :
    lessBT (Trans (oper M n)) (operB (Trans M) (numBT (n - 1))) = true ∧
      lessBT (Trans (oper M n)) (operB (Trans M) (numBT n)) = true ∧
      lessBT (Trans (oper M n)) (Trans M) = true ∧
      lessBT (operB (Trans M) (numBT (n - 1))) (Trans (oper M (n + 1))) = true :=
  Trans_oper_exchange_condV_adm_uncond admForms_vc c1_shape_holds
    condV_setup_holds t2_nonzero_condV_holds M n hST hmono hn hcond hadm

/-- 無条件版（`Trans_oper_exchange_condV_nonadm_uncond`）。非 adm 枝では正しい
Buchholz 添字は `n + 1`（Isabelle が証明した形）。 -/
theorem Trans_oper_exchange_condV_nonadm_uncond_vc
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true)
    (hcond : transCondV M = true)
    (hnadm : adm M (parent M 0 (Lng M - 1)) = false) (hn : 1 ≤ n) :
    lessBT (Trans (oper M n)) (operB (Trans M) (numBT (n + 1))) = true ∧
      lessBT (Trans (oper M n)) (Trans M) = true :=
  Trans_oper_exchange_condV_nonadm_uncond nf3x_vc fseq_condV_holds
    c1_shape_holds condV_setup_holds M n hST hmono hcond hnadm hn

/-- 原文命題（条件 (V) の下での `Trans` と基本列の交換関係）の忠実版の**無条件双子**
（`p_8_5_Trans_oper_exchange`, isabelle/pss_paper.thy:2070、content.md:5153）、**adm 枝**。
原文の添字 `mₙ = n - 1`（`if adm … then n-1 else n`）のままで (1)(2)(3) の三結論が
すべて成立する（`≤` ではなく `<` で厳密。訂正不要）。 -/
theorem Trans_oper_exchange_condV_vc
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hj₁ : 1 < Lng M - 1) (hcond : transCondV M = true)
    (hadm : adm M (parent M 0 (Lng M - 1)) = true) :
    leBT (Trans (oper M n))
        (operB (Trans M)
          (numBT (if adm M (parent M 0 (Lng M - 1)) then n - 1 else n))) = true ∧
      leBT (Trans (oper M n)) (Trans M) = true ∧
      leBT (operB (Trans M)
          (numBT (if adm M (parent M 0 (Lng M - 1)) then n - 1 else n)))
        (Trans (oper M (n + 1))) = true :=
  Trans_oper_exchange_condV admForms_vc c1_shape_holds condV_setup_holds
    t2_nonzero_condV_holds M n hST hmono hn hj₁ hcond hadm

/-- 無条件版（`exchV_holds`）。`8.7-fseq-descend` の `FseqDesc_exchV` と同形
（drop-in）。全 host 無条件（adm 枝は `numBT (m-1)`、非 adm 枝は `numBT (m+1)`）。 -/
theorem exchV_holds_vc :
    ∀ (N : PS) (m : ℕ), STPS N → monoT N = true → 1 < Lng N - 1 →
      transCondV N = true → 1 < m →
      ∃ k, leBT (Trans (oper N m)) (operB (Trans N) (numBT k)) = true :=
  exchV_holds admForms_vc c1_shape_holds condV_setup_holds
    t2_nonzero_condV_holds nf3x_vc fseq_condV_holds

/-- 無条件版（`Trans_oper_descend_condV`）。降下性（原文の結論 (2)）、全 host 無条件。 -/
theorem Trans_oper_descend_condV_vc
    (M : PS) (n : ℕ) (hST : STPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hcond : transCondV M = true) :
    lessBT (Trans (oper M n)) (Trans M) = true :=
  Trans_oper_descend_condV admForms_vc c1_shape_holds condV_setup_holds
    t2_nonzero_condV_holds nf3x_vc fseq_condV_holds M n hST hmono hn hcond

#print axioms Trans_oper_exchange_condV_adm_uncond_vc
#print axioms Trans_oper_exchange_condV_nonadm_uncond_vc
#print axioms Trans_oper_exchange_condV_vc
#print axioms exchV_holds_vc
#print axioms Trans_oper_descend_condV_vc

end PSS
