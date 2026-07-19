import «8».«8.2-condIIIV-slice-nat»
import «8».«8.2-condIIIV-geomih»
import «8».«8.2-condIIIV-capstone»
import «8».«8.2-condIIIV-ve2»

/-!
# §8.2 条件(II)/(IV) — **`CondIIIVterminalSlice` 無条件クローズ**（VE34 キャンペーン完結）

- 原文: `tmp/content.md` L3314 付近「命題（条件(II)か(IV)の下での終切片と `Trans` の関係）」。
  訂正: なし。
- 状態: GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  Wave AR〜AV の全部品を合流させる**最終配線ファイル**。新しい数学は無い。

## 配線

1. `tspinAssemblyIH_holds : TspinAssemblyIH_tc`
   — スライス自然性 `tsx_c1_eq_sn`/`tsx_c2_eq_sn`（`8.2-condIIIV-slice-nat`、
   仮定は regime＋STEP guard のみで def の条項より一般）を
   `tspinAssemblyIH_of_slicenat_gi`（`8.2-condIIIV-geomih`）に食わせるだけ。
2. `condIIIVterminalSlice_holds : CondIIIVterminalSlice`
   — `condIIIVterminalSlice_of_assembly_cw`（`8.2-condIIIV-capstone`）に
   1 と `ve2Residual_holds`（`8.2-condIIIV-ve2`）を渡す。

これで `8.7-termination` の残差フィールド `condIIIVts` は本定理で置換可能になる。
-/

namespace PSS

/-- tsx_assembly（Isabelle 104073）の IH-carrying 結論、無条件。 -/
theorem tspinAssemblyIH_holds : TspinAssemblyIH_tc :=
  tspinAssemblyIH_of_slicenat_gi
    (fun N regD hlt _ _ => tsx_c1_eq_sn N regD hlt)
    (fun N regD hlt _ _ => tsx_c2_eq_sn N regD hlt)

/-- **条件(II)/(IV) 終切片命題の核、無条件**（旧 termination 残差フィールド
`condIIIVts` の中身）。 -/
theorem condIIIVterminalSlice_holds : CondIIIVterminalSlice :=
  condIIIVterminalSlice_of_assembly_cw tspinAssemblyIH_holds ve2Residual_holds

#print axioms tspinAssemblyIH_holds
#print axioms condIIIVterminalSlice_holds

end PSS
