import «7».«7.3-Trans-welldefined»
import «Buchholz-1987».«Buchholz-1987-2.3-W»

/-!
# §7.1 — `Trans` の像と Buchholz (1987) の `W` 階層の橋

文献固有の `W` 構成と、記事固有の翻訳写像 `Trans` を結ぶ二補題。
旧 `7.1-buchholz-wf-W` に混在していたが、文献別ディレクトリを記事側へ
逆依存させないため、ここに分離する。
-/

namespace PSS

/-- `Trans` の像は `D_ω`-free（`m_7_3_Trans_in_T_B` により `T_B` に属する）。
    Isabelle: `y3_Trans_dfree` (pss_scratch.thy:11390)。 -/
theorem y3_Trans_dfree {M : PS} (MR : RTPS M) : dfree_BT (Trans M) = true :=
  Trans_mem_T_B M MR

/-- Isabelle: `y3_Trans_W` (pss_scratch.thy:11395)。 -/
theorem y3_Trans_W (Hprin : Bwl28Principal) (Hadd : Bwl24bAdd) {M : PS} (MR : RTPS M) :
    ∃ m : ℕ, Trans M ∈ bwl_W m :=
  y3_dfree_W_ex Hprin Hadd (y3_Trans_dfree MR)

#print axioms y3_Trans_dfree
#print axioms y3_Trans_W

end PSS
