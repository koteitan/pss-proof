theory Support_7_005
  imports Frontier_7_007
begin

\<comment> \<open>\<open>Lng (PB \<dots>)\<close> is preserved by spineSub (only the last component's argument changes).\<close>
lemma rnsub_Lng_spineSub:
  "t0 \<noteq> Trm [] \<Longrightarrow> Lng (PB (spineSub t0 t)) = Lng (PB t0)"
proof -
  assume "t0 \<noteq> Trm []"
  then obtain xs where t0xs: "t0 = Trm xs" and ne: "xs \<noteq> []" by (cases t0) auto
  have "Lng (PB (spineSub (Trm xs) t)) = length (untrm (spineSub (Trm xs) t))"
    by (simp add: rnsub_Lng_PB)
  also have "\<dots> = length xs" using rnsub_spineSub_len[OF ne] by simp
  also have "\<dots> = Lng (PB (Trm xs))" by (simp add: rnsub_Lng_PB)
  finally show ?thesis using t0xs by simp
qed

end
