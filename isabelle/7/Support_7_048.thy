theory Support_7_048
  imports Frontier_7_052
begin

text \<open>\<open>domB (D\<^sub>u(D\<^sub>v 0)) = NatSet\<close> for \<open>u < v\<close>: \<open>domB(D\<^sub>v 0) = T\<^bsub>v-1\<^esub>\<close> with
  \<open>u \<le> v-1\<close>, so the kind-1 \<open>([].4)(ii)\<close> guard fires the \<open>NatSet\<close> branch.\<close>

lemma domB_Du_Dv0_NatSet:
  assumes uv: "u < v"
  shows "domB (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)) = NatSet"
proof -
  have vpos: "0 < v" using uv by simp
  have db: "domB (Dpt (enat v) 0\<^sub>B) = TBv (enat (v - 1))" by (rule domB_Dw0[OF vpos])
  have bne: "Dpt (enat v) 0\<^sub>B \<noteq> Trm []" by simp
  have nz: "domB (Dpt (enat v) 0\<^sub>B) \<noteq> {Trm []}" using db zero_set_neq_TBv by auto
  have guard: "(\<exists>u'. enat u \<le> enat u' \<and> domB (Dpt (enat v) 0\<^sub>B) = TBv (enat u'))"
  proof (intro exI[of _ "v - 1"] conjI)
    show "enat u \<le> enat (v - 1)" using uv by simp
    show "domB (Dpt (enat v) 0\<^sub>B) = TBv (enat (v - 1))" by (rule db)
  qed
  have "domB (Trm [DB (enat u) (Dpt (enat v) 0\<^sub>B)])
          = (let dbb = domB (Dpt (enat v) 0\<^sub>B) in
             if dbb = {Trm []} then NatSet
             else if (\<exists>u'. enat u \<le> enat u' \<and> dbb = TBv (enat u')) then NatSet
             else dbb)"
    using bne by (subst domB_unfold) simp
  also have "\<dots> = NatSet" using nz guard by (simp add: Let_def)
  finally show ?thesis .
qed

end
