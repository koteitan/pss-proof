theory Frontier_7_049
  imports Support_7_042
begin

section \<open>§7.2 p_7_2_scb_fseq conjunct (1-2): lifting operB through an scb-decomp\<close>

text \<open>The body \<open>BODY = t\<^sub>0 + D\<^sub>v(t\<^sub>1 + D\<^sub>0 0)\<close> of the marked principal has
  \<open>domB BODY = NatSet\<close>: its last principal is \<open>D\<^sub>v(t\<^sub>1 + D\<^sub>0 0)\<close>, whose body
  \<open>t\<^sub>1 + D\<^sub>0 0\<close> ends in \<open>D\<^sub>0 0\<close> (so \<open>domB = {0}\<close>), giving \<open>domB(D\<^sub>v \<dots>) = NatSet\<close>;
  \<open>domB\<close> reads only the last component.\<close>

lemma domB_succ_inner_NatSet:
  "domB (Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)) = NatSet"
proof -
  let ?b = "t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B"
  have ends: "endsD00 ?b" by (rule endsD00_addD00)
  have bne: "?b \<noteq> Trm []" by (cases t\<^sub>1) simp
  have db0: "domB ?b = {Trm []}" by (rule domB_endsD00[OF ends])
  show ?thesis
    by (subst domB_unfold)
       (simp add: bne db0 Let_def NatSet_neq_zero NatSet_neq_TBv)
qed

lemma succ_body_ne: "t\<^sub>0 +\<^sub>B Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B) \<noteq> Trm []"
  by (cases t\<^sub>0) simp

lemma domB_succ_body_NatSet:
  "domB (t\<^sub>0 +\<^sub>B Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)) = NatSet"
proof -
  let ?single = "Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)"
  obtain xs where x0: "t\<^sub>0 = Trm xs" by (cases t\<^sub>0)
  have body: "t\<^sub>0 +\<^sub>B ?single = Trm (xs @ [DB (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)])"
    using x0 by simp
  have ne: "xs @ [DB (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)] \<noteq> []" by simp
  have "domB (t\<^sub>0 +\<^sub>B ?single)
          = domB (Trm [last (xs @ [DB (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)])])"
    unfolding body by (rule domB_last_component[OF ne])
  also have "\<dots> = domB ?single" by simp
  also have "\<dots> = NatSet" by (rule domB_succ_inner_NatSet)
  finally show ?thesis .
qed

lemma d0succ_succ_inner: "d0succ (Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B))"
proof -
  let ?b = "t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B"
  have bne: "?b \<noteq> Trm []" by (cases t\<^sub>1) simp
  have ends: "endsD00 ?b" by (rule endsD00_addD00)
  have ds_b: "d0succ ?b" by (rule d0succ_addD00)
  show ?thesis by (rule d0succ_single_nonzero[OF bne ends ds_b])
qed

lemma d0succ_succ_body: "d0succ (t\<^sub>0 +\<^sub>B Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B))"
proof -
  obtain xs where x0: "t\<^sub>0 = Trm xs" by (cases t\<^sub>0)
  have lst: "last (xs @ [DB (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)]) = DB (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)"
    by simp
  have ds_single: "d0succ (Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B))" by (rule d0succ_succ_inner)
  hence "d0succ (Trm [last (xs @ [DB (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)])])" using lst by simp
  hence "d0succ (Trm (xs @ [DB (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)]))"
    by (simp add: d0succ_def)
  thus ?thesis using x0 by simp
qed

text \<open>The marked principal \<open>c\<^sub>0 = D\<^sub>u BODY\<close> is \<open>d0succ\<close> with \<open>domB = NatSet\<close>.\<close>

text \<open>The marked principal \<open>c\<^sub>0 = D\<^sub>u BODY\<close> is NOT \<open>d0succ\<close> (its body ends in
  \<open>D\<^sub>v(\<dots>)\<close>, not \<open>D\<^sub>0 0\<close>), so \<open>operB_d0succ_unfold\<close> does not apply.  But
  \<open>domB BODY = NatSet\<close> and \<open>operB BODY z\<close> is defined (conjunct (1)), so the single
  \<open>D\<^sub>u\<close>-step is in \<open>operB\<close>'s domain: we extend the domain one principal up over a
  body whose \<open>operB\<close> is already defined and whose \<open>domB = NatSet\<close>.  The taken
  branch is the \<open>else\<close> (\<open>db = NatSet \<noteq> {0}, \<noteq> T\<^sub>u\<close>), giving \<open>D\<^sub>u(operB b z)\<close>.\<close>

lemma operB_dom_NatSet_principal:
  assumes db: "domB b = NatSet" and bne: "b \<noteq> Trm []"
    and domb: "domB_operB_xseq_dom (Inr (Inl (b, z)))"
  shows "domB_operB_xseq_dom (Inr (Inl (Trm [DB v b], z)))"
proof (rule domB_operB_xseq.domintros(2))
  \<comment> \<open>(0) \<open>domB b\<close> total\<close>
  show "domB_operB_xseq_dom (Inl x2)"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
    by (rule domB_dom_all)
next
  \<comment> \<open>(1) \<open>db = {0}\<close> branch: vacuous (\<open>domB b = NatSet \<noteq> {0}\<close>)\<close>
  show "domB_operB_xseq_dom (Inr (Inl (x2, Trm [])))"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "{Trm []} = domB x2" for x1 x2
  proof -
    have "x2 = b" using that(1) by simp
    hence "{Trm []} = NatSet" using that(3) db by simp
    thus ?thesis using NatSet_neq_zero by simp
  qed
next
  \<comment> \<open>(2) \<open>xseq\<close>-guard: \<open>db = T\<^sub>u\<close> vacuous (\<open>NatSet \<noteq> T\<^sub>u\<close>)\<close>
  show "xb = Trm []"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
       "domB x2 = TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inr (x2, enat (tbvIdx (TBv (enat u))), numNat z)))"
       "xb \<in> TBv (enat u)" for x1 x2 u xb
  proof -
    have "x2 = b" using that(1) by simp
    hence "NatSet = TBv (enat u)" using that(4) db by simp
    thus ?thesis using NatSet_neq_TBv by simp
  qed
next
  \<comment> \<open>(3) \<open>0 \<in> T\<^sub>u\<close>\<close>
  show "Trm [] \<in> TBv (enat u)"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
       "domB x2 = TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inr (x2, enat (tbvIdx (TBv (enat u))), numNat z)))"
       for x1 x2 u
    by (simp add: TBv_def)
next
  \<comment> \<open>(4) inner \<open>xseq\<close> guard: vacuous\<close>
  show "xb = Trm []"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
       "domB x2 = TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u)))) (numNat z))))"
       "xb \<in> TBv (enat u)" for x1 x2 u xb
  proof -
    have "x2 = b" using that(1) by simp
    hence "NatSet = TBv (enat u)" using that(4) db by simp
    thus ?thesis using NatSet_neq_TBv by simp
  qed
next
  \<comment> \<open>(5) \<open>0 \<in> T\<^sub>u\<close> again\<close>
  show "Trm [] \<in> TBv (enat u)"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
       "domB x2 = TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u)))) (numNat z))))"
       for x1 x2 u
    by (simp add: TBv_def)
next
  \<comment> \<open>(6) \<open>else\<close>-branch guard side-condition: under \<open>\<not> dom(operB b z)\<close>, every
     \<open>xb \<in> domB b\<close> is \<open>0\<close>.  But \<open>dom(operB b z)\<close> HOLDS (\<open>domb\<close>), so the hypothesis
     \<open>\<not> dom\<close> is false and the premise is vacuous.\<close>
  show "xb = Trm []"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
       "\<forall>u. x1 \<le> enat u \<longrightarrow> domB x2 \<noteq> TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))"
       "xb \<in> domB x2" for x1 x2 xb
  proof -
    have "x2 = b" using that(1) by simp
    hence "\<not> domB_operB_xseq_dom (Inr (Inl (b, z)))" using that(4) by simp
    thus ?thesis using domb by simp
  qed
next
  \<comment> \<open>(7) \<open>0 \<in> domB b\<close> else-guard: same, vacuous via \<open>domb\<close>\<close>
  show "Trm [] \<in> domB x2"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
       "\<forall>u. x1 \<le> enat u \<longrightarrow> domB x2 \<noteq> TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))" for x1 x2
  proof -
    have "x2 = b" using that(1) by simp
    hence "\<not> domB_operB_xseq_dom (Inr (Inl (b, z)))" using that(4) by simp
    thus ?thesis using domb by simp
  qed
next
  \<comment> \<open>(8) two-component multi: vacuous (\<open>a\<close> is single)\<close>
  show "domB_operB_xseq_dom (Inr (Inl (Trm [x21a], z)))"
    if "Trm [DB v b] = Trm [DB x1 x2, x21a]" for x1 x2 x21a
    using that by simp
next
  \<comment> \<open>(9) \<open>(\<ge>3)\<close>-component multi: vacuous (\<open>a\<close> is single)\<close>
  show "domB_operB_xseq_dom (Inr (Inl (Trm [last x22a], z)))"
    if "Trm [DB v b] = Trm (DB x1 x2 # x21a # x22a)" "x22a \<noteq> []" for x1 x2 x21a x22a
    using that(1) by simp
qed

text \<open>\<open>operB\<close> on a single principal over a \<open>NatSet\<close> body with defined \<open>operB\<close>:
  the \<open>else\<close> branch, \<open>operB (D\<^sub>v b) z = D\<^sub>v(operB b z)\<close>.\<close>

lemma operB_NatSet_principal_unfold:
  assumes db: "domB b = NatSet" and bne: "b \<noteq> Trm []"
    and domb: "domB_operB_xseq_dom (Inr (Inl (b, z)))"
  shows "operB (Trm [DB v b]) z = Dprin v (operB b z)"
proof -
  have dom: "domB_operB_xseq_dom (Inr (Inl (Trm [DB v b], z)))"
    by (rule operB_dom_NatSet_principal[OF db bne domb])
  have "operB (Trm [DB v b]) z
          = (let dbb = domB b in
             if dbb = {Trm []} then multBT (Dprin v (operB b (Trm []))) (numNat z + 1)
             else if (\<exists>u. v \<le> enat u \<and> dbb = TBv (enat u))
                  then Dprin v (operB b (xseq b (enat (tbvIdx dbb)) (numNat z)))
             else Dprin v (operB b z))"
    using operB.psimps[OF dom] bne by simp
  also have "\<dots> = Dprin v (operB b z)"
    using db NatSet_neq_zero NatSet_neq_TBv by (simp add: Let_def)
  finally show ?thesis .
qed

end
