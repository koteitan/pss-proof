theory Frontier_7_008
  imports Support_7_005
begin

\<comment> \<open>The rightmost-spine bottom index of \<open>t\<^sub>0\<close> is \<open>v\<close>: \<open>RightNodes t\<^sub>0\<close> ends in \<open>[v]\<close>.
   Same strong induction on \<open>length s\<close> as the flat lemma, tracking only the bottom.\<close>
lemma rnsub_RightNodes_t0_lastv:
  fixes v :: nat
  shows "\<And>t0 s b. flatBT t0 = s @ Dsym (enat v) # Zsym # b \<Longrightarrow>
            (\<forall>x \<in> set b. x = RP) \<Longrightarrow> t0 \<in> T_B \<Longrightarrow>
            \<exists>a0. RightNodes t0 = a0 @ [v]"
proof -
  fix t0 s b
  show "flatBT t0 = s @ Dsym (enat v) # Zsym # b \<Longrightarrow>
        (\<forall>x \<in> set b. x = RP) \<Longrightarrow> t0 \<in> T_B \<Longrightarrow>
        \<exists>a0. RightNodes t0 = a0 @ [v]"
  proof (induction "length s" arbitrary: t0 s b rule: less_induct)
    case less
    obtain xs where t0xs: "t0 = Trm xs" by (cases t0)
    have xs_ne: "xs \<noteq> []"
    proof
      assume "xs = []"
      hence "flatBT t0 = [Zsym]" using t0xs by simp
      thus False using less.prems(1) by (cases s) auto
    qed
    obtain u a where la: "last xs = DB u a" by (cases "last xs")
    obtain pre post where
      post_RP: "\<forall>x \<in> set post. x = RP" and
      PP: "flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post"
      using rnsub_flat_pre_post[OF xs_ne la] by blast
    have Hflat: "flatBT (Trm xs) = (s @ [Dsym (enat v)]) @ Zsym # b"
      using less.prems(1) t0xs by simp
    have no_Z_b: "Zsym \<notin> set b" using less.prems(2) by auto
    have no_Z_post: "Zsym \<notin> set post" using post_RP by auto
    have aTB: "a \<in> T_B"
      using rnsub_TB_last[OF less.prems(3)[unfolded t0xs] xs_ne la] by auto
    have rn_xs: "RightNodes (Trm xs) = the_enat u # RightNodes a"
      using xs_ne la by (cases xs) auto
    show ?case
    proof (cases "a = Trm []")
      case True
      have PPb: "flatBT (Trm xs) = (pre @ [Dsym u]) @ Zsym # post"
        using PP True by simp
      have al: "s @ [Dsym (enat v)] = pre @ [Dsym u] \<and> b = post"
        using rnsub_align_lastZ[of "s @ [Dsym (enat v)]" b "pre @ [Dsym u]" post]
              Hflat PPb no_Z_b no_Z_post by simp
      have "Dsym u = Dsym (enat v)" using al by auto
      hence "u = enat v" by simp
      hence "RightNodes (Trm xs) = [v]" using rn_xs True by simp
      thus ?thesis using t0xs by (intro exI[of _ "[]"]) simp
    next
      case False
      have "Zsym \<in> set (flatBT a)" by (rule rnsub_Zsym_in_flat)
      then obtain fpre fpost where
        fa: "flatBT a = fpre @ Zsym # fpost" and no_Z_fpost: "Zsym \<notin> set fpost"
        by (meson split_list_last)
      have PP2: "flatBT (Trm xs) = (pre @ Dsym u # fpre) @ Zsym # (fpost @ post)"
        using PP fa by simp
      have no_Z_fp: "Zsym \<notin> set (fpost @ post)"
        using no_Z_fpost no_Z_post by simp
      have al: "s @ [Dsym (enat v)] = pre @ Dsym u # fpre \<and> b = fpost @ post"
        using rnsub_align_lastZ[of "s @ [Dsym (enat v)]" b "pre @ Dsym u # fpre" "fpost @ post"]
              Hflat PP2 no_Z_b no_Z_fp by simp
      have fpre_ne: "fpre \<noteq> []"
      proof
        assume "fpre = []"
        hence "flatBT a = Zsym # fpost" using fa by simp
        thus False using rnsub_flat_hd False by blast
      qed
      then obtain fpre' where fpre': "fpre = fpre' @ [Dsym (enat v)]"
                          and s_eq: "s = pre @ Dsym u # fpre'"
        using al by (metis append_eq_append_conv2 append_butlast_last_id
                     last_snoc butlast_snoc append.assoc append_Cons append_Nil2)
      have fa_dec: "flatBT a = fpre' @ Dsym (enat v) # Zsym # fpost"
        using fa fpre' by simp
      have fpost_RP: "\<forall>x \<in> set fpost. x = RP"
        using al less.prems(2) by (metis Un_iff set_append)
      have len_lt: "length fpre' < length s" using s_eq by simp
      have IH: "\<exists>a0. RightNodes a = a0 @ [v]"
        using less.hyps[OF len_lt fa_dec fpost_RP aTB] by blast
      then obtain a0 where "RightNodes a = a0 @ [v]" by blast
      hence "RightNodes (Trm xs) = (the_enat u # a0) @ [v]" using rn_xs by simp
      thus ?thesis using t0xs by blast
    qed
  qed
qed

end
