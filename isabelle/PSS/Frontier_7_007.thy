theory Frontier_7_007
  imports Support_7_004
begin

\<comment> \<open>RightNodes of spineSub: appends RightNodes t at the bottom.\<close>
lemma rnsub_RightNodes_spineSub:
  "t0 \<noteq> Trm [] \<Longrightarrow> RightNodes (spineSub t0 t) = RightNodes t0 @ RightNodes t"
proof (induction t0 t rule: spineSub.induct)
  case (1 xs t)
  show ?case
  proof (cases xs)
    case Nil thus ?thesis using 1 by simp
  next
    case (Cons y ys)
    hence ne: "xs \<noteq> []" by simp
    obtain u a where la: "last xs = DB u a" by (cases "last xs")
    show ?thesis
    proof (cases "a = Trm []")
      case True
      have "spineSub (Trm xs) t = Trm (butlast xs @ [DB u t])"
        using ne la True by (auto split: list.split)
      moreover have "RightNodes (Trm (butlast xs @ [DB u t]))
                   = the_enat u # RightNodes t"
        by (subst rnsub_RightNodes_last) auto
      moreover have "RightNodes (Trm xs) = the_enat u # RightNodes a"
        using ne la by (cases xs) auto
      ultimately show ?thesis using True by simp
    next
      case False
      have eq: "spineSub (Trm xs) t = Trm (butlast xs @ [DB u (spineSub a t)])"
        using ne la False by (auto split: list.split)
      have IH: "RightNodes (spineSub a t) = RightNodes a @ RightNodes t"
        using "1.IH"[of "hd xs" "tl xs" u a] ne la False Cons by simp
      have "RightNodes (Trm (butlast xs @ [DB u (spineSub a t)]))
          = the_enat u # RightNodes (spineSub a t)"
        by (subst rnsub_RightNodes_last) auto
      moreover have "RightNodes (Trm xs) = the_enat u # RightNodes a"
        using ne la by (cases xs) auto
      ultimately show ?thesis using eq IH by simp
    qed
  qed
qed

text \<open>
  Main structural lemma (the article's induction on \<open>Lng(s)\<close>, recast as strong
  induction on \<open>length s\<close>): if \<open>flatBT t\<^sub>0 = s \<frown> D\<^sub>v 0 \<frown> b\<close> with \<open>b\<close> all-\<open>)\<close> and
  \<open>t\<^sub>0,t \<in> T\<^bsub>B\<^esub>\<close>, then \<open>spineSub t\<^sub>0 t\<close> witnesses \<open>flatBT = s \<frown> D\<^sub>v t \<frown> b\<close> and stays
  in \<open>T\<^bsub>B\<^esub>\<close>.  (No use of the unproven scb propositions; purely \<^typ>\<open>BT\<close>-structural.)
\<close>

lemma rnsub_flat_main:
  fixes v :: nat
  shows "\<And>t0 s b. flatBT t0 = s @ Dsym (enat v) # Zsym # b \<Longrightarrow>
            (\<forall>x \<in> set b. x = RP) \<Longrightarrow> t0 \<in> T_B \<Longrightarrow> t \<in> T_B \<Longrightarrow>
            flatBT (spineSub t0 t) = s @ Dsym (enat v) # flatBT t @ b
              \<and> spineSub t0 t \<in> T_B"
proof -
  fix t0 s b
  show "flatBT t0 = s @ Dsym (enat v) # Zsym # b \<Longrightarrow>
        (\<forall>x \<in> set b. x = RP) \<Longrightarrow> t0 \<in> T_B \<Longrightarrow> t \<in> T_B \<Longrightarrow>
        flatBT (spineSub t0 t) = s @ Dsym (enat v) # flatBT t @ b
          \<and> spineSub t0 t \<in> T_B"
  proof (induction "length s" arbitrary: t0 s b rule: less_induct)
    case less
    \<comment> \<open>\<open>t0 = Trm xs\<close> with \<open>xs \<noteq> []\<close> (else flat = [Zsym], no \<open>Dsym\<close>).\<close>
    obtain xs where t0xs: "t0 = Trm xs" by (cases t0)
    have xs_ne: "xs \<noteq> []"
    proof
      assume "xs = []"
      hence "flatBT t0 = [Zsym]" using t0xs by simp
      thus False using less.prems(1) by (cases s) auto
    qed
    obtain u a where la: "last xs = DB u a" by (cases "last xs")
    \<comment> \<open>uniform pre/post decomposition\<close>
    obtain pre post where
      post_RP: "\<forall>x \<in> set post. x = RP" and
      PP: "flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post" and
      PPc: "\<And>c. flatBT (Trm (butlast xs @ [DB u c])) = pre @ (Dsym u # flatBT c) @ post"
      using rnsub_flat_pre_post[OF xs_ne la] by blast
    have Hflat: "flatBT (Trm xs) = (s @ [Dsym (enat v)]) @ Zsym # b"
      using less.prems(1) t0xs by simp
    have no_Z_b: "Zsym \<notin> set b" using less.prems(2) by auto
    have no_Z_post: "Zsym \<notin> set post" using post_RP by auto
    \<comment> \<open>\<open>u \<noteq> \<infinity>\<close>, \<open>a \<in> T_B\<close> from \<open>t0 \<in> T_B\<close>\<close>
    have uinf: "u \<noteq> \<infinity>" and aTB: "a \<in> T_B"
      using rnsub_TB_last[OF less.prems(3)[unfolded t0xs] xs_ne la] by auto
    show ?case
    proof (cases "a = Trm []")
      case True
      \<comment> \<open>bottom reached: \<open>flatBT a = [Zsym]\<close>; align \<open>(s,b)\<close> with \<open>(pre,post)\<close>.\<close>
      have PPb: "flatBT (Trm xs) = (pre @ [Dsym u]) @ Zsym # post"
        using PP True by simp
      have al: "s @ [Dsym (enat v)] = pre @ [Dsym u] \<and> b = post"
        using rnsub_align_lastZ[of "s @ [Dsym (enat v)]" b "pre @ [Dsym u]" post]
              Hflat PPb no_Z_b no_Z_post by simp
      have s_pre: "s = pre" and uv: "Dsym u = Dsym (enat v)"
        using al by auto
      have ueq: "u = enat v" using uv by simp
      have b_post: "b = post" using al by simp
      \<comment> \<open>witness: replace the \<open>0\<close> by \<open>t\<close>\<close>
      have ss: "spineSub (Trm xs) t = Trm (butlast xs @ [DB u t])"
        using xs_ne la True by (auto split: list.split)
      have flat_eq: "flatBT (spineSub (Trm xs) t)
                   = s @ Dsym (enat v) # flatBT t @ b"
        using ss PPc[of t] s_pre ueq b_post by simp
      have mem: "spineSub (Trm xs) t \<in> T_B"
        using ss rnsub_TB_replace_last[OF less.prems(3)[unfolded t0xs] xs_ne uinf less.prems(4)]
        by simp
      show ?thesis using flat_eq mem t0xs by simp
    next
      case False
      \<comment> \<open>recurse into \<open>a\<close>: split \<open>flatBT a\<close> at its last \<open>Zsym\<close>.\<close>
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
      \<comment> \<open>\<open>fpre \<noteq> []\<close> (else \<open>flatBT a\<close> starts with \<open>Zsym\<close>, forcing \<open>a = 0\<close>)\<close>
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
      \<comment> \<open>inner decomposition for the IH\<close>
      have fa_dec: "flatBT a = fpre' @ Dsym (enat v) # Zsym # fpost"
        using fa fpre' by simp
      have fpost_RP: "\<forall>x \<in> set fpost. x = RP"
        using al less.prems(2) by (metis Un_iff set_append)
      have len_lt: "length fpre' < length s"
        using s_eq by simp
      have IH: "flatBT (spineSub a t) = fpre' @ Dsym (enat v) # flatBT t @ fpost
              \<and> spineSub a t \<in> T_B"
        using less.hyps[OF len_lt fa_dec fpost_RP aTB less.prems(4)] by blast
      \<comment> \<open>assemble\<close>
      have ss: "spineSub (Trm xs) t = Trm (butlast xs @ [DB u (spineSub a t)])"
        using xs_ne la False by (auto split: list.split)
      have flat_eq: "flatBT (spineSub (Trm xs) t)
                   = s @ Dsym (enat v) # flatBT t @ b"
      proof -
        have "flatBT (spineSub (Trm xs) t)
            = pre @ Dsym u # flatBT (spineSub a t) @ post"
          using ss PPc[of "spineSub a t"] by simp
        also have "\<dots> = pre @ Dsym u # (fpre' @ Dsym (enat v) # flatBT t @ fpost) @ post"
          using IH by simp
        also have "\<dots> = (pre @ Dsym u # fpre') @ Dsym (enat v) # flatBT t @ (fpost @ post)"
          by simp
        also have "\<dots> = s @ Dsym (enat v) # flatBT t @ b"
          using s_eq al by simp
        finally show ?thesis .
      qed
      have mem: "spineSub (Trm xs) t \<in> T_B"
        using ss IH rnsub_TB_replace_last[OF less.prems(3)[unfolded t0xs] xs_ne uinf]
        by simp
      show ?thesis using flat_eq mem t0xs by simp
    qed
  qed
qed

end
