theory Support_7_013
  imports Frontier_7_016
begin

lemma rnsub_RN_of_maximal:
  assumes "flatBP pp = Dsym u # flatBT a"
  shows "RightNodes (Trm [pp]) = the_enat u # RightNodes a"
proof -
  obtain v c where pc: "pp = DB v c" by (cases pp)
  have "Dsym v # flatBT c = Dsym u # flatBT a" using assms pc by simp
  hence vu: "v = u" and fc: "flatBT c = flatBT a" by simp_all
  have "c = a" by (rule m_7_flatBT_inj[OF fc])
  thus ?thesis using pc vu by simp
qed

\<comment> \<open>CUT-PINNING.  Any scb occurrence's cut reaches the canonical last principal:
   there is a canonical split \<open>flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post\<close>
   (\<open>post\<close> all-\<open>)\<close>, \<open>last xs = DB u a\<close>) with \<open>length pre \<le> length s\<close>.\<close>
lemma rnsub_cut_ge_pre:
  assumes xsne: "xs \<noteq> []"
      and lst: "last xs = DB u a"
  shows "\<exists>pre post. (\<forall>x \<in> set post. x = RP)
            \<and> flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post
            \<and> (\<forall>s pp b. flatBT (Trm xs) = s @ flatBP pp @ b \<longrightarrow> (\<forall>x \<in> set b. x = RP)
                         \<longrightarrow> length pre \<le> length s)"
proof (cases xs rule: rev_cases)
  case Nil thus ?thesis using xsne by simp
next
  case (snoc ys y)
  have y_eq: "y = DB u a" using lst snoc by simp
  show ?thesis
  proof (cases ys)
    case Nil
    \<comment> \<open>single principal: \<open>pre = post = []\<close>; the bound \<open>0 \<le> length s\<close> is trivial.\<close>
    have fl: "flatBT (Trm xs) = [] @ (Dsym u # flatBT a) @ []"
      using snoc Nil y_eq by simp
    show ?thesis
      by (rule exI[of _ "[]"], rule exI[of _ "[]"]) (use fl in simp)
  next
    case (Cons p ps)
    define run where "run = concat (map (\<lambda>r. flatBP r @ [CM]) (p # ps))"
    define pre where "pre = LP # run"
    define post where "post = [RP]"
    have xs_eq: "xs = p # (ps @ [DB u a])" using snoc Cons y_eq by simp
    have flat_xs: "flatBT (Trm xs)
                  = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB u a]))) @ [RP]"
      unfolding xs_eq by (rule rnsub_flat_multi) simp
    \<comment> \<open>Reassociate the leading-component run \<open>flatBP p \<frown> CM-prefixed-rest\<close> into the
       \<open>flatBP r \<frown> [CM]\<close> form plus the final principal.\<close>
    have concat_eq: "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB u a]))
                    = run @ Dsym u # flatBT a"
    proof -
      have "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB u a]))
            = flatBP p @ (concat (map (\<lambda>r. CM # flatBP r) ps) @ [CM]) @ (Dsym u # flatBT a)"
        by simp
      also have "\<dots> = flatBP p @ (CM # concat (map (\<lambda>r. flatBP r @ [CM]) ps))
                        @ (Dsym u # flatBT a)"
        using flat_CM_shift[of ps] by simp
      also have "\<dots> = run @ Dsym u # flatBT a"
        unfolding run_def by simp
      finally show ?thesis .
    qed
    have flat2: "flatBT (Trm xs) = LP # (run @ Dsym u # flatBT a) @ [RP]"
      using flat_xs concat_eq by simp
    have flat_split: "flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post"
      using flat2 unfolding pre_def post_def by simp
    have postRP: "\<forall>x \<in> set post. x = RP" unfolding post_def by simp
    \<comment> \<open>The universal bound: any occurrence's cut reaches past \<open>pre\<close> via the peel.\<close>
    have bound: "\<And>s pp b. flatBT (Trm xs) = s @ flatBP pp @ b \<Longrightarrow> (\<forall>x \<in> set b. x = RP)
                            \<Longrightarrow> length pre \<le> length s"
    proof -
      fix s pp b
      assume occ: "flatBT (Trm xs) = s @ flatBP pp @ b" and bRP: "\<forall>x \<in> set b. x = RP"
      \<comment> \<open>The marked principal starts with \<open>Dsym\<close>, so \<open>s\<close> begins with the leading \<open>LP\<close>.\<close>
      have sne: "s \<noteq> []"
      proof (rule ccontr)
        assume "\<not> s \<noteq> []"
        hence "s = []" by simp
        hence eqf: "flatBT (Trm xs) = flatBP pp @ b" using occ by simp
        have "hd (flatBT (Trm xs)) = LP" using flat_split unfolding pre_def by simp
        moreover have "hd (flatBT (Trm xs)) = Dsym (case pp of DB v c \<Rightarrow> v)"
          using eqf by (cases pp) simp
        ultimately show False by simp
      qed
      have hdLP: "hd (flatBT (Trm xs)) = LP" using flat_split unfolding pre_def by simp
      have shead: "hd s = LP"
        using occ sne hdLP by (simp add: hd_append)
      define s' where "s' = tl s"
      have ss': "s = LP # s'"
        using sne shead unfolding s'_def by (cases s) auto
      have peeleq: "s' @ flatBP pp @ b = run @ (Dsym u # flatBT a @ [RP])"
      proof -
        have "LP # (s' @ flatBP pp @ b) = LP # (run @ Dsym u # flatBT a @ [RP])"
          using occ ss' flat2 by simp
        thus ?thesis by simp
      qed
      have peeleq2: "s' @ flatBP pp @ b
                    = concat (map (\<lambda>r. flatBP r @ [CM]) (p # ps)) @ (Dsym u # flatBT a @ [RP])"
        using peeleq unfolding run_def by simp
      have lenrun: "length (concat (map (\<lambda>r. flatBP r @ [CM]) (p # ps))) \<le> length s'"
        by (rule rnsub_peel_components[OF peeleq2 bRP])
      have "length pre = 1 + length run"
        unfolding pre_def by simp
      also have "\<dots> = 1 + length (concat (map (\<lambda>r. flatBP r @ [CM]) (p # ps)))"
        unfolding run_def by simp
      also have "\<dots> \<le> 1 + length s'" using lenrun by simp
      also have "\<dots> = length s" using ss' by simp
      finally show "length pre \<le> length s" .
    qed
    show ?thesis
      using postRP flat_split bound by blast
  qed
qed

\<comment> \<open>RIGHTNODES LENGTH BOUND.  An scb occurrence's marked-principal RightNodes is
   no longer than the whole term's RightNodes; maximal iff equal length.\<close>
lemma rnsub_RN_occ_len_le:
  "flatBT (Trm ys) = s @ flatBP pp @ b \<Longrightarrow> (\<forall>x \<in> set b. x = RP)
     \<Longrightarrow> length (RightNodes (Trm [pp])) \<le> length (RightNodes (Trm ys))"
proof (induct "length (flatBT (Trm ys))" arbitrary: ys s pp b rule: less_induct)
  case less
  show ?case
  proof (cases ys)
    case Nil
    \<comment> \<open>\<open>flatBT (Trm []) = [Zsym]\<close>: no room for a principal \<open>flatBP pp\<close> (length \<ge> 2).\<close>
    have "length (flatBP pp) \<le> length (flatBT (Trm ys))"
      using less.prems(1) by simp
    moreover have "2 \<le> length (flatBP pp)" by (rule flatBP_len_ge2)
    ultimately show ?thesis using Nil by simp
  next
    case (Cons y0 ys0)
    hence ysne: "ys \<noteq> []" by simp
    obtain u a where lst: "last ys = DB u a" by (cases "last ys") simp
    obtain up ap where ppc: "pp = DB up ap" by (cases pp)
    have occ: "flatBT (Trm ys) = s @ flatBP (DB up ap) @ b"
      using less.prems(1) ppc by simp
    obtain pre post where
      postRP: "\<forall>x \<in> set post. x = RP"
      and PP: "flatBT (Trm ys) = pre @ (Dsym u # flatBT a) @ post"
      and bnd: "\<forall>s pp b. flatBT (Trm ys) = s @ flatBP pp @ b \<longrightarrow> (\<forall>x \<in> set b. x = RP)
                            \<longrightarrow> length pre \<le> length s"
      using rnsub_cut_ge_pre[OF ysne lst] by blast
    have gepre: "length pre \<le> length s"
      using bnd less.prems(1) less.prems(2) by blast
    have dich:
      "(length s = length pre \<and> flatBP pp = Dsym u # flatBT a \<and> b = post)
       \<or> (length pre < length s
            \<and> (\<exists>s2 b2. flatBT a = s2 @ flatBP pp @ b2
                        \<and> (\<forall>x \<in> set b2. x = RP)
                        \<and> length s = length pre + 1 + length s2))"
      using rnsub_cut_ge_pre_dichotomy[OF occ less.prems(2) PP postRP gepre] ppc by simp
    have RNys: "RightNodes (Trm ys) = the_enat u # RightNodes a"
      using rnsub_RightNodes_cons[of y0 ys0] lst Cons by simp
    show ?thesis
    proof (cases "length s = length pre")
      case True
      have "flatBP pp = Dsym u # flatBT a" using dich True by simp
      hence "RightNodes (Trm [pp]) = the_enat u # RightNodes a"
        by (rule rnsub_RN_of_maximal)
      thus ?thesis using RNys by simp
    next
      case False
      hence ltpre: "length pre < length s" using gepre by simp
      have "\<exists>s2 b2. flatBT a = s2 @ flatBP pp @ b2 \<and> (\<forall>x \<in> set b2. x = RP)
                      \<and> length s = length pre + 1 + length s2"
        using dich ltpre by force
      then obtain s2 b2 where
        a_occ: "flatBT a = s2 @ flatBP pp @ b2" and b2RP: "\<forall>x \<in> set b2. x = RP"
        by blast
      obtain zs where azs: "a = Trm zs" by (cases a)
      have meas: "length (flatBT (Trm zs)) < length (flatBT (Trm ys))"
        using PP azs by simp
      have z_occ: "flatBT (Trm zs) = s2 @ flatBP pp @ b2" using a_occ azs by simp
      have IH: "length (RightNodes (Trm [pp])) \<le> length (RightNodes (Trm zs))"
        by (rule less.hyps[OF meas z_occ b2RP])
      have "length (RightNodes (Trm zs)) \<le> length (RightNodes (Trm ys))"
        using RNys azs by simp
      thus ?thesis using IH azs by simp
    qed
  qed
qed

\<comment> \<open>THE CUT-PIN.  Two scb occurrences of the SAME term whose marked-principal
   RightNodes have equal length share the same cut length.\<close>
lemma rnsub_RN_pins_len:
  "flatBT (Trm ys) = s\<^sub>0 @ flatBP p\<^sub>0 @ b\<^sub>0 \<Longrightarrow> (\<forall>x \<in> set b\<^sub>0. x = RP)
     \<Longrightarrow> flatBT (Trm ys) = s\<^sub>1 @ flatBP p\<^sub>1 @ b\<^sub>1 \<Longrightarrow> (\<forall>x \<in> set b\<^sub>1. x = RP)
     \<Longrightarrow> length (RightNodes (Trm [p\<^sub>0])) = length (RightNodes (Trm [p\<^sub>1]))
     \<Longrightarrow> length s\<^sub>0 = length s\<^sub>1"
proof (induct "length (flatBT (Trm ys))" arbitrary: ys s\<^sub>0 p\<^sub>0 b\<^sub>0 s\<^sub>1 p\<^sub>1 b\<^sub>1 rule: less_induct)
  case less
  show ?case
  proof (cases ys)
    case Nil
    have "length (flatBP p\<^sub>0) \<le> length (flatBT (Trm ys))"
      using less.prems(1) by simp
    moreover have "2 \<le> length (flatBP p\<^sub>0)" by (rule flatBP_len_ge2)
    ultimately show ?thesis using Nil by simp
  next
    case (Cons y0 ys0)
    hence ysne: "ys \<noteq> []" by simp
    obtain u a where lst: "last ys = DB u a" by (cases "last ys") simp
    obtain up0 ap0 where pp0: "p\<^sub>0 = DB up0 ap0" by (cases p\<^sub>0)
    obtain up1 ap1 where pp1: "p\<^sub>1 = DB up1 ap1" by (cases p\<^sub>1)
    have occ0: "flatBT (Trm ys) = s\<^sub>0 @ flatBP (DB up0 ap0) @ b\<^sub>0"
      using less.prems(1) pp0 by simp
    have occ1: "flatBT (Trm ys) = s\<^sub>1 @ flatBP (DB up1 ap1) @ b\<^sub>1"
      using less.prems(3) pp1 by simp
    \<comment> \<open>ONE canonical split (with the universal cut-bound) used for both occurrences.\<close>
    obtain pre post where
      postRP: "\<forall>x \<in> set post. x = RP"
      and PP: "flatBT (Trm ys) = pre @ (Dsym u # flatBT a) @ post"
      and bnd: "\<forall>s pp b. flatBT (Trm ys) = s @ flatBP pp @ b \<longrightarrow> (\<forall>x \<in> set b. x = RP)
                            \<longrightarrow> length pre \<le> length s"
      using rnsub_cut_ge_pre[OF ysne lst] by blast
    have gepre0: "length pre \<le> length s\<^sub>0"
      using bnd less.prems(1) less.prems(2) by blast
    have gepre1': "length pre \<le> length s\<^sub>1"
      using bnd less.prems(3) less.prems(4) by blast
    have dich0:
      "(length s\<^sub>0 = length pre \<and> flatBP p\<^sub>0 = Dsym u # flatBT a \<and> b\<^sub>0 = post)
       \<or> (length pre < length s\<^sub>0
            \<and> (\<exists>s2 b2. flatBT a = s2 @ flatBP p\<^sub>0 @ b2
                        \<and> (\<forall>x \<in> set b2. x = RP)
                        \<and> length s\<^sub>0 = length pre + 1 + length s2))"
      using rnsub_cut_ge_pre_dichotomy[OF occ0 less.prems(2) PP postRP gepre0] pp0 by simp
    have dich1:
      "(length s\<^sub>1 = length pre \<and> flatBP p\<^sub>1 = Dsym u # flatBT a \<and> b\<^sub>1 = post)
       \<or> (length pre < length s\<^sub>1
            \<and> (\<exists>s2 b2. flatBT a = s2 @ flatBP p\<^sub>1 @ b2
                        \<and> (\<forall>x \<in> set b2. x = RP)
                        \<and> length s\<^sub>1 = length pre + 1 + length s2))"
      using rnsub_cut_ge_pre_dichotomy[OF occ1 less.prems(4) PP postRP gepre1'] pp1 by simp
    have RNa1: "length (RightNodes (Trm [DB u a])) = 1 + length (RightNodes a)"
      by simp
    show ?thesis
    proof (cases "length s\<^sub>0 = length pre")
      case True \<comment> \<open>occ 0 maximal\<close>
      have m0: "flatBP p\<^sub>0 = Dsym u # flatBT a" using dich0 True by simp
      have rn0: "length (RightNodes (Trm [p\<^sub>0])) = 1 + length (RightNodes a)"
        using rnsub_RN_of_maximal[OF m0] by simp
      \<comment> \<open>occ 1 must also be maximal (else its RN length \<le> length(RN a) < rn0).\<close>
      have "length s\<^sub>1 = length pre"
      proof (rule ccontr)
        assume ne1: "length s\<^sub>1 \<noteq> length pre"
        hence ltp: "length pre < length s\<^sub>1" using gepre1' by simp
        have "\<exists>s2 b2. flatBT a = s2 @ flatBP p\<^sub>1 @ b2 \<and> (\<forall>x \<in> set b2. x = RP)
                        \<and> length s\<^sub>1 = length pre + 1 + length s2"
          using dich1 ltp by force
        then obtain s2 b2 where
          a_occ: "flatBT a = s2 @ flatBP p\<^sub>1 @ b2" and b2RP: "\<forall>x \<in> set b2. x = RP"
          by blast
        obtain zs where azs: "a = Trm zs" by (cases a)
        have "length (RightNodes (Trm [p\<^sub>1])) \<le> length (RightNodes a)"
          using rnsub_RN_occ_len_le[of zs s2 p\<^sub>1 b2] a_occ b2RP azs by simp
        hence "length (RightNodes (Trm [p\<^sub>1])) < 1 + length (RightNodes a)" by simp
        thus False using less.prems(5) rn0 by simp
      qed
      thus ?thesis using True by simp
    next
      case False \<comment> \<open>occ 0 descends\<close>
      hence lt0: "length pre < length s\<^sub>0" using gepre0 by simp
      have "\<exists>s2 b2. flatBT a = s2 @ flatBP p\<^sub>0 @ b2 \<and> (\<forall>x \<in> set b2. x = RP)
                      \<and> length s\<^sub>0 = length pre + 1 + length s2"
        using dich0 lt0 by force
      then obtain s20 b20 where
        a_occ0: "flatBT a = s20 @ flatBP p\<^sub>0 @ b20" and b20RP: "\<forall>x \<in> set b20. x = RP"
        and len0: "length s\<^sub>0 = length pre + 1 + length s20"
        by blast
      \<comment> \<open>occ 1 must also descend (else occ1 maximal: length(RN p1)=1+len(RN a) but
         occ0 descends \<Rightarrow> length(RN p0) \<le> len(RN a) < that, contradicting equality).\<close>
      have "length s\<^sub>1 \<noteq> length pre"
      proof (rule ccontr)
        assume "\<not> length s\<^sub>1 \<noteq> length pre"
        hence True1: "length s\<^sub>1 = length pre" by simp
        have m1: "flatBP p\<^sub>1 = Dsym u # flatBT a" using dich1 True1 by simp
        have rn1: "length (RightNodes (Trm [p\<^sub>1])) = 1 + length (RightNodes a)"
          using rnsub_RN_of_maximal[OF m1] by simp
        obtain zs where azs: "a = Trm zs" by (cases a)
        have "length (RightNodes (Trm [p\<^sub>0])) \<le> length (RightNodes a)"
          using rnsub_RN_occ_len_le[of zs s20 p\<^sub>0 b20] a_occ0 b20RP azs by simp
        hence "length (RightNodes (Trm [p\<^sub>0])) < 1 + length (RightNodes a)" by simp
        thus False using less.prems(5) rn1 by simp
      qed
      hence lt1: "length pre < length s\<^sub>1" using gepre1' by simp
      have "\<exists>s2 b2. flatBT a = s2 @ flatBP p\<^sub>1 @ b2 \<and> (\<forall>x \<in> set b2. x = RP)
                      \<and> length s\<^sub>1 = length pre + 1 + length s2"
        using dich1 lt1 by force
      then obtain s21 b21 where
        a_occ1: "flatBT a = s21 @ flatBP p\<^sub>1 @ b21" and b21RP: "\<forall>x \<in> set b21. x = RP"
        and len1: "length s\<^sub>1 = length pre + 1 + length s21"
        by blast
      obtain zs where azs: "a = Trm zs" by (cases a)
      have meas: "length (flatBT (Trm zs)) < length (flatBT (Trm ys))"
        using PP azs by simp
      have z_occ0: "flatBT (Trm zs) = s20 @ flatBP p\<^sub>0 @ b20" using a_occ0 azs by simp
      have z_occ1: "flatBT (Trm zs) = s21 @ flatBP p\<^sub>1 @ b21" using a_occ1 azs by simp
      have IH: "length s20 = length s21"
        by (rule less.hyps[OF meas z_occ0 b20RP z_occ1 b21RP less.prems(5)])
      show ?thesis using len0 len1 IH by simp
    qed
  qed
qed

\<comment> \<open>UNCONDITIONAL conjunct (4) of \<open>p_7_2_scb_unique\<close>: the kind-0 pin is derived,
   not assumed.  kind-0 forces \<open>length (RightNodes (Trm [p])) = 2\<close> for both
   decompositions, so @{thm [source] rnsub_RN_pins_len} pins the cut length, and
   @{thm [source] m_7_2_scb_c_unique} + @{thm [source] m_7_2_scb_kind_unique_of_ceq}
   close it.\<close>
lemma m_7_2_scb_kind0_unique_uncond:
  assumes tTB: "t \<in> T_B" and tne: "t \<noteq> Trm []"
      and d0: "scb_kind0 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_kind0 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
  shows "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
proof -
  have sd0: "scb_decomp t s\<^sub>0 c\<^sub>0 b\<^sub>0" using d0 by (simp add: scb_kind0_def)
  have sd1: "scb_decomp t s\<^sub>1 c\<^sub>1 b\<^sub>1" using d1 by (simp add: scb_kind0_def)
  obtain ys where ys: "t = Trm ys" by (cases t)
  \<comment> \<open>Unfold the occurrences and the principal strings.\<close>
  from sd0 have e0: "flatBT t = s\<^sub>0 @ c\<^sub>0 @ b\<^sub>0" and pc0: "isPTB_str c\<^sub>0"
    and b0RP: "\<forall>x \<in> set b\<^sub>0. x = RP"
    using tne by (auto simp: scb_decomp_def)
  from sd1 have e1: "flatBT t = s\<^sub>1 @ c\<^sub>1 @ b\<^sub>1" and pc1: "isPTB_str c\<^sub>1"
    and b1RP: "\<forall>x \<in> set b\<^sub>1. x = RP"
    using tne by (auto simp: scb_decomp_def)
  obtain p\<^sub>0 where p0: "c\<^sub>0 = flatBP p\<^sub>0" using pc0 unfolding isPTB_str_def by blast
  obtain p\<^sub>1 where p1: "c\<^sub>1 = flatBP p\<^sub>1" using pc1 unfolding isPTB_str_def by blast
  \<comment> \<open>kind-0 pins both RightNodes lengths to 2.\<close>
  have k0: "\<forall>p. c\<^sub>0 = flatBP p \<longrightarrow>
        (Lng (RightNodes (Trm [p])) = 2 \<and> RightNodes (Trm [p]) ! 1 = 0)"
    using d0 by (simp add: scb_kind0_def)
  have rn0: "length (RightNodes (Trm [p\<^sub>0])) = 2"
    using k0 p0 by simp
  have k1: "\<forall>p. c\<^sub>1 = flatBP p \<longrightarrow>
        (Lng (RightNodes (Trm [p])) = 2 \<and> RightNodes (Trm [p]) ! 1 = 0)"
    using d1 by (simp add: scb_kind0_def)
  have rn1: "length (RightNodes (Trm [p\<^sub>1])) = 2"
    using k1 p1 by simp
  have rneq: "length (RightNodes (Trm [p\<^sub>0])) = length (RightNodes (Trm [p\<^sub>1]))"
    using rn0 rn1 by simp
  \<comment> \<open>Pin the cut length, then close with the \<open>c\<close>-equality reduction.\<close>
  have occ0: "flatBT (Trm ys) = s\<^sub>0 @ flatBP p\<^sub>0 @ b\<^sub>0" using e0 p0 ys by simp
  have occ1: "flatBT (Trm ys) = s\<^sub>1 @ flatBP p\<^sub>1 @ b\<^sub>1" using e1 p1 ys by simp
  have pin: "length s\<^sub>0 = length s\<^sub>1"
    by (rule rnsub_RN_pins_len[OF occ0 b0RP occ1 b1RP rneq])
  have ceq: "c\<^sub>0 = c\<^sub>1" by (rule m_7_2_scb_c_unique[OF tne sd0 sd1 pin])
  show ?thesis by (rule m_7_2_scb_kind_unique_of_ceq[OF tTB ceq sd0 sd1])
qed

\<comment> \<open>UNCONDITIONAL conjunct (5): kind-1 also pins \<open>length (RightNodes (Trm [p]))\<close>,
   namely \<open>j\<^sub>1 + 1\<close> where \<open>j\<^sub>1 = Lng (RightNodes (Trm [p])) - 1\<close>.  Both kind-1
   decompositions share the SAME \<open>j\<^sub>1\<close>? — only if the suffix length is forced.  We
   pin via the SAME RightNodes suffix: kind-1's \<open>j\<^sub>1 \<ge> 1\<close> plus the shared suffix
   property; here we keep the residual that both have equal RightNodes length.\<close>
lemma m_7_2_scb_kind1_unique_uncond:
  assumes tTB: "t \<in> T_B" and tne: "t \<noteq> Trm []"
      and d0: "scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
      and rneq: "\<And>p\<^sub>0 p\<^sub>1. c\<^sub>0 = flatBP p\<^sub>0 \<Longrightarrow> c\<^sub>1 = flatBP p\<^sub>1
                   \<Longrightarrow> length (RightNodes (Trm [p\<^sub>0])) = length (RightNodes (Trm [p\<^sub>1]))"
  shows "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
proof -
  have sd0: "scb_decomp t s\<^sub>0 c\<^sub>0 b\<^sub>0" using d0 by (simp add: scb_kind1_def)
  have sd1: "scb_decomp t s\<^sub>1 c\<^sub>1 b\<^sub>1" using d1 by (simp add: scb_kind1_def)
  obtain ys where ys: "t = Trm ys" by (cases t)
  from sd0 have e0: "flatBT t = s\<^sub>0 @ c\<^sub>0 @ b\<^sub>0" and pc0: "isPTB_str c\<^sub>0"
    and b0RP: "\<forall>x \<in> set b\<^sub>0. x = RP"
    using tne by (auto simp: scb_decomp_def)
  from sd1 have e1: "flatBT t = s\<^sub>1 @ c\<^sub>1 @ b\<^sub>1" and pc1: "isPTB_str c\<^sub>1"
    and b1RP: "\<forall>x \<in> set b\<^sub>1. x = RP"
    using tne by (auto simp: scb_decomp_def)
  obtain p\<^sub>0 where p0: "c\<^sub>0 = flatBP p\<^sub>0" using pc0 unfolding isPTB_str_def by blast
  obtain p\<^sub>1 where p1: "c\<^sub>1 = flatBP p\<^sub>1" using pc1 unfolding isPTB_str_def by blast
  have rneq': "length (RightNodes (Trm [p\<^sub>0])) = length (RightNodes (Trm [p\<^sub>1]))"
    by (rule rneq[OF p0 p1])
  have occ0: "flatBT (Trm ys) = s\<^sub>0 @ flatBP p\<^sub>0 @ b\<^sub>0" using e0 p0 ys by simp
  have occ1: "flatBT (Trm ys) = s\<^sub>1 @ flatBP p\<^sub>1 @ b\<^sub>1" using e1 p1 ys by simp
  have pin: "length s\<^sub>0 = length s\<^sub>1"
    by (rule rnsub_RN_pins_len[OF occ0 b0RP occ1 b1RP rneq'])
  have ceq: "c\<^sub>0 = c\<^sub>1" by (rule m_7_2_scb_c_unique[OF tne sd0 sd1 pin])
  show ?thesis by (rule m_7_2_scb_kind_unique_of_ceq[OF tTB ceq sd0 sd1])
qed



section \<open>§7.2 kind-1 RightNodes length-pin (rnsub_kind1_len_pin)\<close>

text \<open>
  The marked-principal \<open>RightNodes\<close> of an scb occurrence is a SUFFIX
  (\<open>drop k\<close>) of the whole term's \<open>RightNodes\<close> (content.md 1916,
  \<open>RightNodes(c) = (RightNodes(t)_j)_{j=k}^{j_1}\<close>).  Mirrors the descent of
  @{thm [source] rnsub_RN_occ_len_le} but tracks the start index as a \<open>drop\<close>
  witness instead of a length bound.\<close>

lemma rnsub_RN_occ_suffix:
  "flatBT (Trm ys) = s @ flatBP pp @ b \<Longrightarrow> (\<forall>x \<in> set b. x = RP)
     \<Longrightarrow> \<exists>k. RightNodes (Trm [pp]) = drop k (RightNodes (Trm ys))"
proof (induct "length (flatBT (Trm ys))" arbitrary: ys s pp b rule: less_induct)
  case less
  show ?case
  proof (cases ys)
    case Nil
    have "length (flatBP pp) \<le> length (flatBT (Trm ys))"
      using less.prems(1) by simp
    moreover have "2 \<le> length (flatBP pp)" by (rule flatBP_len_ge2)
    ultimately show ?thesis using Nil by simp
  next
    case (Cons y0 ys0)
    hence ysne: "ys \<noteq> []" by simp
    obtain u a where lst: "last ys = DB u a" by (cases "last ys") simp
    obtain up ap where ppc: "pp = DB up ap" by (cases pp)
    have occ: "flatBT (Trm ys) = s @ flatBP (DB up ap) @ b"
      using less.prems(1) ppc by simp
    obtain pre post where
      postRP: "\<forall>x \<in> set post. x = RP"
      and PP: "flatBT (Trm ys) = pre @ (Dsym u # flatBT a) @ post"
      and bnd: "\<forall>s pp b. flatBT (Trm ys) = s @ flatBP pp @ b \<longrightarrow> (\<forall>x \<in> set b. x = RP)
                            \<longrightarrow> length pre \<le> length s"
      using rnsub_cut_ge_pre[OF ysne lst] by blast
    have gepre: "length pre \<le> length s"
      using bnd less.prems(1) less.prems(2) by blast
    have dich:
      "(length s = length pre \<and> flatBP pp = Dsym u # flatBT a \<and> b = post)
       \<or> (length pre < length s
            \<and> (\<exists>s2 b2. flatBT a = s2 @ flatBP pp @ b2
                        \<and> (\<forall>x \<in> set b2. x = RP)
                        \<and> length s = length pre + 1 + length s2))"
      using rnsub_cut_ge_pre_dichotomy[OF occ less.prems(2) PP postRP gepre] ppc by simp
    have RNys: "RightNodes (Trm ys) = the_enat u # RightNodes a"
      using rnsub_RightNodes_cons[of y0 ys0] lst Cons by simp
    show ?thesis
    proof (cases "length s = length pre")
      case True
      have "flatBP pp = Dsym u # flatBT a" using dich True by simp
      hence "RightNodes (Trm [pp]) = the_enat u # RightNodes a"
        by (rule rnsub_RN_of_maximal)
      hence "RightNodes (Trm [pp]) = drop 0 (RightNodes (Trm ys))" using RNys by simp
      thus ?thesis by blast
    next
      case False
      hence ltpre: "length pre < length s" using gepre by simp
      have "\<exists>s2 b2. flatBT a = s2 @ flatBP pp @ b2 \<and> (\<forall>x \<in> set b2. x = RP)
                      \<and> length s = length pre + 1 + length s2"
        using dich ltpre by force
      then obtain s2 b2 where
        a_occ: "flatBT a = s2 @ flatBP pp @ b2" and b2RP: "\<forall>x \<in> set b2. x = RP"
        by blast
      obtain zs where azs: "a = Trm zs" by (cases a)
      have meas: "length (flatBT (Trm zs)) < length (flatBT (Trm ys))"
        using PP azs by simp
      have z_occ: "flatBT (Trm zs) = s2 @ flatBP pp @ b2" using a_occ azs by simp
      obtain k where IH: "RightNodes (Trm [pp]) = drop k (RightNodes (Trm zs))"
        using less.hyps[OF meas z_occ b2RP] by blast
      have "RightNodes (Trm [pp]) = drop (Suc k) (RightNodes (Trm ys))"
        using IH RNys azs by simp
      thus ?thesis by blast
    qed
  qed
qed

text \<open>
  Pure list index-pin: if a list \<open>R\<close> has two suffixes \<open>drop k\<^sub>0 R\<close>,
  \<open>drop k\<^sub>1 R\<close> that each satisfy the kind-1 shape — first element
  \<open>< last element\<close>, interior elements \<open>\<ge> last element\<close>, suffix length \<open>\<ge> 2\<close> —
  then \<open>k\<^sub>0 = k\<^sub>1\<close>.  Both start indices are the LARGEST index \<open>< |R|-1\<close> whose
  value is \<open>< R!(|R|-1)\<close>, hence equal.  (content.md 1916 maximality.)\<close>

lemma rnsub_kind1_drop_index_pin:
  fixes R :: "nat list"
  assumes k0lt: "k\<^sub>0 < length R" and k1lt: "k\<^sub>1 < length R"
      and len0: "2 \<le> length (drop k\<^sub>0 R)" and len1: "2 \<le> length (drop k\<^sub>1 R)"
      and hd0: "(drop k\<^sub>0 R) ! 0 < (drop k\<^sub>0 R) ! (length (drop k\<^sub>0 R) - 1)"
      and int0: "\<forall>j. 0 < j \<and> j < length (drop k\<^sub>0 R) - 1
                    \<longrightarrow> (drop k\<^sub>0 R) ! j \<ge> (drop k\<^sub>0 R) ! (length (drop k\<^sub>0 R) - 1)"
      and hd1: "(drop k\<^sub>1 R) ! 0 < (drop k\<^sub>1 R) ! (length (drop k\<^sub>1 R) - 1)"
      and int1: "\<forall>j. 0 < j \<and> j < length (drop k\<^sub>1 R) - 1
                    \<longrightarrow> (drop k\<^sub>1 R) ! j \<ge> (drop k\<^sub>1 R) ! (length (drop k\<^sub>1 R) - 1)"
  shows "k\<^sub>0 = k\<^sub>1"
proof -
  define L where "L = length R - 1"
  define U where "U = R ! L"
  \<comment> \<open>The last element of every suffix is \<open>R ! L = U\<close>.\<close>
  have last0: "(drop k\<^sub>0 R) ! (length (drop k\<^sub>0 R) - 1) = U"
    using k0lt len0 unfolding U_def L_def by (simp add: nth_drop)
  have last1: "(drop k\<^sub>1 R) ! (length (drop k\<^sub>1 R) - 1) = U"
    using k1lt len1 unfolding U_def L_def by (simp add: nth_drop)
  \<comment> \<open>Both start strictly before the last index \<open>L\<close>, with value \<open>< U\<close>.\<close>
  have k0L: "k\<^sub>0 < L" using len0 unfolding L_def by simp
  have k1L: "k\<^sub>1 < L" using len1 unfolding L_def by simp
  have hd0R: "R ! k\<^sub>0 < U"
    using hd0 last0 k0lt by (simp add: nth_drop)
  have hd1R: "R ! k\<^sub>1 < U"
    using hd1 last1 k1lt by (simp add: nth_drop)
  \<comment> \<open>Interior positions of suffix \<open>i\<close>, translated to absolute indices in \<open>R\<close>,
     have value \<open>\<ge> U\<close>: for \<open>k\<^sub>i < idx < L\<close>, \<open>R!idx \<ge> U\<close>.\<close>
  have intR0: "\<And>idx. k\<^sub>0 < idx \<Longrightarrow> idx < L \<Longrightarrow> R ! idx \<ge> U"
  proof -
    fix idx assume a1: "k\<^sub>0 < idx" and a2: "idx < L"
    have jrng: "0 < idx - k\<^sub>0 \<and> idx - k\<^sub>0 < length (drop k\<^sub>0 R) - 1"
      using a1 a2 k0lt len0 unfolding L_def by simp
    have "(drop k\<^sub>0 R) ! (idx - k\<^sub>0) \<ge> (drop k\<^sub>0 R) ! (length (drop k\<^sub>0 R) - 1)"
      using int0 jrng by blast
    moreover have "(drop k\<^sub>0 R) ! (idx - k\<^sub>0) = R ! idx"
      using a1 a2 k0lt unfolding L_def by (simp add: nth_drop)
    ultimately show "R ! idx \<ge> U" using last0 by simp
  qed
  have intR1: "\<And>idx. k\<^sub>1 < idx \<Longrightarrow> idx < L \<Longrightarrow> R ! idx \<ge> U"
  proof -
    fix idx assume a1: "k\<^sub>1 < idx" and a2: "idx < L"
    have jrng: "0 < idx - k\<^sub>1 \<and> idx - k\<^sub>1 < length (drop k\<^sub>1 R) - 1"
      using a1 a2 k1lt len1 unfolding L_def by simp
    have "(drop k\<^sub>1 R) ! (idx - k\<^sub>1) \<ge> (drop k\<^sub>1 R) ! (length (drop k\<^sub>1 R) - 1)"
      using int1 jrng by blast
    moreover have "(drop k\<^sub>1 R) ! (idx - k\<^sub>1) = R ! idx"
      using a1 a2 k1lt unfolding L_def by (simp add: nth_drop)
    ultimately show "R ! idx \<ge> U" using last1 by simp
  qed
  \<comment> \<open>Trichotomy on \<open>k\<^sub>0\<close> vs \<open>k\<^sub>1\<close>; the strict cases contradict via the other's
     interior \<open>\<ge> U\<close> against this one's start \<open>< U\<close>.\<close>
  show "k\<^sub>0 = k\<^sub>1"
  proof (rule ccontr)
    assume "k\<^sub>0 \<noteq> k\<^sub>1"
    then consider (lt) "k\<^sub>0 < k\<^sub>1" | (gt) "k\<^sub>1 < k\<^sub>0" by linarith
    thus False
    proof cases
      case lt
      have "R ! k\<^sub>1 \<ge> U" by (rule intR0[OF lt k1L])
      thus False using hd1R by simp
    next
      case gt
      have "R ! k\<^sub>0 \<ge> U" by (rule intR1[OF gt k0L])
      thus False using hd0R by simp
    qed
  qed
qed

text \<open>
  kind-1 length-pin (content.md 1916): two kind-1 scb-decompositions of the same
  \<open>t \<noteq> Trm []\<close> have marked principals with EQUAL \<open>RightNodes\<close> length.  Each
  marked-principal \<open>RightNodes\<close> is a suffix of \<open>RightNodes t\<close>
  (@{thm [source] rnsub_RN_occ_suffix}), and the kind-1 shape pins the start index
  (@{thm [source] rnsub_kind1_drop_index_pin}); equal start index gives equal
  suffix length.\<close>

lemma rnsub_kind1_len_pin:
  assumes tne: "t \<noteq> Trm []"
      and d0: "scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
      and p0: "c\<^sub>0 = flatBP p\<^sub>0" and p1: "c\<^sub>1 = flatBP p\<^sub>1"
  shows "length (RightNodes (Trm [p\<^sub>0])) = length (RightNodes (Trm [p\<^sub>1]))"
proof -
  have sd0: "scb_decomp t s\<^sub>0 c\<^sub>0 b\<^sub>0" using d0 by (simp add: scb_kind1_def)
  have sd1: "scb_decomp t s\<^sub>1 c\<^sub>1 b\<^sub>1" using d1 by (simp add: scb_kind1_def)
  obtain ys where ys: "t = Trm ys" by (cases t)
  from sd0 have e0: "flatBT t = s\<^sub>0 @ c\<^sub>0 @ b\<^sub>0" and b0RP: "\<forall>x \<in> set b\<^sub>0. x = RP"
    using tne by (auto simp: scb_decomp_def)
  from sd1 have e1: "flatBT t = s\<^sub>1 @ c\<^sub>1 @ b\<^sub>1" and b1RP: "\<forall>x \<in> set b\<^sub>1. x = RP"
    using tne by (auto simp: scb_decomp_def)
  have occ0: "flatBT (Trm ys) = s\<^sub>0 @ flatBP p\<^sub>0 @ b\<^sub>0" using e0 p0 ys by simp
  have occ1: "flatBT (Trm ys) = s\<^sub>1 @ flatBP p\<^sub>1 @ b\<^sub>1" using e1 p1 ys by simp
  \<comment> \<open>Both marked-principal RightNodes are suffixes of \<open>RightNodes (Trm ys)\<close>.\<close>
  obtain k\<^sub>0 where K0: "RightNodes (Trm [p\<^sub>0]) = drop k\<^sub>0 (RightNodes (Trm ys))"
    using rnsub_RN_occ_suffix[OF occ0 b0RP] by blast
  obtain k\<^sub>1 where K1: "RightNodes (Trm [p\<^sub>1]) = drop k\<^sub>1 (RightNodes (Trm ys))"
    using rnsub_RN_occ_suffix[OF occ1 b1RP] by blast
  define R where "R = RightNodes (Trm ys)"
  \<comment> \<open>Abbreviate the two suffixes; \<open>r\<^sub>i = drop k\<^sub>i R\<close> blocks \<open>RightNodes.simps\<close> from
     re-unfolding \<open>R\<close> during the shape extraction.\<close>
  define r\<^sub>0 where "r\<^sub>0 = drop k\<^sub>0 R"
  define r\<^sub>1 where "r\<^sub>1 = drop k\<^sub>1 R"
  have r0eq: "RightNodes (Trm [p\<^sub>0]) = r\<^sub>0" using K0 R_def r\<^sub>0_def by simp
  have r1eq: "RightNodes (Trm [p\<^sub>1]) = r\<^sub>1" using K1 R_def r\<^sub>1_def by simp
  \<comment> \<open>Extract the kind-1 shape conditions on each suffix (\<open>r\<^sub>i\<close> opaque).  Pull the
     universal \<open>\<forall>p. c = flatBP p \<longrightarrow> \<dots>\<close> from the def and instantiate at \<open>p\<^sub>i\<close>.\<close>
  have all0: "\<forall>p. c\<^sub>0 = flatBP p \<longrightarrow>
        (let r = RightNodes (Trm [p]); j1 = Lng r - 1 in
         j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1))"
    using d0 by (simp add: scb_kind1_def)
  have all1: "\<forall>p. c\<^sub>1 = flatBP p \<longrightarrow>
        (let r = RightNodes (Trm [p]); j1 = Lng r - 1 in
         j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1))"
    using d1 by (simp add: scb_kind1_def)
  have sh0: "let r = r\<^sub>0; j1 = Lng r - 1 in
         j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
    using all0[rule_format, OF p0] unfolding r0eq[symmetric] .
  have sh1: "let r = r\<^sub>1; j1 = Lng r - 1 in
         j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
    using all1[rule_format, OF p1] unfolding r1eq[symmetric] .
  have sh0': "1 \<le> length r\<^sub>0 - 1 \<and> r\<^sub>0 ! 0 < r\<^sub>0 ! (length r\<^sub>0 - 1)
              \<and> (\<forall>j. 0 < j \<and> j < length r\<^sub>0 - 1 \<longrightarrow> r\<^sub>0 ! j \<ge> r\<^sub>0 ! (length r\<^sub>0 - 1))"
    using sh0 by (simp add: Let_def)
  have sh1': "1 \<le> length r\<^sub>1 - 1 \<and> r\<^sub>1 ! 0 < r\<^sub>1 ! (length r\<^sub>1 - 1)
              \<and> (\<forall>j. 0 < j \<and> j < length r\<^sub>1 - 1 \<longrightarrow> r\<^sub>1 ! j \<ge> r\<^sub>1 ! (length r\<^sub>1 - 1))"
    using sh1 by (simp add: Let_def)
  have len0: "2 \<le> length (drop k\<^sub>0 R)"
    using sh0' r\<^sub>0_def by (simp; linarith)
  have len1: "2 \<le> length (drop k\<^sub>1 R)"
    using sh1' r\<^sub>1_def by (simp; linarith)
  have hd0: "(drop k\<^sub>0 R) ! 0 < (drop k\<^sub>0 R) ! (length (drop k\<^sub>0 R) - 1)"
    using sh0' r\<^sub>0_def by simp
  have int0: "\<forall>j. 0 < j \<and> j < length (drop k\<^sub>0 R) - 1
                  \<longrightarrow> (drop k\<^sub>0 R) ! j \<ge> (drop k\<^sub>0 R) ! (length (drop k\<^sub>0 R) - 1)"
    using sh0' r\<^sub>0_def by simp
  have hd1: "(drop k\<^sub>1 R) ! 0 < (drop k\<^sub>1 R) ! (length (drop k\<^sub>1 R) - 1)"
    using sh1' r\<^sub>1_def by simp
  have int1: "\<forall>j. 0 < j \<and> j < length (drop k\<^sub>1 R) - 1
                  \<longrightarrow> (drop k\<^sub>1 R) ! j \<ge> (drop k\<^sub>1 R) ! (length (drop k\<^sub>1 R) - 1)"
    using sh1' r\<^sub>1_def by simp
  \<comment> \<open>The start indices are \<open>< length R\<close> (each suffix is nonempty).\<close>
  have k0lt: "k\<^sub>0 < length R" using len0 by (cases "k\<^sub>0 < length R") simp_all
  have k1lt: "k\<^sub>1 < length R" using len1 by (cases "k\<^sub>1 < length R") simp_all
  have "k\<^sub>0 = k\<^sub>1"
    by (rule rnsub_kind1_drop_index_pin[OF k0lt k1lt len0 len1 hd0 int0 hd1 int1])
  hence "drop k\<^sub>0 R = drop k\<^sub>1 R" by simp
  thus ?thesis using K0 K1 R_def by simp
qed

text \<open>
  UNCONDITIONAL conjunct (5) of @{text p_7_2_scb_unique}: two kind-1
  scb-decompositions of \<open>t \<in> T_B\<close>, \<open>t \<noteq> Trm []\<close> coincide.  The residual
  RightNodes length-pin assumed by @{thm [source] m_7_2_scb_kind1_unique_uncond}
  is now discharged by @{thm [source] rnsub_kind1_len_pin}.\<close>

lemma m_7_2_scb_kind1_unique_uncond':
  assumes tTB: "t \<in> T_B" and tne: "t \<noteq> Trm []"
      and d0: "scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
  shows "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
proof -
  have rneq: "\<And>p\<^sub>0 p\<^sub>1. c\<^sub>0 = flatBP p\<^sub>0 \<Longrightarrow> c\<^sub>1 = flatBP p\<^sub>1
                   \<Longrightarrow> length (RightNodes (Trm [p\<^sub>0])) = length (RightNodes (Trm [p\<^sub>1]))"
    using rnsub_kind1_len_pin[OF tne d0 d1] by blast
  show ?thesis
    by (rule m_7_2_scb_kind1_unique_uncond[OF tTB tne d0 d1 rneq])
qed



section \<open>§7.2 種の排他性 (p_7_2_scb_unique conjunct (3), with t \<noteq> Trm []) — wf16-kinds\<close>

text \<open>
  EMPIRICAL TRUTH-CHECK (\<open>python/_wf16_kinds_check.py\<close>, BT model, indices
  \<open>{0,1,2}\<close>, depth \<open>2\<close>, 1561 \<open>D\<^sub>\<omega>\<close>-free terms):
  \<^item> conjunct (3) kind0/kind1-EXCLUSIVITY: 0 failures over the 1560 NONEMPTY
    terms.  The legacy encoder's sole zero failure came from allowing the kind
    condition to hold vacuously for a non-principal \<open>c\<close>.  A14 is retracted; the
    current positive \<open>isPTB_str c\<close> conjunct excludes that artefact.  This helper
    retains \<open>t \<noteq> Trm []\<close> only because it is the nonempty branch of the final proof.
  \<^item> KEY arithmetic fact (0/39 principals): NO principal \<open>p\<close> has its
    \<^const>\<open>RightNodes\<close> meeting BOTH kind conditions — kind0 forces \<open>j\<^sub>1 = 1\<close> with
    \<open>r ! 1 = 0\<close>, while kind1 needs \<open>r ! 0 < r ! j\<^sub>1\<close>; if both, then \<open>r ! 0 < 0\<close>
    in \<^typ>\<open>nat\<close>, absurd.

  MECHANIZATION.  Both kind0 and kind1 marked principals occur in scb-shaped
  positions, so by the GREEN suffix brick @{thm [source] rnsub_RN_occ_suffix}
  each \<open>RightNodes (Trm [p])\<close> is a \<^const>\<open>drop\<close>-suffix of \<open>RightNodes t\<close>.  Two
  nonempty suffixes of one list share their LAST element; kind0's last element is
  \<open>0\<close>, so kind1's \<open>r ! 0 < r ! j\<^sub>1 = 0\<close> is the contradiction.  No \<open>c\<close>-uniqueness
  / length-pin needed.  Sound — cites only GREEN @{thm [source] rnsub_RN_occ_suffix}
  and pure list/\<^const>\<open>RightNodes\<close> facts.
\<close>

\<comment> \<open>A nonempty \<^const>\<open>drop\<close>-suffix shares the last element of the whole list.\<close>
lemma rnsub_drop_last_eq:
  assumes "k < length R"
  shows "drop k R ! (length (drop k R) - 1) = R ! (length R - 1)"
proof -
  have ne: "drop k R \<noteq> []" using assms by simp
  have Rne: "R \<noteq> []" using assms by auto
  have "drop k R ! (length (drop k R) - 1) = last (drop k R)"
    using ne by (simp add: last_conv_nth)
  also have "\<dots> = last R" using ne by (simp add: last_drop)
  also have "\<dots> = R ! (length R - 1)"
    using Rne by (simp add: last_conv_nth)
  finally show ?thesis .
qed

\<comment> \<open>From a kind-0 scb-decomposition of a nonempty \<open>t\<close>: the marked principal's
   \<^const>\<open>RightNodes\<close> is a length-2 suffix of \<open>RightNodes t\<close> with last entry \<open>0\<close>.
   Hence \<open>RightNodes t\<close> is nonempty and its last element is \<open>0\<close>.\<close>
lemma rnsub_kind0_last0:
  assumes tne: "t \<noteq> Trm []"
      and d0: "scb_kind0 t s c b"
  shows "RightNodes t \<noteq> [] \<and> RightNodes t ! (length (RightNodes t) - 1) = 0"
proof -
  have sd: "scb_decomp t s c b" using d0 by (simp add: scb_kind0_def)
  obtain ys where ys: "t = Trm ys" by (cases t)
  from sd have occ': "flatBT t = s @ c @ b" and pc: "isPTB_str c"
    and bRP: "\<forall>x \<in> set b. x = RP"
    using tne by (auto simp: scb_decomp_def)
  obtain p where p: "c = flatBP p" using pc unfolding isPTB_str_def by blast
  have kc: "Lng (RightNodes (Trm [p])) = 2 \<and> RightNodes (Trm [p]) ! 1 = 0"
    using d0 p by (simp add: scb_kind0_def)
  have occ: "flatBT (Trm ys) = s @ flatBP p @ b" using occ' p ys by simp
  obtain k where suf: "RightNodes (Trm [p]) = drop k (RightNodes (Trm ys))"
    using rnsub_RN_occ_suffix[OF occ bRP] by blast
  have len2: "length (RightNodes (Trm [p])) = 2" using kc by simp
  \<comment> \<open>the suffix is nonempty (length 2), so \<open>k < length (RightNodes (Trm ys))\<close>.\<close>
  have klt: "k < length (RightNodes (Trm ys))"
  proof (rule ccontr)
    assume "\<not> k < length (RightNodes (Trm ys))"
    hence "length (RightNodes (Trm ys)) \<le> k" by simp
    hence "drop k (RightNodes (Trm ys)) = []" by simp
    thus False using suf len2 by simp
  qed
  have RNne: "RightNodes (Trm ys) \<noteq> []" using klt by auto
  \<comment> \<open>last of the suffix = last of \<open>RightNodes (Trm ys)\<close>; and last of the suffix
     is \<open>RightNodes (Trm [p]) ! 1 = 0\<close>.\<close>
  have lasteq: "RightNodes (Trm [p]) ! (length (RightNodes (Trm [p])) - 1)
                  = RightNodes (Trm ys) ! (length (RightNodes (Trm ys)) - 1)"
    using suf rnsub_drop_last_eq[OF klt] by simp
  have "RightNodes (Trm [p]) ! (length (RightNodes (Trm [p])) - 1)
          = RightNodes (Trm [p]) ! 1" using len2 by simp
  hence "RightNodes (Trm ys) ! (length (RightNodes (Trm ys)) - 1) = 0"
    using lasteq kc by simp
  thus ?thesis using RNne ys by simp
qed

\<comment> \<open>From a kind-1 scb-decomposition of a nonempty \<open>t\<close>: the marked principal's
   \<^const>\<open>RightNodes\<close> is a suffix of \<open>RightNodes t\<close> of length \<open>j\<^sub>1+1 \<ge> 2\<close> whose
   LAST element is strictly greater than its FIRST.  Hence \<open>RightNodes t\<close> is
   nonempty and its last element is \<open>> RightNodes (Trm [p]) ! 0 \<ge> 0\<close>.\<close>
lemma rnsub_kind1_lastpos:
  assumes tne: "t \<noteq> Trm []"
      and d1: "scb_kind1 t s c b"
  shows "RightNodes t \<noteq> []
         \<and> RightNodes t ! (length (RightNodes t) - 1) > 0"
proof -
  have sd: "scb_decomp t s c b" using d1 by (simp add: scb_kind1_def)
  obtain ys where ys: "t = Trm ys" by (cases t)
  from sd have occ': "flatBT t = s @ c @ b" and pc: "isPTB_str c"
    and bRP: "\<forall>x \<in> set b. x = RP"
    using tne by (auto simp: scb_decomp_def)
  obtain p where p: "c = flatBP p" using pc unfolding isPTB_str_def by blast
  define R0 where "R0 = RightNodes (Trm [p])"
  define j1 where "j1 = Lng R0 - 1"
  have kc: "j1 \<ge> 1 \<and> R0 ! 0 < R0 ! j1
              \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> R0 ! j \<ge> R0 ! j1)"
    using d1 p unfolding R0_def j1_def by (simp add: scb_kind1_def Let_def)
  have occ: "flatBT (Trm ys) = s @ flatBP p @ b" using occ' p ys by simp
  obtain k where suf: "R0 = drop k (RightNodes (Trm ys))"
    using rnsub_RN_occ_suffix[OF occ bRP] unfolding R0_def by blast
  have j1ge1: "j1 \<ge> 1" using kc by simp
  have len2: "length R0 \<ge> 2" using j1ge1 unfolding j1_def by linarith
  hence j1id: "j1 = length R0 - 1" unfolding j1_def by simp
  have klt: "k < length (RightNodes (Trm ys))"
  proof (rule ccontr)
    assume "\<not> k < length (RightNodes (Trm ys))"
    hence "length (RightNodes (Trm ys)) \<le> k" by simp
    hence "drop k (RightNodes (Trm ys)) = []" by simp
    thus False using suf len2 by simp
  qed
  have RNne: "RightNodes (Trm ys) \<noteq> []" using klt by auto
  have lasteq: "R0 ! (length R0 - 1)
                  = RightNodes (Trm ys) ! (length (RightNodes (Trm ys)) - 1)"
    using suf rnsub_drop_last_eq[OF klt] by simp
  have "R0 ! 0 < R0 ! j1" using kc by simp
  hence "0 < R0 ! j1" by simp
  hence "0 < R0 ! (length R0 - 1)" using j1id by simp
  hence "0 < RightNodes (Trm ys) ! (length (RightNodes (Trm ys)) - 1)"
    using lasteq by simp
  thus ?thesis using RNne ys by simp
qed

text \<open>Nonempty branch of conjunct (3) of @{text p_7_2_scb_unique}:
  \<open>t\<close> is not both 第0種- and 第1種-scb分解可能.  If it were,
  the kind-0 decomposition pins the last \<^const>\<open>RightNodes\<close> entry to \<open>0\<close> while the
  kind-1 decomposition pins it to \<open>> 0\<close> — contradiction.\<close>
lemma m_7_2_scb_kinds_exclusive:
  assumes tne: "t \<noteq> Trm []"
  shows "\<not> scb_kind0_able t \<or> \<not> scb_kind1_able t"
proof (rule ccontr)
  assume "\<not> (\<not> scb_kind0_able t \<or> \<not> scb_kind1_able t)"
  hence k0: "scb_kind0_able t" and k1: "scb_kind1_able t" by auto
  obtain s\<^sub>0 c\<^sub>0 b\<^sub>0 where d0: "scb_kind0 t s\<^sub>0 c\<^sub>0 b\<^sub>0" using k0 by blast
  obtain s\<^sub>1 c\<^sub>1 b\<^sub>1 where d1: "scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1" using k1 by blast
  have last0: "RightNodes t ! (length (RightNodes t) - 1) = 0"
    using rnsub_kind0_last0[OF tne d0] by simp
  have lastpos: "RightNodes t ! (length (RightNodes t) - 1) > 0"
    using rnsub_kind1_lastpos[OF tne d1] by simp
  show False using last0 lastpos by simp
qed


section \<open>§7.2 dom-可分解性 (p_7_2_scb_unique conjunct (2)) — scb側 forward + domB blocker\<close>

text \<open>
  Nonempty branch of conjunct (2):
  \<open>domB t = NatSet \<longleftrightarrow> (scb_kind0_able t \<or> scb_kind1_able t)\<close>.
  The former zero mismatch in \<open>python/_wf16_kinds_check.py\<close> was caused by the
  vacuous kind encoding recorded in retracted A14.  With the current positive
  principal condition, zero makes both sides false; the final theorem proves that
  branch separately.

  EMPIRICAL CHARACTERIZATION (\<open>python/_wf16_dom2.py\<close>/\<open>_dom3.py\<close>/\<open>_dom4.py\<close>,
  BT model indices \<open>{0,1,2}\<close> depth 2, 1560 nonempty terms, 0 mismatches; with
  \<open>R = RightNodes t\<close>, \<open>j\<^sub>1 = Lng R - 1\<close>):
  \<^enum> \<open>scb_kind0_able t \<longleftrightarrow> (j\<^sub>1 \<ge> 1 \<and> R ! j\<^sub>1 = 0)\<close>;
  \<^enum> \<open>scb_kind1_able t \<longleftrightarrow> (j\<^sub>1 \<ge> 1 \<and> (\<exists>k < j\<^sub>1. R ! k < R ! j\<^sub>1))\<close>;
  \<^enum> \<open>domB t = NatSet \<longleftrightarrow> (j\<^sub>1 \<ge> 1 \<and> (R ! j\<^sub>1 = 0 \<or> (\<exists>k < j\<^sub>1. R ! k < R ! j\<^sub>1)))\<close>.
  (1)\<open>\<or>\<close>(2) is exactly (3), matching the article's "(2) follows immediately from
  the recursive definition of \<open>dom\<close>".

  \<^bold>\<open>BLOCKER (honest).\<close>  Equivalence (3) — the \<open>domB\<close> side — is \<^emph>\<open>not\<close> mechanizable
  in the current development: \<^const>\<open>domB\<close> is declared by \<open>function \<dots> by
  pat_completeness auto\<close> with termination DEFERRED ([Buc1] Lemma 3.2; see
  \<open>the article proposition transcription\<close> line 776 and the \<open>termination \<dots> deferred\<close> comment).  There is
  NO \<open>domB.psimps\<close>/\<open>domB_dom\<close> fact in the tree (grep confirms: only \<open>Red_dom\<close>
  occurrences, which are unrelated), so \<open>domB t\<close> cannot be unfolded/evaluated at
  all.  Discharging (2) therefore REDUCES to first proving the deferred
  \<open>domB\<close>/\<open>operB\<close>/\<open>xseq\<close> termination (or at least \<open>domB_operB_xseq_dom\<close> on
  \<^const>\<open>T_B\<close>), then the rightmost-spine induction giving equivalence (3) above.
  That is a separate multi-lemma program ([Buc1] §3), out of scope for this brick.

  What IS banked GREEN below: the \<open>scb\<close>-side forward implications (1)(\<open>\<Rightarrow>\<close>) and
  (2)(\<open>\<Rightarrow>\<close>), i.e. \<open>scb_kind0_able / scb_kind1_able \<Longrightarrow> RightNodes-shape\<close>, sound
  consequences of the GREEN suffix brick @{thm [source] rnsub_RN_occ_suffix} and
  the (3) helpers @{thm [source] rnsub_kind0_last0}, @{thm [source] rnsub_kind1_lastpos}.
  These are exactly the RHS-to-RightNodes half of (2) (the part that does NOT
  touch \<^const>\<open>domB\<close>).
\<close>

\<comment> \<open>kind-0-able \<Longrightarrow> the RightNodes shape \<open>(j\<^sub>1 \<ge> 1 \<and> R ! j\<^sub>1 = 0)\<close>.  The marked
   principal's RightNodes (length 2) is a suffix of \<open>R\<close>, so \<open>Lng R \<ge> 2\<close>
   (i.e. \<open>j\<^sub>1 \<ge> 1\<close>); its last entry is \<open>0\<close> by @{thm [source] rnsub_kind0_last0}.\<close>
lemma rnsub_kind0_able_shape:
  assumes tne: "t \<noteq> Trm []"
      and k0: "scb_kind0_able t"
  shows "Lng (RightNodes t) - 1 \<ge> 1
         \<and> RightNodes t ! (Lng (RightNodes t) - 1) = 0"
proof -
  obtain s c b where d0: "scb_kind0 t s c b" using k0 by blast
  have sd: "scb_decomp t s c b" using d0 by (simp add: scb_kind0_def)
  obtain ys where ys: "t = Trm ys" by (cases t)
  from sd have occ': "flatBT t = s @ c @ b" and pc: "isPTB_str c"
    and bRP: "\<forall>x \<in> set b. x = RP"
    using tne by (auto simp: scb_decomp_def)
  obtain p where p: "c = flatBP p" using pc unfolding isPTB_str_def by blast
  have kc2: "Lng (RightNodes (Trm [p])) = 2" using d0 p by (simp add: scb_kind0_def)
  have occ: "flatBT (Trm ys) = s @ flatBP p @ b" using occ' p ys by simp
  obtain k where suf: "RightNodes (Trm [p]) = drop k (RightNodes (Trm ys))"
    using rnsub_RN_occ_suffix[OF occ bRP] by blast
  have "length (drop k (RightNodes (Trm ys))) = 2" using suf kc2 by simp
  hence lenge: "Lng (RightNodes (Trm ys)) \<ge> 2" by simp
  have last0: "RightNodes t ! (length (RightNodes t) - 1) = 0"
    using rnsub_kind0_last0[OF tne d0] by simp
  show ?thesis using lenge last0 ys by simp
qed

\<comment> \<open>kind-1-able \<Longrightarrow> the RightNodes shape \<open>(j\<^sub>1 \<ge> 1 \<and> (\<exists>k < j\<^sub>1. R ! k < R ! j\<^sub>1))\<close>.
   The marked principal's RightNodes \<open>= drop k R\<close> has first \<open>< last\<close>; its first is
   \<open>R ! k\<close>, its last is \<open>R ! j\<^sub>1\<close> (shared last element), and \<open>k < j\<^sub>1\<close> since the
   suffix has length \<open>\<ge> 2\<close>.\<close>
lemma rnsub_kind1_able_shape:
  assumes tne: "t \<noteq> Trm []"
      and k1: "scb_kind1_able t"
  shows "Lng (RightNodes t) - 1 \<ge> 1
         \<and> (\<exists>k < Lng (RightNodes t) - 1.
              RightNodes t ! k < RightNodes t ! (Lng (RightNodes t) - 1))"
proof -
  obtain s c b where d1: "scb_kind1 t s c b" using k1 by blast
  have sd: "scb_decomp t s c b" using d1 by (simp add: scb_kind1_def)
  obtain ys where ys: "t = Trm ys" by (cases t)
  from sd have occ': "flatBT t = s @ c @ b" and pc: "isPTB_str c"
    and bRP: "\<forall>x \<in> set b. x = RP"
    using tne by (auto simp: scb_decomp_def)
  obtain p where p: "c = flatBP p" using pc unfolding isPTB_str_def by blast
  define R0 where "R0 = RightNodes (Trm [p])"
  define j1 where "j1 = Lng R0 - 1"
  define R where "R = RightNodes (Trm ys)"
  have kc: "j1 \<ge> 1 \<and> R0 ! 0 < R0 ! j1
              \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> R0 ! j \<ge> R0 ! j1)"
    using d1 p unfolding R0_def j1_def by (simp add: scb_kind1_def Let_def)
  have j1ge1: "j1 \<ge> 1" using kc by simp
  have len2: "length R0 \<ge> 2" using j1ge1 unfolding j1_def by linarith
  hence j1id: "j1 = length R0 - 1" unfolding j1_def by simp
  have occ: "flatBT (Trm ys) = s @ flatBP p @ b" using occ' p ys by simp
  obtain k where suf: "R0 = drop k R"
    using rnsub_RN_occ_suffix[OF occ bRP] unfolding R0_def R_def by blast
  \<comment> \<open>start index \<open>k < Lng R\<close>, and \<open>k + j1 = Lng R - 1\<close>.\<close>
  have klt: "k < length R"
  proof (rule ccontr)
    assume "\<not> k < length R"
    hence "length R \<le> k" by simp
    hence "drop k R = []" by simp
    thus False using suf len2 by simp
  qed
  have lenR0: "length R0 = length R - k" using suf klt by simp
  have lenRge: "length R \<ge> 2 + k" using lenR0 len2 by simp
  \<comment> \<open>\<open>j\<^sub>1\<^bsup>t\<^esup> = Lng R - 1\<close>; the witness index is \<open>k < j\<^sub>1\<^bsup>t\<^esup>\<close>.\<close>
  have kltj1t: "k < length R - 1" using lenRge by simp
  \<comment> \<open>\<open>R ! k = R0 ! 0\<close> (first of the suffix).\<close>
  have R0hd: "R0 ! 0 = R ! k" using suf klt by (simp add: nth_drop)
  \<comment> \<open>\<open>R0 ! j1 = R ! (Lng R - 1)\<close> (shared last element).\<close>
  have R0last: "R0 ! j1 = R ! (length R - 1)"
    using suf j1id rnsub_drop_last_eq[OF klt] by simp
  have "R0 ! 0 < R0 ! j1" using kc by simp
  hence wit: "R ! k < R ! (length R - 1)" using R0hd R0last by simp
  have j1tge1: "Lng R - 1 \<ge> 1" using lenRge by simp
  have "\<exists>k < Lng R - 1. R ! k < R ! (Lng R - 1)"
    using kltj1t wit by blast
  thus ?thesis using j1tge1 unfolding R_def using ys by simp
qed

text \<open>The \<open>scb\<close>-side forward half of conjunct (2), assembled: kind-0/kind-1
  decomposability of a nonempty \<open>t\<close> forces the \<^const>\<open>RightNodes\<close> shape that the
  \<^const>\<open>domB\<close>-recursion would land on \<open>NatSet\<close> (the empirical equivalence (3)
  above).  The converse and the \<^const>\<open>domB\<close>-side equivalence (3) remain blocked
  on the deferred \<^const>\<open>domB\<close> termination, as documented above.\<close>
lemma rnsub_kindable_imp_natshape:
  assumes tne: "t \<noteq> Trm []"
      and kab: "scb_kind0_able t \<or> scb_kind1_able t"
  shows "Lng (RightNodes t) - 1 \<ge> 1
         \<and> (RightNodes t ! (Lng (RightNodes t) - 1) = 0
            \<or> (\<exists>k < Lng (RightNodes t) - 1.
                 RightNodes t ! k < RightNodes t ! (Lng (RightNodes t) - 1)))"
  using kab
proof
  assume "scb_kind0_able t"
  thus ?thesis using rnsub_kind0_able_shape[OF tne] by blast
next
  assume "scb_kind1_able t"
  thus ?thesis using rnsub_kind1_able_shape[OF tne] by blast
qed




section \<open>§7.2 GENERALIZED PRINCIPAL-REPLACEMENT SURGERY — scbrepl_image residual (A13 + c1-around 4-1)\<close>


text \<open>GENERALIZED PRINCIPAL-REPLACEMENT SURGERY (discharges the scbrepl_image
  residual: A13 §7.2 add_scb (3) image + m_7_2_scb_replaceable_corr_mod_image).
  An occurrence of a complete principal string \<open>flatBP pr\<close> inside the flat string
  of a term \<open>u \<in> T\<^bsub>B\<^esub>\<close> can be replaced by ANY other complete principal string
  \<open>flatBP pr'\<close> (\<open>pr' \<in> PT\<^bsub>B\<^esub>\<close>), yielding a witness \<open>u' \<in> T\<^bsub>B\<^esub>\<close> with the spliced
  flat string.  Empirically TRUE (0/54510, \<open>python/_gen_surgery_audit.py\<close> + the
  index-changing variant \<open>python/scb_image_audit.py\<close>).  Proof: structural
  \<open>flatBT_flatBP.induct\<close>; the occurrence (head \<open>Dsym\<close>) localizes into exactly one
  \<open>flatBP\<close> chunk by prefix-weight cancellation, mirroring \<open>m_7_flatBT_inj\<close>.\<close>

\<comment> \<open>A complete \<open>flatBP\<close> string is nonempty and starts with a \<open>Dsym\<close>.\<close>
lemma flatBP_nonempty: "flatBP p \<noteq> []"
  by (cases p) simp
lemma flatBP_hd: "\<exists>u rest. flatBP p = Dsym u # rest"
  by (cases p) simp

end
