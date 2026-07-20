theory Frontier_7_006
  imports Support_7_003
begin

text \<open>
  The flat string of \<open>Trm xs\<close> (\<open>xs \<noteq> []\<close>, \<open>last xs = DB u a\<close>) splits as
  \<open>pre \<frown> (Dsym u # flatBT a) \<frown> post\<close> with \<open>post\<close> all-\<open>)\<close>, uniformly for the
  single (\<open>pre = []\<close>, \<open>post = []\<close>) and multi (\<open>pre = LP # \<dots> CM, Dsym u\<close>,
  \<open>post = [RP]\<close>) cases.  Replacing the last principal's argument by any \<open>c\<close>
  changes only the middle component.
\<close>

\<comment> \<open>List alignment at the last \<open>Zsym\<close>.  If two append-decompositions of the same
   string each place a \<open>Zsym\<close> with an all-\<open>RP\<close> (hence \<open>Zsym\<close>-free) tail after it,
   the two \<open>Zsym\<close>-positions and the tails coincide.\<close>
lemma rnsub_align_lastZ:
  assumes "aa @ Zsym # pp = bb @ Zsym # qq"
    and "Zsym \<notin> set pp" and "Zsym \<notin> set qq"
  shows "aa = bb \<and> pp = qq"
proof -
  from assms(1) have
    "\<exists>us. (aa = bb @ us \<and> us @ Zsym # pp = Zsym # qq) \<or>
          (aa @ us = bb \<and> Zsym # pp = us @ Zsym # qq)"
    by (simp add: append_eq_append_conv2)
  then obtain us where
    "(aa = bb @ us \<and> us @ Zsym # pp = Zsym # qq) \<or>
     (aa @ us = bb \<and> Zsym # pp = us @ Zsym # qq)" by blast
  thus ?thesis
  proof (elim disjE conjE)
    assume aa_eq: "aa = bb @ us" and tl: "us @ Zsym # pp = Zsym # qq"
    have "us = []"
    proof (rule ccontr)
      assume "us \<noteq> []"
      then obtain u0 us' where us: "us = u0 # us'" by (cases us) auto
      have "qq = us' @ Zsym # pp" using tl us by simp
      hence "Zsym \<in> set qq" by simp
      thus False using assms(3) by simp
    qed
    thus ?thesis using aa_eq tl by simp
  next
    assume bb_eq: "aa @ us = bb" and tl: "Zsym # pp = us @ Zsym # qq"
    have "us = []"
    proof (rule ccontr)
      assume "us \<noteq> []"
      then obtain u0 us' where us: "us = u0 # us'" by (cases us) auto
      have "pp = us' @ Zsym # qq" using tl us by simp
      hence "Zsym \<in> set pp" by simp
      thus False using assms(2) by simp
    qed
    thus ?thesis using bb_eq tl by simp
  qed
qed

\<comment> \<open>flat of a multi-term with the tail not necessarily a literal cons.\<close>
lemma rnsub_flat_multi:
  "zs \<noteq> [] \<Longrightarrow>
   flatBT (Trm (p # zs)) =
     LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) zs)) @ [RP]"
  by (cases zs) simp_all

lemma rnsub_flat_pre_post:
  assumes "xs \<noteq> []" "last xs = DB u a"
  shows "\<exists>pre post. (\<forall>x \<in> set post. x = RP)
            \<and> flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post
            \<and> (\<forall>c. flatBT (Trm (butlast xs @ [DB u c]))
                    = pre @ (Dsym u # flatBT c) @ post)"
proof (cases xs rule: rev_cases)
  case Nil thus ?thesis using assms by simp
next
  case (snoc ys y)
  \<comment> \<open>\<open>y = last xs = DB u a\<close>\<close>
  have y_eq: "y = DB u a" using assms snoc by simp
  show ?thesis
  proof (cases ys)
    case Nil
    \<comment> \<open>single principal \<open>xs = [DB u a]\<close>: \<open>pre = []\<close>, \<open>post = []\<close>\<close>
    show ?thesis
      apply (rule exI[of _ "[]"], rule exI[of _ "[]"])
      using snoc Nil y_eq by simp
  next
    case (Cons p ps)
    \<comment> \<open>multi: \<open>xs = p # ps @ [DB u a]\<close>; the wrap is \<open>LP # \<dots> @ [RP]\<close>\<close>
    define mid where "mid = concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB u a]))"
    have xs_eq: "xs = p # (ps @ [DB u a])" using snoc Cons y_eq by simp
    have flat_xs: "flatBT (Trm xs) = LP # (flatBP p @ mid) @ [RP]"
      unfolding xs_eq mid_def by (rule rnsub_flat_multi) simp
    \<comment> \<open>peel the last component out of \<open>mid\<close>\<close>
    define midpre where
      "midpre = concat (map (\<lambda>r. CM # flatBP r) ps)"
    have mid_eq: "mid = midpre @ CM # flatBP (DB u a)"
      unfolding mid_def midpre_def by simp
    define pre where "pre = LP # flatBP p @ midpre @ [CM]"
    define post where "post = [RP]"
    have flat_split: "flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post"
      using flat_xs unfolding mid_eq pre_def post_def by simp
    have post_RP: "\<forall>x \<in> set post. x = RP" unfolding post_def by simp
    have sub: "\<And>c. flatBT (Trm (butlast xs @ [DB u c]))
                    = pre @ (Dsym u # flatBT c) @ post"
    proof -
      fix c
      have bl: "butlast xs = p # ps"
        using snoc Cons by simp
      have "flatBT (Trm (p # (ps @ [DB u c])))
            = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB u c]))) @ [RP]"
        by (rule rnsub_flat_multi) simp
      also have "concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB u c]))
               = midpre @ CM # flatBP (DB u c)"
        unfolding midpre_def by simp
      finally show "flatBT (Trm (butlast xs @ [DB u c]))
                    = pre @ (Dsym u # flatBT c) @ post"
        using bl unfolding pre_def post_def by simp
    qed
    show ?thesis
      apply (rule exI[of _ pre], rule exI[of _ post])
      using post_RP flat_split sub by blast
  qed
qed

\<comment> \<open>Every flat string contains at least one \<open>Zsym\<close> (the spine bottom).\<close>
lemma rnsub_Zsym_in_flat: "Zsym \<in> set (flatBT a)"
  and rnsub_Zsym_in_flatP: "Zsym \<in> set (flatBP p)"
proof (induction a and p rule: flatBT_flatBP.induct)
qed auto

\<comment> \<open>\<open>T_B\<close> facts: a single (or last) principal of a \<open>D\<^sub>\<omega>\<close>-free term has \<open>u \<noteq> \<infinity>\<close>
   and a \<open>D\<^sub>\<omega>\<close>-free argument; \<open>butlast\<close> stays \<open>D\<^sub>\<omega>\<close>-free.\<close>
lemma rnsub_TB_last:
  assumes "Trm xs \<in> T_B" "xs \<noteq> []" "last xs = DB u a"
  shows "u \<noteq> \<infinity> \<and> a \<in> T_B"
proof -
  have mem: "DB u a \<in> set xs" using assms last_in_set by metis
  have df: "dfree_BP (DB u a)" using assms(1) mem by (auto simp: T_B_def)
  hence ui: "u \<noteq> \<infinity>" and da: "dfree_BT a" by auto
  have "\<exists>i. u = enat i" using ui by (cases u) auto
  thus ?thesis using da by (simp add: T_B_def)
qed

lemma rnsub_TB_replace_last:
  assumes "Trm xs \<in> T_B" "xs \<noteq> []" "u \<noteq> \<infinity>" "c \<in> T_B"
  shows "Trm (butlast xs @ [DB u c]) \<in> T_B"
proof -
  have "\<forall>p \<in> set (butlast xs). dfree_BP p"
    using assms(1) by (auto simp: T_B_def dest: in_set_butlastD)
  moreover have "dfree_BP (DB u c)"
    using assms(3,4) by (simp add: T_B_def)
  ultimately show ?thesis by (simp add: T_B_def)
qed

text \<open>
  \<open>spineSub t\<^sub>0 t\<close>: replace the rightmost-spine bottom \<open>0\<close>-argument of \<open>t\<^sub>0\<close> by \<open>t\<close>.
  Recurses into \<open>last xs = DB u a\<close>; the bottom is reached when \<open>a = 0\<close>.
\<close>

function spineSub :: "BT \<Rightarrow> BT \<Rightarrow> BT" where
  "spineSub (Trm xs) t =
     (case xs of [] \<Rightarrow> Trm []
      | _ \<Rightarrow> (case last xs of DB u a \<Rightarrow>
                (if a = Trm [] then Trm (butlast xs @ [DB u t])
                 else Trm (butlast xs @ [DB u (spineSub a t)]))))"
  by pat_completeness auto
termination spineSub
  apply (relation "measure (\<lambda>(t0,t). size t0)")
   apply simp
  apply (clarsimp simp only: in_measure prod.case)
  apply (rule rnsub_size_arg_lt')
   apply assumption
  apply simp
  done

end
