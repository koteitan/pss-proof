theory P_8_3_kind0_base_ineq
  imports Support_8_C
begin

subsection \<open>§8.3 条件(II)の下での展開規則\<close>

text \<open>The §8 "conditions (I)–(VI)" are exactly the \<open>Trans\<close>-recursion conditions
  (I)–(VI) of §7.3, i.e. \<open>transCondI\<close> \<dots> \<open>transCondVI\<close>; "\<open>M\<close> satisfies condition
  (II)" is \<open>transCondII M\<close>.  Throughout this subsection \<open>j\<^sub>1 = Lng M - 1\<close>,
  \<open>j\<^sub>0 = parent M 0 j\<^sub>1\<close> (the unique row-0 nearest ancestor of \<open>j\<^sub>1\<close>), and
  \<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close>.  \<open>RT\<^bsub>PS\<^esub>\<^sup>Marked\<close> is modelled by \<open>(M,m) \<in> Marked \<and> M \<in> RT\<^bsub>PS\<^esub>\<close>.
  "第\<open>0\<close>種型基本列" (kind-\<open>0\<close>-type fundamental sequence) is the article's
  descriptive title for these three lemmas — the case \<open>M\<^bsub>1,j\<^sub>1\<^esub> = 0\<close> of the
  fundamental sequence \<open>M[n]\<close>; it is NOT a separately defined notion, so the
  statements use only the existing pair-sequence vocabulary.\<close>

text \<open>補題（第\<open>0\<close>種型基本列の基本不等式） (§8.3, article 3972): for \<open>M \<in> T\<^bsub>PS\<^esub>\<close>,
  \<open>n,r' \<in> \<nat>\<^sub>+\<close>, \<open>q,q' \<in> \<nat>\<close>, with \<open>j\<^sub>1 = Lng M - 1\<close>, if there is a unique
  \<open>j\<^sub>0\<close> with \<open>(0,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (0,j\<^sub>1)\<close>, \<open>M\<^bsub>1,j\<^sub>1\<^esub> = 0\<close>, \<open>q \<le> n-1\<close>, \<open>q' \<le> n-1\<close>,
  and \<open>0 < r' < j\<^sub>1-j\<^sub>0\<close>, then \<open>M[n]\<^bsub>0,j\<^sub>0+q(j\<^sub>1-j\<^sub>0)\<^esub> < M[n]\<^bsub>0,j\<^sub>0+q'(j\<^sub>1-j\<^sub>0)+r'\<^esub>\<close>.
  (Article \<open>r' \<in> j\<^sub>1-j\<^sub>0\<close> with \<open>r' \<in> \<nat>\<^sub>+\<close> is read as \<open>0 < r' < j\<^sub>1-j\<^sub>0\<close>.)\<close>

lemma p_8_3_kind0_base_ineq:
  fixes M :: pairseq
  assumes "M \<in> T_PS" "0 < n" "0 < r'"
    and "hasParent M 0 (Lng M - 1)"
    and "entry M 1 (Lng M - 1) = 0"
    and "q \<le> n - 1" "q' \<le> n - 1"
    and "r' < (Lng M - 1) - parent M 0 (Lng M - 1)"
  shows "entry (M[n]) 0 (parent M 0 (Lng M - 1)
                          + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
       < entry (M[n]) 0 (parent M 0 (Lng M - 1)
                          + q' * ((Lng M - 1) - parent M 0 (Lng M - 1)) + r')"
  by (rule m_8_3_kind0_base_ineq[OF assms])

end
