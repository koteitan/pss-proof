theory P_8_5_Joints_FirstNodes_basic
  imports Support_8_C
begin

text \<open>補題（条件(V)の下での\<open>Joints\<close>と\<open>FirstNodes\<close>と\<open>t\<^sub>2\<close>の基本性質） (§8.5, article 5165):
  for \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>, using the symbols of the \<open>Trans\<close> recursion, set
  \<open>N := (M\<^sub>j)\<^bsub>j=j\<^sub>-\<^sub>1\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close> (\<open>= seg M (Adm M j\<^sub>0) j\<^sub>1\<close>) and \<open>J\<^sub>1 := Lng(Br(Red N))-1\<close>;
  if \<open>(1,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (1,j\<^sub>1)\<close> (\<open>nextR M 1 j\<^sub>0 j\<^sub>1\<close>), \<open>j\<^sub>0\<close> is non-\<open>M\<close>-admissible
  and \<open>j\<^sub>0 < j\<^sub>1-1\<close>, then:
    (1) \<open>J\<^sub>1 \<ge> 0\<close>, \<open>j\<^sub>0-j\<^sub>-\<^sub>1 = Joints(Red N)\<^bsub>J\<^sub>1\<^esub>\<close>, \<open>FirstNodes(Red N)\<^bsub>J\<^sub>1\<^esub> = j\<^sub>1-j\<^sub>-\<^sub>1\<close>;
    (2) \<open>Red(N)\<^bsub>0,j\<^sub>1-j\<^sub>-\<^sub>1\<^esub> = Red(N)\<^bsub>1,j\<^sub>1-j\<^sub>-\<^sub>1\<^esub>\<close>;
    (3) \<open>t\<^sub>2\<close>の各単項成分は \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close> 以上 (each monomial component of \<open>t\<^sub>2\<close> is
        \<open>\<ge> D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close>).
  Parts (1)–(2) are \<open>Trans\<close>-free and use only exposed defs (\<open>Adm\<close>, \<open>parent\<close>,
  \<open>seg\<close>, \<open>Red\<close>, \<open>Br\<close>, \<open>Lng\<close>, \<open>Joints\<close>, \<open>FirstNodes\<close>, \<open>entry\<close>, \<open>nextR\<close>, \<open>adm\<close>),
  hence transcribed.  Part (3) is DEFERRED: it refers to the unexposed internal
  \<open>Trans\<close>-recursion term \<open>t\<^sub>2\<close> (and "monomial component" of it).  BLOCKING
  SYMBOL: \<open>t\<^sub>2\<close>.  Modelling: \<open>Joints\<close>/\<open>FirstNodes\<close> indexing follows §6.4
  (lists indexed by \<open>! J\<^sub>1\<close>); \<open>Red(N)\<^bsub>i,k\<^esub> = entry (Red N) i k\<close>.\<close>

lemma p_8_5_Joints_FirstNodes_basic:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
    and "j0 \<equiv> parent M 0 (Lng M - 1)"
  assumes "M \<in> ST_PS" "M \<in> PT_PS"
    and "nextR M 1 j0 j1"
    and "\<not> adm M j0"
    and "j0 < j1 - 1"
  shows \<comment> \<open>(1)\<close>
        "Lng (Br (Red (seg M (Adm M j0) j1))) \<ge> 1"  \<comment> \<open>article \<open>J\<^sub>1 \<ge> 0\<close> with \<open>J\<^sub>1 = Lng(Br(Red N))-1\<close>\<close>
    and "j0 - Adm M j0
           = Joints (Red (seg M (Adm M j0) j1)) ! (Lng (Br (Red (seg M (Adm M j0) j1))) - 1)"
    and "FirstNodes (Red (seg M (Adm M j0) j1)) ! (Lng (Br (Red (seg M (Adm M j0) j1))) - 1)
           = j1 - Adm M j0"
    and \<comment> \<open>(2)\<close>
        "entry (Red (seg M (Adm M j0) j1)) 0 (j1 - Adm M j0)
           = entry (Red (seg M (Adm M j0) j1)) 1 (j1 - Adm M j0)"
  unfolding j1_def j0_def
  apply (rule m_8_5_Joints_FirstNodes_basic(1)[OF assms(3) assms(4)
        assms(5)[unfolded j1_def j0_def] assms(6)[unfolded j0_def]
        assms(7)[unfolded j1_def j0_def]])
  apply (rule m_8_5_Joints_FirstNodes_basic(2)[OF assms(3) assms(4)
        assms(5)[unfolded j1_def j0_def] assms(6)[unfolded j0_def]
        assms(7)[unfolded j1_def j0_def]])
  apply (rule m_8_5_Joints_FirstNodes_basic(3)[OF assms(3) assms(4)
        assms(5)[unfolded j1_def j0_def] assms(6)[unfolded j0_def]
        assms(7)[unfolded j1_def j0_def]])
  apply (rule m_8_5_Joints_FirstNodes_basic(4)[OF assms(3) assms(4)
        assms(5)[unfolded j1_def j0_def] assms(6)[unfolded j0_def]
        assms(7)[unfolded j1_def j0_def]])
  done

end
