theory Frontier_7_014
  imports Support_7_010
begin

text \<open>Stronger pre/post split (Front B, conjunct 2): like \<open>rnsub_flat_pre_post\<close>
  but the trailing principal \<open>D\<^sub>u a\<close> is replaced \<^emph>\<open>wholesale\<close> (both index \<open>u\<close>
  and argument \<open>a\<close> free), so the same \<open>pre\<close>/\<open>post\<close> serve every principal appended
  after \<open>butlast xs\<close>.  \<open>pre\<close>/\<open>post\<close> depend only on \<open>butlast xs\<close>.\<close>

lemma addscb_flat_pre_post2:
  assumes "xs \<noteq> []"
  shows "\<exists>pre post. (\<forall>x \<in> set post. x = RP)
            \<and> (\<forall>u a. flatBT (Trm (butlast xs @ [DB u a]))
                      = pre @ (Dsym u # flatBT a) @ post)"
proof (cases "butlast xs")
  case Nil
  \<comment> \<open>single principal: \<open>butlast xs = []\<close>, so \<open>pre = post = []\<close>.\<close>
  show ?thesis
    by (rule exI[of _ "[]"], rule exI[of _ "[]"]) (simp add: Nil)
next
  case (Cons p ps)
  \<comment> \<open>multi: the wrap is \<open>LP # \<dots> @ [RP]\<close>, last component peeled off \<open>mid\<close>.\<close>
  define midpre where "midpre = concat (map (\<lambda>r. CM # flatBP r) ps)"
  define pre where "pre = LP # flatBP p @ midpre @ [CM]"
  define post where "post = [RP::Sym]"
  have post_RP: "\<forall>x \<in> set post. x = RP" unfolding post_def by simp
  have body: "\<And>u a. flatBT (Trm (butlast xs @ [DB u a]))
                  = pre @ (Dsym u # flatBT a) @ post"
  proof -
    fix u a
    have "flatBT (Trm (p # (ps @ [DB u a])))
          = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB u a]))) @ [RP]"
      by (rule rnsub_flat_multi) simp
    also have "concat (map (\<lambda>r. CM # flatBP r) (ps @ [DB u a]))
             = midpre @ CM # flatBP (DB u a)"
      unfolding midpre_def by simp
    finally show "flatBT (Trm (butlast xs @ [DB u a]))
                  = pre @ (Dsym u # flatBT a) @ post"
      using Cons unfolding pre_def post_def by simp
  qed
  show ?thesis
    by (rule exI[of _ pre], rule exI[of _ post]) (use post_RP body in blast)
qed

end
