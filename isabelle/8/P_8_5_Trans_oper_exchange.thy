theory P_8_5_Trans_oper_exchange
  imports Support_8_C
begin

subsection \<open>§8.5 条件(V)の下での展開規則\<close>

text \<open>This subsection (article ## 条件(V)の下での展開規則) builds up to the exchange
  relation between the translation \<open>Trans\<close> and the pair-sequence fundamental
  sequence under condition (V).

  COMMON SETUP / NOTATION (same as §8.3/§8.4, all from the \<open>Trans\<close> recursion):
    \<^item> \<open>j\<^sub>1 = Lng M - 1\<close>, the rightmost index;
    \<^item> \<open>j\<^sub>0\<close> = the row-0 nearest ancestor of \<open>j\<^sub>1\<close> (\<open>= parent M 0 j\<^sub>1\<close>);
    \<^item> \<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close> (admissibilization of \<open>j\<^sub>0\<close>);
    \<^item> "条件(V)" \<open>= transCondV\<close>;
    \<^item> the index \<open>m\<^sub>n\<close> is \<open>n-1\<close> when \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible (\<open>adm M j\<^sub>0\<close>) and
      \<open>n\<close> when \<open>j\<^sub>0\<close> is non-\<open>M\<close>-admissible;
    \<^item> the Buchholz-side fundamental sequence \<open>t[k]\<close> is \<open>operB t (numBT k)\<close>, and
      \<open>< / \<le>\<close> on \<open>T\<^bsub>B\<^esub>\<close> are \<open>lessBT\<close>/\<open>leBT\<close>.

  FAITHFULNESS / DEFERRAL.  As in §8.4, several auxiliary §8.5 lemmas state
  relations among the \<^emph>\<open>internal symbols of the \<open>Trans\<close> recursion\<close> (\<open>t\<^sub>2\<close>, \<open>c\<^sub>2\<close>,
  the scb-strings \<open>s\<^sub>1\<close>/\<open>b\<^sub>1\<close>/\<open>s'\<^sub>1\<close>/\<open>b'\<^sub>1\<close>/\<open>s'\<^sub>0\<close>/\<open>b'\<^sub>0\<close>, the auxiliary \<open>t'\<close>) which
  are \<^bold>\<open>not\<close> exposed as separate Isabelle functions (cf. the deferred §7.3
  命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）).  Those are \<^bold>\<open>deferred\<close> (documented as \<open>text\<close>
  notes with the blocking symbols); only the externally-statable facts are
  transcribed as \<open>sorry\<close> lemmas.\<close>

text \<open>命題（条件(V)の下での\<open>Trans\<close>と基本列の交換関係） (§8.5, article 5153): for
  \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, using the symbols of the \<open>Trans\<close>
  recursion, set \<open>m\<^sub>n := n-1\<close> if \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible and \<open>m\<^sub>n := n\<close> if \<open>j\<^sub>0\<close> is
  non-\<open>M\<close>-admissible; if \<open>j\<^sub>1 > 1\<close> and \<open>M\<close> satisfies condition (V), then:
    (1) \<open>Trans(M[n]) \<le> Trans(M)[m\<^sub>n]\<close>;
    (2) \<open>Trans(M[n]) < Trans(M)\<close>;
    (3) \<open>Trans(M)[m\<^sub>n] \<le> Trans(M[n+1])\<close>.
  Here \<open>Trans(M)[k] = operB (Trans M) (numBT k)\<close> is the Buchholz-side
  fundamental sequence.  The only setup symbol that enters the conclusions is
  \<open>j\<^sub>0 = parent M 0 (Lng M - 1)\<close> (exposed, via the case split on \<open>adm M j\<^sub>0\<close>
  that defines \<open>m\<^sub>n\<close>); the conclusions are otherwise symbol-free, hence
  transcribable.\<close>

lemma p_8_5_Trans_oper_exchange:
  fixes M :: pairseq and n :: nat
  defines "j0 \<equiv> parent M 0 (Lng M - 1)"
  defines "mn \<equiv> (if adm M j0 then n - 1 else n)"
  assumes "M \<in> ST_PS" "M \<in> PT_PS" "n \<ge> 1"
    and "Lng M - 1 > 1"
    and "transCondV M"
  shows "leBT (Trans (M[n])) (operB (Trans M) (numBT mn))"
    and "lessBT (Trans (M[n])) (Trans M)"
    and "leBT (operB (Trans M) (numBT mn)) (Trans (M[n+1]))"
  unfolding j0_def mn_def
  apply (rule y3h_p_8_5_Trans_oper_exchange(1)[OF assms(3) assms(4) assms(5) assms(6) assms(7)])
  apply (rule y3h_p_8_5_Trans_oper_exchange(2)[OF assms(3) assms(4) assms(5) assms(6) assms(7)])
  apply (rule y3h_p_8_5_Trans_oper_exchange(3)[OF assms(3) assms(4) assms(5) assms(6) assms(7)])
  done

end
