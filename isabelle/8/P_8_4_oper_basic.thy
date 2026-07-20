theory P_8_4_oper_basic
  imports Support_8_C
begin

text \<open>補題（条件(III)～(V)の下での右端の置き換えと\<open>Trans\<close>の関係） (§8.4): DEFERRED.
  The statement names a unique \<open>(s,b) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>2\<close> whose scb-decompositions of
  \<open>Trans(N')\<close>/\<open>Trans(L')\<close> are described through the \<^bold>\<open>internal \<open>Trans\<close>-recursion
  symbols\<close> \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close>, \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>2\<^esub> 0\<close>, \<open>t\<^sub>2\<close>, \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub>\<close>, and the
  cases split on "\<open>j\<^sub>-\<^sub>2 = j\<^sub>0\<close> / \<open>j\<^sub>0\<close> (non-)\<open>M\<close>-admissible".  The \<open>Trans\<close>-internal
  \<open>t\<^sub>2\<close> (and the case-shaped \<open>c\<close>-component \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub>(t\<^sub>2 + D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> 0)\<close>) is not
  exposed as a separate function (cf. the deferred §7.3 \<open>c\<^sub>1\<close>/\<open>c\<^sub>2\<close> proposition),
  so this lemma cannot be stated without inventing that exposure.  BLOCKING
  SYMBOLS: \<open>t\<^sub>2\<close>, the conditional \<open>c\<close>-shape.\<close>

text \<open>補題（条件(III)～(VI)の下での展開規則の基本性質） (§8.4): partially DEFERRED.
  With \<open>N' = (M\<^sub>j)\<^bsub>j=j\<^sub>-\<^sub>2\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close>, \<open>L'\<close> the \<open>M[n+1]\<close>-derived sequence, and
  \<open>L\<^sub>n = M[n] \<oplus> ((M\<^bsub>0,j\<^sub>-\<^sub>2\<^esub>+n(M\<^bsub>0,j\<^sub>1\<^esub>-M\<^bsub>0,j\<^sub>-\<^sub>2\<^esub>), M\<^bsub>1,j\<^sub>-\<^sub>2\<^esub>)))\<close>, parts (1)–(4)
  are stated via exposed defs (parent ordering, reducedness/monomiality of
  \<open>L\<^sub>n\<close>, agreement of \<open>\<le>\<^bsub>M\<^esub>\<close>/\<open>\<le>\<^bsub>L\<^sub>1\<^esub>\<close> off \<open>(1,j\<^sub>1)\<close>, and conditions of \<open>L\<^sub>1\<close>).
  Part (5), however, names \<open>(s',b')\<close> via scb-decompositions involving the
  internal symbols \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>2\<^esub> 0\<close>, \<open>Trans(L')\<close>, \<open>Trans(Pred N')\<close>.  Parts (1)–(4)
  are transcribable but require building the article-internal sequences \<open>L'\<close>/
  \<open>L\<^sub>n\<close> explicitly; they are interleaved with (5) in a single article lemma whose
  load-bearing content is (5).  DEFERRED as a unit alongside the dependent
  scb-decomposition lemmas.  BLOCKING SYMBOLS (part 5): \<open>s'\<close>/\<open>b'\<close>,
  \<open>Trans(L')\<close>/\<open>Trans(Pred N')\<close> as scb-components.\<close>

text \<open>補題（条件(III)～(VI)の下での\<open>Trans\<close>とscb分解の関係） (§8.4): DEFERRED.
  Names a unique \<open>(s',b')\<close> such that \<open>(s', Trans(N), b')\<close> is the \<^bold>\<open>第\<open>1\<close>種\<close>
  (kind-1, \<open>scb_kind1\<close>) scb-decomposition of \<open>Trans M\<close>, with
  \<open>N = (M\<^sub>j)\<^bsub>j=j\<^sub>-\<^sub>3\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close>, \<open>j\<^sub>-\<^sub>3 = Adm M j\<^sub>-\<^sub>2\<close>.  This is in principle statable
  with \<open>scb_kind1\<close> and exposed defs (\<open>seg\<close>, \<open>Adm\<close>, \<open>parent\<close>, \<open>Trans\<close>), BUT it
  relies on the article-internal \<open>j\<^sub>-\<^sub>2 = parent M 1 j\<^sub>1\<close> setup AND its proof and
  downstream use are entangled with the deferred scb-component lemmas above.
  DEFERRED to keep the §8.4 scb-decomposition cluster a single coherent unit
  (per agent-workflow: do not split an interdependent cluster).  POSSIBLE LATER
  STATEMENT: \<open>\<exists>!sb. scb_kind1 (Trans M) (fst sb) (flatBT (Trans (seg M (Adm M
  (parent M 1 (Lng M-1))) (Lng M-1)))) (snd sb)\<close>.\<close>

text \<open>補題（条件(III)～(V)の下での切片のscb分解） (§8.4): DEFERRED.
  Names \<open>(s'\<^sub>1,b'\<^sub>1)\<close> via scb-decompositions stated through the internal symbols
  \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>1\<^esub> s'\<^sub>1\<close>, \<open>c\<^sub>2\<close>, \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>2\<^esub> 0\<close>, \<open>Trans(Pred N') = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>2\<^esub> t\<^sub>2\<close>.
  The components \<open>c\<^sub>2\<close> and \<open>t\<^sub>2\<close> are unexposed \<open>Trans\<close>-recursion internals (cf.
  deferred §7.3 \<open>c\<^sub>1\<close>/\<open>c\<^sub>2\<close>).  BLOCKING SYMBOLS: \<open>c\<^sub>2\<close>, \<open>t\<^sub>2\<close>, \<open>s'\<^sub>1\<close>/\<open>b'\<^sub>1\<close>.\<close>

text \<open>補題（条件(III)～(V)の下での各種scb分解） (§8.4): DEFERRED.
  Parts (1)–(3) restate the previous (deferred) lemma's \<open>c\<^sub>2\<close>/\<open>t\<^sub>2\<close> scb-data;
  parts (4)–(5) give closed forms for \<open>Trans(L\<^sub>n)\<close> and \<open>Trans(M[n])\<close> as
  \<open>s\<^sub>1 D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>1\<^esub> (s'\<^sub>1 D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>2\<^esub>)\<^sup>n 0 (b'\<^sub>1)\<^sup>n b\<^sub>1\<close> etc., entirely in terms of the
  internal scb-strings \<open>s\<^sub>1\<close>/\<open>b\<^sub>1\<close>/\<open>s'\<^sub>1\<close>/\<open>b'\<^sub>1\<close> and \<open>t\<^sub>2\<close>.  BLOCKING SYMBOLS:
  \<open>s\<^sub>1\<close>, \<open>b\<^sub>1\<close>, \<open>s'\<^sub>1\<close>, \<open>b'\<^sub>1\<close>, \<open>t\<^sub>2\<close> (string concatenation/exponentiation of
  unexposed \<open>Trans\<close>-internal strings).\<close>

text \<open>補題（条件(III)か(IV)の下での各種scb分解） (§8.4): DEFERRED.
  Names a unique 6-tuple \<open>(s'\<^sub>0,s'\<^sub>1,s'\<^sub>2,b'\<^sub>2,b'\<^sub>1,b'\<^sub>0) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>6\<close> describing
  scb-decompositions of \<open>Trans M\<close>, \<open>Trans(Pred N)\<close>, \<open>Trans N\<close>, \<open>c\<^sub>2\<close>,
  \<open>Trans(Pred N')\<close>, \<open>Trans N'\<close>, \<open>Trans L'\<close> and closed forms for \<open>Trans(L\<^sub>n)\<close>,
  \<open>Trans(M[n])\<close> — all through the unexposed internal symbols \<open>c\<^sub>1\<close>, \<open>c\<^sub>2\<close> and the
  scb-strings.  BLOCKING SYMBOLS: \<open>s'\<^sub>0\<dots>b'\<^sub>0\<close>, \<open>c\<^sub>1\<close>, \<open>c\<^sub>2\<close>.\<close>

text \<open>命題 / 補題（条件(III)か(IV)の下での基本列の基本性質） (§8.4): for
  \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>, \<open>n \<in> \<nat>\<^sub>+\<close>, with \<open>j\<^sub>1 = Lng M - 1\<close> and \<open>j\<^sub>-\<^sub>2\<close> the
  unique \<open>(1,\<cdot>) <\<^bsub>M\<^esub>\<^sup>Next (1,j\<^sub>1)\<close>-parent (\<open>hasParent M 1 j\<^sub>1\<close>), if \<open>j\<^sub>1 > 1\<close>
  and \<open>M\<close> satisfies condition (III) or (IV), then:
    (1) \<open>M[n] = M[n+1][1]\<^bsup>j\<^sub>1-j\<^sub>-\<^sub>2\<^esup>\<close> (iterate the \<open>[1]\<close>-fundamental-sequence
        \<open>j\<^sub>1-j\<^sub>-\<^sub>2\<close> times);
    (2) \<open>Trans(M)[n-1] = Trans(M[n+1][1]\<^bsup>j\<^sub>1-1-j\<^sub>-\<^sub>2\<^esup>)\<close>;
    (3) there exist \<open>(s',c'\<^sub>1,c'\<^sub>2,b')\<close> with \<open>c'\<^sub>1,c'\<^sub>2\<close> principal,
        \<open>c'\<^sub>1 < c'\<^sub>2\<close> (\<open>lessBT\<close>), \<open>(s',c'\<^sub>1,b')\<close> an scb-decomposition of
        \<open>Trans(M[n])\<close>, and \<open>(s',c'\<^sub>2,b')\<close> an scb-decomposition of \<open>Trans(M)[n]\<close>.
  Parts (1)–(2) use \<open>j\<^sub>-\<^sub>2 = parent M 1 j\<^sub>1\<close> (exposed) and the iterated
  fundamental sequence; part (3) is purely existential over \<open>(s',c'\<^sub>1,c'\<^sub>2,b')\<close>
  (so no internal-symbol exposure is needed) — hence the whole lemma is
  transcribable.  Here \<open>c'\<^sub>i\<close> principal = \<open>Lng (PB c'\<^sub>i) = 1\<close>, and the
  scb-decomposition uses \<open>scb_decomp\<close> on the flattened component.\<close>

lemma p_8_4_oper_basic:
  assumes "M \<in> ST_PS" "M \<in> PT_PS" "n \<ge> 1"
    and "hasParent M 1 (Lng M - 1)"
    and "Lng M - 1 > 1"
    and "transCondIII M \<or> transCondIV M"
  shows "M[n] = ((\<lambda>N. N[1]) ^^ ((Lng M - 1) - parent M 1 (Lng M - 1))) (M[n+1])"
    and "operB (Trans M) (numBT (n - 1))
           = Trans (((\<lambda>N. N[1]) ^^ ((Lng M - 1) - 1 - parent M 1 (Lng M - 1))) (M[n+1]))"
    and "\<exists>s c1 c2 b.
            Lng (PB c1) = 1 \<and> Lng (PB c2) = 1 \<and> lessBT c1 c2
          \<and> scb_decomp (Trans (M[n])) s (flatBT c1) b
          \<and> scb_decomp (operB (Trans M) (numBT n)) s (flatBT c2) b"
  apply (rule m_8_4_oper_basic_part1[OF assms])
  apply (rule y3m_p_8_4_oper_basic_part2_full[OF assms(1) assms(2) assms(4)
        assms(5) assms(6) assms(3), unfolded s84x_jm2_def])
  apply (rule y3h_p_8_4_oper_basic(2)[OF assms])
  done

end
