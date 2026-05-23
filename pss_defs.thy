theory pss_defs
  imports Main
begin

text \<open>
  Formalization of the definitions in P進大好きbot's article
  "ペア数列の停止性" (Termination of the pair sequence system),
  巨大数研究 Wiki.

  This file contains ONLY the formalized *definitions* of the article
  (the 記法 / 定式化 / 前者関数 / 基本列 / ペア数列システム sections, and
  later sections as they are added).  Definitions are shared between the
  faithful statement file @{file "pss_paper.thy"} and the mechanized-proof
  file @{file "pss_mechanized.thy"}.

  Traceability: every definition is tagged with the article section number
  (§) and the original Japanese name, so it can be matched against
  @{file "tmp/content.md"} (the extracted article text).
\<close>

section \<open>§4 記法 (Notation)\<close>

text \<open>
  An \<open>A\<close>-valued array is an element of \<open>A\<^sup>n\<close>; we model it as a HOL list.
  \<open>Lng a\<close> (the length) is @{const length}.  The empty array \<open>()\<close> is @{term "[]"}.
  We model the binary concatenation \<open>\<oplus>\<^sub>A\<close> as list append @{term "(@)"} and the
  iterated \<open>\<Oplus>\<^sub>A\<close> as @{const concat}.

  NOTE on faithfulness: several definitions below are modelling choices, not
  verbatim transcriptions (e.g. \<open>\<le>\<^sub>M\<close> is given as a reflexive-transitive
  closure rather than via the article's explicit chain).  Lemmas asserting
  that these coincide with the article's literal definitions are collected in
  the "Faithfulness lemmas (忠実性補題)" section of @{file "pss_mechanized.thy"}.
\<close>

abbreviation Lng :: "'a list \<Rightarrow> nat" where
  "Lng xs \<equiv> length xs"


section \<open>§5 定式化 (Formulation)\<close>

text \<open>
  A pair sequence (ペア数列) is a non-empty \<open>(\<nat> \<times> \<nat>)\<close>-valued array.
  \<open>T\<^sub>P\<^sub>S\<close> is the set of all pair sequences.
\<close>

type_synonym pairseq = "(nat \<times> nat) list"

definition T_PS :: "pairseq set" where
  "T_PS = {M. M \<noteq> []}"

text \<open>\<open>Idx(M)\<close>: the set of indices \<open>(i,j)\<close> with \<open>i \<in> {0,1}\<close>, \<open>j < Lng M\<close>.\<close>

definition Idx :: "pairseq \<Rightarrow> (nat \<times> nat) set" where
  "Idx M = {(i,j). i \<in> {0,1} \<and> j < Lng M}"

text \<open>\<open>M\<^bsub>i,j\<^esub>\<close>: the \<open>i\<close>-th component of the \<open>j\<close>-th pair.\<close>

definition entry :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "entry M i j = (if i = 0 then fst (M ! j) else snd (M ! j))"


subsection \<open>§5.1 親子関係 (Parent-child relation)\<close>

text \<open>
  The article defines two relations \<open>(i\<^sub>0,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (i\<^sub>1,j\<^sub>1)\<close> and
  \<open>(i\<^sub>0,j\<^sub>0) \<le>\<^sub>M (i\<^sub>1,j\<^sub>1)\<close> simultaneously by recursion.  Both require
  \<open>i\<^sub>0 = i\<^sub>1\<close>, so we index them by the (single) row \<open>i \<in> {0,1}\<close>.  The recursion
  is in fact stratified by the row:

    \<^item> row 0 \<open><\<^sup>Next\<close> depends only on \<open>M\<close>;
    \<^item> row 0 \<open>\<le>\<close> is the reflexive-transitive closure of row 0 \<open><\<^sup>Next\<close>;
    \<^item> row 1 \<open><\<^sup>Next\<close> depends on row 0 \<open>\<le>\<close>;
    \<^item> row 1 \<open>\<le>\<close> is the reflexive-transitive closure of row 1 \<open><\<^sup>Next\<close>.

  \<open>\<le>\<^sub>M\<close> is faithful to the article's chain definition: a chain \<open>a\<close> of length
  \<open>1\<close> gives reflexivity (with both endpoints in \<open>Idx\<close>), and longer chains give
  the transitive closure of \<open><\<^sup>Next\<close>.
\<close>

definition nextrel0 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextrel0 M j0 j1 \<longleftrightarrow>
     j0 < Lng M \<and> j1 < Lng M \<and> j0 < j1 \<and>
     entry M 0 j0 < entry M 0 j1 \<and>
     (\<forall>j. j0 < j \<and> j < j1 \<longrightarrow> entry M 0 j \<ge> entry M 0 j1)"

definition le0 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "le0 M j0 j1 \<longleftrightarrow> j0 < Lng M \<and> j1 < Lng M \<and> (nextrel0 M)\<^sup>*\<^sup>* j0 j1"

definition nextrel1 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextrel1 M j0 j1 \<longleftrightarrow>
     j0 < Lng M \<and> j1 < Lng M \<and> j0 < j1 \<and>
     entry M 1 j0 < entry M 1 j1 \<and>
     le0 M j0 j1 \<and>
     (\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j \<ge> entry M 1 j1)"

definition le1 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "le1 M j0 j1 \<longleftrightarrow> j0 < Lng M \<and> j1 < Lng M \<and> (nextrel1 M)\<^sup>*\<^sup>* j0 j1"

text \<open>Unified relations indexed by the row \<open>i\<close>.\<close>

definition nextR :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
    \<comment> \<open>\<open>nextR M i j0 j1\<close> models \<open>(i,j0) <\<^bsub>M\<^esub>\<^sup>Next (i,j1)\<close>\<close> where
  "nextR M i j0 j1 = (if i = 0 then nextrel0 M j0 j1 else nextrel1 M j0 j1)"

definition leR :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
    \<comment> \<open>\<open>leR M i j0 j1\<close> models \<open>(i,j0) \<le>\<^sub>M (i,j1)\<close>\<close> where
  "leR M i j0 j1 = (if i = 0 then le0 M j0 j1 else le1 M j0 j1)"


subsection \<open>§5.2 前者関数 (Predecessor functions)\<close>

text \<open>\<open>Pred M\<close>: drop the last pair if \<open>Lng M > 1\<close>, otherwise the identity.\<close>

definition Pred :: "pairseq \<Rightarrow> pairseq" where
  "Pred M = (if Lng M \<le> 1 then M else butlast M)"

text \<open>\<open>Derp M\<close>: drop the first pair (codomain \<open>T\<^sub>P\<^sub>S \<union> {()}\<close>).\<close>

definition Derp :: "pairseq \<Rightarrow> pairseq" where
  "Derp M = tl M"


subsection \<open>§5.3 基本列 (Fundamental sequence, \<open>operator[]\<close>)\<close>

text \<open>
  \<open>i\<^sub>1 = max {i \<in> {0,1} | M\<^bsub>i,j\<^sub>1\<^esub> > 0}\<close>, well-defined when \<open>M\<^bsub>j\<^sub>1\<^esub> \<noteq> (0,0)\<close>.
\<close>

definition idx1 :: "pairseq \<Rightarrow> nat \<Rightarrow> nat" where
  "idx1 M j1 = (if entry M 1 j1 > 0 then 1 else 0)"

text \<open>The (unique, when it exists) parent \<open>j\<^sub>0\<close> of \<open>j\<^sub>1\<close> in row \<open>i\<close>.\<close>

definition hasParent :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hasParent M i j1 \<longleftrightarrow> (\<exists>!j0. nextR M i j0 j1)"

definition parent :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "parent M i j1 = (THE j0. nextR M i j0 j1)"

text \<open>
  \<open>M[n]\<close>, the fundamental sequence.  Faithful transcription of §5.3:
  with \<open>j\<^sub>1 = Lng M - 1\<close>,
    \<^item> if \<open>j\<^sub>1 = 0\<close>: \<open>M[n] = M\<close>;
    \<^item> if \<open>M\<^bsub>j\<^sub>1\<^esub> = (0,0)\<close>: \<open>M[n] = Pred M\<close>;
    \<^item> if no unique parent in row \<open>i\<^sub>1\<close>: \<open>M[n] = Pred M\<close>;
    \<^item> otherwise \<open>M[n] = G \<oplus> \<Oplus> B\<close> with \<open>G = (M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>0-1\<^esup>\<close> and
      \<open>B\<^sub>k = ((M\<^bsub>0,j\<^esub>+k\<delta>\<^sub>0, M\<^bsub>1,j\<^esub>+k\<delta>\<^sub>1))\<^bsub>j=j\<^sub>0\<^esub>\<^bsup>j\<^sub>1-1\<^esup>\<close> for \<open>k = 0..n-1\<close>.
  Here \<open>\<delta>\<^sub>i = M\<^bsub>i,j\<^sub>1\<^esub> - M\<^bsub>i,j\<^sub>0\<^esub>\<close> for \<open>i < i\<^sub>1\<close> and \<open>\<delta>\<^sub>i = 0\<close> for \<open>i \<ge> i\<^sub>1\<close>;
  since \<open>i\<^sub>1 \<le> 1\<close> we always have \<open>\<delta>\<^sub>1 = 0\<close>, and \<open>\<delta>\<^sub>0 \<noteq> 0\<close> only when \<open>i\<^sub>1 = 1\<close>.
\<close>

definition oper :: "pairseq \<Rightarrow> nat \<Rightarrow> pairseq"  ("_[_]" [90,0] 91) where
  "M[n] =
     (let j1 = Lng M - 1 in
      if j1 = 0 then M
      else if entry M 0 j1 = 0 \<and> entry M 1 j1 = 0 then Pred M
      else let i1 = idx1 M j1 in
        if \<not> hasParent M i1 j1 then Pred M
        else let j0 = parent M i1 j1;
                 d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0);
                 d1 = (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0)
             in take j0 M @
                concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1))
                                      [j0..<j1])
                            [0..<n]))"


subsection \<open>§5.4 ペア数列システム (Pair sequence system)\<close>

text \<open>
  A map \<open>f : \<nat>\<^sub>+ \<to> \<nat>\<^sub>+\<close> is fixed (mainly \<open>f(n) = n+1\<close> or \<open>f(n) = n\<^sup>2\<close>); we
  carry it as an explicit parameter.  One expansion step on \<open>(M,n)\<close> with
  \<open>Lng M > 1\<close> sends \<open>M\<close> to \<open>M[n]\<close> and \<open>n\<close> to \<open>f n\<close> (note: by §5.3, \<open>M[n]\<close>
  already equals \<open>Pred M\<close> in the two degenerate sub-cases, so a single
  uniform step is faithful to the article's case split).
\<close>

text \<open>
  \<open>F\<^sub>M(n)\<close> as a (possibly non-terminating, tail-recursive) value.
  Where the recursion does not terminate the value is unspecified.
\<close>

partial_function (tailrec) Fval :: "(nat \<Rightarrow> nat) \<Rightarrow> pairseq \<Rightarrow> nat \<Rightarrow> nat" where
  "Fval f M n = (if Lng M \<le> 1 then f n else Fval f (M[n]) (f n))"

text \<open>
  \<open>Dom(F)\<close> as the set where the recursion terminates, defined inductively
  (the least set closed under the base case and the expansion step).
\<close>

inductive Fdom :: "(nat \<Rightarrow> nat) \<Rightarrow> pairseq \<Rightarrow> nat \<Rightarrow> bool" for f where
  Fdom_base: "Lng M = 1 \<Longrightarrow> Fdom f M n"
| Fdom_step: "\<lbrakk>Lng M > 1; Fdom f (M[n]) (f n)\<rbrakk> \<Longrightarrow> Fdom f M n"

text \<open>
  CORRECTION NOTE (apparent article typo; see @{file "amendments.md"} entry A1).
  The §5.4 proposition 命題（F_M と基本列の関係） uses the second argument n
  (F_M(n) = F_{M[n]}(n)), but this recursive definition of F uses f(n)
  (F_M(n) = F_{M[n]}(f(n))).  For Lng M = 1 the article's n is correct
  (M[n] = M), but for Lng M > 1 it must be f(n); no single fixed argument works
  for both.  We formalize the corrected non-trivial case (Lng M > 1, argument
  f(n)) as p_5_4_F_oper_dom / p_5_4_F_oper_val in @{file "pss_paper.thy"}.
\<close>

end
