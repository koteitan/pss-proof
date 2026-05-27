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
  CORRECTION NOTE (apparent article typo; see @{file "corrections.md"} entry A1).
  The §5.4 proposition 命題（F_M と基本列の関係） uses the second argument n
  (F_M(n) = F_{M[n]}(n)), but this recursive definition of F uses f(n)
  (F_M(n) = F_{M[n]}(f(n))).  For Lng M = 1 the article's n is correct
  (M[n] = M), but for Lng M > 1 it must be f(n); no single fixed argument works
  for both.  We formalize the corrected non-trivial case (Lng M > 1, argument
  f(n)) as p_5_4_F_oper_dom / p_5_4_F_oper_val in @{file "pss_paper.thy"}.
\<close>


section \<open>§6 ペア数列の基本性質 (Basic properties)\<close>

subsection \<open>§6.1 最上行のインクリメント (IncrFirst)\<close>

text \<open>\<open>IncrFirst M\<close>: increment the top row (row 0) of every pair.\<close>

definition IncrFirst :: "pairseq \<Rightarrow> pairseq" where
  "IncrFirst M = map (\<lambda>p. (Suc (fst p), snd p)) M"

text \<open>The inclusive slice \<open>(M\<^sub>j)\<^bsub>j=a\<^esub>\<^bsup>b\<^esup>\<close> (length \<open>b - a + 1\<close> when \<open>a \<le> b\<close>).\<close>

definition seg :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pairseq" where
  "seg M a b = map (\<lambda>j. M ! j) [a..<Suc b]"


subsection \<open>§6.2 単項性 (zero- / mono- / multi-term)\<close>

text \<open>\<open>zeroT M\<close> (零項): \<open>Lng M = 1\<close> and \<open>M\<^bsub>1,0\<^esub> = 0\<close>.\<close>

definition zeroT :: "pairseq \<Rightarrow> bool" where
  "zeroT M \<longleftrightarrow> Lng M = 1 \<and> entry M 1 0 = 0"

text \<open>\<open>monoT M\<close> (単項): not zero, and \<open>(0,0) \<le>\<^sub>M (0, Lng M - 1)\<close>.\<close>

definition monoT :: "pairseq \<Rightarrow> bool" where
  "monoT M \<longleftrightarrow> \<not> zeroT M \<and> leR M 0 0 (Lng M - 1)"

text \<open>\<open>multiT M\<close> (複項): not zero and not mono.\<close>

definition multiT :: "pairseq \<Rightarrow> bool" where
  "multiT M \<longleftrightarrow> \<not> zeroT M \<and> \<not> monoT M"

definition ZT_PS :: "pairseq set" where "ZT_PS = {M. M \<in> T_PS \<and> zeroT M}"
definition PT_PS :: "pairseq set" where "PT_PS = {M. M \<in> T_PS \<and> monoT M}"
definition MT_PS :: "pairseq set" where "MT_PS = {M. M \<in> T_PS \<and> multiT M}"

text \<open>
  \<open>P M\<close> (§6.2): decompose \<open>M\<close> into its non-multi (zero/mono) components.
  When \<open>M\<close> is multi, \<open>P M = P (prefix) @ [suffix]\<close> where the cut is at
  \<open>Pcut M\<close>, the least \<open>j\<^sub>0\<close> with \<open>0 < j\<^sub>0 \<le> Lng M - 1\<close> and
  \<open>(0,j\<^sub>0) \<le>\<^sub>M (0, Lng M - 1)\<close>.  The prefix is strictly shorter, so the
  recursion terminates.
\<close>

definition Pcut :: "pairseq \<Rightarrow> nat" where
  "Pcut M = (LEAST j. 0 < j \<and> j \<le> Lng M - 1 \<and> leR M 0 j (Lng M - 1))"

function P :: "pairseq \<Rightarrow> pairseq list" where
  "P M = (if multiT M \<and> 1 < Lng M
          then P (take (Pcut M) M) @ [drop (Pcut M) M]
          else [M])"
  by pat_completeness auto
termination
proof (relation "measure length")
  show "wf (measure length)" by simp
next
  fix M :: pairseq
  assume "multiT M \<and> 1 < Lng M"
  hence L: "1 < Lng M" by simp
  have wit: "0 < Lng M - 1 \<and> Lng M - 1 \<le> Lng M - 1 \<and> leR M 0 (Lng M - 1) (Lng M - 1)"
    using L by (auto simp: leR_def le0_def)
  have "Pcut M \<le> Lng M - 1" unfolding Pcut_def
    by (rule Least_le[where P = "\<lambda>j. 0 < j \<and> j \<le> Lng M - 1 \<and> leR M 0 j (Lng M - 1)", OF wit])
  hence "Pcut M < Lng M" using L by simp
  thus "(take (Pcut M) M, M) \<in> measure length" by simp
qed


subsection \<open>§6.3 許容性 (Admissibility)\<close>

text \<open>
  \<open>nadm M j\<close> (非\<open>M\<close>許容): \<open>j > Lng M\<close>, or both
  \<open>(1,j-1) <\<^bsub>M\<^esub>\<^sup>Next (1,j)\<close> and \<open>(1,j) <\<^bsub>M\<^esub>\<^sup>Next (1,j+1)\<close>.
\<close>

definition nadm :: "pairseq \<Rightarrow> nat \<Rightarrow> bool" where
  "nadm M j \<longleftrightarrow> j > Lng M \<or> (nextR M 1 (j - 1) j \<and> nextR M 1 j (j + 1))"

text \<open>\<open>adm M j\<close> (\<open>M\<close>許容): not non-admissible.\<close>

definition adm :: "pairseq \<Rightarrow> nat \<Rightarrow> bool" where
  "adm M j \<longleftrightarrow> \<not> nadm M j"

text \<open>\<open>AdmSet M\<close> (\<open>\<nat>\<^sub>M\<close>): the set of \<open>M\<close>-admissible naturals.\<close>

definition AdmSet :: "pairseq \<Rightarrow> nat set" where
  "AdmSet M = {j. adm M j}"

text \<open>\<open>Adm M j\<close> (\<open>Adm\<^sub>M(j)\<close>): the admissibilization of \<open>j\<close>.\<close>

definition Adm :: "pairseq \<Rightarrow> nat \<Rightarrow> nat" where
  "Adm M j = (if adm M j then j else Max {j'. adm M j' \<and> j' < j})"

text \<open>\<open>Marked\<close> (\<open>T\<^bsub>PS\<^esub>\<^sup>Marked\<close>): basepoint-marked pair sequences.\<close>

definition Marked :: "(pairseq \<times> nat) set" where
  "Marked = {(M,m). M \<in> T_PS \<and> adm M m \<and> leR M 0 m (Lng M - 1)}"


subsection \<open>§6.4 幹と枝 (Trunk and branches)\<close>

text \<open>
  \<open>IdxSum Q\<close>: for \<open>Q\<close> a list of pair sequences, the list of cumulative
  length-prefix sums \<open>(\<Sum>\<^bsub>k<J\<^esub> Lng Q\<^sub>k)\<^bsub>J=0\<^esub>\<^bsup>Lng Q\<^esup>\<close> (length \<open>Lng Q + 1\<close>).
\<close>

definition IdxSum :: "pairseq list \<Rightarrow> nat list" where
  "IdxSum Q = map (\<lambda>J. sum_list (map length (take J Q))) [0..<Suc (length Q)]"

text \<open>
  \<open>TrMax M\<close> (幹の右端): the largest \<open>j\<close> such that the row-1 chain
  \<open>(1,j') <\<^bsub>M\<^esub>\<^sup>Next (1,j'+1)\<close> holds for all \<open>j' < j\<close>.
\<close>

definition TrMax :: "pairseq \<Rightarrow> nat" where
  "TrMax M = Max {j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"

text \<open>\<open>Br M\<close> (枝): the \<open>P\<close>-decomposition of the segment to the right of the trunk.\<close>

definition Br :: "pairseq \<Rightarrow> pairseq list" where
  "Br M = (if TrMax M = Lng M - 1 then [] else P (seg M (TrMax M + 1) (Lng M - 1)))"

text \<open>\<open>FirstNodes M\<close>: the left endpoints (in \<open>M\<close>) of the branch components.\<close>

definition FirstNodes :: "pairseq \<Rightarrow> nat list" where
  "FirstNodes M = map (\<lambda>x. TrMax M + 1 + x) (IdxSum (Br M))"

text \<open>
  \<open>Joints M\<close>: for each branch component, the unique parent (in row 0, in \<open>M\<close>)
  of its first node.
\<close>

definition Joints :: "pairseq \<Rightarrow> nat list" where
  "Joints M = map (\<lambda>J. THE j. nextR M 0 j (FirstNodes M ! J)) [0..<length (Br M)]"


subsection \<open>§6.5 簡約化 (Reduction \<open>Red\<close>)\<close>

text \<open>\<open>diagSeq a b\<close>: the diagonal segment \<open>((j,j))\<^bsub>j=a\<^esub>\<^bsup>b\<^esup>\<close> (length \<open>b - a + 1\<close>).\<close>

definition diagSeq :: "nat \<Rightarrow> nat \<Rightarrow> pairseq" where
  "diagSeq a b = map (\<lambda>j. (j, j)) [a..<Suc b]"

text \<open>
  \<open>Red M\<close> (簡約化): faithful transcription of the recursive definition in §6.5.
  Case split (零項 / 複項 / 単項, the latter on \<open>M\<^sub>0 = (0,0)\<close> and on \<open>M\<^bsub>1,0\<^esub>\<close>):
    \<^item> \<open>M\<close> zero: \<open>Red M = ((0,0))\<close>.
    \<^item> \<open>M\<close> multi: \<open>Red M = \<Oplus>\<^bsub>J\<^esub> Red (P M\<^sub>J)\<close>.
    \<^item> \<open>M\<close> mono, \<open>M\<^sub>0 = (0,0)\<close> (so \<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>):
        \<^item> \<open>TrMax M = Lng M - 1\<close>: \<open>Red M = ((j,j))\<^bsub>j=m\<^sub>1\<^sub>0\<^esub>\<^bsup>m\<^sub>1\<^sub>0+(Lng M-1)\<^esup>\<close>;
        \<^item> else: \<open>Red M = ((j,j))\<^bsub>j=0\<^esub>\<^bsup>TrMax M\<^esup> \<oplus> \<Oplus>\<^bsub>J\<^esub> IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red N\<^sub>J)\<close>,
          where (encoding \<open>n\<^sub>J \<in> \<nat>\<union>{-1}\<close> via \<open>np = n\<^sub>J + 1 \<in> \<nat>\<close>)
          \<open>np = 0\<close> if \<open>(Br M\<^sub>J)\<^bsub>1,0\<^esub> = 0\<close> else \<open>np = Suc (THE j. (1,j) <\<^bsub>M\<^esub>\<^sup>Next (1, FirstNodes M\<^sub>J))\<close>,
          \<open>e\<^sub>J = Joints M\<^sub>J + 1 - np\<close>, \<open>N\<^sub>J = (m\<^sub>0\<^sub>0+Joints M\<^sub>J+1, m\<^sub>1\<^sub>0+np) \<oplus> Derp (Br M\<^sub>J)\<close>.
    \<^item> \<open>M\<close> mono, \<open>M\<^sub>0 \<noteq> (0,0)\<close>:
        \<^item> \<open>m\<^sub>1\<^sub>0 = 0\<close>: \<open>Red M = Red ((M\<^bsub>0,j\<^esub>-m\<^sub>0\<^sub>0, M\<^bsub>1,j\<^esub>))\<^bsub>j=0\<^esub>\<^bsup>Lng M-1\<^esup>\<close>;
        \<^item> \<open>m\<^sub>1\<^sub>0 > 0\<close>: with \<open>N = Red (((j,j))\<^bsub>j=0\<^esub>\<^bsup>m\<^sub>1\<^sub>0-1\<^esup> \<oplus> IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup>(M))\<close> and
          \<open>jN = Lng N - 1\<close>: if \<open>m\<^sub>1\<^sub>0 \<le> jN\<close> and \<open>(N\<^sub>j)\<^bsub>j=m\<^sub>1\<^sub>0\<^esub>\<^bsup>jN\<^esup> \<in> PT\<^sub>PS\<close>
          then \<open>Red M = (N\<^bsub>0,j\<^esub>-N\<^bsub>0,m\<^sub>1\<^sub>0\<^esub>+N\<^bsub>1,m\<^sub>1\<^sub>0\<^esub>, N\<^bsub>1,j\<^esub>)\<^bsub>j=m\<^sub>1\<^sub>0\<^esub>\<^bsup>jN\<^esup>\<close>, else \<open>Red M = M\<close>
          (the two \<open>= M\<close> fall-throughs \<^bold>\<open>[19]\<close>/\<^bold>\<open>[20]\<close> are dead branches, proved
          impossible later by §6.5 propositions, but are needed for totality).

  All recursive calls are on \<open>Red\<close>-free arguments (not nested), so the definition
  is accepted by \<open>function\<close>; termination (\<open>= Red_dom\<close>) is the §6.5 well-definedness
  proposition, deferred (transcribed as \<open>sorry\<close> in @{file "pss_paper.thy"}).
\<close>

function (domintros) Red :: "pairseq \<Rightarrow> pairseq" where
  "Red M =
   (if zeroT M then [(0, 0)]
    else if multiT M then concat (map Red (P M))
    else
      (let j1 = Lng M - 1; j1' = TrMax M;
           m00 = entry M 0 0; m10 = entry M 1 0 in
       if m00 = 0 \<and> m10 = 0 then
         (if j1' = j1 then diagSeq m10 (m10 + j1)
          else
            diagSeq 0 j1' @
            concat (map (\<lambda>J.
              (IncrFirst ^^ (Joints M ! J + 1
                  - (if entry (Br M ! J) 1 0 = 0 then 0
                     else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                (Red ((m00 + Joints M ! J + 1,
                       m10 + (if entry (Br M ! J) 1 0 = 0 then 0
                              else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                      # tl (Br M ! J))))
              [0..<Lng (Br M)]))
       else
         (if m10 = 0 then
            Red (map (\<lambda>j. (entry M 0 j - m00, entry M 1 j)) [0..<Suc j1])
          else
            (let N = Red (diagSeq 0 (m10 - 1) @ (IncrFirst ^^ m10) M);
                 jN = Lng N - 1 in
             if m10 \<le> jN \<and> seg N m10 jN \<in> PT_PS then
               map (\<lambda>j. (entry N 0 j - entry N 0 m10 + entry N 1 m10, entry N 1 j))
                   [m10..<Suc jN]
             else M))))"
  by pat_completeness auto


subsection \<open>§6.6 簡約性 (Reducedness)\<close>

text \<open>\<open>RT\<^sub>PS\<close>: the reduced pair sequences \<open>{M \<in> T\<^sub>PS | Red M = M} = Im(Red)\<close>.\<close>

definition RT_PS :: "pairseq set" where
  "RT_PS = {M. M \<in> T_PS \<and> Red M = M}"

text \<open>
  Conditions (A) and (B) of 命題（簡約性と係数の関係）, named for reuse:
    \<^item> (A): whenever \<open>(i,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (i,j\<^sub>1)\<close> has a unique parent \<open>j\<^sub>0\<close>
      (for \<open>i \<in> {0,1}\<close>), then \<open>M\<^bsub>i,j\<^sub>0\<^esub> + 1 = M\<^bsub>i,j\<^sub>1\<^esub>\<close>;
    \<^item> (B): whenever \<open>j\<^sub>1\<close> (\<open>\<le> Lng M - 1\<close>) has no unique row-0 parent, then
      \<open>M\<^bsub>0,j\<^sub>1\<^esub> = M\<^bsub>1,j\<^sub>1\<^esub>\<close>.
\<close>

definition RedCondA :: "pairseq \<Rightarrow> bool" where
  "RedCondA M \<longleftrightarrow>
     (\<forall>i\<le>1. \<forall>j1'. hasParent M i j1' \<longrightarrow> entry M i (parent M i j1') + 1 = entry M i j1')"

definition RedCondB :: "pairseq \<Rightarrow> bool" where
  "RedCondB M \<longleftrightarrow>
     (\<forall>j1'. \<not> hasParent M 0 j1' \<and> j1' \<le> Lng M - 1 \<longrightarrow> entry M 0 j1' = entry M 1 j1')"


subsection \<open>§6.7 標準形 (Standard form)\<close>

text \<open>
  \<open>ST\<^sub>PS\<close> (標準形): the least \<open>S \<subseteq> T\<^sub>PS\<close> closed under the diagonals
  \<open>((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup>\<close> (\<open>u \<le> v\<close>) and the fundamental sequence \<open>M \<mapsto> M[n]\<close>
  (\<open>n \<ge> 1\<close>).  Encoded as an inductive set.
\<close>

inductive_set ST_PS :: "pairseq set" where
  diag: "u \<le> v \<Longrightarrow> diagSeq u v \<in> ST_PS"
| oper: "\<lbrakk>M \<in> ST_PS; 1 \<le> n\<rbrakk> \<Longrightarrow> (M::pairseq)[n] \<in> ST_PS"

text \<open>
  \<open>SkT_PS k\<close> (\<open>S\<^sub>kT\<^sub>PS\<close>): the rank-\<open>k\<close> stratification of \<open>ST\<^sub>PS\<close>;
  \<open>ST\<^sub>PS = \<Union>\<^sub>k S\<^sub>kT\<^sub>PS\<close> (命題 below).
\<close>

fun SkT_PS :: "nat \<Rightarrow> pairseq set" where
  "SkT_PS 0 = {N. \<exists>u v. N = diagSeq u v \<and> u \<le> v}"
| "SkT_PS (Suc k) = {N. \<exists>M n. N = (M::pairseq)[n] \<and> M \<in> SkT_PS k \<and> 1 \<le> n}"

text \<open>
  \<open>anchored_slice\<close> (correction A4): the provisional domain on which the §6.5
  corollaries hold (they are FALSE on all of \<open>T\<^sub>PS\<close>; see corrections.md /
  docs/red-le-domain.md).  \<open>M\<close> is an ancestor-anchored slice: \<open>M = (S\<^sub>j)\<^bsub>j=a\<^esub>\<^bsup>b\<^esup>\<close>
  for some standard (or reduced-and-mono) \<open>S\<close> with \<open>(0,a) \<le>\<^sub>S (0,b)\<close> — the
  hypothesis of 命題 標準形の切片と Br の降順性, and the form of the §7
  use-sites (\<open>N = (M\<^sub>j)\<^bsub>j=lo\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close> with \<open>lo\<close> an ancestor of \<open>j\<^sub>1\<close>).
  Empirically verified (python/, yaBMS); the proof and a possibly simpler
  intrinsic characterization are PENDING.
\<close>

definition anchored_slice :: "pairseq set" where
  "anchored_slice =
     {M. \<exists>S a b. (S \<in> ST_PS \<or> (S \<in> RT_PS \<and> S \<in> PT_PS))
                  \<and> a \<le> b \<and> b < Lng S \<and> le0 S a b \<and> M = seg S a b}"


subsection \<open>§6.8 降順性 (Descending lists)\<close>

text \<open>
  \<open>descending Q\<close> for \<open>Q \<in> T\<^sub>PS\<^bsup><\<omega>\<^esup>\<close>: the left ends \<open>(Q\<^sub>J)\<^bsub>0,0\<^esub>\<close> are weakly
  decreasing in \<open>J\<close>, and tie-broken by weakly decreasing \<open>(Q\<^sub>J)\<^bsub>1,0\<^esub>\<close>.
\<close>

definition descending :: "pairseq list \<Rightarrow> bool" where
  "descending Q \<longleftrightarrow>
     (\<forall>J0 J1. J0 \<le> J1 \<and> J1 \<le> Lng Q - 1 \<longrightarrow>
        entry (Q ! J0) 0 0 \<ge> entry (Q ! J1) 0 0
      \<and> (entry (Q ! J0) 0 0 = entry (Q ! J1) 0 0
           \<longrightarrow> entry (Q ! J0) 1 0 \<ge> entry (Q ! J1) 1 0))"


subsection \<open>§7.4 許容的親子関係 (Admissible parent relation)\<close>

text \<open>
  \<open>nextAdm M i j\<^sub>0 j\<^sub>1\<close> models the admissible parent relation
  \<open>(i,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>NextAdm (i,j\<^sub>1)\<close> (§7.4): \<open>(i,j\<^sub>0) \<le>\<^sub>M (i,j\<^sub>1)\<close>, \<open>j\<^sub>0 < j\<^sub>1\<close>,
  \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible, and every intermediate \<open>j\<close> either is not an
  ancestor of \<open>j\<^sub>1\<close> in row \<open>i\<close> or is non-admissible.  (The article states the
  relation on \<open>\<int>\<^sup>2\<close>; it is used within a single row \<open>i\<close>, matching \<open>\<le>\<^sub>M\<close>.)
\<close>

definition nextAdm :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nextAdm M i j0 j1 \<longleftrightarrow>
     leR M i j0 j1 \<and> j0 < j1 \<and> adm M j0
   \<and> (\<forall>j. j0 < j \<and> j < j1 \<longrightarrow> \<not> leR M i j j1 \<or> \<not> adm M j)"


section \<open>§8 停止性 (Termination)\<close>

text \<open>\<open>DT\<^bsub>PS\<^esub>\<close> (強単項ペア数列): \<open>M\<close> is reduced, mono, and \<open>Br M\<close> is descending
  (§8.2, article 3279–3281).  The \<open>Br\<close>-descending condition is exactly the
  conclusion of §6.8 prop1 (\<open>p_6_8_standard_slice_Br_descending\<close>), so §8.2's
  strong-monomiality of standard slices builds directly on §6.8.\<close>

definition DT_PS :: "pairseq set" where
  "DT_PS = {M. M \<in> RT_PS \<and> monoT M \<and> descending (Br M)}"

text \<open>\<open>LastStep : DT\<^bsub>PS\<^esub> \<to> \<nat>\<close> (§8.2, article 3297–3326): with \<open>J\<^sub>1\<close> the last
  \<open>Br\<close>-index, \<open>0\<close> if \<open>Br M = []\<close>; \<open>J\<^sub>1\<close> if the last branch has equal head rows;
  else the least \<open>J\<close> whose head row-0 equals \<open>(Br M\<^bsub>J\<^sub>1\<^esub>)\<^bsub>0,0\<^esub>\<close> and exceeds its
  own row-1.  (CORRECTION A9: the article writes \<open>J\<^sub>1 := Lng(Br M)\<close> but then
  indexes \<open>Br(M)\<^bsub>J\<^sub>1\<^esub>\<close>, which is out of range; \<open>Lng(Br M) - 1\<close> is meant.)\<close>

definition LastStep :: "pairseq \<Rightarrow> nat" where
  "LastStep M =
     (if Br M = [] then 0
      else let J1 = Lng (Br M) - 1 in
        if entry (Br M ! J1) 0 0 = entry (Br M ! J1) 1 0 then J1
        else Min {J. entry (Br M ! J1) 0 0 = entry (Br M ! J) 0 0
                     \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0})"

end
