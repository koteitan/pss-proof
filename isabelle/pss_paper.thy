theory pss_paper
  imports pss_defs "HOL-Library.Extended_Nat"
    After_6
begin

text \<open>
  Faithful transcription of the *statements* (命題 / 補題 / 系 / 定理) of
  P進大好きbot's article "ペア数列の停止性", in the order they appear.

  After the chapter relocation this file holds no article statement of its own:
  every §5–§8 proposition now lives with its proof in the matching
  per-proposition theory under \<open>5/\<close>, \<open>6/\<close>, \<open>7/\<close> and \<open>8/\<close>.  What remains here is
  the §7 transcription of the \<^bold>\<open>external\<close> reference [Buc1] — its definitions,
  plus the three cited [Buc1] lemmas kept as @{command sorry} because they belong
  to that reference rather than to this article (\<open>buc1_2_2_OT_B_wf\<close>,
  \<open>buc1_3_2a_fseq_lt\<close>, \<open>buc1_3_2_OT_B_closed\<close>; our own proofs of the latter two
  are the \<open>m_buc1_*\<close> facts under \<open>7/\<close>).

  Naming / traceability: each fact is named \<open>p_<sec>_<slug>\<close> and carries a
  comment with the article section (§) and the original Japanese name, so it
  can be located in @{file "tmp/content.md"}.
\<close>

text \<open>§5 has moved to the per-proposition theories in the \<open>5/\<close> directory.\<close>

text \<open>§6 has moved to the 55 per-proposition theories in the \<open>6/\<close> directory and the shared helper theories under \<open>PSS/\<close>.\<close>

section \<open>§7 Buchholz の表記系への翻訳\<close>

text \<open>
  The Buchholz notation system, transcribed from the cited reference
  \<^bold>\<open>[Buc1]\<close> = W. Buchholz, "A new system of proof-theoretic ordinal
  functions", Annals of Pure and Applied Logic 32 (1986), pp. 195–207.
  These are the formulas of the external reference on which §7 of the article
  relies; we transcribe them here (in the paper file) rather than as our own
  modelling definitions.

  Indices \<open>v \<le> \<omega>\<close> of the symbols \<open>D\<^sub>v\<close> are modelled by \<^typ>\<open>enat\<close>
  (a finite \<open>v < \<omega>\<close> is \<open>enat n\<close>; \<open>\<omega>\<close> is \<open>\<infinity>\<close>).
\<close>

subsection \<open>§7.1 Buchholz の表記系 — 項と順序 ([Buc1] §2)\<close>

text \<open>
  [Buc1] (T1)–(T3): a term is \<open>0\<close> (\<open>= Trm []\<close>), a principal term \<open>D\<^sub>v a\<close>
  (\<open>= Trm [DB v a]\<close>), or a tuple \<open>(a\<^sub>0,\<dots>,a\<^sub>k)\<close> (\<open>k \<ge> 1\<close>) of principal
  terms (\<open>= Trm\<close> of a length \<open>\<ge> 2\<close> list).  Single principal: \<open>(a) := a\<close>.
\<close>

datatype BT = Trm "BP list"
     and BP = DB enat BT

abbreviation BZero :: BT  ("0\<^sub>B") where "0\<^sub>B \<equiv> Trm []"

text \<open>[Buc1] (<1)–(<3): the ordering \<open><\<close> on \<open>T\<close>.  As a dictionary order on the
  principal-term lists (a proper prefix is smaller), with principals compared
  by \<open>D\<^sub>u a < D\<^sub>v b \<longleftrightarrow> u < v \<or> (u = v \<and> a < b)\<close>.\<close>

fun lessBT :: "BT \<Rightarrow> BT \<Rightarrow> bool" and lessBP :: "BP \<Rightarrow> BP \<Rightarrow> bool" where
  "lessBT (Trm []) (Trm bs) = (bs \<noteq> [])"
| "lessBT (Trm (a # as)) (Trm []) = False"
| "lessBT (Trm (a # as)) (Trm (b # bs)) =
     (lessBP a b \<or> (a = b \<and> lessBT (Trm as) (Trm bs)))"
| "lessBP (DB u a) (DB v b) = (u < v \<or> (u = v \<and> lessBT a b))"

abbreviation leBT :: "BT \<Rightarrow> BT \<Rightarrow> bool" where
  "leBT a b \<equiv> lessBT a b \<or> a = b"

text \<open>[Buc1] (G1)–(G3): \<open>G\<^sub>u a \<subseteq> T\<close>.\<close>

fun GBT :: "enat \<Rightarrow> BT \<Rightarrow> BT set" and GBP :: "enat \<Rightarrow> BP \<Rightarrow> BT set" where
  "GBT u (Trm ps) = (\<Union>p \<in> set ps. GBP u p)"
| "GBP u (DB v b) = (if u \<le> v then insert b (GBT u b) else {})"

text \<open>[Buc1] §3: addition \<open>a + b\<close> and \<open>a \<cdot> n\<close>.\<close>

fun addBT :: "BT \<Rightarrow> BT \<Rightarrow> BT"  (infixl "+\<^sub>B" 65) where
  "addBT (Trm as) (Trm bs) = Trm (as @ bs)"

fun multBT :: "BT \<Rightarrow> nat \<Rightarrow> BT"  (infixl "*\<^sub>B" 70) where
  "multBT a 0 = 0\<^sub>B"
| "multBT a (Suc n) = (multBT a n) +\<^sub>B a"

text \<open>[Buc1] §3: \<open>T\<^sub>v\<close> for \<open>v \<le> \<omega>\<close> — terms whose top-level principal indices
  are all \<open>\<le> v\<close>.\<close>

definition TBv :: "enat \<Rightarrow> BT set" where
  "TBv v = {t. \<forall>p \<in> set (case t of Trm ps \<Rightarrow> ps). (case p of DB u a \<Rightarrow> u \<le> v)}"

text \<open>\<open>T\<^bsub>B\<^esub>\<close>: the \<open>D\<^sub>\<omega>\<close>-free terms (no index equals \<open>\<omega> = \<infinity>\<close> anywhere).\<close>

fun dfree_BT :: "BT \<Rightarrow> bool" and dfree_BP :: "BP \<Rightarrow> bool" where
  "dfree_BT (Trm ps) = (\<forall>p \<in> set ps. dfree_BP p)"
| "dfree_BP (DB v b) = (v \<noteq> \<infinity> \<and> dfree_BT b)"

definition T_B :: "BT set" where
  "T_B = {t. dfree_BT t}"

text \<open>[Buc1] (OT1)–(OT3): the ordinal terms \<open>OT \<subseteq> T\<close>.  Characterized
  structurally: \<open>0 \<in> OT\<close>; a principal \<open>D\<^sub>v b \<in> OT\<close> iff \<open>b \<in> OT\<close> and
  \<open>G\<^sub>v b < b\<close>; a tuple \<open>(a\<^sub>0,\<dots>,a\<^sub>k) \<in> OT\<close> iff every component is an
  \<open>OT\<close>-principal and the components are non-increasing \<open>a\<^sub>k \<le> \<dots> \<le> a\<^sub>0\<close>.\<close>

fun descP :: "BP list \<Rightarrow> bool" where
  "descP [] = True"
| "descP [p] = True"
| "descP (p # q # ps) = (leBT (Trm [q]) (Trm [p]) \<and> descP (q # ps))"

fun isOT_BT :: "BT \<Rightarrow> bool" and isOT_BP :: "BP \<Rightarrow> bool" where
  "isOT_BT (Trm ps) = ((\<forall>p \<in> set ps. isOT_BP p) \<and> descP ps)"
| "isOT_BP (DB v b) = (isOT_BT b \<and> (\<forall>x \<in> GBT v b. lessBT x b))"

definition OT :: "BT set" where
  "OT = {t. isOT_BT t}"

text \<open>\<open>OT\<^bsub>B\<^esub> := OT \<inter> T\<^bsub>B\<^esub>\<close> (content.md 5951): the \<open>D\<^sub>\<omega>\<close>-free ordinal terms.
  \<open>(OT\<^bsub>B\<^esub>, <)\<close> is well-founded ([Buc1] Lemma 2.2) — the eventual source of
  termination.\<close>

definition OT_B :: "BT set" where
  "OT_B = OT \<inter> T_B"


subsection \<open>§7.1 Buchholz の表記系 — 基本列と \<open>dom\<close> ([Buc1] §3)\<close>

text \<open>\<open>D\<^sub>v a = Trm [DB v a]\<close> (a principal term as a \<^typ>\<open>BT\<close>).\<close>

abbreviation Dprin :: "enat \<Rightarrow> BT \<Rightarrow> BT" where "Dprin v a \<equiv> Trm [DB v a]"

text \<open>The numeral terms \<open>\<nat> \<cong> {0,1,1+1,\<dots>}\<close> ([Buc1] §3): \<open>n\<close> is \<open>n\<close> copies of
  \<open>1 = D\<^sub>0 0\<close>.  \<open>numNat\<close> recovers \<open>n\<close> from a numeral term.\<close>

definition numBT :: "nat \<Rightarrow> BT" where
  "numBT n = Trm (replicate n (DB 0 (Trm [])))"

definition numNat :: "BT \<Rightarrow> nat" where
  "numNat t = (case t of Trm ps \<Rightarrow> length ps)"

definition NatSet :: "BT set" where
  "NatSet = range numBT"

text \<open>\<open>tbvIdx D\<close>: the unique \<open>u\<close> with \<open>D = T\<^sub>u\<close> (used when \<open>dom(b) = T\<^sub>u\<close>).\<close>

definition tbvIdx :: "BT set \<Rightarrow> nat" where
  "tbvIdx D = (THE u. D = TBv (enat u))"

text \<open>
  [Buc1] §3 \<open>dom(a)\<close> and \<open>a[z]\<close>, ([].0)–([].5), with the \<^bold>\<open>[Buc2]\<close>-modified
  case ([].4)(ii) (article footnote, content.md 6427): \<open>x\<^sub>0 = D\<^sub>u 0\<close>,
  \<open>x\<^sub>i = D\<^sub>u b[x\<^bsub>i-1\<^esub>]\<close>, \<open>a[n] = D\<^sub>v b[x\<^sub>n]\<close> (correction A23, revised: the footnote's
  \<open>x\<^sub>i = b[D\<^sub>u x\<^bsub>i-1\<^esub>]\<close> is a \<^emph>\<open>transposition\<close> typo for \<open>x\<^sub>i = D\<^sub>u b[x\<^bsub>i-1\<^esub>]\<close>; with that
  repair the rule is literally Buchholz's fundamental sequence
  \<open>\<psi>\<^sub>v(b)[n] = \<psi>\<^sub>v(b[g\<^sub>n])\<close>, \<open>g\<^sub>0 = \<Omega>\<^sub>u\<close>, \<open>g\<^bsub>n+1\<^esub> = \<psi>\<^sub>u(b[g\<^sub>n])\<close>, and the article's own
  §7.2 (2) holds 112/112 while the earlier "drop the outer \<open>b[\<dots>]\<close>" reading
  fails 60/60); \<open>xseq b u\<close> computes \<open>x\<close>.

  \<open>dom\<close> returns the actual index set (\<open>\<emptyset>\<close>, \<open>{0}\<close>, \<open>\<nat>\<close> = \<open>NatSet\<close>, or
  \<open>T\<^sub>u\<close> = \<open>TBv (enat u)\<close>).  Mutual recursion (with \<open>xseq\<close>); all calls are on
  \<open>dom\<close>/\<open>[]\<close>-free arguments, so the definition is accepted by \<open>function\<close>;
  termination ([Buc1] Lemma 3.2, induction on the length of \<open>a\<close>) is deferred.
\<close>

function (domintros)
  domB :: "BT \<Rightarrow> BT set" and
  operB :: "BT \<Rightarrow> BT \<Rightarrow> BT" and
  xseq :: "BT \<Rightarrow> enat \<Rightarrow> nat \<Rightarrow> BT"
where
  "domB a =
     (case a of Trm xs \<Rightarrow> (case xs of
        [] \<Rightarrow> {}
      | [DB v b] \<Rightarrow>
          (if b = Trm [] then
             (if v = 0 then {Trm []}
              else if v = \<infinity> then NatSet
              else TBv (enat (the_enat v - 1)))
           else
             (let db = domB b in
              if db = {Trm []} then NatSet
              else if (\<exists>u. v \<le> enat u \<and> db = TBv (enat u)) then NatSet
              else db))
      | (p # q # rest) \<Rightarrow> domB (Trm [last (p # q # rest)])))"
| "operB a z =
     (case a of Trm xs \<Rightarrow> (case xs of
        [] \<Rightarrow> Trm []
      | [DB v b] \<Rightarrow>
          (if b = Trm [] then
             (if v = 0 then Trm []
              else if v = \<infinity> then Dprin (enat (numNat z + 1)) (Trm [])
              else z)
           else
             (let db = domB b in
              if db = {Trm []} then multBT (Dprin v (operB b (Trm []))) (numNat z + 1)
              else if (\<exists>u. v \<le> enat u \<and> db = TBv (enat u))
                   then Dprin v (operB b (xseq b (enat (tbvIdx db)) (numNat z)))
              else Dprin v (operB b z)))
      | (p # q # rest) \<Rightarrow>
          addBT (Trm (butlast (p # q # rest))) (operB (Trm [last (p # q # rest)]) z)))"
| "xseq b u i =
     (case i of
        0 \<Rightarrow> Dprin u (Trm [])
      | Suc j \<Rightarrow> Dprin u (operB b (xseq b u j)))"
  by pat_completeness auto

text \<open>
  \<open>P\<^bsub>B\<^esub> : T\<^bsub>B\<^esub> \<to> PT\<^bsub>B\<^esub>\<^bsup><\<omega>\<^esup>\<close> and its inverse \<open>\<Sigma>\<^bsub>B\<^esub>\<close> (§7.1).  In the
  datatype model the principal components of \<open>Trm ps\<close> are simply \<open>(Trm [p])\<^bsub>p\<in>ps\<^esub>\<close>;
  \<open>\<Sigma>\<^bsub>B\<^esub>\<close> concatenates their (length-1) component lists.  Hence \<open>P\<^bsub>B\<^esub>\<close>
  and \<open>\<Sigma>\<^bsub>B\<^esub>\<close> are mutually inverse (命題（順序数項の単項成分の基本性質）(2)).
\<close>

fun untrm :: "BT \<Rightarrow> BP list" where
  "untrm (Trm ps) = ps"

definition PB :: "BT \<Rightarrow> BT list" where
  "PB t = map (\<lambda>p. Trm [p]) (untrm t)"

definition SigmaB :: "BT list \<Rightarrow> BT" where
  "SigmaB ts = Trm (concat (map untrm ts))"

text \<open>[Buc1] の外部補題（\<^bold>\<open>引用\<close>）。原文（P進大好きbot「ペア数列の停止性」）はこれらを
  Buchholz [Buc1] から引用し、\<^bold>\<open>証明していない\<close>。忠実性方針（原作にない原始的要素を
  導入しない）に従い、ここでも引用として \<open>sorry\<close> で立てる（証明は後日埋める、2026-06-25
  ユーザー判断「いったん faithful に、あとで埋める」）。\<^bold>\<open>下流（§8 の交換則・停止性）は
  これらを正当な外部結果として参照してよい\<close>（名前 \<open>buc1_*\<close> がこの引用ステータスを示す）。
  \<^item> [Buc1] Lemma 2.2: \<open>(OT\<^bsub>B\<^esub>, <)\<close> は整礎（停止性の最終的なソース）。
  \<^item> [Buc1] Lemma 3.2 (a): \<open>a \<in> OT\<^bsub>B\<^esub>\<close> かつ \<open>a \<noteq> 0\<close> ならば基本列は狭義下降
    \<open>a[n] < a\<close>（\<open>a[n] = operB a (numBT n)\<close>）。〔§8.3/§8.4/§8.6 の \<open>Trans\<close>×基本列
    交換則の降下と §8.7 停止性が依存〕\<close>

lemma buc1_2_2_OT_B_wf:
  \<comment> \<open>[Buc1] Lemma 2.2 — 引用（未証明）。\<open>{(a,b). a < b}\<close> on \<open>OT\<^bsub>B\<^esub>\<close> の整礎性。\<close>
  "wf {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}"
  sorry

lemma buc1_3_2a_fseq_lt:
  \<comment> \<open>[Buc1] Lemma 3.2 (a) — 引用（未証明）。基本列の狭義下降 \<open>a[n] < a\<close>。\<close>
  assumes "a \<in> OT_B" and "a \<noteq> Trm []"
  shows "lessBT (operB a (numBT n)) a"
  sorry

lemma buc1_3_2_OT_B_closed:
  \<comment> \<open>[Buc1] §3 — 引用（未証明）: \<open>OT\<^bsub>B\<^esub>\<close> は \<open>[]\<close>-演算で閉じる。\<open>a \<in> OT\<^bsub>B\<^esub>\<close>,
       \<open>a \<noteq> 0\<close> ならば基本列 \<open>a[n] = operB a (numBT n)\<close> もまた \<open>OT\<^bsub>B\<^esub>\<close> に属する。
       §8.7 末尾項の零化可能性（@{text m_8_7_toplevel_OT_tail_annihilate}）が
       一般本体 \<open>t' \<in> OT\<^bsub>B\<^esub>\<close> での降下 @{thm [source] buc1_3_2a_fseq_lt} を整礎帰納で
       回すために必要。EMPIRICALLY VALIDATED 0 failures over ~6.3M \<open>(a,n)\<close> pairs
       (\<open>python/_buc1_otb_closed.py\<close>, \<open>max_idx\<le>3, depth\<le>3, width\<le>3\<close>).\<close>
  assumes "a \<in> OT_B" and "a \<noteq> Trm []"
  shows "operB a (numBT n) \<in> OT_B"
  sorry


subsection \<open>§7.2 scb分解 ([Buc1] のアルファベット \<open>\<Sigma>\<close> 上)\<close>

text \<open>The alphabet \<open>\<Sigma>\<close>: the letters \<open>\<^bold>(\<close>, \<open>\<^bold>,\<close>, \<open>\<^bold>)\<close>, \<open>0\<close>, and \<open>D\<^sub>u\<close>
  (\<open>u \<le> \<omega>\<close>).\<close>

datatype Sym = LP | CM | RP | Zsym | Dsym enat

text \<open>\<open>flat t\<close>: the \<open>\<Sigma>\<close>-string of a term.  \<open>0 = "0"\<close>; a principal
  \<open>D\<^sub>u a = "D\<^sub>u" \<frown> flat a\<close>; a tuple \<open>(a\<^sub>0,\<dots>,a\<^sub>k) = "(" a\<^sub>0 "," \<dots> "," a\<^sub>k ")"\<close>
  (single principal uncontracted: \<open>(a) = a\<close>).\<close>

fun flatBT :: "BT \<Rightarrow> Sym list" and flatBP :: "BP \<Rightarrow> Sym list" where
  "flatBT (Trm []) = [Zsym]"
| "flatBT (Trm [p]) = flatBP p"
| "flatBT (Trm (p # q # ps)) =
     LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))) @ [RP]"
| "flatBP (DB u a) = Dsym u # flatBT a"

text \<open>\<open>RightNodes : T\<^bsub>B\<^esub> \<to> \<nat>\<^bsup><\<omega>\<^esup>\<close> (§7.2): \<open>0 \<mapsto> ()\<close>; \<open>D\<^sub>u t' \<mapsto> (u) \<frown>
  RightNodes t'\<close>; a multi term \<open>\<mapsto> RightNodes\<close> of its last principal component.\<close>

function RightNodes :: "BT \<Rightarrow> nat list" where
  "RightNodes (Trm xs) =
     (case xs of [] \<Rightarrow> []
      | _ \<Rightarrow> (case last xs of DB u a \<Rightarrow> the_enat u # RightNodes a))"
  by pat_completeness auto
\<comment> \<open>termination (induction on the rightmost spine) is deferred, like \<open>Red\<close>/\<open>domB\<close>.\<close>

text \<open>
  scb-decomposition (§7.2): \<open>(s,c,b) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>3\<close> is an scb-decomposition
  of \<open>t\<close> when \<open>flat t = s \<frown> c \<frown> b\<close>, \<open>c\<close> is (the string of) a principal term
  \<open>\<in> PT\<^bsub>B\<^esub>\<close> when \<open>t \<noteq> 0\<close>, and \<open>b\<close> consists only of \<open>\<^bold>)\<close>.
\<close>

definition isPTB_str :: "Sym list \<Rightarrow> bool" where
  "isPTB_str c = (\<exists>p. dfree_BP p \<and> c = flatBP p)"

definition scb_decomp :: "BT \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool" where
  "scb_decomp t s c b \<longleftrightarrow>
     flatBT t = s @ c @ b
   \<and> (t \<noteq> Trm [] \<longrightarrow> isPTB_str c)
   \<and> (\<forall>x \<in> set b. x = RP)"

text \<open>第\<open>0\<close>種 / 第\<open>1\<close>種 scb-decomposition (§7.2).  Their \<open>RightNodes\<close>
  conditions refer to the principal term whose string is \<open>c\<close>.\<close>

definition scb_kind0 :: "BT \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool" where
  "scb_kind0 t s c b \<longleftrightarrow>
     scb_decomp t s c b
   \<and> isPTB_str c
   \<and> (\<forall>p. c = flatBP p \<longrightarrow>
        (Lng (RightNodes (Trm [p])) = 2 \<and> RightNodes (Trm [p]) ! 1 = 0))"

definition scb_kind1 :: "BT \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool" where
  "scb_kind1 t s c b \<longleftrightarrow>
     scb_decomp t s c b
   \<and> isPTB_str c
   \<and> (\<forall>p. c = flatBP p \<longrightarrow>
        (let r = RightNodes (Trm [p]); j1 = Lng r - 1 in
         j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)))"

text \<open>\<open>T\<^bsub>B\<^esub>\<^sup>Marked \<subseteq> T\<^bsub>B\<^esub>\<^sup>2\<close>: pairs \<open>(t,c)\<close> for which some scb-decomposition
  \<open>(s,c,b)\<close> of \<open>t\<close> exists (with \<open>c = flat\<close> of the marked principal).\<close>

definition MarkedB :: "(BT \<times> BT) set" where
  "MarkedB = {(t, c). \<exists>s b. scb_decomp t s (flatBT c) b}"


text \<open>\<open>t\<close> が第\<open>0\<close>種 / 第\<open>1\<close>種 scb分解可能 (§7.2): some \<open>scb_kind0\<close> / \<open>scb_kind1\<close>
  decomposition of \<open>t\<close> exists.\<close>

abbreviation scb_kind0_able :: "BT \<Rightarrow> bool" where
  "scb_kind0_able t \<equiv> \<exists>s c b. scb_kind0 t s c b"

abbreviation scb_kind1_able :: "BT \<Rightarrow> bool" where
  "scb_kind1_able t \<equiv> \<exists>s c b. scb_kind1 t s c b"

subsection \<open>§7.3 翻訳写像 (Trans / Mark)\<close>

text \<open>The principal-term constructor \<open>D\<^sub>v t = Trm [DB v t]\<close> (\<open>v :: enat\<close>); on the
  pair-sequence side the row-1 coefficients are \<open>nat\<close>, embedded via \<open>enat\<close>.\<close>

abbreviation Dpt :: "enat \<Rightarrow> BT \<Rightarrow> BT" where
  "Dpt v t \<equiv> Trm [DB v t]"

text \<open>The mutually exclusive conditions (I)–(VI) of the \<open>Trans\<close> recursion
  (article 2096–2106), for a reduced mono \<open>M\<close> with \<open>j\<^sub>1 = Lng M - 1 > 0\<close>.
  Here \<open>j\<^sub>0\<close> is the row-0 nearest ancestor of \<open>j\<^sub>1\<close>, modelled as \<open>parent M 0 j\<^sub>1\<close>
  (FAITHFULNESS: article \<open>j\<^sub>0 = max{j<j\<^sub>1 | (0,j) \<le>\<^sub>M (0,j\<^sub>1)}\<close>; coincidence with
  \<open>parent M 0 j\<^sub>1\<close> to be verified — see \<open>docs/trans-mark.md\<close>).\<close>

definition transCondI :: "pairseq \<Rightarrow> bool" where
  "transCondI M \<longleftrightarrow> entry M 1 (Lng M - 1) = 0 \<and> adm M (parent M 0 (Lng M - 1))"

definition transCondII :: "pairseq \<Rightarrow> bool" where
  "transCondII M \<longleftrightarrow> entry M 1 (Lng M - 1) = 0 \<and> \<not> adm M (parent M 0 (Lng M - 1))"

definition transCondIII :: "pairseq \<Rightarrow> bool" where
  "transCondIII M \<longleftrightarrow> entry M 1 (Lng M - 1) > 0
     \<and> entry M 1 (parent M 0 (Lng M - 1)) \<ge> entry M 1 (Lng M - 1)
     \<and> adm M (parent M 0 (Lng M - 1))"

definition transCondIV :: "pairseq \<Rightarrow> bool" where
  "transCondIV M \<longleftrightarrow> entry M 1 (Lng M - 1) > 0
     \<and> entry M 1 (parent M 0 (Lng M - 1)) \<ge> entry M 1 (Lng M - 1)
     \<and> \<not> adm M (parent M 0 (Lng M - 1))"

definition transCondV :: "pairseq \<Rightarrow> bool" where
  "transCondV M \<longleftrightarrow> entry M 1 (Lng M - 1) > 0
     \<and> entry M 1 (parent M 0 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)
     \<and> parent M 0 (Lng M - 1) + 1 < Lng M - 1"

definition transCondVI :: "pairseq \<Rightarrow> bool" where
  "transCondVI M \<longleftrightarrow> entry M 1 (Lng M - 1) > 0
     \<and> entry M 1 (parent M 0 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)
     \<and> parent M 0 (Lng M - 1) + 1 = Lng M - 1"

text \<open>The string-level connective \<open>s c b\<close> of the article (a \<open>\<Sigma>\<close>-string that is a
  valid term string) is realised at the \<open>BT\<close> level by \<open>unflatBT\<close>: the unique
  term whose \<open>flat\<close> is the given string (\<open>flatBT\<close> is injective on \<open>T\<^bsub>B\<^esub>\<close>).\<close>

definition unflatBT :: "Sym list \<Rightarrow> BT" where
  "unflatBT xs = (THE t. flatBT t = xs)"

text \<open>Accessors for a principal term \<open>D\<^sub>v t\<close> (its head index \<open>v\<close> and body \<open>t\<close>);
  total, with junk defaults off the principal shape.  Used to read \<open>c\<^sub>1 = D\<^sub>v t\<^sub>2\<close>
  and the left end \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub>\<close> of \<open>P\<^bsub>B\<^esub>(t\<^sub>2)\<^bsub>J\<^sub>1\<^esub>\<close>.\<close>

fun bpHeadV :: "BT \<Rightarrow> enat" where
  "bpHeadV (Trm (DB v t # ps)) = v"
| "bpHeadV (Trm []) = 0"

fun bpHeadT :: "BT \<Rightarrow> BT" where
  "bpHeadT (Trm (DB v t # ps)) = t"
| "bpHeadT (Trm []) = 0\<^sub>B"

text \<open>翻訳写像 \<open>Trans\<close> / \<open>Mark\<close> (§7.3, article 2044–2180), a mutual recursion on
  \<open>Lng M\<close>.  Termination is deferred (like \<open>Red\<close> / \<open>RightNodes\<close> / \<open>domB\<close>): we use a
  catch-all \<open>function\<close> and \<open>pat_completeness\<close>, leaving the conditional \<open>psimps\<close>.
  The article's \<open>\<Sigma>\<close>-string connective \<open>s c b\<close> is realised by \<open>unflatBT\<close>.\<close>

function (domintros) Trans :: "pairseq \<Rightarrow> BT" and Mark :: "pairseq \<Rightarrow> nat \<Rightarrow> BT" where
  "Trans M =
     (if M \<notin> RT_PS then Trans (Red M)
      else let j1 = Lng M - 1 in
        if j1 = 0 then
          (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B else Dpt (enat (entry M 1 0)) 0\<^sub>B)
        else if monoT M then
          (let t1 = Trans (Pred M) in
           if t1 = 0\<^sub>B then Dpt 0 (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
           else
             let jp = parent M 0 j1;
                 c1 = Mark (Pred M) (Adm M jp);
                 v = bpHeadV c1;  t2 = bpHeadT c1;  J1 = Lng (PB t2) - 1;
                 pj = PB t2 ! J1;  leftDj0 = (bpHeadV pj = enat (entry M 1 jp));
                 t3 = (if leftDj0 then SigmaB (take J1 (PB t2)) else t2);
                 t4 = (if leftDj0 then bpHeadT pj else t2);
                 c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                       then Dpt v (t2 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                       else if transCondVI M
                       then Dpt v (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                       else if t2 = 0\<^sub>B
                       then Dpt v (Dpt (enat (entry M 1 jp)) (Dpt (enat (entry M 1 j1)) 0\<^sub>B))
                       else Dpt v (t3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                          (t4 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)));
                 sb1 = (SOME sb. scb_decomp t1 (fst sb) (flatBT c1) (snd sb))
             in unflatBT (fst sb1 @ flatBT c2 @ snd sb1))
        else
          (let J1 = Lng (P M) - 1;  PJ = P M ! J1;  j0 = j1 - Lng PJ + 1 in
           if PJ = [(0,0)] then Trans (seg M 0 (j0 - 1)) +\<^sub>B Dpt 0 0\<^sub>B
           else Trans (seg M 0 (j0 - 1)) +\<^sub>B Trans PJ))"
| "Mark M m =
     (if M \<notin> RT_PS then Mark (Red M) m
      else let j1 = Lng M - 1 in
        if j1 = 0 then
          (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B else Dpt (enat (entry M 1 0)) 0\<^sub>B)
        else if monoT M then
          (let t1 = Trans (Pred M) in
           if t1 = 0\<^sub>B then
             (if m = 0 then Dpt 0 (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
              else Dpt (enat (entry M 1 j1)) 0\<^sub>B)
           else
             let jp = parent M 0 j1;
                 c1 = Mark (Pred M) (Adm M jp);
                 v = bpHeadV c1;  t2 = bpHeadT c1;  J1 = Lng (PB t2) - 1;
                 pj = PB t2 ! J1;  leftDj0 = (bpHeadV pj = enat (entry M 1 jp));
                 t3 = (if leftDj0 then SigmaB (take J1 (PB t2)) else t2);
                 t4 = (if leftDj0 then bpHeadT pj else t2);
                 c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                       then Dpt v (t2 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                       else if transCondVI M
                       then Dpt v (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                       else if t2 = 0\<^sub>B
                       then Dpt v (Dpt (enat (entry M 1 jp)) (Dpt (enat (entry M 1 j1)) 0\<^sub>B))
                       else Dpt v (t3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                          (t4 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)))
             in if m < j1 then
                  (let c0 = Mark (Pred M) m in
                   if (c0, c1) \<in> MarkedB
                   then let sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))
                        in unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
                   else Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                else Dpt (enat (entry M 1 j1)) 0\<^sub>B)
        else
          (let J1 = Lng (P M) - 1;  PJ = P M ! J1;  j0 = j1 - Lng PJ + 1 in
           if PJ = [(0,0)] then Dpt 0 0\<^sub>B
           else Mark PJ (m - j0)))"
  by pat_completeness auto

text \<open>Accessors exposing the internal symbols of the recursive definition of
  \<open>Trans\<close> (the \<open>monoT M \<and> j\<^sub>1 > 0 \<and> t\<^sub>1 \<noteq> 0\<close> branch above), so that the §7.3 /
  §8.3–8.5 propositions stated in terms of them become expressible.  Each mirrors
  the corresponding \<open>let\<close>-binding in the \<open>Trans\<close> body verbatim:
  \<open>j\<^sub>1 = transJ1\<close>, \<open>j\<^sub>0 = transJ0\<close> (\<open>= jp\<close>), \<open>j\<^sub>-\<^sub>1 = transJm1\<close>, \<open>t\<^sub>1 = transT1\<close>,
  \<open>c\<^sub>1 = transC1\<close>, \<open>v = transV\<close>, \<open>t\<^sub>2 = transT2\<close>, \<open>c\<^sub>2 = transC2\<close>.  They are total
  functions of \<open>M\<close>; the propositions guard them with the branch conditions
  (\<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>, \<open>j\<^sub>1 > 0\<close>, \<open>t\<^sub>1 \<noteq> 0\<close>) under which they coincide with the
  def-internal symbols.\<close>

definition transJ1 :: "pairseq \<Rightarrow> nat" where
  "transJ1 M = Lng M - 1"
definition transJ0 :: "pairseq \<Rightarrow> nat" where
  "transJ0 M = parent M 0 (transJ1 M)"
definition transJm1 :: "pairseq \<Rightarrow> nat" where
  "transJm1 M = Adm M (transJ0 M)"
definition transT1 :: "pairseq \<Rightarrow> BT" where
  "transT1 M = Trans (Pred M)"
definition transC1 :: "pairseq \<Rightarrow> BT" where
  "transC1 M = Mark (Pred M) (transJm1 M)"
definition transV :: "pairseq \<Rightarrow> enat" where
  "transV M = bpHeadV (transC1 M)"
definition transT2 :: "pairseq \<Rightarrow> BT" where
  "transT2 M = bpHeadT (transC1 M)"
definition transC2 :: "pairseq \<Rightarrow> BT" where
  "transC2 M =
     (let j1 = transJ1 M;  jp = transJ0 M;  v = transV M;  t2 = transT2 M;
          J1 = Lng (PB t2) - 1;  pj = PB t2 ! J1;
          leftDj0 = (bpHeadV pj = enat (entry M 1 jp));
          t3 = (if leftDj0 then SigmaB (take J1 (PB t2)) else t2);
          t4 = (if leftDj0 then bpHeadT pj else t2)
      in if transCondI M \<or> transCondIII M \<or> transCondV M
         then Dpt v (t2 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)
         else if transCondVI M
         then Dpt v (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
         else if t2 = 0\<^sub>B
         then Dpt v (Dpt (enat (entry M 1 jp)) (Dpt (enat (entry M 1 j1)) 0\<^sub>B))
         else Dpt v (t3 +\<^sub>B Dpt (enat (entry M 1 jp))
                            (t4 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)))"

text \<open>\<open>RightAnces : T\<^bsub>PS\<^esub> \<to> \<nat>\<^bsup><\<omega>\<^esup>\<close> (§7.4, article 2704–2741): a recursion on
  \<open>Lng M\<close> mirroring \<open>Trans\<close> (reduced/mono/multi/non-reduced; conditions (I)–(VI);
  \<open>j\<^sub>0 = parent M 0 j\<^sub>1\<close>, \<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close>).  Independent of \<open>Trans\<close>/\<open>Mark\<close>;
  termination deferred (like \<open>Trans\<close>/\<open>RightNodes\<close>).\<close>

function (domintros) RightAnces :: "pairseq \<Rightarrow> nat list" where
  "RightAnces M =
     (if M \<notin> RT_PS then RightAnces (Red M)
      else let j1 = Lng M - 1 in
        if j1 = 0 then (if (M::pairseq) ! 0 = (0,0) then [] else [entry M 1 0])
        else if monoT M then
          (if zeroT (Pred M) then [0, entry M 1 j1]
           else let jp = parent M 0 j1;  jm1 = Adm M jp;
                    a = (if zeroT (seg M 0 jm1) then [0] else RightAnces (seg M 0 jm1)) in
                if transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M
                then a @ [entry M 1 j1]
                else a @ [entry M 1 jp, entry M 1 j1])
        else
          (let J1 = Lng (P M) - 1;  PJ = P M ! J1 in
           if PJ = [(0,0)] then [0] else RightAnces PJ))"
  by pat_completeness auto

end
