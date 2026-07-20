theory pss_paper
  imports pss_defs "HOL-Library.Extended_Nat"
    After_6
begin

text \<open>
  Faithful transcription of the *statements* (命題 / 補題 / 系 / 定理) of
  P進大好きbot's article "ペア数列の停止性", in the order they appear.

  Every remaining §8 statement here is left as @{command sorry}: this file records WHAT
  the article claims, not the proofs.  Statements whose proof the article
  itself omits, and statements we have simply not yet proved, are all
  @{command sorry} here.  The §5–§6 proofs live with their proposition theories
  under \<open>5/\<close> and \<open>6/\<close>; proofs for the remaining chapters live in
  @{file "pss_mechanized.thy"}.

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

section \<open>§8 停止性 (Termination)\<close>

subsection \<open>§8.2 強単項性 (Strong-monomiality)\<close>

text \<open>Article order is §8.1 < §8.2, but §8.2 is grouped first here because it
  introduces \<open>DT\<^bsub>PS\<^esub>\<close> (= \<open>DT_PS\<close>, 強単項) and \<open>LastStep\<close> used throughout §8;
  all statements are \<open>sorry\<close> so the document order is cosmetic.

  Faithfulness note on 強許容 (strong-admissibility): the article uses the
  phrase \<open>M の強許容性\<close> only inside §8.2 proofs (article 3532/3552/3576/3800),
  never as a separate definition.  At each use it denotes the consequence of
  \<open>descending (Br M)\<close> (the third clause of 強単項) re-expressed in
  \<open>FirstNodes\<close>/\<open>Joints\<close> coordinates (e.g. equal row-0 heads \<open>\<Rightarrow>\<close> descending
  row-1 heads).  Hence it is NOT a primitive needed to state the §8.2
  propositions; it only surfaces in their (deferred) proofs.\<close>

text \<open>命題（標準形の直系先祖による切片の簡約化の強単項性） (§8.2, article 3283):
  for \<open>M \<in> ST\<^bsub>PS\<^esub>\<close>, the reduction of an ancestor slice with \<open>(0,j'\<^sub>0) \<le>\<^sub>M (0,j'\<^sub>1)\<close>
  is strong-monomial.  Builds directly on §6.8 prop1
  (\<open>p_6_8_standard_slice_Br_descending\<close>): the slice \<open>M'\<close> is mono with \<open>Br M'\<close>
  descending, so \<open>Red M'\<close> is reduced + mono + \<open>Br\<close>-descending, i.e. \<open>\<in> DT\<^bsub>PS\<^esub>\<close>.\<close>

lemma p_8_2_standard_slice_Red_strongmono:
  assumes "M \<in> ST_PS" "j0' < j1'" "j1' \<le> Lng M - 1" "leR M 0 j0' j1'"
  shows "Red (seg M j0' j1') \<in> DT_PS"
  sorry

text \<open>補題（強単項性の切片への遺伝性） (§8.2, article 3328):
  for \<open>M \<in> DT\<^bsub>PS\<^esub>\<close>, an ancestor slice \<open>M' = (M\<^sub>j)\<^bsub>j=j'\<^sub>0\<^esub>\<^bsup>j'\<^sub>1\<^esup>\<close> with
  \<open>j'\<^sub>0 < j'\<^sub>1 \<le> Lng M - 1\<close> and \<open>j'\<^sub>0 \<le> Joints(M)\<^bsub>J\<^sub>1\<^esub>\<close> (\<open>J\<^sub>1 = Lng(Br M)-1\<close>)
  is again strong-monomial.\<close>

lemma p_8_2_strongmono_slice:
  fixes M :: pairseq
  defines "J1 \<equiv> Lng (Br M) - 1"
  assumes "M \<in> DT_PS" "j0' < j1'" "j1' \<le> Lng M - 1" "j0' \<le> Joints M ! J1"
  shows "seg M j0' j1' \<in> DT_PS"
  sorry

text \<open>補題（部分表現の単項成分と\<open>Pred\<close>の関係） (§8.2, article 3360):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> with \<open>j\<^sub>1 = Lng M - 1 > 1\<close>, set \<open>J\<^sub>1 = Lng(Br M)-1\<close>
  (\<open>Br M \<noteq> []\<close>), \<open>j'\<^sub>0 = Joints(M)\<^bsub>J\<^sub>1\<^esub>\<close>, \<open>j'\<^sub>1 = FirstNodes(M)\<^bsub>J\<^sub>1\<^esub>\<close>.  One of four
  cases (1)–(4) holds, each pinning down \<open>Trans(Pred M)\<close> and \<open>Trans M\<close> for a
  unique tuple of \<open>T\<^bsub>B\<^esub>\<close>-terms.  \<open>D\<^sub>x t = Dpt (enat x) t\<close>; \<open>+\<close> = \<open>+\<^sub>B\<close>;
  \<open>0\<close> = \<open>0\<^sub>B\<close>.  Tuples use \<open>fst\<close>/\<open>snd\<close> projections (\<open>(t\<^sub>1,t\<^sub>2,t\<^sub>3)\<close> as \<open>t123\<close>).\<close>

lemma p_8_2_subexpr_component_Pred:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "Br M \<noteq> []" "j1 > 1"
  shows
    "\<comment> \<open>(1)\<close>
     (j1' = j1 \<and> (TrMax M = 0 \<or> j0' < TrMax M)
        \<and> (entry M 0 j1' = entry M 1 j1' \<or> adm M j0')
        \<and> (\<exists>!t1. Trans (Pred M) = Dpt (enat (entry M 1 0)) t1
              \<and> Trans M = Dpt (enat (entry M 1 0))
                            (t1 +\<^sub>B Dpt (enat (entry M 1 j1')) 0\<^sub>B)))
   \<or> \<comment> \<open>(2)\<close>
     (j1' = j1 \<and> entry M 0 j1' > entry M 1 j1' \<and> \<not> adm M j0'
        \<and> (\<exists>!t12. Trans (Pred M) = Dpt (enat (entry M 1 0)) (fst t12)
              \<and> Trans M = Dpt (enat (entry M 1 0))
                            (fst t12 +\<^sub>B Dpt (enat (entry M 1 j0')) (snd t12))))
   \<or> \<comment> \<open>(3)\<close>
     (\<exists>!t123. Trans (Pred M)
                = Dpt (enat (entry M 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M 1 j1')) (fst (snd t123)))
            \<and> Trans M = Dpt (enat (entry M 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M 1 j1')) (snd (snd t123))))
   \<or> \<comment> \<open>(4)\<close>
     (\<exists>!t123. Trans (Pred M)
                = Dpt (enat (entry M 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M 1 j0')) (fst (snd t123)))
            \<and> Trans M = Dpt (enat (entry M 1 0))
                    (fst t123 +\<^sub>B Dpt (enat (entry M 1 j0')) (snd (snd t123))))"
  sorry

text \<open>補題（強単項性の下での部分表現の単項成分の基本性質） (§8.2, article 3454):
  for \<open>M \<in> DT\<^bsub>PS\<^esub>\<close> (\<open>Br M \<noteq> []\<close>), a unique \<open>t' \<in> T\<^bsub>B\<^esub>\<close> with
  \<open>Trans M = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>0\<^esub> t'\<close> bounds every principal component of \<open>t'\<close> from below.
  「\<open>t'\<close>の各単項成分は \<open>D\<^sub>x 0\<close> 以上」 is modelled as
  \<open>\<forall>p \<in> set (PB t'). leBT (D\<^sub>x 0) p\<close> (the elements of \<open>PB t'\<close> are already the
  principal-component \<^typ>\<open>BT\<close>s, so each summand \<open>p \<ge> D\<^sub>x 0\<close>).\<close>

lemma p_8_2_subexpr_component_strongmono:
  fixes M :: pairseq
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  assumes "M \<in> DT_PS" "Br M \<noteq> []"
  shows "\<exists>!t'.
      \<comment> \<open>(1)\<close>
      Trans M = Dpt (enat (entry M 1 0)) t'
    \<and> \<comment> \<open>(2)\<close>
      ((j0' = 0 \<or> entry M 0 j1' = entry M 1 j1')
         \<longrightarrow> (\<forall>p\<in>set (PB t'). leBT (Dpt (enat (entry M 1 j1')) 0\<^sub>B) p))
    \<and> \<comment> \<open>(3)\<close>
      ((0 < j0' \<and> j0' < TrMax M \<and> entry M 0 j1' > entry M 1 j1')
         \<longrightarrow> (\<forall>p\<in>set (PB t'). leBT (Dpt (enat (entry M 1 j0')) 0\<^sub>B) p))
    \<and> \<comment> \<open>(4)\<close>
      ((0 < j0' \<and> j0' = TrMax M)
         \<longrightarrow> (\<forall>p\<in>set (PB t'). leBT (Dpt (enat (entry M 1 (TrMax M))) 0\<^sub>B) p))"
  sorry

text \<open>補題（条件(V)の下での右端の親の基本性質） (§8.2, article 3602):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>m \<in> \<nat>\<close>, under
  「\<open>m < j'\<^sub>0\<close>」or「\<open>m = j'\<^sub>0 \<and> M\<^bsub>0,j'\<^sub>1\<^esub> = M\<^bsub>1,j'\<^sub>1\<^esub> \<and> Br M\<close> descending」,
  a unique \<open>j\<^sub>0\<close> satisfies (1)–(4).  \<open><\<^bsub>M\<^esub>\<^sup>Next\<close> on row 0 = \<open>nextR M 0\<close>.\<close>

lemma p_8_2_condV_rightmost_parent:
  fixes M :: pairseq and m :: nat
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "Br M \<noteq> []"
    and "m < j0' \<or> (m = j0' \<and> entry M 0 j1' = entry M 1 j1' \<and> descending (Br M))"
  shows "\<exists>!j0.
      \<comment> \<open>(1)\<close> nextR M 0 j0 j1
    \<and> \<comment> \<open>(2)\<close> j0' \<le> j0
    \<and> \<comment> \<open>(3)\<close> (m < j0 \<or> entry M 0 j1 = entry M 1 j1)
    \<and> \<comment> \<open>(4)\<close> (m = j0 \<longrightarrow> j0 < TrMax M)"
  sorry

text \<open>補題（条件(V)の下での終切片と\<open>Trans\<close>の関係） (§8.2, article 3664):
  same hypotheses as the previous lemma, with \<open>M' = (M\<^sub>j)\<^bsub>j=m\<^esub>\<^bsup>j\<^sub>1\<^esup> = seg M m j\<^sub>1\<close>;
  a unique \<open>t\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> gives \<open>Trans M = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>0\<^esub> t\<^sub>1\<close> and \<open>Trans M' = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> t\<^sub>1\<close>.\<close>

lemma p_8_2_condV_terminal_slice_Trans:
  fixes M :: pairseq and m :: nat
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  defines "M' \<equiv> seg M m j1"
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "Br M \<noteq> []"
    and "m < j0' \<or> (m = j0' \<and> entry M 0 j1' = entry M 1 j1' \<and> descending (Br M))"
  shows "\<exists>!t1. Trans M = Dpt (enat (entry M 1 0)) t1
            \<and> Trans M' = Dpt (enat (entry M 1 m)) t1"
  sorry

text \<open>命題（条件(II)か(IV)の下での終切片と\<open>Trans\<close>の関係） (§8.2, article 3314):
  for \<open>M \<in> DT\<^bsub>PS\<^esub>\<close>, set \<open>j\<^sub>1 = Lng M - 1\<close>, \<open>J\<^sub>1 = Lng(Br M)-1\<close> (\<open>Br M \<noteq> []\<close>),
  \<open>j'\<^sub>0 = Joints(M)\<^bsub>J\<^sub>1\<^esub>\<close>, \<open>j'\<^sub>1 = FirstNodes(M)\<^bsub>J\<^sub>1\<^esub>\<close>, \<open>J\<^sub>0 = LastStep M\<close>,
  \<open>m\<^sub>1 = FirstNodes(M)\<^bsub>J\<^sub>0\<^esub> - 1\<close>, \<open>N = seg M 0 m\<^sub>1\<close>, \<open>N' = seg M j'\<^sub>0 m\<^sub>1\<close>,
  \<open>M' = seg M j'\<^sub>0 j\<^sub>1\<close>.  If \<open>0 < j'\<^sub>0 < TrMax M\<close> and \<open>M\<^bsub>0,j'\<^sub>1\<^esub> > M\<^bsub>1,j'\<^sub>1\<^esub>\<close>
  then a unique \<open>(t\<^sub>1,t\<^sub>2) \<in> T\<^bsub>B\<^esub>\<^sup>2\<close> satisfies (1)–(4).\<close>

lemma p_8_2_condIIIV_terminal_slice_Trans:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
  defines "J1 \<equiv> Lng (Br M) - 1"
  defines "j0' \<equiv> Joints M ! J1"
  defines "j1' \<equiv> FirstNodes M ! J1"
  defines "J0 \<equiv> LastStep M"
  defines "m1 \<equiv> FirstNodes M ! J0 - 1"
  defines "N \<equiv> seg M 0 m1"
  defines "N' \<equiv> seg M j0' m1"
  defines "M' \<equiv> seg M j0' j1"
  assumes "M \<in> DT_PS" "Br M \<noteq> []"
    and "0 < j0'" "j0' < TrMax M" "entry M 0 j1' > entry M 1 j1'"
  shows "\<exists>!t12.
      \<comment> \<open>(1)\<close> Trans N = Dpt (enat (entry M 1 0)) (fst t12)
    \<and> \<comment> \<open>(2)\<close> Trans N' = Dpt (enat (entry M 1 j0')) (fst t12)
    \<and> \<comment> \<open>(3)\<close> Trans M' = Dpt (enat (entry M 1 j0')) (fst t12 +\<^sub>B snd t12)
              \<and> snd t12 \<noteq> 0\<^sub>B
    \<and> \<comment> \<open>(4)\<close> Trans M = Dpt (enat (entry M 1 0))
                  (fst t12 +\<^sub>B Dpt (enat (entry M 1 j0')) (fst t12 +\<^sub>B snd t12))"
  sorry



subsection \<open>§8.1 条件(I)の下での展開規則 (Expansion rule under condition (I))\<close>

text \<open>補題（公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.1, article 2837):
  for \<open>u, v \<in> \<nat>\<close> with \<open>u < v\<close>, the diagonal (公差\<open>(1,1)\<close>) pair sequence
  \<open>M = ((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup>\<close> has \<open>Trans(M) = D\<^sub>u D\<^sub>v 0\<close>.  Modelling: \<open>((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup>\<close>
  is the existing \<open>diagSeq u v\<close>; \<open>D\<^sub>u D\<^sub>v 0\<close> is \<open>Dpt (enat u) (Dpt (enat v) 0\<^sub>B)\<close>.\<close>

lemma p_8_1_diagSeq_Trans:
  assumes "u < v"
  shows "Trans (diagSeq u v) = Dpt (enat u) (Dpt (enat v) 0\<^sub>B)"
  sorry

text \<open>系（\<open>Pred\<close>が公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.1, article 2871):
  for \<open>u,v,w,w' \<in> \<nat>\<close> with \<open>u < v\<close>, let \<open>M := ((j,j))\<^bsub>j=u\<^esub>\<^bsup>v\<^esup> \<oplus>\<^bsub>\<nat>\<^sup>2\<^esub> (w',w)\<close>
  (modelled by \<open>diagSeq u v @ [(w', w)]\<close>, the article's \<open>\<oplus>\<^bsub>\<nat>\<^sup>2\<^esub>\<close> being list
  append \<open>@\<close>).  The four cases give the explicit \<open>Trans(M)\<close>.  The article's
  string connective \<open>D\<^sub>u ( a , b )\<close> (with underlined parens/comma) is the
  \<open>BT\<close>-level \<open>Dpt (enat u) (a +\<^sub>B b)\<close> (\<open>+\<^sub>B\<close> realises \<open>\<oplus>\<close> on \<open>T\<^bsub>B\<^esub>\<close>).\<close>

lemma p_8_1_Pred_diagSeq_Trans:
  assumes "u < v"
  shows
    "\<comment> \<open>(1)\<close>
     (w' = v + 1 \<and> u < w \<and> w \<le> v
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) (Dpt (enat w) 0\<^sub>B)))
   \<and> \<comment> \<open>(2)\<close>
     (u < w' \<and> w' \<le> v \<and> w = w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B))
   \<and> \<comment> \<open>(3)\<close>
     (u + 1 < w' \<and> w' \<le> v \<and> w < w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B
                    +\<^sub>B Dpt (enat (w' - 1)) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B)))
   \<and> \<comment> \<open>(4)\<close>
     (u + 1 = w' \<and> w < w'
        \<longrightarrow> Trans (diagSeq u v @ [(w', w)])
              = Dpt (enat u) (Dpt (enat v) 0\<^sub>B +\<^sub>B Dpt (enat w) 0\<^sub>B))"
  sorry

text \<open>補題（条件(I)か(III)の下での\<open>c\<^sub>1\<close>前後の具体表示） (§8.1, article 2923):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>, using the symbols of the recursive definition of
  \<open>Trans\<close> (\<open>j\<^sub>1 = Lng M - 1\<close>, \<open>j\<^sub>0 = parent M 0 j\<^sub>1\<close>, \<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close>,
  \<open>c\<^sub>1 = Mark (Pred M) j\<^sub>-\<^sub>1\<close>), if \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible (\<open>adm M j\<^sub>0\<close>), \<open>j\<^sub>1 > 1\<close>
  and \<open>M\<^bsub>1,j\<^sub>0\<^esub> \<ge> M\<^bsub>1,j\<^sub>1\<^esub>\<close>, then several things hold.  Modelling notes:
    \<^item> \<open>(M\<^sub>j)\<^bsub>j=a\<^esub>\<^bsup>b\<^esup> = seg M a b\<close>; \<open>(M,m) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close> = \<open>(M,m) \<in> Marked\<close>;
      \<open>c\<^sub>1 \<in> PT\<^bsub>B\<^esub>\<close> = \<open>c\<^sub>1 \<in> PT_B\<close>.
    \<^item> The internal \<open>t\<^sub>2, t\<^sub>3, t\<^sub>4 \<in> T\<^bsub>B\<^esub>\<close> of \<open>Trans\<close> are not exposed, so parts
      (3)/(4) are stated with the explicit \<open>Mark\<close>-values they evaluate to:
      (3-1)/(4-1) give \<open>Mark (Pred M) j'\<^sub>-\<^sub>1 = D[M\<^sub>1\<^sub>,\<^sub>j'\<^sub>-\<^sub>1](t' +\<^sub>B c\<^sub>1)\<close> for a
      unique \<open>t' \<in> T\<^bsub>B\<^esub>\<close> (with \<open>t' = 0\<close> in the \<open>j'\<^sub>0+1 = j\<^sub>0\<close> sub-case), and
      (3-2)/(4-2) give \<open>Mark (Pred M) j'\<^sub>-\<^sub>1 = D[M\<^sub>1\<^sub>,\<^sub>j'\<^sub>-\<^sub>1](t'\<^sub>3 +\<^sub>B D[M\<^sub>1\<^sub>,\<^sub>j'\<^sub>0](t'\<^sub>4 +\<^sub>B c\<^sub>1))\<close>
      for unique \<open>(t'\<^sub>3,t'\<^sub>4) \<in> T\<^bsub>B\<^esub>\<^sup>2\<close>.
    \<^item> Part (5) is stated for \<open>n > 1\<close> with \<open>N := seg (M[n]) 0 (j\<^sub>0+(n-1)(j\<^sub>1-j\<^sub>0))\<close>;
      the internal \<open>Trans\<close>-symbols \<open>j\<^sub>1\<^sup>N, j\<^sub>0\<^sup>N, j\<^sub>-\<^sub>1\<^sup>N, t\<^sub>1\<^sup>N\<close> of \<open>N\<close> are recovered
      as \<open>Lng N - 1\<close>, \<open>parent N 0 (Lng N - 1)\<close>, \<open>Adm N (parent N 0 (Lng N - 1))\<close>,
      \<open>Trans (Pred N)\<close> respectively.\<close>

lemma p_8_1_condI_III_c1_around:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
  defines "j0 \<equiv> parent M 0 j1"
  defines "jm1 \<equiv> Adm M j0"
  defines "c1 \<equiv> Mark (Pred M) jm1"
  assumes "M \<in> RT_PS" "M \<in> PT_PS"
    and "adm M j0" "j1 > 1" "entry M 1 j0 \<ge> entry M 1 j1"
  shows
    "\<comment> \<open>(1)\<close>
     Trans (Pred M) \<noteq> 0\<^sub>B \<and> (transCondI M \<or> transCondIII M)
       \<and> Trans (seg M j0 (j1 - 1)) = c1 \<and> c1 \<in> T_B \<and> (\<exists>p. c1 = Trm [p])
   \<and> \<comment> \<open>(2)–(5): under existence of the unique next-parent \<open>j'\<^sub>0\<close> of \<open>j\<^sub>0\<close>\<close>
     (\<forall>j0'. nextR M 0 j0' j0 \<longrightarrow>
        (let jm1' = Adm M j0' in
         \<comment> \<open>(2)\<close>
         (j0' \<le> j1 - 2 \<and> (Pred M, jm1') \<in> Marked
            \<and> (seg M jm1' (j1 - 1), j0 - jm1') \<in> Marked)
         \<comment> \<open>(3) \<open>j'\<^sub>0+1 = j\<^sub>0\<close>\<close>
       \<and> (j0' + 1 = j0 \<longrightarrow>
            \<comment> \<open>(3-1)\<close>
            ((jm1' = j0' \<or> entry M 1 j0' + 1 = entry M 1 j0)
               \<longrightarrow> Mark (Pred M) jm1' = Dpt (enat (entry M 1 jm1')) c1)
          \<and> \<comment> \<open>(3-2)\<close>
            ((jm1' < j0' \<and> entry M 1 j0' \<ge> entry M 1 j0)
               \<longrightarrow> Mark (Pred M) jm1'
                     = Dpt (enat (entry M 1 jm1')) (Dpt (enat (entry M 1 j0')) c1)))
         \<comment> \<open>(4) \<open>j'\<^sub>0+1 < j\<^sub>0\<close>\<close>
       \<and> (j0' + 1 < j0 \<longrightarrow>
            \<comment> \<open>(4-1)\<close>
            ((jm1' = j0' \<or> entry M 1 j0' + 1 = entry M 1 j0)
               \<longrightarrow> (\<exists>!t2'. Mark (Pred M) jm1'
                            = Dpt (enat (entry M 1 jm1')) (t2' +\<^sub>B c1)))
          \<and> \<comment> \<open>(4-2)\<close>
            ((jm1' < j0' \<and> entry M 1 j0' \<ge> entry M 1 j0)
               \<longrightarrow> (\<exists>!t34. Mark (Pred M) jm1'
                            = Dpt (enat (entry M 1 jm1'))
                                  (fst t34 +\<^sub>B Dpt (enat (entry M 1 j0'))
                                                  (snd t34 +\<^sub>B c1)))))
         \<comment> \<open>(5)\<close>
       \<and> (\<forall>n. n > 1 \<longrightarrow>
            (let N = seg (M[n]) 0 (j0 + (n - 1) * (j1 - j0)) in
             (M[n], j0 + (n - 1) * (j1 - j0)) \<in> Marked
             \<and> nextR (M[n]) 0 j0' (j0 + (n - 1) * (j1 - j0))
             \<and> Lng N - 1 = j0 + (n - 1) * (j1 - j0)
             \<and> parent N 0 (Lng N - 1) = j0'
             \<and> Adm N (parent N 0 (Lng N - 1)) = jm1'
             \<and> Trans (Pred N) \<noteq> 0\<^sub>B
             \<and> \<not> transCondVI N))))"
  sorry

text \<open>命題（条件(I)の下での\<open>Trans\<close>と基本列の交換関係） (§8.1, article 2827):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, if \<open>j\<^sub>1 = Lng M - 1 > 1\<close> and \<open>M\<close>
  satisfies condition (I) (\<open>transCondI M\<close>), then
    (1) \<open>Trans(M[n]) = Trans(M)[n-1]\<close> and
    (2) \<open>Trans(M[n]) < Trans(M)\<close>.
  Modelling: the Buchholz fundamental sequence \<open>a[k]\<close> is \<open>operB a (numBT k)\<close>;
  \<open><\<close> on \<open>T\<^bsub>B\<^esub>\<close> is \<open>lessBT\<close>; \<open>n \<in> \<nat>\<^sub>+\<close> is \<open>n \<ge> 1\<close>.\<close>

lemma p_8_1_Trans_fseq_condI:
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "n \<ge> 1"
    and "Lng M - 1 > 1" "transCondI M"
  shows "Trans (M[n]) = operB (Trans M) (numBT (n - 1))"
    and "lessBT (Trans (M[n])) (Trans M)"
  sorry


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
  and \<open>0 < r' < j\<^sub>1-j\<^sub>0\<close>, then \<open>M[n]\<^bsub>0,j\<^sub>0+q(j\<^sub>1-j\<^sub>0)\<^esub> < M[n]\<^bsub>0,q'(j\<^sub>1-j\<^sub>0)+r'\<^esub>\<close>.
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
       < entry (M[n]) 0 (q' * ((Lng M - 1) - parent M 0 (Lng M - 1)) + r')"
  sorry

text \<open>補題（第\<open>0\<close>種型基本列の基本分岐規則） (§8.3, article 3984): for \<open>M \<in> RT\<^bsub>PS\<^esub>\<close>,
  \<open>n \<in> \<nat>\<^sub>+\<close>, \<open>q \<in> \<nat>\<close>, with \<open>j\<^sub>1 = Lng M - 1\<close>, if there is a unique \<open>j\<^sub>0\<close> with
  \<open>(0,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (0,j\<^sub>1)\<close>, \<open>M\<^bsub>1,j\<^sub>1\<^esub> = 0\<close>, \<open>q \<le> n-1\<close>, and \<open>j\<^sub>0\<close> is non-\<open>M\<close>-
  admissible, then \<open>(0,j\<^sub>0-1) <\<^bsub>M[n]\<^esub>\<^sup>Next (0,j\<^sub>0+q(j\<^sub>1-j\<^sub>0))\<close> and
  \<open>(1,j\<^sub>0-1) <\<^bsub>M[n]\<^esub>\<^sup>Next (1,j\<^sub>0+q(j\<^sub>1-j\<^sub>0))\<close>.\<close>

lemma p_8_3_kind0_branch_rule:
  fixes M :: pairseq
  assumes "M \<in> RT_PS" "0 < n"
    and "hasParent M 0 (Lng M - 1)"
    and "entry M 1 (Lng M - 1) = 0"
    and "q \<le> n - 1"
    and "\<not> adm M (parent M 0 (Lng M - 1))"
  shows "nextR (M[n]) 0 (parent M 0 (Lng M - 1) - 1)
            (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))
       \<and> nextR (M[n]) 1 (parent M 0 (Lng M - 1) - 1)
            (parent M 0 (Lng M - 1) + q * ((Lng M - 1) - parent M 0 (Lng M - 1)))"
  sorry

text \<open>補題（第\<open>0\<close>種型基本列の基本基点関係） (§8.3, article 3998): for \<open>M \<in> RT\<^bsub>PS\<^esub>\<close>,
  \<open>n \<in> \<nat>\<^sub>+\<close>, with \<open>j\<^sub>1 = Lng M - 1\<close>, if there is a unique \<open>j\<^sub>0\<close> with
  \<open>(0,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (0,j\<^sub>1)\<close>, \<open>j\<^sub>-\<^sub>1 = Adm\<^sub>M(j\<^sub>0)\<close>, and \<open>M\<^bsub>1,j\<^sub>1\<^esub> = 0\<close>, then:
  (1) if \<open>n > 1\<close> then \<open>(M[n], j\<^sub>0+(n-1)(j\<^sub>1-j\<^sub>0)) \<in> RT\<^bsub>PS\<^esub>\<^sup>Marked\<close>;
  (2) if \<open>j\<^sub>0\<close> is non-\<open>M\<close>-admissible then \<open>(M[n], j\<^sub>-\<^sub>1) \<in> RT\<^bsub>PS\<^esub>\<^sup>Marked\<close>.\<close>

lemma p_8_3_kind0_base_basepoint:
  fixes M :: pairseq
  assumes "M \<in> RT_PS" "0 < n"
    and "hasParent M 0 (Lng M - 1)"
    and "entry M 1 (Lng M - 1) = 0"
  shows "n > 1 \<longrightarrow>
           (M[n], parent M 0 (Lng M - 1)
                  + (n-1) * ((Lng M - 1) - parent M 0 (Lng M - 1))) \<in> Marked
           \<and> M[n] \<in> RT_PS"
    and "\<not> adm M (parent M 0 (Lng M - 1)) \<longrightarrow>
           (M[n], Adm M (parent M 0 (Lng M - 1))) \<in> Marked \<and> M[n] \<in> RT_PS"
  sorry

text \<open>命題（条件(II)の下での\<open>Trans\<close>と基本列の交換関係） (§8.3, article 3958): for
  \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, with the symbols introduced in the
  \<open>Trans\<close> recursion, \<open>L := Red((M\<^sub>j)\<^bsub>j=j\<^sub>-\<^sub>1\<^esub>\<^bsup>j\<^sub>1\<^esup>)\<close>, if \<open>j\<^sub>1 > 1\<close> and \<open>M\<close>
  satisfies condition (II), then, with \<open>m\<^sub>n := n-1\<close> or \<open>m\<^sub>n := n-2\<close> according to
  whether the left end of \<open>P\<^bsub>B\<^esub>(t\<^sub>2)\<^bsub>J\<^sub>1\<^esub>\<close> is \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub>\<close> or not:
  (1) if \<open>m\<^sub>n = -1\<close> then \<open>Trans(M[n]) = s\<^sub>1 D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>1\<^esub> t\<^sub>2 b\<^sub>1\<close>;
  (2) if \<open>m\<^sub>n \<ge> 0\<close> then \<open>Trans(M[n]) = Trans(M)[m\<^sub>n]\<close>;
  (3) \<open>Mark(M[n], j\<^sub>-\<^sub>1) = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>1\<^esub>(t\<^sub>3 + (D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> t\<^sub>4) \<times> (m\<^sub>n+1)))\<close>;
  (4) \<open>Trans(M[n]) < Trans(M)\<close>.

  MODELLING NOTE: conclusions (1)–(3) are stated in terms of the \<open>Trans\<close>-recursion
  locals \<open>s\<^sub>1, b\<^sub>1, t\<^sub>2, t\<^sub>3, t\<^sub>4, c\<^sub>1, c\<^sub>2, v, J\<^sub>1\<close> and the integer-valued index
  \<open>m\<^sub>n \<in> \<nat> \<union> {-1}\<close>, which the \<open>Trans\<close> / \<open>Mark\<close> \<open>function\<close> does not expose as
  separate functions (cf. the deferred §7.3 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）, which
  is likewise "to be stated once they are exposed").  They are therefore deferred
  to the mechanization, where these locals will be defined.  Only the
  self-contained descent conclusion (4) is transcribed here.\<close>

lemma p_8_3_TransCondII_oper_descend:
  fixes M :: pairseq
  assumes "M \<in> ST_PS" "M \<in> PT_PS" "0 < n"
    and "Lng M - 1 > 1"
    and "transCondII M"
  shows "lessBT (Trans (M[n])) (Trans M)"
  sorry


subsection \<open>§8.4 条件(III)か(IV)の下での展開規則\<close>

text \<open>This subsection (article ## 条件(III)か(IV)の下での展開規則) builds up to the
  exchange relation between the translation \<open>Trans\<close> and the pair-sequence
  fundamental sequence under conditions (III)/(IV).

  COMMON SETUP / NOTATION used throughout the article's §8.4 statements:
    \<^item> \<open>j\<^sub>1 = Lng M - 1\<close>, the rightmost index;
    \<^item> \<open>j\<^sub>0\<close> = the row-0 nearest ancestor of \<open>j\<^sub>1\<close> (\<open>= parent M 0 j\<^sub>1\<close>);
    \<^item> \<open>j\<^sub>-\<^sub>2\<close> = the \<^bold>\<open>unique\<close> \<open>j\<close> with \<open>(1,j) <\<^bsub>M\<^esub>\<^sup>Next (1,j\<^sub>1)\<close>, i.e.
      \<open>nextR M 1 j\<^sub>-\<^sub>2 j\<^sub>1\<close>; modelled by \<open>parent M 1 j\<^sub>1\<close> under \<open>hasParent M 1 j\<^sub>1\<close>;
    \<^item> \<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close>, \<open>j\<^sub>-\<^sub>3 = Adm M j\<^sub>-\<^sub>2\<close>;
    \<^item> "条件(III)/(IV)/(V)/(VI)" = \<open>transCondIII\<close>/\<open>transCondIV\<close>/\<open>transCondV\<close>/\<open>transCondVI\<close>;
    \<^item> the Buchholz-side fundamental sequence \<open>t[n]\<close> is \<open>operB t (numBT n)\<close>, and
      \<open>< / \<le>\<close> on \<open>T\<^bsub>B\<^esub>\<close> are \<open>lessBT\<close>/\<open>leBT\<close>.

  FAITHFULNESS / DEFERRAL.  Most of the auxiliary §8.4 \<^emph>\<open>lemmas\<close> state relations
  among the \<^emph>\<open>internal symbols of the \<open>Trans\<close> recursion\<close> (\<open>c\<^sub>1\<close>, \<open>c\<^sub>2\<close>, \<open>t\<^sub>2\<close>,
  \<open>t\<^sub>3\<close>, \<open>t\<^sub>4\<close>, \<open>v\<close>, the scb-strings \<open>s\<^sub>1\<close>/\<open>b\<^sub>1\<close>, \<open>s'\<^sub>0\<dots>b'\<^sub>0\<close>, \<dots>) — the same
  symbols that, in §7.3, are \<^bold>\<open>not\<close> exposed as separate Isabelle functions (cf.
  the deferred §7.3 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）).  Those auxiliary lemmas are
  therefore \<^bold>\<open>deferred\<close> (documented as \<open>text\<close> notes with the precise blocking
  symbols), and only the two \<^emph>\<open>externally-statable\<close> facts — the headline
  proposition and the fundamental-sequence basic property — are transcribed as
  \<open>sorry\<close> lemmas.\<close>

text \<open>命題（条件(III)か(IV)の下での\<open>Trans\<close>と基本列の交換関係） (§8.4): for
  \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, assuming a unique \<open>j\<^sub>-\<^sub>2\<close> with
  \<open>(1,j\<^sub>-\<^sub>2) <\<^bsub>M\<^esub>\<^sup>Next (1,j\<^sub>1)\<close> exists (\<open>hasParent M 1 (Lng M - 1)\<close>), if
  \<open>j\<^sub>1 > 1\<close> and \<open>M\<close> satisfies condition (III) or (IV), then:
    (1) \<open>Trans(M[n]) \<le> Trans(M)[n-1]\<close>;
    (2) \<open>Trans(M[n]) < Trans(M)\<close>;
    (3) \<open>Trans(M)[n-1] < Trans(M[n+1])\<close>.
  Here \<open>Trans(M)[k] = operB (Trans M) (numBT k)\<close> is the Buchholz-side
  fundamental sequence.  (The setup symbols \<open>j\<^sub>-\<^sub>2\<close>/\<open>j\<^sub>-\<^sub>3\<close> appear only in the
  hypothesis; the conclusions (1)–(3) are symbol-free, hence transcribable.)\<close>

lemma p_8_4_Trans_oper_exchange:
  assumes "M \<in> ST_PS" "M \<in> PT_PS" "n \<ge> 1"
    and "hasParent M 1 (Lng M - 1)"
    and "Lng M - 1 > 1"
    and "transCondIII M \<or> transCondIV M"
  shows "leBT (Trans (M[n])) (operB (Trans M) (numBT (n - 1)))"
    and "lessBT (Trans (M[n])) (Trans M)"
    and "lessBT (operB (Trans M) (numBT (n - 1))) (Trans (M[n+1]))"
  sorry

text \<open>補題（右端の非許容直系先祖の基本性質） (§8.4): a \<open>Trans\<close>-free basic property
  of the rightmost non-admissible direct ancestor.  For \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>
  and \<open>m\<^sub>0, m\<^sub>1\<close>, with \<open>j\<^sub>1 = Lng M - 1\<close>, \<open>m\<^sub>-\<^sub>1 = Adm M m\<^sub>0\<close>,
  \<open>N = (M\<^sub>j)\<^bsub>j=m\<^sub>-\<^sub>1\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close>, given \<open>(0,m\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (0,m\<^sub>1) \<le>\<^bsub>M\<^esub> (0,j\<^sub>1)\<close>,
  if \<open>\<not> (1,m\<^sub>1-1) <\<^bsub>M\<^esub>\<^sup>Next (1,m\<^sub>1)\<close> and \<open>m\<^sub>0\<close> is non-\<open>M\<close>-admissible, then with
  \<open>J\<^sub>1 = Lng (Br (Red N)) - 1\<close>: \<open>J\<^sub>1 \<ge> 0\<close>, \<open>0 < m\<^sub>0-m\<^sub>-\<^sub>1 < TrMax (Red N)\<close>,
  \<open>m\<^sub>0-m\<^sub>-\<^sub>1 = Joints (Red N) ! J\<^sub>1\<close>, and \<open>FirstNodes (Red N) ! J\<^sub>1 = m\<^sub>1-m\<^sub>-\<^sub>1\<close>.
  This statement is \<open>Trans\<close>-free and uses only exposed defs (\<open>Adm\<close>, \<open>seg\<close>,
  \<open>Red\<close>, \<open>Br\<close>, \<open>TrMax\<close>, \<open>Joints\<close>, \<open>FirstNodes\<close>, \<open>nextR\<close>, \<open>leR\<close>, \<open>adm\<close>) — hence
  it is transcribable.  Modelling: \<open>(1,m\<^sub>1-1) <\<^bsub>M\<^esub>\<^sup>Next (1,m\<^sub>1)\<close> is
  \<open>nextR M 1 (m\<^sub>1-1) m\<^sub>1\<close>; the \<open>Joints\<close>/\<open>FirstNodes\<close> indices follow §6.4.\<close>

lemma p_8_4_rightmost_nonadm_ancestor:
  fixes M :: pairseq and m0 m1 :: nat
  defines "j1 \<equiv> Lng M - 1"
    and "mm1 \<equiv> Adm M m0"
  assumes "M \<in> ST_PS" "M \<in> PT_PS"
    and "nextR M 0 m0 m1" "leR M 0 m1 j1"
    and "\<not> nextR M 1 (m1 - 1) m1"
    and "\<not> adm M m0"
  shows "Lng (Br (Red (seg M mm1 j1))) \<ge> 1"  \<comment> \<open>article \<open>J\<^sub>1 \<ge> 0\<close> with \<open>J\<^sub>1 = Lng(Br(Red N))-1\<close>\<close>
    and "0 < m0 - mm1 \<and> m0 - mm1 < TrMax (Red (seg M mm1 j1))"
    and "m0 - mm1 = Joints (Red (seg M mm1 j1)) ! (Lng (Br (Red (seg M mm1 j1))) - 1)"
    and "FirstNodes (Red (seg M mm1 j1)) ! (Lng (Br (Red (seg M mm1 j1))) - 1) = m1 - mm1"
  sorry

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
  sorry



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
  sorry

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
  sorry

text \<open>補題（条件(V)の下での各種scb分解） (§8.5, article 5213): DEFERRED.  With
  \<open>N' = (M\<^sub>j)\<^bsub>j=j\<^sub>0\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close>, \<open>L' = (M\<^sub>j)\<^bsub>j=j\<^sub>0\<^esub>\<^bsup>j\<^sub>1-\<^sub>1\<^esup> \<oplus> ((M\<^bsub>0,j\<^sub>1\<^esub>,M\<^bsub>1,j\<^sub>0\<^esub>)))\<close> and
  \<open>L\<^sub>n = M[n] \<oplus> ((M\<^bsub>0,j\<^sub>0\<^esub>+n(M\<^bsub>0,j\<^sub>1\<^esub>-M\<^bsub>0,j\<^sub>0\<^esub>), M\<^bsub>1,j\<^sub>0\<^esub>)))\<close>, the lemma asserts a unique
  \<open>(s'\<^sub>1,b'\<^sub>1) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>2\<close> such that parts (1)–(5) describe scb-decompositions of
  \<open>c\<^sub>2\<close>, \<open>Trans(N')\<close>, \<open>Trans(L')\<close>, \<open>Trans(Pred N')\<close>, and closed forms for
  \<open>Trans(L\<^sub>n)\<close> and \<open>Trans(M[n])\<close> — all stated through the unexposed internal
  \<open>Trans\<close>-recursion symbols \<open>s\<^sub>1\<close>, \<open>b\<^sub>1\<close>, \<open>s'\<^sub>1\<close>, \<open>b'\<^sub>1\<close>, \<open>t\<^sub>2\<close>, \<open>c\<^sub>2\<close> (string
  concatenation/exponentiation of unexposed scb-strings).  Not faithfully
  expressible without inventing that exposure.  BLOCKING SYMBOLS:
  \<open>s\<^sub>1\<close>, \<open>b\<^sub>1\<close>, \<open>s'\<^sub>1\<close>, \<open>b'\<^sub>1\<close>, \<open>t\<^sub>2\<close>, \<open>c\<^sub>2\<close>.\<close>

text \<open>補題（条件(V)の下での基本列のscb分解） (§8.5, article 5352): DEFERRED.  Asserts a
  unique \<open>u \<in> \<nat>\<close>, \<open>(s'\<^sub>0,b'\<^sub>0) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>2\<close> and \<open>t' \<in> T\<^bsub>B\<^esub>\<close> such that
  \<open>(s'\<^sub>0, D\<^sub>u t\<^sub>2, b'\<^sub>0)\<close>, \<open>(s'\<^sub>0, D\<^sub>u(t\<^sub>2 + D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> 0), b'\<^sub>0)\<close>,
  \<open>(s'\<^sub>0, D\<^sub>u(t\<^sub>2 + D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> t'), b'\<^sub>0)\<close> are scb-decompositions of \<open>Trans(M[n])\<close>,
  \<open>Trans(M)[m\<^sub>n]\<close>, \<open>Trans(M[n+1])\<close> respectively.  The scb-components name the
  unexposed internal \<open>Trans\<close>-recursion term \<open>t\<^sub>2\<close> (and the scb-strings
  \<open>s'\<^sub>0\<close>/\<open>b'\<^sub>0\<close>); not faithfully expressible.  BLOCKING SYMBOLS: \<open>t\<^sub>2\<close>,
  \<open>s'\<^sub>0\<close>, \<open>b'\<^sub>0\<close>.\<close>


subsection \<open>§8.6 条件(VI)の下での展開規則 (Expansion rule under condition (VI))\<close>

text \<open>This subsection (article ## 条件(VI)の下での展開規則, content.md 5482–5848)
  proves the exchange relation between \<open>Trans\<close> and the pair-sequence fundamental
  sequence under condition (VI), via three auxiliary lemmas.

  COMMON SETUP / NOTATION (as in §8.1/§8.3/§8.4):
    \<^item> \<open>j\<^sub>1 = Lng M - 1\<close>; \<open>j\<^sub>0 = parent M 0 j\<^sub>1\<close> (the row-0 nearest ancestor of
      \<open>j\<^sub>1\<close>); "\<open>M\<close> satisfies condition (VI)" is \<open>transCondVI M\<close>.
    \<^item> The Buchholz-side fundamental sequence \<open>t[k]\<close> is \<open>operB t (numBT k)\<close>; \<open><\<close> on
      \<open>T\<^bsub>B\<^esub>\<close> is \<open>lessBT\<close>; \<open>n \<in> \<nat>\<^sub>+\<close> is \<open>n \<ge> 1\<close>.  The article's iterated
      principal \<open>D\<^sub>u\<^sup>k 0\<close> (\<open>D\<^sub>u(D\<^sub>u(\<dots>(D\<^sub>u 0)))\<close>, \<open>k\<close> times) is the function
      iteration \<open>(Dpt (enat u) ^^ k) 0\<^sub>B\<close>; the iterated fundamental sequence
      \<open>t[0]\<^sup>k\<close> is \<open>((\<lambda>a. operB a (numBT 0)) ^^ k) t\<close>.
    \<^item> 公差\<open>(1,0)\<close> sequence \<open>((m+j,u))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close> = \<open>map (\<lambda>j. (m+j, u)) [0..<Suc j\<^sub>1]\<close>
      (first coordinate increments by \<open>1\<close>, second is constant \<open>u\<close>); 公差\<open>(1,1)\<close>
      sequence \<open>((u+j,u+j))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close> = \<open>diagSeq u (u+j\<^sub>1)\<close>.\<close>

text \<open>補題（公差\<open>(1,0)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.6, content.md 5496):
  for \<open>u, m, j\<^sub>1 \<in> \<nat>\<close>, with \<open>M := ((m+j,u))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup> \<in> T\<^bsub>PS\<^esub>\<close>,
  \<open>Trans(M) = 0\<close> if \<open>j\<^sub>1 = 0 \<and> u = 0\<close>, and \<open>Trans(M) = D\<^sub>u\<^sup>j\<^sub>1\<^sup>+\<^sup>1 0\<close> if
  \<open>j\<^sub>1 > 0 \<or> u > 0\<close>.  Transcribable: states only \<open>Trans\<close> of an explicit sequence
  against an iterated principal term \<open>(Dpt (enat u) ^^ (j\<^sub>1+1)) 0\<^sub>B\<close>.\<close>

lemma p_8_6_const2nd_Trans:
  fixes u m j1 :: nat
  defines "M \<equiv> map (\<lambda>j. (m + j, u)) [0..<Suc j1]"
  assumes "M \<in> T_PS"
  shows "(j1 = 0 \<and> u = 0 \<longrightarrow> Trans M = 0\<^sub>B)
       \<and> (j1 > 0 \<or> u > 0 \<longrightarrow> Trans M = (Dpt (enat u) ^^ (j1 + 1)) 0\<^sub>B)"
  sorry

text \<open>補題（公差\<open>(1,1)\<close>のペア数列の\<open>Trans\<close>の展開規則） (§8.6, content.md 5575):
  for \<open>u, j\<^sub>1 \<in> \<nat>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, with \<open>M := ((u+j,u+j))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup> \<in> T\<^bsub>PS\<^esub>\<close>
  (\<open>= diagSeq u (u+j\<^sub>1)\<close>), if \<open>j\<^sub>1 > 1\<close> then
  \<open>Trans(M[n]) = D\<^sub>u D\<^bsub>u+j\<^sub>1-1\<^esub>\<^sup>n 0\<close>.  Transcribable: \<open>D\<^bsub>u+j\<^sub>1-1\<^esub>\<^sup>n 0\<close> is
  \<open>(Dpt (enat (u+j\<^sub>1-1)) ^^ n) 0\<^sub>B\<close>, then one outer \<open>D\<^sub>u\<close>.\<close>

lemma p_8_6_diagSeq_Trans_oper:
  fixes u j1 n :: nat
  defines "M \<equiv> diagSeq u (u + j1)"
  assumes "M \<in> T_PS" "0 < n" "j1 > 1"
  shows "Trans ((M::pairseq)[n]) = Dpt (enat u) ((Dpt (enat (u + j1 - 1)) ^^ n) 0\<^sub>B)"
  sorry

text \<open>補題（順序数項の末尾単項の零化可能性） (§8.6, content.md 5621):
  for \<open>t, t' \<in> T\<^bsub>B\<^esub>\<close>, \<open>s, b \<in> \<Sigma>\<^bsup><\<omega>\<^esup>\<close>, and \<open>u, v \<in> \<nat>\<close>, if
  \<open>(s, D\<^sub>u(t' + D\<^sub>v 0), b)\<close> is an scb-decomposition of \<open>t\<close>, then there is
  \<open>k \<in> \<nat>\<close> with \<open>0 < k \<le> v+1\<close> such that \<open>(s, D\<^sub>u t', b)\<close> is an scb-decomposition
  of \<open>t[0]\<^sup>k\<close>.  Transcribable: the scb-decomposition is \<open>scb_decomp\<close> with the
  \<open>c\<close>-component flattened (\<open>flatBT\<close>), and \<open>t[0]\<^sup>k\<close> is the \<open>k\<close>-fold iterate of
  \<open>\<lambda>a. operB a (numBT 0)\<close>.\<close>

lemma p_8_6_trailing_principal_annihilable:
  fixes t t' :: BT and s b :: "Sym list" and u v :: nat
  assumes "t \<in> T_B" "t' \<in> T_B"
    and "scb_decomp t s (flatBT (Dpt (enat u) (t' +\<^sub>B Dpt (enat v) 0\<^sub>B))) b"
  shows "\<exists>k. 0 < k \<and> k \<le> v + 1
            \<and> scb_decomp (((\<lambda>a. operB a (numBT 0)) ^^ k) t)
                         s (flatBT (Dpt (enat u) t')) b"
  sorry

text \<open>命題（条件(VI)の下での\<open>Trans\<close>と基本列の交換関係） (§8.6, content.md 5484):
  for \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, using the symbols of the \<open>Trans\<close>
  recursion, set \<open>m\<^sub>n := n-2\<close> if \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible (\<open>adm M j\<^sub>0\<close>) and
  \<open>m\<^sub>n := n-1\<close> otherwise; if \<open>j\<^sub>1 > 1\<close> and \<open>M\<close> satisfies condition (VI), then:
    (1) if \<open>m\<^sub>n = -1\<close> (i.e. \<open>n = 1\<close> and \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible), there is
        \<open>k \<in> \<nat>\<close> with \<open>1 < k \<le> M\<^bsub>1,j\<^sub>1\<^esub>+1\<close> and
        \<open>Trans(M[n]) = Trans(M)[0]\<^sup>k\<close>;
    (2) if \<open>m\<^sub>n \<ge> 0\<close>, then \<open>Trans(M[n]) = Trans(M)[m\<^sub>n]\<close>;
    (3) \<open>Trans(M[n]) < Trans(M)\<close>.
  Modelling note: the integer-valued index \<open>m\<^sub>n \<in> \<nat> \<union> {-1}\<close> is fully determined
  by \<open>n\<close> and the exposed predicate \<open>adm M j\<^sub>0\<close> (\<open>j\<^sub>0 = parent M 0 (Lng M - 1)\<close>),
  so it need not be exposed as a separate \<open>Trans\<close>-internal: the case \<open>m\<^sub>n = -1\<close>
  is \<open>n = 1 \<and> adm M j\<^sub>0\<close>, the value of \<open>m\<^sub>n\<close> in case (2) is \<open>n - 2\<close> under
  \<open>adm M j\<^sub>0\<close> (here \<open>n \<ge> 2\<close>) and \<open>n - 1\<close> otherwise.  Hence all three conclusions
  are transcribable without exposing the \<open>Trans\<close>-recursion locals
  \<open>s\<^sub>1/c\<^sub>1/c\<^sub>2/b\<^sub>1/t\<^sub>2/v\<close>.  \<open>Trans(M)[0]\<^sup>k = ((\<lambda>a. operB a (numBT 0)) ^^ k) (Trans M)\<close>;
  \<open>Trans(M)[m\<^sub>n] = operB (Trans M) (numBT m\<^sub>n)\<close>.\<close>

lemma p_8_6_Trans_fseq_condVI:
  fixes M :: pairseq and n :: nat
  defines "j0 \<equiv> parent M 0 (Lng M - 1)"
  assumes "M \<in> ST_PS" "M \<in> PT_PS" "0 < n"
    and "Lng M - 1 > 1" "transCondVI M"
  shows "\<comment> \<open>(1) the case \<open>m\<^sub>n = -1\<close>, i.e. \<open>n = 1 \<and> adm M j\<^sub>0\<close>\<close>
         (n = 1 \<and> adm M j0 \<longrightarrow>
            (\<exists>k. 1 < k \<and> k \<le> entry M 1 (Lng M - 1) + 1
               \<and> Trans (M[n]) = ((\<lambda>a. operB a (numBT 0)) ^^ k) (Trans M)))
       \<and> \<comment> \<open>(2) the case \<open>m\<^sub>n \<ge> 0\<close>, with \<open>m\<^sub>n = n-2\<close> if \<open>adm M j\<^sub>0\<close> else \<open>n-1\<close>\<close>
         (\<not> (n = 1 \<and> adm M j0) \<longrightarrow>
            Trans (M[n]) = operB (Trans M) (numBT (if adm M j0 then n - 2 else n - 1)))
       \<and> \<comment> \<open>(3)\<close>
         lessBT (Trans (M[n])) (Trans M)"
  sorry


subsection \<open>§8.7 主結果 (Main result)\<close>

text \<open>補題（公差\<open>(0,0)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.7, article 5857):
  for \<open>u, j\<^sub>1 \<in> \<nat>\<close>, the constant (公差\<open>(0,0)\<close>) sequence
  \<open>M = ((u,u))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close> (= \<open>replicate (Suc j\<^sub>1) (u,u)\<close>) has
  \<open>Trans(M) = (D\<^sub>0 0)\<times>j\<^sub>1\<close> if \<open>u = 0\<close> and \<open>(D\<^sub>u 0)\<times>(j\<^sub>1+1)\<close> if \<open>u > 0\<close>.
  \<open>(D\<^sub>u 0)\<times>k = multBT (D\<^sub>u 0) k\<close> (\<open>k\<close>-fold \<open>+\<^sub>B\<close>-sum).\<close>

lemma p_8_7_const00_Trans:
  shows "Trans (replicate (Suc j1) (u, u))
           = (if u = 0 then multBT (Dpt (enat u) 0\<^sub>B) j1
              else multBT (Dpt (enat u) 0\<^sub>B) (Suc j1))"
  sorry

text \<open>補題（基本列の降下性） (§8.7, article 5869):
  for \<open>M \<in> ST\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, if \<open>Lng M > 1\<close> then
  \<open>Trans(M[n]) < Trans(M)\<close> (\<open><\<close> on \<open>T\<^bsub>B\<^esub>\<close> = \<open>lessBT\<close>).\<close>

lemma p_8_7_fseq_descend:
  assumes "M \<in> ST_PS" "n \<ge> 1" "Lng M > 1"
  shows "lessBT (Trans (M[n])) (Trans M)"
  sorry

text \<open>補題（順序数項の再帰構造） (§8.7, article 5953):
  for \<open>t \<in> OT\<^bsub>B\<^esub>\<close>, \<open>c \<in> T\<^bsub>B\<^esub>\<close> and \<open>s, b \<in> \<Sigma>\<^bsup><\<omega>\<^esup>\<close> (= \<^typ>\<open>Sym list\<close>),
  if \<open>(s,c,b)\<close> is an scb-decomposition of \<open>t\<close> (\<open>scb_decomp t s (flatBT c) b\<close>)
  then \<open>c\<close> is an ordinal term (\<open>c \<in> OT\<close>).\<close>

lemma p_8_7_OT_scb_recursive:
  assumes "t \<in> OT_B" "c \<in> T_B" "scb_decomp t s (flatBT c) b"
  shows "c \<in> OT"
  sorry

text \<open>補題（順序数項の共終数の遺伝性） (§8.7, article 5962):
  for \<open>t, t' \<in> T\<^bsub>B\<^esub>\<close> and \<open>s, b \<in> \<Sigma>\<^bsup><\<omega>\<^esup>\<close>, if \<open>dom(t') = \<nat>\<close>
  (\<open>domB t' = NatSet\<close>) and \<open>(s,t',b)\<close> is an scb-decomposition of \<open>t\<close>, then
  \<open>dom(t) = \<nat>\<close>.\<close>

lemma p_8_7_OT_dom_hereditary:
  assumes "t \<in> T_B" "t' \<in> T_B" "domB t' = NatSet" "scb_decomp t s (flatBT t') b"
  shows "domB t = NatSet"
  sorry

text \<open>補題（順序数項の末尾項の零化可能性） (§8.7, article 5971):
  for \<open>t \<in> OT\<^bsub>B\<^esub>\<close>, \<open>t' \<in> T\<^bsub>B\<^esub>\<close>, \<open>s, b \<in> \<Sigma>\<^bsup><\<omega>\<^esup>\<close>, \<open>u \<in> \<nat>\<close>, if
  \<open>(s, D\<^sub>u t', b)\<close> is an scb-decomposition of \<open>t\<close>, then some \<open>k\<close> makes
  \<open>(s, D\<^sub>u 0, b)\<close> an scb-decomposition of \<open>t[0]\<^sup>k\<close>
  (\<open>t[0]\<^sup>k = ((\<lambda>a. operB a (numBT 0)) ^^ k) t\<close>).\<close>

lemma p_8_7_OT_tail_annihilable:
  assumes "t \<in> OT_B" "t' \<in> T_B"
    and "scb_decomp t s (flatBT (Dpt (enat u) t')) b"
  shows "\<exists>k. scb_decomp (((\<lambda>a. operB a (numBT 0)) ^^ k) t) s
                        (flatBT (Dpt (enat u) 0\<^sub>B)) b"
  sorry

text \<open>補題（\<open>Pred\<close>と\<open>[0]\<close>の関係） (§8.7, article 6014):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> (article writes \<open>PT\<^bsub>B\<^esub>\<close>, a typo for \<open>PT\<^bsub>PS\<^esub>\<close>),
  using the symbols of the recursive definition of \<open>Trans\<close>, if \<open>j\<^sub>1 > 1\<close>,
  \<open>M\<close> fails condition (VI), and \<open>Trans(M)\<close> is an ordinal term, then some \<open>k\<close>
  gives \<open>Trans(M)[0]\<^sup>k = t\<^sub>1\<close>.  The internal \<open>t\<^sub>1\<close> of \<open>Trans\<close> is \<open>Trans (Pred M)\<close>,
  so it is exposed as such here.\<close>

lemma p_8_7_Pred_oper0:
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "Lng M - 1 > 1"
    and "\<not> transCondVI M" "Trans M \<in> OT"
  shows "\<exists>k. ((\<lambda>a. operB a (numBT 0)) ^^ k) (Trans M) = Trans (Pred M)"
  sorry

text \<open>補題（順序数項の基本例） (§8.7, article 6066): four basic memberships in
  \<open>OT\<^bsub>B\<^esub>\<close>.  \<open>D\<^sub>u\<^sup>n 0 = (Dpt (enat u) ^^ n) 0\<^sub>B\<close>; \<open>(D\<^sub>u 0)\<times>(n-1) = multBT (D\<^sub>u 0) (n-1)\<close>.\<close>

lemma p_8_7_OT_examples:
  shows "Dpt (enat u) 0\<^sub>B \<in> OT_B"
    and "Dpt (enat u) (Dpt (enat v) 0\<^sub>B) \<in> OT_B"
    and "n \<ge> 1 \<Longrightarrow> multBT (Dpt (enat u) 0\<^sub>B) (n - 1) \<in> OT_B"
    and "(Dpt (enat u) ^^ n) 0\<^sub>B \<in> OT_B"
  sorry

text \<open>補題（\<open>Trans\<close>が標準形を保つこと） (§8.7, article 6122):
  for \<open>M \<in> ST\<^bsub>PS\<^esub>\<close>, \<open>Trans(M) \<in> OT\<^bsub>B\<^esub>\<close> (\<open>Trans\<close> lands in ordinal terms).\<close>

lemma p_8_7_Trans_preserves_OT:
  assumes "M \<in> ST_PS"
  shows "Trans M \<in> OT_B"
  sorry

text \<open>定理（標準形ペア数列システムの停止性） (§8.7, article 5851):
  \<open>ST\<^bsub>PS\<^esub> \<times> \<nat>\<^sub>+ \<subseteq> Dom(F)\<close>.  Here \<open>Dom(F)\<close> is \<open>Fdom f\<close> (§5.4); the auxiliary
  map \<open>f : \<nat>\<^sub>+ \<to> \<nat>\<^sub>+\<close> is fixed (article 346), modelled by the positivity
  hypothesis \<open>1 \<le> k \<Longrightarrow> 1 \<le> f k\<close>.  The proof is the well-foundedness of \<open><\<close>
  on \<open>OT\<^bsub>B\<^esub>\<close> ([Buc1] Lemma 2.2) together with 基本列の降下性 + Trans が標準形を
  保つこと: each expansion step strictly decreases \<open>Trans\<close>.\<close>

theorem p_8_7_termination:
  assumes "M \<in> ST_PS" "n \<ge> 1" "\<And>k. 1 \<le> k \<Longrightarrow> 1 \<le> f k"
  shows "Fdom f M n"
  sorry

end
