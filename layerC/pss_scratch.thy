theory pss_scratch
  imports "PSS_B.pss_wip"
begin

text \<open>LAYER c — sub-agent scratch theory.  Sub-agents add this round's in-progress
  lemmas here and build session PSS_C, which sits on top of the pre-built PSS_B heap
  (pss_wip) so only this file is processed.  Proven lemmas ACCUMULATE here round after
  round; when the file fattens (per-round build minutes), the parent folds the whole
  body down into pss_wip (LAYER b, one-time PSS_B rebuild) and resets this file
  (last fold: 2026-07-11, 78k lines of rounds up to r54).  Topic-level orientation
  for the folded body: grep docs/thy-toc.md (regenerate: python3 tools/make_toc.py).\<close>



(* ===================================================================== *)
(* ===== r54 od4: the OTpred residuals {DEEPOT, NOBR}.               ===== *)
(* ===== Brick A: the right-spine un-insertion relation od4_R and    ===== *)
(* ===== its OT-algebra (order transfer via a size argument;         ===== *)
(* ===== escape-set shrinking; isOT preservation).  STEP-0 r54       ===== *)
(* ===== validation: T-checks 2232/2232, U-checks 1872/1872,         ===== *)
(* ===== W-checks 140/140, plus 1882/1882 genuine deepened ST_PS     ===== *)
(* ===== instances (od4_step0.py).                                    ===== *)
(* ===================================================================== *)

section \<open>r54-od4 --- \<open>OTpred\<close> residuals: spine un-insertion (prefix \<open>od4_\<close>)\<close>

subsection \<open>The relation: one trailing principal removed (or replaced by a
  smaller trivial \<open>D\<^bsub>w\<^esub> 0\<close>) at ONE position along the right spine\<close>

text \<open>\<open>od4_R a b\<close>: \<open>a\<close> arises from \<open>b\<close> by, at one right-spine level, either
  dropping the trailing principal, or replacing it by a \<open>lessBP\<close>-smaller
  TRIVIAL principal \<open>D\<^bsub>w\<^esub> 0\<^sub>B\<close> (the \<open>transCondVI\<close> boundary shape).  This is
  exactly the \<open>Trans (Pred M)\<close>-vs-\<open>Trans M\<close> surgery shape, read BACKWARDS:
  every \<open>transC2\<close> branch either APPENDS one principal at a spine level
  (conditions I/III/V; the \<open>t\<^sub>2 = 0\<close> / \<open>leftDj0\<close> / else branches) or replaces
  the body by \<open>D\<^bsub>e\<^esub> 0\<close> above a trivial \<open>c\<^sub>1\<close> (condition VI).\<close>

inductive od4_R :: "BT \<Rightarrow> BT \<Rightarrow> bool" where
  od4_R_drop: "od4_R (Trm ps) (Trm (ps @ [p]))"
| od4_R_triv: "lessBP (DB w 0\<^sub>B) p \<Longrightarrow> od4_R (Trm (ps @ [DB w 0\<^sub>B])) (Trm (ps @ [p]))"
| od4_R_deep: "od4_R c c' \<Longrightarrow> od4_R (Trm (ps @ [DB w c])) (Trm (ps @ [DB w c']))"

text \<open>(r55 audit: the r54 draft's \<open>od4_R_cons\<close> --- a cons-context closure ---
  was EXCISED: it was cited nowhere (the scb-context lift \<open>od4_scbext_R\<close> below
  works with @{thm [source] otx2_align3} directly), and its \<open>cases\<close>-binding
  syntax was one of the two r54 build errors.)\<close>

subsection \<open>Size measure and the escape-size bound\<close>

fun od4_sz :: "BT \<Rightarrow> nat" and od4_szP :: "BP \<Rightarrow> nat" where
  "od4_sz (Trm ps) = 1 + sum_list (map od4_szP ps)"
| "od4_szP (DB u b) = 1 + od4_sz b"

lemma od4_sz_pos: "1 \<le> od4_sz t"
  by (cases t) simp

lemma od4_szP_ge2: "2 \<le> od4_szP p"
proof -
  obtain u b where "p = DB u b" by (cases p)
  thus ?thesis using od4_sz_pos[of b] by simp
qed

lemma od4_szP_mem_le: "p \<in> set ps \<Longrightarrow> od4_szP p \<le> sum_list (map od4_szP ps)"
proof -
  assume "p \<in> set ps"
  then obtain pre post where "ps = pre @ p # post" by (meson split_list)
  thus ?thesis by simp
qed

text \<open>Every \<open>G\<^sub>B\<close>-escape is a proper nested body, hence strictly smaller.\<close>

lemma od4_GBT_sz:
  "y \<in> GBT u t \<Longrightarrow> od4_sz y < od4_sz t"
proof (induction "od4_sz t" arbitrary: t y rule: less_induct)
  case less
  obtain ps where tps: "t = Trm ps" by (cases t)
  obtain p where pmem: "p \<in> set ps" and yin: "y \<in> GBP u p"
    using less.prems tps by auto
  obtain v b where pvb: "p = DB v b" by (cases p)
  have uv: "u \<le> v" and ycase: "y = b \<or> y \<in> GBT u b"
    using yin pvb by (auto split: if_split_asm)
  have szle: "od4_szP p \<le> sum_list (map od4_szP ps)"
    by (rule od4_szP_mem_le[OF pmem])
  have bsz: "od4_sz b < od4_sz t" using tps pvb szle by simp
  from ycase show ?case
  proof
    assume "y = b"
    thus ?thesis using bsz by simp
  next
    assume "y \<in> GBT u b"
    hence "od4_sz y < od4_sz b" by (rule less.hyps[OF bsz])
    thus ?thesis using bsz by simp
  qed
qed

subsection \<open>\<open>od4_R\<close> is a strict-order step\<close>

lemma od4_R_lessBT:
  assumes "od4_R a b"
  shows "lessBT a b"
  using assms
proof (induction rule: od4_R.induct)
  case (od4_R_drop ps p)
  have "lessBT (Trm ps) (Trm (ps @ p # []))" by (rule ddx_lessBT_snoc)
  thus ?case by simp
next
  case (od4_R_triv w p ps)
  thus ?case using otx2_lessBT_snocsnoc by blast
next
  case (od4_R_deep c c' ps w)
  have "lessBP (DB w c) (DB w c')" using od4_R_deep.IH by simp
  thus ?case using otx2_lessBT_snocsnoc by blast
qed

subsection \<open>The ORDER-TRANSFER lemma: \<open>y < b\<close> and \<open>od4_sz y < od4_sz a\<close> give
  \<open>y < a\<close> across an un-insertion step\<close>

text \<open>Common-prefix peel: reduce a comparison against \<open>Trm (ps \<frown> Y)\<close> vs
  \<open>Trm (ps \<frown> X)\<close> to the core case \<open>ps = []\<close>.\<close>

lemma od4_peel_less:
  assumes core: "\<And>z. lessBT z (Trm Y) \<Longrightarrow> od4_sz z < od4_sz (Trm X) \<Longrightarrow> lessBT z (Trm X)"
  shows "lessBT y (Trm (ps @ Y)) \<Longrightarrow> od4_sz y < od4_sz (Trm (ps @ X)) \<Longrightarrow> lessBT y (Trm (ps @ X))"
proof (induction ps arbitrary: y)
  case Nil
  thus ?case using core by simp
next
  case (Cons q ps')
  obtain ys where yys: "y = Trm ys" by (cases y)
  show ?case
  proof (cases ys)
    case Nil
    show ?thesis using yys Nil by simp
  next
    case (Cons r ys')
    have split: "lessBP r q \<or> (r = q \<and> lessBT (Trm ys') (Trm (ps' @ Y)))"
      using Cons.prems(1) yys Cons by simp
    show ?thesis
    proof (cases "lessBP r q")
      case True
      thus ?thesis using yys Cons by simp
    next
      case False
      have req: "r = q" and tl: "lessBT (Trm ys') (Trm (ps' @ Y))"
        using split False by blast+
      have sz': "od4_sz (Trm ys') < od4_sz (Trm (ps' @ X))"
        using Cons.prems(2) yys Cons req by simp
      have "lessBT (Trm ys') (Trm (ps' @ X))"
        by (rule Cons.IH[OF tl sz'])
      thus ?thesis using yys Cons req by simp
    qed
  qed
qed

lemma od4_transfer_all:
  assumes R: "od4_R a b"
  shows "\<forall>y. lessBT y b \<longrightarrow> od4_sz y < od4_sz a \<longrightarrow> lessBT y a"
  using R
proof (induction rule: od4_R.induct)
  case (od4_R_drop ps p)
  have core: "\<And>z. lessBT z (Trm [p]) \<Longrightarrow> od4_sz z < od4_sz (Trm []) \<Longrightarrow> lessBT z (Trm [])"
  proof -
    fix z :: BT
    assume "od4_sz z < od4_sz (Trm [])"
    hence "od4_sz z < 1" by simp
    thus "lessBT z (Trm [])" using od4_sz_pos[of z] by simp
  qed
  show ?case
  proof (intro allI impI)
    fix y assume y1: "lessBT y (Trm (ps @ [p]))" and y2: "od4_sz y < od4_sz (Trm ps)"
    have y2': "od4_sz y < od4_sz (Trm (ps @ []))" using y2 by simp
    have "lessBT y (Trm (ps @ []))" by (rule od4_peel_less[OF core y1 y2'])
    thus "lessBT y (Trm ps)" by simp
  qed
next
  case (od4_R_triv w p ps)
  have core: "\<And>z. lessBT z (Trm [p]) \<Longrightarrow> od4_sz z < od4_sz (Trm [DB w 0\<^sub>B])
                \<Longrightarrow> lessBT z (Trm [DB w 0\<^sub>B])"
  proof -
    fix z :: BT
    assume zsz: "od4_sz z < od4_sz (Trm [DB w 0\<^sub>B])"
    obtain zs where zzs: "z = Trm zs" by (cases z)
    have "zs = []"
    proof (cases zs)
      case (Cons z0 zs')
      have "od4_szP z0 \<le> sum_list (map od4_szP zs)" using Cons by simp
      hence "3 \<le> od4_sz z" using od4_szP_ge2[of z0] zzs by simp
      moreover have "od4_sz (Trm [DB w 0\<^sub>B]) = 3" by simp
      ultimately show ?thesis using zsz by simp
    qed simp
    thus "lessBT z (Trm [DB w 0\<^sub>B])" using zzs by simp
  qed
  show ?case
  proof (intro allI impI)
    fix y assume y1: "lessBT y (Trm (ps @ [p]))"
      and y2: "od4_sz y < od4_sz (Trm (ps @ [DB w 0\<^sub>B]))"
    show "lessBT y (Trm (ps @ [DB w 0\<^sub>B]))" by (rule od4_peel_less[OF core y1 y2])
  qed
next
  case (od4_R_deep c c' ps w)
  have core: "\<And>z. lessBT z (Trm [DB w c']) \<Longrightarrow> od4_sz z < od4_sz (Trm [DB w c])
                \<Longrightarrow> lessBT z (Trm [DB w c])"
  proof -
    fix z :: BT
    assume zl: "lessBT z (Trm [DB w c'])" and zsz: "od4_sz z < od4_sz (Trm [DB w c])"
    obtain zs where zzs: "z = Trm zs" by (cases z)
    show "lessBT z (Trm [DB w c])"
    proof (cases zs)
      case Nil
      show ?thesis using zzs Nil by simp
    next
      case (Cons z0 zs')
      obtain u d where z0e: "z0 = DB u d" by (cases z0)
      have notail: "\<not> lessBT (Trm zs') (Trm [])" by (cases zs') simp_all
      have hd: "lessBP (DB u d) (DB w c')"
        using zl zzs Cons z0e notail by auto
      have ud: "u < w \<or> (u = w \<and> lessBT d c')" using hd by simp
      show ?thesis
      proof (cases "u < w")
        case True
        hence "lessBP (DB u d) (DB w c)" by simp
        thus ?thesis using zzs Cons z0e by simp
      next
        case False
        have ueq: "u = w" and dc': "lessBT d c'" using ud False by auto
        have dsz: "od4_sz d < od4_sz c" using zsz zzs Cons z0e by simp
        have "lessBT d c" using od4_R_deep.IH dc' dsz by blast
        hence "lessBP (DB u d) (DB w c)" using ueq by simp
        thus ?thesis using zzs Cons z0e by simp
      qed
    qed
  qed
  show ?case
  proof (intro allI impI)
    fix y assume y1: "lessBT y (Trm (ps @ [DB w c']))"
      and y2: "od4_sz y < od4_sz (Trm (ps @ [DB w c]))"
    show "lessBT y (Trm (ps @ [DB w c]))" by (rule od4_peel_less[OF core y1 y2])
  qed
qed

lemma od4_transfer:
  assumes R: "od4_R a b" and yb: "lessBT y b" and ysz: "od4_sz y < od4_sz a"
  shows "lessBT y a"
  using od4_transfer_all[OF R] yb ysz by blast

subsection \<open>Escape-set shrinking across an un-insertion step\<close>

lemma od4_R_GBT:
  assumes "od4_R a b"
  shows "\<And>y. y \<in> GBT u a \<Longrightarrow> y \<in> GBT u b \<or> y = 0\<^sub>B \<or> (\<exists>y'. od4_R y y' \<and> y' \<in> GBT u b)"
  using assms
proof (induction rule: od4_R.induct)
  case (od4_R_drop ps p)
  thus ?case by auto
next
  case (od4_R_triv w p ps)
  from od4_R_triv.prems have "y \<in> GBT u (Trm ps) \<or> y \<in> GBP u (DB w 0\<^sub>B)" by auto
  thus ?case
  proof
    assume "y \<in> GBT u (Trm ps)"
    thus ?case by auto
  next
    assume "y \<in> GBP u (DB w 0\<^sub>B)"
    hence "y = 0\<^sub>B" by (auto split: if_split_asm)
    thus ?case by blast
  qed
next
  case (od4_R_deep c c' ps w)
  from od4_R_deep.prems have "y \<in> GBT u (Trm ps) \<or> y \<in> GBP u (DB w c)" by auto
  thus ?case
  proof
    assume "y \<in> GBT u (Trm ps)"
    thus ?case by auto
  next
    assume yin: "y \<in> GBP u (DB w c)"
    have uw: "u \<le> w" and ycase: "y = c \<or> y \<in> GBT u c"
      using yin by (auto split: if_split_asm)
    from ycase show ?case
    proof
      assume yc: "y = c"
      have "c' \<in> GBP u (DB w c')" using uw by simp
      hence "c' \<in> GBT u (Trm (ps @ [DB w c']))" by auto
      thus ?case using yc od4_R_deep.hyps by blast
    next
      assume "y \<in> GBT u c"
      from od4_R_deep.IH[OF this] show ?case
      proof (elim disjE exE conjE)
        assume "y \<in> GBT u c'"
        hence "y \<in> GBP u (DB w c')" using uw by simp
        thus ?case by auto
      next
        assume "y = 0\<^sub>B" thus ?case by blast
      next
        fix y' assume "od4_R y y'" and "y' \<in> GBT u c'"
        moreover hence "y' \<in> GBP u (DB w c')" using uw by simp
        ultimately show ?case by auto
      qed
    qed
  qed
qed

subsection \<open>\<open>descP\<close> under a smaller snoc, and the site \<open>G\<close>-transfer\<close>

lemma od4_leBT_trans: "leBT x y \<Longrightarrow> leBT y z \<Longrightarrow> leBT x z"
  using lessBT_trans by blast

lemma od4_descP_snoc:
  "descP (ps @ [p]) \<Longrightarrow> leBT (Trm [p']) (Trm [p]) \<Longrightarrow> descP (ps @ [p'])"
proof (induction ps rule: descP.induct)
  case 1 thus ?case by simp
next
  case (2 q)
  have "leBT (Trm [p]) (Trm [q])" using "2.prems"(1) by simp
  hence "leBT (Trm [p']) (Trm [q])" using od4_leBT_trans[OF "2.prems"(2)] by blast
  thus ?case by simp
next
  case (3 q0 q1 rest)
  have "leBT (Trm [q1]) (Trm [q0])" and "descP ((q1 # rest) @ [p])"
    using "3.prems"(1) by simp_all
  thus ?case using "3.IH" "3.prems"(2) by simp
qed

text \<open>The per-node \<open>G\<^sub>B\<close>-domination transfers backwards across \<open>od4_R\<close>: the
  new escapes are old escapes (order transfer via the size bound), \<open>0\<^sub>B\<close>, or
  \<open>od4_R\<close>-predecessors of old escapes (chain through the old bound).\<close>

lemma od4_site_G:
  assumes R: "od4_R c c'"
    and host: "\<forall>y \<in> GBT w c'. lessBT y c'"
  shows "\<forall>y \<in> GBT w c. lessBT y c"
proof
  fix y assume yin: "y \<in> GBT w c"
  have szy: "od4_sz y < od4_sz c" by (rule od4_GBT_sz[OF yin])
  obtain cs where ccs: "c = Trm cs" by (cases c)
  have csne: "cs \<noteq> []"
  proof
    assume "cs = []"
    thus False using yin ccs by simp
  qed
  from od4_R_GBT[OF R yin] show "lessBT y c"
  proof (elim disjE exE conjE)
    assume "y \<in> GBT w c'"
    hence "lessBT y c'" using host by blast
    thus ?thesis by (rule od4_transfer[OF R _ szy])
  next
    assume "y = 0\<^sub>B"
    thus ?thesis using ccs csne by (cases cs) simp_all
  next
    fix y' assume Ry: "od4_R y y'" and y'in: "y' \<in> GBT w c'"
    have "lessBT y y'" by (rule od4_R_lessBT[OF Ry])
    moreover have "lessBT y' c'" using host y'in by blast
    ultimately have "lessBT y c'" by (rule lessBT_trans)
    thus ?thesis by (rule od4_transfer[OF R _ szy])
  qed
qed

subsection \<open>MAIN: \<open>od4_R\<close> preserves \<open>isOT\<close> backwards\<close>

lemma od4_R_isOT:
  assumes "od4_R a b"
  shows "isOT_BT b \<Longrightarrow> isOT_BT a"
  using assms
proof (induction rule: od4_R.induct)
  case (od4_R_drop ps p)
  have el: "\<forall>q \<in> set ps. isOT_BP q" and dp: "descP (ps @ [p])"
    using od4_R_drop.prems by auto
  show ?case using el descP_append1[OF dp] by simp
next
  case (od4_R_triv w p ps)
  have el: "\<forall>q \<in> set ps. isOT_BP q" and dp: "descP (ps @ [p])"
    using od4_R_triv.prems by auto
  have newOT: "isOT_BP (DB w 0\<^sub>B)" by simp
  have le: "leBT (Trm [DB w 0\<^sub>B]) (Trm [p])" using od4_R_triv.hyps by simp
  have "descP (ps @ [DB w 0\<^sub>B])" by (rule od4_descP_snoc[OF dp le])
  thus ?case using el newOT by auto
next
  case (od4_R_deep c c' ps w)
  have el: "\<forall>q \<in> set ps. isOT_BP q" and dp: "descP (ps @ [DB w c'])"
    and lastOT: "isOT_BP (DB w c')"
    using od4_R_deep.prems by auto
  have c'OT: "isOT_BT c'" and hostG: "\<forall>y \<in> GBT w c'. lessBT y c'"
    using lastOT by simp_all
  have cOT: "isOT_BT c" by (rule od4_R_deep.IH[OF c'OT])
  have cG: "\<forall>y \<in> GBT w c. lessBT y c"
    by (rule od4_site_G[OF od4_R_deep.hyps hostG])
  have newOT: "isOT_BP (DB w c)" using cOT cG by simp
  have "lessBT c c'" by (rule od4_R_lessBT[OF od4_R_deep.hyps])
  hence "lessBP (DB w c) (DB w c')" by simp
  hence le: "leBT (Trm [DB w c]) (Trm [DB w c'])" by simp
  have "descP (ps @ [DB w c])" by (rule od4_descP_snoc[OF dp le])
  thus ?case using el newOT by auto
qed

lemma od4_R_OT_B:
  assumes R: "od4_R a b" and bOT: "b \<in> OT_B" and aTB: "a \<in> T_B"
  shows "a \<in> OT_B"
proof -
  have "isOT_BT b" using bOT by (simp add: OT_B_def OT_def)
  hence "isOT_BT a" by (rule od4_R_isOT[OF R])
  thus ?thesis using aTB by (simp add: OT_B_def OT_def)
qed

(* ===== end r54-od4 Brick A (un-insertion OT algebra) ===== *)

subsection \<open>Brick B: lifting \<open>od4_R\<close> through a shared scb context (the
  \<open>otx2_align3\<close> spine-alignment engine, two-term instance)\<close>

text \<open>If two terms carry same-head principal cores \<open>D\<^sub>v ca\<close> / \<open>D\<^sub>v ca'\<close> at the
  SAME scb hole \<open>(s, b)\<close> (all-\<open>RP\<close> tail) and the bodies are un-insertion
  related, the whole terms are: peel shared right-spine levels with
  @{thm [source] otx2_align3} (third slot duplicated), close with
  @{thm [source] od4_R_deep}.\<close>

lemma od4_scbext_R:
  assumes e1: "flatBT t = s @ flatBP (DB v ca) @ b"
    and e2: "flatBT t' = s @ flatBP (DB v ca') @ b"
    and bR: "\<forall>x \<in> set b. x = RP"
    and site: "od4_R ca ca'"
  shows "od4_R t t'"
  using e1 e2 bR
proof (induction "od4_sz t" arbitrary: t t' s b rule: less_induct)
  case less
  from otx2_align3[OF less.prems(1) less.prems(2) less.prems(2) less.prems(3)]
  show ?case
  proof (elim disjE exE conjE)
    fix qs
    assume A1: "t = Trm (qs @ [DB v ca])" and A2: "t' = Trm (qs @ [DB v ca'])"
    show ?thesis using A1 A2 od4_R_deep[OF site] by simp
  next
    fix qs w lb1 lb2 lb3 sc bc
    assume B1: "t = Trm (qs @ [DB w lb1])" and B2: "t' = Trm (qs @ [DB w lb2])"
      and F1: "flatBT lb1 = sc @ flatBP (DB v ca) @ bc"
      and F2: "flatBT lb2 = sc @ flatBP (DB v ca') @ bc"
      and BC: "\<forall>x \<in> set bc. x = RP"
    have szlb: "od4_sz lb1 < od4_sz t"
    proof -
      have "od4_szP (DB w lb1) \<le> sum_list (map od4_szP (qs @ [DB w lb1]))"
        by (rule od4_szP_mem_le) simp
      thus ?thesis using B1 by simp
    qed
    have "od4_R lb1 lb2" by (rule less.hyps[OF szlb F1 F2 BC])
    thus ?thesis using B1 B2 od4_R_deep by simp
  qed
qed

(* ===== end r54-od4 Brick B (scb context lifting) ===== *)

(* ===================================================================== *)
(* ===== r55 od4 part 2: closing the OTpred residuals.               ===== *)
(* ===== Brick C0: the condVI+nonadm c1 shape (the ONLY branch       ===== *)
(* =====   needing structural knowledge of t2).                      ===== *)
(* ===== Brick C : the surgery-site un-insertion od4_R t2 body2      ===== *)
(* =====   across ALL transC2 branches.                              ===== *)
(* ===== Brick D : MASTER od4_R (Trans (Pred M)) (Trans M).          ===== *)
(* ===== Brick E : the mono OTpred step, free of Br/cond hypotheses. ===== *)
(* ===== Brick F : DEEPOT + NOBR verbatim, OTpred slot residual-free,===== *)
(* =====   census v4.  r55 STEP-0 validation (od4_r55_check.py):     ===== *)
(* =====   MASTER 0-fail and SITE 0-fail on 550 brute reduced-mono   ===== *)
(* =====   hosts + 654 genuine ST_PS hosts (all condition classes,   ===== *)
(* =====   Br=[] and Br<>[]); OT preservation 0-fail; condVI t2      ===== *)
(* =====   shapes: adm -> 0_B (136/136), nadm -> single trivial      ===== *)
(* =====   D_u 0 with u < M1j1 (21/21).                              ===== *)
(* ===================================================================== *)

section \<open>r55-od4 part 2 --- \<open>OTpred\<close> closed: site, master, \<open>DEEPOT\<close>/\<open>NOBR\<close>\<close>

subsection \<open>Brick C0: the condition-(VI) non-admissible \<open>c\<^sub>1\<close> shape\<close>

text \<open>Under condition (VI) with \<open>\<not> adm M j\<^sub>0\<close> (\<open>j\<^sub>0 = Lng M - 2\<close>), the whole run
  \<open>(j\<^sub>-\<^sub>1, j\<^sub>0]\<close> (\<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close>) is non-admissible, so BOTH coefficient rows
  step \<open>+1\<close> along it (@{thm [source] wnx_run_entries}).  The marked component
  \<open>c\<^sub>1 = Mark (Pred M) j\<^sub>-\<^sub>1\<close> reads back as the \<open>Trans\<close> of the backward slice
  (@{thm [source] m_7_4_Mark_Trans_repr}); the slice's reduction is then the
  literal diagonal \<open>diagSeq u (u+d)\<close> (rebase kills the row-0 offset), whose
  \<open>Trans\<close> is the explicit two-level tower @{thm [source] m_8_1_diagSeq_Trans}.
  Hence \<open>t\<^sub>2 = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> 0\<close>, a SINGLE TRIVIAL principal with head
  \<open>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0 < M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<close> (condition (VI)) --- exactly the \<open>od4_R_triv\<close> shape.\<close>

lemma od4_condVI_nadm_c1:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and cond: "transCondVI M" and j1gt: "1 < Lng M - 1"
    and nadm: "\<not> adm M (transJ0 M)"
  shows "transC1 M = Dpt (enat (entry M 1 (transJm1 M)))
                        (Dpt (enat (entry M 1 (transJ0 M))) 0\<^sub>B)"
    and "transT2 M = Dpt (enat (entry M 1 (transJ0 M))) 0\<^sub>B"
proof -
  let ?j1 = "Lng M - 1"
  let ?j0 = "transJ0 M"
  let ?jm1 = "transJm1 M"
  let ?S = "seg M (transJm1 M) (Lng M - 2)"
  let ?R = "Red (seg M (transJm1 M) (Lng M - 2))"
  let ?k = "entry M 0 (transJm1 M) - entry M 1 (transJm1 M)"
  define u where "u = entry M 1 (transJm1 M)"
  define d where "d = transJ0 M - transJm1 M"
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using j1gt by linarith
  have L3: "2 < Lng M" using j1gt by linarith
  have j0eq: "?j0 = Lng M - 2" using c6gx_condVI_j0(1)[OF cond] j1gt by linarith
  have jm1A: "?jm1 = Adm M ?j0" by (simp add: transJm1_def)
  have jm1lt: "?jm1 < ?j0" using nadm_Adm_lt[OF nadm] jm1A by simp
  have dpos: "0 < d" using jm1lt d_def by linarith
  have jm1d: "?jm1 + d = ?j0" using jm1lt d_def by linarith
  have j0L: "?j0 < Lng M" using j0eq L3 by linarith
  \<comment> \<open>the Marked pair and the Mark--Trans representation\<close>
  have hp0: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have mkd: "(Pred M, ?jm1) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp0]
    by (simp add: transJm1_def transJ0_def transJ1_def)
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: Pred_def)
  have jm1P: "?jm1 < Lng (Pred M) - 1" using jm1lt j0eq LP by linarith
  have repr: "Mark (Pred M) ?jm1 = Trans (seg (Pred M) ?jm1 (Lng (Pred M) - 1))"
    by (rule m_7_4_Mark_Trans_repr[OF mkd predRT jm1P])
  have LPm1: "Lng (Pred M) - 1 = Lng M - 2" using LP by simp
  have segP: "seg (Pred M) ?jm1 (Lng (Pred M) - 1) = ?S"
  proof -
    have ab: "?jm1 \<le> Lng M - 2" using jm1lt j0eq by linarith
    have blt: "Lng M - 2 < Lng M - 1" using L3 by linarith
    show ?thesis using m_7_4_seg_Pred_eq[OF L ab blt] LPm1 by simp
  qed
  \<comment> \<open>ancestry \<open>leR M 0 j\<^sub>-\<^sub>1 j\<^sub>0\<close> via the row-1 admissibilization ancestry\<close>
  have j0leL: "?j0 \<le> Lng M - 1" using j0eq by linarith
  have le1a: "leR M 1 ?jm1 ?j0"
    using adm_row1_ancestry[OF MT j0leL] by (simp add: transJm1_def)
  have le0a: "le0 M ?jm1 ?j0"
    using m_le1_imp_le0[OF le1a] by (simp add: leR_def)
  have leab: "leR M 0 ?jm1 (Lng M - 2)" using le0a j0eq by (simp add: leR_def)
  have ablt: "?jm1 < Lng M - 2" using jm1lt j0eq by linarith
  have bLe: "Lng M - 2 \<le> Lng M - 1" by linarith
  \<comment> \<open>the reduced slice and its geometry\<close>
  have anc: "Red ?R = ?R \<and> monoT ?R \<and> ?S = (IncrFirst ^^ ?k) ?R"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR ablt bLe leab] by simp
  have segIF: "?S = (IncrFirst ^^ ?k) ?R" using anc by simp
  have RRT: "?R \<in> RT_PS" and ST: "?S \<in> T_PS"
    using slice_Red_in_RT_PS[OF MR ablt bLe leab] by simp_all
  have LS: "Lng ?S = Suc (Lng M - 2) - ?jm1" by simp
  have LSd: "Lng ?S = d + 1" using LS j0eq jm1d jm1lt L3 by linarith
  have LR: "Lng ?R = Lng ?S" by (rule m_6_5_Lng_Red[OF ST])
  have LRd: "Lng ?R = d + 1" using LR LSd by simp
  \<comment> \<open>the run entry facts, transported into \<open>?R\<close>\<close>
  have runE: "\<And>t. t \<le> d \<Longrightarrow>
        entry M 0 (?jm1 + t) = entry M 0 ?jm1 + t
      \<and> entry M 1 (?jm1 + t) = entry M 1 ?jm1 + t"
  proof -
    fix t assume "t \<le> d"
    hence tle: "t \<le> ?j0 - Adm M ?j0" using d_def jm1A by simp
    show "entry M 0 (?jm1 + t) = entry M 0 ?jm1 + t
        \<and> entry M 1 (?jm1 + t) = entry M 1 ?jm1 + t"
      using wnx_run_entries[OF MR j0L nadm tle] jm1A by simp
  qed
  have cf: "entry M 1 ?jm1 \<le> entry M 0 ?jm1"
    by (rule m_6_6_reduced_coeff[OF MR]) (use jm1lt j0L in linarith)
  have eR: "\<And>t. t < d + 1 \<Longrightarrow> entry ?R 0 t = u + t \<and> entry ?R 1 t = u + t"
  proof -
    fix t assume td: "t < d + 1"
    have tR: "t < Lng ?R" using td LRd by simp
    have tS: "t < Lng ?S" using td LSd by simp
    have eS0: "entry ?S 0 t = entry M 0 (?jm1 + t)"
      and eS1: "entry ?S 1 t = entry M 1 (?jm1 + t)"
      by (rule entry_seg[OF tS])+
    have run: "entry M 0 (?jm1 + t) = entry M 0 ?jm1 + t
             \<and> entry M 1 (?jm1 + t) = entry M 1 ?jm1 + t"
      using runE td by simp
    have f1: "entry ?S 1 t = entry ?R 1 t"
      using segIF entry_funpow_IncrFirst1[OF tR, of ?k] by simp
    have f0: "entry ?S 0 t = entry ?R 0 t + ?k"
      using segIF entry_funpow_IncrFirst0[OF tR, of ?k] by simp
    have "entry ?R 1 t = entry M 1 ?jm1 + t" using f1 eS1 run by simp
    moreover have "entry ?R 0 t = entry M 1 ?jm1 + t"
    proof -
      have "entry ?R 0 t + ?k = entry M 0 ?jm1 + t" using f0 eS0 run by simp
      thus ?thesis using cf by linarith
    qed
    ultimately show "entry ?R 0 t = u + t \<and> entry ?R 1 t = u + t"
      using u_def by simp
  qed
  \<comment> \<open>\<open>?R\<close> is literally the diagonal\<close>
  have Rdiag: "?R = diagSeq u (u + d)"
  proof (rule nth_equalityI)
    show "length ?R = length (diagSeq u (u + d))"
      using LRd by (simp add: diagSeq_def)
  next
    fix t assume "t < length ?R"
    hence td: "t < d + 1" using LRd by simp
    have upt: "[u..<Suc (u + d)] ! t = u + t" by (rule nth_upt) (use td in linarith)
    have lupt: "t < length [u..<Suc (u + d)]" using td by simp
    have dnth: "diagSeq u (u + d) ! t = (u + t, u + t)"
      unfolding diagSeq_def using nth_map[OF lupt] upt by simp
    have e0: "entry ?R 0 t = u + t" and e1: "entry ?R 1 t = u + t"
      using eR[OF td] by simp_all
    have "fst (?R ! t) = u + t" using e0 by (simp add: entry_def)
    moreover have "snd (?R ! t) = u + t" using e1 by (simp add: entry_def)
    ultimately show "?R ! t = diagSeq u (u + d) ! t"
      using dnth by (metis prod.collapse)
  qed
  have TransR: "Trans ?R = Dpt (enat u) (Dpt (enat (u + d)) 0\<^sub>B)"
  proof -
    have "Trans ?R = Trans (diagSeq u (u + d))"
      by (rule arg_cong[where f = Trans, OF Rdiag])
    also have "\<dots> = Dpt (enat u) (Dpt (enat (u + d)) 0\<^sub>B)"
      by (rule m_8_1_diagSeq_Trans) (use dpos in linarith)
    finally show ?thesis .
  qed
  have TransS: "Trans ?S = Trans ?R"
    by (rule Trans_slice_eq_Red[OF MR ablt bLe leab])
  \<comment> \<open>read back \<open>c\<^sub>1\<close> and \<open>t\<^sub>2\<close>\<close>
  have ud: "u + d = entry M 1 ?j0"
  proof -
    have "entry M 1 (?jm1 + d) = entry M 1 ?jm1 + d" using runE[of d] by simp
    thus ?thesis using jm1d u_def by simp
  qed
  have c1eq: "transC1 M = Trans ?S"
    using repr segP by (simp add: transC1_def)
  show c1: "transC1 M = Dpt (enat (entry M 1 (transJm1 M)))
                        (Dpt (enat (entry M 1 (transJ0 M))) 0\<^sub>B)"
    using c1eq TransS TransR ud u_def by simp
  show "transT2 M = Dpt (enat (entry M 1 (transJ0 M))) 0\<^sub>B"
    using c1 by (simp add: transT2_def)
qed

subsection \<open>Brick C: the surgery site is an un-insertion, in EVERY branch\<close>

lemma od4_concat_sing: "concat (map (\<lambda>p. [p]) xs) = xs"
  by (induction xs) auto

text \<open>\<open>od4_R (transT2 M) (bpHeadT (transC2 M))\<close> across the \<open>transC2\<close> branch
  structure: (I)/(III)/(V) and the two else-branches APPEND one principal at the
  top or one spine level down (\<open>od4_R_drop\<close>/\<open>od4_R_deep\<close>); condition (VI)
  REPLACES the body, with \<open>t\<^sub>2 = 0\<close> (adm, @{thm [source] c6gx_condVI_transC1_adm})
  or \<open>t\<^sub>2 = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> 0 <\<^sub>B\<^sub>P D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close> (nadm, Brick C0) --- \<open>od4_R_drop\<close>/\<open>od4_R_triv\<close>.\<close>

lemma od4_site_c2:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and j1gt: "1 < Lng M - 1" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "od4_R (transT2 M) (bpHeadT (transC2 M))"
proof -
  let ?e = "entry M 1 (transJ1 M)"
  let ?ejp = "entry M 1 (transJ0 M)"
  consider (A) "transCondI M \<or> transCondIII M \<or> transCondV M"
    | (B) "transCondVI M"
    | (CD) "\<not> transCondI M \<and> \<not> transCondIII M \<and> \<not> transCondV M \<and> \<not> transCondVI M"
    by blast
  then show ?thesis
  proof cases
    case A
    have c2: "transC2 M = Dpt (transV M) (transT2 M +\<^sub>B Dpt (enat ?e) 0\<^sub>B)"
      using A by (simp add: transC2_def Let_def)
    obtain ts where t2e: "transT2 M = Trm ts" by (cases "transT2 M")
    have body: "bpHeadT (transC2 M) = Trm (ts @ [DB (enat ?e) 0\<^sub>B])"
      using c2 t2e by simp
    show ?thesis
      using od4_R.od4_R_drop[of ts "DB (enat ?e) 0\<^sub>B"] t2e body by simp
  next
    case B
    have j1acc: "entry M 1 (Lng M - 1) = ?e" by (simp add: transJ1_def)
    have body: "bpHeadT (transC2 M) = Dpt (enat ?e) 0\<^sub>B"
      using c6gx_condVI_transC2[OF B] j1acc by simp
    show ?thesis
    proof (cases "adm M (transJ0 M)")
      case True
      have t2z: "transT2 M = 0\<^sub>B"
        using c6gx_condVI_transC1_adm(1)[OF MR MP B j1gt True]
        by (simp add: transT2_def)
      show ?thesis
        using od4_R.od4_R_drop[of "[]" "DB (enat ?e) 0\<^sub>B"] t2z body by simp
    next
      case False
      have t2s: "transT2 M = Dpt (enat ?ejp) 0\<^sub>B"
        by (rule od4_condVI_nadm_c1(2)[OF MR MP B j1gt False])
      have lt: "?ejp < ?e"
        using c6gx_condVI_j0(2)[OF B] by (simp add: transJ1_def)
      have lp: "lessBP (DB (enat ?ejp) 0\<^sub>B) (DB (enat ?e) 0\<^sub>B)" using lt by simp
      show ?thesis
        using od4_R.od4_R_triv[OF lp, of "[]"] t2s body by simp
    qed
  next
    case CD
    show ?thesis
    proof (cases "transT2 M = 0\<^sub>B")
      case t2z: True
      have c2: "transC2 M = Dpt (transV M) (Dpt (enat ?ejp) (Dpt (enat ?e) 0\<^sub>B))"
        using CD t2z by (simp add: transC2_def Let_def)
      have body: "bpHeadT (transC2 M) = Dpt (enat ?ejp) (Dpt (enat ?e) 0\<^sub>B)"
        using c2 by simp
      show ?thesis
        using od4_R.od4_R_drop[of "[]" "DB (enat ?ejp) (Dpt (enat ?e) 0\<^sub>B)"] t2z body
        by simp
    next
      case t2n: False
      let ?J1 = "Lng (PB (transT2 M)) - 1"
      let ?pj = "PB (transT2 M) ! ?J1"
      have c2: "transC2 M = Dpt (transV M)
          ((if bpHeadV ?pj = enat ?ejp
            then SigmaB (take ?J1 (PB (transT2 M))) else transT2 M)
           +\<^sub>B Dpt (enat ?ejp)
                ((if bpHeadV ?pj = enat ?ejp then bpHeadT ?pj else transT2 M)
                 +\<^sub>B Dpt (enat ?e) 0\<^sub>B))"
        using CD t2n by (simp add: transC2_def Let_def)
      obtain qs where t2e: "transT2 M = Trm qs" by (cases "transT2 M")
      have qsne: "qs \<noteq> []" using t2n t2e by simp
      have lenpos: "0 < length qs" using qsne by (cases qs) auto
      have PBe: "PB (transT2 M) = map (\<lambda>p. Trm [p]) qs"
        using t2e by (simp add: PB_def)
      have LPB: "Lng (PB (transT2 M))  = length qs" using PBe by simp
      have idx: "length qs - 1 < length qs" using lenpos by simp
      have pje: "?pj = Trm [qs ! (length qs - 1)]"
        using PBe LPB nth_map[OF idx] by simp
      have pjlast: "?pj = Trm [last qs]"
        using pje last_conv_nth[OF qsne] by simp
      show ?thesis
      proof (cases "bpHeadV ?pj = enat ?ejp")
        case ldj: False
        have body: "bpHeadT (transC2 M)
            = Trm (qs @ [DB (enat ?ejp) (transT2 M +\<^sub>B Dpt (enat ?e) 0\<^sub>B)])"
          using c2 ldj t2e by simp
        show ?thesis
          using od4_R.od4_R_drop[of qs
                  "DB (enat ?ejp) (transT2 M +\<^sub>B Dpt (enat ?e) 0\<^sub>B)"] t2e body
          by simp
      next
        case ldj: True
        obtain uu bb where lqs: "last qs = DB uu bb" by (cases "last qs")
        have uue: "uu = enat ?ejp" using ldj pjlast lqs by simp
        have t4e: "bpHeadT ?pj = bb" using pjlast lqs by simp
        have t3e: "SigmaB (take ?J1 (PB (transT2 M))) = Trm (butlast qs)"
        proof -
          have "take ?J1 (PB (transT2 M)) = map (\<lambda>p. Trm [p]) (take (length qs - 1) qs)"
            using PBe LPB by (simp add: take_map)
          also have "take (length qs - 1) qs = butlast qs"
            by (simp add: butlast_conv_take)
          finally show ?thesis
            by (simp add: SigmaB_def od4_concat_sing o_def)
        qed
        have body: "bpHeadT (transC2 M)
            = Trm (butlast qs @ [DB (enat ?ejp) (bb +\<^sub>B Dpt (enat ?e) 0\<^sub>B)])"
          using c2 ldj t3e t4e by simp
        have t2split: "transT2 M = Trm (butlast qs @ [DB (enat ?ejp) bb])"
          using t2e append_butlast_last_id[OF qsne] lqs uue by (metis)
        obtain bs where bbe: "bb = Trm bs" by (cases bb)
        have inner: "od4_R bb (bb +\<^sub>B Dpt (enat ?e) 0\<^sub>B)"
          using od4_R.od4_R_drop[of bs "DB (enat ?e) 0\<^sub>B"] bbe by simp
        show ?thesis
          using od4_R.od4_R_deep[OF inner, of "butlast qs" "enat ?ejp"]
                t2split body by simp
      qed
    qed
  qed
qed

subsection \<open>Brick D: MASTER --- \<open>Trans (Pred M)\<close> is an un-insertion of \<open>Trans M\<close>\<close>

text \<open>@{thm [source] trans_surgery_localized} gives the SHARED wrappers
  \<open>(s\<^sub>1, b\<^sub>1)\<close> around the aligned cores \<open>D\<^sub>v t\<^sub>2\<close> (Pred side) and \<open>D\<^sub>v body\<^sub>2\<close>
  (host side); @{thm [source] od4_site_c2} relates the cores, and the Brick-B
  lift @{thm [source] od4_scbext_R} propagates through the context.\<close>

lemma od4_master_R:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and j1gt: "1 < Lng M - 1" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "od4_R (Trans (Pred M)) (Trans M)"
proof -
  have J1pos: "transJ1 M > 0" using j1gt by (simp add: transJ1_def)
  obtain s1 b1 body2 where
    S1: "scb_decomp (Trans (Pred M)) s1 (flatBT (Dpt (transV M) (transT2 M))) b1"
    and bRP: "\<forall>x \<in> set b1. x = RP"
    and TM: "Trans M = unflatBT (s1 @ flatBT (Dpt (transV M) body2) @ b1)"
    and c2eq: "transC2 M = Dpt (transV M) body2"
    using trans_surgery_localized[OF MR MP J1pos T1] by blast
  have fTP: "flatBT (Trans (Pred M)) = s1 @ flatBP (DB (transV M) (transT2 M)) @ b1"
    using S1 by (simp add: scb_decomp_def)
  have ipt: "isPTB_str (flatBT (transC2 M))"
    by (rule m_8_5_isPTB_str_transC2_std[OF MR MP J1pos T1])
  have ipt': "isPTB_str (flatBT (Trm [DB (transV M) body2]))"
    using ipt c2eq by simp
  obtain tX where fX: "flatBT tX = s1 @ flatBT (Trm [DB (transV M) body2]) @ b1"
    using scb_replace_principal[OF S1 ipt'] by blast
  have TMX: "Trans M = tX"
  proof -
    have "Trans M = unflatBT (flatBT tX)" using TM fX by simp
    thus ?thesis using unflatBT_flat[of tX] by simp
  qed
  have fTM: "flatBT (Trans M) = s1 @ flatBP (DB (transV M) body2) @ b1"
    using TMX fX by simp
  have body2h: "body2 = bpHeadT (transC2 M)" using c2eq by simp
  have site: "od4_R (transT2 M) body2"
    using od4_site_c2[OF MR MP j1gt T1] body2h by simp
  show ?thesis by (rule od4_scbext_R[OF fTP fTM bRP site])
qed

subsection \<open>Brick E: the mono \<open>OTpred\<close> step --- NO branch/condition hypotheses\<close>

text \<open>For ANY mono standard host: \<open>Trans (Pred M) \<in> OT\<^bsub>B\<^esub>\<close> from
  \<open>Trans M \<in> OT\<^bsub>B\<^esub>\<close>.  \<open>Trans (Pred M) = 0\<close> and \<open>Lng M = 2\<close> are free corners;
  otherwise the master un-insertion plus the Brick-A backwards \<open>isOT\<close>
  preservation @{thm [source] od4_R_OT_B} close the step.  STRICTLY STRONGER
  than both residuals \<open>DEEPOT\<close> and \<open>NOBR\<close> (empirically exact: 0 failures on
  all 1204 reduced mono hosts of the step-0 sweep).\<close>

lemma od4_OTpred_mono:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS" and mono: "monoT M" and L: "1 < Lng M"
    and hostOT: "Trans M \<in> OT_B"
  shows "Trans (Pred M) \<in> OT_B"
proof -
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have MP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predTB: "Trans (Pred M) \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF predRT])
  show ?thesis
  proof (cases "Trans (Pred M) = 0\<^sub>B")
    case True
    thus ?thesis using otx_OT_B_zero by simp
  next
    case T1ne: False
    show ?thesis
    proof (cases "Lng M = 2")
      case L2: True
      have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
      have LP1: "Lng (Pred M) = 1" using L2 by (simp add: Pred_def)
      obtain v where pv: "Pred M = [(v, v)]"
        using m_6_6_oneColumn[OF predT] predRT LP1 by auto
      have tv: "Trans (Pred M) = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using pv Trans_singleton by simp
      show ?thesis
        using tv otx_OT_B_zero m_8_7_OT_ex1[of v] by (cases "v = 0") simp_all
    next
      case False
      have j1gt: "1 < Lng M - 1" using L False by linarith
      have T1: "transT1 M \<noteq> 0\<^sub>B" using T1ne by (simp add: transT1_def)
      have R: "od4_R (Trans (Pred M)) (Trans M)"
        by (rule od4_master_R[OF MR MP j1gt T1])
      show ?thesis by (rule od4_R_OT_B[OF R hostOT predTB])
    qed
  qed
qed

subsection \<open>Brick F: \<open>DEEPOT\<close> and \<open>NOBR\<close> CLOSED; the \<open>OTpred\<close> slot residual-free\<close>

text \<open>The two named r53 residuals, verbatim as consumed by
  @{thm [source] opx_OTpred_of_residuals}.  Both are instances of the
  hypothesis-free mono step @{thm [source] od4_OTpred_mono} (the deepened
  shape equations and the branch dichotomy are not needed).\<close>

lemma od4_DEEPOT:
  fixes K :: pairseq and x :: nat and q q' :: BT and ps :: "BP list"
  assumes KST: "K \<in> ST_PS" and mono: "monoT K" and br: "Br K \<noteq> []"
    and j1gt: "1 < Lng K - 1" and hostOT: "Trans K \<in> OT_B"
    and hW: "Trans K = Dpt (enat (entry K 1 0)) (Trm ps +\<^sub>B Dpt (enat x) q)"
    and pW: "Trans (Pred K) = Dpt (enat (entry K 1 0)) (Trm ps +\<^sub>B Dpt (enat x) q')"
  shows "Trans (Pred K) \<in> OT_B"
proof -
  have L: "1 < Lng K" using j1gt by linarith
  show ?thesis by (rule od4_OTpred_mono[OF KST mono L hostOT])
qed

lemma od4_NOBR:
  fixes K :: pairseq
  assumes KST: "K \<in> ST_PS" and mono: "monoT K" and br: "Br K = []"
    and j1gt: "1 < Lng K - 1" and hostOT: "Trans K \<in> OT_B"
  shows "Trans (Pred K) \<in> OT_B"
proof -
  have L: "1 < Lng K" using j1gt by linarith
  show ?thesis by (rule od4_OTpred_mono[OF KST mono L hostOT])
qed

text \<open>\<^bold>\<open>The \<open>OTpred\<close> slot, with NO residual\<close> --- in the STRONG form (none of the
  census slot's three corner exclusions are needed).\<close>

theorem od4_OTpred_final:
  fixes N :: pairseq
  assumes NST: "N \<in> ST_PS" and hostOT: "Trans N \<in> OT_B" and L: "1 < Lng N"
  shows "Trans (Pred N) \<in> OT_B"
  by (rule opx_OTpred_of_residuals[OF od4_DEEPOT od4_NOBR NST hostOT L])

text \<open>\<^bold>\<open>CENSUS v4 (r55).\<close>  The \<open>OTpred\<close> residuals \<open>DEEPOT\<close> and \<open>NOBR\<close> are GONE:
  both termination pillars now rest on \<open>{OTint, TVall, ordIntC}\<close> alone
  (fold of @{thm [source] opx_termination_census_v3}).  Relative to the r53
  \<open>otx3\<close> ledger, the \<open>OTint\<close> slot is itself already reduced past condition (V)
  (@{thm [source] otx3_OTint_slot}), so the residue in FINEST terms is
  \<open>{otIII, otIV, PredNp, Lpv, L1v, TVall, ordIntC}\<close> plus the [Buc1] 2.2
  well-foundedness core (\<open>wfc_\<close> collapse residual).\<close>

text \<open>\<open>od4_termination_census_v4\<close> is stated AFTER the \<open>oi5_\<close> regime block: under
  the corrected Buchholz fundamental sequence the census carries an \<open>LbaseU\<close> slot,
  which is discharged unconditionally by @{text oi5_LbaseU} (r72).\<close>

(* ===== end r55-od4 part 2 (OTpred CLOSED: DEEPOT + NOBR discharged) ===== *)



(* ===================================================================== *)
(* ===== r55-OI5 (oi5_ prefix): the LAST OTint residuals otIII/otIV. ===== *)
(* ===== Route: the condIII/IV exchange value forms (cpx_condIII_    ===== *)
(* ===== mnform, branch = III or IV with ltJ) exhibit Trans(M[Suc k])===== *)
(* ===== as the d4vx_core tower over base A0 = bpHeadT(Trans(Pred N))===== *)
(* ===== in the shared kind-1 wrapper; the operB fundamental         ===== *)
(* ===== sequence (d13x_fseq_condIII) is the SAME tower over base    ===== *)
(* ===== D_ub 0.  KEY COLLAPSE (r55): peeling the shared context     ===== *)
(* ===== k-1 tower blocks deep, the proven transport otx3_transport  ===== *)
(* ===== applies with the FIXED core triple (X1, A1, X2) for EVERY   ===== *)
(* ===== k >= 1 (head e3 at k = 1, head ub at k >= 2) -- no tower    ===== *)
(* ===== induction for newOT/setle is needed, only the one-block     ===== *)
(* ===== facts OTA1 (isOT_BP (DB e3 A1), transported to ub by        ===== *)
(* ===== G-antitonicity since e3 <= ub) and SETLE1.  STEP-0          ===== *)
(* ===== (python/_r55_oi5_step0.py): ord/newOT/setle/loOT/hiOT ALL   ===== *)
(* ===== pass on genuine condIII hosts incl. block depth r = 2..4    ===== *)
(* ===== (48 deep (host,k) setle passes, 153 nontrivial); no-parent  ===== *)
(* ===== legs (N[m] = Pred N, numBT-0 readback, Pred-OT) 0 failures. ===== *)
(* ===================================================================== *)

section \<open>r55-OI5 --- \<open>otIII\<close>/\<open>otIV\<close>: shared exchange package and \<open>T\<^bsub>B\<^esub>\<close> bricks\<close>

subsection \<open>List and \<open>T\<^bsub>B\<^esub>\<close> helpers\<close>

lemma oi5_set_crep: "set (concat (replicate n xs)) \<subseteq> set xs"
  by (induction n) auto

lemma oi5_crep_RP:
  assumes "\<forall>x \<in> set xs. x = RP"
  shows "\<forall>x \<in> set (concat (replicate n xs)). x = RP"
  using assms by (induction n) auto

text \<open>\<open>d4vx_ins\<close> stays in \<open>T\<^bsub>B\<^esub>\<close>: the flat string of the insertion consists of
  letters of the (dfree) host wrap and of the (dfree) plugged core, so
  @{thm [source] dfree_flat_BT} reads \<open>T\<^bsub>B\<^esub>\<close>-membership straight off the string.\<close>

lemma oi5_d4vx_ins_TB:
  assumes wrap: "flatBT W = s0 @ flatBP (DB (enat v) h) @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and WTB: "W \<in> T_B" and XTB: "X \<in> T_B"
  shows "d4vx_ins s0 ub b0 X \<in> T_B"
proof -
  have fI: "flatBT (d4vx_ins s0 ub b0 X) = s0 @ Dsym (enat ub) # flatBT X @ b0"
    by (rule d4vx_ins_flat[OF wrap b0RP])
  have Wdf: "dfree_BT W" using WTB by (simp add: T_B_def)
  have Xdf: "dfree_BT X" using XTB by (simp add: T_B_def)
  have noW: "\<And>u. Dsym u \<in> set (flatBT W) \<Longrightarrow> u \<noteq> \<infinity>"
    using Wdf[unfolded dfree_flat_BT] by blast
  have noX: "\<And>u. Dsym u \<in> set (flatBT X) \<Longrightarrow> u \<noteq> \<infinity>"
    using Xdf[unfolded dfree_flat_BT] by blast
  have s0sub: "set s0 \<subseteq> set (flatBT W)" and b0sub: "set b0 \<subseteq> set (flatBT W)"
    using wrap by auto
  have "\<And>u. Dsym u \<in> set (flatBT (d4vx_ins s0 ub b0 X)) \<Longrightarrow> u \<noteq> \<infinity>"
  proof -
    fix u assume "Dsym u \<in> set (flatBT (d4vx_ins s0 ub b0 X))"
    hence "Dsym u \<in> set s0 \<union> {Dsym (enat ub)} \<union> set (flatBT X) \<union> set b0"
      using fI by (simp only: set_append) auto
    thus "u \<noteq> \<infinity>" using noW noX s0sub b0sub by auto
  qed
  hence "dfree_BT (d4vx_ins s0 ub b0 X)"
    unfolding dfree_flat_BT by blast
  thus ?thesis by (simp add: T_B_def)
qed

lemma oi5_d4vx_core_TB:
  assumes wrap: "flatBT W = s0 @ flatBP (DB (enat v) h) @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and WTB: "W \<in> T_B" and tTB: "t \<in> T_B"
  shows "d4vx_core s0 ub b0 t k \<in> T_B"
  by (induction k) (auto simp: tTB intro: oi5_d4vx_ins_TB[OF wrap b0RP WTB])

subsection \<open>r72: \<open>base\<^sub>1\<close>, re-seeded to \<open>0\<^sub>B\<close> (the corrected operB tower seed)\<close>

text \<open>\<^bold>\<open>\<open>base\<^sub>1\<^sup>Y\<close>: \<open>A\<^sub>0 < d4vx_ins s\<^sub>0 ub b\<^sub>0 0\<^sub>B\<close>.\<close>  Under the CORRECTED
  Buchholz rule the operB core tower is seeded at \<open>0\<^sub>B\<close>, so the census \<open>base\<^sub>1\<close> must
  bound \<open>A\<^sub>0\<close> by \<open>Y\<^sub>1 = ins 0\<^sub>B\<close> rather than by \<open>X\<^sub>1 = ins (D\<^bsub>ub\<^esub>0)\<close>.  This is
  @{thm [source] crx_base1_of_nest} / @{thm [source] cnv_base1_of_nest} with the
  inserted core replaced by \<open>0\<^sub>B\<close>: the surgery term seen ONE level up is then
  \<open>c' = D\<^bsub>ub\<^esub>0\<close> instead of \<open>D\<^bsub>ub\<^esub>(D\<^bsub>ub\<^esub>0)\<close>, and the comparison is decided by the SAME
  shared-wrapper growth step \<open>D\<^bsub>tv\<^esub>t\<^sub>2 < D\<^bsub>tv\<^esub>(t\<^sub>2 + c')\<close>, which needs only that \<open>c'\<close> is a
  nonempty principal --- NOT what sits inside it.  (Empirically: 363/363 real
  condIII/IV hosts, python/_r72_reseed_step0b.py.)\<close>

lemma oy1_base1Y_condIII:
  fixes M :: pairseq and u1 v1w u2 v2 s0 b0 :: "Sym list"
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and cIII: "transCondIII M"
    and dP: "scb_decomp (Trans (Pred (s84x_N M)))
               (Dsym (enat (entry M 1 (s84x_jm3 M))) # u1)
               (flatBT (transC1 M)) v1w"
    and d2: "scb_decomp (Trans (s84x_N M))
               (Dsym (enat (entry M 1 (s84x_jm3 M))) # u1)
               (flatBT (transC2 M)) v1w"
    and d4c2: "scb_decomp (transC2 M) u2
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) v2"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N M))) s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
  shows "lessBT (bpHeadT (Trans (Pred (s84x_N M))))
           (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0 0\<^sub>B)"
proof -
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?c = "Dpt (enat ?v1) 0\<^sub>B"
  let ?c' = "Dpt (enat ?ub) 0\<^sub>B"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N M)))"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  have c1sh: "transC1 M = Dpt (transV M) (transT2 M)"
    using m_8_5_scbdec_c1_shape(1,2)[OF MR MP J1pos T1] by simp
  have c2sh: "transC2 M = Dpt (transV M) (transT2 M +\<^sub>B ?c)"
    by (rule crx_c2_shape_condIII[OF cIII])
  have t2TB: "transT2 M \<in> T_B" by (rule m_8_5_scbdec_c1_shape(3)[OF MR MP J1pos T1])
  have cTB: "?c \<in> T_B" by (simp add: T_B_def)
  have cp: "\<exists>p. ?c = Trm [p]" by auto
  have c'TB: "?c' \<in> T_B" by (simp add: T_B_def)
  have c'p: "\<exists>p. ?c' = Trm [p]" by auto
  obtain w4 w4' where d4: "scb_decomp (transT2 M +\<^sub>B ?c) w4 (flatBT ?c) w4'"
    using m_7_2_add_scb_conj1[OF t2TB cTB cp] unfolding MarkedB_def by auto
  have d4': "scb_decomp (transT2 M +\<^sub>B ?c') w4 (flatBT ?c') w4'"
    by (rule m_7_2_add_scb_conj2[OF t2TB cTB cp c'TB c'p d4])
  have iptc: "isPTB_str (flatBT ?c)" by (rule isPTB_str_Dpt) simp_all
  have d5: "scb_decomp (Dpt (transV M) (transT2 M +\<^sub>B ?c))
              (Dsym (transV M) # w4) (flatBT ?c) w4'"
    by (rule scb_Dpt_lift[OF d4 iptc])
  have d5c2: "scb_decomp (transC2 M) (Dsym (transV M) # w4) (flatBT ?c) w4'"
    using d5 c2sh by simp
  have c2ne: "transC2 M \<noteq> Trm []" using c2sh by simp
  have pin2: "u2 = Dsym (transV M) # w4 \<and> v2 = w4'"
    by (rule m_7_2_scb_unique_sb[OF d4c2 d5c2 c2ne])
  have fTN: "flatBT (Trans (s84x_N M))
           = Dsym (enat ?e3) # u1 @ flatBT (transC2 M) @ v1w"
    using d2 by (simp add: scb_decomp_def)
  have fbody: "flatBT ?body = u1 @ flatBT (transC2 M) @ v1w"
    by (rule vf2x_flat_head_bpHeadT[OF fTN])
  have fc2: "flatBT (transC2 M) = u2 @ flatBT ?c @ v2"
    using d4c2 by (simp add: scb_decomp_def)
  have v1RP: "\<forall>x \<in> set v1w. x = RP" using d2 by (simp add: scb_decomp_def)
  have v2RP: "\<forall>x \<in> set v2. x = RP" using d4c2 by (simp add: scb_decomp_def)
  have b0RP': "\<forall>x \<in> set (v2 @ v1w). x = RP" using v1RP v2RP by auto
  have fbody2: "flatBT ?body = (u1 @ u2) @ flatBT ?c @ (v2 @ v1w)"
    using fbody fc2 by simp
  have innerC: "scb_decomp ?body (u1 @ u2) (flatBT ?c) (v2 @ v1w)"
    unfolding scb_decomp_def using fbody2 iptc b0RP' by simp
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "[Zsym] = u1 @ flatBT (transC2 M) @ v1w" using fbody z by simp
    hence "[Zsym] = u1 @ (Dsym (transV M)
             # flatBT (transT2 M +\<^sub>B ?c)) @ v1w" using c2sh by simp
    thus False by (cases u1) auto
  qed
  have pin0: "s0 = u1 @ u2 \<and> b0 = v2 @ v1w"
    by (rule m_7_2_scb_unique_sb[OF inner innerC bodyne])
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using fbody2 pin0 by simp
  have b0RP: "\<forall>x \<in> set b0. x = RP" using pin0 b0RP' by simp
  have fins: "flatBT (d4vx_ins s0 ?ub b0 0\<^sub>B)
            = s0 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ b0"
    by (rule d4vx_ins_flat[OF wrap b0RP])
  have ft2c': "flatBT (transT2 M +\<^sub>B ?c') = w4 @ flatBT ?c' @ w4'"
    using d4' by (simp add: scb_decomp_def)
  have fins2: "flatBT (d4vx_ins s0 ?ub b0 0\<^sub>B)
      = u1 @ flatBP (DB (transV M) (transT2 M +\<^sub>B ?c')) @ v1w"
  proof -
    have "s0 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ b0
        = u1 @ (u2 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ v2) @ v1w"
      using pin0 by simp
    also have "u2 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ v2
             = Dsym (transV M) # (w4 @ flatBT ?c' @ w4')"
      using pin2 by simp
    also have "\<dots> = flatBP (DB (transV M) (transT2 M +\<^sub>B ?c'))"
      using ft2c' by simp
    finally show ?thesis using fins by simp
  qed
  have fPN: "flatBT (Trans (Pred (s84x_N M)))
           = Dsym (enat ?e3) # u1 @ flatBT (transC1 M) @ v1w"
    using dP by (simp add: scb_decomp_def)
  have fA0: "flatBT ?A0 = u1 @ flatBT (transC1 M) @ v1w"
    by (rule vf2x_flat_head_bpHeadT[OF fPN])
  have fA0': "flatBT ?A0 = u1 @ flatBP (DB (transV M) (transT2 M)) @ v1w"
    using fA0 c1sh by simp
  have grow: "lessBT (transT2 M) (transT2 M +\<^sub>B ?c')"
    using c4dx_lessBT_grow[of "transT2 M" "DB (enat ?ub) 0\<^sub>B"] by simp
  have core: "lessBP (DB (transV M) (transT2 M))
                     (DB (transV M) (transT2 M +\<^sub>B ?c'))"
    using grow by simp
  show ?thesis by (rule scbext_lessBT[OF fA0' fins2 v1RP core])
qed

lemma oy1_base1Y_condIV:
  fixes M :: pairseq and u1 v1w u2 v2 s0 b0 :: "Sym list"
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and cIV: "transCondIV M"
    and dP: "scb_decomp (Trans (Pred (s84x_N M)))
               (Dsym (enat (entry M 1 (s84x_jm3 M))) # u1)
               (flatBT (transC1 M)) v1w"
    and d2: "scb_decomp (Trans (s84x_N M))
               (Dsym (enat (entry M 1 (s84x_jm3 M))) # u1)
               (flatBT (transC2 M)) v1w"
    and d4c2: "scb_decomp (transC2 M) u2
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) v2"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N M))) s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
  shows "lessBT (bpHeadT (Trans (Pred (s84x_N M))))
           (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0 0\<^sub>B)"
proof -
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?w = "enat (entry M 1 (transJ0 M))"
  let ?c = "Dpt (enat ?v1) 0\<^sub>B"
  let ?cc = "Dpt (enat ?ub) 0\<^sub>B"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N M)))"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  have c1sh: "transC1 M = Dpt (transV M) (transT2 M)"
    using m_8_5_scbdec_c1_shape(1,2)[OF MR MP J1pos T1] by simp
  obtain t3 t4 where t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B"
    and c2full: "transC2 M = Dpt (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?c))"
    and dich: "(t3 = transT2 M \<and> t4 = transT2 M)
             \<or> transT2 M = t3 +\<^sub>B Dpt ?w t4"
    using cnv_c2_shape_condIV[OF MR MP J1pos T1 cIV] by blast
  obtain sB bB where holeU: "\<forall>c'. c' \<in> T_B \<longrightarrow> (\<exists>p. c' = Trm [p]) \<longrightarrow>
      scb_decomp (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B c')) sB (flatBT c') bB"
    using cnv_nested_hole_pair[OF t4TB, of t3 ?w] by blast
  have cTB: "?c \<in> T_B" by (simp add: T_B_def)
  have cp: "\<exists>p. ?c = Trm [p]" by auto
  have ccTB: "?cc \<in> T_B" by (simp add: T_B_def)
  have ccp: "\<exists>p. ?cc = Trm [p]" by auto
  have dB: "scb_decomp (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?c)) sB (flatBT ?c) bB"
    using holeU cTB cp by blast
  have dBcc: "scb_decomp (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc)) sB (flatBT ?cc) bB"
    using holeU ccTB ccp by blast
  have iptc: "isPTB_str (flatBT ?c)" by (rule isPTB_str_Dpt) simp_all
  have dc2can0: "scb_decomp (Dpt (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?c)))
                   (Dsym (transV M) # sB) (flatBT ?c) bB"
    by (rule scb_Dpt_lift[OF dB iptc])
  have dc2can: "scb_decomp (transC2 M) (Dsym (transV M) # sB) (flatBT ?c) bB"
    using dc2can0 c2full by simp
  have c2ne: "transC2 M \<noteq> Trm []" using c2full by simp
  have pin2: "u2 = Dsym (transV M) # sB \<and> v2 = bB"
    by (rule m_7_2_scb_unique_sb[OF d4c2 dc2can c2ne])
  have fTN: "flatBT (Trans (s84x_N M))
           = Dsym (enat ?e3) # u1 @ flatBT (transC2 M) @ v1w"
    using d2 by (simp add: scb_decomp_def)
  have fbody: "flatBT ?body = u1 @ flatBT (transC2 M) @ v1w"
    by (rule vf2x_flat_head_bpHeadT[OF fTN])
  have fc2: "flatBT (transC2 M) = u2 @ flatBT ?c @ v2"
    using d4c2 by (simp add: scb_decomp_def)
  have v1RP: "\<forall>x \<in> set v1w. x = RP" using d2 by (simp add: scb_decomp_def)
  have v2RP: "\<forall>x \<in> set v2. x = RP" using d4c2 by (simp add: scb_decomp_def)
  have b0RP': "\<forall>x \<in> set (v2 @ v1w). x = RP" using v1RP v2RP by auto
  have fbody2: "flatBT ?body = (u1 @ u2) @ flatBT ?c @ (v2 @ v1w)"
    using fbody fc2 by simp
  have innerC: "scb_decomp ?body (u1 @ u2) (flatBT ?c) (v2 @ v1w)"
    unfolding scb_decomp_def using fbody2 iptc b0RP' by simp
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "[Zsym] = u1 @ flatBT (transC2 M) @ v1w" using fbody z by simp
    hence "[Zsym] = u1 @ (Dsym (transV M)
             # flatBT (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?c))) @ v1w" using c2full by simp
    thus False by (cases u1) auto
  qed
  have pin0: "s0 = u1 @ u2 \<and> b0 = v2 @ v1w"
    by (rule m_7_2_scb_unique_sb[OF inner innerC bodyne])
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using fbody2 pin0 by simp
  have b0RP: "\<forall>x \<in> set b0. x = RP" using pin0 b0RP' by simp
  have fins: "flatBT (d4vx_ins s0 ?ub b0 0\<^sub>B)
            = s0 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ b0"
    by (rule d4vx_ins_flat[OF wrap b0RP])
  have fBcc: "flatBT (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc)) = sB @ flatBT ?cc @ bB"
    using dBcc by (simp add: scb_decomp_def)
  have fins2: "flatBT (d4vx_ins s0 ?ub b0 0\<^sub>B)
      = u1 @ flatBP (DB (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc))) @ v1w"
  proof -
    have "s0 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ b0
        = u1 @ (u2 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ v2) @ v1w"
      using pin0 by simp
    also have "u2 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ v2
             = Dsym (transV M) # (sB @ flatBT ?cc @ bB)"
      using pin2 by simp
    also have "\<dots> = flatBP (DB (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc)))"
      using fBcc by simp
    finally show ?thesis using fins by simp
  qed
  have fPN: "flatBT (Trans (Pred (s84x_N M)))
           = Dsym (enat ?e3) # u1 @ flatBT (transC1 M) @ v1w"
    using dP by (simp add: scb_decomp_def)
  have fA0: "flatBT ?A0 = u1 @ flatBT (transC1 M) @ v1w"
    by (rule vf2x_flat_head_bpHeadT[OF fPN])
  have fA0': "flatBT ?A0 = u1 @ flatBP (DB (transV M) (transT2 M)) @ v1w"
    using fA0 c1sh by simp
  have ccne: "?cc \<noteq> 0\<^sub>B" by simp
  have grow: "lessBT (transT2 M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc))"
    by (rule cnv_body_grow[OF dich ccne])
  have core: "lessBP (DB (transV M) (transT2 M))
                     (DB (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc)))"
    using grow by simp
  show ?thesis by (rule scbext_lessBT[OF fA0' fins2 v1RP core])
qed


subsection \<open>The shared condIII / condIV exchange package (\<open>REGS\<close>/\<open>REGSP\<close>/\<open>RUN\<close>
  discharged; interleave bases and \<open>A\<^sub>0 \<in> T\<^bsub>B\<^esub>\<close> included)\<close>

text \<open>The unconditional bundle behind both \<open>otIII\<close> and the non-admeq \<open>otIV\<close> leg:
  @{thm [source] cpx_condIII_mnform} with \<open>REGS\<close> = @{thm [source] mcx_regS},
  \<open>REGSP\<close> = @{thm [source] slx37_regSP_uncond}, \<open>RUN\<close> =
  @{thm [source] wgx37_m0run_of_e1ge} on @{thm [source] e1x_e1ge_uncond}, the
  interleave bases by @{thm [source] crx_base0_of_run} /
  @{thm [source] crx_base1_of_nest} (condIII) resp.
  @{thm [source] cnv_base0_of_run} / @{thm [source] cnv_base1_of_nest} (condIV),
  and \<open>A\<^sub>0 \<in> T\<^bsub>B\<^esub>\<close> read off the flat string via @{thm [source] dfree_flat_BT}.\<close>

lemma oi5_IIIIV_pkg:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
    and ltJ: "s84x_jm3 M < transJm1 M"
  obtains s0 b0 s1 b1 where
      "\<forall>x \<in> set b0. x = RP" and "\<forall>x \<in> set b1. x = RP"
    and "scb_decomp (bpHeadT (Trans (s84x_N M))) s0
         (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
    and "scb_kind1 (Trans M) s1
         (flatBT (Dpt (enat (entry M 1 (s84x_jm3 M)))
                      (bpHeadT (Trans (s84x_N M))))) b1"
    and "\<forall>m. 1 \<le> m \<longrightarrow>
          flatBT (Trans ((M::pairseq)[m]))
            = s1 @ Dsym (enat (entry M 1 (s84x_jm3 M)))
                # flatBT (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                           (bpHeadT (Trans (Pred (s84x_N M)))) (m - 1))
                @ b1"
    and "lessBT (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B)
              (bpHeadT (Trans (Pred (s84x_N M))))"
    and "lessBT (bpHeadT (Trans (Pred (s84x_N M))))
              (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0 0\<^sub>B)"
    and "bpHeadT (Trans (Pred (s84x_N M))) \<in> T_B"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N M)))"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "M \<in> T_PS" using MPT by (simp add: PT_PS_def)
  \<comment> \<open>\<open>REGS\<close>/\<open>REGSP\<close>/\<open>RUN\<close>, unconditional\<close>
  have REGS: "s84x_jm3 M < s84x_jm2 M \<Longrightarrow>
                cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M))"
  proof -
    assume g: "s84x_jm3 M < s84x_jm2 M"
    show "cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M))"
      by (rule mcx_regS[OF MST MPT hp j1gt branch g])
  qed
  have REGSP: "s84x_jm3 M < s84x_jm2 M \<Longrightarrow> Br (Red (Pred (s84x_N M))) \<noteq> [] \<Longrightarrow>
                 cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (Pred (s84x_N M)))"
  proof -
    assume g: "s84x_jm3 M < s84x_jm2 M" and b: "Br (Red (Pred (s84x_N M))) \<noteq> []"
    show "cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (Pred (s84x_N M)))"
      by (rule slx37_regSP_uncond[OF MST MPT hp j1gt branch g b])
  qed
  have E1GE: "entry M 1 (Lng M - 1) \<le> entry M 1 (s84x_jm2 M + 1)"
    by (rule e1x_e1ge_uncond[OF MST MPT hp j1gt])
  have RUN: "nextR M 1 (s84x_jm2 M) (s84x_jm2 M + 1)"
    using wgx37_m0run_of_e1ge[OF hp E1GE] by simp
  \<comment> \<open>the mnform package\<close>
  obtain u1 u2 v2 w1 s1 b1 where
    b0RP: "\<forall>x \<in> set (v2 @ w1). x = RP" and b1RP: "\<forall>x \<in> set b1. x = RP"
    and dPq: "scb_decomp (Trans (Pred (s84x_N M)))
                (Dsym (enat ?e3) # u1) (flatBT (transC1 M)) w1"
    and d2q: "scb_decomp (Trans (s84x_N M))
                (Dsym (enat ?e3) # u1) (flatBT (transC2 M)) w1"
    and d4c2q: "scb_decomp (transC2 M) u2
                  (flatBT (Dpt (enat ?v1) 0\<^sub>B)) v2"
    and inner: "scb_decomp ?body (u1 @ u2)
                  (flatBT (Dpt (enat ?v1) 0\<^sub>B)) (v2 @ w1)"
    and k1: "scb_kind1 (Trans M) s1
               (flatBT (Dpt (enat ?e3) ?body)) b1"
    and A0eq: "?A0 = bpHeadT (Trans (Pred (s84x_Np M)))"
    and MNall: "\<forall>m. 1 \<le> m \<longrightarrow>
        flatBT (Trans ((M::pairseq)[m]))
          = s1 @ Dsym (enat ?e3)
              # flatBT (d4vx_core (u1 @ u2) ?ub (v2 @ w1) ?A0 (m - 1))
              @ b1"
    using cpx_condIII_mnform[OF MST MPT hp j1gt branch ltJ REGS REGSP] by blast
  \<comment> \<open>regime facts\<close>
  have nVI: "\<not> transCondVI M"
  proof (cases "transCondIII M")
    case True
    thus ?thesis by (auto simp: transCondIII_def transCondVI_def)
  next
    case False
    hence cIV: "transCondIV M" using branch by blast
    show ?thesis using c4dx_condIV_excl(4)[OF cIV] .
  qed
  have J1pos: "transJ1 M > 0" using j1gt by (simp add: transJ1_def)
  have T1: "transT1 M \<noteq> 0\<^sub>B"
    using s84d_L4_regime[OF MST MPT hp nVI] by simp
  \<comment> \<open>the interleave bases, per branch\<close>
  have base0Np: "lessBT (Dpt (enat ?ub) 0\<^sub>B) (bpHeadT (Trans (Pred (s84x_Np M))))"
  proof (cases "transCondIII M")
    case True
    show ?thesis by (rule crx_base0_of_run[OF MST MPT hp j1gt True RUN])
  next
    case False
    hence cIV: "transCondIV M" using branch by blast
    show ?thesis by (rule cnv_base0_of_run[OF MST MPT hp j1gt cIV RUN])
  qed
  have base0: "lessBT (Dpt (enat ?ub) 0\<^sub>B) ?A0" using base0Np A0eq by simp
  have base1: "lessBT ?A0 (d4vx_ins (u1 @ u2) ?ub (v2 @ w1) 0\<^sub>B)"
  proof (cases "transCondIII M")
    case True
    show ?thesis
      by (rule oy1_base1Y_condIII[OF MR MPT J1pos T1 True dPq d2q d4c2q inner])
  next
    case False
    hence cIV: "transCondIV M" using branch by blast
    show ?thesis
      by (rule oy1_base1Y_condIV[OF MR MPT J1pos T1 cIV dPq d2q d4c2q inner])
  qed
  \<comment> \<open>\<open>A\<^sub>0 \<in> T\<^bsub>B\<^esub>\<close>: read off the flat string\<close>
  have jm2lt: "s84x_jm2 M < Lng M - 1" by (rule s84c1_jm2_basic(1)[OF hp])
  have jm3le: "s84x_jm3 M \<le> s84x_jm2 M"
    using adm_Adm_le by (simp add: s84x_jm3_def)
  have jm3lt: "s84x_jm3 M < Lng M - 1" using jm3le jm2lt by linarith
  have mM3: "(M, s84x_jm3 M) \<in> Marked"
    using s84d_jm3_Marked(1)[OF MR MT hp] by simp
  have leR3: "leR M 0 (s84x_jm3 M) (Lng M - 1)"
    using mM3 by (simp add: Marked_def)
  have TNRed: "Trans (seg M (s84x_jm3 M) (Lng M - 1))
             = Trans (Red (seg M (s84x_jm3 M) (Lng M - 1)))"
    by (rule Trans_slice_eq_Red[OF MR jm3lt order.refl leR3])
  have RedRT: "Red (seg M (s84x_jm3 M) (Lng M - 1)) \<in> RT_PS"
    using slice_Red_in_RT_PS[OF MR jm3lt order.refl leR3] by simp
  have TN_TB: "Trans (s84x_N M) \<in> T_B"
    using m_7_3_Trans_in_T_B[OF RedRT] TNRed by (simp add: s84x_N_def)
  have TNdf: "dfree_BT (Trans (s84x_N M))" using TN_TB by (simp add: T_B_def)
  have noTN: "\<And>u. Dsym u \<in> set (flatBT (Trans (s84x_N M))) \<Longrightarrow> u \<noteq> \<infinity>"
    using TNdf[unfolded dfree_flat_BT] by blast
  have c1sh: "transC1 M = Dpt (enat (entry M 1 (transJm1 M))) (transT2 M)"
    using m_8_5_scbdec_c1_shape(2)[OF MR MPT J1pos T1] .
  have t2TB: "transT2 M \<in> T_B"
    using m_8_5_scbdec_c1_shape(3)[OF MR MPT J1pos T1] .
  have c1df: "dfree_BT (transC1 M)"
    using c1sh t2TB by (simp add: T_B_def)
  have noc1: "\<And>u. Dsym u \<in> set (flatBT (transC1 M)) \<Longrightarrow> u \<noteq> \<infinity>"
    using c1df[unfolded dfree_flat_BT] by blast
  have fPN: "flatBT (Trans (Pred (s84x_N M)))
           = Dsym (enat ?e3) # u1 @ flatBT (transC1 M) @ w1"
    using dPq by (simp add: scb_decomp_def)
  have fA0: "flatBT ?A0 = u1 @ flatBT (transC1 M) @ w1"
    by (rule vf2x_flat_head_bpHeadT[OF fPN])
  have fTN: "flatBT (Trans (s84x_N M))
           = Dsym (enat ?e3) # u1 @ flatBT (transC2 M) @ w1"
    using d2q by (simp add: scb_decomp_def)
  have u1sub: "set u1 \<subseteq> set (flatBT (Trans (s84x_N M)))"
    and w1sub: "set w1 \<subseteq> set (flatBT (Trans (s84x_N M)))"
    using fTN by auto
  have "\<And>u. Dsym u \<in> set (flatBT ?A0) \<Longrightarrow> u \<noteq> \<infinity>"
  proof -
    fix u assume "Dsym u \<in> set (flatBT ?A0)"
    hence "Dsym u \<in> set u1 \<union> set (flatBT (transC1 M)) \<union> set w1"
      using fA0 by (simp only: set_append) auto
    thus "u \<noteq> \<infinity>" using noTN noc1 u1sub w1sub by auto
  qed
  hence A0df: "dfree_BT ?A0" unfolding dfree_flat_BT by blast
  have A0TB: "?A0 \<in> T_B" using A0df by (simp add: T_B_def)
  \<comment> \<open>assemble\<close>
  show ?thesis
    by (rule that[OF b0RP b1RP inner k1 MNall base0 base1 A0TB])
qed

subsection \<open>Regime bundle (host-only facts)\<close>

lemma oi5_regime:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
  shows "entry M 1 (s84x_jm3 M) < entry M 1 (Lng M - 1)"
    and "entry M 1 (s84x_jm3 M) \<le> entry M 1 (Lng M - 1) - 1"
    and "bpHeadT (Trans (s84x_N M)) \<in> T_B"
    and "domB (bpHeadT (Trans (s84x_N M)))
           = TBv (enat (entry M 1 (Lng M - 1) - 1))"
    and "Trans M \<in> T_B"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "M \<in> T_PS" using MPT by (simp add: PT_PS_def)
  \<comment> \<open>\<open>e\<^sub>3 \<le> M\<^bsub>1,j\<^sub>-\<^sub>2\<^esub>\<close> along the row-1 chain\<close>
  have jm2lt: "s84x_jm2 M < Lng M - 1" by (rule s84c1_jm2_basic(1)[OF hp])
  have jm2leL: "s84x_jm2 M \<le> Lng M - 1" using jm2lt by simp
  have le1chain: "leR M 1 (s84x_jm3 M) (s84x_jm2 M)"
    using adm_row1_ancestry[OF MT jm2leL] by (simp add: s84x_jm3_def)
  have ch1: "(nextrel1 M)\<^sup>*\<^sup>* (s84x_jm3 M) (s84x_jm2 M)"
    using le1chain by (simp add: leR_def le1_def)
  have e3le: "?e3 \<le> entry M 1 (s84x_jm2 M)"
    by (rule w84x_le1_entry_mono[OF ch1])
  show "?e3 < entry M 1 (Lng M - 1)"
    using e3le s84c1_jm2_basic(2)[OF hp] by linarith
  \<comment> \<open>\<open>M\<^bsub>1,j\<^sub>-\<^sub>2\<^esub> = v\<^sub>1 - 1\<close> from RedCondA at the row-1 parent edge\<close>
  have rcA: "RedCondA M" using MR m_6_6_reduced_iff_cond[OF MT] by blast
  have ubeq: "entry M 1 (s84x_jm2 M) = entry M 1 (Lng M - 1) - 1"
  proof -
    have "entry M 1 (parent M 1 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)"
      using rcA[unfolded RedCondA_def, rule_format, of 1 "Lng M - 1"] hp by simp
    thus ?thesis by (simp add: s84x_jm2_def)
  qed
  show "?e3 \<le> entry M 1 (Lng M - 1) - 1" using e3le ubeq by simp
  \<comment> \<open>\<open>body \<in> T\<^bsub>B\<^esub>\<close> via the reduced slice\<close>
  have jm3le: "s84x_jm3 M \<le> s84x_jm2 M"
    using adm_Adm_le by (simp add: s84x_jm3_def)
  have jm3lt: "s84x_jm3 M < Lng M - 1" using jm3le jm2lt by linarith
  have mM3: "(M, s84x_jm3 M) \<in> Marked"
    using s84d_jm3_Marked(1)[OF MR MT hp] by simp
  have leR3: "leR M 0 (s84x_jm3 M) (Lng M - 1)"
    using mM3 by (simp add: Marked_def)
  have TNRed: "Trans (seg M (s84x_jm3 M) (Lng M - 1))
             = Trans (Red (seg M (s84x_jm3 M) (Lng M - 1)))"
    by (rule Trans_slice_eq_Red[OF MR jm3lt order.refl leR3])
  have RedRT: "Red (seg M (s84x_jm3 M) (Lng M - 1)) \<in> RT_PS"
    using slice_Red_in_RT_PS[OF MR jm3lt order.refl leR3] by simp
  have TN_TB: "Trans (s84x_N M) \<in> T_B"
    using m_7_3_Trans_in_T_B[OF RedRT] TNRed by (simp add: s84x_N_def)
  show "bpHeadT (Trans (s84x_N M)) \<in> T_B"
    by (rule w84x_bpHeadT_TB[OF TN_TB])
  show "domB (bpHeadT (Trans (s84x_N M)))
          = TBv (enat (entry M 1 (Lng M - 1) - 1))"
    by (rule crx_dbbodyH[OF MR MPT j1gt hp])
  show "Trans M \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF MR])
qed

subsection \<open>r72: the \<open>LbaseU\<close> census slot, discharged UNCONDITIONALLY\<close>

text \<open>Under the CORRECTED Buchholz fundamental sequence
  (\<open>x\<^sub>0 = D\<^sub>u 0\<close>, \<open>x\<^bsub>j+1\<^esub> = D\<^sub>u (b[x\<^sub>j])\<close>) the census carries the slot

    \<open>LbaseU\<close> : \<open>D\<^bsub>ub\<^esub>0 \<le> d4vx_ins s\<^sub>0 ub b\<^sub>0 0\<close>   (\<open>ub = v\<^sub>1 - 1\<close>),

  the \<open>0\<^sub>B\<close>-seeded base step of the operB core tower.  It is PROVED in \<^theory>\<open>PSS_B.pss_wip\<close>
  as @{thm [source] opf_Lbase_of_domB} from \<open>dom(body) = T\<^bsub>ub\<^esub>\<close> alone --- no \<open>RightNodes\<close>
  bound and NO \<open>ltJ\<close>.  Its three inputs are exactly @{thm [source] oi5_regime}(3),(4)
  and the OT-ness of the census body, which we supply here (@{text oi5_bodyOT}) for
  BOTH regimes: \<open>ltJ\<close> (via the package's kind-1 anchor) and the condIV \<open>admeq\<close> corner
  \<open>j\<^sub>-\<^sub>3 = j\<^sub>-\<^sub>1\<close> (via @{thm [source] c4dx_condIV_k1}, which is \<open>ltJ\<close>-free).\<close>

text \<open>The regime dichotomy: on a condIII/IV \<open>hasParent\<close> host, either \<open>ltJ\<close> holds or
  we are at the condIV \<open>admeq\<close> corner.  \<open>j\<^sub>-\<^sub>3 = Adm(j\<^sub>-\<^sub>2) \<le> Adm(j\<^sub>0) = j\<^sub>-\<^sub>1\<close> by
  admissibilization-maximality (@{thm [source] adm_Adm_max}) since \<open>j\<^sub>-\<^sub>2 < j\<^sub>0\<close>
  (@{thm [source] m_8_4_oper_props_1}); and under (III) \<open>j\<^sub>-\<^sub>1 = j\<^sub>0\<close>, which forces the
  strict case.  So the equality corner is condIV-only.\<close>

lemma oi5_ltJ_or_IVadmeq:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
  shows "s84x_jm3 M < transJm1 M
       \<or> (transCondIV M \<and> Adm M (s84x_jm2 M) = transJm1 M)"
proof -
  have jm2ltj0: "s84x_jm2 M < transJ0 M"
    by (rule m_8_4_oper_props_1(1)[OF MST MPT hp j1gt branch])
  have jm3le: "s84x_jm3 M \<le> s84x_jm2 M"
    using adm_Adm_le by (simp add: s84x_jm3_def)
  have admjm3: "adm M (s84x_jm3 M)"
    using adm_Adm_adm by (simp add: s84x_jm3_def)
  have jm3lej0: "s84x_jm3 M \<le> transJ0 M" using jm3le jm2ltj0 by linarith
  have le: "s84x_jm3 M \<le> transJm1 M"
    using adm_Adm_max[OF admjm3 jm3lej0] by (simp add: transJm1_def)
  show ?thesis
  proof (cases "s84x_jm3 M < transJm1 M")
    case True
    thus ?thesis by blast
  next
    case False
    hence eq: "s84x_jm3 M = transJm1 M" using le by linarith
    have cIV: "transCondIV M"
    proof (cases "transCondIII M")
      case True
      have jm1eq: "transJm1 M = transJ0 M"
        using True
        by (simp add: transJm1_def transJ0_def transJ1_def transCondIII_def Adm_def)
      have False using eq jm1eq jm3le jm2ltj0 by linarith
      thus ?thesis by simp
    next
      case False
      thus ?thesis using branch by blast
    qed
    show ?thesis using cIV eq by (simp add: s84x_jm3_def)
  qed
qed

text \<open>\<^bold>\<open>The census body is in \<open>OT\<close>.\<close>  \<open>body = bpHeadT (Trans (s84x_N M))\<close> sits at the
  kind-1 scb position of \<open>Trans M\<close> as the body of the principal \<open>D\<^bsub>e\<^sub>3\<^esub> body\<close>, so
  OT-heredity (@{thm [source] m_8_7_OT_scb_recursive}) reads \<open>D\<^bsub>e\<^sub>3\<^esub> body \<in> OT\<close> off the
  host's own \<open>Trans M \<in> OT\<^bsub>B\<^esub>\<close>, whence \<open>isOT\<^bsub>BT\<^esub> body\<close>.  The kind-1 anchor comes from
  @{thm [source] oi5_IIIIV_pkg} under \<open>ltJ\<close>, and from @{thm [source] c4dx_condIV_k1} at
  the condIV \<open>admeq\<close> corner (there \<open>j\<^sub>-\<^sub>3 = j\<^sub>-\<^sub>1\<close>, so \<open>Mark M j\<^sub>-\<^sub>3 = c\<^sub>2\<close>, i.e.
  \<open>transC2 M = Trans (s84x_N M)\<close>).\<close>

lemma oi5_bodyOT:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
    and ihOT: "Trans M \<in> OT_B"
  shows "isOT_BT (bpHeadT (Trans (s84x_N M)))"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "M \<in> T_PS" using MPT by (simp add: PT_PS_def)
  have bodyTB: "?body \<in> T_B" by (rule oi5_regime(3)[OF MST MPT hp j1gt branch])
  have DptTB: "Dpt (enat ?e3) ?body \<in> T_B" using bodyTB by (simp add: T_B_def)
  \<comment> \<open>the kind-1 anchor of \<open>Trans M\<close> at \<open>D\<^bsub>e\<^sub>3\<^esub> body\<close>, in BOTH regimes\<close>
  have anchor: "\<exists>s1 b1. scb_decomp (Trans M) s1
                  (flatBT (Dpt (enat ?e3) ?body)) b1"
  proof (cases "s84x_jm3 M < transJm1 M")
    case True
    obtain s0' b0' s1 b1 where
      k1: "scb_kind1 (Trans M) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
      by (rule oi5_IIIIV_pkg[OF MST MPT hp j1gt branch True])
    have "scb_decomp (Trans M) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
      using k1 by (simp add: scb_kind1_def)
    thus ?thesis by blast
  next
    case False
    have cIV: "transCondIV M" and admeq: "Adm M (s84x_jm2 M) = transJm1 M"
      using oi5_ltJ_or_IVadmeq[OF MST MPT hp j1gt branch] False by blast+
    have jm3eq: "s84x_jm3 M = transJm1 M" using admeq by (simp add: s84x_jm3_def)
    have nVI: "\<not> transCondVI M" using c4dx_condIV_excl(4)[OF cIV] .
    have T1: "transT1 M \<noteq> 0\<^sub>B" using s84d_L4_regime[OF MST MPT hp nVI] by simp
    have J1pos: "transJ1 M > 0" using j1gt by (simp add: transJ1_def)
    \<comment> \<open>\<open>transC2 M = Trans (s84x_N M)\<close> at the \<open>admeq\<close> corner\<close>
    have jm2lt: "s84x_jm2 M < Lng M - 1" by (rule s84c1_jm2_basic(1)[OF hp])
    have jm3le: "s84x_jm3 M \<le> s84x_jm2 M"
      using adm_Adm_le by (simp add: s84x_jm3_def)
    have jm3lt: "s84x_jm3 M < Lng M - 1" using jm3le jm2lt by linarith
    have mM3: "(M, s84x_jm3 M) \<in> Marked"
      using s84d_jm3_Marked(1)[OF MR MT hp] by simp
    have repr: "Mark M (s84x_jm3 M) = Trans (s84x_N M)"
      using m_7_4_Mark_Trans_repr[OF mM3 MR jm3lt] by (simp add: s84x_N_def)
    have mk2: "Mark M (transJm1 M) = transC2 M"
      by (rule m_7_3_Mark_rightmost2[OF MR MPT J1pos T1])
    have c2eq: "transC2 M = Trans (s84x_N M)" using repr mk2 jm3eq by simp
    have k1: "scb_kind1 (Trans M) (s84x_s1 M)
                (flatBT (Dpt (enat ?e3) (bpHeadT (transC2 M)))) (s84x_b1 M)"
      by (rule c4dx_condIV_k1[OF MST MPT hp cIV admeq])
    have "scb_decomp (Trans M) (s84x_s1 M)
            (flatBT (Dpt (enat ?e3) ?body)) (s84x_b1 M)"
      using k1 c2eq by (simp add: scb_kind1_def)
    thus ?thesis by blast
  qed
  obtain s1 b1 where
    scbd: "scb_decomp (Trans M) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    using anchor by blast
  have DptOT: "Dpt (enat ?e3) ?body \<in> OT"
    by (rule m_8_7_OT_scb_recursive[OF ihOT DptTB scbd])
  hence "isOT_BT (Dpt (enat ?e3) ?body)" by (simp add: OT_def)
  hence "isOT_BP (DB (enat ?e3) ?body)" by simp
  thus ?thesis by simp
qed

text \<open>\<^bold>\<open>The \<open>LbaseU\<close> slot --- no hypothesis beyond the census premises.\<close>\<close>

lemma oi5_LbaseU:
  fixes Q :: pairseq and s0 b0 :: "Sym list"
  assumes QST: "Q \<in> ST_PS" and QPT: "Q \<in> PT_PS"
    and j1gt: "1 < Lng Q - 1"
    and branch: "transCondIII Q \<or> transCondIV Q"
    and ihOT: "Trans Q \<in> OT_B"
    and hp: "hasParent Q 1 (Lng Q - 1)"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N Q))) s0
                 (flatBT (Dpt (enat (entry Q 1 (Lng Q - 1))) 0\<^sub>B)) b0"
  shows "leBT (Dpt (enat (entry Q 1 (Lng Q - 1) - 1)) 0\<^sub>B)
           (d4vx_ins s0 (entry Q 1 (Lng Q - 1) - 1) b0 0\<^sub>B)"
proof -
  note regime = oi5_regime[OF QST QPT hp j1gt branch]
  have bodyOT: "isOT_BT (bpHeadT (Trans (s84x_N Q)))"
    by (rule oi5_bodyOT[OF QST QPT hp j1gt branch ihOT])
  show ?thesis
    by (rule opf_Lbase_of_domB[OF regime(3) bodyOT regime(4) inner])
qed

subsection \<open>r72: tower algebra for the \<open>0\<^sub>B\<close>-seeded core, and the re-seeded \<open>base\<^sub>1\<close>\<close>

text \<open>\<open>d4vx_core\<close> is \<open>ins\<^sup>k\<close>, so it is monotone in its seed and additive in its index.\<close>

lemma oy1_core_mono:
  fixes W :: BT and hole :: BP and s0 b0 :: "Sym list" and ub :: nat
  assumes wrap: "flatBT W = s0 @ flatBP hole @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and lt: "lessBT X Y"
  shows "lessBT (d4vx_core s0 ub b0 X k) (d4vx_core s0 ub b0 Y k)"
proof (induction k)
  case 0
  show ?case using lt by simp
next
  case (Suc k)
  show ?case
    using c4cx_d4vx_ins_mono[OF wrap b0RP Suc.IH, of ub] by simp
qed

lemma oy1_core_add:
  "d4vx_core s0 ub b0 X (a + b) = d4vx_core s0 ub b0 (d4vx_core s0 ub b0 X b) a"
  by (induction a) simp_all

lemma oy1_ins_le_mono:
  fixes W :: BT and hole :: BP
  assumes wrap: "flatBT W = s0 @ flatBP hole @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and le: "leBT X Y"
  shows "leBT (d4vx_ins s0 ub b0 X) (d4vx_ins s0 ub b0 Y)"
proof (cases "X = Y")
  case True
  thus ?thesis by simp
next
  case False
  have "lessBT X Y" using le False by blast
  thus ?thesis using c4cx_d4vx_ins_mono[OF wrap b0RP, of X Y ub] by blast
qed

text \<open>\<open>b1x_triG z b a\<close> quantifies over the interval \<open>[b, a]\<close>, so it is ANTITONE in
  its upper endpoint: shrinking \<open>a\<close> only removes instances.\<close>

lemma oy1_triG_antitone:
  assumes tri: "b1x_triG z b a" and le: "leBT a' a"
  shows "b1x_triG z b a'"
  unfolding b1x_triG_def
proof (intro allI impI)
  fix u :: enat and c :: BT
  assume bc: "leBT b c" and ca: "leBT c a'"
  have "leBT c a" by (rule od4_leBT_trans[OF ca le])
  thus "b1x_setle (GBT u b) (GBT u c \<union> GBT u z \<union> {Trm []})"
    using tri bc unfolding b1x_triG_def by blast
qed

text \<open>\<^bold>\<open>\<open>base\<^sub>1\<close>, re-seeded to \<open>0\<^sub>B\<close>\<close> --- \<open>A\<^sub>0 < d4vx_ins s\<^sub>0 ub b\<^sub>0 0\<^sub>B = Y\<^sub>1\<close>.  This is
  @{thm [source] crx_base1_of_nest} / @{thm [source] cnv_base1_of_nest} with the
  inserted core \<open>D\<^bsub>ub\<^esub>0\<close> replaced by \<open>0\<^sub>B\<close>: the surgery term seen ONE level up is then
  \<open>c' = D\<^bsub>ub\<^esub>0\<close> instead of \<open>D\<^bsub>ub\<^esub>(D\<^bsub>ub\<^esub>0)\<close>, and the comparison is decided by the SAME
  shared-wrapper growth step \<open>D\<^bsub>tv\<^esub>t\<^sub>2 < D\<^bsub>tv\<^esub>(t\<^sub>2 + c')\<close> --- which needs only that \<open>c'\<close> is
  a nonempty principal, NOT what sits inside it.  (Empirically: 363/363 real
  condIII/IV hosts, python/_r72_reseed_step0b.py.)\<close>

text \<open>The census-level \<open>base\<^sub>1\<^sup>Y\<close>: \<open>A\<^sub>0 < Y\<^sub>1\<close>, on the \<open>ltJ\<close> hosts (the raw
  decompositions come from @{thm [source] cpx_condIII_mnform}, exactly as in
  \<open>ot1_tri0_census\<close> below).\<close>

lemma oy1_base1Y:
  fixes N :: pairseq and s0 b0 :: "Sym list"
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                 (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
  shows "lessBT (bpHeadT (Trans (Pred (s84x_N N))))
           (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0 0\<^sub>B)"
proof -
  have MR: "N \<in> RT_PS" using NST m_6_7_ST_PS_subseteq_RT_PS by blast
  have REGS: "s84x_jm3 N < s84x_jm2 N \<Longrightarrow>
                cfbx_reg (s84x_jm2 N - s84x_jm3 N) (Red (s84x_N N))"
  proof -
    assume g: "s84x_jm3 N < s84x_jm2 N"
    show "cfbx_reg (s84x_jm2 N - s84x_jm3 N) (Red (s84x_N N))"
      by (rule mcx_regS[OF NST NPT hp j1gt branch g])
  qed
  have REGSP: "s84x_jm3 N < s84x_jm2 N \<Longrightarrow> Br (Red (Pred (s84x_N N))) \<noteq> [] \<Longrightarrow>
                 cfbx_reg (s84x_jm2 N - s84x_jm3 N) (Red (Pred (s84x_N N)))"
  proof -
    assume g: "s84x_jm3 N < s84x_jm2 N" and b: "Br (Red (Pred (s84x_N N))) \<noteq> []"
    show "cfbx_reg (s84x_jm2 N - s84x_jm3 N) (Red (Pred (s84x_N N)))"
      by (rule slx37_regSP_uncond[OF NST NPT hp j1gt branch g b])
  qed
  have nVI: "\<not> transCondVI N"
  proof (cases "transCondIII N")
    case True
    thus ?thesis by (auto simp: transCondIII_def transCondVI_def)
  next
    case False
    hence cIV: "transCondIV N" using branch by blast
    show ?thesis using c4dx_condIV_excl(4)[OF cIV] .
  qed
  have J1pos: "transJ1 N > 0" using j1gt by (simp add: transJ1_def)
  have T1: "transT1 N \<noteq> 0\<^sub>B"
    using s84d_L4_regime[OF NST NPT hp nVI] by simp
  obtain u1 u2 v2 w1 s1 b1 where
      dPq: "scb_decomp (Trans (Pred (s84x_N N)))
              (Dsym (enat (entry N 1 (s84x_jm3 N))) # u1) (flatBT (transC1 N)) w1"
    and d2q: "scb_decomp (Trans (s84x_N N))
              (Dsym (enat (entry N 1 (s84x_jm3 N))) # u1) (flatBT (transC2 N)) w1"
    and d4c2q: "scb_decomp (transC2 N) u2
              (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) v2"
    using cpx_condIII_mnform[OF NST NPT hp j1gt branch ltJ REGS REGSP] by blast
  show ?thesis
  proof (cases "transCondIII N")
    case True
    show ?thesis
      by (rule oy1_base1Y_condIII[OF MR NPT J1pos T1 True dPq d2q d4c2q inner])
  next
    case False
    hence cIV: "transCondIV N" using branch by blast
    show ?thesis
      by (rule oy1_base1Y_condIV[OF MR NPT J1pos T1 cIV dPq d2q d4c2q inner])
  qed
qed


text \<open>\<open>base\<^sub>1\<^sup>Y\<close> for the condIV \<open>admeq\<close> tower seed \<open>t\<^sub>2 = transT2 M\<close>: verbatim
  @{thm [source] c4dx_condIV_base1} with the inserted core \<open>D\<^bsub>ub\<^esub>0\<close> replaced by \<open>0\<^sub>B\<close>
  (so the one-level-up surgery term is \<open>c' = D\<^bsub>ub\<^esub>0\<close>); the growth step is again
  seed-independent.\<close>

lemma oy1_base1Y_t2:
  fixes M :: pairseq and s0 b0 :: "Sym list"
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and cIV: "transCondIV M"
    and inner: "scb_decomp (bpHeadT (transC2 M)) s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
  shows "lessBT (transT2 M)
           (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0 0\<^sub>B)"
proof -
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "?v1 - 1"
  let ?jpe = "entry M 1 (transJ0 M)"
  let ?c = "Dpt (enat ?v1) 0\<^sub>B"
  let ?c' = "Dpt (enat ?ub) 0\<^sub>B"
  obtain t3 t4 where t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B"
    and body: "bpHeadT (transC2 M) = t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B ?c)"
    and rel: "(t3 = transT2 M \<and> t4 = transT2 M)
              \<or> transT2 M = t3 +\<^sub>B Dpt (enat ?jpe) t4"
    using c4dx_condIV_c2body_shape[OF MR MP J1pos T1 cIV] by blast
  have cTB: "?c \<in> T_B" by (simp add: T_B_def)
  have cp: "\<exists>p. ?c = Trm [p]" by auto
  have c'TB: "?c' \<in> T_B" by (simp add: T_B_def)
  have c'p: "\<exists>p. ?c' = Trm [p]" by auto
  \<comment> \<open>shared trailing-principal wrapper of \<open>t\<^sub>4 + \<cdot>\<close>, for hole and insertion alike\<close>
  obtain w4 w4' where d4: "scb_decomp (t4 +\<^sub>B ?c) w4 (flatBT ?c) w4'"
    using m_7_2_add_scb_conj1[OF t4TB cTB cp] unfolding MarkedB_def by auto
  have d4': "scb_decomp (t4 +\<^sub>B ?c') w4 (flatBT ?c') w4'"
    by (rule m_7_2_add_scb_conj2[OF t4TB cTB cp c'TB c'p d4])
  have iptc: "isPTB_str (flatBT ?c)" by (rule isPTB_str_Dpt) simp_all
  have iptc': "isPTB_str (flatBT ?c')" by (rule isPTB_str_Dpt) simp_all
  have d5: "scb_decomp (Dpt (enat ?jpe) (t4 +\<^sub>B ?c))
              (Dsym (enat ?jpe) # w4) (flatBT ?c) w4'"
    by (rule scb_Dpt_lift[OF d4 iptc])
  have d5': "scb_decomp (Dpt (enat ?jpe) (t4 +\<^sub>B ?c'))
              (Dsym (enat ?jpe) # w4) (flatBT ?c') w4'"
    by (rule scb_Dpt_lift[OF d4' iptc'])
  have bodyne: "bpHeadT (transC2 M) \<noteq> Trm []" by (rule bpHeadT_transC2_nonzero)
  define STRUCT where "STRUCT = t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B ?c')"
  have flatSTRUCT: "flatBT STRUCT = s0 @ flatBT ?c' @ b0"
  proof (cases "t3 = 0\<^sub>B")
    case True
    have bA: "bpHeadT (transC2 M) = Dpt (enat ?jpe) (t4 +\<^sub>B ?c)"
      using body True by simp
    have DA: "scb_decomp (bpHeadT (transC2 M)) (Dsym (enat ?jpe) # w4) (flatBT ?c) w4'"
      using d5 bA by simp
    have pin: "Dsym (enat ?jpe) # w4 = s0 \<and> w4' = b0"
      by (rule m_7_2_scb_unique_sb[OF DA inner bodyne])
    have SA: "STRUCT = Dpt (enat ?jpe) (t4 +\<^sub>B ?c')"
      using STRUCT_def True by simp
    show ?thesis using d5' SA pin by (simp add: scb_decomp_def)
  next
    case False
    have X1: "length (untrm (Dpt (enat ?jpe) (t4 +\<^sub>B ?c))) = 1" by simp
    have X1': "length (untrm (Dpt (enat ?jpe) (t4 +\<^sub>B ?c'))) = 1" by simp
    have Yne: "untrm t3 \<noteq> []" using False by (cases t3) auto
    have DA: "scb_decomp (bpHeadT (transC2 M))
                (liftS t3 (Dsym (enat ?jpe) # w4)) (flatBT ?c) (w4' @ [RP])"
      using scb_addBT_left[OF d5 X1 Yne] body by simp
    have pin: "liftS t3 (Dsym (enat ?jpe) # w4) = s0 \<and> w4' @ [RP] = b0"
      by (rule m_7_2_scb_unique_sb[OF DA inner bodyne])
    have DA': "scb_decomp STRUCT
                (liftS t3 (Dsym (enat ?jpe) # w4)) (flatBT ?c') (w4' @ [RP])"
      using scb_addBT_left[OF d5' X1' Yne] STRUCT_def by simp
    show ?thesis using DA' pin by (simp add: scb_decomp_def)
  qed
  have insEq: "d4vx_ins s0 ?ub b0 0\<^sub>B = STRUCT"
  proof -
    have "d4vx_ins s0 ?ub b0 0\<^sub>B = unflatBT (s0 @ flatBT ?c' @ b0)"
      by (simp add: d4vx_ins_def)
    also have "\<dots> = unflatBT (flatBT STRUCT)" using flatSTRUCT by simp
    also have "\<dots> = STRUCT" by (rule unflatBT_flat)
    finally show ?thesis .
  qed
  consider (A) "t3 = transT2 M \<and> t4 = transT2 M"
    | (B) "transT2 M = t3 +\<^sub>B Dpt (enat ?jpe) t4"
    using rel by blast
  hence grow: "lessBT (transT2 M) STRUCT"
  proof cases
    case A
    have "STRUCT = transT2 M +\<^sub>B Trm [DB (enat ?jpe) (t4 +\<^sub>B ?c')]"
      using STRUCT_def A by simp
    thus ?thesis
      using c4dx_lessBT_grow[of "transT2 M" "DB (enat ?jpe) (t4 +\<^sub>B ?c')"] by simp
  next
    case B
    have gi: "lessBT t4 (t4 +\<^sub>B ?c')"
      using c4dx_lessBT_grow[of t4 "DB (enat ?ub) 0\<^sub>B"] by simp
    have gl: "lessBT (Dpt (enat ?jpe) t4) (Dpt (enat ?jpe) (t4 +\<^sub>B ?c'))"
      using gi by simp
    have "lessBT (t3 +\<^sub>B Dpt (enat ?jpe) t4) (t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B ?c'))"
      by (rule lessBT_addBT_mono_right[OF gl])
    thus ?thesis using B STRUCT_def by simp
  qed
  show ?thesis using grow insEq by simp
qed


text \<open>\<^bold>\<open>CENSUS v4 (r55, r72-relocated).\<close>  The \<open>OTpred\<close> residuals \<open>DEEPOT\<close> and \<open>NOBR\<close>
  are GONE (@{thm [source] od4_DEEPOT}, @{thm [source] od4_NOBR}), and the corrected
  rule's \<open>LbaseU\<close> slot is discharged by @{thm [source] oi5_LbaseU}: both termination
  pillars rest on \<open>{OTint, TVall, ordIntC}\<close> alone.\<close>

theorem od4_termination_census_v4:
  assumes OTint: "\<And>N m. N \<in> ST_PS \<Longrightarrow> N \<in> PT_PS \<Longrightarrow> 1 < Lng N - 1 \<Longrightarrow>
                  transCondIII N \<or> transCondIV N \<or> transCondV N \<Longrightarrow>
                  Trans N \<in> OT_B \<Longrightarrow> 1 < m \<Longrightarrow> Trans ((N::pairseq)[m]) \<in> OT_B"
    and TVall: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
                  transCondII K \<Longrightarrow> c2sx_tailval K"
    and ordIntC: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
                  transCondIII P \<or> transCondIV P \<or> transCondV P \<Longrightarrow>
                  Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
                  leBT (Trans ((P::pairseq)[n])) (Trans P)"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule opx_termination_census_v3(1)[OF OTint TVall ordIntC od4_DEEPOT od4_NOBR
          oi5_LbaseU])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule opx_termination_census_v3(2)[OF OTint TVall ordIntC od4_DEEPOT od4_NOBR
          oi5_LbaseU])
qed


subsection \<open>The \<open>OTint\<close> step on \<open>hasParent\<close> condIII/IV hosts, modulo the two
  one-block tower facts \<open>OTA1\<close> and \<open>SETLE1\<close>\<close>

text \<open>THE r55 COLLAPSE.  For \<open>m = Suc k\<close>, \<open>k \<ge> 1\<close>, the three aligned terms
  \<open>Trans (M[Suc k])\<close>, \<open>operB (Trans M) (numBT k)\<close>,
  \<open>operB (Trans M) (numBT (Suc k))\<close> share the surgery context \<open>k - 1\<close> tower
  blocks below the kind-1 hole, where their cores are the FIXED triple
  \<open>D\<^sub>h A\<^sub>1 / D\<^sub>h X\<^sub>1 / D\<^sub>h X\<^sub>2\<close> (\<open>h = e\<^sub>3\<close> for \<open>k = 1\<close>, \<open>h = ub\<close> for \<open>k \<ge> 2\<close>) ---
  so ONE application of the proven transport @{thm [source] otx3_transport}
  per case closes the step from the \<open>k\<close>-independent one-block facts.
  \<open>isOT_BP (DB ub A\<^sub>1)\<close> follows from \<open>isOT_BP (DB e\<^sub>3 A\<^sub>1)\<close> by \<open>G\<close>-antitonicity
  (\<open>e\<^sub>3 \<le> ub\<close>, @{thm [source] b1x_GBT_antitone}).\<close>

lemma oi5_OTint_IIIIV_hp:
  fixes N :: pairseq and m :: nat
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and ihOT: "Trans N \<in> OT_B" and mgt: "1 < m"
  shows "Trans ((N::pairseq)[m]) \<in> OT_B"
proof -
  let ?e3 = "entry N 1 (s84x_jm3 N)"
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  have MR: "N \<in> RT_PS" using NST m_6_7_ST_PS_subseteq_RT_PS by blast
  \<comment> \<open>package and regime\<close>
  obtain s0 b0 s1 b1 where
    b0RP: "\<forall>x \<in> set b0. x = RP" and b1RP: "\<forall>x \<in> set b1. x = RP"
    and inner: "scb_decomp ?body s0 (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0"
    and k1: "scb_kind1 (Trans N) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    and mn: "\<forall>m. 1 \<le> m \<longrightarrow>
        flatBT (Trans ((N::pairseq)[m]))
          = s1 @ Dsym (enat ?e3)
              # flatBT (d4vx_core s0 ?ub b0 ?A0 (m - 1)) @ b1"
    and base0: "lessBT (Dpt (enat ?ub) 0\<^sub>B) ?A0"
    and base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 0\<^sub>B)"
    and A0TB: "?A0 \<in> T_B"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  note regime = oi5_regime[OF NST NPT hp j1gt branch]
  have uv: "?e3 < ?v1" by (rule regime(1))
  have e3ub: "?e3 \<le> ?ub" by (rule regime(2))
  have bodyT: "?body \<in> T_B" by (rule regime(3))
  have dbbodyH: "domB ?body = TBv (enat ?ub)" by (rule regime(4))
  have TT: "Trans N \<in> T_B" by (rule regime(5))
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "flatBT ?body = s0 @ flatBT (Dpt (enat ?v1) 0\<^sub>B) @ b0"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0 @ [Dsym (enat ?v1), Zsym] @ b0" using z by simp
    thus False by (cases s0) auto
  qed
  \<comment> \<open>towers.  r72: under the CORRECTED fundamental sequence the operB core is the
      \<open>0\<^sub>B\<close>-seeded tower \<open>Y\<^sub>n = ins\<^sup>n 0\<^sub>B\<close>, ONE LEVEL DEEPER than the old \<open>X\<^sub>n = ins\<^sup>n(D\<^bsub>ub\<^esub>0)\<close>.
      \<open>X\<^sub>0/X\<^sub>1\<close> survive only as the carriers of \<open>base\<^sub>0\<close>/\<open>base\<^sub>1\<close>.\<close>
  define X0 where "X0 = Dpt (enat ?ub) 0\<^sub>B"
  define A1 where "A1 = d4vx_ins s0 ?ub b0 ?A0"
  define Y1 where "Y1 = d4vx_ins s0 ?ub b0 0\<^sub>B"
  define Y2 where "Y2 = d4vx_ins s0 ?ub b0 Y1"
  define Y3 where "Y3 = d4vx_ins s0 ?ub b0 Y2"
  have X0TB: "X0 \<in> T_B" by (simp add: X0_def T_B_def)
  have ZTB: "0\<^sub>B \<in> T_B" by (simp add: T_B_def)
  have A1TB: "A1 \<in> T_B"
    unfolding A1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT A0TB])
  have Y1TB: "Y1 \<in> T_B"
    unfolding Y1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT ZTB])
  have Y2TB: "Y2 \<in> T_B"
    unfolding Y2_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT Y1TB])
  have Y3TB: "Y3 \<in> T_B"
    unfolding Y3_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT Y2TB])
  have fA1: "flatBT A1 = s0 @ Dsym (enat ?ub) # flatBT ?A0 @ b0"
    unfolding A1_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fY1: "flatBT Y1 = s0 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ b0"
    unfolding Y1_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fY2: "flatBT Y2 = s0 @ Dsym (enat ?ub) # flatBT Y1 @ b0"
    unfolding Y2_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fY3: "flatBT Y3 = s0 @ Dsym (enat ?ub) # flatBT Y2 @ b0"
    unfolding Y3_def by (rule d4vx_ins_flat[OF wrap b0RP])
  \<comment> \<open>orders (\<open>ins\<close>-monotonicity, @{thm [source] c4cx_d4vx_ins_mono}):
      \<open>Y\<^sub>1 \<le> A\<^sub>1\<close> from \<open>0\<^sub>B < A\<^sub>0\<close> (\<open>base\<^sub>0\<close>), \<open>A\<^sub>1 \<le> Y\<^sub>3\<close> from \<open>A\<^sub>0 < Y\<^sub>1 < Y\<^sub>2\<close>
      (\<open>base\<^sub>1\<^sup>Y\<close>, r72)\<close>
  have zltA0: "lessBT 0\<^sub>B ?A0"
  proof -
    have "lessBT 0\<^sub>B X0" by (simp add: X0_def)
    thus ?thesis using base0[folded X0_def] lessBT_trans by blast
  qed
  have ordlo: "leBT Y1 A1"
    unfolding Y1_def A1_def
    using c4cx_d4vx_ins_mono[OF wrap b0RP zltA0, of ?ub] by blast
  have A0ltY1: "lessBT ?A0 Y1" using base1[folded Y1_def] .
  have zltY1: "lessBT 0\<^sub>B Y1" using zltA0 A0ltY1 lessBT_trans by blast
  have Y1ltY2: "lessBT Y1 Y2"
    unfolding Y1_def Y2_def
    using c4cx_d4vx_ins_mono[OF wrap b0RP zltY1, of ?ub]
    by (simp add: Y1_def)
  have A0ltY2: "lessBT ?A0 Y2" using A0ltY1 Y1ltY2 lessBT_trans by blast
  have ordhi: "leBT A1 Y3"
    unfolding A1_def Y3_def
    using c4cx_d4vx_ins_mono[OF wrap b0RP A0ltY2, of ?ub] by blast
  \<comment> \<open>the one-block facts (the \<open>SETLE1\<close> slot is now \<open>Y\<^sub>1\<close>-seeded)\<close>
  have newOTe3: "isOT_BP (DB (enat ?e3) A1)"
    unfolding A1_def by (rule OTA1[OF NST NPT hp j1gt branch ihOT b0RP inner])
  have newOTub: "isOT_BP (DB (enat ?ub) A1)"
  proof -
    have A1OT: "isOT_BT A1"
      and gE3: "\<forall>x \<in> GBT (enat ?e3) A1. lessBT x A1"
      using newOTe3 by simp_all
    have le: "enat ?e3 \<le> enat ?ub" using e3ub by simp
    have "GBT (enat ?ub) A1 \<subseteq> GBT (enat ?e3) A1"
      by (rule b1x_GBT_antitone[OF le])
    hence "\<forall>x \<in> GBT (enat ?ub) A1. lessBT x A1" using gE3 by blast
    thus ?thesis using A1OT by simp
  qed
  have setle: "\<And>u. b1x_setle (GBT u A1) (insert Y1 (GBT u Y1))"
    unfolding A1_def Y1_def
    by (rule SETLE1[OF NST NPT hp j1gt branch ihOT b0RP inner])
  \<comment> \<open>fseq closed form of the donors: core \<open>= Y\<^bsub>n+1\<^esub>\<close>\<close>
  have fseq: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate (n + 1) (s0 @ [Dsym (enat ?ub)]))
           @ [Zsym]
           @ concat (replicate (n + 1) b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbodyH bodyne inner k1])
  have Yflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 0\<^sub>B n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT 0\<^sub>B @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fseqY: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)) @ b1"
  proof -
    fix n :: nat
    have A: "flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))
        = concat (replicate (Suc n) (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (Suc n) b0)"
      using Yflat[of "Suc n"] by (simp del: d4vx_core.simps)
    show "flatBT (operB (Trans N) (numBT n))
        = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)) @ b1"
      using fseq[of n] A by (simp del: d4vx_core.simps)
  qed
  \<comment> \<open>donor OT-ness ([Buc1] closure on the slot's own IH)\<close>
  have donOT: "\<And>n. isOT_BT (operB (Trans N) (numBT n))"
    using e4x_OT_B_operB_numBT[OF ihOT] by (simp add: OT_B_def OT_def)
  \<comment> \<open>index bookkeeping\<close>
  obtain k where mk: "m = Suc k" using mgt by (cases m) auto
  have k1n: "1 \<le> k" using mgt mk by simp
  have mnm: "flatBT (Trans ((N::pairseq)[m]))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 ?A0 k) @ b1"
    using mn mgt mk by simp
  \<comment> \<open>the transport, one application per index regime; cores are the FIXED triple
      \<open>(Y\<^sub>1, A\<^sub>1, Y\<^sub>3)\<close> and the donors are \<open>numBT (k-1)\<close> / \<open>numBT (k+1)\<close>\<close>
  have isot: "isOT_BT (Trans ((N::pairseq)[m]))"
  proof (cases "k = 1")
    case True
    \<comment> \<open>hole = the kind-1 position itself, head \<open>e\<^sub>3\<close>; donors \<open>numBT 0\<close> / \<open>numBT 2\<close>\<close>
    have fA1c: "flatBT (d4vx_core s0 ?ub b0 ?A0 k) = flatBT A1"
      using True by (simp add: A1_def)
    have ourflat: "flatBT (Trans ((N::pairseq)[m]))
        = s1 @ flatBT (Dpt (enat ?e3) A1) @ b1"
      using mnm fA1c by simp
    have loflat: "flatBT (operB (Trans N) (numBT 0))
        = s1 @ flatBT (Dpt (enat ?e3) Y1) @ b1"
      using fseqY[of 0] by (simp add: Y1_def)
    have hiflat: "flatBT (operB (Trans N) (numBT (Suc (Suc 0))))
        = s1 @ flatBT (Dpt (enat ?e3) Y3) @ b1"
    proof -
      have "d4vx_core s0 ?ub b0 0\<^sub>B (Suc (Suc (Suc 0))) = Y3"
        by (simp add: Y1_def Y2_def Y3_def)
      thus ?thesis using fseqY[of "Suc (Suc 0)"] by simp
    qed
    have ourdec: "scb_decomp (Trans ((N::pairseq)[m])) s1
                    (flatBT (Dpt (enat ?e3) A1)) b1"
      unfolding scb_decomp_def
      using ourflat b1RP isPTB_str_Dpt[of "enat ?e3" A1] A1TB
      by (simp add: T_B_def)
    have lodec: "scb_decomp (operB (Trans N) (numBT 0)) s1
                    (flatBT (Dpt (enat ?e3) Y1)) b1"
      unfolding scb_decomp_def
      using loflat b1RP isPTB_str_Dpt[of "enat ?e3" Y1] Y1TB
      by (simp add: T_B_def)
    have hidec: "scb_decomp (operB (Trans N) (numBT (Suc (Suc 0)))) s1
                    (flatBT (Dpt (enat ?e3) Y3)) b1"
      unfolding scb_decomp_def
      using hiflat b1RP isPTB_str_Dpt[of "enat ?e3" Y3] Y3TB
      by (simp add: T_B_def)
    have "isOT_BT (Trans ((N::pairseq)[m]))"
      by (rule oix_transportD[OF otx3_transport lodec ourdec hidec
            donOT donOT newOTe3 ordlo ordhi setle])
    thus ?thesis .
  next
    case False
    obtain k' where kA: "k = Suc k'" using k1n by (cases k) auto
    have k'ne: "k' \<noteq> 0" using False kA by simp
    then obtain k2 where kB: "k' = Suc k2" by (cases k') auto
    have kk: "k = Suc (Suc k2)" using kA kB by simp
    \<comment> \<open>hole = \<open>k - 1\<close> blocks deep, head \<open>ub\<close>; donors \<open>numBT (Suc k2) = numBT (k-1)\<close>
        and \<open>numBT (Suc k) = numBT (k+1)\<close>, cores \<open>(Y\<^sub>1, A\<^sub>1, Y\<^sub>3)\<close>\<close>
    let ?blk = "s0 @ [Dsym (enat ?ub)]"
    let ?S = "s1 @ Dsym (enat ?e3) # concat (replicate k2 ?blk) @ s0"
    let ?B = "concat (replicate (Suc k2) b0) @ b1"
    have BRP: "\<forall>x \<in> set ?B. x = RP"
      using oi5_crep_RP[OF b0RP, of "Suc k2"] b1RP by auto
    \<comment> \<open>our flat at the deep hole\<close>
    have Aflat: "flatBT (d4vx_core s0 ?ub b0 ?A0 k)
        = concat (replicate k ?blk) @ flatBT ?A0 @ concat (replicate k b0)"
      by (rule d4vx_core_flat[OF wrap b0RP])
    have crepA: "concat (replicate k ?blk)
        = concat (replicate k2 ?blk) @ s0 @ [Dsym (enat ?ub)]
          @ s0 @ [Dsym (enat ?ub)]"
      using kk by (simp add: s85b_crep_comm_snoc s85b_crep_snoc s85b_crep_comm)
    have crepB: "concat (replicate k b0)
        = b0 @ concat (replicate (Suc k2) b0)"
      using kk by simp
    have ourflat: "flatBT (Trans ((N::pairseq)[m]))
        = ?S @ flatBT (Dpt (enat ?ub) A1) @ ?B"
      using mnm Aflat crepA crepB fA1 by simp
    \<comment> \<open>lo donor \<open>numBT (Suc k2) = numBT (k-1)\<close>: core \<open>Y\<^sub>1\<close> at the deep hole\<close>
    have Fk: "flatBT (operB (Trans N) (numBT (Suc k2)))
        = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 0\<^sub>B k) @ b1"
      using fseqY[of "Suc k2"] kk by (simp del: d4vx_core.simps)
    have loflat: "flatBT (operB (Trans N) (numBT (Suc k2)))
        = ?S @ flatBT (Dpt (enat ?ub) Y1) @ ?B"
      using Fk Yflat[of k] crepA crepB fY1 by simp
    \<comment> \<open>hi donor \<open>numBT (Suc k) = numBT (k+1)\<close>: core \<open>Y\<^sub>3\<close> at the deep hole\<close>
    have crepA3: "concat (replicate (Suc (Suc k)) ?blk)
        = concat (replicate k2 ?blk) @ s0 @ [Dsym (enat ?ub)]
          @ s0 @ [Dsym (enat ?ub)] @ s0 @ [Dsym (enat ?ub)]
          @ s0 @ [Dsym (enat ?ub)]"
      using kk by (simp add: s85b_crep_comm_snoc s85b_crep_snoc s85b_crep_comm)
    have crepB3: "concat (replicate (Suc (Suc k)) b0)
        = b0 @ b0 @ b0 @ concat (replicate (Suc k2) b0)"
      using kk by simp
    have Fh: "flatBT (operB (Trans N) (numBT (Suc k)))
        = s1 @ Dsym (enat ?e3)
            # flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc (Suc k))) @ b1"
      using fseqY[of "Suc k"] by (simp del: d4vx_core.simps)
    have hiflat: "flatBT (operB (Trans N) (numBT (Suc k)))
        = ?S @ flatBT (Dpt (enat ?ub) Y3) @ ?B"
      using Fh Yflat[of "Suc (Suc k)"] crepA3 crepB3 fY1 fY2 fY3 by simp
    have ourdec: "scb_decomp (Trans ((N::pairseq)[m])) ?S
                    (flatBT (Dpt (enat ?ub) A1)) ?B"
      unfolding scb_decomp_def
      using ourflat BRP isPTB_str_Dpt[of "enat ?ub" A1] A1TB
      by (simp add: T_B_def)
    have lodec: "scb_decomp (operB (Trans N) (numBT (Suc k2))) ?S
                    (flatBT (Dpt (enat ?ub) Y1)) ?B"
      unfolding scb_decomp_def
      using loflat BRP isPTB_str_Dpt[of "enat ?ub" Y1] Y1TB
      by (simp add: T_B_def)
    have hidec: "scb_decomp (operB (Trans N) (numBT (Suc k))) ?S
                    (flatBT (Dpt (enat ?ub) Y3)) ?B"
      unfolding scb_decomp_def
      using hiflat BRP isPTB_str_Dpt[of "enat ?ub" Y3] Y3TB
      by (simp add: T_B_def)
    have "isOT_BT (Trans ((N::pairseq)[m]))"
      by (rule oix_transportD[OF otx3_transport lodec ourdec hidec
            donOT donOT newOTub ordlo ordhi setle])
    thus ?thesis .
  qed
  \<comment> \<open>\<open>T\<^bsub>B\<^esub>\<close> side and assembly\<close>
  have m1: "1 \<le> m" using mgt by simp
  have NmST: "(N::pairseq)[m] \<in> ST_PS" by (rule ST_PS.oper[OF NST m1])
  have NmRT: "(N::pairseq)[m] \<in> RT_PS"
    using NmST m_6_7_ST_PS_subseteq_RT_PS by blast
  have "Trans ((N::pairseq)[m]) \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF NmRT])
  thus ?thesis using isot by (simp add: OT_B_def OT_def)
qed

subsection \<open>The \<open>otIII\<close> leg, closed modulo \<open>{OTA1, SETLE1}\<close>\<close>

text \<open>The \<open>hasParent\<close> branch is @{thm [source] oi5_OTint_IIIIV_hp} (\<open>ltJ\<close> holds
  under condIII: \<open>j\<^sub>-\<^sub>1 = j\<^sub>0\<close> and \<open>j\<^sub>-\<^sub>3 \<le> j\<^sub>-\<^sub>2 < j\<^sub>0\<close>); the no-row-1-parent branch
  collapses by \<open>N[m] = Pred N\<close> (@{thm [source] npx_oper_noParent_Pred}) and the
  exact readback \<open>operB (Trans N) (numBT 0) = Trans (Pred N)\<close>
  (@{thm [source] npx_operB_numBT0_Pred_condIII}) into the [Buc1] closure
  @{thm [source] e4x_OT_B_operB_numBT} on the slot's own IH.\<close>

lemma oi5_OTint_condIII:
  fixes N :: pairseq and m :: nat
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS" and j1gt: "1 < Lng N - 1"
    and cIII: "transCondIII N" and ihOT: "Trans N \<in> OT_B" and mgt: "1 < m"
  shows "Trans ((N::pairseq)[m]) \<in> OT_B"
proof (cases "hasParent N 1 (Lng N - 1)")
  case True
  have branch: "transCondIII N \<or> transCondIV N" using cIII by blast
  have jm1eq: "transJm1 N = transJ0 N"
    using cIII
    by (simp add: transJm1_def transJ0_def transJ1_def transCondIII_def Adm_def)
  have jm2ltj0: "s84x_jm2 N < transJ0 N"
    by (rule m_8_4_oper_props_1(1)[OF NST NPT True j1gt branch])
  have jm3le: "s84x_jm3 N \<le> s84x_jm2 N"
    using adm_Adm_le by (simp add: s84x_jm3_def)
  have ltJ: "s84x_jm3 N < transJm1 N" using jm3le jm2ltj0 jm1eq by linarith
  show ?thesis
    by (rule oi5_OTint_IIIIV_hp[OF OTA1 SETLE1 NST NPT True j1gt branch ltJ
          ihOT mgt])
next
  case False
  have NR: "N \<in> RT_PS" using NST m_6_7_ST_PS_subseteq_RT_PS by blast
  have j1gt0: "0 < Lng N - 1" using j1gt by simp
  have epos: "0 < entry N 1 (Lng N - 1)"
    using cIII by (simp add: transCondIII_def)
  have NmP: "(N::pairseq)[m] = Pred N"
    by (rule npx_oper_noParent_Pred[OF j1gt0 epos False])
  have rb: "operB (Trans N) (numBT 0) = Trans (Pred N)"
    by (rule npx_operB_numBT0_Pred_condIII[OF NR NPT j1gt cIII False])
  have "operB (Trans N) (numBT 0) \<in> OT_B"
    by (rule e4x_OT_B_operB_numBT[OF ihOT])
  thus ?thesis using NmP rb by simp
qed

subsection \<open>The \<open>otIV\<close> leg, closed modulo
  \<open>{OTA1, SETLE1, IVADMEQ, IVNP}\<close>\<close>

text \<open>The \<open>\<not> admeq\<close> \<open>hasParent\<close> branch has \<open>ltJ\<close> outright
  (@{thm [source] cnv_condIV_ltJ}) and shares the condIII package; the
  \<open>admeq\<close> branch (whose exchange runs through the r19/r41 \<open>c4dx\<close> package with
  tower base \<open>transT2\<close> instead of \<open>A\<^sub>0\<close>) and the no-row-1-parent corner (whose
  \<open>k = 0\<close> readback is only a \<open>leBT\<close> --- @{thm [source] dpx_condIV_noParent_operB0}
  --- so \<open>Trans (Pred N) \<in> OT\<^bsub>B\<^esub>\<close> does not fall out of the [Buc1] closure)
  are carried as the named residuals \<open>IVADMEQ\<close> / \<open>IVNP\<close>.  On the no-parent
  branch \<open>N[m] = Pred N\<close> still holds (\<open>M\<^bsub>1,j\<^sub>1\<^esub> > 0\<close> under condIV), so \<open>IVNP\<close>
  is stated as the sharp Pred-image fact.\<close>

lemma oi5_OTint_condIV:
  fixes N :: pairseq and m :: nat
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and IVNP: "\<And>P. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIV P \<Longrightarrow> \<not> hasParent P 1 (Lng P - 1) \<Longrightarrow>
        Trans P \<in> OT_B \<Longrightarrow> Trans (Pred P) \<in> OT_B"
    and NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS" and j1gt: "1 < Lng N - 1"
    and cIV: "transCondIV N" and ihOT: "Trans N \<in> OT_B" and mgt: "1 < m"
  shows "Trans ((N::pairseq)[m]) \<in> OT_B"
proof (cases "hasParent N 1 (Lng N - 1)")
  case True
  show ?thesis
  proof (cases "Adm N (s84x_jm2 N) = transJm1 N")
    case eq: True
    show ?thesis
      by (rule IVADMEQ[OF NST NPT \<open>hasParent N 1 (Lng N - 1)\<close> j1gt cIV eq
            ihOT mgt])
  next
    case neq: False
    have branch: "transCondIII N \<or> transCondIV N" using cIV by blast
    have ltJ: "s84x_jm3 N < transJm1 N"
      by (rule cnv_condIV_ltJ[OF NST NPT True j1gt cIV neq])
    show ?thesis
      by (rule oi5_OTint_IIIIV_hp[OF OTA1 SETLE1 NST NPT True j1gt branch ltJ
            ihOT mgt])
  qed
next
  case False
  have j1gt0: "0 < Lng N - 1" using j1gt by simp
  have epos: "0 < entry N 1 (Lng N - 1)"
    using cIV by (simp add: transCondIV_def)
  have NmP: "(N::pairseq)[m] = Pred N"
    by (rule npx_oper_noParent_Pred[OF j1gt0 epos False])
  have "Trans (Pred N) \<in> OT_B"
    by (rule IVNP[OF NST NPT j1gt cIV False ihOT])
  thus ?thesis using NmP by simp
qed

subsection \<open>Census tightening: both pillars modulo
  \<open>{OTA1, SETLE1, IVADMEQ, IVNP, DEEPOT, NOBR, FINRC}\<close>\<close>

text \<open>The r54 master census @{thm [source] oc4_termination_census_master_v2}
  with its \<open>otIII\<close>/\<open>otIV\<close> slots discharged by @{thm [source] oi5_OTint_condIII}
  / @{thm [source] oi5_OTint_condIV}: the two HOST-LEVEL deep-insertion
  residuals are replaced by the sharper ONE-BLOCK tower facts \<open>OTA1\<close>/\<open>SETLE1\<close>
  plus the two condIV corner slots \<open>IVADMEQ\<close>/\<open>IVNP\<close>.  \<open>DEEPOT\<close>/\<open>NOBR\<close>/\<open>FINRC\<close>
  keep their exact r54 shapes.\<close>

theorem oi5_termination_census:
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and IVNP: "\<And>P. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIV P \<Longrightarrow> \<not> hasParent P 1 (Lng P - 1) \<Longrightarrow>
        Trans P \<in> OT_B \<Longrightarrow> Trans (Pred P) \<in> OT_B"
    and DEEPOT: "\<And>K x q q' ps. K \<in> ST_PS \<Longrightarrow> monoT K \<Longrightarrow> Br K \<noteq> [] \<Longrightarrow>
             1 < Lng K - 1 \<Longrightarrow> Trans K \<in> OT_B \<Longrightarrow>
             Trans K = Dpt (enat (entry K 1 0)) (Trm ps +\<^sub>B Dpt (enat x) q) \<Longrightarrow>
             Trans (Pred K) = Dpt (enat (entry K 1 0)) (Trm ps +\<^sub>B Dpt (enat x) q') \<Longrightarrow>
             Trans (Pred K) \<in> OT_B"
    and NOBR: "\<And>K. K \<in> ST_PS \<Longrightarrow> monoT K \<Longrightarrow> Br K = [] \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             Trans K \<in> OT_B \<Longrightarrow> Trans (Pred K) \<in> OT_B"
    and FINRC: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             transCondII K \<Longrightarrow> tvx_finRc K"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have otIII: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIII P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
             Trans ((P::pairseq)[n]) \<in> OT_B"
    by (rule oi5_OTint_condIII[OF OTA1 SETLE1])
  have otIV: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
             Trans ((P::pairseq)[n]) \<in> OT_B"
    by (rule oi5_OTint_condIV[OF OTA1 SETLE1 IVADMEQ IVNP])
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oc4_termination_census_master_v2(1)[OF otIII otIV oi4_PredNp
          oi4_Lpv DEEPOT NOBR FINRC oi5_LbaseU])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oc4_termination_census_master_v2(2)[OF otIII otIV oi4_PredNp
          oi4_Lpv DEEPOT NOBR FINRC oi5_LbaseU])
qed

subsection \<open>The \<open>OTint\<close> slot and the \<open>OTmulti\<close> slot, same residuals\<close>

lemma oi5_OTint_slot:
  fixes N :: pairseq and m :: nat
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and IVNP: "\<And>P. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIV P \<Longrightarrow> \<not> hasParent P 1 (Lng P - 1) \<Longrightarrow>
        Trans P \<in> OT_B \<Longrightarrow> Trans (Pred P) \<in> OT_B"
    and NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS" and j1gt: "1 < Lng N - 1"
    and cond: "transCondIII N \<or> transCondIV N \<or> transCondV N"
    and ihOT: "Trans N \<in> OT_B" and mgt: "1 < m"
  shows "Trans ((N::pairseq)[m]) \<in> OT_B"
  by (rule oi4_OTint_slot_IIIIV[OF oi5_OTint_condIII[OF OTA1 SETLE1]
        oi5_OTint_condIV[OF OTA1 SETLE1 IVADMEQ IVNP]
        NST NPT j1gt cond ihOT mgt])

lemma oi5_OTmulti:
  fixes N :: pairseq and m :: nat
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and IVNP: "\<And>P. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIV P \<Longrightarrow> \<not> hasParent P 1 (Lng P - 1) \<Longrightarrow>
        Trans P \<in> OT_B \<Longrightarrow> Trans (Pred P) \<in> OT_B"
    and TVall: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
                  transCondII K \<Longrightarrow> c2sx_tailval K"
    and NST: "N \<in> ST_PS" and mu: "multiT N" and ihOT: "Trans N \<in> OT_B"
    and mgt: "1 < m" and NPred: "(N::pairseq)[m] \<noteq> Pred N"
  shows "Trans ((N::pairseq)[m]) \<in> OT_B"
  by (rule oc4_OTmulti[OF oi5_OTint_slot[OF OTA1 SETLE1 IVADMEQ IVNP]
        TVall NST mu ihOT mgt NPred oi5_LbaseU])


(* ===================================================================== *)
(* ===== r55 front A+B synthesis: discharge DEEPOT/NOBR via od4     ===== *)
(* ===================================================================== *)

text \<open>The r55 master census: front A's @{thm [source] oi5_termination_census}
  had \<open>DEEPOT\<close>/\<open>NOBR\<close> as ASSUMPTIONS (front A ran on a base without the
  \<open>od4_\<close> \<open>OTpred\<close> material).  Front B closed both unconditionally
  (@{thm [source] od4_DEEPOT}, @{thm [source] od4_NOBR}, instances of the
  hypothesis-free @{thm [source] od4_OTpred_mono}).  Composing them removes
  \<open>DEEPOT\<close>/\<open>NOBR\<close> from the residual set: both termination pillars now hold
  modulo \<open>{OTA1, SETLE1, IVADMEQ, IVNP, FINRC}\<close> only.\<close>

theorem oi6_termination_census:
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and IVNP: "\<And>P. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIV P \<Longrightarrow> \<not> hasParent P 1 (Lng P - 1) \<Longrightarrow>
        Trans P \<in> OT_B \<Longrightarrow> Trans (Pred P) \<in> OT_B"
    and FINRC: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             transCondII K \<Longrightarrow> tvx_finRc K"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi5_termination_census(1)[OF OTA1 SETLE1 IVADMEQ IVNP
          od4_DEEPOT od4_NOBR FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi5_termination_census(2)[OF OTA1 SETLE1 IVADMEQ IVNP
          od4_DEEPOT od4_NOBR FINRC])
qed



(* ===== r56 OTint one-block bricks: OTA1 engine (front A) + IVNP (front B) ===== *)


(* ===================================================================== *)
(* ===== r56 ot1_ : discharge OTA1/SETLE1 (the two one-block tower   ==== *)
(* =====   facts) into oi5_termination_census.  STEP-0 (python)      ==== *)
(* =====   confirmed OTA1 (isOT_BP) and SETLE1 (setle) hold 899/899  ==== *)
(* =====   on genuine condIII/IV ST_PS hosts, decomposition UNIQUE.  ==== *)
(* =====   Body-level drivers verified: tri0 = b1x_triG(Dinf X0)A0 X1,==== *)
(* =====   BE0 (G u A0 <= A0 all-u), newOT_body isOT_BP(DB ub A0).    ==== *)
(* =====   setle_body (G u A0 vs insert X0 (G u X0)) is FALSE (u=0),  ==== *)
(* =====   so the plain otx3_core is BLOCKED; the tri-variant below   ==== *)
(* =====   takes tri0 directly at the hole instead of rebuilding it   ==== *)
(* =====   from a (false) setle.                                       ==== *)
(* ===================================================================== *)

text \<open>@{text otx3_core_tri}: the deep-insertion transport engine
  @{thm [source] otx3_core}, but taking the hole-level G-control
  \<open>b1x_triG (D\<^sub>\<infinity> aLo) a' aHi\<close> DIRECTLY (as \<open>tri0\<close>) instead of deriving it from
  a \<open>setle\<close> via @{thm [source] otx3_setle_triG}.  This is exactly the r55
  \<open>otx3_core\<close> proof with the single \<open>otx3_setle_triG[OF setle]\<close> step replaced
  by the supplied \<open>tri0\<close> (the fixed hole cores \<open>aLo,a',aHi\<close> are invariant across
  the context descent, so \<open>tri0\<close> threads unchanged).  Needed because the
  condIII/IV body-level \<open>setle\<close> \<open>G\<^sub>u A\<^sub>0 \<preceq> insert X\<^sub>0 (G\<^sub>u X\<^sub>0)\<close> is FALSE while its
  weaker G-control \<open>tri0\<close> is TRUE (STEP-0).\<close>

lemma otx3_core_tri:
  "flatBT tLo = s @ flatBP (DB (enat h) aLo) @ b \<Longrightarrow>
   flatBT t' = s @ flatBP (DB (enat h) a') @ b \<Longrightarrow>
   flatBT tHi = s @ flatBP (DB (enat h) aHi) @ b \<Longrightarrow>
   \<forall>x \<in> set b. x = RP \<Longrightarrow>
   isOT_BT tLo \<Longrightarrow> isOT_BT tHi \<Longrightarrow>
   isOT_BP (DB (enat h) a') \<Longrightarrow>
   leBT aLo a' \<Longrightarrow> leBT a' aHi \<Longrightarrow>
   b1x_triG (Dpt \<infinity> aLo) a' aHi \<Longrightarrow>
   isOT_BT t' \<and> leBT tLo t' \<and> leBT t' tHi \<and> b1x_triG (Dpt \<infinity> tLo) t' tHi"
proof (induction t' arbitrary: tLo tHi s b rule: measure_induct_rule[where f=size])
  case (less t')
  note P = less.prems
  from otx2_align3[OF P(1) P(2) P(3) P(4)]
  show ?case
  proof (elim disjE exE conjE)
    \<comment> \<open>case A: the cores are the last top-level components over a shared \<open>qs\<close>\<close>
    fix qs
    assume TLo: "tLo = Trm (qs @ [DB (enat h) aLo])"
      and T': "t' = Trm (qs @ [DB (enat h) a'])"
      and THi: "tHi = Trm (qs @ [DB (enat h) aHi])"
    have LoOT': "isOT_BT (Trm (qs @ [DB (enat h) aLo]))" using P(5) TLo by simp
    have HiOT': "isOT_BT (Trm (qs @ [DB (enat h) aHi]))" using P(6) THi by simp
    show "isOT_BT t' \<and> leBT tLo t' \<and> leBT t' tHi \<and> b1x_triG (Dpt \<infinity> tLo) t' tHi"
      unfolding TLo T' THi
      by (rule otx3_level[OF LoOT' HiOT' P(7) P(8) P(9) P(10)])
  next
    \<comment> \<open>case B: descend through a shared last component into aligned bodies\<close>
    fix qs w lbLo lb' lbHi sc bc
    assume TLo: "tLo = Trm (qs @ [DB w lbLo])"
      and T': "t' = Trm (qs @ [DB w lb'])"
      and THi: "tHi = Trm (qs @ [DB w lbHi])"
      and F1: "flatBT lbLo = sc @ flatBP (DB (enat h) aLo) @ bc"
      and F2: "flatBT lb' = sc @ flatBP (DB (enat h) a') @ bc"
      and F3: "flatBT lbHi = sc @ flatBP (DB (enat h) aHi) @ bc"
      and BC: "\<forall>x \<in> set bc. x = RP"
    have LoOT': "isOT_BT (Trm (qs @ [DB w lbLo]))" using P(5) TLo by simp
    have HiOT': "isOT_BT (Trm (qs @ [DB w lbHi]))" using P(6) THi by simp
    have loP: "isOT_BP (DB w lbLo)" using LoOT' by simp
    have hiP: "isOT_BP (DB w lbHi)" using HiOT' by simp
    have loBT: "isOT_BT lbLo" using loP by simp
    have hiBT: "isOT_BT lbHi" using hiP by simp
    have pin: "DB w lb' \<in> set (qs @ [DB w lb'])" by simp
    have szp: "size (DB w lb') \<le> size_list size (qs @ [DB w lb'])"
      by (rule size_list_estimation'[OF pin order_refl])
    have sz: "size lb' < size t'" using szp T' by simp
    from less.IH[OF sz F1 F2 F3 BC loBT hiBT P(7) P(8) P(9) P(10)]
    have ih1: "isOT_BT lb'" and ih2: "leBT lbLo lb'" and ih3: "leBT lb' lbHi"
      and ih4: "b1x_triG (Dpt \<infinity> lbLo) lb' lbHi" by blast+
    have pOT: "isOT_BP (DB w lb')"
      by (rule otx3_pOT[OF loP hiP ih1 ih2 ih3 ih4])
    show "isOT_BT t' \<and> leBT tLo t' \<and> leBT t' tHi \<and> b1x_triG (Dpt \<infinity> tLo) t' tHi"
      unfolding TLo T' THi
      by (rule otx3_level[OF LoOT' HiOT' pOT ih2 ih3 ih4])
  qed
qed

text \<open>@{text ot1_OTA1_from_bricks}: the OTA1 conclusion \<open>isOT_BP (D\<^bsub>e\<^sub>3\<^esub> A\<^sub>1)\<close>
  packaged as ONE application of @{thm [source] otx3_core_tri} (giving \<open>isOT_BT
  A\<^sub>1\<close> and the lifted G-control \<open>A\<^sub>1 \<triangleleft>\<^bsub>D\<^sub>\<infinity>X\<^sub>1\<^esub> X\<^sub>2\<close>) followed by
  @{thm [source] otx3_pOT} at head \<open>e\<^sub>3\<close>.  This reduces the census assumption
  \<open>OTA1\<close> to exactly the reusable brick set
  \<open>{donor-OT (X\<^sub>1,X\<^sub>2 and their D\<^bsub>e\<^sub>3\<^esub>-principals), newOT_body isOT_BP(D\<^bsub>ub\<^esub> A\<^sub>0),
    base0/base1, tri0}\<close>.  \<open>X\<^sub>0 = D\<^bsub>ub\<^esub>0\<close>, \<open>X\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 X\<^sub>0\<close>,
  \<open>X\<^sub>2 = d4vx_ins s\<^sub>0 ub b\<^sub>0 X\<^sub>1\<close>, \<open>A\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 A\<^sub>0\<close>.\<close>

lemma ot1_OTA1_from_bricks:
  fixes s0 b0 :: "Sym list" and ub e3 :: nat and X0 A0 X1 X2 A1 :: BT
  assumes fX1: "flatBT X1 = s0 @ flatBP (DB (enat ub) X0) @ b0"
    and fA1: "flatBT A1 = s0 @ flatBP (DB (enat ub) A0) @ b0"
    and fX2: "flatBT X2 = s0 @ flatBP (DB (enat ub) X1) @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and X1OT: "isOT_BT X1" and X2OT: "isOT_BT X2"
    and loPe: "isOT_BP (DB (enat e3) X1)"
    and hiPe: "isOT_BP (DB (enat e3) X2)"
    and nub: "isOT_BP (DB (enat ub) A0)"
    and o1: "leBT X0 A0" and o2: "leBT A0 X1"
    and tri0: "b1x_triG (Dpt \<infinity> X0) A0 X1"
  shows "isOT_BP (DB (enat e3) A1)"
proof -
  from otx3_core_tri[OF fX1 fA1 fX2 b0RP X1OT X2OT nub o1 o2 tri0]
  have A1OT: "isOT_BT A1" and ordlo: "leBT X1 A1" and ordhi: "leBT A1 X2"
    and triA: "b1x_triG (Dpt \<infinity> X1) A1 X2" by blast+
  show ?thesis by (rule otx3_pOT[OF loPe hiPe A1OT ordlo ordhi triA])
qed



(* =================================================================== *)
(* r56-IVCORNER (prefix ot2_): the two condIV corner residuals of      *)
(* oi5_OTint_condIV discharged as HYPOTHESIS-FREE lemmas, so that       *)
(* oi5_termination_census loses its IVADMEQ / IVNP assumptions.         *)
(*                                                                      *)
(* Empirical (python/_r56_ivcorner_step0.py, genuine ST_PS oper-orbit): *)
(*   IVADMEQ corner (hasParent, condIV, admeq gate jm3=jm1): 24 hosts,  *)
(*     96/96 (host,n) pairs Trans(P[n]) in OT_B, 0 CEX, IH always OK.   *)
(*   IVNP corner discharged unconditionally by od4_OTpred_final.        *)
(* =================================================================== *)

section \<open>r56-IVCORNER (\<open>ot2_\<close>) --- the two condIV corner residuals\<close>

subsection \<open>\<open>IVNP\<close>: the no-parent condIV corner\<close>

text \<open>\<open>IVNP\<close> is \<open>Trans (Pred P) \<in> OT\<^bsub>B\<^esub>\<close> under condIV with \<open>\<not> hasParent P 1 (Lng
  P - 1)\<close>.  This is a pure \<open>OTpred\<close> step and needs no branch/parent structure:
  the hypothesis-free master @{thm [source] od4_OTpred_final} (front B, r55)
  already gives \<open>Trans (Pred P) \<in> OT\<^bsub>B\<^esub>\<close> for EVERY standard host with
  \<open>1 < Lng P\<close> and \<open>Trans P \<in> OT\<^bsub>B\<^esub>\<close>.  The condIV/\<open>\<not>hasParent\<close> hypotheses are
  simply discarded.\<close>

lemma ot2_IVNP:
  fixes P :: pairseq
  assumes NST: "P \<in> ST_PS" and NPT: "P \<in> PT_PS" and j1gt: "1 < Lng P - 1"
    and cIV: "transCondIV P" and nhp: "\<not> hasParent P 1 (Lng P - 1)"
    and ihOT: "Trans P \<in> OT_B"
  shows "Trans (Pred P) \<in> OT_B"
proof -
  have L: "1 < Lng P" using j1gt by linarith
  show ?thesis by (rule od4_OTpred_final[OF NST ihOT L])
qed


(* ===================================================================== *)
(* ===== r56: discharge IVNP via ot2_IVNP => census modulo 4         ===== *)
(* ===================================================================== *)

text \<open>IVNP (the condIV no-parent corner) is now closed unconditionally by
  @{thm [source] ot2_IVNP} (an instance of the r55 hypothesis-free OTpred
  master @{thm [source] od4_OTpred_final}).  Composing it into
  @{thm [source] oi6_termination_census} removes IVNP from the residual set:
  both termination pillars now hold modulo \<open>{OTA1, SETLE1, IVADMEQ, FINRC}\<close>.\<close>

theorem oi7_termination_census:
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and FINRC: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             transCondII K \<Longrightarrow> tvx_finRc K"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi6_termination_census(1)[OF OTA1 SETLE1 IVADMEQ ot2_IVNP FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi6_termination_census(2)[OF OTA1 SETLE1 IVADMEQ ot2_IVNP FINRC])
qed



(* ===== r57 OTint: tri0 engine (front A) + IVADMEQ pkg-reduction (front B) ===== *)


(* ===================================================================== *)
(* r57 OTA1 engine (front A): the FIXED-z scbext wrapper lift for         *)
(*   b1x_triG, and the trivial-base Dpt-grow principal triG.  Together    *)
(*   they build tri0 = b1x_triG (Dpt inf X0) A0 X1 from the shared-wrapper *)
(*   (fA0'/fins2) decomposition of crx_base1_of_nest / cnv_base1_of_nest. *)
(*   The naive setle route (otx3_setle_triG) is DEAD: the condIII/IV      *)
(*   body-setle G_u A0 <= insert X0 (G_u X0) is FALSE at u=0.             *)
(* ===================================================================== *)

text \<open>@{text scbext_triG}: the FIXED-\<open>z\<close> wrapper lift of a principal-level
  \<open>b1x_triG\<close> through a shared right-spine scbext context \<open>(s,b)\<close> (\<open>b\<close> all-\<open>RP\<close>).
  The hole is right-spine-pinned (@{thm [source] otx2_align3}), so each level
  is one @{thm [source] b1x_triG_Dpt} (nest) followed by one
  @{thm [source] b1x_triG_addBT} (left siblings), both keeping \<open>z\<close> fixed.
  This is the setle-free replacement of @{thm [source] otx3_setle_triG} that
  the false condIII/IV body-setle blocks.\<close>

lemma scbext_triG:
  "flatBT tLo = s @ flatBP cp @ b \<Longrightarrow>
   flatBT tHi = s @ flatBP cp' @ b \<Longrightarrow>
   (\<forall>x \<in> set b. x = RP) \<Longrightarrow>
   b1x_triG z (Trm [cp]) (Trm [cp']) \<Longrightarrow>
   b1x_triG z tLo tHi"
proof (induction tLo arbitrary: tHi s b rule: measure_induct_rule[where f=size])
  case (less tLo)
  note P = less.prems
  from otx2_align3[OF P(1) P(2) P(2) P(3)]
  show ?case
  proof (elim disjE exE conjE)
    fix qs
    assume TLo: "tLo = Trm (qs @ [cp])"
      and THi: "tHi = Trm (qs @ [cp'])"
      and T3: "tHi = Trm (qs @ [cp'])"
    have "b1x_triG z (Trm qs +\<^sub>B Trm [cp]) (Trm qs +\<^sub>B Trm [cp'])"
      by (rule b1x_triG_addBT[OF P(4)])
    thus "b1x_triG z tLo tHi" using TLo THi by simp
  next
    fix qs w lbLo lbHi lb3 sc bc
    assume TLo: "tLo = Trm (qs @ [DB w lbLo])"
      and THi: "tHi = Trm (qs @ [DB w lbHi])"
      and T3: "tHi = Trm (qs @ [DB w lb3])"
      and F1: "flatBT lbLo = sc @ flatBP cp @ bc"
      and F2: "flatBT lbHi = sc @ flatBP cp' @ bc"
      and F3: "flatBT lb3 = sc @ flatBP cp' @ bc"
      and BC: "\<forall>x \<in> set bc. x = RP"
    have pin: "DB w lbLo \<in> set (qs @ [DB w lbLo])" by simp
    have szp: "size (DB w lbLo) \<le> size_list size (qs @ [DB w lbLo])"
      by (rule size_list_estimation'[OF pin order_refl])
    have sz: "size lbLo < size tLo" using szp TLo by simp
    have ih: "b1x_triG z lbLo lbHi"
      by (rule less.IH[OF sz F1 F2 BC P(4)])
    have "b1x_triG z (Trm [DB w lbLo]) (Trm [DB w lbHi])"
      by (rule b1x_triG_Dpt[OF ih])
    hence "b1x_triG z (Trm qs +\<^sub>B Trm [DB w lbLo]) (Trm qs +\<^sub>B Trm [DB w lbHi])"
      by (rule b1x_triG_addBT)
    thus "b1x_triG z tLo tHi" using TLo THi by simp
  qed
qed

text \<open>@{text ot1_triG_grow}: the trivial-base principal growth control.
  Since \<open>G\<^sub>u 0 = {}\<close>, \<open>b1x_triG z 0 c'\<close> holds for any \<open>z, c'\<close>; lifting by
  @{thm [source] b1x_triG_addBT} (append \<open>c'\<close> after \<open>t\<^sub>2\<close>) then
  @{thm [source] b1x_triG_Dpt} (wrap at \<open>v\<close>) gives the growth control with
  \<open>z\<close> FIXED throughout.\<close>

lemma ot1_triG_grow:
  "b1x_triG z (Dpt v t2) (Dpt v (t2 +\<^sub>B c'))"
proof -
  obtain t2s where t2eq: "t2 = Trm t2s" by (cases t2)
  have base: "b1x_triG z 0\<^sub>B c'"
    by (rule b1x_triG_I) (simp add: b1x_setle_def)
  have step: "b1x_triG z t2 (t2 +\<^sub>B c')"
  proof -
    have "b1x_triG z (Trm t2s +\<^sub>B 0\<^sub>B) (Trm t2s +\<^sub>B c')"
      by (rule b1x_triG_addBT[OF base])
    thus ?thesis using t2eq by simp
  qed
  have "b1x_triG z (Trm [DB v t2]) (Trm [DB v (t2 +\<^sub>B c')])"
    by (rule b1x_triG_Dpt[OF step])
  thus ?thesis by simp
qed

text \<open>@{text crx_tri0_of_nest}: the condIII hole G-control \<open>tri0\<close>.  Same
  premises as @{thm [source] crx_base1_of_nest} (NO \<open>ltJ\<close>): it re-exposes the
  shared \<open>(u\<^sub>1,v\<^sub>1\<^sub>w)\<close> wrapper decomposition of \<open>A\<^sub>0 = D\<^bsub>tv\<^esub>(t\<^sub>2)\<close> vs
  \<open>X\<^sub>1 = D\<^bsub>tv\<^esub>(t\<^sub>2 + c')\<close> (@{text fA0'}/@{text fins2}) internal to that lemma, then
  lifts the trivial-base growth control (@{thm [source] ot1_triG_grow}) through
  the wrapper (@{thm [source] scbext_triG}).  The result holds for ANY \<open>z\<close>
  (so in particular \<open>z = D\<^sub>\<infinity> X\<^sub>0\<close>, the shape @{thm [source] otx3_pOT} consumes).\<close>

lemma crx_tri0_of_nest:
  fixes M :: pairseq and u1 v1w u2 v2 s0 b0 :: "Sym list" and z :: BT
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and cIII: "transCondIII M"
    and dP: "scb_decomp (Trans (Pred (s84x_N M)))
               (Dsym (enat (entry M 1 (s84x_jm3 M))) # u1)
               (flatBT (transC1 M)) v1w"
    and d2: "scb_decomp (Trans (s84x_N M))
               (Dsym (enat (entry M 1 (s84x_jm3 M))) # u1)
               (flatBT (transC2 M)) v1w"
    and d4c2: "scb_decomp (transC2 M) u2
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) v2"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N M))) s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
  shows "b1x_triG z (bpHeadT (Trans (Pred (s84x_N M))))
           (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
              (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
proof -
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?c = "Dpt (enat ?v1) 0\<^sub>B"
  let ?c' = "Dpt (enat ?ub) (Dpt (enat ?ub) 0\<^sub>B)"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N M)))"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  have c1sh: "transC1 M = Dpt (transV M) (transT2 M)"
    using m_8_5_scbdec_c1_shape(1,2)[OF MR MP J1pos T1] by simp
  have c2sh: "transC2 M = Dpt (transV M) (transT2 M +\<^sub>B ?c)"
    by (rule crx_c2_shape_condIII[OF cIII])
  have t2TB: "transT2 M \<in> T_B" by (rule m_8_5_scbdec_c1_shape(3)[OF MR MP J1pos T1])
  have cTB: "?c \<in> T_B" by (simp add: T_B_def)
  have cp: "\<exists>p. ?c = Trm [p]" by auto
  have c'TB: "?c' \<in> T_B" by (simp add: T_B_def)
  have c'p: "\<exists>p. ?c' = Trm [p]" by auto
  obtain w4 w4' where d4: "scb_decomp (transT2 M +\<^sub>B ?c) w4 (flatBT ?c) w4'"
    using m_7_2_add_scb_conj1[OF t2TB cTB cp] unfolding MarkedB_def by auto
  have d4': "scb_decomp (transT2 M +\<^sub>B ?c') w4 (flatBT ?c') w4'"
    by (rule m_7_2_add_scb_conj2[OF t2TB cTB cp c'TB c'p d4])
  have iptc: "isPTB_str (flatBT ?c)" by (rule isPTB_str_Dpt) simp_all
  have d5: "scb_decomp (Dpt (transV M) (transT2 M +\<^sub>B ?c))
              (Dsym (transV M) # w4) (flatBT ?c) w4'"
    by (rule scb_Dpt_lift[OF d4 iptc])
  have d5c2: "scb_decomp (transC2 M) (Dsym (transV M) # w4) (flatBT ?c) w4'"
    using d5 c2sh by simp
  have c2ne: "transC2 M \<noteq> Trm []" using c2sh by simp
  have pin2: "u2 = Dsym (transV M) # w4 \<and> v2 = w4'"
    by (rule m_7_2_scb_unique_sb[OF d4c2 d5c2 c2ne])
  have fTN: "flatBT (Trans (s84x_N M))
           = Dsym (enat ?e3) # u1 @ flatBT (transC2 M) @ v1w"
    using d2 by (simp add: scb_decomp_def)
  have fbody: "flatBT ?body = u1 @ flatBT (transC2 M) @ v1w"
    by (rule vf2x_flat_head_bpHeadT[OF fTN])
  have fc2: "flatBT (transC2 M) = u2 @ flatBT ?c @ v2"
    using d4c2 by (simp add: scb_decomp_def)
  have v1RP: "\<forall>x \<in> set v1w. x = RP" using d2 by (simp add: scb_decomp_def)
  have v2RP: "\<forall>x \<in> set v2. x = RP" using d4c2 by (simp add: scb_decomp_def)
  have b0RP': "\<forall>x \<in> set (v2 @ v1w). x = RP" using v1RP v2RP by auto
  have iptcv: "isPTB_str (flatBT ?c)" by (rule isPTB_str_Dpt) simp_all
  have fbody2: "flatBT ?body = (u1 @ u2) @ flatBT ?c @ (v2 @ v1w)"
    using fbody fc2 by simp
  have innerC: "scb_decomp ?body (u1 @ u2) (flatBT ?c) (v2 @ v1w)"
    unfolding scb_decomp_def using fbody2 iptcv b0RP' by simp
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "[Zsym] = u1 @ flatBT (transC2 M) @ v1w" using fbody z by simp
    hence "[Zsym] = u1 @ (Dsym (transV M)
             # flatBT (transT2 M +\<^sub>B ?c)) @ v1w" using c2sh by simp
    thus False by (cases u1) auto
  qed
  have pin0: "s0 = u1 @ u2 \<and> b0 = v2 @ v1w"
    by (rule m_7_2_scb_unique_sb[OF inner innerC bodyne])
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using fbody2 pin0 by simp
  have b0RP: "\<forall>x \<in> set b0. x = RP" using pin0 b0RP' by simp
  have fins: "flatBT (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))
            = s0 @ Dsym (enat ?ub) # flatBT (Dpt (enat ?ub) 0\<^sub>B) @ b0"
    by (rule d4vx_ins_flat[OF wrap b0RP])
  have ft2c': "flatBT (transT2 M +\<^sub>B ?c') = w4 @ flatBT ?c' @ w4'"
    using d4' by (simp add: scb_decomp_def)
  have fins2: "flatBT (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))
      = u1 @ flatBP (DB (transV M) (transT2 M +\<^sub>B ?c')) @ v1w"
  proof -
    have "s0 @ Dsym (enat ?ub) # flatBT (Dpt (enat ?ub) 0\<^sub>B) @ b0
        = u1 @ (u2 @ Dsym (enat ?ub) # flatBT (Dpt (enat ?ub) 0\<^sub>B) @ v2) @ v1w"
      using pin0 by simp
    also have "u2 @ Dsym (enat ?ub) # flatBT (Dpt (enat ?ub) 0\<^sub>B) @ v2
             = Dsym (transV M) # (w4 @ flatBT ?c' @ w4')"
      using pin2 by simp
    also have "\<dots> = flatBP (DB (transV M) (transT2 M +\<^sub>B ?c'))"
      using ft2c' by simp
    finally show ?thesis using fins by simp
  qed
  have fPN: "flatBT (Trans (Pred (s84x_N M)))
           = Dsym (enat ?e3) # u1 @ flatBT (transC1 M) @ v1w"
    using dP by (simp add: scb_decomp_def)
  have fA0: "flatBT ?A0 = u1 @ flatBT (transC1 M) @ v1w"
    by (rule vf2x_flat_head_bpHeadT[OF fPN])
  have fA0': "flatBT ?A0 = u1 @ flatBP (DB (transV M) (transT2 M)) @ v1w"
    using fA0 c1sh by simp
  have prin: "b1x_triG z (Trm [DB (transV M) (transT2 M)])
                         (Trm [DB (transV M) (transT2 M +\<^sub>B ?c')])"
    using ot1_triG_grow[of z "transV M" "transT2 M" ?c'] by simp
  show ?thesis by (rule scbext_triG[OF fA0' fins2 v1RP prin])
qed

text \<open>@{text ot1_triG_add}: the single-append growth control at the top level,
  \<open>b1x_triG z t (t + c')\<close>, from the trivial \<open>G\<^sub>u 0 = {}\<close> base by one
  @{thm [source] b1x_triG_addBT}.\<close>

lemma ot1_triG_add:
  "b1x_triG z t2 (t2 +\<^sub>B c')"
proof -
  obtain t2s where t2eq: "t2 = Trm t2s" by (cases t2)
  have base: "b1x_triG z 0\<^sub>B c'"
    by (rule b1x_triG_I) (simp add: b1x_setle_def)
  have "b1x_triG z (Trm t2s +\<^sub>B 0\<^sub>B) (Trm t2s +\<^sub>B c')"
    by (rule b1x_triG_addBT[OF base])
  thus ?thesis using t2eq by simp
qed

text \<open>@{text cnv_tri0_of_nest}: the condIV mirror of @{thm [source] crx_tri0_of_nest}.
  The condIV insertion grows \<open>t\<^sub>2\<close> into \<open>t\<^sub>3 + D\<^sub>w(t\<^sub>4 + D\<^bsub>ub\<^esub>(D\<^bsub>ub\<^esub> 0))\<close>
  (@{thm [source] cnv_c2_shape_condIV}); by the dichotomy the growth is either a
  top-level append (build by @{thm [source] ot1_triG_grow}) or an append INSIDE
  the nested \<open>D\<^sub>w\<close> body (build by @{thm [source] ot1_triG_add} +
  @{thm [source] b1x_triG_Dpt} + @{thm [source] b1x_triG_addBT}), both with \<open>z\<close>
  fixed; the wrapper decomposition (@{text fA0'}/@{text fins2}) is that of
  @{thm [source] cnv_base1_of_nest}, lifted by @{thm [source] scbext_triG}.\<close>

lemma cnv_tri0_of_nest:
  fixes M :: pairseq and u1 v1w u2 v2 s0 b0 :: "Sym list" and z :: BT
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and cIV: "transCondIV M"
    and dP: "scb_decomp (Trans (Pred (s84x_N M)))
               (Dsym (enat (entry M 1 (s84x_jm3 M))) # u1)
               (flatBT (transC1 M)) v1w"
    and d2: "scb_decomp (Trans (s84x_N M))
               (Dsym (enat (entry M 1 (s84x_jm3 M))) # u1)
               (flatBT (transC2 M)) v1w"
    and d4c2: "scb_decomp (transC2 M) u2
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) v2"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N M))) s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
  shows "b1x_triG z (bpHeadT (Trans (Pred (s84x_N M))))
           (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
              (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
proof -
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?w = "enat (entry M 1 (transJ0 M))"
  let ?c = "Dpt (enat ?v1) 0\<^sub>B"
  let ?cc = "Dpt (enat ?ub) (Dpt (enat ?ub) 0\<^sub>B)"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N M)))"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  have c1sh: "transC1 M = Dpt (transV M) (transT2 M)"
    using m_8_5_scbdec_c1_shape(1,2)[OF MR MP J1pos T1] by simp
  obtain t3 t4 where t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B"
    and c2full: "transC2 M = Dpt (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?c))"
    and dich: "(t3 = transT2 M \<and> t4 = transT2 M)
             \<or> transT2 M = t3 +\<^sub>B Dpt ?w t4"
    using cnv_c2_shape_condIV[OF MR MP J1pos T1 cIV] by blast
  obtain sB bB where holeU: "\<forall>c'. c' \<in> T_B \<longrightarrow> (\<exists>p. c' = Trm [p]) \<longrightarrow>
      scb_decomp (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B c')) sB (flatBT c') bB"
    using cnv_nested_hole_pair[OF t4TB, of t3 ?w] by blast
  have cTB: "?c \<in> T_B" by (simp add: T_B_def)
  have cp: "\<exists>p. ?c = Trm [p]" by auto
  have ccTB: "?cc \<in> T_B" by (simp add: T_B_def)
  have ccp: "\<exists>p. ?cc = Trm [p]" by auto
  have dB: "scb_decomp (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?c)) sB (flatBT ?c) bB"
    using holeU cTB cp by blast
  have dBcc: "scb_decomp (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc)) sB (flatBT ?cc) bB"
    using holeU ccTB ccp by blast
  have iptc: "isPTB_str (flatBT ?c)" by (rule isPTB_str_Dpt) simp_all
  have dc2can0: "scb_decomp (Dpt (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?c)))
                   (Dsym (transV M) # sB) (flatBT ?c) bB"
    by (rule scb_Dpt_lift[OF dB iptc])
  have dc2can: "scb_decomp (transC2 M) (Dsym (transV M) # sB) (flatBT ?c) bB"
    using dc2can0 c2full by simp
  have c2ne: "transC2 M \<noteq> Trm []" using c2full by simp
  have pin2: "u2 = Dsym (transV M) # sB \<and> v2 = bB"
    by (rule m_7_2_scb_unique_sb[OF d4c2 dc2can c2ne])
  have fTN: "flatBT (Trans (s84x_N M))
           = Dsym (enat ?e3) # u1 @ flatBT (transC2 M) @ v1w"
    using d2 by (simp add: scb_decomp_def)
  have fbody: "flatBT ?body = u1 @ flatBT (transC2 M) @ v1w"
    by (rule vf2x_flat_head_bpHeadT[OF fTN])
  have fc2: "flatBT (transC2 M) = u2 @ flatBT ?c @ v2"
    using d4c2 by (simp add: scb_decomp_def)
  have v1RP: "\<forall>x \<in> set v1w. x = RP" using d2 by (simp add: scb_decomp_def)
  have v2RP: "\<forall>x \<in> set v2. x = RP" using d4c2 by (simp add: scb_decomp_def)
  have b0RP': "\<forall>x \<in> set (v2 @ v1w). x = RP" using v1RP v2RP by auto
  have fbody2: "flatBT ?body = (u1 @ u2) @ flatBT ?c @ (v2 @ v1w)"
    using fbody fc2 by simp
  have innerC: "scb_decomp ?body (u1 @ u2) (flatBT ?c) (v2 @ v1w)"
    unfolding scb_decomp_def using fbody2 iptc b0RP' by simp
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "[Zsym] = u1 @ flatBT (transC2 M) @ v1w" using fbody z by simp
    hence "[Zsym] = u1 @ (Dsym (transV M)
             # flatBT (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?c))) @ v1w" using c2full by simp
    thus False by (cases u1) auto
  qed
  have pin0: "s0 = u1 @ u2 \<and> b0 = v2 @ v1w"
    by (rule m_7_2_scb_unique_sb[OF inner innerC bodyne])
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using fbody2 pin0 by simp
  have b0RP: "\<forall>x \<in> set b0. x = RP" using pin0 b0RP' by simp
  have fins: "flatBT (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))
            = s0 @ Dsym (enat ?ub) # flatBT (Dpt (enat ?ub) 0\<^sub>B) @ b0"
    by (rule d4vx_ins_flat[OF wrap b0RP])
  have fBcc: "flatBT (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc)) = sB @ flatBT ?cc @ bB"
    using dBcc by (simp add: scb_decomp_def)
  have fins2: "flatBT (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))
      = u1 @ flatBP (DB (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc))) @ v1w"
  proof -
    have "s0 @ Dsym (enat ?ub) # flatBT (Dpt (enat ?ub) 0\<^sub>B) @ b0
        = u1 @ (u2 @ Dsym (enat ?ub) # flatBT (Dpt (enat ?ub) 0\<^sub>B) @ v2) @ v1w"
      using pin0 by simp
    also have "u2 @ Dsym (enat ?ub) # flatBT (Dpt (enat ?ub) 0\<^sub>B) @ v2
             = Dsym (transV M) # (sB @ flatBT ?cc @ bB)"
      using pin2 by simp
    also have "\<dots> = flatBP (DB (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc)))"
      using fBcc by simp
    finally show ?thesis using fins by simp
  qed
  have fPN: "flatBT (Trans (Pred (s84x_N M)))
           = Dsym (enat ?e3) # u1 @ flatBT (transC1 M) @ v1w"
    using dP by (simp add: scb_decomp_def)
  have fA0: "flatBT ?A0 = u1 @ flatBT (transC1 M) @ v1w"
    by (rule vf2x_flat_head_bpHeadT[OF fPN])
  have fA0': "flatBT ?A0 = u1 @ flatBP (DB (transV M) (transT2 M)) @ v1w"
    using fA0 c1sh by simp
  have prin: "b1x_triG z (Trm [DB (transV M) (transT2 M)])
                         (Trm [DB (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc))])"
    using dich
  proof
    assume A: "t3 = transT2 M \<and> t4 = transT2 M"
    have "b1x_triG z (Dpt (transV M) (transT2 M))
            (Dpt (transV M) (transT2 M +\<^sub>B Dpt ?w (transT2 M +\<^sub>B ?cc)))"
      by (rule ot1_triG_grow[of z "transV M" "transT2 M"
            "Dpt ?w (transT2 M +\<^sub>B ?cc)"])
    thus ?thesis using A by simp
  next
    assume B: "transT2 M = t3 +\<^sub>B Dpt ?w t4"
    obtain t3s where t3eq: "t3 = Trm t3s" by (cases t3)
    have s1: "b1x_triG z t4 (t4 +\<^sub>B ?cc)" by (rule ot1_triG_add)
    have s2: "b1x_triG z (Trm [DB ?w t4]) (Trm [DB ?w (t4 +\<^sub>B ?cc)])"
      by (rule b1x_triG_Dpt[OF s1])
    have s3: "b1x_triG z (Trm t3s +\<^sub>B Trm [DB ?w t4])
                         (Trm t3s +\<^sub>B Trm [DB ?w (t4 +\<^sub>B ?cc)])"
      by (rule b1x_triG_addBT[OF s2])
    have s3': "b1x_triG z (t3 +\<^sub>B Dpt ?w t4) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc))"
      using s3 t3eq by simp
    have "b1x_triG z (Trm [DB (transV M) (t3 +\<^sub>B Dpt ?w t4)])
                     (Trm [DB (transV M) (t3 +\<^sub>B Dpt ?w (t4 +\<^sub>B ?cc))])"
      by (rule b1x_triG_Dpt[OF s3'])
    thus ?thesis using B by simp
  qed
  show ?thesis by (rule scbext_triG[OF fA0' fins2 v1RP prin])
qed



(* =================================================================== *)
(* r57-IVADMEQ (prefix ot2_): the COMMON standard-condIV admeq OT step  *)
(*   Trans(P[n]) in OT_B, via the CLEAN transT2 hole c4cx2 mnform.      *)
(*                                                                      *)
(* The GENERIC oi5_OTint_IIIIV_hp needs ltJ (jm3 < jm1), FALSE at admeq *)
(* (jm3 = jm1).  We mirror its transport (oix_transportD[OF             *)
(* otx3_transport ...]) on the ltJ-FREE admeq mnform                    *)
(* c4cx2_condIV_mnform_of_slice: at the SHARED (s1,b1) surgery position, *)
(* head e3 = M_{1,jm3}, the M[m] core is the FULL d4vx_core tower with   *)
(* base transT2 M, SANDWICHED between the two [Buc1]-closure donors      *)
(* operB(numBT k) (base X0 = D_ub 0) at depths k and (k+1).  Reduces the *)
(* admeq OT step to the two CLEAN d4vx_core tower facts NEWOT/SETLE for  *)
(* the transT2 hole (full depth), plus the host-only mnform package.    *)
(* =================================================================== *)

section \<open>r57-IVADMEQ (\<open>ot2_\<close>) --- the standard-condIV admeq OT step\<close>

subsection \<open>The full-depth OT transport reduction (condV-style, at head \<open>e\<^sub>3\<close>)\<close>

text \<open>The admeq analogue of @{thm [source] oi5_OTint_IIIIV_hp}, but with the
  transport done as ONE substitution of the FULL inner \<open>d4vx_core\<close> tower at head
  \<open>e\<^sub>3\<close> (condV-style, no \<open>k\<close>-dispatch): \<open>Trans (M[Suc k])\<close> reads
  \<open>s\<^sub>1 D\<^bsub>e\<^sub>3\<^esub>(A\<^sub>k) b\<^sub>1\<close> with \<open>A\<^sub>k = d4vx_core s\<^sub>0 ub b\<^sub>0 (transT2 M) k\<close>, sandwiched
  between the [Buc1]-closure donors \<open>W\<^sub>k \<le> A\<^sub>k \<le> W\<^bsub>k+1\<^esub>\<close>
  (\<open>W\<^sub>n = d4vx_core s\<^sub>0 ub b\<^sub>0 (D\<^bsub>ub\<^esub> 0) n\<close>, the closed forms of
  \<open>operB (Trans M) (numBT n)\<close>) at the SAME hole.  The transport
  @{thm [source] otx3_transport} preserves \<open>isOT\<close> from the substituted core being
  an OT principal (\<open>NEWOT\<close>) and its \<open>G\<^sub>u\<close>-sets dominated by the low donor core
  (\<open>SETLE\<close>).  The interleave orders \<open>W\<^sub>k < A\<^sub>k < W\<^bsub>k+1\<^esub>\<close> come from
  @{thm [source] c4cx_d4vx_core_interleave} on the two base facts \<open>base0\<close>/\<open>base1\<close>;
  the donor closed forms from @{thm [source] d13x_fseq_condIII}.\<close>

lemma ot2_IVADMEQ_of_pkg:
  fixes M :: pairseq and m :: nat and s0 s1 b0 b1 :: "Sym list" and body :: BT
  assumes MST: "M \<in> ST_PS"
    and mgt: "1 < m"
    and ihOT: "Trans M \<in> OT_B"
    and t2TB: "transT2 M \<in> T_B"
    and uv: "entry M 1 (s84x_jm3 M) < entry M 1 (Lng M - 1)"
    and bodyT: "body \<in> T_B"
    and bodyne: "body \<noteq> Trm []"
    and dbbody: "domB body = TBv (enat (entry M 1 (Lng M - 1) - 1))"
    and inner: "scb_decomp body s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
    and k1: "scb_kind1 (Trans M) s1
               (flatBT (Dpt (enat (entry M 1 (s84x_jm3 M))) body)) b1"
    and mnform: "\<And>m. 1 \<le> m \<Longrightarrow>
        flatBT (Trans ((M::pairseq)[m]))
          = s1 @ Dsym (enat (entry M 1 (s84x_jm3 M)))
              # flatBT (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                         (transT2 M) (m - 1))
              @ b1"
    and base0: "lessBT (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) (transT2 M)"
    and base1: "lessBT (transT2 M)
                  (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
                     0\<^sub>B)"
    and NEWOT: "\<And>k. isOT_BP (DB (enat (entry M 1 (s84x_jm3 M)))
                    (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0 (transT2 M) k))"
    and SETLE: "\<And>k u. b1x_setle
        (GBT u (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0 (transT2 M) k))
        (insert (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                  0\<^sub>B k)
                (GBT u (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                          0\<^sub>B k)))"
  shows "Trans ((M::pairseq)[m]) \<in> OT_B"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?X0 = "Dpt (enat ?ub) 0\<^sub>B"
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have TT: "Trans M \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF MR])
  have wrap: "flatBT body
      = s0 @ flatBP (DB (enat (entry M 1 (Lng M - 1))) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have b0RP: "\<forall>x \<in> set b0. x = RP" using inner by (simp add: scb_decomp_def)
  have dTM: "scb_decomp (Trans M) s1 (flatBT (Dpt (enat ?e3) body)) b1"
    using k1 by (simp add: scb_kind1_def)
  have b1RP: "\<forall>x \<in> set b1. x = RP" using dTM by (simp add: scb_decomp_def)
  have ZTB: "(0\<^sub>B :: BT) \<in> T_B" by (simp add: T_B_def)
  \<comment> \<open>tower \<open>T\<^bsub>B\<^esub>\<close>-membership\<close>
  have ATB: "\<And>k. d4vx_core s0 ?ub b0 (transT2 M) k \<in> T_B"
    by (rule oi5_d4vx_core_TB[OF wrap b0RP bodyT t2TB])
  have WTB: "\<And>k. d4vx_core s0 ?ub b0 0\<^sub>B k \<in> T_B"
    by (rule oi5_d4vx_core_TB[OF wrap b0RP bodyT ZTB])
  \<comment> \<open>donor closed forms and flats.  r72: the operB core is the \<open>0\<^sub>B\<close>-seeded tower,
      ONE LEVEL DEEPER --- \<open>operB (numBT n)\<close> has core \<open>W\<^bsub>n+1\<^esub>\<close>, not \<open>W\<^sub>n\<close>.\<close>
  have fseq: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate (n + 1) (s0 @ [Dsym (enat ?ub)]))
           @ [Zsym]
           @ concat (replicate (n + 1) b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbody bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 0\<^sub>B n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT (0\<^sub>B :: BT) @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fWn: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))) @ b1"
  proof -
    fix n :: nat
    have A: "flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))
        = concat (replicate (Suc n) (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (Suc n) b0)"
      using Xflat[of "Suc n"] by (simp del: d4vx_core.simps)
    show "flatBT (operB (Trans M) (numBT n))
        = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))) @ b1"
      using fseq[of n] A by (simp del: d4vx_core.simps)
  qed
  \<comment> \<open>index bookkeeping\<close>
  obtain k where mk: "m = Suc k" using mgt by (cases m) auto
  have k1n: "1 \<le> k" using mgt mk by simp
  have Sk: "Suc (m - 1) = m" using mgt by simp
  have SkL: "Suc (m - 2) = m - 1" using mgt by simp
  have fMm: "flatBT (Trans ((M::pairseq)[m]))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 (transT2 M) (m - 1))) @ b1"
    using mnform[of m] mgt by simp
  \<comment> \<open>the three aligned scb-decompositions at \<open>(s\<^sub>1, b\<^sub>1)\<close>, cores at head \<open>e\<^sub>3\<close>;
      donors are \<open>numBT (m-2)\<close> (core \<open>W\<^bsub>m-1\<^esub>\<close>) and \<open>numBT (m-1)\<close> (core \<open>W\<^sub>m\<close>)\<close>
  let ?A = "d4vx_core s0 ?ub b0 (transT2 M) (m - 1)"
  let ?WL = "d4vx_core s0 ?ub b0 0\<^sub>B (m - 1)"
  let ?WH = "d4vx_core s0 ?ub b0 0\<^sub>B m"
  have ourdec: "scb_decomp (Trans ((M::pairseq)[m])) s1
                  (flatBT (Dpt (enat ?e3) ?A)) b1"
    unfolding scb_decomp_def
    using fMm b1RP isPTB_str_Dpt[of "enat ?e3" ?A] ATB by (simp add: T_B_def)
  have lodec: "scb_decomp (operB (Trans M) (numBT (m - 2))) s1
                  (flatBT (Dpt (enat ?e3) ?WL)) b1"
    unfolding scb_decomp_def
    using fWn[of "m - 2"] SkL b1RP isPTB_str_Dpt[of "enat ?e3" ?WL] WTB
    by (simp add: T_B_def)
  have hidec: "scb_decomp (operB (Trans M) (numBT (m - 1))) s1
                  (flatBT (Dpt (enat ?e3) ?WH)) b1"
    unfolding scb_decomp_def
    using fWn[of "m - 1"] Sk b1RP isPTB_str_Dpt[of "enat ?e3" ?WH] WTB
    by (simp add: T_B_def)
  \<comment> \<open>donor OT-ness ([Buc1] 3.2 closure on the slot's own IH)\<close>
  have loOT: "isOT_BT (operB (Trans M) (numBT (m - 2)))"
    using e4x_OT_B_operB_numBT[OF ihOT, of "m - 2"] by (simp add: OT_B_def OT_def)
  have hiOT: "isOT_BT (operB (Trans M) (numBT (m - 1)))"
    using e4x_OT_B_operB_numBT[OF ihOT, of "m - 1"] by (simp add: OT_B_def OT_def)
  \<comment> \<open>interleave orders \<open>W\<^bsub>m-1\<^esub> < A\<^bsub>m-1\<^esub> < W\<^bsub>m\<^esub>\<close> (seed \<open>0\<^sub>B\<close>, \<open>base\<^sub>1\<^sup>Y\<close>)\<close>
  have base0Z: "lessBT (0\<^sub>B :: BT) (transT2 M)"
  proof -
    have "lessBT (0\<^sub>B :: BT) (Dpt (enat ?ub) 0\<^sub>B)" by simp
    thus ?thesis using base0 lessBT_trans by blast
  qed
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0Z base1, of "m - 1"]
  have ordlo: "leBT ?WL ?A" using IL by simp
  have ordhi: "leBT ?A ?WH" using IL Sk by simp
  \<comment> \<open>the two clean tower facts\<close>
  have newOT: "isOT_BP (DB (enat ?e3) ?A)" by (rule NEWOT)
  have setle: "\<And>u. b1x_setle (GBT u ?A) (insert ?WL (GBT u ?WL))"
    by (rule SETLE)
  \<comment> \<open>transport\<close>
  have isot: "isOT_BT (Trans ((M::pairseq)[m]))"
    by (rule oix_transportD[OF otx3_transport lodec ourdec hidec loOT hiOT
          newOT ordlo ordhi setle])
  \<comment> \<open>\<open>T\<^bsub>B\<^esub>\<close> side and assembly\<close>
  have m1: "1 \<le> m" using mgt by simp
  have NmST: "(M::pairseq)[m] \<in> ST_PS" by (rule ST_PS.oper[OF MST m1])
  have NmRT: "(M::pairseq)[m] \<in> RT_PS"
    using NmST m_6_7_ST_PS_subseteq_RT_PS by blast
  have "Trans ((M::pairseq)[m]) \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF NmRT])
  thus ?thesis using isot by (simp add: OT_B_def OT_def)
qed

subsection \<open>Host-only discharge of the mnform package (\<open>d1/d2/d3/HB\<close> residual)\<close>

text \<open>The mnform package of @{thm [source] ot2_IVADMEQ_of_pkg} is discharged
  host-only exactly as @{thm [source] c4dx_condIV_exchange_assembled} discharges
  the descent package: the \<open>mnform\<close> and inner \<open>(s\<^sub>0,b\<^sub>0)\<close> from
  @{thm [source] c4cx2_condIV_mnform_of_slice}, the producer data \<open>uv\<close>/\<open>bodyT\<close>/
  \<open>bodyne\<close>/\<open>dbbody\<close>/\<open>k1\<close> from the \<open>c4dx_condIV_*\<close> bricks, \<open>base0\<close> from the
  component bound \<open>HB\<close> via @{thm [source] s85b_complb_lessBT}, and \<open>base1\<close> from
  @{thm [source] c4dx_condIV_base1}.  So the admeq OT step reduces to the exact
  residual set \<open>{d1,d2,d3,HB,NEWOT,SETLE}\<close>: \<open>d1/d2/d3\<close> are the condition-agnostic
  terminal-slice transports (dischargeable from the r34 \<open>noguard\<close>
  \<open>\<not>(j\<^sub>-\<^sub>3<j\<^sub>-\<^sub>2)\<close> + \<open>regSP\<^sub>R\<close>, an open condIV-geometry residual), \<open>HB\<close> the
  \<open>t\<^sub>2\<close>-component bound, and \<open>NEWOT\<close>/\<open>SETLE\<close> the two clean \<open>transT2\<close>-tower facts.\<close>

lemma ot2_IVADMEQ_mod:
  fixes M :: pairseq and m :: nat and s1' b1' :: "Sym list"
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and cIV: "transCondIV M"
    and admeq: "Adm M (s84x_jm2 M) = transJm1 M"
    and ihOT: "Trans M \<in> OT_B"
    and mgt: "1 < m"
    and d1: "scb_decomp (transC2 M)
               (Dsym (enat (entry M 1 (transJm1 M))) # s1')
               (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b1'"
    and d2: "scb_decomp (Trans (s84x_Np M))
               (Dsym (enat (entry M 1 (s84x_jm2 M))) # s1')
               (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b1'"
    and d3: "Trans (Pred (s84x_Np M))
               = Dpt (enat (entry M 1 (s84x_jm2 M))) (transT2 M)"
    and HB: "\<forall>c \<in> set (PB (transT2 M)).
               leBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B) c"
    and NEWOT: "\<And>s0 b0 k. scb_decomp (bpHeadT (transC2 M)) s0
          (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
          isOT_BP (DB (enat (entry M 1 (s84x_jm3 M)))
                    (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0 (transT2 M) k))"
    and SETLE: "\<And>s0 b0 k u. scb_decomp (bpHeadT (transC2 M)) s0
          (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
          b1x_setle
            (GBT u (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0 (transT2 M) k))
            (insert (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                      0\<^sub>B k)
                    (GBT u (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                              0\<^sub>B k)))"
  shows "Trans ((M::pairseq)[m]) \<in> OT_B"
proof -
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have nVI: "\<not> transCondVI M" using c4dx_condIV_excl(4)[OF cIV] .
  have T1: "transT1 M \<noteq> 0\<^sub>B"
    using s84d_L4_regime[OF MST MPT hp nVI] by simp
  have J1pos: "transJ1 M > 0" using j1gt by (simp add: transJ1_def)
  have branch: "transCondIII M \<or> transCondIV M" using cIV by blast
  have jm2ltj0: "s84x_jm2 M < transJ0 M"
    by (rule m_8_4_oper_props_1(1)[OF MST MPT hp j1gt branch])
  have reg: "s84x_jm2 M < transJ0 M \<or> adm M (transJ0 M)" using jm2ltj0 by blast
  \<comment> \<open>mnform + inner \<open>(s\<^sub>0,b\<^sub>0)\<close> from the slice route\<close>
  obtain s0 b0 where
    inner: "scb_decomp (bpHeadT (transC2 M)) s0
              (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
    and MN: "\<forall>m. 1 \<le> m \<longrightarrow> flatBT (Trans ((M::pairseq)[m]))
         = s84x_s1 M @ Dsym (enat (entry M 1 (s84x_jm3 M)))
             # flatBT (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                        (transT2 M) (m - 1))
             @ s84x_b1 M"
    using c4cx2_condIV_mnform_of_slice[OF MST MPT hp cIV reg admeq d1 d2 d3]
    by blast
  have mn: "\<And>m. 1 \<le> m \<Longrightarrow> flatBT (Trans ((M::pairseq)[m]))
         = s84x_s1 M @ Dsym (enat (entry M 1 (s84x_jm3 M)))
             # flatBT (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                        (transT2 M) (m - 1))
             @ s84x_b1 M"
    using MN by blast
  \<comment> \<open>producer data\<close>
  have uv: "entry M 1 (s84x_jm3 M) < entry M 1 (Lng M - 1)" by (rule c4dx_uv[OF hp])
  have t2TB: "transT2 M \<in> T_B" by (rule m_8_5_scbdec_c1_shape(3)[OF MR MPT J1pos T1])
  have bodyT: "bpHeadT (transC2 M) \<in> T_B"
  proof -
    obtain t3 t4 where t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B"
      and body: "bpHeadT (transC2 M)
          = t3 +\<^sub>B Dpt (enat (entry M 1 (transJ0 M)))
               (t4 +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
      using c4dx_condIV_c2body_shape[OF MR MPT J1pos T1 cIV] by blast
    obtain "as" where "t3 = Trm as" by (cases t3)
    moreover obtain bs where "t4 = Trm bs" by (cases t4)
    ultimately show ?thesis using body t3TB t4TB by (auto simp: T_B_def)
  qed
  have bodyne: "bpHeadT (transC2 M) \<noteq> Trm []" by (rule bpHeadT_transC2_nonzero)
  have dbbody: "domB (bpHeadT (transC2 M))
      = TBv (enat (entry M 1 (Lng M - 1) - 1))"
    by (rule c4dx_condIV_dbbody[OF MR MPT J1pos T1 cIV])
  have k1: "scb_kind1 (Trans M) (s84x_s1 M)
        (flatBT (Dpt (enat (entry M 1 (s84x_jm3 M))) (bpHeadT (transC2 M))))
        (s84x_b1 M)"
    by (rule c4dx_condIV_k1[OF MST MPT hp cIV admeq])
  \<comment> \<open>interleave bases\<close>
  have cond24: "transCondII M \<or> transCondIV M" using cIV by blast
  have t2ne: "transT2 M \<noteq> 0\<^sub>B"
    by (rule m_7_3_t2_nonzero_condIIorIV[OF MR MPT J1pos T1 cond24])
  have v1pos: "0 < entry M 1 (Lng M - 1)" using cIV by (simp add: transCondIV_def)
  have ubv1: "entry M 1 (Lng M - 1) - 1 < entry M 1 (Lng M - 1)" using v1pos by simp
  have base0: "lessBT (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) (transT2 M)"
    by (rule s85b_complb_lessBT[OF ubv1 t2ne HB])
  have base1: "lessBT (transT2 M)
      (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
         0\<^sub>B)"
    by (rule oy1_base1Y_t2[OF MR MPT J1pos T1 cIV inner])
  \<comment> \<open>discharge the two tower facts against this inner scb, then transport\<close>
  show ?thesis
    by (rule ot2_IVADMEQ_of_pkg[OF MST mgt ihOT t2TB uv bodyT bodyne dbbody
          inner k1 mn base0 base1 NEWOT[OF inner] SETLE[OF inner]])
qed

subsection \<open>Surgery \<open>\<rightarrow>\<close> nested \<open>+\<^sub>B\<close>: the \<open>d4vx_ins\<close> hole is a CLEAN body substitution\<close>

text \<open>The foundational rewrite behind the engines: on the condIV \<open>c\<^sub>2\<close>-body shape
  \<open>t\<^sub>3 +\<^sub>B D\<^bsub>jp\<^esub>(t\<^sub>4 +\<^sub>B D\<^bsub>hh\<^esub> 0)\<close> (@{thm [source] c4dx_condIV_c2body_shape}), one
  \<open>d4vx_ins\<close> surgery at the (nested, rightmost) \<open>D\<^bsub>hh\<^esub> 0\<close> hole is EXACTLY the clean
  body substitution \<open>t\<^sub>3 +\<^sub>B D\<^bsub>jp\<^esub>(t\<^sub>4 +\<^sub>B D\<^bsub>ub\<^esub> X)\<close> --- i.e. the surgery term is a
  nested \<open>+\<^sub>B\<close>/\<open>D\<close> expression, amenable to the \<open>+\<^sub>B\<close> \<open>G\<close>-calculus.  This is the
  \<open>X\<close>-abstracted @{thm [source] c4dx_condIV_base1} \<open>insEq\<close> step: the flat of
  \<open>STRUCT = t\<^sub>3 +\<^sub>B D\<^bsub>jp\<^esub>(t\<^sub>4 +\<^sub>B D\<^bsub>ub\<^esub> X)\<close> equals \<open>s\<^sub>0 (D\<^bsub>ub\<^esub> X) b\<^sub>0\<close> (by the shared
  trailing-principal wrapper of \<open>t\<^sub>4 +\<^sub>B \<cdot>\<close>, scb-uniqueness of \<open>(s\<^sub>0,b\<^sub>0)\<close>), so
  \<open>d4vx_ins s\<^sub>0 ub b\<^sub>0 X = unflatBT (flatBT STRUCT) = STRUCT\<close>.\<close>

lemma ot2_dins_addBT_of_shape:
  fixes s0 b0 :: "Sym list" and t3 t4 X :: BT and jpe hh ub :: nat
  assumes t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B" and XTB: "X \<in> T_B"
    and inner: "scb_decomp (t3 +\<^sub>B Dpt (enat jpe) (t4 +\<^sub>B Dpt (enat hh) 0\<^sub>B)) s0
                  (flatBT (Dpt (enat hh) 0\<^sub>B)) b0"
  shows "d4vx_ins s0 ub b0 X
           = t3 +\<^sub>B Dpt (enat jpe) (t4 +\<^sub>B Dpt (enat ub) X)"
proof -
  let ?c = "Dpt (enat hh) 0\<^sub>B"
  let ?cX = "Dpt (enat ub) X"
  have cTB: "?c \<in> T_B" by (simp add: T_B_def)
  have cp: "\<exists>p. ?c = Trm [p]" by auto
  have cXTB: "?cX \<in> T_B"
  proof -
    obtain xs where xe: "X = Trm xs" by (cases X)
    have "dfree_BT (Trm [DB (enat ub) (Trm xs)])"
      using XTB xe by (auto simp: T_B_def)
    thus ?thesis using xe by (simp add: T_B_def)
  qed
  have cXp: "\<exists>p. ?cX = Trm [p]" by auto
  have dfX: "dfree_BT X" using XTB by (simp add: T_B_def)
  obtain w4 w4' where d4: "scb_decomp (t4 +\<^sub>B ?c) w4 (flatBT ?c) w4'"
    using m_7_2_add_scb_conj1[OF t4TB cTB cp] unfolding MarkedB_def by auto
  have d4X: "scb_decomp (t4 +\<^sub>B ?cX) w4 (flatBT ?cX) w4'"
    by (rule m_7_2_add_scb_conj2[OF t4TB cTB cp cXTB cXp d4])
  have iptc: "isPTB_str (flatBT ?c)" by (rule isPTB_str_Dpt) simp_all
  have iptcX: "isPTB_str (flatBT ?cX)" by (rule isPTB_str_Dpt[OF _ dfX]) simp
  have d5: "scb_decomp (Dpt (enat jpe) (t4 +\<^sub>B ?c))
              (Dsym (enat jpe) # w4) (flatBT ?c) w4'"
    by (rule scb_Dpt_lift[OF d4 iptc])
  have d5X: "scb_decomp (Dpt (enat jpe) (t4 +\<^sub>B ?cX))
              (Dsym (enat jpe) # w4) (flatBT ?cX) w4'"
    by (rule scb_Dpt_lift[OF d4X iptcX])
  have bodyne: "t3 +\<^sub>B Dpt (enat jpe) (t4 +\<^sub>B ?c) \<noteq> Trm []" by (cases t3) auto
  define STRUCT where "STRUCT = t3 +\<^sub>B Dpt (enat jpe) (t4 +\<^sub>B ?cX)"
  have flatSTRUCT: "flatBT STRUCT = s0 @ flatBT ?cX @ b0"
  proof (cases "t3 = 0\<^sub>B")
    case True
    have bA: "t3 +\<^sub>B Dpt (enat jpe) (t4 +\<^sub>B ?c) = Dpt (enat jpe) (t4 +\<^sub>B ?c)"
      using True by simp
    have DA: "scb_decomp (t3 +\<^sub>B Dpt (enat jpe) (t4 +\<^sub>B ?c))
                (Dsym (enat jpe) # w4) (flatBT ?c) w4'"
      using d5 bA by simp
    have pin: "Dsym (enat jpe) # w4 = s0 \<and> w4' = b0"
      by (rule m_7_2_scb_unique_sb[OF DA inner bodyne])
    have SA: "STRUCT = Dpt (enat jpe) (t4 +\<^sub>B ?cX)"
      using STRUCT_def True by simp
    show ?thesis using d5X SA pin by (simp add: scb_decomp_def)
  next
    case False
    have X1: "length (untrm (Dpt (enat jpe) (t4 +\<^sub>B ?c))) = 1" by simp
    have X1': "length (untrm (Dpt (enat jpe) (t4 +\<^sub>B ?cX))) = 1" by simp
    have Yne: "untrm t3 \<noteq> []" using False by (cases t3) auto
    have DA: "scb_decomp (t3 +\<^sub>B Dpt (enat jpe) (t4 +\<^sub>B ?c))
                (liftS t3 (Dsym (enat jpe) # w4)) (flatBT ?c) (w4' @ [RP])"
      using scb_addBT_left[OF d5 X1 Yne] by simp
    have pin: "liftS t3 (Dsym (enat jpe) # w4) = s0 \<and> w4' @ [RP] = b0"
      by (rule m_7_2_scb_unique_sb[OF DA inner bodyne])
    have DA': "scb_decomp STRUCT
                (liftS t3 (Dsym (enat jpe) # w4)) (flatBT ?cX) (w4' @ [RP])"
      using scb_addBT_left[OF d5X X1' Yne] STRUCT_def by simp
    show ?thesis using DA' pin by (simp add: scb_decomp_def)
  qed
  have insEq: "d4vx_ins s0 ub b0 X = STRUCT"
  proof -
    have "d4vx_ins s0 ub b0 X = unflatBT (s0 @ flatBT ?cX @ b0)"
      by (simp add: d4vx_ins_def)
    also have "\<dots> = unflatBT (flatBT STRUCT)" using flatSTRUCT by simp
    also have "\<dots> = STRUCT" by (rule unflatBT_flat)
    finally show ?thesis .
  qed
  show ?thesis using insEq STRUCT_def by simp
qed


(* ===== r58 OTint: ltJ-rethread census oi8_ + OTA1 reduced to A0OT (front A) + IVADMEQ NEWOT engine (front B) ===== *)



(* ===================================================================== *)
(* ===== r58 ltJ-THREADED census chain (prefix oi8_): the census   ===== *)
(* =====   demands OTA1/SETLE1 only UNDER ltJ (s84x_jm3 P<transJm1 P). ==== *)
(* =====   condIII always has ltJ; condIV-not-admeq derives it via    ==== *)
(* =====   cnv_condIV_ltJ; condIV-admeq->IVADMEQ; no-parent->IVNP.     ==== *)
(* =====   Verbatim copies of oi5_OTint_IIIIV_hp/condIII/condIV with   ==== *)
(* =====   the ltJ premise added to OTA1/SETLE1 and passed at the two  ==== *)
(* =====   application sites; then a single oi8_termination_census.    ==== *)
(* ===================================================================== *)

lemma oi8_OTint_IIIIV_hp:
  fixes N :: pairseq and m :: nat
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and ihOT: "Trans N \<in> OT_B" and mgt: "1 < m"
  shows "Trans ((N::pairseq)[m]) \<in> OT_B"
proof -
  let ?e3 = "entry N 1 (s84x_jm3 N)"
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  have MR: "N \<in> RT_PS" using NST m_6_7_ST_PS_subseteq_RT_PS by blast
  \<comment> \<open>package and regime\<close>
  obtain s0 b0 s1 b1 where
    b0RP: "\<forall>x \<in> set b0. x = RP" and b1RP: "\<forall>x \<in> set b1. x = RP"
    and inner: "scb_decomp ?body s0 (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0"
    and k1: "scb_kind1 (Trans N) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    and mn: "\<forall>m. 1 \<le> m \<longrightarrow>
        flatBT (Trans ((N::pairseq)[m]))
          = s1 @ Dsym (enat ?e3)
              # flatBT (d4vx_core s0 ?ub b0 ?A0 (m - 1)) @ b1"
    and base0: "lessBT (Dpt (enat ?ub) 0\<^sub>B) ?A0"
    and base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 0\<^sub>B)"
    and A0TB: "?A0 \<in> T_B"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  note regime = oi5_regime[OF NST NPT hp j1gt branch]
  have uv: "?e3 < ?v1" by (rule regime(1))
  have e3ub: "?e3 \<le> ?ub" by (rule regime(2))
  have bodyT: "?body \<in> T_B" by (rule regime(3))
  have dbbodyH: "domB ?body = TBv (enat ?ub)" by (rule regime(4))
  have TT: "Trans N \<in> T_B" by (rule regime(5))
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "flatBT ?body = s0 @ flatBT (Dpt (enat ?v1) 0\<^sub>B) @ b0"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0 @ [Dsym (enat ?v1), Zsym] @ b0" using z by simp
    thus False by (cases s0) auto
  qed
  \<comment> \<open>towers.  r72: under the CORRECTED fundamental sequence the operB core is the
      \<open>0\<^sub>B\<close>-seeded tower \<open>Y\<^sub>n = ins\<^sup>n 0\<^sub>B\<close>, ONE LEVEL DEEPER than the old \<open>X\<^sub>n = ins\<^sup>n(D\<^bsub>ub\<^esub>0)\<close>.
      \<open>X\<^sub>0/X\<^sub>1\<close> survive only as the carriers of \<open>base\<^sub>0\<close>/\<open>base\<^sub>1\<close>.\<close>
  define X0 where "X0 = Dpt (enat ?ub) 0\<^sub>B"
  define A1 where "A1 = d4vx_ins s0 ?ub b0 ?A0"
  define Y1 where "Y1 = d4vx_ins s0 ?ub b0 0\<^sub>B"
  define Y2 where "Y2 = d4vx_ins s0 ?ub b0 Y1"
  define Y3 where "Y3 = d4vx_ins s0 ?ub b0 Y2"
  have X0TB: "X0 \<in> T_B" by (simp add: X0_def T_B_def)
  have ZTB: "0\<^sub>B \<in> T_B" by (simp add: T_B_def)
  have A1TB: "A1 \<in> T_B"
    unfolding A1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT A0TB])
  have Y1TB: "Y1 \<in> T_B"
    unfolding Y1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT ZTB])
  have Y2TB: "Y2 \<in> T_B"
    unfolding Y2_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT Y1TB])
  have Y3TB: "Y3 \<in> T_B"
    unfolding Y3_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT Y2TB])
  have fA1: "flatBT A1 = s0 @ Dsym (enat ?ub) # flatBT ?A0 @ b0"
    unfolding A1_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fY1: "flatBT Y1 = s0 @ Dsym (enat ?ub) # flatBT 0\<^sub>B @ b0"
    unfolding Y1_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fY2: "flatBT Y2 = s0 @ Dsym (enat ?ub) # flatBT Y1 @ b0"
    unfolding Y2_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fY3: "flatBT Y3 = s0 @ Dsym (enat ?ub) # flatBT Y2 @ b0"
    unfolding Y3_def by (rule d4vx_ins_flat[OF wrap b0RP])
  \<comment> \<open>orders (\<open>ins\<close>-monotonicity, @{thm [source] c4cx_d4vx_ins_mono}):
      \<open>Y\<^sub>1 \<le> A\<^sub>1\<close> from \<open>0\<^sub>B < A\<^sub>0\<close> (\<open>base\<^sub>0\<close>), \<open>A\<^sub>1 \<le> Y\<^sub>3\<close> from \<open>A\<^sub>0 < Y\<^sub>1 < Y\<^sub>2\<close>
      (\<open>base\<^sub>1\<^sup>Y\<close>, r72)\<close>
  have zltA0: "lessBT 0\<^sub>B ?A0"
  proof -
    have "lessBT 0\<^sub>B X0" by (simp add: X0_def)
    thus ?thesis using base0[folded X0_def] lessBT_trans by blast
  qed
  have ordlo: "leBT Y1 A1"
    unfolding Y1_def A1_def
    using c4cx_d4vx_ins_mono[OF wrap b0RP zltA0, of ?ub] by blast
  have A0ltY1: "lessBT ?A0 Y1" using base1[folded Y1_def] .
  have zltY1: "lessBT 0\<^sub>B Y1" using zltA0 A0ltY1 lessBT_trans by blast
  have Y1ltY2: "lessBT Y1 Y2"
    unfolding Y1_def Y2_def
    using c4cx_d4vx_ins_mono[OF wrap b0RP zltY1, of ?ub]
    by (simp add: Y1_def)
  have A0ltY2: "lessBT ?A0 Y2" using A0ltY1 Y1ltY2 lessBT_trans by blast
  have ordhi: "leBT A1 Y3"
    unfolding A1_def Y3_def
    using c4cx_d4vx_ins_mono[OF wrap b0RP A0ltY2, of ?ub] by blast
  \<comment> \<open>the one-block facts (the \<open>SETLE1\<close> slot is now \<open>Y\<^sub>1\<close>-seeded)\<close>
  have newOTe3: "isOT_BP (DB (enat ?e3) A1)"
    unfolding A1_def by (rule OTA1[OF NST NPT hp j1gt branch ihOT b0RP inner ltJ])
  have newOTub: "isOT_BP (DB (enat ?ub) A1)"
  proof -
    have A1OT: "isOT_BT A1"
      and gE3: "\<forall>x \<in> GBT (enat ?e3) A1. lessBT x A1"
      using newOTe3 by simp_all
    have le: "enat ?e3 \<le> enat ?ub" using e3ub by simp
    have "GBT (enat ?ub) A1 \<subseteq> GBT (enat ?e3) A1"
      by (rule b1x_GBT_antitone[OF le])
    hence "\<forall>x \<in> GBT (enat ?ub) A1. lessBT x A1" using gE3 by blast
    thus ?thesis using A1OT by simp
  qed
  have setle: "\<And>u. b1x_setle (GBT u A1) (insert Y1 (GBT u Y1))"
    unfolding A1_def Y1_def
    by (rule SETLE1[OF NST NPT hp j1gt branch ihOT b0RP inner ltJ])
  \<comment> \<open>fseq closed form of the donors: core \<open>= Y\<^bsub>n+1\<^esub>\<close>\<close>
  have fseq: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate (n + 1) (s0 @ [Dsym (enat ?ub)]))
           @ [Zsym]
           @ concat (replicate (n + 1) b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbodyH bodyne inner k1])
  have Yflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 0\<^sub>B n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT 0\<^sub>B @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fseqY: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)) @ b1"
  proof -
    fix n :: nat
    have A: "flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))
        = concat (replicate (Suc n) (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (Suc n) b0)"
      using Yflat[of "Suc n"] by (simp del: d4vx_core.simps)
    show "flatBT (operB (Trans N) (numBT n))
        = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)) @ b1"
      using fseq[of n] A by (simp del: d4vx_core.simps)
  qed
  \<comment> \<open>donor OT-ness ([Buc1] closure on the slot's own IH)\<close>
  have donOT: "\<And>n. isOT_BT (operB (Trans N) (numBT n))"
    using e4x_OT_B_operB_numBT[OF ihOT] by (simp add: OT_B_def OT_def)
  \<comment> \<open>index bookkeeping\<close>
  obtain k where mk: "m = Suc k" using mgt by (cases m) auto
  have k1n: "1 \<le> k" using mgt mk by simp
  have mnm: "flatBT (Trans ((N::pairseq)[m]))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 ?A0 k) @ b1"
    using mn mgt mk by simp
  \<comment> \<open>the transport, one application per index regime; cores are the FIXED triple
      \<open>(Y\<^sub>1, A\<^sub>1, Y\<^sub>3)\<close> and the donors are \<open>numBT (k-1)\<close> / \<open>numBT (k+1)\<close>\<close>
  have isot: "isOT_BT (Trans ((N::pairseq)[m]))"
  proof (cases "k = 1")
    case True
    \<comment> \<open>hole = the kind-1 position itself, head \<open>e\<^sub>3\<close>; donors \<open>numBT 0\<close> / \<open>numBT 2\<close>\<close>
    have fA1c: "flatBT (d4vx_core s0 ?ub b0 ?A0 k) = flatBT A1"
      using True by (simp add: A1_def)
    have ourflat: "flatBT (Trans ((N::pairseq)[m]))
        = s1 @ flatBT (Dpt (enat ?e3) A1) @ b1"
      using mnm fA1c by simp
    have loflat: "flatBT (operB (Trans N) (numBT 0))
        = s1 @ flatBT (Dpt (enat ?e3) Y1) @ b1"
      using fseqY[of 0] by (simp add: Y1_def)
    have hiflat: "flatBT (operB (Trans N) (numBT (Suc (Suc 0))))
        = s1 @ flatBT (Dpt (enat ?e3) Y3) @ b1"
    proof -
      have "d4vx_core s0 ?ub b0 0\<^sub>B (Suc (Suc (Suc 0))) = Y3"
        by (simp add: Y1_def Y2_def Y3_def)
      thus ?thesis using fseqY[of "Suc (Suc 0)"] by simp
    qed
    have ourdec: "scb_decomp (Trans ((N::pairseq)[m])) s1
                    (flatBT (Dpt (enat ?e3) A1)) b1"
      unfolding scb_decomp_def
      using ourflat b1RP isPTB_str_Dpt[of "enat ?e3" A1] A1TB
      by (simp add: T_B_def)
    have lodec: "scb_decomp (operB (Trans N) (numBT 0)) s1
                    (flatBT (Dpt (enat ?e3) Y1)) b1"
      unfolding scb_decomp_def
      using loflat b1RP isPTB_str_Dpt[of "enat ?e3" Y1] Y1TB
      by (simp add: T_B_def)
    have hidec: "scb_decomp (operB (Trans N) (numBT (Suc (Suc 0)))) s1
                    (flatBT (Dpt (enat ?e3) Y3)) b1"
      unfolding scb_decomp_def
      using hiflat b1RP isPTB_str_Dpt[of "enat ?e3" Y3] Y3TB
      by (simp add: T_B_def)
    have "isOT_BT (Trans ((N::pairseq)[m]))"
      by (rule oix_transportD[OF otx3_transport lodec ourdec hidec
            donOT donOT newOTe3 ordlo ordhi setle])
    thus ?thesis .
  next
    case False
    obtain k' where kA: "k = Suc k'" using k1n by (cases k) auto
    have k'ne: "k' \<noteq> 0" using False kA by simp
    then obtain k2 where kB: "k' = Suc k2" by (cases k') auto
    have kk: "k = Suc (Suc k2)" using kA kB by simp
    \<comment> \<open>hole = \<open>k - 1\<close> blocks deep, head \<open>ub\<close>; donors \<open>numBT (Suc k2) = numBT (k-1)\<close>
        and \<open>numBT (Suc k) = numBT (k+1)\<close>, cores \<open>(Y\<^sub>1, A\<^sub>1, Y\<^sub>3)\<close>\<close>
    let ?blk = "s0 @ [Dsym (enat ?ub)]"
    let ?S = "s1 @ Dsym (enat ?e3) # concat (replicate k2 ?blk) @ s0"
    let ?B = "concat (replicate (Suc k2) b0) @ b1"
    have BRP: "\<forall>x \<in> set ?B. x = RP"
      using oi5_crep_RP[OF b0RP, of "Suc k2"] b1RP by auto
    \<comment> \<open>our flat at the deep hole\<close>
    have Aflat: "flatBT (d4vx_core s0 ?ub b0 ?A0 k)
        = concat (replicate k ?blk) @ flatBT ?A0 @ concat (replicate k b0)"
      by (rule d4vx_core_flat[OF wrap b0RP])
    have crepA: "concat (replicate k ?blk)
        = concat (replicate k2 ?blk) @ s0 @ [Dsym (enat ?ub)]
          @ s0 @ [Dsym (enat ?ub)]"
      using kk by (simp add: s85b_crep_comm_snoc s85b_crep_snoc s85b_crep_comm)
    have crepB: "concat (replicate k b0)
        = b0 @ concat (replicate (Suc k2) b0)"
      using kk by simp
    have ourflat: "flatBT (Trans ((N::pairseq)[m]))
        = ?S @ flatBT (Dpt (enat ?ub) A1) @ ?B"
      using mnm Aflat crepA crepB fA1 by simp
    \<comment> \<open>lo donor \<open>numBT (Suc k2) = numBT (k-1)\<close>: core \<open>Y\<^sub>1\<close> at the deep hole\<close>
    have Fk: "flatBT (operB (Trans N) (numBT (Suc k2)))
        = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 0\<^sub>B k) @ b1"
      using fseqY[of "Suc k2"] kk by (simp del: d4vx_core.simps)
    have loflat: "flatBT (operB (Trans N) (numBT (Suc k2)))
        = ?S @ flatBT (Dpt (enat ?ub) Y1) @ ?B"
      using Fk Yflat[of k] crepA crepB fY1 by simp
    \<comment> \<open>hi donor \<open>numBT (Suc k) = numBT (k+1)\<close>: core \<open>Y\<^sub>3\<close> at the deep hole\<close>
    have crepA3: "concat (replicate (Suc (Suc k)) ?blk)
        = concat (replicate k2 ?blk) @ s0 @ [Dsym (enat ?ub)]
          @ s0 @ [Dsym (enat ?ub)] @ s0 @ [Dsym (enat ?ub)]
          @ s0 @ [Dsym (enat ?ub)]"
      using kk by (simp add: s85b_crep_comm_snoc s85b_crep_snoc s85b_crep_comm)
    have crepB3: "concat (replicate (Suc (Suc k)) b0)
        = b0 @ b0 @ b0 @ concat (replicate (Suc k2) b0)"
      using kk by simp
    have Fh: "flatBT (operB (Trans N) (numBT (Suc k)))
        = s1 @ Dsym (enat ?e3)
            # flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc (Suc k))) @ b1"
      using fseqY[of "Suc k"] by (simp del: d4vx_core.simps)
    have hiflat: "flatBT (operB (Trans N) (numBT (Suc k)))
        = ?S @ flatBT (Dpt (enat ?ub) Y3) @ ?B"
      using Fh Yflat[of "Suc (Suc k)"] crepA3 crepB3 fY1 fY2 fY3 by simp
    have ourdec: "scb_decomp (Trans ((N::pairseq)[m])) ?S
                    (flatBT (Dpt (enat ?ub) A1)) ?B"
      unfolding scb_decomp_def
      using ourflat BRP isPTB_str_Dpt[of "enat ?ub" A1] A1TB
      by (simp add: T_B_def)
    have lodec: "scb_decomp (operB (Trans N) (numBT (Suc k2))) ?S
                    (flatBT (Dpt (enat ?ub) Y1)) ?B"
      unfolding scb_decomp_def
      using loflat BRP isPTB_str_Dpt[of "enat ?ub" Y1] Y1TB
      by (simp add: T_B_def)
    have hidec: "scb_decomp (operB (Trans N) (numBT (Suc k))) ?S
                    (flatBT (Dpt (enat ?ub) Y3)) ?B"
      unfolding scb_decomp_def
      using hiflat BRP isPTB_str_Dpt[of "enat ?ub" Y3] Y3TB
      by (simp add: T_B_def)
    have "isOT_BT (Trans ((N::pairseq)[m]))"
      by (rule oix_transportD[OF otx3_transport lodec ourdec hidec
            donOT donOT newOTub ordlo ordhi setle])
    thus ?thesis .
  qed
  \<comment> \<open>\<open>T\<^bsub>B\<^esub>\<close> side and assembly\<close>
  have m1: "1 \<le> m" using mgt by simp
  have NmST: "(N::pairseq)[m] \<in> ST_PS" by (rule ST_PS.oper[OF NST m1])
  have NmRT: "(N::pairseq)[m] \<in> RT_PS"
    using NmST m_6_7_ST_PS_subseteq_RT_PS by blast
  have "Trans ((N::pairseq)[m]) \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF NmRT])
  thus ?thesis using isot by (simp add: OT_B_def OT_def)
qed

lemma oi8_OTint_condIII:
  fixes N :: pairseq and m :: nat
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS" and j1gt: "1 < Lng N - 1"
    and cIII: "transCondIII N" and ihOT: "Trans N \<in> OT_B" and mgt: "1 < m"
  shows "Trans ((N::pairseq)[m]) \<in> OT_B"
proof (cases "hasParent N 1 (Lng N - 1)")
  case True
  have branch: "transCondIII N \<or> transCondIV N" using cIII by blast
  have jm1eq: "transJm1 N = transJ0 N"
    using cIII
    by (simp add: transJm1_def transJ0_def transJ1_def transCondIII_def Adm_def)
  have jm2ltj0: "s84x_jm2 N < transJ0 N"
    by (rule m_8_4_oper_props_1(1)[OF NST NPT True j1gt branch])
  have jm3le: "s84x_jm3 N \<le> s84x_jm2 N"
    using adm_Adm_le by (simp add: s84x_jm3_def)
  have ltJ: "s84x_jm3 N < transJm1 N" using jm3le jm2ltj0 jm1eq by linarith
  show ?thesis
    by (rule oi8_OTint_IIIIV_hp[OF OTA1 SETLE1 NST NPT True j1gt branch ltJ
          ihOT mgt])
next
  case False
  have NR: "N \<in> RT_PS" using NST m_6_7_ST_PS_subseteq_RT_PS by blast
  have j1gt0: "0 < Lng N - 1" using j1gt by simp
  have epos: "0 < entry N 1 (Lng N - 1)"
    using cIII by (simp add: transCondIII_def)
  have NmP: "(N::pairseq)[m] = Pred N"
    by (rule npx_oper_noParent_Pred[OF j1gt0 epos False])
  have rb: "operB (Trans N) (numBT 0) = Trans (Pred N)"
    by (rule npx_operB_numBT0_Pred_condIII[OF NR NPT j1gt cIII False])
  have "operB (Trans N) (numBT 0) \<in> OT_B"
    by (rule e4x_OT_B_operB_numBT[OF ihOT])
  thus ?thesis using NmP rb by simp
qed

lemma oi8_OTint_condIV:
  fixes N :: pairseq and m :: nat
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and IVNP: "\<And>P. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIV P \<Longrightarrow> \<not> hasParent P 1 (Lng P - 1) \<Longrightarrow>
        Trans P \<in> OT_B \<Longrightarrow> Trans (Pred P) \<in> OT_B"
    and NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS" and j1gt: "1 < Lng N - 1"
    and cIV: "transCondIV N" and ihOT: "Trans N \<in> OT_B" and mgt: "1 < m"
  shows "Trans ((N::pairseq)[m]) \<in> OT_B"
proof (cases "hasParent N 1 (Lng N - 1)")
  case True
  show ?thesis
  proof (cases "Adm N (s84x_jm2 N) = transJm1 N")
    case eq: True
    show ?thesis
      by (rule IVADMEQ[OF NST NPT \<open>hasParent N 1 (Lng N - 1)\<close> j1gt cIV eq
            ihOT mgt])
  next
    case neq: False
    have branch: "transCondIII N \<or> transCondIV N" using cIV by blast
    have ltJ: "s84x_jm3 N < transJm1 N"
      by (rule cnv_condIV_ltJ[OF NST NPT True j1gt cIV neq])
    show ?thesis
      by (rule oi8_OTint_IIIIV_hp[OF OTA1 SETLE1 NST NPT True j1gt branch ltJ
            ihOT mgt])
  qed
next
  case False
  have j1gt0: "0 < Lng N - 1" using j1gt by simp
  have epos: "0 < entry N 1 (Lng N - 1)"
    using cIV by (simp add: transCondIV_def)
  have NmP: "(N::pairseq)[m] = Pred N"
    by (rule npx_oper_noParent_Pred[OF j1gt0 epos False])
  have "Trans (Pred N) \<in> OT_B"
    by (rule IVNP[OF NST NPT j1gt cIV False ihOT])
  thus ?thesis using NmP by simp
qed


subsection \<open>The ltJ-threaded master census, modulo \<open>{OTA1_ltJ, SETLE1_ltJ, IVADMEQ, FINRC}\<close>\<close>

text \<open>The r58 ltJ-threaded census: the \<open>otIII\<close>/\<open>otIV\<close> slots are discharged by
  @{thm [source] oi8_OTint_condIII} / @{thm [source] oi8_OTint_condIV}, whose
  \<open>OTA1\<close>/\<open>SETLE1\<close> demands carry the extra \<open>ltJ\<close> guard (\<open>s84x_jm3 P < transJm1 P\<close>).
  \<open>DEEPOT\<close>/\<open>NOBR\<close> are closed via @{thm [source] od4_DEEPOT}/@{thm [source] od4_NOBR}
  and \<open>IVNP\<close> via @{thm [source] ot2_IVNP} (as in @{thm [source] oi7_termination_census}),
  leaving both pillars modulo \<open>{OTA1_ltJ, SETLE1_ltJ, IVADMEQ, FINRC}\<close>.\<close>

theorem oi8_termination_census:
  assumes OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and FINRC: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             transCondII K \<Longrightarrow> tvx_finRc K"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have otIII: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIII P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
             Trans ((P::pairseq)[n]) \<in> OT_B"
    by (rule oi8_OTint_condIII[OF OTA1 SETLE1])
  have otIV: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
             Trans ((P::pairseq)[n]) \<in> OT_B"
    by (rule oi8_OTint_condIV[OF OTA1 SETLE1 IVADMEQ ot2_IVNP])
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oc4_termination_census_master_v2(1)[OF otIII otIV oi4_PredNp
          oi4_Lpv od4_DEEPOT od4_NOBR FINRC oi5_LbaseU])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oc4_termination_census_master_v2(2)[OF otIII otIV oi4_PredNp
          oi4_Lpv od4_DEEPOT od4_NOBR FINRC oi5_LbaseU])
qed


(* ===================================================================== *)
(* ===== r58 OTA1_ltJ assembly (front A): reduce the ltJ-guarded    ===== *)
(* =====   census assumption OTA1_ltJ to the two genuinely-hard      ===== *)
(* =====   bricks {nub, tri0} via ot1_OTA1_from_bricks.  Everything   ==== *)
(* =====   else (the flat forms, the donor-OT readoff via            ===== *)
(* =====   m_8_7_OT_scb_recursive on operB(numBT 1/2), the base       ==== *)
(* =====   orders) is discharged from oi5_IIIIV_pkg + oi5_regime.     ==== *)
(* ===================================================================== *)

text \<open>ot1_OTA1_reduce: the OTA1_ltJ conclusion isOT_BP (D_e3 A1) proved from the
  census premises PLUS the two hard bricks nub = isOT_BP (D_ub A0) (the deep-graft
  newOT_body) and tri0 = b1x_triG (D_inf X0) A0 X1 (the CRUX, proven by
  crx_tri0_of_nest / cnv_tri0_of_nest from the raw cpx_condIII_mnform
  decompositions).  The donor bricks (X1,X2 OT and their D_e3-principals) are read
  off the [Buc1]-closure donors operB (Trans N) (numBT 1/2) (OT by
  e4x_OT_B_operB_numBT) at the shared (s1,b1) scb position via
  m_8_7_OT_scb_recursive; the flat forms via d4vx_ins_flat; the base orders
  X0 <= A0 <= X1 from base0/base1 of oi5_IIIIV_pkg.  The census (s0,b0) is
  identified with the package's obtained (s0,b0) by scb uniqueness
  (m_7_2_scb_unique_sb).\<close>

lemma ot1_OTA1_reduce:
  fixes N :: pairseq and s0 b0 :: "Sym list"
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and ihOT: "Trans N \<in> OT_B"
    and b0RP_g: "\<forall>x \<in> set b0. x = RP"
    and inner_g: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                   (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and nub: "isOT_BP (DB (enat (entry N 1 (Lng N - 1) - 1))
                (bpHeadT (Trans (Pred (s84x_N N)))))"
    and tri0: "b1x_triG (Dpt \<infinity> 0\<^sub>B)
                (bpHeadT (Trans (Pred (s84x_N N))))
                (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0 0\<^sub>B)"
  shows "isOT_BP (DB (enat (entry N 1 (s84x_jm3 N)))
           (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
              (bpHeadT (Trans (Pred (s84x_N N))))))"
proof -
  let ?e3 = "entry N 1 (s84x_jm3 N)"
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  \<comment> \<open>package and regime\<close>
  obtain s0p b0p s1 b1 where
    b0RP: "\<forall>x \<in> set b0p. x = RP" and b1RP: "\<forall>x \<in> set b1. x = RP"
    and inner: "scb_decomp ?body s0p (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0p"
    and k1: "scb_kind1 (Trans N) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    and base0: "lessBT (Dpt (enat ?ub) 0\<^sub>B) ?A0"
    and base1: "lessBT ?A0 (d4vx_ins s0p ?ub b0p 0\<^sub>B)"
    and A0TB: "?A0 \<in> T_B"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  note regime = oi5_regime[OF NST NPT hp j1gt branch]
  have uv: "?e3 < ?v1" by (rule regime(1))
  have bodyT: "?body \<in> T_B" by (rule regime(3))
  have dbbodyH: "domB ?body = TBv (enat ?ub)" by (rule regime(4))
  have TT: "Trans N \<in> T_B" by (rule regime(5))
  have wrap: "flatBT ?body = s0p @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0p"
    using inner by (simp add: scb_decomp_def)
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "flatBT ?body = s0p @ flatBT (Dpt (enat ?v1) 0\<^sub>B) @ b0p"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0p @ [Dsym (enat ?v1), Zsym] @ b0p" using z by simp
    thus False by (cases s0p) auto
  qed
  \<comment> \<open>identify the census \<open>(s\<^sub>0,b\<^sub>0)\<close> with the package's\<close>
  have seq: "s0 = s0p" and beq: "b0 = b0p"
    using m_7_2_scb_unique_sb[OF inner_g inner bodyne] by simp_all
  \<comment> \<open>towers over the package \<open>(s\<^sub>0,b\<^sub>0)\<close>.  r72: the tower seed is \<open>0\<^sub>B\<close>
      (the corrected operB core), so \<open>X\<^sub>1 = Y\<^sub>1\<close> is the core of \<open>numBT 0\<close> and
      \<open>X\<^sub>2 = Y\<^sub>2\<close> that of \<open>numBT 1\<close>.\<close>
  define X0 where "X0 = (0\<^sub>B :: BT)"
  define A1 where "A1 = d4vx_ins s0p ?ub b0p ?A0"
  define X1 where "X1 = d4vx_ins s0p ?ub b0p X0"
  define X2 where "X2 = d4vx_ins s0p ?ub b0p X1"
  have X0TB: "X0 \<in> T_B" by (simp add: X0_def T_B_def)
  have A0TB': "?A0 \<in> T_B" by (rule A0TB)
  have X1TB: "X1 \<in> T_B"
    unfolding X1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT X0TB])
  have X2TB: "X2 \<in> T_B"
    unfolding X2_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT X1TB])
  have fA1: "flatBT A1 = s0p @ flatBP (DB (enat ?ub) ?A0) @ b0p"
    unfolding A1_def using d4vx_ins_flat[OF wrap b0RP] by simp
  have fX1: "flatBT X1 = s0p @ flatBP (DB (enat ?ub) X0) @ b0p"
    unfolding X1_def using d4vx_ins_flat[OF wrap b0RP] by simp
  have fX2: "flatBT X2 = s0p @ flatBP (DB (enat ?ub) X1) @ b0p"
    unfolding X2_def using d4vx_ins_flat[OF wrap b0RP] by simp
  \<comment> \<open>fseq closed forms of the donors\<close>
  have fseq: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate (n + 1) (s0p @ [Dsym (enat ?ub)]))
           @ [Zsym]
           @ concat (replicate (n + 1) b0p)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbodyH bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0p ?ub b0p X0 n)
      = concat (replicate n (s0p @ [Dsym (enat ?ub)]))
        @ flatBT X0 @ concat (replicate n b0p)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fseqX: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0p ?ub b0p 0\<^sub>B (Suc n)) @ b1"
  proof -
    fix n :: nat
    have A: "flatBT (d4vx_core s0p ?ub b0p 0\<^sub>B (Suc n))
        = concat (replicate (Suc n) (s0p @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (Suc n) b0p)"
      using Xflat[of "Suc n"] by (simp del: d4vx_core.simps add: X0_def)
    show "flatBT (operB (Trans N) (numBT n))
        = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0p ?ub b0p 0\<^sub>B (Suc n)) @ b1"
      using fseq[of n] A by (simp del: d4vx_core.simps)
  qed
  have donOTB: "\<And>n. operB (Trans N) (numBT n) \<in> OT_B"
    using e4x_OT_B_operB_numBT[OF ihOT] by simp
  \<comment> \<open>donor cores at the kind-1 hole (head e3): X1 = core of numBT 0, X2 = core of numBT 1\<close>
  have loflat: "flatBT (operB (Trans N) (numBT 0))
      = s1 @ flatBT (Dpt (enat ?e3) X1) @ b1"
    using fseqX[of 0] by (simp add: X1_def X0_def)
  have hiflat: "flatBT (operB (Trans N) (numBT 1))
      = s1 @ flatBT (Dpt (enat ?e3) X2) @ b1"
  proof -
    have "d4vx_core s0p ?ub b0p X0 (Suc (Suc 0)) = X2"
      by (simp add: X1_def X2_def)
    thus ?thesis using fseqX[of 1] by (simp add: X0_def)
  qed
  have lodec: "scb_decomp (operB (Trans N) (numBT 0)) s1
                  (flatBT (Dpt (enat ?e3) X1)) b1"
    unfolding scb_decomp_def
    using loflat b1RP isPTB_str_Dpt[of "enat ?e3" X1] X1TB
    by (simp add: T_B_def)
  have hidec: "scb_decomp (operB (Trans N) (numBT 1)) s1
                  (flatBT (Dpt (enat ?e3) X2)) b1"
    unfolding scb_decomp_def
    using hiflat b1RP isPTB_str_Dpt[of "enat ?e3" X2] X2TB
    by (simp add: T_B_def)
  \<comment> \<open>donor OT-ness of the principals via the scb-position readoff\<close>
  have loPe: "isOT_BP (DB (enat ?e3) X1)"
  proof -
    have DptTB: "Dpt (enat ?e3) X1 \<in> T_B" using X1TB by (simp add: T_B_def)
    have "Dpt (enat ?e3) X1 \<in> OT"
      by (rule m_8_7_OT_scb_recursive[OF donOTB[of 0] DptTB lodec])
    thus ?thesis by (simp add: OT_def)
  qed
  have hiPe: "isOT_BP (DB (enat ?e3) X2)"
  proof -
    have DptTB: "Dpt (enat ?e3) X2 \<in> T_B" using X2TB by (simp add: T_B_def)
    have "Dpt (enat ?e3) X2 \<in> OT"
      by (rule m_8_7_OT_scb_recursive[OF donOTB[of 1] DptTB hidec])
    thus ?thesis by (simp add: OT_def)
  qed
  have X1OT: "isOT_BT X1" using loPe by simp
  have X2OT: "isOT_BT X2" using hiPe by simp
  \<comment> \<open>base orders and the tri0 in package form\<close>
  have o1: "leBT X0 ?A0"
  proof -
    have "lessBT (0\<^sub>B :: BT) (Dpt (enat ?ub) 0\<^sub>B)" by simp
    thus ?thesis using base0 lessBT_trans by (auto simp: X0_def)
  qed
  have o2: "leBT ?A0 X1" using base1 by (simp add: X1_def X0_def)
  have tri0p: "b1x_triG (Dpt \<infinity> X0) ?A0 X1"
    using tri0 seq beq by (simp add: X0_def X1_def)
  \<comment> \<open>assemble via the OTA1 engine\<close>
  have "isOT_BP (DB (enat ?e3) A1)"
    by (rule ot1_OTA1_from_bricks[OF fX1 fA1 fX2 b0RP X1OT X2OT loPe hiPe
          nub o1 o2 tri0p])
  thus ?thesis using seq beq by (simp add: A1_def)
qed


text \<open>ot1_tri0_census: the tri0 brick b1x_triG z A0 X1 at the census level, for
  ANY z (so in particular z = D_inf X0).  Rebuilds the raw cpx_condIII_mnform
  decompositions (dPq/d2q/d4c2q) from the same REGS/REGSP/J1pos/T1 setup as
  oi5_IIIIV_pkg, then applies the CRUX crx_tri0_of_nest (condIII) /
  cnv_tri0_of_nest (condIV).  The census (s0,b0) is threaded via the given inner
  decomposition (crx/cnv internally identify it by scb uniqueness).\<close>

lemma ot1_tri0_census:
  fixes N :: pairseq and s0 b0 :: "Sym list" and z :: BT
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and inner_g: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                   (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
  shows "b1x_triG z (bpHeadT (Trans (Pred (s84x_N N))))
           (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
              (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))"
proof -
  have MR: "N \<in> RT_PS" using NST m_6_7_ST_PS_subseteq_RT_PS by blast
  \<comment> \<open>REGS/REGSP, unconditional (as in oi5_IIIIV_pkg)\<close>
  have REGS: "s84x_jm3 N < s84x_jm2 N \<Longrightarrow>
                cfbx_reg (s84x_jm2 N - s84x_jm3 N) (Red (s84x_N N))"
  proof -
    assume g: "s84x_jm3 N < s84x_jm2 N"
    show "cfbx_reg (s84x_jm2 N - s84x_jm3 N) (Red (s84x_N N))"
      by (rule mcx_regS[OF NST NPT hp j1gt branch g])
  qed
  have REGSP: "s84x_jm3 N < s84x_jm2 N \<Longrightarrow> Br (Red (Pred (s84x_N N))) \<noteq> [] \<Longrightarrow>
                 cfbx_reg (s84x_jm2 N - s84x_jm3 N) (Red (Pred (s84x_N N)))"
  proof -
    assume g: "s84x_jm3 N < s84x_jm2 N" and b: "Br (Red (Pred (s84x_N N))) \<noteq> []"
    show "cfbx_reg (s84x_jm2 N - s84x_jm3 N) (Red (Pred (s84x_N N)))"
      by (rule slx37_regSP_uncond[OF NST NPT hp j1gt branch g b])
  qed
  \<comment> \<open>regime facts J1pos/T1\<close>
  have nVI: "\<not> transCondVI N"
  proof (cases "transCondIII N")
    case True
    thus ?thesis by (auto simp: transCondIII_def transCondVI_def)
  next
    case False
    hence cIV: "transCondIV N" using branch by blast
    show ?thesis using c4dx_condIV_excl(4)[OF cIV] .
  qed
  have J1pos: "transJ1 N > 0" using j1gt by (simp add: transJ1_def)
  have T1: "transT1 N \<noteq> 0\<^sub>B"
    using s84d_L4_regime[OF NST NPT hp nVI] by simp
  \<comment> \<open>the raw cpx decompositions\<close>
  obtain u1 u2 v2 w1 s1 b1 where
      dPq: "scb_decomp (Trans (Pred (s84x_N N)))
              (Dsym (enat (entry N 1 (s84x_jm3 N))) # u1) (flatBT (transC1 N)) w1"
    and d2q: "scb_decomp (Trans (s84x_N N))
              (Dsym (enat (entry N 1 (s84x_jm3 N))) # u1) (flatBT (transC2 N)) w1"
    and d4c2q: "scb_decomp (transC2 N) u2
              (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) v2"
    using cpx_condIII_mnform[OF NST NPT hp j1gt branch ltJ REGS REGSP] by blast
  \<comment> \<open>apply the CRUX per branch (census (s0,b0) threaded via inner_g)\<close>
  show ?thesis
  proof (cases "transCondIII N")
    case True
    show ?thesis
      by (rule crx_tri0_of_nest[OF MR NPT J1pos T1 True dPq d2q d4c2q inner_g])
  next
    case False
    hence cIV: "transCondIV N" using branch by blast
    show ?thesis
      by (rule cnv_tri0_of_nest[OF MR NPT J1pos T1 cIV dPq d2q d4c2q inner_g])
  qed
qed


text \<open>\<^bold>\<open>r72\<close>: the \<open>tri0\<close> brick at the CORRECTED tower seed --- upper endpoint
  \<open>Y\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 0\<^sub>B\<close> instead of \<open>X\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 (D\<^bsub>ub\<^esub>0)\<close>.
  @{const b1x_triG} quantifies over the interval \<open>[A\<^sub>0, \<cdot>]\<close>, so it is antitone in its
  upper endpoint (@{thm [source] oy1_triG_antitone}), and \<open>Y\<^sub>1 \<le> X\<^sub>1\<close> by
  \<open>ins\<close>-monotonicity (\<open>0\<^sub>B < D\<^bsub>ub\<^esub>0\<close>).  So the proven census \<open>tri0\<close>
  (@{thm [source] ot1_tri0_census}) transfers verbatim.\<close>

lemma oy1_tri0Y_census:
  fixes N :: pairseq and s0 b0 :: "Sym list" and z :: BT
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and inner_g: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                   (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
  shows "b1x_triG z (bpHeadT (Trans (Pred (s84x_N N))))
           (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0 0\<^sub>B)"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  have tri: "b1x_triG z (bpHeadT (Trans (Pred (s84x_N N))))
               (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))"
    by (rule ot1_tri0_census[OF NST NPT hp j1gt branch ltJ inner_g])
  have wrap: "flatBT (bpHeadT (Trans (s84x_N N)))
      = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner_g by (simp add: scb_decomp_def)
  have b0RP: "\<forall>x \<in> set b0. x = RP" using inner_g by (simp add: scb_decomp_def)
  have zle: "leBT (0\<^sub>B :: BT) (Dpt (enat ?ub) 0\<^sub>B)" by simp
  have le: "leBT (d4vx_ins s0 ?ub b0 0\<^sub>B) (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))"
    by (rule oy1_ins_le_mono[OF wrap b0RP zle])
  show ?thesis by (rule oy1_triG_antitone[OF tri le])
qed

text \<open>ot1_nub_from_A0OT: the newOT_body brick nub = isOT_BP (D_ub A0) from the
  SINGLE genuine unknown A0OT = isOT_BT A0 (A0 = bpHeadT(Trans(Pred(s84x_N N)))).
  Wiring = otx3_pOT at head ub with cores (X0, A0, X1): loP = isOT_BP(D_ub X0)
  free (isOT_BP_Dpt_Dpt_Zero); hiP = isOT_BP(D_ub X1) from the donor readoff
  isOT_BP(D_e3 X1) by G-antitonicity (e3 <= ub); base orders from oi5_IIIIV_pkg;
  tri0 from ot1_tri0_census.  Thus nub is closed once A0OT is available.\<close>

lemma ot1_nub_from_A0OT:
  fixes N :: pairseq and s0 b0 :: "Sym list"
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and ihOT: "Trans N \<in> OT_B"
    and b0RP_g: "\<forall>x \<in> set b0. x = RP"
    and inner_g: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                   (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and A0OT: "isOT_BT (bpHeadT (Trans (Pred (s84x_N N))))"
  shows "isOT_BP (DB (enat (entry N 1 (Lng N - 1) - 1))
           (bpHeadT (Trans (Pred (s84x_N N)))))"
proof -
  let ?e3 = "entry N 1 (s84x_jm3 N)"
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  obtain s0p b0p s1 b1 where
    b0RP: "\<forall>x \<in> set b0p. x = RP" and b1RP: "\<forall>x \<in> set b1. x = RP"
    and inner: "scb_decomp ?body s0p (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0p"
    and k1: "scb_kind1 (Trans N) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    and base0: "lessBT (Dpt (enat ?ub) 0\<^sub>B) ?A0"
    and base1: "lessBT ?A0 (d4vx_ins s0p ?ub b0p 0\<^sub>B)"
    and A0TB: "?A0 \<in> T_B"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  note regime = oi5_regime[OF NST NPT hp j1gt branch]
  have uv: "?e3 < ?v1" by (rule regime(1))
  have e3ub: "?e3 \<le> ?ub" by (rule regime(2))
  have bodyT: "?body \<in> T_B" by (rule regime(3))
  have dbbodyH: "domB ?body = TBv (enat ?ub)" by (rule regime(4))
  have TT: "Trans N \<in> T_B" by (rule regime(5))
  have wrap: "flatBT ?body = s0p @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0p"
    using inner by (simp add: scb_decomp_def)
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "flatBT ?body = s0p @ flatBT (Dpt (enat ?v1) 0\<^sub>B) @ b0p"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0p @ [Dsym (enat ?v1), Zsym] @ b0p" using z by simp
    thus False by (cases s0p) auto
  qed
  have seq: "s0 = s0p" and beq: "b0 = b0p"
    using m_7_2_scb_unique_sb[OF inner_g inner bodyne] by simp_all
  define X0 where "X0 = (0\<^sub>B :: BT)"
  define X1 where "X1 = d4vx_ins s0p ?ub b0p X0"
  have X0TB: "X0 \<in> T_B" by (simp add: X0_def T_B_def)
  have X1TB: "X1 \<in> T_B"
    unfolding X1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT X0TB])
  \<comment> \<open>donor readoff (r72): isOT_BP (D_e3 X1) from the [Buc1]-closure donor operB(numBT 0)\<close>
  have fseq: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate (n + 1) (s0p @ [Dsym (enat ?ub)]))
           @ [Zsym]
           @ concat (replicate (n + 1) b0p)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbodyH bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0p ?ub b0p X0 n)
      = concat (replicate n (s0p @ [Dsym (enat ?ub)]))
        @ flatBT X0 @ concat (replicate n b0p)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fseqX: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0p ?ub b0p 0\<^sub>B (Suc n)) @ b1"
  proof -
    fix n :: nat
    have A: "flatBT (d4vx_core s0p ?ub b0p 0\<^sub>B (Suc n))
        = concat (replicate (Suc n) (s0p @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (Suc n) b0p)"
      using Xflat[of "Suc n"] by (simp del: d4vx_core.simps add: X0_def)
    show "flatBT (operB (Trans N) (numBT n))
        = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0p ?ub b0p 0\<^sub>B (Suc n)) @ b1"
      using fseq[of n] A by (simp del: d4vx_core.simps)
  qed
  have donOTB: "operB (Trans N) (numBT 0) \<in> OT_B"
    using e4x_OT_B_operB_numBT[OF ihOT] by simp
  have loflat: "flatBT (operB (Trans N) (numBT 0))
      = s1 @ flatBT (Dpt (enat ?e3) X1) @ b1"
    using fseqX[of 0] by (simp add: X1_def X0_def)
  have lodec: "scb_decomp (operB (Trans N) (numBT 0)) s1
                  (flatBT (Dpt (enat ?e3) X1)) b1"
    unfolding scb_decomp_def
    using loflat b1RP isPTB_str_Dpt[of "enat ?e3" X1] X1TB
    by (simp add: T_B_def)
  have loPe: "isOT_BP (DB (enat ?e3) X1)"
  proof -
    have DptTB: "Dpt (enat ?e3) X1 \<in> T_B" using X1TB by (simp add: T_B_def)
    have "Dpt (enat ?e3) X1 \<in> OT"
      by (rule m_8_7_OT_scb_recursive[OF donOTB DptTB lodec])
    thus ?thesis by (simp add: OT_def)
  qed
  \<comment> \<open>lift the donor principal to head ub by G-antitonicity (e3 <= ub)\<close>
  have hiP: "isOT_BP (DB (enat ?ub) X1)"
  proof -
    have X1OT: "isOT_BT X1" and gE3: "\<forall>x \<in> GBT (enat ?e3) X1. lessBT x X1"
      using loPe by simp_all
    have le: "enat ?e3 \<le> enat ?ub" using e3ub by simp
    have "GBT (enat ?ub) X1 \<subseteq> GBT (enat ?e3) X1"
      by (rule b1x_GBT_antitone[OF le])
    hence "\<forall>x \<in> GBT (enat ?ub) X1. lessBT x X1" using gE3 by blast
    thus ?thesis using X1OT by simp
  qed
  have loP: "isOT_BP (DB (enat ?ub) X0)" by (simp add: X0_def)
  have o1: "leBT X0 ?A0"
  proof -
    have "lessBT (0\<^sub>B :: BT) (Dpt (enat ?ub) 0\<^sub>B)" by simp
    thus ?thesis using base0 lessBT_trans by (auto simp: X0_def)
  qed
  have o2: "leBT ?A0 X1" using base1 by (simp add: X1_def X0_def)
  have tri0: "b1x_triG (Dpt \<infinity> X0) ?A0 X1"
  proof -
    have "b1x_triG (Dpt \<infinity> (0\<^sub>B :: BT)) ?A0
            (d4vx_ins s0 ?ub b0 0\<^sub>B)"
      by (rule oy1_tri0Y_census[OF NST NPT hp j1gt branch ltJ inner_g])
    thus ?thesis using seq beq by (simp add: X0_def X1_def)
  qed
  show ?thesis
    by (rule otx3_pOT[OF loP hiP A0OT o1 o2 tri0])
qed


text \<open>ot1_OTA1_from_A0OT: the FULL OTA1_ltJ conclusion from the single genuine
  unknown A0OT.  Composes ot1_tri0_census (tri0), ot1_nub_from_A0OT (nub) and
  ot1_OTA1_reduce.  Hence the ltJ-guarded census assumption OTA1_ltJ is closed
  modulo exactly A0OT = isOT_BT (bpHeadT (Trans (Pred (s84x_N N)))).\<close>

lemma ot1_OTA1_from_A0OT:
  fixes N :: pairseq and s0 b0 :: "Sym list"
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and ihOT: "Trans N \<in> OT_B"
    and b0RP_g: "\<forall>x \<in> set b0. x = RP"
    and inner_g: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                   (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and A0OT: "isOT_BT (bpHeadT (Trans (Pred (s84x_N N))))"
  shows "isOT_BP (DB (enat (entry N 1 (s84x_jm3 N)))
           (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
              (bpHeadT (Trans (Pred (s84x_N N))))))"
proof -
  have tri0: "b1x_triG (Dpt \<infinity> (0\<^sub>B :: BT))
                (bpHeadT (Trans (Pred (s84x_N N))))
                (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0 0\<^sub>B)"
    by (rule oy1_tri0Y_census[OF NST NPT hp j1gt branch ltJ inner_g])
  have nub: "isOT_BP (DB (enat (entry N 1 (Lng N - 1) - 1))
               (bpHeadT (Trans (Pred (s84x_N N)))))"
    by (rule ot1_nub_from_A0OT[OF NST NPT hp j1gt branch ltJ ihOT b0RP_g inner_g A0OT])
  show ?thesis
    by (rule ot1_OTA1_reduce[OF NST NPT hp j1gt branch ltJ ihOT b0RP_g inner_g
          nub tri0])
qed


text \<open>oi8_census_via_A0OT: the ltJ-threaded master census with the complex
  OTA1_ltJ assumption REPLACED by the single OT-membership fact
  A0OT = isOT_BT (bpHeadT (Trans (Pred (s84x_N P)))) (the deep-graft newOT_body
  OT-ness, the genuine 8.7 surgery residual).  Everything else in the OTA1 leg is
  discharged by ot1_OTA1_from_A0OT.  Result: both termination pillars hold modulo
  the sharper residual set {A0OT, SETLE1_ltJ, IVADMEQ, FINRC}.\<close>

theorem oi8_census_via_A0OT:
  assumes A0OT: "\<And>P. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        isOT_BT (bpHeadT (Trans (Pred (s84x_N P))))"
    and SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and FINRC: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             transCondII K \<Longrightarrow> tvx_finRc K"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have OTA1: "\<And>P s0 b0. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
  proof -
    fix P :: pairseq and s0 b0 :: "Sym list"
    assume p1: "P \<in> ST_PS" and p2: "P \<in> PT_PS"
      and p3: "hasParent P 1 (Lng P - 1)" and p4: "1 < Lng P - 1"
      and p5: "transCondIII P \<or> transCondIV P" and p6: "Trans P \<in> OT_B"
      and p7: "\<forall>x \<in> set b0. x = RP"
      and p8: "scb_decomp (bpHeadT (Trans (s84x_N P))) s0
                 (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0"
      and p9: "s84x_jm3 P < transJm1 P"
    have a0: "isOT_BT (bpHeadT (Trans (Pred (s84x_N P))))"
      by (rule A0OT[OF p1 p2 p3 p4 p5 p6 p9])
    show "isOT_BP (DB (enat (entry P 1 (s84x_jm3 P)))
                    (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                       (bpHeadT (Trans (Pred (s84x_N P))))))"
      by (rule ot1_OTA1_from_A0OT[OF p1 p2 p3 p4 p5 p9 p6 p7 p8 a0])
  qed
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi8_termination_census(1)[OF OTA1 SETLE1 IVADMEQ FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi8_termination_census(2)[OF OTA1 SETLE1 IVADMEQ FINRC])
qed



(* ===================================================================== *)
(* r58 IVADMEQ2 (front B, prefix ot2_): the CLEAN transT2-hole d4vx_core   *)
(*   tower NEWOT engine, built via the TRI route (otx3_core_tri +          *)
(*   otx3_pOT), NOT the setle induction.  The compound d4vx_ins increment  *)
(*   t3 +B D_jp(t4 +B D_ub .) breaks the oix_twr single-D_e setle          *)
(*   induction (extra Y_A = t4 +B D_ub A_k obligation), but the FLAT-level  *)
(*   context recursion otx3_core_tri applies verbatim through the surgery  *)
(*   wrapper (s0,b0): it lifts the base tri0 up the tower and produces      *)
(*   isOT_BT A_k at each level, and otx3_pOT reads off the D_e3 principal.  *)
(* ===================================================================== *)

text \<open>@{text ot2_tower_newOT}: the tower @{const d4vx_core} newOT for the CLEAN
  base t2 = transT2 M.  A_k = d4vx_core s0 ub b0 t2 k, W_k = the X-tower over
  D_ub 0 (the operB fundamental-sequence core).  Given the base G-control tri0
  (@{thm [source] cnv_tri0_of_nest}), the interleave W_k < A_k < W_(k+1)
  (@{thm [source] c4cx_d4vx_core_interleave}) and the X-tower OT principals
  D_e3 W_k in OT (from operB(Trans M) in OT_B), the joint invariant
  (isOT A_k, A_k triG-below W_(k+1) rel D_inf W_k) lifts level-by-level through
  @{thm [source] otx3_core_tri} (the D_ub-body a' principal supplied by
  @{thm [source] otx3_pOT} at head ub from the SAME invariant); the final
  D_e3 A_k in OT is one more @{thm [source] otx3_pOT} at head e3.  The head-ub
  X-tower principals are the head-antitone rebase
  (@{thm [source] oix_isOT_BP_head_antitone}, e3 <= ub) of the head-e3 ones.\<close>

lemma ot2_tower_newOT:
  fixes s0 b0 :: "Sym list" and ub e3 vv :: nat and W0 t2 :: BT and k :: nat
  assumes wrap: "flatBT W0 = s0 @ flatBP (DB (enat vv) 0\<^sub>B) @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and euB: "e3 \<le> ub"
    and t2OT: "isOT_BT t2"
    and base0: "lessBT (Dpt (enat ub) 0\<^sub>B) t2"
    and base1: "lessBT t2 (d4vx_ins s0 ub b0 0\<^sub>B)"
    and tri0: "b1x_triG (Dpt \<infinity> (0\<^sub>B :: BT)) t2
                 (d4vx_ins s0 ub b0 0\<^sub>B)"
    and Xe3: "\<And>j. isOT_BP (DB (enat e3) (d4vx_core s0 ub b0 0\<^sub>B j))"
  shows "isOT_BP (DB (enat e3) (d4vx_core s0 ub b0 t2 k))"
proof -
  let ?W = "d4vx_core s0 ub b0 (0\<^sub>B :: BT)"
  let ?A = "d4vx_core s0 ub b0 t2"
  \<comment> \<open>X-tower OT facts (bodies, and head-\<open>ub\<close> principals by head antitone)\<close>
  have Wot: "isOT_BT (?W j)" for j using Xe3[of j] by simp
  have Xub: "isOT_BP (DB (enat ub) (?W j))" for j
    using oix_isOT_BP_head_antitone[OF Xe3[of j], of "enat ub"] euB by simp
  \<comment> \<open>interleave orders \<open>W\<^sub>j < A\<^sub>j < W\<^bsub>j+1\<^esub>\<close>\<close>
  have base0Z: "lessBT (0\<^sub>B :: BT) t2"
  proof -
    have "lessBT (0\<^sub>B :: BT) (Dpt (enat ub) 0\<^sub>B)" by simp
    thus ?thesis using base0 lessBT_trans by blast
  qed
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0Z base1]
  have ordlo: "leBT (?W j) (?A j)" for j using IL by blast
  have ordhi: "leBT (?A j) (?W (Suc j))" for j using IL by blast
  \<comment> \<open>the surgery-step flat, in the flatBP form otx3 consumes\<close>
  have fins: "flatBT (d4vx_ins s0 ub b0 X) = s0 @ flatBP (DB (enat ub) X) @ b0" for X
    using d4vx_ins_flat[OF wrap b0RP] by simp
  \<comment> \<open>the joint invariant, lifted level-by-level by otx3_core_tri\<close>
  have inv: "isOT_BT (?A j) \<and> b1x_triG (Dpt \<infinity> (?W j)) (?A j) (?W (Suc j))" for j
  proof (induction j)
    case 0
    show ?case using t2OT tri0 by simp
  next
    case (Suc j)
    have Aot: "isOT_BT (?A j)"
      and TRIj: "b1x_triG (Dpt \<infinity> (?W j)) (?A j) (?W (Suc j))"
      using Suc.IH by blast+
    have nub: "isOT_BP (DB (enat ub) (?A j))"
      by (rule otx3_pOT[OF Xub Xub Aot ordlo ordhi TRIj])
    have fW: "flatBT (?W (Suc j)) = s0 @ flatBP (DB (enat ub) (?W j)) @ b0"
      using fins[of "?W j"] by simp
    have fA: "flatBT (?A (Suc j)) = s0 @ flatBP (DB (enat ub) (?A j)) @ b0"
      using fins[of "?A j"] by simp
    have fW2: "flatBT (?W (Suc (Suc j)))
                 = s0 @ flatBP (DB (enat ub) (?W (Suc j))) @ b0"
      using fins[of "?W (Suc j)"] by simp
    from otx3_core_tri[OF fW fA fW2 b0RP Wot Wot nub ordlo ordhi TRIj]
    have "isOT_BT (?A (Suc j))
        \<and> b1x_triG (Dpt \<infinity> (?W (Suc j))) (?A (Suc j)) (?W (Suc (Suc j)))"
      by blast
    thus ?case by blast
  qed
  have Aotk: "isOT_BT (?A k)"
    and TRIk: "b1x_triG (Dpt \<infinity> (?W k)) (?A k) (?W (Suc k))"
    using inv by blast+
  show ?thesis
    by (rule otx3_pOT[OF Xe3 Xe3 Aotk ordlo ordhi TRIk])
qed

text \<open>@{text ot2_NEWOT_of_pkg}: the NEWOT residual of @{thm [source] ot2_IVADMEQ_mod}
  discharged against the SAME producer package that @{thm [source] ot2_IVADMEQ_of_pkg}
  consumes, plus the four CLEAN tower inputs (\<open>t2OT\<close>, \<open>base0\<close>, \<open>base1\<close>, \<open>tri0\<close>).
  The X-tower OT principals \<open>D\<^bsub>e3\<^esub> W_k in OT\<close> are extracted from
  \<open>operB(Trans M)(numBT k) in OT_B\<close> (@{thm [source] e4x_OT_B_operB_numBT}) via the
  scb readback @{thm [source] d13x_fseq_condIII}/@{thm [source] d4vx_core_flat}
  and OT-heredity @{thm [source] m_8_7_OT_scb_recursive}; then
  @{thm [source] ot2_tower_newOT} closes.\<close>

lemma ot2_NEWOT_of_pkg:
  fixes M :: pairseq and s0 s1 b0 b1 :: "Sym list" and body :: BT and k :: nat
  assumes MST: "M \<in> ST_PS"
    and ihOT: "Trans M \<in> OT_B"
    and uv: "entry M 1 (s84x_jm3 M) < entry M 1 (Lng M - 1)"
    and bodyT: "body \<in> T_B"
    and bodyne: "body \<noteq> Trm []"
    and dbbody: "domB body = TBv (enat (entry M 1 (Lng M - 1) - 1))"
    and inner: "scb_decomp body s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
    and k1: "scb_kind1 (Trans M) s1
               (flatBT (Dpt (enat (entry M 1 (s84x_jm3 M))) body)) b1"
    and t2OT: "isOT_BT (transT2 M)"
    and base0: "lessBT (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) (transT2 M)"
    and base1: "lessBT (transT2 M)
                  (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
                     0\<^sub>B)"
    and tri0: "b1x_triG (Dpt \<infinity> (0\<^sub>B :: BT)) (transT2 M)
                 (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0 0\<^sub>B)"
  shows "isOT_BP (DB (enat (entry M 1 (s84x_jm3 M)))
                    (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0 (transT2 M) k))"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?X0 = "Dpt (enat ?ub) 0\<^sub>B"
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have TT: "Trans M \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF MR])
  have wrap: "flatBT body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have b0RP: "\<forall>x \<in> set b0. x = RP" using inner by (simp add: scb_decomp_def)
  have dTM: "scb_decomp (Trans M) s1 (flatBT (Dpt (enat ?e3) body)) b1"
    using k1 by (simp add: scb_kind1_def)
  have b1RP: "\<forall>x \<in> set b1. x = RP" using dTM by (simp add: scb_decomp_def)
  have X0TB: "(0\<^sub>B :: BT) \<in> T_B" by (simp add: T_B_def)
  have WTB: "\<And>j. d4vx_core s0 ?ub b0 0\<^sub>B j \<in> T_B"
    by (rule oi5_d4vx_core_TB[OF wrap b0RP bodyT X0TB])
  \<comment> \<open>operB fundamental sequence flat, at the shared \<open>(s1,b1)\<close>, core = X-tower\<close>
  have fseq: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate (n + 1) (s0 @ [Dsym (enat ?ub)]))
           @ [Zsym]
           @ concat (replicate (n + 1) b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbody bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 0\<^sub>B n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT (0\<^sub>B :: BT) @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  \<comment> \<open>r72: the operB core is the \<open>0\<^sub>B\<close>-seeded tower ONE LEVEL DEEPER\<close>
  have fWn: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))) @ b1"
  proof -
    fix n :: nat
    have A: "flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))
        = concat (replicate (Suc n) (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (Suc n) b0)"
      using Xflat[of "Suc n"] by (simp del: d4vx_core.simps)
    show "flatBT (operB (Trans M) (numBT n))
        = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))) @ b1"
      using fseq[of n] A by (simp del: d4vx_core.simps)
  qed
  \<comment> \<open>W-tower OT principals from the [Buc1] 3.2 closure of the IH
      (level \<open>j+1\<close> is the core of the donor \<open>numBT j\<close>; level \<open>0\<close> is \<open>0\<^sub>B\<close>)\<close>
  have Xe3: "\<And>j. isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B j))"
  proof -
    fix j :: nat
    show "isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B j))"
    proof (cases j)
      case 0
      thus ?thesis by simp
    next
      case (Suc n)
      have opOT: "operB (Trans M) (numBT n) \<in> OT_B"
        by (rule e4x_OT_B_operB_numBT[OF ihOT])
      have cTB: "Dpt (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)) \<in> T_B"
        using WTB[of "Suc n"] by (simp add: T_B_def del: d4vx_core.simps)
      have Xdec: "scb_decomp (operB (Trans M) (numBT n)) s1
                    (flatBT (Dpt (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)))) b1"
        unfolding scb_decomp_def
        using fWn[of n] b1RP
              isPTB_str_Dpt[of "enat ?e3" "d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)"]
              WTB[of "Suc n"]
        by (simp add: T_B_def del: d4vx_core.simps)
      have "Dpt (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)) \<in> OT"
        by (rule m_8_7_OT_scb_recursive[OF opOT cTB Xdec])
      hence "isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)))"
        by (simp add: OT_def)
      thus ?thesis using Suc by simp
    qed
  qed
  have euB: "?e3 \<le> ?ub" using uv by linarith
  show ?thesis
    by (rule ot2_tower_newOT[OF wrap b0RP euB t2OT base0 base1 tri0 Xe3])
qed

text \<open>@{text ot2_tower_inv}: the joint tower invariant that a SETLE-FREE final
  transport consumes --- \<open>isOT\<^bsub>BT\<^esub> A_k\<close> AND the tower G-control
  \<open>A_k \<triangleleft>\<^bsub>D_inf W_k\<^esub> W_(k+1)\<close>.  Feeding this triG at head \<open>e3\<close> into
  @{thm [source] otx3_core_tri} yields \<open>isOT\<^bsub>BT\<^esub>(Trans(M[m]))\<close> DIRECTLY (no
  @{term b1x_setle} obligation), so it eliminates the SETLE residual of
  @{thm [source] ot2_IVADMEQ_of_pkg} in favour of the already-available base
  \<open>tri0\<close> (@{thm [source] cnv_tri0_of_nest}).  Same proof core as
  @{thm [source] ot2_tower_newOT}, exposing both conjuncts of the invariant.\<close>

lemma ot2_tower_inv:
  fixes s0 b0 :: "Sym list" and ub e3 vv :: nat and W0 t2 :: BT and k :: nat
  assumes wrap: "flatBT W0 = s0 @ flatBP (DB (enat vv) 0\<^sub>B) @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and euB: "e3 \<le> ub"
    and t2OT: "isOT_BT t2"
    and base0: "lessBT (Dpt (enat ub) 0\<^sub>B) t2"
    and base1: "lessBT t2 (d4vx_ins s0 ub b0 0\<^sub>B)"
    and tri0: "b1x_triG (Dpt \<infinity> (0\<^sub>B :: BT)) t2
                 (d4vx_ins s0 ub b0 0\<^sub>B)"
    and Xe3: "\<And>j. isOT_BP (DB (enat e3) (d4vx_core s0 ub b0 0\<^sub>B j))"
  shows "isOT_BT (d4vx_core s0 ub b0 t2 k)
       \<and> b1x_triG (Dpt \<infinity> (d4vx_core s0 ub b0 0\<^sub>B k))
            (d4vx_core s0 ub b0 t2 k)
            (d4vx_core s0 ub b0 0\<^sub>B (Suc k))"
proof -
  let ?W = "d4vx_core s0 ub b0 (0\<^sub>B :: BT)"
  let ?A = "d4vx_core s0 ub b0 t2"
  have Wot: "isOT_BT (?W j)" for j using Xe3[of j] by simp
  have Xub: "isOT_BP (DB (enat ub) (?W j))" for j
    using oix_isOT_BP_head_antitone[OF Xe3[of j], of "enat ub"] euB by simp
  have base0Z: "lessBT (0\<^sub>B :: BT) t2"
  proof -
    have "lessBT (0\<^sub>B :: BT) (Dpt (enat ub) 0\<^sub>B)" by simp
    thus ?thesis using base0 lessBT_trans by blast
  qed
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0Z base1]
  have ordlo: "leBT (?W j) (?A j)" for j using IL by blast
  have ordhi: "leBT (?A j) (?W (Suc j))" for j using IL by blast
  have fins: "flatBT (d4vx_ins s0 ub b0 X) = s0 @ flatBP (DB (enat ub) X) @ b0" for X
    using d4vx_ins_flat[OF wrap b0RP] by simp
  have inv: "isOT_BT (?A j) \<and> b1x_triG (Dpt \<infinity> (?W j)) (?A j) (?W (Suc j))" for j
  proof (induction j)
    case 0
    show ?case using t2OT tri0 by simp
  next
    case (Suc j)
    have Aot: "isOT_BT (?A j)"
      and TRIj: "b1x_triG (Dpt \<infinity> (?W j)) (?A j) (?W (Suc j))"
      using Suc.IH by blast+
    have nub: "isOT_BP (DB (enat ub) (?A j))"
      by (rule otx3_pOT[OF Xub Xub Aot ordlo ordhi TRIj])
    have fW: "flatBT (?W (Suc j)) = s0 @ flatBP (DB (enat ub) (?W j)) @ b0"
      using fins[of "?W j"] by simp
    have fA: "flatBT (?A (Suc j)) = s0 @ flatBP (DB (enat ub) (?A j)) @ b0"
      using fins[of "?A j"] by simp
    have fW2: "flatBT (?W (Suc (Suc j)))
                 = s0 @ flatBP (DB (enat ub) (?W (Suc j))) @ b0"
      using fins[of "?W (Suc j)"] by simp
    from otx3_core_tri[OF fW fA fW2 b0RP Wot Wot nub ordlo ordhi TRIj]
    have "isOT_BT (?A (Suc j))
        \<and> b1x_triG (Dpt \<infinity> (?W (Suc j))) (?A (Suc j)) (?W (Suc (Suc j)))"
      by blast
    thus ?case by blast
  qed
  show ?thesis using inv by blast
qed


(* ===== r59 OTint: A0OT CLOSED => OTA1 pillar done (front A) + SETLE1 body-driver (front B) ===== *)


(* ===================================================================== *)
(* r59 A0OT-closure (front A0OT): the LAST OTA1 residual.                 *)
(*   STEP 1  od4_OTpred_mono_RT   : the RT_PS (not ST_PS) mono OT step.   *)
(*   helper  otx_bpHeadT_OT       : bpHeadT of an OT_B term is OT.        *)
(*   STEP 2-4 ot1_A0OT            : A0OT via the REDUCED slice            *)
(*             Red (s84x_N N) \<in> RT_PS (the raw slice need not be reduced). *)
(*   capstone oi8_census_final    : both pillars modulo                   *)
(*             {SETLE1_ltJ, IVADMEQ, FINRC}.                              *)
(* ===================================================================== *)

text \<open>STEP 1 --- @{text od4_OTpred_mono_RT}: the mono \<open>Trans (Pred M) \<in> OT\<^bsub>B\<^esub>\<close>
  step, VERBATIM from @{thm [source] od4_OTpred_mono} but with the \<open>ST\<^bsub>PS\<^esub>\<close>
  hypothesis replaced by the strictly weaker \<open>RT\<^bsub>PS\<^esub> \<and> PT\<^bsub>PS\<^esub>\<close> pair (the deleted
  lines only served to derive \<open>MR/MP\<close>, everything below uses only \<open>MR/MP/mono\<close>).\<close>

lemma od4_OTpred_mono_RT:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS" and mono: "monoT M"
    and L: "1 < Lng M" and hostOT: "Trans M \<in> OT_B"
  shows "Trans (Pred M) \<in> OT_B"
proof -
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predTB: "Trans (Pred M) \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF predRT])
  show ?thesis
  proof (cases "Trans (Pred M) = 0\<^sub>B")
    case True
    thus ?thesis using otx_OT_B_zero by simp
  next
    case T1ne: False
    show ?thesis
    proof (cases "Lng M = 2")
      case L2: True
      have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
      have LP1: "Lng (Pred M) = 1" using L2 by (simp add: Pred_def)
      obtain v where pv: "Pred M = [(v, v)]"
        using m_6_6_oneColumn[OF predT] predRT LP1 by auto
      have tv: "Trans (Pred M) = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using pv Trans_singleton by simp
      show ?thesis
        using tv otx_OT_B_zero m_8_7_OT_ex1[of v] by (cases "v = 0") simp_all
    next
      case False
      have j1gt: "1 < Lng M - 1" using L False by linarith
      have T1: "transT1 M \<noteq> 0\<^sub>B" using T1ne by (simp add: transT1_def)
      have R: "od4_R (Trans (Pred M)) (Trans M)"
        by (rule od4_master_R[OF MR MP j1gt T1])
      show ?thesis by (rule od4_R_OT_B[OF R hostOT predTB])
    qed
  qed
qed

text \<open>Helper --- @{text otx_bpHeadT_OT}: the principal body of an \<open>OT\<^bsub>B\<^esub>\<close> term is
  itself \<open>OT\<close> (\<open>isOT_BP\<close> at the head yields \<open>isOT_BT\<close> of its body; the \<open>0\<^bsub>B\<^esub>\<close> head
  is \<open>OT\<close> by (OT1)).\<close>

lemma otx_bpHeadT_OT:
  assumes "X \<in> OT_B"
  shows "isOT_BT (bpHeadT X)"
proof -
  have XOT: "isOT_BT X" using assms by (simp add: OT_B_def OT_def)
  obtain ps where Xps: "X = Trm ps" by (cases X)
  show ?thesis
  proof (cases ps)
    case Nil
    thus ?thesis using Xps by simp
  next
    case (Cons p rest)
    obtain v t where pvt: "p = DB v t" by (cases p)
    have "isOT_BP (DB v t)" using XOT Xps Cons pvt by auto
    hence "isOT_BT t" by simp
    thus ?thesis using Xps Cons pvt by simp
  qed
qed

text \<open>STEP 2-4 --- @{text ot1_A0OT}: the LAST OTA1 residual
  \<open>A0OT = isOT_BT (bpHeadT (Trans (Pred (s84x_N N))))\<close>, discharged UNCONDITIONALLY
  from the census premises.  The raw census slice \<open>s84x_N N\<close> need NOT be reduced;
  we route through its reduction \<open>RN = Red (s84x_N N) \<in> RT\<^bsub>PS\<^esub>\<close> (which shares its
  \<open>Trans\<close> value), apply the RT_PS mono OT step @{thm [source] od4_OTpred_mono_RT}
  to \<open>RN\<close>, and transport back along @{thm [source] m_7_4_Trans_PredN}
  (\<open>Trans (Pred RN) = Trans (seg N j\<^sub>-\<^sub>3 (Lng N - 2)) = Trans (Pred (s84x_N N))\<close>).
  \<open>Trans RN \<in> OT\<^bsub>B\<^esub>\<close> is the deep-graft body OT-ness, read off the scb-subterm
  \<open>D\<^bsub>e\<^sub>3\<^esub> body\<close> of \<open>Trans N\<close> (the census kind-1 position) by OT-heredity
  @{thm [source] m_8_7_OT_scb_recursive}.\<close>

lemma ot1_A0OT:
  fixes N :: pairseq
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ihOT: "Trans N \<in> OT_B"
    and ltJ: "s84x_jm3 N < transJm1 N"
  shows "isOT_BT (bpHeadT (Trans (Pred (s84x_N N))))"
proof -
  let ?e3 = "entry N 1 (s84x_jm3 N)"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  let ?S = "seg N (s84x_jm3 N) (Lng N - 1)"
  let ?RN = "Red ?S"
  have MR: "N \<in> RT_PS" using NST m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "N \<in> T_PS" using MR by (simp add: RT_PS_def)
  have mono: "monoT N" using NPT by (simp add: PT_PS_def)
  have Lgt: "1 < Lng N" using j1gt by linarith
  \<comment> \<open>slice geometry\<close>
  have jm2lt: "s84x_jm2 N < Lng N - 1" by (rule s84c1_jm2_basic(1)[OF hp])
  have jm3le: "s84x_jm3 N \<le> s84x_jm2 N" using adm_Adm_le by (simp add: s84x_jm3_def)
  have jm3lt: "s84x_jm3 N < Lng N - 1" using jm3le jm2lt by linarith
  have mM3: "(N, s84x_jm3 N) \<in> Marked" using s84d_jm3_Marked(1)[OF MR MT hp] by simp
  have leR3: "leR N 0 (s84x_jm3 N) (Lng N - 1)" using mM3 by (simp add: Marked_def)
  have jm1lt: "transJm1 N < Lng N - 1" using s84d_jm1_Marked(2)[OF MR NPT Lgt] by simp
  have jm3int: "s84x_jm3 N < Lng N - 2" using ltJ jm1lt j1gt by linarith
  have LNlen: "Lng ?S = Suc (Lng N - 1) - s84x_jm3 N"
    by (simp add: seg_def del: upt_Suc)
  have LN0: "(0::nat) < Lng ?S" using LNlen jm3lt by linarith
  \<comment> \<open>reduced-slice facts (the raw slice need not be reduced)\<close>
  have segT: "?S \<in> T_PS"
    using slice_Red_in_RT_PS[OF MR jm3lt order.refl leR3] by simp
  have RN_RT: "?RN \<in> RT_PS"
    using slice_Red_in_RT_PS[OF MR jm3lt order.refl leR3] by simp
  have RN_mono: "monoT ?RN"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR jm3lt order.refl leR3] by simp
  have RN_T: "?RN \<in> T_PS" using RN_RT by (simp add: RT_PS_def)
  have RN_PT: "?RN \<in> PT_PS" using RN_T RN_mono by (simp add: PT_PS_def)
  have RN_Lng: "1 < Lng ?RN"
  proof -
    have a: "Lng ?RN = Lng ?S" by (rule m_6_5_Lng_Red[OF segT])
    show ?thesis using a LNlen jm3lt Lgt by linarith
  qed
  \<comment> \<open>the slice \<open>Trans\<close> equals its reduction's \<open>Trans\<close>\<close>
  have TeqR: "Trans ?S = Trans ?RN"
    by (rule Trans_slice_eq_Red[OF MR jm3lt order.refl leR3])
  \<comment> \<open>STEP 3: \<open>Trans RN \<in> OT\<^bsub>B\<^esub>\<close> via the census kind-1 scb-subterm of \<open>Trans N\<close>\<close>
  obtain s0 b0 s1 b1 where
    k1: "scb_kind1 (Trans N) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  have scbd: "scb_decomp (Trans N) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    using k1 by (simp add: scb_kind1_def)
  have TReq: "Trans ?RN = Dpt (enat (entry ?RN 1 0)) (bpHeadT (Trans ?RN))"
    by (rule e2x_Trans_principal_head[OF RN_RT RN_mono])
  have e_RN: "entry ?RN 1 0 = ?e3"
  proof -
    have "entry ?RN 1 0 = entry ?S 1 0" by (rule m_6_6_Red_leftend_1[OF segT])
    also have "\<dots> = ?e3" using entry_seg[OF LN0, of 1] by simp
    finally show ?thesis .
  qed
  have bodyR: "bpHeadT (Trans ?RN) = ?body"
  proof -
    have "bpHeadT (Trans ?RN) = bpHeadT (Trans ?S)" using TeqR by simp
    also have "\<dots> = ?body" by (simp add: s84x_N_def)
    finally show ?thesis .
  qed
  have TR_princ: "Trans ?RN = Dpt (enat ?e3) ?body"
    using TReq e_RN bodyR by simp
  have RN_TB: "Trans ?RN \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF RN_RT])
  have DptTB: "Dpt (enat ?e3) ?body \<in> T_B" using RN_TB TR_princ by simp
  have DptOT: "Dpt (enat ?e3) ?body \<in> OT"
    by (rule m_8_7_OT_scb_recursive[OF ihOT DptTB scbd])
  have RN_TransOT: "Trans ?RN \<in> OT_B"
    using DptOT TR_princ RN_TB by (simp add: OT_B_def)
  \<comment> \<open>STEP 1 applied to the reduced slice\<close>
  have predOT: "Trans (Pred ?RN) \<in> OT_B"
    by (rule od4_OTpred_mono_RT[OF RN_RT RN_PT RN_mono RN_Lng RN_TransOT])
  \<comment> \<open>transport: \<open>Trans (Pred RN) = Trans (Pred (s84x_N N))\<close>\<close>
  have blN: "Pred (s84x_N N) = seg N (s84x_jm3 N) (Lng N - 2)"
  proof -
    have LN: "Lng (s84x_N N) = Suc (Lng N - 1) - s84x_jm3 N"
      by (simp add: s84x_N_def seg_def del: upt_Suc)
    have "1 < Lng (s84x_N N)" using LN jm3lt Lgt by linarith
    hence "Pred (s84x_N N) = butlast (s84x_N N)" by (simp add: Pred_def)
    also have "\<dots> = seg N (s84x_jm3 N) (Lng N - 1 - 1)"
      using s84c2_seg_butlast[OF jm3lt] by (simp add: s84x_N_def)
    also have "Lng N - 1 - 1 = Lng N - 2" by simp
    finally show ?thesis .
  qed
  have predEq: "Trans (Pred ?RN) = Trans (Pred (s84x_N N))"
  proof -
    have "Trans (Pred ?RN) = Trans (seg N (s84x_jm3 N) (Lng N - 2))"
      by (rule m_7_4_Trans_PredN[OF mM3 MR jm3int])
    also have "\<dots> = Trans (Pred (s84x_N N))" by (simp add: blN)
    finally show ?thesis .
  qed
  have predOTfinal: "Trans (Pred (s84x_N N)) \<in> OT_B"
    using predOT predEq by simp
  \<comment> \<open>STEP 4: read off the principal head\<close>
  show ?thesis by (rule otx_bpHeadT_OT[OF predOTfinal])
qed

text \<open>CAPSTONE --- @{text oi8_census_final}: the ltJ-threaded master census with
  the A0OT residual now DISCHARGED by @{thm [source] ot1_A0OT}.  Both termination
  pillars hold modulo exactly the three remaining residuals
  \<open>{SETLE1_ltJ, IVADMEQ, FINRC}\<close> (the OTA1 pillar is CLOSED).\<close>

theorem oi8_census_final:
  assumes SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and IVADMEQ: "\<And>P n. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow> transCondIV P \<Longrightarrow>
        Adm P (s84x_jm2 P) = transJm1 P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow> 1 < n \<Longrightarrow>
        Trans ((P::pairseq)[n]) \<in> OT_B"
    and FINRC: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             transCondII K \<Longrightarrow> tvx_finRc K"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi8_census_via_A0OT(1)[OF ot1_A0OT SETLE1 IVADMEQ FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi8_census_via_A0OT(2)[OF ot1_A0OT SETLE1 IVADMEQ FINRC])
qed



(* ===================================================================== *)
(* r59 SETLE1_ltJ (prefix ox5_): the ltJ-guarded census setle residual.    *)
(*   TARGET: b1x_setle (GBT u A1) (insert X1 (GBT u X1)),                   *)
(*     A1 = d4vx_ins s0 ub b0 A0, X1 = d4vx_ins s0 ub b0 X0,                *)
(*     A0 = bpHeadT(Trans(Pred(s84x_N P))), X0 = Dpt ub 0, ub = v1-1.       *)
(*                                                                         *)
(*   STEP-0 FINDING (python/_r59_setle1_step0.py, 119877 base0&base1 hosts): *)
(*     * body driver BE'  : forall u.  G(u,A0) <= {X1} u G(u,X1)  -- 0/119877  *)
(*         FAIL  (TRUE, ox5_body_driver below, from tri0=ot1_tri0_census).   *)
(*     * FULL target setle: 53669/119877 FAIL for GENERAL OT A0 !!           *)
(*     * spine bound lbA<=X1: 55751/119877 FAIL.                            *)
(*   i.e. the naive all-u setle is FALSE without a HEAD-STRUCTURE bound on   *)
(*   A0: A0's rightmost-spine escape heads (transV) can EXCEED X1's outer    *)
(*   head, so the spine-body escapes of A1 are NOT <= any member of         *)
(*   {X1} u G(u,X1).  Concrete CEX (wrap=[D_2 .], tv=4, ub=1, t2=0):         *)
(*     A0=[D_2[D_4 0]], X1=[D_2[D_4[D_1[D_1 0]]]]; base0,base1,ordlo,ordhi   *)
(*     all hold, yet at u=0 the escape [D_4[D_1 A0]] in G(0,A1) exceeds X1.  *)
(*   The 899/899 last-round validation therefore relied on A0 being a real   *)
(*   Trans-image (bpHeadT(Trans(Pred ..))), whose right-spine head structure  *)
(*   bounds transV; ot1_SETLE1_ltJ CANNOT be closed from base0/base1/tri0    *)
(*   alone.  See the ox5_ obstruction note at end of block.                 *)
(* ===================================================================== *)

subsection \<open>The body driver \<open>BE'\<close> (hole-body domination, from \<open>tri0\<close>)\<close>

text \<open>@{text ox5_body_driver}: every \<open>G\<^sub>u\<close>-member of the hole body \<open>A\<^sub>0\<close> is
  \<open>\<le>\<close> some member of \<open>{X\<^sub>1} \<union> G\<^sub>u X\<^sub>1\<close>.  This is the CLEAN piece of the SETLE1
  residual: it is exactly the \<open>c = X\<^sub>1\<close> instance of the census G-control brick
  \<open>tri0 = b1x_triG z A\<^sub>0 X\<^sub>1\<close> (@{thm [source] ot1_tri0_census}, any \<open>z\<close>) at
  \<open>z = 0\<close>, folded against \<open>base\<^sub>1 = A\<^sub>0 < X\<^sub>1\<close>: \<open>G\<^sub>u A\<^sub>0 \<preceq> G\<^sub>u X\<^sub>1 \<union> {0}\<close>, and
  \<open>0 \<le> X\<^sub>1\<close> (as \<open>X\<^sub>1 \<noteq> 0\<close>).  STEP-0 confirms it holds on all 119877 hosts.
  Abstract in \<open>(A\<^sub>0, X\<^sub>1)\<close> so a census wrapper can supply the two inputs.\<close>

lemma ox5_body_driver:
  fixes A0 X1 :: BT and u :: enat
  assumes tri0: "\<And>z. b1x_triG z A0 X1"
    and base1: "lessBT A0 X1"
    and X1ne: "X1 \<noteq> Trm []"
  shows "b1x_setle (GBT u A0) (insert X1 (GBT u X1))"
proof -
  have leA0X1: "leBT A0 X1" using base1 by blast
  have step: "b1x_setle (GBT u A0) (GBT u X1 \<union> GBT u (Trm []) \<union> {Trm []})"
    by (rule b1x_triG_D[OF tri0[of "Trm []"] leA0X1]) simp
  have step': "b1x_setle (GBT u A0) (GBT u X1 \<union> {Trm []})"
    using step by simp
  show ?thesis
    unfolding b1x_setle_def
  proof
    fix x assume "x \<in> GBT u A0"
    then obtain y where yin: "y \<in> GBT u X1 \<union> {Trm []}" and xy: "leBT x y"
      using step' unfolding b1x_setle_def by blast
    show "\<exists>z \<in> insert X1 (GBT u X1). leBT x z"
    proof (cases "y \<in> GBT u X1")
      case True
      thus ?thesis using xy by blast
    next
      case False
      hence "y = Trm []" using yin by blast
      hence "x = Trm []" using xy by (cases x) auto
      moreover have "lessBT (Trm []) X1" using X1ne by simp
      ultimately show ?thesis by blast
    qed
  qed
qed

text \<open>@{text ox5_body_driver_census}: the census-level instance of
  @{thm [source] ox5_body_driver} \<mdash> \<open>tri0\<close> from @{thm [source] ot1_tri0_census}
  and \<open>base\<^sub>1\<close> from @{thm [source] oi5_IIIIV_pkg} (the given \<open>(s\<^sub>0,b\<^sub>0)\<close> is pinned
  to the package's by \<open>scb\<close>-uniqueness inside \<open>crx/cnv_tri0_of_nest\<close>, so the
  two \<open>X\<^sub>1\<close> coincide).\<close>

lemma ox5_body_driver_census:
  fixes N :: pairseq and s0 b0 :: "Sym list" and u :: enat
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                 (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
  shows "b1x_setle
           (GBT u (bpHeadT (Trans (Pred (s84x_N N)))))
           (insert (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                      0\<^sub>B)
                   (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                             0\<^sub>B)))"
proof -
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X1 = "d4vx_ins s0 ?ub b0 0\<^sub>B"
  have tri0: "\<And>z. b1x_triG z ?A0 ?X1"
    by (rule oy1_tri0Y_census[OF NST NPT hp j1gt branch ltJ inner])
  \<comment> \<open>\<open>base\<^sub>1\<close> and the \<open>flat\<close> wrapper from the package (given \<open>(s\<^sub>0,b\<^sub>0)\<close> pinned)\<close>
  obtain s0' b0' s1 b1 where
      b0RP': "\<forall>x \<in> set b0'. x = RP"
    and inner': "scb_decomp (bpHeadT (Trans (s84x_N N))) s0'
         (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0'"
    and base1': "lessBT ?A0 (d4vx_ins s0' ?ub b0' 0\<^sub>B)"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  \<comment> \<open>\<open>(s\<^sub>0,b\<^sub>0)\<close> pinned by \<open>scb\<close>-uniqueness of the shared hole\<close>
  have bodyne: "bpHeadT (Trans (s84x_N N)) \<noteq> Trm []"
  proof
    assume z: "bpHeadT (Trans (s84x_N N)) = Trm []"
    have "flatBT (bpHeadT (Trans (s84x_N N)))
            = s0 @ flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B) @ b0"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0 @ [Dsym (enat (entry N 1 (Lng N - 1))), Zsym] @ b0"
      using z by simp
    thus False by (cases s0) auto
  qed
  have pin: "s0 = s0' \<and> b0 = b0'"
    by (rule m_7_2_scb_unique_sb[OF inner inner' bodyne])
  have X1eq: "?X1 = d4vx_ins s0' ?ub b0' 0\<^sub>B" using pin by simp
  have base1: "lessBT ?A0 ?X1" using base1' X1eq by simp
  have X1ne: "?X1 \<noteq> Trm []" using base1 by (cases ?A0) auto
  show ?thesis by (rule ox5_body_driver[OF tri0 base1 X1ne])
qed


(* ===== r60 OTint: IVADMEQ CLOSED (front B) + SETLE1 head-guarded engine ox6_ (front A) ===== *)


(* ===================================================================== *)
(* r60 SETLE1_ltJ (prefix ox6_): the head-guarded scbext-setle descent.   *)
(*                                                                        *)
(*   STEP-0 r60 (python/_r60_setle1_step0.py, REAL census hosts only,     *)
(*     A0 = bpHeadT(Trans(Pred(s84x_N N)))):                              *)
(*     * FULL setle target  b1x_setle (GBT u A1) (insert X1 (GBT u X1))   *)
(*         HOLDS 146/146 real hosts, 0 fail (r59's 899/899 confirmed).    *)
(*     * stronger POINTWISE head bound (H): every escape y in GBT u A1    *)
(*         has  leBT y X1  OR  y in GBT u X1  --- HOLDS 146/146, 0 fail.  *)
(*   So (H) is the EXACT tight invariant on real hosts.  (The r59 finding *)
(*   stands: for a general OT A0 satisfying only base0/base1, the target  *)
(*   is FALSE --- 53669/119877 fail --- because A0's wrapper right-spine  *)
(*   ancestor heads (transV) can EXCEED X1's head.  Real hosts are safe.) *)
(*                                                                        *)
(*   ROUTE (setle analogue of scbext_triG, via otx2_align3 spine peel):   *)
(*   the census target b1x_setle (GBT u A1) (insert X1 (GBT u X1)) with   *)
(*   A1 = d4vx_ins s0 ub b0 A0, X1 = d4vx_ins s0 ub b0 0\<^sub>B (SHARED wrapper) *)
(*   reduces, by right-spine induction on the wrapper, to exactly THREE   *)
(*   escape families:                                                     *)
(*     (i)   the HOLE escapes GBP u (D_ub A0): dominated via              *)
(*           ox5_body_driver + base1 (= ox6_holeH);                       *)
(*     (ii)  the SHARED wrapper escapes (identical qs-principals of A1     *)
(*           and X1): already in GBT u X1;                                *)
(*     (iii) the right-spine ANCESTOR bodies lbA (at each deeper peel      *)
(*           level, flatBT lbA = sc @ flatBP (D_ub A0) @ bc): need         *)
(*           leBT lbA X1 --- the SPINE HEAD BOUND (spineH), threaded as a  *)
(*           CONSTANT since ancestors-of-lbA are ancestors-of-A1.          *)
(*   The engine ox6_setle_scbext discharges (i)+(ii) unconditionally and  *)
(*   reduces the residual to spineH.  ox6_setle_wrapped packages it for    *)
(*   the d4vx_ins wrapper; ox6_SETLE1_reduce feeds the census (i)/(ii).    *)
(*                                                                        *)
(*   OBSTRUCTION (open): spineH = "every right-spine ancestor body of A1   *)
(*   is leBT X1".  STEP-0 confirms it (146/146) but discharging it needs   *)
(*   the sec7.4 Mark/RightAnces right-spine head structure of the real     *)
(*   Trans-image body = bpHeadT(Trans(s84x_N N)); see the note at end.     *)
(*                                                                        *)
(*   CAVEAT on spineH's shape (honesty): the engine hypothesis is written  *)
(*   universally over ALL (t',sc,bc) with flatBT t' = sc @ flatBP(D_ub A0) *)
(*   @ bc (bc all-RP) and size t' < size A1.  This UNIVERSAL form is        *)
(*   STRONGER than true: e.g. t' = Trm[D_BIG (.. D_ub A0 ..)] has small     *)
(*   tree-size yet head BIG > head X1, so t' > X1.  The TRUE (STEP-0) fact  *)
(*   is the ANCESTOR-RESTRICTED bound: only the finitely-many ACTUAL        *)
(*   right-spine ancestor bodies of A1 (sc a suffix of s0, bc a prefix of   *)
(*   b0) are leBT X1.  Closing SETLE1_ltJ therefore needs (a) the engine    *)
(*   re-threaded with the suffix/prefix restriction (derivable from a hole- *)
(*   position cancellation on the align3 peel), then (b) the sec7.4 head    *)
(*   bound for the actual ancestors.  ox6_setle_scbext is the reusable      *)
(*   spine-induction core; ox6_SETLE1_reduce localizes the residual.        *)
(* ===================================================================== *)

subsection \<open>The head-guarded scbext-setle descent engine \<open>ox6_setle_scbext\<close>\<close>

text \<open>@{text ox6_holeH}: the hole principal \<open>D\<^bsub>v\<^esub> A\<^sub>0\<close>'s \<open>G\<^sub>u\<close>-escapes are
  dominated by \<open>{X\<^sub>1} \<union> G\<^sub>u X\<^sub>1\<close>: \<open>A\<^sub>0\<close> itself by \<open>base\<^sub>1 = A\<^sub>0 < X\<^sub>1\<close>, and
  \<open>G\<^sub>u A\<^sub>0\<close> by the body driver @{thm [source] ox5_body_driver}.\<close>

lemma ox6_holeH:
  fixes A0 X1 :: BT and u v :: enat
  assumes ox5: "b1x_setle (GBT u A0) (insert X1 (GBT u X1))"
    and base1: "lessBT A0 X1"
  shows "b1x_setle (GBP u (DB v A0)) (insert X1 (GBT u X1))"
  unfolding b1x_setle_def
proof
  fix x assume xin: "x \<in> GBP u (DB v A0)"
  hence xd: "x = A0 \<or> x \<in> GBT u A0" by (auto split: if_split_asm)
  thus "\<exists>y\<in>insert X1 (GBT u X1). leBT x y"
  proof
    assume "x = A0" thus ?thesis using base1 by blast
  next
    assume "x \<in> GBT u A0" thus ?thesis using ox5 unfolding b1x_setle_def by blast
  qed
qed

text \<open>@{text ox6_setle_scbext}: the SETLE analogue of @{thm [source] scbext_triG}.
  \<open>t\<^sub>A\<close> and \<open>t\<^sub>X\<close> share the scb wrapper \<open>(s, b)\<close>, differing only at the hole
  principal (\<open>cp\<^sub>A\<close> resp. \<open>cp\<^sub>X\<close>).  By right-spine induction (via
  @{thm [source] otx2_align3}) every \<open>G\<^sub>u t\<^sub>A\<close> escape is: a shared wrapper escape
  (in \<open>G\<^sub>u t\<^sub>X \<subseteq> G\<^sub>u B\<close>, @{text subXB}); a hole escape (@{text holeH}); or a
  right-spine ancestor body \<open>lbA\<close> with \<open>flatBT lbA = sc \<frown> flatBP cp\<^sub>A \<frown> bc\<close>,
  dominated by \<open>B\<close> via @{text spineH}.  \<open>B\<close> is a FIXED global bound (\<open>= X\<^sub>1\<close>);
  @{text spineH} is threaded unchanged since ancestors-of-\<open>lbA\<close> \<open>\<subseteq>\<close>
  ancestors-of-\<open>t\<^sub>A\<close> (guarded by the strict \<open>size\<close> drop).\<close>

lemma ox6_setle_scbext:
  fixes B :: BT and cpA cpX :: BP and u :: enat
  assumes holeH: "b1x_setle (GBP u cpA) (insert B (GBT u B))"
  shows "flatBT tA = s @ flatBP cpA @ b \<Longrightarrow>
         flatBT tX = s @ flatBP cpX @ b \<Longrightarrow>
         (\<forall>x\<in>set b. x = RP) \<Longrightarrow>
         GBT u tX \<subseteq> GBT u B \<Longrightarrow>
         (\<forall>t' sc bc. flatBT t' = sc @ flatBP cpA @ bc \<longrightarrow> (\<forall>x\<in>set bc. x = RP)
              \<longrightarrow> size t' < size tA \<longrightarrow> leBT t' B) \<Longrightarrow>
         b1x_setle (GBT u tA) (insert B (GBT u B))"
proof (induction tA arbitrary: tX s b rule: measure_induct_rule[where f=size])
  case (less tA)
  note fA = less.prems(1) and fX = less.prems(2) and bRP = less.prems(3)
    and subXB = less.prems(4) and spineH = less.prems(5)
  from otx2_align3[OF fA fX fX bRP]
  show ?case
  proof (elim disjE exE conjE)
    \<comment> \<open>Case A: the hole is the last top-level principal\<close>
    fix qs
    assume TA: "tA = Trm (qs @ [cpA])" and TX: "tX = Trm (qs @ [cpX])"
      and TX3: "tX = Trm (qs @ [cpX])"
    have qle: "(\<Union>q\<in>set qs. GBP u q) \<subseteq> GBT u B"
    proof -
      have "(\<Union>q\<in>set qs. GBP u q) \<subseteq> GBT u tX" using TX by auto
      thus ?thesis using subXB by blast
    qed
    show "b1x_setle (GBT u tA) (insert B (GBT u B))"
      unfolding b1x_setle_def
    proof
      fix x assume xin: "x \<in> GBT u tA"
      have "x \<in> (\<Union>q\<in>set qs. GBP u q) \<or> x \<in> GBP u cpA" using xin TA by auto
      thus "\<exists>y\<in>insert B (GBT u B). leBT x y"
      proof
        assume "x \<in> (\<Union>q\<in>set qs. GBP u q)"
        hence "x \<in> GBT u B" using qle by blast
        thus ?thesis by blast
      next
        assume "x \<in> GBP u cpA"
        thus ?thesis using holeH unfolding b1x_setle_def by blast
      qed
    qed
  next
    \<comment> \<open>Case B: the hole is nested one right-spine level deeper\<close>
    fix qs w lbA lbX lb3 sc bc
    assume TA: "tA = Trm (qs @ [DB w lbA])"
      and TX: "tX = Trm (qs @ [DB w lbX])"
      and TX3: "tX = Trm (qs @ [DB w lb3])"
      and FlbA: "flatBT lbA = sc @ flatBP cpA @ bc"
      and FlbX: "flatBT lbX = sc @ flatBP cpX @ bc"
      and Flb3: "flatBT lb3 = sc @ flatBP cpX @ bc"
      and bcRP: "\<forall>x\<in>set bc. x = RP"
    have pin: "DB w lbA \<in> set (qs @ [DB w lbA])" by simp
    have szp: "size (DB w lbA) \<le> size_list size (qs @ [DB w lbA])"
      by (rule size_list_estimation'[OF pin order_refl])
    have szlt: "size lbA < size tA" using szp TA by simp
    have qle: "(\<Union>q\<in>set qs. GBP u q) \<subseteq> GBT u B"
    proof -
      have "(\<Union>q\<in>set qs. GBP u q) \<subseteq> GBT u tX" using TX by auto
      thus ?thesis using subXB by blast
    qed
    have spineH': "\<forall>t' sc' bc'. flatBT t' = sc' @ flatBP cpA @ bc'
          \<longrightarrow> (\<forall>x\<in>set bc'. x = RP) \<longrightarrow> size t' < size lbA \<longrightarrow> leBT t' B"
    proof (intro allI impI)
      fix t' sc' bc'
      assume a1: "flatBT t' = sc' @ flatBP cpA @ bc'"
        and a2: "\<forall>x\<in>set bc'. x = RP" and a3: "size t' < size lbA"
      have "size t' < size tA" using a3 szlt by simp
      thus "leBT t' B" using spineH a1 a2 by blast
    qed
    show "b1x_setle (GBT u tA) (insert B (GBT u B))"
      unfolding b1x_setle_def
    proof
      fix x assume xin: "x \<in> GBT u tA"
      have "x \<in> (\<Union>q\<in>set qs. GBP u q) \<or> x \<in> GBP u (DB w lbA)"
        using xin TA by auto
      thus "\<exists>y\<in>insert B (GBT u B). leBT x y"
      proof
        assume "x \<in> (\<Union>q\<in>set qs. GBP u q)"
        hence "x \<in> GBT u B" using qle by blast
        thus ?thesis by blast
      next
        assume xh: "x \<in> GBP u (DB w lbA)"
        have uw: "u \<le> w" using xh by (auto split: if_split_asm)
        have xcase: "x = lbA \<or> x \<in> GBT u lbA" using xh by (auto split: if_split_asm)
        have lbXin: "lbX \<in> GBT u tX"
        proof -
          have "lbX \<in> GBP u (DB w lbX)" using uw by simp
          thus ?thesis using TX by auto
        qed
        have lbXB: "lbX \<in> GBT u B" using lbXin subXB by blast
        have subX': "GBT u lbX \<subseteq> GBT u B" using b1x_GBT_trans[OF lbXB] by blast
        from xcase show ?thesis
        proof
          assume "x = lbA"
          moreover have "leBT lbA B" using spineH FlbA bcRP szlt by blast
          ultimately show ?thesis by blast
        next
          assume xlbA: "x \<in> GBT u lbA"
          have "b1x_setle (GBT u lbA) (insert B (GBT u B))"
            by (rule less.IH[OF szlt FlbA FlbX bcRP subX' spineH'])
          thus ?thesis using xlbA unfolding b1x_setle_def by blast
        qed
      qed
    qed
  qed
qed

text \<open>@{text ox6_setle_wrapped}: the @{const d4vx_ins} packaging.  With
  \<open>B = X\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 X\<^sub>0\<close>, hole \<open>cp\<^sub>A = D\<^bsub>ub\<^esub> A\<^sub>0\<close>, \<open>cp\<^sub>X = D\<^bsub>ub\<^esub> X\<^sub>0\<close>,
  \<open>subXB\<close> is reflexivity and \<open>holeH\<close> is @{thm [source] ox6_holeH}; only \<open>spineH\<close>
  remains as an input.\<close>

lemma ox6_setle_wrapped:
  fixes A0 X0 W :: BT and hole :: BP and s0 b0 :: "Sym list" and ub :: nat and u :: enat
  assumes ox5: "b1x_setle (GBT u A0)
                  (insert (d4vx_ins s0 ub b0 0\<^sub>B) (GBT u (d4vx_ins s0 ub b0 0\<^sub>B)))"
    and base1: "lessBT A0 (d4vx_ins s0 ub b0 0\<^sub>B)"
    and wrap: "flatBT W = s0 @ flatBP hole @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and spineH: "\<forall>t' sc bc. flatBT t' = sc @ flatBP (DB (enat ub) A0) @ bc
          \<longrightarrow> (\<forall>x\<in>set bc. x = RP) \<longrightarrow> size t' < size (d4vx_ins s0 ub b0 A0)
          \<longrightarrow> leBT t' (d4vx_ins s0 ub b0 0\<^sub>B)"
  shows "b1x_setle (GBT u (d4vx_ins s0 ub b0 A0))
           (insert (d4vx_ins s0 ub b0 0\<^sub>B) (GBT u (d4vx_ins s0 ub b0 0\<^sub>B)))"
proof -
  let ?X1 = "d4vx_ins s0 ub b0 0\<^sub>B"
  let ?A1 = "d4vx_ins s0 ub b0 A0"
  have fA1: "flatBT ?A1 = s0 @ flatBP (DB (enat ub) A0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ub A0] by simp
  have fX1: "flatBT ?X1 = s0 @ flatBP (DB (enat ub) 0\<^sub>B) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ub "0\<^sub>B"] by simp
  have holeH: "b1x_setle (GBP u (DB (enat ub) A0)) (insert ?X1 (GBT u ?X1))"
    by (rule ox6_holeH[OF ox5 base1])
  show ?thesis
    by (rule ox6_setle_scbext[OF holeH fA1 fX1 b0RP subset_refl spineH])
qed

text \<open>@{text ox6_SETLE1_reduce}: the census-level SETLE1 residual reduced to the
  spine head bound.  Feeds \<open>ox5\<close> from @{thm [source] ox5_body_driver_census} and
  \<open>base\<^sub>1\<close>/\<open>wrap\<close> from @{thm [source] oi5_IIIIV_pkg}; \<open>spineH\<close> is the sole open input
  (STEP-0: 146/146 real hosts).  Its conclusion is EXACTLY the \<open>SETLE1\<close> slot of
  @{thm [source] oi8_census_final} / @{thm [source] oi8_OTint_IIIIV_hp} at \<open>u\<close>.\<close>

lemma ox6_SETLE1_reduce:
  fixes N :: pairseq and s0 b0 :: "Sym list" and u :: enat
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                 (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and spineH: "\<forall>t' sc bc.
          flatBT t' = sc @ flatBP (DB (enat (entry N 1 (Lng N - 1) - 1))
                                      (bpHeadT (Trans (Pred (s84x_N N))))) @ bc
          \<longrightarrow> (\<forall>x\<in>set bc. x = RP)
          \<longrightarrow> size t' < size (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                                (bpHeadT (Trans (Pred (s84x_N N)))))
          \<longrightarrow> leBT t' (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                        0\<^sub>B)"
  shows "b1x_setle
           (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                     (bpHeadT (Trans (Pred (s84x_N N))))))
           (insert (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                      0\<^sub>B)
                   (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                             0\<^sub>B)))"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X0 = "Dpt (enat ?ub) 0\<^sub>B"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  \<comment> \<open>the body driver \<open>ox5\<close>\<close>
  have ox5: "b1x_setle (GBT u ?A0)
               (insert (d4vx_ins s0 ?ub b0 0\<^sub>B) (GBT u (d4vx_ins s0 ?ub b0 0\<^sub>B)))"
    by (rule ox5_body_driver_census[OF NST NPT hp j1gt branch ltJ inner])
  \<comment> \<open>\<open>base\<^sub>1\<close> and the flat wrapper from the package (given \<open>(s\<^sub>0,b\<^sub>0)\<close> pinned)\<close>
  obtain s0' b0' s1 b1 where
      b0RP': "\<forall>x \<in> set b0'. x = RP"
    and inner': "scb_decomp ?body s0'
         (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0'"
    and base1': "lessBT ?A0 (d4vx_ins s0' ?ub b0' 0\<^sub>B)"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "flatBT ?body = s0 @ flatBT (Dpt (enat ?v1) 0\<^sub>B) @ b0"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0 @ [Dsym (enat ?v1), Zsym] @ b0" using z by simp
    thus False by (cases s0) auto
  qed
  have pin: "s0 = s0' \<and> b0 = b0'"
    by (rule m_7_2_scb_unique_sb[OF inner inner' bodyne])
  have base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 0\<^sub>B)" using base1' pin by simp
  have b0RP: "\<forall>x \<in> set b0. x = RP" using b0RP' pin by simp
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  show ?thesis
    by (rule ox6_setle_wrapped[OF ox5 base1 wrap b0RP spineH])
qed



(* ===================================================================== *)
(* r60 IVADMEQ-residual (prefix ot2_): close the condIV admeq OT step   *)
(*   Trans(P[n]) in OT_B, discharging the {d1,d2,d3,HB} residual of      *)
(*   ot2_IVADMEQ_mod from the Red-slice regime machinery, and the        *)
(*   NEWOT/SETLE via the SETLE-FREE tower engine (ot2_tower_newOT +       *)
(*   ot2_tower_inv + otx3_core_tri), supplying t2OT and tri0.            *)
(*                                                                       *)
(*   KEY SUBTLETY: the regime facts REGS/REGSP are guarded by            *)
(*   s84x_jm3 M < s84x_jm2 M.  At the admeq corner where jm3 = jm2 the   *)
(*   guard is vacuous, but cpx_d2_condIV/cpx_d3_condIV case-split on it   *)
(*   internally (equality branch: s84x_Np = s84x_N, e1jm2 = e1jm1), so   *)
(*   NO jm3=jm2-aware variant is needed --- the existing (frozen,        *)
(*   proven) dispatchers already cover both corners.                     *)
(* ===================================================================== *)

text \<open>@{text ot2_transT2_OT}: the tower-seed OT fact \<open>isOT\<^bsub>BT\<^esub>(transT2 M)\<close>
  at the condIV admeq host.  Mirrors @{thm [source] ot1_A0OT} but is ltJ-FREE:
  the census kind-1 scb position is supplied by @{thm [source] c4dx_condIV_k1}
  (needs only \<open>admeq\<close>, not \<open>ltJ\<close>), and \<open>jm3 < Lng-2\<close> comes from
  @{thm [source] s84d_L5_rng} (\<open>jm2+1 < Lng-1\<close>) via \<open>jm3 \<le> jm2\<close>.  Route:
  \<open>Trans (Red (s84x_N M)) \<in> OT\<^bsub>B\<^esub>\<close> (deep-graft body OT via
  @{thm [source] m_8_7_OT_scb_recursive}) \<open>\<rightarrow>\<close> RT-mono predecessor OT step
  @{thm [source] od4_OTpred_mono_RT} \<open>\<rightarrow>\<close> transport
  (@{thm [source] m_7_4_Trans_PredN}) to \<open>Trans (Pred (s84x_N M)) = transC1 M
  = D\<^bsub>e1jm1\<^esub>(transT2 M)\<close> (@{thm [source] w84x_PN_c1_of_admeq},
  @{thm [source] m_8_5_scbdec_c1_shape}), whose principal body is \<open>transT2 M\<close>.\<close>

lemma ot2_transT2_OT:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and cIV: "transCondIV M"
    and admeq: "Adm M (s84x_jm2 M) = transJm1 M"
    and ihOT: "Trans M \<in> OT_B"
  shows "isOT_BT (transT2 M)"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?S = "seg M (s84x_jm3 M) (Lng M - 1)"
  let ?RN = "Red ?S"
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have nVI: "\<not> transCondVI M" using c4dx_condIV_excl(4)[OF cIV] .
  have T1: "transT1 M \<noteq> 0\<^sub>B" using s84d_L4_regime[OF MST MPT hp nVI] by simp
  have j1gt: "1 < Lng M - 1" using s84d_L4_regime[OF MST MPT hp nVI] by simp
  have J1pos: "transJ1 M > 0" using j1gt by (simp add: transJ1_def)
  have Lgt: "1 < Lng M" using j1gt by linarith
  have rng: "s84x_jm2 M + 1 < Lng M - 1" by (rule s84d_L5_rng[OF MST MPT hp nVI])
  \<comment> \<open>slice geometry\<close>
  have jm2lt: "s84x_jm2 M < Lng M - 1" by (rule s84c1_jm2_basic(1)[OF hp])
  have jm3le: "s84x_jm3 M \<le> s84x_jm2 M" using adm_Adm_le by (simp add: s84x_jm3_def)
  have jm3lt: "s84x_jm3 M < Lng M - 1" using jm3le jm2lt by linarith
  have mM3: "(M, s84x_jm3 M) \<in> Marked" using s84d_jm3_Marked(1)[OF MR MT hp] by simp
  have leR3: "leR M 0 (s84x_jm3 M) (Lng M - 1)" using mM3 by (simp add: Marked_def)
  have jm2m2: "s84x_jm2 M < Lng M - 2" using rng by linarith
  have jm3int: "s84x_jm3 M < Lng M - 2" using jm3le jm2m2 by linarith
  have LNlen: "Lng ?S = Suc (Lng M - 1) - s84x_jm3 M"
    by (simp add: seg_def del: upt_Suc)
  have LN0: "(0::nat) < Lng ?S" using LNlen jm3lt by linarith
  \<comment> \<open>reduced-slice facts\<close>
  have segT: "?S \<in> T_PS"
    using slice_Red_in_RT_PS[OF MR jm3lt order.refl leR3] by simp
  have RN_RT: "?RN \<in> RT_PS"
    using slice_Red_in_RT_PS[OF MR jm3lt order.refl leR3] by simp
  have RN_mono: "monoT ?RN"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR jm3lt order.refl leR3] by simp
  have RN_T: "?RN \<in> T_PS" using RN_RT by (simp add: RT_PS_def)
  have RN_PT: "?RN \<in> PT_PS" using RN_T RN_mono by (simp add: PT_PS_def)
  have RN_Lng: "1 < Lng ?RN"
  proof -
    have a: "Lng ?RN = Lng ?S" by (rule m_6_5_Lng_Red[OF segT])
    show ?thesis using a LNlen jm3lt Lgt by linarith
  qed
  have TeqR: "Trans ?S = Trans ?RN"
    by (rule Trans_slice_eq_Red[OF MR jm3lt order.refl leR3])
  \<comment> \<open>\<open>Trans RN \<in> OT\<^bsub>B\<^esub>\<close> via the census kind-1 scb-subterm of \<open>Trans M\<close>\<close>
  have k1: "scb_kind1 (Trans M) (s84x_s1 M)
             (flatBT (Dpt (enat ?e3) (bpHeadT (transC2 M)))) (s84x_b1 M)"
    by (rule c4dx_condIV_k1[OF MST MPT hp cIV admeq])
  have scbd: "scb_decomp (Trans M) (s84x_s1 M)
                (flatBT (Dpt (enat ?e3) (bpHeadT (transC2 M)))) (s84x_b1 M)"
    using k1 by (simp add: scb_kind1_def)
  have TReq: "Trans ?RN = Dpt (enat (entry ?RN 1 0)) (bpHeadT (Trans ?RN))"
    by (rule e2x_Trans_principal_head[OF RN_RT RN_mono])
  have e_RN: "entry ?RN 1 0 = ?e3"
  proof -
    have "entry ?RN 1 0 = entry ?S 1 0" by (rule m_6_6_Red_leftend_1[OF segT])
    also have "\<dots> = ?e3" using entry_seg[OF LN0, of 1] by simp
    finally show ?thesis .
  qed
  have TNc2: "Trans (s84x_N M) = transC2 M"
    by (rule w84x_TN_c2_of_admeq[OF MST MPT hp nVI admeq])
  have bodyR: "bpHeadT (Trans ?RN) = bpHeadT (transC2 M)"
  proof -
    have "bpHeadT (Trans ?RN) = bpHeadT (Trans ?S)" using TeqR by simp
    also have "\<dots> = bpHeadT (Trans (s84x_N M))" by (simp add: s84x_N_def)
    also have "\<dots> = bpHeadT (transC2 M)" using TNc2 by simp
    finally show ?thesis .
  qed
  have TR_princ: "Trans ?RN = Dpt (enat ?e3) (bpHeadT (transC2 M))"
    using TReq e_RN bodyR by simp
  have RN_TB: "Trans ?RN \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF RN_RT])
  have DptTB: "Dpt (enat ?e3) (bpHeadT (transC2 M)) \<in> T_B" using RN_TB TR_princ by simp
  have DptOT: "Dpt (enat ?e3) (bpHeadT (transC2 M)) \<in> OT"
    by (rule m_8_7_OT_scb_recursive[OF ihOT DptTB scbd])
  have RN_TransOT: "Trans ?RN \<in> OT_B"
    using DptOT TR_princ RN_TB by (simp add: OT_B_def)
  \<comment> \<open>RT-mono predecessor OT step on the reduced slice\<close>
  have predOT: "Trans (Pred ?RN) \<in> OT_B"
    by (rule od4_OTpred_mono_RT[OF RN_RT RN_PT RN_mono RN_Lng RN_TransOT])
  \<comment> \<open>transport back: \<open>Trans (Pred RN) = Trans (Pred (s84x_N M)) = transC1 M\<close>\<close>
  have predEq: "Trans (Pred ?RN) = Trans (seg M (s84x_jm3 M) (Lng M - 2))"
    by (rule m_7_4_Trans_PredN[OF mM3 MR jm3int])
  have blN: "Pred (s84x_N M) = seg M (s84x_jm3 M) (Lng M - 2)"
  proof -
    have LN: "Lng (s84x_N M) = Suc (Lng M - 1) - s84x_jm3 M"
      by (simp add: s84x_N_def seg_def del: upt_Suc)
    have "1 < Lng (s84x_N M)" using LN jm3lt Lgt by linarith
    hence "Pred (s84x_N M) = butlast (s84x_N M)" by (simp add: Pred_def)
    also have "\<dots> = seg M (s84x_jm3 M) (Lng M - 1 - 1)"
      using s84c2_seg_butlast[OF jm3lt] by (simp add: s84x_N_def)
    also have "Lng M - 1 - 1 = Lng M - 2" by simp
    finally show ?thesis .
  qed
  have predPNOT: "Trans (Pred (s84x_N M)) \<in> OT_B"
    using predOT predEq blN by simp
  have PNc1: "Trans (Pred (s84x_N M)) = transC1 M"
    by (rule w84x_PN_c1_of_admeq[OF MST MPT hp nVI admeq rng])
  have c1shape: "transC1 M = Dpt (enat (entry M 1 (transJm1 M))) (transT2 M)"
    by (rule m_8_5_scbdec_c1_shape(2)[OF MR MPT J1pos T1])
  have prc1OT: "Dpt (enat (entry M 1 (transJm1 M))) (transT2 M) \<in> OT_B"
    using predPNOT PNc1 c1shape by simp
  have "isOT_BT (bpHeadT (Dpt (enat (entry M 1 (transJm1 M))) (transT2 M)))"
    by (rule otx_bpHeadT_OT[OF prc1OT])
  thus ?thesis by simp
qed

text \<open>@{text cnv_tri0_transT2}: the condIV hole G-control \<open>tri0\<close> stated DIRECTLY
  for the tower seed \<open>transT2 M\<close> (the shape @{thm [source] ot2_tower_inv} /
  @{thm [source] ot2_tower_newOT} consume), instead of the outer-wrapped
  \<open>bpHeadT (Trans (Pred (s84x_N M)))\<close> of @{thm [source] cnv_tri0_of_nest}.  It is
  the PRE-\<open>scbext\<close> core of @{thm [source] cnv_tri0_of_nest}: the c2-body dichotomy
  @{thm [source] c4dx_condIV_c2body_shape} plus the \<open>d4vx_ins\<close> nested-\<open>+\<^sub>B\<close> rewrite
  @{thm [source] ot2_dins_addBT_of_shape} give \<open>X\<^sub>1 = t\<^sub>3 + D\<^bsub>jpe\<^esub>(t\<^sub>4 + D\<^bsub>ub\<^esub>(D\<^bsub>ub\<^esub>0))\<close>,
  and the trivial-base growth control (@{thm [source] ot1_triG_add} /
  @{thm [source] b1x_triG_Dpt} / @{thm [source] b1x_triG_addBT}) builds the triG
  in either dichotomy leg WITHOUT the \<open>D\<^bsub>transV\<^esub>\<close> wrap.  ltJ-FREE.\<close>

lemma cnv_tri0_transT2:
  fixes M :: pairseq and s0 b0 :: "Sym list" and z :: BT
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and cIV: "transCondIV M"
    and inner: "scb_decomp (bpHeadT (transC2 M)) s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
  shows "b1x_triG z (transT2 M)
           (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
              0\<^sub>B)"
proof -
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?jpe = "entry M 1 (transJ0 M)"
  let ?c = "Dpt (enat ?v1) 0\<^sub>B"
  let ?cc = "Dpt (enat ?ub) 0\<^sub>B"
  obtain t3 t4 where t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B"
    and body: "bpHeadT (transC2 M) = t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B ?c)"
    and rel: "(t3 = transT2 M \<and> t4 = transT2 M)
              \<or> transT2 M = t3 +\<^sub>B Dpt (enat ?jpe) t4"
    using c4dx_condIV_c2body_shape[OF MR MP J1pos T1 cIV] by blast
  have X0TB: "(0\<^sub>B :: BT) \<in> T_B" by (simp add: T_B_def)
  have inner': "scb_decomp (t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B Dpt (enat ?v1) 0\<^sub>B)) s0
                  (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0"
    using inner body by simp
  have X1eq: "d4vx_ins s0 ?ub b0 0\<^sub>B
            = t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B ?cc)"
    by (rule ot2_dins_addBT_of_shape[OF t3TB t4TB X0TB inner'])
  have prin: "b1x_triG z (transT2 M) (t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B ?cc))"
    using rel
  proof
    assume A: "t3 = transT2 M \<and> t4 = transT2 M"
    have "b1x_triG z (transT2 M)
            (transT2 M +\<^sub>B Dpt (enat ?jpe) (transT2 M +\<^sub>B ?cc))"
      by (rule ot1_triG_add)
    thus ?thesis using A by simp
  next
    assume B: "transT2 M = t3 +\<^sub>B Dpt (enat ?jpe) t4"
    obtain t3s where t3eq: "t3 = Trm t3s" by (cases t3)
    have s1: "b1x_triG z t4 (t4 +\<^sub>B ?cc)" by (rule ot1_triG_add)
    have s2: "b1x_triG z (Trm [DB (enat ?jpe) t4]) (Trm [DB (enat ?jpe) (t4 +\<^sub>B ?cc)])"
      by (rule b1x_triG_Dpt[OF s1])
    have s3: "b1x_triG z (Trm t3s +\<^sub>B Trm [DB (enat ?jpe) t4])
                         (Trm t3s +\<^sub>B Trm [DB (enat ?jpe) (t4 +\<^sub>B ?cc)])"
      by (rule b1x_triG_addBT[OF s2])
    have s3': "b1x_triG z (t3 +\<^sub>B Dpt (enat ?jpe) t4)
                         (t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B ?cc))"
      using s3 t3eq by simp
    thus ?thesis using B by simp
  qed
  show ?thesis using prin X1eq by simp
qed

text \<open>@{text ot2_IVADMEQ_of_pkg_free}: the SETLE-FREE mirror of
  @{thm [source] ot2_IVADMEQ_of_pkg}.  Same producer package, but the two hole
  tower facts \<open>NEWOT\<close> / \<open>SETLE\<close> are replaced by the CLEAN inputs \<open>t2OT\<close> and
  \<open>tri0\<close>: @{thm [source] ot2_tower_newOT} supplies the \<open>isOT\<^bsub>BP\<^esub>(D\<^bsub>e3\<^esub> A\<^sub>k)\<close>
  principals and @{thm [source] ot2_tower_inv} the joint \<open>isOT\<^bsub>BT\<^esub> A\<^sub>k\<close> +
  G-control \<open>A\<^sub>k \<triangleleft>\<^bsub>D\<^sub>\<infinity>W\<^sub>k\<^esub> W\<^bsub>k+1\<^esub>\<close>, so the final transport is one
  @{thm [source] otx3_core_tri} at head \<open>e\<^sub>3\<close> (NO @{term b1x_setle} obligation).\<close>

lemma ot2_IVADMEQ_of_pkg_free:
  fixes M :: pairseq and m :: nat and s0 s1 b0 b1 :: "Sym list" and body :: BT
  assumes MST: "M \<in> ST_PS"
    and mgt: "1 < m"
    and ihOT: "Trans M \<in> OT_B"
    and t2TB: "transT2 M \<in> T_B"
    and t2OT: "isOT_BT (transT2 M)"
    and uv: "entry M 1 (s84x_jm3 M) < entry M 1 (Lng M - 1)"
    and bodyT: "body \<in> T_B"
    and bodyne: "body \<noteq> Trm []"
    and dbbody: "domB body = TBv (enat (entry M 1 (Lng M - 1) - 1))"
    and inner: "scb_decomp body s0
                  (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
    and k1: "scb_kind1 (Trans M) s1
               (flatBT (Dpt (enat (entry M 1 (s84x_jm3 M))) body)) b1"
    and mnform: "\<And>m. 1 \<le> m \<Longrightarrow>
        flatBT (Trans ((M::pairseq)[m]))
          = s1 @ Dsym (enat (entry M 1 (s84x_jm3 M)))
              # flatBT (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                         (transT2 M) (m - 1))
              @ b1"
    and base0: "lessBT (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) (transT2 M)"
    and base1: "lessBT (transT2 M)
                  (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
                     0\<^sub>B)"
    and tri0: "b1x_triG (Dpt \<infinity> (0\<^sub>B :: BT)) (transT2 M)
                 (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0 0\<^sub>B)"
  shows "Trans ((M::pairseq)[m]) \<in> OT_B"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?X0 = "Dpt (enat ?ub) 0\<^sub>B"
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have TT: "Trans M \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF MR])
  have wrap: "flatBT body
      = s0 @ flatBP (DB (enat (entry M 1 (Lng M - 1))) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have b0RP: "\<forall>x \<in> set b0. x = RP" using inner by (simp add: scb_decomp_def)
  have dTM: "scb_decomp (Trans M) s1 (flatBT (Dpt (enat ?e3) body)) b1"
    using k1 by (simp add: scb_kind1_def)
  have b1RP: "\<forall>x \<in> set b1. x = RP" using dTM by (simp add: scb_decomp_def)
  have X0TB: "(0\<^sub>B :: BT) \<in> T_B" by (simp add: T_B_def)
  have euB: "?e3 \<le> ?ub" using uv by linarith
  \<comment> \<open>tower \<open>T\<^bsub>B\<^esub>\<close>-membership\<close>
  have WTB: "\<And>k. d4vx_core s0 ?ub b0 0\<^sub>B k \<in> T_B"
    by (rule oi5_d4vx_core_TB[OF wrap b0RP bodyT X0TB])
  \<comment> \<open>donor closed forms and flats\<close>
  have fseq: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate (n + 1) (s0 @ [Dsym (enat ?ub)]))
           @ [Zsym]
           @ concat (replicate (n + 1) b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbody bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 0\<^sub>B n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT (0\<^sub>B :: BT) @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  \<comment> \<open>r72: the operB core is the \<open>0\<^sub>B\<close>-seeded tower ONE LEVEL DEEPER\<close>
  have fWn: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))) @ b1"
  proof -
    fix n :: nat
    have A: "flatBT (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))
        = concat (replicate (Suc n) (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (Suc n) b0)"
      using Xflat[of "Suc n"] by (simp del: d4vx_core.simps)
    show "flatBT (operB (Trans M) (numBT n))
        = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n))) @ b1"
      using fseq[of n] A by (simp del: d4vx_core.simps)
  qed
  \<comment> \<open>W-tower OT principals from the [Buc1] 3.2 closure of the IH
      (level \<open>j+1\<close> is the core of the donor \<open>numBT j\<close>; level \<open>0\<close> is \<open>0\<^sub>B\<close>)\<close>
  have Xe3: "\<And>j. isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B j))"
  proof -
    fix j :: nat
    show "isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B j))"
    proof (cases j)
      case 0
      thus ?thesis by simp
    next
      case (Suc n)
      have opOT: "operB (Trans M) (numBT n) \<in> OT_B"
        by (rule e4x_OT_B_operB_numBT[OF ihOT])
      have cTB: "Dpt (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)) \<in> T_B"
        using WTB[of "Suc n"] by (simp add: T_B_def del: d4vx_core.simps)
      have Xdec: "scb_decomp (operB (Trans M) (numBT n)) s1
                    (flatBT (Dpt (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)))) b1"
        unfolding scb_decomp_def
        using fWn[of n] b1RP
              isPTB_str_Dpt[of "enat ?e3" "d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)"]
              WTB[of "Suc n"]
        by (simp add: T_B_def del: d4vx_core.simps)
      have "Dpt (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)) \<in> OT"
        by (rule m_8_7_OT_scb_recursive[OF opOT cTB Xdec])
      hence "isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B (Suc n)))"
        by (simp add: OT_def)
      thus ?thesis using Suc by simp
    qed
  qed
  \<comment> \<open>NEWOT and the joint tower invariant from the SETLE-free engine\<close>
  have newOTk: "\<And>k. isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 (transT2 M) k))"
    by (rule ot2_tower_newOT[OF wrap b0RP euB t2OT base0 base1 tri0 Xe3])
  have INV: "\<And>k. isOT_BT (d4vx_core s0 ?ub b0 (transT2 M) k)
      \<and> b1x_triG (Dpt \<infinity> (d4vx_core s0 ?ub b0 0\<^sub>B k))
            (d4vx_core s0 ?ub b0 (transT2 M) k)
            (d4vx_core s0 ?ub b0 0\<^sub>B (Suc k))"
    by (rule ot2_tower_inv[OF wrap b0RP euB t2OT base0 base1 tri0 Xe3])
  \<comment> \<open>index bookkeeping\<close>
  have Sk: "Suc (m - 1) = m" using mgt by simp
  have fMm: "flatBT (Trans ((M::pairseq)[m]))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 (transT2 M) (m - 1))) @ b1"
    using mnform[of m] mgt by simp
  let ?A = "d4vx_core s0 ?ub b0 (transT2 M) (m - 1)"
  let ?WL = "d4vx_core s0 ?ub b0 0\<^sub>B (m - 1)"
  let ?WH = "d4vx_core s0 ?ub b0 0\<^sub>B m"
  have SkL: "Suc (m - 2) = m - 1" using mgt by simp
  have loflat: "flatBT (operB (Trans M) (numBT (m - 2)))
      = s1 @ flatBP (DB (enat ?e3) ?WL) @ b1"
    using fWn[of "m - 2"] SkL by simp
  have hiflat: "flatBT (operB (Trans M) (numBT (m - 1)))
      = s1 @ flatBP (DB (enat ?e3) ?WH) @ b1"
    using fWn[of "m - 1"] Sk by simp
  have loOT: "isOT_BT (operB (Trans M) (numBT (m - 2)))"
    using e4x_OT_B_operB_numBT[OF ihOT, of "m - 2"] by (simp add: OT_B_def OT_def)
  have hiOT: "isOT_BT (operB (Trans M) (numBT (m - 1)))"
    using e4x_OT_B_operB_numBT[OF ihOT, of "m - 1"] by (simp add: OT_B_def OT_def)
  have newOT: "isOT_BP (DB (enat ?e3) ?A)" by (rule newOTk)
  have triA: "b1x_triG (Dpt \<infinity> ?WL) ?A ?WH"
    using INV[of "m - 1"] Sk by simp
  have base0Z: "lessBT (0\<^sub>B :: BT) (transT2 M)"
  proof -
    have "lessBT (0\<^sub>B :: BT) (Dpt (enat ?ub) 0\<^sub>B)" by simp
    thus ?thesis using base0 lessBT_trans by blast
  qed
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0Z base1, of "m - 1"]
  have ordlo: "leBT ?WL ?A" using IL by simp
  have ordhi: "leBT ?A ?WH" using IL Sk by simp
  \<comment> \<open>final transport at head \<open>e\<^sub>3\<close>, SETLE-free\<close>
  have isot: "isOT_BT (Trans ((M::pairseq)[m]))"
    using otx3_core_tri[OF loflat fMm hiflat b1RP loOT hiOT newOT ordlo ordhi triA]
    by blast
  \<comment> \<open>\<open>T\<^bsub>B\<^esub>\<close> side and assembly\<close>
  have m1: "1 \<le> m" using mgt by simp
  have NmST: "(M::pairseq)[m] \<in> ST_PS" by (rule ST_PS.oper[OF MST m1])
  have NmRT: "(M::pairseq)[m] \<in> RT_PS"
    using NmST m_6_7_ST_PS_subseteq_RT_PS by blast
  have "Trans ((M::pairseq)[m]) \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF NmRT])
  thus ?thesis using isot by (simp add: OT_B_def OT_def)
qed

text \<open>@{text ot2_IVADMEQ}: THE condIV admeq OT step (the census \<open>IVADMEQ\<close> slot).
  Discharges the \<open>{d1,d2,d3,HB}\<close> residual of @{thm [source] ot2_IVADMEQ_mod} from
  the Red-slice regime machinery (@{thm [source] mcx_regS} /
  @{thm [source] slx37_regSP_uncond} guarded by \<open>jm3 < jm2\<close>, then
  @{thm [source] m_8_4_slice_scb_part1} / @{thm [source] cpx_d2_condIV} /
  @{thm [source] cpx_d3_condIV} / @{thm [source] HB_condIV_t2_components} --- the
  same route as the proven @{thm [source] cpx_condIV_exchange_uncond}), and the
  \<open>NEWOT\<close>/\<open>SETLE\<close> residual via the SETLE-free
  @{thm [source] ot2_IVADMEQ_of_pkg_free} with \<open>t2OT\<close>
  (@{thm [source] ot2_transT2_OT}) and \<open>tri0\<close>
  (@{thm [source] cnv_tri0_transT2}).\<close>

lemma ot2_IVADMEQ:
  fixes M :: pairseq and m :: nat
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and cIV: "transCondIV M"
    and admeq: "Adm M (s84x_jm2 M) = transJm1 M"
    and ihOT: "Trans M \<in> OT_B"
    and mgt: "1 < m"
  shows "Trans ((M::pairseq)[m]) \<in> OT_B"
proof -
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have nVI: "\<not> transCondVI M" using c4dx_condIV_excl(4)[OF cIV] .
  have T1: "transT1 M \<noteq> 0\<^sub>B" using s84d_L4_regime[OF MST MPT hp nVI] by simp
  have J1pos: "transJ1 M > 0" using j1gt by (simp add: transJ1_def)
  have branch: "transCondIII M \<or> transCondIV M" using cIV by blast
  have jm2ltj0: "s84x_jm2 M < transJ0 M"
    by (rule m_8_4_oper_props_1(1)[OF MST MPT hp j1gt branch])
  have reg: "s84x_jm2 M < transJ0 M \<or> adm M (transJ0 M)" using jm2ltj0 by blast
  \<comment> \<open>Red-slice regime facts, discharged as in \<open>cpx_condIV_exchange_uncond\<close>\<close>
  have REGS: "s84x_jm3 M < s84x_jm2 M \<Longrightarrow>
                cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M))"
  proof -
    assume g: "s84x_jm3 M < s84x_jm2 M"
    show "cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M))"
      by (rule mcx_regS[OF MST MPT hp j1gt branch g])
  qed
  have REGSP: "s84x_jm3 M < s84x_jm2 M \<Longrightarrow> Br (Red (Pred (s84x_N M))) \<noteq> [] \<Longrightarrow>
                 cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (Pred (s84x_N M)))"
  proof -
    assume g: "s84x_jm3 M < s84x_jm2 M" and b: "Br (Red (Pred (s84x_N M))) \<noteq> []"
    show "cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (Pred (s84x_N M)))"
      by (rule slx37_regSP_uncond[OF MST MPT hp j1gt branch g b])
  qed
  \<comment> \<open>the \<open>{d1,d2,d3,HB}\<close> residual\<close>
  obtain sb where d1: "scb_decomp (transC2 M)
        (Dsym (enat (entry M 1 (transJm1 M))) # fst sb)
        (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) (snd sb)"
    using ex1_implies_ex[OF m_8_4_slice_scb_part1[OF MST MPT hp nVI admeq]] by auto
  have d2: "scb_decomp (Trans (s84x_Np M))
        (Dsym (enat (entry M 1 (s84x_jm2 M))) # fst sb)
        (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) (snd sb)"
    by (rule cpx_d2_condIV[OF MST MPT hp nVI admeq REGS d1])
  have rng: "s84x_jm2 M + 1 < Lng M - 1" by (rule s84d_L5_rng[OF MST MPT hp nVI])
  have d3: "Trans (Pred (s84x_Np M))
          = Dpt (enat (entry M 1 (s84x_jm2 M))) (transT2 M)"
    by (rule cpx_d3_condIV[OF MST MPT hp nVI admeq rng REGSP])
  have HB: "\<forall>c \<in> set (PB (transT2 M)).
              leBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B) c"
    by (rule HB_condIV_t2_components[OF MST MPT hp cIV])
  \<comment> \<open>mnform + inner \<open>(s\<^sub>0,b\<^sub>0)\<close> from the slice route\<close>
  obtain s0 b0 where
    inner: "scb_decomp (bpHeadT (transC2 M)) s0
              (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)) b0"
    and MN: "\<forall>m. 1 \<le> m \<longrightarrow> flatBT (Trans ((M::pairseq)[m]))
         = s84x_s1 M @ Dsym (enat (entry M 1 (s84x_jm3 M)))
             # flatBT (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                        (transT2 M) (m - 1))
             @ s84x_b1 M"
    using c4cx2_condIV_mnform_of_slice[OF MST MPT hp cIV reg admeq d1 d2 d3]
    by blast
  have mn: "\<And>m. 1 \<le> m \<Longrightarrow> flatBT (Trans ((M::pairseq)[m]))
         = s84x_s1 M @ Dsym (enat (entry M 1 (s84x_jm3 M)))
             # flatBT (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                        (transT2 M) (m - 1))
             @ s84x_b1 M"
    using MN by blast
  \<comment> \<open>producer data (as in @{thm [source] ot2_IVADMEQ_mod})\<close>
  have uv: "entry M 1 (s84x_jm3 M) < entry M 1 (Lng M - 1)" by (rule c4dx_uv[OF hp])
  have t2TB: "transT2 M \<in> T_B" by (rule m_8_5_scbdec_c1_shape(3)[OF MR MPT J1pos T1])
  have bodyT: "bpHeadT (transC2 M) \<in> T_B"
  proof -
    obtain t3 t4 where t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B"
      and body: "bpHeadT (transC2 M)
          = t3 +\<^sub>B Dpt (enat (entry M 1 (transJ0 M)))
               (t4 +\<^sub>B Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
      using c4dx_condIV_c2body_shape[OF MR MPT J1pos T1 cIV] by blast
    obtain "as" where "t3 = Trm as" by (cases t3)
    moreover obtain bs where "t4 = Trm bs" by (cases t4)
    ultimately show ?thesis using body t3TB t4TB by (auto simp: T_B_def)
  qed
  have bodyne: "bpHeadT (transC2 M) \<noteq> Trm []" by (rule bpHeadT_transC2_nonzero)
  have dbbody: "domB (bpHeadT (transC2 M))
      = TBv (enat (entry M 1 (Lng M - 1) - 1))"
    by (rule c4dx_condIV_dbbody[OF MR MPT J1pos T1 cIV])
  have k1: "scb_kind1 (Trans M) (s84x_s1 M)
        (flatBT (Dpt (enat (entry M 1 (s84x_jm3 M))) (bpHeadT (transC2 M))))
        (s84x_b1 M)"
    by (rule c4dx_condIV_k1[OF MST MPT hp cIV admeq])
  \<comment> \<open>base orders\<close>
  have cond24: "transCondII M \<or> transCondIV M" using cIV by blast
  have t2ne: "transT2 M \<noteq> 0\<^sub>B"
    by (rule m_7_3_t2_nonzero_condIIorIV[OF MR MPT J1pos T1 cond24])
  have v1pos: "0 < entry M 1 (Lng M - 1)" using cIV by (simp add: transCondIV_def)
  have ubv1: "entry M 1 (Lng M - 1) - 1 < entry M 1 (Lng M - 1)" using v1pos by simp
  have base0: "lessBT (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) (transT2 M)"
    by (rule s85b_complb_lessBT[OF ubv1 t2ne HB])
  have base1: "lessBT (transT2 M)
      (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
         0\<^sub>B)"
    by (rule oy1_base1Y_t2[OF MR MPT J1pos T1 cIV inner])
  \<comment> \<open>the two clean tower inputs\<close>
  have t2OT: "isOT_BT (transT2 M)"
    by (rule ot2_transT2_OT[OF MST MPT hp cIV admeq ihOT])
  have tri0: "b1x_triG (Dpt \<infinity> (0\<^sub>B :: BT)) (transT2 M)
                (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0 0\<^sub>B)"
    by (rule cnv_tri0_transT2[OF MR MPT J1pos T1 cIV inner])
  \<comment> \<open>assemble via the SETLE-free of_pkg\<close>
  show ?thesis
    by (rule ot2_IVADMEQ_of_pkg_free[OF MST mgt ihOT t2TB t2OT uv bodyT bodyne
          dbbody inner k1 mn base0 base1 tri0])
qed

text \<open>CAPSTONE --- @{text oi8_census_final_ivadmeq}: the ltJ-threaded master
  census with BOTH the A0OT residual (via @{thm [source] ot1_A0OT}) AND the
  IVADMEQ residual (via @{thm [source] ot2_IVADMEQ}) now DISCHARGED.  Both
  termination pillars hold modulo exactly \<open>{SETLE1_ltJ, FINRC}\<close>.\<close>

theorem oi8_census_final_ivadmeq:
  assumes SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
    and FINRC: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             transCondII K \<Longrightarrow> tvx_finRc K"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi8_census_final(1)[OF SETLE1 ot2_IVADMEQ FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi8_census_final(2)[OF SETLE1 ot2_IVADMEQ FINRC])
qed


(* ===== r61 endgame: SETLE1 restricted engine ox6_*_restr (front A) + FINRC bounded content ot_finRc_* / A9 determination (front B) ===== *)


(* ===================================================================== *)
(* r61 SETLE1_ltJ (prefix ox6_..._restr / ot6_): the ANCESTOR-RESTRICTED  *)
(*   re-thread of the head-guarded scbext-setle descent engine.           *)
(*                                                                        *)
(*   HONESTY FIX over r60's ox6_setle_scbext: r60 threaded spineH         *)
(*   UNIVERSALLY over all (t',sc,bc) with flatBT t' = sc @ flatBP cpA @ bc *)
(*   and size t' < size tA.  That form is STRONGER-THAN-TRUE (a small tree *)
(*   can carry a head BIGGER than X1's, so it is > X1).  The TRUE bound    *)
(*   (STEP-0 r60, 146/146 real hosts; STEP-0 r59's "H" pointwise          *)
(*   invariant) is ANCESTOR-RESTRICTED: it holds only for t' that are the  *)
(*   ACTUAL right-spine ancestor bodies of A1 --- and those come, at every  *)
(*   align3 peel level, with a MATCHED X-side sibling  tx' (same sc,bc,     *)
(*   hole cpX) that the engine already proves lies in  GBT u B.  Keying     *)
(*   spineH on the witness  tx' \<in> GBT u B  is exactly what rules out the     *)
(*   false small-tree/big-head CEX, so the restricted residual is the TRUE  *)
(*   statement.  ox6_setle_scbext_restr is the reusable spine-induction     *)
(*   core; ox6_setle_wrapped_restr packages it for d4vx_ins;                *)
(*   ox6_SETLE1_reduce_restr localises the census SETLE1_ltJ slot to the    *)
(*   restricted ancestor bound.                                            *)
(* ===================================================================== *)

subsection \<open>The ancestor-restricted scbext-setle descent engine
  \<open>ox6_setle_scbext_restr\<close>\<close>

text \<open>@{text ox6_setle_scbext_restr}: the honest re-thread of
  @{thm [source] ox6_setle_scbext}.  Identical right-spine induction, but the
  \<open>spineH\<close> residual is keyed on the MATCHED X-side sibling witness \<open>tx' \<in> G\<^sub>u B\<close>:
  the engine hands \<open>spineH\<close> only the ACTUAL right-spine ancestor bodies \<open>lbA\<close>,
  each paired with its matched \<open>lbX \<in> G\<^sub>u B\<close> (proved \<open>lbXB\<close> below).  This is the
  exact TRUE (STEP-0) bound, unlike the universal (stronger-than-true) form.\<close>

lemma ox6_setle_scbext_restr:
  fixes B :: BT and cpA cpX :: BP and u :: enat
  assumes holeH: "b1x_setle (GBP u cpA) (insert B (GBT u B))"
  shows "flatBT tA = s @ flatBP cpA @ b \<Longrightarrow>
         flatBT tX = s @ flatBP cpX @ b \<Longrightarrow>
         (\<forall>x\<in>set b. x = RP) \<Longrightarrow>
         GBT u tX \<subseteq> GBT u B \<Longrightarrow>
         (\<forall>t' tx' sc bc. flatBT t' = sc @ flatBP cpA @ bc
              \<longrightarrow> flatBT tx' = sc @ flatBP cpX @ bc
              \<longrightarrow> (\<forall>x\<in>set bc. x = RP) \<longrightarrow> tx' \<in> GBT u B
              \<longrightarrow> size t' < size tA \<longrightarrow> leBT t' B) \<Longrightarrow>
         b1x_setle (GBT u tA) (insert B (GBT u B))"
proof (induction tA arbitrary: tX s b rule: measure_induct_rule[where f=size])
  case (less tA)
  note fA = less.prems(1) and fX = less.prems(2) and bRP = less.prems(3)
    and subXB = less.prems(4) and spineH = less.prems(5)
  from otx2_align3[OF fA fX fX bRP]
  show ?case
  proof (elim disjE exE conjE)
    \<comment> \<open>Case A: the hole is the last top-level principal\<close>
    fix qs
    assume TA: "tA = Trm (qs @ [cpA])" and TX: "tX = Trm (qs @ [cpX])"
      and TX3: "tX = Trm (qs @ [cpX])"
    have qle: "(\<Union>q\<in>set qs. GBP u q) \<subseteq> GBT u B"
    proof -
      have "(\<Union>q\<in>set qs. GBP u q) \<subseteq> GBT u tX" using TX by auto
      thus ?thesis using subXB by blast
    qed
    show "b1x_setle (GBT u tA) (insert B (GBT u B))"
      unfolding b1x_setle_def
    proof
      fix x assume xin: "x \<in> GBT u tA"
      have "x \<in> (\<Union>q\<in>set qs. GBP u q) \<or> x \<in> GBP u cpA" using xin TA by auto
      thus "\<exists>y\<in>insert B (GBT u B). leBT x y"
      proof
        assume "x \<in> (\<Union>q\<in>set qs. GBP u q)"
        hence "x \<in> GBT u B" using qle by blast
        thus ?thesis by blast
      next
        assume "x \<in> GBP u cpA"
        thus ?thesis using holeH unfolding b1x_setle_def by blast
      qed
    qed
  next
    \<comment> \<open>Case B: the hole is nested one right-spine level deeper\<close>
    fix qs w lbA lbX lb3 sc bc
    assume TA: "tA = Trm (qs @ [DB w lbA])"
      and TX: "tX = Trm (qs @ [DB w lbX])"
      and TX3: "tX = Trm (qs @ [DB w lb3])"
      and FlbA: "flatBT lbA = sc @ flatBP cpA @ bc"
      and FlbX: "flatBT lbX = sc @ flatBP cpX @ bc"
      and Flb3: "flatBT lb3 = sc @ flatBP cpX @ bc"
      and bcRP: "\<forall>x\<in>set bc. x = RP"
    have pin: "DB w lbA \<in> set (qs @ [DB w lbA])" by simp
    have szp: "size (DB w lbA) \<le> size_list size (qs @ [DB w lbA])"
      by (rule size_list_estimation'[OF pin order_refl])
    have szlt: "size lbA < size tA" using szp TA by simp
    have qle: "(\<Union>q\<in>set qs. GBP u q) \<subseteq> GBT u B"
    proof -
      have "(\<Union>q\<in>set qs. GBP u q) \<subseteq> GBT u tX" using TX by auto
      thus ?thesis using subXB by blast
    qed
    show "b1x_setle (GBT u tA) (insert B (GBT u B))"
      unfolding b1x_setle_def
    proof
      fix x assume xin: "x \<in> GBT u tA"
      have "x \<in> (\<Union>q\<in>set qs. GBP u q) \<or> x \<in> GBP u (DB w lbA)"
        using xin TA by auto
      thus "\<exists>y\<in>insert B (GBT u B). leBT x y"
      proof
        assume "x \<in> (\<Union>q\<in>set qs. GBP u q)"
        hence "x \<in> GBT u B" using qle by blast
        thus ?thesis by blast
      next
        assume xh: "x \<in> GBP u (DB w lbA)"
        have uw: "u \<le> w" using xh by (auto split: if_split_asm)
        have xcase: "x = lbA \<or> x \<in> GBT u lbA" using xh by (auto split: if_split_asm)
        have lbXin: "lbX \<in> GBT u tX"
        proof -
          have "lbX \<in> GBP u (DB w lbX)" using uw by simp
          thus ?thesis using TX by auto
        qed
        have lbXB: "lbX \<in> GBT u B" using lbXin subXB by blast
        have subX': "GBT u lbX \<subseteq> GBT u B" using b1x_GBT_trans[OF lbXB] by blast
        \<comment> \<open>the restricted spineH re-threaded for the deeper level, MATCHED to \<open>lbX\<close>\<close>
        have spineH': "\<forall>t' tx' sc' bc'. flatBT t' = sc' @ flatBP cpA @ bc'
              \<longrightarrow> flatBT tx' = sc' @ flatBP cpX @ bc'
              \<longrightarrow> (\<forall>x\<in>set bc'. x = RP) \<longrightarrow> tx' \<in> GBT u B
              \<longrightarrow> size t' < size lbA \<longrightarrow> leBT t' B"
        proof (intro allI impI)
          fix t' tx' sc' bc'
          assume a1: "flatBT t' = sc' @ flatBP cpA @ bc'"
            and a1x: "flatBT tx' = sc' @ flatBP cpX @ bc'"
            and a2: "\<forall>x\<in>set bc'. x = RP" and a2x: "tx' \<in> GBT u B"
            and a3: "size t' < size lbA"
          have "size t' < size tA" using a3 szlt by simp
          thus "leBT t' B" using spineH a1 a1x a2 a2x by blast
        qed
        from xcase show ?thesis
        proof
          assume "x = lbA"
          moreover have "leBT lbA B"
            using spineH FlbA FlbX bcRP lbXB szlt by blast
          ultimately show ?thesis by blast
        next
          assume xlbA: "x \<in> GBT u lbA"
          have "b1x_setle (GBT u lbA) (insert B (GBT u B))"
            by (rule less.IH[OF szlt FlbA FlbX bcRP subX' spineH'])
          thus ?thesis using xlbA unfolding b1x_setle_def by blast
        qed
      qed
    qed
  qed
qed

text \<open>@{text ox6_setle_wrapped_restr}: the @{const d4vx_ins} packaging of the
  restricted engine.  Mirror of @{thm [source] ox6_setle_wrapped}; only \<open>spineH\<close>
  is now the ancestor-restricted (matched-\<open>tx'\<close>) form.\<close>

lemma ox6_setle_wrapped_restr:
  fixes A0 X0 W :: BT and hole :: BP and s0 b0 :: "Sym list" and ub :: nat and u :: enat
  assumes ox5: "b1x_setle (GBT u A0)
                  (insert (d4vx_ins s0 ub b0 0\<^sub>B) (GBT u (d4vx_ins s0 ub b0 0\<^sub>B)))"
    and base1: "lessBT A0 (d4vx_ins s0 ub b0 0\<^sub>B)"
    and wrap: "flatBT W = s0 @ flatBP hole @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and spineH: "\<forall>t' tx' sc bc.
          flatBT t' = sc @ flatBP (DB (enat ub) A0) @ bc
          \<longrightarrow> flatBT tx' = sc @ flatBP (DB (enat ub) 0\<^sub>B) @ bc
          \<longrightarrow> (\<forall>x\<in>set bc. x = RP)
          \<longrightarrow> tx' \<in> GBT u (d4vx_ins s0 ub b0 0\<^sub>B)
          \<longrightarrow> size t' < size (d4vx_ins s0 ub b0 A0)
          \<longrightarrow> leBT t' (d4vx_ins s0 ub b0 0\<^sub>B)"
  shows "b1x_setle (GBT u (d4vx_ins s0 ub b0 A0))
           (insert (d4vx_ins s0 ub b0 0\<^sub>B) (GBT u (d4vx_ins s0 ub b0 0\<^sub>B)))"
proof -
  let ?X1 = "d4vx_ins s0 ub b0 0\<^sub>B"
  let ?A1 = "d4vx_ins s0 ub b0 A0"
  have fA1: "flatBT ?A1 = s0 @ flatBP (DB (enat ub) A0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ub A0] by simp
  have fX1: "flatBT ?X1 = s0 @ flatBP (DB (enat ub) 0\<^sub>B) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ub "0\<^sub>B"] by simp
  have holeH: "b1x_setle (GBP u (DB (enat ub) A0)) (insert ?X1 (GBT u ?X1))"
    by (rule ox6_holeH[OF ox5 base1])
  show ?thesis
    by (rule ox6_setle_scbext_restr[OF holeH fA1 fX1 b0RP subset_refl spineH])
qed

text \<open>@{text ox6_SETLE1_reduce_restr}: the census-level SETLE1 residual reduced to
  the ANCESTOR-RESTRICTED spine head bound.  Mirror of
  @{thm [source] ox6_SETLE1_reduce}; conclusion is EXACTLY the \<open>SETLE1\<close> slot of
  @{thm [source] oi8_census_final} at \<open>u\<close>, and the sole open input \<open>spineH\<close> is
  now the TRUE (matched-\<open>tx'\<close>) statement.\<close>

lemma ox6_SETLE1_reduce_restr:
  fixes N :: pairseq and s0 b0 :: "Sym list" and u :: enat
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                 (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and spineH: "\<forall>t' tx' sc bc.
          flatBT t' = sc @ flatBP (DB (enat (entry N 1 (Lng N - 1) - 1))
                                      (bpHeadT (Trans (Pred (s84x_N N))))) @ bc
          \<longrightarrow> flatBT tx' = sc @ flatBP (DB (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B) @ bc
          \<longrightarrow> (\<forall>x\<in>set bc. x = RP)
          \<longrightarrow> tx' \<in> GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                            0\<^sub>B)
          \<longrightarrow> size t' < size (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                                (bpHeadT (Trans (Pred (s84x_N N)))))
          \<longrightarrow> leBT t' (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                        0\<^sub>B)"
  shows "b1x_setle
           (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                     (bpHeadT (Trans (Pred (s84x_N N))))))
           (insert (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                      0\<^sub>B)
                   (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                             0\<^sub>B)))"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X0 = "Dpt (enat ?ub) 0\<^sub>B"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  \<comment> \<open>the body driver \<open>ox5\<close>\<close>
  have ox5: "b1x_setle (GBT u ?A0)
               (insert (d4vx_ins s0 ?ub b0 0\<^sub>B) (GBT u (d4vx_ins s0 ?ub b0 0\<^sub>B)))"
    by (rule ox5_body_driver_census[OF NST NPT hp j1gt branch ltJ inner])
  \<comment> \<open>\<open>base\<^sub>1\<close> and the flat wrapper from the package (given \<open>(s\<^sub>0,b\<^sub>0)\<close> pinned)\<close>
  obtain s0' b0' s1 b1 where
      b0RP': "\<forall>x \<in> set b0'. x = RP"
    and inner': "scb_decomp ?body s0'
         (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0'"
    and base1': "lessBT ?A0 (d4vx_ins s0' ?ub b0' 0\<^sub>B)"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "flatBT ?body = s0 @ flatBT (Dpt (enat ?v1) 0\<^sub>B) @ b0"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0 @ [Dsym (enat ?v1), Zsym] @ b0" using z by simp
    thus False by (cases s0) auto
  qed
  have pin: "s0 = s0' \<and> b0 = b0'"
    by (rule m_7_2_scb_unique_sb[OF inner inner' bodyne])
  have base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 0\<^sub>B)" using base1' pin by simp
  have b0RP: "\<forall>x \<in> set b0. x = RP" using b0RP' pin by simp
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  show ?thesis
    by (rule ox6_setle_wrapped_restr[OF ox5 base1 wrap b0RP spineH])
qed



(* ===================================================================== *)
(* ===== r61 FINRC closure attempt (prefix ot_finRc_):  the condII   ==== *)
(* =====   finiteness residual tvx_finRc IS the A9 nth-artifact in     === *)
(* =====   fin-set form.  DETERMINATION + the true bounded content.    === *)
(* ===================================================================== *)

text \<open>\<^bold>\<open>FINRC = the A9 nth-artifact in fin-set form.\<close>  The census slot
  \<open>FINRC\<close> asks for @{const tvx_finRc} \<open>K\<close>, i.e. finiteness of
  \[
     \{J.\ (\mathrm{Br}\,R_c)_{(\mathrm{Lng}(\mathrm{Br}\,R_c)-1)\,0\,0}
              = (\mathrm{Br}\,R_c)_{J\,0\,0}
        \ \wedge\ (\mathrm{Br}\,R_c)_{J\,1\,0} < (\mathrm{Br}\,R_c)_{J\,0\,0}\},
  \]
  where @{term "entry M i j"} is @{term "if i = 0 then fst (M ! j) else snd (M ! j)"}
  (@{thm entry_def}) and \<open>Br R\<^sub>c\<close> is a genuine finite @{typ "pairseq list"}.  The
  set-comprehension binder \<open>J\<close> ranges over \<^bold>\<open>all\<close> naturals, but the article's
  \<open>J\<close> is a \<^emph>\<open>branch index\<close>, ranging over \<open>0, \<dots>, Lng (Br R\<^sub>c) - 1\<close> (exactly the
  correction \<^bold>\<open>A9\<close>: "\<open>J\<^sub>1 := Lng (Br M)\<close>" must be "\<open>J\<^sub>1 := Lng (Br M) - 1\<close>",
  the \<open>Br\<close>-index range being \<open>0..Lng (Br M) - 1\<close>).  For \<open>J \<ge> Lng (Br R\<^sub>c)\<close> the
  list-\<open>nth\<close> \<open>(Br R\<^sub>c) ! J\<close> peels to \<open>[] ! (J - Lng (Br R\<^sub>c))\<close>: Isabelle's
  @{const nth} has \<^bold>\<open>no\<close> equation for the \<open>[]\<close> constructor (it is
  \<open>primrec (nonexhaustive)\<close>), so \<open>[] ! m\<close> is an unspecified value about which
  \<^bold>\<open>nothing\<close> is provable.  Hence the strict inequality
  \<open>(Br R\<^sub>c)_{J,1,0} < (Br R\<^sub>c)_{J,0,0}\<close> is \<^bold>\<open>not refutable\<close> for out-of-range \<open>J\<close>,
  the set is not provably bounded, and @{const tvx_finRc} \<open>K\<close> is \<^bold>\<open>UNPROVABLE as
  literally stated\<close> (the total-\<open>nth\<close> artifact already recorded in the
  \<open>tvx_finRc\<close> comment; same class as the \<open>hqx\<close>/\<open>bpx\<close>/\<open>bfx\<close> fins found
  un-dischargeable in r24/r48, correction-A9 territory).

  Two honest green bricks below make this precise and record the true content:
  \<^item> @{text ot_finRc_bounded}: under the \<^emph>\<open>intended bounded reading\<close>
    (\<open>J < Lng (Br R\<^sub>c)\<close>, the branch-index range) the set is \<^bold>\<open>finite\<close>,
    unconditionally --- it is a subset of \<open>{..< Lng (Br R\<^sub>c)}\<close>.  So the article's
    finiteness claim is \<^bold>\<open>TRUE\<close>; only the formalized (unbounded) binder is wrong.
  \<^item> @{text ot_finRc_reduce}: @{const tvx_finRc} \<open>K\<close> follows from
    \<^bold>\<open>exactly\<close> the A9 out-of-range refutation
    \<open>\<forall>J \<ge> Lng (Br R\<^sub>c). \<not> ((Br R\<^sub>c)_{J,1,0} < (Br R\<^sub>c)_{J,0,0})\<close>.  This localizes the
    entire FINRC residual to that single undischargeable \<open>nth\<close>-artifact premise:
    once \<open>tvx_finRc_def\<close> carries the \<open>J < Lng (Br (tvx_Rc K))\<close> guard (the A9
    fin-form correction), the census FINRC slot is discharged verbatim by
    @{text ot_finRc_bounded}.\<close>

lemma ot_finRc_bounded:
  fixes K :: pairseq
  shows "finite {J. J < Lng (Br (tvx_Rc K))
              \<and> entry (Br (tvx_Rc K) ! (Lng (Br (tvx_Rc K)) - 1)) 0 0
                  = entry (Br (tvx_Rc K) ! J) 0 0
              \<and> entry (Br (tvx_Rc K) ! J) 1 0 < entry (Br (tvx_Rc K) ! J) 0 0}"
  by (rule finite_subset[of _ "{..< Lng (Br (tvx_Rc K))}"]) auto

lemma ot_finRc_reduce:
  fixes K :: pairseq
  assumes OOR: "\<And>J. Lng (Br (tvx_Rc K)) \<le> J \<Longrightarrow>
                  \<not> (entry (Br (tvx_Rc K) ! J) 1 0 < entry (Br (tvx_Rc K) ! J) 0 0)"
  shows "tvx_finRc K"
proof -
  let ?S = "{J. J < Lng (Br (tvx_Rc K)) \<and> entry (Br (tvx_Rc K) ! (Lng (Br (tvx_Rc K)) - 1)) 0 0
                    = entry (Br (tvx_Rc K) ! J) 0 0
                \<and> entry (Br (tvx_Rc K) ! J) 1 0 < entry (Br (tvx_Rc K) ! J) 0 0}"
  have "?S \<subseteq> {..< Lng (Br (tvx_Rc K))}"
  proof (rule subsetI)
    fix J assume "J \<in> ?S"
    hence H: "entry (Br (tvx_Rc K) ! J) 1 0 < entry (Br (tvx_Rc K) ! J) 0 0" by blast
    have "J < Lng (Br (tvx_Rc K))"
    proof (rule ccontr)
      assume "\<not> J < Lng (Br (tvx_Rc K))"
      hence "Lng (Br (tvx_Rc K)) \<le> J" by simp
      from OOR[OF this] H show False by simp
    qed
    thus "J \<in> {..< Lng (Br (tvx_Rc K))}" by simp
  qed
  hence "finite ?S" using finite_subset finite_lessThan by blast
  thus ?thesis by (simp add: tvx_finRc_def)
qed


(* ===== r62: SETLE1 sec7.4 sub-bricks ox7_ (align3-track+leBT-hole; head-bound(ii) REFUTED, needs RightNodes>=v1) + FINRC A9 root=LastStep_def; consumer bodies ot_finRc_LastStep_* (no fin) ===== *)


(* ===================================================================== *)
(* r62 SETLE1_ltJ sec7.4-head-bound front (prefix ox7_):                  *)
(*   BRICK (iii) -- the LOCALIZED-HOLE le-lex congruence, and a targeted  *)
(*   empirical NOTE recording that the r61 head-bound sub-brick (ii) as   *)
(*   literally posed is REFUTED (see the census note above the lemma).    *)
(* ===================================================================== *)

subsection \<open>\<open>ox7_scbext_leBT_hole\<close>: le-lex congruence at a shared right-spine
  hole (le-version of @{thm [source] scbext_lessBT})\<close>

text \<open>@{text ox7_scbext_leBT_hole}: if two trees \<open>t\<close>, \<open>t'\<close> share the same scb
  wrapper \<open>(s, b)\<close> (\<open>b\<close> all-\<open>RP\<close>) and differ only at a same-head hole principal
  \<open>D\<^bsub>w\<^esub> a\<^sub>1\<close> resp. \<open>D\<^bsub>w\<^esub> a\<^sub>2\<close>, then \<open>a\<^sub>1 \<le> a\<^sub>2 \<Longrightarrow> t \<le> t'\<close>.  The strict half is
  @{thm [source] scbext_lessBT} at the hole \<open>DB w a\<^sub>1 < DB w a\<^sub>2\<close> (from
  \<open>a\<^sub>1 < a\<^sub>2\<close>); the equality half is @{thm [source] m_7_flatBT_inj}.  This is the
  reusable localized-hole lex step (BRICK (iii) of the r62 sec7.4 front): the
  order of the two whole trees is decided by the order of the hole bodies when
  the hole sits at the shared deepest-right position and the closing context is
  all-\<open>RP\<close>.\<close>

lemma ox7_scbext_leBT_hole:
  fixes t t' :: BT and s b :: "Sym list" and w :: enat and a1 a2 :: BT
  assumes fa: "flatBT t  = s @ flatBP (DB w a1) @ b"
    and fb: "flatBT t' = s @ flatBP (DB w a2) @ b"
    and bRP: "\<forall>x \<in> set b. x = RP"
    and le: "leBT a1 a2"
  shows "leBT t t'"
proof (cases "a1 = a2")
  case True
  have "flatBT t = flatBT t'" using fa fb True by simp
  hence "t = t'" by (rule m_7_flatBT_inj)
  thus ?thesis by simp
next
  case False
  hence "lessBT a1 a2" using le by blast
  hence "lessBP (DB w a1) (DB w a2)" by simp
  hence "lessBT t t'" by (rule scbext_lessBT[OF fa fb bRP])
  thus ?thesis by blast
qed


subsection \<open>\<open>ox7_align3_track\<close>: strengthened right-spine alignment tracking the
  descended context \<open>(sc, bc)\<close> as a suffix of \<open>s\<close> / prefix of \<open>b\<close>\<close>

text \<open>@{text ox7_align3_track}: the strengthened form of
  @{thm [source] otx2_align3} (BRICK (i) of the r62 sec7.4 front).  Identical
  case split, but the deeper-level branch additionally exposes
  \<open>\<exists>pre. s = pre \<frown> sc\<close> and \<open>\<exists>post. b = bc \<frown> post\<close>, i.e. the descended context
  \<open>(sc, bc)\<close> is pinned as a \<^emph>\<open>suffix of the accumulated \<open>s\<close>\<close> and a \<^emph>\<open>prefix of
  \<open>b\<close>\<close>.  This is derived POST-HOC from @{thm [source] otx2_align3}'s output by a
  single flat cancellation: with \<open>t\<^sub>1 = Trm (qs \<frown> [D\<^bsub>w\<^esub> lb\<^sub>1])\<close> and
  \<open>flat lb\<^sub>1 = sc \<frown> flat cp\<^sub>1 \<frown> bc\<close>, computing \<open>flat t\<^sub>1\<close> via
  @{thm [source] flatBT_multi_last} gives
  \<open>flat t\<^sub>1 = (PRE \<frown> D\<^sub>w \<frown> sc) \<frown> flat cp\<^sub>1 \<frown> (bc \<frown> POST)\<close> with \<open>POST\<close> all-\<open>RP\<close>;
  @{thm [source] m_7_2_scb_unique_sb} against \<open>flat t\<^sub>1 = s \<frown> flat cp\<^sub>1 \<frown> b\<close>
  forces \<open>s = PRE \<frown> D\<^sub>w \<frown> sc\<close> and \<open>b = bc \<frown> POST\<close>.  Only \<open>cp\<^sub>1\<close> needs to be a
  principal-term string (\<open>isPTB_str\<close>); the shared \<open>cp\<^sub>2, cp\<^sub>3\<close> do not.\<close>

lemma ox7_align3_track:
  assumes e1: "flatBT t1 = s @ flatBP cp1 @ b"
    and e2: "flatBT t2 = s @ flatBP cp2 @ b"
    and e3: "flatBT t3 = s @ flatBP cp3 @ b"
    and bR: "\<forall>x \<in> set b. x = RP"
    and pc1: "isPTB_str (flatBP cp1)"
  shows "(\<exists>qs. t1 = Trm (qs @ [cp1]) \<and> t2 = Trm (qs @ [cp2]) \<and> t3 = Trm (qs @ [cp3]))
       \<or> (\<exists>qs w lb1 lb2 lb3 sc bc.
            t1 = Trm (qs @ [DB w lb1]) \<and> t2 = Trm (qs @ [DB w lb2])
          \<and> t3 = Trm (qs @ [DB w lb3])
          \<and> flatBT lb1 = sc @ flatBP cp1 @ bc \<and> flatBT lb2 = sc @ flatBP cp2 @ bc
          \<and> flatBT lb3 = sc @ flatBP cp3 @ bc \<and> (\<forall>x \<in> set bc. x = RP)
          \<and> (\<exists>pre. s = pre @ sc) \<and> (\<exists>post. b = bc @ post))"
proof -
  from otx2_align3[OF e1 e2 e3 bR] show ?thesis
  proof (elim disjE exE conjE)
    fix qs
    assume "t1 = Trm (qs @ [cp1])" and "t2 = Trm (qs @ [cp2])"
      and "t3 = Trm (qs @ [cp3])"
    thus ?thesis by blast
  next
    fix qs w lb1 lb2 lb3 sc bc
    assume TA: "t1 = Trm (qs @ [DB w lb1])" and TB: "t2 = Trm (qs @ [DB w lb2])"
      and TC: "t3 = Trm (qs @ [DB w lb3])"
      and F1: "flatBT lb1 = sc @ flatBP cp1 @ bc"
      and F2: "flatBT lb2 = sc @ flatBP cp2 @ bc"
      and F3: "flatBT lb3 = sc @ flatBP cp3 @ bc"
      and BC: "\<forall>x \<in> set bc. x = RP"
    \<comment> \<open>snoc-flat of \<open>t\<^sub>1\<close>: \<open>flat t\<^sub>1 = PRE \<frown> D\<^sub>w \<frown> flat lb\<^sub>1 \<frown> POST\<close>, \<open>POST\<close> all-\<open>RP\<close>\<close>
    obtain PRE POST where
        fdec: "flatBT t1 = PRE @ Dsym w # flatBT lb1 @ POST"
      and postRP: "\<forall>x \<in> set POST. x = RP"
    proof (cases "qs = []")
      case True
      have "flatBT t1 = Dsym w # flatBT lb1" using TA True by simp
      thus ?thesis using that[of "[]" "[]"] by simp
    next
      case False
      have "flatBT t1 = Wpre qs @ flatBP (DB w lb1) @ [RP]"
        using TA flatBT_multi_last[OF False, of "DB w lb1"] by simp
      hence "flatBT t1 = Wpre qs @ Dsym w # flatBT lb1 @ [RP]" by simp
      thus ?thesis using that[of "Wpre qs" "[RP]"] by simp
    qed
    \<comment> \<open>rewrite as an scb around \<open>cp\<^sub>1\<close> and pin \<open>(s, b)\<close> by uniqueness\<close>
    have fT1: "flatBT t1 = (PRE @ Dsym w # sc) @ flatBP cp1 @ (bc @ POST)"
      using fdec F1 by simp
    have bcPOST_RP: "\<forall>x \<in> set (bc @ POST). x = RP" using BC postRP by auto
    have d_new: "scb_decomp t1 (PRE @ Dsym w # sc) (flatBP cp1) (bc @ POST)"
      unfolding scb_decomp_def using fT1 pc1 bcPOST_RP by simp
    have d_old: "scb_decomp t1 s (flatBP cp1) b"
      unfolding scb_decomp_def using e1 pc1 bR by simp
    have t1ne: "t1 \<noteq> Trm []" using TA by simp
    have pin: "s = PRE @ Dsym w # sc \<and> b = bc @ POST"
      by (rule m_7_2_scb_unique_sb[OF d_old d_new t1ne])
    have ssuf: "\<exists>pre. s = pre @ sc" using pin by (metis append.assoc append_Cons append_Nil)
    have bpre: "\<exists>post. b = bc @ post" using pin by blast
    from TA TB TC F1 F2 F3 BC ssuf bpre show ?thesis by blast
  qed
qed


(* ===================================================================== *)
(* ===== r62 FINRC de-risk (sub-task (4)): the CONSUMER-SIDE of the   === *)
(* =====   A9 fin-form fix, ready to plug in once LastStep_def's Min  === *)
(* =====   binder carries the  J < Lng (Br M)  guard.                 === *)
(* ===================================================================== *)

text \<open>\<^bold>\<open>Where \<open>fin\<close> is really consumed, and why bounded finiteness is the fix.\<close>
  Tracing the \<open>fin\<close> hypothesis of @{thm [source] hqx_condIIIV_of_DT} through
  @{thm [source] vg3x_VE2} / @{thm [source] vgx_condIIIV_of_VE}, it is passed to
  @{thm [source] vgx_LastStep_lt_of_guard} and bottoms out at
  @{thm [source] vgx_LastStep_lt_Lng_Br} (\<open>pss_wip\<close>), whose \<^emph>\<open>only\<close> use of
  finiteness is one step
  \[ \<open>Min ?S \<le> J\<^sub>1\<close> \quad\text{by}\quad @{thm [source] Min_le}, \]
  giving \<open>LastStep M < Lng (Br M)\<close>.  Now @{thm [source] LastStep_def} applies
  \<open>Min\<close> to the \<^bold>\<open>unbounded\<close> binder \<open>?S\<close>, and an infinite-set \<open>Min\<close> is
  HOL-unspecified, so \<^bold>\<open>bounded finiteness cannot bound this \<open>Min\<close>\<close>: merely
  threading a \<open>J < Lng\<close> guard through the \<open>fin\<close> hypotheses (leaving
  @{thm [source] LastStep_def} unbounded) will \<^emph>\<open>fail\<close> here.  The genuine A9 fix
  is at the ROOT: guard the \<open>Min\<close> binder of @{thm [source] LastStep_def} with
  \<open>J < Lng (Br M)\<close> (exactly correction A9, already noted in that definition's own
  comment).  Once that is done the two bricks below show the bound
  \<open>LastStep M < Lng (Br M)\<close> holds with \<^bold>\<open>NO finiteness hypothesis at all\<close> --- so
  the entire \<open>fin\<close>/\<open>FIN\<close>/\<open>FINr\<close>/\<open>FINRC\<close> cascade becomes \<^emph>\<open>vacuous\<close> (droppable),
  not merely guarded, and @{term tvx_finRc}/@{thm [source] tvx_finRc_def} can be
  deleted outright.\<close>

lemma ot_finRc_LastStep_bounded_lt:
  \<comment> \<open>the post-correction body of @{thm [source] vgx_LastStep_lt_Lng_Br}, with the
      \<open>fin\<close> premise ELIMINATED: the guarded else-branch \<open>Min\<close> is unconditionally
      in range.\<close>
  fixes M :: pairseq
  assumes Brne: "Br M \<noteq> []"
    and gt: "entry (Br M ! (Lng (Br M) - 1)) 1 0 < entry (Br M ! (Lng (Br M) - 1)) 0 0"
  shows "Min {J. J < Lng (Br M)
                 \<and> entry (Br M ! (Lng (Br M) - 1)) 0 0 = entry (Br M ! J) 0 0
                 \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}
         < Lng (Br M)"
proof -
  let ?J1 = "Lng (Br M) - 1"
  let ?Sb = "{J. J < Lng (Br M)
                 \<and> entry (Br M ! ?J1) 0 0 = entry (Br M ! J) 0 0
                 \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}"
  have finSb: "finite ?Sb" by (rule finite_subset[of _ "{..< Lng (Br M)}"]) auto
  have J1lt: "?J1 < Lng (Br M)" using Brne by (cases "Br M") auto
  have mem: "?J1 \<in> ?Sb" using gt J1lt by simp
  have "Min ?Sb \<le> ?J1" using finSb mem by (rule Min_le)
  thus ?thesis using J1lt by simp
qed

lemma ot_finRc_LastStep_guard_bounded_lt:
  \<comment> \<open>the post-correction drop-in for @{thm [source] vgx_LastStep_lt_of_guard}:
      from the paper guard (row-1 \<open><\<close> row-0 at the last first node) alone, the
      guarded-\<open>Min\<close> \<open>LastStep\<close> is in range --- \<^bold>\<open>no \<open>fin\<close>\<close>.\<close>
  fixes M :: pairseq
  assumes MP: "M \<in> PT_PS" and Brne: "Br M \<noteq> []"
    and guard: "entry M 1 (FirstNodes M ! (Lng (Br M) - 1))
                  < entry M 0 (FirstNodes M ! (Lng (Br M) - 1))"
  shows "Min {J. J < Lng (Br M)
                 \<and> entry (Br M ! (Lng (Br M) - 1)) 0 0 = entry (Br M ! J) 0 0
                 \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}
         < Lng (Br M)"
proof -
  have h0: "entry (Br M ! (Lng (Br M) - 1)) 0 0
              = entry M 0 (FirstNodes M ! (Lng (Br M) - 1))"
    by (rule vgx_Br_last_head[OF MP Brne])
  have h1: "entry (Br M ! (Lng (Br M) - 1)) 1 0
              = entry M 1 (FirstNodes M ! (Lng (Br M) - 1))"
    by (rule vgx_Br_last_head[OF MP Brne])
  have gt: "entry (Br M ! (Lng (Br M) - 1)) 1 0 < entry (Br M ! (Lng (Br M) - 1)) 0 0"
    using guard h0 h1 by simp
  show ?thesis by (rule ot_finRc_LastStep_bounded_lt[OF Brne gt])
qed


(* ===== r63: SETLE1 sec7.4 RightNodes(body)>=v1 (ox7_) [front A] + buc1 wds_collapse attack-surface wcl_ bricks [front B] ===== *)


(* ===================================================================== *)
(* r63 SETLE1_ltJ sec7.4 spine-monotonicity (prefix ox7_):                *)
(*   the TRUE residual lower bound RightNodes(body) >= v1.                 *)
(*                                                                        *)
(*   KEY: the pkg already hands us  k1 : scb_kind1 (Trans M) s1           *)
(*   (flatBT (D_e3 body)) b1.  scb_kind1's own RightNodes condition IS    *)
(*   the spine head-monotonicity: for r = RightNodes (Trm [D_e3 body])    *)
(*   = e3 # RightNodes body and j1 = |r|-1, all MIDDLE nodes r!j (0<j<j1) *)
(*   are >= r!j1, the DEEPEST head.  And the deepest head r!j1 = v1,       *)
(*   because inner shows body's flat ends in the hole  D_v1 0  (so        *)
(*   rnsub_RightNodes_t0_lastv gives RightNodes body = a0 @ [v1]).  Hence *)
(*   every entry of RightNodes body is >= v1.  (The r62 head-bound        *)
(*   "A0 heads <= ub" is REFUTED and is NOT used.)                        *)
(* ===================================================================== *)

subsection \<open>\<open>ox7_RightNodes_body_ge_v1\<close>: every right-spine head of the terminal
  mono slice body is \<open>\<ge> v\<^sub>1\<close>\<close>

text \<open>@{text ox7_RightNodes_body_ge_v1}: the NEW sec7.4 spine-monotonicity fact
  behind the SETLE1 spine head bound.  \<open>body = bpHeadT (Trans (s84x_N M))\<close> is the
  head body of a \<open>Trans\<close>-image whose enclosing principal \<open>D\<^bsub>e\<^sub>3\<^esub> body\<close> is a
  \<^bold>\<open>kind-1\<close> scb-block (@{thm [source] oi5_IIIIV_pkg}'s \<open>k1\<close>).  The kind-1
  RightNodes condition says the middle spine heads dominate the deepest head;
  the deepest head is \<open>v\<^sub>1\<close> (the hole \<open>D\<^bsub>v\<^sub>1\<^esub> 0\<close> of \<open>inner\<close>, read off by
  @{thm [source] rnsub_RightNodes_t0_lastv}), so ALL heads are \<open>\<ge> v\<^sub>1\<close>.\<close>

lemma ox7_RightNodes_body_ge_v1:
  fixes M :: pairseq
  assumes NST: "M \<in> ST_PS" and NPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
    and ltJ: "s84x_jm3 M < transJm1 M"
  shows "\<forall>x \<in> set (RightNodes (bpHeadT (Trans (s84x_N M)))).
            entry M 1 (Lng M - 1) \<le> x"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N M)))"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  obtain s0 b0 s1 b1 where
    b0RP: "\<forall>x \<in> set b0. x = RP" and b1RP: "\<forall>x \<in> set b1. x = RP"
    and inner: "scb_decomp ?body s0 (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0"
    and k1: "scb_kind1 (Trans M) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    and mn: "\<forall>m. 1 \<le> m \<longrightarrow>
        flatBT (Trans ((M::pairseq)[m]))
          = s1 @ Dsym (enat ?e3)
              # flatBT (d4vx_core s0 ?ub b0 ?A0 (m - 1)) @ b1"
    and base0: "lessBT (Dpt (enat ?ub) 0\<^sub>B) ?A0"
    and base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 0\<^sub>B)"
    and A0TB: "?A0 \<in> T_B"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  have bodyT: "?body \<in> T_B" by (rule oi5_regime(3)[OF NST NPT hp j1gt branch])
  \<comment> \<open>flat form of body: ends in the hole \<open>D\<^bsub>v\<^sub>1\<^esub> 0\<close>\<close>
  have fbody: "flatBT ?body = s0 @ Dsym (enat ?v1) # Zsym # b0"
    using inner by (simp add: scb_decomp_def)
  \<comment> \<open>hence \<open>RightNodes body\<close> ends in \<open>v\<^sub>1\<close>\<close>
  obtain a0 where RNbody: "RightNodes ?body = a0 @ [?v1]"
    using rnsub_RightNodes_t0_lastv[OF fbody b0RP bodyT] by blast
  \<comment> \<open>the kind-1 head-monotonicity for the enclosing principal \<open>D\<^bsub>e\<^sub>3\<^esub> body\<close>\<close>
  let ?p = "DB (enat ?e3) ?body"
  let ?r = "RightNodes (Trm [?p])"
  let ?j1 = "Lng ?r - 1"
  have cflat: "flatBT (Dpt (enat ?e3) ?body) = flatBP ?p" by simp
  have rform: "?r = ?e3 # RightNodes ?body" by (simp add: rnsub_RN_single)
  have rval: "?r = ?e3 # (a0 @ [?v1])" using rform RNbody by simp
  have j1val: "?j1 = Suc (length a0)" using rval by simp
  have rj1: "?r ! ?j1 = ?v1" using rval j1val by (simp add: nth_append)
  \<comment> \<open>unfold the kind-1 window property at \<open>?p\<close>\<close>
  have KC: "let r = RightNodes (Trm [?p]); j1 = Lng r - 1 in
             j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
  proof -
    from k1 have "\<forall>p. flatBT (Dpt (enat ?e3) ?body) = flatBP p \<longrightarrow>
          (let r = RightNodes (Trm [p]); j1 = Lng r - 1 in
           j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1))"
      by (simp add: scb_kind1_def)
    from this[rule_format, OF cflat] show ?thesis .
  qed
  have rmono: "\<forall>j. 0 < j \<and> j < ?j1 \<longrightarrow> ?r ! j \<ge> ?r ! ?j1"
    using KC by (simp add: Let_def)
  \<comment> \<open>every element of \<open>RightNodes body\<close> is \<open>\<ge> v\<^sub>1\<close>\<close>
  show "\<forall>x \<in> set (RightNodes ?body). ?v1 \<le> x"
  proof
    fix x assume xin: "x \<in> set (RightNodes ?body)"
    have "x \<in> set (a0 @ [?v1])" using xin RNbody by simp
    hence "x \<in> set a0 \<or> x = ?v1" by auto
    thus "?v1 \<le> x"
    proof
      assume "x = ?v1" thus ?thesis by simp
    next
      assume "x \<in> set a0"
      then obtain k where klt: "k < length a0" and xk: "a0 ! k = x"
        by (auto simp: in_set_conv_nth)
      have rSuck: "?r ! Suc k = x"
      proof -
        have "?r ! Suc k = (a0 @ [?v1]) ! k" using rval by simp
        also have "\<dots> = a0 ! k" using klt by (simp add: nth_append)
        finally show ?thesis using xk by simp
      qed
      have "0 < Suc k" by simp
      moreover have "Suc k < ?j1" using klt j1val by simp
      ultimately have "?r ! Suc k \<ge> ?r ! ?j1" using rmono by blast
      thus ?thesis using rSuck rj1 by simp
    qed
  qed
qed


(* ===================================================================== *)
(* ===== r63 wcl: buc1-collapse --- engine-entry framing of THE       ===== *)
(* ===== residual wds_collapse (= wfj_collapse_core = wfc_pbody_acc    ===== *)
(* ===== = wf RPrel), the last external citation [Buc1] Lemma 2.2      ===== *)
(* ===== (Buchholz--Schuette Fundierung of (OT_B,<)).                  ===== *)
(* =====                                                               ===== *)
(* ===== This block delivers UNCONDITIONAL structural bricks that      ===== *)
(* ===== sharpen the attack surface for the collapse, WITHOUT citing   ===== *)
(* ===== any residual:                                                 ===== *)
(* =====  (A) wcl_min_bad_secured: the wfs_szP-minimal counterexample  ===== *)
(* =====      to accessibility is automatically G-trace-SECURED        ===== *)
(* =====      (wfj_secT) --- the standard [Buc1]/Buchholz--Schuette     ===== *)
(* =====      entry point: what the collapse engine must refute is a    ===== *)
(* =====      SECURED principal that fails to be accessible.            ===== *)
(* =====  (B) wcl_accfrag_*: the accessible fragment                   ===== *)
(* =====      wfj_frag v \<inter> acc RPrel satisfies the domain/downward/    ===== *)
(* =====      relative-acc clauses of wds_distinguished UNCONDITIONALLY;===== *)
(* =====      its 4th (G-progressiveness) clause is EXACTLY the         ===== *)
(* =====      collapse-core, so under the residual it is the CONCRETE   ===== *)
(* =====      maximal v-distinguished set (= wds_Mset v), discharging   ===== *)
(* =====      the r54 honesty note on D1 witness existence.             ===== *)
(* ===================================================================== *)

section \<open>r63-wcl --- [Buc1] 2.2 collapse: engine-entry framing (prefix \<open>wcl_\<close>)\<close>

subsection \<open>(A) The minimal counterexample to the collapse is \<open>G\<close>-trace-secured\<close>

text \<open>Contrapositive entry point of \<open>wfj_acc_of_collapse_core\<close>: if some
  \<open>OT\<close>+\<open>dfree\<close> principal is NOT \<open>RPrel\<close>-accessible, then a \<open>wfs_szP\<close>-minimal
  such principal \<open>D\<^sub>v b\<close> has its whole \<open>G\<^sub>v\<close>-trace already SECURED
  (\<open>wfj_secT\<close>): the trace components are proper subterms (\<open>wfj_G_szT\<close>), hence
  accessible by \<open>wfs_szP\<close>-minimality.  This is exactly the object the [Buc1]
  Lemma 2.2 collapse must refute --- a secured principal failing to be
  accessible.  Because \<open>wfj_collapse_core \<longleftrightarrow> wf RPrel\<close>
  (\<open>wfj_collapse_core_iff_wf\<close>) and \<open>wds_collapse \<longleftrightarrow> wf RPrel\<close>
  (\<open>wds_collapse_iff_wf\<close>), refuting this single witness closes the last
  external citation.  Unconditional (no residual cited).\<close>

lemma wcl_min_bad_secured:
  assumes bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  shows "\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
               \<and> DB v b \<notin> Wellfounded.acc RPrel
               \<and> (\<forall>x \<in> GBT v b. wfj_secT x)"
proof -
  define Bad where
    "Bad = {p. isOT_BP p \<and> dfree_BP p \<and> p \<notin> Wellfounded.acc RPrel}"
  from bad obtain p0 where p0Bad: "p0 \<in> Bad" unfolding Bad_def by blast
  have wfm: "wf (measure wfs_szP)" by (rule wf_measure)
  have "\<exists>z\<in>Bad. \<forall>y. (y, z) \<in> measure wfs_szP \<longrightarrow> y \<notin> Bad"
    using wfm[unfolded wf_eq_minimal] p0Bad by blast
  then obtain z where zBad: "z \<in> Bad"
    and zmin: "\<forall>y. (y, z) \<in> measure wfs_szP \<longrightarrow> y \<notin> Bad" by blast
  have zot: "isOT_BP z" and zdf: "dfree_BP z"
    and znacc: "z \<notin> Wellfounded.acc RPrel"
    using zBad unfolding Bad_def by auto
  obtain v b where zeq: "z = DB v b" by (cases z) auto
  have otb: "isOT_BT b" using zot zeq by simp
  have dfb: "dfree_BT b" using zdf zeq by simp
  have sec: "\<forall>x \<in> GBT v b. wfj_secT x"
  proof
    fix x assume xG: "x \<in> GBT v b"
    have otx: "isOT_BT x" using wfj_G_OT_T otb xG by blast
    have dfx: "dfree_BT x" using wfj_G_df_T dfb xG by blast
    have szx: "wfs_szT x < wfs_szT b" using wfj_G_szT xG by blast
    obtain rs where xeq: "x = Trm rs" by (cases x) auto
    have "\<forall>r \<in> set rs. r \<in> Wellfounded.acc RPrel"
    proof
      fix r assume rin: "r \<in> set rs"
      have otr: "isOT_BP r" using otx xeq rin by simp
      have dfr: "dfree_BP r" using dfx xeq rin by simp
      have szr: "wfs_szP r < wfs_szT x" using wfs_szP_mem_lt[OF rin] xeq by simp
      have szb: "wfs_szP z = Suc (wfs_szT b)" using zeq by simp
      have "wfs_szP r < wfs_szP z" using szr szx szb by linarith
      then have "(r, z) \<in> measure wfs_szP" by simp
      then have "r \<notin> Bad" using zmin by blast
      then show "r \<in> Wellfounded.acc RPrel"
        using otr dfr unfolding Bad_def by blast
    qed
    then show "wfj_secT x" using xeq by simp
  qed
  show ?thesis using zot zdf znacc sec zeq by blast
qed

text \<open>The immediate corollary in the exact \<open>wfj_collapse_core\<close> shape: refuting
  the secured witness IS the collapse core (hence \<open>wf RPrel\<close> and [Buc1] 2.2).
  This is the sharpest self-contained statement of what remains.\<close>

lemma wcl_core_iff_no_bad_secured:
  "wfj_collapse_core \<longleftrightarrow>
     \<not> (\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
             \<and> DB v b \<notin> Wellfounded.acc RPrel
             \<and> (\<forall>x \<in> GBT v b. wfj_secT x))"
proof
  assume C: "wfj_collapse_core"
  show "\<not> (\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
             \<and> DB v b \<notin> Wellfounded.acc RPrel
             \<and> (\<forall>x \<in> GBT v b. wfj_secT x))"
    using C[unfolded wfj_collapse_core_def] by blast
next
  assume R: "\<not> (\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
             \<and> DB v b \<notin> Wellfounded.acc RPrel
             \<and> (\<forall>x \<in> GBT v b. wfj_secT x))"
  show "wfj_collapse_core"
    unfolding wfj_collapse_core_def using R by blast
qed

subsection \<open>(B) The accessible fragment \<open>wfj_frag v \<inter> acc RPrel\<close> is the
  concrete maximal \<open>v\<close>-distinguished set\<close>

text \<open>Clauses 1--3 (domain, \<open>RPrel\<close>-downward closure, relative accessibility)
  of \<open>wds_distinguished\<close> hold for \<open>A\<^sub>v = wfj_frag v \<inter> acc RPrel\<close>
  UNCONDITIONALLY; clause 4 (\<open>G\<close>-progressiveness) is discharged by
  \<open>wfj_collapse_core\<close>.  So under the residual \<open>A\<^sub>v\<close> is the CONCRETE witness that
  the r54 D1 lemma (\<open>wds_Mset_distinguished\<close>) left abstract, and
  \<open>wds_Mset v = wfj_frag v \<inter> acc RPrel\<close>.\<close>

lemma wcl_accfrag_downclosed:
  assumes pA: "p \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
    and qp: "(q, p) \<in> RPrel"
  shows "q \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
proof -
  have qf: "q \<in> wfj_frag v" using wfj_frag_downclosed pA qp by blast
  have pacc: "p \<in> Wellfounded.acc RPrel" using pA by blast
  have "q \<in> Wellfounded.acc RPrel" using acc_downward[OF pacc qp] .
  then show ?thesis using qf by blast
qed

lemma wcl_accfrag_relacc:
  assumes pA: "p \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
  shows "p \<in> Wellfounded.acc (Restr RPrel (wfj_frag v \<inter> Wellfounded.acc RPrel))"
proof -
  have "p \<in> Wellfounded.acc RPrel" using pA by blast
  moreover have "Restr RPrel (wfj_frag v \<inter> Wellfounded.acc RPrel) \<subseteq> RPrel"
    by blast
  ultimately show ?thesis using acc_subset by blast
qed

lemma wcl_accfrag_prog_of_core:
  assumes C: "wfj_collapse_core"
    and uv: "u \<le> v" and ot: "isOT_BP (DB (enat u) c)"
    and df: "dfree_BP (DB (enat u) c)"
    and cnt: "\<forall>x \<in> GBT (enat u) c.
                x \<in> wds_hullT (wfj_frag v \<inter> Wellfounded.acc RPrel)"
  shows "DB (enat u) c \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
proof -
  have sec: "\<forall>x \<in> GBT (enat u) c. wfj_secT x"
  proof
    fix x assume xG: "x \<in> GBT (enat u) c"
    obtain rs where xeq: "x = Trm rs" by (cases x) auto
    have "\<forall>r \<in> set rs. r \<in> Wellfounded.acc RPrel"
    proof
      fix r assume rin: "r \<in> set rs"
      have "r \<in> set (untrm x)" using xeq rin by simp
      then have "r \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
        using cnt xG by (simp add: wds_hullT_iff)
      then show "r \<in> Wellfounded.acc RPrel" by blast
    qed
    then show "wfj_secT x" using xeq by simp
  qed
  have acc: "DB (enat u) c \<in> Wellfounded.acc RPrel"
    using C[unfolded wfj_collapse_core_def] ot df sec by blast
  have "wfj_hd (DB (enat u) c) \<le> enat v" using uv by simp
  then have "DB (enat u) c \<in> wfj_frag v" using ot df by (simp add: wfj_frag_def)
  then show ?thesis using acc by blast
qed

theorem wcl_accfrag_distinguished_of_core:
  assumes C: "wfj_collapse_core"
  shows "wds_distinguished v (wfj_frag v \<inter> Wellfounded.acc RPrel)"
proof (rule wds_distI)
  show "wfj_frag v \<inter> Wellfounded.acc RPrel \<subseteq> wfj_frag v" by blast
next
  fix p q assume "p \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
    and "(q, p) \<in> RPrel"
  then show "q \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
    by (rule wcl_accfrag_downclosed)
next
  fix p assume "p \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
  then show "p \<in> Wellfounded.acc (Restr RPrel (wfj_frag v \<inter> Wellfounded.acc RPrel))"
    by (rule wcl_accfrag_relacc)
next
  fix u c
  assume "u \<le> v" and "isOT_BP (DB (enat u) c)" and "dfree_BP (DB (enat u) c)"
    and "\<forall>x \<in> GBT (enat u) c.
           x \<in> wds_hullT (wfj_frag v \<inter> Wellfounded.acc RPrel)"
  then show "DB (enat u) c \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
    by (rule wcl_accfrag_prog_of_core[OF C])
qed

corollary wcl_Mset_distinguished_of_core:
  assumes C: "wfj_collapse_core"
  shows "wds_distinguished v (wds_Mset v)"
  by (rule wds_Mset_distinguished[OF wcl_accfrag_distinguished_of_core[OF C]])

corollary wcl_Mset_eq_accfrag_of_core:
  assumes C: "wfj_collapse_core"
  shows "wds_Mset v = wfj_frag v \<inter> Wellfounded.acc RPrel"
proof (rule subset_antisym)
  have "wds_Mset v \<subseteq> wfj_frag v" by (rule wds_Mset_frag)
  moreover have "wds_Mset v \<subseteq> Wellfounded.acc RPrel"
    by (rule wds_Mset_subset_acc)
  ultimately show "wds_Mset v \<subseteq> wfj_frag v \<inter> Wellfounded.acc RPrel" by blast
next
  show "wfj_frag v \<inter> Wellfounded.acc RPrel \<subseteq> wds_Mset v"
    by (rule wds_Mset_upper[OF wcl_accfrag_distinguished_of_core[OF C]])
qed

text \<open>Direct single-name bridge between the two named residuals (previously
  connected only transitively through \<open>wf RPrel\<close>): the collapse core yields
  \<open>wds_collapse\<close> via the concrete accessible-fragment witness.\<close>

corollary wcl_collapse_of_core:
  assumes "wfj_collapse_core" shows "wds_collapse"
  by (rule wds_collapse_of_wf[OF wfj_wf_RPrel_of_collapse_core[OF assms]])

subsection \<open>(C) The minimal counterexample has an \<open>RTrel\<close>-accessible BODY:
  the obstruction is purely the head-\<open>< v\<close> lower segment\<close>

text \<open>Sharper than (A): the \<open>wfs_szP\<close>-minimal non-accessible \<open>OT\<close>+\<open>dfree\<close>
  principal \<open>D\<^sub>v b\<close> has an \<open>RTrel\<close>-accessible BODY \<open>b\<close> (its DIRECT components
  are proper subterms, accessible by minimality; \<open>wfj_secT_tuple_acc\<close>).  Note
  this is complementary to (A): the \<open>G\<^sub>v\<close>-trace shields head-\<open>< v\<close> principals
  (r52 note: they are NOT covered by \<open>wfj_secT\<close>), whereas the direct body
  components ARE secured by size-minimality.\<close>

lemma wcl_min_bad_body_acc:
  assumes bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  shows "\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
               \<and> DB v b \<notin> Wellfounded.acc RPrel
               \<and> b \<in> Wellfounded.acc RTrel"
proof -
  define Bad where
    "Bad = {p. isOT_BP p \<and> dfree_BP p \<and> p \<notin> Wellfounded.acc RPrel}"
  from bad obtain p0 where p0Bad: "p0 \<in> Bad" unfolding Bad_def by blast
  have wfm: "wf (measure wfs_szP)" by (rule wf_measure)
  have "\<exists>z\<in>Bad. \<forall>y. (y, z) \<in> measure wfs_szP \<longrightarrow> y \<notin> Bad"
    using wfm[unfolded wf_eq_minimal] p0Bad by blast
  then obtain z where zBad: "z \<in> Bad"
    and zmin: "\<forall>y. (y, z) \<in> measure wfs_szP \<longrightarrow> y \<notin> Bad" by blast
  have zot: "isOT_BP z" and zdf: "dfree_BP z"
    and znacc: "z \<notin> Wellfounded.acc RPrel"
    using zBad unfolding Bad_def by auto
  obtain v b where zeq: "z = DB v b" by (cases z) auto
  have otb: "isOT_BT b" using zot zeq by simp
  have dfb: "dfree_BT b" using zdf zeq by simp
  have secb: "wfj_secT b"
  proof -
    obtain bs where beq: "b = Trm bs" by (cases b) auto
    have "\<forall>r \<in> set bs. r \<in> Wellfounded.acc RPrel"
    proof
      fix r assume rin: "r \<in> set bs"
      have otr: "isOT_BP r" using otb beq rin by simp
      have dfr: "dfree_BP r" using dfb beq rin by simp
      have szr: "wfs_szP r < wfs_szT b" using wfs_szP_mem_lt[OF rin] beq by simp
      have szb: "wfs_szP z = Suc (wfs_szT b)" using zeq by simp
      have "wfs_szP r < wfs_szP z" using szr szb by linarith
      then have "(r, z) \<in> measure wfs_szP" by simp
      then have "r \<notin> Bad" using zmin by blast
      then show "r \<in> Wellfounded.acc RPrel"
        using otr dfr unfolding Bad_def by blast
    qed
    then show ?thesis using beq by simp
  qed
  have bacc: "b \<in> Wellfounded.acc RTrel"
    by (rule wfj_secT_tuple_acc[OF otb dfb secb])
  show ?thesis using zot zdf znacc bacc zeq by blast
qed

text \<open>Consequently the residual localizes to the head index: any minimal
  body-accessible counterexample sits STRICTLY ABOVE a lower-head
  counterexample.  With \<open>wfc_principal_acc_of_body\<close> (already proven: an
  \<open>OT\<close>+\<open>dfree\<close> principal with an \<open>RTrel\<close>-accessible body and ALL head-\<open>< v\<close>
  predecessors accessible is itself accessible), a witness whose head-\<open>< v\<close>
  segment were fully accessible would be accessible --- contradiction.  Hence
  the obstruction is NOT the body but the lower collapsing segment
  \<open>wfj_frag (v-1)\<close> (unbounded \<open>wfs_szP\<close> by \<open>wfj_frag0_lv_unbounded\<close>, so out of
  reach of size-minimality); this head-index descent is exactly the [Buc1]
  Lemma 2.2 transfinite recursion on \<open>v\<close>.\<close>

corollary wcl_lower_head_bad_exists:
  assumes bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  shows "\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
               \<and> DB v b \<notin> Wellfounded.acc RPrel
               \<and> b \<in> Wellfounded.acc RTrel
               \<and> (\<exists>r. isOT_BP r \<and> dfree_BP r \<and> wfj_hd r < v
                      \<and> r \<notin> Wellfounded.acc RPrel)"
proof -
  obtain v b where otp: "isOT_BP (DB v b)" and dfp: "dfree_BP (DB v b)"
    and nacc: "DB v b \<notin> Wellfounded.acc RPrel"
    and bacc: "b \<in> Wellfounded.acc RTrel"
    using wcl_min_bad_body_acc[OF bad] by blast
  have "\<exists>r. isOT_BP r \<and> dfree_BP r \<and> wfj_hd r < v \<and> r \<notin> Wellfounded.acc RPrel"
  proof (rule ccontr)
    assume "\<not> (\<exists>r. isOT_BP r \<and> dfree_BP r \<and> wfj_hd r < v
                   \<and> r \<notin> Wellfounded.acc RPrel)"
    then have hlt: "\<And>r. isOT_BP r \<Longrightarrow> dfree_BP r \<Longrightarrow> wfj_hd r < v
                        \<Longrightarrow> r \<in> Wellfounded.acc RPrel" by blast
    have "DB v b \<in> Wellfounded.acc RPrel"
      by (rule wfc_principal_acc_of_body[OF hlt bacc otp dfp])
    then show False using nacc by blast
  qed
  then show ?thesis using otp dfp nacc bacc by blast
qed

(* ===================================================================== *)
(* ===== r64: wcl_ continuation --- the LEXICOGRAPHIC (head, size)     ===== *)
(* ===== minimal bad witness, and the sharp UPPER-COMPONENT residual.  ===== *)
(* =====                                                               ===== *)
(* ===== r63 exposed two INCOMPATIBLE minimality framings:             ===== *)
(* =====   * SIZE-minimal bad (wcl_min_bad_body_acc): body is acc, but  ===== *)
(* =====     head-<v predecessors may be LARGER (out of reach), so the ===== *)
(* =====     wfc_principal_acc_of_body hlt-premise is NOT discharged.   ===== *)
(* =====   * HEAD-minimal bad: hlt IS discharged, but the body need not ===== *)
(* =====     be acc.                                                    ===== *)
(* ===== The resolution is the LEXICOGRAPHIC minimum on (head, size)   ===== *)
(* ===== with HEAD dominating: it discharges BOTH the head-<n branch   ===== *)
(* ===== (i, by head-minimality) AND the head-=n smaller-body branch   ===== *)
(* ===== (ii, by size-minimality within the level).  The SOLE residual ===== *)
(* ===== is then the head->n ("upper", shielded/collapsed) components  ===== *)
(* ===== of the minimal-bad body --- exactly the psi-collapse content  ===== *)
(* ===== of [Buc1] Lemma 2.2.  This is a genuine sharpening: the entire ===== *)
(* ===== head-<= n segment of the minimal-bad body is now free.        ===== *)
(* ===================================================================== *)

subsection \<open>(D) The lexicographic \<open>(head, size)\<close>-minimal bad witness\<close>

text \<open>If some \<open>OT\<close>+\<open>dfree\<close> principal is not \<open>RPrel\<close>-accessible, then a
  \<open>(wfj_hd, wfs_szP)\<close>-lexicographically-minimal such principal \<open>D\<^bsub>n\<^esub> b\<close> has:
  (i) EVERY strictly-lower-head \<open>OT\<close>+\<open>dfree\<close> principal accessible (head
  minimality), and (ii) EVERY equal-head strictly-smaller principal accessible
  (size minimality at the level).  The lexicographic wellorder is the standard
  \<open>less_than <*lex*> less_than\<close> pulled back along \<open>g p = (hd\<^sub>nat p, wfs_szP p)\<close>.\<close>

lemma wcl_min_bad_lex:
  assumes bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  shows "\<exists>n b. isOT_BP (DB (enat n) b) \<and> dfree_BP (DB (enat n) b)
             \<and> DB (enat n) b \<notin> Wellfounded.acc RPrel
             \<and> (\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
                    \<longrightarrow> r \<in> Wellfounded.acc RPrel)
             \<and> (\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
                    \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
                    \<longrightarrow> c \<in> Wellfounded.acc RPrel)"
proof -
  define Bad where
    "Bad = {p. isOT_BP p \<and> dfree_BP p \<and> p \<notin> Wellfounded.acc RPrel}"
  define g :: "BP \<Rightarrow> nat \<times> nat" where
    "g = (\<lambda>p. (case wfj_hd p of enat k \<Rightarrow> k | \<infinity> \<Rightarrow> 0, wfs_szP p))"
  from bad obtain p0 where p0Bad: "p0 \<in> Bad" unfolding Bad_def by blast
  have wfR: "wf (inv_image (less_than <*lex*> less_than) g)"
    by (rule wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  have "\<exists>z\<in>Bad. \<forall>y. (y, z) \<in> inv_image (less_than <*lex*> less_than) g
                       \<longrightarrow> y \<notin> Bad"
    using wfR[unfolded wf_eq_minimal] p0Bad by blast
  then obtain z where zBad: "z \<in> Bad"
    and zmin: "\<forall>y. (y, z) \<in> inv_image (less_than <*lex*> less_than) g \<longrightarrow> y \<notin> Bad"
    by blast
  have zot: "isOT_BP z" and zdf: "dfree_BP z"
    and znacc: "z \<notin> Wellfounded.acc RPrel"
    using zBad unfolding Bad_def by auto
  obtain v b where zeq0: "z = DB v b" by (cases z) auto
  have "v \<noteq> \<infinity>" using zdf zeq0 by simp
  then obtain n where vn: "v = enat n" by (cases v) auto
  have zeq: "z = DB (enat n) b" using zeq0 vn by simp
  have gz: "g z = (n, wfs_szP z)" using zeq by (simp add: g_def)
  \<comment> \<open>(i) head minimality: every strictly-lower-head principal is accessible\<close>
  have i: "\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
                \<longrightarrow> r \<in> Wellfounded.acc RPrel"
  proof (intro allI impI)
    fix r assume otr: "isOT_BP r" and dfr: "dfree_BP r" and hlt: "wfj_hd r < enat n"
    show "r \<in> Wellfounded.acc RPrel"
    proof (rule ccontr)
      assume nacc: "r \<notin> Wellfounded.acc RPrel"
      then have rBad: "r \<in> Bad" using otr dfr unfolding Bad_def by blast
      obtain u w where req: "r = DB u w" by (cases r) auto
      have "u \<noteq> \<infinity>" using dfr req by simp
      then obtain m where um: "u = enat m" by (cases u) auto
      have hdr: "wfj_hd r = enat m" using req um by simp
      then have mn: "m < n" using hlt by simp
      have gr: "g r = (m, wfs_szP r)" using hdr by (simp add: g_def)
      have "(g r, g z) \<in> less_than <*lex*> less_than"
        using mn gr gz by (simp add: lex_prod_def)
      then have "(r, z) \<in> inv_image (less_than <*lex*> less_than) g"
        by (simp add: inv_image_def)
      then have "r \<notin> Bad" using zmin by blast
      then show False using rBad by blast
    qed
  qed
  \<comment> \<open>(ii) size minimality within the level \<open>n\<close>\<close>
  have ii: "\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
                 \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
                 \<longrightarrow> c \<in> Wellfounded.acc RPrel"
  proof (intro allI impI)
    fix c assume otc: "isOT_BP c" and dfc: "dfree_BP c"
      and hdc: "wfj_hd c = enat n" and szc: "wfs_szP c < wfs_szP (DB (enat n) b)"
    show "c \<in> Wellfounded.acc RPrel"
    proof (rule ccontr)
      assume nacc: "c \<notin> Wellfounded.acc RPrel"
      then have cBad: "c \<in> Bad" using otc dfc unfolding Bad_def by blast
      have gc: "g c = (n, wfs_szP c)" using hdc by (simp add: g_def)
      have szc': "wfs_szP c < wfs_szP z" using szc zeq by simp
      have "(g c, g z) \<in> less_than <*lex*> less_than"
        using szc' gc gz by (simp add: lex_prod_def)
      then have "(c, z) \<in> inv_image (less_than <*lex*> less_than) g"
        by (simp add: inv_image_def)
      then have "c \<notin> Bad" using zmin by blast
      then show False using cBad by blast
    qed
  qed
  have zot': "isOT_BP (DB (enat n) b)" using zot zeq by simp
  have zdf': "dfree_BP (DB (enat n) b)" using zdf zeq by simp
  have znacc': "DB (enat n) b \<notin> Wellfounded.acc RPrel" using znacc zeq by simp
  show ?thesis using zot' zdf' znacc' i ii by blast
qed

subsection \<open>(E) The sharp UPPER-component residual: the last content of [Buc1] 2.2\<close>

text \<open>\<open>wcl_upper\<close> isolates the ONLY thing the collapse must still supply: for a
  lexicographically-minimal bad principal \<open>D\<^bsub>n\<^esub> b\<close> (head-\<open><n\<close> and equal-head
  smaller predecessors already accessible), the body components with head
  STRICTLY GREATER than \<open>n\<close> --- the \<open>\<psi>\<^bsub>n\<^esub>\<close>-shielded / collapsed coefficients ---
  are accessible.  Under this residual, all body components are accessible
  (head-\<open><n\<close> by (i), head-\<open>=n\<close> by (ii) since they are proper subterms, head-\<open>>n\<close>
  by the residual), so the body is \<open>RTrel\<close>-accessible (\<open>wfj_tuple_acc\<close>) and the
  principal is \<open>RPrel\<close>-accessible (\<open>wfc_principal_acc_of_body\<close>) --- a
  contradiction.  Hence \<open>wcl_upper \<Longrightarrow> wf RPrel\<close> and the whole [Buc1] 2.2 chain.\<close>

definition wcl_upper :: bool where
  "wcl_upper \<longleftrightarrow>
     (\<forall>n b. isOT_BP (DB (enat n) b) \<longrightarrow> dfree_BP (DB (enat n) b) \<longrightarrow>
        DB (enat n) b \<notin> Wellfounded.acc RPrel \<longrightarrow>
        (\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
             \<longrightarrow> r \<in> Wellfounded.acc RPrel) \<longrightarrow>
        (\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
             \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
             \<longrightarrow> c \<in> Wellfounded.acc RPrel) \<longrightarrow>
        (\<forall>w c. DB w c \<in> set (untrm b) \<longrightarrow> enat n < w
               \<longrightarrow> DB w c \<in> Wellfounded.acc RPrel))"

theorem wcl_wf_of_upper:
  assumes U: "wcl_upper"
  shows "wf RPrel"
proof (rule ccontr)
  assume nwf: "\<not> wf RPrel"
  have bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  proof
    assume A: "\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel"
    have "\<forall>p. p \<in> Wellfounded.acc RPrel"
    proof
      fix p :: BP
      show "p \<in> Wellfounded.acc RPrel"
      proof (cases "isOT_BP p \<and> dfree_BP p")
        case True thus ?thesis using A by blast
      next
        case False
        show ?thesis
        proof (rule accI)
          fix q assume "(q, p) \<in> RPrel"
          then have "isOT_BP p \<and> dfree_BP p" by (auto simp add: RPrel_def)
          with False show "q \<in> Wellfounded.acc RPrel" by blast
        qed
      qed
    qed
    then have "wf RPrel" using wfs_wf_iff_all_acc by blast
    with nwf show False by blast
  qed
  obtain n b where otp: "isOT_BP (DB (enat n) b)" and dfp: "dfree_BP (DB (enat n) b)"
    and nacc: "DB (enat n) b \<notin> Wellfounded.acc RPrel"
    and i: "\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
                 \<longrightarrow> r \<in> Wellfounded.acc RPrel"
    and ii: "\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
                  \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
                  \<longrightarrow> c \<in> Wellfounded.acc RPrel"
    using wcl_min_bad_lex[OF bad] by blast
  have otb: "isOT_BT b" using otp by simp
  have dfb: "dfree_BT b" using dfp by simp
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  \<comment> \<open>upper components (head \<open>> n\<close>) accessible by the residual\<close>
  have upper: "\<forall>w c. DB w c \<in> set (untrm b) \<longrightarrow> enat n < w
                     \<longrightarrow> DB w c \<in> Wellfounded.acc RPrel"
    using U[unfolded wcl_upper_def] otp dfp nacc i ii by blast
  \<comment> \<open>ALL body components accessible, by trichotomy on the component head\<close>
  have allcomp: "\<forall>r \<in> set (untrm b). r \<in> Wellfounded.acc RPrel"
  proof
    fix r assume rin: "r \<in> set (untrm b)"
    have rin': "r \<in> set bs" using rin beq by simp
    have otr: "isOT_BP r" using otb beq rin' by simp
    have dfr: "dfree_BP r" using dfb beq rin' by simp
    obtain w c where req: "r = DB w c" by (cases r) auto
    have rmem: "DB w c \<in> set (untrm b)" using rin req by simp
    show "r \<in> Wellfounded.acc RPrel"
    proof (cases w "enat n" rule: linorder_cases)
      case less
      have "wfj_hd r < enat n" using req less by simp
      then show ?thesis using i otr dfr by blast
    next
      case equal
      have hd_r: "wfj_hd r = enat n" using req equal by simp
      have "wfs_szP r < wfs_szT (Trm bs)" using wfs_szP_mem_lt[OF rin'] .
      then have "wfs_szP r < wfs_szT b" using beq by simp
      then have szr: "wfs_szP r < wfs_szP (DB (enat n) b)" by simp
      show ?thesis using ii otr dfr hd_r szr by blast
    next
      case greater
      show ?thesis using upper rmem greater req by blast
    qed
  qed
  have bacc: "b \<in> Wellfounded.acc RTrel"
    by (rule wfj_tuple_acc[OF otb dfb allcomp])
  have hlt: "\<And>r. isOT_BP r \<Longrightarrow> dfree_BP r \<Longrightarrow> wfj_hd r < enat n
                 \<Longrightarrow> r \<in> Wellfounded.acc RPrel"
    using i by blast
  have "DB (enat n) b \<in> Wellfounded.acc RPrel"
    by (rule wfc_principal_acc_of_body[OF hlt bacc otp dfp])
  then show False using nacc by blast
qed

text \<open>Converse sanity: \<open>wcl_upper\<close> is EXACTLY theorem-strength (no overshoot).
  Under \<open>wf RPrel\<close> every principal is accessible, so the residual holds
  vacuously (its \<open>D\<^bsub>n\<^esub> b \<notin> acc\<close> premise is never met).\<close>

lemma wcl_upper_of_wf:
  assumes "wf RPrel" shows "wcl_upper"
proof -
  have "\<forall>p. p \<in> Wellfounded.acc RPrel" using assms wfs_wf_iff_all_acc by blast
  then show ?thesis unfolding wcl_upper_def by blast
qed

theorem wcl_upper_iff_wf: "wcl_upper \<longleftrightarrow> wf RPrel"
  using wcl_wf_of_upper wcl_upper_of_wf by blast

corollary wcl_collapse_of_upper:
  assumes "wcl_upper" shows "wds_collapse"
  by (rule wds_collapse_of_wf[OF wcl_wf_of_upper[OF assms]])

corollary wcl_buc1_2_2_of_upper:
  \<comment> \<open>[Buc1] Lemma 2.2 in original shape, modulo the single \<open>wcl_upper\<close> residual.\<close>
  assumes "wcl_upper"
  shows "wf {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}"
  using wds_buc1_2_2_of_collapse[OF wcl_collapse_of_upper[OF assms]] .

text \<open>\<^bold>\<open>Status after r64.\<close>  The last external citation [Buc1] Lemma 2.2 is now
  pinned to the SINGLE sharpest residual \<open>wcl_upper\<close> (\<open>wcl_upper_iff_wf\<close>: exactly
  theorem-strength).  Compared with r63's \<open>wds_collapse\<close>, the entire head-\<open>\<le> n\<close>
  segment of the minimal-bad body is discharged unconditionally by the
  lexicographic \<open>(head, size)\<close> minimality (\<open>wcl_min_bad_lex\<close>):

  \<^item> head-\<open>< n\<close> components: accessible by head-minimality (clause (i));
  \<^item> head-\<open>= n\<close> components: accessible by size-minimality within the level,
    since they are proper subterms of the body (clause (ii));
  \<^item> head-\<open>> n\<close> components (the \<open>\<psi>\<^bsub>n\<^esub>\<close>-shielded / collapsed coefficients): the
    SOLE remaining obligation \<open>wcl_upper\<close>.

  \<^bold>\<open>Exact obstruction.\<close>  \<open>wcl_upper\<close> asks that the head-\<open>> n\<close> body components of
  the minimal-bad principal be \<open>RPrel\<close>-accessible.  These are exactly Buchholz's
  collapsed coefficients \<open>\<psi>\<^bsub>w\<^esub>(\<dots>)\<close>, \<open>w > n\<close>, appearing under a \<open>\<psi>\<^bsub>n\<^esub>\<close>: their
  accessibility is NOT reachable by any subterm/size descent (they sit at a
  larger head) nor by head-minimality (their head is \<open>> n\<close>, not \<open>< n\<close>).  Closing
  them is the genuine transfinite content --- the [Buc1] distinguished-set /
  fundamental-sequence collapse (\<open>wds_distinguished\<close> + [Buc1] \<open>\<section>\<close>5, cf.
  \<open>wcl_accfrag_distinguished_of_core\<close>, which currently still assumes the collapse
  core).  Estimated 2--4 rounds if the distinguished-set tower induction on \<open>n\<close>
  can be made to feed \<open>wcl_upper\<close> level by level; genuinely external otherwise.\<close>


(* ===================================================================== *)
(* ===== r65: SETLE1_ltJ LEFT-END head bound (prefix ox7_) [front A] ==== *)
(* =====                                                              ==== *)
(* ===== r64 REFUTED the right-spine L1/L2 route: the restricted      ==== *)
(* ===== spineH of ox6_setle_scbext_restr is governed by the FIRST-   ==== *)
(* ===== principal (LEFT-end) head bpHeadV(body), NOT the right spine. ==== *)
(* ===== python census (537 REAL ST_PS-cap-PT_PS hosts, ST_PS oracle): ==== *)
(* =====   * bpHeadV(body) >= v1  holds on ALL 537 (0 failures);       ==== *)
(* =====   * s0 is NEVER empty  => bpHeadV(X1) = bpHeadV(body);         ==== *)
(* =====   * the exact universal spineH (leBT t' X1 for every          ==== *)
(* =====     tx' in GBT u X1 with matched hole + size bound) holds on   ==== *)
(* =====     ALL 537 (0 failures) for u in {0,1};                      ==== *)
(* =====   * the 2 ambiguous hosts M=(0,0)(1,0)(1,1)(2,1)(1,1)(2,1)     ==== *)
(* =====     and its (2,2) variant are NON-real (is_standard = False). ==== *)
(* ===== So the LEFT-end bound closes spineH.  (python:                ==== *)
(* =====   python/_r65_lefthead_step0.py)                             ==== *)
(* =====                                                              ==== *)
(* ===== KEY PROOF IDEA for the LEFT-end bound (r64 said RightNodes    ==== *)
(* ===== ALONE cannot bound bpHeadV; RightNodes + OT descP CAN):       ==== *)
(* =====   body in OT_B  =>  its principal list descP-descending, so    ==== *)
(* =====   head(first principal) >= head(last principal); and          ==== *)
(* =====   head(last principal) = RightNodes(body)!0 (lpx_bpHeadV_PB_  ==== *)
(* =====   last), which is >= v1 by the r63 RightNodes bound.  Hence    ==== *)
(* =====   bpHeadV(body) = head(first) >= head(last) >= v1.            ==== *)
(* ===================================================================== *)

subsection \<open>\<open>ox7_slice_TransOT\<close>: the census slice \<open>Trans (s84x_N M)\<close> is in \<open>OT\<^bsub>B\<^esub>\<close>\<close>

text \<open>@{text ox7_slice_TransOT}: the OT-ness of the RAW census slice's \<open>Trans\<close>
  value.  This is the non-\<open>Pred\<close> mirror of the STEP-3 core of
  @{thm [source] ot1_A0OT}: route through the reduction \<open>RN = Red (s84x_N M)\<close>
  (which shares \<open>Trans\<close>), read \<open>Trans RN = D\<^bsub>e\<^sub>3\<^esub> body\<close> off
  @{thm [source] e2x_Trans_principal_head}, and use OT-heredity
  @{thm [source] m_8_7_OT_scb_recursive} on the census kind-1 scb-subterm
  \<open>D\<^bsub>e\<^sub>3\<^esub> body\<close> of \<open>Trans M\<close> (from the \<open>ihOT : Trans M \<in> OT\<^bsub>B\<^esub>\<close> premise, the same
  hypothesis the census \<open>SETLE1\<close> slot supplies).\<close>

lemma ox7_slice_TransOT:
  fixes N :: pairseq
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ihOT: "Trans N \<in> OT_B"
    and ltJ: "s84x_jm3 N < transJm1 N"
  shows "Trans (s84x_N N) \<in> OT_B"
proof -
  let ?e3 = "entry N 1 (s84x_jm3 N)"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  let ?S = "seg N (s84x_jm3 N) (Lng N - 1)"
  let ?RN = "Red ?S"
  have MR: "N \<in> RT_PS" using NST m_6_7_ST_PS_subseteq_RT_PS by blast
  have MT: "N \<in> T_PS" using MR by (simp add: RT_PS_def)
  have jm2lt: "s84x_jm2 N < Lng N - 1" by (rule s84c1_jm2_basic(1)[OF hp])
  have jm3le: "s84x_jm3 N \<le> s84x_jm2 N" using adm_Adm_le by (simp add: s84x_jm3_def)
  have jm3lt: "s84x_jm3 N < Lng N - 1" using jm3le jm2lt by linarith
  have mM3: "(N, s84x_jm3 N) \<in> Marked" using s84d_jm3_Marked(1)[OF MR MT hp] by simp
  have leR3: "leR N 0 (s84x_jm3 N) (Lng N - 1)" using mM3 by (simp add: Marked_def)
  have LNlen: "Lng ?S = Suc (Lng N - 1) - s84x_jm3 N"
    by (simp add: seg_def del: upt_Suc)
  have LN0: "(0::nat) < Lng ?S" using LNlen jm3lt by linarith
  have segT: "?S \<in> T_PS"
    using slice_Red_in_RT_PS[OF MR jm3lt order.refl leR3] by simp
  have RN_RT: "?RN \<in> RT_PS"
    using slice_Red_in_RT_PS[OF MR jm3lt order.refl leR3] by simp
  have RN_mono: "monoT ?RN"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR jm3lt order.refl leR3] by simp
  have TeqR: "Trans ?S = Trans ?RN"
    by (rule Trans_slice_eq_Red[OF MR jm3lt order.refl leR3])
  obtain s0 b0 s1 b1 where
    k1: "scb_kind1 (Trans N) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  have scbd: "scb_decomp (Trans N) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    using k1 by (simp add: scb_kind1_def)
  have TReq: "Trans ?RN = Dpt (enat (entry ?RN 1 0)) (bpHeadT (Trans ?RN))"
    by (rule e2x_Trans_principal_head[OF RN_RT RN_mono])
  have e_RN: "entry ?RN 1 0 = ?e3"
  proof -
    have "entry ?RN 1 0 = entry ?S 1 0" by (rule m_6_6_Red_leftend_1[OF segT])
    also have "\<dots> = ?e3" using entry_seg[OF LN0, of 1] by simp
    finally show ?thesis .
  qed
  have bodyR: "bpHeadT (Trans ?RN) = ?body"
  proof -
    have "bpHeadT (Trans ?RN) = bpHeadT (Trans ?S)" using TeqR by simp
    also have "\<dots> = ?body" by (simp add: s84x_N_def)
    finally show ?thesis .
  qed
  have TR_princ: "Trans ?RN = Dpt (enat ?e3) ?body"
    using TReq e_RN bodyR by simp
  have RN_TB: "Trans ?RN \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF RN_RT])
  have DptTB: "Dpt (enat ?e3) ?body \<in> T_B" using RN_TB TR_princ by simp
  have DptOT: "Dpt (enat ?e3) ?body \<in> OT"
    by (rule m_8_7_OT_scb_recursive[OF ihOT DptTB scbd])
  have RN_TransOT: "Trans ?RN \<in> OT_B"
    using DptOT TR_princ RN_TB by (simp add: OT_B_def)
  have "Trans (s84x_N N) = Trans ?S" by (simp add: s84x_N_def)
  also have "\<dots> = Trans ?RN" using TeqR by simp
  finally show "Trans (s84x_N N) \<in> OT_B" using RN_TransOT by simp
qed


subsection \<open>\<open>ox7_bpHeadV_body_ge_v1\<close>: the LEFT-end (first-principal) head of the
  terminal mono slice body is \<open>\<ge> v\<^sub>1\<close>\<close>

text \<open>@{text ox7_bpHeadV_body_ge_v1}: the LEFT-end mirror of
  @{thm [source] ox7_RightNodes_body_ge_v1}, and the TRUE residual that r64's
  census identified as governing the restricted \<open>spineH\<close>.  \<open>body \<in> OT\<^bsub>B\<^esub>\<close>
  (@{thm [source] ox7_slice_TransOT} + @{thm [source] otx_bpHeadT_OT}) makes
  \<open>body\<close>'s principal list \<open>descP\<close>-descending
  (@{thm [source] b1x_descP_last_hd}), so the FIRST-principal head
  \<open>bpHeadV body\<close> dominates the LAST-principal head
  \<open>= RightNodes body ! 0\<close> (@{thm [source] lpx_bpHeadV_PB_last}); the latter is
  \<open>\<ge> v\<^sub>1\<close> by the r63 spine bound.  Thus \<open>bpHeadV body \<ge> v\<^sub>1\<close> --- a fact that,
  as r64 stressed, RightNodes ALONE cannot give, but RightNodes + the OT
  descending-principal order does.\<close>

lemma ox7_bpHeadV_body_ge_v1:
  fixes M :: pairseq
  assumes NST: "M \<in> ST_PS" and NPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
    and ihOT: "Trans M \<in> OT_B"
    and ltJ: "s84x_jm3 M < transJm1 M"
  shows "enat (entry M 1 (Lng M - 1))
           \<le> bpHeadV (bpHeadT (Trans (s84x_N M)))"
proof -
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  \<comment> \<open>the body \<open>OT\<^bsub>B\<^esub>\<close> and \<open>T\<^bsub>B\<^esub>\<close> facts\<close>
  have sliceOT: "Trans (s84x_N M) \<in> OT_B"
    by (rule ox7_slice_TransOT[OF NST NPT hp j1gt branch ihOT ltJ])
  have bodyOT: "isOT_BT ?body" by (rule otx_bpHeadT_OT[OF sliceOT])
  have bodyTB: "?body \<in> T_B" by (rule oi5_regime(3)[OF NST NPT hp j1gt branch])
  \<comment> \<open>the pkg scb-decomposition of \<open>body\<close> (its flat ends in the hole \<open>D\<^bsub>v\<^sub>1\<^esub> 0\<close>)\<close>
  obtain s0 b0 s1 b1 where
    b0RP: "\<forall>x \<in> set b0. x = RP"
    and inner: "scb_decomp ?body s0 (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  have fbody: "flatBT ?body = s0 @ Dsym (enat ?v1) # Zsym # b0"
    using inner by (simp add: scb_decomp_def)
  have bodyne: "?body \<noteq> 0\<^sub>B"
  proof
    assume z: "?body = 0\<^sub>B"
    have "flatBT ?body = [Zsym]" using z by simp
    with fbody show False by (cases s0) auto
  qed
  \<comment> \<open>\<open>RightNodes body\<close> ends in \<open>v\<^sub>1\<close> (r63 shape), so its \<open>0\<close>-th entry is \<open>\<ge> v\<^sub>1\<close>\<close>
  obtain a0 where RNbody: "RightNodes ?body = a0 @ [?v1]"
    using rnsub_RightNodes_t0_lastv[OF fbody b0RP bodyTB] by blast
  have RNlen: "0 < length (RightNodes ?body)" using RNbody by simp
  have RN0mem: "RightNodes ?body ! 0 \<in> set (RightNodes ?body)"
    using RNlen by (rule nth_mem)
  have RNge: "\<forall>x \<in> set (RightNodes ?body). ?v1 \<le> x"
    by (rule ox7_RightNodes_body_ge_v1[OF NST NPT hp j1gt branch ltJ])
  have v1_le_RN0: "?v1 \<le> RightNodes ?body ! 0" using RNge RN0mem by blast
  \<comment> \<open>\<open>body = Trm ps\<close> is a nonzero \<open>descP\<close>-descending principal list\<close>
  obtain ps where bps: "?body = Trm ps" by (cases ?body)
  have psne: "ps \<noteq> []" using bodyne bps by auto
  have descPps: "descP ps" using bodyOT bps by simp
  have lasthd: "leBT (Trm [last ps]) (Trm [hd ps])"
    by (rule b1x_descP_last_hd[OF descPps psne])
  \<comment> \<open>LAST-principal head \<open>= enat (RightNodes body ! 0)\<close>\<close>
  have dfbody: "dfree_BT ?body" using bodyTB by (simp add: T_B_def)
  have lenPB: "Lng (PB ?body) = length ps" using bps by (simp add: rnsub_Lng_PB)
  have idxlt: "length ps - 1 < length ps" using psne by (cases ps) auto
  have PBlast: "PB ?body ! (Lng (PB ?body) - 1) = Trm [last ps]"
  proof -
    have "PB ?body = map (\<lambda>p. Trm [p]) ps" using bps by (simp add: PB_def)
    hence "PB ?body ! (Lng (PB ?body) - 1) = Trm [ps ! (length ps - 1)]"
      using lenPB idxlt by (simp add: nth_map)
    also have "ps ! (length ps - 1) = last ps" using psne by (simp add: last_conv_nth)
    finally show ?thesis .
  qed
  have hlast: "bpHeadV (Trm [last ps]) = enat (RightNodes ?body ! 0)"
  proof -
    have "bpHeadV (PB ?body ! (Lng (PB ?body) - 1)) = enat (RightNodes ?body ! 0)"
      by (rule lpx_bpHeadV_PB_last[OF bodyne dfbody])
    thus ?thesis using PBlast by simp
  qed
  \<comment> \<open>FIRST-principal head \<open>= bpHeadV body\<close>, and it dominates the LAST head\<close>
  have hhd: "bpHeadV (Trm [hd ps]) = bpHeadV ?body"
  proof -
    obtain p rest where pr: "ps = p # rest" using psne by (cases ps) auto
    obtain u2 a2 where pv: "p = DB u2 a2" by (cases p)
    have "bpHeadV ?body = u2" using bps pr pv by simp
    moreover have "bpHeadV (Trm [hd ps]) = u2" using pr pv by simp
    ultimately show ?thesis by simp
  qed
  have headmono: "bpHeadV (Trm [last ps]) \<le> bpHeadV (Trm [hd ps])"
  proof -
    obtain u1 a1 where l1: "last ps = DB u1 a1" by (cases "last ps")
    obtain u2 a2 where l2: "hd ps = DB u2 a2" by (cases "hd ps")
    have le: "leBT (Trm [DB u1 a1]) (Trm [DB u2 a2])" using lasthd l1 l2 by simp
    have "u1 \<le> u2"
    proof (cases "Trm [DB u1 a1] = Trm [DB u2 a2]")
      case True thus ?thesis by simp
    next
      case False
      hence "lessBT (Trm [DB u1 a1]) (Trm [DB u2 a2])" using le by blast
      hence "lessBP (DB u1 a1) (DB u2 a2)" by simp
      hence "u1 < u2 \<or> (u1 = u2 \<and> lessBT a1 a2)" by simp
      thus ?thesis by (auto simp: order_le_less)
    qed
    thus ?thesis using l1 l2 by simp
  qed
  \<comment> \<open>chain: \<open>v\<^sub>1 \<le> RightNodes!0 = head(last) \<le> head(first) = bpHeadV body\<close>\<close>
  have "enat ?v1 \<le> enat (RightNodes ?body ! 0)" using v1_le_RN0 by simp
  also have "\<dots> = bpHeadV (Trm [last ps])" using hlast by simp
  also have "\<dots> \<le> bpHeadV (Trm [hd ps])" using headmono by simp
  also have "\<dots> = bpHeadV ?body" using hhd by simp
  finally show "enat ?v1 \<le> bpHeadV ?body" .
qed


subsection \<open>\<open>ox7_ub_lt_bpHeadV_body\<close>: the STRICT LEFT-end head separation
  \<open>ub < bpHeadV body\<close> (the head-side input of the first-difference at position 0)\<close>

text \<open>@{text ox7_ub_lt_bpHeadV_body}: the strict form
  \<open>enat (v\<^sub>1 - 1) < bpHeadV body\<close> --- the exact head-side fact a first-difference
  \<open>spineH\<close> assembly consumes at position 0 (the outer principal), since the
  ancestor's hole head is \<open>ub = v\<^sub>1 - 1\<close> while \<open>X\<^sub>1\<close>'s first-principal head is
  \<open>bpHeadV body\<close>.  It follows from @{thm [source] ox7_bpHeadV_body_ge_v1} and
  \<open>v\<^sub>1 > 0\<close> (a conjunct of both \<open>transCondIII\<close> / \<open>transCondIV\<close>).\<close>

lemma ox7_ub_lt_bpHeadV_body:
  fixes M :: pairseq
  assumes NST: "M \<in> ST_PS" and NPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
    and ihOT: "Trans M \<in> OT_B"
    and ltJ: "s84x_jm3 M < transJm1 M"
  shows "enat (entry M 1 (Lng M - 1) - 1)
           < bpHeadV (bpHeadT (Trans (s84x_N M)))"
proof -
  have v1pos: "0 < entry M 1 (Lng M - 1)"
    using branch by (auto simp: transCondIII_def transCondIV_def)
  have ge: "enat (entry M 1 (Lng M - 1))
              \<le> bpHeadV (bpHeadT (Trans (s84x_N M)))"
    by (rule ox7_bpHeadV_body_ge_v1[OF NST NPT hp j1gt branch ihOT ltJ])
  have "enat (entry M 1 (Lng M - 1) - 1) < enat (entry M 1 (Lng M - 1))"
    using v1pos by simp
  also note ge
  finally show ?thesis .
qed
(* ===================================================================== *)
(* ===== r65 (OPUS 4.8): the tower STEP and the intrinsic-globality   ===== *)
(* ===== obstruction of wcl_upper (prefixes wtw_ / wcl_).             ===== *)
(* =====                                                               ===== *)
(* ===== r64 pinned [Buc1] 2.2 to the single residual wcl_upper: for   ===== *)
(* ===== the lex-(head,size)-minimal bad principal D_n b, the head->n  ===== *)
(* ===== body components are RPrel-accessible.  This round makes the   ===== *)
(* ===== tower STEP explicit and unconditional (wtw_core_step: the     ===== *)
(* ===== level-u principal is accessible once head-<u principals AND   ===== *)
(* ===== the head->=u components are), and CERTIFIES why the residual  ===== *)
(* ===== cannot be discharged level-locally: for a bad witness, EVERY  ===== *)
(* ===== head->n component has the bad principal itself as a strict    ===== *)
(* ===== RPrel-predecessor (wcl_high_comp_bad_pred), so it is provably ===== *)
(* ===== NON-accessible (wcl_high_comp_not_acc) — the head->n content  ===== *)
(* ===== is exactly the shielded material with no elementary handle.   ===== *)
(* ===================================================================== *)

subsection \<open>(F) r65: the unconditional tower STEP and the globality of \<open>wcl_upper\<close>\<close>

text \<open>\<^bold>\<open>The tower step (positive, unconditional).\<close>  This is the clean level-\<open>u\<close>
  successor of the head recursion, isolating the low part (below the head,
  supplied by the induction hypothesis of any head-recursion) from the high
  part (the \<open>\<ge> u\<close> components, the residual).  It says: a level-\<open>u\<close> \<open>OT\<close>+\<open>dfree\<close>
  principal is \<open>RPrel\<close>-accessible as soon as (a) every strictly-lower-head
  \<open>OT\<close>+\<open>dfree\<close> principal is accessible (the tower below), and (b) every direct
  body component of head \<open>\<ge> u\<close> is accessible (the shielded upper part).  The
  low components (head \<open>< u\<close>) are handled by (a), so the body is
  \<open>RTrel\<close>-accessible (\<open>wfj_tuple_acc\<close>) and the principal lifts by
  \<open>wfc_principal_acc_of_body\<close>.  This packages exactly the split that
  \<open>wcl_wf_of_upper\<close> performs inline, as a reusable named brick for the tower.\<close>

lemma wtw_core_step:
  assumes hlt: "\<And>r. isOT_BP r \<Longrightarrow> dfree_BP r \<Longrightarrow> wfj_hd r < enat u
                    \<Longrightarrow> r \<in> Wellfounded.acc RPrel"
    and hge: "\<And>w c. DB w c \<in> set (untrm b) \<Longrightarrow> enat u \<le> w
                     \<Longrightarrow> DB w c \<in> Wellfounded.acc RPrel"
    and ot: "isOT_BP (DB (enat u) b)" and df: "dfree_BP (DB (enat u) b)"
  shows "DB (enat u) b \<in> Wellfounded.acc RPrel"
proof -
  have otb: "isOT_BT b" using ot by simp
  have dfb: "dfree_BT b" using df by simp
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  have allc: "\<forall>r \<in> set (untrm b). r \<in> Wellfounded.acc RPrel"
  proof
    fix r assume rin: "r \<in> set (untrm b)"
    have rin': "r \<in> set bs" using rin beq by simp
    have otr: "isOT_BP r" using otb beq rin' by simp
    have dfr: "dfree_BP r" using dfb beq rin' by simp
    obtain w c where req: "r = DB w c" by (cases r) auto
    show "r \<in> Wellfounded.acc RPrel"
    proof (cases "w < enat u")
      case True
      have "wfj_hd r < enat u" using req True by simp
      then show ?thesis using hlt otr dfr by blast
    next
      case False
      have geu: "enat u \<le> w" using False by (simp add: not_less)
      have "DB w c \<in> set (untrm b)" using rin req by simp
      then have "DB w c \<in> Wellfounded.acc RPrel" using hge geu by blast
      then show ?thesis using req by simp
    qed
  qed
  have bacc: "b \<in> Wellfounded.acc RTrel" by (rule wfj_tuple_acc[OF otb dfb allc])
  show ?thesis by (rule wfc_principal_acc_of_body[OF hlt bacc ot df])
qed

text \<open>\<^bold>\<open>The intrinsic-globality obstruction.\<close>  The head-\<open>> n\<close> components of the
  lex-minimal bad principal \<open>D\<^bsub>n\<^esub> b\<close> are NOT merely "hard to reach": for a
  \<open>bad\<close> (non-accessible) witness they are provably NON-accessible.  The reason is
  structural: \<open>D\<^bsub>n\<^esub> b\<close> is itself a strict \<open>RPrel\<close>-predecessor of every body
  component of head \<open>w > n\<close> (head \<open>n < w\<close> forces \<open>lessBP (D\<^bsub>n\<^esub> b) (D\<^bsub>w\<^esub> c)\<close>
  irrespective of the bodies).  Since accessibility is downward closed
  (\<open>acc_downward\<close>), a component with a non-accessible predecessor is itself
  non-accessible.  Hence \<open>wcl_upper\<close>'s conclusion "the head-\<open>> n\<close> components are
  accessible" is FALSE on any genuine bad witness carrying such a component:
  \<open>wcl_upper\<close> can only hold vacuously, i.e. it is equivalent to \<open>wf RPrel\<close> with
  no proper sub-instance — there is no monotone "partial" progress to be made on
  the residual itself.  Establishing accessibility of those components therefore
  requires first ruling out the bad witness globally, which is the whole theorem
  (\<open>wcl_upper_iff_wf\<close>).  This is the exact certificate that the distinguished-set
  impredicative construction (\<open>wds_collapse\<close>, existence of a distinguished set =
  theorem strength) is unavoidable, and that no head-\<open>< n\<close> / size descent closes
  the head-\<open>> n\<close> level.\<close>

lemma wcl_high_comp_bad_pred:
  assumes ot: "isOT_BP (DB (enat n) b)" and df: "dfree_BP (DB (enat n) b)"
    and comp: "DB w c \<in> set (untrm b)" and hn: "enat n < w"
  shows "(DB (enat n) b, DB w c) \<in> RPrel"
proof -
  have otb: "isOT_BT b" using ot by simp
  have dfb: "dfree_BT b" using df by simp
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  have cin: "DB w c \<in> set bs" using comp beq by simp
  have "\<forall>p \<in> set bs. isOT_BP p" using otb beq by simp
  then have otc: "isOT_BP (DB w c)" using cin by blast
  have "\<forall>p \<in> set bs. dfree_BP p" using dfb beq by simp
  then have dfc: "dfree_BP (DB w c)" using cin by blast
  have "lessBP (DB (enat n) b) (DB w c)" using hn by simp
  then show ?thesis using ot df otc dfc by (simp add: RPrel_def)
qed

corollary wcl_high_comp_not_acc:
  assumes ot: "isOT_BP (DB (enat n) b)" and df: "dfree_BP (DB (enat n) b)"
    and comp: "DB w c \<in> set (untrm b)" and hn: "enat n < w"
    and nacc: "DB (enat n) b \<notin> Wellfounded.acc RPrel"
  shows "DB w c \<notin> Wellfounded.acc RPrel"
proof
  assume acc: "DB w c \<in> Wellfounded.acc RPrel"
  have "DB (enat n) b \<in> Wellfounded.acc RPrel"
    by (rule acc_downward[OF acc wcl_high_comp_bad_pred[OF ot df comp hn]])
  then show False using nacc by blast
qed

text \<open>\<^bold>\<open>Consequently\<close>: on the lex-minimal bad witness \<open>D\<^bsub>n\<^esub> b\<close> (from
  \<open>wcl_min_bad_lex\<close>), the \<open>ONLY\<close> way \<open>wcl_upper\<close> can fail to be immediately
  self-contradictory is that \<open>b\<close> carries \<open>NO\<close> head-\<open>> n\<close> component at all --- in
  which case \<open>wcl_wf_of_upper\<close> already closes via clauses (i)/(ii) with no upper
  content.  If a head-\<open>> n\<close> component exists, \<open>wcl_high_comp_not_acc\<close> shows it is
  non-accessible, so \<open>wcl_upper\<close>'s demand is unmeetable without first refuting the
  witness.  This gives the sharpened obstruction and a strictly-shorter route
  through \<open>wcl_wf_of_upper\<close>: under the residual, either there is no upper content
  (finish by (i)/(ii)) or the residual is self-defeating on the witness.\<close>

lemma wcl_wf_of_upper_via_step:
  \<comment> \<open>Re-derivation of \<open>wf RPrel\<close> from \<open>wcl_upper\<close> through the named tower step
      \<open>wtw_core_step\<close>, making the low/upper split explicit.\<close>
  assumes U: "wcl_upper"
  shows "wf RPrel"
proof (rule ccontr)
  assume nwf: "\<not> wf RPrel"
  have bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  proof
    assume A: "\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel"
    have "\<forall>p. p \<in> Wellfounded.acc RPrel"
    proof
      fix p :: BP
      show "p \<in> Wellfounded.acc RPrel"
      proof (cases "isOT_BP p \<and> dfree_BP p")
        case True thus ?thesis using A by blast
      next
        case False
        show ?thesis
        proof (rule accI)
          fix q assume "(q, p) \<in> RPrel"
          then have "isOT_BP p \<and> dfree_BP p" by (auto simp add: RPrel_def)
          with False show "q \<in> Wellfounded.acc RPrel" by blast
        qed
      qed
    qed
    then have "wf RPrel" using wfs_wf_iff_all_acc by blast
    with nwf show False by blast
  qed
  obtain n b where otp: "isOT_BP (DB (enat n) b)"
    and dfp: "dfree_BP (DB (enat n) b)"
    and nacc: "DB (enat n) b \<notin> Wellfounded.acc RPrel"
    and i: "\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
                 \<longrightarrow> r \<in> Wellfounded.acc RPrel"
    and ii: "\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
                  \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
                  \<longrightarrow> c \<in> Wellfounded.acc RPrel"
    using wcl_min_bad_lex[OF bad] by blast
  have otb: "isOT_BT b" using otp by simp
  have dfb: "dfree_BT b" using dfp by simp
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  \<comment> \<open>the residual supplies the head-\<open>> n\<close> (\<open>= \<ge> Suc n\<close>) components\<close>
  have upper: "\<forall>w c. DB w c \<in> set (untrm b) \<longrightarrow> enat n < w
                     \<longrightarrow> DB w c \<in> Wellfounded.acc RPrel"
    using U[unfolded wcl_upper_def] otp dfp nacc i ii by blast
  have hlt: "\<And>r. isOT_BP r \<Longrightarrow> dfree_BP r \<Longrightarrow> wfj_hd r < enat n
                 \<Longrightarrow> r \<in> Wellfounded.acc RPrel"
    using i by blast
  \<comment> \<open>the head-\<open>\<ge> n\<close> components: head \<open>= n\<close> by (ii) (proper subterms), head \<open>> n\<close> by the residual\<close>
  have hge: "\<And>w c. DB w c \<in> set (untrm b) \<Longrightarrow> enat n \<le> w
                    \<Longrightarrow> DB w c \<in> Wellfounded.acc RPrel"
  proof -
    fix w c assume rmem: "DB w c \<in> set (untrm b)" and geu: "enat n \<le> w"
    have rin': "DB w c \<in> set bs" using rmem beq by simp
    have "\<forall>p \<in> set bs. isOT_BP p" using otb beq by simp
    then have otr: "isOT_BP (DB w c)" using rin' by blast
    have "\<forall>p \<in> set bs. dfree_BP p" using dfb beq by simp
    then have dfr: "dfree_BP (DB w c)" using rin' by blast
    show "DB w c \<in> Wellfounded.acc RPrel"
    proof (cases "w = enat n")
      case True
      have hd_r: "wfj_hd (DB w c) = enat n" using True by simp
      have "wfs_szP (DB w c) < wfs_szT (Trm bs)"
        using wfs_szP_mem_lt[OF rin'] .
      then have "wfs_szP (DB w c) < wfs_szT b" using beq by simp
      then have szr: "wfs_szP (DB w c) < wfs_szP (DB (enat n) b)" by simp
      show ?thesis using ii otr dfr hd_r szr by blast
    next
      case False
      have "enat n < w" using geu False by simp
      then show ?thesis using upper rmem by blast
    qed
  qed
  have "DB (enat n) b \<in> Wellfounded.acc RPrel"
    by (rule wtw_core_step[OF hlt hge otp dfp])
  then show False using nacc by blast
qed

text \<open>\<^bold>\<open>Status after r65.\<close>  The residual for [Buc1] Lemma 2.2 is unchanged
  (\<open>wcl_upper\<close>, \<open>wcl_upper_iff_wf\<close>: exactly theorem-strength).  What r65 adds is
  the precise \<^emph>\<open>shape\<close> of the obstruction, as green bricks:

  \<^item> \<open>wtw_core_step\<close> — the unconditional level-\<open>u\<close> tower step (low part = the
    head-\<open>< u\<close> IH, upper part = the head-\<open>\<ge> u\<close> components), and
    \<open>wcl_wf_of_upper_via_step\<close> re-derives \<open>wf RPrel\<close> from \<open>wcl_upper\<close> through it,
    exposing the low/upper split as a reusable named brick for a future tower.
  \<^item> \<open>wcl_high_comp_bad_pred\<close> / \<open>wcl_high_comp_not_acc\<close> — the head-\<open>> n\<close>
    components of a bad witness are provably NON-accessible (the bad principal is
    their \<open>RPrel\<close>-predecessor).  So \<open>wcl_upper\<close> admits no monotone partial
    progress: its conclusion is false on any genuine witness with upper content;
    it can hold only vacuously.

  \<^bold>\<open>Exact obstruction / next idea.\<close>  The head-\<open>> n\<close> level cannot be discharged by
  any subterm/size descent (its members are lex-\<open>larger\<close>, and non-accessible
  while the witness is bad) nor by the head recursion (head-\<open>< n\<close> has no base:
  \<open>wfj_frag0_lv_unbounded\<close>).  The sole path is the impredicative
  distinguished-set collapse \<open>wds_collapse\<close> (equivalently \<open>wcl_upper\<close>): its
  exhibit-move must construct a \<open>v\<close>-distinguished set on top of \<open>wds_Mset v\<close>
  containing the target \<open>D\<^bsub>v\<^esub> c\<close>, whose only non-cheap clauses are (i) the
  \<open>RPrel\<close>-downward closure of the initial segment \<open>{q \<in> wfj_frag v. q \<le>\<^sub>P D\<^bsub>v\<^esub> c}\<close>
  (a transfinite induction along the wellfounded \<open>acc RPrel\<close>-restriction to
  \<open>wds_Mset v\<close>, using the premise that \<open>c\<close>'s \<open>G\<^sub>v\<close>-trace coefficients already sit in
  the tower), and (ii) its \<open>G\<close>-progressiveness.  The load-bearing missing fact is
  the \<^emph>\<open>existence of one \<open>v\<close>-distinguished set\<close> (the D1 witness for
  \<open>wds_Mset_distinguished\<close>) — itself of theorem strength (\<open>wfj_frag0_lv_unbounded\<close>
  forces it to contain a hereditarily-\<open>G\<close>-low unbounded-level family).  This is
  the genuine [Buc1] \<open>\<section>\<close>5 fundamental-sequence content and remains external-grade:
  a full formalization of the exhibit-move transfinite induction is estimated at
  \<open>\<ge> 5\<close> dedicated rounds (or importing an external well-foundedness of the
  Buchholz \<open>\<psi>\<close>-collapse).\<close>


(* ===================================================================== *)
(* ===== r66 (OPUS 4.8): SETLE1_ltJ position-0 first-difference close === *)
(* =====                                                               === *)
(* ===== r65 localized the census SETLE1_ltJ residual (via             === *)
(* ===== ox6_SETLE1_reduce_restr) to a spineH: leBT t' X1 for every    === *)
(* ===== matched-hole right-spine ancestor body t' of A1, with matched === *)
(* ===== tx' in GBT u X1 sharing the hole (sc,bc).  The r65 next-idea   === *)
(* ===== closes spineH at position 0: t' and X1 differ at the FIRST     === *)
(* ===== principal head, and bpHeadV(t') < bpHeadV(X1) DECIDES          === *)
(* ===== lessBT t' X1 outright (dictionary order, [Buc1] (<1)-(<3)).    === *)
(* ===== This front supplies the two reusable position-0 bricks         === *)
(* ===== (ox7_headlt_lessBT, ox7_bpHeadV_share) and threads the census  === *)
(* ===== SETLE1_ltJ slot down to the SINGLE clean strict-head residual  === *)
(* ===== HEAD: bpHeadV(t') < bpHeadV(X1) (ot7_SETLE1_ltJ_of_head,        === *)
(* ===== oi8_census_SETLE_of_head).  The remaining truth of HEAD is the  === *)
(* ===== census right-spine-terminal geometry (bpHeadV(t')=ub), a deep   === *)
(* ===== Trans-image fact recorded in the status text at the end.        === *)
(* ===================================================================== *)

subsection \<open>\<open>ox7_headlt_lessBT\<close>: the position-0 first-difference --- a strictly
  smaller leftmost principal head decides \<open>lessBT\<close>\<close>

text \<open>@{text ox7_headlt_lessBT}: the dictionary order @{const lessBT}
  (@{thm [source] lessBT.simps}) is decided at the FIRST principal: if the
  leftmost principal head of \<open>t\<close> is strictly below that of \<open>t'\<close>
  (\<open>bpHeadV t < bpHeadV t'\<close>) and both are nonzero, then \<open>lessBT t t'\<close>.  This is
  the exact position-0 head-side step the census \<open>spineH\<close> assembly consumes: it
  turns a strict outer-head separation into the whole-tree order, no matter what
  the deeper bodies are (unlike the shared-hole congruence
  @{thm [source] ox7_scbext_leBT_hole}, which needs the hole bodies ordered).\<close>

lemma ox7_headlt_lessBT:
  fixes t t' :: BT
  assumes lt: "bpHeadV t < bpHeadV t'" and tne: "t \<noteq> 0\<^sub>B" and t'ne: "t' \<noteq> 0\<^sub>B"
  shows "lessBT t t'"
proof -
  obtain ps where tp: "t = Trm ps" by (cases t)
  obtain qs where t'p: "t' = Trm qs" by (cases t')
  have psne: "ps \<noteq> []" using tne tp by auto
  have qsne: "qs \<noteq> []" using t'ne t'p by auto
  obtain p ps' where p: "ps = p # ps'" using psne by (cases ps) auto
  obtain q qs' where q: "qs = q # qs'" using qsne by (cases qs) auto
  obtain u1 a1 where pu: "p = DB u1 a1" by (cases p)
  obtain u2 a2 where qu: "q = DB u2 a2" by (cases q)
  have hu1: "bpHeadV t = u1" using tp p pu by simp
  have hu2: "bpHeadV t' = u2" using t'p q qu by simp
  have "u1 < u2" using lt hu1 hu2 by simp
  hence "lessBP (DB u1 a1) (DB u2 a2)" by simp
  hence "lessBT (Trm (DB u1 a1 # ps')) (Trm (DB u2 a2 # qs'))" by simp
  thus ?thesis using tp t'p p q pu qu by simp
qed


subsection \<open>\<open>ox7_bpHeadV_share\<close>: two trees whose flats share a prefix up to and
  including their first \<open>D\<close>-symbol have equal \<open>bpHeadV\<close>\<close>

text \<open>@{text ox7_bpHeadV_share}: if \<open>flat t\<close> and \<open>flat t'\<close> agree on a prefix
  \<open>sc\<close> and then both continue with the SAME letter \<open>D\<^sub>w\<close>, they have equal leftmost
  principal head.  Consequence of @{thm [source] bpHeadV_find_Dsym} (the first
  \<open>D\<close>-letter of a flat string carries \<open>bpHeadV\<close>) and
  @{thm [source] find_append_local}: the first \<open>D\<close>-letter of \<open>sc \<frown> D\<^sub>w \<frown> r\<close>
  lies in \<open>sc \<frown> [D\<^sub>w]\<close>, hence is independent of the tail \<open>r\<close>.  In the census
  \<open>spineH\<close> this is applied to the matched ancestor bodies \<open>t' = lbA\<close>,
  \<open>tx' = lbX\<close> (shared \<open>sc\<close>, hole head \<open>ub\<close>): they have the SAME outer head.\<close>

lemma ox7_bpHeadV_share:
  fixes t t' :: BT and sc r1 r2 :: "Sym list" and w :: enat
  assumes fa: "flatBT t  = sc @ Dsym w # r1"
    and fb: "flatBT t' = sc @ Dsym w # r2"
  shows "bpHeadV t = bpHeadV t'"
proof -
  let ?P = "\<lambda>x. \<exists>v. x = Dsym v"
  have tne: "t \<noteq> 0\<^sub>B"
  proof
    assume "t = 0\<^sub>B"
    hence "flatBT t = [Zsym]" by simp
    with fa show False by (cases sc) auto
  qed
  have t'ne: "t' \<noteq> 0\<^sub>B"
  proof
    assume "t' = 0\<^sub>B"
    hence "flatBT t' = [Zsym]" by simp
    with fb show False by (cases sc) auto
  qed
  have Pw: "?P (Dsym w)" by blast
  have shared: "find ?P (sc @ Dsym w # r1) = find ?P (sc @ Dsym w # r2)"
    by (simp add: find_append_local) (cases "find ?P sc"; simp add: Pw)
  have "Some (Dsym (bpHeadV t)) = Some (Dsym (bpHeadV t'))"
    using bpHeadV_find_Dsym[OF tne] bpHeadV_find_Dsym[OF t'ne] fa fb shared by simp
  thus ?thesis by simp
qed


subsection \<open>\<open>ot7_SETLE1_ltJ_of_head\<close>: the census SETLE1 slot from the SINGLE
  strict-head residual \<open>HEAD\<close>\<close>

text \<open>@{text ot7_SETLE1_ltJ_of_head}: the census \<open>SETLE1_ltJ\<close> slot (verbatim the
  \<open>SETLE1\<close> assumption of @{thm [source] oi8_census_final_ivadmeq}) is discharged
  from the SINGLE clean residual \<open>HEAD\<close>: every matched-hole right-spine ancestor
  body \<open>t'\<close> of \<open>A\<^sub>1\<close> has strictly smaller leftmost principal head than \<open>X\<^sub>1\<close>.
  From \<open>HEAD\<close> the engine input \<open>spineH\<close> (@{thm [source] ox6_SETLE1_reduce_restr})
  follows position-0 by @{thm [source] ox7_headlt_lessBT}; the tree-nonzero side
  conditions are read off the flats (\<open>t'\<close> has the hole letter \<open>D\<^bsub>ub\<^esub>\<close>; \<open>X\<^sub>1\<close>'s
  flat is the pkg surgery string).  This collapses ALL of the setle / \<open>G\<^sub>B\<close> /
  right-spine engine scaffolding to the one strict-head fact \<open>HEAD\<close>.\<close>

lemma ot7_SETLE1_ltJ_of_head:
  fixes N :: pairseq and s0 b0 :: "Sym list" and u :: enat
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                 (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and HEAD: "\<forall>t' tx' sc bc.
          flatBT t' = sc @ flatBP (DB (enat (entry N 1 (Lng N - 1) - 1))
                                      (bpHeadT (Trans (Pred (s84x_N N))))) @ bc
          \<longrightarrow> flatBT tx' = sc @ flatBP (DB (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B) @ bc
          \<longrightarrow> (\<forall>x\<in>set bc. x = RP)
          \<longrightarrow> tx' \<in> GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                            0\<^sub>B)
          \<longrightarrow> size t' < size (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                                (bpHeadT (Trans (Pred (s84x_N N)))))
          \<longrightarrow> bpHeadV t' < bpHeadV (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                                     0\<^sub>B)"
  shows "b1x_setle
           (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                     (bpHeadT (Trans (Pred (s84x_N N))))))
           (insert (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                      0\<^sub>B)
                   (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                             0\<^sub>B)))"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X0 = "(0\<^sub>B :: BT)"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  let ?X1 = "d4vx_ins s0 ?ub b0 ?X0"
  let ?A1 = "d4vx_ins s0 ?ub b0 ?A0"
  \<comment> \<open>the pkg wrapper facts (pin \<open>(s\<^sub>0,b\<^sub>0)\<close>, get \<open>b\<^sub>0\<close> all-\<open>RP\<close> and the flat of \<open>X\<^sub>1\<close>)\<close>
  obtain s0' b0' s1 b1 where
      b0RP': "\<forall>x \<in> set b0'. x = RP"
    and inner': "scb_decomp ?body s0' (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0'"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "flatBT ?body = s0 @ flatBT (Dpt (enat ?v1) 0\<^sub>B) @ b0"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0 @ [Dsym (enat ?v1), Zsym] @ b0" using z by simp
    thus False by (cases s0) auto
  qed
  have pin: "s0 = s0' \<and> b0 = b0'"
    by (rule m_7_2_scb_unique_sb[OF inner inner' bodyne])
  have b0RP: "\<forall>x \<in> set b0. x = RP" using b0RP' pin by simp
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have fX1: "flatBT ?X1 = s0 @ Dsym (enat ?ub) # flatBT ?X0 @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ?ub ?X0] by simp
  have X1ne: "?X1 \<noteq> 0\<^sub>B"
  proof
    assume "?X1 = 0\<^sub>B"
    hence "flatBT ?X1 = [Zsym]" by simp
    with fX1 show False by (cases s0) auto
  qed
  \<comment> \<open>the engine's \<open>spineH\<close>, closed at position 0 by the strict head separation\<close>
  have spineH: "\<forall>t' tx' sc bc.
        flatBT t' = sc @ flatBP (DB (enat ?ub) ?A0) @ bc
        \<longrightarrow> flatBT tx' = sc @ flatBP (DB (enat ?ub) ?X0) @ bc
        \<longrightarrow> (\<forall>x\<in>set bc. x = RP)
        \<longrightarrow> tx' \<in> GBT u ?X1
        \<longrightarrow> size t' < size ?A1
        \<longrightarrow> leBT t' ?X1"
  proof (intro allI impI)
    fix t' tx' sc bc
    assume fa: "flatBT t' = sc @ flatBP (DB (enat ?ub) ?A0) @ bc"
      and fb: "flatBT tx' = sc @ flatBP (DB (enat ?ub) ?X0) @ bc"
      and bcRP: "\<forall>x\<in>set bc. x = RP"
      and txin: "tx' \<in> GBT u ?X1"
      and szt: "size t' < size ?A1"
    have hlt: "bpHeadV t' < bpHeadV ?X1"
      using HEAD fa fb bcRP txin szt by blast
    have t'ne: "t' \<noteq> 0\<^sub>B"
    proof
      assume "t' = 0\<^sub>B"
      hence "flatBT t' = [Zsym]" by simp
      with fa show False by (cases sc) auto
    qed
    have "lessBT t' ?X1" by (rule ox7_headlt_lessBT[OF hlt t'ne X1ne])
    thus "leBT t' ?X1" by blast
  qed
  show ?thesis
    by (rule ox6_SETLE1_reduce_restr[OF NST NPT hp j1gt branch ltJ inner spineH])
qed

(* ===================================================================== *)
(* ===== r66 (OPUS 4.8) — buc1 MAJOR REFRAME: transcribe Buchholz's   ===== *)
(* ===== OWN proof of wf ([1] \<section>2, Lemmas 2.4--2.8), a FORWARD          ===== *)
(* ===== structural induction on TERM LENGTH (NOT the dead r65         ===== *)
(* ===== head-level / minimal-bad tower).  Prefix  bwo_  (Buchholz     ===== *)
(* ===== well-ordering).                                                ===== *)
(* ===================================================================== *)

section \<open>r66 bwo — Buchholz's own proof of \<open>wf RPrel\<close> ([1] \<section>2, Lemmas 2.4--2.8)\<close>

text \<open>
  \<^bold>\<open>The reframe.\<close>  r65 certified the head-level / minimal-bad-witness route
  DEAD (\<open>wcl_upper\<close> can hold only vacuously; the head-\<open>>n\<close> content is provably
  non-accessible under a bad witness).  Buchholz [1] avoids this entirely: he
  proves \<open>a \<in> W\<^sub>0\<close> by a FORWARD induction on the LENGTH of the term \<open>a\<close>
  (Lemma 2.7), with the impredicative content HIDDEN inside the definitions of
  the derived sets \<open>X\<^bsup>(a)\<^esup>\<close> / \<open>Xbar\<close> / \<open>W\<^sup>*\<close> and their closure lemmas 2.4/2.5/2.6.

  \<^bold>\<open>The correspondence to our machinery\<close> (established this round).  Our target is
  \<^term>\<open>wf RPrel\<close> (\<open>RPrel\<close> = \<open><\<close> on the \<open>D\<^sub>\<omega>\<close>-free \<open>OT\<close> principals); by
  \<open>wfs_wf_iff_all_acc\<close> and the tuple bridge \<open>wf RPrel \<longleftrightarrow> wf RTrel\<close> this is
  ``every \<open>OT\<^bsub>B\<^esub>\<close> term is \<open><\<close>-accessible'' = Buchholz 2.8 (\<open>a \<in> T\<^sub>0 \<Longrightarrow> a \<in> W\<^sub>0\<close>).
  The \<open>T\<close> / \<open><\<close> / \<open>a[z]\<close> / \<open>dom\<close> / \<open>a+b\<close> of [1] are our \<^typ>\<open>BT\<close> / \<open>lessBT\<close> /
  \<open>operB\<close> / \<open>domB\<close> / \<open>addBT\<close>; \<open>D\<^sub>v b\<close> is \<open>Dprin v b = Trm [DB v b]\<close>; \<open>W\<^sub>0\<close> is
  \<^term>\<open>Wellfounded.acc RTrel\<close>.  The five lemmas map as follows:

  \<^item> \<^bold>\<open>2.4(b)\<close>  \<open>a,b \<in> W\<^sub>v \<Longrightarrow> a+b \<in> W\<^sub>v\<close> (the addition / tuple-assembly layer):
    ALREADY PROVEN as \<open>wfj_tuple_acc\<close> (an \<open>OT\<^bsub>B\<^esub>\<close> term all of whose principal
    components are \<open>RPrel\<close>-accessible is \<open>RTrel\<close>-accessible).  Aliased below as
    \<open>bwo_2_4b_addition_closure\<close>.
  \<^item> \<^bold>\<open>2.7 case \<open>a = D\<^sub>v b\<close>\<close> (principal formation, the \<open>W\<^sub>v\<close>-membership step):
    ALREADY PROVEN as \<open>wfc_principal_acc_of_body\<close> (body \<open>RTrel\<close>-accessible +
    accessibility below the head \<open>\<Longrightarrow>\<close> the principal is \<open>RPrel\<close>-accessible).
    Aliased \<open>bwo_2_7_Dv_formation\<close>.
  \<^item> \<^bold>\<open>2.7/2.8 head recursion\<close> (\<open>A\<^sub>\<nu>(X)\<subseteq> X \<Longrightarrow> W\<^sub>\<nu>\<subseteq> X\<close> stratified by head):
    ALREADY PROVEN as \<open>wfc_wf_of_pbody_hyp\<close> — reduces \<^term>\<open>wf RPrel\<close> to
    ``every \<open>OT\<^bsub>B\<^esub>\<close> principal body is \<open>RTrel\<close>-accessible''.  Aliased
    \<open>bwo_2_8_head_recursion\<close>.
  \<^item> \<^bold>\<open>A1/A2\<close> (\<open>A\<^sub>\<nu>(W\<^sub>\<nu>)=W\<^sub>\<nu>\<close>, least-fixpoint induction): our \<^const>\<open>Wellfounded.acc\<close>
    IS the least fixpoint of ``all predecessors accessible \<open>\<Longrightarrow>\<close> accessible''
    (\<open>accI\<close> / \<open>acc.induct\<close>), so A1/A2 are free.
  \<^item> \<^bold>\<open>2.5\<close> (\<open>A\<^sub>\<nu>(X)\<subseteq> X \<Longrightarrow> A\<^sub>\<nu>(Xbar)\<subseteq> Xbar\<close>, the \<open>D\<^sub>\<nu>\<close>-closure crux) and
    \<^bold>\<open>2.6\<close> (\<open>A\<^sub>\<nu>(W\<^sup>*)\<subseteq> W\<^sup>*\<close>): the GENUINELY REMAINING content.  These build the
    below-head accessibility that r65 showed is unreachable head-locally; their
    proofs use the fundamental-sequence operator \<open>operB\<close>/\<open>domB\<close> essentially
    (2.6 case 4.2 sets \<open>z := D\<^sub>u b[1]\<close>).  Isolated here as the single residual
    \<open>bwo_Wstar_total\<close>.

  What this round contributes GREEN: the faithful transcription of the four
  derived-set definitions of [1] p.138 mapped to our term machinery, the three
  correspondence aliases above, and the main reduction \<open>bwo_2_2_wf\<close> that
  discharges \<^term>\<open>wf RPrel\<close> from \<open>bwo_Wstar_total\<close> — reusing the proven tuple
  layer and head recursion, so that the ONLY thing left is Buchholz's
  \<open>W\<^sup>*\<close>-totality (his 2.6 + the 2.7 length induction).\<close>

subsection \<open>(1) The derived sets of [1] p.138: \<open>A\<^sub>\<nu>(X,a)\<close>, \<open>X\<^bsup>(a)\<^esup>\<close>, \<open>Xbar\<close>, \<open>W\<^sup>*\<close>\<close>

text \<open>\<open>W\<^sub>u\<close>-analog: the terms \<open>z\<close> such that the level-\<open>u\<close> principal \<open>D\<^sub>u z\<close> is
  \<open>RPrel\<close>-accessible (used inside \<open>A\<^sub>\<nu>\<close>'s \<open>dom(a)=T\<^sub>u\<close> clause and in \<open>W\<^sup>*\<close>).\<close>

definition bwo_Wlev :: "nat \<Rightarrow> BT set" where
  "bwo_Wlev u = {z. isOT_BT z \<and> dfree_BT z \<and> DB (enat u) z \<in> Wellfounded.acc RPrel}"

text \<open>[1] p.138 (3) the \<open>a\<close>-shift \<open>X\<^bsup>(a)\<^esup> := {y. a+y \<in> X}\<close>.\<close>

definition bwo_shift :: "BT \<Rightarrow> BT set \<Rightarrow> BT set" where
  "bwo_shift a X = {y. addBT a y \<in> X}"

text \<open>[1] p.138 (4) the \<open>D\<^sub>\<nu>\<close>-closure \<open>Xbar := {y. \<forall>x. x \<in> X \<longrightarrow> x + D\<^sub>\<nu> y \<in> X}\<close>.\<close>

definition bwo_Dclosure :: "enat \<Rightarrow> BT set \<Rightarrow> BT set" where
  "bwo_Dclosure nv X = {y. \<forall>x. x \<in> X \<longrightarrow> addBT x (Dprin nv y) \<in> X}"

text \<open>[1] p.138 (5) \<open>W\<^sup>* := {x. \<forall>u<\<nu>. D\<^sub>u x \<in> W\<^sub>u}\<close> (here \<open>\<nu> = \<omega>\<close>, so \<open>u\<close>
  ranges over all finite levels).  A term is in \<open>W\<^sup>*\<close> iff every level-\<open>u\<close>
  principal over it that is a genuine \<open>OT\<^bsub>B\<^esub>\<close> principal is \<open>RPrel\<close>-accessible.\<close>

definition bwo_Wstar :: "BT set" where
  "bwo_Wstar = {x. \<forall>u. isOT_BP (DB (enat u) x) \<longrightarrow> dfree_BP (DB (enat u) x)
                       \<longrightarrow> DB (enat u) x \<in> Wellfounded.acc RPrel}"

text \<open>[1] p.138 (1)(2) the accessibility operator \<open>A\<^sub>\<nu>(X,a)\<close> and \<open>A\<^sub>\<nu>(X) = {x. A\<^sub>\<nu>(X,x)}\<close>,
  transcribed with our \<open>domB\<close>/\<open>operB\<close>; \<open>a[n] = operB a (numBT n)\<close>, \<open>a[z] = operB a z\<close>,
  \<open>{0} = {Trm []}\<close>, \<open>\<nat> = NatSet\<close>, \<open>T\<^sub>u = TBv (enat u)\<close>.\<close>

definition bwo_Aop :: "enat \<Rightarrow> BT set \<Rightarrow> BT \<Rightarrow> bool" where
  "bwo_Aop nv X a \<longleftrightarrow>
     a = Trm [] \<or>
     ((domB a = {Trm []} \<or> domB a = NatSet) \<and> (\<forall>n. operB a (numBT n) \<in> X)) \<or>
     (\<exists>u. enat u < nv \<and> domB a = TBv (enat u) \<and> (\<forall>z \<in> bwo_Wlev u. operB a z \<in> X))"

subsection \<open>(2) Correspondence aliases: Buchholz 2.4(b) / 2.7-\<open>D\<^sub>v\<close> / 2.8 = proven code\<close>

lemmas bwo_2_4b_addition_closure = wfj_tuple_acc
lemmas bwo_2_7_Dv_formation      = wfc_principal_acc_of_body
lemmas bwo_2_8_head_recursion    = wfc_wf_of_pbody_hyp

subsection \<open>(3) The single residual and the main reduction \<open>bwo_2_2_wf\<close>\<close>

text \<open>The residual = Buchholz's \<open>W\<^sup>*\<close>-totality (his 2.6 \<open>A\<^sub>\<nu>(W\<^sup>*)\<subseteq> W\<^sup>*\<close> together with
  the 2.7 length induction give it): every \<open>OT\<^bsub>B\<^esub>\<close> term lies in \<open>W\<^sup>*\<close>.\<close>

definition bwo_Wstar_total :: bool where
  "bwo_Wstar_total \<longleftrightarrow> (\<forall>t. isOT_BT t \<longrightarrow> dfree_BT t \<longrightarrow> t \<in> bwo_Wstar)"

text \<open>From \<open>W\<^sup>*\<close>-totality, every \<open>OT\<^bsub>B\<^esub>\<close> principal is \<open>RPrel\<close>-accessible (take the
  principal's own head as the level \<open>u\<close> in the \<open>W\<^sup>*\<close> clause of its body).\<close>

lemma bwo_all_OT_principal_acc_of_Wstar_total:
  assumes WT: "bwo_Wstar_total"
    and ot: "isOT_BP p" and df: "dfree_BP p"
  shows "p \<in> Wellfounded.acc RPrel"
proof -
  obtain u d where peq: "p = DB u d" by (cases p) auto
  have une: "u \<noteq> \<infinity>" using df peq by simp
  then obtain k where uk: "u = enat k" by (cases u) auto
  have otd: "isOT_BT d" using ot peq by simp
  have dfd: "dfree_BT d" using df peq by simp
  have dW: "d \<in> bwo_Wstar" using WT[unfolded bwo_Wstar_total_def] otd dfd by blast
  have iotk: "isOT_BP (DB (enat k) d)" using ot peq uk by simp
  have idfk: "dfree_BP (DB (enat k) d)" using df peq uk by simp
  have "DB (enat k) d \<in> Wellfounded.acc RPrel"
    using dW iotk idfk unfolding bwo_Wstar_def by blast
  then show ?thesis using peq uk by simp
qed

theorem bwo_2_2_wf:
  assumes WT: "bwo_Wstar_total"
  shows "wf RPrel"
proof (rule bwo_2_8_head_recursion)
  fix v c
  assume otp: "isOT_BP (DB v c)" and dfp: "dfree_BP (DB v c)"
  have otc: "isOT_BT c" using otp by simp
  have dfc: "dfree_BT c" using dfp by simp
  obtain rs where ceq: "c = Trm rs" by (cases c) auto
  have otc': "(\<forall>r \<in> set rs. isOT_BP r) \<and> descP rs" using otc ceq by simp
  have dfc': "\<forall>r \<in> set rs. dfree_BP r" using dfc ceq by simp
  have comps: "\<forall>r \<in> set (untrm c). r \<in> Wellfounded.acc RPrel"
  proof
    fix r assume rin: "r \<in> set (untrm c)"
    have rin': "r \<in> set rs" using rin ceq by simp
    have otr: "isOT_BP r" using otc' rin' by blast
    have dfr: "dfree_BP r" using dfc' rin' by blast
    show "r \<in> Wellfounded.acc RPrel"
      by (rule bwo_all_OT_principal_acc_of_Wstar_total[OF WT otr dfr])
  qed
  show "c \<in> Wellfounded.acc RTrel"
    by (rule bwo_2_4b_addition_closure[OF otc dfc comps])
qed

text \<open>The converse: the residual is EXACTLY \<^term>\<open>wf RPrel\<close>-strength (no
  overshoot).  If \<^term>\<open>wf RPrel\<close> then every principal is accessible, so every
  term is in \<open>W\<^sup>*\<close>.\<close>

lemma bwo_Wstar_total_of_wf:
  assumes "wf RPrel"
  shows "bwo_Wstar_total"
proof (unfold bwo_Wstar_total_def, intro allI impI)
  fix t assume "isOT_BT t" and "dfree_BT t"
  have all: "\<forall>p. p \<in> Wellfounded.acc RPrel" using assms wfs_wf_iff_all_acc by blast
  show "t \<in> bwo_Wstar" unfolding bwo_Wstar_def using all by blast
qed

theorem bwo_2_2_wf_iff: "bwo_Wstar_total \<longleftrightarrow> wf RPrel"
  using bwo_2_2_wf bwo_Wstar_total_of_wf by blast

text \<open>\<^bold>\<open>Round 66 status.\<close>  \<^term>\<open>wf RPrel\<close> is now discharged from the single
  residual \<open>bwo_Wstar_total\<close> via Buchholz's own decomposition — the tuple /
  addition layer (2.4(b) = \<open>wfj_tuple_acc\<close>) and the head recursion (2.8 =
  \<open>wfc_wf_of_pbody_hyp\<close>) are both PROVEN, so nothing head-local remains.  The
  residual \<open>bwo_Wstar_total\<close> is exactly what Buchholz [1] establishes by his
  Lemma 2.6 (\<open>A\<^sub>\<nu>(W\<^sup>*) \<subseteq> W\<^sup>*\<close>) plus the Lemma 2.7 induction on term length, and it
  is the RIGHT residual (it sidesteps the r65 head-level wall because its content
  lives in the fundamental-sequence closure \<open>bwo_Dclosure\<close> / \<open>bwo_Wstar\<close>, not in a
  head-level transfinite induction).

  \<^bold>\<open>Exact remaining obstruction.\<close>  To prove \<open>bwo_Wstar_total\<close> one transcribes
  Lemma 2.6 by cases on \<open>domB b\<close> / the shape of \<open>b\<close>:
  \<^item> cases \<open>b = 0\<close> (\<open>v = 0\<close> / successor / \<open>\<omega>\<close>) and the successor case use only the
    successor / (W2)(W3) closure — reachable from \<open>wfc_principal_acc_of_body\<close>
    once the below-head accessibility is threaded;
  \<^item> case 4.1 (\<open>dom(b)=T\<^sub>u\<close>, \<open>u<v\<close>) is direct;
  \<^item> case 4.2 (\<open>v \<le> u\<close>) is the crux: it needs \<open>operB\<close> at \<open>z := D\<^sub>u b[1]\<close> with
    \<open>1 \<in> W\<^sub>u\<close> and \<open>b[1] \<in> W\<^sup>*\<close>, i.e. the fundamental-sequence step-down of [1] \<section>3.
  The load-bearing missing analytic fact is the fundamental-sequence strict
  descent \<open>a[n] < a\<close> (currently only the \<^emph>\<open>cited\<close> \<open>buc1_3_2a_fseq_lt\<close>, still a
  \<open>sorry\<close> in \<open>pss_paper\<close>) together with its cofinality (every \<open>b < a\<close> is \<open>\<le>\<close> some
  \<open>a[n]\<close>), which turns fundamental-sequence closure into \<open><\<close>-accessibility.
  Proving 2.6 (esp. 4.2) and threading it through the 2.7 length induction is the
  multi-round work; \<open>bwo_2_2_wf\<close> guarantees it is the ONLY work.\<close>

(* ===== end r66 bwo block (Buchholz \<section>2 transcription; residual = bwo_Wstar_total) ===== *)

(* ===================================================================== *)
(* ===== r67 (OPUS 4.8): the r66 HEAD residual is REFUTED             ==== *)
(* =====   (ox7_hole_right_spine_terminal / bpHeadV t' < bpHeadV X1)   ==== *)
(* =====                                                               ==== *)
(* ===== STEP-0 (python/_r67_headterm_step0.py, real ST_PS census      ==== *)
(* ===== hosts, oper-images of diagonals; yaBMS is_standard oracle):    ==== *)
(* =====   The r66 position-0 first-difference HEAD                     ==== *)
(* =====     forall matched-hole tx' in GBT u X1.  bpHeadV t' < bpHeadV ==== *)
(* =====     X1   (t' the A-side, share => bpHeadV t' = bpHeadV tx')    ==== *)
(* =====   is FALSE.  90/332 matched tx' have bpHeadV t' = bpHeadV X1   ==== *)
(* =====   (EQUALITY, never >).  The stronger task claim bpHeadV t'=ub  ==== *)
(* =====   fails 198/332.                                              ==== *)
(* =====                                                               ==== *)
(* ===== GENUINE ST_PS CEX (is_standard = 1 via yaBMS `bms -s`):        ==== *)
(* =====   M = (0,0)(1,1)(2,2)(3,3)(4,1)(5,0)(6,1)(7,1)(8,1)            ==== *)
(* =====   reduced, monoT, condIII, hasParent, 1<Lng-1, ltJ            ==== *)
(* =====   (s84x_jm3=5 < transJm1=7).  v1=1, ub=0.                     ==== *)
(* =====   X1 = D_1(D_1(D_0(D_0 0))),  bpHeadV X1 = 1.                  ==== *)
(* =====   matched tx' = D_1(D_0(D_0 0)) in GBT u X1 (u in {0,1}),      ==== *)
(* =====   flat = [D_0](=sc) @ flatBP(D_0(D_0 0))(=hole P) @ [] (bc);   ==== *)
(* =====   size t' < size A1 (bound SATISFIED, does not exclude it);    ==== *)
(* =====   bpHeadV tx' = 1 = bpHeadV X1  --- NOT strictly less.         ==== *)
(* =====                                                               ==== *)
(* ===== ROOT CAUSE.  The matched-hole set (tx' in GBT u X1 carrying    ==== *)
(* =====   the hole P = D_ub(D_ub 0) at its rightmost spine, bc all-RP) ==== *)
(* =====   is NOT just the immediate parent body of P: it contains      ==== *)
(* =====   EVERY higher right-spine ancestor body of P.  A higher one   ==== *)
(* =====   b1 = D_h0(...P...) has first head h0 = bpHeadV X1, so the    ==== *)
(* =====   position-0 head AGREES with X1 and the first-difference sits ==== *)
(* =====   DEEPER (where t' hits the hole head ub while X1 still has an  ==== *)
(* =====   s0 right-spine head >= v1 > ub).  r66's position-0 reduction ==== *)
(* =====   (ot7_SETLE1_ltJ_of_head, ox7_headlt_lessBT) is thus too      ==== *)
(* =====   STRONG; HEAD cannot be discharged (it is false).             ==== *)
(* =====                                                               ==== *)
(* ===== WHAT IS STILL TRUE (0 fails on all matched tx'):               ==== *)
(* =====   (a) bpHeadV t' <= bpHeadV X1   (weak head bound);            ==== *)
(* =====   (b) leBT t' X1                 (spineH itself; r65: 537/537).==== *)
(* =====   So SETLE1 is reduced (ox6_SETLE1_reduce_restr) to the TRUE   ==== *)
(* =====   spineH = "leBT t' X1 for every matched-hole tx' in GBT u X1  ==== *)
(* =====   (size t' < size A1)", which is NOT further reducible to a    ==== *)
(* =====   position-0 head separation.                                  ==== *)
(* =====                                                               ==== *)
(* ===== CORRECTED RESIDUAL / NEXT IDEA (right-spine DESCENT, not the   ==== *)
(* =====   position-0 head, and INDEPENDENT of A0 since the divergence  ==== *)
(* =====   is strictly before the hole body):                          ==== *)
(* =====   prove   lessBT tx' X1   for every matched-hole tx' in        ==== *)
(* =====   GBT u X1  (X-side, hole body X0 = D_ub 0), by induction down  ==== *)
(* =====   X1's rightmost spine:                                        ==== *)
(* =====     * bpHeadV X1 = h0 is the MAX right-spine head              ==== *)
(* =====       (OT descP + rnsub RightNodes bound, r63/r65; the LEFT-   ==== *)
(* =====       end head governs, cf. ox7_bpHeadV_body_ge_v1);           ==== *)
(* =====     * matched tx' = D_{h_k}(deeper), h_k <= h0; if h_k < h0    ==== *)
(* =====       then bpHeadV tx' < bpHeadV X1 closes at THIS level        ==== *)
(* =====       (ox7_headlt_lessBT); if h_k = h0 recurse into the bodies  ==== *)
(* =====       (both share the head, compare one spine level deeper);    ==== *)
(* =====     * the base of the descent is the hole D_ub, ub < v1 <= all  ==== *)
(* =====       right-spine heads, so the recursion terminates with a     ==== *)
(* =====       strict drop.                                             ==== *)
(* =====   Then transport lessBT tx' X1 to lessBT t' X1 (t' = tx' with   ==== *)
(* =====   hole body X0 -> A0): the first-difference is at an outer      ==== *)
(* =====   principal head, strictly ABOVE the hole body, so replacing    ==== *)
(* =====   X0 by A0 leaves the difference and its verdict unchanged.     ==== *)
(* =====   The load-bearing NEW lemma is "matched right-spine sub-body   ==== *)
(* =====   of the census X1 is lessBT X1" (a shared-outer-heads /        ==== *)
(* =====   hole-head-drop first-difference), which the existing          ==== *)
(* =====   position-0 bricks (ox7_headlt_lessBT / ox7_bpHeadV_share)     ==== *)
(* =====   are too shallow to give.                                     ==== *)
(* ===================================================================== *)


(* ===================================================================== *)
(* ===== r67 buc1: Buchholz [1] Lemma 2.4(a) shift-closure + the    ===== *)
(* ===== addBT/domB/operB glue underneath 2.5/2.6/2.7.  Prefix bwo_ ===== *)
(* ===== (append-only).                                             ===== *)
(* ===================================================================== *)

section \<open>r67 bwo — the \<open>+\<^sub>B\<close> glue and Buchholz [1] Lemma 2.4(a)\<close>

text \<open>
  \<^bold>\<open>Round 67 contribution.\<close>  The fundamental-sequence strict descent
  \<open>a[z] < a\<close> for \<open>z \<in> dom(a) \<union> \<nat>\<close> ([Buc1] Lemma 3.2(a), GENERAL \<open>z\<close>) is
  ALREADY PROVEN in the frozen base as @{thm [source] b1x_descent}
  (and the numeral form @{thm [source] m_buc1_3_2a_fseq_lt}, with \<open>OT\<^bsub>B\<^esub>\<close>-closure
  @{thm [source] m_buc1_3_2_OT_B_closed}).  Hence the descent is NOT the residual
  blocker for \<open>bwo_Wstar_total\<close>.

  Here we transcribe the ABSTRACT set-operator layer of Buchholz's proof that
  does not touch \<open>acc\<close>: the commutation of \<open>domB\<close>/\<open>operB\<close> with a left \<open>+\<^sub>B\<close>-prefix
  (both act on the last principal only), and [Buc1] Lemma 2.4(a) — the shift
  \<open>X\<^bsup>(a)\<^esup>\<close> is \<open>A\<^sub>\<nu>\<close>-closed whenever \<open>X\<close> is and \<open>a \<in> X\<close>.  These are the reusable
  bricks underneath Lemmas 2.5 (\<open>D\<^sub>\<nu>\<close>-closure) and 2.7 (length induction).\<close>

subsection \<open>(4) \<open>+\<^sub>B\<close> / \<open>domB\<close> / \<open>operB\<close> glue\<close>

text \<open>\<open>dom(0) = \<emptyset>\<close>.\<close>

lemma bwo_domB_Nil: "domB (Trm []) = {}"
  by (subst domB_unfold) simp

text \<open>\<open>a + 0 = a\<close>, \<open>0 + b = b\<close>, associativity of \<open>+\<^sub>B\<close> (all from list \<open>@\<close>).\<close>

lemma bwo_addBT_Nil_right: "a +\<^sub>B Trm [] = a"
  by (cases a) simp

lemma bwo_addBT_Nil_left: "Trm [] +\<^sub>B b = b"
  by (cases b) simp

lemma bwo_addBT_assoc: "(a +\<^sub>B b) +\<^sub>B c = a +\<^sub>B (b +\<^sub>B c)"
  by (cases a; cases b; cases c) simp

text \<open>\<open>dom(a + b) = dom(b)\<close> for \<open>b \<noteq> 0\<close> (\<open>dom\<close> reads only the last principal,
  @{thm [source] domB_last_component}).\<close>

lemma bwo_addBT_domB:
  assumes bne: "b \<noteq> Trm []"
  shows "domB (a +\<^sub>B b) = domB b"
proof -
  obtain as where aeq: "a = Trm as" by (cases a) auto
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  have bsne: "bs \<noteq> []" using bne beq by simp
  have absne: "as @ bs \<noteq> []" using bsne by simp
  have "domB (a +\<^sub>B b) = domB (Trm (as @ bs))" using aeq beq by simp
  also have "\<dots> = domB (Trm [last (as @ bs)])" by (rule domB_last_component[OF absne])
  also have "domB (Trm [last (as @ bs)]) = domB (Trm [last bs])" using bsne by simp
  finally have L: "domB (a +\<^sub>B b) = domB (Trm [last bs])" .
  have R: "domB b = domB (Trm [last bs])" using beq domB_last_component[OF bsne] by simp
  show ?thesis using L R by simp
qed

text \<open>\<open>operB\<close> splits off the last principal, uniformly over single/multi terms.\<close>

lemma bwo_operB_split:
  assumes bsne: "bs \<noteq> []"
  shows "operB (Trm bs) z = Trm (butlast bs) +\<^sub>B operB (Trm [last bs]) z"
proof (cases "tl bs")
  case Nil
  from bsne obtain p where "bs = [p]" using Nil by (cases bs) auto
  thus ?thesis by (simp add: bwo_addBT_Nil_left)
next
  case (Cons q rest)
  from bsne obtain p ps where "bs = p # ps" by (cases bs) auto
  hence bs3: "bs = p # q # rest" using Cons by auto
  show ?thesis unfolding bs3 by (rule b1x_operB_multi)
qed

text \<open>\<open>(a + b)[z] = a + b[z]\<close> for \<open>b \<noteq> 0\<close>.\<close>

lemma bwo_addBT_operB:
  assumes bne: "b \<noteq> Trm []"
  shows "operB (a +\<^sub>B b) z = a +\<^sub>B operB b z"
proof -
  obtain as where aeq: "a = Trm as" by (cases a) auto
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  have bsne: "bs \<noteq> []" using bne beq by simp
  have ab: "a +\<^sub>B b = Trm (as @ bs)" using aeq beq by simp
  have absne: "as @ bs \<noteq> []" using bsne by simp
  have lst: "last (as @ bs) = last bs" using bsne by simp
  have blt: "butlast (as @ bs) = as @ butlast bs" using bsne by (simp add: butlast_append)
  have "operB (a +\<^sub>B b) z
          = Trm (butlast (as @ bs)) +\<^sub>B operB (Trm [last (as @ bs)]) z"
    using ab bwo_operB_split[OF absne] by simp
  also have "\<dots> = Trm (as @ butlast bs) +\<^sub>B operB (Trm [last bs]) z"
    using lst blt by simp
  also have "\<dots> = Trm as +\<^sub>B (Trm (butlast bs) +\<^sub>B operB (Trm [last bs]) z)"
  proof -
    have "Trm (as @ butlast bs) +\<^sub>B operB (Trm [last bs]) z
            = (Trm as +\<^sub>B Trm (butlast bs)) +\<^sub>B operB (Trm [last bs]) z" by simp
    also have "\<dots> = Trm as +\<^sub>B (Trm (butlast bs) +\<^sub>B operB (Trm [last bs]) z)"
      by (rule bwo_addBT_assoc)
    finally show ?thesis .
  qed
  also have "\<dots> = Trm as +\<^sub>B operB (Trm bs) z"
    using bwo_operB_split[OF bsne] by simp
  finally show ?thesis using aeq beq by simp
qed

text \<open>\<open>A\<^sub>\<nu>(X,a)\<close> is monotone in the level bound \<open>\<nu>\<close> (only the \<open>T\<^sub>u\<close> clause
  depends on \<open>\<nu>\<close>, through \<open>u < \<nu>\<close>).  Buchholz's \<open>A\<^sub>u(X) \<subseteq> A\<^sub>\<nu>(X)\<close> for \<open>u \<le> \<nu>\<close>.\<close>

lemma bwo_Aop_mono_nv:
  assumes le: "nv \<le> nv'" and a: "bwo_Aop nv X a"
  shows "bwo_Aop nv' X a"
proof -
  consider "a = Trm []"
    | "(domB a = {Trm []} \<or> domB a = NatSet) \<and> (\<forall>n. operB a (numBT n) \<in> X)"
    | u where "enat u < nv" "domB a = TBv (enat u)" "\<forall>z \<in> bwo_Wlev u. operB a z \<in> X"
    using a[unfolded bwo_Aop_def] by blast
  thus ?thesis
  proof cases
    case 1 thus ?thesis unfolding bwo_Aop_def by blast
  next
    case 2 thus ?thesis unfolding bwo_Aop_def by blast
  next
    case (3 u)
    have "enat u < nv'" using 3(1) le by (rule less_le_trans)
    thus ?thesis using 3(2) 3(3) unfolding bwo_Aop_def by blast
  qed
qed

subsection \<open>(5) [Buc1] Lemma 2.4(a): shift closure \<open>A\<^sub>\<nu>(X\<^bsup>(a)\<^esup>) \<subseteq> X\<^bsup>(a)\<^esup>\<close>\<close>

text \<open>Faithful transcription of [Buc1] p.138 Lemma 2.4(a).  Assume \<open>X\<close> is
  \<open>A\<^sub>\<nu>\<close>-closed and \<open>a \<in> X\<close>; then every \<open>b\<close> with \<open>A\<^sub>\<nu>(X\<^bsup>(a)\<^esup>, b)\<close> lies in
  \<open>X\<^bsup>(a)\<^esup>\<close>, i.e. \<open>a + b \<in> X\<close>.  The three cases (\<open>b = 0\<close>; \<open>dom(b) \<in> {{0},\<nat>}\<close>;
  \<open>dom(b) = T\<^sub>u\<close>) use the glue \<open>dom(a+b)=dom(b)\<close> and \<open>(a+b)[z]=a+b[z]\<close> to
  transport the \<open>A\<^sub>\<nu>\<close>-witness for \<open>b\<close> into one for \<open>a+b\<close>.\<close>

lemma bwo_2_4a_shift_closure:
  assumes Acl: "\<And>c. bwo_Aop nv X c \<Longrightarrow> c \<in> X"
    and aX: "a \<in> X"
    and body: "bwo_Aop nv (bwo_shift a X) b"
  shows "b \<in> bwo_shift a X"
proof -
  have goal: "a +\<^sub>B b \<in> X"
  proof -
    consider (zero) "b = Trm []"
      | (num) "(domB b = {Trm []} \<or> domB b = NatSet)
               \<and> (\<forall>n. operB b (numBT n) \<in> bwo_shift a X)"
      | (tu) u where "enat u < nv" "domB b = TBv (enat u)"
               "\<forall>z \<in> bwo_Wlev u. operB b z \<in> bwo_shift a X"
      using body[unfolded bwo_Aop_def] by blast
    thus ?thesis
    proof cases
      case zero
      thus ?thesis using aX bwo_addBT_Nil_right by simp
    next
      case num
      have bne: "b \<noteq> Trm []"
      proof
        assume z: "b = Trm []"
        have dz: "domB b = {}" using z bwo_domB_Nil by simp
        have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
        moreover have "Trm [] \<in> {Trm []}" by simp
        ultimately show False using conjunct1[OF num] dz by auto
      qed
      have d: "domB (a +\<^sub>B b) = {Trm []} \<or> domB (a +\<^sub>B b) = NatSet"
        using conjunct1[OF num] bwo_addBT_domB[OF bne] by simp
      have op: "\<forall>n. operB (a +\<^sub>B b) (numBT n) \<in> X"
      proof (intro allI)
        fix n
        have "operB b (numBT n) \<in> bwo_shift a X" using conjunct2[OF num] by blast
        hence "a +\<^sub>B operB b (numBT n) \<in> X" by (simp add: bwo_shift_def)
        thus "operB (a +\<^sub>B b) (numBT n) \<in> X"
          using bwo_addBT_operB[OF bne] by simp
      qed
      have "bwo_Aop nv X (a +\<^sub>B b)"
        using d op unfolding bwo_Aop_def by blast
      thus ?thesis by (rule Acl)
    next
      case (tu u)
      have bne: "b \<noteq> Trm []"
      proof
        assume z: "b = Trm []"
        have "TBv (enat u) = {}" using z tu(2) bwo_domB_Nil by simp
        moreover have "Trm [] \<in> TBv (enat u)" by (simp add: TBv_def)
        ultimately show False by simp
      qed
      have d: "domB (a +\<^sub>B b) = TBv (enat u)"
        using tu(2) bwo_addBT_domB[OF bne] by simp
      have op: "\<forall>z \<in> bwo_Wlev u. operB (a +\<^sub>B b) z \<in> X"
      proof
        fix z assume zW: "z \<in> bwo_Wlev u"
        have "operB b z \<in> bwo_shift a X" using tu(3) zW by blast
        hence "a +\<^sub>B operB b z \<in> X" by (simp add: bwo_shift_def)
        thus "operB (a +\<^sub>B b) z \<in> X"
          using bwo_addBT_operB[OF bne] by simp
      qed
      have "bwo_Aop nv X (a +\<^sub>B b)"
        using tu(1) d op unfolding bwo_Aop_def by blast
      thus ?thesis by (rule Acl)
    qed
  qed
  show ?thesis using goal by (simp add: bwo_shift_def)
qed

subsection \<open>(6) [Buc1] Lemma 2.5 sub-result (1), modulo leastness (A2)\<close>

text \<open>Shape of the successor-principal \<open>D\<^bsub>u+1\<^esub>0\<close>: its domain is \<open>T\<^sub>u\<close> and its
  fundamental sequence is the identity, \<open>(D\<^bsub>u+1\<^esub>0)[z] = z\<close> (operB case ([].2)).\<close>

lemma bwo_domB_Dsucc0: "domB (Trm [DB (enat (Suc u)) (Trm [])]) = TBv (enat u)"
  by (subst domB_unfold) (simp add: zero_enat_def)

lemma bwo_operB_Dsucc0: "operB (Trm [DB (enat (Suc u)) (Trm [])]) z = z"
proof (rule b1x_operB_Dsucc)
  show "enat (Suc u) \<noteq> 0" by (simp add: zero_enat_def)
  show "enat (Suc u) \<noteq> \<infinity>" by simp
qed

text \<open>[Buc1] Lemma 2.5, sub-result (1): \<open>\<forall>u<\<nu>. a + D\<^bsub>u+1\<^esub>0 \<in> X\<close> (p.138).  This is
  the ONLY step of Lemma 2.5 that invokes Buchholz's leastness
  (A2) \<open>A\<^sub>u(Y) \<subseteq> Y \<Longrightarrow> W\<^sub>u \<subseteq> Y\<close>.  For the \<^emph>\<open>acc\<close>-based \<open>bwo_Wlev\<close> of this
  development (A2) is the \<^bold>\<open>hard\<close> direction — it says
  \<open>{z. D\<^sub>u z \<in> acc} \<subseteq>\<close> every \<open>A\<^sub>u\<close>-closed set, i.e. the fundamental sequences are
  cofinal in the \<open><\<close>-predecessors of \<open>D\<^sub>u z\<close> (Buchholz's genuine \<section>2/\<section>3 content,
  NOT free here because \<open>bwo_Wlev\<close> is defined via \<open>acc\<close>, not as the least fixpoint
  of \<open>A\<^sub>u\<close>).  It is carried as the explicit hypothesis \<open>A2\<close>, isolating it as THE
  residual; everything else — 2.4(a), the level monotonicity \<open>A\<^sub>u \<subseteq> A\<^sub>\<nu>\<close>, and the
  \<open>+\<^sub>B\<close>/\<open>domB\<close>/\<open>operB\<close> glue — is discharged.\<close>

lemma bwo_2_5_sub1:
  assumes Acl: "\<And>c. bwo_Aop nv X c \<Longrightarrow> c \<in> X"
    and aX: "a \<in> X"
    and A2: "\<And>Y. (\<And>c. bwo_Aop (enat u) Y c \<Longrightarrow> c \<in> Y) \<Longrightarrow> bwo_Wlev u \<subseteq> Y"
    and ult: "enat u < nv"
  shows "a +\<^sub>B Trm [DB (enat (Suc u)) (Trm [])] \<in> X"
proof -
  let ?D = "Trm [DB (enat (Suc u)) (Trm [])] :: BT"
  have Dne: "?D \<noteq> Trm []" by simp
  have domAD: "domB (a +\<^sub>B ?D) = TBv (enat u)"
    using bwo_addBT_domB[OF Dne] bwo_domB_Dsucc0 by simp
  have opAD: "\<And>z. operB (a +\<^sub>B ?D) z = a +\<^sub>B z"
  proof -
    fix z
    have "operB (a +\<^sub>B ?D) z = a +\<^sub>B operB ?D z" by (rule bwo_addBT_operB[OF Dne])
    also have "\<dots> = a +\<^sub>B z" using bwo_operB_Dsucc0 by simp
    finally show "operB (a +\<^sub>B ?D) z = a +\<^sub>B z" .
  qed
  \<comment> \<open>2.4(a): \<open>X\<^bsup>(a)\<^esup>\<close> is \<open>A\<^sub>\<nu>\<close>-closed, hence \<open>A\<^sub>u\<close>-closed since \<open>A\<^sub>u \<subseteq> A\<^sub>\<nu>\<close>\<close>
  have shiftAu: "\<And>c. bwo_Aop (enat u) (bwo_shift a X) c \<Longrightarrow> c \<in> bwo_shift a X"
  proof -
    fix c assume "bwo_Aop (enat u) (bwo_shift a X) c"
    hence bnv: "bwo_Aop nv (bwo_shift a X) c"
      by (rule bwo_Aop_mono_nv[OF less_imp_le[OF ult]])
    show "c \<in> bwo_shift a X" by (rule bwo_2_4a_shift_closure[OF Acl aX bnv])
  qed
  \<comment> \<open>(A2): \<open>W\<^sub>u \<subseteq> X\<^bsup>(a)\<^esup>\<close>\<close>
  have WsubShift: "bwo_Wlev u \<subseteq> bwo_shift a X" by (rule A2[OF shiftAu])
  have azX: "\<And>z. z \<in> bwo_Wlev u \<Longrightarrow> a +\<^sub>B z \<in> X"
  proof -
    fix z assume "z \<in> bwo_Wlev u"
    hence "z \<in> bwo_shift a X" using WsubShift by blast
    thus "a +\<^sub>B z \<in> X" by (simp add: bwo_shift_def)
  qed
  have opX: "\<forall>z \<in> bwo_Wlev u. operB (a +\<^sub>B ?D) z \<in> X"
  proof
    fix z assume "z \<in> bwo_Wlev u"
    hence "a +\<^sub>B z \<in> X" by (rule azX)
    thus "operB (a +\<^sub>B ?D) z \<in> X" using opAD by simp
  qed
  have "bwo_Aop nv X (a +\<^sub>B ?D)"
    using ult domAD opX unfolding bwo_Aop_def by blast
  thus ?thesis by (rule Acl)
qed

(* ===== end r67 bwo block (glue + [Buc1] Lemma 2.4(a) + 2.5 sub(1)/A2) ===== *)


(* ===================================================================== *)
(* ===== r68 (OPUS 4.8): the CORRECTED SETLE1 residual — the DEEP    ==== *)
(* =====   first-difference descent.  Prefix  ox8_.                   ==== *)
(* =====                                                              ==== *)
(* ===== r67 REFUTED the position-0 HEAD route (bpHeadV t' < bpHeadV  ==== *)
(* ===== X1 is FALSE: the matched-hole set contains EVERY higher      ==== *)
(* ===== right-spine ancestor, and a higher one shares X1's outer     ==== *)
(* ===== head).  The TRUE residual (spineH of ox6_SETLE1_reduce_restr)==== *)
(* ===== is  leBT t' X1  for the matched right-spine ancestor bodies. ==== *)
(* =====                                                              ==== *)
(* ===== STEP-0 (python/_r68_deepdesc_step0.py; 1984 REAL ST_PS       ==== *)
(* ===== census hosts = BFS-standard corpus, condIII/IV + hasParent + ==== *)
(* ===== 1<Lng-1 + ltJ; 11306 peel levels):                           ==== *)
(* =====   * goal   lessBT Z_k X1  : 11306/11306 (0 fails)            ==== *)
(* =====   * X-side lessBT Y_k X1  : 11306/11306                      ==== *)
(* =====   * VERDICT INVARIANCE    : 11306/11306 — the verdict of     ==== *)
(* =====     lessBT (Y_k with hole body := Q) X1 is the SAME for      ==== *)
(* =====     Q in {0, D_ub 0, A0, BIG}, i.e. the first difference     ==== *)
(* =====     sits strictly ABOVE the hole body (so the X0 -> A0       ==== *)
(* =====     transport is sound).                                     ==== *)
(* =====   * X1's right spine above the hole: heads all >= v1 > ub,   ==== *)
(* =====     and EVERY spine level is a PURE CHAIN (single principal, ==== *)
(* =====     11306/11306) — the comparison path = the spine path.     ==== *)
(* =====   * bpHeadV Z_k > bpHeadV X1 : NEVER (0/11306); = : 4083     ==== *)
(* =====     (r67's CEX class, needs the deep descent); < : 7223.     ==== *)
(* =====   * every matched tx' in GBT 0 X1 IS a spine body Y_k        ==== *)
(* =====     (off-spine matched: 0).                                  ==== *)
(* =====   * NEGATIVE: the stepwise chain  lessBT Y_k Y_(k-1)  FAILS  ==== *)
(* =====     2274/11306 — so the descent CANNOT be assembled by       ==== *)
(* =====     transitivity along the spine; it must be proved AGAINST  ==== *)
(* =====     X1 directly (a lexicographic / self-maximality fact).    ==== *)
(* =====   * isOT_BT X1 : 1984/1984.                                  ==== *)
(* =====                                                              ==== *)
(* ===== THE SOURCE OF THE DESCENT (this block).  The self-maximality ==== *)
(* ===== of the spine is NOT an OT-generic fact (the head word can    ==== *)
(* ===== genuinely increase: 3379 strict drops vs 5943 non-drops) —   ==== *)
(* ===== it comes from ONE Buchholz G-condition, at the LOW enclosing ==== *)
(* ===== head e3:  D_e3(body) is the deepest-right principal of       ==== *)
(* ===== Trans M (the kind-1 scb block k1 of oi5_IIIIV_pkg), so       ==== *)
(* ===== m_8_7_OT_scb_recursive gives  isOT_BP (D_e3 body), i.e.      ==== *)
(* =====     for all x in G_e3(body).  x < body.                      ==== *)
(* ===== And e3 < v1 (oi5_regime(1)) <= EVERY right-spine head of     ==== *)
(* ===== body (ox7_RightNodes_body_ge_v1), so the WHOLE right spine   ==== *)
(* ===== of body lies inside G_e3(body).  Hence EVERY right-spine     ==== *)
(* ===== sub-body of body is < body — exactly the self-maximality     ==== *)
(* ===== that STEP-0 measures, now unconditional.                     ==== *)
(* ===================================================================== *)

section \<open>r68 ox8 — right-spine sub-bodies and the OT \<open>G\<close>-descent\<close>

subsection \<open>(1) The right-spine sub-body operators \<open>ox8_lastV\<close> / \<open>ox8_lastT\<close> /
  \<open>ox8_rsub\<close>\<close>

text \<open>\<open>ox8_lastT t\<close> = the body of the LAST principal of \<open>t\<close> (\<open>0\<close> if \<open>t = 0\<close>),
  \<open>ox8_lastV t\<close> its head.  This is exactly the step the align3 peel
  (@{thm [source] otx2_align3} Case B, @{thm [source] ox7_align3_track}) takes:
  the engine's ancestor bodies are the iterates \<open>ox8_rsub t k\<close>.  Note
  @{const RightNodes} walks the SAME chain (its defining equation reads the last
  principal), which is what makes the r63 spine bound
  @{thm [source] ox7_RightNodes_body_ge_v1} applicable to these iterates.\<close>

fun ox8_lastV :: "BT \<Rightarrow> enat" where
  "ox8_lastV (Trm ps) = (if ps = [] then 0 else (case last ps of DB v b \<Rightarrow> v))"

fun ox8_lastT :: "BT \<Rightarrow> BT" where
  "ox8_lastT (Trm ps) = (if ps = [] then Trm [] else (case last ps of DB v b \<Rightarrow> b))"

fun ox8_rsub :: "BT \<Rightarrow> nat \<Rightarrow> BT" where
  "ox8_rsub t 0 = t"
| "ox8_rsub t (Suc k) = ox8_rsub (ox8_lastT t) k"

text \<open>The one-step \<open>G\<^bsub>B\<^esub>\<close>-membership: the last principal's body lies in
  \<open>G\<^sub>u t\<close> as soon as \<open>u\<close> is below that principal's head (clause (G2)).\<close>

lemma ox8_lastT_GBT:
  assumes ne: "t \<noteq> 0\<^sub>B" and uh: "u \<le> ox8_lastV t"
  shows "ox8_lastT t \<in> GBT u t"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using ne tps by auto
  obtain v b where lp: "last ps = DB v b" by (cases "last ps")
  have hv: "ox8_lastV t = v" using tps psne lp by simp
  have ht: "ox8_lastT t = b" using tps psne lp by simp
  have uv: "u \<le> v" using uh hv by simp
  have bin: "b \<in> GBP u (last ps)" using uv lp by simp
  have lin: "last ps \<in> set ps" using psne by simp
  have "b \<in> (\<Union>p \<in> set ps. GBP u p)" using bin lin by blast
  hence "b \<in> GBT u t" using tps by simp
  thus ?thesis using ht by simp
qed

text \<open>Iterated: every right-spine sub-body \<open>ox8_rsub t k\<close> (\<open>k \<ge> 1\<close>) lies in
  \<open>G\<^sub>u t\<close>, provided the spine is alive and its heads stay \<open>\<ge> u\<close> down to level
  \<open>k-1\<close> (@{thm [source] b1x_GBT_trans} closes the chain).\<close>

lemma ox8_rsub_GBT:
  "\<lbrakk> 1 \<le> k; \<forall>j<k. ox8_rsub t j \<noteq> 0\<^sub>B \<and> u \<le> ox8_lastV (ox8_rsub t j) \<rbrakk>
     \<Longrightarrow> ox8_rsub t k \<in> GBT u t"
proof (induction k arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc k)
  have tne: "t \<noteq> 0\<^sub>B" and htv: "u \<le> ox8_lastV t" using Suc.prems(2) by force+
  have step: "ox8_lastT t \<in> GBT u t" by (rule ox8_lastT_GBT[OF tne htv])
  show ?case
  proof (cases "k = 0")
    case True
    have "ox8_rsub t (Suc 0) = ox8_lastT t" by simp
    thus ?thesis using step True by simp
  next
    case False
    hence k1: "1 \<le> k" by simp
    have prem: "\<forall>j<k. ox8_rsub (ox8_lastT t) j \<noteq> 0\<^sub>B
                       \<and> u \<le> ox8_lastV (ox8_rsub (ox8_lastT t) j)"
    proof (intro allI impI)
      fix j assume jk: "j < k"
      have sj: "Suc j < Suc k" using jk by simp
      have H: "ox8_rsub t (Suc j) \<noteq> 0\<^sub>B \<and> u \<le> ox8_lastV (ox8_rsub t (Suc j))"
        using Suc.prems(2) sj by blast
      show "ox8_rsub (ox8_lastT t) j \<noteq> 0\<^sub>B
             \<and> u \<le> ox8_lastV (ox8_rsub (ox8_lastT t) j)"
        using H by simp
    qed
    have IH: "ox8_rsub (ox8_lastT t) k \<in> GBT u (ox8_lastT t)"
      by (rule Suc.IH[OF k1 prem])
    have sub: "GBT u (ox8_lastT t) \<subseteq> GBT u t" by (rule b1x_GBT_trans[OF step])
    have "ox8_rsub t (Suc k) = ox8_rsub (ox8_lastT t) k" by simp
    thus ?thesis using IH sub by auto
  qed
qed

subsection \<open>(2) The \<open>G\<close>-descent: an \<open>OT\<close> principal bounds its whole right spine\<close>

text \<open>@{text ox8_rsub_lessBT_of_OTP}: THE descent engine.  If \<open>D\<^sub>u t\<close> is an \<open>OT\<close>
  principal (clause (OT2): \<open>G\<^sub>u t < t\<close>) and \<open>u\<close> is below every right-spine head
  of \<open>t\<close> down to level \<open>k-1\<close>, then the \<open>k\<close>-th right-spine sub-body of \<open>t\<close> is
  \<^emph>\<open>strictly below \<open>t\<close> itself\<close>.  This is the ONLY source of the census
  spine-descent: STEP-0 shows the head word genuinely increases along the spine
  (so no monotone/step-wise argument can work), and the stepwise chain
  \<open>Y\<^sub>k < Y\<^bsub>k-1\<^esub>\<close> is FALSE (2274/11306) — but the \<^emph>\<open>direct\<close> bound against the
  whole term holds always, and this lemma is why.\<close>

lemma ox8_rsub_lessBT_of_OTP:
  assumes otp: "isOT_BP (DB u t)"
    and kge: "1 \<le> k"
    and alive: "\<forall>j<k. ox8_rsub t j \<noteq> 0\<^sub>B \<and> u \<le> ox8_lastV (ox8_rsub t j)"
  shows "lessBT (ox8_rsub t k) t"
proof -
  have G: "\<forall>x \<in> GBT u t. lessBT x t" using otp by simp
  have mem: "ox8_rsub t k \<in> GBT u t" by (rule ox8_rsub_GBT[OF kge alive])
  show ?thesis using G mem by blast
qed

subsection \<open>(3) \<open>RightNodes\<close> reads exactly the \<open>ox8_rsub\<close> chain\<close>

lemma ox8_RightNodes_cons:
  assumes ne: "t \<noteq> 0\<^sub>B"
  shows "RightNodes t = the_enat (ox8_lastV t) # RightNodes (ox8_lastT t)"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using ne tps by auto
  obtain v b where lp: "last ps = DB v b" by (cases "last ps")
  have R: "RightNodes (Trm ps) = the_enat v # RightNodes b"
  proof (cases ps)
    case Nil thus ?thesis using psne by simp
  next
    case (Cons p qs)
    have "RightNodes (Trm (p # qs))
            = (case last (p # qs) of DB u a \<Rightarrow> the_enat u # RightNodes a)" by simp
    thus ?thesis using Cons lp by simp
  qed
  have hv: "ox8_lastV t = v" using tps psne lp by simp
  have ht: "ox8_lastT t = b" using tps psne lp by simp
  show ?thesis using R tps hv ht by simp
qed

lemma ox8_rsub_head_RN:
  "\<lbrakk> \<forall>j\<le>k. ox8_rsub t j \<noteq> 0\<^sub>B \<rbrakk>
     \<Longrightarrow> the_enat (ox8_lastV (ox8_rsub t k)) \<in> set (RightNodes t)"
proof (induction k arbitrary: t)
  case 0
  have tne: "t \<noteq> 0\<^sub>B" using 0 by force
  have "RightNodes t = the_enat (ox8_lastV t) # RightNodes (ox8_lastT t)"
    by (rule ox8_RightNodes_cons[OF tne])
  thus ?case by simp
next
  case (Suc k)
  have tne: "t \<noteq> 0\<^sub>B" using Suc.prems by force
  have prem: "\<forall>j\<le>k. ox8_rsub (ox8_lastT t) j \<noteq> 0\<^sub>B"
  proof (intro allI impI)
    fix j assume "j \<le> k"
    hence sj: "Suc j \<le> Suc k" by simp
    have H: "ox8_rsub t (Suc j) \<noteq> 0\<^sub>B" using Suc.prems sj by blast
    show "ox8_rsub (ox8_lastT t) j \<noteq> 0\<^sub>B" using H by simp
  qed
  have IH: "the_enat (ox8_lastV (ox8_rsub (ox8_lastT t) k))
              \<in> set (RightNodes (ox8_lastT t))" by (rule Suc.IH[OF prem])
  have "RightNodes t = the_enat (ox8_lastV t) # RightNodes (ox8_lastT t)"
    by (rule ox8_RightNodes_cons[OF tne])
  thus ?case using IH by simp
qed

subsection \<open>(4) \<open>d\<close>-freeness along the spine\<close>

lemma ox8_dfree_lastT: "dfree_BT t \<Longrightarrow> dfree_BT (ox8_lastT t)"
proof -
  assume df: "dfree_BT t"
  obtain ps where tps: "t = Trm ps" by (cases t)
  show ?thesis
  proof (cases "ps = []")
    case True thus ?thesis using tps by simp
  next
    case False
    obtain v b where lp: "last ps = DB v b" by (cases "last ps")
    have dfps: "\<forall>p \<in> set ps. dfree_BP p" using df tps by simp
    have mem: "DB v b \<in> set ps" using False lp by (metis last_in_set)
    have "dfree_BP (DB v b)" using dfps mem by blast
    hence "dfree_BT b" by simp
    thus ?thesis using tps False lp by simp
  qed
qed

lemma ox8_dfree_rsub: "dfree_BT t \<Longrightarrow> dfree_BT (ox8_rsub t k)"
proof (induction k arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc k)
  have "dfree_BT (ox8_lastT t)" by (rule ox8_dfree_lastT[OF Suc.prems])
  thus ?case using Suc.IH by simp
qed

lemma ox8_dfree_lastV:
  assumes df: "dfree_BT t" and ne: "t \<noteq> 0\<^sub>B"
  shows "ox8_lastV t \<noteq> \<infinity>"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using ne tps by auto
  obtain v b where lp: "last ps = DB v b" by (cases "last ps")
  have dfps: "\<forall>p \<in> set ps. dfree_BP p" using df tps by simp
  have mem: "DB v b \<in> set ps" using psne lp by (metis last_in_set)
  have "dfree_BP (DB v b)" using dfps mem by blast
  hence "v \<noteq> \<infinity>" by simp
  thus ?thesis using tps psne lp by simp
qed

subsection \<open>(5) Census: \<open>D\<^bsub>e\<^sub>3\<^esub>(body)\<close> is an \<open>OT\<close> principal\<close>

text \<open>@{text ox8_OTP_e3_body}: the kind-1 scb block \<open>k\<^sub>1\<close> of
  @{thm [source] oi5_IIIIV_pkg} says \<open>flat (Trans M) = s\<^sub>1 \<frown> flat (D\<^bsub>e\<^sub>3\<^esub> body) \<frown> b\<^sub>1\<close>
  with \<open>b\<^sub>1\<close> all-\<open>RP\<close>, i.e. \<open>D\<^bsub>e\<^sub>3\<^esub>(body)\<close> is a genuine right-spine component of
  \<open>Trans M \<in> OT\<^bsub>B\<^esub>\<close>.  \<open>OT\<close>-heredity at scb positions
  (@{thm [source] m_8_7_OT_scb_recursive}) hands us the \<open>OT\<close> principal, hence
  Buchholz's (OT2) condition \<open>G\<^bsub>e\<^sub>3\<^esub>(body) < body\<close>.\<close>

lemma ox8_OTP_e3_body:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
    and ihOT: "Trans M \<in> OT_B"
    and ltJ: "s84x_jm3 M < transJm1 M"
  shows "isOT_BP (DB (enat (entry M 1 (s84x_jm3 M)))
                     (bpHeadT (Trans (s84x_N M))))"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  obtain s0 b0 s1 b1 where
    k1: "scb_kind1 (Trans M) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    by (rule oi5_IIIIV_pkg[OF MST MPT hp j1gt branch ltJ])
  have scb: "scb_decomp (Trans M) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    using k1 by (simp add: scb_kind1_def)
  have bodyTB: "?body \<in> T_B" by (rule oi5_regime(3)[OF MST MPT hp j1gt branch])
  have cTB: "Dpt (enat ?e3) ?body \<in> T_B" using bodyTB by (simp add: T_B_def)
  have "Dpt (enat ?e3) ?body \<in> OT"
    by (rule m_8_7_OT_scb_recursive[OF ihOT cTB scb])
  thus ?thesis by (simp add: OT_def)
qed

subsection \<open>(6) CENSUS KEYSTONE: every right-spine sub-body of \<open>body\<close> is
  \<open>< body\<close> (the self-maximality of the spine)\<close>

text \<open>@{text ox8_body_rspine_lessBT}: the census form of the descent.  \<open>e\<^sub>3 < v\<^sub>1\<close>
  (@{thm [source] oi5_regime}(1)) and every right-spine head of \<open>body\<close> is \<open>\<ge> v\<^sub>1\<close>
  (@{thm [source] ox7_RightNodes_body_ge_v1}), so \<open>e\<^sub>3\<close> is below the WHOLE right
  spine; @{thm [source] ox8_rsub_lessBT_of_OTP} then bounds every right-spine
  sub-body by \<open>body\<close>.  This is the fact STEP-0 measures (11306/11306) and the
  ONLY available source of it (the spine head word is NOT monotone, and the
  stepwise descent is false).\<close>

theorem ox8_body_rspine_lessBT:
  fixes M :: pairseq and k :: nat
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
    and ihOT: "Trans M \<in> OT_B"
    and ltJ: "s84x_jm3 M < transJm1 M"
    and kge: "1 \<le> k"
    and alive: "\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N M))) j \<noteq> 0\<^sub>B"
  shows "lessBT (ox8_rsub (bpHeadT (Trans (s84x_N M))) k)
                (bpHeadT (Trans (s84x_N M)))"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  have otp: "isOT_BP (DB (enat ?e3) ?body)"
    by (rule ox8_OTP_e3_body[OF MST MPT hp j1gt branch ihOT ltJ])
  have e3lt: "?e3 < ?v1" by (rule oi5_regime(1)[OF MST MPT hp j1gt branch])
  have RNge: "\<forall>x \<in> set (RightNodes ?body). ?v1 \<le> x"
    by (rule ox7_RightNodes_body_ge_v1[OF MST MPT hp j1gt branch ltJ])
  have bodyTB: "?body \<in> T_B" by (rule oi5_regime(3)[OF MST MPT hp j1gt branch])
  have dfb: "dfree_BT ?body" using bodyTB by (simp add: T_B_def)
  have alive': "\<forall>j<k. ox8_rsub ?body j \<noteq> 0\<^sub>B
                      \<and> enat ?e3 \<le> ox8_lastV (ox8_rsub ?body j)"
  proof (intro allI impI)
    fix j assume jk: "j < k"
    have ne: "ox8_rsub ?body j \<noteq> 0\<^sub>B" using alive jk by simp
    have prem: "\<forall>i\<le>j. ox8_rsub ?body i \<noteq> 0\<^sub>B"
    proof (intro allI impI)
      fix i assume "i \<le> j"
      hence "i < k" using jk by simp
      thus "ox8_rsub ?body i \<noteq> 0\<^sub>B" using alive by simp
    qed
    have mem: "the_enat (ox8_lastV (ox8_rsub ?body j)) \<in> set (RightNodes ?body)"
      by (rule ox8_rsub_head_RN[OF prem])
    have ge: "?v1 \<le> the_enat (ox8_lastV (ox8_rsub ?body j))" using RNge mem by blast
    have dfj: "dfree_BT (ox8_rsub ?body j)" by (rule ox8_dfree_rsub[OF dfb])
    have fin: "ox8_lastV (ox8_rsub ?body j) \<noteq> \<infinity>" by (rule ox8_dfree_lastV[OF dfj ne])
    obtain i where vi: "ox8_lastV (ox8_rsub ?body j) = enat i"
      using fin by (cases "ox8_lastV (ox8_rsub ?body j)") auto
    have "?v1 \<le> i" using ge vi by simp
    hence "?e3 \<le> i" using e3lt by simp
    hence "enat ?e3 \<le> ox8_lastV (ox8_rsub ?body j)" using vi by simp
    thus "ox8_rsub ?body j \<noteq> 0\<^sub>B \<and> enat ?e3 \<le> ox8_lastV (ox8_rsub ?body j)"
      using ne by simp
  qed
  show ?thesis by (rule ox8_rsub_lessBT_of_OTP[OF otp kge alive'])
qed

subsection \<open>(7) STATUS — the EXACT residual after r68: the surgery TRANSPORT\<close>

text \<open>
  \<^bold>\<open>What is now proven (unconditionally).\<close>  @{thm [source] ox8_body_rspine_lessBT}:
  for the census host \<open>M\<close> (\<open>ST_PS\<close>, \<open>PT_PS\<close>, \<open>hasParent\<close>, \<open>1 < Lng M - 1\<close>,
  \<open>condIII \<or> condIV\<close>, \<open>Trans M \<in> OT\<^bsub>B\<^esub>\<close>, \<open>ltJ\<close>) EVERY right-spine sub-body of
  \<open>body = bpHeadT (Trans (s84x_N M))\<close> is \<^emph>\<open>strictly below \<open>body\<close>\<close>.  This is the
  \<^bold>\<open>self-maximality\<close> of the census spine — the fact the SETLE1 descent needs, and
  (per STEP-0) the only true one: the spine head word is NOT monotone (3379
  strict drops among 11306 levels), and the stepwise chain
  \<open>Y\<^sub>k < Y\<^bsub>k-1\<^esub>\<close> is FALSE (2274/11306), so nothing weaker than the direct
  \<open>G\<close>-condition bound can produce it.

  \<^bold>\<open>The one remaining gap: the surgery TRANSPORT.\<close>  The census \<open>spineH\<close>
  (@{thm [source] ox6_SETLE1_reduce_restr}) compares the peel bodies of the
  \<^emph>\<open>surgered\<close> trees: with \<open>X\<^sub>0 = D\<^bsub>ub\<^esub>0\<close>, \<open>X\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 X\<^sub>0\<close>,
  \<open>A\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 A\<^sub>0\<close>, it needs
  \[ \<open>leBT (ox8_rsub A\<^sub>1 k) X\<^sub>1\<close> \qquad (k \<ge> 1), \]
  whereas the \<open>G\<close>-descent gives the \<^emph>\<open>leaf\<close>-version
  \<open>lessBT (ox8_rsub body k) body\<close>.  \<open>X\<^sub>1\<close> / \<open>A\<^sub>1\<close> are \<open>body\<close> with its deepest-right
  LEAF principal \<open>D\<^bsub>v\<^sub>1\<^esub>0\<close> replaced by \<open>D\<^bsub>ub\<^esub>X\<^sub>0\<close> / \<open>D\<^bsub>ub\<^esub>A\<^sub>0\<close> (\<open>ub = v\<^sub>1 - 1 < v\<^sub>1\<close>),
  and the peel keeps the two sides aligned: at every align3 level the three
  trees share \<open>(qs, w, sc, bc)\<close> (@{thm [source] ox7_align3_track}), so the peel
  bodies are \<open>lbB = ox8_rsub body k\<close>, \<open>lbX = ox8_rsub X\<^sub>1 k\<close>, \<open>lbA = ox8_rsub A\<^sub>1 k\<close>
  with the SAME context.  The needed lemma is therefore exactly

  \<^bold>\<open>TRANSPORT\<close>: \<open>flatBT WB = s \<frown> flat (D\<^bsub>v\<^sub>1\<^esub>0) \<frown> b\<close>, \<open>flatBT WX = s \<frown> flat (D\<^bsub>ub\<^esub>X\<^sub>0) \<frown> b\<close>,
  \<open>flatBT tB = sc \<frown> flat (D\<^bsub>v\<^sub>1\<^esub>0) \<frown> bc\<close>, \<open>flatBT tA = sc \<frown> flat (D\<^bsub>ub\<^esub>A\<^sub>0) \<frown> bc\<close>,
  \<open>b, bc\<close> all-\<open>RP\<close>, \<open>s = pre \<frown> sc\<close> with \<open>pre \<noteq> []\<close>, \<open>ub < v\<^sub>1\<close>, and
  \<open>lessBT tB WB\<close>  \<Longrightarrow>  \<open>lessBT tA WX\<close>.

  STEP-0 validates TRANSPORT as verdict-INVARIANCE (11306/11306: the verdict of
  \<open>lessBT (level-k body with hole content \<open>Q\<close>) X\<^sub>1\<close> is the same for
  \<open>Q \<in> {0, X\<^sub>0, A\<^sub>0, BIG}\<close>), i.e. the first difference lies strictly ABOVE the hole
  body.  Its proof is a lock-step first-difference induction: the surgery only
  ever touches the LAST principal of each right-spine level
  (@{thm [source] scb_to_last_component}), while the \<open>lessBT\<close> recursion walks the
  principal lists from the LEFT, so at every position either (i) the compared
  principals are hole-free — hence literally identical in the leaf- and the
  surgered version, and the verdict transports verbatim; or (ii) the compared
  principal is the hole-carrying last one, where the surgery is a strict
  DECREASE (\<open>D\<^bsub>ub\<^esub>Q < D\<^bsub>v\<^sub>1\<^esub>0\<close> by \<open>ub < v\<^sub>1\<close>, @{thm [source] scbext_lessBT}), so a
  verdict \<open>'<'\<close> on the left is preserved and an EQUALITY on the left becomes a
  strict \<open>'<'\<close> — the same verdict as the leaf version's prefix rule.

  \<^bold>\<open>The one case that needs a census input\<close> (and hence the exact Isar
  obstruction).  The dangerous branch of (ii) is when the comparison reaches the
  hole-carrying last principal of the RIGHT operand (\<open>WX\<close>) while the left operand
  (\<open>tA\<close>) still offers a hole-FREE principal at that index — there the surgery
  \<^emph>\<open>lowers the right side\<close> and a leaf-version \<open>'<'\<close> could flip.  This requires
  \<open>|principal list of tA| > |principal list of WX|\<close> at a common peel depth.  STEP-0
  shows it never happens on real census hosts, because EVERY right-spine level of
  \<open>X\<^sub>1\<close> above the hole is a \<^bold>\<open>pure chain\<close> (a single principal; 11306/11306), so the
  right operand's list has length 1 and the comparison at index 0 is exactly the
  hole-carrying principal on both sides.  The missing brick is therefore either
  (a) the chain-ness of the census spine — \<open>ox8_lastT\<close>-levels of \<open>body\<close> above the
  hole have a single principal (a \<open>Trans\<close>-image geometry fact), or (b) a
  head-hypothesis strong enough to rule the flip out
  (\<open>bpHeadV\<close> of the left operand's index-\<open>|QS|\<close> principal \<open>< W\<close>, which for the
  hole level follows from \<open>descP\<close> + \<open>ub < v\<^sub>1 \<le> W\<close> only when that principal is the
  hole itself).  Everything else in TRANSPORT is elementary
  (@{thm [source] scbext_lessBT}, @{thm [source] ox7_align3_track},
  @{thm [source] ox7_headlt_lessBT}).

  \<^bold>\<open>Assembly once TRANSPORT lands\<close>: TRANSPORT + @{thm [source] ox8_body_rspine_lessBT}
  give \<open>spineH\<close> of @{thm [source] ox6_SETLE1_reduce_restr} (the \<open>tx' \<in> G\<^sub>u X\<^sub>1\<close>
  witness is not even needed — the align3-track suffix relation \<open>s\<^sub>0 = pre \<frown> sc\<close>,
  \<open>pre \<noteq> []\<close>, is what the engine really supplies), hence the census
  \<open>SETLE1_ltJ\<close> slot of @{thm [source] oi8_census_final_ivadmeq}, leaving
  \<open>{FINRC}\<close> only.
\<close>

(* ===== end r68 ox8 block (part 1: the G-descent source; residual = TRANSPORT) ===== *)


(* =====================================================================
   r68 bwl block.  Prefix  bwl_  ([Buc1] \<section>2 with the CORRECT semantics for
   \<open>W\<^sub>v\<close>: the LEAST FIXPOINT of the accessibility operator \<open>A\<^sub>v\<close>).
   ===================================================================== *)

text \<open>\<^bold>\<open>Why this block exists.\<close>  Round 66 transcribed [Buc1] \<section>2 but defined the
  level sets by \<^emph>\<open>accessibility\<close>, \<open>bwo_Wlev u = {z. D\<^sub>u z \<in> acc RPrel}\<close>.  With that
  reading Buchholz's leastness principle

    (A2)  \<open>A\<^sub>u(Y) \<subseteq> Y \<Longrightarrow> W\<^sub>u \<subseteq> Y\<close>

  is NOT free — it becomes a cofinality statement about fundamental sequences —
  and round 67 had to carry it as an explicit hypothesis of
  @{thm [source] bwo_2_5_sub1}.  But in [1] p.137 \<open>W\<^sub>v\<close> is by DEFINITION the
  \<^bold>\<open>iterated inductive definition\<close> generated by

    (W1) \<open>0 \<in> W\<^sub>v\<close>;
    (W2) \<open>dom(a) \<in> {{0}, \<nat>}\<close>, \<open>\<forall>n. a[n] \<in> W\<^sub>v\<close> \<Longrightarrow> \<open>a \<in> W\<^sub>v\<close>;
    (W3) \<open>dom(a) = T\<^sub>u\<close> with \<open>u < v\<close>, \<open>\<forall>z \<in> W\<^sub>u. a[z] \<in> W\<^sub>v\<close> \<Longrightarrow> \<open>a \<in> W\<^sub>v\<close>

  i.e. \<open>W\<^sub>v = lfp (A\<^sub>v)\<close> where the LOWER levels \<open>W\<^sub>u\<close> \<open>(u < v)\<close> occur as
  \<^emph>\<open>parameters\<close> (this is exactly why it is an ITERATED inductive definition: the
  occurrence of \<open>W\<^sub>u\<close> in (W3) is not monotone in the set being generated, so the
  whole family cannot be produced by a single \<open>lfp\<close>).  With that definition
  (A1) and (A2) are the fixpoint equation and the induction rule of the
  \<open>lfp\<close> — FREE.  We rebuild the \<section>2 machinery on that basis.\<close>

subsection \<open>(1) The operator \<open>A\<^sub>\<nu>\<close>, parametrised by the lower-level family\<close>

text \<open>[1] p.138(1)(2), with the lower levels supplied as a parameter \<open>Wf\<close>.\<close>

definition bwl_Aop :: "(nat \<Rightarrow> BT set) \<Rightarrow> enat \<Rightarrow> BT set \<Rightarrow> BT \<Rightarrow> bool" where
  "bwl_Aop Wf nv X a \<longleftrightarrow>
     a = Trm [] \<or>
     ((domB a = {Trm []} \<or> domB a = NatSet) \<and> (\<forall>n. operB a (numBT n) \<in> X)) \<or>
     (\<exists>u. enat u < nv \<and> domB a = TBv (enat u) \<and> (\<forall>z \<in> Wf u. operB a z \<in> X))"

definition bwl_Aset :: "(nat \<Rightarrow> BT set) \<Rightarrow> enat \<Rightarrow> BT set \<Rightarrow> BT set" where
  "bwl_Aset Wf nv X = {a. bwl_Aop Wf nv X a}"

lemma bwl_Aop_mono_X:
  assumes "bwl_Aop Wf nv X a" and "X \<subseteq> Y"
  shows "bwl_Aop Wf nv Y a"
  using assms unfolding bwl_Aop_def by blast

lemma bwl_Aset_mono: "mono (bwl_Aset Wf nv)"
proof (rule monoI)
  fix X Y :: "BT set" assume XY: "X \<subseteq> Y"
  show "bwl_Aset Wf nv X \<subseteq> bwl_Aset Wf nv Y"
    unfolding bwl_Aset_def using XY by (blast intro: bwl_Aop_mono_X)
qed

text \<open>Level monotonicity of the operator itself ([1] uses \<open>A\<^sub>u(X) \<subseteq> A\<^sub>\<nu>(X)\<close> for
  \<open>u \<le> \<nu>\<close> in the proof of 2.5(1)).\<close>

lemma bwl_Aop_mono_nv:
  assumes le: "nv \<le> nv'" and a: "bwl_Aop Wf nv X a"
  shows "bwl_Aop Wf nv' X a"
  using a le unfolding bwl_Aop_def by (blast intro: less_le_trans)

text \<open>\<open>A\<^sub>\<nu>\<close> only reads the levels \<open>u < \<nu>\<close> of its family parameter.\<close>

lemma bwl_Aop_cong:
  assumes W: "\<And>u. enat u < nv \<Longrightarrow> Wf u = Wg u"
  shows "bwl_Aop Wf nv X a = bwl_Aop Wg nv X a"
proof -
  have "\<And>u. enat u < nv \<Longrightarrow>
          (\<forall>z \<in> Wf u. operB a z \<in> X) = (\<forall>z \<in> Wg u. operB a z \<in> X)"
    using W by simp
  hence "(\<exists>u. enat u < nv \<and> domB a = TBv (enat u) \<and> (\<forall>z \<in> Wf u. operB a z \<in> X))
       = (\<exists>u. enat u < nv \<and> domB a = TBv (enat u) \<and> (\<forall>z \<in> Wg u. operB a z \<in> X))"
    by blast
  thus ?thesis unfolding bwl_Aop_def by blast
qed

subsection \<open>(2) The iterated inductive definition \<open>W\<^sub>v = lfp A\<^sub>v\<close>\<close>

text \<open>\<open>bwl_Wf n\<close> is the family of levels \<^emph>\<open>below\<close> \<open>n\<close> (levels \<open>\<ge> n\<close> are junk \<open>{}\<close>);
  each stage is an honest \<open>lfp\<close> of the (monotone) operator built from the
  previously-defined stages.\<close>

primrec bwl_Wf :: "nat \<Rightarrow> nat \<Rightarrow> BT set" where
  "bwl_Wf 0 = (\<lambda>u. {})"
| "bwl_Wf (Suc v) =
     (\<lambda>u. if u = v then lfp (bwl_Aset (bwl_Wf v) (enat v)) else bwl_Wf v u)"

definition bwl_W :: "nat \<Rightarrow> BT set" where
  "bwl_W u = bwl_Wf (Suc u) u"

lemma bwl_Wf_coh: "u < n \<Longrightarrow> bwl_Wf n u = bwl_Wf (Suc u) u"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc v)
  show ?case
  proof (cases "u = v")
    case True thus ?thesis by simp
  next
    case False
    hence ulv: "u < v" using Suc.prems by simp
    have "bwl_Wf (Suc v) u = bwl_Wf v u" using False by simp
    also have "\<dots> = bwl_Wf (Suc u) u" using Suc.IH[OF ulv] .
    finally show ?thesis .
  qed
qed

lemma bwl_Wf_eq_W: "u < n \<Longrightarrow> bwl_Wf n u = bwl_W u"
  unfolding bwl_W_def by (rule bwl_Wf_coh)

text \<open>The defining equation: \<open>W\<^sub>v\<close> IS the least fixpoint of \<open>A\<^sub>v\<close> over the family
  \<open>W\<close> itself (the stage-truncation is invisible because \<open>A\<^sub>v\<close> only reads \<open>u < v\<close>).\<close>

lemma bwl_W_unfold: "bwl_W v = lfp (bwl_Aset bwl_W (enat v))"
proof -
  have stage: "bwl_W v = lfp (bwl_Aset (bwl_Wf v) (enat v))"
    unfolding bwl_W_def by simp
  have cong: "bwl_Wf v u = bwl_W u" if "enat u < enat v" for u
  proof -
    have "u < v" using that by simp
    thus ?thesis by (rule bwl_Wf_eq_W)
  qed
  have ptw: "bwl_Aset (bwl_Wf v) (enat v) X = bwl_Aset bwl_W (enat v) X" for X
  proof (rule set_eqI)
    fix a
    show "(a \<in> bwl_Aset (bwl_Wf v) (enat v) X) = (a \<in> bwl_Aset bwl_W (enat v) X)"
      unfolding bwl_Aset_def mem_Collect_eq
      by (rule bwl_Aop_cong[where Wf = "bwl_Wf v" and Wg = bwl_W and nv = "enat v",
                            OF cong])
  qed
  have "bwl_Aset (bwl_Wf v) (enat v) = bwl_Aset bwl_W (enat v)"
    using ptw by (rule ext)
  thus ?thesis using stage by simp
qed

text \<open>\<^bold>\<open>(A1)\<close> [1] p.138: \<open>A\<^sub>v(W\<^sub>v) = W\<^sub>v\<close> — the fixpoint equation, FREE.\<close>

lemma bwl_A1: "bwl_Aset bwl_W (enat v) (bwl_W v) = bwl_W v"
  using lfp_unfold[OF bwl_Aset_mono, of bwl_W "enat v", symmetric]
  by (simp add: bwl_W_unfold)

text \<open>\<^bold>\<open>(A2)\<close> [1] p.138: \<open>A\<^sub>v(Y) \<subseteq> Y \<Longrightarrow> W\<^sub>v \<subseteq> Y\<close> — the induction rule, FREE.
  This is the hypothesis that round 67 had to assume.\<close>

lemma bwl_A2:
  assumes A: "bwl_Aset bwl_W (enat v) Y \<subseteq> Y"
  shows "bwl_W v \<subseteq> Y"
proof -
  have "lfp (bwl_Aset bwl_W (enat v)) \<subseteq> Y"
    by (rule lfp_lowerbound[of "bwl_Aset bwl_W (enat v)" Y, OF A])
  thus ?thesis by (simp add: bwl_W_unfold)
qed

text \<open>Practical (pointwise) forms of (A1)/(A2).\<close>

lemma bwl_A1_intro:
  assumes "bwl_Aop bwl_W (enat v) (bwl_W v) a"
  shows "a \<in> bwl_W v"
proof -
  have "a \<in> bwl_Aset bwl_W (enat v) (bwl_W v)"
    using assms unfolding bwl_Aset_def by simp
  thus ?thesis using bwl_A1 by simp
qed

lemma bwl_A1_dest:
  assumes "a \<in> bwl_W v"
  shows "bwl_Aop bwl_W (enat v) (bwl_W v) a"
proof -
  have "a \<in> bwl_Aset bwl_W (enat v) (bwl_W v)" using assms bwl_A1 by simp
  thus ?thesis unfolding bwl_Aset_def by simp
qed

lemma bwl_A2':
  assumes Y: "\<And>c. bwl_Aop bwl_W (enat v) Y c \<Longrightarrow> c \<in> Y"
  shows "bwl_W v \<subseteq> Y"
proof (rule bwl_A2, rule subsetI)
  fix x assume "x \<in> bwl_Aset bwl_W (enat v) Y"
  hence "bwl_Aop bwl_W (enat v) Y x" unfolding bwl_Aset_def by simp
  thus "x \<in> Y" by (rule Y)
qed

text \<open>(W1): \<open>0 \<in> W\<^sub>v\<close>.\<close>

lemma bwl_W_zero: "Trm [] \<in> bwl_W v"
  by (rule bwl_A1_intro) (simp add: bwl_Aop_def)

text \<open>(W2)/(W3) as introduction rules.\<close>

lemma bwl_W2:
  assumes d: "domB a = {Trm []} \<or> domB a = NatSet"
    and op: "\<And>n. operB a (numBT n) \<in> bwl_W v"
  shows "a \<in> bwl_W v"
proof (rule bwl_A1_intro)
  show "bwl_Aop bwl_W (enat v) (bwl_W v) a"
    unfolding bwl_Aop_def using d op by blast
qed

lemma bwl_W3:
  assumes uv: "u < v" and d: "domB a = TBv (enat u)"
    and op: "\<And>z. z \<in> bwl_W u \<Longrightarrow> operB a z \<in> bwl_W v"
  shows "a \<in> bwl_W v"
proof (rule bwl_A1_intro)
  have lt: "enat u < enat v" using uv by simp
  have all: "\<forall>z \<in> bwl_W u. operB a z \<in> bwl_W v" using op by blast
  show "bwl_Aop bwl_W (enat v) (bwl_W v) a"
    unfolding bwl_Aop_def using lt d all by blast
qed

text \<open>[1] p.137 Proposition: \<open>u \<le> v \<Longrightarrow> W\<^sub>u \<subseteq> W\<^sub>v\<close>.  Free from (A1)+(A2)+level
  monotonicity of \<open>A\<close>.\<close>

lemma bwl_W_level_mono:
  assumes uv: "u \<le> v"
  shows "bwl_W u \<subseteq> bwl_W v"
proof (rule bwl_A2')
  fix c assume c: "bwl_Aop bwl_W (enat u) (bwl_W v) c"
  have le: "enat u \<le> enat v" using uv by simp
  have "bwl_Aop bwl_W (enat v) (bwl_W v) c" by (rule bwl_Aop_mono_nv[OF le c])
  thus "c \<in> bwl_W v" by (rule bwl_A1_intro)
qed

(* ===== end r68 bwl part 1 (lfp semantics: A1/A2/W1/W2/W3/level-mono FREE) ===== *)

subsection \<open>(3) [Buc1] Lemma 2.4 on the \<open>lfp\<close> semantics\<close>

text \<open>2.4(a) \<open>A\<^sub>\<nu>(X) \<subseteq> X\<close>, \<open>a \<in> X\<close> \<Longrightarrow> \<open>A\<^sub>\<nu>(X\<^bsup>(a)\<^esup>) \<subseteq> X\<^bsup>(a)\<^esup>\<close> — same proof as
  @{thm [source] bwo_2_4a_shift_closure}, but for the family-parametric \<open>bwl_Aop\<close>
  (the lower levels enter only as an opaque set, so the argument is unchanged).\<close>

lemma bwl_2_4a_shift:
  assumes Acl: "\<And>c. bwl_Aop Wf nv X c \<Longrightarrow> c \<in> X"
    and aX: "a \<in> X"
    and body: "bwl_Aop Wf nv (bwo_shift a X) b"
  shows "b \<in> bwo_shift a X"
proof -
  have goal: "a +\<^sub>B b \<in> X"
  proof -
    consider (zero) "b = Trm []"
      | (num) "(domB b = {Trm []} \<or> domB b = NatSet)
               \<and> (\<forall>n. operB b (numBT n) \<in> bwo_shift a X)"
      | (tu) u where "enat u < nv" "domB b = TBv (enat u)"
               "\<forall>z \<in> Wf u. operB b z \<in> bwo_shift a X"
      using body[unfolded bwl_Aop_def] by blast
    thus ?thesis
    proof cases
      case zero
      thus ?thesis using aX bwo_addBT_Nil_right by simp
    next
      case num
      have bne: "b \<noteq> Trm []"
      proof
        assume z: "b = Trm []"
        have dz: "domB b = {}" using z bwo_domB_Nil by simp
        have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
        moreover have "Trm [] \<in> {Trm []}" by simp
        ultimately show False using conjunct1[OF num] dz by auto
      qed
      have d: "domB (a +\<^sub>B b) = {Trm []} \<or> domB (a +\<^sub>B b) = NatSet"
        using conjunct1[OF num] bwo_addBT_domB[OF bne] by simp
      have op: "\<forall>n. operB (a +\<^sub>B b) (numBT n) \<in> X"
      proof (intro allI)
        fix n
        have "operB b (numBT n) \<in> bwo_shift a X" using conjunct2[OF num] by blast
        hence "a +\<^sub>B operB b (numBT n) \<in> X" by (simp add: bwo_shift_def)
        thus "operB (a +\<^sub>B b) (numBT n) \<in> X"
          using bwo_addBT_operB[OF bne] by simp
      qed
      have "bwl_Aop Wf nv X (a +\<^sub>B b)"
        using d op unfolding bwl_Aop_def by blast
      thus ?thesis by (rule Acl)
    next
      case (tu u)
      have bne: "b \<noteq> Trm []"
      proof
        assume z: "b = Trm []"
        have "TBv (enat u) = {}" using z tu(2) bwo_domB_Nil by simp
        moreover have "Trm [] \<in> TBv (enat u)" by (simp add: TBv_def)
        ultimately show False by simp
      qed
      have d: "domB (a +\<^sub>B b) = TBv (enat u)"
        using tu(2) bwo_addBT_domB[OF bne] by simp
      have op: "\<forall>z \<in> Wf u. operB (a +\<^sub>B b) z \<in> X"
      proof
        fix z assume zW: "z \<in> Wf u"
        have "operB b z \<in> bwo_shift a X" using tu(3) zW by blast
        hence "a +\<^sub>B operB b z \<in> X" by (simp add: bwo_shift_def)
        thus "operB (a +\<^sub>B b) z \<in> X"
          using bwo_addBT_operB[OF bne] by simp
      qed
      have "bwl_Aop Wf nv X (a +\<^sub>B b)"
        using tu(1) d op unfolding bwl_Aop_def by blast
      thus ?thesis by (rule Acl)
    qed
  qed
  show ?thesis using goal by (simp add: bwo_shift_def)
qed

text \<open>2.4(b) \<open>a, b \<in> W\<^sub>v \<Longrightarrow> a + b \<in> W\<^sub>v\<close>.  Buchholz derives it from 2.4(a)
  together with (A1) and (A2) — both of which are now FREE.  (This is the
  genuine [1] 2.4(b); the r66 alias \<open>bwo_2_4b_addition_closure\<close> pointed at the
  \<^emph>\<open>acc\<close>-side tuple lemma instead.)\<close>

lemma bwl_2_4b_add:
  assumes a: "a \<in> bwl_W v" and b: "b \<in> bwl_W v"
  shows "a +\<^sub>B b \<in> bwl_W v"
proof -
  have Acl: "\<And>c. bwl_Aop bwl_W (enat v) (bwl_W v) c \<Longrightarrow> c \<in> bwl_W v"
    by (rule bwl_A1_intro)
  have sh: "\<And>c. bwl_Aop bwl_W (enat v) (bwo_shift a (bwl_W v)) c
                 \<Longrightarrow> c \<in> bwo_shift a (bwl_W v)"
    by (rule bwl_2_4a_shift[OF Acl a])
  have "bwl_W v \<subseteq> bwo_shift a (bwl_W v)" by (rule bwl_A2'[OF sh])
  hence "b \<in> bwo_shift a (bwl_W v)" using b by blast
  thus ?thesis by (simp add: bwo_shift_def)
qed

text \<open>Iterated form \<open>a \<cdot> n \<in> W\<^sub>v\<close> (needed in [1] 2.6 case 3).\<close>

lemma bwl_2_4b_mult:
  assumes y: "y \<in> bwl_W v"
  shows "y *\<^sub>B n \<in> bwl_W v"
proof (induction n)
  case 0 show ?case by (simp add: bwl_W_zero)
next
  case (Suc n)
  show ?case using bwl_2_4b_add[OF Suc.IH y] by simp
qed

subsection \<open>(4) The numerals live in every \<open>W\<^sub>v\<close>\<close>

lemma bwl_domB_one: "domB (Trm [DB 0 (Trm [])]) = {Trm []}"
  by (subst domB_unfold) simp

lemma bwl_one_W: "Trm [DB 0 (Trm [])] \<in> bwl_W v"
proof (rule bwl_W2)
  show "domB (Trm [DB 0 (Trm [])]) = {Trm []}
        \<or> domB (Trm [DB 0 (Trm [])]) = NatSet"
    using bwl_domB_one by simp
next
  fix n show "operB (Trm [DB 0 (Trm [])]) (numBT n) \<in> bwl_W v"
    by (simp add: b1x_operB_D0 bwl_W_zero)
qed

lemma bwl_numBT_W: "numBT n \<in> bwl_W v"
  using bwl_2_4b_mult[OF bwl_one_W, of n v] by (simp add: numBT_def b1x_mult_single)

subsection \<open>(5) [Buc1] Lemma 2.5 sub-result (1) — now UNCONDITIONAL\<close>

text \<open>Round 67 had to assume (A2) here; on the \<open>lfp\<close> semantics it is
  @{thm [source] bwl_A2'}, so the lemma is unconditional.\<close>

lemma bwl_2_5_sub1:
  assumes Acl: "\<And>c. bwl_Aop bwl_W nv X c \<Longrightarrow> c \<in> X"
    and aX: "a \<in> X"
    and ult: "enat u < nv"
  shows "a +\<^sub>B Trm [DB (enat (Suc u)) (Trm [])] \<in> X"
proof -
  let ?D = "Trm [DB (enat (Suc u)) (Trm [])] :: BT"
  have Dne: "?D \<noteq> Trm []" by simp
  have domAD: "domB (a +\<^sub>B ?D) = TBv (enat u)"
    using bwo_addBT_domB[OF Dne] bwo_domB_Dsucc0 by simp
  have opAD: "\<And>z. operB (a +\<^sub>B ?D) z = a +\<^sub>B z"
  proof -
    fix z
    have "operB (a +\<^sub>B ?D) z = a +\<^sub>B operB ?D z" by (rule bwo_addBT_operB[OF Dne])
    also have "\<dots> = a +\<^sub>B z" using bwo_operB_Dsucc0 by simp
    finally show "operB (a +\<^sub>B ?D) z = a +\<^sub>B z" .
  qed
  have shiftAu: "\<And>c. bwl_Aop bwl_W (enat u) (bwo_shift a X) c
                      \<Longrightarrow> c \<in> bwo_shift a X"
  proof -
    fix c assume "bwl_Aop bwl_W (enat u) (bwo_shift a X) c"
    hence bnv: "bwl_Aop bwl_W nv (bwo_shift a X) c"
      by (rule bwl_Aop_mono_nv[OF less_imp_le[OF ult]])
    show "c \<in> bwo_shift a X" by (rule bwl_2_4a_shift[OF Acl aX bnv])
  qed
  have WsubShift: "bwl_W u \<subseteq> bwo_shift a X" by (rule bwl_A2'[OF shiftAu])
  have opX: "\<forall>z \<in> bwl_W u. operB (a +\<^sub>B ?D) z \<in> X"
  proof
    fix z assume "z \<in> bwl_W u"
    hence "z \<in> bwo_shift a X" using WsubShift by blast
    hence "a +\<^sub>B z \<in> X" by (simp add: bwo_shift_def)
    thus "operB (a +\<^sub>B ?D) z \<in> X" using opAD by simp
  qed
  have "bwl_Aop bwl_W nv X (a +\<^sub>B ?D)"
    using ult domAD opX unfolding bwl_Aop_def by blast
  thus ?thesis by (rule Acl)
qed

(* ===== end r68 bwl part 2 ([Buc1] 2.4(a),(b), numerals, 2.5(1) unconditional) ===== *)

subsection \<open>(6) Shape lemmas for the principal \<open>D\<^sub>w c\<close> (guards of \<open>operB\<close>/\<open>domB\<close>)\<close>

lemma bwl_domB_case_i:
  assumes "b \<noteq> Trm []" and "domB b = {Trm []}"
  shows "domB (Trm [DB v b]) = NatSet"
  using assms by (subst domB_unfold) (simp add: Let_def)

lemma bwl_TBv_neq_zero: "TBv (enat m) \<noteq> {Trm []}"
proof
  assume H: "TBv (enat m) = {Trm []}"
  have "Trm [DB 0 (Trm [])] \<in> TBv (enat m)" by (simp add: TBv_def)
  hence "Trm [DB 0 (Trm [])] \<in> {Trm []}" using H by simp
  thus False by simp
qed

text \<open>If \<open>dom(c) = T\<^sub>m\<close> with \<open>m < w\<close> then the \<open>xseq\<close>-branch ([].4)(ii) of \<open>D\<^sub>w c\<close> is
  \<^emph>\<open>not\<close> taken, so ([].4)(iii) applies: \<open>dom(D\<^sub>w c) = dom(c)\<close>, \<open>(D\<^sub>w c)[z] = D\<^sub>w(c[z])\<close>.\<close>

lemma bwl_case_iii_guard_TBv:
  assumes mw: "m < w"
  shows "\<not> (\<exists>u. enat w \<le> enat u \<and> TBv (enat m) = TBv (enat u))"
proof
  assume "\<exists>u. enat w \<le> enat u \<and> TBv (enat m) = TBv (enat u)"
  then obtain u where wu: "enat w \<le> enat u" and eq: "TBv (enat m) = TBv (enat u)"
    by blast
  have "m = u" using eq by (rule TBv_enat_inj)
  thus False using wu mw by simp
qed

text \<open>\<open>D\<^sub>w 0 \<in> W\<^sub>w\<close>: for \<open>w = 0\<close> it is the numeral \<open>1\<close>; for \<open>w = s+1\<close> it is (W3) with
  \<open>dom(D\<^bsub>s+1\<^esub>0) = T\<^sub>s\<close>, \<open>(D\<^bsub>s+1\<^esub>0)[z] = z\<close> and the level monotonicity \<open>W\<^sub>s \<subseteq> W\<^sub>w\<close>.\<close>

lemma bwl_D_zero_W: "Trm [DB (enat w) (Trm [])] \<in> bwl_W w"
proof (cases w)
  case 0
  have z: "enat 0 = (0 :: enat)" by (simp add: zero_enat_def)
  show ?thesis using bwl_one_W[of 0] z 0 by simp
next
  case (Suc s)
  show ?thesis
  proof (rule bwl_W3[where u = s])
    show "s < w" using Suc by simp
    show "domB (Trm [DB (enat w) (Trm [])]) = TBv (enat s)"
      using Suc bwo_domB_Dsucc0[of s] by simp
  next
    fix z assume "z \<in> bwl_W s"
    hence zw: "z \<in> bwl_W w" using bwl_W_level_mono[of s w] Suc by auto
    show "operB (Trm [DB (enat w) (Trm [])]) z \<in> bwl_W w"
      using Suc bwo_operB_Dsucc0[of s z] zw by simp
  qed
qed

subsection \<open>(7) The collapsing closure: \<open>u \<le> w \<Longrightarrow> x \<in> W\<^sub>u \<Longrightarrow> D\<^sub>w x \<in> W\<^sub>w\<close>\<close>

text \<open>\<^bold>\<open>This is the first real dividend of the \<open>lfp\<close> semantics.\<close>  It is proved by the
  (now free) induction rule (A2) at level \<open>u\<close>, applied to the set
  \<open>Y := {x. D\<^sub>w x \<in> W\<^sub>w}\<close>: one shows \<open>A\<^sub>u(Y) \<subseteq> Y\<close> by the three \<open>A\<close>-clauses, using the
  three \<open>D\<^sub>w\<close>-shape branches ([].4)(i)/(iii) of \<open>dom\<close>/\<open>[\<cdot>]\<close> — the \<open>xseq\<close>-branch
  ([].4)(ii) never fires because every level \<open>m\<close> occurring in an \<open>A\<^sub>u\<close>-clause
  satisfies \<open>m < u \<le> w\<close>.  Buchholz uses instances of this inside 2.6.\<close>

lemma bwl_key_collapse_sub:
  assumes uw: "u \<le> w"
  shows "bwl_W u \<subseteq> {x. Trm [DB (enat w) x] \<in> bwl_W w}"
proof (rule bwl_A2')
  fix c assume A: "bwl_Aop bwl_W (enat u) {x. Trm [DB (enat w) x] \<in> bwl_W w} c"
  let ?Y = "{x. Trm [DB (enat w) x] \<in> bwl_W w}"
  consider (zero) "c = Trm []"
    | (num) "(domB c = {Trm []} \<or> domB c = NatSet) \<and> (\<forall>n. operB c (numBT n) \<in> ?Y)"
    | (tu) m where "enat m < enat u" "domB c = TBv (enat m)"
             "\<forall>z \<in> bwl_W m. operB c z \<in> ?Y"
    using A[unfolded bwl_Aop_def] by blast
  then have main: "Trm [DB (enat w) c] \<in> bwl_W w"
  proof cases
    case zero
    thus ?thesis using bwl_D_zero_W by simp
  next
    case num
    have cne: "c \<noteq> Trm []"
    proof
      assume z: "c = Trm []"
      have dz: "domB c = {}" using z bwo_domB_Nil by simp
      have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
      moreover have "Trm [] \<in> {Trm []}" by simp
      ultimately show False using conjunct1[OF num] dz by auto
    qed
    show ?thesis
    proof (cases "domB c = {Trm []}")
      case True
      have dW: "domB (Trm [DB (enat w) c]) = NatSet"
        by (rule bwl_domB_case_i[OF cne True])
      have base: "Trm [DB (enat w) (operB c (Trm []))] \<in> bwl_W w"
      proof -
        have "operB c (numBT 0) \<in> ?Y" using num by blast
        moreover have "numBT 0 = Trm []" by (simp add: numBT_def)
        ultimately show ?thesis by simp
      qed
      show ?thesis
      proof (rule bwl_W2)
        show "domB (Trm [DB (enat w) c]) = {Trm []}
              \<or> domB (Trm [DB (enat w) c]) = NatSet" using dW by simp
      next
        fix n
        have eq: "operB (Trm [DB (enat w) c]) (numBT n)
                = Trm [DB (enat w) (operB c (Trm []))] *\<^sub>B (numNat (numBT n) + 1)"
          by (rule b1x_operB_case_i[OF cne True])
        show "operB (Trm [DB (enat w) c]) (numBT n) \<in> bwl_W w"
          unfolding eq by (rule bwl_2_4b_mult[OF base])
      qed
    next
      case False
      have dN: "domB c = NatSet" using num False by blast
      have g3: "\<not> (\<exists>u'. enat w \<le> enat u' \<and> domB c = TBv (enat u'))"
        using dN NatSet_neq_TBv by blast
      have dW: "domB (Trm [DB (enat w) c]) = domB c"
        by (rule b1x_domB_case_iii[OF cne False g3])
      show ?thesis
      proof (rule bwl_W2)
        show "domB (Trm [DB (enat w) c]) = {Trm []}
              \<or> domB (Trm [DB (enat w) c]) = NatSet" using dW dN by simp
      next
        fix n
        have "operB (Trm [DB (enat w) c]) (numBT n)
                = Trm [DB (enat w) (operB c (numBT n))]"
          by (rule b1x_operB_case_iii[OF cne False g3])
        moreover have "operB c (numBT n) \<in> ?Y" using num by blast
        ultimately show "operB (Trm [DB (enat w) c]) (numBT n) \<in> bwl_W w" by simp
      qed
    qed
  next
    case (tu m)
    have mw: "m < w" using tu(1) uw by simp
    have cne: "c \<noteq> Trm []"
    proof
      assume z: "c = Trm []"
      have "TBv (enat m) = {}" using z tu(2) bwo_domB_Nil by simp
      moreover have "Trm [] \<in> TBv (enat m)" by (simp add: TBv_def)
      ultimately show False by simp
    qed
    have g2: "domB c \<noteq> {Trm []}" using tu(2) bwl_TBv_neq_zero by simp
    have g3: "\<not> (\<exists>u'. enat w \<le> enat u' \<and> domB c = TBv (enat u'))"
      using tu(2) bwl_case_iii_guard_TBv[OF mw] by simp
    have dW: "domB (Trm [DB (enat w) c]) = TBv (enat m)"
      using b1x_domB_case_iii[OF cne g2 g3] tu(2) by simp
    show ?thesis
    proof (rule bwl_W3[where u = m])
      show "m < w" by (rule mw)
      show "domB (Trm [DB (enat w) c]) = TBv (enat m)" by (rule dW)
    next
      fix z assume zm: "z \<in> bwl_W m"
      have "operB (Trm [DB (enat w) c]) z = Trm [DB (enat w) (operB c z)]"
        by (rule b1x_operB_case_iii[OF cne g2 g3])
      moreover have "operB c z \<in> ?Y" using tu(3) zm by blast
      ultimately show "operB (Trm [DB (enat w) c]) z \<in> bwl_W w" by simp
    qed
  qed
  show "c \<in> ?Y" using main by simp
qed

lemma bwl_key_collapse:
  assumes uw: "u \<le> w" and x: "x \<in> bwl_W u"
  shows "Trm [DB (enat w) x] \<in> bwl_W w"
  using bwl_key_collapse_sub[OF uw] x by blast

text \<open>Two immediate corollaries: every \<open>W\<^sub>w\<close> is closed under its own \<open>D\<^sub>w\<close>, and the
  \<open>D\<^sub>w\<close>-towers over \<open>0\<close> all lie in \<open>W\<^sub>w\<close>.\<close>

lemma bwl_W_Dself: "x \<in> bwl_W w \<Longrightarrow> Trm [DB (enat w) x] \<in> bwl_W w"
  by (rule bwl_key_collapse[OF order_refl])

(* ===== end r68 bwl part 3 (collapsing closure W_u -> D_w W_u subseteq W_w, u<=w) ===== *)

subsection \<open>(8) The \<open>xseq\<close> branch ([].4)(ii), i.e. the [Buc2]-corrected case\<close>

lemma bwl_numNat_numBT: "numNat (numBT n) = n"
  by (simp add: numNat_def numBT_def)

lemma bwl_tbvIdx: "tbvIdx (TBv (enat u)) = u"
  unfolding tbvIdx_def
proof (rule the_equality)
  show "TBv (enat u) = TBv (enat u)" by simp
next
  fix u' assume "TBv (enat u) = TBv (enat u')"
  hence "u = u'" by (rule TBv_enat_inj)
  thus "u' = u" by simp
qed

lemma bwl_domB_case_ii:
  assumes bne: "b \<noteq> Trm []" and g2: "domB b \<noteq> {Trm []}"
    and g3: "\<exists>u. v \<le> enat u \<and> domB b = TBv (enat u)"
  shows "domB (Trm [DB v b]) = NatSet"
proof -
  have e1: "(b = Trm []) = False" using bne by simp
  have e2: "(domB b = {Trm []}) = False" using g2 by simp
  have e3: "(\<exists>u. v \<le> enat u \<and> domB b = TBv (enat u)) = True" using g3 by simp
  show ?thesis by (subst domB_unfold) (simp add: Let_def e1 e2 e3)
qed

lemma bwl_operB_case_ii:
  assumes bne: "b \<noteq> Trm []" and g2: "domB b \<noteq> {Trm []}"
    and g3: "\<exists>u. v \<le> enat u \<and> domB b = TBv (enat u)"
  shows "operB (Trm [DB v b]) z
           = Trm [DB v (operB b (xseq b (enat (tbvIdx (domB b))) (numNat z)))]"
proof -
  have e1: "(b = Trm []) = False" using bne by simp
  have e2: "(domB b = {Trm []}) = False" using g2 by simp
  have e3: "(\<exists>u. v \<le> enat u \<and> domB b = TBv (enat u)) = True" using g3 by simp
  show ?thesis by (subst b1x_operB_unfold) (simp add: Let_def e1 e2 e3)
qed

subsection \<open>(9) The DOWNWARD collapse \<open>W\<^sub>m \<subseteq> {y. \<forall>v \<le> m. D\<^sub>v y \<in> W\<^sub>v}\<close>\<close>

text \<open>\<^bold>\<open>The hard half of the collapsing closure\<close> — and the step where the
  [Buc2]-corrected fundamental sequence ([].4)(ii) (\<open>x\<^sub>0 = D\<^sub>u 0\<close>, \<open>x\<^sub>i = b[D\<^sub>u x\<^bsub>i-1\<^esub>]\<close>,
  \<open>(D\<^sub>v b)[n] = D\<^sub>v x\<^sub>n\<close>; correction A23) really has to be handled.  Buchholz's own
  2.6 case 4.2 uses the (typo-afflicted) literal \<open>a[n] := D\<^sub>v b[D\<^sub>u b[1]]\<close>, for which
  \<open>1 \<in> W\<^sub>u\<close> suffices; with the corrected \<open>xseq\<close> the base point of the sequence is
  \<open>x\<^sub>0 = D\<^sub>u 0\<close>, whose \<open>D\<^sub>v\<close>-image at levels \<open>v < u\<close> is not available from
  @{thm [source] bwl_key_collapse}.  The repair is a STRONG INDUCTION ON THE LEVEL
  \<open>m\<close>: in the \<open>dom(c) = T\<^sub>k\<close> clause one has \<open>k < m\<close>, so the induction hypothesis
  applies to \<open>W\<^sub>k \<ni> D\<^sub>k 0\<close> and supplies exactly the missing \<open>D\<^sub>v(D\<^sub>k 0) \<in> W\<^sub>v\<close> for
  \<open>v < k\<close>; levels \<open>v \<ge> k\<close> come from @{thm [source] bwl_key_collapse}.  The \<open>x\<^sub>j\<close> then
  stay inside the invariant by an inner induction on \<open>j\<close>.\<close>

lemma bwl_DC:
  "bwl_W m \<subseteq> {y. \<forall>v \<le> m. Trm [DB (enat v) y] \<in> bwl_W v}"
proof (induction m rule: less_induct)
  case (less m)
  let ?Y = "{y. \<forall>v \<le> m. Trm [DB (enat v) y] \<in> bwl_W v}"
  show ?case
  proof (rule bwl_A2')
    fix c assume A: "bwl_Aop bwl_W (enat m) ?Y c"
    consider (zero) "c = Trm []"
      | (num) "(domB c = {Trm []} \<or> domB c = NatSet) \<and> (\<forall>n. operB c (numBT n) \<in> ?Y)"
      | (tu) k where "enat k < enat m" "domB c = TBv (enat k)"
               "\<forall>z \<in> bwl_W k. operB c z \<in> ?Y"
      using A[unfolded bwl_Aop_def] by blast
    then have main: "\<And>v. v \<le> m \<Longrightarrow> Trm [DB (enat v) c] \<in> bwl_W v"
    proof cases
      case zero
      fix v assume "v \<le> m"
      show "Trm [DB (enat v) c] \<in> bwl_W v" using zero bwl_D_zero_W by simp
    next
      case num
      have cne: "c \<noteq> Trm []"
      proof
        assume z: "c = Trm []"
        have dz: "domB c = {}" using z bwo_domB_Nil by simp
        have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
        moreover have "Trm [] \<in> {Trm []}" by simp
        ultimately show False using conjunct1[OF num] dz by auto
      qed
      fix v assume vm: "v \<le> m"
      show "Trm [DB (enat v) c] \<in> bwl_W v"
      proof (cases "domB c = {Trm []}")
        case True
        have dW: "domB (Trm [DB (enat v) c]) = NatSet"
          by (rule bwl_domB_case_i[OF cne True])
        have base: "Trm [DB (enat v) (operB c (Trm []))] \<in> bwl_W v"
        proof -
          have "operB c (numBT 0) \<in> ?Y" using num by blast
          moreover have "numBT 0 = Trm []" by (simp add: numBT_def)
          ultimately show ?thesis using vm by simp
        qed
        show ?thesis
        proof (rule bwl_W2)
          show "domB (Trm [DB (enat v) c]) = {Trm []}
                \<or> domB (Trm [DB (enat v) c]) = NatSet" using dW by simp
        next
          fix n
          have eq: "operB (Trm [DB (enat v) c]) (numBT n)
                  = Trm [DB (enat v) (operB c (Trm []))] *\<^sub>B (numNat (numBT n) + 1)"
            by (rule b1x_operB_case_i[OF cne True])
          show "operB (Trm [DB (enat v) c]) (numBT n) \<in> bwl_W v"
            unfolding eq by (rule bwl_2_4b_mult[OF base])
        qed
      next
        case False
        have dN: "domB c = NatSet" using num False by blast
        have g3: "\<not> (\<exists>u'. enat v \<le> enat u' \<and> domB c = TBv (enat u'))"
          using dN NatSet_neq_TBv by blast
        have dW: "domB (Trm [DB (enat v) c]) = domB c"
          by (rule b1x_domB_case_iii[OF cne False g3])
        show ?thesis
        proof (rule bwl_W2)
          show "domB (Trm [DB (enat v) c]) = {Trm []}
                \<or> domB (Trm [DB (enat v) c]) = NatSet" using dW dN by simp
        next
          fix n
          have "operB (Trm [DB (enat v) c]) (numBT n)
                  = Trm [DB (enat v) (operB c (numBT n))]"
            by (rule b1x_operB_case_iii[OF cne False g3])
          moreover have "operB c (numBT n) \<in> ?Y" using num by blast
          ultimately show "operB (Trm [DB (enat v) c]) (numBT n) \<in> bwl_W v"
            using vm by simp
        qed
      qed
    next
      case (tu k)
      have km: "k < m" using tu(1) by simp
      have cne: "c \<noteq> Trm []"
      proof
        assume z: "c = Trm []"
        have "TBv (enat k) = {}" using z tu(2) bwo_domB_Nil by simp
        moreover have "Trm [] \<in> TBv (enat k)" by (simp add: TBv_def)
        ultimately show False by simp
      qed
      have g2: "domB c \<noteq> {Trm []}" using tu(2) bwl_TBv_neq_zero by simp
      \<comment> \<open>r72: under the CORRECTED ([].4)(ii) (\<open>x\<^sub>0 = D\<^sub>k 0\<close>, \<open>x\<^bsub>j+1\<^esub> = D\<^sub>k (c[x\<^sub>j])\<close>,
         \<open>(D\<^sub>v c)[n] = D\<^sub>v (c[x\<^sub>n])\<close>) the \<open>xseq\<close> lives in \<open>W\<^sub>k\<close> OUTRIGHT, so the A23
         workaround (the base point at EVERY level, via the upward collapse) is
         no longer needed --- only \<open>x\<^sub>0 = D\<^sub>k 0 \<in> W\<^sub>k\<close>.\<close>
      have Dk0: "Trm [DB (enat k) (Trm [])] \<in> bwl_W k" by (rule bwl_D_zero_W)
      fix v assume vm: "v \<le> m"
      show "Trm [DB (enat v) c] \<in> bwl_W v"
      proof (cases "k < v")
        case True
        \<comment> \<open>([].4)(iii): \<open>dom(D\<^sub>v c) = T\<^sub>k\<close> and \<open>(D\<^sub>v c)[z] = D\<^sub>v(c[z])\<close>\<close>
        have g3: "\<not> (\<exists>u'. enat v \<le> enat u' \<and> domB c = TBv (enat u'))"
          using tu(2) bwl_case_iii_guard_TBv[OF True] by simp
        have dW: "domB (Trm [DB (enat v) c]) = TBv (enat k)"
          using b1x_domB_case_iii[OF cne g2 g3] tu(2) by simp
        show ?thesis
        proof (rule bwl_W3[where u = k])
          show "k < v" by (rule True)
          show "domB (Trm [DB (enat v) c]) = TBv (enat k)" by (rule dW)
        next
          fix z assume zk: "z \<in> bwl_W k"
          have "operB (Trm [DB (enat v) c]) z = Trm [DB (enat v) (operB c z)]"
            by (rule b1x_operB_case_iii[OF cne g2 g3])
          moreover have "operB c z \<in> ?Y" using tu(3) zk by blast
          ultimately show "operB (Trm [DB (enat v) c]) z \<in> bwl_W v" using vm by simp
        qed
      next
        case False
        \<comment> \<open>([].4)(ii): the \<open>xseq\<close> branch, \<open>v \<le> k\<close>\<close>
        hence vk: "enat v \<le> enat k" by simp
        have g3: "\<exists>u'. enat v \<le> enat u' \<and> domB c = TBv (enat u')"
          using vk tu(2) by blast
        have dW: "domB (Trm [DB (enat v) c]) = NatSet"
          by (rule bwl_domB_case_ii[OF cne g2 g3])
        have tb: "tbvIdx (domB c) = k" using tu(2) by (simp add: bwl_tbvIdx)
        \<comment> \<open>the \<open>xseq\<close> stays inside \<open>W\<^sub>k\<close>: \<open>x\<^bsub>j+1\<^esub> = D\<^sub>k (c[x\<^sub>j])\<close>, and \<open>c[x\<^sub>j] \<in> ?Y\<close>
           by \<open>tu(3)\<close>, so its \<open>D\<^sub>k\<close>-image is in \<open>W\<^sub>k\<close> (\<open>k \<le> m\<close>)\<close>
        have xW: "xseq c (enat k) j \<in> bwl_W k" for j
        proof (induction j)
          case 0
          have x0: "xseq c (enat k) 0 = Trm [DB (enat k) (Trm [])]" by (rule b1x_xseq_0)
          show ?case using x0 Dk0 by simp
        next
          case (Suc j)
          have xs: "xseq c (enat k) (Suc j)
                      = Trm [DB (enat k) (operB c (xseq c (enat k) j))]"
            by (rule b1x_xseq_Suc)
          have cY: "operB c (xseq c (enat k) j) \<in> ?Y"
            using tu(3) Suc.IH by blast
          have "Trm [DB (enat k) (operB c (xseq c (enat k) j))] \<in> bwl_W k"
            using cY km by auto
          thus ?case using xs by simp
        qed
        show ?thesis
        proof (rule bwl_W2)
          show "domB (Trm [DB (enat v) c]) = {Trm []}
                \<or> domB (Trm [DB (enat v) c]) = NatSet" using dW by simp
        next
          fix n
          have "operB (Trm [DB (enat v) c]) (numBT n)
                  = Trm [DB (enat v)
                      (operB c (xseq c (enat (tbvIdx (domB c))) (numNat (numBT n))))]"
            by (rule bwl_operB_case_ii[OF cne g2 g3])
          hence eq: "operB (Trm [DB (enat v) c]) (numBT n)
                       = Trm [DB (enat v) (operB c (xseq c (enat k) n))]"
            using tb bwl_numNat_numBT by simp
          have "xseq c (enat k) n \<in> bwl_W k" by (rule xW)
          hence "operB c (xseq c (enat k) n) \<in> ?Y" using tu(3) by blast
          hence "Trm [DB (enat v) (operB c (xseq c (enat k) n))] \<in> bwl_W v"
            using vm by blast
          thus "operB (Trm [DB (enat v) c]) (numBT n) \<in> bwl_W v" using eq by simp
        qed
      qed
    qed
    show "c \<in> ?Y" using main by blast
  qed
qed

text \<open>Combining the two directions: every \<open>W\<^sub>m\<close> is contained in Buchholz's \<open>W\<^sup>*\<close>.\<close>

lemma bwl_W_subset_star:
  assumes y: "y \<in> bwl_W m"
  shows "Trm [DB (enat v) y] \<in> bwl_W v"
proof (cases "v \<le> m")
  case True
  have "y \<in> {y. \<forall>v \<le> m. Trm [DB (enat v) y] \<in> bwl_W v}" using bwl_DC y by blast
  thus ?thesis using True by blast
next
  case False
  hence "m \<le> v" by simp
  thus ?thesis by (rule bwl_key_collapse[OF _ y])
qed

(* ===== end r68 bwl part 4 (downward collapse; W_m inside Wstar) ===== *)

subsection \<open>(10) [Buc1] p.138(5): \<open>W\<^sup>* = {x. \<forall>u < \<nu>. D\<^sub>u x \<in> W\<^sub>u}\<close> (here \<open>\<nu> = \<omega>\<close>)\<close>

definition bwl_Wstar :: "BT set" where
  "bwl_Wstar = {x. \<forall>u. Trm [DB (enat u) x] \<in> bwl_W u}"

lemma bwl_WstarI: "(\<And>u. Trm [DB (enat u) x] \<in> bwl_W u) \<Longrightarrow> x \<in> bwl_Wstar"
  unfolding bwl_Wstar_def by blast

lemma bwl_WstarD: "x \<in> bwl_Wstar \<Longrightarrow> Trm [DB (enat u) x] \<in> bwl_W u"
  unfolding bwl_Wstar_def by blast

text \<open>By the two collapse directions, every level set already sits inside \<open>W\<^sup>*\<close>.\<close>

lemma bwl_W_in_Wstar: "y \<in> bwl_W m \<Longrightarrow> y \<in> bwl_Wstar"
  by (rule bwl_WstarI) (rule bwl_W_subset_star)

lemma bwl_zero_Wstar: "Trm [] \<in> bwl_Wstar"
  by (rule bwl_W_in_Wstar[OF bwl_W_zero])

subsection \<open>(11) [Buc1] Lemma 2.6: \<open>A\<^sub>\<nu>(W\<^sup>*) \<subseteq> W\<^sup>*\<close>\<close>

lemma bwl_2_6:
  assumes A: "bwl_Aop bwl_W \<infinity> bwl_Wstar b"
  shows "b \<in> bwl_Wstar"
proof (rule bwl_WstarI)
  fix v :: nat
  consider (zero) "b = Trm []"
    | (num) "(domB b = {Trm []} \<or> domB b = NatSet)
             \<and> (\<forall>n. operB b (numBT n) \<in> bwl_Wstar)"
    | (tu) u where "domB b = TBv (enat u)" "\<forall>z \<in> bwl_W u. operB b z \<in> bwl_Wstar"
    using A[unfolded bwl_Aop_def] by blast
  thus "Trm [DB (enat v) b] \<in> bwl_W v"
  proof cases
    case zero
    thus ?thesis using bwl_D_zero_W by simp
  next
    case num
    have bne: "b \<noteq> Trm []"
    proof
      assume z: "b = Trm []"
      have dz: "domB b = {}" using z bwo_domB_Nil by simp
      have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
      moreover have "Trm [] \<in> {Trm []}" by simp
      ultimately show False using conjunct1[OF num] dz by auto
    qed
    show ?thesis
    proof (cases "domB b = {Trm []}")
      case True
      have dW: "domB (Trm [DB (enat v) b]) = NatSet"
        by (rule bwl_domB_case_i[OF bne True])
      have base: "Trm [DB (enat v) (operB b (Trm []))] \<in> bwl_W v"
      proof -
        have "operB b (numBT 0) \<in> bwl_Wstar" using num by blast
        moreover have "numBT 0 = Trm []" by (simp add: numBT_def)
        ultimately show ?thesis using bwl_WstarD by simp
      qed
      show ?thesis
      proof (rule bwl_W2)
        show "domB (Trm [DB (enat v) b]) = {Trm []}
              \<or> domB (Trm [DB (enat v) b]) = NatSet" using dW by simp
      next
        fix n
        have eq: "operB (Trm [DB (enat v) b]) (numBT n)
                = Trm [DB (enat v) (operB b (Trm []))] *\<^sub>B (numNat (numBT n) + 1)"
          by (rule b1x_operB_case_i[OF bne True])
        show "operB (Trm [DB (enat v) b]) (numBT n) \<in> bwl_W v"
          unfolding eq by (rule bwl_2_4b_mult[OF base])
      qed
    next
      case False
      have dN: "domB b = NatSet" using num False by blast
      have g3: "\<not> (\<exists>u'. enat v \<le> enat u' \<and> domB b = TBv (enat u'))"
        using dN NatSet_neq_TBv by blast
      have dW: "domB (Trm [DB (enat v) b]) = domB b"
        by (rule b1x_domB_case_iii[OF bne False g3])
      show ?thesis
      proof (rule bwl_W2)
        show "domB (Trm [DB (enat v) b]) = {Trm []}
              \<or> domB (Trm [DB (enat v) b]) = NatSet" using dW dN by simp
      next
        fix n
        have "operB (Trm [DB (enat v) b]) (numBT n)
                = Trm [DB (enat v) (operB b (numBT n))]"
          by (rule b1x_operB_case_iii[OF bne False g3])
        moreover have "operB b (numBT n) \<in> bwl_Wstar" using num by blast
        ultimately show "operB (Trm [DB (enat v) b]) (numBT n) \<in> bwl_W v"
          using bwl_WstarD by simp
      qed
    qed
  next
    case (tu u)
    have bne: "b \<noteq> Trm []"
    proof
      assume z: "b = Trm []"
      have "TBv (enat u) = {}" using z tu(1) bwo_domB_Nil by simp
      moreover have "Trm [] \<in> TBv (enat u)" by (simp add: TBv_def)
      ultimately show False by simp
    qed
    have g2: "domB b \<noteq> {Trm []}" using tu(1) bwl_TBv_neq_zero by simp
    show ?thesis
    proof (cases "u < v")
      case True
      \<comment> \<open>[1] 2.6 case 4.1: \<open>u < v\<close>, branch ([].4)(iii), rule (W3)\<close>
      have g3: "\<not> (\<exists>u'. enat v \<le> enat u' \<and> domB b = TBv (enat u'))"
        using tu(1) bwl_case_iii_guard_TBv[OF True] by simp
      have dW: "domB (Trm [DB (enat v) b]) = TBv (enat u)"
        using b1x_domB_case_iii[OF bne g2 g3] tu(1) by simp
      show ?thesis
      proof (rule bwl_W3[where u = u])
        show "u < v" by (rule True)
        show "domB (Trm [DB (enat v) b]) = TBv (enat u)" by (rule dW)
      next
        fix z assume zu: "z \<in> bwl_W u"
        have "operB (Trm [DB (enat v) b]) z = Trm [DB (enat v) (operB b z)]"
          by (rule b1x_operB_case_iii[OF bne g2 g3])
        moreover have "operB b z \<in> bwl_Wstar" using tu(2) zu by blast
        ultimately show "operB (Trm [DB (enat v) b]) z \<in> bwl_W v"
          using bwl_WstarD by simp
      qed
    next
      case False
      \<comment> \<open>[1] 2.6 case 4.2: \<open>v \<le> u\<close>, the \<open>xseq\<close> branch ([].4)(ii).  \<^bold>\<open>r72\<close>: under the
         CORRECTED rule (\<open>x\<^sub>0 = D\<^sub>u 0\<close>, \<open>x\<^bsub>j+1\<^esub> = D\<^sub>u (b[x\<^sub>j])\<close>, \<open>(D\<^sub>v b)[n] = D\<^sub>v (b[x\<^sub>n])\<close>)
         the whole case collapses to ONE invariant, \<open>x\<^sub>j \<in> W\<^sub>u\<close>: the base point is
         \<open>D\<^sub>u 0 \<in> W\<^sub>u\<close> and the step is \<open>x\<^sub>j \<in> W\<^sub>u \<Longrightarrow> b[x\<^sub>j] \<in> W\<^sup>* \<Longrightarrow> D\<^sub>u (b[x\<^sub>j]) \<in> W\<^sub>u\<close>.
         Buchholz's \<open>b[1] \<in> W\<^sup>*\<close> detour and the A23 base-point workaround are BOTH
         unnecessary.\<close>
      hence vu: "enat v \<le> enat u" by simp
      have g3: "\<exists>u'. enat v \<le> enat u' \<and> domB b = TBv (enat u')"
        using vu tu(1) by blast
      have dW: "domB (Trm [DB (enat v) b]) = NatSet"
        by (rule bwl_domB_case_ii[OF bne g2 g3])
      have tb: "tbvIdx (domB b) = u" using tu(1) by (simp add: bwl_tbvIdx)
      have xW: "xseq b (enat u) j \<in> bwl_W u" for j
      proof (induction j)
        case 0
        have x0: "xseq b (enat u) 0 = Trm [DB (enat u) (Trm [])]" by (rule b1x_xseq_0)
        show ?case using x0 bwl_D_zero_W by simp
      next
        case (Suc j)
        have xs: "xseq b (enat u) (Suc j)
                    = Trm [DB (enat u) (operB b (xseq b (enat u) j))]"
          by (rule b1x_xseq_Suc)
        have bW: "operB b (xseq b (enat u) j) \<in> bwl_Wstar"
          using tu(2) Suc.IH by blast
        have "Trm [DB (enat u) (operB b (xseq b (enat u) j))] \<in> bwl_W u"
          using bW by (rule bwl_WstarD)
        thus ?case using xs by simp
      qed
      show ?thesis
      proof (rule bwl_W2)
        show "domB (Trm [DB (enat v) b]) = {Trm []}
              \<or> domB (Trm [DB (enat v) b]) = NatSet" using dW by simp
      next
        fix n
        have "operB (Trm [DB (enat v) b]) (numBT n)
                = Trm [DB (enat v)
                    (operB b (xseq b (enat (tbvIdx (domB b))) (numNat (numBT n))))]"
          by (rule bwl_operB_case_ii[OF bne g2 g3])
        hence eq: "operB (Trm [DB (enat v) b]) (numBT n)
                     = Trm [DB (enat v) (operB b (xseq b (enat u) n))]"
          using tb bwl_numNat_numBT by simp
        have "operB b (xseq b (enat u) n) \<in> bwl_Wstar" using tu(2) xW by blast
        hence "Trm [DB (enat v) (operB b (xseq b (enat u) n))] \<in> bwl_W v"
          by (rule bwl_WstarD)
        thus "operB (Trm [DB (enat v) b]) (numBT n) \<in> bwl_W v" using eq by simp
      qed
    qed
  qed
qed

subsection \<open>(12) [Buc1] Lemma 2.7 (length induction) for the \<open>D\<^sub>\<omega>\<close>-free terms\<close>

lemma bwl_size_list_butlast:
  "l \<noteq> [] \<Longrightarrow> size_list size (butlast l) < size_list size (l :: BP list)"
  by (induction l) auto

lemma bwl_size_butlast_lt:
  "xs \<noteq> [] \<Longrightarrow> size (Trm (butlast xs) :: BT) < size (Trm xs :: BT)"
  using bwl_size_list_butlast by simp

text \<open>[1] 2.7: \<open>A\<^sub>\<nu>(X) \<subseteq> X \<Longrightarrow> a \<in> X\<close>, for \<open>a\<close> containing no \<open>D\<^sub>v\<close> with \<open>v > \<nu>\<close>.  We take
  \<open>\<nu> = \<omega> = \<infinity>\<close> and restrict to the \<open>D\<^sub>\<omega>\<close>-free terms \<open>T\<^bsub>B\<^esub>\<close> (which is all we ever need).
  \<^bold>\<open>Consequence: Buchholz's case 3 (\<open>a = D\<^sub>\<nu> b\<close> with the index EQUAL to \<open>\<nu>\<close>), the only
  case that needs Lemma 2.5 and the \<open>D\<^sub>\<nu>\<close>-closure \<open>Xbar\<close>, cannot arise\<close> — a \<open>D\<^sub>\<omega>\<close>-free
  principal always has a FINITE index \<open>n < \<omega>\<close>, i.e. Buchholz's case 4, which is
  discharged by 2.6 plus the leastness (A2).  So the whole 6-case \<open>Xbar\<close> analysis of
  [1] 2.5 is bypassed.  The induction is on \<open>size\<close> (subsuming his induction on the
  length of \<open>a\<close>), and the set \<open>X\<close> must be generalised (case 2 instantiates it with the
  shift \<open>X\<^bsup>(c)\<^esup>\<close>, case 3 with \<open>W\<^sup>*\<close>).\<close>

lemma bwl_2_7_aux:
  "\<forall>X. (\<forall>c. bwl_Aop bwl_W \<infinity> X c \<longrightarrow> c \<in> X) \<longrightarrow> dfree_BT a \<longrightarrow> a \<in> X"
proof (induction a rule: measure_induct_rule[where f = size])
  case (less a)
  show ?case
  proof (intro allI impI)
    fix X :: "BT set"
    assume Acl: "\<forall>c. bwl_Aop bwl_W \<infinity> X c \<longrightarrow> c \<in> X"
    assume dfa: "dfree_BT a"
    obtain xs where axs: "a = Trm xs" by (cases a)
    show "a \<in> X"
    proof (cases xs)
      case Nil
      have "bwl_Aop bwl_W \<infinity> X (Trm [])" by (simp add: bwl_Aop_def)
      thus ?thesis using Acl axs Nil by blast
    next
      case (Cons p ps)
      show ?thesis
      proof (cases ps)
        case Nil
        \<comment> \<open>single principal \<open>a = D\<^sub>w b\<close>; \<open>D\<^sub>\<omega>\<close>-freeness forces \<open>w = n < \<omega> = \<nu>\<close> ([1] 2.7 case 4)\<close>
        obtain w b where peq: "p = DB w b" by (cases p)
        have aeq: "a = Trm [DB w b]" using axs Cons Nil peq by simp
        have wfin: "w \<noteq> \<infinity>" using dfa aeq by simp
        have dfb: "dfree_BT b" using dfa aeq by simp
        obtain n where wn: "w = enat n" using wfin by (cases w) auto
        have Wcl: "\<forall>c. bwl_Aop bwl_W \<infinity> bwl_Wstar c \<longrightarrow> c \<in> bwl_Wstar"
          using bwl_2_6 by blast
        have szb: "size b < size a" using aeq by simp
        have bW: "b \<in> bwl_Wstar" using less.IH[OF szb] Wcl dfb by blast
        have Dn: "Trm [DB (enat n) b] \<in> bwl_W n" using bW by (rule bwl_WstarD)
        have AnX: "\<And>c. bwl_Aop bwl_W (enat n) X c \<Longrightarrow> c \<in> X"
        proof -
          fix c assume c: "bwl_Aop bwl_W (enat n) X c"
          have inf: "enat n \<le> \<infinity>" by simp
          have "bwl_Aop bwl_W \<infinity> X c" by (rule bwl_Aop_mono_nv[OF inf c])
          thus "c \<in> X" using Acl by blast
        qed
        have "bwl_W n \<subseteq> X" by (rule bwl_A2'[OF AnX])
        thus ?thesis using Dn aeq wn by blast
      next
        case (Cons q qs)
        \<comment> \<open>\<open>a = c + a\<^sub>k\<close> with \<open>c\<close> the butlast ([1] 2.7 case 2, via 2.4(a))\<close>
        have xne: "xs \<noteq> []" using axs \<open>xs = p # ps\<close> by simp
        have xs2: "xs = p # q # qs" using \<open>xs = p # ps\<close> \<open>ps = q # qs\<close> by simp
        have allf: "\<forall>r \<in> set xs. dfree_BP r" using dfa axs by simp
        have aeq: "a = Trm (butlast xs) +\<^sub>B Trm [last xs]"
          using axs xne by (simp add: append_butlast_last_id)
        have szc: "size (Trm (butlast xs) :: BT) < size a"
          using axs bwl_size_butlast_lt[OF xne] by simp
        have szl: "size (Trm [last xs] :: BT) < size a"
          using axs xs2 b1x_size_last_lt[of p q qs] by simp
        have dfc: "dfree_BT (Trm (butlast xs))"
          using allf by (auto dest: in_set_butlastD)
        have dfl: "dfree_BT (Trm [last xs])"
        proof -
          have "last xs \<in> set xs" using xne by simp
          hence "dfree_BP (last xs)" using allf by blast
          thus ?thesis by simp
        qed
        have Acl': "\<And>e. bwl_Aop bwl_W \<infinity> X e \<Longrightarrow> e \<in> X" using Acl by blast
        have cX: "Trm (butlast xs) \<in> X" using less.IH[OF szc] Acl dfc by blast
        have shcl: "\<And>d. bwl_Aop bwl_W \<infinity> (bwo_shift (Trm (butlast xs)) X) d
                          \<Longrightarrow> d \<in> bwo_shift (Trm (butlast xs)) X"
          by (rule bwl_2_4a_shift[OF Acl' cX])
        have "Trm [last xs] \<in> bwo_shift (Trm (butlast xs)) X"
          using less.IH[OF szl] shcl dfl by blast
        hence "Trm (butlast xs) +\<^sub>B Trm [last xs] \<in> X"
          by (simp add: bwo_shift_def)
        thus ?thesis using aeq by simp
      qed
    qed
  qed
qed

subsection \<open>(13) [Buc1] 2.8 for \<open>T\<^bsub>B\<^esub>\<close>: every \<open>D\<^sub>\<omega>\<close>-free term lies in \<open>W\<^sup>*\<close>\<close>

theorem bwl_2_8_dfree_Wstar:
  assumes df: "dfree_BT t"
  shows "t \<in> bwl_Wstar"
proof -
  have Wcl: "\<forall>c. bwl_Aop bwl_W \<infinity> bwl_Wstar c \<longrightarrow> c \<in> bwl_Wstar"
    using bwl_2_6 by blast
  show ?thesis using bwl_2_7_aux[of t] Wcl df by blast
qed

corollary bwl_2_8_principal:
  assumes df: "dfree_BT t"
  shows "Trm [DB (enat u) t] \<in> bwl_W u"
  using bwl_2_8_dfree_Wstar[OF df] by (rule bwl_WstarD)

text \<open>\<^bold>\<open>Status.\<close>  [Buc1] \<section>2 is now fully mechanized on its own (\<open>lfp\<close>) terms: every
  \<open>D\<^sub>\<omega>\<close>-free term is in \<open>W\<^sup>*\<close>, i.e. all its principals \<open>D\<^sub>u t\<close> are in the inductively
  generated \<open>W\<^sub>u\<close>.  Note this needed NO \<open>OT\<close> (normal-form) hypothesis.\<close>

(* ===== end r68 bwl part 5 ([Buc1] 2.6, 2.7 for dfree, 2.8: T_B inside Wstar) ===== *)

subsection \<open>(14) The bridge \<open>W\<^sub>u \<longrightarrow> acc\<close>, and the NEW single residual \<open>bwl_cof\<close>\<close>

text \<open>\<^bold>\<open>Where the remaining work now sits.\<close>  Part 5 proves that every \<open>D\<^sub>\<omega>\<close>-free term
  lies in \<open>W\<^sup>*\<close> — that is Buchholz's \<^emph>\<open>fundamental-sequence\<close> well-foundedness (the
  hydra theorem), and it is now unconditional.  What \<open>wf RPrel\<close> additionally needs is
  that \<open>W\<^sub>u\<close>-membership implies \<open><\<close>-ACCESSIBILITY, and the ONLY gap between the two is
  that the \<open>W\<close>-rules (W2)/(W3) descend along the fundamental sequences \<open>a[n]\<close> / \<open>a[z]\<close>,
  whereas \<open>acc\<close> quantifies over ALL \<open><\<close>-predecessors.  So the bridge is exactly the
  \<^bold>\<open>cofinality (Bachmann) property\<close>: every \<open>b < a\<close> is \<open>\<le>\<close> some element of \<open>a\<close>'s
  fundamental sequence.  We isolate it as \<open>bwl_cof\<close> and show it is SUFFICIENT.

  (This is the same mathematical content that round 67 met as the unprovable
  hypothesis (A2) of the \<^emph>\<open>acc\<close>-based \<open>bwo_Wlev\<close>; the \<open>lfp\<close> restructuring did not
  make it disappear, but it has (i) made the whole of Buchholz \<section>2 unconditional,
  and (ii) reduced the residual from a statement about \<open>acc\<close>-sets to a purely
  \<^emph>\<open>order-theoretic\<close> statement about \<open><\<close> and \<open>[\<cdot>]\<close> on \<open>OT\<^bsub>B\<^esub>\<close>, with no fixpoints
  in it.)\<close>

definition bwl_cof :: bool where
  "bwl_cof \<longleftrightarrow>
     (\<forall>a b. isOT_BT a \<longrightarrow> dfree_BT a \<longrightarrow> isOT_BT b \<longrightarrow> dfree_BT b \<longrightarrow> lessBT b a \<longrightarrow>
        (((domB a = {Trm []} \<or> domB a = NatSet)
             \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n))))
         \<and> (\<forall>m. domB a = TBv (enat m)
             \<longrightarrow> (\<exists>z. z \<in> bwl_W m \<and> z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z
                        \<and> leBT b (operB a z)))))"

lemma bwl_not_lessBT_zero: "\<not> lessBT y (Trm [])"
proof (cases y)
  case (Trm ys)
  then show ?thesis by (cases ys) simp_all
qed

text \<open>The principal embedding \<open>p \<mapsto> D\<^sub>? p = Trm [p]\<close> reflects accessibility.\<close>

lemma bwl_acc_BP_of_BT_aux:
  assumes "y \<in> Wellfounded.acc RTrel"
  shows "\<forall>q. y = Trm [q] \<longrightarrow> q \<in> Wellfounded.acc RPrel"
  using assms
proof (induction rule: acc.induct)
  case (accI y)
  show ?case
  proof (intro allI impI)
    fix q assume yq: "y = Trm [q]"
    show "q \<in> Wellfounded.acc RPrel"
    proof (rule acc.intros)
      fix r assume rq: "(r, q) \<in> RPrel"
      have "(Trm [r], Trm [q]) \<in> RTrel" by (rule wfox_RPrel_into_RTrel[OF rq])
      hence ry: "(Trm [r], y) \<in> RTrel" using yq by simp
      have "\<forall>q'. Trm [r] = Trm [q'] \<longrightarrow> q' \<in> Wellfounded.acc RPrel"
        by (rule accI.IH[OF ry])
      thus "r \<in> Wellfounded.acc RPrel" by simp
    qed
  qed
qed

lemma bwl_acc_BP_of_BT:
  "Trm [p] \<in> Wellfounded.acc RTrel \<Longrightarrow> p \<in> Wellfounded.acc RPrel"
  using bwl_acc_BP_of_BT_aux by blast

text \<open>\<^bold>\<open>The bridge.\<close>  Under \<open>bwl_cof\<close> the set \<open>acc RTrel\<close> is \<open>A\<^sub>u\<close>-closed, so the (free)
  leastness (A2) gives \<open>W\<^sub>u \<subseteq> acc RTrel\<close>.  Note the terms that are NOT in \<open>OT\<^bsub>B\<^esub>\<close> are
  \<open>acc\<close> for free (they have no \<open>RTrel\<close>-predecessors at all).\<close>

lemma bwl_acc_of_W:
  assumes COF: "bwl_cof"
  shows "bwl_W u \<subseteq> Wellfounded.acc RTrel"
proof (rule bwl_A2')
  fix c assume A: "bwl_Aop bwl_W (enat u) (Wellfounded.acc RTrel) c"
  show "c \<in> Wellfounded.acc RTrel"
  proof (cases "isOT_BT c \<and> dfree_BT c")
    case False
    show ?thesis
    proof (rule acc.intros)
      fix y assume "(y, c) \<in> RTrel"
      hence "isOT_BT c \<and> dfree_BT c" by (simp add: RTrel_def)
      thus "y \<in> Wellfounded.acc RTrel" using False by simp
    qed
  next
    case True
    have otc: "isOT_BT c" and dfc: "dfree_BT c" using True by simp_all
    have cOT: "c \<in> OT_B" using otc dfc by (simp add: OT_B_def OT_def T_B_def)
    consider (zero) "c = Trm []"
      | (num) "(domB c = {Trm []} \<or> domB c = NatSet)
               \<and> (\<forall>n. operB c (numBT n) \<in> Wellfounded.acc RTrel)"
      | (tu) m where "enat m < enat u" "domB c = TBv (enat m)"
               "\<forall>z \<in> bwl_W m. operB c z \<in> Wellfounded.acc RTrel"
      using A[unfolded bwl_Aop_def] by blast
    thus ?thesis
    proof cases
      case zero
      show ?thesis
      proof (rule acc.intros)
        fix y assume "(y, c) \<in> RTrel"
        hence "lessBT y (Trm [])" using zero by (simp add: RTrel_def)
        thus "y \<in> Wellfounded.acc RTrel" using bwl_not_lessBT_zero by simp
      qed
    next
      case num
      have cne: "c \<noteq> Trm []"
      proof
        assume z: "c = Trm []"
        have dz: "domB c = {}" using z bwo_domB_Nil by simp
        have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
        moreover have "Trm [] \<in> {Trm []}" by simp
        ultimately show False using conjunct1[OF num] dz by auto
      qed
      show ?thesis
      proof (rule acc.intros)
        fix b assume bc: "(b, c) \<in> RTrel"
        have otb: "isOT_BT b" and dfb: "dfree_BT b" and lb: "lessBT b c"
          using bc by (simp_all add: RTrel_def)
        have cofc: "((domB c = {Trm []} \<or> domB c = NatSet)
                       \<longrightarrow> (\<exists>n. leBT b (operB c (numBT n))))
                    \<and> (\<forall>m. domB c = TBv (enat m)
                       \<longrightarrow> (\<exists>z. z \<in> bwl_W m \<and> z \<in> domB c \<and> isOT_BT z \<and> dfree_BT z
                                  \<and> leBT b (operB c z)))"
          by (rule COF[unfolded bwl_cof_def, rule_format, OF otc dfc otb dfb lb])
        have D: "domB c = {Trm []} \<or> domB c = NatSet" using num by blast
        have "\<exists>n. leBT b (operB c (numBT n))" using conjunct1[OF cofc] D by simp
        then obtain n where nb: "leBT b (operB c (numBT n))" by blast
        have accn: "operB c (numBT n) \<in> Wellfounded.acc RTrel" using num by blast
        have otn: "operB c (numBT n) \<in> OT_B"
          by (rule m_buc1_3_2_OT_B_closed[OF cOT cne])
        show "b \<in> Wellfounded.acc RTrel"
        proof (cases "b = operB c (numBT n)")
          case True thus ?thesis using accn by simp
        next
          case False
          hence "lessBT b (operB c (numBT n))" using nb by simp
          hence "(b, operB c (numBT n)) \<in> RTrel"
            using otb dfb otn by (simp add: RTrel_def OT_B_def OT_def T_B_def)
          thus ?thesis by (rule acc_downward[OF accn])
        qed
      qed
    next
      case (tu m)
      have cne: "c \<noteq> Trm []"
      proof
        assume z: "c = Trm []"
        have "TBv (enat m) = {}" using z tu(2) bwo_domB_Nil by simp
        moreover have "Trm [] \<in> TBv (enat m)" by (simp add: TBv_def)
        ultimately show False by simp
      qed
      show ?thesis
      proof (rule acc.intros)
        fix b assume bc: "(b, c) \<in> RTrel"
        have otb: "isOT_BT b" and dfb: "dfree_BT b" and lb: "lessBT b c"
          using bc by (simp_all add: RTrel_def)
        have cofc: "((domB c = {Trm []} \<or> domB c = NatSet)
                       \<longrightarrow> (\<exists>n. leBT b (operB c (numBT n))))
                    \<and> (\<forall>m. domB c = TBv (enat m)
                       \<longrightarrow> (\<exists>z. z \<in> bwl_W m \<and> z \<in> domB c \<and> isOT_BT z \<and> dfree_BT z
                                  \<and> leBT b (operB c z)))"
          by (rule COF[unfolded bwl_cof_def, rule_format, OF otc dfc otb dfb lb])
        have "\<exists>z. z \<in> bwl_W m \<and> z \<in> domB c \<and> isOT_BT z \<and> dfree_BT z
                    \<and> leBT b (operB c z)"
          using conjunct2[OF cofc] tu(2) by simp
        then obtain z where zW: "z \<in> bwl_W m" and zd: "z \<in> domB c"
          and otz: "isOT_BT z" and dfz: "dfree_BT z"
          and nb: "leBT b (operB c z)" by blast
        have accz: "operB c z \<in> Wellfounded.acc RTrel" using tu(3) zW by blast
        have "isOT_BT (operB c z) \<and> dfree_BT (operB c z)"
          using b1x_master[OF otc dfc cne disjI1[OF zd]] otz dfz by blast
        hence otz': "operB c z \<in> OT_B" by (simp add: OT_B_def OT_def T_B_def)
        show "b \<in> Wellfounded.acc RTrel"
        proof (cases "b = operB c z")
          case True thus ?thesis using accz by simp
        next
          case False
          hence "lessBT b (operB c z)" using nb by simp
          hence "(b, operB c z) \<in> RTrel"
            using otb dfb otz' by (simp add: RTrel_def OT_B_def OT_def T_B_def)
          thus ?thesis by (rule acc_downward[OF accz])
        qed
      qed
    qed
  qed
qed

text \<open>\<^bold>\<open>Consequence: the r66 residual \<open>bwo_Wstar_total\<close> is implied by \<open>bwl_cof\<close>\<close> — hence
  so is \<open>wf RPrel\<close> ([Buc1] Lemma 2.2), via the already-proven \<open>bwo_2_2_wf\<close>.\<close>

theorem bwl_Wstar_total_of_cof:
  assumes COF: "bwl_cof"
  shows "bwo_Wstar_total"
proof (unfold bwo_Wstar_total_def, intro allI impI)
  fix t assume ot: "isOT_BT t" and df: "dfree_BT t"
  show "t \<in> bwo_Wstar"
  proof (unfold bwo_Wstar_def, intro CollectI allI impI)
    fix u assume "isOT_BP (DB (enat u) t)" and "dfree_BP (DB (enat u) t)"
    have "Trm [DB (enat u) t] \<in> bwl_W u" by (rule bwl_2_8_principal[OF df])
    hence "Trm [DB (enat u) t] \<in> Wellfounded.acc RTrel"
      using bwl_acc_of_W[OF COF] by blast
    thus "DB (enat u) t \<in> Wellfounded.acc RPrel" by (rule bwl_acc_BP_of_BT)
  qed
qed

theorem bwl_wf_RPrel_of_cof:
  assumes COF: "bwl_cof"
  shows "wf RPrel"
  by (rule bwo_2_2_wf[OF bwl_Wstar_total_of_cof[OF COF]])

text \<open>\<^bold>\<open>Round-68 status.\<close>  The residual for \<open>wf RPrel\<close> is now the single statement
  \<open>bwl_cof\<close>: for \<open>OT\<^bsub>B\<^esub>\<close> terms \<open>b < a\<close>, the fundamental sequence of \<open>a\<close> reaches above
  \<open>b\<close> — \<open>\<exists>n. b \<le> a[n]\<close> when \<open>dom(a) \<in> {{0},\<nat>}\<close>, and \<open>\<exists>z \<in> W\<^sub>m \<inter> dom(a). b \<le> a[z]\<close> when
  \<open>dom(a) = T\<^sub>m\<close>.  Everything else in [Buc1] \<section>2 is now proved unconditionally.\<close>

(* ===== end r68 bwl part 6 (bridge; residual = bwl_cof, the Bachmann property) ===== *)


(* ===================================================================== *)
(* ===== r69 FINRC ROOT SURGERY (prefix ot9_): correction A9 fin-form === *)
(* =====   LastStep_def's Min-binder is now GUARDED by J < Lng (Br M). == *)
(* =====   Consequence: the whole fin/finM/FINRC cascade is PROVABLE.  == *)
(* ===================================================================== *)

text \<open>\<^bold>\<open>What changed (the only frozen-definition edit of the campaign).\<close>
  @{thm [source] LastStep_def} used to apply \<open>Min\<close> to the UNBOUNDED comprehension
  \<open>{J. (Br M)\<^bsub>J\<^sub>1,0,0\<^esub> = (Br M)\<^bsub>J,0,0\<^esub> \<and> (Br M)\<^bsub>J,1,0\<^esub> < (Br M)\<^bsub>J,0,0\<^esub>}\<close>, whereas the
  article's \<open>J\<close> is a \<^emph>\<open>branch index\<close> (\<open>0 \<dots> Lng (Br M) - 1\<close>).  Out of range,
  \<open>Br M ! J\<close> peels to \<open>[] ! (J - Lng (Br M))\<close> --- HOL-unspecified junk --- so the
  set was not provably finite, \<open>Min\<close> on an infinite set is junk, and every
  downstream fact had to carry an UNDISCHARGEABLE \<open>finite \<dots>\<close> side condition
  (\<open>fin\<close>/\<open>finM\<close>/\<open>FINRC\<close>, 129 occurrences).  \<open>LastStep_def\<close> now reads
  \<open>Min {J. J < Lng (Br M) \<and> \<dots>}\<close> (CORRECTION A9, fin-form), and the same guard was
  inserted verbatim into every one of those 129 comprehensions in \<open>pss_wip\<close>.

  \<^bold>\<open>FAITHFULNESS (no value changes on the intended domain).\<close>  The \<open>Br M = []\<close> and
  the diagonal (\<open>row-0 = row-1\<close>) branches are untouched.  In the else-branch, on
  any \<^emph>\<open>reduced\<close> host (@{thm [source] m_6_6_reduced_coeff}: \<open>row-1 \<le> row-0\<close>
  everywhere, hence \<open>\<noteq>\<close> gives \<open>row-1 < row-0\<close> at \<open>J\<^sub>1\<close>) the index \<open>J\<^sub>1\<close> itself
  lies in the guarded set, so \<open>Min\<close>\<open>(guarded) \<le> J\<^sub>1 < Lng (Br M)\<close>, while every
  element the OLD set had in addition is \<open>\<ge> Lng (Br M) > J\<^sub>1\<close>.  Therefore
  \<^bold>\<open>whenever the old set was finite --- i.e. exactly when the old \<open>Min\<close> was
  well-defined at all, which is precisely what the old \<open>fin\<close> hypotheses assumed
  --- the two \<open>Min\<close>s COINCIDE\<close>; where it was infinite the old value was HOL-junk.
  @{text ot9_LastStep_A9_faithful} machine-checks this: under the old \<open>fin\<close>
  hypothesis, the NEW \<open>LastStep\<close> equals the OLD definition's value verbatim.  So
  the edit is a disambiguation of the article's binder, not a semantic change,
  and no previously proven fact loses its meaning.\<close>

lemma ot9_LastStep_A9_faithful:
  \<comment> \<open>the new (guarded) \<open>LastStep\<close> agrees with the OLD (unguarded) definition on
      every host where the old one was well-defined (\<open>finU\<close> = the old \<open>fin\<close>).\<close>
  fixes M :: pairseq
  assumes Brne: "Br M \<noteq> []"
    and gt: "entry (Br M ! (Lng (Br M) - 1)) 1 0 < entry (Br M ! (Lng (Br M) - 1)) 0 0"
    and finU: "finite {J. entry (Br M ! (Lng (Br M) - 1)) 0 0 = entry (Br M ! J) 0 0
                          \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}"
  shows "LastStep M = Min {J. entry (Br M ! (Lng (Br M) - 1)) 0 0 = entry (Br M ! J) 0 0
                              \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}"
proof -
  let ?J1 = "Lng (Br M) - 1"
  let ?U = "{J. entry (Br M ! ?J1) 0 0 = entry (Br M ! J) 0 0
                \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}"
  let ?G = "{J. J < Lng (Br M) \<and> entry (Br M ! ?J1) 0 0 = entry (Br M ! J) 0 0
                \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}"
  have J1lt: "?J1 < Lng (Br M)" using Brne by (cases "Br M") auto
  have finG: "finite ?G" by (rule finite_subset[of _ "{..< Lng (Br M)}"]) auto
  have memG: "?J1 \<in> ?G" using gt J1lt by simp
  have Gne: "?G \<noteq> {}" using memG by blast
  have sub: "?G \<subseteq> ?U" by blast
  have LS: "LastStep M = Min ?G" by (rule vgx_LastStep_elsecase[OF Brne gt])
  have MGle: "Min ?G \<le> ?J1" using finG memG by (rule Min_le)
  have le1: "Min ?U \<le> Min ?G" by (rule Min_antimono[OF sub Gne finU])
  have Une: "?U \<noteq> {}" using Gne sub by blast
  have memU: "Min ?U \<in> ?U" using finU Une by (rule Min_in)
  have le2: "Min ?G \<le> Min ?U"
  proof (cases "Min ?U < Lng (Br M)")
    case True
    have "Min ?U \<in> ?G" using memU True by simp
    thus ?thesis by (rule Min_le[OF finG])
  next
    case False
    hence "Lng (Br M) \<le> Min ?U" by simp
    thus ?thesis using MGle J1lt by linarith
  qed
  have "Min ?G = Min ?U" using le1 le2 by simp
  thus ?thesis using LS by simp
qed

text \<open>\<^bold>\<open>FINRC, discharged.\<close>  With the A9 guard in place, @{const tvx_finRc} is the
  finiteness of a set of BRANCH INDICES of \<open>R\<^sub>c\<close>, hence a subset of
  \<open>{..< Lng (Br R\<^sub>c)}\<close>: finite UNCONDITIONALLY --- no host hypothesis at all.  This
  is the r61 brick @{thm [source] ot_finRc_bounded} now applying to the actual
  definition (its statement and this one are literally the same set).\<close>

lemma ot9_FINRC: "tvx_finRc K"
  unfolding tvx_finRc_def
  by (rule finite_subset[of _ "{..< Lng (Br (tvx_Rc K))}"]) auto

text \<open>\<^bold>\<open>CAPSTONE (r69).\<close>  @{thm [source] oi8_census_final_ivadmeq} with its
  \<open>FINRC\<close> slot DISCHARGED: both termination pillars (\<open>Trans M \<in> OT\<^bsub>B\<^esub>\<close> for all
  \<open>M \<in> ST\<^bsub>PS\<^esub>\<close>, and the fundamental-sequence descent \<open>Trans (M[n]) < Trans M\<close>) now
  hold modulo the single remaining census residual \<open>SETLE1_ltJ\<close>.\<close>

theorem oi8_census_FINRC:
  assumes SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have FINRC: "\<And>K. K \<in> ST_PS \<Longrightarrow> K \<in> PT_PS \<Longrightarrow> 1 < Lng K - 1 \<Longrightarrow>
             transCondII K \<Longrightarrow> tvx_finRc K"
    by (rule ot9_FINRC)
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi8_census_final_ivadmeq(1)[OF SETLE1 FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi8_census_final_ivadmeq(2)[OF SETLE1 FINRC])
qed

(* ===== end r69 FINRC root surgery (A9 fin-form): FINRC DISCHARGED ===== *)



(* ===================================================================== *)
(* ===== r69 (OPUS 4.8): the SURGERY TRANSPORT.  Prefix  ox9_.        ==== *)
(* =====                                                              ==== *)
(* ===== r68 proved the TRUE SOURCE of the SETLE1 descent             ==== *)
(* ===== (ox8_body_rspine_lessBT: every right-spine sub-body of       ==== *)
(* ===== body = bpHeadT (Trans (s84x_N M)) is < body, from the ONE    ==== *)
(* ===== Buchholz G-condition at the low enclosing head e3).  What    ==== *)
(* ===== SETLE1 actually needs is that comparison carried over to the ==== *)
(* ===== SURGERED trees  A1 = body[hole := D_ub A0],                  ==== *)
(* ===== X1 = body[hole := D_ub X0]  (hole = D_v1 0, ub = v1 - 1):    ==== *)
(* =====     lessBT (ox8_rsub A1 k) X1     (k >= 1).                  ==== *)
(* =====                                                              ==== *)
(* ===== STEP-0 (python/_r69_transport_step0{,b,c}.py; standard ST_PS ==== *)
(* ===== corpus, condIII/IV + hasParent + 1<Lng-1 + ltJ; 361/427      ==== *)
(* ===== hosts, 1117 peel levels):                                    ==== *)
(* =====  * lessBT (ox8_rsub A1 k) X1        : 1117/1117              ==== *)
(* =====  * lessBT (ox8_rsub body k) body    : 1117/1117 (= ox8)      ==== *)
(* =====  * r68's claim "every spine level of X1 above the hole is a  ==== *)
(* =====    PURE CHAIN" is FALSE on this corpus (14 hosts have a wide ==== *)
(* =====    hole level, 15 have a non-monotone width word), and the   ==== *)
(* =====    dangerous branch (C) below DOES occur (13/1117).  So the  ==== *)
(* =====    r68 assembly sketch (chain-ness) is NOT the right brick.  ==== *)
(* =====  * the TRUE brick: EVERY head occurring ANYWHERE in body is  ==== *)
(* =====    >= v1 (427/427 hosts; ox9_hge below).  With it the whole  ==== *)
(* =====    transport is elementary -- the surgery never flips a      ==== *)
(* =====    verdict, because the LEFT operand can never reach the     ==== *)
(* =====    RIGHT operand's leaf hole D_v1 0 (that would need a head  ==== *)
(* =====    < v1).  Run as a decision procedure the proof below       ==== *)
(* =====    closes 1117/1117 with 0 dangers.                          ==== *)
(* =====                                                              ==== *)
(* ===== So SETLE1 is REDUCED, unconditionally, to the single local   ==== *)
(* ===== head-bound  ox9_hge (enat v1) (bpHeadT (Trans (s84x_N M)))   ==== *)
(* ===== -- a Trans-image geometry fact, NOT an OT fact (descP only   ==== *)
(* ===== bounds heads from below by the LAST head of their own list). ==== *)
(* ===================================================================== *)

section \<open>r69 ox9 --- the surgery transport\<close>

subsection \<open>(1) The all-heads bound \<open>ox9_hge\<close> and the hole relation \<open>ox9_holeD\<close>\<close>

text \<open>@{text ox9_hge} \<open>v t\<close>: EVERY \<open>D\<close>-index occurring anywhere in \<open>t\<close> is \<open>\<ge> v\<close>.
  This is the one census input the transport needs.  It is strictly stronger than
  @{thm [source] ox7_RightNodes_body_ge_v1} (which bounds only the RIGHT-SPINE
  heads); \<open>descP\<close> propagates the spine bound to the top-level principals of every
  spine level, but NOT into off-spine bodies -- and the transport's dangerous
  branch lives exactly there.\<close>

fun ox9_hge :: "enat \<Rightarrow> BT \<Rightarrow> bool" and ox9_hgeP :: "enat \<Rightarrow> BP \<Rightarrow> bool" where
  "ox9_hge v (Trm ps) = (\<forall>p \<in> set ps. ox9_hgeP v p)"
| "ox9_hgeP v (DB w b) = (v \<le> w \<and> ox9_hge v b)"

text \<open>\<^bold>\<open>CORRECTION (r69 STEP-0d).\<close>  @{const ox9_hge} \<open>v\<^sub>1 body\<close> is \<^bold>\<open>FALSE\<close> on the
  census: 2/425 deep standard hosts carry a head \<open>< v\<^sub>1\<close> inside \<open>body\<close> (e.g.
  \<open>M = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,0)(6,1)(7,2)(8,0)(7,1)(8,1)\<close>, where
  \<open>v\<^sub>1 = 1\<close> and \<open>D\<^sub>0 0\<close> occurs in \<open>body\<close>).  But the transport survives, because such
  a small head appears only with a body that is \<^emph>\<open>below the surgery filler\<close>
  \<open>X\<^sub>0 = D\<^bsub>ub\<^esub>0\<close>: the comparison against the lowered hole \<open>D\<^bsub>ub\<^esub>X\<^sub>0\<close> is then still
  won on the SECOND component.  \<open>ox9_ok\<close> below is exactly that weakening --- and
  it is what the base case of @{text ox9_TT} actually needs.\<close>

fun ox9_ok :: "enat \<Rightarrow> enat \<Rightarrow> BT \<Rightarrow> bool"
  and ox9_okP :: "enat \<Rightarrow> enat \<Rightarrow> BP \<Rightarrow> bool" where
  "ox9_ok v ub (Trm ps) = (\<forall>p \<in> set ps. ox9_okP v ub p)"
| "ox9_okP v ub (DB w b) = ((v \<le> w \<or> lessBT b (Dpt ub 0\<^sub>B)) \<and> ox9_ok v ub b)"

lemma ox9_ok_of_hge: "ox9_hge v t \<Longrightarrow> ox9_ok v ub t"
  and ox9_okP_of_hgeP: "ox9_hgeP v p \<Longrightarrow> ox9_okP v ub p"
  by (induct t and p rule: ox9_hge_ox9_hgeP.induct) auto

text \<open>@{text ox9_holeD} \<open>e p q t t'\<close>: \<open>t'\<close> is \<open>t\<close> with its deepest-right principal
  \<open>p\<close> replaced by \<open>q\<close>, the hole sitting at right-spine depth \<open>e\<close>.  This is the
  structural content of the flat surgery \<open>flat t = s \<frown> flat p \<frown> b\<close>,
  \<open>flat t' = s \<frown> flat q \<frown> b\<close> (\<open>b\<close> all-\<open>RP\<close>) -- see
  @{text ox9_holeD_of_flat3} below, which reads it off @{thm [source] otx2_align3}.\<close>

inductive ox9_holeD :: "nat \<Rightarrow> BP \<Rightarrow> BP \<Rightarrow> BT \<Rightarrow> BT \<Rightarrow> bool" where
  ox9_hD0: "ox9_holeD 0 p q (Trm (ps @ [p])) (Trm (ps @ [q]))"
| ox9_hDS: "ox9_holeD k p q b b'
     \<Longrightarrow> ox9_holeD (Suc k) p q (Trm (ps @ [DB w b])) (Trm (ps @ [DB w b']))"

lemma ox9_holeD_0E:
  assumes "ox9_holeD 0 p q t t'"
  obtains ps where "t = Trm (ps @ [p])" and "t' = Trm (ps @ [q])"
  using assms by (cases rule: ox9_holeD.cases) auto

lemma ox9_holeD_SucE:
  assumes "ox9_holeD (Suc e) p q t t'"
  obtains ps w b b' where "t = Trm (ps @ [DB w b])" and "t' = Trm (ps @ [DB w b'])"
    and "ox9_holeD e p q b b'"
  using assms by (cases rule: ox9_holeD.cases) auto

lemma ox9_holeD_ne:
  assumes "ox9_holeD e p q t t'"
  shows "t \<noteq> 0\<^sub>B"
  using assms by (cases rule: ox9_holeD.cases) auto


subsection \<open>(2) Elementary \<open>lessBT\<close> / \<open>lessBP\<close> facts\<close>

lemma ox9_lessBT_zero: "\<not> lessBT t 0\<^sub>B"
proof (cases t)
  case (Trm ps) thus ?thesis by (cases ps) auto
qed

lemma ox9_lessBP_iff: "lessBP a b \<longleftrightarrow> lessBT (Trm [a]) (Trm [b])" by simp

lemma ox9_lessBP_trans: "lessBP a b \<Longrightarrow> lessBP b c \<Longrightarrow> lessBP a c"
  using lessBT_trans[of "Trm [a]" "Trm [b]" "Trm [c]"] by simp

text \<open>The surgery at a shared position strictly lowers, at the list level and at
  the tree level.\<close>

lemma ox9_snoc_lessBT: "lessBP q p \<Longrightarrow> lessBT (Trm (ps @ [q])) (Trm (ps @ [p]))"
  by (induct ps) auto

lemma ox9_holeD_lessBT:
  "ox9_holeD e p q t t' \<Longrightarrow> lessBP q p \<Longrightarrow> lessBT t' t"
proof (induction e p q t t' rule: ox9_holeD.induct)
  case (ox9_hD0 p q ps)
  thus ?case by (simp add: ox9_snoc_lessBT)
next
  case (ox9_hDS k p q b b' ps w)
  have "lessBT b' b" using ox9_hDS.IH ox9_hDS.prems by simp
  hence "lessBP (DB w b') (DB w b)" by simp
  thus ?case by (simp add: ox9_snoc_lessBT)
qed


subsection \<open>(3) The one-sided transport \<open>ox9_TT\<close>: a tree all of whose heads are
  \<open>\<ge> v\<close> can NEVER reach the leaf hole \<open>D\<^sub>v 0\<close>\<close>

text \<open>@{text ox9_lexP}: the list-level walk with a hole ONLY in the right operand.
  The right operand's hole principal \<open>q\<close> is compared against a left principal only
  through the hypothesis \<open>HT\<close>; everything else is unchanged by the surgery, so the
  verdict transports verbatim.\<close>

lemma ox9_lexP:
  assumes HT: "\<And>x. ox9_okP v ub x \<Longrightarrow> lessBP x q \<Longrightarrow> lessBP x q'"
  shows "ox9_ok v ub (Trm xs) \<Longrightarrow> lessBT (Trm xs) (Trm (ys @ [q]))
         \<Longrightarrow> lessBT (Trm xs) (Trm (ys @ [q']))"
proof (induction ys arbitrary: xs)
  case Nil
  note P1 = Nil.prems(1) and P2 = Nil.prems(2)
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis by simp
  next
    case (Cons x xs')
    have hx: "ox9_okP v ub x" using P1 Cons by simp
    have "lessBP x q \<or> (x = q \<and> lessBT (Trm xs') 0\<^sub>B)" using P2 Cons by simp
    hence lx: "lessBP x q" using ox9_lessBT_zero by blast
    have "lessBP x q'" by (rule HT[OF hx lx])
    thus ?thesis using Cons by simp
  qed
next
  case (Cons y ys')
  note IH = Cons.IH and P1 = Cons.prems(1) and P2 = Cons.prems(2)
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis by simp
  next
    case (Cons x xs')
    have hxs: "ox9_ok v ub (Trm xs')" using P1 Cons by simp
    have "lessBP x y \<or> (x = y \<and> lessBT (Trm xs') (Trm (ys' @ [q])))"
      using P2 Cons by simp
    thus ?thesis
    proof
      assume "lessBP x y"
      thus ?thesis using Cons by simp
    next
      assume A: "x = y \<and> lessBT (Trm xs') (Trm (ys' @ [q]))"
      have "lessBT (Trm xs') (Trm (ys' @ [q']))" by (rule IH[OF hxs]) (use A in simp)
      thus ?thesis using Cons A by simp
    qed
  qed
qed

text \<open>@{text ox9_TT_aux}: the hole-replacement premise \<open>PX\<close> is carried through the
  induction (the relation's replacement \<open>q'\<close> is the SAME at every depth).  In the
  census it is discharged for \<open>q' = D\<^bsub>ub\<^esub>X\<^sub>0\<close> from @{const ox9_ok}: a left principal
  \<open>D\<^sub>c XB\<close> that reaches the leaf hole has \<open>c < v\<^sub>1\<close>, hence \<open>c \<le> ub\<close>, and
  @{const ox9_ok} then hands us \<open>XB < X\<^sub>0\<close> --- which decides \<open>D\<^sub>c XB < D\<^bsub>ub\<^esub>X\<^sub>0\<close> on
  the second component when \<open>c = ub\<close>.\<close>

lemma ox9_TT_aux:
  "ox9_holeD e p q' R R' \<Longrightarrow> p = DB v 0\<^sub>B
   \<Longrightarrow> (\<forall>x. ox9_okP v ub x \<longrightarrow> lessBP x (DB v 0\<^sub>B) \<longrightarrow> lessBP x q')
   \<Longrightarrow> ox9_ok v ub L \<Longrightarrow> lessBT L R \<Longrightarrow> lessBT L R'"
proof (induction e p q' R R' arbitrary: L rule: ox9_holeD.induct)
  case (ox9_hD0 p q ps)
  have pd: "p = DB v 0\<^sub>B" using ox9_hD0.prems(1) by simp
  have HT: "\<And>x. ox9_okP v ub x \<Longrightarrow> lessBP x p \<Longrightarrow> lessBP x q"
    using ox9_hD0.prems(2) pd by blast
  obtain xs where Lx: "L = Trm xs" by (cases L)
  have hge: "ox9_ok v ub (Trm xs)" using ox9_hD0.prems(3) Lx by simp
  have lt: "lessBT (Trm xs) (Trm (ps @ [p]))" using ox9_hD0.prems(4) Lx by simp
  show ?case using ox9_lexP[OF HT hge lt] Lx by simp
next
  case (ox9_hDS k p q b b' ps w)
  have pd: "p = DB v 0\<^sub>B" using ox9_hDS.prems(1) by simp
  have PX: "\<forall>x. ox9_okP v ub x \<longrightarrow> lessBP x (DB v 0\<^sub>B) \<longrightarrow> lessBP x q"
    using ox9_hDS.prems(2) by simp
  have HT: "\<And>x. ox9_okP v ub x \<Longrightarrow> lessBP x (DB w b) \<Longrightarrow> lessBP x (DB w b')"
  proof -
    fix x assume hx: "ox9_okP v ub x" and lx: "lessBP x (DB w b)"
    obtain c XB where xc: "x = DB c XB" by (cases x)
    have hXB: "ox9_ok v ub XB" using hx xc by simp
    have "c < w \<or> (c = w \<and> lessBT XB b)" using lx xc by simp
    thus "lessBP x (DB w b')"
    proof
      assume "c < w" thus ?thesis using xc by simp
    next
      assume A: "c = w \<and> lessBT XB b"
      have "lessBT XB b'" by (rule ox9_hDS.IH[OF pd PX hXB]) (use A in simp)
      thus ?thesis using xc A by simp
    qed
  qed
  obtain xs where Lx: "L = Trm xs" by (cases L)
  have hge: "ox9_ok v ub (Trm xs)" using ox9_hDS.prems(3) Lx by simp
  have lt: "lessBT (Trm xs) (Trm (ps @ [DB w b]))" using ox9_hDS.prems(4) Lx by simp
  show ?case using ox9_lexP[OF HT hge lt] Lx by simp
qed

lemma ox9_TT:
  assumes hd: "ox9_holeD e (DB v 0\<^sub>B) q' R R'"
    and PX: "\<And>x. ox9_okP v ub x \<Longrightarrow> lessBP x (DB v 0\<^sub>B) \<Longrightarrow> lessBP x q'"
    and hge: "ox9_ok v ub L" and lt: "lessBT L R"
  shows "lessBT L R'"
  using ox9_TT_aux[OF hd refl _ hge lt] PX by blast


subsection \<open>(4) The two-sided transport \<open>ox9_MAIN\<close>\<close>

text \<open>@{text ox9_lexM}: the list-level lock-step walk, with a hole in the last
  principal of BOTH operands.  Three principal-level side conditions:
  \<open>PD\<close> (the two hole principals meet), \<open>PB\<close> (the left hole principal meets a
  hole-free right principal -- the surgery LOWERS the left, so the verdict is
  preserved), \<open>PC\<close> (a hole-free left principal meets the right hole principal --
  the surgery LOWERS the right, so a flip is a priori possible; this is the one
  dangerous branch, discharged by @{thm [source] ox9_TT}).\<close>

lemma ox9_lexM:
  assumes PD: "lessBP pL pR \<Longrightarrow> lessBP pL' pR'"
    and PB: "\<And>y. lessBP pL y \<or> pL = y \<Longrightarrow> lessBP pL' y"
    and PC: "\<And>x. ox9_okP v ub x \<Longrightarrow> lessBP x pR \<Longrightarrow> lessBP x pR'"
  shows "ox9_ok v ub (Trm xs) \<Longrightarrow> lessBT (Trm (xs @ [pL])) (Trm (ys @ [pR]))
         \<Longrightarrow> lessBT (Trm (xs @ [pL'])) (Trm (ys @ [pR']))"
proof (induction ys arbitrary: xs)
  case Nil
  note P1 = Nil.prems(1) and P2 = Nil.prems(2)
  show ?case
  proof (cases xs)
    case Nil
    have "lessBP pL pR" using P2 Nil by simp
    thus ?thesis using PD Nil by simp
  next
    case (Cons x xs')
    have hx: "ox9_okP v ub x" using P1 Cons by simp
    have "lessBP x pR \<or> (x = pR \<and> lessBT (Trm (xs' @ [pL])) 0\<^sub>B)"
      using P2 Cons by simp
    hence lx: "lessBP x pR" using ox9_lessBT_zero by blast
    have "lessBP x pR'" by (rule PC[OF hx lx])
    thus ?thesis using Cons by simp
  qed
next
  case (Cons y ys')
  note IH = Cons.IH and P1 = Cons.prems(1) and P2 = Cons.prems(2)
  show ?case
  proof (cases xs)
    case Nil
    have "lessBP pL y \<or> (pL = y \<and> lessBT 0\<^sub>B (Trm (ys' @ [pR])))"
      using P2 Nil by simp
    hence "lessBP pL y \<or> pL = y" by blast
    hence "lessBP pL' y" by (rule PB)
    thus ?thesis using Nil by simp
  next
    case (Cons x xs')
    have hxs: "ox9_ok v ub (Trm xs')" using P1 Cons by simp
    have "lessBP x y \<or> (x = y \<and> lessBT (Trm (xs' @ [pL])) (Trm (ys' @ [pR])))"
      using P2 Cons by simp
    thus ?thesis
    proof
      assume "lessBP x y"
      thus ?thesis using Cons by simp
    next
      assume A: "x = y \<and> lessBT (Trm (xs' @ [pL])) (Trm (ys' @ [pR]))"
      have "lessBT (Trm (xs' @ [pL'])) (Trm (ys' @ [pR']))"
        by (rule IH[OF hxs]) (use A in simp)
      thus ?thesis using Cons A by simp
    qed
  qed
qed

text \<open>@{text ox9_MAIN}: THE TRANSPORT.  \<open>WB\<close> carries the hole at right-spine depth
  \<open>dR\<close>, \<open>tB\<close> (a STRICTLY deeper right-spine sub-body of the same tree) at depth
  \<open>dL < dR\<close>; \<open>WX = WB[hole := pX]\<close>, \<open>tA = tB[hole := pA]\<close>, both surgeries strictly
  lowering (\<open>pA, pX < D\<^bsub>v\<^sub>1\<^esub>0\<close>).  If every head of \<open>tB\<close> is \<open>\<ge> v\<^sub>1\<close> then
  \<open>lessBT tB WB\<close> transports to \<open>lessBT tA WX\<close>.

  \<open>dL < dR\<close> is what makes the RIGHT operand's hole principal a genuine spine
  principal \<open>D\<^bsub>w\<^esub>RB\<close> (never the leaf \<open>D\<^bsub>v\<^sub>1\<^esub>0\<close>): its HEAD is untouched by the
  surgery, so the head comparison transports and only the body recursion is left.
  The left operand's leaf case (\<open>dL = 0\<close>) is decided outright: \<open>lessBP (D\<^bsub>v\<^sub>1\<^esub>0) pR\<close>
  forces \<open>v\<^sub>1 \<le> w\<close>, and \<open>pA\<close>'s head is \<open>< v\<^sub>1 \<le> w\<close>.\<close>

lemma ox9_MAIN:
  fixes v1 ub :: enat
  assumes PXOK: "\<And>x. ox9_okP v1 ub x \<Longrightarrow> lessBP x (DB v1 0\<^sub>B) \<Longrightarrow> lessBP x pX"
  shows "ox9_holeD dR (DB v1 0\<^sub>B) pX WB WX \<Longrightarrow>
         ox9_holeD dL (DB v1 0\<^sub>B) pA tB tA \<Longrightarrow>
         lessBP pA (DB v1 0\<^sub>B) \<Longrightarrow> dL < dR \<Longrightarrow>
         ox9_ok v1 ub tB \<Longrightarrow> lessBT tB WB \<Longrightarrow> lessBT tA WX"
proof (induction dR arbitrary: dL WB WX tB tA rule: less_induct)
  case (less dR)
  note hdR = less.prems(1) and hdL = less.prems(2) and pAlt = less.prems(3)
    and dlt = less.prems(4) and hge = less.prems(5) and lt = less.prems(6)
  obtain e where dRe: "dR = Suc e" using dlt by (cases dR) auto
  have hdR': "ox9_holeD (Suc e) (DB v1 0\<^sub>B) pX WB WX" using hdR dRe by simp
  obtain ys wR RB RB' where
      WBd: "WB = Trm (ys @ [DB wR RB])" and WXd: "WX = Trm (ys @ [DB wR RB'])"
    and hdRB: "ox9_holeD e (DB v1 0\<^sub>B) pX RB RB'"
    by (rule ox9_holeD_SucE[OF hdR'])
  \<comment> \<open>the dangerous branch (C), discharged by @{thm [source] ox9_TT}\<close>
  have PC: "\<And>x. ox9_okP v1 ub x \<Longrightarrow> lessBP x (DB wR RB) \<Longrightarrow> lessBP x (DB wR RB')"
  proof -
    fix x assume hx: "ox9_okP v1 ub x" and lx: "lessBP x (DB wR RB)"
    obtain c XB where xc: "x = DB c XB" by (cases x)
    have hXB: "ox9_ok v1 ub XB" using hx xc by simp
    have "c < wR \<or> (c = wR \<and> lessBT XB RB)" using lx xc by simp
    thus "lessBP x (DB wR RB')"
    proof
      assume "c < wR" thus ?thesis using xc by simp
    next
      assume A: "c = wR \<and> lessBT XB RB"
      have ltXB: "lessBT XB RB" using A by simp
      have "lessBT XB RB'" by (rule ox9_TT[OF hdRB PXOK hXB ltXB])
      thus ?thesis using xc A by simp
    qed
  qed
  show ?case
  proof (cases dL)
    case 0
    have hdL': "ox9_holeD 0 (DB v1 0\<^sub>B) pA tB tA" using hdL 0 by simp
    obtain xs where tBd: "tB = Trm (xs @ [DB v1 0\<^sub>B])" and tAd: "tA = Trm (xs @ [pA])"
      by (rule ox9_holeD_0E[OF hdL'])
    obtain c A0 where pAc: "pA = DB c A0" by (cases pA)
    have cv: "c < v1"
    proof -
      have "c < v1 \<or> (c = v1 \<and> lessBT A0 0\<^sub>B)" using pAlt pAc by simp
      thus ?thesis using ox9_lessBT_zero by blast
    qed
    have PD: "lessBP (DB v1 0\<^sub>B) (DB wR RB) \<Longrightarrow> lessBP pA (DB wR RB')"
    proof -
      assume "lessBP (DB v1 0\<^sub>B) (DB wR RB)"
      hence "v1 < wR \<or> (v1 = wR \<and> lessBT 0\<^sub>B RB)" by simp
      hence "v1 \<le> wR" by auto
      hence "c < wR" using cv by simp
      thus "lessBP pA (DB wR RB')" using pAc by simp
    qed
    have PB: "\<And>y. lessBP (DB v1 0\<^sub>B) y \<or> (DB v1 0\<^sub>B) = y \<Longrightarrow> lessBP pA y"
    proof -
      fix y assume "lessBP (DB v1 0\<^sub>B) y \<or> (DB v1 0\<^sub>B) = y"
      thus "lessBP pA y"
      proof
        assume "lessBP (DB v1 0\<^sub>B) y"
        thus ?thesis using ox9_lessBP_trans[OF pAlt] by blast
      next
        assume "(DB v1 0\<^sub>B) = y"
        thus ?thesis using pAlt by simp
      qed
    qed
    have hgex: "ox9_ok v1 ub (Trm xs)" using hge tBd by simp
    have lt': "lessBT (Trm (xs @ [DB v1 0\<^sub>B])) (Trm (ys @ [DB wR RB]))"
      using lt tBd WBd by simp
    have "lessBT (Trm (xs @ [pA])) (Trm (ys @ [DB wR RB']))"
      by (rule ox9_lexM[OF PD PB PC hgex lt'])
    thus ?thesis using tAd WXd by simp
  next
    case (Suc eL)
    have hdL': "ox9_holeD (Suc eL) (DB v1 0\<^sub>B) pA tB tA" using hdL Suc by simp
    obtain xs wL LB LA where
        tBd: "tB = Trm (xs @ [DB wL LB])" and tAd: "tA = Trm (xs @ [DB wL LA])"
      and hdLB: "ox9_holeD eL (DB v1 0\<^sub>B) pA LB LA"
      by (rule ox9_holeD_SucE[OF hdL'])
    have hLB: "ox9_ok v1 ub LB" using hge tBd by simp
    have eLe: "eL < e" using dlt Suc dRe by simp
    have PD: "lessBP (DB wL LB) (DB wR RB) \<Longrightarrow> lessBP (DB wL LA) (DB wR RB')"
    proof -
      assume "lessBP (DB wL LB) (DB wR RB)"
      hence "wL < wR \<or> (wL = wR \<and> lessBT LB RB)" by simp
      thus "lessBP (DB wL LA) (DB wR RB')"
      proof
        assume "wL < wR" thus ?thesis by simp
      next
        assume A: "wL = wR \<and> lessBT LB RB"
        have "lessBT LA RB'"
          by (rule less.IH[OF _ hdRB hdLB pAlt eLe hLB]) (use A eLe dRe in simp_all)
        thus ?thesis using A by simp
      qed
    qed
    have lowLA: "lessBT LA LB" by (rule ox9_holeD_lessBT[OF hdLB pAlt])
    have PB: "\<And>y. lessBP (DB wL LB) y \<or> (DB wL LB) = y \<Longrightarrow> lessBP (DB wL LA) y"
    proof -
      fix y assume H: "lessBP (DB wL LB) y \<or> (DB wL LB) = y"
      have low: "lessBP (DB wL LA) (DB wL LB)" using lowLA by simp
      from H show "lessBP (DB wL LA) y"
      proof
        assume "lessBP (DB wL LB) y"
        thus ?thesis using ox9_lessBP_trans[OF low] by blast
      next
        assume "(DB wL LB) = y"
        thus ?thesis using low by simp
      qed
    qed
    have hgex: "ox9_ok v1 ub (Trm xs)" using hge tBd by simp
    have lt': "lessBT (Trm (xs @ [DB wL LB])) (Trm (ys @ [DB wR RB]))"
      using lt tBd WBd by simp
    have "lessBT (Trm (xs @ [DB wL LA])) (Trm (ys @ [DB wR RB']))"
      by (rule ox9_lexM[OF PD PB PC hgex lt'])
    thus ?thesis using tAd WXd by simp
  qed
qed


subsection \<open>(5) Reading \<open>ox9_holeD\<close> off the flat surgery, and descending it\<close>

text \<open>@{text ox9_holeD_of_flat3}: the flat-level surgery data of the census (one
  body \<open>t\<close>, two replacements \<open>q\<^sub>1, q\<^sub>2\<close> at the SAME wrapper \<open>(s,b)\<close>) yields the two
  structural hole relations at the SAME depth -- by iterating
  @{thm [source] otx2_align3}, which is exactly the right-spine peel.\<close>

lemma ox9_holeD_of_flat3:
  "flatBT t = s @ flatBP p @ b \<Longrightarrow> flatBT t1 = s @ flatBP q1 @ b \<Longrightarrow>
   flatBT t2 = s @ flatBP q2 @ b \<Longrightarrow> (\<forall>x \<in> set b. x = RP) \<Longrightarrow>
   \<exists>e. ox9_holeD e p q1 t t1 \<and> ox9_holeD e p q2 t t2"
proof (induction t arbitrary: t1 t2 s b rule: measure_induct_rule[where f=size])
  case (less t)
  from otx2_align3[OF less.prems(1) less.prems(2) less.prems(3) less.prems(4)]
  show ?case
  proof (elim disjE exE conjE)
    fix qs
    assume T: "t = Trm (qs @ [p])" and T1: "t1 = Trm (qs @ [q1])"
      and T2: "t2 = Trm (qs @ [q2])"
    have "ox9_holeD 0 p q1 t t1 \<and> ox9_holeD 0 p q2 t t2"
      using T T1 T2 by (simp add: ox9_holeD.ox9_hD0)
    thus ?thesis by blast
  next
    fix qs w lb1 lb2 lb3 sc bc
    assume T: "t = Trm (qs @ [DB w lb1])" and T1: "t1 = Trm (qs @ [DB w lb2])"
      and T2: "t2 = Trm (qs @ [DB w lb3])"
      and F: "flatBT lb1 = sc @ flatBP p @ bc"
      and F1: "flatBT lb2 = sc @ flatBP q1 @ bc"
      and F2: "flatBT lb3 = sc @ flatBP q2 @ bc"
      and BC: "\<forall>x \<in> set bc. x = RP"
    have pin: "DB w lb1 \<in> set (qs @ [DB w lb1])" by simp
    have szp: "size (DB w lb1) \<le> size_list size (qs @ [DB w lb1])"
      by (rule size_list_estimation'[OF pin order_refl])
    have szlt: "size lb1 < size t" using szp T by simp
    from less.IH[OF szlt F F1 F2 BC] obtain e where
      E: "ox9_holeD e p q1 lb1 lb2 \<and> ox9_holeD e p q2 lb1 lb3" by blast
    have "ox9_holeD (Suc e) p q1 t t1 \<and> ox9_holeD (Suc e) p q2 t t2"
      using E T T1 T2 by (simp add: ox9_holeD.ox9_hDS)
    thus ?thesis by blast
  qed
qed

lemma ox9_rsub_Suc: "ox8_rsub t (Suc k) = ox8_lastT (ox8_rsub t k)"
proof (induction k arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc k)
  have "ox8_rsub t (Suc (Suc k)) = ox8_rsub (ox8_lastT t) (Suc k)" by simp
  also have "\<dots> = ox8_lastT (ox8_rsub (ox8_lastT t) k)" by (rule Suc.IH)
  also have "\<dots> = ox8_lastT (ox8_rsub t (Suc k))" by simp
  finally show ?case .
qed

lemma ox9_holeD_lastT:
  assumes "ox9_holeD (Suc e) p q t t'"
  shows "ox9_holeD e p q (ox8_lastT t) (ox8_lastT t')"
proof -
  obtain ps w b b' where T: "t = Trm (ps @ [DB w b])" and T': "t' = Trm (ps @ [DB w b'])"
    and H: "ox9_holeD e p q b b'"
    by (rule ox9_holeD_SucE[OF assms])
  have "ox8_lastT t = b" using T by simp
  moreover have "ox8_lastT t' = b'" using T' by simp
  ultimately show ?thesis using H by simp
qed

lemma ox9_holeD_rsub:
  "ox9_holeD dR p q t t' \<Longrightarrow> k \<le> dR
   \<Longrightarrow> ox9_holeD (dR - k) p q (ox8_rsub t k) (ox8_rsub t' k)"
proof (induction k arbitrary: t t' dR)
  case 0 thus ?case by simp
next
  case (Suc k)
  obtain e where dRe: "dR = Suc e" using Suc.prems(2) by (cases dR) auto
  have H: "ox9_holeD (Suc e) p q t t'" using Suc.prems(1) dRe by simp
  have step: "ox9_holeD e p q (ox8_lastT t) (ox8_lastT t')"
    by (rule ox9_holeD_lastT[OF H])
  have kle: "k \<le> e" using Suc.prems(2) dRe by simp
  have IH: "ox9_holeD (e - k) p q (ox8_rsub (ox8_lastT t) k) (ox8_rsub (ox8_lastT t') k)"
    by (rule Suc.IH[OF step kle])
  have r1: "ox8_rsub t (Suc k) = ox8_rsub (ox8_lastT t) k" by simp
  have r2: "ox8_rsub t' (Suc k) = ox8_rsub (ox8_lastT t') k" by simp
  have "dR - Suc k = e - k" using dRe by simp
  thus ?case using IH r1 r2 by simp
qed

lemma ox9_ok_lastT: "ox9_ok v ub t \<Longrightarrow> ox9_ok v ub (ox8_lastT t)"
proof -
  assume H: "ox9_ok v ub t"
  obtain ps where T: "t = Trm ps" by (cases t)
  show ?thesis
  proof (cases "ps = []")
    case True thus ?thesis using T by simp
  next
    case False
    obtain w b where lp: "last ps = DB w b" by (cases "last ps")
    have mem: "DB w b \<in> set ps" using False lp by (metis last_in_set)
    have hall: "\<forall>p \<in> set ps. ox9_okP v ub p" using H T by simp
    have "ox9_okP v ub (DB w b)" using hall mem by blast
    hence "ox9_ok v ub b" by simp
    moreover have "ox8_lastT t = b" using T False lp by simp
    ultimately show ?thesis by simp
  qed
qed

lemma ox9_ok_rsub: "ox9_ok v ub t \<Longrightarrow> ox9_ok v ub (ox8_rsub t k)"
proof (induction k arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc k)
  have "ox9_ok v ub (ox8_lastT t)" by (rule ox9_ok_lastT[OF Suc.prems])
  thus ?case using Suc.IH by simp
qed


subsection \<open>(6) The re-threaded SETLE engine \<open>ox9_engine\<close>\<close>

text \<open>@{text ox9_engine}: the right-spine peel of @{thm [source] ox6_setle_scbext_restr},
  re-threaded so that at every level the three trees are the ITERATED RIGHT-SPINE
  SUB-BODIES \<open>ox8_rsub WB k\<close> / \<open>ox8_rsub A\<^sub>1 k\<close> / \<open>ox8_rsub X\<^sub>1 k\<close> of the surgery
  triple.  That is exactly the data the residual needs: the spine descent
  \<open>DESC\<close> (= @{thm [source] ox8_body_rspine_lessBT}) and the transport
  @{thm [source] ox9_MAIN} then close the ancestor bound \<open>leBT (ox8_rsub A\<^sub>1 k) X\<^sub>1\<close>
  outright -- no \<open>spineH\<close> residual is left.\<close>

lemma ox9_engine:
  fixes u v1 ub :: enat and WB A1 X1 :: BT and pA pX :: BP
  assumes holeH: "b1x_setle (GBP u pA) (insert X1 (GBT u X1))"
    and hdA: "ox9_holeD dR (DB v1 0\<^sub>B) pA WB A1"
    and hdX: "ox9_holeD dR (DB v1 0\<^sub>B) pX WB X1"
    and pAlt: "lessBP pA (DB v1 0\<^sub>B)"
    and PXOK: "\<And>x. ox9_okP v1 ub x \<Longrightarrow> lessBP x (DB v1 0\<^sub>B) \<Longrightarrow> lessBP x pX"
    and hgeB: "ox9_ok v1 ub WB"
    and DESC: "\<And>k. 1 \<le> k \<Longrightarrow> k \<le> dR \<Longrightarrow> lessBT (ox8_rsub WB k) WB"
  shows "dR - k = m \<Longrightarrow> k \<le> dR \<Longrightarrow> GBT u (ox8_rsub X1 k) \<subseteq> GBT u X1
         \<Longrightarrow> b1x_setle (GBT u (ox8_rsub A1 k)) (insert X1 (GBT u X1))"
proof (induction m arbitrary: k rule: less_induct)
  case (less m)
  note mk = less.prems(1) and kle = less.prems(2) and subX = less.prems(3)
  have hdAk: "ox9_holeD (dR - k) (DB v1 0\<^sub>B) pA (ox8_rsub WB k) (ox8_rsub A1 k)"
    by (rule ox9_holeD_rsub[OF hdA kle])
  have hdXk: "ox9_holeD (dR - k) (DB v1 0\<^sub>B) pX (ox8_rsub WB k) (ox8_rsub X1 k)"
    by (rule ox9_holeD_rsub[OF hdX kle])
  show ?case
  proof (cases "dR - k")
    case 0
    \<comment> \<open>the hole is the last top-level principal of this level\<close>
    have hA: "ox9_holeD 0 (DB v1 0\<^sub>B) pA (ox8_rsub WB k) (ox8_rsub A1 k)"
      using hdAk 0 by simp
    have hX: "ox9_holeD 0 (DB v1 0\<^sub>B) pX (ox8_rsub WB k) (ox8_rsub X1 k)"
      using hdXk 0 by simp
    obtain ps where WBk: "ox8_rsub WB k = Trm (ps @ [DB v1 0\<^sub>B])"
      and A1k: "ox8_rsub A1 k = Trm (ps @ [pA])"
      by (rule ox9_holeD_0E[OF hA])
    obtain ps' where WBk': "ox8_rsub WB k = Trm (ps' @ [DB v1 0\<^sub>B])"
      and X1k: "ox8_rsub X1 k = Trm (ps' @ [pX])"
      by (rule ox9_holeD_0E[OF hX])
    have pseq: "ps = ps'" using WBk WBk' by simp
    have qsub: "(\<Union>q \<in> set ps. GBP u q) \<subseteq> GBT u X1"
    proof -
      have "(\<Union>q \<in> set ps. GBP u q) \<subseteq> GBT u (ox8_rsub X1 k)" using X1k pseq by auto
      thus ?thesis using subX by blast
    qed
    show ?thesis
      unfolding b1x_setle_def
    proof
      fix x assume xin: "x \<in> GBT u (ox8_rsub A1 k)"
      have "x \<in> (\<Union>q \<in> set ps. GBP u q) \<or> x \<in> GBP u pA" using xin A1k by auto
      thus "\<exists>y \<in> insert X1 (GBT u X1). leBT x y"
      proof
        assume "x \<in> (\<Union>q \<in> set ps. GBP u q)"
        hence "x \<in> GBT u X1" using qsub by blast
        thus ?thesis by blast
      next
        assume "x \<in> GBP u pA"
        thus ?thesis using holeH unfolding b1x_setle_def by blast
      qed
    qed
  next
    case (Suc e)
    have hA: "ox9_holeD (Suc e) (DB v1 0\<^sub>B) pA (ox8_rsub WB k) (ox8_rsub A1 k)"
      using hdAk Suc by simp
    have hX: "ox9_holeD (Suc e) (DB v1 0\<^sub>B) pX (ox8_rsub WB k) (ox8_rsub X1 k)"
      using hdXk Suc by simp
    obtain ps w LB LA where WBk: "ox8_rsub WB k = Trm (ps @ [DB w LB])"
      and A1k: "ox8_rsub A1 k = Trm (ps @ [DB w LA])"
      and hdLB: "ox9_holeD e (DB v1 0\<^sub>B) pA LB LA"
      by (rule ox9_holeD_SucE[OF hA])
    obtain ps' w' LB' LX where WBk': "ox8_rsub WB k = Trm (ps' @ [DB w' LB'])"
      and X1k: "ox8_rsub X1 k = Trm (ps' @ [DB w' LX])"
      by (rule ox9_holeD_SucE[OF hX])
    have pseq: "ps = ps' \<and> w = w' \<and> LB = LB'" using WBk WBk' by simp
    \<comment> \<open>the three peels are the next right-spine sub-bodies\<close>
    have rB: "ox8_rsub WB (Suc k) = LB" using ox9_rsub_Suc[of WB k] WBk by simp
    have rA: "ox8_rsub A1 (Suc k) = LA" using ox9_rsub_Suc[of A1 k] A1k by simp
    have rX: "ox8_rsub X1 (Suc k) = LX" using ox9_rsub_Suc[of X1 k] X1k by simp
    have kSle: "Suc k \<le> dR" using kle Suc by simp
    have hLB: "ox9_ok v1 ub LB" using ox9_ok_rsub[OF hgeB, of "Suc k"] rB by simp
    have descLB: "lessBT LB WB" using DESC[of "Suc k"] kSle rB by simp
    have eLdR: "e < dR" using Suc kle by simp
    \<comment> \<open>the ancestor bound at this level: the TRANSPORT\<close>
    have leLA: "leBT LA X1"
    proof -
      have "lessBT LA X1"
        by (rule ox9_MAIN[OF PXOK hdX hdLB pAlt eLdR hLB descLB])
      thus ?thesis by blast
    qed
    have qsub: "(\<Union>q \<in> set ps. GBP u q) \<subseteq> GBT u X1"
    proof -
      have "(\<Union>q \<in> set ps. GBP u q) \<subseteq> GBT u (ox8_rsub X1 k)" using X1k pseq by auto
      thus ?thesis using subX by blast
    qed
    show ?thesis
      unfolding b1x_setle_def
    proof
      fix x assume xin: "x \<in> GBT u (ox8_rsub A1 k)"
      have "x \<in> (\<Union>q \<in> set ps. GBP u q) \<or> x \<in> GBP u (DB w LA)" using xin A1k by auto
      thus "\<exists>y \<in> insert X1 (GBT u X1). leBT x y"
      proof
        assume "x \<in> (\<Union>q \<in> set ps. GBP u q)"
        hence "x \<in> GBT u X1" using qsub by blast
        thus ?thesis by blast
      next
        assume xh: "x \<in> GBP u (DB w LA)"
        have uw: "u \<le> w" using xh by (auto split: if_split_asm)
        have xcase: "x = LA \<or> x \<in> GBT u LA" using xh by (auto split: if_split_asm)
        \<comment> \<open>the matched \<open>X\<close>-side sibling lies in \<open>G\<^sub>u X\<^sub>1\<close>, which re-threads the peel\<close>
        have LXin: "LX \<in> GBT u X1"
        proof -
          have "LX \<in> GBP u (DB w' LX)" using uw pseq by simp
          hence "LX \<in> GBT u (ox8_rsub X1 k)" using X1k by auto
          thus ?thesis using subX by blast
        qed
        have subX': "GBT u (ox8_rsub X1 (Suc k)) \<subseteq> GBT u X1"
          using b1x_GBT_trans[OF LXin] rX by simp
        from xcase show ?thesis
        proof
          assume "x = LA"
          thus ?thesis using leLA by blast
        next
          assume xLA: "x \<in> GBT u LA"
          have mlt: "dR - Suc k < m" using mk Suc by simp
          have IH: "b1x_setle (GBT u (ox8_rsub A1 (Suc k))) (insert X1 (GBT u X1))"
            by (rule less.IH[OF mlt refl kSle subX'])
          have "b1x_setle (GBT u LA) (insert X1 (GBT u X1))" using IH rA by simp
          thus ?thesis using xLA unfolding b1x_setle_def by blast
        qed
      qed
    qed
  qed
qed


subsection \<open>(7) The census \<open>SETLE1_ltJ\<close> slot, modulo the head bound --- WITHDRAWN (r72)\<close>

text \<open>\<^bold>\<open>r72 (corrected Buchholz fundamental sequence): the r69 \<open>ox9\<close> census route is
  WITHDRAWN.\<close>  \<open>ox9_SETLE1_ltJ\<close> / \<open>oi9_census_SETLE_ok\<close> / \<open>oi9_census_OKH\<close> and the two
  \<open>OKH\<close> capstones \<open>y3_PSS_acc_of_OKH_cofimg\<close> / \<open>y3_PSS_acc_of_OKH_bwl_cof\<close> lived on the
  hypothesis \<open>ALLH = ox9_ok v\<^sub>1 (v\<^sub>1-1) body\<close>, which r70 REFUTED
  (\<open>ox10_cex_not_ok\<close> below) --- so those census wrappers were already vacuous,
  and the live route is \<open>ox10\<close>/\<open>ox11\<close>/\<open>ox12\<close> (the \<open>KK\<close> spine bound).  Under the corrected
  rule the \<open>SETLE1\<close> slot's low donor core is \<open>Y\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 0\<^sub>B\<close> (the operB core
  is \<open>0\<^sub>B\<close>-seeded), and the \<open>ox9\<close> head-separation argument bounds an escape at head
  exactly \<open>ub\<close> only by \<open>D\<^bsub>ub\<^esub>0\<close>, never by \<open>0\<^sub>B\<close> --- it cannot reach the new bound.  The
  \<open>ox9_holeD\<close>/\<open>ox9_ok\<close>/\<open>ox9_lexP\<close> INFRASTRUCTURE is kept (\<open>ox10\<close>--\<open>ox12\<close> use it); only the
  four refuted-route wrappers are removed.  No live theorem depended on them
  (\<open>oi12_census\<close>, \<open>ox12_KK_free\<close>, \<open>y5_*\<close> all go through \<open>KK\<close>).\<close>

(* ===== end r69 ox9 block (census wrappers withdrawn in r72; engine kept) ===== *)

(* ===================================================================== *)
(* ===== r70 (OKH front).  STEP-0 verdict: the r69 census residual  ==== *)
(* =====   OKH  =  ox9_ok v1 (v1-1) (bpHeadT (Trans (s84x_N P)))    ==== *)
(* ===== is  FALSE.  So is the recommended route "leafcond".  Both  ==== *)
(* ===== die on the SAME witness, a genuine ST_PS census host:      ==== *)
(* =====                                                            ==== *)
(* =====  P = (0,0)(1,1)(2,1)(3,1)(4,0)(5,1)(6,1)(7,1)(8,0)(9,1)    ==== *)
(* =====      (10,1)(11,1)(11,0)(12,0)(10,1)(11,1)(10,1)(11,1)      ==== *)
(* =====                                                            ==== *)
(* ===== certified (python/_r70_okh_cex.py) to satisfy EVERY census ==== *)
(* ===== hypothesis: P in ST_PS (explicit oper chain from           ==== *)
(* ===== diagSeq 0 2, replayed), monoT (hence PT_PS), hasParent P 1 ==== *)
(* ===== (Lng P - 1), 1 < Lng P - 1, transCondIII P, Trans P in     ==== *)
(* ===== OT_B, s84x_jm3 P = 8 < 16 = transJm1 P.  For it            ==== *)
(* =====   v1 = 1,  ub = 0,  X0 = D_0 0,  pX = D_0 X0 = D_0(D_0 0)  ==== *)
(* =====   body = bpHeadT (Trans (s84x_N P))                        ==== *)
(* =====        = D_1((D_1((D_1 0, D_0(D_0 0))), D_1(D_1 0),        ==== *)
(* =====              D_1(D_1 0)))                                  ==== *)
(* ===== and body carries, OFF the right spine, the principal       ==== *)
(* =====   D_0 (D_0 0)  =  pX  EXACTLY.                             ==== *)
(* ===== Its head 0 < v1 = 1 and its body D_0 0 is NOT < X0 = D_0 0 ==== *)
(* ===== (they are EQUAL), so ox9_okP fails -- ox9_ok fails at      ==== *)
(* ===== EQUALITY with the surgery filler.  ox10_cex_not_ok below   ==== *)
(* ===== is the Isabelle check.  (ox9_hge and leafcond die a        ==== *)
(* ===== fortiori.)  Corpus: pure ST_PS (diagSeq + oper closure),   ==== *)
(* ===== maxlen 20, 542 census hosts / 1212 peel levels: 8 hosts    ==== *)
(* ===== refute ox9_ok.  (r69 saw 0 -- its walks were too short.)   ==== *)
(* ===== Hence theorem oi9_census_OKH is VACUOUS.                   ==== *)
(* =====                                                            ==== *)
(* ===== BUT the transport TARGET survives (1212/1212, 0 failures): ==== *)
(* ===== ox9_ok was only ever a SUFFICIENT condition, and it is     ==== *)
(* ===== strictly too strong -- it is a GLOBAL "every principal     ==== *)
(* ===== anywhere" guard, while ox9_lexP consumes it only at the    ==== *)
(* ===== hole-aligned positions of the tie path, which the bad      ==== *)
(* ===== principal never occupies (it lives in the body of a        ==== *)
(* ===== NON-last principal, off the right spine).                  ==== *)
(* =====                                                            ==== *)
(* ===== r70 route: ox9_ok/PXOK/DESC are consumed by ox9_engine     ==== *)
(* ===== ONLY to feed ox9_MAIN, whose ONLY output is                ==== *)
(* =====   leLA : leBT (ox8_rsub A1 (Suc k)) X1.                    ==== *)
(* ===== Take that as the hypothesis instead, and factor it:        ==== *)
(* =====   MONO(k): lessBT (ox8_rsub A1 k) (ox8_rsub WB k)          ==== *)
(* =====            -- ALREADY PROVEN (ox9_holeD_lessBT: the        ==== *)
(* =====               surgery pA < D_v1 0 lowers the tree)         ==== *)
(* =====   KK(k)  : lessBT (ox8_rsub WB k) X1                       ==== *)
(* =====            -- the UNSURGERED spine sub-body of the census  ==== *)
(* =====               body stays below the LOWERED body X1.        ==== *)
(* ===== KK is a Trans-image geometry fact with NO A0 and NO        ==== *)
(* ===== ox9_ok in it, and it is TRUE on the corpus (1212/1212,     ==== *)
(* ===== including all 8 ox9_ok-refuting hosts; python/_r70_key.py).==== *)
(* ===== ox10_engine below re-derives the whole census from KK.     ==== *)
(* ===================================================================== *)

section \<open>r70 ox10 --- OKH is FALSE; the census residual becomes the \<open>KK\<close> bound\<close>

subsection \<open>(1) The counterexample: \<open>ox9_ok\<close> fails at EQUALITY with the filler\<close>

text \<open>@{text ox10_cexBody} is \<open>bpHeadT (Trans (s84x_N P))\<close> for the census host \<open>P\<close>
  displayed above (python/_r70_okh_cex.py; \<open>v\<^sub>1 = 1\<close>, \<open>ub = 0\<close>).  It carries the
  principal \<open>D\<^sub>0(D\<^sub>0 0)\<close>, which is EXACTLY the surgery filler \<open>pX = D\<^bsub>ub\<^esub>X\<^sub>0\<close>: head
  \<open>0 < v\<^sub>1\<close> and body \<open>D\<^sub>0 0 = X\<^sub>0\<close>, so \<open>lessBT XB X\<^sub>0\<close> fails by irreflexivity.\<close>

definition ox10_cexBody :: BT where
  "ox10_cexBody =
     Trm [DB (enat 1)
           (Trm [DB (enat 1)
                   (Trm [DB (enat 1) 0\<^sub>B,
                         DB (enat 0) (Trm [DB (enat 0) 0\<^sub>B])]),
                 DB (enat 1) (Trm [DB (enat 1) 0\<^sub>B]),
                 DB (enat 1) (Trm [DB (enat 1) 0\<^sub>B])])]"

lemma ox10_cex_not_ok: "\<not> ox9_ok (enat 1) (enat 0) ox10_cexBody"
  by (simp add: ox10_cexBody_def)

lemma ox10_cex_not_hge: "\<not> ox9_hge (enat 1) ox10_cexBody"
  by (simp add: ox10_cexBody_def)

text \<open>The bad principal is a \<^emph>\<open>witness of the equality case\<close>: it is \<open>\<le>\<close> the filler
  but not \<open><\<close> it.  No weakening of @{const ox9_ok} that still yields
  \<open>lessBP x pX\<close> (which @{thm [source] ox9_lexP}'s base case needs) can survive it;
  the guard has to become POSITIONAL.  That is what @{text ox10_engine} does --
  by not needing a guard at all.\<close>


subsection \<open>(2) \<open>ox10_engine\<close>: the same engine, driven by \<open>KK\<close> alone\<close>

text \<open>Identical to @{thm [source] ox9_engine} except that the ancestor bound
  \<open>leLA\<close> at each peel level is no longer produced by @{thm [source] ox9_MAIN}
  (which needs the refuted @{const ox9_ok}); it is produced by

    @{thm [source] ox9_holeD_lessBT} (\<open>MONO\<close>, unconditional) + \<open>KK\<close> + transitivity.

  So \<open>PXOK\<close>, \<open>hgeB\<close> and \<open>DESC\<close> all disappear from the hypotheses.\<close>

lemma ox10_engine:
  fixes u v1 :: enat and WB A1 X1 :: BT and pA pX :: BP
  assumes holeH: "b1x_setle (GBP u pA) (insert X1 (GBT u X1))"
    and hdA: "ox9_holeD dR (DB v1 0\<^sub>B) pA WB A1"
    and hdX: "ox9_holeD dR (DB v1 0\<^sub>B) pX WB X1"
    and pAlt: "lessBP pA (DB v1 0\<^sub>B)"
    and KK: "\<And>j. 1 \<le> j \<Longrightarrow> j \<le> dR \<Longrightarrow> lessBT (ox8_rsub WB j) X1"
  shows "dR - k = m \<Longrightarrow> k \<le> dR \<Longrightarrow> GBT u (ox8_rsub X1 k) \<subseteq> GBT u X1
         \<Longrightarrow> b1x_setle (GBT u (ox8_rsub A1 k)) (insert X1 (GBT u X1))"
proof (induction m arbitrary: k rule: less_induct)
  case (less m)
  note mk = less.prems(1) and kle = less.prems(2) and subX = less.prems(3)
  have hdAk: "ox9_holeD (dR - k) (DB v1 0\<^sub>B) pA (ox8_rsub WB k) (ox8_rsub A1 k)"
    by (rule ox9_holeD_rsub[OF hdA kle])
  have hdXk: "ox9_holeD (dR - k) (DB v1 0\<^sub>B) pX (ox8_rsub WB k) (ox8_rsub X1 k)"
    by (rule ox9_holeD_rsub[OF hdX kle])
  show ?case
  proof (cases "dR - k")
    case 0
    have hA: "ox9_holeD 0 (DB v1 0\<^sub>B) pA (ox8_rsub WB k) (ox8_rsub A1 k)"
      using hdAk 0 by simp
    have hX: "ox9_holeD 0 (DB v1 0\<^sub>B) pX (ox8_rsub WB k) (ox8_rsub X1 k)"
      using hdXk 0 by simp
    obtain ps where WBk: "ox8_rsub WB k = Trm (ps @ [DB v1 0\<^sub>B])"
      and A1k: "ox8_rsub A1 k = Trm (ps @ [pA])"
      by (rule ox9_holeD_0E[OF hA])
    obtain ps' where WBk': "ox8_rsub WB k = Trm (ps' @ [DB v1 0\<^sub>B])"
      and X1k: "ox8_rsub X1 k = Trm (ps' @ [pX])"
      by (rule ox9_holeD_0E[OF hX])
    have pseq: "ps = ps'" using WBk WBk' by simp
    have qsub: "(\<Union>q \<in> set ps. GBP u q) \<subseteq> GBT u X1"
    proof -
      have "(\<Union>q \<in> set ps. GBP u q) \<subseteq> GBT u (ox8_rsub X1 k)" using X1k pseq by auto
      thus ?thesis using subX by blast
    qed
    show ?thesis
      unfolding b1x_setle_def
    proof
      fix x assume xin: "x \<in> GBT u (ox8_rsub A1 k)"
      have "x \<in> (\<Union>q \<in> set ps. GBP u q) \<or> x \<in> GBP u pA" using xin A1k by auto
      thus "\<exists>y \<in> insert X1 (GBT u X1). leBT x y"
      proof
        assume "x \<in> (\<Union>q \<in> set ps. GBP u q)"
        hence "x \<in> GBT u X1" using qsub by blast
        thus ?thesis by blast
      next
        assume "x \<in> GBP u pA"
        thus ?thesis using holeH unfolding b1x_setle_def by blast
      qed
    qed
  next
    case (Suc e)
    have hA: "ox9_holeD (Suc e) (DB v1 0\<^sub>B) pA (ox8_rsub WB k) (ox8_rsub A1 k)"
      using hdAk Suc by simp
    have hX: "ox9_holeD (Suc e) (DB v1 0\<^sub>B) pX (ox8_rsub WB k) (ox8_rsub X1 k)"
      using hdXk Suc by simp
    obtain ps w LB LA where WBk: "ox8_rsub WB k = Trm (ps @ [DB w LB])"
      and A1k: "ox8_rsub A1 k = Trm (ps @ [DB w LA])"
      and hdLB: "ox9_holeD e (DB v1 0\<^sub>B) pA LB LA"
      by (rule ox9_holeD_SucE[OF hA])
    obtain ps' w' LB' LX where WBk': "ox8_rsub WB k = Trm (ps' @ [DB w' LB'])"
      and X1k: "ox8_rsub X1 k = Trm (ps' @ [DB w' LX])"
      by (rule ox9_holeD_SucE[OF hX])
    have pseq: "ps = ps' \<and> w = w' \<and> LB = LB'" using WBk WBk' by simp
    have rB: "ox8_rsub WB (Suc k) = LB" using ox9_rsub_Suc[of WB k] WBk by simp
    have rA: "ox8_rsub A1 (Suc k) = LA" using ox9_rsub_Suc[of A1 k] A1k by simp
    have rX: "ox8_rsub X1 (Suc k) = LX" using ox9_rsub_Suc[of X1 k] X1k by simp
    have kSle: "Suc k \<le> dR" using kle Suc by simp
    \<comment> \<open>the ancestor bound at this level: \<open>MONO\<close> (unconditional) + \<open>KK\<close>\<close>
    have leLA: "leBT LA X1"
    proof -
      have hdLA: "ox9_holeD (dR - Suc k) (DB v1 0\<^sub>B) pA
                    (ox8_rsub WB (Suc k)) (ox8_rsub A1 (Suc k))"
        by (rule ox9_holeD_rsub[OF hdA kSle])
      have mono: "lessBT (ox8_rsub A1 (Suc k)) (ox8_rsub WB (Suc k))"
        by (rule ox9_holeD_lessBT[OF hdLA pAlt])
      have kk: "lessBT (ox8_rsub WB (Suc k)) X1" using KK[of "Suc k"] kSle by simp
      have "lessBT (ox8_rsub A1 (Suc k)) X1" by (rule lessBT_trans[OF mono kk])
      thus ?thesis using rA by blast
    qed
    have qsub: "(\<Union>q \<in> set ps. GBP u q) \<subseteq> GBT u X1"
    proof -
      have "(\<Union>q \<in> set ps. GBP u q) \<subseteq> GBT u (ox8_rsub X1 k)" using X1k pseq by auto
      thus ?thesis using subX by blast
    qed
    show ?thesis
      unfolding b1x_setle_def
    proof
      fix x assume xin: "x \<in> GBT u (ox8_rsub A1 k)"
      have "x \<in> (\<Union>q \<in> set ps. GBP u q) \<or> x \<in> GBP u (DB w LA)" using xin A1k by auto
      thus "\<exists>y \<in> insert X1 (GBT u X1). leBT x y"
      proof
        assume "x \<in> (\<Union>q \<in> set ps. GBP u q)"
        hence "x \<in> GBT u X1" using qsub by blast
        thus ?thesis by blast
      next
        assume xh: "x \<in> GBP u (DB w LA)"
        have uw: "u \<le> w" using xh by (auto split: if_split_asm)
        have xcase: "x = LA \<or> x \<in> GBT u LA" using xh by (auto split: if_split_asm)
        have LXin: "LX \<in> GBT u X1"
        proof -
          have "LX \<in> GBP u (DB w' LX)" using uw pseq by simp
          hence "LX \<in> GBT u (ox8_rsub X1 k)" using X1k by auto
          thus ?thesis using subX by blast
        qed
        have subX': "GBT u (ox8_rsub X1 (Suc k)) \<subseteq> GBT u X1"
          using b1x_GBT_trans[OF LXin] rX by simp
        from xcase show ?thesis
        proof
          assume "x = LA"
          thus ?thesis using leLA by blast
        next
          assume xLA: "x \<in> GBT u LA"
          have mlt: "dR - Suc k < m" using mk Suc by simp
          have IH: "b1x_setle (GBT u (ox8_rsub A1 (Suc k))) (insert X1 (GBT u X1))"
            by (rule less.IH[OF mlt refl kSle subX'])
          have "b1x_setle (GBT u LA) (insert X1 (GBT u X1))" using IH rA by simp
          thus ?thesis using xLA unfolding b1x_setle_def by blast
        qed
      qed
    qed
  qed
qed


subsection \<open>(3) The census \<open>SETLE1\<close> slot from \<open>KK\<close>\<close>

text \<open>Same statement as the (withdrawn) \<open>ox9_SETLE1_ltJ\<close>, with the refuted
  \<open>ALLH\<close> (= \<open>OKH\<close>) replaced by the (empirically true) spine bound \<open>KK\<close>.  The
  aliveness side condition of \<open>KK\<close> is the same one @{thm [source] ox8_body_rspine_lessBT}
  carries, and it is discharged inside from the hole structure.\<close>

lemma ox10_SETLE1_ltJ:
  fixes N :: pairseq and s0 b0 :: "Sym list" and u :: enat
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                 (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and KK: "\<And>k. 1 \<le> k \<Longrightarrow> (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N N))) j \<noteq> 0\<^sub>B)
              \<Longrightarrow> lessBT (ox8_rsub (bpHeadT (Trans (s84x_N N))) k)
                    (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                       0\<^sub>B)"
  shows "b1x_setle
           (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                     (bpHeadT (Trans (Pred (s84x_N N))))))
           (insert (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                      0\<^sub>B)
                   (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                             0\<^sub>B)))"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X0 = "(0\<^sub>B :: BT)"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  let ?X1 = "d4vx_ins s0 ?ub b0 ?X0"
  let ?A1 = "d4vx_ins s0 ?ub b0 ?A0"
  have v1pos: "0 < ?v1"
    using branch by (auto simp: transCondIII_def transCondIV_def)
  have ublt: "?ub < ?v1" using v1pos by simp
  have pAlt: "lessBP (DB (enat ?ub) ?A0) (DB (enat ?v1) 0\<^sub>B)" using ublt by simp
  \<comment> \<open>the body driver and \<open>base\<^sub>1\<close> (pin \<open>(s\<^sub>0,b\<^sub>0)\<close> against the package)\<close>
  have ox5: "b1x_setle (GBT u ?A0) (insert ?X1 (GBT u ?X1))"
    by (rule ox5_body_driver_census[OF NST NPT hp j1gt branch ltJ inner])
  obtain s0' b0' s1 b1 where
      b0RP': "\<forall>x \<in> set b0'. x = RP"
    and inner': "scb_decomp ?body s0' (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0'"
    and base1': "lessBT ?A0 (d4vx_ins s0' ?ub b0' 0\<^sub>B)"
    by (rule oi5_IIIIV_pkg[OF NST NPT hp j1gt branch ltJ])
  have bodyne: "?body \<noteq> Trm []"
  proof
    assume z: "?body = Trm []"
    have "flatBT ?body = s0 @ flatBT (Dpt (enat ?v1) 0\<^sub>B) @ b0"
      using inner by (simp add: scb_decomp_def)
    hence "[Zsym] = s0 @ [Dsym (enat ?v1), Zsym] @ b0" using z by simp
    thus False by (cases s0) auto
  qed
  have pin: "s0 = s0' \<and> b0 = b0'"
    by (rule m_7_2_scb_unique_sb[OF inner inner' bodyne])
  have base1: "lessBT ?A0 ?X1" using base1' pin by simp
  have holeH: "b1x_setle (GBP u (DB (enat ?ub) ?A0)) (insert ?X1 (GBT u ?X1))"
    by (rule ox6_holeH[OF ox5 base1])
  \<comment> \<open>the three flat surgery strings\<close>
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have fA1: "flatBT ?A1 = s0 @ flatBP (DB (enat ?ub) ?A0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ?ub ?A0] by simp
  have fX1: "flatBT ?X1 = s0 @ flatBP (DB (enat ?ub) ?X0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ?ub ?X0] by simp
  obtain dR where
      hdA: "ox9_holeD dR (DB (enat ?v1) 0\<^sub>B) (DB (enat ?ub) ?A0) ?body ?A1"
    and hdX: "ox9_holeD dR (DB (enat ?v1) 0\<^sub>B) (DB (enat ?ub) ?X0) ?body ?X1"
    using ox9_holeD_of_flat3[OF wrap fA1 fX1 b0RP] by blast
  \<comment> \<open>the spine bound, with aliveness read off the surgery structure\<close>
  have KKd: "\<And>k. 1 \<le> k \<Longrightarrow> k \<le> dR \<Longrightarrow> lessBT (ox8_rsub ?body k) ?X1"
  proof -
    fix k :: nat assume kge: "1 \<le> k" and kle: "k \<le> dR"
    have alive: "\<forall>j<k. ox8_rsub ?body j \<noteq> 0\<^sub>B"
    proof (intro allI impI)
      fix j assume jk: "j < k"
      have jle: "j \<le> dR" using jk kle by simp
      have "ox9_holeD (dR - j) (DB (enat ?v1) 0\<^sub>B) (DB (enat ?ub) ?A0)
              (ox8_rsub ?body j) (ox8_rsub ?A1 j)"
        by (rule ox9_holeD_rsub[OF hdA jle])
      thus "ox8_rsub ?body j \<noteq> 0\<^sub>B" by (rule ox9_holeD_ne)
    qed
    show "lessBT (ox8_rsub ?body k) ?X1" by (rule KK[OF kge alive])
  qed
  \<comment> \<open>run the engine from the top (\<open>k = 0\<close>)\<close>
  have e0: "dR - 0 = dR" by simp
  have k0: "(0::nat) \<le> dR" by simp
  have sub0: "GBT u (ox8_rsub ?X1 0) \<subseteq> GBT u ?X1" by simp
  have top: "b1x_setle (GBT u (ox8_rsub ?A1 0)) (insert ?X1 (GBT u ?X1))"
    by (rule ox10_engine[OF holeH hdA hdX pAlt KKd e0 k0 sub0])
  thus ?thesis by simp
qed


subsection \<open>(4) The census roll-up: both pillars from \<open>KK\<close> alone\<close>

text \<open>\<^bold>\<open>Round-70 capstone.\<close>  The r69 residual \<open>OKH\<close> is FALSE
  (@{thm [source] ox10_cex_not_ok}), so the (r72-withdrawn) \<open>oi9_census_OKH\<close> was vacuous.
  Both termination pillars are re-derived here from the \<^emph>\<open>spine bound\<close> \<open>KK\<close>,
  which is TRUE on the whole deep census corpus (1212/1212 peel levels, all 8
  \<open>ox9_ok\<close>-refuting hosts included).  \<open>KK\<close> mentions neither \<open>A\<^sub>0\<close> nor any
  head guard: it says only that the right-spine sub-bodies of the census body
  stay below the LOWERED body \<open>X\<^sub>1\<close> --- i.e. that the descent
  @{thm [source] ox8_body_rspine_lessBT} is decided strictly ABOVE the hole.\<close>

theorem oi10_census_KK:
  assumes KK: "\<And>P s0 b0 k. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
             hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIII P \<or> transCondIV P \<Longrightarrow>
             (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
             scb_decomp (bpHeadT (Trans (s84x_N P))) s0
               (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
             s84x_jm3 P < transJm1 P \<Longrightarrow>
             1 \<le> k \<Longrightarrow>
             (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B) \<Longrightarrow>
             lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
               (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                  0\<^sub>B)"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
  proof -
    fix P :: pairseq and s0 b0 :: "Sym list" and u :: enat
    assume A1: "P \<in> ST_PS" and A2: "P \<in> PT_PS"
      and A3: "hasParent P 1 (Lng P - 1)" and A4: "1 < Lng P - 1"
      and A5: "transCondIII P \<or> transCondIV P" and A6: "Trans P \<in> OT_B"
      and A7: "\<forall>x \<in> set b0. x = RP"
      and A8: "scb_decomp (bpHeadT (Trans (s84x_N P))) s0
                (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0"
      and A9: "s84x_jm3 P < transJm1 P"
    have H: "\<And>k. 1 \<le> k \<Longrightarrow>
               (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B) \<Longrightarrow>
               lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
                 (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    0\<^sub>B)"
      by (rule KK[OF A1 A2 A3 A4 A5 A7 A8 A9])
    show "b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
      by (rule ox10_SETLE1_ltJ[OF A1 A2 A3 A4 A5 A7 A8 A9 H])
  qed
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi8_census_final_ivadmeq(1)[OF SETLE1 ot9_FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
         lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi8_census_final_ivadmeq(2)[OF SETLE1 ot9_FINRC])
qed

subsection \<open>(5) \<open>ox10_lexP\<close>: the list transport with a POSITIONAL guard\<close>

text \<open>\<^bold>\<open>Why @{const ox9_ok} was doomed.\<close>  @{thm [source] ox9_lexP} demands the guard
  \<open>HT\<close> for EVERY principal of the left operand.  Its proof needs it for exactly ONE:
  the principal sitting at the RIGHT operand's hole index \<open>\<bar>ys\<bar>\<close> --- and only when
  the left operand's list actually has \<open>ys\<close> as a prefix (otherwise the walk is
  decided earlier and the hole is never compared).  The refuting principal
  \<open>D\<^sub>0(D\<^sub>0 0)\<close> of @{const ox10_cexBody} lives in the body of a NON-last principal, so
  it never occupies a hole-aligned position; the global guard sees it, the walk
  does not.  @{text ox10_lexP} is @{thm [source] ox9_lexP} with the guard moved to
  where it is used.  (STEP-0 measurement: over 1700 census peel levels the walk of
  \<open>ox8_rsub body k\<close> against \<open>X\<^sub>1\<close> reaches the hole \<^bold>\<open>0\<close> times --- python/_r70_hd.py.)\<close>

lemma ox10_lexP:
  "lessBT (Trm xs) (Trm (ys @ [q]))
   \<Longrightarrow> (\<forall>zs x. xs = ys @ x # zs \<longrightarrow> lessBP x q \<longrightarrow> lessBP x q')
   \<Longrightarrow> lessBT (Trm xs) (Trm (ys @ [q']))"
proof (induction ys arbitrary: xs)
  case Nil
  note P1 = Nil.prems(1) and P2 = Nil.prems(2)
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis by simp
  next
    case (Cons x xs')
    have "lessBP x q \<or> (x = q \<and> lessBT (Trm xs') 0\<^sub>B)" using P1 Cons by simp
    hence lx: "lessBP x q" using ox9_lessBT_zero by blast
    have E: "xs = [] @ x # xs'" using Cons by simp
    have "lessBP x q'" using P2 E lx by blast
    thus ?thesis using Cons by simp
  qed
next
  case (Cons y ys')
  note IH = Cons.IH and P1 = Cons.prems(1) and P2 = Cons.prems(2)
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis by simp
  next
    case (Cons x xs')
    have "lessBP x y \<or> (x = y \<and> lessBT (Trm xs') (Trm (ys' @ [q])))"
      using P1 Cons by simp
    thus ?thesis
    proof
      assume "lessBP x y"
      thus ?thesis using Cons by simp
    next
      assume A: "x = y \<and> lessBT (Trm xs') (Trm (ys' @ [q]))"
      have G: "\<forall>zs x2. xs' = ys' @ x2 # zs \<longrightarrow> lessBP x2 q \<longrightarrow> lessBP x2 q'"
      proof (intro allI impI)
        fix zs x2 assume E: "xs' = ys' @ x2 # zs" and L: "lessBP x2 q"
        have "xs = (y # ys') @ x2 # zs" using Cons E A by simp
        thus "lessBP x2 q'" using P2 L by blast
      qed
      have "lessBT (Trm xs') (Trm (ys' @ [q']))" by (rule IH[OF _ G]) (use A in simp)
      thus ?thesis using Cons A by simp
    qed
  qed
qed

text \<open>@{thm [source] ox9_lexP} is the special case in which the positional guard is
  discharged from the (refuted) GLOBAL predicate @{const ox9_ok} --- so
  @{text ox10_lexP} is strictly more general, and it is the hook any future proof
  of \<open>KK\<close> should use.\<close>

lemma ox10_lexP_subsumes_ox9:
  assumes HT: "\<And>x. ox9_okP v ub x \<Longrightarrow> lessBP x q \<Longrightarrow> lessBP x q'"
    and ok: "ox9_ok v ub (Trm xs)"
    and lt: "lessBT (Trm xs) (Trm (ys @ [q]))"
  shows "lessBT (Trm xs) (Trm (ys @ [q']))"
proof -
  have G: "\<forall>zs x. xs = ys @ x # zs \<longrightarrow> lessBP x q \<longrightarrow> lessBP x q'"
  proof (intro allI impI)
    fix zs x assume E: "xs = ys @ x # zs" and L: "lessBP x q"
    have "x \<in> set xs" using E by simp
    hence "ox9_okP v ub x" using ok by simp
    thus "lessBP x q'" by (rule HT[OF _ L])
  qed
  show ?thesis by (rule ox10_lexP[OF lt G])
qed

(* ===== end r70 ox10 block (OKH refuted; census residual = KK) ========== *)



(* =====================================================================
   r70 front y3 (prefix  y3_ ).  THE W-INDUCTION TERMINATION ENGINE.

   Goal of the round: retire the last external citation ([Buc1] 2.2,
   \<open>wf (<)\<close>) by running the termination proof on the FUNDAMENTAL-SEQUENCE
   well-foundedness that r68 proved unconditionally (\<open>bwl_2_8\<close>: every
   \<open>D\<^sub>\<omega>\<close>-free term lies in \<open>W\<^sup>*\<close>), instead of on \<open>wf RPrel\<close>.

   What this block establishes:
   (1) \<open>y3_TBv_dfree_W\<close>: every \<open>D\<^sub>\<omega>\<close>-free \<open>z \<in> T\<^sub>m\<close> is ALREADY in \<open>W\<^sub>m\<close>.
       Consequence: the \<open>z \<in> W\<^sub>m\<close> side condition of the r68 residual
       \<open>bwl_cof\<close> is FREE, and \<open>bwl_cof\<close> collapses to the purely
       order-theoretic \<open>y3_cof0\<close> (no fixpoint set occurs in it).
   (2) \<open>y3_W_acc\<close>: \<open>W\<^sub>v\<close>-membership gives ACCESSIBILITY along the
       fundamental-sequence tree — Buchholz's hydra theorem in \<open>acc\<close> form,
       free from the \<open>lfp\<close> induction rule, no cofinality needed.
   (3) \<open>y3_PSS_acc_of_OKH_cofimg\<close>: PSS termination (accessibility of the
       \<open>M \<rightarrow> M[n]\<close> step relation) proved by W-INDUCTION, using NO \<open>wf\<close>,
       NO \<open>buc1_2_2_OT_B_wf\<close>, NO \<open>bwl_cof\<close> — modulo the census residual
       \<open>OKH\<close> and the NEW residual \<open>y3_cofimg\<close> (\<open>bwl_cof\<close> with the smaller
       argument restricted to \<open>Trans\<close>-images, and with no \<open>W\<close>-membership
       clause).  \<open>y3_cofimg\<close> is strictly weaker than \<open>bwl_cof\<close>
       (@{thm [source] y3_cofimg_of_bwl_cof}).

   HONEST FINDING (see the closing text): the fseq CORRESPONDENCE is NOT an
   equation.  The article's exchange laws give equality only in the
   condition-(I)/(II) legs; legs (III)-(VI) give \<open>\<le>\<close> only, and in leg (VI)
   with \<open>adm\<close> the proven @{thm [source] c613x_condVI_exch_adm} gives a STRICT
   \<open><\<close>.  So \<open>Trans (M[n])\<close> is in general NOT a fundamental-sequence child of
   \<open>Trans M\<close>, and a cofinality (step-down) property is unavoidable.
   ===================================================================== *)

section \<open>r70-y3 --- W-induction as the termination engine (\<open>y3_\<close>)\<close>

subsection \<open>(1) \<open>W\<close> is monotone in the level, and every \<open>D\<^sub>\<omega>\<close>-free \<open>T\<^sub>m\<close>-term is in \<open>W\<^sub>m\<close>\<close>

lemma y3_W_mono:
  assumes uv: "u \<le> v"
  shows "bwl_W u \<subseteq> bwl_W v"
proof (rule bwl_A2')
  fix c assume A: "bwl_Aop bwl_W (enat u) (bwl_W v) c"
  have le: "enat u \<le> enat v" using uv by simp
  have "bwl_Aop bwl_W (enat v) (bwl_W v) c" by (rule bwl_Aop_mono_nv[OF le A])
  thus "c \<in> bwl_W v" by (rule bwl_A1_intro)
qed

text \<open>The key closure: a \<open>D\<^sub>\<omega>\<close>-free term all of whose top-level principal indices are
  \<open>\<le> m\<close> lies in \<open>W\<^sub>m\<close>.  Each principal is in \<open>W\<close> at its own index by
  @{thm [source] bwl_2_8_principal}, lifts to \<open>W\<^sub>m\<close> by @{thm [source] y3_W_mono},
  and the tuple is assembled by the addition closure @{thm [source] bwl_2_4b_add}.\<close>

lemma y3_TBv_dfree_W_aux:
  assumes df: "\<forall>p \<in> set ps. dfree_BP p"
    and bd: "\<forall>p \<in> set ps. (case p of DB w b \<Rightarrow> w \<le> enat m)"
  shows "Trm ps \<in> bwl_W m"
  using assms
proof (induction ps)
  case Nil
  show ?case by (simp add: bwl_W_zero)
next
  case (Cons p ps)
  obtain w b where pwb: "p = DB w b" by (cases p)
  have dfp: "dfree_BP p" using Cons.prems(1) by simp
  have wne: "w \<noteq> \<infinity>" and dfb: "dfree_BT b" using dfp pwb by simp_all
  obtain k where wk: "w = enat k" using wne by (cases w) auto
  have kle: "enat k \<le> enat m" using Cons.prems(2) pwb wk by simp
  hence km: "k \<le> m" by simp
  have pW: "Trm [DB (enat k) b] \<in> bwl_W k" by (rule bwl_2_8_principal[OF dfb])
  have pWm: "Trm [p] \<in> bwl_W m" using pW y3_W_mono[OF km] pwb wk by blast
  have d1: "\<forall>q \<in> set ps. dfree_BP q" using Cons.prems(1) by simp
  have d2: "\<forall>q \<in> set ps. (case q of DB w' b' \<Rightarrow> w' \<le> enat m)" using Cons.prems(2) by simp
  have rest: "Trm ps \<in> bwl_W m" by (rule Cons.IH[OF d1 d2])
  have "Trm [p] +\<^sub>B Trm ps \<in> bwl_W m" by (rule bwl_2_4b_add[OF pWm rest])
  thus ?case by simp
qed

lemma y3_TBv_dfree_W:
  assumes df: "dfree_BT z" and tb: "z \<in> TBv (enat m)"
  shows "z \<in> bwl_W m"
proof -
  obtain ps where zps: "z = Trm ps" by (cases z)
  have d1: "\<forall>p \<in> set ps. dfree_BP p" using df zps by simp
  have d2: "\<forall>p \<in> set ps. (case p of DB w b \<Rightarrow> w \<le> enat m)"
    using tb zps by (simp add: TBv_def)
  show ?thesis using y3_TBv_dfree_W_aux[OF d1 d2] zps by simp
qed

text \<open>Every \<open>D\<^sub>\<omega>\<close>-free term has a finite level, hence lies in SOME \<open>W\<^sub>m\<close>.\<close>

lemma y3_dfree_ex_lev_aux:
  assumes "\<forall>p \<in> set ps. dfree_BP p"
  shows "\<exists>m. \<forall>p \<in> set ps. (case p of DB w b \<Rightarrow> w \<le> enat m)"
  using assms
proof (induction ps)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  obtain w b where pwb: "p = DB w b" by (cases p)
  have wne: "w \<noteq> \<infinity>" using Cons.prems pwb by simp
  obtain k where wk: "w = enat k" using wne by (cases w) auto
  have d1: "\<forall>q \<in> set ps. dfree_BP q" using Cons.prems by simp
  obtain m where m: "\<forall>q \<in> set ps. (case q of DB w' b' \<Rightarrow> w' \<le> enat m)"
    using Cons.IH[OF d1] by blast
  have "\<forall>q \<in> set (p # ps). (case q of DB w' b' \<Rightarrow> w' \<le> enat (max k m))"
  proof
    fix q assume qin: "q \<in> set (p # ps)"
    obtain w' b' where qwb: "q = DB w' b'" by (cases q)
    show "case q of DB w' b' \<Rightarrow> w' \<le> enat (max k m)"
    proof (cases "q = p")
      case True
      have "w \<le> enat (max k m)" using wk by simp
      thus ?thesis using True pwb qwb by simp
    next
      case False
      hence qps: "q \<in> set ps" using qin by simp
      have hq: "case q of DB w2 b2 \<Rightarrow> w2 \<le> enat m" using m qps by blast
      have le1: "w' \<le> enat m" using hq qwb by simp
      have le2: "enat m \<le> enat (max k m)" by simp
      have "w' \<le> enat (max k m)" using le1 le2 by (rule order_trans)
      thus ?thesis using qwb by simp
    qed
  qed
  thus ?case by blast
qed

lemma y3_dfree_ex_lev:
  assumes df: "dfree_BT z"
  shows "\<exists>m. z \<in> TBv (enat m)"
proof -
  obtain ps where zps: "z = Trm ps" by (cases z)
  have d1: "\<forall>p \<in> set ps. dfree_BP p" using df zps by simp
  obtain m where m: "\<forall>p \<in> set ps. (case p of DB w b \<Rightarrow> w \<le> enat m)"
    using y3_dfree_ex_lev_aux[OF d1] by blast
  have "z \<in> TBv (enat m)" using m zps by (simp add: TBv_def)
  thus ?thesis by blast
qed

corollary y3_dfree_W_ex:
  assumes df: "dfree_BT z"
  shows "\<exists>m. z \<in> bwl_W m"
  using y3_dfree_ex_lev[OF df] y3_TBv_dfree_W[OF df] by blast

text \<open>\<open>Trans\<close>-images are \<open>D\<^sub>\<omega>\<close>-free (they are in \<open>T\<^bsub>B\<^esub>\<close> by
  @{thm [source] m_7_3_Trans_in_T_B}), hence in \<open>W\<close>.\<close>

lemma y3_Trans_dfree:
  assumes MR: "M \<in> RT_PS"
  shows "dfree_BT (Trans M)"
  using m_7_3_Trans_in_T_B[OF MR] by (simp add: T_B_def)

corollary y3_Trans_W:
  assumes MR: "M \<in> RT_PS"
  shows "\<exists>m. Trans M \<in> bwl_W m"
  by (rule y3_dfree_W_ex[OF y3_Trans_dfree[OF MR]])


subsection \<open>(2) The three \<open>dom\<close>-shapes are pairwise distinct\<close>

lemma y3_one_in_TBv: "Trm [DB 0 (Trm [DB 0 (Trm [])])] \<in> TBv (enat m)"
  by (simp add: TBv_def)

lemma y3_D0one_not_NatSet: "Trm [DB 0 (Trm [DB 0 (Trm [])])] \<notin> NatSet"
proof
  assume "Trm [DB 0 (Trm [DB 0 (Trm [])])] \<in> NatSet"
  then obtain n where n: "Trm [DB 0 (Trm [DB 0 (Trm [])])] = numBT n"
    by (auto simp: NatSet_def)
  hence l: "[DB 0 (Trm [DB 0 (Trm [])])] = replicate n (DB 0 (Trm []))"
    by (simp add: numBT_def)
  show False using l by (cases n) auto
qed

lemma y3_TBv_ne_zeroset: "TBv (enat m) \<noteq> {Trm []}"
proof
  assume e: "TBv (enat m) = {Trm []}"
  have "Trm [DB 0 (Trm [DB 0 (Trm [])])] \<in> TBv (enat m)" by (rule y3_one_in_TBv)
  hence "Trm [DB 0 (Trm [DB 0 (Trm [])])] = Trm []" using e by simp
  thus False by simp
qed

lemma y3_TBv_ne_NatSet: "TBv (enat m) \<noteq> NatSet"
proof
  assume e: "TBv (enat m) = NatSet"
  have "Trm [DB 0 (Trm [DB 0 (Trm [])])] \<in> TBv (enat m)" by (rule y3_one_in_TBv)
  hence "Trm [DB 0 (Trm [DB 0 (Trm [])])] \<in> NatSet" using e by simp
  thus False using y3_D0one_not_NatSet by simp
qed

lemma y3_TBv_inj:
  assumes e: "TBv (enat m) = TBv (enat m')"
  shows "m = m'"
proof -
  have le: "\<And>i j. TBv (enat i) = TBv (enat j) \<Longrightarrow> i \<le> j"
  proof -
    fix i j :: nat assume ij: "TBv (enat i) = TBv (enat j)"
    have "Trm [DB (enat i) (Trm [])] \<in> TBv (enat i)" by (simp add: TBv_def)
    hence "Trm [DB (enat i) (Trm [])] \<in> TBv (enat j)" using ij by simp
    hence "enat i \<le> enat j" by (simp add: TBv_def)
    thus "i \<le> j" by simp
  qed
  show ?thesis using le[OF e] le[OF e[symmetric]] by simp
qed


subsection \<open>(3) The residual \<open>bwl_cof\<close> loses its \<open>W\<close>-membership clause\<close>

text \<open>\<open>y3_cof0\<close> is \<open>bwl_cof\<close> with the clause \<open>z \<in> W\<^sub>m\<close> DELETED: a purely
  order-theoretic cofinality statement about \<open><\<close> and \<open>[\<cdot>]\<close> on \<open>OT\<^bsub>B\<^esub>\<close>.  It implies
  \<open>bwl_cof\<close> because the missing clause is now free (@{thm [source] y3_TBv_dfree_W}:
  \<open>z \<in> dom(a) = T\<^sub>m\<close> and \<open>z\<close> \<open>D\<^sub>\<omega>\<close>-free already force \<open>z \<in> W\<^sub>m\<close>).\<close>

definition y3_cof0 :: bool where
  "y3_cof0 \<longleftrightarrow>
     (\<forall>a b. isOT_BT a \<longrightarrow> dfree_BT a \<longrightarrow> isOT_BT b \<longrightarrow> dfree_BT b \<longrightarrow> lessBT b a \<longrightarrow>
        (((domB a = {Trm []} \<or> domB a = NatSet)
             \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n))))
         \<and> (\<forall>m. domB a = TBv (enat m)
             \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z)))))"

lemma y3_cof0_imp_bwl_cof:
  assumes C0: "y3_cof0"
  shows "bwl_cof"
proof -
  have main: "\<And>a b. isOT_BT a \<Longrightarrow> dfree_BT a \<Longrightarrow> isOT_BT b \<Longrightarrow> dfree_BT b \<Longrightarrow>
      lessBT b a \<Longrightarrow>
      (((domB a = {Trm []} \<or> domB a = NatSet) \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n))))
       \<and> (\<forall>m. domB a = TBv (enat m)
             \<longrightarrow> (\<exists>z. z \<in> bwl_W m \<and> z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z
                        \<and> leBT b (operB a z))))"
  proof -
    fix a b assume ota: "isOT_BT a" and dfa: "dfree_BT a"
      and otb: "isOT_BT b" and dfb: "dfree_BT b" and lba: "lessBT b a"
    have c0: "((domB a = {Trm []} \<or> domB a = NatSet)
                  \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n))))
              \<and> (\<forall>m. domB a = TBv (enat m)
                  \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z)))"
      using C0[unfolded y3_cof0_def] ota dfa otb dfb lba by blast
    have num: "(domB a = {Trm []} \<or> domB a = NatSet)
                  \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n)))"
      using c0 by blast
    have tu: "\<forall>m. domB a = TBv (enat m)
                  \<longrightarrow> (\<exists>z. z \<in> bwl_W m \<and> z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z
                             \<and> leBT b (operB a z))"
    proof (intro allI impI)
      fix m assume dm: "domB a = TBv (enat m)"
      obtain z where z1: "z \<in> domB a" and z2: "isOT_BT z" and z3: "dfree_BT z"
        and z4: "leBT b (operB a z)" using c0 dm by blast
      have zTB: "z \<in> TBv (enat m)" using z1 dm by simp
      have zW: "z \<in> bwl_W m" by (rule y3_TBv_dfree_W[OF z3 zTB])
      show "\<exists>z. z \<in> bwl_W m \<and> z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z
                  \<and> leBT b (operB a z)"
        using zW z1 z2 z3 z4 by blast
    qed
    show "(((domB a = {Trm []} \<or> domB a = NatSet)
              \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n))))
           \<and> (\<forall>m. domB a = TBv (enat m)
              \<longrightarrow> (\<exists>z. z \<in> bwl_W m \<and> z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z
                         \<and> leBT b (operB a z))))"
      using num tu by blast
  qed
  show ?thesis unfolding bwl_cof_def using main by blast
qed

theorem y3_wf_RPrel_of_cof0:
  assumes C0: "y3_cof0"
  shows "wf RPrel"
  by (rule bwl_wf_RPrel_of_cof[OF y3_cof0_imp_bwl_cof[OF C0]])


subsection \<open>(4) The FREE hydra theorem: \<open>W\<^sub>v \<subseteq> acc\<close> of the fundamental-sequence tree\<close>

text \<open>\<open>y3_child v a b\<close>: \<open>b\<close> is a child of \<open>a\<close> in the fundamental-sequence tree, exactly
  as the two generating clauses (W2)/(W3) of \<open>W\<^sub>v\<close> descend.  By
  @{thm [source] y3_TBv_dfree_W}, in the (W3) case the admissible arguments \<open>z\<close> include
  ALL \<open>D\<^sub>\<omega>\<close>-free elements of \<open>dom(a)\<close>, so this really is the full fseq tree.\<close>

definition y3_child :: "nat \<Rightarrow> BT \<Rightarrow> BT \<Rightarrow> bool" where
  "y3_child v a b \<longleftrightarrow>
     ((domB a = {Trm []} \<or> domB a = NatSet) \<and> (\<exists>n. b = operB a (numBT n)))
     \<or> (\<exists>m. m < v \<and> domB a = TBv (enat m) \<and> (\<exists>z. z \<in> bwl_W m \<and> b = operB a z))"

definition y3_Rel :: "nat \<Rightarrow> (BT \<times> BT) set" where
  "y3_Rel v = {(b, a). y3_child v a b}"

theorem y3_W_acc: "bwl_W v \<subseteq> Wellfounded.acc (y3_Rel v)"
proof (rule bwl_A2')
  fix c assume A: "bwl_Aop bwl_W (enat v) (Wellfounded.acc (y3_Rel v)) c"
  consider (zero) "c = Trm []"
    | (num) "(domB c = {Trm []} \<or> domB c = NatSet)
             \<and> (\<forall>n. operB c (numBT n) \<in> Wellfounded.acc (y3_Rel v))"
    | (tu) m where "enat m < enat v" "domB c = TBv (enat m)"
             "\<forall>z \<in> bwl_W m. operB c z \<in> Wellfounded.acc (y3_Rel v)"
    using A[unfolded bwl_Aop_def] by blast
  thus "c \<in> Wellfounded.acc (y3_Rel v)"
  proof cases
    case zero
    show ?thesis
    proof (rule acc.intros)
      fix b assume "(b, c) \<in> y3_Rel v"
      hence ch: "y3_child v c b" by (simp add: y3_Rel_def)
      have dz: "domB c = {}" using zero bwo_domB_Nil by simp
      have n1: "domB c \<noteq> {Trm []}" using dz by simp
      have n2: "domB c \<noteq> NatSet"
      proof
        assume "domB c = NatSet"
        hence "NatSet = {}" using dz by simp
        moreover have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
        ultimately show False by simp
      qed
      have n3: "\<And>m. domB c \<noteq> TBv (enat m)"
      proof -
        fix m :: nat
        show "domB c \<noteq> TBv (enat m)"
        proof
          assume e: "domB c = TBv (enat m)"
          have "Trm [] \<in> TBv (enat m)" by (simp add: TBv_def)
          thus False using e dz by simp
        qed
      qed
      show "b \<in> Wellfounded.acc (y3_Rel v)"
        using ch n1 n2 n3 unfolding y3_child_def by blast
    qed
  next
    case num
    show ?thesis
    proof (rule acc.intros)
      fix b assume "(b, c) \<in> y3_Rel v"
      hence ch: "y3_child v c b" by (simp add: y3_Rel_def)
      have D: "domB c = {Trm []} \<or> domB c = NatSet" using num by blast
      have notTB: "\<And>m. domB c \<noteq> TBv (enat m)"
        using D y3_TBv_ne_zeroset y3_TBv_ne_NatSet by metis
      have "\<exists>n. b = operB c (numBT n)"
        using ch notTB unfolding y3_child_def by blast
      then obtain n where bn: "b = operB c (numBT n)" by blast
      show "b \<in> Wellfounded.acc (y3_Rel v)" using bn num by blast
    qed
  next
    case (tu m)
    show ?thesis
    proof (rule acc.intros)
      fix b assume "(b, c) \<in> y3_Rel v"
      hence ch: "y3_child v c b" by (simp add: y3_Rel_def)
      have notNum: "\<not> (domB c = {Trm []} \<or> domB c = NatSet)"
        using tu(2) y3_TBv_ne_zeroset y3_TBv_ne_NatSet by metis
      obtain m' z where m'1: "domB c = TBv (enat m')" and m'2: "z \<in> bwl_W m'"
        and m'3: "b = operB c z"
        using ch notNum unfolding y3_child_def by blast
      have "TBv (enat m') = TBv (enat m)" using m'1 tu(2) by simp
      hence mm: "m' = m" by (rule y3_TBv_inj)
      have "z \<in> bwl_W m" using m'2 mm by simp
      thus "b \<in> Wellfounded.acc (y3_Rel v)" using tu(3) m'3 by blast
    qed
  qed
qed


subsection \<open>(5) The NEW residual \<open>y3_cofimg\<close> and the citation-free termination engine\<close>

text \<open>The PSS one-step relation: \<open>M \<rightarrow> M[n]\<close> for \<open>n \<ge> 1\<close> at a non-degenerate \<open>M\<close>.\<close>

definition y3_PSSrel :: "(pairseq \<times> pairseq) set" where
  "y3_PSSrel = {(N, M). M \<in> ST_PS \<and> 1 < Lng M \<and> (\<exists>n. 1 \<le> n \<and> N = (M::pairseq)[n])}"

text \<open>\<open>y3_cofimg\<close>: \<open>y3_cof0\<close> with the SMALLER argument restricted to \<open>Trans\<close>-images.
  This is all the termination proof ever needs, and it is implied by \<open>bwl_cof\<close>
  (hence a fortiori by \<open>y3_cof0\<close>).\<close>

definition y3_cofimg :: bool where
  "y3_cofimg \<longleftrightarrow>
     (\<forall>a M. isOT_BT a \<longrightarrow> dfree_BT a \<longrightarrow> M \<in> ST_PS \<longrightarrow> lessBT (Trans M) a \<longrightarrow>
        (((domB a = {Trm []} \<or> domB a = NatSet)
             \<longrightarrow> (\<exists>n. leBT (Trans M) (operB a (numBT n))))
         \<and> (\<forall>m. domB a = TBv (enat m)
             \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z
                        \<and> leBT (Trans M) (operB a z)))))"

lemma y3_cofimg_of_bwl_cof:
  assumes COF: "bwl_cof"
    and TOT: "\<And>N. N \<in> ST_PS \<Longrightarrow> Trans N \<in> OT_B"
  shows "y3_cofimg"
proof (unfold y3_cofimg_def, intro allI impI)
  fix a :: BT and M :: pairseq
  assume ota: "isOT_BT a" and dfa: "dfree_BT a" and MST: "M \<in> ST_PS"
    and lt: "lessBT (Trans M) a"
  have MOT: "Trans M \<in> OT_B" by (rule TOT[OF MST])
  have otb: "isOT_BT (Trans M)" and dfb: "dfree_BT (Trans M)"
    using MOT by (simp_all add: OT_B_def OT_def T_B_def)
  have C: "((domB a = {Trm []} \<or> domB a = NatSet)
               \<longrightarrow> (\<exists>n. leBT (Trans M) (operB a (numBT n))))
           \<and> (\<forall>m. domB a = TBv (enat m)
               \<longrightarrow> (\<exists>z. z \<in> bwl_W m \<and> z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z
                          \<and> leBT (Trans M) (operB a z)))"
    by (rule COF[unfolded bwl_cof_def, rule_format, OF ota dfa otb dfb lt])
  show "((domB a = {Trm []} \<or> domB a = NatSet)
            \<longrightarrow> (\<exists>n. leBT (Trans M) (operB a (numBT n))))
        \<and> (\<forall>m. domB a = TBv (enat m)
            \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z
                       \<and> leBT (Trans M) (operB a z)))"
    using C by blast
qed

text \<open>\<^bold>\<open>THE ENGINE.\<close>  Termination of the PSS step relation by W-INDUCTION
  (@{thm [source] bwl_A2'}) on \<open>Trans M\<close>.  The invariant is
  \<open>Y = {a. a \<in> OT\<^bsub>B\<^esub> \<longrightarrow> (\<forall>N \<in> ST\<^bsub>PS\<^esub>. Trans N \<le> a \<longrightarrow> N accessible)}\<close>;
  the \<open>\<le>\<close> (rather than \<open>=\<close>) is forced by the article's exchange laws, which give only
  \<open>Trans (M[n]) \<le> (Trans M)[k]\<close> in the condition-(III)--(VI) legs, and the \<open>\<le>\<close> is
  absorbed by \<open>y3_cofimg\<close> at each node.  NO \<open>wf\<close>, NO \<open>buc1_2_2_OT_B_wf\<close>,
  NO \<open>bwl_cof\<close> is used.\<close>

theorem y3_PSS_acc_of_cofimg:
  assumes DESC: "\<And>N n. N \<in> ST_PS \<Longrightarrow> 1 \<le> n \<Longrightarrow> 1 < Lng N \<Longrightarrow>
                   lessBT (Trans ((N::pairseq)[n])) (Trans N)"
    and TOT: "\<And>N. N \<in> ST_PS \<Longrightarrow> Trans N \<in> OT_B"
    and COF: "y3_cofimg"
    and MST: "M \<in> ST_PS"
  shows "M \<in> Wellfounded.acc y3_PSSrel"
proof -
  define Y :: "BT set" where
    "Y = {a. isOT_BT a \<longrightarrow> dfree_BT a \<longrightarrow>
              (\<forall>N. N \<in> ST_PS \<longrightarrow> leBT (Trans N) a \<longrightarrow> N \<in> Wellfounded.acc y3_PSSrel)}"
  have Ycl: "\<And>v c. bwl_Aop bwl_W (enat v) Y c \<Longrightarrow> c \<in> Y"
  proof -
    fix v :: nat and c :: BT
    assume A: "bwl_Aop bwl_W (enat v) Y c"
    show "c \<in> Y"
    proof (cases "isOT_BT c \<and> dfree_BT c")
      case False
      thus ?thesis by (auto simp: Y_def)
    next
      case True
      have otc: "isOT_BT c" and dfc: "dfree_BT c" using True by simp_all
      have cOT: "c \<in> OT_B" using otc dfc by (simp add: OT_B_def OT_def T_B_def)
      have body: "\<forall>N. N \<in> ST_PS \<longrightarrow> leBT (Trans N) c
                        \<longrightarrow> N \<in> Wellfounded.acc y3_PSSrel"
      proof (intro allI impI)
        fix N :: pairseq
        assume NST: "N \<in> ST_PS" and leN: "leBT (Trans N) c"
        show "N \<in> Wellfounded.acc y3_PSSrel"
        proof (rule acc.intros)
          fix K :: pairseq
          assume KN: "(K, N) \<in> y3_PSSrel"
          then obtain n where L: "1 < Lng N" and n1: "1 \<le> n"
            and Keq: "K = (N::pairseq)[n]"
            by (auto simp: y3_PSSrel_def)
          have KST: "K \<in> ST_PS" using ST_PS.oper[OF NST n1] Keq by simp
          have desc: "lessBT (Trans K) (Trans N)"
            using DESC[OF NST n1 L] Keq by simp
          have ltc: "lessBT (Trans K) c"
          proof (cases "Trans N = c")
            case True
            thus ?thesis using desc by simp
          next
            case False
            hence "lessBT (Trans N) c" using leN by simp
            thus ?thesis by (rule lessBT_trans[OF desc])
          qed
          have cne: "c \<noteq> Trm []"
          proof
            assume z: "c = Trm []"
            have "lessBT (Trans K) (Trm [])" using ltc z by simp
            thus False using bwl_not_lessBT_zero by simp
          qed
          have cofK: "((domB c = {Trm []} \<or> domB c = NatSet)
                          \<longrightarrow> (\<exists>n'. leBT (Trans K) (operB c (numBT n'))))
                      \<and> (\<forall>m. domB c = TBv (enat m)
                          \<longrightarrow> (\<exists>z. z \<in> domB c \<and> isOT_BT z \<and> dfree_BT z
                                     \<and> leBT (Trans K) (operB c z)))"
            using COF[unfolded y3_cofimg_def] otc dfc KST ltc by blast
          consider (zero) "c = Trm []"
            | (num) "(domB c = {Trm []} \<or> domB c = NatSet)
                     \<and> (\<forall>n. operB c (numBT n) \<in> Y)"
            | (tu) m where "enat m < enat v" "domB c = TBv (enat m)"
                     "\<forall>z \<in> bwl_W m. operB c z \<in> Y"
            using A[unfolded bwl_Aop_def] by blast
          thus "K \<in> Wellfounded.acc y3_PSSrel"
          proof cases
            case zero
            thus ?thesis using cne by simp
          next
            case num
            have D: "domB c = {Trm []} \<or> domB c = NatSet" using num by blast
            obtain n' where n': "leBT (Trans K) (operB c (numBT n'))"
              using cofK D by blast
            have dY: "operB c (numBT n') \<in> Y" using num by blast
            have dOT: "operB c (numBT n') \<in> OT_B"
              by (rule m_buc1_3_2_OT_B_closed[OF cOT cne])
            have otd: "isOT_BT (operB c (numBT n'))"
              and dfd: "dfree_BT (operB c (numBT n'))"
              using dOT by (simp_all add: OT_B_def OT_def T_B_def)
            have "\<forall>N'. N' \<in> ST_PS \<longrightarrow> leBT (Trans N') (operB c (numBT n'))
                          \<longrightarrow> N' \<in> Wellfounded.acc y3_PSSrel"
              using dY otd dfd by (simp add: Y_def)
            thus ?thesis using KST n' by blast
          next
            case (tu m)
            obtain z where zd: "z \<in> domB c" and otz: "isOT_BT z" and dfz: "dfree_BT z"
              and lez: "leBT (Trans K) (operB c z)"
              using cofK tu(2) by blast
            have zTB: "z \<in> TBv (enat m)" using zd tu(2) by simp
            have zW: "z \<in> bwl_W m" by (rule y3_TBv_dfree_W[OF dfz zTB])
            have dY: "operB c z \<in> Y" using tu(3) zW by blast
            have "isOT_BT (operB c z) \<and> dfree_BT (operB c z)"
              using b1x_master[OF otc dfc cne disjI1[OF zd]] otz dfz by blast
            hence otd: "isOT_BT (operB c z)" and dfd: "dfree_BT (operB c z)"
              by simp_all
            have "\<forall>N'. N' \<in> ST_PS \<longrightarrow> leBT (Trans N') (operB c z)
                          \<longrightarrow> N' \<in> Wellfounded.acc y3_PSSrel"
              using dY otd dfd by (simp add: Y_def)
            thus ?thesis using KST lez by blast
          qed
        qed
      qed
      show ?thesis using body by (simp add: Y_def)
    qed
  qed
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  obtain v where vW: "Trans M \<in> bwl_W v" using y3_Trans_W[OF MR] by blast
  have sub: "bwl_W v \<subseteq> Y" by (rule bwl_A2'[OF Ycl])
  have MY: "Trans M \<in> Y" using vW sub by blast
  have MOT: "Trans M \<in> OT_B" by (rule TOT[OF MST])
  have otM: "isOT_BT (Trans M)" and dfM: "dfree_BT (Trans M)"
    using MOT by (simp_all add: OT_B_def OT_def T_B_def)
  have "\<forall>N. N \<in> ST_PS \<longrightarrow> leBT (Trans N) (Trans M)
              \<longrightarrow> N \<in> Wellfounded.acc y3_PSSrel"
    using MY otM dfM by (simp add: Y_def)
  thus ?thesis using MST by blast
qed

text \<open>\<^bold>\<open>r72\<close>: the two \<open>OKH\<close> capstones (\<open>y3_PSS_acc_of_OKH_cofimg\<close> /
  \<open>y3_PSS_acc_of_OKH_bwl_cof\<close>) are WITHDRAWN together with \<open>oi9_census_OKH\<close> --- their
  \<open>OKH\<close> hypothesis was refuted in r70 (@{thm [source] ox10_cex_not_ok}), so they were
  vacuous; the live capstones are \<open>y4_PSS_acc_of_KK\<close> / \<open>y4_PSS_wf_of_KK\<close> below,
  driven by the \<open>KK\<close> spine bound.\<close>
(* ===== end r70 y3 block ===== *)

text \<open>\<^bold>\<open>MECHANICAL PROOF-TERM AUDIT (r70-y3, Isabelle2025-2).\<close>  The dependency
  graphs were walked with \<open>Proofterm.fold_body_thms\<close> and intersected with the 131
  \<open>sorry\<close>-carrying statements of \<open>pss_paper\<close>.  Result:

  \<^item> @{thm [source] y3_PSS_acc_of_cofimg} (the engine): \<^bold>\<open>0 sorry-dependencies\<close>.
  \<^item> @{thm [source] y3_W_acc}, @{thm [source] y3_TBv_dfree_W},
    @{thm [source] y3_cof0_imp_bwl_cof}, @{thm [source] bwl_2_8_principal}: 0 each.
  \<^item> the (r72-withdrawn) \<open>y3_PSS_acc_of_OKH_cofimg\<close> capstone and \<open>oi9_census_OKH\<close>:
    \<^bold>\<open>exactly ONE\<close> — \<open>pss_paper.buc1_3_2a_fseq_lt\<close>.

  So \<open>buc1_2_2_OT_B_wf\<close> ([Buc1] Lemma 2.2, \<open>wf (<)\<close>) is \<^bold>\<open>OUT of the graph\<close>: the
  W-induction engine replaces it.  The single remaining \<open>sorry\<close> in the chain,
  \<open>buc1_3_2a_fseq_lt\<close> (\<open>a \<noteq> 0 \<Longrightarrow> a[n] < a\<close>), is a \<^emph>\<open>stale citation\<close>: the identical
  statement is already PROVEN as \<open>m_buc1_3_2a_fseq_lt\<close> (\<open>layerB/pss_wip.thy\<close> 49765).
  Removing it is a mechanical swap at the 7 call sites that still cite the paper
  version (\<open>layerB/pss_wip.thy\<close> lines 27797, 27874, 36809, 39574, 39633, 51962, 51989)
  — a FROZEN-layer edit, so it is left to the parent (one \<open>PSS_B\<close> rebuild).  After
  that swap the whole termination chain is \<open>sorry\<close>-free modulo the two named
  hypotheses \<open>OKH\<close> and \<open>y3_cofimg\<close>.\<close>

text \<open>\<^bold>\<open>WHY THE CORRESPONDENCE IS NOT AN EQUATION\<close> (r70-y3 refutation, empirical, 397
  genuine \<open>ST\<^bsub>PS\<^esub>\<close> hosts via \<open>python/_r15_vx_lib.py\<close>).  For \<open>EQ := (\<exists>k. Trans (M[n])
  = operB (Trans M) (numBT k))\<close>: cond (I) 332/332, cond (VI) 132/132, cond (III)
  72/196 — and the 72 successes are EXACTLY the hosts with \<open>dom (Trans M) = T\<^sub>u\<close>;
  cond (IV) 0/4, cond (V) 0/70.  \<open>\<le>\<close> holds 100%.  Widening the fseq argument from
  numerals to ARBITRARY \<open>D\<^sub>\<omega>\<close>-free \<open>z\<close> adds ZERO equalities, and every failing host
  has \<open>dom (Trans M) = \<nat>\<close>, whose fseq children ARE exactly the numerals.  Minimal
  witness \<open>M = (0,0)(1,1)(2,1)\<close>, \<open>n = 2\<close> (condIII): \<open>Trans (M[2])\<close> lies STRICTLY
  between two consecutive members of the fundamental sequence of \<open>Trans M\<close> — it is a
  grand-child (reached at fseq-depth 3), not a child.  Hence (W2)/(W3) alone cannot
  see the PSS step, and the \<open>\<le>\<close> must be absorbed by a cofinality property — which is
  precisely what \<open>y3_cofimg\<close> is.  This is consistent with the proven exchange slots:
  @{thm [source] npx_exchIII_slot_uncond}, @{thm [source] dpx_exchIV_slot_uncond},
  @{thm [source] dpx_exchVI_slot_uncond} are \<open>leBT\<close>-only, and
  @{thm [source] c613x_condVI_exch_adm} is even a STRICT \<open><\<close>.\<close>

(* ===== end r70 y3 audit/refutation notes ===== *)


text \<open>\<^bold>\<open>Round-70 capstone (re-based).\<close>  \<open>oi9_census_OKH\<close> is VACUOUS
  (its hypothesis \<open>OKH\<close> is refuted --- see @{thm [source] ox10_cex_not_ok}), so the
  termination engine must be fed by the TRUE census @{thm [source] oi10_census_KK}.
  Result: PSS termination (accessibility of the step relation) modulo EXACTLY
  \<open>{KK, y3_cofimg}\<close> --- with \<^bold>\<open>no\<close> \<open>wf\<close>, no \<open>buc1_2_2\<close>, no \<open>bwl_cof\<close>.\<close>

theorem y3_PSS_acc_of_KK_cofimg:
  assumes KK: "\<And>P s0 b0 k. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
             hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIII P \<or> transCondIV P \<Longrightarrow>
             (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
             scb_decomp (bpHeadT (Trans (s84x_N P))) s0
               (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
             s84x_jm3 P < transJm1 P \<Longrightarrow>
             1 \<le> k \<Longrightarrow>
             (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B) \<Longrightarrow>
             lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
               (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                  0\<^sub>B)"
    and COF: "y3_cofimg"
    and MST: "M \<in> ST_PS"
  shows "M \<in> Wellfounded.acc y3_PSSrel"
proof -
  have TOT: "\<And>N. N \<in> ST_PS \<Longrightarrow> Trans N \<in> OT_B"
    using oi10_census_KK(1)[OF KK] by blast
  have DESC: "\<And>N n. N \<in> ST_PS \<Longrightarrow> 1 \<le> n \<Longrightarrow> 1 < Lng N \<Longrightarrow>
                lessBT (Trans ((N::pairseq)[n])) (Trans N)"
    using oi10_census_KK(2)[OF KK] by blast
  show ?thesis by (rule y3_PSS_acc_of_cofimg[OF DESC TOT COF MST])
qed

(* =====================================================================
   r71 front KK (prefix  ox11_ ).  THE POSITIONAL TRANSPORT.

   r70 left ONE residual for both termination pillars:

     KK(k) :  lessBT (ox8_rsub body k) X1        (1 <= k, spine alive)
       body = bpHeadT (Trans (s84x_N P)),  v1 = entry P 1 (Lng P - 1),
       ub   = v1 - 1,  X0 = D_ub 0,  X1 = body[hole := D_ub X0],
       hole = D_v1 0 = the LAST principal of  ox8_rsub body dR  (the
              deepest right-spine level; ox9_holeD dR ... body X1).

   We KNOW  lessBT (ox8_rsub body k) body   unconditionally
   (@{thm [source] ox8_body_rspine_lessBT}: the self-maximality of the census
   spine, from the OT2 condition of the OT principal D_e3 body).  Since
   X1 < body, that does NOT give KK: the surgery LOWERS the right operand.

   The r69/r70 route tried to transport the verdict across the surgery with a
   GLOBAL guard (\<open>ox9_ok\<close> = "every principal anywhere is harmless").  That guard
   is FALSE (@{thm [source] ox10_cex_not_ok}) --- and no weakening of it can work,
   because the refuting principal is an EQUALITY witness.  The repair is
   @{thm [source] ox10_lexP}: the guard is only ever CONSUMED at the position of
   the right operand's hole.  This block builds the tree-level analogue.

   \<open>ox11_safe e p q Z W\<close> = "the lex walk of Z against W is decided STRICTLY ABOVE
   the hole (or reaches it harmlessly)": at every level of the hole path it
   either decides left of the hole-aligned index, or ties on the head and
   recurses; only at the bottom does it consume a guard on the hole principal.

   \<open>ox11_TT\<close> is then the positional analogue of \<open>ox9_TT\<close>, with NO global guard.
   ===================================================================== *)

section \<open>r71 ox11 --- the POSITIONAL transport (the repair of \<open>ox9_TT\<close>)\<close>

subsection \<open>(1) A prefix verdict survives any extension of the right operand\<close>

text \<open>If the walk is decided strictly LEFT of the right operand's last principal
  --- i.e. already against the prefix \<open>ps\<close> --- then the last principal is
  irrelevant, whatever it is.  (\<open>xs = ps\<close> is included: a proper prefix is
  smaller.)  This is the \<open>A\<close>-case of the walk, and it is where the surgery is
  invisible.\<close>

lemma ox11_snoc_le:
  "leBT (Trm xs) (Trm ps) \<Longrightarrow> lessBT (Trm xs) (Trm (ps @ [q]))"
proof (induction ps arbitrary: xs)
  case Nil
  have "xs = []" using Nil ox9_lessBT_zero by (cases xs) auto
  thus ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis by simp
  next
    case (Cons x xs')
    have D: "lessBP x y \<or> (x = y \<and> leBT (Trm xs') (Trm ys))"
      using Cons.prems Cons by auto
    thus ?thesis
    proof
      assume "lessBP x y"
      thus ?thesis using Cons by simp
    next
      assume A: "x = y \<and> leBT (Trm xs') (Trm ys)"
      have "lessBT (Trm xs') (Trm (ys @ [q]))" using Cons.IH A by blast
      thus ?thesis using Cons A by simp
    qed
  qed
qed


subsection \<open>(2) \<open>ox11_safe\<close>: the walk is decided above the hole\<close>

text \<open>\<open>ox11_safe e p q Z W\<close>.  \<open>W\<close> carries the hole \<open>p\<close> at right-spine depth \<open>e\<close>
  (as in @{const ox9_holeD}), and \<open>q\<close> is the replacement.  At the bottom
  (\<open>e = 0\<close>) the hole principal \<open>p\<close> is the LAST principal of \<open>W\<close>, and the ONLY
  thing that can break the transport is a left principal sitting at exactly the
  hole-aligned index \<open>\<bar>ps\<bar>\<close> (after the prefix \<open>ps\<close> has been matched verbatim)
  which is \<open>< p\<close> but not \<open>< q\<close>.  Above the bottom, the hole is buried inside the
  LAST principal's body, so the walk only ever meets it after tying on the head
  \<open>w\<close> at the hole-aligned index --- and then the requirement recurses one level
  down.  Everything else (a verdict left of the hole-aligned index, a strictly
  smaller head at it, a shorter left list) is untouched by the surgery and needs
  no hypothesis at all.\<close>

fun ox11_safe :: "nat \<Rightarrow> BP \<Rightarrow> BP \<Rightarrow> BT \<Rightarrow> BT \<Rightarrow> bool" where
  "ox11_safe 0 p q Z W =
     (\<forall>ps x rest. W = Trm (ps @ [p]) \<longrightarrow> Z = Trm (ps @ x # rest)
        \<longrightarrow> lessBP x p \<longrightarrow> lessBP x q)"
| "ox11_safe (Suc e) p q Z W =
     (\<forall>ps w LW t rest. W = Trm (ps @ [DB w LW]) \<longrightarrow> Z = Trm (ps @ DB w t # rest)
        \<longrightarrow> lessBT t LW \<longrightarrow> ox11_safe e p q t LW)"


subsection \<open>(3) \<open>ox11_TT\<close>: THE POSITIONAL TRANSPORT\<close>

text \<open>The analogue of @{thm [source] ox9_TT}, with the refuted global guard
  @{const ox9_ok} replaced by the positional @{const ox11_safe}.  Every step is
  @{thm [source] ox10_lexP}: at depth \<open>Suc e\<close> the two operands' hole principals
  share their HEAD \<open>w\<close> (the surgery is buried in the body), so the head
  comparison transports verbatim and only the body branch recurses.\<close>

lemma ox11_TT:
  "ox9_holeD e p q W A \<Longrightarrow> ox11_safe e p q Z W \<Longrightarrow> lessBT Z W \<Longrightarrow> lessBT Z A"
proof (induction e p q W A arbitrary: Z rule: ox9_holeD.induct)
  case (ox9_hD0 p q ps)
  obtain zs where Z: "Z = Trm zs" by (cases Z)
  have SF: "ox11_safe 0 p q (Trm zs) (Trm (ps @ [p]))"
    using ox9_hD0.prems(1) Z by simp
  have G: "\<forall>rest x. zs = ps @ x # rest \<longrightarrow> lessBP x p \<longrightarrow> lessBP x q"
  proof (intro allI impI)
    fix rest x assume E: "zs = ps @ x # rest" and L: "lessBP x p"
    have H: "\<forall>ps' x' rest'. Trm (ps @ [p]) = Trm (ps' @ [p])
               \<longrightarrow> Trm zs = Trm (ps' @ x' # rest') \<longrightarrow> lessBP x' p \<longrightarrow> lessBP x' q"
      using SF by simp
    show "lessBP x q" using H E L by blast
  qed
  have lt: "lessBT (Trm zs) (Trm (ps @ [p]))" using ox9_hD0.prems(2) Z by simp
  show ?case using ox10_lexP[OF lt G] Z by simp
next
  case (ox9_hDS k p q b b' ps w)
  obtain zs where Z: "Z = Trm zs" by (cases Z)
  have SF: "ox11_safe (Suc k) p q (Trm zs) (Trm (ps @ [DB w b]))"
    using ox9_hDS.prems(1) Z by simp
  have H: "\<forall>ps' w' LW t' rest'. Trm (ps @ [DB w b]) = Trm (ps' @ [DB w' LW])
             \<longrightarrow> Trm zs = Trm (ps' @ DB w' t' # rest')
             \<longrightarrow> lessBT t' LW \<longrightarrow> ox11_safe k p q t' LW"
    using SF by simp
  have lt: "lessBT (Trm zs) (Trm (ps @ [DB w b]))" using ox9_hDS.prems(2) Z by simp
  have G: "\<forall>rest x. zs = ps @ x # rest \<longrightarrow> lessBP x (DB w b) \<longrightarrow> lessBP x (DB w b')"
  proof (intro allI impI)
    fix rest x assume E: "zs = ps @ x # rest" and L: "lessBP x (DB w b)"
    obtain a t where xd: "x = DB a t" by (cases x)
    have "a < w \<or> (a = w \<and> lessBT t b)" using L xd by simp
    thus "lessBP x (DB w b')"
    proof
      assume "a < w"
      thus ?thesis using xd by simp
    next
      assume A: "a = w \<and> lessBT t b"
      have E': "Trm zs = Trm (ps @ DB w t # rest)" using E xd A by simp
      have sf: "ox11_safe k p q t b" using H E' A by blast
      have "lessBT t b'" by (rule ox9_hDS.IH[OF sf]) (use A in simp)
      thus ?thesis using xd A by simp
    qed
  qed
  show ?case using ox10_lexP[OF lt G] Z by simp
qed

text \<open>@{thm [source] ox9_TT} is the special case in which @{const ox11_safe} is
  discharged from the (refuted) global @{const ox9_ok}: hereditarily-\<open>ok\<close> left
  operands are safe at EVERY position, in particular at the hole-aligned ones.\<close>

lemma ox11_safe_of_ok_aux:
  assumes PX: "\<And>x. ox9_okP v ub x \<Longrightarrow> lessBP x p \<Longrightarrow> lessBP x q"
  shows "\<forall>Z W. ox9_ok v ub Z \<longrightarrow> ox11_safe e p q Z W"
proof (induction e)
  case 0
  show ?case
  proof (intro allI impI)
    fix Z W :: BT assume OK: "ox9_ok v ub Z"
    have G: "\<forall>ps x rest. W = Trm (ps @ [p]) \<longrightarrow> Z = Trm (ps @ x # rest)
               \<longrightarrow> lessBP x p \<longrightarrow> lessBP x q"
    proof (intro allI impI)
      fix ps x rest
      assume "W = Trm (ps @ [p])" and ZE: "Z = Trm (ps @ x # rest)" and L: "lessBP x p"
      have "ox9_okP v ub x" using OK ZE by simp
      thus "lessBP x q" by (rule PX[OF _ L])
    qed
    show "ox11_safe 0 p q Z W" using G by simp
  qed
next
  case (Suc e)
  show ?case
  proof (intro allI impI)
    fix Z W :: BT assume OK: "ox9_ok v ub Z"
    have G: "\<forall>ps w LW t rest. W = Trm (ps @ [DB w LW])
               \<longrightarrow> Z = Trm (ps @ DB w t # rest)
               \<longrightarrow> lessBT t LW \<longrightarrow> ox11_safe e p q t LW"
    proof (intro allI impI)
      fix ps w LW t rest
      assume "W = Trm (ps @ [DB w LW])" and ZE: "Z = Trm (ps @ DB w t # rest)"
        and "lessBT t LW"
      have "ox9_okP v ub (DB w t)" using OK ZE by simp
      hence "ox9_ok v ub t" by simp
      thus "ox11_safe e p q t LW" using Suc.IH by blast
    qed
    show "ox11_safe (Suc e) p q Z W" using G by simp
  qed
qed

lemma ox11_safe_of_ok:
  assumes PX: "\<And>x. ox9_okP v ub x \<Longrightarrow> lessBP x p \<Longrightarrow> lessBP x q"
    and OK: "ox9_ok v ub Z"
  shows "ox11_safe e p q Z W"
  using ox11_safe_of_ok_aux[of v ub p q e] PX OK by blast


subsection \<open>(4) Discharging \<open>ox11_safe\<close> from a CLOSED SET plus a BOTTOM GUARD\<close>

text \<open>\<open>ox11_spge v e W\<close>: the first \<open>e\<close> right-spine heads of \<open>W\<close> are \<open>\<ge> v\<close>.  On the
  census body this is @{thm [source] ox7_RightNodes_body_ge_v1}.\<close>

fun ox11_spge :: "enat \<Rightarrow> nat \<Rightarrow> BT \<Rightarrow> bool" where
  "ox11_spge v 0 W = True"
| "ox11_spge v (Suc e) W =
     (\<forall>ps w LW. W = Trm (ps @ [DB w LW]) \<longrightarrow> (v \<le> w \<and> ox11_spge v e LW))"

lemma ox11_spge_of_rsub:
  "(\<And>j. j < e \<Longrightarrow> ox8_rsub W j \<noteq> 0\<^sub>B \<and> v \<le> ox8_lastV (ox8_rsub W j))
     \<Longrightarrow> ox11_spge v e W"
proof (induction e arbitrary: W)
  case 0
  thus ?case by simp
next
  case (Suc e)
  have "\<forall>ps w LW. W = Trm (ps @ [DB w LW]) \<longrightarrow> (v \<le> w \<and> ox11_spge v e LW)"
  proof (intro allI impI)
    fix ps w LW assume WE: "W = Trm (ps @ [DB w LW])"
    have lv: "ox8_lastV W = w" using WE by simp
    have lt: "ox8_lastT W = LW" using WE by simp
    have h0: "v \<le> ox8_lastV (ox8_rsub W 0)" using Suc.prems[of 0] by simp
    have vw: "v \<le> w" using h0 lv by simp
    have IHp: "\<And>j. j < e \<Longrightarrow> ox8_rsub LW j \<noteq> 0\<^sub>B \<and> v \<le> ox8_lastV (ox8_rsub LW j)"
    proof -
      fix j assume je: "j < e"
      have sj: "Suc j < Suc e" using je by simp
      have H: "ox8_rsub W (Suc j) \<noteq> 0\<^sub>B \<and> v \<le> ox8_lastV (ox8_rsub W (Suc j))"
        using Suc.prems sj by blast
      have R: "ox8_rsub W (Suc j) = ox8_rsub LW j" using lt by simp
      show "ox8_rsub LW j \<noteq> 0\<^sub>B \<and> v \<le> ox8_lastV (ox8_rsub LW j)" using H R by simp
    qed
    have "ox11_spge v e LW" by (rule Suc.IH[OF IHp])
    thus "v \<le> w \<and> ox11_spge v e LW" using vw by simp
  qed
  thus ?case by simp
qed

text \<open>\<^bold>\<open>The reduction.\<close>  Let \<open>S\<close> be any set of trees that contains the left operand
  and is CLOSED under "body of a top-level principal whose head is \<open>\<ge> v\<close>"
  (on the census: \<open>S = {body} \<union> G\<^bsub>v\<^sub>1\<^esub>(body)\<close>, closed by
  @{thm [source] b1x_GBT_trans}).  Since every hole-path head of \<open>W\<close> is \<open>\<ge> v\<close>,
  every term the walk can descend into stays inside \<open>S\<close>.  Hence @{const ox11_safe}
  follows from a SINGLE guard, at the BOTTOM level only:

    no \<open>t \<in> S\<close> whose principal list begins with the bottom prefix \<open>ps\<close> carries, at
    the hole-aligned index \<open>\<bar>ps\<bar>\<close>, a principal that is \<open>< p\<close> but not \<open>< q\<close>.

  This is the positional replacement of the refuted @{const ox9_ok}: the same
  implication, but demanded ONLY at the one index where the walk can consume it.\<close>

lemma ox11_safe_of_set:
  fixes S :: "BT set" and v :: enat and B :: BT
  assumes CL: "\<And>t ps w b rest. t \<in> S \<Longrightarrow> t = Trm (ps @ DB w b # rest) \<Longrightarrow> v \<le> w
                 \<Longrightarrow> b \<in> S"
    and BG: "\<And>t ps x rest. t \<in> S \<Longrightarrow> B = Trm (ps @ [p]) \<Longrightarrow> t = Trm (ps @ x # rest)
                 \<Longrightarrow> lessBP x p \<Longrightarrow> lessBP x q"
  shows "\<forall>W Z. ox8_rsub W e = B \<longrightarrow> ox11_spge v e W \<longrightarrow> Z \<in> S
           \<longrightarrow> ox11_safe e p q Z W"
proof (induction e)
  case 0
  show ?case
  proof (intro allI impI)
    fix W Z :: BT
    assume R: "ox8_rsub W 0 = B" and ZS: "Z \<in> S"
    have WB: "W = B" using R by simp
    have G: "\<forall>ps x rest. W = Trm (ps @ [p]) \<longrightarrow> Z = Trm (ps @ x # rest)
               \<longrightarrow> lessBP x p \<longrightarrow> lessBP x q"
    proof (intro allI impI)
      fix ps x rest
      assume WE: "W = Trm (ps @ [p])" and ZE: "Z = Trm (ps @ x # rest)"
        and L: "lessBP x p"
      have BE: "B = Trm (ps @ [p])" using WB WE by simp
      show "lessBP x q" by (rule BG[OF ZS BE ZE L])
    qed
    show "ox11_safe 0 p q Z W" using G by simp
  qed
next
  case (Suc e)
  show ?case
  proof (intro allI impI)
    fix W Z :: BT
    assume R: "ox8_rsub W (Suc e) = B" and SP: "ox11_spge v (Suc e) W"
      and ZS: "Z \<in> S"
    have SPU: "\<forall>ps w LW. W = Trm (ps @ [DB w LW])
                 \<longrightarrow> (v \<le> w \<and> ox11_spge v e LW)" using SP by simp
    have G: "\<forall>ps w LW t rest. W = Trm (ps @ [DB w LW])
               \<longrightarrow> Z = Trm (ps @ DB w t # rest)
               \<longrightarrow> lessBT t LW \<longrightarrow> ox11_safe e p q t LW"
    proof (intro allI impI)
      fix ps w LW t rest
      assume WE: "W = Trm (ps @ [DB w LW])" and ZE: "Z = Trm (ps @ DB w t # rest)"
        and L: "lessBT t LW"
      have H: "v \<le> w \<and> ox11_spge v e LW" using SPU WE by blast
      have tS: "t \<in> S" by (rule CL[OF ZS ZE]) (use H in simp)
      have rs: "ox8_rsub LW e = B"
      proof -
        have "ox8_rsub W (Suc e) = ox8_rsub LW e" using WE by simp
        thus ?thesis using R by simp
      qed
      show "ox11_safe e p q t LW" using Suc.IH rs H tS by blast
    qed
    show "ox11_safe (Suc e) p q Z W" using G by simp
  qed
qed



subsection \<open>(5) The census: \<open>KK\<close> from the BOTTOM GUARD alone\<close>

lemma ox11_holeD_ne2:
  assumes "ox9_holeD e p q t t'"
  shows "t' \<noteq> 0\<^sub>B"
  using assms by (cases rule: ox9_holeD.cases) auto

text \<open>\<^bold>\<open>The r71 reduction.\<close>  \<open>KK\<close> --- the LAST residual of the termination census
  --- follows from the single POSITIONAL guard

  \<open>BG\<close>:  no \<open>t\<close> in \<open>{body} \<union> G\<^bsub>v\<^sub>1\<^esub>(body)\<close> whose principal list starts with the
        bottom prefix \<open>ps\<close> (\<open>ox8_rsub body d = Trm (ps @ [D\<^bsub>v\<^sub>1\<^esub>0])\<close>) carries at the
        hole-aligned index \<open>\<bar>ps\<bar>\<close> a principal that is \<open>< D\<^bsub>v\<^sub>1\<^esub>0\<close> but not \<open>< D\<^bsub>ub\<^esub>X\<^sub>0\<close>.

  Everything else is unconditional:
  \<^item> \<open>lessBT (ox8_rsub body k) body\<close> --- @{thm [source] ox8_body_rspine_lessBT};
  \<^item> the hole structure \<open>ox9_holeD dR (D\<^bsub>v\<^sub>1\<^esub>0) (D\<^bsub>ub\<^esub>X\<^sub>0) body X\<^sub>1\<close> --- the flat surgery;
  \<^item> every hole-path head of \<open>body\<close> is \<open>\<ge> v\<^sub>1\<close> --- @{thm [source] ox7_RightNodes_body_ge_v1};
  \<^item> hence every right-spine sub-body lies in \<open>G\<^bsub>v\<^sub>1\<^esub>(body)\<close> --- @{thm [source] ox8_rsub_GBT} ---
    and \<open>G\<^bsub>v\<^sub>1\<^esub>\<close> is closed under the walk's descents --- @{thm [source] b1x_GBT_trans};
  \<^item> the transport --- @{thm [source] ox11_TT} / @{thm [source] ox11_safe_of_set}.

  \<open>BG\<close> is the positional replacement of the REFUTED global @{const ox9_ok}: the same
  implication, demanded only at the one index where @{thm [source] ox10_lexP} can
  consume it.  The r70 counterexample principal \<open>D\<^sub>0(D\<^sub>0 0)\<close> lives at index 1 of a
  \<open>G\<^bsub>v\<^sub>1\<^esub>\<close>-element whose hole-aligned index is 0, so it does not refute \<open>BG\<close>.\<close>

lemma ox11_KK_of_BG:
  fixes N :: pairseq and s0 b0 :: "Sym list" and k :: nat
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ihOT: "Trans N \<in> OT_B"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                 (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and BG: "\<And>t ps x rest d.
               t \<in> insert (bpHeadT (Trans (s84x_N N)))
                     (GBT (enat (entry N 1 (Lng N - 1)))
                          (bpHeadT (Trans (s84x_N N)))) \<Longrightarrow>
               ox8_rsub (bpHeadT (Trans (s84x_N N))) d
                 = Trm (ps @ [DB (enat (entry N 1 (Lng N - 1))) 0\<^sub>B]) \<Longrightarrow>
               t = Trm (ps @ x # rest) \<Longrightarrow>
               lessBP x (DB (enat (entry N 1 (Lng N - 1))) 0\<^sub>B) \<Longrightarrow>
               lessBP x (DB (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B)"
    and kge: "1 \<le> k"
    and alive: "\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N N))) j \<noteq> 0\<^sub>B"
  shows "lessBT (ox8_rsub (bpHeadT (Trans (s84x_N N))) k)
           (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
              0\<^sub>B)"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X0 = "(0\<^sub>B :: BT)"
  let ?X1 = "d4vx_ins s0 ?ub b0 ?X0"
  let ?A1 = "d4vx_ins s0 ?ub b0 ?A0"
  let ?p = "DB (enat ?v1) 0\<^sub>B"
  let ?pX = "DB (enat ?ub) ?X0"
  let ?S = "insert ?body (GBT (enat ?v1) ?body)"
  \<comment> \<open>the three flat surgery strings, and the hole relation they induce\<close>
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have fA1: "flatBT ?A1 = s0 @ flatBP (DB (enat ?ub) ?A0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ?ub ?A0] by simp
  have fX1: "flatBT ?X1 = s0 @ flatBP (DB (enat ?ub) ?X0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ?ub ?X0] by simp
  obtain dR where
      hdA: "ox9_holeD dR ?p (DB (enat ?ub) ?A0) ?body ?A1"
    and hdX: "ox9_holeD dR ?p ?pX ?body ?X1"
    using ox9_holeD_of_flat3[OF wrap fA1 fX1 b0RP] by blast
  \<comment> \<open>\<open>d\<close>-freeness and the right-spine head bound\<close>
  have bodyTB: "?body \<in> T_B" by (rule oi5_regime(3)[OF NST NPT hp j1gt branch])
  have dfb: "dfree_BT ?body" using bodyTB by (simp add: T_B_def)
  have RNge: "\<forall>x \<in> set (RightNodes ?body). ?v1 \<le> x"
    by (rule ox7_RightNodes_body_ge_v1[OF NST NPT hp j1gt branch ltJ])
  \<comment> \<open>the hole path is alive down to \<open>dR\<close>, and its heads are \<open>\<ge> v\<^sub>1\<close>\<close>
  have aliveD: "\<And>j. j \<le> dR \<Longrightarrow> ox8_rsub ?body j \<noteq> 0\<^sub>B"
  proof -
    fix j :: nat assume jle: "j \<le> dR"
    have "ox9_holeD (dR - j) ?p ?pX (ox8_rsub ?body j) (ox8_rsub ?X1 j)"
      by (rule ox9_holeD_rsub[OF hdX jle])
    thus "ox8_rsub ?body j \<noteq> 0\<^sub>B" by (rule ox9_holeD_ne)
  qed
  have headge: "\<And>j. j \<le> dR \<Longrightarrow> enat ?v1 \<le> ox8_lastV (ox8_rsub ?body j)"
  proof -
    fix j :: nat assume jle: "j \<le> dR"
    have ne: "ox8_rsub ?body j \<noteq> 0\<^sub>B" by (rule aliveD[OF jle])
    have prem: "\<forall>i\<le>j. ox8_rsub ?body i \<noteq> 0\<^sub>B"
    proof (intro allI impI)
      fix i assume "i \<le> j"
      hence "i \<le> dR" using jle by simp
      thus "ox8_rsub ?body i \<noteq> 0\<^sub>B" by (rule aliveD)
    qed
    have mem: "the_enat (ox8_lastV (ox8_rsub ?body j)) \<in> set (RightNodes ?body)"
      by (rule ox8_rsub_head_RN[OF prem])
    have ge: "?v1 \<le> the_enat (ox8_lastV (ox8_rsub ?body j))" using RNge mem by blast
    have dfj: "dfree_BT (ox8_rsub ?body j)" by (rule ox8_dfree_rsub[OF dfb])
    have fin: "ox8_lastV (ox8_rsub ?body j) \<noteq> \<infinity>" by (rule ox8_dfree_lastV[OF dfj ne])
    obtain i where vi: "ox8_lastV (ox8_rsub ?body j) = enat i"
      using fin by (cases "ox8_lastV (ox8_rsub ?body j)") auto
    have "?v1 \<le> i" using ge vi by simp
    thus "enat ?v1 \<le> ox8_lastV (ox8_rsub ?body j)" using vi by simp
  qed
  \<comment> \<open>the bottom level: the hole is the LAST principal there, so the spine dies at \<open>dR+1\<close>\<close>
  have hd0: "ox9_holeD 0 ?p ?pX (ox8_rsub ?body dR) (ox8_rsub ?X1 dR)"
    using ox9_holeD_rsub[OF hdX le_refl] by simp
  obtain psR where BR: "ox8_rsub ?body dR = Trm (psR @ [?p])"
    and XR: "ox8_rsub ?X1 dR = Trm (psR @ [?pX])"
    by (rule ox9_holeD_0E[OF hd0])
  show ?thesis
  proof (cases "k \<le> dR")
    case True
    \<comment> \<open>the left operand lives in the closed set \<open>S\<close>\<close>
    have alive2: "\<forall>j<k. ox8_rsub ?body j \<noteq> 0\<^sub>B
                        \<and> enat ?v1 \<le> ox8_lastV (ox8_rsub ?body j)"
    proof (intro allI impI)
      fix j assume jk: "j < k"
      have jle: "j \<le> dR" using jk True by simp
      show "ox8_rsub ?body j \<noteq> 0\<^sub>B \<and> enat ?v1 \<le> ox8_lastV (ox8_rsub ?body j)"
        using aliveD[OF jle] headge[OF jle] by simp
    qed
    have ZS: "ox8_rsub ?body k \<in> ?S"
    proof -
      have "ox8_rsub ?body k \<in> GBT (enat ?v1) ?body"
        by (rule ox8_rsub_GBT[OF kge alive2])
      thus ?thesis by simp
    qed
    \<comment> \<open>\<open>S\<close> is closed under the walk's descents\<close>
    have CL: "\<And>t ps w b rest. t \<in> ?S \<Longrightarrow> t = Trm (ps @ DB w b # rest)
                \<Longrightarrow> enat ?v1 \<le> w \<Longrightarrow> b \<in> ?S"
    proof -
      fix t :: BT and ps rest :: "BP list" and w :: enat and b :: BT
      assume tS: "t \<in> ?S" and tE: "t = Trm (ps @ DB w b # rest)"
        and vw: "enat ?v1 \<le> w"
      have bin: "b \<in> GBT (enat ?v1) t"
      proof -
        have "b \<in> GBP (enat ?v1) (DB w b)" using vw by simp
        moreover have "DB w b \<in> set (ps @ DB w b # rest)" by simp
        ultimately show ?thesis using tE by auto
      qed
      show "b \<in> ?S"
      proof (cases "t = ?body")
        case True
        thus ?thesis using bin by simp
      next
        case False
        hence tG: "t \<in> GBT (enat ?v1) ?body" using tS by simp
        have "GBT (enat ?v1) t \<subseteq> GBT (enat ?v1) ?body" by (rule b1x_GBT_trans[OF tG])
        thus ?thesis using bin by auto
      qed
    qed
    have spge: "ox11_spge (enat ?v1) dR ?body"
    proof (rule ox11_spge_of_rsub)
      fix j :: nat assume "j < dR"
      hence jle: "j \<le> dR" by simp
      show "ox8_rsub ?body j \<noteq> 0\<^sub>B \<and> enat ?v1 \<le> ox8_lastV (ox8_rsub ?body j)"
        using aliveD[OF jle] headge[OF jle] by simp
    qed
    have BG': "\<And>t ps x rest. t \<in> ?S \<Longrightarrow> ox8_rsub ?body dR = Trm (ps @ [?p])
                 \<Longrightarrow> t = Trm (ps @ x # rest) \<Longrightarrow> lessBP x ?p \<Longrightarrow> lessBP x ?pX"
      by (rule BG)
    have SS: "\<forall>W Z. ox8_rsub W dR = ox8_rsub ?body dR \<longrightarrow> ox11_spge (enat ?v1) dR W
                \<longrightarrow> Z \<in> ?S \<longrightarrow> ox11_safe dR ?p ?pX Z W"
      by (rule ox11_safe_of_set[OF CL BG'])
    have safe: "ox11_safe dR ?p ?pX (ox8_rsub ?body k) ?body"
      using SS spge ZS by blast
    have lt: "lessBT (ox8_rsub ?body k) ?body"
      by (rule ox8_body_rspine_lessBT[OF NST NPT hp j1gt branch ihOT ltJ kge alive])
    show ?thesis by (rule ox11_TT[OF hdX safe lt])
  next
    case False
    \<comment> \<open>past the hole the spine is dead: \<open>k = dR+1\<close> and the left operand is \<open>0\<close>\<close>
    have kgt: "dR < k" using False by simp
    have zeroS: "ox8_rsub ?body (Suc dR) = 0\<^sub>B"
    proof -
      have "ox8_lastT (ox8_rsub ?body dR) = 0\<^sub>B" using BR by simp
      thus ?thesis using ox9_rsub_Suc[of ?body dR] by simp
    qed
    have kSuc: "k = Suc dR"
    proof (rule ccontr)
      assume "k \<noteq> Suc dR"
      hence "Suc dR < k" using kgt by simp
      thus False using alive zeroS by blast
    qed
    have z: "ox8_rsub ?body k = 0\<^sub>B" using kSuc zeroS by simp
    have X1ne: "?X1 \<noteq> 0\<^sub>B" by (rule ox11_holeD_ne2[OF hdX])
    have "lessBT 0\<^sub>B ?X1"
    proof -
      obtain xs where X1e: "?X1 = Trm xs" by (cases ?X1)
      have "xs \<noteq> []" using X1ne X1e by auto
      thus ?thesis using X1e by simp
    qed
    thus ?thesis using z by simp
  qed
qed


subsection \<open>(6) The census roll-up: both pillars from the BOTTOM GUARD alone\<close>

text \<open>\<^bold>\<open>Round-71 capstone.\<close>  @{thm [source] oi10_census_KK} derived both termination
  pillars from \<open>KK\<close>; @{thm [source] ox11_KK_of_BG} derives \<open>KK\<close> from the positional
  bottom guard \<open>BG\<close>.  So both pillars now hold modulo \<open>BG\<close> --- a purely LOCAL
  statement about ONE index of the census body's \<open>G\<^bsub>v\<^sub>1\<^esub>\<close>-closure, with no walk, no
  spine descent and no \<open>ox9_ok\<close> in it.

  Empirically (python/_r71_walk.py; pure \<open>ST_PS\<close> corpus, 537 census hosts / 1205
  peel levels): \<open>KK\<close> 1205/1205, the walk reaches the hole 0 times, and \<open>BG\<close> holds
  with 26 NON-VACUOUS exercises and 0 failures (28/0 even over ALL subterms of
  \<open>body\<close>, i.e. dropping the \<open>G\<^bsub>v\<^sub>1\<^esub>\<close>-restriction).\<close>

theorem oi11_census_BG:
  assumes BG: "\<And>P s0 b0 t ps x rest d. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
             hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
             (\<forall>y \<in> set b0. y = RP) \<Longrightarrow>
             scb_decomp (bpHeadT (Trans (s84x_N P))) s0
               (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
             s84x_jm3 P < transJm1 P \<Longrightarrow>
             t \<in> insert (bpHeadT (Trans (s84x_N P)))
                   (GBT (enat (entry P 1 (Lng P - 1)))
                        (bpHeadT (Trans (s84x_N P)))) \<Longrightarrow>
             ox8_rsub (bpHeadT (Trans (s84x_N P))) d
               = Trm (ps @ [DB (enat (entry P 1 (Lng P - 1))) 0\<^sub>B]) \<Longrightarrow>
             t = Trm (ps @ x # rest) \<Longrightarrow>
             lessBP x (DB (enat (entry P 1 (Lng P - 1))) 0\<^sub>B) \<Longrightarrow>
             lessBP x (DB (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B)"
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
  proof -
    fix P :: pairseq and s0 b0 :: "Sym list" and u :: enat
    assume A1: "P \<in> ST_PS" and A2: "P \<in> PT_PS"
      and A3: "hasParent P 1 (Lng P - 1)" and A4: "1 < Lng P - 1"
      and A5: "transCondIII P \<or> transCondIV P" and A6: "Trans P \<in> OT_B"
      and A7: "\<forall>x \<in> set b0. x = RP"
      and A8: "scb_decomp (bpHeadT (Trans (s84x_N P))) s0
                (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0"
      and A9: "s84x_jm3 P < transJm1 P"
    have BG': "\<And>t ps x rest d.
                 t \<in> insert (bpHeadT (Trans (s84x_N P)))
                       (GBT (enat (entry P 1 (Lng P - 1)))
                            (bpHeadT (Trans (s84x_N P)))) \<Longrightarrow>
                 ox8_rsub (bpHeadT (Trans (s84x_N P))) d
                   = Trm (ps @ [DB (enat (entry P 1 (Lng P - 1))) 0\<^sub>B]) \<Longrightarrow>
                 t = Trm (ps @ x # rest) \<Longrightarrow>
                 lessBP x (DB (enat (entry P 1 (Lng P - 1))) 0\<^sub>B) \<Longrightarrow>
                 lessBP x (DB (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B)"
      by (rule BG[OF A1 A2 A3 A4 A5 A6 A7 A8 A9])
    have H: "\<And>k. 1 \<le> k \<Longrightarrow>
               (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B) \<Longrightarrow>
               lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
                 (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    0\<^sub>B)"
    proof -
      fix k :: nat assume kge: "1 \<le> k"
        and alv: "\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B"
      show "lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
              (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                 0\<^sub>B)"
        by (rule ox11_KK_of_BG[OF A1 A2 A3 A4 A5 A6 A7 A8 A9 BG' kge alv])
    qed
    show "b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
      by (rule ox10_SETLE1_ltJ[OF A1 A2 A3 A4 A5 A7 A8 A9 H])
  qed
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi8_census_final_ivadmeq(1)[OF SETLE1 ot9_FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
         lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi8_census_final_ivadmeq(2)[OF SETLE1 ot9_FINRC])
qed



(* ================================================================= *)
(*   r71 front y4 (prefix  y4_ ).  THE BACHMANN / COFINALITY PROOF.   *)
(*                                                                     *)
(*   Goal: discharge  y3_cof0  (hence  y3_cofimg ), the LAST           *)
(*   non-census residual of PSS termination.                           *)
(*                                                                     *)
(*   NOTE ON THE CITED LEVER (honest report).  The r71 brief pointed   *)
(*   at [Buc1-Hydra] section 3 ("the relations <<_k and the functions  *)
(*   H_a", pp.140-143) as the place where Buchholz PROVES the          *)
(*   step-down/Bachmann machinery.  He does NOT.  Section 3 defines    *)
(*   c <<_k a by transfinite induction and proves 3.1-3.8, but every   *)
(*   one of those lemmas relates <<_k to the fundamental sequences     *)
(*   a[z] and to the Hardy functions H_a (3.6(d): c <<_k a ==>         *)
(*   H_c(n) < H_a(n) for n >= k).  The hydra paper NEVER DEFINES AN    *)
(*   ORDER < ON T at all -- termination there is carried entirely by   *)
(*   the accessibility sets W_v, which is precisely the machinery we   *)
(*   already mechanized in the bwl_ block.  So section 3 contains NO   *)
(*   lemma connecting < to <<_k, and cannot be cited for cofinality.   *)
(*   (The order < and its well-foundedness live in the OTHER Buchholz  *)
(*   paper, [Buc1] = APAL 32 (1986); its Bachmann property is what we  *)
(*   need, and we PROVE it below rather than cite it.)                 *)
(*                                                                     *)
(*   The proof below is self-contained and rests only on the PROVEN    *)
(*   b1x_ toolkit (descent, b1x_mono, b1x_lowerbound, the G-set        *)
(*   lemmas) and the proven order lemmas of pss_mechanized.            *)
(* ================================================================= *)

section \<open>r71-y4 --- the Bachmann (cofinality) property of the fundamental sequences (\<open>y4_\<close>)\<close>

subsection \<open>(1) The \<open>xseq\<close> tower is strictly increasing\<close>

text \<open>\<open>x\<^sub>0 = D\<^sub>u 0\<close>, \<open>x\<^bsub>i+1\<^esub> = c[D\<^sub>u x\<^sub>i]\<close> (the ([].4)(ii) tower).  Strict increase is
  immediate from the two PROVEN facts @{thm [source] b1x_lowerbound} (\<open>z \<le> c[z]\<close> on a
  \<open>T\<^sub>u\<close> domain) and @{thm [source] b1x_mono} (\<open>c[\<cdot>]\<close> strictly monotone there).\<close>

text \<open>\<^bold>\<open>r72\<close>: with the CORRECTED rule every tower member is a \<open>D\<^sub>u\<close>-principal
  (\<open>x\<^sub>0 = D\<^sub>u 0\<close>, \<open>x\<^bsub>j+1\<^esub> = D\<^sub>u (c[x\<^sub>j])\<close>), hence lies in \<open>T\<^sub>u = dom c\<close> --- which is what
  makes \<open>c[x\<^sub>j]\<close> well-formed and the monotonicity toolkit applicable.\<close>

lemma y4_xseq_Dpt: "\<exists>t. xseq c (enat u) n = Trm [DB (enat u) t]"
proof (cases n)
  case 0
  thus ?thesis using b1x_xseq_0[of c "enat u"] by auto
next
  case (Suc j)
  thus ?thesis using b1x_xseq_Suc[of c "enat u" j] by auto
qed

lemma y4_xseq_TBv: "xseq c (enat u) n \<in> TBv (enat u)"
proof -
  obtain t where "xseq c (enat u) n = Trm [DB (enat u) t]"
    using y4_xseq_Dpt by blast
  thus ?thesis using b1x_Dpt_TBv[of u t] by simp
qed

lemma y4_xseq_lt:
  assumes ot: "isOT_BT c" and dc: "domB c = TBv (enat u)"
  shows "lessBT (xseq c (enat u) n) (xseq c (enat u) (Suc n))"
proof (induction n)
  case 0
  have x0: "xseq c (enat u) 0 = Trm [DB (enat u) (Trm [])]" by (rule b1x_xseq_0)
  have x1: "xseq c (enat u) (Suc 0)
              = Trm [DB (enat u) (operB c (xseq c (enat u) 0))]" by (rule b1x_xseq_Suc)
  have zin: "xseq c (enat u) 0 \<in> TBv (enat u)" by (rule y4_xseq_TBv)
  have le: "leBT (xseq c (enat u) 0) (operB c (xseq c (enat u) 0))"
    by (rule b1x_lowerbound[OF ot dc zin])
  have z0ne: "lessBT (Trm []) (xseq c (enat u) 0)" using x0 by simp
  have ne: "lessBT (Trm []) (operB c (xseq c (enat u) 0))"
    using b1x_less_le_trans[OF z0ne le] .
  show ?case using x0 x1 ne by simp
next
  case (Suc n)
  have e1: "xseq c (enat u) (Suc n)
              = Trm [DB (enat u) (operB c (xseq c (enat u) n))]" by (rule b1x_xseq_Suc)
  have e2: "xseq c (enat u) (Suc (Suc n))
              = Trm [DB (enat u) (operB c (xseq c (enat u) (Suc n)))]"
    by (rule b1x_xseq_Suc)
  have z1: "xseq c (enat u) n \<in> TBv (enat u)" by (rule y4_xseq_TBv)
  have z2: "xseq c (enat u) (Suc n) \<in> TBv (enat u)" by (rule y4_xseq_TBv)
  have blt: "lessBT (operB c (xseq c (enat u) n)) (operB c (xseq c (enat u) (Suc n)))"
    by (rule b1x_mono[OF dc z1 z2 Suc.IH])
  show ?case using e1 e2 blt by simp
qed

lemma y4_xseq_mono:
  assumes ot: "isOT_BT c" and dc: "domB c = TBv (enat u)" and mn: "m < n"
  shows "lessBT (xseq c (enat u) m) (xseq c (enat u) n)"
  using mn
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m = n")
    case True
    thus ?thesis using y4_xseq_lt[OF ot dc, of n] by simp
  next
    case False
    hence mn': "m < n" using Suc.prems by simp
    have "lessBT (xseq c (enat u) m) (xseq c (enat u) n)" by (rule Suc.IH[OF mn'])
    thus ?thesis using y4_xseq_lt[OF ot dc, of n] by (rule lessBT_trans)
  qed
qed

lemma y4_xseq_le_mono:
  assumes ot: "isOT_BT c" and dc: "domB c = TBv (enat u)" and mn: "m \<le> n"
  shows "leBT (xseq c (enat u) m) (xseq c (enat u) n)"
  using mn y4_xseq_mono[OF ot dc, of m n] by (cases "m = n") auto


subsection \<open>(2) List/order helpers for the two reductions\<close>

text \<open>\<open>leBT\<close>-forms of the two proven \<open>addBT\<close> order facts.\<close>

lemma y4_leBT_addBT_self: "leBT t (t +\<^sub>B c)"
proof (cases "c = 0\<^sub>B")
  case True
  have "t +\<^sub>B 0\<^sub>B = t" by (cases t) simp
  thus ?thesis using True by simp
next
  case False
  thus ?thesis using lessBT_addBT_self[of c t] by simp
qed

lemma y4_leBT_addBT_mono_right:
  assumes "leBT a b" shows "leBT (t +\<^sub>B a) (t +\<^sub>B b)"
  using assms lessBT_addBT_mono_right[of a b t] by auto

text \<open>\<^bold>\<open>The prefix split.\<close>  A term below \<open>(a\<^sub>0,\<dots>,a\<^sub>k)\<close> is either \<open>\<le>\<close> the front
  \<open>(a\<^sub>0,\<dots>,a\<^bsub>k-1\<^esub>)\<close>, or it extends that front by a nonempty block whose head
  principal is \<open>< a\<^sub>k\<close>.  This is what turns the multi-principal case of the
  Bachmann property into the single-principal case.\<close>

lemma y4_prefix_split:
  "lessBT (Trm ys) (Trm (ps @ [q])) \<Longrightarrow>
     leBT (Trm ys) (Trm ps)
     \<or> (\<exists>rs. ys = ps @ rs \<and> rs \<noteq> [] \<and> lessBP (hd rs) q)"
proof (induction ps arbitrary: ys)
  case Nil
  show ?case
  proof (cases ys)
    case Nil thus ?thesis by simp
  next
    case (Cons r rs')
    have "lessBP r q" using Nil.prems Cons by simp
    thus ?thesis using Cons by auto
  qed
next
  case (Cons p ps')
  show ?case
  proof (cases ys)
    case Nil thus ?thesis by simp
  next
    case (Cons r rs')
    have step: "lessBP r p \<or> (r = p \<and> lessBT (Trm rs') (Trm (ps' @ [q])))"
      using Cons.prems Cons by simp
    show ?thesis
    proof (cases "lessBP r p")
      case True
      hence "lessBT (Trm (r # rs')) (Trm (p # ps'))" by simp
      thus ?thesis using Cons by simp
    next
      case False
      hence rp: "r = p" and rec: "lessBT (Trm rs') (Trm (ps' @ [q]))" using step by auto
      have ih: "leBT (Trm rs') (Trm ps')
                 \<or> (\<exists>ss. rs' = ps' @ ss \<and> ss \<noteq> [] \<and> lessBP (hd ss) q)"
        by (rule Cons.IH[OF rec])
      show ?thesis
      proof (cases "leBT (Trm rs') (Trm ps')")
        case True
        hence "leBT (Trm (p # rs')) (Trm (p # ps'))" by auto
        thus ?thesis using Cons rp by simp
      next
        case False
        then obtain ss where sseq: "rs' = ps' @ ss" and ssne: "ss \<noteq> []"
          and sslt: "lessBP (hd ss) q" using ih by blast
        have "ys = (p # ps') @ ss" using Cons rp sseq by simp
        thus ?thesis using ssne sslt by blast
      qed
    qed
  qed
qed

text \<open>A suffix of an \<open>OT\<close> principal list is again \<open>OT\<close>; and its \<open>G\<close>-set is contained
  in the whole term's \<open>G\<close>-set.\<close>

lemma y4_descP_suffix: "descP (ps @ rs) \<Longrightarrow> descP rs"
  by (induction ps) (auto elim: descP.elims split: list.splits)

lemma y4_OT_suffix:
  assumes "isOT_BT (Trm (ps @ rs))" shows "isOT_BT (Trm rs)"
  using assms y4_descP_suffix[of ps rs] by auto

lemma y4_GBT_suffix: "GBT u (Trm rs) \<subseteq> GBT u (Trm (ps @ rs))"
  by auto


subsection \<open>(3) THE COLLAPSING COFINALITY --- case ([].4)(ii)\<close>

text \<open>\<^bold>\<open>The inner induction.\<close>  Along the \<open>T\<^sub>u\<close>-domain "context" \<open>c'\<close> (a sub-context of
  the tower host \<open>c\<^sub>0\<close>), every \<open>OT\<close> term \<open>y < c'\<close> whose \<open>G\<^sub>u\<close>-escapes are ALREADY
  bounded by the tower \<open>(x\<^sub>n)\<close> of \<open>c\<^sub>0\<close> satisfies \<open>y \<le> c'[D\<^sub>u x\<^sub>n]\<close> for some \<open>n\<close>.

  This is the exact place where the \<open>OT\<close> \<open>G\<close>-condition is INDISPENSABLE: without it
  \<open>y = D\<^sub>0(D\<^sub>5 0) < D\<^sub>1 0\<close> would be a counterexample (it exceeds every \<open>D\<^sub>0\<^bsup>n\<^esup>0\<close>), and
  it is exactly \<open>G\<^sub>0 y < y\<close> that rules it out.\<close>

lemma y4_inner:
  assumes ot0: "isOT_BT c0" and dc0: "domB c0 = TBv (enat u)"
  shows "isOT_BT c' \<Longrightarrow> domB c' = TBv (enat u) \<Longrightarrow> isOT_BT y \<Longrightarrow> lessBT y c' \<Longrightarrow>
         (\<forall>x \<in> GBT (enat u) y. \<exists>n. leBT x (operB c0 (xseq c0 (enat u) n))) \<Longrightarrow>
         (\<exists>n. leBT y (operB c' (xseq c0 (enat u) n)))"
proof (induction c' arbitrary: y rule: measure_induct_rule[where f=size])
  case (less c' y)
  note GB = less.prems(5)
  obtain cs where ceq: "c' = Trm cs" by (cases c')
  show ?case
  proof (cases cs)
    case Nil
    have "domB c' = {}" using ceq Nil by (subst domB_unfold) simp
    thus ?thesis using less.prems(2) b1x_zero_TBv by auto
  next
    case ConsP: (Cons p ps)
    show ?thesis
    proof (cases ps)
      case Nil
      obtain w bb where peq: "p = DB w bb" by (cases p)
      have aeq: "c' = Trm [DB w bb]" using ceq ConsP Nil peq by simp
      show ?thesis
      proof (cases "bb = Trm []")
        case bb0: True
        \<comment> \<open>\<open>c' = D\<^bsub>u+1\<^esub>0\<close>: the tower base.  \<open>c'[z] = z\<close>.\<close>
        have unf: "domB c' = (if w = 0 then {Trm []} else if w = \<infinity> then NatSet
                    else TBv (enat (the_enat w - 1)))"
          using aeq bb0 by (subst domB_unfold) simp
        have w0: "w \<noteq> 0" using unf less.prems(2) zero_set_neq_TBv by (auto split: if_splits)
        have winf: "w \<noteq> \<infinity>" using unf less.prems(2) NatSet_neq_TBv w0 by (auto split: if_splits)
        have tw: "TBv (enat (the_enat w - 1)) = TBv (enat u)"
          using unf less.prems(2) w0 winf by simp
        have wu: "the_enat w - 1 = u" by (rule y3_TBv_inj[OF tw])
        obtain kw where wk: "w = enat kw" using winf by (cases w) auto
        have kwpos: "kw \<noteq> 0" using w0 wk by (simp add: zero_enat_def)
        have wval: "w = enat (Suc u)" using wk wu kwpos by simp
        have oper: "\<And>z. operB c' z = z" using aeq bb0 b1x_operB_Dsucc[OF w0 winf] by simp
        show ?thesis
        proof (cases y)
          case (Trm ys)
          show ?thesis
          proof (cases ys)
            case Nil
            have "leBT y (xseq c0 (enat u) 0)" using Trm Nil by simp
            thus ?thesis using oper by auto
          next
            case (Cons r rs)
            obtain w1 y1 where req: "r = DB w1 y1" by (cases r)
            have hlt: "lessBP (DB w1 y1) (DB (enat (Suc u)) (Trm []))"
              using less.prems(4) Trm Cons aeq wval bb0 req by simp
            have w1lt: "w1 < enat (Suc u)" using hlt by auto
            have w1le: "w1 \<le> enat u" using w1lt by (cases w1) (auto simp: Suc_ile_eq)
            show ?thesis
            proof (cases "w1 = enat u")
              case w1eq: True
              have y1G: "y1 \<in> GBT (enat u) y" using Trm Cons req w1eq by auto
              \<comment> \<open>r72: the escapes are bounded by the CORRECTED cofinal chain \<open>c\<^sub>0[x\<^sub>m]\<close>,
                 and \<open>x\<^bsub>m+2\<^esub> = D\<^sub>u (c\<^sub>0[x\<^bsub>m+1\<^esub>])\<close>, so one step of strict increase suffices\<close>
              obtain m where m: "leBT y1 (operB c0 (xseq c0 (enat u) m))"
                using GB y1G by blast
              have xlt: "lessBT (xseq c0 (enat u) m) (xseq c0 (enat u) (Suc m))"
                by (rule y4_xseq_lt[OF ot0 dc0])
              have z1: "xseq c0 (enat u) m \<in> TBv (enat u)" by (rule y4_xseq_TBv)
              have z2: "xseq c0 (enat u) (Suc m) \<in> TBv (enat u)" by (rule y4_xseq_TBv)
              have clt: "lessBT (operB c0 (xseq c0 (enat u) m))
                                (operB c0 (xseq c0 (enat u) (Suc m)))"
                by (rule b1x_mono[OF dc0 z1 z2 xlt])
              have lt: "lessBT y1 (operB c0 (xseq c0 (enat u) (Suc m)))"
                using m clt b1x_le_less_trans by blast
              have xs: "xseq c0 (enat u) (Suc (Suc m))
                          = Trm [DB (enat u) (operB c0 (xseq c0 (enat u) (Suc m)))]"
                by (rule b1x_xseq_Suc)
              have "lessBP (DB w1 y1)
                      (DB (enat u) (operB c0 (xseq c0 (enat u) (Suc m))))"
                using lt w1eq by simp
              hence "lessBT y (xseq c0 (enat u) (Suc (Suc m)))"
                using Trm Cons req xs by simp
              thus ?thesis using oper by auto
            next
              case False
              hence w1s: "w1 < enat u" using w1le by simp
              have x0: "xseq c0 (enat u) 0 = Trm [DB (enat u) (Trm [])]"
                by (rule b1x_xseq_0)
              have "lessBP (DB w1 y1) (DB (enat u) (Trm []))" using w1s by simp
              hence "lessBT y (xseq c0 (enat u) 0)"
                using Trm Cons req x0 by simp
              thus ?thesis using oper by auto
            qed
          qed
        qed
      next
        case bbne: False
        \<comment> \<open>\<open>c' = D\<^sub>w bb\<close> with \<open>dom(bb) = T\<^sub>u\<close>, \<open>u < w\<close>: case ([].4)(iii), peel one \<open>D\<close>.\<close>
        have dbc: "domB (Trm [DB w bb]) = TBv (enat u)" using less.prems(2) aeq by simp
        have struct: "domB bb = TBv (enat u)
                        \<and> \<not> (\<exists>u'. w \<le> enat u' \<and> domB bb = TBv (enat u'))"
          by (rule domB_single_TBv_struct[OF dbc bbne])
        have dbb: "domB bb = TBv (enat u)" using struct by blast
        have nk: "\<not> (\<exists>u'. w \<le> enat u' \<and> domB bb = TBv (enat u'))" using struct by blast
        have dbnz: "domB bb \<noteq> {Trm []}" using dbb zero_set_neq_TBv by auto
        have wgt: "enat u < w" using nk dbb by (auto simp: not_le)
        have oper: "\<And>z. operB c' z = Trm [DB w (operB bb z)]"
          using aeq b1x_operB_case_iii[OF bbne dbnz nk] by simp
        have otbb: "isOT_BT bb" using less.prems(1) aeq by simp
        have szbb: "size bb < size c'" using aeq by simp
        show ?thesis
        proof (cases y)
          case (Trm ys)
          show ?thesis
          proof (cases ys)
            case Nil
            have "leBT y (Trm [DB w (operB bb (xseq c0 (enat u) 0))])"
              using Trm Nil by simp
            thus ?thesis using oper by auto
          next
            case (Cons r rs)
            obtain w1 y1 where req: "r = DB w1 y1" by (cases r)
            have hlt: "lessBP (DB w1 y1) (DB w bb)"
              using less.prems(4) Trm Cons aeq req by simp
            show ?thesis
            proof (cases "w1 = w")
              case w1eq: True
              have y1lt: "lessBT y1 bb" using hlt w1eq by simp
              have oty1: "isOT_BT y1" using less.prems(3) Trm Cons req by simp
              have uw: "enat u \<le> w" using wgt by simp
              have y1G: "y1 \<in> GBT (enat u) y" using Trm Cons req w1eq uw by auto
              have sub: "GBT (enat u) y1 \<subseteq> GBT (enat u) y" by (rule b1x_GBT_trans[OF y1G])
              have GB1: "\<forall>x \<in> GBT (enat u) y1. \<exists>n. leBT x (operB c0 (xseq c0 (enat u) n))"
                using GB sub by blast
              obtain n where n: "leBT y1 (operB bb (xseq c0 (enat u) n))"
                using less.IH[OF szbb otbb dbb oty1 y1lt GB1] by blast
              have zlt: "lessBT (xseq c0 (enat u) n)
                                (xseq c0 (enat u) (Suc n))"
                using y4_xseq_lt[OF ot0 dc0, of n] by simp
              have z1: "xseq c0 (enat u) n \<in> TBv (enat u)" by (rule y4_xseq_TBv)
              have z2: "xseq c0 (enat u) (Suc n) \<in> TBv (enat u)" by (rule y4_xseq_TBv)
              have blt: "lessBT (operB bb (xseq c0 (enat u) n))
                                (operB bb (xseq c0 (enat u) (Suc n)))"
                by (rule b1x_mono[OF dbb z1 z2 zlt])
              have y1lt2: "lessBT y1 (operB bb (xseq c0 (enat u) (Suc n)))"
                using n blt b1x_le_less_trans by blast
              have "lessBP (DB w1 y1) (DB w (operB bb (xseq c0 (enat u) (Suc n))))"
                using y1lt2 w1eq by simp
              hence "lessBT y (Trm [DB w (operB bb (xseq c0 (enat u) (Suc n)))])"
                using Trm Cons req by simp
              thus ?thesis using oper by auto
            next
              case False
              hence w1s: "w1 < w" using hlt by auto
              have "lessBP (DB w1 y1) (DB w (operB bb (xseq c0 (enat u) 0)))"
                using w1s by simp
              hence "lessBT y (Trm [DB w (operB bb (xseq c0 (enat u) 0))])"
                using Trm Cons req by simp
              thus ?thesis using oper by auto
            qed
          qed
        qed
      qed
    next
      case ConsQ: (Cons q rest)
      \<comment> \<open>multi-principal \<open>c'\<close>: ([].5) reduces to the LAST principal.\<close>
      have cseq: "cs = p # q # rest" using ConsP ConsQ by simp
      have ne: "cs \<noteq> []" using cseq by simp
      have split: "cs = butlast cs @ [last cs]" using ne by simp
      have dlast: "domB (Trm [last cs]) = TBv (enat u)"
        using less.prems(2) ceq domB_last_component[OF ne] by simp
      have otlast: "isOT_BT (Trm [last cs])"
        using less.prems(1) ceq ne by (simp add: last_in_set)
      have szlast: "size (Trm [last cs] :: BT) < size c'"
        using ceq cseq b1x_size_last_lt[of p q rest] by simp
      have operc: "\<And>z. operB c' z = Trm (butlast cs) +\<^sub>B operB (Trm [last cs]) z"
        using ceq cseq b1x_operB_multi[of p q rest] by simp
      obtain ys where yeq: "y = Trm ys" by (cases y)
      have ylt: "lessBT (Trm ys) (Trm (butlast cs @ [last cs]))"
        using less.prems(4) yeq ceq split by simp
      have PS: "leBT (Trm ys) (Trm (butlast cs))
                 \<or> (\<exists>rs. ys = butlast cs @ rs \<and> rs \<noteq> [] \<and> lessBP (hd rs) (last cs))"
        by (rule y4_prefix_split[OF ylt])
      show ?thesis
      proof (cases "leBT (Trm ys) (Trm (butlast cs))")
        case True
        have "leBT (Trm (butlast cs))
                   (Trm (butlast cs) +\<^sub>B operB (Trm [last cs])
                          (xseq c0 (enat u) 0))"
          by (rule y4_leBT_addBT_self)
        hence "leBT y (operB c' (xseq c0 (enat u) 0))"
          using True yeq operc leBT_trans by metis
        thus ?thesis by blast
      next
        case False
        then obtain rs where rseq: "ys = butlast cs @ rs" and rsne: "rs \<noteq> []"
          and rslt: "lessBP (hd rs) (last cs)" using PS by blast
        have rscons: "rs = hd rs # tl rs" using rsne by simp
        have y'lt: "lessBT (Trm rs) (Trm [last cs])"
          using rslt by (subst rscons) simp
        have oty': "isOT_BT (Trm rs)"
          using less.prems(3) yeq rseq y4_OT_suffix[of "butlast cs" rs] by simp
        have Gsub: "GBT (enat u) (Trm rs) \<subseteq> GBT (enat u) y"
          using yeq rseq y4_GBT_suffix[of "enat u" rs "butlast cs"] by simp
        have GB': "\<forall>x \<in> GBT (enat u) (Trm rs). \<exists>n. leBT x (operB c0 (xseq c0 (enat u) n))"
          using GB Gsub by blast
        obtain n where n: "leBT (Trm rs)
              (operB (Trm [last cs]) (xseq c0 (enat u) n))"
          using less.IH[OF szlast otlast dlast oty' y'lt GB'] by blast
        have "leBT (Trm (butlast cs) +\<^sub>B Trm rs)
                   (Trm (butlast cs) +\<^sub>B
                     operB (Trm [last cs]) (xseq c0 (enat u) n))"
          by (rule y4_leBT_addBT_mono_right[OF n])
        moreover have "Trm (butlast cs) +\<^sub>B Trm rs = y" using yeq rseq by simp
        ultimately have "leBT y (operB c' (xseq c0 (enat u) n))"
          using operc by simp
        thus ?thesis by blast
      qed
    qed
  qed
qed

text \<open>\<^bold>\<open>The outer induction\<close> = the ([].4)(ii) residual, DISCHARGED.  For an \<open>OT\<close> host
  \<open>c\<close> with \<open>dom(c) = T\<^sub>u\<close>, every \<open>OT\<close> term \<open>e < c\<close> whose \<open>G\<^sub>u\<close>-escapes stay below \<open>c\<close>
  is caught by the tower.  The \<open>G\<close>-hypothesis is exactly what an \<open>OT\<close> principal
  \<open>D\<^sub>v e\<close> supplies (\<open>G\<^sub>v e < e < c\<close> and \<open>G\<^sub>u \<subseteq> G\<^sub>v\<close> for \<open>v \<le> u\<close>).\<close>

lemma y4_xseq_cof:
  assumes ot: "isOT_BT c" and dc: "domB c = TBv (enat u)"
  shows "isOT_BT e \<Longrightarrow> lessBT e c \<Longrightarrow> (\<forall>x \<in> GBT (enat u) e. lessBT x c) \<Longrightarrow>
         (\<exists>n. leBT e (operB c (xseq c (enat u) n)))"
proof (induction e rule: measure_induct_rule[where f=size])
  case (less e)
  have GB: "\<forall>x \<in> GBT (enat u) e. \<exists>n. leBT x (operB c (xseq c (enat u) n))"
  proof
    fix x assume xin: "x \<in> GBT (enat u) e"
    have szx: "size x < size e" by (rule b1x_GBT_size[OF xin])
    have otx: "isOT_BT x" using wfj_G_OT_T xin less.prems(1) by blast
    have xlt: "lessBT x c" using less.prems(3) xin by blast
    have xG: "\<forall>z \<in> GBT (enat u) x. lessBT z c"
      using b1x_GBT_trans[OF xin] less.prems(3) by blast
    show "\<exists>n. leBT x (operB c (xseq c (enat u) n))"
      by (rule less.IH[OF szx otx xlt xG])
  qed
  show ?case
    using y4_inner[OF ot dc ot dc less.prems(1) less.prems(2) GB] by blast
qed


subsection \<open>(4) Strict increase of the \<open>\<nat>\<close>-indexed fundamental sequence\<close>

text \<open>[Buc1-Hydra] 3.3 for \<open><\<close> (his 3.3 states it for \<open>\<ll>\<^sub>k\<close>): on an \<open>\<nat>\<close> domain the
  fundamental sequence STRICTLY INCREASES.  Case ([].4)(ii) is exactly
  @{thm [source] y4_xseq_lt}; case ([].4)(i) is the numeral-block prefix growth.
  \<open>D\<^sub>\<omega>\<close>-freeness kills the \<open>D\<^sub>\<omega>0\<close> arm.\<close>

lemma y4_N_mono:
  "isOT_BT a \<Longrightarrow> dfree_BT a \<Longrightarrow> domB a = NatSet \<Longrightarrow>
   lessBT (operB a (numBT n)) (operB a (numBT (Suc n)))"
proof (induction a arbitrary: n rule: measure_induct_rule[where f=size])
  case (less a n)
  obtain xs where axs: "a = Trm xs" by (cases a)
  show ?case
  proof (cases xs)
    case Nil
    have "domB a = {}" using axs Nil by (subst domB_unfold) simp
    moreover have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
    ultimately show ?thesis using less.prems(3) by auto
  next
    case ConsP: (Cons p ps)
    show ?thesis
    proof (cases ps)
      case Nil
      obtain v bb where peq: "p = DB v bb" by (cases p)
      have aeq: "a = Trm [DB v bb]" using axs ConsP Nil peq by simp
      show ?thesis
      proof (cases "bb = Trm []")
        case bb0: True
        have unf: "domB a = (if v = 0 then {Trm []} else if v = \<infinity> then NatSet
                    else TBv (enat (the_enat v - 1)))"
          using aeq bb0 by (subst domB_unfold) simp
        have vinf: "v = \<infinity>"
          using unf less.prems(3) NatSet_neq_zero NatSet_neq_TBv
          by (auto split: if_splits)
        have "v \<noteq> \<infinity>" using less.prems(2) aeq by simp
        thus ?thesis using vinf by simp
      next
        case bbne: False
        have otbb: "isOT_BT bb" using less.prems(1) aeq by simp
        have dfbb: "dfree_BT bb" using less.prems(2) aeq by simp
        have szbb: "size bb < size a" using aeq by simp
        show ?thesis
        proof (cases "domB bb = {Trm []}")
          case dz: True
          \<comment> \<open>([].4)(i): \<open>a[n] = (D\<^sub>v bb[0])\<cdot>(n+1)\<close> --- prefix growth.\<close>
          have op: "\<And>z. operB a z
              = multBT (Trm [DB v (operB bb (Trm []))]) (numNat z + 1)"
            using aeq b1x_operB_case_i[OF bbne dz] by simp
          have opn: "operB a (numBT n)
              = Trm (replicate (Suc n) (DB v (operB bb (Trm []))))"
            using op[of "numBT n"] bwl_numNat_numBT[of n] b1x_mult_single
            by (simp add: replicate_append_same)
          have opsn: "operB a (numBT (Suc n))
              = Trm (replicate (Suc (Suc n)) (DB v (operB bb (Trm []))))"
            using op[of "numBT (Suc n)"] bwl_numNat_numBT[of "Suc n"] b1x_mult_single
            by (simp add: replicate_append_same)
          have "lessBT (Trm (replicate (Suc n) (DB v (operB bb (Trm [])))))
                       (Trm (replicate (Suc n) (DB v (operB bb (Trm []))))
                          +\<^sub>B Trm [DB v (operB bb (Trm []))])"
            by (rule lessBT_addBT_self) simp
          moreover have "Trm (replicate (Suc n) (DB v (operB bb (Trm []))))
                          +\<^sub>B Trm [DB v (operB bb (Trm []))]
                        = Trm (replicate (Suc (Suc n)) (DB v (operB bb (Trm []))))"
            by (simp add: replicate_append_same)
          ultimately show ?thesis using opn opsn by simp
        next
          case dnz: False
          show ?thesis
          proof (cases "\<exists>u. v \<le> enat u \<and> domB bb = TBv (enat u)")
            case kii: True
            \<comment> \<open>([].4)(ii), CORRECTED: \<open>a[n] = D\<^sub>v (bb[x\<^sub>n])\<close> --- the tower increases
               (@{thm [source] y4_xseq_lt}) and \<open>bb[\<cdot>]\<close> is monotone on \<open>T\<^sub>u\<close>.\<close>
            obtain u where uu: "v \<le> enat u" and du: "domB bb = TBv (enat u)" using kii by blast
            have op: "\<And>z. operB a z
                = Trm [DB v (operB bb
                    (xseq bb (enat (tbvIdx (domB bb))) (numNat z)))]"
              using aeq bwl_operB_case_ii[OF bbne dnz kii] by simp
            have tid: "tbvIdx (domB bb) = u" using du bwl_tbvIdx by simp
            have opn: "operB a (numBT n) = Trm [DB v (operB bb (xseq bb (enat u) n))]"
              using op[of "numBT n"] bwl_numNat_numBT[of n] tid by simp
            have opsn: "operB a (numBT (Suc n))
                = Trm [DB v (operB bb (xseq bb (enat u) (Suc n)))]"
              using op[of "numBT (Suc n)"] bwl_numNat_numBT[of "Suc n"] tid by simp
            have xlt: "lessBT (xseq bb (enat u) n) (xseq bb (enat u) (Suc n))"
              by (rule y4_xseq_lt[OF otbb du])
            have z1: "xseq bb (enat u) n \<in> TBv (enat u)" by (rule y4_xseq_TBv)
            have z2: "xseq bb (enat u) (Suc n) \<in> TBv (enat u)" by (rule y4_xseq_TBv)
            have "lessBT (operB bb (xseq bb (enat u) n))
                         (operB bb (xseq bb (enat u) (Suc n)))"
              by (rule b1x_mono[OF du z1 z2 xlt])
            thus ?thesis using opn opsn by simp
          next
            case kiii: False
            \<comment> \<open>([].4)(iii): \<open>a[z] = D\<^sub>v bb[z]\<close> --- IH on \<open>bb\<close>.\<close>
            have op: "\<And>z. operB a z = Trm [DB v (operB bb z)]"
              using aeq b1x_operB_case_iii[OF bbne dnz kiii] by simp
            have dbn: "domB bb = NatSet"
              using less.prems(3) aeq b1x_domB_case_iii[OF bbne dnz kiii] by simp
            have "lessBT (operB bb (numBT n)) (operB bb (numBT (Suc n)))"
              by (rule less.IH[OF szbb otbb dfbb dbn])
            thus ?thesis using op by simp
          qed
        qed
      qed
    next
      case ConsQ: (Cons q rest)
      have cseq: "xs = p # q # rest" using ConsP ConsQ by simp
      have ne: "xs \<noteq> []" using cseq by simp
      have dlast: "domB (Trm [last xs]) = NatSet"
        using less.prems(3) axs domB_last_component[OF ne] by simp
      have otlast: "isOT_BT (Trm [last xs])"
        using less.prems(1) axs ne by (simp add: last_in_set)
      have dflast: "dfree_BT (Trm [last xs])"
        using less.prems(2) axs ne by (simp add: last_in_set)
      have szlast: "size (Trm [last xs] :: BT) < size a"
        using axs cseq b1x_size_last_lt[of p q rest] by simp
      have op: "\<And>z. operB a z = Trm (butlast xs) +\<^sub>B operB (Trm [last xs]) z"
        using axs cseq b1x_operB_multi[of p q rest] by simp
      have "lessBT (operB (Trm [last xs]) (numBT n)) (operB (Trm [last xs]) (numBT (Suc n)))"
        by (rule less.IH[OF szlast otlast dflast dlast])
      hence "lessBT (Trm (butlast xs) +\<^sub>B operB (Trm [last xs]) (numBT n))
                    (Trm (butlast xs) +\<^sub>B operB (Trm [last xs]) (numBT (Suc n)))"
        by (rule lessBT_addBT_mono_right)
      thus ?thesis using op by simp
    qed
  qed
qed

lemma y4_N_mono_le:
  assumes "isOT_BT a" "dfree_BT a" "domB a = NatSet" "m \<le> n"
  shows "leBT (operB a (numBT m)) (operB a (numBT n))"
  using assms(4)
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m = Suc n")
    case True thus ?thesis by simp
  next
    case False
    hence "m \<le> n" using Suc.prems by simp
    hence "leBT (operB a (numBT m)) (operB a (numBT n))" by (rule Suc.IH)
    moreover have "lessBT (operB a (numBT n)) (operB a (numBT (Suc n)))"
      by (rule y4_N_mono[OF assms(1-3)])
    ultimately show ?thesis using b1x_le_less_trans by blast
  qed
qed


subsection \<open>(5) Helpers for the Bachmann induction\<close>

text \<open>In a \<open>descP\<close> list every principal is \<open>\<le>\<close> the head.\<close>

lemma y4_descP_all_le_hd:
  "descP ps \<Longrightarrow> p \<in> set ps \<Longrightarrow> leBT (Trm [p]) (Trm [hd ps])"
proof (induction ps rule: descP.induct)
  case 1 thus ?case by simp
next
  case (2 q) thus ?case by simp
next
  case (3 p1 q1 ps1)
  have le1: "leBT (Trm [q1]) (Trm [p1])" and d1: "descP (q1 # ps1)"
    using "3.prems"(1) by simp_all
  show ?case
  proof (cases "p = p1")
    case True thus ?thesis by simp
  next
    case False
    hence pin: "p \<in> set (q1 # ps1)" using "3.prems"(2) by simp
    have h: "leBT (Trm [p]) (Trm [q1])" using "3.IH"[OF d1 pin] by simp
    have "leBT (Trm [p]) (Trm [p1])" by (rule leBT_trans[OF h le1])
    thus ?thesis by simp
  qed
qed

text \<open>An \<open>OT\<close> term whose HEAD index is \<open>\<le> m\<close> lies in \<open>T\<^sub>m\<close> (all its indices are then \<open>\<le> m\<close>).\<close>

lemma y4_TBv_of_head:
  assumes ot: "isOT_BT (Trm (DB w e # rs))" and wm: "w \<le> enat m"
  shows "Trm (DB w e # rs) \<in> TBv (enat m)"
proof -
  have dsc: "descP (DB w e # rs)" using ot by simp
  have "\<And>p. p \<in> set (DB w e # rs) \<Longrightarrow> (case p of DB u _ \<Rightarrow> u \<le> enat m)"
  proof -
    fix p assume pin: "p \<in> set (DB w e # rs)"
    obtain u t where peq: "p = DB u t" by (cases p)
    have "leBT (Trm [p]) (Trm [DB w e])" using y4_descP_all_le_hd[OF dsc pin] by simp
    hence "u \<le> w" using peq b1x_leBT_single_idx by simp
    thus "(case p of DB u _ \<Rightarrow> u \<le> enat m)" using peq wm by simp
  qed
  thus ?thesis by (simp add: TBv_def)
qed

text \<open>\<open>1 = D\<^sub>0 0\<close> is the MINIMAL principal.\<close>

lemma y4_leBT_min: "leBT (Trm [DB 0 (Trm [])]) (Trm [p])"
proof (cases p)
  case (DB w e)
  show ?thesis
  proof (cases w)
    case (enat k)
    show ?thesis
    proof (cases k)
      case 0
      hence w0: "w = 0" using enat by (simp add: zero_enat_def)
      show ?thesis using DB w0 by (cases "e = Trm []") auto
    next
      case (Suc k')
      have "(0::enat) < w" using enat Suc by (simp add: zero_enat_def)
      thus ?thesis using DB by simp
    qed
  next
    case infinity
    have "(0::enat) < w" using infinity by (simp add: zero_enat_def)
    thus ?thesis using DB by simp
  qed
qed

text \<open>Bumping a \<open>T\<^sub>m\<close>-witness: \<open>z + 1\<close> is again an \<open>OT\<close>, \<open>D\<^sub>\<omega>\<close>-free element of \<open>T\<^sub>m\<close>, and
  \<open>z < z + 1\<close>.  This is what absorbs the equality case of the Bachmann induction.\<close>

lemma y4_bump:
  assumes ot: "isOT_BT z" and df: "dfree_BT z" and tv: "z \<in> TBv (enat m)"
  shows "isOT_BT (z +\<^sub>B Trm [DB 0 (Trm [])]) \<and> dfree_BT (z +\<^sub>B Trm [DB 0 (Trm [])])
         \<and> (z +\<^sub>B Trm [DB 0 (Trm [])]) \<in> TBv (enat m)
         \<and> lessBT z (z +\<^sub>B Trm [DB 0 (Trm [])])"
proof -
  obtain zs where zeq: "z = Trm zs" by (cases z)
  have dsc: "descP zs" using ot zeq by simp
  have bnd: "zs = [] \<or> [DB 0 (Trm [])] = []
               \<or> leBT (Trm [hd [DB 0 (Trm [])]]) (Trm [last zs])"
    using y4_leBT_min by simp
  have dsc': "descP (zs @ [DB 0 (Trm [])])"
    by (rule b1x_descP_append[OF dsc _ bnd]) simp
  have prs: "\<forall>p \<in> set (zs @ [DB 0 (Trm [])]). isOT_BP p" using ot zeq by simp
  have ot': "isOT_BT (Trm (zs @ [DB 0 (Trm [])]))" using prs dsc' by simp
  have df': "dfree_BT (Trm (zs @ [DB 0 (Trm [])]))" using df zeq by simp
  have tv': "Trm (zs @ [DB 0 (Trm [])]) \<in> TBv (enat m)"
    using tv zeq by (auto simp: TBv_def zero_enat_def)
  have lt: "lessBT (Trm zs) (Trm zs +\<^sub>B Trm [DB 0 (Trm [])])"
    by (rule lessBT_addBT_self) simp
  show ?thesis using zeq ot' df' tv' lt by simp
qed

text \<open>On a \<open>{0}\<close> domain the bracket IGNORES its argument (the last principal is \<open>D\<^sub>0 0\<close>,
  which is simply deleted).\<close>

lemma y4_operB_domzero_const:
  "domB c = {Trm []} \<Longrightarrow> operB c z = operB c (Trm [])"
proof (induction c arbitrary: z rule: measure_induct_rule[where f=size])
  case (less c z)
  obtain cs where ceq: "c = Trm cs" by (cases c)
  show ?case
  proof (cases cs)
    case Nil
    have "domB c = {}" using ceq Nil by (subst domB_unfold) simp
    thus ?thesis using less.prems by auto
  next
    case ConsP: (Cons p ps)
    show ?thesis
    proof (cases ps)
      case Nil
      obtain v bb where peq: "p = DB v bb" by (cases p)
      have aeq: "c = Trm [DB v bb]" using ceq ConsP Nil peq by simp
      show ?thesis
      proof (cases "bb = Trm []")
        case True
        have unf: "domB c = (if v = 0 then {Trm []} else if v = \<infinity> then NatSet
                      else TBv (enat (the_enat v - 1)))"
          using aeq True by (subst domB_unfold) simp
        have v0: "v = 0"
          using unf less.prems NatSet_neq_zero bwl_TBv_neq_zero by (auto split: if_splits)
        show ?thesis using aeq True v0 by (simp add: b1x_operB_D0)
      next
        case bbne: False
        show ?thesis
        proof (cases "domB bb = {Trm []}")
          case True
          have "domB c = NatSet" using aeq bwl_domB_case_i[OF bbne True] by simp
          thus ?thesis using less.prems NatSet_neq_zero by simp
        next
          case F1: False
          show ?thesis
          proof (cases "\<exists>u. v \<le> enat u \<and> domB bb = TBv (enat u)")
            case True
            have "domB c = NatSet" using aeq bwl_domB_case_ii[OF bbne F1 True] by simp
            thus ?thesis using less.prems NatSet_neq_zero by simp
          next
            case F2: False
            have "domB c = domB bb" using aeq b1x_domB_case_iii[OF bbne F1 F2] by simp
            thus ?thesis using less.prems F1 by simp
          qed
        qed
      qed
    next
      case ConsQ: (Cons q rest)
      have cseq: "cs = p # q # rest" using ConsP ConsQ by simp
      have ne: "cs \<noteq> []" using cseq by simp
      have dlast: "domB (Trm [last cs]) = {Trm []}"
        using less.prems ceq domB_last_component[OF ne] by simp
      have szlast: "size (Trm [last cs] :: BT) < size c"
        using ceq cseq b1x_size_last_lt[of p q rest] by simp
      have op: "\<And>w. operB c w = Trm (butlast cs) +\<^sub>B operB (Trm [last cs]) w"
        using ceq cseq b1x_operB_multi[of p q rest] by simp
      have "operB (Trm [last cs]) z = operB (Trm [last cs]) (Trm [])"
        by (rule less.IH[OF szlast dlast])
      thus ?thesis using op by simp
    qed
  qed
qed

text \<open>A \<open>descP\<close> block is \<open>\<le>\<close> the constant block of its head, of the same length --- the
  ([].4)(i) equality absorber.\<close>

lemma y4_le_replicate:
  "(\<forall>p \<in> set rs. leBT (Trm [p]) (Trm [q])) \<Longrightarrow>
    leBT (Trm rs) (Trm (replicate (length rs) q))"
proof (induction rs)
  case Nil thus ?case by simp
next
  case (Cons r rs')
  have hd: "leBT (Trm [r]) (Trm [q])" using Cons.prems by simp
  have ih: "leBT (Trm rs') (Trm (replicate (length rs') q))"
    using Cons.prems by (intro Cons.IH) simp
  show ?case
  proof (cases "r = q")
    case True
    show ?thesis using ih True by simp
  next
    case False
    hence "lessBP r q" using hd by simp
    thus ?thesis by simp
  qed
qed

lemma y4_dfree_suffix: "dfree_BT (Trm (ps @ rs)) \<Longrightarrow> dfree_BT (Trm rs)"
  by simp


subsection \<open>(6) \<^bold>\<open>THE BACHMANN (COFINALITY) PROPERTY\<close>\<close>

text \<open>\<^bold>\<open>\<open>b < a\<close> \<Longrightarrow> \<open>b \<le> a[z]\<close> for some \<open>z \<in> dom(a)\<close>\<close>, for \<open>OT\<close>, \<open>D\<^sub>\<omega>\<close>-free \<open>a\<close>, \<open>b\<close>.
  Strong induction on \<open>size a\<close>, mirroring the \<open>operB\<close> recursion:

  \<^item> multi-principal: @{thm [source] y4_prefix_split} reduces to the LAST principal;
  \<^item> \<open>a = 1\<close>: \<open>b < 1\<close> forces \<open>b = 0 = a[0]\<close>;
  \<^item> \<open>a = D\<^bsub>m+1\<^esub>0\<close> (\<open>dom = T\<^sub>m\<close>, \<open>a[z] = z\<close>): the witness is \<open>z := b\<close> itself
    (@{thm [source] y4_TBv_of_head} puts \<open>b\<close> in \<open>T\<^sub>m\<close>);
  \<^item> ([].4)(i): the equality case is absorbed by the numeral block (@{thm [source] y4_le_replicate});
  \<^item> ([].4)(ii): @{thm [source] y4_xseq_cof} --- the collapsing cofinality;
  \<^item> ([].4)(iii): IH on the body, with the equality case absorbed by BUMPING the
    fundamental-sequence index (@{thm [source] y4_N_mono} on \<open>\<nat>\<close>, @{thm [source] y4_bump}
    + @{thm [source] b1x_mono} on \<open>T\<^sub>m\<close>).\<close>

lemma y4_bachmann:
  "isOT_BT a \<Longrightarrow> dfree_BT a \<Longrightarrow> isOT_BT b \<Longrightarrow> dfree_BT b \<Longrightarrow> lessBT b a \<Longrightarrow>
     (((domB a = {Trm []} \<or> domB a = NatSet) \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n))))
      \<and> (\<forall>m. domB a = TBv (enat m)
           \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z))))"
proof (induction a arbitrary: b rule: measure_induct_rule[where f=size])
  case (less a b)
  obtain xs where axs: "a = Trm xs" by (cases a)
  obtain bs where bbs: "b = Trm bs" by (cases b)
  show ?case
  proof (cases xs)
    case Nil
    thus ?thesis using less.prems(5) axs by simp
  next
    case ConsP: (Cons p ps)
    show ?thesis
    proof (cases ps)
      case Nil
      obtain v c where peq: "p = DB v c" by (cases p)
      have aeq: "a = Trm [DB v c]" using axs ConsP Nil peq by simp
      have vinf: "v \<noteq> \<infinity>" using less.prems(2) aeq by simp
      have otc: "isOT_BT c" using less.prems(1) aeq by simp
      have dfc: "dfree_BT c" using less.prems(2) aeq by simp
      have szc: "size c < size a" using aeq by simp
      show ?thesis
      proof (cases "c = Trm []")
        case c0: True
        show ?thesis
        proof (cases "v = 0")
          case v0: True
          have da: "domB a = {Trm []}" using aeq c0 v0 by (subst domB_unfold) simp
          have op: "\<And>z. operB a z = Trm []" using aeq c0 v0 by (simp add: b1x_operB_D0)
          have b0: "b = Trm []"
          proof (cases bs)
            case Nil thus ?thesis using bbs by simp
          next
            case (Cons r rs)
            obtain w e where req: "r = DB w e" by (cases r)
            have hh: "lessBP (DB w e) (DB 0 (Trm []))
                       \<or> (DB w e = DB 0 (Trm []) \<and> lessBT (Trm rs) (Trm []))"
              using less.prems(5) bbs Cons req aeq c0 v0 by simp
            have "\<not> lessBP (DB w e) (DB 0 (Trm []))"
              by (cases w) (auto simp: zero_enat_def)
            hence False using hh by simp
            thus ?thesis by simp
          qed
          have c1: "(domB a = {Trm []} \<or> domB a = NatSet)
                      \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n)))" using b0 op by auto
          have c2: "\<forall>m. domB a = TBv (enat m)
                      \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z))"
            using da bwl_TBv_neq_zero by auto
          show ?thesis using c1 c2 by blast
        next
          case vne0: False
          have da: "domB a = TBv (enat (the_enat v - 1))"
            using aeq c0 b1x_domB_Dsucc[OF vne0 vinf] by simp
          have op: "\<And>z. operB a z = z" using aeq c0 b1x_operB_Dsucc[OF vne0 vinf] by simp
          obtain kv where kv: "v = enat kv" using vinf by (cases v) auto
          have kvne: "kv \<noteq> 0" using vne0 kv by (simp add: zero_enat_def)
          have c1: "(domB a = {Trm []} \<or> domB a = NatSet)
                      \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n)))"
          proof (intro impI)
            assume DA: "domB a = {Trm []} \<or> domB a = NatSet"
            have "TBv (enat (the_enat v - 1)) = {Trm []}
                    \<or> TBv (enat (the_enat v - 1)) = NatSet" using DA da by simp
            hence False using bwl_TBv_neq_zero NatSet_neq_TBv by metis
            thus "\<exists>n. leBT b (operB a (numBT n))" by simp
          qed
          have c2: "\<forall>m. domB a = TBv (enat m)
                      \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z))"
          proof (intro allI impI)
            fix m assume dm: "domB a = TBv (enat m)"
            have mm: "the_enat v - 1 = m" using y3_TBv_inj da dm by simp
            have vval: "v = enat (Suc m)" using kv kvne mm by simp
            have btv: "b \<in> TBv (enat m)"
            proof (cases bs)
              case Nil thus ?thesis using bbs b1x_zero_TBv by simp
            next
              case (Cons r rs)
              obtain w e where req: "r = DB w e" by (cases r)
              have hh: "lessBP (DB w e) (DB (enat (Suc m)) (Trm []))"
                using less.prems(5) bbs Cons req aeq c0 vval by simp
              have wlt: "w < enat (Suc m)" using hh by auto
              have wle: "w \<le> enat m" using wlt by (cases w) (auto simp: Suc_ile_eq)
              have otb': "isOT_BT (Trm (DB w e # rs))" using less.prems(3) bbs Cons req by simp
              show ?thesis using y4_TBv_of_head[OF otb' wle] bbs Cons req by simp
            qed
            have "b \<in> domB a \<and> isOT_BT b \<and> dfree_BT b \<and> leBT b (operB a b)"
              using btv dm less.prems(3) less.prems(4) op by simp
            thus "\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z)" by blast
          qed
          show ?thesis using c1 c2 by blast
        qed
      next
        case cne: False
        \<comment> \<open>head-split of \<open>b\<close> against the single principal \<open>D\<^sub>v c\<close>\<close>
        have HS: "bs = [] \<or> (\<exists>w e rs. bs = DB w e # rs
                      \<and> (w < v \<or> (w = v \<and> lessBT e c)))"
        proof (cases bs)
          case Nil thus ?thesis by simp
        next
          case (Cons r rs)
          obtain w e where req: "r = DB w e" by (cases r)
          have "lessBP (DB w e) (DB v c)"
            using less.prems(5) bbs Cons req aeq by simp
          hence "w < v \<or> (w = v \<and> lessBT e c)" by auto
          thus ?thesis using Cons req by blast
        qed
        show ?thesis
        proof (cases "domB c = {Trm []}")
          case dz: True
          \<comment> \<open>([].4)(i)\<close>
          have da: "domB a = NatSet" using aeq bwl_domB_case_i[OF cne dz] by simp
          define q0 where "q0 = DB v (operB c (Trm []))"
          have opn: "\<And>n. operB a (numBT n) = Trm (replicate (Suc n) q0)"
            using aeq b1x_operB_case_i[OF cne dz] bwl_numNat_numBT b1x_mult_single q0_def
            by (simp add: replicate_append_same)
          have c1: "\<exists>n. leBT b (operB a (numBT n))"
          proof (cases bs)
            case Nil
            have "leBT b (Trm (replicate (Suc 0) q0))" using bbs Nil by simp
            thus ?thesis using opn by metis
          next
            case (Cons r rs)
            obtain w e rs' where beq: "bs = DB w e # rs'"
              and disj: "w < v \<or> (w = v \<and> lessBT e c)" using HS Cons by blast
            show ?thesis
            proof (cases "w < v")
              case True
              have "lessBP (DB w e) q0" using True q0_def by simp
              hence "leBT b (Trm (replicate (Suc 0) q0))" using bbs beq by simp
              thus ?thesis using opn by metis
            next
              case False
              have wv: "w = v" and elt: "lessBT e c" using disj False by auto
              have ote: "isOT_BT e" using less.prems(3) bbs beq wv by simp
              have dfe: "dfree_BT e" using less.prems(4) bbs beq by simp
              have IH: "\<exists>n. leBT e (operB c (numBT n))"
                using less.IH[OF szc otc dfc ote dfe elt] dz by blast
              then obtain n' where n': "leBT e (operB c (numBT n'))" by blast
              have ee: "leBT e (operB c (Trm []))"
                using n' y4_operB_domzero_const[OF dz, of "numBT n'"] by simp
              show ?thesis
              proof (cases "e = operB c (Trm [])")
                case eq: True
                have rq: "DB w e = q0" using wv eq q0_def by simp
                have dsc: "descP (q0 # rs')" using less.prems(3) bbs beq rq by simp
                have allle: "\<forall>x \<in> set rs'. leBT (Trm [x]) (Trm [q0])"
                  using y4_descP_all_le_hd[OF dsc] by auto
                have "leBT (Trm rs') (Trm (replicate (length rs') q0))"
                  by (rule y4_le_replicate[OF allle])
                hence "leBT (Trm (q0 # rs')) (Trm (q0 # replicate (length rs') q0))"
                  by (simp add: lessBP_irrefl)
                hence "leBT b (Trm (replicate (Suc (length rs')) q0))"
                  using bbs beq rq by simp
                thus ?thesis using opn by metis
              next
                case False
                hence "lessBT e (operB c (Trm []))" using ee by blast
                hence "lessBP (DB w e) q0" using wv q0_def by simp
                hence "leBT b (Trm (replicate (Suc 0) q0))" using bbs beq by simp
                thus ?thesis using opn by metis
              qed
            qed
          qed
          have c2: "\<forall>m. domB a = TBv (enat m)
                      \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z))"
            using da NatSet_neq_TBv by auto
          show ?thesis using c1 c2 by blast
        next
          case dnz: False
          show ?thesis
          proof (cases "\<exists>u. v \<le> enat u \<and> domB c = TBv (enat u)")
            case kii: True
            \<comment> \<open>([].4)(ii) --- the tower; @{thm [source] y4_xseq_cof}\<close>
            obtain u' where vu: "v \<le> enat u'" and du: "domB c = TBv (enat u')" using kii by blast
            have da: "domB a = NatSet" using aeq bwl_domB_case_ii[OF cne dnz kii] by simp
            have tid: "tbvIdx (domB c) = u'" using du bwl_tbvIdx by simp
            have opn: "\<And>n. operB a (numBT n)
                = Trm [DB v (operB c (xseq c (enat u') n))]"
              using aeq bwl_operB_case_ii[OF cne dnz kii] bwl_numNat_numBT tid by simp
            have c1: "\<exists>n. leBT b (operB a (numBT n))"
            proof (cases bs)
              case Nil
              have "leBT b (Trm [DB v (operB c (xseq c (enat u') 0))])"
                using bbs Nil by simp
              thus ?thesis using opn by metis
            next
              case (Cons r rs)
              obtain w e rs' where beq: "bs = DB w e # rs'"
                and disj: "w < v \<or> (w = v \<and> lessBT e c)" using HS Cons by blast
              show ?thesis
              proof (cases "w < v")
                case True
                have "leBT b (Trm [DB v (operB c (xseq c (enat u') 0))])"
                  using True bbs beq by simp
                thus ?thesis using opn by metis
              next
                case False
                have wv: "w = v" and elt: "lessBT e c" using disj False by auto
                have ote: "isOT_BT e" using less.prems(3) bbs beq wv by simp
                have Gv: "\<forall>x \<in> GBT v e. lessBT x e"
                  using less.prems(3) bbs beq wv by simp
                have Gsub: "GBT (enat u') e \<subseteq> GBT v e" by (rule b1x_GBT_antitone[OF vu])
                have G: "\<forall>x \<in> GBT (enat u') e. lessBT x c"
                  using Gv Gsub elt lessBT_trans by blast
                \<comment> \<open>r72: the cofinal chain of the CORRECTED rule is \<open>c[x\<^sub>n]\<close>\<close>
                obtain n where n: "leBT e (operB c (xseq c (enat u') n))"
                  using y4_xseq_cof[OF otc du ote elt G] by blast
                have xlt: "lessBT (xseq c (enat u') n) (xseq c (enat u') (Suc n))"
                  by (rule y4_xseq_lt[OF otc du])
                have z1: "xseq c (enat u') n \<in> TBv (enat u')" by (rule y4_xseq_TBv)
                have z2: "xseq c (enat u') (Suc n) \<in> TBv (enat u')" by (rule y4_xseq_TBv)
                have clt: "lessBT (operB c (xseq c (enat u') n))
                                  (operB c (xseq c (enat u') (Suc n)))"
                  by (rule b1x_mono[OF du z1 z2 xlt])
                have lt: "lessBT e (operB c (xseq c (enat u') (Suc n)))"
                  using n clt b1x_le_less_trans by blast
                have "lessBP (DB w e) (DB v (operB c (xseq c (enat u') (Suc n))))"
                  using lt wv by simp
                hence "leBT b (Trm [DB v (operB c (xseq c (enat u') (Suc n)))])"
                  using bbs beq by simp
                thus ?thesis using opn by metis
              qed
            qed
            have c2: "\<forall>m. domB a = TBv (enat m)
                        \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z))"
              using da NatSet_neq_TBv by auto
            show ?thesis using c1 c2 by blast
          next
            case kiii: False
            \<comment> \<open>([].4)(iii) --- \<open>a[z] = D\<^sub>v c[z]\<close>, IH on \<open>c\<close> + index bump\<close>
            have da: "domB a = domB c" using aeq b1x_domB_case_iii[OF cne dnz kiii] by simp
            have op: "\<And>z. operB a z = Trm [DB v (operB c z)]"
              using aeq b1x_operB_case_iii[OF cne dnz kiii] by simp
            have c1: "(domB a = {Trm []} \<or> domB a = NatSet)
                        \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n)))"
            proof (intro impI)
              assume DA: "domB a = {Trm []} \<or> domB a = NatSet"
              have dcN: "domB c = NatSet" using DA da dnz by blast
              show "\<exists>n. leBT b (operB a (numBT n))"
              proof (cases bs)
                case Nil
                have "leBT b (Trm [DB v (operB c (numBT 0))])" using bbs Nil by simp
                thus ?thesis using op by metis
              next
                case (Cons r rs)
                obtain w e rs' where beq: "bs = DB w e # rs'"
                  and disj: "w < v \<or> (w = v \<and> lessBT e c)" using HS Cons by blast
                show ?thesis
                proof (cases "w < v")
                  case True
                  have "leBT b (Trm [DB v (operB c (numBT 0))])" using True bbs beq by simp
                  thus ?thesis using op by metis
                next
                  case False
                  have wv: "w = v" and elt: "lessBT e c" using disj False by auto
                  have ote: "isOT_BT e" using less.prems(3) bbs beq wv by simp
                  have dfe: "dfree_BT e" using less.prems(4) bbs beq by simp
                  obtain n where n: "leBT e (operB c (numBT n))"
                    using less.IH[OF szc otc dfc ote dfe elt] dcN by blast
                  have "lessBT (operB c (numBT n)) (operB c (numBT (Suc n)))"
                    by (rule y4_N_mono[OF otc dfc dcN])
                  hence lt: "lessBT e (operB c (numBT (Suc n)))"
                    using n b1x_le_less_trans by blast
                  have "lessBP (DB w e) (DB v (operB c (numBT (Suc n))))" using lt wv by simp
                  hence "leBT b (Trm [DB v (operB c (numBT (Suc n)))])" using bbs beq by simp
                  thus ?thesis using op by metis
                qed
              qed
            qed
            have c2: "\<forall>m. domB a = TBv (enat m)
                        \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z))"
            proof (intro allI impI)
              fix m assume dm: "domB a = TBv (enat m)"
              have dcm: "domB c = TBv (enat m)" using da dm by simp
              show "\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z)"
              proof (cases bs)
                case Nil
                have z0: "Trm [] \<in> domB a" using dm b1x_zero_TBv by simp
                have "leBT b (Trm [DB v (operB c (Trm []))])" using bbs Nil by simp
                hence "leBT b (operB a (Trm []))" using op by simp
                thus ?thesis using z0 by auto
              next
                case (Cons r rs)
                obtain w e rs' where beq: "bs = DB w e # rs'"
                  and disj: "w < v \<or> (w = v \<and> lessBT e c)" using HS Cons by blast
                show ?thesis
                proof (cases "w < v")
                  case True
                  have z0: "Trm [] \<in> domB a" using dm b1x_zero_TBv by simp
                  have "leBT b (Trm [DB v (operB c (Trm []))])" using True bbs beq by simp
                  hence "leBT b (operB a (Trm []))" using op by simp
                  thus ?thesis using z0 by auto
                next
                  case False
                  have wv: "w = v" and elt: "lessBT e c" using disj False by auto
                  have ote: "isOT_BT e" using less.prems(3) bbs beq wv by simp
                  have dfe: "dfree_BT e" using less.prems(4) bbs beq by simp
                  obtain z where zin: "z \<in> domB c" and otz: "isOT_BT z" and dfz: "dfree_BT z"
                    and lez: "leBT e (operB c z)"
                    using less.IH[OF szc otc dfc ote dfe elt] dcm by blast
                  have ztv: "z \<in> TBv (enat m)" using zin dcm by simp
                  define z' where "z' = z +\<^sub>B Trm [DB 0 (Trm [])]"
                  have bump: "isOT_BT z' \<and> dfree_BT z' \<and> z' \<in> TBv (enat m) \<and> lessBT z z'"
                    using y4_bump[OF otz dfz ztv] z'_def by simp
                  have "lessBT (operB c z) (operB c z')"
                    using b1x_mono[OF dcm ztv] bump by blast
                  hence lt: "lessBT e (operB c z')" using lez b1x_le_less_trans by blast
                  have "lessBP (DB w e) (DB v (operB c z'))" using lt wv by simp
                  hence "leBT b (Trm [DB v (operB c z')])" using bbs beq by simp
                  hence leb: "leBT b (operB a z')" using op by simp
                  have "z' \<in> domB a" using dm bump by simp
                  thus ?thesis using leb bump by blast
                qed
              qed
            qed
            show ?thesis using c1 c2 by blast
          qed
        qed
      qed
    next
      case ConsQ: (Cons q rest)
      \<comment> \<open>multi-principal: ([].5) reduces to the LAST principal\<close>
      have cseq: "xs = p # q # rest" using ConsP ConsQ by simp
      have ne: "xs \<noteq> []" using cseq by simp
      have split: "xs = butlast xs @ [last xs]" using ne by simp
      have dlast: "domB (Trm [last xs]) = domB a"
        using axs domB_last_component[OF ne] by simp
      have otlast: "isOT_BT (Trm [last xs])"
        using less.prems(1) axs ne by (simp add: last_in_set)
      have dflast: "dfree_BT (Trm [last xs])"
        using less.prems(2) axs ne by (simp add: last_in_set)
      have szlast: "size (Trm [last xs] :: BT) < size a"
        using axs cseq b1x_size_last_lt[of p q rest] by simp
      have op: "\<And>z. operB a z = Trm (butlast xs) +\<^sub>B operB (Trm [last xs]) z"
        using axs cseq b1x_operB_multi[of p q rest] by simp
      have ylt: "lessBT (Trm bs) (Trm (butlast xs @ [last xs]))"
        using less.prems(5) bbs axs split by simp
      have PS: "leBT (Trm bs) (Trm (butlast xs))
                 \<or> (\<exists>rs. bs = butlast xs @ rs \<and> rs \<noteq> [] \<and> lessBP (hd rs) (last xs))"
        by (rule y4_prefix_split[OF ylt])
      show ?thesis
      proof (cases "leBT (Trm bs) (Trm (butlast xs))")
        case True
        have any: "\<And>z. leBT b (operB a z)"
        proof -
          fix z
          have "leBT (Trm (butlast xs)) (Trm (butlast xs) +\<^sub>B operB (Trm [last xs]) z)"
            by (rule y4_leBT_addBT_self)
          thus "leBT b (operB a z)" using True bbs op leBT_trans by metis
        qed
        have c1: "(domB a = {Trm []} \<or> domB a = NatSet)
                    \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n)))" using any by blast
        have c2: "\<forall>m. domB a = TBv (enat m)
                    \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z))"
        proof (intro allI impI)
          fix m assume dm: "domB a = TBv (enat m)"
          have "Trm [] \<in> domB a \<and> isOT_BT (Trm []) \<and> dfree_BT (Trm [])
                  \<and> leBT b (operB a (Trm []))"
            using dm b1x_zero_TBv any by simp
          thus "\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z)" by blast
        qed
        show ?thesis using c1 c2 by blast
      next
        case False
        then obtain rs where rseq: "bs = butlast xs @ rs" and rsne: "rs \<noteq> []"
          and rslt: "lessBP (hd rs) (last xs)" using PS by blast
        have rscons: "rs = hd rs # tl rs" using rsne by simp
        have b'lt: "lessBT (Trm rs) (Trm [last xs])" using rslt by (subst rscons) simp
        have otb': "isOT_BT (Trm rs)"
          using less.prems(3) bbs rseq y4_OT_suffix[of "butlast xs" rs] by simp
        have dfb': "dfree_BT (Trm rs)" using less.prems(4) bbs rseq by simp
        have IH: "((domB (Trm [last xs]) = {Trm []} \<or> domB (Trm [last xs]) = NatSet)
                     \<longrightarrow> (\<exists>n. leBT (Trm rs) (operB (Trm [last xs]) (numBT n))))
                  \<and> (\<forall>m. domB (Trm [last xs]) = TBv (enat m)
                     \<longrightarrow> (\<exists>z. z \<in> domB (Trm [last xs]) \<and> isOT_BT z \<and> dfree_BT z
                                \<and> leBT (Trm rs) (operB (Trm [last xs]) z)))"
          by (rule less.IH[OF szlast otlast dflast otb' dfb' b'lt])
        have breb: "Trm (butlast xs) +\<^sub>B Trm rs = b" using bbs rseq by simp
        have c1: "(domB a = {Trm []} \<or> domB a = NatSet)
                    \<longrightarrow> (\<exists>n. leBT b (operB a (numBT n)))"
        proof (intro impI)
          assume DA: "domB a = {Trm []} \<or> domB a = NatSet"
          hence "domB (Trm [last xs]) = {Trm []} \<or> domB (Trm [last xs]) = NatSet"
            using dlast by simp
          then obtain n where n: "leBT (Trm rs) (operB (Trm [last xs]) (numBT n))"
            using IH by blast
          have "leBT (Trm (butlast xs) +\<^sub>B Trm rs)
                     (Trm (butlast xs) +\<^sub>B operB (Trm [last xs]) (numBT n))"
            by (rule y4_leBT_addBT_mono_right[OF n])
          thus "\<exists>n. leBT b (operB a (numBT n))" using breb op by metis
        qed
        have c2: "\<forall>m. domB a = TBv (enat m)
                    \<longrightarrow> (\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z))"
        proof (intro allI impI)
          fix m assume dm: "domB a = TBv (enat m)"
          hence "domB (Trm [last xs]) = TBv (enat m)" using dlast by simp
          then obtain z where zin: "z \<in> domB (Trm [last xs])" and otz: "isOT_BT z"
            and dfz: "dfree_BT z" and lez: "leBT (Trm rs) (operB (Trm [last xs]) z)"
            using IH by blast
          have "leBT (Trm (butlast xs) +\<^sub>B Trm rs)
                     (Trm (butlast xs) +\<^sub>B operB (Trm [last xs]) z)"
            by (rule y4_leBT_addBT_mono_right[OF lez])
          hence leb: "leBT b (operB a z)" using breb op by metis
          have "z \<in> domB a" using zin dlast by simp
          thus "\<exists>z. z \<in> domB a \<and> isOT_BT z \<and> dfree_BT z \<and> leBT b (operB a z)"
            using otz dfz leb by blast
        qed
        show ?thesis using c1 c2 by blast
      qed
    qed
  qed
qed

text \<open>\<^bold>\<open>\<open>y3_cof0\<close> --- DISCHARGED.\<close>  (It is literally @{thm [source] y4_bachmann}.)\<close>

theorem y4_cof0: "y3_cof0"
  unfolding y3_cof0_def using y4_bachmann by blast


subsection \<open>(7) CAPSTONES --- \<open>wf RPrel\<close> unconditionally, [Buc1] 2.2 RETIRED, and
  PSS termination modulo \<open>{KK}\<close>\<close>

text \<open>\<^bold>\<open>\<open>wf RPrel\<close> is now a THEOREM\<close> (no hypothesis, no citation): the r68 residual
  \<open>bwl_cof\<close> and the r70 residual \<open>y3_cof0\<close> are both discharged by
  @{thm [source] y4_bachmann}.\<close>

theorem y4_wf_RPrel: "wf RPrel"
  by (rule y3_wf_RPrel_of_cof0[OF y4_cof0])

theorem y4_bwl_cof: "bwl_cof"
  by (rule y3_cof0_imp_bwl_cof[OF y4_cof0])

text \<open>\<^bold>\<open>[Buc1] Lemma 2.2 --- RETIRED AS A CITATION.\<close>  The sorry'd
  @{thm [source] buc1_2_2_OT_B_wf} (\<open>(OT\<^bsub>B\<^esub>, <)\<close> is well-founded) is now PROVED,
  with 0 sorry-dependencies, via \<open>W\<^sub>v\<close> ([Buc1-Hydra] \<section>2, the \<open>bwl_\<close> block) plus the
  Bachmann property (this block) plus the tuple lift @{thm [source] wfox_tuple_lift}.\<close>

theorem y4_buc1_2_2_OT_B_wf: "wf {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}"
  using wfox_tuple_lift[OF y4_wf_RPrel] wfox_goal_eq_RTrel by simp

text \<open>\<open>y3_cofimg\<close> --- the r70 residual --- follows from \<open>y3_cof0\<close> given only the census
  totality \<open>Trans N \<in> OT\<^bsub>B\<^esub>\<close>.\<close>

theorem y4_cofimg:
  assumes TOT: "\<And>N. N \<in> ST_PS \<Longrightarrow> Trans N \<in> OT_B"
  shows "y3_cofimg"
  by (rule y3_cofimg_of_bwl_cof[OF y4_bwl_cof TOT])

text \<open>\<^bold>\<open>THE ROUND-71 CAPSTONE.\<close>  PSS termination (accessibility of the one-step
  relation \<open>M \<rightarrow> M[n]\<close> on \<open>ST\<^bsub>PS\<^esub>\<close>) modulo \<^bold>\<open>the single census hypothesis \<open>KK\<close>\<close> ---
  with NO \<open>wf\<close> citation, NO \<open>[Buc1] 2.2\<close>, NO \<open>bwl_cof\<close>, NO \<open>y3_cof0\<close>, NO \<open>y3_cofimg\<close>.
  The order-theoretic residual of the termination proof is GONE.\<close>

theorem y4_PSS_acc_of_KK:
  assumes KK: "\<And>P s0 b0 k. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
             hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIII P \<or> transCondIV P \<Longrightarrow>
             (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
             scb_decomp (bpHeadT (Trans (s84x_N P))) s0
               (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
             s84x_jm3 P < transJm1 P \<Longrightarrow>
             1 \<le> k \<Longrightarrow>
             (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B) \<Longrightarrow>
             lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
               (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                  0\<^sub>B)"
    and MST: "M \<in> ST_PS"
  shows "M \<in> Wellfounded.acc y3_PSSrel"
proof -
  have TOT: "\<And>N. N \<in> ST_PS \<Longrightarrow> Trans N \<in> OT_B"
    using oi10_census_KK(1)[OF KK] by blast
  have COF: "y3_cofimg" by (rule y4_cofimg[OF TOT])
  show ?thesis by (rule y3_PSS_acc_of_KK_cofimg[OF KK COF MST])
qed

text \<open>\<^bold>\<open>Round-71 status.\<close>
  \<^item> \<open>y3_cofimg\<close> (r70's residual): \<^bold>\<open>DISCHARGED\<close> (@{thm [source] y4_cofimg}, modulo census
    totality only).
  \<^item> \<open>y3_cof0\<close>, \<open>bwl_cof\<close> (r68/r70 residuals): \<^bold>\<open>DISCHARGED\<close> unconditionally.
  \<^item> \<open>wf RPrel\<close> / [Buc1] Lemma 2.2: \<^bold>\<open>PROVED\<close>, no longer cited.
  \<^item> PSS termination: modulo \<^bold>\<open>{KK}\<close> ONLY (@{thm [source] y4_PSS_acc_of_KK}).

  The r71 brief's proposed lever ([Buc1-Hydra] \<section>3, the \<open>\<ll>\<^sub>k\<close> relations) turned out
  NOT to contain the needed statement --- that paper has no order \<open><\<close> at all, so its
  \<open>\<ll>\<^sub>k\<close>/\<open>H\<^sub>a\<close> lemmas 3.1--3.8 cannot yield cofinality.  The property was proved from
  scratch instead, on the proven \<open>b1x_\<close> descent/monotonicity/\<open>G\<close>-set toolkit.\<close>


subsection \<open>(8) HONESTY REPORT --- audits, and why the \<open>G\<close>-hypothesis is load-bearing\<close>

text \<open>\<^bold>\<open>(a) The oracle audit is STRUCTURALLY IMPOSSIBLE in this project\<close> (r71 finding).
  All three sessions set \<open>quick_and_dirty\<close> in \<^verbatim>\<open>ROOT\<close>.  Under that option the
  \<open>datatype\<close>/\<open>fun\<close>/\<open>function\<close> packages emit their derived theorems via
  \<^ML>\<open>Goal.prove_sorry\<close>, which CHEATS with the \<open>Pure.skip_proof\<close> oracle.  Consequently
  \<^emph>\<open>every\<close> theorem that so much as mentions \<^typ>\<open>BT\<close> carries \<open>Pure.skip_proof\<close> --- even
  \<open>lessBT.simps\<close> and \<open>descP.simps\<close> themselves.  Measured (r71, \<^ML>\<open>Thm_Deps.all_oracles\<close>):
  \<open>refl\<close>, \<open>conjI\<close>, \<open>list.induct\<close> report \<open>[]\<close>; a fresh \<open>(1::nat)+1 = 2\<close> reports \<open>[]\<close>;
  a fresh \<open>lessBT 0\<^sub>B (D\<^sub>0 0)\<close> reports \<open>[Pure.skip_proof]\<close>.  So an oracle audit CANNOT
  distinguish a real \<open>sorry\<close> from a package artifact here, and any past claim of
  "0 sorry-dependencies" must be read as a BY-NAME audit, not a proof-term audit.
  (\<open>quick_and_dirty\<close> cannot simply be switched off: the frozen \<open>pss_paper\<close> citations
  are \<open>sorry\<close>, which batch mode rejects without it.)

  \<^bold>\<open>(b) By-name transitive audit\<close> (the audit that IS available; the \<open>sorry\<close>'d citations
  are plain \<open>lemma \<dots> sorry\<close>, never \<open>[simp]\<close>, so they can only enter by explicit name):
  \<^item> @{thm [source] y4_xseq_cof}, @{thm [source] y4_bachmann}, @{thm [source] y4_cof0},
    @{thm [source] y4_wf_RPrel}, @{thm [source] y4_buc1_2_2_OT_B_wf},
    @{thm [source] y4_cofimg}: \<^bold>\<open>SORRY-FREE\<close>.
  \<^item> @{thm [source] y4_PSS_acc_of_KK} reaches exactly TWO \<open>sorry\<close>'d citations, BOTH via
    \<open>oi10_census_KK\<close> (the census), namely \<open>buc1_3_2a_fseq_lt\<close> and
    \<open>m_6_8_slice_Br_descending_monoT\<close>.  These are \<^bold>\<open>INHERITED, not introduced\<close>: r70's
    capstone \<open>y3_PSS_acc_of_KK_cofimg\<close> has precisely the same two.  \<open>buc1_3_2a_fseq_lt\<close>
    ([Buc1] 3.2(a), \<open>a[n] < a\<close>) is the known STALE citation --- it is already proved
    unconditionally as @{thm [source] b1x_descent}; rewiring \<open>f7x_fseq_descend_mono\<close> to
    \<open>b1x_descent\<close> would remove it (a layerB edit, hence out of this front's scope).

  \<^bold>\<open>(c) Vacuity.\<close>  @{thm [source] y4_cof0}, @{thm [source] y4_wf_RPrel} and
  @{thm [source] y4_buc1_2_2_OT_B_wf} have \<^bold>\<open>no hypotheses at all\<close>, so they cannot be
  vacuously green.  @{thm [source] y4_bachmann}: 16 359 156 \<open>OT\<close>/\<open>D\<^sub>\<omega>\<close>-free pairs \<open>b < a\<close>
  checked (terms of \<open>\<le> 5\<close> \<open>D\<close>-nodes, indices \<open>\<le> 2\<close>), 0 failures, and all three domain
  cases are exercised (\<open>{0}\<close>: 2 557 682; \<open>\<nat>\<close>: 8 063 522; \<open>T\<^sub>u\<close>: 5 737 952).

  \<^bold>\<open>(d) The \<open>G\<close>-hypothesis of @{thm [source] y4_xseq_cof} is LOAD-BEARING\<close>, not decoration.
  Of \<^bold>\<open>4 813 348\<close> hosts satisfying all its hypotheses (terms of \<open>\<le> 5\<close> \<open>D\<close>-nodes,
  indices \<open>\<le> 2\<close>), \<^bold>\<open>4 466 385 have \<open>G\<^sub>u e \<noteq> \<emptyset>\<close>\<close> (93%) --- the hypothesis is
  genuinely exercised, not vacuously true --- and the conclusion holds in
  4 813 348/4 813 348, 0 failures.  Dropping the \<open>G\<close>-hypothesis produces
  \<^bold>\<open>13 845 genuine counterexamples\<close>, e.g. \<open>c = D\<^sub>1 0\<close>, \<open>u = 0\<close>, \<open>e = D\<^sub>0(D\<^sub>1 0)\<close>:
  then \<open>e < c\<close> but \<open>e\<close> exceeds EVERY \<open>x\<^sub>n = D\<^sub>0\<^bsup>n+1\<^esup>0\<close>.  In every one of those
  13 845 the offending \<open>G\<close>-escape is \<open>\<ge> c\<close> --- exactly what the hypothesis forbids.
  So the \<open>OT\<close> \<open>G\<close>-condition is precisely the discriminating content of the collapsing
  cofinality.  (Shallower run, \<open>\<le> 4\<close> nodes: 115 225/126 701 non-vacuous, 1 168
  counterexamples --- same picture.)\<close>



text \<open>\<^bold>\<open>The ARTICLE'S OWN route, assembled --- and now CITATION-FREE.\<close>  The article derives
  termination from the two pillars plus the well-ordering of \<open>(OT\<^bsub>B\<^esub>, <)\<close>, which it CITES
  as [Buc1] Lemma 2.2.  We no longer need the citation: the very same statement is our own
  theorem @{thm [source] y4_buc1_2_2_OT_B_wf}.  So this is the article's route, transcribed
  faithfully, with the citation slot filled by our proof --- PSS termination in the article's
  own \<open>wf\<close> form, modulo the SINGLE residual \<open>KK\<close>, with no \<open>sorry\<close> anywhere.\<close>

theorem y4_PSS_wf_of_KK:
  assumes KK: "\<And>P s0 b0 k. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
             hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIII P \<or> transCondIV P \<Longrightarrow>
             (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
             scb_decomp (bpHeadT (Trans (s84x_N P))) s0
               (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
             s84x_jm3 P < transJm1 P \<Longrightarrow>
             1 \<le> k \<Longrightarrow>
             (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B) \<Longrightarrow>
             lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
               (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                  0\<^sub>B)"
  shows "wf y3_PSSrel"
proof -
  have TOT: "\<And>N. N \<in> ST_PS \<Longrightarrow> Trans N \<in> OT_B"
    using oi10_census_KK(1)[OF KK] by blast
  have DESC: "\<And>N n. N \<in> ST_PS \<Longrightarrow> 1 \<le> n \<Longrightarrow> 1 < Lng N \<Longrightarrow>
                lessBT (Trans ((N::pairseq)[n])) (Trans N)"
    using oi10_census_KK(2)[OF KK] by blast
  have wfR: "wf {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}"
    by (rule y4_buc1_2_2_OT_B_wf)
  have sub: "y3_PSSrel
               \<subseteq> inv_image {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b} Trans"
  proof
    fix p :: "pairseq \<times> pairseq"
    assume "p \<in> y3_PSSrel"
    then obtain N M' n where p: "p = (N, M')" and MST': "M' \<in> ST_PS"
      and Lg: "1 < Lng M'" and n1: "1 \<le> n" and Neq: "N = (M'::pairseq)[n]"
      unfolding y3_PSSrel_def by auto
    have NST: "N \<in> ST_PS"
      using Neq MST' n1 by (simp add: ST_PS.oper)
    have lt: "lessBT (Trans N) (Trans M')"
      using Neq DESC[OF MST' n1 Lg] by simp
    show "p \<in> inv_image {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b} Trans"
      using p TOT[OF NST] TOT[OF MST'] lt by simp
  qed
  show "wf y3_PSSrel"
    by (rule wf_subset[OF wf_inv_image[OF wfR] sub])
qed

corollary y4_PSS_acc_of_KK_wf:
  assumes KK: "\<And>P s0 b0 k. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
             hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
             transCondIII P \<or> transCondIV P \<Longrightarrow>
             (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
             scb_decomp (bpHeadT (Trans (s84x_N P))) s0
               (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
             s84x_jm3 P < transJm1 P \<Longrightarrow>
             1 \<le> k \<Longrightarrow>
             (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B) \<Longrightarrow>
             lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
               (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                  0\<^sub>B)"
    and MST: "M \<in> ST_PS"
  shows "M \<in> Wellfounded.acc y3_PSSrel"
  by (rule acc_wfD[OF y4_PSS_wf_of_KK[OF KK]])


(* ================================================================= *)
(*   r72 front A (prefix  ox12_ / oi12_ / y5_ ).   K K   I S   C L O S E D.  *)
(*                                                                     *)
(*   The BOTTOM GUARD  BG  of r71 is NOT NEEDED.  ox11_safe is VACUOUS *)
(*   on the census, by a pure SIZE count -- the left operand simply    *)
(*   HAS NOT GOT ENOUGH PRINCIPAL SYMBOLS to walk all the way down to  *)
(*   the hole.  This is the formal content of the r70/r71 empirical    *)
(*   observation "the walk reaches the hole 0 times out of 4301".      *)
(*                                                                     *)
(*   szT (Trm ps) = sum of szP over ps,  szP (D_v b) = 1 + szT b.      *)
(*                                                                     *)
(*   (a) Down the walk the strict inequality szT Z < szT W is an       *)
(*       INVARIANT: if W = (ps @ [D_w LW]) and Z = (ps @ D_w t # rest) *)
(*       then szT W = szT ps + 1 + szT LW and szT Z = szT ps + 1 +     *)
(*       szT t + szT rest, so szT Z < szT W forces szT t < szT LW.     *)
(*   (b) At the BOTTOM the hole principal is p = D_v1 0, of size 1.    *)
(*       So szT W = szT ps + 1, while any Z = (ps @ x # rest) has      *)
(*       szT Z >= szT ps + szP x >= szT ps + 1 = szT W.  Contradiction *)
(*       with the invariant: the bottom clause is VACUOUS.             *)
(*   (c) The left operand of KK is  ox8_rsub body k  with  k >= 1, and *)
(*       one right-spine step strictly drops szT (it discards the D of *)
(*       the last principal, and every sibling).  So szT Z < szT body. *)
(*                                                                     *)
(*   Combining, ox11_safe dR p pX (ox8_rsub body k) body holds with NO *)
(*   hypothesis, and ox11_TT transports ox8_body_rspine_lessBT across  *)
(*   the surgery.  KK follows unconditionally.                         *)
(*                                                                     *)
(*   NOTE the two REFUTED cousins of this measure (do not re-attempt): *)
(*     * HEIGHT instead of size: FALSE (31/477 census hosts have a     *)
(*       branch deeper than the right spine; python/_r72_ht.py).       *)
(*     * a global "every principal anywhere" guard (ox9_ok/OKH): FALSE *)
(*       (ox10_cex_not_ok).                                            *)
(*   Size is exactly the measure that both the head-tie descent and    *)
(*   the prefix-match consume, which is why it -- and not height --    *)
(*   closes the walk.                                                  *)
(* ================================================================= *)

section \<open>r72 ox12 --- \<open>KK\<close> CLOSED: \<open>ox11_safe\<close> is vacuous by a SIZE count\<close>

subsection \<open>(1) The symbol count \<open>ox12_szT\<close> / \<open>ox12_szP\<close>\<close>

fun ox12_szT :: "BT \<Rightarrow> nat" and ox12_szP :: "BP \<Rightarrow> nat" where
  "ox12_szT (Trm ps) = sum_list (map ox12_szP ps)"
| "ox12_szP (DB v b) = Suc (ox12_szT b)"

lemma ox12_szP_pos: "Suc 0 \<le> ox12_szP x"
  by (cases x) simp

lemma ox12_szT_zero: "ox12_szT 0\<^sub>B = 0"
  by simp

text \<open>The hole principal \<open>D\<^bsub>v\<^sub>1\<^esub>0\<close> has size exactly \<open>1\<close> --- this is the fact that
  makes the bottom clause of @{const ox11_safe} vacuous.\<close>

lemma ox12_szP_Dzero: "ox12_szP (DB v 0\<^sub>B) = Suc 0"
  by simp


subsection \<open>(2) THE COLLAPSE: \<open>ox11_safe\<close> from \<open>ox12_szT Z < ox12_szT W\<close>\<close>

text \<open>\<^bold>\<open>The r72 keystone.\<close>  If the left operand \<open>Z\<close> carries strictly fewer
  \<open>D\<close>-symbols than \<open>W\<close>, the lex walk of \<open>Z\<close> against \<open>W\<close> can NEVER reach the
  hole, whatever the hole depth \<open>e\<close> --- PROVIDED the hole principal \<open>p\<close> is
  \<open>D\<^sub>v 0\<close> (size \<open>1\<close>), which on the census it is.  No guard, no \<open>G\<close>-set, no
  \<open>OT\<close>: pure counting.\<close>

lemma ox12_safe_of_size_aux:
  assumes P0: "ox12_szP p = Suc 0"
  shows "\<forall>Z W. ox12_szT Z < ox12_szT W \<longrightarrow> ox11_safe e p q Z W"
proof (induction e)
  case 0
  show ?case
  proof (intro allI impI)
    fix Z W :: BT
    assume LT: "ox12_szT Z < ox12_szT W"
    have G: "\<forall>ps x rest. W = Trm (ps @ [p]) \<longrightarrow> Z = Trm (ps @ x # rest)
               \<longrightarrow> lessBP x p \<longrightarrow> lessBP x q"
    proof (intro allI impI)
      fix ps :: "BP list" and x :: BP and rest :: "BP list"
      assume WE: "W = Trm (ps @ [p])" and ZE: "Z = Trm (ps @ x # rest)"
      have szW: "ox12_szT W = ox12_szT (Trm ps) + Suc 0" using WE P0 by simp
      have szZ: "ox12_szT Z
                   = ox12_szT (Trm ps) + ox12_szP x + ox12_szT (Trm rest)"
        using ZE by simp
      have xpos: "Suc 0 \<le> ox12_szP x" by (rule ox12_szP_pos)
      have False using LT szW szZ xpos by linarith
      thus "lessBP x q" by simp
    qed
    show "ox11_safe 0 p q Z W" using G by simp
  qed
next
  case (Suc e)
  show ?case
  proof (intro allI impI)
    fix Z W :: BT
    assume LT: "ox12_szT Z < ox12_szT W"
    have G: "\<forall>ps w LW t rest. W = Trm (ps @ [DB w LW])
               \<longrightarrow> Z = Trm (ps @ DB w t # rest)
               \<longrightarrow> lessBT t LW \<longrightarrow> ox11_safe e p q t LW"
    proof (intro allI impI)
      fix ps :: "BP list" and w :: enat and LW :: BT and t :: BT
        and rest :: "BP list"
      assume WE: "W = Trm (ps @ [DB w LW])" and ZE: "Z = Trm (ps @ DB w t # rest)"
      have szW: "ox12_szT W = ox12_szT (Trm ps) + Suc (ox12_szT LW)"
        using WE by simp
      have szZ: "ox12_szT Z
                   = ox12_szT (Trm ps) + Suc (ox12_szT t) + ox12_szT (Trm rest)"
        using ZE by simp
      have tlt: "ox12_szT t < ox12_szT LW" using LT szW szZ by linarith
      show "ox11_safe e p q t LW" using Suc.IH tlt by blast
    qed
    show "ox11_safe (Suc e) p q Z W" using G by simp
  qed
qed

lemma ox12_safe_of_size:
  assumes P0: "ox12_szP p = Suc 0" and LT: "ox12_szT Z < ox12_szT W"
  shows "ox11_safe e p q Z W"
  using ox12_safe_of_size_aux[OF P0] LT by blast


subsection \<open>(3) One right-spine step strictly drops the symbol count\<close>

lemma ox12_sz_lastT_lt:
  assumes ne: "t \<noteq> 0\<^sub>B"
  shows "ox12_szT (ox8_lastT t) < ox12_szT t"
proof -
  obtain ps where T: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using ne T by auto
  obtain as x where SP: "ps = as @ [x]"
    by (metis psne append_butlast_last_id)
  obtain w b where X: "x = DB w b" by (cases x)
  have T2: "t = Trm (as @ [DB w b])" using T SP X by simp
  have lt: "ox8_lastT t = b" using T2 by simp
  have sz: "ox12_szT t = ox12_szT (Trm as) + Suc (ox12_szT b)" using T2 by simp
  show ?thesis using lt sz by simp
qed

lemma ox12_sz_rsub_le: "ox12_szT (ox8_rsub t k) \<le> ox12_szT t"
proof (induction k arbitrary: t)
  case 0
  show ?case by simp
next
  case (Suc k)
  have step: "ox12_szT (ox8_lastT t) \<le> ox12_szT t"
  proof (cases "t = 0\<^sub>B")
    case True
    thus ?thesis by simp
  next
    case False
    show ?thesis using ox12_sz_lastT_lt[OF False] by simp
  qed
  have "ox12_szT (ox8_rsub t (Suc k)) = ox12_szT (ox8_rsub (ox8_lastT t) k)"
    by simp
  also have "\<dots> \<le> ox12_szT (ox8_lastT t)" by (rule Suc.IH)
  also have "\<dots> \<le> ox12_szT t" by (rule step)
  finally show ?case .
qed

lemma ox12_sz_rsub_lt:
  assumes ne: "t \<noteq> 0\<^sub>B" and k1: "1 \<le> k"
  shows "ox12_szT (ox8_rsub t k) < ox12_szT t"
proof -
  obtain j where kj: "k = Suc j" using k1 by (cases k) auto
  have "ox12_szT (ox8_rsub t k) = ox12_szT (ox8_rsub (ox8_lastT t) j)"
    using kj by simp
  also have "\<dots> \<le> ox12_szT (ox8_lastT t)" by (rule ox12_sz_rsub_le)
  also have "\<dots> < ox12_szT t" by (rule ox12_sz_lastT_lt[OF ne])
  finally show ?thesis .
qed


subsection \<open>(4) \<open>KK\<close> --- PROVED (the census, with \<open>Trans N \<in> OT\<^bsub>B\<^esub>\<close> available)\<close>

text \<open>The r70/r71 residual \<open>KK\<close>, discharged.  Everything is as in
  @{thm [source] ox11_KK_of_BG} except that the bottom guard \<open>BG\<close> is replaced by
  @{thm [source] ox12_safe_of_size}: the hole principal is \<open>D\<^bsub>v\<^sub>1\<^esub>0\<close> (size \<open>1\<close>) and
  the left operand \<open>ox8_rsub body k\<close> (\<open>k \<ge> 1\<close>) is strictly smaller than \<open>body\<close>,
  so @{const ox11_safe} holds for free.  No case split on \<open>k \<le> d\<^sub>R\<close> is needed
  either --- the size argument covers the dead-spine range as well.\<close>

theorem ox12_KK:
  fixes N :: pairseq and s0 b0 :: "Sym list" and k :: nat
  assumes NST: "N \<in> ST_PS" and NPT: "N \<in> PT_PS"
    and hp: "hasParent N 1 (Lng N - 1)"
    and j1gt: "1 < Lng N - 1"
    and branch: "transCondIII N \<or> transCondIV N"
    and ihOT: "Trans N \<in> OT_B"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and inner: "scb_decomp (bpHeadT (Trans (s84x_N N))) s0
                 (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0"
    and ltJ: "s84x_jm3 N < transJm1 N"
    and kge: "1 \<le> k"
    and alive: "\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N N))) j \<noteq> 0\<^sub>B"
  shows "lessBT (ox8_rsub (bpHeadT (Trans (s84x_N N))) k)
           (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
              0\<^sub>B)"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X0 = "(0\<^sub>B :: BT)"
  let ?X1 = "d4vx_ins s0 ?ub b0 ?X0"
  let ?A1 = "d4vx_ins s0 ?ub b0 ?A0"
  let ?p = "DB (enat ?v1) 0\<^sub>B"
  let ?pX = "DB (enat ?ub) ?X0"
  \<comment> \<open>the flat surgery, and the hole relation it induces (verbatim from \<open>ox11\<close>)\<close>
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have fA1: "flatBT ?A1 = s0 @ flatBP (DB (enat ?ub) ?A0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ?ub ?A0] by simp
  have fX1: "flatBT ?X1 = s0 @ flatBP (DB (enat ?ub) ?X0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ?ub ?X0] by simp
  obtain dR where
      hdA: "ox9_holeD dR ?p (DB (enat ?ub) ?A0) ?body ?A1"
    and hdX: "ox9_holeD dR ?p ?pX ?body ?X1"
    using ox9_holeD_of_flat3[OF wrap fA1 fX1 b0RP] by blast
  \<comment> \<open>the SIZE collapse: \<open>ox11_safe\<close> for free\<close>
  have bodyne: "?body \<noteq> 0\<^sub>B" by (rule ox9_holeD_ne[OF hdX])
  have psz: "ox12_szP ?p = Suc 0" by (rule ox12_szP_Dzero)
  have szlt: "ox12_szT (ox8_rsub ?body k) < ox12_szT ?body"
    by (rule ox12_sz_rsub_lt[OF bodyne kge])
  have safe: "ox11_safe dR ?p ?pX (ox8_rsub ?body k) ?body"
    by (rule ox12_safe_of_size[OF psz szlt])
  \<comment> \<open>the self-maximality of the census body (r68), transported (r71)\<close>
  have lt: "lessBT (ox8_rsub ?body k) ?body"
    by (rule ox8_body_rspine_lessBT[OF NST NPT hp j1gt branch ihOT ltJ kge alive])
  show ?thesis by (rule ox11_TT[OF hdX safe lt])
qed


subsection \<open>(5) The census roll-up --- UNCONDITIONAL\<close>

text \<open>@{thm [source] oi11_census_BG} with \<open>BG\<close> discharged by @{thm [source] ox12_KK}.
  Both termination pillars, with \<^bold>\<open>no residual hypothesis\<close>.\<close>

theorem oi12_census:
  shows "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    and "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have SETLE1: "\<And>P s0 b0 u. P \<in> ST_PS \<Longrightarrow> P \<in> PT_PS \<Longrightarrow>
        hasParent P 1 (Lng P - 1) \<Longrightarrow> 1 < Lng P - 1 \<Longrightarrow>
        transCondIII P \<or> transCondIV P \<Longrightarrow> Trans P \<in> OT_B \<Longrightarrow>
        (\<forall>x \<in> set b0. x = RP) \<Longrightarrow>
        scb_decomp (bpHeadT (Trans (s84x_N P))) s0
          (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0 \<Longrightarrow>
        s84x_jm3 P < transJm1 P \<Longrightarrow>
        b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
  proof -
    fix P :: pairseq and s0 b0 :: "Sym list" and u :: enat
    assume A1: "P \<in> ST_PS" and A2: "P \<in> PT_PS"
      and A3: "hasParent P 1 (Lng P - 1)" and A4: "1 < Lng P - 1"
      and A5: "transCondIII P \<or> transCondIV P" and A6: "Trans P \<in> OT_B"
      and A7: "\<forall>x \<in> set b0. x = RP"
      and A8: "scb_decomp (bpHeadT (Trans (s84x_N P))) s0
                (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0"
      and A9: "s84x_jm3 P < transJm1 P"
    have H: "\<And>k. 1 \<le> k \<Longrightarrow>
               (\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B) \<Longrightarrow>
               lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
                 (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    0\<^sub>B)"
    proof -
      fix k :: nat assume kge: "1 \<le> k"
        and alv: "\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B"
      show "lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
              (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                 0\<^sub>B)"
        by (rule ox12_KK[OF A1 A2 A3 A4 A5 A6 A7 A8 A9 kge alv])
    qed
    show "b1x_setle
          (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                    (bpHeadT (Trans (Pred (s84x_N P))))))
          (insert (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                     0\<^sub>B)
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            0\<^sub>B)))"
      by (rule ox10_SETLE1_ltJ[OF A1 A2 A3 A4 A5 A7 A8 A9 H])
  qed
  show "\<forall>M. M \<in> ST_PS \<longrightarrow> Trans M \<in> OT_B"
    by (rule oi8_census_final_ivadmeq(1)[OF SETLE1 ot9_FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
         lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oi8_census_final_ivadmeq(2)[OF SETLE1 ot9_FINRC])
qed


subsection \<open>(6) \<open>KK\<close> in the exact shape the capstones assume (no \<open>OT\<^bsub>B\<^esub>\<close> premise)\<close>

text \<open>@{thm [source] ox12_KK} needs \<open>Trans N \<in> OT\<^bsub>B\<^esub>\<close>, which the capstones'
  \<open>KK\<close> does not supply.  It is now free: @{thm [source] oi12_census}(1) gives it for
  every \<open>N \<in> ST_PS\<close>, unconditionally.\<close>

theorem ox12_KK_free:
  fixes P :: pairseq and s0 b0 :: "Sym list" and k :: nat
  assumes A1: "P \<in> ST_PS" and A2: "P \<in> PT_PS"
    and A3: "hasParent P 1 (Lng P - 1)"
    and A4: "1 < Lng P - 1"
    and A5: "transCondIII P \<or> transCondIV P"
    and A7: "\<forall>x \<in> set b0. x = RP"
    and A8: "scb_decomp (bpHeadT (Trans (s84x_N P))) s0
               (flatBT (Dpt (enat (entry P 1 (Lng P - 1))) 0\<^sub>B)) b0"
    and A9: "s84x_jm3 P < transJm1 P"
    and kge: "1 \<le> k"
    and alive: "\<forall>j<k. ox8_rsub (bpHeadT (Trans (s84x_N P))) j \<noteq> 0\<^sub>B"
  shows "lessBT (ox8_rsub (bpHeadT (Trans (s84x_N P))) k)
           (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
              0\<^sub>B)"
proof -
  have A6: "Trans P \<in> OT_B" using oi12_census(1) A1 by blast
  show ?thesis by (rule ox12_KK[OF A1 A2 A3 A4 A5 A6 A7 A8 A9 kge alive])
qed


subsection \<open>(7) \<^bold>\<open>PSS TERMINATION --- UNCONDITIONAL\<close>\<close>

text \<open>\<^bold>\<open>THE THEOREM.\<close>  \<open>KK\<close> was the single residual hypothesis of both r71
  capstones (@{thm [source] y4_PSS_wf_of_KK}, @{thm [source] y4_PSS_acc_of_KK}).
  @{thm [source] ox12_KK_free} discharges it.  Hence the termination of the pair
  sequence system is proved outright: no residual hypothesis, no \<open>sorry\<close>, no
  citation ([Buc1] Lemma 2.2 is our own @{thm [source] y4_buc1_2_2_OT_B_wf}).
  The ML audit block below fails the build if any of these reaches a \<open>sorry\<close>'d
  statement of \<open>pss_paper\<close>.\<close>

theorem y5_PSS_wf: "wf y3_PSSrel"
  by (rule y4_PSS_wf_of_KK[OF ox12_KK_free])

theorem y5_PSS_acc:
  assumes MST: "M \<in> ST_PS"
  shows "M \<in> Wellfounded.acc y3_PSSrel"
  by (rule y4_PSS_acc_of_KK[OF ox12_KK_free MST])

theorem y5_Trans_OT_B: "M \<in> ST_PS \<Longrightarrow> Trans M \<in> OT_B"
  using oi12_census(1) by blast

theorem y5_Trans_descend:
  "M \<in> ST_PS \<Longrightarrow> 1 \<le> n \<Longrightarrow> 1 < Lng M \<Longrightarrow>
     lessBT (Trans ((M::pairseq)[n])) (Trans M)"
  using oi12_census(2) by blast


subsection \<open>(8) The ARTICLE'S OWN termination statement (\<open>p_8_7_termination\<close>)\<close>

text \<open>\<open>wf y3_PSSrel\<close> is termination in OUR formulation.  The article states it as
  \<open>Fdom f M n\<close> --- the expansion recursion \<open>(M,n) \<mapsto> (M[n], f n)\<close> reaches
  \<open>Lng = 1\<close> (\<^const>\<open>Fdom\<close>, \<open>pss_defs\<close> \<section>5.4).  We discharge that statement
  outright, by well-founded induction along @{thm [source] y5_PSS_acc}.

  The only extra ingredient is that an \<open>ST_PS\<close> sequence is never EMPTY (otherwise
  neither \<^const>\<open>Fdom\<close> rule could fire): \<open>diagSeq u v\<close> has length \<open>Suc v - u \<ge> 1\<close>,
  and \<^const>\<open>oper\<close> preserves non-emptiness --- in the degenerate branches because
  \<^const>\<open>Pred\<close> does, and in the tiling branch because \<open>take j\<^sub>0 M @ \<Oplus>\<^bsub>k<n\<^esub> B\<^sub>k\<close> has
  length \<open>min j\<^sub>0 (Lng M) + n \<cdot> (j\<^sub>1 - j\<^sub>0)\<close>, which is \<open>\<ge> 1\<close> whether \<open>j\<^sub>0 = 0\<close>
  (then \<open>n \<cdot> j\<^sub>1 \<ge> 1\<close>, as \<open>n \<ge> 1\<close> and \<open>j\<^sub>1 \<noteq> 0\<close> in that branch) or \<open>j\<^sub>0 \<ge> 1\<close>.\<close>

lemma y5_take_concat_ne:
  fixes M :: "'a list" and F :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  assumes L: "1 \<le> length M" and n1: "1 \<le> n" and j1: "0 < j1"
  shows "take j0 M @ concat (map (\<lambda>k. map (F k) [j0..<j1]) [0..<n]) \<noteq> []"
proof (cases "j0 = 0")
  case False
  hence j0pos: "0 < j0" by simp
  have "take j0 M \<noteq> []" using L j0pos by (cases M) auto
  thus ?thesis by simp
next
  case True
  have "concat (map (\<lambda>k. map (F k) [j0..<j1]) [0..<n]) \<noteq> []"
  proof -
    have U: "[0..<n] = 0 # [Suc 0..<n]" using n1 by (simp add: upt_conv_Cons)
    have "concat (map (\<lambda>k. map (F k) [j0..<j1]) [0..<n])
            = map (F 0) [j0..<j1]
                @ concat (map (\<lambda>k. map (F k) [j0..<j1]) [Suc 0..<n])"
      using U by simp
    moreover have "map (F 0) [j0..<j1] \<noteq> []" using True j1 by simp
    ultimately show ?thesis by simp
  qed
  thus ?thesis using True by simp
qed

lemma y5_Lng_Pred_pos:
  assumes L: "1 \<le> Lng M"
  shows "1 \<le> Lng (Pred M)"
proof (cases "Lng M \<le> 1")
  case True
  have "Pred M = M" using True by (simp add: Pred_def)
  thus ?thesis using L by simp
next
  case False
  have "Pred M = butlast M" using False by (simp add: Pred_def)
  hence "Lng (Pred M) = Lng M - 1" by simp
  thus ?thesis using False by simp
qed

lemma y5_Lng_oper_pos:
  assumes L: "1 \<le> Lng M" and n1: "1 \<le> n"
  shows "1 \<le> Lng ((M::pairseq)[n])"
proof (cases "1 < Lng M")
  case False
  hence L1: "Lng M = 1" using L by simp
  have "(M::pairseq)[n] = M" by (rule roper_oper_Lng1[OF L1])
  thus ?thesis using L by simp
next
  case True
  note Lgt = True
  have predpos: "1 \<le> Lng (Pred M)" by (rule y5_Lng_Pred_pos[OF L])
  \<comment> \<open>rewrite the three GUARDS to \<open>True\<close>/\<open>False\<close> --- never let \<open>simp\<close> de Morgan them\<close>
  have nz: "(Lng M - 1 = 0) = False" using Lgt by simp
  show ?thesis
  proof (cases "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0")
    case True
    have c2: "(entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0) = True"
      using True by simp
    have "(M::pairseq)[n] = Pred M"
      unfolding oper_def Let_def by (simp only: nz c2 if_False if_True)
    thus ?thesis using predpos by simp
  next
    case False
    note nzero = False
    have c2: "(entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0) = False"
      using nzero by simp
    show ?thesis
    proof (cases "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
      case False
      have c3: "(\<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)) = True"
        using False by simp
      have "(M::pairseq)[n] = Pred M"
        unfolding oper_def Let_def by (simp only: nz c2 c3 if_False if_True)
      thus ?thesis using predpos by simp
    next
      case True
      note hp = True
      let ?j1 = "Lng M - 1"
      let ?i1 = "idx1 M ?j1"
      let ?j0 = "parent M ?i1 ?j1"
      let ?d0 = "(if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0)"
      let ?d1 = "(if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0)"
      have E: "(M::pairseq)[n]
                 = take ?j0 M
                     @ concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0,
                                                    entry M 1 j + k * ?d1))
                                            [?j0..<?j1])
                                   [0..<n])"
        using poper_oper_expand[OF Lgt nzero hp] by (simp only: Let_def)
      have jpos: "0 < ?j1" using Lgt by simp
      have NE: "(M::pairseq)[n] \<noteq> []"
        using E y5_take_concat_ne[OF L n1 jpos, of ?j0
                 "\<lambda>k j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)"]
        by simp
      \<comment> \<open>\<open>length_greater_0_conv\<close> is not usable here (simpset loop) --- use \<open>cases\<close>\<close>
      show ?thesis using NE by (cases "(M::pairseq)[n]") auto
    qed
  qed
qed

lemma y5_ST_PS_Lng_pos:
  assumes "M \<in> ST_PS"
  shows "1 \<le> Lng M"
  using assms
proof (induction M rule: ST_PS.induct)
  case (diag u v)
  thus ?case by simp
next
  case (oper M n)
  show ?case by (rule y5_Lng_oper_pos[OF oper.IH oper.hyps(2)])
qed

text \<open>\<^bold>\<open>THE ARTICLE'S THEOREM.\<close>  \<open>p_8_7_termination\<close> (\<open>pss_paper\<close>, transcribed as
  \<open>sorry\<close>): for \<open>M \<in> ST_PS\<close>, \<open>n \<ge> 1\<close> and any \<open>f\<close> with \<open>f(k) \<ge> 1\<close> for \<open>k \<ge> 1\<close>,
  the pair sequence system \<open>F\<^sub>M(n)\<close> is DEFINED --- i.e. the expansion halts.
  PROVED, unconditionally.\<close>

theorem y5_Fdom:
  assumes MST: "M \<in> ST_PS" and n1: "1 \<le> n"
    and fpos: "\<And>k. 1 \<le> k \<Longrightarrow> 1 \<le> f k"
  shows "Fdom f M n"
proof -
  have accM: "M \<in> Wellfounded.acc y3_PSSrel" by (rule y5_PSS_acc[OF MST])
  have MAIN: "\<And>x. x \<in> Wellfounded.acc y3_PSSrel \<Longrightarrow>
                  x \<in> ST_PS \<longrightarrow> (\<forall>m. 1 \<le> m \<longrightarrow> Fdom f x m)"
  proof -
    fix x0 :: pairseq
    assume A0: "x0 \<in> Wellfounded.acc y3_PSSrel"
    show "x0 \<in> ST_PS \<longrightarrow> (\<forall>m. 1 \<le> m \<longrightarrow> Fdom f x0 m)"
      using A0
    proof (induction rule: Wellfounded.acc.induct)
      case (accI x)
      show ?case
      proof
        assume xST: "x \<in> ST_PS"
        show "\<forall>m. 1 \<le> m \<longrightarrow> Fdom f x m"
        proof (intro allI impI)
          fix m :: nat assume m1: "1 \<le> m"
          show "Fdom f x m"
          proof (cases "1 < Lng x")
            case False
            have "1 \<le> Lng x" by (rule y5_ST_PS_Lng_pos[OF xST])
            hence L1: "Lng x = 1" using False by simp
            show ?thesis by (rule Fdom.Fdom_base[OF L1])
          next
            case True
            have step: "((x::pairseq)[m], x) \<in> y3_PSSrel"
              using xST True m1 by (auto simp: y3_PSSrel_def)
            have opST: "(x::pairseq)[m] \<in> ST_PS" by (rule ST_PS.oper[OF xST m1])
            have fm1: "1 \<le> f m" by (rule fpos[OF m1])
            have D: "Fdom f ((x::pairseq)[m]) (f m)"
              using accI.IH[OF step] opST fm1 by blast
            show ?thesis by (rule Fdom.Fdom_step[OF True D])
          qed
        qed
      qed
    qed
  qed
  show ?thesis using MAIN[OF accM] MST n1 by blast
qed


text \<open>\<^bold>\<open>Circularity / sorry audit\<close> (fails the build if violated, so a green build IS
  the audit).  Two facts are asserted:
  \<^item> Our proof of [Buc1] Lemma 2.2 (@{thm [source] y4_buc1_2_2_OT_B_wf}) and its
    ingredients depend on \<^bold>\<open>no\<close> \<open>sorry\<close> at all --- in particular NOT on the cited
    \<open>pss_paper.buc1_2_2_OT_B_wf\<close> they replace.  So the citation is genuinely DISCHARGED,
    not assumed.
  \<^item> The termination theorem @{thm [source] y4_PSS_acc_of_KK} inherits exactly ONE
    \<open>sorry\<close>, \<open>pss_paper.buc1_3_2a_fseq_lt\<close> --- and that one is STALE: the very same
    statement is already proved as \<open>m_buc1_3_2a_fseq_lt\<close> (layerB).  Removing it is a
    citation-hygiene edit, not mathematics.\<close>

subsection \<open>(9) The \<open>OT\<close>-membership slots of \<section>8.1 and \<section>8.3, now unblocked\<close>

text \<open>Both the \<section>8.1 (condition (I)) and the \<section>8.3 (condition (II)) exchange
  propositions were tracked with an open \<open>OT\<close>-membership slot, waiting on the \<section>8.7
  lemma "\<open>Trans\<close> preserves standard form".  That lemma is now
  @{thm [source] y5_Trans_OT_B}, unconditionally, so the slots close outright ---
  and with them the article's \<section>8.3 statement
  \<open>p_8_3_TransCondII_oper_descend\<close>, which is exactly the descent pillar under
  strictly stronger hypotheses.\<close>

theorem y5_8_1_condI_OT:
  assumes MST: "M \<in> ST_PS" and MP: "M \<in> PT_PS"
    and j1gt: "1 < Lng M - 1" and condI: "transCondI M" and n1: "1 \<le> n"
  shows "Trans M \<in> OT_B" and "Trans ((M::pairseq)[n]) \<in> OT_B"
proof -
  show "Trans M \<in> OT_B" by (rule y5_Trans_OT_B[OF MST])
  have "(M::pairseq)[n] \<in> ST_PS" using MST n1 by (simp add: ST_PS.oper)
  thus "Trans ((M::pairseq)[n]) \<in> OT_B" by (rule y5_Trans_OT_B)
qed

theorem y5_8_3_condII_OT:
  assumes MST: "M \<in> ST_PS" and MP: "M \<in> PT_PS"
    and j1gt: "1 < Lng M - 1" and condII: "transCondII M" and n1: "1 \<le> n"
  shows "Trans M \<in> OT_B" and "Trans ((M::pairseq)[n]) \<in> OT_B"
proof -
  show "Trans M \<in> OT_B" by (rule y5_Trans_OT_B[OF MST])
  have "(M::pairseq)[n] \<in> ST_PS" using MST n1 by (simp add: ST_PS.oper)
  thus "Trans ((M::pairseq)[n]) \<in> OT_B" by (rule y5_Trans_OT_B)
qed

text \<open>The article's \<section>8.3 proposition, verbatim (\<open>p_8_3_TransCondII_oper_descend\<close>).\<close>

theorem y5_8_3_TransCondII_oper_descend:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS" and MP: "M \<in> PT_PS" and n0: "0 < n"
    and j1gt: "1 < Lng M - 1" and condII: "transCondII M"
  shows "lessBT (Trans ((M::pairseq)[n])) (Trans M)"
proof -
  have L: "1 < Lng M" using j1gt by simp
  show ?thesis by (rule y5_Trans_descend[OF MST _ L]) (use n0 in simp)
qed


subsection \<open>Well-definedness holes (footnote audit): \<open>LastStep\<close>'s \<open>Min\<close> is nonempty,
  and \<open>nextAdm\<close>'s \<open>\<exists>!\<close>\<close>

text \<open>HOLE 1 --- the article's footnotes [59]/[61] (\<^file>\<open>../tmp/content.md\<close>, footnote
  block): «この時簡約性と係数の基本性質より \<open>(Br(M)\<^bsub>J\<^sub>1\<^esub>)\<^bsub>0,0\<^esub> \<ge> (Br(M)\<^bsub>J\<^sub>1\<^esub>)\<^bsub>1,0\<^esub>\<close> である»
  and «\<open>J = J\<^sub>1\<close> が条件を満たすため \<open>min\<close> が存在する».  On a \<^emph>\<open>reduced\<close> host the
  coefficient inequality \<open>row-1 \<le> row-0\<close> (@{thm [source] m_6_6_reduced_coeff})
  transports to the head of the last \<open>Br\<close>-block (@{thm [source] vgx_Br_last_head}),
  so in the \<open>else\<close> branch of @{const LastStep} (heads \<^emph>\<open>differ\<close>) the inequality is
  STRICT, and \<open>J\<^sub>1\<close> itself lies in the \<open>Min\<close>-set: the set is nonempty (and, by
  correction A9, finite), so \<open>Min\<close> is not HOL junk.  This discharges the \<open>gt\<close> /
  \<open>guard\<close> side conditions carried by @{thm [source] vgx_LastStep_lt_Lng_Br},
  @{thm [source] vgx_LastStep_lt_of_guard} and
  @{thm [source] ot_finRc_LastStep_guard_bounded_lt}.\<close>

lemma y3_Br_last_head_coeff:
  \<comment> \<open>footnote [59]: \<open>(Br M\<^bsub>J\<^sub>1\<^esub>)\<^bsub>1,0\<^esub> \<le> (Br M\<^bsub>J\<^sub>1\<^esub>)\<^bsub>0,0\<^esub>\<close> on a reduced mono host.\<close>
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and Mm: "monoT M" and Brne: "Br M \<noteq> []"
  shows "entry (Br M ! (Lng (Br M) - 1)) 1 0 \<le> entry (Br M ! (Lng (Br M) - 1)) 0 0"
proof -
  let ?J1 = "Lng (Br M) - 1"
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have MP: "M \<in> PT_PS" using MT Mm by (simp add: PT_PS_def)
  have J1Br: "?J1 < Lng (Br M)" using Brne by (cases "Br M") auto
  have fnlt: "FirstNodes M ! ?J1 < Lng M" by (rule a1_FN_lt[OF MP J1Br])
  have h0: "entry (Br M ! ?J1) 0 0 = entry M 0 (FirstNodes M ! ?J1)"
    by (rule vgx_Br_last_head[OF MP Brne])
  have h1: "entry (Br M ! ?J1) 1 0 = entry M 1 (FirstNodes M ! ?J1)"
    by (rule vgx_Br_last_head[OF MP Brne])
  have "entry M 1 (FirstNodes M ! ?J1) \<le> entry M 0 (FirstNodes M ! ?J1)"
    by (rule m_6_6_reduced_coeff[OF MR fnlt])
  thus ?thesis using h0 h1 by simp
qed

lemma y3_LastStep_gt:
  \<comment> \<open>in the \<open>else\<close> branch (heads differ) the coefficient inequality is STRICT.\<close>
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and Mm: "monoT M" and Brne: "Br M \<noteq> []"
    and neq: "entry (Br M ! (Lng (Br M) - 1)) 0 0 \<noteq> entry (Br M ! (Lng (Br M) - 1)) 1 0"
  shows "entry (Br M ! (Lng (Br M) - 1)) 1 0 < entry (Br M ! (Lng (Br M) - 1)) 0 0"
  using y3_Br_last_head_coeff[OF MR Mm Brne] neq by simp

lemma y3_LastStep_J1_mem:
  \<comment> \<open>footnote [61]: \<open>J = J\<^sub>1\<close> satisfies the condition, so the \<open>Min\<close>-set is nonempty.\<close>
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and Mm: "monoT M" and Brne: "Br M \<noteq> []"
    and neq: "entry (Br M ! (Lng (Br M) - 1)) 0 0 \<noteq> entry (Br M ! (Lng (Br M) - 1)) 1 0"
  shows "(Lng (Br M) - 1)
           \<in> {J. J < Lng (Br M)
                 \<and> entry (Br M ! (Lng (Br M) - 1)) 0 0 = entry (Br M ! J) 0 0
                 \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}"
proof -
  have J1Br: "Lng (Br M) - 1 < Lng (Br M)" using Brne by (cases "Br M") auto
  show ?thesis using J1Br y3_LastStep_gt[OF MR Mm Brne neq] by simp
qed

lemma y3_LastStep_set_nonempty:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and Mm: "monoT M" and Brne: "Br M \<noteq> []"
    and neq: "entry (Br M ! (Lng (Br M) - 1)) 0 0 \<noteq> entry (Br M ! (Lng (Br M) - 1)) 1 0"
  shows "{J. J < Lng (Br M)
             \<and> entry (Br M ! (Lng (Br M) - 1)) 0 0 = entry (Br M ! J) 0 0
             \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0} \<noteq> {}"
  using y3_LastStep_J1_mem[OF MR Mm Brne neq] by blast

text \<open>Guard-free drop-in for @{thm [source] ot_finRc_LastStep_guard_bounded_lt}: in the
  \<open>else\<close> branch, reducedness alone (no \<open>gt\<close>, no \<open>guard\<close>, no \<open>fin\<close>) puts the \<open>Min\<close> in range.\<close>

lemma y3_LastStep_bounded_lt_neq:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and Mm: "monoT M" and Brne: "Br M \<noteq> []"
    and neq: "entry (Br M ! (Lng (Br M) - 1)) 0 0 \<noteq> entry (Br M ! (Lng (Br M) - 1)) 1 0"
  shows "Min {J. J < Lng (Br M)
                 \<and> entry (Br M ! (Lng (Br M) - 1)) 0 0 = entry (Br M ! J) 0 0
                 \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}
         < Lng (Br M)"
  by (rule ot_finRc_LastStep_bounded_lt[OF Brne y3_LastStep_gt[OF MR Mm Brne neq]])

text \<open>Guard-free drop-in for @{thm [source] vgx_LastStep_lt_Lng_Br} and
  @{thm [source] vgx_LastStep_lt_of_guard}: on a reduced mono host with \<open>Br M \<noteq> []\<close>,
  \<open>LastStep M < Lng (Br M)\<close> --- \<^bold>\<open>unconditionally\<close> (both branches of the definition).\<close>

lemma y3_LastStep_lt_Lng_Br:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and Mm: "monoT M" and Brne: "Br M \<noteq> []"
  shows "LastStep M < Lng (Br M)"
proof -
  let ?J1 = "Lng (Br M) - 1"
  have J1Br: "?J1 < Lng (Br M)" using Brne by (cases "Br M") auto
  show ?thesis
  proof (cases "entry (Br M ! ?J1) 0 0 = entry (Br M ! ?J1) 1 0")
    case True
    hence "LastStep M = ?J1" using Brne unfolding LastStep_def Let_def by simp
    thus ?thesis using J1Br by simp
  next
    case False
    have gt: "entry (Br M ! ?J1) 1 0 < entry (Br M ! ?J1) 0 0"
      by (rule y3_LastStep_gt[OF MR Mm Brne False])
    have LS: "LastStep M = Min {J. J < Lng (Br M)
                                   \<and> entry (Br M ! ?J1) 0 0 = entry (Br M ! J) 0 0
                                   \<and> entry (Br M ! J) 1 0 < entry (Br M ! J) 0 0}"
      by (rule vgx_LastStep_elsecase[OF Brne gt])
    show ?thesis using LS y3_LastStep_bounded_lt_neq[OF MR Mm Brne False] by simp
  qed
qed

lemma y3_LastStep_lt_Lng_Br_DT:
  \<comment> \<open>the declared domain of @{const LastStep} is \<open>DT\<^bsub>PS\<^esub>\<close>, where the hypotheses are free.\<close>
  fixes M :: pairseq
  assumes MD: "M \<in> DT_PS" and Brne: "Br M \<noteq> []"
  shows "LastStep M < Lng (Br M)"
proof -
  have MR: "M \<in> RT_PS" and Mm: "monoT M" using MD by (simp_all add: DT_PS_def)
  show ?thesis by (rule y3_LastStep_lt_Lng_Br[OF MR Mm Brne])
qed

text \<open>HOLE 2 --- \<open>\<exists>!j\<^sub>0. nextAdm M 0 j\<^sub>0 (Lng M - 1)\<close>, assumed as \<open>uniq\<close> by
  @{thm [source] m_7_4_Trans_nextAdm} / @{thm [source] m_7_4_Mark_nextAdm} and used by the
  \<open>THE\<close>-binders of \<section>7.4.  UNIQUENESS is unconditional (the maximality clause of
  @{const nextAdm} rules out a second, larger witness).  EXISTENCE holds for a
  \<open>monoT\<close> host of length \<open>> 1\<close>: column \<open>0\<close> is always admissible
  (@{thm [source] adm_zero}) and, by \<open>monoT\<close>, a row-0 ancestor of \<open>Lng M - 1\<close>; the
  \<^emph>\<open>largest\<close> such column is the NextAdm-parent.\<close>

lemma y3_nextAdm_unique:
  fixes M :: pairseq
  assumes A: "nextAdm M i a j1" and B: "nextAdm M i b j1"
  shows "a = b"
proof -
  have Aa: "a < j1" and Amax: "\<And>j. a < j \<Longrightarrow> j < j1 \<Longrightarrow> \<not> leR M i j j1 \<or> \<not> adm M j"
    using A unfolding nextAdm_def by blast+
  have Bb: "b < j1" and Ble: "leR M i b j1" and Badm: "adm M b"
    and Bmax: "\<And>j. b < j \<Longrightarrow> j < j1 \<Longrightarrow> \<not> leR M i j j1 \<or> \<not> adm M j"
    using B unfolding nextAdm_def by blast+
  have Ale: "leR M i a j1" and Aadm: "adm M a" using A unfolding nextAdm_def by blast+
  show ?thesis
  proof (rule ccontr)
    assume ne: "a \<noteq> b"
    show False
    proof (cases "a < b")
      case True
      show False using Amax[OF True Bb] Ble Badm by simp
    next
      case False
      hence ba: "b < a" using ne by simp
      show False using Bmax[OF ba Aa] Ale Aadm by simp
    qed
  qed
qed

lemma y3_nextAdm_ex:
  fixes M :: pairseq
  assumes Mm: "monoT M" and L: "1 < Lng M"
  shows "\<exists>j0. nextAdm M 0 j0 (Lng M - 1)"
proof -
  let ?j1 = "Lng M - 1"
  let ?A = "{j. j < ?j1 \<and> leR M 0 j ?j1 \<and> adm M j}"
  have j1pos: "0 < ?j1" using L by simp
  have le00: "leR M 0 0 ?j1" using Mm by (simp add: monoT_def)
  have zeroA: "0 \<in> ?A" using j1pos le00 adm_zero by simp
  hence ne: "?A \<noteq> {}" by blast
  have fin: "finite ?A" by (rule finite_subset[of _ "{..< ?j1}"]) auto
  have mem: "Max ?A \<in> ?A" by (rule Max_in[OF fin ne])
  have P1: "Max ?A < ?j1" and P2: "leR M 0 (Max ?A) ?j1" and P3: "adm M (Max ?A)"
    using mem by simp_all
  have maxcl: "\<forall>j. Max ?A < j \<and> j < ?j1 \<longrightarrow> \<not> leR M 0 j ?j1 \<or> \<not> adm M j"
  proof (intro allI impI)
    fix j assume H: "Max ?A < j \<and> j < ?j1"
    show "\<not> leR M 0 j ?j1 \<or> \<not> adm M j"
    proof (rule ccontr)
      assume "\<not> (\<not> leR M 0 j ?j1 \<or> \<not> adm M j)"
      hence jle: "leR M 0 j ?j1" and jadm: "adm M j" by auto
      have jA: "j \<in> ?A" using H jle jadm by simp
      have "j \<le> Max ?A" by (rule Max_ge[OF fin jA])
      thus False using H by simp
    qed
  qed
  have "nextAdm M 0 (Max ?A) ?j1"
    using P1 P2 P3 maxcl unfolding nextAdm_def by blast
  thus ?thesis by blast
qed

lemma y3_nextAdm_ex1:
  fixes M :: pairseq
  assumes Mm: "monoT M" and L: "1 < Lng M"
  shows "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
  using y3_nextAdm_ex[OF Mm L] y3_nextAdm_unique by blast

text \<open>\<open>uniq\<close>-free restatements of the two \<section>7.4 consumers.\<close>

lemma y3_7_4_Trans_nextAdm:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and Mm: "monoT M" and L: "1 < Lng M"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M))
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Trans M)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
  by (rule m_7_4_Trans_nextAdm[OF MR y3_nextAdm_ex1[OF Mm L]])

lemma y3_7_4_Mark_nextAdm:
  fixes M :: pairseq
  assumes MR: "M \<in> RT_PS" and Mm: "monoT M" and L: "1 < Lng M"
    and jM: "(M, j) \<in> Marked"
    and jle: "leR M 0 j (THE j0. nextAdm M 0 j0 (Lng M - 1))"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) j)
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Mark M j)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
  by (rule m_7_4_Mark_nextAdm[OF MR y3_nextAdm_ex1[OF Mm L] jM jle])

ML \<open>
  fun sorry_deps th =
    let
      val all_sorries =
        ["pss_paper.p_5_1_parent_exists_1", "pss_paper.p_5_1_parent_exists_2", "pss_paper.p_5_1_parent_exists_3", "pss_paper.p_5_1_parent_exists_4", "pss_paper.p_5_1_parent_basic_1", "pss_paper.p_5_1_parent_basic_2", "pss_paper.p_5_1_ancestor_basic_1", "pss_paper.p_5_1_ancestor_basic_2", "pss_paper.p_5_1_ancestor_tree_1", "pss_paper.p_5_1_ancestor_tree_2", "pss_paper.p_5_3_pred_is_oper1", "pss_paper.p_5_4_F_oper_dom", "pss_paper.p_5_4_F_oper_val", "pss_paper.p_6_1_le_IncrFirst_inv", "pss_paper.p_6_2_multi_crit_12", "pss_paper.p_6_2_multi_crit_23", "pss_paper.p_6_2_mono_prefix", "pss_paper.p_6_2_mono_ancestor_slice", "pss_paper.p_6_2_P_IncrFirst", "pss_paper.p_6_2_P_components_1", "pss_paper.p_6_2_P_components_2", "pss_paper.p_6_2_P_additive", "pss_paper.p_6_2_P_oper_1", "pss_paper.p_6_2_P_oper_2", "pss_paper.p_6_2_nonmulti_oper_1", "pss_paper.p_6_2_nonmulti_oper_2", "pss_paper.p_6_3_adm_slice", "pss_paper.p_6_3_admof_slice", "pss_paper.p_6_3_marked_slice", "pss_paper.p_6_4_P_IdxSum", "pss_paper.p_6_4_P_IdxSum_char_1", "pss_paper.p_6_4_P_IdxSum_char_2", "pss_paper.p_6_4_P_leftend_mono", "pss_paper.p_6_4_mono_slice_next", "pss_paper.p_6_4_FirstNodes_TrMax_Joints", "pss_paper.p_6_4_FirstNodes_Joints_mono", "pss_paper.p_6_4_mono_slice", "pss_paper.p_6_5_Red_welldef", "pss_paper.p_6_5_Red_IncrFirst", "pss_paper.p_6_5_Lng_Red", "pss_paper.p_6_5_Red_zeroT", "pss_paper.p_6_5_Red_le", "pss_paper.p_6_5_Red_monoT", "pss_paper.p_6_5_P_Red", "pss_paper.p_6_5_monoT_Red", "pss_paper.p_6_5_Red_idem", "pss_paper.p_6_5_Red_Pred", "pss_paper.p_6_5_Red_oper", "pss_paper.p_6_5_Red_adm", "pss_paper.p_6_5_admof_Red", "pss_paper.p_6_5_Red_marked", "pss_paper.p_6_6_reduced_slice", "pss_paper.p_6_6_P_reduced", "pss_paper.p_6_6_reduced_oper", "pss_paper.p_6_6_reduced_iff_cond", "pss_paper.p_6_6_Red_leftend_1", "pss_paper.p_6_6_Red_leftend_2", "pss_paper.p_6_6_reduced_coeff", "pss_paper.p_6_6_reduced_leftend", "pss_paper.p_6_6_condAB_coeff", "pss_paper.p_6_6_ancestor_slice_Red_IncrFirst", "pss_paper.p_6_6_oneColumn", "pss_paper.p_6_7_standard_reduced", "pss_paper.p_6_7_ST_eq_Union_SkT", "pss_paper.p_6_7_standard_P_components", "pss_paper.p_6_7_standard_prefix", "pss_paper.p_6_8_standard_slice_Br_descending", "pss_paper.p_6_8_standard_P_descending", "pss_paper.p_7_1_lessBT_linord", "pss_paper.p_7_1_term_components", "pss_paper.buc1_2_2_OT_B_wf", "pss_paper.buc1_3_2a_fseq_lt", "pss_paper.buc1_3_2_OT_B_closed", "pss_paper.p_7_1_paren_balance", "pss_paper.p_7_2_scb_replaceable", "pss_paper.p_7_2_scb_compose", "pss_paper.p_7_2_scb_triviality", "pss_paper.p_7_2_scb_unique", "pss_paper.p_7_2_add_scb", "pss_paper.p_7_2_scb_fseq", "pss_paper.p_7_2_RightNodes_subexpr", "pss_paper.p_7_3_twoColumn", "pss_paper.p_7_3_Trans_IncrFirst_Red", "pss_paper.p_7_3_Mark_IncrFirst_Red", "pss_paper.p_7_3_Trans_zeroT", "pss_paper.p_7_3_c1_c2", "pss_paper.p_7_3_Pred_Trans_descend", "pss_paper.p_7_3_Mark_rightmost1", "pss_paper.p_7_3_Trans_monoT", "pss_paper.p_7_4_Adm_nextAdm", "pss_paper.p_7_4_Trans_nextAdm", "pss_paper.p_7_4_Mark_nextAdm", "pss_paper.p_7_4_Trans_Mark_Pred", "pss_paper.p_7_4_Mark_Trans_repr", "pss_paper.p_7_4_Trans_Mark_seg", "pss_paper.p_7_4_RightNodes_Mark", "pss_paper.p_7_4_RightAnces_RightNodes", "pss_paper.p_7_4_RightAnces_zeroT", "pss_paper.p_8_2_standard_slice_Red_strongmono", "pss_paper.p_8_2_strongmono_slice", "pss_paper.p_8_2_subexpr_component_Pred", "pss_paper.p_8_2_subexpr_component_strongmono", "pss_paper.p_8_2_condV_rightmost_parent", "pss_paper.p_8_2_condV_terminal_slice_Trans", "pss_paper.p_8_2_condIIIV_terminal_slice_Trans", "pss_paper.p_8_1_diagSeq_Trans", "pss_paper.p_8_1_Pred_diagSeq_Trans", "pss_paper.p_8_1_condI_III_c1_around", "pss_paper.p_8_1_Trans_fseq_condI", "pss_paper.p_8_3_kind0_base_ineq", "pss_paper.p_8_3_kind0_branch_rule", "pss_paper.p_8_3_kind0_base_basepoint", "pss_paper.p_8_3_TransCondII_oper_descend", "pss_paper.p_8_4_Trans_oper_exchange", "pss_paper.p_8_4_rightmost_nonadm_ancestor", "pss_paper.p_8_4_oper_basic", "pss_paper.p_8_5_Trans_oper_exchange", "pss_paper.p_8_5_Joints_FirstNodes_basic", "pss_paper.p_8_6_const2nd_Trans", "pss_paper.p_8_6_diagSeq_Trans_oper", "pss_paper.p_8_6_trailing_principal_annihilable", "pss_paper.p_8_6_Trans_fseq_condVI", "pss_paper.p_8_7_const00_Trans", "pss_paper.p_8_7_fseq_descend", "pss_paper.p_8_7_OT_scb_recursive", "pss_paper.p_8_7_OT_dom_hereditary", "pss_paper.p_8_7_OT_tail_annihilable", "pss_paper.p_8_7_Pred_oper0", "pss_paper.p_8_7_OT_examples", "pss_paper.p_8_7_Trans_preserves_OT", "pss_paper.p_8_7_termination"];
      val ds =
        Proofterm.fold_body_thms
          (fn {thm_name, ...} => fn acc => insert (op =) (Thm_Name.short thm_name) acc)
          [Thm.proof_body_of th] [];
    in filter (member (op =) all_sorries) ds end;

  fun assert_clean (n, th) =
    (case sorry_deps th of
       [] => ()
     | bad => error ("AUDIT FAILED: " ^ n ^ " depends on sorry: " ^ commas bad));

  fun assert_only_stale (n, th) =
    (case sorry_deps th of
       ["pss_paper.buc1_3_2a_fseq_lt"] => ()
     | bad => error ("AUDIT FAILED: " ^ n ^ " sorry-deps = [" ^ commas bad ^
                     "] (expected exactly the stale buc1_3_2a_fseq_lt)"));

  val _ = map assert_clean
    [("y4_buc1_2_2_OT_B_wf", @{thm y4_buc1_2_2_OT_B_wf}),
     ("y4_wf_RPrel",         @{thm y4_wf_RPrel}),
     ("y4_cof0",             @{thm y4_cof0}),
     ("y4_bwl_cof",          @{thm y4_bwl_cof}),
     ("y4_PSS_acc_of_KK",    @{thm y4_PSS_acc_of_KK}),
     ("y4_PSS_wf_of_KK",     @{thm y4_PSS_wf_of_KK}),
     ("oi10_census_KK",      @{thm oi10_census_KK(1)}),
     \<comment> \<open>r72: the residual KK is DISCHARGED --- these are UNCONDITIONAL\<close>
     ("ox12_KK_free",        @{thm ox12_KK_free}),
     ("oi12_census(1)",      @{thm oi12_census(1)}),
     ("oi12_census(2)",      @{thm oi12_census(2)}),
     ("y5_Trans_OT_B",       @{thm y5_Trans_OT_B}),
     ("y5_Trans_descend",    @{thm y5_Trans_descend}),
     ("y5_PSS_acc",          @{thm y5_PSS_acc}),
     ("y5_PSS_wf",           @{thm y5_PSS_wf}),
     \<comment> \<open>r72: the ARTICLE'S OWN termination statement, p_8_7_termination\<close>
     ("y5_Fdom",             @{thm y5_Fdom}),
     \<comment> \<open>r72: the \<section>8.1 / \<section>8.3 OT-membership slots\<close>
     ("y5_8_1_condI_OT",     @{thm y5_8_1_condI_OT(2)}),
     ("y5_8_3_condII_OT",    @{thm y5_8_3_condII_OT(2)}),
     ("y5_8_3_TransCondII_oper_descend", @{thm y5_8_3_TransCondII_oper_descend})];

  \<comment> \<open>r72: assert the termination theorems carry NO free hypothesis left ---
      \<open>y5_PSS_wf\<close> must be a closed statement (no meta-premises, no schematics).\<close>
  val _ =
    let
      val th = @{thm y5_PSS_wf};
      val t  = Thm.prop_of th;
    in
      if Thm.nprems_of th = 0 andalso null (Thm.hyps_of th)
         andalso null (Term.add_frees t []) andalso null (Term.add_vars t [])
      then () else error "AUDIT FAILED: y5_PSS_wf is not a closed hypothesis-free statement"
    end;
\<close>
end
