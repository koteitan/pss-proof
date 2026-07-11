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
    by (rule opx_termination_census_v3(1)[OF OTint TVall ordIntC od4_DEEPOT od4_NOBR])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule opx_termination_census_v3(2)[OF OTint TVall ordIntC od4_DEEPOT od4_NOBR])
qed

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
              (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
                 (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
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
  have base1: "lessBT ?A0 (d4vx_ins (u1 @ u2) ?ub (v2 @ w1) (Dpt (enat ?ub) 0\<^sub>B))"
  proof (cases "transCondIII M")
    case True
    show ?thesis
      by (rule crx_base1_of_nest[OF MR MPT J1pos T1 True dPq d2q d4c2q inner])
  next
    case False
    hence cIV: "transCondIV M" using branch by blast
    show ?thesis
      by (rule cnv_base1_of_nest[OF MR MPT J1pos T1 cIV dPq d2q d4c2q inner])
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
    and base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))"
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
  \<comment> \<open>towers\<close>
  define X0 where "X0 = Dpt (enat ?ub) 0\<^sub>B"
  define A1 where "A1 = d4vx_ins s0 ?ub b0 ?A0"
  define X1 where "X1 = d4vx_ins s0 ?ub b0 X0"
  define X2 where "X2 = d4vx_ins s0 ?ub b0 X1"
  have X0TB: "X0 \<in> T_B" by (simp add: X0_def T_B_def)
  have A1TB: "A1 \<in> T_B"
    unfolding A1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT A0TB])
  have X1TB: "X1 \<in> T_B"
    unfolding X1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT X0TB])
  have X2TB: "X2 \<in> T_B"
    unfolding X2_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT X1TB])
  have fA1: "flatBT A1 = s0 @ Dsym (enat ?ub) # flatBT ?A0 @ b0"
    unfolding A1_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fX1: "flatBT X1 = s0 @ Dsym (enat ?ub) # flatBT X0 @ b0"
    unfolding X1_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fX2: "flatBT X2 = s0 @ Dsym (enat ?ub) # flatBT X1 @ b0"
    unfolding X2_def by (rule d4vx_ins_flat[OF wrap b0RP])
  \<comment> \<open>orders (interleave at height 1)\<close>
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0[folded X0_def]
              base1[folded X0_def], of 1]
  have ordlo: "leBT X1 A1"
    using IL by (simp add: X1_def A1_def X0_def)
  have ordhi: "leBT A1 X2"
    using IL by (simp add: X1_def X2_def A1_def X0_def)
  \<comment> \<open>the one-block facts\<close>
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
  have setle: "\<And>u. b1x_setle (GBT u A1) (insert X1 (GBT u X1))"
    unfolding A1_def X1_def X0_def
    by (rule SETLE1[OF NST NPT hp j1gt branch ihOT b0RP inner])
  \<comment> \<open>fseq closed forms of the donors\<close>
  have fseq: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate n (s0 @ [Dsym (enat ?ub)]))
           @ [Dsym (enat ?ub)] @ [Zsym] @ concat (replicate n b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbodyH bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 X0 n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT X0 @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fseqX: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 X0 n) @ b1"
    using fseq Xflat by (simp add: X0_def)
  \<comment> \<open>donor OT-ness ([Buc1] closure on the slot's own IH)\<close>
  have donOT: "\<And>n. isOT_BT (operB (Trans N) (numBT n))"
    using e4x_OT_B_operB_numBT[OF ihOT] by (simp add: OT_B_def OT_def)
  \<comment> \<open>index bookkeeping\<close>
  obtain k where mk: "m = Suc k" using mgt by (cases m) auto
  have k1n: "1 \<le> k" using mgt mk by simp
  have mnm: "flatBT (Trans ((N::pairseq)[m]))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 ?A0 k) @ b1"
    using mn mgt mk by simp
  \<comment> \<open>the transport, one application per index regime\<close>
  have isot: "isOT_BT (Trans ((N::pairseq)[m]))"
  proof (cases "k = 1")
    case True
    \<comment> \<open>hole = the kind-1 position itself, head \<open>e\<^sub>3\<close>, cores \<open>(X\<^sub>1, A\<^sub>1, X\<^sub>2)\<close>\<close>
    have fA1c: "flatBT (d4vx_core s0 ?ub b0 ?A0 k) = flatBT A1"
      using True by (simp add: A1_def)
    have ourflat: "flatBT (Trans ((N::pairseq)[m]))
        = s1 @ flatBT (Dpt (enat ?e3) A1) @ b1"
      using mnm fA1c by simp
    have loflat: "flatBT (operB (Trans N) (numBT 1))
        = s1 @ flatBT (Dpt (enat ?e3) X1) @ b1"
      using fseqX[of 1] by (simp add: X1_def)
    have hiflat: "flatBT (operB (Trans N) (numBT 2))
        = s1 @ flatBT (Dpt (enat ?e3) X2) @ b1"
    proof -
      have "d4vx_core s0 ?ub b0 X0 2 = X2"
        by (simp add: numeral_2_eq_2 X1_def X2_def)
      thus ?thesis using fseqX[of 2] by simp
    qed
    have ourdec: "scb_decomp (Trans ((N::pairseq)[m])) s1
                    (flatBT (Dpt (enat ?e3) A1)) b1"
      unfolding scb_decomp_def
      using ourflat b1RP isPTB_str_Dpt[of "enat ?e3" A1] A1TB
      by (simp add: T_B_def)
    have lodec: "scb_decomp (operB (Trans N) (numBT 1)) s1
                    (flatBT (Dpt (enat ?e3) X1)) b1"
      unfolding scb_decomp_def
      using loflat b1RP isPTB_str_Dpt[of "enat ?e3" X1] X1TB
      by (simp add: T_B_def)
    have hidec: "scb_decomp (operB (Trans N) (numBT 2)) s1
                    (flatBT (Dpt (enat ?e3) X2)) b1"
      unfolding scb_decomp_def
      using hiflat b1RP isPTB_str_Dpt[of "enat ?e3" X2] X2TB
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
    \<comment> \<open>hole = \<open>k - 1\<close> blocks deep, head \<open>ub\<close>, cores \<open>(X\<^sub>1, A\<^sub>1, X\<^sub>2)\<close>\<close>
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
    \<comment> \<open>lo donor at the deep hole\<close>
    have loflat: "flatBT (operB (Trans N) (numBT k))
        = ?S @ flatBT (Dpt (enat ?ub) X1) @ ?B"
      using fseqX[of k] Xflat[of k] crepA crepB fX1 by simp
    \<comment> \<open>hi donor at the deep hole\<close>
    have crepA2: "concat (replicate (Suc k) ?blk)
        = concat (replicate k2 ?blk) @ s0 @ [Dsym (enat ?ub)]
          @ s0 @ [Dsym (enat ?ub)] @ s0 @ [Dsym (enat ?ub)]"
      using kk by (simp add: s85b_crep_comm_snoc s85b_crep_snoc s85b_crep_comm)
    have crepB2: "concat (replicate (Suc k) b0)
        = b0 @ b0 @ concat (replicate (Suc k2) b0)"
      using kk by simp
    have hiflat: "flatBT (operB (Trans N) (numBT (Suc k)))
        = ?S @ flatBT (Dpt (enat ?ub) X2) @ ?B"
      using fseqX[of "Suc k"] Xflat[of "Suc k"] crepA2 crepB2 fX2 fX1 by simp
    have ourdec: "scb_decomp (Trans ((N::pairseq)[m])) ?S
                    (flatBT (Dpt (enat ?ub) A1)) ?B"
      unfolding scb_decomp_def
      using ourflat BRP isPTB_str_Dpt[of "enat ?ub" A1] A1TB
      by (simp add: T_B_def)
    have lodec: "scb_decomp (operB (Trans N) (numBT k)) ?S
                    (flatBT (Dpt (enat ?ub) X1)) ?B"
      unfolding scb_decomp_def
      using loflat BRP isPTB_str_Dpt[of "enat ?ub" X1] X1TB
      by (simp add: T_B_def)
    have hidec: "scb_decomp (operB (Trans N) (numBT (Suc k))) ?S
                    (flatBT (Dpt (enat ?ub) X2)) ?B"
      unfolding scb_decomp_def
      using hiflat BRP isPTB_str_Dpt[of "enat ?ub" X2] X2TB
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
          oi4_Lpv DEEPOT NOBR FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oc4_termination_census_master_v2(2)[OF otIII otIV oi4_PredNp
          oi4_Lpv DEEPOT NOBR FINRC])
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
        TVall NST mu ihOT mgt NPred])


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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                     (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
    and NEWOT: "\<And>k. isOT_BP (DB (enat (entry M 1 (s84x_jm3 M)))
                    (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0 (transT2 M) k))"
    and SETLE: "\<And>k u. b1x_setle
        (GBT u (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0 (transT2 M) k))
        (insert (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                  (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) k)
                (GBT u (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                          (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) k)))"
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
  have X0TB: "?X0 \<in> T_B" by (simp add: T_B_def)
  \<comment> \<open>tower \<open>T\<^bsub>B\<^esub>\<close>-membership\<close>
  have ATB: "\<And>k. d4vx_core s0 ?ub b0 (transT2 M) k \<in> T_B"
    by (rule oi5_d4vx_core_TB[OF wrap b0RP bodyT t2TB])
  have WTB: "\<And>k. d4vx_core s0 ?ub b0 ?X0 k \<in> T_B"
    by (rule oi5_d4vx_core_TB[OF wrap b0RP bodyT X0TB])
  \<comment> \<open>donor closed forms and flats\<close>
  have fseq: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate n (s0 @ [Dsym (enat ?ub)]))
           @ [Dsym (enat ?ub)] @ [Zsym] @ concat (replicate n b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbody bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 ?X0 n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT ?X0 @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fWn: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 n)) @ b1"
    using fseq Xflat by simp
  \<comment> \<open>index bookkeeping\<close>
  obtain k where mk: "m = Suc k" using mgt by (cases m) auto
  have k1n: "1 \<le> k" using mgt mk by simp
  have Sk: "Suc (m - 1) = m" using mgt by simp
  have fMm: "flatBT (Trans ((M::pairseq)[m]))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 (transT2 M) (m - 1))) @ b1"
    using mnform[of m] mgt by simp
  \<comment> \<open>the three aligned scb-decompositions at \<open>(s\<^sub>1, b\<^sub>1)\<close>, cores at head \<open>e\<^sub>3\<close>\<close>
  let ?A = "d4vx_core s0 ?ub b0 (transT2 M) (m - 1)"
  let ?WL = "d4vx_core s0 ?ub b0 ?X0 (m - 1)"
  let ?WH = "d4vx_core s0 ?ub b0 ?X0 m"
  have ourdec: "scb_decomp (Trans ((M::pairseq)[m])) s1
                  (flatBT (Dpt (enat ?e3) ?A)) b1"
    unfolding scb_decomp_def
    using fMm b1RP isPTB_str_Dpt[of "enat ?e3" ?A] ATB by (simp add: T_B_def)
  have lodec: "scb_decomp (operB (Trans M) (numBT (m - 1))) s1
                  (flatBT (Dpt (enat ?e3) ?WL)) b1"
    unfolding scb_decomp_def
    using fWn[of "m - 1"] b1RP isPTB_str_Dpt[of "enat ?e3" ?WL] WTB
    by (simp add: T_B_def)
  have hidec: "scb_decomp (operB (Trans M) (numBT m)) s1
                  (flatBT (Dpt (enat ?e3) ?WH)) b1"
    unfolding scb_decomp_def
    using fWn[of m] b1RP isPTB_str_Dpt[of "enat ?e3" ?WH] WTB
    by (simp add: T_B_def)
  \<comment> \<open>donor OT-ness ([Buc1] 3.2 closure on the slot's own IH)\<close>
  have loOT: "isOT_BT (operB (Trans M) (numBT (m - 1)))"
    using e4x_OT_B_operB_numBT[OF ihOT, of "m - 1"] by (simp add: OT_B_def OT_def)
  have hiOT: "isOT_BT (operB (Trans M) (numBT m))"
    using e4x_OT_B_operB_numBT[OF ihOT, of m] by (simp add: OT_B_def OT_def)
  \<comment> \<open>interleave orders \<open>W\<^bsub>m-1\<^esub> < A\<^bsub>m-1\<^esub> < W\<^bsub>m\<^esub>\<close>\<close>
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0 base1, of "m - 1"]
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
                      (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) k)
                    (GBT u (d4vx_core s0 (entry M 1 (Lng M - 1) - 1) b0
                              (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B) k)))"
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
         (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
    by (rule c4dx_condIV_base1[OF MR MPT J1pos T1 cIV inner])
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
    and base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))"
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
  \<comment> \<open>towers\<close>
  define X0 where "X0 = Dpt (enat ?ub) 0\<^sub>B"
  define A1 where "A1 = d4vx_ins s0 ?ub b0 ?A0"
  define X1 where "X1 = d4vx_ins s0 ?ub b0 X0"
  define X2 where "X2 = d4vx_ins s0 ?ub b0 X1"
  have X0TB: "X0 \<in> T_B" by (simp add: X0_def T_B_def)
  have A1TB: "A1 \<in> T_B"
    unfolding A1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT A0TB])
  have X1TB: "X1 \<in> T_B"
    unfolding X1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT X0TB])
  have X2TB: "X2 \<in> T_B"
    unfolding X2_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT X1TB])
  have fA1: "flatBT A1 = s0 @ Dsym (enat ?ub) # flatBT ?A0 @ b0"
    unfolding A1_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fX1: "flatBT X1 = s0 @ Dsym (enat ?ub) # flatBT X0 @ b0"
    unfolding X1_def by (rule d4vx_ins_flat[OF wrap b0RP])
  have fX2: "flatBT X2 = s0 @ Dsym (enat ?ub) # flatBT X1 @ b0"
    unfolding X2_def by (rule d4vx_ins_flat[OF wrap b0RP])
  \<comment> \<open>orders (interleave at height 1)\<close>
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0[folded X0_def]
              base1[folded X0_def], of 1]
  have ordlo: "leBT X1 A1"
    using IL by (simp add: X1_def A1_def X0_def)
  have ordhi: "leBT A1 X2"
    using IL by (simp add: X1_def X2_def A1_def X0_def)
  \<comment> \<open>the one-block facts\<close>
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
  have setle: "\<And>u. b1x_setle (GBT u A1) (insert X1 (GBT u X1))"
    unfolding A1_def X1_def X0_def
    by (rule SETLE1[OF NST NPT hp j1gt branch ihOT b0RP inner ltJ])
  \<comment> \<open>fseq closed forms of the donors\<close>
  have fseq: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate n (s0 @ [Dsym (enat ?ub)]))
           @ [Dsym (enat ?ub)] @ [Zsym] @ concat (replicate n b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbodyH bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 X0 n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT X0 @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fseqX: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 X0 n) @ b1"
    using fseq Xflat by (simp add: X0_def)
  \<comment> \<open>donor OT-ness ([Buc1] closure on the slot's own IH)\<close>
  have donOT: "\<And>n. isOT_BT (operB (Trans N) (numBT n))"
    using e4x_OT_B_operB_numBT[OF ihOT] by (simp add: OT_B_def OT_def)
  \<comment> \<open>index bookkeeping\<close>
  obtain k where mk: "m = Suc k" using mgt by (cases m) auto
  have k1n: "1 \<le> k" using mgt mk by simp
  have mnm: "flatBT (Trans ((N::pairseq)[m]))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 ?A0 k) @ b1"
    using mn mgt mk by simp
  \<comment> \<open>the transport, one application per index regime\<close>
  have isot: "isOT_BT (Trans ((N::pairseq)[m]))"
  proof (cases "k = 1")
    case True
    \<comment> \<open>hole = the kind-1 position itself, head \<open>e\<^sub>3\<close>, cores \<open>(X\<^sub>1, A\<^sub>1, X\<^sub>2)\<close>\<close>
    have fA1c: "flatBT (d4vx_core s0 ?ub b0 ?A0 k) = flatBT A1"
      using True by (simp add: A1_def)
    have ourflat: "flatBT (Trans ((N::pairseq)[m]))
        = s1 @ flatBT (Dpt (enat ?e3) A1) @ b1"
      using mnm fA1c by simp
    have loflat: "flatBT (operB (Trans N) (numBT 1))
        = s1 @ flatBT (Dpt (enat ?e3) X1) @ b1"
      using fseqX[of 1] by (simp add: X1_def)
    have hiflat: "flatBT (operB (Trans N) (numBT 2))
        = s1 @ flatBT (Dpt (enat ?e3) X2) @ b1"
    proof -
      have "d4vx_core s0 ?ub b0 X0 2 = X2"
        by (simp add: numeral_2_eq_2 X1_def X2_def)
      thus ?thesis using fseqX[of 2] by simp
    qed
    have ourdec: "scb_decomp (Trans ((N::pairseq)[m])) s1
                    (flatBT (Dpt (enat ?e3) A1)) b1"
      unfolding scb_decomp_def
      using ourflat b1RP isPTB_str_Dpt[of "enat ?e3" A1] A1TB
      by (simp add: T_B_def)
    have lodec: "scb_decomp (operB (Trans N) (numBT 1)) s1
                    (flatBT (Dpt (enat ?e3) X1)) b1"
      unfolding scb_decomp_def
      using loflat b1RP isPTB_str_Dpt[of "enat ?e3" X1] X1TB
      by (simp add: T_B_def)
    have hidec: "scb_decomp (operB (Trans N) (numBT 2)) s1
                    (flatBT (Dpt (enat ?e3) X2)) b1"
      unfolding scb_decomp_def
      using hiflat b1RP isPTB_str_Dpt[of "enat ?e3" X2] X2TB
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
    \<comment> \<open>hole = \<open>k - 1\<close> blocks deep, head \<open>ub\<close>, cores \<open>(X\<^sub>1, A\<^sub>1, X\<^sub>2)\<close>\<close>
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
    \<comment> \<open>lo donor at the deep hole\<close>
    have loflat: "flatBT (operB (Trans N) (numBT k))
        = ?S @ flatBT (Dpt (enat ?ub) X1) @ ?B"
      using fseqX[of k] Xflat[of k] crepA crepB fX1 by simp
    \<comment> \<open>hi donor at the deep hole\<close>
    have crepA2: "concat (replicate (Suc k) ?blk)
        = concat (replicate k2 ?blk) @ s0 @ [Dsym (enat ?ub)]
          @ s0 @ [Dsym (enat ?ub)] @ s0 @ [Dsym (enat ?ub)]"
      using kk by (simp add: s85b_crep_comm_snoc s85b_crep_snoc s85b_crep_comm)
    have crepB2: "concat (replicate (Suc k) b0)
        = b0 @ b0 @ concat (replicate (Suc k2) b0)"
      using kk by simp
    have hiflat: "flatBT (operB (Trans N) (numBT (Suc k)))
        = ?S @ flatBT (Dpt (enat ?ub) X2) @ ?B"
      using fseqX[of "Suc k"] Xflat[of "Suc k"] crepA2 crepB2 fX2 fX1 by simp
    have ourdec: "scb_decomp (Trans ((N::pairseq)[m])) ?S
                    (flatBT (Dpt (enat ?ub) A1)) ?B"
      unfolding scb_decomp_def
      using ourflat BRP isPTB_str_Dpt[of "enat ?ub" A1] A1TB
      by (simp add: T_B_def)
    have lodec: "scb_decomp (operB (Trans N) (numBT k)) ?S
                    (flatBT (Dpt (enat ?ub) X1)) ?B"
      unfolding scb_decomp_def
      using loflat BRP isPTB_str_Dpt[of "enat ?ub" X1] X1TB
      by (simp add: T_B_def)
    have hidec: "scb_decomp (operB (Trans N) (numBT (Suc k))) ?S
                    (flatBT (Dpt (enat ?ub) X2)) ?B"
      unfolding scb_decomp_def
      using hiflat BRP isPTB_str_Dpt[of "enat ?ub" X2] X2TB
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
          oi4_Lpv od4_DEEPOT od4_NOBR FINRC])
  show "\<forall>M n. M \<in> ST_PS \<longrightarrow> 1 \<le> n \<longrightarrow> 1 < Lng M \<longrightarrow>
           lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule oc4_termination_census_master_v2(2)[OF otIII otIV oi4_PredNp
          oi4_Lpv od4_DEEPOT od4_NOBR FINRC])
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
    and tri0: "b1x_triG (Dpt \<infinity> (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))
                (bpHeadT (Trans (Pred (s84x_N N))))
                (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                   (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))"
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
    and base1: "lessBT ?A0 (d4vx_ins s0p ?ub b0p (Dpt (enat ?ub) 0\<^sub>B))"
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
  \<comment> \<open>towers over the package \<open>(s\<^sub>0,b\<^sub>0)\<close>\<close>
  define X0 where "X0 = Dpt (enat ?ub) 0\<^sub>B"
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
           # concat (replicate n (s0p @ [Dsym (enat ?ub)]))
           @ [Dsym (enat ?ub)] @ [Zsym] @ concat (replicate n b0p)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbodyH bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0p ?ub b0p X0 n)
      = concat (replicate n (s0p @ [Dsym (enat ?ub)]))
        @ flatBT X0 @ concat (replicate n b0p)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fseqX: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0p ?ub b0p X0 n) @ b1"
    using fseq Xflat by (simp add: X0_def)
  have donOTB: "\<And>n. operB (Trans N) (numBT n) \<in> OT_B"
    using e4x_OT_B_operB_numBT[OF ihOT] by simp
  \<comment> \<open>donor cores at the kind-1 hole (head e3): X1 at depth 1, X2 at depth 2\<close>
  have loflat: "flatBT (operB (Trans N) (numBT 1))
      = s1 @ flatBT (Dpt (enat ?e3) X1) @ b1"
    using fseqX[of 1] by (simp add: X1_def)
  have hiflat: "flatBT (operB (Trans N) (numBT 2))
      = s1 @ flatBT (Dpt (enat ?e3) X2) @ b1"
  proof -
    have "d4vx_core s0p ?ub b0p X0 2 = X2"
      by (simp add: numeral_2_eq_2 X1_def X2_def)
    thus ?thesis using fseqX[of 2] by simp
  qed
  have lodec: "scb_decomp (operB (Trans N) (numBT 1)) s1
                  (flatBT (Dpt (enat ?e3) X1)) b1"
    unfolding scb_decomp_def
    using loflat b1RP isPTB_str_Dpt[of "enat ?e3" X1] X1TB
    by (simp add: T_B_def)
  have hidec: "scb_decomp (operB (Trans N) (numBT 2)) s1
                  (flatBT (Dpt (enat ?e3) X2)) b1"
    unfolding scb_decomp_def
    using hiflat b1RP isPTB_str_Dpt[of "enat ?e3" X2] X2TB
    by (simp add: T_B_def)
  \<comment> \<open>donor OT-ness of the principals via the scb-position readoff\<close>
  have loPe: "isOT_BP (DB (enat ?e3) X1)"
  proof -
    have DptTB: "Dpt (enat ?e3) X1 \<in> T_B" using X1TB by (simp add: T_B_def)
    have "Dpt (enat ?e3) X1 \<in> OT"
      by (rule m_8_7_OT_scb_recursive[OF donOTB[of 1] DptTB lodec])
    thus ?thesis by (simp add: OT_def)
  qed
  have hiPe: "isOT_BP (DB (enat ?e3) X2)"
  proof -
    have DptTB: "Dpt (enat ?e3) X2 \<in> T_B" using X2TB by (simp add: T_B_def)
    have "Dpt (enat ?e3) X2 \<in> OT"
      by (rule m_8_7_OT_scb_recursive[OF donOTB[of 2] DptTB hidec])
    thus ?thesis by (simp add: OT_def)
  qed
  have X1OT: "isOT_BT X1" using loPe by simp
  have X2OT: "isOT_BT X2" using hiPe by simp
  \<comment> \<open>base orders and the tri0 in package form\<close>
  have o1: "leBT X0 ?A0" using base0 by (simp add: X0_def)
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
    and base1: "lessBT ?A0 (d4vx_ins s0p ?ub b0p (Dpt (enat ?ub) 0\<^sub>B))"
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
  define X0 where "X0 = Dpt (enat ?ub) 0\<^sub>B"
  define X1 where "X1 = d4vx_ins s0p ?ub b0p X0"
  have X0TB: "X0 \<in> T_B" by (simp add: X0_def T_B_def)
  have X1TB: "X1 \<in> T_B"
    unfolding X1_def by (rule oi5_d4vx_ins_TB[OF wrap b0RP bodyT X0TB])
  \<comment> \<open>donor readoff: isOT_BP (D_e3 X1) from the [Buc1]-closure donor operB(numBT 1)\<close>
  have fseq: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate n (s0p @ [Dsym (enat ?ub)]))
           @ [Dsym (enat ?ub)] @ [Zsym] @ concat (replicate n b0p)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbodyH bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0p ?ub b0p X0 n)
      = concat (replicate n (s0p @ [Dsym (enat ?ub)]))
        @ flatBT X0 @ concat (replicate n b0p)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fseqX: "\<And>n. flatBT (operB (Trans N) (numBT n))
      = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0p ?ub b0p X0 n) @ b1"
    using fseq Xflat by (simp add: X0_def)
  have donOTB: "operB (Trans N) (numBT 1) \<in> OT_B"
    using e4x_OT_B_operB_numBT[OF ihOT] by simp
  have loflat: "flatBT (operB (Trans N) (numBT 1))
      = s1 @ flatBT (Dpt (enat ?e3) X1) @ b1"
    using fseqX[of 1] by (simp add: X1_def)
  have lodec: "scb_decomp (operB (Trans N) (numBT 1)) s1
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
  have loP: "isOT_BP (DB (enat ?ub) X0)"
    using isOT_BP_Dpt_Dpt_Zero by (simp add: X0_def)
  have o1: "leBT X0 ?A0" using base0 by (simp add: X0_def)
  have o2: "leBT ?A0 X1" using base1 by (simp add: X1_def X0_def)
  have tri0: "b1x_triG (Dpt \<infinity> X0) ?A0 X1"
  proof -
    have "b1x_triG (Dpt \<infinity> X0) ?A0
            (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))"
      by (rule ot1_tri0_census[OF NST NPT hp j1gt branch ltJ inner_g])
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
  have tri0: "b1x_triG (Dpt \<infinity> (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))
                (bpHeadT (Trans (Pred (s84x_N N))))
                (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                   (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))"
    by (rule ot1_tri0_census[OF NST NPT hp j1gt branch ltJ inner_g])
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
    and base1: "lessBT t2 (d4vx_ins s0 ub b0 (Dpt (enat ub) 0\<^sub>B))"
    and tri0: "b1x_triG (Dpt \<infinity> (Dpt (enat ub) 0\<^sub>B)) t2
                 (d4vx_ins s0 ub b0 (Dpt (enat ub) 0\<^sub>B))"
    and Xe3: "\<And>j. isOT_BP (DB (enat e3) (d4vx_core s0 ub b0 (Dpt (enat ub) 0\<^sub>B) j))"
  shows "isOT_BP (DB (enat e3) (d4vx_core s0 ub b0 t2 k))"
proof -
  let ?X0 = "Dpt (enat ub) 0\<^sub>B"
  let ?W = "d4vx_core s0 ub b0 ?X0"
  let ?A = "d4vx_core s0 ub b0 t2"
  \<comment> \<open>X-tower OT facts (bodies, and head-\<open>ub\<close> principals by head antitone)\<close>
  have Wot: "isOT_BT (?W j)" for j using Xe3[of j] by simp
  have Xub: "isOT_BP (DB (enat ub) (?W j))" for j
    using oix_isOT_BP_head_antitone[OF Xe3[of j], of "enat ub"] euB by simp
  \<comment> \<open>interleave orders \<open>W\<^sub>j < A\<^sub>j < W\<^bsub>j+1\<^esub>\<close>\<close>
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0 base1]
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
                     (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
    and tri0: "b1x_triG
                 (Dpt \<infinity> (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))
                 (transT2 M)
                 (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
                    (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
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
  have X0TB: "?X0 \<in> T_B" by (simp add: T_B_def)
  have WTB: "\<And>j. d4vx_core s0 ?ub b0 ?X0 j \<in> T_B"
    by (rule oi5_d4vx_core_TB[OF wrap b0RP bodyT X0TB])
  \<comment> \<open>operB fundamental sequence flat, at the shared \<open>(s1,b1)\<close>, core = X-tower\<close>
  have fseq: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate n (s0 @ [Dsym (enat ?ub)]))
           @ [Dsym (enat ?ub)] @ [Zsym] @ concat (replicate n b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbody bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 ?X0 n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT ?X0 @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fWn: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 n)) @ b1"
    using fseq Xflat by simp
  \<comment> \<open>X-tower OT principals from the [Buc1] 3.2 closure of the IH\<close>
  have Xe3: "\<And>j. isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j))"
  proof -
    fix j
    have opOT: "operB (Trans M) (numBT j) \<in> OT_B"
      by (rule e4x_OT_B_operB_numBT[OF ihOT])
    have cTB: "Dpt (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j) \<in> T_B"
      using WTB by (simp add: T_B_def)
    have Xdec: "scb_decomp (operB (Trans M) (numBT j)) s1
                  (flatBT (Dpt (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j))) b1"
      unfolding scb_decomp_def
      using fWn b1RP isPTB_str_Dpt[of "enat ?e3" "d4vx_core s0 ?ub b0 ?X0 j"] WTB
      by (simp add: T_B_def)
    have "Dpt (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j) \<in> OT"
      by (rule m_8_7_OT_scb_recursive[OF opOT cTB Xdec])
    thus "isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j))"
      by (simp add: OT_def)
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
    and base1: "lessBT t2 (d4vx_ins s0 ub b0 (Dpt (enat ub) 0\<^sub>B))"
    and tri0: "b1x_triG (Dpt \<infinity> (Dpt (enat ub) 0\<^sub>B)) t2
                 (d4vx_ins s0 ub b0 (Dpt (enat ub) 0\<^sub>B))"
    and Xe3: "\<And>j. isOT_BP (DB (enat e3) (d4vx_core s0 ub b0 (Dpt (enat ub) 0\<^sub>B) j))"
  shows "isOT_BT (d4vx_core s0 ub b0 t2 k)
       \<and> b1x_triG (Dpt \<infinity> (d4vx_core s0 ub b0 (Dpt (enat ub) 0\<^sub>B) k))
            (d4vx_core s0 ub b0 t2 k)
            (d4vx_core s0 ub b0 (Dpt (enat ub) 0\<^sub>B) (Suc k))"
proof -
  let ?X0 = "Dpt (enat ub) 0\<^sub>B"
  let ?W = "d4vx_core s0 ub b0 ?X0"
  let ?A = "d4vx_core s0 ub b0 t2"
  have Wot: "isOT_BT (?W j)" for j using Xe3[of j] by simp
  have Xub: "isOT_BP (DB (enat ub) (?W j))" for j
    using oix_isOT_BP_head_antitone[OF Xe3[of j], of "enat ub"] euB by simp
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0 base1]
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                      (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))
                   (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                             (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))))"
proof -
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X1 = "d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B)"
  have tri0: "\<And>z. b1x_triG z ?A0 ?X1"
    by (rule ot1_tri0_census[OF NST NPT hp j1gt branch ltJ inner])
  \<comment> \<open>\<open>base\<^sub>1\<close> and the \<open>flat\<close> wrapper from the package (given \<open>(s\<^sub>0,b\<^sub>0)\<close> pinned)\<close>
  obtain s0' b0' s1 b1 where
      b0RP': "\<forall>x \<in> set b0'. x = RP"
    and inner': "scb_decomp (bpHeadT (Trans (s84x_N N))) s0'
         (flatBT (Dpt (enat (entry N 1 (Lng N - 1))) 0\<^sub>B)) b0'"
    and base1': "lessBT ?A0 (d4vx_ins s0' ?ub b0' (Dpt (enat ?ub) 0\<^sub>B))"
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
  have X1eq: "?X1 = d4vx_ins s0' ?ub b0' (Dpt (enat ?ub) 0\<^sub>B)" using pin by simp
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
(*   A1 = d4vx_ins s0 ub b0 A0, X1 = d4vx_ins s0 ub b0 X0 (SHARED wrapper) *)
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
                  (insert (d4vx_ins s0 ub b0 X0) (GBT u (d4vx_ins s0 ub b0 X0)))"
    and base1: "lessBT A0 (d4vx_ins s0 ub b0 X0)"
    and wrap: "flatBT W = s0 @ flatBP hole @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and spineH: "\<forall>t' sc bc. flatBT t' = sc @ flatBP (DB (enat ub) A0) @ bc
          \<longrightarrow> (\<forall>x\<in>set bc. x = RP) \<longrightarrow> size t' < size (d4vx_ins s0 ub b0 A0)
          \<longrightarrow> leBT t' (d4vx_ins s0 ub b0 X0)"
  shows "b1x_setle (GBT u (d4vx_ins s0 ub b0 A0))
           (insert (d4vx_ins s0 ub b0 X0) (GBT u (d4vx_ins s0 ub b0 X0)))"
proof -
  let ?X1 = "d4vx_ins s0 ub b0 X0"
  let ?A1 = "d4vx_ins s0 ub b0 A0"
  have fA1: "flatBT ?A1 = s0 @ flatBP (DB (enat ub) A0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ub A0] by simp
  have fX1: "flatBT ?X1 = s0 @ flatBP (DB (enat ub) X0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ub X0] by simp
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
                        (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))"
  shows "b1x_setle
           (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                     (bpHeadT (Trans (Pred (s84x_N N))))))
           (insert (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                      (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))
                   (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                             (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))))"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X0 = "Dpt (enat ?ub) 0\<^sub>B"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  \<comment> \<open>the body driver \<open>ox5\<close>\<close>
  have ox5: "b1x_setle (GBT u ?A0)
               (insert (d4vx_ins s0 ?ub b0 ?X0) (GBT u (d4vx_ins s0 ?ub b0 ?X0)))"
    by (rule ox5_body_driver_census[OF NST NPT hp j1gt branch ltJ inner])
  \<comment> \<open>\<open>base\<^sub>1\<close> and the flat wrapper from the package (given \<open>(s\<^sub>0,b\<^sub>0)\<close> pinned)\<close>
  obtain s0' b0' s1 b1 where
      b0RP': "\<forall>x \<in> set b0'. x = RP"
    and inner': "scb_decomp ?body s0'
         (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0'"
    and base1': "lessBT ?A0 (d4vx_ins s0' ?ub b0' ?X0)"
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
  have base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 ?X0)" using base1' pin by simp
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
              (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
proof -
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "entry M 1 (Lng M - 1) - 1"
  let ?jpe = "entry M 1 (transJ0 M)"
  let ?c = "Dpt (enat ?v1) 0\<^sub>B"
  let ?cc = "Dpt (enat ?ub) (Dpt (enat ?ub) 0\<^sub>B)"
  obtain t3 t4 where t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B"
    and body: "bpHeadT (transC2 M) = t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B ?c)"
    and rel: "(t3 = transT2 M \<and> t4 = transT2 M)
              \<or> transT2 M = t3 +\<^sub>B Dpt (enat ?jpe) t4"
    using c4dx_condIV_c2body_shape[OF MR MP J1pos T1 cIV] by blast
  have X0TB: "Dpt (enat ?ub) 0\<^sub>B \<in> T_B" by (simp add: T_B_def)
  have inner': "scb_decomp (t3 +\<^sub>B Dpt (enat ?jpe) (t4 +\<^sub>B Dpt (enat ?v1) 0\<^sub>B)) s0
                  (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0"
    using inner body by simp
  have X1eq: "d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B)
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
                     (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
    and tri0: "b1x_triG (Dpt \<infinity> (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))
                 (transT2 M)
                 (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
                    (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
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
  have X0TB: "?X0 \<in> T_B" by (simp add: T_B_def)
  have euB: "?e3 \<le> ?ub" using uv by linarith
  \<comment> \<open>tower \<open>T\<^bsub>B\<^esub>\<close>-membership\<close>
  have WTB: "\<And>k. d4vx_core s0 ?ub b0 ?X0 k \<in> T_B"
    by (rule oi5_d4vx_core_TB[OF wrap b0RP bodyT X0TB])
  \<comment> \<open>donor closed forms and flats\<close>
  have fseq: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ (Dsym (enat ?e3)
           # concat (replicate n (s0 @ [Dsym (enat ?ub)]))
           @ [Dsym (enat ?ub)] @ [Zsym] @ concat (replicate n b0)) @ b1"
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbody bodyne inner k1])
  have Xflat: "\<And>n. flatBT (d4vx_core s0 ?ub b0 ?X0 n)
      = concat (replicate n (s0 @ [Dsym (enat ?ub)]))
        @ flatBT ?X0 @ concat (replicate n b0)"
    by (rule d4vx_core_flat[OF wrap b0RP])
  have fWn: "\<And>n. flatBT (operB (Trans M) (numBT n))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 n)) @ b1"
    using fseq Xflat by simp
  \<comment> \<open>X-tower OT principals from the [Buc1] 3.2 closure of the IH\<close>
  have Xe3: "\<And>j. isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j))"
  proof -
    fix j
    have opOT: "operB (Trans M) (numBT j) \<in> OT_B"
      by (rule e4x_OT_B_operB_numBT[OF ihOT])
    have cTB: "Dpt (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j) \<in> T_B"
      using WTB by (simp add: T_B_def)
    have Xdec: "scb_decomp (operB (Trans M) (numBT j)) s1
                  (flatBT (Dpt (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j))) b1"
      unfolding scb_decomp_def
      using fWn b1RP isPTB_str_Dpt[of "enat ?e3" "d4vx_core s0 ?ub b0 ?X0 j"] WTB
      by (simp add: T_B_def)
    have "Dpt (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j) \<in> OT"
      by (rule m_8_7_OT_scb_recursive[OF opOT cTB Xdec])
    thus "isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 ?X0 j))"
      by (simp add: OT_def)
  qed
  \<comment> \<open>NEWOT and the joint tower invariant from the SETLE-free engine\<close>
  have newOTk: "\<And>k. isOT_BP (DB (enat ?e3) (d4vx_core s0 ?ub b0 (transT2 M) k))"
    by (rule ot2_tower_newOT[OF wrap b0RP euB t2OT base0 base1 tri0 Xe3])
  have INV: "\<And>k. isOT_BT (d4vx_core s0 ?ub b0 (transT2 M) k)
      \<and> b1x_triG (Dpt \<infinity> (d4vx_core s0 ?ub b0 ?X0 k))
            (d4vx_core s0 ?ub b0 (transT2 M) k)
            (d4vx_core s0 ?ub b0 ?X0 (Suc k))"
    by (rule ot2_tower_inv[OF wrap b0RP euB t2OT base0 base1 tri0 Xe3])
  \<comment> \<open>index bookkeeping\<close>
  have Sk: "Suc (m - 1) = m" using mgt by simp
  have fMm: "flatBT (Trans ((M::pairseq)[m]))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 (transT2 M) (m - 1))) @ b1"
    using mnform[of m] mgt by simp
  let ?A = "d4vx_core s0 ?ub b0 (transT2 M) (m - 1)"
  let ?WL = "d4vx_core s0 ?ub b0 ?X0 (m - 1)"
  let ?WH = "d4vx_core s0 ?ub b0 ?X0 m"
  have loflat: "flatBT (operB (Trans M) (numBT (m - 1)))
      = s1 @ flatBP (DB (enat ?e3) ?WL) @ b1"
    using fWn[of "m - 1"] by simp
  have hiflat: "flatBT (operB (Trans M) (numBT m))
      = s1 @ flatBP (DB (enat ?e3) ?WH) @ b1"
    using fWn[of m] by simp
  have loOT: "isOT_BT (operB (Trans M) (numBT (m - 1)))"
    using e4x_OT_B_operB_numBT[OF ihOT, of "m - 1"] by (simp add: OT_B_def OT_def)
  have hiOT: "isOT_BT (operB (Trans M) (numBT m))"
    using e4x_OT_B_operB_numBT[OF ihOT, of m] by (simp add: OT_B_def OT_def)
  have newOT: "isOT_BP (DB (enat ?e3) ?A)" by (rule newOTk)
  have triA: "b1x_triG (Dpt \<infinity> ?WL) ?A ?WH"
    using INV[of "m - 1"] Sk by simp
  note IL = c4cx_d4vx_core_interleave[OF wrap b0RP base0 base1, of "m - 1"]
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
         (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
    by (rule c4dx_condIV_base1[OF MR MPT J1pos T1 cIV inner])
  \<comment> \<open>the two clean tower inputs\<close>
  have t2OT: "isOT_BT (transT2 M)"
    by (rule ot2_transT2_OT[OF MST MPT hp cIV admeq ihOT])
  have tri0: "b1x_triG (Dpt \<infinity> (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))
                (transT2 M)
                (d4vx_ins s0 (entry M 1 (Lng M - 1) - 1) b0
                   (Dpt (enat (entry M 1 (Lng M - 1) - 1)) 0\<^sub>B))"
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
                     (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))
                  (GBT u (d4vx_ins s0 (entry P 1 (Lng P - 1) - 1) b0
                            (Dpt (enat (entry P 1 (Lng P - 1) - 1)) 0\<^sub>B))))"
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
                  (insert (d4vx_ins s0 ub b0 X0) (GBT u (d4vx_ins s0 ub b0 X0)))"
    and base1: "lessBT A0 (d4vx_ins s0 ub b0 X0)"
    and wrap: "flatBT W = s0 @ flatBP hole @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and spineH: "\<forall>t' tx' sc bc.
          flatBT t' = sc @ flatBP (DB (enat ub) A0) @ bc
          \<longrightarrow> flatBT tx' = sc @ flatBP (DB (enat ub) X0) @ bc
          \<longrightarrow> (\<forall>x\<in>set bc. x = RP)
          \<longrightarrow> tx' \<in> GBT u (d4vx_ins s0 ub b0 X0)
          \<longrightarrow> size t' < size (d4vx_ins s0 ub b0 A0)
          \<longrightarrow> leBT t' (d4vx_ins s0 ub b0 X0)"
  shows "b1x_setle (GBT u (d4vx_ins s0 ub b0 A0))
           (insert (d4vx_ins s0 ub b0 X0) (GBT u (d4vx_ins s0 ub b0 X0)))"
proof -
  let ?X1 = "d4vx_ins s0 ub b0 X0"
  let ?A1 = "d4vx_ins s0 ub b0 A0"
  have fA1: "flatBT ?A1 = s0 @ flatBP (DB (enat ub) A0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ub A0] by simp
  have fX1: "flatBT ?X1 = s0 @ flatBP (DB (enat ub) X0) @ b0"
    using d4vx_ins_flat[OF wrap b0RP, of ub X0] by simp
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
          \<longrightarrow> flatBT tx' = sc @ flatBP (DB (enat (entry N 1 (Lng N - 1) - 1))
                                      (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B)) @ bc
          \<longrightarrow> (\<forall>x\<in>set bc. x = RP)
          \<longrightarrow> tx' \<in> GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                            (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))
          \<longrightarrow> size t' < size (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                                (bpHeadT (Trans (Pred (s84x_N N)))))
          \<longrightarrow> leBT t' (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                        (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))"
  shows "b1x_setle
           (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                     (bpHeadT (Trans (Pred (s84x_N N))))))
           (insert (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                      (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))
                   (GBT u (d4vx_ins s0 (entry N 1 (Lng N - 1) - 1) b0
                             (Dpt (enat (entry N 1 (Lng N - 1) - 1)) 0\<^sub>B))))"
proof -
  let ?v1 = "entry N 1 (Lng N - 1)"
  let ?ub = "entry N 1 (Lng N - 1) - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N N)))"
  let ?X0 = "Dpt (enat ?ub) 0\<^sub>B"
  let ?body = "bpHeadT (Trans (s84x_N N))"
  \<comment> \<open>the body driver \<open>ox5\<close>\<close>
  have ox5: "b1x_setle (GBT u ?A0)
               (insert (d4vx_ins s0 ?ub b0 ?X0) (GBT u (d4vx_ins s0 ?ub b0 ?X0)))"
    by (rule ox5_body_driver_census[OF NST NPT hp j1gt branch ltJ inner])
  \<comment> \<open>\<open>base\<^sub>1\<close> and the flat wrapper from the package (given \<open>(s\<^sub>0,b\<^sub>0)\<close> pinned)\<close>
  obtain s0' b0' s1 b1 where
      b0RP': "\<forall>x \<in> set b0'. x = RP"
    and inner': "scb_decomp ?body s0'
         (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0'"
    and base1': "lessBT ?A0 (d4vx_ins s0' ?ub b0' ?X0)"
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
  have base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 ?X0)" using base1' pin by simp
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
  let ?S = "{J. entry (Br (tvx_Rc K) ! (Lng (Br (tvx_Rc K)) - 1)) 0 0
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

end
