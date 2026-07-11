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

end
