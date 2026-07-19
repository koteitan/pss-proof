theory Frontier_6_089
  imports Support_6_067
begin

text \<open>§6.5 m10>0 brick (b5): the row-1 NJ head of a coreReduce branch equals the
  component's row-1 head, npJ (coreReduce M) J = entry (Br (coreReduce M) ! J) 1 0.
  The unique row-1 parent p of the first node lies on the coreReduce trunk
  (largest-below through the joint), where row-1 entries equal the index.  If
  p sits in the shifted M-part, the edge transfers to M and RedCondA M pins the
  +1; if p sits in the diagonal prefix, no M-side ancestor has a smaller row-1
  value (else its transfer would contradict uniqueness), and the edge from
  index b-1 is constructed directly, so p = b-1 by uniqueness.\<close>

lemma coreReduce_nextrel1_transfer:
  assumes MT: "M \<in> T_PS" and pos: "0 < entry M 1 0"
    and kM: "k < Lng M" and kM': "k' < Lng M"
  shows "nextrel1 (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)
            (entry M 1 0 + k) (entry M 1 0 + k')
         = nextrel1 M k k'"
proof -
  let ?m = "entry M 1 0"
  let ?Y = "(IncrFirst ^^ ?m) M"
  let ?A = "diagSeq 0 (?m - 1) @ ?Y"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
  have LA: "Lng ?A = ?m + Lng M" using Ld by simp
  have dropA: "drop ?m ?A = ?Y" using Ld by simp
  have segA: "seg ?A ?m (Lng ?A - 1) = ?Y"
    using seg_to_last_eq_drop[of ?A ?m] LA LMpos dropA by simp
  have bnd: "Lng ?A - 1 < Lng ?A" using LA LMpos by simp
  have kS: "k < Lng (seg ?A ?m (Lng ?A - 1))" using segA kM by simp
  have kS': "k' < Lng (seg ?A ?m (Lng ?A - 1))" using segA kM' by simp
  have "nextrel1 (seg ?A ?m (Lng ?A - 1)) k k' = nextrel1 ?A (?m + k) (?m + k')"
    by (rule adm_nextrel1_seg[OF bnd kS kS'])
  moreover have "nextrel1 (seg ?A ?m (Lng ?A - 1)) k k' = nextrel1 M k k'"
    using segA nextrel1_funpow_IncrFirst_eq[of ?m M] by simp
  ultimately show ?thesis by simp
qed

lemma npJ_coreReduce:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
    and pos: "0 < entry M 1 0"
    and JBr: "J < Lng (Br M)"
  shows "npJ (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M) J
         = entry (Br M ! J) 1 0"
proof -
  let ?m = "entry M 1 0"
  let ?A = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  let ?b = "entry (Br M ! J) 1 0"
  have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
  have LA: "Lng ?A = ?m + Lng M" using Ld by simp
  have LApos: "0 < Lng ?A" using LA LMpos by simp
  have Ane: "?A \<noteq> []" using LApos length_greater_0_conv by blast
  have AT: "?A \<in> T_PS" using Ane by (simp add: T_PS_def)
  have crM: "coreReduce M = ?A" by (rule coreReduce_m10pos_form[OF pos])
  have monoA: "monoT ?A" using coreReduce_monoT_m10_pos[OF MT mono pos] crM by simp
  have brA: "Br ?A = map (IncrFirst ^^ ?m) (Br M)"
    by (rule Br_coreReduce[OF MT condA mono pos])
  have JA: "J < length (Br ?A)" using JBr brA by simp
  have brMne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF MPT JBr])
  have brMpos: "0 < Lng (Br M ! J)" using brMne by (cases "Br M ! J") auto
  have brAJ: "Br ?A ! J = (IncrFirst ^^ ?m) (Br M ! J)" using brA JBr by simp
  have br10A: "entry (Br ?A ! J) 1 0 = ?b"
    using brAJ entry_funpow_IncrFirst1[OF brMpos] by simp
  show ?thesis
  proof (cases "?b = 0")
    case True
    thus ?thesis using br10A by (simp add: npJ_def)
  next
    case bne: False
    have bpos: "0 < ?b" using bne by simp
    let ?fnM = "FirstNodes M ! J"  let ?jnM = "Joints M ! J"
    let ?fnA = "?m + ?fnM"
    have fnTr: "?jnM \<le> TrMax M \<and> TrMax M < ?fnM"
      by (rule m_6_4_FirstNodes_TrMax_Joints[OF MPT JBr])
    have nxJM: "nextR M 0 ?jnM ?fnM" by (rule Joints_parent_nextR[OF MPT JBr])
    have nr0M: "nextrel0 M ?jnM ?fnM" using nxJM by (simp add: nextR_def)
    have jnML: "?jnM < Lng M" and fnML: "?fnM < Lng M"
      using nr0M by (simp_all add: nextrel0_def)
    have fnAmap: "FirstNodes ?A ! J = ?fnA"
    proof -
      have fnmap: "FirstNodes ?A = map ((+) ?m) (FirstNodes M)"
        by (rule FirstNodes_coreReduce[OF MT condA mono pos])
      have lenFN: "J < length (FirstNodes M)"
        using JBr by (simp add: FirstNodes_def IdxSum_def)
      show ?thesis using fnmap lenFN by simp
    qed
    have fnAL: "?fnA < Lng ?A" using fnML LA by simp
    have e1fnM: "entry M 1 ?fnM = ?b"
      using entry_FirstNodes_eq_component_gen[OF MPT] JBr by simp
    have e1fnA: "entry ?A 1 ?fnA = ?b"
    proof -
      have "?A ! ?fnA = ((IncrFirst ^^ ?m) M) ! ?fnM" using Ld by (simp add: nth_append)
      hence "entry ?A 1 ?fnA = entry ((IncrFirst ^^ ?m) M) 1 ?fnM" by (simp add: entry_def)
      thus ?thesis using entry_funpow_IncrFirst1[OF fnML] e1fnM by simp
    qed
    have e10A: "entry ?A 1 0 = 0"
    proof -
      have "?A ! 0 = diagSeq 0 (?m - 1) ! 0" using Ld pos by (simp add: nth_append)
      also have "\<dots> = (0, 0)" using pos by (simp add: diagSeq_def del: upt_Suc)
      finally show ?thesis by (simp add: entry_def)
    qed
    have e10lt: "entry ?A 1 0 < entry ?A 1 ?fnA" using e10A e1fnA bpos by simp
    have fnApos: "0 < ?fnA" using pos by simp
    have le00: "leR ?A 0 0 ?fnA"
    proof -
      have root: "leR ?A 0 0 (Lng ?A - 1)" using monoA by (simp add: monoT_def)
      have fle: "?fnA \<le> Lng ?A - 1" using fnAL by simp
      show ?thesis by (rule m_5_1_ancestor_tree_1[OF AT root _ fle]) simp
    qed
    obtain p where pb: "p < ?fnA" and pc: "nextR ?A 1 p ?fnA"
      using m_5_1_parent_exists_2[OF AT fnApos fnAL e10lt le00] by blast
    have ex1: "\<exists>!x. nextR ?A 1 x ?fnA" using pc nextR1_unique by blast
    have the_p: "(THE x. nextR ?A 1 x ?fnA) = p" by (rule the1_equality[OF ex1 pc])
    have npval: "npJ ?A J = Suc p"
      using br10A bne the_p fnAmap by (simp add: npJ_def)
    \<comment> \<open>p lies on the trunk of A\<close>
    have nr0A: "nextrel0 ?A (?m + ?jnM) ?fnA"
      using coreReduce_nextrel0_transfer[OF MT pos jnML fnML] nr0M by simp
    have nxA0: "nextR ?A 0 (?m + ?jnM) ?fnA" using nr0A by (simp add: nextR_def)
    have le0pf: "leR ?A 0 p ?fnA"
      using pc by (simp add: nextR_def nextrel1_def leR_def)
    have e0plt: "entry ?A 0 p < entry ?A 0 ?fnA"
      by (rule m_5_1_ancestor_basic_1[OF AT pb order.refl le0pf])
    have p_le: "p \<le> ?m + ?jnM" by (rule nextR0_largest_below[OF nxA0 pb e0plt])
    have trA: "TrMax ?A = ?m + TrMax M" by (rule TrMax_coreReduce[OF MT condA mono pos])
    have pTrA: "p \<le> TrMax ?A" using p_le fnTr trA by linarith
    have e1p: "entry ?A 1 p = p" by (rule coreReduce_trunk_e1[OF MT condA mono pos pTrA])
    \<comment> \<open>conclude Suc p = b by the two positions of p\<close>
    have sucp: "Suc p = ?b"
    proof (cases "?m \<le> p")
      case True
      define k where "k = p - ?m"
      have pk: "p = ?m + k" using True k_def by simp
      have kTr: "k \<le> TrMax M" using pTrA trA pk by simp
      have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
      have kM: "k < Lng M" using kTr tb LMpos by linarith
      have nr1A: "nextrel1 ?A (?m + k) (?m + ?fnM)" using pc pk by (simp add: nextR_def)
      have nr1M: "nextrel1 M k ?fnM"
        using coreReduce_nextrel1_transfer[OF MT pos kM fnML] nr1A by simp
      have nxM1: "nextR M 1 k ?fnM" using nr1M by (simp add: nextR_def)
      have ex1M: "\<exists>!x. nextR M 1 x ?fnM" using nxM1 nextR1_unique by blast
      have hpM: "hasParent M 1 ?fnM" unfolding hasParent_def by (rule ex1M)
      have parM: "parent M 1 ?fnM = k"
      proof -
        have "nextR M 1 (parent M 1 ?fnM) ?fnM"
          using hpM unfolding hasParent_def parent_def by (rule theI')
        thus ?thesis using nxM1 by (rule nextR1_unique)
      qed
      have cA1: "entry M 1 (parent M 1 ?fnM) + 1 = entry M 1 ?fnM"
        using condA hpM unfolding RedCondA_def by blast
      have e1k: "entry M 1 k = ?m + k"
        using trunk_entries_offset[OF MT condA kTr] by simp
      have "?m + k + 1 = ?b" using cA1 parM e1k e1fnM by simp
      thus ?thesis using pk by simp
    next
      case False
      hence plt: "p < ?m" by simp
      \<comment> \<open>no M-side le0-ancestor of the first node has a smaller row-1 value\<close>
      have nosmall: "\<And>k. k < Lng M \<Longrightarrow> le0 M k ?fnM \<Longrightarrow> ?b \<le> entry M 1 k"
      proof (rule ccontr)
        fix k assume kM: "k < Lng M" and le0k: "le0 M k ?fnM"
          and nb: "\<not> ?b \<le> entry M 1 k"
        have elt: "entry M 1 k < entry M 1 ?fnM" using nb e1fnM by simp
        have kfn: "k < ?fnM"
        proof -
          have "k \<le> ?fnM" using le0k nextrel0_rtrancl_mono[of M k ?fnM]
            by (simp add: le0_def)
          moreover have "k \<noteq> ?fnM" using elt by auto
          ultimately show ?thesis by simp
        qed
        have leRk: "leR M 0 k ?fnM" using le0k by (simp add: leR_def)
        obtain p' where pb': "p' < ?fnM" and pc': "nextR M 1 p' ?fnM"
          using m_5_1_parent_exists_2[OF MT kfn fnML elt leRk] by blast
        have pM': "p' < Lng M" using pb' fnML by linarith
        have nr1A': "nextrel1 ?A (?m + p') (?m + ?fnM)"
          using coreReduce_nextrel1_transfer[OF MT pos pM' fnML] pc'
          by (simp add: nextR_def)
        have "nextR ?A 1 (?m + p') ?fnA" using nr1A' by (simp add: nextR_def)
        hence "?m + p' = p" using pc by (rule nextR1_unique)
        thus False using plt by simp
      qed
      have bm: "?b \<le> ?m"
      proof -
        have le00M: "le0 M 0 ?fnM"
        proof -
          have root: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
          have fle: "?fnM \<le> Lng M - 1" using fnML by simp
          have "leR M 0 0 ?fnM" by (rule m_5_1_ancestor_tree_1[OF MT root _ fle]) simp
          thus ?thesis by (simp add: leR_def)
        qed
        show ?thesis using nosmall[OF LMpos le00M] by simp
      qed
      \<comment> \<open>the trunk of A is a row-0 chain, so b-1 reaches the joint\<close>
      have trunk_le0: "\<And>a b'. a \<le> b' \<Longrightarrow> b' \<le> TrMax ?A \<Longrightarrow> le0 ?A a b'"
      proof -
        fix a b' show "a \<le> b' \<Longrightarrow> b' \<le> TrMax ?A \<Longrightarrow> le0 ?A a b'"
        proof (induct b')
          case 0
          hence a0: "a = 0" by simp
          have "(0::nat) < Lng ?A" using LApos .
          thus ?case using a0 by (simp add: le0_def)
        next
          case (Suc b')
          show ?case
          proof (cases "a = Suc b'")
            case True
            have "Suc b' < Lng ?A"
              using Suc.prems(2) TrMax_bound[OF AT] LApos by linarith
            thus ?thesis using True by (simp add: le0_def)
          next
            case False
            have ab: "a \<le> b'" using Suc.prems(1) False by simp
            have bTr: "b' \<le> TrMax ?A" using Suc.prems(2) by simp
            have IH: "le0 ?A a b'" by (rule Suc.hyps[OF ab bTr])
            have st: "nextR ?A 1 b' (b' + 1)"
              by (rule TrMax_trunk_step[OF AT]) (use Suc.prems(2) in simp)
            have "le0 ?A b' (b' + 1)" using st by (simp add: nextR_def nextrel1_def)
            hence "le0 ?A b' (Suc b')" by simp
            thus ?thesis using IH le0_trans by blast
          qed
        qed
      qed
      have b1jn: "?b - 1 \<le> ?m + ?jnM" using bm by simp
      have jnTrA: "?m + ?jnM \<le> TrMax ?A" using trA fnTr by simp
      have le0b1jn: "le0 ?A (?b - 1) (?m + ?jnM)" by (rule trunk_le0[OF b1jn jnTrA])
      have le0jnfn: "le0 ?A (?m + ?jnM) ?fnA"
      proof -
        have bnds: "?m + ?jnM < Lng ?A \<and> ?fnA < Lng ?A"
          using nr0A by (simp add: nextrel0_def)
        show ?thesis unfolding le0_def using bnds nr0A by (blast intro: r_into_rtranclp)
      qed
      have le0b1fn: "le0 ?A (?b - 1) ?fnA" using le0b1jn le0jnfn le0_trans by blast
      \<comment> \<open>entries and valley for the constructed edge\<close>
      have b1m: "?b - 1 < ?m" using bm bpos by simp
      have e1b1: "entry ?A 1 (?b - 1) = ?b - 1"
      proof -
        have "?A ! (?b - 1) = diagSeq 0 (?m - 1) ! (?b - 1)"
          using b1m Ld by (simp add: nth_append)
        also have "\<dots> = (?b - 1, ?b - 1)" using b1m pos by (simp add: diagSeq_def del: upt_Suc)
        finally show ?thesis by (simp add: entry_def)
      qed
      have e1b1lt: "entry ?A 1 (?b - 1) < entry ?A 1 ?fnA" using e1b1 e1fnA bpos by simp
      have vall: "\<forall>j. ?b - 1 < j \<and> le0 ?A j ?fnA \<longrightarrow> entry ?A 1 j \<ge> entry ?A 1 ?fnA"
      proof (intro allI impI)
        fix j assume H: "?b - 1 < j \<and> le0 ?A j ?fnA"
        from H have jgt: "?b - 1 < j" and jle0: "le0 ?A j ?fnA" by auto
        show "entry ?A 1 j \<ge> entry ?A 1 ?fnA"
        proof (cases "j < ?m")
          case True
          have "?A ! j = diagSeq 0 (?m - 1) ! j" using True Ld by (simp add: nth_append)
          also have "\<dots> = (j, j)" using True pos by (simp add: diagSeq_def del: upt_Suc)
          finally have "entry ?A 1 j = j" by (simp add: entry_def)
          thus ?thesis using jgt bpos e1fnA by simp
        next
          case False
          define k where "k = j - ?m"
          have jk: "j = ?m + k" using False k_def by simp
          have le0Aj: "le0 ?A (?m + k) (?m + ?fnM)" using jle0 jk by simp
          have "le0 M k ?fnM" by (rule coreReduce_le0_back[OF MT pos fnML le0Aj])
          moreover have kM: "k < Lng M"
            using le0Aj LA by (simp add: le0_def)
          ultimately have "?b \<le> entry M 1 k" using nosmall by blast
          moreover have "entry ?A 1 j = entry M 1 k"
          proof -
            have "?A ! j = ((IncrFirst ^^ ?m) M) ! k" using jk Ld by (simp add: nth_append)
            hence "entry ?A 1 j = entry ((IncrFirst ^^ ?m) M) 1 k" by (simp add: entry_def)
            thus ?thesis using entry_funpow_IncrFirst1[OF kM] by simp
          qed
          ultimately show ?thesis using e1fnA by simp
        qed
      qed
      have b1L: "?b - 1 < Lng ?A" using b1m LA by linarith
      have b1fn: "?b - 1 < ?fnA" using b1m by simp
      have nr1b1: "nextrel1 ?A (?b - 1) ?fnA"
        unfolding nextrel1_def using b1L fnAL b1fn e1b1lt le0b1fn vall by simp
      have "nextR ?A 1 (?b - 1) ?fnA" using nr1b1 by (simp add: nextR_def)
      hence "?b - 1 = p" using pc by (rule nextR1_unique)
      thus ?thesis using bpos by simp
    qed
    show ?thesis using npval sucp by simp
  qed
qed


text \<open>§6.5 m10>0 brick (b6): lowering the row-0 head below the (strictly higher)
  tail preserves the congR structure, and in a mono sequence every later row-0
  value strictly exceeds the head (a tie column would be unreachable and
  unspannable, breaking the trunk chain).  Together with the general branch
  head value this lets the master key cdn_red_cong identify Red (NJ A J) with
  Red (Br A ! J) in the m10>0 assembly.\<close>

lemma mono_tail_row0_strict:
  assumes XT: "X \<in> T_PS" and mono: "monoT X"
    and q1: "1 \<le> q" and qL: "q < Lng X"
  shows "entry X 0 0 < entry X 0 q"
proof (rule ccontr)
  assume nlt: "\<not> entry X 0 0 < entry X 0 q"
  have ge: "entry X 0 0 \<le> entry X 0 q" by (rule entry0_ge_min[OF XT mono qL])
  have eq: "entry X 0 q = entry X 0 0" using nlt ge by simp
  have conf: "\<And>y. (nextrel0 X)\<^sup>*\<^sup>* 0 y \<Longrightarrow> y < q"
  proof -
    fix y assume "(nextrel0 X)\<^sup>*\<^sup>* 0 y"
    thus "y < q"
    proof (induction rule: rtranclp_induct)
      case base show ?case using q1 by simp
    next
      case (step p y)
      have pq: "p < q" by (rule step.IH)
      have py: "p < y" and yL: "y < Lng X"
        using step.hyps(2) by (simp_all add: nextrel0_def)
      have eplt: "entry X 0 p < entry X 0 y"
        using step.hyps(2) by (simp add: nextrel0_def)
      have pL: "p < Lng X" using py yL by linarith
      have pge: "entry X 0 0 \<le> entry X 0 p" by (rule entry0_ge_min[OF XT mono pL])
      show ?case
      proof (rule ccontr)
        assume "\<not> y < q"
        hence yq: "q \<le> y" by simp
        show False
        proof (cases "y = q")
          case True
          show False using eplt eq pge True by simp
        next
          case False
          hence qy: "q < y" using yq by simp
          have vall: "\<forall>j. p < j \<and> j < y \<longrightarrow> entry X 0 j \<ge> entry X 0 y"
            using step.hyps(2) unfolding nextrel0_def by blast
          have "entry X 0 q \<ge> entry X 0 y" using vall pq qy by blast
          hence "entry X 0 y \<le> entry X 0 0" using eq by simp
          thus False using eplt pge by simp
        qed
      qed
    qed
  qed
  have Xne: "X \<noteq> []" using XT by (simp add: T_PS_def)
  have LXpos: "0 < Lng X" using Xne by (cases X) auto
  have "le0 X 0 (Lng X - 1)" using mono by (simp add: monoT_def leR_def)
  hence "(nextrel0 X)\<^sup>*\<^sup>* 0 (Lng X - 1)" by (simp add: le0_def)
  hence "Lng X - 1 < q" by (rule conf)
  thus False using qL by linarith
qed

lemma congR_head0_lower:
  assumes ab: "a \<le> b"
    and strict: "\<And>q. 1 \<le> q \<Longrightarrow> q < Lng ((b, h) # T) \<Longrightarrow> b < entry ((b, h) # T) 0 q"
  shows "congR ((a, h) # T) ((b, h) # T)"
proof -
  let ?Aa = "(a, h) # T"  let ?X = "(b, h) # T"
  have L: "Lng ?Aa = Lng ?X" by simp
  have e1: "\<And>j. j < Lng ?X \<Longrightarrow> entry ?Aa 1 j = entry ?X 1 j"
  proof -
    fix j assume "j < Lng ?X"
    show "entry ?Aa 1 j = entry ?X 1 j"
      by (cases j) (simp_all add: entry_def)
  qed
  have e0tail: "\<And>j. 1 \<le> j \<Longrightarrow> entry ?Aa 0 j = entry ?X 0 j"
  proof -
    fix j assume "1 \<le> (j::nat)"
    then obtain j' where "j = Suc j'" by (cases j) auto
    thus "entry ?Aa 0 j = entry ?X 0 j" by (simp add: entry_def)
  qed
  have nxt: "nextrel0 ?Aa = nextrel0 ?X"
  proof (intro ext)
    fix p q
    show "nextrel0 ?Aa p q = nextrel0 ?X p q"
    proof (cases "p = 0")
      case True
      show ?thesis
      proof (cases "0 < q \<and> q < Lng ?X")
        case qok: True
        have q1: "1 \<le> q" and qL: "q < Lng ?X" using qok by auto
        have eq_q: "entry ?Aa 0 q = entry ?X 0 q" using e0tail[OF q1] .
        have bq: "b < entry ?X 0 q" by (rule strict[OF q1 qL])
        have aq: "a < entry ?X 0 q" using ab bq by linarith
        have headA: "entry ?Aa 0 0 = a" and headX: "entry ?X 0 0 = b"
          by (simp_all add: entry_def)
        have vAX: "(\<forall>j. 0 < j \<and> j < q \<longrightarrow> entry ?Aa 0 j \<ge> entry ?Aa 0 q)
                   = (\<forall>j. 0 < j \<and> j < q \<longrightarrow> entry ?X 0 j \<ge> entry ?X 0 q)"
        proof -
          have "\<And>j. 0 < j \<and> j < q \<Longrightarrow>
                  (entry ?Aa 0 j \<ge> entry ?Aa 0 q) = (entry ?X 0 j \<ge> entry ?X 0 q)"
          proof -
            fix j assume H: "0 < j \<and> j < q"
            have "entry ?Aa 0 j = entry ?X 0 j" using e0tail H by simp
            thus "(entry ?Aa 0 j \<ge> entry ?Aa 0 q) = (entry ?X 0 j \<ge> entry ?X 0 q)"
              using eq_q by simp
          qed
          thus ?thesis by blast
        qed
        show ?thesis
          unfolding nextrel0_def
          using True qok headA headX aq bq eq_q vAX by auto
      next
        case False
        hence "\<not> (p < q \<and> q < Lng ?X)" using True by auto
        thus ?thesis unfolding nextrel0_def using L by auto
      qed
    next
      case pn0: False
      hence p1: "1 \<le> p" by simp
      show ?thesis
      proof (cases "p < q \<and> q < Lng ?X \<and> p < Lng ?X")
        case ok: True
        have ep: "entry ?Aa 0 p = entry ?X 0 p" using e0tail[OF p1] .
        have eq_q: "entry ?Aa 0 q = entry ?X 0 q"
          using e0tail ok p1 by simp
        have vAX: "(\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?Aa 0 j \<ge> entry ?Aa 0 q)
                   = (\<forall>j. p < j \<and> j < q \<longrightarrow> entry ?X 0 j \<ge> entry ?X 0 q)"
        proof -
          have "\<And>j. p < j \<and> j < q \<Longrightarrow>
                  (entry ?Aa 0 j \<ge> entry ?Aa 0 q) = (entry ?X 0 j \<ge> entry ?X 0 q)"
          proof -
            fix j assume H: "p < j \<and> j < q"
            have "1 \<le> j" using H p1 by linarith
            hence "entry ?Aa 0 j = entry ?X 0 j" using e0tail by simp
            thus "(entry ?Aa 0 j \<ge> entry ?Aa 0 q) = (entry ?X 0 j \<ge> entry ?X 0 q)"
              using eq_q by simp
          qed
          thus ?thesis by blast
        qed
        show ?thesis unfolding nextrel0_def using ok ep eq_q vAX L by auto
      next
        case False
        thus ?thesis unfolding nextrel0_def using L by auto
      qed
    qed
  qed
  show ?thesis unfolding congR_def using L nxt e1 by simp
qed

lemma BrJ_head0_gen:
  assumes M: "M \<in> PT_PS"
    and condA: "RedCondA M"
    and JBr: "J < Lng (Br M)"
  shows "entry (Br M ! J) 0 0 = entry M 0 0 + Joints M ! J + 1"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  let ?f = "FirstNodes M ! J"  let ?jn = "Joints M ! J"
  have fnTr: "?jn \<le> TrMax M \<and> TrMax M < ?f"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M JBr])
  have jnTr: "?jn \<le> TrMax M" using fnTr by blast
  have nxJ: "nextR M 0 ?jn ?f" by (rule Joints_parent_nextR[OF M JBr])
  have hp0: "hasParent M 0 ?f"
    unfolding hasParent_def using nxJ idxsum_parent0_unique by blast
  have par0: "parent M 0 ?f = ?jn"
  proof -
    have "nextR M 0 (parent M 0 ?f) ?f"
      using hp0 unfolding hasParent_def parent_def by (rule theI')
    thus ?thesis using nxJ by (rule idxsum_parent0_unique)
  qed
  have e0jn: "entry M 0 ?jn = entry M 0 0 + ?jn"
    using trunk_entries_offset[OF MT condA jnTr] by blast
  have cA0: "entry M 0 (parent M 0 ?f) + 1 = entry M 0 ?f"
    using condA hp0 unfolding RedCondA_def by blast
  have e0f: "entry M 0 ?f = entry M 0 0 + ?jn + 1" using cA0 par0 e0jn by simp
  show ?thesis
    using entry_FirstNodes_eq_component_gen[OF M] JBr e0f by simp
qed


text \<open>§6.5 m10>0 stage-1 helpers for the final assembly (b7): IncrFirst as a pair
  map, funpow invariances, the rebase as a pair map, and the BLOCK VALUE of the
  coreReduce branches -- each lifted reduced block is the rebase image of the
  M-branch component.\<close>

lemma funpow_IncrFirst_as_map:
  "(IncrFirst ^^ k) Z = map (\<lambda>p. (fst p + k, snd p)) Z"
proof (induction k)
  case 0 show ?case by (simp add: map_idI)
next
  case (Suc k)
  show ?case using Suc.IH by (simp add: IncrFirst_def o_def)
qed

lemma multiT_funpow_IncrFirst: "multiT ((IncrFirst ^^ k) Z) = multiT Z"
  by (induction k) (simp_all add: IncrFirst_multiT_eq)

lemma rebase_as_pair_map:
  "map (\<lambda>j. (entry Z 0 j - c0 + c1, entry Z 1 j)) [0..<Lng Z]
   = map (\<lambda>p. (fst p - c0 + c1, snd p)) Z"
proof (rule nth_equalityI)
  show "length (map (\<lambda>j. (entry Z 0 j - c0 + c1, entry Z 1 j)) [0..<Lng Z])
        = length (map (\<lambda>p. (fst p - c0 + c1, snd p)) Z)" by simp
next
  fix j assume "j < length (map (\<lambda>j. (entry Z 0 j - c0 + c1, entry Z 1 j)) [0..<Lng Z])"
  hence jZ: "j < Lng Z" by simp
  show "map (\<lambda>j. (entry Z 0 j - c0 + c1, entry Z 1 j)) [0..<Lng Z] ! j
        = map (\<lambda>p. (fst p - c0 + c1, snd p)) Z ! j"
    using jZ by (simp add: entry_def del: upt_Suc)
qed

lemma coreReduce_block_value:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
    and pos: "0 < entry M 1 0"
    and JBr: "J < Lng (Br M)"
    and IH: "Red ((IncrFirst ^^ entry M 1 0) (Br M ! J))
             = map (\<lambda>j. (entry ((IncrFirst ^^ entry M 1 0) (Br M ! J)) 0 j
                           - entry ((IncrFirst ^^ entry M 1 0) (Br M ! J)) 0 0
                           + entry ((IncrFirst ^^ entry M 1 0) (Br M ! J)) 1 0,
                         entry ((IncrFirst ^^ entry M 1 0) (Br M ! J)) 1 j))
                   [0..<Lng ((IncrFirst ^^ entry M 1 0) (Br M ! J))]"
  shows "(IncrFirst ^^ (Joints (diagSeq 0 (entry M 1 0 - 1)
                                 @ (IncrFirst ^^ entry M 1 0) M) ! J + 1
                        - npJ (diagSeq 0 (entry M 1 0 - 1)
                                 @ (IncrFirst ^^ entry M 1 0) M) J))
           (Red (NJ (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M) J))
         = map (\<lambda>p. (fst p - entry M 0 0 + entry M 1 0, snd p)) (Br M ! J)"
proof -
  let ?m = "entry M 1 0"  let ?c0 = "entry M 0 0"
  let ?A = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  let ?B = "Br M ! J"
  let ?X = "(IncrFirst ^^ ?m) ?B"
  let ?jn = "Joints M ! J"
  have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brMne: "?B \<noteq> []" by (rule Br_component_nonempty[OF MPT JBr])
  have brMpos: "0 < Lng ?B" using brMne by (cases ?B) auto
  have Xpos: "0 < Lng ?X" using brMpos by simp
  have Xne: "?X \<noteq> []" using Xpos length_greater_0_conv by blast
  have brA: "Br ?A = map (IncrFirst ^^ ?m) (Br M)"
    by (rule Br_coreReduce[OF MT condA mono pos])
  have brAJ: "Br ?A ! J = ?X" using brA JBr by simp
  have jnA: "Joints ?A ! J = ?m + ?jn" by (rule Joints_coreReduce[OF MT condA mono pos JBr])
  let ?b = "entry ?B 1 0"
  have npA: "npJ ?A J = ?b" by (rule npJ_coreReduce[OF MT condA mono pos JBr])
  have nple: "?b \<le> ?m + ?jn + 1"
  proof -
    have crM: "coreReduce M = ?A" by (rule coreReduce_m10pos_form[OF pos])
    have monoA: "monoT ?A" using coreReduce_monoT_m10_pos[OF MT mono pos] crM by simp
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have LMpos: "0 < Lng M" using Mne by (cases M) auto
    have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
    have LA: "Lng ?A = ?m + Lng M" using Ld by simp
    have LApos: "0 < Lng ?A" using LA LMpos by simp
    have Ane: "?A \<noteq> []" using LApos length_greater_0_conv by blast
    have AT: "?A \<in> T_PS" using Ane by (simp add: T_PS_def)
    have APT: "?A \<in> PT_PS" using AT monoA by (simp add: PT_PS_def)
    have e10A: "entry ?A 1 0 = 0"
    proof -
      have "?A ! 0 = diagSeq 0 (?m - 1) ! 0" using Ld pos by (simp add: nth_append)
      also have "\<dots> = (0, 0)" using pos by (simp add: diagSeq_def del: upt_Suc)
      finally show ?thesis by (simp add: entry_def)
    qed
    have JA: "J < Lng (Br ?A)" using JBr brA by simp
    have "npJ ?A J \<le> Joints ?A ! J + 1"
      by (rule npJ_le_Joints_Suc[OF APT e10A JA])
    thus ?thesis using npA jnA by simp
  qed
  \<comment> \<open>head values of the shifted component\<close>
  have h0B: "entry ?B 0 0 = ?c0 + ?jn + 1" by (rule BrJ_head0_gen[OF MPT condA JBr])
  have h0X: "entry ?X 0 0 = ?c0 + ?jn + 1 + ?m"
    using entry_funpow_IncrFirst0[OF brMpos] h0B by simp
  have h1X: "entry ?X 1 0 = ?b"
    using entry_funpow_IncrFirst1[OF brMpos] by simp
  \<comment> \<open>NJ of A at J, and the head-lowering congruence\<close>
  have e00A: "entry ?A 0 0 = 0"
  proof -
    have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
    have "?A ! 0 = diagSeq 0 (?m - 1) ! 0" using Ld pos by (simp add: nth_append)
    also have "\<dots> = (0, 0)" using pos by (simp add: diagSeq_def del: upt_Suc)
    finally show ?thesis by (simp add: entry_def)
  qed
  have e10A: "entry ?A 1 0 = 0"
  proof -
    have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
    have "?A ! 0 = diagSeq 0 (?m - 1) ! 0" using Ld pos by (simp add: nth_append)
    also have "\<dots> = (0, 0)" using pos by (simp add: diagSeq_def del: upt_Suc)
    finally show ?thesis by (simp add: entry_def)
  qed
  have NJA: "NJ ?A J = (?m + ?jn + 1, ?b) # tl ?X"
    unfolding NJ_def using e00A e10A jnA npA brAJ by simp
  have Xcons: "?X = (?c0 + ?jn + 1 + ?m, ?b) # tl ?X"
  proof -
    have c: "?X = hd ?X # tl ?X" using Xne by simp
    have "hd ?X = (entry ?X 0 0, entry ?X 1 0)"
      using Xne by (cases ?X) (auto simp: entry_def)
    thus ?thesis using c h0X h1X by simp
  qed
  have strict: "\<And>q. 1 \<le> q \<Longrightarrow> q < Lng ((?c0 + ?jn + 1 + ?m, ?b) # tl ?X)
                 \<Longrightarrow> ?c0 + ?jn + 1 + ?m < entry ((?c0 + ?jn + 1 + ?m, ?b) # tl ?X) 0 q"
  proof -
    fix q assume q1: "1 \<le> q" and qL: "q < Lng ((?c0 + ?jn + 1 + ?m, ?b) # tl ?X)"
    have qX: "q < Lng ?X" using qL Xcons brMpos by simp
    from Br_component_nonmulti[OF MPT JBr] show
      "?c0 + ?jn + 1 + ?m < entry ((?c0 + ?jn + 1 + ?m, ?b) # tl ?X) 0 q"
    proof
      assume z: "zeroT ?B"
      have "Lng ?B = 1" using z by (simp add: zeroT_def)
      hence "Lng ?X = 1" by simp
      thus ?thesis using q1 qX by simp
    next
      assume mB: "monoT ?B"
      have XT: "?X \<in> T_PS" using Xne by (simp add: T_PS_def)
      have monoX: "monoT ?X" by (induction ?m) (use mB in \<open>simp_all add: IncrFirst_monoT_eq\<close>)
      have "entry ?X 0 0 < entry ?X 0 q" by (rule mono_tail_row0_strict[OF XT monoX q1 qX])
      moreover have "entry ((?c0 + ?jn + 1 + ?m, ?b) # tl ?X) 0 q = entry ?X 0 q"
        using Xcons by simp
      ultimately show ?thesis using h0X by simp
    qed
  qed
  have ab: "?m + ?jn + 1 \<le> ?c0 + ?jn + 1 + ?m" by simp
  have cong: "congR (NJ ?A J) ?X"
    using congR_head0_lower[OF ab strict] NJA Xcons by simp
  have NJne: "NJ ?A J \<noteq> []" using NJA by simp
  have NJT: "NJ ?A J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have redeq: "Red (NJ ?A J) = Red ?X" by (rule cdn_red_cong[OF cong NJT])
  \<comment> \<open>arithmetic: lift exponent undoes the rebase down to the m00-normalization\<close>
  have eJ: "Joints ?A ! J + 1 - npJ ?A J = ?m + ?jn + 1 - ?b" using jnA npA by simp
  have IHmap: "Red ?X = map (\<lambda>p. (fst p - (?c0 + ?jn + 1 + ?m) + ?b, snd p)) ?X"
    using IH rebase_as_pair_map[of ?X "entry ?X 0 0" "entry ?X 1 0"] h0X h1X by simp
  have geB: "\<And>j. j < Lng ?B \<Longrightarrow> ?c0 + ?jn + 1 \<le> entry ?B 0 j"
  proof -
    fix j assume jB: "j < Lng ?B"
    from Br_component_nonmulti[OF MPT JBr] show "?c0 + ?jn + 1 \<le> entry ?B 0 j"
    proof
      assume z: "zeroT ?B"
      have "Lng ?B = 1" using z by (simp add: zeroT_def)
      hence "j = 0" using jB by simp
      thus ?thesis using h0B by simp
    next
      assume mB: "monoT ?B"
      have BT: "?B \<in> T_PS" using brMne by (simp add: T_PS_def)
      have "entry ?B 0 0 \<le> entry ?B 0 j" by (rule entry0_ge_min[OF BT mB jB])
      thus ?thesis using h0B by simp
    qed
  qed
  show ?thesis
  proof -
    have "(IncrFirst ^^ (Joints ?A ! J + 1 - npJ ?A J)) (Red (NJ ?A J))
          = (IncrFirst ^^ (?m + ?jn + 1 - ?b)) (Red ?X)" using eJ redeq by simp
    also have "\<dots> = map (\<lambda>p. (fst p + (?m + ?jn + 1 - ?b), snd p))
                       (map (\<lambda>p. (fst p - (?c0 + ?jn + 1 + ?m) + ?b, snd p)) ?X)"
      using IHmap funpow_IncrFirst_as_map by simp
    also have "\<dots> = map (\<lambda>p. (fst p - ?c0 + ?m, snd p)) ?B"
    proof -
      have Xmap: "?X = map (\<lambda>p. (fst p + ?m, snd p)) ?B"
        by (rule funpow_IncrFirst_as_map)
      show ?thesis
      proof (rule nth_equalityI)
        show "length (map (\<lambda>p. (fst p + (?m + ?jn + 1 - ?b), snd p))
                       (map (\<lambda>p. (fst p - (?c0 + ?jn + 1 + ?m) + ?b, snd p)) ?X))
              = length (map (\<lambda>p. (fst p - ?c0 + ?m, snd p)) ?B)"
          using Xmap by simp
      next
        fix j assume "j < length (map (\<lambda>p. (fst p + (?m + ?jn + 1 - ?b), snd p))
                       (map (\<lambda>p. (fst p - (?c0 + ?jn + 1 + ?m) + ?b, snd p)) ?X))"
        hence jB: "j < Lng ?B" by simp
        have jX: "j < Lng ?X" using jB by simp
        have xval: "fst (?X ! j) = fst (?B ! j) + ?m"
          using Xmap jB by simp
        have yval: "snd (?X ! j) = snd (?B ! j)"
          using Xmap jB by simp
        have gej: "?c0 + ?jn + 1 \<le> fst (?B ! j)"
          using geB[OF jB] by (simp add: entry_def)
        have arith: "fst (?B ! j) + ?m - (?c0 + ?jn + 1 + ?m) + ?b
                       + (?m + ?jn + 1 - ?b)
                     = fst (?B ! j) - ?c0 + ?m"
          using gej nple by linarith
        show "map (\<lambda>p. (fst p + (?m + ?jn + 1 - ?b), snd p))
                (map (\<lambda>p. (fst p - (?c0 + ?jn + 1 + ?m) + ?b, snd p)) ?X) ! j
              = map (\<lambda>p. (fst p - ?c0 + ?m, snd p)) ?B ! j"
          using jX jB xval yval arith by simp
      qed
    qed
    finally show ?thesis .
  qed
qed


text \<open>§6.5 monoCong MAIN (closed form): for a non-multi RedCondA sequence, Red is
  exactly the row-0 rebase by \<open>-m\<^sub>0\<^sub>0 + m\<^sub>1\<^sub>0\<close>.  Strong induction on Lng; zeroT
  collapses to [(0,0)]; the core case is @{thm [source] Red_rebase_core}; the
  shift case routes through shiftRow0 and the core case (components of the
  shifted sequence are strictly shorter than M, so the master IH still feeds
  the core engine).  The m10>0 case is the remaining residual (coreReduce
  branch-structure bricks, see memory pss-65-monocong).
  Empirically exhaustive: 12400 cases (len<=5, e<=3), 0 mismatches.\<close>

lemma drop_diagSeq:
  assumes "k \<le> t"
  shows "drop k (diagSeq 0 t) = diagSeq k t"
  using assms by (simp add: diagSeq_def drop_map)

text \<open>§6.5 m10>0 stage-2 (b7): the VALUE of Red (coreReduce M) -- the diagonal up
  to the lifted trunk followed by the m00-rebase images of the M-branch
  components (uniformly, the branches list being empty in the trunk-whole case).\<close>

lemma Red_coreReduce_eq:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
    and pos: "0 < entry M 1 0"
    and IH: "\<And>X. Lng X < Lng M \<Longrightarrow> X \<in> T_PS \<Longrightarrow> RedCondA X \<Longrightarrow> \<not> multiT X
              \<Longrightarrow> Red X = map (\<lambda>j. (entry X 0 j - entry X 0 0 + entry X 1 0,
                                     entry X 1 j)) [0..<Lng X]"
  shows "Red (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)
         = diagSeq 0 (entry M 1 0 + TrMax M)
           @ concat (map (\<lambda>J. map (\<lambda>p. (fst p - entry M 0 0 + entry M 1 0, snd p))
                                 (Br M ! J))
                         [0..<Lng (Br M)])"
proof -
  let ?m = "entry M 1 0"  let ?c0 = "entry M 0 0"
  let ?f = "\<lambda>p. (fst p - ?c0 + ?m, snd p)"
  define A where "A = diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
  have LA: "Lng A = ?m + Lng M" using Ld A_def by simp
  have LApos: "0 < Lng A" using LA LMpos by simp
  have Ane: "A \<noteq> []" using LApos length_greater_0_conv by blast
  have AT: "A \<in> T_PS" using Ane by (simp add: T_PS_def)
  have crM: "coreReduce M = A" using coreReduce_m10pos_form[OF pos] A_def by simp
  have monoA: "monoT A" using coreReduce_monoT_m10_pos[OF MT mono pos] crM by simp
  have domA: "Red_dom A" by (rule m_6_5_Red_welldef[OF AT])
  have nzA: "\<not> zeroT A" using monoA by (simp add: monoT_def)
  have nmuA: "\<not> multiT A" using monoA by (simp add: multiT_def)
  have headA: "A ! 0 = (0, 0)"
  proof -
    have "A ! 0 = diagSeq 0 (?m - 1) ! 0" using Ld pos A_def by (simp add: nth_append)
    also have "\<dots> = (0, 0)" using pos by (simp add: diagSeq_def del: upt_Suc)
    finally show ?thesis .
  qed
  have e00A: "entry A 0 0 = 0" using headA by (simp add: entry_def)
  have e10A: "entry A 1 0 = 0" using headA by (simp add: entry_def)
  have trA: "TrMax A = ?m + TrMax M"
    using TrMax_coreReduce[OF MT condA mono pos] A_def by simp
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have goal: "Red A = diagSeq 0 (?m + TrMax M)
                @ concat (map (\<lambda>J. map ?f (Br M ! J)) [0..<Lng (Br M)])"
  proof (cases "TrMax M = Lng M - 1")
    case True
    have aw: "TrMax A = Lng A - 1" using trA True LA LMpos by linarith
    have rA: "Red A = diagSeq (entry A 1 0) (entry A 1 0 + (Lng A - 1))"
      using Red.psimps[OF domA] nzA nmuA e00A e10A aw by (simp add: Let_def)
    have rA': "Red A = diagSeq 0 (?m + TrMax M)"
      using rA e10A trA aw by simp
    have "Br M = []" using True by (simp add: Br_def)
    thus ?thesis using rA' by simp
  next
    case False
    have tlt: "TrMax M < Lng M - 1" using tb False by linarith
    have awne: "TrMax A \<noteq> Lng A - 1" using trA LA LMpos tlt by linarith
    have rA: "Red A = diagSeq 0 (TrMax A)
                @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints A ! J + 1 - npJ A J))
                                     (Red (NJ A J))) [0..<Lng (Br A)])"
      using Red.psimps[OF domA] nzA nmuA e00A e10A awne
      by (simp add: Let_def NJ_def npJ_def)
    have brA: "Br A = map (IncrFirst ^^ ?m) (Br M)"
      using Br_coreReduce[OF MT condA mono pos] A_def by simp
    have lenBrA: "Lng (Br A) = Lng (Br M)" using brA by simp
    have blocks: "\<And>J. J < Lng (Br M) \<Longrightarrow>
                    (IncrFirst ^^ (Joints A ! J + 1 - npJ A J)) (Red (NJ A J))
                    = map ?f (Br M ! J)"
    proof -
      fix J assume JBr: "J < Lng (Br M)"
      let ?X = "(IncrFirst ^^ ?m) (Br M ! J)"
      have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
      have brMne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF MPT JBr])
      have brMpos: "0 < Lng (Br M ! J)" using brMne by (cases "Br M ! J") auto
      have Xne: "?X \<noteq> []"
      proof -
        have "0 < Lng ?X" using brMpos by simp
        thus ?thesis using length_greater_0_conv by blast
      qed
      have XT: "?X \<in> T_PS" using Xne by (simp add: T_PS_def)
      have condAX: "RedCondA ?X"
        by (rule RedCondA_funpow_IncrFirst[OF RedCondA_BrJ[OF MPT condA JBr]])
      have nmuX: "\<not> multiT ?X"
        using Br_component_nonmulti[OF MPT JBr] multiT_funpow_IncrFirst[of ?m "Br M ! J"]
        by (auto simp: multiT_def)
      have lb: "Lng ?X < Lng M"
      proof -
        let ?S = "seg M (TrMax M + 1) (Lng M - 1)"
        have brQ: "Br M = P ?S" using False by (simp add: Br_def)
        have JP: "J < length (P ?S)" using JBr brQ by simp
        have "Lng (Br M ! J) \<le> Lng (concat (P ?S))"
          using length_nth_le_concat[OF JP] brQ by simp
        also have "\<dots> = Lng ?S" using idxsum_concat_P[of ?S] by simp
        also have "\<dots> < Lng M" using tlt by simp
        finally show ?thesis by simp
      qed
      have IHX: "Red ?X = map (\<lambda>j. (entry ?X 0 j - entry ?X 0 0 + entry ?X 1 0,
                                     entry ?X 1 j)) [0..<Lng ?X]"
        by (rule IH[OF lb XT condAX nmuX])
      show "(IncrFirst ^^ (Joints A ! J + 1 - npJ A J)) (Red (NJ A J))
            = map ?f (Br M ! J)"
        using coreReduce_block_value[OF MT condA mono pos JBr IHX] A_def by simp
    qed
    have maps: "map (\<lambda>J. (IncrFirst ^^ (Joints A ! J + 1 - npJ A J)) (Red (NJ A J)))
                    [0..<Lng (Br A)]
                = map (\<lambda>J. map ?f (Br M ! J)) [0..<Lng (Br M)]"
      using lenBrA by (intro map_cong) (use blocks in simp_all)
    show ?thesis using rA maps trA by simp
  qed
  show ?thesis using goal A_def by simp
qed

end
