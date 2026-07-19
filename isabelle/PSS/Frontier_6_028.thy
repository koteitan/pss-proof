theory Frontier_6_028
  imports Support_6_010
begin

text \<open>PROTOTYPE (worktree): green reusable helpers for the §6.8 prop1 slice
  bookkeeping (\<open>take\<close>/\<open>drop\<close> of a \<open>seg\<close>, slices of a \<open>diagSeq\<close>, \<open>oper\<close> agreeing
  with \<open>M\<close> below \<open>Lng M - 1\<close>), used by the conditional \<open>Br\<close> induction below.\<close>

lemma take_seg:
  assumes c1: "1 \<le> c" and cb: "c \<le> Suc b - a"
  shows "take c (seg M a b) = seg M a (a + c - 1)"
proof -
  have ac: "a + c \<le> Suc b" using c1 cb by linarith
  have e1: "Suc (a + c - 1) = a + c" using c1 by simp
  have e2: "seg M a (a + c - 1) = map (\<lambda>j. M ! j) [a..<a + c]"
    using e1 by (simp add: seg_def del: upt_Suc)
  have "take c (seg M a b) = map (\<lambda>j. M ! j) (take c [a..<Suc b])"
    by (simp add: seg_def take_map del: upt_Suc)
  also have "\<dots> = map (\<lambda>j. M ! j) [a..<a + c]"
    using ac by (simp add: take_upt min.absorb1 del: upt_Suc)
  finally show ?thesis using e2 by simp
qed

text \<open>§6.8 sub-case A "butlast bridge".  When the last \<open>Pcut\<close> of a multi-term
  segment \<open>seg X a b\<close> sits at its right endpoint (\<open>Pcut (seg X a b) = b - a\<close>),
  dropping the last index \<open>b\<close> removes exactly the last \<open>P\<close>-component: the
  \<open>P\<close>-decomposition of \<open>seg X a (b-1)\<close> is the \<open>butlast\<close> of that of \<open>seg X a b\<close>.
  Minimal hypotheses (pinned empirically, 0 failures at depth 6): \<open>a < b\<close>,
  \<open>multiT (seg X a b)\<close>, and \<open>Pcut (seg X a b) = b - a\<close>.  Without \<open>Pcut = b - a\<close>
  it is false (the dropped index lies inside a non-final component); for a mono
  segment it is false too (then \<open>P\<close> is a singleton and \<open>butlast\<close> is empty).\<close>

lemma P_seg_butlast_bridge:
  assumes ab: "a < b"
    and multi: "multiT (seg X a b)"
    and pc: "Pcut (seg X a b) = b - a"
  shows "P (seg X a (b - 1)) = butlast (P (seg X a b))"
proof -
  have L: "1 < Lng (seg X a b)" using ab by (simp add: Lng_seg)
  have but: "butlast (P (seg X a b)) = P (take (Pcut (seg X a b)) (seg X a b))"
    using poper_last_P_multi[OF multi L] by simp
  have c1: "1 \<le> b - a" using ab by simp
  have cb: "b - a \<le> Suc b - a" by simp
  have "take (Pcut (seg X a b)) (seg X a b) = seg X a (a + (b - a) - 1)"
    using take_seg[OF c1 cb] pc by simp
  also have "a + (b - a) - 1 = b - 1" using ab by simp
  finally have "take (Pcut (seg X a b)) (seg X a b) = seg X a (b - 1)" .
  with but show ?thesis by simp
qed

lemma drop_seg:
  shows "drop c (seg M a b) = seg M (a + c) b"
proof -
  have "drop c (seg M a b) = map (\<lambda>j. M ! j) (drop c [a..<Suc b])"
    by (simp add: seg_def drop_map del: upt_Suc)
  also have "\<dots> = map (\<lambda>j. M ! j) [a + c..<Suc b]"
    by (simp add: drop_upt del: upt_Suc)
  finally show ?thesis by (simp add: seg_def del: upt_Suc)
qed

text \<open>A slice of the rank-0 standard form \<open>diagSeq u v\<close> is again a \<open>diagSeq\<close>,
  hence non-multi: this is the base case of the rank induction.\<close>

lemma seg_diagSeq:
  assumes ab: "a \<le> b" and bv: "b \<le> v - u" and uv: "u \<le> v"
  shows "seg (diagSeq u v) a b = diagSeq (u + a) (u + b)"
proof (rule nth_equalityI)
  have l1: "length (seg (diagSeq u v) a b) = Suc b - a" by simp
  have l2: "length (diagSeq (u + a) (u + b)) = Suc (u + b) - (u + a)" by simp
  show leq: "length (seg (diagSeq u v) a b) = length (diagSeq (u + a) (u + b))"
    using l1 l2 ab by presburger
  fix i assume "i < length (seg (diagSeq u v) a b)"
  hence ic: "i < Suc b - a" by simp
  have ai: "a + i < Suc v - u" using ic bv ab uv by linarith
  have ib: "i < Suc (u + b) - (u + a)" using ic by linarith
  have "seg (diagSeq u v) a b ! i = diagSeq u v ! (a + i)" using ic by (rule seg_nth_eq)
  also have "\<dots> = (u + (a + i), u + (a + i))" by (rule diagSeq_nth[OF ai])
  also have "\<dots> = ((u + a) + i, (u + a) + i)" by simp
  also have "\<dots> = diagSeq (u + a) (u + b) ! i" by (rule diagSeq_nth[symmetric, OF ib])
  finally show "seg (diagSeq u v) a b ! i = diagSeq (u + a) (u + b) ! i" .
qed

text \<open>The fundamental sequence \<open>M[n]\<close> agrees with \<open>M\<close> on every index strictly
  below \<open>Lng M - 1\<close>: in the two degenerate \<open>oper\<close> cases \<open>M[n] = Pred M = butlast M\<close>,
  and in the generic case \<open>M[n] = take j0 M @ B\<^sub>0 @ \<dots>\<close> with \<open>take j0 M @ B\<^sub>0 =
  take j1 M\<close> (the \<open>k=0\<close> block \<open>B\<^sub>0\<close> carries the unshifted \<open>M\<close>-entries on \<open>[j0..<j1]\<close>).
  This lets a slice ending before \<open>Lng M - 1\<close> reduce to a slice of \<open>M\<close>.\<close>

lemma oper_nth_lt:
  assumes M: "M \<in> T_PS" and L: "1 < Lng M" and n: "n \<ge> 1" and i: "i < Lng M - 1"
  shows "(M[n]) ! i = M ! i"
proof -
  let ?j1 = "Lng M - 1"
  have nz: "?j1 \<noteq> 0" using L by simp
  show ?thesis
  proof (cases "entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0")
    case True
    hence op: "M[n] = Pred M" using nz by (simp add: oper_def Let_def)
    have "Pred M = butlast M" using L by (simp add: Pred_def)
    thus ?thesis using op i by (simp add: nth_butlast)
  next
    case notzero: False
    show ?thesis
    proof (cases "hasParent M (idx1 M ?j1) ?j1")
      case False
      hence op: "M[n] = Pred M" using notzero nz by (simp add: oper_def Let_def)
      have "Pred M = butlast M" using L by (simp add: Pred_def)
      thus ?thesis using op i by (simp add: nth_butlast)
    next
      case haspar: True
      let ?i1 = "idx1 M ?j1"
      let ?j0 = "parent M ?i1 ?j1"
      let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
      let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
      let ?f = "\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) [?j0..<?j1]"
      have parR: "nextR M ?i1 ?j0 ?j1"
        using haspar unfolding hasParent_def parent_def by (rule theI')
      have j0lt: "?j0 < ?j1" using poper_nextR_imp_le0[OF parR] by simp
      have oper: "M[n] = take ?j0 M @ concat (map ?f [0..<n])"
        using poper_oper_expand[OF L notzero haspar, of n] by (simp add: Let_def)
      have n0: "0 < n" using n by simp
      have blocks_hd: "concat (map ?f [0..<n]) = ?f 0 @ concat (map ?f [1..<n])"
        using n0 by (subst upt_conv_Cons) auto
      have operB: "M[n] = take ?j0 M @ ?f 0 @ concat (map ?f [1..<n])"
        using oper blocks_hd by simp
      have lenj0: "length (take ?j0 M) = ?j0" using j0lt L by simp
      have lenB0: "length (?f 0) = ?j1 - ?j0" by simp
      show ?thesis
      proof (cases "i < ?j0")
        case True
        have "(M[n]) ! i = (take ?j0 M) ! i"
          using operB True lenj0 by (simp add: nth_append)
        also have "\<dots> = M ! i" using True by (simp add: nth_take)
        finally show ?thesis .
      next
        case False
        hence ge: "?j0 \<le> i" by simp
        have iltj1: "i < ?j1" using i by simp
        have off: "i - ?j0 < ?j1 - ?j0" using ge iltj1 by linarith
        have B0i: "?f 0 ! (i - ?j0) = M ! i"
        proof -
          have idx: "[?j0..<?j1] ! (i - ?j0) = i" using off ge by (simp add: nth_upt)
          have "?f 0 ! (i - ?j0) = (entry M 0 i, entry M 1 i)"
            using off idx by (simp add: nth_map del: upt_Suc)
          also have "\<dots> = M ! i" by (rule entry_pair)
          finally show ?thesis .
        qed
        have "(M[n]) ! i = (?f 0 @ concat (map ?f [1..<n])) ! (i - ?j0)"
          using operB ge lenj0 by (simp add: nth_append)
        also have "\<dots> = ?f 0 ! (i - ?j0)" using off lenB0 by (simp add: nth_append)
        also have "\<dots> = M ! i" by (rule B0i)
        finally show ?thesis .
      qed
    qed
  qed
qed



text \<open>A \<open>diagSeq\<close> is trunk-only: \<open>TrMax = Lng - 1\<close>, hence \<open>Br (diagSeq u v) = []\<close>.
  Used in the base case (\<open>k = 0\<close>) of the §6.8 prop1 rank induction.\<close>

lemma Br_diagSeq:
  assumes uv: "u \<le> v"
  shows "Br (diagSeq u v) = []"
proof -
  have "TrMax (diagSeq u v) = v - u" by (rule TrMax_diagSeq[OF uv])
  moreover have "Lng (diagSeq u v) - 1 = v - u" using uv by simp
  ultimately have "TrMax (diagSeq u v) = Lng (diagSeq u v) - 1" by simp
  thus ?thesis by (simp add: Br_def)
qed

text \<open>Domination of branch components by their head pair \<open>C\<^bsub>0\<^esub>\<close>, in the
  \<open>descending\<close> order (row-0 weakly larger, tie-broken by row-1 weakly larger).
  \<open>descending Q\<close> is exactly \<open>cdom\<close>-monotonicity of \<open>Q\<close> along its indices, so the
  §6.8 prop1 sub-cases — which all assemble \<open>Br(M') = take J\<^sub>1 (Br N') @ blocks\<close> —
  reduce to \<open>cdom\<close> transitivity plus a single junction inequality.\<close>

definition cdom :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "cdom C D \<longleftrightarrow> entry D 0 0 \<le> entry C 0 0
                \<and> (entry C 0 0 = entry D 0 0 \<longrightarrow> entry D 1 0 \<le> entry C 1 0)"

lemma cdom_trans:
  assumes CD: "cdom C D" and DE: "cdom D E" shows "cdom C E"
proof -
  from CD have a: "entry D 0 0 \<le> entry C 0 0"
    and a': "entry C 0 0 = entry D 0 0 \<longrightarrow> entry D 1 0 \<le> entry C 1 0"
    by (auto simp: cdom_def)
  from DE have b: "entry E 0 0 \<le> entry D 0 0"
    and b': "entry D 0 0 = entry E 0 0 \<longrightarrow> entry E 1 0 \<le> entry D 1 0"
    by (auto simp: cdom_def)
  show ?thesis unfolding cdom_def
  proof (intro conjI impI)
    show "entry E 0 0 \<le> entry C 0 0" using a b by simp
    assume "entry C 0 0 = entry E 0 0"
    hence "entry C 0 0 = entry D 0 0" and "entry D 0 0 = entry E 0 0" using a b by auto
    thus "entry E 1 0 \<le> entry C 1 0" using a' b' by simp
  qed
qed

text \<open>\<open>descending\<close> re-expressed as \<open>cdom\<close>-monotonicity along the index.\<close>

lemma descending_via_cdom:
  "descending Q \<longleftrightarrow> (\<forall>J0 J1. J0 \<le> J1 \<longrightarrow> J1 < Lng Q \<longrightarrow> cdom (Q ! J0) (Q ! J1))"
proof (cases "Q = []")
  case True thus ?thesis by (simp add: descending_def cdom_def)
next
  case False
  hence pos: "0 < Lng Q" by simp
  have key: "(J1 \<le> Lng Q - 1) = (J1 < Lng Q)" for J1 using pos by linarith
  show ?thesis
    unfolding descending_def cdom_def
    by (metis key)
qed

lemma descendingI_cdom:
  assumes "\<And>J0 J1. J0 \<le> J1 \<Longrightarrow> J1 < Lng Q \<Longrightarrow> cdom (Q ! J0) (Q ! J1)"
  shows "descending Q"
  using assms descending_via_cdom by blast

lemma descending_cdomD:
  assumes "descending Q" "J0 \<le> J1" "J1 < Lng Q"
  shows "cdom (Q ! J0) (Q ! J1)"
  using assms descending_via_cdom by blast

text \<open>Concatenation: \<open>A @ B\<close> is descending iff both are and the junction
  \<open>cdom (last A) (B\<^bsub>0\<^esub>)\<close> holds.  The within-\<open>A\<close>, junction and within-\<open>B\<close> steps
  compose by @{thm [source] cdom_trans}.\<close>

lemma descending_append:
  assumes dA: "descending A" and dB: "descending B"
    and junc: "A \<noteq> [] \<Longrightarrow> B \<noteq> [] \<Longrightarrow> cdom (last A) (B ! 0)"
  shows "descending (A @ B)"
proof (rule descendingI_cdom)
  fix J0 J1 assume le: "J0 \<le> J1" and j1: "J1 < Lng (A @ B)"
  let ?lA = "Lng A"
  show "cdom ((A @ B) ! J0) ((A @ B) ! J1)"
  proof (cases "J1 < ?lA")
    case True \<comment> \<open>both in \<open>A\<close>\<close>
    have "cdom (A ! J0) (A ! J1)" using descending_cdomD[OF dA le True] .
    thus ?thesis using True le by (simp add: nth_append)
  next
    case j1A: False
    hence j1B: "J1 - ?lA < Lng B" using j1 by auto
    have eJ1: "(A @ B) ! J1 = B ! (J1 - ?lA)" using j1A by (simp add: nth_append)
    show ?thesis
    proof (cases "J0 < ?lA")
      case True \<comment> \<open>\<open>J0\<close> in \<open>A\<close>, \<open>J1\<close> in \<open>B\<close>: chain through \<open>last A\<close> and \<open>B\<^bsub>0\<^esub>\<close>\<close>
      have Ane: "A \<noteq> []" using True by auto
      have Bne: "B \<noteq> []" using j1B by auto
      have eJ0: "(A @ B) ! J0 = A ! J0" using True by (simp add: nth_append)
      have lastA: "A ! (?lA - 1) = last A" using Ane by (simp add: last_conv_nth)
      have B0: "B ! 0 = B ! 0" ..
      have s1: "cdom (A ! J0) (last A)"
        using descending_cdomD[OF dA, of J0 "?lA - 1"] True lastA by simp
      have s2: "cdom (last A) (B ! 0)" using junc[OF Ane Bne] .
      have s3: "cdom (B ! 0) (B ! (J1 - ?lA))"
        using descending_cdomD[OF dB, of 0 "J1 - ?lA"] j1B by simp
      have "cdom (A ! J0) (B ! (J1 - ?lA))"
        using cdom_trans[OF cdom_trans[OF s1 s2] s3] .
      thus ?thesis using eJ0 eJ1 by simp
    next
      case False \<comment> \<open>both in \<open>B\<close>\<close>
      hence j0A: "\<not> J0 < ?lA" .
      have le': "J0 - ?lA \<le> J1 - ?lA" using le by simp
      have eJ0: "(A @ B) ! J0 = B ! (J0 - ?lA)" using j0A by (simp add: nth_append)
      have "cdom (B ! (J0 - ?lA)) (B ! (J1 - ?lA))"
        using descending_cdomD[OF dB le' j1B] .
      thus ?thesis using eJ0 eJ1 by simp
    qed
  qed
qed

text \<open>A prefix of a descending list is descending.\<close>

lemma descending_take:
  assumes "descending Q" shows "descending (take m Q)"
proof (rule descendingI_cdom)
  fix J0 J1 assume le: "J0 \<le> J1" and j1: "J1 < Lng (take m Q)"
  have j1Q: "J1 < Lng Q" using j1 by simp
  have "cdom (Q ! J0) (Q ! J1)" using descending_cdomD[OF assms le j1Q] .
  thus "cdom (take m Q ! J0) (take m Q ! J1)"
    using j1 le by simp
qed

text \<open>A list all of whose entries carry the same head pair \<open>(entry _ 0 0, entry _ 1 0)\<close>
  is \<open>descending\<close> (every \<open>cdom\<close> step is a reflexive equality).  This is the
  closing fact for the \<open>i\<^sub>1=0\<close> branch blocks (article 1488/1494/1500): the
  \<open>n\<close> repeated copies of \<open>seg N j\<^sub>0\<^sup>N (j\<^sub>1\<^sup>N-1)\<close> all start with \<open>N\<^bsub>j\<^sub>0\<^sup>N\<^esub>\<close>.\<close>

lemma descending_const_head:
  assumes "\<And>J. J < Lng Q \<Longrightarrow> entry (Q ! J) 0 0 = v0 \<and> entry (Q ! J) 1 0 = v1"
  shows "descending Q"
proof (rule descendingI_cdom)
  fix J0 J1 assume "J0 \<le> J1" and j1: "J1 < Lng Q"
  hence j0: "J0 < Lng Q" by simp
  have "entry (Q ! J0) 0 0 = entry (Q ! J1) 0 0"
    using assms[OF j0] assms[OF j1] by simp
  moreover have "entry (Q ! J0) 1 0 = entry (Q ! J1) 1 0"
    using assms[OF j0] assms[OF j1] by simp
  ultimately show "cdom (Q ! J0) (Q ! J1)" by (simp add: cdom_def)
qed

end
