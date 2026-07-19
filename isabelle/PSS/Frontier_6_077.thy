theory Frontier_6_077
  imports Support_6_056
begin

text \<open>§6.7 oper-tiling brick (Front B, le0 base-correspondence, FORWARD):  a
  row-0 reachability chain in \<open>N\<close> CONFINED to the active slice \<open>[j\<^sub>0, j\<^sub>1)\<close> lifts
  verbatim into block \<open>q\<close> of \<open>N[n]\<close>.  Confinement is expressed as the
  reflexive-transitive closure of the RESTRICTED step relation
  \<open>nextrel0 N a b \<and> j\<^sub>0 \<le> a \<and> b < j\<^sub>1\<close>; each such step lifts by
  @{thm [source] oper_gen_nextrel0_within} (which needs exactly \<open>j\<^sub>0 \<le> a\<close>,
  \<open>b < j\<^sub>1\<close>, \<open>q < n\<close>), and \<open>le0_def\<close> stitches the lifted steps back into a
  \<open>le0 (N[n])\<close>.  This is the reusable core of the row-1 parent reflection (the
  le0-reachable predecessors of a within-block column map, by period base, onto
  the le0-reachable predecessors of its base column).  Empirically 0-fail
  (python/_fb_le0_forward2.py: 3510/3510 block-confined lifts).\<close>

lemma oper_gen_le0_within_forward:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and a0: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> a"
    and aj1: "a < Lng N - 1"
    and chain: "(\<lambda>u v. nextrel0 N u v
                  \<and> parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> u
                  \<and> v < Lng N - 1)\<^sup>*\<^sup>* a b"
  shows "le0 ((N::pairseq)[n])
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (a - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (b - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?base = "?j0 + q * ?w"
  let ?R = "\<lambda>u v. nextrel0 N u v \<and> ?j0 \<le> u \<and> v < ?j1"
  let ?lift = "\<lambda>z. ?base + (z - ?j0)"
  have w0: "0 < ?w" using j0lt by linarith
  have LngNn: "Lng (N[n]) = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have aw: "a - ?j0 < ?w" using a0 aj1 by linarith
  have liftalt: "?lift a < Lng (N[n])"
  proof -
    have "?lift a < ?j0 + q * ?w + ?w" using aw by linarith
    also have "?j0 + q * ?w + ?w = ?j0 + (q + 1) * ?w" by simp
    also have "\<dots> \<le> ?j0 + n * ?w"
      using mult_le_mono1[of "q+1" n ?w] qn by simp
    finally show ?thesis using LngNn by simp
  qed
  from chain show ?thesis
  proof (induction rule: rtranclp_induct)
    case base
    show ?case using liftalt by (simp add: le0_def)
  next
    case (step y z)
    have ystep: "?R y z" by (rule step.hyps(2))
    have nyz: "nextrel0 N y z" using ystep by simp
    have y0: "?j0 \<le> y" using ystep by simp
    have zj1: "z < ?j1" using ystep by simp
    \<comment> \<open>lift the single step \<open>nextrel0 N y z\<close> into block \<open>q\<close>\<close>
    have lifted: "nextrel0 (N[n]) (?lift y) (?lift z)"
      by (rule oper_gen_nextrel0_within[OF L notzero hp j0lt qn y0 zj1 nyz])
    have hop: "(nextrel0 (N[n]))\<^sup>*\<^sup>* (?lift y) (?lift z)"
      using lifted by (rule r_into_rtranclp)
    have IH: "le0 (N[n]) (?lift a) (?lift y)" by (rule step.IH)
    have alt: "?lift a < Lng (N[n])" using IH by (simp add: le0_def)
    have zlt: "?lift z < Lng (N[n])" using lifted by (simp add: nextrel0_def)
    have ch1: "(nextrel0 (N[n]))\<^sup>*\<^sup>* (?lift a) (?lift y)"
      using IH by (simp add: le0_def)
    have "(nextrel0 (N[n]))\<^sup>*\<^sup>* (?lift a) (?lift z)"
      using ch1 hop by (rule rtranclp_trans)
    thus ?case using alt zlt by (simp add: le0_def)
  qed
qed


text \<open>§6.7 oper-tiling ROW-1 parent CHARACTERIZATION (Front A, the \<open>i\<^sub>1 = 0\<close>
  / d0zero CLEANER case).  This is the LAST brick: for the tiling branch with
  \<open>i\<^sub>1 = 0\<close> and a within-block column \<open>j\<^sub>0 \<le> x < Lng (N[n])\<close> that has a row-1
  parent, the period base \<open>x' = base x\<close> has a row-1 parent in \<open>N\<close> and the row-1
  \<open>N\<close>-entries of the two parents agree.  Built on the verbatim per-block
  periodicity of BOTH rows (\<open>d\<^sub>0 = d\<^sub>1 = 0\<close>) plus the block-confinement of \<open>le0\<close>
  (@{thm [source] oper_d0zero_le0_confined}).  Empirically 0-fail
  (/tmp/charac_i0_check.py: 1758/1758; le0 base-correspondence 17604/17604).\<close>

text \<open>Helper (i0, row-agnostic entry base reading): in the \<open>i\<^sub>1 = 0\<close> layout, BOTH
  rows of \<open>N[n]\<close> are verbatim-periodic, so for any column \<open>z < Lng (N[n])\<close> and any
  row \<open>i\<close>, \<open>entry (N[n]) i z = entry N i (base z)\<close> with the period base
  \<open>base z = (if z < j\<^sub>0 then z else j\<^sub>0 + (z - j\<^sub>0) mod w)\<close>.\<close>

lemma oper_d0zero_entryi_base:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and zlt: "z < Lng ((N::pairseq)[n])"
  shows "entry ((N::pairseq)[n]) i z
       = entry N i (if z < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then z
            else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  have j0eq: "?j0 = parent N 0 ?j1" using i1z by simp
  have j0lt': "parent N 0 ?j1 < ?j1" using j0lt j0eq by simp
  have w0: "0 < ?w" using j0lt by linarith
  have lenNn: "Lng ((N::pairseq)[n]) = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  show ?thesis
  proof (cases "z < ?j0")
    case True
    thus ?thesis using operB_gen_entry_prefix[OF L notzero hp True, of n i] by simp
  next
    case False
    hence ge: "?j0 \<le> z" by simp
    let ?q = "(z - ?j0) div ?w"  let ?s = "(z - ?j0) mod ?w"
    have sw: "?s < ?w" using w0 by simp
    have sw': "?s < ?j1 - parent N 0 ?j1" using sw j0eq by simp
    have zmj: "z - ?j0 < n * ?w" using zlt ge lenNn by linarith
    have qn: "?q < n" using less_mult_imp_div_less[OF zmj] .
    have dm: "?q * ?w + ?s = z - ?j0"
      using div_mult_mod_eq[of "z - ?j0" ?w] by (simp add: mult.commute)
    have zsplit: "z = ?j0 + ?q * ?w + ?s" using dm ge by linarith
    \<comment> \<open>both rows read verbatim at the base \<open>j\<^sub>0 + s\<close> (since \<open>d\<^sub>0 = d\<^sub>1 = 0\<close>)\<close>
    have ntheq': "((N::pairseq)[n]) ! (parent N 0 ?j1 + ?q * (?j1 - parent N 0 ?j1) + ?s)
                    = N ! (parent N 0 ?j1 + ?s)"
      by (rule oper_d0zero_nth[OF L notzero hp i1z j0lt' qn sw'])
    have ntheq: "((N::pairseq)[n]) ! (?j0 + ?q * ?w + ?s) = N ! (?j0 + ?s)"
      using ntheq' j0eq by simp
    have "entry ((N::pairseq)[n]) i z = entry N i (?j0 + ?s)"
      using zsplit ntheq by (simp add: entry_def)
    thus ?thesis using False by simp
  qed
qed

text \<open>Helper (i0, BACKWARD in-block single \<open>nextrel0\<close> step): in the \<open>i\<^sub>1 = 0\<close>
  layout block \<open>q\<close> of \<open>N[n]\<close> is a VERBATIM copy of the active slice \<open>[j\<^sub>0,j\<^sub>1)\<close>
  (\<open>d\<^sub>0 = 0\<close>), so a row-0 step \<open>nextrel0 (N[n]) (j\<^sub>0+q\<cdot>w+s\<^sub>u) (j\<^sub>0+q\<cdot>w+s\<^sub>v)\<close> with both
  offsets \<open>< w\<close> is exactly the base step \<open>nextrel0 N (j\<^sub>0+s\<^sub>u) (j\<^sub>0+s\<^sub>v)\<close>.  The
  converse of @{thm [source] oper_gen_nextrel0_within}.  Valley: an intermediate
  \<open>N\<close>-column \<open>j\<^sub>0+t\<close> (\<open>s\<^sub>u < t < s\<^sub>v\<close>) is read off block \<open>q\<close> at the same offset by
  @{thm [source] oper_gen_block_entry0}.\<close>

lemma oper_d0zero_nextrel0_inblock_back:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and su: "su < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and sv: "sv < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and step: "nextrel0 ((N::pairseq)[n])
                  (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                     + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + su)
                  (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                     + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sv)"
  shows "nextrel0 N (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + su)
                    (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + sv)"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?base = "?j0 + q * ?w"
  let ?u = "?base + su"  let ?v = "?base + sv"
  have w0: "0 < ?w" using j0lt by linarith
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  from step have uv: "?u < ?v" and sv0: "entry ?Nn 0 ?u < entry ?Nn 0 ?v"
    and smid: "\<And>z. ?u < z \<Longrightarrow> z < ?v \<Longrightarrow> entry ?Nn 0 ?v \<le> entry ?Nn 0 z"
    by (auto simp: nextrel0_def)
  have suv: "su < sv" using uv by simp
  \<comment> \<open>row-0 readings of the two endpoints (verbatim, \<open>d\<^sub>0 = 0\<close>)\<close>
  have e_u: "entry ?Nn 0 ?u = entry N 0 (?j0 + su)"
    using oper_gen_block_entry0[OF L notzero hp j0lt qn su] i1z by simp
  have e_v: "entry ?Nn 0 ?v = entry N 0 (?j0 + sv)"
    using oper_gen_block_entry0[OF L notzero hp j0lt qn sv] i1z by simp
  have ev: "entry N 0 (?j0 + su) < entry N 0 (?j0 + sv)" using sv0 e_u e_v by simp
  \<comment> \<open>index bounds in \<open>N\<close>\<close>
  have ulN: "?j0 + su < Lng N" using su L j0lt by linarith
  have vlN: "?j0 + sv < Lng N" using sv L j0lt by linarith
  have uvN: "?j0 + su < ?j0 + sv" using suv by simp
  \<comment> \<open>valley in \<open>N\<close>: intermediate \<open>j\<^sub>0+t\<close> (\<open>su<t<sv\<close>) lifts to block \<open>q\<close>\<close>
  have valley: "\<And>j. ?j0 + su < j \<Longrightarrow> j < ?j0 + sv \<Longrightarrow> entry N 0 (?j0 + sv) \<le> entry N 0 j"
  proof -
    fix j assume jlo: "?j0 + su < j" and jhi: "j < ?j0 + sv"
    let ?t = "j - ?j0"
    have jge: "?j0 \<le> j" using jlo by linarith
    have tlt: "?t < sv" using jhi jge by linarith
    have tw: "?t < ?w" using tlt sv by linarith
    have jsplit: "j = ?j0 + ?t" using jge by simp
    let ?z = "?base + ?t"
    have zlo: "?u < ?z" using jlo jge by simp
    have zhi: "?z < ?v" using jhi jge by simp
    have e_z: "entry ?Nn 0 ?z = entry N 0 (?j0 + ?t)"
      using oper_gen_block_entry0[OF L notzero hp j0lt qn tw] i1z by simp
    have "entry ?Nn 0 ?v \<le> entry ?Nn 0 ?z" using smid[OF zlo zhi] .
    thus "entry N 0 (?j0 + sv) \<le> entry N 0 j"
      using e_v e_z jsplit by simp
  qed
  show ?thesis
    unfolding nextrel0_def
    using ulN vlN uvN ev valley by blast
qed

text \<open>Helper (i0, FORWARD slice \<open>le0\<close> lift): a base row-0 chain \<open>le0 N a b\<close> wholly
  inside the active slice (\<open>j\<^sub>0 \<le> a\<close>, \<open>b < j\<^sub>1\<close>) lifts into block \<open>q\<close> of \<open>N[n]\<close>
  (translate by \<open>q\<cdot>w\<close>): \<open>le0 (N[n]) (j\<^sub>0+q\<cdot>w+(a-j\<^sub>0)) (j\<^sub>0+q\<cdot>w+(b-j\<^sub>0))\<close>.  Every node
  of the chain lies in \<open>[a,b] \<subseteq> [j\<^sub>0,j\<^sub>1)\<close>, so each \<open>nextrel0 N\<close> step lifts by
  @{thm [source] oper_gen_nextrel0_within}.  (The \<open>le0\<close>-flavoured restatement of
  @{thm [source] oper_gen_le0_within_forward}, taking a PLAIN \<open>le0 N a b\<close>.)\<close>

lemma oper_d0zero_le0_slice_lift:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and a0: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> a"
    and bj1: "b < Lng N - 1"
    and reach: "le0 N a b"
  shows "le0 ((N::pairseq)[n])
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (a - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (b - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  have chain: "(nextrel0 N)\<^sup>*\<^sup>* a b" using reach by (simp add: le0_def)
  \<comment> \<open>promote to the RESTRICTED closure required by the forward lift, peeling from
     the FRONT so each peeled node \<open>y\<close> has the suffix chain \<open>y \<to>\<^sup>* b\<close> (hence \<open>y \<le> b\<close>)\<close>
  have restrgen: "(nextrel0 N)\<^sup>*\<^sup>* a b \<Longrightarrow> ?j0 \<le> a
                    \<longrightarrow> (\<lambda>u v. nextrel0 N u v \<and> ?j0 \<le> u \<and> v < ?j1)\<^sup>*\<^sup>* a b"
  proof (induction rule: converse_rtranclp_induct)
    case base show ?case by simp
  next
    case (step c y)
    show ?case
    proof
      assume c0: "?j0 \<le> c"
      have ncy: "nextrel0 N c y" by (rule step.hyps(1))
      have yb: "y \<le> b" using step.hyps(2) by (rule nextrel0_rtrancl_mono)
      have cy: "c < y" using ncy by (simp add: nextrel0_def)
      have y0: "?j0 \<le> y" using c0 cy by linarith
      have yj1: "y < ?j1" using yb bj1 by linarith
      have rstep: "nextrel0 N c y \<and> ?j0 \<le> c \<and> y < ?j1" using ncy c0 yj1 by simp
      have tail: "(\<lambda>u v. nextrel0 N u v \<and> ?j0 \<le> u \<and> v < ?j1)\<^sup>*\<^sup>* y b"
        using step.IH y0 by simp
      show "(\<lambda>u v. nextrel0 N u v \<and> ?j0 \<le> u \<and> v < ?j1)\<^sup>*\<^sup>* c b"
        using rstep tail by (rule converse_rtranclp_into_rtranclp)
    qed
  qed
  have restr: "(\<lambda>u v. nextrel0 N u v \<and> ?j0 \<le> u \<and> v < ?j1)\<^sup>*\<^sup>* a b"
    using restrgen[OF chain] a0 by simp
  have aj1: "a < ?j1"
  proof -
    have "a \<le> b" using chain by (rule nextrel0_rtrancl_mono)
    thus ?thesis using bj1 by linarith
  qed
  show ?thesis
    by (rule oper_gen_le0_within_forward[OF L notzero hp j0lt qn a0 aj1 restr])
qed

text \<open>Helper (i0, FORWARD unified single \<open>nextrel0\<close> base step): a row-0 step
  \<open>nextrel0 (N[n]) y z\<close> with both endpoints confined to the prefix and one block
  \<open>q\<close> (\<open>y, z < j\<^sub>0 + (q+1)\<cdot>w\<close>) maps to the base step \<open>nextrel0 N (base y) (base z)\<close>.
  Three regions.  Prefix\<rightarrow>prefix: verbatim (@{thm [source] operB_gen_entry_prefix}).
  Block\<rightarrow>block: @{thm [source] oper_d0zero_nextrel0_inblock_back}.  Cross
  prefix\<rightarrow>block: the target \<open>z\<close> MUST be a block-start (offset \<open>0\<close>), because the
  block-start of \<open>z\<close>'s block carries the row-0 minimum \<open>e\<^sub>0(N,j\<^sub>0)\<close>
  (@{thm [source] parent_block_entry0_min}) which would violate the \<open>nextrel0\<close>
  valley unless \<open>z\<close> itself sits at that minimum; then the step is \<open>nextrel0 N y j\<^sub>0\<close>.
  Empirically 0-fail (/tmp/step_check.py, /tmp/crossbase.py).\<close>

lemma oper_d0zero_nextrel0_base:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and zcf: "z < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (q + 1) * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and step: "nextrel0 ((N::pairseq)[n]) y z"
  shows "nextrel0 N
            (if y < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then y
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            (if z < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then z
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  have j0eq: "?j0 = parent N 0 ?j1" using i1z by simp
  have hp0: "hasParent N 0 ?j1" using hp i1z by simp
  have parR': "nextR N 0 (parent N 0 ?j1) ?j1"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  have parR0: "nextrel0 N ?j0 ?j1" using parR' j0eq by (simp add: nextR_def)
  have parR0u: "nextrel0 N (parent N 0 ?j1) ?j1" using parR0 j0eq by simp
  \<comment> \<open>row-0 block minimum (parent-0 form for @{thm [source] parent_block_entry0_min})\<close>
  have minL: "\<And>s. s < ?w \<Longrightarrow> entry N 0 ?j0 \<le> entry N 0 (?j0 + s)"
  proof -
    fix s assume "s < ?w"
    hence "s < ?j1 - parent N 0 ?j1" using j0eq by simp
    thus "entry N 0 ?j0 \<le> entry N 0 (?j0 + s)"
      using parent_block_entry0_min(1)[OF parR0u] j0eq by simp
  qed
  have minS: "\<And>s. 0 < s \<Longrightarrow> s < ?w \<Longrightarrow> entry N 0 ?j0 < entry N 0 (?j0 + s)"
  proof -
    fix s assume sp: "0 < s" and "s < ?w"
    hence "s < ?j1 - parent N 0 ?j1" using j0eq by simp
    thus "entry N 0 ?j0 < entry N 0 (?j0 + s)"
      using parent_block_entry0_min(2)[OF parR0u] sp j0eq by simp
  qed
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  from step have yz: "y < z" and zlt: "z < Lng ?Nn"
    and sv: "entry ?Nn 0 y < entry ?Nn 0 z"
    and smid: "\<And>j. y < j \<Longrightarrow> j < z \<Longrightarrow> entry ?Nn 0 z \<le> entry ?Nn 0 j"
    by (auto simp: nextrel0_def)
  show ?thesis
  proof (cases "z < ?j0")
    case True \<comment> \<open>both in prefix (verbatim)\<close>
    have yj0: "y < ?j0" using yz True by linarith
    have eyz: "\<And>j. j \<le> z \<Longrightarrow> entry ?Nn 0 j = entry N 0 j"
    proof -
      fix j assume "j \<le> z"
      hence "j < ?j0" using True by linarith
      thus "entry ?Nn 0 j = entry N 0 j"
        using operB_gen_entry_prefix[OF L notzero hp, of j n 0] by simp
    qed
    have eN: "entry N 0 y < entry N 0 z" using sv eyz[of y] eyz[of z] yz by simp
    have vN: "\<And>j. y < j \<Longrightarrow> j < z \<Longrightarrow> entry N 0 z \<le> entry N 0 j"
    proof -
      fix j assume jl: "y < j" and jh: "j < z"
      have "entry ?Nn 0 z \<le> entry ?Nn 0 j" using smid[OF jl jh] .
      thus "entry N 0 z \<le> entry N 0 j" using eyz[of z] eyz[of j] jh by simp
    qed
    have zN: "z < Lng N" using True L j0lt by linarith
    have yN: "y < Lng N" using yj0 L j0lt by linarith
    have "nextrel0 N y z" unfolding nextrel0_def using yz yN zN eN vN by blast
    thus ?thesis using True yj0 by simp
  next
    case False
    hence zge: "?j0 \<le> z" by simp
    let ?sz = "(z - ?j0) mod ?w"  let ?qz = "(z - ?j0) div ?w"
    have szw: "?sz < ?w" using w0 by simp
    have zsplit: "z = ?j0 + ?qz * ?w + ?sz"
    proof -
      have "?qz * ?w + ?sz = z - ?j0"
        using div_mult_mod_eq[of "z - ?j0" ?w] by (simp add: mult.commute)
      thus ?thesis using zge by linarith
    qed
    have zmj: "z - ?j0 < n * ?w" using zlt lenNn zge by linarith
    have qzlt: "?qz < n" using less_mult_imp_div_less[OF zmj] .
    have e_z: "entry ?Nn 0 z = entry N 0 (?j0 + ?sz)"
    proof -
      have "entry ?Nn 0 (?j0 + ?qz * ?w + ?sz) = entry N 0 (?j0 + ?sz)"
        using oper_gen_block_entry0[OF L notzero hp j0lt qzlt szw] i1z by simp
      thus ?thesis using zsplit by simp
    qed
    show ?thesis
    proof (cases "?j0 \<le> y")
      case True \<comment> \<open>both in block(s); confinement forces SAME block, use in-block-back\<close>
      \<comment> \<open>derive \<open>y\<close>'s block = \<open>z\<close>'s block via the barrier\<close>
      let ?sy = "(y - ?j0) mod ?w"  let ?qy = "(y - ?j0) div ?w"
      have syw: "?sy < ?w" using w0 by simp
      have ysplit: "y = ?j0 + ?qy * ?w + ?sy"
      proof -
        have "?qy * ?w + ?sy = y - ?j0"
          using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
        thus ?thesis using True by linarith
      qed
      have ymj: "y - ?j0 < n * ?w" using yz zmj by linarith
      have qylt0: "?qy < n" using less_mult_imp_div_less[OF ymj] .
      have e_y: "entry ?Nn 0 y = entry N 0 (?j0 + ?sy)"
      proof -
        have "entry ?Nn 0 (?j0 + ?qy * ?w + ?sy) = entry N 0 (?j0 + ?sy)"
          using oper_gen_block_entry0[OF L notzero hp j0lt qylt0 syw] i1z by simp
        thus ?thesis using ysplit by simp
      qed
      have qyz: "?qy = ?qz"
      proof (rule ccontr)
        assume "?qy \<noteq> ?qz"
        \<comment> \<open>\<open>qy \<le> qz\<close> since \<open>y < z\<close> and offsets \<open>< w\<close>\<close>
        have ymj_lt: "?qy * ?w + ?sy < ?qz * ?w + ?sz"
          using yz ysplit zsplit True zge by linarith
        have qyle: "?qy \<le> ?qz"
        proof (rule ccontr)
          assume "\<not> ?qy \<le> ?qz"
          hence "?qz + 1 \<le> ?qy" by simp
          hence "(?qz + 1) * ?w \<le> ?qy * ?w" using mult_le_mono1 by blast
          hence "?qz * ?w + ?w \<le> ?qy * ?w" by (simp add: algebra_simps)
          thus False using ymj_lt szw by linarith
        qed
        hence qylt: "?qy < ?qz" using \<open>?qy \<noteq> ?qz\<close> by linarith
        \<comment> \<open>block-start of \<open>z\<close>'s block lies strictly between \<open>y\<close> and \<open>z\<close>\<close>
        let ?B = "?j0 + ?qz * ?w"
        have yB: "y < ?B"
        proof -
          have "(?qy + 1) * ?w \<le> ?qz * ?w" using qylt mult_le_mono1[of "?qy+1" ?qz ?w] by simp
          hence "?qy * ?w + ?w \<le> ?qz * ?w" by (simp add: algebra_simps)
          hence "?qy * ?w + ?sy < ?qz * ?w" using syw by linarith
          thus ?thesis using ysplit by linarith
        qed
        have Bz: "?B \<le> z" using zsplit by simp
        have eB: "entry ?Nn 0 ?B = entry N 0 ?j0"
        proof -
          have "entry ?Nn 0 (?j0 + ?qz * ?w + 0) = entry N 0 (?j0 + 0)"
            using oper_gen_block_entry0[OF L notzero hp j0lt qzlt w0] i1z by simp
          thus ?thesis by simp
        qed
        show False
        proof (cases "?B = z")
          case True
          have "?sz = 0" using zsplit True by simp
          have ez_min: "entry ?Nn 0 z = entry N 0 ?j0" using e_z \<open>?sz = 0\<close> by simp
          have ey_ge: "entry N 0 ?j0 \<le> entry ?Nn 0 y"
            using e_y minL[OF syw] by simp
          show False using sv ez_min ey_ge by simp
        next
          case False
          hence Bzs: "?B < z" using Bz by linarith
          have "entry ?Nn 0 z \<le> entry ?Nn 0 ?B" using smid[OF yB Bzs] .
          hence zle_min: "entry ?Nn 0 z \<le> entry N 0 ?j0" using eB by simp
          have z_ge_min: "entry N 0 ?j0 \<le> entry ?Nn 0 z"
            using e_z minL[OF szw] by simp
          have zeqmin: "entry ?Nn 0 z = entry N 0 ?j0" using zle_min z_ge_min by simp
          \<comment> \<open>so \<open>s\<^sub>z = 0\<close> by min-strictness; but then \<open>?B = z\<close>, contradiction\<close>
          have "?sz = 0"
          proof (rule ccontr)
            assume "?sz \<noteq> 0"
            hence "0 < ?sz" by simp
            hence "entry N 0 ?j0 < entry N 0 (?j0 + ?sz)"
              using minS[OF \<open>0 < ?sz\<close> szw] by simp
            thus False using e_z zeqmin by simp
          qed
          hence "?B = z" using zsplit by simp
          thus False using Bzs by simp
        qed
      qed
      \<comment> \<open>same block: in-block-back\<close>
      have ysplit': "y = ?j0 + ?qz * ?w + ?sy" using ysplit qyz by simp
      have zsplit': "z = ?j0 + ?qz * ?w + ?sz" using zsplit by simp
      have stepBlk: "nextrel0 ?Nn (?j0 + ?qz * ?w + ?sy) (?j0 + ?qz * ?w + ?sz)"
        using step ysplit' zsplit' by simp
      have "nextrel0 N (?j0 + ?sy) (?j0 + ?sz)"
        by (rule oper_d0zero_nextrel0_inblock_back[OF L notzero hp i1z j0lt qzlt syw szw stepBlk])
      thus ?thesis using True False by simp
    next
      case False \<comment> \<open>cross: \<open>y < j\<^sub>0 \<le> z\<close>; show \<open>z\<close> is a block-start (\<open>s\<^sub>z = 0\<close>)\<close>
      hence yj0: "y < ?j0" by simp
      let ?B = "?j0 + ?qz * ?w"
      have Bz: "?B \<le> z" using zsplit by simp
      have eB: "entry ?Nn 0 ?B = entry N 0 ?j0"
      proof -
        have "entry ?Nn 0 (?j0 + ?qz * ?w + 0) = entry N 0 (?j0 + 0)"
          using oper_gen_block_entry0[OF L notzero hp j0lt qzlt w0] i1z by simp
        thus ?thesis by simp
      qed
      have yB: "y < ?B" using yj0 zge by simp
      have szero: "?sz = 0"
      proof (rule ccontr)
        assume "?sz \<noteq> 0"
        hence spos: "0 < ?sz" by simp
        \<comment> \<open>then \<open>e\<^sub>0(N[n],z) > e\<^sub>0(N,j\<^sub>0) = e\<^sub>0(N[n],B)\<close>, and \<open>B\<close> sits between \<open>y\<close> and \<open>z\<close>\<close>
        have zgtmin: "entry N 0 ?j0 < entry ?Nn 0 z"
          using e_z minS[OF spos szw] by simp
        show False
        proof (cases "?B = z")
          case True
          have "?sz = 0" using zsplit True by simp
          thus False using \<open>?sz \<noteq> 0\<close> by simp
        next
          case False
          hence "?B < z" using Bz by linarith
          have "entry ?Nn 0 z \<le> entry ?Nn 0 ?B" using smid[OF yB \<open>?B < z\<close>] .
          thus False using eB zgtmin by simp
        qed
      qed
      have zj0blk: "z = ?B" using zsplit szero by simp
      \<comment> \<open>the base of z is the block start; the step reads \<open>nextrel0 N y j\<^sub>0\<close>\<close>
      have eyz_y: "entry ?Nn 0 y = entry N 0 y"
        using operB_gen_entry_prefix[OF L notzero hp yj0, of n 0] by simp
      have ez_min: "entry ?Nn 0 z = entry N 0 ?j0" using e_z szero by simp
      have eN: "entry N 0 y < entry N 0 ?j0" using sv eyz_y ez_min by simp
      have vN: "\<And>j. y < j \<Longrightarrow> j < ?j0 \<Longrightarrow> entry N 0 ?j0 \<le> entry N 0 j"
      proof -
        fix j assume jl: "y < j" and jh: "j < ?j0"
        have jz: "j < z" using jh zge by linarith
        have ej: "entry ?Nn 0 j = entry N 0 j"
          using operB_gen_entry_prefix[OF L notzero hp jh, of n 0] by simp
        have "entry ?Nn 0 z \<le> entry ?Nn 0 j" using smid[OF jl jz] .
        thus "entry N 0 ?j0 \<le> entry N 0 j" using ez_min ej by simp
      qed
      have yN: "y < Lng N" using yj0 L j0lt by linarith
      have j0N: "?j0 < Lng N" using j0lt L by linarith
      have "nextrel0 N y ?j0" unfolding nextrel0_def using yj0 yN j0N eN vN by blast
      thus ?thesis using yj0 False szero zj0blk zge by simp
    qed
  qed
qed

text \<open>Helper (i0, FORWARD \<open>le0\<close> base-correspondence): a row-0 reachability chain
  \<open>le0 (N[n]) p x\<close> ending at a within-block column \<open>x = j\<^sub>0+q\<cdot>w+s\<^sub>x\<close> (\<open>q < n\<close>,
  \<open>s\<^sub>x < w\<close>) reflects, column-by-column under the period BASE, to
  \<open>le0 N (base p) (base x)\<close>.  Each node \<open>y\<close> of the chain has a suffix \<open>y \<to>\<^sup>* x\<close>,
  hence \<open>y \<le> x < j\<^sub>0+(q+1)\<cdot>w\<close>, so the unified single-step base map
  @{thm [source] oper_d0zero_nextrel0_base} applies; the closure stitches the base
  steps.  (FORWARD half of the \<open>le0\<close> base-correspondence; the BACKWARD slice half
  is @{thm [source] oper_d0zero_le0_slice_lift}.)  Empirically 0-fail
  (/tmp/le0_basecorr.py: 17604/17604).\<close>

lemma oper_d0zero_le0_base_fwd:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and sx: "sx < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and reach: "le0 ((N::pairseq)[n]) p
                  (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                     + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sx)"
  shows "le0 N
            (if p < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then p
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (p - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + sx)"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?x = "?j0 + q * ?w + sx"
  let ?base = "\<lambda>z. if z < ?j0 then z else ?j0 + (z - ?j0) mod ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have q1w: "?j0 + (q + 1) * ?w = ?j0 + q * ?w + ?w" by simp
  have xcf: "?x < ?j0 + (q + 1) * ?w" using sx q1w by linarith
  have basex: "?base ?x = ?j0 + sx"
  proof -
    have "\<not> ?x < ?j0" by simp
    moreover have "(?x - ?j0) mod ?w = sx"
    proof -
      have "?x - ?j0 = q * ?w + sx" by simp
      thus ?thesis using sx by simp
    qed
    ultimately show ?thesis by simp
  qed
  have chain: "(nextrel0 ?Nn)\<^sup>*\<^sup>* p ?x" using reach by (simp add: le0_def)
  have xlt: "?x < Lng ?Nn" using reach by (simp add: le0_def)
  \<comment> \<open>front-peeling: each node \<open>c\<close> has suffix \<open>c \<to>\<^sup>* x\<close>, so \<open>c \<le> x < j\<^sub>0+(q+1)\<cdot>w\<close>\<close>
  have main: "(nextrel0 ?Nn)\<^sup>*\<^sup>* p ?x \<Longrightarrow> (nextrel0 N)\<^sup>*\<^sup>* (?base p) (?base ?x)"
  proof (induction rule: converse_rtranclp_induct)
    case base show ?case by simp
  next
    case (step c y)
    have ncy: "nextrel0 ?Nn c y" by (rule step.hyps(1))
    \<comment> \<open>\<open>y \<le> x\<close> from suffix; \<open>y < j\<^sub>0+(q+1)\<cdot>w\<close>\<close>
    have yx: "y \<le> ?x" using step.hyps(2) by (rule nextrel0_rtrancl_mono)
    have ycf: "y < ?j0 + (q + 1) * ?w" using yx xcf by linarith
    have bstep: "nextrel0 N (?base c) (?base y)"
      by (rule oper_d0zero_nextrel0_base[OF L notzero hp i1z j0lt qn ycf ncy])
    have tail: "(nextrel0 N)\<^sup>*\<^sup>* (?base y) (?base ?x)" by (rule step.IH)
    show ?case using bstep tail by (rule converse_rtranclp_into_rtranclp)
  qed
  have ch: "(nextrel0 N)\<^sup>*\<^sup>* (?base p) (?j0 + sx)" using main[OF chain] basex by simp
  \<comment> \<open>endpoints in range\<close>
  have j0wN: "?j0 + ?w < Lng N" using j0lt L by linarith
  have bpN: "?base p < Lng N"
  proof (cases "p < ?j0")
    case True
    hence "?base p = p" by simp
    thus ?thesis using True j0wN w0 by linarith
  next
    case False
    have "(p - ?j0) mod ?w < ?w" using w0 by (rule mod_less_divisor)
    hence "?base p < ?j0 + ?w" using False by simp
    thus ?thesis using j0wN by linarith
  qed
  have xN: "?j0 + sx < Lng N" using sx L j0lt by linarith
  show ?thesis using ch bpN xN by (simp add: le0_def)
qed

text \<open>Helper (i0, BACKWARD single \<open>nextrel0\<close> lift): a base row-0 step
  \<open>nextrel0 N a b\<close> with RIGHT endpoint strictly inside the active slice (\<open>b < j\<^sub>1\<close>)
  lifts into block \<open>q\<close> of \<open>N[n]\<close> under the period LIFT
  \<open>lift z = (if z < j\<^sub>0 then z else j\<^sub>0 + q\<cdot>w + (z - j\<^sub>0))\<close>.  Prefix\<rightarrow>prefix is verbatim;
  slice\<rightarrow>slice is @{thm [source] oper_gen_nextrel0_within}; the CROSS step
  \<open>a < j\<^sub>0 \<le> b\<close> necessarily has \<open>b = j\<^sub>0\<close> (a row-0 \<open>nextrel0\<close> target landing in the
  slice must sit at the slice MINIMUM \<open>e\<^sub>0(N,j\<^sub>0)\<close>, but every interior column is
  strictly above it by @{thm [source] parent_block_entry0_min}), so its lift
  \<open>a \<to> j\<^sub>0+q\<cdot>w\<close> hits a block-start, whose row-0 minimum survives the valley.
  Empirically 0-fail (/tmp/crossstep.py, /tmp/crossb.py: cross targets are the
  slice minimum, 171/171).\<close>

lemma oper_d0zero_nextrel0_lift:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and blt: "b < Lng N - 1"
    and step: "nextrel0 N a b"
  shows "nextrel0 ((N::pairseq)[n])
            (if a < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then a
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  + (a - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            (if b < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then b
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  + (b - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  have j0eq: "?j0 = parent N 0 ?j1" using i1z by simp
  have hp0: "hasParent N 0 ?j1" using hp i1z by simp
  have parR': "nextR N 0 (parent N 0 ?j1) ?j1"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  have parR0u: "nextrel0 N (parent N 0 ?j1) ?j1" using parR' by (simp add: nextR_def)
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  from step have ab: "a < b" and sv: "entry N 0 a < entry N 0 b"
    and smid: "\<And>j. a < j \<Longrightarrow> j < b \<Longrightarrow> entry N 0 b \<le> entry N 0 j"
    by (auto simp: nextrel0_def)
  show ?thesis
  proof (cases "b < ?j0")
    case True \<comment> \<open>both prefix: verbatim\<close>
    have aj0: "a < ?j0" using ab True by linarith
    have prfx: "\<And>j. j \<le> b \<Longrightarrow> entry ?Nn 0 j = entry N 0 j"
    proof -
      fix j assume "j \<le> b" hence "j < ?j0" using True by linarith
      thus "entry ?Nn 0 j = entry N 0 j"
        using operB_gen_entry_prefix[OF L notzero hp, of j n 0] by simp
    qed
    have aN: "a < Lng ?Nn" using aj0 lenNn w0 qn j0lt by simp
    have bN: "b < Lng ?Nn" using True lenNn w0 qn j0lt by simp
    have ev: "entry ?Nn 0 a < entry ?Nn 0 b" using sv prfx[of a] prfx[of b] ab by simp
    have vy: "\<And>j. a < j \<Longrightarrow> j < b \<Longrightarrow> entry ?Nn 0 b \<le> entry ?Nn 0 j"
    proof -
      fix j assume jl: "a < j" and jh: "j < b"
      have "entry N 0 b \<le> entry N 0 j" using smid[OF jl jh] .
      thus "entry ?Nn 0 b \<le> entry ?Nn 0 j" using prfx[of b] prfx[of j] jh by simp
    qed
    have "nextrel0 ?Nn a b" unfolding nextrel0_def using ab aN bN ev vy by blast
    thus ?thesis using True aj0 by simp
  next
    case False
    hence bge: "?j0 \<le> b" by simp
    show ?thesis
    proof (cases "?j0 \<le> a")
      case True \<comment> \<open>both slice: forward within\<close>
      have lifted: "nextrel0 ?Nn (?j0 + q * ?w + (a - ?j0)) (?j0 + q * ?w + (b - ?j0))"
        by (rule oper_gen_nextrel0_within[OF L notzero hp j0lt qn True blt step])
      thus ?thesis using True False by simp
    next
      case False \<comment> \<open>cross: a<j0<=b<j1; show b = j0\<close>
      hence aj0: "a < ?j0" by simp
      \<comment> \<open>\<open>b = j\<^sub>0\<close>: a slice target of a \<open>nextrel0\<close> step must be the slice minimum\<close>
      have bj0: "b = ?j0"
      proof (rule ccontr)
        assume "b \<noteq> ?j0"
        hence bgt: "?j0 < b" using bge by linarith
        let ?s = "b - ?j0"
        have sw: "?s < ?w" using bge blt by linarith
        have spos: "0 < ?s" using bgt by simp
        have s0: "?s < ?j1 - parent N 0 ?j1" using sw j0eq by simp
        have bmin: "entry N 0 (parent N 0 ?j1) < entry N 0 (parent N 0 ?j1 + ?s)"
          using parent_block_entry0_min(2)[OF parR0u s0] spos .
        have bsplit: "parent N 0 ?j1 + ?s = b" using bge j0eq by simp
        have ej0lt: "entry N 0 ?j0 < entry N 0 b" using bmin bsplit j0eq by simp
        \<comment> \<open>but \<open>j\<^sub>0\<close> sits strictly between \<open>a\<close> and \<open>b\<close>, and the valley forces \<open>e\<^sub>0 b \<le> e\<^sub>0 j\<^sub>0\<close>\<close>
        have aj0b: "a < ?j0 \<and> ?j0 < b" using aj0 bgt by simp
        have "entry N 0 b \<le> entry N 0 ?j0" using smid aj0 bgt by simp
        thus False using ej0lt by simp
      qed
      \<comment> \<open>lift the cross step \<open>a \<to> j\<^sub>0\<close> to \<open>a \<to> j\<^sub>0+q\<cdot>w\<close> (block start of block q)\<close>
      let ?B = "?j0 + q * ?w"
      have aN: "a < Lng ?Nn" using aj0 lenNn w0 qn j0lt by simp
      have BN: "?B < Lng ?Nn"
      proof -
        have "?B < ?j0 + q * ?w + ?w" using w0 by linarith
        also have "\<dots> = ?j0 + (q + 1) * ?w" by simp
        also have "\<dots> \<le> ?j0 + n * ?w" using mult_le_mono1[of "q+1" n ?w] qn by simp
        finally show ?thesis using lenNn by simp
      qed
      have prfxa: "entry ?Nn 0 a = entry N 0 a"
        using operB_gen_entry_prefix[OF L notzero hp aj0, of n 0] by simp
      have eB: "entry ?Nn 0 ?B = entry N 0 ?j0"
      proof -
        have "entry ?Nn 0 (?j0 + q * ?w + 0) = entry N 0 (?j0 + 0)"
          using oper_gen_block_entry0[OF L notzero hp j0lt qn w0] i1z by simp
        thus ?thesis by simp
      qed
      have evB: "entry ?Nn 0 a < entry ?Nn 0 ?B"
        using sv prfxa eB bj0 by simp
      have aB: "a < ?B" using aj0 by simp
      \<comment> \<open>valley on \<open>(a, B)\<close>: prefix part verbatim (smid), block part \<open>\<ge> e\<^sub>0 j\<^sub>0\<close>\<close>
      have vyB: "\<And>z. a < z \<Longrightarrow> z < ?B \<Longrightarrow> entry ?Nn 0 ?B \<le> entry ?Nn 0 z"
      proof -
        fix z assume zl: "a < z" and zh: "z < ?B"
        show "entry ?Nn 0 ?B \<le> entry ?Nn 0 z"
        proof (cases "z < ?j0")
          case True \<comment> \<open>prefix: \<open>z\<close> between \<open>a\<close> and \<open>j\<^sub>0\<close>; use smid at \<open>j\<^sub>0 = b\<close>\<close>
          have ez: "entry ?Nn 0 z = entry N 0 z"
            using operB_gen_entry_prefix[OF L notzero hp True, of n 0] by simp
          have "entry N 0 b \<le> entry N 0 z" using smid zl True bj0 by simp
          thus ?thesis using ez eB bj0 by simp
        next
          case False \<comment> \<open>block region: \<open>z \<ge> j\<^sub>0\<close>, row-0 \<open>\<ge> e\<^sub>0 j\<^sub>0\<close> (block minimum)\<close>
          hence zge: "?j0 \<le> z" by simp
          have zlt: "z < Lng ?Nn" using zh BN by linarith
          let ?sz = "(z - ?j0) mod ?w"
          have szw: "?sz < ?w" using w0 by simp
          have ez: "entry ?Nn 0 z = entry N 0 (?j0 + ?sz)"
            using oper_d0zero_entryi_base[OF L notzero hp i1z j0lt zlt, of 0] False by simp
          have "entry N 0 ?j0 \<le> entry N 0 (?j0 + ?sz)"
          proof -
            have s0: "?sz < ?j1 - parent N 0 ?j1" using szw j0eq by simp
            show ?thesis using parent_block_entry0_min(1)[OF parR0u s0] j0eq by simp
          qed
          thus ?thesis using ez eB by simp
        qed
      qed
      have "nextrel0 ?Nn a ?B" unfolding nextrel0_def using aB aN BN evB vyB by blast
      thus ?thesis using aj0 False bj0 by simp
    qed
  qed
qed

text \<open>Helper (i0, BACKWARD \<open>le0\<close> lift, GENERAL): a base row-0 reachability chain
  \<open>le0 N a x'\<close> ending strictly inside the active slice (\<open>x' = j\<^sub>0 + s\<^sub>x\<close>, \<open>s\<^sub>x < w\<close>)
  lifts into block \<open>q\<close> of \<open>N[n]\<close> under the period LIFT
  \<open>lift z = (if z < j\<^sub>0 then z else j\<^sub>0 + q\<cdot>w + (z - j\<^sub>0))\<close>:
  \<open>le0 (N[n]) (lift a) (j\<^sub>0+q\<cdot>w+s\<^sub>x)\<close>.  Every chain node \<open>y \<le> x' < j\<^sub>1\<close>, so each
  \<open>nextrel0 N\<close> step lifts by @{thm [source] oper_d0zero_nextrel0_lift}; the closure
  stitches the lifted steps.  (BACKWARD half of the \<open>le0\<close> base-correspondence, for
  ARBITRARY start \<open>a\<close> — prefix or slice.)  Empirically 0-fail
  (/tmp/le0_basecorr.py: 17604/17604).\<close>

lemma oper_d0zero_le0_lift:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and sx: "sx < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and reach: "le0 N a (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + sx)"
  shows "le0 ((N::pairseq)[n])
            (if a < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then a
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  + (a - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sx)"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?xp = "?j0 + sx"
  let ?lift = "\<lambda>z. if z < ?j0 then z else ?j0 + q * ?w + (z - ?j0)"
  have w0: "0 < ?w" using j0lt by linarith
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have xpj1: "?xp < ?j1" using sx by linarith
  have chain: "(nextrel0 N)\<^sup>*\<^sup>* a ?xp" using reach by (simp add: le0_def)
  \<comment> \<open>lifted endpoints sit in range, and \<open>lift x' = j\<^sub>0+q\<cdot>w+s\<^sub>x\<close>\<close>
  have liftxp: "?lift ?xp = ?j0 + q * ?w + sx"
  proof -
    have "\<not> ?xp < ?j0" by simp
    thus ?thesis by simp
  qed
  have liftrng: "\<And>z. z < ?j1 \<Longrightarrow> ?lift z < Lng ?Nn"
  proof -
    fix z assume zj1: "z < ?j1"
    show "?lift z < Lng ?Nn"
    proof (cases "z < ?j0")
      case True thus ?thesis using lenNn w0 qn j0lt by simp
    next
      case False
      have oz: "z - ?j0 < ?w" using zj1 False by linarith
      have "?lift z = ?j0 + q * ?w + (z - ?j0)" using False by simp
      also have "\<dots> < ?j0 + q * ?w + ?w" using oz by linarith
      also have "\<dots> = ?j0 + (q + 1) * ?w" by simp
      also have "\<dots> \<le> ?j0 + n * ?w" using mult_le_mono1[of "q+1" n ?w] qn by simp
      finally show ?thesis using lenNn by simp
    qed
  qed
  \<comment> \<open>front-peeling closure lift: each node \<open>y \<le> x' < j\<^sub>1\<close>\<close>
  have main: "(nextrel0 N)\<^sup>*\<^sup>* a ?xp \<Longrightarrow> (nextrel0 ?Nn)\<^sup>*\<^sup>* (?lift a) (?lift ?xp)"
  proof (induction rule: converse_rtranclp_induct)
    case base show ?case by simp
  next
    case (step c y)
    have ncy: "nextrel0 N c y" by (rule step.hyps(1))
    have yx: "y \<le> ?xp" using step.hyps(2) by (rule nextrel0_rtrancl_mono)
    have yj1: "y < ?j1" using yx xpj1 by linarith
    have lstep: "nextrel0 ?Nn (?lift c) (?lift y)"
      by (rule oper_d0zero_nextrel0_lift[OF L notzero hp i1z j0lt qn yj1 ncy])
    have tail: "(nextrel0 ?Nn)\<^sup>*\<^sup>* (?lift y) (?lift ?xp)" by (rule step.IH)
    show ?case using lstep tail by (rule converse_rtranclp_into_rtranclp)
  qed
  have ch: "(nextrel0 ?Nn)\<^sup>*\<^sup>* (?lift a) (?j0 + q * ?w + sx)"
    using main[OF chain] liftxp by simp
  \<comment> \<open>endpoints in range\<close>
  have aj1: "a < ?j1" using chain nextrel0_rtrancl_mono[of N a ?xp] xpj1 by linarith
  have laN: "?lift a < Lng ?Nn" using liftrng[OF aj1] .
  have xN: "?j0 + q * ?w + sx < Lng ?Nn" using liftrng[OF xpj1] liftxp by simp
  show ?thesis using ch laN xN by (simp add: le0_def)
qed

end
