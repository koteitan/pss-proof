theory Frontier_6_031
  imports Support_6_013
begin

text \<open>§6.8 d0pos row-0 access at the block-(\<open>k\<close>) right boundary (offset \<open>s = w\<close>),
  which is the START of block \<open>k+1\<close>: \<open>entry (M[n]) 0 (j\<^sub>0 + k\<cdot>w + w) = entry M 0 j\<^sub>1
  + k\<cdot>\<delta>\<close>.  Because \<open>j\<^sub>0 + w = j\<^sub>1\<close> and \<open>\<delta> = entry M 0 j\<^sub>1 - entry M 0 j\<^sub>0\<close>, this equals
  \<open>entry M 0 j\<^sub>0 + (k+1)\<cdot>\<delta>\<close>, matching block \<open>k+1\<close>'s offset-0 value.  Stated via the
  block-\<open>(k+1)\<close> reading (offset \<open>0\<close>); requires \<open>k+1 < n\<close>.\<close>

lemma oper_d1pos_entry0_boundary:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and k1: "k + 1 < n"
  shows "entry (M[n]) 0 (parent M 1 (Lng M - 1)
                 + (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)))
       = entry M 0 (Lng M - 1)
            + k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1)))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"  let ?j1 = "Lng M - 1"  let ?w = "?j1 - ?j0"
  let ?delta = "entry M 0 ?j1 - entry M 0 ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  \<comment> \<open>\<open>entry M 0 j\<^sub>0 \<le> entry M 0 j\<^sub>1\<close> from the row-1 parent relation\<close>
  have hp1: "hasParent M 1 ?j1" using hp i1z by simp
  have parR: "nextR M 1 ?j0 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have "leR M 0 ?j0 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  hence "(nextrel0 M)\<^sup>*\<^sup>* ?j0 ?j1" by (simp add: leR_def le0_def)
  hence e0le: "entry M 0 ?j0 \<le> entry M 0 ?j1" by (rule nextrel0_rtrancl_entry0_mono)
  \<comment> \<open>read the boundary as block \<open>(k+1)\<close> offset \<open>0\<close>\<close>
  have e: "entry (M[n]) 0 (?j0 + (k + 1) * ?w + 0)
         = entry M 0 (?j0 + 0) + (k + 1) * ?delta"
    by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt k1 w0])
  have val: "entry M 0 (?j0 + 0) + (k + 1) * ?delta = entry M 0 ?j1 + k * ?delta"
  proof -
    have d: "entry M 0 ?j0 + ?delta = entry M 0 ?j1" using e0le by simp
    have "entry M 0 (?j0 + 0) + (k + 1) * ?delta
            = (entry M 0 ?j0 + ?delta) + k * ?delta" by simp
    also have "\<dots> = entry M 0 ?j1 + k * ?delta" using d by simp
    finally show ?thesis .
  qed
  show ?thesis using e val by simp
qed

text \<open>§6.8 d0pos \<open>nextrel0\<close> TRANSFER (article 1536): a base row-0 step
  \<open>nextrel0 M x y\<close> with \<open>j\<^sub>0 \<le> x < y \<le> j\<^sub>1\<close> lifts verbatim into block \<open>k\<close> of \<open>M[n]\<close>
  (translate by the block start \<open>j\<^sub>0 + k\<cdot>w\<close>): \<open>nextrel0 (M[n]) (j\<^sub>0+k\<cdot>w+(x-j\<^sub>0))
  (j\<^sub>0+k\<cdot>w+(y-j\<^sub>0))\<close>.  Both endpoints and all intermediate indices lie inside block
  \<open>k\<close> (offset \<open>< w\<close>), where \<open>M[n]\<close>'s row 0 is \<open>M\<close>'s row 0 shifted by the constant
  \<open>k\<cdot>\<delta>\<close>; the strict-increase and valley conditions of \<open>nextrel0\<close> are invariant under
  a uniform additive shift, so the step transfers.  The right endpoint may be
  \<open>y = j\<^sub>1\<close> (block-\<open>(k+1)\<close> start, offset \<open>0\<close>), handled by the boundary reading;
  this is why \<open>k+1 < n\<close> is required.\<close>

lemma oper_d1pos_nextrel0_transfer:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and k1: "k + 1 < n"
    and xy: "parent M 1 (Lng M - 1) \<le> x" "y \<le> Lng M - 1"
    and step: "nextrel0 M x y"
  shows "nextrel0 ((M::pairseq)[n])
            (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) + (x - parent M 1 (Lng M - 1)))
            (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) + (y - parent M 1 (Lng M - 1)))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"  let ?j1 = "Lng M - 1"  let ?w = "?j1 - ?j0"
  let ?delta = "entry M 0 ?j1 - entry M 0 ?j0"
  let ?base = "?j0 + k * ?w"
  let ?tx = "?base + (x - ?j0)"  let ?ty = "?base + (y - ?j0)"
  have w0: "0 < ?w" using j0lt by linarith
  \<comment> \<open>decode the base step\<close>
  from step have sx: "x < y" and sm: "x < Lng M" "y < Lng M"
    and sv: "entry M 0 x < entry M 0 y"
    and smid: "\<And>j. x < j \<Longrightarrow> j < y \<Longrightarrow> entry M 0 y \<le> entry M 0 j"
    by (auto simp: nextrel0_def)
  have x0: "?j0 \<le> x" using xy(1) .
  have xle: "x \<le> y" using sx by simp
  have yle: "y \<le> ?j1" using xy(2) .
  \<comment> \<open>offsets\<close>
  have ox: "x - ?j0 < ?w" using x0 sx yle by linarith
  \<comment> \<open>hold \<open>w\<close> abstract for all index-bound arithmetic (avoid nat-sub expansion)\<close>
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have lenMn: "Lng (M[n]) = ?j0 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  \<comment> \<open>row-0 at \<open>tx\<close>: block \<open>k\<close> offset \<open>x-j\<^sub>0 < w\<close>\<close>
  have e_tx: "entry (M[n]) 0 ?tx = entry M 0 x + k * ?delta"
  proof -
    have "entry (M[n]) 0 (?j0 + k * ?w + (x - ?j0)) = entry M 0 (?j0 + (x - ?j0)) + k * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt _ ox]) (use k1 in linarith)
    thus ?thesis using x0 by simp
  qed
  \<comment> \<open>row-0 at \<open>ty\<close>: either block \<open>k\<close> offset \<open>< w\<close>, or the block boundary (\<open>y=j\<^sub>1\<close>)\<close>
  have e_ty: "entry (M[n]) 0 ?ty = entry M 0 y + k * ?delta"
  proof (cases "y < ?j1")
    case True
    have oy: "y - ?j0 < ?w" using x0 xle yle True by linarith
    have "entry (M[n]) 0 (?j0 + k * ?w + (y - ?j0)) = entry M 0 (?j0 + (y - ?j0)) + k * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt _ oy]) (use k1 in linarith)
    thus ?thesis using x0 xle yle by simp
  next
    case False
    hence yeq: "y = ?j1" using yle by linarith
    have tyeq: "?ty = ?j0 + (k + 1) * ?w"
    proof -
      have "?ty = ?j0 + k * w + w" using yeq wdef by simp
      also have "\<dots> = ?j0 + (k + 1) * w" by (simp add: algebra_simps)
      finally show ?thesis using wdef by simp
    qed
    have bdy: "entry (M[n]) 0 (?j0 + (k + 1) * ?w) = entry M 0 ?j1 + k * ?delta"
      by (rule oper_d1pos_entry0_boundary[OF L notzero hp i1z j0lt k1])
    have "entry (M[n]) 0 ?ty = entry (M[n]) 0 (?j0 + (k + 1) * ?w)"
      using tyeq by (rule arg_cong[where f="\<lambda>z. entry (M[n]) 0 z"])
    also have "\<dots> = entry M 0 ?j1 + k * ?delta" by (rule bdy)
    also have "\<dots> = entry M 0 y + k * ?delta" using yeq by simp
    finally show ?thesis .
  qed
  \<comment> \<open>index bounds (all in abstract \<open>w\<close>)\<close>
  have kn: "k < n" using k1 by simp
  have oxw: "x - ?j0 < w" using ox wdef by simp
  have oyw: "y - ?j0 \<le> w" using x0 xle yle wdef by linarith
  have txw: "?tx = ?j0 + k * w + (x - ?j0)" using wdef by simp
  have tyw: "?ty = ?j0 + k * w + (y - ?j0)" using wdef by simp
  have klt: "?j0 + (k + 1) * w < ?j0 + n * w"
    using add_strict_left_mono[OF mult_less_mono1[OF k1 w0'], of ?j0] .
  have txlt: "?tx < Lng (M[n])"
  proof -
    have "?tx \<le> ?j0 + k * w + w" using txw oxw by linarith
    also have "\<dots> = ?j0 + (k + 1) * w" by (simp add: algebra_simps)
    finally show ?thesis using klt lenMn by linarith
  qed
  have tylt: "?ty < Lng (M[n])"
  proof -
    have "?ty \<le> ?j0 + k * w + w" using tyw oyw by linarith
    also have "\<dots> = ?j0 + (k + 1) * w" by (simp add: algebra_simps)
    finally show ?thesis using klt lenMn by linarith
  qed
  have txty: "?tx < ?ty" using sx x0 by linarith
  have ev: "entry (M[n]) 0 ?tx < entry (M[n]) 0 ?ty"
    using e_tx e_ty sv by simp
  \<comment> \<open>valley: intermediate index \<open>?tx < z < ?ty\<close> sits inside block \<open>k\<close> (offset \<open>< w\<close>)\<close>
  have valley: "\<And>z. ?tx < z \<Longrightarrow> z < ?ty \<Longrightarrow> entry (M[n]) 0 ?ty \<le> entry (M[n]) 0 z"
  proof -
    fix z assume zlo: "?tx < z" and zhi: "z < ?ty"
    have zge: "?base \<le> z" using zlo x0 by linarith
    let ?t = "z - ?base"
    have ztw: "?t < ?w" using zhi zge oyw wdef by linarith
    have zsplit: "z = ?j0 + k * ?w + ?t" using zge by simp
    have e_z: "entry (M[n]) 0 z = entry M 0 (?j0 + ?t) + k * ?delta"
    proof -
      have "entry (M[n]) 0 (?j0 + k * ?w + ?t) = entry M 0 (?j0 + ?t) + k * ?delta"
        by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt _ ztw]) (use k1 in linarith)
      thus ?thesis using zsplit by simp
    qed
    \<comment> \<open>the M-index \<open>j\<^sub>0+?t\<close> sits strictly between \<open>x\<close> and \<open>y\<close>\<close>
    have jlo: "x < ?j0 + ?t" using zlo zge x0 by linarith
    have jhi: "?j0 + ?t < y" using zhi zge x0 xle yle by linarith
    have "entry M 0 y \<le> entry M 0 (?j0 + ?t)" using smid[OF jlo jhi] .
    thus "entry (M[n]) 0 ?ty \<le> entry (M[n]) 0 z"
      using e_z e_ty by simp
  qed
  show ?thesis
    unfolding nextrel0_def
    using txlt tylt txty ev valley by blast
qed

text \<open>§6.8 d0pos INTER-BLOCK row-0 monotonicity (article 1530-1538): consecutive
  fundamental-sequence block STARTS are row-0 ancestors,
  \<open>(0, j\<^sub>0 + k\<cdot>w) \<le>\<^sub>M\<^bsub>[n]\<^esub> (0, j\<^sub>0 + (k+1)\<cdot>w)\<close>, for \<open>k+1 < n\<close>
  (\<open>w = Lng M - 1 - j\<^sub>0\<close>, \<open>j\<^sub>0 = parent M 1 (Lng M-1)\<close>).

  Proof (article line 1536): the base row-0 reachability \<open>(0,j\<^sub>0) \<le>\<^sub>M (0,j\<^sub>1)\<close>
  (\<open>j\<^sub>1 = Lng M-1\<close>) holds because \<open>j\<^sub>0 = parent M 1 j\<^sub>1\<close> means \<open>nextR M 1 j\<^sub>0 j\<^sub>1\<close>,
  whence \<open>le0 M j\<^sub>0 j\<^sub>1\<close> (@{thm [source] poper_nextR_imp_le0}).  Block \<open>k\<close> of \<open>M[n]\<close>
  is exactly the slice \<open>[j\<^sub>0,j\<^sub>1]\<close> with row 0 shifted by the constant \<open>k\<cdot>\<delta>\<close> and
  row 1 unchanged, so each base \<open>nextrel0\<close> step lifts verbatim
  (@{thm [source] oper_d1pos_nextrel0_transfer}); the whole base chain
  \<open>j\<^sub>0 \<rightarrow>\<^sup>* j\<^sub>1\<close> therefore lifts to \<open>j\<^sub>0+k\<cdot>w \<rightarrow>\<^sup>* j\<^sub>0+k\<cdot>w+w = j\<^sub>0+(k+1)\<cdot>w\<close>, giving the
  claimed \<open>le0\<close>.  Empirically validated (\<open>python/red_model.py\<close>, \<open>is_standard\<close> +
  \<open>KMAX=6\<close>): 195/195 standard d0pos block-start pairs satisfy this \<open>le0\<close>, and the
  underlying step transfer holds 495/495.\<close>

lemma oper_d1pos_block_chain:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and k1: "k + 1 < n"
  shows "le0 ((M::pairseq)[n])
            (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
            (parent M 1 (Lng M - 1) + (k + 1) * (Lng M - 1 - parent M 1 (Lng M - 1)))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"  let ?j1 = "Lng M - 1"  let ?w = "?j1 - ?j0"
  let ?base = "?j0 + k * ?w"
  have w0: "0 < ?w" using j0lt by linarith
  \<comment> \<open>base reachability \<open>j\<^sub>0 \<rightarrow>\<^sup>* j\<^sub>1\<close> in \<open>M\<close>, from the row-1 parent relation\<close>
  have hp1: "hasParent M 1 ?j1" using hp i1z by simp
  have parR: "nextR M 1 ?j0 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have "leR M 0 ?j0 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  hence baseR: "(nextrel0 M)\<^sup>*\<^sup>* ?j0 ?j1" by (simp add: leR_def le0_def)
  \<comment> \<open>lift the whole chain into block \<open>k\<close>; generalise the right endpoint \<open>?j1\<close> to a
     running variable \<open>y\<close> with \<open>j\<^sub>0 \<le> y \<le> j\<^sub>1\<close>\<close>
  have lift: "\<And>y. (nextrel0 M)\<^sup>*\<^sup>* ?j0 y \<Longrightarrow> ?j0 \<le> y \<and> y \<le> ?j1
                   \<longrightarrow> (nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (y - ?j0))"
  proof -
    fix y assume "(nextrel0 M)\<^sup>*\<^sup>* ?j0 y"
    thus "?j0 \<le> y \<and> y \<le> ?j1 \<longrightarrow> (nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (y - ?j0))"
    proof (induction rule: rtranclp_induct)
      case base
      show ?case by simp
    next
      case (step u v)
      show ?case
      proof
        assume vb: "?j0 \<le> v \<and> v \<le> ?j1"
        \<comment> \<open>indices increase along the chain, so \<open>j\<^sub>0 \<le> u \<le> v\<close>\<close>
        have j0u: "?j0 \<le> u" using step.hyps(1) nextrel0_rtrancl_mono by blast
        have uv: "u < v" using step.hyps(2) by (simp add: nextrel0_def)
        have ule: "u \<le> ?j1" using uv vb by linarith
        have IH: "(nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (u - ?j0))"
          using step.IH j0u ule by simp
        \<comment> \<open>transfer the single step \<open>nextrel0 M u v\<close>\<close>
        have stp: "nextrel0 (M[n]) (?base + (u - ?j0)) (?base + (v - ?j0))"
          by (rule oper_d1pos_nextrel0_transfer
                  [OF L notzero hp i1z j0lt k1 j0u _ step.hyps(2)]) (use vb in simp)
        show "(nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (v - ?j0))"
          using IH stp by simp
      qed
    qed
  qed
  have chain: "(nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (?j1 - ?j0))"
    using lift[OF baseR] j0lt by simp
  have endeq: "?base + (?j1 - ?j0) = ?j0 + (k + 1) * ?w"
  proof -
    obtain w where wdef: "w = ?w" by blast
    have "?base + (?j1 - ?j0) = ?j0 + k * w + w" using wdef by simp
    also have "\<dots> = ?j0 + (k + 1) * w" by (simp add: algebra_simps)
    finally show ?thesis using wdef by simp
  qed
  \<comment> \<open>index bounds for the \<open>le0\<close> wrapper.  Hold \<open>w\<close> abstract through a fresh
     variable so no decision procedure ever sees \<open>(k+1)\<cdot>(Lng M - Suc j\<^sub>0)\<close>
     (the nat-sub double-expansion loop).  Build the goals in \<open>w\<close>, then fold.\<close>
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have kn: "k < n" using k1 by simp
  have lenMn: "Lng (M[n]) = ?j0 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  have klt: "?j0 + k * w < ?j0 + n * w"
    using add_strict_left_mono[OF mult_less_mono1[OF kn w0'], of ?j0] .
  have k1lt: "?j0 + (k + 1) * w < ?j0 + n * w"
    using add_strict_left_mono[OF mult_less_mono1[OF k1 w0'], of ?j0] .
  have baselt: "?base < Lng (M[n])"
    using klt lenMn wdef by simp
  have endlt: "?j0 + (k + 1) * ?w < Lng (M[n])"
    using k1lt lenMn wdef by simp
  have chain': "(nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?j0 + (k + 1) * ?w)"
    using chain unfolding endeq[symmetric] .
  show ?thesis
    unfolding le0_def
    using baselt endlt chain' by blast
qed

text \<open>§6.8 d0pos TRANSITIVE inter-block reachability (article 1530-1545): the
  block-0 start \<open>j\<^sub>0 = parent M 1 j\<^sub>1\<close> row-0-reaches ANY later block start
  \<open>j\<^sub>0 + k\<cdot>w\<close> (\<open>w = Lng M - 1 - j\<^sub>0\<close>), for every \<open>k < n\<close>.  Proof: induction on
  \<open>k\<close>.  Base \<open>k=0\<close> is \<open>le0_refl\<close> at \<open>j\<^sub>0\<close> (in range since \<open>0 < n\<close>).  Step
  \<open>k \<rightarrow> k+1\<close>: from the IH \<open>le0 (M[n]) j\<^sub>0 (j\<^sub>0+k\<cdot>w)\<close> (valid as \<open>k < n\<close>) compose
  one consecutive-block step \<open>oper_d1pos_block_chain\<close>, which at its \<open>k\<close> needs
  \<open>k+1 < n\<close> — exactly the hypothesis for the \<open>k+1\<close> target — via \<open>le0_trans\<close>.
  Hence the required bound is \<open>k < n\<close> (not \<open>k+1 \<le> n\<close> in a stronger sense; they
  coincide, but the last chained step \<open>(k-1) \<rightarrow> k\<close> uses \<open>block_chain\<close> at index
  \<open>k-1\<close> with side-condition \<open>(k-1)+1 = k < n\<close>).  Empirically validated
  (\<open>python/red_model.py\<close>, \<open>is_standard\<close> + \<open>KMAX=6\<close>): 378/378 standard d0pos
  block-start pairs with \<open>k < n\<close> satisfy this \<open>le0\<close>.\<close>

lemma oper_d1pos_le0_blockstarts:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and kn: "k < n"
  shows "le0 ((M::pairseq)[n])
            (parent M 1 (Lng M - 1))
            (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  \<comment> \<open>hold \<open>w\<close> abstract so no decision procedure sees the nat-sub double-expansion\<close>
  obtain w where wdef: "?w = w" by blast
  have w0: "0 < w" using j0lt wdef by linarith
  have lenMn: "Lng (M[n]) = ?j0 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  \<comment> \<open>induction on \<open>k\<close>, guarding the claim by the running bound \<open>k < n\<close>\<close>
  have "k < n \<longrightarrow> le0 (M[n]) ?j0 (?j0 + k * w)"
  proof (induction k)
    case 0
    show ?case
    proof
      assume "0 < n"
      hence "?j0 < ?j0 + n * w" using w0 by simp
      hence "?j0 < Lng (M[n])" using lenMn by simp
      thus "le0 (M[n]) ?j0 (?j0 + 0 * w)" using le0_refl by simp
    qed
  next
    case (Suc k)
    show ?case
    proof
      assume sn: "Suc k < n"
      have kn': "k < n" using sn by simp
      have IH: "le0 (M[n]) ?j0 (?j0 + k * w)" using Suc.IH kn' by simp
      \<comment> \<open>one consecutive-block step \<open>k \<rightarrow> k+1\<close>; \<open>block_chain\<close> needs \<open>k+1 < n\<close>\<close>
      have k1: "k + 1 < n" using sn by simp
      have step: "le0 (M[n]) (?j0 + k * ?w) (?j0 + (k + 1) * ?w)"
        by (rule oper_d1pos_block_chain[OF L notzero hp i1z j0lt k1])
      have step': "le0 (M[n]) (?j0 + k * w) (?j0 + Suc k * w)"
        using step wdef by simp
      show "le0 (M[n]) ?j0 (?j0 + Suc k * w)"
        using le0_trans[OF IH step'] .
    qed
  qed
  hence "le0 (M[n]) ?j0 (?j0 + k * w)" using kn by simp
  thus ?thesis using wdef by simp
qed

end
