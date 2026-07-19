theory Frontier_6_035
  imports Support_6_017
begin

text \<open>§6.8 d1pos: the standard-form row-1 increment bound (general AND last-column)
  is FALSE — see the B3N residual inside \<open>TrMax_seg_oper_d1pos_brle_capped\<close> below.
  The N-side boundary inequality is true only with the full capped \<open>\<not>brle\<close> slice
  context, so it lives as a precisely-scoped inline residual there, not as a
  standalone lemma.\<close>

text \<open>§6.8 d1pos capped \<open>le0\<close>-at-the-block-boundary STUB (precisely-scoped residual).
  In the capped layout the slice \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close> reaches, at its
  position \<open>c+1 = j\<^sub>1\<^sup>red - j\<^sub>0\<^sup>red\<close>, the START of block \<open>q+1\<close> (\<open>N\<close>-index
  \<open>j\<^sub>-\<^sub>2\<^sup>N + (q+1)\<cdot>w\<close>), and \<open>j'\<^sub>1\<close> lies inside that same block \<open>q+1\<close>; the whole slice
  end is row-0-reachable from that block start.  Concretely:
  \<open>le0 M' (c+1) (Lng M' - 1)\<close> with \<open>c = j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red\<close>.  This is the within-
  block \<open>le0\<close> from the block-(\<open>q+1\<close>) start to the slice end, the analogue of
  @{thm [source] oper_d1pos_block_chain} restricted to the final partial block.
  DEEP-VERIFIED (\<open>python/d1pos_b3_boundary.py\<close> and the inline le0 probe, KMAX=7
  len=12): \<open>le0 M' (c+1) (Lng M'-1)\<close> holds 1688/1688 on all capped \<open>\<not>brle\<close> slices.
  RESIDUAL — the within-block \<open>le0\<close> brick (\<open>oper_d1pos_seg_le0_*\<close>) is not yet
  available; left precisely-scoped.\<close>

text \<open>§6.8 d1pos WITHIN-block \<open>nextrel0\<close> transfer (\<open>k < n\<close> only): a base row-0 step
  \<open>nextrel0 M x y\<close> whose right endpoint stays STRICTLY inside the slice
  (\<open>y < Lng M-1\<close>) lifts into block \<open>k\<close> of \<open>M[n]\<close> without ever touching the block
  boundary, so only \<open>k < n\<close> is needed (the boundary version
  @{thm [source] oper_d1pos_nextrel0_transfer} needs \<open>k+1 < n\<close>).  Both endpoints and
  intermediate indices have offset \<open>< w\<close>; row 0 of \<open>M[n]\<close> there is \<open>M\<close>'s row 0 shifted
  by the constant \<open>k\<cdot>\<delta>\<close> (@{thm [source] oper_d1pos_entry0}), under which \<open>nextrel0\<close>
  is invariant.\<close>

lemma oper_d1pos_nextrel0_within:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and kn: "k < n"
    and xge: "parent M 1 (Lng M - 1) \<le> x"
    and ylt: "y < Lng M - 1"
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
  from step have sx: "x < y" and sm: "x < Lng M" "y < Lng M"
    and sv: "entry M 0 x < entry M 0 y"
    and smid: "\<And>j. x < j \<Longrightarrow> j < y \<Longrightarrow> entry M 0 y \<le> entry M 0 j"
    by (auto simp: nextrel0_def)
  have x0: "?j0 \<le> x" using xge .
  have xle: "x \<le> y" using sx by simp
  have yle: "y \<le> ?j1" using ylt by linarith
  have ox: "x - ?j0 < ?w" using x0 sx ylt by linarith
  have oy: "y - ?j0 < ?w" using x0 xle ylt by linarith
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have lenMn: "Lng (M[n]) = ?j0 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  have e_tx: "entry (M[n]) 0 ?tx = entry M 0 x + k * ?delta"
  proof -
    have "entry (M[n]) 0 (?j0 + k * ?w + (x - ?j0)) = entry M 0 (?j0 + (x - ?j0)) + k * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt kn ox])
    thus ?thesis using x0 by simp
  qed
  have e_ty: "entry (M[n]) 0 ?ty = entry M 0 y + k * ?delta"
  proof -
    have "entry (M[n]) 0 (?j0 + k * ?w + (y - ?j0)) = entry M 0 (?j0 + (y - ?j0)) + k * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt kn oy])
    thus ?thesis using x0 xle yle by simp
  qed
  have oxw: "x - ?j0 < w" using ox wdef by simp
  have oyw: "y - ?j0 < w" using oy wdef by simp
  have txw: "?tx = ?j0 + k * w + (x - ?j0)" using wdef by simp
  have tyw: "?ty = ?j0 + k * w + (y - ?j0)" using wdef by simp
  have klt: "?j0 + k * w + w \<le> ?j0 + n * w"
  proof -
    have "?j0 + k * w + w = ?j0 + (k + 1) * w" by (simp add: algebra_simps)
    also have "\<dots> \<le> ?j0 + n * w" using mult_le_mono1[of "k+1" n w] kn by simp
    finally show ?thesis .
  qed
  have txlt: "?tx < Lng (M[n])"
  proof -
    have "?tx < ?j0 + k * w + w" using txw oxw by linarith
    thus ?thesis using klt lenMn by linarith
  qed
  have tylt: "?ty < Lng (M[n])"
  proof -
    have "?ty < ?j0 + k * w + w" using tyw oyw by linarith
    thus ?thesis using klt lenMn by linarith
  qed
  have txty: "?tx < ?ty" using sx x0 by linarith
  have ev: "entry (M[n]) 0 ?tx < entry (M[n]) 0 ?ty"
    using e_tx e_ty sv by simp
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
        by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt kn ztw])
      thus ?thesis using zsplit by simp
    qed
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

text \<open>§6.8 d1pos WITHIN-block reach (\<open>k < n\<close>): block \<open>k\<close>'s start row-0-reaches any
  index strictly inside block \<open>k\<close> (offset \<open>t < w\<close>), \<open>le0 (M[n]) (j\<^sub>0+k\<cdot>w) (j\<^sub>0+k\<cdot>w+t)\<close>.
  Lift the base reachability \<open>j\<^sub>0 \<rightarrow>\<^sup>* (j\<^sub>0+t)\<close> in \<open>M\<close> (a prefix of the parent chain
  \<open>j\<^sub>0 \<rightarrow>\<^sup>* j\<^sub>1\<close>) into block \<open>k\<close> via @{thm [source] oper_d1pos_nextrel0_within}; the
  running right endpoint never touches the boundary (\<open>< j\<^sub>1\<close>), so only \<open>k < n\<close> is used.\<close>

lemma oper_d1pos_le0_within:
  assumes MT: "M \<in> T_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and kn: "k < n"
    and tw: "t < Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "le0 ((M::pairseq)[n])
            (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
            (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) + t)"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"  let ?j1 = "Lng M - 1"  let ?w = "?j1 - ?j0"
  let ?base = "?j0 + k * ?w"
  have w0: "0 < ?w" using j0lt by linarith
  \<comment> \<open>base reachability \<open>j\<^sub>0 \<rightarrow>\<^sup>* j\<^sub>1\<close> in \<open>M\<close>\<close>
  have hp1: "hasParent M 1 ?j1" using hp i1z by simp
  have parR: "nextR M 1 ?j0 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have "leR M 0 ?j0 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  hence baseR: "(nextrel0 M)\<^sup>*\<^sup>* ?j0 ?j1" by (simp add: leR_def le0_def)
  \<comment> \<open>lift the prefix \<open>j\<^sub>0 \<rightarrow>\<^sup>* y\<close> for any \<open>j\<^sub>0 \<le> y < j\<^sub>1\<close>\<close>
  have lift: "\<And>y. (nextrel0 M)\<^sup>*\<^sup>* ?j0 y \<Longrightarrow> ?j0 \<le> y \<and> y < ?j1
                   \<longrightarrow> (nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (y - ?j0))"
  proof -
    fix y assume "(nextrel0 M)\<^sup>*\<^sup>* ?j0 y"
    thus "?j0 \<le> y \<and> y < ?j1 \<longrightarrow> (nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (y - ?j0))"
    proof (induction rule: rtranclp_induct)
      case base
      show ?case by simp
    next
      case (step u v)
      show ?case
      proof
        assume vb: "?j0 \<le> v \<and> v < ?j1"
        have j0u: "?j0 \<le> u" using step.hyps(1) nextrel0_rtrancl_mono by blast
        have uv: "u < v" using step.hyps(2) by (simp add: nextrel0_def)
        have ult: "u < ?j1" using uv vb by linarith
        have IH: "(nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (u - ?j0))"
          using step.IH j0u ult by simp
        have stp: "nextrel0 (M[n]) (?base + (u - ?j0)) (?base + (v - ?j0))"
          by (rule oper_d1pos_nextrel0_within
                  [OF L notzero hp i1z j0lt kn j0u _ step.hyps(2)]) (use vb in simp)
        show "(nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + (v - ?j0))"
          using IH stp by simp
      qed
    qed
  qed
  \<comment> \<open>obtain a base witness \<open>j\<^sub>0 \<rightarrow>\<^sup>* (j\<^sub>0+t)\<close> via @{thm [source] le0_build}: the
     row-0 strict-increase hypothesis comes from @{thm [source] le0_ances_aux} on the
     parent chain \<open>j\<^sub>0 \<rightarrow>\<^sup>* j\<^sub>1\<close>\<close>
  have tj1: "?j0 + t < ?j1" using tw by linarith
  have ances: "\<forall>j. ?j0 < j \<and> j \<le> ?j1 \<longrightarrow> entry M 0 ?j0 < entry M 0 j"
    by (rule le0_ances_aux[OF baseR])
  have tLM: "?j0 + t < Lng M" using tj1 by simp
  have basePrefix: "(nextrel0 M)\<^sup>*\<^sup>* ?j0 (?j0 + t)"
  proof (cases "t = 0")
    case True thus ?thesis by simp
  next
    case False
    hence j0lt': "?j0 < ?j0 + t" by simp
    show ?thesis
    proof (rule le0_build[OF MT tLM j0lt'])
      show "\<forall>j. ?j0 < j \<and> j \<le> ?j0 + t \<longrightarrow> entry M 0 ?j0 < entry M 0 j"
        using ances tj1 by auto
    qed
  qed
  have chain: "(nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + ((?j0 + t) - ?j0))"
    using lift[OF basePrefix] tj1 by simp
  hence chain': "(nextrel0 (M[n]))\<^sup>*\<^sup>* ?base (?base + t)" by simp
  \<comment> \<open>index bounds\<close>
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have lenMn: "Lng (M[n]) = ?j0 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  have klt: "?j0 + k * w + w \<le> ?j0 + n * w"
  proof -
    have "?j0 + k * w + w = ?j0 + (k + 1) * w" by (simp add: algebra_simps)
    also have "\<dots> \<le> ?j0 + n * w" using mult_le_mono1[of "k+1" n w] kn by simp
    finally show ?thesis .
  qed
  have tww: "t < w" using tw wdef by simp
  have baselt: "?base < Lng (M[n])"
  proof -
    have "?base = ?j0 + k * w" using wdef by simp
    also have "\<dots> < ?j0 + k * w + w" using w0' by simp
    also have "\<dots> \<le> ?j0 + n * w" by (rule klt)
    finally show ?thesis using lenMn by simp
  qed
  have endlt: "?base + t < Lng (M[n])"
  proof -
    have "?base + t = ?j0 + k * w + t" using wdef by simp
    also have "\<dots> < ?j0 + k * w + w" using tww by simp
    also have "\<dots> \<le> ?j0 + n * w" by (rule klt)
    finally show ?thesis using lenMn by simp
  qed
  show ?thesis
    unfolding le0_def using baselt endlt chain' by blast
qed

text \<open>§6.8 d1pos TRANSITIVE block-start reach (\<open>k \<le> r < n\<close>): block \<open>k\<close>'s start
  row-0-reaches block \<open>r\<close>'s start, \<open>le0 (M[n]) (j\<^sub>0+k\<cdot>w) (j\<^sub>0+r\<cdot>w)\<close>.  Induction on the
  gap \<open>r-k\<close>: each step composes one consecutive-block hop
  @{thm [source] oper_d1pos_block_chain} (needs \<open>(r-1)+1=r < n\<close>) via
  @{thm [source] le0_trans}.\<close>

lemma oper_d1pos_le0_start_to_start:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and kr: "k \<le> r"
    and rn: "r < n"
  shows "le0 ((M::pairseq)[n])
            (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
            (parent M 1 (Lng M - 1) + r * (Lng M - 1 - parent M 1 (Lng M - 1)))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  obtain w where wdef: "?w = w" by blast
  have w0: "0 < w" using j0lt wdef by linarith
  have lenMn: "Lng (M[n]) = ?j0 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  \<comment> \<open>induction on the gap \<open>m = r - k\<close>; the target is \<open>k+m\<close>\<close>
  have gen: "\<And>m. k + m < n \<longrightarrow> le0 (M[n]) (?j0 + k * w) (?j0 + (k + m) * w)"
  proof -
    fix m show "k + m < n \<longrightarrow> le0 (M[n]) (?j0 + k * w) (?j0 + (k + m) * w)"
    proof (induction m)
      case 0
      show ?case
      proof
        assume "k + 0 < n"
        hence "k < n" by simp
        hence "?j0 + k * w < ?j0 + n * w" using w0 by simp
        hence "?j0 + k * w < Lng (M[n])" using lenMn by simp
        thus "le0 (M[n]) (?j0 + k * w) (?j0 + (k + 0) * w)" using le0_refl by simp
      qed
    next
      case (Suc m)
      show ?case
      proof
        assume sn: "k + Suc m < n"
        have km: "k + m < n" using sn by simp
        have IH: "le0 (M[n]) (?j0 + k * w) (?j0 + (k + m) * w)" using Suc.IH km by simp
        have k1: "(k + m) + 1 < n" using sn by simp
        have step: "le0 (M[n]) (?j0 + (k + m) * ?w) (?j0 + ((k + m) + 1) * ?w)"
          by (rule oper_d1pos_block_chain[OF L notzero hp i1z j0lt k1])
        have step': "le0 (M[n]) (?j0 + (k + m) * w) (?j0 + (k + Suc m) * w)"
          using step wdef by simp
        show "le0 (M[n]) (?j0 + k * w) (?j0 + (k + Suc m) * w)"
          using le0_trans[OF IH step'] .
      qed
    qed
  qed
  obtain m where mdef: "r = k + m" using kr le_Suc_ex by blast
  have "le0 (M[n]) (?j0 + k * w) (?j0 + (k + m) * w)" using gen mdef rn by simp
  thus ?thesis using wdef mdef by simp
qed

text \<open>§6.8 d1pos block-start reaches ANY later in-range index (\<open>k < n\<close>): the
  block-\<open>k\<close> start \<open>j\<^sub>0+k\<cdot>w\<close> row-0-reaches every \<open>x\<close> with \<open>j\<^sub>0+k\<cdot>w \<le> x < Lng (M[n])\<close>.
  Decompose \<open>x = j\<^sub>0 + r\<cdot>w + t\<close> (block \<open>r\<close>, offset \<open>t < w\<close>, \<open>k \<le> r < n\<close>); chain the
  block-start reach @{thm [source] oper_d1pos_le0_start_to_start} (\<open>k \<rightarrow> r\<close>) with the
  within-block reach @{thm [source] oper_d1pos_le0_within} (block-\<open>r\<close> start \<open>\<rightarrow> +t\<close>)
  via @{thm [source] le0_trans}.\<close>

lemma oper_d1pos_le0_start_to_any:
  assumes MT: "M \<in> T_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and kn: "k < n"
    and xge: "parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)) \<le> x"
    and xlt: "x < Lng ((M::pairseq)[n])"
  shows "le0 ((M::pairseq)[n])
            (parent M 1 (Lng M - 1) + k * (Lng M - 1 - parent M 1 (Lng M - 1)))
            x"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  obtain w where wdef: "?w = w" by blast
  have w0: "0 < w" using j0lt wdef by linarith
  have lenMn: "Lng (M[n]) = ?j0 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  \<comment> \<open>decompose \<open>x - j\<^sub>0 = r\<cdot>w + t\<close> with \<open>t < w\<close>\<close>
  have xge0: "?j0 \<le> x" using xge by linarith
  obtain d where ddef: "d = x - ?j0" by blast
  have xeq: "x = ?j0 + d" using ddef xge0 by simp
  have dlt: "d < n * w" using xeq xlt lenMn by linarith
  define r where "r = d div w"
  define t where "t = d mod w"
  have drt: "d = r * w + t" using r_def t_def by simp
  have tw: "t < w" using w0 t_def by simp
  have rn: "r < n"
  proof -
    have "r * w \<le> d" using drt by linarith
    also have "d < n * w" by (rule dlt)
    finally have "r * w < n * w" .
    thus ?thesis using w0 by simp
  qed
  \<comment> \<open>\<open>k \<le> r\<close>: from \<open>j\<^sub>0 + k\<cdot>w \<le> x = j\<^sub>0 + r\<cdot>w + t\<close>, so \<open>k\<cdot>w \<le> r\<cdot>w + t < (r+1)\<cdot>w\<close>\<close>
  have kr: "k \<le> r"
  proof -
    have xgew: "?j0 + k * w \<le> x" using xge wdef by simp
    have "k * w \<le> d" using xgew xeq by linarith
    hence "k * w < (r + 1) * w" using drt tw by (simp add: algebra_simps)
    hence "k < r + 1" using mult_less_cancel2[of k w "r+1"] w0 by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>block-start chain \<open>k \<rightarrow> r\<close>\<close>
  have c1: "le0 (M[n]) (?j0 + k * w) (?j0 + r * w)"
    using oper_d1pos_le0_start_to_start[OF L notzero hp i1z j0lt kr rn] wdef by simp
  \<comment> \<open>within-block reach in block \<open>r\<close> to offset \<open>t\<close>\<close>
  have tw': "t < ?w" using tw wdef by simp
  have c2: "le0 (M[n]) (?j0 + r * ?w) (?j0 + r * ?w + t)"
    by (rule oper_d1pos_le0_within[OF MT L notzero hp i1z j0lt rn tw'])
  have c2': "le0 (M[n]) (?j0 + r * w) (?j0 + r * w + t)" using c2 wdef by simp
  have xrw: "x = ?j0 + r * w + t" using xeq drt by (simp add: add.assoc)
  have res: "le0 (M[n]) (?j0 + k * w) x"
    using le0_trans[OF c1 c2'] xrw by simp
  show ?thesis using res wdef by simp
qed

lemma oper_d1pos_seg_le0_boundary:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and qn: "q < n"
    and s0eq: "j0red = parent N 1 (Lng N - 1) + s0"
    and s0lt: "s0 < Lng N - 1 - parent N 1 (Lng N - 1)"
    and j0'eq: "j0' = parent N 1 (Lng N - 1)
                  + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0"
    and cap: "j1red = Lng N - 1"
    and j1redspan: "j1red < j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
  shows "le0 (seg ((N::pairseq)[n]) j0' j1')
            (j1red - 1 - j0red + 1)
            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?j1N = "Lng N - 1"
  let ?j0 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?j0"
  let ?c1 = "j1red - 1 - j0red + 1"
  let ?end = "Lng ?Mp - 1"
  have w0: "0 < ?w" using j0lt by linarith
  have s0w': "s0 < ?w" using s0lt .
  \<comment> \<open>\<open>j\<^sub>0\<^sup>red < j\<^sub>1\<^sup>red\<close>, so \<open>c+1 = j\<^sub>1\<^sup>red - j\<^sub>0\<^sup>red\<close>\<close>
  have j0j1red: "j0red < j1red" using s0eq cap s0w' j0lt by linarith
  have c1eq: "?c1 = j1red - j0red" using j0j1red by simp
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  \<comment> \<open>slice length and endpoint identities\<close>
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have endeq: "?end = j1' - j0'" using LMp j0j1' by linarith
  \<comment> \<open>\<open>c+1 \<le> end\<close> (the slice crosses the block boundary, capped span overshoots)\<close>
  have c1le: "?c1 \<le> ?end"
  proof -
    have "?c1 = j1red - j0red" by (rule c1eq)
    also have "\<dots> < j1' - j0'" using j1redspan j0j1red by linarith
    also have "\<dots> = ?end" using endeq by simp
    finally show ?thesis by linarith
  qed
  \<comment> \<open>\<open>j'\<^sub>0 + (c+1) = j\<^sub>0\<^sup>N + (q+1)\<cdot>w\<close> (block-\<open>(q+1)\<close> start)\<close>
  obtain w where wdef: "?w = w" by blast
  have s0c1: "s0 + ?c1 = ?w"
  proof -
    have e: "?c1 = ?j1N - j0red" using cap j0j1red by linarith
    have "s0 + ?c1 = s0 + (?j1N - (?j0 + s0))" using e s0eq by simp
    also have "\<dots> = ?j1N - ?j0" using s0w' j0lt by linarith
    finally show ?thesis .
  qed
  have idx_c1: "j0' + ?c1 = ?j0 + (q + 1) * ?w"
  proof -
    have step1: "j0' + ?c1 = ?j0 + q * ?w + (s0 + ?c1)" using j0'eq by (simp add: add.assoc)
    have step2: "?j0 + q * ?w + (s0 + ?c1) = ?j0 + q * ?w + ?w"
      by (rule arg_cong[OF s0c1, of "\<lambda>z. ?j0 + q * ?w + z"])
    have step3: "?j0 + q * ?w + ?w = ?j0 + (q + 1) * ?w"
    proof -
      have "?j0 + q * w + w = ?j0 + (q + 1) * w" by (simp add: algebra_simps)
      thus ?thesis using wdef by simp
    qed
    from step1 step2 have "j0' + ?c1 = ?j0 + q * ?w + ?w" by (rule trans)
    from this step3 show ?thesis by (rule trans)
  qed
  \<comment> \<open>\<open>j'\<^sub>0 + end = j'\<^sub>1\<close>\<close>
  have idx_end: "j0' + ?end = j1'" using endeq j0'le by simp
  \<comment> \<open>\<open>q+1 < n\<close> from the cap (block-\<open>(q+1)\<close> start \<open>\<le> j'\<^sub>1 < Lng (N[n]) = j\<^sub>0\<^sup>N+n\<cdot>w\<close>)\<close>
  have LngMn: "Lng ?M = ?j0 + n * ?w"
    by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
  have qn1start_le: "?j0 + (q + 1) * ?w \<le> j1'"
  proof -
    have "?j0 + (q + 1) * ?w = j0' + ?c1" using idx_c1 by simp
    also have "\<dots> \<le> j0' + ?end" using c1le by simp
    also have "\<dots> = j1'" using idx_end by simp
    finally show ?thesis .
  qed
  have qn1: "q + 1 < n"
  proof -
    have "?j0 + (q + 1) * ?w \<le> j1'" by (rule qn1start_le)
    also have "j1' < Lng ?M" by (rule j1lt)
    also have "\<dots> = ?j0 + n * ?w" by (rule LngMn)
    finally have "(q + 1) * w < n * w" using wdef by simp
    moreover have "0 < w" using w0 wdef by simp
    ultimately show ?thesis using mult_less_cancel2[of "q+1" w n] by simp
  qed
  \<comment> \<open>===== reduce the slice \<open>le0\<close> to an \<open>N[n]\<close>-level \<open>le0\<close> =====\<close>
  have c1leD: "?c1 \<le> j1' - j0'" using c1le endeq by simp
  have endleD: "?end \<le> j1' - j0'" using endeq by simp
  have seg_iff: "le0 ?Mp ?c1 ?end \<longleftrightarrow> le0 ?M (j0' + ?c1) (j0' + ?end)"
    by (rule adm_le0_seg[OF j1lt c1leD endleD j0'le])
  \<comment> \<open>the \<open>N[n]\<close>-level \<open>le0\<close>: block-\<open>(q+1)\<close> start reaches \<open>j'\<^sub>1\<close> (any later in-range index)\<close>
  have reach: "le0 ?M (?j0 + (q + 1) * ?w) j1'"
    by (rule oper_d1pos_le0_start_to_any[OF N L notzero hp i1z j0lt qn1 qn1start_le j1lt])
  have "le0 ?M (j0' + ?c1) (j0' + ?end)"
    using reach idx_c1 idx_end by simp
  thus ?thesis using seg_iff by simp
qed

text \<open>§6.8 d1pos N-side boundary residual (B3N).  In the capped \<open>\<not>brle\<close> slice
  context the row-1 parent of the last column does NOT exceed the predecessor's
  row-1 entry:
    \<open>entry N 1 (parent N 1 (Lng N-1)) \<le> entry N 1 (Lng N-2)\<close>.

  FALSE in isolation (CE \<open>N=(0,0)(1,1)(2,2)(3,0)(2,2)\<close>: \<open>jm2=1\<close>,
  \<open>entry N 1 4 = 2 > entry N 1 3 = 0\<close>; there the predecessor \<open>Lng N-2 = 3\<close> is
  NOT row-0-reachable to the last column \<open>Lng N-1\<close>, so the \<open>nextrel1\<close> minimality
  clause does not apply to it).  The minimal sufficient extra hypothesis is the
  \<open>fill\<close> condition: the \<open>N\<close>-reference reduced slice \<open>seg N a (Lng N-1)\<close> (with
  \<open>a < Lng N-1\<close>) is a FULL trunk (\<open>TrMax = Lng - 1\<close>).  Then its last trunk step
  \<open>Lng N-2 \<rightarrow> Lng N-1\<close> transfers to \<open>le0 N (Lng N-2)(Lng N-1)\<close>
  (@{thm [source] trunk_le0}, @{thm [source] adm_le0_seg}), and the \<open>nextrel1\<close>
  minimality of the parent \<open>jm2\<close> (from @{thm [source] hasParent_def}) gives
  \<open>entry N 1 (Lng N-2) \<ge> entry N 1 (Lng N-1) > entry N 1 jm2\<close> (when
  \<open>jm2 < Lng N-2\<close>; the case \<open>jm2 = Lng N-2\<close> is reflexive).

  DEEP-VERIFIED (rank 9: \<open>python/d1pos_b3n_fillsuff.py\<close>,
  \<open>python/d1pos_b3n_chain_rand.py\<close>, len\<le>16 maxval=9, 600k\<endash>800k samples): the bare
  claim fails ~10% (3904/37919), but \<open>fill \<Longrightarrow> B3N\<close> has 0 counterexamples over
  18112 fill cases; the keystone transfer \<open>fill \<Longrightarrow> le0 N (Lng N-2)(Lng N-1)\<close>
  is also 0/14315 failures.\<close>

lemma oper_d1pos_b3n_boundary:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS"
    and L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and a_lt: "a < Lng N - 1"
    and fill: "TrMax (seg N a (Lng N - 1)) = Lng (seg N a (Lng N - 1)) - 1"
  shows "entry N 1 (parent N 1 (Lng N - 1)) \<le> entry N 1 (Lng N - 2)"
proof -
  let ?j1N = "Lng N - 1"
  let ?jm2 = "parent N 1 ?j1N"
  let ?S = "seg N a ?j1N"
  \<comment> \<open>\<open>parR1\<close>: the row-1 parent relation \<open>nextrel1 N jm2 (Lng N-1)\<close>\<close>
  have parR1: "nextR N 1 ?jm2 ?j1N"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have nr1: "nextrel1 N ?jm2 ?j1N" using parR1 by (simp add: nextR_def)
  have H1: "entry N 1 ?jm2 < entry N 1 ?j1N" using nr1 by (simp add: nextrel1_def)
  have jm2lt: "?jm2 < ?j1N" using nr1 by (simp add: nextrel1_def)
  \<comment> \<open>the minimality clause of \<open>nextrel1\<close>: \<open>\<forall>j. jm2 < j \<and> le0 N j (Lng N-1) \<longrightarrow> entry N 1 j \<ge> entry N 1 (Lng N-1)\<close>\<close>
  have minim: "\<And>j. ?jm2 < j \<Longrightarrow> le0 N j ?j1N \<Longrightarrow> entry N 1 ?j1N \<le> entry N 1 j"
    using nr1 by (simp add: nextrel1_def)
  \<comment> \<open>\<open>S \<in> T_PS\<close> and its length\<close>
  have ST: "?S \<in> T_PS" using a_lt by (simp add: T_PS_def seg_def)
  have aleN: "a \<le> ?j1N" using a_lt by linarith
  have LS: "Lng ?S = Suc ?j1N - a" using aleN by simp
  have LSpos: "1 < Lng ?S" using LS a_lt by linarith
  \<comment> \<open>last trunk step of the FILLED slice: \<open>le0 S (Lng S-2)(Lng S-1)\<close>\<close>
  have fillT: "TrMax ?S = Lng ?S - 1" by (rule fill)
  have le0S: "le0 ?S (Lng ?S - 2) (Lng ?S - 1)"
  proof -
    have ab: "Lng ?S - 2 \<le> Lng ?S - 1" by simp
    have bT: "Lng ?S - 1 \<le> TrMax ?S" using fillT by simp
    have "leR ?S 0 (Lng ?S - 2) (Lng ?S - 1)"
      by (rule trunk_le0[OF ST ab bT])
    thus ?thesis by (simp add: leR_def)
  qed
  \<comment> \<open>transfer the slice trunk step back to \<open>N\<close>: \<open>le0 N (Lng N-2)(Lng N-1)\<close>\<close>
  have idx_lo: "a + (Lng ?S - 2) = ?j1N - 1"
  proof -
    have "a + (Lng ?S - 2) = a + (Suc ?j1N - a - 2)" using LS by simp
    also have "\<dots> = ?j1N - 1" using a_lt by linarith
    finally show ?thesis .
  qed
  have idx_hi: "a + (Lng ?S - 1) = ?j1N"
  proof -
    have "a + (Lng ?S - 1) = a + (Suc ?j1N - a - 1)" using LS by simp
    also have "\<dots> = ?j1N" using a_lt by linarith
    finally show ?thesis .
  qed
  have lo_le: "Lng ?S - 2 \<le> ?j1N - a" using LS by linarith
  have hi_le: "Lng ?S - 1 \<le> ?j1N - a" using LS by linarith
  have aj1N: "a \<le> ?j1N" using a_lt by linarith
  have j1Nlt: "?j1N < Lng N" using L by linarith
  have le0N: "le0 N (?j1N - 1) ?j1N"
  proof -
    have "le0 N (a + (Lng ?S - 2)) (a + (Lng ?S - 1))"
      using adm_le0_seg[OF j1Nlt lo_le hi_le aj1N] le0S by simp
    thus ?thesis using idx_lo idx_hi by simp
  qed
  \<comment> \<open>combine: either \<open>jm2 = Lng N-2\<close> (reflexive) or minimality applies\<close>
  show ?thesis
  proof (cases "?jm2 = ?j1N - 1")
    case True
    have "?j1N - 1 = Lng N - 2" by simp
    thus ?thesis using True by simp
  next
    case False
    hence "?jm2 < ?j1N - 1" using jm2lt by linarith
    have step: "entry N 1 ?j1N \<le> entry N 1 (?j1N - 1)"
      using minim[OF \<open>?jm2 < ?j1N - 1\<close> le0N] .
    have idxeq2: "?j1N - 1 = Lng N - 2" by simp
    have "entry N 1 ?jm2 \<le> entry N 1 (?j1N - 1)" using step H1 by linarith
    thus ?thesis using idxeq2 by simp
  qed
qed

end
