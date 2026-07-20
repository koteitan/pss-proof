theory Frontier_6_036
  imports Support_6_018
begin

text \<open>§6.8 d1pos \<open>brle\<close>-conclusion closer, CAPPED form (the across-block min-cap
  ACTIVE: \<open>j\<^sub>1\<^sup>red = Lng N - 1 < j\<^sub>0\<^sup>red + (j'\<^sub>1 - j'\<^sub>0)\<close>).  This is the capped twin of
  @{thm [source] TrMax_seg_oper_d1pos_brle_uncapped}: when the \<open>N\<close>-reference trunk
  FILLS its (capped) reduced slice (\<open>fill : TrMax N\<^sub>red = Lng N\<^sub>red - 1\<close>), the
  \<open>M'\<close>-branch is a single component, i.e.\ \<open>brle (M')\<close>.

  Proof by contradiction.  Assume \<open>\<not>brle\<close>, giving \<open>Mlt : TrMax M' < Lng M' - 1\<close>
  and \<open>notle : \<not> le0 M' (TrMax M'+1)(Lng M'-1)\<close>.  Let \<open>c = j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red\<close>
  (\<open>= Lng N\<^sub>red - 2\<close>, \<open>< Lng M' - 1\<close> since the slice crosses the block boundary).

  \<^item> CONFINEMENT \<open>TrMax M' \<le> c\<close>: the boundary row-1 NON-increase
    \<open>entry M' 1 (c+1) \<le> entry M' 1 c\<close> (= B3) makes the trunk step \<open>c \<rightarrow> c+1\<close> fail,
    so by @{thm [source] TrMax_trunk_step} (contrapositive) \<open>TrMax M' \<le> c\<close>.  B3 in
    turn = the N-side boundary inequality \<open>entry N 1 j\<^sub>-\<^sub>2\<^sup>N \<le> entry N 1 (Lng N-2)\<close>
    (B3N, a precisely-scoped inline residual — the H1+H2 decomposition was unsound,
    H2 being false), via the index identities
    \<open>entry M' 1 c = entry N 1 (Lng N-2)\<close> (block \<open>q\<close>, offset \<open>w-1\<close>) and
    \<open>entry M' 1 (c+1) = entry N 1 j\<^sub>-\<^sub>2\<^sup>N\<close> (block \<open>q+1\<close>, offset \<open>0\<close>; \<open>q+1<n\<close> from the
    cap), @{thm [source] oper_d1pos_entry1}.

  \<^item> STRICT-2 \<open>TrMax M' + 1 \<le> c\<close>: if \<open>TrMax M' = c\<close> then \<open>TrMax M' + 1 = c+1\<close> and
    @{thm [source] oper_d1pos_seg_le0_boundary} gives \<open>le0 M' (c+1)(Lng M'-1)\<close>,
    contradicting \<open>notle\<close>.

  \<^item> SYM TRUNK TRANSFER: with the \<open>[0,c]\<close> pointwise agreement (identical to the
    \<open>_eq_span\<close> keystone), the \<open>M'\<close>-side strict-2 confinement \<open>tncM1\<close> and the stop
    \<open>stopM\<close> (from \<open>Mlt\<close>, @{thm [source] TrMax_stop}),
    @{thm [source] TrMax_eq_of_prefix_agree_sym} gives \<open>TrMax M' = TrMax N\<^sub>red\<close>.

  \<^item> CONTRADICTION: \<open>fill\<close> makes \<open>TrMax N\<^sub>red = Lng N\<^sub>red - 1 = c + 1 > c \<ge> TrMax M'\<close>,
    contradicting \<open>TrMax M' = TrMax N\<^sub>red\<close>.

  DEEP-VERIFIED (\<open>python/d1pos_b3_boundary.py\<close>, \<open>python/d1pos_capped_tnc.py\<close>, KMAX=7
  len=12): the capped confinement \<open>TrMax M' \<le> c\<close> 1688/1688, the B3 boundary
  non-increase 1688/1688, the strict-2 \<open>TrMax M'+1 \<le> c\<close> 1688/1688, and the
  boundary \<open>le0\<close> 1688/1688.  Modulo the H2 stub (agent A) and the boundary-\<open>le0\<close>
  residual.\<close>

lemma TrMax_seg_oper_d1pos_brle_capped:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and monoN: "monoT N" and std: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and qn: "q < n"
    and s0w: "j0red < Lng N - 1"
    and s0eq: "j0red = parent N 1 (Lng N - 1) + s0"
    and s0lt: "s0 < Lng N - 1 - parent N 1 (Lng N - 1)"
    and j0'eq: "j0' = parent N 1 (Lng N - 1)
                  + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0"
    and shamt: "shamt = q * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and j1redle: "j1red \<le> Lng N - 1"
    and j0j1red: "j0red < j1red"
    \<comment> \<open>CAPPED span: the min-cap is ACTIVE\<close>
    and cap: "j1red = Lng N - 1"
    and j1redspan: "j1red < j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    \<comment> \<open>the \<open>N\<close>-reference trunk fills its (capped) reduced slice\<close>
    and fill: "TrMax (seg N j0red j1red) = Lng (seg N j0red j1red) - 1"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1')
            = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
       \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1)"
proof (rule ccontr)
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?j0 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?j0"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?j0"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?Npp = "(IncrFirst ^^ shamt) ?Np"
  let ?c = "j1red - 1 - j0red"
  assume "\<not> ?thesis"
  hence ndisj1: "TrMax ?Mp \<noteq> Lng ?Mp - 1"
    and notle: "\<not> le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1)" by auto
  \<comment> \<open>basic facts\<close>
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NppT: "?Npp \<in> T_PS"
  proof -
    have "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
    thus ?thesis by (induction shamt) (simp_all add: T_PS_def IncrFirst_def)
  qed
  have tb: "TrMax ?Mp \<le> Lng ?Mp - 1" by (rule TrMax_bound[OF MpT])
  have Mlt: "TrMax ?Mp < Lng ?Mp - 1" using tb ndisj1 by linarith
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have LNpp: "Lng ?Npp = Suc j1red - j0red" by simp
  have trShift: "TrMax ?Npp = TrMax ?Np" by (rule TrMax_funpow_IncrFirst)
  \<comment> \<open>\<open>c = Lng N\<^sub>red - 2\<close>; \<open>c < Lng M' - 1\<close> (the slice crosses the block boundary)\<close>
  have cLNp: "?c = Lng ?Np - 2" using LNp j0j1red by linarith
  \<comment> \<open>abstract both nat-differences to fresh vars so no decision procedure
     re-expands the nested \<open>j'\<^sub>1 - j'\<^sub>0\<close> / \<open>j\<^sub>1\<^sup>red - j\<^sub>0\<^sup>red\<close>\<close>
  obtain D where Ddef: "D = j1' - j0'" by blast
  obtain E where Edef: "E = j1red - j0red" by blast
  have Dgt: "0 < D" using Ddef j0j1' by linarith
  have spanE: "E < D" using Edef Ddef j1redspan j0j1red by linarith
  have cE: "?c = E - 1" using Edef by simp
  have LMpD: "Lng ?Mp = Suc D" using LMp Ddef j0j1' by linarith
  have cM: "?c < Lng ?Mp"
  proof -
    have "?c < E" using cE Edef j0j1red by linarith
    also have "E < D" by (rule spanE)
    also have "D < Suc D" by simp
    finally show ?thesis using LMpD by simp
  qed
  have cMlt: "?c + 1 < Lng ?Mp"
  proof -
    have "?c + 1 = E" using cE Edef j0j1red by linarith
    also have "E < D" by (rule spanE)
    also have "D < Suc D" by simp
    finally show ?thesis using LMpD by simp
  qed
  have cN: "?c < Lng ?Npp" using LNpp j0j1red by linarith
  \<comment> \<open>========== boundary index identities ==========\<close>
  have w0: "0 < ?w" using j0lt by linarith
  have s0w': "s0 < ?w" using s0lt .
  \<comment> \<open>hold \<open>w\<close> abstract for the block arithmetic (nat-sub double-expansion guard)\<close>
  obtain w where wdef: "?w = w" by blast
  have blockstep: "\<And>k. ?j0 + k * ?w + ?w = ?j0 + (k + 1) * ?w"
  proof -
    fix k
    have "?j0 + k * w + w = ?j0 + (k + 1) * w" by (simp add: algebra_simps)
    thus "?j0 + k * ?w + ?w = ?j0 + (k + 1) * ?w" using wdef by simp
  qed
  \<comment> \<open>\<open>q+1 < n\<close> from the cap: \<open>j'\<^sub>0 + (c+1) = j\<^sub>0\<^sup>N + (q+1)\<cdot>w < Lng (N[n]) = j\<^sub>0\<^sup>N + n\<cdot>w\<close>\<close>
  have LngMn: "Lng ?M = ?j0 + n * ?w"
    by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
  have s0c1: "s0 + (?c + 1) = ?w"
  proof -
    have e: "?c + 1 = ?j1N - j0red" using cap j0j1red by linarith
    have "s0 + (?c + 1) = s0 + (?j1N - (?j0 + s0))" using e s0eq by simp
    also have "\<dots> = ?j1N - ?j0" using s0w' j0lt by linarith
    finally show ?thesis .
  qed
  have idx_c1: "j0' + (?c + 1) = ?j0 + (q + 1) * ?w"
  proof -
    have step1: "j0' + (?c + 1) = ?j0 + q * ?w + (s0 + (?c + 1))" using j0'eq by (simp add: add.assoc)
    have step2: "?j0 + q * ?w + (s0 + (?c + 1)) = ?j0 + q * ?w + ?w"
      by (rule arg_cong[OF s0c1, of "\<lambda>z. ?j0 + q * ?w + z"])
    have step3: "?j0 + q * ?w + ?w = ?j0 + (q + 1) * ?w" by (rule blockstep)
    from step1 step2 have "j0' + (?c + 1) = ?j0 + q * ?w + ?w" by (rule trans)
    from this step3 show ?thesis by (rule trans)
  qed
  have qn1lt: "?j0 + (q + 1) * ?w < ?j0 + n * ?w"
  proof -
    have "j0' + (?c + 1) \<le> j1'" using cMlt LMp by linarith
    hence "?j0 + (q + 1) * ?w \<le> j1'" using idx_c1 by simp
    also have "j1' < Lng ?M" by (rule j1lt)
    finally show ?thesis using LngMn by simp
  qed
  have qn1: "q + 1 < n"
  proof -
    have "?j0 + (q + 1) * w < ?j0 + n * w" using qn1lt wdef by simp
    hence "(q + 1) * w < n * w" by simp
    moreover have "0 < w" using w0 wdef by simp
    ultimately show ?thesis using mult_less_cancel2[of "q+1" w n] by simp
  qed
  \<comment> \<open>\<open>entry M' 1 (c+1) = entry N 1 j\<^sub>-\<^sub>2\<^sup>N\<close> (block \<open>q+1\<close>, offset \<open>0\<close>)\<close>
  have e1_c1: "entry ?Mp 1 (?c + 1) = entry N 1 ?j0"
  proof -
    have "entry ?Mp 1 (?c + 1) = entry ?M 1 (j0' + (?c + 1))"
      using cMlt by (simp add: entry_seg)
    also have "\<dots> = entry ?M 1 (?j0 + (q + 1) * ?w + 0)" using idx_c1 by simp
    also have "\<dots> = entry N 1 (?j0 + 0)"
      by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn1 w0])
    finally show ?thesis by simp
  qed
  \<comment> \<open>\<open>entry M' 1 c = entry N 1 (Lng N-2)\<close> (block \<open>q\<close>, offset \<open>w-1\<close>)\<close>
  have s0c: "s0 + ?c = ?w - 1" using s0c1 w0 by linarith
  have idx_c: "j0' + ?c = ?j0 + q * ?w + (?w - 1)"
  proof -
    have step1: "j0' + ?c = ?j0 + q * ?w + (s0 + ?c)" using j0'eq by (simp add: add.assoc)
    have step2: "?j0 + q * ?w + (s0 + ?c) = ?j0 + q * ?w + (?w - 1)"
      by (rule arg_cong[OF s0c, of "\<lambda>z. ?j0 + q * ?w + z"])
    show ?thesis using step1 step2 by (rule trans)
  qed
  have wm1w: "?w - 1 < ?w"
  proof -
    have "w - 1 < w" using w0 wdef by simp
    thus ?thesis using wdef by simp
  qed
  have j0le1N: "?j0 \<le> ?j1N" by (rule less_imp_le[OF j0lt])
  have j0w: "?j0 + ?w = ?j1N" using le_add_diff_inverse[OF j0le1N] .
  have j0wm1: "?j0 + (?w - 1) = ?j1N - 1"
  proof -
    have "?j0 + (?w - 1) = ?j0 + ?w - 1" using w0 by simp
    also have "\<dots> = ?j1N - 1" using j0w by simp
    finally show ?thesis .
  qed
  have e1_c: "entry ?Mp 1 ?c = entry N 1 (?j1N - 1)"
  proof -
    have "entry ?Mp 1 ?c = entry ?M 1 (j0' + ?c)"
      using cM by (simp add: entry_seg)
    also have "\<dots> = entry ?M 1 (?j0 + q * ?w + (?w - 1))" using idx_c by simp
    also have "\<dots> = entry N 1 (?j0 + (?w - 1))"
      by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn wm1w])
    also have "\<dots> = entry N 1 (?j1N - 1)" using j0wm1 by simp
    finally show ?thesis .
  qed
  \<comment> \<open>========== B3 = H1 + H2 ==========\<close>
  \<comment> \<open>H1: \<open>entry N 1 j\<^sub>-\<^sub>2\<^sup>N < entry N 1 (Lng N-1)\<close>, DIRECT from \<open>parR1\<close>\<close>
  have haspar1: "hasParent N 1 ?j1N" using hp i1z by simp
  have parR1: "nextR N 1 ?j0 ?j1N"
    using haspar1 unfolding hasParent_def parent_def by (rule theI')
  have H1: "entry N 1 ?j0 < entry N 1 ?j1N"
    using parR1 by (simp add: nextR_def nextrel1_def)
  \<comment> \<open>N-side boundary inequality B3N: \<open>entry N 1 j\<^sub>-\<^sub>2 \<le> entry N 1 (Lng N-2)\<close>.
     TRUE in the capped \<open>\<not>brle\<close> slice context (deep-verified 1688/1688,
     python/d1pos_b3_boundary.py).  The earlier \<open>B3 = H1 + H2\<close> decomposition was
     UNSOUND: the row-1 increment bound H2 (\<open>entry N 1 (Lng N-1) \<le> entry N 1 (Lng N-2)+1\<close>)
     is FALSE when the last column's nextrel1-parent is NOT the predecessor
     (CE N=(0,0)(1,1)(2,2)(3,0)(2,2): jm2=1, entry N 1 4=2 > entry N 1 3+1=1).  B3N
     needs the full slice context, so it is a precisely-scoped inline residual (the
     false standalone H2 stub oper_d1pos_row1_incr_bound was removed).\<close>
  have B3N: "entry N 1 ?j0 \<le> entry N 1 (?j1N - 1)"
  proof -
    have fillS: "TrMax (seg N j0red ?j1N) = Lng (seg N j0red ?j1N) - 1"
      using fill cap by simp
    have b3nlem: "entry N 1 (parent N 1 (Lng N - 1)) \<le> entry N 1 (Lng N - 2)"
      by (rule oper_d1pos_b3n_boundary[OF N L haspar1 s0w fillS])
    have idxeq: "?j1N - 1 = Lng N - 2" by simp
    show ?thesis using b3nlem idxeq by simp
  qed
  have B3: "entry ?Mp 1 (?c + 1) \<le> entry ?Mp 1 ?c"
    using B3N e1_c1 e1_c by simp
  \<comment> \<open>========== confinement \<open>TrMax M' \<le> c\<close> via boundary stop ==========\<close>
  have boundary_stop: "\<not> nextR ?Mp 1 ?c (?c + 1)"
  proof
    assume "nextR ?Mp 1 ?c (?c + 1)"
    hence "nextrel1 ?Mp ?c (?c + 1)" by (simp add: nextR_def)
    hence "entry ?Mp 1 ?c < entry ?Mp 1 (?c + 1)" by (simp add: nextrel1_def)
    thus False using B3 by simp
  qed
  have tncM: "TrMax ?Mp \<le> ?c"
  proof (rule ccontr)
    assume "\<not> TrMax ?Mp \<le> ?c"
    hence "?c < TrMax ?Mp" by simp
    hence "nextR ?Mp 1 ?c (?c + 1)" by (rule TrMax_trunk_step[OF MpT])
    thus False using boundary_stop by simp
  qed
  \<comment> \<open>========== strict-2 \<open>TrMax M' + 1 \<le> c\<close> via boundary \<open>le0\<close> + \<open>notle\<close> ==========\<close>
  have tncM1: "TrMax ?Mp + 1 \<le> ?c"
  proof -
    have "TrMax ?Mp \<noteq> ?c"
    proof
      assume eq: "TrMax ?Mp = ?c"
      have "le0 ?Mp (?c + 1) (Lng ?Mp - 1)"
        by (rule oper_d1pos_seg_le0_boundary[OF N L notzero hp i1z j0lt n1 qn
              s0eq s0lt j0'eq cap j1redspan j0j1' j1lt])
      hence "le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1)" using eq by simp
      thus False using notle by simp
    qed
    with tncM show ?thesis by linarith
  qed
  \<comment> \<open>========== pointwise agreement on \<open>[0,c]\<close> (identical to \<open>_eq_span\<close>) ==========\<close>
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Npp ! s"
  proof -
    fix s assume sc: "s \<le> ?c"
    have sM: "s < Suc j1' - j0'" using sc cM LMp by linarith
    have sNp: "s < Suc j1red - j0red" using sc cN LNpp by linarith
    have s0sw: "s0 + s < ?w"
    proof -
      have "j0red + s \<le> j1red - 1" using sc j0j1red by linarith
      hence "?j0 + s0 + s \<le> ?j1N - 1" using s0eq j1redle j0j1red by linarith
      thus ?thesis using j0lt by linarith
    qed
    have lhs_idx: "j0' + s = ?j0 + q * ?w + (s0 + s)" using j0'eq by (simp add: add.assoc)
    have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
    also have "\<dots> = ?M ! (?j0 + q * ?w + (s0 + s))" by (rule arg_cong[OF lhs_idx, of "(!) ?M"])
    also have "\<dots> = (entry N 0 (?j0 + (s0 + s)) + q * ?delta, entry N 1 (?j0 + (s0 + s)))"
      by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt qn s0sw])
    finally have LHS: "?Mp ! s = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))"
      using shamt by simp
    have ii: "s < Lng ?Np" using sNp by simp
    have R0: "entry ?Npp 0 s = entry ?Np 0 s + shamt"
      by (rule entry_funpow_IncrFirst0[OF ii])
    have R1: "entry ?Npp 1 s = entry ?Np 1 s"
      by (rule entry_funpow_IncrFirst1[OF ii])
    have segN0: "entry ?Np 0 s = entry N 0 (?j0 + (s0 + s))"
    proof -
      have "?Np ! s = N ! (j0red + s)" using sNp by (rule seg_nth_eq)
      thus ?thesis using s0eq by (simp add: entry_def add.assoc)
    qed
    have segN1: "entry ?Np 1 s = entry N 1 (?j0 + (s0 + s))"
    proof -
      have "?Np ! s = N ! (j0red + s)" using sNp by (rule seg_nth_eq)
      thus ?thesis using s0eq by (simp add: entry_def add.assoc)
    qed
    have ilenpp: "s < length ?Npp" using LNpp sNp by simp
    have "?Npp ! s = (entry ?Npp 0 s, entry ?Npp 1 s)"
      using ilenpp by (cases "?Npp ! s") (simp add: entry_def)
    also have "\<dots> = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))"
      using R0 R1 segN0 segN1 by simp
    finally have RHS: "?Npp ! s = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))" .
    show "?Mp ! s = ?Npp ! s" using LHS RHS by simp
  qed
  \<comment> \<open>========== SYM transfer: \<open>TrMax M' = TrMax N\<^sub>red\<close> ==========\<close>
  have stopM: "\<not> nextR ?Mp 1 (TrMax ?Mp) (TrMax ?Mp + 1)"
    by (rule TrMax_stop[OF MpT Mlt])
  have TrEq: "TrMax ?Mp = TrMax ?Npp"
    by (rule TrMax_eq_of_prefix_agree_sym[OF MpT NppT agree cM cN tncM1 stopM])
  have TrEqNp: "TrMax ?Mp = TrMax ?Np" using TrEq trShift by simp
  \<comment> \<open>========== contradiction: \<open>fill\<close> forces \<open>TrMax N\<^sub>red = c+1 > c \<ge> TrMax M'\<close> ==========\<close>
  have "TrMax ?Np = Lng ?Np - 1" by (rule fill)
  hence "TrMax ?Mp = ?c + 1" using TrEqNp cLNp LNp j0j1red by linarith
  thus False using tncM by linarith
qed

text \<open>§6.8 d1pos CAPPED trunk-confinement \<open>tnc\<close> (\<open>oper_d1pos_ctx_tnc_capped\<close>) — the
  LAST missing discharger for the four cell-assembly lemmas
  (\<open>oper_d1pos_notbrle_LOW_take_eq_regA\<close> / \<open>_regB\<close> / \<open>_boundary\<close> /
  \<open>_periodic\<close>, all defined below), all of which carry the reference-trunk confinement
  \<open>tnc : TrMax (seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red) \<le> j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red\<close> as a hypothesis.

  STEP-0 RESOLUTION (sub-agent tncdis, rank-stratified SkT_PS generator
  \<open>gen_std\<close> = diagSeq base \<rightarrow> oper-closure \<rightarrow> is_standard; KMAX=10, len\<le>12,
  399 in-context \<open>N\<close>, 7074 in-context \<open>\<not>brle\<close> slice cases).  The decisive findings:

  \<^item> \<open>tnc\<close> (both \<open>\<le>\<close> and STRICT \<open><\<close>) is UNIVERSAL in-context: 7074/7074.  Equivalently
    \<open>TrMax (seg N j\<^sub>0' (Lng N-1)) = TrMax (seg N j\<^sub>0' (Lng N-1))\<close> is never a full
    trunk (\<open>Br \<noteq> []\<close>; \<open>fill_count = 0\<close>).

  \<^item> But \<open>tnc\<close> is NOT a pure \<open>N\<close>-fact: \<open>seg N a (Lng N-1)\<close> IS a full trunk for
    148/3091 \<open>(N,a)\<close> pairs (e.g.\ \<open>N=(0,0)(1,1)(2,2)\<close>, \<open>a=0\<close>: row-1 \<open>[0,1,2]\<close>
    climbs straight to the boundary).  Those \<open>N\<close> are exactly the ones \<open>\<not>brle\<close>
    EXCLUDES — the implication \<open>fill \<Longrightarrow> brle(M')\<close> is what makes \<open>tnc\<close> hold.

  \<^item> The keystone \<open>le0 N (Lng N-2)(Lng N-1)\<close> is NON-universal in-context (1080/7074),
    and BARE B3N \<open>entry N 1 jm2 \<le> entry N 1 (Lng N-2)\<close> is ALSO non-universal
    in-context: 8 in-context \<open>N\<close>-families are B3N-FALSE (e.g.\
    \<open>N=(0,0)(1,1)(2,2)(3,0)(2,2)\<close>, \<open>jm2=1\<close>, \<open>entry N 1 1 = 1 > entry N 1 3 = 0\<close>),
    and for those the \<open>M'\<close>-side cut-B3 \<open>entry M' 1 (c+1) \<le> entry M' 1 c\<close> is FALSE
    too — so NEITHER @{thm [source] oper_d1pos_ctx_b3n} (keystone) NOR
    @{thm [source] oper_d1pos_ctx_tnc} (per-slice cut-B3) discharges \<open>tnc\<close>
    universally.  In those B3N-false cases the \<open>M'\<close>-trunk stops EARLY (at the first
    row-1 drop / block-boundary copy), strictly below the cut \<open>c\<close>, so \<open>tnc\<close> still
    holds — but for a reason that is NOT a single inequality at \<open>c\<close>.

  The SOUND universal route is the CONTRAPOSITIVE of the already-green
  @{thm [source] TrMax_seg_oper_d1pos_brle_capped}: that lemma proves
  \<open>fill (TrMax N\<^sub>red = Lng N\<^sub>red - 1) \<Longrightarrow> brle(M')\<close>; contrapositively \<open>\<not>brle(M')\<close>
  gives \<open>\<not>fill\<close>, and with @{thm [source] TrMax_bound} (\<open>TrMax \<le> Lng-1\<close>) the only
  remaining possibility is \<open>TrMax N\<^sub>red \<le> Lng N\<^sub>red - 2 = j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red\<close>, i.e.
  exactly \<open>tnc\<close>.  This carries NO new empirical residual — it reuses the
  deep-verified \<open>_brle_capped\<close> machinery wholesale.\<close>

lemma oper_d1pos_ctx_tnc_capped:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and monoN: "monoT N" and std: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and qn: "q < n"
    and s0w: "j0red < Lng N - 1"
    and s0eq: "j0red = parent N 1 (Lng N - 1) + s0"
    and s0lt: "s0 < Lng N - 1 - parent N 1 (Lng N - 1)"
    and j0'eq: "j0' = parent N 1 (Lng N - 1)
                  + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0"
    and shamt: "shamt = q * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and j1redle: "j1red \<le> Lng N - 1"
    and j0j1red: "j0red < j1red"
    and cap: "j1red = Lng N - 1"
    and j1redspan: "j1red < j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    \<comment> \<open>\<open>\<not>brle\<close> on the consumer slice \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close>\<close>
    and notbrle: "\<not> (TrMax (seg ((N::pairseq)[n]) j0' j1')
                        = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
                      \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
                            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
                            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1))"
  shows "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
proof -
  let ?Np = "seg N j0red j1red"
  \<comment> \<open>contrapositive of @{thm [source] TrMax_seg_oper_d1pos_brle_capped}:
     \<open>\<not>brle(M')\<close> excludes the \<open>fill\<close> (full-trunk) case\<close>
  have notfill: "TrMax ?Np \<noteq> Lng ?Np - 1"
  proof
    assume fill: "TrMax ?Np = Lng ?Np - 1"
    have "TrMax (seg ((N::pairseq)[n]) j0' j1')
            = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
       \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1)"
      by (rule TrMax_seg_oper_d1pos_brle_capped[OF N monoN std L notzero hp i1z j0lt
            n1 qn s0w s0eq s0lt j0'eq shamt j1redle j0j1red cap j1redspan j0j1' j1lt fill])
    thus False using notbrle by simp
  qed
  \<comment> \<open>\<open>Lng N\<^sub>red - 1 = j\<^sub>1\<^sup>red - j\<^sub>0\<^sup>red\<close>, and \<open>TrMax \<le> Lng - 1\<close>, so \<open>\<not>fill\<close> forces \<open>\<le> Lng - 2\<close>\<close>
  have NpT: "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
  have lenNp: "Lng ?Np - 1 = j1red - j0red" using j0j1red by (simp del: Lng_seg add: Lng_seg)
  have tb: "TrMax ?Np \<le> Lng ?Np - 1" by (rule TrMax_bound[OF NpT])
  have "TrMax ?Np < Lng ?Np - 1" using tb notfill by linarith
  hence "TrMax ?Np < j1red - j0red" using lenNp by simp
  thus ?thesis using j0j1red by linarith
qed

text \<open>§6.8 sub-case A block-fold groundwork.  In the d0zero periodic layout
  \<open>M[n] = take j\<^sub>0 M @ (block)\<^bsup>n\<^esup>\<close>, the row-0 value at any index \<open>x \<ge> j\<^sub>0\<close> is at
  least the block-start minimum \<open>M\<^bsub>0,j\<^sub>0\<^esub>\<close> (combine
  @{thm [source] oper_d0zero_entry0} with @{thm [source] parent_block_entry0_min}).\<close>

lemma oper_d0zero_entry0_min:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
    and x0: "parent M 0 (Lng M - 1) \<le> x"
    and xlt: "x < parent M 0 (Lng M - 1) + n * (Lng M - 1 - parent M 0 (Lng M - 1))"
  shows "entry M 0 (parent M 0 (Lng M - 1)) \<le> entry ((M::pairseq)[n]) 0 x"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  let ?s = "(x - ?j0) mod ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have sw: "?s < ?w" using w0 by simp
  have parR0: "nextrel0 M ?j0 (Lng M - 1)"
  proof -
    have hp0: "hasParent M 0 (Lng M - 1)" using hp i1z by simp
    have "nextR M 0 ?j0 (Lng M - 1)"
      using hp0 unfolding hasParent_def parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  have eq: "entry ((M::pairseq)[n]) 0 x = entry M 0 (?j0 + ?s)"
    using oper_d0zero_entry0[OF L notzero hp i1z j0lt x0 xlt] .
  have "entry M 0 ?j0 \<le> entry M 0 (?j0 + ?s)"
    using parent_block_entry0_min(1)[OF parR0 sw] .
  thus ?thesis using eq by simp
qed

text \<open>Single block-fold step (the iterated @{thm [source] m_6_2_P_additive} brick for
  sub-case A).  In the d0zero layout, splitting the slice \<open>seg (M[n]) a (B+s)\<close> at a
  block boundary \<open>B = j\<^sub>0 + k\<cdot>w\<close> (\<open>k \<ge> 1\<close>, left-minimal because every block-start
  carries the row-0 minimum \<open>M\<^bsub>0,j\<^sub>0\<^esub>\<close>) peels the trailing partial block
  \<open>seg M j\<^sub>0 (j\<^sub>0+s)\<close>, which is itself a single \<open>P\<close>-component.\<close>

lemma oper_d0zero_seg_P_split:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and aB: "parent M 0 (Lng M - 1) < a"
    and k1: "1 \<le> k"
    and ale: "a < parent M 0 (Lng M - 1) + k * (Lng M - 1 - parent M 0 (Lng M - 1))"
    and sw: "s < Lng M - 1 - parent M 0 (Lng M - 1)"
    and blockmono: "le0 M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + s)"
    and Bsk: "parent M 0 (Lng M - 1) + k * (Lng M - 1 - parent M 0 (Lng M - 1)) + s
                < Lng ((M::pairseq)[n])"
    and kn: "k < n"
  shows "P (seg ((M::pairseq)[n]) a
              (parent M 0 (Lng M - 1) + k * (Lng M - 1 - parent M 0 (Lng M - 1)) + s))
       = P (seg ((M::pairseq)[n]) a
              (parent M 0 (Lng M - 1) + k * (Lng M - 1 - parent M 0 (Lng M - 1)) - 1))
       @ [seg M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + s)]"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  let ?B = "?j0 + k * ?w"  let ?MN = "(M::pairseq)[n]"
  let ?Q = "seg ?MN a (?B + s)"
  have w0: "0 < ?w" using aB ale k1
    by (cases "?w = 0") auto
  have j0lt: "?j0 < Lng M - 1" using w0 by linarith
  have aB': "a < ?B" using ale .
  \<comment> \<open>length of the slice and the cut index \<open>c = B - a\<close>\<close>
  have lenQ: "Lng ?Q = Suc (?B + s) - a" by (rule Lng_seg)
  let ?c = "?B - a"
  have c0: "0 < ?c" using aB' by simp
  have BsM: "?B + s < Lng ?MN" using Bsk by simp
  have aleBs: "a \<le> ?B + s" using aB' by simp
  have cQ: "?c \<le> Lng ?Q - 1" using lenQ aB' aleBs by linarith
  have QT: "?Q \<in> T_PS"
  proof -
    have "0 < Lng ?Q" using lenQ aleBs by linarith
    hence "?Q \<noteq> []" using length_greater_0_conv by blast
    thus ?thesis by (simp add: T_PS_def)
  qed
  \<comment> \<open>row-0 of \<open>Q\<close> at the cut \<open>= M\<^bsub>0,j\<^sub>0\<^esub>\<close> (block start)\<close>
  have nseg: "\<And>i. i < Suc (?B + s) - a \<Longrightarrow> ?Q ! i = ?MN ! (a + i)"
    by (rule seg_nth_eq)
  have cidx: "?c < Suc (?B + s) - a" using aB' by linarith
  have entryQc: "entry ?Q 0 ?c = entry ?MN 0 ?B"
  proof -
    have "?Q ! ?c = ?MN ! (a + ?c)" using cidx by (rule nseg)
    moreover have "a + ?c = ?B" using aB' by simp
    ultimately show ?thesis by (simp add: entry_def)
  qed
  have Bval: "entry ?MN 0 ?B = entry M 0 ?j0"
  proof -
    have x0: "?j0 \<le> ?B" by simp
    have xlt: "?B < ?j0 + n * ?w" using kn w0 by (simp add: mult_strict_right_mono)
    have "entry ?MN 0 ?B = entry M 0 (?j0 + (?B - ?j0) mod ?w)"
      using oper_d0zero_entry0[OF L notzero hp i1z j0lt x0 xlt] .
    moreover have "(?B - ?j0) mod ?w = 0" by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>left-minimality at the cut: every earlier index has row-0 \<open>\<ge> M\<^bsub>0,j\<^sub>0\<^esub>\<close>\<close>
  have lmin: "\<And>j. j < ?c \<Longrightarrow> entry ?Q 0 ?c \<le> entry ?Q 0 j"
  proof -
    fix j assume jc: "j < ?c"
    have jidx: "j < Suc (?B + s) - a" using jc cidx by linarith
    have "?Q ! j = ?MN ! (a + j)" using jidx by (rule nseg)
    hence eQj: "entry ?Q 0 j = entry ?MN 0 (a + j)" by (simp add: entry_def)
    have ge: "?j0 \<le> a + j" using aB by simp
    have lt: "a + j < ?j0 + n * ?w"
    proof -
      have "a + j < ?B" using jc aB' by linarith
      also have "?B \<le> ?j0 + n * ?w" using kn w0 by (simp add: mult_le_mono1 less_imp_le)
      finally show ?thesis .
    qed
    have "entry M 0 ?j0 \<le> entry ?MN 0 (a + j)"
      using oper_d0zero_entry0_min[OF L notzero hp i1z j0lt ge lt] .
    thus "entry ?Q 0 ?c \<le> entry ?Q 0 j"
      using eQj entryQc Bval by simp
  qed
  \<comment> \<open>apply \<open>P\<close>-additivity at the cut\<close>
  have padd: "P ?Q = P (seg ?Q 0 (?c - 1)) @ P (seg ?Q ?c (Lng ?Q - 1))"
    by (rule m_6_2_P_additive[OF QT c0 cQ lmin])
  \<comment> \<open>left part \<open>= seg (M[n]) a (B-1)\<close>\<close>
  have left: "seg ?Q 0 (?c - 1) = seg ?MN a (?B - 1)"
  proof -
    have "seg ?Q 0 (?c - 1) = seg ?MN (a + 0) (a + (?c - 1))"
      by (rule seg_of_seg[OF aleBs]) (use cQ lenQ in linarith)
    moreover have "a + (?c - 1) = ?B - 1" using aB' by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>right part \<open>= seg (M[n]) B (B+s)\<close>, a single block which reads off \<open>seg M j\<^sub>0 (j\<^sub>0+s)\<close>\<close>
  have right_seg: "seg ?Q ?c (Lng ?Q - 1) = seg ?MN ?B (?B + s)"
  proof -
    have "seg ?Q ?c (Lng ?Q - 1) = seg ?MN (a + ?c) (a + (Lng ?Q - 1))"
      by (rule seg_of_seg[OF aleBs]) simp
    moreover have "a + ?c = ?B" using aB' by simp
    moreover have "a + (Lng ?Q - 1) = ?B + s" using lenQ aleBs by linarith
    ultimately show ?thesis by simp
  qed
  have blockseg: "seg ?MN ?B (?B + s) = seg M ?j0 (?j0 + s)"
  proof (rule nth_equalityI)
    show "length (seg ?MN ?B (?B + s)) = length (seg M ?j0 (?j0 + s))" by simp
    fix i assume "i < length (seg ?MN ?B (?B + s))"
    hence ic: "i < Suc s" by simp
    have e1: "seg ?MN ?B (?B + s) ! i = ?MN ! (?j0 + k * ?w + i)"
      using ic by (simp add: seg_nth_eq)
    have e2: "?MN ! (?j0 + k * ?w + i) = M ! (?j0 + i)"
      by (rule oper_d0zero_nth[OF L notzero hp i1z j0lt kn]) (use ic sw in linarith)
    have e3: "M ! (?j0 + i) = seg M ?j0 (?j0 + s) ! i" using ic by (simp add: seg_nth_eq)
    show "seg ?MN ?B (?B + s) ! i = seg M ?j0 (?j0 + s) ! i" using e1 e2 e3 by simp
  qed
  have right_single: "P (seg M ?j0 (?j0 + s)) = [seg M ?j0 (?j0 + s)]"
  proof (rule poper_P_nonmulti)
    show "\<not> (multiT (seg M ?j0 (?j0 + s)) \<and> 1 < Lng (seg M ?j0 (?j0 + s)))"
    proof (cases "1 < Lng (seg M ?j0 (?j0 + s))")
      case True
      \<comment> \<open>the block fragment is mono (its left end is the row-0 ancestor of every entry),
         hence not multi: \<open>j\<^sub>0\<close> is \<open>\<le>\<^sub>M\<close> the right end\<close>
      have Lseg: "Lng (seg M ?j0 (?j0 + s)) = Suc s" by simp
      have s1: "1 \<le> s" using True Lseg by simp
      have le0js: "le0 M ?j0 (?j0 + s)" using blockmono .
      have segmono: "monoT (seg M ?j0 (?j0 + s))"
      proof -
        have segL: "?j0 + s < Lng M" using sw j0lt by linarith
        have eqv: "le0 (seg M ?j0 (?j0 + s)) 0 s = le0 M (?j0 + 0) (?j0 + s)"
          using adm_le0_seg[OF segL, where a=0 and b=s and j0'="?j0"] by simp
        have "le0 (seg M ?j0 (?j0 + s)) 0 s" using eqv le0js by simp
        hence le00: "leR (seg M ?j0 (?j0 + s)) 0 0 (Lng (seg M ?j0 (?j0 + s)) - 1)"
          using Lseg by (simp add: leR_def)
        have nz: "\<not> zeroT (seg M ?j0 (?j0 + s))" using True by (simp add: zeroT_def)
        show ?thesis using le00 nz by (simp add: monoT_def)
      qed
      thus ?thesis by (simp add: multiT_def)
    next
      case False thus ?thesis by simp
    qed
  qed
  have right: "P (seg ?Q ?c (Lng ?Q - 1)) = [seg M ?j0 (?j0 + s)]"
    using right_seg blockseg right_single by simp
  show ?thesis using padd left right by simp
qed

text \<open>Whole-block fold: iterating @{thm [source] oper_d0zero_seg_P_split} at \<open>s = w-1\<close>
  over the \<open>m\<close> block boundaries \<open>j\<^sub>0+w, \<dots>, j\<^sub>0+m\<cdot>w\<close> peels \<open>m-1\<close> verbatim copies of the
  full block \<open>blk = seg M j\<^sub>0 (Lng M-2)\<close> off the right of a block-0-anchored slice.\<close>

lemma oper_d0zero_seg_P_hfold:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and aB: "parent M 0 (Lng M - 1) < a"
    and aw: "a \<le> Lng M - 2"
    and blockmono: "\<And>s. s < Lng M - 1 - parent M 0 (Lng M - 1)
                      \<Longrightarrow> le0 M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + s)"
    and mn: "m \<le> n"
    and m1: "1 \<le> m"
  shows "P (seg ((M::pairseq)[n]) a
              (parent M 0 (Lng M - 1) + m * (Lng M - 1 - parent M 0 (Lng M - 1)) - 1))
       = P (seg ((M::pairseq)[n]) a (Lng M - 2))
       @ replicate (m - 1) (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  let ?MN = "(M::pairseq)[n]"  let ?blk = "seg M ?j0 (Lng M - 2)"
  have w0: "0 < ?w" using aB aw by linarith
  have j0w1: "?j0 + ?w - 1 = Lng M - 2" using w0 by simp
  have j0lt: "?j0 < Lng M - 1" using w0 by linarith
  have lenMN: "Lng ?MN = ?j0 + n * ?w"
  proof -
    have e: "?MN = take ?j0 M @ concat (replicate n (map ((!) M) [?j0..<Lng M - 1]))"
      by (rule oper_d0zero_expand[OF L notzero hp i1z])
    have t: "length (take ?j0 M) = ?j0" using j0lt by simp
    have b: "length (map ((!) M) [?j0..<Lng M - 1]) = ?w" by simp
    show ?thesis using e t b by (simp add: length_concat sum_list_replicate)
  qed
  show ?thesis using mn m1
  proof (induction m)
    case 0 thus ?case by simp
  next
    case (Suc m)
    show ?case
    proof (cases "m = 0")
      case True
      have "?j0 + Suc m * ?w - 1 = Lng M - 2" using True j0w1 by simp
      thus ?thesis using True by simp
    next
      case False
      hence m1': "1 \<le> m" by simp
      have Smn: "Suc m \<le> n" using Suc.prems by simp
      have mln: "m < n" using Smn by simp
      \<comment> \<open>peel the \<open>m\<close>-th full block via the step lemma at boundary \<open>j\<^sub>0+m\<cdot>w\<close>, \<open>s=w-1\<close>\<close>
      have sw: "?w - 1 < ?w" using w0 by simp
      have bm: "le0 M ?j0 (?j0 + (?w - 1))" using blockmono[OF sw] .
      have aboundary: "a < ?j0 + m * ?w"
      proof -
        have "a \<le> ?j0 + ?w - 1" using aw j0w1 by simp
        also have "?j0 + ?w - 1 < ?j0 + ?w" using w0 by simp
        also have "?j0 + ?w \<le> ?j0 + m * ?w" using m1' by simp
        finally show ?thesis .
      qed
      have Bsk: "?j0 + m * ?w + (?w - 1) < Lng ?MN"
      proof -
        have "?j0 + m * ?w + (?w - 1) < ?j0 + Suc m * ?w" using w0 by simp
        also have "?j0 + Suc m * ?w \<le> ?j0 + n * ?w"
          using mult_le_mono1[OF Smn, of ?w] by linarith
        finally show ?thesis using lenMN by simp
      qed
      have step: "P (seg ?MN a (?j0 + m * ?w + (?w - 1)))
                 = P (seg ?MN a (?j0 + m * ?w - 1)) @ [seg M ?j0 (?j0 + (?w - 1))]"
        by (rule oper_d0zero_seg_P_split[OF L notzero hp i1z aB m1' aboundary sw bm Bsk mln])
      have rend: "?j0 + m * ?w + (?w - 1) = ?j0 + Suc m * ?w - 1" using w0 by simp
      have j0we: "?j0 + (?w - 1) = Lng M - 2" using w0 j0w1 by linarith
      have blk_eq: "seg M ?j0 (?j0 + (?w - 1)) = ?blk" using j0we by simp
      have mlen: "m \<le> n" using mln by simp
      have IH: "P (seg ?MN a (?j0 + m * ?w - 1))
              = P (seg ?MN a (Lng M - 2)) @ replicate (m - 1) ?blk"
        by (rule Suc.IH[OF mlen m1'])
      have repl: "replicate (m - 1) ?blk @ [?blk] = replicate m ?blk"
      proof -
        have "replicate (m - 1) ?blk @ [?blk] = ?blk # replicate (m - 1) ?blk"
          by (rule replicate_append_same)
        also have "\<dots> = replicate (Suc (m - 1)) ?blk" by simp
        also have "Suc (m - 1) = m" using m1' by simp
        finally show ?thesis .
      qed
      have "P (seg ?MN a (?j0 + Suc m * ?w - 1))
          = P (seg ?MN a (?j0 + m * ?w - 1)) @ [?blk]"
        using step rend blk_eq by simp
      also have "\<dots> = P (seg ?MN a (Lng M - 2)) @ (replicate (m - 1) ?blk @ [?blk])"
        using IH by simp
      also have "\<dots> = P (seg ?MN a (Lng M - 2)) @ replicate m ?blk"
        using repl by simp
      finally show ?thesis by simp
    qed
  qed
qed

text \<open>Block-1-anchored fold (§6.8 d0zero case-A pure-block regime, \<open>j'\<^sub>0 = j\<^sub>0\<^sup>N\<close>): a
  slice that STARTS at the block-1 boundary \<open>j\<^sub>0 + w\<close> and ends inside block \<open>m+1\<close>
  decomposes into \<open>m\<close> verbatim copies of the full block \<open>blk = seg M j\<^sub>0 (Lng M-2)\<close>
  followed by one partial block \<open>seg M j\<^sub>0 (j\<^sub>0+s)\<close>.  Like
  @{thm [source] oper_d0zero_seg_P_hfold}, but with empty branch prefix
  (the base case \<open>m=0\<close> is the single block-1 fragment, a non-multi component).\<close>

lemma oper_d0zero_seg_P_blk1fold:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
    and blockmono: "\<And>s. s < Lng M - 1 - parent M 0 (Lng M - 1)
                      \<Longrightarrow> le0 M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + s)"
    and sw: "s < Lng M - 1 - parent M 0 (Lng M - 1)"
    and mn: "Suc m < n"
  shows "P (seg ((M::pairseq)[n])
              (parent M 0 (Lng M - 1) + (Lng M - 1 - parent M 0 (Lng M - 1)))
              (parent M 0 (Lng M - 1) + Suc m * (Lng M - 1 - parent M 0 (Lng M - 1)) + s))
       = replicate m (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))
       @ [seg M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + s)]"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  let ?MN = "(M::pairseq)[n]"  let ?blk = "seg M ?j0 (Lng M - 2)"
  let ?a = "?j0 + ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w - 1 = Lng M - 2" using w0 by simp
  have aB: "?j0 < ?a" using w0 by simp
  have parR0: "nextrel0 M ?j0 (Lng M - 1)"
  proof -
    have hp0: "hasParent M 0 (Lng M - 1)" using hp i1z by simp
    have "nextR M 0 ?j0 (Lng M - 1)"
      using hp0 unfolding hasParent_def parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  have lenMN: "Lng ?MN = ?j0 + n * ?w"
  proof -
    have e: "?MN = take ?j0 M @ concat (replicate n (map ((!) M) [?j0..<Lng M - 1]))"
      by (rule oper_d0zero_expand[OF L notzero hp i1z])
    have t: "length (take ?j0 M) = ?j0" using j0lt by simp
    have b: "length (map ((!) M) [?j0..<Lng M - 1]) = ?w" by simp
    show ?thesis using e t b by (simp add: length_concat sum_list_replicate)
  qed
  have gen: "\<And>s m. s < ?w \<Longrightarrow> Suc m < n \<Longrightarrow>
       P (seg ?MN ?a (?j0 + Suc m * ?w + s))
       = replicate m ?blk @ [seg M ?j0 (?j0 + s)]"
  proof -
    fix s0 m0
    show "s0 < ?w \<Longrightarrow> Suc m0 < n \<Longrightarrow>
       P (seg ?MN ?a (?j0 + Suc m0 * ?w + s0))
       = replicate m0 ?blk @ [seg M ?j0 (?j0 + s0)]"
    proof (induction m0 arbitrary: s0)
    case (0 s)
    note sw = \<open>s < ?w\<close>
    \<comment> \<open>base: the block-1 fragment \<open>seg (M[n]) (j\<^sub>0+w) (j\<^sub>0+w+s)\<close> reads \<open>seg M j\<^sub>0 (j\<^sub>0+s)\<close>,
       a single non-multi \<open>P\<close>-component\<close>
    have S1n: "1 < n" using "0.prems" by simp
    have blockseg: "seg ?MN ?a (?a + s) = seg M ?j0 (?j0 + s)"
    proof (rule nth_equalityI)
      show "length (seg ?MN ?a (?a + s)) = length (seg M ?j0 (?j0 + s))" by simp
      fix i assume "i < length (seg ?MN ?a (?a + s))"
      hence ic: "i < Suc s" by simp
      have e1: "seg ?MN ?a (?a + s) ! i = ?MN ! (?j0 + 1 * ?w + i)"
        using ic by (simp add: seg_nth_eq)
      have e2: "?MN ! (?j0 + 1 * ?w + i) = M ! (?j0 + i)"
        by (rule oper_d0zero_nth[OF L notzero hp i1z j0lt S1n]) (use ic sw in linarith)
      have e3: "M ! (?j0 + i) = seg M ?j0 (?j0 + s) ! i" using ic by (simp add: seg_nth_eq)
      show "seg ?MN ?a (?a + s) ! i = seg M ?j0 (?j0 + s) ! i" using e1 e2 e3 by simp
    qed
    have bm: "le0 M ?j0 (?j0 + s)" using blockmono[OF sw] .
    have single: "P (seg M ?j0 (?j0 + s)) = [seg M ?j0 (?j0 + s)]"
    proof (rule poper_P_nonmulti)
      show "\<not> (multiT (seg M ?j0 (?j0 + s)) \<and> 1 < Lng (seg M ?j0 (?j0 + s)))"
      proof (cases "1 < Lng (seg M ?j0 (?j0 + s))")
        case True
        have Lseg: "Lng (seg M ?j0 (?j0 + s)) = Suc s" by simp
        have segmono: "monoT (seg M ?j0 (?j0 + s))"
        proof -
          have segL: "?j0 + s < Lng M" using sw j0lt by linarith
          have eqv: "le0 (seg M ?j0 (?j0 + s)) 0 s = le0 M (?j0 + 0) (?j0 + s)"
            using adm_le0_seg[OF segL, where a=0 and b=s and j0'="?j0"] by simp
          have "le0 (seg M ?j0 (?j0 + s)) 0 s" using eqv bm by simp
          hence le00: "leR (seg M ?j0 (?j0 + s)) 0 0 (Lng (seg M ?j0 (?j0 + s)) - 1)"
            using Lseg by (simp add: leR_def)
          have nz: "\<not> zeroT (seg M ?j0 (?j0 + s))" using True by (simp add: zeroT_def)
          show ?thesis using le00 nz by (simp add: monoT_def)
        qed
        thus ?thesis by (simp add: multiT_def)
      next
        case False thus ?thesis by simp
      qed
    qed
    have "?j0 + Suc 0 * ?w + s = ?a + s" by simp
    thus ?case using blockseg single by simp
  next
    case (Suc m s)
    note sw = \<open>s < ?w\<close>
    have Smn: "Suc (Suc m) < n" using Suc.prems(2) by simp
    have Smn1: "Suc m < n" using Smn by simp
    \<comment> \<open>split off the inner partial \<open>seg M j\<^sub>0 (j\<^sub>0+s)\<close> at the outermost boundary
       \<open>j\<^sub>0 + (Suc(Suc m))\<cdot>w\<close>; the prefix \<open>P(seg (M[n]) (j\<^sub>0+w) (j\<^sub>0+(Suc(Suc m))w-1))\<close>
       is the IH at \<open>m\<close>, \<open>s' = w-1\<close> (\<open>= replicate (Suc m) blk\<close>)\<close>
    have k1: "1 \<le> Suc (Suc m)" by simp
    have wmul: "1 * ?w < Suc (Suc m) * ?w" using w0 by simp
    have aBk: "?a < ?j0 + Suc (Suc m) * ?w" using wmul by simp
    have bmw: "le0 M ?j0 (?j0 + s)" using blockmono[OF sw] .
    have SSSle: "Suc (Suc (Suc m)) * ?w \<le> n * ?w"
    proof -
      have "Suc (Suc (Suc m)) \<le> n" using Smn by simp
      thus ?thesis by (rule mult_le_mono1)
    qed
    have Bsk: "?j0 + Suc (Suc m) * ?w + s < Lng ?MN"
    proof -
      have "Suc (Suc m) * ?w + ?w = Suc (Suc (Suc m)) * ?w" by simp
      hence "?j0 + Suc (Suc m) * ?w + s < ?j0 + n * ?w"
        using sw SSSle by linarith
      thus ?thesis using lenMN by simp
    qed
    have split: "P (seg ?MN ?a (?j0 + Suc (Suc m) * ?w + s))
               = P (seg ?MN ?a (?j0 + Suc (Suc m) * ?w - 1)) @ [seg M ?j0 (?j0 + s)]"
      by (rule oper_d0zero_seg_P_split[OF L notzero hp i1z aB k1 aBk sw bmw Bsk Smn])
    have sw': "?w - 1 < ?w" using w0 by simp
    \<comment> \<open>\<open>j\<^sub>0 + Suc m * w + (w-1) = j\<^sub>0 + Suc(Suc m)*w - 1\<close> aligns IH-endpoint with split-prefix\<close>
    have rend: "?j0 + Suc m * ?w + (?w - 1) = ?j0 + Suc (Suc m) * ?w - 1"
      using w0 by simp
    have blkidx: "?j0 + (?w - 1) = Lng M - 2" using w0 j0w1 by linarith
    have blkval: "seg M ?j0 (?j0 + (?w - 1)) = ?blk" using blkidx by simp
    have IH: "P (seg ?MN ?a (?j0 + Suc m * ?w + (?w - 1)))
            = replicate m ?blk @ [seg M ?j0 (?j0 + (?w - 1))]"
      by (rule Suc.IH[OF sw' Smn1])
    have prefix: "P (seg ?MN ?a (?j0 + Suc (Suc m) * ?w - 1)) = replicate (Suc m) ?blk"
    proof -
      have "P (seg ?MN ?a (?j0 + Suc (Suc m) * ?w - 1)) = replicate m ?blk @ [?blk]"
        using IH rend blkval by simp
      also have "\<dots> = replicate (Suc m) ?blk"
        by (simp add: replicate_append_same)
      finally show ?thesis .
    qed
    have "P (seg ?MN ?a (?j0 + Suc (Suc m) * ?w + s))
        = replicate (Suc m) ?blk @ [seg M ?j0 (?j0 + s)]"
      using split prefix by simp
    thus ?case by simp
    qed
  qed
  show ?thesis using gen[OF sw mn] .
qed

text \<open>Block-0-anchored fold (§6.8 d0zero case-B): a slice that STARTS at the
  block-0 boundary \<open>j\<^sub>0\<close> itself and ends inside block \<open>qb\<close> decomposes into \<open>qb\<close>
  verbatim copies of the full block \<open>blk = seg M j\<^sub>0 (Lng M-2)\<close> followed by one
  partial block \<open>seg M j\<^sub>0 (j\<^sub>0+r2)\<close>.  Unlike @{thm [source]
  oper_d0zero_seg_P_blk1fold} (anchored at \<open>j\<^sub>0+w\<close>) this includes the leftmost
  full block: peel it off by one @{thm [source] m_6_2_P_additive} cut at the
  block-1 boundary \<open>j\<^sub>0+w\<close> (\<open>P(seg j\<^sub>0 (j\<^sub>0+w-1)) = [blk]\<close>, a single multi
  component), then the high tail is @{thm [source] oper_d0zero_seg_P_blk1fold}
  with \<open>m = qb-1\<close>.  The \<open>qb=0\<close> base is the lone partial block.\<close>

lemma oper_d0zero_seg_P_blk0fold:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
    and blockmono: "\<And>s. s < Lng M - 1 - parent M 0 (Lng M - 1)
                      \<Longrightarrow> le0 M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + s)"
    and r2w: "r2 < Lng M - 1 - parent M 0 (Lng M - 1)"
    and qbn: "qb < n"
  shows "P (seg ((M::pairseq)[n])
              (parent M 0 (Lng M - 1))
              (parent M 0 (Lng M - 1) + qb * (Lng M - 1 - parent M 0 (Lng M - 1)) + r2))
       = replicate qb (seg M (parent M 0 (Lng M - 1)) (Lng M - 2))
       @ [seg M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + r2)]"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  let ?MN = "(M::pairseq)[n]"  let ?blk = "seg M ?j0 (Lng M - 2)"
  let ?partial = "seg M ?j0 (?j0 + r2)"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w - 1 = Lng M - 2" using w0 by simp
  have parR0: "nextrel0 M ?j0 (Lng M - 1)"
  proof -
    have hp0: "hasParent M 0 (Lng M - 1)" using hp i1z by simp
    have "nextR M 0 ?j0 (Lng M - 1)"
      using hp0 unfolding hasParent_def parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  have lenMN: "Lng ?MN = ?j0 + n * ?w"
  proof -
    have e: "?MN = take ?j0 M @ concat (replicate n (map ((!) M) [?j0..<Lng M - 1]))"
      by (rule oper_d0zero_expand[OF L notzero hp i1z])
    have t: "length (take ?j0 M) = ?j0" using j0lt by simp
    have b: "length (map ((!) M) [?j0..<Lng M - 1]) = ?w" by simp
    show ?thesis using e t b by (simp add: length_concat sum_list_replicate)
  qed
  show ?thesis
  proof (cases "qb = 0")
    case True
    \<comment> \<open>base: \<open>P(seg M[n] j\<^sub>0 (j\<^sub>0+r2)) = [partial]\<close>, a single non-multi block fragment\<close>
    have blockseg: "seg ?MN ?j0 (?j0 + r2) = ?partial"
    proof (rule nth_equalityI)
      show "length (seg ?MN ?j0 (?j0 + r2)) = length ?partial" by simp
      fix i assume "i < length (seg ?MN ?j0 (?j0 + r2))"
      hence ic: "i < Suc r2" by simp
      have q0: "(0::nat) < n" using qbn by simp
      have e1: "seg ?MN ?j0 (?j0 + r2) ! i = ?MN ! (?j0 + i)"
        using ic by (simp add: seg_nth_eq)
      have e2: "?MN ! (?j0 + i) = M ! (?j0 + i)"
        using oper_d0zero_nth[OF L notzero hp i1z j0lt q0, of i] ic r2w by simp
      have e3: "M ! (?j0 + i) = ?partial ! i" using ic by (simp add: seg_nth_eq)
      show "seg ?MN ?j0 (?j0 + r2) ! i = ?partial ! i" using e1 e2 e3 by simp
    qed
    have bm: "le0 M ?j0 (?j0 + r2)" using blockmono[OF r2w] .
    have single: "P ?partial = [?partial]"
    proof (rule poper_P_nonmulti)
      show "\<not> (multiT ?partial \<and> 1 < Lng ?partial)"
      proof (cases "1 < Lng ?partial")
        case True
        have Lseg: "Lng ?partial = Suc r2" by simp
        have segmono: "monoT ?partial"
        proof -
          have segL: "?j0 + r2 < Lng M" using r2w j0lt by linarith
          have eqv: "le0 ?partial 0 r2 = le0 M (?j0 + 0) (?j0 + r2)"
            using adm_le0_seg[OF segL, where a=0 and b=r2 and j0'="?j0"] by simp
          have "le0 ?partial 0 r2" using eqv bm by simp
          hence le00: "leR ?partial 0 0 (Lng ?partial - 1)" using Lseg by (simp add: leR_def)
          have nz: "\<not> zeroT ?partial" using True by (simp add: zeroT_def)
          show ?thesis using le00 nz by (simp add: monoT_def)
        qed
        thus ?thesis by (simp add: multiT_def)
      next
        case False thus ?thesis by simp
      qed
    qed
    show ?thesis using True blockseg single by simp
  next
    case False
    hence qb1: "1 \<le> qb" by simp
    \<comment> \<open>peel the leftmost full block by a \<open>P\<close>-additive cut at the block-1 boundary
       \<open>j\<^sub>0+w\<close>; the tail is @{thm [source] oper_d0zero_seg_P_blk1fold} with \<open>m=qb-1\<close>\<close>
    let ?End = "?j0 + qb * ?w + r2"
    let ?Q = "seg ?MN ?j0 ?End"
    have endlt: "?End < Lng ?MN"
    proof -
      have "qb * ?w + r2 < n * ?w"
      proof -
        have "qb * ?w + r2 < qb * ?w + ?w" using r2w by simp
        also have "\<dots> = Suc qb * ?w" by simp
        also have "\<dots> \<le> n * ?w" using mult_le_mono1[OF Suc_leI[OF qbn], of ?w] .
        finally show ?thesis .
      qed
      thus ?thesis using lenMN by simp
    qed
    have aleEnd: "?j0 \<le> ?End" by simp
    have lenQ: "Lng ?Q = Suc ?End - ?j0" by (rule Lng_seg)
    let ?c = "?w"   \<comment> \<open>cut index in \<open>Q\<close>: global \<open>j\<^sub>0+w\<close> is local \<open>w\<close>\<close>
    have c0: "0 < ?c" using w0 .
    have cle: "?c \<le> Lng ?Q - 1"
    proof -
      have wle: "?w \<le> qb * ?w" using mult_le_mono1[OF qb1, of ?w] by simp
      have "?j0 + ?w \<le> ?j0 + qb * ?w + r2" using wle by linarith
      thus ?thesis using lenQ aleEnd by linarith
    qed
    have QT: "?Q \<in> T_PS"
    proof -
      have "0 < Lng ?Q" using lenQ aleEnd by linarith
      hence "?Q \<noteq> []" using length_greater_0_conv by blast
      thus ?thesis by (simp add: T_PS_def)
    qed
    \<comment> \<open>left-minimality at the cut \<open>c=w\<close> (row-0 there \<open>= M\<^bsub>0,j\<^sub>0\<^esub>\<close>, the block min)\<close>
    have nseg: "\<And>i. i < Suc ?End - ?j0 \<Longrightarrow> ?Q ! i = ?MN ! (?j0 + i)"
      by (rule seg_nth_eq)
    have cidx: "?c < Suc ?End - ?j0" using cle lenQ by linarith
    have entryQc: "entry ?Q 0 ?c = entry M 0 ?j0"
    proof -
      have n2: "1 < n" using qbn qb1 by linarith
      have x0: "?j0 \<le> ?j0 + ?w" by simp
      have wnw: "?w < n * ?w" using n2 w0 by (simp add: mult_strict_right_mono)
      have xlt: "?j0 + ?w < ?j0 + n * ?w" using wnw by linarith
      have "?Q ! ?c = ?MN ! (?j0 + ?w)" using nseg[OF cidx] .
      hence "entry ?Q 0 ?c = entry ?MN 0 (?j0 + ?w)" by (simp add: entry_def)
      moreover have "entry ?MN 0 (?j0 + ?w)
                   = entry M 0 (?j0 + ((?j0 + ?w) - ?j0) mod ?w)"
        using oper_d0zero_entry0[OF L notzero hp i1z j0lt x0 xlt] .
      moreover have "((?j0 + ?w) - ?j0) mod ?w = 0" by simp
      ultimately show ?thesis by simp
    qed
    have lmin: "\<And>j. j < ?c \<Longrightarrow> entry ?Q 0 ?c \<le> entry ?Q 0 j"
    proof -
      fix j assume jc: "j < ?c"
      have jidx: "j < Suc ?End - ?j0" using jc cidx by linarith
      have "?Q ! j = ?MN ! (?j0 + j)" using nseg[OF jidx] .
      hence eQj: "entry ?Q 0 j = entry ?MN 0 (?j0 + j)" by (simp add: entry_def)
      have ge: "?j0 \<le> ?j0 + j" by simp
      have lt: "?j0 + j < ?j0 + n * ?w" using jc w0 qbn by (cases n) auto
      have "entry M 0 ?j0 \<le> entry ?MN 0 (?j0 + j)"
        using oper_d0zero_entry0_min[OF L notzero hp i1z j0lt ge lt] .
      thus "entry ?Q 0 ?c \<le> entry ?Q 0 j" using eQj entryQc by simp
    qed
    have padd: "P ?Q = P (seg ?Q 0 (?c - 1)) @ P (seg ?Q ?c (Lng ?Q - 1))"
      by (rule m_6_2_P_additive[OF QT c0 cle lmin])
    \<comment> \<open>left part \<open>= seg M[n] j\<^sub>0 (j\<^sub>0+w-1)\<close>, whose \<open>P\<close> is the single full block \<open>[blk]\<close>;
       the @{thm seg_of_seg} side goal \<open>c-1 \<le> End-j\<^sub>0\<close> via an explicit \<open>db\<close> witness
       (the old \<open>(use cle lenQ in linarith)\<close> blew up >2400s on the compound terms)\<close>
    have leftseg: "seg ?Q 0 (?c - 1) = seg ?MN ?j0 (?j0 + ?w - 1)"
    proof -
      have db: "?c - 1 \<le> ?End - ?j0"
      proof -
        have e: "?End - ?j0 = qb * ?w + r2" by simp
        have "?w \<le> qb * ?w" using mult_le_mono1[OF qb1, of ?w] by simp
        thus ?thesis using e by linarith
      qed
      have idxL: "?j0 + (?c - 1) = ?j0 + ?w - 1" using w0 by linarith
      have "seg ?Q 0 (?c - 1) = seg ?MN (?j0 + 0) (?j0 + (?c - 1))"
        by (rule seg_of_seg[OF aleEnd db])
      thus ?thesis using idxL by simp
    qed
    have blkseg: "seg ?MN ?j0 (?j0 + ?w - 1) = ?blk"
    proof -
      have "seg ?MN ?j0 (Lng M - 2) = ?blk"
      proof (rule nth_equalityI)
        show "length (seg ?MN ?j0 (Lng M - 2)) = length ?blk" by simp
        fix i assume "i < length (seg ?MN ?j0 (Lng M - 2))"
        hence ic: "i < Suc (Lng M - 2) - ?j0" by simp
        hence iw: "?j0 + i < Lng M - 1" using j0lt L j0w1 w0 by linarith
        have q0: "(0::nat) < n" using qbn by simp
        have e1: "seg ?MN ?j0 (Lng M - 2) ! i = ?MN ! (?j0 + i)"
          using ic by (simp add: seg_nth_eq)
        have e2: "?MN ! (?j0 + i) = M ! (?j0 + i)"
          using oper_d0zero_nth[OF L notzero hp i1z j0lt q0, of i] iw by simp
        have e3: "M ! (?j0 + i) = ?blk ! i" using ic by (simp add: seg_nth_eq)
        show "seg ?MN ?j0 (Lng M - 2) ! i = ?blk ! i" using e1 e2 e3 by simp
      qed
      thus ?thesis using j0w1 by simp
    qed
    have leftP: "P (seg ?Q 0 (?c - 1)) = [?blk]"
    proof -
      have "P ?blk = [?blk]"
      proof (rule poper_P_nonmulti)
        show "\<not> (multiT ?blk \<and> 1 < Lng ?blk)"
        proof (cases "1 < Lng ?blk")
          case True
          have Lblk: "Lng ?blk = Suc (Lng M - 2) - ?j0" by simp
          have segmono: "monoT ?blk"
          proof -
            have wm1: "?w - 1 < ?w" using w0 by simp
            have bm: "le0 M ?j0 (?j0 + (?w - 1))" using blockmono[OF wm1] .
            \<comment> \<open>both \<open>linarith\<close> and \<open>presburger\<close> loop in preprocessing on the \<open>?w\<close>-expanded
               double-\<open>parent\<close> goal once \<open>j0lt\<close> is supplied; chain through the cheap
               \<open>w0\<close>-only assoc + \<open>j0w1\<close> (\<open>by simp\<close> trans) instead — keeps \<open>j0lt\<close> out of arith\<close>
            have assoc: "?j0 + (?w - 1) = ?j0 + ?w - 1" using w0 by linarith
            have idxe: "?j0 + (?w - 1) = Lng M - 2" using assoc j0w1 by simp
            have lt2: "Lng M - 2 < Lng M" using L by linarith
            have segL: "?j0 + (?w - 1) < Lng M" using idxe lt2 by simp
            have j0le2: "?j0 \<le> Lng M - 2"
            proof -
              have "?j0 \<le> ?j0 + ?w - 1" using w0 by linarith
              thus ?thesis using j0w1 by simp
            qed
            have ej: "?j0 + (Lng M - 2 - ?j0) = Lng M - 2" using j0le2 by simp
            have eqv: "le0 ?blk 0 (Lng M - 2 - ?j0) = le0 M (?j0 + 0) (?j0 + (Lng M - 2 - ?j0))"
              using adm_le0_seg[OF segL[unfolded idxe], where a=0 and b="Lng M - 2 - ?j0" and j0'="?j0"] ej
              by simp
            have bm2: "le0 M ?j0 (?j0 + (Lng M - 2 - ?j0))" using bm idxe ej by simp
            have "le0 ?blk 0 (Lng M - 2 - ?j0)" using eqv bm2 by simp
            hence le00: "leR ?blk 0 0 (Lng ?blk - 1)" using Lblk by (simp add: leR_def)
            \<comment> \<open>\<open>Lng ?blk = Suc(Lng M-2)-?j0\<close> normalizes messily; extract only the
               \<open>Lng = 1\<close> conjunct and contradict \<open>True\<close>, avoiding the \<open>entry\<close> blowup\<close>
            have nz: "\<not> zeroT ?blk"
            proof
              assume "zeroT ?blk"
              hence "Lng ?blk = 1" by (simp add: zeroT_def)
              thus False using True by simp
            qed
            show ?thesis using le00 nz by (simp add: monoT_def)
          qed
          thus ?thesis by (simp add: multiT_def)
        next
          case False thus ?thesis by simp
        qed
      qed
      thus ?thesis using leftseg blkseg by simp
    qed
    \<comment> \<open>right part \<open>= seg M[n] (j\<^sub>0+w) End\<close>; \<open>blk1fold\<close> at \<open>m = qb-1\<close>, \<open>s = r2\<close>\<close>
    have rightseg: "seg ?Q ?c (Lng ?Q - 1) = seg ?MN (?j0 + ?w) ?End"
    proof -
      have e: "?j0 + (Lng ?Q - 1) = ?End" using lenQ aleEnd by linarith
      have "seg ?Q ?c (Lng ?Q - 1) = seg ?MN (?j0 + ?w) (?j0 + (Lng ?Q - 1))"
        by (rule seg_of_seg[OF aleEnd]) simp
      \<comment> \<open>rewrite the endpoint via @{thm arg_cong}, not \<open>simp\<close>: the \<open>Lng_seg\<close> simproc
         mangles \<open>?j0 + (Lng Q - 1)\<close> into an assoc-shifted \<open>qb*w+r2\<close> form simp won't re-close\<close>
      also have "\<dots> = seg ?MN (?j0 + ?w) ?End"
        using arg_cong[OF e, of "seg ?MN (?j0 + ?w)"] .
      finally show ?thesis .
    qed
    have qbS: "qb = Suc (qb - 1)" using qb1 by simp
    have endeq: "?End = ?j0 + Suc (qb - 1) * ?w + r2" using qbS by simp
    have mn': "Suc (qb - 1) < n" using qbn qbS by simp
    have rightP: "P (seg ?MN (?j0 + ?w) ?End)
                = replicate (qb - 1) ?blk @ [?partial]"
      using oper_d0zero_seg_P_blk1fold[OF L notzero hp i1z j0lt blockmono r2w mn']
            endeq by simp
    have "P ?Q = [?blk] @ (replicate (qb - 1) ?blk @ [?partial])"
      using padd leftP rightseg rightP by simp
    also have "\<dots> = (?blk # replicate (qb - 1) ?blk) @ [?partial]" by simp
    also have "?blk # replicate (qb - 1) ?blk = replicate (Suc (qb - 1)) ?blk" by simp
    also have "Suc (qb - 1) = qb" using qb1 by simp
    finally show ?thesis .
  qed
qed

text \<open>§6.8 d1pos GENERAL brick (regime-INDEPENDENT): a slice whose endpoints are
  row-0 reachable (\<open>le0 M a b\<close>, \<open>a < b\<close>) is \<open>monoT\<close>.  This is the \<open>a\<close>-free version of
  @{thm [source] oper_d1pos_seg_mono} (whose block-start/oper hypotheses are not
  actually used in the \<open>monoT\<close> derivation): \<open>\<not> zeroT\<close> from \<open>1 < Lng\<close> (as \<open>a < b\<close>),
  the \<open>leR\<close> body transfers via @{thm [source] adm_le0_seg}.\<close>

lemma monoT_seg_of_le0:
  assumes blt: "b < Lng M" and ab: "a < b" and leab: "le0 M a b"
  shows "monoT (seg M a b)"
proof -
  let ?S = "seg M a b"
  have LS: "Lng ?S = Suc b - a" by (simp only: Lng_seg)
  have LSgt1: "1 < Lng ?S" using LS ab by simp
  have nzS: "\<not> zeroT ?S"
  proof
    assume "zeroT ?S"
    hence "Lng ?S = 1" by (simp add: zeroT_def)
    thus False using LSgt1 by simp
  qed
  have LSm1: "Lng ?S - 1 = b - a" using LS ab by simp
  have aleb: "a \<le> b" using ab by simp
  have b0le: "b - a \<le> b - a" by (rule order.refl)
  have z0le: "(0::nat) \<le> b - a" by simp
  have tr: "le0 ?S 0 (b - a) = le0 M (a + 0) (a + (b - a))"
    by (rule adm_le0_seg[where M="M" and j0'=a and j1'=b and a=0 and b="b - a",
          OF blt z0le b0le aleb])
  have ab0: "a + 0 = a" by simp
  have abb: "a + (b - a) = b" using aleb by simp
  have le0S: "le0 ?S 0 (b - a)" using tr ab0 abb leab by simp
  have leRS: "leR ?S 0 0 (Lng ?S - 1)" using le0S LSm1 by (simp add: leR_def)
  show ?thesis using nzS leRS by (simp add: monoT_def)
qed

text \<open>§6.8 d1pos DIRECT route — the clean reduction of \<open>descending (Br M')\<close> for a
  monoT slice \<open>M'\<close> to a SINGLE row-0 reachability fact.  Empirically (python/
  d1pos_fold_Br_decomp.py + d1pos_fold_lastblock.py, rank-stratified standard
  generator, KMAX=4): for the i1=1 (d0pos) fold the branch region
  \<open>Yp = seg M' (TrMax M'+1)(Lng M'-1)\<close> is ALWAYS a SINGLE \<open>P\<close>-component
  (\<open>P Yp = [Yp]\<close>, 5548/5548) — the delta-shifted block boundaries are NOT row-0
  left-minima so \<open>P\<close> does not split.  Equivalently \<open>Yp\<close> is non-multi, and (when
  \<open>1 < Lng Yp\<close>) \<open>monoT\<close>, which is EXACTLY \<open>le0 M' (TrMax M'+1)(Lng M'-1)\<close>
  (the empirical iff is 257/257).  Hence \<open>Br M' = [Yp]\<close> and \<open>descending\<close> is the
  trivial singleton case.  This lemma packages that reduction: the row-1
  tie-break of \<open>Br M'\<close> is VACUOUS (one component), replacing the
  \<open>slice_P_tiebreak\<close> stub on the d1pos branch.  The single
  residual hypothesis \<open>brle\<close> (\<open>le0 (seg M j0' j1') (TrMax (seg M j0' j1')+1)
  (Lng (seg M j0' j1')-1)\<close>) is the genuine d1pos content (article 1542-1620:
  the branch trunk-end row-0-reaches the slice end).\<close>

text \<open>§6.8 d1pos ¬brle structural split (regime-independent).  For a branch region
  \<open>Yp \<in> T_PS\<close> with a row-0 LEFT-MINIMUM anchor \<open>c\<close> (\<open>0 < c \<le> Lng Yp - 1\<close>) that is
  also a single-component cut (\<open>le0 Yp c (Lng Yp - 1)\<close>, so the tail
  \<open>seg Yp c (Lng Yp - 1)\<close> is one \<open>monoT\<close> component), \<open>P Yp\<close> splits as
  \<open>P (seg Yp 0 (c-1)) @ [seg Yp c (Lng Yp - 1)]\<close>.  This is the multi-component
  fold of the d1pos branch (the \<open>\<not>brle\<close> case): \<open>c\<close> is the last \<open>FirstNodes\<close>
  position, \<open>seg Yp 0 (c-1)\<close> is the prefix (a \<open>q\<cdot>\<delta>\<close>-shifted copy of the \<open>N\<close>-side
  branch), and \<open>seg Yp c (Lng Yp - 1)\<close> the last (single) component.  Empirically
  verified: \<open>python/d1pos_notbrle_anchor.py\<close> (split 12/12, tail single monoT 12/12)
  and \<open>python/d1pos_notbrle_goal.py\<close> (204/204, 0 failures, rank-stratified std gen).
  This packages the @{thm [source] m_6_2_P_additive} split + the tail's
  @{thm [source] monoT_seg_of_le0} property as a single reusable brick.\<close>

lemma oper_d1pos_notbrle_P_split:
  assumes YpT: "Yp \<in> T_PS"
    and c0: "0 < c" and cle: "c \<le> Lng Yp - 1"
    and lmin: "\<And>j. j < c \<Longrightarrow> entry Yp 0 c \<le> entry Yp 0 j"
    and tailnm: "\<not> multiT (seg Yp c (Lng Yp - 1))"
  shows "P Yp = P (seg Yp 0 (c - 1)) @ [seg Yp c (Lng Yp - 1)]"
proof -
  \<comment> \<open>the additive split at the row-0 left-min cut \<open>c\<close>\<close>
  have split: "P Yp = P (seg Yp 0 (c - 1)) @ P (seg Yp c (Lng Yp - 1))"
    by (rule m_6_2_P_additive[OF YpT c0 cle lmin])
  \<comment> \<open>the tail is a single (non-multi) component, so \<open>P tail = [tail]\<close>.  NB the tail
     is NOT always \<open>monoT\<close> — when \<open>c = Lng Yp - 1\<close> it is the single last node, which
     may be \<open>zeroT\<close> (row-1 0, 21/75 degenerate cases empirically); but a singleton
     list is still \<open>descending\<close>, and either way \<open>\<not> multiT tail\<close> gives \<open>P tail = [tail]\<close>.\<close>
  have Ptail: "P (seg Yp c (Lng Yp - 1)) = [seg Yp c (Lng Yp - 1)]"
  proof -
    have "\<not> (multiT (seg Yp c (Lng Yp - 1)) \<and> 1 < Lng (seg Yp c (Lng Yp - 1)))"
      using tailnm by simp
    thus ?thesis by (rule poper_P_nonmulti)
  qed
  show "P Yp = P (seg Yp 0 (c - 1)) @ [seg Yp c (Lng Yp - 1)]"
    using split Ptail by simp
qed

end
