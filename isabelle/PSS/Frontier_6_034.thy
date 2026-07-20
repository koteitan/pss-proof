theory Frontier_6_034
  imports Support_6_016
begin

text \<open>§6.8 d1pos TrEq keystone, CAPPED-GENERAL form.  Identical to
  @{thm [source] TrMax_seg_oper_d1pos_eq} but the in-block span hypothesis is
  weakened from the verbatim equality \<open>j\<^sub>1\<^sup>red = j\<^sub>0\<^sup>red + (j'\<^sub>1 - j'\<^sub>0)\<close> (UNCAPPED
  only) to the inequality \<open>j\<^sub>1\<^sup>red \<le> j\<^sub>0\<^sup>red + (j'\<^sub>1 - j'\<^sub>0)\<close>, which holds in BOTH the
  uncapped (\<open>=\<close>) and the CAPPED (\<open>j\<^sub>1\<^sup>red = Lng N-1 <\<close>) sub-cases (the across-block
  sub-case).  \<open>span\<close> was used ONLY to establish \<open>c < Lng M'\<close> (\<open>cM\<close>); under the
  weaker \<open>\<le>\<close> we still have \<open>c = j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red < j\<^sub>1\<^sup>red - j\<^sub>0\<^sup>red \<le> j'\<^sub>1 - j'\<^sub>0 < Lng M'\<close>.
  The pointwise agreement on \<open>[0,c]\<close> is unaffected (it never used \<open>span\<close>: it bounds
  the in-block offset by \<open>j\<^sub>1\<^sup>red\<close>, @{thm [source] oper_d1pos_nth}).  DEEP-VERIFIED
  (KMAX=6 len=11, formula-G, EXACT in-block hyps incl.\ \<open>\<not>brle\<close>,
  \<open>python/d1pos_treq_tnc_stop.py\<close>): TrEq 207/207, agreement 207/207, \<open>tnc\<close> 207/207,
  \<open>stop\<close> 207/207, 130 of them the CAPPED sub-case.\<close>

lemma TrMax_seg_oper_d1pos_eq_span:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
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
    \<comment> \<open>CAPPED-general span: \<open>\<le>\<close> instead of \<open>=\<close>\<close>
    and j1redspan: "j1red \<le> j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red))
                  (TrMax (seg N j0red j1red) + 1)"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1')
       = TrMax (seg N j0red j1red)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?j0 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?j0"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?j0"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?Npp = "(IncrFirst ^^ shamt) ?Np"
  let ?c = "j1red - 1 - j0red"
  have j0redge: "?j0 \<le> j0red" using s0eq by simp
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NppT: "?Npp \<in> T_PS"
  proof -
    have "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
    thus ?thesis by (induction shamt) (simp_all add: T_PS_def IncrFirst_def)
  qed
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have LNpp: "Lng ?Npp = Suc j1red - j0red" by simp
  have trShift: "TrMax ?Npp = TrMax ?Np" by (rule TrMax_funpow_IncrFirst)
  have cN: "?c < Lng ?Npp" using LNpp j0j1red by linarith
  \<comment> \<open>\<open>c < Lng M'\<close> from the WEAK span: \<open>c < j\<^sub>1\<^sup>red - j\<^sub>0\<^sup>red \<le> j'\<^sub>1 - j'\<^sub>0 < Lng M'\<close>\<close>
  have cM: "?c < Lng ?Mp"
  proof -
    have "?c < j1red - j0red" using j0j1red by linarith
    also have "j1red - j0red \<le> j1' - j0'" using j1redspan by linarith
    also have "j1' - j0' < Suc j1' - j0'" using j0j1' by linarith
    finally show ?thesis using LMp by simp
  qed
  have tncShift: "TrMax ?Npp \<le> ?c" using tnc trShift by simp
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
  have stopShift: "\<not> nextR ?Mp 1 (TrMax ?Npp) (TrMax ?Npp + 1)"
    using stop trShift by simp
  have "TrMax ?Mp = TrMax ?Npp"
    by (rule TrMax_eq_of_prefix_agree[OF MpT NppT agree cM cN tncShift stopShift])
  thus ?thesis using trShift by simp
qed

text \<open>§6.8 d1pos TrEq keystone, \<open>\<not>brle\<close>-UNCONDITIONAL UNCAPPED form.  In the
  uncapped sub-case the min-cap is inactive: \<open>j\<^sub>1\<^sup>red = j\<^sub>0\<^sup>red + (j'\<^sub>1 - j'\<^sub>0)\<close>, so
  \<open>c = j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red = Lng M' - 2\<close> (\<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close>).  Here the two
  trunk-confinement obligations \<open>tnc\<close>/\<open>stop\<close> of the conditional keystone are
  DISCHARGED FROM \<open>\<not>brle\<close> directly, with NO reference-side intrinsic property:

  \<^item> \<open>\<not>brle\<close> gives \<open>Mlt : TrMax M' < Lng M' - 1\<close> and
    \<open>notle : \<not> le0 M' (TrMax M' + 1) (Lng M' - 1)\<close>.
  \<^item> Since \<open>c = Lng M' - 2\<close>, \<open>Mlt\<close> already gives \<open>TrMax M' \<le> c\<close>; and if equality
    held (\<open>TrMax M' = c = Lng M' - 2\<close>) then \<open>TrMax M' + 1 = Lng M' - 1\<close> and
    \<open>le0 M' (Lng M'-1) (Lng M'-1)\<close> holds by @{thm [source] le0_refl}, contradicting
    \<open>notle\<close>.  Hence \<open>TrMax M' + 1 \<le> c\<close> (the strict-2 confinement, deep-verified
    \<open>tN+1\<le>c\<close> 2360/2360 KMAX=7, \<open>python/d1pos_tn_strict.py\<close>).
  \<^item> The \<open>M'\<close>-side boundary stop is then @{thm [source] TrMax_stop} of \<open>M'\<close> (from
    \<open>Mlt\<close>); the trunks coincide by the SYMMETRIC prefix transfer
    @{thm [source] TrMax_eq_of_prefix_agree_sym} (confinement on the \<open>M'\<close> side),
    with the SAME pointwise agreement on \<open>[0,c]\<close> as the conditional keystone.

  This breaks the apparent circularity (the reference \<open>N\<^sub>p\<close> has a NONZERO last
  row-1, so no intrinsic confinement is available): the confinement is carried
  by \<open>\<not>brle\<close> on the \<open>M'\<close> side and transferred to the trunk equality, never
  through the unknown \<open>TrMax N\<^sub>p\<close>.  DEEP-VERIFIED (KMAX=6 len=11, formula-G,
  EXACT in-block hyps incl.\ \<open>\<not>brle\<close>, \<open>python/d1pos_treq_tnc_stop.py\<close>): on the 77
  uncapped \<open>\<not>brle\<close>-residual cases TrEq 77/77, \<open>tN+1\<le>c\<close> 77/77, agreement 77/77.\<close>

lemma TrMax_seg_oper_d1pos_eq_notbrle_uncapped:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
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
    \<comment> \<open>UNCAPPED span (the min-cap inactive): verbatim equality\<close>
    and span: "j1red = j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    \<comment> \<open>\<open>\<not>brle\<close> as its two conjuncts, on \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close>\<close>
    and Mlt: "TrMax (seg ((N::pairseq)[n]) j0' j1')
                < Lng (seg ((N::pairseq)[n]) j0' j1') - 1"
    and notle: "\<not> le0 (seg ((N::pairseq)[n]) j0' j1')
                  (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
                  (Lng (seg ((N::pairseq)[n]) j0' j1') - 1)"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1')
       = TrMax (seg N j0red j1red)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?j0 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?j0"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?j0"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?Npp = "(IncrFirst ^^ shamt) ?Np"
  let ?c = "j1red - 1 - j0red"
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NppT: "?Npp \<in> T_PS"
  proof -
    have "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
    thus ?thesis by (induction shamt) (simp_all add: T_PS_def IncrFirst_def)
  qed
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNpp: "Lng ?Npp = Suc j1red - j0red" by simp
  have trShift: "TrMax ?Npp = TrMax ?Np" by (rule TrMax_funpow_IncrFirst)
  \<comment> \<open>UNCAPPED: \<open>c = Lng M' - 2\<close>\<close>
  have spanD: "j1' - j0' = j1red - j0red" using span j0j1red by linarith
  have cLMp: "?c = Lng ?Mp - 2" using spanD j0j1red j0j1' LMp by linarith
  have cM: "?c < Lng ?Mp" using cLMp LMp j0j1' by linarith
  have cN: "?c < Lng ?Npp" using LNpp j0j1red by linarith
  \<comment> \<open>strict-2 confinement on \<open>M'\<close> from \<open>\<not>brle\<close>: \<open>TrMax M' + 1 \<le> c\<close>\<close>
  have LMp2: "2 \<le> Lng ?Mp" using LMp j0j1' by linarith
  have tncM1: "TrMax ?Mp + 1 \<le> ?c"
  proof -
    have le_c: "TrMax ?Mp \<le> ?c" using Mlt cLMp by linarith
    have "TrMax ?Mp \<noteq> ?c"
    proof
      assume eq: "TrMax ?Mp = ?c"
      have endlt: "Lng ?Mp - 1 < Lng ?Mp" using LMp2 by linarith
      have "TrMax ?Mp + 1 = Lng ?Mp - 1" using eq cLMp LMp2 by linarith
      hence "le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1)"
        using le0_refl[OF endlt] by simp
      thus False using notle by simp
    qed
    with le_c show ?thesis by linarith
  qed
  have tncM: "TrMax ?Mp \<le> ?c" using tncM1 by linarith
  \<comment> \<open>\<open>M'\<close>-side boundary stop from \<open>Mlt\<close> (maximality)\<close>
  have stopM: "\<not> nextR ?Mp 1 (TrMax ?Mp) (TrMax ?Mp + 1)"
    by (rule TrMax_stop[OF MpT Mlt])
  \<comment> \<open>pointwise agreement on \<open>[0, c]\<close> (identical to the conditional keystone)\<close>
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
  \<comment> \<open>SYMMETRIC transfer: \<open>M'\<close>-side strict-2 confinement + stop pin \<open>TrMax M' = TrMax N\<^sub>p\<^sub>p\<close>\<close>
  have "TrMax ?Mp = TrMax ?Npp"
    by (rule TrMax_eq_of_prefix_agree_sym[OF MpT NppT agree cM cN tncM1 stopM])
  thus ?thesis using trShift by simp
qed

end
