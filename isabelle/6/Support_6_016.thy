theory Support_6_016
  imports Frontier_6_033
begin

text \<open>§6.8 d0pos (\<open>i\<^sub>1=1\<close>) TrEq KEYSTONE — the d1pos analogue (keystone) of
  @{thm [source] TrMax_seg_oper_d0zero_eq}.  In the residual d0pos \<open>\<not>brle\<close> closure
  the slice \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close> sits in block \<open>q\<close> of the d1pos fold:
  \<open>j'\<^sub>0 = j\<^sub>-\<^sub>2 + q\<cdot>w + s\<^sub>0\<close> with \<open>j\<^sub>-\<^sub>2 = parent N 1 (Lng N-1)\<close>, \<open>w = Lng N-1-j\<^sub>-\<^sub>2\<close>,
  \<open>s\<^sub>0 = j\<^sub>0\<^sup>red - j\<^sub>-\<^sub>2 < w\<close>.  The reference is the \<open>(IncrFirst^^shamt)\<close>-shift
  (\<open>shamt = q\<cdot>\<delta>\<close>, \<open>\<delta> = N\<^bsub>0,Lng N-1\<^esub> - N\<^bsub>0,j\<^sub>-\<^sub>2\<^esub>\<close>) of the base slice
  \<open>N\<^sub>p = seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red\<close> (\<open>j\<^sub>1\<^sup>red\<close> the MIN-CAP \<open>min (j\<^sub>0\<^sup>red+(j'\<^sub>1-j'\<^sub>0)) (Lng N-1)\<close>).
  \<open>TrMax\<close> being \<open>IncrFirst\<close>-invariant (@{thm [source] TrMax_funpow_IncrFirst}), and
  \<open>M'\<close> agreeing with the shift exactly on the in-block prefix \<open>[0, c]\<close>
  (\<open>c = j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red\<close>, period of \<open>N[n]\<close> shifted-intact below the block end, via
  @{thm [source] oper_d1pos_nth}), @{thm [source] TrMax_eq_of_prefix_agree} reduces
  \<open>TrMax M' = TrMax N\<^sub>p\<close> to the trunk-confinement \<open>TrMax N\<^sub>p \<le> c\<close> (\<open>tnc\<close>) and the
  boundary stop \<open>\<not> nextR M' 1 (TrMax N\<^sub>p) (TrMax N\<^sub>p + 1)\<close> (\<open>stop\<close>), here taken as
  hypotheses (exactly the d0zero stop-as-hypothesis form of
  @{thm [source] TrMax_seg_oper_d0zero_eq}).  DEEP-VERIFIED with the EXACT in-block
  hyps incl. \<open>\<not>brle\<close> (\<open>python/d1pos_treq_residuals.py\<close>, is_standard rank-stratified
  std gen, len\<le>11, KMAX\<ge>6, formula-G): TrEq 22431/22431, prefix-agreement
  22431/22431, \<open>tnc\<close> 22431/22431, \<open>stop\<close> 22431/22431 (15246 of them the hard
  across-block CAPPED sub-case).  NB the bare keystone WITHOUT \<open>\<not>brle\<close> is FALSE
  (72917/74750: the \<open>brle\<close>-true degenerate-tail slices, e.g.
  \<open>seg (N[2]) 8 9 = (5,0)(6,0)\<close> vs \<open>seg N 8 9 = (5,0)(6,1)\<close>, \<open>w=1\<close>) — the \<open>tnc\<close>
  hypothesis is what carries the \<open>\<not>brle\<close> content into the proof.\<close>

lemma TrMax_seg_oper_d1pos_eq:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    \<comment> \<open>\<open>j'\<^sub>0\<close> sits at block \<open>q\<close>, offset \<open>s\<^sub>0\<close>; \<open>j\<^sub>0\<^sup>red = j\<^sub>-\<^sub>2 + s\<^sub>0\<close>; \<open>shamt = q\<cdot>\<delta>\<close>\<close>
    and qn: "q < n"
    and s0w: "j0red < Lng N - 1"
    and s0eq: "j0red = parent N 1 (Lng N - 1) + s0"
    and s0lt: "s0 < Lng N - 1 - parent N 1 (Lng N - 1)"
    and j0'eq: "j0' = parent N 1 (Lng N - 1)
                  + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0"
    and shamt: "shamt = q * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    \<comment> \<open>the MIN-CAP endpoint and the in-block span hypotheses\<close>
    and j1redle: "j1red \<le> Lng N - 1"
    and j0j1red: "j0red < j1red"
    and span: "j1red = j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    \<comment> \<open>trunk-confinement (\<open>tnc\<close>) and boundary stop (the \<open>\<not>brle\<close> content)\<close>
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
  \<comment> \<open>basic index facts\<close>
  have j0redge: "?j0 \<le> j0red" using s0eq by simp
  have j0redltw: "j0red < j1red" by (rule j0j1red)
  have j1redgt: "j0red < j1red" by (rule j0j1red)
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  \<comment> \<open>\<open>j'\<^sub>1 - j'\<^sub>0 = j\<^sub>1\<^sup>red - j\<^sub>0\<^sup>red\<close> (span)\<close>
  have spanD: "j1' - j0' = j1red - j0red" using span j0j1red by linarith
  \<comment> \<open>both slices non-empty, hence in \<open>T_PS\<close>\<close>
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NppT: "?Npp \<in> T_PS"
  proof -
    have "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
    thus ?thesis by (induction shamt) (simp_all add: T_PS_def IncrFirst_def)
  qed
  \<comment> \<open>lengths\<close>
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have LNpp: "Lng ?Npp = Suc j1red - j0red" by simp
  \<comment> \<open>\<open>TrMax\<close> of the shift is \<open>TrMax\<close> of the base\<close>
  have trShift: "TrMax ?Npp = TrMax ?Np" by (rule TrMax_funpow_IncrFirst)
  \<comment> \<open>\<open>c\<close> is within both slices\<close>
  have cN: "?c < Lng ?Npp" using LNpp j0j1red by linarith
  have cM: "?c < Lng ?Mp"
  proof -
    have "?c = j1' - 1 - j0'" using spanD j0j1red j0j1' by linarith
    thus ?thesis using LMp j0j1' by linarith
  qed
  \<comment> \<open>trunk-confinement on the shifted side\<close>
  have tncShift: "TrMax ?Npp \<le> ?c" using tnc trShift by simp
  \<comment> \<open>pointwise agreement on \<open>[0, c]\<close>: in-block period of \<open>N[n]\<close> shifted by \<open>shamt\<close>\<close>
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Npp ! s"
  proof -
    fix s assume sc: "s \<le> ?c"
    \<comment> \<open>index bounds\<close>
    have sM: "s < Suc j1' - j0'" using sc cM LMp by linarith
    have sNp: "s < Suc j1red - j0red" using sc cN LNpp by linarith
    \<comment> \<open>\<open>s\<^sub>0 + s < w\<close>: the slice position \<open>s\<close> stays inside block \<open>q\<close>\<close>
    have s0sw: "s0 + s < ?w"
    proof -
      have "j0red + s \<le> j1red - 1" using sc j0j1red by linarith
      hence "?j0 + s0 + s \<le> ?j1N - 1" using s0eq j1redle j0j1red by linarith
      thus ?thesis using j0lt by linarith
    qed
    \<comment> \<open>LHS: oper block-read at block \<open>q\<close>, offset \<open>s\<^sub>0+s\<close>\<close>
    have lhs_idx: "j0' + s = ?j0 + q * ?w + (s0 + s)" using j0'eq by (simp add: add.assoc)
    have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
    also have "\<dots> = ?M ! (?j0 + q * ?w + (s0 + s))" by (rule arg_cong[OF lhs_idx, of "(!) ?M"])
    also have "\<dots> = (entry N 0 (?j0 + (s0 + s)) + q * ?delta, entry N 1 (?j0 + (s0 + s)))"
      by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt qn s0sw])
    finally have LHS: "?Mp ! s = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))"
      using shamt by simp
    \<comment> \<open>RHS: base slice node \<open>j\<^sub>0\<^sup>red + s = j\<^sub>0 + s\<^sub>0 + s\<close> shifted in row 0 by \<open>shamt\<close>\<close>
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
  \<comment> \<open>boundary stop on the shifted side (\<open>TrMax ?Npp = TrMax ?Np\<close>)\<close>
  have stopShift: "\<not> nextR ?Mp 1 (TrMax ?Npp) (TrMax ?Npp + 1)"
    using stop trShift by simp
  have "TrMax ?Mp = TrMax ?Npp"
    by (rule TrMax_eq_of_prefix_agree[OF MpT NppT agree cM cN tncShift stopShift])
  thus ?thesis using trShift by simp
qed

end
