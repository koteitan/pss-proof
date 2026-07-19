theory Support_6_017
  imports Frontier_6_034
begin

text \<open>§6.8 d1pos \<open>brle\<close>-conclusion closer (UNCAPPED form).  This is the
  contrapositive of the trunk-confinement (\<open>tnc\<close>) that the capped keystone needs:
  if the \<open>N\<close>-reference trunk FILLS its slice (\<open>TrMax (seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red)
  = Lng (seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red) - 1\<close>), then the \<open>M'\<close>-branch is a single component, i.e.
  \<open>brle (M')\<close> holds (\<open>TrMax M' = Lng M'-1 \<or> le0 M' (TrMax M'+1)(Lng M'-1)\<close>).  Proved
  by contradiction: assume \<open>\<not>brle\<close>; then the UNCONDITIONAL UNCAPPED keystone
  @{thm [source] TrMax_seg_oper_d1pos_eq_notbrle_uncapped} gives \<open>TrEq :
  TrMax M' = TrMax (seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red)\<close>, and the first \<open>\<not>brle\<close> conjunct gives \<open>Mlt :
  TrMax M' < Lng M' - 1\<close>; the UNCAPPED span makes \<open>Lng (seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red) = Lng M'\<close>,
  so \<open>TrMax (seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red) = TrMax M' < Lng M'-1 = Lng (seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red) - 1\<close>,
  contradicting the fill hypothesis.  DEEP-VERIFIED (\<open>python/zz_fillb_*.py\<close>,
  is_standard d1pos rank-stratified, KMAX=7 len=12: target \<open>brle\<close> 198/198 on all
  fill slices; the contrapositive \<open>\<not>brle \<Longrightarrow> \<not>fill\<close> 1083/1083; uncapped \<open>TrEq\<close> and
  \<open>Lng N\<^sub>red = Lng M'\<close> hold; capped sub-case is a separate residual brick).\<close>

lemma TrMax_seg_oper_d1pos_brle_uncapped:
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
    \<comment> \<open>UNCAPPED span (min-cap inactive)\<close>
    and span: "j1red = j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    \<comment> \<open>the \<open>N\<close>-reference trunk fills its slice\<close>
    and fill: "TrMax (seg N j0red j1red) = Lng (seg N j0red j1red) - 1"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1')
            = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
       \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1)"
proof (rule ccontr)
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  assume "\<not> ?thesis"
  hence ndisj1: "TrMax ?Mp \<noteq> Lng ?Mp - 1"
    and notle: "\<not> le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1)" by auto
  \<comment> \<open>\<open>M'\<close> non-empty, in \<open>T_PS\<close>; \<open>TrMax M' \<le> Lng M'-1\<close> turns \<open>ndisj1\<close> into \<open>Mlt\<close>\<close>
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have tb: "TrMax ?Mp \<le> Lng ?Mp - 1" by (rule TrMax_bound[OF MpT])
  have Mlt: "TrMax ?Mp < Lng ?Mp - 1" using tb ndisj1 by linarith
  \<comment> \<open>uncapped keystone: \<open>TrMax M' = TrMax N\<^sub>red\<close>\<close>
  have TrEq: "TrMax ?Mp = TrMax ?Np"
    by (rule TrMax_seg_oper_d1pos_eq_notbrle_uncapped[OF N L notzero hp i1z j0lt
          n1 qn s0w s0eq s0lt j0'eq shamt j1redle j0j1red span j0j1' j1lt Mlt notle])
  \<comment> \<open>UNCAPPED span \<open>\<Longrightarrow>\<close> \<open>Lng N\<^sub>red = Lng M'\<close>\<close>
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have spanD: "j1' - j0' = j1red - j0red" using span j0j1red by linarith
  have LenEq: "Lng ?Np = Lng ?Mp" using LNp LMp spanD j0j1red j0j1' by linarith
  \<comment> \<open>fill + \<open>TrEq\<close> + \<open>LenEq\<close> contradict \<open>Mlt\<close>\<close>
  have "TrMax ?Np = Lng ?Np - 1" by (rule fill)
  hence "TrMax ?Mp = Lng ?Mp - 1" using TrEq LenEq by simp
  thus False using Mlt by simp
qed

end
