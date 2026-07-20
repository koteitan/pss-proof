theory Support_7_034
  imports Frontier_7_039
begin

text \<open>系（条件(II)か(IV)の下で \<open>t\<^sub>2\<close> が \<open>0\<close> でないこと）.  For
  \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> with \<open>t\<^sub>1 \<noteq> 0\<close>, under condition (II) or (IV) the second
  body component \<open>t\<^sub>2 = transT2 M = bpHeadT (transC1 M)\<close> is non-zero.  Proof: under
  (II)/(IV) the row-0 parent \<open>j\<^sub>0 = transJ0 M\<close> is non-\<open>M\<close>-admissible, so the
  basepoint \<open>j\<^sub>-\<^sub>1 = transJm1 M = Adm\<^sub>M(j\<^sub>0)\<close> is strictly below \<open>j\<^sub>0\<close>; with
  \<open>j\<^sub>0 < j\<^sub>1\<close> (parent ancestry) this puts \<open>j\<^sub>-\<^sub>1 < Lng (Pred M) - 1\<close>, so \<open>c\<^sub>1\<close> is NOT
  the rightmost-basepoint shape \<open>D\<^bsub>M\<^bsub>1,j\<^sub>-\<^sub>1\<^esub>\<^esub> 0\<close> (@{thm [source] Mark_tail_nonzero}).
  But \<open>c\<^sub>1 = D\<^bsub>v\<^esub> t\<^sub>2\<close> with leftmost head \<open>v = M\<^bsub>1,j\<^sub>-\<^sub>1\<^esub>\<close>
  (@{thm [source] Mark_leftend_form}); were \<open>t\<^sub>2 = 0\<close> then \<open>c\<^sub>1 = D\<^bsub>M\<^bsub>1,j\<^sub>-\<^sub>1\<^esub>\<^esub> 0\<close>,
  the excluded shape.  Hence \<open>t\<^sub>2 \<noteq> 0\<close>.\<close>

lemma m_7_3_t2_nonzero_condIIorIV:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and cond: "transCondII M \<or> transCondIV M"
  shows "transT2 M \<noteq> 0\<^sub>B"
proof
  assume t2z: "transT2 M = 0\<^sub>B"
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  \<comment> \<open>positional abbreviations\<close>
  let ?j1 = "Lng M - 1"
  let ?jp = "parent M 0 ?j1"
  have jpeq: "transJ0 M = ?jp" by (simp add: transJ0_def transJ1_def)
  have jm1eq: "transJm1 M = Adm M ?jp" by (simp add: transJm1_def jpeq)
  \<comment> \<open>(II)/(IV) both assert \<open>\<not> adm M j\<^sub>0\<close>\<close>
  have nadmjp: "\<not> adm M ?jp"
    using cond by (auto simp: transCondII_def transCondIV_def)
  \<comment> \<open>\<open>j\<^sub>-\<^sub>1 = Adm\<^sub>M(j\<^sub>0) < j\<^sub>0 < j\<^sub>1\<close>\<close>
  have jm1ltjp: "transJm1 M < ?jp"
    using nadm_Adm_lt[OF nadmjp] jm1eq by simp
  have parR: "nextR M 0 ?jp ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have jplt: "?jp < ?j1" using parR by (simp add: nextR_def nextrel0_def)
  have jm1small: "transJm1 M < Lng (Pred M) - 1"
  proof -
    have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: Pred_def)
    \<comment> \<open>\<open>j\<^sub>-\<^sub>1 < j\<^sub>0 < j\<^sub>1\<close> gives \<open>j\<^sub>-\<^sub>1 \<le> j\<^sub>0 - 1 \<le> j\<^sub>1 - 2 = Lng (Pred M) - 1\<close>, strict\<close>
    have "transJm1 M < ?j1 - 1" using jm1ltjp jplt by linarith
    thus ?thesis using LP by simp
  qed
  \<comment> \<open>\<open>(Pred M, j\<^sub>-\<^sub>1) \<in> Marked\<close>\<close>
  have mkd: "(Pred M, transJm1 M) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] jm1eq by simp
  \<comment> \<open>\<open>c\<^sub>1\<close> is a single principal term \<open>D\<^bsub>v\<^esub> t\<^sub>2\<close>\<close>
  have pc1: "Lng (PB (transC1 M)) = 1"
    by (rule transC1_single_principal[OF MR MP J1pos T1])
  have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
    using principal_reconstruct[OF pc1]
    by (simp add: transV_def transT2_def)
  have c1mark: "transC1 M = Mark (Pred M) (transJm1 M)"
    by (simp add: transC1_def)
  \<comment> \<open>leftmost head of \<open>c\<^sub>1\<close> is \<open>D\<^bsub>(Pred M)\<^bsub>1,j\<^sub>-\<^sub>1\<^esub>\<^esub>\<close>\<close>
  have c1ne: "transC1 M \<noteq> 0\<^sub>B" using c1Dpt by simp
  have lf: "Mark (Pred M) (transJm1 M) = 0\<^sub>B
            \<or> (\<exists>t. Mark (Pred M) (transJm1 M)
                    = Dpt (enat (entry (Pred M) 1 (transJm1 M))) t)"
    using Mark_leftend_form mkd predRT by blast
  have c1left: "transV M = enat (entry (Pred M) 1 (transJm1 M))"
  proof -
    from lf c1mark c1ne obtain t where
      "transC1 M = Dpt (enat (entry (Pred M) 1 (transJm1 M))) t" by auto
    thus ?thesis using c1Dpt by simp
  qed
  \<comment> \<open>so \<open>t\<^sub>2 = 0\<close> would give \<open>c\<^sub>1 = D\<^bsub>(Pred M)\<^bsub>1,j\<^sub>-\<^sub>1\<^esub>\<^esub> 0\<close> — the excluded shape\<close>
  have c1form: "Mark (Pred M) (transJm1 M)
                  = Dpt (enat (entry (Pred M) 1 (transJm1 M))) 0\<^sub>B"
    using c1mark c1Dpt c1left t2z by simp
  have "Mark (Pred M) (transJm1 M)
          \<noteq> Dpt (enat (entry (Pred M) 1 (transJm1 M))) 0\<^sub>B"
    using Mark_tail_nonzero mkd predRT jm1small by blast
  thus False using c1form by simp
qed


section \<open>§7.3 系（左端第\<open>1\<close>基点の \<open>Mark\<close> の基本性質）— content.md 2417\<close>

text \<open>For \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>: (1) the column-\<open>0\<close> basepoint is marked, and
  (2) among all basepoints \<open>m\<close>, the marked value equals \<open>Trans M\<close> exactly when
  \<open>m = 0\<close>.  The forward direction (\<open>m = 0 \<Longrightarrow> Mark M 0 = Trans M\<close>) is
  @{thm [source] ra_Mark0_eq_Trans}; the reverse (\<open>m > 0 \<Longrightarrow> Mark M m \<noteq> Trans M\<close>)
  is @{thm [source] Mark0_ne_Mark} (the article's \<open>Mark\<close>-order-preservation
  applied at \<open>m\<^sub>0 = 0 < m\<^sub>1 = m\<close>).\<close>

lemma m_7_3_Mark_leftmost1:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
  shows "(M, 0) \<in> Marked"
    and "(M, m) \<in> Marked \<Longrightarrow> (Mark M m = Trans M) \<longleftrightarrow> (m = 0)"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have leM0: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  show m0M: "(M, 0) \<in> Marked"
    using MT leM0 adm_index0 by (simp add: Marked_def)
  assume mM: "(M, m) \<in> Marked"
  show "(Mark M m = Trans M) \<longleftrightarrow> (m = 0)"
  proof
    assume "Mark M m = Trans M"
    show "m = 0"
    proof (rule ccontr)
      assume "m \<noteq> 0"
      hence pos: "0 < m" by simp
      have "Mark M m \<noteq> Trans M" by (rule Mark0_ne_Mark[OF MR m0M mM pos])
      thus False using \<open>Mark M m = Trans M\<close> by simp
    qed
  next
    assume "m = 0"
    thus "Mark M m = Trans M"
      using ra_Mark0_eq_Trans m0M MR by simp
  qed
qed

end
