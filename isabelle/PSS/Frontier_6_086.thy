theory Frontier_6_086
  imports Support_6_065
begin

text \<open>\<open>Pred K = butlast K\<close> is the prefix \<open>[0, Lng K-2]\<close> of \<open>K\<close>, so \<open>nextR _ 1\<close>
  agrees on both ends inside that prefix (@{thm [source] nextrel1_prefix_imp}
  both ways).  This is the engine for the CLEAN degenerate branch \<open>gtw_pred\<close>.\<close>

lemma nextR1_pred_agree:
  assumes L: "1 < Lng K" and xc: "x \<le> Lng K - 2" and yc: "y \<le> Lng K - 2"
  shows "nextR K 1 x y \<longleftrightarrow> nextR (Pred K) 1 x y"
proof -
  have pb: "Pred K = butlast K" using L by (simp add: Pred_def)
  have lbl: "length (butlast K) = Lng K - 1" by simp
  let ?c = "Lng K - 2"
  have agreeKP: "\<And>j. j \<le> ?c \<Longrightarrow> K ! j = (Pred K) ! j"
  proof -
    fix j assume "j \<le> ?c"
    hence jl: "j < length (butlast K)" using L lbl by linarith
    show "K ! j = (Pred K) ! j" using pb jl by (simp add: nth_butlast)
  qed
  have agreePK: "\<And>j. j \<le> ?c \<Longrightarrow> (Pred K) ! j = K ! j" using agreeKP by simp
  have cM: "?c < Lng K" using L by simp
  have cN: "?c < Lng (Pred K)" using L pb lbl by simp
  show ?thesis
  proof
    assume "nextR K 1 x y"
    hence h: "nextrel1 K x y" by (simp add: nextR_def)
    have "nextrel1 (Pred K) x y"
      by (rule nextrel1_prefix_imp[OF agreeKP cM cN xc yc h])
    thus "nextR (Pred K) 1 x y" by (simp add: nextR_def)
  next
    assume "nextR (Pred K) 1 x y"
    hence h: "nextrel1 (Pred K) x y" by (simp add: nextR_def)
    have "nextrel1 K x y"
      by (rule nextrel1_prefix_imp[OF agreePK cN cM xc yc h])
    thus "nextR K 1 x y" by (simp add: nextR_def)
  qed
qed

text \<open>The degenerate \<open>oper\<close> branch (\<open>K[n] = Pred K\<close>) of \<open>gtw_oper_step\<close>, proved
  UNCONDITIONALLY: \<open>GTWF (Pred K)\<close> from \<open>GTWF K\<close>.  Every \<open>y\<close> with a \<open>Pred K\<close>-parent
  has \<open>y < Lng K-1\<close>, hence \<open>parent/hasParent\<close> agree with \<open>K\<close> (@{thm [source]
  nextR1_pred_agree}); apply \<open>GTWF K\<close> in \<open>K\<close>, transfer the interior witness back.
  This is the branch that the last-node \<open>TreeWF\<close> could not handle cleanly.\<close>

lemma gtw_pred:
  assumes L: "1 < Lng K" and gtw: "GTWF K"
  shows "GTWF (Pred K)"
proof (intro allI impI)
  fix y z
  assume hpPy: "hasParent (Pred K) 1 y"
     and H: "parent (Pred K) 1 y < z \<and> z < y"
  have lp: "Lng (Pred K) = Lng K - 1" using L by (simp add: Pred_def)
  \<comment> \<open>\<open>y\<close> sits inside the shared prefix\<close>
  have parPy: "nextR (Pred K) 1 (parent (Pred K) 1 y) y"
    using hpPy unfolding hasParent_def parent_def by (rule theI')
  have ylt: "y < Lng (Pred K)" using parPy by (simp add: nextR_def nextrel1_def)
  have yK: "y \<le> Lng K - 2" using ylt lp by linarith
  have pyJ: "parent (Pred K) 1 y < y" using parPy by (simp add: nextR_def nextrel1_def)
  have pyK: "parent (Pred K) 1 y \<le> Lng K - 2" using pyJ yK by linarith
  \<comment> \<open>reflect \<open>y\<close>'s parent to \<open>K\<close>\<close>
  have parKy_wit: "nextR K 1 (parent (Pred K) 1 y) y"
    using nextR1_pred_agree[OF L pyK yK] parPy by simp
  have hpKy: "hasParent K 1 y"
    unfolding hasParent_def using parKy_wit nextR1_unique by blast
  have parKy: "nextR K 1 (parent K 1 y) y"
    using hpKy unfolding hasParent_def parent_def by (rule theI')
  have peqy: "parent K 1 y = parent (Pred K) 1 y"
    by (rule nextR1_unique[OF parKy parKy_wit])
  \<comment> \<open>apply \<open>GTWF K\<close>\<close>
  have HK: "parent K 1 y < z \<and> z < y" using H peqy by simp
  have gk: "hasParent K 1 z \<and> parent K 1 y \<le> parent K 1 z" using gtw hpKy HK by blast
  hence hpKz: "hasParent K 1 z" and ineqK: "parent K 1 y \<le> parent K 1 z" by auto
  \<comment> \<open>reflect \<open>z\<close> back to \<open>Pred K\<close>\<close>
  have zK: "z \<le> Lng K - 2" using H yK by linarith
  have parKz: "nextR K 1 (parent K 1 z) z"
    using hpKz unfolding hasParent_def parent_def by (rule theI')
  have pzlt: "parent K 1 z < z" using parKz by (simp add: nextR_def nextrel1_def)
  have pzK: "parent K 1 z \<le> Lng K - 2" using pzlt zK by linarith
  have parPz_wit: "nextR (Pred K) 1 (parent K 1 z) z"
    using nextR1_pred_agree[OF L pzK zK] parKz by simp
  have hpPz: "hasParent (Pred K) 1 z"
    unfolding hasParent_def using parPz_wit nextR1_unique by blast
  have parPz: "nextR (Pred K) 1 (parent (Pred K) 1 z) z"
    using hpPz unfolding hasParent_def parent_def by (rule theI')
  have peqz: "parent (Pred K) 1 z = parent K 1 z"
    by (rule nextR1_unique[OF parPz parPz_wit])
  show "hasParent (Pred K) 1 z \<and> parent (Pred K) 1 y \<le> parent (Pred K) 1 z"
  proof
    show "hasParent (Pred K) 1 z" by (rule hpPz)
    have "parent (Pred K) 1 y \<le> parent K 1 z" using peqy ineqK by simp
    thus "parent (Pred K) 1 y \<le> parent (Pred K) 1 z" using peqz by simp
  qed
qed

end
