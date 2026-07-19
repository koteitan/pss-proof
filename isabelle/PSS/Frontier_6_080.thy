theory Frontier_6_080
  imports Support_6_059
begin

text \<open>§6.7 Front A — d1pos OFFSET-WITHIN-block le0 (the MISSING BRICK): an
  N-base row-0 path from j0+sp to j0+sx staying inside the period (sx < w) lifts
  verbatim into block q<n of N[n], giving le0 (N[n]) (j0+q*w+sp) (j0+q*w+sx).
  Generalises oper_d1pos_le0_within (start-to-offset, sp=0) to offset-to-offset.
  Each base step nextrel0 N u v lifts by oper_gen_nextrel0_within (i1-agnostic);
  the running endpoints never reach the boundary, so only q<n is used.\<close>

lemma oper_d1pos_le0_offset_within:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and sxw: "sx < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and basepath: "(nextrel0 N)\<^sup>*\<^sup>* (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + sp)
                                   (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + sx)"
  shows "le0 ((N::pairseq)[n])
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sp)
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sx)"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"  let ?base = "?j0 + q * ?w"
  let ?Nn = "(N::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>lift the base path \<open>j\<^sub>0+s\<^sub>p \<rightarrow>\<^sup>* y\<close> into block \<open>q\<close>, for any \<open>y\<close> within the period\<close>
  have lift: "\<And>y. (nextrel0 N)\<^sup>*\<^sup>* (?j0 + sp) y \<Longrightarrow> ?j0 + sp \<le> y \<and> y < ?j1
                   \<longrightarrow> (nextrel0 ?Nn)\<^sup>*\<^sup>* (?base + sp) (?base + (y - ?j0))"
  proof -
    fix y assume "(nextrel0 N)\<^sup>*\<^sup>* (?j0 + sp) y"
    thus "?j0 + sp \<le> y \<and> y < ?j1 \<longrightarrow> (nextrel0 ?Nn)\<^sup>*\<^sup>* (?base + sp) (?base + (y - ?j0))"
    proof (induction rule: rtranclp_induct)
      case base
      show ?case by simp
    next
      case (step u v)
      show ?case
      proof
        assume vb: "?j0 + sp \<le> v \<and> v < ?j1"
        have spu: "?j0 + sp \<le> u" using step.hyps(1) nextrel0_rtrancl_mono by blast
        have j0u: "?j0 \<le> u" using spu by linarith
        have uv: "u < v" using step.hyps(2) by (simp add: nextrel0_def)
        have ult: "u < ?j1" using uv vb by linarith
        have IH: "(nextrel0 ?Nn)\<^sup>*\<^sup>* (?base + sp) (?base + (u - ?j0))"
          using step.IH spu ult by simp
        have stp: "nextrel0 ?Nn (?base + (u - ?j0)) (?base + (v - ?j0))"
          using oper_gen_nextrel0_within[OF L notzero hp j0lt qn j0u _ step.hyps(2)] vb
          by simp
        show "(nextrel0 ?Nn)\<^sup>*\<^sup>* (?base + sp) (?base + (v - ?j0))"
          using IH stp by simp
      qed
    qed
  qed
  \<comment> \<open>endpoint \<open>j\<^sub>0+s\<^sub>x\<close>: apply lift; \<open>s\<^sub>x < w\<close> keeps it inside the period\<close>
  have sxj1: "?j0 + sx < ?j1" using sxw j0lt by linarith
  have spge: "?j0 + sp \<le> ?j0 + sx" using basepath nextrel0_rtrancl_mono by blast
  have chain: "(nextrel0 ?Nn)\<^sup>*\<^sup>* (?base + sp) (?base + ((?j0 + sx) - ?j0))"
    using lift[OF basepath] spge sxj1 by simp
  have chain': "(nextrel0 ?Nn)\<^sup>*\<^sup>* (?base + sp) (?base + sx)" using chain by simp
  \<comment> \<open>index bounds for \<open>le0\<close>\<close>
  have spsx: "sp \<le> sx" using spge by simp
  have sxww: "sx < w" using sxw wdef by simp
  have spww: "sp < w" using spsx sxww by linarith
  have klt: "?j0 + q * w + w \<le> ?j0 + n * w"
  proof -
    have "?j0 + q * w + w = ?j0 + (q + 1) * w" by simp
    also have "\<dots> \<le> ?j0 + n * w" using mult_le_mono1[of "q+1" n w] qn by simp
    finally show ?thesis .
  qed
  have basew: "?base = ?j0 + q * w" using wdef by simp
  have lenNnw: "Lng ?Nn = ?j0 + n * w" using lenNn wdef by simp
  have srcb: "?base + sp < Lng ?Nn"
  proof -
    have "?base + sp < ?j0 + q * w + w" using basew spww by linarith
    also have "\<dots> \<le> ?j0 + n * w" by (rule klt)
    finally show ?thesis using lenNnw by simp
  qed
  have dstb: "?base + sx < Lng ?Nn"
  proof -
    have "?base + sx < ?j0 + q * w + w" using basew sxww by linarith
    also have "\<dots> \<le> ?j0 + n * w" by (rule klt)
    finally show ?thesis using lenNnw by simp
  qed
  show ?thesis
    unfolding le0_def using srcb dstb chain' by blast
qed

end
