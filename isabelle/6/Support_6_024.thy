theory Support_6_024
  imports Frontier_6_041
begin

text \<open>§6.8 命題（標準形の切片と \<open>Br\<close> の降順性の関係） — FAITHFUL conditional form
  (article content.md 1422–1615), the \<open>monoT M\<close> core after the WLOG reduction
  (1434).  By induction on the rank \<open>k\<close> (plain, no minimal rank: in the \<open>Suc k\<close>
  step \<open>M = N[n]\<close>, a multi \<open>N\<close> forces \<open>M = P(N)\<^sub>0 \<in> SkT_PS k\<close> so the IH applies to
  \<open>M\<close>; otherwise \<open>N\<close> is monoT and the IH applies to the ambient \<open>N\<close>).
  TODO: base case needs \<open>TrMax (diagSeq) = Lng - 1\<close> (so \<open>Br\<close> of a diagonal slice
  is \<open>[]\<close>); the \<open>Suc k\<close> step is the article's case analysis (1438–1586).\<close>

lemma m_6_8_slice_Br_descending_monoT:
  shows "M \<in> SkT_PS k \<Longrightarrow> monoT M \<Longrightarrow> j0' < j1' \<Longrightarrow> j1' \<le> Lng M - 1
         \<Longrightarrow> leR M 0 j0' j1' \<Longrightarrow> descending (Br (seg M j0' j1'))"
proof -
  have "\<forall>M j0' j1'. M \<in> SkT_PS k \<longrightarrow> monoT M \<longrightarrow> j0' < j1' \<longrightarrow> j1' \<le> Lng M - 1
          \<longrightarrow> leR M 0 j0' j1' \<longrightarrow> descending (Br (seg M j0' j1'))"
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI)
      fix M j0' j1'
      assume M0: "M \<in> SkT_PS 0" and mono: "monoT M" and lt: "j0' < j1'"
        and j1: "j1' \<le> Lng M - 1" and leR: "leR M 0 j0' j1'"
      from M0 obtain u v where Muv: "M = diagSeq u v" and uv: "u \<le> v" by auto
      \<comment> \<open>the slice is itself a diagonal \<open>diagSeq (u+j0') (u+j1')\<close>, whose \<open>Br\<close> is empty\<close>
      have leab: "j0' \<le> j1'" using lt by simp
      have j1v: "j1' \<le> v - u" using j1 uv by (simp add: Muv)
      have slice: "seg M j0' j1' = diagSeq (u + j0') (u + j1')"
        using seg_diagSeq[OF leab j1v uv] Muv by simp
      have le2: "u + j0' \<le> u + j1'" using leab by simp
      have "Br (seg M j0' j1') = []" using slice Br_diagSeq[OF le2] by simp
      thus "descending (Br (seg M j0' j1'))" by (simp add: descending_def)
    qed
  next
    case (Suc k)
    note IHk = Suc.IH
    show ?case
    proof (intro allI impI)
      fix M j0' j1'
      assume MS: "M \<in> SkT_PS (Suc k)" and mono: "monoT M" and lt: "j0' < j1'"
        and j1: "j1' \<le> Lng M - 1" and leR: "leR M 0 j0' j1'"
      from MS obtain N n where Neq: "M = (N::pairseq)[n]" and NS: "N \<in> SkT_PS k"
        and n1: "1 \<le> n" by auto
      have NT: "N \<in> T_PS" using NS SkT_PS_subset_ST_PS ST_PS_T_PS by blast
      have jM: "j1' < Lng M" using j1 lt by linarith
      show "descending (Br (seg M j0' j1'))"
      proof (cases "multiT N")
        case multiN: True
        \<comment> \<open>article 1442: a multi \<open>N\<close> forces \<open>M = P(N)\<^sub>0 \<in> SkT_PS k\<close> (else \<open>M\<close> would be
           multi), so the IH applies to \<open>M\<close> itself\<close>
        have lenPN: "1 < length (P N)" using multiN m_6_2_P_components_2[OF NT] by simp
        have PM: "P M = [M]"
        proof -
          have "\<not> (multiT M \<and> 1 < Lng M)" using mono by (simp add: multiT_def)
          thus ?thesis by (rule poper_P_nonmulti)
        qed
        have MP0: "M = P N ! 0"
        proof (cases "Lng (last (P N)) = 1")
          case last1: True
          have PMeq: "P M = butlast (P N)"
          proof -
            have "P (N[n]) = butlast (P N)"
              using conjunct2[OF m_6_2_P_oper_1[OF NT n1 last1]] lenPN by simp
            thus ?thesis using Neq by simp
          qed
          have "butlast (P N) = [M]" using PMeq PM by simp
          hence l1: "length (butlast (P N)) = 1" by simp
          hence len2: "length (P N) = 2" using lenPN by simp
          have "butlast (P N) = take 1 (P N)"
            using len2 by (simp add: butlast_conv_take)
          also have "\<dots> = [P N ! 0]" using lenPN by (cases "P N") auto
          finally have "butlast (P N) = [P N ! 0]" .
          thus ?thesis using \<open>butlast (P N) = [M]\<close> by simp
        next
          case lastgt: False
          have lastpos: "0 < Lng (last (P N))"
            using idxsum_P_component_nonempty[OF NT, of "length (P N) - 1"] P_nonempty
            by (simp add: last_conv_nth)
          with lastgt have lgt: "1 < Lng (last (P N))" by linarith
          have PMeq: "P M = butlast (P N) @ P ((last (P N))[n])"
            using conjunct2[OF m_6_2_P_oper_2[OF NT n1 lgt]] Neq by simp
          have "length (P N) - 1 \<le> length (butlast (P N))" by simp
          moreover have "1 \<le> length (P ((last (P N))[n]))"
            using P_nonempty by (cases "P ((last (P N))[n])") auto
          ultimately have "2 \<le> length (P M)" using PMeq lenPN by simp
          thus ?thesis using PM by simp
        qed
        have Mmem: "M \<in> SkT_PS k"
        proof -
          have "0 < Lng (P N)" using lenPN by linarith
          hence "P N ! 0 \<in> SkT_PS k" using m_6_7_standard_P_components[OF NS] by blast
          thus ?thesis using MP0 by simp
        qed
        have "descending (Br (seg M j0' j1'))"
          using IHk Mmem mono lt j1 leR by blast
        thus ?thesis .
      next
        case nmN: False
        show ?thesis
        proof (cases "1 < Lng N")
          case LNgt: True
          have monoN: "monoT N" using nmN LNgt by (auto simp: multiT_def zeroT_def)
          show ?thesis
          proof (cases "j1' < Lng N - 1")
            case jsmall: True
            \<comment> \<open>article 1446: the slice lies in the \<open>butlast\<close> prefix where \<open>M = N[n]\<close>
               agrees with \<open>N\<close> (@{thm [source] oper_nth_lt}); reduce to IH on \<open>N\<close>\<close>
            have agree: "\<And>i. i \<le> j1' \<Longrightarrow> M ! i = N ! i"
            proof -
              fix i assume "i \<le> j1'"
              hence "i < Lng N - 1" using jsmall by linarith
              thus "M ! i = N ! i" using Neq oper_nth_lt[OF NT LNgt n1, of i] by simp
            qed
            have segeq: "seg M j0' j1' = seg N j0' j1'"
            proof (rule nth_equalityI)
              show "length (seg M j0' j1') = length (seg N j0' j1')" by simp
              fix i assume "i < length (seg M j0' j1')"
              hence ic: "i < Suc j1' - j0'" by simp
              have ij: "j0' + i \<le> j1'" using ic by linarith
              have "seg M j0' j1' ! i = M ! (j0' + i)" using ic by (rule seg_nth_eq)
              also have "\<dots> = N ! (j0' + i)" using agree[OF ij] by simp
              also have "\<dots> = seg N j0' j1' ! i" using ic by (simp add: seg_nth_eq)
              finally show "seg M j0' j1' ! i = seg N j0' j1' ! i" .
            qed
            \<comment> \<open>transfer \<open>leR\<close> from \<open>M\<close> to \<open>N\<close> via the slice (@{thm [source] adm_le0_seg})\<close>
            have j0j1: "j0' \<le> j1'" using lt by simp
            have jNlt: "j1' < Lng N" using jsmall by linarith
            have idx: "j0' + (j1' - j0') = j1'" using j0j1 by simp
            have stepM: "le0 (seg M j0' j1') 0 (j1' - j0') = le0 M j0' j1'"
              using adm_le0_seg[OF jM _ _ j0j1, of 0 "j1' - j0'"] idx by simp
            have stepN: "le0 (seg N j0' j1') 0 (j1' - j0') = le0 N j0' j1'"
              using adm_le0_seg[OF jNlt _ _ j0j1, of 0 "j1' - j0'"] idx by simp
            have "le0 M j0' j1'" using leR by (simp add: leR_def)
            hence "le0 N j0' j1'" using stepM stepN segeq by simp
            hence leRN: "leR N 0 j0' j1'" by (simp add: leR_def)
            have j1N: "j1' \<le> Lng N - 1" using jsmall by linarith
            have "descending (Br (seg N j0' j1'))"
              using IHk NS monoN lt j1N leRN by blast
            thus ?thesis using segeq by simp
          next
            case jlarge: False
            \<comment> \<open>slice reaches index \<open>\<ge> Lng N - 1\<close>: the \<open>n>1\<close> block cases (article 1452–1589).
               First the shared groundwork: the oper is generic (a degenerate oper
               gives \<open>M = Pred N\<close>, \<open>Lng M = Lng N - 1\<close>, contradicting \<open>j1' \<ge> Lng N - 1\<close>),
               then split on \<open>N\<^bsub>1,Lng N-1\<^esub>\<close> (\<open>= 0\<close>: i1=0, unshifted blocks, 1460–1514;
               \<open>> 0\<close>: i1=1, \<open>\<delta>\<close>-shifted blocks, 1516–1589).\<close>
            have bge: "Lng N - 1 \<le> j1'" using jlarge by simp
            have nzj1N: "Lng N - 1 \<noteq> 0" using LNgt by simp
            have notzeroN: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
            proof
              assume "entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0"
              hence "(N::pairseq)[n] = Pred N" using nzj1N by (simp add: oper_def Let_def)
              hence "Lng M = Lng N - 1" using Neq LNgt by (simp add: Pred_def)
              thus False using bge j1 LNgt by presburger
            qed
            have hasparN: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
            proof (rule ccontr)
              assume "\<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
              hence "(N::pairseq)[n] = Pred N" using notzeroN nzj1N by (simp add: oper_def Let_def)
              hence "Lng M = Lng N - 1" using Neq LNgt by (simp add: Pred_def)
              thus False using bge j1 LNgt by presburger
            qed
            show ?thesis
            proof (cases "entry N 1 (Lng N - 1) = 0")
              case d0zero: True
              \<comment> \<open>\<open>i\<^sub>1 = 0\<close>: layout \<open>M = take j\<^sub>0\<^sup>N N @ (block)\<^bsup>n\<^esup>\<close>, block \<open>= (N\<^sub>j)\<^bsub>j=j\<^sub>0\<^sup>N\<^esub>\<^bsup>j\<^sub>1\<^sup>N-1\<^esup>\<close>
                 (unshifted, article 1460).  GREEN groundwork below; the case
                 analysis 1464/1466/1502 on \<open>j\<^sub>0\<^sup>N\<close> vs \<open>j'\<^sub>0,j'\<^sub>1\<close> remains.\<close>
              have i1zN: "idx1 N (Lng N - 1) = 0" using d0zero by (simp add: idx1_def)
              have haspar0: "hasParent N 0 (Lng N - 1)" using hasparN i1zN by simp
              have parR: "nextR N 0 (parent N 0 (Lng N - 1)) (Lng N - 1)"
                using haspar0 unfolding hasParent_def parent_def by (rule theI')
              have j0Nlt: "parent N 0 (Lng N - 1) < Lng N - 1"
                using poper_nextR_imp_le0[OF parR] by simp
              have layout: "M = take (parent N 0 (Lng N - 1)) N
                @ concat (replicate n (map ((!) N) [parent N 0 (Lng N - 1)..<Lng N - 1]))"
                using Neq oper_d0zero_expand[OF LNgt notzeroN hasparN i1zN] by simp
              have parR0N: "nextrel0 N (parent N 0 (Lng N - 1)) (Lng N - 1)"
                using parR by (simp add: nextR_def)
              let ?j0N = "parent N 0 (Lng N - 1)"  let ?w = "Lng N - 1 - ?j0N"
              have w0: "0 < ?w" using j0Nlt by linarith
              have LngM: "Lng M = ?j0N + n * ?w"
              proof -
                have t: "length (take ?j0N N) = ?j0N" using j0Nlt LNgt by simp
                have b: "length (map ((!) N) [?j0N..<Lng N - 1]) = ?w" by simp
                show ?thesis using layout t b by (simp add: length_concat sum_list_replicate)
              qed
              have le0M: "le0 M j0' j1'" using leR by (simp add: leR_def)
              have j0'lt: "j0' < Lng M" using lt jM by linarith
              show ?thesis
              proof (cases "?j0N \<le> j0'")
                case ge: True
                \<comment> \<open>article 1502: \<open>j'\<^sub>0 \<ge> j\<^sub>0\<^sup>N\<close>; the slice lies inside one block, so it
                   equals a slice of \<open>N\<close> (block periodicity), reduce to IHk on \<open>N\<close>\<close>
                define q where "q = (j0' - ?j0N) div ?w"
                define rr where "rr = (j0' - ?j0N) mod ?w"
                define rp where "rp = j1' - (?j0N + q * ?w)"
                define A where "A = ?j0N + rr"
                define E where "E = ?j0N + rp"
                have qn: "q < n"
                proof -
                  have "j0' - ?j0N < n * ?w" using j0'lt LngM ge by linarith
                  thus ?thesis unfolding q_def using less_mult_imp_div_less by simp
                qed
                have j0'mod: "q * ?w + rr = j0' - ?j0N"
                  unfolding q_def rr_def using div_mult_mod_eq[of "j0' - ?j0N" ?w]
                  by (simp add: mult.commute)
                have j0'split: "j0' = ?j0N + q * ?w + rr" using j0'mod ge by linarith
                \<comment> \<open>confinement: \<open>j'\<^sub>1\<close> stays in \<open>j'\<^sub>0\<close>'s block\<close>
                have abN: "(nextrel0 ((N::pairseq)[n]))\<^sup>*\<^sup>* j0' j1'"
                  using le0M Neq by (simp add: le0_def)
                have altN: "j0' < Lng ((N::pairseq)[n])" using j0'lt Neq by simp
                have conf: "j1' < ?j0N + (q + 1) * ?w"
                  using oper_d0zero_le0_confined[OF LNgt notzeroN hasparN i1zN ge altN abN]
                  by (simp add: q_def)
                have conf': "j1' < ?j0N + q * ?w + ?w" using conf by (simp add: algebra_simps)
                have r'lt: "rp < ?w" unfolding rp_def using conf' j0'split lt by linarith
                have rrr': "rr < rp" unfolding rp_def using j0'split lt by linarith
                have j1'split: "j1' = ?j0N + q * ?w + rp"
                  unfolding rp_def using j0'split lt by linarith
                have aend: "A < E" unfolding A_def E_def using rrr' by simp
                have endle: "E \<le> Lng N - 1" unfolding E_def using r'lt by linarith
                \<comment> \<open>the two slices coincide pointwise (block periodicity)\<close>
                have segeq: "seg M j0' j1' = seg N A E"
                proof (rule nth_equalityI)
                  have "length (seg M j0' j1') = Suc j1' - j0'" by simp
                  also have "\<dots> = Suc E - A"
                    unfolding A_def E_def using j0'split j1'split rrr' by linarith
                  also have "\<dots> = length (seg N A E)" by simp
                  finally show "length (seg M j0' j1') = length (seg N A E)" .
                  fix i assume "i < length (seg M j0' j1')"
                  hence ic: "i < Suc j1' - j0'" by simp
                  have rri: "rr + i < ?w" using ic j0'split j1'split r'lt by linarith
                  have ic': "i < Suc E - A"
                    unfolding A_def E_def using ic j0'split j1'split rrr' by linarith
                  have "seg M j0' j1' ! i = M ! (j0' + i)" using ic by (rule seg_nth_eq)
                  also have "j0' + i = ?j0N + q * ?w + (rr + i)" using j0'split by simp
                  also have "M ! (?j0N + q * ?w + (rr + i)) = N ! (?j0N + (rr + i))"
                    using Neq oper_d0zero_nth[OF LNgt notzeroN hasparN i1zN j0Nlt qn rri] by simp
                  also have "?j0N + (rr + i) = A + i" unfolding A_def by simp
                  also have "N ! (A + i) = seg N A E ! i" using ic' by (simp add: seg_nth_eq)
                  finally show "seg M j0' j1' ! i = seg N A E ! i" .
                qed
                \<comment> \<open>transfer \<open>leR\<close> through the equal slices (@{thm [source] adm_le0_seg})\<close>
                have j0j1: "j0' \<le> j1'" using lt by simp
                have aleb: "A \<le> E" using aend by simp
                have jNlt: "E < Lng N" using endle LNgt by linarith
                have idxM: "j0' + (j1' - j0') = j1'" using j0j1 by simp
                have idxN: "A + (E - A) = E" using aleb by linarith
                have leneq: "j1' - j0' = E - A"
                  unfolding A_def E_def using j0'split j1'split rrr' by linarith
                have stepM: "le0 (seg M j0' j1') 0 (j1' - j0') = le0 M j0' j1'"
                  using adm_le0_seg[OF jM _ _ j0j1, of 0 "j1' - j0'"] idxM by simp
                have stepN: "le0 (seg N A E) 0 (E - A) = le0 N A E"
                  using adm_le0_seg[OF jNlt _ _ aleb, of 0 "E - A"] idxN by simp
                have "le0 N A E" using le0M stepM stepN segeq leneq by simp
                hence leRN: "leR N 0 A E" by (simp add: leR_def)
                have "descending (Br (seg N A E))"
                  using IHk NS monoN aend endle leRN by blast
                thus ?thesis using segeq by simp
              next
                case lt0: False
                \<comment> \<open>article 1466: \<open>j'\<^sub>0 < j\<^sub>0\<^sup>N < j'\<^sub>1\<close>; the slice straddles the trunk/branch
                   junction.  GROUNDWORK (green): \<open>leR N 0 j'\<^sub>0 j\<^sub>1\<^sup>N\<close> (article 1476, via
                   row-0 convexity + prefix agreement) so IHk gives \<open>descending (Br N')\<close>
                   with \<open>N' = seg N j'\<^sub>0 (Lng N-1)\<close>.  The \<open>Br\<close>-under-oper decomposition
                   (\<open>Br M' = take J\<^sub>1 (Br N') @ blocks\<close>, 1486/1492/1498) remains.\<close>
                have j0'lt0N: "j0' < ?j0N" using lt0 by linarith
                have MT: "M \<in> T_PS" using MS SkT_PS_subset_ST_PS ST_PS_T_PS by blast
                have j0Nle1: "?j0N \<le> j1'" using j0Nlt bge by linarith
                have j0'le: "j0' \<le> ?j0N" using j0'lt0N by simp
                \<comment> \<open>row-0 convexity (木構造(1)): \<open>(0,j'\<^sub>0) \<le>\<^sub>M (0,j\<^sub>0\<^sup>N)\<close>\<close>
                have le0Mj0: "le0 M j0' ?j0N"
                  using m_5_1_ancestor_tree_1[OF MT leR j0'le j0Nle1] by (simp add: leR_def)
                \<comment> \<open>\<open>M = N[n]\<close> agrees with \<open>N\<close> on \<open>[0, j\<^sub>0\<^sup>N]\<close>, so \<open>le0\<close> transfers to \<open>N\<close>\<close>
                have agree: "\<And>x. x \<le> ?j0N \<Longrightarrow> M ! x = N ! x"
                  using Neq oper_d0zero_nth_le_parent[OF LNgt notzeroN hasparN i1zN n1] by simp
                have j0NltN: "?j0N < Lng N" using j0Nlt LNgt by linarith
                have nw0: "0 < n * ?w" using n1 w0 by simp
                have j0NltM: "?j0N < Lng M" using LngM nw0 by linarith
                have le0Nj0: "le0 N j0' ?j0N"
                  using le0_prefix_agree[OF agree j0NltM j0NltN _ _ le0Mj0] j0'lt0N by simp
                have le0NjN: "le0 N ?j0N (Lng N - 1)"
                proof -
                  have "(nextrel0 N)\<^sup>*\<^sup>* ?j0N (Lng N - 1)" using parR0N by (rule r_into_rtranclp)
                  thus ?thesis using parR0N by (simp add: le0_def nextrel0_def)
                qed
                have leRN: "leR N 0 j0' (Lng N - 1)"
                  using le0_trans[OF le0Nj0 le0NjN] by (simp add: leR_def)
                have j0'lt1N: "j0' < Lng N - 1" using j0'lt0N j0Nlt by linarith
                have descN': "descending (Br (seg N j0' (Lng N - 1)))"
                  using IHk NS monoN j0'lt1N leRN by blast
                \<comment> \<open>GROUNDWORK for the \<open>Br\<close>-under-oper decomposition (article 1486/1492/1498).
                   Pin \<open>TrMax M' = TrMax N'\<close> (proven brick), expose the branch region
                   \<open>S = seg M' (TrMax N'+1)(Lng M'-1)\<close> with \<open>Br M' = P S\<close>, and record the
                   junction inequality \<open>N\<^bsub>0,j\<^sub>0\<^sup>N\<^esub> < N\<^bsub>0,j\<^sub>1\<^sup>N\<^esub>\<close>.\<close>
                have bge2: "Lng N - 2 \<le> j1'" using bge by linarith
                have jMn: "j1' < Lng ((N::pairseq)[n])" using jM Neq by simp
                have TrEq: "TrMax (seg M j0' j1') = TrMax (seg N j0' (Lng N - 1))"
                  using TrMax_seg_oper_d0zero_eq_caseA[OF NT LNgt notzeroN hasparN i1zN
                    parR0N n1 j0'lt0N bge2 jMn] Neq by simp
                \<comment> \<open>junction: row-0 of the parent step is strict (\<open>nextrel0\<close>)\<close>
                have junc0: "entry N 0 ?j0N < entry N 0 (Lng N - 1)"
                  using parR0N by (simp add: nextrel0_def)
                \<comment> \<open>Split on the position of \<open>FirstNodes(N')\<^bsub>J\<^sub>1\<^esub>\<close> relative to the trunk
                   (article 1484/1490/1496): sub-case A is \<open>j\<^sub>0\<^sup>N - j'\<^sub>0 \<le> TrMax(N')\<close>.\<close>
                let ?Np = "seg N j0' (Lng N - 1)"
                show ?thesis
                proof (cases "?j0N - j0' \<le> TrMax ?Np")
                  case caseA: True
                  \<comment> \<open>article 1484-1488: \<open>FirstNodes(N')\<^bsub>J\<^sub>1\<^esub> = j\<^sub>1\<^sup>N - j'\<^sub>0\<close>, the branch region of
                     \<open>M'\<close> folds into \<open>take J\<^sub>1 (Br N') @ blocks\<close> with all block heads \<open>N\<^bsub>j\<^sub>0\<^sup>N\<^esub>\<close>.
                     Close \<open>descending (Br M')\<close> via the FirstNodes tie-break
                     (@{text descending_Br_of_FN_tiebreak}).\<close>
                  let ?M' = "seg M j0' j1'"
                  have monoM': "monoT ?M'"
                    using m_6_2_mono_ancestor_slice[OF MT lt leR] .
                  have M'ne: "?M' \<noteq> []"
                  proof -
                    have "Lng ?M' = Suc j1' - j0'" by (rule Lng_seg)
                    hence "0 < Lng ?M'" using lt by linarith
                    thus ?thesis using length_greater_0_conv by blast
                  qed
                  have M'T: "?M' \<in> T_PS" using M'ne by (simp add: T_PS_def)
                  have M'PT: "?M' \<in> PT_PS" using M'T monoM' by (simp add: PT_PS_def)
                  \<comment> \<open>article 1480: \<open>TrMax(N') < j\<^sub>1\<^sup>N - j'\<^sub>0\<close> (\<open>Br N' \<noteq> []\<close>).  \<open>?Np \<in> T_PS\<close>,
                     \<open>1 < Lng ?Np\<close> and \<open>?Np\<^bsub>1, last\<^esub> = 0\<close> from the d0zero hypotheses.\<close>
                  have NpL: "Lng ?Np = Lng N - j0'" using j0'lt1N by simp
                  have NpLgt: "1 < Lng ?Np"
                    using NpL j0'lt0N j0Nlt by linarith
                  have Npne: "?Np \<noteq> []" using NpLgt length_greater_0_conv by fastforce
                  have NpT: "?Np \<in> T_PS" using Npne by (simp add: T_PS_def)
                  have Nplast: "?Np ! (Lng ?Np - 1) = N ! (Lng N - 1)"
                  proof -
                    have idx: "Lng ?Np - 1 < Suc (Lng N - 1) - j0'" using NpL NpLgt by linarith
                    have "?Np ! (Lng ?Np - 1) = N ! (j0' + (Lng ?Np - 1))"
                      using idx by (rule seg_nth_eq)
                    moreover have "j0' + (Lng ?Np - 1) = Lng N - 1"
                      using NpL j0'lt1N by linarith
                    ultimately show ?thesis by simp
                  qed
                  have Npz: "entry ?Np 1 (Lng ?Np - 1) = 0"
                    using Nplast d0zero by (simp add: entry_def)
                  have TrNplt: "TrMax ?Np < Lng ?Np - 1"
                    by (rule TrMax_lt_last_of_row1_zero[OF NpT NpLgt Npz])
                  \<comment> \<open>so \<open>Br ?Np \<noteq> []\<close>; record \<open>J\<^sub>1 = Lng (Br ?Np) - 1\<close>\<close>
                  have BrNpne: "Br ?Np \<noteq> []"
                  proof -
                    have ne: "TrMax ?Np \<noteq> Lng ?Np - 1" using TrNplt by simp
                    have "Br ?Np = P (seg ?Np (TrMax ?Np + 1) (Lng ?Np - 1))"
                      using ne by (simp add: Br_def)
                    moreover have "P (seg ?Np (TrMax ?Np + 1) (Lng ?Np - 1)) \<noteq> []"
                      by (rule P_nonempty)
                    ultimately show ?thesis by simp
                  qed
                  \<comment> \<open>branch region of \<open>M'\<close> as a slice of \<open>M\<close>: \<open>Br M' = P (seg M a j'\<^sub>1)\<close>,
                     \<open>a = j'\<^sub>0 + TrMax(N') + 1\<close> (\<open>TrMax M' = TrMax N'\<close> by \<open>TrEq\<close>).\<close>
                  have TrM'lt: "TrMax ?M' < Lng ?M' - 1"
                  proof -
                    have "Lng ?M' - 1 = j1' - j0'" by simp
                    moreover have "TrMax ?M' = TrMax ?Np" using TrEq by simp
                    moreover have "TrMax ?Np < Lng N - 1 - j0'" using TrNplt NpL by linarith
                    moreover have "Lng N - 1 - j0' \<le> j1' - j0'" using bge by linarith
                    ultimately show ?thesis by linarith
                  qed
                  have BrM'P: "Br ?M' = P (seg M (j0' + TrMax ?Np + 1) j1')"
                  proof -
                    have ne: "TrMax ?M' \<noteq> Lng ?M' - 1" using TrM'lt by simp
                    have "Br ?M' = P (seg ?M' (TrMax ?M' + 1) (Lng ?M' - 1))"
                      using ne by (simp add: Br_def)
                    also have "Lng ?M' - 1 = j1' - j0'" by simp
                    also have "seg ?M' (TrMax ?M' + 1) (j1' - j0')
                             = seg M (j0' + (TrMax ?M' + 1)) (j0' + (j1' - j0'))"
                      by (rule seg_of_seg[OF less_imp_le[OF lt]]) simp
                    also have "j0' + (j1' - j0') = j1'" using lt by simp
                    also have "TrMax ?M' = TrMax ?Np" using TrEq by simp
                    finally show ?thesis by simp
                  qed
                  \<comment> \<open>and \<open>Br N' = P (seg N a (Lng N-1))\<close>, the same starting index \<open>a\<close>\<close>
                  have BrNpP: "Br ?Np = P (seg N (j0' + TrMax ?Np + 1) (Lng N - 1))"
                  proof -
                    have ne: "TrMax ?Np \<noteq> Lng ?Np - 1" using TrNplt by simp
                    have "Br ?Np = P (seg ?Np (TrMax ?Np + 1) (Lng ?Np - 1))"
                      using ne by (simp add: Br_def)
                    also have "Lng ?Np - 1 = (Lng N - 1) - j0'" using NpL by simp
                    also have "seg ?Np (TrMax ?Np + 1) ((Lng N - 1) - j0')
                             = seg N (j0' + (TrMax ?Np + 1)) (j0' + ((Lng N - 1) - j0'))"
                      by (rule seg_of_seg[OF _ _]) (use j0'lt1N in auto)
                    also have "j0' + ((Lng N - 1) - j0') = Lng N - 1" using j0'lt1N by simp
                    finally show ?thesis by simp
                  qed
                  \<comment> \<open>CLOSED sub-case A (article 1484-1488) via the \<open>descending_append\<close>
                     route: \<open>Br M' = X @ Y\<close> with \<open>X = P(seg M a (Lng N-2))\<close> the
                     truncated branch and \<open>Y = replicate (qb-1) blk @ [partial]\<close> the
                     repeated whole/partial blocks.  \<open>X\<close> is \<open>butlast (Br N')\<close>
                     (\<open>P_seg_butlast_bridge\<close> with \<open>Pcut(seg N a (Lng N-1)) = endpoint\<close>,
                     proven from \<open>nextrel0_above_parent_trivial\<close>), descending by
                     \<open>descending_take[OF descN']\<close>; \<open>Y\<close> has constant head \<open>N\<^bsub>j\<^sub>0\<^sup>N\<^esub>\<close>
                     (\<open>descending_const_head\<close>); junction \<open>cdom\<close> from \<open>junc0\<close>
                     (block head row-0 \<open>= N\<^bsub>0,j\<^sub>0\<^sup>N\<^esub> < N\<^bsub>0,Lng N-1\<^esub> \<le> entry (last X) 0 0\<close>).\<close>
                  let ?a = "j0' + TrMax ?Np + 1"
                  let ?qb = "(j1' - ?j0N) div ?w"  let ?r2 = "(j1' - ?j0N) mod ?w"
                  let ?blk = "seg N ?j0N (Lng N - 2)"  let ?partial = "seg N ?j0N (?j0N + ?r2)"
                  \<comment> \<open>basic arithmetic facts on \<open>a\<close>, \<open>qb\<close>, \<open>r2\<close>\<close>
                  have aj0N: "?j0N < ?a" using caseA j0'lt0N by linarith
                  have alt1N: "?a \<le> Lng N - 1"
                  proof -
                    have "TrMax ?Np < Lng ?Np - 1" by (rule TrNplt)
                    hence "TrMax ?Np < Lng N - 1 - j0'" using NpL by linarith
                    thus ?thesis using j0'lt1N by linarith
                  qed
                  have aMlt: "?a < Lng M"
                  proof -
                    have "?a \<le> Lng N - 1" by (rule alt1N)
                    also have "Lng N - 1 \<le> j1'" by (rule bge)
                    also have "j1' < Lng M" by (rule jM)
                    finally show ?thesis .
                  qed
                  have jw: "?j0N + ?w = Lng N - 1" using w0 j0Nlt by simp
                  have qbr2: "?qb * ?w + ?r2 = j1' - ?j0N"
                    using div_mult_mod_eq[of "j1' - ?j0N" ?w] by (simp add: mult.commute)
                  have j1Nge: "?j0N \<le> j1'" using j0Nlt bge by linarith
                  have j1split: "j1' = ?j0N + ?qb * ?w + ?r2" using qbr2 j1Nge by linarith
                  have r2w: "?r2 < ?w" using w0 by simp
                  have qb1: "1 \<le> ?qb"
                  proof -
                    have "?w \<le> j1' - ?j0N" using bge jw j1Nge by linarith
                    thus ?thesis using w0 by (simp add: div_greater_zero_iff Suc_leI)
                  qed
                  have qbn: "?qb < n"
                  proof -
                    have "j1' - ?j0N < n * ?w" using jM LngM j1Nge by linarith
                    thus ?thesis using less_mult_imp_div_less by simp
                  qed
                  \<comment> \<open>blockmono: every offset within a block is \<open>\<ge>\<^sub>0\<close> the block start \<open>j\<^sub>0\<^sup>N\<close>\<close>
                  have blockmono: "\<And>s. s < ?w \<Longrightarrow> le0 N ?j0N (?j0N + s)"
                    using parent_block_le0[OF parR0N] by simp
                  \<comment> \<open>the two main regimes coincide with \<open>J\<^sub>1 = Lng (Br N') - 1 \<ge> 1\<close> vs \<open>= 0\<close>\<close>
                  show ?thesis
                  proof (cases "?a < Lng N - 1")
                    case asmall: True
                    \<comment> \<open>regime \<open>J\<^sub>1 \<ge> 1\<close>: the branch slice \<open>seg N a (Lng N-1) = Br N'\<close> is multi,
                       so \<open>P(seg M a (Lng N-2)) = butlast (Br N') = take J\<^sub>1 (Br N')\<close>\<close>
                    have aw: "?a \<le> Lng N - 2" using asmall by linarith
                    \<comment> \<open>fold identity: \<open>Br M' = P(seg M a (Lng N-2)) @ replicate (qb-1) blk @ [partial]\<close>\<close>
                    have foldmid: "P (seg M ?a (?j0N + ?qb * ?w - 1))
                                 = P (seg M ?a (Lng N - 2)) @ replicate (?qb - 1) ?blk"
                      using oper_d0zero_seg_P_hfold[OF LNgt notzeroN hasparN i1zN aj0N aw
                        blockmono qbn[THEN less_imp_le] qb1] Neq by simp
                    have aB': "?a < ?j0N + ?qb * ?w"
                    proof -
                      have "?a \<le> Lng N - 2" by (rule aw)
                      also have "Lng N - 2 < ?j0N + ?w" using jw w0 by linarith
                      also have "?j0N + ?w \<le> ?j0N + ?qb * ?w" using qb1 by simp
                      finally show ?thesis .
                    qed
                    have Bsk: "?j0N + ?qb * ?w + ?r2 < Lng M" using j1split jM by simp
                    have bmr2: "le0 N ?j0N (?j0N + ?r2)" using blockmono[OF r2w] .
                    have foldlast: "P (seg M ?a j1')
                                  = P (seg M ?a (?j0N + ?qb * ?w - 1)) @ [?partial]"
                      using oper_d0zero_seg_P_split[OF LNgt notzeroN hasparN i1zN aj0N qb1 aB'
                        r2w bmr2 Bsk[unfolded Neq] qbn] j1split Neq by simp
                    have fold: "Br ?M' = P (seg M ?a (Lng N - 2))
                                       @ replicate (?qb - 1) ?blk @ [?partial]"
                      using BrM'P foldlast foldmid by simp
                    \<comment> \<open>the prefix \<open>seg M a (Lng N-2)\<close> equals \<open>seg N a (Lng N-2)\<close> (period intact)\<close>
                    have segMN: "seg M ?a (Lng N - 2) = seg N ?a (Lng N - 2)"
                    proof (rule nth_equalityI)
                      show "length (seg M ?a (Lng N - 2)) = length (seg N ?a (Lng N - 2))" by simp
                      fix i assume "i < length (seg M ?a (Lng N - 2))"
                      hence ic: "i < Suc (Lng N - 2) - ?a" by simp
                      have ai: "?a + i < Lng N - 1" using ic aw by linarith
                      have "seg M ?a (Lng N - 2) ! i = M ! (?a + i)" using ic by (rule seg_nth_eq)
                      also have "\<dots> = N ! (?a + i)"
                        using Neq oper_nth_lt[OF NT LNgt n1 ai] by simp
                      also have "\<dots> = seg N ?a (Lng N - 2) ! i" using ic by (simp add: seg_nth_eq)
                      finally show "seg M ?a (Lng N - 2) ! i = seg N ?a (Lng N - 2) ! i" .
                    qed
                    \<comment> \<open>\<open>seg N a (Lng N-1) = Br N'\<close> is multi (\<open>Lng (Br N') = J\<^sub>1 + 1 \<ge> 2\<close>)\<close>
                    have aLN1: "?a < Lng N - 1" by (rule asmall)
                    have segNT: "seg N ?a (Lng N - 1) \<in> T_PS"
                    proof -
                      have "0 < Lng (seg N ?a (Lng N - 1))" using aLN1 by simp
                      hence "seg N ?a (Lng N - 1) \<noteq> []" using length_greater_0_conv by blast
                      thus ?thesis by (simp add: T_PS_def)
                    qed
                    have LsegN: "1 < Lng (seg N ?a (Lng N - 1))" using aLN1 by simp
                    \<comment> \<open>\<open>seg N a (Lng N-1)\<close> is multi: it is not mono, because \<open>a\<close> (above \<open>j\<^sub>0\<^sup>N\<close>)
                       is NOT a row-0 ancestor of the leaf (\<open>nextrel0_above_parent_trivial\<close>),
                       so \<open>leR (seg) 0 0 (Lng-1)\<close> fails.\<close>
                    have notmono: "\<not> le0 N ?a (Lng N - 1)"
                    proof
                      assume "le0 N ?a (Lng N - 1)"
                      hence "(nextrel0 N)\<^sup>*\<^sup>* ?a (Lng N - 1)" by (simp add: le0_def)
                      hence "?a = Lng N - 1"
                        using nextrel0_above_parent_trivial[OF parR0N] aj0N by simp
                      thus False using aLN1 by simp
                    qed
                    have multiseg: "multiT (seg N ?a (Lng N - 1))"
                    proof -
                      have nz: "\<not> zeroT (seg N ?a (Lng N - 1))" using LsegN by (simp add: zeroT_def)
                      have aj1: "?a \<le> Lng N - 1" using aLN1 by linarith
                      have NLpos: "Lng N - 1 < Lng N" using LNgt by linarith
                      have idx: "(Lng N - 1) - ?a \<le> (Lng N - 1) - ?a" by simp
                      have aend: "?a + ((Lng N - 1) - ?a) = Lng N - 1" using aj1 by simp
                      have transfer0: "le0 (seg N ?a (Lng N - 1)) 0 ((Lng N - 1) - ?a)
                                    = le0 N (?a + 0) (?a + ((Lng N - 1) - ?a))"
                        using adm_le0_seg[OF NLpos _ idx aj1, of 0] by blast
                      have transfer: "le0 (seg N ?a (Lng N - 1)) 0 ((Lng N - 1) - ?a)
                                    = le0 N ?a (Lng N - 1)"
                        using transfer0 aend by (metis add_0_right)
                      have Lseg1: "Lng (seg N ?a (Lng N - 1)) - 1 = (Lng N - 1) - ?a"
                        using aLN1 by simp
                      have "\<not> leR (seg N ?a (Lng N - 1)) 0 0 (Lng (seg N ?a (Lng N - 1)) - 1)"
                        using notmono transfer Lseg1 by (simp add: leR_def)
                      thus ?thesis using nz by (simp add: multiT_def monoT_def)
                    qed
                    have BrNpne2: "1 < length (Br ?Np)"
                      using m_6_2_P_components_2[OF segNT] multiseg BrNpP by simp
                    \<comment> \<open>\<open>Pcut(seg N a (Lng N-1)) = (Lng N-1) - a\<close>: the leaf has no proper
                       row-0 ancestor above \<open>j\<^sub>0\<^sup>N\<close>, and the slice starts above \<open>j\<^sub>0\<^sup>N\<close>\<close>
                    have Pcutend: "Pcut (seg N ?a (Lng N - 1)) = (Lng N - 1) - ?a"
                    proof -
                      let ?S = "seg N ?a (Lng N - 1)"  let ?e = "(Lng N - 1) - ?a"
                      have Le: "Lng ?S - 1 = ?e" using aLN1 by simp
                      let ?Q = "\<lambda>j. 0 < j \<and> j \<le> Lng ?S - 1 \<and> leR ?S 0 j (Lng ?S - 1)"
                      have wit: "?Q ?e" using LsegN Le by (auto simp: leR_def le0_def)
                      have uniq: "\<And>j. ?Q j \<Longrightarrow> j = ?e"
                      proof -
                        fix j assume Qj: "?Q j"
                        hence jpos: "0 < j" and jle: "j \<le> ?e" and lej: "leR ?S 0 j ?e"
                          using Le by auto
                        have jlt: "j < Lng N" using jle aLN1 by linarith
                        have ele: "?e \<le> Lng N" using aLN1 by linarith
                        have aj1: "?a \<le> Lng N - 1" using aLN1 by linarith
                        have transfer: "le0 ?S j ?e = le0 N (?a + j) (?a + ?e)"
                          using adm_le0_seg[where M=N and j0'="?a" and j1'="Lng N - 1"
                              and a=j and b="?e"] aj1 jle Le by simp
                        have aej: "?a + ?e = Lng N - 1" using aLN1 by simp
                        have le0je: "le0 ?S j ?e" using lej by (simp add: leR_def)
                        have le0aje: "le0 N (?a + j) (Lng N - 1)"
                          using le0je transfer aej by metis
                        have chain: "(nextrel0 N)\<^sup>*\<^sup>* (?a + j) (Lng N - 1)"
                          using le0aje unfolding le0_def by (rule conjunct2[OF conjunct2])
                        have agt: "?j0N < ?a + j" using aj0N jpos by linarith
                        have "?a + j = Lng N - 1"
                          by (rule nextrel0_above_parent_trivial[OF parR0N chain agt])
                        thus "j = ?e" using aej by linarith
                      qed
                      have "(LEAST j. ?Q j) = ?e"
                        by (rule Least_equality[where P = ?Q and x = ?e, OF wit])
                           (use uniq in fastforce)
                      thus ?thesis unfolding Pcut_def by simp
                    qed
                    \<comment> \<open>bridge: \<open>P(seg N a (Lng N-2)) = butlast (Br N') = take J\<^sub>1 (Br N')\<close>\<close>
                    have bridge: "P (seg N ?a (Lng N - 2)) = butlast (Br ?Np)"
                    proof -
                      have "P (seg N ?a ((Lng N - 1) - 1)) = butlast (P (seg N ?a (Lng N - 1)))"
                        by (rule P_seg_butlast_bridge[OF aLN1 multiseg]) (use Pcutend in simp)
                      moreover have "(Lng N - 1) - 1 = Lng N - 2" by simp
                      ultimately show ?thesis using BrNpP by simp
                    qed
                    have Xdesc: "descending (P (seg M ?a (Lng N - 2)))"
                    proof -
                      have "P (seg M ?a (Lng N - 2)) = butlast (Br ?Np)"
                        using segMN bridge by simp
                      also have "butlast (Br ?Np) = take (length (Br ?Np) - 1) (Br ?Np)"
                        by (simp add: butlast_conv_take)
                      finally show ?thesis using descending_take[OF descN'] by simp
                    qed
                    \<comment> \<open>tail \<open>Y\<close>: every component starts with the block head \<open>N\<^bsub>j\<^sub>0\<^sup>N\<^esub>\<close>\<close>
                    let ?Y = "replicate (?qb - 1) ?blk @ [?partial]"
                    have blkhd0: "entry ?blk 0 0 = entry N 0 ?j0N"
                      using w0 j0Nlt by (simp add: entry_seg)
                    have blkhd1: "entry ?blk 1 0 = entry N 1 ?j0N"
                      using w0 j0Nlt by (simp add: entry_seg)
                    have parhd0: "entry ?partial 0 0 = entry N 0 ?j0N"
                      by (simp add: entry_seg)
                    have parhd1: "entry ?partial 1 0 = entry N 1 ?j0N"
                      by (simp add: entry_seg)
                    have Ydesc: "descending ?Y"
                    proof (rule descending_const_head)
                      fix J assume "J < Lng ?Y"
                      hence Jlt: "J < (?qb - 1) + 1" by simp
                      show "entry (?Y ! J) 0 0 = entry N 0 ?j0N \<and> entry (?Y ! J) 1 0 = entry N 1 ?j0N"
                      proof (cases "J < ?qb - 1")
                        case True
                        hence "?Y ! J = ?blk" by (simp add: nth_append)
                        thus ?thesis using blkhd0 blkhd1 by simp
                      next
                        case False
                        hence "J = ?qb - 1" using Jlt by linarith
                        hence "?Y ! J = ?partial" by (simp add: nth_append)
                        thus ?thesis using parhd0 parhd1 by simp
                      qed
                    qed
                    \<comment> \<open>junction: \<open>cdom (last X) (Y\<^bsub>0\<^esub>)\<close>; the block head row-0 \<open>= N\<^bsub>0,j\<^sub>0\<^sup>N\<^esub>\<close> is
                       strictly below the leaf row-0 \<open>= N\<^bsub>0,Lng N-1\<^esub> \<le> entry (last X) 0 0\<close>\<close>
                    have leafval: "entry (Br ?Np ! (length (Br ?Np) - 1)) 0 0 = entry N 0 (Lng N - 1)"
                    proof -
                      have lastB: "Br ?Np ! (length (Br ?Np) - 1) = last (Br ?Np)"
                        using BrNpne by (simp add: last_conv_nth)
                      have "last (Br ?Np) = drop (Pcut (seg N ?a (Lng N - 1))) (seg N ?a (Lng N - 1))"
                        using poper_last_P_multi[OF multiseg LsegN] BrNpP by simp
                      also have "\<dots> = drop ((Lng N - 1) - ?a) (seg N ?a (Lng N - 1))"
                        using Pcutend by simp
                      also have "\<dots> = seg N (?a + ((Lng N - 1) - ?a)) (Lng N - 1)"
                        by (rule drop_seg)
                      also have "?a + ((Lng N - 1) - ?a) = Lng N - 1" using aLN1 by simp
                      finally have "last (Br ?Np) = seg N (Lng N - 1) (Lng N - 1)" .
                      thus ?thesis using lastB by (simp add: entry_seg)
                    qed
                    have junc_cdom: "cdom (last (P (seg M ?a (Lng N - 2)))) (?Y ! 0)"
                    proof -
                      \<comment> \<open>\<open>last X = Br N' ! (J\<^sub>1 - 1)\<close>, the penultimate branch component\<close>
                      have lenBrk: "length (Br ?Np) = Suc (length (Br ?Np) - 1)"
                        using BrNpne by (cases "Br ?Np") auto
                      have Xeq: "P (seg M ?a (Lng N - 2)) = take (length (Br ?Np) - 1) (Br ?Np)"
                        using segMN bridge by (simp add: butlast_conv_take)
                      have Xlen: "length (P (seg M ?a (Lng N - 2))) = length (Br ?Np) - 1"
                        using Xeq BrNpne2 by simp
                      have Xne: "P (seg M ?a (Lng N - 2)) \<noteq> []" using Xlen BrNpne2 by auto
                      have arith2: "length (P (seg M ?a (Lng N - 2))) - 1 = length (Br ?Np) - 2"
                        using Xlen by simp
                      have lt2: "length (Br ?Np) - 2 < length (Br ?Np) - 1"
                        using BrNpne2 by linarith
                      have lastXeq: "last (P (seg M ?a (Lng N - 2))) = Br ?Np ! (length (Br ?Np) - 2)"
                      proof -
                        have "last (P (seg M ?a (Lng N - 2)))
                              = P (seg M ?a (Lng N - 2)) ! (length (P (seg M ?a (Lng N - 2))) - 1)"
                          using Xne by (rule last_conv_nth)
                        also have "\<dots> = P (seg M ?a (Lng N - 2)) ! (length (Br ?Np) - 2)"
                          using arith2 by simp
                        also have "\<dots> = take (length (Br ?Np) - 1) (Br ?Np) ! (length (Br ?Np) - 2)"
                          using Xeq by simp
                        also have "\<dots> = Br ?Np ! (length (Br ?Np) - 2)"
                          using lt2 by simp
                        finally show ?thesis .
                      qed
                      \<comment> \<open>\<open>descN'\<close> gives \<open>cdom (Br N' ! (J\<^sub>1-1)) (Br N' ! J\<^sub>1)\<close>\<close>
                      have cdomBr: "cdom (Br ?Np ! (length (Br ?Np) - 2)) (Br ?Np ! (length (Br ?Np) - 1))"
                      proof (rule descending_cdomD[OF descN'])
                        show "length (Br ?Np) - 2 \<le> length (Br ?Np) - 1" by simp
                        show "length (Br ?Np) - 1 < Lng (Br ?Np)" using BrNpne by simp
                      qed
                      \<comment> \<open>leaf row-0 \<open>\<le> entry (last X) 0 0\<close> from \<open>cdomBr\<close>\<close>
                      have leaf_le: "entry N 0 (Lng N - 1) \<le> entry (last (P (seg M ?a (Lng N - 2)))) 0 0"
                        using cdomBr leafval lastXeq by (simp add: cdom_def)
                      \<comment> \<open>block-head row-0 \<open>= N\<^bsub>0,j\<^sub>0\<^sup>N\<^esub> < N\<^bsub>0,Lng N-1\<^esub>\<close> (\<open>junc0\<close>) \<open>\<Longrightarrow>\<close> strict drop\<close>
                      have Y0hd: "entry (?Y ! 0) 0 0 = entry N 0 ?j0N"
                      proof (cases "?qb - 1 = 0")
                        case True hence "?Y ! 0 = ?partial" by simp
                          thus ?thesis using parhd0 by simp
                      next
                        case False hence "?Y ! 0 = ?blk" by (simp add: nth_append)
                          thus ?thesis using blkhd0 by simp
                      qed
                      have "entry (?Y ! 0) 0 0 < entry (last (P (seg M ?a (Lng N - 2)))) 0 0"
                        using Y0hd junc0 leaf_le by linarith
                      thus ?thesis by (simp add: cdom_def)
                    qed
                    have "descending (P (seg M ?a (Lng N - 2)) @ ?Y)"
                      by (rule descending_append[OF Xdesc Ydesc]) (use junc_cdom in simp)
                    thus ?thesis using fold by simp
                  next
                    case alarge: False
                    \<comment> \<open>regime \<open>J\<^sub>1 = 0\<close> (\<open>a = Lng N - 1 = j\<^sub>0\<^sup>N + w\<close>): \<open>Br M' = P(seg M a j1')\<close>
                       is the pure block tail \<open>replicate (qb-1) blk @ [partial]\<close>
                       (@{thm [source] oper_d0zero_seg_P_blk1fold}), all heads \<open>N\<^bsub>j\<^sub>0\<^sup>N\<^esub>\<close>,
                       hence descending by @{thm [source] descending_const_head}.\<close>
                    have aeq: "?a = Lng N - 1" using alarge alt1N by linarith
                    have aeqw: "?a = ?j0N + ?w" using aeq jw by simp
                    \<comment> \<open>\<open>qb = Suc (qb-1)\<close> and \<open>j1' = j\<^sub>0\<^sup>N + Suc (qb-1) * w + r2\<close>\<close>
                    have qbS: "?qb = Suc (?qb - 1)" using qb1 by simp
                    have j1split': "j1' = ?j0N + Suc (?qb - 1) * ?w + ?r2"
                      using j1split qbS by simp
                    have qbn': "Suc (?qb - 1) < n" using qbn qbS by simp
                    have fold: "Br ?M' = replicate (?qb - 1) ?blk @ [?partial]"
                    proof -
                      have "P (seg M ?a j1') = replicate (?qb - 1) ?blk @ [?partial]"
                        using oper_d0zero_seg_P_blk1fold[OF LNgt notzeroN hasparN i1zN j0Nlt
                          blockmono r2w qbn'] aeqw j1split' Neq by simp
                      thus ?thesis using BrM'P by simp
                    qed
                    \<comment> \<open>tail descending: every component starts with the block head \<open>N\<^bsub>j\<^sub>0\<^sup>N\<^esub>\<close>\<close>
                    have blkhd0: "entry ?blk 0 0 = entry N 0 ?j0N"
                      using w0 j0Nlt by (simp add: entry_seg)
                    have blkhd1: "entry ?blk 1 0 = entry N 1 ?j0N"
                      using w0 j0Nlt by (simp add: entry_seg)
                    have parhd0: "entry ?partial 0 0 = entry N 0 ?j0N" by (simp add: entry_seg)
                    have parhd1: "entry ?partial 1 0 = entry N 1 ?j0N" by (simp add: entry_seg)
                    let ?Y = "replicate (?qb - 1) ?blk @ [?partial]"
                    have Ydesc: "descending ?Y"
                    proof (rule descending_const_head)
                      fix J assume "J < Lng ?Y"
                      hence Jlt: "J < (?qb - 1) + 1" by simp
                      show "entry (?Y ! J) 0 0 = entry N 0 ?j0N \<and> entry (?Y ! J) 1 0 = entry N 1 ?j0N"
                      proof (cases "J < ?qb - 1")
                        case True
                        hence "?Y ! J = ?blk" by (simp add: nth_append)
                        thus ?thesis using blkhd0 blkhd1 by simp
                      next
                        case False
                        hence "J = ?qb - 1" using Jlt by linarith
                        hence "?Y ! J = ?partial" by (simp add: nth_append)
                        thus ?thesis using parhd0 parhd1 by simp
                      qed
                    qed
                    show ?thesis using fold Ydesc by simp
                  qed
                next
                  case caseBC: False
                  \<comment> \<open>article 1490/1496: \<open>TrMax(N') < d = j\<^sub>0\<^sup>N - j'\<^sub>0\<close>.  Re-derive the same
                     \<open>Br M'\<close>-decomposition groundwork as sub-case A (none of A's local
                     facts are in scope here), then split on the regime
                     \<open>j\<^sub>-\<^sub>1 \<le> TrMax(N')\<close> (sub-case B) vs \<open>TrMax(N') < j\<^sub>-\<^sub>1\<close> (sub-case C).\<close>
                  let ?Np = "seg N j0' (Lng N - 1)"
                  have BClt: "TrMax ?Np < ?j0N - j0'" using caseBC by linarith
                  let ?M' = "seg M j0' j1'"
                  have monoM': "monoT ?M'"
                    using m_6_2_mono_ancestor_slice[OF MT lt leR] .
                  have M'ne: "?M' \<noteq> []"
                  proof -
                    have "Lng ?M' = Suc j1' - j0'" by (rule Lng_seg)
                    hence "0 < Lng ?M'" using lt by linarith
                    thus ?thesis using length_greater_0_conv by blast
                  qed
                  have NpL: "Lng ?Np = Lng N - j0'" using j0'lt1N by simp
                  have NpLgt: "1 < Lng ?Np" using NpL j0'lt0N j0Nlt by linarith
                  have Npne: "?Np \<noteq> []" using NpLgt length_greater_0_conv by fastforce
                  have NpT: "?Np \<in> T_PS" using Npne by (simp add: T_PS_def)
                  have Nplast: "?Np ! (Lng ?Np - 1) = N ! (Lng N - 1)"
                  proof -
                    have idx: "Lng ?Np - 1 < Suc (Lng N - 1) - j0'" using NpL NpLgt by linarith
                    have "?Np ! (Lng ?Np - 1) = N ! (j0' + (Lng ?Np - 1))"
                      using idx by (rule seg_nth_eq)
                    moreover have "j0' + (Lng ?Np - 1) = Lng N - 1"
                      using NpL j0'lt1N by linarith
                    ultimately show ?thesis by simp
                  qed
                  have Npz: "entry ?Np 1 (Lng ?Np - 1) = 0"
                    using Nplast d0zero by (simp add: entry_def)
                  have TrNplt: "TrMax ?Np < Lng ?Np - 1"
                    by (rule TrMax_lt_last_of_row1_zero[OF NpT NpLgt Npz])
                  have BrNpne: "Br ?Np \<noteq> []"
                  proof -
                    have ne: "TrMax ?Np \<noteq> Lng ?Np - 1" using TrNplt by simp
                    have "Br ?Np = P (seg ?Np (TrMax ?Np + 1) (Lng ?Np - 1))"
                      using ne by (simp add: Br_def)
                    moreover have "P (seg ?Np (TrMax ?Np + 1) (Lng ?Np - 1)) \<noteq> []"
                      by (rule P_nonempty)
                    ultimately show ?thesis by simp
                  qed
                  have TrM'lt: "TrMax ?M' < Lng ?M' - 1"
                  proof -
                    have "Lng ?M' - 1 = j1' - j0'" by simp
                    moreover have "TrMax ?M' = TrMax ?Np" using TrEq by simp
                    moreover have "TrMax ?Np < Lng N - 1 - j0'" using TrNplt NpL by linarith
                    moreover have "Lng N - 1 - j0' \<le> j1' - j0'" using bge by linarith
                    ultimately show ?thesis by linarith
                  qed
                  let ?a = "j0' + TrMax ?Np + 1"
                  let ?qb = "(j1' - ?j0N) div ?w"  let ?r2 = "(j1' - ?j0N) mod ?w"
                  let ?blk = "seg N ?j0N (Lng N - 2)"  let ?partial = "seg N ?j0N (?j0N + ?r2)"
                  have BrM'P: "Br ?M' = P (seg M ?a j1')"
                  proof -
                    have ne: "TrMax ?M' \<noteq> Lng ?M' - 1" using TrM'lt by simp
                    have "Br ?M' = P (seg ?M' (TrMax ?M' + 1) (Lng ?M' - 1))"
                      using ne by (simp add: Br_def)
                    also have "Lng ?M' - 1 = j1' - j0'" by simp
                    also have "seg ?M' (TrMax ?M' + 1) (j1' - j0')
                             = seg M (j0' + (TrMax ?M' + 1)) (j0' + (j1' - j0'))"
                      by (rule seg_of_seg[OF less_imp_le[OF lt]]) simp
                    also have "j0' + (j1' - j0') = j1'" using lt by simp
                    also have "TrMax ?M' = TrMax ?Np" using TrEq by simp
                    finally show ?thesis by simp
                  qed
                  have BrNpP: "Br ?Np = P (seg N ?a (Lng N - 1))"
                  proof -
                    have ne: "TrMax ?Np \<noteq> Lng ?Np - 1" using TrNplt by simp
                    have "Br ?Np = P (seg ?Np (TrMax ?Np + 1) (Lng ?Np - 1))"
                      using ne by (simp add: Br_def)
                    also have "Lng ?Np - 1 = (Lng N - 1) - j0'" using NpL by simp
                    also have "seg ?Np (TrMax ?Np + 1) ((Lng N - 1) - j0')
                             = seg N (j0' + (TrMax ?Np + 1)) (j0' + ((Lng N - 1) - j0'))"
                      by (rule seg_of_seg[OF _ _]) (use j0'lt1N in auto)
                    also have "j0' + ((Lng N - 1) - j0') = Lng N - 1" using j0'lt1N by simp
                    finally show ?thesis by simp
                  qed
                  \<comment> \<open>basic arithmetic on \<open>a\<close>, \<open>qb\<close>, \<open>r2\<close>; in sub-case BC \<open>a \<le> j\<^sub>0\<^sup>N\<close>\<close>
                  have ale: "?a \<le> ?j0N" using BClt j0'lt0N by linarith
                  have alt1N: "?a \<le> Lng N - 1"
                  proof -
                    have "TrMax ?Np < Lng N - 1 - j0'" using TrNplt NpL by linarith
                    thus ?thesis using j0'lt1N by linarith
                  qed
                  have jw: "?j0N + ?w = Lng N - 1" using w0 j0Nlt by simp
                  have qbr2: "?qb * ?w + ?r2 = j1' - ?j0N"
                    using div_mult_mod_eq[of "j1' - ?j0N" ?w] by (simp add: mult.commute)
                  have j1Nge: "?j0N \<le> j1'" using j0Nlt bge by linarith
                  have j1split: "j1' = ?j0N + ?qb * ?w + ?r2" using qbr2 j1Nge by linarith
                  have r2w: "?r2 < ?w" using w0 by simp
                  have qbn: "?qb < n"
                  proof -
                    have "j1' - ?j0N < n * ?w" using jM LngM j1Nge by linarith
                    thus ?thesis using less_mult_imp_div_less by simp
                  qed
                  have blockmono: "\<And>s. s < ?w \<Longrightarrow> le0 N ?j0N (?j0N + s)"
                    using parent_block_le0[OF parR0N] by simp
                  \<comment> \<open>HIGH half (block-0-anchored fold): \<open>P(seg M j\<^sub>0\<^sup>N j'\<^sub>1) = replicate qb blk @ [partial]\<close>\<close>
                  have hival: "P (seg M ?j0N j1') = replicate ?qb ?blk @ [?partial]"
                    using oper_d0zero_seg_P_blk0fold[OF LNgt notzeroN hasparN i1zN j0Nlt
                      blockmono r2w qbn] j1split Neq by simp
                  \<comment> \<open>HIGH half is descending: all heads are the block head \<open>N\<^bsub>j\<^sub>0\<^sup>N\<^esub>\<close>\<close>
                  let ?Y = "replicate ?qb ?blk @ [?partial]"
                  have blkhd0: "entry ?blk 0 0 = entry N 0 ?j0N"
                    using w0 j0Nlt by (simp add: entry_seg)
                  have blkhd1: "entry ?blk 1 0 = entry N 1 ?j0N"
                    using w0 j0Nlt by (simp add: entry_seg)
                  have parhd0: "entry ?partial 0 0 = entry N 0 ?j0N" by (simp add: entry_seg)
                  have parhd1: "entry ?partial 1 0 = entry N 1 ?j0N" by (simp add: entry_seg)
                  have Ydesc: "descending ?Y"
                  proof (rule descending_const_head)
                    fix J assume "J < Lng ?Y"
                    hence Jlt: "J < ?qb + 1" by simp
                    show "entry (?Y ! J) 0 0 = entry N 0 ?j0N \<and> entry (?Y ! J) 1 0 = entry N 1 ?j0N"
                    proof (cases "J < ?qb")
                      case True
                      hence "?Y ! J = ?blk" by (simp add: nth_append)
                      thus ?thesis using blkhd0 blkhd1 by simp
                    next
                      case False
                      hence "J = ?qb" using Jlt by linarith
                      hence "?Y ! J = ?partial" by (simp add: nth_append)
                      thus ?thesis using parhd0 parhd1 by simp
                    qed
                  qed
                  show ?thesis
                  proof (cases "?a < ?j0N")
                    case asmall: True
                    \<comment> \<open>sub-case B, regime \<open>J\<^sub>1 \<ge> 1\<close> (\<open>a < j\<^sub>0\<^sup>N\<close>): the branch region of \<open>M'\<close> is
                       \<open>P(seg M a (j\<^sub>0\<^sup>N-1)) @ (replicate qb blk @ [partial])\<close>.  The LOW part is a
                       prefix of \<open>Br N'\<close> (N-side \<open>P\<close>-additive split at \<open>j\<^sub>0\<^sup>N\<close>, descending by
                       \<open>descending_take\<close>); the HIGH part is the block tail \<open>?Y\<close> (\<open>Ydesc\<close>);
                       junction by \<open>junc0\<close>.  Sub-case B requires \<open>j\<^sub>-\<^sub>1 \<le> TrMax(N')\<close>, i.e.
                       \<open>parent N 0 j\<^sub>0\<^sup>N < a\<close>, which makes \<open>j\<^sub>0\<^sup>N\<close> the left-minimal P-cut.\<close>
                    show ?thesis
                    proof (cases "parent ?Np 0 (?j0N - j0') \<le> TrMax ?Np")
                      case caseB: True
                      \<comment> \<open>sub-case B, \<open>J\<^sub>1 \<ge> 1\<close>.  CRUX (now proven): \<open>j\<^sub>0\<^sup>N\<close> is a left-minimal
                         row-0 P-cut of \<open>seg N a (Lng N-1)\<close>.  Its row-0 parent \<open>p\<close> exists
                         (\<open>m_5_1_parent_exists_1\<close> from \<open>entry N 0 j'\<^sub>0 < entry N 0 j\<^sub>0\<^sup>N\<close>), and the
                         N'-coordinate parent \<open>p - j'\<^sub>0 = parent N' 0 (j\<^sub>0\<^sup>N-j'\<^sub>0)\<close>
                         (\<open>adm_nextrel0_seg\<close> + uniqueness) is \<open>\<le> TrMax(N')\<close> by \<open>caseB\<close>, so
                         \<open>p \<le> j'\<^sub>0 + TrMax(N') = a-1 < a\<close>.  The \<open>nextrel0\<close> valley clause for
                         \<open>p \<rightarrow> j\<^sub>0\<^sup>N\<close> then gives \<open>entry N 0 j\<^sub>0\<^sup>N \<le> entry N 0 q\<close> for all \<open>q\<in>[a,j\<^sub>0\<^sup>N)\<close>.\<close>
                      have j0Nlt1: "?j0N < Lng N - 1" using parR0N by (simp add: nextrel0_def)
                      have j0Nle1: "?j0N \<le> Lng N - 1" using j0Nlt1 by simp
                      have e_lt: "entry N 0 j0' < entry N 0 ?j0N"
                        by (rule m_5_1_ancestor_basic_1[OF NT j0'lt0N j0Nle1 leRN])
                      obtain p where p: "j0' \<le> p" "p < ?j0N" "nextR N 0 p ?j0N"
                        using m_5_1_parent_exists_1[OF NT j0'lt0N j0NltN e_lt] by auto
                      have npr: "nextrel0 N p ?j0N" using p(3) by (simp add: nextR_def)
                      \<comment> \<open>shift the parent into \<open>N'\<close> coordinates and identify it via uniqueness\<close>
                      have pj0': "j0' + (p - j0') = p" using p(1) by simp
                      have j0Nj0': "j0' + (?j0N - j0') = ?j0N" using j0'lt0N by simp
                      have LN1ltN: "Lng N - 1 < Lng N" using j0NltN by linarith
                      have pNp: "p - j0' < Lng ?Np" using p(1) p(2) j0Nlt1 NpL by linarith
                      have j0NNp: "?j0N - j0' < Lng ?Np" using j0'lt0N j0Nlt1 NpL by linarith
                      have nprNp: "nextrel0 ?Np (p - j0') (?j0N - j0')"
                        using adm_nextrel0_seg[OF LN1ltN pNp j0NNp] npr pj0' j0Nj0' by simp
                      have nRNp: "nextR ?Np 0 (p - j0') (?j0N - j0')"
                        using nprNp by (simp add: nextR_def)
                      have ex1Np: "\<exists>!x. nextR ?Np 0 x (?j0N - j0')"
                        using nRNp idxsum_ex1_parent0_iff[of ?Np "?j0N - j0'"] by blast
                      \<comment> \<open>identify the outer \<open>parent\<close> via uniqueness; stash the inner index
                         \<open>?j0N - j0'\<close> in a fresh \<open>b\<close> so \<open>unfolding parent_def\<close> does not also
                         unfold the \<open>?j0N = parent N 0 (Lng N-1)\<close> hidden inside it\<close>
                      have parNp_eq: "parent ?Np 0 (?j0N - j0') = p - j0'"
                      proof -
                        obtain b where bdef: "?j0N - j0' = b" by blast
                        have nRb: "nextR ?Np 0 (p - j0') b" using nRNp bdef by simp
                        have ex1b: "\<exists>!x. nextR ?Np 0 x b" using ex1Np bdef by simp
                        have pb: "parent ?Np 0 b = p - j0'"
                          unfolding parent_def using nRb ex1b by (rule the1_equality[rotated])
                        show ?thesis using pb bdef by simp
                      qed
                      have plt_a: "p < ?a"
                      proof -
                        have "p - j0' \<le> TrMax ?Np" using caseB parNp_eq by simp
                        thus ?thesis using p(1) by linarith
                      qed
                      have leftmin: "\<And>q. ?a \<le> q \<Longrightarrow> q < ?j0N \<Longrightarrow> entry N 0 ?j0N \<le> entry N 0 q"
                      proof -
                        fix q assume "?a \<le> q" "q < ?j0N"
                        hence "p < q \<and> q < ?j0N" using plt_a by linarith
                        thus "entry N 0 ?j0N \<le> entry N 0 q" using npr by (simp add: nextrel0_def)
                      qed
                      \<comment> \<open>fold: \<open>Br M' = LOW @ HIGH\<close>, \<open>LOW = P(seg M a (j\<^sub>0\<^sup>N-1))\<close> (the prefix below
                         the cut, period intact), \<open>HIGH = ?Y = P(seg M j\<^sub>0\<^sup>N j'\<^sub>1)\<close> (\<open>hival\<close>).
                         The cut \<open>j\<^sub>0\<^sup>N\<close> is left-minimal in \<open>?X = seg M a j'\<^sub>1\<close> by \<open>leftmin\<close> + period
                         agreement (\<open>agree\<close>: \<open>M\<close> and \<open>N\<close> coincide on \<open>[0,j\<^sub>0\<^sup>N]\<close>).\<close>
                      let ?c = "?j0N - ?a"
                      let ?X = "seg M ?a j1'"
                      have aj1: "?a < j1'" using asmall j1Nge by linarith
                      have LngX: "Lng ?X = Suc j1' - ?a" by (rule Lng_seg)
                      have XT: "?X \<in> T_PS"
                      proof -
                        have "0 < Lng ?X" using LngX aj1 by linarith
                        hence "?X \<noteq> []" using length_greater_0_conv by blast
                        thus ?thesis by (simp add: T_PS_def)
                      qed
                      have c0: "0 < ?c" using asmall by linarith
                      have cle: "?c \<le> Lng ?X - 1" using LngX j1Nge asmall by linarith
                      have ac: "?a + ?c = ?j0N" using asmall by linarith
                      have axc: "?a + (Lng ?X - 1) = j1'" using LngX aj1 by linarith
                      have lminX: "\<And>j. j < ?c \<Longrightarrow> entry ?X 0 ?c \<le> entry ?X 0 j"
                      proof -
                        fix j assume jc: "j < ?c"
                        have jX: "j < Lng ?X" using jc cle by linarith
                        have cX: "?c < Lng ?X" using cle LngX aj1 by linarith
                        have aleq: "?a + j \<le> ?j0N" using jc by linarith
                        have eX_j: "entry ?X 0 j = entry N 0 (?a + j)"
                        proof -
                          have "?X ! j = M ! (?a + j)" by (rule seg_nth_eq) (use jX LngX in simp)
                          also have "M ! (?a + j) = N ! (?a + j)" using agree[OF aleq] .
                          finally have "?X ! j = N ! (?a + j)" .
                          thus ?thesis by (simp add: entry_def)
                        qed
                        have eX_c: "entry ?X 0 ?c = entry N 0 ?j0N"
                        proof -
                          have "?X ! ?c = M ! (?a + ?c)" by (rule seg_nth_eq) (use cX LngX in simp)
                          hence "?X ! ?c = M ! ?j0N" using ac by simp
                          also have "M ! ?j0N = N ! ?j0N" using agree[of ?j0N] by simp
                          finally have "?X ! ?c = N ! ?j0N" .
                          thus ?thesis by (simp add: entry_def)
                        qed
                        have "entry N 0 ?j0N \<le> entry N 0 (?a + j)"
                          using leftmin[of "?a + j"] jc by linarith
                        thus "entry ?X 0 ?c \<le> entry ?X 0 j" using eX_j eX_c by simp
                      qed
                      have Msplit: "P ?X = P (seg ?X 0 (?c - 1)) @ P (seg ?X ?c (Lng ?X - 1))"
                        by (rule m_6_2_P_additive[OF XT c0 cle lminX])
                      \<comment> \<open>hoist \<open>idx\<close>: needed by both segLOW (M-side) and segLOW_N (N-side, in Xdesc).
                         \<open>using c0 ac by linarith\<close> loops (\<open>?c\<close> double-expands the complex atoms
                         \<open>?j0N\<close>/\<open>?a\<close> with \<open>ac\<close> in scope); chain the \<open>c0\<close>-only assoc then \<open>ac\<close>
                         via \<open>also\<close>/\<open>finally\<close> (CLAUDE.md gotcha)\<close>
                      have idx: "?a + (?c - 1) = ?j0N - 1"
                      proof -
                        have "?a + (?c - 1) = ?a + ?c - 1" using c0 by linarith
                        also have "\<dots> = ?j0N - 1" using ac by simp
                        finally show ?thesis .
                      qed
                      have segLOW: "seg ?X 0 (?c - 1) = seg M ?a (?j0N - 1)"
                      proof -
                        have db: "?c - 1 \<le> j1' - ?a" using cle LngX by linarith
                        have "seg ?X 0 (?c - 1) = seg M (?a + 0) (?a + (?c - 1))"
                          by (rule seg_of_seg[OF less_imp_le[OF aj1] db])
                        also have "\<dots> = seg M ?a (?a + (?c - 1))" by simp
                        also have "\<dots> = seg M ?a (?j0N - 1)"
                          using arg_cong[OF idx, of "seg M ?a"] .
                        finally show ?thesis .
                      qed
                      have segHIGH: "seg ?X ?c (Lng ?X - 1) = seg M ?j0N j1'"
                      proof -
                        have db: "Lng ?X - 1 \<le> j1' - ?a" using LngX by linarith
                        have "seg ?X ?c (Lng ?X - 1) = seg M (?a + ?c) (?a + (Lng ?X - 1))"
                          by (rule seg_of_seg[OF less_imp_le[OF aj1] db])
                        also have "\<dots> = seg M ?j0N (?a + (Lng ?X - 1))"
                          using arg_cong[OF ac, of "\<lambda>x. seg M x (?a + (Lng ?X - 1))"] .
                        also have "\<dots> = seg M ?j0N j1'"
                          using arg_cong[OF axc, of "seg M ?j0N"] .
                        finally show ?thesis .
                      qed
                      have fold: "Br ?M' = P (seg M ?a (?j0N - 1)) @ ?Y"
                      proof -
                        have "Br ?M' = P (seg M ?a (?j0N - 1)) @ P (seg M ?j0N j1')"
                          using BrM'P Msplit segLOW segHIGH by simp
                        thus ?thesis using hival by simp
                      qed
                      \<comment> \<open>Xdesc: \<open>LOW = P(seg M a (j\<^sub>0\<^sup>N-1)) = take J\<^sub>1 (Br N')\<close>, descending by
                         \<open>descending_take[OF descN']\<close>.  N-side \<open>m_6_2_P_additive\<close> at the
                         same cut \<open>j\<^sub>0\<^sup>N\<close> (\<open>leftmin\<close> directly) + period agreement.\<close>
                      let ?Y' = "seg N ?a (Lng N - 1)"
                      have aLN1: "?a < Lng N - 1" using asmall j0Nlt1 by linarith
                      have aLN1_le: "?a \<le> Lng N - 1" using aLN1 by linarith
                      have LngY': "Lng ?Y' = Suc (Lng N - 1) - ?a" by (rule Lng_seg)
                      have Y'T: "?Y' \<in> T_PS"
                      proof -
                        have "0 < Lng ?Y'" using LngY' aLN1 by linarith
                        hence "?Y' \<noteq> []" using length_greater_0_conv by blast
                        thus ?thesis by (simp add: T_PS_def)
                      qed
                      have cle': "?c \<le> Lng ?Y' - 1" using LngY' j0Nlt1 by linarith
                      have axc': "?a + (Lng ?Y' - 1) = Lng N - 1" using LngY' aLN1 by linarith
                      have lminY': "\<And>j. j < ?c \<Longrightarrow> entry ?Y' 0 ?c \<le> entry ?Y' 0 j"
                      proof -
                        fix j assume jc: "j < ?c"
                        have jY': "j < Lng ?Y'" using jc cle' by linarith
                        have cY': "?c < Lng ?Y'" using cle' LngY' aLN1 by linarith
                        have eY'_j: "entry ?Y' 0 j = entry N 0 (?a + j)"
                        proof -
                          have "?Y' ! j = N ! (?a + j)" by (rule seg_nth_eq) (use jY' LngY' in simp)
                          thus ?thesis by (simp add: entry_def)
                        qed
                        have eY'_c: "entry ?Y' 0 ?c = entry N 0 ?j0N"
                        proof -
                          have "?Y' ! ?c = N ! (?a + ?c)" by (rule seg_nth_eq) (use cY' LngY' in simp)
                          hence "?Y' ! ?c = N ! ?j0N" using ac by simp
                          thus ?thesis by (simp add: entry_def)
                        qed
                        have "entry N 0 ?j0N \<le> entry N 0 (?a + j)"
                          using leftmin[of "?a + j"] jc by linarith
                        thus "entry ?Y' 0 ?c \<le> entry ?Y' 0 j" using eY'_j eY'_c by simp
                      qed
                      have Nsplit: "P ?Y' = P (seg ?Y' 0 (?c - 1)) @ P (seg ?Y' ?c (Lng ?Y' - 1))"
                        by (rule m_6_2_P_additive[OF Y'T c0 cle' lminY'])
                      have segLOW_N: "seg ?Y' 0 (?c - 1) = seg N ?a (?j0N - 1)"
                      proof -
                        have db: "?c - 1 \<le> Lng N - 1 - ?a" using cle' LngY' by linarith
                        have "seg ?Y' 0 (?c - 1) = seg N (?a + 0) (?a + (?c - 1))"
                          by (rule seg_of_seg[OF aLN1_le db])
                        also have "\<dots> = seg N ?a (?a + (?c - 1))" by simp
                        also have "\<dots> = seg N ?a (?j0N - 1)"
                          using arg_cong[OF idx, of "seg N ?a"] .
                        finally show ?thesis .
                      qed
                      have segHIGH_N: "seg ?Y' ?c (Lng ?Y' - 1) = seg N ?j0N (Lng N - 1)"
                      proof -
                        have db: "Lng ?Y' - 1 \<le> Lng N - 1 - ?a" using LngY' by linarith
                        have "seg ?Y' ?c (Lng ?Y' - 1) = seg N (?a + ?c) (?a + (Lng ?Y' - 1))"
                          by (rule seg_of_seg[OF aLN1_le db])
                        also have "\<dots> = seg N ?j0N (?a + (Lng ?Y' - 1))"
                          using arg_cong[OF ac, of "\<lambda>x. seg N x (?a + (Lng ?Y' - 1))"] .
                        also have "\<dots> = seg N ?j0N (Lng N - 1)"
                          using arg_cong[OF axc', of "seg N ?j0N"] .
                        finally show ?thesis .
                      qed
                      have NbrSplit: "Br ?Np = P (seg N ?a (?j0N - 1)) @ P (seg N ?j0N (Lng N - 1))"
                        using BrNpP Nsplit segLOW_N segHIGH_N by simp
                      \<comment> \<open>period agreement: \<open>M\<close> and \<open>N\<close> coincide on \<open>[?a, ?j0N-1]\<close> (\<open>\<le> ?j0N\<close>)\<close>
                      have segMN: "seg M ?a (?j0N - 1) = seg N ?a (?j0N - 1)"
                      proof (rule nth_equalityI)
                        show "length (seg M ?a (?j0N - 1)) = length (seg N ?a (?j0N - 1))" by simp
                        fix i assume "i < length (seg M ?a (?j0N - 1))"
                        hence ic: "i < Suc (?j0N - 1) - ?a" by simp
                        have aileq: "?a + i \<le> ?j0N" using ic c0 by linarith
                        have "seg M ?a (?j0N - 1) ! i = M ! (?a + i)"
                          by (rule seg_nth_eq) (use ic in simp)
                        also have "\<dots> = N ! (?a + i)" using agree[OF aileq] .
                        also have "\<dots> = seg N ?a (?j0N - 1) ! i"
                          by (rule seg_nth_eq[symmetric]) (use ic in simp)
                        finally show "seg M ?a (?j0N - 1) ! i = seg N ?a (?j0N - 1) ! i" .
                      qed
                      have Xdesc: "descending (P (seg M ?a (?j0N - 1)))"
                      proof -
                        have lowEq: "P (seg M ?a (?j0N - 1)) = P (seg N ?a (?j0N - 1))"
                          using segMN by simp
                        have takeEq: "P (seg N ?a (?j0N - 1))
                                    = take (length (P (seg N ?a (?j0N - 1)))) (Br ?Np)"
                          using NbrSplit by simp
                        from lowEq takeEq
                        have "P (seg M ?a (?j0N - 1))
                            = take (length (P (seg N ?a (?j0N - 1)))) (Br ?Np)" by simp
                        thus ?thesis using descending_take[OF descN'] by simp
                      qed
                      \<comment> \<open>junction \<open>cdom\<close>: \<open>cdom (last LOW) (?Y!0)\<close>.  Plan:
                         (i) \<open>NbrSplit\<close>: \<open>Br N' = LOWN @ HIGHN\<close> with \<open>LOWN = P(seg N a (j\<^sub>0\<^sup>N-1))\<close>
                         and \<open>HIGHN = P(seg N j\<^sub>0\<^sup>N (Lng N-1))\<close>;
                         (ii) \<open>descending_cdomD[OF descN']\<close>: \<open>cdom (Br N' ! (J\<^sub>1-1)) (Br N' ! J\<^sub>1)\<close>
                         where \<open>J\<^sub>1 = length LOWN\<close>;
                         (iii) \<open>last LOWN = Br N' ! (J\<^sub>1-1)\<close> and \<open>HIGHN!0 = Br N' ! J\<^sub>1\<close>;
                         (iv) heads of \<open>HIGHN!0\<close> and \<open>?Y!0\<close> are both \<open>(entry N 0 j\<^sub>0\<^sup>N, entry N 1 j\<^sub>0\<^sup>N)\<close>
                         (via \<open>m_6_4_P_IdxSum\<close>+\<open>entry_seg\<close> on the N-side, \<open>blkhd_/parhd_\<close> on the Y-side);
                         (v) \<open>cdom_def\<close> depends only on entry _ 0 0 and entry _ 1 0, so the
                         \<open>cdom\<close> transfers from \<open>HIGHN!0\<close> to \<open>?Y!0\<close>; \<open>segMN\<close> turns \<open>last LOWN\<close>
                         into \<open>last (P(seg M a (j\<^sub>0\<^sup>N-1)))\<close>.\<close>
                      have junc_cdom: "cdom (last (P (seg M ?a (?j0N - 1)))) (?Y ! 0)"
                      proof -
                        let ?LOWN = "P (seg N ?a (?j0N - 1))"
                        let ?HIGHN = "P (seg N ?j0N (Lng N - 1))"
                        let ?J1 = "length ?LOWN"
                        have LOWN_ne: "?LOWN \<noteq> []" by (rule P_nonempty)
                        have HIGHN_ne: "?HIGHN \<noteq> []" by (rule P_nonempty)
                        have J1pos: "0 < ?J1" using LOWN_ne by (cases ?LOWN) auto
                        have BrNp_eq: "Br ?Np = ?LOWN @ ?HIGHN" using NbrSplit .
                        \<comment> \<open>(iii) the junction indices land where expected\<close>
                        have last_low_low: "last ?LOWN = ?LOWN ! (?J1 - 1)"
                          using LOWN_ne by (rule last_conv_nth)
                        have lowJ1m1: "(?LOWN @ ?HIGHN) ! (?J1 - 1) = ?LOWN ! (?J1 - 1)"
                          using J1pos by (simp add: nth_append)
                        have high0_low: "(?LOWN @ ?HIGHN) ! ?J1 = ?HIGHN ! 0"
                          by (simp add: nth_append)
                        have last_low_eq: "last ?LOWN = Br ?Np ! (?J1 - 1)"
                          using last_low_low lowJ1m1 BrNp_eq by simp
                        have high0_eq: "?HIGHN ! 0 = Br ?Np ! ?J1"
                          using high0_low BrNp_eq by simp
                        \<comment> \<open>(ii) \<open>cdom\<close> from \<open>descN'\<close> on adjacent indices in \<open>Br N'\<close>\<close>
                        have J1_lt: "?J1 < Lng (Br ?Np)"
                          using HIGHN_ne BrNp_eq by simp
                        have cdomBr: "cdom (Br ?Np ! (?J1 - 1)) (Br ?Np ! ?J1)"
                          by (rule descending_cdomD[OF descN' diff_le_self J1_lt])
                        \<comment> \<open>(iv) heads of \<open>HIGHN!0\<close> are \<open>(entry N _ j\<^sub>0\<^sup>N)\<close>\<close>
                        let ?SN = "seg N ?j0N (Lng N - 1)"
                        have SNL: "Lng ?SN = Suc (Lng N - 1) - ?j0N" by (rule Lng_seg)
                        have SNpos: "0 < Lng ?SN" using SNL j0NltN by linarith
                        have SNne: "?SN \<noteq> []" using SNpos length_greater_0_conv by blast
                        have SNT: "?SN \<in> T_PS" using SNne by (simp add: T_PS_def)
                        have HIGHN_JL: "0 < length ?HIGHN"
                          using HIGHN_ne by (cases ?HIGHN) auto
                        have HIGHN0_len_pos: "0 < Lng (?HIGHN ! 0)"
                          by (rule idxsum_P_component_nonempty[OF SNT HIGHN_JL])
                        have HIGHN_Jle: "(0::nat) \<le> Lng ?HIGHN - 1"
                          using HIGHN_ne by (cases ?HIGHN) auto
                        have HIGHN0_seg:
                          "?HIGHN ! 0 = seg ?SN (IdxSum ?HIGHN ! 0) (IdxSum ?HIGHN ! 1 - 1)"
                          using m_6_4_P_IdxSum[OF SNT HIGHN_Jle] by simp
                        have idx0: "IdxSum ?HIGHN ! 0 = 0" by (simp add: idxsum_nth)
                        have HIGHN0_lp:
                          "0 < Lng (seg ?SN (IdxSum ?HIGHN ! 0) (IdxSum ?HIGHN ! 1 - 1))"
                        proof -
                          have "Lng (?HIGHN ! 0)
                                = Lng (seg ?SN (IdxSum ?HIGHN ! 0) (IdxSum ?HIGHN ! 1 - 1))"
                            using HIGHN0_seg by simp
                          thus ?thesis using HIGHN0_len_pos by simp
                        qed
                        have H0hd0: "entry (?HIGHN ! 0) 0 0 = entry N 0 ?j0N"
                        proof -
                          have step1: "entry (?HIGHN ! 0) 0 0
                                       = entry (seg ?SN (IdxSum ?HIGHN ! 0) (IdxSum ?HIGHN ! 1 - 1)) 0 0"
                            using HIGHN0_seg by simp
                          have step2: "entry (seg ?SN (IdxSum ?HIGHN ! 0) (IdxSum ?HIGHN ! 1 - 1)) 0 0
                                       = entry ?SN 0 (IdxSum ?HIGHN ! 0 + 0)"
                            by (rule entry_seg[OF HIGHN0_lp])
                          have step3: "entry ?SN 0 (IdxSum ?HIGHN ! 0 + 0) = entry ?SN 0 0"
                            by (simp only: idx0 add_0)
                          have step4: "entry ?SN 0 0 = entry N 0 (?j0N + 0)"
                            by (rule entry_seg) (use SNpos in simp)
                          have step5: "entry N 0 (?j0N + 0) = entry N 0 ?j0N" by simp
                          from step1 step2 step3 step4 step5 show ?thesis by simp
                        qed
                        have H0hd1: "entry (?HIGHN ! 0) 1 0 = entry N 1 ?j0N"
                        proof -
                          have step1: "entry (?HIGHN ! 0) 1 0
                                       = entry (seg ?SN (IdxSum ?HIGHN ! 0) (IdxSum ?HIGHN ! 1 - 1)) 1 0"
                            using HIGHN0_seg by simp
                          have step2: "entry (seg ?SN (IdxSum ?HIGHN ! 0) (IdxSum ?HIGHN ! 1 - 1)) 1 0
                                       = entry ?SN 1 (IdxSum ?HIGHN ! 0 + 0)"
                            by (rule entry_seg[OF HIGHN0_lp])
                          have step3: "entry ?SN 1 (IdxSum ?HIGHN ! 0 + 0) = entry ?SN 1 0"
                            by (simp only: idx0 add_0)
                          have step4: "entry ?SN 1 0 = entry N 1 (?j0N + 0)"
                            by (rule entry_seg) (use SNpos in simp)
                          have step5: "entry N 1 (?j0N + 0) = entry N 1 ?j0N" by simp
                          from step1 step2 step3 step4 step5 show ?thesis by simp
                        qed
                        \<comment> \<open>heads of \<open>?Y!0\<close> are also \<open>(entry N _ j\<^sub>0\<^sup>N)\<close>\<close>
                        have Y0hd0: "entry (?Y ! 0) 0 0 = entry N 0 ?j0N"
                        proof (cases "?qb = 0")
                          case True hence "?Y ! 0 = ?partial" by simp
                            thus ?thesis using parhd0 by simp
                        next
                          case False hence "?Y ! 0 = ?blk" by (simp add: nth_append)
                            thus ?thesis using blkhd0 by simp
                        qed
                        have Y0hd1: "entry (?Y ! 0) 1 0 = entry N 1 ?j0N"
                        proof (cases "?qb = 0")
                          case True hence "?Y ! 0 = ?partial" by simp
                            thus ?thesis using parhd1 by simp
                        next
                          case False hence "?Y ! 0 = ?blk" by (simp add: nth_append)
                            thus ?thesis using blkhd1 by simp
                        qed
                        \<comment> \<open>(v) transfer \<open>cdom\<close> from \<open>HIGHN!0\<close> to \<open>?Y!0\<close> via same heads;
                           \<open>segMN\<close> swaps \<open>M\<close> for \<open>N\<close> in the \<open>last (P ...)\<close>\<close>
                        have lastM_eq: "last (P (seg M ?a (?j0N - 1))) = last ?LOWN"
                          using segMN by simp
                        have key: "cdom (last ?LOWN) (?HIGHN ! 0)"
                          using cdomBr last_low_eq high0_eq by simp
                        from key have row0: "entry (?HIGHN ! 0) 0 0 \<le> entry (last ?LOWN) 0 0"
                          and row1cond: "entry (last ?LOWN) 0 0 = entry (?HIGHN ! 0) 0 0
                                          \<longrightarrow> entry (?HIGHN ! 0) 1 0 \<le> entry (last ?LOWN) 1 0"
                          unfolding cdom_def by auto
                        show ?thesis
                          unfolding cdom_def
                        proof (intro conjI impI)
                          show "entry (?Y ! 0) 0 0 \<le> entry (last (P (seg M ?a (?j0N - 1)))) 0 0"
                            using row0 H0hd0 Y0hd0 lastM_eq by simp
                          assume eq0: "entry (last (P (seg M ?a (?j0N - 1)))) 0 0 = entry (?Y ! 0) 0 0"
                          hence "entry (last ?LOWN) 0 0 = entry (?HIGHN ! 0) 0 0"
                            using H0hd0 Y0hd0 lastM_eq by simp
                          hence "entry (?HIGHN ! 0) 1 0 \<le> entry (last ?LOWN) 1 0"
                            using row1cond by simp
                          thus "entry (?Y ! 0) 1 0 \<le> entry (last (P (seg M ?a (?j0N - 1)))) 1 0"
                            using H0hd1 Y0hd1 lastM_eq by simp
                        qed
                      qed
                      show ?thesis
                        using descending_append[OF Xdesc Ydesc] junc_cdom fold by simp
                    next
                      case caseC: False
                      \<comment> \<open>sub-case C (article 1496-1500): \<open>TrMax(N') < j\<^sub>-\<^sub>1\<close>; \<open>j\<^sub>0\<^sup>N\<close>'s row-0
                         parent lies in the branch.  \<open>Br M' = take J\<^sub>1 (Br N') @ [tail]\<close>
                         with \<open>tail = seg M (FN\<^bsub>J\<^sub>1\<^esub>+j'\<^sub>0) j'\<^sub>1\<close>; the tail head equals
                         \<open>(Br N'\<^bsub>J\<^sub>1\<^esub>)\<^bsub>0\<^esub>\<close>, so \<open>Br M'\<close> shares \<open>Br N'\<close>'s descending head sequence.\<close>
                      have j0Nlt1: "?j0N < Lng N - 1" using j0Nlt by simp
                      \<comment> \<open>\<open>?Np \<in> PT_PS\<close>\<close>
                      have monoNp: "monoT ?Np"
                        using m_6_2_mono_ancestor_slice[OF NT _ leRN] j0'lt1N by simp
                      have NpPT: "?Np \<in> PT_PS" using NpT monoNp by (simp add: PT_PS_def)
                      \<comment> \<open>\<open>J\<^sub>1 = Lng (Br N') - 1\<close>, the last branch component index\<close>
                      let ?J1 = "Lng (Br ?Np) - 1"
                      have J1L: "?J1 < length (Br ?Np)" using BrNpne by (cases "Br ?Np") auto
                      \<comment> \<open>\<open>?fn = FirstNodes(N')\<^bsub>J\<^sub>1\<^esub>\<close> (N' coords), \<open>?fnM = j'\<^sub>0 + ?fn\<close> (M/N coords)\<close>
                      let ?fn = "FirstNodes ?Np ! ?J1"
                      let ?fnM = "j0' + ?fn"
                      have fnval: "?fn = TrMax ?Np + 1 + IdxSum (Br ?Np) ! ?J1"
                        by (rule FirstNodes_nth[OF J1L])
                      \<comment> \<open>\<open>?a \<le> ?fnM\<close>: \<open>?fn \<ge> TrMax(N')+1\<close>, \<open>?a = j'\<^sub>0+TrMax(N')+1\<close>\<close>
                      have a_le_fnM: "?a \<le> ?fnM" using fnval by simp
                      \<comment> \<open>\<open>?fnM < ?j0N\<close> (article 1500): \<open>FN\<^bsub>J\<^sub>1\<^esub> \<le> j\<^sub>-\<^sub>1 < j\<^sub>0\<^sup>N - j'\<^sub>0\<close>.
                         \<open>j\<^sub>-\<^sub>1 = parent N' 0 (j\<^sub>0\<^sup>N-j'\<^sub>0)\<close> and \<open>caseC\<close>: \<open>TrMax(N') < j\<^sub>-\<^sub>1\<close>;
                         \<open>FN\<^bsub>J\<^sub>1\<^esub>\<close> is the last row-0 left-minimum of the branch region.\<close>
                      let ?jm1 = "parent ?Np 0 (?j0N - j0')"
                      have j0Npos: "0 < ?j0N - j0'" using j0'lt0N by linarith
                      have j0Ng: "?j0N - j0' < Lng ?Np" using j0'lt0N j0Nlt1 NpL by linarith
                      \<comment> \<open>\<open>le0 N' 0 (j\<^sub>0\<^sup>N-j'\<^sub>0)\<close> by transferring \<open>le0Nj0\<close> across the slice\<close>
                      have LN1ltN: "Lng N - 1 < Lng N" using j0NltN by linarith
                      have bsmall: "?j0N - j0' \<le> Lng N - 1 - j0'" using j0Nlt1 by linarith
                      have le0Np: "le0 ?Np 0 (?j0N - j0')"
                      proof -
                        have "le0 ?Np 0 (?j0N - j0')
                            = le0 N (j0' + 0) (j0' + (?j0N - j0'))"
                          by (rule adm_le0_seg[where M=N and j0'=j0' and j1'="Lng N - 1"
                                and a=0 and b="?j0N - j0'", OF LN1ltN _ bsmall])
                             (use j0'lt1N in auto)
                        also have "j0' + 0 = j0'" by simp
                        also have "j0' + (?j0N - j0') = ?j0N" using j0'lt0N by simp
                        finally show ?thesis using le0Nj0 by simp
                      qed
                      have leRNp: "leR ?Np 0 0 (?j0N - j0')" using le0Np by (simp add: leR_def)
                      have e_lt: "entry ?Np 0 0 < entry ?Np 0 (?j0N - j0')"
                        by (rule m_5_1_ancestor_basic_1[OF NpT j0Npos order.refl leRNp])
                      obtain p where p: "nextR ?Np 0 p (?j0N - j0')"
                        using m_5_1_parent_exists_1[OF NpT j0Npos j0Ng e_lt] by blast
                      have ex1: "\<exists>!x. nextR ?Np 0 x (?j0N - j0')"
                        using p idxsum_ex1_parent0_iff by metis
                      have jm1eq: "?jm1 = p"
                      proof -
                        obtain b where bdef: "?j0N - j0' = b" by blast
                        have pb: "nextR ?Np 0 p b" using p bdef by simp
                        have ex1b: "\<exists>!x. nextR ?Np 0 x b" using ex1 bdef by simp
                        have "parent ?Np 0 b = p"
                          unfolding parent_def using pb ex1b by (rule the1_equality[rotated])
                        thus ?thesis using bdef by simp
                      qed
                      have jm1lt: "?jm1 < ?j0N - j0'"
                        using jm1eq p by (simp add: nextR_def nextrel0_def)
                      have caseC': "TrMax ?Np < ?jm1" using caseC by linarith
                      \<comment> \<open>leaf parent: \<open>(0, j\<^sub>0\<^sup>N-j'\<^sub>0) <\<^sub>N\<^sub>'\<^sup>Next (0, Lng N'-1)\<close> (article 1482),
                         transferring \<open>parR0N\<close> across the slice\<close>
                      have leafidx: "Lng ?Np - 1 < Lng ?Np" using NpLgt by linarith
                      have nleaf: "nextrel0 ?Np (?j0N - j0') (Lng ?Np - 1)"
                      proof -
                        have e1: "?j0N - j0' < Lng ?Np" using j0Ng .
                        have shiftL: "j0' + (Lng ?Np - 1) = Lng N - 1" using NpL j0'lt1N by linarith
                        have shiftJ: "j0' + (?j0N - j0') = ?j0N" using j0'lt0N by simp
                        have "nextrel0 ?Np (?j0N - j0') (Lng ?Np - 1)
                            = nextrel0 N (j0' + (?j0N - j0')) (j0' + (Lng ?Np - 1))"
                          by (rule adm_nextrel0_seg[OF LN1ltN e1 leafidx])
                        also have "\<dots> = nextrel0 N ?j0N (Lng N - 1)"
                          using shiftL shiftJ by simp
                        finally show ?thesis using parR0N by simp
                      qed
                      \<comment> \<open>STEP 1 (article 1498): \<open>FN\<^bsub>J\<^sub>1\<^esub> \<le> j\<^sub>-\<^sub>1\<close>, hence \<open>?fnM < ?j0N\<close>.\<close>
                      \<comment> \<open>the last branch component is \<open>seg ?Np ?fn (Lng ?Np-1)\<close>\<close>
                      let ?S = "seg ?Np (TrMax ?Np + 1) (Lng ?Np - 1)"
                      have trNpne: "TrMax ?Np \<noteq> Lng ?Np - 1" using TrNplt by simp
                      have brQ: "Br ?Np = P ?S" using trNpne by (simp add: Br_def)
                      have ST: "?S \<in> T_PS"
                      proof -
                        have "0 < Lng ?S" using TrNplt by simp
                        thus ?thesis using length_greater_0_conv by (fastforce simp: T_PS_def)
                      qed
                      have J1Br: "?J1 < length (Br ?Np)" using J1L by simp
                      have J1leQ: "?J1 \<le> Lng (P ?S) - 1" using J1Br brQ by (cases "P ?S") auto
                      have lenS: "Lng ?S = Lng ?Np - 1 - TrMax ?Np" using TrNplt by simp
                      \<comment> \<open>\<open>IdxSum (Br ?Np) ! (?J1+1) = Lng ?S\<close> (total length)\<close>
                      have BrNpne': "length (Br ?Np) = Suc ?J1" using BrNpne by (cases "Br ?Np") auto
                      have idxtot: "IdxSum (Br ?Np) ! (?J1 + 1) = Lng ?S"
                      proof -
                        have "?J1 + 1 = length (Br ?Np)" using BrNpne' by simp
                        hence "IdxSum (Br ?Np) ! (?J1 + 1) = sum_list (map length (Br ?Np))"
                          by (simp add: idxsum_nth)
                        also have "\<dots> = length (concat (Br ?Np))" by (simp add: length_concat)
                        also have "concat (Br ?Np) = ?S" using brQ idxsum_concat_P by simp
                        finally show ?thesis by simp
                      qed
                      have idxJ1: "IdxSum (Br ?Np) ! ?J1 = ?fn - (TrMax ?Np + 1)"
                        using fnval by simp
                      have fnge: "TrMax ?Np + 1 \<le> ?fn" using fnval by simp
                      \<comment> \<open>\<open>Br ?Np ! ?J1 = seg ?Np ?fn (Lng ?Np-1)\<close> via \<open>m_6_4_P_IdxSum\<close> + \<open>seg_of_seg\<close>\<close>
                      have compS: "Br ?Np ! ?J1
                          = seg ?S (IdxSum (Br ?Np) ! ?J1) (IdxSum (Br ?Np) ! (?J1 + 1) - 1)"
                        using m_6_4_P_IdxSum[OF ST J1leQ] brQ by simp
                      have idxJ1le: "IdxSum (Br ?Np) ! ?J1 \<le> Lng ?S - 1"
                        using idxsum_leftend_lmin[OF ST J1Br[unfolded brQ]] brQ by simp
                      have comp_eq: "Br ?Np ! ?J1 = seg ?Np ?fn (Lng ?Np - 1)"
                      proof -
                        have ab': "TrMax ?Np + 1 \<le> Lng ?Np - 1" using TrNplt by linarith
                        have hi: "IdxSum (Br ?Np) ! (?J1 + 1) - 1
                                  \<le> (Lng ?Np - 1) - (TrMax ?Np + 1)"
                          using idxtot lenS by linarith
                        have "seg ?S (IdxSum (Br ?Np) ! ?J1) (IdxSum (Br ?Np) ! (?J1 + 1) - 1)
                            = seg ?Np ((TrMax ?Np + 1) + IdxSum (Br ?Np) ! ?J1)
                                       ((TrMax ?Np + 1) + (IdxSum (Br ?Np) ! (?J1 + 1) - 1))"
                          by (rule seg_of_seg[OF ab' hi])
                        also have "(TrMax ?Np + 1) + IdxSum (Br ?Np) ! ?J1 = ?fn"
                          using idxJ1 fnge by simp
                        also have "(TrMax ?Np + 1) + (IdxSum (Br ?Np) ! (?J1 + 1) - 1) = Lng ?Np - 1"
                          using idxtot lenS TrNplt by linarith
                        finally show ?thesis using compS by simp
                      qed
                      \<comment> \<open>the component is non-multi (each \<open>P\<close>-component) and non-empty\<close>
                      have compne: "0 < Lng (Br ?Np ! ?J1)"
                        using idxsum_P_component_nonempty[OF ST J1Br[unfolded brQ]] brQ by simp
                      have compNT: "Br ?Np ! ?J1 \<in> T_PS"
                        using compne length_greater_0_conv by (fastforce simp: T_PS_def)
                      have compnm: "\<not> multiT (Br ?Np ! ?J1)"
                        using m_6_2_P_components_1[OF ST] brQ J1Br[unfolded brQ]
                        by (auto simp: multiT_def)
                      \<comment> \<open>\<open>?fn < Lng ?Np - 1\<close>: else the last component is the single leaf, whose
                         row-0 parent would be \<open>\<le> TrMax\<close>, contradicting \<open>nleaf\<close>+\<open>BClt\<close>\<close>
                      have parent_fn: "parent ?Np 0 ?fn \<le> TrMax ?Np"
                      proof -
                        have "Joints ?Np ! ?J1 = parent ?Np 0 ?fn"
                          by (rule Joints_nth[OF J1Br])
                        thus ?thesis using m_6_4_FirstNodes_TrMax_Joints[OF NpPT J1Br] by simp
                      qed
                      have fnLng: "?fn < Lng ?Np - 1"
                      proof (rule ccontr)
                        assume "\<not> ?fn < Lng ?Np - 1"
                        moreover have "?fn \<le> Lng ?Np - 1"
                          using comp_eq compne by (cases "?fn \<le> Lng ?Np - 1") auto
                        ultimately have feq: "?fn = Lng ?Np - 1" by linarith
                        \<comment> \<open>then \<open>?j0N-j0'\<close> is the row-0 parent of \<open>?fn=leaf\<close>; uniqueness vs \<open>parent_fn\<close>\<close>
                        have fnIdx: "?fn = (TrMax ?Np + 1) + IdxSum (Br ?Np) ! ?J1"
                          using fnval by simp
                        have p1: "(0::nat) < TrMax ?Np + 1" by simp
                        have p2: "TrMax ?Np + 1 \<le> Lng ?Np - 1" using TrNplt by linarith
                        have slnext: "hasParent ?Np 0
                            ((TrMax ?Np + 1) + IdxSum (P (seg ?Np (TrMax ?Np + 1) (Lng ?Np - 1))) ! ?J1)"
                          using m_6_4_mono_slice_next[OF NpPT p1 p2 J1leQ] by simp
                        have hpfn: "hasParent ?Np 0 ?fn"
                          using slnext fnIdx brQ by simp
                        have nfn: "nextR ?Np 0 (parent ?Np 0 ?fn) ?fn"
                        proof -
                          have "\<exists>!x. nextR ?Np 0 x ?fn" using hpfn by (simp add: hasParent_def)
                          thus ?thesis unfolding parent_def by (rule theI')
                        qed
                        have nfn': "nextR ?Np 0 (?j0N - j0') ?fn"
                          using nleaf feq by (simp add: nextR_def)
                        have "parent ?Np 0 ?fn = ?j0N - j0'"
                          using idxsum_parent0_unique[OF nfn nfn'] .
                        thus False using parent_fn BClt by linarith
                      qed
                      \<comment> \<open>\<open>FN\<^sub>J\<^sub>1\<close> strictly row-0-dominates every other component member\<close>
                      have compdom: "\<And>q. ?fn < q \<Longrightarrow> q \<le> Lng ?Np - 1
                                      \<Longrightarrow> entry ?Np 0 ?fn < entry ?Np 0 q"
                      proof -
                        fix q assume q1: "?fn < q" and q2: "q \<le> Lng ?Np - 1"
                        let ?C = "Br ?Np ! ?J1"
                        have LC: "Lng ?C = Suc (Lng ?Np - 1) - ?fn"
                          using comp_eq by (simp only: Lng_seg)
                        have crit: "\<forall>j. 0 < j \<and> j < Lng ?C
                                      \<longrightarrow> entry ?C 0 0 < entry ?C 0 j"
                          using m_6_2_multi_crit_12[OF compNT] compnm by blast
                        let ?j = "q - ?fn"
                        have jpos: "0 < ?j" using q1 by simp
                        have jlt: "?j < Lng ?C" using LC q1 q2 by linarith
                        have e0: "entry ?C 0 0 = entry ?Np 0 ?fn"
                          using comp_eq compne by (simp add: entry_seg)
                        have ej: "entry ?C 0 ?j = entry ?Np 0 q"
                        proof -
                          have "entry ?C 0 ?j = entry ?Np 0 (?fn + ?j)"
                            using comp_eq jlt LC by (simp add: entry_seg)
                          thus ?thesis using q1 by simp
                        qed
                        have "entry ?C 0 0 < entry ?C 0 ?j" using crit jpos jlt by blast
                        thus "entry ?Np 0 ?fn < entry ?Np 0 q" using e0 ej by simp
                      qed
                      \<comment> \<open>\<open>?fn \<le> ?j0N-j0'\<close> from \<open>nleaf\<close> (\<open>?j0N-j0'\<close> is the parent of the leaf)\<close>
                      have fn_le_d: "?fn \<le> ?j0N - j0'"
                      proof -
                        have nleafR: "nextR ?Np 0 (?j0N - j0') (Lng ?Np - 1)"
                          using nleaf by (simp add: nextR_def)
                        have edom: "entry ?Np 0 ?fn < entry ?Np 0 (Lng ?Np - 1)"
                          using compdom[OF fnLng] by simp
                        show ?thesis
                          by (rule nextR0_largest_below[OF nleafR fnLng edom])
                      qed
                      \<comment> \<open>\<open>?fn \<noteq> ?j0N-j0'\<close>: their row-0 parents differ (\<open>\<le> TrMax\<close> vs \<open>?jm1 > TrMax\<close>)\<close>
                      have fn_ne_d: "?fn \<noteq> ?j0N - j0'"
                      proof
                        assume "?fn = ?j0N - j0'"
                        hence "parent ?Np 0 (?j0N - j0') \<le> TrMax ?Np" using parent_fn by simp
                        thus False using jm1eq caseC' by simp
                      qed
                      have fn_lt_d: "?fn < ?j0N - j0'" using fn_le_d fn_ne_d by linarith
                      \<comment> \<open>\<open>?fn \<le> ?jm1\<close> from \<open>p\<close> (\<open>?jm1\<close> is the parent of \<open>?j0N-j0'\<close>)\<close>
                      have fn_le_jm1: "?fn \<le> ?jm1"
                      proof -
                        have pR: "nextR ?Np 0 ?jm1 (?j0N - j0')" using jm1eq p by simp
                        have edom2: "entry ?Np 0 ?fn < entry ?Np 0 (?j0N - j0')"
                          using compdom[OF fn_lt_d] j0Ng by simp
                        show ?thesis
                          by (rule nextR0_largest_below[OF pR fn_lt_d edom2])
                      qed
                      have fnM_lt: "?fnM < ?j0N"
                        using fn_le_jm1 jm1lt j0'lt0N by linarith
                      \<comment> \<open>STEP 2 (article 1498): the tail \<open>seg M ?fnM j'\<^sub>1\<close> is a single
                         non-multi \<open>P\<close>-component, i.e. \<open>?fnM\<close> row-0-strictly-dominates
                         the whole tail (crossing the oper boundary at \<open>?j0N\<close>).\<close>
                      \<comment> \<open>N-side domination from \<open>compdom\<close>, translated by \<open>entry_seg\<close>\<close>
                      have Ndom: "\<And>q. ?fnM < q \<Longrightarrow> q \<le> Lng N - 1
                                    \<Longrightarrow> entry N 0 ?fnM < entry N 0 q"
                      proof -
                        fix q assume q1: "?fnM < q" and q2: "q \<le> Lng N - 1"
                        have qj0': "j0' \<le> q" using q1 by simp
                        have qLng: "q - j0' \<le> Lng ?Np - 1" using q2 NpL by linarith
                        have fnNp: "?fn < q - j0'" using q1 by simp
                        have efn: "entry N 0 ?fnM = entry ?Np 0 ?fn"
                        proof -
                          have "?fn < Lng ?Np" using fnLng by linarith
                          thus ?thesis by (simp add: entry_seg)
                        qed
                        have eq': "entry N 0 q = entry ?Np 0 (q - j0')"
                        proof -
                          have "q - j0' < Lng ?Np" using qLng TrNplt by linarith
                          hence "entry ?Np 0 (q - j0') = entry N 0 (j0' + (q - j0'))"
                            by (simp add: entry_seg)
                          thus ?thesis using qj0' by simp
                        qed
                        have "entry ?Np 0 ?fn < entry ?Np 0 (q - j0')"
                          using compdom[OF fnNp qLng] .
                        thus "entry N 0 ?fnM < entry N 0 q" using efn eq' by simp
                      qed
                      \<comment> \<open>\<open>entry M 0 ?fnM = entry N 0 ?fnM\<close> (\<open>?fnM < ?j0N\<close>, agree)\<close>
                      have efnM_MN: "entry M 0 ?fnM = entry N 0 ?fnM"
                        using agree[of ?fnM] fnM_lt by (simp add: entry_def)
                      \<comment> \<open>strict row-0 domination of \<open>?fnM\<close> over the whole tail \<open>(?fnM, j'\<^sub>1]\<close> in \<open>M\<close>\<close>
                      have Mdom: "\<And>q. ?fnM < q \<Longrightarrow> q \<le> j1'
                                    \<Longrightarrow> entry M 0 ?fnM < entry M 0 q"
                      proof -
                        fix q assume q1: "?fnM < q" and q2: "q \<le> j1'"
                        show "entry M 0 ?fnM < entry M 0 q"
                        proof (cases "q \<le> ?j0N")
                          case low: True
                          have qN: "q \<le> Lng N - 1" using low j0NltN by linarith
                          have "entry M 0 q = entry N 0 q"
                            using agree[of q] low by (simp add: entry_def)
                          thus ?thesis using Ndom[OF q1 qN] efnM_MN by simp
                        next
                          case high: False
                          \<comment> \<open>\<open>q > ?j0N\<close>: \<open>entry M 0 q \<ge> entry N 0 ?j0N > entry N 0 ?fnM\<close>\<close>
                          have qge: "?j0N \<le> q" using high by linarith
                          have qlt: "q < ?j0N + n * ?w" using q2 j1 lt LngM by linarith
                          have eblk: "entry N 0 ?j0N \<le> entry M 0 q"
                            using oper_d0zero_entry0_min[OF LNgt notzeroN hasparN i1zN j0Nlt qge qlt]
                                  Neq by simp
                          have fnj0N: "entry N 0 ?fnM < entry N 0 ?j0N"
                            using Ndom[OF fnM_lt] j0NltN by simp
                          show ?thesis using eblk fnj0N efnM_MN by simp
                        qed
                      qed
                      \<comment> \<open>hence the tail is non-multi, so a single \<open>P\<close>-component\<close>
                      let ?TL = "seg M ?fnM j1'"
                      have fnMj1: "?fnM < j1'" using fnM_lt j1Nge by linarith
                      have LngTL: "Lng ?TL = Suc j1' - ?fnM" by (rule Lng_seg)
                      have TLT: "?TL \<in> T_PS"
                      proof -
                        have "0 < Lng ?TL" using LngTL fnMj1 by linarith
                        thus ?thesis using length_greater_0_conv by (fastforce simp: T_PS_def)
                      qed
                      have hitail: "P ?TL = [?TL]"
                      proof (rule poper_P_nonmulti)
                        show "\<not> (multiT ?TL \<and> 1 < Lng ?TL)"
                        proof (cases "1 < Lng ?TL")
                          case False thus ?thesis by simp
                        next
                          case True
                          have crit: "\<forall>j. 0 < j \<and> j < Lng ?TL
                                        \<longrightarrow> entry ?TL 0 0 < entry ?TL 0 j"
                          proof (intro allI impI)
                            fix j assume j: "0 < j \<and> j < Lng ?TL"
                            have e0: "entry ?TL 0 0 = entry M 0 ?fnM"
                              using True by (simp add: entry_seg)
                            have ej: "entry ?TL 0 j = entry M 0 (?fnM + j)"
                              using j LngTL by (simp add: entry_seg)
                            have q1: "?fnM < ?fnM + j" using j by simp
                            have q2: "?fnM + j \<le> j1'" using j LngTL by linarith
                            show "entry ?TL 0 0 < entry ?TL 0 j"
                              using Mdom[OF q1 q2] e0 ej by simp
                          qed
                          have "\<not> multiT ?TL"
                            using m_6_2_multi_crit_12[OF TLT] crit by blast
                          thus ?thesis by simp
                        qed
                      qed
                      show ?thesis
                      proof (cases "?J1 = 0")
                        case J1z: True
                        \<comment> \<open>only one branch component: \<open>?a = ?fnM\<close>, \<open>Br M' = [?TL]\<close>\<close>
                        have idxz: "IdxSum (Br ?Np) ! ?J1 = 0" using J1z by (simp add: idxsum_nth)
                        have aeqfn: "?fnM = ?a" using idxJ1 idxz a_le_fnM fnval by simp
                        have "Br ?M' = P (seg M ?fnM j1')"
                          using BrM'P arg_cong[OF aeqfn, of "\<lambda>x. P (seg M x j1')"] by simp
                        hence "Br ?M' = [?TL]" using hitail by simp
                        thus ?thesis by (simp add: descending_def)
                      next
                        case J1pos: False
                      \<comment> \<open>STEP 3 (article 1498): \<open>LOW = P(seg M ?a (?fnM-1)) = take J\<^sub>1 (Br N')\<close>.
                         N-side \<open>P\<close>-additive split of \<open>Br N' = P(seg N ?a (Lng N-1))\<close> at \<open>?fnM\<close>;
                         the HIGH part is the single last component \<open>seg N ?fnM (Lng N-1)\<close>.\<close>
                      let ?Yn = "seg N ?a (Lng N - 1)"
                      have aLN1: "?a < Lng N - 1" using a_le_fnM fnM_lt j0NltN by linarith
                      have aLN1_le: "?a \<le> Lng N - 1" using aLN1 by linarith
                      have LngYn: "Lng ?Yn = Suc (Lng N - 1) - ?a" by (rule Lng_seg)
                      have YnT: "?Yn \<in> T_PS"
                      proof -
                        have "0 < Lng ?Yn" using LngYn aLN1 by linarith
                        thus ?thesis using length_greater_0_conv by (fastforce simp: T_PS_def)
                      qed
                      let ?cn = "?fnM - ?a"
                      have idxJ1pos: "0 < IdxSum (Br ?Np) ! ?J1"
                      proof -
                        have "IdxSum (Br ?Np) ! ?J1 = sum_list (map length (take ?J1 (Br ?Np)))"
                          using J1Br by (simp add: idxsum_nth)
                        moreover have "take ?J1 (Br ?Np) \<noteq> []" using J1pos J1Br by auto
                        moreover have "\<And>C. C \<in> set (take ?J1 (Br ?Np)) \<Longrightarrow> 0 < length C"
                          using idxsum_P_component_nonempty[OF ST] brQ
                          by (metis in_set_conv_nth length_take min.absorb4 nth_take
                              set_take_subset subsetD)
                        ultimately show ?thesis
                          by (cases "take ?J1 (Br ?Np)") (auto simp: sum_list_eq_0_iff)
                      qed
                      have cn0: "0 < ?cn" using idxJ1 idxJ1pos a_le_fnM fnval by simp
                      have fnM_le1: "?fnM \<le> Lng N - 1" using fnM_lt j0NltN by linarith
                      have cnle: "?cn \<le> Lng ?Yn - 1" using LngYn fnM_le1 a_le_fnM by linarith
                      have acn: "?a + ?cn = ?fnM" using a_le_fnM by simp
                      have axcn: "?a + (Lng ?Yn - 1) = Lng N - 1" using LngYn aLN1 by linarith
                      \<comment> \<open>left-minimality of \<open>?fnM\<close> within \<open>[?a, ?fnM)\<close> (last-component left-end)\<close>
                      have lminLOW: "\<And>q. ?a \<le> q \<Longrightarrow> q < ?fnM \<Longrightarrow> entry N 0 ?fnM \<le> entry N 0 q"
                      proof -
                        fix q assume qa: "?a \<le> q" and qfn: "q < ?fnM"
                        \<comment> \<open>translate to \<open>?S\<close> coords; \<open>idxsum_leftend_lmin\<close> at the last component\<close>
                        let ?i = "q - j0' - (TrMax ?Np + 1)"
                        have lmS: "\<forall>j < IdxSum (Br ?Np) ! ?J1.
                                     entry ?S 0 (IdxSum (Br ?Np) ! ?J1) \<le> entry ?S 0 j"
                          using idxsum_leftend_lmin[OF ST J1Br[unfolded brQ]] brQ by simp
                        have iidx: "?i < IdxSum (Br ?Np) ! ?J1"
                          using qfn qa idxJ1 fnge by linarith
                        have iS: "?i < Lng ?S"
                          using iidx idxJ1le by linarith
                        have qS: "q - j0' < Lng ?Np" using qfn fnM_lt fnLng by linarith
                        have eqJ1: "entry ?S 0 (IdxSum (Br ?Np) ! ?J1) = entry ?Np 0 ?fn"
                        proof -
                          have "IdxSum (Br ?Np) ! ?J1 < Lng ?S" using idxJ1le iS by linarith
                          hence "entry ?S 0 (IdxSum (Br ?Np) ! ?J1)
                               = entry ?Np 0 ((TrMax ?Np + 1) + IdxSum (Br ?Np) ! ?J1)"
                            by (simp add: entry_seg)
                          thus ?thesis using idxJ1 fnval a_le_fnM by simp
                        qed
                        have eqi: "entry ?S 0 ?i = entry ?Np 0 (q - j0')"
                        proof -
                          have e1: "entry ?S 0 ?i = entry ?Np 0 ((TrMax ?Np + 1) + ?i)"
                            using iS by (simp add: entry_seg)
                          have e2: "(TrMax ?Np + 1) + ?i = q - j0'"
                            using qa by linarith
                          show ?thesis using e1 arg_cong[OF e2, of "entry ?Np 0"] by simp
                        qed
                        have efnM: "entry N 0 ?fnM = entry ?Np 0 ?fn"
                          using fnLng by (simp add: entry_seg)
                        have eq2: "entry N 0 q = entry ?Np 0 (q - j0')"
                        proof -
                          have "entry ?Np 0 (q - j0') = entry N 0 (j0' + (q - j0'))"
                            using qS by (simp add: entry_seg)
                          moreover have "j0' + (q - j0') = q" using qa by linarith
                          ultimately show ?thesis by simp
                        qed
                        have "entry ?S 0 (IdxSum (Br ?Np) ! ?J1) \<le> entry ?S 0 ?i"
                          using lmS iidx by blast
                        thus "entry N 0 ?fnM \<le> entry N 0 q"
                          using eqJ1 eqi efnM eq2 by simp
                      qed
                      have lminYn: "\<And>j. j < ?cn \<Longrightarrow> entry ?Yn 0 ?cn \<le> entry ?Yn 0 j"
                      proof -
                        fix j assume jcn: "j < ?cn"
                        have jYn: "j < Lng ?Yn" using jcn cnle by linarith
                        have cYn: "?cn < Lng ?Yn" using cnle LngYn aLN1 by linarith
                        have eYj: "entry ?Yn 0 j = entry N 0 (?a + j)"
                          using jYn by (simp add: entry_seg)
                        have eYc: "entry ?Yn 0 ?cn = entry N 0 ?fnM"
                          using cYn acn by (simp add: entry_seg)
                        have "entry N 0 ?fnM \<le> entry N 0 (?a + j)"
                          using lminLOW[of "?a + j"] jcn by simp
                        thus "entry ?Yn 0 ?cn \<le> entry ?Yn 0 j" using eYj eYc by simp
                      qed
                      have Nsplit: "P ?Yn = P (seg ?Yn 0 (?cn - 1)) @ P (seg ?Yn ?cn (Lng ?Yn - 1))"
                        by (rule m_6_2_P_additive[OF YnT cn0 cnle lminYn])
                      have segLOW_N: "seg ?Yn 0 (?cn - 1) = seg N ?a (?fnM - 1)"
                      proof -
                        have db: "?cn - 1 \<le> Lng N - 1 - ?a" using cnle LngYn by linarith
                        have "seg ?Yn 0 (?cn - 1) = seg N (?a + 0) (?a + (?cn - 1))"
                          by (rule seg_of_seg[OF aLN1_le db])
                        also have "\<dots> = seg N ?a (?a + (?cn - 1))" by simp
                        also have "?a + (?cn - 1) = ?fnM - 1" using cn0 acn by linarith
                        finally show ?thesis by simp
                      qed
                      have segHIGH_N: "seg ?Yn ?cn (Lng ?Yn - 1) = seg N ?fnM (Lng N - 1)"
                      proof -
                        have db: "Lng ?Yn - 1 \<le> Lng N - 1 - ?a" using LngYn by linarith
                        have "seg ?Yn ?cn (Lng ?Yn - 1) = seg N (?a + ?cn) (?a + (Lng ?Yn - 1))"
                          by (rule seg_of_seg[OF aLN1_le db])
                        also have "?a + ?cn = ?fnM" using acn .
                        also have "?a + (Lng ?Yn - 1) = Lng N - 1" using axcn .
                        finally show ?thesis by simp
                      qed
                      \<comment> \<open>the N-side HIGH is the single non-multi last component \<open>seg N ?fnM (Lng N-1)\<close>\<close>
                      have compN_eq: "seg N ?fnM (Lng N - 1) = Br ?Np ! ?J1"
                      proof -
                        have ab2: "j0' \<le> Lng N - 1" using j0'lt1N by linarith
                        have db2: "Lng ?Np - 1 \<le> (Lng N - 1) - j0'" using NpL by linarith
                        have endeq: "j0' + (Lng ?Np - 1) = Lng N - 1" using NpL j0'lt1N by linarith
                        have "Br ?Np ! ?J1 = seg ?Np ?fn (Lng ?Np - 1)" using comp_eq .
                        also have "seg ?Np ?fn (Lng ?Np - 1) = seg N ?fnM (j0' + (Lng ?Np - 1))"
                          by (rule seg_of_seg[OF ab2 db2])
                        also have "\<dots> = seg N ?fnM (Lng N - 1)"
                          using arg_cong[OF endeq, of "seg N ?fnM"] .
                        finally show ?thesis by simp
                      qed
                      have HIGH_N_single: "P (seg N ?fnM (Lng N - 1)) = [seg N ?fnM (Lng N - 1)]"
                      proof (rule poper_P_nonmulti)
                        show "\<not> (multiT (seg N ?fnM (Lng N - 1)) \<and> 1 < Lng (seg N ?fnM (Lng N - 1)))"
                          using compnm compN_eq by simp
                      qed
                      have BrNp_split: "Br ?Np = P (seg N ?a (?fnM - 1)) @ [seg N ?fnM (Lng N - 1)]"
                        using BrNpP Nsplit segLOW_N segHIGH_N HIGH_N_single by simp
                      \<comment> \<open>\<open>P(seg N ?a (?fnM-1)) = take J\<^sub>1 (Br N')\<close>\<close>
                      have lowN_take: "P (seg N ?a (?fnM - 1)) = take ?J1 (Br ?Np)"
                      proof -
                        have "take ?J1 (Br ?Np)
                            = take ?J1 (P (seg N ?a (?fnM - 1)) @ [seg N ?fnM (Lng N - 1)])"
                          using BrNp_split by simp
                        moreover have "length (P (seg N ?a (?fnM - 1))) = ?J1"
                        proof -
                          have "length (Br ?Np)
                              = length (P (seg N ?a (?fnM - 1)) @ [seg N ?fnM (Lng N - 1)])"
                            using BrNp_split by simp
                          also have "\<dots> = length (P (seg N ?a (?fnM - 1))) + 1" by simp
                          finally show ?thesis using BrNpne' by simp
                        qed
                        ultimately show ?thesis using BrNpne' by simp
                      qed
                      \<comment> \<open>period agreement: \<open>M = N\<close> on \<open>[?a, ?fnM-1]\<close> (\<open>\<le> ?fnM \<le> ?j0N\<close>)\<close>
                      have segMN: "seg M ?a (?fnM - 1) = seg N ?a (?fnM - 1)"
                      proof (rule nth_equalityI)
                        show "length (seg M ?a (?fnM - 1)) = length (seg N ?a (?fnM - 1))" by simp
                        fix i assume "i < length (seg M ?a (?fnM - 1))"
                        hence ic: "i < Suc (?fnM - 1) - ?a" by simp
                        have aile: "?a + i \<le> ?j0N" using ic cn0 acn fnM_lt by linarith
                        have "seg M ?a (?fnM - 1) ! i = M ! (?a + i)"
                          by (rule seg_nth_eq) (use ic in simp)
                        also have "\<dots> = N ! (?a + i)" using agree[OF aile] .
                        also have "\<dots> = seg N ?a (?fnM - 1) ! i"
                          by (rule seg_nth_eq[symmetric]) (use ic in simp)
                        finally show "seg M ?a (?fnM - 1) ! i = seg N ?a (?fnM - 1) ! i" .
                      qed
                      have LOW_eq: "P (seg M ?a (?fnM - 1)) = take ?J1 (Br ?Np)"
                        using segMN lowN_take by simp
                      \<comment> \<open>STEP 5: fold \<open>Br M' = LOW @ [?TL]\<close> via \<open>BrM'P\<close> + \<open>P\<close>-additivity on \<open>M\<close>-side\<close>
                      let ?X = "seg M ?a j1'"
                      have aj1: "?a < j1'" using fnM_lt fnMj1 a_le_fnM by linarith
                      have LngX: "Lng ?X = Suc j1' - ?a" by (rule Lng_seg)
                      have XT: "?X \<in> T_PS"
                      proof -
                        have "0 < Lng ?X" using LngX aj1 by linarith
                        thus ?thesis using length_greater_0_conv by (fastforce simp: T_PS_def)
                      qed
                      have cnleX: "?cn \<le> Lng ?X - 1" using LngX fnMj1 a_le_fnM by linarith
                      have axcX: "?a + (Lng ?X - 1) = j1'" using LngX aj1 by linarith
                      have lminX: "\<And>j. j < ?cn \<Longrightarrow> entry ?X 0 ?cn \<le> entry ?X 0 j"
                      proof -
                        fix j assume jcn: "j < ?cn"
                        have jX: "j < Lng ?X" using jcn cnleX by linarith
                        have cX: "?cn < Lng ?X" using cnleX LngX aj1 by linarith
                        have eXj: "entry ?X 0 j = entry M 0 (?a + j)"
                          using jX by (simp add: entry_seg)
                        have eXc: "entry ?X 0 ?cn = entry M 0 ?fnM"
                          using cX acn by (simp add: entry_seg)
                        \<comment> \<open>\<open>?a+j < ?fnM \<le> ?j0N\<close>, so \<open>M = N\<close>; use \<open>lminLOW\<close> + \<open>efnM_MN\<close>\<close>
                        have ajfn: "?a + j < ?fnM" using jcn acn by linarith
                        have ajle: "?a + j \<le> ?j0N" using ajfn fnM_lt by linarith
                        have "entry M 0 (?a + j) = entry N 0 (?a + j)"
                          using agree[OF ajle] by (simp add: entry_def)
                        moreover have "entry N 0 ?fnM \<le> entry N 0 (?a + j)"
                          using lminLOW[of "?a + j"] ajfn by simp
                        ultimately show "entry ?X 0 ?cn \<le> entry ?X 0 j"
                          using eXj eXc efnM_MN by simp
                      qed
                      have Msplit: "P ?X = P (seg ?X 0 (?cn - 1)) @ P (seg ?X ?cn (Lng ?X - 1))"
                        by (rule m_6_2_P_additive[OF XT cn0 cnleX lminX])
                      have segLOW_M: "seg ?X 0 (?cn - 1) = seg M ?a (?fnM - 1)"
                      proof -
                        have db: "?cn - 1 \<le> j1' - ?a" using cnleX LngX by linarith
                        have "seg ?X 0 (?cn - 1) = seg M (?a + 0) (?a + (?cn - 1))"
                          by (rule seg_of_seg[OF less_imp_le[OF aj1] db])
                        also have "\<dots> = seg M ?a (?a + (?cn - 1))" by simp
                        also have "?a + (?cn - 1) = ?fnM - 1" using cn0 acn by linarith
                        finally show ?thesis by simp
                      qed
                      have segHIGH_M: "seg ?X ?cn (Lng ?X - 1) = seg M ?fnM j1'"
                      proof -
                        have db: "Lng ?X - 1 \<le> j1' - ?a" using LngX by linarith
                        have "seg ?X ?cn (Lng ?X - 1) = seg M (?a + ?cn) (?a + (Lng ?X - 1))"
                          by (rule seg_of_seg[OF less_imp_le[OF aj1] db])
                        also have "?a + ?cn = ?fnM" using acn .
                        also have "?a + (Lng ?X - 1) = j1'" using axcX .
                        finally show ?thesis by simp
                      qed
                      have fold: "Br ?M' = take ?J1 (Br ?Np) @ [?TL]"
                      proof -
                        have "Br ?M' = P (seg M ?a (?fnM - 1)) @ P (seg M ?fnM j1')"
                          using BrM'P Msplit segLOW_M segHIGH_M by simp
                        thus ?thesis using LOW_eq hitail by simp
                      qed
                      \<comment> \<open>STEP 4: junction \<open>cdom (last LOW) (?TL)\<close>.  \<open>last LOW = Br N' ! (J\<^sub>1-1)\<close>,
                         \<open>cdom\<close> from \<open>descN'\<close> on adjacent \<open>J\<^sub>1-1, J\<^sub>1\<close>; the \<open>?TL\<close> head equals
                         \<open>(Br N' ! J\<^sub>1)\<^sub>0\<close> since \<open>M_{?fnM} = N_{?fnM}\<close> (article 1500).\<close>
                      have junc_cdom: "?J1 \<noteq> 0 \<Longrightarrow> cdom (last (take ?J1 (Br ?Np))) ?TL"
                      proof -
                        assume J1ne: "?J1 \<noteq> 0"
                        have takelen: "length (take ?J1 (Br ?Np)) = ?J1"
                          using J1Br by simp
                        have takene: "take ?J1 (Br ?Np) \<noteq> []" using J1ne takelen by auto
                        have lastlow: "last (take ?J1 (Br ?Np)) = Br ?Np ! (?J1 - 1)"
                        proof -
                          have "last (take ?J1 (Br ?Np)) = take ?J1 (Br ?Np) ! (?J1 - 1)"
                            using takene takelen by (simp add: last_conv_nth)
                          also have "\<dots> = Br ?Np ! (?J1 - 1)"
                            using J1ne J1Br by simp
                          finally show ?thesis .
                        qed
                        have cdomBr: "cdom (Br ?Np ! (?J1 - 1)) (Br ?Np ! ?J1)"
                          by (rule descending_cdomD[OF descN' diff_le_self J1L])
                        \<comment> \<open>\<open>?TL\<close> head row-0/row-1 \<open>= (Br N' ! J\<^sub>1)\<close> head (both \<open>= N_{?fnM}\<close>)\<close>
                        have TLne: "0 < Lng ?TL" using LngTL fnMj1 by linarith
                        have TLhd0: "entry ?TL 0 0 = entry N 0 ?fnM"
                          using TLne efnM_MN by (simp add: entry_seg)
                        have TLhd1: "entry ?TL 1 0 = entry N 1 ?fnM"
                        proof -
                          have "entry ?TL 1 0 = entry M 1 ?fnM" using TLne by (simp add: entry_seg)
                          also have "\<dots> = entry N 1 ?fnM"
                            using agree[of ?fnM] fnM_lt by (simp add: entry_def)
                          finally show ?thesis .
                        qed
                        have compLpos: "0 < Lng (seg N ?fnM (Lng N - 1))"
                          using compne compN_eq by simp
                        have Chd0: "entry (Br ?Np ! ?J1) 0 0 = entry N 0 ?fnM"
                        proof -
                          have "entry (seg N ?fnM (Lng N - 1)) 0 0 = entry N 0 (?fnM + 0)"
                            by (rule entry_seg[OF compLpos])
                          thus ?thesis using compN_eq by simp
                        qed
                        have Chd1: "entry (Br ?Np ! ?J1) 1 0 = entry N 1 ?fnM"
                        proof -
                          have "entry (seg N ?fnM (Lng N - 1)) 1 0 = entry N 1 (?fnM + 0)"
                            by (rule entry_seg[OF compLpos])
                          thus ?thesis using compN_eq by simp
                        qed
                        show "cdom (last (take ?J1 (Br ?Np))) ?TL"
                          unfolding cdom_def
                        proof (intro conjI impI)
                          from cdomBr have r0: "entry (Br ?Np ! ?J1) 0 0
                                                  \<le> entry (Br ?Np ! (?J1 - 1)) 0 0"
                            and r1: "entry (Br ?Np ! (?J1 - 1)) 0 0 = entry (Br ?Np ! ?J1) 0 0
                                      \<longrightarrow> entry (Br ?Np ! ?J1) 1 0 \<le> entry (Br ?Np ! (?J1 - 1)) 1 0"
                            unfolding cdom_def by auto
                          show "entry ?TL 0 0 \<le> entry (last (take ?J1 (Br ?Np))) 0 0"
                            using r0 lastlow TLhd0 Chd0 by simp
                          assume "entry (last (take ?J1 (Br ?Np))) 0 0 = entry ?TL 0 0"
                          hence "entry (Br ?Np ! (?J1 - 1)) 0 0 = entry (Br ?Np ! ?J1) 0 0"
                            using lastlow TLhd0 Chd0 by simp
                          hence "entry (Br ?Np ! ?J1) 1 0 \<le> entry (Br ?Np ! (?J1 - 1)) 1 0"
                            using r1 by simp
                          thus "entry ?TL 1 0 \<le> entry (last (take ?J1 (Br ?Np))) 1 0"
                            using lastlow TLhd1 Chd1 by simp
                        qed
                      qed
                      have TLdesc: "descending [?TL]" by (simp add: descending_def)
                      have LOWdesc: "descending (take ?J1 (Br ?Np))"
                        by (rule descending_take[OF descN'])
                      have junc: "cdom (last (take ?J1 (Br ?Np))) (?TL)"
                        using junc_cdom J1pos by simp
                      have "descending (take ?J1 (Br ?Np) @ [?TL])"
                        by (rule descending_append[OF LOWdesc TLdesc]) (use junc in simp)
                      thus ?thesis using fold by simp
                      qed
                    qed
                  next
                    case alarge: False
                    \<comment> \<open>sub-case B, regime \<open>J\<^sub>1 = 0\<close> (\<open>a = j\<^sub>0\<^sup>N\<close>, i.e. \<open>TrMax(N') = d-1\<close>):
                       \<open>Br M' = P(seg M j\<^sub>0\<^sup>N j'\<^sub>1) = ?Y\<close> directly (block-0 fold), descending
                       by \<open>Ydesc\<close>.  This regime is independent of the B/C split.\<close>
                    have aeq: "?a = ?j0N" using alarge ale by linarith
                    have fold: "Br ?M' = ?Y"
                    proof -
                      have "Br ?M' = P (seg M ?j0N j1')" using BrM'P aeq by simp
                      thus ?thesis using hival by simp
                    qed
                    show ?thesis using fold Ydesc by simp
                  qed
                qed
              qed
            next
              case d0pos: False
              \<comment> \<open>\<open>i\<^sub>1 = 1\<close>: \<open>M = prefix @ \<Oplus>\<^sub>k IncrFirst\<^bsup>k\<delta>\<^esup>(block)\<close>, article 1516–1589.
                 GREEN GROUNDWORK (geometry common to all four article sub-cases):
                 \<open>i\<^sub>1 = 1\<close>, \<open>j\<^sub>-\<^sub>2\<^sup>N = parent N 1 (Lng N-1)\<close>, \<open>\<delta> > 0\<close> (always), the
                 fundamental-sequence layout/length, prefix agreement \<open>M = N\<close> on
                 \<open>[0, j\<^sub>-\<^sub>2\<^sup>N]\<close>, the last-node identity \<open>M\<^bsub>j\<^sub>1\<^sup>N\<^esub> = (N\<^bsub>0,j\<^sub>1\<^sup>N\<^esub>, N\<^bsub>1,j\<^sub>-\<^sub>2\<^sup>N\<^esub>)\<close>,
                 and \<open>le0 N j\<^sub>-\<^sub>2\<^sup>N (Lng N-1)\<close>.  Empirically verified (red_model, KMAX=6,
                 18 standard d0pos witnesses): \<open>\<delta>>0\<close>, block-floor formula, prefix
                 agreement, last-node identity all hold with 0 failures.\<close>
              have d1posN: "0 < entry N 1 (Lng N - 1)" using d0pos by simp
              have i1zN: "idx1 N (Lng N - 1) = 1" using d1posN by (simp add: idx1_def)
              \<comment> \<open>\<open>j\<^sub>-\<^sub>2\<^sup>N = parent N 1 (Lng N-1)\<close>: the row-1 parent of the last node\<close>
              have haspar1: "hasParent N 1 (Lng N - 1)" using hasparN i1zN by simp
              have parR1: "nextR N 1 (parent N 1 (Lng N - 1)) (Lng N - 1)"
                using haspar1 unfolding hasParent_def parent_def by (rule theI')
              have j0Nlt: "parent N 1 (Lng N - 1) < Lng N - 1"
                using poper_nextR_imp_le0[OF parR1] by simp
              let ?j0N = "parent N 1 (Lng N - 1)"  let ?w = "Lng N - 1 - ?j0N"
              let ?delta = "entry N 0 (Lng N - 1) - entry N 0 ?j0N"
              have w0: "0 < ?w" using j0Nlt by linarith
              have j0NltN: "?j0N < Lng N" using j0Nlt LNgt by linarith
              \<comment> \<open>\<open>le0 N j\<^sub>-\<^sub>2\<^sup>N (Lng N-1)\<close>: a conjunct of the row-1 next-relation
                 \<open>nextR N 1 j\<^sub>-\<^sub>2\<^sup>N (Lng N-1)\<close> (\<open>j\<^sub>-\<^sub>2\<^sup>N\<close> is a row-0 ancestor of the last
                 node, article: \<open>(1,j\<^sub>-\<^sub>2\<^sup>N) <\<^sup>Next (1,j\<^sub>1\<^sup>N)\<close> implies \<open>(0,j\<^sub>-\<^sub>2\<^sup>N) \<le> (0,j\<^sub>1\<^sup>N)\<close>).\<close>
              have le0NjN: "le0 N ?j0N (Lng N - 1)"
                using parR1 by (simp add: nextR_def nextrel1_def)
              \<comment> \<open>\<open>\<delta> > 0\<close> ALWAYS (article 1522; empirically 0 failures over 17128 cases):
                 the row-0 \<open>nextrel0\<close>-chain \<open>j\<^sub>-\<^sub>2\<^sup>N \<rightarrow>\<^sup>* Lng N-1\<close> with \<open>j\<^sub>-\<^sub>2\<^sup>N < Lng N-1\<close>
                 forces a strict row-0 increase (@{thm [source] le0_ances_aux}).\<close>
              have deltaPos: "0 < ?delta"
              proof -
                have chain: "(nextrel0 N)\<^sup>*\<^sup>* ?j0N (Lng N - 1)"
                  using le0NjN by (simp add: le0_def)
                have "entry N 0 ?j0N < entry N 0 (Lng N - 1)"
                  using le0_ances_aux[OF chain] j0Nlt by simp
                thus ?thesis by simp
              qed
              \<comment> \<open>fundamental-sequence layout + length (\<open>oper_d1pos_*\<close>)\<close>
              have layout: "M = take ?j0N N
                @ concat (map (\<lambda>k. map (\<lambda>j. (entry N 0 j + k * ?delta, entry N 1 j))
                      [?j0N..<Lng N - 1]) [0..<n])"
                using Neq oper_d1pos_expand[OF LNgt notzeroN hasparN i1zN] by simp
              have LngM: "Lng M = ?j0N + n * ?w"
                using Neq oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0Nlt] by simp
              have le0M: "le0 M j0' j1'" using leR by (simp add: leR_def)
              have j0'lt: "j0' < Lng M" using lt jM by linarith
              have nw0: "0 < n * ?w" using n1 w0 by simp
              have j0NltM: "?j0N < Lng M" using LngM nw0 by linarith
              have MT: "M \<in> T_PS" using MS SkT_PS_subset_ST_PS ST_PS_T_PS by blast
              \<comment> \<open>prefix agreement: \<open>M = N\<close> on \<open>[0, j\<^sub>-\<^sub>2\<^sup>N]\<close> inclusive.  For \<open>x < j\<^sub>-\<^sub>2\<^sup>N\<close>
                 use \<open>oper_d1pos_nth_prefix\<close>; at \<open>x = j\<^sub>-\<^sub>2\<^sup>N\<close> it is the head of block 0,
                 \<open>(N\<^bsub>0,j\<^sub>-\<^sub>2\<^sup>N\<^esub> + 0\<cdot>\<delta>, N\<^bsub>1,j\<^sub>-\<^sub>2\<^sup>N\<^esub>) = N\<^bsub>j\<^sub>-\<^sub>2\<^sup>N\<^esub>\<close> (\<open>oper_d1pos_nth\<close>, \<open>q=0,s=0\<close>).\<close>
              have agree: "\<And>x. x \<le> ?j0N \<Longrightarrow> M ! x = N ! x"
              proof -
                fix x assume xle: "x \<le> ?j0N"
                show "M ! x = N ! x"
                proof (cases "x < ?j0N")
                  case True
                  show ?thesis
                    using Neq oper_d1pos_nth_prefix[OF LNgt notzeroN hasparN i1zN True] by simp
                next
                  case False
                  hence xeq: "x = ?j0N" using xle by linarith
                  have npos: "0 < n" using n1 by simp
                  have s0: "(0::nat) < ?w" using w0 .
                  have "M ! ?j0N = (M::pairseq) ! (?j0N + 0 * ?w + 0)" by simp
                  also have "M ! (?j0N + 0 * ?w + 0)
                      = (entry N 0 (?j0N + 0) + 0 * ?delta, entry N 1 (?j0N + 0))"
                    using Neq oper_d1pos_nth[OF LNgt notzeroN hasparN i1zN j0Nlt npos s0] by simp
                  also have "\<dots> = (entry N 0 ?j0N, entry N 1 ?j0N)" by simp
                  also have "\<dots> = N ! ?j0N" using j0NltN by (simp add: entry_def)
                  finally show ?thesis using xeq by simp
                qed
              qed
              \<comment> \<open>article TOP SPLIT (1542 / 1592) on \<open>j'\<^sub>0\<close> vs \<open>j\<^sub>-\<^sub>2\<^sup>N = ?j0N\<close>.
                 BANKED (green): the would-be "A0" sub-case \<open>j'\<^sub>1 \<le> j\<^sub>-\<^sub>2\<^sup>N\<close> (article 1540,
                 slice inside the \<open>M = N\<close> prefix, reduce to IH on \<open>N\<close>) is VACUOUS in
                 this jlarge branch: \<open>j\<^sub>-\<^sub>2\<^sup>N = parent N 1 (Lng N-1) < Lng N-1 \<le> j'\<^sub>1\<close>
                 (\<open>j0Nlt\<close> + \<open>bge\<close>), so always \<open>j\<^sub>-\<^sub>2\<^sup>N < j'\<^sub>1\<close>.  Empirically confirmed
                 (0 of 1648 d0pos jlarge slices fall in A0; whole theorem also has
                 0 descending failures — python/sk_68_d0pos_audit.py).
                 So the slice always crosses \<open>j\<^sub>-\<^sub>2\<^sup>N\<close>, leaving exactly the two genuine
                 hard regimes below, both funnelled to the single residual sorry.\<close>
              have j0Nltj1: "?j0N < j1'" using j0Nlt bge by linarith
              show ?thesis
              proof (cases "j1' \<le> ?j0N")
                case A0: True
                \<comment> \<open>CLOSED (green) — the article's "A0" (1540): vacuous here, since
                   \<open>j\<^sub>-\<^sub>2\<^sup>N < j'\<^sub>1\<close> (\<open>j0Nltj1\<close>) contradicts \<open>j'\<^sub>1 \<le> j\<^sub>-\<^sub>2\<^sup>N\<close>.\<close>
                have False using A0 j0Nltj1 by linarith
                thus ?thesis ..
              next
                case crossesA0: False
                \<comment> \<open>RESIDUAL HARD REGIME (article 1542–1620), single relocated sorry.
                 TWO regimes on \<open>j'\<^sub>0\<close> vs \<open>j\<^sub>-\<^sub>2\<^sup>N\<close> (\<open>= ?j0N\<close>); both share the missing
                 brick \<open>oper_d1pos_seg_P_*\<close> (the \<open>\<delta>\<close>-shifted block-fold analogue of
                 \<open>oper_d0zero_seg_P_blk0fold/_split/_hfold\<close>), which does NOT yet exist.

                 (A) \<open>j'\<^sub>0 < j\<^sub>-\<^sub>2\<^sup>N\<close> (\<open>< j'\<^sub>1\<close> by \<open>j0Nltj1\<close>; article 1544–1589): derive
                     \<open>(0,j'\<^sub>0) \<le>\<^sub>N (0,j\<^sub>1\<^sup>N)\<close> via row-0 convexity \<open>m_5_1_ancestor_tree_1\<close> +
                     the n-block chain \<open>(0,j\<^sub>-\<^sub>2\<^sup>N) \<le>\<^sub>M (0,j\<^sub>1)\<close> (have:
                     @{thm [source] oper_d1pos_block_chain},
                     @{thm [source] oper_d1pos_nextrel0_transfer}); IH gives
                     \<open>descending (Br N')\<close>, \<open>N' = seg N j'\<^sub>0 (Lng N-1)\<close>.  Then \<open>J\<^sub>1 = -1\<close>
                     (1546, single-block constant-head fold) vs \<open>J\<^sub>1 \<ge> 0\<close> (1552, 3
                     sub-subcases on \<open>TrMax(N')\<close> vs \<open>j\<^sub>-\<^sub>2\<^sup>N-j'\<^sub>0\<close> / \<open>j\<^sub>-\<^sub>3\<close>).

                 (B) \<open>j\<^sub>-\<^sub>2\<^sup>N \<le> j'\<^sub>0\<close> (article 1592–1620): divide \<open>j'\<^sub>0-j\<^sub>-\<^sub>2\<^sup>N\<close> by \<open>?w\<close>,
                     reduce to \<open>q=0\<close> via @{thm [source] oper_d1pos_seg_period_reduce};
                     then \<open>j'\<^sub>1 < j\<^sub>1\<^sup>N\<close> (1602, \<open>M = Pred N\<close>-prefix, \<open>M' = seg N j'\<^sub>0 j'\<^sub>1\<close>,
                     reduce to IH on \<open>N\<close>) vs \<open>j'\<^sub>1 \<ge> j\<^sub>1\<^sup>N\<close> (1606, 3 sub-subcases on
                     \<open>TrMax(N')\<close> vs \<open>j\<^sub>1\<^sup>N-j'\<^sub>0\<close> / \<open>j\<^sub>0\<^sup>N-j'\<^sub>0\<close>.
                 CLOSURE (article-faithful direct, docs continued 32–33): case-split
                 on \<open>brle = (TrMax M' = end \<or> le0 M' (TrMax M'+1)(Lng M'-1))\<close>.
                 EMPIRICALLY (python/d1pos_Br_singleton_check.py, rank-stratified std):
                 \<open>brle\<close> holds iff \<open>Br M'\<close> is a SINGLE component (137/149); the 12/149
                 \<open>\<not>brle\<close> cases are the genuine multi-component d0pos remainder.
                 - \<open>brle\<close>: @{thm [source] descending_Br_of_branch_le0} (FULLY PROVEN —
                   \<open>Y\<^sub>p\<close> non-multi so \<open>P Y\<^sub>p = [Y\<^sub>p]\<close>, descending is the trivial singleton).
                 - \<open>\<not>brle\<close>: the multi-component article regime A/B decomposition
                   \<open>Br M' = (Br N')[0..J\<^sub>1-1] @ [tail]\<close> with the junction row-1 tie-break
                   (D3, empirically 132/132), via \<open>IHk\<close> on \<open>N\<close>-slices.  RESIDUAL (the
                   last d0pos piece; no longer the over-general \<open>slice_P_tiebreak\<close>).\<close>
                let ?M' = "seg M j0' j1'"
                have M'T: "?M' \<in> T_PS"
                proof -
                  have "length ?M' = Suc j1' - j0'" using Lng_seg by simp
                  hence "0 < length ?M'" using lt by simp
                  thus ?thesis by (cases ?M') (auto simp: T_PS_def)
                qed
                show ?thesis
                proof (cases "TrMax ?M' = Lng ?M' - 1
                              \<or> le0 ?M' (TrMax ?M' + 1) (Lng ?M' - 1)")
                  case brle: True
                  \<comment> \<open>single-component branch: descending is the trivial singleton case\<close>
                  show ?thesis by (rule descending_Br_of_branch_le0[OF M'T brle])
                next
                  case notbrle: False
                  \<comment> \<open>multi-component d0pos remainder: article regime A/B decomposition
                     \<open>Br M' = LOW @ [tail]\<close> with \<open>LOW\<close> the \<open>(IncrFirst^^(q\<delta>))\<close>-shift of
                     \<open>take J\<^sub>1 (Br N\<^sub>p)\<close> (\<open>N\<^sub>p = seg N j\<^sub>0\<^sup>red (Lng N-1)\<close>), junction row-1
                     tie-break via @{thm [source] descending_shift_append}.  \<open>descending
                     (Br N\<^sub>p)\<close> from \<open>IHk\<close> on \<open>N\<close>; the precise block-fold + first-node
                     geometry is the agent-A identification stub
                     @{thm [source] oper_d1pos_notbrle_LOW_take_eq} (parent replaces at
                     merge).  DEEP-verified 30/30 (python/d1pos_notbrle_wire.py).\<close>
                  have stdN: "N \<in> ST_PS" using NS SkT_PS_subset_ST_PS by blast
                  obtain j0red j1red shamt LOW tail where
                      ASM: "j0red < j1red" "j1red \<le> Lng N - 1"
                        "le0 N j0red j1red"
                        "Br ?M' = LOW @ [tail]"
                        "Br (seg N j0red j1red) \<noteq> []"
                        "length LOW = Lng (Br (seg N j0red j1red)) - 1"
                        "\<forall>J. J < length LOW
                             \<longrightarrow> entry (LOW ! J) 0 0
                                   = entry (Br (seg N j0red j1red) ! J) 0 0 + shamt
                               \<and> entry (LOW ! J) 1 0
                                   = entry (Br (seg N j0red j1red) ! J) 1 0"
                        "entry tail 0 0
                           = entry (Br (seg N j0red j1red)
                                      ! (Lng (Br (seg N j0red j1red)) - 1)) 0 0 + shamt"
                        "entry tail 1 0
                           \<le> entry (Br (seg N j0red j1red)
                                      ! (Lng (Br (seg N j0red j1red)) - 1)) 1 0"
                    using oper_d1pos_notbrle_LOW_take_eq[OF NT monoN stdN LNgt notzeroN
                            hasparN i1zN Neq n1 M'T le0M lt jM bge notbrle] by blast
                  let ?Np = "seg N j0red j1red"
                  \<comment> \<open>\<open>descending (Br N\<^sub>p)\<close> via \<open>IHk\<close> on the \<open>N\<close>-slice (\<open>N \<in> SkT_PS k\<close>,
                     FREE endpoint \<open>j1red \<le> Lng N-1\<close>)\<close>
                  have leRNp: "leR N 0 j0red j1red"
                    using ASM(3) by (simp add: leR_def)
                  have descNp: "descending (Br ?Np)"
                    using IHk NS monoN ASM(1) ASM(2) leRNp by blast
                  \<comment> \<open>assemble \<open>descending (LOW @ [tail])\<close> by the shift-append brick\<close>
                  have "descending (LOW @ [tail])"
                  proof (rule descending_shift_append[OF descNp ASM(5) ASM(6)])
                    fix J assume "J < length LOW"
                    thus "entry (LOW ! J) 0 0 = entry (Br ?Np ! J) 0 0 + shamt"
                      using ASM(7) by blast
                  next
                    fix J assume "J < length LOW"
                    thus "entry (LOW ! J) 1 0 = entry (Br ?Np ! J) 1 0"
                      using ASM(7) by blast
                  next
                    show "entry tail 0 0 = entry (Br ?Np ! (Lng (Br ?Np) - 1)) 0 0 + shamt"
                      using ASM(8) .
                  next
                    show "entry tail 1 0 \<le> entry (Br ?Np ! (Lng (Br ?Np) - 1)) 1 0"
                      using ASM(9) .
                  qed
                  thus ?thesis using ASM(4) by simp
                qed
              qed
            qed
          qed
        next
          case LN1: False
          \<comment> \<open>\<open>Lng N = 1\<close>: then \<open>M = N[n] = N\<close>, \<open>Lng M = 1\<close>, contradicting \<open>j0' < j1'\<close>\<close>
          have LN: "Lng N = 1" using LN1 NT by (cases N) (auto simp: T_PS_def)
          hence "M = N" using Neq by (simp add: oper_def Let_def)
          hence "Lng M = 1" using LN by simp
          thus ?thesis using lt j1 by simp
        qed
      qed
    qed
  qed
  thus "M \<in> SkT_PS k \<Longrightarrow> monoT M \<Longrightarrow> j0' < j1' \<Longrightarrow> j1' \<le> Lng M - 1
        \<Longrightarrow> leR M 0 j0' j1' \<Longrightarrow> descending (Br (seg M j0' j1'))" by blast
qed

end
