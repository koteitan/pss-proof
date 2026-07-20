theory Support_7_012
  imports Frontier_7_015
begin

\<comment> \<open>PEEL ENGINE.  An scb occurrence \<open>s \<frown> flatBP P \<frown> b\<close> (\<open>b\<close> all-\<open>)\<close>) whose string
   begins with the complete-component run \<open>concat (map (\<lambda>r. flatBP r \<frown> [CM]) ms)\<close>
   has \<open>length (that run) \<le> length s\<close>.  Induction on \<open>ms\<close>; the marked principal
   \<open>flatBP pp\<close> cannot start at or before a unit's \<open>flatBP r\<close>: the unit's top-level
   \<open>CM\<close> would then land either inside the all-\<open>)\<close> tail \<open>b\<close> (excluded) or be straddled
   by \<open>flatBP pp\<close>, forcing a negative-weight prefix \<open>d\<close> (a suffix of the complete
   \<open>flatBP r\<close>) to be a prefix of \<open>flatBP pp\<close> — impossible by prefix-nonnegativity.\<close>
lemma rnsub_peel_components:
  assumes "s @ flatBP pp @ b = concat (map (\<lambda>r. flatBP r @ [CM]) ms) @ tail"
      and "\<forall>x \<in> set b. x = RP"
  shows "length (concat (map (\<lambda>r. flatBP r @ [CM]) ms)) \<le> length s"
  using assms
proof (induct ms arbitrary: s)
  case Nil
  show ?case by simp
next
  case (Cons r ms)
  define unit where "unit = flatBP r @ [CM]"
  define rest where "rest = concat (map (\<lambda>r. flatBP r @ [CM]) ms)"
  have eq: "s @ flatBP pp @ b = flatBP r @ CM # (rest @ tail)"
    using Cons.prems(1) unfolding unit_def rest_def by simp
  \<comment> \<open>Step 1: the cut reaches past \<open>flatBP r\<close>, i.e. \<open>length (flatBP r) < length s\<close>.\<close>
  have rlt: "length (flatBP r) < length s"
  proof (rule ccontr)
    assume "\<not> length (flatBP r) < length s"
    hence sle: "length s \<le> length (flatBP r)" by simp
    \<comment> \<open>\<open>s\<close> is a prefix of \<open>flatBP r\<close>: \<open>flatBP r = s @ d\<close>.\<close>
    define d where "d = drop (length s) (flatBP r)"
    have sd: "flatBP r = s @ d"
    proof -
      have "s = take (length s) (s @ flatBP pp @ b)" by simp
      also have "\<dots> = take (length s) (flatBP r @ CM # rest @ tail)" using eq by simp
      also have "\<dots> = take (length s) (flatBP r)" using sle by (simp add: take_append)
      finally have "s = take (length s) (flatBP r)" .
      thus ?thesis unfolding d_def by (metis append_take_drop_id)
    qed
    \<comment> \<open>So \<open>flatBP pp @ b = d @ CM # rest @ tail\<close>.\<close>
    have mid: "flatBP pp @ b = d @ CM # (rest @ tail)"
    proof -
      have "s @ flatBP pp @ b = s @ d @ CM # (rest @ tail)" using eq sd by simp
      thus ?thesis by simp
    qed
    \<comment> \<open>If \<open>s = flatBP r\<close> (whole), the marked principal would begin with the unit's
       \<open>CM\<close> — impossible (\<open>flatBP pp\<close> begins with \<open>Dsym\<close>).\<close>
    have sproper: "length s < length (flatBP r)"
    proof (rule ccontr)
      assume "\<not> length s < length (flatBP r)"
      hence lse: "length s = length (flatBP r)" using sle by simp
      have "length d = length (flatBP r) - length s"
        unfolding d_def by (simp only: length_drop)
      hence "length d = 0" using lse by simp
      hence dnil: "d = []" by simp
      have "flatBP pp @ b = CM # (rest @ tail)" using mid dnil by simp
      hence "hd (flatBP pp @ b) = CM" by simp
      moreover have "hd (flatBP pp @ b) = Dsym (case pp of DB v c \<Rightarrow> v)"
        by (cases pp) simp
      ultimately show False by simp
    qed
    have ne: "d \<noteq> []" using sproper unfolding d_def by simp
    \<comment> \<open>\<open>s\<close> is a PROPER prefix of \<open>flatBP r\<close>, so \<open>flatinj_dsum s \<ge> 0\<close>, hence the
       suffix \<open>d\<close> has \<open>flatinj_dsum d \<le> -1\<close>.\<close>
    have ssum: "0 \<le> flatinj_dsum s"
      by (rule flatinj_prefix_nonneg_BP[OF sd ne])
    have dsum: "flatinj_dsum d \<le> -1"
    proof -
      have "flatinj_dsum (flatBP r) = flatinj_dsum s + flatinj_dsum d"
        using sd by simp
      hence "flatinj_dsum d = -1 - flatinj_dsum s"
        by (simp add: flatinj_dsum_flatBP)
      thus ?thesis using ssum by simp
    qed
    \<comment> \<open>Now locate the \<open>CM\<close> (at position \<open>length d\<close>) inside \<open>flatBP pp\<close> or \<open>b\<close>.\<close>
    show False
    proof (cases "length (flatBP pp) \<le> length d")
      case True
      \<comment> \<open>\<open>flatBP pp\<close> is a prefix of \<open>d\<close>; the \<open>CM\<close> lands in \<open>b\<close>.\<close>
      have ppd: "d = flatBP pp @ drop (length (flatBP pp)) d"
      proof -
        have "flatBP pp = take (length (flatBP pp)) (flatBP pp @ b)" by simp
        also have "\<dots> = take (length (flatBP pp)) (d @ CM # (rest @ tail))" using mid by simp
        also have "\<dots> = take (length (flatBP pp)) d" using True by (simp add: take_append)
        finally have "flatBP pp = take (length (flatBP pp)) d" .
        thus ?thesis by (metis append_take_drop_id)
      qed
      have "flatBP pp @ b = flatBP pp @ drop (length (flatBP pp)) d @ CM # (rest @ tail)"
        using mid ppd by (metis append.assoc append_Cons)
      hence "b = drop (length (flatBP pp)) d @ CM # (rest @ tail)" by simp
      hence "CM \<in> set b" by simp
      thus False using Cons.prems(2) by auto
    next
      case False
      \<comment> \<open>\<open>d\<close> is a proper prefix of \<open>flatBP pp\<close> (the \<open>CM\<close> follows), so
         \<open>flatinj_dsum d \<ge> 0\<close>, contradicting \<open>flatinj_dsum d \<le> -1\<close>.\<close>
      hence flt: "length d < length (flatBP pp)" by simp
      have dpp: "flatBP pp = d @ CM # drop (Suc (length d)) (flatBP pp)"
      proof -
        have "d @ CM # (rest @ tail) = flatBP pp @ b" using mid by simp
        \<comment> \<open>compare prefixes of length \<open>Suc (length d)\<close>.\<close>
        have take1: "take (Suc (length d)) (d @ CM # (rest @ tail)) = d @ [CM]"
          by simp
        have take2: "take (Suc (length d)) (flatBP pp @ b) = d @ [CM]"
          using take1 mid by simp
        have "Suc (length d) \<le> length (flatBP pp)" using flt by simp
        hence "take (Suc (length d)) (flatBP pp) = d @ [CM]"
          using take2 by (simp add: take_append)
        hence "flatBP pp = (d @ [CM]) @ drop (Suc (length d)) (flatBP pp)"
          by (metis append_take_drop_id length_append_singleton)
        thus ?thesis by simp
      qed
      have dpre: "flatBP pp = d @ (CM # drop (Suc (length d)) (flatBP pp))"
        using dpp by simp
      have dne: "CM # drop (Suc (length d)) (flatBP pp) \<noteq> []" by simp
      have "0 \<le> flatinj_dsum d"
        by (rule flatinj_prefix_nonneg_BP[OF dpre dne])
      thus False using dsum by simp
    qed
  qed
  \<comment> \<open>Step 2: \<open>length unit = length (flatBP r) + 1 \<le> length s\<close>.\<close>
  have lenge: "length unit \<le> length s"
  proof -
    have "length unit = Suc (length (flatBP r))"
      unfolding unit_def by simp
    thus ?thesis using rlt by simp
  qed
  \<comment> \<open>Peel the unit and recurse.  \<open>s\<close> begins with \<open>unit = flatBP r @ [CM]\<close>.\<close>
  have stake: "take (length unit) s = unit"
  proof -
    have lu: "length unit = Suc (length (flatBP r))"
      unfolding unit_def by simp
    have "take (length unit) s = take (length unit) (s @ flatBP pp @ b)"
      using lenge by simp
    also have "\<dots> = take (length unit) (flatBP r @ CM # rest @ tail)" using eq by simp
    also have "\<dots> = flatBP r @ [CM]" using lu by (simp add: take_append)
    also have "\<dots> = unit" unfolding unit_def by simp
    finally show ?thesis .
  qed
  define s2 where "s2 = drop (length unit) s"
  have seq: "s = unit @ s2"
    unfolding s2_def using stake by (metis append_take_drop_id)
  have eq2: "s2 @ flatBP pp @ b = rest @ tail"
  proof -
    have "unit @ (s2 @ flatBP pp @ b) = unit @ (rest @ tail)"
      using eq seq unfolding unit_def rest_def by simp
    thus ?thesis by simp
  qed
  have IH: "length rest \<le> length s2"
    using Cons.hyps[of s2] eq2 Cons.prems(2)
    unfolding rest_def by simp
  have "length (concat (map (\<lambda>r. flatBP r @ [CM]) (r # ms)))
        = length unit + length rest"
    unfolding unit_def rest_def by simp
  also have "\<dots> \<le> length unit + length s2" using IH by simp
  also have "\<dots> = length s" using seq by simp
  finally show ?case .
qed



\<comment> \<open>CM-shift reassociation: \<open>concat (CM-prefixed) \<frown> [CM] = CM # concat (CM-suffixed)\<close>.\<close>
lemma flat_CM_shift:
  "concat (map (\<lambda>r. CM # flatBP r) ps) @ [CM]
   = CM # concat (map (\<lambda>r. flatBP r @ [CM]) ps)"
  by (induct ps) simp_all

end
