theory Frontier_7_016
  imports Support_7_012
begin

\<comment> \<open>If a marked principal's string IS the last principal \<open>Dsym u # flatBT a\<close>, then
   (by \<^const>\<open>flatBT\<close> injectivity) its term is \<open>DB u a\<close>, so its \<open>RightNodes\<close> is
   \<open>the_enat u # RightNodes a\<close>.\<close>
\<comment> \<open>A complete principal string has length \<open>\<ge> 2\<close> (\<open>Dsym\<close> head + nonempty
   \<open>flatBT\<close> argument).\<close>
lemma flatBP_len_ge2: "2 \<le> length (flatBP pp)"
proof -
  obtain v c where pc: "pp = DB v c" by (cases pp)
  have "flatBT c \<noteq> []" using flatBT_last_not_CM[of c] by simp
  hence "1 \<le> length (flatBT c)" by (cases "flatBT c") auto
  thus ?thesis using pc by simp
qed

end
