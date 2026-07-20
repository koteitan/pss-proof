theory Frontier_6_048
  imports Support_6_029
begin

(* ===== keystone foundation block from workflow kf-stab ===== *)

text \<open>List helper: two concatenations with identical block-length profiles are
  equal block-by-block.  If \<open>concat xs = concat ys\<close> and the lengths match
  componentwise (\<open>map length xs = map length ys\<close>), then \<open>xs = ys\<close>.
  The matching length lists force the same number of blocks and the same cut
  points, so each block is a take/drop of the common concatenation.\<close>

lemma concat_eq_of_map_length_eq:
  "concat xs = concat ys \<Longrightarrow> map length xs = map length ys \<Longrightarrow> xs = ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(2) obtain y ys' where ys: "ys = y # ys'"
    by (cases ys) auto
  have lxy: "length x = length y" using Cons.prems(2) ys by simp
  have ltl: "map length xs = map length ys'" using Cons.prems(2) ys by simp
  have ceq: "x @ concat xs = y @ concat ys'"
    using Cons.prems(1) ys by simp
  have xy: "x = y" using ceq lxy by (simp add: append_eq_append_conv)
  have ctl: "concat xs = concat ys'"
    using ceq xy by simp
  have "xs = ys'" by (rule Cons.IH[OF ctl ltl])
  thus ?case using xy ys by simp
qed

end
