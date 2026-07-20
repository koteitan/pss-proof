(* Phase-0 fact dependency extraction for the frozen PSS development.

   This file is loaded by a disposable theory outside the repository.  It does
   not alter the PSS theories or sessions.  The output is deliberately raw:
   chapter ownership and the proposed physical partition are derived by the
   companion Python analysis, while every dependency edge here comes from
   Thm_Deps.thm_deps over Isabelle theorem identities.
*)

local

val project_theories =
  [("pss_defs", "PSS_A.pss_defs"),
   ("pss_paper", "PSS_A.pss_paper"),
   ("pss_mechanized", "PSS_A.pss_mechanized"),
   ("pss_wip", "PSS_B.pss_wip"),
   ("pss_scratch", "PSS_C.pss_scratch")];

fun clean_field s =
  String.translate
    (fn #"\t" => " " | #"\n" => " " | #"\r" => " " | c => String.str c) s;

fun line fields = space_implode "\t" (map clean_field fields) ^ "\n";

fun thm_id_string thm_name = Thm_Name.print thm_name;

fun fact_rows (theory_label, theory_name) =
  let
    val thy = Thy_Info.get_theory theory_name;
    val space = Global_Theory.fact_space thy;
    fun one (thm_id, ((thm_name as (base_name, index)), pos)) =
      let
        val th = Global_Theory.get_thm_name thy (thm_name, pos);
        val has_skip = Thm_Deps.has_skip_proof [th];
        val {pos = fact_pos, concealed, group, ...} = Name_Space.the_entry space base_name;
      in
        (thm_id_string thm_name,
         line
           [thm_id_string thm_name,
            theory_label,
            fst thm_name,
            string_of_int index,
            string_of_int (#serial thm_id),
            the_default "" (Position.file_of fact_pos),
            string_of_int (the_default 0 (Position.line_of fact_pos)),
            Bool.toString concealed,
            string_of_int group,
            string_of_int (length (Thm.hyps_of th)),
            Bool.toString has_skip],
         th,
         has_skip)
      end;
  in map one (Global_Theory.dest_thm_names thy) end;

val facts = maps fact_rows project_theories;
val project_ids = Symtab.make_set (map #1 facts);
val final_thy = Thy_Info.get_theory "PSS_C.pss_scratch";

fun edge_rows (source, _, th, _) =
  Thm_Deps.thm_deps final_thy [th]
  |> map (fn (dep_id, dep_name) =>
       line
         [source,
          thm_id_string dep_name,
          #theory_name dep_id,
          Bool.toString (Symtab.defined project_ids (thm_id_string dep_name))]);

val edges = maps edge_rows facts;

val article_facts = filter (String.isPrefix "pss_paper.p_" o #1) facts;

fun proposition_match_rows (article_name, _, article_th, _) =
  facts
  |> map_filter (fn (candidate_name, _, candidate_th, candidate_has_skip) =>
       if candidate_name <> article_name andalso
          Term.aconv_untyped (Thm.full_prop_of article_th, Thm.full_prop_of candidate_th)
       then SOME (line [article_name, candidate_name])
       else NONE);

val proposition_matches = maps proposition_match_rows article_facts;

val out_dir =
  (case getenv "PSS_PHASE0_OUT" of
    "" => error "PSS_PHASE0_OUT is not set"
  | s => Path.explode s);

val _ = Isabelle_System.make_directory out_dir;
val _ =
  File.write_list (out_dir + Path.basic "facts.raw.tsv")
    (line
       ["fact", "theory", "base_name", "index", "serial", "source_file",
        "source_line", "concealed", "group", "hypotheses", "has_skip_proof"] :: map #2 facts);
val _ =
  File.write_list (out_dir + Path.basic "dependencies.raw.tsv")
    (line ["source", "target", "target_theory", "target_is_project"] ::
      edges);
val _ =
  File.write_list (out_dir + Path.basic "proposition_matches.raw.tsv")
    (line ["article_fact", "clean_equivalent_fact"] :: proposition_matches);

val _ =
  writeln
    ("PHASE0_DAG_EXTRACTED facts=" ^ string_of_int (length facts) ^
     " dependency_rows=" ^ string_of_int (length edges) ^
     " proposition_matches=" ^ string_of_int (length proposition_matches));

in

val phase0_fact_dag_extracted = true;

end;
