theory TerminationTriple
imports "EvmFacts" "./Hoare"  "HoareTripleForInstructions"

begin



(*
lemma gas_decreases_in_triples :
 "vctx_gas v2 \<ge> vctx_gas v1 \<Longrightarrow>
  (all_but_gas ** gas_pred g) (contexts_as_set v1 c) \<Longrightarrow>
  (all_but_gas ** gas_pred g2) (contexts_as_set v2 c)"
apply(auto simp add:rw sep_def gas_smaller_def
  not_continuing_def all_but_gas_def
         failing_def some_gas_def code_def
 gas_pred_def context_rw)
*)

definition all_context :: "state_element set_pred" where
"all_context s = (\<exists>c v.  s = contexts_as_set v c)"

lemma gas_decreases_in_triples :
 "(rest ** all_context) (contexts_as_set v1 c) \<Longrightarrow>
  rest {}"

lemma gas_decreases_in_triples :
 "(rest ** all_context) (contexts_as_set v1 c) \<Longrightarrow>
  (rest ** all_context) (contexts_as_set v2 c)"

lemma gas_decreases_in_triples :
 "vctx_gas v2 \<ge> vctx_gas v1 \<Longrightarrow>
  (all ** gas_pred g) (contexts_as_set v1 c) \<Longrightarrow>
  (all ** gas_smaller g) (contexts_as_set v2 c)"

lemma foo_helper [simp] :
"(rest **
        all ** continuing ** code {} ** gas_pred g)
        (insert (ContinuingElm True)
          (contexts_as_set x1 co_ctx)) =
  (rest ** all ** code {} ** gas_pred g)
    (contexts_as_set x1 co_ctx)"
apply (auto simp add:context_rw)
done

lemma using_gas_triple :
   "triple {} (gas_pred g ** continuing ** all) {}
    (gas_smaller g ** continuing ** all
    ## gas_smaller g ** all ** not_continuing **
      (delegating ## calling ## creating ## destructing)
    ## all ** some_gas ** not_continuing **
       (failing ## returning))"
apply(auto simp add: triple_def)
 apply(rule_tac x = 1 in exI)
 apply(case_tac presult; auto)
apply (simp add:sep_add_def instruction_result_as_set_def
  program_sem.simps next_state_def)
apply (case_tac "vctx_next_instruction x1 co_ctx")
apply auto
using case_1 apply force
defer
using case_1 apply force
using meter_gas_check apply force
using case_1 apply force
  apply (metis (mono_tags) sep_continuing_sep sep_lc singleton_iff state_element.inject(21))
  apply (metis instruction_result_as_set_def sep_continuing_sep set_pred.left_commute to_environment_not_continuing)
apply (case_tac "instruction_sem x1 co_ctx a"; auto)
defer
using no_annotation_inst apply force
apply (case_tac x31; auto)


(*
 auto simp add: instruction_result_as_set_def sep_def sep_add_def)
*)
end
