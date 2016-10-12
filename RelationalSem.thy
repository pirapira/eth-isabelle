theory RelationalSem

imports Main "./ContractSem"

begin

inductive world_turn :: "(account_state * instruction_result) \<Rightarrow> (account_state * variable_env) \<Rightarrow> bool"
where
  world_continue: "world_turn (orig, (InstructionContinue (v, _))) (orig, v)"
| world_return:
  "account_state_natural_change account_state_going_out account_state_back \<Longrightarrow>
   build_venv_returned account_state_back result new_v \<Longrightarrow>
   world_turn (account_state_going_out, (InstructionToWorld (act, Some orig_v))) (account_state_back, new_v)"
| world_fail:
  "account_state_natural_change account_state_going_out account_state_back \<Longrightarrow>
   build_venv_failed account_state_back = Some new_v \<Longrightarrow>
   world_turn (account_state_going_out, (InstructionToWorld (act, Some orig_v))) (account_state_back, new_v)"

inductive contract_turn :: "(account_state * instruction_result) \<Rightarrow> (account_state * instruction_result) \<Rightarrow> bool"
where
  contract_to_continue:
  "world_turn (orig_account, orig_result) (mid_account, venv) \<Longrightarrow>
   build_cenv mid_account = cenv \<Longrightarrow>
   instrucition_sem cenv venv = InstructionContinue (continuing_v, n) \<Longrightarrow>
   contract_turn (orig_account, orig_result) (orig_account, InstructionContinue (continuing_v, n))"
| contract_call_world:
  "world_turn (orig_account, orig_result) (mid_account, venv) \<Longrightarrow>
   build_cenv mid_account = cenv \<Longrightarrow>
   instrucition_sem cenv venv = InstructionToWorld (act, Some going_v) \<Longrightarrow>
   account_state_going_out =
     update_account_state a act (venv_storage going_v)
                                (venv_balance going_v) (Some going_v) \<Longrightarrow>
   contract_turn (orig_account, orig_result) (account_state_going_out, InstructionToWorld (act, Some going_v))"
| contract_stop:
  "world_turn (orig_account, orig_result) (mid_account, venv) \<Longrightarrow>
   build_cenv mid_account = cenv \<Longrightarrow>
   instrucition_sem cenv venv = InstructionToWorld (act, None) \<Longrightarrow>
   account_state_going_out =
     (case act of
       ContractFail \<Rightarrow> update_account_state mid_account ContractFail (venv_storage_at_call venv) (venv_balance_at_call venv) None 
     | ContractReturn x \<Rightarrow> update_account_state mid_account (ContractReturn x)
                             (venv_storage venv) (venv_balance venv) None
     | ContractSuicide final_balance \<Rightarrow> update_account_state mid_account
                                        (ContractSuicide final_balance) (\<lambda> _. 0) final_balance None
     | _ \<Rightarrow> undefined (* should not happen *)
     ) \<Longrightarrow>
   contract_turn (orig_account, orig_result) (account_state_going_out, InstructionToWorld (act, None))"

end
