theory RelationalSem

imports Main "./ContractSem"

begin

inductive account_state_natural_change :: "account_state \<Rightarrow> account_state \<Rightarrow> bool"
where
natural:
"account_address old = account_address new \<Longrightarrow>
 account_storage old = account_storage new \<Longrightarrow>
 account_code old = account_code new \<Longrightarrow>
 account_balance old \<le> account_balance new \<Longrightarrow>
 account_ongoing_calls old = account_ongoing_calls new \<Longrightarrow>
 account_state_natural_change old new"

inductive world_turn :: "(account_state * instruction_result) \<Rightarrow> (account_state * variable_env) \<Rightarrow> bool"
where
  world_continue: "world_turn (orig, (InstructionContinue (v, _))) (orig, v)"
| world_return:
  "account_state_natural_change account_state_going_out account_state_back \<Longrightarrow>
   build_venv_returned account_state_back result new_v \<Longrightarrow>
   world_turn (account_state_going_out, (InstructionToWorld (_, Some _, _, _))) (account_state_back, new_v)"
| world_fail:
  "account_state_natural_change account_state_going_out account_state_back \<Longrightarrow>
   build_venv_failed account_state_back = Some new_v \<Longrightarrow>
   world_turn (account_state_going_out, (InstructionToWorld (_, Some _, _, _))) (account_state_back, new_v)"

inductive contract_turn :: "(account_state * instruction_result) \<Rightarrow> (account_state * instruction_result) \<Rightarrow> bool"
where
  contract_to_continue:
  "world_turn (orig_account, orig_result) (mid_account, venv) \<Longrightarrow>
   build_cenv mid_account = cenv \<Longrightarrow>
   instrucition_sem cenv venv = InstructionContinue (continuing_v, n) \<Longrightarrow>
   contract_turn (orig_account, orig_result) (orig_account, InstructionContinue (continuing_v, n))"
| contract_to_world:
  "world_turn (orig_account, orig_result) (mid_account, venv) \<Longrightarrow>
   build_cenv mid_account = cenv \<Longrightarrow>
   instrucition_sem cenv venv = InstructionToWorld (act, opt_v, st, bal) \<Longrightarrow>
   account_state_going_out = update_account_state a act st bal opt_v \<Longrightarrow>
   contract_turn (orig_account, orig_result) (account_state_going_out, InstructionToWorld (act, opt_v, st, bal))"

end
