(*
   Copyright 2016 Yoichi Hirai

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

theory Instructions

imports Main "~~/src/HOL/Word/Word" "./ContractEnv" "./lem/Evm"

begin

declare bits_inst_code.simps [simp]
declare sarith_inst_code.simps [simp]
declare arith_inst_code.simps [simp]
declare info_inst_code.simps [simp]
declare dup_inst_code_def [simp]
declare memory_inst_code.simps [simp]
declare storage_inst_code.simps [simp]
declare pc_inst_code.simps [simp]
declare stack_inst_code.simps [simp]
declare swap_inst_code_def [simp]
declare log_inst_code.simps [simp]
declare misc_inst_code.simps [simp]
declare inst_code.simps [simp]
declare inst_size_def [simp]
declare drop_bytes.simps [simp]
declare program_size.simps [simp]
declare program_code.simps [simp]

end
