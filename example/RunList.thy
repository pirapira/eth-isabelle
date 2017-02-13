theory "RunList" 

imports 
   "InstructionAux" "ProgramList" "InstructionRelocate"
"InstructionPc"

begin

definition p_length :: "inst list \<Rightarrow> nat" where
"p_length lst = length (program_list_of_lst lst)"

definition program_at ::
 "program \<Rightarrow> inst list \<Rightarrow> int \<Rightarrow> bool" where
"program_at prog lst n = (\<forall>x.
   x \<ge> p_length lst \<or>
   program_map_of_lst 0 lst x = program_content prog (x+n))"

theorem program_list_content_eq2 :
  "program_map_of_lst t lst (n+t) = index (program_list_of_lst lst) n"
using program_list_map_eq by auto

theorem program_list_content_eq3 :
  "index (program_list_of_lst lst) n = program_map_of_lst 0 lst (n+0)"
  using program_list_map_eq by blast

theorem program_list_content_eq4 :
  "program_map_of_lst 0 lst n = index (program_list_of_lst lst) n"
  by (simp add: program_list_content_eq3)

definition program_int_map :: "inst list \<Rightarrow> int \<Rightarrow> inst option" where
"program_int_map lst x = program_map_of_lst 0 lst (nat x)"

theorem program_location :
 "program_at (program_of_lst (a@b) program_int_map) b (p_length a)"
apply(auto simp:program_at_def p_length_def
   program_list_content_eq4 program_list_append
   program_int_map_def)
  by (smt nat_diff_distrib' nat_int negative_zle)

(*
definition eval_expr_at :: "variable_env \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> 256 word option" where
"eval_expr_at v addr n expr =
  get_top v (program_iter \<lparr>
       cenv_program = \<lparr>
         program_content = program_content_of_lst n (compile_expr expr),
         program_length = 0,
         program_annotation = (\<lambda> x. [])
       \<rparr>,
       cenv_this = addr \<rparr>
     (Continue (v\<lparr>venv_pc := n \<rparr>) 100 100) (count_steps expr))"
*)

(* what is same as list of instructions *)

fun run_list :: "constant_ctx \<Rightarrow> variable_ctx \<Rightarrow>
   inst list \<Rightarrow> variable_ctx option" where
"run_list c v [] = Some v"
| "run_list c v (Cons a t) = (case instruction_sem v c a of
  InstructionContinue v \<Rightarrow> run_list c v t
 | _ \<Rightarrow> None)"

theorem program_content_first [simp] :
  "program_map_of_lst 0 (a # lst) 0 = Some a"
apply(cases a)
apply(auto)
apply(subst program_list_content_eq4)
apply(cases "get_stack a")
apply(auto)
done

(*
theorem simple_relocatable [simp] :
  "xa \<in> set (compile_simple x) \<Longrightarrow> relocatable xa"
apply(induction x arbitrary:xa)
apply(auto)
done

theorem expr_aux1 : 
"(\<And>x. x \<in> set (compile_expr e1) \<Longrightarrow>
             relocatable x) \<Longrightarrow>
       (\<And>x. x \<in> set (compile_expr e2) \<Longrightarrow>
             relocatable x) \<Longrightarrow>
       x \<in> set (binop_inst x1a) \<Longrightarrow> relocatable x"
apply(cases x1a)
apply(auto simp:binop_inst.simps)
done

theorem expr_aux2 : 
"(\<And>x. x \<in> set (compile_expr e) \<Longrightarrow>
             relocatable x) \<Longrightarrow>
       x \<in> set (unop_inst x1a) \<Longrightarrow> relocatable x"
apply(cases x1a)
apply(auto simp:unop_inst.simps)
done

theorem expr_relocatable :
  "x \<in> set (compile_expr e) \<Longrightarrow> relocatable x"
apply(induction e arbitrary:x)
apply(auto)
using expr_aux1 apply(blast)
using expr_aux2 apply(blast)
done
*)

theorem word_length [simp] :
 "length ((word_rsplit (w::256 word)) :: 8 word list) = 32"
apply(rule length_word_rsplit_even_size)
apply(auto simp:word_size)
done

(*
theorem simple_good :
  "xa \<in> set (compile_expr (Simple x)) \<Longrightarrow>
   0 < inst_size xa"
apply(induction x arbitrary:xa)
apply(auto)
done

theorem good_aux1 : "(\<And>x. x \<in> set (compile_expr e1) \<Longrightarrow>
             0 < inst_size x) \<Longrightarrow>
       (\<And>x. x \<in> set (compile_expr e2) \<Longrightarrow>
             0 < inst_size x) \<Longrightarrow>
       x \<in> set (compile_expr (Binary x1a e1 e2)) \<Longrightarrow>
       0 < inst_size x"
apply(cases x1a)
apply(auto simp:binop_inst.simps)
done

theorem good_aux2 :
"(\<And>x. x \<in> set (compile_expr e) \<Longrightarrow>
             0 < inst_size x) \<Longrightarrow>
       x \<in> set (compile_expr (Unary x1a e)) \<Longrightarrow>
       0 < inst_size x"
apply(cases x1a)
apply(auto simp:unop_inst.simps)
done

theorem expr_good :
  "x \<in> set (compile_expr e) \<Longrightarrow> inst_size x > 0"
apply(induction e arbitrary:x)
using simple_good apply(blast)
using good_aux1 apply(blast)
using good_aux2 apply(blast)
done
*)

(*
theorem program_next_aux :
" (p_length (a # lst) \<le> 0 \<or>
        program_content_of_lst 0 (a # lst) 0 =
        program_content (cenv_program c)
         (0 + venv_pc v)) \<Longrightarrow>
    inst_code a \<noteq> [] \<Longrightarrow>
    program_content (cenv_program c) (venv_pc v) =
    Some a"
apply(auto)
apply(auto simp:p_length_def)
apply(cases a)
apply(auto)
apply(cases "get_stack a")
apply(auto)
done
*)

fun good_inst :: "inst \<Rightarrow> bool" where
"good_inst (Stack (PUSH_N lst)) = (length lst > 0 \<and> length lst \<le> 32)"
| "good_inst _ = True"

lemma program_length_not_empty : "p_length (a # lst) = 0 \<Longrightarrow>
    False"
apply(auto simp:p_length_def)
apply(cases a)
apply(auto)
apply(cases "get_stack a")
apply(auto)
done

lemma program_next_some :
"(p_length (a # lst) \<le> 0 \<or>
           program_map_of_lst 0
            (a # lst) 0 =
           program_content
            (cctx_program c)
            (int 0 + vctx_pc v)) \<Longrightarrow>
       program_content (cctx_program c)
        (vctx_pc v) =
       Some a"
apply(auto)
using program_length_not_empty apply blast

done

lemma program_next_none :
 "   ( p_length (a # lst) \<le> 0 \<or>
     program_map_of_lst 0 (a # lst) 0 =
        program_content (cctx_program c)
         (int 0 + vctx_pc v) ) \<Longrightarrow>
    program_content (cctx_program c)
     (vctx_pc v) =
    None \<Longrightarrow>
    Misc STOP = a"
apply(auto)
using program_length_not_empty apply blast
done

theorem program_next : 
  "program_at (cctx_program c) (a # lst) (vctx_pc v) \<Longrightarrow>
   vctx_next_instruction v c = Some a"
apply(auto simp:program_content_first
    program_at_def vctx_next_instruction_def split:option.split)
using program_next_none apply blast
using program_next_some apply fastforce
done

definition program_step  :: "constant_ctx \<Rightarrow> instruction_result \<Rightarrow> instruction_result "  where
"program_step c pr1 = (
  (case  pr1 of
    InstructionToEnvironment _ _ _ => pr1
  | InstructionAnnotationFailure => pr1
  | InstructionContinue v =>
     if \<not> (check_annotations v c) then InstructionAnnotationFailure else
     (case  vctx_next_instruction v c of
        None => InstructionToEnvironment (ContractFail [ShouldNotHappen]) v None
      | Some i =>
        if check_resources v c ((vctx_stack   v)) i then
          instruction_sem v c i
        else
          InstructionToEnvironment (ContractFail
              ((case  inst_stack_numbers i of
                 (consumed, produced) =>
                 (if (((int (List.length ((vctx_stack   v))) + produced) - consumed) \<le>( 1024 :: int)) then [] else [TooLongStack])
                  @ (if predict_gas i v c \<le>(vctx_gas   v) then [] else [OutOfGas])
               )
              ))
              v None
     )
  ))"

fun program_iter ::
   "nat \<Rightarrow> constant_ctx \<Rightarrow> instruction_result \<Rightarrow> instruction_result"  where
"program_iter 0 ctx x = x"
| "program_iter (Suc n) ctx x = program_iter n ctx (program_step ctx x)"

lemma program_step_is_next_state :
 "program_step c x = next_state stopper c x"
  by (simp add: program_step_def)

declare instruction_sem_def [simp del]
declare check_annotations_def [simp del]
declare vctx_next_instruction_def [simp del]

theorem simple_step :
  "program_step c (InstructionContinue v) = InstructionContinue v2 \<Longrightarrow>
   instruction_sem v c (get_some (vctx_next_instruction v c)) =
   InstructionContinue v2"
apply(auto simp:program_step_def)
apply(cases "\<not> check_annotations v c")
apply(auto)
apply(cases "vctx_next_instruction v c")
apply(auto)
apply(cases "check_resources v c (vctx_stack v) (get_some (vctx_next_instruction v c))")
apply(auto)
done

theorem program_step_continue :
 "InstructionContinue v2 = program_step c x \<Longrightarrow>
  \<exists>v. x = InstructionContinue v"
apply(cases x)
apply(auto simp:program_step_def)
done

theorem program_iter_continue :
 "InstructionContinue v2 = program_iter steps c x \<Longrightarrow>
  \<exists>v n k. x = InstructionContinue v"
apply(induction steps arbitrary:v2 n2 k2 c)
apply(auto simp:program_step_continue)
apply(cases x)
apply(auto simp:program_step_def)
done

theorem list_like_step :
  "relocatable inst \<Longrightarrow>
   vctx_next_instruction v c = Some inst \<Longrightarrow>
   program_step c (InstructionContinue v) = InstructionContinue v2 \<Longrightarrow>
   run_list c v [inst] = Some v3 \<Longrightarrow>
   v2 = v3"
apply(simp)
apply(cases "instruction_sem v c inst")
apply(auto)
using simple_step
apply(fastforce)
done

theorem asd :
  "run_list c v (a # lst) = Some v3 \<Longrightarrow>
   \<exists>v2. run_list c v [a] = Some v2"
apply(cases "instruction_sem v c a")
apply(auto)
done

declare run_list.simps [simp del]

fun get_push :: "inst \<Rightarrow> byte list" where
"get_push (Stack (PUSH_N lst)) = lst"

theorem inst_size_eq :
  "good_inst a \<Longrightarrow>
   inst_size a = p_length [a]"
apply(auto simp:p_length_def)
apply(cases a)
apply(auto)
apply(cases "get_stack a")
apply(auto)
done

theorem no_jump_inc_pc2 :
   "program_step c (InstructionContinue v) = InstructionContinue nv \<Longrightarrow>
   is_inc_pc (vctx_next_instruction v c) \<Longrightarrow>
   vctx_pc nv = vctx_pc v + 1"
apply(auto simp:program_step_def)
apply(cases "\<not> check_annotations v c")
apply(auto)
apply(cases "vctx_next_instruction v c")
apply(auto)
apply(cases "check_resources v c
            (vctx_stack v) (get_some (vctx_next_instruction v c))")
apply(auto simp:no_jump_inc_pc)
done

theorem push_inc_pc2 :
   "program_step c (InstructionContinue v) = InstructionContinue nv \<Longrightarrow>
   vctx_next_instruction v c = Some (Stack (PUSH_N lst)) \<Longrightarrow>
   good_inst (Stack (PUSH_N lst)) \<Longrightarrow>
   vctx_pc nv = vctx_pc v + length lst + 1"
apply(auto simp:program_step_def)
apply(cases "\<not> check_annotations v c")
apply(auto)
apply(cases "vctx_next_instruction v c")
apply(auto)
apply(cases "check_resources v c
            (vctx_stack v) (get_some (vctx_next_instruction v c))")
apply(auto simp:push_inc_pc)
using push_inc_pc
done



theorem unknown_fail :
  "vctx_next_instruction v c = Some (Unknown x1) \<Longrightarrow>
   program_step c (InstructionContinue v) =
          InstructionContinue v2 \<Longrightarrow>
   False"
apply(auto simp:program_step_def)
apply(cases "\<not> check_annotations v c")
apply(cases "vctx_next_instruction v c")
apply(auto)
apply(cases "check_resources v c
            (vctx_stack v) (get_some (vctx_next_instruction v c))")
apply(auto simp:instruction_sem_def)
done

theorem correct_pc_inc1 :
  "relocatable a \<Longrightarrow>
   good_inst a \<Longrightarrow>
   vctx_next_instruction v c = Some a \<Longrightarrow>
   program_step c (InstructionContinue v) = InstructionContinue v2 \<Longrightarrow>
   vctx_pc v2 = vctx_pc v + inst_size a"
apply(cases a)
apply(auto)
using unknown_fail
apply(blast)
apply(auto simp:is_inc_pc.simps no_jump_inc_pc2)
apply(cases "get_stack a")
apply(auto simp:is_inc_pc.simps no_jump_inc_pc2)
apply(cases "get_push a")
apply(auto simp:push_inc_pc2)
done

theorem app_cons : "a # lst = [a]@lst"
apply(auto)
done

theorem asdf :
  "program_list_of_lst (a#lst) =
   program_list_of_lst [a] @ program_list_of_lst lst"
using program_list_append
apply(subst app_cons)
apply(blast)
done

declare program_list_of_lst.simps [simp del]

theorem program_index :
"index (program_list_of_lst (a#lst)) (n+p_length[a]) =
 index (program_list_of_lst lst) n"
apply(auto simp:p_length_def)
apply(subst asdf)
apply(auto)
done

theorem test :
 "p_length (a # lst) \<le> (xa+p_length[a]) \<or>
               index (program_list_of_lst (a # lst))
                (xa+p_length[a]) =
               program_content prog (xa + p_length[a] + (x::int)) \<Longrightarrow>
          index (program_list_of_lst lst) xa \<noteq>
          program_content prog
           (int xa + (x + int (p_length [a]))) \<Longrightarrow>
          p_length lst \<le> xa"
apply(auto)
apply(simp add:p_length_def)
apply(subst (asm) (2) asdf)
apply(auto)
apply(auto simp:program_index)
by (simp add: add.left_commute semiring_normalization_rules(24))

theorem program_at_inst :
  "program_at prog (a # lst) (x::int) \<Longrightarrow>
   program_at prog lst (x + p_length [a])"
apply(auto simp:program_at_def inst_size_eq)
apply(auto simp:program_list_content_eq4)

apply(rule_tac xa=xa and a=a and prog=prog and x="x" in test)
apply fastforce
apply fastforce
done

theorem inst_size_eq2 :
  "good_inst a \<Longrightarrow>
   p_length [a] = inst_size a"
apply(subst inst_size_eq)
apply(auto)
done

declare inst_size_def [simp del]

theorem program_at_next_aux :
 "program_at (cctx_program c) (a # lst) (vctx_pc v) \<Longrightarrow>
  relocatable a \<Longrightarrow>
  good_inst a \<Longrightarrow>
  program_step c (InstructionContinue v) = InstructionContinue v2 \<Longrightarrow>
  vctx_pc v2 = vctx_pc v + p_length [a]"
apply(auto simp:inst_size_eq2)
using correct_pc_inc1 program_next
apply(blast)
done

theorem program_at_next :
 "program_at (cctx_program c) (a # lst) (vctx_pc v) \<Longrightarrow>
  relocatable a \<Longrightarrow>
  good_inst a \<Longrightarrow>
  program_step c (InstructionContinue v) = InstructionContinue v2 \<Longrightarrow>
  program_at (cctx_program c) lst (vctx_pc v2)"
apply(subst program_at_next_aux)
apply auto
apply(simp add:program_at_inst)
done

theorem run_list_step :
"run_list c v (a # lst) = Some v3 \<Longrightarrow>
 run_list c v [a] = Some v2 \<Longrightarrow>
 run_list c v2 lst = Some v3"
apply(auto simp:run_list.simps)
apply(cases "instruction_sem v c a")
apply(auto)
apply(auto simp:run_list.simps)
done

fun abc1 :: "constant_ctx \<Rightarrow> variable_ctx \<Rightarrow> variable_ctx" where
"abc1 c v = (case program_step c (InstructionContinue v) of
  InstructionContinue a \<Rightarrow> a)"

lemma program_step_failure :
 "program_step c InstructionAnnotationFailure =
    InstructionContinue v2 \<Longrightarrow> False"
apply (auto simp:program_step_def)
done

lemma program_step_failure_env :
 "program_step c InstructionAnnotationFailure =
    InstructionToEnvironment x31 x32
        x33 \<Longrightarrow> False"
apply (auto simp:program_step_def)
done

lemma program_step_env :
 "program_step c (InstructionToEnvironment x31 x32
        x33) =
    InstructionContinue v2 \<Longrightarrow> False"
apply (auto simp:program_step_def)
done

lemma program_step_env_failure :
 "program_step c (InstructionToEnvironment x31 x32
        x33) =
    InstructionAnnotationFailure \<Longrightarrow> False"
apply (auto simp:program_step_def)
done

lemma program_iter_failure :
 "program_iter n c InstructionAnnotationFailure =
    InstructionContinue v2 \<Longrightarrow> False"
apply (induction n arbitrary:v2)
apply (auto)
apply (cases "program_step c
          InstructionAnnotationFailure")
apply auto
using program_step_failure apply blast
using program_step_failure_env apply blast
done

lemma program_iter_env :
 "program_iter n c (InstructionToEnvironment e f g) =
    InstructionContinue v2 \<Longrightarrow> False"
apply (induction n arbitrary:v2 e f g)
apply (cases n)
apply (auto)
apply (cases "program_step c
          (InstructionToEnvironment e f g)")
using program_step_env apply blast
using program_step_env_failure apply blast
  using program_step_def by auto

theorem step_abc1 :
   "program_iter (length lst) c
        (program_step c (InstructionContinue v))
         = InstructionContinue v2
       \<Longrightarrow>
       program_step c (InstructionContinue v) =
       InstructionContinue (abc1 c v)"
apply(auto)
apply(cases "program_step c (InstructionContinue v)")
apply(auto)
using program_iter_failure apply blast
using program_iter_env apply blast
done

theorem list_aux2 :
"     program_step c (InstructionContinue v) =
      InstructionContinue vv \<Longrightarrow>
      run_list c v [a] = Some vv \<Longrightarrow>


       program_at (cctx_program c) (a # lst)
        (vctx_pc v) \<Longrightarrow>
       program_iter (length lst) c
        (program_step c (InstructionContinue v))  =
       InstructionContinue v2 \<Longrightarrow>
       run_list c v (a # lst) = Some v3 \<Longrightarrow>
       relocatable a \<Longrightarrow>
       good_inst a \<Longrightarrow>
       \<forall>x\<in>set lst. relocatable x \<and> good_inst x \<Longrightarrow>

      ( program_at (cctx_program c) lst
            (vctx_pc vv) \<and>
           program_iter (length lst) c (InstructionContinue vv) =
           InstructionContinue v2 \<and>
           run_list c vv lst = Some v3)"
apply(auto)
apply(simp add:program_at_next)
using run_list_step
apply(blast)
done

theorem list_aux3 :
"     vv = abc1 c v \<Longrightarrow>
      program_step c (InstructionContinue v) =
      InstructionContinue vv \<Longrightarrow>
      run_list c v [a] = Some vv \<Longrightarrow>

      ( program_at (cctx_program c) lst
            (vctx_pc vv) \<Longrightarrow>
        program_iter (length lst) c (InstructionContinue vv) =
           InstructionContinue v2 \<Longrightarrow>
        run_list c vv lst = Some v3 \<Longrightarrow> v2 = v3) \<Longrightarrow>


       program_at (cctx_program c) (a # lst)
        (vctx_pc v) \<Longrightarrow>
       program_iter (length lst) c
        (program_step c (InstructionContinue v)) =
       InstructionContinue v2 \<Longrightarrow>
       run_list c v (a # lst) = Some v3 \<Longrightarrow>
       relocatable a \<Longrightarrow>
       good_inst a \<Longrightarrow>
       \<forall>x\<in>set lst. relocatable x \<and> good_inst x \<Longrightarrow>
       v2 = v3"
using list_aux2
apply blast
done


(*
theorem list_aux2 :
"     program_step c (Continue v e1 e2) =
      Continue vv ee1 ee2 \<Longrightarrow>
      run_list c v [a] = Some vv \<Longrightarrow>


       program_at (cenv_program c) (a # lst)
        (venv_pc v) \<Longrightarrow>
       program_iter c
        (program_step c (Continue v e1 e2))
        (length lst) =
       Continue v2 f1 f2 \<Longrightarrow>
       run_list c v (a # lst) = Some v3 \<Longrightarrow>
       relocatable a \<Longrightarrow>
       0 < inst_size a \<Longrightarrow>
       \<forall>x\<in>set lst. relocatable x \<and> 0 < inst_size x \<Longrightarrow>

      ( program_at (cenv_program c) lst
            (venv_pc vv) \<and>
           program_iter c (Continue vv ee1 ee2)
            (length lst) =
           Continue v2 f1 f2 \<and>
           run_list c vv lst = Some v3)"
apply(auto)
apply(simp add:program_at_next)
using run_list_step
apply(blast)
done

theorem list_aux :
"     program_step c (Continue v e1 e2) =
      Continue vv ee1 ee2 \<Longrightarrow>
      run_list c v [a] = Some vv \<Longrightarrow>

      ( program_at (cenv_program c) lst
            (venv_pc vv) \<Longrightarrow>
           program_iter c (Continue vv ee1 ee2)
            (length lst) =
           Continue v2 f1 f2 \<Longrightarrow>
           run_list c vv lst = Some v3 \<Longrightarrow> v2 = v3) \<Longrightarrow>


       program_at (cenv_program c) (a # lst)
        (venv_pc v) \<Longrightarrow>
       program_iter c
        (program_step c (Continue v e1 e2))
        (length lst) =
       Continue v2 f1 f2 \<Longrightarrow>
       run_list c v (a # lst) = Some v3 \<Longrightarrow>
       relocatable a \<Longrightarrow>
       0 < inst_size a \<Longrightarrow>
       \<forall>x\<in>set lst. relocatable x \<and> 0 < inst_size x \<Longrightarrow>
       v2 = v3"
using list_aux2
apply blast
done

theorem why :
   "Continue v2 f1 f2 = program_iter c
        (program_step c (Continue v e1 e2))
        (length lst)
       \<Longrightarrow>
       \<exists>vv ee1 ee2. program_step c (Continue v e1 e2) =
       Continue vv ee1 ee2"
using program_iter_continue
apply(blast)
done

theorem why2 :
   "program_iter c
        (program_step c (Continue v e1 e2))
        (length lst) = Continue v2 f1 f2
       \<Longrightarrow>
       \<exists>vv ee1 ee2. program_step c (Continue v e1 e2) =
       Continue vv ee1 ee2"
using why
by metis


fun abc2 :: "constant_env \<Rightarrow> variable_env \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"abc2 c v e1 e2 = (case program_step c (Continue v e1 e2) of
  Continue _ a _ \<Rightarrow> a)"

fun abc3 :: "constant_env \<Rightarrow> variable_env \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"abc3 c v e1 e2 = (case program_step c (Continue v e1 e2) of
  Continue _ _ a \<Rightarrow> a)"



theorem list_aux3 :
"     vv = abc1 c v e1 e2 \<Longrightarrow>
      ee1 = abc2 c v e1 e2 \<Longrightarrow>
      ee2 = abc3 c v e1 e2 \<Longrightarrow>
      program_step c (Continue v e1 e2) =
      Continue vv ee1 ee2 \<Longrightarrow>
      run_list c v [a] = Some vv \<Longrightarrow>

      ( program_at (cenv_program c) lst
            (venv_pc vv) \<Longrightarrow>
           program_iter c (Continue vv ee1 ee2)
            (length lst) =
           Continue v2 f1 f2 \<Longrightarrow>
           run_list c vv lst = Some v3 \<Longrightarrow> v2 = v3) \<Longrightarrow>


       program_at (cenv_program c) (a # lst)
        (venv_pc v) \<Longrightarrow>
       program_iter c
        (program_step c (Continue v e1 e2))
        (length lst) =
       Continue v2 f1 f2 \<Longrightarrow>
       run_list c v (a # lst) = Some v3 \<Longrightarrow>
       relocatable a \<Longrightarrow>
       0 < inst_size a \<Longrightarrow>
       \<forall>x\<in>set lst. relocatable x \<and> 0 < inst_size x \<Longrightarrow>
       v2 = v3"
using list_aux2
apply blast
done

declare abc2.simps [simp del]
declare abc3.simps [simp del]
*)

declare abc1.simps [simp del]

theorem list_like_step2 :
  "relocatable inst \<Longrightarrow>
   good_inst inst \<Longrightarrow>
   vctx_next_instruction v c = Some inst \<Longrightarrow>
   program_step c (InstructionContinue v) = InstructionContinue v2 \<Longrightarrow>
   run_list c v (inst#lst) = Some v3 \<Longrightarrow>
   run_list c v [inst] = Some v2"
using list_like_step asd
apply(fastforce)
done

theorem list_like_step3 :
  "relocatable inst \<Longrightarrow>
   good_inst inst \<Longrightarrow>
   vctx_next_instruction v c = Some inst \<Longrightarrow>
   program_step c (InstructionContinue v) = InstructionContinue v2 \<Longrightarrow>
   run_list c v (inst#lst) = Some v3 \<Longrightarrow>
   run_list c v [inst] = Some (abc1 c v)"
apply(auto simp:abc1.simps)
using list_like_step asd
apply(fastforce)
done

theorem list_like_run :
  "(\<forall>x \<in> set lst. relocatable x \<and> good_inst x) \<Longrightarrow>
   program_at (cctx_program c) lst (vctx_pc v) \<Longrightarrow>
   program_iter (length lst) c (InstructionContinue v)
       = InstructionContinue v2 \<Longrightarrow>
   run_list c v lst = Some v3 \<Longrightarrow>
   v2 = v3"
apply(induction lst arbitrary:v v2 v3)
apply(simp add:run_list.simps)
apply(auto simp:simple_step)

(* apply(auto simp:program_iter.simps) *)
apply(rule list_aux3)

apply(auto)
using step_abc1
apply(blast)
apply(rule list_like_step3)
apply(auto)
apply(rule program_next)
apply(auto)
using step_abc1
apply(blast)
done

end


