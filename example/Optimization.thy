theory Optimization

imports Main "~~/src/HOL/Word/Word"

begin

type_synonym mword = "256 word"

lemma add0 : "(x :: mword) + 0 = x"
apply(auto)
done

lemma mul1 : "(x :: mword) * 1 = x"
apply(auto)
done

definition evm_div :: "mword \<Rightarrow> mword \<Rightarrow> mword"
where
"evm_div a b =
  (if b = 0 then 0 else a div b)"

lemma zero_div : "evm_div 0 (x :: mword) = 0"
apply(simp add: evm_div_def)
apply(simp add: word_div_def)
done

  
lemma div1 : "evm_div (x :: mword) 1 = x"
apply(simp add: evm_div_def)
apply(simp add: word_div_def)
done

definition evm_sdiv :: "mword \<Rightarrow> mword \<Rightarrow> mword"
where
"evm_sdiv a b =
     (if b = 0 then 0 else
                        word_of_int ((sint a) div (sint b)))"

lemma sint1 : "sint (1 :: mword) = 1"
apply(simp add: sint_uint)
done
                        
lemma sdiv1 : "evm_sdiv x 1 = x"
apply(simp add: evm_sdiv_def add: sint1)
done

definition evm_mod :: "mword \<Rightarrow> mword \<Rightarrow> mword"
where
"evm_mod =
(\<lambda> a divisor. (if divisor = 0 then 0 else a mod divisor))"

lemma zero_mod : "evm_mod 0 x = 0"
apply(simp add: evm_mod_def add: word_mod_def)
done

lemma mod_refl : "evm_mod x x = 0"
apply(simp add: evm_mod_def add: word_mod_def)
done

lemma not_not : "NOT (NOT (x :: mword)) = x"
apply(auto)
done

lemma xor_refl : "(x :: mword) XOR x = 0"
apply(auto)
done


end