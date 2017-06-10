theory EvmSep
imports
  "Separation_Algebra"
begin
instantiation "set" :: (type) zero
begin
  definition zero_set_def: "0 \<equiv> {}"
  instance ..
end  
  
instantiation "set" :: (type) sep_algebra
begin

definition
  plus_set_def: "s1 + s2 \<equiv> s1 \<union> s2"

definition
  sep_disj_set_def: "sep_disj s1 s2 \<equiv> s1 \<inter> s2 = {}"

instance
  apply (intro_classes ; 
        fastforce simp: plus_set_def sep_disj_set_def zero_set_def)
  done
end
  
lemmas sep_set_conv = zero_set_def plus_set_def sep_disj_set_def
  
thm sep_conj_ac
end