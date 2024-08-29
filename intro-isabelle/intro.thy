theory intro
  imports Main
begin

term "True"
value "True \<or> False"

value "Suc 0"
term "0 :: nat" 
value "15 + 2 :: nat"

term "[False]"
term "False#[]"
term "[False, True]"
value "length [False, True]"

type_synonym string = "char list"
term "oi :: string"

datatype 'a ArvBin = Vazia | Nodo "'a ArvBin" 'a "'a ArvBin"

term "Vazia"
term "Nodo Vazia True Vazia"

definition sq :: "nat \<Rightarrow> nat" where "sq n = n * n"

value "sq 3"

fun ehpar :: "nat \<Rightarrow> bool" where 
"ehpar 0 = True" |
"ehpar (Suc 0) = False" |
"ehpar (Suc (Suc n)) = ehpar n"

value "ehpar 2"

(*
fun somatorio :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 somatorio i f = (if i > f then 0 else i + somatorio (Suc f)"
*)

primrec soma :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"soma x 0 = x" |
"soma x (Suc y) = Suc (soma x y)"

value "soma 2 3"

theorem somaassoc: "\<forall>x y . soma x (soma y z) = soma (soma x y) z"
  apply (induction z)
   apply (simp)
  apply (simp)
  done



end