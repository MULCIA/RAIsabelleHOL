chapter {* R4: Cuantificadores sobre listas *}

theory R4_Cuantificadores_sobre_listas
imports Main
begin

text {* 
  --------------------------------------------------------------------- 
  Ejercicio 1. Definir la función 
     todos :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool
  tal que (todos p xs) se verifica si todos los elementos de la lista 
  xs cumplen la propiedad p. Por ejemplo, se verifica 
     todos (\<lambda>x. 1<length x) [[2,1,4],[1,3]]
     \<not>todos (\<lambda>x. 1<length x) [[2,1,4],[3]]

  Nota: La función todos es equivalente a la predefinida list_all. 
  --------------------------------------------------------------------- 
*}

fun todos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "todos p [] = True"
| "todos p (x#xs) = (p x \<and> todos p xs)"

text {* 
  --------------------------------------------------------------------- 
  Ejercicio 2. Definir la función 
     algunos :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool
  tal que (algunos p xs) se verifica si algunos elementos de la lista 
  xs cumplen la propiedad p. Por ejemplo, se verifica 
     algunos (\<lambda>x. 1<length x) [[2,1,4],[3]]
     \<not>algunos (\<lambda>x. 1<length x) [[],[3]]"

  Nota: La función algunos es equivalente a la predefinida list_ex. 
  --------------------------------------------------------------------- 
*}

fun algunos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
   "algunos p []     = False"
| "algunos p (x#xs) = (p x \<or> algunos p xs)"

text {*
  --------------------------------------------------------------------- 
  Ejercicio 3.1. Demostrar o refutar automáticamente 
     todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)
  --------------------------------------------------------------------- 
*}

lemma "todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)"
by (induct xs) auto

text {*
  --------------------------------------------------------------------- 
  Ejercicio 3.2. Demostrar o refutar detalladamente
     todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)
  --------------------------------------------------------------------- 
*}


lemma "todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)"
proof (induct xs)
  show "todos (\<lambda>x. P x \<and> Q x) [] = (todos P [] \<and> todos Q [])" by simp
next
  fix a xs
  assume HI: "todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)" 
  have "todos (\<lambda>x. P x \<and> Q x) (a # xs) =  ((P a \<and> Q a) \<and> (todos P xs \<and> todos Q xs))" using HI by simp
  also have "... = ((P a \<and> todos P xs) \<and> (Q a \<and> todos Q xs))" by blast
  also have "... = (todos P (a#xs) \<and> todos Q (a#xs)) " by simp
 finally show "todos (\<lambda>x. P x \<and> Q x) (a#xs) = (todos P (a#xs) \<and> todos Q (a#xs))" by simp 
qed

text {*
  --------------------------------------------------------------------- 
  Ejercicio 4.1. Demostrar o refutar automáticamente
     todos P (x @ y) = (todos P x \<and> todos P y)
  --------------------------------------------------------------------- 
*}

lemma "todos P (x @ y) = (todos P x \<and> todos P y)"
by (induct x) auto

text {*
  --------------------------------------------------------------------- 
  Ejercicio 4.2. Demostrar o refutar detalladamente
     todos P (x @ y) = (todos P x \<and> todos P y)
  --------------------------------------------------------------------- 
*}

lemma todos_append: "todos P (x @ y) = (todos P x \<and> todos P y)"
proof (induct x)
  show "todos P ([] @ y) = (todos P [] \<and> todos P y)" by simp
next 
  fix a x
  assume HI: "todos P (x @ y) = (todos P x \<and> todos P y)"
  have "todos P ((a#x) @ y) = (P a \<and> (todos P (x @ y)))" by simp
  also have "... = (P a \<and> (todos P x \<and> todos P y))" using HI by simp
  finally show "todos P ((a # x) @ y) = (todos P (a # x) \<and> todos P y)" by simp
qed

text {*
  --------------------------------------------------------------------- 
  Ejercicio 5.1. Demostrar o refutar automáticamente 
     todos P (rev xs) = todos P xs
  --------------------------------------------------------------------- 
*}

lemma "todos P (rev xs) = todos P xs" 
apply (induct xs)
apply simp
apply (simp add: todos_append)
apply auto
done

text {*
  --------------------------------------------------------------------- 
  Ejercicio 5.2. Demostrar o refutar detalladamente
     todos P (rev xs) = todos P xs
  --------------------------------------------------------------------- 
*}

lemma "todos P (rev xs) = todos P xs"
proof (induct xs)
show "todos P (rev []) = todos P []" by simp
next
fix a xs
  assume HI: "todos P (rev xs) = todos P xs"
  have "todos P (rev (a # xs)) = (todos P ((rev xs)@[a]))" by simp
  also have "... = (todos P (rev xs) \<and> todos P [a])" by (simp add:todos_append)
  also have "... = (todos P xs \<and> P a)" using HI by simp
  also have "... = (P a \<and> todos P xs)" by arith
  also have "... = (todos P (a#xs))" by simp
  finally show "todos P (rev (a # xs)) = (todos P (a#xs))" by simp    
qed

text {*
  --------------------------------------------------------------------- 
  Ejercicio 6. Demostrar o refutar:
    algunos (\<lambda>x. P x \<and> Q x) xs = (algunos P xs \<and> algunos Q xs)
  --------------------------------------------------------------------- 
*}

lemma "algunos (\<lambda>x. P x \<and> Q x) xs = (algunos P xs \<and> algunos Q xs)"
quickcheck
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 7.1. Demostrar o refutar automáticamente 
     algunos P (map f xs) = algunos (P \<circ> f) xs
  --------------------------------------------------------------------- 
*}

lemma "algunos P (map f xs) = algunos (P o f) xs"
apply (induct xs)
apply auto
done

text {*
  --------------------------------------------------------------------- 
  Ejercicio 7.2. Demostrar o refutar datalladamente
     algunos P (map f xs) = algunos (P \<circ> f) xs
  --------------------------------------------------------------------- 
*}

lemma "algunos P (map f xs) = algunos (P o f) xs"
proof (induct xs)
  show "algunos P (map f []) = algunos (P \<circ> f) []"  by simp
next
  fix a xs
  assume H1: "algunos P (map f xs) = algunos (P \<circ> f) xs"
  have  "algunos P (map f (a # xs)) = (algunos P (map f [a]) \<or> algunos P (map f xs))" by simp
  also have "\<dots> = (algunos (P \<circ> f) [a] \<or>  algunos (P \<circ> f) xs )" using H1 by simp
  also have "\<dots> = algunos (P \<circ> f) (a#xs)" by simp
  finally show "algunos P (map f (a # xs)) = algunos (P \<circ> f) (a#xs)" by simp
qed

text {*
  --------------------------------------------------------------------- 
  Ejercicio 8.1. Demostrar o refutar automáticamente 
     algunos P (xs @ ys) = (algunos P xs \<or> algunos P ys)
  --------------------------------------------------------------------- 
*}

lemma "algunos P (xs @ ys) = (algunos P xs \<or> algunos P ys)"
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 8.2. Demostrar o refutar detalladamente
     algunos P (xs @ ys) = (algunos P xs \<or> algunos P ys)
  --------------------------------------------------------------------- 
*}

lemma algunos_append:
  "algunos P (xs @ ys) = (algunos P xs \<or> algunos P ys)"
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 9.1. Demostrar o refutar automáticamente
     algunos P (rev xs) = algunos P xs
  --------------------------------------------------------------------- 
*}

lemma "algunos P (rev xs) = algunos P xs"
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 9.2. Demostrar o refutar detalladamente
     algunos P (rev xs) = algunos P xs
  --------------------------------------------------------------------- 
*}

lemma "algunos P (rev xs) = algunos P xs"
oops

text {*
  --------------------------------------------------------------------- 
  Ejercicio 10. Encontrar un término no trivial Z tal que sea cierta la 
  siguiente ecuación:
     algunos (\<lambda>x. P x \<or> Q x) xs = Z
  y demostrar la equivalencia de forma automática y detallada.
  --------------------------------------------------------------------- 
*}

text {*
  --------------------------------------------------------------------- 
  Ejercicio 11.1. Demostrar o refutar automáticamente
     algunos P xs = (\<not> todos (\<lambda>x. (\<not> P x)) xs)
  --------------------------------------------------------------------- 
*}

lemma "algunos P xs = (\<not> todos (\<lambda>x. (\<not> P x)) xs)"
oops
     
text {*
  --------------------------------------------------------------------- 
  Ejercicio 11.2. Demostrar o refutar datalladamente
     algunos P xs = (\<not> todos (\<lambda>x. (\<not> P x)) xs)
  --------------------------------------------------------------------- 
*}

lemma "algunos P xs = (\<not> todos (\<lambda>x. (\<not> P x)) xs)"
oops
     
text {*
  --------------------------------------------------------------------- 
  Ejercicio 12. Definir la funcion primitiva recursiva 
     estaEn :: 'a \<Rightarrow> 'a list \<Rightarrow> bool
  tal que (estaEn x xs) se verifica si el elemento x está en la lista
  xs. Por ejemplo, 
     estaEn (2::nat) [3,2,4] = True
     estaEn (1::nat) [3,2,4] = False
  --------------------------------------------------------------------- 
*}

fun estaEn :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "estaEn x [] = False"
| "estaEn x (a#xs) = ((a = x) \<or> (estaEn x xs))"

text {*
  --------------------------------------------------------------------- 
  Ejercicio 13. Expresar la relación existente entre estaEn y algunos. 
  Demostrar dicha relación de forma automática y detallada.
  --------------------------------------------------------------------- 
*}

end