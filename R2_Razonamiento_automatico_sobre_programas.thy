chapter {* R2: Razonamiento sobre programas en Isabelle/HOL *}

theory R2_Razonamiento_automatico_sobre_programas
imports Main 
begin

declare [[names_short]]

text {* --------------------------------------------------------------- 
  Ejercicio 1.1. Definir la función
     sumaImpares :: nat \<Rightarrow> nat
  tal que (sumaImpares n) es la suma de los n primeros números
  impares. Por ejemplo,
     sumaImpares 5  =  25
  ------------------------------------------------------------------ *}

fun sumaImpares :: "nat \<Rightarrow> nat" where
  "sumaImpares 0 = 0"
| "sumaImpares n = ((n*2)-1) + sumaImpares(n-1)"

value "sumaImpares 5 = 25"

text {* --------------------------------------------------------------- 
  Ejercicio 1.2. Demostrar que 
     sumaImpares n = n*n
  ------------------------------------------------------------------- *}

lemma "sumaImpares n = n*n"
apply (induct n)
apply auto
done

text {* --------------------------------------------------------------- 
  Ejercicio 2.1. Definir la función
     sumaPotenciasDeDosMasUno :: nat \<Rightarrow> nat
  tal que 
     (sumaPotenciasDeDosMasUno n) = 1 + 2^0 + 2^1 + 2^2 + ... + 2^n. 
  Por ejemplo, 
     sumaPotenciasDeDosMasUno 3  =  16
  ------------------------------------------------------------------ *}

fun sumaPotenciasDeDosMasUno :: "nat \<Rightarrow> nat" where
  "sumaPotenciasDeDosMasUno 0 = 2"
| "sumaPotenciasDeDosMasUno n = 2^n + sumaPotenciasDeDosMasUno(n-1)"

value "sumaPotenciasDeDosMasUno 3 = 16"

text {* --------------------------------------------------------------- 
  Ejercicio 2.2. Demostrar que 
     sumaPotenciasDeDosMasUno n = 2^(n+1)
  ------------------------------------------------------------------- *}

lemma "sumaPotenciasDeDosMasUno n = 2^(n+1)"
by (induct n) auto

text {* --------------------------------------------------------------- 
  Ejercicio 3.1. Definir la función
     copia :: nat \<Rightarrow> 'a \<Rightarrow> 'a list
  tal que (copia n x) es la lista formado por n copias del elemento
  x. Por ejemplo, 
     copia 3 x = [x,x,x]
  ------------------------------------------------------------------ *}

fun copia :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "copia 0 x = []"
| "copia n x = [x] @ copia (n-1) x"

value "copia 3 x = [x,x,x]"

text {* --------------------------------------------------------------- 
  Ejercicio 3.2. Definir la función
     todos :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool
  tal que (todos p xs) se verifica si todos los elementos de xs cumplen
  la propiedad p. Por ejemplo,
     todos (\<lambda>x. x>(1::nat)) [2,6,4] = True
     todos (\<lambda>x. x>(2::nat)) [2,6,4] = False
  Nota: La conjunción se representa por \<and>
  ----------------------------------------------------------------- *}

fun todos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "todos p [] = True"
| "todos p (x#xs) = (p x \<and> todos p xs)"

value "todos (\<lambda>x. x>(1::nat)) [2,6,4] = True"
value "todos (\<lambda>x. x>(2::nat)) [2,6,4] = False"

text {* --------------------------------------------------------------- 
  Ejercicio 3.3. Demostrar que todos los elementos de (copia n x) son
  iguales a x. 
  ------------------------------------------------------------------- *}

lemma "todos (\<lambda>y. y=x) (copia n x)"
by (induct n) auto

text {* --------------------------------------------------------------- 
  Ejercicio 4.1. Definir, recursivamente y sin usar (@), la función
     amplia :: 'a list \<Rightarrow> 'a \<Rightarrow> 'a list
  tal que (amplia xs y) es la lista obtenida añadiendo el elemento y al
  final de la lista xs. Por ejemplo,
     amplia [d,a] t = [d,a,t]
  ------------------------------------------------------------------ *}

fun amplia :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "amplia [] y = [y]"
| "amplia (x#xs) y = x # amplia xs y"

value "amplia [d,a] t = [d,a,t]"

text {* --------------------------------------------------------------- 
  Ejercicio 4.2. Demostrar que 
     amplia xs y = xs @ [y]
  ------------------------------------------------------------------- *}

lemma "amplia xs y = xs @ [y]"
apply (induct xs)
apply auto
done

end