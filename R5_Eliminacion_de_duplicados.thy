chapter {* R5: Eliminación de duplicados *}

theory R5_Eliminacion_de_duplicados
imports Main 
begin
        
text {*
  --------------------------------------------------------------------- 
  Ejercicio 1. Definir la funcion primitiva recursiva 
     estaEn :: 'a \<Rightarrow> 'a list \<Rightarrow> bool
  tal que (estaEn x xs) se verifica si el elemento x está en la lista
  xs. Por ejemplo, 
     estaEn (2::nat) [3,2,4] = True
     estaEn (1::nat) [3,2,4] = False
  --------------------------------------------------------------------- 
*}

fun estaEn :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "estaEn _ [] = False"
| "estaEn x (y#xs) = ((x = y) \<or> (estaEn x xs))"

value "estaEn (2::nat) [3,2,4] = True"
value "estaEn (1::nat) [3,2,4] = False"

text {* 
  --------------------------------------------------------------------- 
  Ejercicio 2. Definir la función primitiva recursiva 
     sinDuplicados :: 'a list \<Rightarrow> bool
  tal que (sinDuplicados xs) se verifica si la lista xs no contiene
  duplicados. Por ejemplo,  
     sinDuplicados [1::nat,4,2]   = True
     sinDuplicados [1::nat,4,2,4] = False
  --------------------------------------------------------------------- 
*}

fun sinDuplicados :: "'a list \<Rightarrow> bool" where
  "sinDuplicados [] = True"
| "sinDuplicados (x#xs) = (\<not>estaEn x xs \<and> sinDuplicados xs)"

value "sinDuplicados [1::nat,4,2]   = True"
value "sinDuplicados [1::nat,4,2,4] = False"

text {* 
  --------------------------------------------------------------------- 
  Ejercicio 3. Definir la función primitiva recursiva 
     borraDuplicados :: 'a list \<Rightarrow> bool
  tal que (borraDuplicados xs) es la lista obtenida eliminando los
  elementos duplicados de la lista xs. Por ejemplo, 
     borraDuplicados [1::nat,2,4,2,3] = [1,4,2,3]

  Nota: La función borraDuplicados es equivalente a la predefinida
  remdups.  
  --------------------------------------------------------------------- 
*}

fun borraDuplicados :: "'a list \<Rightarrow> 'a list" where
  "borraDuplicados[] = []"
| "borraDuplicados (x#xs) = (if estaEn x xs then borraDuplicados xs  else x # borraDuplicados xs)"

value "borraDuplicados [1::nat,2,4,2,3] = [1,4,2,3]"

text {*
  --------------------------------------------------------------------- 
  Ejercicio 4.1. Demostrar o refutar automáticamente
     length (borraDuplicados xs) \<le> length xs
  --------------------------------------------------------------------- 
*}

-- "La demostración automática es"
lemma length_borraDuplicados:
  "length (borraDuplicados xs) \<le> length xs"
by (induct xs) auto

text {*
  --------------------------------------------------------------------- 
  Ejercicio 4.2. Demostrar o refutar detalladamente
     length (borraDuplicados xs) \<le> length xs
  --------------------------------------------------------------------- 
*}

-- "La demostración estructurada es"

lemma length_borraDuplicados_2: "length (borraDuplicados xs) \<le> length xs" (is "?P xs")
proof (induct xs)
  show "?P []" by simp
next 
  fix a xs
  assume HI: "?P xs"
  have "length (borraDuplicados (a # xs)) \<le> 1+length (borraDuplicados xs)" by simp
  also have "... \<le> 1+length xs" using HI by simp
  finally show "?P (a # xs)" by simp
qed


text {*
  --------------------------------------------------------------------- 
  Ejercicio 5.1. Demostrar o refutar automáticamente
     estaEn a (borraDuplicados xs) = estaEn a xs
  --------------------------------------------------------------------- 
*}

-- "La demostración automática es"
lemma estaEn_borraDuplicados: 
  "estaEn a (borraDuplicados xs) = estaEn a xs"
by (induct xs) auto

text {*
  --------------------------------------------------------------------- 
  Ejercicio 5.2. Demostrar o refutar detalladamente
     estaEn a (borraDuplicados xs) = estaEn a xs
  Nota: Para la demostración de la equivalencia se puede usar
     proof (rule iffI)
  La regla iffI es
     \<lbrakk>P \<Longrightarrow> Q ; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P = Q
  --------------------------------------------------------------------- 
*}

-- "La demostración estructurada es"
lemma estaEn_borraDuplicados_2: "estaEn a (borraDuplicados xs) = estaEn a xs" (is "?P a xs")
proof (induct xs)
  show "?P a []" by simp
next 
  fix b xs
  assume HI: "?P a xs"
  show "?P a (b#xs)"
  proof (rule iffI)
    assume HII: "?P a (b#xs)"
oops
    
    
  

text {*
  --------------------------------------------------------------------- 
  Ejercicio 6.1. Demostrar o refutar automáticamente
     sinDuplicados (borraDuplicados xs)
  --------------------------------------------------------------------- 
*}

-- "La demostración automática"
lemma sinDuplicados_borraDuplicados:
  "sinDuplicados (borraDuplicados xs)"
by (induct xs) (auto simp add: estaEn_borraDuplicados)

text {*
  --------------------------------------------------------------------- 
  Ejercicio 6.2. Demostrar o refutar detalladamente
     sinDuplicados (borraDuplicados xs)
  --------------------------------------------------------------------- 
*}

-- "La demostración estructurada es"
lemma sinDuplicados_borraDuplicados_2:
  "sinDuplicados (borraDuplicados xs)"
proof (induct xs)
  show "sinDuplicados (borraDuplicados [])" by simp
next
  fix x xs
  assume HI: "sinDuplicados (borraDuplicados xs)"
  show "sinDuplicados (borraDuplicados (x # xs))" 
  proof (cases)
    assume "estaEn x xs" 
    then show "sinDuplicados (borraDuplicados (x # xs))" using HI by simp
  next
    assume "\<not>(estaEn x xs)"
    then show "sinDuplicados (borraDuplicados (x # xs))" using HI by (simp add: estaEn_borraDuplicados)
  qed
qed

text {*
  --------------------------------------------------------------------- 
  Ejercicio 7. Demostrar o refutar:
    borraDuplicados (rev xs) = rev (borraDuplicados xs)
  --------------------------------------------------------------------- 
*}

end